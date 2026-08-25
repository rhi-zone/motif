//! Continuous coordinate optimization at a fixed [`Skeleton`]: simulated
//! annealing over the `2 * vertex_count` coordinate values.
//!
//! # Why simulated annealing, and at which level
//!
//! `docs/asymmetric-methods.md` §1.1 establishes that a fixed skeleton's
//! realization space is `(n - 3)`-dimensional and continuous (a flex),
//! and §1.4 conjectures the area-maximizing point sits where several
//! `area <= 1` inequality constraints are simultaneously active — i.e.
//! this is a constrained continuous optimization on a manifold cut out
//! by smooth equality constraints (length, incidence), intersected with
//! a polytope-like region cut out by inequality constraints (area caps).
//! The objective (sum of bounded-face areas as a function of vertex
//! coordinates) is *not* smooth-everywhere in a way that's easy to
//! differentiate analytically: face structure itself (how many faces,
//! which vertices bound which face) is a combinatorial function of the
//! coordinates through the arrangement builder, so its gradient has
//! removable-but-awkward discontinuities exactly where topology could
//! change. Simulated annealing needs no gradient, tolerates a
//! non-smooth objective, and (via its temperature schedule) can escape
//! the local optima that a naive coordinate hill-climb would get stuck
//! in near topology changes — the standard reasons to reach for it here.
//!
//! We run SA at the **inner** (continuous, fixed-skeleton) level only.
//! The **outer** (discrete, which-skeleton) level is handled by
//! `skeleton::random_growth` + multistart in `search.rs`: each random
//! seed produces a structurally different skeleton, and many independent
//! (skeleton, coordinate-seed) pairs are tried and compared. This is
//! deliberately *not* SA-over-graphs (e.g. proposing edge-rewires with a
//! Metropolis rule on the graph itself, as one could): that would need a
//! notion of "graph-adjacent skeleton" with a well-defined proposal
//! distribution and is a materially bigger undertaking (closer to what
//! Cox et al., arXiv:1901.00319, do with 3-connected cubic planar graph
//! enumeration) than the time budget here supports. Multistart over
//! random skeletons plus a few hand-built structured families (regular
//! polygon, grid, hub-polygon) is the pragmatic outer search implemented
//! instead; extending it to true annealed graph moves is future work.
//!
//! # Handling the area <= 1 cap: penalty, not projection or rejection
//!
//! The cap is folded into the objective as a smooth squared-hinge
//! penalty (`max(0, area - 1)^2` per face), not enforced by projecting
//! infeasible points back to feasibility, and not by hard-rejecting any
//! proposed move that violates it. Reasons:
//! - **Not hard rejection**: early in the search, most random
//!   perturbations of an unconverged configuration will have some
//!   over-large face; hard-rejecting all of them would make the walk
//!   unable to move at all until it accidentally lands in the feasible
//!   region, which for an `(n-3)`-dimensional space found by local moves
//!   is not a good way to get there.
//! - **Not projection**: there's no simple closed-form projection from
//!   an infeasible point back to the feasible set for this constraint
//!   (a `<= 1` area bound on an arbitrary polygon is not a projection
//!   onto a convex set in coordinate space), so "projection" would
//!   itself have to be an inner optimization.
//! - **Penalty with a continuation schedule** (weight grows over the
//!   run) is the standard compromise: early iterations can pass through
//!   mildly infeasible states while exploring, and by the end the weight
//!   is high enough that the accepted state is feasible in practice.
//!   The *authoritative* feasibility check is still always
//!   [`crate::Configuration::validate`] on the final result — this
//!   module's penalty is a search heuristic, never the source of truth
//!   for whether a claimed result is valid.
//!
//! The `length` and `incidence` equality constraints get the same
//! squared-penalty treatment (not a separate projection/Newton step),
//! for the same "no simple closed-form projection" reason, and because a
//! single unified penalty objective is simpler to reason about and to
//! justify than mixing two different constraint-handling strategies in
//! one optimizer. Precision comes from the annealing schedule itself:
//! step size and temperature both decay to near zero by the end of the
//! run, so the final phase behaves like small-step stochastic hill
//! climbing on a smooth, well-conditioned (by then, since the penalty
//! weight is high and residuals are already small) local objective —
//! empirically enough to land within the crate's default `1e-6`
//! tolerances (see the record-matching tests in `tests/`).

use crate::arrangement::build_arrangement;
use crate::geometry::Point;
use crate::rng::Rng;
use crate::skeleton::Skeleton;
use serde::{Deserialize, Serialize};

/// Parameters for one annealing run. All schedules are geometric
/// (`value_k = start * (end/start)^(k/iterations)`), the standard cheap
/// choice; `seed` makes the whole run reproducible.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnnealParams {
    pub iterations: usize,
    pub initial_temp: f64,
    pub final_temp: f64,
    /// Gaussian step standard deviation for a single vertex-coordinate
    /// proposal, at the start and end of the run.
    pub initial_step: f64,
    pub final_step: f64,
    /// Weight on the summed (length + incidence + cap) penalty, at the
    /// start and end of the run.
    pub initial_penalty: f64,
    pub final_penalty: f64,
    pub seed: u64,
}

impl Default for AnnealParams {
    fn default() -> Self {
        AnnealParams {
            iterations: 200_000,
            initial_temp: 0.05,
            final_temp: 1e-7,
            initial_step: 0.3,
            final_step: 1e-6,
            initial_penalty: 5.0,
            final_penalty: 5.0e6,
            seed: 0,
        }
    }
}

fn geometric(start: f64, end: f64, frac: f64) -> f64 {
    if start <= 0.0 || end <= 0.0 {
        return start + (end - start) * frac;
    }
    start * (end / start).powf(frac)
}

/// The raw components of the objective at one coordinate assignment,
/// before combining into a score. Exposed so callers (and tests) can
/// inspect *why* a candidate scored the way it did, not just the score.
#[derive(Debug, Clone, Copy)]
pub struct Residuals {
    pub area: f64,
    pub length_sq: f64,
    pub incidence_sq: f64,
    pub cap_sq: f64,
}

impl Residuals {
    pub fn penalty(&self) -> f64 {
        self.length_sq + self.incidence_sq + self.cap_sq
    }
}

/// Evaluate a skeleton at given coordinates: total bounded-face area
/// (using a loose, schedule-dependent tolerance for arrangement
/// construction — see module docs) plus the three penalty components.
pub fn evaluate(skeleton: &Skeleton, coords: &[Point], arrangement_tol: f64) -> Residuals {
    let mut length_sq = 0.0;
    for &(u, v) in &skeleton.fences {
        let len = coords[u].dist(coords[v]);
        length_sq += (len - 1.0).powi(2);
    }

    let mut incidence_sq = 0.0;
    for &(v, f) in &skeleton.t_junctions {
        let (a, b) = skeleton.fences[f];
        let seg = crate::geometry::Segment::new(coords[a], coords[b]);
        let d = seg.direction();
        let len2 = d.dot(d).max(1e-12);
        let t = (coords[v] - coords[a]).dot(d) / len2;
        let closest = coords[a] + d.scale(t);
        let perp = coords[v].dist(closest);
        incidence_sq += perp * perp;
        // Hinge: the landing point should fall strictly between the
        // target fence's endpoints (t in [0,1]); penalize overshoot.
        incidence_sq += (-t).max(0.0).powi(2) + (t - 1.0).max(0.0).powi(2);
    }

    let segments: Vec<crate::geometry::Segment> = skeleton
        .fences
        .iter()
        .map(|&(u, v)| crate::geometry::Segment::new(coords[u], coords[v]))
        .collect();
    let arrangement = build_arrangement(&segments, arrangement_tol, arrangement_tol);
    let mut area = 0.0;
    let mut cap_sq = 0.0;
    for face in &arrangement.bounded_faces {
        area += face.area;
        cap_sq += (face.area - 1.0).max(0.0).powi(2);
    }

    Residuals {
        area,
        length_sq,
        incidence_sq,
        cap_sq,
    }
}

/// Outcome of one annealing run.
#[derive(Debug, Clone)]
pub struct AnnealResult {
    pub coords: Vec<Point>,
    pub final_residuals: Residuals,
    pub final_score: f64,
    pub params: AnnealParams,
}

fn score(residuals: &Residuals, penalty_weight: f64) -> f64 {
    residuals.area - penalty_weight * residuals.penalty()
}

/// Run simulated annealing on `skeleton`'s coordinates, starting from
/// `init_coords`, with schedules given by `params`. Single-vertex
/// Gaussian-perturbation proposals, Metropolis acceptance, geometric
/// decay of temperature and penalty-weight (see module docs for why this
/// combination).
///
/// The proposal step size is **not** on a fixed geometric schedule.
/// Early testing (chasing the exact unit-triangle area, n=3) showed a
/// fixed `initial_step -> final_step` decay stalls: convergence via
/// single-coordinate Metropolis moves toward a smooth local optimum is a
/// biased random walk, not gradient descent, so the distance it can
/// still cover in the time remaining depends on how far off it *already
/// is*, not on iteration count alone — a schedule tuned for one
/// skeleton's convergence rate silently undershoots or overshoots
/// another's. Instead we use the standard "1-in-5 success rule" (Rechenberg):
/// track the acceptance rate in a rolling window and grow the step when
/// it's above 20% (still finding easy improvements, so take bigger
/// swings) or shrink it when below (already near a local optimum, so
/// only fine moves help). This lets the step size home in on whatever
/// scale the residual actually needs, which is what got the triangle
/// case (and everything since) down to the crate's `1e-6` validation
/// tolerance.
pub fn anneal(skeleton: &Skeleton, init_coords: Vec<Point>, params: AnnealParams) -> AnnealResult {
    assert_eq!(init_coords.len(), skeleton.vertex_count);
    let mut rng = Rng::new(params.seed);
    let mut coords = init_coords;

    // Arrangement tolerance during the search must be loose enough that
    // not-yet-converged T-junctions still register as landing on their
    // target fence (otherwise the traced topology, and hence the area
    // term, is wrong for most of the run) but tight enough by the end
    // that it matches the crate's real validation tolerance.
    let arrangement_tol_of = |frac: f64| geometric(0.05, 1e-6, frac).max(1e-6);

    let mut residuals = evaluate(skeleton, &coords, arrangement_tol_of(0.0));
    let mut cur_score = score(&residuals, params.initial_penalty);

    let mut best_coords = coords.clone();
    let mut best_score = score(&residuals, params.final_penalty);
    let mut best_residuals = residuals;

    let mut step = params.initial_step;
    const WINDOW: usize = 50;
    let mut window_accepts = 0usize;
    let mut window_total = 0usize;

    for iter in 0..params.iterations {
        let frac = iter as f64 / params.iterations.max(1) as f64;
        let temp = geometric(params.initial_temp, params.final_temp, frac);
        let penalty_weight = geometric(params.initial_penalty, params.final_penalty, frac);
        let arrangement_tol = arrangement_tol_of(frac);

        let v = rng.range_usize(skeleton.vertex_count);
        let dx = rng.gaussian() * step;
        let dy = rng.gaussian() * step;
        let old = coords[v];
        coords[v] = Point::new(old.x + dx, old.y + dy);

        let new_residuals = evaluate(skeleton, &coords, arrangement_tol);
        let new_score = score(&new_residuals, penalty_weight);

        let accept = new_score >= cur_score || {
            let delta = new_score - cur_score;
            rng.bernoulli((delta / temp.max(1e-300)).exp())
        };

        window_total += 1;
        if accept {
            window_accepts += 1;
            cur_score = new_score;
            residuals = new_residuals;
            // Track the best *feasible-leaning* score seen using the
            // final (harshest) penalty weight, so "best" isn't
            // contaminated by an early, loosely-penalized high score
            // that's actually badly infeasible.
            let strict_score = score(&residuals, params.final_penalty);
            if strict_score > best_score {
                best_score = strict_score;
                best_coords = coords.clone();
                best_residuals = residuals;
            }
        } else {
            coords[v] = old;
        }

        if window_total >= WINDOW {
            let rate = window_accepts as f64 / window_total as f64;
            if rate > 0.2 {
                step *= 1.2;
            } else {
                step *= 0.85;
            }
            step = step.clamp(params.final_step, params.initial_step * 4.0);
            window_accepts = 0;
            window_total = 0;
        }
    }

    AnnealResult {
        coords: best_coords,
        final_residuals: best_residuals,
        final_score: best_score,
        params,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::skeleton::regular_polygon;

    #[test]
    fn anneal_recovers_unit_triangle_area_from_perturbed_start() {
        let (sk, exact_coords) = regular_polygon(3);
        let mut rng = Rng::new(123);
        let perturbed: Vec<Point> = exact_coords
            .iter()
            .map(|p| Point::new(p.x + rng.gaussian() * 0.2, p.y + rng.gaussian() * 0.2))
            .collect();
        let params = AnnealParams {
            iterations: 20_000,
            ..AnnealParams::default()
        };
        let result = anneal(&sk, perturbed, params);
        let expected_area = 3f64.sqrt() / 4.0;
        assert!(
            (result.final_residuals.area - expected_area).abs() < 1e-4,
            "area = {}, expected {}",
            result.final_residuals.area,
            expected_area
        );
        assert!(result.final_residuals.penalty() < 1e-6);
    }
}
