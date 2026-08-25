//! Boundary-first seeded enumeration of skeletons ("subdivide a fixed
//! regular k-gon" instead of "generate then filter free skeletons").
//!
//! # Why this exists, and how it supersedes the corner-graph approach
//!
//! An earlier attempt in this session generated free combinatorial
//! skeletons (a "corner graph" of ordinary-corner vertices plus
//! T-junction pendants attached to it) and filtered the results with
//! the moduli-dimension / boundary-bound / face-count checks from
//! `docs/upper-bounds.md`. That is generate-then-reject: the raw
//! generation step still explodes combinatorially before any filter
//! gets a chance to prune it, because the corner graph's own vertex
//! count and edge set are unconstrained at generation time.
//!
//! This module inverts the order: the outer boundary is not searched
//! for, it is **constructed** directly from the DERIVED, VERIFIED
//! boundary-polygon lemma (`docs/upper-bounds.md` §4,
//! [`crate::bounds::boundary_polygon_bound`]): total enclosed area
//! equals the outer boundary polygon's shoelace area (interior fences
//! only subdivide it), and that area is maximized, among all simple
//! polygons with `k` unit sides, by the *regular* unit k-gon. So for a
//! target area, [`k_min`] computes the smallest boundary-fence count
//! `k` that could possibly reach it — a hard combinatorial lower bound
//! requiring no geometry search at all — and the boundary itself is
//! then built by [`crate::skeleton::regular_polygon`], not searched
//! for. Only the *interior* subdivision (`n - k` remaining fences) is
//! actually enumerated, which is a much smaller space because the
//! boundary's coordinates are already fixed.
//!
//! **Verified against both solved asymmetric records before adopting
//! this as the primary mechanism** (checked directly against
//! `tests/records.rs` and `docs/upper-bounds.md`'s own bound table, not
//! asserted from a peer's say-so): `kinked_hexagon_n8`'s boundary is
//! exactly 6 fences (APEX-SL-BL-BA-BR-SR-APEX) with 2 interior chords
//! (PL-PR, BA-M) — `k_min(2.0893244080014) == 6` below, matching
//! exactly. `split_hub_pinwheel_n11`'s boundary is exactly 7 fences
//! (B-E-G-R-S1-S2-D-B) with 4 interior chords — `k_min(3.5372167764)
//! == 7`, matching exactly. Both ground-truth records sit at their
//! `k_min` precisely, with no slack — real evidence for the
//! decomposition, not a guess.
//!
//! The boundary is *seeded* as regular, not *locked* as regular: every
//! skeleton built here is still handed to the existing free-coordinate
//! annealer ([`crate::anneal::anneal`]), which is free to move boundary
//! vertices away from the regular polygon if that is where the true
//! optimum for that skeleton lies (see `domino_via_boundary_seed` below,
//! whose true optimal boundary is a *non-regular*, flattened hexagon —
//! the regular-hexagon initial guess is only a starting point).

use crate::anneal::{anneal, AnnealParams};
use crate::bounds::boundary_polygon_bound;
use crate::configuration::{Configuration, Tolerance};
use crate::geometry::Point;
use crate::skeleton::{regular_polygon, Skeleton};

/// The smallest `k` in `3..=cap` such that
/// `boundary_polygon_bound(k) >= target_area`, i.e. the fewest fences a
/// simple unit-edge boundary polygon could use and still have a chance
/// of enclosing `target_area` (before any interior subdivision — see
/// module docs). Returns `None` if no `k <= cap` suffices (shouldn't
/// happen for any `cap >= n`, since `boundary_polygon_bound` is
/// increasing and unbounded).
///
/// **DERIVED** directly from `docs/upper-bounds.md` §4 (already
/// DERIVED, VERIFIED there); this function adds no new geometric claim,
/// only inverts an existing monotone function.
pub fn k_min(target_area: f64, cap: usize) -> Option<usize> {
    (3..=cap).find(|&k| boundary_polygon_bound(k as u32) >= target_area - 1e-9)
}

/// A skeleton under construction, seeded from a fixed regular unit
/// k-gon boundary. Interior fences are added combinatorially on top;
/// each helper returns the skeleton in a state that is *not*
/// necessarily immediately valid (a freshly created ordinary vertex may
/// have degree 1 until a later call reuses it) — call
/// [`BoundaryBuilder::finish`] and then `Skeleton::validate_shape` once
/// construction is complete.
pub struct BoundaryBuilder {
    pub k: usize,
    pub coords: Vec<Point>,
    pub fences: Vec<(usize, usize)>,
    pub t_junctions: Vec<(usize, usize)>,
}

impl BoundaryBuilder {
    /// Seed with the regular unit k-gon boundary (`k` fences, `k`
    /// ordinary-corner vertices, no T-junctions).
    pub fn new(k: usize) -> Self {
        let (sk, coords) = regular_polygon(k);
        BoundaryBuilder {
            k,
            coords,
            fences: sk.fences,
            t_junctions: Vec::new(),
        }
    }

    /// A new interior fence from an existing vertex `anchor` to a fresh
    /// vertex (initial coordinate guess `guess`). The fresh vertex has
    /// degree 1 after this call alone — it must be reused as an
    /// `anchor` (or a `direct_chord` endpoint) by a later call, or the
    /// final `validate_shape` will reject it as a dangling ordinary
    /// endpoint. Returns the new vertex's index, so callers can build
    /// shared hubs (multiple chords reusing the same returned index) —
    /// this is the "vertex-sharing" move `random_growth` and the
    /// outer-SA search structurally could not find (see module docs and
    /// the n=12 case below).
    pub fn shared_vertex_chord(&mut self, anchor: usize, guess: Point) -> usize {
        let v = self.coords.len();
        self.coords.push(guess);
        self.fences.push((anchor, v));
        v
    }

    /// A fence directly between two already-existing vertices (both
    /// ordinary corners of one more fence after this call). Used e.g.
    /// for the domino's shared interior edge, which connects two
    /// pre-existing boundary vertices.
    pub fn direct_chord(&mut self, u: usize, v: usize) {
        self.fences.push((u, v));
    }

    /// A new fence from `anchor` to a fresh vertex T-junctioned onto the
    /// interior of `target_fence` (initial guess at parameter `t` along
    /// that fence). Self-closing: a T-junction pendant never needs a
    /// later call to become valid.
    pub fn t_junction_chord(&mut self, anchor: usize, target_fence: usize, t: f64) -> usize {
        let v = self.fresh_t_junction_vertex(target_fence, t);
        self.fences.push((anchor, v));
        v
    }

    /// A fresh vertex T-junctioned onto `target_fence`, with **no**
    /// fence of its own yet — the caller must connect it via
    /// [`Self::direct_chord`] (to another existing/fresh vertex) before
    /// `finish`, or it stays a dangling endpoint. This is the pattern
    /// the ground-truth `kinked_hexagon_n8`/`split_hub_pinwheel_n11`
    /// skeletons actually use for chord endpoints that land by
    /// T-junction: the landing point IS the chord's endpoint, with no
    /// separate "anchor" fence — `t_junction_chord` (which *does* add an
    /// anchor fence) is for the different case of a fresh spoke from an
    /// existing vertex.
    pub fn fresh_t_junction_vertex(&mut self, target_fence: usize, t: f64) -> usize {
        let (a, b) = self.fences[target_fence];
        let guess = self.coords[a] + (self.coords[b] - self.coords[a]).scale(t);
        let v = self.coords.len();
        self.coords.push(guess);
        self.t_junctions.push((v, target_fence));
        v
    }

    pub fn finish(self) -> (Skeleton, Vec<Point>) {
        let vertex_count = self.coords.len();
        (
            Skeleton {
                vertex_count,
                fences: self.fences,
                t_junctions: self.t_junctions,
            },
            self.coords,
        )
    }
}

/// Moduli dimension per `docs/asymmetric-methods.md` §1.1/§1.3:
/// `dim = (n - 3) - sum_v max(deg(v) - 2, 0)` over vertices that are
/// *ordinary corners* (>=2 fences sharing that endpoint exactly), since
/// only those can carry an over-determined multi-way coincidence;
/// T-junction pendants are dimension-neutral at the baseline rate and
/// contribute 0 to the sum by construction (their degree, counting the
/// one fence they anchor, is 1, so `max(1-2,0) = 0`).
pub fn moduli_dimension(sk: &Skeleton) -> i64 {
    let n = sk.n() as i64;
    let mut excess = 0i64;
    for v in 0..sk.vertex_count {
        let deg = sk.fences.iter().filter(|&&(a, b)| a == v || b == v).count() as i64;
        if deg >= 2 {
            excess += (deg - 2).max(0);
        }
    }
    n - 3 - excess
}

/// Anneal `sk` from `init_coords` and validate the result. Returns
/// `Some((total_area, configuration))` only if
/// `Configuration::validate` actually passes — never reports a number
/// that didn't pass validation.
pub fn anneal_and_validate(
    sk: &Skeleton,
    init_coords: Vec<Point>,
    seed: u64,
    iterations: usize,
) -> Option<(f64, Configuration)> {
    sk.validate_shape().ok()?;
    let params = AnnealParams {
        seed,
        iterations,
        ..AnnealParams::default()
    };
    let result = anneal(sk, init_coords, params);
    let config = sk.to_configuration(&result.coords);
    match config.validate(Tolerance::default()) {
        Ok(report) => Some((report.total_area, config)),
        Err(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn k_min_matches_hand_derivation_at_ground_truth_records() {
        // n=8 (kinked_hexagon_n8): boundary is 6 fences, target 2.0893244080014.
        assert_eq!(k_min(2.0893244080014, 30), Some(6));
        // n=11 (split_hub_pinwheel_n11): boundary is 7 fences, target 3.5372167764.
        assert_eq!(k_min(3.5372167764, 30), Some(7));
        // n=4 trivial square: boundary is all 4 fences, target 1.
        assert_eq!(k_min(1.0, 30), Some(4));
        // n=7 domino: boundary is 6 fences (the 1x2 rectangle's
        // perimeter), target 2.
        assert_eq!(k_min(2.0, 30), Some(6));
        // n=12 trivial 2x2 grid: boundary is 8 fences, target 4.
        assert_eq!(k_min(4.0, 30), Some(8));
        // n=18: boundary_polygon_bound(9) = 9*cot(pi/9)/4 is EXACTLY the
        // recorded area (6.18182+), saturated with zero slack.
        assert_eq!(k_min(6.18182, 30), Some(9));
        assert!(boundary_polygon_bound(9) - 6.18182 < 0.001);
    }

    #[test]
    fn n4_trivial_square_needs_no_interior_fences() {
        let (sk, coords) = BoundaryBuilder::new(4).finish();
        assert_eq!(sk.n(), 4);
        let (area, _) = anneal_and_validate(&sk, coords, 0, 5_000)
            .expect("regular unit square should already validate");
        assert!((area - 1.0).abs() < 1e-6, "area = {area}");
    }

    #[test]
    fn n7_domino_via_direct_chord_between_antipodal_boundary_vertices() {
        // Boundary: regular unit hexagon, k = k_min(2.0) = 6. Interior:
        // one direct chord between the two antipodal vertices (3 apart
        // in the 6-cycle) — mirrors the ground-truth domino skeleton's
        // interior fence connecting two boundary vertices directly (no
        // fresh vertex). The regular-hexagon guess has antipodal
        // distance 2, far from the required 1; annealing must deform
        // the whole boundary into the true (non-regular, flattened)
        // hexagon shape for this to validate at all.
        let mut b = BoundaryBuilder::new(6);
        b.direct_chord(1, 4);
        let (sk, coords) = b.finish();
        sk.validate_shape().unwrap();
        assert_eq!(sk.n(), 7);
        // Vertices 1 and 4 each go from degree 2 (two boundary fences)
        // to degree 3 (plus the direct chord): excess 1 each, total 2.
        assert_eq!(moduli_dimension(&sk), 7 - 3 - 2);

        let mut best: Option<f64> = None;
        for seed in 0..8 {
            if let Some((area, _)) = anneal_and_validate(&sk, coords.clone(), seed, 150_000) {
                best = Some(best.map_or(area, |b: f64| b.max(area)));
            }
        }
        let area = best.expect("at least one seed should validate");
        assert!((area - 2.0).abs() < 1e-3, "area = {area}, expected 2.0");
    }

    #[test]
    fn n8_kinked_hexagon_via_boundary_seed_two_interior_tjunction_chords() {
        // Boundary: regular unit hexagon, k = k_min(2.0893...) = 6.
        // Interior: mirrors kinked_hexagon_n8's PL/PR/M structure
        // exactly — PL and PR are each *purely* T-junction landing
        // points (no separate anchor fence; the PL-PR chord itself is
        // their only fence, degree 1 discharged solely by the
        // T-junction record, matching the ground-truth skeleton), and
        // M is a third fresh vertex T-junctioned onto the interior of
        // the PL-PR chord, connected to boundary vertex BA (index 3).
        let mut b = BoundaryBuilder::new(6);
        // Boundary vertices 0..6 in order (0=APEX); fences 0..6 the
        // same order (fence i = (i, i+1 mod 6)); BA = index 3.
        let pl = b.fresh_t_junction_vertex(0, 0.4); // lands on fence 0 (APEX-SL)
        let pr = b.fresh_t_junction_vertex(5, 0.6); // lands on fence 5 (SR-APEX)
        b.direct_chord(pl, pr);
        let pl_pr_fence = b.fences.len() - 1;
        b.t_junction_chord(3, pl_pr_fence, 0.5); // BA -> lands mid PL-PR

        let (sk, coords) = b.finish();
        sk.validate_shape().unwrap();
        assert_eq!(sk.n(), 8);

        let mut best: Option<f64> = None;
        for seed in 0..8 {
            if let Some((area, _)) = anneal_and_validate(&sk, coords.clone(), seed, 200_000) {
                best = Some(best.map_or(area, |b: f64| b.max(area)));
            }
        }
        let area = best.expect("at least one seed should validate");
        assert!(
            (area - 2.0893244080014).abs() < 1e-2,
            "area = {area}, expected ~2.0893"
        );
    }

    #[test]
    fn n12_grid_via_boundary_seed_shared_hub_vertex() {
        // Boundary: regular unit OCTAGON, k = k_min(4.0) = 8. Interior:
        // ONE shared hub vertex, connected by 4 fences to 4 alternating
        // boundary vertices — the vertex-SHARING pattern (9 distinct
        // vertices for 12 fences) that `random_growth` (0/200) and the
        // outer-Metropolis-SA (89.5% of target) both failed to find,
        // because neither ever reuses a freshly created vertex across
        // multiple new fences.
        let mut b = BoundaryBuilder::new(8);
        let hub = b.shared_vertex_chord(1, Point::new(0.0, 0.0));
        b.direct_chord(3, hub);
        b.direct_chord(5, hub);
        b.direct_chord(7, hub);

        let (sk, coords) = b.finish();
        sk.validate_shape().unwrap();
        assert_eq!(sk.n(), 12);
        // Hub vertex has degree 4 (excess 2). Each of the 4 spoke
        // boundary vertices (1,3,5,7) goes from degree 2 to degree 3
        // (excess 1 each, total 4). Combined excess 6.
        assert_eq!(moduli_dimension(&sk), 12 - 3 - 6);

        let mut best: Option<f64> = None;
        for seed in 0..8 {
            if let Some((area, _)) = anneal_and_validate(&sk, coords.clone(), seed, 300_000) {
                best = Some(best.map_or(area, |b: f64| b.max(area)));
            }
        }
        let area = best.expect("at least one seed should validate");
        assert!((area - 4.0).abs() < 1e-3, "area = {area}, expected 4.0");
    }

    #[test]
    fn n11_split_hub_via_boundary_seed_three_way_coincidence() {
        // Boundary: regular unit HEPTAGON, k = k_min(3.5372167764) = 7.
        // Interior: mirrors split_hub_pinwheel_n11 exactly — three fresh
        // T-junction pendants (Q1, Q2, F), each landing on a distinct
        // boundary fence, all sharing ONE ordinary-corner hub vertex H2
        // (the m=3 coincidence from `docs/asymmetric-methods.md` §1.3);
        // plus a fourth chord C-H1, both pure T-junction pendants, with
        // H1 landing on the *interior* of the Q1-H2 fence (a T-junction
        // onto an interior fence, not a boundary one).
        let mut b = BoundaryBuilder::new(7);
        // Boundary vertices/fences 0..7 in order.
        let q1 = b.fresh_t_junction_vertex(5, 0.5); // lands on fence 5
        let h2 = b.shared_vertex_chord(q1, Point::new(0.1, 0.1)); // fence (q1,h2)
        let q1_h2_fence = b.fences.len() - 1;
        let q2 = b.fresh_t_junction_vertex(3, 0.5); // lands on fence 3
        b.direct_chord(q2, h2);
        let f = b.fresh_t_junction_vertex(1, 0.5); // lands on fence 1
        b.direct_chord(f, h2);
        let c = b.fresh_t_junction_vertex(6, 0.5); // lands on fence 6
        let h1 = b.fresh_t_junction_vertex(q1_h2_fence, 0.5); // lands on interior of Q1-H2
        b.direct_chord(c, h1);

        let (sk, coords) = b.finish();
        sk.validate_shape().unwrap();
        assert_eq!(sk.n(), 11);
        // H2 has degree 3 (excess 1) — the single m=3 coincidence;
        // every other vertex stays at degree <= 2. dim = 11-3-1 = 7,
        // matching `docs/asymmetric-methods.md` §1.3's measured value
        // for the real split-hub skeleton exactly.
        assert_eq!(moduli_dimension(&sk), 11 - 3 - 1);

        let mut best: Option<f64> = None;
        for seed in 0..12 {
            if let Some((area, _)) = anneal_and_validate(&sk, coords.clone(), seed, 300_000) {
                best = Some(best.map_or(area, |b: f64| b.max(area)));
            }
        }
        let area = best.expect("at least one seed should validate");
        assert!(
            (area - 3.5372167764).abs() < 1e-2,
            "area = {area}, expected ~3.5372167764"
        );
    }
}
