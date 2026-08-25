//! Systematic backtracking enumeration of the interior-subdivision layer
//! on top of a fixed regular-k-gon boundary (`boundary_subdivision.rs`).
//!
//! `boundary_subdivision.rs` established the mechanism (boundary
//! construction from `k_min`, `BoundaryBuilder` primitives) and verified
//! it against hand-picked, ground-truth-mirroring interior layouts. This
//! module replaces "hand-picked" with "generated": given `k` (boundary
//! size) and `m = n - k` (interior fences to place), it backtracks over
//! every way to add `m` fences one at a time, each fence's two endpoints
//! independently drawn from three "sites":
//!
//! - [`Site::Existing`] — reuse any current vertex (boundary or
//!   already-placed interior).
//! - [`Site::NewT`] — a fresh vertex T-junctioned onto an existing
//!   fence's interior (self-closing: no later reuse required).
//! - [`Site::NewFree`] — a fresh vertex with no T-junction yet, which
//!   **must** be resolved by a later fence reusing it as `Existing`, or
//!   the finished skeleton has a dangling endpoint and
//!   `validate_shape` rejects it.
//!
//! `NewFree` + `NewFree` (both endpoints fresh and free in the same
//! chord) is deliberately excluded: such a fence has no connection to
//! the rest of the graph at creation time, and verifying it will
//! eventually be reachable from the boundary (rather than forming an
//! orphaned sub-component) would need real connectivity tracking this
//! pass doesn't implement. Every combinatorial pattern used in
//! `boundary_subdivision.rs`'s hand-built coverage tests is still
//! reachable: `Existing+Existing` = `direct_chord`, `Existing+NewT` =
//! `t_junction_chord`, `Existing+NewFree` = `shared_vertex_chord`, and
//! `NewT+NewT` (both endpoints land by T-junction on two *different*
//! existing fences, no anchor at all — `split_hub_pinwheel_n11`'s C-H1
//! fence) is a genuinely new case this generator adds that no single
//! existing `BoundaryBuilder` method produces alone.
//!
//! # Pruning
//!
//! 1. At most 2 simultaneously-open `NewFree` pending vertices (chosen
//!    as a reasonable cap, not derived — every ground-truth skeleton
//!    inspected so far never has more than 1 open at a time).
//! 2. After every fence, the moduli-dimension excess (see
//!    `boundary_subdivision::moduli_dimension`) computed from the
//!    *current partial* degree sequence, using the *final* n's `n - 3`
//!    budget — valid because degree (hence excess) is monotonically
//!    non-decreasing as more fences are added, so a branch already over
//!    budget can never recover.
//! 3. A hard cap on total recursive node visits (a runaway-recursion
//!    guard, not a principled bound) — when hit, the search is reported
//!    as truncated/best-effort, never silently treated as exhaustive.
//! 4. At each completed (`remaining == 0`) candidate: `validate_shape`
//!    (rejects any still-dangling `NewFree` vertex), then the
//!    Euler/face-count filter (`bounded_faces = E' - V' + 1` on the
//!    T-junction-resolved graph, `E' = n + t_junctions` (each
//!    T-junction splits its target fence in two), `V' = vertex_count`
//!    unchanged (the T-junction's landing vertex is already counted —
//!    see `bounded_faces`'s doc comment for the ground-truth check that
//!    caught an earlier, wrong version of this formula); reject if
//!    `bounded_faces < target
//!    area`, since every field is capped at area 1 so `total_area <=
//!    bounded_faces` always).
//!
//! Deduplication uses an **exact** key (canonicalized, sorted fence and
//! T-junction lists — see `structural_key`'s doc comment for why a
//! cheaper structural invariant was tried first and rejected: it
//! measurably collapsed genuinely different topologies together and
//! silently dropped one, at both n=7 and n=8). The exact key only
//! merges leaves that are literally identical, so it under-dedupes
//! true isomorphic-but-differently-indexed duplicates (wasted compute,
//! never a wrong or missing answer).

use crate::boundary_subdivision::{anneal_and_validate, BoundaryBuilder};
use crate::configuration::Configuration;
use crate::geometry::Point;
use crate::skeleton::Skeleton;
use std::collections::HashSet;

type DedupKey = (Vec<(usize, usize)>, Vec<(usize, usize)>);

const MAX_PENDING_FREE: usize = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Site {
    Existing(usize),
    NewT(usize),
    NewFree,
}

#[derive(Clone)]
struct State {
    coords: Vec<Point>,
    fences: Vec<(usize, usize)>,
    t_junctions: Vec<(usize, usize)>,
    pending_free: Vec<usize>,
}

/// Partial-skeleton moduli excess (see module docs point 2): sum over
/// vertices of `max(deg - 2, 0)`, computed from the fences placed so
/// far.
fn partial_excess(fences: &[(usize, usize)], vertex_count: usize) -> i64 {
    let mut excess = 0i64;
    for v in 0..vertex_count {
        let deg = fences.iter().filter(|&&(a, b)| a == v || b == v).count() as i64;
        if deg >= 2 {
            excess += deg - 2;
        }
    }
    excess
}

/// Resolve one site against `state`, materializing a fresh vertex (and,
/// for `NewT`, a T-junction record) if needed. Returns the resolved
/// vertex index; the caller is responsible for pushing the eventual
/// fence.
fn resolve(state: &mut State, site: Site) -> usize {
    match site {
        Site::Existing(v) => v,
        Site::NewT(target_fence) => {
            let (a, b) = state.fences[target_fence];
            let guess = state.coords[a] + (state.coords[b] - state.coords[a]).scale(0.5);
            let v = state.coords.len();
            state.coords.push(guess);
            state.t_junctions.push((v, target_fence));
            v
        }
        Site::NewFree => {
            // Placed near the centroid of current coords as a
            // placeholder guess; the annealer moves it freely.
            let cx = state.coords.iter().map(|p| p.x).sum::<f64>() / state.coords.len() as f64;
            let cy = state.coords.iter().map(|p| p.y).sum::<f64>() / state.coords.len() as f64;
            let v = state.coords.len();
            state.coords.push(Point::new(cx * 0.3, cy * 0.3));
            state.pending_free.push(v);
            v
        }
    }
}

/// All candidate sites for one endpoint of the next chord.
fn candidate_sites(state: &State) -> Vec<Site> {
    let mut sites: Vec<Site> = (0..state.coords.len()).map(Site::Existing).collect();
    sites.extend((0..state.fences.len()).map(Site::NewT));
    if state.pending_free.len() < MAX_PENDING_FREE {
        sites.push(Site::NewFree);
    }
    sites
}

/// Result of an exhaustive-or-truncated interior-subdivision search at
/// one `(k, m)`.
pub struct SearchStats {
    pub k: usize,
    pub m: usize,
    pub n: usize,
    pub node_visits: u64,
    pub node_cap_hit: bool,
    pub max_leaves_hit: bool,
    pub raw_candidates: u64,
    pub survived_moduli: u64,
    pub survived_shape_and_euler: u64,
    pub deduped_count: usize,
    pub best_valid_area: Option<f64>,
    pub best_config: Option<Configuration>,
    /// The deduped survivor skeletons themselves, for inspection/
    /// debugging and for a caller that wants to re-anneal with a
    /// different budget than `search`'s built-in screen-then-refine.
    pub survivors: Vec<Skeleton>,
}

/// Dedup key. **Deliberately exact, not a coarse structural invariant**
/// — two earlier attempts at a coarse invariant (degree sequence alone;
/// degree sequence + T-junction-target-type + boundary-chord-span
/// multiset) each measurably collapsed genuinely different,
/// independently realizable topologies into one dedup class and
/// silently dropped one of them (observed directly: the domino's
/// antipodal boundary chord collapsing with the infeasible skip-1 chord
/// at n=7; a majority of n=8's 288 shape/Euler survivors collapsing to
/// only 5 classes, none of which was the real kinked-hexagon pattern).
/// A coarse invariant is *not* actually safe here the way this module's
/// earlier design doc claimed ("never causes a missed topology") — this
/// exact key trades that broken promise for a true one: it
/// canonicalizes each fence to `(min, max)` and sorts the fence and
/// T-junction lists, so it only ever merges leaves whose generated
/// vertex-index-labeled structure is *literally* identical (e.g. the
/// two site-orderings of a single terminal fence with nothing added
/// after it). It deliberately keeps apart two leaves that are truly
/// isomorphic but reached through a different vertex-creation order
/// (their indices differ) — generating and annealing both is wasted
/// compute, never a wrong or missing answer, which is the correctness
/// direction that matters.
fn structural_key(sk: &Skeleton, _k: usize) -> DedupKey {
    let mut fences: Vec<(usize, usize)> = sk
        .fences
        .iter()
        .map(|&(u, v)| (u.min(v), u.max(v)))
        .collect();
    fences.sort_unstable();
    let mut t_junctions = sk.t_junctions.clone();
    t_junctions.sort_unstable();
    (fences, t_junctions)
}

/// `bounded_faces` of the T-junction-resolved planar graph, assuming
/// connectivity (true by construction here: every fence this generator
/// adds touches the already-connected structure via `Existing` or a
/// T-junction landing on an already-connected fence — the excluded
/// `NewFree`+`NewFree` case is exactly the one combination that could
/// break this, which is why it's excluded).
fn bounded_faces(sk: &Skeleton) -> i64 {
    // Each T-junction splits its target fence into 2 edges (+1 edge),
    // using the T-junction's *own* vertex as the split point — that
    // vertex is already counted in `vertex_count` (it's one endpoint of
    // the skeleton's own `t_junctions` pairs, not a fresh point), so V
    // does NOT grow per T-junction. An earlier version of this function
    // added `t_junctions.len()` to both E and V, which is wrong (double
    // counts the landing vertex) and was verified wrong against both
    // ground-truth records before this fix: `kinked_hexagon_n8`
    // (vertex_count=9, t_junctions=3) must give 3 bounded faces —
    // `(8+3) - 9 + 1 = 3`, correct only without the extra `+3` on V;
    // `split_hub_pinwheel_n11` (vertex_count=13, t_junctions=5) must
    // give 4 — `(11+5) - 13 + 1 = 4`, same check. This bug was silently
    // rejecting valid candidates (including the true kinked-hexagon
    // topology) at the Euler filter before it was found.
    let e = sk.n() as i64 + sk.t_junctions.len() as i64;
    let v = sk.vertex_count as i64;
    e - v + 1
}

/// Enumerate + anneal every interior subdivision of a regular unit
/// k-gon boundary reaching `n = k + m` fences, screening candidates with
/// a quick low-iteration anneal and only running the full-budget
/// annealer (needed for a `Configuration::validate`-passing result) on
/// the top `refine_top` candidates by screen score — annealing every
/// single survivor at full budget is not affordable at the sizes this
/// module reaches, so this two-stage approach is the deliberate
/// engineering tradeoff: exhaustiveness (or its absence) is reported at
/// the *combinatorial* level regardless, via `node_cap_hit`.
/// `max_leaves`: once this many deduped complete candidates have been
/// collected, recursion stops entirely (treated the same as
/// `node_cap_hit` — reported, never silently exhaustive). This exists
/// because the screening pass (one cheap anneal per deduped leaf) is
/// the actual runtime bottleneck at larger `m`, not the pure
/// combinatorial recursion — n=8's 288 shape/Euler-surviving candidates
/// alone took several minutes to screen one at a time, so an m large
/// enough to produce thousands of survivors needs this cap to stay
/// within an affordable budget for this pass.
#[allow(clippy::too_many_arguments)]
pub fn search(
    k: usize,
    m: usize,
    target_area: f64,
    node_cap: u64,
    max_leaves: usize,
    refine_top: usize,
    screen_iters: usize,
    refine_iters: usize,
) -> SearchStats {
    let n = k + m;
    let (boundary_sk, boundary_coords) = BoundaryBuilder::new(k).finish();
    let init = State {
        coords: boundary_coords,
        fences: boundary_sk.fences,
        t_junctions: Vec::new(),
        pending_free: Vec::new(),
    };

    let mut stats = SearchStats {
        k,
        m,
        n,
        node_visits: 0,
        node_cap_hit: false,
        max_leaves_hit: false,
        raw_candidates: 0,
        survived_moduli: 0,
        survived_shape_and_euler: 0,
        deduped_count: 0,
        best_valid_area: None,
        best_config: None,
        survivors: Vec::new(),
    };
    let mut leaves: Vec<(Skeleton, Vec<Point>)> = Vec::new();
    let mut seen_keys: HashSet<DedupKey> = HashSet::new();

    recurse(
        &init,
        m,
        n,
        k,
        target_area,
        node_cap,
        max_leaves,
        &mut stats,
        &mut leaves,
        &mut seen_keys,
    );

    // Screen every deduped leaf with a cheap anneal, then fully anneal
    // (and validate) the top `refine_top` by screen score.
    // `refine_top == 0` skips screening/annealing entirely — a
    // combinatorics-only pass, useful for reporting how large the
    // survivor set actually is before spending any annealing budget on
    // it (screening every leaf, not just the refined top, is itself the
    // dominant cost at larger `m` once thousands of leaves survive the
    // moduli/Euler filters).
    let scored: Vec<(f64, usize)> = if refine_top == 0 {
        Vec::new()
    } else {
        let mut scored: Vec<(f64, usize)> = leaves
            .iter()
            .enumerate()
            .map(|(i, (sk, coords))| {
                let params = crate::anneal::AnnealParams {
                    seed: 0,
                    iterations: screen_iters,
                    ..Default::default()
                };
                let result = crate::anneal::anneal(sk, coords.clone(), params);
                (result.final_residuals.area, i)
            })
            .collect();
        scored.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
        scored
    };

    // Seeds 0-1: exact regular-k-gon boundary initial guess. Seeds 2-3:
    // the boundary vertices are pre-jittered (Gaussian, sigma 0.3-0.6)
    // before annealing — real initial-guess diversity, not just a
    // different RNG walk from the same starting shape. Added because a
    // peer flagged that seeding *only* the exact regular polygon risks
    // never finding a genuinely non-convex/reflex optimal boundary even
    // though nothing in the skeleton itself forces convexity (the
    // combinatorial boundary is just a k-cycle; convexity is purely a
    // coordinate/shape question the annealer is free to move away
    // from, given a start that isn't always dead-center in the convex
    // basin).
    for &(_, i) in scored.iter().take(refine_top) {
        let (sk, coords) = &leaves[i];
        for seed in 0..4u64 {
            let init = if seed < 2 {
                coords.clone()
            } else {
                let mut rng = crate::rng::Rng::new(seed);
                let sigma = if seed == 2 { 0.3 } else { 0.6 };
                coords
                    .iter()
                    .enumerate()
                    .map(|(vi, &p)| {
                        if vi < k {
                            Point::new(p.x + rng.gaussian() * sigma, p.y + rng.gaussian() * sigma)
                        } else {
                            p
                        }
                    })
                    .collect()
            };
            if let Some((area, config)) = anneal_and_validate(sk, init, seed, refine_iters) {
                if stats.best_valid_area.is_none_or(|b| area > b) {
                    stats.best_valid_area = Some(area);
                    stats.best_config = Some(config);
                }
            }
        }
    }
    stats.survivors = leaves.iter().map(|(sk, _)| sk.clone()).collect();
    stats
}

#[allow(clippy::too_many_arguments)]
fn recurse(
    state: &State,
    remaining: usize,
    n: usize,
    k: usize,
    target_area: f64,
    node_cap: u64,
    max_leaves: usize,
    stats: &mut SearchStats,
    leaves: &mut Vec<(Skeleton, Vec<Point>)>,
    seen_keys: &mut HashSet<DedupKey>,
) {
    if stats.node_visits >= node_cap {
        stats.node_cap_hit = true;
        return;
    }
    if leaves.len() >= max_leaves {
        stats.max_leaves_hit = true;
        return;
    }
    stats.node_visits += 1;

    if remaining == 0 {
        if !state.pending_free.is_empty() {
            return; // dangling — never valid
        }
        let sk = Skeleton {
            vertex_count: state.coords.len(),
            fences: state.fences.clone(),
            t_junctions: state.t_junctions.clone(),
        };
        if sk.validate_shape().is_err() {
            return;
        }
        // Euler/face-count filter: total_area <= bounded_faces always
        // (every field <= 1), so a candidate that can't even reach
        // `target_area` many bounded faces is provably hopeless.
        if (bounded_faces(&sk) as f64) < target_area - 1e-9 {
            return;
        }
        stats.survived_shape_and_euler += 1;
        let key = structural_key(&sk, k);
        if seen_keys.insert(key) {
            stats.deduped_count += 1;
            leaves.push((sk, state.coords.clone()));
        }
        return;
    }

    let sites = candidate_sites(state);
    for &site_a in &sites {
        for &site_b in &sites {
            if matches!((site_a, site_b), (Site::NewFree, Site::NewFree)) {
                continue;
            }
            stats.raw_candidates += 1;
            let mut next = state.clone();
            let va = resolve(&mut next, site_a);
            let vb = resolve(&mut next, site_b);
            if va == vb {
                continue;
            }
            if next
                .fences
                .iter()
                .any(|&(a, b)| (a, b) == (va, vb) || (a, b) == (vb, va))
            {
                continue;
            }
            next.fences.push((va, vb));
            next.pending_free.retain(|&p| p != va && p != vb);

            let excess = partial_excess(&next.fences, next.coords.len());
            if (n as i64) - 3 - excess < 0 {
                continue;
            }
            stats.survived_moduli += 1;

            recurse(
                &next,
                remaining - 1,
                n,
                k,
                target_area,
                node_cap,
                max_leaves,
                stats,
                leaves,
                seen_keys,
            );
            if stats.node_cap_hit || stats.max_leaves_hit {
                return;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn n7_exhaustive_recovers_domino_area() {
        // k_min(2.0) = 6, m = 1: fully exhaustive at this size (no node
        // cap or leaf cap ever hit for a single-fence interior layer —
        // confirmed separately via `examples/debug_n7.rs`: 168 raw, 150
        // moduli survivors, 126 shape/Euler survivors, 81 exact-dedup
        // topologies, ALL screened, top 12 fully annealed).
        let stats = search(6, 1, 2.0, 5_000_000, 1000, 12, 20_000, 150_000);
        assert!(!stats.node_cap_hit, "n=7 search should be exhaustive");
        assert!(!stats.max_leaves_hit, "n=7 search should be exhaustive");
        let area = stats.best_valid_area.expect("should find a valid config");
        assert!((area - 2.0).abs() < 1e-2, "area = {area}");
    }

    #[test]
    fn n8_search_finds_a_valid_configuration() {
        // k_min(2.0893...) = 6, m = 2. The true exhaustive combinatorial
        // count here is large — 8469 distinct topologies after the
        // moduli/Euler filters (confirmed via
        // `examples/debug_n8.rs`, refine_top=0) — too many to fully
        // screen-and-anneal within a fast test budget, so this
        // deliberately uses a small leaf cap and does NOT assert
        // near-record precision (a leaf-capped, deterministic-order
        // truncation is not guaranteed, and empirically does not
        // reliably, land on the specific kinked-hexagon topology that
        // reaches 2.0893244080014 — that record is independently
        // confirmed via `boundary_subdivision.rs`'s hand-constructed
        // coverage test instead). This test only checks the search
        // mechanism itself produces *some* valid, non-trivial
        // configuration, not that it's exhaustive or near-optimal.
        let stats = search(6, 2, 2.0893244080014, 5_000_000, 100, 10, 5_000, 40_000);
        let area = stats.best_valid_area.expect("should find a valid config");
        assert!(area > 1.5, "area = {area}");
    }
}
