//! Upper bounds on `A(n)`, the maximum total enclosed area achievable with
//! `n` unit fences.
//!
//! Every construction elsewhere in this crate is a *lower* bound (an
//! explicit configuration proving `A(n) >= area`). This module is the
//! complementary direction: functions that prove `A(n) <= bound(n)` for
//! *every* valid configuration, unconditionally (no genericity or
//! skeleton-shape assumption — these bounds hold for the true, unknown
//! optimum, not just for the constructions this crate happens to encode).
//!
//! Full derivations, hypotheses, and status tags (DERIVED / CONJECTURED /
//! VERIFIED) are in `docs/upper-bounds.md`; this module gives only the
//! computable form of each *proved* bound (the conjectured
//! polyomino-ceiling function is included too, clearly marked, purely so
//! it can be tested against the record table — it is not asserted as a
//! theorem anywhere in this module or its tests).

use std::f64::consts::PI;

/// The isoperimetric bound: `A(n) <= n / sqrt(pi)`, unconditionally, for
/// every `n >= 1`.
///
/// Proof sketch (full version in `docs/upper-bounds.md` Theorem 1):
/// total fence length is exactly `n`; every point of the arrangement
/// borders at most two face-sides (bounded or unbounded), so the
/// perimeters of the bounded faces, summed *with the multiplicity each
/// edge contributes to each face's boundary walk*, are at most `2n`;
/// each bounded face's walk-perimeter is at least its measure-theoretic
/// (De Giorgi) perimeter, which by the classical planar isoperimetric
/// inequality is at least `2*sqrt(pi * area)`; and since every field's
/// area is capped at 1, `area <= sqrt(area)`, so summing over fields
/// gives `A(n) <= sum(sqrt(area_i)) <= n / sqrt(pi)`.
///
/// **DERIVED, VERIFIED** — see `docs/upper-bounds.md` §1.
pub fn isoperimetric_bound(n: u32) -> f64 {
    n as f64 / PI.sqrt()
}

/// The boundary-polygon bound: for a configuration whose bounded-face
/// union has a single simple (Jordan) outer boundary built from unit
/// fences, `A(n) <= (n/4) * cot(pi/n)` for `n >= 3`.
///
/// This is the area of the *regular* n-gon with unit sides — the unique
/// area-maximizing simple polygon among all polygons with `n` sides of
/// length 1 (a classical fact: for fixed side lengths in fixed cyclic
/// order, area is maximized by the polygon inscribed in a circle, and
/// equal side lengths force that cyclic polygon to be regular). Interior
/// fences never add area (they only subdivide the region the outer
/// boundary already encloses), so using `k < n` fences on the boundary
/// and the rest as interior scaffolding can only *reduce* achievable
/// area relative to the `k = n` case, which is why `n` (not the unknown
/// true boundary-fence count) is a safe, if often loose, substitute.
///
/// Hypotheses under which this is a valid bound for *every* n-fence
/// configuration (not just ones that happen to look like this) are
/// spelled out in `docs/upper-bounds.md` §4; the short version is that a
/// disconnected/multi-boundary-component configuration is also covered,
/// because the regular-n-gon area function is superadditive on the
/// relevant range (checked numerically for `n` up to 24, not proven in
/// general).
///
/// **DERIVED, VERIFIED for n=3,4 (tight — matches the known optimal
/// triangle and square exactly), otherwise unverified for tightness.**
/// Panics if `n < 3` (no simple polygon has fewer than 3 sides).
pub fn boundary_polygon_bound(n: u32) -> f64 {
    assert!(n >= 3, "a polygon needs at least 3 sides");
    let n = n as f64;
    (n / 4.0) / (PI / n).tan()
}

/// The tighter of the two proved bounds above. Valid for `n >= 3`.
///
/// **DERIVED** (immediate corollary of the two bounds it combines).
pub fn combined_bound(n: u32) -> f64 {
    isoperimetric_bound(n).min(boundary_polygon_bound(n))
}

/// Harary & Harborth's (1976) minimum-edge-count function for a
/// polyomino of `cells` unit squares: `f(cells) = 2*cells +
/// ceil(2*sqrt(cells))`. This is a fact about *square-cell* animals,
/// proved in the literature (Harary & Harborth, "Extremal animals", J.
/// Combin. Inform. System Sci. 1 (1976)) — it is not itself conjectural.
///
/// **DERIVED from the cited literature result** (not re-proved here).
pub fn harary_harborth_min_edges(cells: u32) -> u32 {
    assert!(cells >= 1);
    let s = (cells as f64).sqrt();
    2 * cells + (2.0 * s).ceil() as u32
}

/// The conjectured "polyomino ceiling": `A*(n) = min { cells : f(cells)
/// > n }`, i.e. the smallest cell count a minimum-edge polyomino could
/// exceed `n` fences trying to reach.
///
/// **This function computes a CONJECTURE, not a proved bound.** The
/// conjecture (`A(n) < polyomino_ceiling(n)` for all n) is supported by
/// every known record (n=3..24, all 22 checked in
/// `tests/upper_bounds.rs`) but is missing the step that would make it a
/// theorem: Harary–Harborth bounds edge-minimality only for polyominoes
/// (axis-aligned unit-square cells), and says nothing about arrangements
/// whose fields are non-square or have area below 1 — which is exactly
/// what every open-record configuration (n=11, 13, 14, ...) actually is.
/// See `docs/upper-bounds.md` §5 for the attempted discharging argument,
/// where it breaks, and why closing this gap is the single highest-value
/// remaining target.
pub fn polyomino_ceiling(n: u32) -> u32 {
    let mut cells = 1;
    while harary_harborth_min_edges(cells) <= n {
        cells += 1;
    }
    cells
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn isoperimetric_bound_matches_formula() {
        assert!((isoperimetric_bound(10) - 10.0 / PI.sqrt()).abs() < 1e-12);
    }

    #[test]
    fn boundary_polygon_bound_is_tight_at_n3_and_n4() {
        // Equilateral triangle: area sqrt(3)/4.
        assert!((boundary_polygon_bound(3) - 3f64.sqrt() / 4.0).abs() < 1e-9);
        // Unit square: area 1.
        assert!((boundary_polygon_bound(4) - 1.0).abs() < 1e-9);
    }

    #[test]
    fn combined_bound_picks_the_tighter_side() {
        // Crossover is around n ~ 7.5; check both regimes pick correctly.
        assert!(combined_bound(4) <= boundary_polygon_bound(4) + 1e-9);
        assert!(combined_bound(20) <= isoperimetric_bound(20) + 1e-9);
    }

    #[test]
    fn harary_harborth_matches_known_small_values() {
        // A=1: single cell, 4 edges (f(1)=2+ceil(2)=4).
        assert_eq!(harary_harborth_min_edges(1), 4);
        // A=4: 2x2 block, 12 edges — matches skeleton::polyomino's n=12
        // grid record exactly (see docs/upper-bounds.md and
        // tests/records.rs::grid_2x2_n12).
        assert_eq!(harary_harborth_min_edges(4), 12);
    }
}
