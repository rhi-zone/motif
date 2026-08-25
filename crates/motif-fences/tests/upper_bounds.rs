//! Checks every proved upper bound in `motif_fences::bounds` against the
//! full n=3..24 record table (`/tmp/fence-records.md`), plus a
//! not-asserted informational check of the *conjectured*
//! polyomino-ceiling function.
//!
//! If a record ever violates a bound tagged proved below, that is a bug
//! in the bound (or in this table), not a discovery — see
//! `docs/upper-bounds.md`.

use motif_fences::bounds::{
    boundary_polygon_bound, combined_bound, isoperimetric_bound, polyomino_ceiling,
};
use motif_fences::{Configuration, Tolerance};

/// (n, best known area). Decimal-only entries (no closed form published)
/// use the digits from Friedman's table, which are lower bounds on the
/// true optimum (his site marks them "+").
const RECORDS: &[(u32, f64)] = &[
    (3, 0.4330127019), // sqrt(3)/4
    (4, 1.0),
    (5, 1.0),
    (6, 1.4330127019), // 1 + sqrt(3)/4
    (7, 2.0),
    (8, 2.08932),
    (9, 2.5980762114), // 3*sqrt(3)/2
    (10, 3.0),
    (11, 3.53721),
    (12, 4.0),
    (13, 4.07361),
    (14, 4.66942),
    (15, 5.0),
    (16, 5.53131),
    (17, 6.0),
    (18, 6.18182), // 9*cot(pi/9)/4
    (19, 6.76059),
    (20, 7.0),
    (21, 7.69139),
    (22, 8.0),
    (23, 8.52289),
    (24, 9.0),
];

#[test]
fn every_record_satisfies_the_isoperimetric_bound() {
    for &(n, area) in RECORDS {
        let bound = isoperimetric_bound(n);
        assert!(
            area <= bound + 1e-6,
            "n={n}: record area {area} exceeds isoperimetric bound {bound}"
        );
    }
}

#[test]
fn every_record_satisfies_the_boundary_polygon_bound() {
    for &(n, area) in RECORDS {
        let bound = boundary_polygon_bound(n);
        assert!(
            area <= bound + 1e-6,
            "n={n}: record area {area} exceeds boundary-polygon bound {bound}"
        );
    }
}

#[test]
fn every_record_satisfies_the_combined_bound() {
    for &(n, area) in RECORDS {
        let bound = combined_bound(n);
        assert!(
            area <= bound + 1e-6,
            "n={n}: record area {area} exceeds combined bound {bound}"
        );
    }
}

#[test]
fn boundary_polygon_bound_is_exactly_tight_at_n3_and_n4() {
    let (_, a3) = RECORDS[0];
    let (_, a4) = RECORDS[1];
    assert!((a3 - boundary_polygon_bound(3)).abs() < 1e-6);
    assert!((a4 - boundary_polygon_bound(4)).abs() < 1e-6);
}

/// Informational only: every known record sits strictly below the
/// conjectured polyomino ceiling. This is evidence for the conjecture
/// (22/22 data points, matching the coordinator's independent check),
/// not a proof — see docs/upper-bounds.md §5 for the open gap. Kept as
/// a test (not just a doc claim) so a future record that violates it is
/// caught immediately as the interesting event it would be.
#[test]
fn every_record_sits_below_the_conjectured_polyomino_ceiling() {
    for &(n, area) in RECORDS {
        let ceiling = polyomino_ceiling(n) as f64;
        assert!(
            area < ceiling,
            "n={n}: record area {area} does NOT sit below the conjectured \
             ceiling {ceiling} — this is a counterexample to the conjecture \
             in docs/upper-bounds.md §5, not a bug: investigate before touching this test"
        );
    }
}

/// Prints the full comparison table (bound vs. record vs. slack) for
/// `docs/upper-bounds.md`'s table. Run with `cargo test -q -p
/// motif-fences --test upper_bounds print_bound_table -- --nocapture`.
#[test]
fn print_bound_table() {
    println!(
        "{:>3} | {:>10} | {:>12} | {:>12} | {:>12} | {:>6}",
        "n", "record", "isoperim", "boundary", "combined", "A*(n)"
    );
    for &(n, area) in RECORDS {
        println!(
            "{:>3} | {:>10.5} | {:>12.5} | {:>12.5} | {:>12.5} | {:>6}",
            n,
            area,
            isoperimetric_bound(n),
            boundary_polygon_bound(n),
            combined_bound(n),
            polyomino_ceiling(n)
        );
    }
}

/// docs/upper-bounds.md §5.4.1: the unit square (area 1 > pi/4, convex,
/// diameter sqrt(2) > 1) admits a Bieberbach chord — a unit-length
/// interior fence with both endpoints on its boundary — constructed by
/// the intermediate-value argument of §5.4's theorem. Concretely: from
/// P0 = (0.5, 0) (the bottom side's midpoint), sweeping to Q = (1, t) on
/// the right side, |P0 Q|^2 = 0.25 + t^2 = 1 gives t = sqrt(3)/2, a
/// genuine T-junction (0 < t < 1), not a vertex. Adding this chord to the
/// square yields a valid 5-fence configuration with the same total area
/// (interior chords only subdivide, per §4.1) — a constructive proof that
/// A(5) >= A(4) = 1, and it happens to match the n=5 record (also 1)
/// exactly, not just bound it from below.
#[test]
fn square_plus_bieberbach_chord_n5_matches_record() {
    let p = |x: f64, y: f64| (x, y);
    let t = 3f64.sqrt() / 2.0;
    let segments = [
        (p(0.0, 0.0), p(1.0, 0.0)),
        (p(1.0, 0.0), p(1.0, 1.0)),
        (p(1.0, 1.0), p(0.0, 1.0)),
        (p(0.0, 1.0), p(0.0, 0.0)),
        (p(0.5, 0.0), p(1.0, t)), // the Bieberbach chord
    ];
    let config = Configuration::from_coords(&segments);
    let report = config
        .validate(Tolerance::default())
        .unwrap_or_else(|violations| {
            panic!("expected a valid configuration, got violations: {violations:?}")
        });
    assert_eq!(report.fence_count, 5);
    assert_eq!(
        report.field_areas.len(),
        2,
        "chord should split the square in two"
    );
    assert!(
        (report.total_area - 1.0).abs() < 1e-9,
        "total_area = {}, expected 1.0 (n=5 record)",
        report.total_area
    );
}

/// docs/upper-bounds.md §5.4.3: the n=8 record's own pentagon face
/// (area 0.999687, convex) admits a genuine T-junction Bieberbach chord —
/// unlike the n=4 square case, this one lands in the *interior* of an
/// existing boundary fence (SR-BR), not at a vertex, demonstrating the
/// theorem's constructive step on a non-square, non-regular face. The
/// new fence connects M=(0,1) (the n=8 skeleton's existing horizontal-
/// chord T-junction point) to a new T-junction point on fence SR-BR.
/// This gives a valid 9-fence configuration with the same total area
/// as the n=8 record — a constructive proof that A(9) >= A(8) via the
/// record's own construction, not just via a trivial polyomino cell.
#[test]
fn kinked_hexagon_plus_bieberbach_chord_n9_matches_area() {
    let p = |x: f64, y: f64| (x, y);
    let apex = p(0.0, 1.1799003888196817);
    let sl = p(-0.940947139421975, 0.8413468763381202);
    let sr = p(0.940947139421975, 0.8413468763381202);
    let bl = p(-0.9875080474158787, -0.1575685764639594);
    let br = p(0.9875080474158787, -0.1575685764639594);
    let ba = p(0.0, 0.0);
    let pl = p(-0.5, 1.0);
    let pr = p(0.5, 1.0);
    let m = p(0.0, 1.0);
    // The Bieberbach chord: found by the general search in
    // examples/scratch_bieberbach_survey.rs, landing on the interior of
    // fence SR-BR at parameter ~0.1588 from SR.
    let q = p(0.9483398612403985, 0.6827437824367476);
    let segments = [
        (apex, sl),
        (sl, bl),
        (bl, ba),
        (ba, br),
        (br, sr),
        (sr, apex),
        (pl, pr),
        (ba, m),
        (m, q), // the Bieberbach chord
    ];
    let config = Configuration::from_coords(&segments);
    let report = config
        .validate(Tolerance::default())
        .unwrap_or_else(|violations| {
            panic!("expected a valid configuration, got violations: {violations:?}")
        });
    assert_eq!(report.fence_count, 9);
    assert!(
        (report.total_area - 2.0893244080014).abs() < 1e-6,
        "total_area = {}, expected 2.0893244080014 (n=8 record's own area, unchanged by subdivision)",
        report.total_area
    );
}

/// docs/upper-bounds.md §5.4.3: the n=9 hexagon+spokes record's own
/// rhombus fields (area 0.866025, convex) also admit a Bieberbach chord
/// — but this is the "degenerate-witness" sub-case the survey uncovered:
/// the field's own four sides are already unit fences (two hexagon
/// sides, two spokes), so sweeping from the diameter-realizing vertex
/// finds *only* its two existing neighbors at distance 1 (would
/// duplicate an edge already there). A valid, non-duplicate chord still
/// exists — but as a vertex-to-vertex "free diagonal" (center to the
/// non-adjacent hexagon vertex, both already-existing points,
/// coincidentally at distance exactly 1), found only by trying a
/// *different* starting vertex, not the diameter pair. See
/// docs/upper-bounds.md §5.4.3 for why this means the theorem's clean
/// single-vertex proof needs the caveat spelled out there.
#[test]
fn hexagon_with_spokes_plus_bieberbach_diagonal_n10_matches_area() {
    let center = (0.0, 0.0);
    let vertices: Vec<(f64, f64)> = (0..6)
        .map(|k| ((k as f64) * std::f64::consts::PI / 3.0).cos())
        .zip((0..6).map(|k| ((k as f64) * std::f64::consts::PI / 3.0).sin()))
        .collect();
    let mut segments: Vec<((f64, f64), (f64, f64))> = (0..6)
        .map(|i| (vertices[i], vertices[(i + 1) % 6]))
        .collect();
    for &i in &[0, 2, 4] {
        segments.push((center, vertices[i]));
    }
    // The Bieberbach "free diagonal": center to hexagon vertex 1 (not a
    // spoke target), both already-existing points, distance exactly 1
    // (hexagon circumradius). Splits one rhombus field into two
    // triangles.
    segments.push((center, vertices[1]));
    let config = Configuration::from_coords(&segments);
    let report = config
        .validate(Tolerance::default())
        .unwrap_or_else(|violations| {
            panic!("expected a valid configuration, got violations: {violations:?}")
        });
    assert_eq!(report.fence_count, 10);
    assert!(
        (report.total_area - 3.0 * 3f64.sqrt() / 2.0).abs() < 1e-9,
        "total_area = {}, expected 3*sqrt(3)/2 (n=9 record's own area, unchanged by subdivision)",
        report.total_area
    );
}

/// docs/upper-bounds.md §5.4.3: the n=11 split-hub record (the actual
/// published record, not a weaker skeleton) has three fields at exactly
/// the area-1 cap; one of them (bounded by fence F's chord and others)
/// admits a genuine T-junction Bieberbach chord found directly from its
/// diameter-realizing vertex (no fallback needed, unlike n=9). New fence:
/// from F=(1.250166787118965, 0.17254561714132796) to a new T-junction
/// point. Constructive proof that A(12) >= A(11) via the actual record,
/// not a weaker skeleton.
#[test]
fn split_hub_pinwheel_plus_bieberbach_chord_n12_matches_area() {
    let p = |x: f64, y: f64| (x, y);
    let b = p(0.0, 0.0);
    let e = p(1.0, 0.0);
    let g = p(1.823186950926246, 0.5677704147142139);
    let r = p(1.5451976715140148, 1.5283545914170518);
    let s1 = p(0.8079995672096562, 2.2040312559616106);
    let s2 = p(-0.07392359713025984, 1.7326380737870366);
    let d = p(-0.534630666826967, 0.845085824096082);
    let c = p(-0.2368227699437535, 0.3743435947856081);
    let q1 = p(-0.20976669066959178, 1.4709363305184016);
    let q2 = p(1.3210722790920153, 1.7337760333703467);
    let f = p(1.250166787118965, 0.17254561714132796);
    let h1 = p(0.45144652866934915, 1.0997988812000283);
    let h2 = p(0.662256483448314, 0.9814717416038052);
    // The Bieberbach chord: found by the general search in
    // examples/scratch_bieberbach_survey.rs, from F, landing by
    // T-junction on the interior of an existing boundary fence.
    let q = p(1.6756728741338502, 1.0775011795383336);
    let segments = [
        (b, e),
        (e, g),
        (g, r),
        (r, s1),
        (s1, s2),
        (s2, d),
        (d, b),
        (c, h1),
        (q1, h2),
        (q2, h2),
        (f, h2),
        (f, q), // the Bieberbach chord
    ];
    let config = Configuration::from_coords(&segments);
    let report = config
        .validate(Tolerance::default())
        .unwrap_or_else(|violations| {
            panic!("expected a valid configuration, got violations: {violations:?}")
        });
    assert_eq!(report.fence_count, 12);
    assert!(
        (report.total_area - 3.5372167764).abs() < 1e-6,
        "total_area = {}, expected 3.5372167764 (n=11 record's own area, unchanged by subdivision)",
        report.total_area
    );
}
