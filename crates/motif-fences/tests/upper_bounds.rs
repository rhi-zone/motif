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
