//! Optimizer-vs-table validation: run the annealer (not hand-coded
//! coordinates) on structured skeleton generators and check it recovers
//! known record areas through the real evaluator
//! ([`Configuration::validate`]), not just the annealer's internal
//! penalty score. This is the correctness test for `anneal`/`skeleton`/
//! `search`: if the optimizer can't rediscover the trivial cases it has
//! no business being trusted on the open ones.

use motif_fences::anneal::{anneal, AnnealParams};
use motif_fences::skeleton::{grid, hexagon_with_spokes, regular_polygon};
use motif_fences::Tolerance;

fn assert_recovers(
    skeleton: motif_fences::skeleton::Skeleton,
    init_coords: Vec<motif_fences::Point>,
    seed: u64,
    expected_area: f64,
) {
    let params = AnnealParams {
        seed,
        ..AnnealParams::default()
    };
    let result = anneal(&skeleton, init_coords, params);
    let config = skeleton.to_configuration(&result.coords);
    let report = config
        .validate(Tolerance::default())
        .unwrap_or_else(|v| panic!("optimizer result did not validate: {v:?}"));
    assert!(
        (report.total_area - expected_area).abs() < 1e-4,
        "total_area = {}, expected {}",
        report.total_area,
        expected_area
    );
}

#[test]
fn recovers_triangle_n3() {
    let (sk, coords) = regular_polygon(3);
    assert_recovers(sk, coords, 1, 3f64.sqrt() / 4.0);
}

#[test]
fn recovers_square_n4() {
    let (sk, coords) = regular_polygon(4);
    assert_recovers(sk, coords, 1, 1.0);
}

#[test]
fn recovers_domino_n7() {
    let (sk, coords) = grid(2, 1);
    assert_recovers(sk, coords, 1, 2.0);
}

#[test]
fn recovers_hexagon_spokes_n9() {
    let (sk, coords) = hexagon_with_spokes(&[0, 2, 4]);
    assert_recovers(sk, coords, 1, 3.0 * 3f64.sqrt() / 2.0);
}

#[test]
fn recovers_grid_2x2_n12() {
    let (sk, coords) = grid(2, 2);
    assert_recovers(sk, coords, 1, 4.0);
}
