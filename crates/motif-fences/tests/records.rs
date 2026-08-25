//! Hand-encoded constructions for known/conjectured fence-packing records,
//! checked against Erich Friedman's table
//! (<https://erich-friedman.github.io/packing/fence/>).

use motif_fences::{Configuration, Tolerance};
use std::f64::consts::PI;

fn assert_area(config: &Configuration, expected_area: f64, expected_fields: usize) {
    let report = config
        .validate(Tolerance::default())
        .unwrap_or_else(|violations| {
            panic!("expected a valid configuration, got violations: {violations:?}")
        });
    assert_eq!(report.fence_count, config.fence_count());
    assert_eq!(
        report.field_areas.len(),
        expected_fields,
        "field_areas = {:?}",
        report.field_areas
    );
    assert!(
        (report.total_area - expected_area).abs() < 1e-6,
        "total_area = {}, expected {}",
        report.total_area,
        expected_area
    );
}

/// n=3: a unit equilateral triangle. Area = sqrt(3)/4.
#[test]
fn triangle_n3() {
    let a = (0.0, 0.0);
    let b = (1.0, 0.0);
    let c = (0.5, 3f64.sqrt() / 2.0);
    let config = Configuration::from_coords(&[(a, b), (b, c), (c, a)]);
    assert_area(&config, 3f64.sqrt() / 4.0, 1);
}

/// n=4: a unit square. Area = 1.
#[test]
fn square_n4() {
    let (a, b, c, d) = ((0.0, 0.0), (1.0, 0.0), (1.0, 1.0), (0.0, 1.0));
    let config = Configuration::from_coords(&[(a, b), (b, c), (c, d), (d, a)]);
    assert_area(&config, 1.0, 1);
}

/// n=7: a 1x2 domino of two unit squares sharing an edge. The shared edge
/// is a single fence (both its endpoints already lie on the two
/// perpendicular fences they meet), for 7 fences total (3 per square's
/// remaining sides + 1 shared). Area = 2.
#[test]
fn domino_n7() {
    let p = |x: f64, y: f64| (x, y);
    let segments = [
        (p(0.0, 0.0), p(1.0, 0.0)),
        (p(1.0, 0.0), p(2.0, 0.0)),
        (p(2.0, 0.0), p(2.0, 1.0)),
        (p(2.0, 1.0), p(1.0, 1.0)),
        (p(1.0, 1.0), p(0.0, 1.0)),
        (p(0.0, 1.0), p(0.0, 0.0)),
        (p(1.0, 0.0), p(1.0, 1.0)), // shared middle fence
    ];
    let config = Configuration::from_coords(&segments);
    assert_eq!(config.fence_count(), 7);
    assert_area(&config, 2.0, 2);
}

/// n=12: a 2x2 grid of unit squares (3x3 lattice of points, 12 unit
/// edges: 2 rows of 3 horizontal-run edges... concretely, the standard
/// grid graph). Area = 4.
#[test]
fn grid_2x2_n12() {
    let mut segments = Vec::new();
    // 3x3 grid of points at integer coordinates 0..=2.
    // Horizontal unit edges: for each row y in 0..=2, x in 0..2.
    for y in 0..=2 {
        for x in 0..2 {
            segments.push(((x as f64, y as f64), (x as f64 + 1.0, y as f64)));
        }
    }
    // Vertical unit edges: for each column x in 0..=2, y in 0..2.
    for x in 0..=2 {
        for y in 0..2 {
            segments.push(((x as f64, y as f64), (x as f64, y as f64 + 1.0)));
        }
    }
    let config = Configuration::from_coords(&segments);
    assert_eq!(config.fence_count(), 12);
    assert_area(&config, 4.0, 4);
}

/// n=9: a regular unit-side hexagon with 3 spokes from the center to
/// alternating vertices.
///
/// Sanity check baked into the construction: a regular hexagon's
/// circumradius equals its side length, so a unit-side hexagon's center
/// is exactly distance 1 from every vertex — the spokes are unit length
/// fences, same as the hexagon's sides. Each spoke's center-endpoint
/// lies on the *other* two spokes at their shared center endpoint
/// (endpoints counting as "on" a fence includes a fence's own
/// endpoints), so the "endpoint lies on another fence" rule is satisfied
/// there too. The spokes to alternating vertices split the hexagon into
/// 3 congruent kite-shaped fields (2 hexagon sides + 2 spokes each) of
/// area (hexagon area)/3 each, comfortably under the area <= 1 bound.
/// Area = 3*sqrt(3)/2.
#[test]
fn hexagon_with_spokes_n9() {
    let center = (0.0, 0.0);
    let vertices: Vec<(f64, f64)> = (0..6)
        .map(|k| ((k as f64) * PI / 3.0).cos())
        .zip((0..6).map(|k| ((k as f64) * PI / 3.0).sin()))
        .collect();

    // Sanity check the geometric claim the construction depends on:
    // circumradius (center to vertex) equals side length, both unit.
    for &v in &vertices {
        let r = (v.0 * v.0 + v.1 * v.1).sqrt();
        assert!((r - 1.0).abs() < 1e-9, "circumradius should be 1, got {r}");
    }
    for i in 0..6 {
        let a = vertices[i];
        let b = vertices[(i + 1) % 6];
        let side = ((a.0 - b.0).powi(2) + (a.1 - b.1).powi(2)).sqrt();
        assert!((side - 1.0).abs() < 1e-9, "side should be 1, got {side}");
    }

    let mut segments: Vec<((f64, f64), (f64, f64))> = (0..6)
        .map(|i| (vertices[i], vertices[(i + 1) % 6]))
        .collect();
    // Spokes to alternating vertices (0, 2, 4).
    for &i in &[0, 2, 4] {
        segments.push((center, vertices[i]));
    }
    let config = Configuration::from_coords(&segments);
    assert_eq!(config.fence_count(), 9);
    assert_area(&config, 3.0 * 3f64.sqrt() / 2.0, 3);
}

/// n=18: a regular unit-side 9-gon (area 9*cot(pi/9)/4, matching the
/// record's exact-area expression exactly — that expression is precisely
/// the closed-form area of a regular 9-gon of side 1) with 9 additional
/// unit fences subdividing it so every field has area <= 1.
///
/// This crate does NOT claim a construction for the 9 additional fences.
/// The 9-gon's circumradius is 1/(2*sin(pi/9)) ~ 1.4619, so — unlike the
/// n=9 hexagon case — spokes from the center to the vertices are *not*
/// unit length, and no other unit-length subdivision that (a) keeps
/// every endpoint incident to another fence and (b) splits the 9-gon
/// into <=1-area fields was found or sourced (Friedman's page attributes
/// this record to Maurizio Morandi but its page provides only a
/// rendered image, not coordinates, and no textual description of the
/// subdivision was recoverable). Rather than fabricate coordinates that
/// would only coincidentally validate, this is left an open,
/// intentionally-ignored test: filling it in requires either sourcing
/// the actual construction or independently deriving a valid one.
#[test]
#[ignore = "no sourced or independently-derived construction for the 9 extra fences; see doc comment"]
fn regular_9gon_with_subdivision_n18() {
    unimplemented!("open: what are the 9 additional unit fences that subdivide the 9-gon?")
}
