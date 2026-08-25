//! Hand-encoded constructions for known/conjectured fence-packing records,
//! checked against Erich Friedman's table
//! (<https://erich-friedman.github.io/packing/fence/>).

use motif_fences::skeleton::{polyomino, Skeleton};
use motif_fences::{Configuration, Point, Tolerance};
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

/// n=11: the "split hub" asymmetric pinwheel, reproducing the published
/// record (Teodor Tohanean, area 3.53721+) to the precision recovered by
/// a numeric solve (SLSQP from a traced initial guess; see
/// `docs/asymmetric-methods.md` for the derivation and open questions).
///
/// Skeleton: a unit-edge heptagon B-E-G-R-S1-S2-D-B (7 boundary fences,
/// ordinary corners throughout) plus 4 interior unit chords, each one
/// endpoint at a boundary vertex and the other landing by T-junction:
/// C-H1 (C T-junctions onto D-B), Q1-H2 (Q1 T-junctions onto S2-D),
/// Q2-H2 (Q2 T-junctions onto S1-R), F-H2 (F T-junctions onto G-E). H2 is
/// a genuine 3-way endpoint coincidence (Q1, Q2, F chords share it as an
/// ordinary corner, no extra T-junction bookkeeping needed per
/// `skeleton.rs`'s dimension-neutral-corner rule). H1 is an ordinary
/// T-junction: it is C's chord's only endpoint, and it T-junctions onto
/// the *interior* of Q1's chord (fence Q1-H2), not onto the boundary.
///
/// 13 vertices, 11 fences, 4 bounded faces: one quadrilateral
/// (C-H1-Q1-D) and three others, three of which sit exactly at the
/// area-1 cap at the optimum (the fourth, the quadrilateral, is the
/// residual 0.5372...).
#[test]
fn split_hub_pinwheel_n11() {
    // Vertex order: B, E, G, R, S1, S2, D, C, Q1, Q2, F, H1, H2.
    const B: usize = 0;
    const E: usize = 1;
    const G: usize = 2;
    const R: usize = 3;
    const S1: usize = 4;
    const S2: usize = 5;
    const D: usize = 6;
    const C: usize = 7;
    const Q1: usize = 8;
    const Q2: usize = 9;
    const F: usize = 10;
    const H1: usize = 11;
    const H2: usize = 12;

    let coords_raw: [(f64, f64); 13] = [
        (0.0, 0.0),                                 // B
        (1.0, 0.0),                                 // E
        (1.823186950926246, 0.5677704147142139),    // G
        (1.5451976715140148, 1.5283545914170518),   // R
        (0.8079995672096562, 2.2040312559616106),   // S1
        (-0.07392359713025984, 1.7326380737870366), // S2
        (-0.534630666826967, 0.845085824096082),    // D
        (-0.2368227699437535, 0.3743435947856081),  // C
        (-0.20976669066959178, 1.4709363305184016), // Q1
        (1.3210722790920153, 1.7337760333703467),   // Q2
        (1.250166787118965, 0.17254561714132796),   // F
        (0.45144652866934915, 1.0997988812000283),  // H1
        (0.662256483448314, 0.9814717416038052),    // H2
    ];
    let coords: Vec<Point> = coords_raw.iter().map(|&(x, y)| Point::new(x, y)).collect();

    let fences = vec![
        (B, E),   // 0: boundary
        (E, G),   // 1: boundary; F T-junctions onto this
        (G, R),   // 2: boundary
        (R, S1),  // 3: boundary; Q2 T-junctions onto this
        (S1, S2), // 4: boundary
        (S2, D),  // 5: boundary; Q1 T-junctions onto this
        (D, B),   // 6: boundary; C T-junctions onto this
        (C, H1),  // 7: interior chord
        (Q1, H2), // 8: interior chord; H1 T-junctions onto this
        (Q2, H2), // 9: interior chord, shares H2 endpoint with fence 8
        (F, H2),  // 10: interior chord, shares H2 endpoint with fences 8, 9
    ];

    let t_junctions = vec![
        (C, 6),  // C's chord endpoint lands on D-B
        (Q1, 5), // Q1's chord endpoint lands on S2-D
        (Q2, 3), // Q2's chord endpoint lands on R-S1
        (F, 1),  // F's chord endpoint lands on E-G
        (H1, 8), // H1 lands on the interior of Q1-H2
    ];

    let skeleton = Skeleton {
        vertex_count: 13,
        fences,
        t_junctions,
    };
    skeleton.validate_shape().unwrap();
    assert_eq!(skeleton.n(), 11);

    let config = skeleton.to_configuration(&coords);
    assert_area(&config, 3.5372167764, 4);
}

/// n=15: the P-pentomino (5 cells: a 2x2 block plus one cell on top of
/// the left column), the trivial minimum-edge polyomino for A=5. Unlike
/// n=4/7/10/12/17/22/24 (all rectangle-shaped for their A), A=5 has no
/// edge-minimal *rectangle* (a 1x5 strip needs 16 edges, not 15) — the
/// minimum-edge shape is this non-rectangular polyomino instead, which
/// `skeleton::grid` cannot express (see `skeleton::polyomino`). Area = 5.
#[test]
fn p_pentomino_n15() {
    let cells = [(0, 0), (1, 0), (0, 1), (1, 1), (0, 2)];
    let (sk, coords) = polyomino(&cells);
    assert_eq!(sk.n(), 15);
    let config = sk.to_configuration(&coords);
    assert_area(&config, 5.0, 5);
}

/// n=20: a 3x3 square of cells with two opposite corners removed, the
/// trivial minimum-edge polyomino for A=7 (again non-rectangular: a 1x7
/// strip needs 22 edges — that's the *n=22* record, A=8 — and no
/// rectangle factors 7 more squarely). Area = 7.
#[test]
fn notched_square_n20() {
    let cells = [(1, 0), (2, 0), (0, 1), (1, 1), (2, 1), (0, 2), (1, 2)];
    let (sk, coords) = polyomino(&cells);
    assert_eq!(sk.n(), 20);
    let config = sk.to_configuration(&coords);
    assert_area(&config, 7.0, 7);
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

/// n=8: the "kinked hexagon" construction, reproducing the published
/// record (Daniel Mathias, 2.08932+) to the precision recovered by a
/// numeric solve (SLSQP from a traced initial guess, then verified
/// through `Configuration::validate`).
///
/// Skeleton: a hexagonal boundary Apex-SL-BL-BA-BR-SR-Apex (6 fences,
/// ordinary corners throughout) plus 2 interior chords. The horizontal
/// chord PL-PR does *not* run between the shoulder vertices — pixel
/// inspection of the record image shows a kink partway up each
/// apex-shoulder edge, and both of the chord's endpoints land by
/// T-junction on the *interior* of those edges (at parameter ~0.531 from
/// the apex). The vertical chord BA-M runs from the bottom apex up to a
/// third T-junction M on the interior of PL-PR (at its midpoint, by
/// symmetry).
///
/// That distinction is load-bearing, not cosmetic: tying the chord
/// directly to the shoulder vertices instead makes the skeleton rigid
/// (finitely many real solutions, best total area 1.860038), well short
/// of the record. The T-junction version has one genuine continuous
/// modulus, and its critical point is the record.
///
/// 9 vertices, 8 fences, 3 bounded faces. Unusually for these records,
/// **no** area-cap constraint is active at the optimum: the two
/// pentagons sit at 0.99969 (close to, but strictly under, 1) and the
/// top triangle at 0.08995. The optimum is a smooth critical point on
/// the 1-parameter equality manifold, not a boundary point — re-solving
/// with the area caps dropped entirely reproduces the same solution, and
/// forcing a pentagon to exactly 1 gives a strictly lower total.
#[test]
fn kinked_hexagon_n8() {
    // Vertex order: Apex, SL, SR, BL, BR, BA, PL, PR, M.
    const APEX: usize = 0;
    const SL: usize = 1;
    const SR: usize = 2;
    const BL: usize = 3;
    const BR: usize = 4;
    const BA: usize = 5;
    const PL: usize = 6;
    const PR: usize = 7;
    const M: usize = 8;

    let coords_raw: [(f64, f64); 9] = [
        (0.0, 1.1799004013071016),                   // Apex
        (-0.9409471268040679, 0.8413468650542507),   // SL
        (0.9409471268040679, 0.8413468650542507),    // SR
        (-0.9875080549728485, -0.15756858139242782), // BL
        (0.9875080549728485, -0.15756858139242782),  // BR
        (0.0, 0.0),                                  // BA
        (-0.5, 1.0),                                 // PL
        (0.5, 1.0),                                  // PR
        (0.0, 1.0),                                  // M
    ];
    let coords: Vec<Point> = coords_raw.iter().map(|&(x, y)| Point::new(x, y)).collect();

    let fences = vec![
        (APEX, SL), // 0: boundary; PL T-junctions onto this
        (SL, BL),   // 1: boundary
        (BL, BA),   // 2: boundary
        (BA, BR),   // 3: boundary
        (BR, SR),   // 4: boundary
        (SR, APEX), // 5: boundary; PR T-junctions onto this
        (PL, PR),   // 6: horizontal interior chord; M T-junctions onto this
        (BA, M),    // 7: vertical interior chord
    ];

    let t_junctions = vec![
        (PL, 0), // PL lands on the interior of Apex-SL
        (PR, 5), // PR lands on the interior of SR-Apex
        (M, 6),  // M lands on the interior of PL-PR
    ];

    let skeleton = Skeleton {
        vertex_count: 9,
        fences,
        t_junctions,
    };
    skeleton.validate_shape().unwrap();
    assert_eq!(skeleton.n(), 8);

    let config = skeleton.to_configuration(&coords);
    assert_area(&config, 2.0893244027, 3);
}
