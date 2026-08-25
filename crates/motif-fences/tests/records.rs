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
/// Friedman's page attributes the record to Maurizio Morandi but
/// provides only a rendered image (`18.gif`), no coordinates and no
/// textual description; a web search for a source description (a paper,
/// forum post, or packomania-style page) turned up nothing. Rather than
/// fabricate coordinates that would only coincidentally validate, this
/// is left an open, intentionally-ignored test.
///
/// What *is* now established, from tracing `18.gif` (VERIFIED against
/// the image) plus closed-form geometry (DERIVED):
///
/// - The exact area match forces the boundary to be *exactly* the
///   regular unit-side 9-gon: interior chords never change total
///   enclosed area (it's always exactly the boundary polygon's own
///   shoelace area), and for a polygon with fixed unit side lengths the
///   regular (cyclic, equal-angle) polygon is the *unique* area
///   maximizer — so any valid construction's boundary must be that
///   exact 9-gon, not merely close to it. Spokes from its center to its
///   vertices are *not* unit length (circumradius 1/(2 sin(pi/9)) ~
///   1.4619 =/= 1), unlike the n=9 hexagon case, so the extra 9 fences
///   can't be a simple center-spoke wheel.
/// - The image has a vertical mirror symmetry (confirmed from multiple
///   clean pixel coordinate pairs) and its interior reads as a small
///   triangular hub near (not at) the center, with 6 more chords running
///   from 6 of the 9 boundary vertices in to the hub — i.e. exactly the
///   combinatorial family `skeleton::hub_polygon(9, 3, outer_spokes)`
///   already provides, with `outer_spokes` pairing consecutive boundary
///   vertices onto each hub edge:
///   `[(0,0),(1,0),(3,1),(4,1),(6,2),(7,2)]` (skipping vertices 2, 5, 8,
///   which read as spoke-free plain corners in the image — this matches
///   `hub_polygon_shape_is_valid` in `skeleton.rs`'s tests, which was
///   already anticipating this exact skeleton).
/// - **That specific skeleton is infeasible, not merely unsolved
///   (DERIVED, checked by direct computation, not just unproven).**
///   Under the mirror-symmetric ansatz the hub triangle's position
///   reduces to one continuous parameter (its offset along the axis of
///   symmetry). The two apex-adjacent boundary vertices' spokes and the
///   four side-vertex spokes' T-junction landing points are only
///   simultaneously realizable (both real and within their target
///   edge's segment) for that parameter in roughly [0.24, 0.34] (hub
///   edge length units, circumradius 1.4619). Across that entire window
///   the top face (apex + 2 boundary edges + 2 spokes + hub's top edge)
///   has area 1.30-1.56, and a side face has area 1.36-1.49 — both
///   *always* exceeding the area-1 cap by 30-55%, checked by explicit
///   shoelace computation at 2% steps through the window, not just at
///   its ends. A free-standing search (letting one spoke's landing point
///   range over its full reachable unit circle, ignoring the other
///   spokes' constraints) shows the top face *can* drop under area 1,
///   but only if the hub sits far outside that window (around parameter
///   0.5) — i.e. the top-face and side-face requirements pull the hub's
///   position in incompatible directions. This isn't a numerical-solver
///   failure to converge; it's a 1-parameter family with an explicitly
///   computed, everywhere-infeasible image.
///
/// What remained open at that point: the trace above (a small triangular
/// hub with 6 spokes) turned out to be a **misread of the image**, not
/// the true construction — see `regular_9gon_split_diagonal_hub_n18`
/// below for the corrected trace, which matches the record exactly.
/// This proven-infeasible variant is kept as a documented negative
/// result (it rules out that one specific spoke-to-hub-edge assignment,
/// still a useful fact) but no longer represents the crate's best
/// understanding of `18.gif`.
#[test]
#[ignore = "superseded: this specific hub_polygon(9,3,6-spoke) reading of 18.gif is proven infeasible (see doc comment) and was also a misread of the image — see regular_9gon_split_diagonal_hub_n18 for the corrected trace, which matches the record"]
fn regular_9gon_with_subdivision_n18() {
    unimplemented!("superseded, see regular_9gon_split_diagonal_hub_n18")
}

/// n=18: the corrected trace of `18.gif`, matching the published record
/// (Maurizio Morandi, 6.18182+ = `9*cot(pi/9)/4`) exactly.
///
/// The boundary is the regular unit-side 9-gon forced by the exact area
/// match (see `regular_9gon_with_subdivision_n18`'s doc comment for that
/// derivation, unchanged). The interior is **not** a small hub polygon
/// with spokes converging on it (that reading was traced from the image
/// but proven infeasible, and — independently — was a misread: a
/// careful re-trace at 10-25x pixel zoom, following the repo's tracing
/// protocol, shows no small closed hub at all). The actual interior
/// structure, mirror-symmetric about the vertical axis through the apex
/// `v0` and the midpoint of the opposite edge `v4-v5`:
///
/// - Three boundary edges per side carry a T-junction each (6 total,
///   mirror pairs): on `v0-v1`/`v0-v8` (near the apex), on `v2-v3`/`v6-v7`,
///   and on `v3-v4`/`v5-v6`. Each spawns one interior fence.
/// - `h_end_l`-`h_end_r`: a single **horizontal, on-axis-centered**
///   interior fence (`H`), an ordinary corner at each end (not a
///   T-junction) — the two apex-adjacent T-junction fences (`j12`-`m`,
///   `j4`-`j7`) land on `H`'s *interior* as T-junctions at `m` and `j7`.
/// - `h_end_l`-`c` and `h_end_r`-`c`: two more interior fences
///   ("diagonals") running from `H`'s two endpoints down to a single
///   shared interior point `c`, which sits exactly on the mirror axis.
///   The `v2-v3`/`v6-v7`-anchored T-junction fences (`j0`-`j11`,
///   `j9`-`j13`) land on these diagonals' interiors (at `j11`, `j13`).
/// - `j6`-`c` and `j10`-`c`: the `v3-v4`/`v5-v6`-anchored T-junction
///   fences run straight to `c` themselves (ordinary corner, not a
///   T-junction).
/// - `c` is thus a 4-way ordinary-corner coincidence (both diagonals and
///   both of these last two fences share that one endpoint) — costing
///   `4-2=2` moduli dimensions (`docs/asymmetric-methods.md` §1.3); with
///   `n=18` that leaves `18-3-2=13` moduli, comfortably positive, so the
///   skeleton has real room to satisfy every field's area cap (unlike
///   the disproven hub reading, whose 1-parameter family was
///   *everywhere* infeasible).
///
/// This gives exactly 9 interior fences (2+2+2+1+2 across the 5 kinds
/// above) forming 7 bounded faces total (Euler check: 22 vertices, 28
/// edges after subdividing at every T-junction/corner, 8 faces
/// including the unbounded one), each `<=1`; the two largest sit right
/// at `0.9956`, i.e. near, not at, the cap (unlike the n=11 record,
/// where 3 of 4 faces sit exactly *at* the cap at its optimum) — this
/// particular numeric solve did not attempt to prove this is *the*
/// area-maximizing configuration for this skeleton (no multi-start,
/// unlike n=11's later Jacobian-rank check), only that it validates.
///
/// Traced from `18.gif` (184x180px) via skeletonize + junction-cluster +
/// branch-walk + a from-scratch pixel/line-fit pass (the repo's existing
/// `trace2-4.py`/`analyze.py` scripts undercounted this skeleton's real
/// junction structure), boundary vertices fit to the exact regular 9-gon
/// by least-squares against 3 independently-traced pixel points
/// (residual ~0.04px), then solved: T-junction fractions and the free
/// interior points (`h_end_l`, `c`) refined by `scipy.optimize.SLSQP`
/// from the pixel-traced initial guess, satisfying the 5 remaining unit-
/// length equality constraints (boundary is closed-form; T-junction
/// collinearity is enforced by construction via each point's fraction
/// along its target fence) while minimizing the two over-cap faces'
/// excess — landing all faces safely `<1`. Scratch solve scripts:
/// `/tmp/fences-verify-n18/solve4.py` (feasibility) and `solve5.py`
/// (face-area minimization).
#[test]
fn regular_9gon_split_diagonal_hub_n18() {
    let v0 = Point::new(1.4619022000815, 0.0000000000000);
    let v1 = Point::new(0.5222095792956, 0.3420201433257);
    let v2 = Point::new(0.0222095792956, 1.2080455471101);
    let v3 = Point::new(0.1958577569626, 2.1928533001223);
    let v4 = Point::new(0.9619022000815, 2.8356409098089);
    let v5 = Point::new(1.9619022000815, 2.8356409098089);
    let v6 = Point::new(2.7279466432005, 2.1928533001223);
    let v7 = Point::new(2.9015948208675, 1.2080455471101);
    let v8 = Point::new(2.4015948208675, 0.3420201433257);
    let j12 = Point::new(0.9157227562649, 0.1987930601173);
    let j4 = Point::new(2.0080816438982, 0.1987930601173);
    let j0 = Point::new(0.1022827626416, 1.6621631360589);
    let j9 = Point::new(2.8215216375215, 1.6621631360589);
    let j6 = Point::new(0.5808761249775, 2.5159220707201);
    let j10 = Point::new(2.3429282751856, 2.5159220707201);
    let m = Point::new(1.1241592641019, 1.1768289603790);
    let j7 = Point::new(1.7996451360612, 1.1768289603790);
    let h_end_l = Point::new(0.9619022000815, 1.1768289603790);
    let h_end_r = Point::new(1.9619022000815, 1.1768289603790);
    let j11 = Point::new(1.0371459727647, 1.3071549976195);
    let j13 = Point::new(1.8866584273983, 1.3071549976195);
    let c = Point::new(1.4619022000815, 2.0428543641635);

    let coords = vec![
        v0, v1, v2, v3, v4, v5, v6, v7, v8, j12, j4, j0, j9, j6, j10, m, j7, h_end_l, h_end_r, j11,
        j13, c,
    ];

    const V0: usize = 0;
    const V1: usize = 1;
    const V2: usize = 2;
    const V3: usize = 3;
    const V4: usize = 4;
    const V5: usize = 5;
    const V6: usize = 6;
    const V7: usize = 7;
    const V8: usize = 8;
    const J12: usize = 9;
    const J4: usize = 10;
    const J0: usize = 11;
    const J9: usize = 12;
    const J6: usize = 13;
    const J10: usize = 14;
    const M: usize = 15;
    const J7: usize = 16;
    const HENDL: usize = 17;
    const HENDR: usize = 18;
    const J11: usize = 19;
    const J13: usize = 20;
    const C: usize = 21;

    let fences = vec![
        (V0, V1),
        (V1, V2),
        (V2, V3),
        (V3, V4),
        (V4, V5),
        (V5, V6),
        (V6, V7),
        (V7, V8),
        (V8, V0),
        (J12, M),
        (J4, J7),
        (J0, J11),
        (J9, J13),
        (J6, C),
        (J10, C),
        (HENDL, HENDR),
        (HENDL, C),
        (HENDR, C),
    ];
    let t_junctions = vec![
        (J12, 0),
        (J4, 8),
        (J0, 2),
        (J9, 6),
        (J6, 3),
        (J10, 5),
        (M, 15),
        (J7, 15),
        (J11, 16),
        (J13, 17),
    ];

    let sk = Skeleton {
        vertex_count: 22,
        fences,
        t_junctions,
    };
    sk.validate_shape().unwrap();
    assert_eq!(sk.n(), 18);

    let config = sk.to_configuration(&coords);
    assert_area(&config, 9.0 / 4.0 / (PI / 9.0).tan(), 7);
}

/// n=8: the "kinked hexagon" construction, reproducing the published
/// record (Daniel Mathias, 2.08932+) at total area 2.0893244080014,
/// verified through `Configuration::validate`.
///
/// The area is an exact algebraic number: a smooth interior critical point of
/// the (unit-length + T-junction) equality-constrained area function, no
/// area-cap active. Its exact minimal polynomial over ℚ — degree 24,
/// irreducible, root-matched to 580+ digits beyond the precision used to find
/// it — is derived in `docs/asymmetric-methods.md` §8.2, along with a
/// 100-digit decimal `2.0893244080014165918046324322618127695067429339652509...`.
/// Whether the degree-24 extension is solvable in radicals is open (no
/// available tool computes Galois groups above degree 6).
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
/// of the record.
///
/// Moduli dimension 4, measured: the constraint Jacobian (8 unit-length
/// plus 3 collinearity equations against 18 raw coordinates) has clean
/// rank 11 — smallest singular value 0.648, no near-zero tail — and
/// 18 - 11 - 3 rigid motions = 4. That confirms `docs/asymmetric-methods.md`
/// §1.3's `n - 3 - sum(m_i - 2)` rule, which predicts 8 - 3 - 1 = 4 from the
/// single degree-3 coincidence at BA. Rank is 11 at 40 random points of the
/// constraint variety too, so the count is structural rather than an artifact
/// of the symmetric point.
///
/// The mirror symmetry here is **emergent, not imposed**. It was originally
/// found under a symmetry ansatz, which is the failure mode that cost n=13
/// (see §7) — but unlike n=13, that ansatz left a live modulus (the symmetric
/// stratum is 1-dimensional inside the 4-dimensional space, matching the
/// tangent space's 1-symmetric + 3-antisymmetric decomposition). It was then
/// checked without the ansatz: 480 symmetry-breaking multistarts over all 18
/// free coordinates, 362 feasible convergences, **all 362** returning to this
/// configuration and **none** exceeding it. Because the objective and
/// constraints are symmetric, a symmetric point is automatically critical in
/// every antisymmetric direction, so criticality alone would prove nothing;
/// the reduced Hessian settles it, with eigenvalues -1.398 (symmetric) and
/// -0.869, -0.508, -0.016 (antisymmetric) — negative definite, a strict local
/// maximum rather than a saddle.
///
/// 9 vertices, 8 fences, 3 bounded faces. Unusually for these records,
/// **no** area-cap constraint is active at the optimum: the two
/// pentagons sit at 0.99969 (slack 3.1e-4) and the top triangle at
/// 0.08995. The optimum is a smooth interior critical point, not a
/// boundary point — re-solving with the area caps dropped entirely
/// reproduces the same solution, and forcing a pentagon to exactly 1
/// gives a strictly lower total.
///
/// Scope: this is a strict local maximum *on this skeleton*. It says
/// nothing about other n=8 skeletons.
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
        (0.0, 1.1799003888196817),                  // Apex
        (-0.940947139421975, 0.8413468763381202),   // SL
        (0.940947139421975, 0.8413468763381202),    // SR
        (-0.9875080474158787, -0.1575685764639594), // BL
        (0.9875080474158787, -0.1575685764639594),  // BR
        (0.0, 0.0),                                 // BA
        (-0.5, 1.0),                                // PL
        (0.5, 1.0),                                 // PR
        (0.0, 1.0),                                 // M
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
    assert_area(&config, 2.0893244080014, 3);
}

/// n=13: the "grid wedge" — a 2x2 arrangement of fields whose right side
/// closes to a wedge/arrowhead instead of a flat edge.
///
/// This is a verified-valid configuration at total area 4.0645952819. It
/// is **not** the published record (Bram Cohen, 4.07361+), which it falls
/// short of by 0.0090 (0.22%). It is encoded here because the
/// configuration itself is real and reproducible, and because the *reason*
/// it falls short is a method finding worth keeping: it was solved under
/// an imposed exact-mirror-symmetry ansatz, which left effectively zero
/// free moduli against this skeleton's true moduli dimension of **5**
/// (`n - 3` corrected by §1.3's coincidence rule). See
/// `docs/asymmetric-methods.md` §7 for the write-up and §8 for the count,
/// and the rule it generalizes to.
///
/// Skeleton: an octagonal boundary TL-TM-TR-P-BR-BM-BL-LM-TL (8 fences).
/// The top, bottom, and left "edges" each look like a single straight
/// 2-unit run in the record image, but a fence is exactly unit length, so
/// each is really two collinear (or, on the left, slightly bent) unit
/// fences meeting at a midpoint vertex — TM, BM, LM respectively. Those
/// midpoint vertices are ordinary shared corners, not T-junctions. Two
/// interior dividers cross at the center C: the horizontal LM-C, C-RM and
/// the vertical TM-C, C-BM. The 13th fence is the chord UT-LT spanning
/// the wedge; the horizontal divider's right end RM lands by T-junction on
/// that chord's interior (at its midpoint, by symmetry).
///
/// The fence budget forces this: 8 boundary, plus 2 horizontal-divider
/// halves, plus 2 vertical-divider halves, is 12 — leaving exactly one. A
/// point-hub reading of the right-side cluster — RM as an ordinary 3-way
/// vertex with separate unit spokes RM-UT and RM-LT — needs a 14th fence and
/// so is not available at n=13 at all. This is a stronger conclusion than
/// n=11's split-beats-hub comparison: here the hub variant is infeasible
/// on budget, not merely worse.
///
/// 13 vertices, 13 fences, 5 bounded faces (the visual read of "4 fields"
/// misses the small triangle at the wedge tip). Active area caps at the
/// optimum: the two pentagons, exactly at 1. The two quads (0.9876) and
/// the tip triangle (0.0893) have slack.
#[test]
fn grid_wedge_n13() {
    const TL: usize = 0;
    const TM: usize = 1;
    const TR: usize = 2;
    const P: usize = 3;
    const BR: usize = 4;
    const BM: usize = 5;
    const BL: usize = 6;
    const LM: usize = 7;
    const C: usize = 8;
    const RM: usize = 9;
    const UT: usize = 10;
    const LT: usize = 11;

    let coords_raw: [(f64, f64); 12] = [
        (-1.1567560360, 0.9876373551),  // TL
        (-0.1567560360, 0.9876373551),  // TM
        (0.8421883010, 0.9417003158),   // TR
        (1.1786411435, 0.0),            // P (wedge tip)
        (0.8421883010, -0.9417003158),  // BR
        (-0.1567560360, -0.9876373551), // BM
        (-1.1567560360, -0.9876373551), // BL
        (-1.0, 0.0),                    // LM
        (0.0, 0.0),                     // C
        (1.0, 0.0),                     // RM
        (1.0, 0.5),                     // UT
        (1.0, -0.5),                    // LT
    ];
    let coords: Vec<Point> = coords_raw.iter().map(|&(x, y)| Point::new(x, y)).collect();

    let fences = vec![
        (TL, TM), // 0: boundary
        (TM, TR), // 1: boundary
        (TR, P),  // 2: boundary; UT T-junctions onto this
        (P, BR),  // 3: boundary; LT T-junctions onto this
        (BR, BM), // 4: boundary
        (BM, BL), // 5: boundary
        (BL, LM), // 6: boundary
        (LM, TL), // 7: boundary
        (LM, C),  // 8: horizontal divider, left half
        (C, RM),  // 9: horizontal divider, right half
        (TM, C),  // 10: vertical divider, top half
        (C, BM),  // 11: vertical divider, bottom half
        (UT, LT), // 12: the wedge chord; RM T-junctions onto this
    ];

    let t_junctions = vec![
        (RM, 12), // RM lands on the interior of the UT-LT chord
        (UT, 2),  // UT lands on the interior of TR-P
        (LT, 3),  // LT lands on the interior of P-BR
    ];

    let skeleton = Skeleton {
        vertex_count: 12,
        fences,
        t_junctions,
    };
    skeleton.validate_shape().unwrap();
    assert_eq!(skeleton.n(), 13);

    let config = skeleton.to_configuration(&coords);
    assert_area(&config, 4.0645952819, 5);

    // Explicitly record the gap: this is a valid configuration, not the
    // published record.
    let published_record = 4.07361;
    let report = config.validate(Tolerance::default()).unwrap();
    assert!(
        report.total_area < published_record,
        "if this ever exceeds the published record, the record table or this \
         construction changed — investigate, do not silently update"
    );
}
