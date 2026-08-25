use motif_fences::bounds::{is_convex_polygon, BIEBERBACH_AREA_THRESHOLD};
use motif_fences::build_arrangement;
use motif_fences::skeleton::Skeleton;
use motif_fences::{Configuration, Point};

fn survey(name: &str, config: &Configuration) {
    let arr = build_arrangement(&config.segments, 1e-6, 1e-7);
    println!("== {name} ({} faces) ==", arr.bounded_faces.len());
    for (i, f) in arr.bounded_faces.iter().enumerate() {
        let convex = is_convex_polygon(&f.boundary, 1e-9);
        let qualifies = f.area > BIEBERBACH_AREA_THRESHOLD && convex;
        println!(
            "  face {i}: area={:.6} convex={} qualifies={} verts={}",
            f.area,
            convex,
            qualifies,
            f.boundary.len()
        );
        if qualifies {
            try_chord(&format!("    {name} face {i} chord"), &f.boundary);
        }
    }
}

fn main() {
    demo_chords();
}

fn demo_chords() {
    // n=9 hexagon + spokes
    {
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
        let config = Configuration::from_coords(&segments);
        survey("n=9 hexagon+spokes", &config);
    }

    // n=8 kinked hexagon
    {
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
            (0.0, 1.1799003888196817),
            (-0.940947139421975, 0.8413468763381202),
            (0.940947139421975, 0.8413468763381202),
            (-0.9875080474158787, -0.1575685764639594),
            (0.9875080474158787, -0.1575685764639594),
            (0.0, 0.0),
            (-0.5, 1.0),
            (0.5, 1.0),
            (0.0, 1.0),
        ];
        let coords: Vec<Point> = coords_raw.iter().map(|&(x, y)| Point::new(x, y)).collect();
        let fences = vec![
            (APEX, SL),
            (SL, BL),
            (BL, BA),
            (BA, BR),
            (BR, SR),
            (SR, APEX),
            (PL, PR),
            (BA, M),
        ];
        let t_junctions = vec![(PL, 0), (PR, 5), (M, 6)];
        let skeleton = Skeleton {
            vertex_count: 9,
            fences,
            t_junctions,
        };
        skeleton.validate_shape().unwrap();
        let config = skeleton.to_configuration(&coords);
        survey("n=8 kinked hexagon", &config);
    }

    // n=11 split hub
    {
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
            (0.0, 0.0),
            (1.0, 0.0),
            (1.823186950926246, 0.5677704147142139),
            (1.5451976715140148, 1.5283545914170518),
            (0.8079995672096562, 2.2040312559616106),
            (-0.07392359713025984, 1.7326380737870366),
            (-0.534630666826967, 0.845085824096082),
            (-0.2368227699437535, 0.3743435947856081),
            (-0.20976669066959178, 1.4709363305184016),
            (1.3210722790920153, 1.7337760333703467),
            (1.250166787118965, 0.17254561714132796),
            (0.45144652866934915, 1.0997988812000283),
            (0.662256483448314, 0.9814717416038052),
        ];
        let coords: Vec<Point> = coords_raw.iter().map(|&(x, y)| Point::new(x, y)).collect();
        let fences = vec![
            (B, E),
            (E, G),
            (G, R),
            (R, S1),
            (S1, S2),
            (S2, D),
            (D, B),
            (C, H1),
            (Q1, H2),
            (Q2, H2),
            (F, H2),
        ];
        let t_junctions = vec![(C, 6), (Q1, 5), (Q2, 3), (F, 1), (H1, 8)];
        let skeleton = Skeleton {
            vertex_count: 13,
            fences,
            t_junctions,
        };
        skeleton.validate_shape().unwrap();
        let config = skeleton.to_configuration(&coords);
        survey("n=11 split hub", &config);
    }

    // n=13 grid wedge (our skeleton, NOT the record)
    {
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
            (-1.1567560360, 0.9876373551),
            (-0.1567560360, 0.9876373551),
            (0.8421883010, 0.9417003158),
            (1.1786411435, 0.0),
            (0.8421883010, -0.9417003158),
            (-0.1567560360, -0.9876373551),
            (-1.1567560360, -0.9876373551),
            (-1.0, 0.0),
            (0.0, 0.0),
            (1.0, 0.0),
            (1.0, 0.5),
            (1.0, -0.5),
        ];
        let coords: Vec<Point> = coords_raw.iter().map(|&(x, y)| Point::new(x, y)).collect();
        let fences = vec![
            (TL, TM),
            (TM, TR),
            (TR, P),
            (P, BR),
            (BR, BM),
            (BM, BL),
            (BL, LM),
            (LM, TL),
            (LM, C),
            (C, RM),
            (TM, C),
            (C, BM),
            (UT, LT),
        ];
        let t_junctions = vec![(RM, 12), (UT, 2), (LT, 3)];
        let skeleton = Skeleton {
            vertex_count: 12,
            fences,
            t_junctions,
        };
        skeleton.validate_shape().unwrap();
        let config = skeleton.to_configuration(&coords);
        survey("n=13 grid wedge (our skeleton, not the record)", &config);
    }
}

fn poly_diam_pair(boundary: &[Point]) -> (usize, usize, f64) {
    let n = boundary.len();
    let mut best = (0, 0, 0.0f64);
    for i in 0..n {
        for j in (i + 1)..n {
            let d = ((boundary[i].x - boundary[j].x).powi(2)
                + (boundary[i].y - boundary[j].y).powi(2))
            .sqrt();
            if d > best.2 {
                best = (i, j, d);
            }
        }
    }
    best
}

/// Find a boundary point Q (on some edge, possibly exactly at a vertex)
/// with |P0 - Q| = 1, excluding P0's own two face-boundary neighbors
/// (which are guaranteed distance 1 already, via the existing boundary
/// fences themselves — a "chord" to one of them would just duplicate an
/// edge already there, not add anything). A solution landing exactly on
/// some OTHER vertex is fine and valid (an endpoint coinciding with an
/// existing vertex still "lies on another fence"); only the two adjacent
/// ones are excluded. Scans the whole boundary loop (not just up to the
/// diameter partner), inclusive of edge endpoints, and returns every
/// valid candidate found (a face can have more than one).
fn find_chord(boundary: &[Point], p0_idx: usize) -> Vec<(Point, usize, f64)> {
    let n = boundary.len();
    let p0 = boundary[p0_idx];
    let prev = boundary[(p0_idx + n - 1) % n];
    let next = boundary[(p0_idx + 1) % n];
    let is_excluded = |q: Point| -> bool {
        let close = |a: Point, b: Point| ((a.x - b.x).powi(2) + (a.y - b.y).powi(2)).sqrt() < 1e-6;
        close(q, prev) || close(q, next) || close(q, p0)
    };
    let mut out = Vec::new();
    for k in 0..n {
        let i = (p0_idx + k) % n;
        let j = (p0_idx + k + 1) % n;
        let a = boundary[i];
        let b = boundary[j];
        // |a + t*(b-a) - p0|^2 = 1, solve quadratic in t over [0,1]
        let dx = b.x - a.x;
        let dy = b.y - a.y;
        let ex = a.x - p0.x;
        let ey = a.y - p0.y;
        let aa = dx * dx + dy * dy;
        let bb = 2.0 * (ex * dx + ey * dy);
        let cc = ex * ex + ey * ey - 1.0;
        let disc = bb * bb - 4.0 * aa * cc;
        if disc < 0.0 {
            continue;
        }
        let sq = disc.sqrt();
        for t in [(-bb + sq) / (2.0 * aa), (-bb - sq) / (2.0 * aa)] {
            if (-1e-9..=1.0 + 1e-9).contains(&t) {
                let tc = t.clamp(0.0, 1.0);
                let q = Point::new(a.x + tc * dx, a.y + tc * dy);
                if !is_excluded(q) {
                    out.push((q, i, tc));
                }
            }
        }
    }
    out
}

fn try_chord(name: &str, boundary: &[Point]) {
    let (i, j, diam) = poly_diam_pair(boundary);
    println!("{name}: diam={diam:.6} between verts {i},{j}");
    let candidates = find_chord(boundary, i);
    if !candidates.is_empty() {
        for (q, edge_i, t) in &candidates {
            println!(
                "  [from diam vert {i}] chord P0={:?} -> Q={:?} (edge starting at vert {edge_i}, t={t:.6}), len={:.8}",
                boundary[i],
                q,
                ((boundary[i].x - q.x).powi(2) + (boundary[i].y - q.y).powi(2)).sqrt()
            );
        }
        return;
    }
    println!("  no non-degenerate chord starting from diam vert {i}; trying every vertex...");
    let mut found_any = false;
    for k in 0..boundary.len() {
        let cs = find_chord(boundary, k);
        for (q, edge_i, t) in cs {
            found_any = true;
            println!(
                "  [from vert {k}] chord P0={:?} -> Q={:?} (edge starting at vert {edge_i}, t={t:.6}), len={:.8}",
                boundary[k],
                q,
                ((boundary[k].x - q.x).powi(2) + (boundary[k].y - q.y).powi(2)).sqrt()
            );
        }
    }
    if !found_any {
        println!("  NO CHORD FOUND FROM ANY VERTEX -- genuine counterexample candidate");
    }
}
