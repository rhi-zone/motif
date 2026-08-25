//! Planar arrangement construction and bounded-face extraction.
//!
//! Given a set of unit segments ("fences"), this module:
//! 1. finds every point where two fences meet (proper crossings, and
//!    endpoints landing on another fence's interior — the common
//!    T-junction case for this problem),
//! 2. merges near-duplicate points into a single vertex,
//! 3. splits each original fence into sub-edges between consecutive
//!    vertices lying on it,
//! 4. traces the faces of the resulting planar straight-line graph, and
//! 5. reports which of those faces are bounded (finite-area) rather than
//!    the single unbounded outer face.
//!
//! Face tracing uses the standard "next edge in angular order" walk over
//! directed edges (a minimal DCEL-style traversal): at each vertex, the
//! next edge of the current face is the neighbor immediately following
//! the edge just arrived from, in counterclockwise angular order around
//! that vertex. Every directed edge belongs to exactly one traced face;
//! for a connected planar graph this produces exactly `E - V + 2` faces,
//! of which exactly one — identified by its signed (shoelace) area having
//! the opposite sign from the rest — is the unbounded outer face. Pendant
//! ("dangling") edges are automatically absorbed into whichever face
//! walks up and back down them, contributing zero net signed area, so
//! they don't need special-casing.

use crate::geometry::{Point, Segment};
use std::collections::HashSet;

/// A bounded face of the arrangement, described by its boundary vertices
/// in traversal order (not necessarily convex; may be non-simple only in
/// the degenerate pendant-edge sense described above).
#[derive(Debug, Clone)]
pub struct Face {
    pub boundary: Vec<Point>,
    pub area: f64,
}

/// The full arrangement: all vertices, all sub-edges, and the extracted
/// bounded faces.
#[derive(Debug, Clone)]
pub struct Arrangement {
    pub vertices: Vec<Point>,
    /// Sub-edges as vertex-index pairs (undirected, deduplicated).
    pub edges: Vec<(usize, usize)>,
    pub bounded_faces: Vec<Face>,
}

/// Merge a raw point into `vertices`, returning its index. Points within
/// `tol` of an existing vertex are treated as the same vertex.
fn merge_vertex(vertices: &mut Vec<Point>, p: Point, tol: f64) -> usize {
    for (i, v) in vertices.iter().enumerate() {
        if v.dist(p) <= tol {
            return i;
        }
    }
    vertices.push(p);
    vertices.len() - 1
}

/// Build the planar arrangement of `segments` and extract its bounded
/// faces.
///
/// `incidence_tol` is used both as the point-to-segment distance
/// tolerance (for deciding whether a point lies on a segment) and, in
/// parameter space (`incidence_tol / segment length`), as the slack
/// allowed when deciding whether a computed line/line intersection falls
/// within the two segments' `[0,1]` ranges. `vertex_merge_tol` is the
/// distance below which two raw points (endpoints or intersections) are
/// merged into a single arrangement vertex.
///
/// Colinear-overlapping segments (two fences lying along the same line
/// with overlapping interiors) are not supported: `Segment::intersect`
/// returns `None` for near-parallel lines, so overlap is silently not
/// turned into shared sub-edges. This is not needed by any construction
/// in this crate's test suite; a future extension would need explicit
/// colinear-overlap handling.
pub fn build_arrangement(
    segments: &[Segment],
    incidence_tol: f64,
    vertex_merge_tol: f64,
) -> Arrangement {
    let n = segments.len();

    // 1. Collect all "cut points" on each segment: its own endpoints,
    // proper crossings with other segments, and any other segment's
    // endpoint that lands on this segment's interior (T-junctions).
    let mut cut_points: Vec<Vec<Point>> =
        (0..n).map(|i| vec![segments[i].a, segments[i].b]).collect();

    for i in 0..n {
        for j in (i + 1)..n {
            let len_i = segments[i].length().max(1e-9);
            let len_j = segments[j].length().max(1e-9);
            let slack = incidence_tol / len_i.min(len_j);
            if let Some(p) = segments[i].intersect(&segments[j], slack) {
                cut_points[i].push(p);
                cut_points[j].push(p);
            }
        }
    }
    // T-junctions: endpoint of one segment lying on another segment's
    // interior, which the line/line intersection above already covers
    // in the generic (non-parallel) case, but we also check explicitly
    // here so a near-parallel-but-touching-at-an-endpoint configuration
    // (e.g. two fences meeting end-to-end) is never missed.
    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            for &p in &[segments[i].a, segments[i].b] {
                if segments[j].contains_point(p, incidence_tol) {
                    cut_points[j].push(p);
                }
            }
        }
    }

    // 2. Merge all raw points into a global, deduplicated vertex set.
    let mut vertices: Vec<Point> = Vec::new();
    let mut cut_indices: Vec<Vec<usize>> = Vec::with_capacity(n);
    for pts in &cut_points {
        let idxs: Vec<usize> = pts
            .iter()
            .map(|&p| merge_vertex(&mut vertices, p, vertex_merge_tol))
            .collect();
        cut_indices.push(idxs);
    }

    // 3. For each segment, sort its cut vertices along the segment and
    // connect consecutive distinct vertices into sub-edges.
    let mut edge_set: HashSet<(usize, usize)> = HashSet::new();
    for (i, seg) in segments.iter().enumerate() {
        let mut idxs = cut_indices[i].clone();
        idxs.sort_by(|&a, &b| {
            let ta = seg.param_of(vertices[a]);
            let tb = seg.param_of(vertices[b]);
            ta.partial_cmp(&tb).unwrap()
        });
        idxs.dedup();
        for w in idxs.windows(2) {
            let (u, v) = (w[0], w[1]);
            if u == v {
                continue;
            }
            edge_set.insert((u.min(v), u.max(v)));
        }
    }
    let edges: Vec<(usize, usize)> = edge_set.into_iter().collect();

    // 4. Build angularly-sorted adjacency lists, then trace faces.
    let vcount = vertices.len();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); vcount];
    for &(u, v) in &edges {
        adj[u].push(v);
        adj[v].push(u);
    }
    for (v, neighbors) in adj.iter_mut().enumerate() {
        let origin = vertices[v];
        neighbors.sort_by(|&a, &b| {
            let angle_a = (vertices[a] - origin).y.atan2((vertices[a] - origin).x);
            let angle_b = (vertices[b] - origin).y.atan2((vertices[b] - origin).x);
            angle_a.partial_cmp(&angle_b).unwrap()
        });
    }

    let mut visited: HashSet<(usize, usize)> = HashSet::new();
    let mut traced_faces: Vec<(Vec<usize>, f64)> = Vec::new();
    for &(a, b) in &edges {
        for &(start_u, start_v) in &[(a, b), (b, a)] {
            if visited.contains(&(start_u, start_v)) {
                continue;
            }
            let mut boundary = Vec::new();
            let mut cur = (start_u, start_v);
            loop {
                visited.insert(cur);
                boundary.push(cur.0);
                let w = cur.1;
                let prev = cur.0;
                let neighbors = &adj[w];
                let idx = neighbors
                    .iter()
                    .position(|&nb| nb == prev)
                    .expect("adjacency is symmetric");
                let next_idx = (idx + 1) % neighbors.len();
                let next_v = neighbors[next_idx];
                cur = (w, next_v);
                if cur == (start_u, start_v) {
                    break;
                }
            }
            let area = signed_area(&boundary, &vertices);
            traced_faces.push((boundary, area));
        }
    }

    // 5. Exactly one traced face is the unbounded outer face; for a
    // connected graph it's the one whose signed area has the opposite
    // sign from the (consistently-oriented) bounded faces. Empirically
    // (verified against the unit-square, and against a two-square
    // domino where the classification actually distinguishes the two
    // bounded squares from the shared outer boundary), the `idx + 1`
    // ("next neighbor counterclockwise from the reverse edge")
    // convention above traces every *bounded* face with a negative
    // signed area and the single unbounded outer face with a positive
    // one — i.e. the walk keeps each bounded face's interior on its
    // right, not its left. So bounded faces are the negative-area ones;
    // we report their area as the (positive) magnitude.
    let bounded_faces: Vec<Face> = traced_faces
        .into_iter()
        .filter(|(_, area)| *area < -1e-9)
        .map(|(boundary, area)| Face {
            boundary: boundary.into_iter().map(|i| vertices[i]).collect(),
            area: -area,
        })
        .collect();

    Arrangement {
        vertices,
        edges,
        bounded_faces,
    }
}

fn signed_area(boundary: &[usize], vertices: &[Point]) -> f64 {
    let mut sum = 0.0;
    for i in 0..boundary.len() {
        let p = vertices[boundary[i]];
        let q = vertices[boundary[(i + 1) % boundary.len()]];
        sum += p.cross(q);
    }
    sum / 2.0
}
