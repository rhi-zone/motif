//! Combinatorial skeletons: the discrete "which endpoint lands where"
//! structure that stays fixed while the continuous optimizer
//! (`anneal.rs`) searches for coordinates. This is the machine-readable
//! form the family-mining half of the task needs — a skeleton plus its
//! solved coordinates fully describes a construction's incidence
//! structure, independent of the particular numbers found.
//!
//! Grounded in `docs/asymmetric-methods.md`:
//! - §1.1: a fixed skeleton has `n - 3` moduli (generic case).
//! - §1.2: a vertex shared by >= 2 fences as an endpoint ("ordinary
//!   corner") discharges the incidence rule for free — no T-junction
//!   bookkeeping needed.
//! - §1.3: a single point where >= 3 fence-ends coincide is
//!   over-determined generically (excess `m - 2` equations) and is only
//!   realizable for special symmetric ansätze — so skeleton builders
//!   here default to *not* producing such hubs unless a caller
//!   explicitly asks for one (`hub_polygon` with `spoke_share_vertex:
//!   false`, or the m=6 exact case).
//! - §2's move catalog (M1-M4) is implemented directly as
//!   [`Move::Flap`], [`Move::Cell1`], [`Move::Notch`], [`Move::ChordEar`]
//!   in `random_growth`.

use crate::configuration::Configuration;
use crate::geometry::{Point, Segment};
use crate::rng::Rng;
use serde::{Deserialize, Serialize};

/// A combinatorial skeleton on `vertex_count` abstract vertices.
///
/// `fences[i] = (u, v)`: fence `i`'s two endpoints are vertices `u` and
/// `v`. A vertex is an "ordinary corner" if it appears as an endpoint of
/// two or more fences (§1.2, dimension-neutral, no extra bookkeeping). A
/// vertex appearing as an endpoint of exactly one fence MUST have a
/// matching entry in `t_junctions` — `(vertex, target_fence)` meaning
/// that vertex's realized position must lie in `target_fence`'s (open)
/// interior — or the skeleton can never realize to a valid configuration
/// (that endpoint would always dangle).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Skeleton {
    pub vertex_count: usize,
    pub fences: Vec<(usize, usize)>,
    pub t_junctions: Vec<(usize, usize)>,
}

impl Skeleton {
    pub fn n(&self) -> usize {
        self.fences.len()
    }

    /// How many fences a vertex is an endpoint of.
    fn endpoint_degree(&self, v: usize) -> usize {
        self.fences
            .iter()
            .filter(|&&(a, b)| a == v || b == v)
            .count()
    }

    /// Structural sanity check (does not touch coordinates): every fence
    /// references valid, distinct vertices, and every vertex that is an
    /// endpoint of exactly one fence has a T-junction entry aiming it at
    /// some *other* fence.
    pub fn validate_shape(&self) -> Result<(), String> {
        for (i, &(u, v)) in self.fences.iter().enumerate() {
            if u >= self.vertex_count || v >= self.vertex_count {
                return Err(format!("fence {i} references out-of-range vertex"));
            }
            if u == v {
                return Err(format!("fence {i} has coincident endpoints"));
            }
        }
        for &(v, f) in &self.t_junctions {
            if v >= self.vertex_count {
                return Err(format!("t_junction references out-of-range vertex {v}"));
            }
            if f >= self.fences.len() {
                return Err(format!("t_junction references out-of-range fence {f}"));
            }
        }
        for v in 0..self.vertex_count {
            let deg = self.endpoint_degree(v);
            if deg == 0 {
                continue; // unused vertex index; harmless but pointless
            }
            if deg == 1 {
                let has_tj = self.t_junctions.iter().any(|&(tv, tf)| {
                    tv == v
                        && !{
                            let (a, b) = self.fences[tf];
                            a == v || b == v
                        }
                });
                if !has_tj {
                    return Err(format!(
                        "vertex {v} is a lone endpoint with no T-junction target"
                    ));
                }
            }
        }
        Ok(())
    }

    /// Realize this skeleton at the given coordinates as a
    /// [`Configuration`], for handing to [`Configuration::validate`].
    pub fn to_configuration(&self, coords: &[Point]) -> Configuration {
        Configuration::new(
            self.fences
                .iter()
                .map(|&(u, v)| Segment::new(coords[u], coords[v]))
                .collect(),
        )
    }
}

/// A skeleton plus the coordinates that realize it — the full
/// machine-readable record of one candidate construction, suitable for
/// serializing and mining for family patterns across many runs.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SkeletonInstance {
    pub skeleton: Skeleton,
    pub coords: Vec<(f64, f64)>,
}

impl SkeletonInstance {
    pub fn configuration(&self) -> Configuration {
        let pts: Vec<Point> = self.coords.iter().map(|&(x, y)| Point::new(x, y)).collect();
        self.skeleton.to_configuration(&pts)
    }
}

// ---------------------------------------------------------------------
// Deterministic builders for named families (§2, §1.3 in the docs).
// ---------------------------------------------------------------------

/// A regular unit-side k-gon: k vertices, k boundary fences, ordinary
/// corners throughout (no T-junctions needed).
pub fn regular_polygon(k: usize) -> (Skeleton, Vec<Point>) {
    assert!(k >= 3);
    let circumradius = 1.0 / (2.0 * (std::f64::consts::PI / k as f64).sin());
    let coords: Vec<Point> = (0..k)
        .map(|i| {
            let theta = 2.0 * std::f64::consts::PI * i as f64 / k as f64;
            Point::new(circumradius * theta.cos(), circumradius * theta.sin())
        })
        .collect();
    let fences: Vec<(usize, usize)> = (0..k).map(|i| (i, (i + 1) % k)).collect();
    (
        Skeleton {
            vertex_count: k,
            fences,
            t_junctions: Vec::new(),
        },
        coords,
    )
}

/// An `a` x `b` grid of unit squares (the minimum-edge polyomino
/// skeleton for a rectangle), as a lattice graph of `(a+1)*(b+1)`
/// vertices.
pub fn grid(a: usize, b: usize) -> (Skeleton, Vec<Point>) {
    assert!(a >= 1 && b >= 1);
    let idx = |x: usize, y: usize| y * (a + 1) + x;
    let mut coords = vec![Point::new(0.0, 0.0); (a + 1) * (b + 1)];
    for y in 0..=b {
        for x in 0..=a {
            coords[idx(x, y)] = Point::new(x as f64, y as f64);
        }
    }
    let mut fences = Vec::new();
    for y in 0..=b {
        for x in 0..a {
            fences.push((idx(x, y), idx(x + 1, y)));
        }
    }
    for x in 0..=a {
        for y in 0..b {
            fences.push((idx(x, y), idx(x, y + 1)));
        }
    }
    (
        Skeleton {
            vertex_count: (a + 1) * (b + 1),
            fences,
            t_junctions: Vec::new(),
        },
        coords,
    )
}

/// A regular unit-side hexagon with unit spokes from the center to the
/// vertices listed in `spoke_vertices` (indices into the hexagon's 6
/// boundary vertices). The m=6 exact point-hub case from §1.3 — the only
/// m for which spokes from a regular m-gon's vertices to one common
/// center are simultaneously unit length.
pub fn hexagon_with_spokes(spoke_vertices: &[usize]) -> (Skeleton, Vec<Point>) {
    let (mut sk, mut coords) = regular_polygon(6);
    let center_idx = coords.len();
    coords.push(Point::new(0.0, 0.0));
    for &v in spoke_vertices {
        assert!(v < 6);
        sk.fences.push((center_idx, v));
    }
    sk.vertex_count += 1;
    (sk, coords)
}

/// A central regular unit-side `inner`-gon surrounded by an outer
/// regular unit-side `outer`-gon, connected by spokes from a subset of
/// outer vertices, each landing by **T-junction** on an inner-polygon
/// edge (not at an inner vertex) — the general hub family that
/// generalizes past the m=6 exact-point-hub case (§1.3) to hubs that
/// back off from a point to a small sub-polygon, which is what the
/// docs' re-read of `18.gif`/`21.gif` describes. `outer_spokes` lists
/// `(outer_vertex_index, inner_fence_index)` pairs: which outer vertex
/// gets a spoke, and which inner-polygon edge it targets.
///
/// This only fixes the *combinatorial* choice; whether a consistent
/// unit-length, non-crossing realization exists for a given choice of
/// `outer`, `inner`, and `outer_spokes` is exactly what the annealer in
/// `anneal.rs` is asked to determine.
pub fn hub_polygon(
    outer: usize,
    inner: usize,
    outer_spokes: &[(usize, usize)],
) -> (Skeleton, Vec<Point>) {
    let (outer_sk, outer_coords) = regular_polygon(outer);
    let (inner_sk, inner_coords) = regular_polygon(inner);
    // Shrink the inner polygon well inside the outer one as a starting
    // guess; the annealer will move it.
    let shrink = 0.3;
    let mut coords = outer_coords;
    let inner_offset = coords.len();
    coords.extend(inner_coords.iter().map(|p| p.scale(shrink)));

    let mut fences = outer_sk.fences;
    let inner_fence_offset = fences.len();
    fences.extend(
        inner_sk
            .fences
            .iter()
            .map(|&(u, v)| (u + inner_offset, v + inner_offset)),
    );

    let mut t_junctions = Vec::new();
    for &(outer_vertex, inner_fence) in outer_spokes {
        assert!(outer_vertex < outer);
        assert!(inner_fence < inner_sk.fences.len());
        // New spoke: one endpoint at the (already-incident) outer
        // vertex, the other a fresh vertex T-junctioned onto the chosen
        // inner-polygon fence (M4, chord-ear, §3).
        let spoke_end = coords.len();
        // Initial guess: partway from the outer vertex toward the inner
        // polygon's centroid.
        let (a, b) = inner_sk.fences[inner_fence];
        let mid = Point::new(
            (coords[a + inner_offset].x + coords[b + inner_offset].x) / 2.0,
            (coords[a + inner_offset].y + coords[b + inner_offset].y) / 2.0,
        );
        coords.push(mid);
        fences.push((outer_vertex, spoke_end));
        t_junctions.push((spoke_end, inner_fence_offset + inner_fence));
    }

    let vertex_count = coords.len();
    (
        Skeleton {
            vertex_count,
            fences,
            t_junctions,
        },
        coords,
    )
}

// ---------------------------------------------------------------------
// Randomized growth from the M1-M4 move catalog (§2, §3).
// ---------------------------------------------------------------------

/// The four local moves from docs §3, applied to the *combinatorial*
/// skeleton only (geometry is left to the annealer). Delta-n per move
/// matches the table there: Flap/Notch add 2 fences, Cell1 adds 3,
/// ChordEar adds 1 (the only move that can hit odd deltas, so any target
/// n is reachable by mixing in ChordEar steps).
#[derive(Debug, Clone, Copy)]
enum Move {
    /// M1: attach a new vertex to both ends of an existing fence,
    /// forming a new triangle-shaped face against that fence.
    Flap,
    /// M2: attach a 2-new-vertex, 3-new-fence quad sharing 1 existing
    /// edge.
    Cell1,
    /// M3: attach a 1-new-vertex, 2-new-fence quad closing a notch at an
    /// existing vertex (the vertex's two incident fences become 2 of the
    /// quad's 4 sides).
    Notch,
    /// M4: one new fence from an existing vertex to a fresh vertex,
    /// which lands by T-junction on some other existing fence.
    ChordEar,
}

/// Grow a random asymmetric skeleton with exactly `n` fences, starting
/// from a unit triangle and applying random M1-M4 moves (docs §3) until
/// the fence count reaches `n` exactly — using `ChordEar` (Δn=1) for the
/// final step(s) whenever a larger move would overshoot. Returns the
/// skeleton and an initial (not yet optimized, and not necessarily even
/// close to unit-length) coordinate guess for the annealer to start
/// from.
///
/// This is the crate's outer-level discrete search primitive: calling it
/// with different `seed`s produces structurally different skeletons,
/// which `search.rs` multistarts the inner annealer over.
pub fn random_growth(n: usize, seed: u64) -> (Skeleton, Vec<Point>) {
    assert!(n >= 3, "no valid skeleton below n=3 (needs a closed face)");
    let mut rng = Rng::new(seed);

    // Seed: a unit triangle, placed arbitrarily (the annealer moves
    // everything anyway; this is just a starting guess with roughly the
    // right scale).
    let mut coords = vec![
        Point::new(0.0, 0.0),
        Point::new(1.0, 0.0),
        Point::new(0.5, 0.87),
    ];
    let mut fences: Vec<(usize, usize)> = vec![(0, 1), (1, 2), (2, 0)];
    let mut t_junctions: Vec<(usize, usize)> = Vec::new();

    while fences.len() < n {
        let remaining = n - fences.len();
        let candidates: &[Move] = if remaining == 1 {
            &[Move::ChordEar]
        } else if remaining == 2 {
            &[Move::Flap, Move::Notch, Move::ChordEar]
        } else {
            &[Move::Flap, Move::Notch, Move::Cell1, Move::ChordEar]
        };
        let mv = candidates[rng.range_usize(candidates.len())];
        match mv {
            Move::Flap => {
                let (u, v) = fences[rng.range_usize(fences.len())];
                let w = coords.len();
                let mid = coords[u].scale(0.5) + coords[v].scale(0.5);
                let perp = Point::new(-(coords[v].y - coords[u].y), coords[v].x - coords[u].x);
                let jitter = rng.range_f64(0.3, 0.7);
                coords.push(mid + perp.scale(jitter));
                fences.push((u, w));
                fences.push((w, v));
            }
            Move::Cell1 => {
                let (u, v) = fences[rng.range_usize(fences.len())];
                let w = coords.len();
                let x = coords.len() + 1;
                let perp = Point::new(-(coords[v].y - coords[u].y), coords[v].x - coords[u].x);
                coords.push(coords[v] + perp.scale(0.5));
                coords.push(coords[u] + perp.scale(0.5));
                fences.push((v, w));
                fences.push((w, x));
                fences.push((x, u));
            }
            Move::Notch => {
                // Pick a vertex with >= 2 incident fences and use two of
                // its incident fences' *other* endpoints as the notch's
                // open ends.
                let candidates_v: Vec<usize> = (0..coords.len())
                    .filter(|&v| fences.iter().filter(|&&(a, b)| a == v || b == v).count() >= 2)
                    .collect();
                if candidates_v.is_empty() {
                    continue;
                }
                let v = candidates_v[rng.range_usize(candidates_v.len())];
                let incident: Vec<usize> = fences
                    .iter()
                    .enumerate()
                    .filter(|(_, &(a, b))| a == v || b == v)
                    .map(|(i, _)| i)
                    .collect();
                if incident.len() < 2 {
                    continue;
                }
                let f0 = incident[rng.range_usize(incident.len())];
                let f1 = incident[rng.range_usize(incident.len())];
                if f0 == f1 {
                    continue;
                }
                let other = |f: usize, v: usize| {
                    let (a, b) = fences[f];
                    if a == v {
                        b
                    } else {
                        a
                    }
                };
                let u = other(f0, v);
                let w = other(f1, v);
                if u == w {
                    continue;
                }
                let x = coords.len();
                let guess = coords[u] + coords[w] - coords[v];
                coords.push(guess);
                fences.push((u, x));
                fences.push((x, w));
            }
            Move::ChordEar => {
                let u = rng.range_usize(coords.len());
                let target_f = rng.range_usize(fences.len());
                let (a, b) = fences[target_f];
                if a == u || b == u {
                    continue;
                }
                let w = coords.len();
                let t = rng.range_f64(0.3, 0.7);
                let landing = coords[a] + (coords[b] - coords[a]).scale(t);
                coords.push(landing);
                let new_f = fences.len();
                fences.push((u, w));
                t_junctions.push((w, target_f));
                let _ = new_f;
            }
        }
    }

    let vertex_count = coords.len();
    (
        Skeleton {
            vertex_count,
            fences,
            t_junctions,
        },
        coords,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn regular_polygon_shape_is_valid() {
        for k in 3..=9 {
            let (sk, _) = regular_polygon(k);
            sk.validate_shape().unwrap();
            assert_eq!(sk.n(), k);
        }
    }

    #[test]
    fn grid_shape_is_valid() {
        let (sk, _) = grid(2, 2);
        sk.validate_shape().unwrap();
        assert_eq!(sk.n(), 12);
    }

    #[test]
    fn hexagon_spokes_shape_is_valid() {
        let (sk, _) = hexagon_with_spokes(&[0, 2, 4]);
        sk.validate_shape().unwrap();
        assert_eq!(sk.n(), 9);
    }

    #[test]
    fn hub_polygon_shape_is_valid() {
        let (sk, _) = hub_polygon(9, 3, &[(0, 0), (1, 0), (3, 1), (4, 1), (6, 2), (7, 2)]);
        sk.validate_shape().unwrap();
        assert_eq!(sk.n(), 18);
    }

    #[test]
    fn random_growth_hits_target_n_and_is_valid() {
        for n in 3..=25 {
            for seed in 0..5 {
                let (sk, coords) = random_growth(n, seed);
                assert_eq!(sk.n(), n, "n mismatch for seed {seed}");
                assert_eq!(coords.len(), sk.vertex_count);
                sk.validate_shape()
                    .unwrap_or_else(|e| panic!("n={n} seed={seed}: {e}"));
            }
        }
    }
}
