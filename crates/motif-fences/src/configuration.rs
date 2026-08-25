//! The public evaluator API: a [`Configuration`] of unit fences, validated
//! against the problem's rules and scored by enclosed area.

use crate::arrangement::build_arrangement;
use crate::geometry::{Point, Segment};

/// A segment expressed as a pair of raw `(x, y)` coordinate tuples, for
/// [`Configuration::from_coords`].
pub type SegmentCoords = ((f64, f64), (f64, f64));

/// Tolerances used throughout validation and arrangement construction.
///
/// A single shared tolerance would conflate unrelated sources of error
/// (floating-point roundoff in a hand-computed `cos`/`sin` coordinate vs.
/// how far apart two points may be before they're "the same point"), so
/// each use is named separately. All default to `1e-6`, appropriate for
/// hand-derived closed-form coordinates around unit scale; tighten or
/// loosen per configuration if needed.
#[derive(Debug, Clone, Copy)]
pub struct Tolerance {
    /// Allowed deviation of a fence's length from exactly 1.
    pub length: f64,
    /// Allowed perpendicular distance for "this point lies on this
    /// fence" (endpoint-incidence checks, and the parameter-space slack
    /// derived from it for intersection detection).
    pub incidence: f64,
    /// Distance below which two raw points (endpoints, intersections)
    /// are merged into a single arrangement vertex.
    pub vertex_merge: f64,
    /// Slack added to the area <= 1 per-field bound, i.e. a field is
    /// flagged only if its area exceeds `1 + area_slack`.
    pub area_slack: f64,
}

impl Default for Tolerance {
    fn default() -> Self {
        Tolerance {
            length: 1e-6,
            incidence: 1e-6,
            vertex_merge: 1e-7,
            area_slack: 1e-9,
        }
    }
}

/// Which endpoint of a fence a violation refers to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Endpoint {
    A,
    B,
}

/// A single way a [`Configuration`] can fail to be a valid fence
/// arrangement.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Violation {
    /// A fence's length differs from 1 by more than `Tolerance::length`.
    WrongLength { segment: usize, length: f64 },
    /// A fence endpoint does not lie on any other fence.
    DanglingEndpoint { segment: usize, endpoint: Endpoint },
    /// A bounded field's area exceeds `1 + Tolerance::area_slack`.
    FieldTooLarge { field: usize, area: f64 },
}

/// A successful validation report: the enclosed area breakdown of a
/// configuration that satisfies every rule.
#[derive(Debug, Clone)]
pub struct Report {
    pub fence_count: usize,
    /// Area of each bounded face ("field") of the arrangement, in the
    /// order the arrangement builder discovered them (no meaningful
    /// ordering beyond that — don't rely on it to identify a particular
    /// geometric field).
    pub field_areas: Vec<f64>,
    /// Total enclosed area. This implements "sum of the bounded faces'
    /// areas", not "area of the union of the enclosed region" — see
    /// module-level discussion in `lib.rs` for why, and when the two
    /// definitions coincide (they do for every construction in this
    /// crate's test suite: the fields never overlap and every bounded
    /// face is simply connected).
    pub total_area: f64,
}

/// A candidate arrangement of `n` unit fences.
#[derive(Debug, Clone)]
pub struct Configuration {
    pub segments: Vec<Segment>,
}

impl Configuration {
    pub fn new(segments: Vec<Segment>) -> Self {
        Configuration { segments }
    }

    /// Convenience constructor from raw coordinate pairs.
    pub fn from_coords(segments: &[SegmentCoords]) -> Self {
        Configuration {
            segments: segments
                .iter()
                .map(|&((ax, ay), (bx, by))| Segment::new(Point::new(ax, ay), Point::new(bx, by)))
                .collect(),
        }
    }

    pub fn fence_count(&self) -> usize {
        self.segments.len()
    }

    /// Validate this configuration against every rule of the problem and,
    /// if it passes, report its enclosed area.
    ///
    /// All violations are collected (not just the first) so a caller
    /// debugging a hand-built configuration sees everything wrong with it
    /// in one pass.
    pub fn validate(&self, tol: Tolerance) -> Result<Report, Vec<Violation>> {
        let mut violations = Vec::new();

        for (i, seg) in self.segments.iter().enumerate() {
            let len = seg.length();
            if (len - 1.0).abs() > tol.length {
                violations.push(Violation::WrongLength {
                    segment: i,
                    length: len,
                });
            }
        }

        for (i, seg) in self.segments.iter().enumerate() {
            for (endpoint, p) in [(Endpoint::A, seg.a), (Endpoint::B, seg.b)] {
                let lies_on_another = self
                    .segments
                    .iter()
                    .enumerate()
                    .any(|(j, other)| j != i && other.contains_point(p, tol.incidence));
                if !lies_on_another {
                    violations.push(Violation::DanglingEndpoint {
                        segment: i,
                        endpoint,
                    });
                }
            }
        }

        // Field-area checks need the arrangement even if endpoint/length
        // checks already failed, so a caller sees the full picture; but
        // an arrangement built from garbage input (e.g. wildly
        // mis-lengthed segments) is not meaningful, so only attempt it
        // when there are no length violations.
        let has_length_violation = violations
            .iter()
            .any(|v| matches!(v, Violation::WrongLength { .. }));
        let mut field_areas = Vec::new();
        if !has_length_violation {
            let arrangement = build_arrangement(&self.segments, tol.incidence, tol.vertex_merge);
            for (i, face) in arrangement.bounded_faces.iter().enumerate() {
                field_areas.push(face.area);
                if face.area > 1.0 + tol.area_slack {
                    violations.push(Violation::FieldTooLarge {
                        field: i,
                        area: face.area,
                    });
                }
            }
        }

        if !violations.is_empty() {
            return Err(violations);
        }

        let total_area: f64 = field_areas.iter().sum();
        Ok(Report {
            fence_count: self.segments.len(),
            field_areas,
            total_area,
        })
    }
}
