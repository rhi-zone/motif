//! Evaluator for Erich Friedman's "fences" packing problem
//! (<https://erich-friedman.github.io/packing/fence/>):
//!
//! > Place `n` straight fences, each of length exactly 1, in the plane.
//! > Every fence endpoint must lie on some other fence (anywhere along
//! > it, not necessarily at an endpoint). The arrangement's bounded faces
//! > are "fields"; every field must have area <= 1. Maximize total
//! > enclosed area.
//!
//! The phrase "not necessarily at an endpoint" might suggest endpoints
//! must land on segment interiors only. However, this reading renders the
//! problem vacuous: any finite set of segments has an extremal point
//! (topmost, ties broken rightmost) that is necessarily an endpoint; if
//! that endpoint must lie on the interior of another segment, that
//! segment extends beyond the extremal point, a contradiction. Thus
//! endpoint-on-endpoint incidence is not merely allowed—it is required by
//! the non-emptiness of the constraint set. This is confirmed by every
//! known record: all valid configurations (n=3 equilateral triangle, n=4
//! unit square, n=9 hexagon-with-spokes) contain adjacent fences meeting
//! endpoint-to-endpoint.
//!
//! # What "total enclosed area" means here
//!
//! This crate implements **total enclosed area = sum of the bounded
//! faces' areas** of the planar arrangement induced by the fences (i.e.
//! the sum of the per-field areas that the problem statement's own area
//! bound (`each field <= 1`) is stated in terms of), not "area of the
//! union of the enclosed region" (i.e. the area you'd get by painting
//! every bounded face and measuring the resulting blob, which
//! double-counts nothing but also *undercounts nothing only when faces
//! don't overlap*).
//!
//! These two readings coincide whenever the arrangement's bounded faces
//! are pairwise interior-disjoint and none contains another — true of
//! every construction this crate encodes (a triangle, squares and grids
//! of squares, a hexagon-with-spokes), and true of any arrangement drawn
//! as a simple planar subdivision, which is the natural reading of
//! Friedman's diagrams. They would differ only for a configuration whose
//! fences cross in a way that makes one bounded face geometrically
//! nested inside another with an unfenced gap between them — a
//! pathological case not exhibited by any known record and not
//! encountered by this crate's tests. We chose the sum-of-faces
//! definition because it's what the "area <= 1 per field" rule directly
//! constrains, and because face-by-face reporting (see
//! [`configuration::Report::field_areas`]) is what a caller needs to
//! check that rule at all; if the two definitions ever needed to be
//! told apart for some future adversarial construction, the union area
//! would need its own polygon-union routine, which this crate does not
//! (yet) provide.
//!
//! # Numerical tolerance
//!
//! Every geometric predicate here is tolerance-based (see
//! [`configuration::Tolerance`]) — segment length, "point lies on
//! segment" incidence, vertex merging, and the area bound all take an
//! explicit epsilon, defaulted for hand-derived unit-scale coordinates.
//! Endpoint incidences (on either segment interiors or endpoints) are
//! common in valid configurations and are handled by explicit
//! endpoint-on-segment checks in [`arrangement::build_arrangement`],
//! not just generic line/line intersection.

pub mod anneal;
pub mod arrangement;
pub mod configuration;
pub mod geometry;
pub mod rng;
pub mod search;
pub mod skeleton;

pub use arrangement::{build_arrangement, Arrangement, Face};
pub use configuration::{Configuration, Endpoint, Report, SegmentCoords, Tolerance, Violation};
pub use geometry::{Point, Segment};
