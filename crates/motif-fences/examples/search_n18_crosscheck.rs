//! Read-only validation check for n=18: does
//! `interior_enumerate::search` at k=9, m=9 independently generate a
//! topology isomorphic to (or annealing to the same area as) the
//! corrected structure landed by a parallel pixel-retrace effort
//! (`tests/records.rs::regular_9gon_split_diagonal_hub_n18`, commit
//! `1ac892a`)? That structure has 22 vertices for 18 fences (13 beyond
//! the 9-vertex boundary) and 10 T-junctions, including chords with
//! BOTH endpoints fresh (no boundary anchor) and one shared 4-way hub
//! vertex (C) plus a 2-way sub-hub (HENDL/HENDR) — well beyond what
//! this search can exhaustively reach at m=9 (raw branching per level is
//! already in the hundreds; m=9 raw leaves would be astronomically
//! larger than any affordable node cap). This example does NOT edit
//! `tests/records.rs` (owned by the parallel agent) — it only reads the
//! recorded target area for comparison.
//!
//! Run with: `cargo run --release --example search_n18_crosscheck`

use motif_fences::interior_enumerate::search;
use std::f64::consts::PI;

fn main() {
    let target = 9.0 / 4.0 / (PI / 9.0).tan(); // exact n=18 record area
    println!("n=18 target area: {target}");

    // Node cap kept modest given m=9's branching; this is explicitly a
    // best-effort probe, not an exhaustive search, and is reported as
    // such regardless of outcome.
    let stats = search(9, 9, target, 1_000_000, 500, 5, 3_000, 30_000);
    println!(
        "node_visits={} cap_hit={}",
        stats.node_visits, stats.node_cap_hit
    );
    println!("raw_candidates={}", stats.raw_candidates);
    println!("survived_moduli={}", stats.survived_moduli);
    println!(
        "survived_shape_and_euler={}",
        stats.survived_shape_and_euler
    );
    println!("deduped_count={}", stats.deduped_count);
    println!("best_valid_area={:?}", stats.best_valid_area);
    if let Some(area) = stats.best_valid_area {
        println!("matches_n18_record={}", (area - target).abs() < 1e-2);
    }
}
