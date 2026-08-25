//! Runs `interior_enumerate::search` at the two "discriminating test"
//! open n's a peer session flagged: n=13 (k_min=8, m=5) and n=21
//! (k_min=10, m=11), both of which have careful traced constructions
//! stuck ~0.009 below the published record despite re-tracing
//! (n=13: 4.0645952819 vs 4.07361; n=21: 7.682823 vs 7.69139).
//!
//! Run with: `cargo run --release --example search_open_n -- 13`
//! or `... -- 21`. Prints the full filter-by-filter breakdown and the
//! best valid area found, so the caller can judge exhaustive-vs-
//! best-effort from `node_cap_hit` and the raw counts directly.

use motif_fences::interior_enumerate::search;

fn main() {
    let which: u32 = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(13);

    // Budgets kept modest — n=8's m=2 alone already produced 8469
    // distinct combinatorial survivors, so m=5 (n=13) and m=11 (n=21)
    // are certain to be astronomically larger than any affordable
    // exhaustive search; this is explicitly a truncated, best-effort
    // probe, reported as such via `node_cap_hit`/`max_leaves_hit`.
    let (k, m, target, node_cap, max_leaves, refine_top, screen_iters, refine_iters) = match which {
        13 => (
            8usize,
            5usize,
            4.07361f64,
            500_000u64,
            500usize,
            8usize,
            5_000usize,
            40_000usize,
        ),
        21 => (
            10usize,
            11usize,
            7.69139f64,
            500_000u64,
            500usize,
            8usize,
            5_000usize,
            40_000usize,
        ),
        n => panic!("no configuration for n={n}"),
    };

    let stats = search(
        k,
        m,
        target,
        node_cap,
        max_leaves,
        refine_top,
        screen_iters,
        refine_iters,
    );
    println!("n={which} k={k} m={m} target={target}");
    println!(
        "node_visits={} cap_hit={} max_leaves_hit={}",
        stats.node_visits, stats.node_cap_hit, stats.max_leaves_hit
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
        println!("beats_record={}", area > target);
    }
}
