use motif_fences::interior_enumerate::search;

fn main() {
    let stats = search(6, 1, 2.0, 5_000_000, 1000, 12, 20_000, 150_000);
    println!("k={} m={} n={}", stats.k, stats.m, stats.n);
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
    for sk in &stats.survivors {
        println!("survivor: fences={:?} tj={:?}", sk.fences, sk.t_junctions);
    }
}
