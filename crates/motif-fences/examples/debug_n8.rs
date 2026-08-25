use motif_fences::interior_enumerate::search;

fn main() {
    // Combinatorics-only pass (refine_top=0): no annealing, just the
    // true raw/survived/deduped counts, uncapped.
    let stats = search(6, 2, 2.0893244080014, 50_000_000, 10_000_000, 0, 1, 1);
    println!("k={} m={} n={}", stats.k, stats.m, stats.n);
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

    // Coverage check: is the kinked-hexagon pattern (2 interior fences,
    // the first with BOTH endpoints pure T-junction pendants) present
    // among the full, exhaustive survivor set?
    let boundary_fence_count = 6;
    let mut found = 0;
    for sk in &stats.survivors {
        let tj_targets: Vec<usize> = sk.t_junctions.iter().map(|&(v, _)| v).collect();
        let interior_fences: Vec<(usize, usize)> = sk.fences[boundary_fence_count..].to_vec();
        if interior_fences.len() == 2 {
            let (a, b) = interior_fences[0];
            let deg = |v: usize| sk.fences.iter().filter(|&&(x, y)| x == v || y == v).count();
            if deg(a) == 1 && deg(b) == 1 && tj_targets.contains(&a) && tj_targets.contains(&b) {
                found += 1;
            }
        }
    }
    println!(
        "kinked-hexagon-pattern matches among ALL {} survivors: {found}",
        stats.survivors.len()
    );
}
