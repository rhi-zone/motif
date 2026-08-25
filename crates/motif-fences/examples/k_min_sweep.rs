//! Prints `k_min(n)` (the smallest boundary-fence count that could
//! possibly reach the recorded/target area at `n`, per
//! `boundary_subdivision::k_min`) for every entry in the fences-problem
//! record table, plus the resulting interior-fence budget `n - k_min`.
//!
//! Run with: `cargo run --release --example k_min_sweep`

use motif_fences::boundary_subdivision::k_min;

fn main() {
    // (n, target area) for every record in `/tmp/fence-records.md`.
    let records: &[(u32, f64)] = &[
        (3, 3f64.sqrt() / 4.0),
        (4, 1.0),
        (5, 1.0),
        (6, 1.0 + 3f64.sqrt() / 4.0),
        (7, 2.0),
        (8, 2.0893244080014),
        (9, 3.0 * 3f64.sqrt() / 2.0),
        (10, 3.0),
        (11, 3.5372167764),
        (12, 4.0),
        (13, 4.07361),
        (14, 4.66942),
        (15, 5.0),
        (16, 5.53131),
        (17, 6.0),
        (18, 6.18182),
        (19, 6.76059),
        (20, 7.0),
        (21, 7.69139),
        (22, 8.0),
        (23, 8.52289),
        (24, 9.0),
    ];

    println!(
        "{:>3} {:>12} {:>7} {:>10}",
        "n", "target", "k_min", "interior"
    );
    for &(n, target) in records {
        match k_min(target, 60) {
            Some(k) => println!(
                "{:>3} {:>12.6} {:>7} {:>10}",
                n,
                target,
                k,
                n as i64 - k as i64
            ),
            None => println!("{:>3} {:>12.6} {:>7}", n, target, "NONE"),
        }
    }
}
