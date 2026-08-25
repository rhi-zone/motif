//! Prototype for `docs/reframings.md` item 1 (polynomial system / numerical
//! algebraic geometry), scaled down to what this repo's toolchain can
//! actually run: no homotopy-continuation solver (HomotopyContinuation.jl,
//! Bertini, PHCpack) is available in `nix develop` here (checked: no
//! julia, no python3 — only the Rust toolchain + bun), so this does not
//! enumerate all isolated roots of the n=11 split-hub polynomial system.
//! Instead it runs many independent SA solves of the *same fixed skeleton*
//! (`tests/records.rs::split_hub_pinwheel_n11`, duplicated here since that
//! file is off-limits per task instructions) from varied initial guesses,
//! which is the practical multi-start experiment
//! `docs/asymmetric-methods.md` §5 flags as never having been run for
//! open question (A): "whether [the n=11 KKT point] is the global optimum
//! for its own skeleton is UNKNOWN — no multi-start was run."
//!
//! Not a proof either way — SA multistart finding no better point is
//! empirical evidence, not a certificate (that would need the actual
//! homotopy-continuation enumeration, or interval-arithmetic global
//! optimization, neither available here). See `docs/reframings.md` item 1
//! for the full assessment and what real root-counting would need.

use motif_fences::anneal::{anneal, AnnealParams};
use motif_fences::configuration::Tolerance;
use motif_fences::geometry::Point;
use motif_fences::rng::Rng;
use motif_fences::skeleton::Skeleton;

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

const TRACED: [(f64, f64); 13] = [
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

const RECORD_AREA: f64 = 3.5372167764;

fn split_hub_skeleton() -> Skeleton {
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
    let sk = Skeleton {
        vertex_count: 13,
        fences,
        t_junctions,
    };
    sk.validate_shape().unwrap();
    assert_eq!(sk.n(), 11);
    sk
}

fn traced_coords() -> Vec<Point> {
    TRACED.iter().map(|&(x, y)| Point::new(x, y)).collect()
}

/// Perturb the traced guess by Gaussian noise of the given std-dev (a
/// "near" multistart: same basin family, different starting offsets, to
/// check the SA schedule itself isn't what's making every run land on
/// the same point).
fn perturbed(rng: &mut Rng, sigma: f64) -> Vec<Point> {
    traced_coords()
        .into_iter()
        .map(|p| {
            Point::new(
                p.x + rng.range_f64(-sigma, sigma),
                p.y + rng.range_f64(-sigma, sigma),
            )
        })
        .collect()
}

/// A fully independent random guess in a bounding box comparable to the
/// traced construction's extent (a "far" multistart: no information from
/// the traced solution at all, only the skeleton's combinatorics).
fn random_coords(rng: &mut Rng) -> Vec<Point> {
    (0..13)
        .map(|_| Point::new(rng.range_f64(-1.5, 2.5), rng.range_f64(-1.0, 2.5)))
        .collect()
}

fn main() {
    let sk = split_hub_skeleton();
    let mut results: Vec<(String, u64, Option<f64>)> = Vec::new();

    // Near multistarts: increasing perturbation of the known solution.
    for &sigma in &[0.05, 0.15, 0.3, 0.6] {
        for seed in 0..8u64 {
            let mut rng = Rng::new(seed * 1000 + (sigma * 100.0) as u64);
            let init = perturbed(&mut rng, sigma);
            let params = AnnealParams {
                iterations: 300_000,
                seed: seed + 1,
                ..AnnealParams::default()
            };
            let result = anneal(&sk, init, params);
            let config = sk.to_configuration(&result.coords);
            let area = config
                .validate(Tolerance::default())
                .ok()
                .map(|r| r.total_area);
            results.push((format!("near sigma={sigma}"), seed, area));
        }
    }

    // Far multistarts: fully random init, only the skeleton is fixed.
    for seed in 0..20u64 {
        let mut rng = Rng::new(seed + 500);
        let init = random_coords(&mut rng);
        let params = AnnealParams {
            iterations: 300_000,
            seed: seed + 1,
            ..AnnealParams::default()
        };
        let result = anneal(&sk, init, params);
        let config = sk.to_configuration(&result.coords);
        let area = config
            .validate(Tolerance::default())
            .ok()
            .map(|r| r.total_area);
        results.push(("far random".to_string(), seed, area));
    }

    let mut best: Option<f64> = None;
    let mut valid_count = 0;
    let mut beat_record = 0;
    let mut matched_record = 0;
    for (label, seed, area) in &results {
        match area {
            Some(a) => {
                valid_count += 1;
                if *a > best.unwrap_or(f64::NEG_INFINITY) {
                    best = Some(*a);
                }
                if *a > RECORD_AREA + 1e-4 {
                    beat_record += 1;
                }
                if (*a - RECORD_AREA).abs() < 1e-3 {
                    matched_record += 1;
                }
                println!("{label} seed={seed} VALID area={a:.8}");
            }
            None => println!("{label} seed={seed} invalid"),
        }
    }

    println!("---");
    println!("total runs: {}", results.len());
    println!("valid runs: {valid_count}");
    println!("runs matching record (within 1e-3): {matched_record}");
    println!("runs strictly beating record (>1e-4 margin): {beat_record}");
    println!("best area found: {best:?}");
    println!("published record: {RECORD_AREA}");
}
