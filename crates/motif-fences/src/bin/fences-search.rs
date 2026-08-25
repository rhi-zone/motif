//! CLI entry point for the fences optimizer: chase a record at a given
//! `n`, and/or dump the machine-readable skeleton+coordinates JSON for
//! downstream family mining.
//!
//! Usage:
//! ```text
//! fences-search --n 18 --generator hub --attempts 20 --seed 1 --iterations 300000
//! fences-search --n 11 --generator random --attempts 200 --seed 1
//! ```
//!
//! `--generator` selects the skeleton family: `random` (random_growth
//! multistart, the general-purpose outer search), `polygon`, `grid:AxB`,
//! `hexspokes`, or `hub:OUTER:INNER` (regular outer-gon with a regular
//! inner-gon hub, spokes chosen randomly per attempt). Output is one
//! JSON [`motif_fences::search::SearchRecord`] per line on stdout
//! (printed as found, not sorted — pipe through `sort` if you need best-first),
//! so it composes with
//! `jq`/`head` etc.

use motif_fences::anneal::AnnealParams;
use motif_fences::search::{run_one, SearchRecord};
use motif_fences::skeleton::{grid, hexagon_with_spokes, hub_polygon, regular_polygon};

struct Args {
    n: usize,
    generator: String,
    attempts: usize,
    seed: u64,
    iterations: usize,
}

fn parse_args() -> Args {
    let mut n = None;
    let mut generator = "random".to_string();
    let mut attempts = 50usize;
    let mut seed = 1u64;
    let mut iterations = 200_000usize;

    let mut args = std::env::args().skip(1);
    while let Some(flag) = args.next() {
        match flag.as_str() {
            "--n" => n = args.next().and_then(|v| v.parse().ok()),
            "--generator" => generator = args.next().unwrap_or_default(),
            "--attempts" => attempts = args.next().and_then(|v| v.parse().ok()).unwrap_or(attempts),
            "--seed" => seed = args.next().and_then(|v| v.parse().ok()).unwrap_or(seed),
            "--iterations" => {
                iterations = args
                    .next()
                    .and_then(|v| v.parse().ok())
                    .unwrap_or(iterations)
            }
            _ => {}
        }
    }

    Args {
        n: n.expect("--n is required"),
        generator,
        attempts,
        seed,
        iterations,
    }
}

/// Print one record as a JSON line and flush immediately, so a `kill`ed
/// or long-running search still leaves usable partial output on disk
/// (see [`motif_fences::search::search_random_growth_streaming`] docs).
fn emit(record: &SearchRecord) {
    println!("{}", serde_json::to_string(record).unwrap());
    use std::io::Write;
    let _ = std::io::stdout().flush();
    if let Some(report) = &record.valid_report {
        eprintln!(
            "  seed={} area={:.6} fields={} (valid)",
            record.seed,
            report.total_area,
            report.field_areas.len()
        );
    }
}

fn main() {
    let args = parse_args();
    let params = AnnealParams {
        iterations: args.iterations,
        ..AnnealParams::default()
    };

    let records: Vec<SearchRecord> = if args.generator == "random" {
        motif_fences::search::search_random_growth_streaming(
            args.n,
            args.attempts,
            args.seed,
            params,
            emit,
        )
    } else if args.generator == "polygon" {
        let (sk, coords) = regular_polygon(args.n);
        let r = run_one(args.n, "polygon", args.seed, sk, coords, params);
        emit(&r);
        vec![r]
    } else if args.generator == "hexspokes" {
        let (sk, coords) = hexagon_with_spokes(&[0, 2, 4]);
        let r = run_one(args.n, "hexspokes", args.seed, sk, coords, params);
        emit(&r);
        vec![r]
    } else if let Some(rest) = args.generator.strip_prefix("grid:") {
        let (a, b) = rest.split_once('x').expect("grid:AxB");
        let (sk, coords) = grid(a.parse().unwrap(), b.parse().unwrap());
        let r = run_one(args.n, "grid", args.seed, sk, coords, params);
        emit(&r);
        vec![r]
    } else if let Some(rest) = args.generator.strip_prefix("hub:") {
        let mut parts = rest.split(':');
        let outer: usize = parts.next().unwrap().parse().unwrap();
        let inner: usize = parts.next().unwrap().parse().unwrap();
        (0..args.attempts)
            .map(|i| {
                let seed = args.seed + i as u64;
                let mut rng = motif_fences::rng::Rng::new(seed);
                let n_spokes = args.n - outer - inner;
                let mut spokes = Vec::new();
                for _ in 0..n_spokes {
                    let ov = rng.range_usize(outer);
                    let inf = rng.range_usize(inner);
                    spokes.push((ov, inf));
                }
                let (sk, coords) = hub_polygon(outer, inner, &spokes);
                let mut p = params.clone();
                p.seed = seed;
                let r = run_one(args.n, "hub", seed, sk, coords, p);
                emit(&r);
                r
            })
            .collect()
    } else {
        panic!("unknown generator {:?}", args.generator);
    };

    if let Some(best) = records
        .iter()
        .find(|r| r.valid_report.is_some())
        .or_else(|| records.first())
    {
        if let Some(report) = &best.valid_report {
            eprintln!(
                "best valid: n={} area={:.6} fields={}",
                best.n,
                report.total_area,
                report.field_areas.len()
            );
        } else {
            eprintln!("no valid result found among {} attempts", records.len());
        }
    }
}
