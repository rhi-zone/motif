//! Prototype + benchmark harness for the spring-relaxation / topology-move
//! question posed to this sidequest: does a foam-style T1 transition have
//! a working analog in a graph of *rigid unit-length* fences, and if a
//! substitute move set exists, does it fix `skeleton::random_growth`'s
//! documented outer-search failure (0/200 at n=4)?
//!
//! Full derivation: `docs/spring-topology-search.md`. Short version: a
//! literal T1 (triggered by an edge shrinking to zero) has no analog
//! here — every fence is pinned at length 1 and never shrinks, so there
//! is no "edge collapses to a point" event to detect. The two moves
//! below are what's left after that trigger is ruled out: unconditional
//! stochastic graph-edit proposals in the style of Wooten-Winer-Weaire
//! bond switching (Wooten, Winer & Weaire, *Phys. Rev. Lett.* 54, 1392
//! (1985)) rather than a geometric zero-crossing trigger. Each proposal
//! is evaluated by handing the *unmodified, already-solid* inner
//! annealer (`anneal::anneal`) the edited skeleton and re-solving from
//! scratch (or from the pre-edit coordinates, for `rewire_existing`).
//!
//! This file is a standalone experiment, not part of the crate's public
//! search API — it duplicates a little bit of plumbing from `search.rs`
//! rather than extending it, so it doesn't compete for edits with other
//! in-flight work on this crate. Run with:
//!
//! ```text
//! cargo run --release --bin spring-topology-prototype -- --mode reroute-growth --n 4 --attempts 200
//! cargo run --release --bin spring-topology-prototype -- --mode baseline       --n 4 --attempts 200
//! cargo run --release --bin spring-topology-prototype -- --mode rewire --n 12 --attempts 20 --rewire-steps 40
//! ```

use motif_fences::anneal::{anneal, AnnealParams};
use motif_fences::configuration::Tolerance;
use motif_fences::geometry::Point;
use motif_fences::rng::Rng;
use motif_fences::search::search_random_growth;
use motif_fences::skeleton::{random_growth, Skeleton};

// ---------------------------------------------------------------------
// The two candidate moves.
// ---------------------------------------------------------------------

fn endpoint_degree(sk: &Skeleton, v: usize) -> usize {
    sk.fences.iter().filter(|&&(a, b)| a == v || b == v).count()
}

/// Delta-n = +1. Delete one "plain" fence (u,v) — not the target of any
/// T-junction, and with both endpoints already at degree >= 2 so removal
/// can't strand them — and replace it with a 2-fence detour through a
/// fresh vertex w: (u,w),(w,v). This is the one move in this file that
/// can turn a smaller cycle into a bigger one (triangle -> quadrilateral)
/// without ever needing an edge to "shrink": nothing shrinks, the whole
/// edit is a single discrete substitution. It is exactly what
/// `skeleton::random_growth`'s M1-M4 catalog lacks (that catalog only
/// ever adds fences, never retires one), which is the mechanism §[crux]
/// of the accompanying doc argues is *why* it can't reach the unit
/// square from a triangle seed.
fn reroute_new_vertex(
    sk: &Skeleton,
    coords: &[Point],
    rng: &mut Rng,
) -> Option<(Skeleton, Vec<Point>)> {
    let candidates: Vec<usize> = (0..sk.fences.len())
        .filter(|&f| {
            let (u, v) = sk.fences[f];
            !sk.t_junctions.iter().any(|&(_, tf)| tf == f)
                && endpoint_degree(sk, u) >= 2
                && endpoint_degree(sk, v) >= 2
        })
        .collect();
    if candidates.is_empty() {
        return None;
    }
    let f = candidates[rng.range_usize(candidates.len())];
    let (u, v) = sk.fences[f];

    let fences: Vec<(usize, usize)> = sk
        .fences
        .iter()
        .enumerate()
        .filter(|&(i, _)| i != f)
        .map(|(_, &e)| e)
        .collect();
    let t_junctions: Vec<(usize, usize)> = sk
        .t_junctions
        .iter()
        .map(|&(tv, tf)| (tv, if tf > f { tf - 1 } else { tf }))
        .collect();

    let w = coords.len();
    let mut new_coords = coords.to_vec();
    let mid = coords[u].scale(0.5) + coords[v].scale(0.5);
    let perp = Point::new(-(coords[v].y - coords[u].y), coords[v].x - coords[u].x);
    let sign = if rng.bernoulli(0.5) { 1.0 } else { -1.0 };
    let jitter = rng.range_f64(0.3, 0.7) * sign;
    new_coords.push(mid + perp.scale(jitter));

    let mut fences = fences;
    fences.push((u, w));
    fences.push((w, v));

    Some((
        Skeleton {
            vertex_count: new_coords.len(),
            fences,
            t_junctions,
        },
        new_coords,
    ))
}

/// Delta-n = 0. Pick two "plain" fences (a,b) and (c,d) with 4 distinct
/// endpoints, and re-pair them: (a,c)+(b,d) or (a,d)+(b,c), chosen at
/// random. This is the literal Wooten-Winer-Weaire bond-switching move
/// applied to the fence graph — no coordinate trigger decides *when* to
/// propose it (there is no analog of "bond length -> 0" for a rigid unit
/// bar); the proposal is unconditional, and Metropolis/greedy acceptance
/// after re-annealing is what filters good swaps from bad ones. Vertex
/// degrees at a,b,c,d are unchanged by construction, and T-junction
/// targets are untouched (candidates exclude any fence that is a
/// T-junction's target, so no target index is invalidated), so this
/// move can never produce a structurally invalid skeleton given a
/// structurally valid input.
fn rewire_existing(sk: &Skeleton, rng: &mut Rng) -> Option<Skeleton> {
    let candidates: Vec<usize> = (0..sk.fences.len())
        .filter(|&f| !sk.t_junctions.iter().any(|&(_, tf)| tf == f))
        .collect();
    if candidates.len() < 2 {
        return None;
    }
    for _ in 0..20 {
        let i = candidates[rng.range_usize(candidates.len())];
        let j = candidates[rng.range_usize(candidates.len())];
        if i == j {
            continue;
        }
        let (a, b) = sk.fences[i];
        let (c, d) = sk.fences[j];
        if a == c || a == d || b == c || b == d {
            continue;
        }
        let mut fences = sk.fences.clone();
        if rng.bernoulli(0.5) {
            fences[i] = (a, c);
            fences[j] = (b, d);
        } else {
            fences[i] = (a, d);
            fences[j] = (b, c);
        }
        return Some(Skeleton {
            vertex_count: sk.vertex_count,
            fences,
            t_junctions: sk.t_junctions.clone(),
        });
    }
    None
}

// ---------------------------------------------------------------------
// Experiment 1: does reroute_new_vertex, applied greedily from a
// triangle seed, reach n exactly and let the annealer find the unit
// square at n=4?
// ---------------------------------------------------------------------

fn grow_with_reroute(n: usize, seed: u64) -> (Skeleton, Vec<Point>) {
    let mut rng = Rng::new(seed);
    let mut coords = vec![
        Point::new(0.0, 0.0),
        Point::new(1.0, 0.0),
        Point::new(0.5, 0.87),
    ];
    let mut sk = Skeleton {
        vertex_count: 3,
        fences: vec![(0, 1), (1, 2), (2, 0)],
        t_junctions: Vec::new(),
    };
    while sk.fences.len() < n {
        match reroute_new_vertex(&sk, &coords, &mut rng) {
            Some((new_sk, new_coords)) => {
                sk = new_sk;
                coords = new_coords;
            }
            None => break, // stuck: no eligible plain fence (shouldn't happen for a simple cycle)
        }
    }
    (sk, coords)
}

fn run_reroute_growth(n: usize, attempts: usize, base_seed: u64, iterations: usize) {
    let tol = Tolerance::default();
    let mut valid = 0usize;
    let mut best_area = 0.0f64;
    let mut areas: Vec<f64> = Vec::new();
    for i in 0..attempts {
        let seed = base_seed + i as u64;
        let (sk, coords) = grow_with_reroute(n, seed);
        let params = AnnealParams {
            iterations,
            seed,
            ..AnnealParams::default()
        };
        let result = anneal(&sk, coords, params);
        let config = sk.to_configuration(&result.coords);
        if let Ok(report) = config.validate(tol) {
            valid += 1;
            areas.push(report.total_area);
            if report.total_area > best_area {
                best_area = report.total_area;
            }
        }
    }
    println!(
        "[reroute-growth] n={n} attempts={attempts}: valid={valid}/{attempts}, best_area={best_area:.6}"
    );
    areas.sort_by(|a, b| b.partial_cmp(a).unwrap());
    println!("  top areas: {:?}", &areas[..areas.len().min(10)]);
}

fn run_baseline(n: usize, attempts: usize, base_seed: u64, iterations: usize) {
    let params = AnnealParams {
        iterations,
        ..AnnealParams::default()
    };
    let records = search_random_growth(n, attempts, base_seed, params);
    let valid = records.iter().filter(|r| r.valid_report.is_some()).count();
    let best_area = records
        .iter()
        .filter_map(|r| r.valid_report.as_ref().map(|v| v.total_area))
        .fold(0.0f64, f64::max);
    println!(
        "[baseline random_growth] n={n} attempts={attempts}: valid={valid}/{attempts}, best_area={best_area:.6}"
    );
}

// ---------------------------------------------------------------------
// Experiment 2: greedy hill-climb with rewire_existing on top of the
// best random_growth seed, for n where the target skeleton needs
// interior chords (n=11, 12, 15) rather than just a bigger boundary
// cycle.
// ---------------------------------------------------------------------

fn run_rewire(n: usize, base_seed: u64, iterations: usize, rewire_steps: usize) {
    let tol = Tolerance::default();
    let params = AnnealParams {
        iterations,
        ..AnnealParams::default()
    };

    // Seed from the best of `attempts` random_growth starts (reusing the
    // existing, solid outer generator as the rewire chain's starting
    // point, per the task: this prototype is about topology *search*,
    // not about re-deriving the inner annealer).
    let mut rng = Rng::new(base_seed);
    let (mut sk, init_coords) = random_growth(n, base_seed);
    let mut result = anneal(&sk, init_coords, params.clone());
    let mut best_area = sk
        .to_configuration(&result.coords)
        .validate(tol)
        .map(|r| r.total_area)
        .unwrap_or(0.0);
    println!("[rewire] n={n} start (random_growth seed {base_seed}): area={best_area:.6}");

    let mut accepted = 0usize;
    for step in 0..rewire_steps {
        let Some(candidate_sk) = rewire_existing(&sk, &mut rng) else {
            continue;
        };
        let mut p = params.clone();
        p.seed = base_seed.wrapping_add(1000 + step as u64);
        let candidate_result = anneal(&candidate_sk, result.coords.clone(), p);
        let candidate_area = candidate_sk
            .to_configuration(&candidate_result.coords)
            .validate(tol)
            .map(|r| r.total_area)
            .unwrap_or(0.0);
        if candidate_area > best_area {
            best_area = candidate_area;
            sk = candidate_sk;
            result = candidate_result;
            accepted += 1;
            println!("  step {step}: accepted, area={best_area:.6}");
        }
    }
    println!(
        "[rewire] n={n}: final best_area={best_area:.6} ({accepted}/{rewire_steps} rewires accepted)"
    );
}

// ---------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------

struct Args {
    mode: String,
    n: usize,
    attempts: usize,
    seed: u64,
    iterations: usize,
    rewire_steps: usize,
}

fn parse_args() -> Args {
    let mut mode = "baseline".to_string();
    let mut n = None;
    let mut attempts = 50usize;
    let mut seed = 1u64;
    let mut iterations = 60_000usize;
    let mut rewire_steps = 30usize;

    let mut args = std::env::args().skip(1);
    while let Some(flag) = args.next() {
        match flag.as_str() {
            "--mode" => mode = args.next().unwrap_or(mode),
            "--n" => n = args.next().and_then(|v| v.parse().ok()),
            "--attempts" => attempts = args.next().and_then(|v| v.parse().ok()).unwrap_or(attempts),
            "--seed" => seed = args.next().and_then(|v| v.parse().ok()).unwrap_or(seed),
            "--iterations" => {
                iterations = args
                    .next()
                    .and_then(|v| v.parse().ok())
                    .unwrap_or(iterations)
            }
            "--rewire-steps" => {
                rewire_steps = args
                    .next()
                    .and_then(|v| v.parse().ok())
                    .unwrap_or(rewire_steps)
            }
            _ => {}
        }
    }

    Args {
        mode,
        n: n.expect("--n is required"),
        attempts,
        seed,
        iterations,
        rewire_steps,
    }
}

fn main() {
    let args = parse_args();
    match args.mode.as_str() {
        "reroute-growth" => run_reroute_growth(args.n, args.attempts, args.seed, args.iterations),
        "baseline" => run_baseline(args.n, args.attempts, args.seed, args.iterations),
        "rewire" => run_rewire(args.n, args.seed, args.iterations, args.rewire_steps),
        other => panic!("unknown --mode {other} (expected reroute-growth, baseline, rewire)"),
    }
}
