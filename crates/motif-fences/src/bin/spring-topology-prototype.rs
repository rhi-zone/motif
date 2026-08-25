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

/// Delta-n = +1. The move `reroute_new_vertex` and `rewire_existing` are
/// both missing: neither can ever *create* a T-junction (reroute always
/// lands its new vertex at an ordinary degree-2 corner; rewire only
/// repairs existing plain-fence pairings). But T-junctions are load-
/// bearing in every open-record skeleton this crate has solved so far
/// (n=8's kinked-hexagon chord lands mid-edge, not at a shoulder vertex;
/// n=11's split hub has a T-junction onto a chord's interior) — a move
/// set that can't express "new fence anchored at an existing vertex,
/// landing by T-junction on an existing fence's interior" cannot ever
/// reach those topologies, no matter how the outer search is driven.
/// This is exactly `skeleton.rs`'s private M4/ChordEar move, reimplemented
/// here (that module doesn't expose it) so the outer-SA proposal set can
/// use it directly.
fn chord_ear(sk: &Skeleton, coords: &[Point], rng: &mut Rng) -> Option<(Skeleton, Vec<Point>)> {
    if sk.fences.is_empty() {
        return None;
    }
    for _ in 0..20 {
        let u = rng.range_usize(coords.len());
        let target_f = rng.range_usize(sk.fences.len());
        let (a, b) = sk.fences[target_f];
        if a == u || b == u {
            continue;
        }
        let w = coords.len();
        let t = rng.range_f64(0.2, 0.8);
        let landing = coords[a] + (coords[b] - coords[a]).scale(t);
        let mut new_coords = coords.to_vec();
        new_coords.push(landing);

        let mut fences = sk.fences.clone();
        fences.push((u, w));
        let mut t_junctions = sk.t_junctions.clone();
        t_junctions.push((w, target_f));

        return Some((
            Skeleton {
                vertex_count: new_coords.len(),
                fences,
                t_junctions,
            },
            new_coords,
        ));
    }
    None
}

/// Delta-n = 0. Reassign one existing T-junction's target fence to a
/// different existing plain fence (the geometric "candidate (b)" trigger
/// from `docs/spring-topology-search.md` §1.2: a T-junction foot sliding
/// past its host's endpoint into a neighboring fence's interior is a
/// real, well-defined event, just narrow — it can't create new topology,
/// only relocate an existing incidence). Complements `rewire_existing`
/// (which only ever touches plain fences) with the T-junction-side
/// analogue of the same WWW-style unconditional proposal: no geometric
/// precondition, acceptance is left entirely to re-annealing +
/// Metropolis at the outer level.
fn retarget_t_junction(sk: &Skeleton, rng: &mut Rng) -> Option<Skeleton> {
    if sk.t_junctions.is_empty() {
        return None;
    }
    let idx = rng.range_usize(sk.t_junctions.len());
    let (v, old_f) = sk.t_junctions[idx];
    let candidates: Vec<usize> = (0..sk.fences.len())
        .filter(|&g| {
            g != old_f && {
                let (a, b) = sk.fences[g];
                a != v && b != v
            }
        })
        .collect();
    if candidates.is_empty() {
        return None;
    }
    let g = candidates[rng.range_usize(candidates.len())];
    let mut t_junctions = sk.t_junctions.clone();
    t_junctions[idx] = (v, g);
    Some(Skeleton {
        vertex_count: sk.vertex_count,
        fences: sk.fences.clone(),
        t_junctions,
    })
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
// Experiment 3: multistart over graph-edit chains, with Metropolis
// acceptance at the OUTER level (not the plain random multistart
// `search.rs` currently uses — see that module's own docs, and
// `docs/spring-topology-search.md` §6 for why a single greedy chain
// plateaus). `reroute_new_vertex` and `chord_ear` (delta-n=+1) build an
// initial skeleton of the target size with mixed topology (cycles and
// T-junctions both reachable, unlike pure `grow_with_reroute`); once at
// the target n, `rewire_existing` and `retarget_t_junction` (delta-n=0)
// are proposed by an outer Metropolis loop with its own geometric
// temperature schedule, each proposal scored by re-running the
// unmodified inner annealer from the *current* chain's coordinates. This
// is the WWW precedent (Wooten, Winer & Weaire 1985): unconditional
// graph-edit proposals, Metropolis acceptance, no geometric trigger.
// ---------------------------------------------------------------------

/// Build an initial skeleton of exactly `n` fences by mixing
/// `reroute_new_vertex` and `chord_ear` (both delta-n=+1) from a
/// triangle seed, so different chains start from structurally different
/// topologies (some cycle-only, some with T-junctions).
fn grow_mixed(n: usize, seed: u64) -> (Skeleton, Vec<Point>) {
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
        let use_reroute = rng.bernoulli(0.5);
        let step = if use_reroute {
            reroute_new_vertex(&sk, &coords, &mut rng)
        } else {
            chord_ear(&sk, &coords, &mut rng)
        }
        .or_else(|| reroute_new_vertex(&sk, &coords, &mut rng))
        .or_else(|| chord_ear(&sk, &coords, &mut rng));
        match step {
            Some((new_sk, new_coords)) => {
                sk = new_sk;
                coords = new_coords;
            }
            None => break, // no eligible move; stop short (validate_shape will catch it downstream)
        }
    }
    (sk, coords)
}

/// Anneal `(sk, init_coords)` and return `(anneal result, score, valid)`.
/// `score` is the validated total area when the result passes
/// `Configuration::validate`, otherwise a penalty-based fallback (always
/// strictly less than any valid score, i.e. < 0) so Metropolis
/// acceptance still has a usable gradient toward feasibility even while
/// exploring infeasible skeletons.
fn score_of(
    sk: &Skeleton,
    init_coords: Vec<Point>,
    params: &AnnealParams,
    tol: Tolerance,
) -> (motif_fences::anneal::AnnealResult, f64, bool) {
    let result = anneal(sk, init_coords, params.clone());
    let config = sk.to_configuration(&result.coords);
    match config.validate(tol) {
        Ok(report) => (result, report.total_area, true),
        Err(_) => {
            let penalty_score = -1.0 - result.final_residuals.penalty();
            (result, penalty_score, false)
        }
    }
}

/// One outer-SA chain: grow to `n`, then run `outer_iters` Metropolis
/// proposals of `rewire_existing` / `retarget_t_junction`, each evaluated
/// by a fresh inner-annealer run of `inner_iters` iterations from the
/// chain's current coordinates. Returns the best-scoring (skeleton,
/// coords, score, valid) seen anywhere in the chain, not just the final
/// state (standard SA elitism — the chain's last state need not be its
/// best, especially near the end of the temperature schedule).
fn outer_sa_chain(
    n: usize,
    chain_seed: u64,
    outer_iters: usize,
    inner_iters: usize,
) -> (Skeleton, Vec<Point>, f64, bool) {
    let tol = Tolerance::default();
    let mut rng = Rng::new(chain_seed ^ 0xA5A5_5A5A_1234_5678);

    let (mut sk, init_coords) = grow_mixed(n, chain_seed);
    let inner_params = AnnealParams {
        iterations: inner_iters,
        seed: chain_seed,
        ..AnnealParams::default()
    };
    let (result, mut cur_score, mut cur_valid) = score_of(&sk, init_coords, &inner_params, tol);
    let mut coords = result.coords;

    let mut best_sk = sk.clone();
    let mut best_coords = coords.clone();
    let mut best_score = cur_score;
    let mut best_valid = cur_valid;

    let (t_start, t_end) = (0.3f64, 0.001f64);
    for iter in 0..outer_iters {
        let frac = iter as f64 / outer_iters.max(1) as f64;
        let temp = t_start * (t_end / t_start).powf(frac);

        let proposal = if rng.bernoulli(0.5) {
            rewire_existing(&sk, &mut rng)
        } else {
            retarget_t_junction(&sk, &mut rng)
        };
        let Some(cand_sk) = proposal else { continue };
        if cand_sk.validate_shape().is_err() {
            continue; // defensive: neither move should produce this, but never trust silently
        }

        let mut p = inner_params.clone();
        p.seed = chain_seed.wrapping_add(1_000_000).wrapping_add(iter as u64);
        let (cand_result, cand_score, cand_valid) = score_of(&cand_sk, coords.clone(), &p, tol);

        let accept = cand_score >= cur_score
            || rng.bernoulli(((cand_score - cur_score) / temp.max(1e-9)).exp());
        if accept {
            sk = cand_sk;
            coords = cand_result.coords;
            cur_score = cand_score;
            cur_valid = cand_valid;
            if cur_score > best_score {
                best_score = cur_score;
                best_sk = sk.clone();
                best_coords = coords.clone();
                best_valid = cur_valid;
            }
        }
    }

    (best_sk, best_coords, best_score, best_valid)
}

/// Multistart over `num_chains` independent `outer_sa_chain` runs (each
/// with its own growth seed and Metropolis trajectory), reporting every
/// chain's outcome and the best across all of them. This is the
/// "multistart over graph-edit chains" architecture: the outer level
/// gets its own Metropolis loop instead of `search.rs`'s current plain
/// random multistart (see that module's docs), with `reroute_new_vertex`
/// / `chord_ear` / `rewire_existing` / `retarget_t_junction` as the
/// proposal moves and the unmodified inner annealer as the evaluator.
fn run_outer_sa(
    n: usize,
    num_chains: usize,
    base_seed: u64,
    outer_iters: usize,
    inner_iters: usize,
) {
    let tol = Tolerance::default();
    let mut global_best_score = f64::NEG_INFINITY;
    let mut global_best: Option<(Skeleton, Vec<Point>)> = None;

    for c in 0..num_chains {
        let chain_seed = base_seed.wrapping_add(c as u64 * 7919);
        let (sk, coords, score, valid) = outer_sa_chain(n, chain_seed, outer_iters, inner_iters);
        println!("[outer-sa] n={n} chain={c} seed={chain_seed}: score={score:.6} valid={valid}");
        if score > global_best_score {
            global_best_score = score;
            global_best = Some((sk, coords));
        }
    }

    match global_best {
        Some((sk, coords)) => match sk.to_configuration(&coords).validate(tol) {
            Ok(report) => {
                println!(
                    "[outer-sa] n={n}: BEST valid, total_area={:.10}, fields={}",
                    report.total_area,
                    report.field_areas.len()
                );
                let instance = motif_fences::skeleton::SkeletonInstance {
                    skeleton: sk,
                    coords: coords.iter().map(|p| (p.x, p.y)).collect(),
                };
                println!(
                    "[outer-sa] n={n}: skeleton_json={}",
                    serde_json::to_string(&instance).unwrap()
                );
            }
            Err(violations) => {
                println!(
                    "[outer-sa] n={n}: BEST invalid (score={global_best_score:.6}), violations={violations:?}"
                );
            }
        },
        None => println!("[outer-sa] n={n}: no chains produced a candidate"),
    }
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
    chains: usize,
    outer_iterations: usize,
}

fn parse_args() -> Args {
    let mut mode = "baseline".to_string();
    let mut n = None;
    let mut attempts = 50usize;
    let mut seed = 1u64;
    let mut iterations = 60_000usize;
    let mut rewire_steps = 30usize;
    let mut chains = 8usize;
    let mut outer_iterations = 150usize;

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
            "--chains" => chains = args.next().and_then(|v| v.parse().ok()).unwrap_or(chains),
            "--outer-iterations" => {
                outer_iterations = args
                    .next()
                    .and_then(|v| v.parse().ok())
                    .unwrap_or(outer_iterations)
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
        chains,
        outer_iterations,
    }
}

fn main() {
    let args = parse_args();
    match args.mode.as_str() {
        "reroute-growth" => run_reroute_growth(args.n, args.attempts, args.seed, args.iterations),
        "baseline" => run_baseline(args.n, args.attempts, args.seed, args.iterations),
        "rewire" => run_rewire(args.n, args.seed, args.iterations, args.rewire_steps),
        "outer-sa" => run_outer_sa(
            args.n,
            args.chains,
            args.seed,
            args.outer_iterations,
            args.iterations,
        ),
        other => {
            panic!("unknown --mode {other} (expected reroute-growth, baseline, rewire, outer-sa)")
        }
    }
}
