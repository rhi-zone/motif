//! Prototype probe: stage 1+2 of the MMT-style theory-morphism pipeline
//! (Kohlhase/Rabe/Kaliszyk/Gauthier, CICM 2018) — generate cheap alignment
//! signals between declaration pairs, then rank candidates for a human (or
//! later, Lean-side proof search) to verify. No verification happens here.
//!
//! Signals used (all cheap: no Lean re-elaboration, just corpus data):
//!
//! - **Dependency Jaccard**: Jaccard similarity of each declaration's
//!   resolved in-corpus dependency set (`Corpus::dependencies`). Two
//!   declarations that lean on the same supporting lemmas/instances are
//!   candidates for playing structurally analogous roles.
//! - **Premise-vocabulary Jaccard**: Jaccard similarity of raw
//!   `premises[].fullName` sets (includes premises outside the corpus, e.g.
//!   core typeclass ops like `Mul.mul`/`Inv.inv`) — a proxy for shared
//!   typeclass/operation context, finer-grained than resolved deps alone.
//! - **Proof-shape similarity**: for the minority of declarations with a
//!   non-empty tactic trace, similarity of tactic-step count (a very coarse
//!   proxy for proof shape — the corpus only gives goal-state text, not
//!   tactic names, so this is intentionally weak and down-weighted).
//!
//! Trivial-pair exclusion: Mathlib's `@[to_additive]` generates a
//! syntactically mirrored additive declaration for nearly every
//! multiplicative one in `Group/Defs.lean` and `Commutator.lean`. Those
//! pairs score at or near the maximum on every signal here *by
//! construction* (identical proof shape, near-identical dependency/premise
//! sets modulo add/mul renaming) and would otherwise dominate the top-N,
//! telling us nothing we don't already know from the `to_additive`
//! attribute itself. We detect and exclude them by name-normalization
//! (stripping a leading "add" and lowercasing the next char) plus a same/
//! adjacent-declaration heuristic, and report how many were excluded.

use motif_corpus::Corpus;
use std::collections::HashSet;
use std::path::Path;

/// Strip a Mathlib `to_additive`-style "add" prefix, if present, and
/// lowercase the following character, for name-normalization purposes.
/// E.g. `addCommutatorElement_def` -> `commutatorElement_def`,
/// `AddSemigroup` -> `Semigroup`. Not a general-purpose normalizer — just
/// good enough to catch the additive/multiplicative twins in this corpus.
fn strip_add_prefix(name: &str) -> String {
    let base = name.rsplit('.').next().unwrap_or(name);
    if let Some(rest) = base.strip_prefix("add") {
        if let Some(c) = rest.chars().next() {
            if c.is_uppercase() {
                return format!("{}{}", c.to_lowercase(), &rest[c.len_utf8()..]);
            }
        }
    } else if let Some(rest) = base.strip_prefix("Add") {
        if let Some(c) = rest.chars().next() {
            if c.is_uppercase() {
                return rest.to_string();
            }
        }
    }
    base.to_string()
}

fn is_additive_twin(a: &str, b: &str) -> bool {
    strip_add_prefix(a) == strip_add_prefix(b)
}

fn jaccard<T: Eq + std::hash::Hash>(a: &HashSet<T>, b: &HashSet<T>) -> f64 {
    if a.is_empty() && b.is_empty() {
        return 0.0;
    }
    let inter = a.intersection(b).count() as f64;
    let union = a.union(b).count() as f64;
    if union == 0.0 {
        0.0
    } else {
        inter / union
    }
}

fn main() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("testdata/group-cross-file-sample.jsonl");
    let corpus = Corpus::load([&path]).expect("corpus should load");
    let n = corpus.records.len();
    println!("Loaded {n} declarations from {}\n", path.display());

    // Precompute per-declaration signal sets.
    let dep_sets: Vec<HashSet<usize>> = (0..n)
        .map(|i| corpus.dependencies(i).iter().copied().collect())
        .collect();
    let premise_sets: Vec<HashSet<&str>> = corpus
        .records
        .iter()
        .map(|r| r.premises.iter().map(|p| p.full_name.as_str()).collect())
        .collect();
    let tactic_counts: Vec<usize> = corpus.records.iter().map(|r| r.tactics.len()).collect();

    struct Candidate {
        i: usize,
        j: usize,
        score: f64,
        dep_jac: f64,
        prem_jac: f64,
        tactic_sim: Option<f64>,
    }

    let mut candidates = Vec::new();
    let mut excluded_additive_twins = 0usize;
    let mut excluded_empty = 0usize;

    for i in 0..n {
        for j in (i + 1)..n {
            let ri = &corpus.records[i];
            let rj = &corpus.records[j];

            if is_additive_twin(&ri.n, &rj.n) {
                excluded_additive_twins += 1;
                continue;
            }

            let dep_jac = jaccard(&dep_sets[i], &dep_sets[j]);
            let prem_jac = jaccard(&premise_sets[i], &premise_sets[j]);

            // Require at least one non-trivial signal (both empty deps and
            // both empty premises means "no evidence", not "identical").
            if dep_sets[i].is_empty()
                && dep_sets[j].is_empty()
                && premise_sets[i].is_empty()
                && premise_sets[j].is_empty()
            {
                excluded_empty += 1;
                continue;
            }

            let tactic_sim = if tactic_counts[i] > 0 && tactic_counts[j] > 0 {
                let a = tactic_counts[i] as f64;
                let b = tactic_counts[j] as f64;
                Some(1.0 - (a - b).abs() / a.max(b))
            } else {
                None
            };

            let score = match tactic_sim {
                Some(t) => 0.5 * dep_jac + 0.3 * prem_jac + 0.2 * t,
                None => 0.6 * dep_jac + 0.4 * prem_jac,
            };

            if score <= 0.0 {
                continue;
            }

            candidates.push(Candidate {
                i,
                j,
                score,
                dep_jac,
                prem_jac,
                tactic_sim,
            });
        }
    }

    candidates.sort_by(|a, b| b.score.partial_cmp(&a.score).unwrap());

    println!(
        "Excluded {excluded_additive_twins} to_additive twin pairs (trivial: mirrored by \
         construction), {excluded_empty} pairs with no signal at all (both sides have empty \
         deps and premises)."
    );
    println!(
        "{} candidate pairs scored, showing top 20:\n",
        candidates.len()
    );

    if let Some((rank, c)) = candidates
        .iter()
        .enumerate()
        .find(|(_, c)| corpus.records[c.i].m != corpus.records[c.j].m)
    {
        println!(
            "(best cross-file candidate is #{} at score {:.3}: {} <-> {})\n",
            rank + 1,
            c.score,
            corpus.records[c.i].n,
            corpus.records[c.j].n
        );
    }

    for (rank, c) in candidates.iter().take(20).enumerate() {
        let ri = &corpus.records[c.i];
        let rj = &corpus.records[c.j];
        println!(
            "#{:<2} score={:.3}  dep_jac={:.2} prem_jac={:.2} tactic_sim={}",
            rank + 1,
            c.score,
            c.dep_jac,
            c.prem_jac,
            c.tactic_sim
                .map(|t| format!("{t:.2}"))
                .unwrap_or_else(|| "n/a".to_string()),
        );
        println!("    {} [{}, {}]", ri.n, ri.k, ri.m);
        println!("    {} [{}, {}]", rj.n, rj.k, rj.m);

        let shared_deps: Vec<&str> = dep_sets[c.i]
            .intersection(&dep_sets[c.j])
            .map(|&id| corpus.records[id].n.as_str())
            .collect();
        if !shared_deps.is_empty() {
            println!("    shared deps: {}", shared_deps.join(", "));
        }
        let shared_premises: Vec<&str> = premise_sets[c.i]
            .intersection(&premise_sets[c.j])
            .copied()
            .collect();
        if !shared_premises.is_empty() {
            println!("    shared premises: {}", shared_premises.join(", "));
        }
        println!();
    }
}
