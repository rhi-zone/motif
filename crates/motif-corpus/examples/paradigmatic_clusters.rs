//! Probe: paradigmatic clustering over the corpus's usage graph.
//!
//! Saussurean structuralism identifies an element by two axes:
//! - **syntagmatic**: what co-occurs with X in a fixed local combination.
//! - **paradigmatic**: what could *substitute* for X in that slot — found by
//!   distributional similarity ("a term is characterized by the company it
//!   keeps", Harris).
//!
//! Operationalization on this corpus:
//! - "context" for a declaration `d` = its resolved *out-edges*: the set of
//!   other declarations `d` depends on (union of `deps`, `tdeps`, and
//!   `premises[].fullName`, resolved via `Corpus`). This is the syntagmatic
//!   structure — what co-occurs with `d` in its own proof/statement.
//! - "paradigmatic class" = a cluster of declarations whose *out-edge sets*
//!   are highly similar (Jaccard). Two declarations with near-identical
//!   dependency sets are playing a similar structural role — they draw on
//!   the same surrounding machinery — even if their names/content look
//!   unrelated. This is the standard move: instead of comparing d1 and d2
//!   directly, compare their *distributions over context*, i.e. what they
//!   each co-occur with.
//!
//! Clustering: greedy threshold + union-find over all pairs with Jaccard
//! similarity >= THRESHOLD. Simple, no need for anything fancier for a probe.
//!
//! Declarations with a tiny context (< MIN_CONTEXT deps) are excluded before
//! clustering: two declarations that both depend on nothing/almost-nothing
//! are trivially "similar" (Jaccard of near-empty sets is degenerate / not
//! meaningful), which would otherwise dominate the output with a vacuous
//! giant cluster.

use motif_corpus::Corpus;
use std::collections::{HashMap, HashSet};

const MIN_CONTEXT: usize = 3;
const JACCARD_THRESHOLD: f64 = 0.6;

fn jaccard(a: &HashSet<usize>, b: &HashSet<usize>) -> f64 {
    let inter = a.intersection(b).count();
    if inter == 0 {
        return 0.0;
    }
    let union = a.union(b).count();
    inter as f64 / union as f64
}

struct UnionFind {
    parent: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        UnionFind {
            parent: (0..n).collect(),
        }
    }
    fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }
    fn union(&mut self, a: usize, b: usize) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            self.parent[ra] = rb;
        }
    }
}

fn main() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("testdata/group-cross-file-sample.jsonl");
    let corpus = Corpus::load([&path]).expect("corpus should load");
    println!(
        "loaded {} declarations, {} resolved edges\n",
        corpus.records.len(),
        corpus.edge_count()
    );

    // context(d) = out-edge set (what d depends on), restricted to
    // declarations with at least MIN_CONTEXT resolved dependencies.
    let contexts: HashMap<usize, HashSet<usize>> = (0..corpus.records.len())
        .filter_map(|id| {
            let ctx: HashSet<usize> = corpus.dependencies(id).iter().copied().collect();
            if ctx.len() >= MIN_CONTEXT {
                Some((id, ctx))
            } else {
                None
            }
        })
        .collect();
    println!(
        "{} declarations have >= {} resolved dependencies (candidates for clustering)\n",
        contexts.len(),
        MIN_CONTEXT
    );

    let ids: Vec<usize> = contexts.keys().copied().collect();
    let mut uf = UnionFind::new(corpus.records.len());
    let mut pair_count = 0usize;
    for i in 0..ids.len() {
        for j in (i + 1)..ids.len() {
            let (a, b) = (ids[i], ids[j]);
            let sim = jaccard(&contexts[&a], &contexts[&b]);
            if sim >= JACCARD_THRESHOLD {
                uf.union(a, b);
                pair_count += 1;
            }
        }
    }
    println!(
        "{} pairs exceeded Jaccard >= {} among {} candidates\n",
        pair_count,
        JACCARD_THRESHOLD,
        ids.len()
    );

    let mut groups: HashMap<usize, Vec<usize>> = HashMap::new();
    for &id in &ids {
        let root = uf.find(id);
        groups.entry(root).or_default().push(id);
    }

    let mut clusters: Vec<Vec<usize>> = groups.into_values().filter(|g| g.len() > 1).collect();
    clusters.sort_by_key(|g| std::cmp::Reverse(g.len()));

    println!(
        "=== {} paradigmatic clusters (size > 1) ===\n",
        clusters.len()
    );

    for (ci, cluster) in clusters.iter().enumerate() {
        println!("--- cluster {} (size {}) ---", ci, cluster.len());
        for &id in cluster {
            let r = &corpus.records[id];
            println!(
                "  {} [{}]  ({} deps)",
                r.id,
                r.k,
                corpus.dependencies(id).len()
            );
        }
        // Show the shared context (intersection) for the first two members,
        // as a sanity-check sample rather than full n-way intersection.
        if cluster.len() >= 2 {
            let shared: Vec<&str> = contexts[&cluster[0]]
                .intersection(&contexts[&cluster[1]])
                .map(|&id| corpus.records[id].id.as_str())
                .collect();
            println!("  shared context (members 0,1): {:?}", shared);
        }
        println!();
    }
}
