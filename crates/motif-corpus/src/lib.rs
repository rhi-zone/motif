//! Loader for the JSONL corpus produced by
//! `langlands/scripts/lean-extraction/ExtractBatch.lean`.
//!
//! This crate is intentionally minimal: struct definitions matching the
//! corpus schema plus a `load` function that reads a JSONL file into
//! `Vec<DeclRecord>`. No indexing, no query engine — that's for whichever
//! experiment builds on top of this to add, once it knows what it needs.
//!
//! See `langlands/scripts/lean-extraction/README.md` for the schema
//! documentation and how to (re)generate a corpus file.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::Path;

/// A source position (1-based line, 0-based column), as reported by Lean's
/// `Position` type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Position {
    pub line: u32,
    pub column: u32,
}

/// One tactic step's before/after goal state, with a byte-offset span into
/// the source file.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TacticTrace {
    #[serde(rename = "stateBefore")]
    pub state_before: String,
    #[serde(rename = "stateAfter")]
    pub state_after: String,
    /// Byte offset of the tactic's start.
    pub pos: u32,
    /// Byte offset of the tactic's end.
    #[serde(rename = "endPos")]
    pub end_pos: u32,
}

/// One constant (premise) reference inside a declaration's proof term.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PremiseTrace {
    #[serde(rename = "fullName")]
    pub full_name: String,
    #[serde(rename = "modName")]
    pub mod_name: String,
    pub pos: Option<Position>,
    #[serde(rename = "endPos")]
    pub end_pos: Option<Position>,
}

/// One declaration's joined corpus record: statement-level metadata
/// (name/kind/module/byte-range/typeclass deps, mirroring lean-pool's
/// `Extract.lean`) plus the tactic/premise trace entries assigned to it
/// during the InfoTree walk (mirroring the ported LeanDojo-style
/// extractor). See the module docs and the extraction script's README for
/// how these are joined and their known limitations (single-file scope,
/// first-match declaration assignment for overlapping ranges).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclRecord {
    /// Fully qualified declaration name.
    pub id: String,
    /// Display name (may differ from `id` for private declarations).
    pub n: String,
    /// Module the declaration was defined in.
    pub m: String,
    /// Declaration kind: theorem/def/opaque/axiom/structure/inductive.
    pub k: String,
    /// Full declaration byte range: `[startLine, startCol, endLine, endCol]`.
    pub r: [u32; 4],
    /// Name-selection range: `[nameLine, nameCol]`.
    pub s: [u32; 2],
    pub doc: Option<String>,
    /// Intra-file dependency edges (see crate docs: no cross-file join).
    pub deps: Vec<String>,
    /// Statement-only (type) dependency edges; present only for theorems.
    pub tdeps: Option<Vec<String>>,
    /// Count of distinct out-of-file (or otherwise unresolved) dependencies.
    pub ext: u32,
    /// Tactic-tree entries whose byte range falls inside this declaration.
    pub tactics: Vec<TacticTrace>,
    /// Premise (constant-use) entries whose byte range falls inside this
    /// declaration.
    pub premises: Vec<PremiseTrace>,
}

/// Load a JSONL corpus file (one `DeclRecord` per line) into memory.
///
/// Returns an error on I/O failure or if any line fails to parse as a
/// `DeclRecord`; the error identifies the offending line number.
pub fn load(path: impl AsRef<Path>) -> io::Result<Vec<DeclRecord>> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    let mut records = Vec::new();
    for (i, line) in reader.lines().enumerate() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        let record: DeclRecord = serde_json::from_str(&line).map_err(|e| {
            io::Error::new(io::ErrorKind::InvalidData, format!("line {}: {e}", i + 1))
        })?;
        records.push(record);
    }
    Ok(records)
}

/// Index of a [`DeclRecord`] within a [`Corpus`]'s `records` vector.
pub type DeclId = usize;

/// A loaded corpus plus a resolved cross-declaration dependency graph.
///
/// `ExtractBatch.lean` elaborates each input file independently, so a
/// declaration's `deps`/`tdeps`/`premises` fields only ever carry *names* —
/// fully qualified Lean identifiers — not resolved references to other
/// records, even when the referenced declaration is sitting in the same
/// loaded corpus (just from a different file). `Corpus` closes that gap
/// entirely on the Rust side: it builds a `name -> DeclId` index over every
/// loaded record's `id` field (fully qualified names are unique across all
/// of Mathlib, so this index is safe to build across an arbitrary set of
/// files, not just one), then resolves each record's `deps`, `tdeps`, and
/// `premises[].fullName` entries against it. A name that resolves becomes a
/// real edge; a name that doesn't (because the declaration it names wasn't
/// part of this corpus) is simply left unresolved — same meaning as the
/// existing `ext` counter, just now at corpus scope instead of file scope.
///
/// This does not replace `ext`: `ext` (as emitted by `ExtractBatch.lean`)
/// counts dependencies unresolved *within a single file*, so it stays an
/// upper bound / sanity check on how much a given corpus slice can ever
/// resolve, no matter how many files get loaded into it.
pub struct Corpus {
    pub records: Vec<DeclRecord>,
    /// `edges[i]` is the set of `DeclId`s that `records[i]` depends on
    /// (union of `deps`, `tdeps`, and `premises[].fullName`, resolved
    /// against this corpus's name index, self-references dropped,
    /// deduplicated and sorted).
    edges: Vec<Vec<DeclId>>,
}

impl Corpus {
    /// Build a `Corpus` from already-loaded records, resolving cross-record
    /// dependency edges by fully qualified name.
    pub fn from_records(records: Vec<DeclRecord>) -> Self {
        let index: HashMap<&str, DeclId> = records
            .iter()
            .enumerate()
            .map(|(i, r)| (r.id.as_str(), i))
            .collect();

        let edges = records
            .iter()
            .enumerate()
            .map(|(i, r)| {
                let mut resolved: Vec<DeclId> = r
                    .deps
                    .iter()
                    .map(String::as_str)
                    .chain(r.tdeps.iter().flatten().map(String::as_str))
                    .chain(r.premises.iter().map(|p| p.full_name.as_str()))
                    .filter_map(|name| index.get(name).copied())
                    .filter(|&id| id != i)
                    .collect();
                resolved.sort_unstable();
                resolved.dedup();
                resolved
            })
            .collect();

        Corpus { records, edges }
    }

    /// Load one or more JSONL corpus files and join them into a single
    /// `Corpus` with cross-file dependency edges resolved.
    ///
    /// This is the entry point for the actual point of this crate: loading
    /// several `ExtractBatch.lean` outputs (or one output covering many
    /// files) and getting back real dependency edges between declarations
    /// that were extracted from different files, not just the per-file
    /// `ext` count `ExtractBatch.lean` emits on its own.
    pub fn load(paths: impl IntoIterator<Item = impl AsRef<Path>>) -> io::Result<Self> {
        let mut records = Vec::new();
        for path in paths {
            records.extend(load(path)?);
        }
        Ok(Self::from_records(records))
    }

    /// Resolved outgoing dependency edges for `id`: other declarations in
    /// this corpus that `records[id]` depends on.
    pub fn dependencies(&self, id: DeclId) -> &[DeclId] {
        &self.edges[id]
    }

    /// In-degree of every declaration: how many other declarations in this
    /// corpus depend on it. Index-aligned with `records`.
    pub fn in_degrees(&self) -> Vec<u32> {
        let mut counts = vec![0u32; self.records.len()];
        for targets in &self.edges {
            for &t in targets {
                counts[t] += 1;
            }
        }
        counts
    }

    /// Total number of resolved cross-declaration edges in the graph.
    pub fn edge_count(&self) -> usize {
        self.edges.iter().map(Vec::len).sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn loads_sample_corpus() {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("testdata/group-defs-sample.jsonl");
        let records = load(&path).expect("corpus should load");
        assert!(
            records.len() > 300,
            "expected a few hundred declarations from the Group/Defs.lean batch, got {}",
            records.len()
        );

        // At least one theorem should carry a non-empty tactic trace,
        // proving the statement/proof-structure join actually happened.
        assert!(
            records
                .iter()
                .any(|r| r.k == "theorem" && !r.tactics.is_empty()),
            "expected at least one theorem with a populated tactic trace"
        );

        // Every record should have a non-empty id and module.
        for r in &records {
            assert!(!r.id.is_empty());
            assert!(!r.m.is_empty());
        }
    }

    #[test]
    fn resolves_cross_file_dependency_edges() {
        // `Mathlib/Algebra/Group/{Defs,Commutator}.lean`: `Commutator.lean`'s
        // declarations reference `Group` etc. from `Defs.lean`. Both files
        // were extracted in the same batch but elaborated independently by
        // `ExtractBatch.lean`, so those references only show up as names
        // (`deps`/`premises[].fullName`) in the raw JSONL, never as edges —
        // proving the join actually crosses file boundaries (not just
        // resolving each file's declarations against itself) is the point
        // of this test.
        let path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("testdata/group-cross-file-sample.jsonl");
        let corpus = Corpus::load([&path]).expect("corpus should load");
        assert!(corpus.records.len() > 300);

        let modules: std::collections::HashSet<&str> =
            corpus.records.iter().map(|r| r.m.as_str()).collect();
        assert!(modules.contains("Mathlib.Algebra.Group.Defs"));
        assert!(modules.contains("Mathlib.Algebra.Group.Commutator"));

        // At least one Commutator.lean declaration must resolve a
        // dependency edge into a Defs.lean declaration.
        let commutator_ids: Vec<DeclId> = corpus
            .records
            .iter()
            .enumerate()
            .filter(|(_, r)| r.m == "Mathlib.Algebra.Group.Commutator")
            .map(|(i, _)| i)
            .collect();
        assert!(!commutator_ids.is_empty());

        let found_cross_file_edge = commutator_ids.iter().any(|&id| {
            corpus
                .dependencies(id)
                .iter()
                .any(|&dep| corpus.records[dep].m == "Mathlib.Algebra.Group.Defs")
        });
        assert!(
            found_cross_file_edge,
            "expected at least one Commutator.lean declaration to resolve a dependency edge \
             into a Defs.lean declaration"
        );

        assert!(corpus.edge_count() > 0);
    }
}
