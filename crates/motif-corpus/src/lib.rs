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
}
