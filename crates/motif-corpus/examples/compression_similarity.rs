//! Probe: does compressibility track anything meaningful about a Mathlib
//! declaration?
//!
//! Structure = compressibility. This example turns each declaration in the
//! committed test corpus into a canonical string, measures its compression
//! ratio (raw size / compressed size) as a per-declaration "density" signal,
//! and computes pairwise Normalized Compression Distance (NCD) to find the
//! most similar declarations by that signal.
//!
//! # Encoding choice
//!
//! The corpus (`DeclRecord`) does not carry the declaration's source text —
//! only a byte range into a source file we don't have loaded here. So the
//! canonical string is built from what the record *does* carry:
//!
//! - `k` (kind) and `doc` (docstring, if any) — cheap, stable metadata.
//! - `premises[].fullName` in encounter order — which lemmas/constants the
//!   proof term invokes, in the order they're used. This is the closest
//!   proxy we have to "what mathematical machinery does this declaration
//!   depend on."
//! - `tactics[].stateBefore`/`stateAfter` in encounter order — the actual
//!   goal-state text at each proof step. This is the closest proxy we have
//!   to "what does the proof actually do," independent of tactic syntax.
//!
//! Order is preserved (not sorted) because proof/premise order is itself
//! structure a compressor can exploit (e.g. repeated near-identical
//! before/after states from a chain of `rw`/`simp` steps compress very
//! well; that's a real signal, not noise to normalize away).
//!
//! `def`s with no tactic trace and few premises encode to very short
//! strings; that's expected and reported as such below rather than hidden.

use flate2::write::DeflateEncoder;
use flate2::Compression;
use motif_corpus::{load, DeclRecord};
use std::io::Write;
use std::path::Path;

/// Canonical string encoding for a declaration. See module docs for the
/// rationale behind each field's inclusion and ordering.
fn encode(r: &DeclRecord) -> String {
    let mut s = String::new();
    s.push_str(&r.k);
    s.push('\n');
    if let Some(doc) = &r.doc {
        s.push_str(doc);
        s.push('\n');
    }
    for p in &r.premises {
        s.push_str(&p.full_name);
        s.push(',');
    }
    s.push('\n');
    for t in &r.tactics {
        s.push_str(&t.state_before);
        s.push_str("=>");
        s.push_str(&t.state_after);
        s.push('\n');
    }
    s
}

/// Compressed size in bytes of `data` under raw DEFLATE at max compression.
/// Raw deflate (no gzip/zlib header) so tiny strings aren't dominated by
/// fixed container overhead.
fn compressed_size(data: &[u8]) -> usize {
    let mut enc = DeflateEncoder::new(Vec::new(), Compression::best());
    enc.write_all(data).expect("in-memory write can't fail");
    enc.finish().expect("in-memory finish can't fail").len()
}

/// NCD(x, y) = (C(xy) - min(C(x), C(y))) / max(C(x), C(y))
fn ncd(cx: usize, cy: usize, x: &[u8], y: &[u8]) -> f64 {
    let mut xy = Vec::with_capacity(x.len() + y.len());
    xy.extend_from_slice(x);
    xy.extend_from_slice(y);
    let cxy = compressed_size(&xy);
    (cxy as f64 - cx.min(cy) as f64) / cx.max(cy) as f64
}

fn main() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("testdata/group-cross-file-sample.jsonl");
    let records = load(&path).expect("corpus should load");
    println!(
        "loaded {} declarations from {}",
        records.len(),
        path.display()
    );

    let encoded: Vec<String> = records.iter().map(encode).collect();
    let raw_sizes: Vec<usize> = encoded.iter().map(|s| s.len()).collect();
    let comp_sizes: Vec<usize> = encoded
        .iter()
        .map(|s| compressed_size(s.as_bytes()))
        .collect();

    // Per-declaration compression ratio (raw / compressed). Skip
    // pathologically tiny strings (empty premises+tactics+doc) where the
    // ratio is dominated by fixed deflate overhead rather than content.
    let mut ratios: Vec<(usize, f64)> = raw_sizes
        .iter()
        .zip(&comp_sizes)
        .enumerate()
        .filter(|(_, (&raw, _))| raw >= 16)
        .map(|(i, (&raw, &comp))| (i, raw as f64 / comp.max(1) as f64))
        .collect();

    ratios.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());

    println!("\n=== corpus-level density: compression ratio (raw/compressed) ===");
    println!(
        "n = {} declarations with raw encoded size >= 16 bytes",
        ratios.len()
    );
    let mean: f64 = ratios.iter().map(|(_, r)| r).sum::<f64>() / ratios.len() as f64;
    let var: f64 =
        ratios.iter().map(|(_, r)| (r - mean).powi(2)).sum::<f64>() / ratios.len() as f64;
    println!("mean ratio = {:.3}, stddev = {:.3}", mean, var.sqrt());

    println!("\n--- top 8 MOST compressible (highest ratio = most redundant/boilerplate) ---");
    for &(i, ratio) in ratios.iter().take(8) {
        let r = &records[i];
        println!(
            "  {:6.2}x  {:<40} kind={:<9} raw={:4}B comp={:3}B  tactics={} premises={}",
            ratio,
            r.id,
            r.k,
            raw_sizes[i],
            comp_sizes[i],
            r.tactics.len(),
            r.premises.len()
        );
    }

    println!("\n--- top 8 LEAST compressible (lowest ratio = most novel/irreducible) ---");
    for &(i, ratio) in ratios.iter().rev().take(8) {
        let r = &records[i];
        println!(
            "  {:6.2}x  {:<40} kind={:<9} raw={:4}B comp={:3}B  tactics={} premises={}",
            ratio,
            r.id,
            r.k,
            raw_sizes[i],
            comp_sizes[i],
            r.tactics.len(),
            r.premises.len()
        );
    }

    // Pairwise NCD. 360 declarations -> ~64.6k pairs, each pair a single
    // deflate call over a concatenation of typically-short strings -- cheap
    // enough to just do exhaustively for a corpus this size instead of
    // restricting scope up front.
    println!("\n=== pairwise NCD (Normalized Compression Distance) ===");
    let n = records.len();
    let mut best: Vec<(f64, usize, usize)> = Vec::new();
    for i in 0..n {
        for j in (i + 1)..n {
            if raw_sizes[i] < 16 || raw_sizes[j] < 16 {
                continue; // same floor as the ratio ranking above
            }
            let d = ncd(
                comp_sizes[i],
                comp_sizes[j],
                encoded[i].as_bytes(),
                encoded[j].as_bytes(),
            );
            best.push((d, i, j));
        }
    }
    best.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
    println!("computed NCD over {} pairs", best.len());

    println!("\n--- top 12 closest pairs by NCD (smallest distance = most similar) ---");
    for &(d, i, j) in best.iter().take(12) {
        println!(
            "  NCD={:.4}  {} <-> {}  (kinds {}/{}, modules {}/{})",
            d, records[i].id, records[j].id, records[i].k, records[j].k, records[i].m, records[j].m
        );
    }

    println!("\n--- 6 farthest pairs by NCD (largest distance = least similar) ---");
    for &(d, i, j) in best.iter().rev().take(6) {
        println!(
            "  NCD={:.4}  {} <-> {}  (kinds {}/{}, modules {}/{})",
            d, records[i].id, records[j].id, records[i].k, records[j].k, records[i].m, records[j].m
        );
    }
}
