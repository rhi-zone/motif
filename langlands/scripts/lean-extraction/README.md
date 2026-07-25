# Lean extraction: batch corpus pipeline

Two Lean scripts and one Rust loader that turn Mathlib source files into a
queryable JSONL corpus of declarations, each carrying both statement-level
metadata and proof-structure data (tactic states, premise references).

This is infra, not an analysis: it exists so the *next* structure-discovery
experiment (clustering, similarity search, morphism search, whatever) can
load real data with one function call instead of re-deriving a Lean
extraction pipeline from scratch.

## Files

- `ExtractOne.lean` — the original prototype. Takes one file + an explicit
  line range, re-elaborates the file, and dumps tactic-tree + premise data
  for whatever falls in that range. Superseded by `ExtractBatch.lean` for
  corpus generation; kept as-is since it was tonight's first verified
  artifact and is a smaller reference for the InfoTree-walking core.
- `ExtractBatch.lean` — the batch corpus extractor. Takes a list of files,
  elaborates each ONCE, and emits one JSON record per declaration found in
  that file, joining statement-level metadata with proof-structure data
  in the same pass (see "Design choices" below).
- `README.md` — this file.

## Running it

From inside `~/git/lean-pool` (its `lake env` has built Mathlib oleans, on
`lean-toolchain` `v4.32.0-rc1`), under `nix develop
~/git/rhizone/motif/langlands` (provisions `elan`, which auto-switches to
lean-pool's pinned toolchain):

```bash
cd ~/git/lean-pool
nix develop ~/git/rhizone/motif/langlands --command \
  lake env lean --run ~/git/rhizone/motif/langlands/scripts/lean-extraction/ExtractBatch.lean \
    /path/to/out.jsonl \
    .lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean \
    .lake/packages/mathlib/Mathlib/Algebra/Group/Commutator.lean \
    .lake/packages/mathlib/Mathlib/Algebra/Group/Embedding.lean \
    .lake/packages/mathlib/Mathlib/Algebra/Group/ConjFinite.lean \
    .lake/packages/mathlib/Mathlib/Algebra/Group/Idempotent.lean
```

First CLI argument is the output JSONL path; the rest are `.lean` file
paths (relative to CWD or absolute — both work, see "Module name
resolution" below). To extend to a bigger batch, just list more files. A
config file / module-list-based invocation was judged unnecessary for now —
a shell glob or a generated argument list covers it (e.g. `$(find
.lake/packages/mathlib/Mathlib/Algebra/Group -maxdepth 1 -name '*.lean')`);
add a config-file reader if a future experiment needs to select modules
some other way than shell globbing.

**Memory grows across the batch — split large batches into multiple
invocations.** `ExtractBatch.lean` runs all listed files in one Lean
process, and per-file `Environment`/elaboration state is not released
between files. On this machine (54 GB RAM), processing all 32 top-level
`.lean` files in `Mathlib/Algebra/Group/` in a single invocation hit ~29.5
GB RSS partway through file 23 and got SIGTERM'd by `earlyoom`
(confirmed via `journalctl -k`, not a script bug — the process produces
correct output right up to the kill, it's pure unbounded growth). The fix
used here: split the file list into two (or more) invocations, each
producing its own JSONL, then concatenate — this is safe because the
cross-file dependency join (see below) happens afterward in Rust, over
however many JSONL files/invocations you feed it, so splitting the Lean
side costs nothing except needing to pick a split point empirically (23
files was the observed ceiling for this batch on this machine; expect it to
vary with declaration size/complexity, not just file count). Don't pipe a
run through `time (...)` or similar without a generous timeout / without
checking `$?` — a `SIGTERM`-killed run can still print plausible-looking
"N declarations" progress lines and leave a *truncated last JSONL line* on
disk that will fail to parse; always verify the run's own "wrote N
declarations across M files" completion line printed, not just that the
process exited.

```bash
cd ~/git/lean-pool
FILES=$(find .lake/packages/mathlib/Mathlib/Algebra/Group -maxdepth 1 -name '*.lean' | sort)
# split point (23) is empirically the observed memory ceiling for this
# directory on a 54 GB machine — re-check for other directories/machines.
nix develop ~/git/rhizone/motif/langlands --command \
  lake env lean --run ~/git/rhizone/motif/langlands/scripts/lean-extraction/ExtractBatch.lean \
    /path/to/part1.jsonl $(echo "$FILES" | head -n 23)
nix develop ~/git/rhizone/motif/langlands --command \
  lake env lean --run ~/git/rhizone/motif/langlands/scripts/lean-extraction/ExtractBatch.lean \
    /path/to/part2.jsonl $(echo "$FILES" | tail -n +24)
cat /path/to/part1.jsonl /path/to/part2.jsonl > /path/to/combined.jsonl
```

Then load `part1.jsonl`/`part2.jsonl` (or the concatenated file — either
works) together via `motif_corpus::Corpus::load` to get cross-file edges
spanning both invocations; see "Cross-file dependency join" below.

### Verified test run (2026-07-25, 32-file batch)

All 32 top-level `.lean` files in `Mathlib/Algebra/Group/` (subdirectories
excluded — e.g. `Subgroup/`, `Units/` — to keep this a bounded slice rather
than the whole tree), split into two invocations (files 1–23, then 24–32,
per the memory note above) → **2399 declarations**, **3.3 MB** combined
JSONL, **~45s + ~14s ≈ 59s** wall-clock across both invocations. See
"Cross-file dependency join" below for the graph stats this batch was run
to produce.

### Verified test run (2026-07-25, 5-file batch)

5 files (`Defs.lean` + 4 small neighbors in
`Mathlib/Algebra/Group/`) → **392 declarations**, **412 KB** JSONL, **~8s**
wall-clock (most of it Mathlib import/elaboration of `Defs.lean`; the 4
small files took ~5s combined for all of them). 60 of the 392 declarations
carry a non-empty tactic trace (the rest are term-mode proofs/defs, where
`ExtractOne`'s `TacticInfo`-only walk correctly finds no tactic steps).

## Corpus JSONL schema

One JSON object per line, one line per declaration:

```json
{
  "id": "zpow_negSucc",
  "n": "zpow_negSucc",
  "m": "Mathlib.Algebra.Group.Defs",
  "k": "theorem",
  "r": [1065, 0, 1067, 34],
  "s": [1065, 8],
  "doc": null,
  "deps": ["zpow_natCast", "Monoid", "DivInvMonoid.toZPow", "..."],
  "tdeps": ["zpow_natCast", "..."],
  "ext": 20,
  "tactics": [
    {
      "stateBefore": "G : Type u_1\ninst✝ : DivInvMonoid G\n...\n⊢ a ^ Int.negSucc n = (a ^ (n + 1))⁻¹",
      "stateAfter": "...",
      "pos": 45727,
      "endPos": 45748
    }
  ],
  "premises": [
    {
      "fullName": "zpow_natCast",
      "modName": "Mathlib.Algebra.Group.Defs",
      "pos": {"line": 1066, "column": 8},
      "endPos": {"line": 1066, "column": 20}
    }
  ]
}
```

Field meanings:

| field | meaning |
|---|---|
| `id` | fully qualified declaration name |
| `n` | display name (may differ from `id` for private decls) |
| `m` | module (see "Module name resolution" below) |
| `k` | `theorem` \| `def` \| `opaque` \| `axiom` \| `structure` \| `inductive` |
| `r` | full declaration byte range as `[startLine, startCol, endLine, endCol]` (1-based lines, 0-based cols) |
| `s` | name-selection range `[nameLine, nameCol]` |
| `doc` | docstring, if any |
| `deps` | **intra-file** dependency edges (kernel-closure-expanded through generated auxiliaries, same algorithm as lean-pool's `Extract.lean`) |
| `tdeps` | statement-only (type) dependency edges — present only for `theorem`s (proof is elided in the "does this need X to elaborate" sense) |
| `ext` | count of distinct dependencies NOT resolved to a `deps`/`tdeps` edge — i.e. out-of-file or otherwise external |
| `tactics` | array of `{stateBefore, stateAfter, pos, endPos}` — before/after pretty-printed goal states per tactic step, `pos`/`endPos` are **byte offsets** into the source file |
| `premises` | array of `{fullName, modName, pos, endPos}` — constants referenced inside this declaration's elaborated term, `pos`/`endPos` are `{line, column}` positions (Lean `Position`, 1-based lines / 0-based cols) — note this uses a DIFFERENT position encoding than `tactics` (byte offset vs line/col); both come straight from the underlying InfoTree walk and were left as-is rather than normalized, since neither extractor needed the other's encoding |

## Design choices

**Statement + proof-structure extraction folded into one pass**, rather
than running lean-pool's `Extract.lean` and `ExtractOne.lean`'s successor
separately and joining by declaration name afterward. `ExtractBatch.lean`
re-elaborates the whole file with `infoState.enabled := true` (needed for
the InfoTree walk), which produces a full `Environment` with extension
state populated — the same thing `Extract.lean`'s statement-level queries
(`isGenerated`, `findDeclarationRanges?`, `isStructure`, docstrings, ...)
need. Since full elaboration is already paid for, running `Extract.lean`'s
`importModules ... loadExts := false` afterward as a second pass would be
pure waste — it exists as a fast path specifically for when you *don't*
want to pay elaboration cost. One elaboration, one InfoTree walk, one
record per declaration.

**Declaration boundaries**: after `IO.processCommands` on the file's own
(unimported) source, a constant newly introduced by that file has NO
module index yet — `Environment.getModuleIdxFor?` only resolves constants
that arrived via an imported `.olean`. So "defined in this file" is exactly
`getModuleIdxFor? = none`. This is also the fallback branch `ExtractOne.lean`
already relied on for premise module-name attribution
(`if let some modIdx := ... else env.header.mainModule`), so it's a
verified-consistent assumption, not a new guess. Given that predicate,
declaration ranges come from `findDeclarationRanges?` (same call
`Extract.lean` uses), and each tactic/premise trace entry (which carries a
byte position from the InfoTree walk) is assigned to the first declaration
whose byte span contains it.

**Module name resolution**: `moduleNameOfFileName` needs a source root
directory to strip off the file path; our `LEAN_PATH` only has *built*
`.olean` directories, not source roots, so passing `none` produces a raw,
ugly module name (e.g. `«.lake».packages.mathlib.Mathlib.Algebra.Group.…`).
`ExtractBatch.lean`'s `guessRootDir` heuristic splits the path at its first
capitalized component (Lean/Lake convention: `<lowercase-package-dir>/
<CapitalizedRootNamespace>/...`, e.g. `.lake/packages/mathlib/Mathlib/...`)
and passes everything before that as the root. This is a heuristic, not a
proper search-path lookup — see Known limitations.

## Known limitations / next-step flags

- **Cross-file dependency join is Rust-side and name-based, not
  scope-based.** `Corpus::from_records` (see "Cross-file dependency join"
  below) resolves edges purely by matching `deps`/`tdeps`/`premises[].fullName`
  strings against other loaded records' `id` field. This is safe because
  Lean fully-qualified names are globally unique, but it means the edge set
  is exactly as complete as the corpus you load — a name that isn't backed
  by a loaded record (because that file wasn't included in the batch) stays
  unresolved, same as the file-scoped `ext` counter, just now correctly
  spanning however many files you actually load together. It does not
  re-derive anything Lean-side; if two different `ExtractBatch.lean`
  invocations are joined, correctness depends on `id` truly being globally
  unique across them (true for real Mathlib declarations, would NOT hold
  if the same file were accidentally extracted twice into the same corpus
  — no duplicate-detection is done).
- **`ExtractBatch.lean`'s per-invocation memory grows with batch size and
  is not released between files** — see "Memory grows across the batch" in
  "Running it" above. Large batches need to be split into multiple
  invocations (safe: the cross-file join happens afterward in Rust, so
  splitting the Lean-side extraction into N invocations costs nothing
  edge-wise as long as all N outputs get loaded into the same `Corpus`).
  No fix was attempted on the Lean side tonight (e.g. forcibly dropping
  `Environment`s between files, or forking a subprocess per file) — the
  split-invocation workaround was judged sufficient for corpus sizes in the
  low thousands of declarations; it will not scale to unattended
  full-Mathlib extraction without either a real fix or a lot of manual
  splitting.
- **Declaration-assignment for overlapping ranges is first-match, not
  innermost-match.** If Lean's `findDeclarationRanges?` produces nested or
  overlapping ranges (e.g. auxiliary declarations from a `where` clause),
  a trace entry goes to whichever declaration is encountered first when
  scanning, not necessarily the innermost enclosing one. Not observed as
  an issue on the tested files, but not verified against files with heavy
  `where`/`let rec` usage either.
- **`guessRootDir`'s module-name heuristic** assumes the Lean/Lake
  lowercase-dir/Capitalized-namespace convention. It works for the tested
  Mathlib/lean-pool layout but is not a substitute for a real source
  search path; a file that violates the convention gets an unresolved
  raw module name instead of failing loudly.
- **`tactics[].pos` (byte offset) vs `premises[].pos` (line/column)** use
  different encodings, inherited unchanged from `ExtractOne.lean`'s two
  code paths (`TacticInfo` used `String.Pos.Raw` directly; `TermInfo` went
  through `FileMap.toPosition`). Left unnormalized rather than guessing
  which encoding a future consumer wants — normalize in the Rust loader or
  in Lean, whichever the first real consumer needs.
- **Not tested past ~2.4k declarations / 32 files.** Verified on a 32-file,
  2399-declaration batch (see "Cross-file dependency join" below).
  Full-Mathlib extraction (100k+ declarations) remains explicitly out of
  scope; the memory-growth issue above means it would need either a real
  per-file memory fix or scripted splitting into many invocations, neither
  of which has been built.

## Cross-file dependency join

`ExtractBatch.lean` still elaborates each file independently, so a
declaration's `deps`/`tdeps`/`premises` fields are just names — they don't
resolve to other declarations even when the referenced declaration is
another record sitting in the same corpus. `crates/motif-corpus` closes
this gap on the Rust side: `Corpus::from_records` (or `Corpus::load`,
which loads one or more JSONL files and joins them in one step) builds a
`name -> DeclId` index over every loaded record's `id` field, then resolves
each record's `deps` ∪ `tdeps` ∪ `premises[].fullName` against that index.
Names that resolve become real `Vec<DeclId>` edges (`Corpus::dependencies`);
names that don't stay unresolved, same meaning as `ext` but now correctly
computed at whole-corpus scope instead of per-file. `Corpus::in_degrees`
and `Corpus::edge_count` are the only other operations — deliberately
minimal, no clustering/similarity/query layer on top (that's for whichever
experiment builds on this next).

This works file-name-agnostically because Lean fully-qualified names
(`DeclRecord.id`, `PremiseTrace.full_name`) are globally unique — verified
by reading real corpus output before deciding on this approach (rather
than assuming): every `id`/`fullName` in the checked corpus is already a
dotted fully-qualified path (`Mathlib.Algebra.Group.Defs`,
`DivInvMonoid.zpow_neg'`, etc.), so no extra name-resolution logic
(overload disambiguation, relative-name lookup) was needed on the Lean
side — the existing fields were sufficient.

### Verified cross-file graph stats (32-file batch, 2026-07-25)

Loading both halves of the 32-file batch (see above) into one `Corpus`:

| metric | value |
|---|---|
| declarations | 2399 |
| resolved cross-declaration edges | 6312 |
| average out-degree | 2.63 |
| declarations with ≥1 resolved dependency | 2163 / 2399 (90%) |

Top in-degree ("most depended-upon") declarations — a sanity check that the
join is finding real structure, not just resolving self-references:

| in-degree | declaration | module |
|---|---|---|
| 120 | `Monoid` | `Mathlib.Algebra.Group.Defs` |
| 105 | `AddChar` | `Mathlib.Algebra.Group.AddChar` |
| 90 | `AddMonoid` | `Mathlib.Algebra.Group.Defs` |
| 88 | `DivisionMonoid.toDivInvOneMonoid` | `Mathlib.Algebra.Group.Basic` |
| 86 | `SubtractionMonoid.toSubNegZeroMonoid` | `Mathlib.Algebra.Group.Basic` |
| 83 | `Semigroup` | `Mathlib.Algebra.Group.Defs` |
| 58 | `mul_assoc` | `Mathlib.Algebra.Group.Defs` |

`Monoid`, `Semigroup`, `mul_assoc` sitting at the top of the in-degree list
is exactly what's expected from the algebraic hierarchy this directory
defines — a real signal that the join is doing something meaningful, not
just structurally present with degenerate output.

## Rust loader

`crates/motif-corpus` (new crate, workspace member via the existing
`members = ["crates/*"]` glob in the top-level `Cargo.toml`) — `serde`-based
struct definitions (`DeclRecord`, `TacticTrace`, `PremiseTrace`, `Position`)
mirroring this schema field-for-field, plus:

- `motif_corpus::load(path) -> io::Result<Vec<DeclRecord>>` — reads one
  JSONL file line-by-line into `Vec<DeclRecord>`, no joining.
- `motif_corpus::Corpus` — wraps loaded records plus the resolved
  cross-declaration dependency graph described above. `Corpus::load(paths)`
  is the one-call entry point: load N JSONL files (from N
  `ExtractBatch.lean` invocations, e.g. after splitting a batch for the
  memory reason above) and get back edges resolved across all of them.

Still no query engine, no indexing beyond the one `name -> DeclId` map used
internally to build the edge list — deliberately just enough that a future
experiment can `cargo run` or write a short script against real loaded data
with real dependency edges. See `crates/motif-corpus/src/lib.rs`.

Two corpus samples are checked in:

- `testdata/group-defs-sample.jsonl` — single-file (`Defs.lean`, 392
  declarations), exercises `load` and the statement/proof-structure join
  (`loads_sample_corpus` test).
- `testdata/group-cross-file-sample.jsonl` — two files (`Defs.lean` +
  `Commutator.lean`, 360 declarations total), exercises `Corpus::load`
  resolving a real dependency edge from `Commutator.lean` into a
  `Defs.lean` declaration (`resolves_cross_file_dependency_edges` test) —
  i.e. proves the join actually crosses file boundaries, not just
  resolving each file against itself.

The full 32-file/2399-declaration corpus used for the graph stats above is
not checked in (3.3 MB, and reproducible in ~1 minute via the two-invocation
command in "Running it"); only the two smaller, purpose-built samples are.

## Structure-discovery prototypes (2026-07-25)

Three deliberately-throwaway probes were built in parallel against
`crates/motif-corpus/testdata/group-cross-file-sample.jsonl` (360
declarations, `Defs.lean` + `Commutator.lean`) to test different notions of
"structure discovery" over the corpus before committing to one direction.
All three live in `crates/motif-corpus/examples/` and are kept as-is —
they're real, working, informative probes, not scratch to delete once a
headline result lands or doesn't.

### `paradigmatic_clusters.rs` — dependency-set Jaccard clustering

Linguistic-structuralist framing: a declaration's "paradigmatic class" is
the set of other declarations whose *context* (resolved out-edge set —
union of `deps`/`tdeps`/`premises[].fullName`) is Jaccard-similar to its
own, following the distributional-similarity move ("a term is
characterized by the company it keeps"). Clustering is greedy
threshold + union-find over all pairs at Jaccard ≥ 0.6, restricted to
declarations with ≥ 3 resolved dependencies (to avoid vacuous clustering
of near-empty context sets).

Result: 26 clusters, ~25 of which looked genuinely structural — e.g. the
`zpow`-family lemmas clustered together, and notably `LeftCancelMonoid`
and `RightCancelMonoid` lemma families formed two separate, mirror-image
clusters purely from dependency structure, without ever being told
left/right are related. That's a real symmetry the data reproduced on its
own, not an artifact of naming.

One clear artifact: a 42-member catch-all cluster, caused by greedy
transitive-closure chaining — union-find merges A and C into one cluster
once both A~B and B~C clear the threshold, even though A~B and B~C
similarity doesn't imply A~C similarity. A real fix needs either
connected-components-with-min-density (not plain union-find) or a proper
clustering algorithm (e.g. threshold graph + community detection) instead
of naive pairwise-threshold transitive closure.

### `compression_similarity.rs` — NCD over string-encoded declarations (paused)

Encoded each declaration as a string (kind + doc + premises in encounter
order + tactic state transitions), computed per-declaration DEFLATE
compression ratio, and computed full pairwise Normalized Compression
Distance (`NCD(x,y) = (C(xy) - min(C(x),C(y))) / max(C(x),C(y))`) across
all ~64.6k pairs in the 360-declaration corpus.

Headline result: NCD's closest pairs rediscovered Mathlib's
`@[to_additive]` mul/add mirror structure — e.g.
`AddLeftCancelMonoid`/`AddRightCancelMonoid` at NCD ≈ 0.10, near the top of
the closest-pairs list.

**This result does not survive scrutiny, and that's the important part to
record here — not softened.** Two independent problems:

1. **Circularity.** `to_additive` is itself a Lean metaprogram that
   generates the additive declarations from the multiplicative ones via
   literal mechanical string-level substitution (`Mul`→`Add`, etc.).
   Finding those generated pairs "close" under string compression isn't
   discovering hidden structure — it's recovering a known syntactic
   transformation that already exists as engineering, elsewhere, on
   purpose. Nearly circular, not evidence of anything.
2. **Deeper methodological flaw: reducing structured objects to strings
   is fundamentally wrong, because strings force a total order onto data
   that doesn't intrinsically have one.** Premises are a set; dependency
   structure is a graph; a tactic trace is closer to a tree (branching
   goal states) than a line. "Premises in encounter order" was one
   specific arbitrary choice, but the problem isn't fixable by picking a
   different order, or even a canonical/sorted order — *any* string
   linearization smuggles in an ordering artifact, and that artifact then
   contaminates any distance/compression metric built on top of the
   string (DEFLATE's LZ77 window is itself order-sensitive, so the
   ordering choice isn't neutral to the very metric being computed).

**Decision: pause this direction.** Not deleted, not declared permanently
wrong in principle — information-theoretic notions of structure
(compressibility, MDL, mutual information) aren't inherently invalid, only
*this string-shaped operationalization* of them is. The fix, if revisited,
is a complexity/similarity measure defined natively on sets/graphs/trees,
not on a derived string encoding — nobody has designed that yet.

Contrast: `paradigmatic_clusters.rs` and `morphism_candidates.rs` both use
Jaccard similarity over *sets* (dependency sets, premise sets) —
order-independent by construction — and do not have this problem. That's
why those two are being kept as real signal while this one is paused.

### `morphism_candidates.rs` — cross-declaration similarity ranking

Ranks declaration pairs by combined Jaccard similarity across
dependency-set overlap, premise-vocabulary overlap, and proof-shape/tactic-
count similarity (where tactic data is available), explicitly excluding
`to_additive` mirror pairs via name-normalization (stripping the
Mathlib `add`-prefix convention) — 228 of ~15.6k pairs would otherwise
dominate trivially, for the same circularity reason as the compression
probe above.

Result: validated the plumbing, but the test corpus (`Defs.lean` +
`Commutator.lean`) turned out to be effectively one theory, not two — so
every top-ranked pair was a same-file left/right or mul/inv dual already
obvious from Mathlib's own naming convention (`pow_one` ↔ `one_pow`, etc.).
The best genuinely cross-file pair scored 0.157 similarity, ranked #4653
of 15354 — essentially noise, not signal.

Self-assessed conclusion: this only tested the plumbing (does the ranking
pipeline work at all), not the real question, because the corpus wasn't
diverse enough to contain any actually-unrelated structure to find. The
real target — stated directly by the user this session — is **structural
relationships between parts of the corpus that aren't obviously already
related**, not confirmation of known naming-convention pairs within one
theory. Testing that requires a corpus spanning genuinely distinct
theories (e.g. group + ring, or group + lattice), which this single-theory
test corpus cannot probe by construction. See `TODO.md` for the concrete
next step.
