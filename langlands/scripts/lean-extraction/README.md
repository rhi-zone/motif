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

### Verified test run (2026-07-25)

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

- **No cross-file dependency join.** Each input file is elaborated
  independently (matching `ExtractOne.lean`'s single-file re-elaboration
  model). A declaration's `deps`/`tdeps` only include edges to OTHER
  declarations in the SAME file; references to declarations from other
  files in the same batch are counted only via `ext`, never resolved into
  an edge — even if that other file was ALSO in the batch and its
  declarations are sitting right there in the output JSONL. Joining across
  files (e.g. cumulative import + a shared `exposed : NameSet` across the
  whole batch, or a post-hoc join in Rust by matching `id` against `deps`
  from OTHER files' external references) is real future work if an
  experiment needs the dependency graph to span files.
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
- **Not tested at Mathlib scale.** Verified on 5 small-to-medium files
  (392 declarations total, ~8s). Full-Mathlib extraction (100k+
  declarations) was explicitly out of scope tonight; expect memory/runtime
  characteristics to need re-checking before attempting that scale — this
  was infra validation, not a production run.

## Rust loader

`crates/motif-corpus` (new crate, workspace member via the existing
`members = ["crates/*"]` glob in the top-level `Cargo.toml`) — `serde`-based
struct definitions (`DeclRecord`, `TacticTrace`, `PremiseTrace`, `Position`)
mirroring this schema field-for-field, plus `motif_corpus::load(path) ->
io::Result<Vec<DeclRecord>>` reading a JSONL file line-by-line. No query
engine, no indexing — deliberately just enough that a future experiment can
`cargo run` or write a short script against real loaded data. See
`crates/motif-corpus/src/lib.rs`; a corpus sample from the verified test
run is checked in at `crates/motif-corpus/testdata/group-defs-sample.jsonl`
and exercised by the crate's one test (`loads_sample_corpus`).
