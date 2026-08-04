# TODO

## Known limitations

- **Saturation incompleteness**: Some derivable theorems (double complement, zero annihilation, additive commutativity in rings) require reverse identity/absorption rules that cause e-graph blowup. These are added as explicit axioms instead. A more principled approach to controlled term introduction would help.
- **No binder support**: Can't express quantified axioms or lambda terms in the s-expression language.
- **Flat s-expressions**: Pattern matching in `classify.rs` is fragile — adding new axiom shapes requires new detector functions.
- **Discover: shared e-graph saturation blowup**: Morphism discovery builds a separate e-graph per (axiom, candidate-combo) check. A single shared e-graph would be faster (one saturation pass), but theories with distributivity/commutativity (e.g. rings) blow up when many candidate-translated expressions are added together. Incremental saturation or e-graph cloning could fix this.
- **Discover: enumerate-then-check**: Template candidates are generated blind to axiom structure, then brute-force checked. When axioms tightly constrain the morphism (e.g. `sub(a,a) = zero`, `sub(a,zero) = a` together force `sub → add + negate`), a synthesis approach that derives the template from axiom constraints would avoid enumeration entirely.
- **Discover: argument dropping**: `uses_all_args` rejects templates that don't reference every positional arg, ruling out valid interpretations like projections (`proj(a,b) → a`) and constant maps (`absorb(a) → zero`).
- **Discover: depth ceiling**: Template depth is bounded by enumeration. Interesting morphisms can require deep templates (depth 4+) where candidate counts are already intractable at depth 2 against larger signatures.
- **One-way morphisms only**: `discover` finds source→target interpretations. Morita equivalence — two theories that interpret each other but share no direct signature morphism (e.g. groups via `{e, inv, mul}` vs `{div}`) — requires round-trip discovery and equivalence-of-interpretations checking, neither of which exists yet.

## Vision: proof comprehension

Long-term goal: given any proof, explain every step by finding its structural meaning — what move is being made, and where that same move appears elsewhere in mathematics. The "graph of all proofs" falls out naturally as exhaust from this process.

Key ideas:
- A proof step is represented in *all* extractable projections simultaneously (formal term, equational content, categorical structure, natural language, etc.) — all added to the e-graph as equivalent nodes
- The architecture is intentionally substrate-neutral: nodes carry arbitrary content, edges are typed relations ("is a projection of," "is a proof of," "is an instance of"), e-graph handles equivalence
- Content (which nodes matter, which rewrites are meaningful) is the research problem; the substrate shouldn't foreclose anything

Near-term: **Lean/Mathlib proof step extraction and annotation**
1. Pick a simple Mathlib proof (basic group theory result)
2. Extract proof steps (tactic tree or term)
3. Extracted data (tactic tree, premises, statement metadata) is itself a
   valid native representation — not raw material to translate into motif's
   `Signature`/`Theory` vocabulary before it "counts." (Corrected 2026-07-25,
   user direction — see `docs/research/vision.md` principle 9: motif has no
   single canonical substrate everything funnels through.)
4. Once enough corpus data is extracted, look for structural relationships
   across it directly in its native form: symmetries, isomorphisms,
   translations between pieces/regions, and gaps/density variation in what's
   proven vs. what neighboring structure would suggest. Kept intentionally
   vague — this is a near-term *direction*, not a designed plan; concrete
   cross-representation relationship-finding machinery is future work.
5. Output: annotated proof/corpus region where structural relationships found
   so far are recorded

This is the smallest concrete exercise of the full vision, and the gaps it reveals drive what to build next.

**2026-07-25 extraction scaffolding**: two working extraction paths, both run successfully against Mathlib built inside `~/git/lean-pool`.

1. **Statement-level extraction** — lean-pool's own `scripts/exposition/Extract.lean` (external repo, not vendored here), run via `lake env lean --run` after retargeting its `poolRoot` constant at an arbitrary Mathlib module (e.g. `Mathlib.Algebra.Group.Defs`). Schema at `~/git/lean-pool/python/lean_pool/exposition/SCHEMA.md`; one JSON object per declaration:
   ```json
   {"id": "Foo.aux", "n": "Foo.aux", "m": "Mathlib.Algebra.Group.Defs",
    "k": "theorem", "r": [435, 0, 446, 23], "s": [435, 6],
    "deps": ["<id>", ...], "ext": 127}
   ```
   Extracted 356 declarations from one file in seconds (after `lake update mathlib` cache-built, ~2m48s, cache hit, no source build).

2. **Proof-structure extraction** — `langlands/scripts/lean-extraction/ExtractOne.lean`, ported from LeanDojo v1's `ExtractData.lean` (LeanDojo's Python package is deprecated; this Lean-side logic walks Lean's stable `Elab.InfoTree` API directly, no LeanDojo dependency). Per declaration: full tactic tree with before/after pretty-printed proof-state text at each step (including sub-goal branches, e.g. induction cases), plus a premise trace (which prior lemmas/constants each tactic step invokes, with source positions). Invocation:
   ```
   lake env lean --run langlands/scripts/lean-extraction/ExtractOne.lean <mathlib-file> <startLine> <endLine>
   ```
   run from inside `~/git/lean-pool` (so `LEAN_PATH` resolves its built Mathlib oleans), under `nix develop langlands --command ...` (langlands' flake provisions elan; lean-pool's `lean-toolchain` pins v4.32.0-rc1, distinct from langlands' own v4.32.1 — elan switches per-project toolchain automatically). Verified on `mul_pow_mul` in `Mathlib.Algebra.Group.Defs` (real multi-step induction proof, `zero`/`succ` case branching, `succ` case shows premises `pow_succ'`/`mul_assoc`); re-verified after moving the script into this repo. Example output shape:
   ```json
   {"tactics": [{"stateBefore": "case zero\n...\n⊢ (a * b) ^ 0 * a = a * (b * a) ^ 0",
                 "stateAfter": "no goals", "pos": 29161, "endPos": 29165}],
    "premises": [{"fullName": "mul_pow_mul", "modName": "...Defs",
                  "pos": {"line": 693, "column": 21}, "endPos": {"line": 693, "column": 32}}]}
   ```
   Porting note (only break going from LeanDojo's Lean v4.20 pin to v4.32.0-rc1): `String.Pos` became an indexed structure (`structure String.Pos (s : String)`, part of a byte/codepoint safety overhaul); fixed by using `String.Pos.Raw` (the plain `{byteIdx : Nat}` struct `Syntax.getPos?`/`FileMap` APIs already return) and projecting `.byteIdx` in the `ToJson` instance. Everything else (`InfoTree`, `TacticInfo`, `ContextInfo.runMetaM`, `Command.mkState`, `IO.processCommands`) ported unchanged.

   Considered ntp-toolkit (CMU L3 lab) as an alternative — actively maintained, lighter footprint, but flatter output schema (flat `(state, nextTactic)` JSONL rows, no explicit tactic tree/premises) — chose the LeanDojo InfoTree-porting approach for full fidelity instead. LeanDojo-v2 (actively maintained successor to the deprecated v1 package) not evaluated in depth — unexplored.

   Corpus scope (decided): mathlib4 (full, ~300K declarations order of magnitude) + lean-pool's own indexed projects + TauCeti (no extraction tooling of its own yet — needs the same approach pointed at it). Extract structure of both proofs and proven statements, kept in their native Lean-derived form (tactic tree, premises, statement metadata) — no requirement to flatten into motif's quantifier-free `Signature` representation first (see "No single substrate" correction above; the typeclass-hierarchy/binder-heavy-statement vs. flat `Signature` gap noted in "No binder support" above is a real gap for *that one representation*, not a blocker for corpus analysis in general).

   Next steps (unstarted):
   - Run `ExtractOne.lean` across a small batch of files to check the porting note generalizes (only tested on one declaration so far).
   - Once there's enough extracted corpus data, start looking for structural relationships across it in its native form (step 4 of the near-term plan above) — direction only, no design yet.

**2026-07-25 structure-discovery prototypes**: three throwaway probes built against the 360-declaration `group-cross-file-sample.jsonl` corpus to test different notions of structure discovery — see `langlands/scripts/lean-extraction/README.md` ("Structure-discovery prototypes" section) for full results. Summary: dependency-set Jaccard clustering (`crates/motif-corpus/examples/paradigmatic_clusters.rs`) and cross-declaration similarity ranking (`morphism_candidates.rs`) both produced real signal and are being kept; string-encoded NCD/compression similarity (`compression_similarity.rs`) is paused — its headline `to_additive`-mirror result turned out circular (recovering a known mechanical transformation) and its whole approach has a deeper flaw (linearizing sets/graphs into strings smuggles in an arbitrary order that then contaminates any distance metric on top).

Next steps (direction, not a plan):
- `paradigmatic_clusters.rs`: fix the greedy transitive-closure artifact (one 42-member catch-all cluster from naive union-find chaining, A~B~C merged despite A≁C) — needs connected-components-with-min-density or real community detection instead of pairwise-threshold transitive closure.
- `morphism_candidates.rs`: the test corpus (`Defs.lean` + `Commutator.lean`) is effectively one theory, so every top-ranked pair was an already-obvious same-theory naming-convention dual. The user's stated real goal is finding shared structure between *unrelated* parts of the corpus — testing that needs a corpus spanning genuinely distinct theories (e.g. group + ring, or group + lattice), not more files within group theory.

Relevant fields to eventually handle: Langlands program, HoTT/CoC, elliptic curves, harmonic analysis (Kakeya hierarchy), BB(5)-style exhaustive classification, Curry-Howard-Lambek correspondence.

## Potential next work

- Vector space theory (scalar field + module axioms — first parameterized theory)
- Morphisms as first-class objects (homomorphisms within a theory, not just translations between)
- Translation/morphism DSL files for file-based workflow
- Axiom-guided morphism synthesis (use axiom constraints to derive templates instead of enumerating candidates)
- Bi-interpretability / Morita equivalence detection between theories
- **Mathlib: Henselian valued fields — algebraic extensions are Henselian.** Prove "valuation rings of algebraic extensions of a Henselian field are Henselian" in Mathlib/Lean. Confirmed missing entirely (2026-08-04): Mathlib's only Henselian-related file, `Mathlib/RingTheory/Henselian.lean`, has just the bare definitions + two lemmas — nothing about integral/algebraic extensions, no Krasner's-lemma-style machinery. This is a standard classical fact (one of the characterizing properties of Henselian valued fields, same family as unique-extension-of-valuation, itself confirmed classical via Engler-Prestel/Ribenboim). Would unblock `langlands/Langlands/UnramifiedExtension.lean`'s `exists_restrictNormalHom_decompositionSubgroup_surjective` sorry (this is "route 1" of two routes considered there; "route 2", a discriminant-unit/monogenic-order argument, was chosen instead for that session since route 1 has zero Mathlib scaffolding to build from and is closer to its own standalone PR-sized Mathlib contribution than a quick extension of existing work). Worth a dedicated future pass independent of whether route 2 succeeds — it's generally useful beyond this one theorem.

### [x] Update CLAUDE.md — corrections as documentation lag (2026-03-29)

Add to the corrections section:
> **Corrections are documentation lag, not model failure.** When the same mistake recurs, the fix is writing the invariant down — not repeating the correction. Every correction that doesn't produce a CLAUDE.md edit will happen again. Exception: during active design, corrections are the work itself — don't prematurely document a design that hasn't settled yet.

Add to the Session Handoff section:
> **Initiate a handoff after a significant mid-session correction.** When a correction happens after substantial wrong-path work, the wrong reasoning is still in context and keeps pulling. Writing down the invariant and starting fresh beats continuing with poisoned context — the next session loads the invariant from turn 1 before any wrong reasoning exists.

Conventional commit: `docs: add corrections-as-documentation-lag + context-poisoning handoff rule`
