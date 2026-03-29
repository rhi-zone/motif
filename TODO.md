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
3. Match each step against motif's existing theory/axiom vocabulary
4. Identify what new structure unmatched steps require
5. Output: annotated proof where each step is labeled with its structural meaning

This is the smallest concrete exercise of the full vision, and the gaps it reveals drive what to build next.

Relevant fields to eventually handle: Langlands program, HoTT/CoC, elliptic curves, harmonic analysis (Kakeya hierarchy), BB(5)-style exhaustive classification, Curry-Howard-Lambek correspondence.

## Potential next work

- Vector space theory (scalar field + module axioms — first parameterized theory)
- Morphisms as first-class objects (homomorphisms within a theory, not just translations between)
- Translation/morphism DSL files for file-based workflow
- Axiom-guided morphism synthesis (use axiom constraints to derive templates instead of enumerating candidates)
- Bi-interpretability / Morita equivalence detection between theories

### [x] Update CLAUDE.md — corrections as documentation lag (2026-03-29)

Add to the corrections section:
> **Corrections are documentation lag, not model failure.** When the same mistake recurs, the fix is writing the invariant down — not repeating the correction. Every correction that doesn't produce a CLAUDE.md edit will happen again. Exception: during active design, corrections are the work itself — don't prematurely document a design that hasn't settled yet.

Add to the Session Handoff section:
> **Initiate a handoff after a significant mid-session correction.** When a correction happens after substantial wrong-path work, the wrong reasoning is still in context and keeps pulling. Writing down the invariant and starting fresh beats continuing with poisoned context — the next session loads the invariant from turn 1 before any wrong reasoning exists.

Conventional commit: `docs: add corrections-as-documentation-lag + context-poisoning handoff rule`
