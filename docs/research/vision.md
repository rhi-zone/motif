# Vision: Structural Exploration of Mathematics

Core ideas distilled from early design conversations. This is the "why" and
"what" — the "how" lives in the architecture and prior art documents.

## Thesis

Mathematics is a dense graph of structural relationships, not a tree of fields.
The boundaries between disciplines — algebra, analysis, topology, combinatorics
— are human filing systems, not properties of mathematical reality.

Discovery happens by navigating structure, not by enumerating possibilities.

## Core Principles

### 1. Math is a graph, not a tree

Fields are clusters in a graph, not branches of a tree. Deep results are hubs
with high connectivity, not leaves. The "hyphenated fields" (algebraic topology,
analytic number theory, geometric group theory) are where action happens — the
partitions are porous.

Multiple parentage is normal. Cycles are normal. Concepts get re-rooted across
eras. Trees forbid all of this; math thrives on it.

### 2. Tools transfer, formulas don't

The universal layer of mathematical knowledge is structural moves:

- Symmetry / group actions
- Composition / morphisms
- Optimization / variational principles
- Duality (Fourier, Pontryagin, LP, categorical)
- Linearity / linear algebra
- Equivalence / isomorphism

Specific formulas are domain-local expressions of these tools. The formula is
context-bound, representation-specific, optimized for a domain. The tool is
abstract, transferable, and discipline-agnostic.

Fields don't contain tools — tools generate fields. Fields are clusters where
certain tools proved useful together.

### 3. DSLs as sugar over shared IR(s)

Mathematicians already use implicit DSLs everywhere:

- "Let X be a smooth..." (analysis DSL)
- G ↷ X (group-action DSL)
- E[·|F] (probability DSL)
- Commutative diagrams (category DSL)
- O(·), ~, ≈ (asymptotics DSL)
- "wlog", "for a.e." (meta-DSL / proof-control-flow)

The existence of DSLs isn't the question. The question is what a formal system
does with that reality. The goal: make the implicit elaboration explicit and
shareable. Not invent DSLs — absorb them as observed phenomena.

Key subtlety: DSLs aren't just syntax. They encode:
- Default coercions (N ⊂ Z ⊂ Q ⊂ R)
- Standard identifications ("up to iso")
- Hidden hypotheses (measurable, compact, smooth)
- Which equality notion is in play
- Information-hiding regimes (what's "obvious" to omit)

### 4. Multiple interchangeable bottoms

No single foundation is "the" correct one. Production proof assistants chose
five genuinely different kernels (Lean/CIC, Coq/pCIC, Agda/MLTT, Idris/QTT,
ATS/separated statics-dynamics), all encoding "the same math" with different
natural representations.

The set of bottoms must be extensible/interchangeable. The truth is in the
invariants across translations, not in any single representation.

Foundations are coordinate systems on a shared structure space, not the root of
a tree.

### 5. Cross-compile + diff = discovery

Compile the same math through multiple IR pipelines. Translate between
representations. Diff modulo known/continuously learned equivalences. Residuals
reveal:

- Hidden assumptions
- Structural invariants
- Accidental vs. essential distinctions
- New equivalences to add to the library

This is differential testing applied to mathematical semantics. It's translation
validation for math.

Learning E (the equivalence set) is essentially learning mathematics. Even
partial E is useful.

### 6. Pruning >> search

The interesting manifold in mathematical idea-space is measure-zero within
rounding error. Discovery isn't brute-force enumeration — it's navigation.

Good priors beat cheap compute. Ramanujan wasn't searching more; he was pruning
better. His intuition acted as a strong prior, a heuristic filter, a pattern
salience detector landing disproportionately in fertile regions.

The bottleneck is learning good taste in idea-space. That's partly culture,
training, mentorship, immersion, feedback loops — not just compute.

### 7. Cross-field translation as removing artificial restrictions

Translation isn't mapping A → B. It's removing boundaries that were never
fundamental. Domain-dependence is superficial; the transferable structure is what
matters.

Cross-field barriers exist because of:
- Historical accidents
- Notation traditions
- Pedagogy paths
- Journal communities
- Cultural identity of fields

Not because reality is partitioned that way.

When barriers drop, things click: algebra + geometry → algebraic geometry.
Logic + CS → type theory. Probability + physics → statistical mechanics. In
hindsight obvious, beforehand unrelated. The borders were bookkeeping, not
ontology.

### 8. Symmetry is a property of structure, not truth

Math has approximate global symmetries — recurring structural motifs:

- Dualities (object ↔ dual, space ↔ function space, primal ↔ dual)
- Discrete ↔ continuous (sums ↔ integrals, graphs ↔ manifolds)
- Algebra ↔ geometry (equations ↔ spaces, operations ↔ transformations)
- Syntax ↔ semantics (programs ↔ proofs, types ↔ propositions)

These are properties of structure, not truth. Symmetry says "these
configurations behave the same under transformation" — that's relational, not
propositional.

Math might be like a curved manifold: locally structured, approximate
symmetries, no global isometry. You move far and see familiar patterns, but not
perfectly.

## Non-Goals

- **Human-writable language.** The IR is machine-targeted. Humans interact
  through surface layers (which are someone else's problem, at least for now).
- **Interop with existing proof assistants.** We're here to explore, not to
  integrate. Existing systems are prior art and potential future backends, not
  integration targets.
- **Replacing Lean/Coq/etc.** Different layer of the stack. Those are formal
  truth engines. This is a structure/translation engine.
- **Forcing mathematicians to adopt anything.** The system is formalization as
  mirror, not as leash. Capture what mathematicians already do without requiring
  new habits.

## Open Questions

- What are the first structural primitives? Composition, morphisms, rewrite
  rules? At what granularity?
- Where exactly does the e-graph layer meet the structural primitives layer?
- How do you represent binders in an e-graph-friendly way?
- What's the first concrete mathematical domain to ground the abstractions?
- How do you formalize "interestingness" / structural salience for pruning?
- Can the equivalence set E be learned, or must it be curated?
