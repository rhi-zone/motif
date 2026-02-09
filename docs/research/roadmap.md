# Roadmap

Where motif is heading, roughly ordered by readiness.

## 1. Deepen algebra (mostly done)

Stay in the universal algebra lane and make it robust before generalizing.

- ~~More theories: monoid, abelian group, lattice, field~~ ✓ (+ semiring, boolean algebra)
- ~~Translation composition: chain forgetful functors (ring → group → monoid)~~ ✓
- ~~Axiom preservation checking: validate that translations are structure-preserving~~ ✓
- ~~Structural property detection and classification from axiom patterns~~ ✓
- ~~Saturation diff: compare equivalences across theories~~ ✓
- ~~Theory inclusion / subtheory checking~~ ✓
- ~~Automatic theory lattice from pairwise inclusion~~ ✓
- ~~Theory definition DSL parser~~ ✓
- Remaining: vector space (requires scalar field + module axioms)

## 2. Structural primitives

Abstract the recurring patterns (composition, duality, morphisms) as first-class
concepts in the type system, not just as axioms within theories.

- Morphisms as first-class: not just translations between theories, but arrows
  within a theory (homomorphisms, isomorphisms)
- Composition as explicit structure, not implicit in axiom chaining
- Duality: formalize the object ↔ dual pattern that recurs everywhere
- Functoriality: translations that preserve composition automatically

This is the "math is a graph" thesis becoming concrete.

## 3. Cross-backend

Export to at least one proof assistant to test the cross-compilation thesis
across genuinely different formal systems.

- Lean 4 backend: compile Theory → Lean declarations
- Verify: same axioms, same equivalences discovered independently
- Diff: what does Lean's type theory see that egglog's e-graphs don't, and vice versa?
- This is "multiple interchangeable bottoms" from the vision doc

## 4. Surface language

A human-friendly DSL for defining theories and translations, so the workflow
isn't "write Rust structs by hand."

- Parser for a lightweight theory definition language
- REPL or notebook interface for interactive exploration
- Visualization of the theory graph (which theories exist, how they're connected)

## Open questions (from vision doc, still unresolved)

- Where does the e-graph layer meet structural primitives? Are they the same layer?
- How to represent binders (lambda, quantifiers) in an e-graph-friendly way?
- How to formalize "interestingness" for pruning the saturation space?
- Can the equivalence set E be learned from examples, or must it be curated?
- What's the right granularity for structural primitives?
