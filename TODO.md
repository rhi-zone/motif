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

## Potential next work

- Vector space theory (scalar field + module axioms — first parameterized theory)
- Morphisms as first-class objects (homomorphisms within a theory, not just translations between)
- Translation/morphism DSL files for file-based workflow
- Axiom-guided morphism synthesis (use axiom constraints to derive templates instead of enumerating candidates)
- Bi-interpretability / Morita equivalence detection between theories
