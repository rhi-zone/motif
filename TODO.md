# TODO

## Known limitations

- **Saturation incompleteness**: Some derivable theorems (double complement, zero annihilation, additive commutativity in rings) require reverse identity/absorption rules that cause e-graph blowup. These are added as explicit axioms instead. A more principled approach to controlled term introduction would help.
- **No binder support**: Can't express quantified axioms or lambda terms in the s-expression language.
- **Flat s-expressions**: Pattern matching in `classify.rs` is fragile — adding new axiom shapes requires new detector functions.

## Potential next work

- Vector space theory (scalar field + module axioms — first parameterized theory)
- Morphisms as first-class objects (homomorphisms within a theory, not just translations between)
- Lean 4 backend for cross-system verification
- Theory definition files (`.theory`) loaded from disk
