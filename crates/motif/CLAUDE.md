# CLAUDE.md — crates/motif

Scoped to the `motif` crate (egglog integration). See the repo-root `CLAUDE.md` for project-wide rules.

## egglog caveats

- Reserved primitive names (cannot be used as constructors): f64 `neg`, `abs`, `min`, `max`, `to-f64`, `to-i64`, `to-string`; i64 `not-i64`, `log2`, `count-matches`; bool `not`, `and`, `or`, `xor`. Use `negate` for algebraic negation.
- Rewrite safety: all RHS variables must appear in LHS; bare variables on LHS cause `Ungrounded`; unbound RHS variables cause `Unbound`.
- Bidirectional rewrites only safe when both sides are constructor expressions with the same free variables. Identity laws (`f(x) = x`) and inverse laws are forward-only — reverse creates unbounded terms. Associativity is safe bidirectional.
- Seed nullary constructors: constants like `(zero)`, `(one)` must be added explicitly via `(let seed_X__ (X))` or axioms referencing them won't fire.
- Use `(ruleset name)` before any `(rule/rewrite ... :ruleset name)`; drive with `(run-schedule (repeat N (run ruleset)))`.
- iter_limit 5–10 is usually enough; 20+ with bidirectional rewrites + distributivity → blowup.
