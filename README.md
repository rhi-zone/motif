# motif

Structural exploration of mathematics: theories as e-graphs, equivalences discovered by saturation, translations between theories checked for axiom preservation.

## What it does

motif represents an algebraic theory (a signature of operations plus equational axioms) as an [egglog](https://egglog-lang.org/) e-graph. Saturating the e-graph under the axioms surfaces equivalences between expressions that weren't stated up front — the theory tells you what it implies, not just what you wrote down. On top of that core, motif can:

- **Classify** theories by detecting structural properties (commutativity, idempotence, etc.) from axiom patterns
- **Check subtheory / inclusion** relationships and build a **theory lattice** from pairwise inclusion
- **Discover morphisms** — operation mappings between theories that preserve axioms
- **Diff** what two theories prove about the same expression
- **Conjecture** novel equivalences in an extended theory relative to a weaker base
- **Export to Lean 4** to cross-check discovered equivalences against an independent kernel

Theories are written in a small `.theory` DSL (see `examples/*.theory` for group, monoid, ring, lattice, field, and other algebraic structures) and driven through the `motif` CLI (`crates/motif-cli`) or used as a library (`crates/motif`).

```
theory Group {
  ops: e/0, inv/1, mul/2
  notation: e = const "e", inv = postfix "⁻¹", mul = infix "·" 6
  axiom right_identity: (mul a (e)) = a
  axiom left_inverse: (mul (inv a) a) = (e)
  axiom associativity: (mul (mul a b) c) = (mul a (mul b c))
}
```

## Why

Mathematics is a dense graph of structural relationships, not a tree of fields — the boundaries between algebra, analysis, topology, and so on are filing systems, not properties of the underlying structure. motif treats theories as compilable, cross-checkable objects: the same equational content can be saturated for implied equivalences, translated into another theory, or exported to a different formal kernel (Lean/Mathlib, via the `langlands` subproject) to see what each representation does or doesn't see. Full rationale in `docs/research/vision.md`.

## Layout

- `crates/motif` — core library: theory representation, egglog compilation, classification, inclusion, discovery, diffing, Lean export
- `crates/motif-cli` — the `motif` command-line binary
- `examples/*.theory` — sample algebraic theories
- `langlands/` — a Lean 4 + Mathlib subproject used as an independent cross-check backend
- `docs/research/` — vision, prior-art survey of proof assistant kernels, and roadmap

## Docs

Full documentation: https://docs.rhi.zone/motif/

## License

Licensed under MIT OR Apache-2.0.
