import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Langlands.NonarchimedeanUnconditionalSummability

/-!
# Flattening a sigma-indexed family of `HasSum`s in an ultrametric group

`Mathlib.Topology.Algebra.InfiniteSum.Constructions`'s `HasSum.sigma_of_hasSum` assembles a flat
`HasSum` on a sigma type `Σ b, γ b` from (a) a `HasSum` for each fiber `c ↦ f ⟨b, c⟩`, (b) a `HasSum`
for the fiber-sums `g`, and (c) `Summable f` on the flat type, supplied as a separate hypothesis (in
general topological additive groups, establishing that third hypothesis needs its own
rearrangement/Cauchy argument).

In a complete ultrametric normed group, `Langlands.NonarchimedeanUnconditionalSummability`'s
`IsUltrametricDist.summable_of_tendsto_zero` gets `Summable f` for free from the much weaker
`Tendsto f cofinite (nhds 0)` (unconditional convergence needs only termwise convergence to zero, no
separate rearrangement argument) — so in this setting, the sigma-flattening assembly only needs that
cofinite-vanishing hypothesis, not a full summability proof. This file records that specialization as
its own named lemma, general-purpose and not tied to any particular series
(this is the "sigma-reindexing" tool identified as needed, but not built, in `ROADMAP.md`'s tenth pass
on the `exp`/`log` mutual-inverse thread, step (i) of the remaining assembly).
-/

@[expose] public section

open Filter

/-- **Sigma-flattening of `HasSum` in a complete ultrametric normed group.** If each fiber
`c ↦ f ⟨b, c⟩` sums to `g b`, the fiber-sums `g` sum to `a`, and `f` (on the flat sigma type) tends to
`0` along `cofinite`, then `f` itself sums to `a`. The only summability work needed is the
`cofinite`-vanishing hypothesis: `IsUltrametricDist.summable_of_tendsto_zero` supplies `Summable f`
from it, which is what the general `HasSum.sigma_of_hasSum` needs as its third hypothesis. -/
theorem HasSum.sigma_of_isUltrametricDist {G : Type*} [NormedAddCommGroup G] [IsUltrametricDist G]
    [CompleteSpace G] {β : Type*} {γ : β → Type*} {f : (Σ _b : β, γ _b) → G} {g : β → G} {a : G}
    (ha : HasSum g a) (hf : ∀ b, HasSum (fun c => f ⟨b, c⟩) (g b))
    (hzero : Tendsto f cofinite (nhds 0)) :
    HasSum f a :=
  ha.sigma_of_hasSum hf (IsUltrametricDist.summable_of_tendsto_zero hzero)
