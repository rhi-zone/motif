import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Ultrametric normed additive groups are nonarchimedean, hence unconditionally summable

`Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean` proves that in a complete nonarchimedean
additive group (`NonarchimedeanAddGroup`, from `Mathlib.Topology.Algebra.Nonarchimedean.Basic`:
every neighborhood of `0` contains an open subgroup), a function tending to `0` along `cofinite` is
automatically `Summable` (`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`) — the classical
fact that absolute/termwise convergence in an ultrametric setting is *unconditional* convergence,
needing no separate rearrangement argument. But nothing in the vendored Mathlib
(confirmed by exhaustive grep of every file mentioning `IsUltrametricDist` or `NonarchimedeanRing`/
`NonarchimedeanAddGroup`) connects the metric-space notion `IsUltrametricDist` (used throughout
`Langlands.NonarchimedeanExponential`) to the topological-group notion `NonarchimedeanAddGroup` that
this summability lemma actually needs — so the lemma was unreachable for any `IsUltrametricDist`-based
development, including this repo's, without first building that bridge.

This file builds the bridge, in full Mathlib-quality generality (not tied to any specific field or to
`exp`/`log`): **every seminormed additive group with an ultrametric distance is nonarchimedean**
(`IsUltrametricDist.toNonarchimedeanAddGroup`). The proof is short and general: for `r > 0`, the ball
`Metric.ball (0 : G) r` is already an additive subgroup (closed under `+` by the ultrametric triangle
inequality `IsUltrametricDist.norm_add_le_max`, closed under negation by `norm_neg`, contains `0`) and
open (`Metric.isOpen_ball`); since balls of positive radius form a neighborhood basis at `0`
(`Metric.nhds_basis_ball`), this open subgroup can be found inside any neighborhood of `0`.

Combining the two gives `IsUltrametricDist.summable_of_tendsto_zero`: in a *complete* seminormed
additive group with an ultrametric distance, any sequence tending to `0` is unconditionally summable
— exactly the hypothesis needed to upgrade `Langlands.NonarchimedeanExponential.exp`/`.log`'s
along-`range n` `Tendsto` facts (`tendsto_partialSum_exp`, `tendsto_partialSum_log`) to genuine
`HasSum` statements, which is done in `Langlands.NonarchimedeanExponentialHasSum`.

## Ring-level addition: `IsUltrametricDist.toNonarchimedeanRing`

The same gap exists one level up: `Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean` also proves
`HasSum.mul_of_nonarchimedean` (Cauchy product `fun i : α × β ↦ f i.1 * g i.2` sums to `a * b`, for any
two `HasSum`s in a nonarchimedean ring, **with no additional summability hypothesis on the product** —
the nonarchimedean case needs none, unlike the archimedean Mathlib API which requires
`Summable (fun p ↦ f p.1 * g p.2)` as a separate hypothesis, e.g. `HasSum.mul`), but that lemma needs
`NonarchimedeanRing R` (`Mathlib.Topology.Algebra.Nonarchimedean.Basic`: a topological ring whose
underlying additive group is nonarchimedean), and nothing bridges `IsUltrametricDist` to it either.
`IsUltrametricDist.toNonarchimedeanRing` closes that gap: any `SeminormedRing` with an ultrametric
distance is a `NonarchimedeanRing`, by pairing the topological-ring instance every seminormed ring
already carries (`NonUnitalSeminormedRing.toIsTopologicalRing`) with `toNonarchimedeanAddGroup`'s
`is_nonarchimedean` witness (both notions ultimately say "every neighborhood of `0` contains an open
additive subgroup"; `NonarchimedeanRing` just packages that fact together with the ring topology).
This makes `HasSum.mul_of_nonarchimedean`/`Summable.mul_of_nonarchimedean`/
`tsum_mul_tsum_of_nonarchimedean` available, unconditionally, for any `NormedField` (or more generally
`SeminormedRing`) carrying `IsUltrametricDist` — the key remaining tool identified in `ROADMAP.md`'s
ninth pass for the `exp`/`log` mutual-inverse thread's substitution-composition step.
-/

@[expose] public section

namespace IsUltrametricDist

variable {G : Type*} [SeminormedAddCommGroup G] [IsUltrametricDist G]

/-- **A ball of positive radius around `0` in an ultrametric seminormed additive group is an
additive subgroup.** Closure under addition is the ultrametric triangle inequality
(`IsUltrametricDist.norm_add_le_max`); closure under negation is `norm_neg`. -/
def addSubgroupBall {r : ℝ} (hr : 0 < r) : AddSubgroup G where
  carrier := Metric.ball (0 : G) r
  add_mem' {x y} hx hy := by
    simp only [Metric.mem_ball, dist_zero_right] at hx hy ⊢
    exact (norm_add_le_max x y).trans_lt (max_lt hx hy)
  zero_mem' := Metric.mem_ball_self hr
  neg_mem' {x} hx := by
    simp only [Metric.mem_ball, dist_zero_right] at hx ⊢
    rwa [norm_neg]

/-- **`addSubgroupBall`, packaged as an `OpenAddSubgroup`** (balls are always open in a metric
space). -/
def openAddSubgroupBall {r : ℝ} (hr : 0 < r) : OpenAddSubgroup G where
  toAddSubgroup := addSubgroupBall hr
  isOpen' := Metric.isOpen_ball

/-- **Every seminormed additive group with an ultrametric distance is nonarchimedean**: every
neighborhood of `0` contains an open subgroup, namely a small enough ball (`openAddSubgroupBall`),
since balls of positive radius form a neighborhood basis at `0` (`Metric.nhds_basis_ball`). -/
instance (priority := 100) toNonarchimedeanAddGroup : NonarchimedeanAddGroup G where
  is_nonarchimedean U hU := by
    obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_ball.mem_iff.mp hU
    exact ⟨openAddSubgroupBall hr, hrU⟩

/-- **Unconditional summability from convergence to zero, in a complete ultrametric seminormed
additive group.** The classical fact that in a nonarchimedean setting, "the terms tend to zero" is
already enough for unconditional (order-independent) summability — no separate absolute-convergence
or rearrangement argument is needed, unlike the archimedean case. A direct corollary of
`toNonarchimedeanAddGroup` feeding `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`. -/
theorem summable_of_tendsto_zero [CompleteSpace G] {α : Type*} {f : α → G}
    (hf : Filter.Tendsto f Filter.cofinite (nhds 0)) : Summable f :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hf

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R]

/-- **Every seminormed ring with an ultrametric distance is a nonarchimedean ring**: it is already a
topological ring (`NonUnitalSeminormedRing.toIsTopologicalRing`), and its underlying additive group is
nonarchimedean (`toNonarchimedeanAddGroup`, since `SeminormedRing` is in particular a
`SeminormedAddCommGroup`) — exactly the two ingredients `NonarchimedeanRing` packages. This unlocks
`Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean`'s `HasSum.mul_of_nonarchimedean` and friends for
any such ring, with no separate summability side-condition on the product family. -/
instance (priority := 100) toNonarchimedeanRing : NonarchimedeanRing R where
  __ := (inferInstance : IsTopologicalRing R)
  is_nonarchimedean := (toNonarchimedeanAddGroup (G := R)).is_nonarchimedean

end IsUltrametricDist
