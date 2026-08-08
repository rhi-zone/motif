import Langlands.NonarchimedeanExponential
import Langlands.NormMap

/-!
# Transporting `exp`/`log` across two `RankOne` instances on the same valued field

## The diamond this file closes

`Langlands.TotallyRamifiedCyclotomicConcreteExample`'s closing section ("Two blockers found")
diagnoses a genuine instance diamond for `v.adicCompletion K`, `K` a number field: this repo's
`Langlands.NormMap.instNontriviallyNormedFieldAdicCompletion` (`Valued.toNontriviallyNormedField`
applied to `Valuation.IsRankOneDiscrete.rankOne _ (e := 2)`) and Mathlib's `NumberField.
HeightOneSpectrum.instNormedFieldValuedAdicCompletion` (the same construction, `e := absNorm
v.asIdeal`) are both registered `NormedField` instances on the same type, and Mathlib's wins
instance search (confirmed by `#synth NormedField (v.adicCompletion K)` resolving to the
`absNorm`-based instance whenever both are in scope). Every `‖·‖` written in a file importing both
elaborates to Mathlib's norm, while `Langlands.NonarchimedeanExponential`'s `exp`/`log` (built in
`Langlands.NormMap`'s scope) are stated in terms of the repo's.

**Root cause, confirmed at the Lean level (not just diagnosed).** `Valued.toNormedField`/
`Valued.toNontriviallyNormedField` (`Mathlib.Topology.Algebra.Valued.NormedValued`) set
`toUniformSpace := Valued.toUniformSpace` — literally the ambient `Valued` instance's own uniform
space, independent of which `RankOne` instance (`hv`) is supplied. Both competing instances here
are built from the *same* ambient `Valued (v.adicCompletion K) ℤᵐ⁰`, so their `toUniformSpace`
fields are the identical term; this is checked directly (`rfl`, no `PseudoMetricSpace.ext`-style
argument needed) for both concrete instances in a scratch reproduction. So the two instances share
a topology and differ *only* in `norm`/`dist`, by a fixed `rpow` scaling
(`Langlands.NormMap.Valuation.norm_rankOne_rpow`): this is **not** the `HenselianValuation`
`UniformSpaceTransport` situation (built for two `NormedField`s with *unrelated*, non-defeq
`UniformSpace`s, needing `PseudoMetricSpace.ext` to unify them) — here the uniform space is free,
and the only work is showing the `choose`n limits `NonarchimedeanExponential.exp`/`log` extract from
Cauchy sequences agree despite being extracted relative to different `norm`s, via
`tendsto_nhds_unique` on the shared topology.

## Main results

* `tendsto_nhds_unique_of_topologicalSpace_eq` : a fully general combinator (no `NormedField`/
  valuation content) — a sequence's limit is the same regardless of which of two *equal*
  topologies is used to compute it. This is the reusable core of the transport argument.
* `NonarchimedeanExponential.exp_eq_of_rankOne`, `.log_eq_of_rankOne` : for *any* `Valued K Γ₀` and
  any two `RankOne (Valued.v)` instances, `exp`/`log` agree on the common convergence domain. Not
  scoped to `v.adicCompletion K` or to this repo's chosen `e := 2` — it is the general shape of
  every future diamond of this kind (any number-field-specific concrete instance mixing this
  repo's `NormMap` machinery with a Mathlib `RankOne` built at a different `e`).
* `NonarchimedeanExponential.norm_lt_convergenceRadius_iff_of_rankOne` : for the two `rankOne`-built
  instances specifically, membership in `exp`'s convergence domain is instance-independent — an
  `hx` hypothesis proved under one instance transfers to the other for free, via
  `Valuation.norm_rankOne_rpow`.

## What this does *not* close

Blocker (2) of the concrete file (`IsGalois (v.adicCompletion K) (w.adicCompletion L)`, needed by
`Langlands.AdicCompletionNormExpTrace.norm_exp_eq_exp_trace`) is untouched and is a separate,
independently-fixable gap. Wiring `exp_eq_of_rankOne`/`norm_lt_convergenceRadius_iff_of_rankOne`
into the concrete cyclotomic file itself (to actually invoke `norm_exp_eq_exp_trace` under
Mathlib's ambient instance) is not done here either — the diamond is closed at the infrastructure
level, but assembling it with the concrete example still needs blocker (2) resolved first.
-/

noncomputable section

open Filter Topology NonarchimedeanExponential
open scoped WithZero NNReal

/-- **A sequence's limit does not depend on which of two equal topologies is used to state
convergence.** Purely about `Filter.Tendsto`/`nhds`, with no reference to `NormedField`,
`Valuation`, or any other structure — the fully general form of the argument
`NonarchimedeanExponential.exp_eq_of_rankOne` below specializes: if `f` tends to `L₁` in `nhds`
computed from `t₁` and to `L₂` in `nhds` computed from `t₂`, and `t₁ = t₂`, then `L₁ = L₂` by
uniqueness of limits in a Hausdorff space. Used to identify two `choose`n limits (here, `exp`/`log`
values) that were extracted relative to two different, but topologically-equal, ambient
structures. -/
theorem tendsto_nhds_unique_of_topologicalSpace_eq {α β : Type*} {f : α → β}
    {l : Filter α} [l.NeBot] {t₁ t₂ : TopologicalSpace β} (ht : t₁ = t₂)
    [@T2Space β t₂] {L₁ L₂ : β}
    (h₁ : @Filter.Tendsto α β f l (@nhds β t₁ L₁))
    (h₂ : @Filter.Tendsto α β f l (@nhds β t₂ L₂)) : L₁ = L₂ := by
  subst ht
  exact tendsto_nhds_unique h₁ h₂

/-- **`NonarchimedeanExponential.exp` agrees across any two `RankOne` instances on the same
`Valued` field, on their common convergence domain.**

The two instances share `toUniformSpace = Valued.toUniformSpace` unconditionally (`rfl`,
independent of `hv`), so `[CompleteSpace K]`, `[T2Space K]`, and the ring structure `[Field K]`
`[CharZero K]` are single ambient hypotheses valid for both; only the `norm`s and hence the
convergence-domain hypotheses (`hnorm₁`/`hnorm₂`, `hx₁`/`hx₂`) genuinely differ per instance. The
proof feeds each instance's own `tendsto_partialSum_exp` into
`tendsto_nhds_unique_of_topologicalSpace_eq`. -/
theorem NonarchimedeanExponential.exp_eq_of_rankOne
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [val : Valued K Γ₀]
    [CompleteSpace K] [T2Space K] [CharZero K] {p : ℕ} [hp : Fact p.Prime]
    (hv₁ hv₂ : Valuation.RankOne val.v) {x : K}
    (hnorm₁ : @norm K (Valued.toNormedField K Γ₀ (hv := hv₁)).toNorm (p : K) < 1)
    (hnorm₂ : @norm K (Valued.toNormedField K Γ₀ (hv := hv₂)).toNorm (p : K) < 1)
    (hx₁ : @norm K (Valued.toNormedField K Γ₀ (hv := hv₁)).toNorm x
        < @convergenceRadius K (Valued.toNormedField K Γ₀ (hv := hv₁)) p)
    (hx₂ : @norm K (Valued.toNormedField K Γ₀ (hv := hv₂)).toNorm x
        < @convergenceRadius K (Valued.toNormedField K Γ₀ (hv := hv₂)) p) :
    @exp K (Valued.toNormedField K Γ₀ (hv := hv₁)) (by haveI := hv₁; infer_instance) _ p hp
        ‹CompleteSpace K› hnorm₁ x
      = @exp K (Valued.toNormedField K Γ₀ (hv := hv₂)) (by haveI := hv₂; infer_instance) _ p hp
        ‹CompleteSpace K› hnorm₂ x := by
  apply tendsto_nhds_unique_of_topologicalSpace_eq
    (l := (Filter.atTop : Filter ℕ))
    (f := fun m => ∑ k ∈ Finset.range (m + 1), x ^ k / (k.factorial : K)) rfl
  · exact @tendsto_partialSum_exp K (Valued.toNormedField K Γ₀ (hv := hv₁))
      (by haveI := hv₁; infer_instance) _ p hp ‹CompleteSpace K› hnorm₁ x hx₁
  · exact @tendsto_partialSum_exp K (Valued.toNormedField K Γ₀ (hv := hv₂))
      (by haveI := hv₂; infer_instance) _ p hp ‹CompleteSpace K› hnorm₂ x hx₂

/-- The `log` analogue of `NonarchimedeanExponential.exp_eq_of_rankOne`; same proof shape, fed
`tendsto_partialSum_log` instead. -/
theorem NonarchimedeanExponential.log_eq_of_rankOne
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [val : Valued K Γ₀]
    [CompleteSpace K] [T2Space K] [CharZero K] {p : ℕ} [hp : Fact p.Prime]
    (hv₁ hv₂ : Valuation.RankOne val.v) {x : K}
    (hnorm₁ : @norm K (Valued.toNormedField K Γ₀ (hv := hv₁)).toNorm (p : K) < 1)
    (hnorm₂ : @norm K (Valued.toNormedField K Γ₀ (hv := hv₂)).toNorm (p : K) < 1)
    (hx₁ : @norm K (Valued.toNormedField K Γ₀ (hv := hv₁)).toNorm x
        < @logConvergenceRadius K (Valued.toNormedField K Γ₀ (hv := hv₁)) p)
    (hx₂ : @norm K (Valued.toNormedField K Γ₀ (hv := hv₂)).toNorm x
        < @logConvergenceRadius K (Valued.toNormedField K Γ₀ (hv := hv₂)) p) :
    @log K (Valued.toNormedField K Γ₀ (hv := hv₁)) (by haveI := hv₁; infer_instance) _ p hp
        ‹CompleteSpace K› hnorm₁ x
      = @log K (Valued.toNormedField K Γ₀ (hv := hv₂)) (by haveI := hv₂; infer_instance) _ p hp
        ‹CompleteSpace K› hnorm₂ x := by
  apply tendsto_nhds_unique_of_topologicalSpace_eq
    (l := (Filter.atTop : Filter ℕ))
    (f := fun m => ∑ k ∈ Finset.range m, (-1 : K) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K)) rfl
  · exact @tendsto_partialSum_log K (Valued.toNormedField K Γ₀ (hv := hv₁))
      (by haveI := hv₁; infer_instance) _ p hp ‹CompleteSpace K› hnorm₁ x hx₁
  · exact @tendsto_partialSum_log K (Valued.toNormedField K Γ₀ (hv := hv₂))
      (by haveI := hv₂; infer_instance) _ p hp ‹CompleteSpace K› hnorm₂ x hx₂

/-- **Membership in `exp`'s convergence domain is independent of which `rankOne`-built instance
is used to test it.** A direct corollary of `Valuation.norm_rankOne_rpow`: since `‖x‖₁ = ‖x‖₂ ^ r`
and `‖p‖₁ = ‖p‖₂ ^ r` for `r := log e₁ / log e₂ > 0`, the convergence radius itself scales the same
way (`convergenceRadius₁ = convergenceRadius₂ ^ r`), and `rpow` by a fixed positive exponent is
order-preserving. This is what lets a convergence-domain hypothesis established under one instance
(e.g. this repo's `e := 2`) discharge the corresponding hypothesis of `exp_eq_of_rankOne` under the
other (e.g. Mathlib's `e := absNorm v.asIdeal`), without redoing the geometric-series estimate. -/
theorem NonarchimedeanExponential.norm_lt_convergenceRadius_iff_of_rankOne
    {K : Type*} [Field K] [val : Valued K ℤᵐ⁰]
    [Valuation.IsRankOneDiscrete val.v] {p : ℕ} [Fact p.Prime]
    {e₁ e₂ : ℝ≥0} (he₁ : 1 < e₁) (he₂ : 1 < e₂) (x : K) :
    @norm K (Valued.toNormedField K ℤᵐ⁰
        (hv := Valuation.IsRankOneDiscrete.rankOne val.v he₁)).toNorm x
        < @convergenceRadius K
          (Valued.toNormedField K ℤᵐ⁰ (hv := Valuation.IsRankOneDiscrete.rankOne val.v he₁)) p
      ↔ @norm K (Valued.toNormedField K ℤᵐ⁰
          (hv := Valuation.IsRankOneDiscrete.rankOne val.v he₂)).toNorm x
        < @convergenceRadius K
          (Valued.toNormedField K ℤᵐ⁰ (hv := Valuation.IsRankOneDiscrete.rankOne val.v he₂)) p := by
  have hr : (0 : ℝ) < Real.log e₁ / Real.log e₂ :=
    div_pos (Real.log_pos (by exact_mod_cast he₁)) (Real.log_pos (by exact_mod_cast he₂))
  have hnx : @norm K (Valued.toNormedField K ℤᵐ⁰
      (hv := Valuation.IsRankOneDiscrete.rankOne val.v he₁)).toNorm x
        = (@norm K (Valued.toNormedField K ℤᵐ⁰
            (hv := Valuation.IsRankOneDiscrete.rankOne val.v he₂)).toNorm x)
          ^ (Real.log e₁ / Real.log e₂) :=
    Valuation.norm_rankOne_rpow val.v he₁ he₂ x
  have hnp : @norm K (Valued.toNormedField K ℤᵐ⁰
      (hv := Valuation.IsRankOneDiscrete.rankOne val.v he₁)).toNorm (@Nat.cast K _ p)
        = (@norm K (Valued.toNormedField K ℤᵐ⁰
            (hv := Valuation.IsRankOneDiscrete.rankOne val.v he₂)).toNorm (@Nat.cast K _ p))
          ^ (Real.log e₁ / Real.log e₂) :=
    Valuation.norm_rankOne_rpow val.v he₁ he₂ _
  have hp2nonneg : (0 : ℝ) ≤ @norm K (Valued.toNormedField K ℤᵐ⁰
      (hv := Valuation.IsRankOneDiscrete.rankOne val.v he₂)).toNorm (p : K) :=
    @Valuation.norm_nonneg K _ ℤᵐ⁰ _ val.v (Valuation.IsRankOneDiscrete.rankOne val.v he₂) (p : K)
  have hx2nonneg : (0 : ℝ) ≤ @norm K (Valued.toNormedField K ℤᵐ⁰
      (hv := Valuation.IsRankOneDiscrete.rankOne val.v he₂)).toNorm x :=
    @Valuation.norm_nonneg K _ ℤᵐ⁰ _ val.v (Valuation.IsRankOneDiscrete.rankOne val.v he₂) x
  have hcr : @convergenceRadius K
      (Valued.toNormedField K ℤᵐ⁰ (hv := Valuation.IsRankOneDiscrete.rankOne val.v he₁)) p
      = (@convergenceRadius K
          (Valued.toNormedField K ℤᵐ⁰ (hv := Valuation.IsRankOneDiscrete.rankOne val.v he₂)) p)
          ^ (Real.log e₁ / Real.log e₂) := by
    unfold NonarchimedeanExponential.convergenceRadius
    rw [hnp, (Real.rpow_mul hp2nonneg (Real.log e₁ / Real.log e₂) (((p : ℝ) - 1)⁻¹)).symm,
      (Real.rpow_mul hp2nonneg (((p : ℝ) - 1)⁻¹) (Real.log e₁ / Real.log e₂)).symm, mul_comm]
  have hcr2nonneg : (0 : ℝ) ≤ @convergenceRadius K
      (Valued.toNormedField K ℤᵐ⁰ (hv := Valuation.IsRankOneDiscrete.rankOne val.v he₂)) p := by
    unfold NonarchimedeanExponential.convergenceRadius; exact Real.rpow_nonneg hp2nonneg _
  rw [hnx, hcr, Real.rpow_lt_rpow_iff hx2nonneg hcr2nonneg hr]

end
