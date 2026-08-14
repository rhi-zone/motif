/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.TotallyRamifiedResidueField

/-!
# The generator of a monogenic totally ramified extension is a uniformizer

`Langlands/TotallyRamifiedResidueField.lean` uses monogenicity (`Algebra.adjoin 𝒪[K] {π} = 𝒪_L`,
from `LocalField.adjoin_eq_integralClosure_of_isUniformizer`) plus `π ∈ 𝔪_{𝒪_L}` to get
residue-field preservation. The *same* monogenicity, plus the Eisenstein data
`LocalField.isEisensteinAt_minpoly_of_isUniformizer` already supplies, gives the sharper statement
that `π` generates the maximal ideal: `𝔪_{𝒪_L} = (π)`, i.e. `π` is literally a uniformizer of
`𝒪_L`, not merely an element of its maximal ideal.

This is what `Langlands/LubinTateTowerStep.lean` needs of its `α' : O'` — its Weierstrass-preparation
step takes `hα' : Irreducible α'` — so it is the second of the two facts (alongside residue-field
preservation) that turn the abstract moving base `O'` into the concrete `O_{K_1}`.

## Main results

* `IsLocalRing.maximalIdeal_eq_span_of_adjoin_singleton` : the elementary engine, the `𝔪`-level
  companion of `IsLocalRing.residueField_map_surjective_of_adjoin_singleton`. For `B` generated as
  an `A`-algebra by `π ∈ 𝔪_B`, with `𝔪_A · B ⊆ (π)`, one gets `𝔪_B = (π)`. (`IsLocalHom` is *not*
  needed: the direction actually used — `algebraMap A B a` a nonunit forces `a` a nonunit — is free
  for any ring homomorphism, via `IsUnit.map`.)
* `LocalField.coeff_zero_minpoly_associated_of_isUniformizer` : the constant coefficient of
  `minpoly ↥𝒪[K] π` is an *associate* of `ϖ`, upgrading
  `isEisensteinAt_minpoly_of_isUniformizer`'s `∈ 𝔪 ∧ ∉ 𝔪 ^ 2` to the sharp form, via
  `IsDiscreteValuationRing.associated_pow_irreducible`.
* `LocalField.maximalIdeal_integralClosure_eq_span_of_isUniformizer` : `𝔪_{𝒪_L} = (π)`.
* `LocalField.irreducible_of_isUniformizer` : hence `Irreducible (π : 𝒪_L)`, via
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
-/

noncomputable section

open IsLocalRing ValuativeRel Polynomial

/-! ## The elementary engine -/

/-- **A local ring generated over a local subring by one element `π` of the maximal ideal, with
`𝔪_A · B ⊆ (π)`, has `𝔪_B = (π)`.** The `𝔪`-level companion of
`IsLocalRing.residueField_map_surjective_of_adjoin_singleton`, and proved by the same decomposition:
every `x : B` is `Polynomial.aeval π p`, hence `π * aeval π p.divX + algebraMap A B (p.coeff 0)`. If
moreover `x ∈ 𝔪_B` then `algebraMap A B (p.coeff 0) ∈ 𝔪_B`, so `p.coeff 0` is a nonunit of `A`
(a unit would map to a unit, `IsUnit.map`), i.e. `p.coeff 0 ∈ 𝔪_A`; both summands are then in
`(π)`. -/
theorem IsLocalRing.maximalIdeal_eq_span_of_adjoin_singleton
    {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    {π : B} (hπ : π ∈ maximalIdeal B)
    (hadj : Algebra.adjoin A ({π} : Set B) = ⊤)
    (hsub : (maximalIdeal A).map (algebraMap A B) ≤ Ideal.span {π}) :
    maximalIdeal B = Ideal.span {π} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · have hxadj : x ∈ Algebra.adjoin A ({π} : Set B) := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hxadj
    obtain ⟨p, hp⟩ := hxadj
    have hp' : Polynomial.aeval π p = x := hp
    have key : Polynomial.aeval π (Polynomial.X * p.divX + Polynomial.C (p.coeff 0)) =
        Polynomial.aeval π p := by
      rw [Polynomial.X_mul_divX_add]
    have hsplit : π * Polynomial.aeval π p.divX + algebraMap A B (p.coeff 0) = x := by
      rw [← hp', ← key, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
    have hcmem : algebraMap A B (p.coeff 0) ∈ maximalIdeal B := by
      have : algebraMap A B (p.coeff 0) = x - π * Polynomial.aeval π p.divX := by
        rw [← hsplit]; ring
      rw [this]
      exact Ideal.sub_mem _ hx (Ideal.mul_mem_right _ _ hπ)
    have hc0 : p.coeff 0 ∈ maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      exact ((IsLocalRing.mem_maximalIdeal _).mp hcmem) (hu.map (algebraMap A B))
    rw [← hsplit]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
      (hsub (Ideal.mem_map_of_mem _ hc0))
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hπ

namespace LocalField

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(valuation K).valuationSubring]
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

omit [Algebra.IsSeparable K L] in
/-- **The constant coefficient of `minpoly ↥𝒪[K] π` is an associate of `ϖ`.** Sharpens
`isEisensteinAt_minpoly_of_isUniformizer`'s `coeff 0 ∈ 𝔪 ∧ coeff 0 ∉ 𝔪 ^ 2` to an exact
`Associated`: in a discrete valuation ring every nonzero element is an associate of `ϖ ^ m`
(`IsDiscreteValuationRing.associated_pow_irreducible`), and `m = 0` is excluded by `∈ 𝔪`,
`m ≥ 2` by `∉ 𝔪 ^ 2`. -/
theorem coeff_zero_minpoly_associated_of_isUniformizer
    {ϖ : ↥(valuation K).valuationSubring} (hϖ : Irreducible ϖ) {π : L}
    (hram : ‖(ϖ : K)‖ = spectralNorm K L π ^ (minpoly K π).natDegree) :
    Associated ((minpoly ↥(valuation K).valuationSubring π).coeff 0) ϖ := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hπint : IsIntegral ↥(valuation K).valuationSubring π :=
    isIntegral_of_isUniformizer K hϖ hram
  have hEis := isEisensteinAt_minpoly_of_isUniformizer K hϖ hram
  have hdegpos : 0 < (minpoly ↥(valuation K).valuationSubring π).natDegree :=
    minpoly.natDegree_pos hπint
  have hmem : (minpoly ↥(valuation K).valuationSubring π).coeff 0 ∈
      maximalIdeal ↥(valuation K).valuationSubring := hEis.mem hdegpos
  have hnsq : (minpoly ↥(valuation K).valuationSubring π).coeff 0 ∉
      maximalIdeal ↥(valuation K).valuationSubring ^ 2 := hEis.notMem
  have hne : (minpoly ↥(valuation K).valuationSubring π).coeff 0 ≠ 0 := by
    intro h0
    exact hnsq (h0 ▸ Ideal.zero_mem _)
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hϖ
  match m, hv with
  | 0, hv =>
    exact absurd (IsUnit.of_mul_eq_one _ (by simpa using hv))
      ((IsLocalRing.mem_maximalIdeal _).mp hmem)
  | 1, hv => exact ⟨v, by simpa using hv⟩
  | (m + 2), hv =>
    refine absurd ?_ hnsq
    have ha : (minpoly ↥(valuation K).valuationSubring π).coeff 0 =
        ϖ ^ (m + 2) * ((v⁻¹ : (↥(valuation K).valuationSubring)ˣ) :
          ↥(valuation K).valuationSubring) := by
      rw [← hv, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨ϖ ^ m * ((v⁻¹ : (↥(valuation K).valuationSubring)ˣ) :
      ↥(valuation K).valuationSubring), by rw [ha]; ring⟩

/-- **`𝔪_{𝒪_L} = (π)`**: the generator of a monogenic totally ramified extension generates the
maximal ideal of the ring of integers.

`IsLocalRing.maximalIdeal_eq_span_of_adjoin_singleton` reduces this to `𝔪_{𝒪[K]} · 𝒪_L ⊆ (π)`,
i.e. (since `𝔪_{𝒪[K]} = (ϖ)`) to `ϖ ∈ (π)`. That follows from the Eisenstein relation: evaluating
`minpoly ↥𝒪[K] π` at `π` inside `𝒪_L` and splitting off the constant term
(`Polynomial.X_mul_divX_add`) gives `algebraMap (coeff 0) = -π * aeval π (divX …) ∈ (π)`, and
`coeff 0` is an associate of `ϖ` by
`coeff_zero_minpoly_associated_of_isUniformizer`. -/
theorem maximalIdeal_integralClosure_eq_span_of_isUniformizer
    {ϖ : ↥(valuation K).valuationSubring} (hϖ : Irreducible ϖ) {π : L}
    (hram : ‖(ϖ : K)‖ = spectralNorm K L π ^ (minpoly K π).natDegree)
    (hgen : (minpoly K π).natDegree = Module.finrank K L)
    (hπint : IsIntegral ↥(valuation K).valuationSubring π) :
    maximalIdeal ↥(integralClosure ↥(valuation K).valuationSubring L) =
      Ideal.span {(⟨π, hπint⟩ : ↥(integralClosure ↥(valuation K).valuationSubring L))} := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hϖlt : ‖(ϖ : K)‖ < 1 :=
    (mem_maximalIdeal_iff_norm_lt_one K ϖ).mp
      ((IsLocalRing.mem_maximalIdeal _).mpr fun hu => hϖ.not_isUnit hu)
  have hspec : spectralNorm K L π < 1 := by
    by_contra hge
    push Not at hge
    have h1 : (1 : ℝ) ≤ spectralNorm K L π ^ (minpoly K π).natDegree := one_le_pow₀ hge
    rw [← hram] at h1
    linarith
  have hπ'mem : (⟨π, hπint⟩ : ↥(integralClosure ↥(valuation K).valuationSubring L)) ∈
      maximalIdeal ↥(integralClosure ↥(valuation K).valuationSubring L) :=
    mem_maximalIdeal_integralClosure_of_spectralNorm_lt_one K _ hspec
  refine IsLocalRing.maximalIdeal_eq_span_of_adjoin_singleton hπ'mem
    (adjoin_singleton_eq_top_of_isUniformizer K hϖ hram hgen hπint) ?_
  -- `𝔪_{𝒪[K]} · 𝒪_L ⊆ (π)`, via `ϖ ∈ (π)`.
  set q : (↥(valuation K).valuationSubring)[X] := minpoly ↥(valuation K).valuationSubring π with hq
  have haevalS : Polynomial.aeval
      (⟨π, hπint⟩ : ↥(integralClosure ↥(valuation K).valuationSubring L)) q = 0 := by
    refine Subtype.ext ?_
    have haeval := Polynomial.aeval_algHom_apply
      (Subalgebra.val (integralClosure ↥(valuation K).valuationSubring L))
      (⟨π, hπint⟩ : ↥(integralClosure ↥(valuation K).valuationSubring L)) q
    simpa [hq, minpoly.aeval] using haeval.symm
  have hkey : Polynomial.aeval
      (⟨π, hπint⟩ : ↥(integralClosure ↥(valuation K).valuationSubring L))
        (Polynomial.X * q.divX + Polynomial.C (q.coeff 0)) = 0 := by
    rw [Polynomial.X_mul_divX_add]; exact haevalS
  rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hkey
  have hc0span : algebraMap ↥(valuation K).valuationSubring
      ↥(integralClosure ↥(valuation K).valuationSubring L) (q.coeff 0) ∈
      Ideal.span {(⟨π, hπint⟩ : ↥(integralClosure ↥(valuation K).valuationSubring L))} := by
    have : algebraMap ↥(valuation K).valuationSubring
        ↥(integralClosure ↥(valuation K).valuationSubring L) (q.coeff 0) =
        -((⟨π, hπint⟩ : ↥(integralClosure ↥(valuation K).valuationSubring L)) *
          Polynomial.aeval (⟨π, hπint⟩ :
            ↥(integralClosure ↥(valuation K).valuationSubring L)) q.divX) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hkey
    rw [this]
    exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  obtain ⟨w, hw⟩ := coeff_zero_minpoly_associated_of_isUniformizer K hϖ hram
  have hϖspan : algebraMap ↥(valuation K).valuationSubring
      ↥(integralClosure ↥(valuation K).valuationSubring L) ϖ ∈
      Ideal.span {(⟨π, hπint⟩ : ↥(integralClosure ↥(valuation K).valuationSubring L))} := by
    rw [← hw, map_mul]
    exact Ideal.mul_mem_right _ _ hc0span
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_le,
    Set.singleton_subset_iff]
  exact hϖspan

/-- **The generator of a monogenic totally ramified extension is irreducible in `𝒪_L`** — i.e. it is
a uniformizer. Immediate from `maximalIdeal_integralClosure_eq_span_of_isUniformizer` via
`IsDiscreteValuationRing.irreducible_iff_uniformizer`. This is the `hα' : Irreducible α'` input
`Langlands/LubinTateTowerStep.lean`'s Weierstrass-preparation step requires of its moving base. -/
theorem irreducible_of_isUniformizer
    {ϖ : ↥(valuation K).valuationSubring} (hϖ : Irreducible ϖ) {π : L}
    (hram : ‖(ϖ : K)‖ = spectralNorm K L π ^ (minpoly K π).natDegree)
    (hgen : (minpoly K π).natDegree = Module.finrank K L)
    (hπint : IsIntegral ↥(valuation K).valuationSubring π) :
    Irreducible (⟨π, hπint⟩ : ↥(integralClosure ↥(valuation K).valuationSubring L)) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (maximalIdeal_integralClosure_eq_span_of_isUniformizer K hϖ hram hgen hπint)

end LocalField
