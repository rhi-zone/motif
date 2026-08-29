/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.TowerBundle
import Langlands.TotallyRamifiedResidueField
import Langlands.TotallyRamifiedUniformizer

/-!
# Residue-field preservation and uniformizer-ness over an intermediate extension

`Langlands/TowerBundle.lean` builds the complete-discretely-valued `ValuativeRel` bundle on an
intermediate extension `M / K` carrying no valuation structure of its own — only a
`A : ValuationSubring M` lying over `𝒪[K]` plus a `RankOne A.valuation` instance — and uses it to
transport `Langlands.TotallyRamifiedEisenstein.LocalField.adjoin_eq_integralClosure_of_isUniformizer`
to base `M`. This file supplies the two matching `_of_valuationSubring` variants for a tower
argument that needs to move the base up one level (e.g. from `K` to an intermediate `K_1`) rather
than working with the fixed base `K`:
`Langlands.TotallyRamifiedResidueField.residueField_map_bijective_of_isUniformizer` and
`Langlands.TotallyRamifiedUniformizer.irreducible_of_isUniformizer`, both restated with their base
field taken to be such an `M`, by the same `letI`-substitution `TowerBundle.lean` already uses — no
new mathematical content, only that transport.

## Why this is a separate file, not an addition to `TowerBundle.lean`

`Langlands.TotallyRamifiedResidueField`/`Langlands.TotallyRamifiedUniformizer` import
`Langlands.MonogenicIntegralClosure`, which itself imports `Langlands.TowerBundle` (for
`isDiscreteValuationRing_valuation_valuationSubring_of_finiteDimensional`, used to build the
concrete `O_{K_1}` DVR instance). Importing either into `TowerBundle.lean` directly would close a
cycle (`TowerBundle → TotallyRamifiedResidueField → MonogenicIntegralClosure → TowerBundle`); this
file sits downstream of all three instead.

## Main results

* `LocalField.residueField_map_bijective_of_isUniformizer_of_valuationSubring` : the residue field
  of `𝒪_M` (built as `↥A`) maps bijectively onto the residue field of `𝒪_N`, for `N / M` finite
  separable with a totally ramified generator.
* `LocalField.irreducible_of_isUniformizer_of_valuationSubring` : that generator, viewed in `𝒪_N`,
  is irreducible there — a genuine uniformizer of `𝒪_N`.

Both are reusable at every tower level: `M` is an arbitrary field carrying only a `ValuationSubring`
over `𝒪[K]`, not specific to any particular intermediate field. Applying them *at* a concrete
intermediate field (i.e. discharging `A`, `hA`, `hR` there concretely) is a separate, further step.
-/

open ValuativeRel Valuation IsLocalRing

namespace LocalField

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  {M : Type*} [Field M] [Algebra K M] [FiniteDimensional K M]

/-- **Residue-field preservation over an intermediate extension.**
`LocalField.residueField_map_bijective_of_isUniformizer` (`Langlands.TotallyRamifiedResidueField`)
applied with its base field taken to be `M / K` as above: under the same hypothesis package as
`LocalField.adjoin_eq_integralClosure_of_isUniformizer_of_valuationSubring`
(`Langlands/TowerBundle.lean`), the residue field of `𝒪_M` (built as `↥A`) maps bijectively onto the
residue field of `𝒪_N`.

Reusable at every tower level: `M` is an arbitrary intermediate extension carrying no `ValuativeRel`
of its own, only a `ValuationSubring A` lying over `𝒪[K]` — exactly the shape a tower argument would
need one level up, at `M` a concrete intermediate field. -/
theorem residueField_map_bijective_of_isUniformizer_of_valuationSubring
    (A : ValuationSubring M)
    (hA : A.comap (algebraMap K M) = (ValuativeRel.valuation K).valuationSubring)
    (hR : Valuation.RankOne A.valuation)
    (N : Type*) [Field N] [Algebra M N] [FiniteDimensional M N] [Algebra.IsSeparable M N] :
    letI := hR
    letI : Valued M A.ValueGroup := Valued.mk' A.valuation
    letI : NontriviallyNormedField M := Valued.toNontriviallyNormedField M A.ValueGroup
    letI : IsUltrametricDist M := inferInstance
    letI : CompleteSpace M := exists_completeSpace_of_finiteDimensional K A hA
    letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
    letI : (NormedField.valuation (K := M)).Compatible :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := M))
    letI : IsDiscreteValuationRing ↥(ValuativeRel.valuation M).valuationSubring :=
      isDiscreteValuationRing_valuation_valuationSubring_of_finiteDimensional K A hA hR
    ∀ ϖ : ↥(ValuativeRel.valuation M).valuationSubring, Irreducible ϖ →
      ∀ π : N, ‖(ϖ : M)‖ = spectralNorm M N π ^ (minpoly M π).natDegree →
        (minpoly M π).natDegree = Module.finrank M N →
        Function.Bijective (IsLocalRing.ResidueField.map
          (algebraMap ↥(ValuativeRel.valuation M).valuationSubring
            ↥(integralClosure ↥(ValuativeRel.valuation M).valuationSubring N))) := by
  haveI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  haveI : Algebra.IsAlgebraic M N := Algebra.IsAlgebraic.of_finite M N
  letI := hR
  letI : Valued M A.ValueGroup := Valued.mk' A.valuation
  letI : NontriviallyNormedField M := Valued.toNontriviallyNormedField M A.ValueGroup
  haveI : IsUltrametricDist M := inferInstance
  haveI : CompleteSpace M := exists_completeSpace_of_finiteDimensional K A hA
  letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
  haveI : (NormedField.valuation (K := M)).Compatible :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := M))
  haveI : IsDiscreteValuationRing ↥(ValuativeRel.valuation M).valuationSubring :=
    isDiscreteValuationRing_valuation_valuationSubring_of_finiteDimensional K A hA hR
  exact fun _ϖ hϖ _π hram hgen =>
    residueField_map_bijective_of_isUniformizer (K := M) (L := N) hϖ hram hgen

/-- **The generator of a monogenic totally ramified extension is a uniformizer of `𝒪_N`, over an
intermediate extension.** `LocalField.irreducible_of_isUniformizer`
(`Langlands.TotallyRamifiedUniformizer`) applied with its base field taken to be `M / K` as above —
the second input `LubinTateTowerStep.lean`'s Weierstrass-preparation step needs of its moving base,
now available for a moving base `M` built only from a `ValuationSubring` over `𝒪[K]`, one level up
from where a concrete `K → K_1` instantiation would supply it directly. -/
theorem irreducible_of_isUniformizer_of_valuationSubring
    (A : ValuationSubring M)
    (hA : A.comap (algebraMap K M) = (ValuativeRel.valuation K).valuationSubring)
    (hR : Valuation.RankOne A.valuation)
    (N : Type*) [Field N] [Algebra M N] [FiniteDimensional M N] [Algebra.IsSeparable M N] :
    letI := hR
    letI : Valued M A.ValueGroup := Valued.mk' A.valuation
    letI : NontriviallyNormedField M := Valued.toNontriviallyNormedField M A.ValueGroup
    letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
    ∀ ϖ : ↥(ValuativeRel.valuation M).valuationSubring, Irreducible ϖ →
      ∀ (π : N) (hπint : IsIntegral ↥(ValuativeRel.valuation M).valuationSubring π),
        ‖(ϖ : M)‖ = spectralNorm M N π ^ (minpoly M π).natDegree →
        (minpoly M π).natDegree = Module.finrank M N →
        Irreducible (⟨π, hπint⟩ :
          ↥(integralClosure ↥(ValuativeRel.valuation M).valuationSubring N)) := by
  haveI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  haveI : Algebra.IsAlgebraic M N := Algebra.IsAlgebraic.of_finite M N
  letI := hR
  letI : Valued M A.ValueGroup := Valued.mk' A.valuation
  letI : NontriviallyNormedField M := Valued.toNontriviallyNormedField M A.ValueGroup
  haveI : IsUltrametricDist M := inferInstance
  haveI : CompleteSpace M := exists_completeSpace_of_finiteDimensional K A hA
  letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
  haveI : (NormedField.valuation (K := M)).Compatible :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := M))
  haveI : IsDiscreteValuationRing ↥(ValuativeRel.valuation M).valuationSubring :=
    isDiscreteValuationRing_valuation_valuationSubring_of_finiteDimensional K A hA hR
  exact fun _ϖ hϖ _π hπint hram hgen =>
    irreducible_of_isUniformizer (K := M) (L := N) hϖ hram hgen hπint

end LocalField
