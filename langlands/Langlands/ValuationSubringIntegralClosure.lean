/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.AdicCompletionIntegralClosure
import Langlands.NormMap

/-!
# A `ValuationSubring` lying over `𝒪[K]` is the integral closure of `𝒪[K]`

`Langlands.UnramifiedExtension.HenselianLocalRing.exists_isDiscreteValuationRing_integralClosure_residueField_equiv`
produces an intermediate field `M := IntermediateField.adjoin K {x}` together with the ring
`integralClosure R M` for `R` a Henselian discrete valuation ring with fraction field `K`.
`Langlands.TowerBundle` instead builds its totally-ramified-monogenicity bundle on `M` from an
explicit `A : ValuationSubring M` lying over `𝒪[K]`. Composing the two into one tower argument
requires identifying these two rings for the same `M`.

This file proves that identification: for `K` in the `NontriviallyNormedField` /
`IsUltrametricDist` / `ValuativeRel` / `Compatible` / `CompleteSpace` bundle that
`Langlands.NormMap.isIntegral_of_mem_of_comap_eq` and `Langlands.TowerBundle` already use, `M / K`
finite, and `A : ValuationSubring M` with `A.comap (algebraMap K M) = (ValuativeRel.valuation
K).valuationSubring`, the underlying set of `A` equals the underlying set of `integralClosure
↥(ValuativeRel.valuation K).valuationSubring M`. Neither direction needs `R := ↥(ValuativeRel.valuation
K).valuationSubring` to be Henselian, Dedekind, or have finite residue field — those instances are
needed elsewhere to *construct* `M` via the unramified-extension theorem above, but not for this
bridge, which only uses:

* the hard direction, `Langlands.NormMap.isIntegral_of_mem_of_comap_eq` — every `x ∈ A` is integral
  over `R`, using completeness of `K` and finiteness of `M / K`;
* the easy direction, `Valuation.isIntegral_imp_map_le_one` (`Langlands.AdicCompletionIntegralClosure`)
  — every element of `M` integral over `R` has `A`-valuation `≤ 1`, hence lies in `A`, using only
  that `R`'s elements themselves have `A`-valuation `≤ 1` (immediate from `hA`).

## Main results

* `LocalField.isIntegral_iff_mem_valuationSubring` : `x : M` is integral over `R` iff `x ∈ A`.
* `LocalField.coe_valuationSubring_eq_integralClosure` : `(A : Set M) = ↑(integralClosure R M)`.
* `LocalField.isIntegralClosure_valuationSubring` : `↥A` is the integral closure of `R` in `M`,
  i.e. `IsIntegralClosure ↥A R M`.
-/

open ValuativeRel

namespace LocalField

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K] [Field M] [Algebra K M]
  (A : ValuationSubring M)
  (hA : A.comap (algebraMap K M) = (ValuativeRel.valuation K).valuationSubring)

include hA

omit [IsUltrametricDist K] [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K] in
/-- Every element of `↥(ValuativeRel.valuation K).valuationSubring`, viewed in `M` via the algebra
map, lies in `A`. Immediate from `hA`: such an element already lies in `A.comap (algebraMap K M)`. -/
theorem algebraMap_mem_valuationSubring (a : (ValuativeRel.valuation K).valuationSubring) :
    algebraMap (ValuativeRel.valuation K).valuationSubring M a ∈ A := by
  rw [IsScalarTower.algebraMap_apply (ValuativeRel.valuation K).valuationSubring K M,
    ← ValuationSubring.mem_comap, hA]
  exact a.2

variable [FiniteDimensional K M]

/-- **The valuation subring lying over `𝒪[K]` is the integral closure of `𝒪[K]`.** For `M / K`
finite and `A : ValuationSubring M` comapping to `(ValuativeRel.valuation K).valuationSubring`, an
element `x : M` is integral over `↥(ValuativeRel.valuation K).valuationSubring` iff `x ∈ A`.

The forward direction is `Valuation.isIntegral_imp_map_le_one`, using
`algebraMap_mem_valuationSubring` and `ValuationSubring.valuation_le_one_iff` to see that every
element of `↥(ValuativeRel.valuation K).valuationSubring` has `A`-valuation `≤ 1`. The reverse
direction is `Langlands.NormMap.isIntegral_of_mem_of_comap_eq` applied directly with `hA`. -/
theorem isIntegral_iff_mem_valuationSubring {x : M} :
    IsIntegral (ValuativeRel.valuation K).valuationSubring x ↔ x ∈ A := by
  constructor
  · intro hx
    have hle : ∀ a : (ValuativeRel.valuation K).valuationSubring,
        A.valuation (algebraMap _ M a) ≤ 1 :=
      fun a => (A.valuation_le_one_iff _).mpr (algebraMap_mem_valuationSubring A hA a)
    exact (A.valuation_le_one_iff x).mp (Valuation.isIntegral_imp_map_le_one A.valuation hle hx)
  · intro hx
    exact IsDedekindDomain.HeightOneSpectrum.isIntegral_of_mem_of_comap_eq A hA hx

/-- The underlying set of `A` equals the underlying set of the integral closure of `𝒪[K]` in `M`. -/
theorem coe_valuationSubring_eq_integralClosure :
    (A : Set M) = ↑(integralClosure (ValuativeRel.valuation K).valuationSubring M) := by
  ext x
  simp only [SetLike.mem_coe, mem_integralClosure_iff]
  exact (isIntegral_iff_mem_valuationSubring A hA).symm

/-- **`↥A` is the integral closure of `𝒪[K]` in `M`.** Stated as a `theorem` rather than an
`instance`: `hA` is a genuine hypothesis on the particular `A`, not something typeclass search can
discover, so a caller registers this locally (`haveI := isIntegralClosure_valuationSubring A hA`)
after supplying `hA`. -/
theorem isIntegralClosure_valuationSubring :
    IsIntegralClosure A (ValuativeRel.valuation K).valuationSubring M where
  algebraMap_injective := Subtype.coe_injective
  isIntegral_iff {x} := by
    rw [isIntegral_iff_mem_valuationSubring A hA]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

end LocalField
