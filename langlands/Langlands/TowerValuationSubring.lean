/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.ValuationSubringIntegralClosure

/-!
# The integral closure of `𝒪[K]` in a finite extension, as a `ValuationSubring`

`Langlands.ValuationSubringIntegralClosure` goes from a `ValuationSubring M` lying over `𝒪[K]` to
the integral closure: given `A`, it shows `↥A` *is* `integralClosure 𝒪[K] M`. Serre's tower
argument needs the other direction. The unramified half
(`Langlands.UnramifiedExtension.HenselianLocalRing.exists_isDiscreteValuationRing_integralClosure_residueField_equiv`)
hands back `M := IntermediateField.adjoin K {x}` together with the fact that `integralClosure R ↥M`
is a *discrete valuation ring*; the totally ramified half
(`Langlands.TowerBundle.LocalField.adjoin_eq_integralClosure_of_isUniformizer_of_valuationSubring`)
wants an explicit `A : ValuationSubring M` with `A.comap (algebraMap K M) = 𝒪[K]`.

This file manufactures that `A` from the integral closure, using only that the integral closure is
a valuation ring with fraction field `M`.

## Main results

* `LocalField.integralClosureValuationSubring` : the integral closure of `R` in `M`, packaged as a
  `ValuationSubring M`, whenever it is a valuation ring with fraction field `M`.
* `LocalField.comap_integralClosureValuationSubring` : for `R := 𝒪[K]` and `M / K` finite, that
  valuation subring lies over `𝒪[K]`.
* `LocalField.integralClosureValuationSubring_eq` : conversely, *every* `A : ValuationSubring M`
  lying over `𝒪[K]` equals it — so the tower object is unique, and the two halves' presentations of
  `𝒪_M` are literally the same term.

## Implementation notes

`ValuationSubring.ofSubring` keeps the underlying `Subring` definitionally, so
`↥(integralClosureValuationSubring R M)` and `↥(integralClosure R M)` have the same carrier by
`rfl` — which is what lets a monogenicity statement proved for one be read off for the other.
-/

open ValuativeRel

namespace LocalField

section OfIntegralClosure

variable (R : Type*) [CommRing R] [IsDomain R] (M : Type*) [Field M] [Algebra R M]
  [ValuationRing ↥(integralClosure R M)] [IsFractionRing ↥(integralClosure R M) M]

/-- **The integral closure of `R` in `M` as a valuation subring**, for `R` whose integral closure in
`M` happens to be a valuation ring with fraction field `M` (e.g. a discrete valuation ring, as
produced by the unramified half of Serre's tower argument).

`ValuationRing.isInteger_or_isInteger` supplies exactly `ValuationSubring.ofSubring`'s hypothesis:
each `x : M` or its inverse is in the range of `algebraMap ↥(integralClosure R M) M`, which is the
inclusion of the carrier. -/
def integralClosureValuationSubring : ValuationSubring M :=
  ValuationSubring.ofSubring (integralClosure R M).toSubring fun x => by
    rcases ValuationRing.isInteger_or_isInteger (K := M) ↥(integralClosure R M) x with
      ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl (by rw [← ha]; exact a.2)
    · exact Or.inr (by rw [← ha]; exact a.2)

omit [IsDomain R] in
@[simp]
theorem mem_integralClosureValuationSubring {x : M} :
    x ∈ integralClosureValuationSubring R M ↔ IsIntegral R x := Iff.rfl

omit [IsDomain R] in
@[simp]
theorem coe_integralClosureValuationSubring :
    ((integralClosureValuationSubring R M : ValuationSubring M) : Set M) =
      ↑(integralClosure R M) := rfl

end OfIntegralClosure

section Tower

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  (M : Type*) [Field M] [Algebra K M] [FiniteDimensional K M]
  [ValuationRing ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring M)]
  [IsFractionRing ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring M) M]

omit [IsUltrametricDist K] [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K] in
/-- **The tower object lies over `𝒪[K]`.** The integral closure of `𝒪[K]` in `M`, viewed as a
`ValuationSubring M`, comaps along `algebraMap K M` to `𝒪[K]` itself.

Both directions are formal: an element of `K` integral over `𝒪[K]` is integral already as an
element of `K` (`IsIntegral.tower_bot`, the algebra map `K → M` being injective) hence lies in
`𝒪[K]` (`IsIntegrallyClosed.isIntegral_iff`); conversely an element of `𝒪[K]` is integral over
`𝒪[K]`. Neither completeness of `K` nor finiteness of `M / K` is used. -/
theorem comap_integralClosureValuationSubring :
    (integralClosureValuationSubring ↥(ValuativeRel.valuation K).valuationSubring M).comap
        (algebraMap K M) =
      (ValuativeRel.valuation K).valuationSubring := by
  have hinj : Function.Injective (algebraMap K M) := FaithfulSMul.algebraMap_injective K M
  refine ValuationSubring.ext _ _ fun y => ?_
  rw [ValuationSubring.mem_comap, mem_integralClosureValuationSubring]
  constructor
  · intro hy
    obtain ⟨z, hz⟩ :=
      (IsIntegrallyClosed.isIntegral_iff
        (R := ↥(ValuativeRel.valuation K).valuationSubring) (K := K)).mp
        (IsIntegral.tower_bot (A := K) (B := M) hinj hy)
    exact hz ▸ z.2
  · intro hy
    have : algebraMap K M y =
        algebraMap ↥(ValuativeRel.valuation K).valuationSubring M ⟨y, hy⟩ := by
      rw [IsScalarTower.algebraMap_apply ↥(ValuativeRel.valuation K).valuationSubring K M]
      rfl
    rw [this]
    exact isIntegral_algebraMap

/-- **Uniqueness of the tower object.** Any `A : ValuationSubring M` lying over `𝒪[K]` equals the
integral closure valuation subring. Immediate from
`Langlands.ValuationSubringIntegralClosure.LocalField.isIntegral_iff_mem_valuationSubring`, which
identifies membership in `A` with integrality over `𝒪[K]`. -/
theorem integralClosureValuationSubring_eq (A : ValuationSubring M)
    (hA : A.comap (algebraMap K M) = (ValuativeRel.valuation K).valuationSubring) :
    A = integralClosureValuationSubring ↥(ValuativeRel.valuation K).valuationSubring M :=
  ValuationSubring.ext _ _ fun x =>
    ((isIntegral_iff_mem_valuationSubring A hA (x := x)).symm.trans
      (mem_integralClosureValuationSubring _ _).symm)

end Tower

end LocalField
