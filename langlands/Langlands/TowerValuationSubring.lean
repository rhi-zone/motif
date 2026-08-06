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
* `LocalField.algebra` : `Algebra R (integralClosureValuationSubring R M)`, closed by definitional
  transport from `integralClosure R M`'s own `Subalgebra`-algebra structure. This is the instance
  the tower theorem's concrete instantiation was missing — not a diamond between two independently
  built structures, but a registered-instance gap on top of a term that was already definitionally
  the right one.
* `LocalField.isScalarTower` : the transported algebra is compatible with `Algebra R M`, by the
  same transport.
* `LocalField.finite` : `Module.Finite R (integralClosureValuationSubring R M)`, transported from
  `IsIntegralClosure.finite` (needs `R` integrally closed and Noetherian, `M / K` finite separable
  for `K` the fraction field of `R`).

## Implementation notes

`ValuationSubring.ofSubring` keeps the underlying `Subring` definitionally, so
`↥(integralClosureValuationSubring R M)` and `↥(integralClosure R M)` have the same carrier by
`rfl` — which is what lets a monogenicity statement proved for one be read off for the other, and
what lets the `Algebra`/`IsScalarTower`/`Module.Finite` instances above be produced by
`inferInstanceAs` rather than by a coincidence-of-two-constructions transport lemma.
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

/-- **The missing `Algebra` instance, closed by definitional transport, not by a diamond-style
coincidence proof.** `↥(integralClosureValuationSubring R M)` unfolds to
`↥(integralClosure R M).toSubring`, whose carrier is the same predicate as
`↥(integralClosure R M)` (`mem_integralClosureValuationSubring` above is `Iff.rfl`) — so the two
types are definitionally equal and the `Subalgebra`'s own `R`-algebra structure transports across
by `inferInstanceAs`. No independent construction is being reconciled here: it is the same term,
just missing a registered instance for the `ValuationSubring`-coercion spelling of it. -/
noncomputable instance algebra : Algebra R (integralClosureValuationSubring R M) :=
  inferInstanceAs (Algebra R (integralClosure R M))

/-- The transported `Algebra` instance is compatible with the ambient `Algebra R M`, again by
definitional transport from the `Subalgebra` case. -/
instance isScalarTower : IsScalarTower R (integralClosureValuationSubring R M) M :=
  inferInstanceAs (IsScalarTower R (integralClosure R M) M)

end OfIntegralClosure

section Finite

variable {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  {M : Type*} [Field M] [Algebra R M]
  [ValuationRing ↥(integralClosure R M)] [IsFractionRing ↥(integralClosure R M) M]

/-- **Finiteness of the tower object, transported from `IsIntegralClosure.finite`.** For `R`
integrally closed and Noetherian with fraction field `K`, and `M / K` finite separable, the integral
closure of `R` in `M` is a finite `R`-module — hence so is its `ValuationSubring`-coerced
presentation, by the same definitional transport as `algebra` above.

Stated as a `theorem`, not an `instance`, since `K` (the fraction field of `R`) does not appear in
the conclusion and so cannot be found by instance search — the caller supplies it explicitly, as
`IsIntegralClosure.finite` itself requires. -/
theorem finite (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [Algebra K M]
    [IsScalarTower R K M] [FiniteDimensional K M] [Algebra.IsSeparable K M] :
    Module.Finite R (integralClosureValuationSubring R M) :=
  haveI := IsIntegralClosure.finite R K M (integralClosure R M)
  inferInstanceAs (Module.Finite R (integralClosure R M))

end Finite

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
