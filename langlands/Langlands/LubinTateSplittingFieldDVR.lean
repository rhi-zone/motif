/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.ValueGroupCyclic
import Langlands.LubinTateSplittingField
import Langlands.NormMap

/-!
# `O_{K_1}` is a discrete valuation ring

`ROADMAP.md`'s Phase 2c thirty-ninth pass ("scoping and a first closed piece of the `K_n` tower
generalization") identifies the largest remaining gap in generalizing the Lubin-Tate tower step
(`Langlands/LubinTateTowerStep.lean`) to arbitrary `n`: whether `K_1 := Q.SplittingField`
(`Langlands.LubinTate.K_1`, `Langlands/LubinTateSplittingField.lean`), a genuine finite extension of
`K` built entirely in the `spectralNorm`/`NormedField` formalism (not `ValuativeRel`), has a ring of
integers `O_{K_1}` that is itself a discrete valuation ring.

This file closes that question, in general and at the arc's concrete instantiation.

## Main results

* `NormedField.isDiscreteValuationRing_valuationSubring_of_finiteDimensional` : the general,
  formalism-neutral statement — for `K` complete-discretely-valued in the `ValuativeRel` sense and
  `L / K` finite with a norm on `L` extending `K`'s (`hnorm`), the closed-unit-ball valuation subring
  of `L` is a discrete valuation ring. No `spectralNorm`, no `RankOne`, no `IsUltrametricDist`
  anywhere in the statement or proof — it needs only `ValuationSubring.isDiscreteValuationRing_of_comap_eq`
  (`Langlands.ValueGroupCyclic`), applied to the closed unit ball of `L`'s norm, once that ball's
  comap along `algebraMap K L` is identified with `𝒪[K]`.
* `LubinTate.isDiscreteValuationRing_valuationSubring_K_1` : the corollary at `K_1`, using
  `spectralNorm_extends` (`K_1`'s norm restricts to `K`'s norm on `K`'s image, the same fact
  `K_1.hOK_transport`/`K_1.hπnorm_transport` already use) to discharge `hnorm`.
* `IsDedekindDomain.HeightOneSpectrum.isDiscreteValuationRing_valuationSubring_K_1_of_adicCompletion`
  : the same at this arc's concrete instantiation `K := v.adicCompletion F`, where
  `[ValuativeRel K] [(NormedField.valuation).Compatible]
  [IsDiscreteValuationRing (ValuativeRel.valuation K).valuationSubring]` are already Mathlib/repo
  instances (`Langlands.NormMap`), so the corollary carries **no further hypothesis** of that kind.

## Why no `RankOne`/`ValuativeRel` bridge on `L` is needed

`ValuationSubring.isDiscreteValuationRing_of_comap_eq` (`Langlands/ValueGroupCyclic.lean`) proves
`IsDiscreteValuationRing A` for `A : ValuationSubring L` lying over a discrete `𝒪 : ValuationSubring
K` directly, from `[FiniteDimensional K L]` alone — no `ValuativeRel L`, no `RankOne A.valuation`,
no norm on `L` at all. What *is* needed is identifying `A := (NormedField.valuation (K :=
L)).valuationSubring`'s comap with `𝒪[K]`, which is exactly `hnorm` (that `L`'s norm restricts to
`K`'s) unfolded through `NormedField.valuation_apply` and the `ValuativeRel`/`NormedField.valuation`
identification on `K` (`Valuation.isEquiv_iff_valuationSubring` applied to the two `Compatible`
valuations on `K`, the same pattern `Langlands.UnramifiedExtension.henselianLocalRing_of_valuationSubring`
uses). This sidesteps `Langlands/TowerBundle.lean`'s heavier `letI`-bundle route (which additionally
builds a `ValuativeRel L` and needs `RankOne A.valuation`, via `LocalField.exists_rankOne_compatible`)
entirely — that machinery is exactly what `Langlands/LubinTateTowerStep.lean`'s Henselian/completeness
needs next, but plain discreteness does not.
-/

noncomputable section

open ValuativeRel

/-- **The closed-unit-ball valuation subring of a finite extension of a complete
discretely-valued field is a discrete valuation ring**, given the extension's norm restricts to the
base field's norm.

`K` is taken in the `ValuativeRel` bundle (`[ValuativeRel K] [(NormedField.valuation).Compatible]
[IsDiscreteValuationRing (ValuativeRel.valuation K).valuationSubring]`), matching
`Langlands/TowerBundle.lean`'s base-field bundle; `L` needs only a `NontriviallyNormedField`
structure and `hnorm`, the fact that `L`'s norm extends `K`'s along `algebraMap K L` — no
`ValuativeRel L`, `RankOne`, or `IsUltrametricDist` anywhere. -/
theorem NormedField.isDiscreteValuationRing_valuationSubring_of_finiteDimensional
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
    [(NormedField.valuation (K := K)).Compatible]
    [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [Algebra K L]
    [FiniteDimensional K L]
    (hnorm : ∀ x : K, ‖algebraMap K L x‖ = ‖x‖) :
    IsDiscreteValuationRing ↥(NormedField.valuation (K := L)).valuationSubring := by
  set 𝒪 : ValuationSubring K := (ValuativeRel.valuation K).valuationSubring with h𝒪
  haveI h𝒪dvr : IsDiscreteValuationRing 𝒪 := ‹_›
  set A : ValuationSubring L := (NormedField.valuation (K := L)).valuationSubring with hA
  have hsub : 𝒪 = (NormedField.valuation (K := K)).valuationSubring := by
    have hequiv : (ValuativeRel.valuation K).IsEquiv (NormedField.valuation (K := K)) :=
      ValuativeRel.isEquiv _ _
    exact (Valuation.isEquiv_iff_valuationSubring _ _).mp hequiv
  have hcomap : A.comap (algebraMap K L) = 𝒪 := by
    rw [hsub]
    ext x
    have hnn : ‖algebraMap K L x‖₊ = ‖x‖₊ :=
      NNReal.coe_injective (by rw [coe_nnnorm, coe_nnnorm, hnorm])
    rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
      Valuation.mem_valuationSubring_iff, NormedField.valuation_apply,
      NormedField.valuation_apply, hnn]
  rw [hA]
  exact ValuationSubring.isDiscreteValuationRing_of_comap_eq A hcomap

namespace LubinTate

open IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Algebra O K] [IsFractionRing O K]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`O_{K_1} := ↥(NormedField.valuation (K := K_1 P)).valuationSubring` is a discrete valuation
ring**, for any `K` complete-discretely-valued in the `ValuativeRel` sense. Applies
`NormedField.isDiscreteValuationRing_valuationSubring_of_finiteDimensional` with `hnorm` discharged
by `spectralNorm_extends` via `K_1.norm_eq_spectralNorm` — the same route
`K_1.hOK_transport`/`K_1.hπnorm_transport` (`Langlands/LubinTateSplittingField.lean`) already use to
transport `K`'s own norm hypotheses down to `K_1`. -/
theorem isDiscreteValuationRing_valuationSubring_K_1 (P : O[X]) :
    IsDiscreteValuationRing ↥(NormedField.valuation (K := K_1 (K := K) P)).valuationSubring :=
  NormedField.isDiscreteValuationRing_valuationSubring_of_finiteDimensional
    (K := K) (L := K_1 (K := K) P) fun x => by
      rw [K_1.norm_eq_spectralNorm, spectralNorm_extends]

end LubinTate

namespace IsDedekindDomain.HeightOneSpectrum

open LubinTate IsLocalRing Polynomial

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F] (v : HeightOneSpectrum A)

/-- **The same, at this arc's concrete instantiation `K := v.adicCompletion F`.** `K`'s
`ValuativeRel`/`Compatible`/`IsDiscreteValuationRing` bundle is already available as instances
(`Langlands.NormMap`'s `instValuativeRelValuedAdicCompletion`,
`instance : (NormedField.valuation (K := v.adicCompletion F)).Compatible`, and
`instIsDiscreteValuationRingValuationSubringAdicCompletion`), so this corollary carries no
hypothesis beyond `K_1`'s own standing package
(`[IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [Algebra O (v.adicCompletion
F)] [IsFractionRing O (v.adicCompletion F)]`). -/
theorem isDiscreteValuationRing_valuationSubring_K_1_of_adicCompletion
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [Algebra O (v.adicCompletion F)] [IsFractionRing O (v.adicCompletion F)] (P : O[X]) :
    IsDiscreteValuationRing
      ↥(NormedField.valuation (K := K_1 (K := v.adicCompletion F) P)).valuationSubring :=
  isDiscreteValuationRing_valuationSubring_K_1 P

end IsDedekindDomain.HeightOneSpectrum
