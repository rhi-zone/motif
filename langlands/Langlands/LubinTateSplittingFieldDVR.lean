/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.ValueGroupCyclic
import Langlands.LubinTateSplittingField
import Langlands.NormMap
import Langlands.MonogenicIntegralClosure
import Langlands.TowerValuationSubring
import Langlands.TowerBundle
import Langlands.LubinTateRootCountConcrete

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
open scoped WithZero

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

/-- **`↥(NormedField.valuation (K := L)).valuationSubring` is Henselian**, for `L / K` finite
separable, `K` complete-discretely-valued in the `ValuativeRel` sense with finite residue field, and
`L`'s norm extending `K`'s.

Identifies `A := (NormedField.valuation (K := L)).valuationSubring` with `𝒪_L :=
LocalField.integralClosureValuationSubring 𝒪[K] L` via uniqueness of the valuation subring
extension (`LocalField.valuationSubring_eq_of_comap_eq`, `Langlands/HenselianValuation.lean`) — both
comap to `𝒪[K]`, `A` by the same computation as
`NormedField.isDiscreteValuationRing_valuationSubring_of_finiteDimensional`, `𝒪_L` by
`LocalField.comap_integralClosureValuationSubring` (`Langlands/TowerValuationSubring.lean`). This
transports `𝒪_L`'s module-finiteness over `𝒪[K]` (`LocalField.finite`, needing separability) across
to `A`, giving `Finite (ResidueField A)` via `IsLocalRing.ResidueField.finite_of_finite`; a `RankOne
A.valuation` instance comes from `LocalField.exists_rankOne_compatible`
(`Langlands/HenselianValuation.lean`); `Langlands/TowerBundle.lean`'s
`henselianLocalRing_of_comap_eq` assembles these into `HenselianLocalRing ↥A`. -/
theorem NormedField.henselianLocalRing_valuationSubring_of_finiteDimensional
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
    [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
    [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
    [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hnorm : ∀ x : K, ‖algebraMap K L x‖ = ‖x‖) :
    HenselianLocalRing ↥(NormedField.valuation (K := L)).valuationSubring := by
  set 𝒪 : ValuationSubring K := (ValuativeRel.valuation K).valuationSubring with h𝒪
  set A : ValuationSubring L := (NormedField.valuation (K := L)).valuationSubring with hAdef
  have hcomapA : A.comap (algebraMap K L) = 𝒪 := by
    have hsub : 𝒪 = (NormedField.valuation (K := K)).valuationSubring := by
      have hequiv : (ValuativeRel.valuation K).IsEquiv (NormedField.valuation (K := K)) :=
        ValuativeRel.isEquiv _ _
      exact (Valuation.isEquiv_iff_valuationSubring _ _).mp hequiv
    rw [hAdef, hsub]
    ext x
    have hnn : ‖algebraMap K L x‖₊ = ‖x‖₊ :=
      NNReal.coe_injective (by rw [coe_nnnorm, coe_nnnorm, hnorm])
    rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
      Valuation.mem_valuationSubring_iff, NormedField.valuation_apply,
      NormedField.valuation_apply, hnn]
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hcomapI : (LocalField.integralClosureValuationSubring ↥𝒪 L).comap (algebraMap K L) = 𝒪 :=
    LocalField.comap_integralClosureValuationSubring K L
  have hAeq : A = LocalField.integralClosureValuationSubring ↥𝒪 L :=
    LocalField.valuationSubring_eq_of_comap_eq K hcomapA hcomapI
  haveI hmodfin : Module.Finite ↥𝒪 ↥(LocalField.integralClosureValuationSubring ↥𝒪 L) :=
    LocalField.finite (R := ↥𝒪) (M := L) K
  haveI hlocalhom :
      IsLocalHom (algebraMap ↥𝒪 ↥(LocalField.integralClosureValuationSubring ↥𝒪 L)) :=
    inferInstanceAs (IsLocalHom (algebraMap ↥𝒪 ↥(integralClosure ↥𝒪 L)))
  haveI hfinA : Finite (IsLocalRing.ResidueField ↥A) := by
    rw [hAeq]
    exact IsLocalRing.ResidueField.finite_of_finite (R := ↥𝒪) ‹_›
  obtain ⟨hR, -⟩ := LocalField.exists_rankOne_compatible K A hcomapA
  exact LocalField.henselianLocalRing_of_comap_eq K A hcomapA hR hfinA

/-- **`↥(NormedField.valuation (K := L)).valuationSubring` is `(maximalIdeal)`-adically
complete**, under exactly the hypotheses of
`NormedField.henselianLocalRing_valuationSubring_of_finiteDimensional` (`L / K` finite separable,
`K` complete-discretely-valued with finite residue field, `L`'s norm extending `K`'s). Same proof
shape: identify `A := (NormedField.valuation (K := L)).valuationSubring` with `𝒪_L` via
`LocalField.valuationSubring_eq_of_comap_eq`, transport finiteness of the residue field, obtain the
`RankOne A.valuation` instance, and apply `LocalField.isAdicComplete_of_comap_eq`
(`Langlands/TowerBundle.lean`) in place of `henselianLocalRing_of_comap_eq`. This is the instance
`PowerSeries.exists_isWeierstrassFactorization` needs by name; `HenselianLocalRing` alone (already
available from the theorem above) is not a substitute. -/
theorem NormedField.isAdicComplete_valuationSubring_of_finiteDimensional
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
    [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
    [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
    [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hnorm : ∀ x : K, ‖algebraMap K L x‖ = ‖x‖) :
    IsAdicComplete
      (IsLocalRing.maximalIdeal ↥(NormedField.valuation (K := L)).valuationSubring)
      ↥(NormedField.valuation (K := L)).valuationSubring := by
  set 𝒪 : ValuationSubring K := (ValuativeRel.valuation K).valuationSubring with h𝒪
  set A : ValuationSubring L := (NormedField.valuation (K := L)).valuationSubring with hAdef
  have hcomapA : A.comap (algebraMap K L) = 𝒪 := by
    have hsub : 𝒪 = (NormedField.valuation (K := K)).valuationSubring := by
      have hequiv : (ValuativeRel.valuation K).IsEquiv (NormedField.valuation (K := K)) :=
        ValuativeRel.isEquiv _ _
      exact (Valuation.isEquiv_iff_valuationSubring _ _).mp hequiv
    rw [hAdef, hsub]
    ext x
    have hnn : ‖algebraMap K L x‖₊ = ‖x‖₊ :=
      NNReal.coe_injective (by rw [coe_nnnorm, coe_nnnorm, hnorm])
    rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
      Valuation.mem_valuationSubring_iff, NormedField.valuation_apply,
      NormedField.valuation_apply, hnn]
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hcomapI : (LocalField.integralClosureValuationSubring ↥𝒪 L).comap (algebraMap K L) = 𝒪 :=
    LocalField.comap_integralClosureValuationSubring K L
  have hAeq : A = LocalField.integralClosureValuationSubring ↥𝒪 L :=
    LocalField.valuationSubring_eq_of_comap_eq K hcomapA hcomapI
  haveI hmodfin : Module.Finite ↥𝒪 ↥(LocalField.integralClosureValuationSubring ↥𝒪 L) :=
    LocalField.finite (R := ↥𝒪) (M := L) K
  haveI hlocalhom :
      IsLocalHom (algebraMap ↥𝒪 ↥(LocalField.integralClosureValuationSubring ↥𝒪 L)) :=
    inferInstanceAs (IsLocalHom (algebraMap ↥𝒪 ↥(integralClosure ↥𝒪 L)))
  haveI hfinA : Finite (IsLocalRing.ResidueField ↥A) := by
    rw [hAeq]
    exact IsLocalRing.ResidueField.finite_of_finite (R := ↥𝒪) ‹_›
  obtain ⟨hR, -⟩ := LocalField.exists_rankOne_compatible K A hcomapA
  exact LocalField.isAdicComplete_of_comap_eq K A hcomapA hR hfinA

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

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`O_{K_1}` is Henselian**, given `K_1 P / K` is separable (e.g. from `isGalois_K_1`,
`Langlands/LubinTateSplittingFieldDegree.lean`, at the arc's usual hypothesis package) and `𝒪[K]`
has finite residue field. Applies
`NormedField.henselianLocalRing_valuationSubring_of_finiteDimensional` the same way
`isDiscreteValuationRing_valuationSubring_K_1` applies its discreteness counterpart. -/
theorem henselianLocalRing_valuationSubring_K_1
    [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
    (P : O[X]) [Algebra.IsSeparable K (K_1 (K := K) P)] :
    HenselianLocalRing ↥(NormedField.valuation (K := K_1 (K := K) P)).valuationSubring :=
  NormedField.henselianLocalRing_valuationSubring_of_finiteDimensional
    (K := K) (L := K_1 (K := K) P) fun x => by
      rw [K_1.norm_eq_spectralNorm, spectralNorm_extends]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`O_{K_1}` is `(maximalIdeal)`-adically complete**, under the same hypotheses as
`henselianLocalRing_valuationSubring_K_1`. Applies
`NormedField.isAdicComplete_valuationSubring_of_finiteDimensional` the same way
`henselianLocalRing_valuationSubring_K_1` applies its Henselian counterpart. This is the instance
`PowerSeries.exists_isWeierstrassFactorization` needs by name to run over `O_{K_1}`, unblocking
`LubinTateTowerStep.lean`'s Weierstrass-preparation step at the `K_1 → K_2` tower step. -/
theorem isAdicComplete_valuationSubring_K_1
    [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
    (P : O[X]) [Algebra.IsSeparable K (K_1 (K := K) P)] :
    IsAdicComplete
      (IsLocalRing.maximalIdeal ↥(NormedField.valuation (K := K_1 (K := K) P)).valuationSubring)
      ↥(NormedField.valuation (K := K_1 (K := K) P)).valuationSubring :=
  NormedField.isAdicComplete_valuationSubring_of_finiteDimensional
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

/-- **`(ValuativeRel.valuation (v.adicCompletion F)).valuationSubring = v.adicCompletionIntegers
F`**, as `ValuationSubring`s. Both are `Valued.v.valuationSubring` for the same ambient `Valued`
structure: `v.adicCompletionIntegers F` by Mathlib's own definition
(`IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers`), and
`(ValuativeRel.valuation (v.adicCompletion F)).valuationSubring` by the same `Compatible`-chasing
computation `Langlands.NormMap`'s `instIsDiscreteValuationRingValuationSubringAdicCompletion` uses
internally, exposed here as its own lemma so `Finite (ResidueField (v.adicCompletionIntegers F))`
transports to `𝒪[v.adicCompletion F]` without re-deriving that computation. -/
theorem valuationSubring_valuation_eq_adicCompletionIntegers :
    (ValuativeRel.valuation (v.adicCompletion F)).valuationSubring
      = v.adicCompletionIntegers F := by
  refine ValuationSubring.ext _ _ fun x => ?_
  rw [Valuation.mem_valuationSubring_iff, mem_adicCompletionIntegers]
  have h1 : (ValuativeRel.valuation (v.adicCompletion F)) x ≤ 1 ↔
      x ≤ᵥ (1 : v.adicCompletion F) := by
    rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (v.adicCompletion F)),
      map_one]
  have h2 : x ≤ᵥ (1 : v.adicCompletion F) ↔ Valued.v x ≤ 1 := by
    rw [Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)),
      map_one]
  rw [h1, h2]

/-- **The base `O := v.adicCompletionIntegers F` is `(maximalIdeal)`-adically complete.** This
closes the gap `Langlands/LubinTateSplittingFieldDegreeConcrete.lean`'s module docstring records as
missing: applies `isAdicComplete_of_valuationSubring` (`Langlands.UnramifiedExtension`) at `K :=
v.adicCompletion F` — whose `NontriviallyNormedField`/`IsUltrametricDist`/`ValuativeRel`/
`Compatible`/`CompleteSpace`/`IsDiscreteValuationRing` bundle is already available as instances
(`Langlands.NormMap`, `Mathlib.RingTheory.DedekindDomain.AdicValuation`'s `CompleteSpace
(adicCompletion K v)` instance) — then transports along
`valuationSubring_valuation_eq_adicCompletionIntegers`. Residue-field finiteness comes from
`instFiniteResidueFieldAdicCompletionIntegers` (`Langlands/LubinTateRootCountConcrete.lean`),
itself from `[Finite (A ⧸ v.asIdeal)]`. -/
instance isAdicComplete_adicCompletionIntegers [Finite (A ⧸ v.asIdeal)] :
    IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) := by
  haveI : Finite (IsLocalRing.ResidueField
      ↥(ValuativeRel.valuation (v.adicCompletion F)).valuationSubring) := by
    rw [valuationSubring_valuation_eq_adicCompletionIntegers]
    infer_instance
  have h := isAdicComplete_of_valuationSubring (v.adicCompletion F)
  rwa [valuationSubring_valuation_eq_adicCompletionIntegers] at h

/-- **`O_{K_1}` is `(maximalIdeal)`-adically complete, at this arc's concrete instantiation**, given
`K_1 P / v.adicCompletion F` is separable and `𝒪[v.adicCompletion F]` has finite residue field —
the same hypotheses as `henselianLocalRing_valuationSubring_K_1_of_adicCompletion`. -/
theorem isAdicComplete_valuationSubring_K_1_of_adicCompletion
    [Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F))]
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [Algebra O (v.adicCompletion F)] [IsFractionRing O (v.adicCompletion F)] (P : O[X])
    [Algebra.IsSeparable (v.adicCompletion F) (K_1 (K := v.adicCompletion F) P)] :
    IsAdicComplete
      (IsLocalRing.maximalIdeal
        ↥(NormedField.valuation (K := K_1 (K := v.adicCompletion F) P)).valuationSubring)
      ↥(NormedField.valuation (K := K_1 (K := v.adicCompletion F) P)).valuationSubring := by
  haveI : Finite (IsLocalRing.ResidueField
      ↥(ValuativeRel.valuation (v.adicCompletion F)).valuationSubring) := by
    rw [valuationSubring_valuation_eq_adicCompletionIntegers]
    infer_instance
  exact isAdicComplete_valuationSubring_K_1 P

/-- **`O_{K_1}` is Henselian, at this arc's concrete instantiation**, given `K_1 P / v.adicCompletion
F` is separable and `𝒪[v.adicCompletion F]` (equivalently, `v.adicCompletionIntegers F`, by
`valuationSubring_valuation_eq_adicCompletionIntegers`) has finite residue field — a genuine
hypothesis here (residue-field finiteness of `v` is not automatic for a general Dedekind domain,
e.g. it fails for function fields with infinite constant field), independent of `O`'s own residue
field. -/
theorem henselianLocalRing_valuationSubring_K_1_of_adicCompletion
    [Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F))]
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [Algebra O (v.adicCompletion F)] [IsFractionRing O (v.adicCompletion F)] (P : O[X])
    [Algebra.IsSeparable (v.adicCompletion F) (K_1 (K := v.adicCompletion F) P)] :
    HenselianLocalRing
      ↥(NormedField.valuation (K := K_1 (K := v.adicCompletion F) P)).valuationSubring := by
  haveI : Finite (IsLocalRing.ResidueField
      ↥(ValuativeRel.valuation (v.adicCompletion F)).valuationSubring) := by
    rw [valuationSubring_valuation_eq_adicCompletionIntegers]
    infer_instance
  exact henselianLocalRing_valuationSubring_K_1 P

end IsDedekindDomain.HeightOneSpectrum
