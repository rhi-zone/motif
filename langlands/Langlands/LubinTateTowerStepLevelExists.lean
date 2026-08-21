/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLevelConnect
import Langlands.EisensteinUniformizerAbstract
import Langlands.IntegralClosureTower
import Langlands.LubinTateTowerStepConcreteK2Flat
import Langlands.LubinTateTowerStepK3Degree

/-!
# The existence half of the inductive tower step, generic in `Level` (`ROADMAP.md` §83)

`§82` closed the connecting identity generically over `Level` and named the precise remaining
obstacle for the `∀ n` chain: *"generalize `exists_eisenstein_tower_step_K_2` to produce a
`TowerStep` over `lvl.next Pn` from a `TowerStep` over `lvl`"*, plus a generic `hOK_transport`
needed before transitivity generalizes. This file does both.

## What the general engine already gave, and what the concrete files added on top

`Langlands/LubinTateTowerStep.lean`'s `exists_isWeierstrassFactorization_shifted` is **already** the
general `n`-step engine: it takes an arbitrary complete DVR `O'`, an arbitrary local
`ψ : O →+* O'`, and an arbitrary irreducible `α' : O'`, and produces the next Eisenstein polynomial.
Read against it, `exists_eisenstein_tower_step_K_2` (`Langlands/LubinTateTowerStepConcreteK2.lean`)
adds exactly four `K_2`-specific things, and nothing else:

1. the *uniformizer* `α'` at the next level (`irreducible_of_isEisensteinAt_K_2`);
2. the `IsAdicComplete` instance for the next level's ring of integers;
3. the `IsLocalHom` instance for the next level's structure map;
4. (in `§77`'s `exists_eisenstein_tower_step_K_2_flat'`) a nested → flat spelling transport of the
   engine's whole output along `integralClosureRingEquiv`.

This file supplies (1)–(3) generically. **(4) turns out not to be needed at all generically**: the
engine can be run *directly* at the flat `(lvl.next Pn).OL`, since all three of its side conditions
are available there; only the *uniformizer's* irreducibility is inherently relative to `lvl.OL`, and
that single `Prop` transports along `integralClosureRingEquiv` by `Irreducible.map` alone — no
`Polynomial.map`/`PowerSeries.map` transport of the output, and hence no `hcompeq`-style
structure-map identification, is required.

## A correction to `§82`'s ledger, checked by build

`§82` recorded `[IsDomain lvl.OL]`/`[IsDiscreteValuationRing lvl.OL]` as *"not derivable generically
(no lemma in this repo constructs them)"*. That is **wrong**, and this file corrects it:
`LocalField.isDiscreteValuationRing_integralClosure` (`Langlands/MonogenicIntegralClosure.lean`)
constructs exactly this for `↥(integralClosure ↥𝒪[K] L)` given `[FiniteDimensional K L]`, and
`Level` stores that as its `finiteDim` field. `Level.isDiscreteValuationRing_OL`/`Level.isDomain_OL`
below close by `infer_instance` after `letI := lvl.algL; letI := lvl.finiteDim`. What is true, and
what `§82`'s observation was really about, is that these are not found by *instance search* at a
concrete tower level, because `finiteDim` is deliberately not a global instance — which is why the
concrete `K_3`-level files carry `[IsDiscreteValuationRing (O_K2 P₂)]` as an ambient hypothesis.
Nothing here removes those ambient hypotheses from the existing concrete files.

## Main results

* `Level.isDiscreteValuationRing_OL`, `Level.isDomain_OL`, `Level.algebraIsSeparable`,
  `Level.isAdicComplete_OL`, `Level.isLocalHom_towerHom` : the side facts about a level's own ring
  of integers, all derived from `Level`'s stored fields.
* `Level.algebraMap_OL_towerHom`, `Level.algebraMap_O_eq_comp_L`, `Level.algebraMap_O_eq_comp_OL` :
  the generic forms of `algebraMap_O_K_1_eq_comp_towerHom`/`K_2.algebraMap_O_eq_comp_K_1`/
  `K_3.algebraMap_O_eq_comp_O_K2`.
* **`Level.hOK_transport`** : `§82`'s named prerequisite — `hOK` one level up, generically.
* `Level.hπnorm_transport` : likewise for the strict uniformizer bound.
* `Level.irreducible_root_next` : the next level's generator is a uniformizer of
  `(lvl.next Pn).OL`, the generic `irreducible_of_isEisensteinAt_K_2`.
* **`Level.exists_tower_step_next`** : the generic existence step — every field a `TowerStep` over
  `lvl.next Pn` needs, produced from level-`n` data.
* **`TowerStep.exists_next`** : the same, packaged as an actual `TowerStep f hOK` whose `lvl` is
  `ts.lvl.next ts.nextPoly` (by `rfl`).
* `Level.exists_piTorsion_translate_of_root` : transitivity of the `piTorsion` translation action,
  generically — the first consumer of `Level.hOK_transport`.
* `Level.adjoin_eq_integralClosure_next` : monogenicity of the next level's ring of integers over
  `lvl.OL`, the generic `adjoin_eq_integralClosure_K_2`/`adjoin_eq_integralClosure_K_3`.

## Concrete checks, in this arc's established `rfl`-against-the-real-theorem discipline

* **Depth `K_1 → K_2`**: `exists_eisenstein_tower_step_K_2_flat'_of_Level` states `§77`'s
  `exists_eisenstein_tower_step_K_2_flat'` verbatim and proves it from
  `Level.exists_tower_step_next` at `level_K_1`; an `example` checks the fully-applied terms are
  `rfl`-equal. Likewise `exists_piTorsion_translate_of_aeval_P₂_eq_zero_of_Level` and
  `adjoin_eq_integralClosure_K_2_of_Level` against their real concrete counterparts.
* **Depth `K_2 → K_3`**: there is no pre-existing `exists_eisenstein_tower_step_K_3` in this repo to
  compare against — so the check available at this depth is instantiation, not recovery:
  `exists_eisenstein_tower_step_K_3` below runs the *same* generic theorem at `level_K_2`, in the
  real `K_3`-level hypothesis package (`finrank_K_3_eq_residueCard` supplying `hgen`), **producing
  `K_4`'s Eisenstein polynomial** — the first time this arc reaches that depth. Two `example`s check
  by `rfl` that the level it lands on is the real one: `((level_K_2 P₂).next P₃).L` is literally
  `K_3 P₃`, and `(level_K_2 P₂).next P₃` is literally `((level_K_1).next P₂).next P₃`.

## What this does not close

**Not generalized**: the degree/splitting/residue-field chain (`§75`–`§77`'s
`finrank_K_n_eq_residueCard`, `adjoin_root_eq_top_K_n`, `piTorsion_one_K_n_eq_algebraMap_image`,
`splits_divX_map_*`, `residueFieldEquiv_K_n`). `Level.exists_tower_step_next` therefore takes
`hgen : (minpoly lvl.L β).natDegree = Module.finrank lvl.L (K_2 (K' := lvl.L) Pn)` — "the chosen root
generates the next field" — as an explicit hypothesis, exactly as the concrete theorems take `hβfin`/
`hγfin`. Generalizing that chain needs two things `Level`/`TowerStep` do not currently carry: an
`Algebra O lvl.L` composite (the generic `K_2.instAlgebraO` one level *down*, needed to even state
`(P.divX.map (algebraMap O lvl.L)).Splits`), and the `Splits`-over-`lvl.L` fact itself as an
induction invariant — at `K_1` it is free from `K_1`'s construction, and at each later level it is
obtained by `Polynomial.Splits.map`, so it is genuinely level-indexed data rather than a corollary.
That is a separate, larger piece of work and is **not attempted** here.
-/

noncomputable section

open scoped Polynomial IntermediateField

namespace LubinTate

open IsLocalRing PowerSeries Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]

/-- **`lvl.OL` is a discrete valuation ring**, derived from `Level`'s own stored fields —
`LocalField.isDiscreteValuationRing_integralClosure` applied at `L := lvl.L`, whose
`[FiniteDimensional K L]` hypothesis is exactly `lvl.finiteDim`. See this file's module docstring
for why `§82` recorded this as underivable, and in what (weaker) sense that observation was right. -/
theorem Level.isDiscreteValuationRing_OL (lvl : Level K) : IsDiscreteValuationRing lvl.OL := by
  letI := lvl.algL
  letI := lvl.finiteDim
  infer_instance

/-- **`lvl.OL` is a domain**, likewise derived from `Level`'s own fields. -/
theorem Level.isDomain_OL (lvl : Level K) : IsDomain lvl.OL := by
  letI := lvl.algL
  letI := lvl.finiteDim
  infer_instance

/-- **`lvl.L / K` is separable** in characteristic zero: it is finite (`lvl.finiteDim`), hence
integral, and every integral extension of a `CharZero` field is separable — the same shortcut
`algebraIsSeparable_K_K_2` (`Langlands/LubinTateTowerStepAdicCompleteK2.lean`) uses at the concrete
`K_1 → K_2` level. -/
theorem Level.algebraIsSeparable (lvl : Level K) [CharZero K] :
    letI := lvl.algL
    Algebra.IsSeparable K lvl.L := by
  letI := lvl.algL
  letI := lvl.finiteDim
  haveI : Algebra.IsIntegral K lvl.L := Algebra.IsIntegral.of_finite _ _
  exact Algebra.IsSeparable.of_integral K lvl.L

/-- **`lvl.OL` is `(maximalIdeal)`-adically complete**, generically — the generic form of the
`hAdicbase` step in `exists_eisenstein_tower_step_K_2`'s own proof, which instantiates
`NormedField.isAdicComplete_integralClosure_of_finiteDimensional` at the concrete `K_2 P₂`. -/
theorem Level.isAdicComplete_OL (lvl : Level K) [CharZero K]
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖) :
    letI := lvl.isDiscreteValuationRing_OL
    IsAdicComplete (maximalIdeal lvl.OL) lvl.OL := by
  letI := lvl.algL
  letI := lvl.finiteDim
  haveI := lvl.algebraIsSeparable
  exact NormedField.isAdicComplete_integralClosure_of_finiteDimensional (K := K) (L := lvl.L) hnormL

/-- **The generic structure map `O →+* lvl.OL` is local** — the generic `isLocalHom_towerHom`/
`isLocalHom_comp_towerHom_K_2`, composing `isLocalHom_toValuationSubring` with
`LocalField.isLocalHom_algebraMap_integralClosure` (an instance, general in `L`). -/
theorem Level.isLocalHom_towerHom (lvl : Level K) (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) :
    IsLocalHom (lvl.towerHom hOK) := by
  letI := lvl.algL
  letI := lvl.finiteDim
  haveI := isLocalHom_toValuationSubring (K := K) hOK hπ hπnorm
  exact RingHom.isLocalHom_comp _ _

/-- The generic `𝒪[K] → lvl.OL → lvl.L` composite, run out of `O`, is the ordinary `K`-route map. -/
theorem Level.algebraMap_OL_towerHom (lvl : Level K) (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (c : O) :
    letI := lvl.algL
    algebraMap lvl.OL lvl.L (lvl.towerHom hOK c) = algebraMap K lvl.L (algebraMap O K c) := by
  letI := lvl.algL
  have htower : lvl.towerHom hOK c =
      algebraMap ↥(ValuativeRel.valuation K).valuationSubring lvl.OL
        (toValuationSubring (K := K) hOK c) := rfl
  rw [htower, ← IsScalarTower.algebraMap_apply
      ↥(ValuativeRel.valuation K).valuationSubring lvl.OL lvl.L,
    IsScalarTower.algebraMap_apply ↥(ValuativeRel.valuation K).valuationSubring K lvl.L]
  rw [show algebraMap ↥(ValuativeRel.valuation K).valuationSubring K
      (toValuationSubring (K := K) hOK c) = algebraMap O K c from
    coe_toValuationSubring (K := K) hOK c]

/-- `algebraMap O (K_2 (K' := lvl.L) Pn)` collapses to the ordinary map through `K` and `lvl.L`. -/
theorem Level.algebraMap_O_eq_comp_L (lvl : Level K) (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := lvl.algL
    letI := lvl.instAlgebraO Pn hOK
    ⇑(algebraMap O (K_2 (K' := lvl.L) Pn)) =
      ⇑(algebraMap lvl.L (K_2 (K' := lvl.L) Pn)) ∘ ⇑(algebraMap K lvl.L) ∘ ⇑(algebraMap O K) := by
  letI := lvl.algL
  letI := lvl.instAlgebraO Pn hOK
  funext c
  show algebraMap lvl.L (K_2 (K' := lvl.L) Pn) (algebraMap lvl.OL lvl.L (lvl.towerHom hOK c)) = _
  rw [lvl.algebraMap_OL_towerHom hOK c]
  rfl

/-- `algebraMap O (K_2 (K' := lvl.L) Pn)` also collapses through `lvl.OL`. -/
theorem Level.algebraMap_O_eq_comp_OL (lvl : Level K) (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := lvl.instAlgebraO Pn hOK
    ⇑(algebraMap O (K_2 (K' := lvl.L) Pn)) =
      ⇑(algebraMap lvl.OL (K_2 (K' := lvl.L) Pn)) ∘ ⇑(lvl.towerHom hOK) := by
  letI := lvl.algL
  letI := lvl.instAlgebraO Pn hOK
  funext c
  show algebraMap lvl.L (K_2 (K' := lvl.L) Pn) (algebraMap lvl.OL lvl.L (lvl.towerHom hOK c)) = _
  exact (IsScalarTower.algebraMap_apply lvl.OL lvl.L (K_2 (K' := lvl.L) Pn) _).symm

/-- **`hOK` transports one level up**, generically. -/
theorem Level.hOK_transport (lvl : Level K) (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖) :
    letI := lvl.instAlgebraO Pn hOK
    ∀ c : O, ‖algebraMap O (K_2 (K' := lvl.L) Pn) c‖ ≤ 1 := by
  letI := lvl.algL
  letI := lvl.instAlgebraO Pn hOK
  intro c
  rw [congrFun (lvl.algebraMap_O_eq_comp_OL Pn hOK) c]
  exact lvl.norm_le_one_of_mem_OL_next Pn hnormL _

/-- **`hπnorm` transports one level up**, generically. -/
theorem Level.hπnorm_transport (lvl : Level K) (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖)
    {π : O} (hπnorm : ‖algebraMap O K π‖ < 1) :
    letI := lvl.instAlgebraO Pn hOK
    ‖algebraMap O (K_2 (K' := lvl.L) Pn) π‖ < 1 := by
  letI := lvl.algL
  letI := lvl.instAlgebraO Pn hOK
  rw [congrFun (lvl.algebraMap_O_eq_comp_L Pn hOK) π]
  show ‖algebraMap lvl.L (K_2 (K' := lvl.L) Pn) (algebraMap K lvl.L (algebraMap O K π))‖ < 1
  rw [K_2.norm_eq_spectralNorm, spectralNorm_extends, hnormL]
  exact hπnorm

section Exists

variable (lvl : Level K) [IsDomain lvl.OL] [IsDiscreteValuationRing lvl.OL]

/-- **The next level's generator is a uniformizer of the next level's ring of integers.** -/
theorem Level.irreducible_root_next [CharZero K] (Pn : lvl.OL[X])
    {α' : lvl.OL} (hα'irr : Irreducible α')
    (hPdist : Pn.IsDistinguishedAt (maximalIdeal lvl.OL))
    (hassoc : Associated (Pn.coeff 0) α')
    (hirr : Irreducible (Pn.map (algebraMap lvl.OL lvl.L)))
    {β : K_2 (K' := lvl.L) Pn}
    (hβroot : Polynomial.aeval β (Pn.map (algebraMap lvl.OL lvl.L)) = 0)
    (hgen : (minpoly lvl.L β).natDegree = Module.finrank lvl.L (K_2 (K' := lvl.L) Pn)) :
    letI := (lvl.next Pn).algL
    ∃ hβint : IsIntegral ↥(ValuativeRel.valuation K).valuationSubring β,
      Irreducible (⟨β, hβint⟩ : (lvl.next Pn).OL) := by
  letI := lvl.algL
  letI := lvl.finiteDim
  letI := (lvl.next Pn).algL
  haveI : CharZero lvl.L := charZero_of_injective_algebraMap (algebraMap K lvl.L).injective
  haveI : Algebra.IsIntegral lvl.L (K_2 (K' := lvl.L) Pn) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable lvl.L (K_2 (K' := lvl.L) Pn) := Algebra.IsSeparable.of_integral _ _
  haveI htower : IsScalarTower ↥(ValuativeRel.valuation K).valuationSubring lvl.L
      (K_2 (K' := lvl.L) Pn) := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI := (lvl.next Pn).isDomain_OL
  haveI := (lvl.next Pn).isDiscreteValuationRing_OL
  haveI : IsDomain ↥(integralClosure lvl.OL (K_2 (K' := lvl.L) Pn)) :=
    isDomain_integralClosure_integralClosure
      (R := ↥(ValuativeRel.valuation K).valuationSubring) (L := lvl.L) (M := K_2 (K' := lvl.L) Pn)
  haveI : IsDiscreteValuationRing ↥(integralClosure lvl.OL (K_2 (K' := lvl.L) Pn)) :=
    isDiscreteValuationRing_integralClosure_integralClosure
      (R := ↥(ValuativeRel.valuation K).valuationSubring) (L := lvl.L) (M := K_2 (K' := lvl.L) Pn)
  -- `β` is integral over `lvl.OL`, witnessed by `Pn` itself.
  have hβint : IsIntegral lvl.OL β := by
    refine ⟨Pn, hPdist.monic, ?_⟩
    have h1 : Polynomial.aeval β (Polynomial.map (algebraMap lvl.OL lvl.L) Pn) = 0 := hβroot
    rwa [Polynomial.aeval_map_algebraMap] at h1
  have hβint' : IsIntegral ↥(ValuativeRel.valuation K).valuationSubring β :=
    (isIntegral_iff_isIntegral_integralClosure
      (R := ↥(ValuativeRel.valuation K).valuationSubring) (L := lvl.L)
      (M := K_2 (K' := lvl.L) Pn)).mpr hβint
  refine ⟨hβint', ?_⟩
  -- `minpoly lvl.OL β = Pn`, on the nose.
  have hminK : minpoly lvl.L β = Pn.map (algebraMap lvl.OL lvl.L) :=
    (minpoly.eq_of_irreducible_of_monic hirr hβroot (hPdist.monic.map _)).symm
  have hminR : minpoly lvl.OL β = Pn := by
    have hfrac : minpoly lvl.L β =
        Polynomial.map (algebraMap lvl.OL lvl.L) (minpoly lvl.OL β) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' lvl.L hβint
    have hinj : Function.Injective (algebraMap lvl.OL lvl.L) :=
      IsFractionRing.injective _ lvl.L
    exact Polynomial.map_injective _ hinj (hfrac ▸ hminK)
  have hEisPn : Pn.IsEisensteinAt (maximalIdeal lvl.OL) :=
    hPdist.monic.isEisensteinAt_of_mem_of_notMem (maximalIdeal.isMaximal lvl.OL).ne_top
      (fun {n} hn => hPdist.toIsWeaklyEisensteinAt.mem hn)
      (not_mem_sq_maximalIdeal_of_associated hα'irr hassoc)
  have hEis : (minpoly lvl.OL β).IsEisensteinAt (maximalIdeal lvl.OL) := by
    rw [hminR]; exact hEisPn
  have hnested : Irreducible
      (⟨β, hβint⟩ : ↥(integralClosure lvl.OL (K_2 (K' := lvl.L) Pn))) :=
    irreducible_of_isEisensteinAt (R := lvl.OL) (K := lvl.L) (L := K_2 (K' := lvl.L) Pn)
      hα'irr hβint hEis hgen
  have hmap := hnested.map
    (integralClosureRingEquiv (R := ↥(ValuativeRel.valuation K).valuationSubring)
      (L := lvl.L) (M := K_2 (K' := lvl.L) Pn)).symm
  exact hmap

/-- **The generic existence step.** -/
theorem Level.exists_tower_step_next [CharZero K] (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1)
    {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {α' : lvl.OL} (hα'irr : Irreducible α')
    (hPdist : Pn.IsDistinguishedAt (maximalIdeal lvl.OL))
    (hassoc : Associated (Pn.coeff 0) α') (hdeg : 0 < Pn.natDegree)
    (hα'norm : ‖algebraMap lvl.OL (K_2 (K' := lvl.L) Pn) α'‖ < 1)
    (hirr : Irreducible (Pn.map (algebraMap lvl.OL lvl.L)))
    {β : K_2 (K' := lvl.L) Pn}
    (hβroot : Polynomial.aeval β (Pn.map (algebraMap lvl.OL lvl.L)) = 0)
    (hgen : (minpoly lvl.L β).natDegree = Module.finrank lvl.L (K_2 (K' := lvl.L) Pn)) :
    letI := (lvl.next Pn).isDiscreteValuationRing_OL
    ∃ (Pnext : (lvl.next Pn).OL[X]) (unext : (lvl.next Pn).OL⟦X⟧) (gen : (lvl.next Pn).OL),
      IsUnit unext ∧ Pnext.IsDistinguishedAt (maximalIdeal (lvl.next Pn).OL) ∧
        Pnext.natDegree = residueCard O ∧ Irreducible gen ∧
        shifted f ((lvl.next Pn).towerHom hOK) gen = (Pnext : _⟦X⟧) * unext ∧
        Associated (Pnext.coeff 0) gen ∧
        ‖algebraMap (lvl.next Pn).OL (K_2 (K' := (lvl.next Pn).L) Pnext) gen‖ < 1 := by
  letI := lvl.algL
  letI := lvl.finiteDim
  letI := (lvl.next Pn).algL
  haveI := (lvl.next Pn).isDomain_OL
  haveI := (lvl.next Pn).isDiscreteValuationRing_OL
  haveI := (lvl.next Pn).isAdicComplete_OL (hnorm_K_of_Level lvl Pn hnormL)
  haveI := (lvl.next Pn).isLocalHom_towerHom hOK hπ hπnorm
  obtain ⟨hβint, hβirr⟩ :=
    lvl.irreducible_root_next Pn hα'irr hPdist hassoc hirr hβroot hgen
  obtain ⟨Pnext, unext, hdist, hunit, heqW, hdegW, hassocW⟩ :=
    exists_isWeierstrassFactorization_shifted (O' := (lvl.next Pn).OL) hf
      ((lvl.next Pn).towerHom hOK) hβirr
  refine ⟨Pnext, unext, ⟨β, hβint⟩, hunit, hdist, hdegW, hβirr, heqW, hassocW, ?_⟩
  have hcoe : algebraMap (lvl.next Pn).OL (K_2 (K' := (lvl.next Pn).L) Pnext)
      (⟨β, hβint⟩ : (lvl.next Pn).OL) =
      algebraMap (lvl.next Pn).L (K_2 (K' := (lvl.next Pn).L) Pnext) β :=
    IsScalarTower.algebraMap_apply _ (lvl.next Pn).L _ _
  rw [hcoe, K_2.norm_eq_spectralNorm, spectralNorm_extends]
  exact lvl.norm_lt_one_of_root Pn hnormL hα'irr hPdist hassoc hdeg hα'norm hβroot

/-- **Transitivity of the `piTorsion` translation action on roots**, generically. -/
theorem Level.exists_piTorsion_translate_of_root (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖)
    {π : O} (hπ : Irreducible π) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {α' : lvl.OL} {v : lvl.OL⟦X⟧} (hv : IsUnit v)
    (heq : shifted f (lvl.towerHom hOK) α' = (Pn : lvl.OL⟦X⟧) * v)
    (hα'irr : Irreducible α') (hPdist : Pn.IsDistinguishedAt (maximalIdeal lvl.OL))
    (hassoc : Associated (Pn.coeff 0) α') (hdeg : 0 < Pn.natDegree)
    (hα'norm : ‖algebraMap lvl.OL (K_2 (K' := lvl.L) Pn) α'‖ < 1)
    {x x' : K_2 (K' := lvl.L) Pn}
    (hroot : Polynomial.aeval x (Pn.map (algebraMap lvl.OL lvl.L)) = 0)
    (hroot' : Polynomial.aeval x' (Pn.map (algebraMap lvl.OL lvl.L)) = 0) :
    letI := lvl.instAlgebraO Pn hOK
    ∃ t' ∈ piTorsion (K := K_2 (K' := lvl.L) Pn) hπ hf 1, x' = FPiEval hπ hf x t' := by
  letI := lvl.algL
  letI := lvl.instAlgebraO Pn hOK
  have h1 := lvl.eval_f_eq_of_root Pn hOK hnormL hv heq hα'irr hPdist hassoc hdeg hα'norm hroot
  have h2 := lvl.eval_f_eq_of_root Pn hOK hnormL hv heq hα'irr hPdist hassoc hdeg hα'norm hroot'
  have hx : ‖x‖ < 1 :=
    lvl.norm_lt_one_of_root Pn hnormL hα'irr hPdist hassoc hdeg hα'norm hroot
  have hx' : ‖x'‖ < 1 :=
    lvl.norm_lt_one_of_root Pn hnormL hα'irr hPdist hassoc hdeg hα'norm hroot'
  exact exists_piTorsion_translate_of_eval_f_eq (lvl.hOK_transport Pn hOK hnormL) hπ hf hx hx'
    (h1.trans h2.symm)

/-- **Monogenicity of the next level's ring of integers over `lvl.OL`**, generically. -/
theorem Level.adjoin_eq_integralClosure_next [CharZero K] (Pn : lvl.OL[X])
    {α' : lvl.OL} (hα'irr : Irreducible α')
    (hPdist : Pn.IsDistinguishedAt (maximalIdeal lvl.OL))
    (hassoc : Associated (Pn.coeff 0) α')
    (hirr : Irreducible (Pn.map (algebraMap lvl.OL lvl.L)))
    {β : K_2 (K' := lvl.L) Pn}
    (hβroot : Polynomial.aeval β (Pn.map (algebraMap lvl.OL lvl.L)) = 0)
    (hgen : (minpoly lvl.L β).natDegree = Module.finrank lvl.L (K_2 (K' := lvl.L) Pn)) :
    Algebra.adjoin lvl.OL ({β} : Set (K_2 (K' := lvl.L) Pn)) =
      integralClosure lvl.OL (K_2 (K' := lvl.L) Pn) := by
  letI := lvl.algL
  letI := lvl.finiteDim
  haveI : CharZero lvl.L := charZero_of_injective_algebraMap (algebraMap K lvl.L).injective
  haveI : Algebra.IsIntegral lvl.L (K_2 (K' := lvl.L) Pn) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable lvl.L (K_2 (K' := lvl.L) Pn) := Algebra.IsSeparable.of_integral _ _
  have hβint : IsIntegral lvl.OL β := by
    refine ⟨Pn, hPdist.monic, ?_⟩
    have h1 : Polynomial.aeval β (Polynomial.map (algebraMap lvl.OL lvl.L) Pn) = 0 := hβroot
    rwa [Polynomial.aeval_map_algebraMap] at h1
  have hminK : minpoly lvl.L β = Pn.map (algebraMap lvl.OL lvl.L) :=
    (minpoly.eq_of_irreducible_of_monic hirr hβroot (hPdist.monic.map _)).symm
  have hminR : minpoly lvl.OL β = Pn := by
    have hfrac : minpoly lvl.L β =
        Polynomial.map (algebraMap lvl.OL lvl.L) (minpoly lvl.OL β) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' lvl.L hβint
    have hinj : Function.Injective (algebraMap lvl.OL lvl.L) := IsFractionRing.injective _ lvl.L
    exact Polynomial.map_injective _ hinj (hfrac ▸ hminK)
  have hEisPn : Pn.IsEisensteinAt (maximalIdeal lvl.OL) :=
    hPdist.monic.isEisensteinAt_of_mem_of_notMem (maximalIdeal.isMaximal lvl.OL).ne_top
      (fun {n} hn => hPdist.toIsWeaklyEisensteinAt.mem hn)
      (not_mem_sq_maximalIdeal_of_associated hα'irr hassoc)
  have hIdeq : Submodule.span lvl.OL ({α'} : Set lvl.OL) = maximalIdeal lvl.OL := by
    rw [Ideal.submodule_span_eq]
    exact (Irreducible.maximalIdeal_eq hα'irr).symm
  have hEis : (minpoly lvl.OL β).IsEisensteinAt
      (Submodule.span lvl.OL ({α'} : Set lvl.OL)) := by
    rw [hminR, hIdeq]; exact hEisPn
  exact adjoin_eq_integralClosure_of_isEisensteinAt hα'irr hβint hEis hgen

/-- **The induction step, at the level of the bundled `TowerStep` data.** -/
theorem TowerStep.exists_next {f : O⟦X⟧} {hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1}
    (ts : TowerStep f hOK) [CharZero K]
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1)
    (hf : IsLubinTatePoly π (residueCard O) f)
    (hirr : Irreducible (ts.nextPoly.map (algebraMap ts.lvl.OL ts.lvl.L)))
    {β : K_2 (K' := ts.lvl.L) ts.nextPoly}
    (hβroot : Polynomial.aeval β (ts.nextPoly.map (algebraMap ts.lvl.OL ts.lvl.L)) = 0)
    (hgen : (minpoly ts.lvl.L β).natDegree =
      Module.finrank ts.lvl.L (K_2 (K' := ts.lvl.L) ts.nextPoly)) :
    ∃ st : TowerStep f hOK, st.lvl = ts.lvl.next ts.nextPoly := by
  letI := ts.instDomain
  letI := ts.instDVR
  obtain ⟨Pnext, unext, gen, hunit, hdist, hdegW, hgenirr, heqW, hassocW, hnormW⟩ :=
    ts.lvl.exists_tower_step_next ts.nextPoly hOK ts.hnormL hπ hπnorm hf ts.genIrr ts.nextDist
      ts.nextAssoc ts.nextDegPos ts.genNormLt hirr hβroot hgen
  refine ⟨{ lvl := ts.lvl.next ts.nextPoly
            hnormL := hnorm_K_of_Level ts.lvl ts.nextPoly ts.hnormL
            instDomain := (ts.lvl.next ts.nextPoly).isDomain_OL
            instDVR := (ts.lvl.next ts.nextPoly).isDiscreteValuationRing_OL
            gen := gen, genIrr := hgenirr, nextPoly := Pnext, nextDist := hdist
            nextAssoc := hassocW
            nextDegPos := by rw [hdegW]; exact lt_of_lt_of_le two_pos two_le_residueCard
            unit := unext, unitIsUnit := hunit, weierstrass := heqW
            genNormLt := hnormW }, rfl⟩

end Exists

section ConcreteCheck

variable {P : O[X]}
  (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])

theorem exists_eisenstein_tower_step_K_2_flat'_of_Level (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : K_2 (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂)] [CharZero K]
    [IsDiscreteValuationRing ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (K_2 (K' := K_1 (K := K) P) P₂))]
    [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)] :
    ∃ (P₃ : (O_K2 (K := K) P₂)[X]) (u₃ : (O_K2 (K := K) P₂)⟦X⟧) (β' : O_K2 (K := K) P₂),
      IsUnit u₃ ∧ P₃.IsDistinguishedAt (maximalIdeal _) ∧ P₃.natDegree = residueCard O ∧
      Irreducible β' ∧
      letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : _⟦X⟧) * u₃ ∧
      Associated (P₃.coeff 0) β' := by
  have hxK : IsIntegral (K_1 (K := K) P) β := by
    refine ⟨P₂.map (algebraMap _ (K_1 (K := K) P)), hP₂dist.monic.map _, hβroot⟩
  have hgen : (minpoly (K_1 (K := K) P) β).natDegree =
      Module.finrank (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂) :=
    (IntermediateField.adjoin.finrank hxK).symm.trans (hβfin.trans
      (finrank_K_2_eq_residueCard (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq hPdist
        hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hβroot hβfin).symm)
  obtain ⟨P₃, u₃, β', hu₃, hdist, hdeg₃, hirr₃, heq₃, hassoc₃, -⟩ :=
    Level.exists_tower_step_next (level_K_1 (K := K) (P := P)) P₂ hOK
      (hnorm_K_K_1 (K := K) (P := P)) hπ hπnorm hf hα'irr hP₂dist hassoc hdeg hα'norm hirr
      hβroot hgen
  exact ⟨P₃, u₃, β', hu₃, hdist, hdeg₃, hirr₃, heq₃, hassoc₃⟩

example (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : K_2 (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂)] [CharZero K]
    [IsDiscreteValuationRing ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (K_2 (K' := K_1 (K := K) P) P₂))]
    [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)] :
    exists_eisenstein_tower_step_K_2_flat'_of_Level (K := K) (P := P) P₂ hOK hπ hπnorm hf hu heq
        hPdist hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hirr hβroot hβfin =
      exists_eisenstein_tower_step_K_2_flat' (K := K) (P := P) P₂ hOK hπ hπnorm hf hu heq
        hPdist hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hirr hβroot hβfin := rfl

theorem exists_piTorsion_translate_of_aeval_P₂_eq_zero_of_Level
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))⟦X⟧}
    (_hu₂ : IsUnit u₂) (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (_hα'coe : (α' : K_1 (K := K) P) = α)
    {β β' : K_2 (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβ'root : Polynomial.aeval β' (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    ∃ t' ∈ piTorsion (K := K_2 (K' := K_1 (K := K) P) P₂) hπ hf 1,
      β' = FPiEval hπ hf β t' :=
  Level.exists_piTorsion_translate_of_root (level_K_1 (K := K) (P := P)) P₂ hOK
    (hnorm_K_K_1 (K := K) (P := P)) hπ hf _hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hβroot
    hβ'root

/-- The generic transitivity fact, at `level_K_1`, is literally
`exists_piTorsion_translate_of_aeval_P₂_eq_zero`. -/
example (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))⟦X⟧}
    (_hu₂ : IsUnit u₂) (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    {β β' : K_2 (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβ'root : Polynomial.aeval β' (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0) :
    exists_piTorsion_translate_of_aeval_P₂_eq_zero_of_Level (K := K) (P := P) P₂ hOK hπ hf _hu₂
        heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hβroot hβ'root =
      exists_piTorsion_translate_of_aeval_P₂_eq_zero (K := K) (P := P) (P₂ := P₂) hOK hπ hf _hu₂
        heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hβroot hβ'root := rfl

theorem adjoin_eq_integralClosure_K_2_of_Level (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : K_2 (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂)] [CharZero K] :
    Algebra.adjoin ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        ({β} : Set (K_2 (K' := K_1 (K := K) P) P₂)) =
      integralClosure ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) (K_2 (K' := K_1 (K := K) P) P₂) := by
  have hxK : IsIntegral (K_1 (K := K) P) β :=
    ⟨P₂.map (algebraMap _ (K_1 (K := K) P)), hP₂dist.monic.map _, hβroot⟩
  have hgen : (minpoly (K_1 (K := K) P) β).natDegree =
      Module.finrank (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂) :=
    (IntermediateField.adjoin.finrank hxK).symm.trans (hβfin.trans
      (finrank_K_2_eq_residueCard (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq hPdist
        hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hβroot hβfin).symm)
  exact Level.adjoin_eq_integralClosure_next (level_K_1 (K := K) (P := P)) P₂ hα'irr hP₂dist
    hassoc hirr hβroot hgen

/-- **…and it is literally `adjoin_eq_integralClosure_K_2`**, checked by `rfl` on the fully-applied
terms. -/
example (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : K_2 (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂)] [CharZero K] :
    adjoin_eq_integralClosure_K_2_of_Level (K := K) (P := P) P₂ hOK hπ hπnorm hf hu heq hPdist
        hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hirr hβroot hβfin =
      adjoin_eq_integralClosure_K_2 (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq hPdist
        hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hirr hβroot hβfin := rfl

/-! ### Depth 2 -/

variable (P₃ : (O_K2 (K := K) P₂)[X])
  [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]

example : ((level_K_2 (K := K) (P := P) P₂).next P₃).L =
    K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃ := rfl

example : (level_K_2 (K := K) (P := P) P₂).next P₃ =
    ((level_K_1 (K := K) (P := P)).next P₂).next P₃ := rfl

/-- **`K_4`'s Eisenstein polynomial**, produced by the generic step at `level_K_2`. -/
theorem exists_eisenstein_tower_step_K_3 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    (β' : O_K2 (K := K) P₂) (u₃ : (O_K2 (K := K) P₂)⟦X⟧) (hu₃ : IsUnit u₃)
    (heq₃ :
      letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : _⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₃.coeff 0) β') (hdeg : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃}
    (hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0)
    (hγfin : Module.finrank (K2P2 (K := K) P₂) (K2P2 (K := K) P₂)⟮γ⟯ = residueCard O)
    [Algebra.IsSeparable (K2P2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂)
      (K' := K2P2 (K := K) P₂) P₃)] [CharZero K] :
    letI := ((level_K_2 (K := K) (P := P) P₂).next P₃).isDiscreteValuationRing_OL
    ∃ (P₄ : ((level_K_2 (K := K) (P := P) P₂).next P₃).OL[X])
      (u₄ : ((level_K_2 (K := K) (P := P) P₂).next P₃).OL⟦X⟧)
      (gen : ((level_K_2 (K := K) (P := P) P₂).next P₃).OL),
      IsUnit u₄ ∧
        P₄.IsDistinguishedAt (maximalIdeal ((level_K_2 (K := K) (P := P) P₂).next P₃).OL) ∧
        P₄.natDegree = residueCard O ∧ Irreducible gen ∧
        shifted f (((level_K_2 (K := K) (P := P) P₂).next P₃).towerHom hOK) gen =
          (P₄ : _⟦X⟧) * u₄ ∧
        Associated (P₄.coeff 0) gen ∧
        ‖algebraMap ((level_K_2 (K := K) (P := P) P₂).next P₃).OL
          (K_2 (K' := ((level_K_2 (K := K) (P := P) P₂).next P₃).L) P₄) gen‖ < 1 := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  haveI := finiteDimensional_K_K_2 (K := K) (P := P) P₂
  have hirr : Irreducible (P₃.map (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂))) :=
    Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated hβ'irr hP₃dist.monic
      hP₃dist.toIsWeaklyEisensteinAt hdeg hassoc
  have hxK : IsIntegral (K2P2 (K := K) P₂) γ :=
    ⟨P₃.map (algebraMap _ (K2P2 (K := K) P₂)), hP₃dist.monic.map _, hγroot⟩
  have hgen : (minpoly (K2P2 (K := K) P₂) γ).natDegree =
      Module.finrank (K2P2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) :=
    (IntermediateField.adjoin.finrank hxK).symm.trans (hγfin.trans
      (finrank_K_3_eq_residueCard (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq hPdist hPdeg
        β' u₃ hu₃ heq₃ hβ'irr hP₃dist hassoc hdeg hβ'norm hγroot hγfin).symm)
  exact Level.exists_tower_step_next (level_K_2 (K := K) (P := P) P₂) P₃ hOK
    (hnorm_K_K_2 (K := K) (P := P) P₂) hπ hπnorm hf hβ'irr hP₃dist hassoc hdeg hβ'norm hirr
    hγroot hgen

end ConcreteCheck

end LubinTate

end
