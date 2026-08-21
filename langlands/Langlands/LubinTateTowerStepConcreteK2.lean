/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepMonogenic
import Langlands.LubinTateTowerStepAdicCompleteK2
import Langlands.EisensteinUniformizerAbstract
import Langlands.IntegralClosureTower

/-!
# The tower step, instantiated at `O_{K_2}` — producing `K_3`'s Eisenstein polynomial

`ROADMAP.md §62` left two independent gaps standing between the general `IsAdicComplete`/
`IsDiscreteValuationRing` `RingEquiv` transport (`Langlands/IntegralClosureTower.lean`) and
actually running `Langlands/LubinTateTowerStep.lean`'s `TowerStep` machinery at `O' := O_{K_2}`:

1. **The missing `Algebra`/`IsScalarTower` composite** at `R := 𝒪[K]` (`isScalarTower_R_K_1_K_2`
   below). This turns out to be free: Mathlib's `Algebra.ofSubsemiring` (`R` a subring of `K`,
   `[Algebra K M]` in scope) and `Tower.subsemiring` (the accompanying `IsScalarTower R K M`)
   already supply `Algebra R (nextSplittingField P₂)` and `IsScalarTower R K (nextSplittingField P₂)` automatically, once
   `K_2.instAlgebraK` is activated via `letI`; the remaining `IsScalarTower R (K_1 P) (nextSplittingField P₂)`
   (not `R K (nextSplittingField P₂)`) follows by `rfl`, since `K_2.algebraMap_K_eq`'s two-hop composite and
   `Algebra.ofSubsemiring`'s composite agree definitionally.
2. **The `nextSplittingField`-level uniformizer.** `Langlands/EisensteinUniformizerAbstract.lean` provides the
   bare-Eisenstein analogue of `exists_irreducible_uniformizer_K_1`'s machinery, avoiding the
   `ValuativeRel (K_1 P)` diamond. `irreducible_of_isEisensteinAt_K_2` below applies it: the
   generator `β` (already supplied by `Langlands/LubinTateTowerStepDegree.lean`'s
   `exists_finrank_adjoin_eq_residueCard_K_2`) has Eisenstein minimal polynomial over `O_{K_1}`
   (`minpoly O_{K_1} β = P₂` on the nose — the same identification `Langlands/
   LubinTateTowerStepMonogenic.lean`'s `adjoin_eq_integralClosure_K_2` makes, reproduced here
   because it is not itself exported as a standalone lemma) and generates `nextSplittingField P₂` over `K_1 P`
   (`hgen`, from `finrank_K_2_eq_residueCard`), so it is irreducible in `O_{K_2}`.

With both closed, `exists_eisenstein_tower_step_K_2` runs `TowerStep`'s
`exists_isWeierstrassFactorization_shifted` at `O' := O_{K_2}` (the `O_{K_1}`-relative spelling),
`ψ := ` the three-hop composite `O → O_{K_1} → O_{K_2}` (`isLocalHom_comp_towerHom_K_2`, already
built), `α' := ` the `nextSplittingField`-uniformizer above — **producing a monic degree-`q` polynomial `P₃` over
`O_{K_2}`, Weierstrass factor of `f(X) - β'`, Eisenstein at `𝔪_{O_{K_2}}`. This is `K_3`'s
Eisenstein polynomial.**

## What `exists_eisenstein_tower_step_K_2` still asks of its caller

Its own conclusion mentions `maximalIdeal O_{K_2}` (via `IsDistinguishedAt`), so — as `§62`'s
Obstacle 2 diagnosed — `[IsDiscreteValuationRing O_{K_2}]` must be an ambient hypothesis of the
*statement itself*, not something derivable purely inside the proof: `O_{K_2}`'s `Algebra K
(nextSplittingField P₂)` structure needed to state that instance is only available once `K_2.instAlgebraK` is
`letI`-activated, which cannot happen before the theorem's own return type is elaborated. In
return, this instance genuinely *is* available at every call site that has already done the same
`letI`/`haveI` staging this file's own proof does (`isAdicComplete_integralClosure_integralClosure`
applied to the base-relative `NormedField.isAdicComplete_integralClosure_of_finiteDimensional`
fact) — it is bookkeeping, not a new mathematical gap.

## Relation to `ROADMAP.md`'s two-gap framing

Both gaps recorded in `§62`'s "Next step" are closed by this file plus
`Langlands/EisensteinUniformizerAbstract.lean`: `K_3`'s Eisenstein polynomial is produced. See
`ROADMAP.md` for the full account of what this establishes about the tower's iterability past
`nextSplittingField`.
-/

noncomputable section

open scoped Polynomial IntermediateField
open IsLocalRing Polynomial PowerSeries

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]
variable {P : O[X]}
  {P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X]}

/-- **`IsScalarTower R (K_1 P) (nextSplittingField P₂)`, `R := 𝒪[K]`** — `§62`'s Obstacle 3, closed. `Algebra R
(K_1 P)` and `Algebra R (nextSplittingField P₂)` both resolve automatically via Mathlib's `Algebra.ofSubsemiring`
(`R` a `Subring K`) once `K_2.instAlgebraK` is active; the two composites `R → K → K_1 P → K_2 P₂`
and `R → K_1 P → K_2 P₂` agree on the nose (`Algebra.ofSubsemiring`'s composite unfolds through
`K_2.algebraMap_K_eq`'s own two-hop composite by `rfl`), so `IsScalarTower.of_algebraMap_eq` closes
with the trivial witness. -/
theorem isScalarTower_R_K_1_K_2 :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    IsScalarTower ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)
      (nextSplittingField (K' := K_1 (K := K) P) P₂) := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rfl

/-- **The level-2 generator `β`, viewed in `O_{K_2}`, is irreducible there** — a uniformizer of
`O_{K_2}`, the `nextSplittingField`-level analogue of `exists_irreducible_uniformizer_K_1`. Reproduces `Langlands/
LubinTateTowerStepMonogenic.lean`'s `adjoin_eq_integralClosure_K_2` proof up through `hminR`/`hgen`
(not exported there as standalone lemmas) and finishes with `Langlands/
EisensteinUniformizerAbstract.lean`'s `irreducible_of_isEisensteinAt` instead of `Langlands/
EisensteinMonogenicAbstract.lean`'s `adjoin_eq_integralClosure_of_isEisensteinAt` — the same
Eisenstein data (`hminR`, `hEisP₂`, `hgen`), a different conclusion. -/
theorem irreducible_of_isEisensteinAt_K_2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
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
    (hα'norm : ‖algebraMap _ (nextSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : nextSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂)]
    [IsDiscreteValuationRing ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (nextSplittingField (K' := K_1 (K := K) P) P₂))] :
    ∃ hβint : IsIntegral ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) β,
      Irreducible (⟨β, hβint⟩ : ↥(integralClosure
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (nextSplittingField (K' := K_1 (K := K) P) P₂))) := by
  have hβint : IsIntegral ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)) β := by
    refine ⟨P₂, hP₂dist.monic, ?_⟩
    have h1 : Polynomial.aeval β (Polynomial.map
        (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (K_1 (K := K) P)) P₂) = 0 := hβroot
    rwa [Polynomial.aeval_map_algebraMap] at h1
  refine ⟨hβint, ?_⟩
  have hminK1 : minpoly (K_1 (K := K) P) β = P₂.map
      (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) (K_1 (K := K) P)) :=
    (minpoly.eq_of_irreducible_of_monic hirr hβroot (hP₂dist.monic.map _)).symm
  have hminR : minpoly ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)) β = P₂ := by
    have hfrac : minpoly (K_1 (K := K) P) β = Polynomial.map
        (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (K_1 (K := K) P))
        (minpoly ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) β) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' (K_1 (K := K) P) hβint
    have hinj : Function.Injective (algebraMap
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (K_1 (K := K) P)) :=
      IsFractionRing.injective _ (K_1 (K := K) P)
    exact (Polynomial.map_injective _ hinj (hfrac ▸ hminK1))
  have hEisP₂ : P₂.IsEisensteinAt (maximalIdeal
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))) :=
    hP₂dist.monic.isEisensteinAt_of_mem_of_notMem
      (maximalIdeal.isMaximal ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P))).ne_top
      (fun {n} hn => hP₂dist.toIsWeaklyEisensteinAt.mem hn)
      (not_mem_sq_maximalIdeal_of_associated hα'irr hassoc)
  have hxK : IsIntegral (K_1 (K := K) P) β := hβint.tower_top
  have hgen : (minpoly (K_1 (K := K) P) β).natDegree =
      Module.finrank (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂) :=
    (IntermediateField.adjoin.finrank hxK).symm.trans (hβfin.trans
      (finrank_K_2_eq_residueCard (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq hPdist
        hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hβroot hβfin).symm)
  exact irreducible_of_isEisensteinAt hα'irr hβint (hminR.symm ▸ hEisP₂) hgen

/-- **The tower step, instantiated at `O_{K_2}`.** `O' := O_{K_2}` (`O_{K_1}`-relative spelling),
`ψ := ` the three-hop composite `O → O_{K_1} → O_{K_2}` (`isLocalHom_comp_towerHom_K_2`), `α' := `
`irreducible_of_isEisensteinAt_K_2`'s uniformizer. `Langlands/LubinTateTowerStep.lean`'s
`exists_isWeierstrassFactorization_shifted` gives back a monic degree-`q` polynomial `P₃` over
`O_{K_2}`, distinguished at `𝔪_{O_{K_2}}` — **`K_3`'s Eisenstein polynomial.**

`[IsDiscreteValuationRing O_{K_2}]` is taken as an ambient hypothesis rather than derived (see the
module docstring): the conclusion itself mentions `maximalIdeal O_{K_2}`, which needs this instance
to elaborate at all, before `K_2.instAlgebraK`'s `letI` (needed to derive it) is available.

The conclusion also returns the generator `β' := ⟨β, hβint⟩` (the nested-`O_{K_2}`-typed uniformizer
`irreducible_of_isEisensteinAt_K_2` builds `hβirr` for), `Irreducible β'`, the Weierstrass equation
`shifted f ψ β' = P₃ * u₃` for `ψ` the three-hop nested structure map `O → O_{K_1} → (nested O_{K_2})`
this theorem's own proof already builds to call
`exists_isWeierstrassFactorization_shifted`, and `Associated (P₃.coeff 0) β'` — previously discarded
via `-` patterns (`ROADMAP.md §76`). This matches `exists_eisenstein_tower_step_K_1`'s own standard
(see its docstring): downstream root-membership arguments at the `K_2 → K_3` step can rebuild `P₃`'s
Eisenstein-shape data without re-invoking `exists_isWeierstrassFactorization_shifted` at a possibly
different existential witness, and — new at this level — without losing `β'`/`heq₃` entirely, which
the flat-spelling `K_3`-level theorems (`Langlands/LubinTateTowerStepK3RootConnect.lean`) require as
explicit hypotheses. -/
theorem exists_eisenstein_tower_step_K_2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
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
    (hα'norm : ‖algebraMap _ (nextSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : nextSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂)] [CharZero K]
    [IsDiscreteValuationRing ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (nextSplittingField (K' := K_1 (K := K) P) P₂))] :
    ∃ (P₃ : (↥(integralClosure
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (nextSplittingField (K' := K_1 (K := K) P) P₂)))[X])
      (u₃ : (↥(integralClosure
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (nextSplittingField (K' := K_1 (K := K) P) P₂)))⟦X⟧)
      (β' : ↥(integralClosure
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (nextSplittingField (K' := K_1 (K := K) P) P₂))),
      IsUnit u₃ ∧ P₃.IsDistinguishedAt (maximalIdeal _) ∧ P₃.natDegree = residueCard O ∧
        Irreducible β' ∧
        shifted f ((algebraMap ↥(integralClosure
          ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
          ↥(integralClosure
            ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
            (nextSplittingField (K' := K_1 (K := K) P) P₂))).comp (towerHom (K := K) hOK P)) β' =
          (P₃ : _⟦X⟧) * u₃ ∧
        Associated (P₃.coeff 0) β' := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  haveI := finiteDimensional_K_K_2 (K := K) (P := P) P₂
  haveI := algebraIsSeparable_K_K_2 (K := K) (P := P) P₂
  haveI := isScalarTower_R_K_1_K_2 (K := K) (P := P) (P₂ := P₂)
  haveI hAdicbase : IsAdicComplete
      (maximalIdeal ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (nextSplittingField (K' := K_1 (K := K) P) P₂)))
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (nextSplittingField (K' := K_1 (K := K) P) P₂)) :=
    NormedField.isAdicComplete_integralClosure_of_finiteDimensional
      (K := K) (L := nextSplittingField (K' := K_1 (K := K) P) P₂) (K_2.hnorm_K (K := K) (P := P) P₂)
  haveI hAdictop := isAdicComplete_integralClosure_integralClosure
    (R := ↥(ValuativeRel.valuation K).valuationSubring) (L := K_1 (K := K) P)
    (M := nextSplittingField (K' := K_1 (K := K) P) P₂)
  obtain ⟨hβint, hβirr⟩ :=
    irreducible_of_isEisensteinAt_K_2 hOK hπ hπnorm hf hu heq hPdist hPdeg hu₂ heq₂ hα'irr hP₂dist
      hassoc hdeg hα'norm hα'coe hirr hβroot hβfin
  haveI := isLocalHom_comp_towerHom_K_2 P₂ hOK hπ hπnorm hf hu heq hPdist hPdeg hu₂ heq₂ hα'irr
    hP₂dist hassoc hdeg hα'norm hα'coe hirr hβroot hβfin
  obtain ⟨P₃, u₃, hP₃dist, hu₃, heq₃, hdeg₃, hassoc₃⟩ :=
    exists_isWeierstrassFactorization_shifted (O' := ↥(integralClosure
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (nextSplittingField (K' := K_1 (K := K) P) P₂))) hf
      ((algebraMap ↥(integralClosure
        ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        ↥(integralClosure
          ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
          (nextSplittingField (K' := K_1 (K := K) P) P₂))).comp (towerHom (K := K) hOK P))
      hβirr
  exact ⟨P₃, u₃, ⟨β, hβint⟩, hu₃, hP₃dist, hdeg₃, hβirr, heq₃, hassoc₃⟩

end LubinTate

end
