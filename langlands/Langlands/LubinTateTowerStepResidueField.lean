/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLocalRing
import Langlands.LubinTateResidueFieldPreservation

/-!
# Residue-field preservation for `O_{K_2}`

`Langlands/LubinTateTowerStepLocalRing.lean` closes `[IsLocalRing O_{K_2}]`,
`[IsLocalHom (algebraMap O_{K_1} O_{K_2})]`, and `β ∈ maximalIdeal O_{K_2}` — the three inputs
`IsLocalRing.residueFieldEquivOfAdjoinSingleton` (`Langlands/TotallyRamifiedResidueField.lean`) needs
besides monogenicity itself (`Langlands/LubinTateTowerStepMonogenic.lean`'s
`adjoin_eq_integralClosure_K_2`, transported to the `O_{K_2}`-level `⊤` statement by
`Algebra.adjoin_singleton_eq_top_of_adjoin_eq_integralClosure`). This file assembles them into
`ResidueField O_{K_1} ≃+* ResidueField O_{K_2}`, then composes with
`Langlands/LubinTateResidueFieldPreservation.lean`'s `LubinTate.residueFieldEquiv_K_1` for the full
tower statement.

## Main result

* `LubinTate.residueFieldEquiv_K_2` : **`ResidueField ↥𝒪[K] ≃+* ResidueField O_{K_2}`.**

## Why the result is stated for `ResidueField ↥𝒪[K]`, not `ResidueField O`

`residueFieldEquiv_K_1` is stated `ResidueField ↥𝒪[K] ≃+* ResidueField ↥𝒪_{K_1}` — its *source* is
the residue field of `𝒪[K] := (ValuativeRel.valuation K).valuationSubring`, not of the abstract base
ring `O` the ambient hypothesis package (`hOK`, `hπnorm`, …) is stated in terms of. No lemma
identifying `ResidueField O` with `ResidueField ↥𝒪[K]` exists here (relating `O`'s image in `K` to
the *literal* valuation subring is a separate open gap — see `Langlands/LubinTateTowerStep.lean`'s
module docstring). This file states its result with the same `↥𝒪[K]` source `residueFieldEquiv_K_1`
itself uses, rather than overclaiming a statement about `O` that nothing here establishes.
-/

noncomputable section

open scoped Polynomial PowerSeries IntermediateField
open IsLocalRing Polynomial PowerSeries ValuativeRel

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Algebra O K] [IsFractionRing O K]
variable {P : O[X]}
  {P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X]}

/-- **`ResidueField ↥𝒪[K] ≃+* ResidueField O_{K_2}`.** Residue-field preservation for the
second Lubin-Tate tower step. Composes
`LubinTate.residueFieldEquiv_K_1` (`ResidueField ↥𝒪[K] ≃+* ResidueField O_{K_1}`) with
`IsLocalRing.residueFieldEquivOfAdjoinSingleton` applied at `A := O_{K_1}`, `B := O_{K_2}`, `π := β`
(viewed inside `O_{K_2}`) — `β ∈ maximalIdeal O_{K_2}` from
`mem_maximalIdeal_integralClosure_K_2`, and `Algebra.adjoin O_{K_1} {β} = ⊤` from
`adjoin_eq_integralClosure_K_2` transported via
`Algebra.adjoin_singleton_eq_top_of_adjoin_eq_integralClosure`.

Takes `[IsLocalRing O_{K_2}]` / `[IsLocalHom (algebraMap O_{K_1} O_{K_2})]` as explicit hypotheses,
rather than deriving them internally, because `ResidueField O_{K_2}` needs `[IsLocalRing O_{K_2}]`
already to *state* this theorem's conclusion — instance resolution cannot see past the `:= by` to
hypotheses derived inside the proof. Callers supply them via `isLocalRing_integralClosure_K_2` /
`isLocalHom_algebraMap_integralClosure_K_2` (`haveI`), exactly as
`mem_maximalIdeal_integralClosure_K_2` (`Langlands/LubinTateTowerStepLocalRing.lean`) already does. -/
def residueFieldEquiv_K_2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {ϖ : ↥(ValuativeRel.valuation K).valuationSubring} (hϖ : Irreducible ϖ)
    (hϖnorm : ‖(ϖ : K)‖ = ‖algebraMap O K π‖)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)]
    [IsLocalRing ↥(integralClosure
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (baseChangeSplittingField (K' := K_1 (K := K) P) P₂))]
    [IsLocalHom (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)) ↥(integralClosure
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)))] :
    ResidueField ↥(ValuativeRel.valuation K).valuationSubring ≃+*
      ResidueField (↥(integralClosure
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (baseChangeSplittingField (K' := K_1 (K := K) P) P₂))) := by
  have hβint : IsIntegral ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)) β := by
    refine ⟨P₂, hP₂dist.monic, ?_⟩
    have h1 : Polynomial.aeval β (Polynomial.map (algebraMap
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (K_1 (K := K) P)) P₂) = 0 := hβroot
    rwa [Polynomial.aeval_map_algebraMap] at h1
  have hadjL : Algebra.adjoin ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)) ({β} : Set (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)) =
      integralClosure ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) :=
    adjoin_eq_integralClosure_K_2 hOK hπ hπnorm hf hu heq hPdist hPdeg hu₂ heq₂ hα'irr hP₂dist
      hassoc hdeg hα'norm hα'coe hirr hβroot hβfin
  have hadjS : Algebra.adjoin ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)) ({(⟨β, hβint⟩ : ↥(integralClosure
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)))} : Set (↥(integralClosure
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)))) = ⊤ :=
    Algebra.adjoin_singleton_eq_top_of_adjoin_eq_integralClosure hβint hadjL
  have hβroot' : Polynomial.aeval β P₂ = 0 := by
    have h1 : Polynomial.aeval β (Polynomial.map (algebraMap
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (K_1 (K := K) P)) P₂) = 0 := hβroot
    rwa [Polynomial.aeval_map_algebraMap] at h1
  have hβmem := mem_maximalIdeal_of_isDistinguishedAt_root
    (R := ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))
    (L := baseChangeSplittingField (K' := K_1 (K := K) P) P₂) hP₂dist hβint hβroot'
  exact (residueFieldEquiv_K_1 hOK hπ hπnorm hf hu heq hPdist hPdeg hϖ hϖnorm).trans
    (IsLocalRing.residueFieldEquivOfAdjoinSingleton hβmem hadjS)

end LubinTate

end
