/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLocalRingK3
import Langlands.LubinTateTowerStepResidueField
import Langlands.IntegralClosureTower
import Langlands.LubinTateResidueFieldPreservation

/-!
# Residue-field preservation for `O_{K_3}` (flat spelling)

The `K_2 → K_3` analogue of `Langlands/LubinTateTowerStepResidueField.lean`'s `residueFieldEquiv_K_2`,
against the *flat* `O_{K_2}` spelling. `Langlands/LubinTateTowerStepLocalRingK3.lean` closes
`[IsLocalRing O_{K_3}]`, `[IsLocalHom (algebraMap O_{K_2} O_{K_3})]`, and `γ ∈ maximalIdeal O_{K_3}` —
the three inputs `IsLocalRing.residueFieldEquivOfAdjoinSingleton` needs besides monogenicity itself
(`Langlands/LubinTateTowerStepMonogenicK3.lean`'s `adjoin_eq_integralClosure_K_3`).

Assembling the *full* tower composite `ResidueField ↥𝒪[K] ≃+* ResidueField O_{K_3}` needs one further
piece beyond the `K_1 → K_2` template: `residueFieldEquiv_K_2` (`Langlands/
LubinTateTowerStepResidueField.lean`) is itself stated against the **nested** `O_{K_2}` spelling
(`ResidueField ↥𝒪[K] ≃+* ResidueField (nested O_{K_2})`), since it predates `ROADMAP.md §73`'s switch
to the flat spelling and was not itself revisited. Bridging its nested-typed codomain to the flat
`O_{K_2}` this file's own one-hop step is built against uses `Langlands/IntegralClosureTower.lean`'s
`residueFieldEquiv_integralClosure_integralClosure` (`.symm`, nested → flat) — exactly the tool that
file's own docstring anticipates for this purpose. `[IsLocalRing (nested O_{K_2})]`, needed for that
bridge, comes for free from the *flat* `[IsLocalRing O_{K_2}]` ambient hypothesis via
`Langlands/IntegralClosureTower.lean`'s `isLocalRing_integralClosure_integralClosure` instance
(flat → nested), with no need to re-derive it through the heavier `K_1 → K_2`-level Eisenstein
machinery `residueFieldEquiv_K_2`'s own proof uses internally.

## Main result

* `residueFieldEquiv_K_3` : **`ResidueField ↥𝒪[K] ≃+* ResidueField O_{K_3}`** (flat spelling).
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
  [Finite (ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]
variable {P : O[X]} (P₂ : (↥(integralClosure
    ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
  [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]
  (P₃ : (O_K2 (K := K) P₂)[X])

set_option synthInstance.maxHeartbeats 1000000 in
/-- **`ResidueField ↥𝒪[K] ≃+* ResidueField O_{K_3}`** (flat spelling), the `K_2 → K_3` analogue of
`residueFieldEquiv_K_2`. Composes: (1) `residueFieldEquiv_K_2` itself (`ResidueField ↥𝒪[K] ≃+*
ResidueField (nested O_{K_2})`); (2) `residueFieldEquiv_integralClosure_integralClosure.symm`, the
nested → flat bridge for `O_{K_2}` (`Langlands/IntegralClosureTower.lean`); (3) `IsLocalRing.
residueFieldEquivOfAdjoinSingleton` applied at `A := O_{K_2}` (flat), `B := O_{K_3}`, `π := γ` — `γ ∈
maximalIdeal O_{K_3}` from `mem_maximalIdeal_integralClosure_K_3`, `Algebra.adjoin O_{K_2} {γ} = ⊤`
from `adjoin_eq_integralClosure_K_3` transported via
`Algebra.adjoin_singleton_eq_top_of_adjoin_eq_integralClosure`.

Takes `[IsLocalRing O_{K_3}]` / `[IsLocalHom (algebraMap O_{K_2} O_{K_3})]` as explicit hypotheses,
exactly as `residueFieldEquiv_K_2` does one level down, for the same reason (the conclusion itself
needs `[IsLocalRing O_{K_3}]` to state `ResidueField O_{K_3}` before the proof can supply it).
Callers get them via `isLocalRing_integralClosure_K_3` / `isLocalHom_algebraMap_integralClosure_K_3`
(`Langlands/LubinTateTowerStepLocalRingK3.lean`, `haveI`).

**`synthInstance.maxHeartbeats` raised**: the `Algebra (O_K2 P₂) ↥(integralClosure (O_K2 P₂)
(K_3 P₃))` instance this proof needs (for `integralClosure (O_K2 P₂) (K_3 P₃)` to be well-formed)
resolves by ordinary instance search — the same search that succeeds by default in
`Langlands/LubinTateTowerStepMonogenicK3.lean` — but the much larger accumulated hypothesis context
here (the full `K → K_1` plus `K_1 → K_2` plus `K_2 → K_3` hypothesis package) makes the search
itself slower, past the default `20000`-heartbeat budget; not a new elaboration-cost class beyond
what `Langlands/LubinTateTowerStepK3.lean`'s module docstring already documents for this doubly-nested
type shape. -/
def residueFieldEquiv_K_3 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
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
    (hassoc₂ : Associated (P₂.coeff 0) α') (hdeg₂ : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)]
    (β' : O_K2 (K := K) P₂) (u₃ : (O_K2 (K := K) P₂)⟦X⟧) (hu₃ : IsUnit u₃)
    (heq₃ :
      letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : _⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc₃ : Associated (P₃.coeff 0) β') (hdeg₃ : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃}
    (hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0)
    (hγfin : Module.finrank (K2P2 (K := K) P₂) (K2P2 (K := K) P₂)⟮γ⟯ = residueCard O)
    [Algebra.IsSeparable (K2P2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂)
      (K' := K2P2 (K := K) P₂) P₃)]
    [IsLocalRing (↥(integralClosure (O_K2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)))]
    [IsLocalHom (algebraMap (O_K2 (K := K) P₂) (↥(integralClosure (O_K2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃))))] :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    ResidueField ↥(ValuativeRel.valuation K).valuationSubring ≃+*
      ResidueField (↥(integralClosure (O_K2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃))) := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  haveI := isScalarTower_R_K_1_K_2 (K := K) (P := P) (P₂ := P₂)
  haveI hlocnested : IsLocalRing ↥(integralClosure
      (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))
      (K2P2 (K := K) P₂)) :=
    isLocalRing_integralClosure_integralClosure
      (R := ↥(ValuativeRel.valuation K).valuationSubring) (L := K_1 (K := K) P)
      (M := K2P2 (K := K) P₂)
  haveI := isLocalHom_algebraMap_integralClosure_K_2 (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf
    hu heq hPdist hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc₂ hdeg₂ hα'norm hα'coe hirr hβroot hβfin
  have e1 := residueFieldEquiv_K_2 (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq hPdist
    hPdeg hϖ hϖnorm hu₂ heq₂ hα'irr hP₂dist hassoc₂ hdeg₂ hα'norm hα'coe hirr hβroot hβfin
  have e2 := (residueFieldEquiv_integralClosure_integralClosure
    (R := ↥(ValuativeRel.valuation K).valuationSubring) (L := K_1 (K := K) P)
    (M := K2P2 (K := K) P₂)).symm
  have hγint : IsIntegral (O_K2 (K := K) P₂) γ := by
    refine ⟨P₃, hP₃dist.monic, ?_⟩
    have h1 : Polynomial.aeval γ (Polynomial.map
        (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) P₃) = 0 := hγroot
    rwa [Polynomial.aeval_map_algebraMap] at h1
  have hadjL : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      Algebra.adjoin (O_K2 (K := K) P₂)
        ({γ} : Set (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) =
      integralClosure (O_K2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) :=
    adjoin_eq_integralClosure_K_3 (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq hPdist hPdeg β'
      u₃ hu₃ heq₃ hβ'irr hP₃dist hassoc₃ hdeg₃ hβ'norm hγroot hγfin
  have hadjS : Algebra.adjoin (O_K2 (K := K) P₂)
      ({(⟨γ, hγint⟩ : ↥(integralClosure (O_K2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)))} :
        Set (↥(integralClosure (O_K2 (K := K) P₂)
          (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)))) = ⊤ :=
    Algebra.adjoin_singleton_eq_top_of_adjoin_eq_integralClosure hγint hadjL
  have hγmem := mem_maximalIdeal_integralClosure_K_3 (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu
    heq hPdist hPdeg β' u₃ hu₃ heq₃ hβ'irr hP₃dist hassoc₃ hdeg₃ hβ'norm hγroot hγint
  exact (e1.trans e2).trans (IsLocalRing.residueFieldEquivOfAdjoinSingleton hγmem hadjS)

end LubinTate

end
