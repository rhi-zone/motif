/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepMonogenicK3
import Langlands.IntegralExtensionLocalRing

/-!
# `IsLocalRing O_{K_3}`, one level up from `Langlands/LubinTateTowerStepLocalRing.lean`

`Langlands/LubinTateTowerStepLocalRing.lean`'s three engines
(`Algebra.adjoin_singleton_eq_top_of_adjoin_eq_integralClosure`,
`isLocalRing_integralClosure_of_isDistinguishedAt_root`,
`mem_maximalIdeal_of_isDistinguishedAt_root`) are stated **fully abstractly** — `R`/`L` arbitrary type
variables, no reference to the Lubin-Tate tower's concrete `K_1`/`baseChangeSplittingField` types. This file instantiates
them one level up, at `R := O_{K_2}` (flat spelling), `L := K_3 P₃`, exactly mirroring
`Langlands/LubinTateTowerStepLocalRing.lean`'s own `K_1 → K_2` instantiation — **no new general
infrastructure was needed**: the abstract engines transfer mechanically, since they never depended on
which spelling (nested or flat) of the previous level's `O` they were applied at.

## Main results

* `isLocalRing_integralClosure_K_3` : **`IsLocalRing O_{K_3}`**, instantiation of
  `isLocalRing_integralClosure_of_isDistinguishedAt_root` at `R := O_{K_2}`, `L := K_3 P₃`.
* `isLocalHom_algebraMap_integralClosure_K_3` : the free corollary
  `IsLocalHom (algebraMap O_{K_2} O_{K_3})`.
* `mem_maximalIdeal_integralClosure_K_3` : `γ` (viewed inside `O_{K_3}`) lies in `maximalIdeal
  O_{K_3}`.
-/

noncomputable section

open scoped Polynomial PowerSeries IntermediateField
open IsLocalRing Polynomial PowerSeries

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

/-- **`IsLocalRing O_{K_3}`.** Under exactly `adjoin_eq_integralClosure_K_3`'s hypothesis package,
`O_{K_3} := integralClosure O_{K_2} (K_3 P₃)` is a local ring. Instantiation of
`isLocalRing_integralClosure_of_isDistinguishedAt_root` at `R := O_{K_2}`, `L := K_3 P₃`; `hγroot`
supplies the root-at-`R`-level fact via `Polynomial.aeval_map_algebraMap`, and
`adjoin_eq_integralClosure_K_3` supplies `hadjL`. -/
theorem isLocalRing_integralClosure_K_3 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
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
      (K' := K2P2 (K := K) P₂) P₃)] :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    IsLocalRing (↥(integralClosure (O_K2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃))) := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  have hγroot' : Polynomial.aeval γ P₃ = 0 := by
    have h1 : Polynomial.aeval γ (Polynomial.map
        (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) P₃) = 0 := hγroot
    rwa [Polynomial.aeval_map_algebraMap] at h1
  exact isLocalRing_integralClosure_of_isDistinguishedAt_root hP₃dist hdeg hγroot'
    (adjoin_eq_integralClosure_K_3 (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq hPdist hPdeg β'
      u₃ hu₃ heq₃ hβ'irr hP₃dist hassoc hdeg hβ'norm hγroot hγfin)

/-- **`algebraMap O_{K_2} O_{K_3}` is a local homomorphism.** Free corollary of
`isLocalRing_integralClosure_K_3` via `IsLocalHom.algebraMap_of_isIntegral`. -/
theorem isLocalHom_algebraMap_integralClosure_K_3 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
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
      (K' := K2P2 (K := K) P₂) P₃)] :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    IsLocalHom (algebraMap (O_K2 (K := K) P₂) (↥(integralClosure (O_K2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)))) := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  haveI := isLocalRing_integralClosure_K_3 (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq hPdist
    hPdeg β' u₃ hu₃ heq₃ hβ'irr hP₃dist hassoc hdeg hβ'norm hγroot hγfin
  exact IsLocalHom.algebraMap_of_isIntegral
    (R := O_K2 (K := K) P₂)
    (S := ↥(integralClosure (O_K2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)))

/-- **`γ` (viewed inside `O_{K_3}`) lies in `maximalIdeal O_{K_3}`.** The instantiation of
`mem_maximalIdeal_of_isDistinguishedAt_root` needed for residue-field-preservation. Takes
`[IsLocalRing O_{K_3}]`/`[IsLocalHom (algebraMap O_{K_2} O_{K_3})]` as explicit hypotheses — callers
supply them via `isLocalRing_integralClosure_K_3` / `isLocalHom_algebraMap_integralClosure_K_3`
(`haveI`). -/
theorem mem_maximalIdeal_integralClosure_K_3 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
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
    [Algebra.IsSeparable (K2P2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂)
      (K' := K2P2 (K := K) P₂) P₃)]
    (hγint : IsIntegral (O_K2 (K := K) P₂) γ)
    [IsLocalRing (↥(integralClosure (O_K2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)))]
    [IsLocalHom (algebraMap (O_K2 (K := K) P₂) (↥(integralClosure (O_K2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃))))] :
    (⟨γ, hγint⟩ : ↥(integralClosure (O_K2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃))) ∈
      maximalIdeal (↥(integralClosure (O_K2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃))) := by
  have hγroot' : Polynomial.aeval γ P₃ = 0 := by
    have h1 : Polynomial.aeval γ (Polynomial.map
        (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) P₃) = 0 := hγroot
    rwa [Polynomial.aeval_map_algebraMap] at h1
  exact mem_maximalIdeal_of_isDistinguishedAt_root
    (R := O_K2 (K := K) P₂)
    (L := K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) hP₃dist hγint hγroot'

end LubinTate

end
