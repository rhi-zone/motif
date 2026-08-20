/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLevelResidueField
import Langlands.LubinTateTowerStepResidueFieldK3

/-!
# The `K_2 → K_3` residue-field cross-check `ROADMAP.md §88` left open

`§88` closed `Level.residueFieldEquiv_next` (the generic one-hop residue-field-preservation step)
and checked it against both concrete depths, but the `K_2 → K_3` check there was only a
*type-checks* confirmation, not a data-level `rfl` against `residueFieldEquiv_K_3` itself:
`residueFieldEquiv_K_3`'s own codomain is reached through the nested-vs-flat `residueFieldEquiv_
integralClosure_integralClosure` bridge (`Langlands/IntegralClosureTower.lean`), which `§88`
explicitly left untested rather than forced. This file does that check, at the concrete `K_2 → K_3`
depth this arc has fully built.

## What the check states

`residueFieldEquiv_K_3` is (per its own proof, `Langlands/LubinTateTowerStepResidueFieldK3.lean`) the
composite `residueFieldEquiv_K_2 |>.trans (nested-flat bridge) |>.trans
(IsLocalRing.residueFieldEquivOfAdjoinSingleton hγmem hadjS)`. `Level.residueFieldEquiv_next
(level_K_2 P₂) P₃ …` is exactly a repackaging of that final factor, generic in `lvl : Level K`. Since
`Level.residueFieldEquiv_next` derives its `hgen` internally from `Splits`+`[CharZero K]` data
(`§86`/`§87`/`§88`'s established route) rather than taking `hβfin`/`hγfin` directly the way
`residueFieldEquiv_K_3` does, this check supplies the `Splits` witness via `Level.splits_next
(level_K_1) P₂ hOK (splits_divX_map_K_1 P)` (the identical expression
`Langlands/LubinTateTowerStepLevelMonogenicHgenCheck.lean`'s own `K_2 → K_3` check already uses for
the same purpose) and an ambient `[CharZero K]`, and derives `hirr` the same way
`adjoin_eq_integralClosure_K_3`'s own proof does
(`Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated`) — matching that file's already-
established pattern for bridging the two hypothesis packages, not a new derivation route.

**What the `rfl` does and does not establish**, unchanged from every other `rfl` check in this arc:
both sides are `RingEquiv` *data*, not a `Prop` — so, as `§88` itself notes for the one-hop
`Level.residueFieldEquiv_next` check, definitional proof irrelevance does *not* apply here the way it
does for the `Prop`-valued checks (`§82`–`§87`). A `rfl` between two `RingEquiv` terms is a materially
stronger claim: it says the generic route's composite (`residueFieldEquiv_K_2` composed with the
nested-flat bridge composed with the *generic* final step) produces the literal same equivalence, as
data, that `residueFieldEquiv_K_3`'s independently-hand-written proof produces. -/

noncomputable section

open scoped Polynomial IntermediateField

open IsLocalRing Polynomial PowerSeries LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K] [CharZero K]

/-- Auxiliary construction only: the generic-route composite for `ResidueField ↥𝒪[K] ≃+*
`ResidueField O_{K_3}` (flat), built exactly the way `residueFieldEquiv_K_3`'s own proof composes
its three factors, except the final factor is `Level.residueFieldEquiv_next` (generic) rather than
a direct `IsLocalRing.residueFieldEquivOfAdjoinSingleton` call. Stated as a separate `def` (rather
than inlined into the `example` below) purely so its local `haveI`s (`isScalarTower_R_K_1_K_2`,
`isLocalRing_integralClosure_integralClosure`, `isLocalHom_algebraMap_integralClosure_K_2`) are
available while its *body* elaborates, without forcing the comparison `example`'s own *type* to
need them at signature-elaboration time. -/
noncomputable def genericResidueFieldEquiv_K_3_route {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]
    (P₃ : (O_K2 (K := K) P₂)[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
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
    (hα'norm : ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : K_2 (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂)]
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
  letI := (level_K_2 (K := K) (P := P) P₂).algL
  letI := (level_K_2 (K := K) (P := P) P₂).finiteDim
  exact ((residueFieldEquiv_K_2 (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq hPdist hPdeg hϖ
      hϖnorm hu₂ heq₂ hα'irr hP₂dist hassoc₂ hdeg₂ hα'norm hα'coe hirr hβroot hβfin).trans
    (residueFieldEquiv_integralClosure_integralClosure
      (R := ↥(ValuativeRel.valuation K).valuationSubring) (L := K_1 (K := K) P)
      (M := K2P2 (K := K) P₂)).symm).trans
    (Level.residueFieldEquiv_next (level_K_2 (K := K) (P := P) P₂) P₃ hOK
      (hnorm_K_K_2 (K := K) (P := P) P₂) hπ hπnorm hf hu heq hPdist hPdeg
      (Level.splits_next (level_K_1 (K := K) (P := P)) P₂ hOK (splits_divX_map_K_1 (K := K) P))
      hu₃ heq₃ hβ'irr hP₃dist hassoc₃ hdeg₃ hβ'norm
      (Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated hβ'irr hP₃dist.monic
        hP₃dist.toIsWeaklyEisensteinAt hdeg₃ hassoc₃)
      hγroot)

/-- **…and it is literally `residueFieldEquiv_K_3`**, checked by `rfl` on the fully-applied terms —
this arc's established non-vacuity discipline (`§78`–`§88`), now closing the one data-level check
`§88` left untested. -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]
    (P₃ : (O_K2 (K := K) P₂)[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
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
    (hα'norm : ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : K_2 (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂)]
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
    genericResidueFieldEquiv_K_3_route (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq hPdist hPdeg
        hϖ hϖnorm hu₂ heq₂ hα'irr hP₂dist hassoc₂ hdeg₂ hα'norm hα'coe hirr hβroot hβfin β' u₃ hu₃
        heq₃ hβ'irr hP₃dist hassoc₃ hdeg₃ hβ'norm hγroot =
      residueFieldEquiv_K_3 (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq hPdist hPdeg hϖ hϖnorm
        hu₂ heq₂ hα'irr hP₂dist hassoc₂ hdeg₂ hα'norm hα'coe hirr hβroot hβfin β' u₃ hu₃ heq₃ hβ'irr
        hP₃dist hassoc₃ hdeg₃ hβ'norm hγroot hγfin := rfl

end
