/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLevelInvariance
import Langlands.LubinTateTowerStepMonogenic
import Langlands.LubinTateTowerStepMonogenicK3

/-!
# Item-1 gap `ROADMAP.md §86` left open: does the generic monogenicity theorem, fed the *derived*
`hgen`, still agree with the concrete hand-written theorems?

`§86` derived `Level.natDegree_minpoly_eq_finrank` (the generic `hgen`) but did not re-check that
`Level.adjoin_eq_integralClosure_next` (`§83`), fed *that* derived `hgen` rather than an externally
assumed one, still produces the same monogenicity fact as `adjoin_eq_integralClosure_K_2`
(`Langlands/LubinTateTowerStepMonogenic.lean`) and `adjoin_eq_integralClosure_K_3`
(`Langlands/LubinTateTowerStepMonogenicK3.lean`) at the two real concrete depths. This file is
exactly that check, at both depths, `rfl`.

What the `rfl` does and does not establish, unchanged from every other `rfl` check in this arc
(`§82`–`§86`): both sides are proofs of a `Prop` (an equation between subalgebras), so definitional
proof irrelevance makes the check about whether the two *statements* elaborate to the same type —
which is the real content here, since it is exactly what could fail if the derived `hgen`'s stated
type did not match what `Level.adjoin_eq_integralClosure_next`'s `hgen` argument expects, or if the
generic theorem's conclusion, instantiated, did not line up with the concrete theorem's own
statement. It is not an independent re-proof of monogenicity.

* At `K_1 → K_2` (`level_K_1`): `adjoin_eq_integralClosure_K_2` takes `hirr` as an **explicit**
  hypothesis, so the check simply reuses the caller-supplied `hirr` on both sides.
* At `K_2 → K_3` (`level_K_2`): `adjoin_eq_integralClosure_K_3` **derives** `hirr` internally (from
  `hβ'irr`/`hP₃dist`/`hassoc`/`hdeg` via `Polynomial.irreducible_map_of_isWeaklyEisensteinAt_
  associated`, per that file's own module docstring) rather than taking it as a hypothesis, so this
  check derives `hirr` the identical way before feeding it to `Level.adjoin_eq_integralClosure_next`,
  matching what the concrete theorem's own proof does line for line.

Both checks needed `letI := (level_K_2 …).algL; letI := (level_K_2 …).finiteDim` active before
`IsFractionRing (level_K_2 …).OL (level_K_2 …).L` resolves for the `irreducible_map_of_
isWeaklyEisensteinAt_associated` call at the `K_2 → K_3` depth — the same `§83`-documented pattern
(`Level.isDiscreteValuationRing_OL`/`Level.isDomain_OL`'s own derivation) applied here to a different
consumer of the same two `letI`s; not a new elaboration-cost finding.
-/

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

/-- **`K_1 → K_2`, `rfl`-recovery**: `Level.adjoin_eq_integralClosure_next`, fed the *derived*
`Level.natDegree_minpoly_eq_finrank` as its `hgen`, agrees exactly with
`adjoin_eq_integralClosure_K_2`. -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' =
      (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)))⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)] :
    Level.adjoin_eq_integralClosure_next (level_K_1 (K := K) (P := P)) P₂ hα'irr hP₂dist hassoc hirr
        hβroot
        (Level.natDegree_minpoly_eq_finrank (level_K_1 (K := K) (P := P)) P₂ hOK
          (hnorm_K_K_1 (K := K) (P := P)) hπ hπnorm hf hu heq hPdist hPdeg
          (splits_divX_map_K_1 (K := K) P) hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hβroot) =
      adjoin_eq_integralClosure_K_2 (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq hPdist
        hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hirr hβroot hβfin := rfl

/-- **`K_2 → K_3`, `rfl`-recovery**: the same generic theorem at `level_K_2`, fed the *derived*
`hgen` and an `hirr` derived the identical way `adjoin_eq_integralClosure_K_3`'s own proof derives
it, agrees exactly with `adjoin_eq_integralClosure_K_3`. -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]
    (P₃ : (O_K2 (K := K) P₂)[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    (β' : O_K2 (K := K) P₂) (u₃ : (O_K2 (K := K) P₂)⟦X⟧) (hu₃ : IsUnit u₃)
    (heq₃ : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : (O_K2 (K := K) P₂)⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₃.coeff 0) β') (hdeg : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃}
    (hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0)
    (hγfin : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      Module.finrank (K2P2 (K := K) P₂) (K2P2 (K := K) P₂)⟮γ⟯ = residueCard O)
    [Algebra.IsSeparable (K2P2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂)
      (K' := K2P2 (K := K) P₂) P₃)] :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := (level_K_2 (K := K) (P := P) P₂).algL
    letI := (level_K_2 (K := K) (P := P) P₂).finiteDim
    Level.adjoin_eq_integralClosure_next (level_K_2 (K := K) (P := P) P₂) P₃ hβ'irr hP₃dist hassoc
        (Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated hβ'irr hP₃dist.monic
          hP₃dist.toIsWeaklyEisensteinAt hdeg hassoc)
        hγroot
        (Level.natDegree_minpoly_eq_finrank (level_K_2 (K := K) (P := P) P₂) P₃ hOK
          (hnorm_K_K_2 (K := K) (P := P) P₂) hπ hπnorm hf hu heq hPdist hPdeg
          (Level.splits_next (level_K_1 (K := K) (P := P)) P₂ hOK (splits_divX_map_K_1 (K := K) P))
          hu₃ heq₃ hβ'irr hP₃dist hassoc hdeg hβ'norm hγroot) =
      adjoin_eq_integralClosure_K_3 (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq hPdist hPdeg
        β' u₃ hu₃ heq₃ hβ'irr hP₃dist hassoc hdeg hβ'norm hγroot hγfin := rfl

end
