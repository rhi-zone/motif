/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLevelInvariance
import Langlands.LubinTateTowerStepLocalRing
import Langlands.TotallyRamifiedResidueField

/-!
# Residue-field preservation closes generically, over `Level`

The generic form of residue-field preservation across one tower hop is blocked by an
elaboration-cost `whnf` timeout inside `IsLocalRing.residueFieldEquivOfAdjoinSingleton hβmem hadjS`
at the abstract `lvl : Level K` — a reflexive structural-congruence walk, not a diamond and not
instance search.

**This file closes it, at default heartbeats, with no `maxHeartbeats` override anywhere.** The fix is
to avoid the caller reconstructing `⟨β, hβint⟩`'s underlying integrality proof more than once. The
naive derivation obtains `hβint : IsIntegral lvl.OL β` via a `refine ⟨Pn, hPndist.monic, ?_⟩;
rwa [...]` tactic block, then *separately* re-derives the same fact as a standalone
`hβroot' : Polynomial.aeval β Pn = 0` for `mem_maximalIdeal_of_isDistinguishedAt_root`'s own
`hβroot` argument — two independently-elaborated proof terms of propositionally (but not
syntactically) identical statements, both ending up embedded in the subtype value `⟨β, hβint⟩` that
`hβmem`'s and `hadjS`'s *types* both mention. Deriving `hβroot'` once and using it directly as the
third component of `hβint` (`⟨Pn, hPndist.monic, hβroot'⟩`, term-mode, not a second tactic block) —
so both `hβmem` and `hadjS` are built from the literal same `hβint` term, not two
term-level-distinct-but-defeq ones — removes the elaboration cost: the un-deduplicated version does
not close even given `maxHeartbeats 1000000`, reduced no further than `≈202,000`–`210,000` in
bisection (barely over the default `200,000`), while the deduplicated version below closes cleanly at
the plain default. (Explicit named `A`/`B`/`π` arguments on
`IsLocalRing.residueFieldEquivOfAdjoinSingleton`, tried in combination with the deduplication, made
things *worse* — pushed the timeout back to the theorem's stated conclusion type at line scope, not
just the tactic body — so are deliberately not used here.)

The underlying diagnosis is accurate in kind (a reflexive structural-congruence `whnf` walk, not a
diamond) but was incomplete in scope: part of the walk's cost is genuinely avoidable term-level
duplication introduced by the caller reconstructing the same integrality witness twice, not solely an
intrinsic property of unifying the doubly-nested `Subalgebra` type itself.

## Main result

* `Level.residueFieldEquiv_next` : **`ResidueField lvl.OL ≃+* ResidueField ↥(integralClosure lvl.OL
  (baseChangeSplittingField (K' := lvl.L) Pn))`**, generic in `lvl : Level K` — the one-hop residue-field-preservation
  step, the last piece of the `∀ n` induction. Takes `[IsLocalRing ↥(integralClosure lvl.OL (baseChangeSplittingField Pn))]`
  / `[IsLocalHom (algebraMap lvl.OL ↥(integralClosure lvl.OL (baseChangeSplittingField Pn)))]` as explicit hypotheses, for
  the same reason `residueFieldEquiv_K_2`/`_K_3` do: `ResidueField ↥(integralClosure lvl.OL (baseChangeSplittingField Pn))`
  needs the instance already to *state* the theorem's conclusion, so instance resolution cannot see
  past the `:= by` to anything derived inside the proof.
-/

noncomputable section

open scoped Polynomial PowerSeries IntermediateField
open IsLocalRing Polynomial PowerSeries ValuativeRel

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]

variable (lvl : Level K) [IsDomain lvl.OL] [IsDiscreteValuationRing lvl.OL]

/-- **Residue-field preservation, one tower hop, generic in `lvl : Level K`.** `hgen` is derived
(not assumed) via `Level.natDegree_minpoly_eq_finrank`, fed to
`Level.adjoin_eq_integralClosure_next` for monogenicity, then the elementary quotient argument
(`IsLocalRing.residueFieldEquivOfAdjoinSingleton`, `Langlands/TotallyRamifiedResidueField.lean`)
gives the residue-field isomorphism. See the module docstring above for exactly which
term-duplication removal is what makes this close at default heartbeats. -/
def Level.residueFieldEquiv_next (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    {P : O[X]} (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    (hSplits : letI := lvl.instAlgebraOSelf (O := O);
      (P.divX.map (algebraMap O lvl.L)).Splits)
    {α' : lvl.OL} {v : lvl.OL⟦X⟧} (hv : IsUnit v)
    (heqn : shifted f (lvl.towerHom hOK) α' = (Pn : lvl.OL⟦X⟧) * v)
    (hα'irr : Irreducible α') (hPndist : Pn.IsDistinguishedAt (maximalIdeal lvl.OL))
    (hassoc : Associated (Pn.coeff 0) α') (hdeg : 0 < Pn.natDegree)
    (hα'norm : ‖algebraMap lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn) α'‖ < 1)
    (hirr : Irreducible (Pn.map (algebraMap lvl.OL lvl.L)))
    {β : baseChangeSplittingField (K' := lvl.L) Pn}
    (hβroot : Polynomial.aeval β (Pn.map (algebraMap lvl.OL lvl.L)) = 0)
    [CharZero K]
    [IsLocalRing ↥(integralClosure lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn))]
    [IsLocalHom (algebraMap lvl.OL ↥(integralClosure lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn)))] :
    letI := lvl.instAlgebraO Pn hOK
    ResidueField lvl.OL ≃+* ResidueField ↥(integralClosure lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn)) := by
  letI := lvl.algL
  letI := lvl.finiteDim
  letI := lvl.instAlgebraO Pn hOK
  have hgen : (minpoly lvl.L β).natDegree = Module.finrank lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) :=
    lvl.natDegree_minpoly_eq_finrank Pn hOK hnormL hπ hπnorm hf hu heq hPdist hPdeg hSplits hv heqn
      hα'irr hPndist hassoc hdeg hα'norm hβroot
  have hadjL := lvl.adjoin_eq_integralClosure_next Pn hα'irr hPndist hassoc hirr hβroot hgen
  have hβroot' : Polynomial.aeval β Pn = 0 := by
    have h1 : Polynomial.aeval β (Polynomial.map (algebraMap lvl.OL lvl.L) Pn) = 0 := hβroot
    rwa [Polynomial.aeval_map_algebraMap] at h1
  have hβint : IsIntegral lvl.OL β := ⟨Pn, hPndist.monic, hβroot'⟩
  have hadjS := Algebra.adjoin_singleton_eq_top_of_adjoin_eq_integralClosure hβint hadjL
  have hβmem := mem_maximalIdeal_of_isDistinguishedAt_root
    (R := lvl.OL) (L := baseChangeSplittingField (K' := lvl.L) Pn) hPndist hβint hβroot'
  exact IsLocalRing.residueFieldEquivOfAdjoinSingleton hβmem hadjS

end LubinTate

end
