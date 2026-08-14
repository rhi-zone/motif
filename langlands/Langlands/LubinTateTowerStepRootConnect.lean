/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepSplittingField
import Langlands.NonarchimedeanPowerSeriesEvalAevalMap
import Langlands.EisensteinRootNorm
import Langlands.LubinTateEisensteinQ

/-!
# Connecting `eval_map_towerHom` to the roots of `P₂`

`ROADMAP.md` §52's item 5 needs, precisely: turning "`β` is a root of `P₂`'s image" (stated, as in
`exists_finrank_adjoin_eq_residueCard_K_2`, via the *polynomial* route through `K_1 P`,
`Polynomial.aeval β (P₂.map (algebraMap O_{K_1} (K_1 P))) = 0`) into "`eval f β = algebraMap (K_1
P) K_2 α`" (an equation about the *power-series* `eval`, directly against the original base `O`,
matching what `Langlands.LubinTateRootTranslation`'s generic translation machinery
(`eval_f_FPiEval`, `sub_mem_piTorsion_one_of_eval_f_eq`) needs to be instantiated at `K := K_2`).

This file closes that connection, in two steps:

* `norm_lt_one_of_aeval_P₂_eq_zero` : a root of `P₂`'s image lies in the open unit ball of `K_2`.
  Via `Langlands.EisensteinRootNorm`'s ultrametric-only Eisenstein-polygon computation (no
  irreducibility needed, so it applies inside `K_2`, where `P₂`'s image is *not* irreducible) fed
  the norm data `exists_eisenstein_tower_step_K_1`'s `IsDistinguishedAt`/`Associated (P₂.coeff 0)
  α'` output transports to, via `Langlands.LubinTateEisensteinQ.norm_coeff_map_of_
  isWeaklyEisensteinAt_associated`.
* `eval_f_eq_of_aeval_P₂_eq_zero` : the connecting identity itself. Chains the Weierstrass
  factorization `shifted f ψ α' = (P₂ : _⟦X⟧) * u₂` through `eval` (`eval_mul`, `eval_sub`,
  `eval_C`, using the norm bound above to discharge their `‖β‖ < 1` hypothesis and
  `K_2.norm_le_one_of_mem_O_K1` for their coefficient-bound hypotheses), then `eval_map_towerHom`
  to land on `eval f β` itself.

## What this does not do

This file does not instantiate `eval_f_FPiEval`/`sub_mem_piTorsion_one_of_eval_f_eq` at `K := K_2`
(item 5's well-definedness/injectivity/transitivity), and does not touch item 6. See `ROADMAP.md`
for the precise state of both.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace LubinTate

open IsLocalRing PowerSeries Polynomial NonarchimedeanPowerSeriesEval

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Algebra O K] [IsFractionRing O K]
variable {π : O} {f : O⟦X⟧} {P : O[X]}

/-! ## `O_{K_1}`'s image in `K_2` lands in the closed unit ball -/

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **Every element of `O_{K_1}`, algebra-mapped into `K_2` (via whichever `Algebra O_{K_1} K_2`
instance ordinary instance search finds — the same one `eval_map_towerHom`'s naturality corollary
uses), has norm at most `1`.** Unlike `K_2.hOK_transport` (which only bounds the image of
`towerHom hOK P c` for `c : O`), this bounds *every* element of `O_{K_1}` directly: `O_{K_1} :=
integralClosure ↥𝒪[K] (K_1 P)`, so `norm_le_one_of_mem_integralClosure` applies to an arbitrary
element of it, with `K'` at the *original* base `K` (not `K_1 P`) — the same `hnorm` witness
`K_2.hOK_transport` already builds inline. -/
theorem K_2.norm_le_one_of_mem_O_K1 {P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X]}
    (c : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))) :
    ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) c‖ ≤ 1 := by
  have heq : algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) (K_2 (K' := K_1 (K := K) P) P₂) c =
      algebraMap (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂)
        (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (K_1 (K := K) P) c) :=
    IsScalarTower.algebraMap_apply _ _ _ c
  rw [K_2.norm_eq_spectralNorm, heq, spectralNorm_extends]
  exact norm_le_one_of_mem_integralClosure
    (fun x => by rw [K_1.norm_eq_spectralNorm, spectralNorm_extends]) c

/-- **`algebraMap O_{K_1} K_2` is injective.** Factors as the injective field embedding `K_1 P →
K_2` composed with the injective subring inclusion `O_{K_1} → K_1 P` (`Subtype.coe_injective`,
since `O_{K_1}`'s algebra structure is the subalgebra one). -/
instance K_2.instFaithfulSMul_O_K1 {P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X]} :
    FaithfulSMul ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (K_2 (K' := K_1 (K := K) P) P₂) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have heq : ⇑(algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) (K_2 (K' := K_1 (K := K) P) P₂)) =
      ⇑(algebraMap (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂)) ∘
        ⇑(algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (K_1 (K := K) P)) :=
    funext fun c => IsScalarTower.algebraMap_apply _ _ _ c
  rw [heq]
  exact (algebraMap (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂)).injective.comp
    Subtype.coe_injective

/-! ## The connecting identity -/

variable {P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X]}
  {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
  {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))⟦X⟧}

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **A root of `P₂`'s image (via the `K_1 P` polynomial route) lies in `K_2`'s open unit ball.**
Via `Langlands.EisensteinRootNorm`'s ultrametric-only Eisenstein-polygon computation — no
irreducibility over a base field is needed, so this applies inside `K_2` itself, where `P₂`'s image
is *not* irreducible. `norm_coeff_map_of_isWeaklyEisensteinAt_associated`
(`Langlands.LubinTateEisensteinQ`) transports `P₂`'s `O_{K_1}`-level Eisenstein data
(`hP₂dist`/`hassoc`, `exists_eisenstein_tower_step_K_1`'s extra output) to the norm-bound shape
`Polynomial.norm_lt_one_of_isEisensteinShape_of_root` needs. `hα'norm` (`‖α'‖ < 1` in `K_2`) is
carried as an explicit hypothesis, matching the standing `hπnorm`-style convention this whole arc
uses at level `1` (never derived from irreducibility alone for an abstract base). -/
theorem norm_lt_one_of_aeval_P₂_eq_zero (hα'irr : Irreducible α')
    (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _)) (hassoc : Associated (P₂.coeff 0) α')
    (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {β : K_2 (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0) : ‖β‖ < 1 := by
  have hstep : Polynomial.aeval β P₂ = 0 := by
    rw [aeval_map_eq_eval_coe] at hβroot
    rwa [eval_coe_eq_aeval] at hβroot
  obtain ⟨hmonic, hdegeq, hc0, -, hweak⟩ :=
    norm_coeff_map_of_isWeaklyEisensteinAt_associated (K := K_2 (K' := K_1 (K := K) P) P₂)
      K_2.norm_le_one_of_mem_O_K1 hα'irr hP₂dist.monic hP₂dist.toIsWeaklyEisensteinAt hassoc
  refine Polynomial.norm_lt_one_of_isEisensteinShape_of_root hmonic (by rw [hdegeq]; exact hdeg)
    hα'norm hc0 hweak
    (by rw [Polynomial.aeval_def, ← Polynomial.eval_map] at hstep; exact hstep)

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **The connecting identity itself**: for `β` a root of `P₂`'s image, `eval f β` equals `α`
(the level-`1` generator `P₂`'s constant term is built from), algebra-mapped into `K_2` — an
equation about the power-series `eval`, directly against the original base `O` (via
`K_2.instAlgebraO`), matching what `Langlands.LubinTateRootTranslation`'s generic translation
machinery needs to be instantiated at `K := K_2`.

Chains the Weierstrass factorization `shifted f ψ α' = (P₂ : _⟦X⟧) * u₂` through `eval`
(`eval_mul`/`eval_sub`/`eval_C`, using `norm_lt_one_of_aeval_P₂_eq_zero` for their `‖β‖ < 1`
hypothesis and `K_2.norm_le_one_of_mem_O_K1` for their coefficient-bound hypotheses), then
`eval_map_towerHom` to land on `eval f β` itself. -/
theorem eval_f_eq_of_aeval_P₂_eq_zero (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (_hu₂ : IsUnit u₂) (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    {β : K_2 (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    NonarchimedeanPowerSeriesEval.eval f β =
      algebraMap (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂) α := by
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  have hβnorm : ‖β‖ < 1 :=
    norm_lt_one_of_aeval_P₂_eq_zero hα'irr hP₂dist hassoc hdeg hα'norm hβroot
  have hstep0 : NonarchimedeanPowerSeriesEval.eval
      (↑P₂ : PowerSeries ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P))) β = 0 := by
    rw [← aeval_map_eq_eval_coe (K' := K_1 (K := K) P)]; exact hβroot
  have hbP₂ : ∀ n, ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂)
      (PowerSeries.coeff n (↑P₂ : PowerSeries ↥(integralClosure
        ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))))‖ ≤ 1 :=
    fun n ↦ K_2.norm_le_one_of_mem_O_K1 _
  have hbu₂ : ∀ n, ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂)
      (PowerSeries.coeff n u₂)‖ ≤ 1 := fun n ↦ K_2.norm_le_one_of_mem_O_K1 _
  have hshifted0 :
      NonarchimedeanPowerSeriesEval.eval (shifted f (towerHom (K := K) hOK P) α') β = 0 := by
    rw [heq₂, NonarchimedeanPowerSeriesEval.eval_mul hbP₂ hbu₂ hβnorm, hstep0, zero_mul]
  have hbfmap : ∀ n, ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂)
      (PowerSeries.coeff n (PowerSeries.map (towerHom (K := K) hOK P) f))‖ ≤ 1 :=
    fun n ↦ K_2.norm_le_one_of_mem_O_K1 _
  have hbCα' : ∀ n, ‖algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂)
      (PowerSeries.coeff n (PowerSeries.C α'))‖ ≤ 1 := fun n ↦ K_2.norm_le_one_of_mem_O_K1 _
  have hsub :
      NonarchimedeanPowerSeriesEval.eval (PowerSeries.map (towerHom (K := K) hOK P) f) β -
        NonarchimedeanPowerSeriesEval.eval (PowerSeries.C α' : PowerSeries _) β = 0 := by
    rw [← NonarchimedeanPowerSeriesEval.eval_sub hbfmap hbCα' hβnorm]
    exact hshifted0
  rw [NonarchimedeanPowerSeriesEval.eval_C] at hsub
  have hmapeq :
      NonarchimedeanPowerSeriesEval.eval (PowerSeries.map (towerHom (K := K) hOK P) f) β =
        algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) (α' : _) := sub_eq_zero.mp hsub
  rw [eval_map_towerHom (K := K) (P := P) P₂ hOK β] at hmapeq
  have hfinal : algebraMap _ (K_2 (K' := K_1 (K := K) P) P₂) (α' : _) =
      algebraMap (K_1 (K := K) P) (K_2 (K' := K_1 (K := K) P) P₂) α := by
    rw [← hα'coe]
    exact IsScalarTower.algebraMap_apply _ (K_1 (K := K) P) _ α'
  rw [hmapeq, hfinal]

end LubinTate

end
