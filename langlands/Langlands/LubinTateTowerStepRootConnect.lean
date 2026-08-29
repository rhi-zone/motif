/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepSplittingField
import Langlands.NonarchimedeanPowerSeriesEvalAevalMap
import Langlands.EisensteinRootNorm
import Langlands.LubinTateEisensteinQ
import Langlands.LubinTateRootTranslation

/-!
# Connecting `eval_map_towerHom` to the roots of `P₂`

Turning "`β` is a root of `P₂`'s image" (stated, as in
`exists_finrank_adjoin_eq_residueCard_K_2`, via the *polynomial* route through `K_1 P`,
`Polynomial.aeval β (P₂.map (algebraMap O_{K_1} (K_1 P))) = 0`) into "`eval f β = algebraMap (K_1
P) baseChangeSplittingField α`" (an equation about the *power-series* `eval`, directly against the original base `O`,
matching what `Langlands.LubinTateRootTranslation`'s generic translation machinery
(`eval_f_FPiEval`, `sub_mem_piTorsion_one_of_eval_f_eq`) needs to be instantiated at `K := baseChangeSplittingField`).

This file closes that connection, in two steps:

* `norm_lt_one_of_aeval_P₂_eq_zero` : a root of `P₂`'s image lies in the open unit ball of `baseChangeSplittingField`.
  Via `Langlands.EisensteinRootNorm`'s ultrametric-only Eisenstein-polygon computation (no
  irreducibility needed, so it applies inside `baseChangeSplittingField`, where `P₂`'s image is *not* irreducible) fed
  the norm data `exists_eisenstein_tower_step_K_1`'s `IsDistinguishedAt`/`Associated (P₂.coeff 0)
  α'` output transports to, via `Langlands.LubinTateEisensteinQ.norm_coeff_map_of_
  isWeaklyEisensteinAt_associated`.
* `eval_f_eq_of_aeval_P₂_eq_zero` : the connecting identity itself. Chains the Weierstrass
  factorization `shifted f ψ α' = (P₂ : _⟦X⟧) * u₂` through `eval` (`eval_mul`, `eval_sub`,
  `eval_C`, using the norm bound above to discharge their `‖β‖ < 1` hypothesis and
  `K_2.norm_le_one_of_mem_O_K1` for their coefficient-bound hypotheses), then `eval_map_towerHom`
  to land on `eval f β` itself.

Beyond that connection, this file also builds the `O`-algebra composite naturality facts needed to
run the whole `piTorsion`/translation machinery at `K := baseChangeSplittingField` (norm and
injectivity transport for `algebraMap O baseChangeSplittingField`, and the fact that the level-`1`
`π`-torsion does not grow when passing from `K_1 P` to `baseChangeSplittingField`,
`piTorsion_one_K_2_eq_algebraMap_image`). It does not itself instantiate
`eval_f_FPiEval`/`sub_mem_piTorsion_one_of_eval_f_eq` at `K := baseChangeSplittingField`.
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

/-! ## `O_{K_1}`'s image in `baseChangeSplittingField` lands in the closed unit ball -/

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **Every element of `O_{K_1}`, algebra-mapped into `baseChangeSplittingField` (via whichever `Algebra O_{K_1} baseChangeSplittingField`
instance ordinary instance search finds — the same one `eval_map_towerHom`'s naturality corollary
uses), has norm at most `1`.** Unlike `K_2.hOK_transport` (which only bounds the image of
`towerHom hOK P c` for `c : O`), this bounds *every* element of `O_{K_1}` directly: `O_{K_1} :=
integralClosure ↥𝒪[K] (K_1 P)`, so `norm_le_one_of_mem_integralClosure` applies to an arbitrary
element of it, with `K'` at the *original* base `K` (not `K_1 P`) — the same `hnorm` witness
`K_2.hOK_transport` already builds inline. -/
theorem K_2.norm_le_one_of_mem_O_K1 {P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X]}
    (c : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))) :
    ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) c‖ ≤ 1 := by
  have heq : algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) c =
      algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)
        (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (K_1 (K := K) P) c) :=
    IsScalarTower.algebraMap_apply _ _ _ c
  rw [baseChangeSplittingField.norm_eq_spectralNorm, heq, spectralNorm_extends]
  exact norm_le_one_of_mem_integralClosure
    (fun x => by rw [K_1.norm_eq_spectralNorm, spectralNorm_extends]) c

/-- **`algebraMap O_{K_1} baseChangeSplittingField` is injective.** Factors as the injective field embedding `K_1 P →
baseChangeSplittingField` composed with the injective subring inclusion `O_{K_1} → K_1 P` (`Subtype.coe_injective`,
since `O_{K_1}`'s algebra structure is the subalgebra one). -/
instance K_2.instFaithfulSMul_O_K1 {P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X]} :
    FaithfulSMul ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have heq : ⇑(algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)) =
      ⇑(algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)) ∘
        ⇑(algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (K_1 (K := K) P)) :=
    funext fun c => IsScalarTower.algebraMap_apply _ _ _ c
  rw [heq]
  exact (algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)).injective.comp
    Subtype.coe_injective

/-! ## The connecting identity -/

variable {P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X]}
  {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
  {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))⟦X⟧}

/-- **`‖α'‖ < 1` in `baseChangeSplittingField`, discharged from the standing hypothesis set.** `exists_irreducible_
uniformizer_K_1`'s `hram : ‖(ϖ:K)‖ = spectralNorm K (K_1 P) α ^ (minpoly K α).natDegree` together
with the standing `hπnorm : ‖algebraMap O K π‖ < 1` (via `hϖnorm`) force `‖(ϖ:K)‖ < 1`; since the
exponent `(minpoly K α).natDegree` is positive (`minpoly.natDegree_pos`, `α` integral over `K` as
`K_1 P` is finite-dimensional over `K`), `pow_lt_one_iff_of_nonneg` forces `spectralNorm K (K_1 P) α
< 1`. Transported to `baseChangeSplittingField` by `baseChangeSplittingField.norm_eq_spectralNorm` + `spectralNorm_extends` (the `K_1 P → K_2`
hop) composed with `K_1.norm_eq_spectralNorm` + `spectralNorm_extends` (the `K → K_1 P` hop, run in
reverse) — the same two-hop pattern `K_2.hOK_transport`/`K_2.norm_le_one_of_mem_O_K1` already use —
and `IsScalarTower.algebraMap_apply` to identify `algebraMap _ baseChangeSplittingField α'` with `algebraMap (K_1 P) baseChangeSplittingField
α` via `hα'coe`. -/
theorem hα'norm_lt_one_of_hram (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {ϖ : ↥(ValuativeRel.valuation K).valuationSubring}
    (hϖnorm : ‖(ϖ : K)‖ = ‖algebraMap O K π‖) {α : K_1 (K := K) P}
    (hα : Polynomial.aeval α (P.divX.map (algebraMap O K)) = 0)
    [FiniteDimensional K (K_1 (K := K) P)]
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    (hα'coe : (α' : K_1 (K := K) P) = α)
    {P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))[X]} :
    ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1 := by
  have hram := norm_eq_spectralNorm_pow_natDegree_K_1 hOK hπ hf hu heq hPdist hPdeg hϖnorm hα
  have hϖlt : ‖(ϖ : K)‖ < 1 := by rw [hϖnorm]; exact hπnorm
  rw [hram] at hϖlt
  have hdegpos : 0 < (minpoly K α).natDegree :=
    minpoly.natDegree_pos (IsIntegral.of_finite K α)
  have hspeclt : spectralNorm K (K_1 (K := K) P) α < 1 :=
    (pow_lt_one_iff_of_nonneg (spectralNorm_nonneg α) hdegpos.ne').mp hϖlt
  have hcoe : algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _) =
      algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) α := by
    rw [← hα'coe]
    exact IsScalarTower.algebraMap_apply _ (K_1 (K := K) P) _ α'
  rw [hcoe, baseChangeSplittingField.norm_eq_spectralNorm, spectralNorm_extends, K_1.norm_eq_spectralNorm]
  exact hspeclt

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **A root of `P₂`'s image (via the `K_1 P` polynomial route) lies in `baseChangeSplittingField`'s open unit ball.**
Via `Langlands.EisensteinRootNorm`'s ultrametric-only Eisenstein-polygon computation — no
irreducibility over a base field is needed, so this applies inside `baseChangeSplittingField` itself, where `P₂`'s image
is *not* irreducible. `norm_coeff_map_of_isWeaklyEisensteinAt_associated`
(`Langlands.LubinTateEisensteinQ`) transports `P₂`'s `O_{K_1}`-level Eisenstein data
(`hP₂dist`/`hassoc`, `exists_eisenstein_tower_step_K_1`'s extra output) to the norm-bound shape
`Polynomial.norm_lt_one_of_isEisensteinShape_of_root` needs. `hα'norm` (`‖α'‖ < 1` in `baseChangeSplittingField`) is
carried as an explicit hypothesis, matching the standing `hπnorm`-style convention this whole arc
uses at level `1` (never derived from irreducibility alone for an abstract base). -/
theorem norm_lt_one_of_aeval_P₂_eq_zero (hα'irr : Irreducible α')
    (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _)) (hassoc : Associated (P₂.coeff 0) α')
    (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0) : ‖β‖ < 1 := by
  have hstep : Polynomial.aeval β P₂ = 0 := by
    rw [aeval_map_eq_eval_coe] at hβroot
    rwa [eval_coe_eq_aeval] at hβroot
  obtain ⟨hmonic, hdegeq, hc0, -, hweak⟩ :=
    norm_coeff_map_of_isWeaklyEisensteinAt_associated (K := baseChangeSplittingField (K' := K_1 (K := K) P) P₂)
      K_2.norm_le_one_of_mem_O_K1 hα'irr hP₂dist.monic hP₂dist.toIsWeaklyEisensteinAt hassoc
  refine Polynomial.norm_lt_one_of_isEisensteinShape_of_root hmonic (by rw [hdegeq]; exact hdeg)
    hα'norm hc0 hweak
    (by rw [Polynomial.aeval_def, ← Polynomial.eval_map] at hstep; exact hstep)

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **The connecting identity itself**: for `β` a root of `P₂`'s image, `eval f β` equals `α`
(the level-`1` generator `P₂`'s constant term is built from), algebra-mapped into `baseChangeSplittingField` — an
equation about the power-series `eval`, directly against the original base `O` (via
`K_2.instAlgebraO`), matching what `Langlands.LubinTateRootTranslation`'s generic translation
machinery needs to be instantiated at `K := baseChangeSplittingField`.

Chains the Weierstrass factorization `shifted f ψ α' = (P₂ : _⟦X⟧) * u₂` through `eval`
(`eval_mul`/`eval_sub`/`eval_C`, using `norm_lt_one_of_aeval_P₂_eq_zero` for their `‖β‖ < 1`
hypothesis and `K_2.norm_le_one_of_mem_O_K1` for their coefficient-bound hypotheses), then
`eval_map_towerHom` to land on `eval f β` itself. -/
theorem eval_f_eq_of_aeval_P₂_eq_zero (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (_hu₂ : IsUnit u₂) (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    NonarchimedeanPowerSeriesEval.eval f β =
      algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) α := by
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  have hβnorm : ‖β‖ < 1 :=
    norm_lt_one_of_aeval_P₂_eq_zero hα'irr hP₂dist hassoc hdeg hα'norm hβroot
  have hstep0 : NonarchimedeanPowerSeriesEval.eval
      (↑P₂ : PowerSeries ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P))) β = 0 := by
    rw [← aeval_map_eq_eval_coe (K' := K_1 (K := K) P)]; exact hβroot
  have hbP₂ : ∀ n, ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)
      (PowerSeries.coeff n (↑P₂ : PowerSeries ↥(integralClosure
        ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))))‖ ≤ 1 :=
    fun n ↦ K_2.norm_le_one_of_mem_O_K1 _
  have hbu₂ : ∀ n, ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)
      (PowerSeries.coeff n u₂)‖ ≤ 1 := fun n ↦ K_2.norm_le_one_of_mem_O_K1 _
  have hshifted0 :
      NonarchimedeanPowerSeriesEval.eval (shifted f (towerHom (K := K) hOK P) α') β = 0 := by
    rw [heq₂, NonarchimedeanPowerSeriesEval.eval_mul hbP₂ hbu₂ hβnorm, hstep0, zero_mul]
  have hbfmap : ∀ n, ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)
      (PowerSeries.coeff n (PowerSeries.map (towerHom (K := K) hOK P) f))‖ ≤ 1 :=
    fun n ↦ K_2.norm_le_one_of_mem_O_K1 _
  have hbCα' : ∀ n, ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)
      (PowerSeries.coeff n (PowerSeries.C α'))‖ ≤ 1 := fun n ↦ K_2.norm_le_one_of_mem_O_K1 _
  have hsub :
      NonarchimedeanPowerSeriesEval.eval (PowerSeries.map (towerHom (K := K) hOK P) f) β -
        NonarchimedeanPowerSeriesEval.eval (PowerSeries.C α' : PowerSeries _) β = 0 := by
    rw [← NonarchimedeanPowerSeriesEval.eval_sub hbfmap hbCα' hβnorm]
    exact hshifted0
  rw [NonarchimedeanPowerSeriesEval.eval_C] at hsub
  have hmapeq :
      NonarchimedeanPowerSeriesEval.eval (PowerSeries.map (towerHom (K := K) hOK P) f) β =
        algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _) := sub_eq_zero.mp hsub
  rw [eval_map_towerHom (K := K) (P := P) P₂ hOK β] at hmapeq
  have hfinal : algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _) =
      algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) α := by
    rw [← hα'coe]
    exact IsScalarTower.algebraMap_apply _ (K_1 (K := K) P) _ α'
  rw [hmapeq, hfinal]

/-! ## Transitivity of the translation action on roots of `P₂`'s image -/

/-- **Transitivity of the `piTorsion hπ hf 1` translation action on roots of `P₂`'s image, at `K :=
baseChangeSplittingField`.** For `β, β'` both roots (via the `K_1 P` polynomial route), there is `t' ∈ piTorsion hπ hf 1`
(evaluated inside `baseChangeSplittingField`) with `β' = F_π(β, t')`. Both `eval f β` and `eval f β'` equal `algebraMap
(K_1 P) baseChangeSplittingField α` by `eval_f_eq_of_aeval_P₂_eq_zero` (applied to each root separately), hence to each
other; `Langlands.LubinTateRootTranslation.exists_piTorsion_translate_of_eval_f_eq` (the *generic*
transitivity fact, needing no cardinality-matching) then supplies `t'` directly. No separate
"well-definedness converse" of `eval_f_eq_of_aeval_P₂_eq_zero` is needed: the argument only ever uses
its already-proved forward direction, applied once to each of `β` and `β'`. -/
theorem exists_piTorsion_translate_of_aeval_P₂_eq_zero (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    (_hu₂ : IsUnit u₂) (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    {β β' : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβ'root : Polynomial.aeval β' (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    ∃ t' ∈ piTorsion (K := baseChangeSplittingField (K' := K_1 (K := K) P) P₂) hπ hf 1,
      β' = FPiEval hπ hf β t' := by
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  have h1 := eval_f_eq_of_aeval_P₂_eq_zero hOK _hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe
    hβroot
  have h2 := eval_f_eq_of_aeval_P₂_eq_zero hOK _hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe
    hβ'root
  have hβnorm : ‖β‖ < 1 := norm_lt_one_of_aeval_P₂_eq_zero hα'irr hP₂dist hassoc hdeg hα'norm hβroot
  have hβ'norm : ‖β'‖ < 1 :=
    norm_lt_one_of_aeval_P₂_eq_zero hα'irr hP₂dist hassoc hdeg hα'norm hβ'root
  exact exists_piTorsion_translate_of_eval_f_eq (K_2.hOK_transport (K := K) (P := P) P₂ hOK) hπ hf
    hβnorm hβ'norm (h1.trans h2.symm)

/-! ## `algebraMap O (K_1 P)` agrees with the first two hops of `K_2.instAlgebraO`'s composite -/

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **The ordinary `algebraMap O (K_1 P)` (`K_1.instAlgebraO`'s two-hop `O → K → K_1 P`) equals the
first two hops of `K_2.instAlgebraO`'s three-hop composite**, `algebraMap O_{K_1} (K_1 P) ∘ towerHom
hOK P`. Unlike `K_2.algebraMap_O_eq` (true by `rfl`, since it unfolds `K_2.instAlgebraO`'s own
definition), this is a genuinely different composite through `K` that has to be proved equal, not
merely unfolded: `towerHom hOK P` factors as `algebraMap 𝒪[K] O_{K_1} ∘ toValuationSubring hOK`, so
the right side becomes `algebraMap 𝒪[K] (K_1 P) (toValuationSubring hOK c)`
(`IsScalarTower.algebraMap_apply` at the `𝒪[K] → O_{K_1} → K_1 P` tower, an automatic instance for
`O_{K_1} := integralClosure 𝒪[K] (K_1 P)` as a subalgebra of `K_1 P`); rewriting again along
`IsScalarTower.algebraMap_apply` at the `𝒪[K] → K → K_1 P` tower (also automatic,
`ValuationSubring.instIsScalarTowerSubtypeMemValuationSubringWithZeroMultiplicativeInt` specialized
at the identity algebra `K → K`) reduces this to `algebraMap K (K_1 P) (algebraMap 𝒪[K] K
(toValuationSubring hOK c))`, and `coe_toValuationSubring` identifies the inner term with `algebraMap
O K c`, landing on `algebraMap K (K_1 P) (algebraMap O K c) = algebraMap O (K_1 P) c`
(`K_1.algebraMap_O_eq`, `rfl`). -/
theorem algebraMap_O_K_1_eq_comp_towerHom (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    ⇑(algebraMap O (K_1 (K := K) P)) =
      ⇑(algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) (K_1 (K := K) P)) ∘ ⇑(towerHom (K := K) hOK P) := by
  funext c
  show algebraMap O (K_1 (K := K) P) c =
    algebraMap _ (K_1 (K := K) P) (towerHom (K := K) hOK P c)
  have htower : towerHom (K := K) hOK P c =
      algebraMap ↥(ValuativeRel.valuation K).valuationSubring
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (toValuationSubring (K := K) hOK c) := rfl
  rw [htower, ← IsScalarTower.algebraMap_apply
      ↥(ValuativeRel.valuation K).valuationSubring
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (K_1 (K := K) P),
    IsScalarTower.algebraMap_apply ↥(ValuativeRel.valuation K).valuationSubring K
      (K_1 (K := K) P)]
  rw [show algebraMap ↥(ValuativeRel.valuation K).valuationSubring K
      (toValuationSubring (K := K) hOK c) = algebraMap O K c from
    coe_toValuationSubring (K := K) hOK c]
  exact (congrFun (K_1.algebraMap_O_eq (K := K) P) c).symm

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`K_2.instAlgebraO`'s composite collapses to the ordinary two-hop `algebraMap (K_1 P) baseChangeSplittingField ∘
algebraMap O (K_1 P)`.** Immediate from `K_2.algebraMap_O_eq` (the three-hop composite, `rfl`) and
`algebraMap_O_K_1_eq_comp_towerHom` (the first two hops equal the ordinary `algebraMap O (K_1 P)`).
This is the single fact everything else in this section reduces to: once `algebraMap O baseChangeSplittingField` is
identified with a genuine `K → K_1 P → K_2` tower map, norm transport (`K_2.hπnorm_transport`),
injectivity (`K_2.instFaithfulSMul_O`), and the roots-multiset transport
(`divX_map_algebraMap_O_K_2_eq_map`) all become one-line consequences of the corresponding `K_1 P`
facts. -/
theorem K_2.algebraMap_O_eq_comp_K_1 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    ⇑(algebraMap O (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)) =
      ⇑(algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)) ∘
        ⇑(algebraMap O (K_1 (K := K) P)) := by
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  rw [K_2.algebraMap_O_eq (K := K) (P := P) P₂ hOK, algebraMap_O_K_1_eq_comp_towerHom (K := K) hOK]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`K`'s strict uniformizer bound (`hπnorm`) transports down to `baseChangeSplittingField` unchanged.** The `baseChangeSplittingField`
analogue of `K_1.hπnorm_transport`, via `K_2.algebraMap_O_eq_comp_K_1` and `spectralNorm_extends` at
the `K_1 P → K_2` hop, reducing to the already-transported `K_1.hπnorm_transport` at the `K → K_1 P`
hop. -/
theorem K_2.hπnorm_transport (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπnorm : ‖algebraMap O K π‖ < 1) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    ‖algebraMap O (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) π‖ < 1 := by
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  have hcoe : algebraMap O (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) π =
      algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)
        (algebraMap O (K_1 (K := K) P) π) :=
    congrFun (K_2.algebraMap_O_eq_comp_K_1 (K := K) (P := P) hOK) π
  rw [baseChangeSplittingField.norm_eq_spectralNorm, hcoe, spectralNorm_extends]
  exact K_1.hπnorm_transport (K := K) P hπnorm

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- **`algebraMap O baseChangeSplittingField` is injective.** The composite of `algebraMap O (K_1 P)` (injective,
`K_1.instFaithfulSMul`) and `algebraMap (K_1 P) baseChangeSplittingField` (injective, any ring hom out of a field),
identified via `K_2.algebraMap_O_eq_comp_K_1`. -/
theorem K_2.instFaithfulSMul_O (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    FaithfulSMul O (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) := by
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  rw [faithfulSMul_iff_algebraMap_injective]
  rw [K_2.algebraMap_O_eq_comp_K_1 (K := K) (P := P) hOK]
  exact (algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)).injective.comp
    (FaithfulSMul.algebraMap_injective O (K_1 (K := K) P))

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **`Q := P.divX`'s image over `baseChangeSplittingField` (via `K_2.instAlgebraO`) is `Q`'s image over `K_1 P`, further
mapped along `algebraMap (K_1 P) baseChangeSplittingField`.** `Polynomial.map_map` plus
`K_2.algebraMap_O_eq_comp_K_1` (as a `RingHom` equality, `RingHom.ext`). This is the piece needed to
transport the roots-multiset identity `Polynomial.Monic.roots_map_of_card_eq_natDegree` supplies at
`K_1 P` up to `baseChangeSplittingField`. -/
theorem divX_map_algebraMap_O_K_2_eq_map (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    P.divX.map (algebraMap O (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)) =
      (P.divX.map (algebraMap O (K_1 (K := K) P))).map
        (algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)) := by
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  have hcomp : (algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)).comp
      (algebraMap O (K_1 (K := K) P)) = algebraMap O (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) :=
    RingHom.ext fun c =>
      (congrFun (K_2.algebraMap_O_eq_comp_K_1 (K := K) (P := P) hOK) c).symm
  rw [Polynomial.map_map, hcomp]

/-! ## The `piTorsion hπ hf 1`-invariance of the `K_1 P → K_2` transition -/

/-- **`piTorsion hπ hf 1`, evaluated inside `baseChangeSplittingField`, is exactly the `algebraMap (K_1 P) baseChangeSplittingField`-image of
`piTorsion hπ hf 1` evaluated inside `K_1 P`.** The level-`1` `π`-torsion does not grow when passing
from `K_1 P` to `baseChangeSplittingField`.

Proof: at each of `K := K_1 P` and `K := baseChangeSplittingField`, `piTorsion hπ hf 1 \ {0}` is exactly the root set of
`Q := P.divX`'s image (`piTorsion_one_sdiff_zero_eq_roots_toFinset`). `Q`'s image splits completely
over `K_1 P` by construction (`splits_divX_map_K_1`) and is monic, so `Polynomial.splits_iff_card_
roots` gives `roots.card = natDegree`, and `Polynomial.Monic.roots_map_of_card_eq_natDegree` transports
the roots multiset along `algebraMap (K_1 P) baseChangeSplittingField` onto the roots of the further-mapped polynomial —
which `divX_map_algebraMap_O_K_2_eq_map` identifies with `Q`'s image over `baseChangeSplittingField` itself. Converting the
multiset identity to a `Finset.image` identity (`Multiset.toFinset_map`) and reassembling `{0}`
(`algebraMap` sends `0` to `0`, and `0 ∈ piTorsion hπ hf 1` at both ends) gives the full set
equality. -/
theorem piTorsion_one_K_2_eq_algebraMap_image (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    (piTorsion (K := baseChangeSplittingField (K' := K_1 (K := K) P) P₂) hπ hf 1 : Set (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)) =
      algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) ''
        (piTorsion (K := K_1 (K := K) P) hπ hf 1) := by
  classical
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  letI := K_2.instFaithfulSMul_O (K := K) (P := P) (P₂ := P₂) hOK
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  have hQmonic : (P.divX.map (algebraMap O (K_1 (K := K) P))).Monic :=
    (divX_isWeaklyEisensteinAt_and_associated hu heq hf.1 hf.2.1 hPdist hPdeg2).1.map _
  have hcard : (P.divX.map (algebraMap O (K_1 (K := K) P))).roots.card =
      (P.divX.map (algebraMap O (K_1 (K := K) P))).natDegree :=
    Polynomial.splits_iff_card_roots.mp (splits_divX_map_K_1 (K := K) P)
  have hrootsmap : (P.divX.map (algebraMap O (K_1 (K := K) P))).roots.map
      (algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂)) =
      ((P.divX.map (algebraMap O (K_1 (K := K) P))).map
        (algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂))).roots :=
    hQmonic.roots_map_of_card_eq_natDegree _ hcard
  rw [← divX_map_algebraMap_O_K_2_eq_map (K := K) (P := P) (P₂ := P₂) hOK] at hrootsmap
  have hfinseteq : Finset.image (algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂))
      (P.divX.map (algebraMap O (K_1 (K := K) P))).roots.toFinset =
      (P.divX.map (algebraMap O (baseChangeSplittingField (K' := K_1 (K := K) P) P₂))).roots.toFinset := by
    rw [← Multiset.toFinset_map, hrootsmap]
  have hstep1 := piTorsion_one_sdiff_zero_eq_roots_toFinset (K := K_1 (K := K) P)
    (K_1.hOK_transport P hOK) hπ (K_1.hπnorm_transport P hπnorm) hf hu heq hPdist hPdeg
  have hstep2 := piTorsion_one_sdiff_zero_eq_roots_toFinset
    (K := baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (K_2.hOK_transport (K := K) (P := P) P₂ hOK) hπ
    (K_2.hπnorm_transport (K := K) (P := P) (P₂ := P₂) hOK hπnorm) hf hu heq hPdist hPdeg
  have himageeq :
      algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) ''
        (piTorsion (K := K_1 (K := K) P) hπ hf 1 \ {0}) =
      piTorsion (K := baseChangeSplittingField (K' := K_1 (K := K) P) P₂) hπ hf 1 \ {0} := by
    rw [hstep1, hstep2, ← Finset.coe_image, hfinseteq]
  have h0 : algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) ''
      (piTorsion (K := K_1 (K := K) P) hπ hf 1) =
      insert (algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) 0)
        (algebraMap (K_1 (K := K) P) (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) ''
          (piTorsion (K := K_1 (K := K) P) hπ hf 1 \ {0})) := by
    rw [← Set.image_insert_eq]
    congr 1
    rw [Set.insert_sdiff_singleton]
    exact (Set.insert_eq_self.mpr (zero_mem_piTorsion hπ hf 1)).symm
  rw [h0, himageeq, map_zero, Set.insert_sdiff_singleton]
  exact (Set.insert_eq_self.mpr (zero_mem_piTorsion hπ hf 1)).symm

end LubinTate

end
