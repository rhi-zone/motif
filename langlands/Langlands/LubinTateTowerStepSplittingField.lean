/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepConcrete
import Langlands.NonarchimedeanPowerSeriesEvalMap

/-!
# `nextSplittingField` carries the same `NormedField`/`Algebra O` package `K_1` does

`ROADMAP.md` §51's item 5/6 prerequisite: `LubinTate.nextSplittingField` (`Langlands/LubinTateTowerStepConcrete.lean`)
is so far only a bare `Field`/`Algebra K_1`/`IsSplittingField`. `piTorsion`, `FPiEval`, and `eval`
(`Langlands.NonarchimedeanPowerSeriesEval`) all need `[NormedField nextSplittingField] [IsUltrametricDist nextSplittingField]
[CompleteSpace nextSplittingField] [Algebra O nextSplittingField]` before they even typecheck at `K := nextSplittingField`. This file supplies
that package, by the *same* `spectralNorm` route `Langlands/LubinTateSplittingField.lean` used for
`K_1` relative to `K` — but stated **generically for `LubinTate.nextSplittingField`'s own two free parameters**
(`O'`, `K'`), not hardcoded to the concrete `O' := O_{K_1}`, `K' := K_1 P` instantiation. Since
`LubinTate.nextSplittingField`'s definition already has this shape (it is literally "the general one-step splitting
field construction", reused at level 2), the norm-extension package proved here is reusable verbatim
at the *next* tower step (`K_3`, splitting field of a degree-`q` Eisenstein polynomial over `O_{K_2}`)
without modification — this is the "same pattern" `LubinTateTowerStep.lean`'s docstring names as what
a `K_3` step would need.

## Main results

* `nextSplittingField.instNontriviallyNormedField` / `nextSplittingField.instIsUltrametricDist` / `nextSplittingField.instCompleteSpace` /
  `nextSplittingField.instNormedSpace` : the generic `spectralNorm`-based instance package, exactly mirroring
  `K_1`'s own (`Langlands/LubinTateSplittingField.lean`), for *any* base field `K'` with the required
  norm structure and *any* `P₂ : O'[X]`.
* `K_2.instAlgebraO` : `Algebra O (nextSplittingField P₂)`, built as the explicit three-hop composite
  `O →(towerHom hOK P)→ O_{K_1} ↪ K_1 P →(algebraMap)→ K_2 P₂` — **not** via whatever
  `Algebra O_{K_1} (nextSplittingField P₂)` instance ordinary instance search happens to manufacture for
  `LubinTate.nextSplittingField`'s underlying `Polynomial.SplittingField` (checked directly: such an instance *does*
  get found automatically, but is not defeq to the honest tower composite, so cannot be used to prove
  norm transport by `rw [spectralNorm_extends]`). This choice makes `algebraMap O (nextSplittingField P₂)` equal that
  three-hop composite **true by definition** (`K_2.algebraMap_O_eq`, `rfl`), which is exactly the
  hypothesis `NonarchimedeanPowerSeriesEval.eval_map` needs to identify `eval (f.map (towerHom hOK P))
  β` with `eval f β` — the eval-naturality-under-base-change fact `ROADMAP.md` §51 flagged as needed
  and not yet built.
* `K_2.hOK_transport` : `K`'s standing norm hypothesis transports down to `nextSplittingField` unchanged, by
  `spectralNorm_extends` at the `K_1 P → K_2` hop, composed with `norm_le_one_of_mem_integralClosure`
  at the `O_{K_1} → K_1 P` hop.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace LubinTate

open IsLocalRing PowerSeries Polynomial

/-! ## The generic `spectralNorm` package for `LubinTate.nextSplittingField`'s own two free parameters -/

section NormExtension

variable {O' : Type*} [CommRing O']
variable {K' : Type*} [NontriviallyNormedField K'] [IsUltrametricDist K'] [CompleteSpace K']
  [Algebra O' K']
variable (P₂ : O'[X])

instance nextSplittingField.instFiniteDimensional : FiniteDimensional K' (nextSplittingField (K' := K') P₂) :=
  inferInstanceAs (FiniteDimensional K' (P₂.map (algebraMap O' K')).SplittingField)

instance nextSplittingField.instIsAlgebraic : Algebra.IsAlgebraic K' (nextSplittingField (K' := K') P₂) :=
  Algebra.IsAlgebraic.of_finite K' (nextSplittingField (K' := K') P₂)

/-- **The extended norm on `nextSplittingField`**, `spectralNorm K' nextSplittingField` made into an actual
`NontriviallyNormedField` structure — the exact analogue of `K_1.instNontriviallyNormedField`, one
level up and with the base field left as a free parameter `K'` rather than fixed to this arc's `K`. -/
instance nextSplittingField.instNontriviallyNormedField : NontriviallyNormedField (nextSplittingField (K' := K') P₂) :=
  spectralNorm.nontriviallyNormedField K' (nextSplittingField (K' := K') P₂)

/-- **`nextSplittingField`'s norm is literally `spectralNorm K' nextSplittingField`** — true by `rfl`. -/
theorem nextSplittingField.norm_eq_spectralNorm (x : nextSplittingField (K' := K') P₂) :
    ‖x‖ = spectralNorm K' (nextSplittingField (K' := K') P₂) x := rfl

instance nextSplittingField.instIsUltrametricDist : IsUltrametricDist (nextSplittingField (K' := K') P₂) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (show IsNonarchimedean (fun x : nextSplittingField (K' := K') P₂ => ‖x‖) from isNonarchimedean_spectralNorm)

instance nextSplittingField.instCompleteSpace : CompleteSpace (nextSplittingField (K' := K') P₂) :=
  spectralNorm.completeSpace K' (nextSplittingField (K' := K') P₂)

instance nextSplittingField.instNormedSpace : NormedSpace K' (nextSplittingField (K' := K') P₂) :=
  spectralNorm.normedSpace K' (nextSplittingField (K' := K') P₂)

end NormExtension

/-! ## A norm bound for elements of an integral closure, extracted for reuse -/

section IntegralClosureNormBound

/-- **An element of `integralClosure 𝒪[K'] L`, viewed in `L`, has norm at most `1`** — the
extraction of the `hAeq` step inside
`NormedField.isAdicComplete_integralClosure_of_finiteDimensional`'s proof
(`Langlands/LubinTateTowerStepConcrete.lean`) as a standalone, reusable fact: the extended norm's
closed unit ball on `L` and `LocalField.integralClosureValuationSubring 𝒪[K'] L` are the same
`ValuationSubring` (`LocalField.valuationSubring_eq_of_comap_eq`, since both comap to `𝒪[K']` along
`algebraMap K' L`), and `↥(integralClosureValuationSubring 𝒪[K'] L)` is definitionally
`↥(integralClosure 𝒪[K'] L)`. -/
theorem norm_le_one_of_mem_integralClosure
    {K' : Type*} [NontriviallyNormedField K'] [IsUltrametricDist K'] [ValuativeRel K']
    [(NormedField.valuation (K := K')).Compatible] [CompleteSpace K']
    [IsDiscreteValuationRing ↥(ValuativeRel.valuation K').valuationSubring]
    {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [Algebra K' L]
    [FiniteDimensional K' L]
    (hnorm : ∀ x : K', ‖algebraMap K' L x‖ = ‖x‖)
    (y : ↥(integralClosure ↥(ValuativeRel.valuation K').valuationSubring L)) :
    ‖(y : L)‖ ≤ 1 := by
  haveI : Algebra.IsAlgebraic K' L := Algebra.IsAlgebraic.of_finite K' L
  have hcomapA : (NormedField.valuation (K := L)).valuationSubring.comap (algebraMap K' L) =
      (ValuativeRel.valuation K').valuationSubring := by
    have hsub : (ValuativeRel.valuation K').valuationSubring =
        (NormedField.valuation (K := K')).valuationSubring :=
      (Valuation.isEquiv_iff_valuationSubring _ _).mp (ValuativeRel.isEquiv _ _)
    rw [hsub]
    ext x
    have hnn : ‖algebraMap K' L x‖₊ = ‖x‖₊ :=
      NNReal.coe_injective (by rw [coe_nnnorm, coe_nnnorm, hnorm])
    rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
      Valuation.mem_valuationSubring_iff, NormedField.valuation_apply,
      NormedField.valuation_apply, hnn]
  have hcomapI : (LocalField.integralClosureValuationSubring
      ↥(ValuativeRel.valuation K').valuationSubring L).comap (algebraMap K' L) =
      (ValuativeRel.valuation K').valuationSubring :=
    LocalField.comap_integralClosureValuationSubring K' L
  have hAeq : (NormedField.valuation (K := L)).valuationSubring =
      LocalField.integralClosureValuationSubring ↥(ValuativeRel.valuation K').valuationSubring L :=
    LocalField.valuationSubring_eq_of_comap_eq K' hcomapA hcomapI
  have hmem : (y : L) ∈ (NormedField.valuation (K := L)).valuationSubring := by
    rw [hAeq]; exact y.2
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply] at hmem
  exact_mod_cast hmem

end IntegralClosureNormBound

/-! ## The concrete instantiation: `Algebra O (nextSplittingField P₂)` via `towerHom`, and norm transport -/

section Concrete

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Algebra O K] [IsFractionRing O K]
variable {P : O[X]} (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X])

/-- **`Algebra O (nextSplittingField P₂)`**, built as the explicit three-hop composite
`O →(towerHom hOK P)→ O_{K_1} →(algebraMap, the subalgebra inclusion)→ K_1 P →(algebraMap)→ K_2 P₂` —
not via whatever `Algebra O_{K_1} (nextSplittingField P₂)` instance ordinary instance search manufactures directly
for `LubinTate.nextSplittingField`'s underlying `Polynomial.SplittingField` (that instance is *not* defeq to this
composite, so cannot be used to prove norm transport by `rw`). This choice makes
`K_2.algebraMap_O_eq` `rfl`. -/
@[reducible] def K_2.instAlgebraO (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    Algebra O (nextSplittingField (K' := K_1 (K := K) P) P₂) :=
  ((algebraMap (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂)).comp
    ((algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      (K_1 (K := K) P)).comp (towerHom (K := K) hOK P))).toAlgebra

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K]
  [CompleteSpace K] [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] in
/-- **`algebraMap O (nextSplittingField P₂)` really is the three-hop composite** — true by definition of
`K_2.instAlgebraO`, recorded so downstream proofs can rewrite along it. -/
theorem K_2.algebraMap_O_eq (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    ⇑(algebraMap O (nextSplittingField (K' := K_1 (K := K) P) P₂)) =
      ⇑(algebraMap (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂)) ∘
        ⇑(algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (K_1 (K := K) P)) ∘ ⇑(towerHom (K := K) hOK P) := rfl

omit [Finite (ResidueField O)] [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
/-- **`K`'s uniform norm bound (`hOK`) transports down to `nextSplittingField` unchanged.** Chains
`spectralNorm_extends` at the `K_1 P → K_2` hop with `norm_le_one_of_mem_integralClosure` (`≤ 1` for
the image of `towerHom hOK P c`, viewed in `K_1 P`, since it lies in the integral closure `O_{K_1}` by
construction) at the `O_{K_1} → K_1 P` hop. -/
theorem K_2.hOK_transport (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    ∀ c : O, ‖algebraMap O (nextSplittingField (K' := K_1 (K := K) P) P₂) c‖ ≤ 1 := by
  intro c
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  have hcoe : algebraMap O (nextSplittingField (K' := K_1 (K := K) P) P₂) c =
      algebraMap (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂)
        (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (K_1 (K := K) P) (towerHom (K := K) hOK P c)) :=
    congrFun (K_2.algebraMap_O_eq (K := K) (P := P) P₂ hOK) c
  rw [nextSplittingField.norm_eq_spectralNorm, hcoe, spectralNorm_extends]
  have hnorm : ∀ x : K, ‖algebraMap K (K_1 (K := K) P) x‖ = ‖x‖ := fun x => by
    rw [K_1.norm_eq_spectralNorm, spectralNorm_extends]
  exact norm_le_one_of_mem_integralClosure hnorm (towerHom (K := K) hOK P c)

omit [Finite (ResidueField O)] [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] in
/-- **The naturality corollary this file exists for**: `eval (f.map (towerHom hOK P)) β` (evaluated
over `nextSplittingField` at `Algebra O_{K_1} nextSplittingField`) equals `eval f β` (evaluated over `nextSplittingField` at the composite
`Algebra O nextSplittingField` of `K_2.instAlgebraO`). Immediate from `K_2.algebraMap_O_eq` (`rfl`) via
`NonarchimedeanPowerSeriesEval.eval_map` — no convergence argument is needed, since `eval_map` is a
termwise identity between two `tsum`s with definitionally-equal summands. -/
theorem eval_map_towerHom (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {f : O⟦X⟧}
    (β : nextSplittingField (K' := K_1 (K := K) P) P₂) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    NonarchimedeanPowerSeriesEval.eval (PowerSeries.map (towerHom (K := K) hOK P) f) β =
      NonarchimedeanPowerSeriesEval.eval f β := by
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  exact NonarchimedeanPowerSeriesEval.eval_map (towerHom (K := K) hOK P)
    (fun r => (congrFun (K_2.algebraMap_O_eq (K := K) (P := P) P₂ hOK) r).symm) f β

end Concrete

end LubinTate

end
