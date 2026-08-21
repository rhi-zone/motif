/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepSplittingField

/-!
# `K`'s norm transports to `nextSplittingField` unchanged, at the *base* field (not the outer ring `O`)

`Langlands/LubinTateTowerStepSplittingField.lean`'s `K_2.hOK_transport` transports the *outer ring*
`O`'s norm bound (`hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1`) down to `nextSplittingField`. This file proves the
different, stronger fact needed to instantiate the base-relative general theorems of
`Langlands/LubinTateSplittingFieldDVR.lean`/`Langlands/LubinTateTowerStepConcrete.lean`
(`NormedField.isDiscreteValuationRing_valuationSubring_of_finiteDimensional`,
`NormedField.isAdicComplete_integralClosure_of_finiteDimensional`) directly at `L := nextSplittingField`, skipping
the `K_1` hop: **`K`'s own norm (not `O`'s) extends to `nextSplittingField` exactly** (an equality, not merely a
`≤ 1` bound), for elements of `K` itself.

Checked directly against the file this equality was hypothesized to already be sitting in
(`Langlands/LubinTateTowerStepConcrete.lean`, per `ROADMAP.md`'s task framing): no such `K → K_2`
norm-equality fact exists there or anywhere else in this repo prior to this file. What *does* already
exist is `K_2.hOK_transport`, a different fact — a `≤ 1` bound for the outer ring `O`, not a norm
equality for `K` — built for a different purpose (transporting `NonarchimedeanPowerSeriesEval`'s base
ring down the tower), and not reusable here as claimed.

## Main results

* `K_2.instAlgebraK` : `Algebra K (nextSplittingField P₂)`, the explicit two-hop composite `K →(algebraMap)→ K_1 P
  →(algebraMap)→ K_2 P₂` — mirroring `K_2.instAlgebraO`'s three-hop construction one level up, but
  simpler since `K_1` already carries `Algebra K (K_1 P)` directly (no `towerHom`/`hOK` needed).
* `K_2.algebraMap_K_eq` : `algebraMap K (nextSplittingField P₂)` really is that two-hop composite, by `rfl`.
* `K_2.hnorm_K` : **`∀ x : K, ‖algebraMap K (nextSplittingField P₂) x‖ = ‖x‖`** — the `hnorm` hypothesis
  `NormedField.isDiscreteValuationRing_valuationSubring_of_finiteDimensional`/
  `NormedField.isAdicComplete_integralClosure_of_finiteDimensional` need, instantiated directly at
  `L := nextSplittingField P₂`. Two applications of `spectralNorm_extends` chained through the two-hop composite:
  first at the `K_1 P → K_2` hop (`spectralNorm_extends` applied to `algebraMap K (K_1 P) x`), then
  at the `K → K_1 P` hop (`K_1.norm_eq_spectralNorm`, `spectralNorm_extends`) — exactly the same
  two-step pattern `K_1.hOK_transport`/`K_2.hOK_transport` already use, just for `K`'s own norm
  instead of `O`'s bound.
-/

noncomputable section

open scoped Polynomial

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Algebra O K] [IsFractionRing O K]
variable {P : O[X]} (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X])

/-- **`Algebra K (nextSplittingField P₂)`**, the explicit two-hop composite `K → K_1 P → K_2 P₂`. Mirrors
`K_2.instAlgebraO` one level down: `K_1` already carries `Algebra K (K_1 P)` directly
(`K_1.instAlgebra`), so no `towerHom`/`hOK` detour is needed. -/
@[reducible] def K_2.instAlgebraK :
    Algebra K (nextSplittingField (K' := K_1 (K := K) P) P₂) :=
  ((algebraMap (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂)).comp
    (algebraMap K (K_1 (K := K) P))).toAlgebra

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [IsUltrametricDist K] [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] [IsFractionRing O K] in
/-- **`algebraMap K (nextSplittingField P₂)` really is the two-hop composite** — true by definition of
`K_2.instAlgebraK`. -/
theorem K_2.algebraMap_K_eq :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    ⇑(algebraMap K (nextSplittingField (K' := K_1 (K := K) P) P₂)) =
      ⇑(algebraMap (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂)) ∘
        ⇑(algebraMap K (K_1 (K := K) P)) := rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [(NormedField.valuation (K := K)).Compatible]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] [IsFractionRing O K] in
/-- **`K`'s own norm extends to `nextSplittingField` exactly**, for elements of `K` itself — the `hnorm` hypothesis
the base-relative general theorems of `Langlands/LubinTateSplittingFieldDVR.lean`/
`Langlands/LubinTateTowerStepConcrete.lean` need, instantiated directly at `L := nextSplittingField P₂`, skipping the
`K_1` hop. Two applications of `spectralNorm_extends`, chained through `K_2.algebraMap_K_eq`. -/
theorem K_2.hnorm_K :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    ∀ x : K, ‖algebraMap K (nextSplittingField (K' := K_1 (K := K) P) P₂) x‖ = ‖x‖ := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  intro x
  have hcoe : algebraMap K (nextSplittingField (K' := K_1 (K := K) P) P₂) x =
      algebraMap (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂)
        (algebraMap K (K_1 (K := K) P) x) :=
    congrFun (K_2.algebraMap_K_eq (K := K) (P := P) P₂) x
  rw [nextSplittingField.norm_eq_spectralNorm, hcoe, spectralNorm_extends, K_1.norm_eq_spectralNorm,
    spectralNorm_extends]

end LubinTate

end
