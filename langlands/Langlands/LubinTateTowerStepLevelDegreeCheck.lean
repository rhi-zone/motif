/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLevelDegree
import Langlands.LubinTateTowerStepDegree
import Langlands.LubinTateTowerStepK3Degree

/-!
# Concrete `rfl`-checks for `Level.FPiEval_algebraMap_mem_adjoin`, against `LevelDegree.lean`

Split out of `Langlands/LubinTateTowerStepLevelDegree.lean` (`ROADMAP.md §100`), for the same reason
as `LubinTateTowerStepLevelExistsCheck.lean`: checking `Level.FPiEval_algebraMap_mem_adjoin` against
the real hand-named `FPiEval_algebraMap_mem_adjoin`/`FPiEval_algebraMap_mem_adjoin_K3` needs to
import `LubinTateTowerStepDegree.lean`/`LubinTateTowerStepK3Degree.lean` directly, and
`LevelDegree.lean` sits in the import closure of every downstream `Level*.lean` file (via
`LevelInvariance`), so keeping those imports there would put `LubinTateTowerStepK3Degree.lean` back
in that closure for no reason but housing checks.

## Main results

Unchanged from `LevelDegree.lean`'s own former two `example`s: `Level.FPiEval_algebraMap_mem_adjoin`,
instantiated at `level_K_1`/`level_K_2`, is `rfl`-equal to `FPiEval_algebraMap_mem_adjoin`/
`FPiEval_algebraMap_mem_adjoin_K3`.
-/

noncomputable section

open scoped Polynomial IntermediateField

namespace LubinTate

open IsLocalRing PowerSeries Polynomial NonarchimedeanPowerSeriesEval
open NonarchimedeanMvPowerSeriesEvalFin2

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- **`K_1 → K_2`, `rfl`-recovery.** The generic lemma, applied at `level_K_1`, types exactly as
`FPiEval_algebraMap_mem_adjoin`'s own statement, and the two fully-applied proof terms are
`rfl`-equal (proof irrelevance witnessing the two *statements* elaborate to the same `Prop`). -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f)
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂} (hβ : ‖β‖ < 1) {t : K_1 (K := K) P} (ht : ‖t‖ < 1) :
    Level.FPiEval_algebraMap_mem_adjoin (level_K_1 (K := K) (P := P)) P₂ hOK
        (hnorm_K_K_1 (K := K) (P := P)) hπ hf hβ ht =
      FPiEval_algebraMap_mem_adjoin hOK hπ hf hβ ht := rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- **`K_2 → K_3`, `rfl`-recovery.** The generic lemma, applied at `level_K_2`, types exactly as
`FPiEval_algebraMap_mem_adjoin_K3`'s own statement (`Langlands/LubinTateTowerStepK3Degree.lean`),
and the two proof terms are `rfl`-equal. -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]
    (P₃ : (O_K2 (K := K) P₂)[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃} (hγ : ‖γ‖ < 1)
    {t : K2P2 (K := K) P₂} (ht : ‖t‖ < 1) :
    Level.FPiEval_algebraMap_mem_adjoin (level_K_2 (K := K) (P := P) P₂) P₃ hOK
        (hnorm_K_K_2 (K := K) (P := P) P₂) hπ hf hγ ht =
      FPiEval_algebraMap_mem_adjoin_K3 (K := K) (P := P) P₂ P₃ hOK hπ hf hγ ht := rfl


end LubinTate

end
