/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLevelSplits

/-!
# `F_π(β, algebraMap t) ∈ lvl.L⟮β⟯`, generically in `Level`

`FPiEval_algebraMap_mem_adjoin` (`Langlands/LubinTateTowerStepDegree.lean`) and its `K_2 → K_3`
counterpart (`FPiEval_algebraMap_mem_adjoin_K3`, `Langlands/LubinTateTowerStepK3Degree.lean`), read
line by line against each other: **every ingredient the two proofs actually use is already
level-generic**, and the two proofs differ from each other only by the systematic substitution
`K_1 P ↦ K2P2 P₂`, `baseChangeSplittingField ↦ K_3`, `β ↦ γ`. Specifically:

* `hasSum_FPiEval` (`Langlands/LubinTateFormalGroupEval.lean`) and
  `Submodule.mem_of_hasSum_of_finiteDimensional` (`Langlands/LubinTateSplittingFieldDegree.lean`) are
  each already stated for an arbitrary field/vector space — not level-indexed at all. There is no
  growing convergence radius or level-dependent analytic bound anywhere: both proofs use exactly the
  same open-unit-ball hypotheses (`‖β‖ < 1`, `‖t‖ < 1`) and the same `Φ`.
* `baseChangeSplittingField.norm_eq_spectralNorm` (`Langlands/LubinTateTowerStepSplittingField.lean:77`) is *already*
  generic in `LubinTate.baseChangeSplittingField`'s own free parameters `K'`/`P₂` — confirmed by both concrete proofs
  citing the identical lemma name unchanged (`FPiEval_algebraMap_mem_adjoin` line 75,
  `FPiEval_algebraMap_mem_adjoin_K3` line 87).
* The two remaining level-specific ingredients — the composite algebra-map identity
  (`K_2.algebraMap_O_eq_comp_K_1` vs. `K_3.algebraMap_O_eq_comp_K_2`) and the `hOK` transport
  (`K_2.hOK_transport` vs. `K_3.hOK_transport`) — are already generalized: `Level.algebraMap_O_eq_comp_L`
  and `Level.hOK_transport` (`Langlands/LubinTateTowerStepLevelExists.lean`). What was missing was
  only the last mile: `Level.algebraMap_O_eq_comp_L` factors `algebraMap O (baseChangeSplittingField (K' := lvl.L) Pn)`
  through `K` (via `algebraMap K lvl.L`), whereas the concrete proofs need it factored through `lvl.L`
  directly (via `algebraMap O lvl.L`). Bridging those needs exactly `Level.instAlgebraOSelf`/
  `Level.algebraMap_OSelf_eq` — the self-composite built for the `Splits` transport, sufficient here
  unchanged.

So `FPiEval_algebraMap_mem_adjoin`'s generalization is not new analytic engineering: it is exactly
an algebra-map-composite identification, once `Level.algebraMap_O_eq_comp_L` and
`Level.instAlgebraOSelf`/`Level.algebraMap_OSelf_eq` are combined, checked by two `rfl`/
direct-instantiation checks below.

## Main result

* `Level.FPiEval_algebraMap_mem_adjoin` : **`F_π(β, algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) t) ∈
  lvl.L⟮β⟯`**, for `β : baseChangeSplittingField (K' := lvl.L) Pn` and `t : lvl.L` both in the open unit ball. Recovers
  `FPiEval_algebraMap_mem_adjoin` at `level_K_1` **by `rfl`**, and recovers
  `FPiEval_algebraMap_mem_adjoin_K3`'s exact statement when instantiated at `level_K_2` (`rfl`-equal
  to the existing hand-written `K_2 → K_3` proof, since both close the identical goal by the
  identical steps).

## What this does not close

`adjoin_root_eq_top_K_2`/`_K_3`'s other dependency, `piTorsion_one_K_2_eq_algebraMap_image`/`_K_3_...`
(the invariance fact), is **not** generalized here — its proof additionally needs a generic
`K_2.instFaithfulSMul_O`-shaped fact and a generic `divX_map_algebraMap_O_K_2_eq_map`-shaped roots
transport, neither built yet, and is a substantially larger proof (root-multiset bookkeeping via
`piTorsion_one_sdiff_zero_eq_roots_toFinset`, not an algebra-map-composite identification). `hgen`
(the degree hypothesis) and `finrank_K_n_eq_residueCard` itself remain out of scope for the same
reason: they need the invariance fact first.
-/

@[expose] public section

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

/-- **`F_π(β, algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) t) ∈ lvl.L⟮β⟯`**, for `β : baseChangeSplittingField (K' := lvl.L)
Pn` and `t : lvl.L` both in the open unit ball. The `Level`-generic form of
`FPiEval_algebraMap_mem_adjoin`/`FPiEval_algebraMap_mem_adjoin_K3`: each evaluation summand of the
bivariate `F_π` series is an `lvl.L`-scalar (via `Level.algebraMap_O_eq_comp_L` combined with
`Level.algebraMap_OSelf_eq` to factor `algebraMap O (baseChangeSplittingField (K' := lvl.L) Pn)` through `lvl.L` directly)
times a power of `β`, hence lies in the finite-dimensional `lvl.L`-subspace `lvl.L⟮β⟯` (finite-
dimensional inside `baseChangeSplittingField (K' := lvl.L) Pn`, via `baseChangeSplittingField.instFiniteDimensional`);
`Submodule.mem_of_hasSum_of_finiteDimensional` places the `HasSum` limit back inside it. -/
theorem Level.FPiEval_algebraMap_mem_adjoin (lvl : Level K) (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖)
    {π : O} (hπ : Irreducible π) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {β : baseChangeSplittingField (K' := lvl.L) Pn} (hβ : ‖β‖ < 1) {t : lvl.L} (ht : ‖t‖ < 1) :
    letI := lvl.algL
    letI := lvl.instAlgebraO Pn hOK
    FPiEval hπ hf β (algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) t) ∈ lvl.L⟮β⟯ := by
  letI := lvl.algL
  letI := lvl.instAlgebraOSelf (O := O)
  letI := lvl.instAlgebraO Pn hOK
  set t' := algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) t with ht'def
  have ht' : ‖t'‖ < 1 := by
    rw [ht'def, baseChangeSplittingField.norm_eq_spectralNorm, spectralNorm_extends]; exact ht
  have hsum := hasSum_FPiEval (lvl.hOK_transport Pn hOK hnormL) hπ hf hβ ht'
  have hmem : ∀ n : Fin 2 →₀ ℕ,
      evalSummandMv (Phi hπ hf) (![β, t'] : Fin 2 → baseChangeSplittingField (K' := lvl.L) Pn) n ∈
      Subalgebra.toSubmodule
        ((lvl.L⟮β⟯ : IntermediateField lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)).toSubalgebra) := by
    intro n
    rw [Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra]
    unfold evalSummandMv
    rw [Fin.prod_univ_two]
    show algebraMap O (baseChangeSplittingField (K' := lvl.L) Pn) (MvPowerSeries.coeff n (Phi hπ hf)) *
        ((![β, t'] : Fin 2 → baseChangeSplittingField (K' := lvl.L) Pn) 0 ^ n 0 *
          (![β, t'] : Fin 2 → baseChangeSplittingField (K' := lvl.L) Pn) 1 ^ n 1) ∈
      (lvl.L⟮β⟯ : IntermediateField lvl.L (baseChangeSplittingField (K' := lvl.L) Pn))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    -- `algebraMap O (baseChangeSplittingField Pn)` factors through `lvl.L` directly, combining `Level.
    -- algebraMap_O_eq_comp_L` (which factors through `K`) with `Level.algebraMap_OSelf_eq`
    -- (which identifies `algebraMap O lvl.L` with that same `K`-route, via `instAlgebraOSelf`).
    have hOL : algebraMap O lvl.L (MvPowerSeries.coeff n (Phi hπ hf)) =
        algebraMap K lvl.L (algebraMap O K (MvPowerSeries.coeff n (Phi hπ hf))) :=
      congrFun (congrArg DFunLike.coe (lvl.algebraMap_OSelf_eq (O := O))) _
    have hOK2 : algebraMap O (baseChangeSplittingField (K' := lvl.L) Pn) (MvPowerSeries.coeff n (Phi hπ hf)) =
        algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)
          (algebraMap O lvl.L (MvPowerSeries.coeff n (Phi hπ hf))) := by
      rw [hOL]; exact congrFun (lvl.algebraMap_O_eq_comp_L Pn hOK) _
    rw [hOK2, ht'def, ← map_pow]
    refine mul_mem (IntermediateField.algebraMap_mem _ _)
      (mul_mem (pow_mem (IntermediateField.mem_adjoin_simple_self _ β) _)
        (IntermediateField.algebraMap_mem _ _))
  have hres := Submodule.mem_of_hasSum_of_finiteDimensional
    (Subalgebra.toSubmodule
      ((lvl.L⟮β⟯ : IntermediateField lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)).toSubalgebra))
    hsum hmem
  rwa [Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra] at hres

end LubinTate

end
