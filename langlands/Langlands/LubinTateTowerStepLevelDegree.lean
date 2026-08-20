/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLevelSplits
import Langlands.LubinTateTowerStepDegree
import Langlands.LubinTateTowerStepK3Degree

/-!
# `F_π(β, algebraMap t) ∈ lvl.L⟮β⟯`, generically in `Level`

`ROADMAP.md` §84 named `FPiEval_algebraMap_mem_adjoin` (`Langlands/LubinTateTowerStepDegree.lean`) as
the one piece of the degree/splitting chain not yet generalized over `Level`, and assessed it as "a
real analytic argument ... a genuinely new piece of engineering, not a mechanical substitution".
Reading `FPiEval_algebraMap_mem_adjoin` and its `K_2 → K_3` counterpart
(`FPiEval_algebraMap_mem_adjoin_K3`, `Langlands/LubinTateTowerStepK3Degree.lean`) line by line against
each other finds the opposite: **every ingredient the two proofs actually use is already
level-generic**, and the two proofs differ from each other only by the systematic substitution
`K_1 P ↦ K2P2 P₂`, `K_2 ↦ K_3`, `β ↦ γ`. Specifically:

* `hasSum_FPiEval` (`Langlands/LubinTateFormalGroupEval.lean`) and
  `Submodule.mem_of_hasSum_of_finiteDimensional` (`Langlands/LubinTateSplittingFieldDegree.lean`) are
  each already stated for an arbitrary field/vector space — not level-indexed at all. There is no
  growing convergence radius or level-dependent analytic bound anywhere: both proofs use exactly the
  same open-unit-ball hypotheses (`‖β‖ < 1`, `‖t‖ < 1`) and the same `Φ`.
* `K_2.norm_eq_spectralNorm` (`Langlands/LubinTateTowerStepSplittingField.lean:77`) is *already*
  generic in `LubinTate.K_2`'s own free parameters `K'`/`P₂` — confirmed by both concrete proofs
  citing the identical lemma name unchanged (`FPiEval_algebraMap_mem_adjoin` line 75,
  `FPiEval_algebraMap_mem_adjoin_K3` line 87).
* The two remaining level-specific ingredients — the composite algebra-map identity
  (`K_2.algebraMap_O_eq_comp_K_1` vs. `K_3.algebraMap_O_eq_comp_K_2`) and the `hOK` transport
  (`K_2.hOK_transport` vs. `K_3.hOK_transport`) — were *already* generalized before this pass:
  `Level.algebraMap_O_eq_comp_L` and `Level.hOK_transport`, both §83
  (`Langlands/LubinTateTowerStepLevelExists.lean`). What was missing was only the last mile:
  `Level.algebraMap_O_eq_comp_L` factors `algebraMap O (K_2 (K' := lvl.L) Pn)` through `K` (via
  `algebraMap K lvl.L`), whereas the concrete proofs need it factored through `lvl.L` directly (via
  `algebraMap O lvl.L`). Bridging those needs exactly `Level.instAlgebraOSelf`/
  `Level.algebraMap_OSelf_eq` — §84's self-composite, built the very next pass after §83 for an
  unrelated purpose (the `Splits` transport) but sufficient here unchanged.

So `FPiEval_algebraMap_mem_adjoin`'s generalization is not new analytic engineering: it is exactly
the "algebra-map-composite identification" pattern §84 itself named as the *easy* case, once
`Level.algebraMap_O_eq_comp_L` (§83) and `Level.instAlgebraOSelf`/`Level.algebraMap_OSelf_eq` (§84) are
combined. §84's assessment of this specific lemma was wrong; corrected here, checked by two `rfl`/
direct-instantiation checks below, not merely argued.

## Main result

* `Level.FPiEval_algebraMap_mem_adjoin` : **`F_π(β, algebraMap lvl.L (K_2 (K' := lvl.L) Pn) t) ∈
  lvl.L⟮β⟯`**, for `β : K_2 (K' := lvl.L) Pn` and `t : lvl.L` both in the open unit ball. Recovers
  `FPiEval_algebraMap_mem_adjoin` at `level_K_1` **by `rfl`**, and recovers
  `FPiEval_algebraMap_mem_adjoin_K3`'s exact statement when instantiated at `level_K_2` (the first
  time this specific fact is reached at that depth via the generic route, `rfl`-equal to the existing
  hand-written `K_2 → K_3` proof since both close the identical goal by the identical steps).

## What this does not close

`adjoin_root_eq_top_K_2`/`_K_3`'s other dependency, `piTorsion_one_K_2_eq_algebraMap_image`/`_K_3_...`
(the invariance fact), is **not** generalized here — its proof additionally needs a generic
`K_2.instFaithfulSMul_O`-shaped fact and a generic `divX_map_algebraMap_O_K_2_eq_map`-shaped roots
transport, neither built yet, and is a substantially larger proof (root-multiset bookkeeping via
`piTorsion_one_sdiff_zero_eq_roots_toFinset`, not an algebra-map-composite identification). `hgen`
(the degree hypothesis) and `finrank_K_n_eq_residueCard` itself remain out of scope for the same
reason §84 left them out of scope: they need the invariance fact first. Precisely characterized, not
attempted, per this project's "diagnose and stop rather than force a workaround" discipline.
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

/-- **`F_π(β, algebraMap lvl.L (K_2 (K' := lvl.L) Pn) t) ∈ lvl.L⟮β⟯`**, for `β : K_2 (K' := lvl.L)
Pn` and `t : lvl.L` both in the open unit ball. The `Level`-generic form of
`FPiEval_algebraMap_mem_adjoin`/`FPiEval_algebraMap_mem_adjoin_K3`: each evaluation summand of the
bivariate `F_π` series is an `lvl.L`-scalar (via `Level.algebraMap_O_eq_comp_L` combined with
`Level.algebraMap_OSelf_eq` to factor `algebraMap O (K_2 (K' := lvl.L) Pn)` through `lvl.L` directly)
times a power of `β`, hence lies in the finite-dimensional `lvl.L`-subspace `lvl.L⟮β⟯` (finite-
dimensional inside `K_2 (K' := lvl.L) Pn`, via `K_2.instFiniteDimensional`);
`Submodule.mem_of_hasSum_of_finiteDimensional` places the `HasSum` limit back inside it. -/
theorem Level.FPiEval_algebraMap_mem_adjoin (lvl : Level K) (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖)
    {π : O} (hπ : Irreducible π) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {β : K_2 (K' := lvl.L) Pn} (hβ : ‖β‖ < 1) {t : lvl.L} (ht : ‖t‖ < 1) :
    letI := lvl.algL
    letI := lvl.instAlgebraO Pn hOK
    FPiEval hπ hf β (algebraMap lvl.L (K_2 (K' := lvl.L) Pn) t) ∈ lvl.L⟮β⟯ := by
  letI := lvl.algL
  letI := lvl.instAlgebraOSelf (O := O)
  letI := lvl.instAlgebraO Pn hOK
  set t' := algebraMap lvl.L (K_2 (K' := lvl.L) Pn) t with ht'def
  have ht' : ‖t'‖ < 1 := by
    rw [ht'def, K_2.norm_eq_spectralNorm, spectralNorm_extends]; exact ht
  have hsum := hasSum_FPiEval (lvl.hOK_transport Pn hOK hnormL) hπ hf hβ ht'
  have hmem : ∀ n : Fin 2 →₀ ℕ,
      evalSummandMv (Phi hπ hf) (![β, t'] : Fin 2 → K_2 (K' := lvl.L) Pn) n ∈
      Subalgebra.toSubmodule
        ((lvl.L⟮β⟯ : IntermediateField lvl.L (K_2 (K' := lvl.L) Pn)).toSubalgebra) := by
    intro n
    rw [Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra]
    unfold evalSummandMv
    rw [Fin.prod_univ_two]
    show algebraMap O (K_2 (K' := lvl.L) Pn) (MvPowerSeries.coeff n (Phi hπ hf)) *
        ((![β, t'] : Fin 2 → K_2 (K' := lvl.L) Pn) 0 ^ n 0 *
          (![β, t'] : Fin 2 → K_2 (K' := lvl.L) Pn) 1 ^ n 1) ∈
      (lvl.L⟮β⟯ : IntermediateField lvl.L (K_2 (K' := lvl.L) Pn))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    -- `algebraMap O (K_2 Pn)` factors through `lvl.L` directly, combining `Level.
    -- algebraMap_O_eq_comp_L` (which factors through `K`) with `Level.algebraMap_OSelf_eq`
    -- (which identifies `algebraMap O lvl.L` with that same `K`-route, via `instAlgebraOSelf`).
    have hOL : algebraMap O lvl.L (MvPowerSeries.coeff n (Phi hπ hf)) =
        algebraMap K lvl.L (algebraMap O K (MvPowerSeries.coeff n (Phi hπ hf))) :=
      congrFun (congrArg DFunLike.coe (lvl.algebraMap_OSelf_eq (O := O))) _
    have hOK2 : algebraMap O (K_2 (K' := lvl.L) Pn) (MvPowerSeries.coeff n (Phi hπ hf)) =
        algebraMap lvl.L (K_2 (K' := lvl.L) Pn)
          (algebraMap O lvl.L (MvPowerSeries.coeff n (Phi hπ hf))) := by
      rw [hOL]; exact congrFun (lvl.algebraMap_O_eq_comp_L Pn hOK) _
    rw [hOK2, ht'def, ← map_pow]
    refine mul_mem (IntermediateField.algebraMap_mem _ _)
      (mul_mem (pow_mem (IntermediateField.mem_adjoin_simple_self _ β) _)
        (IntermediateField.algebraMap_mem _ _))
  have hres := Submodule.mem_of_hasSum_of_finiteDimensional
    (Subalgebra.toSubmodule
      ((lvl.L⟮β⟯ : IntermediateField lvl.L (K_2 (K' := lvl.L) Pn)).toSubalgebra))
    hsum hmem
  rwa [Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra] at hres

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- **`K_1 → K_2`, `rfl`-recovery.** The generic lemma, applied at `level_K_1`, types exactly as
`FPiEval_algebraMap_mem_adjoin`'s own statement, and the two fully-applied proof terms are
`rfl`-equal (proof irrelevance witnessing the two *statements* elaborate to the same `Prop`, per the
same discipline §82/§83 already applied to their own `rfl` checks). -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f)
    {β : K_2 (K' := K_1 (K := K) P) P₂} (hβ : ‖β‖ < 1) {t : K_1 (K := K) P} (ht : ‖t‖ < 1) :
    Level.FPiEval_algebraMap_mem_adjoin (level_K_1 (K := K) (P := P)) P₂ hOK
        (hnorm_K_K_1 (K := K) (P := P)) hπ hf hβ ht =
      FPiEval_algebraMap_mem_adjoin hOK hπ hf hβ ht := rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] in
/-- **`K_2 → K_3`, `rfl`-recovery.** The generic lemma, applied at `level_K_2`, types exactly as
`FPiEval_algebraMap_mem_adjoin_K3`'s own statement (unlike §83's existence step, this depth
*already* has a hand-written theorem to check against — `FPiEval_algebraMap_mem_adjoin_K3`,
`Langlands/LubinTateTowerStepK3Degree.lean`), and the two proof terms are `rfl`-equal. -/
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
