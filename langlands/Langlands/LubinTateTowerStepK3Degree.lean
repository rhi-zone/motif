/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepK3RootConnect
import Langlands.LubinTateSplittingFieldDegree

/-!
# `K2P2⟮γ⟯ = K_3` and `[K_3 : baseChangeSplittingField] = q`

The `K_2 → K_3` analogue of `Langlands/LubinTateTowerStepDegree.lean`: reassembling
`exists_piTorsion_translate_of_aeval_P₃_eq_zero` (transitivity) and `piTorsion_one_K_3_eq_
algebraMap_image` (the `K2P2 P₂ → K_3` `piTorsion`-invariance fact, `Langlands/
LubinTateTowerStepK3RootConnect.lean`) into the headline structural statement, mirroring
`Langlands.LubinTateTowerStepDegree`'s `K_1⟮β⟯ = baseChangeSplittingField`/`[baseChangeSplittingField : K_1] = q` argument one level up.

## Scope, relative to the `K_1 → K_2` template

`Langlands/LubinTateTowerStepDegree.lean`'s `finrank_K_2_eq_residueCard` takes `Module.finrank
(K_1 P) (K_1 P)⟮β⟯ = residueCard O` as an external hypothesis (`hβfin`) rather than deriving `β`'s
existence itself — that existence comes from `exists_finrank_adjoin_eq_residueCard_K_2` (`Langlands/
LubinTateTowerStepConcrete.lean`), built from `exists_eisenstein_tower_step_K_1`'s *concrete* output.
This file mirrors that same scope decision one level up: `finrank_K_3_eq_residueCard` below takes an
analogous `hγfin` hypothesis rather than deriving `γ`'s existence from `exists_eisenstein_tower_
step_K_2`'s output, which lives in the *nested* `O_{K_2}` type (`Langlands/
LubinTateTowerStepConcreteK2.lean`) and would need transporting to the flat spelling first — that
transport is not built here.

## Main results

* `FPiEval_algebraMap_mem_adjoin_K3` : **`F_π(γ, algebraMap t) ∈ (K2P2 P₂)⟮γ⟯`**, for `γ : K_3` in
  the open unit ball and `t : K2P2 P₂` in the open unit ball. The `K_2 → K_3` analogue of
  `FPiEval_algebraMap_mem_adjoin`.
* `adjoin_root_eq_top_K_3` : **`(K2P2 P₂)⟮γ⟯ = ⊤`**, for `γ` any root of `P₃`'s image in `K_3`.
* `finrank_K_3_eq_residueCard` : **`Module.finrank (K2P2 P₂) (K_3 P₃) = residueCard O`** —
  `[K_3 : baseChangeSplittingField] = q`, given `hγfin : Module.finrank (K2P2 P₂) (K2P2 P₂)⟮γ⟯ = residueCard O` for the
  same `γ`.
-/

@[expose] public section

noncomputable section

open scoped Polynomial IntermediateField

namespace LubinTate

open IsLocalRing PowerSeries Polynomial NonarchimedeanPowerSeriesEval
open NonarchimedeanMvPowerSeriesEvalFin2

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]
variable {π : O} {f : O⟦X⟧} {P : O[X]} (P₂ : (↥(integralClosure
    ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
  [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]
  (P₃ : (O_K2 (K := K) P₂)[X])

/-! ## `F_π(γ, algebraMap t)` stays inside `(K2P2 P₂)⟮γ⟯` -/

/-- **`F_π(γ, algebraMap (K2P2 P₂) K_3 t) ∈ (K2P2 P₂)⟮γ⟯`**, for `γ : K_3` and `t : K2P2 P₂` both in
the open unit ball. The `K_2 → K_3` analogue of `FPiEval_algebraMap_mem_adjoin`: each evaluation
summand of the bivariate `F_π` series is a `K2P2 P₂`-scalar (via `K_3.algebraMap_O_eq_comp_K_2`)
times a power of `γ`, hence lies in the finite-dimensional `K2P2 P₂`-subspace `(K2P2 P₂)⟮γ⟯`, and the
`HasSum` limit stays there too (`Submodule.mem_of_hasSum_of_finiteDimensional`). -/
theorem FPiEval_algebraMap_mem_adjoin_K3 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃} (hγ : ‖γ‖ < 1)
    {t : K2P2 (K := K) P₂} (ht : ‖t‖ < 1) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    FPiEval hπ hf γ
        (algebraMap (K2P2 (K := K) P₂)
          (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) t) ∈
      (K2P2 (K := K) P₂)⟮γ⟯ := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
  set t' := algebraMap (K2P2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) t with ht'def
  have ht' : ‖t'‖ < 1 := by
    rw [ht'def, baseChangeSplittingField.norm_eq_spectralNorm, spectralNorm_extends]; exact ht
  have hsum := hasSum_FPiEval (K_3.hOK_transport (K := K) (P := P) P₂ P₃ hOK) hπ hf hγ ht'
  have hmem : ∀ n : Fin 2 →₀ ℕ,
      evalSummandMv (Phi hπ hf)
        (![γ, t'] : Fin 2 → K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) n ∈
      Subalgebra.toSubmodule
        ((K2P2 (K := K) P₂)⟮γ⟯ : IntermediateField (K2P2 (K := K) P₂)
          (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)).toSubalgebra := by
    intro n
    rw [Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra]
    unfold evalSummandMv
    rw [Fin.prod_univ_two]
    show algebraMap O (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
        (MvPowerSeries.coeff n (Phi hπ hf)) *
        ((![γ, t'] : Fin 2 → K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) 0 ^ n 0 *
          (![γ, t'] : Fin 2 → K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) 1 ^
            n 1) ∈
      ((K2P2 (K := K) P₂)⟮γ⟯ : IntermediateField (K2P2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show algebraMap O (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
        (MvPowerSeries.coeff n (Phi hπ hf)) =
        algebraMap (K2P2 (K := K) P₂)
          (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
          (algebraMap O (K2P2 (K := K) P₂) (MvPowerSeries.coeff n (Phi hπ hf))) from
      congrFun (K_3.algebraMap_O_eq_comp_K_2 (K := K) (P := P) P₂ P₃ hOK) _,
      ht'def, ← map_pow]
    refine mul_mem (IntermediateField.algebraMap_mem _ _)
      (mul_mem (pow_mem (IntermediateField.mem_adjoin_simple_self _ γ) _)
        (IntermediateField.algebraMap_mem _ _))
  have hres := Submodule.mem_of_hasSum_of_finiteDimensional
    (Subalgebra.toSubmodule
      ((K2P2 (K := K) P₂)⟮γ⟯ : IntermediateField (K2P2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)).toSubalgebra) hsum hmem
  rwa [Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra] at hres

/-! ## `(K2P2 P₂)⟮γ⟯ = K_3` -/

/-- **`(K2P2 P₂)⟮γ⟯ = ⊤`, for `γ` any root of `P₃`'s image in `K_3`.** `K_3` is *by construction*
the splitting field of `P₃`'s image over `K2P2 P₂`, generated by its roots (`Polynomial.
IsSplittingField.adjoin_rootSet`). Every root `γ'` differs from `γ` by a `piTorsion hπ hf 1`-
translate (`exists_piTorsion_translate_of_aeval_P₃_eq_zero`), and — by `piTorsion_one_K_3_eq_
algebraMap_image` — that translate is the `algebraMap`-image of a `K2P2 P₂`-torsion point `t`, so
`γ' = F_π(γ, algebraMap t) ∈ (K2P2 P₂)⟮γ⟯` by `FPiEval_algebraMap_mem_adjoin_K3`; `γ` itself
trivially lies in its own adjoin. -/
theorem adjoin_root_eq_top_K_3 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    (β' : O_K2 (K := K) P₂) (u₃ : (O_K2 (K := K) P₂)⟦X⟧) (hu₃ : IsUnit u₃)
    (heq₃ :
      letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : _⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₃.coeff 0) β') (hdeg : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃}
    (hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    ((K2P2 (K := K) P₂)⟮γ⟯ : IntermediateField (K2P2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) = ⊤ := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
  have hγnorm : ‖γ‖ < 1 :=
    norm_lt_one_of_aeval_P₃_eq_zero (K := K) (P := P) P₂ P₃ β' hβ'irr hP₃dist hassoc hdeg hβ'norm
      hγroot
  have hroots : ((P₃.map (algebraMap _ (K2P2 (K := K) P₂))).rootSet
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) ⊆
      (((K2P2 (K := K) P₂)⟮γ⟯ : IntermediateField (K2P2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)).toSubalgebra :
        Set (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) := by
    intro γ' hγ'
    obtain ⟨-, hγ'root⟩ := Polynomial.mem_rootSet'.mp hγ'
    obtain ⟨t', ht'mem, ht'eq⟩ :=
      exists_piTorsion_translate_of_aeval_P₃_eq_zero (K := K) (P := P) P₂ P₃ hOK hπ hf β' u₃ hu₃
        heq₃ hβ'irr hP₃dist hassoc hdeg hβ'norm hγroot hγ'root
    rw [piTorsion_one_K_3_eq_algebraMap_image (K := K) (P := P) (P₂ := P₂) (P₃ := P₃) hOK hπ hπnorm
      hf hu heq hPdist hPdeg] at ht'mem
    obtain ⟨t, htmem, htmem'⟩ := ht'mem
    rw [SetLike.mem_coe, IntermediateField.mem_toSubalgebra, ht'eq, ← htmem']
    exact FPiEval_algebraMap_mem_adjoin_K3 (K := K) (P := P) P₂ P₃ hOK hπ hf hγnorm htmem.1
  have hle : (⊤ : Subalgebra (K2P2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) ≤
      ((K2P2 (K := K) P₂)⟮γ⟯ : IntermediateField (K2P2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)).toSubalgebra := by
    rw [← Polynomial.IsSplittingField.adjoin_rootSet
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
      (P₃.map (algebraMap _ (K2P2 (K := K) P₂)))]
    exact Algebra.adjoin_le hroots
  refine eq_top_iff.mpr fun x _ ↦ ?_
  exact (IntermediateField.mem_toSubalgebra _ x).mp (hle Algebra.mem_top)

/-! ## `[K_3 : baseChangeSplittingField] = q` -/

/-- **`Module.finrank (K2P2 P₂) (K_3 P₃) = residueCard O`** — `[K_3 : baseChangeSplittingField] = q`. Takes `hγfin : Module.finrank (K2P2 P₂)
(K2P2 P₂)⟮γ⟯ = residueCard O` as an external hypothesis (see the module docstring for why — the
existence of such a `γ` at a *concrete* `P₃` needs `exists_eisenstein_tower_step_K_2`'s output
transported from the nested `O_{K_2}` spelling, out of scope here); `adjoin_root_eq_top_K_3`
upgrades the same `γ` to `(K2P2 P₂)⟮γ⟯ = ⊤`, so `IntermediateField.finrank_top'` identifies
`Module.finrank (K2P2 P₂) (K_3 P₃)` with `Module.finrank (K2P2 P₂) (K2P2 P₂)⟮γ⟯`. -/
theorem finrank_K_3_eq_residueCard (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    (β' : O_K2 (K := K) P₂) (u₃ : (O_K2 (K := K) P₂)⟦X⟧) (hu₃ : IsUnit u₃)
    (heq₃ :
      letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : _⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₃.coeff 0) β') (hdeg : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃}
    (hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0)
    (hγfin : Module.finrank (K2P2 (K := K) P₂) (K2P2 (K := K) P₂)⟮γ⟯ = residueCard O) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    Module.finrank (K2P2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) =
      residueCard O := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
  have htop := adjoin_root_eq_top_K_3 (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq hPdist hPdeg
    β' u₃ hu₃ heq₃ hβ'irr hP₃dist hassoc hdeg hβ'norm hγroot
  rw [← IntermediateField.finrank_top' (F := K2P2 (K := K) P₂)
    (E := K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃), ← htop]
  exact hγfin

end LubinTate

end
