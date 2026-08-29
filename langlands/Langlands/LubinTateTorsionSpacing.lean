import Langlands.LubinTateTorsionGroup
import Langlands.LubinTateRootCount
import Langlands.LubinTateFormalGroupEval
import Langlands.NonarchimedeanMvPowerSeriesEvalFin2

/-!
# Minimum spacing of `piTorsion hπ hf 1`'s nonzero elements

The mod-`π` factoring's "close ⟹ equal" step needs a genuine minimum-spacing / discreteness fact
on `piTorsion hπ hf 1`'s distinct elements. This file gets one without any discriminant
computation, using machinery already in the repo:

* `piTorsionAddCommGroup` (`Langlands.LubinTateTorsionGroup`): `piTorsion hπ hf 1` is an
  `AddCommGroup` under `F_π`-addition. For distinct nonzero `α, β`, the `F_π`-difference
  `γ := FPiEval hπ hf α (eval (PhiInv hπ hf) β)` is itself a *nonzero* element of `piTorsion hπ hf
  1` (`mem_piTorsion_FPiEval`, `mem_piTorsion_PhiInv`; nonzero via the group's `sub_ne_zero`).
* `norm_eq_rpow_of_mem_piTorsion_one_ne_zero` (`Langlands.LubinTateRootCount`, new): every nonzero
  torsion point — `α`, `β`, and `γ` alike — has the *same exact* norm `c ^ (1/(q-1) : ℝ)`, `c :=
  ‖algebraMap O K π‖`, `q - 1 := P.divX.natDegree`. No splitting hypothesis needed.
* `norm_eval_sub_coeff_one_mul_le` (`Langlands.NonarchimedeanPowerSeriesEval`, already in the repo)
  applied to `PhiInv hπ hf` (linear coefficient `-1`, `coeff_one_PhiInv`) gives `i_{F_π}(β) ≈ -β`
  to quadratic order.
* `norm_evalMv_sub_linear_le` (`Langlands.NonarchimedeanMvPowerSeriesEvalFin2`, new) applied to `Φ
  := Phi hπ hf` (linear part `X + Y`, `coeff_Phi_of_degree_eq_one`) gives `F_π(α, i_{F_π}(β)) ≈ α +
  i_{F_π}(β)` to quadratic order.

Chaining these two quadratic approximations gives `‖γ - (α - β)‖ ≤ (max ‖α‖ ‖β‖) ^ 2 = c ^ (2/(q-1)
: ℝ)`, strictly less than `‖γ‖ = c ^ (1/(q-1) : ℝ)` whenever `q ≥ 2` (always true,
`P.divX.natDegree ≥ 1`). The ultrametric isosceles-triangle principle
(`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`) then forces `‖α - β‖ = ‖γ‖` exactly — an
*exact* common spacing value for every pair of distinct nonzero torsion points, sharper than a mere
lower bound, and needing only `q ≥ 2`.

## Main result

* `norm_sub_eq_rpow_of_mem_piTorsion_one_ne_zero_of_ne` : for distinct nonzero `α, β ∈ piTorsion hπ
  hf 1`, `‖α - β‖ = ‖algebraMap O K π‖ ^ (1 / (P.divX.natDegree : ℝ))` exactly — the same value
  `norm_eq_rpow_of_mem_piTorsion_one_ne_zero` gives for `‖α‖`/`‖β‖` themselves.

This spacing fact is what makes the mod-`π` factoring possible: `Langlands/LubinTateModPiFactoring.lean`
assembles it with `coeff_one_phiU` and `mem_piTorsion_eval_phiU` to turn the quadratic closeness
bound `norm_eval_sub_coeff_one_mul_le` applied to `phiU` into the exact equality `eval (phiU u) α =
eval (phiU v) α`.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace LubinTate

open NonarchimedeanPowerSeriesEval NonarchimedeanMvPowerSeriesEvalFin2 PowerSeries IsLocalRing
  Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [FaithfulSMul O K]
variable {π : O} {f : O⟦X⟧}

omit [FaithfulSMul O K] in
/-- **`i_{F_π}(x)` agrees with `-x` to quadratic order.** Specializes
`NonarchimedeanPowerSeriesEval.norm_eval_sub_coeff_one_mul_le` to `PhiInv hπ hf` (constant term `0`,
linear coefficient `-1`, `coeff_one_PhiInv`). -/
theorem norm_eval_PhiInv_add_le (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {x : K} (hx : ‖x‖ < 1) :
    ‖eval (PhiInv hπ hf) x + x‖ ≤ ‖x‖ ^ 2 := by
  have hPhiInvBound : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (PhiInv hπ hf))‖ ≤ 1 :=
    fun k ↦ hOK _
  have hkey := norm_eval_sub_coeff_one_mul_le hPhiInvBound
    (by simp [constantCoeff_PhiInv hπ hf] : PowerSeries.constantCoeff (PhiInv hπ hf) = 0) hx
  rw [coeff_one_PhiInv] at hkey
  rwa [map_neg, map_one, neg_one_mul, sub_neg_eq_add] at hkey

omit [FaithfulSMul O K] in
/-- **`F_π(a, b)` agrees with the ordinary sum `a + b` to quadratic order.** Specializes
`NonarchimedeanMvPowerSeriesEvalFin2.norm_evalMv_sub_linear_le` to `Φ := Phi hπ hf` (constant term
`0`, both linear coefficients `1`, `coeff_Phi_of_degree_eq_one`). -/
theorem norm_FPiEval_sub_add_le (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ‖FPiEval hπ hf a b - (a + b)‖ ≤ (max ‖a‖ ‖b‖) ^ 2 := by
  have hkey := norm_evalMv_sub_linear_le (norm_algebraMap_coeff_Phi_le_one hOK hπ hf)
    (constantCoeff_Phi hπ hf) (y := ![a, b])
    (show ‖(![a, b] : Fin 2 → K) 0‖ < 1 by simpa using ha)
    (show ‖(![a, b] : Fin 2 → K) 1‖ < 1 by simpa using hb)
  rw [coeff_Phi_of_degree_eq_one hπ hf (m := Finsupp.single 0 1) (by simp),
    coeff_Phi_of_degree_eq_one hπ hf (m := Finsupp.single 1 1) (by simp)] at hkey
  simp only [map_one, one_mul] at hkey
  simpa [FPiEval] using hkey

/-- **The minimum spacing theorem: every pair of distinct nonzero elements of `piTorsion hπ hf 1`
is exactly `‖algebraMap O K π‖ ^ (1 / (P.divX.natDegree : ℝ))` apart.** The main result of this
file — see the module docstring for the route. -/
theorem norm_sub_eq_rpow_of_mem_piTorsion_one_ne_zero_of_ne
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree)
    {α β : K} (hα : α ∈ piTorsion (K := K) hπ hf 1) (hα0 : α ≠ 0)
    (hβ : β ∈ piTorsion (K := K) hπ hf 1) (hβ0 : β ≠ 0) (hαβ : α ≠ β) :
    ‖α - β‖ = ‖algebraMap O K π‖ ^ (1 / (P.divX.natDegree : ℝ)) := by
  have hf0 : PowerSeries.coeff 0 f = 0 := hf.1
  have hf1 : PowerSeries.coeff 1 f = π := hf.2.1
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf0 hf1 hPdist hPdeg2
  have hαnorm : ‖α‖ < 1 := hα.1
  have hβnorm : ‖β‖ < 1 := hβ.1
  set β' : K := eval (PhiInv hπ hf) β with hβ'def
  set γ : K := FPiEval hπ hf α β' with hγdef
  -- `γ` is a nonzero torsion point.
  have hβ'mem : β' ∈ piTorsion (K := K) hπ hf 1 := mem_piTorsion_PhiInv hOK hπ hf 1 hβ
  have hγmem : γ ∈ piTorsion (K := K) hπ hf 1 := mem_piTorsion_FPiEval hOK hπ hf 1 hα hβ'mem
  have hγ0 : γ ≠ 0 := by
    intro hγeq
    apply hαβ
    letI := piTorsionAddCommGroup hOK hπ hf 1
    have hcoeq : ((⟨α, hα⟩ - ⟨β, hβ⟩ :
        ↥(piTorsion (K := K) hπ hf 1)) : K) = γ := by
      rw [sub_eq_add_neg, coe_piTorsion_add, coe_piTorsion_neg]
    have hsubzero : (⟨α, hα⟩ - ⟨β, hβ⟩ : ↥(piTorsion (K := K) hπ hf 1)) = 0 :=
      Subtype.ext (hcoeq.trans hγeq)
    have := sub_eq_zero.mp hsubzero
    exact congrArg Subtype.val this
  -- The three exact norms.
  set c : ℝ := ‖algebraMap O K π‖ with hcdef
  have hnormα : ‖α‖ = c ^ (1 / (P.divX.natDegree : ℝ)) :=
    norm_eq_rpow_of_mem_piTorsion_one_ne_zero hOK hπ hπnorm hf hu heq hPdist hPdeg2 hα hα0
  have hnormβ : ‖β‖ = c ^ (1 / (P.divX.natDegree : ℝ)) :=
    norm_eq_rpow_of_mem_piTorsion_one_ne_zero hOK hπ hπnorm hf hu heq hPdist hPdeg2 hβ hβ0
  have hnormγ : ‖γ‖ = c ^ (1 / (P.divX.natDegree : ℝ)) :=
    norm_eq_rpow_of_mem_piTorsion_one_ne_zero hOK hπ hπnorm hf hu heq hPdist hPdeg2 hγmem hγ0
  -- The quadratic closeness bound `‖γ - (α - β)‖ ≤ c ^ (2/(q-1))`.
  have hPhiInvBound : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (PhiInv hπ hf))‖ ≤ 1 :=
    fun k ↦ hOK _
  have hβ'norm : ‖β'‖ ≤ ‖β‖ :=
    norm_eval_le hPhiInvBound (by simp [constantCoeff_PhiInv hπ hf]) hβnorm
  have hβ'lt1 : ‖β'‖ < 1 := lt_of_le_of_lt hβ'norm hβnorm
  have hstep1 : ‖eval (PhiInv hπ hf) β + β‖ ≤ ‖β‖ ^ 2 := norm_eval_PhiInv_add_le hOK hπ hf hβnorm
  have hstep2 : ‖γ - (α + β')‖ ≤ (max ‖α‖ ‖β'‖) ^ 2 :=
    norm_FPiEval_sub_add_le hOK hπ hf hαnorm hβ'lt1
  have hmaxle : max ‖α‖ ‖β'‖ ≤ c ^ (1 / (P.divX.natDegree : ℝ)) := by
    rw [max_le_iff]
    exact ⟨hnormα.le, hβ'norm.trans hnormβ.le⟩
  have hstep2' : ‖γ - (α + β')‖ ≤ (c ^ (1 / (P.divX.natDegree : ℝ))) ^ 2 :=
    hstep2.trans (pow_le_pow_left₀ (le_trans (norm_nonneg _) (le_max_left _ _)) hmaxle 2)
  have hstep1' : ‖eval (PhiInv hπ hf) β + β‖ ≤ (c ^ (1 / (P.divX.natDegree : ℝ))) ^ 2 := by
    rw [← hnormβ]; exact hstep1
  have hcombine : γ - (α - β) = (γ - (α + β')) + (eval (PhiInv hπ hf) β + β) := by
    rw [hβ'def]; ring
  have htri : ‖γ - (α - β)‖ ≤ max ‖γ - (α + β')‖ ‖eval (PhiInv hπ hf) β + β‖ := by
    rw [hcombine]; exact IsUltrametricDist.norm_add_le_max _ _
  have hbound : ‖γ - (α - β)‖ ≤ (c ^ (1 / (P.divX.natDegree : ℝ))) ^ 2 :=
    htri.trans (max_le hstep2' hstep1')
  -- Strictness: `c ^ (2/(q-1)) < c ^ (1/(q-1))`, using `q - 1 = P.divX.natDegree ≥ 1`.
  have hinj : Function.Injective (algebraMap O K) := FaithfulSMul.algebraMap_injective O K
  have hc0 : 0 < c := by
    rw [hcdef, norm_pos_iff]
    exact (map_ne_zero_iff (algebraMap O K) hinj).mpr hπ.ne_zero
  have hc1 : c < 1 := hπnorm
  have hn0 : (0 : ℝ) < (P.divX.natDegree : ℝ) := by exact_mod_cast hQdeg
  have hexp : (1 / (P.divX.natDegree : ℝ)) < (2 / (P.divX.natDegree : ℝ)) := by
    gcongr
    norm_num
  have hstrict : c ^ (2 / (P.divX.natDegree : ℝ)) < c ^ (1 / (P.divX.natDegree : ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_gt hc0 hc1 hexp
  have hsq : (c ^ (1 / (P.divX.natDegree : ℝ))) ^ 2 = c ^ (2 / (P.divX.natDegree : ℝ)) := by
    rw [← Real.rpow_natCast (c ^ (1 / (P.divX.natDegree : ℝ))) 2, ← Real.rpow_mul hc0.le]
    congr 1; ring
  have hlt : ‖γ - (α - β)‖ < ‖γ‖ := by
    rw [hnormγ]
    calc ‖γ - (α - β)‖ ≤ (c ^ (1 / (P.divX.natDegree : ℝ))) ^ 2 := hbound
      _ = c ^ (2 / (P.divX.natDegree : ℝ)) := hsq
      _ < c ^ (1 / (P.divX.natDegree : ℝ)) := hstrict
  -- The ultrametric isosceles-triangle principle finishes it.
  have hdnorm : ‖(α - β) - γ‖ < ‖γ‖ := by
    rw [show (α - β) - γ = -(γ - (α - β)) by ring, norm_neg]; exact hlt
  have hne : ‖(α - β) - γ‖ ≠ ‖γ‖ := hdnorm.ne
  have hiso := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  have heq : ((α - β) - γ) + γ = α - β := by ring
  rw [heq, max_eq_right hdnorm.le] at hiso
  rw [hiso, hnormγ]

end LubinTate

end
