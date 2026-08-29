import Langlands.LubinTateResidueUnitsAction

/-!
# Freeness of the `(O/π)ˣ`-action on nonzero `π`-torsion

`eval (phiU hπ hf u) α = α` (α nonzero torsion) forces `u ≡ 1 (mod π)`. This is provable by a
genuinely *simpler* argument than the mod-`π` factoring (`eval_phiU_eq_of_dvd_sub`) needed: no
minimum-spacing fact (`norm_sub_eq_rpow_of_mem_piTorsion_one_ne_zero_of_ne`) is required at all.

## Route

For `u, v : Oˣ` with `eval (phiU hπ hf u) α = eval (phiU hπ hf v) α` (`α` a nonzero element of
`piTorsion hπ hf 1`), suppose toward a contradiction that `π ∤ ((u:O) - (v:O))`. Since `O` is local
with `maximalIdeal O = Ideal.span {π}` (`hπ.maximalIdeal_eq`), non-divisibility means `(u:O)-(v:O)`
is **a unit** (`IsLocalRing.notMem_maximalIdeal`), so `‖algebraMap O K ((u:O)-(v:O))‖ = 1` exactly
(`norm_algebraMap_eq_one_of_isUnit`) — not merely `≤ 1`. Combined with the two quadratic-closeness
bounds `‖eval (phiU u) α - (u:O) • α‖ ≤ ‖α‖ ^ 2` (and the same for `v`,
`norm_eval_sub_coeff_one_mul_le` + `coeff_one_phiU`), the assumed equality `eval (phiU u) α = eval
(phiU v) α` forces `‖((u:O)-(v:O)) • α‖ ≤ ‖α‖ ^ 2`, i.e. `‖α‖ ≤ ‖α‖ ^ 2` (using the exact norm-`1`
fact to cancel `‖algebraMap O K ((u:O)-(v:O))‖`). Since `0 < ‖α‖ < 1`, `‖α‖ ^ 2 < ‖α‖` strictly —
contradiction. **No minimum-spacing argument is needed**; the exact norm-`1` fact for the unit
`(u:O)-(v:O)` does the same job the spacing theorem did for the forward direction, more directly.

## Main results

* `dvd_sub_of_eval_phiU_eq` : the converse of `eval_phiU_eq_of_dvd_sub` — `eval (phiU hπ hf u) α =
  eval (phiU hπ hf v) α` (α nonzero torsion) forces `π ∣ ((u:O) - (v:O))`.
* `residuePiTorsion_smul_eq_self_iff` / freeness : `u' • α = α` (in the `(ResidueField O)ˣ`-action)
  forces `u' = 1`, for `α` a nonzero element of `piTorsion hπ hf 1`.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace LubinTate

open NonarchimedeanPowerSeriesEval PowerSeries IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [FaithfulSMul O K]
variable {π : O} {f : O⟦X⟧}

omit [FaithfulSMul O K] in
/-- **The converse of `eval_phiU_eq_of_dvd_sub`.** If `eval (phiU hπ hf u) α = eval (phiU hπ hf v)
α` for `α` a nonzero element of `piTorsion hπ hf 1`, then `π ∣ ((u:O) - (v:O))`. See the module
docstring for the route: no minimum-spacing fact is needed, only that a non-multiple of `π` is a
unit of `O` (hence maps to `K` with norm exactly `1`). -/
theorem dvd_sub_of_eval_phiU_eq (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f) {u v : Oˣ}
    {α : K} (hα : α ∈ piTorsion (K := K) hπ hf 1) (hα0 : α ≠ 0)
    (heval : eval (phiU hπ hf u) α = eval (phiU hπ hf v) α) :
    π ∣ ((u : O) - (v : O)) := by
  by_contra hndvd
  have hαnorm : ‖α‖ < 1 := hα.1
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα0
  have hunit : IsUnit ((u : O) - (v : O)) := by
    rw [← IsLocalRing.notMem_maximalIdeal, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
    exact hndvd
  have hnormuv : ‖algebraMap O K ((u : O) - (v : O))‖ = 1 :=
    norm_algebraMap_eq_one_of_isUnit hOK hunit
  have huBound : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (phiU hπ hf u))‖ ≤ 1 := fun k ↦ hOK _
  have hvBound : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (phiU hπ hf v))‖ ≤ 1 := fun k ↦ hOK _
  have hstepA : ‖eval (phiU hπ hf u) α - algebraMap O K (u : O) * α‖ ≤ ‖α‖ ^ 2 := by
    have := norm_eval_sub_coeff_one_mul_le huBound (constantCoeff_phiU hπ hf u) hαnorm
    rwa [coeff_one_phiU] at this
  have hstepB : ‖eval (phiU hπ hf v) α - algebraMap O K (v : O) * α‖ ≤ ‖α‖ ^ 2 := by
    have := norm_eval_sub_coeff_one_mul_le hvBound (constantCoeff_phiU hπ hf v) hαnorm
    rwa [coeff_one_phiU] at this
  have hdiff : ‖algebraMap O K (u : O) * α - algebraMap O K (v : O) * α‖ ≤ ‖α‖ ^ 2 := by
    have heqsub : algebraMap O K (u : O) * α - algebraMap O K (v : O) * α =
        (algebraMap O K (u : O) * α - eval (phiU hπ hf u) α) +
          (eval (phiU hπ hf v) α - algebraMap O K (v : O) * α) := by
      rw [heval]; ring
    rw [heqsub]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hstepB)
    rwa [show algebraMap O K (u : O) * α - eval (phiU hπ hf u) α =
        -(eval (phiU hπ hf u) α - algebraMap O K (u : O) * α) by ring, norm_neg]
  have hdiffeq : algebraMap O K (u : O) * α - algebraMap O K (v : O) * α =
      algebraMap O K ((u : O) - (v : O)) * α := by rw [map_sub, sub_mul]
  rw [hdiffeq, norm_mul, hnormuv, one_mul] at hdiff
  have hcontra : ‖α‖ ^ 2 < ‖α‖ := by
    calc ‖α‖ ^ 2 = ‖α‖ * ‖α‖ := sq ‖α‖
      _ < 1 * ‖α‖ := by gcongr
      _ = ‖α‖ := one_mul _
  exact absurd hdiff (not_le.mpr hcontra)

/-- **Freeness of the `(ResidueField O)ˣ`-action on nonzero `π`-torsion.** If `u' • α = α` for `α`
a nonzero element of `piTorsion hπ hf 1`, then `u' = 1`. Lifts `u'` to `Oˣ` via `surjInv`, unfolds
`u' • α` to `eval (phiU (surjInv u')) α` (`coe_residuePiTorsion_smul`) and `α` to `eval (phiU 1)
α` (`phiU_one_eq_X` + `eval_X`), then applies `dvd_sub_of_eval_phiU_eq` against `v := 1` and
`residueUnitsMap_eq_iff_dvd_sub` to conclude `residueUnitsMap (surjInv u') = 1`, i.e. (by
`Function.rightInverse_surjInv` and `map_one`) `u' = 1`. -/
theorem eq_one_of_residuePiTorsion_smul_eq_self (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {w : O⟦X⟧} (hw : IsUnit w) (heq : f = (P : O⟦X⟧) * w)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree)
    {u' : (ResidueField O)ˣ} {x : ↥(piTorsion (K := K) hπ hf 1)} (hx0 : (x : K) ≠ 0)
    (hfix : letI := residuePiTorsionMulAction hOK hπ hπnorm hf hw heq hPdist hPdeg2
      u' • x = x) :
    u' = 1 := by
  letI := residuePiTorsionMulAction hOK hπ hπnorm hf hw heq hPdist hPdeg2
  have hcoe : ((u' • x : ↥(piTorsion (K := K) hπ hf 1)) : K) = (x : K) := congrArg Subtype.val hfix
  rw [coe_residuePiTorsion_smul hOK hπ hπnorm hf hw heq hPdist hPdeg2] at hcoe
  have hXeq : eval (phiU hπ hf (1 : Oˣ)) (x : K) = (x : K) := by
    rw [phiU_one_eq_X hπ hf]; exact eval_X _
  have heval : eval (phiU hπ hf (Function.surjInv residueUnitsMap_surjective u')) (x : K) =
      eval (phiU hπ hf (1 : Oˣ)) (x : K) := by rw [hcoe, hXeq]
  have hdvd := dvd_sub_of_eval_phiU_eq hOK hπ hf x.2 hx0 heval
  have hmapeq : residueUnitsMap (Function.surjInv residueUnitsMap_surjective u') =
      residueUnitsMap (1 : Oˣ) :=
    (residueUnitsMap_eq_iff_dvd_sub hπ).mpr hdvd
  rw [map_one] at hmapeq
  rwa [Function.rightInverse_surjInv residueUnitsMap_surjective u'] at hmapeq

end LubinTate

end
