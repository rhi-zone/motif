import Langlands.LubinTateTorsionSpacing
import Langlands.LubinTateUnitsAction

/-!
# The `Oˣ`-action on nonzero `π`-torsion factors through `(O/π)ˣ`

`ROADMAP.md` §37/§38 identified the mod-`π` factoring — `u ≡ v (mod π)` in `Oˣ` implies `eval
(phiU hπ hf u) α = eval (phiU hπ hf v) α` exactly, for `α` a nonzero element of `piTorsion hπ hf
1` — as the missing step turning the quadratic *closeness* bound
`NonarchimedeanPowerSeriesEval.norm_eval_sub_coeff_one_mul_le` into an *exact* equality, and
flagged the required minimum-spacing fact as needing genuinely new ramification infrastructure.
`Langlands.LubinTateTorsionSpacing.norm_sub_eq_rpow_of_mem_piTorsion_one_ne_zero_of_ne` supplies
exactly that (built without any discriminant computation); this file assembles it with the
existing tail bound to close the factoring.

## Route

For `u, v : Oˣ` with `π ∣ ((u:O) - (v:O))` and `α` a nonzero element of `piTorsion hπ hf 1`:

* `A := eval (phiU hπ hf u) α`, `B := eval (phiU hπ hf v) α` both lie in `piTorsion hπ hf 1`
  (`mem_piTorsion_eval_phiU`).
* `‖A - algebraMap O K (u:O) * α‖ ≤ ‖α‖ ^ 2` and similarly for `B`, `v`
  (`norm_eval_sub_coeff_one_mul_le` + `coeff_one_phiU`).
* `‖algebraMap O K (u:O) * α - algebraMap O K (v:O) * α‖ ≤ c * ‖α‖` (`c := ‖algebraMap O K π‖`),
  since `(u:O) - (v:O)` is a multiple of `π`.
* Telescoping these three bounds gives `‖A - B‖ ≤ max (‖α‖ ^ 2) (c * ‖α‖) = c ^ (2/(q-1)) `combined
  with `c^(q/(q-1))`, both **strictly less** than the spacing value `‖α‖ = c ^ (1/(q-1))` (exponent
  arithmetic, needing only `residueCard O ≥ 2`, always true).
* If `A ≠ B`, `‖A - B‖` equals the spacing value exactly — either via
  `norm_sub_eq_rpow_of_mem_piTorsion_one_ne_zero_of_ne` (both nonzero) or via
  `norm_eq_rpow_of_mem_piTorsion_one_ne_zero` directly (one of them zero, so `‖A-B‖` is the other's
  own norm) — contradicting the strict bound above. Hence `A = B`.

## Main result

* `eval_phiU_eq_of_dvd_sub` : the mod-`π` factoring, exactly as sketched above.
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

/-- **The `Oˣ`-action on nonzero `π`-torsion factors through `(O/π)ˣ`.** `u ≡ v (mod π)` in `Oˣ`
implies `eval (phiU hπ hf u) α = eval (phiU hπ hf v) α` exactly, for `α` a nonzero element of
`piTorsion hπ hf 1`. See the module docstring for the route. -/
theorem eval_phiU_eq_of_dvd_sub (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]} {w : O⟦X⟧} (hw : IsUnit w)
    (heq : f = (P : O⟦X⟧) * w) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg2 : 2 ≤ P.natDegree) {u v : Oˣ} (huv : π ∣ ((u : O) - (v : O)))
    {α : K} (hα : α ∈ piTorsion (K := K) hπ hf 1) (hα0 : α ≠ 0) :
    eval (phiU hπ hf u) α = eval (phiU hπ hf v) α := by
  by_contra hne
  set c : ℝ := ‖algebraMap O K π‖ with hcdef
  set A : K := eval (phiU hπ hf u) α with hAdef
  set B : K := eval (phiU hπ hf v) α with hBdef
  have hαnorm : ‖α‖ < 1 := hα.1
  have hAmem : A ∈ piTorsion (K := K) hπ hf 1 := mem_piTorsion_eval_phiU hOK hπ hf 1 u hα
  have hBmem : B ∈ piTorsion (K := K) hπ hf 1 := mem_piTorsion_eval_phiU hOK hπ hf 1 v hα
  have hnormα : ‖α‖ = c ^ (1 / (P.divX.natDegree : ℝ)) :=
    norm_eq_rpow_of_mem_piTorsion_one_ne_zero hOK hπ hπnorm hf hw heq hPdist hPdeg2 hα hα0
  -- Step 1: `A`/`B` are within `‖α‖ ^ 2` of `algebraMap (u:O) * α` / `algebraMap (v:O) * α`.
  have huBound : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (phiU hπ hf u))‖ ≤ 1 := fun k ↦ hOK _
  have hvBound : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (phiU hπ hf v))‖ ≤ 1 := fun k ↦ hOK _
  have hstepA : ‖A - algebraMap O K (u : O) * α‖ ≤ ‖α‖ ^ 2 := by
    have := norm_eval_sub_coeff_one_mul_le huBound (constantCoeff_phiU hπ hf u) hαnorm
    rwa [coeff_one_phiU] at this
  have hstepB : ‖B - algebraMap O K (v : O) * α‖ ≤ ‖α‖ ^ 2 := by
    have := norm_eval_sub_coeff_one_mul_le hvBound (constantCoeff_phiU hπ hf v) hαnorm
    rwa [coeff_one_phiU] at this
  -- Step 2: `algebraMap (u:O) * α` and `algebraMap (v:O) * α` are within `c * ‖α‖` of each other.
  have hstepUV : ‖algebraMap O K (u : O) * α - algebraMap O K (v : O) * α‖ ≤ c * ‖α‖ := by
    obtain ⟨y, hy⟩ := huv
    have heqsub : algebraMap O K (u : O) * α - algebraMap O K (v : O) * α =
        algebraMap O K π * algebraMap O K y * α := by
      rw [← sub_mul, ← map_sub, hy, map_mul]
    rw [heqsub, hcdef]
    calc ‖algebraMap O K π * algebraMap O K y * α‖
        = ‖algebraMap O K π‖ * ‖algebraMap O K y‖ * ‖α‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖algebraMap O K π‖ * 1 * ‖α‖ := by
          gcongr
          exact hOK y
      _ = ‖algebraMap O K π‖ * ‖α‖ := by ring
  -- Step 3: telescope, then bound each piece strictly below the spacing value.
  have htri1 : ‖A - algebraMap O K (v : O) * α‖ ≤
      max (‖α‖ ^ 2) (c * ‖α‖) := by
    have heqsub : A - algebraMap O K (v : O) * α =
        (A - algebraMap O K (u : O) * α) +
          (algebraMap O K (u : O) * α - algebraMap O K (v : O) * α) := by ring
    rw [heqsub]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max hstepA hstepUV)
  have htri2 : ‖A - B‖ ≤ max (max (‖α‖ ^ 2) (c * ‖α‖)) (‖α‖ ^ 2) := by
    have heqsub : A - B = (A - algebraMap O K (v : O) * α) + (algebraMap O K (v : O) * α - B) :=
      by ring
    rw [heqsub]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max htri1 ?_)
    rwa [show algebraMap O K (v : O) * α - B = -(B - algebraMap O K (v : O) * α) by ring,
      norm_neg]
  have hinj : Function.Injective (algebraMap O K) := FaithfulSMul.algebraMap_injective O K
  have hc0 : 0 < c := by
    rw [hcdef, norm_pos_iff]
    exact (map_ne_zero_iff (algebraMap O K) hinj).mpr hπ.ne_zero
  have hc1 : c < 1 := hπnorm
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hw heq hf.1 hf.2.1 hPdist hPdeg2
  have hn0 : (0 : ℝ) < (P.divX.natDegree : ℝ) := by exact_mod_cast hQdeg
  have hsqlt : ‖α‖ ^ 2 < c ^ (1 / (P.divX.natDegree : ℝ)) := by
    rw [hnormα]
    have hexp : (1 / (P.divX.natDegree : ℝ)) < (2 / (P.divX.natDegree : ℝ)) := by
      gcongr; norm_num
    have hsq : (c ^ (1 / (P.divX.natDegree : ℝ))) ^ 2 = c ^ (2 / (P.divX.natDegree : ℝ)) := by
      rw [← Real.rpow_natCast (c ^ (1 / (P.divX.natDegree : ℝ))) 2, ← Real.rpow_mul hc0.le]
      congr 1; ring
    rw [hsq]
    exact Real.rpow_lt_rpow_of_exponent_gt hc0 hc1 hexp
  have hcαlt : c * ‖α‖ < c ^ (1 / (P.divX.natDegree : ℝ)) := by
    rw [hnormα]
    have hexp : (1 / (P.divX.natDegree : ℝ)) < (1 + 1 / (P.divX.natDegree : ℝ)) := by linarith
    have hcprod : c * c ^ (1 / (P.divX.natDegree : ℝ)) = c ^ (1 + 1 / (P.divX.natDegree : ℝ)) := by
      rw [Real.rpow_add hc0, Real.rpow_one]
    rw [hcprod]
    exact Real.rpow_lt_rpow_of_exponent_gt hc0 hc1 hexp
  have hboundstrict : ‖A - B‖ < c ^ (1 / (P.divX.natDegree : ℝ)) := by
    refine lt_of_le_of_lt htri2 ?_
    rw [max_lt_iff, max_lt_iff]
    exact ⟨⟨hsqlt, hcαlt⟩, hsqlt⟩
  -- Step 4: but `A ≠ B` forces `‖A - B‖` to equal the spacing value exactly.
  have hnormAB : ‖A - B‖ = c ^ (1 / (P.divX.natDegree : ℝ)) := by
    rcases eq_or_ne A 0 with hA0 | hA0
    · rcases eq_or_ne B 0 with hB0 | hB0
      · exact absurd (hA0.trans hB0.symm) hne
      · rw [hA0, zero_sub, norm_neg]
        exact norm_eq_rpow_of_mem_piTorsion_one_ne_zero hOK hπ hπnorm hf hw heq hPdist hPdeg2 hBmem hB0
    · rcases eq_or_ne B 0 with hB0 | hB0
      · rw [hB0, sub_zero]
        exact norm_eq_rpow_of_mem_piTorsion_one_ne_zero hOK hπ hπnorm hf hw heq hPdist hPdeg2 hAmem hA0
      · exact norm_sub_eq_rpow_of_mem_piTorsion_one_ne_zero_of_ne hOK hπ hπnorm hf hw heq hPdist
          hPdeg2 hAmem hA0 hBmem hB0 hne
  rw [hnormAB] at hboundstrict
  exact lt_irrefl _ hboundstrict

end LubinTate

end
