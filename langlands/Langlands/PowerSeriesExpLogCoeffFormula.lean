import Langlands.PowerSeriesExpLog
import Langlands.PowerSeriesCoeffPowTuple

/-!
# A closed-form finite formula for `exp A`'s and `log A`'s substitution coefficients

`PowerSeries.exp_sub_one_subst_log` (`Langlands.PowerSeriesExpLog`) proves the formal identity
`(exp A - 1).subst (log A) = X`. This file extracts, from that identity plus `coeff_subst'` and
`coeff_pow_eq_sum_antidiagonalTuple` (`Langlands.PowerSeriesCoeffPowTuple`), a closed finite-sum
formula for `∑ n ∈ range (m+1), coeff n (exp A) * coeff m (log A ^ n)` — the exact quantity a
convergent, degree-`m`-grouped sum of `exp`/`log` coefficients needs to match, to conclude
`exp(log(1+X)) = 1 + X` at a point.
-/

@[expose] public section

namespace PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- **`log A ^ n`'s coefficients below degree `n` vanish.** Since `log A` has zero constant term
(`constantCoeff_log`), `X ∣ log A`, hence `X ^ n ∣ (log A) ^ n`; `X_pow_dvd_iff` then forces every
coefficient below degree `n` to vanish. -/
theorem coeff_log_pow_eq_zero_of_lt {m n : ℕ} (hmn : m < n) :
    coeff m ((log A) ^ n) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr constantCoeff_log) n) m hmn

/-- **`exp A`'s formal substitution into `log A`, as a finite sum.** Rewrites `coeff_subst'`'s
`finsum` (over `d : ℕ`) as a `Finset.range (m + 1)` sum, using `coeff_log_pow_eq_zero_of_lt` to see
every term with `d > m` vanishes. -/
theorem coeff_exp_subst_log_eq_sum (m : ℕ) :
    coeff m ((exp A).subst (log A)) =
      ∑ n ∈ Finset.range (m + 1), coeff n (exp A) * coeff m ((log A) ^ n) := by
  rw [coeff_subst' HasSubst.log]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (m + 1))]
  · simp [smul_eq_mul]
  · intro n hn
    simp only [Function.mem_support] at hn
    by_contra hcon
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hcon
    exact hn (by rw [coeff_log_pow_eq_zero_of_lt hcon, smul_zero])

/-- **The closed form.** `coeff m (exp A .subst (log A))` is `1` at `m = 0` and `m = 1`, and `0`
otherwise — from `exp_sub_one_subst_log` (`(exp A - 1).subst (log A) = X`) plus `1.subst (log A) = 1`
(substitution is a ring homomorphism). -/
theorem coeff_exp_subst_log (m : ℕ) :
    coeff m ((exp A).subst (log A)) = (if m = 0 then 1 else if m = 1 then 1 else 0) := by
  have hone : (1 : A⟦X⟧).subst (log A) = 1 := by
    rw [← coe_substAlgHom HasSubst.log, map_one]
  have hsplit : (exp A).subst (log A) = X + 1 := by
    have h := exp_sub_one_subst_log A
    rw [subst_sub HasSubst.log, hone] at h
    exact sub_eq_iff_eq_add.mp h
  rw [hsplit, map_add, coeff_X, coeff_one]
  rcases eq_or_ne m 0 with rfl | h0
  · simp
  · rcases eq_or_ne m 1 with rfl | h1
    · simp
    · simp [h0, h1]

/-- **The finite-sum closed form.** Combining `coeff_exp_subst_log_eq_sum` and
`coeff_exp_subst_log`: `∑ n ∈ range (m+1), coeff n (exp A) * coeff m (log A ^ n)` is `1` at `m = 0`
and `m = 1`, and `0` otherwise. -/
theorem sum_coeff_exp_mul_coeff_log_pow (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), coeff n (exp A) * coeff m ((log A) ^ n) =
      (if m = 0 then 1 else if m = 1 then 1 else 0) := by
  rw [← coeff_exp_subst_log_eq_sum, coeff_exp_subst_log]

end PowerSeries
