import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monic

/-!
# The exact norm of a root of an Eisenstein-shaped polynomial

Let `L` be a nonarchimedean normed field and `p : L[X]` monic of degree `n ≥ 1` whose coefficients
below the leading one all have norm `≤ c`, with the constant coefficient of norm *exactly* `c`, for
some `0 < c < 1` — the Eisenstein shape. Then **every root `α` of `p` in `L` satisfies
`‖α‖ ^ n = c` exactly**, hence `‖α‖ = c ^ (1 / n : ℝ)`, and in particular `‖α‖ < 1`.

This is the Newton-polygon computation for an Eisenstein polygon, in the one case where the polygon
is a single segment and no general Newton-polygon machinery is needed. The whole argument is three
applications of the ultrametric inequality to the two rearrangements of `p.eval α = 0`:

* `α ^ n = -∑_{i < n} p_i α ^ i`, giving `‖α‖ < 1` (else the `i = n - 1` term dominates and forces
  `‖α‖ ≤ c < 1`) and then `‖α‖ ^ n ≤ c` (with `‖α‖ < 1`, `‖p_i α ^ i‖ ≤ c` for every `i < n`);
* `p_0 = -(α ^ n + ∑_{1 ≤ i < n} p_i α ^ i)`, giving `c ≤ ‖α‖ ^ n` — every term of the inner sum has
  norm `≤ c ‖α‖ < c`, so the ultrametric bound `c = ‖p_0‖ ≤ max (‖α‖ ^ n) (…)` can only be met by
  the `α ^ n` term.

## Relation to `spectralNorm`

`Mathlib.Analysis.Normed.Unbundled.SpectralNorm` computes the same quantity by a different route
(`spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`, via the minimal polynomial), packaged for this
repo as `Langlands.spectralNorm_eq_norm_coeff_zero_rpow_of_aeval_eq_zero`. That route needs strictly
more: the polynomial must be **irreducible over a complete base field `K`**, with `L / K` algebraic,
so that it can be identified with `minpoly K α`. Those hypotheses fail exactly when `L` is large
enough for `p` to split — the case of interest for a splitting-field construction.

The lemmas here need **no base field, no completeness, no algebraicity, and no irreducibility** —
only the ultrametric inequality on `L` itself. That is what makes them usable *inside* a splitting
field of `p`, where `p` is by construction not irreducible.

## Main results

* `Polynomial.norm_lt_one_of_isEisensteinShape_of_root` : a root of an Eisenstein-shaped monic
  polynomial lies in the open unit ball.
* `Polynomial.norm_pow_natDegree_eq_of_isEisensteinShape_of_root` : `‖α‖ ^ p.natDegree = c`, exactly.
* `Polynomial.norm_eq_rpow_of_isEisensteinShape_of_root` : the same in `rpow` form,
  `‖α‖ = c ^ (1 / p.natDegree : ℝ)`.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace Polynomial

variable {L : Type*} [NormedField L] [IsUltrametricDist L] {p : L[X]} {c : ℝ}

omit [IsUltrametricDist L] in
/-- The rearrangement `α ^ n = -∑_{i < n} p_i α ^ i` of `p.eval α = 0`, for `p` monic of degree
`n`. -/
theorem pow_natDegree_eq_neg_sum_of_monic_of_root (hmonic : p.Monic) {α : L}
    (hα : p.eval α = 0) :
    α ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, p.coeff i * α ^ i := by
  have hev : (∑ i ∈ Finset.range p.natDegree, p.coeff i * α ^ i) + α ^ p.natDegree = 0 := by
    have h := (eval_eq_sum_range (p := p) α).symm.trans hα
    rwa [Finset.sum_range_succ, hmonic.coeff_natDegree, one_mul] at h
  linear_combination hev

/-- **A root of an Eisenstein-shaped monic polynomial lies in the open unit ball.** If `1 ≤ ‖α‖`,
the ultrametric bound on `α ^ n = -∑_{i < n} p_i α ^ i` is dominated by the `i = n - 1` term, giving
`‖α‖ ^ n ≤ c ‖α‖ ^ (n - 1)` and hence `‖α‖ ≤ c < 1` — a contradiction. -/
theorem norm_lt_one_of_isEisensteinShape_of_root (hmonic : p.Monic) (hdeg : 0 < p.natDegree)
    (hc1 : c < 1) (hc0 : 0 < c) (hweak : ∀ i < p.natDegree, ‖p.coeff i‖ ≤ c)
    {α : L} (hα : p.eval α = 0) : ‖α‖ < 1 := by
  by_contra hge
  rw [not_lt] at hge
  have hne : (Finset.range p.natDegree).Nonempty := Finset.nonempty_range_iff.mpr hdeg.ne'
  obtain ⟨i, hi, hile⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
    (fun i ↦ p.coeff i * α ^ i)
  rw [Finset.mem_range] at hi
  have hnormkey : ‖α‖ ^ p.natDegree = ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * α ^ i‖ := by
    rw [← norm_pow, pow_natDegree_eq_neg_sum_of_monic_of_root hmonic hα, norm_neg]
  have hstep : ‖α‖ ^ p.natDegree ≤ c * ‖α‖ ^ (p.natDegree - 1) := by
    rw [hnormkey]
    refine hile.trans ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hweak i hi) (pow_le_pow_right₀ hge (by omega)) (by positivity) hc0.le
  have hαpos : (0 : ℝ) < ‖α‖ := lt_of_lt_of_le one_pos hge
  have hApos : (0 : ℝ) < ‖α‖ ^ (p.natDegree - 1) := by positivity
  have hsplit : ‖α‖ ^ p.natDegree = ‖α‖ * ‖α‖ ^ (p.natDegree - 1) := by
    conv_lhs => rw [show p.natDegree = 1 + (p.natDegree - 1) by omega]
    rw [pow_add, pow_one]
  rw [hsplit] at hstep
  have := le_of_mul_le_mul_right (by linarith : ‖α‖ * ‖α‖ ^ (p.natDegree - 1) ≤
    c * ‖α‖ ^ (p.natDegree - 1)) hApos
  linarith

/-- **The exact norm of a root of an Eisenstein-shaped monic polynomial: `‖α‖ ^ n = c`.** See the
module docstring for the two-rearrangement argument. -/
theorem norm_pow_natDegree_eq_of_isEisensteinShape_of_root (hmonic : p.Monic)
    (hdeg : 0 < p.natDegree) (hc1 : c < 1) (hc0 : 0 < c) (hc0eq : ‖p.coeff 0‖ = c)
    (hweak : ∀ i < p.natDegree, ‖p.coeff i‖ ≤ c) {α : L} (hα : p.eval α = 0) :
    ‖α‖ ^ p.natDegree = c := by
  have hlt1 : ‖α‖ < 1 :=
    norm_lt_one_of_isEisensteinShape_of_root hmonic hdeg hc1 hc0 hweak hα
  have hne : (Finset.range p.natDegree).Nonempty := Finset.nonempty_range_iff.mpr hdeg.ne'
  have hnormkey : ‖α‖ ^ p.natDegree = ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * α ^ i‖ := by
    rw [← norm_pow, pow_natDegree_eq_neg_sum_of_monic_of_root hmonic hα, norm_neg]
  -- Upper bound: with `‖α‖ < 1`, every term of the sum has norm at most `c`.
  have hle : ‖α‖ ^ p.natDegree ≤ c := by
    obtain ⟨i, hi, hile⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
      (fun i ↦ p.coeff i * α ^ i)
    rw [Finset.mem_range] at hi
    rw [hnormkey]
    refine hile.trans ?_
    rw [norm_mul, norm_pow]
    calc ‖p.coeff i‖ * ‖α‖ ^ i ≤ c * 1 :=
          mul_le_mul (hweak i hi) (pow_le_one₀ (norm_nonneg _) hlt1.le) (by positivity) hc0.le
      _ = c := mul_one c
  -- Lower bound: peel off the constant term and dominate the rest by `c ‖α‖ < c`.
  obtain ⟨m, hm⟩ : ∃ m, p.natDegree = m + 1 := ⟨p.natDegree - 1, by omega⟩
  set T : L := ∑ k ∈ Finset.range m, p.coeff (k + 1) * α ^ (k + 1) with hTdef
  have hsplit : (∑ i ∈ Finset.range p.natDegree, p.coeff i * α ^ i) = T + p.coeff 0 := by
    rw [hTdef, hm, Finset.sum_range_succ' (fun i ↦ p.coeff i * α ^ i) m, pow_zero, mul_one]
  have hc0expr : p.coeff 0 = -(α ^ p.natDegree + T) := by
    have := pow_natDegree_eq_neg_sum_of_monic_of_root hmonic hα
    rw [hsplit] at this
    linear_combination this
  have hTlt : ‖T‖ < c := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · simp [hTdef, hm0, hc0]
    · obtain ⟨k, hk, hkle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
        (Finset.nonempty_range_iff.mpr hmpos.ne') (fun k ↦ p.coeff (k + 1) * α ^ (k + 1))
      rw [Finset.mem_range] at hk
      refine lt_of_le_of_lt hkle ?_
      rw [norm_mul, norm_pow]
      calc ‖p.coeff (k + 1)‖ * ‖α‖ ^ (k + 1)
          ≤ c * ‖α‖ ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (hweak (k + 1) (by omega)) (by positivity)
        _ < c * 1 := by
            exact mul_lt_mul_of_pos_left
              (pow_lt_one₀ (norm_nonneg _) hlt1 (Nat.succ_ne_zero k)) hc0
        _ = c := mul_one c
  have hmax : c ≤ max (‖α‖ ^ p.natDegree) ‖T‖ := by
    rw [← hc0eq, hc0expr, norm_neg, ← norm_pow]
    exact IsUltrametricDist.norm_add_le_max _ _
  have hge : c ≤ ‖α‖ ^ p.natDegree := by
    rcases max_choice (‖α‖ ^ p.natDegree) ‖T‖ with h | h <;> rw [h] at hmax
    · exact hmax
    · linarith
  exact le_antisymm hle hge

/-- **The exact norm of a root of an Eisenstein-shaped monic polynomial, `rpow` form:
`‖α‖ = c ^ (1 / n : ℝ)`.** -/
theorem norm_eq_rpow_of_isEisensteinShape_of_root (hmonic : p.Monic) (hdeg : 0 < p.natDegree)
    (hc1 : c < 1) (hc0 : 0 < c) (hc0eq : ‖p.coeff 0‖ = c)
    (hweak : ∀ i < p.natDegree, ‖p.coeff i‖ ≤ c) {α : L} (hα : p.eval α = 0) :
    ‖α‖ = c ^ (1 / (p.natDegree : ℝ)) := by
  have hpow := norm_pow_natDegree_eq_of_isEisensteinShape_of_root hmonic hdeg hc1 hc0 hc0eq hweak hα
  rw [← hpow, one_div, Real.pow_rpow_inv_natCast (norm_nonneg α) hdeg.ne']

end Polynomial

end
