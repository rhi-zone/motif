import Langlands.NonarchimedeanExpLogFlatHasSum
import Langlands.PowerSeriesExpLogCoeffFormula
import Langlands.PowerSeriesCoeffPowTuple

/-!
# Degree-`m` matching: `exp hnorm (log hnorm x) = 1 + x`

This file closes steps (ii)–(iv) of the four-step assembly `ROADMAP.md`'s tenth/eleventh/twelfth
passes describe for the `exp`/`log` mutual-inverse identity, completing item 2 of the wild-case's
five-item list. Step (i) (`hasSum_coeff_exp_log`, `Langlands.NonarchimedeanExpLogFlatHasSum`) gives a
flat `HasSum` over `Σ n, Fin n → ℕ` for `exp hnorm (log hnorm x)`. This file:

* regroups that flat sum by total `x`-degree `m := ∑ i, g i` (`HasSum.tsum_fiberwise`, a ready-made
  Mathlib regrouping tool for `HasSum` in a complete Hausdorff uniform additive group — applicable
  here since `K` is such a group, with no extra rearrangement hypothesis needed beyond the flat
  `HasSum` itself);
* identifies each degree-`m` fiber's sum with `x ^ m * (coefficient of X^m in exp.subst(log))`,
  matching the convergent tuple-indexed grouping against `PowerSeries.coeff_pow_eq_sum_antidiagonalTuple`
  and `PowerSeries.sum_coeff_exp_mul_coeff_log_pow` (`Langlands.PowerSeriesExpLogCoeffFormula`);
* concludes, via `HasSum.unique`, that `exp hnorm (log hnorm x)` equals the sum of the degree-graded
  series `∑' m, x^m * (1 if m ∈ {0,1} else 0)`, which is a finite sum equal to `1 + x`.
-/

@[expose] public section

namespace NonarchimedeanExponential

open Filter Topology

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]
variable {p : ℕ} [hp : Fact p.Prime]

/-! ## The total-degree projection and its associated finite `Finset` -/

/-- **The total `x`-degree of a flat index** `⟨n, g⟩ : Σ n, Fin n → ℕ`. -/
def totalDegree (q : Σ _n : ℕ, Fin _n → ℕ) : ℕ := ∑ i, q.2 i

/-- **The finite `Finset` of flat indices of total degree `m` with length `≤ m`.** Every index
`⟨n, g⟩` with `totalDegree ⟨n, g⟩ = m` and `n > m` contributes `0` to the flat `exp`/`log` family
(`apply_eq_zero_of_totalDegree_eq_of_lt`, below), so this `Finset` captures every potentially-nonzero
index of a given total degree. -/
def degreeFinset (m : ℕ) : Finset (Σ _n : ℕ, Fin _n → ℕ) :=
  (Finset.range (m + 1)).sigma (fun n => Finset.Nat.antidiagonalTuple n m)

theorem mem_degreeFinset {m : ℕ} {q : Σ _n : ℕ, Fin _n → ℕ} :
    q ∈ degreeFinset m ↔ q.1 ≤ m ∧ totalDegree q = m := by
  rw [degreeFinset, Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple]
  exact and_congr Nat.lt_succ_iff Iff.rfl

/-! ## Vanishing outside `degreeFinset` within a fixed-degree fiber -/

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **A flat index of total degree `m` but length `n > m` contributes `0`.** By pigeonhole, if every
entry of `g : Fin n → ℕ` were `≥ 1` then `∑ i, g i ≥ n > m`, contradicting `∑ i, g i = m`; so some
entry is `0`, making the `log`-coefficient factor `0` (`coeff 0 (log K) = 0`) and hence the whole
product `0`. Same case-split as `norm_coeff_exp_mul_prod_le`'s `hz` branch
(`Langlands.NonarchimedeanExpLogCofinite`), stated here as its own equality fact rather than a norm
bound. -/
theorem apply_eq_zero_of_totalDegree_eq_of_lt {x : K} {m n : ℕ} (hmn : m < n) {g : Fin n → ℕ}
    (hg : ∑ i, g i = m) :
    PowerSeries.coeff n (PowerSeries.exp K) *
        ∏ i, (PowerSeries.coeff (g i) (PowerSeries.log K) * x ^ (g i)) = 0 := by
  have hz : ∃ i, g i = 0 := by
    by_contra hc
    push Not at hc
    have hnle : n ≤ ∑ i, g i := by
      calc n = ∑ _i : Fin n, 1 := by simp
        _ ≤ ∑ i, g i := Finset.sum_le_sum (fun i _ => Nat.one_le_iff_ne_zero.mpr (hc i))
    omega
  obtain ⟨i, hi⟩ := hz
  have hzero : (∏ j, (PowerSeries.coeff (g j) (PowerSeries.log K) * x ^ (g j))) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [hi]
    simp [PowerSeries.coeff_log]
  rw [hzero, mul_zero]

/-! ## The finite degree-`m` sum, in closed form -/

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The finite degree-`m` sum, computed exactly.** A purely algebraic identity (no convergence
hypothesis needed): summing the flat `exp`/`log` family over `degreeFinset m` gives
`x ^ m` times `1` if `m ∈ {0, 1}` and `0` otherwise — matching, term by term, the convergent
tuple-indexed grouping (via `Finset.sum_sigma'`, `Finset.prod_mul_distrib`,
`Finset.prod_pow_eq_pow_sum`) against `PowerSeries.coeff_pow_eq_sum_antidiagonalTuple`'s tuple-sum
formula for `coeff m (log K ^ n)` and `PowerSeries.sum_coeff_exp_mul_coeff_log_pow`'s closed form for
`∑ n, coeff n (exp K) * coeff m (log K ^ n)`. -/
theorem sum_degreeFinset_eq (x : K) (m : ℕ) :
    ∑ q ∈ degreeFinset m,
        (PowerSeries.coeff q.1 (PowerSeries.exp K) *
          ∏ i, (PowerSeries.coeff (q.2 i) (PowerSeries.log K) * x ^ (q.2 i)))
      = x ^ m * (if m = 0 then (1 : K) else if m = 1 then 1 else 0) := by
  rw [degreeFinset, Finset.sum_sigma]
  have hterm : ∀ n ∈ Finset.range (m + 1),
      ∑ g ∈ Finset.Nat.antidiagonalTuple n m,
          (PowerSeries.coeff n (PowerSeries.exp K) *
            ∏ i, (PowerSeries.coeff (g i) (PowerSeries.log K) * x ^ (g i)))
        = x ^ m * (PowerSeries.coeff n (PowerSeries.exp K) *
            PowerSeries.coeff m ((PowerSeries.log K) ^ n)) := by
    intro n _
    have hstep : ∀ g ∈ Finset.Nat.antidiagonalTuple n m,
        (PowerSeries.coeff n (PowerSeries.exp K) *
            ∏ i, (PowerSeries.coeff (g i) (PowerSeries.log K) * x ^ (g i)))
          = x ^ m * (PowerSeries.coeff n (PowerSeries.exp K) *
              ∏ i, PowerSeries.coeff (g i) (PowerSeries.log K)) := by
      intro g hg
      rw [Finset.Nat.mem_antidiagonalTuple] at hg
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hg]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, ← Finset.mul_sum,
      ← PowerSeries.coeff_pow_eq_sum_antidiagonalTuple]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    PowerSeries.sum_coeff_exp_mul_coeff_log_pow]

/-! ## The per-degree fiber `HasSum` -/

omit [IsUltrametricDist K] [CompleteSpace K] in
set_option maxHeartbeats 1000000 in
/-- **The degree-`m` fiber, summed.** The flat family, restricted to indices of total degree `m`,
has `HasSum` to `x ^ m * (1 if m ∈ {0,1} else 0)`: every index outside `degreeFinset m` within this
fiber contributes `0` (`apply_eq_zero_of_totalDegree_eq_of_lt`), so `hasSum_sum_of_ne_finset_zero`
reduces the fiber sum to the finite sum over `degreeFinset m`, computed by `sum_degreeFinset_eq`. -/
theorem hasSum_fiber_totalDegree (x : K) (m : ℕ) :
    HasSum (fun q : totalDegree ⁻¹' {m} =>
        PowerSeries.coeff q.1.1 (PowerSeries.exp K) *
          ∏ i, (PowerSeries.coeff (q.1.2 i) (PowerSeries.log K) * x ^ (q.1.2 i)))
      (x ^ m * (if m = 0 then (1 : K) else if m = 1 then 1 else 0)) := by
  set f : (Σ _n : ℕ, Fin _n → ℕ) → K := fun q =>
    PowerSeries.coeff q.1 (PowerSeries.exp K) *
      ∏ i, (PowerSeries.coeff (q.2 i) (PowerSeries.log K) * x ^ (q.2 i)) with hfdef
  have hvanish : ∀ q ∉ degreeFinset m, (Set.indicator (totalDegree ⁻¹' {m}) f) q = 0 := by
    intro q hq
    by_cases hmem : q ∈ (totalDegree ⁻¹' {m} : Set (Σ _n : ℕ, Fin _n → ℕ))
    · have hmeq : totalDegree q = m := hmem
      have hlt : m < q.1 := by
        rcases lt_or_ge m q.1 with h | h
        · exact h
        · exact absurd (mem_degreeFinset.mpr ⟨h, hmeq⟩) hq
      rw [Set.indicator_of_mem hmem]
      show PowerSeries.coeff q.1 (PowerSeries.exp K) *
          ∏ i, (PowerSeries.coeff (q.2 i) (PowerSeries.log K) * x ^ (q.2 i)) = 0
      exact apply_eq_zero_of_totalDegree_eq_of_lt hlt hmeq
    · exact Set.indicator_of_notMem hmem f
  have hsum : HasSum (Set.indicator (totalDegree ⁻¹' {m}) f)
      (∑ q ∈ degreeFinset m, (Set.indicator (totalDegree ⁻¹' {m}) f) q) :=
    hasSum_sum_of_ne_finset_zero hvanish
  have heq : ∑ q ∈ degreeFinset m, (Set.indicator (totalDegree ⁻¹' {m}) f) q
      = x ^ m * (if m = 0 then (1 : K) else if m = 1 then 1 else 0) := by
    have hmemfib : ∀ q ∈ degreeFinset m, q ∈ (totalDegree ⁻¹' {m} : Set (Σ _n : ℕ, Fin _n → ℕ)) :=
      fun q hq => Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (mem_degreeFinset.mp hq).2)
    rw [Finset.sum_congr rfl (fun q hq => Set.indicator_of_mem (hmemfib q hq) f)]
    exact sum_degreeFinset_eq x m
  rw [heq] at hsum
  exact hasSum_subtype_iff_indicator.mpr hsum

/-! ## The main result -/

/-- **The degree-graded `HasSum`.** Regrouping the flat `HasSum` `hasSum_coeff_exp_log` by total
`x`-degree (`HasSum.tsum_fiberwise`, valid since `K` is a complete Hausdorff uniform additive group)
and identifying each fiber's sum via `hasSum_fiber_totalDegree`, the degree-graded series
`fun m => x ^ m * (1 if m ∈ {0,1} else 0)` sums to `exp hnorm (log hnorm x)`. -/
theorem hasSum_degree_graded (hnorm : ‖(p : K)‖ < 1) {x : K}
    (hx : ‖x‖ < expLogCompositionRadius K p) :
    HasSum (fun m : ℕ => x ^ m * (if m = 0 then (1 : K) else if m = 1 then 1 else 0))
      (exp hnorm (log hnorm x)) := by
  have hflat := hasSum_coeff_exp_log hnorm hx
  have hfib := hflat.tsum_fiberwise totalDegree
  have heq : ∀ m : ℕ,
      (∑' q : totalDegree ⁻¹' {m}, (fun q : Σ _n : ℕ, Fin _n → ℕ =>
          PowerSeries.coeff q.1 (PowerSeries.exp K) *
            ∏ i, (PowerSeries.coeff (q.2 i) (PowerSeries.log K) * x ^ (q.2 i))) (q : _))
        = x ^ m * (if m = 0 then (1 : K) else if m = 1 then 1 else 0) :=
    fun m => (hasSum_fiber_totalDegree x m).tsum_eq
  simpa only [heq] using hfib

/-- **`exp hnorm (log hnorm x) = 1 + x`, the convergent mutual-inverse identity.** The degree-graded
series `hasSum_degree_graded` produces has finite support `{0, 1}` (every other term vanishes by
construction), so it also, directly, sums to `1 + x`; uniqueness of `HasSum` in a Hausdorff space
identifies the two sums. This closes item 2 of the wild-case's five-item list: the mutual-inverse
relationship between the convergent `exp` and `log`. -/
theorem exp_log_eq_one_add (hnorm : ‖(p : K)‖ < 1) {x : K}
    (hx : ‖x‖ < expLogCompositionRadius K p) :
    exp hnorm (log hnorm x) = 1 + x := by
  have hgraded := hasSum_degree_graded hnorm hx
  have htarget : HasSum (fun m : ℕ => x ^ m * (if m = 0 then (1 : K) else if m = 1 then 1 else 0))
      (1 + x) := by
    have hvanish : ∀ m ∉ ({0, 1} : Finset ℕ),
        x ^ m * (if m = 0 then (1 : K) else if m = 1 then 1 else 0) = 0 := by
      intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      push Not at hm
      simp [hm.1, hm.2]
    have hval : ∑ m ∈ ({0, 1} : Finset ℕ),
        x ^ m * (if m = 0 then (1 : K) else if m = 1 then 1 else 0) = 1 + x := by
      simp
    rw [← hval]
    exact hasSum_sum_of_ne_finset_zero hvanish
  exact hgraded.unique htarget

end NonarchimedeanExponential
