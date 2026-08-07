import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Log
import Langlands.NonarchimedeanExponentialHasSum

/-!
# The flat `exp`/`log` composite family is `cofinite`-null

`Langlands.NonarchimedeanSigmaSummability`'s `HasSum.sigma_of_isUltrametricDist` flattens the outer
`HasSum` from `hasSum_coeff_exp` (over `n`) and the inner `HasSum`s from `HasSum.pow_of_nonarchimedean`
applied to `hasSum_coeff_log` (over tuples `g : Fin n → ℕ`) into one flat `HasSum`, provided the flat
family `f ⟨n, g⟩ := coeff n (exp K) * ∏ i, (coeff (g i) (log K) * x ^ (g i))` (on `Σ n, Fin n → ℕ`)
tends to `0` along `cofinite`. `ROADMAP.md`'s eleventh pass found this precise gap and diagnosed why
the crude per-`n` bound `‖f ⟨n, g⟩‖ ≤ ‖c_n‖ * s ^ n` alone cannot prove it: the fiber `Fin n → ℕ` over a
fixed `n` is itself infinite, and that bound is constant across the fiber. This file closes the gap.

## Route

1. `norm_coeff_log_mul_pow_le`: a per-index bound `‖coeff m (log K) * x ^ m‖ ≤ r ^ m` (`r := ‖x‖/‖p‖`),
   uniform in `m` including `m = 0` (where the left side is literally `0`, since `coeff 0 (log K) = 0`).
2. `norm_prod_coeff_log_mul_pow_le`: multiplying `n` such bounds gives the *tight* product bound
   `‖∏ i, (coeff (g i) (log K) * x ^ (g i))‖ ≤ r ^ (∑ i, g i)`, decaying in the tuple's actual total
   degree, not just its length.
3. `norm_coeff_exp_mul_prod_le`: combined with `‖c_n‖ ≥ 0`, and using that a product with any zero
   factor is `0` while a product with every factor nonzero has total degree `≥ n`, this tight bound
   forces the *coarse* per-`n` bound `‖f ⟨n, g⟩‖ ≤ ‖c_n‖ * r ^ n` to hold after all, resolving the
   eleventh pass's apparent obstruction (the coarse bound is valid; it merely isn't tight enough on its
   own to see the fiber's finiteness — the tight bound (2) is what does that work).
4. `norm_coeff_exp_le`, `div_norm_lt_convergenceRadius`, `tendsto_norm_coeff_exp_mul_pow_atTop_zero`:
   `‖c_n‖ * r ^ n → 0` as `n → ∞`, using `norm_pow_div_factorial_le` at `x := 1` to bound `‖c_n‖` and the
   domain-compatibility fact (already proved for `norm_log_lt_convergenceRadius`) that
   `r = ‖x‖ / ‖p‖ < convergenceRadius K p` under this file's hypothesis `‖x‖ < expLogCompositionRadius K p`.
5. `finite_setOf_ge_of_tendsto_zero`, `finite_setOf_sum_mem_of_finite`: two general-purpose finiteness
   facts (a real sequence tending to `0` is `≥ ε` only finitely often; the set of tuples whose entries
   sum into a finite set is itself finite), assembled in `tendsto_cofinite_exp_log_flatSum` into: for
   `ε > 0`, only finitely many `n` have `‖c_n‖ * r ^ n ≥ ε` (step 4), and for each such `n` only finitely
   many tuples `g` have total degree small enough for `‖c_n‖ * r ^ (∑ g i) ≥ ε` to be possible (step 2 +
   step 5) — so the whole "bad set" `{q | ε ≤ ‖f q‖}` is a finite union of finite sets, hence finite.

## What this does not close

This file only proves the `Tendsto f cofinite (nhds 0)` prerequisite for step (i) of the assembly
`ROADMAP.md`'s tenth/eleventh passes describe. It does not build the flat `HasSum` itself (applying
`HasSum.sigma_of_isUltrametricDist`) or attempt steps (ii)–(iv) (matching the flattened sum's degree-`m`
slice against `PowerSeries.coeff_subst'`, invoking `PowerSeries.exp_sub_one_subst_log`, concluding via
uniqueness of `HasSum`) — see `ROADMAP.md`'s pass log for the current state of that remaining assembly.
-/

@[expose] public section

namespace NonarchimedeanExponential

open Filter Topology

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]
variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Per-term and per-tuple bounds on the `log`-coefficient family -/

omit [CompleteSpace K] in
/-- **A uniform per-index bound on the `log`-coefficient terms.** For every `m : ℕ` (including
`m = 0`, where the left side is literally `0` since `coeff 0 (log K) = 0`),
`‖coeff m (log K) * x ^ m‖ ≤ (‖x‖ / ‖p‖) ^ m`. This is exactly the bound `hasSum_coeff_log`'s and
`norm_log_le`'s proofs use internally at shifted indices `m = k + 1`, restated here as its own
`m`-indexed statement (duplicated rather than refactored out of those already-closed proofs). -/
theorem norm_coeff_log_mul_pow_le (hnorm : ‖(p : K)‖ < 1) (x : K) (m : ℕ) :
    ‖PowerSeries.coeff m (PowerSeries.log K) * x ^ m‖ ≤ (‖x‖ / ‖(p : K)‖) ^ m := by
  cases m with
  | zero => simp [PowerSeries.coeff_log]
  | succ n =>
    have hshift : PowerSeries.coeff (n + 1) (PowerSeries.log K) * x ^ (n + 1)
        = (-1 : K) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : K) := by
      rw [PowerSeries.coeff_log, if_neg n.succ_ne_zero]
      have hpow : ((-1 : ℚ) ^ (n + 1 + 1)) = (-1 : ℚ) ^ n := by ring
      rw [hpow, map_div₀, map_pow, map_neg, map_one, map_natCast]
      ring
    rw [hshift]
    have hneg1 : ‖(-1 : K) ^ n‖ = 1 := by rw [norm_pow, norm_neg, norm_one, one_pow]
    calc ‖(-1 : K) ^ n * x ^ (n + 1) / ((n + 1 : ℕ) : K)‖
        = ‖x ^ (n + 1) / ((n + 1 : ℕ) : K)‖ := by
          rw [norm_div, norm_mul, hneg1, one_mul, ← norm_div]
      _ ≤ (‖x‖ / ‖(p : K)‖) ^ (n + 1) := norm_pow_div_natCast_le hnorm x n.succ_ne_zero

omit [CompleteSpace K] in
/-- **The tight product bound.** For a tuple `g : Fin n → ℕ`,
`‖∏ i, (coeff (g i) (log K) * x ^ (g i))‖ ≤ (‖x‖ / ‖p‖) ^ (∑ i, g i)` — decaying in the tuple's
*actual* total degree `∑ i, g i`, not just its length `n`. From `norm_coeff_log_mul_pow_le` termwise,
via multiplicativity of the norm over a finite product (`norm_prod`) and `∏ i, a ^ f i = a ^ ∑ i, f i`
(`Finset.prod_pow_eq_pow_sum`). -/
theorem norm_prod_coeff_log_mul_pow_le (hnorm : ‖(p : K)‖ < 1) (x : K) {n : ℕ} (g : Fin n → ℕ) :
    ‖∏ i, (PowerSeries.coeff (g i) (PowerSeries.log K) * x ^ (g i))‖
      ≤ (‖x‖ / ‖(p : K)‖) ^ (∑ i, g i) := by
  rw [norm_prod]
  calc ∏ i : Fin n, ‖PowerSeries.coeff (g i) (PowerSeries.log K) * x ^ (g i)‖
      ≤ ∏ i : Fin n, (‖x‖ / ‖(p : K)‖) ^ (g i) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _)
          (fun i _ => norm_coeff_log_mul_pow_le hnorm x (g i))
    _ = (‖x‖ / ‖(p : K)‖) ^ (∑ i, g i) := Finset.prod_pow_eq_pow_sum _ _ _

omit [CompleteSpace K] in
/-- **The coarse per-`n` bound, valid after all.** For `x` with `‖x‖ < logConvergenceRadius K p`
(so `r := ‖x‖ / ‖p‖ < 1`) and any `c : K`,
`‖c * ∏ i, (coeff (g i) (log K) * x ^ (g i))‖ ≤ ‖c‖ * r ^ n`. If some `g i = 0` the product is
literally `0` (`coeff 0 (log K) = 0`), so the bound is trivial; otherwise every `g i ≥ 1`, forcing
`∑ i, g i ≥ n`, and monotonicity of `r ^ ·` (decreasing, since `0 ≤ r < 1`) turns the tight bound
`norm_prod_coeff_log_mul_pow_le` into this coarser one. This resolves `ROADMAP.md`'s eleventh-pass
finding: the coarse bound is correct, it just isn't by itself enough to see the fiber's finiteness. -/
theorem norm_coeff_exp_mul_prod_le (hnorm : ‖(p : K)‖ < 1) {x : K}
    (hx : ‖x‖ < logConvergenceRadius K p) {n : ℕ} (g : Fin n → ℕ) (c : K) :
    ‖c * ∏ i, (PowerSeries.coeff (g i) (PowerSeries.log K) * x ^ (g i))‖
      ≤ ‖c‖ * (‖x‖ / ‖(p : K)‖) ^ n := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  set r := ‖x‖ / ‖(p : K)‖ with hrdef
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg x) hp0.le
  have hr1 : r < 1 := by rw [hrdef, div_lt_one hp0]; exact hx
  by_cases hz : ∃ i, g i = 0
  · obtain ⟨i, hi⟩ := hz
    have hzero : (∏ j, (PowerSeries.coeff (g j) (PowerSeries.log K) * x ^ (g j))) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [hi]
      simp [PowerSeries.coeff_log]
    rw [hzero, mul_zero, norm_zero]
    positivity
  · push Not at hz
    have hnge : n ≤ ∑ i, g i := by
      calc n = ∑ _i : Fin n, 1 := by simp
        _ ≤ ∑ i, g i := Finset.sum_le_sum (fun i _ => Nat.one_le_iff_ne_zero.mpr (hz i))
    calc ‖c * ∏ i, (PowerSeries.coeff (g i) (PowerSeries.log K) * x ^ (g i))‖
        = ‖c‖ * ‖∏ i, (PowerSeries.coeff (g i) (PowerSeries.log K) * x ^ (g i))‖ := norm_mul _ _
      _ ≤ ‖c‖ * r ^ (∑ i, g i) :=
          mul_le_mul_of_nonneg_left (norm_prod_coeff_log_mul_pow_le hnorm x g) (norm_nonneg c)
      _ ≤ ‖c‖ * r ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1.le hnge) (norm_nonneg c)

/-! ## `‖c_n‖ * r ^ n → 0` -/

omit [CompleteSpace K] in
/-- **A geometric bound on `exp`'s coefficients.** `‖coeff n (exp K)‖ ≤ (1 / convergenceRadius K p) ^ n`
— plug `x := 1` into `norm_pow_div_factorial_le` and identify `coeff n (exp K) = 1 ^ n / n !`. -/
theorem norm_coeff_exp_le (hnorm : ‖(p : K)‖ < 1) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.exp K)‖ ≤ (1 / convergenceRadius K p) ^ n := by
  have hcoeff : PowerSeries.coeff n (PowerSeries.exp K) = (1 : K) ^ n / (n.factorial : K) := by
    have hinv : (algebraMap ℚ K) (1 / (n.factorial : ℚ)) = ((n.factorial : K))⁻¹ := by
      rw [one_div, map_inv₀, map_natCast]
    rw [PowerSeries.coeff_exp, hinv, div_eq_mul_inv, one_pow, one_mul]
  rw [hcoeff]
  simpa [convergenceRadius] using norm_pow_div_factorial_le hnorm (1 : K) n

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The `exp`/`log` domain-compatibility ratio bound.** Under this file's standing hypothesis
`‖x‖ < expLogCompositionRadius K p`, the ratio `r := ‖x‖ / ‖p‖` itself lies strictly below
`convergenceRadius K p` — this is exactly the intermediate fact `norm_log_lt_convergenceRadius`'s proof
establishes on the way to bounding `‖log hnorm x‖`, extracted here as its own reusable statement. -/
theorem div_norm_lt_convergenceRadius (hnorm : ‖(p : K)‖ < 1) {x : K}
    (hx : ‖x‖ < expLogCompositionRadius K p) :
    ‖x‖ / ‖(p : K)‖ < convergenceRadius K p := by
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  have hp1 : ((p : ℝ) - 1) ≠ 0 := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    intro h; nlinarith
  rw [div_lt_iff₀ hp0]
  have hexp : (((p : ℝ) - 1)⁻¹) + 1 = (p : ℝ) / ((p : ℝ) - 1) := by
    rw [eq_div_iff hp1]; field_simp; ring
  have hcomb : ‖(p : K)‖ ^ (((p : ℝ) - 1)⁻¹) * ‖(p : K)‖ ^ (1 : ℝ)
      = ‖(p : K)‖ ^ ((p : ℝ) / ((p : ℝ) - 1)) := by
    rw [← Real.rpow_add hp0, hexp]
  rw [Real.rpow_one] at hcomb
  have heq : convergenceRadius K p * ‖(p : K)‖ = expLogCompositionRadius K p := by
    unfold convergenceRadius expLogCompositionRadius
    exact hcomb
  rwa [heq]

omit [CompleteSpace K] in
/-- **`‖c_n‖ * r ^ n → 0` as `n → ∞`.** Combining `norm_coeff_exp_le` with `r < convergenceRadius K p`
(`div_norm_lt_convergenceRadius`) bounds `‖c_n‖ * r ^ n ≤ (r / convergenceRadius K p) ^ n`, a genuine
geometric decay since `0 ≤ r / convergenceRadius K p < 1`. -/
theorem tendsto_norm_coeff_exp_mul_pow_atTop_zero (hnorm : ‖(p : K)‖ < 1) {x : K}
    (hx : ‖x‖ < expLogCompositionRadius K p) :
    Tendsto (fun n => ‖PowerSeries.coeff n (PowerSeries.exp K)‖ * (‖x‖ / ‖(p : K)‖) ^ n)
      atTop (nhds 0) := by
  set r := ‖x‖ / ‖(p : K)‖ with hrdef
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg x) (norm_nonneg _)
  have hrcr : r < convergenceRadius K p := div_norm_lt_convergenceRadius hnorm hx
  have hcr0 : 0 < convergenceRadius K p := Real.rpow_pos_of_pos norm_natCast_pos _
  have hratio0 : 0 ≤ r / convergenceRadius K p := div_nonneg hr0 hcr0.le
  have hratio1 : r / convergenceRadius K p < 1 := (div_lt_one hcr0).mpr hrcr
  have hbound : ∀ n, ‖PowerSeries.coeff n (PowerSeries.exp K)‖ * r ^ n
      ≤ (r / convergenceRadius K p) ^ n := by
    intro n
    calc ‖PowerSeries.coeff n (PowerSeries.exp K)‖ * r ^ n
        ≤ (1 / convergenceRadius K p) ^ n * r ^ n :=
          mul_le_mul_of_nonneg_right (norm_coeff_exp_le hnorm n) (pow_nonneg hr0 n)
      _ = (r / convergenceRadius K p) ^ n := by
          rw [← mul_pow]; ring_nf
  exact squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 n)) hbound
    (tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1)

/-! ## Two general-purpose finiteness facts -/

/-- **A nonnegative real sequence tending to `0` exceeds any positive threshold only finitely
often.** If `g : ℕ → ℝ` is nonnegative and tends to `0` along `atTop`, and `ε > 0`, then
`{n | ε ≤ g n}` is finite. -/
theorem finite_setOf_ge_of_tendsto_zero {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n)
    (hg : Tendsto g atTop (nhds 0)) {ε : ℝ} (hε : 0 < ε) : {n : ℕ | ε ≤ g n}.Finite := by
  have h := Metric.tendsto_nhds.mp hg ε hε
  rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at h
  have heq : {n : ℕ | ¬ dist (g n) 0 < ε} = {n : ℕ | ε ≤ g n} := by
    ext n
    simp only [Set.mem_setOf_eq, dist_eq_norm, sub_zero, Real.norm_eq_abs, not_lt,
      abs_of_nonneg (hg0 n)]
  rwa [heq] at h

/-- **The set of tuples whose entries sum into a finite set is finite.** For `S : Set ℕ` finite,
`{g : Fin n → ℕ | (∑ i, g i) ∈ S}` is finite: every entry of such a tuple is bounded by an upper bound
`M` of `S` (`Finset.single_le_sum`), so the set embeds in the finite box `∏ i, Set.Iic M`
(`Set.Finite.pi`). -/
theorem finite_setOf_sum_mem_of_finite {n : ℕ} {S : Set ℕ} (hS : S.Finite) :
    {g : Fin n → ℕ | (∑ i, g i) ∈ S}.Finite := by
  obtain ⟨M, hM⟩ := hS.bddAbove
  have hsub : {g : Fin n → ℕ | (∑ i, g i) ∈ S} ⊆ Set.univ.pi (fun _ : Fin n => Set.Iic M) := by
    intro g hg i _
    show g i ≤ M
    calc g i ≤ ∑ j, g j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      _ ≤ M := hM hg
  exact (Set.Finite.pi (fun _ => Set.finite_Iic M)).subset hsub

/-! ## The main result -/

omit [CompleteSpace K] in
/-- **The flat `exp`/`log` composite family is `cofinite`-null.** For `‖x‖ < expLogCompositionRadius
K p` (the domain making both `log hnorm x`'s series and `exp`'s series at that point converge, per
`NonarchimedeanExponentialHasSum`), the family `f ⟨n, g⟩ := coeff n (exp K) * ∏ i, (coeff (g i) (log K)
* x ^ (g i))` on `Σ n, Fin n → ℕ` tends to `0` along `cofinite`. For `ε > 0`, the "bad set"
`{q | ε ≤ ‖f q‖}` is a finite union (over the finitely many `n` with `‖c_n‖ * r ^ n ≥ ε`,
`finite_setOf_ge_of_tendsto_zero` applied to `tendsto_norm_coeff_exp_mul_pow_atTop_zero`) of finite
fibers (`finite_setOf_sum_mem_of_finite` applied to the finitely many total degrees `d` with
`ε / ‖c_n‖ ≤ r ^ d`), using `norm_coeff_exp_mul_prod_le` to see every bad `q = ⟨n, g⟩` has `n` in that
finite set, and `norm_prod_coeff_log_mul_pow_le` to see every bad `g` in a given fiber has total degree
in that fiber's finite set. This is exactly the prerequisite `HasSum.sigma_of_isUltrametricDist`
(`Langlands.NonarchimedeanSigmaSummability`) needs to flatten the outer/inner `HasSum`s for
`exp hnorm (log hnorm x)` into one flat sum. -/
theorem tendsto_cofinite_exp_log_flatSum (hnorm : ‖(p : K)‖ < 1) {x : K}
    (hx : ‖x‖ < expLogCompositionRadius K p) :
    Tendsto (fun q : Σ _n : ℕ, Fin _n → ℕ =>
        PowerSeries.coeff q.1 (PowerSeries.exp K) *
          ∏ i, (PowerSeries.coeff (q.2 i) (PowerSeries.log K) * x ^ (q.2 i)))
      cofinite (nhds 0) := by
  set f : (Σ _n : ℕ, Fin _n → ℕ) → K := fun q =>
    PowerSeries.coeff q.1 (PowerSeries.exp K) *
      ∏ i, (PowerSeries.coeff (q.2 i) (PowerSeries.log K) * x ^ (q.2 i)) with hfdef
  have hxlog : ‖x‖ < logConvergenceRadius K p :=
    lt_logConvergenceRadius_of_lt_expLogCompositionRadius hnorm hx
  have hp0 : (0 : ℝ) < ‖(p : K)‖ := norm_natCast_pos
  set r := ‖x‖ / ‖(p : K)‖ with hrdef
  have hr0 : 0 ≤ r := div_nonneg (norm_nonneg x) hp0.le
  have hr1 : r < 1 := by rw [hrdef, div_lt_one hp0]; exact hxlog
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  have hgoal_eq : {q : Σ _n : ℕ, Fin _n → ℕ | ¬ dist (f q) 0 < ε} = {q | ε ≤ ‖f q‖} := by
    ext q; simp [dist_eq_norm, not_lt]
  rw [hgoal_eq]
  set N : Set ℕ := {n : ℕ | ε ≤ ‖PowerSeries.coeff n (PowerSeries.exp K)‖ * r ^ n} with hNdef
  have hN : N.Finite :=
    finite_setOf_ge_of_tendsto_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 n))
      (tendsto_norm_coeff_exp_mul_pow_atTop_zero hnorm hx) hε
  have hfiber : ∀ n ∈ N, {g : Fin n → ℕ | ε ≤ ‖f ⟨n, g⟩‖}.Finite := by
    intro n _
    by_cases hc0 : PowerSeries.coeff n (PowerSeries.exp K) = 0
    · have : {g : Fin n → ℕ | ε ≤ ‖f ⟨n, g⟩‖} = ∅ := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
        show ‖PowerSeries.coeff n (PowerSeries.exp K) *
          ∏ i, (PowerSeries.coeff (g i) (PowerSeries.log K) * x ^ (g i))‖ < ε
        rw [hc0, zero_mul, norm_zero]
        exact hε
      rw [this]; exact Set.finite_empty
    · have hcpos : 0 < ‖PowerSeries.coeff n (PowerSeries.exp K)‖ := norm_pos_iff.mpr hc0
      have hD : {d : ℕ | ε / ‖PowerSeries.coeff n (PowerSeries.exp K)‖ ≤ r ^ d}.Finite :=
        finite_setOf_ge_of_tendsto_zero (fun d => pow_nonneg hr0 d)
          (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1) (div_pos hε hcpos)
      have hsub : {g : Fin n → ℕ | ε ≤ ‖f ⟨n, g⟩‖}
          ⊆ {g : Fin n → ℕ | (∑ i, g i) ∈ {d : ℕ | ε / ‖PowerSeries.coeff n
              (PowerSeries.exp K)‖ ≤ r ^ d}} := by
        intro g hg
        simp only [Set.mem_setOf_eq] at hg ⊢
        have hle : ε ≤ ‖PowerSeries.coeff n (PowerSeries.exp K)‖ * r ^ (∑ i, g i) := by
          refine hg.trans ?_
          show ‖PowerSeries.coeff n (PowerSeries.exp K) *
              ∏ i, (PowerSeries.coeff (g i) (PowerSeries.log K) * x ^ (g i))‖
            ≤ ‖PowerSeries.coeff n (PowerSeries.exp K)‖ * r ^ (∑ i, g i)
          calc ‖PowerSeries.coeff n (PowerSeries.exp K) *
                ∏ i, (PowerSeries.coeff (g i) (PowerSeries.log K) * x ^ (g i))‖
              = ‖PowerSeries.coeff n (PowerSeries.exp K)‖ *
                ‖∏ i, (PowerSeries.coeff (g i) (PowerSeries.log K) * x ^ (g i))‖ := norm_mul _ _
            _ ≤ ‖PowerSeries.coeff n (PowerSeries.exp K)‖ * r ^ (∑ i, g i) :=
                mul_le_mul_of_nonneg_left (norm_prod_coeff_log_mul_pow_le hnorm x g)
                  (norm_nonneg _)
        rwa [div_le_iff₀ hcpos, mul_comm]
      exact (finite_setOf_sum_mem_of_finite hD).subset hsub
  have hBadSub : {q : Σ _n : ℕ, Fin _n → ℕ | ε ≤ ‖f q‖}
      ⊆ ⋃ n ∈ N, Sigma.mk n '' {g : Fin n → ℕ | ε ≤ ‖f ⟨n, g⟩‖} := by
    rintro ⟨n, g⟩ hq
    have hq' : ε ≤ ‖f ⟨n, g⟩‖ := hq
    have hnN : n ∈ N := hq'.trans (norm_coeff_exp_mul_prod_le hnorm hxlog g _)
    exact Set.mem_biUnion hnN ⟨g, hq', rfl⟩
  exact (hN.biUnion (fun n hn => (hfiber n hn).image _)).subset hBadSub

end NonarchimedeanExponential
