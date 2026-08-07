import Langlands.NonarchimedeanExponentialHasSum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.Field

/-!
# The group-homomorphism law for the nonarchimedean exponential

`NonarchimedeanExponential.exp` has been available in this repo since the exp/log thread began, but
the law that makes it an *exponential* — `exp (x + y) = exp x * exp y` — was never proved.
`Langlands.NonarchimedeanExponential`'s and
`Langlands.NonarchimedeanExponentialUnitsFiltration`'s docstrings both flag it as unattempted, and
it is what upgrades `exp_mem_principalUnitsPow`'s pointwise landing statement into an actual
group homomorphism `(𝔪_A^i, +) → U_A^{(i)}`. It is also a prerequisite of *every* route to the
wild-case norm/trace compatibility formula `N_{L/K}(exp x) = exp(Tr_{L/K} x)`.

## Route

The Cauchy product, exactly as `NormedSpace.exp_add_of_commute_of_mem_ball` does it over ℝ/ℂ, but
with the summability of the product family coming from the nonarchimedean structure rather than
from absolute convergence:

* `IsUltrametricDist.norm_add_le_max` puts `x + y` in the convergence domain whenever `x` and `y`
  are — **no radius shrinkage**, unlike the composite `exp ∘ log`.
* `Summable.mul_of_nonarchimedean` (via this repo's `IsUltrametricDist.toNonarchimedeanRing`) gives
  summability of `fun (i, j) ↦ (xⁱ/i!)(yʲ/j!)` for free, with no norm-summability side condition.
* `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` regroups that product over
  `Finset.antidiagonal`.
* The finite identity `∑_{k+l=n} xᵏ/k! · yˡ/l! = (x+y)ⁿ/n!` is `Commute.add_pow'` together with
  `Nat.cast_add_choose`.

## Main results

* `NonarchimedeanExponential.exp_zero` : `exp 0 = 1`.
* `NonarchimedeanExponential.exp_add` : the group-homomorphism law.
* `NonarchimedeanExponential.exp_mul_exp_neg` / `NonarchimedeanExponential.isUnit_exp` :
  `exp x * exp (-x) = 1`, so `exp x` is a unit with explicit inverse.
-/

noncomputable section

namespace NonarchimedeanExponential

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]
variable {p : ℕ} [hp : Fact p.Prime]

/-- `exp 0 = 1`: only the `n = 0` term of the series survives. -/
theorem exp_zero (hnorm : ‖(p : K)‖ < 1) : exp hnorm (0 : K) = 1 := by
  have h0 : ‖(0 : K)‖ < convergenceRadius K p := by
    rw [norm_zero]
    exact Real.rpow_pos_of_pos norm_natCast_pos _
  have hs := hasSum_exp hnorm h0
  have hone : HasSum (fun n : ℕ => (0 : K) ^ n / (n.factorial : K)) 1 := by
    have : (fun n : ℕ => (0 : K) ^ n / (n.factorial : K)) = fun n : ℕ => if n = 0 then 1 else 0 := by
      funext n
      rcases n with _ | n <;> simp
    rw [this]
    simpa using hasSum_ite_eq (0 : ℕ) (1 : K)
  exact (hone.unique hs).symm

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The finite binomial-over-factorials identity behind `exp_add`'s `n`-th block:
`((k+l).choose k) • (xᵏ yˡ) / (k+l)! = xᵏ/k! · yˡ/l!`, by `Nat.cast_add_choose`. -/
private theorem nsmul_choose_div_factorial (k l : ℕ) (x y : K) :
    (k + l).choose k • (x ^ k * y ^ l) / (((k + l).factorial : ℕ) : K)
      = x ^ k / ((k.factorial : ℕ) : K) * (y ^ l / ((l.factorial : ℕ) : K)) := by
  have h1 : ((k.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_pos _).ne'
  have h2 : ((l.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_pos _).ne'
  have h3 : (((k + l).factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_pos _).ne'
  rw [nsmul_eq_mul, Nat.cast_add_choose]
  field_simp

-- The `rw` chain below (three `HasSum.tsum_eq` rewrites through `exp`s `dif`/`Classical.choose`
-- definition, then the antidiagonal regrouping) exceeds the default heartbeat budget.
set_option maxHeartbeats 800000 in
/-- **The group-homomorphism law.** For `x` and `y` in `exp`'s convergence domain,
`exp (x + y) = exp x * exp y`.

`x + y` is again in the domain by the ultrametric inequality (`IsUltrametricDist.norm_add_le_max`),
so all three exponentials are given by their series (`hasSum_exp`). Multiplying the series for `x`
and `y` is legitimate with no extra hypothesis in a nonarchimedean ring
(`Summable.mul_of_nonarchimedean`), and regrouping the resulting `ℕ × ℕ`-indexed family over
`Finset.antidiagonal` (`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`) turns the `n`-th block
into `∑_{k+l=n} xᵏ/k! · yˡ/l!`, which is `(x+y)ⁿ/n!` by the binomial theorem
(`Commute.add_pow'`) and `((k+l).choose k : K) = (k+l)!/(k!·l!)` (`Nat.cast_add_choose`). -/
theorem exp_add (hnorm : ‖(p : K)‖ < 1) {x y : K}
    (hx : ‖x‖ < convergenceRadius K p) (hy : ‖y‖ < convergenceRadius K p) :
    exp hnorm (x + y) = exp hnorm x * exp hnorm y := by
  have hxy : ‖x + y‖ < convergenceRadius K p :=
    lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max x y) (max_lt hx hy)
  have hfx := hasSum_exp hnorm hx
  have hfy := hasSum_exp hnorm hy
  have hfxy := hasSum_exp hnorm hxy
  rw [← hfx.tsum_eq, ← hfy.tsum_eq, ← hfxy.tsum_eq,
    hfx.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hfy.summable
      (hfx.summable.mul_of_nonarchimedean hfy.summable)]
  refine tsum_congr fun n => ?_
  rw [(Commute.all x y).add_pow', Finset.sum_div]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hn : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
  subst hn
  exact nsmul_choose_div_factorial kl.1 kl.2 x y

/-- `exp x * exp (-x) = 1`. -/
theorem exp_mul_exp_neg (hnorm : ‖(p : K)‖ < 1) {x : K} (hx : ‖x‖ < convergenceRadius K p) :
    exp hnorm x * exp hnorm (-x) = 1 := by
  have hnx : ‖-x‖ < convergenceRadius K p := by rwa [norm_neg]
  rw [← exp_add hnorm hx hnx, add_neg_cancel, exp_zero]

/-- `exp x` is a unit, with explicit inverse `exp (-x)`. -/
theorem isUnit_exp (hnorm : ‖(p : K)‖ < 1) {x : K} (hx : ‖x‖ < convergenceRadius K p) :
    IsUnit (exp hnorm x) :=
  IsUnit.of_mul_eq_one _ (exp_mul_exp_neg hnorm hx)

end NonarchimedeanExponential

end
