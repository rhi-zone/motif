import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Langlands.NonarchimedeanUnconditionalSummability

/-!
# Evaluating a power series at a concrete point of a complete ultrametric normed field

`Mathlib.RingTheory.PowerSeries.Evaluation`'s `PowerSeries.aeval`/`PowerSeries.hasEvalIdeal` is
Mathlib's vehicle for "evaluate a power series at a topologically nilpotent element", but it
requires the target ring to carry `[UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S]
[IsLinearTopology S S] [T2Space S] [CompleteSpace S] [Algebra R S] [ContinuousSMul R S]`. No
instance connects `IsLinearTopology` to this repo's `NormedField`/`IsUltrametricDist`-based rings
(confirmed by grep of both this repo's `Langlands/*.lean` and the relevant vendored Mathlib paths,
`RingTheory/DedekindDomain/` and `RingTheory/Valuation/` — no hits for `IsLinearTopology` in either),
and building that instance stack from scratch would be a large, diamond-risk-prone undertaking (this
repo already hit a `NormedField`/`RankOne` diamond once, `ROADMAP.md` §6u).

This file instead builds evaluation from scratch at the lighter generality this repo's other
analytic files already use successfully (`Langlands.NonarchimedeanExponential`,
`Langlands.NonarchimedeanUnconditionalSummability`): a plain `NormedField`/`IsUltrametricDist`/
`CompleteSpace` target, with no `UniformSpace`/`IsLinearTopology` typeclass stack at all. The
convergence argument is in fact *simpler* than `Langlands.NonarchimedeanExponential.exp`/`.log`: for
a power series with every coefficient of norm at most `1` (the exact nonarchimedean analogue of "the
coefficients lie in the ring of integers"), evaluated at a point of norm `< 1`, the `n`-th term is
bounded by `‖x‖ ^ n` directly — no factorial/Legendre estimate is needed, unlike `exp`'s
`n!`-denominators. Combined with
`Langlands.NonarchimedeanUnconditionalSummability.IsUltrametricDist.summable_of_tendsto_zero`, the
partial sums are not just Cauchy but unconditionally (`HasSum`) convergent, with no separate
rearrangement argument.

## Route

* `evalSummand f x n := algebraMap R K (coeff n f) * x ^ n` — the `n`-th term.
* `norm_evalSummand_le` — `‖evalSummand f x n‖ ≤ ‖x‖ ^ n`, given every coefficient of `f` has
  algebra-mapped norm at most `1`.
* `tendsto_evalSummand_atTop_zero`, `summable_evalSummand` — the geometric bound forces the terms to
  `0`, hence (via `IsUltrametricDist.summable_of_tendsto_zero`) unconditional summability.
* `eval`, `hasSum_eval` — the evaluation itself, as a `tsum` with its defining `HasSum` property.
* `eval_add` — evaluation is additive on the domain where both series' coefficients are bounded.

## What this does not do

This file does **not** build a full ring/algebra-hom structure for `eval` (in particular, no
Cauchy-product/multiplicativity `eval (f * g) x = eval f x * eval g x`, and no compatibility with
`PowerSeries.subst`/composition) — only what is needed to state and use evaluation at all. See
`Langlands.LubinTateFormalGroupEval`'s module docstring for the precise remaining gap this leaves
for the Lubin-Tate torsion-point thread.
-/

@[expose] public section

noncomputable section

namespace NonarchimedeanPowerSeriesEval

variable {R K : Type*} [CommRing R] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra R K]

/-- The `n`-th summand of the evaluation series `Σ (algebraMap (coeff n f)) * x ^ n`. -/
def evalSummand (f : PowerSeries R) (x : K) (n : ℕ) : K :=
  algebraMap R K (PowerSeries.coeff n f) * x ^ n

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The per-term bound**: if every coefficient of `f`, algebra-mapped into `K`, has norm at most
`1`, then the `n`-th evaluation summand at `x` has norm at most `‖x‖ ^ n`. No factorial/Legendre
estimate is needed here, unlike `Langlands.NonarchimedeanExponential.norm_pow_div_factorial_le` —
this is the sense in which evaluating a bounded-coefficient series is a strictly simpler convergence
argument than the exponential series. -/
theorem norm_evalSummand_le {f : PowerSeries R}
    (hf : ∀ n, ‖algebraMap R K (PowerSeries.coeff n f)‖ ≤ 1) (x : K) (n : ℕ) :
    ‖evalSummand f x n‖ ≤ ‖x‖ ^ n := by
  unfold evalSummand
  rw [norm_mul, norm_pow]
  calc ‖algebraMap R K (PowerSeries.coeff n f)‖ * ‖x‖ ^ n
      ≤ 1 * ‖x‖ ^ n := mul_le_mul_of_nonneg_right (hf n) (pow_nonneg (norm_nonneg x) n)
    _ = ‖x‖ ^ n := one_mul _

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The evaluation summands tend to `0` along `atTop`, for `x` inside the unit ball. Same
`squeeze_zero`/`tendsto_pow_atTop_nhds_zero_of_lt_one` pattern as
`Langlands.NonarchimedeanExponentialHasSum`'s `tendsto_zero_of_geometric_bound`. -/
theorem tendsto_evalSummand_atTop_zero {f : PowerSeries R}
    (hf : ∀ n, ‖algebraMap R K (PowerSeries.coeff n f)‖ ≤ 1) {x : K} (hx : ‖x‖ < 1) :
    Filter.Tendsto (evalSummand f x) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) (norm_evalSummand_le hf x)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg x) hx)

/-- **Unconditional summability of the evaluation series.** Since `ℕ`'s `cofinite` filter equals
`atTop`, `tendsto_evalSummand_atTop_zero` upgrades (via
`IsUltrametricDist.summable_of_tendsto_zero`, which needs no separate rearrangement argument in the
nonarchimedean setting) directly to `Summable`. -/
theorem summable_evalSummand {f : PowerSeries R}
    (hf : ∀ n, ‖algebraMap R K (PowerSeries.coeff n f)‖ ≤ 1) {x : K} (hx : ‖x‖ < 1) :
    Summable (evalSummand f x) :=
  IsUltrametricDist.summable_of_tendsto_zero
    (Nat.cofinite_eq_atTop ▸ tendsto_evalSummand_atTop_zero hf hx)

/-- **Evaluation of a power series at a concrete point.** Defined unconditionally as
`∑' n, evalSummand f x n` (`tsum`'s usual convention: `0` when the family is not summable);
meaningful exactly when `f`'s coefficients are algebra-mapped-norm-bounded by `1` and `‖x‖ < 1`, per
`hasSum_eval`. -/
def eval (f : PowerSeries R) (x : K) : K := ∑' n, evalSummand f x n

/-- **The defining property of `eval`**: on the domain where it is meaningful, the evaluation
summands genuinely (unconditionally) sum to `eval f x`. This is the precise sense in which `eval`
"agrees with the formal object" `f`: every one of `f`'s coefficients contributes its term to the
sum, and the sum is independent of the order/grouping in which those contributions are added
(`HasSum`, not merely a sequential limit). -/
theorem hasSum_eval {f : PowerSeries R}
    (hf : ∀ n, ‖algebraMap R K (PowerSeries.coeff n f)‖ ≤ 1) {x : K} (hx : ‖x‖ < 1) :
    HasSum (evalSummand f x) (eval f x) :=
  (summable_evalSummand hf hx).hasSum

/-- **Evaluation is additive**, on the domain where both series have algebra-mapped-norm-bounded
coefficients. Proved by matching `PowerSeries.coeff_add` (`coeff` is an `R`-linear map) against the
ultrametric bound `‖a + b‖ ≤ max ‖a‖ ‖b‖ ≤ 1` needed to see `f + g`'s own coefficients are bounded,
then `Summable.tsum_add`. -/
theorem eval_add {f g : PowerSeries R}
    (hf : ∀ n, ‖algebraMap R K (PowerSeries.coeff n f)‖ ≤ 1)
    (hg : ∀ n, ‖algebraMap R K (PowerSeries.coeff n g)‖ ≤ 1) {x : K} (hx : ‖x‖ < 1) :
    eval (f + g) x = eval f x + eval g x := by
  have hfg : ∀ n, ‖algebraMap R K (PowerSeries.coeff n (f + g))‖ ≤ 1 := fun n ↦ by
    rw [map_add, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))
  have hterm : ∀ n, evalSummand (f + g) x n = evalSummand f x n + evalSummand g x n := fun n ↦ by
    unfold evalSummand
    rw [map_add, map_add, add_mul]
  simp only [eval, hterm]
  exact Summable.tsum_add (summable_evalSummand hf hx) (summable_evalSummand hg hx)

end NonarchimedeanPowerSeriesEval

end
