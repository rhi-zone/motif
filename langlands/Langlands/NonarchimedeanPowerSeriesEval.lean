import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
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
* `eval_mul`, `coeff_bound_mul` — evaluation is multiplicative, via Mathlib's nonarchimedean Cauchy
  product formula `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`
  (`Mathlib.Topology.Algebra.InfiniteSum.Ring`), which needs only `[T3Space α] [IsTopologicalSemiring
  α]` — no `NonarchimedeanRing` typeclass required for this particular direction, since it isn't a
  rearrangement argument (it re-groups the already-known-summable `ℕ × ℕ`-indexed product family by
  `Finset.antidiagonal`, matching `PowerSeries.coeff_mul` exactly). The summability of that product
  family itself *is* obtained via the nonarchimedean route (`HasSum.mul_of_nonarchimedean`, which
  needs no separate summability hypothesis, unlike the general/archimedean case) — see the local
  `NonarchimedeanRing K` instance below, bridged from `NormedField K`/`IsUltrametricDist K` (no
  instance for this connection exists in Mathlib itself, confirmed by grep; the bridge is immediate,
  Prop-valued, and diamond-free — `NonarchimedeanRing` only adds the `is_nonarchimedean` field on top
  of `IsTopologicalRing`, and `NonarchimedeanAddGroup K`'s own instance, from `IsUltrametricDist`,
  already supplies exactly that field).
* `eval_one`, `coeff_bound_one`, `coeff_bound_pow`, `eval_pow` — the multiplicative structure
  extended to `1` and to powers, by direct induction on `eval_mul`.

## What this does not do

This file does **not** build compatibility between `eval` and `PowerSeries.subst`/composition —
that is `Langlands.NonarchimedeanPowerSeriesEvalSubst.eval_subst`, built on top of `eval_mul`/
`eval_pow`. See that file's module docstring for the univariate result, and
`Langlands.LubinTateFormalGroupEval`'s module docstring for the precise remaining gap (the
bivariate-outer form) this leaves for the Lubin-Tate torsion-point thread.
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

omit [CompleteSpace K] in
/-- **`eval f x` lies in the maximal ideal whenever `f` does**: if `f` has zero constant term (so
every evaluation summand of index `0` vanishes) and bounded coefficients, `‖eval f x‖ ≤ ‖x‖`. Via
the ultrametric bound `IsUltrametricDist.norm_tsum_le` (`‖∑' i, g i‖ ≤ ⨆ i, ‖g i‖`, unconditional,
no summability hypothesis needed), applied to `evalSummand f x`. -/
theorem norm_eval_le {f : PowerSeries R}
    (hf : ∀ n, ‖algebraMap R K (PowerSeries.coeff n f)‖ ≤ 1)
    (hf0 : PowerSeries.constantCoeff f = 0) {x : K} (hx : ‖x‖ < 1) :
    ‖eval f x‖ ≤ ‖x‖ := by
  unfold eval
  refine (IsUltrametricDist.norm_tsum_le _).trans (ciSup_le fun n ↦ ?_)
  match n with
  | 0 =>
      have h0 : evalSummand f x 0 = 0 := by
        unfold evalSummand
        rw [PowerSeries.coeff_zero_eq_constantCoeff, hf0, map_zero, zero_mul]
      rw [h0, norm_zero]
      exact norm_nonneg x
  | n + 1 =>
      calc ‖evalSummand f x (n + 1)‖ ≤ ‖x‖ ^ (n + 1) := norm_evalSummand_le hf x (n + 1)
        _ ≤ ‖x‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg x) hx.le (by omega)
        _ = ‖x‖ := pow_one _

/-- **`eval f x` lies within `‖x‖` of `f`'s constant term, algebra-mapped into `K`** — the
general form of `norm_eval_le` (which is the `constantCoeff f = 0` case, where the target
`algebraMap R K (constantCoeff f)` is `0`). Splits `eval f x` off at index `0`
(`Summable.tsum_eq_zero_add`), identifies the index-`0` summand with `algebraMap R K (constantCoeff
f)`, and bounds the remaining tail exactly as `norm_eval_le` does. -/
theorem norm_eval_sub_algebraMap_constantCoeff_le {f : PowerSeries R}
    (hf : ∀ n, ‖algebraMap R K (PowerSeries.coeff n f)‖ ≤ 1) {x : K} (hx : ‖x‖ < 1) :
    ‖eval f x - algebraMap R K (PowerSeries.constantCoeff f)‖ ≤ ‖x‖ := by
  have h0 : evalSummand f x 0 = algebraMap R K (PowerSeries.constantCoeff f) := by
    unfold evalSummand
    rw [PowerSeries.coeff_zero_eq_constantCoeff, pow_zero, mul_one]
  have hsplit : eval f x =
      evalSummand f x 0 + ∑' n, evalSummand f x (n + 1) :=
    (summable_evalSummand hf hx).tsum_eq_zero_add
  rw [hsplit, h0, add_sub_cancel_left]
  refine (IsUltrametricDist.norm_tsum_le _).trans (ciSup_le fun n ↦ ?_)
  calc ‖evalSummand f x (n + 1)‖ ≤ ‖x‖ ^ (n + 1) := norm_evalSummand_le hf x (n + 1)
    _ ≤ ‖x‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg x) hx.le (by omega)
    _ = ‖x‖ := pow_one _

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

/-- **`K` is a nonarchimedean ring** in Mathlib's `NonarchimedeanRing` sense, whenever it is a
`NormedField` with an ultrametric norm. No instance connecting these already exists in Mathlib
(confirmed by grep across `Mathlib/Analysis/` and `Mathlib/Topology/Algebra/Nonarchimedean/`); the
bridge is immediate since both sides are `Prop`-valued and share the same underlying
`is_nonarchimedean` field — `NonarchimedeanAddGroup K`'s own instance (from `IsUltrametricDist K`
via `Mathlib.Analysis.Normed.Group.Ultra`) supplies exactly the fact `NonarchimedeanRing` needs on
top of the (already-automatic) `IsTopologicalRing K` instance. No diamond risk: this only adds a
`Prop` field to structure already present, it does not touch any data-carrying instance. -/
instance : NonarchimedeanRing K :=
  { (inferInstance : IsTopologicalRing K) with
    is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean }

/-- **Evaluation is multiplicative**, on the domain where both series have
algebra-mapped-norm-bounded coefficients. The Cauchy product formula
`Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` regroups the `ℕ × ℕ`-indexed product family (whose
summability comes from `HasSum.mul_of_nonarchimedean`, needing no separate hypothesis given the
`NonarchimedeanRing K` instance above) by `Finset.antidiagonal`, matching `PowerSeries.coeff_mul`
term-by-term. -/
theorem eval_mul {f g : PowerSeries R}
    (hf : ∀ n, ‖algebraMap R K (PowerSeries.coeff n f)‖ ≤ 1)
    (hg : ∀ n, ‖algebraMap R K (PowerSeries.coeff n g)‖ ≤ 1) {x : K} (hx : ‖x‖ < 1) :
    eval (f * g) x = eval f x * eval g x := by
  have hfg : Summable (fun i : ℕ × ℕ => evalSummand f x i.1 * evalSummand g x i.2) :=
    ((hasSum_eval hf hx).mul_of_nonarchimedean (hasSum_eval hg hx)).summable
  unfold eval
  rw [(summable_evalSummand hf hx).tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (summable_evalSummand hg hx) hfg]
  congr 1
  funext n
  unfold evalSummand
  rw [PowerSeries.coeff_mul, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [map_mul, ← hp, pow_add]
  ring

omit [CompleteSpace K] in
/-- **Coefficient boundedness is preserved by multiplication.** `coeff n (f * g)` is a sum, over
`Finset.antidiagonal n`, of products of bounded coefficients; the nonempty-sum ultrametric bound
`Finset.Nonempty.norm_sum_le_sup'_norm` bounds it by `1`. -/
theorem coeff_bound_mul {f g : PowerSeries R}
    (hf : ∀ n, ‖algebraMap R K (PowerSeries.coeff n f)‖ ≤ 1)
    (hg : ∀ n, ‖algebraMap R K (PowerSeries.coeff n g)‖ ≤ 1) :
    ∀ n, ‖algebraMap R K (PowerSeries.coeff n (f * g))‖ ≤ 1 := by
  intro n
  rw [PowerSeries.coeff_mul, map_sum]
  refine (Finset.Nonempty.norm_sum_le_sup'_norm
    ⟨(0, n), Finset.mem_antidiagonal.mpr (by simp)⟩ _).trans ?_
  simp only [Finset.sup'_le_iff]
  intro p _
  rw [map_mul, norm_mul]
  calc ‖algebraMap R K (PowerSeries.coeff p.1 f)‖ * ‖algebraMap R K (PowerSeries.coeff p.2 g)‖
      ≤ 1 * 1 := mul_le_mul (hf p.1) (hg p.2) (norm_nonneg _) zero_le_one
    _ = 1 := mul_one 1

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Evaluation at `X` is the identity**: only the linear term contributes. -/
theorem eval_X (x : K) : eval (PowerSeries.X : PowerSeries R) x = x := by
  have hterm : ∀ n, evalSummand (PowerSeries.X : PowerSeries R) x n = if n = 1 then x else 0 := by
    intro n
    unfold evalSummand
    match n with
    | 0 => simp
    | 1 => simp
    | n + 2 => simp [PowerSeries.coeff_X]
  unfold eval
  rw [tsum_eq_single 1 (by intro n hn; rw [hterm]; simp [hn])]
  rw [hterm]; simp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Evaluating any series with zero constant term at `0` gives `0`.** Every summand vanishes
termwise: the constant term because `coeff 0 f = 0`, every other term because `0 ^ n = 0` for
`n ≥ 1`. No convergence argument is needed. -/
theorem eval_zero_of_coeff_zero_eq_zero {f : PowerSeries R} (hf0 : PowerSeries.coeff 0 f = 0) :
    eval f (0 : K) = 0 := by
  have hterm : ∀ n, evalSummand f (0 : K) n = 0 := by
    intro n
    unfold evalSummand
    match n with
    | 0 => rw [hf0, map_zero, zero_mul]
    | n + 1 => rw [pow_succ, mul_zero, mul_zero]
  unfold eval
  simp [hterm]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The coefficients of `X : PowerSeries R`, algebra-mapped into `K`, are trivially bounded by
`1`. -/
theorem coeff_bound_X :
    ∀ n, ‖algebraMap R K (PowerSeries.coeff n (PowerSeries.X : PowerSeries R))‖ ≤ 1 := by
  intro n
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => simp [PowerSeries.coeff_X]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Evaluation at `1` is `1`**: only the constant term (`= 1`) contributes. -/
theorem eval_one (x : K) : eval (1 : PowerSeries R) x = 1 := by
  have hterm : ∀ n, evalSummand (1 : PowerSeries R) x n = if n = 0 then 1 else 0 := by
    intro n
    unfold evalSummand
    match n with
    | 0 => simp
    | n + 1 => simp
  unfold eval
  rw [tsum_eq_single 0 (by intro n hn; rw [hterm]; simp [hn])]
  rw [hterm]; simp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The coefficients of `1 : PowerSeries R`, algebra-mapped into `K`, are trivially bounded by `1`. -/
theorem coeff_bound_one :
    ∀ n, ‖algebraMap R K (PowerSeries.coeff n (1 : PowerSeries R))‖ ≤ 1 := by
  intro n
  match n with
  | 0 => simp
  | n + 1 => simp

omit [CompleteSpace K] in
/-- **Coefficient boundedness is preserved by powers**, by induction on `coeff_bound_mul`. -/
theorem coeff_bound_pow {f : PowerSeries R}
    (hf : ∀ n, ‖algebraMap R K (PowerSeries.coeff n f)‖ ≤ 1) :
    ∀ (m n : ℕ), ‖algebraMap R K (PowerSeries.coeff n (f ^ m))‖ ≤ 1 := by
  intro m
  induction m with
  | zero => intro n; simpa using coeff_bound_one (R := R) (K := K) n
  | succ m ih => intro n; rw [pow_succ]; exact coeff_bound_mul ih hf n

/-- **Evaluation is compatible with powers**: `eval (f ^ n) x = (eval f x) ^ n`, by induction on
`eval_mul`. -/
theorem eval_pow {f : PowerSeries R}
    (hf : ∀ n, ‖algebraMap R K (PowerSeries.coeff n f)‖ ≤ 1) {x : K} (hx : ‖x‖ < 1) :
    ∀ n, eval (f ^ n) x = eval f x ^ n
  | 0 => by simpa using eval_one (R := R) (K := K) x
  | n + 1 => by
      rw [pow_succ, pow_succ, eval_mul (coeff_bound_pow hf n) hf hx, eval_pow hf hx n]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Evaluation of a coerced polynomial agrees with `Polynomial.aeval`.** No coefficient-bound or
`‖x‖ < 1` hypothesis is needed: a polynomial's coefficients vanish above its `natDegree`
(`Polynomial.coeff_eq_zero_of_natDegree_lt`), so the defining `tsum` has finite support and reduces
(`tsum_eq_sum`) to exactly the finite sum `Polynomial.eval₂_eq_sum_range` uses to define
`Polynomial.aeval` (`Polynomial.aeval_def`) — the two sides are termwise identical via
`Polynomial.coeff_coe` (`(↑P : PowerSeries R).coeff n = P.coeff n`). -/
theorem eval_coe_eq_aeval (P : Polynomial R) (x : K) :
    eval (P : PowerSeries R) x = Polynomial.aeval x P := by
  unfold eval
  rw [tsum_eq_sum (s := Finset.range (P.natDegree + 1)) fun n hn ↦ by
      unfold evalSummand
      rw [Polynomial.coeff_coe,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hn), map_zero, zero_mul],
    Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  exact Finset.sum_congr rfl fun n _ ↦ by unfold evalSummand; rw [Polynomial.coeff_coe]

end NonarchimedeanPowerSeriesEval

end
