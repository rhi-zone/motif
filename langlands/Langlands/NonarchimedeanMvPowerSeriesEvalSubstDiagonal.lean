import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Substitution
import Langlands.NonarchimedeanPowerSeriesEvalSubst
import Langlands.NonarchimedeanMvPowerSeriesEvalFin2

/-!
# Same-arity diagonal eval-subst compatibility: `ROADMAP.md` §23's "Lemma S"

`Φ : MvPowerSeries (Fin 2) R` (bivariate outer), substituted by the **diagonal family**
`h i := g.subst (X i)` (`g : PowerSeries R` univariate, embedded along axis `i` — not landing in
`Unit`-space, unlike `Langlands.NonarchimedeanPowerSeriesEvalSubstMv`'s family), lands back in
`MvPowerSeries (Fin 2) R`. Evaluating the composite multivariately at `y : Fin 2 → K` agrees with
evaluating `Φ` multivariately at the point obtained by evaluating `g` univariately at each
coordinate of `y` separately.

## Route

The double-interchange argument mirrors `Langlands.NonarchimedeanPowerSeriesEvalSubstMv.eval_subst_mv`,
but with **both** index roles (outer `d`, inner `m`) as `Fin 2 →₀ ℕ` rather than one being `ℕ`.

Concretely, set `T : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) → K := fun (d, m) ↦ algebraMap R K (coeff d Φ) *
evalSummandMv (h 0 ^ d 0 * h 1 ^ d 1) y m`.

* `coeff_subst_X_zero_mul_subst_X_one` : a two-line generalization of Mathlib's
  `PowerSeries.coeff_subst_X_zero_subst_mul_X_one` (same series in both slots) to *different*
  series `f0`/`f1`: `coeff e (subst X₀ f0 * subst X₁ f1) = coeff (e 0) f0 * coeff (e 1) f1`. Same
  proof (`Finset.sum_eq_single` at the unique surviving antidiagonal point).
* `coeff_eq_zero_diag_pow_of_lt` : `h 0 ^ d 0 * h 1 ^ d 1`'s coefficient at any `m` with
  `m.degree < d.degree` vanishes — from `PowerSeries.constantCoeff_subst_eq_zero` (each `h i` has
  zero constant term) and `MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero`/`le_order_mul`.
* `coeff_subst_diag_finset_degree` : the finite-degree form of `MvPowerSeries.coeff_subst` for the
  diagonal family.
* `hasSum_row_e_S` : grouping `T` by `m`, the row `d ↦ T (d, m)` sums to `evalSummandMv (Φ.subst h)
  y m`, via `coeff_subst_diag_finset_degree`.
* `hasSum_row_d_S` : grouping `T` by `d`, the row `m ↦ T (d, m)` sums to `evalSummandMv Φ (fun i ↦
  eval g (y i)) d` — the row is a genuine *product of two independent univariate geometric sums*
  (`HasSum.mul_of_nonarchimedean`, reindexed from `ℕ × ℕ` to `Fin 2 →₀ ℕ` via the bespoke
  `finsuppFin2EquivProdNat`), not a single `HasSum.mul_left` as in the other eval-subst files.
* `tendsto_T_cofinite_zero_S` : the uniform bound `‖T (d, m)‖ ≤ (max ‖y 0‖ ‖y 1‖) ^ m.degree`
  together with `coeff_eq_zero_diag_pow_of_lt` confine `{(d, m) : ‖T (d, m)‖ ≥ ε}` to a finite box
  (`Finsupp.finite_of_degree_lt` on both factors).
* `eval_subst_S` : chaining the two identifications.

## What this does not do

This closes `ROADMAP.md` §23's "Lemma S" only. Combined with "Lemma A"
(`Langlands.NonarchimedeanPowerSeriesEvalSubstMvIn`), it gives "Fact E" — the Lubin-Tate-specific
closure fact `piTorsion` needs — assembled in `Langlands.LubinTateTorsionPoints`.
-/

@[expose] public section

noncomputable section

namespace NonarchimedeanMvPowerSeriesEvalFin2

open NonarchimedeanPowerSeriesEval

variable {R K : Type*} [CommRing R] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra R K]

/-- **The diagonal embedding of a univariate series along axis `i`**: `g.subst (X i)`, packaged as
a family `Fin 2 → MvPowerSeries (Fin 2) R` for direct use as a same-arity substitutand. -/
def diagEmbed (g : PowerSeries R) : Fin 2 → MvPowerSeries (Fin 2) R :=
  fun i ↦ PowerSeries.subst (MvPowerSeries.X i) g

omit [IsUltrametricDist K] [CompleteSpace K] [Algebra R K] in
/-- Every component of the diagonal family has zero constant term, given `g` does. -/
theorem constantCoeff_diagEmbed {g : PowerSeries R} (hg0 : PowerSeries.constantCoeff g = 0)
    (i : Fin 2) : MvPowerSeries.constantCoeff (diagEmbed g i) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) g hg0

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **A two-series generalization of Mathlib's `PowerSeries.coeff_subst_X_zero_subst_mul_X_one`**:
for *different* univariate series `f0`, `f1` diagonally embedded along axes `0`/`1`, the
coefficient of their product at a bivariate multi-index `e` is the product of the univariate
coefficients — same proof (`Finset.sum_eq_single` at the unique surviving antidiagonal point
`(single 0 (e 0), single 1 (e 1))`), generalized from Mathlib's same-`f`-in-both-slots case. -/
theorem coeff_subst_X_zero_mul_subst_X_one (f0 f1 : PowerSeries R) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) f0 *
      PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) f1) =
      PowerSeries.coeff (e 0) f0 * PowerSeries.coeff (e 1) f1 := by
  rw [MvPowerSeries.coeff_mul,
    Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1)) ?_ ?_]
  · grind [PowerSeries.coeff_subst_single]
  · intro b hb hb'
    by_contra hmul_ne_zero
    rcases ne_zero_and_ne_zero_of_mul hmul_ne_zero with ⟨h0, h1⟩
    simp only [Fin.isValue, PowerSeries.coeff_subst_single, ne_eq, ite_eq_right_iff,
      not_forall, exists_prop] at h0 h1
    apply hb'
    rw [Prod.ext_iff, ← Finset.HasAntidiagonal.mem_antidiagonal.mp hb, h0.1, h1.1]
    simp
  · intro he
    have he' : Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) = e := by
      ext i
      fin_cases i <;> simp
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr he') he

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `diagEmbed g 0 ^ d 0 * diagEmbed g 1 ^ d 1`'s coefficient at any multi-index `m` with
`m.degree < d.degree` vanishes, given `g` has zero constant term. -/
theorem coeff_eq_zero_diag_pow_of_lt {g : PowerSeries R} (hg0 : PowerSeries.constantCoeff g = 0)
    {d m : Fin 2 →₀ ℕ} (hlt : m.degree < d.degree) :
    MvPowerSeries.coeff m (diagEmbed g 0 ^ (d 0) * diagEmbed g 1 ^ (d 1)) = 0 := by
  have h0 : (d 0 : ℕ∞) ≤ (diagEmbed g 0 ^ (d 0)).order :=
    MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (constantCoeff_diagEmbed hg0 0)
  have h1 : (d 1 : ℕ∞) ≤ (diagEmbed g 1 ^ (d 1)).order :=
    MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (constantCoeff_diagEmbed hg0 1)
  refine MvPowerSeries.coeff_of_lt_order ?_
  calc (m.degree : ℕ∞) < (d.degree : ℕ∞) := by exact_mod_cast hlt
    _ = (d 0 : ℕ∞) + (d 1 : ℕ∞) := by rw [degree_fin_two]; push_cast; ring
    _ ≤ (diagEmbed g 0 ^ (d 0)).order + (diagEmbed g 1 ^ (d 1)).order := add_le_add h0 h1
    _ ≤ (diagEmbed g 0 ^ (d 0) * diagEmbed g 1 ^ (d 1)).order := MvPowerSeries.le_order_mul

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Every coefficient of a diagonally-embedded power (`diagEmbed g i ^ d`), algebra-mapped into
`K`, is bounded by `1`, given `g`'s coefficients are. `diagEmbed g i`'s own coefficients are
literally either `0` or a coefficient of `g` (`PowerSeries.coeff_subst_single`), so this reduces
to `coeff_bound_pow_mv`. -/
theorem coeff_bound_diagEmbed {g : PowerSeries R} (i : Fin 2)
    (hg : ∀ n, ‖algebraMap R K (PowerSeries.coeff n g)‖ ≤ 1) :
    ∀ n : Fin 2 →₀ ℕ, ‖algebraMap R K (MvPowerSeries.coeff n (diagEmbed g i))‖ ≤ 1 := by
  intro n
  show ‖algebraMap R K (MvPowerSeries.coeff n (PowerSeries.subst (MvPowerSeries.X i) g))‖ ≤ 1
  rw [PowerSeries.coeff_subst_single]
  split
  · exact hg _
  · simp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The finite-degree form of `MvPowerSeries.coeff_subst`**, for the diagonal substitutand
family `diagEmbed g`: the `m`-th coefficient of `Φ.subst (diagEmbed g)` is the *finite* sum, over
`{d | d.degree ≤ m.degree}`, of `coeff d Φ • coeff m (diagEmbed g 0 ^ d 0 * diagEmbed g 1 ^ d 1)`.
-/
theorem coeff_subst_diag_finset_degree {g : PowerSeries R} {Φ : MvPowerSeries (Fin 2) R}
    (hg0 : PowerSeries.constantCoeff g = 0) (m : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff m (MvPowerSeries.subst (diagEmbed g) Φ) =
      ∑ d ∈ (Finsupp.finite_of_degree_le (σ := Fin 2) m.degree).toFinset,
        MvPowerSeries.coeff d Φ • MvPowerSeries.coeff m
          (diagEmbed g 0 ^ (d 0) * diagEmbed g 1 ^ (d 1)) := by
  have ha : MvPowerSeries.HasSubst (diagEmbed g) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_diagEmbed hg0)
  rw [MvPowerSeries.coeff_subst ha]
  rw [finsum_eq_sum_of_support_subset _
    (s := (Finsupp.finite_of_degree_le (σ := Fin 2) m.degree).toFinset)]
  · apply Finset.sum_congr rfl
    intro d _
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun s ↦ pow_zero _), Fin.prod_univ_two]
  · intro d hd
    simp only [Function.mem_support] at hd
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    by_contra hge
    push Not at hge
    apply hd
    rw [Finsupp.prod_fintype _ _ (fun s ↦ pow_zero _), Fin.prod_univ_two,
      coeff_eq_zero_diag_pow_of_lt hg0 (by omega), smul_zero]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Grouping `T (d, m) := algebraMap (coeff d Φ) * evalSummandMv (diagEmbed g 0 ^ d 0 *
diagEmbed g 1 ^ d 1) y m` by `m`**: the row `d ↦ T (d, m)` sums to
`evalSummandMv (Φ.subst (diagEmbed g)) y m`. -/
theorem hasSum_row_e_S {g : PowerSeries R} {Φ : MvPowerSeries (Fin 2) R}
    (hg0 : PowerSeries.constantCoeff g = 0) (y : Fin 2 → K) (m : Fin 2 →₀ ℕ) :
    HasSum (fun d : Fin 2 →₀ ℕ ↦ algebraMap R K (MvPowerSeries.coeff d Φ) *
        evalSummandMv (diagEmbed g 0 ^ (d 0) * diagEmbed g 1 ^ (d 1)) y m)
      (evalSummandMv (MvPowerSeries.subst (diagEmbed g) Φ) y m) := by
  set s := (Finsupp.finite_of_degree_le (σ := Fin 2) m.degree).toFinset with hsdef
  have hzero : ∀ d ∉ s, algebraMap R K (MvPowerSeries.coeff d Φ) *
      evalSummandMv (diagEmbed g 0 ^ (d 0) * diagEmbed g 1 ^ (d 1)) y m = 0 := by
    intro d hd
    rw [hsdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hd
    unfold evalSummandMv
    rw [coeff_eq_zero_diag_pow_of_lt hg0 hd, map_zero, zero_mul, mul_zero]
  have hval : HasSum
      (fun d : Fin 2 →₀ ℕ ↦ algebraMap R K (MvPowerSeries.coeff d Φ) *
        evalSummandMv (diagEmbed g 0 ^ (d 0) * diagEmbed g 1 ^ (d 1)) y m)
      (∑ d ∈ s, algebraMap R K (MvPowerSeries.coeff d Φ) *
        evalSummandMv (diagEmbed g 0 ^ (d 0) * diagEmbed g 1 ^ (d 1)) y m) :=
    hasSum_sum_of_ne_finset_zero hzero
  convert hval using 1
  unfold evalSummandMv
  rw [coeff_subst_diag_finset_degree hg0 m, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [smul_eq_mul, map_mul]
  ring

/-- **The bespoke `Fin 2 →₀ ℕ ≃ ℕ × ℕ` equivalence** `m ↦ (m 0, m 1)`, used to reindex a
product of two independent univariate `HasSum`s into a `Fin 2 →₀ ℕ`-indexed one. -/
def finsuppFin2EquivProdNat : (Fin 2 →₀ ℕ) ≃ ℕ × ℕ where
  toFun m := (m 0, m 1)
  invFun p := Finsupp.equivFunOnFinite.symm ![p.1, p.2]
  left_inv m := by
    ext i
    fin_cases i <;> simp
  right_inv p := by simp

set_option maxHeartbeats 1000000 in
/-- **Grouping `T (d, m) := algebraMap (coeff d Φ) * evalSummandMv (diagEmbed g 0 ^ d 0 *
diagEmbed g 1 ^ d 1) y m` by `d`**: the row `m ↦ T (d, m)` sums to `evalSummandMv Φ (fun i ↦ eval g
(y i)) d`. Unlike every other eval-subst file's `hasSum_row_d`, this row is a genuine *product of
two independent univariate geometric sums*, via `HasSum.mul_of_nonarchimedean` reindexed from
`ℕ × ℕ` to `Fin 2 →₀ ℕ`. -/
theorem hasSum_row_d_S {g : PowerSeries R} {Φ : MvPowerSeries (Fin 2) R}
    (hg : ∀ n, ‖algebraMap R K (PowerSeries.coeff n g)‖ ≤ 1) {y : Fin 2 → K}
    (hy0 : ‖y 0‖ < 1) (hy1 : ‖y 1‖ < 1) (d : Fin 2 →₀ ℕ) :
    HasSum (fun m : Fin 2 →₀ ℕ ↦ algebraMap R K (MvPowerSeries.coeff d Φ) *
        evalSummandMv (diagEmbed g 0 ^ (d 0) * diagEmbed g 1 ^ (d 1)) y m)
      (evalSummandMv Φ (fun i ↦ eval g (y i)) d) := by
  have hd0 : HasSum (evalSummand (g ^ (d 0)) (y 0)) (eval (g ^ (d 0)) (y 0)) :=
    hasSum_eval (coeff_bound_pow hg (d 0)) hy0
  have hd1 : HasSum (evalSummand (g ^ (d 1)) (y 1)) (eval (g ^ (d 1)) (y 1)) :=
    hasSum_eval (coeff_bound_pow hg (d 1)) hy1
  have hprod : HasSum (fun p : ℕ × ℕ ↦ evalSummand (g ^ (d 0)) (y 0) p.1 *
      evalSummand (g ^ (d 1)) (y 1) p.2)
      (eval (g ^ (d 0)) (y 0) * eval (g ^ (d 1)) (y 1)) := hd0.mul_of_nonarchimedean hd1
  have hreindex : HasSum
      (fun m : Fin 2 →₀ ℕ ↦
        evalSummand (g ^ (d 0)) (y 0) (m 0) * evalSummand (g ^ (d 1)) (y 1) (m 1))
      (eval (g ^ (d 0)) (y 0) * eval (g ^ (d 1)) (y 1)) :=
    (Equiv.hasSum_iff finsuppFin2EquivProdNat).mpr hprod
  have h2 := hreindex.mul_left (algebraMap R K (MvPowerSeries.coeff d Φ))
  have hfun : (fun m : Fin 2 →₀ ℕ ↦ algebraMap R K (MvPowerSeries.coeff d Φ) *
      evalSummandMv (diagEmbed g 0 ^ (d 0) * diagEmbed g 1 ^ (d 1)) y m) =
      (fun m : Fin 2 →₀ ℕ ↦ algebraMap R K (MvPowerSeries.coeff d Φ) *
        (evalSummand (g ^ (d 0)) (y 0) (m 0) * evalSummand (g ^ (d 1)) (y 1) (m 1))) := by
    funext m
    unfold evalSummandMv evalSummand diagEmbed
    rw [Fin.prod_univ_two, ← PowerSeries.subst_pow (PowerSeries.HasSubst.X (0 : Fin 2)) g (d 0),
      ← PowerSeries.subst_pow (PowerSeries.HasSubst.X (1 : Fin 2)) g (d 1),
      coeff_subst_X_zero_mul_subst_X_one, map_mul]
    ring
  rw [hfun]
  have hval : evalSummandMv Φ (fun i ↦ eval g (y i)) d =
      algebraMap R K (MvPowerSeries.coeff d Φ) *
        (eval (g ^ (d 0)) (y 0) * eval (g ^ (d 1)) (y 1)) := by
    unfold evalSummandMv
    rw [Fin.prod_univ_two, eval_pow hg hy0, eval_pow hg hy1]
  rw [hval]
  exact h2

omit [CompleteSpace K] in
/-- **`T` tends to `0` along `cofinite` on `(Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)`**: the uniform bound
`‖T (d, m)‖ ≤ (max ‖y 0‖ ‖y 1‖) ^ m.degree` together with `coeff_eq_zero_diag_pow_of_lt`
(`T (d, m) = 0` when `m.degree < d.degree`) confine `{(d, m) : ‖T (d, m)‖ ≥ ε}` to a finite box,
via `Finsupp.finite_of_degree_lt` on both factors. -/
theorem tendsto_T_cofinite_zero_S {g : PowerSeries R} {Φ : MvPowerSeries (Fin 2) R}
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hg : ∀ n, ‖algebraMap R K (PowerSeries.coeff n g)‖ ≤ 1) {y : Fin 2 → K}
    (hy0 : ‖y 0‖ < 1) (hy1 : ‖y 1‖ < 1) :
    Filter.Tendsto
      (fun p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) ↦ algebraMap R K (MvPowerSeries.coeff p.1 Φ) *
        evalSummandMv (diagEmbed g 0 ^ (p.1 0) * diagEmbed g 1 ^ (p.1 1)) y p.2)
      Filter.cofinite (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  set r := max ‖y 0‖ ‖y 1‖ with hrdef
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg _) (le_max_left _ _)
  have hr1 : r < 1 := max_lt hy0 hy1
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one hε hr1
  have hbound : ∀ p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ),
      ‖algebraMap R K (MvPowerSeries.coeff p.1 Φ) *
        evalSummandMv (diagEmbed g 0 ^ (p.1 0) * diagEmbed g 1 ^ (p.1 1)) y p.2‖ ≤
        r ^ p.2.degree := by
    intro p
    rw [norm_mul]
    calc ‖algebraMap R K (MvPowerSeries.coeff p.1 Φ)‖ *
          ‖evalSummandMv (diagEmbed g 0 ^ (p.1 0) * diagEmbed g 1 ^ (p.1 1)) y p.2‖
        ≤ 1 * r ^ p.2.degree :=
          mul_le_mul (hΦ p.1) (norm_evalSummandMv_le
            (coeff_bound_mul_mv (coeff_bound_pow_mv (coeff_bound_diagEmbed 0 hg) (p.1 0))
              (coeff_bound_pow_mv (coeff_bound_diagEmbed 1 hg) (p.1 1))) y p.2)
            (norm_nonneg _) zero_le_one
      _ = r ^ p.2.degree := one_mul _
  have hfin : Set.Finite {p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) |
      Finsupp.degree p.1 ≤ D ∧ Finsupp.degree p.2 < D} := by
    have heq : {p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) |
        Finsupp.degree p.1 ≤ D ∧ Finsupp.degree p.2 < D} =
        {d : Fin 2 →₀ ℕ | Finsupp.degree d ≤ D} ×ˢ {m : Fin 2 →₀ ℕ | Finsupp.degree m < D} := rfl
    rw [heq]
    exact (Finsupp.finite_of_degree_le (σ := Fin 2) D).prod
      (Finsupp.finite_of_degree_lt (σ := Fin 2) D)
  refine hfin.subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq, not_lt, dist_eq_norm, sub_zero] at hp
  have hnd : Finsupp.degree p.2 < D := by
    by_contra hge
    push Not at hge
    have := pow_le_pow_of_le_one hr0 hr1.le hge
    linarith [hbound p, hD]
  have hd : Finsupp.degree p.1 ≤ Finsupp.degree p.2 := by
    by_contra hlt
    push Not at hlt
    have hz : algebraMap R K (MvPowerSeries.coeff p.1 Φ) *
        evalSummandMv (diagEmbed g 0 ^ (p.1 0) * diagEmbed g 1 ^ (p.1 1)) y p.2 = 0 := by
      unfold evalSummandMv
      rw [coeff_eq_zero_diag_pow_of_lt hg0 hlt, map_zero, zero_mul, mul_zero]
    rw [hz] at hp; simp at hp; linarith
  exact ⟨by omega, hnd⟩

set_option maxHeartbeats 1000000 in
/-- **Same-arity diagonal eval-subst compatibility (`ROADMAP.md` §23's "Lemma S").**
`evalMv (Φ.subst (diagEmbed g)) y = evalMv Φ (fun i ↦ eval g (y i))`, for `Φ : MvPowerSeries
(Fin 2) R` and `g : PowerSeries R` with zero constant term. -/
theorem eval_subst_S {g : PowerSeries R} {Φ : MvPowerSeries (Fin 2) R}
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hg : ∀ n, ‖algebraMap R K (PowerSeries.coeff n g)‖ ≤ 1)
    (hΦ : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n Φ)‖ ≤ 1) {y : Fin 2 → K}
    (hy0 : ‖y 0‖ < 1) (hy1 : ‖y 1‖ < 1) :
    evalMv (MvPowerSeries.subst (diagEmbed g) Φ) y = evalMv Φ (fun i ↦ eval g (y i)) := by
  set T : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) → K :=
    fun p ↦ algebraMap R K (MvPowerSeries.coeff p.1 Φ) *
      evalSummandMv (diagEmbed g 0 ^ (p.1 0) * diagEmbed g 1 ^ (p.1 1)) y p.2 with hTdef
  have hTsum : Summable T :=
    IsUltrametricDist.summable_of_tendsto_zero (tendsto_T_cofinite_zero_S hΦ hg0 hg hy0 hy1)
  set A := ∑' p, T p with hAdef
  have hTA : HasSum T A := hTsum.hasSum
  -- group by `d`
  have hbyD : HasSum (fun d : Fin 2 →₀ ℕ ↦ evalSummandMv Φ (fun i ↦ eval g (y i)) d) A :=
    hTA.prod_fiberwise (fun d ↦ hasSum_row_d_S hg hy0 hy1 d)
  have hgy0 : ‖eval g (y 0)‖ < 1 := lt_of_le_of_lt (norm_eval_le hg hg0 hy0) hy0
  have hgy1 : ‖eval g (y 1)‖ < 1 := lt_of_le_of_lt (norm_eval_le hg hg0 hy1) hy1
  have hAeq1 : A = evalMv Φ (fun i ↦ eval g (y i)) := hbyD.unique (hasSum_evalMv hΦ hgy0 hgy1)
  -- group by `m`
  have hbyE : HasSum (evalSummandMv (MvPowerSeries.subst (diagEmbed g) Φ) y) A := by
    have hTswap : HasSum (fun q : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) ↦ T (q.2, q.1)) A :=
      (Equiv.hasSum_iff (Equiv.prodComm (Fin 2 →₀ ℕ) (Fin 2 →₀ ℕ))).mpr hTA
    exact hTswap.prod_fiberwise (fun m ↦ hasSum_row_e_S hg0 y m)
  have hAeq2 : evalMv (MvPowerSeries.subst (diagEmbed g) Φ) y = A := by
    unfold evalMv; exact hbyE.tsum_eq
  rw [hAeq2, hAeq1]

end NonarchimedeanMvPowerSeriesEvalFin2

end
