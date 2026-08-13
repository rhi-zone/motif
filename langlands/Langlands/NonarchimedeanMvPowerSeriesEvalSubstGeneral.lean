import Mathlib.RingTheory.MvPowerSeries.Substitution
import Langlands.NonarchimedeanMvPowerSeriesEval

/-!
# General eval-subst compatibility: `evalMv (Φ.subst A) z = evalMv Φ (fun i ↦ evalMv (A i) z)`

`ROADMAP.md` §25/§26's **"Lemma-A-analogue"**, in the form that subsumes both of that section's two
scoped compatibilities: a *multivariate* outer series `Φ : MvPowerSeries τ R` substituted by an
**arbitrary** family `A : τ → MvPowerSeries σ R` (each component with zero constant term and
algebra-mapped-norm-bounded coefficients), with `τ` and `σ` two arbitrary finite index types.

Neither `Langlands.NonarchimedeanPowerSeriesEvalSubstMvIn.eval_subst_A` (univariate outer, i.e.
`τ = Unit`) nor `Langlands.NonarchimedeanMvPowerSeriesEvalSubstDiagonal.eval_subst_S` (`τ = σ =
Fin 2`, *diagonal* family `A i = g.subst (X i)` reusing one univariate `g` along every axis) covers
the shape associativity needs, which is `τ = Fin 2`, `σ = Fin 3`, and a **mixed** family whose two
components have different shapes: `A 0 = Φ.subst ![X 0, X 1]` (a genuinely bivariate composite
embedded in 3-variable space) and `A 1 = X 2` (a bare coordinate). Stating the lemma for a
completely arbitrary family removes the shape question entirely — and, applied twice (once for the
outer `Φ.subst ![_, X 2]`, once for the inner `Φ.subst ![X 0, X 1]`), it is the *only* eval-subst
compatibility that nesting needs; no separate "Lemma-S-analogue" arises.

## Route

The same double-series-interchange shape as the two earlier files, with outer index `d : τ →₀ ℕ`
and inner index `n : σ →₀ ℕ`; set
`T : (τ →₀ ℕ) × (σ →₀ ℕ) → K := fun (d, n) ↦ algebraMap R K (coeff d Φ) *
evalSummandMv (∏ i, A i ^ d i) z n`.

The step that made `eval_subst_S` expensive — identifying the `d`-row's sum, where the diagonal
family forced a hand-built "product of two independent geometric series" argument
(`HasSum.mul_of_nonarchimedean` plus a bespoke `Fin 2 →₀ ℕ ≃ ℕ × ℕ` reindexing) because no
multivariate multiplicativity was available at the time — is here a one-liner
(`hasSum_evalMv` on the single series `∏ i, A i ^ d i`, then `HasSum.mul_left`), because
`Langlands.NonarchimedeanMvPowerSeriesEval.evalMv_mul`/`evalMv_pow` are now stated for a general
finite index type. That is what `evalMv_prod`/`evalMv_prod_pow` below package.

* `coeff_bound_prod_mv`, `evalMv_prod` : coefficient boundedness and `evalMv`-multiplicativity
  extended from binary products to arbitrary `Finset` products, by `Finset.induction_on`.
* `evalMv_prod_pow` : `evalMv (∏ i, A i ^ d i) z = ∏ i, (evalMv (A i) z) ^ d i`.
* `coeff_eq_zero_prod_pow_of_degree_lt` : `∏ i, A i ^ d i` has no coefficient below total degree
  `d.degree`, from `MvPowerSeries.le_order_prod`/`le_order_pow_of_constantCoeff_eq_zero` (the same
  argument as `Langlands.LubinTate.coeff_prod_pow_eq_zero_of_degree_lt`, restated here over
  `Finset.univ` rather than `d.support` to keep this file independent of the Lubin-Tate
  development).
* `coeff_subst_finset_degree_G` : the finite-range form of `MvPowerSeries.coeff_subst`.
* `hasSum_row_e_G` / `hasSum_row_d_G` / `tendsto_T_cofinite_zero_G` : the two row identifications
  and the summability of `T`.
* `eval_subst_G` : chaining the two identifications via `HasSum.prod_fiberwise`.

## What this does not do

No Lubin-Tate-specific statement is proved here; `Langlands.LubinTateFormalGroupEval` applies this
lemma to `PhiAssocLeft`/`PhiAssocRight` to get associativity of `FPiEval`.
-/

@[expose] public section

noncomputable section

namespace NonarchimedeanMvPowerSeriesEval

variable {σ τ R K : Type*} [Fintype σ] [Nonempty σ] [DecidableEq σ] [Fintype τ] [Nonempty τ]
  [DecidableEq τ] [CommRing R] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra R K]

omit [Fintype σ] [Nonempty σ] [Fintype τ] [Nonempty τ] [DecidableEq τ] [CompleteSpace K] in
/-- **Coefficient boundedness is preserved by arbitrary finite products**, by `Finset.induction_on`
on `coeff_bound_mul_mv`. -/
theorem coeff_bound_prod_mv {ι : Type*} [DecidableEq ι] {F : ι → MvPowerSeries σ R}
    (hF : ∀ i n, ‖algebraMap R K (MvPowerSeries.coeff n (F i))‖ ≤ 1) (s : Finset ι) :
    ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n (∏ i ∈ s, F i))‖ ≤ 1 := by
  induction s using Finset.induction_on with
  | empty => intro n; simpa using coeff_bound_one_mv (σ := σ) (R := R) (K := K) n
  | insert a s hi ih =>
      intro n
      rw [Finset.prod_insert hi]
      exact coeff_bound_mul_mv (hF _) ih n

omit [Fintype τ] [Nonempty τ] [DecidableEq τ] in
/-- **`evalMv` is multiplicative over arbitrary finite products**, by `Finset.induction_on` on
`evalMv_mul` (the general-`σ` one, from `Langlands.NonarchimedeanMvPowerSeriesEval`). -/
theorem evalMv_prod {ι : Type*} [DecidableEq ι] {F : ι → MvPowerSeries σ R}
    (hF : ∀ i n, ‖algebraMap R K (MvPowerSeries.coeff n (F i))‖ ≤ 1) {z : σ → K}
    (hz : ∀ j, ‖z j‖ < 1) (s : Finset ι) :
    evalMv (∏ i ∈ s, F i) z = ∏ i ∈ s, evalMv (F i) z := by
  induction s using Finset.induction_on with
  | empty => simpa using evalMv_one (σ := σ) (R := R) (K := K) z
  | insert a s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        evalMv_mul (hF _) (coeff_bound_prod_mv hF _) hz, ih]

omit [Nonempty τ] in
/-- **`evalMv (∏ i, A i ^ d i) z = ∏ i, (evalMv (A i) z) ^ d i`** — the multi-index power-product
form of `evalMv_prod`, obtained by combining it with `evalMv_pow` factorwise. This is the
ingredient that replaces `eval_subst_S`'s bespoke two-factor geometric-series argument. -/
theorem evalMv_prod_pow {A : τ → MvPowerSeries σ R}
    (hA : ∀ i n, ‖algebraMap R K (MvPowerSeries.coeff n (A i))‖ ≤ 1) {z : σ → K}
    (hz : ∀ j, ‖z j‖ < 1) (d : τ →₀ ℕ) :
    evalMv (∏ i, A i ^ (d i)) z = ∏ i, (evalMv (A i) z) ^ (d i) := by
  rw [evalMv_prod (fun i ↦ coeff_bound_pow_mv (hA i) (d i)) hz]
  exact Finset.prod_congr rfl fun i _ ↦ evalMv_pow (hA i) hz (d i)

omit [Fintype σ] [Nonempty σ] [DecidableEq σ] [Nonempty τ] [DecidableEq τ] [IsUltrametricDist K]
  [CompleteSpace K] [Algebra R K] in
/-- **`∏ i, A i ^ d i` has no coefficient below total degree `d.degree`**, given every `A i` has
zero constant term: `MvPowerSeries.le_order_prod` reduces to the per-factor bound
`MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero`, and `Finsupp.degree_eq_sum` matches the
resulting sum against `d.degree`. -/
theorem coeff_eq_zero_prod_pow_of_degree_lt {A : τ → MvPowerSeries σ R}
    (hA0 : ∀ i, MvPowerSeries.constantCoeff (A i) = 0) {d : τ →₀ ℕ} {n : σ →₀ ℕ}
    (h : n.degree < d.degree) :
    MvPowerSeries.coeff n (∏ i, A i ^ (d i)) = 0 := by
  have hsum : (d.degree : ℕ∞) ≤ ∑ i : τ, (A i ^ (d i)).order := by
    rw [Finsupp.degree_eq_sum]
    push_cast
    exact Finset.sum_le_sum fun i _ ↦
      MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (hA0 i)
  exact MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (Nat.cast_lt.mpr h)
    (hsum.trans (MvPowerSeries.le_order_prod _ Finset.univ)))

omit [Fintype σ] [Nonempty σ] [DecidableEq σ] [Nonempty τ] [DecidableEq τ] [IsUltrametricDist K]
  [CompleteSpace K] in
/-- **The finite-degree form of `MvPowerSeries.coeff_subst`** for an arbitrary substitutand family
`A` with zero constant terms: the `n`-th coefficient of `Φ.subst A` is the *finite* sum, over
`{d | d.degree ≤ n.degree}`, of `coeff d Φ • coeff n (∏ i, A i ^ d i)`. -/
theorem coeff_subst_finset_degree_G {Φ : MvPowerSeries τ R} {A : τ → MvPowerSeries σ R}
    (hA0 : ∀ i, MvPowerSeries.constantCoeff (A i) = 0) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff n (MvPowerSeries.subst A Φ) =
      ∑ d ∈ (Finsupp.finite_of_degree_le (σ := τ) n.degree).toFinset,
        MvPowerSeries.coeff d Φ • MvPowerSeries.coeff n (∏ i, A i ^ (d i)) := by
  have ha : MvPowerSeries.HasSubst A := MvPowerSeries.hasSubst_of_constantCoeff_zero hA0
  rw [MvPowerSeries.coeff_subst ha, finsum_eq_sum_of_support_subset _
    (s := (Finsupp.finite_of_degree_le (σ := τ) n.degree).toFinset)]
  · refine Finset.sum_congr rfl fun d _ ↦ ?_
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun s ↦ pow_zero _)]
  · intro d hd
    simp only [Function.mem_support] at hd
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    by_contra hge
    push Not at hge
    apply hd
    rw [Finsupp.prod_fintype _ _ (fun s ↦ pow_zero _),
      coeff_eq_zero_prod_pow_of_degree_lt hA0 (by omega), smul_zero]

omit [Nonempty σ] [DecidableEq σ] [Nonempty τ] [DecidableEq τ] [IsUltrametricDist K]
  [CompleteSpace K] in
/-- **Grouping `T (d, n) := algebraMap (coeff d Φ) * evalSummandMv (∏ i, A i ^ d i) z n` by `n`**:
the row `d ↦ T (d, n)` sums to `evalSummandMv (Φ.subst A) z n`, via
`coeff_subst_finset_degree_G` (a finite sum, so `hasSum_sum_of_ne_finset_zero` applies). -/
theorem hasSum_row_e_G {Φ : MvPowerSeries τ R} {A : τ → MvPowerSeries σ R}
    (hA0 : ∀ i, MvPowerSeries.constantCoeff (A i) = 0) (z : σ → K) (n : σ →₀ ℕ) :
    HasSum (fun d : τ →₀ ℕ ↦ algebraMap R K (MvPowerSeries.coeff d Φ) *
        evalSummandMv (∏ i, A i ^ (d i)) z n)
      (evalSummandMv (MvPowerSeries.subst A Φ) z n) := by
  set s := (Finsupp.finite_of_degree_le (σ := τ) n.degree).toFinset with hsdef
  have hzero : ∀ d ∉ s, algebraMap R K (MvPowerSeries.coeff d Φ) *
      evalSummandMv (∏ i, A i ^ (d i)) z n = 0 := by
    intro d hd
    rw [hsdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hd
    unfold evalSummandMv
    rw [coeff_eq_zero_prod_pow_of_degree_lt hA0 hd, map_zero, zero_mul, mul_zero]
  have hval : HasSum
      (fun d : τ →₀ ℕ ↦ algebraMap R K (MvPowerSeries.coeff d Φ) *
        evalSummandMv (∏ i, A i ^ (d i)) z n)
      (∑ d ∈ s, algebraMap R K (MvPowerSeries.coeff d Φ) *
        evalSummandMv (∏ i, A i ^ (d i)) z n) :=
    hasSum_sum_of_ne_finset_zero hzero
  convert hval using 1
  unfold evalSummandMv
  rw [coeff_subst_finset_degree_G hA0 n, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [smul_eq_mul, map_mul]
  ring

omit [Nonempty τ] in
/-- **Grouping `T (d, n) := algebraMap (coeff d Φ) * evalSummandMv (∏ i, A i ^ d i) z n` by `d`**:
the row `n ↦ T (d, n)` sums to `evalSummandMv Φ (fun i ↦ evalMv (A i) z) d`. A single
`HasSum.mul_left` on `hasSum_evalMv` for the series `∏ i, A i ^ d i`, identified through
`evalMv_prod_pow` — no independent-geometric-series argument, unlike `eval_subst_S`'s
corresponding step. -/
theorem hasSum_row_d_G {Φ : MvPowerSeries τ R} {A : τ → MvPowerSeries σ R}
    (hA : ∀ i n, ‖algebraMap R K (MvPowerSeries.coeff n (A i))‖ ≤ 1) {z : σ → K}
    (hz : ∀ j, ‖z j‖ < 1) (d : τ →₀ ℕ) :
    HasSum (fun n : σ →₀ ℕ ↦ algebraMap R K (MvPowerSeries.coeff d Φ) *
        evalSummandMv (∏ i, A i ^ (d i)) z n)
      (evalSummandMv Φ (fun i ↦ evalMv (A i) z) d) := by
  have h1 : HasSum (evalSummandMv (∏ i, A i ^ (d i)) z) (evalMv (∏ i, A i ^ (d i)) z) :=
    hasSum_evalMv (coeff_bound_prod_mv (fun i ↦ coeff_bound_pow_mv (hA i) (d i)) Finset.univ) hz
  have h2 := h1.mul_left (algebraMap R K (MvPowerSeries.coeff d Φ))
  rwa [evalMv_prod_pow hA hz d] at h2

omit [Nonempty τ] [CompleteSpace K] in
/-- **`T` tends to `0` along `cofinite` on `(τ →₀ ℕ) × (σ →₀ ℕ)`**: the uniform bound
`‖T (d, n)‖ ≤ (Finset.univ.sup' _ fun j => ‖z j‖) ^ n.degree` together with
`coeff_eq_zero_prod_pow_of_degree_lt` (`T (d, n) = 0` when `n.degree < d.degree`) confine
`{(d, n) : ‖T (d, n)‖ ≥ ε}` to a finite box, via `Finsupp.finite_of_degree_le`/
`Finsupp.finite_of_degree_lt`. -/
theorem tendsto_T_cofinite_zero_G {Φ : MvPowerSeries τ R} {A : τ → MvPowerSeries σ R}
    (hΦ : ∀ d, ‖algebraMap R K (MvPowerSeries.coeff d Φ)‖ ≤ 1)
    (hA0 : ∀ i, MvPowerSeries.constantCoeff (A i) = 0)
    (hA : ∀ i n, ‖algebraMap R K (MvPowerSeries.coeff n (A i))‖ ≤ 1) {z : σ → K}
    (hz : ∀ j, ‖z j‖ < 1) :
    Filter.Tendsto
      (fun p : (τ →₀ ℕ) × (σ →₀ ℕ) ↦ algebraMap R K (MvPowerSeries.coeff p.1 Φ) *
        evalSummandMv (∏ i, A i ^ (p.1 i)) z p.2)
      Filter.cofinite (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  set r := Finset.univ.sup' Finset.univ_nonempty fun j => ‖z j‖ with hrdef
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg (z (Classical.arbitrary σ)))
    (Finset.le_sup' (fun j => ‖z j‖) (Finset.mem_univ (Classical.arbitrary σ)))
  have hr1 : r < 1 := (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun j _ ↦ hz j)
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one hε hr1
  have hbound : ∀ p : (τ →₀ ℕ) × (σ →₀ ℕ),
      ‖algebraMap R K (MvPowerSeries.coeff p.1 Φ) *
        evalSummandMv (∏ i, A i ^ (p.1 i)) z p.2‖ ≤ r ^ p.2.degree := by
    intro p
    rw [norm_mul]
    calc ‖algebraMap R K (MvPowerSeries.coeff p.1 Φ)‖ *
          ‖evalSummandMv (∏ i, A i ^ (p.1 i)) z p.2‖
        ≤ 1 * r ^ p.2.degree :=
          mul_le_mul (hΦ p.1) (norm_evalSummandMv_le
            (coeff_bound_prod_mv (fun i ↦ coeff_bound_pow_mv (hA i) (p.1 i)) Finset.univ) z p.2)
            (norm_nonneg _) zero_le_one
      _ = r ^ p.2.degree := one_mul _
  have hfin : Set.Finite {p : (τ →₀ ℕ) × (σ →₀ ℕ) |
      Finsupp.degree p.1 ≤ D ∧ Finsupp.degree p.2 < D} := by
    have heq : {p : (τ →₀ ℕ) × (σ →₀ ℕ) |
        Finsupp.degree p.1 ≤ D ∧ Finsupp.degree p.2 < D} =
        {d : τ →₀ ℕ | Finsupp.degree d ≤ D} ×ˢ {n : σ →₀ ℕ | Finsupp.degree n < D} := rfl
    rw [heq]
    exact (Finsupp.finite_of_degree_le (σ := τ) D).prod (Finsupp.finite_of_degree_lt (σ := σ) D)
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
    have hzz : algebraMap R K (MvPowerSeries.coeff p.1 Φ) *
        evalSummandMv (∏ i, A i ^ (p.1 i)) z p.2 = 0 := by
      unfold evalSummandMv
      rw [coeff_eq_zero_prod_pow_of_degree_lt hA0 hlt, map_zero, zero_mul, mul_zero]
    rw [hzz] at hp; simp at hp; linarith
  exact ⟨by omega, hnd⟩

omit [DecidableEq σ] [Fintype τ] [Nonempty τ] [DecidableEq τ] [CompleteSpace K] in
/-- **Every component of the substituted family evaluates into the maximal ideal**, so the outer
`evalMv Φ` is applied at a legitimate point — no extra hypothesis is needed for the main theorem
beyond zero constant terms and bounded coefficients. -/
theorem norm_evalMv_lt_one {A : MvPowerSeries σ R}
    (hA : ∀ n, ‖algebraMap R K (MvPowerSeries.coeff n A)‖ ≤ 1)
    (hA0 : MvPowerSeries.constantCoeff A = 0) {z : σ → K} (hz : ∀ j, ‖z j‖ < 1) :
    ‖evalMv A z‖ < 1 :=
  lt_of_le_of_lt (norm_evalMv_le hA hA0 hz)
    ((Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun j _ ↦ hz j))

set_option maxHeartbeats 1000000 in
/-- **General eval-subst compatibility.** `evalMv (Φ.subst A) z = evalMv Φ (fun i ↦ evalMv (A i) z)`
for a multivariate outer `Φ : MvPowerSeries τ R` and an *arbitrary* substitutand family
`A : τ → MvPowerSeries σ R` with zero constant terms and bounded coefficients, `τ` and `σ`
arbitrary finite index types. Subsumes `NonarchimedeanPowerSeriesEval.eval_subst_A` (`τ` a
one-point type) and `NonarchimedeanMvPowerSeriesEvalFin2.eval_subst_S` (`A` diagonal). -/
theorem eval_subst_G {Φ : MvPowerSeries τ R} {A : τ → MvPowerSeries σ R}
    (hΦ : ∀ d, ‖algebraMap R K (MvPowerSeries.coeff d Φ)‖ ≤ 1)
    (hA0 : ∀ i, MvPowerSeries.constantCoeff (A i) = 0)
    (hA : ∀ i n, ‖algebraMap R K (MvPowerSeries.coeff n (A i))‖ ≤ 1) {z : σ → K}
    (hz : ∀ j, ‖z j‖ < 1) :
    evalMv (MvPowerSeries.subst A Φ) z = evalMv Φ (fun i ↦ evalMv (A i) z) := by
  set T : (τ →₀ ℕ) × (σ →₀ ℕ) → K :=
    fun p ↦ algebraMap R K (MvPowerSeries.coeff p.1 Φ) *
      evalSummandMv (∏ i, A i ^ (p.1 i)) z p.2 with hTdef
  have hTsum : Summable T :=
    IsUltrametricDist.summable_of_tendsto_zero (tendsto_T_cofinite_zero_G hΦ hA0 hA hz)
  set S := ∑' p, T p with hSdef
  have hTS : HasSum T S := hTsum.hasSum
  -- group by `d`
  have hbyD : HasSum (fun d : τ →₀ ℕ ↦ evalSummandMv Φ (fun i ↦ evalMv (A i) z) d) S :=
    hTS.prod_fiberwise (fun d ↦ hasSum_row_d_G hA hz d)
  have hAz : ∀ i, ‖evalMv (A i) z‖ < 1 := fun i ↦ norm_evalMv_lt_one (hA i) (hA0 i) hz
  have hSeq1 : S = evalMv Φ (fun i ↦ evalMv (A i) z) := hbyD.unique (hasSum_evalMv hΦ hAz)
  -- group by `n`
  have hbyE : HasSum (evalSummandMv (MvPowerSeries.subst A Φ) z) S := by
    have hTswap : HasSum (fun q : (σ →₀ ℕ) × (τ →₀ ℕ) ↦ T (q.2, q.1)) S :=
      (Equiv.hasSum_iff (Equiv.prodComm (σ →₀ ℕ) (τ →₀ ℕ))).mpr hTS
    exact hTswap.prod_fiberwise (fun n ↦ hasSum_row_e_G hA0 z n)
  have hSeq2 : evalMv (MvPowerSeries.subst A Φ) z = S := by
    unfold evalMv; exact hbyE.tsum_eq
  rw [hSeq2, hSeq1]

end NonarchimedeanMvPowerSeriesEval

end
