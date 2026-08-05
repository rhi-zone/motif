import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.Minpoly
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.GroupWithZero.WithZero
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Uniqueness of the extension of a complete nonarchimedean valuation

This file bridges the `ValuationSubring`/`ValuativeRel` formalism (used by
`IsNonarchimedeanLocalField`) with the `NormedField`/`AbsoluteValue` formalism (used by
`Mathlib.Analysis.Normed.Unbundled.SpectralNorm`), and proves that for `K` a complete
nonarchimedean local field and `L / K` algebraic, a `ValuationSubring` of `L` whose comap along
`algebraMap K L` is `𝒪[K]` is unique. Since `K`-automorphisms of `L` preserve that comap condition
(`ValuationSubring.comap_smul_eq`), the decomposition subgroup of such an extension is all of
`Gal(L/K)`.

## Main results

* `MulArchimedean.of_units` : `MulArchimedean Γ₀ˣ` implies `MulArchimedean Γ₀`, for `Γ₀` a
  linearly ordered commutative group with zero.
* `Valuation.exists_pow_le_of_isAlgebraic` : for `v : Valuation L Γ₀` and `x : L` nonzero and
  algebraic over `K`, some coefficient index `i < (minpoly K x).natDegree` satisfies
  `v x ^ (natDegree - i) ≤ v (algebraMap K L (coeff i))`.
* `Valuation.exists_pow_eq_of_isAlgebraic` : the same setting yields an *exact* equality
  `v (algebraMap K L c) = v x ^ m` for some `c ≠ 0` and `1 ≤ m ≤ (minpoly K x).natDegree`.
* `Valuation.exists_rpow_eq_of_isEquiv` : Hölder's uniqueness theorem for `ℝ≥0`-valued
  valuations — equivalent valuations `v₁`, `v₂` with `v₁` nontrivial satisfy `v₂ = v₁ ^ t` for a
  unique `t > 0`.
* `LocalField.exists_rankOne_compatible` : for a `ValuationSubring A` of `L` with
  `A.comap (algebraMap K L) = 𝒪[K]`, a `RankOne A.valuation` instance whose embedding
  `A.ValueGroup → ℝ≥0`, pulled back along `A.valuation.restrict ∘ algebraMap K L`, reproduces
  `‖·‖` on `K`.
* `LocalField.exists_rankOne_absoluteValue_extends` : under the same hypotheses, an
  `AbsoluteValue L ℝ` extending `‖·‖` on `K` whose closed unit ball is `A`.
* `LocalField.valuationSubring_eq_of_comap_eq` and
  `LocalField.valuationSubring_eq_of_comap_eq_of_isNonarchimedeanLocalField` : uniqueness of the
  valuation subring extension, for `K` given by the abstract normed-field bundle and by
  `IsNonarchimedeanLocalField` respectively.
* `ValuationSubring.comap_smul_eq` : the comap of a `(L ≃ₐ[K] L)`-translate of a valuation subring
  along `algebraMap K L` is independent of the translate.
* `PseudoMetricSpace.toUniformSpace_eq_of_toDist_eq` and `CompleteSpace.of_pseudoMetricSpace_toDist_eq` :
  transport a `CompleteSpace` instance across two `PseudoMetricSpace` structures on the same type
  that agree on `dist` but were built via unrelated, non-defeq constructions — the tool needed to
  reconcile a `Valued`/`RankOne`-built `NontriviallyNormedField` with a `spectralNorm`-built one on
  the same field (see the "nineteenth pass" and later entries of `ROADMAP.md`).
* `LocalField.exists_completeSpace_of_finiteDimensional` : for `A : ValuationSubring L` with
  `A.comap (algebraMap K L) = 𝒪[K]`, `K` complete, `L / K` finite, `L` is complete with respect to
  the `Valued.mk' A.valuation`-determined uniform space — the permanent, reusable assembly of the
  "twentieth pass" transport lemmas above, composed with `spectralNorm.completeSpace`.

## Implementation notes

`exists_rankOne_compatible` combines two facts:

1. **Rank preservation under algebraic extension**: if `K` carries a rank-≤-1 (real-valued)
   valuation and `L / K` is algebraic, any valuation subring `A` of `L` restricting to `𝒪[K]` is
   again of rank ≤ 1, i.e. `A.valuation` admits an order embedding of `A.ValueGroup` into `ℝ≥0`.
   Given nontriviality (which transfers from `𝒪[K]` along the comap hypothesis), by
   `Valuation.nonempty_rankOne_iff_mulArchimedean` this is equivalent to
   `MonoidWithZeroHom.ValueGroup₀ (.ofClass A.valuation)` being `MulArchimedean`.
2. **Compatible normalization**: the embedding `A.ValueGroup → ℝ≥0` can be chosen to agree with
   the embedding used to build the `NormedField K` structure, so that the extended norm restricts
   to `‖·‖` on `K` and not merely to an equivalent norm.

Everything downstream is formal. `exists_rankOne_absoluteValue_extends` builds
`Valued L A.ValueGroup` via `Valued.mk'` (which needs no ambient topology on `L`), transports the
`RankOne A.valuation` instance into a `NontriviallyNormedField L` via
`Valued.toNontriviallyNormedField`, and takes `f := NormedField.toAbsoluteValue L`; then
`f x ≤ 1 ↔ x ∈ A` is `Valued.toNormedField.norm_le_one_iff` composed with
`ValuationSubring.valuation_le_one_iff`.

The hypothesis `[(NormedField.valuation (K := K)).Compatible]` is necessary:
`[NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]` are independent parameters,
and nothing among them forces `ValuativeRel.valuation K` to be nontrivial relative to `‖·‖`. With
`ValuativeRel K := ValuativeRel.ofValuation (1 : Valuation K ℝ≥0)` and `A := (⊤ : ValuationSubring
L)`, the comap hypothesis holds while `A.valuation` is trivial, so no `RankOne A.valuation`
instance exists.

## References

* Bourbaki, *Commutative Algebra*, VI §10
* Engler–Prestel, *Valued Fields*, Thm. 3.2.4
-/

noncomputable section

open ValuativeRel Valuation IsLocalRing
open scoped NNReal

section ReusableInfrastructure

/-- If the unit group `Γ₀ˣ` of a linearly ordered commutative group with zero is `MulArchimedean`,
so is `Γ₀`. Transferred along the order isomorphism `WithZero Γ₀ˣ ≃*o Γ₀`
(`WithZero.withZeroUnitsEquiv`). -/
theorem MulArchimedean.of_units {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (h : MulArchimedean Γ₀ˣ) : MulArchimedean Γ₀ := by
  classical
  have hwz : MulArchimedean (WithZero Γ₀ˣ) := WithZero.instMulArchimedean Γ₀ˣ
  exact MulArchimedean.comap (WithZero.withZeroUnitsEquiv (G := Γ₀)).symm.toMonoidHom
    WithZero.withZeroUnitsEquiv_symm_strictMono

/-- Ultrametric bound via the minimal polynomial: for `v` a valuation on `L` and `x : L` nonzero
and algebraic over a subfield `K` with `n := (minpoly K x).natDegree`, there is an index `i < n`
with `v x ^ (n - i) ≤ v (algebraMap K L ((minpoly K x).coeff i))`.

Obtained by applying the ultrametric inequality to `x ^ n = -∑ i ∈ range n, c i • x ^ i`, where the
maximal term on the right dominates. Only algebraicity of `x` over `K` is required, not finiteness
of `L / K`, and no compatibility between valuations on `K` and on `L` beyond `v` itself. -/
theorem Valuation.exists_pow_le_of_isAlgebraic {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀) {x : L} (hx : x ≠ 0)
    (halg : IsAlgebraic K x) :
    ∃ i < (minpoly K x).natDegree,
      v x ^ ((minpoly K x).natDegree - i) ≤ v (algebraMap K L ((minpoly K x).coeff i)) := by
  have hxi : IsIntegral K x := halg.isIntegral
  have hn0 : 0 < (minpoly K x).natDegree := minpoly.natDegree_pos hxi
  have hmonic : (minpoly K x).Monic := minpoly.monic hxi
  have haeval : (Polynomial.aeval x) (minpoly K x) = 0 := minpoly.aeval K x
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ] at haeval
  simp only [Algebra.smul_def, hmonic.coeff_natDegree, map_one, one_mul] at haeval
  set n := (minpoly K x).natDegree with hn
  have hxn : x ^ n = -∑ i ∈ Finset.range n, algebraMap K L (((minpoly K x).coeff i)) * x ^ i := by
    linear_combination haeval
  set f : ℕ → Γ₀ := fun i => v (algebraMap K L ((minpoly K x).coeff i)) * v x ^ i with hf
  have hne : (Finset.range n).Nonempty := Finset.nonempty_range_iff.mpr hn0.ne'
  have hbound : v x ^ n ≤ (Finset.range n).sup' hne f := by
    rw [← Valuation.map_pow, hxn, Valuation.map_neg]
    apply Valuation.map_sum_le
    intro i hi
    simp only [Valuation.map_mul, Valuation.map_pow, hf]
    exact Finset.le_sup' f hi
  obtain ⟨i, hi, hle⟩ := (Finset.le_sup'_iff hne).mp hbound
  simp only [hf] at hle
  have hvx_ne : v x ≠ 0 := (Valuation.ne_zero_iff v).mpr hx
  have hile : i ≤ n := le_of_lt (Finset.mem_range.mp hi)
  have hvxi_pos : (0 : Γ₀) < v x ^ i := zero_lt_iff.mpr (pow_ne_zero i hvx_ne)
  refine ⟨i, Finset.mem_range.mp hi, ?_⟩
  have heq : v x ^ (n - i) * v x ^ i ≤ v (algebraMap K L ((minpoly K x).coeff i)) * v x ^ i := by
    rwa [← pow_add, Nat.sub_add_cancel hile]
  have heq' : v x ^ i * v x ^ (n - i) ≤ v x ^ i * v (algebraMap K L ((minpoly K x).coeff i)) := by
    rw [mul_comm (v x ^ i), mul_comm (v x ^ i)]; exact heq
  exact (mul_le_mul_iff_right₀ hvxi_pos).mp heq'

/-- Exact form of the minimal polynomial bound: for `v` a valuation on `L` and `x : L` nonzero and
algebraic over a subfield `K`, some power `x ^ m` with `1 ≤ m ≤ (minpoly K x).natDegree` has
exactly the valuation of `algebraMap K L c` for some nonzero `c : K`.

Where `exists_pow_le_of_isAlgebraic` bounds `v x` above by a `K`-value, the equality here gives the
reverse direction as well: if `1 < v x` then `1 < v (algebraMap K L c) = v x ^ m`, exhibiting a
`K`-element of valuation exceeding `1` dominated by a power of `x`. This is the step that transfers
rank ≤ 1 across an algebraic extension (Bourbaki, *Comm. Alg.* VI §10.1; Engler–Prestel, *Valued
Fields* Thm. 3.2.4), obtained here without passing through `Polynomial.reverse` or `minpoly K x⁻¹`.

The minimal polynomial relation writes `0` as the sum of the terms
`t i := algebraMap K L ((minpoly K x).coeff i) * x ^ i`. Were the values `v (t i)` pairwise
distinct over the support of the coefficients, the maximal term would dominate the sum
(`Valuation.map_sum_eq_of_lt`), forcing `v 0 ≠ 0`. Two distinct indices `i < j` therefore satisfy
`v (t i) = v (t j)`; cancelling `v x ^ i` gives the claim with `m := j - i` and
`c := (minpoly K x).coeff i * ((minpoly K x).coeff j)⁻¹`. -/
theorem Valuation.exists_pow_eq_of_isAlgebraic {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀) {x : L} (hx : x ≠ 0)
    (halg : IsAlgebraic K x) :
    ∃ (m : ℕ) (c : K), 1 ≤ m ∧ m ≤ (minpoly K x).natDegree ∧ c ≠ 0 ∧
      v (algebraMap K L c) = v x ^ m := by
  classical
  have hxi : IsIntegral K x := halg.isIntegral
  set p := minpoly K x with hp
  set n := p.natDegree with hn
  have hn0 : 0 < n := minpoly.natDegree_pos hxi
  have hmonic : p.Monic := minpoly.monic hxi
  have haeval : (Polynomial.aeval x) p = 0 := minpoly.aeval K x
  set t : ℕ → L := fun i => algebraMap K L (p.coeff i) * x ^ i with ht
  have hsum0 : ∑ i ∈ Finset.range (n + 1), t i = 0 := by
    have hrw := Polynomial.aeval_eq_sum_range (R := K) (S := L) (p := p) x
    simp only [Algebra.smul_def] at hrw
    rw [ht, ← hrw]
    exact haeval
  have hvx_ne : v x ≠ 0 := (Valuation.ne_zero_iff v).mpr hx
  have halgmap_inj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have ht_eq_zero_iff : ∀ i, t i = 0 ↔ p.coeff i = 0 := by
    intro i
    simp only [ht, mul_eq_zero, pow_eq_zero_iff' , hx, ne_eq, false_and, or_false,
      map_eq_zero_iff _ halgmap_inj]
  -- **Step 1**: `S`, the support of the coefficient sequence within `range (n + 1)`. Nonempty
  -- since the leading coefficient `p.coeff n = 1 ≠ 0` (monic).
  set S : Finset ℕ := (Finset.range (n + 1)).filter (fun i => p.coeff i ≠ 0) with hS
  have hnS : n ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_self n, by rw [hmonic.coeff_natDegree]; exact one_ne_zero⟩
  have hSne : S.Nonempty := ⟨n, hnS⟩
  have hsub : ∑ i ∈ S, t i = ∑ i ∈ Finset.range (n + 1), t i := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro i hiR hiS
    have hi0 : p.coeff i = 0 := by
      by_contra hne
      exact hiS (Finset.mem_filter.mpr ⟨hiR, hne⟩)
    exact (ht_eq_zero_iff i).mpr hi0
  have hsumS : ∑ i ∈ S, t i = 0 := hsub.trans hsum0
  -- **Step 2**: some two distinct indices in `S` must tie in `v`-valuation of their terms --
  -- otherwise the (uniquely) maximal term would dominate the sum `∑ i ∈ S, t i = 0`, forcing its
  -- (nonzero) valuation to be `0`.
  have hexists_tie : ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ v (t i) = v (t j) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j, hjS, hmax⟩ := Finset.exists_max_image S (fun i => v (t i)) hSne
    have hstrict : ∀ i ∈ S \ {j}, v (t i) < v (t j) := by
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hi
      exact lt_of_le_of_ne (hmax i hi.1) (hcon i hi.1 j hjS hi.2)
    have hdom := v.map_sum_eq_of_lt hjS hstrict
    rw [hsumS, Valuation.map_zero] at hdom
    have hcj0 : p.coeff j ≠ 0 := (Finset.mem_filter.mp hjS).2
    have htj_ne : t j ≠ 0 := fun h => hcj0 ((ht_eq_zero_iff j).mp h)
    exact (Valuation.ne_zero_iff v).mpr htj_ne hdom.symm
  obtain ⟨i, hiS, j, hjS, hij, hveq⟩ := hexists_tie
  -- **Step 3**: WLOG `i < j`; cancel the common factor `v x ^ i` to get `v (algebraMap c) = v x ^
  -- m` exactly, for `c := p.coeff i * (p.coeff j)⁻¹` and `m := j - i`.
  have hiS' := Finset.mem_filter.mp hiS
  have hjS' := Finset.mem_filter.mp hjS
  have hci : p.coeff i ≠ 0 := hiS'.2
  have hcj : p.coeff j ≠ 0 := hjS'.2
  have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hiS'.1)
  have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjS'.1)
  -- symmetric core argument, applied to whichever of `i, j` is smaller
  have hcore : ∀ a b : ℕ, a < b → b ≤ n → p.coeff a ≠ 0 → p.coeff b ≠ 0 →
      v (t a) = v (t b) →
      ∃ (m : ℕ) (c : K), 1 ≤ m ∧ m ≤ n ∧ c ≠ 0 ∧ v (algebraMap K L c) = v x ^ m := by
    intro a b hab hbn hca hcb hveq'
    refine ⟨b - a, p.coeff a * (p.coeff b)⁻¹, by omega, by omega, mul_ne_zero hca (inv_ne_zero hcb),
      ?_⟩
    have hxpow_ne : v x ^ a ≠ 0 := pow_ne_zero a hvx_ne
    have hveq_terms : v (algebraMap K L (p.coeff a)) * v x ^ a
        = v (algebraMap K L (p.coeff b)) * v x ^ b := by
      simpa only [ht, Valuation.map_mul, Valuation.map_pow] using hveq'
    have hveq'' : v (algebraMap K L (p.coeff a)) * v x ^ a
        = v (algebraMap K L (p.coeff b)) * (v x ^ a * v x ^ (b - a)) := by
      rw [← pow_add, Nat.add_sub_cancel' hab.le]; exact hveq_terms
    have hveq''' : v (algebraMap K L (p.coeff a))
        = v (algebraMap K L (p.coeff b)) * v x ^ (b - a) := by
      have hshuf := hveq''
      rw [mul_comm (v x ^ a) (v x ^ (b-a)), ← mul_assoc] at hshuf
      exact mul_right_cancel₀ hxpow_ne hshuf
    have hcb0 : v (algebraMap K L (p.coeff b)) ≠ 0 :=
      (Valuation.ne_zero_iff v).mpr (fun h => hcb ((map_eq_zero_iff _ halgmap_inj).mp h))
    rw [map_mul, map_inv₀, map_mul, map_inv₀, hveq''',
      mul_comm (v (algebraMap K L (p.coeff b))) (v x ^ (b - a)), mul_assoc,
      mul_inv_cancel₀ hcb0, mul_one]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hcore i j hlt hjle hci hcj hveq
  · obtain ⟨m, c, hm1, hmn, hc0, hceq⟩ := hcore j i hgt hile hcj hci hveq.symm
    exact ⟨m, c, hm1, hmn, hc0, hceq⟩

/-- Hölder's uniqueness theorem, specialized to `ℝ≥0`-valued valuations: equivalent valuations
`v₁ v₂ : Valuation K ℝ≥0` with `v₁` nontrivial satisfy `v₂ x = v₁ x ^ t` for a fixed `t > 0`.

This is the uniqueness half of the embedding theorem for archimedean linearly ordered groups (any
two strictly monotone embeddings into `ℝ` agree up to a positive real scalar), stated for
embeddings already landing in `ℝ≥0`, which avoids `MulArchimedean`/`ValueGroup₀` as a separate
hypothesis: the image subgroup of `(ℝ, +)` obtained via `Real.log` is archimedean automatically.
Mathlib has the existence half, `Archimedean.exists_orderAddMonoidHom_real_injective`, but not this
one.

The proof is the classical density argument. Fix an anchor `c₀` with `1 < v₁ c₀`, hence `1 < v₂ c₀`
by equivalence. For every `x` the identity `v c₀ ^ p < v x ^ n ↔ v (c₀ ^ p / x ^ n) < 1` is a
comparison against `1` and so transfers across `hequiv`; running it over all `p / n ∈ ℚ` and using
density of `ℚ` in `ℝ` forces
`Real.log (v₁ x) / Real.log (v₁ c₀) = Real.log (v₂ x) / Real.log (v₂ c₀)`. -/
theorem Valuation.exists_rpow_eq_of_isEquiv {K : Type*} [Field K] (v₁ v₂ : Valuation K ℝ≥0)
    [hv₁ : v₁.IsNontrivial] (hequiv : v₁.IsEquiv v₂) :
    ∃ t : ℝ, 0 < t ∧ ∀ x : K, v₂ x = v₁ x ^ t := by
  classical
  -- Step 1: an anchor `c₀` with `v₁ c₀ > 1` (hence `v₂ c₀ > 1` too, via `hequiv`).
  obtain ⟨c, hc0, hc1⟩ := hv₁.exists_val_nontrivial
  have hcne0 : c ≠ 0 := (Valuation.ne_zero_iff v₁).mp hc0
  obtain ⟨c₀, hv1c0⟩ : ∃ c₀ : K, 1 < v₁ c₀ := by
    rcases lt_or_gt_of_ne hc1 with hlt | hgt
    · exact ⟨c⁻¹, by
        rw [map_inv₀]
        exact (one_lt_inv₀ (zero_lt_iff.mpr hc0)).mpr hlt⟩
    · exact ⟨c, hgt⟩
  have hv2c0 : 1 < v₂ c₀ := by
    have h := hequiv.lt_iff_lt (x := (1 : K)) (y := c₀)
    rw [map_one, map_one] at h
    exact h.mp hv1c0
  set L1c : ℝ := Real.log (v₁ c₀ : ℝ) with hL1c_def
  set L2c : ℝ := Real.log (v₂ c₀ : ℝ) with hL2c_def
  have hL1c_pos : 0 < L1c := Real.log_pos (by exact_mod_cast hv1c0)
  have hL2c_pos : 0 < L2c := Real.log_pos (by exact_mod_cast hv2c0)
  set t : ℝ := L2c / L1c with ht_def
  have ht_pos : 0 < t := div_pos hL2c_pos hL1c_pos
  refine ⟨t, ht_pos, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [NNReal.zero_rpow ht_pos.ne']
  -- Step 2: the core valuation-level equivalence, for any integer power `p` of `c₀` and natural
  -- power `n` of `x` -- purely algebraic, transfers across `hequiv` via the comparison to `1`.
  have hv1x_ne : v₁ x ≠ 0 := (Valuation.ne_zero_iff v₁).mpr hx0
  have hv2x_ne : v₂ x ≠ 0 := (Valuation.ne_zero_iff v₂).mpr hx0
  have hcompare : ∀ (v : Valuation K ℝ≥0), v x ≠ 0 → ∀ (p : ℤ) (n : ℕ),
      v c₀ ^ p < v x ^ n ↔ v (c₀ ^ p / x ^ n) < 1 := by
    intro v hvne p n
    rw [map_div₀, map_zpow₀, map_pow]
    exact (div_lt_one (zero_lt_iff.mpr (pow_ne_zero n hvne))).symm
  have hvcore : ∀ (p : ℤ) (n : ℕ), v₁ c₀ ^ p < v₁ x ^ n ↔ v₂ c₀ ^ p < v₂ x ^ n := by
    intro p n
    rw [hcompare v₁ hv1x_ne p n, hcompare v₂ hv2x_ne p n]
    have hiff := hequiv.lt_iff_lt (x := c₀ ^ p / x ^ n) (y := (1 : K))
    rwa [map_one, map_one] at hiff
  -- Step 3: transport `hvcore` to a real-log statement, for all `p : ℤ`, `n : ℕ`.
  have hv1x_pos : (0 : ℝ) < (v₁ x : ℝ) := by exact_mod_cast zero_lt_iff.mpr hv1x_ne
  have hv2x_pos : (0 : ℝ) < (v₂ x : ℝ) := by exact_mod_cast zero_lt_iff.mpr hv2x_ne
  have hv1c0_pos : (0 : ℝ) < (v₁ c₀ : ℝ) := by positivity
  have hv2c0_pos : (0 : ℝ) < (v₂ c₀ : ℝ) := by positivity
  have hlogcore : ∀ (p : ℤ) (n : ℕ),
      (p : ℝ) * L1c < (n : ℝ) * Real.log (v₁ x : ℝ) ↔
        (p : ℝ) * L2c < (n : ℝ) * Real.log (v₂ x : ℝ) := by
    intro p n
    have h1 : (p : ℝ) * L1c < (n : ℝ) * Real.log (v₁ x : ℝ) ↔ v₁ c₀ ^ p < v₁ x ^ n := by
      rw [hL1c_def, ← Real.log_zpow, ← Real.log_pow,
        Real.log_lt_log_iff (zpow_pos hv1c0_pos p) (pow_pos hv1x_pos n),
        ← NNReal.coe_zpow, ← NNReal.coe_pow, NNReal.coe_lt_coe]
    have h2 : (p : ℝ) * L2c < (n : ℝ) * Real.log (v₂ x : ℝ) ↔ v₂ c₀ ^ p < v₂ x ^ n := by
      rw [hL2c_def, ← Real.log_zpow, ← Real.log_pow,
        Real.log_lt_log_iff (zpow_pos hv2c0_pos p) (pow_pos hv2x_pos n),
        ← NNReal.coe_zpow, ← NNReal.coe_pow, NNReal.coe_lt_coe]
    rw [h1, h2]
    exact hvcore p n
  -- Step 4: specialize to `p := q.num`, `n := q.den` for `q : ℚ`, converting `(q:ℝ) * A < B` to
  -- the integer/natural-power form via `Rat.cast_def`.
  have hqcast : ∀ (A B : ℝ) (q : ℚ), (q : ℝ) * A < B ↔ (q.num : ℝ) * A < (q.den : ℝ) * B := by
    intro A B q
    rw [Rat.cast_def, div_mul_eq_mul_div, div_lt_iff₀ (by exact_mod_cast q.den_pos),
      mul_comm B (q.den : ℝ)]
  have hrat : ∀ q : ℚ, (q : ℝ) * L1c < Real.log (v₁ x : ℝ) ↔
      (q : ℝ) * L2c < Real.log (v₂ x : ℝ) := by
    intro q
    rw [hqcast L1c _ q, hqcast L2c _ q]
    exact hlogcore q.num q.den
  -- Step 5: density of `ℚ` in `ℝ` forces the two ratios to agree exactly.
  have hAB : Real.log (v₁ x : ℝ) / L1c = Real.log (v₂ x : ℝ) / L2c := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      have h1 : ¬ (q : ℝ) * L1c < Real.log (v₁ x : ℝ) := by
        rw [not_lt, ← div_le_iff₀ hL1c_pos]; exact hq1.le
      have h2 : (q : ℝ) * L2c < Real.log (v₂ x : ℝ) := by
        rw [← lt_div_iff₀ hL2c_pos]; exact hq2
      exact h1 ((hrat q).mpr h2)
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      have h1 : (q : ℝ) * L1c < Real.log (v₁ x : ℝ) := by
        rw [← lt_div_iff₀ hL1c_pos]; exact hq2
      have h2 : ¬ (q : ℝ) * L2c < Real.log (v₂ x : ℝ) := by
        rw [not_lt, ← div_le_iff₀ hL2c_pos]; exact hq1.le
      exact h2 ((hrat q).mp h1)
  have hkey : Real.log (v₁ x : ℝ) * L2c = Real.log (v₂ x : ℝ) * L1c :=
    (div_eq_div_iff hL1c_pos.ne' hL2c_pos.ne').mp hAB
  have hlogeq : Real.log (v₂ x : ℝ) = t * Real.log (v₁ x : ℝ) := by
    rw [ht_def]; field_simp; linarith [hkey]
  have hv2x_eq : (v₂ x : ℝ) = (v₁ x : ℝ) ^ t := by
    rw [Real.rpow_def_of_pos hv1x_pos, mul_comm, ← hlogeq, Real.exp_log hv2x_pos]
  apply NNReal.coe_injective
  rw [NNReal.coe_rpow]
  exact hv2x_eq

end ReusableInfrastructure

section UniformSpaceTransport

/-- Two `PseudoMetricSpace` structures on the same type that agree on `dist` induce the same
`UniformSpace` structure, regardless of how each instance's `toUniformSpace` field was
independently constructed.

This is the uniform-space-level corollary of `PseudoMetricSpace.ext`: that lemma proves full
structural equality `m = m'` of two `PseudoMetricSpace`s from `dist` equality alone, using each
side's own `uniformity_dist` axiom (a proof every `PseudoMetricSpace` instance is required to
carry, pinning `uniformity = ⨅ ε>0, 𝓟{p | dist p.1 p.2 < ε}` as a function of `dist`) together
with `UniformSpace.ext`. Taking `toUniformSpace` of that equality gives this. -/
theorem PseudoMetricSpace.toUniformSpace_eq_of_toDist_eq {α : Type*} {m m' : PseudoMetricSpace α}
    (h : m.toDist = m'.toDist) : m.toUniformSpace = m'.toUniformSpace := by
  rw [PseudoMetricSpace.ext h]

/-- Transport a `CompleteSpace` instance across two `PseudoMetricSpace` structures on the same
type that agree on `dist`, even when their `UniformSpace` fields were built via unrelated
constructions and are not defeq.

This is the missing tool identified by the "nineteenth pass" of `ROADMAP.md`'s Phase 2b: composing
a `Valued`/`RankOne`-built `NontriviallyNormedField M` (the totally-ramified route, via
`Valued.mk'` + `Valued.toNontriviallyNormedField`) with `spectralNorm.completeSpace` (which is
pinned to `spectralNorm.uniformSpace K M`, built from the unrelated abstract sup-over-embeddings
construction in `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`) fails as a hard type mismatch,
not a slow-to-unify defeq issue, because the two `UniformSpace M` terms come from unrelated
construction paths. Mathlib has `UniformSpace.replaceTopology` (topology level only) but no
`UniformSpace.replaceUniformity` / `CompleteSpace.replaceUniformity`; `PseudoMetricSpace.ext`,
keyed on `dist` rather than on the construction route, supplies the missing uniformity-level
transport instead. The `dist` equality hypothesis itself follows from pointwise norm equality
(e.g. via `spectralNorm_unique_field_norm_ext`, already used elsewhere in this file), funext'd. -/
theorem CompleteSpace.of_pseudoMetricSpace_toDist_eq {α : Type*} {m m' : PseudoMetricSpace α}
    (h : m.toDist = m'.toDist) (h' : @CompleteSpace α m'.toUniformSpace) :
    @CompleteSpace α m.toUniformSpace :=
  (PseudoMetricSpace.toUniformSpace_eq_of_toDist_eq h).symm ▸ h'

end UniformSpaceTransport

section NormedFieldValuativeRelBridge

/-- If the norm on `K` equals `RankOne.hom v ∘ v.restrict` for a `Compatible`, `RankOne` valuation
`v`, then the norm's canonical valuation `NormedField.valuation` is itself `Compatible` with the
ambient `ValuativeRel K`.

The hypothesis `hnorm` holds by `rfl` whenever the `NormedField`/`Valued` structure on `K` is built
from `v` — via `Valued.toNormedField` or `Valued.toNontriviallyNormedField`, by
`Valued.toNormedField.coe_valuation_eq_rankOne_hom_comp_valuation`. This supplies the
`Compatible` instance required by `LocalField.exists_rankOne_compatible`, which rules out a
`ValuativeRel K` unrelated to the norm. -/
theorem NormedField.valuation_compatible_of_eq_rankOne_hom_comp_restrict
    {K Γ₀ : Type*} [NormedField K] [IsUltrametricDist K] [ValuativeRel K]
    [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) [hv : RankOne v] [v.Compatible]
    (hnorm : ∀ x : K, (NormedField.valuation x : ℝ≥0) = RankOne.hom v (v.restrict x)) :
    (NormedField.valuation (K := K)).Compatible where
  vle_iff_le x y := by
    rw [Valuation.Compatible.vle_iff_le (v := v), ← v.restrict_le_iff,
      ← (RankOne.strictMono v).le_iff_le, ← hnorm x, ← hnorm y]

end NormedFieldValuativeRelBridge

namespace LocalField

section NormedFieldBridge

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible]
  {L : Type*} [Field L] [Algebra K L]

/-- A `ValuationSubring A` of an algebraic extension `L / K` with
`A.comap (algebraMap K L) = 𝒪[K]` admits a `RankOne` structure on `A.valuation` whose embedding
`A.ValueGroup → ℝ≥0` is normalized to the `NontriviallyNormedField` structure on `K`: pulling it
back along `A.valuation.restrict ∘ algebraMap K L` reproduces `‖·‖`.

This combines rank preservation under an algebraic extension (equivalently, `MulArchimedean` of
`MonoidWithZeroHom.ValueGroup₀ (.ofClass A.valuation)`, by
`Valuation.nonempty_rankOne_iff_mulArchimedean`) with the normalization of the resulting embedding
into `ℝ≥0` to match the one already fixed on `K`.

The section hypothesis `[(NormedField.valuation (K := K)).Compatible]` is `Valuation.Compatible`
from `Mathlib.RingTheory.Valuation.ValuativeRel.Basic`, i.e. `x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖`. It yields
`ValuativeRel.IsNontrivial K` and `ValuativeRel.IsRankLeOne K`, hence a `RankOne (valuation K)`
instance whose `hom'` matches `‖·‖` exactly rather than up to equivalence (`hRK_compat` below);
this is the statement for the base field itself, i.e. the case `L = K`, `A = 𝒪[K]`. Without it the
statement is false: for the trivial `ValuativeRel K` and `A = ⊤` the comap hypothesis holds while
`A.valuation` is trivial.

The proof extends rank ≤ 1 from `K` to `L` as follows. By `hequiv`, the restriction of
`A.valuation` to `K` is equivalent to `valuation K`.

* Steps 3a–3c give nontriviality of `A.valuation` (`hvA_nontrivial`), the bound
  `A.valuation x ≤ A.valuation (algebraMap K L c)` for `1 < A.valuation x`
  (`hbound`, from `Valuation.exists_pow_le_of_isAlgebraic`), and the archimedean bound
  `valuation K c ≤ valuation K d ^ M` for `1 < valuation K d` (`hKboundPos`, `hAanchorPos`, from
  the `MulArchimedean` value group of `hRK`).
* Step 3d (`hLtoK`) supplies the reverse bound — a `K`-element of valuation exceeding `1` dominated
  by a power of an arbitrary `y : L` — from `Valuation.exists_pow_eq_of_isAlgebraic`.
* Steps 3e–3f assemble these into `MulArchimedean A.ValueGroup` (`hMArchA`) and transfer it to
  `Nonempty (RankOne A.valuation)` via `nonempty_rankOne_iff_mulArchimedean`.
* Step 3g normalizes: the instance `hR` obtained above need not match `‖·‖` on `K`. Applying
  `Valuation.exists_rpow_eq_of_isEquiv` to the `ℝ≥0`-valued valuations obtained by pushing
  `A.valuation.restrict.comap (algebraMap K L)` along `hR.hom'` and `(valuation K).restrict` along
  `hRK.hom'` gives an exponent `t`; rescaling `hR.hom'` by `t` via `NNReal.rpow` produces the
  compatible instance `hR'`. -/
theorem exists_rankOne_compatible [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L) (hA : A.comap (algebraMap K L) = (valuation K).valuationSubring) :
    ∃ hR : RankOne A.valuation, ∀ x : K,
      (hR.hom' (A.valuation.restrict (algebraMap K L x)) : ℝ) = ‖x‖ := by
  -- **Step 1**: build the `Compatible`, norm-matching `RankOne (valuation K)` instance.
  haveI hvK_nontrivial : ValuativeRel.IsNontrivial K :=
    (ValuativeRel.isNontrivial_iff_isNontrivial (NormedField.valuation (K := K))).mpr inferInstance
  haveI hvK_rankLeOne : ValuativeRel.IsRankLeOne K :=
    ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean (NormedField.valuation (K := K))
  set eK : ValuativeRel.RankLeOneStruct K :=
    { emb := (RankOne.hom (NormedField.valuation (K := K))).comp
        (ValuativeRel.ValueGroupWithZero.orderMonoidIso
          (NormedField.valuation (K := K))).toMonoidWithZeroHom
      strictMono := (RankOne.strictMono (NormedField.valuation (K := K))).comp
        (ValuativeRel.ValueGroupWithZero.orderMonoidIso_strictMono
          (NormedField.valuation (K := K))) } with heK
  set hRK : RankOne (valuation K) := Valuation.RankOne.ofRankLeOneStruct eK with hRK_def
  have hRK_compat : ∀ x : K, (hRK.hom' ((valuation K).restrict x) : ℝ) = ‖x‖ := by
    intro x
    have hgoal : hRK.hom' ((valuation K).restrict x)
        = RankOne.hom (NormedField.valuation (K := K))
            ((NormedField.valuation (K := K)).restrict x) := by
      show (eK.emb.comp MonoidWithZeroHom.ValueGroup₀.embedding)
        ((valuation K).restrict x) = _
      rw [MonoidWithZeroHom.comp_apply, Valuation.embedding_restrict, heK]
      show (RankOne.hom (NormedField.valuation (K := K))).comp
        (ValuativeRel.ValueGroupWithZero.orderMonoidIso
          (NormedField.valuation (K := K))).toMonoidWithZeroHom (valuation K x) = _
      rw [MonoidWithZeroHom.comp_apply]
      congr 1
      show ValuativeRel.ValueGroupWithZero.orderMonoidIso
        (NormedField.valuation (K := K)) (valuation K x) = _
      rw [ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀,
        ← Valuation.restrict_def]
    rw [hgoal]
    have hfun : RankOne.hom (NormedField.valuation (K := K)) =
        MonoidWithZeroHom.ValueGroup₀.embedding
          (f := MonoidWithZeroHom.ofClass (NormedField.valuation (K := K))) := rfl
    rw [hfun, Valuation.embedding_restrict, NormedField.valuation_apply]
    rfl
  -- **Step 2**: relate `A.valuation` restricted to `K` to `valuation K` via the fact that two
  -- valuations on a field with the same valuation subring are equivalent
  -- (`Valuation.isEquiv_iff_valuationSubring`).
  have hw : (A.valuation.comap (algebraMap K L)).valuationSubring
      = (valuation K).valuationSubring := by
    rw [← hA]
    ext x
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply, ValuationSubring.mem_comap,
      ← A.valuation_le_one_iff]
  have hequiv : (A.valuation.comap (algebraMap K L)).IsEquiv (valuation K) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr hw
  -- **Step 3**: extend rank ≤ 1 (and the compatible normalization) from `valuation K` (via
  -- `hequiv`) to the whole of `A.valuation` on `L`.
  -- Step 3a: nontriviality of `A.valuation` (transferred from `valuation K` via `hequiv`).
  have hvK_nontrivial' : (valuation K).IsNontrivial := hRK.toIsNontrivial
  have hcomap_nontrivial : (A.valuation.comap (algebraMap K L)).IsNontrivial :=
    Valuation.isNontrivial_of_isEquiv hequiv.symm hvK_nontrivial'
  haveI hvA_nontrivial : A.valuation.IsNontrivial := by
    obtain ⟨r, hr0, hr1⟩ := hcomap_nontrivial.exists_val_nontrivial
    exact ⟨algebraMap K L r, by simpa [Valuation.comap_apply] using hr0,
      by simpa [Valuation.comap_apply] using hr1⟩
  -- Step 3b: one-directional bound -- every `x : L` with `1 < A.valuation x` is dominated by
  -- `A.valuation` of some nonzero `c : K`, via the minimal polynomial bound
  -- `Valuation.exists_pow_le_of_isAlgebraic` applied to `x` itself (using `1 < A.valuation x` to
  -- turn the exponentiated bound into a bound on `A.valuation x` itself, via `le_self_pow₀`).
  have hbound : ∀ x : L, x ≠ 0 → 1 < A.valuation x →
      ∃ c : K, c ≠ 0 ∧ A.valuation x ≤ A.valuation (algebraMap K L c) := by
    intro x hx hX
    obtain ⟨i, hi, hle⟩ :=
      Valuation.exists_pow_le_of_isAlgebraic A.valuation hx (Algebra.IsAlgebraic.isAlgebraic (R := K) x)
    set n := (minpoly K x).natDegree with hn
    have hpos : 0 < n - i := by omega
    refine ⟨(minpoly K x).coeff i, ?_, ?_⟩
    · rintro hc0
      rw [hc0, map_zero, map_zero] at hle
      have hxi0 : A.valuation x ^ (n - i) = 0 := le_antisymm hle zero_le
      rw [pow_eq_zero_iff hpos.ne'] at hxi0
      rw [hxi0] at hX
      exact absurd hX (by norm_num)
    · exact (le_self_pow₀ hX.le hpos.ne').trans hle
  -- Step 3c: any `c : K` is dominated by a power of any nontrivial `d : K`'s image (or its
  -- inverse), using `hRK`'s `MulArchimedean` value group directly (via `nonempty_rankOne_iff_
  -- mulArchimedean`) and pushing the resulting bound through `embedding`/`.restrict`.
  have hArchK : MulArchimedean (MonoidWithZeroHom.ValueGroup₀ (.ofClass (valuation K))) :=
    Valuation.nonempty_rankOne_iff_mulArchimedean.mp ⟨hRK⟩
  have hKbound : ∀ c d : K, d ≠ 0 → valuation K d ≠ 1 →
      ∃ M : ℕ, valuation K c ≤ valuation K d ^ M ∨ valuation K c ≤ (valuation K d)⁻¹ ^ M := by
    intro c d hd hd1
    set rc := (valuation K).restrict c with hrc
    set rd := (valuation K).restrict d with hrd
    have hrd0 : rd ≠ 0 := by
      simpa [hrd, Valuation.restrict_def, MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff]
        using (Valuation.ne_zero_iff (valuation K)).mpr hd
    have hrd1 : rd ≠ 1 := by
      simpa [hrd, Valuation.restrict_def, MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_one_iff]
        using hd1
    rcases lt_or_gt_of_ne hrd1 with hlt | hlt
    · have hlt' : 1 < rd⁻¹ := one_lt_inv₀ (zero_lt_iff.mpr hrd0) |>.mpr hlt
      obtain ⟨M, hM⟩ := hArchK.arch rc hlt'
      refine ⟨M, Or.inr ?_⟩
      have := (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
        (f := MonoidWithZeroHom.ofClass (valuation K))).monotone hM
      rwa [map_pow, map_inv₀, Valuation.embedding_restrict, Valuation.embedding_restrict] at this
    · obtain ⟨M, hM⟩ := hArchK.arch rc hlt
      refine ⟨M, Or.inl ?_⟩
      have := (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
        (f := MonoidWithZeroHom.ofClass (valuation K))).monotone hM
      rwa [map_pow, Valuation.embedding_restrict, Valuation.embedding_restrict] at this
  -- Step 3c': the direct (`d`'s image `> 1`, hence only the non-inverse branch is ever needed)
  -- specialization of `hKbound`, transferred across `hequiv` to `A.valuation`.
  have hKboundPos : ∀ c d : K, 1 < valuation K d →
      ∃ M : ℕ, valuation K c ≤ valuation K d ^ M := by
    intro c d hd1
    set rc := (valuation K).restrict c with hrc
    set rd := (valuation K).restrict d with hrd
    have hlt : 1 < rd := by
      have h := (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
        (f := MonoidWithZeroHom.ofClass (valuation K))).lt_iff_lt (a := 1) (b := rd)
      rw [map_one, Valuation.embedding_restrict] at h
      exact h.mp hd1
    obtain ⟨M, hM⟩ := hArchK.arch rc hlt
    refine ⟨M, ?_⟩
    have := (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
      (f := MonoidWithZeroHom.ofClass (valuation K))).monotone hM
    rwa [map_pow, Valuation.embedding_restrict, Valuation.embedding_restrict] at this
  have hAanchorPos : ∀ c d : K, 1 < A.valuation (algebraMap K L d) →
      ∃ M : ℕ, A.valuation (algebraMap K L c) ≤ A.valuation (algebraMap K L d) ^ M := by
    intro c d hd1
    have hd1K : 1 < valuation K d := by
      have h := hequiv.lt_iff_lt (x := (1 : K)) (y := d)
      rw [Valuation.comap_apply, Valuation.comap_apply, map_one] at h
      exact h.mp hd1
    obtain ⟨M, hM⟩ := hKboundPos c d hd1K
    refine ⟨M, ?_⟩
    have h := (hequiv.le_iff_le (x := c) (y := d ^ M)).mpr (by rwa [map_pow])
    rwa [Valuation.comap_apply, Valuation.comap_apply, map_pow, map_pow] at h
  -- Step 3d: the reverse of `hbound` -- a `K`-element of valuation exceeding `1` dominated by a
  -- power of an arbitrary `y : L`. `Valuation.exists_pow_eq_of_isAlgebraic` applied to `y` gives
  -- `m ≥ 1` and `d : K` with `A.valuation (algebraMap K L d) = A.valuation y ^ m` exactly; with
  -- `1 < A.valuation y` and `m ≥ 1` that value exceeds `1`.
  have hLtoK : ∀ y : L, y ≠ 0 → 1 < A.valuation y →
      ∃ (d : K) (N : ℕ), 1 < A.valuation (algebraMap K L d) ∧
        A.valuation (algebraMap K L d) ≤ A.valuation y ^ N := by
    intro y hy0 hy1
    obtain ⟨m, d, hm1, -, hd0, hdeq⟩ :=
      Valuation.exists_pow_eq_of_isAlgebraic A.valuation hy0 (Algebra.IsAlgebraic.isAlgebraic (R := K) y)
    refine ⟨d, m, ?_, hdeq.le⟩
    rw [hdeq]
    exact one_lt_pow₀ hy1 (by omega)
  -- Step 3e: assemble `MulArchimedean A.ValueGroup` from `hbound`, `hLtoK`, `hAanchorPos`.
  have hMArchA : MulArchimedean A.ValueGroup := by
    refine ⟨fun x {y} hy1 => ?_⟩
    by_cases hx1 : x ≤ 1
    · exact ⟨0, by simpa using hx1⟩
    rw [not_le] at hx1
    obtain ⟨p, hp⟩ := A.valuation_surjective x
    have hp0 : p ≠ 0 := by
      rintro rfl
      rw [map_zero] at hp
      exact absurd (hp ▸ hx1) (by simp)
    obtain ⟨c, hc0, hxc⟩ := hbound p hp0 (by rw [hp]; exact hx1)
    rw [hp] at hxc
    have hκ1 : 1 < A.valuation (algebraMap K L c) := hx1.trans_le hxc
    obtain ⟨q, hq⟩ := A.valuation_surjective y
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [map_zero] at hq
      exact absurd (hq ▸ hy1) (by simp)
    obtain ⟨d, N, hd1, hdy⟩ := hLtoK q hq0 (by rw [hq]; exact hy1)
    rw [hq] at hdy
    obtain ⟨M, hM⟩ := hAanchorPos c d hd1
    refine ⟨N * M, ?_⟩
    calc x ≤ A.valuation (algebraMap K L c) := hxc
      _ ≤ A.valuation (algebraMap K L d) ^ M := hM
      _ ≤ (y ^ N) ^ M := pow_le_pow_left₀ (zero_le) hdy M
      _ = y ^ (N * M) := (pow_mul y N M).symm
  -- Step 3f: transfer `MulArchimedean A.ValueGroup` to `MulArchimedean (ValueGroup₀ (.ofClass
  -- A.valuation))`, then obtain the `RankOne A.valuation` instance itself.
  have hMArchA' : MulArchimedean (MonoidWithZeroHom.ValueGroup₀ (.ofClass A.valuation)) :=
    MulArchimedean.comap
      (MonoidWithZeroHom.ValueGroup₀.embedding (f := MonoidWithZeroHom.ofClass A.valuation)).toMonoidHom
      (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (f := MonoidWithZeroHom.ofClass A.valuation))
  obtain ⟨hR⟩ := Valuation.nonempty_rankOne_iff_mulArchimedean.mpr hMArchA'
  -- Step 3g: the embedding of `hR` need not agree with `‖·‖` on `K`. Push
  -- `A.valuation.restrict.comap (algebraMap K L)` and `(valuation K).restrict` forward along
  -- `hR.hom'` and `hRK.hom'` into two equivalent `ℝ≥0`-valued valuations on `K`, relate them by a
  -- positive exponent `t` via `Valuation.exists_rpow_eq_of_isEquiv`, then rescale `hR.hom'` by `t`
  -- (`NNReal.rpow`) to obtain a `RankOne A.valuation` instance matching `‖·‖` on `K`.
  set v' : Valuation K (MonoidWithZeroHom.ValueGroup₀ (.ofClass A.valuation)) :=
    A.valuation.restrict.comap (algebraMap K L) with hv'_def
  set v1 : Valuation K ℝ≥0 := v'.map hR.hom' hR.strictMono'.monotone with hv1_def
  have hv1_equiv_v' : v1.IsEquiv v' :=
    Valuation.isEquiv_map_self_of_strictMono hR.hom' hR.strictMono'
  have hcomap_isEquiv_v' :
      (A.valuation.comap (algebraMap K L)).IsEquiv v' :=
    (Valuation.isEquiv_restrict (v := A.valuation)).comap (algebraMap K L)
  have hv'_nontrivial : v'.IsNontrivial :=
    Valuation.isNontrivial_of_isEquiv hcomap_isEquiv_v' hcomap_nontrivial
  have hv1_nontrivial : v1.IsNontrivial :=
    Valuation.isNontrivial_of_isEquiv hv1_equiv_v'.symm hv'_nontrivial
  set v2 : Valuation K ℝ≥0 := (valuation K).restrict.map hRK.hom' hRK.strictMono'.monotone
    with hv2_def
  have hv2_apply : ∀ x : K, (v2 x : ℝ) = ‖x‖ := hRK_compat
  have hv2_equiv_restrict : v2.IsEquiv (valuation K).restrict :=
    Valuation.isEquiv_map_self_of_strictMono hRK.hom' hRK.strictMono'
  have hv2_isEquiv_valK : v2.IsEquiv (valuation K) :=
    hv2_equiv_restrict.trans (Valuation.isEquiv_restrict (v := valuation K)).symm
  have hv1_isEquiv_v2 : v1.IsEquiv v2 :=
    (hv1_equiv_v'.trans hcomap_isEquiv_v'.symm).trans (hequiv.trans hv2_isEquiv_valK.symm)
  obtain ⟨t, ht_pos, ht⟩ := Valuation.exists_rpow_eq_of_isEquiv v1 v2 hv1_isEquiv_v2
  -- Rescale `hR.hom'` by `t` to match `v2` (i.e. `‖·‖`) exactly.
  let hom2 : MonoidWithZeroHom.ValueGroup₀ (.ofClass A.valuation) →*₀ ℝ≥0 :=
    { toFun := fun γ => hR.hom' γ ^ t
      map_zero' := by simp [NNReal.zero_rpow ht_pos.ne']
      map_one' := by simp
      map_mul' := fun a b => by simp [NNReal.mul_rpow] }
  have hom2_strictMono : StrictMono hom2 := by
    intro a b hab
    exact NNReal.rpow_lt_rpow (hR.strictMono' hab) ht_pos
  let hR' : Valuation.RankOne A.valuation :=
    { hvA_nontrivial with hom' := hom2, strictMono' := hom2_strictMono }
  refine ⟨hR', fun x => ?_⟩
  show (hom2 (A.valuation.restrict (algebraMap K L x)) : ℝ) = ‖x‖
  have : hom2 (A.valuation.restrict (algebraMap K L x)) = v1 x ^ t := rfl
  rw [this, ← ht x]
  exact hv2_apply x

/-- A `ValuationSubring A` of an algebraic extension `L / K` with
`A.comap (algebraMap K L) = 𝒪[K]` is the closed unit ball of an absolute value on `L` extending
`‖·‖` on `K`.

The rank-1 structure on `A.valuation` compatible with `‖·‖` comes from
`exists_rankOne_compatible`; the remainder transports the `Valued`/`RankOne` data into a
`NontriviallyNormedField L` via `Valued.mk'` and `Valued.toNontriviallyNormedField` and takes the
associated `AbsoluteValue`. -/
theorem exists_rankOne_absoluteValue_extends [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L) (hA : A.comap (algebraMap K L) = (valuation K).valuationSubring) :
    ∃ f : AbsoluteValue L ℝ, (∀ x : K, f (algebraMap K L x) = ‖x‖) ∧ ∀ x : L, f x ≤ 1 ↔ x ∈ A := by
  obtain ⟨hR, hcompat⟩ := exists_rankOne_compatible K A hA
  letI := hR
  letI : Valued L A.ValueGroup := Valued.mk' A.valuation
  letI : NontriviallyNormedField L := Valued.toNontriviallyNormedField L A.ValueGroup
  refine ⟨NormedField.toAbsoluteValue L, fun x => ?_, fun x => ?_⟩
  · show ‖algebraMap K L x‖ = ‖x‖
    rw [← hcompat x]
    rfl
  · show ‖x‖ ≤ 1 ↔ x ∈ A
    rw [Valued.toNormedField.norm_le_one_iff]
    exact A.valuation_le_one_iff x

/-- **Completeness transport across the `Valued`/`spectralNorm` diamond.** For `A : ValuationSubring
L` with `A.comap (algebraMap K L) = 𝒪[K]`, `K` complete, and `L / K` finite, `L` is complete with
respect to the uniform space determined by `A.valuation` via `Valued.mk'` — the same canonical
uniform structure `exists_rankOne_absoluteValue_extends` and this file's other theorems build via
`Valued.mk'` + `Valued.toNontriviallyNormedField`.

**Design choice (shape (a) from the task, not (b)):** the conclusion is stated as `CompleteSpace L`
relative to the explicit `UniformSpace` term `(Valued.mk' A.valuation).toUniformSpace`, not relative
to an ambient `[Valued L A.ValueGroup]`/`[RankOne A.valuation]` instance argument. This is possible
(and preferable to threading those as hypotheses) because `Valued.mk' A.valuation` needs no
`RankOne` instance to determine `L`'s uniform structure — `RankOne` is only needed internally, to
build the *normed*-field structure used to compare against `spectralNorm`, not to state the
conclusion. A caller that has already done `letI := Valued.mk' A.valuation` (mirroring
`exists_rankOne_absoluteValue_extends`'s own downstream usage pattern) gets `CompleteSpace L`
immediately by `haveI := exists_completeSpace_of_finiteDimensional K A hA`, with no further `letI`
chain to repeat.

**Why this needs `Langlands.HenselianValuation`'s new `UniformSpaceTransport` lemmas and not just
`spectralNorm.completeSpace` directly**: `Mathlib`'s general "finite extension of a complete
nonarchimedean field is complete" theorem, `spectralNorm.completeSpace`, is pinned to
`spectralNorm.uniformSpace K L` — a uniform structure built from the abstract sup-over-embeddings
spectral norm, a *different, non-defeq* construction from `Valued.mk' A.valuation`'s (built from the
concrete `A.valuation`/`RankOne` data), even though both norms agree pointwise. Composing them
requires the `PseudoMetricSpace.ext`-based transport
(`CompleteSpace.of_pseudoMetricSpace_toDist_eq`, `UniformSpaceTransport` section above), applied to
the pointwise norm equality supplied by `spectralNorm_unique_field_norm_ext` (using the same
absolute value `exists_rankOne_absoluteValue_extends` builds, here inlined via the same `hR` from
`exists_rankOne_compatible` so the two constructions provably agree rather than merely being
propositionally equal witnesses of separate existentials). -/
theorem exists_completeSpace_of_finiteDimensional [CompleteSpace K] [Algebra.IsAlgebraic K L]
    [FiniteDimensional K L] (A : ValuationSubring L)
    (hA : A.comap (algebraMap K L) = (valuation K).valuationSubring) :
    @CompleteSpace L (Valued.mk' A.valuation).toUniformSpace := by
  obtain ⟨hR, hcompat⟩ := exists_rankOne_compatible K A hA
  letI := hR
  letI : Valued L A.ValueGroup := Valued.mk' A.valuation
  letI hnfValued : NontriviallyNormedField L := Valued.toNontriviallyNormedField L A.ValueGroup
  letI hnfSpectral : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField K L
  -- `‖·‖` notation is ambiguous with both `hnfValued`/`hnfSpectral` in scope (it resolves to
  -- whichever instance typeclass search prefers, not necessarily `hnfValued`), so every `L`-typed
  -- norm/dist below is pinned explicitly to `hnfValued` rather than written via bare `‖·‖`/`dist`.
  have hfK : ∀ x : K, (@norm L hnfValued.toNorm) (algebraMap K L x) = ‖x‖ := fun x => by
    rw [← hcompat x]; rfl
  have hfK' : ∀ x : K, (@NormedField.toAbsoluteValue L hnfValued.toNormedField)
      (algebraMap K L x) = ‖x‖ := hfK
  have hnorm_eq : ∀ y : L, (@norm L hnfValued.toNorm) y = spectralNorm K L y := fun y =>
    spectralNorm_unique_field_norm_ext hfK' y
  have hdist_eq : hnfValued.toDist = hnfSpectral.toDist :=
    Dist.ext (funext fun x => funext fun y => hnorm_eq (x - y))
  exact CompleteSpace.of_pseudoMetricSpace_toDist_eq hdist_eq (spectralNorm.completeSpace K L)

/-- A nonunit `π ≠ 0` of a `ValuationSubring A` of `L` extending `𝒪[K]` (i.e. `A.comap
(algebraMap K L) = 𝒪[K]`) has `spectralNorm K L π < 1`, provided `K` is complete.

This is gap 1 of `Langlands.TotallyRamifiedEisenstein`'s Eisenstein-ness-from-uniformizer route:
connecting a concrete uniformizer of a `ValuationSubring` to the abstract `spectralNorm` hypothesis
`spectralNorm_coeff_lt_one` needs. The absolute value `f` supplied by
`exists_rankOne_absoluteValue_extends` agrees with `spectralNorm K L` everywhere by
`spectralNorm_unique_field_norm_ext` (using `[CompleteSpace K]`), so it suffices to show `f π < 1`.
Since `π` is a nonunit, `π⁻¹ ∉ A` (`ValuationSubring.mem_nonunits_iff_or`), hence `f π⁻¹ > 1` by the
`≤ 1 ↔ ∈ A` characterization from `exists_rankOne_absoluteValue_extends`; since `f` is
multiplicative and `f π⁻¹ = (f π)⁻¹` (`map_inv₀`), `f π = (f π⁻¹)⁻¹ < 1`. -/
theorem spectralNorm_lt_one_of_mem_nonunits [Algebra.IsAlgebraic K L] [CompleteSpace K]
    {A : ValuationSubring L} (hA : A.comap (algebraMap K L) = (valuation K).valuationSubring)
    {π : L} (hπ : π ∈ A.nonunits) (hπ0 : π ≠ 0) :
    spectralNorm K L π < 1 := by
  obtain ⟨f, hfK, hfA⟩ := exists_rankOne_absoluteValue_extends K A hA
  rw [← spectralNorm_unique_field_norm_ext hfK π]
  have hinv_notmem : π⁻¹ ∉ A := (A.mem_nonunits_iff_or.mp hπ).resolve_left hπ0
  have hf_inv_gt : 1 < f π⁻¹ := lt_of_not_ge (fun h => hinv_notmem ((hfA π⁻¹).mp h))
  have h2 : (f π⁻¹)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hf_inv_gt
  rwa [map_inv₀, inv_inv] at h2

/-- Uniqueness of the extension of a complete nonarchimedean valuation to an algebraic extension:
if `K` is complete with respect to a nontrivial nonarchimedean norm and `L / K` is algebraic, any
two `ValuationSubring`s of `L` restricting to `𝒪[K]` coincide.

This is what makes the decomposition subgroup of a Henselian (in particular complete) valued
field's valuation ring extension the whole Galois group. Proved from
`spectralNorm_unique_field_norm_ext`, the unique norm extension theorem, applied to the absolute
values supplied by `exists_rankOne_absoluteValue_extends`. -/
theorem valuationSubring_eq_of_comap_eq [Algebra.IsAlgebraic K L] [CompleteSpace K]
    {A B : ValuationSubring L}
    (hA : A.comap (algebraMap K L) = (valuation K).valuationSubring)
    (hB : B.comap (algebraMap K L) = (valuation K).valuationSubring) :
    A = B := by
  obtain ⟨f, hfK, hfA⟩ := exists_rankOne_absoluteValue_extends K A hA
  obtain ⟨g, hgK, hgB⟩ := exists_rankOne_absoluteValue_extends K B hB
  refine ValuationSubring.ext _ _ fun x => ?_
  rw [← hfA, ← hgB, spectralNorm_unique_field_norm_ext hfK x,
    spectralNorm_unique_field_norm_ext hgK x]

/-- `valuationSubring_eq_of_comap_eq` for a nonarchimedean local field `K`, taking
`IsNonarchimedeanLocalField K` in place of the
`NontriviallyNormedField`/`IsUltrametricDist`/`ValuativeRel`/`Compatible`/`CompleteSpace` bundle.

The `NormedField`/`Valued`/`RankOne`/`CompleteSpace` instance chain is constructed here once. Since
`L` is a free type variable, this applies to any `L` algebraic over `K`: both
`L = AlgebraicClosure K`, as used by `LocalField.decompositionSubgroup_eq_top`
(`Langlands.WeilGroup`), and a finite subextension `K(x) ⊆ L`, as used by
`ValuationSubring.exists_restrictNormalHom_decompositionSubgroup_surjective`
(`Langlands.UnramifiedExtension`). -/
theorem valuationSubring_eq_of_comap_eq_of_isNonarchimedeanLocalField
    {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    {A B : ValuationSubring L}
    (hA : A.comap (algebraMap K L) = (valuation K).valuationSubring)
    (hB : B.comap (algebraMap K L) = (valuation K).valuationSubring) :
    A = B := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : IsUltrametricDist K := inferInstance
  haveI : CompleteSpace K := inferInstance
  -- The `NontriviallyNormedField K` structure above is built from `Valued.v = valuation K`, so its
  -- `NormedField.valuation` agrees with `Valued.v` definitionally, giving the `Compatible`
  -- instance `valuationSubring_eq_of_comap_eq` requires.
  have hnorm : ∀ x : K, (NormedField.valuation x : NNReal)
      = RankOne.hom (Valued.v (R := K)) ((Valued.v (R := K)).restrict x) := fun x =>
    congrFun (Valued.coe_valuation_eq_rankOne_hom_comp_valuation K (ValueGroupWithZero K)) x
  haveI : (NormedField.valuation (K := K)).Compatible :=
    NormedField.valuation_compatible_of_eq_rankOne_hom_comp_restrict (Valued.v (R := K)) hnorm
  exact valuationSubring_eq_of_comap_eq K hA hB

end NormedFieldBridge

end LocalField

section ComapSmul

open scoped Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The comap of a `σ`-translate of a valuation subring of `L` (for `σ : L ≃ₐ[K] L`) along
`algebraMap K L` does not depend on `σ`: automorphisms of `L` over `K` fix `K` pointwise, so
`σ • A` restricts to the same subring of `K` that `A` does. -/
theorem ValuationSubring.comap_smul_eq (σ : L ≃ₐ[K] L) (A : ValuationSubring L) :
    (σ • A).comap (algebraMap K L) = A.comap (algebraMap K L) := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    show σ⁻¹ (algebraMap K L x) = algebraMap K L x from σ⁻¹.commutes x]

end ComapSmul
