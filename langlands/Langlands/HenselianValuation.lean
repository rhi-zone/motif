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
# Bridging `ValuationSubring` and `NormedField`, and uniqueness of valuation extension

This file bridges the `ValuationSubring`/`ValuativeRel` formalism (used for
`IsNonarchimedeanLocalField`) with the `NormedField`/`AbsoluteValue` formalism (used by
`Mathlib.Analysis.Normed.Unbundled.SpectralNorm`), in order to prove: for `K` a complete
nonarchimedean local field and `L / K` algebraic, a `ValuationSubring` of `L` whose comap along
`algebraMap K L` is `𝒪[K]` is *unique*. Combined with the fact that `K`-automorphisms of `L`
preserve this comap condition (`ValuationSubring.comap_smul_eq`), this gives that the
decomposition subgroup of any such extension is all of `Gal(L/K)`.

## Main definitions/results

* `LocalField.exists_rankOne_compatible` : given a `ValuationSubring A` of `L` extending `𝒪[K]`
  (in the sense `A.comap (algebraMap K L) = 𝒪[K]`), there is a `RankOne A.valuation` instance
  whose associated embedding `A.ValueGroup → ℝ≥0`, pulled back along
  `A.valuation.restrict ∘ algebraMap K L`, reproduces `‖·‖` on `K`. This packages the two
  genuinely deep facts described in the docstring below and is now **fully proved, with no
  `sorry`**: the former `hLtoK` gap (a reverse-direction minimal-polynomial estimate not derivable
  from `Valuation.exists_pow_le_of_isAlgebraic` alone) is closed by
  `Valuation.exists_pow_eq_of_isAlgebraic`; the compatible-normalization gap (Step 3g) is closed by
  `Valuation.exists_rpow_eq_of_isEquiv`, a from-scratch proof of Hölder's uniqueness theorem for
  archimedean linearly ordered groups, specialized to `ℝ≥0`-valued valuations (see that lemma's
  docstring for the argument; it is not otherwise in Mathlib, which only has the *existence* half,
  `Archimedean.exists_orderAddMonoidHom_real_injective`).
* `LocalField.exists_rankOne_absoluteValue_extends` : given the same hypotheses, there is an
  `AbsoluteValue L ℝ` extending the norm on `K` (from a fixed rank-1 embedding for `K`) whose
  closed unit ball is `A`. This is the purely formal consequence of
  `exists_rankOne_compatible` described in the implementation notes below; it has no `sorry` of
  its own.
* `LocalField.valuationSubring_eq_of_comap_eq` : uniqueness of the valuation subring extension,
  via `spectralNorm_unique_field_norm_ext` (the "unique norm extension theorem" for complete
  nonarchimedean fields) applied to the absolute values produced by the above.
* `ValuationSubring.comap_smul_eq` : the comap of a `G`-translate of a valuation subring (for
  `G = L ≃ₐ[K] L`) along `algebraMap K L` does not depend on the translate, since automorphisms
  in `G` fix `K` pointwise. A purely formal fact, no `sorry`.

## Implementation notes

`exists_rankOne_compatible` packages together two facts, both now fully proved:

1. **Rank preservation under algebraic extension**: if `K` has a rank-≤-1 (i.e. real-valued)
   valuation and `L / K` is algebraic, then any valuation subring `A` of `L` restricting to
   `𝒪[K]` is again of rank ≤ 1, i.e. `A.valuation` (valued in the abstract group `A.ValueGroup`)
   admits an order-embedding into `ℝ≥0`. This is a standard fact (e.g. Bourbaki, *Commutative
   Algebra*, VI §10, or Engler-Prestel, *Valued Fields*), not yet in Mathlib. Equivalently (given
   nontriviality, which transfers from `𝒪[K]` via the comap hypothesis), by
   `Valuation.nonempty_rankOne_iff_mulArchimedean` this is the statement that
   `MonoidWithZeroHom.ValueGroup₀ (.ofClass A.valuation)` is `MulArchimedean`.
2. **Compatible normalization**: moreover the embedding `A.ValueGroup → ℝ≥0` can be chosen so
   that it agrees with the fixed embedding used to build the `NormedField K` structure on `K`
   (i.e. so that the extended norm genuinely restricts to `‖·‖` on `K`, not just something
   equivalent to it).

Once these are granted (i.e. once `exists_rankOne_compatible` is discharged), the rest is formal
— this is exactly what `exists_rankOne_absoluteValue_extends` carries out: build
`Valued L A.ValueGroup` via `Valued.mk'` (which needs no ambient topology on `L`), transport the
resulting `RankOne A.valuation` instance into a `NontriviallyNormedField L` via
`Valued.toNontriviallyNormedField`, and take `f := NormedField.toAbsoluteValue L`; then
`f x ≤ 1 ↔ x ∈ A` is `Valued.toNormedField.norm_le_one_iff` composed with
`ValuationSubring.valuation_le_one_iff`.

## A genuine gap found while attempting `exists_rankOne_compatible`

Two reusable pieces of infrastructure for the "rank preservation under algebraic extension"
argument are proved below with no `sorry`:

* `MulArchimedean.of_units`: for `Γ₀` a `LinearOrderedCommGroupWithZero`, `MulArchimedean Γ₀ˣ`
  transfers to `MulArchimedean Γ₀` (via the order isomorphism `WithZero Γ₀ˣ ≃*o Γ₀`, i.e.
  `WithZero.withZeroUnitsEquiv`, and `MulArchimedean.comap` along its inverse).
* `Valuation.exists_pow_le_of_isAlgebraic`: the "ultrametric inequality applied to the minimal
  polynomial" bound — for `v : Valuation L Γ₀` and `x : L` algebraic over `K` with `x ≠ 0`, some
  coefficient `i < (minpoly K x).natDegree` of the minimal polynomial satisfies
  `v x ^ (natDegree - i) ≤ v (algebraMap K L (coeff i))`. This is the key tool that bounds `v x`
  above by a power of a `K`-value, for *any* `x : L` and *any* valuation `v` on `L` — it does not
  need `L` finite over `K`, only algebraicity, and it needs no compatibility hypothesis between
  `K`'s norm and its `ValuativeRel` structure.

However, **`exists_rankOne_compatible`, as stated, is not provable from its current hypotheses**,
and this was confirmed with a concrete counterexample rather than left as an unverified
suspicion. The issue: `[NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]` are
three *independent* typeclass parameters with no built-in link between them — nothing forces
`ValuativeRel.valuation K` to be equivalent to (or even nontrivial relative to) the norm `‖·‖`.
Concretely: instantiate `ValuativeRel K := ValuativeRel.ofValuation (1 : Valuation K ℝ≥0)` (the
*trivial* valuation, whose `valuationSubring` is all of `K`) alongside any nontrivially normed
ultrametric `K`. Then take `A := (⊤ : ValuationSubring L)`. Since `(⊤ : ValuationSubring L).comap
(algebraMap K L) = ⊤ = (1 : Valuation K ℝ≥0).valuationSubring`, the hypothesis `hA` holds. But
`A.valuation` (`⊤`'s own valuation) is the *trivial* valuation on `L` — it has no `IsNontrivial`
instance, hence no `RankOne` instance can possibly exist for it, directly contradicting the `∃ hR
: RankOne A.valuation, …` conclusion. (`nix develop --command lake env lean` on a standalone file
confirms `example : ValuativeRel.IsRankLeOne K` — let alone any norm-compatibility fact — is *not*
derivable from `[NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]` alone; no
instance bridges them.)

This was fixed by strengthening the hypotheses of `exists_rankOne_compatible`, adding
`[(NormedField.valuation (K := K)).Compatible]` (see the `## Fix` section on the theorem itself)
to tie `valuation K` to the norm via `Valuation.Compatible` from
`Mathlib.RingTheory.Valuation.ValuativeRel.Basic`. With the signature corrected,
`exists_rankOne_compatible` is now **fully proved**: fact #1 (rank preservation) uses the two
lemmas above plus `Valuation.exists_pow_eq_of_isAlgebraic`; fact #2 (compatible normalization)
uses `Valuation.exists_rpow_eq_of_isEquiv` (Hölder uniqueness for `ℝ≥0`-valued valuations, proved
from scratch below) to rescale the rank-≤-1 embedding obtained for fact #1 so it matches `‖·‖`
on `K` exactly.
-/

noncomputable section

open ValuativeRel Valuation IsLocalRing
open scoped NNReal

section ReusableInfrastructure

/-- **General archimedean transfer for groups with zero.** If the units `Γ₀ˣ` of a linearly
ordered commutative group with zero are `MulArchimedean`, so is `Γ₀` itself. Proved via the order
isomorphism `WithZero Γ₀ˣ ≃*o Γ₀` (`WithZero.withZeroUnitsEquiv`): `MulArchimedean` transfers to
`WithZero Γ₀ˣ` from `Γ₀ˣ` (`WithZero.instMulArchimedean`), then pulls back along the (strictly
monotone) inverse of that isomorphism via `MulArchimedean.comap`. -/
theorem MulArchimedean.of_units {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (h : MulArchimedean Γ₀ˣ) : MulArchimedean Γ₀ := by
  classical
  have hwz : MulArchimedean (WithZero Γ₀ˣ) := WithZero.instMulArchimedean Γ₀ˣ
  exact MulArchimedean.comap (WithZero.withZeroUnitsEquiv (G := Γ₀)).symm.toMonoidHom
    WithZero.withZeroUnitsEquiv_symm_strictMono

/-- **Ultrametric bound via the minimal polynomial.** If `v` is a valuation on `L` and `x : L` is
algebraic (and nonzero) over a subfield `K`, then applying the ultrametric inequality to the
equation `(minpoly K x).aeval x = 0` (rearranged as `x ^ n = -∑_{i < n} c_i x ^ i` for `n` the
degree and `c_i` the coefficients) shows the maximum term on the right dominates, giving some
`i < n` with `v x ^ (n - i) ≤ v (algebraMap K L (c_i))`. This is the key tool bounding `v x` above
by a power of a `K`-value: it needs only algebraicity (not finiteness) of `x` over `K`, and no
compatibility between valuations on `K` and `L` beyond `v` itself. -/
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

/-- **Exact archimedean bound via the minimal polynomial (reverse direction).** If `v` is a
valuation on `L` and `x : L` is algebraic (and nonzero) over a subfield `K`, then some power
`x ^ m` (with `1 ≤ m ≤ (minpoly K x).natDegree`) has *exactly* the same `v`-valuation as
`algebraMap K L c` for some nonzero `c : K`. Combined with `exists_pow_le_of_isAlgebraic` (which
only bounds `v x` from *above* by a `K`-value), this supplies the missing reverse-direction bound:
since the equality is exact, `1 < v x` forces `1 < v (algebraMap K L c) = v x ^ m`, i.e. some
`K`-anchor exceeding `1` is *dominated* by a power of `x`, not just dominating one -- this is
exactly what `Bourbaki, *Comm. Alg.* VI §10.1` / `Engler-Prestel, *Valued Fields* Thm. 3.2.4` use
(via the reversed-minimal-polynomial relationship) to show rank ≤ 1 is preserved under algebraic
extension; this lemma reaches the same conclusion directly, without introducing `Polynomial.
reverse` or the minimal polynomial of `x⁻¹` as separate infrastructure.

Proof idea: the minimal polynomial relation `∑_{i=0}^n c_i x^i = 0` (`c_n = 1`, monic) expresses
`0` as a sum of `n+1` terms `t_i := algebraMap K L c_i * x ^ i`. If the valuations `v (t_i)` were
pairwise distinct among the terms with nonzero coefficient, the (unique) maximal term would
dominate the whole sum (`Valuation.map_sum_eq_of_lt`), forcing `v 0 = v (t_j) ≠ 0`, absurd. So two
distinct indices `i ≠ j` (both with nonzero coefficient) must tie in valuation:
`v (algebraMap c_i) * v x ^ i = v (algebraMap c_j) * v x ^ j`; canceling the smaller power of `v x`
(nonzero, since `x ≠ 0`) and setting `m := max i j - min i j`, `c :=` the corresponding ratio of
coefficients gives `v (algebraMap c) = v x ^ m` exactly. -/
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

/-- **Hölder's uniqueness theorem for archimedean groups, specialized to `ℝ≥0`-valued
valuations.** If `v₁ v₂ : Valuation K ℝ≥0` are equivalent (`v₁.IsEquiv v₂`, i.e. they induce the
same preorder/valuation subring on `K`) and `v₁` is nontrivial, then `v₂` equals `v₁` raised to a
fixed positive real power: `∃ t > 0, ∀ x, v₂ x = v₁ x ^ t`. This is the archimedean-linearly-ordered-
group uniqueness fact (any two strictly monotone embeddings of such a group into `ℝ` agree up to a
positive real scalar) specialized to the case where both embeddings already land directly in `ℝ≥0`:
this sidesteps needing `MulArchimedean`/`ValueGroup₀` machinery as a separate hypothesis, since any
subgroup of `(ℝ, +)` (reached here via `Real.log`) is automatically archimedean, being a subgroup of
an archimedean group. Not currently in Mathlib in any form (only the *existence* half,
`Archimedean.exists_orderAddMonoidHom_real_injective` in `Mathlib.Data.Real.Embedding`, is present).
The proof is the classical density argument: pick an anchor `c₀` with `v₁ c₀ > 1` (so `v₂ c₀ > 1`
too, via `hequiv`), then show `Real.log (v₁ x) / Real.log (v₁ c₀) = Real.log (v₂ x) / Real.log
(v₂ c₀)` for every `x` by comparing against every rational `p / n` via the valuation identity
`v c₀ ^ p < v x ^ n ↔ v (c₀ ^ p / x ^ n) < 1`, which -- being purely an order-comparison against `1`
-- transfers across `hequiv` unchanged; density of `ℚ` in `ℝ` then forces the two ratios to agree
exactly, not just up to rational approximation. -/
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

section NormedFieldValuativeRelBridge

/-- **Bridging lemma, closing the gap documented above.** If the norm on `K` literally equals
`hv.hom ∘ v.restrict` for some `Compatible`, `RankOne` valuation `v` on `K` -- which is exactly
what happens whenever the `NormedField`/`Valued` structure on `K` is *built from* `v` (e.g. via
`Valued.toNormedField`/`Valued.toNontriviallyNormedField`, using
`Valued.toNormedField.coe_valuation_eq_rankOne_hom_comp_valuation` to see the hypothesis `hnorm`
holds by `rfl` in that case) -- then the norm's own canonical valuation `NormedField.valuation` is
again `Compatible` with the ambient `ValuativeRel K`. This is precisely the extra hypothesis added
to `LocalField.exists_rankOne_compatible` below to rule out instantiating a `ValuativeRel K`
independent of (in particular, trivial relative to) the norm. -/
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

/-- **Fixed statement** (see the module docstring for the counterexample this repairs, and the
`## Fix` section below for what changed and why): a `ValuationSubring A` of an algebraic extension
`L` of `K` with `A.comap (algebraMap K L) = 𝒪[K]` admits a `RankOne` structure on `A.valuation`
(i.e. `A` has rank ≤ 1, and is nontrivial since `𝒪[K]` is) whose associated embedding
`A.ValueGroup → ℝ≥0` is normalized to agree with the fixed `NontriviallyNormedField` structure on
`K`: pulling the resulting embedding back along `A.valuation.restrict ∘ algebraMap K L` reproduces
`‖·‖` on `K`.

This packages the two facts described in the module docstring:
1. rank preservation of a rank-≤-1 valuation under an algebraic extension (equivalently, that
   `MonoidWithZeroHom.ValueGroup₀ (.ofClass A.valuation)` is `MulArchimedean`; see
   `Valuation.nonempty_rankOne_iff_mulArchimedean`), and
2. that the resulting embedding into `ℝ≥0` can be normalized to match the one already fixed on
   `K`, not just something equivalent to it.

## Fix

The extra hypothesis `[(NormedField.valuation (K := K)).Compatible]` (added to the
`NormedFieldBridge` section variables) ties `valuation K` to `‖·‖`: it is the `Valuation.Compatible`
class from `Mathlib.RingTheory.Valuation.ValuativeRel.Basic`, saying `x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖`. This
rules out the counterexample from the module docstring: with `ValuativeRel K := .ofValuation
(1 : Valuation K ℝ≥0)` (trivial), `x ≤ᵥ y` holds unconditionally (for `x ≠ 0`), so `Compatible`
would force `‖x‖ ≤ ‖y‖` for *all* `x ≠ 0, y`, contradicting nontriviality of `‖·‖`. Concretely, this
hypothesis is what's needed to derive `ValuativeRel.IsNontrivial K` and `ValuativeRel.IsRankLeOne K`
(hence a `RankOne (valuation K)` instance, built explicitly below with `hom'` matching `‖·‖`
on the nose, not just up to equivalence -- see `hRK_compat`), which is fact #1 + fact #2 restricted
to the base field `K` itself (i.e. the case `L = K`, `A = 𝒪[K]`).

Extending this rank-≤-1-ness from `K` to all of `L`: via `hequiv` below, the K-restriction of
`A.valuation` is equivalent to `valuation K`, hence itself rank ≤ 1 with matching normalization;
`A.valuation` on the whole of `L` is bridged to this via the "rank preservation under algebraic
extension" argument. The proof below carries this out as far as it goes:

* Steps 3a-3c build the reusable one-directional pieces: nontriviality of `A.valuation`
  (`hvA_nontrivial`), the bound `A.valuation x ≤ A.valuation (algebraMap c)` for `x` with
  `1 < A.valuation x` (`hbound`, via `Valuation.exists_pow_le_of_isAlgebraic`), and the
  `K`-internal archimedean bound `valuation K c ≤ (valuation K d) ^ M` for any `c` and any `d`
  with `1 < valuation K d` (`hKboundPos`/`hAanchorPos`, via `hRK`'s `MulArchimedean` value group
  and `nonempty_rankOne_iff_mulArchimedean`).
* Step 3d (`hLtoK`) was the reverse-direction bound (some `K`-anchor dominated *by* a power of an
  arbitrary `y : L`, not the other way round) -- not obtainable from
  `Valuation.exists_pow_le_of_isAlgebraic` by any combination of applications to `y`, `y⁻¹`, or
  auxiliary elements. **This gap is now closed** by `Valuation.exists_pow_eq_of_isAlgebraic`
  (proved in `ReusableInfrastructure` above): rather than going through the explicit
  reversed-minimal-polynomial relationship between `minpoly K y` and `minpoly K y⁻¹` (the route
  Bourbaki, *Comm. Alg.* VI §10.1 / Engler-Prestel, *Valued Fields* Thm. 3.2.4 take), it directly
  extracts an *exact* equality `v (algebraMap K L c) = v y ^ m` from a tie between two terms of
  the minimal-polynomial sum (forced by `Valuation.map_sum_eq_of_lt`, since no term can uniquely
  dominate a sum that equals `0`).
* Steps 3e-3f assemble `hbound`, `hLtoK`, and `hAanchorPos` into `MulArchimedean A.ValueGroup`
  directly (`hMArchA`, via the `MulArchimedean` class's `arch` field) and transfer this to obtain
  `Nonempty (RankOne A.valuation)` (`hR`) via `nonempty_rankOne_iff_mulArchimedean` -- i.e. rank
  ≤ 1 of `A.valuation` is now **fully proved**, with no remaining `sorry`.
* Step 3g fixes the normalization: `hR` is *some* `RankOne` instance, not necessarily the one
  matching `‖·‖` on `K`. This needs Hölder's uniqueness theorem for archimedean linearly ordered
  groups (any two strictly monotone monoid homs into `ℝ≥0` agree up to a positive real power) --
  not in Mathlib, so it is proved from scratch here as `Valuation.exists_rpow_eq_of_isEquiv`
  (specialized to the case where both homs already land in `ℝ≥0`, which sidesteps needing
  `MulArchimedean`/`ValueGroup₀` as a separate hypothesis). Applying it to the two `ℝ≥0`-valued
  valuations obtained by pushing `A.valuation.restrict.comap (algebraMap K L)` forward along
  `hR.hom'` and `(valuation K).restrict` forward along `hRK.hom'` gives an exponent `t`; rescaling
  `hR.hom'` by `t` (via `NNReal.rpow`) produces the compatible `RankOne` instance `hR'`.

With Step 3g closed, `exists_rankOne_compatible` has **no remaining `sorry`**. -/
theorem exists_rankOne_compatible [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L) (hA : A.comap (algebraMap K L) = (valuation K).valuationSubring) :
    ∃ hR : RankOne A.valuation, ∀ x : K,
      (hR.hom' (A.valuation.restrict (algebraMap K L x)) : ℝ) = ‖x‖ := by
  -- **Step 1**: build the `Compatible`, norm-matching `RankOne (valuation K)` instance from the
  -- new hypothesis.
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
  -- **Step 3d.** `hbound` above (via `Valuation.exists_pow_le_of_isAlgebraic`) only ever bounds a
  -- power of an element `x : L` *above* by a `K`-value. The reverse bound needed here -- some
  -- `K`-anchor exceeding `1` *dominated* by a power of `y` -- is now supplied directly by
  -- `Valuation.exists_pow_eq_of_isAlgebraic` (proved above in `ReusableInfrastructure`): applied
  -- to `y`, it gives `m ≥ 1` and `d : K` (both from ties in the minimal-polynomial-term
  -- valuations, per that lemma's docstring) with `A.valuation (algebraMap K L d) = A.valuation y
  -- ^ m` *exactly*. Since `1 < A.valuation y` and `m ≥ 1`, this anchor is automatically `> 1`.
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
  -- **Step 3g.** `hR` is *some* `RankOne A.valuation` instance (Steps 3a-3f establish its
  -- existence unconditionally), but its embedding need not agree with `‖·‖` on `K`. Fix this by
  -- pushing `A.valuation.restrict.comap (algebraMap K L)` and `(valuation K).restrict` forward
  -- along `hR.hom'`/`hRK.hom'` respectively into two genuinely `ℝ≥0`-valued, equivalent
  -- valuations on `K`, applying `Valuation.exists_rpow_eq_of_isEquiv` (proved above) to relate
  -- them by a positive real exponent `t`, then rescaling `hR.hom'` by `t` (via `NNReal.rpow`) to
  -- get a new `RankOne A.valuation` instance whose embedding matches `‖·‖` on `K` exactly.
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

/-- Given a rank-1 structure on `A.valuation` compatible with `‖·‖` on `K` (packaged by
`exists_rankOne_compatible`), the purely formal part of `exists_rankOne_absoluteValue_extends`:
transport the `Valued`/`RankOne` data into a `NontriviallyNormedField L` (via `Valued.mk'` and
`Valued.toNontriviallyNormedField`) and take the associated `AbsoluteValue`. -/
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

/-- **Uniqueness of the extension of a complete nonarchimedean valuation to an algebraic
extension.** If `K` is complete with respect to a nontrivial nonarchimedean norm and `L / K` is
algebraic, then any two `ValuationSubring`s of `L` restricting to `𝒪[K]` coincide.

This is the standard fact that makes the decomposition subgroup of a Henselian (in particular,
complete) valued field's valuation ring extension equal to the *whole* Galois group: it is proved
here from `spectralNorm_unique_field_norm_ext` (Mathlib's unique norm extension theorem) via
`exists_rankOne_absoluteValue_extends`, so its only dependency on unformalized mathematics is
that one lemma. -/
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

end NormedFieldBridge

end LocalField

section ComapSmul

open scoped Pointwise

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The comap of a `σ`-translate of a valuation subring of `L` (for `σ : L ≃ₐ[K] L`) along
`algebraMap K L` does not depend on `σ`: automorphisms of `L` over `K` fix `K` pointwise, so
`σ • A` restricts to the same subring of `K` that `A` does. Purely formal, no `sorry`. -/
theorem ValuationSubring.comap_smul_eq (σ : L ≃ₐ[K] L) (A : ValuationSubring L) :
    (σ • A).comap (algebraMap K L) = A.comap (algebraMap K L) := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    show σ⁻¹ (algebraMap K L x) = algebraMap K L x from σ⁻¹.commutes x]

end ComapSmul
