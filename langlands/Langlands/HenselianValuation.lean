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
  genuinely deep facts that are not yet in Mathlib (see the docstring below) and is recorded as
  the sole `sorry` in this file.
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

The single deep `sorry`, `exists_rankOne_compatible`, packages together:

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

Fixing this requires strengthening the hypotheses of `exists_rankOne_compatible`, e.g. by adding
`[ValuativeRel.IsNontrivial K]` and an explicit compatibility hypothesis tying `valuation K` to
the norm (such as `[Fact (NormedField.valuation (K := K)).Compatible]`, using
`Valuation.Compatible` from `Mathlib.RingTheory.Valuation.ValuativeRel.Basic`). Given this is a
change to the theorem's signature (not just its proof), `exists_rankOne_compatible` is left as
the file's one `sorry`, with the mathematical content of fact #1 (modulo this missing hypothesis)
captured by the two lemmas above, ready to be assembled once the signature is corrected.
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

What remains genuinely open (and is the one `sorry` left in this file): extending this rank-≤-1-ness
from `K` to all of `L`. Via `hequiv` below, the K-restriction of `A.valuation` is equivalent to
`valuation K`, hence itself rank ≤ 1 with matching normalization; but `A.valuation` on the whole of
`L` could a priori still have larger rank. Bridging this needs the "rank preservation under
algebraic extension" argument sketched in the module docstring: bound every `x ≠ 0` in `L` above
and below (via `x` and `x⁻¹`'s minimal polynomials, using `Valuation.exists_pow_le_of_isAlgebraic`
above) by powers of `K`-values, chain through `MulArchimedeanClass.mk_eq_mk` using the
archimedean-ness of `valuation K`'s value group (now genuinely available, via `hRK` below and
`MulArchimedean.of_units`), and invoke `Valuation.nonempty_rankOne_iff_mulArchimedean`. This is not
yet in Mathlib and is not attempted here; only the (now correct, and no longer a counterexample)
statement and its `K`-restricted special case are established. -/
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
  -- **Step 3**, the genuine remaining gap: extend rank ≤ 1 (and the compatible normalization)
  -- from `valuation K` (via `hequiv`, i.e. from the K-part of `A.valuation`) to the whole of
  -- `A.valuation` on `L`. See the "What remains genuinely open" paragraph of the docstring above.
  sorry

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
