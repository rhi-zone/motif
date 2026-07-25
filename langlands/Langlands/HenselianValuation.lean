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
  genuinely deep facts described in the docstring below. As of this file's current state, the
  existence half (`RankOne A.valuation` is nonempty, i.e. rank ≤ 1 is preserved) is proved in
  full *modulo one precisely-scoped `sorry`* (`hLtoK` in the proof, a genuine reverse-direction
  minimal-polynomial estimate not derivable from `Valuation.exists_pow_le_of_isAlgebraic` alone);
  the compatible-normalization half is a second, separately-scoped `sorry` (a Hölder-uniqueness-
  for-archimedean-groups argument, also not yet in Mathlib). See the two `sorry`-site comments
  in the proof for the precise mathematical content each represents.
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
* Step 3d (`hLtoK`) is the **first genuine remaining gap**: the *reverse*-direction bound (some
  `K`-anchor dominated *by* a power of an arbitrary `y : L`, not the other way round). This is
  not obtainable from `Valuation.exists_pow_le_of_isAlgebraic` by any combination of applications
  to `y`, `y⁻¹`, or auxiliary elements -- see the `sorry`-site comment for why -- and needs the
  explicit reversed-minimal-polynomial relationship between `minpoly K y` and `minpoly K y⁻¹`
  (Bourbaki, *Comm. Alg.* VI §10.1; Engler-Prestel, *Valued Fields* Thm. 3.2.4), which is new
  infrastructure not yet written down anywhere.
* Steps 3e-3f assemble `hbound`, `hLtoK`, and `hAanchorPos` into `MulArchimedean A.ValueGroup`
  directly (`hMArchA`, via the `MulArchimedean` class's `arch` field) and transfer this to obtain
  `Nonempty (RankOne A.valuation)` (`hR`) via `nonempty_rankOne_iff_mulArchimedean` -- i.e. rank
  ≤ 1 of `A.valuation` is fully proved *modulo* `hLtoK`.
* Step 3g is the **second genuine remaining gap**: `hR` is *some* `RankOne` instance, not
  necessarily the one matching `‖·‖` on `K`. Fixing the normalization needs Hölder's uniqueness
  theorem for archimedean linearly ordered groups (any two strictly monotone monoid homs into
  `ℝ≥0` agree up to a positive real power), which is not in Mathlib; see the `sorry`-site comment
  for the intended rescaling construction once it is available.

Both gaps are self-contained, precisely-scoped pieces of missing infrastructure -- not
tactic-closable, and not resolvable by further exploration of what is already proved above. -/
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
  -- **Step 3d, the first genuine remaining gap.** `hbound` above (via `Valuation.
  -- exists_pow_le_of_isAlgebraic`) only ever bounds a power of an element `x : L` *above* by a
  -- `K`-value: `A.valuation x ^ (n - i) ≤ A.valuation (algebraMap c_i)`. That one-sidedness is a
  -- structural feature of the ultrametric-on-the-minimal-polynomial argument (it comes from
  -- `Valuation.map_sum_le`, an inequality, not an equality), and no combination of applications
  -- of `hbound` to `y`, `y⁻¹`, or auxiliary `K`-elements yields the *reverse* containment needed
  -- here: some `K`-anchor dominated *by* a power of `y` (as opposed to dominating a power of
  -- `y`). Concretely: applying `hbound` to `y` gives `y ≤ (K-anchor)`; applying it to `y⁻¹` gives
  -- `(K-anchor)⁻¹ ≤ y`, but that anchor's sign (`≤ 1` or `> 1`) is not controlled by the
  -- existential, so it need not be informative (if the anchor is `≥ 1`, `(anchor)⁻¹ ≤ 1 < y` is
  -- vacuous). The standard fix (Bourbaki, *Comm. Alg.* VI §10.1; Engler-Prestel, *Valued
  -- Fields* Thm. 3.2.4) uses the *explicit* relationship between the coefficients of
  -- `minpoly K y` and `minpoly K y⁻¹` (the latter is, up to the nonzero constant term of the
  -- former, the "reversed" polynomial), which is not yet available in this file or in Mathlib as
  -- a reusable lemma. Formalizing that relationship (and redoing the ultrametric argument with
  -- it) is the real remaining content of "rank ≤ 1 is preserved under algebraic extension"; it
  -- is a self-contained, well-scoped piece of new infrastructure, not a tactic-closable gap. -/
  have hLtoK : ∀ y : L, y ≠ 0 → 1 < A.valuation y →
      ∃ (d : K) (N : ℕ), 1 < A.valuation (algebraMap K L d) ∧
        A.valuation (algebraMap K L d) ≤ A.valuation y ^ N := by
    sorry
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
  -- **Step 3g, the second genuine remaining gap.** `hR` is *some* `RankOne A.valuation`
  -- instance (Steps 3a-3f above establish its existence unconditionally), but its embedding
  -- `hR.hom' : ValueGroup₀ (.ofClass A.valuation) → ℝ≥0` need not agree with `‖·‖` on `K` (only
  -- `Nonempty` was produced, not a specific normalization). Fixing this is routine in substance
  -- but not yet written down: for a `MulArchimedean` linearly ordered group, any two strictly
  -- monotone monoid homomorphisms into `ℝ≥0` agree up to raising to a positive real power
  -- (Hölder's theorem for archimedean ordered groups -- not currently in Mathlib, see the
  -- `nonempty_rankOne_iff_mulArchimedean` proof in `Mathlib.RingTheory.Valuation.RankOne` for the
  -- one-sided existence construction this would need to be paired with a uniqueness half of).
  -- Given that, the fix is: pick any `c₀ : K` with `1 < valuation K c₀` (exists by
  -- `hvK_nontrivial`), let `r₀ := hR.hom' (A.valuation.restrict (algebraMap K L c₀))` and
  -- `s₀ := ‖c₀‖` (both `> 1`), and rescale `hR.hom'` by the exponent `Real.log s₀ / Real.log r₀`
  -- (an `NNReal.rpow`) to build a new embedding matching `‖·‖` at `c₀`; Hölder uniqueness (once
  -- available) then upgrades this single-point match to agreement on all of `K`. This is a
  -- self-contained, well-scoped piece of missing order-theory infrastructure, not a
  -- tactic-closable gap.
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
