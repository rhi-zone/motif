import Langlands.ResidueFieldNorm
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# `w.adicCompletionIntegers L` is the integral closure of `v.adicCompletionIntegers K`

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`. `Langlands.NormMap` proves
(`IsDedekindDomain.HeightOneSpectrum.isIntegral_of_mem_of_comap_eq`) that every element of
`w.adicCompletionIntegers L`, viewed as a valuation subring of `w.adicCompletion L` comapping to
`v.adicCompletionIntegers K`, is integral over `v.adicCompletionIntegers K` — the hard half of
identifying `w.adicCompletionIntegers L` with the integral closure of `v.adicCompletionIntegers K`
in `w.adicCompletion L` (Serre, *Local Fields*, Ch. II §2), proved there via a Galois-conjugate
argument that genuinely uses completeness.

This file supplies the other, easy half — every element of `w.adicCompletion L` integral over
`v.adicCompletionIntegers K` already lies in `w.adicCompletionIntegers L` — via a standalone
generalization of `Valuation.Integers.isIntegral_iff_v_le_one` (`isIntegral_imp_map_le_one` below)
that drops the surjectivity-onto-the-valuation-ring hypothesis bundled into `Valuation.Integers`,
needed here because `v.adicCompletionIntegers K` sits properly inside `w.adicCompletionIntegers L`
in general. Together the two halves give `IsIntegralClosure (w.adicCompletionIntegers L)
(v.adicCompletionIntegers K) (w.adicCompletion L)`, which unlocks `Module.Finite`/`Module.Free` of
`w.adicCompletionIntegers L` over `v.adicCompletionIntegers K` from
`Mathlib.RingTheory.DedekindDomain.IntegralClosure`, under a `Algebra.IsSeparable` hypothesis on
`w.adicCompletion L / v.adicCompletion K` (automatic in characteristic `0`, e.g. for number
fields, but not in general — Mathlib's `IsIntegralClosure.finite`/`.module_free` are themselves
stated only for finite *separable* extensions).

## Main results

* `Valuation.isIntegral_imp_map_le_one` : a standalone, non-`HeightOneSpectrum`-specific
  generalization of the easy half of `Valuation.Integers.isIntegral_iff_v_le_one`.
* `IsDedekindDomain.HeightOneSpectrum.isIntegral_iff_mem_adicCompletionIntegers` : an element of
  `w.adicCompletion L` is integral over `v.adicCompletionIntegers K` iff it lies in
  `w.adicCompletionIntegers L`.
* `IsDedekindDomain.HeightOneSpectrum.instIsIntegralClosureAdicCompletionIntegers` :
  `w.adicCompletionIntegers L` is the integral closure of `v.adicCompletionIntegers K` in
  `w.adicCompletion L`.
* `IsDedekindDomain.HeightOneSpectrum.instModuleFiniteAdicCompletionIntegers` :
  `w.adicCompletionIntegers L` is a finite `v.adicCompletionIntegers K`-module.
* `IsDedekindDomain.HeightOneSpectrum.instModuleFreeAdicCompletionIntegers` :
  `w.adicCompletionIntegers L` is a free `v.adicCompletionIntegers K`-module.
-/

noncomputable section

open IsDedekindDomain IsLocalRing

namespace Valuation

section IsIntegralImpMapLeOne

open Polynomial

variable {R O : Type*} {Γ₀ : Type*} [CommRing R] [CommRing O]
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) [Algebra O R]

/-- If every element of `O` has valuation `≤ 1` in `R` under an algebra map `O →+* R`, then every
element of `R` integral over `O` also has valuation `≤ 1`.

This is the easy half of `Valuation.Integers.isIntegral_iff_v_le_one`, generalized to drop the
`Valuation.Integers` bundling — in particular its `exists_of_le_one` surjectivity field, which
does not hold when `O` is a proper subring of `v.integer` (as with `v.adicCompletionIntegers K`
inside `w.adicCompletionIntegers L`). The proof is otherwise identical to the forward direction of
`Valuation.Integers.isIntegral_iff_v_le_one`. -/
theorem isIntegral_imp_map_le_one (hle : ∀ a : O, v (algebraMap O R a) ≤ 1) {x : R}
    (hx : IsIntegral O x) : v x ≤ 1 := by
  nontriviality R
  obtain ⟨f, hm, hf⟩ := hx
  by_cases hn : f.natDegree = 0
  · exfalso
    rw [Polynomial.natDegree_eq_zero] at hn
    obtain ⟨c, rfl⟩ := hn
    rw [Polynomial.eval₂_C] at hf
    have hc1 : c = 1 := by
      have := hm.leadingCoeff
      rwa [Polynomial.leadingCoeff_C] at this
    rw [hc1, map_one] at hf
    exact one_ne_zero hf
  simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
    one_mul, add_eq_zero_iff_eq_neg] at hf
  apply_fun v at hf
  simp only [map_neg, map_pow] at hf
  contrapose! hf
  refine ne_of_lt (v.map_sum_lt ?_ ?_)
  · simp [hn, (hf.trans' zero_lt_one).ne']
  · simp only [Finset.mem_range, map_mul, map_pow]
    intro i hi
    exact mul_lt_of_le_one_of_lt (hle _) <| pow_lt_pow_right₀ hf hi

end IsIntegralImpMapLeOne

end Valuation

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

/-! ### The algebra structure of `w.adicCompletion L` over `v.adicCompletionIntegers K` -/

/-- `v.adicCompletionIntegers K`-algebra structure on `w.adicCompletion L`, the composite through
`v.adicCompletion K`. -/
instance instAlgebraAdicCompletionIntegersAdicCompletion :
    Algebra (v.adicCompletionIntegers K) (w.adicCompletion L) :=
  ((adicCompletionComap K L v w).comp (v.adicCompletionIntegers K).subtype).toAlgebra

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
theorem algebraMap_adicCompletionIntegers_adicCompletion (a : v.adicCompletionIntegers K) :
    algebraMap (v.adicCompletionIntegers K) (w.adicCompletion L) a =
      adicCompletionComap K L v w (a : v.adicCompletion K) := rfl

instance instIsScalarTowerAdicCompletionIntegersAdicCompletion :
    IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun a => (algebraMap_adicCompletionIntegers_adicCompletion K L v w a).symm

instance instIsScalarTowerAdicCompletionIntegers :
    IsScalarTower (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
      (w.adicCompletion L) :=
  .of_algebraMap_eq fun a => by
    rw [algebraMap_adicCompletionIntegers_adicCompletion]
    exact coe_algebraMap_adicCompletionIntegers K L v w a

/-- `w.adicCompletion L` is a torsion-free `v.adicCompletionIntegers K`-module: the algebra map
`v.adicCompletionIntegers K → w.adicCompletion L` is injective (a composite of the injective
inclusion into `v.adicCompletion K` with the injective ring hom `adicCompletionComap` out of the
field `v.adicCompletion K`), and `w.adicCompletion L` is a field. -/
instance instIsTorsionFreeAdicCompletionIntegersAdicCompletion :
    Module.IsTorsionFree (v.adicCompletionIntegers K) (w.adicCompletion L) :=
  have hinj : Function.Injective
      (algebraMap (v.adicCompletionIntegers K) (w.adicCompletion L)) :=
    (RingHom.injective (adicCompletionComap K L v w)).comp Subtype.coe_injective
  .of_smul_eq_zero fun r x hrx => by
    rw [Algebra.smul_def] at hrx
    rcases mul_eq_zero.mp hrx with h | h
    · exact Or.inl (hinj (by rwa [map_zero]))
    · exact Or.inr h

/-! ### `w.adicCompletionIntegers L` is the integral closure of `v.adicCompletionIntegers K` -/

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- Every element of `v.adicCompletionIntegers K`, viewed inside `w.adicCompletion L` via
`adicCompletionComap`, lies in `w.adicCompletionIntegers L`. This is `adicCompletionIntegers_comap_eq`
read pointwise, and supplies the hypothesis of `Valuation.isIntegral_imp_map_le_one`. -/
theorem valuation_algebraMap_adicCompletionIntegers_le_one (a : v.adicCompletionIntegers K) :
    Valued.v (adicCompletionComap K L v w (a : v.adicCompletion K)) ≤ 1 := by
  rw [← mem_adicCompletionIntegers,
    ← ValuationSubring.mem_comap (A := w.adicCompletionIntegers L)
      (f := adicCompletionComap K L v w),
    adicCompletionIntegers_comap_eq K L v w]
  exact a.2

omit [Algebra.IsIntegral R S] in
/-- An element of `w.adicCompletion L` is integral over `v.adicCompletionIntegers K` iff it lies
in `w.adicCompletionIntegers L`. The forward direction is
`Valuation.isIntegral_imp_map_le_one`; the reverse is
`IsDedekindDomain.HeightOneSpectrum.isIntegral_of_mem_of_comap_eq` (`Langlands.NormMap`), applied
with the completeness of `v.adicCompletion K`. -/
theorem isIntegral_iff_mem_adicCompletionIntegers {x : w.adicCompletion L} :
    IsIntegral (v.adicCompletionIntegers K) x ↔ x ∈ w.adicCompletionIntegers L := by
  constructor
  · intro hx
    rw [mem_adicCompletionIntegers]
    exact Valuation.isIntegral_imp_map_le_one Valued.v
      (valuation_algebraMap_adicCompletionIntegers_le_one K L v w) hx
  · intro hx
    have hbridge := valuation_valuationSubring_eq_adicCompletionIntegers K v
    have hcomap : (w.adicCompletionIntegers L).comap (adicCompletionComap K L v w)
        = (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring := by
      rw [hbridge]; exact adicCompletionIntegers_comap_eq K L v w
    have := isIntegral_of_mem_of_comap_eq (w.adicCompletionIntegers L) hcomap
      (x := x) hx
    rwa [hbridge] at this

/-- `w.adicCompletionIntegers L` is the integral closure of `v.adicCompletionIntegers K` in
`w.adicCompletion L`. -/
instance instIsIntegralClosureAdicCompletionIntegers :
    IsIntegralClosure (w.adicCompletionIntegers L) (v.adicCompletionIntegers K)
      (w.adicCompletion L) where
  algebraMap_injective := Subtype.coe_injective
  isIntegral_iff {x} := by
    rw [isIntegral_iff_mem_adicCompletionIntegers K L v w]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

/-! ### Galois automorphisms preserve `w.adicCompletionIntegers L` and its maximal-ideal filtration
EXACTLY -/

omit [Algebra.IsIntegral R S] in
/-- **A `K_v`-algebra automorphism of `L_w` preserves `w.adicCompletionIntegers L`.** `σ` fixes
`v.adicCompletion K` pointwise, so `σ.toAlgHom` is an algebra map over `v.adicCompletionIntegers K`
too (via `instIsScalarTowerAdicCompletionIntegersAdicCompletion`); `IsIntegral.map` then carries
integrality over `v.adicCompletionIntegers K` along `σ`, and `isIntegral_iff_mem_adicCompletionIntegers`
converts this back to membership in `w.adicCompletionIntegers L`. -/
theorem mem_adicCompletionIntegers_algEquiv
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) {x : w.adicCompletion L}
    (hx : x ∈ w.adicCompletionIntegers L) : σ x ∈ w.adicCompletionIntegers L := by
  rw [← isIntegral_iff_mem_adicCompletionIntegers K L v w] at hx ⊢
  exact hx.map σ.toAlgHom

omit [Algebra.IsIntegral R S] in
/-- **The restriction of a `K_v`-algebra automorphism of `L_w` to `w.adicCompletionIntegers L`, as
a ring automorphism of that subring.** Built directly from `mem_adicCompletionIntegers_algEquiv`
applied to `σ` and `σ.symm`. -/
noncomputable def restrictAdicCompletionIntegers
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :
    w.adicCompletionIntegers L ≃+* w.adicCompletionIntegers L where
  toFun x := ⟨σ x, mem_adicCompletionIntegers_algEquiv K L v w σ x.2⟩
  invFun x := ⟨σ.symm x, mem_adicCompletionIntegers_algEquiv K L v w σ.symm x.2⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

omit [Algebra.IsIntegral R S] in
@[simp]
theorem coe_restrictAdicCompletionIntegers
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (x : w.adicCompletionIntegers L) :
    (restrictAdicCompletionIntegers K L v w σ x : w.adicCompletion L) = σ (x : w.adicCompletion L) :=
  rfl

omit [Algebra.IsIntegral R S] in
/-- **`restrictAdicCompletionIntegers σ` fixes the maximal ideal of `w.adicCompletionIntegers L`
exactly**, for *any* `K_v`-algebra automorphism `σ` of `L_w`. A ring isomorphism sends a maximal
ideal to a maximal ideal (`Ideal.map_isMaximal_of_equiv`), and `w.adicCompletionIntegers L` is a
local ring with a unique maximal ideal (`IsLocalRing.eq_maximalIdeal`), so the image is that same
ideal — no epsilon or Lipschitz-constant estimate is needed, unlike the analytic ε/δ route this
lemma replaces in `AdicCompletionNormExpTrace.lean`. -/
theorem map_maximalIdeal_restrictAdicCompletionIntegers
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :
    Ideal.map (restrictAdicCompletionIntegers K L v w σ) (maximalIdeal (w.adicCompletionIntegers L))
      = maximalIdeal (w.adicCompletionIntegers L) :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.map_isMaximal_of_equiv (restrictAdicCompletionIntegers K L v w σ))

omit [Algebra.IsIntegral R S] in
/-- **`σ` preserves membership in `𝔪_{L_w}^i` exactly, for the SAME `i`.** Unlike a generic ε/δ
continuity argument, the threshold level `i` here needs no adjustment at all when passing from `x`
to `σ x` — Galois conjugation is an *exact* symmetry of the filtration, not merely a continuous
one. -/
theorem restrictAdicCompletionIntegers_mem_maximalIdeal_pow
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) {i : ℕ}
    {x : w.adicCompletionIntegers L} (hx : x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i) :
    restrictAdicCompletionIntegers K L v w σ x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i := by
  rw [← map_maximalIdeal_restrictAdicCompletionIntegers K L v w σ, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hx

/-! ### `Module.Finite` / `Module.Free` -/

variable [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]

/-- `w.adicCompletionIntegers L` is a finite `v.adicCompletionIntegers K`-module. Requires
`w.adicCompletion L / v.adicCompletion K` separable (automatic in characteristic `0`), matching
the hypotheses of `IsIntegralClosure.finite`. -/
instance instModuleFiniteAdicCompletionIntegers :
    Module.Finite (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  IsIntegralClosure.finite (v.adicCompletionIntegers K) (v.adicCompletion K) (w.adicCompletion L)
    (w.adicCompletionIntegers L)

/-- `w.adicCompletionIntegers L` is a free `v.adicCompletionIntegers K`-module. -/
instance instModuleFreeAdicCompletionIntegers :
    Module.Free (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  IsIntegralClosure.module_free (v.adicCompletionIntegers K) (v.adicCompletion K)
    (w.adicCompletion L) (w.adicCompletionIntegers L)

end IsDedekindDomain.HeightOneSpectrum

end
