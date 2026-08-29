import Langlands.AdicCompletionIntegralClosure
import Langlands.AdicCompletionRamificationIdeal
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# The exact image of a filtration level under the trace map

This file computes `Tr_{L/K}(𝔪_B ^ i)` **exactly**, for an AKLB extension in which both `A` and `B`
are discrete valuation rings, in terms of the different exponent `d` (`differentIdeal A B =
𝔪_B ^ d`) and the ramification exponent `e` (`𝔪_A · B = 𝔪_B ^ e`):

`Tr_{L/K}(𝔪_B ^ i) = 𝔪_A ^ ((i + d) / e)`

with `/` natural-number division, i.e. `⌊(i + d) / e⌋`.

The point is that the answer is an *equality*, not merely a containment: no separate surjectivity
or genericity argument is needed. Mathlib's `differentialIdeal_le_fractionalIdeal_iff` is an *iff*,
so instantiating it at the principal fractional ideals `π_B ^ (i - j·e)` pins down the truth value
of `Tr(𝔪_B ^ i) ⊆ 𝔪_A ^ j` at *every* `j`; running it at `j = (i+d)/e` (true) and at `j + 1`
(false) sandwiches the image between two consecutive powers of `𝔪_A`, and ideals of a DVR are
totally ordered, so the sandwich collapses to an equality.

## Route

1. `DiscreteValuationTrace.exists_algebraMap_eq_zpow_iff` — in a DVR `R` with uniformizer `π` and
   fraction field `F`, the integer power `(algebraMap R F π) ^ n` lies in the image of `R` exactly
   when `0 ≤ n`. This is the only place discreteness of the valuation enters, and it is what turns
   every containment below into an inequality between integers.
2. `DiscreteValuationTrace.map_trace_spanSingleton_zpow_le_one_iff` — the core criterion, obtained
   by instantiating `differentialIdeal_le_fractionalIdeal_iff` at `I := π_B ^ (-n)` (so that
   `I⁻¹ = π_B ^ n`): `Tr(π_B ^ n · B) ⊆ A ↔ -n ≤ d`.
3. `DiscreteValuationTrace.map_trace_spanSingleton_zpow_le_coeSubmodule_iff` — the scaled form.
   Multiplying through by `π_A ^ (-j)`, whose image in `L` generates `𝔪_B ^ (-j·e)` by the
   hypothesis `he`, turns the criterion into `Tr(π_B ^ n · B) ⊆ 𝔪_A ^ j ↔ j·e ≤ n + d`. The
   scaling itself is `K`-linearity of the trace, applied elementwise; the unit ambiguity between
   `algebraMap A L π_A` and `π_B ^ e` is absorbed once, at the level of `spanSingleton`.
4. `DiscreteValuationTrace.map_trace_coeSubmodule_maximalIdeal_pow` — the headline equality, by the
   sandwich argument.

Everything is phrased with `Submodule.map ((Algebra.trace K L).restrictScalars A)`, i.e. with the
`K`-linear trace, so no naturality statement relating the bundled integral trace
`Algebra.trace A B : B →ₗ[A] A` to `Algebra.trace K L` is needed: the image is manifestly an
`A`-submodule of `K`, and step 3 at `j = 0` places it inside `A`.

## Main results

* `DiscreteValuationTrace.map_trace_coeSubmodule_maximalIdeal_pow` : the generic DVR-AKLB
  statement.
* `IsDedekindDomain.HeightOneSpectrum.map_trace_coeSubmodule_maximalIdeal_pow_adicCompletion` : its
  instantiation at a pair of adic completions, where the ramification hypothesis `he` is supplied
  by `map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx'` and `e` is
  `v.asIdeal.ramificationIdx' w.asIdeal`.
-/

noncomputable section

open nonZeroDivisors IsLocalRing IsLocalization FractionalIdeal

namespace DiscreteValuationTrace

/-! ### Integer powers of a uniformizer -/

section DVRZPow

variable {R F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Algebra R F]
  [IsFractionRing R F]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Integrality of an integer power of a uniformizer is decided by the sign of the exponent.**
In a discrete valuation ring `R` with fraction field `F` and uniformizer `π`, the element
`(algebraMap R F π) ^ n` (for `n : ℤ`) lies in the image of `R` if and only if `0 ≤ n`.

The forward direction is where irreducibility is used: if `n < 0`, clearing denominators exhibits
`π` as a unit. -/
theorem exists_algebraMap_eq_zpow_iff {π : R} (hπ : Irreducible π) (n : ℤ) :
    (∃ r : R, algebraMap R F r = (algebraMap R F π) ^ n) ↔ 0 ≤ n := by
  have hπ0 : (algebraMap R F π) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hπ.ne_zero
  constructor
  · rintro ⟨r, hr⟩
    by_contra hn
    push Not at hn
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -((k + 1 : ℕ) : ℤ) := ⟨(-n - 1).toNat, by omega⟩
    subst hk
    rw [zpow_neg, zpow_natCast] at hr
    have hpow : (algebraMap R F π) ^ (k + 1) ≠ 0 := pow_ne_zero _ hπ0
    have hmap : algebraMap R F (r * π ^ (k + 1)) = algebraMap R F 1 := by
      rw [map_mul, map_pow, hr, map_one, inv_mul_cancel₀ hpow]
    have hmul : r * π ^ (k + 1) = 1 := IsFractionRing.injective R F hmap
    refine hπ.not_isUnit (IsUnit.of_mul_eq_one (r * π ^ k) ?_)
    rw [← hmul]; ring
  · intro hn
    lift n to ℕ using hn
    exact ⟨π ^ n, by rw [map_pow, zpow_natCast]⟩

omit [IsFractionRing R F] in
/-- Membership in `𝔪_R ^ j`, read off through a uniformizer: `t : F` lies in the image of `𝔪_R ^ j`
exactly when it is `π ^ j` times the image of an element of `R`. -/
theorem mem_coeSubmodule_maximalIdeal_pow_iff {π : R} (hπ : Irreducible π) (j : ℕ) (t : F) :
    t ∈ coeSubmodule F (maximalIdeal R ^ j) ↔
      ∃ c : R, algebraMap R F c * (algebraMap R F π) ^ j = t := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.span_singleton_pow,
    coeSubmodule, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    exact ⟨c, by simp [Algebra.linearMap_apply, map_mul, map_pow]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c * π ^ j, Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩, by
      simp [Algebra.linearMap_apply, map_mul, map_pow]⟩

/-- Powers of the maximal ideal of a DVR, viewed inside the fraction field, are totally ordered by
their exponent — with the order reversed. -/
theorem coeSubmodule_maximalIdeal_pow_le_iff {π : R} (hπ : Irreducible π) (k m : ℕ) :
    coeSubmodule F (maximalIdeal R ^ k) ≤ coeSubmodule F (maximalIdeal R ^ m) ↔ m ≤ k := by
  constructor
  · intro h
    have hmem : (algebraMap R F π) ^ k ∈ coeSubmodule F (maximalIdeal R ^ m) :=
      h ((mem_coeSubmodule_maximalIdeal_pow_iff hπ k _).mpr ⟨1, by rw [map_one, one_mul]⟩)
    obtain ⟨c, hc⟩ := (mem_coeSubmodule_maximalIdeal_pow_iff hπ m _).mp hmem
    have hπ0 : (algebraMap R F π) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hπ.ne_zero
    have hc' : algebraMap R F c = (algebraMap R F π) ^ ((k : ℤ) - m) := by
      rw [zpow_sub₀ hπ0, zpow_natCast, zpow_natCast, eq_div_iff (pow_ne_zero _ hπ0), hc]
    have := (exists_algebraMap_eq_zpow_iff hπ ((k : ℤ) - m)).mp ⟨c, hc'⟩
    omega
  · intro h
    exact Submodule.map_mono (Ideal.pow_le_pow_right h)

end DVRZPow

/-! ### The generic DVR-AKLB trace image formula -/

section AKLB

variable {A K L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K]
  [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [IsIntegralClosure B A L] [IsIntegrallyClosed A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B] [IsFractionRing B L] [IsDiscreteValuationRing A]
  [IsDiscreteValuationRing B]

omit [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [IsIntegralClosure B A L] [IsIntegrallyClosed A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] in
/-- A containment `Tr(y · B) ⊆ N` unfolded to a statement about the elements `Tr (b · y)`. -/
theorem map_trace_spanSingleton_le_iff (y : L) (N : Submodule A K) :
    Submodule.map ((Algebra.trace K L).restrictScalars A)
        (Submodule.restrictScalars A
          ((spanSingleton B⁰ y : FractionalIdeal B⁰ L) : Submodule B L)) ≤ N ↔
      ∀ b : B, Algebra.trace K L (algebraMap B L b * y) ∈ N := by
  rw [Submodule.map_le_iff_le_comap]
  constructor
  · intro h b
    have hmem : algebraMap B L b * y ∈ Submodule.restrictScalars A
        ((spanSingleton B⁰ y : FractionalIdeal B⁰ L) : Submodule B L) := by
      rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe]
      exact (FractionalIdeal.mem_spanSingleton _).mpr ⟨b, by rw [Algebra.smul_def]⟩
    simpa using h hmem
  · intro h z hz
    rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_spanSingleton] at hz
    obtain ⟨b, rfl⟩ := hz
    rw [Algebra.smul_def]
    simpa using h b

omit [IsDiscreteValuationRing A] in
/-- **The core trace criterion.** With `d` the different exponent (`differentIdeal A B = 𝔪_B ^ d`),
the trace maps the principal fractional ideal `π_B ^ n · B` into `A` exactly when `-n ≤ d`.

This is `differentialIdeal_le_fractionalIdeal_iff` instantiated at `I := π_B ^ (-n)` — so that
`I⁻¹ = π_B ^ n` — together with `exists_algebraMap_eq_zpow_iff`, which turns the resulting
containment of principal fractional ideals into an inequality of integers. -/
theorem map_trace_spanSingleton_zpow_le_one_iff {πB : B} (hπB : Irreducible πB) {d : ℕ}
    (hd : differentIdeal A B = maximalIdeal B ^ d) (n : ℤ) :
    Submodule.map ((Algebra.trace K L).restrictScalars A)
        (Submodule.restrictScalars A
          ((spanSingleton B⁰ ((algebraMap B L πB) ^ n) : FractionalIdeal B⁰ L) :
            Submodule B L)) ≤ 1 ↔ -n ≤ (d : ℤ) := by
  have hx0 : (algebraMap B L πB) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hπB.ne_zero
  have hI : (spanSingleton B⁰ ((algebraMap B L πB) ^ (-n)) : FractionalIdeal B⁰ L) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact zpow_ne_zero _ hx0
  have hiff := differentialIdeal_le_fractionalIdeal_iff (A := A) (K := K) hI
  rw [FractionalIdeal.spanSingleton_inv, ← zpow_neg, neg_neg] at hiff
  rw [← hiff, hd, (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp hπB,
    Ideal.span_singleton_pow, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_spanSingleton]
  have hstep : (∃ z : B, z • (algebraMap B L πB) ^ (-n) = algebraMap B L (πB ^ d)) ↔
      ∃ z : B, algebraMap B L z = (algebraMap B L πB) ^ ((d : ℤ) + n) := by
    refine exists_congr fun z => ?_
    rw [Algebra.smul_def, map_pow, zpow_neg, ← div_eq_mul_inv,
      div_eq_iff (zpow_ne_zero n hx0), ← zpow_natCast (algebraMap B L πB) d, ← zpow_add₀ hx0]
  rw [hstep, exists_algebraMap_eq_zpow_iff hπB]
  omega

/-- **The scaled trace criterion.** `Tr(π_B ^ n · B) ⊆ 𝔪_A ^ j ↔ j·e ≤ n + d`, where `e` is the
ramification exponent (`𝔪_A · B = 𝔪_B ^ e`) and `d` the different exponent.

The scaling by `π_A ^ (-j)` is `K`-linearity of the trace applied elementwise
(`map_trace_spanSingleton_le_iff` on both sides); the unit ambiguity between `algebraMap A L π_A`
and `π_B ^ e` is absorbed once, in `hspan`, at the level of `spanSingleton`. -/
theorem map_trace_spanSingleton_zpow_le_coeSubmodule_iff {πA : A} (hπA : Irreducible πA) {πB : B}
    (hπB : Irreducible πB) {d e : ℕ} (hd : differentIdeal A B = maximalIdeal B ^ d)
    (he : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ e) (n : ℤ) (j : ℕ) :
    Submodule.map ((Algebra.trace K L).restrictScalars A)
        (Submodule.restrictScalars A
          ((spanSingleton B⁰ ((algebraMap B L πB) ^ n) : FractionalIdeal B⁰ L) :
            Submodule B L)) ≤ coeSubmodule K (maximalIdeal A ^ j) ↔
      (j : ℤ) * e ≤ n + d := by
  set x : L := algebraMap B L πB with hxdef
  set α : K := algebraMap A K πA with hαdef
  have hx0 : x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hπB.ne_zero
  have hα0 : α ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hπA.ne_zero
  have hαL0 : algebraMap K L α ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr hα0
  -- `algebraMap A B π_A` and `π_B ^ e` are associated.
  obtain ⟨u, hu⟩ : Associated (algebraMap A B πA) (πB ^ e) := by
    refine Ideal.span_singleton_eq_span_singleton.mp ?_
    rw [← Ideal.span_singleton_pow, ← (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp
      hπB, ← he, (IsDiscreteValuationRing.irreducible_iff_uniformizer πA).mp hπA, Ideal.map_span,
      Set.image_singleton]
  -- Hence `algebraMap K L α = π_B ^ e * (unit)⁻¹` in `L`.
  have hθ : algebraMap K L α = x ^ e * algebraMap B L ((u⁻¹ : Bˣ) : B) := by
    rw [hαdef, ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L, hxdef,
      ← map_pow, ← map_mul]
    congr 1
    rw [← hu]
    simp [mul_assoc]
  have hwu0 : algebraMap B L ((u : Bˣ) : B) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr u.ne_zero
  have hθ0 : algebraMap K L α ≠ 0 := hαL0
  -- The positive-power form of the comparison, in `ℕ` exponents only.
  have hpos : (algebraMap K L α) ^ j * (algebraMap B L ((u : Bˣ) : B)) ^ j = x ^ (j * e) := by
    rw [hθ, mul_pow, mul_assoc, ← mul_pow, ← map_mul]
    simp [← pow_mul, Nat.mul_comm]
  have hθinv : (algebraMap K L α) ^ (-(j : ℤ)) =
      x ^ (-((j : ℤ) * e)) * (algebraMap B L ((u : Bˣ) : B)) ^ j := by
    have hx' : x ^ (-((j : ℤ) * e)) = (x ^ (j * e))⁻¹ := by
      rw [← zpow_natCast x (j * e), ← zpow_neg]
      push_cast
      ring_nf
    rw [zpow_neg, zpow_natCast, hx', ← hpos]
    field_simp
  -- The scaled fractional ideal is again a power of `π_B`.
  have hspan : (spanSingleton B⁰ ((algebraMap K L α) ^ (-(j : ℤ)) * x ^ n) :
        FractionalIdeal B⁰ L) =
      spanSingleton B⁰ (x ^ (n - (j : ℤ) * e)) := by
    have hval : (algebraMap K L α) ^ (-(j : ℤ)) * x ^ n =
        algebraMap B L (((u : Bˣ) : B) ^ j) * x ^ (n - (j : ℤ) * e) := by
      rw [hθinv, map_pow, zpow_sub₀ hx0, zpow_neg]
      field_simp
    rw [hval, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← FractionalIdeal.coeIdeal_span_singleton,
      Ideal.span_singleton_eq_top.mpr (u.isUnit.pow j), FractionalIdeal.coeIdeal_top, one_mul]
  -- Now compare the two containments elementwise.
  have hcore := map_trace_spanSingleton_zpow_le_one_iff (A := A) (K := K) (L := L) hπB hd
    (n - (j : ℤ) * e)
  rw [← hspan, map_trace_spanSingleton_le_iff] at hcore
  rw [map_trace_spanSingleton_le_iff]
  refine Iff.trans ?_ (hcore.trans ⟨by omega, by omega⟩)
  refine forall_congr' fun b => ?_
  rw [mem_coeSubmodule_maximalIdeal_pow_iff hπA, Submodule.mem_one]
  have hlin : ∀ (c : K) (y : L), Algebra.trace K L (algebraMap K L c * y) =
      c * Algebra.trace K L y := by
    intro c y
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hrw : Algebra.trace K L (algebraMap B L b * ((algebraMap K L α) ^ (-(j : ℤ)) * x ^ n)) =
      α ^ (-(j : ℤ)) * Algebra.trace K L (algebraMap B L b * x ^ n) := by
    rw [show algebraMap B L b * ((algebraMap K L α) ^ (-(j : ℤ)) * x ^ n)
        = algebraMap K L (α ^ (-(j : ℤ))) * (algebraMap B L b * x ^ n) by
      rw [map_zpow₀]; ring, hlin]
  rw [hrw]
  simp only [← hαdef]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← hc, zpow_neg, zpow_natCast]
    field_simp
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hc, zpow_neg, zpow_natCast]
    field_simp

omit [IsIntegrallyClosed A] [IsDiscreteValuationRing A] in
/-- Every nonzero different ideal of a DVR extension is a power of the maximal ideal. -/
theorem exists_differentIdeal_eq_maximalIdeal_pow (hbot : differentIdeal A B ≠ ⊥) :
    ∃ d : ℕ, differentIdeal A B = maximalIdeal B ^ d := by
  obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨d, hd⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hbot hπB
  exact ⟨d, by rw [hd, (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp hπB,
    Ideal.span_singleton_pow]⟩

/-- **The exact image of a filtration level under the trace map.**

`Tr_{L/K}(𝔪_B ^ i) = 𝔪_A ^ ((i + d) / e)`, with `d` the different exponent
(`differentIdeal A B = 𝔪_B ^ d`) and `e` the ramification exponent (`𝔪_A · B = 𝔪_B ^ e`);
the division is natural-number division, i.e. `⌊(i + d) / e⌋`.

The proof is a sandwich. `map_trace_spanSingleton_zpow_le_coeSubmodule_iff` decides the containment
`Tr(𝔪_B ^ i) ⊆ 𝔪_A ^ j` for every `j`: it holds at `j := (i + d) / e` and fails at `j + 1`. The
image is an `A`-submodule of `K` contained in the image of `A`, hence of the form `𝔪_A ^ k` (a
nonzero ideal of a DVR is a power of the maximal ideal); the two facts force
`(i + d) / e ≤ k ≤ (i + d) / e`. -/
theorem map_trace_coeSubmodule_maximalIdeal_pow {d e : ℕ} (he0 : e ≠ 0)
    (hd : differentIdeal A B = maximalIdeal B ^ d)
    (he : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ e) (i : ℕ) :
    Submodule.map ((Algebra.trace K L).restrictScalars A)
        (Submodule.restrictScalars A (coeSubmodule L (maximalIdeal B ^ i))) =
      coeSubmodule K (maximalIdeal A ^ ((i + d) / e)) := by
  obtain ⟨πA, hπA⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible B
  set j₀ := (i + d) / e with hj₀
  -- Rewrite the source as a principal fractional ideal.
  have hsrc : coeSubmodule L (maximalIdeal B ^ i) =
      ((spanSingleton B⁰ ((algebraMap B L πB) ^ (i : ℤ)) : FractionalIdeal B⁰ L) :
        Submodule B L) := by
    rw [← FractionalIdeal.coe_coeIdeal (S := B⁰) (P := L) (maximalIdeal B ^ i),
      (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp hπB, Ideal.span_singleton_pow,
      FractionalIdeal.coeIdeal_span_singleton, map_pow, zpow_natCast]
  rw [hsrc]
  set M := Submodule.map ((Algebra.trace K L).restrictScalars A)
    (Submodule.restrictScalars A
      ((spanSingleton B⁰ ((algebraMap B L πB) ^ (i : ℤ)) : FractionalIdeal B⁰ L) :
        Submodule B L)) with hM
  have hcrit := map_trace_spanSingleton_zpow_le_coeSubmodule_iff (A := A) (K := K) (L := L) hπA hπB
    hd he (i : ℤ)
  -- Containment at `j₀`, non-containment at `j₀ + 1`.
  have h1 : M ≤ coeSubmodule K (maximalIdeal A ^ j₀) := by
    rw [hM, hcrit]
    have : j₀ * e ≤ i + d := Nat.div_mul_le_self _ _
    exact_mod_cast this
  have h2 : ¬ (M ≤ coeSubmodule K (maximalIdeal A ^ (j₀ + 1))) := by
    rw [hM, hcrit]
    have hlt : i + d < (j₀ + 1) * e :=
      (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero he0)).mp (Nat.lt_succ_self _)
    intro hcon
    have : ((j₀ + 1) * e : ℕ) ≤ ((i + d : ℕ) : ℤ) := by push_cast at hcon ⊢; linarith
    omega
  -- The image lands inside `A`, so it comes from an ideal of `A`.
  have hle1 : M ≤ 1 := by
    refine h1.trans ?_
    rw [← IsLocalization.coeSubmodule_top K]
    exact Submodule.map_mono le_top
  have hrange : M ≤ LinearMap.range (Algebra.linearMap A K) := by
    rwa [← Submodule.one_eq_range]
  obtain ⟨I, hI⟩ : ∃ I : Ideal A, coeSubmodule K I = M :=
    ⟨Submodule.comap (Algebra.linearMap A K) M, Submodule.map_comap_eq_self hrange⟩
  have hIbot : I ≠ ⊥ := by
    rintro rfl
    exact h2 (by rw [← hI]; simp [coeSubmodule])
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hIbot hπA
  have hMk : M = coeSubmodule K (maximalIdeal A ^ k) := by
    rw [← hI, hk, (IsDiscreteValuationRing.irreducible_iff_uniformizer πA).mp hπA,
      Ideal.span_singleton_pow]
  rw [hMk] at h1 h2 ⊢
  have hkge : j₀ ≤ k := (coeSubmodule_maximalIdeal_pow_le_iff hπA k j₀).mp h1
  have hkle : k ≤ j₀ := by
    by_contra hcon
    push Not at hcon
    exact h2 ((coeSubmodule_maximalIdeal_pow_le_iff hπA k (j₀ + 1)).mpr hcon)
  rw [le_antisymm hkle hkge]

end AKLB

end DiscreteValuationTrace

/-! ### Instantiation at a pair of adic completions -/

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]
  [FiniteDimensional (v.adicCompletion K) (w.adicCompletion L)]

omit [Module.Finite K L] [Algebra.IsIntegral R S]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]
  [FiniteDimensional (v.adicCompletion K) (w.adicCompletion L)] in
/-- The algebra map `𝒪_{K_v} → 𝒪_{L_w}` is injective: it is the restriction of the injective ring
homomorphism `adicCompletionComap`. -/
theorem algebraMap_adicCompletionIntegers_injective : Function.Injective
    (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) := by
  intro a b hab
  apply Subtype.ext
  apply RingHom.injective (adicCompletionComap K L v w)
  rw [← coe_algebraMap_adicCompletionIntegers K L v w a,
    ← coe_algebraMap_adicCompletionIntegers K L v w b, hab]

/-- `𝒪_{L_w}` is a torsion-free `𝒪_{K_v}`-module: the algebra map between them is injective and
`𝒪_{L_w}` is a domain. -/
instance instIsTorsionFreeAdicCompletionIntegersAdicCompletionIntegers :
    Module.IsTorsionFree (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  .of_smul_eq_zero fun r x hrx => by
    rw [Algebra.smul_def] at hrx
    rcases mul_eq_zero.mp hrx with h | h
    · exact Or.inl (algebraMap_adicCompletionIntegers_injective K L v w (by rwa [map_zero]))
    · exact Or.inr h

omit [Algebra.IsIntegral R S] in
/-- **The trace image formula at a pair of adic completions.**
`Tr_{L_w/K_v}(𝔪_{L_w} ^ i) = 𝔪_{K_v} ^ ((i + d) / e)`, with `d` the different exponent and
`e = v.asIdeal.ramificationIdx' w.asIdeal`. -/
theorem map_trace_coeSubmodule_maximalIdeal_pow_adicCompletion {d : ℕ}
    (hd : differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      maximalIdeal (w.adicCompletionIntegers L) ^ d) (i : ℕ) :
    Submodule.map
        ((Algebra.trace (v.adicCompletion K) (w.adicCompletion L)).restrictScalars
          (v.adicCompletionIntegers K))
        (Submodule.restrictScalars (v.adicCompletionIntegers K)
          (coeSubmodule (w.adicCompletion L) (maximalIdeal (w.adicCompletionIntegers L) ^ i))) =
      coeSubmodule (v.adicCompletion K)
        (maximalIdeal (v.adicCompletionIntegers K) ^
          ((i + d) / v.asIdeal.ramificationIdx' w.asIdeal)) :=
  DiscreteValuationTrace.map_trace_coeSubmodule_maximalIdeal_pow
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot) hd
    (map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx' K L v w) i

end IsDedekindDomain.HeightOneSpectrum
