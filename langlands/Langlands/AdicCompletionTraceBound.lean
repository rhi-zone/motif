import Langlands.NonarchimedeanExponentialExtension

/-!
# A nonarchimedean bound on the trace map of an extension of adic completions

Stating the wild-case norm/trace compatibility formula `N_{L_w/K_v}(exp x) = exp(Tr_{L_w/K_v} x)`
requires knowing that `Tr_{L_w/K_v}(x)` lands in `exp_{K_v}`'s convergence domain whenever `x` lies
in `exp_{L_w}`'s. Mathlib has no lemma connecting `Algebra.trace` or `Algebra.norm` to any nonarchimedean norm (a
loogle search for `Algebra.trace` together with `Norm.norm` returns no declarations).

This file closes that gap. The route deliberately avoids the analytic "all conjugates have the same
absolute value" argument (which would go through `spectralNorm`): that argument needs
`w.adicCompletion L` to be a `NormedAlgebra` over `v.adicCompletion K`, which is **false** for this
repo's normalizations — `Langlands.NormMap`'s `instRankOneValuedAdicCompletion` picks the same
rank-one base `2` at every place, so `‖algebraMap K_v L_w a‖ = ‖a‖ ^ e` with `e` the ramification
index (`valuation_algebraMap_pow_eq`), and `norm_smul_le` fails as soon as `e > 1`.

What is used instead is integrality, which is normalization-free:

1. `x ∈ w.adicCompletionIntegers L` is integral over `v.adicCompletionIntegers K`
   (`isIntegral_of_mem_of_comap_eq`, already in `Langlands.NormMap`), hence so is its trace
   (`Algebra.isIntegral_trace`), and a valuation subring is integrally closed in its fraction
   field — so `Tr(x) ∈ v.adicCompletionIntegers K`.
2. Scaling by an element of the base: if `‖x‖ ≤ ‖algebraMap a‖` then `x / algebraMap a` is an
   integer of `L_w`, and `Tr` is `K_v`-linear, so `‖Tr(x)‖ ≤ ‖a‖`.

Step 2 is what makes the bound quantitative, and it is *not* sharp: the sharp classical bound is
`‖Tr(x)‖_{K_v} ≤ ‖x‖_{L_w} ^ (1/e)`, whereas scaling by base-field elements only reaches the value
group of `K_v`, losing up to a factor of `‖π_K‖`. That loss is irrelevant for the intended use —
`exp`'s convergence domain is specified existentially (`∃ i₀, ∀ i ≥ i₀, …`), so a bound that tends
to `0` as the filtration level grows is all that is needed.

## Main results

* `ValuationSubring.trace_mem_of_isIntegral` : general — for `L / K` a finite extension of fields
  and `O` a valuation subring of `K`, an element of `L` integral over `O` has `Algebra.trace K L`
  in `O`.
* `IsDedekindDomain.HeightOneSpectrum.trace_mem_adicCompletionIntegers` : `Tr_{L_w/K_v}` maps
  `w.adicCompletionIntegers L` into `v.adicCompletionIntegers K`.
* `IsDedekindDomain.HeightOneSpectrum.norm_trace_le` : **the trace-norm bound.**
  `‖x‖ ≤ ‖algebraMap K_v L_w a‖ → ‖Tr_{L_w/K_v}(x)‖ ≤ ‖a‖`.
* `IsDedekindDomain.HeightOneSpectrum.exists_maximalIdeal_pow_norm_trace_lt_convergenceRadius` /
  `..._lt_logConvergenceRadius` : the payoff — some `i₀` has `Tr_{L_w/K_v}(𝔪_{L_w}^i)` inside
  `exp_{K_v}`'s (resp. `log_{K_v}`'s) convergence domain for every `i ≥ i₀`.

## What this does *not* give

The compatibility formula itself. With this file, `N_{L_w/K_v}(exp_{L_w} x) = exp_{K_v}(Tr x)` is
finally *stateable* (both sides are defined on a common domain). Proving it additionally needs the
group-homomorphism law `exp (x + y) = exp x * exp y`, which no file in this repo currently
provides.
-/

noncomputable section

open IsDedekindDomain IsLocalRing NonarchimedeanExponential

namespace ValuationSubring

/-- **The trace of an integral element lies in the valuation subring.** For `L / K` a finite
extension of fields and `O` a valuation subring of `K`, an element `x : L` integral over `O` has
`Algebra.trace K L x ∈ O`: the trace of an integral element is integral (`Algebra.isIntegral_trace`)
and a valuation subring is integrally closed in its fraction field. -/
theorem trace_mem_of_isIntegral {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (O : ValuationSubring K) [Algebra O L] [IsScalarTower O K L] {x : L}
    (hx : IsIntegral O x) : Algebra.trace K L x ∈ O := by
  obtain ⟨y, hy⟩ :=
    IsIntegrallyClosedIn.algebraMap_eq_of_integral
      (Algebra.isIntegral_trace (R := O) (L := K) (F := L) hx)
  exact hy ▸ y.2

end ValuationSubring

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

omit [Algebra.IsIntegral R S] in
/-- **`Tr_{L_w/K_v}` maps the integers of `L_w` into the integers of `K_v`.** Every element of
`w.adicCompletionIntegers L` is integral over `v.adicCompletionIntegers K`
(`isIntegral_of_mem_of_comap_eq`, applied through `adicCompletionIntegers_comap_eq` and
`valuation_valuationSubring_eq_adicCompletionIntegers`), and `trace_mem_of_isIntegral` finishes. -/
theorem trace_mem_adicCompletionIntegers {x : w.adicCompletion L}
    (hx : x ∈ w.adicCompletionIntegers L) :
    Algebra.trace (v.adicCompletion K) (w.adicCompletion L) x ∈ v.adicCompletionIntegers K := by
  have hbridge := valuation_valuationSubring_eq_adicCompletionIntegers K v
  have hcomap : (w.adicCompletionIntegers L).comap (adicCompletionComap K L v w)
      = (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring := by
    rw [hbridge]; exact adicCompletionIntegers_comap_eq K L v w
  have h1 : IsIntegral (v.adicCompletionIntegers K) x := by
    have := isIntegral_of_mem_of_comap_eq (w.adicCompletionIntegers L) hcomap (x := x) hx
    rwa [hbridge] at this
  exact ValuationSubring.trace_mem_of_isIntegral _ h1

omit [Algebra.IsIntegral R S] in
/-- **The trace-norm bound.** If `x : L_w` is bounded in norm by the image of `a : K_v`, then
`Tr_{L_w/K_v}(x)` is bounded in norm by `a` itself.

For `a = 0` the hypothesis forces `x = 0`. Otherwise `x / algebraMap a` has norm `≤ 1`, hence is an
integer of `L_w`, hence has trace an integer of `K_v` (`trace_mem_adicCompletionIntegers`); since
`Tr` is `K_v`-linear and `x = a • (x / algebraMap a)`, the claim follows from multiplicativity of
the norm.

Note the two norms live at *different* normalizations: `‖·‖` on the left is `L_w`'s, on the right
`K_v`'s, and `‖algebraMap a‖ = ‖a‖ ^ e`. This is why the statement is phrased through
`algebraMap` rather than as a bare inequality between `‖Tr x‖` and `‖x‖`. -/
theorem norm_trace_le {a : v.adicCompletion K} {x : w.adicCompletion L}
    (hx : ‖x‖ ≤ ‖algebraMap (v.adicCompletion K) (w.adicCompletion L) a‖) :
    ‖Algebra.trace (v.adicCompletion K) (w.adicCompletion L) x‖ ≤ ‖a‖ := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [map_zero, norm_zero] at hx ⊢
    have : x = 0 := norm_le_zero_iff.mp hx
    simp [this]
  have hb : algebraMap (v.adicCompletion K) (w.adicCompletion L) a ≠ 0 :=
    (map_ne_zero_iff (algebraMap (v.adicCompletion K) (w.adicCompletion L))
      (RingHom.injective (algebraMap (v.adicCompletion K) (w.adicCompletion L)))).mpr ha
  set b := algebraMap (v.adicCompletion K) (w.adicCompletion L) a with hbdef
  have hb0 : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hy : ‖x / b‖ ≤ 1 := by rw [norm_div, div_le_one hb0]; exact hx
  have hymem : x / b ∈ w.adicCompletionIntegers L :=
    (mem_adicCompletionIntegers_iff_norm_le_one w _).mpr hy
  have htr := trace_mem_adicCompletionIntegers K L v w hymem
  have htrnorm : ‖Algebra.trace (v.adicCompletion K) (w.adicCompletion L) (x / b)‖ ≤ 1 :=
    (mem_adicCompletionIntegers_iff_norm_le_one v _).mp htr
  have hxeq : x = a • (x / b) := by
    rw [Algebra.smul_def, ← hbdef]
    field_simp
  rw [hxeq, map_smul, smul_eq_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) htrnorm

omit [Algebra.IsIntegral R S] in
/-- **The quantitative payoff, at an arbitrary target accuracy.** For any `ε > 0`, all sufficiently
deep levels of `L_w`'s filtration have `‖Tr_{L_w/K_v}(x)‖ < ε`.

Pick `c : K_v` with `0 < ‖c‖ < 1` (`NormedField.exists_norm_lt_one`) and `n` with `‖c‖ ^ n < ε`;
then `b := algebraMap (cⁿ)` is a nonzero element of `L_w`, and a uniformizer `π_L` of
`w.adicCompletionIntegers L` has `‖π_L‖ ^ i ≤ ‖b‖` for all large `i`. For such `i`, every
`x ∈ 𝔪_{L_w}^i` has `‖x‖ ≤ ‖π_L‖ ^ i ≤ ‖b‖`, so `norm_trace_le` gives `‖Tr x‖ ≤ ‖c‖ ^ n < ε`.

No residue-characteristic or characteristic-zero hypothesis is used: the bound is purely metric. -/
theorem exists_maximalIdeal_pow_norm_trace_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x : w.adicCompletionIntegers L,
      x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i →
        ‖Algebra.trace (v.adicCompletion K) (w.adicCompletion L) (x : w.adicCompletion L)‖ < ε := by
  obtain ⟨c, hc0, hcnorm⟩ := NormedField.exists_norm_lt_one (v.adicCompletion K)
  obtain ⟨πL, hπLnorm, hπL⟩ := exists_uniformizer w (F := L)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hcnorm
  set a : v.adicCompletion K := c ^ n with hadef
  have ha0 : a ≠ 0 := pow_ne_zero _ (norm_pos_iff.mp hc0)
  set b := algebraMap (v.adicCompletion K) (w.adicCompletion L) a with hbdef
  have hb0 : (0 : ℝ) < ‖b‖ :=
    norm_pos_iff.mpr ((map_ne_zero_iff (algebraMap (v.adicCompletion K) (w.adicCompletion L))
      (RingHom.injective (algebraMap (v.adicCompletion K) (w.adicCompletion L)))).mpr ha0)
  obtain ⟨i₀, hi₀⟩ := exists_pow_lt_of_lt_one hb0 hπLnorm
  refine ⟨i₀, fun i hi x hx => ?_⟩
  have hxnorm : ‖(x : w.adicCompletion L)‖ ≤ ‖b‖ := by
    refine le_trans (norm_le_pow_of_mem_maximalIdeal_pow (w.adicCompletionIntegers L)
      (mem_adicCompletionIntegers_iff_norm_le_one w) hπL hx) ?_
    exact le_trans (pow_le_pow_of_le_one (norm_nonneg _) hπLnorm.le hi) hi₀.le
  refine lt_of_le_of_lt (norm_trace_le K L v w hxnorm) ?_
  rw [hadef, norm_pow]
  exact hn

omit [Algebra.IsIntegral R S] in
/-- **The concrete-witness core of `exists_maximalIdeal_pow_norm_trace_lt`.** Same conclusion shape
(a uniform trace-norm bound on a filtration level), but taking the witnessing data — a nonzero `a :
K_v`, a uniformizer `πL` of `L_w`, and an explicit `i₀` with `‖πL‖ ^ i₀ ≤ ‖algebraMap a‖` — as
EXPLICIT hypotheses rather than deriving them via `exists_pow_lt_of_lt_one`/`NormedField.exists_norm_lt_one`.
This is exactly the reusable piece a concrete instance needs to close `i₀` to a literal numeral:
supply a concrete uniformizer for `a` and a concrete numeral for `i₀`, and this lemma produces the
bound directly, with no existential anywhere. -/
theorem forall_maximalIdeal_pow_norm_trace_le {a : v.adicCompletion K}
    {πL : w.adicCompletionIntegers L} (hπLnorm : ‖(πL : w.adicCompletion L)‖ < 1)
    (hπL : maximalIdeal (w.adicCompletionIntegers L) =
      Ideal.span ({πL} : Set (w.adicCompletionIntegers L)))
    {i₀ : ℕ}
    (hi₀ : ‖(πL : w.adicCompletion L)‖ ^ i₀ ≤
      ‖algebraMap (v.adicCompletion K) (w.adicCompletion L) a‖) :
    ∀ i ≥ i₀, ∀ x : w.adicCompletionIntegers L, x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i →
      ‖Algebra.trace (v.adicCompletion K) (w.adicCompletion L) (x : w.adicCompletion L)‖ ≤ ‖a‖ := by
  intro i hi x hx
  have hxnorm : ‖(x : w.adicCompletion L)‖ ≤
      ‖algebraMap (v.adicCompletion K) (w.adicCompletion L) a‖ := by
    refine le_trans (norm_le_pow_of_mem_maximalIdeal_pow (w.adicCompletionIntegers L)
      (mem_adicCompletionIntegers_iff_norm_le_one w) hπL hx) ?_
    exact le_trans (pow_le_pow_of_le_one (norm_nonneg _) hπLnorm.le hi) hi₀
  exact norm_trace_le K L v w hxnorm

variable [CharZero K] (p : ℕ) [hp : Fact p.Prime]

omit [Algebra.IsIntegral R S] in
/-- The trace maps a high-enough filtration level of `L_w` into `exp_{K_v}`'s convergence domain —
`exists_maximalIdeal_pow_norm_trace_lt` at `ε := convergenceRadius K_v p`. -/
theorem exists_maximalIdeal_pow_norm_trace_lt_convergenceRadius :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x : w.adicCompletionIntegers L,
      x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i →
        ‖Algebra.trace (v.adicCompletion K) (w.adicCompletion L) (x : w.adicCompletion L)‖ <
          convergenceRadius (v.adicCompletion K) p :=
  exists_maximalIdeal_pow_norm_trace_lt K L v w (Real.rpow_pos_of_pos norm_natCast_pos _)

omit [Algebra.IsIntegral R S] in
/-- The `log`-domain analogue of
`exists_maximalIdeal_pow_norm_trace_lt_convergenceRadius`, at the (more conservative) threshold
`logConvergenceRadius K_v p = ‖p‖`. -/
theorem exists_maximalIdeal_pow_norm_trace_lt_logConvergenceRadius :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x : w.adicCompletionIntegers L,
      x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i →
        ‖Algebra.trace (v.adicCompletion K) (w.adicCompletion L) (x : w.adicCompletion L)‖ <
          logConvergenceRadius (v.adicCompletion K) p :=
  exists_maximalIdeal_pow_norm_trace_lt K L v w norm_natCast_pos

end IsDedekindDomain.HeightOneSpectrum

end
