import Langlands.AdicCompletionTraceBound
import Langlands.NonarchimedeanExponentialRingHom

/-!
# The norm/trace compatibility formula `N_{L_w/K_v}(exp x) = exp(Tr_{L_w/K_v} x)`

The wild-case payoff of this repo's exp/log thread (ROADMAP.md Phase 2b, item 5 of the wild-case
list), proved here **for a Galois extension of completions**.

## Route

The classical one — conjugates — made available by three pieces that had to be built first:

1. `NonarchimedeanExponential.exp_add` and `.exp_sum`
   (`Langlands.NonarchimedeanExponentialAdd`, `Langlands.NonarchimedeanExponentialRingHom`):
   `exp` of a finite sum is the product of the `exp`s. Without this the formula is unprovable by
   any route; it was unattempted in every prior pass.
2. `NonarchimedeanExponential.map_exp`: a *continuous* ring homomorphism commutes with `exp`. The
   `K_v`-automorphisms of `L_w` are continuous for free — not by any isometry or
   uniqueness-of-valuation-extension argument, but because a linear map on a finite-dimensional
   Hausdorff topological vector space over a complete field is continuous
   (`LinearMap.continuous_of_finiteDimensional`), and `Langlands.NormMap` already supplies
   `ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)` and
   `Module.Finite (v.adicCompletion K) (w.adicCompletion L)`.
3. `Langlands.AdicCompletionTraceBound`: `Tr_{L_w/K_v}` maps deep enough filtration levels of
   `L_w` into any prescribed neighbourhood of `0` in `K_v` — in particular into `exp_{K_v}`'s
   convergence domain, which is what makes the right-hand side defined at all.

With those, `Algebra.norm_eq_prod_automorphisms` and `Algebra.trace_eq_sum_automorphisms` turn the
identity into `∏_σ σ(exp x) = ∏_σ exp(σ x) = exp(∑_σ σ x)`, and injectivity of
`algebraMap K_v L_w` transports it back down.

Note what is *not* needed: no `spectralNorm`, no "all conjugates have the same absolute value", and
no `NormedAlgebra K_v L_w` — the last of which is in fact **false** for this repo's normalizations
(see `Langlands.AdicCompletionTraceBound`'s docstring). Continuity replaces isometry throughout.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.continuous_algEquiv` : every `K_v`-algebra automorphism of
  `L_w` is continuous.
* `IsDedekindDomain.HeightOneSpectrum.norm_exp_eq_exp_trace` : the formula, with the four
  convergence-domain memberships it consumes as explicit hypotheses.
* `IsDedekindDomain.HeightOneSpectrum.exists_maximalIdeal_pow_norm_exp_eq_exp_trace` : the formula
  on a filtration level — some `i₀` has it hold for every `x ∈ 𝔪_{L_w}^i`, `i ≥ i₀`, with no
  hypotheses on `x` beyond that membership.

## Scope

`IsGalois (v.adicCompletion K) (w.adicCompletion L)` is assumed. Removing it means running the
argument in a normal closure of `L_w / K_v`, which needs the exponential — and a norm — on that
closure; nothing in this repo provides either. The Galois case is the one the wild-case norm-group
index argument uses.
-/

noncomputable section

open IsDedekindDomain IsLocalRing NonarchimedeanExponential Algebra

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

omit [Algebra.IsIntegral R S] in
/-- **Every `K_v`-algebra automorphism of `L_w` is continuous.** `L_w` is a finite-dimensional
Hausdorff topological `K_v`-module with continuous scalar action (`Langlands.NormMap`) and `K_v` is
complete, so *every* `K_v`-linear map out of `L_w` is continuous
(`LinearMap.continuous_of_finiteDimensional`). No isometry or valuation-extension uniqueness is
involved. -/
theorem continuous_algEquiv
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) : Continuous σ :=
  σ.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional

variable [CharZero K] [CharZero L] (p : ℕ) [hp : Fact p.Prime]

omit [Algebra.IsIntegral R S] in
/-- **The norm/trace compatibility formula.** For `x : L_w` such that `x`, all its conjugates, the
trace `Tr_{L_w/K_v}(x)`, and that trace's image in `L_w` lie in the relevant convergence domains,

`N_{L_w/K_v}(exp_{L_w} x) = exp_{K_v}(Tr_{L_w/K_v} x)`.

Applying the injective `algebraMap K_v L_w` to both sides, the left becomes `∏_σ σ (exp x)`
(`Algebra.norm_eq_prod_automorphisms`), which is `∏_σ exp (σ x)` because each `σ` is a continuous
ring homomorphism (`continuous_algEquiv`, `map_exp`), which is `exp (∑_σ σ x)` (`exp_sum`), which
is `exp (algebraMap (Tr x))` (`Algebra.trace_eq_sum_automorphisms`), which is the image of the
right-hand side (`map_exp` again, for `algebraMap K_v L_w`). -/
theorem norm_exp_eq_exp_trace [IsGalois (v.adicCompletion K) (w.adicCompletion L)]
    (hnormK : ‖(p : v.adicCompletion K)‖ < 1) (hnormL : ‖(p : w.adicCompletion L)‖ < 1)
    {x : w.adicCompletion L} (hx : ‖x‖ < convergenceRadius (w.adicCompletion L) p)
    (hσ : ∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      ‖σ x‖ < convergenceRadius (w.adicCompletion L) p)
    (htrK : ‖Algebra.trace (v.adicCompletion K) (w.adicCompletion L) x‖ <
      convergenceRadius (v.adicCompletion K) p)
    (htrL : ‖algebraMap (v.adicCompletion K) (w.adicCompletion L)
        (Algebra.trace (v.adicCompletion K) (w.adicCompletion L) x)‖ <
      convergenceRadius (w.adicCompletion L) p) :
    Algebra.norm (v.adicCompletion K) (exp hnormL x)
      = exp hnormK (Algebra.trace (v.adicCompletion K) (w.adicCompletion L) x) := by
  apply FaithfulSMul.algebraMap_injective (v.adicCompletion K) (w.adicCompletion L)
  rw [Algebra.norm_eq_prod_automorphisms]
  have hconj : ∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      σ (exp hnormL x) = exp hnormL (σ x) := fun σ =>
    map_exp hnormL hnormL (σ : w.adicCompletion L ≃+* w.adicCompletion L).toRingHom
      (continuous_algEquiv K L v w σ) hx (hσ σ)
  rw [Finset.prod_congr rfl fun σ _ => hconj σ,
    ← exp_sum hnormL fun σ (_ : σ ∈ Finset.univ) => hσ σ,
    ← trace_eq_sum_automorphisms]
  exact (map_exp hnormK hnormL (algebraMap (v.adicCompletion K) (w.adicCompletion L))
    (continuous_adicCompletionComap K L v w) htrK htrL).symm

omit [Algebra.IsIntegral R S] [Module.IsTorsionFree R S] [CharZero K] [CharZero L] in
/-- Continuity at `0`, in ε/δ form: a continuous map sending `0` to `0` pulls any ball around `0`
back to a ball around `0`. -/
private theorem exists_delta_of_continuous {M N : Type*} [SeminormedAddCommGroup M]
    [SeminormedAddCommGroup N] (f : M → N) (hf : Continuous f) (h0 : f 0 = 0) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ z : M, ‖z‖ < δ → ‖f z‖ < ε := by
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuous_iff.mp hf 0 ε hε
  refine ⟨δ, hδ0, fun z hz => ?_⟩
  have := hδ z (by simpa [dist_eq_norm] using hz)
  simpa [h0, dist_eq_norm] using this

omit [Algebra.IsIntegral R S] in
/-- **The norm/trace compatibility formula on a filtration level.** Some `i₀` has

`N_{L_w/K_v}(exp_{L_w} x) = exp_{K_v}(Tr_{L_w/K_v} x)`

for *every* `x ∈ 𝔪_{L_w}^i` with `i ≥ i₀` — no further hypotheses on `x`.

All four convergence-domain hypotheses of `norm_exp_eq_exp_trace` are produced by pairing
`exists_maximalIdeal_pow_norm_lt` / `exists_maximalIdeal_pow_norm_trace_lt` (which reach any
prescribed accuracy at a deep enough level) with continuity at `0` of the maps involved: the
finitely many conjugations `σ` (`continuous_algEquiv`) and `algebraMap K_v L_w`
(`continuous_adicCompletionComap`). Finiteness of `Gal(L_w/K_v)` is what lets the per-`σ`
thresholds be combined into one. -/
theorem exists_maximalIdeal_pow_norm_exp_eq_exp_trace
    [IsGalois (v.adicCompletion K) (w.adicCompletion L)]
    (hnormK : ‖(p : v.adicCompletion K)‖ < 1) (hnormL : ‖(p : w.adicCompletion L)‖ < 1) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x : w.adicCompletionIntegers L,
      x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i →
        Algebra.norm (v.adicCompletion K) (exp hnormL (x : w.adicCompletion L))
          = exp hnormK (Algebra.trace (v.adicCompletion K) (w.adicCompletion L)
              (x : w.adicCompletion L)) := by
  classical
  have hcrL : (0 : ℝ) < convergenceRadius (w.adicCompletion L) p :=
    Real.rpow_pos_of_pos norm_natCast_pos _
  have hcrK : (0 : ℝ) < convergenceRadius (v.adicCompletion K) p :=
    Real.rpow_pos_of_pos norm_natCast_pos _
  obtain ⟨i1, h1⟩ := exists_maximalIdeal_pow_norm_lt (F := L) w hcrL
  have hgal : ∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
      ∃ i : ℕ, ∀ j ≥ i, ∀ x : w.adicCompletionIntegers L,
        x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ j →
          ‖σ (x : w.adicCompletion L)‖ < convergenceRadius (w.adicCompletion L) p := by
    intro σ
    obtain ⟨δ, hδ0, hδ⟩ := exists_delta_of_continuous (fun z => σ z)
      (continuous_algEquiv K L v w σ) (map_zero σ) hcrL
    obtain ⟨i, hi⟩ := exists_maximalIdeal_pow_norm_lt (F := L) w hδ0
    exact ⟨i, fun j hj x hx => hδ _ (hi j hj x hx)⟩
  choose iσ hiσ using hgal
  obtain ⟨i3, h3⟩ := exists_maximalIdeal_pow_norm_trace_lt K L v w hcrK
  obtain ⟨δ, hδ0, hδ⟩ := exists_delta_of_continuous
    (fun a => algebraMap (v.adicCompletion K) (w.adicCompletion L) a)
    (continuous_adicCompletionComap K L v w) (map_zero _) hcrL
  obtain ⟨i4, h4⟩ := exists_maximalIdeal_pow_norm_trace_lt K L v w hδ0
  refine ⟨max (max i1 (Finset.univ.sup iσ)) (max i3 i4), fun i hi x hx => ?_⟩
  have hi1 : i1 ≤ i := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hi
  have hi2 : Finset.univ.sup iσ ≤ i :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hi
  have hi3 : i3 ≤ i := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hi
  have hi4 : i4 ≤ i := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hi
  exact norm_exp_eq_exp_trace K L v w p hnormK hnormL (h1 i hi1 x hx)
    (fun σ => hiσ σ i (le_trans (Finset.le_sup (Finset.mem_univ σ)) hi2) x hx)
    (h3 i hi3 x hx) (hδ _ (h4 i hi4 x hx))

end IsDedekindDomain.HeightOneSpectrum

end
