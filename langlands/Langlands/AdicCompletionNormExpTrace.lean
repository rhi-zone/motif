import Langlands.AdicCompletionIntegralClosure
import Langlands.AdicCompletionTraceBound
import Langlands.NonarchimedeanExponentialRingHom

/-!
# The norm/trace compatibility formula `N_{L_w/K_v}(exp x) = exp(Tr_{L_w/K_v} x)`

The norm/trace compatibility formula in the wild ramification case, proved here **for a Galois
extension of completions**.

## Route

The classical one — conjugates — made available by three pieces that had to be built first:

1. `NonarchimedeanExponential.exp_add` and `.exp_sum`
   (`Langlands.NonarchimedeanExponentialAdd`, `Langlands.NonarchimedeanExponentialRingHom`):
   `exp` of a finite sum is the product of the `exp`s. Without this the formula is unprovable by
   any route.
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

omit [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L] [IsFractionRing S L] [Algebra R S]
  [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [Module.Finite K L]
  [Algebra.IsIntegral R S] [Module.IsTorsionFree R S] [CharZero L] [CharZero K] hp in
/-- **`convergenceRadius (v.adicCompletion K) p` is a literal power of `2` whenever `Valued.v (p :
v.adicCompletion K) = WithZero.exp (-k)` for some integer `k`.** `convergenceRadius F p = ‖(p:F)‖ ^
((p-1)⁻¹:ℝ)`; `norm_eq_two_zpow_of_valued_eq_exp` (`Langlands.NormMap`) evaluates `‖(p:K_v)‖` to the
literal `2 ^ (-k)` (a real `zpow`), and reassociating the `rpow` exponent against it
(`Real.rpow_intCast`, `Real.rpow_mul`) lands on the single `rpow` `2 ^ (-(k:ℝ) * ((p:ℝ)-1)⁻¹)`. Proved
in this `NumberField`-free file (no fresh `‖·‖`/`convergenceRadius` type ascription at a
`NumberField`-visible call site) to avoid triggering the `NormedField (v.adicCompletion K)`
instance diamond. -/
theorem convergenceRadius_eq_rpow_of_valued_natCast_eq_exp {k : ℤ}
    (h : Valued.v (((p : ℕ) : v.adicCompletion K)) = WithZero.exp (-k)) :
    convergenceRadius (v.adicCompletion K) p = (2 : ℝ) ^ (-(k : ℝ) * ((p : ℝ) - 1)⁻¹) := by
  unfold convergenceRadius
  rw [norm_eq_two_zpow_of_valued_eq_exp (v := v) h, ← Real.rpow_intCast (2 : ℝ) (-k),
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  push_cast
  ring_nf

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

omit [Algebra.IsIntegral R S] [Module.Finite K L] [CharZero K] [CharZero L] hp in
/-- **`convergenceRadius` scales by the exact ramification index across `algebraMap K_v L_w`.**
`convergenceRadius F p = ‖(p : F)‖ ^ ((p - 1)⁻¹ : ℝ)`, and `(p : w.adicCompletion L) = algebraMap
(p : v.adicCompletion K)` (`map_natCast`), so `norm_algebraMap_pow_eq` gives `‖(p : L_w)‖ = ‖(p :
K_v)‖ ^ e` EXACTLY. Raising both sides to the `(p - 1)⁻¹` power and reassociating the exponents
(`Real.rpow_natCast`, `Real.rpow_mul`, `norm_nonneg`) turns this into `convergenceRadius L_w p =
(convergenceRadius K_v p) ^ e` — an exact equation between the two convergence radii, not merely an
order comparison. This is what lets the `algebraMap`-side threshold of
`exists_maximalIdeal_pow_norm_exp_eq_exp_trace` reuse the `K_v`-side trace threshold directly. -/
theorem convergenceRadius_eq_pow :
    convergenceRadius (w.adicCompletion L) p =
      (convergenceRadius (v.adicCompletion K) p) ^ (v.asIdeal.ramificationIdx' w.asIdeal) := by
  have hpL : ((p : ℕ) : w.adicCompletion L) =
      adicCompletionComap K L v w ((p : ℕ) : v.adicCompletion K) := by
    rw [map_natCast]
  unfold convergenceRadius
  rw [hpL, norm_algebraMap_pow_eq, ← Real.rpow_natCast (‖((p : ℕ) : v.adicCompletion K)‖)
      (v.asIdeal.ramificationIdx' w.asIdeal), ← Real.rpow_mul (norm_nonneg _),
    ← Real.rpow_natCast (‖((p : ℕ) : v.adicCompletion K)‖ ^ (((p : ℝ) - 1)⁻¹))
      (v.asIdeal.ramificationIdx' w.asIdeal),
    ← Real.rpow_mul (norm_nonneg _), mul_comm]

omit [Algebra.IsIntegral R S] in
/-- **The norm/trace compatibility formula on a filtration level.** Some `i₀` has

`N_{L_w/K_v}(exp_{L_w} x) = exp_{K_v}(Tr_{L_w/K_v} x)`

for *every* `x ∈ 𝔪_{L_w}^i` with `i ≥ i₀` — no further hypotheses on `x`.

`i₀ := max i1 i3` is genuinely closed-form in terms of the two remaining existential witnesses:

* `i1` (`exists_maximalIdeal_pow_norm_lt`) supplies both `hx` directly and, via
  `restrictAdicCompletionIntegers_mem_maximalIdeal_pow` (`Langlands.AdicCompletionIntegralClosure`
  — Galois conjugation preserves `𝔪_{L_w}^i` EXACTLY, for the same `i`), `hσ` for every conjugate at
  the SAME threshold `i1` — no per-`σ` threshold or `Finset.sup` is needed at all, unlike the
  ε/δ-continuity route this replaces.
* `i3` (`exists_maximalIdeal_pow_norm_trace_lt`) supplies `htrK` directly, and (via
  `norm_algebraMap_pow_eq` and `convergenceRadius_eq_pow`, both EXACT ramification-index-`e`
  equations) `htrL` at that SAME threshold `i3` too: `‖Tr x‖ < convergenceRadius K_v p` implies
  `‖algebraMap (Tr x)‖ = ‖Tr x‖ ^ e < (convergenceRadius K_v p) ^ e = convergenceRadius L_w p`.

Both conveniences replace what would otherwise require a separate ε/δ-continuity argument per
hypothesis. -/
theorem exists_maximalIdeal_pow_norm_exp_eq_exp_trace
    [IsGalois (v.adicCompletion K) (w.adicCompletion L)]
    (hnormK : ‖(p : v.adicCompletion K)‖ < 1) (hnormL : ‖(p : w.adicCompletion L)‖ < 1) :
    ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x : w.adicCompletionIntegers L,
      x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i →
        Algebra.norm (v.adicCompletion K) (exp hnormL (x : w.adicCompletion L))
          = exp hnormK (Algebra.trace (v.adicCompletion K) (w.adicCompletion L)
              (x : w.adicCompletion L)) := by
  have hcrL : (0 : ℝ) < convergenceRadius (w.adicCompletion L) p :=
    Real.rpow_pos_of_pos norm_natCast_pos _
  have hcrK : (0 : ℝ) < convergenceRadius (v.adicCompletion K) p :=
    Real.rpow_pos_of_pos norm_natCast_pos _
  obtain ⟨i1, h1⟩ := exists_maximalIdeal_pow_norm_lt (F := L) w hcrL
  obtain ⟨i3, h3⟩ := exists_maximalIdeal_pow_norm_trace_lt K L v w hcrK
  refine ⟨max i1 i3, fun i hi x hx => ?_⟩
  have hi1 : i1 ≤ i := le_trans (le_max_left _ _) hi
  have hi3 : i3 ≤ i := le_trans (le_max_right _ _) hi
  refine norm_exp_eq_exp_trace K L v w p hnormK hnormL (h1 i hi1 x hx) (fun σ => ?_)
    (h3 i hi3 x hx) ?_
  · have hmem := restrictAdicCompletionIntegers_mem_maximalIdeal_pow K L v w σ hx
    have := h1 i hi1 _ hmem
    rwa [coe_restrictAdicCompletionIntegers] at this
  · have htrK := h3 i hi3 x hx
    rw [show (algebraMap (v.adicCompletion K) (w.adicCompletion L))
        = adicCompletionComap K L v w from rfl, norm_algebraMap_pow_eq,
      convergenceRadius_eq_pow K L v w p]
    exact pow_lt_pow_left₀ htrK (norm_nonneg _)
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)

omit [Algebra.IsIntegral R S] in
/-- **The concrete-witness core of `exists_maximalIdeal_pow_norm_exp_eq_exp_trace`.** Same
conclusion shape, at `i₀ := max i1 i3`, but taking the two convergence-domain memberships `h1`/`h3`
(what `exists_maximalIdeal_pow_norm_lt`/`exists_maximalIdeal_pow_norm_trace_lt` produce internally)
as EXPLICIT hypotheses rather than deriving them existentially. Exactly the piece a concrete
instance needs to supply literal `i1`/`i3` (e.g. via `forall_maximalIdeal_pow_norm_lt`/
`forall_maximalIdeal_pow_norm_trace_le`, both `AdicCompletionTraceBound`/
`NonarchimedeanExponentialAdicCompletion`) and close `i₀` to a numeral. -/
theorem forall_maximalIdeal_pow_norm_exp_eq_exp_trace
    [IsGalois (v.adicCompletion K) (w.adicCompletion L)]
    (hnormK : ‖(p : v.adicCompletion K)‖ < 1) (hnormL : ‖(p : w.adicCompletion L)‖ < 1)
    {i1 i3 : ℕ}
    (h1 : ∀ i ≥ i1, ∀ x : w.adicCompletionIntegers L,
      x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i →
        ‖(x : w.adicCompletion L)‖ < convergenceRadius (w.adicCompletion L) p)
    (h3 : ∀ i ≥ i3, ∀ x : w.adicCompletionIntegers L,
      x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i →
        ‖Algebra.trace (v.adicCompletion K) (w.adicCompletion L) (x : w.adicCompletion L)‖ <
          convergenceRadius (v.adicCompletion K) p) :
    ∀ i ≥ max i1 i3, ∀ x : w.adicCompletionIntegers L,
      x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i →
        Algebra.norm (v.adicCompletion K) (exp hnormL (x : w.adicCompletion L))
          = exp hnormK (Algebra.trace (v.adicCompletion K) (w.adicCompletion L)
              (x : w.adicCompletion L)) := by
  intro i hi x hx
  have hi1 : i1 ≤ i := le_trans (le_max_left _ _) hi
  have hi3 : i3 ≤ i := le_trans (le_max_right _ _) hi
  refine norm_exp_eq_exp_trace K L v w p hnormK hnormL (h1 i hi1 x hx) (fun σ => ?_)
    (h3 i hi3 x hx) ?_
  · have hmem := restrictAdicCompletionIntegers_mem_maximalIdeal_pow K L v w σ hx
    have := h1 i hi1 _ hmem
    rwa [coe_restrictAdicCompletionIntegers] at this
  · have htrK := h3 i hi3 x hx
    rw [show (algebraMap (v.adicCompletion K) (w.adicCompletion L))
        = adicCompletionComap K L v w from rfl, norm_algebraMap_pow_eq,
      convergenceRadius_eq_pow K L v w p]
    exact pow_lt_pow_left₀ htrK (norm_nonneg _)
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)

end IsDedekindDomain.HeightOneSpectrum

end
