/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.TotallyRamifiedCyclotomicConcreteExample
import Langlands.AdicCompletionTraceSurjectivity
import Langlands.NakayamaMonogenic
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# The different exponent of `ℚ_3(ζ_9) / ℚ_3(ζ_3)` is `6`

`Langlands.AdicCompletionTraceSurjectivity` and `Langlands.AdicCompletionNormGroupImage` both carry
the different exponent `d` as an *explicit hypothesis* `differentIdeal A B = maximalIdeal B ^ d`,
because `Mathlib`'s `differentIdeal_ne_bot` only produces `d`'s existence, never its value. This
file computes `d` outright for the concrete mixed-characteristic wild Galois instance built in
`Langlands.TotallyRamifiedCyclotomicConcreteExample` (`K = ℚ(ζ_3) ⊆ L = ℚ(ζ_9)`, completed at the
unique places above `3`):

* `Langlands.TotallyRamifiedCyclotomicConcreteExample.differentIdeal_eq` :
  `differentIdeal 𝒪_{K_v} 𝒪_{L_w} = 𝔪_{L_w} ^ 6`.

## Route

Mathlib's `conductor_mul_differentIdeal` says `𝔣 * 𝔇 = (f'(x))` whenever `x : B` generates `L` over
`K`, with `f := minpoly A x`. The conductor `𝔣` is `⊤` exactly when `B = A[x]`, so the whole
computation reduces to three concrete facts about `Θ₀` — the image of `theta = ζ_9 - 1` in
`𝒪_{L_w}`, already known there to be an exact uniformizer:

1. **`𝒪_{L_w} = 𝒪_{K_v}[Θ₀]`** (`adjoin_Θ₀_eq_top`), hence `conductor = ⊤`. This is
   `LocalField.adjoin_singleton_eq_top_of_forall_sub_mem_span` (Nakayama) fed the two fields of the
   already-proved `IsTotallyRamified` instance: residue surjectivity
   (`exists_sub_algebraMap_mem_maximalIdeal`) and `𝔪_{K_v} 𝒪_{L_w} = 𝔪_{L_w} ^ e`
   (`map_maximalIdeal_eq` with `ramificationIdx'_eq : e = 3`).
2. **`minpoly 𝒪_{K_v} Θ₀ = eisPoly c₀ = (X + 1) ^ 3 - c₀`** (`minpoly_Θ₀_eq`), by descending the
   completed-level minimal polynomial `minpoly K_v Θ` — pinned by the Eisenstein irreducibility
   already established in the instance file — along `minpoly.isIntegrallyClosed_eq_field_fractions`.
3. **The valuation bookkeeping.** `derivative (eisPoly a) = 3 (X + 1) ^ 2`, so
   `f'(Θ₀) = 3 (Θ₀ + 1) ^ 2 = 3 ζ_9 ^ 2`. The factor `ζ_9` is a root of unity, hence a unit, so the
   ideal is `span {3}`; and `span {(3 : 𝒪_{L_w})} = 𝔪_{L_w} ^ 6` because
   `IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow` gives
   `span {(3 : 𝓞 L)} = w.asIdeal ^ [ℚ(ζ_9) : ℚ] = w.asIdeal ^ 6` already at the number-field level.

The exponent `6` is `v_{L_w}(3)`, i.e. the absolute ramification index `e(L_w / ℚ_3) = φ(9) = 6`;
the two-step cross-check is the tower formula `d(L_w/ℚ_3) = d(L_w/K_v) + e(L_w/K_v) · d(K_v/ℚ_3)`,
i.e. `9 = 6 + 3 · 1`, matching the classical discriminant exponent `p^{n-1}(pn - n - 1) = 9` of
`ℚ(ζ_9)`.
-/

noncomputable section

open IsLocalRing Polynomial IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace Langlands.TotallyRamifiedCyclotomicConcreteExample

/-! ### `𝒪_{L_w} = 𝒪_{K_v}[Θ₀]`, hence the conductor is trivial -/

/-- **`Θ₀` generates `𝒪_{L_w}` over `𝒪_{K_v}`.** Both hypotheses of the Nakayama criterion are
fields of the already-established `IsTotallyRamified` instance: residue surjectivity, and
`𝔪_{K_v} 𝒪_{L_w} = 𝔪_{L_w} ^ e` with `e = p = 3`. -/
theorem adjoin_Θ₀_eq_top :
    Algebra.adjoin (v.adicCompletionIntegers K) ({Θ₀} : Set (w.adicCompletionIntegers L)) = ⊤ := by
  refine LocalField.adjoin_singleton_eq_top_of_forall_sub_mem_span (e := p) ?_ ?_
  · intro s
    obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_maximalIdeal s
    exact ⟨r, by rwa [maximalIdeal_L₀_eq] at hr⟩
  · rw [map_maximalIdeal_eq, ramificationIdx'_eq, maximalIdeal_L₀_eq, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _

theorem conductor_Θ₀_eq_top : conductor (v.adicCompletionIntegers K) Θ₀ = ⊤ :=
  conductor_eq_top_of_adjoin_eq_top adjoin_Θ₀_eq_top

/-! ### `minpoly 𝒪_{K_v} Θ₀ = eisPoly c₀` -/

theorem aeval_Θ_eisPoly :
    aeval Θ (eisPoly (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) c₀)) = 0 := by
  rw [show eisPoly (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) c₀) =
      (minpoly K theta).map (algebraMap K (v.adicCompletion K)) by
    rw [minpoly_theta_eq, eisPoly_map]; rfl,
    Polynomial.aeval_map_algebraMap (v.adicCompletion K) Θ (minpoly K theta), Θ,
    Polynomial.aeval_algebraMap_apply (w.adicCompletion L) theta (minpoly K theta),
    minpoly.aeval, map_zero]

theorem isIntegral_Θ : IsIntegral (v.adicCompletion K) Θ :=
  ⟨_, eisPoly_monic _, aeval_Θ_eisPoly⟩

/-- The completed-level minimal polynomial, pinned by the Eisenstein irreducibility already proved
in `TotallyRamifiedCyclotomicConcreteExample` (`map_minpoly_theta_irreducible`). -/
theorem minpoly_Kv_Θ_eq :
    minpoly (v.adicCompletion K) Θ =
      eisPoly (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) c₀) := by
  refine (minpoly.eq_of_irreducible_of_monic ?_ aeval_Θ_eisPoly (eisPoly_monic _)).symm
  rw [show eisPoly (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) c₀) =
      (minpoly K theta).map (algebraMap K (v.adicCompletion K)) by
    rw [minpoly_theta_eq, eisPoly_map]; rfl]
  exact map_minpoly_theta_irreducible

theorem isIntegral_Θ₀ : IsIntegral (v.adicCompletionIntegers K) Θ₀ :=
  IsIntegralClosure.isIntegral (v.adicCompletionIntegers K) (w.adicCompletion L) Θ₀

/-- **The integral-level minimal polynomial is the Eisenstein polynomial itself.** `𝒪_{K_v}` is
integrally closed with fraction field `K_v`, so `minpoly 𝒪_{K_v} Θ₀` is the unique preimage of
`minpoly K_v Θ` under the (injective) coefficient map. -/
theorem minpoly_Θ₀_eq : minpoly (v.adicCompletionIntegers K) Θ₀ = eisPoly c₀ := by
  refine Polynomial.map_injective (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
    (FaithfulSMul.algebraMap_injective _ _) ?_
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions (v.adicCompletion K) (w.adicCompletion L)
    isIntegral_Θ₀, eisPoly_map]
  exact minpoly_Kv_Θ_eq

/-- `Θ` generates `L_w` over `K_v` — the primitivity hypothesis of `conductor_mul_differentIdeal`,
in `Algebra.adjoin` (rather than `IntermediateField.adjoin`) form. -/
theorem adjoin_Kv_Θ_eq_top :
    Algebra.adjoin (v.adicCompletion K)
      ({algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) Θ₀} :
        Set (w.adicCompletion L)) = ⊤ := by
  have htop := IsDedekindDomain.HeightOneSpectrum.adjoin_thetaw_eq_top K L v w
    isIntegral_theta adjoin_theta_eq_top isIntegral_Θ
  rw [show algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) Θ₀ = Θ from rfl,
    ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic isIntegral_Θ.isAlgebraic]
  rw [show IntermediateField.adjoin (v.adicCompletion K) ({Θ} : Set (w.adicCompletion L)) = ⊤ from
    htop]
  rfl

/-! ### `v_{L_w}(3) = 6`, and `ζ_9` is a unit -/

theorem isUnit_of_valuation_eq_one {x : w.adicCompletionIntegers L}
    (hx : Valued.v (x : w.adicCompletion L) = 1) : IsUnit x :=
  Valuation.Integers.isUnit_of_one' (Valuation.integer.integers _) hx

/-- `3` factors as `w.asIdeal ^ 6` already in `𝓞 L`: this is Mathlib's
`map_eq_span_zeta_sub_one_pow` (`p 𝓞_{ℚ(ζ_{p^{k+1}})} = (ζ - 1) ^ [ℚ(ζ_{p^{k+1}}) : ℚ]`) at
`p = 3`, `k = 1`, where `[L : ℚ] = 6`. -/
theorem span_three_eq : Ideal.span {(3 : 𝓞 L)} = w.asIdeal ^ 6 := by
  have h := IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow p 1 hζ
  rw [Ideal.map_span, Set.image_singleton, finrank_ℚ_L] at h
  show Ideal.span {(3 : 𝓞 L)} = Ideal.span {hζ.toInteger - 1} ^ 6
  rw [← h]
  norm_num

theorem intValuation_three : w.intValuation (3 : 𝓞 L) = WithZero.exp (-6 : ℤ) := by
  have hspan : Ideal.span {(3 : 𝓞 L)} = Ideal.span {(hζ.toInteger - 1) ^ 6} := by
    rw [span_three_eq, ← Ideal.span_singleton_pow]; rfl
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hu1 : w.intValuation (u : 𝓞 L) = 1 :=
    intValuation_eq_one_iff.mpr fun hmem =>
      w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem u.isUnit)
  have h := congrArg w.intValuation hu
  rw [map_mul, hu1, mul_one, map_pow, intValuation_ζ_sub_one, ← WithZero.exp_nsmul,
    nsmul_eq_mul, mul_neg_one] at h
  rw [h]
  norm_num

theorem valuation_three :
    Valued.v ((3 : w.adicCompletionIntegers L) : w.adicCompletion L) = WithZero.exp (-6 : ℤ) := by
  rw [show (3 : w.adicCompletionIntegers L) =
      algebraMap (𝓞 L) (w.adicCompletionIntegers L) (3 : 𝓞 L) from (map_ofNat _ 3).symm,
    IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    w.valuation_of_algebraMap]
  exact intValuation_three

/-- `Θ₀ + 1` is the image of `ζ_9` — this is what makes the derivative's `(Θ₀ + 1) ^ 2` factor a
unit and leaves `span {3}` behind. -/
theorem Θ₀_add_one_eq :
    (Θ₀ : w.adicCompletionIntegers L) + 1 =
      algebraMap (𝓞 L) (w.adicCompletionIntegers L) hζ.toInteger := by
  have hθ1 : theta + 1 = algebraMap (𝓞 L) L hζ.toInteger := by
    rw [show algebraMap (𝓞 L) L hζ.toInteger = ζ from rfl, theta]; ring
  apply Subtype.ext
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  show (Θ : w.adicCompletion L) + 1 = _
  rw [Θ, ← map_one (algebraMap L (w.adicCompletion L)), ← map_add, hθ1]
  rfl

theorem isUnit_Θ₀_add_one : IsUnit ((Θ₀ : w.adicCompletionIntegers L) + 1) := by
  refine isUnit_of_valuation_eq_one ?_
  rw [Θ₀_add_one_eq, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    w.valuation_of_algebraMap]
  exact intValuation_eq_one_iff.mpr fun hmem =>
    w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
      (hζ.toInteger_isPrimitiveRoot.isUnit (by positivity)))

/-! ### `span {3} = 𝔪_{L_w} ^ 6` -/

theorem valuation_Θ_pow_six :
    Valued.v ((Θ : w.adicCompletion L) ^ 6) = WithZero.exp (-6 : ℤ) := by
  rw [map_pow, valuation_Θ, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one]
  norm_num

/-- The unit relating `3` to `Θ ^ 6`. -/
def u₃ : w.adicCompletion L := (3 : w.adicCompletion L) / Θ ^ 6

theorem valuation_u₃ : Valued.v (u₃ : w.adicCompletion L) = 1 := by
  rw [u₃, map_div₀, show Valued.v (3 : w.adicCompletion L) = WithZero.exp (-6 : ℤ) from
    valuation_three, valuation_Θ_pow_six, div_self WithZero.exp_ne_zero]

/-- `u₃`, viewed inside `w.adicCompletionIntegers L`. -/
def u₃₀ : w.adicCompletionIntegers L :=
  ⟨u₃, by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 L) L w, valuation_u₃]⟩

theorem u₃₀_isUnit : IsUnit (u₃₀ : w.adicCompletionIntegers L) :=
  isUnit_of_valuation_eq_one valuation_u₃

theorem three_eq_Θ₀_pow_mul :
    (3 : w.adicCompletionIntegers L) = (Θ₀ : w.adicCompletionIntegers L) ^ 6 * u₃₀ := by
  apply Subtype.ext
  show (3 : w.adicCompletion L) = (Θ : w.adicCompletion L) ^ 6 * u₃
  rw [u₃, mul_div_cancel₀ _ (pow_ne_zero _ Θ_ne_zero)]

theorem span_three_L₀ :
    Ideal.span {(3 : w.adicCompletionIntegers L)} =
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ 6 := by
  rw [three_eq_Θ₀_pow_mul, Ideal.span_singleton_mul_right_unit u₃₀_isUnit,
    ← Ideal.span_singleton_pow, ← maximalIdeal_L₀_eq]

/-! ### The different exponent -/

/-- `derivative ((X + 1) ^ 3 - C a) = 3 (X + 1) ^ 2`, evaluated. -/
theorem aeval_derivative_eisPoly {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (a : R) (y : S) : aeval y (derivative (eisPoly a)) = 3 * (y + 1) ^ 2 := by
  simp [eisPoly, derivative_add, derivative_mul, map_ofNat]
  ring

/-- **The different exponent of `L_w / K_v = ℚ_3(ζ_9) / ℚ_3(ζ_3)` is `6`.**

`𝒪_{L_w} = 𝒪_{K_v}[Θ₀]` makes the conductor trivial, so `conductor_mul_differentIdeal` computes the
different outright as `span {f'(Θ₀)}` for `f = (X + 1) ^ 3 - c₀`; and `f'(Θ₀) = 3 (Θ₀ + 1) ^ 2` is
`3` times a unit, whose ideal is `𝔪_{L_w} ^ 6`.

This discharges the `hd : differentIdeal A B = maximalIdeal B ^ d` hypothesis of
`Langlands.AdicCompletionTraceSurjectivity` and `Langlands.AdicCompletionNormGroupImage` for this
instance, with `d = 6`. -/
theorem differentIdeal_eq :
    differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ 6 := by
  have h := conductor_mul_differentIdeal (v.adicCompletionIntegers K) (v.adicCompletion K)
    (w.adicCompletion L) Θ₀ adjoin_Kv_Θ_eq_top
  rw [conductor_Θ₀_eq_top, Ideal.top_mul, minpoly_Θ₀_eq, aeval_derivative_eisPoly] at h
  rw [h, show (3 : w.adicCompletionIntegers L) * ((Θ₀ : w.adicCompletionIntegers L) + 1) ^ 2 =
      3 * ((Θ₀ + 1) ^ 2) from rfl,
    Ideal.span_singleton_mul_right_unit (isUnit_Θ₀_add_one.pow 2), span_three_L₀]

end Langlands.TotallyRamifiedCyclotomicConcreteExample

end
