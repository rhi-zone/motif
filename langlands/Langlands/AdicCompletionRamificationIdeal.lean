import Langlands.NormMap
import Langlands.ResidueFieldNorm
import Langlands.NonarchimedeanExponentialAdicCompletion

/-!
# The ideal-power ramification formula at adic completions, generically

`Langlands.TotallyRamifiedCyclotomicConcreteExample.map_maximalIdeal_eq` (and the analogous
theorems in every other concrete `IsTotallyRamified` instance in this repo) proves, for a
*specific* uniformizer built by hand, that `𝔪_{K_v} · 𝒪_{L_w} = 𝔪_{L_w}^e`. That argument never
actually uses total ramification — only that `w.adicCompletionIntegers L` is local (a single place
lies above `v`, automatic at the level of completions) and `v.asIdeal.ramificationIdx' w.asIdeal`
is *defined* as the exponent making this identity hold. This file extracts the generic statement,
for an arbitrary uniformizer produced existentially
(`NonarchimedeanExponentialAdicCompletion.exists_isUniformizer_valued`) rather than a
hand-constructed one, so it applies to *any* `IsDedekindDomain.HeightOneSpectrum` pair `v`, `w`
with `w.asIdeal.LiesOver v.asIdeal` — no `IsTotallyRamified` hypothesis needed.

This is prerequisite infrastructure for relating `Tr_{L_w/K_v}(𝔪_{L_w}^i)` to `𝔪_{K_v}^j` via the
different ideal: that computation needs exactly this ideal-power identity to translate a scaling
by `𝔪_{K_v}^{-j}` (in `K_v`) into a scaling by `𝔪_{L_w}^{-je}` (in `L_w`).

## Route

Both `v.adicCompletionIntegers K` and `w.adicCompletionIntegers L` carry a uniformizer whose
valuation is *exactly* `WithZero.exp (-1)` (`Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective`,
using surjectivity of `Valued.v` at each completion) — the same canonical value at every place,
since `Langlands.NormMap` normalizes every completion's valuation to the same rank-one base. The
image of `K_v`'s uniformizer `πK` under `algebraMap (v.adicCompletionIntegers K)
(w.adicCompletionIntegers L)` therefore has the same valuation, `WithZero.exp (-e)`
(`Langlands.NormMap.valuation_algebraMap_pow_eq`), as `L_w`'s uniformizer `πL` raised to the `e`-th
power — so their ratio is a unit of `w.adicCompletionIntegers L`, and `Ideal.span {algebraMap πK} =
Ideal.span {πL} ^ e` up to that unit, i.e. `𝔪_{K_v} · 𝒪_{L_w} = 𝔪_{L_w}^e` exactly.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx'` : the
  headline identity, `Ideal.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers
  L)) (maximalIdeal (v.adicCompletionIntegers K)) = maximalIdeal (w.adicCompletionIntegers L) ^
  (v.asIdeal.ramificationIdx' w.asIdeal)`, with no `IsTotallyRamified` hypothesis.
-/

noncomputable section

open IsDedekindDomain IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- **The ideal-power ramification formula, generically.** `𝔪_{K_v} · 𝒪_{L_w} = 𝔪_{L_w}^e`, for `e
:= v.asIdeal.ramificationIdx' w.asIdeal`, with no `IsTotallyRamified` hypothesis: this identity
holds at every place, not just totally ramified ones. -/
theorem map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx' :
    Ideal.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L))
        (maximalIdeal (v.adicCompletionIntegers K)) =
      maximalIdeal (w.adicCompletionIntegers L) ^ (v.asIdeal.ramificationIdx' w.asIdeal) := by
  obtain ⟨πK, hπKu⟩ := exists_isUniformizer_valued v (F := K)
  obtain ⟨πL, hπLu⟩ := exists_isUniformizer_valued w (F := L)
  set e := v.asIdeal.ramificationIdx' w.asIdeal with hedef
  have hπKmem : πK ∈ v.adicCompletionIntegers K :=
    (mem_adicCompletionIntegers R K v).mpr hπKu.val_lt_one.le
  have hπLmem : πL ∈ w.adicCompletionIntegers L :=
    (mem_adicCompletionIntegers S L w).mpr hπLu.val_lt_one.le
  set πK₀ : v.adicCompletionIntegers K := ⟨πK, hπKmem⟩ with hπK₀def
  set πL₀ : w.adicCompletionIntegers L := ⟨πL, hπLmem⟩ with hπL₀def
  have hspanK : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {πK₀} := hπKu.is_generator
  have hspanL : maximalIdeal (w.adicCompletionIntegers L) = Ideal.span {πL₀} := hπLu.is_generator
  have hπKval : Valued.v πK = WithZero.exp (-1 : ℤ) := by
    rw [hπKu.val, Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (valuedAdicCompletion_surjective K v), Units.val_mk0]
  have hπLval : Valued.v πL = WithZero.exp (-1 : ℤ) := by
    rw [hπLu.val, Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (valuedAdicCompletion_surjective L w), Units.val_mk0]
  have hπL_ne_zero : (πL₀ : w.adicCompletion L) ≠ 0 := hπLu.ne_zero
  have hvalcomap :
      Valued.v (adicCompletionComap K L v w πK) = WithZero.exp (-(e : ℤ)) := by
    rw [valuation_algebraMap_pow_eq K L v w πK, hπKval, ← WithZero.exp_nsmul, nsmul_eq_mul,
      mul_neg_one]
  have hvalpow :
      Valued.v ((πL₀ : w.adicCompletionIntegers L) : w.adicCompletion L) ^ e =
        WithZero.exp (-(e : ℤ)) := by
    rw [hπLval, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one]
  have hvaleq :
      Valued.v (adicCompletionComap K L v w πK) =
        Valued.v ((πL₀ : w.adicCompletionIntegers L) : w.adicCompletion L) ^ e := by
    rw [hvalcomap, hvalpow]
  have hcomap_ne_zero : adicCompletionComap K L v w πK ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvalcomap
    exact absurd hvalcomap.symm (by simp)
  set u : w.adicCompletion L :=
    adicCompletionComap K L v w πK / (πL₀ : w.adicCompletion L) ^ e with hudef
  have huval : Valued.v u = 1 := by
    rw [hudef, map_div₀, hvalcomap, map_pow, hvalpow, div_self WithZero.exp_ne_zero]
  have huval_le : Valued.v u ≤ 1 := huval.le
  have humem : u ∈ w.adicCompletionIntegers L := (mem_adicCompletionIntegers S L w).mpr huval_le
  set u₀ : w.adicCompletionIntegers L := ⟨u, humem⟩ with hu₀def
  have hu_ne_zero : u ≠ 0 := by
    intro h0
    rw [h0, map_zero] at huval
    exact absurd huval (by simp)
  have hu₀_isUnit : IsUnit (u₀ : w.adicCompletionIntegers L) := by
    refine IsUnit.of_mul_eq_one
      (⟨(u : w.adicCompletion L)⁻¹, by
        rw [mem_adicCompletionIntegers S L w, map_inv₀, huval, inv_one]⟩) ?_
    apply Subtype.ext
    show (u : w.adicCompletion L) * (u : w.adicCompletion L)⁻¹ = 1
    exact mul_inv_cancel₀ hu_ne_zero
  have hcomap_eq : algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) πK₀ =
      (πL₀ : w.adicCompletionIntegers L) ^ e * u₀ := by
    apply Subtype.ext
    show (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) πK₀ :
        w.adicCompletion L) = ((πL₀ ^ e * u₀ : w.adicCompletionIntegers L) : w.adicCompletion L)
    rw [coe_algebraMap_adicCompletionIntegers]
    push_cast
    show adicCompletionComap K L v w πK = (πL₀ : w.adicCompletion L) ^ e * u
    rw [hudef]
    field_simp
  rw [hspanK, Ideal.map_span, Set.image_singleton, hcomap_eq,
    Ideal.span_singleton_mul_right_unit hu₀_isUnit, ← Ideal.span_singleton_pow, ← hspanL]
