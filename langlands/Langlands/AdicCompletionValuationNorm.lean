import Langlands.AdicCompletionResidueDegree
import Langlands.NonarchimedeanExponentialAdicCompletion
import Langlands.NormMapResidueCompatibility
import Langlands.TotallyRamifiedNormIndex
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# The valuation-of-norm formula, generically: `v(N_{L/K}(x)) = w(x) ^ f`

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`, and `f := v.asIdeal.inertiaDeg' w.asIdeal`. This file proves
the classical valuation-of-norm formula, for every `x : (w.adicCompletion L)ˣ`:

`Valued.v (Algebra.norm (v.adicCompletion K) (x : w.adicCompletion L)) = (Valued.v (x : w.adicCompletion L)) ^ f`

with no `IsTotallyRamified` hypothesis. Both sides are valued in the *same* `ℤᵐ⁰`, since
`Langlands.NormMap` normalizes every completion's valuation to the same rank-one base.

## Route

1. For `x : L₀` nonzero, `Ideal.span {x} = maximalIdeal L₀ ^ n` for `n : ℕ` the "additive
   valuation" of `x` (`IsDiscreteValuationRing.associated_pow_irreducible`, against a uniformizer
   `πL₀` of `L₀`), and `Valued.v x = Valued.v πL₀ ^ n = WithZero.exp (-n)`.
2. `Ideal.relNorm K₀ (Ideal.span {x}) = Ideal.span {Algebra.norm K₀ x}` (`Ideal.relNorm_singleton`
   + `Algebra.intNorm_eq_norm`), and `Ideal.relNorm K₀ (maximalIdeal L₀) = maximalIdeal K₀ ^ f`
   (`Ideal.relNorm_eq_pow_of_isMaximal`, with the exponent identified as `f` via
   `Langlands.AdicCompletionResidueDegree.inertiaDeg'_eq_finrank_residueField`). So
   `Ideal.span {Algebra.norm K₀ x} = maximalIdeal K₀ ^ (f * n)`, giving
   `Valued.v (algebraMap K₀ K (Algebra.norm K₀ x)) = WithZero.exp (-(f * n)) = (Valued.v x) ^ f`.
3. `Algebra.norm K₀ x` transports to the field-level `Algebra.norm K (x : L)` via
   `algebraMap_norm_eq_norm_algebraMap` (already in the repo), closing the case `x ∈ L₀ \ {0}`.
4. Extend to all of `(w.adicCompletion L)ˣ` via the "L-self" uniformizer decomposition
   `exists_zpow_mul_unit_eq_of_irreducible_self` (`Langlands.TotallyRamifiedNormIndex`, applied at
   `w` instead of `v`) and multiplicativity of both the norm and the valuation.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valued_norm_eq_pow_of_ne_zero_of_mem_adicCompletionIntegers`
  : the case `x ∈ L₀ \ {0}`.
* `IsDedekindDomain.HeightOneSpectrum.valued_localNormMap_eq_pow` : the headline formula, for every
  `x : (w.adicCompletion L)ˣ`.
-/

noncomputable section

open IsDedekindDomain IsLocalRing

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]

/-! ### `(maximalIdeal L₀).LiesOver (maximalIdeal K₀)`, and the maximal-ideal inertia degree -/

omit [Algebra.IsIntegral R S] in
/-- `maximalIdeal L₀` lies over `maximalIdeal K₀`: transported from the generic fact for a pair of
`Valuation.HasExtension` valuation subrings (`Mathlib.RingTheory.Valuation.Extension`), through
the `adicCompletionIntegers = valuationSubring` unfolding, exactly as `ResidueFieldNorm`'s
`Algebra`/`IsLocalHom` instances are. -/
instance : Ideal.LiesOver (maximalIdeal (w.adicCompletionIntegers L))
    (maximalIdeal (v.adicCompletionIntegers K)) :=
  inferInstanceAs (Ideal.LiesOver
    (maximalIdeal (Valuation.valuationSubring (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)))
    (maximalIdeal (Valuation.valuationSubring (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))))

omit [Algebra.IsIntegral R S] [Module.Finite K L]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- **The maximal-ideal inertia degree equals `f`.** `(maximalIdeal L₀).inertiaDeg K₀ =
v.asIdeal.inertiaDeg' w.asIdeal`, via `Ideal.inertiaDeg_eq_of_isMaximal` (reducing to
`Module.finrank (ResidueField K₀) (ResidueField L₀)`, `ResidueField` unfolding definitionally to
the quotient by the maximal ideal) and
`Langlands.AdicCompletionResidueDegree.inertiaDeg'_eq_finrank_residueField`. -/
theorem maximalIdeal_inertiaDeg_eq_inertiaDeg' :
    (maximalIdeal (w.adicCompletionIntegers L)).inertiaDeg (v.adicCompletionIntegers K) =
      v.asIdeal.inertiaDeg' w.asIdeal := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal (p := maximalIdeal (v.adicCompletionIntegers K))
    (q := maximalIdeal (w.adicCompletionIntegers L)),
    inertiaDeg'_eq_finrank_residueField K L v w]
  rfl

/-! ### `PerfectField (FractionRing K₀)`, under `CharZero K` -/

variable [CharZero K]

omit [Algebra.IsIntegral R S] [Module.Finite K L]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- `v.adicCompletionIntegers K` has characteristic `0`, pulled back from `CharZero K` along the
scalar-tower algebra map into `v.adicCompletion K` (`RingHom.charZero`, needing `CharZero
(v.adicCompletion K)`, itself pulled back from `CharZero K` along the injective field map
`algebraMap K (v.adicCompletion K)`). -/
instance instCharZeroAdicCompletionIntegers : CharZero (v.adicCompletionIntegers K) := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_ringHom
      (RingHom.injective (algebraMap K (v.adicCompletion K)))
  exact RingHom.charZero (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))

omit [Algebra.IsIntegral R S] [Module.Finite K L]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- `FractionRing K₀` is a perfect field: `CharZero K₀` (above) gives `CharZero (FractionRing
K₀)` (`IsFractionRing.charZero`), and a `CharZero` field is perfect. -/
instance instPerfectFieldFractionRingAdicCompletionIntegers :
    PerfectField (FractionRing (v.adicCompletionIntegers K)) :=
  haveI : CharZero (FractionRing (v.adicCompletionIntegers K)) :=
    IsFractionRing.charZero (v.adicCompletionIntegers K)
  PerfectField.ofCharZero

/-! ### The valuation-of-norm formula: the integral case -/

omit [Algebra.IsIntegral R S] in
/-- **The valuation-of-norm formula, for `x ∈ L₀ \ {0}`.** `Valued.v (algebraMap K₀ K
(Algebra.norm K₀ x)) = (Valued.v (x : L)) ^ f`. Proved by writing `x` as `πL₀ ^ n` times a unit
(`IsDiscreteValuationRing.associated_pow_irreducible`), tracking that decomposition through
`Ideal.relNorm` (`Ideal.relNorm_singleton`, `Ideal.relNorm_eq_pow_of_isMaximal`, and
`maximalIdeal_inertiaDeg_eq_inertiaDeg'` to identify the exponent as `f`), and reading the
resulting ideal equality back off as a valuation via a second uniformizer `πK₀` of `K₀`. -/
theorem valued_norm_eq_pow_of_ne_zero (x : w.adicCompletionIntegers L) (hx : x ≠ 0) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        (Algebra.norm (v.adicCompletionIntegers K) x)) =
      (Valued.v (x : w.adicCompletion L)) ^ (v.asIdeal.inertiaDeg' w.asIdeal) := by
  set f := v.asIdeal.inertiaDeg' w.asIdeal with hfdef
  -- A uniformizer `πL₀` of `L₀`, and `x`'s decomposition against it.
  obtain ⟨πL, hπLu⟩ := exists_isUniformizer_valued w (F := L)
  have hπLmem : πL ∈ w.adicCompletionIntegers L :=
    (mem_adicCompletionIntegers S L w).mpr hπLu.val_lt_one.le
  set πL₀ : w.adicCompletionIntegers L := ⟨πL, hπLmem⟩ with hπL₀def
  have hspanL : maximalIdeal (w.adicCompletionIntegers L) = Ideal.span {πL₀} := hπLu.is_generator
  have hπL₀irr : Irreducible πL₀ :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer πL₀).mpr hspanL
  obtain ⟨n, hassocL⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hπL₀irr
  obtain ⟨uL, huL⟩ := hassocL
  -- `Ideal.span {x} = maximalIdeal L₀ ^ n`.
  have hspanx : Ideal.span ({x} : Set (w.adicCompletionIntegers L)) =
      maximalIdeal (w.adicCompletionIntegers L) ^ n := by
    rw [hspanL, Ideal.span_singleton_pow,
      Ideal.span_singleton_eq_span_singleton.mpr ⟨uL, huL⟩]
  -- Track this through `relNorm`.
  have hrelnorm_x : Ideal.relNorm (v.adicCompletionIntegers K)
      (Ideal.span ({x} : Set (w.adicCompletionIntegers L))) =
      Ideal.span
        ({Algebra.norm (v.adicCompletionIntegers K) x} : Set (v.adicCompletionIntegers K)) := by
    rw [Ideal.relNorm_singleton, Algebra.intNorm_eq_norm]
  have hrelnorm_maxL : Ideal.relNorm (v.adicCompletionIntegers K)
      (maximalIdeal (w.adicCompletionIntegers L)) = maximalIdeal (v.adicCompletionIntegers K) ^ f := by
    rw [Ideal.relNorm_eq_pow_of_isMaximal (maximalIdeal (w.adicCompletionIntegers L))
      (maximalIdeal (v.adicCompletionIntegers K)), maximalIdeal_inertiaDeg_eq_inertiaDeg']
  have hspannorm : Ideal.span
      ({Algebra.norm (v.adicCompletionIntegers K) x} : Set (v.adicCompletionIntegers K)) =
      maximalIdeal (v.adicCompletionIntegers K) ^ (f * n) := by
    rw [← hrelnorm_x, hspanx, map_pow, hrelnorm_maxL, pow_mul]
  -- A uniformizer `πK₀` of `K₀`, reading the ideal equality off as a valuation.
  obtain ⟨πK, hπKu⟩ := exists_isUniformizer_valued v (F := K)
  have hπKmem : πK ∈ v.adicCompletionIntegers K :=
    (mem_adicCompletionIntegers R K v).mpr hπKu.val_lt_one.le
  set πK₀ : v.adicCompletionIntegers K := ⟨πK, hπKmem⟩ with hπK₀def
  have hspanK : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {πK₀} := hπKu.is_generator
  rw [hspanK, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at hspannorm
  obtain ⟨uK, huK⟩ := hspannorm
  -- Compute the two valuations.
  have hπLval : Valued.v (πL₀ : w.adicCompletion L) = WithZero.exp (-1 : ℤ) := by
    rw [show (πL₀ : w.adicCompletion L) = πL from rfl, hπLu.val,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (valuedAdicCompletion_surjective L w), Units.val_mk0]
  have hπKval : Valued.v (πK₀ : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [show (πK₀ : v.adicCompletion K) = πK from rfl, hπKu.val,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (valuedAdicCompletion_surjective K v), Units.val_mk0]
  have hxval : Valued.v (x : w.adicCompletion L) = WithZero.exp (-(n : ℤ)) := by
    have huLval : Valued.v ((uL : (w.adicCompletionIntegers L)ˣ) :
        w.adicCompletion L) = 1 :=
      adicCompletionIntegers.isUnit_iff_valued_eq_one.mp (uL : (w.adicCompletionIntegers L)ˣ).isUnit
    have hcast : (x : w.adicCompletion L) * ((uL : (w.adicCompletionIntegers L)ˣ) :
        w.adicCompletion L) = (πL₀ : w.adicCompletion L) ^ n := by
      have h := congrArg (fun y : w.adicCompletionIntegers L => (y : w.adicCompletion L)) huL
      simpa using h
    have hval := congrArg Valued.v hcast
    rw [map_mul, map_pow, hπLval, huLval, mul_one, ← WithZero.exp_nsmul, nsmul_eq_mul,
      mul_neg_one] at hval
    exact hval
  have hnormval : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (Algebra.norm (v.adicCompletionIntegers K) x)) = WithZero.exp (-((f * n : ℕ) : ℤ)) := by
    have huKval : Valued.v ((uK : (v.adicCompletionIntegers K)ˣ) :
        v.adicCompletion K) = 1 :=
      adicCompletionIntegers.isUnit_iff_valued_eq_one.mp
        (uK : (v.adicCompletionIntegers K)ˣ).isUnit
    have hcast : (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        (Algebra.norm (v.adicCompletionIntegers K) x)) *
        ((uK : (v.adicCompletionIntegers K)ˣ) : v.adicCompletion K) =
        (πK₀ : v.adicCompletion K) ^ (f * n) := by
      have h := congrArg (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) huK
      rw [map_mul, map_pow] at h
      exact h
    have hval := congrArg Valued.v hcast
    rw [map_mul, map_pow, hπKval, huKval, mul_one, ← WithZero.exp_nsmul, nsmul_eq_mul,
      mul_neg_one] at hval
    exact hval
  rw [hnormval, hxval, ← WithZero.exp_nsmul, nsmul_eq_mul]
  congr 1
  push_cast
  ring

/-! ### The valuation-of-norm formula, on all of `(w.adicCompletion L)ˣ` -/

omit [Algebra.IsIntegral R S] in
/-- **The valuation-of-norm formula, headline form.** For every `a : (w.adicCompletion L)ˣ`,
`Valued.v (Algebra.norm (v.adicCompletion K) (a : w.adicCompletion L)) = (Valued.v (a :
w.adicCompletion L)) ^ f`. Extends `valued_norm_eq_pow_of_ne_zero` from `L₀ \ {0}` to all of
`(w.adicCompletion L)ˣ` via the "L-self" uniformizer decomposition
`exists_zpow_mul_unit_eq_of_irreducible_self` (`a = πL₀ ^ k * u` for `k : ℤ`, `u : L₀ˣ`) and
multiplicativity of both the norm and the valuation: the `πL₀`-part is handled by
`valued_norm_eq_pow_of_ne_zero` itself (at `x := πL₀`, `n = 1`), and the unit part contributes
nothing to either side (`localNormMap_mem_units` for the norm, `adicCompletionIntegers.isUnit_iff_valued_eq_one`
for the valuation). -/
theorem valued_localNormMap_eq_pow (a : (w.adicCompletion L)ˣ) :
    Valued.v (Algebra.norm (v.adicCompletion K) (a : w.adicCompletion L)) =
      (Valued.v (a : w.adicCompletion L)) ^ (v.asIdeal.inertiaDeg' w.asIdeal) := by
  set f := v.asIdeal.inertiaDeg' w.asIdeal with hfdef
  obtain ⟨πL, hπLu⟩ := exists_isUniformizer_valued w (F := L)
  have hπLmem : πL ∈ w.adicCompletionIntegers L :=
    (mem_adicCompletionIntegers S L w).mpr hπLu.val_lt_one.le
  set πL₀ : w.adicCompletionIntegers L := ⟨πL, hπLmem⟩ with hπL₀def
  have hspanL : maximalIdeal (w.adicCompletionIntegers L) = Ideal.span {πL₀} := hπLu.is_generator
  have hπL₀irr : Irreducible πL₀ :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer πL₀).mpr hspanL
  have hπLval : Valued.v (πL₀ : w.adicCompletion L) = WithZero.exp (-1 : ℤ) := by
    rw [show (πL₀ : w.adicCompletion L) = πL from rfl, hπLu.val,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (valuedAdicCompletion_surjective L w), Units.val_mk0]
  obtain ⟨k, u, hku⟩ := exists_zpow_mul_unit_eq_of_irreducible_self w hπL₀irr a
  -- Valuation side: `Valued.v a = Valued.v πL₀ ^ k`.
  have huval : Valued.v ((u : (w.adicCompletionIntegers L)ˣ) : w.adicCompletion L) = 1 :=
    adicCompletionIntegers.isUnit_iff_valued_eq_one.mp (u : (w.adicCompletionIntegers L)ˣ).isUnit
  have haval : Valued.v (a : w.adicCompletion L) = WithZero.exp (-(k : ℤ)) := by
    have hval := congrArg Valued.v hku
    rw [map_mul, map_zpow₀, hπLval, huval, mul_one, ← WithZero.exp_zsmul, zsmul_eq_mul,
      mul_neg_one] at hval
    exact hval
  -- Norm side: `Algebra.norm a = (Algebra.norm πL₀) ^ k * Algebra.norm u`.
  have hnormsplit : Algebra.norm (v.adicCompletion K) (a : w.adicCompletion L) =
      (Algebra.norm (v.adicCompletion K) (πL₀ : w.adicCompletion L)) ^ k *
        Algebra.norm (v.adicCompletion K)
          ((u : (w.adicCompletionIntegers L)ˣ) : w.adicCompletion L) := by
    rw [hku, map_mul, Algebra.norm_zpow]
  have hval_normπL : Valued.v (Algebra.norm (v.adicCompletion K) (πL₀ : w.adicCompletion L)) =
      WithZero.exp (-(f : ℤ)) := by
    have h1 := valued_norm_eq_pow_of_ne_zero K L v w πL₀ hπL₀irr.ne_zero
    rw [algebraMap_norm_eq_norm_algebraMap K L v w πL₀, hπLval, ← WithZero.exp_nsmul,
      nsmul_eq_mul, mul_neg_one] at h1
    exact h1
  have hval_normU : Valued.v (Algebra.norm (v.adicCompletion K)
      ((u : (w.adicCompletionIntegers L)ˣ) : w.adicCompletion L)) = 1 := by
    have hmem : embedL L w u ∈ (w.adicCompletionIntegers L).units :=
      range_embedL_eq L w ▸ ⟨u, rfl⟩
    have hu' := adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      (localNormMap_mem_units K L v w hmem)
    rwa [show ((localNormMap K L v w (embedL L w u) : (v.adicCompletion K)ˣ) : v.adicCompletion K)
        = Algebra.norm (v.adicCompletion K)
            ((u : (w.adicCompletionIntegers L)ˣ) : w.adicCompletion L)
        from rfl] at hu'
  rw [haval, ← WithZero.exp_nsmul, nsmul_eq_mul]
  rw [hnormsplit, map_mul, map_zpow₀, hval_normπL, hval_normU, mul_one, ← WithZero.exp_zsmul,
    zsmul_eq_mul]
  congr 1
  push_cast
  ring

end IsDedekindDomain.HeightOneSpectrum

end
