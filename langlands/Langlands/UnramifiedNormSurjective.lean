import Langlands.PrincipalUnitsCauchySequence
import Langlands.PrincipalUnitsSuccessiveApproximation
import Langlands.UnitGroupModPrincipalUnitsSurjective

/-!
# Full unramified norm-group surjectivity

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`. This file assembles the classical successive-approximation
argument (Serre, *Local Fields*, Ch. V §2-3) into the full statement `N_{L/K}(L^×) ⊇ O_K^×`, under
`IsUnramified`: **every unit of `K₀` is the norm of a unit of `L₀`.**

## Route

1. `exists_isUnit_norm_residue_eq`: the "level 0" base case — every unit `y : K₀` is the norm of
   some `x₀ : L₀ˣ` modulo `𝔪_K`, i.e. `residue K₀ (N x₀) = residue K₀ y`. Built directly from the
   residue-field norm surjectivity (`Langlands.ResidueFieldNorm`) and surjectivity of reduction on
   unit groups (`Langlands.UnitGroupModPrincipalUnitsSurjective`), via
   `residue_norm_eq_norm_residue_of_isUnramified` (`Langlands.NormMapResidueCompatibility`) —
   without needing to go through `localNormMap` at all.
2. `exists_isUnit_mul_one_add_uniformizer_eq`: (1) rewritten as the exact multiplicative invariant
   `y = Algebra.norm K₀ x₀ * (1 + π·t₀)` that the successive-approximation recursion starts from.
3. `oneStepCorrection_of_isUnramified`: the per-level correction, `exists_one_add_uniformizer_pow_
   smul_norm_sub_mem` (`Langlands.PrincipalUnitsCauchySequence`, via surjectivity of the
   residue-field trace) repackaged as `OneStepCorrection`.
4. `exists_isUnit_norm_eq_of_correction` (`Langlands.PrincipalUnitsSuccessiveApproximation`): the
   recursion, the Cauchy-sequence bound and the limit argument, which between them use **no**
   ramification hypothesis — only (2) and (3).

## Relation to `Langlands.PrincipalUnitsSuccessiveApproximation`

Steps (2)–(4) were originally written in this file against `IsUnramified` directly. When the tame
totally-ramified case (`Langlands.TotallyRamifiedNormSurjective`) needed the identical recursion,
Cauchy bound and limit argument with a different one-step correction, the ramification-free part
was extracted to `Langlands.PrincipalUnitsSuccessiveApproximation` rather than duplicated; this
file now only supplies the two unramified-specific inputs (1)/(2) and (3). The statement and proof
term of `exists_isUnit_algebraMap_norm_eq_of_isUnramified` are unchanged in content.

## Main result

* `IsDedekindDomain.HeightOneSpectrum.exists_isUnit_algebraMap_norm_eq_of_isUnramified`
-/

noncomputable section

open IsDedekindDomain IsLocalRing Filter Topology

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]

omit [Algebra.IsIntegral R S] in
/-- **The base case: every unit of `K₀` is the norm of a unit of `L₀`, modulo `𝔪_K`.** Under
`IsUnramified`, for `y : K₀` a unit, there is a unit `x : L₀` with `residue K₀ (Algebra.norm K₀ x)
= residue K₀ y`. -/
theorem exists_isUnit_norm_residue_eq [Finite (ResidueField (w.adicCompletionIntegers L))]
    (hU : IsUnramified K L v w) {y : v.adicCompletionIntegers K} (hy : IsUnit y) :
    ∃ x : w.adicCompletionIntegers L, IsUnit x ∧
      residue (v.adicCompletionIntegers K) (Algebra.norm (v.adicCompletionIntegers K) x) =
        residue (v.adicCompletionIntegers K) y := by
  classical
  set t : (ResidueField (v.adicCompletionIntegers K))ˣ :=
    (Ne.isUnit ((residue_ne_zero_iff_isUnit y).mpr hy)).unit with ht
  obtain ⟨s, hs⟩ := residueField_units_norm_surjective (K := K) (L := L) (v := v) (w := w) t
  obtain ⟨xu, hxu⟩ := surjective_units_map_residue (A := w.adicCompletionIntegers L) s
  refine ⟨(xu : w.adicCompletionIntegers L), xu.isUnit, ?_⟩
  rw [residue_norm_eq_norm_residue_of_isUnramified K L v w hU]
  have hxures : residue (w.adicCompletionIntegers L) (xu : w.adicCompletionIntegers L) =
      (s : ResidueField (w.adicCompletionIntegers L)) := by
    rw [← hxu]; exact (Units.coe_map _ xu).symm
  rw [hxures]
  have hs' : Algebra.norm (ResidueField (v.adicCompletionIntegers K))
      (s : ResidueField (w.adicCompletionIntegers L)) =
      (t : ResidueField (v.adicCompletionIntegers K)) := by
    rw [← hs]; exact (Units.coe_map _ s).symm
  rw [hs']
  have : (t : ResidueField (v.adicCompletionIntegers K)) =
      residue (v.adicCompletionIntegers K) y := by
    rw [ht]; exact (Ne.isUnit ((residue_ne_zero_iff_isUnit y).mpr hy)).unit_spec
  rw [this]

/-! ### The successive-approximation sequence -/

variable [Finite (ResidueField (w.adicCompletionIntegers L))]
  {π : v.adicCompletionIntegers K}

omit [Algebra.IsIntegral R S] in
/-- The base case of the successive-approximation sequence, in exact multiplicative form: `y =
Algebra.norm K₀ x * (1 + π * t)` for some unit `x : L₀` and some `t : K₀`. -/
theorem exists_isUnit_mul_one_add_uniformizer_eq (hU : IsUnramified K L v w) (hπ : Irreducible π)
    {y : v.adicCompletionIntegers K} (hy : IsUnit y) :
    ∃ p : w.adicCompletionIntegers L × v.adicCompletionIntegers K,
      IsUnit p.1 ∧ y = Algebra.norm (v.adicCompletionIntegers K) p.1 * (1 + π ^ (0 + 1) * p.2) := by
  obtain ⟨x, hx, hxy⟩ := exists_isUnit_norm_residue_eq K L v w hU hy
  set Nx := Algebra.norm (v.adicCompletionIntegers K) x with hNxdef
  obtain ⟨Nx', hNx'0⟩ := (hx.map (Algebra.norm (v.adicCompletionIntegers K))).exists_right_inv
  have hNx' : Nx * Nx' = 1 := by rw [hNxdef]; exact hNx'0
  have hsub : y - Nx ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (Ideal.Quotient.eq).mp hxy.symm
  have hspan : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π} := hπ.maximalIdeal_eq
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hspan ▸ hsub)
  refine ⟨(x, c * Nx'), hx, ?_⟩
  simp only [zero_add, pow_one]
  linear_combination -hc - (π * c) * hNx'

omit [Algebra.IsIntegral R S] in
/-- The one-step correction hypothesis
(`Langlands.PrincipalUnitsSuccessiveApproximation`'s `OneStepCorrection`), supplied in the
unramified case by `exists_one_add_uniformizer_pow_smul_norm_sub_mem`
(`Langlands.PrincipalUnitsCauchySequence`) — surjectivity of the residue-field trace
`𝓀[L] → 𝓀[K]`. -/
theorem oneStepCorrection_of_isUnramified (hU : IsUnramified K L v w) (hπ : Irreducible π) :
    OneStepCorrection K L v w π :=
  fun n t => exists_one_add_uniformizer_pow_smul_norm_sub_mem K L v w hU hπ n t

omit [Algebra.IsIntegral R S] in
/-- **Full unramified norm-group surjectivity.** Under `IsUnramified`, every unit `y` of `K₀` is
the exact norm `Algebra.norm K₀ x` of some unit `x` of `L₀`: `N_{L/K}(L^×) ⊇ O_K^×`.

The successive-approximation machinery this rests on lives in
`Langlands.PrincipalUnitsSuccessiveApproximation`, stated with no ramification hypothesis; this
theorem supplies its two inputs — `oneStepCorrection_of_isUnramified` (via the residue-field trace)
and `exists_isUnit_mul_one_add_uniformizer_eq` (via the residue-field norm). -/
theorem exists_isUnit_algebraMap_norm_eq_of_isUnramified (hU : IsUnramified K L v w)
    (hπ : Irreducible π) {y : v.adicCompletionIntegers K} (hy : IsUnit y) :
    ∃ x : w.adicCompletionIntegers L, IsUnit x ∧
      Algebra.norm (v.adicCompletionIntegers K) x = y :=
  exists_isUnit_norm_eq_of_correction K L v w (oneStepCorrection_of_isUnramified K L v w hU hπ) hπ
    (exists_isUnit_mul_one_add_uniformizer_eq K L v w hU hπ hy)

end IsDedekindDomain.HeightOneSpectrum

end
