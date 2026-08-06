import Langlands.PrincipalUnitsSuccessiveApproximation
import Langlands.TotallyRamifiedTrace

/-!
# Tame totally ramified norm-group surjectivity on the principal units

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`. This file closes the tame totally-ramified counterpart of
`Langlands.UnramifiedNormSurjective`: under `IsTotallyRamified` and `IsTamelyRamified`,

**every principal unit of `K₀` is the norm of a unit of `L₀`** — `N_{L/K}(U_L) ⊇ U_K^{(1)}`.

## The statement is at `U_K^{(1)}`, not `U_K`, and this is not a gap in the argument

The unramified case reaches all of `U_K` because the level-`0` obstruction vanishes there: the
residue-field norm `𝓀[L] → 𝓀[K]` is surjective for an extension of finite fields
(`Langlands.ResidueFieldNorm`). In the totally ramified case `𝓀[L] = 𝓀[K]` and the induced map on
level `0` is instead `ū ↦ ū ^ e`, whose image is the subgroup of `e`-th powers of `𝓀[K]ˣ` — a
*proper* subgroup as soon as `e > 1` and `e ∣ #𝓀[K]ˣ`. So `N_{L/K}(U_L) = U_K` is **false** for a
totally ramified extension of degree `e > 1`, and `U_K^{(1)}` (equivalently: exactly the units
whose residue is an `e`-th power) is the correct target. That level-`0` computation is a classical
fact stated here only to explain the shape of the theorem; it is **not** formalized in this file,
and neither is the sharper `N_{L/K}(U_L) = {u : ū ∈ (𝓀[K]ˣ)^e}`.

## Route

1. `exists_finrank_nsmul_residue_eq`: under `IsTamelyRamified`, multiplication by `[L₀ : K₀]` is
   surjective on `𝓀[K]` — the *only* place tameness is used. Immediate: the degree is a unit of
   `𝓀[K]`, so one divides by it and lifts along `IsLocalRing.residue_surjective`.
2. `exists_one_add_uniformizer_pow_smul_norm_sub_mem_of_isTotallyRamified`: the one-step correction.
   Feeding the `r : K₀` from (1) into `Langlands.TotallyRamifiedTrace`'s
   `exists_norm_one_add_uniformizer_pow_smul_eq_finrank_nsmul` at `z := algebraMap K₀ L₀ r` gives
   `N(1 + π^{n+1} • z) = 1 + π^{n+1}·y` with `ȳ = [L₀:K₀] · r̄ = t̄`, i.e. the required congruence
   mod `π^{n+2}`. Structurally identical to `Langlands.PrincipalUnitsCauchySequence`'s unramified
   version, with the residue-field trace replaced by multiplication by the degree.
3. `exists_isUnit_norm_eq_of_isTotallyRamified`: `Langlands.PrincipalUnitsSuccessiveApproximation`'s
   `exists_isUnit_norm_eq_of_correction`, applied with (2) and the base case `y = N(1)·(1 + π·t)`
   (available for free once `y ∈ 1 + 𝔪_K`, unlike the unramified case where the base case is the
   residue-field norm surjectivity).

## On the filtration index shift

`ROADMAP.md` Phase 2b's thirty-ninth pass records that on the `L` side the relevant filtration
index is `e·j`, not `j`: `1 + π_K^j • L₀` is `U_{L₀}^{(e·j)}`, by
`IsTotallyRamified.map_maximalIdeal_eq`. That is a correct reading of what is proved, but it is
never needed as a hypothesis or a step: the whole argument quantifies over `z : L₀` directly, and
only the `K`-side index `j` appears anywhere in the statements.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.IsTamelyRamified`
* `IsDedekindDomain.HeightOneSpectrum.exists_one_add_uniformizer_pow_smul_norm_sub_mem_of_isTotallyRamified`
* `IsDedekindDomain.HeightOneSpectrum.exists_isUnit_norm_eq_of_isTotallyRamified`
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

/-- **Tameness.** The degree `[L₀ : K₀]` — equal to the ramification index `e` under
`IsTotallyRamified` (`IsTotallyRamified.finrank_eq`) — is invertible in the residue field `𝓀[K]`.
Classically: `p ∤ e`, for `p` the residue characteristic.

Stated on `𝓀[K]` rather than `𝓀[L]` because that is where the graded map of
`Langlands.TotallyRamifiedTrace` lands; the two are the same field under `IsTotallyRamified`, but
saying so requires the residue-field identification this file otherwise never needs. -/
abbrev IsTamelyRamified : Prop :=
  IsUnit ((Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) : ℕ) :
    ResidueField (v.adicCompletionIntegers K))

omit [Algebra.IsIntegral R S] [Module.Finite K L]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- **Multiplication by the degree is surjective on `𝓀[K]`, under tameness.** This is the entire
content of the tame hypothesis for the norm computation: it is what makes the graded map of
`exists_norm_one_add_uniformizer_pow_smul_eq_finrank_nsmul` hit every residue class, which is what
the successive approximation needs at each level.

The conclusion is stated as "`residue K₀ t` is hit" rather than "the map is surjective" so that it
composes directly with `IsLocalRing.residue_surjective` at the call site. -/
theorem exists_finrank_nsmul_residue_eq (htame : IsTamelyRamified K L v w)
    (t : v.adicCompletionIntegers K) :
    ∃ r : v.adicCompletionIntegers K,
      Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) •
          residue (v.adicCompletionIntegers K) r =
        residue (v.adicCompletionIntegers K) t := by
  obtain ⟨u, hu⟩ := htame
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective
    (R := v.adicCompletionIntegers K)
    ((u⁻¹ : (ResidueField (v.adicCompletionIntegers K))ˣ) *
      residue (v.adicCompletionIntegers K) t)
  refine ⟨r, ?_⟩
  rw [hr, nsmul_eq_mul, ← hu, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

omit [Algebra.IsIntegral R S] in
/-- **The one-step correction for a tame totally ramified extension.** For `π` a uniformizer of
`K₀`, `n : ℕ` and `t : K₀`, there is `z : L₀` with
`Algebra.norm K₀ (1 + π^{n+1}•z) ≡ 1 + π^{n+1}·t \pmod{π^{n+2}}`.

The totally-ramified counterpart of `Langlands.PrincipalUnitsCauchySequence`'s
`exists_one_add_uniformizer_pow_smul_norm_sub_mem`. The correction witness is taken in the image of
`K₀` (`z := algebraMap K₀ L₀ r`), which is possible precisely because the induced map on the graded
pieces is multiplication by the degree rather than a residue-field trace. -/
theorem exists_one_add_uniformizer_pow_smul_norm_sub_mem_of_isTotallyRamified
    (h : IsTotallyRamified K L v w) (htame : IsTamelyRamified K L v w)
    {π : v.adicCompletionIntegers K} (hπ : Irreducible π) (n : ℕ)
    (t : v.adicCompletionIntegers K) :
    ∃ z : w.adicCompletionIntegers L,
      Algebra.norm (v.adicCompletionIntegers K) (1 + π ^ (n + 1) • z) -
        (1 + π ^ (n + 1) * t) ∈ Ideal.span {π ^ (n + 2)} := by
  obtain ⟨r, hr⟩ := exists_finrank_nsmul_residue_eq K L v w htame t
  set z := algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) r with hzdef
  have hx : z - algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) r ∈
      maximalIdeal (w.adicCompletionIntegers L) := by
    rw [hzdef, sub_self]; exact Submodule.zero_mem _
  obtain ⟨y, hy, hyres⟩ :=
    exists_norm_one_add_uniformizer_pow_smul_eq_finrank_nsmul K L v w h hπ n hx
  refine ⟨z, ?_⟩
  have hyt : residue (v.adicCompletionIntegers K) y = residue (v.adicCompletionIntegers K) t := by
    rw [hyres, hr]
  have hsub : y - t ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (Ideal.Quotient.eq).mp hyt
  have hspan : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π} := hπ.maximalIdeal_eq
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hspan ▸ hsub)
  have hfinal : Algebra.norm (v.adicCompletionIntegers K) (1 + π ^ (n + 1) • z) -
      (1 + π ^ (n + 1) * t) = π ^ (n + 2) * c := by
    rw [hy]
    have hyt' : y = t + c * π := by linear_combination -hc
    rw [hyt']; ring
  rw [hfinal]
  exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩

omit [Algebra.IsIntegral R S] in
/-- The one-step correction hypothesis
(`Langlands.PrincipalUnitsSuccessiveApproximation`'s `OneStepCorrection`), supplied in the tame
totally-ramified case by
`exists_one_add_uniformizer_pow_smul_norm_sub_mem_of_isTotallyRamified`. -/
theorem oneStepCorrection_of_isTotallyRamified (h : IsTotallyRamified K L v w)
    (htame : IsTamelyRamified K L v w) {π : v.adicCompletionIntegers K} (hπ : Irreducible π) :
    OneStepCorrection K L v w π :=
  fun n t =>
    exists_one_add_uniformizer_pow_smul_norm_sub_mem_of_isTotallyRamified K L v w h htame hπ n t

omit [Algebra.IsIntegral R S] in
/-- **Tame totally ramified norm-surjectivity on the principal units.** Under `IsTotallyRamified`
and `IsTamelyRamified`, every principal unit `y` of `K₀` (`y - 1 ∈ 𝔪_K`) is the exact norm
`Algebra.norm K₀ x` of some unit `x` of `L₀`: `N_{L/K}(U_L) ⊇ U_K^{(1)}`.

See the module docstring for why the hypothesis is `y ∈ 1 + 𝔪_K` rather than `IsUnit y` — the
level-`0` piece genuinely is not in the image for `e > 1`, so this is the correct statement, not a
weakened one.

The base case the successive approximation needs is free here: `y = Algebra.norm K₀ 1 * (1 + π·t)`
with `t` given by `y - 1 ∈ 𝔪_K = span{π}`. -/
theorem exists_isUnit_norm_eq_of_isTotallyRamified (h : IsTotallyRamified K L v w)
    (htame : IsTamelyRamified K L v w) {π : v.adicCompletionIntegers K} (hπ : Irreducible π)
    {y : v.adicCompletionIntegers K} (hy : y - 1 ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ∃ x : w.adicCompletionIntegers L, IsUnit x ∧
      Algebra.norm (v.adicCompletionIntegers K) x = y := by
  have hspan : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π} := hπ.maximalIdeal_eq
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hspan ▸ hy)
  refine exists_isUnit_norm_eq_of_correction K L v w
    (oneStepCorrection_of_isTotallyRamified K L v w h htame hπ) hπ ⟨(1, t), isUnit_one, ?_⟩
  simp only [map_one, one_mul, zero_add, pow_one]
  linear_combination -ht

end IsDedekindDomain.HeightOneSpectrum

end
