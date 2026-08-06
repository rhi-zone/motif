import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Langlands.NormMapResidueCompatibility
import Langlands.TotallyRamifiedValuationExtension

/-!
# The norm of a totally ramified extension is the `e`-th power on residues

For `L₀ / K₀` a finite free extension of local rings whose residue extension is *trivial*, the ring
norm reduces mod `𝔪_K` to the `[L₀ : K₀]`-th power map:

`N_{L₀/K₀}(x) ≡ x̄ ^ [L₀ : K₀] (mod 𝔪_K)`.

This is the **level-`0` computation** listed as open in `ROADMAP.md` Phase 2b's fortieth-pass entry,
and the exact multiplicative counterpart of `Langlands.TotallyRamifiedTrace`'s
`IsLocalRing.residue_trace_eq_finrank_nsmul_residue` (`Tr(x) ≡ [L₀:K₀] · x̄`). Under
`IsTotallyRamified` the exponent is the ramification index `e`
(`IsTotallyRamified.finrank_eq`), so on units it says `N(u) ≡ ū ^ e`, exhibiting the level-`0`
graded map of the principal-units filtration as `ū ↦ ū ^ e` on `𝓀[K]ˣ` — the map whose image is the
subgroup of `e`-th powers, which is why
`Langlands.TotallyRamifiedNormSurjective`'s `exists_isUnit_norm_eq_of_isTotallyRamified` reaches
only `U_K^{(1)}` and not all of `U_K`.

## Route

The same three-step shape as the trace file, with `det` in place of `trace`, working in the Artinian
quotient `A := L₀ ⧸ 𝔪_K·L₀` over `κ := 𝓀[K]`:

1. `IsLocalRing.residue_norm_eq_norm_residue` (`Langlands.NormMapResidueCompatibility`, general, no
   ramification content) moves the statement into `A` over `κ`.
2. Triviality of the residue extension writes `x = algebraMap r + z` with `r : K₀` and `z ∈ 𝔪_L`,
   so in `A` the multiplication-by-`x̄` endomorphism is `algebraMap κ (End κ A) r̄ + ν`, where `ν` is
   multiplication by `z̄`.
3. `z ∈ 𝔪_L` and `𝔪_L ^ [L₀:K₀] ≤ 𝔪_K·L₀` (`IsTotallyRamified.pow_finrank_le`) make `ν` nilpotent,
   so `LinearMap.charpoly (-ν) = X ^ finrank κ A` (`IsNilpotent.charpoly_eq_X_pow_finrank`, valid
   since `κ` is a field hence a domain). Evaluating that at `r̄` via `LinearMap.eval_charpoly`
   (`eval t f.charpoly = det (algebraMap t - f)`) gives `det (algebraMap r̄ + ν) = r̄ ^ finrank κ A`,
   and `IsLocalRing.finrank_quotient_map` rewrites the exponent to `finrank K₀ L₀`.

Where the trace argument used "a nilpotent endomorphism has trace `0`", this uses "a nilpotent
endomorphism has characteristic polynomial `X ^ d`" — the same basis-free input, one step stronger.
As in the trace file, **no Eisenstein presentation, power basis or companion matrix is
constructed**, and gap 3 of the thirty-ninth-pass entry (threading
`Langlands.TotallyRamifiedEisenstein`'s abstract `ValuativeRel`/`spectralNorm` bundle into the
`HeightOneSpectrum` setting) is neither used nor closed.

## What this does *not* give

The sharp description `N_{L/K}(U_L) = {u ∈ U_K : ū ∈ (𝓀[K]ˣ)^e}` needs, besides the congruence
proved here (which gives `⊆`), a surjectivity statement in the other direction: that every unit
whose residue is an `e`-th power *is* a norm. That would combine this file's formula at level `0`
with `Langlands.TotallyRamifiedNormSurjective`'s `U_K^{(1)}` result by a one-step correction at
level `0`, and is not attempted here.

## Main results

* `IsLocalRing.norm_residue_add_eq_pow` : `N_{A/κ}(algebraMap c + z̄) = c ^ finrank R S` for
  `z ∈ 𝔪_S`, the determinant computation proper.
* `IsLocalRing.residue_norm_eq_residue_pow_finrank` : the general form,
  `residue (N_{S/R} x) = residue r ^ finrank R S` whenever `x ≡ algebraMap r (mod 𝔪_S)`.
* `IsDedekindDomain.HeightOneSpectrum.residue_norm_eq_residue_pow_finrank_of_isTotallyRamified` and
  its packaged existential form, plus
  `residue_norm_eq_residue_pow_ramificationIdx_of_isTotallyRamified` phrasing the exponent as the
  ramification index `e`.
-/

noncomputable section

open IsDedekindDomain IsLocalRing

namespace IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
  [Module.Finite R S] [Module.Free R S]

attribute [local instance] Ideal.Quotient.field

/-- **`det (c + ν) = c ^ d` for `ν` nilpotent.** Concretely: in `A := S ⧸ 𝔪_R·S` over `κ := 𝓀[R]`,
the norm of `algebraMap c + z̄` is `c ^ finrank R S`, for any `z ∈ 𝔪_S` (given a power of `𝔪_S`
inside `𝔪_R·S`, here the `finrank R S`-th, as supplied by `IsTotallyRamified.pow_finrank_le` in the
intended application).

The multiplicative counterpart of `Langlands.TotallyRamifiedTrace`'s
`trace_residue_eq_zero_of_mem_maximalIdeal`: there the nilpotence of `z̄` made the trace vanish, here
it makes the characteristic polynomial of (minus) multiplication-by-`z̄` equal `X ^ d`
(`IsNilpotent.charpoly_eq_X_pow_finrank`, applicable since `κ` is a field hence a domain), which
`LinearMap.eval_charpoly` turns into the determinant identity. Basis-free. -/
theorem norm_residue_add_eq_pow
    (hpow : maximalIdeal S ^ Module.finrank R S ≤ Ideal.map (algebraMap R S) (maximalIdeal R))
    {z : S} (hz : z ∈ maximalIdeal S) (c : R ⧸ maximalIdeal R) :
    Algebra.norm (R ⧸ maximalIdeal R)
        (algebraMap (R ⧸ maximalIdeal R) (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) c +
          Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)) z) =
      c ^ Module.finrank R S := by
  classical
  -- `A := S ⧸ 𝔪_R·S` is a finite `κ`-module: `IsLocalRing.basisQuotient` reduces a basis of `S`
  -- over `R` to one of `A` over `κ`, on the same (finite) index type. Not an instance in Mathlib,
  -- so it has to be supplied by hand before `charpoly` is available.
  haveI : Module.Finite (R ⧸ maximalIdeal R)
      (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
    Module.Finite.of_basis (IsLocalRing.basisQuotient (Module.Free.chooseBasis R S))
  set pS := Ideal.map (algebraMap R S) (maximalIdeal R) with hpSdef
  have hzn : (Ideal.Quotient.mk pS z) ^ Module.finrank R S = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hpow (Ideal.pow_mem_pow hz _)
  have hnil : IsNilpotent (Algebra.lmul (R ⧸ maximalIdeal R) (S ⧸ pS)
      (Ideal.Quotient.mk pS z)) := ⟨Module.finrank R S, by rw [← map_pow, hzn, map_zero]⟩
  rw [Algebra.norm_apply, map_add, AlgHom.commutes, ← sub_neg_eq_add, ← LinearMap.eval_charpoly,
    IsNilpotent.charpoly_eq_X_pow_finrank hnil.neg, Polynomial.eval_pow, Polynomial.eval_X,
    IsLocalRing.finrank_quotient_map]

/-- **The norm of an extension with trivial residue extension is the degree-th power on residues.**
If `x : S` is congruent mod `𝔪_S` to (the image of) `r : R`, and some power of `𝔪_S` lies in
`𝔪_R · S`, then

`residue R (Algebra.norm R x) = residue R r ^ finrank R S`.

The exact multiplicative analogue of `Langlands.TotallyRamifiedTrace`'s
`residue_trace_eq_finrank_nsmul_residue`, and, as there, the hypothesis `hx` is triviality of the
residue extension applied at the single element `x`, so no `Algebra 𝓀[R] 𝓀[S]` instance is
needed. -/
theorem residue_norm_eq_residue_pow_finrank
    (hpow : maximalIdeal S ^ Module.finrank R S ≤ Ideal.map (algebraMap R S) (maximalIdeal R))
    {x : S} {r : R} (hx : x - algebraMap R S r ∈ maximalIdeal S) :
    residue R (Algebra.norm R x) = residue R r ^ Module.finrank R S := by
  obtain ⟨z, hz, rfl⟩ : ∃ z ∈ maximalIdeal S, x = algebraMap R S r + z :=
    ⟨x - algebraMap R S r, hx, by ring⟩
  rw [show residue R (Algebra.norm R (algebraMap R S r + z)) =
      Ideal.Quotient.mk (maximalIdeal R) (Algebra.norm R (algebraMap R S r + z)) from rfl,
    residue_norm_eq_norm_residue, map_add, ← Ideal.Quotient.algebraMap_quotient_map_quotient,
    norm_residue_add_eq_pow hpow hz]
  rfl

end IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]

omit [Algebra.IsIntegral R S] in
/-- `IsLocalRing.residue_norm_eq_residue_pow_finrank` specialized to the adic-completion setting
under `IsTotallyRamified`: `N_{L₀/K₀}(x) ≡ r̄ ^ [L₀ : K₀] (mod 𝔪_K)` whenever `x ≡ r (mod 𝔪_L)`.
The `hpow` hypothesis is supplied by `IsTotallyRamified.pow_finrank_le`. -/
theorem residue_norm_eq_residue_pow_finrank_of_isTotallyRamified
    (h : IsTotallyRamified K L v w) {x : w.adicCompletionIntegers L}
    {r : v.adicCompletionIntegers K}
    (hx : x - algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) r ∈
      maximalIdeal (w.adicCompletionIntegers L)) :
    residue (v.adicCompletionIntegers K)
        (Algebra.norm (v.adicCompletionIntegers K) x) =
      residue (v.adicCompletionIntegers K) r ^
        Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  IsLocalRing.residue_norm_eq_residue_pow_finrank h.pow_finrank_le hx

omit [Algebra.IsIntegral R S] in
/-- The same with the exponent written as the ramification index `e` rather than the degree, via
`IsTotallyRamified.finrank_eq`. This is the level-`0` formula in its classical form: `N(u) ≡ ū ^ e
(mod 𝔪_K)`. -/
theorem residue_norm_eq_residue_pow_ramificationIdx_of_isTotallyRamified
    (h : IsTotallyRamified K L v w) {x : w.adicCompletionIntegers L}
    {r : v.adicCompletionIntegers K}
    (hx : x - algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) r ∈
      maximalIdeal (w.adicCompletionIntegers L)) :
    residue (v.adicCompletionIntegers K)
        (Algebra.norm (v.adicCompletionIntegers K) x) =
      residue (v.adicCompletionIntegers K) r ^ (v.asIdeal.ramificationIdx' w.asIdeal) :=
  h.finrank_eq ▸ residue_norm_eq_residue_pow_finrank_of_isTotallyRamified K L v w h hx

omit [Algebra.IsIntegral R S] in
/-- The packaged existential form: under `IsTotallyRamified`, for every `x : L₀` there is `r : K₀`
with `x ≡ r (mod 𝔪_L)` and `N_{L₀/K₀}(x) ≡ r̄ ^ [L₀ : K₀] (mod 𝔪_K)`. The witness `r` comes from
`IsTotallyRamified.exists_sub_algebraMap_mem_maximalIdeal`, i.e. from triviality of the residue
extension; `r̄` is "the residue of `x`, read in `𝓀[K]`". -/
theorem exists_residue_norm_eq_residue_pow_finrank_of_isTotallyRamified
    (h : IsTotallyRamified K L v w) (x : w.adicCompletionIntegers L) :
    ∃ r : v.adicCompletionIntegers K,
      x - algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) r ∈
          maximalIdeal (w.adicCompletionIntegers L) ∧
        residue (v.adicCompletionIntegers K)
            (Algebra.norm (v.adicCompletionIntegers K) x) =
          residue (v.adicCompletionIntegers K) r ^
            Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  obtain ⟨r, hr⟩ := h.exists_sub_algebraMap_mem_maximalIdeal x
  exact ⟨r, hr, residue_norm_eq_residue_pow_finrank_of_isTotallyRamified K L v w h hr⟩

end IsDedekindDomain.HeightOneSpectrum

end
