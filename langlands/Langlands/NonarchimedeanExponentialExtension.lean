import Langlands.NonarchimedeanExponentialAdicCompletion
import Langlands.NormMap

/-!
# Wiring two fields into the exp/log machinery: shared residue characteristic across `L / K`

`Langlands.NonarchimedeanExponentialAdicCompletion` instantiates
`NonarchimedeanExponential.exp`/`.log` for `v.adicCompletionIntegers F`, but only at a **single**
place `v` of a **single** field `F` — no file in this repo's exp/log thread has ever brought two
fields `K`, `L` (an actual extension `L / K`, in the shape `Langlands.NormMap` uses throughout the
norm-map construction: `v : HeightOneSpectrum R`, `w : HeightOneSpectrum S`, `[w.asIdeal.LiesOver
v.asIdeal]`) into this machinery *together*. Stating the wild-case payoff
`N_{L/K}(exp x) = exp(Tr_{L/K}(x))` needs exactly that: `exp` instantiated compatibly at both
`v.adicCompletion K` and `w.adicCompletion L`, with the **same** residue characteristic `p` feeding
both instantiations (a finite extension of local fields always has matching residue characteristic
`p` between base and top — only `e`/`f` differ — but this repo had no lemma making that fact
available at the `HeightOneSpectrum`/`adicCompletion` level).

This file closes that one gap: the residue characteristic is shared. It does **not** attempt the
harder gap the assessment for this task surfaced independently — see "What remains" below.

## Main result

* `IsDedekindDomain.HeightOneSpectrum.charP_quotient_of_liesOver` : `[CharP (R ⧸ v.asIdeal) p] →
  CharP (S ⧸ w.asIdeal) p`, for `w.asIdeal.LiesOver v.asIdeal`. The quotient map `R ⧸ v.asIdeal →+*
  S ⧸ w.asIdeal` induced by `algebraMap R S` (`Ideal.quotientMap`, composed with the ring
  equivalence `Ideal.quotEquivOfEq` transporting along `v.asIdeal = w.asIdeal.under R`,
  `Ideal.over_def`) is injective (`Ideal.quotientMap_injective`, which applies precisely because
  `v.asIdeal` **is** `w.asIdeal`'s comap — exactly what `LiesOver` asserts), so characteristic
  transfers forward (`charP_of_injective_ringHom`). Stated as a plain theorem, not a
  typeclass-resolvable `instance`: `R` is not determined by the conclusion `CharP (S ⧸ w.asIdeal) p`
  alone, so instance search cannot find it — callers supply it explicitly (`haveI := ...`).
* `exists_maximalIdeal_pow_lt_convergenceRadius_of_liesOver` /
  `..._lt_logConvergenceRadius_of_liesOver` : combining the above with
  `Langlands.AdicCompletionMixedCharacteristic`'s `instCharPResidueFieldAdicCompletionIntegers` (at
  both `v` and `w`) and `instCharZeroAdicCompletion` (at both `K` and `L`, the latter via
  `charZero_of_algebra` in this file, itself `charZero_of_injective_algebraMap` applied to
  `algebraMap K L`) gives, from a *single* hypothesis `[CharP (R ⧸ v.asIdeal) p]` at the base,
  **both** `exp`'s (resp. `log`'s) convergence-domain existence statements for
  `v.adicCompletionIntegers K` and `w.adicCompletionIntegers L` simultaneously, for the same `p` —
  the first time this repo's exp/log machinery has been run at two fields of an actual extension at
  once.

## What remains toward item 5 (`N_{L/K}(exp x) = exp(Tr_{L/K}(x))`)

This file closes only the "shared `p`" sub-question the task's feasibility assessment flagged.
Two harder gaps remain, neither attempted here:

* **Domain compatibility.** ~~To state the formula for `x` in `exp_L`'s convergence domain, one
  needs `Tr_{L/K}(x)` to land in `exp_K`'s convergence domain.~~ **Closed** in
  `Langlands.AdicCompletionTraceBound` (`norm_trace_le`,
  `exists_maximalIdeal_pow_norm_trace_lt`), by an integrality argument rather than the analytic
  conjugates/`spectralNorm` route — see that file's docstring for why the latter is unavailable at
  this repo's normalizations. Mathlib still has no lemma connecting `Algebra.trace`/`Algebra.norm`
  to `IsUltrametricDist`; that part of this file's original assessment stands.
* **Landing in `U^{(i)}`, an explicit closed-form threshold, and the mutual-inverse identity** — items
  2–4's remaining sub-parts (`Langlands.NonarchimedeanExponentialFiltration`'s and
  `Langlands.NonarchimedeanExponential`'s "What remains" sections) are all still open and are
  prerequisites for a *sharp* version of item 5, though not for the wiring closed in this file.

`N_{L/K}(exp x) = exp(Tr_{L/K}(x))` itself is now proved, for `IsGalois K_v L_w`, in
`Langlands.AdicCompletionNormExpTrace` (`norm_exp_eq_exp_trace`); this file supplies one of its
preconditions.
-/

noncomputable section

open IsDedekindDomain IsLocalRing NonarchimedeanExponential

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

omit [IsDedekindDomain R] [IsDedekindDomain S] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S] in
/-- **The residue characteristic is shared across `w.asIdeal.LiesOver v.asIdeal`.** The quotient
map `R ⧸ v.asIdeal →+* S ⧸ w.asIdeal` induced by `algebraMap R S` is injective — `v.asIdeal` *is*
`w.asIdeal`'s comap along `algebraMap R S` (`Ideal.over_def`, unfolding `Ideal.under`), which is
exactly the condition `Ideal.quotientMap_injective` needs — so `CharP` transfers forward
(`charP_of_injective_ringHom`). -/
theorem charP_quotient_of_liesOver (p : ℕ) [CharP (R ⧸ v.asIdeal) p] :
    CharP (S ⧸ w.asIdeal) p := by
  have hv : v.asIdeal = Ideal.comap (algebraMap R S) w.asIdeal := Ideal.over_def w.asIdeal v.asIdeal
  have hinj : Function.Injective
      ((Ideal.quotientMap w.asIdeal (algebraMap R S) (le_refl _)).comp
        (Ideal.quotEquivOfEq hv).toRingHom) :=
    (Ideal.quotientMap_injective (I := w.asIdeal) (f := algebraMap R S)).comp
      (Ideal.quotEquivOfEq hv).injective
  exact charP_of_injective_ringHom hinj p

omit [Module.Finite K L] in
/-- **`L` has characteristic zero whenever `K` does**, along the extension `[Algebra K L]`:
`algebraMap K L` is injective (`K` is a field, hence `IsSimpleRing`, into the nontrivial ring `L`),
and `CharZero` transfers forward along an injective ring hom
(`charZero_of_injective_algebraMap`) — the same one-line argument
`Langlands.AdicCompletionMixedCharacteristic.instCharZeroAdicCompletion` uses one level up, applied
here at the level of `K`/`L` themselves rather than their completions. -/
theorem charZero_of_algebra [CharZero K] : CharZero L :=
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap K L))

omit [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [Module.Finite K L]
  [Algebra.IsIntegral R S] [Module.IsTorsionFree R S] in
/-- **Both `exp`'s convergence-domain existence statements, for `v` and for `w`, from a single
hypothesis at the base.** Given `[CharZero K]` and `[CharP (R ⧸ v.asIdeal) p]`, both
`v.adicCompletionIntegers K` and `w.adicCompletionIntegers L` get the residue-characteristic-`p`
and `CharZero` instances `NonarchimedeanExponentialAdicCompletion`'s machinery needs
(`charZero_of_algebra` and `AdicCompletionMixedCharacteristic`'s instances chain through
automatically for `L`, using `charP_quotient_of_liesOver` for the shared `p`), so `exp`'s
convergence-domain existence statement holds at both places simultaneously, for the same `p`. -/
theorem exists_maximalIdeal_pow_lt_convergenceRadius_of_liesOver
    (p : ℕ) [Fact p.Prime] [CharZero K] [CharP (R ⧸ v.asIdeal) p] :
    (∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x : v.adicCompletionIntegers K,
      x ∈ maximalIdeal (v.adicCompletionIntegers K) ^ i →
        ‖(x : v.adicCompletion K)‖ < convergenceRadius (v.adicCompletion K) p) ∧
    (∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x : w.adicCompletionIntegers L,
      x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i →
        ‖(x : w.adicCompletion L)‖ < convergenceRadius (w.adicCompletion L) p) := by
  haveI := charZero_of_algebra K L
  haveI := charP_quotient_of_liesOver v w p
  exact ⟨exists_maximalIdeal_pow_lt_convergenceRadius v p,
    exists_maximalIdeal_pow_lt_convergenceRadius w p⟩

omit [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [Module.Finite K L]
  [Algebra.IsIntegral R S] [Module.IsTorsionFree R S] in
/-- The `log`-domain analogue of `exists_maximalIdeal_pow_lt_convergenceRadius_of_liesOver`. -/
theorem exists_maximalIdeal_pow_lt_logConvergenceRadius_of_liesOver
    (p : ℕ) [Fact p.Prime] [CharZero K] [CharP (R ⧸ v.asIdeal) p] :
    (∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x : v.adicCompletionIntegers K,
      x ∈ maximalIdeal (v.adicCompletionIntegers K) ^ i →
        ‖(x : v.adicCompletion K)‖ < logConvergenceRadius (v.adicCompletion K) p) ∧
    (∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x : w.adicCompletionIntegers L,
      x ∈ maximalIdeal (w.adicCompletionIntegers L) ^ i →
        ‖(x : w.adicCompletion L)‖ < logConvergenceRadius (w.adicCompletion L) p) := by
  haveI := charZero_of_algebra K L
  haveI := charP_quotient_of_liesOver v w p
  exact ⟨exists_maximalIdeal_pow_lt_logConvergenceRadius v p,
    exists_maximalIdeal_pow_lt_logConvergenceRadius w p⟩

end IsDedekindDomain.HeightOneSpectrum

end
