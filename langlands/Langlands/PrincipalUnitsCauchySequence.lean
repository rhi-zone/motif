import Langlands.NormTraceLinearization
import Langlands.UnitGroupModPrincipalUnitsSurjective
import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Perfect

/-!
# One-step correction on the principal-units filtration

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`, `𝓀[K] := IsLocalRing.ResidueField K₀`,
`𝓀[L] := IsLocalRing.ResidueField L₀`. This file proves the single Hensel-lift correction step of
the successive-approximation argument sketched in `ROADMAP.md`'s Phase 2a "sixth pass" entry, step
3: given a target residual error `t : K₀` at filtration level `n`, there is `z : L₀` correcting it
to filtration level `n+1`, i.e. `Algebra.norm K₀ (1 + π^{n+1}•z) ≡ 1 + π^{n+1}·t \pmod{π^{n+2}}`.

## Route

Given `t : K₀`, `Algebra.trace_surjective` on the residue-field extension `𝓀[L]/𝓀[K]` (available
once `𝓀[L]` is finite: `𝓀[K]` is then also finite, by injectivity of `algebraMap 𝓀[K] 𝓀[L]`, hence
`PerfectField 𝓀[K]`, hence `Algebra.IsSeparable 𝓀[K] 𝓀[L]`, via Mathlib's general
`Algebra.IsAlgebraic.isSeparable_of_perfectField`) gives `w̄ : 𝓀[L]` with
`Algebra.trace 𝓀[K] 𝓀[L] w̄ = residue K₀ t`. Lifting `w̄` to `z : L₀` (`IsLocalRing.residue_surjective`)
and feeding it into `exists_norm_one_add_uniformizer_pow_smul_eq_trace_add`
(`Langlands.NormTraceLinearization`) gives `y : K₀` with `Algebra.norm K₀ (1+π^{n+1}•z) = 1+π^{n+1}·y`
and `residue K₀ y = residue K₀ t`, i.e. `y - t ∈ 𝔪_K = span{π}`; multiplying through by `π^{n+1}`
upgrades this to the claimed `mod π^{n+2}` congruence.

## Main result

* `IsDedekindDomain.HeightOneSpectrum.exists_one_add_uniformizer_pow_smul_norm_sub_mem`
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

omit [Algebra.IsIntegral R S] in
/-- **The one-step Hensel-lift correction on the principal-units filtration.** Under
`IsUnramified`, with `𝓀[L]` finite, for `π` a uniformizer of `K₀`, `n : ℕ`, and `t : K₀`: there is
`z : L₀` with `Algebra.norm K₀ (1 + π^{n+1}•z) ≡ 1 + π^{n+1}·t \pmod{π^{n+2}}`.

Read against the successive-approximation sketch: if `N(x) ≡ y \pmod{π^{n+1}}`, writing
`y·N(x)⁻¹ = 1 + π^{n+1}·t`, this `z` gives `x' := x·(1+π^{n+1}•z)` with `N(x') ≡ y \pmod{π^{n+2}}` —
one filtration level closer. -/
theorem exists_one_add_uniformizer_pow_smul_norm_sub_mem
    [Finite (ResidueField (w.adicCompletionIntegers L))] (hU : IsUnramified K L v w)
    {π : v.adicCompletionIntegers K} (hπ : Irreducible π) (n : ℕ)
    (t : v.adicCompletionIntegers K) :
    ∃ z : w.adicCompletionIntegers L,
      Algebra.norm (v.adicCompletionIntegers K) (1 + π ^ (n + 1) • z) -
          (1 + π ^ (n + 1) * t) ∈ Ideal.span {π ^ (n + 2)} := by
  classical
  -- `𝓀[K]` is finite: it injects into the finite field `𝓀[L]`.
  haveI hfinK : Finite (ResidueField (v.adicCompletionIntegers K)) :=
    Finite.of_injective
      (algebraMap (ResidueField (v.adicCompletionIntegers K))
        (ResidueField (w.adicCompletionIntegers L)))
      (algebraMap (ResidueField (v.adicCompletionIntegers K))
        (ResidueField (w.adicCompletionIntegers L))).injective
  haveI : PerfectField (ResidueField (v.adicCompletionIntegers K)) := PerfectField.ofFinite
  haveI : Module.Finite (ResidueField (v.adicCompletionIntegers K))
      (ResidueField (w.adicCompletionIntegers L)) :=
    Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ResidueField (v.adicCompletionIntegers K))
      (ResidueField (w.adicCompletionIntegers L)) := .of_finite _ _
  haveI : Algebra.IsSeparable (ResidueField (v.adicCompletionIntegers K))
      (ResidueField (w.adicCompletionIntegers L)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- Lift `residue K₀ t` along the trace of the residue-field extension.
  obtain ⟨wbar, hwbar⟩ := Algebra.trace_surjective (ResidueField (v.adicCompletionIntegers K))
    (ResidueField (w.adicCompletionIntegers L)) (residue (v.adicCompletionIntegers K) t)
  obtain ⟨z, hz⟩ := IsLocalRing.residue_surjective (R := w.adicCompletionIntegers L) wbar
  obtain ⟨y, hy, hyres⟩ :=
    exists_norm_one_add_uniformizer_pow_smul_eq_trace_add K L v w hU hπ n z
  refine ⟨z, ?_⟩
  have hyt : residue (v.adicCompletionIntegers K) y = residue (v.adicCompletionIntegers K) t := by
    rw [hyres, hz, hwbar]
  have hsub : y - t ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (Ideal.Quotient.eq).mp hyt
  have hspan : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {π} := hπ.maximalIdeal_eq
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hspan ▸ hsub)
  have : Algebra.norm (v.adicCompletionIntegers K) (1 + π ^ (n + 1) • z) -
      (1 + π ^ (n + 1) * t) = π ^ (n + 2) * c := by
    rw [hy]
    have hyt' : y = t + c * π := by linear_combination -hc
    rw [hyt']; ring
  rw [this]
  exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩

end IsDedekindDomain.HeightOneSpectrum

end
