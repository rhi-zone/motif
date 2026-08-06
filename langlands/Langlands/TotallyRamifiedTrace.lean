import Langlands.NormTraceLinearization
import Langlands.TotallyRamifiedValuationExtension

/-!
# The trace of a totally ramified extension is multiplication by the degree

For `L₀ / K₀` a finite free extension of local rings whose residue extension is *trivial*, the
ring trace reduces mod `𝔪_K` to multiplication by the degree:

`Tr_{L₀/K₀}(x) ≡ [L₀ : K₀] · x̄ (mod 𝔪_K)`.

This is the totally-ramified counterpart of `Langlands.NormTraceLinearization`'s
`residue_trace_eq_trace_residue_of_isUnramified` (which reduces the trace to the residue-field
trace `𝓀[L] → 𝓀[K]`, a statement with no content here since `𝓀[L] = 𝓀[K]`), and closes gaps 3 and
4 of `ROADMAP.md` Phase 2b's thirty-ninth-pass entry.

## Route

The thirty-ninth pass derived this formula by hand and proposed two proof routes — Newton's
identities on the Eisenstein minimal polynomial, or the reduced companion matrix. **Neither is used
here**, and in particular the Eisenstein/monogenicity presentation of `O_L = O_K[π_L]` is *not*
needed: gap 3 (threading `Langlands.TotallyRamifiedEisenstein`'s abstract `ValuativeRel`/
`spectralNorm` bundle into the `HeightOneSpectrum` adic-completion setting, flagged as the riskiest
unknown) is *avoided*, not closed. See "## Why no Eisenstein presentation is needed" below.

The route actually taken works with the Artinian quotient `A := L₀ ⧸ 𝔪_K·L₀` directly:

1. `IsLocalRing.residue_trace_eq_trace_residue` (already proved, in
   `Langlands.NormTraceLinearization`, with no unramified hypothesis anywhere): the ring trace
   commutes with reduction, `residue (Tr_{L₀/K₀} x) = Tr_{A/κ}(x mod 𝔪_K·L₀)` where
   `κ := 𝓀[K] = K₀ ⧸ 𝔪_K`.
2. Triviality of the residue extension says every `x : L₀` can be written `x = algebraMap r + z`
   with `r : K₀` and `z ∈ 𝔪_L`. Trace is additive, so the two summands can be handled separately.
3. `Algebra.trace_algebraMap` handles the first summand exactly: `Tr_{A/κ}(algebraMap c) =
   finrank κ A • c`, and `IsLocalRing.finrank_quotient_map` identifies `finrank κ A` with
   `finrank K₀ L₀` — no basis of `A` is ever constructed or named.
4. The second summand contributes `0`: `z ∈ 𝔪_L` and `𝔪_L ^ [L₀:K₀] ≤ 𝔪_K·L₀`
   (`IsTotallyRamified.pow_finrank_le`) make `z` *nilpotent in `A`*, hence multiplication by `z` a
   nilpotent `κ`-endomorphism of `A`, hence of trace `0` (`LinearMap.isNilpotent_trace_of_isNilpotent`
   plus `IsNilpotent.eq_zero`, `κ` being a field and so reduced).

## Why no Eisenstein presentation is needed

The companion-matrix route the thirty-ninth pass proposed computes `Tr(π_L^k)` for `0 ≤ k ≤ e-1`
individually, which is why it wants the power basis `1, π_L, …, π_L^{e-1}` — i.e. monogenicity.
Step 4 above sidesteps this: *every* element of `𝔪_L` reduces to a nilpotent of `A` at once, and
"the trace of a nilpotent endomorphism vanishes" is basis-free. The three facts about `A` the
argument does consume — that it is finite free over `κ` of rank `[L₀ : K₀]`, that `κ → A` is a
section of `A ↠ 𝓀[L]`, and that `𝔪_L·A` is nilpotent — are exactly what
`Langlands.TotallyRamifiedValuationExtension`'s `IsTotallyRamified` records, and none of them
requires a generator of `A` over `κ`.

What is genuinely lost relative to the companion-matrix route: nothing that the downstream
norm-group argument uses. What is *not* obtained (and would still need Eisenstein): the individual
values `Tr(π_L^k) ∈ 𝔪_K` for `1 ≤ k ≤ e-1`, and the graded structure `A ≅ κ[T]/(T^e)`.

## Main results

* `IsLocalRing.trace_residue_eq_zero_of_mem_maximalIdeal` : the trace of (the reduction of) an
  element of `𝔪_S` vanishes, given a power of `𝔪_S` inside `𝔪_R·S`. General; no residue-extension
  hypothesis.
* `IsLocalRing.residue_trace_eq_finrank_nsmul_residue` : the general form of the trace formula,
  `residue (Tr_{S/R} x) = finrank R S • residue r` whenever `x ≡ algebraMap r (mod 𝔪_S)`.
* `IsDedekindDomain.HeightOneSpectrum.residue_trace_eq_finrank_nsmul_residue_of_isTotallyRamified` :
  its adic-completion specialization under `IsTotallyRamified`.
* `IsDedekindDomain.HeightOneSpectrum.exists_norm_one_add_uniformizer_pow_smul_eq_finrank_nsmul` :
  **the graded-piece formula.** Combining the above with `Algebra.exists_norm_one_add_smul_eq`
  (reused verbatim from `Langlands.NormTraceLinearization`, no new derivation): for `π` a
  uniformizer of `K₀`, `N_{L₀/K₀}(1 + π^{n+1} • x) = 1 + π^{n+1} · y` with
  `ȳ = [L₀ : K₀] · r̄`. So the map induced on the `(n+1)`-st graded piece is **multiplication by
  the degree** on `κ` — the totally-ramified replacement for the residue-field trace
  `Algebra.trace 𝓀[K] 𝓀[L]` of the unramified case.
-/

noncomputable section

open IsDedekindDomain IsLocalRing

namespace IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
  [Module.Finite R S] [Module.Free R S]

attribute [local instance] Ideal.Quotient.field

omit [Module.Finite R S] [Module.Free R S] in
/-- The trace over `𝓀[R] = R ⧸ 𝔪_R` of (the reduction of) an element `z ∈ 𝔪_S` vanishes, provided
some power of `𝔪_S` is contained in `𝔪_R · S` — here the `finrank R S`-th, the exponent supplied
by `IsTotallyRamified.pow_finrank_le` in the intended application.

The containment makes `z` nilpotent in `A := S ⧸ 𝔪_R·S`, so multiplication by `z` is a nilpotent
`𝓀[R]`-endomorphism of `A`; a nilpotent endomorphism has nilpotent trace
(`LinearMap.isNilpotent_trace_of_isNilpotent`), and `𝓀[R]` is a field, hence reduced. Basis-free:
no power basis or companion matrix for `A` is constructed. -/
theorem trace_residue_eq_zero_of_mem_maximalIdeal
    (hpow : maximalIdeal S ^ Module.finrank R S ≤ Ideal.map (algebraMap R S) (maximalIdeal R))
    {z : S} (hz : z ∈ maximalIdeal S) :
    Algebra.trace (R ⧸ maximalIdeal R) (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)) z) = 0 := by
  set pS := Ideal.map (algebraMap R S) (maximalIdeal R) with hpSdef
  have hzn : (Ideal.Quotient.mk pS z) ^ Module.finrank R S = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hpow (Ideal.pow_mem_pow hz _)
  have hnil : IsNilpotent (Algebra.lmul (R ⧸ maximalIdeal R) (S ⧸ pS)
      (Ideal.Quotient.mk pS z)) := ⟨Module.finrank R S, by rw [← map_pow, hzn, map_zero]⟩
  rw [Algebra.trace_apply]
  exact IsNilpotent.eq_zero (LinearMap.isNilpotent_trace_of_isNilpotent hnil)

/-- **The trace of an extension with trivial residue extension is multiplication by the degree.**
If `x : S` is congruent mod `𝔪_S` to (the image of) `r : R`, and some power of `𝔪_S` lies in
`𝔪_R · S`, then

`residue R (Algebra.trace R S x) = finrank R S • residue R r`.

The hypothesis `hx` is exactly triviality of the residue extension, applied at the single element
`x`; taking it as a hypothesis (rather than assuming `𝓀[R] → 𝓀[S]` surjective globally) keeps the
statement independent of any `Algebra 𝓀[R] 𝓀[S]` instance.

Proof: `residue_trace_eq_trace_residue` moves everything into `A := S ⧸ 𝔪_R·S` over `κ := 𝓀[R]`;
additivity of the trace splits `x = algebraMap r + z` with `z ∈ 𝔪_S`; `Algebra.trace_algebraMap`
evaluates the first summand as `finrank κ A • r̄` (rewritten by `finrank_quotient_map` to
`finrank R S • r̄`), and `trace_residue_eq_zero_of_mem_maximalIdeal` kills the second. -/
theorem residue_trace_eq_finrank_nsmul_residue
    (hpow : maximalIdeal S ^ Module.finrank R S ≤ Ideal.map (algebraMap R S) (maximalIdeal R))
    {x : S} {r : R} (hx : x - algebraMap R S r ∈ maximalIdeal S) :
    residue R (Algebra.trace R S x) = Module.finrank R S • residue R r := by
  obtain ⟨z, hz, rfl⟩ : ∃ z ∈ maximalIdeal S, x = algebraMap R S r + z :=
    ⟨x - algebraMap R S r, hx, by ring⟩
  rw [show residue R (Algebra.trace R S (algebraMap R S r + z)) =
      Ideal.Quotient.mk (maximalIdeal R) (Algebra.trace R S (algebraMap R S r + z)) from rfl,
    residue_trace_eq_trace_residue, map_add, map_add,
    trace_residue_eq_zero_of_mem_maximalIdeal hpow hz, add_zero,
    ← Ideal.Quotient.algebraMap_quotient_map_quotient, Algebra.trace_algebraMap,
    IsLocalRing.finrank_quotient_map]
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
/-- `IsLocalRing.residue_trace_eq_finrank_nsmul_residue` specialized to the adic-completion setting
under `IsTotallyRamified`: `Tr_{L₀/K₀}(x) ≡ [L₀ : K₀] · r̄ (mod 𝔪_K)` whenever `x ≡ r (mod 𝔪_L)`.

The `hpow` hypothesis of the general lemma is supplied by `IsTotallyRamified.pow_finrank_le`, and
the witness `r` by `IsTotallyRamified.exists_sub_algebraMap_mem_maximalIdeal` (see
`residue_trace_eq_finrank_nsmul_residue_of_isTotallyRamified'` for the packaged existential
form). -/
theorem residue_trace_eq_finrank_nsmul_residue_of_isTotallyRamified
    (h : IsTotallyRamified K L v w) {x : w.adicCompletionIntegers L}
    {r : v.adicCompletionIntegers K}
    (hx : x - algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) r ∈
      maximalIdeal (w.adicCompletionIntegers L)) :
    residue (v.adicCompletionIntegers K)
        (Algebra.trace (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) x) =
      Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) •
        residue (v.adicCompletionIntegers K) r :=
  IsLocalRing.residue_trace_eq_finrank_nsmul_residue h.pow_finrank_le hx

omit [Algebra.IsIntegral R S] in
/-- The packaged existential form: under `IsTotallyRamified`, for every `x : L₀` there is `r : K₀`
with `x ≡ r (mod 𝔪_L)` and `Tr_{L₀/K₀}(x) ≡ [L₀ : K₀] · r̄ (mod 𝔪_K)`. -/
theorem exists_residue_trace_eq_finrank_nsmul_residue_of_isTotallyRamified
    (h : IsTotallyRamified K L v w) (x : w.adicCompletionIntegers L) :
    ∃ r : v.adicCompletionIntegers K,
      x - algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) r ∈
          maximalIdeal (w.adicCompletionIntegers L) ∧
        residue (v.adicCompletionIntegers K)
            (Algebra.trace (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) x) =
          Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) •
            residue (v.adicCompletionIntegers K) r := by
  obtain ⟨r, hr⟩ := h.exists_sub_algebraMap_mem_maximalIdeal x
  exact ⟨r, hr, residue_trace_eq_finrank_nsmul_residue_of_isTotallyRamified K L v w h hr⟩

omit [Algebra.IsIntegral R S] in
/-- **The norm linearizes to multiplication by the degree on the graded pieces of the
principal-units filtration, for a totally ramified extension.** Let `π` be a uniformizer of `K₀`.
Under `IsTotallyRamified`, for every `n : ℕ`, every `x : L₀` and every `r : K₀` with
`x ≡ r (mod 𝔪_L)`, there is `y : K₀` with

* `Algebra.norm K₀ (1 + π ^ (n+1) • x) = 1 + π ^ (n+1) * y`, and
* `residue K₀ y = [L₀ : K₀] • residue K₀ r`.

This is the exact totally-ramified analogue of `Langlands.NormTraceLinearization`'s
`exists_norm_one_add_uniformizer_pow_smul_eq_trace_add`, with the residue-field trace
`Algebra.trace 𝓀[K] 𝓀[L]` — which carries no information here, `𝓀[L]` and `𝓀[K]` being the same
field — replaced by multiplication by `[L₀ : K₀]` (`= e`, by `IsTotallyRamified.finrank_eq`).

The proof reuses `Algebra.exists_norm_one_add_smul_eq` verbatim: that determinant-Taylor lemma
carries no unramifiedness hypothesis, and its scalar `t := π ^ (n+1)` lives in the *base* `K₀`, so
the only thing that changes between the two cases is the trace computation. Note the resulting
index correspondence on the `L` side is `i_L = e · (n+1)`, not `n+1`, since `π^{n+1} • L₀` is
`𝔪_L ^ (e·(n+1))` under `IsTotallyRamified.map_maximalIdeal_eq` — but that description is not
needed by this statement, which quantifies over all `x : L₀` directly. -/
theorem exists_norm_one_add_uniformizer_pow_smul_eq_finrank_nsmul
    (h : IsTotallyRamified K L v w) {π : v.adicCompletionIntegers K} (hπ : Irreducible π) (n : ℕ)
    {x : w.adicCompletionIntegers L} {r : v.adicCompletionIntegers K}
    (hx : x - algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) r ∈
      maximalIdeal (w.adicCompletionIntegers L)) :
    ∃ y : v.adicCompletionIntegers K,
      Algebra.norm (v.adicCompletionIntegers K) (1 + π ^ (n + 1) • x) = 1 + π ^ (n + 1) * y ∧
        residue (v.adicCompletionIntegers K) y =
          Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) •
            residue (v.adicCompletionIntegers K) r := by
  obtain ⟨c, hc⟩ := Algebra.exists_norm_one_add_smul_eq (R := v.adicCompletionIntegers K)
    (S := w.adicCompletionIntegers L) (π ^ (n + 1) : v.adicCompletionIntegers K) x
  refine ⟨Algebra.trace (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) x
    + π ^ (n + 1) * c, ?_, ?_⟩
  · rw [hc]; ring
  · have hπmem : π ∈ maximalIdeal (v.adicCompletionIntegers K) :=
      hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
    have hπnmem : π ^ (n + 1) ∈ maximalIdeal (v.adicCompletionIntegers K) :=
      Ideal.pow_mem_of_mem _ hπmem (n + 1) n.succ_pos
    have hres0 : residue (v.adicCompletionIntegers K) (π ^ (n + 1)) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hπnmem
    rw [map_add, map_mul, hres0, zero_mul, add_zero]
    exact residue_trace_eq_finrank_nsmul_residue_of_isTotallyRamified K L v w h hx

end IsDedekindDomain.HeightOneSpectrum

end
