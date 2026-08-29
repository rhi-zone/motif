import Langlands.UnramifiedValuationExtension

/-!
# Total ramification for valuation-ring extensions

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`. This file defines `IsTotallyRamified`, the `e = [L₀ : K₀]`
counterpart of `Langlands.UnramifiedValuationExtension`'s `IsUnramified` (`e = 1`) — no such
predicate existed elsewhere in this repo's adic-completion vocabulary.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.IsTotallyRamified` : a three-field `Prop`-valued structure
  packaging the classical content of "`L₀ / K₀` is totally ramified", with
  `e := v.asIdeal.ramificationIdx' w.asIdeal` (the ramification index already computed and used by
  `Langlands.NormMap`'s `adicCompletionIntegers_comap_eq`):
  1. `map_maximalIdeal_eq` : `𝔪_K · O_L = 𝔪_L ^ e` — the index correspondence. For `e = 1` this is
     literally `IsUnramified`.
  2. `finrank_eq` : `[L₀ : K₀] = e` — total ramification proper (`f = 1` in `e·f = n`).
  3. `exists_sub_algebraMap_mem_maximalIdeal` : the residue extension `𝓀[K] → 𝓀[L]` is trivial,
     in the elementary form "every `y : L₀` is congruent mod `𝔪_L` to an element of `K₀`".

## Design note: why three fields, and why the third is not derived

Classically, (3) follows from (1) and (2) via the fundamental identity `e·f = n` for a finite
extension of complete discrete valuation rings — `f = n / e = 1`, so `𝓀[L] = 𝓀[K]`. That identity
is not available in this repository for `K₀ → L₀` — even "the totally ramified case has equal
residue fields" is nowhere verified here — and deriving it is a self-contained piece of work of its
own. Rather than weaken the predicate to what happens to be cheap, all three classical components
are recorded as fields; a future development that proves `e·f = n` in this setting can drop (3) to
a theorem and re-derive it, with no change to any consumer's statement.

Similarly, `finrank_eq` is stated with `Module.finrank K₀ L₀` on the left rather than
`Module.finrank K L`: `Langlands.AdicCompletionIntegralClosure` supplies `Module.Free K₀ L₀`, so it
is the completed-module rank that the trace computations downstream
(`Langlands.TotallyRamifiedTrace`) actually consume.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.IsTotallyRamified.pow_finrank_le` : `𝔪_L ^ [L₀ : K₀] ≤
  𝔪_K · O_L`, the one consequence of `map_maximalIdeal_eq`/`finrank_eq` that the trace argument
  needs (it only ever uses `≤`, and only ever at the exponent `[L₀ : K₀]`).
* `IsDedekindDomain.HeightOneSpectrum.isUnramified_of_isTotallyRamified_of_finrank_eq_one` : a
  totally ramified extension of degree `1` is unramified — the sanity check that the two predicates
  agree where they overlap.
-/

noncomputable section

open IsDedekindDomain IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

/-- **The extension `L₀ / K₀` is totally ramified.** Writing `e := v.asIdeal.ramificationIdx'
w.asIdeal` for the ramification index (the same `e` `Langlands.NormMap`'s
`adicCompletionIntegers_comap_eq` uses), this bundles the three classical components: the index
correspondence `𝔪_K · O_L = 𝔪_L ^ e`, the degree equality `[L₀ : K₀] = e`, and triviality of the
residue extension. See the module docstring for why the third is a field rather than a derived
theorem. -/
structure IsTotallyRamified : Prop where
  /-- `𝔪_K · O_L = 𝔪_L ^ e`: the maximal ideal of the base generates exactly the `e`-th power of
  the maximal ideal of the top. The `e = 1` case is `IsUnramified`. -/
  map_maximalIdeal_eq :
    Ideal.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L))
        (maximalIdeal (v.adicCompletionIntegers K)) =
      maximalIdeal (w.adicCompletionIntegers L) ^ (v.asIdeal.ramificationIdx' w.asIdeal)
  /-- `[L₀ : K₀] = e`: the ramification index exhausts the degree, i.e. the residue degree is `1`.
  This is what makes the extension *totally* ramified rather than merely ramified. -/
  finrank_eq :
    Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      v.asIdeal.ramificationIdx' w.asIdeal
  /-- The residue extension `𝓀[K] → 𝓀[L]` is trivial: every `y : L₀` differs from (the image of)
  some `r : K₀` by an element of `𝔪_L`. Equivalently, `algebraMap 𝓀[K] 𝓀[L]` is surjective — stated
  in this elementary form to avoid depending on the `Algebra 𝓀[K] 𝓀[L]` instance. -/
  exists_sub_algebraMap_mem_maximalIdeal :
    ∀ y : w.adicCompletionIntegers L, ∃ r : v.adicCompletionIntegers K,
      y - algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) r ∈
        maximalIdeal (w.adicCompletionIntegers L)

variable {K L v w}

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- `𝔪_L ^ [L₀ : K₀] ≤ 𝔪_K · O_L`. Combining `map_maximalIdeal_eq` and `finrank_eq`: the exponent
`e` in the former is rewritten to `[L₀ : K₀]` by the latter, and the resulting equality is weakened
to `≤`. This is the only form in which `Langlands.TotallyRamifiedTrace` consumes total ramification
— it needs a power of `𝔪_L` inside `𝔪_K · O_L` (to make `𝔪_L / 𝔪_K·O_L` nilpotent), not the exact
equality. -/
theorem IsTotallyRamified.pow_finrank_le (h : IsTotallyRamified K L v w) :
    maximalIdeal (w.adicCompletionIntegers L) ^
        Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) ≤
      Ideal.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L))
        (maximalIdeal (v.adicCompletionIntegers K)) :=
  le_of_eq (by rw [h.finrank_eq, h.map_maximalIdeal_eq])

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- A totally ramified extension of degree `1` is unramified — the sanity check that
`IsTotallyRamified` and `IsUnramified` agree where they overlap (`e = f = 1`). -/
theorem isUnramified_of_isTotallyRamified_of_finrank_eq_one (h : IsTotallyRamified K L v w)
    (h1 : Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) = 1) :
    IsUnramified K L v w := by
  have he : v.asIdeal.ramificationIdx' w.asIdeal = 1 := h.finrank_eq ▸ h1
  rw [IsUnramified, h.map_maximalIdeal_eq, he, pow_one]

end IsDedekindDomain.HeightOneSpectrum

end
