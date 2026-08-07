import Langlands.NormMap

/-!
# Every `y : v.adicCompletionIntegers F` is congruent mod `𝔪` to some `algebraMap A r`

Let `A` be a Dedekind domain with fraction field `F` and `v` a place of `A`. This file proves that
`algebraMap A (v.adicCompletionIntegers F)`, followed by the residue map, is surjective onto
`IsLocalRing.ResidueField (v.adicCompletionIntegers F)` — in the elementary form
`Langlands.TotallyRamifiedConcreteExample`'s remaining gap needs it in: every `y :
v.adicCompletionIntegers F` differs from (the image of) some `r : A` by an element of
`maximalIdeal (v.adicCompletionIntegers F)`.

## Proof idea

`A → v.adicCompletionIntegers F` is not the whole story; the classical fact "the residue field does
not change under completion" needs a two-step approximation, chaining two density facts already in
Mathlib that had not previously been composed in this repository:

1. `K` (here `F`) is dense in its adic completion (`IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap`),
   so `y`'s image in the completion is approximated, to any prescribed metric precision, by
   `algebraMap F (v.adicCompletion F) l` for some `l : F` (`Metric.mem_closure_iff`, using the
   `NontriviallyNormedField` structure on the completion built in `Langlands.NormMap`, whose norm
   is compatible with `Valued.v` via `Valued.toNormedField.norm_lt_one_iff`).
2. Once `l : F` is known to satisfy `v.valuation F l ≤ 1` (forced by the approximation, `y` itself
   having valuation `≤ 1`), `A` is dense in "`F`-elements of valuation `≤ 1`" in the *un-completed*
   `v`-adic topology on `F` itself (`IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer`),
   giving `r : A` with `algebraMap A F r` exactly matching `l`'s valuation-`≤ 1` approximation data.

Composing the two triangle inequalities (`y` vs. `algebraMap l`, then `algebraMap l` vs.
`algebraMap (algebraMap r)`) via the ultrametric inequality closes the gap: both differences have
valuation `< 1`, hence so does their sum, landing `y - algebraMap r` in the maximal ideal.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.exists_algebraMap_sub_mem_maximalIdeal`
-/

noncomputable section

open IsDedekindDomain IsLocalRing

open scoped WithZero Valued

namespace IsDedekindDomain.HeightOneSpectrum

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F] (v : HeightOneSpectrum A)

/-- **Every `y : v.adicCompletionIntegers F` is congruent mod `maximalIdeal` to `algebraMap A r`
for some `r : A`.** Equivalently, `algebraMap A (v.adicCompletionIntegers F)` composed with the
residue map is surjective onto `ResidueField (v.adicCompletionIntegers F)`. See the module
docstring for the two-step density argument. -/
theorem exists_algebraMap_sub_mem_maximalIdeal (y : v.adicCompletionIntegers F) :
    ∃ r : A, (y : v.adicCompletionIntegers F) - algebraMap A (v.adicCompletionIntegers F) r ∈
      maximalIdeal (v.adicCompletionIntegers F) := by
  set y' : v.adicCompletion F := (y : v.adicCompletion F) with hy'def
  have hy'le : Valued.v y' ≤ 1 := (mem_adicCompletionIntegers A F v).mp y.2
  -- The valuation of `algebraMap F (v.adicCompletion F) k` is `v.valuation F k`, for any `k : F`
  -- (the coe `(↑k : v.adicCompletion F)` used by Mathlib's `valued_coe` is definitionally the
  -- same map as `algebraMap F (v.adicCompletion F)`).
  have hval : ∀ k : F, Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
    fun k => IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe F v k
  -- Step 1: approximate `y'` by `algebraMap F (v.adicCompletion F) l`, `l : F`.
  obtain ⟨b, ⟨l, hlb⟩, hdist⟩ :=
    Metric.mem_closure_iff.mp (v.denseRange_algebraMap F y') 1 one_pos
  rw [← hlb, dist_eq_norm] at hdist
  have hlt : Valued.v (y' - algebraMap F (v.adicCompletion F) l) < 1 :=
    Valued.toNormedField.norm_lt_one_iff.mp hdist
  -- `l` also has valuation `≤ 1` (ultrametric: `algebraMap l = y' + (algebraMap l - y')`, both
  -- summands `≤ 1`).
  have hlle : Valued.v (algebraMap F (v.adicCompletion F) l) ≤ 1 := by
    have hsum : algebraMap F (v.adicCompletion F) l =
        y' + (algebraMap F (v.adicCompletion F) l - y') := by ring
    rw [hsum]
    refine le_trans (Valuation.map_add _ _ _) (max_le hy'le ?_)
    rw [Valuation.map_sub_swap]
    exact hlt.le
  have hFle : v.valuation F l ≤ 1 := (hval l) ▸ hlle
  -- Step 2: approximate `l` by `algebraMap A F r`, `r : A`, at the un-completed level.
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer hFle (1 : ℤᵐ⁰ˣ)
  refine ⟨r, ?_⟩
  have hAF : algebraMap A (v.adicCompletion F) r = algebraMap F (v.adicCompletion F)
      (algebraMap A F r) := (IsScalarTower.algebraMap_apply A F (v.adicCompletion F) r)
  have hrlt : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap A F r) -
      algebraMap F (v.adicCompletion F) l) < 1 := by
    rw [← map_sub, hval]
    simpa using hr
  have hzcoe : (((y : v.adicCompletionIntegers F) -
      algebraMap A (v.adicCompletionIntegers F) r : v.adicCompletionIntegers F) :
        v.adicCompletion F) = y' - algebraMap A (v.adicCompletion F) r := by
    rw [hy'def]
    simp only [hAF]
    rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hone : Valued.v (((y : v.adicCompletionIntegers F) -
      algebraMap A (v.adicCompletionIntegers F) r : v.adicCompletionIntegers F) :
        v.adicCompletion F) = 1 := adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hu
  rw [hzcoe, hAF] at hone
  have hsum : y' - algebraMap F (v.adicCompletion F) (algebraMap A F r) =
      (y' - algebraMap F (v.adicCompletion F) l) +
        (algebraMap F (v.adicCompletion F) l -
          algebraMap F (v.adicCompletion F) (algebraMap A F r)) := by ring
  have hlt2 : Valued.v (y' - algebraMap F (v.adicCompletion F) (algebraMap A F r)) < 1 := by
    rw [hsum]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hlt ?_)
    rwa [Valuation.map_sub_swap]
  exact absurd hone hlt2.ne

end IsDedekindDomain.HeightOneSpectrum

end
