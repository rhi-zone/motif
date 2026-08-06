import Langlands.TotallyRamifiedNormSurjective
import Langlands.PrincipalUnitsFiltrationAdicCompletion
import Langlands.UnramifiedNormRange

/-!
# The tame totally ramified norm group contains `⟨N(π_L)⟩ · U_K^{(1)}`

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`. This file combines the two halves of Phase 2b's totally
ramified norm-group theorem into one containment of subgroups of `(v.adicCompletion K)ˣ`:

`Subgroup.zpowers (N(π_L)) ⊔ U_K^{(1)} ≤ MonoidHom.range (localNormMap K L v w)`

under `IsTotallyRamified` and `IsTamelyRamified`, where `π_L` is any uniformizer of `L₀`.

## This is `⊇`, not `=`

Only the containment is proved. `N_{L/K}(U_L)` is strictly larger than `U_K^{(1)}` in general (it
is the set of units whose residue is an `e`-th power of `𝓀[K]ˣ` — see
`Langlands.TotallyRamifiedNormResidue`'s
`residue_norm_eq_residue_pow_ramificationIdx_of_isTotallyRamified`, which proves the `⊆` half of
that description), and the *unit* half of the norm group is only known here to *contain*
`U_K^{(1)}`: the matching surjectivity at level `0` is not formalized. So the `⊔` here is
genuinely smaller than `MonoidHom.range (localNormMap K L v w)`, and nothing stronger is claimed. Contrast `Langlands.UnramifiedNormRange`'s `localNormMap_range_eq`, an equality,
available there because the unramified unit half is all of `O_K^×`.

## `N(π_L)` is a uniformizer of `K₀`: proved concretely, not by instantiating the abstract bundle

`Langlands.TotallyRamifiedEisenstein`'s `LocalField.norm_isUniformizer_eq_of_isUniformizer` proves
`‖Algebra.norm K π‖ = ‖ϖ‖` in the abstract `ValuativeRel`/`spectralNorm` bundle, via the Eisenstein
minimal polynomial and `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly`. Instantiating it here
would require, besides the instance bundle on `v.adicCompletion K` / `w.adicCompletion L`,
producing its two hypotheses: `hram : ‖(ϖ : K)‖ = spectralNorm K L π ^ (minpoly K π).natDegree`
(which needs `spectralNorm_unique_field_norm_ext` to identify `spectralNorm` with the adic norm
already on `w.adicCompletion L`, then a translation of `IsTotallyRamified` into that norm equation)
and `hgen : (minpoly K π).natDegree = Module.finrank K L` (i.e. `π_L` generates `L_w` over `K_v`,
which is *not* part of `IsTotallyRamified` and would itself have to be derived).

None of that is needed. In the concrete setting the statement is available from
`IsTotallyRamified`'s own two ideal-theoretic fields by a short divisibility argument, and in a
*stronger* form (`Associated (N(π_L)) π_K`, i.e. `N(π_L)` generates `𝔪_K` on the nose, rather than
an equality of real norms):

* `map_maximalIdeal_eq` says `𝔪_K · L₀ = 𝔪_L ^ e`; rewriting both sides as principal ideals
  (`Irreducible.maximalIdeal_eq`, `Ideal.map_span`, `Ideal.span_singleton_pow`) and applying
  `Ideal.span_singleton_eq_span_singleton` gives `Associated (algebraMap π_K) (π_L ^ e)` in `L₀`.
* `Algebra.norm K₀` is a `MonoidHom`, so it preserves `Associated` (`Associated.map`);
  `Algebra.norm_algebraMap` (available since `L₀` is `Module.Free` over `K₀`, from
  `Langlands.AdicCompletionIntegralClosure`) evaluates the left side as `π_K ^ [L₀:K₀]`, which
  `finrank_eq` rewrites to `π_K ^ e`.
* `Associated.pow_iff` (valid since `K₀` is an integrally closed domain) cancels the common
  exponent `e`, which is nonzero by
  `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver`.

So `norm_isUniformizer_eq_of_isUniformizer` is **not** used by this file, and no bridging between
the `HeightOneSpectrum` and `ValuativeRel` settings is performed. That bridging remains open as a
task in its own right (`ROADMAP.md` Phase 2b, thirty-ninth pass's gap 3); it is simply not a
prerequisite for the result proved here.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.associated_norm_uniformizer_of_isTotallyRamified`
* `IsDedekindDomain.HeightOneSpectrum.irreducible_norm_of_isTotallyRamified`
* `IsDedekindDomain.HeightOneSpectrum.principalUnitsPowKField` : `U_K^{(i)}` pushed forward from
  `K₀ˣ` (where `Langlands.PrincipalUnitsFiltrationAdicCompletion` defines it) to
  `(v.adicCompletion K)ˣ`, along `Units.map (algebraMap K₀ K_v)` — the same embedding
  `Langlands.UnramifiedNormRange` uses for `(v.adicCompletionIntegers K).units`.
* `IsDedekindDomain.HeightOneSpectrum.localNormMap_range_ge_of_isTotallyRamified`
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

/-! ### `N(π_L)` is a uniformizer of `K₀` -/

omit [Algebra.IsIntegral R S] in
/-- **The norm of a uniformizer of `L₀` is a uniformizer of `K₀`, in `Associated` form.** For `π_L`
irreducible in `L₀` and `π` irreducible in `K₀`, `Algebra.norm K₀ π_L` is associated to `π` — i.e.
it generates `𝔪_K`.

See the module docstring for why this is proved directly from `IsTotallyRamified`'s ideal-theoretic
fields rather than by instantiating `Langlands.TotallyRamifiedEisenstein`'s
`norm_isUniformizer_eq_of_isUniformizer`. -/
theorem associated_norm_uniformizer_of_isTotallyRamified (h : IsTotallyRamified K L v w)
    {πL : w.adicCompletionIntegers L} (hπL : Irreducible πL)
    {π : v.adicCompletionIntegers K} (hπ : Irreducible π) :
    Associated (Algebra.norm (v.adicCompletionIntegers K) πL) π := by
  have he0 : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
  -- `𝔪_K · L₀ = 𝔪_L ^ e`, with both sides written as principal ideals.
  have hspan : Ideal.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L))
      (Ideal.span {π}) =
      Ideal.span {πL ^ (v.asIdeal.ramificationIdx' w.asIdeal)} := by
    rw [← hπ.maximalIdeal_eq, h.map_maximalIdeal_eq, hπL.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [Ideal.map_span, Set.image_singleton] at hspan
  have hassoc : Associated
      (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) π)
      (πL ^ (v.asIdeal.ramificationIdx' w.asIdeal)) :=
    Ideal.span_singleton_eq_span_singleton.mp hspan
  have hnorm := hassoc.map (Algebra.norm (v.adicCompletionIntegers K) :
    w.adicCompletionIntegers L →* v.adicCompletionIntegers K)
  rw [Algebra.norm_algebraMap, map_pow, h.finrank_eq] at hnorm
  exact ((Associated.pow_iff he0).mp hnorm).symm

omit [Algebra.IsIntegral R S] in
/-- **The norm of a uniformizer of `L₀` is irreducible in `K₀`.** The form actually consumed
downstream: it is what makes `uniformizerUnit K v` applicable to `Algebra.norm K₀ π_L`, so that the
cyclic generator of the norm group can be exhibited as a genuine uniformizer unit. The base
uniformizer `π` of `K₀` is obtained internally (`IsDiscreteValuationRing.exists_irreducible`), so
no choice of it appears in the statement. -/
theorem irreducible_norm_of_isTotallyRamified (h : IsTotallyRamified K L v w)
    {πL : w.adicCompletionIntegers L} (hπL : Irreducible πL) :
    Irreducible (Algebra.norm (v.adicCompletionIntegers K) πL) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  exact (associated_norm_uniformizer_of_isTotallyRamified K L v w h hπL hπ).symm.irreducible hπ

/-! ### `N(π_L)` lies in the norm group -/

omit [Module.Finite K L] [Algebra.IsIntegral R S]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- A uniformizer of `L₀` is nonzero in `w.adicCompletion L`, hence a unit of that field. -/
theorem coe_ne_zero_of_irreducible {πL : w.adicCompletionIntegers L} (hπL : Irreducible πL) :
    ((πL : w.adicCompletion L)) ≠ 0 := by
  rw [Ne, ZeroMemClass.coe_eq_zero]
  exact hπL.ne_zero

variable [Finite (ResidueField (w.adicCompletionIntegers L))]

omit [Algebra.IsIntegral R S] [Finite (ResidueField (w.adicCompletionIntegers L))] in
/-- **The uniformizer unit `N(π_L)` is a norm.** Witnessed by the unit of `(w.adicCompletion L)ˣ`
corresponding to `π_L` itself: `localNormMap` of it is `Algebra.norm K_v (π_L : L_w)`, which
`Langlands.NormMapResidueCompatibility`'s `algebraMap_norm_eq_norm_algebraMap` identifies with the
image of the integers-level norm `Algebra.norm K₀ π_L`. -/
theorem uniformizerUnit_norm_mem_range (h : IsTotallyRamified K L v w)
    {πL : w.adicCompletionIntegers L} (hπL : Irreducible πL) :
    uniformizerUnit K v (irreducible_norm_of_isTotallyRamified K L v w h hπL) ∈
      MonoidHom.range (localNormMap K L v w) := by
  refine ⟨(coe_ne_zero_of_irreducible L w hπL).isUnit.unit, ?_⟩
  apply Units.ext
  show Algebra.norm (v.adicCompletion K)
      (((coe_ne_zero_of_irreducible L w hπL).isUnit.unit : (w.adicCompletion L)ˣ) :
        w.adicCompletion L) =
    (uniformizerUnit K v (irreducible_norm_of_isTotallyRamified K L v w h hπL) :
      v.adicCompletion K)
  rw [IsUnit.unit_spec, coe_uniformizerUnit, algebraMap_norm_eq_norm_algebraMap K L v w πL]
  rfl

/-! ### The principal units of `K₀` as a subgroup of `(v.adicCompletion K)ˣ` -/

omit [Algebra.IsIntegral R S] [Module.Finite K L]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]
  [Finite (ResidueField (w.adicCompletionIntegers L))] in
/-- **`U_K^{(i)}` as a subgroup of `(v.adicCompletion K)ˣ`.**
`Langlands.PrincipalUnitsFiltrationAdicCompletion`'s `principalUnitsPowK` lives in `K₀ˣ`; this
pushes it forward along `Units.map (algebraMap K₀ K_v)`, the same embedding
`Langlands.UnramifiedNormRange` uses to view `O_K^×` inside `(v.adicCompletion K)ˣ`. The map is
injective (`algebraMap K₀ K_v` is the subtype inclusion), so no information is lost, but that is
not needed for the containment proved below. -/
def principalUnitsPowKField (i : ℕ) : Subgroup (v.adicCompletion K)ˣ :=
  (principalUnitsPowK K v i).map
    (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)))

/-! ### The containment -/

omit [Algebra.IsIntegral R S] [Finite (ResidueField (w.adicCompletionIntegers L))] in
/-- **`⟨N(π_L)⟩ · U_K^{(1)} ≤ N_{L/K}(L_w^×)`, for a tame totally ramified extension.** The two
generators of the `⊔` are handled separately, mirroring `Langlands.UnramifiedNormRange`'s
`localNormMap_range_eq`:

* `Subgroup.zpowers_le` reduces the cyclic part to the single membership
  `uniformizerUnit_norm_mem_range`;
* the principal-unit part is `Langlands.TotallyRamifiedNormSurjective`'s
  `exists_isUnit_norm_eq_of_isTotallyRamified` applied pointwise, with the resulting unit of `L₀`
  pushed into `(w.adicCompletion L)ˣ` by `Units.map (algebraMap L₀ L_w)` and
  `algebraMap_norm_eq_norm_algebraMap` used to match the two levels of norm.

Only `≤` is proved; see the module docstring. -/
theorem localNormMap_range_ge_of_isTotallyRamified (h : IsTotallyRamified K L v w)
    (htame : IsTamelyRamified K L v w) {πL : w.adicCompletionIntegers L} (hπL : Irreducible πL) :
    Subgroup.zpowers
        (uniformizerUnit K v (irreducible_norm_of_isTotallyRamified K L v w h hπL)) ⊔
      principalUnitsPowKField K v 1 ≤ MonoidHom.range (localNormMap K L v w) := by
  apply sup_le
  · rw [Subgroup.zpowers_le]
    exact uniformizerUnit_norm_mem_range K L v w h hπL
  · rintro y hy
    simp only [principalUnitsPowKField, Subgroup.mem_map] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hy1 : (y₀ : v.adicCompletionIntegers K) - 1 ∈
        maximalIdeal (v.adicCompletionIntegers K) := by
      have h1 : (y₀ : v.adicCompletionIntegers K) - 1 ∈
          maximalIdeal (v.adicCompletionIntegers K) ^ 1 := hy₀
      rwa [pow_one] at h1
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
    obtain ⟨x, hx, hxy⟩ := exists_isUnit_norm_eq_of_isTotallyRamified K L v w h htame hπ hy1
    refine ⟨Units.map (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) hx.unit, ?_⟩
    apply Units.ext
    show Algebra.norm (v.adicCompletion K)
        (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)
          (hx.unit : w.adicCompletionIntegers L)) =
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        (y₀ : v.adicCompletionIntegers K))
    rw [hx.unit_spec, ← algebraMap_norm_eq_norm_algebraMap K L v w x, hxy]

end IsDedekindDomain.HeightOneSpectrum

end
