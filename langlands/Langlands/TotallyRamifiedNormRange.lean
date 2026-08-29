import Langlands.TotallyRamifiedNormSurjective
import Langlands.PrincipalUnitsFiltrationAdicCompletion
import Langlands.UnramifiedNormRange

/-!
# The totally ramified norm group: exact range, and a tame lower bound at `U_K^{(1)}`

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`. This file proves two statements about
`MonoidHom.range (localNormMap K L v w)` as a subgroup of `(v.adicCompletion K)ˣ`:

1. **The exact range, unconditionally on tameness**
   (`localNormMap_range_eq_of_isTotallyRamified`):
   `MonoidHom.range (localNormMap K L v w) = Subgroup.zpowers (N(π_L)) ⊔ N_{L/K}(U_L)`,
   where `N_{L/K}(U_L)` is *literally* the image of `(w.adicCompletionIntegers L).units` under
   `localNormMap`, not a description of it. This needs `IsTotallyRamified` (only to know
   `N(π_L)` is irreducible, hence a genuine `uniformizerUnit`) but *not* `IsTamelyRamified`.
2. **A tame lower bound at the smaller, but explicit, subgroup `U_K^{(1)}`**
   (`localNormMap_range_ge_of_isTotallyRamified`):
   `Subgroup.zpowers (N(π_L)) ⊔ U_K^{(1)} ≤ MonoidHom.range (localNormMap K L v w)`,
   under `IsTotallyRamified` and `IsTamelyRamified`, where `π_L` is any uniformizer of `L₀`.

## Why `N_{L/K}(U_L) ≠ U_K^{(1)}` in general, even under `IsTamelyRamified`

`N_{L/K}(U_L)` is the set of units whose residue is an `e`-th power of `𝓀[K]ˣ`
(`Langlands.TotallyRamifiedNormResidue`'s
`residue_norm_eq_residue_pow_ramificationIdx_of_isTotallyRamified` proves the `⊆` half of that
description; the matching surjectivity at level `0` is not formalized here). On the finite cyclic
group `𝓀[K]ˣ` of order `q - 1`, the `e`-th power map has image of index `gcd(e, q-1)`, a *proper*
subgroup whenever `gcd(e, q-1) > 1`.

**This can happen even under `IsTamelyRamified` as literally defined in this repo**
(`IsUnit ((e : ℕ) : 𝓀[K])`, i.e. `p ∤ e` for `p` the residue characteristic): `p ∤ e` does **not**
imply `gcd(e, q-1) = 1`. Counterexample: `p = 2`, `q = 16` (so `q - 1 = 15 = 3 · 5`), `e = 3` —
`p ∤ e` holds (`2 ∤ 3`) but `gcd(3, 15) = 3 ≠ 1`. Here the `e`-th power map on the cyclic group
`𝓀[K]ˣ` of order `15` has image of index `3`, i.e. order `5` — a subgroup strictly between `{1}`
and `𝓀[K]ˣ`. So a tame (`p ∤ e`), totally ramified extension of degree `3` over a residue field
`𝔽₁₆` would have `N_{L/K}(U_L)` of index `3` in `U_K` (not index `15 = #𝓀[K]ˣ`, which is what
`N_{L/K}(U_L) = U_K^{(1)}` would require) — strictly between `U_K^{(1)}` and `U_K`. `IsTamelyRamified`
alone does not force `gcd(e,q-1) = 1`, so no general theorem `N_{L/K}(U_L) = U_K^{(1)}` under only
`IsTamelyRamified` can be proved, and none is claimed here. Consequently
`localNormMap_range_ge_of_isTotallyRamified`'s `⊔` is only a lower bound on the range in general,
never claimed to be an equality — contrast `Langlands.UnramifiedNormRange`'s
`localNormMap_range_eq`, an equality, available there because the unramified unit half is all of
`O_K^×` with no level-`0` obstruction at all.

The full level-`0` finite-field computation (image of `x ↦ x^e` on a finite cyclic group, and its
relationship to the "tame" hypothesis) is **not formalized in Lean anywhere in this repo** — the
paragraph above is a hand computation, recorded here to fix precisely what is and is not proved.
Formalizing it would need the image of `x ↦ x^e` on `𝓀[K]ˣ`, identified with the subgroup of index
`gcd(e, q-1)` — routine finite-cyclic-group theory (`orderOf`/`IsCyclic` machinery in Mathlib), but
is not needed here, since `localNormMap_range_eq_of_isTotallyRamified` above gives the exact
range without it.

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
task in its own right; it is simply not a prerequisite for the result proved here.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.associated_norm_uniformizer_of_isTotallyRamified`
* `IsDedekindDomain.HeightOneSpectrum.irreducible_norm_of_isTotallyRamified`
* `IsDedekindDomain.HeightOneSpectrum.exists_zpow_mul_unit_eq_of_irreducible` : every unit of
  `w.adicCompletion L` is `π_L^k` times a unit of `L₀`, for `π_L` any irreducible element of `L₀`
  — no ramification hypothesis needed. The totally-ramified-file counterpart of
  `Langlands.UnramifiedNormRange`'s `exists_zpow_mul_unit_eq`, simplified because `π_L` is already
  irreducible in `L₀` (unlike the image of a `K₀`-uniformizer, which is not once the extension
  ramifies).
* `IsDedekindDomain.HeightOneSpectrum.localNormMap_range_eq_of_isTotallyRamified` : **the exact
  range**, `MonoidHom.range (localNormMap K L v w) = Subgroup.zpowers (N(π_L)) ⊔
  (w.adicCompletionIntegers L).units.map (localNormMap K L v w)`, under `IsTotallyRamified` alone
  (no tameness needed).
* `IsDedekindDomain.HeightOneSpectrum.principalUnitsPowKField` : `U_K^{(i)}` pushed forward from
  `K₀ˣ` (where `Langlands.PrincipalUnitsFiltrationAdicCompletion` defines it) to
  `(v.adicCompletion K)ˣ`, along `Units.map (algebraMap K₀ K_v)` — the same embedding
  `Langlands.UnramifiedNormRange` uses for `(v.adicCompletionIntegers K).units`.
* `IsDedekindDomain.HeightOneSpectrum.localNormMap_range_ge_of_isTotallyRamified` : the tame lower
  bound `Subgroup.zpowers (N(π_L)) ⊔ U_K^{(1)} ≤ MonoidHom.range (localNormMap K L v w)`.
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
theorem localNormMap_irreducibleUnit_eq (h : IsTotallyRamified K L v w)
    {πL : w.adicCompletionIntegers L} (hπL : Irreducible πL) :
    localNormMap K L v w (coe_ne_zero_of_irreducible L w hπL).isUnit.unit =
      uniformizerUnit K v (irreducible_norm_of_isTotallyRamified K L v w h hπL) := by
  -- (statement, not just membership: reused both by `uniformizerUnit_norm_mem_range` and by the
  -- exact-equality theorem `localNormMap_range_eq_of_isTotallyRamified` below, which needs the
  -- identity itself to push `zpow`s through.)
  apply Units.ext
  show Algebra.norm (v.adicCompletion K)
      (((coe_ne_zero_of_irreducible L w hπL).isUnit.unit : (w.adicCompletion L)ˣ) :
        w.adicCompletion L) =
    (uniformizerUnit K v (irreducible_norm_of_isTotallyRamified K L v w h hπL) :
      v.adicCompletion K)
  rw [IsUnit.unit_spec, coe_uniformizerUnit, algebraMap_norm_eq_norm_algebraMap K L v w πL]
  rfl

omit [Algebra.IsIntegral R S] [Finite (ResidueField (w.adicCompletionIntegers L))] in
theorem uniformizerUnit_norm_mem_range (h : IsTotallyRamified K L v w)
    {πL : w.adicCompletionIntegers L} (hπL : Irreducible πL) :
    uniformizerUnit K v (irreducible_norm_of_isTotallyRamified K L v w h hπL) ∈
      MonoidHom.range (localNormMap K L v w) :=
  ⟨(coe_ne_zero_of_irreducible L w hπL).isUnit.unit, localNormMap_irreducibleUnit_eq K L v w h hπL⟩

/-! ### The uniformizer-power decomposition, directly in terms of `π_L` -/

section Decomposition

omit [Module.Finite K L] [Algebra.IsIntegral R S]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]
  [Finite (ResidueField (w.adicCompletionIntegers L))] in
/-- **Base case of the uniformizer-power decomposition, using `π_L` directly.** If a unit `a` of
`w.adicCompletion L` has `Valued.v a ≤ 1` (i.e. `a` lies in `L₀`), it decomposes as `a = π_L^n * u`
for some `n : ℕ` and unit `u` of `L₀`, for *any* irreducible `π_L : L₀` — no ramification
hypothesis is needed. This is `Langlands.UnramifiedNormRange`'s
`exists_pow_mul_unit_eq_of_valued_le_one` with the outer `algebraMap K₀ L₀` layer dropped: there
`π` had to be lifted from `K₀` and irreducibility of the lift needed `IsUnramified`
(`algebraMap_uniformizer_irreducible`), which is false once the extension ramifies; here `π_L` is
already an element of `L₀`, so its irreducibility is simply the hypothesis. -/
theorem exists_pow_mul_unit_eq_of_valued_le_one_of_irreducible
    {πL : w.adicCompletionIntegers L} (hπL : Irreducible πL)
    {a : (w.adicCompletion L)ˣ} (hle : Valued.v (a : w.adicCompletion L) ≤ 1) :
    ∃ (n : ℕ) (u : (w.adicCompletionIntegers L)ˣ),
      (a : w.adicCompletion L) =
        ((πL : w.adicCompletionIntegers L) : w.adicCompletion L) ^ n * (u : w.adicCompletion L) := by
  set x : w.adicCompletionIntegers L :=
    ⟨(a : w.adicCompletion L), (mem_adicCompletionIntegers S L w).mpr hle⟩ with hxdef
  have hx0 : x ≠ 0 := by
    rw [Ne, ← ZeroMemClass.coe_eq_zero]
    exact a.ne_zero
  obtain ⟨n, u₀, hu₀⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0 hπL
  refine ⟨n, u₀⁻¹, ?_⟩
  have hval : x = πL ^ n * ((u₀⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L) :=
    (Units.eq_mul_inv_iff_mul_eq u₀).mpr hu₀
  have hcast := congrArg (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) hval
  simp only [map_mul, map_pow] at hcast
  rw [hxdef] at hcast
  exact hcast

omit [Module.Finite K L] [Algebra.IsIntegral R S]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]
  [Finite (ResidueField (w.adicCompletionIntegers L))] in
/-- **The uniformizer-power decomposition, using `π_L` directly.** Every unit `a` of
`w.adicCompletion L` decomposes as `a = π_L^k * u` for some `k : ℤ` and some unit `u` of `L₀`, for
any irreducible `π_L : L₀` — the totally-ramified-file counterpart of
`Langlands.UnramifiedNormRange`'s `exists_zpow_mul_unit_eq`, again with no ramification
hypothesis. -/
theorem exists_zpow_mul_unit_eq_of_irreducible
    {πL : w.adicCompletionIntegers L} (hπL : Irreducible πL) (a : (w.adicCompletion L)ˣ) :
    ∃ (k : ℤ) (u : (w.adicCompletionIntegers L)ˣ),
      (a : w.adicCompletion L) =
        ((πL : w.adicCompletionIntegers L) : w.adicCompletion L) ^ k * (u : w.adicCompletion L) := by
  rcases le_total (Valued.v (a : w.adicCompletion L)) 1 with hle | hge
  · obtain ⟨n, u, hnu⟩ := exists_pow_mul_unit_eq_of_valued_le_one_of_irreducible L w hπL hle
    exact ⟨(n : ℤ), u, by rw [hnu, zpow_natCast]⟩
  · have hinv_le : Valued.v (((a⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L)) ≤ 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨n, u, hnu⟩ :=
      exists_pow_mul_unit_eq_of_valued_le_one_of_irreducible L w hπL hinv_le
    refine ⟨-(n : ℤ), u⁻¹, ?_⟩
    rw [Units.val_inv_eq_inv_val] at hnu
    have ha : (a : w.adicCompletion L) = ((a : w.adicCompletion L)⁻¹)⁻¹ := (inv_inv _).symm
    rw [ha, hnu, mul_inv, ← algebraMap_coe_inv_eq L w u, zpow_neg, zpow_natCast]

end Decomposition

/-! ### The exact norm-group range, in terms of `N(U_L)` -/

omit [Algebra.IsIntegral R S] [Finite (ResidueField (w.adicCompletionIntegers L))] in
/-- **The exact norm-group range: `N_{L/K}(L_w^×) = ⟨N(π_L)⟩ · N_{L/K}(U_L)`.** Unlike
`localNormMap_range_ge_of_isTotallyRamified`, this is an *equality*, and it needs neither
`IsTamelyRamified` nor any classification of `N_{L/K}(U_L)` as a residue condition: the reverse
inclusion is a direct consequence of `exists_zpow_mul_unit_eq_of_irreducible` (every unit of `L_w`
is `π_L^k` times a unit of `L₀`) pushed through `localNormMap`'s multiplicativity, exactly
mirroring `Langlands.UnramifiedNormRange`'s `localNormMap_range_le`/`localNormMap_range_eq` but
with `π_L` in place of the (here, generally non-irreducible) image of a `K₀`-uniformizer.

`N_{L/K}(U_L)` itself is *not* replaced by `U_K^{(1)}` here — see the module docstring on why that
would be false in general once `gcd(e, #𝓀[K]ˣ) > 1`, which `IsTamelyRamified` (`p ∤ e`) does not
rule out. -/
theorem localNormMap_range_eq_of_isTotallyRamified (h : IsTotallyRamified K L v w)
    {πL : w.adicCompletionIntegers L} (hπL : Irreducible πL) :
    MonoidHom.range (localNormMap K L v w) =
      Subgroup.zpowers
          (uniformizerUnit K v (irreducible_norm_of_isTotallyRamified K L v w h hπL)) ⊔
        (w.adicCompletionIntegers L).units.map (localNormMap K L v w) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨k, u, hku⟩ := exists_zpow_mul_unit_eq_of_irreducible L w hπL a
    set embed : (w.adicCompletionIntegers L)ˣ →* (w.adicCompletion L)ˣ :=
      Units.map (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) with hembeddef
    have ha : a = (coe_ne_zero_of_irreducible L w hπL).isUnit.unit ^ k * embed u := by
      apply Units.ext
      push_cast
      rw [(coe_ne_zero_of_irreducible L w hπL).isUnit.unit_spec]
      exact hku
    have hu_mem : embed u ∈ (w.adicCompletionIntegers L).units :=
      Submonoid.mem_units_of_val_mem_inv_val_mem _ (u : w.adicCompletionIntegers L).2
        ((u⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L).2
    rw [ha, map_mul, map_zpow, localNormMap_irreducibleUnit_eq K L v w h hπL]
    exact Subgroup.mem_sup.mpr ⟨_, Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k, _,
      Subgroup.mem_map.mpr ⟨embed u, hu_mem, rfl⟩, rfl⟩
  · apply sup_le
    · rw [Subgroup.zpowers_le]
      exact uniformizerUnit_norm_mem_range K L v w h hπL
    · rintro _ ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩

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
