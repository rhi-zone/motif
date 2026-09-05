import Langlands.UnramifiedNormSurjective
import Langlands.AdicCompletionUniformizerDecomposition
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The full unramified norm-group theorem: `N_{L/K}(L^×) = ⟨π⟩^n · O_K^×`

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`. `Langlands.UnramifiedNormSurjective` proves the "easy"
direction `N_{L/K}(L^×) ⊇ O_K^×` under `IsUnramified`. This file proves the reverse inclusion and
combines both into the full classical statement, as an equality of subgroups of
`(v.adicCompletion K)ˣ`:

`MonoidHom.range (localNormMap K L v w) = Subgroup.zpowers (πunit ^ n) ⊔ (v.adicCompletionIntegers K).units`

where `πunit : (v.adicCompletion K)ˣ` is the unit corresponding to (the image of) a uniformizer `π`
of `K₀`, and `n := Module.finrank (v.adicCompletion K) (w.adicCompletion L)` is the local degree
`[L_w : K_v]` (which, since `L/K` is unramified, equals the residue degree).

## Route

1. `algebraMap_uniformizer_irreducible` : under `IsUnramified`, the image of a uniformizer `π` of
   `K₀` in `L₀` is itself irreducible (a uniformizer of `L₀`) — since `IsUnramified` says
   `𝔪_K·L₀ = 𝔪_L`, and `𝔪_K = (π)`, so `𝔪_L = (algebraMap π)`, which is
   `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
2. `exists_zpow_mul_unit_eq` : **every unit `a` of `w.adicCompletion L` decomposes as
   `a = ϖ^k · u` for some `k : ℤ` and some unit `u` of `L₀`**, where `ϖ` is the image of `π` in
   `L₀`. Built from `IsDiscreteValuationRing.associated_pow_irreducible` (every nonzero element of
   a DVR is a unit times a power of a fixed irreducible), applied directly when `a ∈ L₀` (i.e.
   `Valued.v a ≤ 1`), or to `a⁻¹` and inverted when `Valued.v a > 1`.
3. `norm_algebraMap_uniformizer_eq` : `Algebra.norm (v.adicCompletion K)` of the (`L₀`-route) image
   of `π` is exactly `π^n`, via `Algebra.norm_algebraMap` at the field level, using
   `Langlands.ResidueFieldNorm.coe_algebraMap_adicCompletionIntegers` (already proved by `rfl`) to
   identify the `L₀`-route image of `π` with `adicCompletionComap`'s (i.e. the `K_v`-route)
   image, the form `Algebra.norm_algebraMap` is stated for.
4. `localNormMap_range_le` : combining (2) and (3) with `localNormMap_mem_units` (norm of a local
   unit of `L₀` is a local unit of `K₀`) gives the reverse inclusion
   `MonoidHom.range (localNormMap K L v w) ≤ Subgroup.zpowers (πunit ^ n) ⊔ (v.adicCompletionIntegers K).units`.
5. `localNormMap_range_eq` : the main theorem, combining (4) with the reverse inclusion (both
   generators of the sup lie in the range: `πunit ^ n` via (3), and `O_K^×` via
   `Langlands.UnramifiedNormSurjective`'s `exists_isUnit_algebraMap_norm_eq_of_isUnramified`).

## Main result

* `IsDedekindDomain.HeightOneSpectrum.localNormMap_range_eq`
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

omit [Module.Finite K L] [Algebra.IsIntegral R S]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- Under `IsUnramified`, the image in `L₀` of a uniformizer `π` of `K₀` is itself a uniformizer of
`L₀` (irreducible): `IsUnramified` says `𝔪_K·L₀ = 𝔪_L`, and `𝔪_K = (π)`
(`Irreducible.maximalIdeal_eq`), so `𝔪_L = (algebraMap π)`
(`Ideal.map_span`/`Set.image_singleton`), which is exactly
`IsDiscreteValuationRing.irreducible_iff_uniformizer`. -/
theorem algebraMap_uniformizer_irreducible (hU : IsUnramified K L v w)
    {π : v.adicCompletionIntegers K} (hπ : Irreducible π) :
    Irreducible (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) π) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hU, hπ.maximalIdeal_eq,
    Ideal.map_span, Set.image_singleton]

section Decomposition

variable {π : v.adicCompletionIntegers K}

omit [Module.Finite K L] [Algebra.IsIntegral R S]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- **Base case of the uniformizer-power decomposition.** If a unit `a` of `w.adicCompletion L`
has `Valued.v a ≤ 1` (i.e. `a` lies in `L₀`), it decomposes as `a = ϖ^n * u` for some `n : ℕ` and
some unit `u` of `L₀`, where `ϖ` is the image of `π` in `L₀`. This is
`IsDiscreteValuationRing.associated_pow_irreducible` (every nonzero element of a DVR is associated
to a power of a fixed irreducible), transported from the ring-level `Associated` witness to a
field-level unit equation via the algebra map `L₀ → w.adicCompletion L`. This is now a thin
specialization of `Langlands.AdicCompletionUniformizerDecomposition`'s
`exists_pow_mul_unit_eq_of_valued_le_one_of_irreducible`, applied at `F := L`, `v := w`, with the
irreducible element taken to be `algebraMap π` (irreducible by `algebraMap_uniformizer_irreducible`,
which is where `IsUnramified` is actually used — the general lemma itself needs no ramification
hypothesis). -/
theorem exists_pow_mul_unit_eq_of_valued_le_one (hU : IsUnramified K L v w) (hπ : Irreducible π)
    {a : (w.adicCompletion L)ˣ} (hle : Valued.v (a : w.adicCompletion L) ≤ 1) :
    ∃ (n : ℕ) (u : (w.adicCompletionIntegers L)ˣ),
      (a : w.adicCompletion L) =
        ((algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) π :
            w.adicCompletionIntegers L) : w.adicCompletion L) ^ n *
          (u : w.adicCompletion L) :=
  exists_pow_mul_unit_eq_of_valued_le_one_of_irreducible w
    (algebraMap_uniformizer_irreducible K L v w hU hπ) hle

omit [Module.Finite K L] [Algebra.IsIntegral R S]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- **The uniformizer-power decomposition.** Every unit `a` of `w.adicCompletion L` decomposes as
`a = ϖ^k * u` for some `k : ℤ` and some unit `u` of `L₀`, where `ϖ` is the image of `π` in `L₀`.
If `Valued.v a ≤ 1`, this is the base case (`exists_pow_mul_unit_eq_of_valued_le_one`) directly.
Otherwise `Valued.v a⁻¹ ≤ 1` (`inv_le_one_of_one_le₀`), so the base case applies to `a⁻¹`, giving
`a⁻¹ = ϖ^n * u`; inverting (`Units.val_inv_eq_inv_val`, `mul_inv`, `zpow_neg`/`zpow_natCast`) gives
`a = ϖ^(-n) * u⁻¹`. This is now a thin specialization of
`Langlands.AdicCompletionUniformizerDecomposition`'s `exists_zpow_mul_unit_eq_of_irreducible`,
applied at `F := L`, `v := w`, with the irreducible element `algebraMap π` (see
`exists_pow_mul_unit_eq_of_valued_le_one`'s docstring). -/
theorem exists_zpow_mul_unit_eq (hU : IsUnramified K L v w) (hπ : Irreducible π)
    (a : (w.adicCompletion L)ˣ) :
    ∃ (k : ℤ) (u : (w.adicCompletionIntegers L)ˣ),
      (a : w.adicCompletion L) =
        ((algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) π :
            w.adicCompletionIntegers L) : w.adicCompletion L) ^ k *
          (u : w.adicCompletion L) :=
  exists_zpow_mul_unit_eq_of_irreducible w (algebraMap_uniformizer_irreducible K L v w hU hπ) a

end Decomposition

/-! ### The image of the uniformizer under `Algebra.norm` -/

omit [Algebra.IsIntegral R S] [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- `Algebra.norm (v.adicCompletion K)` of the (`L₀`-route) image of a uniformizer `π` of `K₀` is
exactly `π^n`, where `n` is the local degree `[L_w : K_v]`. The `L₀`-route image
`(algebraMap K₀ L₀ π : L₀ : L_w)` equals `adicCompletionComap K L v w (algebraMap K₀ K_v π)` by
`coe_algebraMap_adicCompletionIntegers` (`Langlands.ResidueFieldNorm`, proved there by `rfl`), and
`adicCompletionComap` is definitionally `algebraMap (v.adicCompletion K) (w.adicCompletion L)`
(`Langlands.NormMap`'s `Algebra (v.adicCompletion K) (w.adicCompletion L)` instance is built as
`(adicCompletionComap K L v w).toAlgebra`), so `Algebra.norm_algebraMap` applies directly. -/
theorem norm_algebraMap_uniformizer_eq {π : v.adicCompletionIntegers K} :
    Algebra.norm (v.adicCompletion K)
        ((algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) π :
            w.adicCompletionIntegers L) : w.adicCompletion L) =
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) ^
        Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  rw [coe_algebraMap_adicCompletionIntegers]
  exact Algebra.norm_algebraMap (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π)

/-! ### The full unramified norm-group theorem -/

omit [Algebra.IsIntegral R S] [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- The image in `v.adicCompletion K` of a uniformizer `π` of `K₀` is nonzero. -/
theorem algebraMap_uniformizer_ne_zero {π : v.adicCompletionIntegers K} (hπ : Irreducible π) :
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) ≠ 0 := by
  show (π : v.adicCompletion K) ≠ 0
  rw [Ne, ZeroMemClass.coe_eq_zero]
  exact hπ.ne_zero

omit [Module.Finite K L] [Algebra.IsIntegral R S]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
/-- The image in `w.adicCompletion L` of `algebraMap K₀ L₀ π` is nonzero, under `IsUnramified`
(`algebraMap_uniformizer_irreducible` gives irreducibility in `L₀`, hence nonzero-ness). -/
theorem algebraMap_algebraMap_uniformizer_ne_zero (hU : IsUnramified K L v w)
    {π : v.adicCompletionIntegers K} (hπ : Irreducible π) :
    ((algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) π :
        w.adicCompletionIntegers L) : w.adicCompletion L) ≠ 0 := by
  rw [Ne, ZeroMemClass.coe_eq_zero]
  exact (algebraMap_uniformizer_irreducible K L v w hU hπ).ne_zero

variable [Finite (ResidueField (w.adicCompletionIntegers L))]

/-- The unit of `(v.adicCompletion K)ˣ` corresponding to (the image of) a uniformizer `π` of `K₀`. -/
def uniformizerUnit {π : v.adicCompletionIntegers K} (hπ : Irreducible π) :
    (v.adicCompletion K)ˣ :=
  (algebraMap_uniformizer_ne_zero K v hπ).isUnit.unit

/-- The unit of `(w.adicCompletion L)ˣ` corresponding to (the image of) `algebraMap K₀ L₀ π`. -/
def algebraMapUniformizerUnit (hU : IsUnramified K L v w) {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) : (w.adicCompletion L)ˣ :=
  (algebraMap_algebraMap_uniformizer_ne_zero K L v w hU hπ).isUnit.unit

omit [Algebra.IsIntegral R S] in
theorem coe_uniformizerUnit {π : v.adicCompletionIntegers K} (hπ : Irreducible π) :
    (uniformizerUnit K v hπ : v.adicCompletion K) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π :=
  (algebraMap_uniformizer_ne_zero K v hπ).isUnit.unit_spec

omit [Module.Finite K L] [Algebra.IsIntegral R S]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]
  [Finite (ResidueField (w.adicCompletionIntegers L))] in
theorem coe_algebraMapUniformizerUnit (hU : IsUnramified K L v w) {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) :
    (algebraMapUniformizerUnit K L v w hU hπ : w.adicCompletion L) =
      ((algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) π :
          w.adicCompletionIntegers L) : w.adicCompletion L) :=
  (algebraMap_algebraMap_uniformizer_ne_zero K L v w hU hπ).isUnit.unit_spec

omit [Algebra.IsIntegral R S] [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]
  [Finite (ResidueField (w.adicCompletionIntegers L))] in
/-- **`localNormMap` of the uniformizer unit is exactly `π^n`.** This is
`norm_algebraMap_uniformizer_eq` transported from `Algebra.norm` to `localNormMap` (which is
`Units.map (Algebra.norm ...)`) via `Units.ext`. -/
theorem localNormMap_algebraMapUniformizerUnit_eq (hU : IsUnramified K L v w)
    {π : v.adicCompletionIntegers K} (hπ : Irreducible π) :
    localNormMap K L v w (algebraMapUniformizerUnit K L v w hU hπ) =
      uniformizerUnit K v hπ ^ Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  apply Units.ext
  push_cast
  rw [show (localNormMap K L v w (algebraMapUniformizerUnit K L v w hU hπ) :
        v.adicCompletion K) =
      Algebra.norm (v.adicCompletion K)
        (algebraMapUniformizerUnit K L v w hU hπ : w.adicCompletion L) from rfl,
    coe_algebraMapUniformizerUnit K L v w hU hπ, norm_algebraMap_uniformizer_eq K L v w,
    coe_uniformizerUnit K v hπ]

omit [Algebra.IsIntegral R S] [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]
  [Finite (ResidueField (w.adicCompletionIntegers L))] in
/-- **The reverse inclusion.** Every element of `MonoidHom.range (localNormMap K L v w)` lies in
`Subgroup.zpowers (uniformizerUnit ^ n) ⊔ (v.adicCompletionIntegers K).units`. Combines the
uniformizer-power decomposition (`exists_zpow_mul_unit_eq`) of a preimage `a`, `localNormMap`'s
multiplicativity and compatibility with `zpow` (`Units.map` is a group hom), and
`localNormMap_algebraMapUniformizerUnit_eq`/`localNormMap_mem_units`. -/
theorem localNormMap_range_le (hU : IsUnramified K L v w) {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) :
    MonoidHom.range (localNormMap K L v w) ≤
      Subgroup.zpowers
          (uniformizerUnit K v hπ ^ Module.finrank (v.adicCompletion K) (w.adicCompletion L)) ⊔
        (v.adicCompletionIntegers K).units := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨k, u, hku⟩ := exists_zpow_mul_unit_eq K L v w hU hπ a
  set embed : (w.adicCompletionIntegers L)ˣ →*
      (w.adicCompletion L)ˣ :=
    Units.map (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) with hembeddef
  have ha : a = algebraMapUniformizerUnit K L v w hU hπ ^ k * embed u := by
    apply Units.ext
    push_cast
    rw [coe_algebraMapUniformizerUnit K L v w hU hπ]
    exact hku
  have hu_mem : embed u ∈ (w.adicCompletionIntegers L).units :=
    Submonoid.mem_units_of_val_mem_inv_val_mem _ (u : w.adicCompletionIntegers L).2
      ((u⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L).2
  rw [ha, map_mul, map_zpow, localNormMap_algebraMapUniformizerUnit_eq K L v w hU hπ]
  exact Subgroup.mem_sup.mpr ⟨_, Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k, _,
    localNormMap_mem_units K L v w hu_mem, rfl⟩

omit [Algebra.IsIntegral R S] in
/-- **The main theorem.** `N_{L/K}(L^×) = ⟨π⟩^n · O_K^×`, as an equality of subgroups of
`(v.adicCompletion K)ˣ`: `⊆` is `localNormMap_range_le`; `⊇` combines
`localNormMap_algebraMapUniformizerUnit_eq` (`uniformizerUnit ^ n` is a norm) with
`Langlands.UnramifiedNormSurjective`'s `exists_isUnit_algebraMap_norm_eq_of_isUnramified` (every
unit of `K₀` is a norm). -/
theorem localNormMap_range_eq (hU : IsUnramified K L v w) {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) :
    MonoidHom.range (localNormMap K L v w) =
      Subgroup.zpowers
          (uniformizerUnit K v hπ ^ Module.finrank (v.adicCompletion K) (w.adicCompletion L)) ⊔
        (v.adicCompletionIntegers K).units := by
  apply le_antisymm (localNormMap_range_le K L v w hU hπ)
  apply sup_le
  · rw [Subgroup.zpowers_le]
    exact ⟨_, localNormMap_algebraMapUniformizerUnit_eq K L v w hU hπ⟩
  · rintro y hy
    obtain ⟨hy1, hy2⟩ := Submonoid.mem_units_iff (v.adicCompletionIntegers K).toSubmonoid y |>.mp hy
    set y₀ : v.adicCompletionIntegers K := ⟨(y : v.adicCompletion K), hy1⟩ with hy₀def
    have hy₀u : IsUnit y₀ := by
      refine IsUnit.of_mul_eq_one
        (⟨(y⁻¹ : (v.adicCompletion K)ˣ), hy2⟩ : v.adicCompletionIntegers K) ?_
      apply Subtype.ext
      show (y : v.adicCompletion K) * ((y⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1
      exact_mod_cast y.mul_inv
    obtain ⟨x, hx, hxy⟩ := exists_isUnit_algebraMap_norm_eq_of_isUnramified K L v w hU hπ hy₀u
    refine ⟨Units.map (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) hx.unit, ?_⟩
    apply Units.ext
    show Algebra.norm (v.adicCompletion K)
        (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)
          (hx.unit : w.adicCompletionIntegers L)) = (y : v.adicCompletion K)
    rw [hx.unit_spec, ← algebraMap_norm_eq_norm_algebraMap K L v w x, hxy]
    rfl

end IsDedekindDomain.HeightOneSpectrum

end
