import Langlands.TotallyRamifiedNormRange
import Langlands.TotallyRamifiedNormResidueImage
import Mathlib.GroupTheory.Index

/-!
# The totally ramified norm-group index, at the `(v.adicCompletion K)ˣ` level

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`, `e := v.asIdeal.ramificationIdx' w.asIdeal`. This file bridges
`Langlands.TotallyRamifiedNormResidueImage`'s `K₀ˣ`-level index formula
(`index_normUnitsK₀_range_eq_of_isTotallyRamified`) up to the ambient-field index
`[(v.adicCompletion K)ˣ : MonoidHom.range (localNormMap K L v w)]`, closing the gap left open by
that file's module docstring.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.range_units_map_algebraMap_adicCompletionIntegers_eq` : the
  generic embedding-range lemma, proved once and instantiated at both `K` and `L`.
* `IsDedekindDomain.HeightOneSpectrum.index_localNormMap_range_eq_index_normUnitsK₀_of_isTotallyRamified`
  : the field-level norm index equals the `K₀ˣ`-level norm index, exactly, under
  `IsTotallyRamified` alone — no `IsTamelyRamified`. Applies to wild totally ramified extensions.
-/

noncomputable section

open IsDedekindDomain IsLocalRing

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

/-! ### Step 0: the embedding range lemma -/

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F]

/-- **The image of `K₀ˣ` (or `L₀ˣ`) inside the ambient field's units is exactly the local units.**
`Units.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))` has range exactly
`(v.adicCompletionIntegers F).units`. -/
theorem range_units_map_algebraMap_adicCompletionIntegers_eq (v : HeightOneSpectrum A) :
    MonoidHom.range
        (Units.map
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).toMonoidHom) =
      (v.adicCompletionIntegers F).units := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact Submonoid.mem_units_of_val_mem_inv_val_mem _ (x : v.adicCompletionIntegers F).2
      ((x⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
  · intro y hy
    obtain ⟨hy1, hy2⟩ :=
      (Submonoid.mem_units_iff (v.adicCompletionIntegers F).toSubmonoid y).mp hy
    set y₀ : v.adicCompletionIntegers F := ⟨(y : v.adicCompletion F), hy1⟩ with hy₀def
    have hy₀u : IsUnit y₀ := by
      refine IsUnit.of_mul_eq_one
        (⟨(y⁻¹ : (v.adicCompletion F)ˣ), hy2⟩ : v.adicCompletionIntegers F) ?_
      apply Subtype.ext
      show (y : v.adicCompletion F) * ((y⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1
      exact_mod_cast y.mul_inv
    refine ⟨hy₀u.unit, ?_⟩
    apply Units.ext
    show algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (hy₀u.unit : _) = y
    rw [hy₀u.unit_spec, hy₀def]
    rfl

/-! ### Task 2: the "K-self" uniformizer decomposition -/

section KSelfDecomposition

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F] (v : HeightOneSpectrum A)

/-- **Base case of the "K-self" uniformizer decomposition.** If a unit `a` of `v.adicCompletion F`
has `Valued.v a ≤ 1` (i.e. `a` lies in `v.adicCompletionIntegers F`), it decomposes as `a = π^n * u`
for some `n : ℕ` and unit `u` of `v.adicCompletionIntegers F`, for any irreducible `π :
v.adicCompletionIntegers F`. The single-field (no extension) analogue of
`exists_pow_mul_unit_eq_of_valued_le_one_of_irreducible`, with `S := A`, `L := F`, `w := v`
stripped out entirely (that reflexive self-instantiation was tried first, per the task brief, but
synthesizing the requisite self-instances for `IsScalarTower`/`Module.Finite`/`LiesOver` did not
typecheck cleanly within a couple of attempts, so this direct standalone proof — a verbatim copy of
the extension-agnostic reasoning — is used instead). -/
theorem exists_pow_mul_unit_eq_of_valued_le_one_of_irreducible_self
    {π : v.adicCompletionIntegers F} (hπ : Irreducible π)
    {a : (v.adicCompletion F)ˣ} (hle : Valued.v (a : v.adicCompletion F) ≤ 1) :
    ∃ (n : ℕ) (u : (v.adicCompletionIntegers F)ˣ),
      (a : v.adicCompletion F) =
        ((π : v.adicCompletionIntegers F) : v.adicCompletion F) ^ n * (u : v.adicCompletion F) := by
  set x : v.adicCompletionIntegers F :=
    ⟨(a : v.adicCompletion F), (mem_adicCompletionIntegers A F v).mpr hle⟩ with hxdef
  have hx0 : x ≠ 0 := by
    rw [Ne, ← ZeroMemClass.coe_eq_zero]
    exact a.ne_zero
  obtain ⟨n, u₀, hu₀⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0 hπ
  refine ⟨n, u₀⁻¹, ?_⟩
  have hval : x = π ^ n * ((u₀⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :=
    (Units.eq_mul_inv_iff_mul_eq u₀).mpr hu₀
  have hcast := congrArg (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) hval
  simp only [map_mul, map_pow] at hcast
  rw [hxdef] at hcast
  exact hcast

/-- **The "K-self" uniformizer decomposition.** Every unit `a` of `v.adicCompletion F` decomposes
as `a = π^k * u` for some `k : ℤ` and some unit `u` of `v.adicCompletionIntegers F`, for any
irreducible `π : v.adicCompletionIntegers F` — the single-field analogue of
`exists_zpow_mul_unit_eq_of_irreducible`, needed in Task 3 to decompose an arbitrary unit of
`(v.adicCompletion K)ˣ` against a `K₀`-uniformizer (as opposed to `N(π_L)`, the object
`exists_zpow_mul_unit_eq_of_irreducible` decomposes against). -/
theorem exists_zpow_mul_unit_eq_of_irreducible_self
    {π : v.adicCompletionIntegers F} (hπ : Irreducible π) (a : (v.adicCompletion F)ˣ) :
    ∃ (k : ℤ) (u : (v.adicCompletionIntegers F)ˣ),
      (a : v.adicCompletion F) =
        ((π : v.adicCompletionIntegers F) : v.adicCompletion F) ^ k * (u : v.adicCompletion F) := by
  rcases le_total (Valued.v (a : v.adicCompletion F)) 1 with hle | hge
  · obtain ⟨n, u, hnu⟩ := exists_pow_mul_unit_eq_of_valued_le_one_of_irreducible_self v hπ hle
    exact ⟨(n : ℤ), u, by rw [hnu, zpow_natCast]⟩
  · have hinv_le : Valued.v (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) ≤ 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨n, u, hnu⟩ :=
      exists_pow_mul_unit_eq_of_valued_le_one_of_irreducible_self v hπ hinv_le
    refine ⟨-(n : ℤ), u⁻¹, ?_⟩
    rw [Units.val_inv_eq_inv_val] at hnu
    have ha : (a : v.adicCompletion F) = ((a : v.adicCompletion F)⁻¹)⁻¹ := (inv_inv _).symm
    have hinv : ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletion F) =
        ((u : (v.adicCompletionIntegers F)ˣ) : v.adicCompletion F)⁻¹ := by
      have h1 : (u : v.adicCompletionIntegers F) *
          ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) = 1 := u.mul_inv
      have h2 : ((u : v.adicCompletionIntegers F) : v.adicCompletion F) *
          (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :
            v.adicCompletion F) = 1 := by exact_mod_cast h1
      exact eq_inv_of_mul_eq_one_right h2
    rw [ha, hnu, mul_inv, ← hinv, zpow_neg, zpow_natCast]

end KSelfDecomposition

/-! ### Task 1: the bridging lemma -/

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]

/-- The embedding `K₀ˣ ↪ (v.adicCompletion K)ˣ`, with range exactly `(v.adicCompletionIntegers
K).units` (`range_units_map_algebraMap_adicCompletionIntegers_eq`). -/
def embedK : (v.adicCompletionIntegers K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom

/-- The embedding `L₀ˣ ↪ (w.adicCompletion L)ˣ`, with range exactly `(w.adicCompletionIntegers
L).units` (`range_units_map_algebraMap_adicCompletionIntegers_eq`). -/
def embedL : (w.adicCompletionIntegers L)ˣ →* (w.adicCompletion L)ˣ :=
  Units.map (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)).toMonoidHom

omit [Algebra.IsIntegral R S] in
/-- `embedK`'s range is exactly `(v.adicCompletionIntegers K).units` (a restatement of
`range_units_map_algebraMap_adicCompletionIntegers_eq` in terms of the `embedK` abbreviation, for
`rw`-friendliness downstream). -/
theorem range_embedK_eq : MonoidHom.range (embedK K v) = (v.adicCompletionIntegers K).units :=
  range_units_map_algebraMap_adicCompletionIntegers_eq v

omit [Algebra.IsIntegral R S] in
/-- `embedL`'s range is exactly `(w.adicCompletionIntegers L).units` (a restatement of
`range_units_map_algebraMap_adicCompletionIntegers_eq` in terms of the `embedL` abbreviation, for
`rw`-friendliness downstream). -/
theorem range_embedL_eq : MonoidHom.range (embedL L w) = (w.adicCompletionIntegers L).units :=
  range_units_map_algebraMap_adicCompletionIntegers_eq w

omit [Algebra.IsIntegral R S] in
/-- **`localNormMap ∘ embedL = embedK ∘ normUnitsK₀`.** The square commutes: pushing a unit of
`L₀` into `(w.adicCompletion L)ˣ` and then taking the local norm agrees with first taking the
`K₀`-level norm and then pushing into `(v.adicCompletion K)ˣ`. This is exactly
`algebraMap_norm_eq_norm_algebraMap`, transported from `Algebra.norm` to `Units.map`. -/
theorem localNormMap_comp_embedL_eq :
    (localNormMap K L v w).comp (embedL L w) = (embedK K v).comp (normUnitsK₀ K L v w) := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  show Algebra.norm (v.adicCompletion K)
      (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)
        (x : w.adicCompletionIntegers L)) =
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (Algebra.norm (v.adicCompletionIntegers K) (x : w.adicCompletionIntegers L))
  rw [algebraMap_norm_eq_norm_algebraMap K L v w x]

omit [Algebra.IsIntegral R S] in
/-- **Task 1: the bridging lemma.** `N_{L/K}(U_L)`, at the `(v.adicCompletion K)ˣ` level (the
literal image `(w.adicCompletionIntegers L).units.map (localNormMap K L v w)` that
`localNormMap_range_eq_of_isTotallyRamified` is phrased in terms of), coincides with the
`K₀ˣ`-level range `MonoidHom.range (normUnitsK₀ K L v w)` pushed forward along `embedK`. Proved by
rewriting `(w.adicCompletionIntegers L).units` as `MonoidHom.range (embedL L w)` (Step 0) and
pushing both sides of the commuting square (`localNormMap_comp_embedL_eq`) through
`MonoidHom.map_range`. -/
theorem units_map_localNormMap_eq_map_normUnitsK₀ :
    (w.adicCompletionIntegers L).units.map (localNormMap K L v w) =
      (MonoidHom.range (normUnitsK₀ K L v w)).map (embedK K v) := by
  rw [← range_embedL_eq L w, MonoidHom.map_range, MonoidHom.map_range,
    localNormMap_comp_embedL_eq K L v w]

/-! ### Task 3: assembling the index -/

variable [Finite (ResidueField (w.adicCompletionIntegers L))]

omit [Algebra.IsIntegral R S] in
/-- `embedK` is injective: `algebraMap K₀ (v.adicCompletion K)` is the subtype inclusion, hence
injective, and `Units.map` of an injective monoid hom is injective. -/
theorem embedK_injective : Function.Injective (embedK K v) :=
  Units.map_injective Subtype.coe_injective

omit [Algebra.IsIntegral R S] in
/-- A uniformizer of `K₀` has valuation strictly between `0` and `1` in `(v.adicCompletion K)ˣ`.
-/
theorem valued_coe_lt_one_of_irreducible {π : v.adicCompletionIntegers K} (hπ : Irreducible π) :
    0 < Valued.v (π : v.adicCompletion K) ∧ Valued.v (π : v.adicCompletion K) < 1 := by
  refine ⟨(zero_lt_iff).mpr ?_, ?_⟩
  · rw [Ne, Valuation.zero_iff, ZeroMemClass.coe_eq_zero]
    exact hπ.ne_zero
  · have hmem : π ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
      hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
    exact Valuation.mem_maximalIdeal_iff (v.adicCompletion K) Valued.v |>.mp hmem

omit [Algebra.IsIntegral R S] in
/-- **Task 3, step 1: `G ⊔ U_K = ⊤`.** Every unit `a` of `(v.adicCompletion K)ˣ` decomposes
(`exists_zpow_mul_unit_eq_of_irreducible_self`, applied to `π := N(π_L)`) as `a = π'^k * embedK u`
for `π' := uniformizerUnit K v (irreducible_norm_of_isTotallyRamified ...)` — the same generator
`localNormMap_range_eq_of_isTotallyRamified` uses for `G`'s cyclic part — so `a ∈ zpowers π' ⊔ U_K
≤ G ⊔ U_K`, using `π' ∈ G` (`uniformizerUnit_norm_mem_range`). -/
theorem sup_units_eq_top (h : IsTotallyRamified K L v w) {πL : w.adicCompletionIntegers L}
    (hπL : Irreducible πL) :
    MonoidHom.range (localNormMap K L v w) ⊔ (v.adicCompletionIntegers K).units = ⊤ := by
  set hπ := irreducible_norm_of_isTotallyRamified K L v w h hπL with hπirr
  set π' := uniformizerUnit K v hπ with hπ'def
  rw [eq_top_iff]
  rintro a -
  obtain ⟨k, u, hku⟩ := exists_zpow_mul_unit_eq_of_irreducible_self v hπ a
  have ha : a = π' ^ k * embedK K v u := by
    apply Units.ext
    push_cast
    rw [coe_uniformizerUnit]
    exact hku
  rw [ha]
  refine Subgroup.mul_mem_sup ?_ ?_
  · exact Subgroup.zpow_mem _ (uniformizerUnit_norm_mem_range K L v w h hπL) k
  · have hmem : embedK K v u ∈ MonoidHom.range (embedK K v) := ⟨u, rfl⟩
    rwa [range_embedK_eq K v] at hmem

omit [Algebra.IsIntegral R S] in
/-- **Task 3, step 2: `G ⊓ U_K = U_K'`.** `⊇` is immediate from
`localNormMap_range_eq_of_isTotallyRamified` (`U_K' ≤ G`) and `localNormMap_mem_units` (`U_K' ≤
U_K`). `⊆`: writing `y = π'^k * u'` for `u' ∈ U_K'` (from `G`'s exact-range decomposition), `u' ∈
U_K` forces `π'^k = y * u'⁻¹ ∈ U_K`, i.e. `Valued.v π' ^ k = 1`; since `0 < Valued.v π' < 1`
(`valued_coe_lt_one_of_irreducible`), `zpow_right_strictAnti₀` is injective, forcing `k = 0`, so
`y = u' ∈ U_K'`. -/
theorem inf_units_eq_units_map (h : IsTotallyRamified K L v w) {πL : w.adicCompletionIntegers L}
    (hπL : Irreducible πL) :
    MonoidHom.range (localNormMap K L v w) ⊓ (v.adicCompletionIntegers K).units =
      (w.adicCompletionIntegers L).units.map (localNormMap K L v w) := by
  set hπ := irreducible_norm_of_isTotallyRamified K L v w h hπL with hπirr
  set π' := uniformizerUnit K v hπ with hπ'def
  apply le_antisymm
  · rintro y ⟨hyG, hyU⟩
    rw [localNormMap_range_eq_of_isTotallyRamified K L v w h hπL] at hyG
    obtain ⟨a, ha, u', hu', hau⟩ := Subgroup.mem_sup.mp hyG
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨x, hxmem, hxeq⟩ := hu'
    have hu'U : u' ∈ (v.adicCompletionIntegers K).units := by
      rw [← hxeq]
      exact localNormMap_mem_units K L v w hxmem
    have ha' : π' ^ k = y * u'⁻¹ := by
      rw [hk]
      exact eq_mul_inv_of_mul_eq hau
    have hpk_mem : π' ^ k ∈ (v.adicCompletionIntegers K).units := by
      rw [ha']
      exact Subgroup.mul_mem _ hyU (Subgroup.inv_mem _ hu'U)
    have hval1 : Valued.v ((π' ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 :=
      adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hpk_mem
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ'def, coe_uniformizerUnit] at hval1
    obtain ⟨hpos, hlt⟩ := valued_coe_lt_one_of_irreducible K v hπ
    have hk0 : k = 0 := (zpow_right_strictAnti₀ hpos hlt).injective (by simpa using hval1)
    have ha0 : a = 1 := by rw [← hk, hk0, zpow_zero]
    refine ⟨x, hxmem, ?_⟩
    have hyu' : y = u' := by rw [← hau, ha0, one_mul]
    exact hxeq.trans hyu'.symm
  · intro y hy
    obtain ⟨x, hxmem, hxy⟩ := hy
    refine ⟨⟨x, hxy⟩, ?_⟩
    rw [← hxy]
    exact localNormMap_mem_units K L v w hxmem

omit [Algebra.IsIntegral R S] in
/-- **The totally ramified norm-group index equals the `K₀ˣ`-level norm-group index, exactly, with
NO tameness hypothesis.** `[(v.adicCompletion K)ˣ : MonoidHom.range (localNormMap K L v w)] =
[K₀ˣ : MonoidHom.range (normUnitsK₀ K L v w)]`.

This is `sup_units_eq_top` and `inf_units_eq_units_map` (both `IsTotallyRamified`-only, no
`IsTamelyRamified`) chased through the same `Subgroup.relIndex` algebra as
`index_localNormMap_range_eq_of_isTotallyRamified` below, stopped one rewrite short of that
theorem's final step: `index_normUnitsK₀_range_eq_of_isTotallyRamified` (which *does* need
`IsTamelyRamified`) is never invoked. Consequently this holds for the wild case too — e.g. the
concrete `K = ℚ_3(ζ_3) ⊆ L = ℚ_3(ζ_9)` instance
(`Langlands.TotallyRamifiedCyclotomicConcreteExample`), where `e = p = 3` is genuinely wild. -/
theorem index_localNormMap_range_eq_index_normUnitsK₀_of_isTotallyRamified
    (h : IsTotallyRamified K L v w) {πL : w.adicCompletionIntegers L} (hπL : Irreducible πL) :
    (MonoidHom.range (localNormMap K L v w)).index =
      (MonoidHom.range (normUnitsK₀ K L v w)).index := by
  set G := MonoidHom.range (localNormMap K L v w) with hGdef
  set U_K := (v.adicCompletionIntegers K).units with hUKdef
  haveI hGnormal : G.Normal := G.normal_of_isMulCommutative
  have hstep1 : G ⊔ U_K = ⊤ := sup_units_eq_top K L v w h hπL
  have hstep2 : G ⊓ U_K = (w.adicCompletionIntegers L).units.map (localNormMap K L v w) :=
    inf_units_eq_units_map K L v w h hπL
  have hidx : G.index = G.relIndex U_K := by
    rw [← Subgroup.relIndex_top_right (H := G), ← hstep1, Subgroup.relIndex_sup_left]
  rw [hidx, ← Subgroup.inf_relIndex_right, hstep2, units_map_localNormMap_eq_map_normUnitsK₀ K L v w,
    show U_K = Subgroup.map (embedK K v) ⊤ from
      (range_embedK_eq K v).symm.trans (MonoidHom.range_eq_map _),
    Subgroup.relIndex_map_map_of_injective _ _ (embedK_injective K v),
    Subgroup.relIndex_top_right]

omit [Algebra.IsIntegral R S] in
/-- **Task 3: the totally ramified norm-group index.** `[(v.adicCompletion K)ˣ :
MonoidHom.range (localNormMap K L v w)] = gcd(e, #κ[K]ˣ)`, the classical formula, transported from
the `K₀ˣ`-level index formula `index_normUnitsK₀_range_eq_of_isTotallyRamified` via
`Subgroup.relIndex` algebra (steps 1–2 above) and `Subgroup.relIndex_map_map_of_injective`
(`embedK` injective). -/
theorem index_localNormMap_range_eq_of_isTotallyRamified (h : IsTotallyRamified K L v w)
    (htame : IsTamelyRamified K L v w) {πL : w.adicCompletionIntegers L} (hπL : Irreducible πL) :
    (MonoidHom.range (localNormMap K L v w)).index =
      Nat.gcd (v.asIdeal.ramificationIdx' w.asIdeal)
        (Nat.card (ResidueField (v.adicCompletionIntegers K))ˣ) := by
  set G := MonoidHom.range (localNormMap K L v w) with hGdef
  set U_K := (v.adicCompletionIntegers K).units with hUKdef
  haveI hGnormal : G.Normal := G.normal_of_isMulCommutative
  have hstep1 : G ⊔ U_K = ⊤ := sup_units_eq_top K L v w h hπL
  have hstep2 : G ⊓ U_K = (w.adicCompletionIntegers L).units.map (localNormMap K L v w) :=
    inf_units_eq_units_map K L v w h hπL
  have hidx : G.index = G.relIndex U_K := by
    rw [← Subgroup.relIndex_top_right (H := G), ← hstep1, Subgroup.relIndex_sup_left]
  rw [hidx, ← Subgroup.inf_relIndex_right, hstep2, units_map_localNormMap_eq_map_normUnitsK₀ K L v w,
    show U_K = Subgroup.map (embedK K v) ⊤ from
      (range_embedK_eq K v).symm.trans (MonoidHom.range_eq_map _),
    Subgroup.relIndex_map_map_of_injective _ _ (embedK_injective K v),
    Subgroup.relIndex_top_right, index_normUnitsK₀_range_eq_of_isTotallyRamified K L v w h htame]

end IsDedekindDomain.HeightOneSpectrum

end
