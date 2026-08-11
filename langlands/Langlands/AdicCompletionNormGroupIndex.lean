import Langlands.AdicCompletionNormGroupImage
import Langlands.AdicCompletionUnitsValuationHom
import Langlands.AdicCompletionValuationNorm
import Langlands.FiniteIndexSubgroupsZ
import Langlands.PrincipalUnitsFiltrationIndex
import Langlands.TotallyRamifiedNormIndex

/-!
# The wild-case norm-group index, bounded by a filtration level

Let `K₀ := v.adicCompletionIntegers K`, `L₀ := w.adicCompletionIntegers L`, `e :=
v.asIdeal.ramificationIdx' w.asIdeal`, and let `d` be the different exponent
(`differentIdeal K₀ L₀ = 𝔪_{L₀} ^ d`). `Langlands.AdicCompletionNormGroupImage` computes the norm
group of a deep filtration level exactly,

`N_{L_w/K_v}(U_{L₀}^{(i)}) = U_{K₀}^{((i + d) / e)}` for `i ≫ 0`,

with no tameness hypothesis. This file turns that equality into *index* statements, mirroring the
`Subgroup.relIndex` bridging of `Langlands.TotallyRamifiedNormIndex` — but the bridging argument is
different, and the conclusion is weaker in a way that is intrinsic, not an artifact of the proof.

## What transfers from the tame case, and what does not

`TotallyRamifiedNormIndex`'s Task 3 computes `[K_vˣ : N(L_wˣ)]` on the nose, from two facts:

* `sup_units_eq_top` : `N(L_wˣ) ⊔ U_{K_v} = ⊤`, because under `IsTotallyRamified` the norm of a
  uniformizer of `L₀` is a uniformizer of `K₀`, so the norm group already meets every valuation
  class; and
* `inf_units_eq_units_map` : `N(L_wˣ) ⊓ U_{K_v} = N(U_{L₀})`, again via that uniformizer
  decomposition.

Neither is available here. Without total ramification the valuations of norms form the subgroup
`f · v(K_vˣ)` (`f` the residue degree), so `N(L_wˣ) ⊔ U_{K_v} = ⊤` is simply false in general
(unless `f = 1`) — but the valuation-side factor `[K_vˣ : N(L_wˣ) ⊔ U_{K_v}]` itself **is** computed
here, exactly, as `f` (`index_sup_units_eq_inertiaDeg'`), via the valuation-of-norm formula
(`Langlands.AdicCompletionValuationNorm.valued_localNormMap_eq_pow`) pushed through the surjective
`MonoidHom (v.adicCompletion K)ˣ →* ℤᵐ⁰ˣ` built from `Valued.v`
(`Langlands.AdicCompletionUnitsValuationHom.valuationUnitsHom`) and the index-comap identity for
surjective homs. What is *not* available is `inf_units_eq_units_map`'s exact computation of
`N(L_wˣ) ⊓ U_{K_v}`; only the containment `N(U_{L₀}^{(i)}) ≤ N(L_wˣ) ⊓ U_{K_v}` holds
unconditionally, which bounds the units-side factor. So the results below are stated as:

* the valuation-side factor `[K_vˣ : N(L_wˣ) ⊔ U_{K_v}] = f` — **exact**, unconditionally
  (`index_sup_units_eq_inertiaDeg'`);
* the **relative** index `[U_{K_v} : N(L_wˣ) ⊓ U_{K_v}]` — the units-side factor — is *divisible
  into* the index of a filtration level, hence finite, but not computed exactly;
* the total index `[K_vˣ : N(L_wˣ)]` factors as (valuation-side) · (units-side)
  (`index_range_localNormMap_eq_mul`), with the first factor now known exactly (`= f`) and the
  second bounded, not computed, here.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.relIndex_range_localNormMap_units_dvd_index_map_normUnitsK₀` :
  the generic bridging lemma. For *any* subgroup `X ≤ L₀ˣ`, `[U_{K_v} : N(L_wˣ) ⊓ U_{K_v}]` divides
  `[K₀ˣ : N(X)]`. No tameness, no exponential, no hypothesis on `X`.
* `IsDedekindDomain.HeightOneSpectrum.exists_index_dvd_index_principalUnitsPow` : the wild-case
  instantiation — for some `j`, both `[K₀ˣ : N(L₀ˣ)]` and `[U_{K_v} : N(L_wˣ) ⊓ U_{K_v}]` divide
  `[K₀ˣ : U_{K₀}^{(j+1)}] = #κ_{K₀}ˣ · (#κ_{K₀})^j` (`ValuationSubring.index_principalUnitsPow`).
* `IsDedekindDomain.HeightOneSpectrum.index_ne_zero_of_finite_residueField` : the qualitative
  headline — with a finite residue field, the local-unit norm group `N(L₀ˣ) ≤ K₀ˣ` has *finite
  index*, and so does `N(L_wˣ) ⊓ U_{K_v}` inside `U_{K_v}`, in the wild case, with no tameness
  hypothesis.
* `IsDedekindDomain.HeightOneSpectrum.index_range_localNormMap_eq_mul` : the factorization
  `[K_vˣ : N(L_wˣ)] = [K_vˣ : N(L_wˣ) ⊔ U_{K_v}] · [U_{K_v} : N(L_wˣ) ⊓ U_{K_v}]`.
* `IsDedekindDomain.HeightOneSpectrum.index_sup_units_eq_inertiaDeg'` : the valuation-side factor,
  computed exactly: `[K_vˣ : N(L_wˣ) ⊔ U_{K_v}] = v.asIdeal.inertiaDeg' w.asIdeal`, with no tameness
  hypothesis.
* `IsDedekindDomain.HeightOneSpectrum.index_range_localNormMap_eq_inertiaDeg'_mul_relIndex` :
  `index_range_localNormMap_eq_mul` and `index_sup_units_eq_inertiaDeg'` combined,
  `[K_vˣ : N(L_wˣ)] = f · [U_{K_v} : N(L_wˣ) ⊓ U_{K_v}]`.

## Scope

`d` remains a hypothesis, inherited from `Langlands.AdicCompletionTraceSurjectivity`. Filtration
levels below the `exp`/`log` threshold are untouched, which is exactly why the units-side results
here are divisibilities rather than equalities: `N(U_{L₀})` may be strictly larger than
`N(U_{L₀}^{(i)})`, and nothing here computes that gap. The valuation-side factor
`[K_vˣ : N(L_wˣ) ⊔ U_{K_v}]` **is** now computed exactly, as `f`
(`index_sup_units_eq_inertiaDeg'`) — the remaining gap in this file is entirely on the units side.
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
/-- The `K₀ˣ`-level norm image of any `X ≤ L₀ˣ`, pushed into `K_vˣ`, lands in the field-level norm
group: the square `localNormMap ∘ embedL = embedK ∘ normUnitsK₀` commutes
(`localNormMap_comp_embedL_eq`). -/
theorem map_embedK_map_normUnitsK₀_le_range_localNormMap
    (X : Subgroup (w.adicCompletionIntegers L)ˣ) :
    Subgroup.map (embedK K v) (Subgroup.map (normUnitsK₀ K L v w) X) ≤
      MonoidHom.range (localNormMap K L v w) := by
  rw [Subgroup.map_map, ← localNormMap_comp_embedL_eq K L v w, ← Subgroup.map_map]
  exact Subgroup.map_le_range _ _

omit [Algebra.IsIntegral R S] in
/-- **The wild-case bridging lemma.** For *any* subgroup `X` of `L₀ˣ`, the relative index of the
field-level norm group inside the local units,

`[U_{K_v} : N_{L_w/K_v}(L_wˣ) ⊓ U_{K_v}]`,

divides the `K₀ˣ`-level index `[K₀ˣ : N(X)]` of the norm image of `X`.

This is the wild analogue of `TotallyRamifiedNormIndex`'s Task 3 steps, with the tame-specific
uniformizer decomposition removed: only the containment `N(X) ≤ N(L_wˣ) ⊓ U_{K_v}` is used (via
`map_embedK_map_normUnitsK₀_le_range_localNormMap` and `range_embedK_eq`), so no tameness, no
`IsTotallyRamified`, and no information about `X` is needed. The price is that the conclusion is a
divisibility, not the equality the tame argument obtains — see this file's module docstring. -/
theorem relIndex_range_localNormMap_units_dvd_index_map_normUnitsK₀
    (X : Subgroup (w.adicCompletionIntegers L)ˣ) :
    (MonoidHom.range (localNormMap K L v w)).relIndex (v.adicCompletionIntegers K).units ∣
      (Subgroup.map (normUnitsK₀ K L v w) X).index := by
  set G := MonoidHom.range (localNormMap K L v w) with hG
  set U := (v.adicCompletionIntegers K).units with hU
  set P := Subgroup.map (normUnitsK₀ K L v w) X with hP
  set M := Subgroup.map (embedK K v) P with hM
  have hinj : Function.Injective (embedK K v) := Units.map_injective Subtype.coe_injective
  have hUmap : U = Subgroup.map (embedK K v) ⊤ :=
    (range_embedK_eq K v).symm.trans (MonoidHom.range_eq_map _)
  have hMG : M ≤ G := map_embedK_map_normUnitsK₀_le_range_localNormMap K L v w X
  have hMU : M ≤ U := by
    rw [hUmap]
    exact Subgroup.map_mono le_top
  have hMinf : M ≤ G ⊓ U := le_inf hMG hMU
  have hmul := Subgroup.relIndex_mul_relIndex M (G ⊓ U) U hMinf inf_le_right
  have hMrel : M.relIndex U = P.index := by
    rw [hM, hUmap, Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.relIndex_top_right]
  rw [← Subgroup.inf_relIndex_right (H := G) (K := U), ← hMrel]
  exact dvd_of_mul_left_eq _ hmul

variable [FiniteDimensional (v.adicCompletion K) (w.adicCompletion L)]
variable [CharZero K] [CharZero L] (p : ℕ) [hp : Fact p.Prime]

omit [Algebra.IsIntegral R S] in
/-- **The wild-case index bound at a filtration level.** For every `i` above the threshold of
`exists_map_principalUnitsPow_normUnitsK₀_eq` with `(i + d) / e ≠ 0`, both

* the `K₀ˣ`-level norm-group index `[K₀ˣ : N(L₀ˣ)]`, and
* the field-level relative index `[U_{K_v} : N(L_wˣ) ⊓ U_{K_v}]`

divide `[K₀ˣ : U_{K₀}^{((i+d)/e)}] = #κ_{K₀}ˣ · (#κ_{K₀})^{(i+d)/e - 1}`. Packaged existentially in
`i`, since the threshold itself is existential. -/
theorem exists_index_dvd_index_principalUnitsPow
    [IsGalois (v.adicCompletion K) (w.adicCompletion L)] {d : ℕ}
    (hd : differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      maximalIdeal (w.adicCompletionIntegers L) ^ d)
    (hnormK : ‖(p : v.adicCompletion K)‖ < 1) (hnormL : ‖(p : w.adicCompletion L)‖ < 1) :
    ∃ j : ℕ,
      (MonoidHom.range (normUnitsK₀ K L v w)).index ∣
          (ValuationSubring.principalUnitsPow (v.adicCompletionIntegers K) (j + 1)).index ∧
        (MonoidHom.range (localNormMap K L v w)).relIndex
            (v.adicCompletionIntegers K).units ∣
          (ValuationSubring.principalUnitsPow (v.adicCompletionIntegers K) (j + 1)).index := by
  obtain ⟨i₀, hi₀⟩ :=
    exists_map_principalUnitsPow_normUnitsK₀_eq K L v w p hd hnormK hnormL
  have he0 : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
  set e := v.asIdeal.ramificationIdx' w.asIdeal with he
  set i := max i₀ e with hi
  have hikey := hi₀ i (le_max_left _ _)
  have hj : (i + d) / e ≠ 0 := by
    have hei : e ≤ i := le_max_right _ _
    have h1 : 1 ≤ (i + d) / e :=
      (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero he0)).mpr (by omega)
    omega
  obtain ⟨j, hjeq⟩ := Nat.exists_eq_succ_of_ne_zero hj
  rw [hjeq] at hikey
  refine ⟨j, ?_, ?_⟩
  · rw [← hikey]
    exact Subgroup.index_dvd_of_le (Subgroup.map_le_range _ _)
  · rw [← hikey]
    exact relIndex_range_localNormMap_units_dvd_index_map_normUnitsK₀ K L v w _

omit [Algebra.IsIntegral R S] in
/-- **The wild-case norm group of local units has finite index.** With a finite residue field and no
tameness hypothesis, `[K₀ˣ : N_{L_w/K_v}(L₀ˣ)] ≠ 0` and
`[U_{K_v} : N_{L_w/K_v}(L_wˣ) ⊓ U_{K_v}] ≠ 0`.

Both follow from `exists_index_dvd_index_principalUnitsPow` together with
`ValuationSubring.index_principalUnitsPow_ne_zero`: a divisor of a nonzero natural number is
nonzero. This is the qualitative half of local class field theory's finiteness input on the units
side; the valuation side (`[K_vˣ : N(L_wˣ) ⊔ U_{K_v}]`) is not addressed here. -/
theorem index_ne_zero_of_finite_residueField
    [IsGalois (v.adicCompletion K) (w.adicCompletion L)]
    [Finite (ResidueField (v.adicCompletionIntegers K))] {d : ℕ}
    (hd : differentIdeal (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      maximalIdeal (w.adicCompletionIntegers L) ^ d)
    (hnormK : ‖(p : v.adicCompletion K)‖ < 1) (hnormL : ‖(p : w.adicCompletion L)‖ < 1) :
    (MonoidHom.range (normUnitsK₀ K L v w)).index ≠ 0 ∧
      (MonoidHom.range (localNormMap K L v w)).relIndex
        (v.adicCompletionIntegers K).units ≠ 0 := by
  obtain ⟨j, hdvd1, hdvd2⟩ :=
    exists_index_dvd_index_principalUnitsPow K L v w p hd hnormK hnormL
  obtain ⟨πK, hπKirr⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hπK : maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span ({πK} : Set (v.adicCompletionIntegers K)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer πK).mp hπKirr
  have hne : (ValuationSubring.principalUnitsPow (v.adicCompletionIntegers K) (j + 1)).index ≠ 0 :=
    ValuationSubring.index_principalUnitsPow_ne_zero _ hπK hπKirr.ne_zero j
  exact ⟨fun h => hne (zero_dvd_iff.mp (h ▸ hdvd1)), fun h => hne (zero_dvd_iff.mp (h ▸ hdvd2))⟩

omit [Module.Finite K L] [Algebra.IsIntegral R S]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]
  [FiniteDimensional (v.adicCompletion K) (w.adicCompletion L)] [CharZero K] [CharZero L] in
/-- **The two-factor decomposition of the field-level norm index.**

`[K_vˣ : N(L_wˣ)] = [K_vˣ : N(L_wˣ) ⊔ U_{K_v}] · [U_{K_v} : N(L_wˣ) ⊓ U_{K_v}]`.

The right factor is the one bounded above (`relIndex_range_localNormMap_units_dvd_*`); the left
factor is the valuation-side contribution — classically the residue degree `f` — which this file
does not compute, and which is exactly what the tame argument's `sup_units_eq_top` supplies (as
`1`) in `TotallyRamifiedNormIndex`. Stated unconditionally, for any place pair. -/
theorem index_range_localNormMap_eq_mul :
    (MonoidHom.range (localNormMap K L v w)).index =
      (MonoidHom.range (localNormMap K L v w) ⊔ (v.adicCompletionIntegers K).units).index *
        (MonoidHom.range (localNormMap K L v w)).relIndex
          (v.adicCompletionIntegers K).units := by
  set G := MonoidHom.range (localNormMap K L v w) with hG
  set U := (v.adicCompletionIntegers K).units with hU
  haveI : G.Normal := G.normal_of_isMulCommutative
  rw [mul_comm, ← Subgroup.relIndex_sup_left (H := U) (K := G),
    Subgroup.relIndex_mul_index le_sup_left]

omit [Algebra.IsIntegral R S] [FiniteDimensional (v.adicCompletion K) (w.adicCompletion L)]
  [CharZero L] in
/-- **The valuation-side factor of the norm-group index, computed exactly.**
`[K_vˣ : N_{L_w/K_v}(L_wˣ) ⊔ U_{K_v}] = v.asIdeal.inertiaDeg' w.asIdeal`, with no tameness
hypothesis — the factor `TotallyRamifiedNormIndex.sup_units_eq_top` computes as `1` under
`IsTotallyRamified`, and which `index_range_localNormMap_eq_mul` otherwise leaves uncomputed.

Route: `φ := valuationUnitsHom K v : K_vˣ →* ℤᵐ⁰ˣ` is surjective with kernel `U_{K_v}`
(`Langlands.AdicCompletionUnitsValuationHom`), so `N(L_wˣ) ⊔ U_{K_v} = comap φ (map φ (N(L_wˣ)))`
(`Subgroup.comap_map_eq`), and its index equals `(map φ (N(L_wˣ))).index`
(`Subgroup.index_comap_of_surjective`). The valuation-of-norm formula
(`valued_localNormMap_eq_pow`) identifies `φ ∘ localNormMap` with `(powMonoidHom f) ∘ ψ` for
`ψ := valuationUnitsHom L w` (also surjective), so `map φ (N(L_wˣ)) = range (powMonoidHom f :
ℤᵐ⁰ˣ →* ℤᵐ⁰ˣ)` (`MonoidHom.range_comp` twice). Transporting that range's index along the `MulEquiv`
`WithZero.unitsWithZeroEquiv : ℤᵐ⁰ˣ ≃* Multiplicative ℤ` (`MulEquiv.map_range_powMonoidHom`,
`Subgroup.index_map_of_bijective`) reduces it to
`Langlands.FiniteIndexSubgroupsZ.MonoidHom.index_range_powMonoidHom_multiplicativeInt`, which gives
exactly `f`. -/
theorem index_sup_units_eq_inertiaDeg' :
    (MonoidHom.range (localNormMap K L v w) ⊔ (v.adicCompletionIntegers K).units).index =
      v.asIdeal.inertiaDeg' w.asIdeal := by
  set f := v.asIdeal.inertiaDeg' w.asIdeal with hf
  set φ := valuationUnitsHom K v with hφ
  set ψ := valuationUnitsHom L w with hψ
  have hφsurj : Function.Surjective φ := valuationUnitsHom_surjective K v
  have hψsurj : Function.Surjective ψ := valuationUnitsHom_surjective L w
  have hcomp : φ.comp (localNormMap K L v w) = (powMonoidHom f).comp ψ := by
    ext a
    simp only [MonoidHom.comp_apply, powMonoidHom_apply, Units.val_pow_eq_pow_val]
    show Valued.v (Algebra.norm (v.adicCompletion K) (a : w.adicCompletion L)) =
      (Valued.v (a : w.adicCompletion L)) ^ f
    exact valued_localNormMap_eq_pow K L v w a
  have hsup : MonoidHom.range (localNormMap K L v w) ⊔ (v.adicCompletionIntegers K).units
      = Subgroup.comap φ (Subgroup.map φ (MonoidHom.range (localNormMap K L v w))) := by
    rw [Subgroup.comap_map_eq, valuationUnitsHom_ker K v]
  rw [hsup,
    Subgroup.index_comap_of_surjective
      (H := Subgroup.map φ (MonoidHom.range (localNormMap K L v w))) hφsurj,
    ← MonoidHom.range_comp, hcomp, MonoidHom.range_comp, ψ.range_eq_top_of_surjective hψsurj,
    ← MonoidHom.range_eq_map]
  set e : ℤᵐ⁰ˣ ≃* Multiplicative ℤ := WithZero.unitsWithZeroEquiv with he
  have hidx := Subgroup.index_map_equiv (H := MonoidHom.range (powMonoidHom f : ℤᵐ⁰ˣ →* ℤᵐ⁰ˣ)) e
  rw [MulEquiv.map_range_powMonoidHom e f] at hidx
  rw [← hidx, MonoidHom.index_range_powMonoidHom_multiplicativeInt]

omit [Algebra.IsIntegral R S] [FiniteDimensional (v.adicCompletion K) (w.adicCompletion L)]
  [CharZero L] in
/-- **The norm-group index, with its valuation-side factor made explicit.**
`[K_vˣ : N(L_wˣ)] = f · [U_{K_v} : N(L_wˣ) ⊓ U_{K_v}]`, `f := v.asIdeal.inertiaDeg' w.asIdeal` —
`index_range_localNormMap_eq_mul`'s two-factor decomposition with the (previously uncomputed)
first factor substituted by `index_sup_units_eq_inertiaDeg'`. The remaining factor,
`[U_{K_v} : N(L_wˣ) ⊓ U_{K_v}]`, is the units-side quantity this file only bounds
(`exists_index_dvd_index_principalUnitsPow`), not computes. -/
theorem index_range_localNormMap_eq_inertiaDeg'_mul_relIndex :
    (MonoidHom.range (localNormMap K L v w)).index =
      v.asIdeal.inertiaDeg' w.asIdeal *
        (MonoidHom.range (localNormMap K L v w)).relIndex (v.adicCompletionIntegers K).units := by
  rw [index_range_localNormMap_eq_mul, index_sup_units_eq_inertiaDeg']

end IsDedekindDomain.HeightOneSpectrum

end
