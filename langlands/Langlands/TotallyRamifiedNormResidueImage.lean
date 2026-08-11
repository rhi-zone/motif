import Langlands.PrincipalUnitsFiltration
import Langlands.TotallyRamifiedNormResidue
import Langlands.TotallyRamifiedNormSurjective
import Langlands.UnitGroupModPrincipalUnitsSurjective
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The level-`0` image of `residue ∘ N`, at the `K₀ˣ` level

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`, `κ := ResidueField K₀`, `e := v.asIdeal.ramificationIdx'
w.asIdeal`. This file computes the exact image of the level-`0` map "`residue` composed with the
ring norm `Algebra.norm K₀ : L₀ → K₀`" as a subgroup of `κˣ`, closing the surjectivity direction
that `Langlands.TotallyRamifiedNormResidue`'s
`residue_norm_eq_residue_pow_ramificationIdx_of_isTotallyRamified` left open (it gives only the
`⊆` half of "the image is the `e`-th powers of `κˣ`").

## Route

`residueNormUnits : L₀ˣ →* κˣ` is `x ↦ residue (Algebra.norm K₀ x)` (well-defined on units since
`Algebra.norm K₀` and `residue K₀` are both `MonoidHom`s, hence send units to units).
`range_residueNormUnits_eq_of_isTotallyRamified` shows, under `IsTotallyRamified` alone (no
tameness), that `MonoidHom.range residueNormUnits = MonoidHom.range (powMonoidHom e)`:

* `⊆`: for `x : L₀ˣ`, `IsTotallyRamified.exists_sub_algebraMap_mem_maximalIdeal` gives `r : K₀`
  with `x ≡ algebraMap r (mod 𝔪_L)`, so
  `residue_norm_eq_residue_pow_ramificationIdx_of_isTotallyRamified` gives
  `residue (N x) = (residue r) ^ e`. Since `x` is a unit, so is `N x` (norm is a `MonoidHom`), so
  `residue (N x) ≠ 0`; since `κ` is a field (no zero divisors) this forces `residue r ≠ 0`, i.e.
  `residue r` is a unit of `κ` (`isUnit_iff_ne_zero`), witnessing membership in the range of
  `powMonoidHom e`.
* `⊇`: for `s : κˣ`, `Langlands.UnitGroupModPrincipalUnitsSurjective`'s
  `surjective_units_map_residue` (applied to `K₀`, not `L₀`) gives `r₀ : K₀ˣ` with
  `residue r₀ = s`. Taking `x := algebraMap K₀ L₀ r₀` directly (not via any lift chosen inside
  `L₀`) as a unit of `L₀`, `residue_norm_eq_residue_pow_ramificationIdx_of_isTotallyRamified`
  applies with the trivial witness `x - algebraMap r₀ = 0 ∈ 𝔪_L`, giving
  `residue (N x) = (residue r₀) ^ e = s ^ e`.

Neither direction needs `𝓀[L] = 𝓀[K]` as an isomorphism, nor `IsTamelyRamified` — matching the
repo's established avoidance of building an `Algebra 𝓀[K] 𝓀[L]` instance
(`IsTotallyRamified`'s docstring).

## Main results

* `IsDedekindDomain.HeightOneSpectrum.residueNormUnits`
* `IsDedekindDomain.HeightOneSpectrum.range_residueNormUnits_eq_of_isTotallyRamified`
-/

noncomputable section

open IsDedekindDomain IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]

omit [Algebra.IsIntegral R S] in
/-- **`residue ∘ N`, as a map on unit groups.** The composite `L₀ˣ → K₀ˣ → κˣ`: first the ring
norm `Algebra.norm K₀ : L₀ → K₀` (a `MonoidHom`, hence lands in units on units), then reduction
mod `𝔪_K`. -/
def residueNormUnits : (w.adicCompletionIntegers L)ˣ →* (ResidueField (v.adicCompletionIntegers K))ˣ :=
  (Units.map (residue (v.adicCompletionIntegers K)).toMonoidHom).comp
    (Units.map (Algebra.norm (v.adicCompletionIntegers K)))

omit [Algebra.IsIntegral R S] [Module.Finite K L]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
@[simp]
theorem residueNormUnits_apply (x : (w.adicCompletionIntegers L)ˣ) :
    (residueNormUnits K L v w x : ResidueField (v.adicCompletionIntegers K)) =
      residue (v.adicCompletionIntegers K)
        (Algebra.norm (v.adicCompletionIntegers K) (x : w.adicCompletionIntegers L)) := by
  show ((Units.map (residue (v.adicCompletionIntegers K)).toMonoidHom).comp
      (Units.map (Algebra.norm (v.adicCompletionIntegers K))) x :
      ResidueField (v.adicCompletionIntegers K)) = _
  rw [MonoidHom.comp_apply, Units.coe_map, Units.coe_map]
  rfl

omit [Algebra.IsIntegral R S] in
/-- **The level-`0` image is exactly the `e`-th powers of `κˣ`, unconditionally on tameness.**
The exact-range counterpart of
`Langlands.TotallyRamifiedNormResidue.residue_norm_eq_residue_pow_ramificationIdx_of_isTotallyRamified`,
which only gave the `⊆` half. -/
theorem range_residueNormUnits_eq_of_isTotallyRamified (h : IsTotallyRamified K L v w) :
    MonoidHom.range (residueNormUnits K L v w) =
      MonoidHom.range (powMonoidHom (v.asIdeal.ramificationIdx' w.asIdeal) :
        (ResidueField (v.adicCompletionIntegers K))ˣ →*
          (ResidueField (v.adicCompletionIntegers K))ˣ) := by
  have he0 : v.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨r, hr⟩ := h.exists_sub_algebraMap_mem_maximalIdeal (x : w.adicCompletionIntegers L)
    have hres := residue_norm_eq_residue_pow_ramificationIdx_of_isTotallyRamified K L v w h hr
    have hNxu : IsUnit (Algebra.norm (v.adicCompletionIntegers K)
        (x : w.adicCompletionIntegers L)) :=
      x.isUnit.map (Algebra.norm (v.adicCompletionIntegers K))
    have hNxne : residue (v.adicCompletionIntegers K)
        (Algebra.norm (v.adicCompletionIntegers K) (x : w.adicCompletionIntegers L)) ≠ 0 :=
      (hNxu.map (residue (v.adicCompletionIntegers K)).toMonoidHom).ne_zero
    have hrne : residue (v.adicCompletionIntegers K) r ≠ 0 := ne_zero_pow he0 (hres ▸ hNxne)
    refine ⟨(isUnit_iff_ne_zero.mpr hrne).unit, ?_⟩
    apply Units.ext
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, IsUnit.unit_spec,
      residueNormUnits_apply]
    exact hres.symm
  · rintro _ ⟨s, rfl⟩
    obtain ⟨r0, hr0⟩ := surjective_units_map_residue (A := v.adicCompletionIntegers K) s
    have hru : IsUnit (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
        (r0 : v.adicCompletionIntegers K)) :=
      r0.isUnit.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L))
    refine ⟨hru.unit, ?_⟩
    apply Units.ext
    have hx : (hru.unit : w.adicCompletionIntegers L) -
        algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
          (r0 : v.adicCompletionIntegers K) ∈ maximalIdeal (w.adicCompletionIntegers L) := by
      rw [hru.unit_spec, sub_self]; exact Submodule.zero_mem _
    have hres := residue_norm_eq_residue_pow_ramificationIdx_of_isTotallyRamified K L v w h hx
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, residueNormUnits_apply]
    rw [hres]
    congr 1
    have hcast := congrArg Units.val hr0
    simpa [Units.coe_map] using hcast

/-! ### The classical norm-group description and the index formula, at the `K₀ˣ` level -/

section ClassicalDescription

variable [Finite (ResidueField (w.adicCompletionIntegers L))]

omit [Algebra.IsIntegral R S] in
/-- **`N_{L/K}(U_L)`, literally, at the `K₀ˣ` level.** The ring norm `Algebra.norm K₀ : L₀ → K₀`
as a map on unit groups — the same construction `residueNormUnits` composes with `residue`, kept
separate here because the classical description below targets its range directly, before any
residue-field reduction. -/
def normUnitsK₀ : (w.adicCompletionIntegers L)ˣ →* (v.adicCompletionIntegers K)ˣ :=
  Units.map (Algebra.norm (v.adicCompletionIntegers K))

omit [Algebra.IsIntegral R S] [Finite (ResidueField (w.adicCompletionIntegers L))] in
/-- **The classical norm-group description, at the `K₀ˣ` level.** Under `IsTotallyRamified` and
`IsTamelyRamified`,

`N_{L/K}(U_L) = {u ∈ K₀ˣ : residue u ∈ (κˣ)^e}`,

phrased as `MonoidHom.range normUnitsK₀ = Subgroup.comap (Units.map (residue K₀).toMonoidHom)
(MonoidHom.range (powMonoidHom e))`.

Proof: write `φ := Units.map (residue K₀).toMonoidHom` and `N_L := range normUnitsK₀`.
`residueNormUnits = φ.comp normUnitsK₀`, so `MonoidHom.range_comp` turns
`range_residueNormUnits_eq_of_isTotallyRamified` into `N_L.map φ = range (powMonoidHom e)`.
Separately, `ker φ ≤ N_L`: `ker φ` is exactly the principal units (`u ≡ 1 (mod 𝔪_K)`), and
`Langlands.TotallyRamifiedNormSurjective.exists_isUnit_norm_eq_of_isTotallyRamified` — the *only*
place `IsTamelyRamified` is used in this theorem — makes every principal unit a norm.
`Subgroup.comap_map_eq_self` then gives `comap φ (N_L.map φ) = N_L`, i.e.
`comap φ (range (powMonoidHom e)) = N_L`. -/
theorem normUnitsK₀_range_eq_of_isTotallyRamified (h : IsTotallyRamified K L v w)
    (htame : IsTamelyRamified K L v w) :
    MonoidHom.range (normUnitsK₀ K L v w) =
      Subgroup.comap (Units.map (residue (v.adicCompletionIntegers K)).toMonoidHom)
        (MonoidHom.range (powMonoidHom (v.asIdeal.ramificationIdx' w.asIdeal) :
          (ResidueField (v.adicCompletionIntegers K))ˣ →*
            (ResidueField (v.adicCompletionIntegers K))ˣ)) := by
  set φ := Units.map (residue (v.adicCompletionIntegers K)).toMonoidHom with hφdef
  set NL := MonoidHom.range (normUnitsK₀ K L v w) with hNLdef
  have hmap : NL.map φ =
      MonoidHom.range (powMonoidHom (v.asIdeal.ramificationIdx' w.asIdeal) :
        (ResidueField (v.adicCompletionIntegers K))ˣ →*
          (ResidueField (v.adicCompletionIntegers K))ˣ) := by
    rw [hNLdef, ← MonoidHom.range_comp]
    exact range_residueNormUnits_eq_of_isTotallyRamified K L v w h
  have hker : φ.ker ≤ NL := by
    intro u hu
    have hu1 : φ u = 1 := MonoidHom.mem_ker.mp hu
    have hcast : residue (v.adicCompletionIntegers K) (u : v.adicCompletionIntegers K) = 1 := by
      have hu1' := congrArg Units.val hu1
      simpa [hφdef, Units.coe_map] using hu1'
    have heq1 : residue (v.adicCompletionIntegers K) (u : v.adicCompletionIntegers K) =
        residue (v.adicCompletionIntegers K) (1 : v.adicCompletionIntegers K) := by
      rw [hcast, map_one]
    have hy : (u : v.adicCompletionIntegers K) - 1 ∈ maximalIdeal (v.adicCompletionIntegers K) :=
      (Ideal.Quotient.eq).mp heq1
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
    obtain ⟨x, hx, hxy⟩ := exists_isUnit_norm_eq_of_isTotallyRamified K L v w h htame hπ hy
    refine ⟨hx.unit, ?_⟩
    apply Units.ext
    show (Units.map (Algebra.norm (v.adicCompletionIntegers K)) hx.unit :
        v.adicCompletionIntegers K) = (u : v.adicCompletionIntegers K)
    rw [Units.coe_map, hx.unit_spec, hxy]
  rw [hNLdef] at hker ⊢
  rw [← hmap]
  exact (Subgroup.comap_map_eq_self hker).symm

omit [Algebra.IsIntegral R S] [Module.Finite K L]
  [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)] in
include L w in
/-- `𝓀[K]` is finite, given `𝓀[L]` is: it injects into it via the (functorial) `algebraMap`. -/
theorem finite_residueField_base : Finite (ResidueField (v.adicCompletionIntegers K)) :=
  Finite.of_injective
    (algebraMap (ResidueField (v.adicCompletionIntegers K))
      (ResidueField (w.adicCompletionIntegers L)))
    (algebraMap (ResidueField (v.adicCompletionIntegers K))
      (ResidueField (w.adicCompletionIntegers L))).injective

omit [Algebra.IsIntegral R S] [Finite (ResidueField (w.adicCompletionIntegers L))] in
/-- **The level-`1` principal units, together with the norm group, already exhaust `K₀ˣ` —
whenever the ramification index is coprime to `#κ_{K₀}ˣ`, with NO tameness hypothesis.**

`N_{L/K}(L₀ˣ) ⊔ U_{K₀}^{(1)} = ⊤`, i.e. `MonoidHom.range (normUnitsK₀ K L v w) ⊔
ValuationSubring.principalUnitsPow (v.adicCompletionIntegers K) 1 = ⊤`.

Route: `residueNormUnits = φ.comp (normUnitsK₀ K L v w)` for `φ := Units.map (residue K₀).toMonoidHom`,
so `range_residueNormUnits_eq_of_isTotallyRamified` (no tameness) gives `Subgroup.map φ
(range (normUnitsK₀ K L v w)) = range (powMonoidHom e)`. When `e` is coprime to `#κ_{K₀}ˣ`, the
`e`-th-power map on the finite cyclic group `κ_{K₀}ˣ` is surjective
(`IsCyclic.index_powMonoidHom_range` gives index `gcd(e, #κ_{K₀}ˣ) = 1`), so this is `⊤`. Then
`Subgroup.comap_map_eq` (general, no surjectivity needed) turns `comap φ ⊤ = range (normUnitsK₀) ⊔
ker φ` into `⊤ = range (normUnitsK₀) ⊔ ker φ`, and `ker φ = U_{K₀}^{(1)}` by `principalUnitsPow_one`.

This is the ring-level analogue of `TotallyRamifiedNormIndex.sup_units_eq_top`, reached by a
completely different route (residue-level surjectivity of the norm rather than the uniformizer
decomposition), and — unlike that lemma — genuinely restricted to instances where the coprimality
holds; nothing here claims it in general. -/
theorem sup_normUnitsK₀_principalUnitsPow_one_eq_top_of_isTotallyRamified
    (h : IsTotallyRamified K L v w) [Finite (ResidueField (v.adicCompletionIntegers K))]
    (hcop : Nat.Coprime (v.asIdeal.ramificationIdx' w.asIdeal)
        (Nat.card (ResidueField (v.adicCompletionIntegers K))ˣ)) :
    MonoidHom.range (normUnitsK₀ K L v w) ⊔
        ValuationSubring.principalUnitsPow (v.adicCompletionIntegers K) 1 = ⊤ := by
  haveI hfinKu : Finite (ResidueField (v.adicCompletionIntegers K))ˣ :=
    Finite.of_injective Units.val Units.val_injective
  have hmap : Subgroup.map (Units.map (residue (v.adicCompletionIntegers K)).toMonoidHom)
      (MonoidHom.range (normUnitsK₀ K L v w)) =
      MonoidHom.range (powMonoidHom (v.asIdeal.ramificationIdx' w.asIdeal) :
        (ResidueField (v.adicCompletionIntegers K))ˣ →*
          (ResidueField (v.adicCompletionIntegers K))ˣ) := by
    rw [← MonoidHom.range_comp]
    exact range_residueNormUnits_eq_of_isTotallyRamified K L v w h
  have hidx1 : (MonoidHom.range (powMonoidHom (v.asIdeal.ramificationIdx' w.asIdeal) :
      (ResidueField (v.adicCompletionIntegers K))ˣ →*
        (ResidueField (v.adicCompletionIntegers K))ˣ)).index = 1 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_comm]
    exact hcop.gcd_eq_one
  have htop : MonoidHom.range (powMonoidHom (v.asIdeal.ramificationIdx' w.asIdeal) :
      (ResidueField (v.adicCompletionIntegers K))ˣ →*
        (ResidueField (v.adicCompletionIntegers K))ˣ) = ⊤ := Subgroup.index_eq_one.mp hidx1
  have hcomap := Subgroup.comap_map_eq (Units.map (residue (v.adicCompletionIntegers K)).toMonoidHom)
    (MonoidHom.range (normUnitsK₀ K L v w))
  rw [hmap, htop, Subgroup.comap_top, ← ValuationSubring.principalUnitsPow_one] at hcomap
  exact hcomap.symm

omit [Algebra.IsIntegral R S] in
/-- **The index formula, at the `K₀ˣ` level.** Under `IsTotallyRamified` and `IsTamelyRamified`,
`[K₀ˣ : N_{L/K}(U_L)] = gcd(e, #κˣ)` — the classical index computation for the finite cyclic group
`κˣ`, transported across the norm-group description via `Subgroup.index_comap_of_surjective`
(`φ` is surjective, `Langlands.UnitGroupModPrincipalUnitsSurjective.surjective_units_map_residue`)
and `IsCyclic.index_powMonoidHom_range` (the `e`-th-power image in a finite cyclic group has index
`gcd(e, |group|)`). -/
theorem index_normUnitsK₀_range_eq_of_isTotallyRamified (h : IsTotallyRamified K L v w)
    (htame : IsTamelyRamified K L v w) :
    (MonoidHom.range (normUnitsK₀ K L v w)).index =
      Nat.gcd (v.asIdeal.ramificationIdx' w.asIdeal)
        (Nat.card (ResidueField (v.adicCompletionIntegers K))ˣ) := by
  haveI hfinK : Finite (ResidueField (v.adicCompletionIntegers K)) :=
    finite_residueField_base K L v w
  haveI hfinKu : Finite (ResidueField (v.adicCompletionIntegers K))ˣ :=
    Finite.of_injective Units.val Units.val_injective
  rw [normUnitsK₀_range_eq_of_isTotallyRamified K L v w h htame,
    Subgroup.index_comap_of_surjective
      (H := MonoidHom.range (powMonoidHom (v.asIdeal.ramificationIdx' w.asIdeal) :
        (ResidueField (v.adicCompletionIntegers K))ˣ →*
          (ResidueField (v.adicCompletionIntegers K))ˣ))
      (surjective_units_map_residue (A := v.adicCompletionIntegers K)),
    IsCyclic.index_powMonoidHom_range, Nat.gcd_comm]

end ClassicalDescription

end IsDedekindDomain.HeightOneSpectrum

end
