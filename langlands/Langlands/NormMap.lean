import Langlands.IdeleGroup
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Norm.Defs

/-!
# Local pieces of the idèle norm map

This file assembles the infrastructure the idèle norm map `NumberField.IdeleGroup.normMap`
(`Langlands/IdeleGroup.lean`) needs, filling in the three gaps identified in the survey there:

1. The place-lying-over relation between `HeightOneSpectrum R` and `HeightOneSpectrum S` for a
   ring extension `R → S`: this turns out to already be present in Mathlib, just not under the
   name the previous survey looked for. `IsDedekindDomain.HeightOneSpectrum.under` (in
   `Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas`) restricts a height-one prime `w` of `S` to
   one of `R` (given `Algebra.IsIntegral R S`), and the "lying over" relation itself is
   `w.asIdeal.LiesOver v.asIdeal` (from `Mathlib.RingTheory.Ideal.Over`, applied to the
   underlying ideals) -- indeed `Mathlib.NumberTheory.RamificationInertia.Valuation` already
   states its results in terms of exactly this relation, e.g.
   `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`. `finite_liesOver` below packages the
   finiteness of the set of places lying over a given `v`, via `IsDedekindDomain.primesOver_finite`.
2. Local norm maps between completions of different fields: Mathlib does have (as of a 2026
   addition, `Mathlib.NumberTheory.RamificationInertia.Valuation`) the uniform continuity of
   `algebraMap K L` between the *valued fields* `WithVal (v.valuation K)` and
   `WithVal (w.valuation L)` for `w` lying over `v`
   (`IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver`). Composed with
   `UniformSpace.Completion.mapRingHom` and the identification of `adicCompletion` with the
   completion of the valued field (`adicCompletion.equiv`), this gives an honest ring hom
   `v.adicCompletion K →+* w.adicCompletion L` (`adicCompletionComap` below) -- not a `sorry`.
   The local norm map itself (`localNormMap`) is then `Units.map (Algebra.norm _)` for the
   `Algebra` structure this ring hom induces; also not a `sorry`, though its good behavior
   (matching the classical local norm, being trivial off a finite set of places, etc.) is not
   proved here.
3. A ring hom `AdeleRing S L →+* AdeleRing R K` induced by a finite extension: still missing.
   Assembling the local norms of (2) into a global map on the finite adèles requires knowing the
   local norm map is a *local unit* (valuation `1`) whenever `a_w` is, at all but finitely many
   places -- i.e. that `adicCompletionComap`/`localNormMap` restricts well to
   `adicCompletionIntegers`. This "almost everywhere" implication is now proved unconditionally,
   as `eventually_localNormMap_mem_units` below, on top of one isolated per-place `sorry`
   (`localNormMap_mem_units`: the local norm of a *single* local unit is a local unit -- the
   standard fact that, for a finite extension of complete discretely-valued fields, the ring of
   integers of the top field is the integral closure of the ring of integers of the bottom field,
   which is not yet in Mathlib). Still missing beyond this: the archimedean/infinite-place half
   of the norm map, and the final assembly of both halves into a ring hom on the full adèle rings
   (via `RestrictedProduct.mkUnit` for the finite part, analogous to
   `IdeleGroup.exists_toFractionalIdeal_eq`). `IdeleGroup.normMap` therefore remains a `sorry`,
   though the specific gap identified in the task ("an almost-everywhere-unit idèle maps to an
   almost-everywhere-unit idèle") is now closed.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionComap` : the ring hom
  `v.adicCompletion K →+* w.adicCompletion L` induced by `algebraMap K L`, for `w` a place of `S`
  lying over `v`.
* `IsDedekindDomain.HeightOneSpectrum.localNormMap` : the local norm map on units,
  `(w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ`.
* `IsDedekindDomain.HeightOneSpectrum.finite_liesOver` : only finitely many places of `S` lie over
  a given place `v` of `R`.
* `IsDedekindDomain.HeightOneSpectrum.localNormMap_mem_units` : the local norm of a local unit is
  a local unit (`sorry`: needs uniqueness of the extension of a complete valuation).
* `IsDedekindDomain.HeightOneSpectrum.eventually_localNormMap_mem_units` : an idèle that is almost
  everywhere a local unit has local norms that are almost everywhere a local unit -- the "missing
  gap" for `IdeleGroup.normMap`, now proved (modulo the single `sorry` above).
-/

noncomputable section

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

section RankOne

open scoped WithZero NNReal

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F] (v : HeightOneSpectrum A)

/-- **Connecting instance**: the `v`-adic completion of the fraction field of a Dedekind domain
has a rank-one valuation. Mathlib already builds `Valuation.IsRankOneDiscrete` for
`(Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)` completely generally (for *any* Dedekind domain
`A` with fraction field `F`, not just `𝓞 K` for a number field `K`) in
`Mathlib.NumberTheory.NumberField.Completion.FinitePlace` -- it just lives under the
`NumberField` namespace because that is where it happens to have been added, even though its
statement never mentions `NumberField`. That instance is built via
`Valuation.IsRankOneDiscrete.mk'` applied to `v.valuation F`: cyclicity of the value group comes
from `Subgroup.isCyclic` (any subgroup of the cyclic group `ℤᵐ⁰ˣ` is cyclic), nontriviality from
`v.valuation F`'s surjectivity (`HeightOneSpectrum.valuation_surjective`).

What was missing is turning that `IsRankOneDiscrete` fact into an actual `Valuation.RankOne`
*instance* -- the `ℝ≥0`-embedded-value-group structure that `Valued.toNormedField`/`NormedField`
and this session's uniqueness-of-valuation-extension machinery (`Langlands.HenselianValuation`)
need as a hypothesis. `Valuation.IsRankOneDiscrete.rankOne` builds a `RankOne` instance from *any*
real `e > 1`, with no further hypotheses: it does not need the residue field `A ⧸ v.asIdeal` to be
finite (contrast `NumberField.instRankOneAdicCompletion`, which specifically uses
`e = absNorm v.asIdeal` so the resulting norm matches the classical adic absolute value -- a
choice only available when `Module.Finite ℤ A`/`Module.Free ℤ A`, i.e. essentially when `A = 𝓞 K`).
For a bare Dedekind domain with no such finiteness assumption, any fixed `e` (here `e := 2`)
suffices to get an unconditional `RankOne` instance.

This alone does not close `IsDedekindDomain.HeightOneSpectrum.localNormMap_mem_units` below: the
remaining gap there is uniqueness of the extension of a *complete* discrete valuation to a finite
extension of `v.adicCompletion A`, which additionally needs the completion to be algebraic over
its base (not just rank-one) -- a separate blocker, not attempted here. -/
noncomputable instance instRankOneValuedAdicCompletion :
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (by norm_num : (1 : ℝ≥0) < 2)

end RankOne

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

/-- The ring hom `v.adicCompletion K →+* w.adicCompletion L` induced by `algebraMap K L`, for a
place `w` of `S` lying over a place `v` of `R`. Built by extending the uniformly continuous map
`algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))`
(`uniformContinuous_algebraMap_liesOver`) to the completions, then transporting along the
identification of `adicCompletion` with the completion of the valued field
(`adicCompletion.equiv`). -/
def adicCompletionComap : v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
        (uniformContinuous_algebraMap_liesOver K L v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom)

/-- The `w.adicCompletion L` obtained from `v.adicCompletion K` via `adicCompletionComap`, for a
place `w` of `S` lying over a place `v` of `R`. -/
instance : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (adicCompletionComap K L v w).toAlgebra

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- `adicCompletionComap` is continuous: it is built by composing the (unconditionally
continuous) `UniformSpace.Completion.map` of a uniformly continuous map with the two
homeomorphisms `adicCompletion.equiv`, whose continuity in each direction is
`adicCompletion.continuous_toCompletion` / `adicCompletion.continuous_ofCompletion`. -/
theorem continuous_adicCompletionComap : Continuous (adicCompletionComap K L v w) :=
  (adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v)

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- `adicCompletionComap` agrees, on the image of `K`, with `algebraMap K (w.adicCompletion L)`
composed through `algebraMap K L`. This is the compatibility fact needed for
`IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)`. -/
theorem adicCompletionComap_algebraMap (x : K) :
    adicCompletionComap K L v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  apply (adicCompletion.equiv L w).injective
  simp only [adicCompletionComap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, adicCompletion.equiv_apply,
    algebraMap_adicCompletion_toCompletion, UniformSpace.Completion.algebraMap_def,
    UniformSpace.Completion.coe_mapRingHom,
    UniformSpace.Completion.map_coe (uniformContinuous_algebraMap_liesOver K L v w)]
  exact congrArg _ <|
    (IsScalarTower.algebraMap_apply K (WithVal (v.valuation K)) (WithVal (w.valuation L)) x).symm.trans
      (IsScalarTower.algebraMap_apply K L (WithVal (w.valuation L)) x)

/-- The scalar tower `K → v.adicCompletion K → w.adicCompletion L`, for a place `w` of `S` lying
over a place `v` of `R`. Needed (together with `instContinuousSMulAdicCompletionAdicCompletion`
below) to instantiate Mathlib's `NumberField.HeightOneSpectrum.instModuleFiniteAdicCompletion`-style
finiteness argument in the general Dedekind-domain setting. -/
instance : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x => (adicCompletionComap_algebraMap K L v w x).symm

/-- `v.adicCompletion K` acts continuously on `w.adicCompletion L`, via `adicCompletionComap`. -/
instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) where
  continuous_smul :=
    (continuous_adicCompletionComap K L v w).comp continuous_fst |>.mul continuous_snd

open scoped TensorProduct Valued in
/-- **`w.adicCompletion L` is a finite `v.adicCompletion K`-module.** Mathlib already proves this
(`NumberField.HeightOneSpectrum.instModuleFiniteAdicCompletion` in
`Mathlib.NumberTheory.NumberField.Completion.FinitePlace`), but only under `[NumberField K]
[NumberField L]` hypotheses -- even though the proof itself only uses `Module.Finite K L`
(to get `Kv ⊗[K] L` finite-dimensional over `Kv`) together with the `Algebra`/`ContinuousSMul`/
`IsScalarTower` instances just built above, none of which need `K`/`L` to be number fields. The
proof is otherwise identical: `Φ : Kv ⊗[K] L →ₗ[Kv] Lw` (the multiplication map) has closed,
hence (being finite-dimensional) all of, `Lw` as its range, since its range is dense
(`w.denseRange_algebraMap L`, itself fully general for any Dedekind domain). -/
instance : Module.Finite (v.adicCompletion K) (w.adicCompletion L) :=
  let Φ : v.adicCompletion K ⊗[K] L →ₗ[v.adicCompletion K] w.adicCompletion L :=
    Algebra.TensorProduct.lift (Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
      (w.adicCompletion L)) (Algebra.algHom K L (w.adicCompletion L))
      (fun _ _ => mul_comm ..) |>.toLinearMap
  have h_dense : DenseRange Φ := by
    apply (w.denseRange_algebraMap L).mono
    rintro _ ⟨l, rfl⟩
    exact ⟨1 ⊗ₜ l, by simp [Φ, Algebra.algHom]⟩
  .of_surjective Φ (by
    rw [← Set.range_eq_univ, ← Φ.coe_range, ← Φ.range.closed_of_finiteDimensional.closure_eq]
    exact h_dense.closure_range)

/-- **Algebraicity of `w.adicCompletion L` over `v.adicCompletion K`.** The missing ingredient
`LocalField.valuationSubring_eq_of_comap_eq` (`Langlands.HenselianValuation`) needs to apply
uniqueness-of-valuation-extension to `w.adicCompletion L / v.adicCompletion K`: finite extensions
are algebraic. -/
instance : Algebra.IsAlgebraic (v.adicCompletion K) (w.adicCompletion L) :=
  .of_finite _ _

/-- The local norm map `N_{L_w/K_v} : (w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ`, for a place
`w` of `S` lying over a place `v` of `R`: the norm of the finite (as `L / K` is finite, hence so is
`L_w / K_v`, though this finiteness is not needed for the definition itself) extension
`w.adicCompletion L` of `v.adicCompletion K`, transported to units via `Units.map`. This is the
local factor of the idèle norm map `N_{L/K} a = (∏_{w ∣ v} N_{L_w/K_v}(a_w))_v`. -/
def localNormMap : (w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (Algebra.norm (v.adicCompletion K) : w.adicCompletion L →* v.adicCompletion K)

/-- Only finitely many places `w` of `S` lie over a given place `v` of `R`: the set
`{w // w.asIdeal.LiesOver v.asIdeal}` injects into `v.asIdeal.primesOver S`
(via `w ↦ w.asIdeal`), which is finite since `v.asIdeal` is a nonzero (hence maximal, by
`IsDedekindDomain.HeightOneSpectrum.isMaximal`) ideal of the Dedekind domain `R` and `S / R` is
integral (`IsDedekindDomain.primesOver_finite`). -/
theorem finite_liesOver (v : HeightOneSpectrum R) :
    {w : HeightOneSpectrum S | w.asIdeal.LiesOver v.asIdeal}.Finite := by
  have hsub : (fun w : HeightOneSpectrum S => w.asIdeal) ''
      {w : HeightOneSpectrum S | w.asIdeal.LiesOver v.asIdeal} ⊆ v.asIdeal.primesOver S := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, hw⟩
  exact Set.Finite.of_finite_image
    (Set.Finite.subset (IsDedekindDomain.primesOver_finite v.asIdeal S) hsub)
    (HeightOneSpectrum.asIdeal_injective.injOn)

/-- **Key local fact.** The local norm map sends local units to local units: if `a` has
valuation `1` at `w` (i.e. `a ∈ w.adicCompletionIntegers L`, as a unit), its norm
`N_{L_w/K_v}(a)` has valuation `1` at `v`.

This is the standard fact from local field theory that, for a finite extension of *complete*
discretely-valued fields (`v.adicCompletion K` is complete, being defined as a
`UniformSpace.Completion`), the extension of `v` to `L_w` is unique, so
`w.adicCompletionIntegers L` is exactly the integral closure of `v.adicCompletionIntegers K` in
`w.adicCompletion L` (see e.g. Serre, *Local Fields*, Ch. II §2). Granting that, the proof
would combine `isIntegral_norm` (the norm of an integral element is integral,
`Mathlib.RingTheory.Norm.Transitivity`) with the fact that a `ValuationSubring` is integrally
closed (`Mathlib.RingTheory.Valuation.LocalSubring`), applied to `v.adicCompletionIntegers K`
(which is literally a `ValuationSubring` by definition).

The "integral closure = ring of integers" half of this needs
`LocalField.valuationSubring_eq_of_comap_eq` (`Langlands.HenselianValuation`), which requires
`Algebra.IsAlgebraic (v.adicCompletion K) (w.adicCompletion L)`. That algebraicity fact is now
available unconditionally for any finite extension `L / K` of fraction fields of Dedekind domains
(`instAlgebraIsAlgebraicAdicCompletionAdicCompletion` above, via the generalized
`Module.Finite (v.adicCompletion K) (w.adicCompletion L)` instance above it -- itself a
generalization, to arbitrary Dedekind domains, of Mathlib's
`NumberField.HeightOneSpectrum.instModuleFiniteAdicCompletion`, which is only stated for number
fields even though its proof never uses that). What remains is a *second*, separate gap:
`valuationSubring_eq_of_comap_eq` also needs `v.adicCompletion K` to carry a
`NontriviallyNormedField`/`IsUltrametricDist`/`ValuativeRel`/`Valuation.Compatible` bridge
compatible with its own `Valued` structure -- the same bridge
`valuationSubring_eq_of_comap_eq_of_isNonarchimedeanLocalField` builds, but only for `K` satisfying
`IsNonarchimedeanLocalField K`, not for a bare `v.adicCompletion K` of an arbitrary Dedekind
domain. Building that bridge generically (mirroring the RankOne/NontriviallyNormedField work done
for the algebraicity gap) is not yet attempted here. This is recorded as a `sorry` isolating
exactly that missing ingredient, so that the assembly argument below
(`eventually_localNormMap_mem_units`) can be proved unconditionally on top of it. -/
theorem localNormMap_mem_units {a : (w.adicCompletion L)ˣ}
    (ha : a ∈ (w.adicCompletionIntegers L).units) :
    localNormMap K L v w a ∈ (v.adicCompletionIntegers K).units := by
  sorry

/-- **Main assembly lemma**, and the key missing piece for `IdeleGroup.normMap`
(`Langlands/IdeleGroup.lean`): if a family `a : ∀ w, (w.adicCompletion L)ˣ` of local units at
places of `S` is almost everywhere (in the cofinite filter on `HeightOneSpectrum S`) a genuine
local unit -- the restricted-product condition defining a finite idèle of `L` -- then, for all
but finitely many places `v` of `R`, *every* place `w` lying over `v` has `a w` a local unit,
hence (via `localNormMap_mem_units`) its local norm `N_{L_w/K_v}(a w)` is a local unit at `v`.

The point is that finitely many "bad" places `w` of `S` can only lie over finitely many places
`v` of `R`: each `w` lies over a *unique* `v` (`w.asIdeal.LiesOver v.asIdeal` determines
`v = HeightOneSpectrum.under R w`, `Ideal.LiesOver.over`), so the bad `v`'s are exactly the
(finite) image of the bad `w`'s under `HeightOneSpectrum.under R`; away from that finite set,
every `w` lying over `v` is good. This is what lets the local norm maps be assembled into a
genuine finite idèle of `K` (once the local units are packaged via `RestrictedProduct.mkUnit`,
as in `IdeleGroup.exists_toFractionalIdeal_eq`). -/
theorem eventually_localNormMap_mem_units
    {a : ∀ w : HeightOneSpectrum S, (w.adicCompletion L)ˣ}
    (ha : ∀ᶠ w : HeightOneSpectrum S in Filter.cofinite,
      a w ∈ (w.adicCompletionIntegers L).units) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      ∀ w : HeightOneSpectrum S, ∀ _ : w.asIdeal.LiesOver v.asIdeal,
        localNormMap K L v w (a w) ∈ (v.adicCompletionIntegers K).units := by
  rw [Filter.eventually_cofinite] at ha ⊢
  refine Set.Finite.subset (ha.image (HeightOneSpectrum.under R)) fun v hv => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨w, hw, hcontra⟩ := hv
  haveI := hw
  have hveq : v = HeightOneSpectrum.under R w := HeightOneSpectrum.ext hw.over
  exact ⟨w, mt (localNormMap_mem_units K L v w) hcontra, hveq.symm⟩

end IsDedekindDomain.HeightOneSpectrum

end
