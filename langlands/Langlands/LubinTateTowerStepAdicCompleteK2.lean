/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepBaseNorm
import Langlands.LubinTateTowerStepLocalRing
import Langlands.MonogenicIntegralClosure
import Langlands.IntegralClosureTower

/-!
# `O_{K_2}` is `IsDomain`/`IsDiscreteValuationRing`/`(maximalIdeal)`-adically complete

`ROADMAP.md §60`/`§61` diagnosed `IsHausdorff`/`IsPrecomplete`/`IsAdicComplete` transport across the
two `O_{K_2}` spellings (`integralClosure O_{K_1} nextSplittingField` vs `integralClosure 𝒪[K] nextSplittingField`) as blocked on a
`rw`-motive failure, and recorded (via a loogle check that missed the right query) that no general
`RingEquiv`-indexed transport lemma existed in Mathlib for either class. `Langlands/
IntegralClosureTower.lean` corrects that: Mathlib already provides
`IsHausdorff.congr_ringEquiv`/`IsPrecomplete.congr_ringEquiv`/`IsAdicComplete.congr_ringEquiv`
(`Mathlib/RingTheory/AdicCompletion/Topology.lean`), and combining them with
`IsLocalRing.map_ringEquiv_maximalIdeal` closes `isAdicComplete_integralClosure_integralClosure`/
`isDiscreteValuationRing_integralClosure_integralClosure` there, generally, for any tower
`R ⊆ L ⊆ M`.

This file instantiates that general result at the concrete Lubin-Tate tower step
(`R := 𝒪[K]`, `L := K_1 P`, `M := nextSplittingField P₂`), establishing the base-relative facts
(`isDiscreteValuationRing_integralClosure`, `NormedField.isAdicComplete_integralClosure_of_
finiteDimensional`, both already general in `Langlands/MonogenicIntegralClosure.lean`/`Langlands/
LubinTateTowerStepConcrete.lean`) and transporting them to the `O_{K_1}`-relative spelling
`O_{K_2} := integralClosure O_{K_1} (nextSplittingField P₂)` that `Langlands/LubinTateTowerStep.lean`'s `TowerStep`
section needs to run the *next* inductive step.

## A genuinely new, second-order obstruction found and resolved along the way: an elaboration diamond

Directly hand-writing the goal `IsAdicComplete (maximalIdeal A) A` for the *doubly*-nested type
`A := ↥(integralClosure (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring L)) M)` as a
**fresh** declaration (a `theorem`'s stated type, an `example`, or a `#synth`/`inferInstanceAs`
query) fails with "Application type mismatch" — reproduced directly, five independent minimal
variants, all failing identically: Lean's own elaborator, when checking the *first* explicit argument
of `IsAdicComplete` (`maximalIdeal A`, whose type is `Ideal A` with a *specific*, concretely-resolved
`CommSemiring A` instance already baked in), does not accept it against the still-unresolved
`Ideal ?m (CommSemiring.toSemiring ?m CommRing.toCommSemiring)` expected type generated for
`IsAdicComplete`'s own implicit ring parameter — even though the two are almost certainly *defeq*
(same underlying `CommRing`/`ValuationSubring`/`Subalgebra` data), the elaborator refuses the
application without unfolding that deeply. This does **not** happen for the single-nested `O_{K_1}`
type (`isAdicComplete_integralClosure_K_1`, `Langlands/LubinTateTowerStepConcrete.lean`, closes
cleanly), nor for the doubly-nested type with a fully abstract base ring `R` (`Langlands/
IntegralClosureTower.lean`'s own `isAdicComplete_integralClosure_integralClosure` instance, general
`[CommRing R]`, closes cleanly) — it is specific to the *concrete* base `R :=
↥(ValuativeRel.valuation K).valuationSubring` composed through **two** `integralClosure` layers.

**Confirmed not a real mathematical obstruction, only an elaboration one**: applying the already
fully-elaborated general instance/theorem (`isAdicComplete_integralClosure_integralClosure`, or a
downstream generic theorem parametrized by an abstract `O'` such as `Langlands/
LubinTateTowerStep.lean`'s `TowerStep` section) *at* the concrete doubly-nested type — by ordinary
function application / instance-argument resolution, substituting into an already-closed type rather
than independently re-elaborating a freshly hand-written goal — succeeds without issue (checked
directly: `#check @isAdicComplete_integralClosure_integralClosure R L M _ _ _ _ _ _ _ _ _` at the
concrete `R`, and a generic `variable (O') [IsAdicComplete (maximalIdeal O') O']`-taking dummy
theorem applied at the concrete `O' := A`, both type-check cleanly). The practical upshot: this file
never states `IsAdicComplete`/`IsDiscreteValuationRing` as a hand-typed goal for `O_{K_2}` itself;
it only stages the needed base-spelling facts via `haveI` and lets ordinary instance search supply
`O_{K_2}`'s facts *at the point they are consumed* (e.g. inside `LubinTateTowerStep.lean`'s
`TowerStep` section, instantiated at `O' := O_{K_2}`), which is exactly the pattern under which the
diamond does not arise.

## What this file closes, and what remains for `K_3`

* `finiteDimensional_K_K_2` / `algebraIsSeparable_K_K_2` : `FiniteDimensional K (nextSplittingField P₂)` (tower law)
  and `Algebra.IsSeparable K (nextSplittingField P₂)` (given `[CharZero K]`), needed to instantiate the base-relative
  general theorems directly at `L := nextSplittingField P₂` (skipping the `K_1` hop), mirroring `K_2.hnorm_K`'s own
  two-hop pattern (`Langlands/LubinTateTowerStepBaseNorm.lean`).
* `isLocalHom_comp_towerHom_K_2` : the composite `ψ : O →+* O_{K_2}` (`O` → `O_{K_1}` →`O_{K_2}`,
  the moving-base structure map `Langlands/LubinTateTowerStep.lean`'s `TowerStep` section needs for
  the *next* step) is local, by `RingHom.isLocalHom_comp` chaining `isLocalHom_towerHom` and
  `isLocalHom_algebraMap_integralClosure_K_2`.

## A third obstacle, found while trying to actually apply the transport at `O_{K_2}`: a missing `Algebra`/`IsScalarTower` instance

Beyond the elaboration diamond above, actually *invoking*
`isDiscreteValuationRing_integralClosure_integralClosure`/`isAdicComplete_integralClosure_
integralClosure` at `R := ↥(ValuativeRel.valuation K).valuationSubring`, `L := K_1 P`,
`M := nextSplittingField P₂` needs `[Algebra R M]` and `[IsScalarTower R L M]` — i.e. `Algebra ↥(ValuativeRel.
valuation K).valuationSubring (nextSplittingField P₂)` and its compatibility with the existing `Algebra R (K_1 P)`/
`Algebra (K_1 P) (nextSplittingField P₂)` instances. **This instance does not exist in this repo.** `Langlands/
LubinTateTowerStepSplittingField.lean` builds exactly this three-hop composite, but only for the
*arc's base ring* `O` (`K_2.instAlgebraO`, given `hOK`) and for `K` itself (`K_2.instAlgebraK`,
`Langlands/LubinTateTowerStepBaseNorm.lean`) — neither is `R := ↥(ValuativeRel.valuation
K).valuationSubring` (`𝒪[K]`, the ring of integers of `K` itself, distinct from the arc's abstract
`O`, which relates to `K` only through `hOK`/`towerHom`). Building `𝒪[K]`'s own three-hop composite
`Algebra 𝒪[K] (nextSplittingField P₂)` — mirroring `K_2.instAlgebraO`/`K_2.instAlgebraK` one more time — is new,
straightforward-looking but unbuilt plumbing; checked directly (`grep`, no hits for `Algebra
↥(ValuativeRel.valuation K).valuationSubring (nextSplittingField` anywhere in this repo), not attempted here given
this pass's remaining scope.

## What this file closes, and what remains for `K_3`

Closed, general, `sorry`-free: `isScalarTower_K_K_1_K_2`, `finiteDimensional_K_K_2`,
`algebraIsSeparable_K_K_2`, `isLocalHom_comp_towerHom_K_2` (see doc comments above each). These are
real, useful pieces of the `K_2 → K_3` step's supporting infrastructure, and the diamond diagnosis
above is a genuine, load-bearing finding for anyone attempting to apply `Langlands/
IntegralClosureTower.lean`'s transport lemma at a concrete instantiation.

**Not closed here**: an end-to-end `IsDomain`/`IsDiscreteValuationRing`/`IsAdicComplete` witness for
`O_{K_2}` usable by `Langlands/LubinTateTowerStep.lean`'s `TowerStep` section, blocked on the missing
`Algebra`/`IsScalarTower` instance above (not the transport lemma itself, which is genuinely general
and does close in the abstract — verified directly by application, see above). **Also not attempted**:
constructing an irreducible/uniformizer element of `O_{K_2}` itself (the `α'` input
`LubinTateTowerStep.exists_isWeierstrassFactorization_shifted`/`isEisensteinAt_shifted` need to
actually produce `K_3`'s Eisenstein polynomial). At the `K_1` level this needed
`natDegree_minpoly_eq_finrank_K_1`/`norm_eq_spectralNorm_pow_natDegree_K_1`/
`exists_irreducible_uniformizer_K_1` (`Langlands/LubinTateSplittingFieldDVR.lean`/`Langlands/
LubinTateTowerStepConcrete.lean`) — a genuine ramification-degree computation, not a corollary of
`IsAdicComplete`/`IsDiscreteValuationRing`. The `nextSplittingField`-level analogue of that machinery does not exist
in this repo and is **not** built here: checked directly (`grep`, no hits for any
`natDegree_minpoly_eq_finrank_K_2`/`norm_eq_spectralNorm_pow_natDegree_K_2`/
`exists_irreducible_uniformizer_K_2`-shaped declaration). Both remaining gaps are new content
comparable in scope to the several existing files that build their `K_1`-level analogues, **not**
corollaries of the `IsAdicComplete`/`IsDiscreteValuationRing` transport this pass closes — contrary
to `ROADMAP.md §60`'s forecast that "no new mathematics [is] identified as needed beyond that one
transport". `K_3`'s Eisenstein polynomial is therefore still not produced; see `ROADMAP.md` for the
precise handoff.
-/

@[expose] public section

noncomputable section

open scoped Polynomial IntermediateField
open IsLocalRing Polynomial PowerSeries

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]
variable {P : O[X]} (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X])

/-- **`IsScalarTower K (K_1 P) (nextSplittingField P₂)`** for the two-hop composite algebra
`K_2.instAlgebraK`. -/
theorem isScalarTower_K_K_1_K_2 :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    IsScalarTower K (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂) := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact congrFun (K_2.algebraMap_K_eq (K := K) (P := P) P₂) x

/-- **`FiniteDimensional K (nextSplittingField P₂)`**, via the tower law (`Module.Finite.trans`) applied to
`K_1.instFiniteDimensional` and `nextSplittingField.instFiniteDimensional`, using `isScalarTower_K_K_1_K_2`. -/
theorem finiteDimensional_K_K_2 :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    FiniteDimensional K (nextSplittingField (K' := K_1 (K := K) P) P₂) := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  haveI := isScalarTower_K_K_1_K_2 (K := K) (P := P) P₂
  exact Module.Finite.trans (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂)

/-- **`Algebra.IsSeparable K (nextSplittingField P₂)`**, given `[CharZero K]`. `nextSplittingField P₂ / K` is finite
(`finiteDimensional_K_K_2`), hence integral; every integral extension of a `CharZero` field is
separable (`Algebra.IsSeparable.of_integral`) — the same shortcut the generic `Level.algebraIsSeparable`
(`Langlands/LubinTateTowerStepLevelExists.lean`) uses one hop down, at `K_1 P` instead of `K`. -/
theorem algebraIsSeparable_K_K_2 [CharZero K] :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    Algebra.IsSeparable K (nextSplittingField (K' := K_1 (K := K) P) P₂) := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  haveI := finiteDimensional_K_K_2 (K := K) (P := P) P₂
  haveI : Algebra.IsIntegral K (nextSplittingField (K' := K_1 (K := K) P) P₂) := Algebra.IsIntegral.of_finite _ _
  exact Algebra.IsSeparable.of_integral K (nextSplittingField (K' := K_1 (K := K) P) P₂)

/-- **The composite `ψ : O →+* O_{K_2}`** (`O → O_{K_1} → O_{K_2}`) is local. The moving-base
structure map `Langlands/LubinTateTowerStep.lean`'s `TowerStep` section needs for the *next*
inductive step, built from `isLocalHom_towerHom` (`O → O_{K_1}`) and
`isLocalHom_algebraMap_integralClosure_K_2` (`O_{K_1} → O_{K_2}`) via `RingHom.isLocalHom_comp`. -/
theorem isLocalHom_comp_towerHom_K_2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' = (P₂ : _⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (nextSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    (hirr : Irreducible (P₂.map (algebraMap _ (K_1 (K := K) P))))
    {β : nextSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O)
    [Algebra.IsSeparable (K_1 (K := K) P) (nextSplittingField (K' := K_1 (K := K) P) P₂)] :
    IsLocalHom ((algebraMap
      ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
      ↥(integralClosure
        ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
        (nextSplittingField (K' := K_1 (K := K) P) P₂))).comp (towerHom (K := K) hOK P)) := by
  haveI := isLocalHom_towerHom (K := K) hOK hπ hπnorm P
  haveI := isLocalHom_algebraMap_integralClosure_K_2 hOK hπ hπnorm hf hu heq hPdist hPdeg hu₂ heq₂
    hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hirr hβroot hβfin
  exact RingHom.isLocalHom_comp _ _

end LubinTate
