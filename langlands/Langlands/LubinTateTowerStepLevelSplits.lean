/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLevelExists
import Langlands.LubinTateSplittingFieldTorsion

/-!
# The `Algebra O lvl.L` self-composite, and the `Splits` invariant, generic in `Level` (`ROADMAP.md`
§84)

`§83` closed the existence half of the inductive tower step and named the precise remaining
obstacle for the degree/splitting chain (`[K_{n+1}:K_n] = residueCard O`,
`residueFieldEquiv_K_n`): stating `(P.divX.map (algebraMap O lvl.L)).Splits` at all needs an
`Algebra O lvl.L` composite that `Level`/`TowerStep` did not carry, and the `Splits` fact itself is
genuine level-indexed induction data (free at the base from `K_1`'s own construction, and
propagated to every later level by `Polynomial.Splits.map`), not a corollary of anything `Level`
already holds. This file supplies both.

## The self-composite, and why it is safe to build generically (unlike `Level.OL` itself)

`Level.instAlgebraOSelf` is the two-hop `O → K → lvl.L` composite — the same shape as
`K_1.instAlgebraO` (`Langlands/LubinTateSplittingField.lean`), generalized to an arbitrary `lvl.L`
via `lvl.algL`. It needs no `hOK` at all (unlike `Level.instAlgebraO`, the *next*-level composite,
which routes through `lvl.OL` and hence needs `hOK` to build `Level.towerHom`): `Algebra K lvl.L`
(`lvl.algL`) and `Algebra O K` (ambient) compose directly, with no `Algebra.ofSubsemiring` search
anywhere in the construction. This is exactly the distinction `§78` drew for
`instAlgebraK_of_algebraL`: genericity over an abstract intermediate type costs nothing when the
construction is a plain `RingHom.comp`, and only becomes expensive when a subring/subalgebra
membership search (`Algebra.ofSubsemiring`) is involved — which this composite never invokes.

`Level.instAlgebraOSelf`, instantiated at `level_K_1`, is **`K_1.instAlgebraO` on the nose (`rfl`)**:
both unfold to the identical `((algebraMap K (K_1 P)).comp (algebraMap O K)).toAlgebra` term, since
`level_K_1.algL := K_1.instAlgebra` (`§80`). No new proof is needed for the base case; it is a
definitional coincidence, not a theorem.

## The composite identity one level up

`Level.algebraMap_OSelf_next_eq` proves `algebraMap O (lvl.next Pn).L` (via the *next* level's own
self-composite) agrees, as a `RingHom`, with `algebraMap O (nextSplittingField (K' := lvl.L) Pn)` (via
`lvl.instAlgebraO Pn hOK`, `§82`'s *next*-level-from-`lvl` composite) — the generalization of
`algebraMap_O_K_1_eq_comp_towerHom`/`K_2.algebraMap_O_eq_comp_K_1`
(`Langlands/LubinTateTowerStepRootConnect.lean`). Built entirely from two already-proved pieces, no
new elaboration-cost investigation needed: `(lvl.next Pn).algebraMap_OSelf_eq` (this file, `rfl`) and
`algebraMap_K_eq_of_Level`/`Level.algebraMap_O_eq_comp_L` (`§81`/`§83`, already committed). This
sidesteps entirely the diamond risk a naive proof via `IsScalarTower lvl.OL lvl.L (nextSplittingField (K' :=
lvl.L) Pn)` would run into: that instance is not registered anywhere for an abstract `lvl` (the
`nextSplittingField` combinator's own `[Algebra O' K']` hypothesis, instantiated at `O' := lvl.OL`, would need to
be found by the same `Algebra.ofSubsemiring`-style search `§73`/`§79` already documented as
expensive/diamond-prone against an abstract ambient level); this proof never needs that instance,
only raw function composition through already-known composite facts.

## The `Splits` transport

`Level.splits_next` transports `(Q.map (algebraMap O lvl.L)).Splits` (self-composite) to
`(Q.map (algebraMap O (nextSplittingField (K' := lvl.L) Pn))).Splits` (next-level composite), by
`Polynomial.Splits.map` plus `Polynomial.map_map` plus the composite identity above — the direct
generalization of `splits_divX_map_K2P2` (`§75`), whose own proof used exactly this shape one level
down (`(splits_divX_map_K_1 P).map … ` then `Polynomial.map_map` then `K_2.algebraMap_O_eq_comp_K_1`).
`§75` already established that the mathematical content here is free once stated correctly
("splitting propagates up the tower... the only per-level work is bookkeeping the algebra-map
composites") — this file makes that bookkeeping itself generic in `lvl`, rather than redone by hand
at every new depth.

## Checked against both concrete depths

* **Base case, `rfl`**: `level_K_1.instAlgebraOSelf = K_1.instAlgebraO`.
* **`K_1 → K_2`, by application**: `Level.splits_next (level_K_1) P₂ hOK (splits_divX_map_K_1 P)`
  has exactly `splits_divX_map_K2P2`'s type — checked directly by `example`, not merely claimed to
  "specialize" (it typechecks *as* that statement, using the base-case `rfl` above to bridge the
  two `Algebra O (K_1 P)` instances).
* **`K_2 → K_3`, instantiation not recovery** (`§83`'s own discipline: there is no pre-existing
  `splits_divX_map_K3P3`/similar in this repo to compare against, checked by `grep` before writing):
  the same generic step, run twice (`level_K_1 → level_K_2 → (level_K_2).next P₃`), types against
  `K_3.instAlgebraO`'s real four-hop composite and produces `(P.divX.map (algebraMap O (K_3 P₃))).
  Splits` — the first time this arc has this fact at that depth.

## What this does not close

**Not attempted**: propagating `Splits`/`Level.instAlgebraOSelf` into `piTorsion`-invariance
(`piTorsion_one_K_2_eq_algebraMap_image`/`_K_3_eq_algebraMap_image`'s generic form),
`adjoin_root_eq_top`, or the degree computation (`hgen`, `finrank_..._eq_residueCard`) themselves.
Those need, beyond what is built here: a generic `Level`-level `FaithfulSMul O lvl.L`/injectivity
fact (the `K_2.instFaithfulSMul_O`/`K_3.instFaithfulSMul_O` analogue, itself needing `[FaithfulSMul
O K]` composed through the self-composite — mechanical, but not built here), and — the genuinely
larger remaining piece — `FPiEval_algebraMap_mem_adjoin`'s generic form, which is not bookkeeping: it
is a `tsum`-lands-in-a-finite-dimensional-subspace analytic argument
(`Submodule.mem_of_hasSum_of_finiteDimensional`), currently written once per concrete level
(`Langlands/LubinTateTowerStepDegree.lean`/`LubinTateTowerStepK3Degree.lean`) and not yet
restated generically. `Level.exists_tower_step_next`'s `hgen` hypothesis (`§83`) therefore remains
an external hypothesis, unchanged by this file. See `ROADMAP.md §84` for the full account.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace LubinTate

open IsLocalRing PowerSeries Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]

/-- **`Algebra O lvl.L`, the self-composite**, `O → K → lvl.L`, built the same way as
`K_1.instAlgebraO`: composing the ambient `algebraMap O K` with `lvl.algL`'s own `algebraMap K
lvl.L`. Unlike `Level.instAlgebraO` (`§82`, the *next*-level composite), this needs no `hOK`: it
never routes through `lvl.OL`/`Level.towerHom`, so it involves no `Algebra.ofSubsemiring` search —
safe to generalize over an abstract `lvl`, per the same distinction `§78` drew for
`instAlgebraK_of_algebraL`. -/
@[reducible] def Level.instAlgebraOSelf (lvl : Level K) : Algebra O lvl.L :=
  letI := lvl.algL
  ((algebraMap K lvl.L).comp (algebraMap O K)).toAlgebra

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [IsFractionRing O K] in
/-- `Level.instAlgebraOSelf`'s `algebraMap`, unfolded — true by `rfl`, its own definition. -/
theorem Level.algebraMap_OSelf_eq (lvl : Level K) :
    letI := lvl.algL
    letI := lvl.instAlgebraOSelf (O := O)
    (algebraMap O lvl.L : O →+* lvl.L) = (algebraMap K lvl.L).comp (algebraMap O K) := by
  letI := lvl.algL
  rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [IsFractionRing O K] in
/-- **Base case, `rfl`**: `level_K_1`'s self-instance is literally `K_1.instAlgebraO` — both unfold
to the same `O → K → K_1 P` composite, since `level_K_1.algL := K_1.instAlgebra`. -/
example (P : O[X]) :
    Level.instAlgebraOSelf (O := O) (level_K_1 (O := O) (K := K) (P := P)) =
      K_1.instAlgebraO (O := O) (K := K) (P := P) := rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [IsFractionRing O K] in
/-- **The composite through `lvl.instAlgebraO Pn hOK` (`§82`'s next-level composite) agrees with the
next level's own self-composite.** Generalizes `algebraMap_O_K_1_eq_comp_towerHom`/
`K_2.algebraMap_O_eq_comp_K_1` (`Langlands/LubinTateTowerStepRootConnect.lean`); built purely from
already-committed pieces (`Level.algebraMap_OSelf_eq`, `algebraMap_K_eq_of_Level` `§81`,
`Level.algebraMap_O_eq_comp_L` `§83`), never from an `IsScalarTower lvl.OL lvl.L (nextSplittingField (K' :=
lvl.L) Pn)` instance search — see the module docstring for why that route is avoided. -/
theorem Level.algebraMap_OSelf_next_eq (lvl : Level K) (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := lvl.algL
    letI := (lvl.next Pn).instAlgebraOSelf (O := O)
    letI := lvl.instAlgebraO Pn hOK
    (algebraMap O (lvl.next Pn).L : O →+* (lvl.next Pn).L) =
      algebraMap O (nextSplittingField (K' := lvl.L) Pn) := by
  letI := lvl.algL
  letI := (lvl.next Pn).instAlgebraOSelf (O := O)
  letI := lvl.instAlgebraO Pn hOK
  letI := (lvl.next Pn).algL
  have h1 := (lvl.next Pn).algebraMap_OSelf_eq (O := O)
  apply RingHom.ext
  intro c
  show algebraMap O (lvl.next Pn).L c = algebraMap O (nextSplittingField (K' := lvl.L) Pn) c
  rw [show algebraMap O (lvl.next Pn).L c =
      (algebraMap K (lvl.next Pn).L) (algebraMap O K c) from congrFun (congrArg _ h1) c]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)] in
/-- **`Level.algebraMap_OSelf_next_eq`, checked against the real `K_1 → K_2` step**: the composite
identity, applied at `level_K_1`, types exactly against `K_2.instAlgebraO`. -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))[X]) (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := (level_K_2 (K := K) (P := P) P₂).instAlgebraOSelf (O := O)
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    (algebraMap O (level_K_2 (K := K) (P := P) P₂).L :
        O →+* (level_K_2 (K := K) (P := P) P₂).L) =
      algebraMap O (nextSplittingField (K' := K_1 (K := K) P) P₂) :=
  Level.algebraMap_OSelf_next_eq (level_K_1 (K := K) (P := P)) P₂ hOK

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [IsFractionRing O K] in
/-- **The `Splits` invariant transports one level up.** `Q`'s image, known to split over `lvl.L`
(its self-composite), maps further to split over the next level's field, via `Polynomial.Splits.map`
plus `Polynomial.map_map` plus `Level.algebraMap_OSelf_next_eq`. Generalizes `splits_divX_map_K2P2`
(`§75`), whose proof is exactly this shape one level down. -/
theorem Level.splits_next (lvl : Level K) (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {Q : O[X]}
    (hSplits : letI := lvl.instAlgebraOSelf (O := O); (Q.map (algebraMap O lvl.L)).Splits) :
    letI := lvl.instAlgebraO Pn hOK
    (Q.map (algebraMap O (nextSplittingField (K' := lvl.L) Pn))).Splits := by
  letI := lvl.algL
  letI := lvl.instAlgebraOSelf (O := O)
  letI := lvl.instAlgebraO Pn hOK
  have hmap := hSplits.map (algebraMap lvl.L (nextSplittingField (K' := lvl.L) Pn))
  rw [Polynomial.map_map] at hmap
  rwa [show (algebraMap lvl.L (nextSplittingField (K' := lvl.L) Pn)).comp (algebraMap O lvl.L) =
      algebraMap O (nextSplittingField (K' := lvl.L) Pn) from
    (Level.algebraMap_OSelf_next_eq lvl Pn hOK)] at hmap

omit [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)] in
/-- **`Level.splits_next`, checked against the real `splits_divX_map_K2P2` (`§75`)**: applying it at
`level_K_1`, fed `splits_divX_map_K_1` (free from `K_1`'s own construction) for the base case,
produces exactly `splits_divX_map_K2P2`'s statement. -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))[X]) (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    (P.divX.map (algebraMap O (K2P2 (K := K) P₂))).Splits :=
  Level.splits_next (level_K_1 (K := K) (P := P)) P₂ hOK (splits_divX_map_K_1 P)

omit [Finite (IsLocalRing.ResidueField O)]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)] in
/-- **`Level.splits_next`, run twice, at the `K_2 → K_3` depth this arc has never reached for this
fact before** — instantiation, not recovery (`§83`'s own discipline: no pre-existing
`splits_divX_map_K3P3`/similar exists in this repo to compare against, checked by `grep` before
writing this file). -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))[X]) (P₃ : (O_K2 (K := K) P₂)[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    (P.divX.map
        (algebraMap O (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃))).Splits := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  exact Level.splits_next (level_K_2 (K := K) (P := P) P₂) P₃ hOK
    (Level.splits_next (level_K_1 (K := K) (P := P)) P₂ hOK (splits_divX_map_K_1 P))

end LubinTate

end
