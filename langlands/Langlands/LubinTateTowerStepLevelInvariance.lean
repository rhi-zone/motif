/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepLevelDegree

/-!
# `piTorsion`-invariance and the degree theorem, generically in `Level` (`ROADMAP.md` §86)

`§85` narrowed what stands between `Level.FPiEval_algebraMap_mem_adjoin` and the `∀ n` degree
theorem to precisely three items: a generic `FaithfulSMul O lvl.L`, a generic roots-multiset
transport along the level-change ring map, and reapplication of the already-generic
`piTorsion_one_sdiff_zero_eq_roots_toFinset` at two levels. This file supplies all three, closes
`piTorsion_one_K_2_eq_algebraMap_image`/`_K_3_eq_algebraMap_image`'s generic form, and then the
whole degree chain that was blocked on it — `adjoin_root_eq_top`, `hgen`, and
`finrank_K_n_eq_residueCard` — all checked `rfl`-equal to the two hand-written concrete depths.

## What the three items actually turned out to be

* **`FaithfulSMul O lvl.L` is mechanical, as `§84` guessed** — checked by real elaboration, not
  assumed: `Level.faithfulSMul_OSelf` is `IsFractionRing.injective O K` composed with
  `(algebraMap K lvl.L).injective`, through `Level.algebraMap_OSelf_eq`'s (`§84`) factorization of
  the self-composite. It needs no hypothesis beyond the ambient `[IsFractionRing O K]` the whole
  arc already carries. The next-level analogue (`Level.faithfulSMul_O_next`, the generic
  `K_2.instFaithfulSMul_O`/`K_3.instFaithfulSMul_O`) is the same composition one hop longer,
  through `Level.algebraMap_O_eq_comp_L` (`§83`).
* **The roots-multiset transport needs no new general-purpose lemma.** `§85` flagged this as
  possibly Mathlib-shaped work. Checked against Mathlib directly before writing anything:
  `Polynomial.Monic.roots_map_of_card_eq_natDegree`
  (`Mathlib/Algebra/Polynomial/Roots.lean`) and `Polynomial.Splits.roots_map`
  (`Mathlib/Algebra/Polynomial/Splits.lean`) already state exactly the multiset transport, and
  `Multiset.toFinset_map` converts it to the `Finset.image` form. What was genuinely missing is
  only this repo's own algebra-map bookkeeping — `Level.map_algebraMap_O_next_eq_map`, the generic
  `divX_map_algebraMap_O_K_2_eq_map`/`_K_3_eq_map`, which is `Polynomial.map_map` plus the
  composite identity `Level.algebraMap_OSelf_comp_next`. Adding a "general" roots-transport lemma
  here would have duplicated Mathlib, so none was added.
* **`piTorsion_one_sdiff_zero_eq_roots_toFinset` transfers unchanged**, as `§85` predicted: it is
  already generic in its own field parameter (`Langlands/LubinTateRootCount.lean`), and the two
  instantiations need only `hOK`/`hπnorm` at each level. At `lvl.L` those come from `hnormL`
  through `Level.norm_algebraMap_OSelf` (new here, one line); at the next level they are
  `Level.hOK_transport`/`Level.hπnorm_transport` (`§83`) unchanged.

## The degree chain, which follows once invariance closes

With invariance generic, `adjoin_root_eq_top_K_2`/`_K_3`'s proof generalizes verbatim
(`Level.adjoin_root_eq_top`), since every other ingredient was already generic:
`Level.norm_lt_one_of_root` and `Level.exists_piTorsion_translate_of_root` (`§82`/`§83`),
`Level.FPiEval_algebraMap_mem_adjoin` (`§85`), and `Polynomial.IsSplittingField.adjoin_rootSet`,
which applies to `baseChangeSplittingField (K' := lvl.L) Pn` by that combinator's own construction at every level.

`hgen` — the hypothesis `Level.exists_tower_step_next`/`Level.adjoin_eq_integralClosure_next` have
taken externally since `§83` — is then **derivable, not assumed**: `Level.natDegree_minpoly_eq_finrank`
is `IntermediateField.adjoin.finrank` applied to `Level.adjoin_root_eq_top`'s conclusion, with `β`'s
integrality free from `Algebra.IsIntegral.of_finite`. The degree theorem itself
(`Level.finrank_next_eq_residueCard`) is `IntermediateField.finrank_top'` against the same
conclusion, exactly as the two concrete versions are.

## Checked against both concrete depths, by `rfl`

Four `example`s, each a fully-applied generic term checked `rfl`-equal to the corresponding
hand-written concrete theorem (proof irrelevance witnessing that the two *statements* elaborate to
the same `Prop` — the discipline `§82`–`§85` already use):

* `Level.piTorsion_one_next_eq_algebraMap_image` at `level_K_1` = `piTorsion_one_K_2_eq_algebraMap_image`
* the same at `level_K_2` = `piTorsion_one_K_3_eq_algebraMap_image`
* `Level.finrank_next_eq_residueCard` at `level_K_1` = `finrank_K_2_eq_residueCard`
* the same at `level_K_2` = `finrank_K_3_eq_residueCard`

The `K_2 → K_3` instances feed the generic `Splits` datum as `Level.splits_next (level_K_1) P₂ hOK
(splits_divX_map_K_1 P)` (`§84`), i.e. the induction actually runs one hop before being consumed.

## What this does not close, and the precise reason

**Residue-field preservation (`residueFieldEquiv_K_2`/`_K_3`'s generic form) is not closed here**,
and it is not blocked on mathematics: attempted for real this pass, and abandoned on an
elaboration-cost obstacle that was diagnosed rather than forced. The generic step assembles from
pieces that all exist — `Level.adjoin_eq_integralClosure_next` (`§76`/`§83`, now feedable the
derived `hgen`), `Algebra.adjoin_singleton_eq_top_of_adjoin_eq_integralClosure`,
`mem_maximalIdeal_of_isDistinguishedAt_root`, `IsLocalRing.residueFieldEquivOfAdjoinSingleton`, and
`residueFieldEquiv_integralClosure_integralClosure` for the nested→flat bridge — but applying
`IsLocalRing.residueFieldEquivOfAdjoinSingleton` to the *real* `hβmem`/`hadjS` terms over an
abstract `lvl` exceeds the default `maxHeartbeats` in `whnf`. Measured with `set_option diagnostics
true`: 90565 `Membership.mem`, 89736 `Set`, 50194 `integralClosure`, 46028 `SetLike.coe`, 44525
`Set.Mem` unfoldings, dragging 751 `baseChangeSplittingField`/`SplittingField` and the `Ideal.Quotient`/`RingCon`
quotient internals underneath them. Two things were checked and ruled out, rather than assumed: the
same application with *opaque* hypotheses of the same shape elaborates in seconds, and an explicit
type ascription on `hβmem` does not help — so this is the `§72`-class structural `whnf` walk over
`↥(integralClosure lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn))`'s set-membership unfolding, not an instance
search and not a two-committed-instances diamond. Per this project's no-shim rule no
`maxHeartbeats` override was added; the piece is left open with this measurement on the record.

A smaller, genuinely diagnosed instance issue *was* root-caused and is recorded because it is the
same family: `Algebra lvl.OL ↥(integralClosure lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn))` — the plain
`Subalgebra.algebra` instance — is not reached by instance search inside the default
`synthInstance.maxHeartbeats` over an abstract `lvl`, though it *is* reached with a larger budget,
and the instance search then finds is `rfl`-equal to `Subalgebra.algebra _` (checked by a real
`example ... := rfl`). That one is therefore fixable by naming the instance rather than searching
for it — but it is not on the path of anything this file commits.

## Main results

* `Level.norm_algebraMap_OSelf` : `‖algebraMap O lvl.L c‖ = ‖algebraMap O K c‖`, from `hnormL`.
* `Level.faithfulSMul_OSelf` / `Level.faithfulSMul_O_next` : injectivity of the self- and
  next-level `O`-algebra maps.
* `Level.algebraMap_OSelf_comp_next` / `Level.map_algebraMap_O_next_eq_map` : the composite
  identity and its `Polynomial.map` form.
* `Level.piTorsion_one_next_eq_algebraMap_image` : **the invariance fact**, generic in `lvl`.
* `Level.adjoin_root_eq_top` : `lvl.L⟮β⟯ = ⊤`, generic in `lvl`.
* `Level.natDegree_minpoly_eq_finrank` : `hgen`, no longer an external hypothesis.
* `Level.finrank_next_eq_residueCard` : **`[K_{n+1} : K_n] = residueCard O`**, generic in `lvl`.
-/
@[expose] public section

noncomputable section

open scoped Polynomial IntermediateField

namespace LubinTate

open IsLocalRing PowerSeries Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]

/-- **The self-composite preserves `K`'s norm on `O`'s image**: `‖algebraMap O lvl.L c‖ =
‖algebraMap O K c‖`, immediately from `Level.algebraMap_OSelf_eq` (`§84`) and `hnormL`. This is the
generic form of the computation `K_1.hOK_transport`/`K_1.hπnorm_transport` each do by hand, and it
supplies both the `hOK`- and the `hπnorm`-shaped hypotheses that
`piTorsion_one_sdiff_zero_eq_roots_toFinset` needs at `lvl.L` itself. -/
theorem Level.norm_algebraMap_OSelf (lvl : Level K)
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖) (c : O) :
    letI := lvl.instAlgebraOSelf (O := O)
    ‖algebraMap O lvl.L c‖ = ‖algebraMap O K c‖ := by
  letI := lvl.algL
  letI := lvl.instAlgebraOSelf (O := O)
  show ‖algebraMap K lvl.L (algebraMap O K c)‖ = ‖algebraMap O K c‖
  exact hnormL _

/-- **`algebraMap O lvl.L` is injective**, for the self-composite `Level.instAlgebraOSelf` (`§84`)
— the `Level`-generic `K_1.instFaithfulSMul`, and the gap `§84`/`§85` each named as still open.
`§84` predicted it would be mechanical; checked here by real elaboration, it is: the composite is
`algebraMap K lvl.L ∘ algebraMap O K`, injective as a ring hom out of a field composed with
`IsFractionRing.injective`. It needs no hypothesis beyond the ambient `[IsFractionRing O K]` the
whole arc already carries — in particular no `hOK` and no norm data. -/
theorem Level.faithfulSMul_OSelf (lvl : Level K) :
    letI := lvl.instAlgebraOSelf (O := O)
    FaithfulSMul O lvl.L := by
  letI := lvl.algL
  letI := lvl.instAlgebraOSelf (O := O)
  rw [faithfulSMul_iff_algebraMap_injective]
  intro a b hab
  exact IsFractionRing.injective O K ((algebraMap K lvl.L).injective hab)

/-- **`algebraMap O (baseChangeSplittingField (K' := lvl.L) Pn)` is injective** — the `Level`-generic
`K_2.instFaithfulSMul_O`/`K_3.instFaithfulSMul_O`. The same composition one hop longer, reading the
three factors off `Level.algebraMap_O_eq_comp_L` (`§83`). -/
theorem Level.faithfulSMul_O_next (lvl : Level K) (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := lvl.instAlgebraO Pn hOK
    FaithfulSMul O (baseChangeSplittingField (K' := lvl.L) Pn) := by
  letI := lvl.algL
  letI := lvl.instAlgebraO Pn hOK
  rw [faithfulSMul_iff_algebraMap_injective, lvl.algebraMap_O_eq_comp_L Pn hOK]
  exact ((algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)).injective.comp
    (algebraMap K lvl.L).injective).comp (IsFractionRing.injective O K)

/-- **`algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) ∘ algebraMap O lvl.L = algebraMap O (baseChangeSplittingField (K' :=
lvl.L) Pn)`**, as a `RingHom` equality. Bridges `Level.algebraMap_O_eq_comp_L` (`§83`, which factors
the next-level composite through `K`) with `Level.algebraMap_OSelf_eq` (`§84`, which identifies
`algebraMap O lvl.L` with that same `K`-route) — the same combination `§85` performed inline inside
`Level.FPiEval_algebraMap_mem_adjoin`, extracted here as a standalone `RingHom` identity so that
`Polynomial.map_map` can consume it directly. -/
theorem Level.algebraMap_OSelf_comp_next (lvl : Level K) (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := lvl.instAlgebraOSelf (O := O)
    letI := lvl.instAlgebraO Pn hOK
    (algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)).comp (algebraMap O lvl.L) =
      algebraMap O (baseChangeSplittingField (K' := lvl.L) Pn) := by
  letI := lvl.algL
  letI := lvl.instAlgebraOSelf (O := O)
  letI := lvl.instAlgebraO Pn hOK
  refine RingHom.ext fun c => ?_
  rw [RingHom.comp_apply, congrFun (lvl.algebraMap_O_eq_comp_L Pn hOK) c,
    congrFun (congrArg DFunLike.coe (lvl.algebraMap_OSelf_eq (O := O))) c]
  rfl

/-- **Any `Q : O[X]`'s image over `baseChangeSplittingField (K' := lvl.L) Pn` is its image over `lvl.L`, mapped
further.** The `Level`-generic `divX_map_algebraMap_O_K_2_eq_map`
(`Langlands/LubinTateTowerStepRootConnect.lean`) / `divX_map_algebraMap_O_K_3_eq_map`
(`Langlands/LubinTateTowerStepK3RootConnect.lean`): `Polynomial.map_map` plus
`Level.algebraMap_OSelf_comp_next`. Stated for an arbitrary `Q`, since nothing in the argument uses
more than that. -/
theorem Level.map_algebraMap_O_next_eq_map (lvl : Level K) (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (Q : O[X]) :
    letI := lvl.instAlgebraOSelf (O := O)
    letI := lvl.instAlgebraO Pn hOK
    Q.map (algebraMap O (baseChangeSplittingField (K' := lvl.L) Pn)) =
      (Q.map (algebraMap O lvl.L)).map (algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)) := by
  letI := lvl.algL
  letI := lvl.instAlgebraOSelf (O := O)
  letI := lvl.instAlgebraO Pn hOK
  rw [Polynomial.map_map, lvl.algebraMap_OSelf_comp_next Pn hOK]

/-- **`piTorsion hπ hf 1`, evaluated inside `baseChangeSplittingField (K' := lvl.L) Pn`, is exactly the
`algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)`-image of `piTorsion hπ hf 1` evaluated inside `lvl.L`** —
the level-`1` `π`-torsion does not grow going up one tower step, generically in `lvl : Level K`.
The `Level`-generic `piTorsion_one_K_2_eq_algebraMap_image`
(`Langlands/LubinTateTowerStepRootConnect.lean`) / `piTorsion_one_K_3_eq_algebraMap_image`
(`Langlands/LubinTateTowerStepK3RootConnect.lean`), which — read line by line — are the same proof
under a systematic substitution, with nothing `n`-specific in it.

`hSplits` (`Q := P.divX`'s image splits over `lvl.L`) is genuinely level-indexed induction data, not
derivable from `Level`: it is free at the base from `K_1 P`'s own construction
(`splits_divX_map_K_1`) and propagates upward by `Level.splits_next` (`§84`).

Proof: at each of `lvl.L` and `baseChangeSplittingField (K' := lvl.L) Pn`, `piTorsion hπ hf 1 \ {0}` is the root set of
`Q`'s image (`piTorsion_one_sdiff_zero_eq_roots_toFinset`, already generic in its own field
parameter); `hSplits` plus `Polynomial.splits_iff_card_roots` gives `roots.card = natDegree`, so
`Polynomial.Monic.roots_map_of_card_eq_natDegree` transports the roots multiset along
`algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)` onto the roots of the further-mapped polynomial, which
`Level.map_algebraMap_O_next_eq_map` identifies with `Q`'s own image over the next level.
`Multiset.toFinset_map` converts to `Finset.image`, and `{0}` is reassembled at both ends. -/
theorem Level.piTorsion_one_next_eq_algebraMap_image (lvl : Level K) (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    (hSplits : letI := lvl.instAlgebraOSelf (O := O);
      (P.divX.map (algebraMap O lvl.L)).Splits) :
    letI := lvl.instAlgebraOSelf (O := O)
    letI := lvl.instAlgebraO Pn hOK
    (piTorsion (K := baseChangeSplittingField (K' := lvl.L) Pn) hπ hf 1 : Set (baseChangeSplittingField (K' := lvl.L) Pn)) =
      algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) '' (piTorsion (K := lvl.L) hπ hf 1) := by
  classical
  letI := lvl.algL
  letI := lvl.instAlgebraOSelf (O := O)
  letI := lvl.instAlgebraO Pn hOK
  haveI := lvl.faithfulSMul_OSelf (O := O)
  haveI := lvl.faithfulSMul_O_next Pn hOK
  have hOKL : ∀ c : O, ‖algebraMap O lvl.L c‖ ≤ 1 := by
    intro c; rw [lvl.norm_algebraMap_OSelf hnormL c]; exact hOK c
  have hπnormL : ‖algebraMap O lvl.L π‖ < 1 := by
    rw [lvl.norm_algebraMap_OSelf hnormL π]; exact hπnorm
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  have hQmonic : (P.divX.map (algebraMap O lvl.L)).Monic :=
    (divX_isWeaklyEisensteinAt_and_associated hu heq hf.1 hf.2.1 hPdist hPdeg2).1.map _
  have hcard : (P.divX.map (algebraMap O lvl.L)).roots.card =
      (P.divX.map (algebraMap O lvl.L)).natDegree :=
    Polynomial.splits_iff_card_roots.mp hSplits
  have hrootsmap : (P.divX.map (algebraMap O lvl.L)).roots.map
      (algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)) =
      ((P.divX.map (algebraMap O lvl.L)).map
        (algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn))).roots :=
    hQmonic.roots_map_of_card_eq_natDegree _ hcard
  rw [← lvl.map_algebraMap_O_next_eq_map Pn hOK P.divX] at hrootsmap
  have hfinseteq : Finset.image (algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn))
      (P.divX.map (algebraMap O lvl.L)).roots.toFinset =
      (P.divX.map (algebraMap O (baseChangeSplittingField (K' := lvl.L) Pn))).roots.toFinset := by
    rw [← Multiset.toFinset_map, hrootsmap]
  have hstep1 := piTorsion_one_sdiff_zero_eq_roots_toFinset (K := lvl.L)
    hOKL hπ hπnormL hf hu heq hPdist hPdeg
  have hstep2 := piTorsion_one_sdiff_zero_eq_roots_toFinset (K := baseChangeSplittingField (K' := lvl.L) Pn)
    (lvl.hOK_transport Pn hOK hnormL) hπ (lvl.hπnorm_transport Pn hOK hnormL hπnorm)
    hf hu heq hPdist hPdeg
  have himageeq :
      algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) '' (piTorsion (K := lvl.L) hπ hf 1 \ {0}) =
      piTorsion (K := baseChangeSplittingField (K' := lvl.L) Pn) hπ hf 1 \ {0} := by
    rw [hstep1, hstep2, ← Finset.coe_image, hfinseteq]
  have h0 : algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) '' (piTorsion (K := lvl.L) hπ hf 1) =
      insert (algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) 0)
        (algebraMap lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) ''
          (piTorsion (K := lvl.L) hπ hf 1 \ {0})) := by
    rw [← Set.image_insert_eq]
    congr 1
    rw [Set.insert_sdiff_singleton]
    exact (Set.insert_eq_self.mpr (zero_mem_piTorsion hπ hf 1)).symm
  rw [h0, himageeq, map_zero, Set.insert_sdiff_singleton]
  exact (Set.insert_eq_self.mpr (zero_mem_piTorsion hπ hf 1)).symm

section Degree

variable (lvl : Level K) [IsDomain lvl.OL] [IsDiscreteValuationRing lvl.OL]

/-- **`lvl.L⟮β⟯ = ⊤`, for `β` any root of `Pn`'s image in `baseChangeSplittingField (K' := lvl.L) Pn`** — the
`Level`-generic `adjoin_root_eq_top_K_2`/`adjoin_root_eq_top_K_3`.

`baseChangeSplittingField (K' := lvl.L) Pn` is by construction the splitting field of `Pn`'s image over `lvl.L`, hence
generated by its roots (`Polynomial.IsSplittingField.adjoin_rootSet`). Every root `β'` differs from
`β` by a `piTorsion hπ hf 1`-translate (`Level.exists_piTorsion_translate_of_root`, `§83`), and by
`Level.piTorsion_one_next_eq_algebraMap_image` (above) that translate is the `algebraMap`-image of
an `lvl.L`-torsion point `t`, so `β' = F_π(β, algebraMap t) ∈ lvl.L⟮β⟯` by
`Level.FPiEval_algebraMap_mem_adjoin` (`§85`); `β` lies in its own adjoin. -/
theorem Level.adjoin_root_eq_top (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    {P : O[X]} (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    (hSplits : letI := lvl.instAlgebraOSelf (O := O);
      (P.divX.map (algebraMap O lvl.L)).Splits)
    {α' : lvl.OL} {v : lvl.OL⟦X⟧} (hv : IsUnit v)
    (heqn : shifted f (lvl.towerHom hOK) α' = (Pn : lvl.OL⟦X⟧) * v)
    (hα'irr : Irreducible α') (hPndist : Pn.IsDistinguishedAt (maximalIdeal lvl.OL))
    (hassoc : Associated (Pn.coeff 0) α') (hdeg : 0 < Pn.natDegree)
    (hα'norm : ‖algebraMap lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn) α'‖ < 1)
    {β : baseChangeSplittingField (K' := lvl.L) Pn}
    (hβroot : Polynomial.aeval β (Pn.map (algebraMap lvl.OL lvl.L)) = 0) :
    letI := lvl.instAlgebraO Pn hOK
    (lvl.L⟮β⟯ : IntermediateField lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)) = ⊤ := by
  letI := lvl.algL
  letI := lvl.instAlgebraOSelf (O := O)
  letI := lvl.instAlgebraO Pn hOK
  have hβnorm : ‖β‖ < 1 :=
    lvl.norm_lt_one_of_root Pn hnormL hα'irr hPndist hassoc hdeg hα'norm hβroot
  have hroots : ((Pn.map (algebraMap lvl.OL lvl.L)).rootSet (baseChangeSplittingField (K' := lvl.L) Pn)) ⊆
      ((lvl.L⟮β⟯ : IntermediateField lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)).toSubalgebra :
        Set (baseChangeSplittingField (K' := lvl.L) Pn)) := by
    intro β' hβ'
    obtain ⟨-, hβ'root⟩ := Polynomial.mem_rootSet'.mp hβ'
    obtain ⟨t', ht'mem, ht'eq⟩ :=
      lvl.exists_piTorsion_translate_of_root Pn hOK hnormL hπ hf hv heqn hα'irr hPndist hassoc
        hdeg hα'norm hβroot hβ'root
    rw [lvl.piTorsion_one_next_eq_algebraMap_image Pn hOK hnormL hπ hπnorm hf hu heq hPdist
      hPdeg hSplits] at ht'mem
    obtain ⟨t, htmem, htmem'⟩ := ht'mem
    rw [SetLike.mem_coe, IntermediateField.mem_toSubalgebra, ht'eq, ← htmem']
    exact lvl.FPiEval_algebraMap_mem_adjoin Pn hOK hnormL hπ hf hβnorm htmem.1
  have hle : (⊤ : Subalgebra lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)) ≤
      (lvl.L⟮β⟯ : IntermediateField lvl.L (baseChangeSplittingField (K' := lvl.L) Pn)).toSubalgebra := by
    rw [← Polynomial.IsSplittingField.adjoin_rootSet (baseChangeSplittingField (K' := lvl.L) Pn)
      (Pn.map (algebraMap lvl.OL lvl.L))]
    exact Algebra.adjoin_le hroots
  refine eq_top_iff.mpr fun x _ ↦ ?_
  exact (IntermediateField.mem_toSubalgebra _ x).mp (hle Algebra.mem_top)

/-- **`hgen`, derived rather than assumed**: `(minpoly lvl.L β).natDegree = Module.finrank lvl.L
(baseChangeSplittingField (K' := lvl.L) Pn)` — the chosen root really does generate the next field.

This hypothesis has been carried externally by `Level.irreducible_root_next`,
`Level.exists_tower_step_next` and `Level.adjoin_eq_integralClosure_next` since `§83`, which is
where `§83`/`§84` both located the remaining obstacle to a self-contained `∀ n` step. It follows
from `Level.adjoin_root_eq_top` by `IntermediateField.finrank_top'` and
`IntermediateField.adjoin.finrank`; `β`'s integrality over `lvl.L` is free from
`Algebra.IsIntegral.of_finite`, `baseChangeSplittingField (K' := lvl.L) Pn` being finite over `lvl.L`. -/
theorem Level.natDegree_minpoly_eq_finrank (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    {P : O[X]} (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    (hSplits : letI := lvl.instAlgebraOSelf (O := O);
      (P.divX.map (algebraMap O lvl.L)).Splits)
    {α' : lvl.OL} {v : lvl.OL⟦X⟧} (hv : IsUnit v)
    (heqn : shifted f (lvl.towerHom hOK) α' = (Pn : lvl.OL⟦X⟧) * v)
    (hα'irr : Irreducible α') (hPndist : Pn.IsDistinguishedAt (maximalIdeal lvl.OL))
    (hassoc : Associated (Pn.coeff 0) α') (hdeg : 0 < Pn.natDegree)
    (hα'norm : ‖algebraMap lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn) α'‖ < 1)
    {β : baseChangeSplittingField (K' := lvl.L) Pn}
    (hβroot : Polynomial.aeval β (Pn.map (algebraMap lvl.OL lvl.L)) = 0) :
    (minpoly lvl.L β).natDegree = Module.finrank lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) := by
  letI := lvl.algL
  haveI : Algebra.IsIntegral lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) := Algebra.IsIntegral.of_finite _ _
  have hβint : IsIntegral lvl.L β := Algebra.IsIntegral.isIntegral β
  have htop := lvl.adjoin_root_eq_top Pn hOK hnormL hπ hπnorm hf hu heq hPdist hPdeg hSplits
    hv heqn hα'irr hPndist hassoc hdeg hα'norm hβroot
  rw [← IntermediateField.finrank_top' (F := lvl.L) (E := baseChangeSplittingField (K' := lvl.L) Pn), ← htop,
    IntermediateField.adjoin.finrank hβint]

/-- **`Module.finrank lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) = residueCard O`** — `[K_{n+1} : K_n] = q`,
generically in `lvl : Level K`. The `Level`-generic `finrank_K_2_eq_residueCard`
(`Langlands/LubinTateTowerStepDegree.lean`) / `finrank_K_3_eq_residueCard`
(`Langlands/LubinTateTowerStepK3Degree.lean`), and the theorem the whole degree/splitting half of
the `∀ n` tower step was aiming at.

`hβfin` (`Module.finrank lvl.L lvl.L⟮β⟯ = residueCard O`) stays an explicit hypothesis, exactly as
it is in both concrete versions: it is what the transitivity/root-count half of the argument
supplies about the chosen root, not something `Level` carries. `Level.adjoin_root_eq_top` upgrades
that `β` to `lvl.L⟮β⟯ = ⊤`, and `IntermediateField.finrank_top'` transfers the rank. -/
theorem Level.finrank_next_eq_residueCard (Pn : lvl.OL[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    {P : O[X]} (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    (hSplits : letI := lvl.instAlgebraOSelf (O := O);
      (P.divX.map (algebraMap O lvl.L)).Splits)
    {α' : lvl.OL} {v : lvl.OL⟦X⟧} (hv : IsUnit v)
    (heqn : shifted f (lvl.towerHom hOK) α' = (Pn : lvl.OL⟦X⟧) * v)
    (hα'irr : Irreducible α') (hPndist : Pn.IsDistinguishedAt (maximalIdeal lvl.OL))
    (hassoc : Associated (Pn.coeff 0) α') (hdeg : 0 < Pn.natDegree)
    (hα'norm : ‖algebraMap lvl.OL (baseChangeSplittingField (K' := lvl.L) Pn) α'‖ < 1)
    {β : baseChangeSplittingField (K' := lvl.L) Pn}
    (hβroot : Polynomial.aeval β (Pn.map (algebraMap lvl.OL lvl.L)) = 0)
    (hβfin : letI := lvl.algL; Module.finrank lvl.L lvl.L⟮β⟯ = residueCard O) :
    letI := lvl.algL
    Module.finrank lvl.L (baseChangeSplittingField (K' := lvl.L) Pn) = residueCard O := by
  letI := lvl.algL
  have htop := lvl.adjoin_root_eq_top Pn hOK hnormL hπ hπnorm hf hu heq hPdist hPdeg hSplits
    hv heqn hα'irr hPndist hassoc hdeg hα'norm hβroot
  rw [← IntermediateField.finrank_top' (F := lvl.L) (E := baseChangeSplittingField (K' := lvl.L) Pn), ← htop]
  exact hβfin

end Degree
/-! ## The generic theorems really are the concrete ones -/


/-- **Invariance, `K_1 → K_2`, `rfl`-recovery**: the generic theorem at `level_K_1`, fed
`splits_divX_map_K_1` (free from `K_1 P`'s own construction), types exactly as
`piTorsion_one_K_2_eq_algebraMap_image`'s own statement. -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O) :
    Level.piTorsion_one_next_eq_algebraMap_image (level_K_1 (K := K) (P := P)) P₂ hOK
        (hnorm_K_K_1 (K := K) (P := P)) hπ hπnorm hf hu heq hPdist hPdeg
        (splits_divX_map_K_1 (K := K) P) =
      piTorsion_one_K_2_eq_algebraMap_image (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq
        hPdist hPdeg := rfl

/-- **Invariance, `K_2 → K_3`, `rfl`-recovery**: the same generic theorem at `level_K_2`, fed the
`Splits` datum propagated one hop by `Level.splits_next` (`§84`), types exactly as
`piTorsion_one_K_3_eq_algebraMap_image`'s own statement. -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]
    (P₃ : (O_K2 (K := K) P₂)[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O) :
    Level.piTorsion_one_next_eq_algebraMap_image (level_K_2 (K := K) (P := P) P₂) P₃ hOK
        (hnorm_K_K_2 (K := K) (P := P) P₂) hπ hπnorm hf hu heq hPdist hPdeg
        (Level.splits_next (level_K_1 (K := K) (P := P)) P₂ hOK
          (splits_divX_map_K_1 (K := K) P)) =
      piTorsion_one_K_3_eq_algebraMap_image (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq
        hPdist hPdeg := rfl

/-- **The degree theorem, `K_1 → K_2`, `rfl`-recovery** against `finrank_K_2_eq_residueCard`.
The concrete version's extra `hα'coe : (α' : K_1 P) = α` argument is the inessential
scaffolding `§82` already identified; the generic theorem does not need it. -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    {α' : ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))}
    {u₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)))⟦X⟧} (hu₂ : IsUnit u₂)
    (heq₂ : shifted f (towerHom (K := K) hOK P) α' =
      (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)))⟦X⟧) * u₂)
    (hα'irr : Irreducible α') (hP₂dist : P₂.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₂.coeff 0) α') (hdeg : 0 < P₂.natDegree)
    (hα'norm : ‖algebraMap _ (baseChangeSplittingField (K' := K_1 (K := K) P) P₂) (α' : _)‖ < 1)
    {α : K_1 (K := K) P} (hα'coe : (α' : K_1 (K := K) P) = α)
    {β : baseChangeSplittingField (K' := K_1 (K := K) P) P₂}
    (hβroot : Polynomial.aeval β (P₂.map (algebraMap _ (K_1 (K := K) P))) = 0)
    (hβfin : Module.finrank (K_1 (K := K) P) (K_1 (K := K) P)⟮β⟯ = residueCard O) :
    Level.finrank_next_eq_residueCard (level_K_1 (K := K) (P := P)) P₂ hOK
        (hnorm_K_K_1 (K := K) (P := P)) hπ hπnorm hf hu heq hPdist hPdeg
        (splits_divX_map_K_1 (K := K) P) hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hβroot
        hβfin =
      finrank_K_2_eq_residueCard (K := K) (P := P) (P₂ := P₂) hOK hπ hπnorm hf hu heq hPdist
        hPdeg hu₂ heq₂ hα'irr hP₂dist hassoc hdeg hα'norm hα'coe hβroot hβfin := rfl

/-- **The degree theorem, `K_2 → K_3`, `rfl`-recovery** against `finrank_K_3_eq_residueCard` —
the first time this arc has the degree computation stated once and checked at both real depths. -/
example {P : O[X]}
    (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
    [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]
    (P₃ : (O_K2 (K := K) P₂)[X])
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O)
    (β' : O_K2 (K := K) P₂) (u₃ : (O_K2 (K := K) P₂)⟦X⟧) (hu₃ : IsUnit u₃)
    (heq₃ : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : (O_K2 (K := K) P₂)⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₃.coeff 0) β') (hdeg : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃}
    (hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0)
    (hγfin : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      Module.finrank (K2P2 (K := K) P₂) (K2P2 (K := K) P₂)⟮γ⟯ = residueCard O) :
    Level.finrank_next_eq_residueCard (level_K_2 (K := K) (P := P) P₂) P₃ hOK
        (hnorm_K_K_2 (K := K) (P := P) P₂) hπ hπnorm hf hu heq hPdist hPdeg
        (Level.splits_next (level_K_1 (K := K) (P := P)) P₂ hOK (splits_divX_map_K_1 (K := K) P))
        hu₃ heq₃ hβ'irr hP₃dist hassoc hdeg hβ'norm hγroot hγfin =
      finrank_K_3_eq_residueCard (K := K) (P := P) P₂ P₃ hOK hπ hπnorm hf hu heq hPdist hPdeg
        β' u₃ hu₃ heq₃ hβ'irr hP₃dist hassoc hdeg hβ'norm hγroot hγfin := rfl

end LubinTate

end
