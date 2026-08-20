/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepK3
import Langlands.IntegralClosureTower
import Langlands.NonarchimedeanPowerSeriesEvalAevalMap
import Langlands.EisensteinRootNorm
import Langlands.LubinTateEisensteinQ
import Langlands.LubinTateRootTranslation

/-!
# Norm-transport, connecting-identity, and transitivity infrastructure for the `K_2 → K_3` step

The `K_2 → K_3` analogue of `Langlands/LubinTateTowerStepRootConnect.lean`. **Update (`ROADMAP.md
§74`): the theorem this file was previously blocked on, `norm_lt_one_of_aeval_P₃_eq_zero`, now
closes**, against the *flat* `O_{K_2}` spelling `§73` switched to — see "History: the blocker, and
how it closed" below. The connecting identity (`eval_f_eq_of_aeval_P₃_eq_zero`) and transitivity
(`exists_piTorsion_translate_of_aeval_P₃_eq_zero`) close as well, built directly on top of it,
mirroring `Langlands/LubinTateTowerStepRootConnect.lean`'s own structure at the `K_1 → K_2` step.
**Invariance** (`piTorsion_one_K_3_eq_algebraMap_image`'s analogue) and the full degree computation
(`[K_3 : K_2] = q`) are **not built in this file** — see "What remains, and why it wasn't attempted"
below.

**Update (`ROADMAP.md §73`):** `O_{K_2}` is now the *flat* spelling `↥(integralClosure ↥𝒪[K]
(K_2 P₂))`, not the nested `↥(integralClosure O_{K_1} (K_2 P₂))` this docstring originally described
(`§62`–`§72`). `norm_le_one_of_mem_O_K2_in_K2P2`'s `Langlands/IntegralClosureTower.lean` detour
(mentioned below) is consequently **no longer needed** — with the flat spelling, `y.2` already is
the fact `norm_le_one_of_mem_integralClosure` needs directly. `K_3.instFaithfulSMul_O_K2` also
changed from `instance` to `theorem` (it now needs a `letI`-activated `Algebra ↥𝒪[K] (K_2 P₂)` to
even state, so cannot be found by ordinary instance search without that `letI` already active — see
`§73`).

## Naming, relative to the `K_1 → K_2` template

`α`/`α'` (the `K_1`-level generator, and its view inside `O_{K_1}`) are replaced by `β`/`β'` (the
`K_2`-level generator `Langlands/LubinTateTowerStepDegree.lean` produces, and its view inside
`O_{K_2}`); `β` (the `K_2`-level generator, root of `P₂`'s image, playing "`α`'s role" one level up)
is replaced by `γ` (the `K_3`-level generator, root of `P₃`'s image).
`O_{K_1}`/`K_1 P` become `O_{K_2}`/`K_2 P₂`; `K_2` becomes `K_3`.

## What closes here, and what is genuinely new relative to a mechanical substitution

* **`O_{K_2}`'s elements, viewed in `K_2 P₂`, do not have norm `≤ 1` "for free"** the way `O_{K_1}`'s
  did in `K_2`: `K_2.norm_le_one_of_mem_O_K1` applies `norm_le_one_of_mem_integralClosure` directly,
  because `O_{K_1} := integralClosure ↥𝒪[K] (K_1 P)` is *literally* of the shape that theorem needs.
  `O_{K_2} := integralClosure O_{K_1} (K_2 P₂)` is integral closure over the *intermediate* ring
  `O_{K_1}`, not `↥𝒪[K]` directly. Closed via `Langlands/IntegralClosureTower.lean`'s
  `isIntegral_iff_isIntegral_integralClosure` (`R ⊆ L ⊆ M`: integral over `R` iff integral over
  `↥(integralClosure R L)`), identifying an `O_{K_2}`-element's underlying value as integral over
  `↥𝒪[K]` directly, landing it in `integralClosure ↥𝒪[K] (K_2 P₂)` — applicable with `K' := K`
  (`K_2.hnorm_K` supplying `hnorm`, the same base-relative shortcut `Langlands/
  LubinTateTowerStepAdicCompleteK2.lean` already uses for `IsAdicComplete`).
* **An elaboration-cost lesson that closed several pieces**: `FaithfulSMul`/injectivity goals
  mentioning the doubly-`K_2`-nested `K_3` type, closed via an explicit `(algebraMap ...).injective`
  *dot-notation* term, do not terminate within several million heartbeats — the *same* fact, closed
  via the named lemma application `RingHom.injective _` instead of dot notation, elaborates in a few
  seconds. This closed `K_3.instFaithfulSMul_O_K2`/`K_3.instFaithfulSMul_O` (both needed — an earlier
  draft of this docstring claimed only the `O`-relative one was needed, mirroring
  `K_2.instFaithfulSMul_O_K1` being declared-but-unused at the `K_1 → K_2` step; that claim did not
  survive contact with the next file's needs — see "What does not close" below). This is a **new,
  narrower elaboration finding** than `Langlands/LubinTateTowerStepK3.lean`'s two (naming `O'`;
  avoiding premature return-type ascription): dot-notation projection forces a different (and here,
  catastrophically expensive) elaboration path than the equivalent named-lemma application, for this
  specific type shape. `NonarchimedeanPowerSeriesEval.eval_map`'s general form hits an analogous
  "expected type has an unresolved implicit ring parameter" snag when its `hcomp` proof is supplied as
  a pointwise `rfl`; `eval_map_towerHom2` is proved by directly repeating `eval_map`'s own short proof
  (`unfold`/`congr`/`funext`/`rw [PowerSeries.coeff_map]`) rather than invoking the general lemma,
  sidestepping the issue entirely.
* `IsDiscreteValuationRing (O_{K_2})` is needed (as an ambient hypothesis, not derived — mirroring
  `exists_eisenstein_tower_step_K_2`'s own treatment of the same instance) even for facts that,
  on the surface, look unrelated to it (`norm_coeff_map_of_isWeaklyEisensteinAt_associated`'s
  `[IsDiscreteValuationRing O]` hypothesis is threaded through, one level up, wherever `O_{K_2}`
  plays the "base ring" role).

## History: the blocker, and how it closed (`ROADMAP.md §65`–`§74`)

`norm_lt_one_of_aeval_P₃_eq_zero` — the `K_2 → K_3` analogue of `norm_lt_one_of_aeval_P₂_eq_zero` —
was, against the *nested* `O_{K_2}` spelling, a genuine, sustained, unresolved elaboration-cost
obstacle across five separate passes (`§65`–`§72`): every individual prerequisite instance/fact
elaborated in 2–4 seconds alone, but combining any two of them in one declaration exceeded
`400,000` heartbeats, and the full five-conjunct combination exceeded `8,000,000` heartbeats (40×
default) with no result. `§72`'s `trace.Meta.isDefEq`-instrumented run identified the mechanism
directly (not by inference): a large *reflexive* structural-congruence `isDefEq` walk (70,890+
logged comparisons, every one a term compared against itself, all succeeding) over `O_{K_2}`'s own
doubly-nested-`Subalgebra` type's definitional unfolding — cost scaling with unfolding *depth*, not
a genuine two-instance diamond.

**`§74` confirms directly**: against the *flat* `O_{K_2}` spelling `§73` switched to (one
`integralClosure` layer instead of two), the exact same repro that timed out at `400,000`–
`4,000,000` heartbeats under the nested spelling now elaborates **at or under default heartbeats
(`200,000`), in seconds**, both for `§72`'s minimal `isUnit_one` repro and for the
`Associated`-destructuring variant that previously needed `4,000,000` heartbeats. The full
`norm_lt_one_of_aeval_P₃_eq_zero` theorem — never successfully drafted as a real declaration by any
of `§65`–`§72` — closes as a genuine, `sorry`-free, non-scoped-test declaration for the first time
in this arc. See `ROADMAP.md §74` for exact timings and the implication for the tower's
representation choice.

## What remains, and why it wasn't attempted

**Invariance** (the `K_3`-level analogue of `piTorsion_one_K_2_eq_algebraMap_image`, `Langlands/
LubinTateTowerStepRootConnect.lean:386`) needs a genuinely new fact this file does not yet have: that
the level-`1` torsion polynomial `Q := P.divX`'s image splits completely not just over `K_1 P`
(`splits_divX_map_K_1`, already built) but over `K2P2 P₂` too — `K2P2` is a *further* extension of
`K_1 P`, not `Q`'s own splitting field, so this is not free from `splits_divX_map_K_1` alone; it
needs an explicit "splits is preserved under further field extension" transport (plausibly via
Mathlib's `Polynomial.splits_comp_of_splits` composed with `algebraMap (K_1 P) (K2P2 P₂)`, but this
was not checked or built this pass). Building it, then reproducing `piTorsion_one_K_2_eq_
algebraMap_image`'s multiset/`Finset.image` argument at this level, is a genuinely new, nontrivial
piece of work, not a mechanical substitution — deliberately left for a future pass rather than
forced through in the time remaining after the diagnostic result above (`ROADMAP.md §74`). The full
degree computation (`[K_3 : K_2] = q`, mirroring `Langlands/LubinTateTowerStepDegree.lean`) depends
on invariance and was likewise not attempted.

## Main results (closed)

* `norm_le_one_of_mem_O_K2_in_K2P2` / `K_3.norm_le_one_of_mem_O_K2` : the bound theorem above, and its
  extension one hop further into `K_3`.
* `K_3.instFaithfulSMul_O_K2` / `K_3.instFaithfulSMul_O` : `algebraMap O_{K_2} K_3` and `algebraMap O
  K_3` are both injective.
* `K_3.algebraMap_O_eq_comp_K_2` / `K_3.algebraMap_O_eq_comp_O_K2` : `K_3.instAlgebraO`'s four-hop
  composite collapses to the ordinary two-hop composites through `K_2 P₂` and through `O_{K_2}`
  respectively.
* `eval_map_towerHom2` : naturality of `eval` under the four-hop-derived `O → O_{K_2}` structure map.
* `towerHom2` : the `O → O_{K_2}` structure map itself.
* `K_3.hOK_transport` : `K`'s uniform norm bound transports down to `K_3` unchanged.
* `norm_lt_one_of_aeval_P₃_eq_zero` : a root of `P₃`'s image lies in the open unit ball of `K_3`
  (`ROADMAP.md §74`).
* `eval_f_eq_of_aeval_P₃_eq_zero` : the connecting identity, `eval f γ = algebraMap O_{K_2} K_3 β'`
  for `γ` a root of `P₃`'s image.
* `exists_piTorsion_translate_of_aeval_P₃_eq_zero` : transitivity of the `piTorsion hπ hf 1`
  translation action on roots of `P₃`'s image, at `K := K_3`.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace LubinTate

open IsLocalRing PowerSeries Polynomial NonarchimedeanPowerSeriesEval

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]
variable {π : O} {f : O⟦X⟧} {P : O[X]} (P₂ : (↥(integralClosure
    ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))[X])
  [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]

/-! ## `O_{K_2}`'s elements, viewed in `K_2 P₂`, have norm at most `1` -/

/-- **`O_{K_2}`'s elements, viewed in `K_2 P₂`, have norm at most `1`.** With the *flat* spelling
`O_{K_2} := ↥(integralClosure ↥𝒪[K] (K_2 P₂))` (`ROADMAP.md §73`), `y.2` **already is** membership in
`integralClosure ↥𝒪[K] (K_2 P₂)` directly — `norm_le_one_of_mem_integralClosure` applies to `y`
verbatim, with no `Langlands/IntegralClosureTower.lean` detour needed (unlike the nested spelling,
where `y.2` was membership in `integralClosure O_{K_1} (K_2 P₂)` and had to be converted first). -/
theorem norm_le_one_of_mem_O_K2_in_K2P2 (y : O_K2 (K := K) P₂) :
    ‖(y : K_2 (K' := K_1 (K := K) P) P₂)‖ ≤ 1 := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  haveI := finiteDimensional_K_K_2 (K := K) (P := P) P₂
  exact norm_le_one_of_mem_integralClosure (K' := K) (L := K_2 (K' := K_1 (K := K) P) P₂)
    (K_2.hnorm_K (K := K) (P := P) P₂) y

variable (P₃ : (O_K2 (K := K) P₂)[X])

/-- **`O_{K_2}`'s elements, viewed in `K_3`, have norm at most `1`.** The `K_2 → K_3` analogue of
`K_2.norm_le_one_of_mem_O_K1`: chains `spectralNorm_extends` at the `K_2 P₂ → K_3` hop with
`norm_le_one_of_mem_O_K2_in_K2P2` above.

**`letI := K_2.instAlgebraK …` is needed in the statement itself**, not just the proof — with the
flat spelling, `Algebra (O_{K_2}) K_3` (needed just to state `algebraMap _ (K_3 …) c`) is not
automatically available the way it was for the nested spelling: Mathlib's
`IsScalarTower.subalgebra'` instance (`Mathlib.Algebra.Algebra.Subalgebra.Tower`) derives
`Algebra ↥S₀ A` for `S₀ : Subalgebra R S` given `[Algebra R S] [Algebra S A]`; for the *nested*
spelling `R := O_{K_1}`, `Algebra O_{K_1} (K_2 P₂)` is free (`K_2.instAlgebra`), but for the *flat*
spelling `R := ↥𝒪[K]`, `Algebra ↥𝒪[K] (K_2 P₂)` is exactly `K_2.instAlgebraK`'s
`Algebra.ofSubsemiring`-derived instance, which needs the `letI` active (`ROADMAP.md §73`). -/
theorem K_3.norm_le_one_of_mem_O_K2 (c : O_K2 (K := K) P₂) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) c‖ ≤ 1 := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  have heq : algebraMap (O_K2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂)
      (K' := K2P2 (K := K) P₂) P₃) c =
      algebraMap (K2P2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
        (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂) c) :=
    IsScalarTower.algebraMap_apply _ _ _ c
  rw [K_2.norm_eq_spectralNorm, heq, spectralNorm_extends]
  exact norm_le_one_of_mem_O_K2_in_K2P2 (K := K) (P := P) P₂ c

/-- **`algebraMap O_{K_2} K_3` is injective.** Needed by `norm_coeff_map_of_isWeaklyEisensteinAt_
associated`'s `[FaithfulSMul O_{K_2} K_3]` requirement (mirroring `K_2.instFaithfulSMul_O_K1`'s own
role at the `K_1 → K_2` step — this pass's earlier module-docstring note that this instance "is not
built here since nothing downstream needs it" was **wrong**, corrected here: it genuinely is needed,
just not by the pieces built before this one). Built via the `intro a b hab` + separate `have`s
style (not `rw` immediately followed by a composed `.comp` term), and `RingHom.injective _` (not
dot notation) for the first hop — the same two fixes that closed `K_3.instFaithfulSMul_O`. -/
theorem K_3.instFaithfulSMul_O_K2 :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    FaithfulSMul (O_K2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  rw [faithfulSMul_iff_algebraMap_injective]
  have h1 : Function.Injective
      (algebraMap (K2P2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) :=
    RingHom.injective _
  have h2 : Function.Injective (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) :=
    Subtype.coe_injective
  intro a b hab
  have ha : algebraMap (O_K2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂)
      (K' := K2P2 (K := K) P₂) P₃) a =
      algebraMap (K2P2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
        (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂) a) :=
    IsScalarTower.algebraMap_apply _ _ _ a
  have hb : algebraMap (O_K2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂)
      (K' := K2P2 (K := K) P₂) P₃) b =
      algebraMap (K2P2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
        (algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂) b) :=
    IsScalarTower.algebraMap_apply _ _ _ b
  rw [ha, hb] at hab
  exact h2 (h1 hab)

/-! ## `algebraMap O K_3`, `algebraMap O_{K_2} K_3`, and their compatibility -/

/-- **`algebraMap O (K_2 P₂)` [via `K_2.instAlgebraO`] equals `algebraMap O_{K_2} (K_2 P₂) ∘`
the first three hops of `K_3.instAlgebraO`'s composite** (`O → ↥𝒪[K] → O_{K_2}`). By `rfl`, unlike
`algebraMap_O_K_1_eq_comp_towerHom` (which needs a genuine proof at the `K → K_1 P` level) —
**relative to the flat `O_{K_2}` spelling** (`ROADMAP.md §73`), the middle hop is `↥𝒪[K] → O_{K_2}`
(the subalgebra inclusion), not `O_{K_1} → O_{K_2}` as with the nested spelling — `O_{K_2}`'s algebra
structure over `K_2 P₂` and `K`'s two-hop composite (`K_2.instAlgebraK`) already agree definitionally
once both are routed through the same `Algebra.ofSubsemiring`-derived instance (`letI`-activated),
confirmed `rfl` directly. -/
theorem algebraMap_O_K2P2_eq_comp_towerHom2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    ⇑(algebraMap O (K2P2 (K := K) P₂)) =
      ⇑(algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) ∘
        ⇑(algebraMap ↥(ValuativeRel.valuation K).valuationSubring (O_K2 (K := K) P₂)) ∘
        ⇑(toValuationSubring (K := K) hOK) := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  rfl

/-- **`K_3.instAlgebraO`'s composite collapses to the ordinary two-hop `algebraMap (K_2 P₂) K_3 ∘
algebraMap O (K_2 P₂)`.** The `K_2 → K_3` analogue of `K_2.algebraMap_O_eq_comp_K_1`. -/
theorem K_3.algebraMap_O_eq_comp_K_2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    ⇑(algebraMap O (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) =
      ⇑(algebraMap (K2P2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) ∘
        ⇑(algebraMap O (K2P2 (K := K) P₂)) := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
  rw [K_3.algebraMap_O_eq (K := K) (P := P) P₂ P₃ hOK,
    algebraMap_O_K2P2_eq_comp_towerHom2 (K := K) (P₂ := P₂) hOK]

/-- **`algebraMap O K_3` [via `K_3.instAlgebraO`] equals the ordinary `algebraMap O_{K_2} K_3`
composed with the `O → O_{K_2}` structure map** (`O → O_{K_1} → O_{K_2}`, the composite
`isLocalHom_comp_towerHom_K_2` proves local). Needed for `eval_map_towerHom2`'s naturality
hypothesis. -/
theorem K_3.algebraMap_O_eq_comp_O_K2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    ⇑(algebraMap O (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) =
      ⇑(algebraMap (O_K2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂)
        (K' := K2P2 (K := K) P₂) P₃)) ∘
      ⇑((algebraMap ↥(ValuativeRel.valuation K).valuationSubring
          (O_K2 (K := K) P₂)).comp (toValuationSubring (K := K) hOK)) := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
  funext c
  show algebraMap O (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) c = _
  rw [K_3.algebraMap_O_eq (K := K) (P := P) P₂ P₃ hOK]
  exact (IsScalarTower.algebraMap_apply (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)
    (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
    (algebraMap ↥(ValuativeRel.valuation K).valuationSubring
      (O_K2 (K := K) P₂) (toValuationSubring (K := K) hOK c))).symm

/-- **`algebraMap O K_3` is injective.** Mirrors `K_2.instFaithfulSMul_O`'s own proof exactly:
rewrite via `K_3.algebraMap_O_eq_comp_K_2` to the ordinary two-hop composite, then compose two
injective maps — closed via `RingHom.injective _` (a named lemma application), **not** `(algebraMap
...).injective` (dot notation), which hits the elaboration wall described in the module docstring. -/
theorem K_3.instFaithfulSMul_O (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    FaithfulSMul O (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
  rw [faithfulSMul_iff_algebraMap_injective]
  have h1 : Function.Injective
      (algebraMap (K2P2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) :=
    RingHom.injective _
  haveI := K_2.instFaithfulSMul_O (K := K) (P := P) (P₂ := P₂) hOK
  have h2 : Function.Injective (algebraMap O (K2P2 (K := K) P₂)) :=
    FaithfulSMul.algebraMap_injective O (K2P2 (K := K) P₂)
  have h3 := h1.comp h2
  rwa [K_3.algebraMap_O_eq_comp_K_2 (K := K) (P := P) P₂ P₃ hOK]

/-- **`eval` is natural under the `O → O_{K_2}` structure map.** Proved directly by repeating
`NonarchimedeanPowerSeriesEval.eval_map`'s own short proof (rather than invoking that lemma), which
sidesteps an elaboration snag when its `hcomp` argument is supplied as a pointwise `rfl` at this
type — see the module docstring. -/
theorem eval_map_towerHom2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {f : O⟦X⟧}
    (γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    NonarchimedeanPowerSeriesEval.eval
      (PowerSeries.map ((algebraMap ↥(ValuativeRel.valuation K).valuationSubring
        (O_K2 (K := K) P₂)).comp (toValuationSubring (K := K) hOK)) f) γ =
      NonarchimedeanPowerSeriesEval.eval f γ := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
  unfold NonarchimedeanPowerSeriesEval.eval
  congr 1

/-- **The `O → O_{K_2}` structure map**, the composite `O → ↥𝒪[K] → O_{K_2}` — the moving-base
structure map `Langlands/LubinTateTowerStep.lean`'s `TowerStep` section needs at `O' := O_{K_2}`.
Mirrors `towerHom` one level up. **The middle hop is `↥𝒪[K] → O_{K_2}` (the subalgebra inclusion),
not `O_{K_1} → O_{K_2}`**, since the flat `O_{K_2}` sits directly over `↥𝒪[K]`, not over `O_{K_1}`
(`ROADMAP.md §73`) — so this composite uses `toValuationSubring hOK : O →+* ↥𝒪[K]` directly, rather
than the three-hop `towerHom hOK P : O →+* O_{K_1}`. -/
def towerHom2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    O →+* O_K2 (K := K) P₂ :=
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  (algebraMap ↥(ValuativeRel.valuation K).valuationSubring
    (O_K2 (K := K) P₂)).comp (toValuationSubring (K := K) hOK)

/-- **`K`'s uniform norm bound (`hOK`) transports down to `K_3` unchanged.** The `K_2 → K_3` analogue
of `K_2.hOK_transport`: chains `K_3.algebraMap_O_eq`'s four-hop composite with
`IsScalarTower.algebraMap_apply` (folding the last two hops into the single `algebraMap O_{K_2} K_3`
map) and `K_3.norm_le_one_of_mem_O_K2` (the bound on that single hop). -/
theorem K_3.hOK_transport (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    ∀ c : O, ‖algebraMap O (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) c‖ ≤ 1 := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
  intro c
  have hcoe : algebraMap O (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) c =
      algebraMap (O_K2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
        (algebraMap ↥(ValuativeRel.valuation K).valuationSubring (O_K2 (K := K) P₂)
          (toValuationSubring (K := K) hOK c)) := by
    have h1 := congrFun (K_3.algebraMap_O_eq (K := K) (P := P) P₂ P₃ hOK) c
    rw [h1]
    exact (IsScalarTower.algebraMap_apply (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
      (algebraMap ↥(ValuativeRel.valuation K).valuationSubring (O_K2 (K := K) P₂)
        (toValuationSubring (K := K) hOK c))).symm
  rw [hcoe]
  exact K_3.norm_le_one_of_mem_O_K2 (K := K) (P := P) P₂ P₃ _

/-! ## The `K_2 → K_3` analogue of `norm_lt_one_of_aeval_P₂_eq_zero` -/

/-- **A root of `P₃`'s image (via the `K2P2` polynomial route) lies in `K_3`'s open unit ball.**
The `K_2 → K_3` analogue of `norm_lt_one_of_aeval_P₂_eq_zero` (`Langlands/
LubinTateTowerStepRootConnect.lean`), closed here for the first time against the **flat** `O_{K_2}`
spelling (`ROADMAP.md §73`/`§74`) — `§65`–`§72` diagnosed and never closed this theorem against the
*nested* spelling, blocked on a severe `isDefEq`-cost obstacle now confirmed (`§74`) to be resolved
by the flat switch. Same argument as `norm_lt_one_of_aeval_P₂_eq_zero`, one level up: `Langlands.
EisensteinRootNorm`'s ultrametric-only Eisenstein-polygon computation (no irreducibility over a base
field needed), fed the norm data `norm_coeff_map_of_isWeaklyEisensteinAt_associated`
(`Langlands.LubinTateEisensteinQ`) produces from `P₃`'s `O_{K_2}`-level Eisenstein data (`hP₃dist`/
`hassoc`). `hβ'irr`/`hβ'norm` are carried as explicit hypotheses (not derived from `O_{K_2}`'s own
construction), matching this arc's standing convention at every tower level. -/
theorem norm_lt_one_of_aeval_P₃_eq_zero (β' : O_K2 (K := K) P₂) (hβ'irr : Irreducible β')
    (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _)) (hassoc : Associated (P₃.coeff 0) β')
    (hdeg : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃}
    (hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    ‖γ‖ < 1 := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  have hstep : Polynomial.aeval γ P₃ = 0 := by
    rw [aeval_map_eq_eval_coe] at hγroot
    rwa [eval_coe_eq_aeval] at hγroot
  haveI := K_3.instFaithfulSMul_O_K2 (K := K) (P := P) P₂ P₃
  obtain ⟨hmonic, hdegeq, hc0, -, hweak⟩ :=
    norm_coeff_map_of_isWeaklyEisensteinAt_associated
      (K := K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
      (K_3.norm_le_one_of_mem_O_K2 (K := K) (P := P) P₂ P₃) hβ'irr hP₃dist.monic
      hP₃dist.toIsWeaklyEisensteinAt hassoc
  refine Polynomial.norm_lt_one_of_isEisensteinShape_of_root hmonic (by rw [hdegeq]; exact hdeg)
    hβ'norm hc0 hweak
    (by rw [Polynomial.aeval_def, ← Polynomial.eval_map] at hstep; exact hstep)

/-- **The connecting identity itself**: for `γ` a root of `P₃`'s image, `eval f γ` equals `β'`
(the `O_{K_2}`-level generator `P₃`'s constant term is built from), algebra-mapped into `K_3` — the
`K_2 → K_3` analogue of `eval_f_eq_of_aeval_P₂_eq_zero`. Simpler in one respect than that template:
since `β'` is already an `O_{K_2}` element (not a field-level `α` reached via a separate `hα'coe`
witness), the conclusion is stated directly as `algebraMap O_{K_2} K_3 β'`, with no intermediate
field-level identification needed. Chains the Weierstrass factorization
`shifted f (towerHom2 hOK) β' = (P₃ : _⟦X⟧) * u₃` through `eval` (`eval_mul`/`eval_sub`/`eval_C`,
using `norm_lt_one_of_aeval_P₃_eq_zero` for the `‖γ‖ < 1` hypothesis and
`K_3.norm_le_one_of_mem_O_K2` for the coefficient-bound hypotheses), then `eval_map_towerHom2` to
land on `eval f γ` itself. -/
theorem eval_f_eq_of_aeval_P₃_eq_zero (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    (β' : O_K2 (K := K) P₂) (u₃ : (O_K2 (K := K) P₂)⟦X⟧) (_hu₃ : IsUnit u₃)
    (heq₃ :
      letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : _⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₃.coeff 0) β') (hdeg : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
    {γ : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃}
    (hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    NonarchimedeanPowerSeriesEval.eval f γ =
      algebraMap (O_K2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
        β' := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
  have hγnorm : ‖γ‖ < 1 :=
    norm_lt_one_of_aeval_P₃_eq_zero (K := K) (P := P) P₂ P₃ β' hβ'irr hP₃dist hassoc hdeg hβ'norm
      hγroot
  have hstep0 : NonarchimedeanPowerSeriesEval.eval
      (↑P₃ : PowerSeries (O_K2 (K := K) P₂)) γ = 0 := by
    rw [← aeval_map_eq_eval_coe (K' := K2P2 (K := K) P₂)]; exact hγroot
  have hbP₃ : ∀ n, ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
      (PowerSeries.coeff n (↑P₃ : PowerSeries (O_K2 (K := K) P₂)))‖ ≤ 1 :=
    fun n ↦ K_3.norm_le_one_of_mem_O_K2 (K := K) (P := P) P₂ P₃ _
  have hbu₃ : ∀ n, ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
      (PowerSeries.coeff n u₃)‖ ≤ 1 :=
    fun n ↦ K_3.norm_le_one_of_mem_O_K2 (K := K) (P := P) P₂ P₃ _
  have hshifted0 : NonarchimedeanPowerSeriesEval.eval
      (shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β') γ = 0 := by
    rw [heq₃, NonarchimedeanPowerSeriesEval.eval_mul hbP₃ hbu₃ hγnorm, hstep0, zero_mul]
  have hbfmap : ∀ n, ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
      (PowerSeries.coeff n (PowerSeries.map (towerHom2 (K := K) (P := P) P₂ hOK) f))‖ ≤ 1 :=
    fun n ↦ K_3.norm_le_one_of_mem_O_K2 (K := K) (P := P) P₂ P₃ _
  have hbCβ' : ∀ n, ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
      (PowerSeries.coeff n (PowerSeries.C β' : PowerSeries _))‖ ≤ 1 :=
    fun n ↦ K_3.norm_le_one_of_mem_O_K2 (K := K) (P := P) P₂ P₃ _
  have hsub : NonarchimedeanPowerSeriesEval.eval
      (PowerSeries.map (towerHom2 (K := K) (P := P) P₂ hOK) f) γ -
      NonarchimedeanPowerSeriesEval.eval (PowerSeries.C β' : PowerSeries _) γ = 0 := by
    rw [← NonarchimedeanPowerSeriesEval.eval_sub hbfmap hbCβ' hγnorm]
    exact hshifted0
  rw [NonarchimedeanPowerSeriesEval.eval_C] at hsub
  have hmapeq : NonarchimedeanPowerSeriesEval.eval
      (PowerSeries.map (towerHom2 (K := K) (P := P) P₂ hOK) f) γ =
      algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) β' :=
    sub_eq_zero.mp hsub
  unfold towerHom2 at hmapeq
  rwa [eval_map_towerHom2 (K := K) (P := P) P₂ P₃ hOK γ] at hmapeq

/-! ## Transitivity of the translation action on roots of `P₃`'s image -/

/-- **Transitivity of the `piTorsion hπ hf 1` translation action on roots of `P₃`'s image, at
`K := K_3`.** The `K_2 → K_3` analogue of `exists_piTorsion_translate_of_aeval_P₂_eq_zero`: for
`γ, γ'` both roots (via the `K2P2` polynomial route), there is `t' ∈ piTorsion hπ hf 1` (evaluated
inside `K_3`) with `γ' = F_π(γ, t')`. Both `eval f γ` and `eval f γ'` equal `algebraMap O_{K_2} K_3
β'` by `eval_f_eq_of_aeval_P₃_eq_zero` (applied to each root separately), hence to each other;
`Langlands.LubinTateRootTranslation.exists_piTorsion_translate_of_eval_f_eq` (the *generic*
transitivity fact) then supplies `t'` directly. -/
theorem exists_piTorsion_translate_of_aeval_P₃_eq_zero (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    (β' : O_K2 (K := K) P₂) (u₃ : (O_K2 (K := K) P₂)⟦X⟧) (_hu₃ : IsUnit u₃)
    (heq₃ :
      letI := K_2.instAlgebraK (K := K) (P := P) P₂
      shifted f (towerHom2 (K := K) (P := P) P₂ hOK) β' = (P₃ : _⟦X⟧) * u₃)
    (hβ'irr : Irreducible β') (hP₃dist : P₃.IsDistinguishedAt (maximalIdeal _))
    (hassoc : Associated (P₃.coeff 0) β') (hdeg : 0 < P₃.natDegree)
    (hβ'norm : letI := K_2.instAlgebraK (K := K) (P := P) P₂
      ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) (β' : _)‖ < 1)
    {γ γ' : K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃}
    (hγroot : Polynomial.aeval γ (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0)
    (hγ'root : Polynomial.aeval γ' (P₃.map (algebraMap _ (K2P2 (K := K) P₂))) = 0) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    ∃ t' ∈ piTorsion (K := K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) hπ hf 1,
      γ' = FPiEval hπ hf γ t' := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
  have h1 := eval_f_eq_of_aeval_P₃_eq_zero (K := K) (P := P) P₂ P₃ hOK β' u₃ _hu₃ heq₃ hβ'irr
    hP₃dist hassoc hdeg hβ'norm hγroot
  have h2 := eval_f_eq_of_aeval_P₃_eq_zero (K := K) (P := P) P₂ P₃ hOK β' u₃ _hu₃ heq₃ hβ'irr
    hP₃dist hassoc hdeg hβ'norm hγ'root
  have hγnorm : ‖γ‖ < 1 :=
    norm_lt_one_of_aeval_P₃_eq_zero (K := K) (P := P) P₂ P₃ β' hβ'irr hP₃dist hassoc hdeg hβ'norm
      hγroot
  have hγ'norm : ‖γ'‖ < 1 :=
    norm_lt_one_of_aeval_P₃_eq_zero (K := K) (P := P) P₂ P₃ β' hβ'irr hP₃dist hassoc hdeg hβ'norm
      hγ'root
  exact exists_piTorsion_translate_of_eval_f_eq (K_3.hOK_transport (K := K) (P := P) P₂ P₃ hOK) hπ
    hf hγnorm hγ'norm (h1.trans h2.symm)

end LubinTate

end
