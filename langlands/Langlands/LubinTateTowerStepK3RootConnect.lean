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
# Norm-transport and structure-map infrastructure for the `K_2 → K_3` step

The `K_2 → K_3` analogue of `Langlands/LubinTateTowerStepRootConnect.lean`, **up through the
structure-map/injectivity infrastructure only** — the connecting identity itself
(`eval f γ = algebraMap (K_2 P₂) K_3 β`) and everything downstream of it (transitivity, invariance)
are **not built in this file**: see "What does not close" below for a precise account of a genuine
elaboration-cost obstacle blocking it, found and diagnosed (not forced through) after sustained
effort.

## Naming, relative to the `K_1 → K_2` template

`α`/`α'` (the `K_1`-level generator, and its view inside `O_{K_1}`) are replaced by `β`/`β'` (the
`K_2`-level generator `Langlands/LubinTateTowerStepDegree.lean` produces, and its view inside
`O_{K_2}`); `β` (the `K_2`-level generator, root of `P₂`'s image, playing "`α`'s role" one level up)
is replaced by `γ` (the `K_3`-level generator, root of `P₃`'s image, not yet reached — see below).
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

## What does NOT close: a genuine, sustained, unresolved elaboration-cost obstacle

`norm_lt_one_of_aeval_P₃_eq_zero` — the `K_2 → K_3` analogue of `norm_lt_one_of_aeval_P₂_eq_zero`,
needed for the connecting identity, transitivity, and invariance facts that would otherwise complete
this file's Main Results list — **does not close**, and was not forced through with a workaround or
a `sorry`. Full diagnostic record:

* The theorem needs `norm_coeff_map_of_isWeaklyEisensteinAt_associated` (`Langlands/
  LubinTateEisensteinQ.lean`) instantiated at `O := O_{K_2}`, `K := K_3`, which — checked directly —
  genuinely needs `[FaithfulSMul O_{K_2} K_3]` (contrary to this file's own earlier working
  assumption that only the `O`-relative `FaithfulSMul` was consumed downstream at the `K_1 → K_2`
  step; corrected, and `K_3.instFaithfulSMul_O_K2` was built to supply it).
* **Even with every individual prerequisite instance/fact available and separately fast to
  elaborate**, applying `norm_coeff_map_of_isWeaklyEisensteinAt_associated`'s conclusion — or
  reproducing its proof inline, decomposed into five separate `have`s, one real (non-`sorry`,
  non-`inferInstance`) term at a time — **is not itself sufficient**: the moment *two or more* of
  these real terms (e.g. `K_3.norm_le_one_of_mem_O_K2 ...` together with a `Polynomial.
  IsDistinguishedAt.monic`/`.toIsWeaklyEisensteinAt` projection, or `norm_algebraMap_eq_one_of_isUnit`
  applied with its `O`/`K` named explicitly) appear together in the *same* declaration, elaboration
  cost explodes. Confirmed by extensive, systematic bisection (not 2-3 tries): each piece alone
  elaborates in 2-4 seconds; combining any two of them exceeds `400,000` heartbeats; the full original
  five-piece `obtain` exceeded `8,000,000` heartbeats (40× default) after over three minutes of wall
  time with no result. This reproduces reliably and precisely — removing any one "real" term from a
  failing combination restores fast elaboration; re-adding it reproduces the failure — ruling out
  transient/nondeterministic causes.
* **This is a different failure shape from every other elaboration obstacle found in this arc**
  (`ROADMAP.md §62`'s Obstacle 2, this pass's own `K_3.lean`/earlier-in-this-file findings): those
  were single-term costs, fixable by naming an implicit explicitly, swapping dot notation for a named
  lemma, or deferring a return-type ascription. This one is a **combinatorial interaction** between
  multiple independently-cheap real terms sharing the same doubly-`K_2`-nested ambient type — no
  single-term fix of the kind that closed every earlier obstacle in this arc was found to apply, after
  genuine, systematic attempts (bare application, eta-expansion, pre-staged `have`s with explicit
  ascription, explicit named-argument variants of `norm_coeff_map_of_isWeaklyEisensteinAt_associated`
  and of `norm_algebraMap_eq_one_of_isUnit` — all tried, all exhibiting the same interaction).
* No further mitigation was found within this pass's effort budget. Per this project's stop-and-
  diagnose discipline, this is recorded as a precise, load-bearing blocker rather than forced through
  — see `ROADMAP.md §65` for the handoff.

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

/-- **`O_{K_2}`'s elements, viewed in `K_2 P₂`, have norm at most `1`.** Uses
`Langlands/IntegralClosureTower.lean`'s `isIntegral_iff_isIntegral_integralClosure` to identify the
underlying value with an element of `integralClosure ↥𝒪[K] (K_2 P₂)`, then
`norm_le_one_of_mem_integralClosure` directly at `K' := K` (`K_2.hnorm_K` supplying `hnorm`). -/
theorem norm_le_one_of_mem_O_K2_in_K2P2 (y : O_K2 (K := K) P₂) :
    ‖(y : K_2 (K' := K_1 (K := K) P) P₂)‖ ≤ 1 := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  haveI := isScalarTower_R_K_1_K_2 (K := K) (P := P) (P₂ := P₂)
  haveI := finiteDimensional_K_K_2 (K := K) (P := P) P₂
  have hyint' : IsIntegral ↥(ValuativeRel.valuation K).valuationSubring
      (y : K_2 (K' := K_1 (K := K) P) P₂) :=
    (isIntegral_iff_isIntegral_integralClosure
      (R := ↥(ValuativeRel.valuation K).valuationSubring) (L := K_1 (K := K) P)
      (M := K_2 (K' := K_1 (K := K) P) P₂)).mpr y.2
  exact norm_le_one_of_mem_integralClosure (K' := K) (L := K_2 (K' := K_1 (K := K) P) P₂)
    (K_2.hnorm_K (K := K) (P := P) P₂) (⟨(y : K_2 (K' := K_1 (K := K) P) P₂), hyint'⟩)

variable (P₃ : (O_K2 (K := K) P₂)[X])

/-- **`O_{K_2}`'s elements, viewed in `K_3`, have norm at most `1`.** The `K_2 → K_3` analogue of
`K_2.norm_le_one_of_mem_O_K1`: chains `spectralNorm_extends` at the `K_2 P₂ → K_3` hop with
`norm_le_one_of_mem_O_K2_in_K2P2` above. -/
theorem K_3.norm_le_one_of_mem_O_K2 (c : O_K2 (K := K) P₂) :
    ‖algebraMap _ (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) c‖ ≤ 1 := by
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
instance K_3.instFaithfulSMul_O_K2 :
    FaithfulSMul (O_K2 (K := K) P₂)
      (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) := by
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
the first three hops of `K_3.instAlgebraO`'s composite** (`O → O_{K_1} → O_{K_2}`). By `rfl`, unlike
`algebraMap_O_K_1_eq_comp_towerHom` (which needs a genuine proof at the `K → K_1 P` level) — both
composites from `O_{K_1}` onward already agree definitionally, since `O_{K_2}`'s algebra structure
over `K_2 P₂` and `K_1 P`'s do too (`Subalgebra`-derived, confirmed `rfl` directly). -/
theorem algebraMap_O_K2P2_eq_comp_towerHom2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    ⇑(algebraMap O (K2P2 (K := K) P₂)) =
      ⇑(algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) ∘
        ⇑(algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (O_K2 (K := K) P₂)) ∘
        ⇑(towerHom (K := K) hOK P) := by
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  rfl

/-- **`K_3.instAlgebraO`'s composite collapses to the ordinary two-hop `algebraMap (K_2 P₂) K_3 ∘
algebraMap O (K_2 P₂)`.** The `K_2 → K_3` analogue of `K_2.algebraMap_O_eq_comp_K_1`. -/
theorem K_3.algebraMap_O_eq_comp_K_2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    ⇑(algebraMap O (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) =
      ⇑(algebraMap (K2P2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) ∘
        ⇑(algebraMap O (K2P2 (K := K) P₂)) := by
  letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
  letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
  rw [K_3.algebraMap_O_eq (K := K) (P := P) P₂ P₃ hOK,
    algebraMap_O_K2P2_eq_comp_towerHom2 (K := K) (P₂ := P₂) hOK]

/-- **`algebraMap O K_3` [via `K_3.instAlgebraO`] equals the ordinary `algebraMap O_{K_2} K_3`
composed with the `O → O_{K_2}` structure map** (`O → O_{K_1} → O_{K_2}`, the composite
`isLocalHom_comp_towerHom_K_2` proves local). Needed for `eval_map_towerHom2`'s naturality
hypothesis. -/
theorem K_3.algebraMap_O_eq_comp_O_K2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    ⇑(algebraMap O (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) =
      ⇑(algebraMap (O_K2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂)
        (K' := K2P2 (K := K) P₂) P₃)) ∘
      ⇑((algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
          (K_1 (K := K) P)) (O_K2 (K := K) P₂)).comp (towerHom (K := K) hOK P)) := by
  letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
  funext c
  show algebraMap O (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) c = _
  rw [K_3.algebraMap_O_eq (K := K) (P := P) P₂ P₃ hOK]
  exact (IsScalarTower.algebraMap_apply (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)
    (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)
    (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (K_1 (K := K) P)) (O_K2 (K := K) P₂) (towerHom (K := K) hOK P c))).symm

/-- **`algebraMap O K_3` is injective.** Mirrors `K_2.instFaithfulSMul_O`'s own proof exactly:
rewrite via `K_3.algebraMap_O_eq_comp_K_2` to the ordinary two-hop composite, then compose two
injective maps — closed via `RingHom.injective _` (a named lemma application), **not** `(algebraMap
...).injective` (dot notation), which hits the elaboration wall described in the module docstring. -/
theorem K_3.instFaithfulSMul_O (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraO (K := K) (P := P) P₂ hOK
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    FaithfulSMul O (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) := by
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
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    NonarchimedeanPowerSeriesEval.eval
      (PowerSeries.map ((algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
        (K_1 (K := K) P)) (O_K2 (K := K) P₂)).comp (towerHom (K := K) hOK P)) f) γ =
      NonarchimedeanPowerSeriesEval.eval f γ := by
  letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
  unfold NonarchimedeanPowerSeriesEval.eval
  congr 1

/-- **The `O → O_{K_2}` structure map**, the composite `O → O_{K_1} → O_{K_2}` — the moving-base
structure map `Langlands/LubinTateTowerStep.lean`'s `TowerStep` section needs at `O' := O_{K_2}`.
Mirrors `towerHom` one level up. -/
def towerHom2 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    O →+* O_K2 (K := K) P₂ :=
  (algebraMap ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P))
    (O_K2 (K := K) P₂)).comp (towerHom (K := K) hOK P)

end LubinTate

end
