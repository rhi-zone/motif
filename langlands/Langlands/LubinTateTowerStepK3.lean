/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepConcreteK3
import Langlands.LubinTateTowerStepAdicCompleteK2

/-!
# `K_3` carries the same `NormedField`/`Algebra O` package `K_1`/`baseChangeSplittingField` do

`LubinTate.K_3` (`Langlands/LubinTateTowerStepConcreteK3.lean`) is so far only a bare `Field`/
`Algebra (baseChangeSplittingField P₂)`/`IsSplittingField`. This file supplies the `NontriviallyNormedField`/
`IsUltrametricDist`/`CompleteSpace`/`NormedSpace`/`Algebra O` package, exactly mirroring
`Langlands/LubinTateTowerStepSplittingField.lean`'s `baseChangeSplittingField`-level construction, one level up.

**Update (`ROADMAP.md §73`):** `O_{K_2}` below is now the *flat* spelling
`↥(integralClosure ↥𝒪[K] (baseChangeSplittingField P₂))` (integral closure directly over the tower's base), not the
nested `↥(integralClosure O_{K_1} (baseChangeSplittingField P₂))` this docstring originally described throughout
`§62`–`§72`. The rest of this docstring is kept as the historical record of how the
`NontriviallyNormedField`/`Algebra O` package was established — every claim below about *why* each
piece resolves still holds for the flat spelling too (see `§73` for what changed and why), except
where a passage names `O_{K_1}` as `O_{K_2}`'s immediate base, which is specific to the
now-superseded nested spelling.

## Mechanical vs. new content

`Langlands/LubinTateTowerStepSplittingField.lean`'s `NormExtension` section is already generic in
its own free parameters `O'`/`K'` — its own docstring predicts exactly this reuse ("reusable verbatim
at the *next* tower step ... without modification"). **Confirmed directly, not assumed**: since
`K_3 P₃ := baseChangeSplittingField (K' := K') P₃` (`LubinTateTowerStepConcreteK3.lean`) unfolds definitionally to `baseChangeSplittingField`'s
own construction, `baseChangeSplittingField.instNontriviallyNormedField`/`.instIsUltrametricDist`/`.instCompleteSpace`/
`.instNormedSpace`, applied at `O' := O_{K_2}`, `K' := baseChangeSplittingField P₂`, solve for `K_3` verbatim — the only
prerequisite is `Algebra O_{K_2} (baseChangeSplittingField P₂)`, which (checked directly via a `trace.Meta.synthInstance`
probe, not assumed) resolves by ordinary instance search: `O_{K_2} := integralClosure O_{K_1}
(baseChangeSplittingField P₂)` is, exactly as `Langlands/LubinTateTowerStepMonogenic.lean`'s docstring found one level
down for `O_{K_1}`, a genuine `Subalgebra`-coerced type of `baseChangeSplittingField P₂`, so Mathlib's generic
`Subalgebra.instSMulSubtypeMem`-derived `Algebra` instance supplies it automatically. **This half is
mechanical, modulo one new elaboration obstacle below.**

## A new elaboration obstacle, found and diagnosed: `baseChangeSplittingField` applied to a `baseChangeSplittingField`-nested `K'`

Directly hand-writing a goal or instance whose stated type is `baseChangeSplittingField (K' := baseChangeSplittingField (K' := K_1 P) P₂) P₃`
— i.e. `baseChangeSplittingField` (or `K_3`, defined in terms of it) applied at a base field `K'` that is *itself* a
`baseChangeSplittingField` application, rather than a `K_1`-application as at the `K_1 → K_2` step — fails with
"Application type mismatch", reproduced directly (several independent minimal variants, all
failing identically): with `O'` left implicit or given as `_`, the elaborator never unifies `O'`
with `P₃`'s actual ring before checking the application, leaving a bare metavariable and rejecting
`P₃`. This is the *same shape* of "Application type mismatch" diamond `ROADMAP.md §62`'s Obstacle 2
already diagnosed for the doubly-nested `integralClosure` type (`↥(integralClosure
(↥(integralClosure R L)) M)`) — but here it hits `baseChangeSplittingField`/`K_3`'s own `SplittingField`-based
construction instead, the first time this specific construction has been applied two levels deep.

**Confirmed not a mathematical obstruction, and confirmed fixable** (unlike `§62`'s case, which
needed a new general transport lemma): supplying `O'` **explicitly by name** (`baseChangeSplittingField (O' := ...)
(K' := ...) P₃`), rather than leaving it for unification, sidesteps the elaborator's stuck
metavariable entirely — checked directly, several independent minimal reproductions, all succeeding
once `O'` is named. This is the exact same lesson `§62`'s Obstacle 2 already recorded ("name every
implicit type parameter the section binds, don't rely on unification to recover it") extended to a
new site. Every declaration below that mentions `K_3 (... ) P₃` therefore gives `O'` explicitly.

## A second, independent elaboration obstacle: catastrophic elaboration cost, not just rejection

Even once `O'` is named, checking an *explicit proof term* against a stated goal mentioning
`K_3 (O' := ...) (K' := ...) P₃` does not merely fail — it is prohibitively **slow**: a single
`instance` built as `baseChangeSplittingField.instNontriviallyNormedField P₃ : NontriviallyNormedField (K_3 ...)` (rather
than closed by `inferInstance`) exceeds `1_000_000` heartbeats (confirmed directly, several
independent timed reproductions, one left running unbounded for over four minutes with no result).
Two independent mitigations were found, both confirmed directly by timing before being adopted here:

* **`inferInstance` instead of an explicit witness term.** `baseChangeSplittingField.instNontriviallyNormedField P₃`
  elaborated as an explicit term (whose own implicit `O'`/`K'` must be *inferred*, then checked by
  `isDefEq` against the stated goal) is what times out; `inferInstance` (typeclass search, a
  differently-implemented and apparently far cheaper unification strategy against the same goal)
  closes the identical goal in about two seconds. Used for every `NontriviallyNormedField`/
  `IsUltrametricDist`/`CompleteSpace`/`NormedSpace`/`FiniteDimensional` instance below.
* **No explicit return-type ascription on `K_3.instAlgebraO`.** This one cannot be closed by
  `inferInstance` (it is a hand-built composite, not a pre-existing instance), so the fix is
  different: stating its return type as `Algebra O (K_3 (O' := ...) (K' := ...) P₃)` propagates that
  expected type into the elaboration of every inner `algebraMap`/`.comp` step and does not terminate;
  omitting the ascription and letting Lean infer the type (`Algebra O (baseChangeSplittingField (K' := K2P2 P₂) P₃)` —
  defeq to, but not syntactically, `Algebra O (K_3 ...)`) elaborates in under three seconds, and the
  one remaining defeq check against `K_3`'s spelling — needed only once, at each downstream *use*
  site — is itself fast (confirmed directly: `K_3.instAlgebraO ... hOK` type-checked against the
  explicit `Algebra O (K_3 ...)` ascription in well under the default heartbeat budget).
* **Naming `O_{K_2}`/`baseChangeSplittingField P₂` once via `abbrev`, referenced everywhere else**, rather than repeating
  the raw nested expression at each site, is additional (smaller) mitigation in the same spirit —
  every re-occurrence of the raw text is a fresh, non-cached elaboration.

This is a **genuinely new obstacle class**, not previously seen at the `K → K_1` or `K_1 → K_2`
steps: prior passes' "Application type mismatch" diamonds (`§62` Obstacle 2, and the first obstacle
above) are outright *rejections*; this one is a goal that **is** provable and **is** accepted, just
only after an elaboration cost that scales badly with how many times the doubly-`baseChangeSplittingField`-nested type is
written out fresh. Whether this generalizes to a `K_4` level (`K_3`-of-`K_3`-of-`baseChangeSplittingField`-of-`K_1`,
compounding the nesting once more) is not tested here — plausibly it makes the corresponding fixes
*more* necessary, not less, but this is not verified.

## Main results

* `K_3.instNontriviallyNormedField` / `.instIsUltrametricDist` / `.instCompleteSpace` /
  `.instNormedSpace` / `.instFiniteDimensional` : forwarded verbatim from `baseChangeSplittingField`'s generic package.
* `K_3.instAlgebraO` : the four-hop composite `Algebra O (K_3 P₃)` — `O → O_{K_1} → O_{K_2} →
  baseChangeSplittingField P₂ → K_3 P₃`, one hop longer than `K_2.instAlgebraO`'s three-hop composite (`O_{K_1} → O_{K_2}`
  inserted). Genuinely new plumbing, though mechanical in shape.
* `K_3.algebraMap_O_eq` : `algebraMap O (K_3 P₃)` really is that four-hop composite — `rfl`.
-/

noncomputable section

open scoped Polynomial

namespace LubinTate

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Algebra O K] [IsFractionRing O K]
variable {P : O[X]} (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X])

/-- **`baseChangeSplittingField P₂`, named once.** Elaborating the doubly-nested `K_3`/`baseChangeSplittingField`-of-`baseChangeSplittingField` type from scratch,
textually, at every site that needs it is prohibitively expensive for the elaborator (see the module
docstring's "elaboration obstacle" section) — `K_3.instAlgebraO`, written with the raw expression
repeated three times, does not terminate within `1_000_000` heartbeats. Binding it once as a named
`abbrev` and referencing the name everywhere else keeps every subsequent occurrence a cheap constant
lookup instead of a fresh re-elaboration. -/
abbrev K2P2 : Type _ := baseChangeSplittingField (K' := K_1 (K := K) P) P₂

/-- **`O_{K_2}`, named once — the *flat* spelling** `↥(integralClosure ↥𝒪[K] (baseChangeSplittingField P₂))`, integral
closure directly over the tower's base `↥𝒪[K]` rather than over the intermediate `O_{K_1}`. This
replaces the nested spelling `↥(integralClosure ↥(integralClosure ↥𝒪[K] (K_1 P)) (K2P2 P₂))` used
through `ROADMAP.md §72` (see `ROADMAP.md §73` for the full account of why, and of the elaboration
obstacle this switch previously hit). The `letI := K_2.instAlgebraK …` inside the `abbrev` body
supplies `Algebra K (K2P2 P₂)`, from which Mathlib's `Algebra.ofSubsemiring` instance derives
`Algebra ↥𝒪[K] (K2P2 P₂)` automatically — the same `Algebra.ofSubsemiring` route
`isScalarTower_R_K_1_K_2` (`Langlands/LubinTateTowerStepConcreteK2.lean`) already uses successfully
one level down, now applied to a *concrete* `letI`-bound instance rather than an ambient
`variable`-introduced hypothesis (the latter is what made the analogous switch time out at
`200,000` heartbeats — see `ROADMAP.md §73`). -/
abbrev O_K2 : Type _ :=
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K2P2 (K := K) P₂))

variable (P₃ : (O_K2 (K := K) P₂)[X])

/-! ## The generic `spectralNorm` package, forwarded from `baseChangeSplittingField` -/

instance K_3.instNontriviallyNormedField :
    NontriviallyNormedField (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) :=
  inferInstance

instance K_3.instIsUltrametricDist :
    IsUltrametricDist (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) :=
  inferInstance

instance K_3.instCompleteSpace :
    CompleteSpace (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) :=
  inferInstance

instance K_3.instNormedSpace :
    NormedSpace (K2P2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) :=
  inferInstance

instance K_3.instFiniteDimensional :
    FiniteDimensional (K2P2 (K := K) P₂) (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃) :=
  inferInstance

/-! ## `Algebra O (K_3 P₃)`, the four-hop composite -/

/-- **`Algebra O (K_3 P₃)`**, built as the explicit four-hop composite `O →(toValuationSubring hOK)→
↥𝒪[K] →(algebraMap, the subalgebra inclusion)→ O_{K_2} →(algebraMap, the subalgebra inclusion)→
baseChangeSplittingField P₂ →(algebraMap)→ K_3 P₃` — not via whatever `Algebra O_{K_2} (K_3 P₃)` instance ordinary
instance search manufactures directly for `LubinTate.K_3`'s underlying `Polynomial.SplittingField`
(that instance is not defeq to this composite, so cannot be used to prove norm transport by `rw`).
Mirrors `K_2.instAlgebraO`, one hop longer. This choice makes `K_3.algebraMap_O_eq` `rfl`.

**The middle hop changed relative to the nested-spelling version**: the *flat* `O_{K_2} :=
↥(integralClosure ↥𝒪[K] (baseChangeSplittingField P₂))` has no `Algebra O_{K_1} (O_{K_2})` structure at all (unlike the
nested spelling, where `O_{K_2}` is itself an `integralClosure` over `O_{K_1}`), so the composite
goes `O → ↥𝒪[K] → O_{K_2}` directly (`toValuationSubring hOK` then the `O_{K_2}` subalgebra
inclusion) rather than through `towerHom hOK P : O →+* O_{K_1}`. The `letI := K_2.instAlgebraK …`
activates the same `Algebra K (baseChangeSplittingField P₂)` instance `O_{K_2}`'s own `abbrev` body used internally, so
that `algebraMap ↥𝒪[K] (O_{K_2} P₂)`/`algebraMap (O_{K_2} P₂) (baseChangeSplittingField P₂)` resolve against the matching
`Subalgebra`-derived instance (`ROADMAP.md §73`). -/
-- **No explicit return-type ascription here, deliberately** — see the module docstring's
-- "elaboration obstacle" section. Ascribing `Algebra O (K_3 (O' := ...) (K' := ...) P₃)` directly
-- propagates that expected type into elaboration of every inner `algebraMap`/`.comp` step, which
-- does not terminate within `1_000_000` heartbeats. Letting Lean infer the type (`Algebra O
-- (baseChangeSplittingField (K' := K2P2 P₂) P₃)`, defeq to but not syntactically `Algebra O (K_3 ...)`) is fast; the
-- defeq check against `K_3`'s spelling happens only once, cheaply, at each *use* site (confirmed
-- directly: `K_3.instAlgebraO ... hOK : Algebra O (K_3 (O' := ...) (K' := ...) P₃)` type-checks in
-- under three seconds).
@[reducible] noncomputable def K_3.instAlgebraO (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :=
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  ((algebraMap (K2P2 (K := K) P₂)
    (baseChangeSplittingField (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)).comp
    ((algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)).comp
      ((algebraMap ↥(ValuativeRel.valuation K).valuationSubring
        (O_K2 (K := K) P₂)).comp
        (toValuationSubring (K := K) hOK)))).toAlgebra

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K]
  [CompleteSpace K] [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] in
/-- **`algebraMap O (K_3 P₃)` really is the four-hop composite** — true by definition of
`K_3.instAlgebraO`, recorded so downstream proofs can rewrite along it. -/
theorem K_3.algebraMap_O_eq (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := K_3.instAlgebraO (K := K) (P := P) P₂ P₃ hOK
    ⇑(algebraMap O (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) =
      ⇑(algebraMap (K2P2 (K := K) P₂)
        (K_3 (O' := O_K2 (K := K) P₂) (K' := K2P2 (K := K) P₂) P₃)) ∘
        ⇑(algebraMap (O_K2 (K := K) P₂) (K2P2 (K := K) P₂)) ∘
        ⇑(algebraMap ↥(ValuativeRel.valuation K).valuationSubring
          (O_K2 (K := K) P₂)) ∘
        ⇑(toValuationSubring (K := K) hOK) := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  rfl

end LubinTate

end
