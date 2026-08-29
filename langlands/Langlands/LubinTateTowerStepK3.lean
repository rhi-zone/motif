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

`O_{K_2}` below is the *flat* spelling `↥(integralClosure ↥𝒪[K] (baseChangeSplittingField P₂))` — integral closure
directly over the tower's base `↥𝒪[K]`, not over the intermediate `O_{K_1}`.

## Mechanical vs. new content

`Langlands/LubinTateTowerStepSplittingField.lean`'s `NormExtension` section is already generic in
its own free parameters `O'`/`K'`, so it is reusable verbatim at this next tower step: since
`K_3 P₃ := baseChangeSplittingField (K' := K') P₃` (`LubinTateTowerStepConcreteK3.lean`) unfolds definitionally to `baseChangeSplittingField`'s
own construction, `baseChangeSplittingField.instNontriviallyNormedField`/`.instIsUltrametricDist`/`.instCompleteSpace`/
`.instNormedSpace`, applied at `O' := O_{K_2}`, `K' := baseChangeSplittingField P₂`, solve for `K_3` verbatim — the only
prerequisite is `Algebra O_{K_2} (baseChangeSplittingField P₂)`, which resolves by ordinary instance search:
`O_{K_2}` is a genuine `Subalgebra`-coerced type of `baseChangeSplittingField P₂`, so Mathlib's generic
`Subalgebra.instSMulSubtypeMem`-derived `Algebra` instance supplies it automatically. This half is
mechanical, modulo the elaboration caveats below.

## Elaboration caveat: `baseChangeSplittingField` applied to a `baseChangeSplittingField`-nested `K'`

Writing a goal or instance whose stated type is `baseChangeSplittingField (K' := baseChangeSplittingField (K' := K_1 P) P₂) P₃`
— i.e. `baseChangeSplittingField` (or `K_3`, defined in terms of it) applied at a base field `K'` that is *itself* a
`baseChangeSplittingField` application, rather than a `K_1`-application as at the `K_1 → K_2` step — fails with
"Application type mismatch" if `O'` is left implicit or given as `_`: the elaborator never unifies `O'`
with `P₃`'s actual ring before checking the application, leaving a bare metavariable and rejecting
`P₃`. Supplying `O'` **explicitly by name** (`baseChangeSplittingField (O' := ...) (K' := ...) P₃`), rather than
leaving it for unification, avoids the stuck metavariable entirely. Every declaration below that
mentions `K_3 (... ) P₃` therefore gives `O'` explicitly.

## Elaboration caveat: cost, not just rejection

Even once `O'` is named, checking an *explicit proof term* against a stated goal mentioning
`K_3 (O' := ...) (K' := ...) P₃` is prohibitively **slow**: a single `instance` built as
`baseChangeSplittingField.instNontriviallyNormedField P₃ : NontriviallyNormedField (K_3 ...)` (rather than closed by
`inferInstance`) exceeds `1_000_000` heartbeats without finishing. Two mitigations are used here:

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
  site — is itself fast.
* **Naming `O_{K_2}`/`baseChangeSplittingField P₂` once via `abbrev`, referenced everywhere else**, rather than repeating
  the raw nested expression at each site, is additional (smaller) mitigation in the same spirit —
  every re-occurrence of the raw text is a fresh, non-cached elaboration.

The first caveat above is an outright *rejection*; this one is a goal that **is** provable and **is**
accepted, just only after an elaboration cost that scales badly with how many times the doubly-nested
type is written out fresh. Whether this generalizes to a `K_4` level (compounding the nesting once
more) is untested.

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
docstring's elaboration-caveat sections) — `K_3.instAlgebraO`, written with the raw expression
repeated three times, does not terminate within `1_000_000` heartbeats. Binding it once as a named
`abbrev` and referencing the name everywhere else keeps every subsequent occurrence a cheap constant
lookup instead of a fresh re-elaboration. -/
abbrev K2P2 : Type _ := baseChangeSplittingField (K' := K_1 (K := K) P) P₂

/-- **`O_{K_2}`, named once — the *flat* spelling** `↥(integralClosure ↥𝒪[K] (baseChangeSplittingField P₂))`, integral
closure directly over the tower's base `↥𝒪[K]` rather than over the intermediate `O_{K_1}` (the
nested spelling `↥(integralClosure ↥(integralClosure ↥𝒪[K] (K_1 P)) (K2P2 P₂))`). The `letI :=
K_2.instAlgebraK …` inside the `abbrev` body supplies `Algebra K (K2P2 P₂)`, from which Mathlib's
`Algebra.ofSubsemiring` instance derives `Algebra ↥𝒪[K] (K2P2 P₂)` automatically — the same
`Algebra.ofSubsemiring` route `isScalarTower_R_K_1_K_2` (`Langlands/LubinTateTowerStepConcreteK2.lean`) already
uses successfully one level down, now applied to a *concrete* `letI`-bound instance rather than an
ambient `variable`-introduced hypothesis. Using the ambient-hypothesis form instead times out at
`200,000` heartbeats; the concrete `letI`-bound form does not. -/
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

**The middle hop**: the *flat* `O_{K_2} := ↥(integralClosure ↥𝒪[K] (baseChangeSplittingField P₂))` has no
`Algebra O_{K_1} (O_{K_2})` structure at all (unlike the nested spelling, where `O_{K_2}` is itself an
`integralClosure` over `O_{K_1}`), so the composite goes `O → ↥𝒪[K] → O_{K_2}` directly (`toValuationSubring hOK`
then the `O_{K_2}` subalgebra inclusion) rather than through `towerHom hOK P : O →+* O_{K_1}`. The
`letI := K_2.instAlgebraK …` activates the same `Algebra K (baseChangeSplittingField P₂)` instance `O_{K_2}`'s own
`abbrev` body used internally, so that `algebraMap ↥𝒪[K] (O_{K_2} P₂)`/`algebraMap (O_{K_2} P₂) (baseChangeSplittingField P₂)`
resolve against the matching `Subalgebra`-derived instance. -/
-- No explicit return-type ascription here, deliberately (see the module docstring's
-- elaboration-caveat sections). Ascribing `Algebra O (K_3 (O' := ...) (K' := ...) P₃)` directly
-- propagates that expected type into elaboration of every inner `algebraMap`/`.comp` step, which
-- does not terminate within `1_000_000` heartbeats. Letting Lean infer the type (`Algebra O
-- (baseChangeSplittingField (K' := K2P2 P₂) P₃)`, defeq to but not syntactically `Algebra O (K_3 ...)`) is fast; the
-- defeq check against `K_3`'s spelling happens only once, cheaply, at each *use* site.
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
