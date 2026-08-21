/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepInductiveAlgebraK
import Langlands.LubinTateTowerStepRootConnect
import Langlands.LubinTateTowerStepK3RootConnect

/-!
# Bundling `L`'s data avoids `§79`'s `O_L`-type diamond, checked directly (`ROADMAP.md` §80)

`§79` found that stating a generic lemma directly about elements of `↥(integralClosure ↥𝒪[K] L)`
(`O_L`'s type itself, for an abstract intermediate field `L`) hits a genuine instance diamond: taking
`[Algebra ↥𝒪[K] L]` as an *independent* ambient hypothesis, parallel to but separate from
`[Algebra K L]`, produces a term that does not unify with `norm_le_one_of_mem_integralClosure`'s own
internally-`Algebra.ofSubsemiring`-derived instance of the same class — two different, non-defeq
witnesses of the same `Prop`-level fact.

This file tests a genuinely different encoding — bundling `L` and its `[Algebra K L]` instance as
data in a `structure`, with `O_L`'s type defined as a `def` that derives `Algebra ↥𝒪[K] L` via
ordinary typeclass search from *that same stored field* (never as a second, independently-supplied
hypothesis) — and finds, checked directly by an actual clean build (not asserted), that **this
avoids the diamond**: `norm_le_one_of_mem_integralClosure` applies to an element of the bundled
`Level.OL` with no cast, no bridge, no workaround.

## Why this works where `§79`'s attempt did not

Traced directly (`set_option trace.Meta.synthInstance true` against a minimal repro, this pass):
typeclass search resolves `Algebra ↥𝒪[K] L` from an ambient `[Algebra K L]` to
`Algebra.ofSubsemiring (ValuativeRel.valuation K).valuationSubring ‹Algebra K L›` — i.e. the
resolved term is a genuine *function* of whichever `[Algebra K L]` term is in local scope, not a
fixed constant baked in once. `§79`'s attempt supplied `Algebra ↥𝒪[K] L` as an **independent**
hypothesis — a fresh, opaque local variable structurally unrelated to `[Algebra K L]` — so of course
it disagreed with the lemma's own re-derivation. This file's `Level.OL` instead lets ordinary
typeclass search derive `Algebra ↥𝒪[K] lvl.L` from `lvl.algL` (the structure's *own* stored
`[Algebra K L]` field, activated via `letI`) at the point `Level.OL` is defined, and every downstream
use activates the *same* `lvl.algL` via `letI` before calling `norm_le_one_of_mem_integralClosure` —
so both routes resolve to the literally same `Algebra.ofSubsemiring _ lvl.algL` term. No independent
second hypothesis for `O_L`'s type is ever introduced; the diamond `§79` hit structurally cannot arise
here.

**A genuinely new mechanical requirement surfaced by this test, not previously needed**: both the
`Level` structure and every concrete `Level` value built from it must be marked `@[reducible]`
(matching `§78`'s own finding for its `structure`-bundling scratch experiment) — without this,
typeclass search for `Algebra lvl.OL lvl.L` (needed by the combined bound below, via Mathlib's
`IsScalarTower.subalgebra'`) fails to unfold `lvl.OL`'s definition far enough to recognize it as a
`Subalgebra`, even though the *type* elaborates fine either way. Confirmed directly: the concrete
`level_K_1`/`level_K_2` `def`s below failed to typecheck the `.OL` non-vacuity `example` until marked
`@[reducible]`, with no other change.

## What this does not test or claim

**Not tested**: whether this pattern scales past one level of bundling (e.g. a `Level` whose `L`
field is itself built from a previous `Level`, recursively) — every concrete check below builds `L`
directly from the existing concrete tower constructions (`K_1 P`, `nextSplittingField (K' := K_1 P) P₂`), not from a
chain of `Level` values. **Not claimed**: that this closes any part of `§79`'s "what remains" list
(the connecting-identity/transitivity/degree/monogenicity chain) — only the norm-bound piece `§79`
itself already generalized (in two composed pieces) is re-derived here in one bundled step, checked
against the same two concrete depths `§79` used.

## Main results

* `Level` : bundles `L`, `[NontriviallyNormedField L]`/`[IsUltrametricDist L]`/`[CompleteSpace L]`,
  and `algL : Algebra K L` stored as a plain field (never tagged `instance`, so there is exactly one
  term for it in any given `Level` value, reached only by projection).
* `Level.OL` : `O_L`, defined via ordinary typeclass search from `lvl.algL` (never an independent
  hypothesis) — `@[reducible]`.
* `Level.norm_le_one_of_mem_OL` : `O_L`'s elements have norm `≤ 1` in `L` itself, given `L`'s own norm
  bound from `K` — direct application of `norm_le_one_of_mem_integralClosure` to `lvl.OL`'s elements,
  the exact thing `§79` found could not be stated generically against an independent `O_L` hypothesis.
* `Level.norm_le_one_of_mem_algebraMap_OL` : the combined bound, `O_L`-membership directly to a norm
  bound in `nextSplittingField (K' := lvl.L) P₂` (one hop further) — folds `§79`'s two separately-composed pieces
  (`norm_le_one_of_mem_integralClosure` + `norm_le_one_of_algebraMap_le_one_of_algebraL`) into one
  lemma taking `O_L`-membership as its hypothesis, not requiring the caller to invoke the first piece
  themselves.
* Two `example`s (`level_K_1`/`level_K_2`, `L := K_1 P` and `L := nextSplittingField (K' := K_1 P) P₂`): the bundled
  combined lemma, instantiated at each, is checked by `funext`+`rfl` to be *literally*
  `K_2.norm_le_one_of_mem_O_K1` / `K_3.norm_le_one_of_mem_O_K2` — not merely an equivalent
  restatement, the same discipline `§79` used for its own non-vacuity checks.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [Finite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).valuationSubring)]
  [Algebra O K] [IsFractionRing O K]

/-- **Bundled level data**: a field `L`, its normed-field/completeness structure, and
`algL : Algebra K L` stored as a plain field — deliberately *not* tagged `instance`, so there is
exactly one term for it per `Level` value, reached only by projection, never independently
re-derived by a second call site. -/
structure Level (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
    [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
    [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] where
  L : Type*
  [instNormedField : NontriviallyNormedField L]
  [instUltra : IsUltrametricDist L]
  [instComplete : CompleteSpace L]
  algL : Algebra K L
  finiteDim : @FiniteDimensional K L _ _ (@Algebra.toModule K L _ _ algL)

attribute [instance] Level.instNormedField Level.instUltra Level.instComplete

variable (lvl : Level K)

/-- **`O_L`, derived from the structure's own stored `algL` via ordinary typeclass search** — the
single elaborated term this whole file's finding hinges on: never an independent hypothesis, always
a function of `lvl.algL`. `@[reducible]`, per this file's module docstring. -/
@[reducible] def Level.OL (lvl : Level K) : Type _ :=
  letI := lvl.algL
  ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring lvl.L)

/-- **`O_L`'s elements have norm `≤ 1` in `L` itself**, given `L`'s own norm bound from `K`. Direct
application of `norm_le_one_of_mem_integralClosure` to an element of `lvl.OL` — the thing `§79`'s
independent-ambient-hypothesis attempt could not do generically. -/
theorem Level.norm_le_one_of_mem_OL :
    letI := lvl.algL
    ∀ (hnormL : ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖) (y : lvl.OL), ‖(y : lvl.L)‖ ≤ 1 := by
  letI := lvl.algL
  letI := lvl.finiteDim
  intro hnormL y
  exact norm_le_one_of_mem_integralClosure hnormL y

variable {O' : Type*} [CommRing O']

/-- **The combined bound**: `O_L`-membership directly to a norm bound in `nextSplittingField (K' := lvl.L) P₂`
(one hop further), generic in `lvl : Level K`. Folds `§79`'s two separately-composed pieces
(`norm_le_one_of_mem_integralClosure` + `norm_le_one_of_algebraMap_le_one_of_algebraL`) into one
lemma taking `O_L`-membership as its hypothesis. -/
theorem Level.norm_le_one_of_mem_algebraMap_OL [Algebra O' lvl.L] (P₂ : O'[X]) :
    letI := lvl.algL
    letI algOL : Algebra lvl.OL (nextSplittingField (K' := lvl.L) P₂) :=
      ((algebraMap lvl.L (nextSplittingField (K' := lvl.L) P₂)).comp
        (algebraMap lvl.OL lvl.L)).toAlgebra
    ∀ (hnormL : ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖) (c : lvl.OL),
      ‖algebraMap lvl.OL (nextSplittingField (K' := lvl.L) P₂) c‖ ≤ 1 := by
  letI := lvl.algL
  letI := lvl.finiteDim
  letI algOL : Algebra lvl.OL (nextSplittingField (K' := lvl.L) P₂) :=
    ((algebraMap lvl.L (nextSplittingField (K' := lvl.L) P₂)).comp
      (algebraMap lvl.OL lvl.L)).toAlgebra
  intro hnormL c
  have hc : ‖(c : lvl.L)‖ ≤ 1 := norm_le_one_of_mem_integralClosure hnormL c
  have heq : algebraMap lvl.OL (nextSplittingField (K' := lvl.L) P₂) c =
      algebraMap lvl.L (nextSplittingField (K' := lvl.L) P₂) (algebraMap lvl.OL lvl.L c) := rfl
  rw [nextSplittingField.norm_eq_spectralNorm, heq, spectralNorm_extends]
  exact hc

/-! ## Concrete check 1: `L := K_1 P` recovers `K_2.norm_le_one_of_mem_O_K1` exactly -/

variable {P : O[X]}

/-- The concrete `Level` at `L := K_1 P`, from the real, already-registered global
`K_1.instAlgebra`/`K_1.instFiniteDimensional` instances — never an independently-supplied
hypothesis. `@[reducible]`, needed for the non-vacuity checks below (this file's module docstring). -/
@[reducible] def level_K_1 : Level K where
  L := K_1 (K := K) P
  algL := K_1.instAlgebra P
  finiteDim := K_1.instFiniteDimensional P

/-- `(level_K_1).OL` really is the already-used flat `O_{K_1}` type. -/
example : (level_K_1 (K := K) (P := P)).OL =
    ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)) := rfl

variable (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X])

/-- **The bundled combined lemma, instantiated at `level_K_1`, is literally
`K_2.norm_le_one_of_mem_O_K1`** — checked by `funext`+`rfl`, the same discipline `§79` used for its
own non-vacuity checks. -/
example :
    letI := (level_K_1 (K := K) (P := P)).algL
    (fun c => (level_K_1 (K := K) (P := P)).norm_le_one_of_mem_algebraMap_OL P₂
        (fun x => by rw [K_1.norm_eq_spectralNorm, spectralNorm_extends]) c) =
    (fun c => K_2.norm_le_one_of_mem_O_K1 (K := K) (P := P) (P₂ := P₂) c) := by
  letI := (level_K_1 (K := K) (P := P)).algL
  funext c
  rfl

/-! ## Concrete check 2: `L := nextSplittingField (K' := K_1 P) P₂` recovers `K_3.norm_le_one_of_mem_O_K2` exactly -/

/-- The concrete `Level` at `L := nextSplittingField (K' := K_1 P) P₂`, from `§78`'s own composite
`K_2.instAlgebraK`/`finiteDimensional_K_K_2` — again never an independently-supplied hypothesis. -/
@[reducible] def level_K_2 : Level K where
  L := nextSplittingField (K' := K_1 (K := K) P) P₂
  algL := K_2.instAlgebraK (K := K) (P := P) P₂
  finiteDim := finiteDimensional_K_K_2 (K := K) (P := P) P₂

/-- `(level_K_2).OL` really is the already-used flat `O_{K_2}` type. -/
example :
    letI := (level_K_2 (K := K) (P := P) P₂).algL
    (level_K_2 (K := K) (P := P) P₂).OL =
    ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
      (nextSplittingField (K' := K_1 (K := K) P) P₂)) := by
  letI := (level_K_2 (K := K) (P := P) P₂).algL
  rfl

variable (P₃ : (O_K2 (K := K) P₂)[X])
  [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]

/-- **The bundled combined lemma, instantiated at `level_K_2`, is literally
`K_3.norm_le_one_of_mem_O_K2`** — checked by `funext`+`rfl`. -/
example :
    letI := (level_K_2 (K := K) (P := P) P₂).algL
    (fun c => (level_K_2 (K := K) (P := P) P₂).norm_le_one_of_mem_algebraMap_OL
        (O' := O_K2 (K := K) P₂) P₃ (hnorm_K_K_2 (K := K) (P := P) P₂) c) =
    (fun c => K_3.norm_le_one_of_mem_O_K2 (K := K) (P := P) P₂ (P₃ := P₃) c) := by
  letI := (level_K_2 (K := K) (P := P) P₂).algL
  funext c
  rfl

end LubinTate

end
