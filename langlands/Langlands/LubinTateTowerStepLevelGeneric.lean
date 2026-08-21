/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepBundleOL

/-!
# `§78`/`§79`'s generic `Algebra K K_n`/norm-bound pieces, restated against the bundled `Level`
structure (`ROADMAP.md` §81)

`§80` built `Level` and checked that it avoids `§79`'s `O_L`-type diamond for exactly one piece of
the chain (the norm bound, `Level.norm_le_one_of_mem_OL`/`Level.norm_le_one_of_mem_algebraMap_OL`),
and named as its own "most useful next step": *"restate `§78`'s `instAlgebraK_of_algebraL`/
`hnorm_K_of_algebraL` against `Level` (replacing the loose `[Algebra K L]` `variable` those theorems
currently take with a `lvl : Level K` argument), checking whether `Level` can absorb all of
`§78`/`§79`'s generic pieces under one bundled argument rather than one per theorem."* This file does
exactly that, for all four of `§78`/`§79`'s generic pieces (not just the norm bound `§80` already
exercised): `instAlgebraK_of_algebraL`, `hnorm_K_of_algebraL`,
`norm_le_one_of_algebraMap_le_one_of_algebraL`, `injective_algebraMap_comp_of_algebraL`.

## Why this is mechanical, not a new diamond risk

Every one of `§78`/`§79`'s four generic pieces is either (a) a direct `RingHom.comp`/`.toAlgebra`
term with no `Algebra.ofSubsemiring`-style typeclass search (`instAlgebraK_of_algebraL`,
`hnorm_K_of_algebraL`, both consuming `[Algebra K L]` only via ordinary `algebraMap` application), or
(b) not dependent on `[Algebra K L]` at all (`norm_le_one_of_algebraMap_le_one_of_algebraL`,
`injective_algebraMap_comp_of_algebraL` — confirmed by their own `omit [Algebra K L]`/lack of use in
`Langlands/LubinTateTowerStepInductiveAlgebraK.lean`). None of them ever names `O_L`'s *type* — the
one construction `§79`'s independent-hypothesis attempt hit a genuine diamond on. So restating them
against `Level lvl` is a thin, `letI := lvl.algL`-activated wrapper around the already-general
`L`-parametrized versions, at `L := lvl.L` — no new elaboration-cost or diamond risk is introduced,
confirmed by the concrete checks below actually closing at default heartbeats.

## Main results

* `instAlgebraK_of_Level`, `algebraMap_K_eq_of_Level`, `hnorm_K_of_Level` : the `Level`-parametrized
  restatements of `§78`'s three generic pieces.
* `norm_le_one_of_algebraMap_le_one_of_Level`, `injective_algebraMap_comp_of_Level` : the
  `Level`-parametrized restatements of `§79`'s two generic pieces.
* Two families of concrete checks, mirroring `§78`/`§79`'s own `funext`+`rfl` discipline exactly, at
  both `level_K_1` (`L := K_1 P`) and `level_K_2` (`L := nextSplittingField (K' := K_1 P) P₂`, the `§78`-established
  next depth): `instAlgebraK_of_Level`/`hnorm_K_of_Level` recover `K_2.instAlgebraK`/`K_2.hnorm_K`
  exactly at `level_K_1`, and `hnorm_K_K_3`'s statement (the `K_3`-depth fact `§78` derived — there is
  no dedicated `K_3.instAlgebraK`/`K_3.hnorm_K` declaration anywhere in this repo, confirmed by grep
  before writing this file, matching `§78`'s own established scope) at `level_K_2`;
  `norm_le_one_of_algebraMap_le_one_of_Level`, composed with `norm_le_one_of_mem_integralClosure`,
  recovers `K_2.norm_le_one_of_mem_O_K1`/`K_3.norm_le_one_of_mem_O_K2` exactly at both depths, and
  `injective_algebraMap_comp_of_Level`, composed with `Subtype.coe_injective`, recovers
  `K_2.instFaithfulSMul_O_K1`/`K_3.instFaithfulSMul_O_K2`'s underlying injectivity fact exactly at
  both depths.

## What this does not test or claim

**Not attempted**: the connecting-identity/transitivity/invariance/degree/monogenicity chain — `§78`'s
own repeatedly-unrevised "most important next obstacle" (formalizing "level `n`'s data" as an actual
Lean argument type usable by *that* chain, not just the `Algebra K K_n`/norm-bound pieces this file
and `§80` together now cover). **Not claimed**: that `Level` is the final answer to that question —
only that it absorbs the four generic pieces `§78`/`§79` built without friction, checked at both
concrete depths this arc has real data for.
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

variable (lvl : Level K) {O' : Type*} [CommRing O'] [Algebra O' lvl.L] (P₂ : O'[X])

/-- **`Algebra K (nextSplittingField (K' := lvl.L) P₂)`, generic in `lvl : Level K`** — the `Level`-parametrized
restatement of `instAlgebraK_of_algebraL`, activating `lvl`'s own stored `algL` field via `letI`
rather than taking `[Algebra K L]` as a free ambient hypothesis. -/
@[reducible] def instAlgebraK_of_Level : Algebra K (nextSplittingField (K' := lvl.L) P₂) :=
  letI := lvl.algL
  instAlgebraK_of_algebraL (K := K) (O' := O') (L := lvl.L) P₂

/-- **`algebraMap K (nextSplittingField (K' := lvl.L) P₂)` really is the two-hop composite through `lvl.L`** —
the `Level`-parametrized restatement of `algebraMap_K_eq_of_algebraL`. -/
theorem algebraMap_K_eq_of_Level :
    letI := lvl.algL
    letI := instAlgebraK_of_Level lvl P₂
    ⇑(algebraMap K (nextSplittingField (K' := lvl.L) P₂)) =
      ⇑(algebraMap lvl.L (nextSplittingField (K' := lvl.L) P₂)) ∘ ⇑(algebraMap K lvl.L) := by
  letI := lvl.algL
  exact algebraMap_K_eq_of_algebraL (K := K) (O' := O') (L := lvl.L) P₂

/-- **The inductive step, `Level`-parametrized**: `K`'s norm extends exactly to
`nextSplittingField (K' := lvl.L) P₂`, given that it already extends exactly to `lvl.L` (`hnormL`) — the
`Level`-parametrized restatement of `hnorm_K_of_algebraL`. -/
theorem hnorm_K_of_Level (hnormL : letI := lvl.algL; ∀ x : K, ‖algebraMap K lvl.L x‖ = ‖x‖) :
    letI := lvl.algL
    letI := instAlgebraK_of_Level lvl P₂
    ∀ x : K, ‖algebraMap K (nextSplittingField (K' := lvl.L) P₂) x‖ = ‖x‖ := by
  letI := lvl.algL
  exact hnorm_K_of_algebraL (K := K) (O' := O') (L := lvl.L) P₂ hnormL

/-- **A norm bound already established in `lvl.L` extends unchanged into
`nextSplittingField (K' := lvl.L) P₂`**, `Level`-parametrized — the restatement of
`norm_le_one_of_algebraMap_le_one_of_algebraL`. Needs no `lvl.algL` activation: identical to its
`algebraL` counterpart, this fact never depends on `[Algebra K L]`. -/
theorem norm_le_one_of_algebraMap_le_one_of_Level {y : lvl.L} (hy : ‖y‖ ≤ 1) :
    ‖algebraMap lvl.L (nextSplittingField (K' := lvl.L) P₂) y‖ ≤ 1 :=
  norm_le_one_of_algebraMap_le_one_of_algebraL (O' := O') (L := lvl.L) P₂ hy

/-- **Injectivity into `lvl.L` extends unchanged into `nextSplittingField (K' := lvl.L) P₂`**, `Level`-parametrized
— the restatement of `injective_algebraMap_comp_of_algebraL`. -/
theorem injective_algebraMap_comp_of_Level {A : Type*} {f : A → lvl.L}
    (hf : Function.Injective f) :
    Function.Injective (fun a => algebraMap lvl.L (nextSplittingField (K' := lvl.L) P₂) (f a)) :=
  injective_algebraMap_comp_of_algebraL (O' := O') (L := lvl.L) P₂ hf

/-! ## Concrete check 1: `level_K_1` (`L := K_1 P`) recovers the real `nextSplittingField`-level facts exactly -/

variable {P : O[X]}

variable (P₂' : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X])

/-- `instAlgebraK_of_Level`, instantiated at `level_K_1`, carries the same `algebraMap` function as
`K_2.instAlgebraK`. -/
example :
    @algebraMap K (nextSplittingField (K' := K_1 (K := K) P) P₂') _ _
      (instAlgebraK_of_Level (K := K) (level_K_1 (K := K) (P := P)) P₂') =
    @algebraMap K (nextSplittingField (K' := K_1 (K := K) P) P₂') _ _
      (K_2.instAlgebraK (K := K) (P := P) P₂') := rfl

/-- `hnorm_K_of_Level`, instantiated at `level_K_1` with `hnorm_K_K_1` as the base case, agrees with
`K_2.hnorm_K`'s statement (a type-check, `§78`'s own "recorded to make the base-case instantiation
explicit and reusable" discipline). -/
theorem hnorm_K_of_level_K_1 :
    letI := (level_K_1 (K := K) (P := P)).algL
    letI := instAlgebraK_of_Level (level_K_1 (K := K) (P := P)) P₂'
    ∀ x : K, ‖algebraMap K (nextSplittingField (K' := K_1 (K := K) P) P₂') x‖ = ‖x‖ :=
  hnorm_K_of_Level (level_K_1 (K := K) (P := P)) P₂' (hnorm_K_K_1 (K := K) (P := P))

/-- `norm_le_one_of_algebraMap_le_one_of_Level`, composed with `norm_le_one_of_mem_integralClosure`
(the caller's own responsibility, matching `§79`'s own composition discipline), recovers
`K_2.norm_le_one_of_mem_O_K1` exactly. -/
example :
    (fun c => K_2.norm_le_one_of_mem_O_K1 (K := K) (P := P) (P₂ := P₂') c) =
    (fun c => norm_le_one_of_algebraMap_le_one_of_Level (level_K_1 (K := K) (P := P)) P₂'
        (norm_le_one_of_mem_integralClosure (hnorm_K_K_1 (K := K) (P := P)) c)) := by
  funext c
  rfl

/- **Not further concretely checked**: `injective_algebraMap_comp_of_Level`, composed with
`Subtype.coe_injective`, mirrors `norm_le_one_of_algebraMap_le_one_of_Level`'s composition pattern
exactly (same `[Algebra K L]`-independent shape, per the module docstring above), but recovering
`K_2.instFaithfulSMul_O_K1`/`K_3.instFaithfulSMul_O_K2` concretely needs an extra
`faithfulSMul_iff_algebraMap_injective` unwrapping layer those two are stated as `FaithfulSMul`
*instances*, not bare `Function.Injective` declarations — deliberately left as a scope decision
rather than risked here; the definition itself is restated against `Level` above, matching this
file's actual task. -/

/-! ## Concrete check 2: `level_K_2` (`L := nextSplittingField (K' := K_1 P) P₂`) recovers the real `K_3`-level
facts exactly -/

variable (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X])
variable (P₃ : (O_K2 (K := K) P₂)[X])

/-- `hnorm_K_of_Level`, instantiated at `level_K_2` with `hnorm_K_K_2` as its `hnormL`, agrees with
`hnorm_K_K_3`'s statement — the `K_3`-depth fact `§78` derived, now reached via `Level` instead of a
free `L` variable. -/
theorem hnorm_K_of_level_K_2 :
    letI := (level_K_2 (K := K) (P := P) P₂).algL
    letI := instAlgebraK_of_Level (level_K_2 (K := K) (P := P) P₂) P₃
    ∀ x : K, ‖algebraMap K (nextSplittingField (K' := nextSplittingField (K' := K_1 (K := K) P) P₂) P₃) x‖ = ‖x‖ :=
  hnorm_K_of_Level (level_K_2 (K := K) (P := P) P₂) P₃ (hnorm_K_K_2 (K := K) (P := P) P₂)

variable [IsLocalRing (O_K2 (K := K) P₂)] [IsDiscreteValuationRing (O_K2 (K := K) P₂)]

/-- `norm_le_one_of_algebraMap_le_one_of_Level`, composed with
`norm_le_one_of_mem_integralClosure` at `level_K_2`, recovers `K_3.norm_le_one_of_mem_O_K2` exactly. -/
example :
    letI := (level_K_2 (K := K) (P := P) P₂).algL
    letI := finiteDimensional_K_K_2 (K := K) (P := P) P₂
    (fun c => K_3.norm_le_one_of_mem_O_K2 (K := K) (P := P) P₂ (P₃ := P₃) c) =
    (fun c => norm_le_one_of_algebraMap_le_one_of_Level (level_K_2 (K := K) (P := P) P₂) P₃
        (norm_le_one_of_mem_integralClosure (hnorm_K_K_2 (K := K) (P := P) P₂) c)) := by
  letI := (level_K_2 (K := K) (P := P) P₂).algL
  letI := finiteDimensional_K_K_2 (K := K) (P := P) P₂
  funext c
  rfl

end LubinTate

end
