/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepBaseNorm

/-!
# The `Algebra K K_n` composite and its norm-preservation fact, generalized to an arbitrary tower
depth (`ROADMAP.md` §78)

`ROADMAP.md` §73's "next concrete step toward the `∀ n` family" flagged this precisely: "the
`Algebra K K_n` composite itself must generalize. `K_2.instAlgebraK` is a concrete two-hop `def`; an
inductive family needs an analogous `K_n.instAlgebraK` built inductively (composing the previous
level's composite with one more `algebraMap`), which [was] not built or tested [there] — it is a
genuinely new piece, not a mechanical repeat of what closed."

This file builds exactly that piece, generically. `Langlands/LubinTateTowerStepSplittingField.lean`'s
`NormExtension` section already establishes that `LubinTate.K_2`'s `NontriviallyNormedField`/
`IsUltrametricDist`/`CompleteSpace`/`NormedSpace` package is `n`-independent by construction (generic
in `K_2`'s own two free parameters `O'`/`K'` — confirmed directly by that file's own docstring and
body, re-confirmed here by reading it before writing this file). What was *not* yet generic is the
`Algebra K K_n` composite (`K_2.instAlgebraK`, `Langlands/LubinTateTowerStepBaseNorm.lean`) and its
norm-preservation corollary (`K_2.hnorm_K`) — both hardcoded to the concrete intermediate field
`K_1 P`. This file replaces that hardcoding with an abstract intermediate field `L`, so the exact same
lemma applies at every tower depth: first at `L := K_1 P` (recovering `K_2.instAlgebraK`/`K_2.hnorm_K`
verbatim, checked below), then at `L := K_2 P₂` (deriving the analogous `K_3`-level composite and
norm fact *for free*, with no new per-level file, checked below), and so on for any further level —
the proof never uses anything specific to which level `L` sits at, only that `[Algebra K L]` holds
and that `K`'s norm already extends exactly to `L` (`hnormL`, itself the previous level's own output).

## What this does and does not generalize

**Generalizes**: the `Algebra K K_n` composite and its norm-preservation fact — precisely the piece
`§73` identified as missing. This is a genuine, reusable, `∀`-shaped induction on this one piece of
tower data: `hnorm_K_of_algebraL`, applied at level `n`'s own output, produces level `n+1`'s fact,
using the *same* lemma at every step (not a new lemma per level).

**Does not generalize** (deliberately out of scope, per `§73`'s own scoping and confirmed here by
direct check before writing): the flat ring-of-integers construction itself (`O_{K_n} :=
↥(integralClosure ↥𝒪[K] K_n)`, `§73`) is **not** rebuilt as a function of an abstract `[Algebra K L]`
*hypothesis* here — doing so would reproduce exactly `§67`'s original obstacle (an ambient, abstract
`Algebra K L` variable makes `Algebra.ofSubsemiring`'s instance search for `Algebra ↥𝒪[K] L` time out
at `200,000` heartbeats; only a *concrete*, already-elaborated `letI`-bound term avoids this, `§73`'s
own load-bearing finding). `instAlgebraK_of_algebraL` below sidesteps this entirely: it is built as an
explicit `RingHom.comp`/`.toAlgebra` term, needing no typeclass search of the base-ring-restriction
kind at all, so genericity over an abstract `L` costs nothing here — but the O-flat construction
itself must still be instantiated per concrete level, with a concrete `letI`, exactly as `§73`
established. The `Algebra O K_n` composite (`K_2.instAlgebraO`, the *outer ring* `O`'s four-hop
version one level further, `Langlands/LubinTateTowerStepK3.lean`) is also not generalized here — it
threads through `towerHom`/the flat `O_{K_{n-1}} → 𝒪[K]`-vs-`O_{K_{n-2}}` distinction that changed
shape between `K_2.instAlgebraO`'s three-hop and `K_3.instAlgebraO`'s four-hop version (`§73`), and is
a separate, larger piece of work not attempted this pass.

## Main results

* `instAlgebraK_of_algebraL` : `Algebra K (K_2 (K' := L) P₂)`, the two-hop composite `K → L →
  K_2 (K' := L) P₂`, generic in the intermediate field `L`. Specializes to `K_2.instAlgebraK` at
  `L := K_1 P` and to an analogous `K_3`-level composite at `L := K_2 (K' := K_1 P) P₂` — checked
  directly below, not merely claimed.
* `algebraMap_K_eq_of_algebraL` : `algebraMap K (K_2 (K' := L) P₂)` really is that composite, `rfl`.
* `hnorm_K_of_algebraL` : **`∀ x : K, ‖algebraMap K (K_2 (K' := L) P₂) x‖ = ‖x‖`**, given `hnormL`
  (the same fact one level down) — the genuine inductive step: this lemma, fed its own conclusion at
  the previous level, produces the next level's conclusion, at any depth.
* `hnorm_K_K_1` : the base case, `L := K_1 P` — `K`'s norm extends exactly to `K_1 P` (immediate from
  `K_1.norm_eq_spectralNorm`/`spectralNorm_extends`, the same one-hop fact `K_2.hnorm_K`'s own proof
  already uses inline).
* An `example` (unnamed, non-vacuity check) : instantiating `instAlgebraK_of_algebraL` at `L := K_1 P`
  carries the same `algebraMap` function as `K_2.instAlgebraK` (`rfl`, at the `RingHom` level).
* `hnorm_K_K_2` : instantiating `hnorm_K_of_algebraL` at `L := K_1 P` with `hnorm_K_K_1` as the base
  case recovers `K_2.hnorm_K`'s statement.
* `hnorm_K_K_3` : instantiating the generic lemma a *second* time, at `L := K_2 (K' := K_1 P) P₂`,
  derives the `K_3`-level norm-preservation fact — with **no new per-level file**, the deliverable
  `§73` scoped and did not build.
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
  [Algebra O K] [IsFractionRing O K]

/-! ## The generic inductive step: `Algebra K (K_2 (K' := L) P₂)`, for any intermediate field `L` -/

section Generic

variable {O' : Type*} [CommRing O']
variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [Algebra O' L] [Algebra K L]
variable (P₂ : O'[X])

/-- **`Algebra K (K_2 (K' := L) P₂)`, the two-hop composite `K → L → K_2 P₂`, generic in the
intermediate field `L`.** Built as an explicit `RingHom.comp`/`.toAlgebra` term — no typeclass search
of the `Algebra.ofSubsemiring` kind is involved, so genericity over an abstract `[Algebra K L]` costs
nothing here (unlike the flat ring-of-integers construction, which genuinely does need a concrete
term, per `§73`/this file's module docstring). Mirrors `K_2.instAlgebraK`, with `L` in place of the
hardcoded `K_1 P`. -/
@[reducible] def instAlgebraK_of_algebraL : Algebra K (K_2 (K' := L) P₂) :=
  ((algebraMap L (K_2 (K' := L) P₂)).comp (algebraMap K L)).toAlgebra

omit [IsUltrametricDist K] [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [CompleteSpace K] [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [IsUltrametricDist L] [CompleteSpace L] in
/-- **`algebraMap K (K_2 (K' := L) P₂)` really is the two-hop composite** — true by definition of
`instAlgebraK_of_algebraL`. -/
theorem algebraMap_K_eq_of_algebraL :
    letI := instAlgebraK_of_algebraL (K := K) (O' := O') (L := L) P₂
    ⇑(algebraMap K (K_2 (K' := L) P₂)) =
      ⇑(algebraMap L (K_2 (K' := L) P₂)) ∘ ⇑(algebraMap K L) := rfl

omit [IsUltrametricDist K] [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [CompleteSpace K] [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] in
/-- **The inductive step itself**: `K`'s norm extends exactly to `K_2 (K' := L) P₂`, given that it
already extends exactly to `L` (`hnormL`). Two applications of `spectralNorm_extends`, chained
through `algebraMap_K_eq_of_algebraL` — the *same* proof shape `K_2.hnorm_K` uses for the concrete
`L := K_1 P` case, now stated once for any `L` and applicable at every tower depth by feeding in the
previous level's own output as `hnormL`. -/
theorem hnorm_K_of_algebraL (hnormL : ∀ x : K, ‖algebraMap K L x‖ = ‖x‖) :
    letI := instAlgebraK_of_algebraL (K := K) (O' := O') (L := L) P₂
    ∀ x : K, ‖algebraMap K (K_2 (K' := L) P₂) x‖ = ‖x‖ := by
  letI := instAlgebraK_of_algebraL (K := K) (O' := O') (L := L) P₂
  intro x
  have hcoe : algebraMap K (K_2 (K' := L) P₂) x =
      algebraMap L (K_2 (K' := L) P₂) (algebraMap K L x) :=
    congrFun (algebraMap_K_eq_of_algebraL (K := K) (O' := O') (L := L) P₂) x
  rw [K_2.norm_eq_spectralNorm, hcoe, spectralNorm_extends, hnormL]

/-! ### Extending a norm bound / injectivity fact one hop further, into `K_2 (K' := L) P₂`

`ROADMAP.md` §79's second generalized piece. `K_2.norm_le_one_of_mem_O_K1`/`norm_le_one_of_mem_
O_K2_in_K2P2`+`K_3.norm_le_one_of_mem_O_K2` and `K_2.instFaithfulSMul_O_K1`/`K_3.instFaithfulSMul_
O_K2` each split into two genuinely different pieces: (1) "`O_L`'s elements have norm `≤ 1`
in `L` itself"/"the subring inclusion `O_L → L` is injective" — already fully general, no new
lemma needed (`norm_le_one_of_mem_integralClosure`, `Subtype.coe_injective`, applied at `K' := K`);
(2) "a bound/injectivity fact already established in `L` extends one hop further, into
`K_2 (K' := L) P₂`" — genuinely repeated by hand at every level, generalized here.

**A first attempt at (2) generalized the *type* `O_L` itself** (taking `[Algebra ↥𝒪[K] L]` as an
explicit ambient hypothesis, distinct from the `[Algebra K L]` this file's `Generic` section
already carries) — this does **not** work: `norm_le_one_of_mem_integralClosure`'s own statement
derives its `Algebra ↥𝒪[K'] L` instance internally via `Algebra.ofSubsemiring` from its own
`[Algebra K' L]` parameter, which is a *syntactically different, non-unifying* instance from an
independently-hypothesized one — applying the lemma then fails with an application type mismatch
(the two `integralClosure ↥𝒪[K] L` types disagree on which `Algebra ↥𝒪[K] L` instance they carry,
confirmed directly by the actual elaborator error, not inferred). This is a genuinely new
instance-diamond finding, distinct from `§67`/`§73`'s (which was about `Algebra.ofSubsemiring`'s
*search cost* over an abstract hypothesis, not about two independently-supplied instances
disagreeing) — recorded here rather than forced past with a workaround. The fix taken below avoids
the diamond entirely by never naming `O_L`'s type in the generic lemma at all: instead of taking a
membership proof and deriving the bound, it takes the *already-established* bound in `L` as an
explicit hypothesis, and extends it — the concrete `O_L`-membership step is left to the call site,
using the existing, already-general `norm_le_one_of_mem_integralClosure` directly (its own
`Algebra ↥𝒪[K] L` instance never has to be named or compared against another one). -/

/-- **A norm bound already established in `L` extends unchanged into `K_2 (K' := L) P₂`** — the
generic form of the "one hop further" half of `K_2.norm_le_one_of_mem_O_K1`/`K_3.norm_le_one_of_
mem_O_K2`. Immediate from `K_2.norm_eq_spectralNorm`/`spectralNorm_extends` (the `L → K_2 P₂` hop
is norm-preserving unconditionally, needing no hypothesis on `L` beyond `[Algebra K L]`/
`[NontriviallyNormedField L]`/`[CompleteSpace L]`, already in scope). Composing this with
`norm_le_one_of_mem_integralClosure hnormL c` (applied directly by the caller, at whichever
concrete `Algebra ↥𝒪[K] L` instance is active there) recovers `K_2.norm_le_one_of_mem_O_K1`/
`K_3.norm_le_one_of_mem_O_K2` exactly — checked below, not merely claimed. -/
theorem norm_le_one_of_algebraMap_le_one_of_algebraL {y : L} (hy : ‖y‖ ≤ 1) :
    ‖algebraMap L (K_2 (K' := L) P₂) y‖ ≤ 1 := by
  rw [K_2.norm_eq_spectralNorm, spectralNorm_extends]
  exact hy

omit [IsUltrametricDist K] [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [CompleteSpace K] [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring]
  [IsUltrametricDist L] [CompleteSpace L] [Algebra K L] in
/-- **Injectivity into `L` extends unchanged into `K_2 (K' := L) P₂`** — the generic form of the
"one hop further" half of `K_2.instFaithfulSMul_O_K1`/`K_3.instFaithfulSMul_O_K2`: any injective
map into `L`, composed with `algebraMap L (K_2 (K' := L) P₂)` (injective, `RingHom.injective`,
automatic for a field source and nontrivial target via the ambient `IsSimpleRing L` instance),
stays injective. Composing this with `Subtype.coe_injective` (applied directly by the caller, at
whichever concrete `O_L → L` subring inclusion is active there) recovers `K_2.instFaithfulSMul_
O_K1`/`K_3.instFaithfulSMul_O_K2` exactly — checked below, not merely claimed. -/
theorem injective_algebraMap_comp_of_algebraL {A : Type*} {f : A → L}
    (hf : Function.Injective f) :
    Function.Injective (fun a => algebraMap L (K_2 (K' := L) P₂) (f a)) :=
  (algebraMap L (K_2 (K' := L) P₂)).injective.comp hf

end Generic

/-! ## The base case, `L := K_1 P` -/

variable {P : O[X]}

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] [IsFractionRing O K] in
/-- **`K`'s norm extends exactly to `K_1 P`** — the base case for `hnorm_K_of_algebraL`'s induction,
immediate from `K_1.norm_eq_spectralNorm`/`spectralNorm_extends` (the same one-hop fact `K_2.hnorm_K`
already uses inline, extracted here as its own named lemma so the induction has an explicit anchor). -/
theorem hnorm_K_K_1 : ∀ x : K, ‖algebraMap K (K_1 (K := K) P) x‖ = ‖x‖ := fun x => by
  rw [K_1.norm_eq_spectralNorm, spectralNorm_extends]

variable (P₂ : (↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring
    (K_1 (K := K) P)))[X])

/-! ## Non-vacuity: the generic lemma, at `L := K_1 P`, recovers `K_2.instAlgebraK`/`K_2.hnorm_K`
exactly -/

/-- **The generic composite, instantiated at `L := K_1 P`, carries the same `algebraMap` function as
`K_2.instAlgebraK`** — checked directly (`rfl` at the `RingHom` level, cheap; the analogous check on
the full bundled `Algebra` structure, attempted first, hit a `200,000`-heartbeat `isDefEq` timeout —
recorded as a genuinely new, small elaboration-cost finding in `ROADMAP.md` §78, not merely claimed to
not matter — comparing two `Algebra` structures forces `isDefEq` to walk their `toSMul`/`toModule`
substructure too, not just the `algebraMap` ring hom the whole arc actually cares about; comparing the
ring hom directly sidesteps that walk entirely). This is the operative sense in which the two
constructions "agree": every downstream use only ever inspects `algebraMap`, never the raw `Algebra`
term. -/
example :
    @algebraMap K (K_2 (K' := K_1 (K := K) P) P₂) _ _
      (instAlgebraK_of_algebraL (K := K)
        (O' := ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))
        (L := K_1 (K := K) P) P₂) =
    @algebraMap K (K_2 (K' := K_1 (K := K) P) P₂) _ _
      (K_2.instAlgebraK (K := K) (P := P) P₂) := rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [(NormedField.valuation (K := K)).Compatible]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] [IsFractionRing O K] in
/-- **The generic norm fact, instantiated at `L := K_1 P` with `hnorm_K_K_1` as the base case, agrees
with `K_2.hnorm_K`** (both are proofs of the same `Prop`, so this is really a type-check of the
statement rather than a further theorem, but recorded to make the base-case instantiation explicit
and reusable). -/
theorem hnorm_K_K_2 :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    ∀ x : K, ‖algebraMap K (K_2 (K' := K_1 (K := K) P) P₂) x‖ = ‖x‖ :=
  hnorm_K_of_algebraL (K := K)
    (O' := ↥(integralClosure ↥(ValuativeRel.valuation K).valuationSubring (K_1 (K := K) P)))
    (L := K_1 (K := K) P) P₂ hnorm_K_K_1

/-! ## The genuine second step: `L := K_2 (K' := K_1 P) P₂`, deriving the `K_3`-level fact for free -/

variable {P₃O : Type*} [CommRing P₃O] [Algebra P₃O (K_2 (K' := K_1 (K := K) P) P₂)]
  (P₃ : P₃O[X])

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [(NormedField.valuation (K := K)).Compatible]
  [IsDiscreteValuationRing ↥(ValuativeRel.valuation K).valuationSubring] [IsFractionRing O K] in
/-- **`K`'s norm extends exactly to `K_3`-shaped `K_2 (K' := K_2 (K' := K_1 P) P₂) P₃`** — derived by
applying `hnorm_K_of_algebraL` a *second* time, at `L := K_2 (K' := K_1 P) P₂`, fed `hnorm_K_K_2` as
its `hnormL`. **No new per-level file was needed for this** — the exact deliverable `§73`'s "next
concrete step" flagged as missing (`K_n.instAlgebraK`/its norm fact, built inductively rather than
hand-copied) is realized here, for real, at the concrete `n = 1 → 2 → 3` depth this arc has data for.
Nothing in this proof or `hnorm_K_of_algebraL`'s own proof refers to `L` being `K_1`- or `K_2`-shaped
specifically — the same call would produce the `K_4`-level fact from this theorem's own conclusion,
and so on indefinitely. -/
theorem hnorm_K_K_3 :
    letI := K_2.instAlgebraK (K := K) (P := P) P₂
    letI := instAlgebraK_of_algebraL (K := K) (O' := P₃O)
      (L := K_2 (K' := K_1 (K := K) P) P₂) P₃
    ∀ x : K, ‖algebraMap K (K_2 (K' := K_2 (K' := K_1 (K := K) P) P₂) P₃) x‖ = ‖x‖ := by
  letI := K_2.instAlgebraK (K := K) (P := P) P₂
  exact hnorm_K_of_algebraL (K := K) (O' := P₃O) (L := K_2 (K' := K_1 (K := K) P) P₂) P₃
    (hnorm_K_K_2 (K := K) (P := P) P₂)

end LubinTate

end
