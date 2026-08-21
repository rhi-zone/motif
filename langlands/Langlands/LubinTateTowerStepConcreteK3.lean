/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepConcreteK2

/-!
# `K_3`, a named convenience alias for the level-3 Lubin-Tate extension

`Langlands/LubinTateTowerStepConcreteK2.lean`'s `exists_eisenstein_tower_step_K_2` produces `K_3`'s
Eisenstein polynomial `P₃ : O_{K_2}[X]` but stops short of building `K_3` itself as a field object
(`ROADMAP.md §63`, "Not yet done, and not claimed"). This file supplies it.

**`K_3` is not an independent construction.** `LubinTate.nextSplittingField` (`Langlands/
LubinTateTowerStepConcrete.lean`, renamed from `K_2` — `ROADMAP.md` §92 — once its genuinely
generic role across every tower level was recognized) is the general one-step splitting-field
combinator. `K_3` is *literally* that same combinator, applied one level further:
`K_3 P₃ := nextSplittingField (K' := nextSplittingField P₂) P₃`. Its `Field`/`Algebra K'`/
`IsSplittingField` instances forward verbatim from `nextSplittingField`'s own, via the definitional
equality — no new content.

`K_3` is kept, deliberately, as a thin `@[reducible]` name for this one concrete instantiation
(`ROADMAP.md` §92 considered deleting it outright, in favor of writing `nextSplittingField (K' :=
nextSplittingField P₂) P₃` at every call site, but found roughly 200 bare call sites of `K_3` across
the `K_2 → K_3`-consuming files — `LubinTateTowerStepK3*.lean`, `LubinTateTowerStepLevelInvariance.lean`,
and others — making that migration a large, risky mechanical sweep for no mathematical gain, since
`K_3` was already `@[reducible]` and unfolds transparently wherever needed). Keeping the name is a
readability/reviewability choice, not a claim that `K_3` is anything other than a named
specialization of `nextSplittingField`.

## Main results

* `LubinTate.K_3` : the splitting field of (the image of) `P₃` over `nextSplittingField P₂` — the
  level-3 Lubin-Tate extension, i.e. `nextSplittingField` applied one level past `nextSplittingField`
  itself.
* `K_3.instField` / `K_3.instAlgebra` / `K_3.instIsSplittingField` : the basic field-object package,
  forwarded from `nextSplittingField`'s own instances.
-/

noncomputable section

open scoped Polynomial

namespace LubinTate

/-- **`K_3`, the level-3 Lubin-Tate extension**: `LubinTate.nextSplittingField`'s general one-step splitting-field
construction, instantiated one level further (`O' := O_{K_2}`, `K' := nextSplittingField P₂`, in the concrete
tower). Mirrors `LubinTate.nextSplittingField`'s own definition, one level up — this file's whole point is that no
new mathematical content is needed to *define* the field object itself, only to re-derive its
degree/monogenicity/residue-field facts (see `ROADMAP.md` for the full account). -/
@[reducible] def K_3 {O' : Type*} [CommRing O'] {K' : Type*} [Field K'] [Algebra O' K']
    (P₃ : O'[X]) : Type _ :=
  nextSplittingField (K' := K') P₃

instance K_3.instField {O' : Type*} [CommRing O'] {K' : Type*} [Field K'] [Algebra O' K']
    (P₃ : O'[X]) : Field (K_3 (K' := K') P₃) :=
  nextSplittingField.instField P₃

instance K_3.instAlgebra {O' : Type*} [CommRing O'] {K' : Type*} [Field K'] [Algebra O' K']
    (P₃ : O'[X]) : Algebra K' (K_3 (K' := K') P₃) :=
  nextSplittingField.instAlgebra P₃

instance K_3.instIsSplittingField {O' : Type*} [CommRing O'] {K' : Type*} [Field K']
    [Algebra O' K'] (P₃ : O'[X]) :
    Polynomial.IsSplittingField K' (K_3 (K' := K') P₃) (P₃.map (algebraMap O' K')) :=
  nextSplittingField.instIsSplittingField P₃

end LubinTate

end
