/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepConcreteK2

/-!
# `K_3`, a named convenience alias for the level-3 Lubin-Tate extension

`Langlands/LubinTateTowerStepConcreteK2.lean`'s `exists_eisenstein_tower_step_K_2` produces `K_3`'s
Eisenstein polynomial `P₃ : O_{K_2}[X]` but stops short of building `K_3` itself as a field object.
This file supplies it.

**`K_3` is not an independent construction.** `LubinTate.baseChangeSplittingField` (`Langlands/
LubinTateTowerStepConcrete.lean`) is the general one-step splitting-field combinator, generic across
every tower level. `K_3` is *literally* that same combinator, applied one level further:
`K_3 P₃ := baseChangeSplittingField (K' := baseChangeSplittingField P₂) P₃`. Its `Field`/`Algebra K'`/
`IsSplittingField` instances forward verbatim from `baseChangeSplittingField`'s own, via the definitional
equality — no new content.

`K_3` is kept, deliberately, as a thin `@[reducible]` name for this one concrete instantiation rather
than writing `baseChangeSplittingField (K' := baseChangeSplittingField P₂) P₃` at every call site: there are
roughly 200 bare call sites of `K_3` across the `K_2 → K_3`-consuming files
(`LubinTateTowerStepK3*.lean`, `LubinTateTowerStepLevelInvariance.lean`, and others), making an
inline-everywhere rewrite a large, risky mechanical sweep for no mathematical gain, since `K_3` is
already `@[reducible]` and unfolds transparently wherever needed. Keeping the name is a
readability/reviewability choice, not a claim that `K_3` is anything other than a named
specialization of `baseChangeSplittingField`.

## Main results

* `LubinTate.K_3` : the splitting field of (the image of) `P₃` over `baseChangeSplittingField P₂` — the
  level-3 Lubin-Tate extension, i.e. `baseChangeSplittingField` applied one level past `baseChangeSplittingField`
  itself.
* `K_3.instField` / `K_3.instAlgebra` / `K_3.instIsSplittingField` : the basic field-object package,
  forwarded from `baseChangeSplittingField`'s own instances.
-/

noncomputable section

open scoped Polynomial

namespace LubinTate

/-- **`K_3`, the level-3 Lubin-Tate extension**: `LubinTate.baseChangeSplittingField`'s general one-step splitting-field
construction, instantiated one level further (`O' := O_{K_2}`, `K' := baseChangeSplittingField P₂`, in the concrete
tower). Mirrors `LubinTate.baseChangeSplittingField`'s own definition, one level up — no new mathematical content is
needed to *define* the field object itself; only its degree/monogenicity/residue-field facts still need to be
re-derived at this level. -/
@[reducible] def K_3 {O' : Type*} [CommRing O'] {K' : Type*} [Field K'] [Algebra O' K']
    (P₃ : O'[X]) : Type _ :=
  baseChangeSplittingField (K' := K') P₃

instance K_3.instField {O' : Type*} [CommRing O'] {K' : Type*} [Field K'] [Algebra O' K']
    (P₃ : O'[X]) : Field (K_3 (K' := K') P₃) :=
  baseChangeSplittingField.instField P₃

instance K_3.instAlgebra {O' : Type*} [CommRing O'] {K' : Type*} [Field K'] [Algebra O' K']
    (P₃ : O'[X]) : Algebra K' (K_3 (K' := K') P₃) :=
  baseChangeSplittingField.instAlgebra P₃

instance K_3.instIsSplittingField {O' : Type*} [CommRing O'] {K' : Type*} [Field K']
    [Algebra O' K'] (P₃ : O'[X]) :
    Polynomial.IsSplittingField K' (K_3 (K' := K') P₃) (P₃.map (algebraMap O' K')) :=
  baseChangeSplittingField.instIsSplittingField P₃

end LubinTate

end
