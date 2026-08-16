/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.LubinTateTowerStepConcreteK2

/-!
# `K_3`, the level-3 Lubin-Tate extension

`Langlands/LubinTateTowerStepConcreteK2.lean`'s `exists_eisenstein_tower_step_K_2` produces `K_3`'s
Eisenstein polynomial `P₃ : O_{K_2}[X]` but stops short of building `K_3` itself as a field object
(`ROADMAP.md §63`, "Not yet done, and not claimed"). This file supplies it.

`LubinTate.K_2` (`Langlands/LubinTateTowerStepConcrete.lean`) is already generic in its own free
parameters `O'`/`K'` — "the general one-step splitting field construction". `K_3` is *literally* that
same construction, instantiated one level further: `K_3 P₃ := K_2 (K' := K_2 P₂) P₃`. Its `Field`/
`Algebra K'`/`IsSplittingField` instances forward verbatim from `K_2`'s own, via the definitional
equality — no new content, exactly mirroring how `K_2` itself was built as a one-line `def` in
`LubinTateTowerStepConcrete.lean`.

## Main results

* `LubinTate.K_3` : the splitting field of (the image of) `P₃` over `K_2 P₂` — the level-3 Lubin-Tate
  extension.
* `K_3.instField` / `K_3.instAlgebra` / `K_3.instIsSplittingField` : the basic field-object package,
  forwarded from `K_2`'s own instances.
-/

noncomputable section

open scoped Polynomial

namespace LubinTate

/-- **`K_3`, the level-3 Lubin-Tate extension**: `LubinTate.K_2`'s general one-step splitting-field
construction, instantiated one level further (`O' := O_{K_2}`, `K' := K_2 P₂`, in the concrete
tower). Mirrors `LubinTate.K_2`'s own definition, one level up — this file's whole point is that no
new mathematical content is needed to *define* the field object itself, only to re-derive its
degree/monogenicity/residue-field facts (see `ROADMAP.md` for the full account). -/
@[reducible] def K_3 {O' : Type*} [CommRing O'] {K' : Type*} [Field K'] [Algebra O' K']
    (P₃ : O'[X]) : Type _ :=
  K_2 (K' := K') P₃

instance K_3.instField {O' : Type*} [CommRing O'] {K' : Type*} [Field K'] [Algebra O' K']
    (P₃ : O'[X]) : Field (K_3 (K' := K') P₃) :=
  K_2.instField P₃

instance K_3.instAlgebra {O' : Type*} [CommRing O'] {K' : Type*} [Field K'] [Algebra O' K']
    (P₃ : O'[X]) : Algebra K' (K_3 (K' := K') P₃) :=
  K_2.instAlgebra P₃

instance K_3.instIsSplittingField {O' : Type*} [CommRing O'] {K' : Type*} [Field K']
    [Algebra O' K'] (P₃ : O'[X]) :
    Polynomial.IsSplittingField K' (K_3 (K' := K') P₃) (P₃.map (algebraMap O' K')) :=
  K_2.instIsSplittingField P₃

end LubinTate

end
