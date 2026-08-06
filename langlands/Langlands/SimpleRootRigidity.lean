/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Henselian

/-!
# Rigidity of simple roots in a local ring

A *simple* root of a polynomial over a local ring — one at which the derivative is a unit — is
determined by its residue: two roots of the same polynomial with the same residue, one of them
simple, are equal. Mathlib states this as
`IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub` (`stacks 06RR`), with the hypothesis phrased as
`¬ IsUnit (a - b)`; this file restates it in residue-field terms and adds the two small utilities
needed to move between "residue is nonzero" and "is a unit".

The consumers are `Langlands.HenselianResidueLift` (where the root is produced by Hensel's lemma)
and `Langlands.RamificationFiltration` (where rigidity forces a ramification-group element to fix
the lifted root *on the nose*, not merely modulo `𝔪`, which is what makes the kernel argument for
the associated-graded embeddings work).

This file is deliberately kept to a `Mathlib.RingTheory.Henselian`-only import so that
`Langlands.RamificationFiltration` — a general-theory file over an arbitrary
`A : ValuationSubring L` — does not have to depend on the local-fields machinery of
`Langlands.UnramifiedExtension`.
-/

noncomputable section

open Polynomial IsLocalRing

/-- The residue of `q.eval x` is the evaluation of `q` at the residue of `x`, read in
`ResidueField R` as an `R`-algebra. `Polynomial.eval_map_apply` plus the identification of
`algebraMap R (ResidueField R)` with `residue R`. -/
theorem IsLocalRing.residue_eval {R : Type*} [CommRing R] [IsLocalRing R] (q : R[X]) (x : R) :
    residue R (q.eval x) = aeval (residue R x) q := by
  rw [aeval_def, ResidueField.algebraMap_eq, ← Polynomial.eval_map, Polynomial.eval_map_apply]

/-- In a local ring, an element whose residue is nonzero is a unit. -/
theorem IsLocalRing.isUnit_of_residue_ne_zero {R : Type*} [CommRing R] [IsLocalRing R] {a : R}
    (h : residue R a ≠ 0) : IsUnit a := by
  by_contra hu
  exact h ((residue_eq_zero_iff a).mpr (mem_maximalIdeal a |>.mpr (mem_nonunits_iff.mpr hu)))

/-- **Two roots with the same residue, one of them simple, coincide.** This is the rigidity that
makes a Hensel-lifted root canonical: `IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`
(Mathlib, `stacks 06RR`) with its `¬ IsUnit (x - y)` hypothesis rewritten as equality of residues.

The intended use is with `y := σ x` for `σ` a ring automorphism fixing the coefficients of `q` and
acting trivially on the residue field: then `σ x` is again a root with the same residue as `x`, so
`σ x = x` *on the nose*. -/
theorem IsLocalRing.eq_of_isRoot_of_residue_eq {R : Type*} [CommRing R] [IsLocalRing R] {q : R[X]}
    {x y : R} (hx : q.eval x = 0) (hy : q.eval y = 0) (hres : residue R x = residue R y)
    (hd : IsUnit ((derivative q).eval x)) : x = y := by
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hx hy ?_ hd
  rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, hres, sub_self]

end
