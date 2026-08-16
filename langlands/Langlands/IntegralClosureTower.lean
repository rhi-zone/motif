/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.Defs

/-!
# Integral closure commutes with towers: `integralClosure R M` and `integralClosure (integralClosure R L) M`

For a tower of rings `R ⊆ L ⊆ M`, an element of `M` is integral over `R` iff it is integral over
`↥(integralClosure R L)` — no hypothesis on the tower beyond the algebra/scalar-tower structure is
needed. This is a pure consequence of transitivity of integrality: `↥(integralClosure R L)` is
always integral over `R` (`integralClosure.AlgebraIsIntegral`), so `isIntegral_trans` gives the
"only if" direction, and `IsIntegral.tower_top` (integrality only grows as the base ring grows)
gives the "if" direction.

This file exists to check, precisely, the caveat flagged for the Lubin-Tate tower: whether
`O_{K_2} := integralClosure O_{K_1} K_2` (integral closure over the *intermediate* ring) coincides
with `integralClosure O K_2` (integral closure over the *base*). The answer is yes, as sets, always
— the two spellings denote the same ring (`toSubring_integralClosure_eq`).

## What this closes, and what it does not

`toSubring_integralClosure_eq` and `isIntegral_iff_isIntegral_integralClosure` are complete,
general, `sorry`-free facts: the caveat itself is resolved — the two `O_{K_2}` spellings are
genuinely the same subring of `K_2`, unconditionally. `isDomain_integralClosure_integralClosure`
and `isLocalRing_integralClosure_integralClosure` transport those two specific instances across the
two spellings (`↥S` and `↥S.toSubring` are defeq, so a bare instance ascription suffices once the
`Subring`-level equality is rewritten).

**`IsDiscreteValuationRing`/`IsAdicComplete` transport does *not* close here.** Both classes bundle
a further instance argument into their own signature (`IsDiscreteValuationRing` requires
`[IsDomain R]`; `IsAdicComplete`'s ideal argument is `IsLocalRing.maximalIdeal`, itself requiring
`[IsLocalRing R]`), and that auxiliary instance is *also* stated relative to one spelling
(`↥(integralClosure R M).toSubring`) but gets embedded, at elaboration time, as a **fixed** proof
term inside the very type being rewritten — `rw`'s motive-generalization then tries to abstract the
rewritten subterm out of a type whose other, non-generalized argument still depends on the concrete,
un-abstracted term, and fails with "motive is not type correct". This was hit consistently (not a
one-off): every attempt to rewrite `IsDiscreteValuationRing`/`IsAdicComplete` across the
`Subring`-level equality, including forcing the auxiliary `IsDomain`/`IsLocalRing` instance into
scope first via `haveI`, hit the same failure. The blocker is a genuine Lean elaboration obstacle
(dependent motives across classes with nested instance arguments), not a mathematical gap — the
underlying *fact* (both rings are DVRs / adically complete, since they are literally the same ring)
is true, but turning it into a Lean `instance` needs a different technique (e.g. building an
explicit `RingEquiv.subringCongr`-based ring equivalence and proving `IsDiscreteValuationRing`/
`IsAdicComplete` transport along a `RingEquiv` from scratch, which Mathlib does not provide
off-the-shelf) that was not completed in this pass. See `ROADMAP.md` for the precise handoff.
-/

section IsIntegralClosureTower

variable {R L M : Type*} [CommRing R] [CommRing L] [CommRing M] [Algebra R L] [Algebra L M]
  [Algebra R M] [IsScalarTower R L M]

/-- **An element of `M` is integral over `R` iff it is integral over `↥(integralClosure R L)`.**
The intermediate ring `↥(integralClosure R L)` is always integral over `R`
(`integralClosure.AlgebraIsIntegral`), regardless of any hypothesis on `L` itself (e.g. `L` need not
be integral, algebraic, or finite over `R`). -/
theorem isIntegral_iff_isIntegral_integralClosure {x : M} :
    IsIntegral R x ↔ IsIntegral (↥(integralClosure R L)) x := by
  haveI : Algebra.IsIntegral R ↥(integralClosure R L) := integralClosure.AlgebraIsIntegral
  constructor
  · intro hx
    exact hx.tower_top
  · intro hx
    exact isIntegral_trans x hx

/-- **`integralClosure R M` and `integralClosure (↥(integralClosure R L)) M` denote the same
subring of `M`**, restricted to a common base. Direct corollary of
`isIntegral_iff_isIntegral_integralClosure`. -/
theorem integralClosure_eq_restrictScalars_integralClosure_integralClosure :
    integralClosure R M =
      (integralClosure (↥(integralClosure R L)) M).restrictScalars R := by
  ext x
  simp only [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  exact isIntegral_iff_isIntegral_integralClosure (L := L)

/-- **`integralClosure R M` and `integralClosure (↥(integralClosure R L)) M` have the same
underlying `Subring M`** — the base-ring-independent form of
`integralClosure_eq_restrictScalars_integralClosure_integralClosure`, stated at the `Subring` level
so it can be used to `rw` across instances whose class does not itself depend on any further
`Subalgebra`-base-indexed instance argument (see the module docstring for exactly where this
technique does and does not go through). -/
theorem toSubring_integralClosure_eq :
    (integralClosure R M).toSubring = (integralClosure (↥(integralClosure R L)) M).toSubring := by
  ext x
  simp only [Subalgebra.mem_toSubring, mem_integralClosure_iff]
  exact isIntegral_iff_isIntegral_integralClosure (L := L)

/-- **`IsDomain` transports from `↥(integralClosure R M)` to `↥(integralClosure (↥(integralClosure
R L)) M)`.** `↥S` and `↥S.toSubring` are defeq (`Subalgebra.toSubring` reuses the same carrier), so
a bare instance ascription identifies `IsDomain ↥(integralClosure R M)` with `IsDomain
↥(integralClosure R M).toSubring`; `toSubring_integralClosure_eq` then rewrites the latter across to
the target spelling, purely at the `Subring M` level (no further instance argument is nested inside
`IsDomain`'s own signature, so the `rw` motive stays well-typed). -/
instance isDomain_integralClosure_integralClosure
    [inst : IsDomain ↥(integralClosure R M)] :
    IsDomain ↥(integralClosure (↥(integralClosure R L)) M) := by
  have hdom : IsDomain ↥(integralClosure R M).toSubring := inst
  rw [toSubring_integralClosure_eq (R := R) (L := L) (M := M)] at hdom
  exact hdom

/-- **`IsLocalRing` transports from `↥(integralClosure R M)` to `↥(integralClosure
(↥(integralClosure R L)) M)`.** Same technique as `isDomain_integralClosure_integralClosure`. -/
instance isLocalRing_integralClosure_integralClosure
    [inst : IsLocalRing ↥(integralClosure R M)] :
    IsLocalRing ↥(integralClosure (↥(integralClosure R L)) M) := by
  have hloc : IsLocalRing ↥(integralClosure R M).toSubring := inst
  rw [toSubring_integralClosure_eq (R := R) (L := L) (M := M)] at hloc
  exact hloc

end IsIntegralClosureTower
