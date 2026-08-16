/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.PrincipalIdealDomain

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

**`IsDiscreteValuationRing`/`IsAdicComplete` transport does *not* close here, even after
decomposing each into its constituent pieces.** `isPrincipalIdealRing_integralClosure_
integralClosure` closes — `IsPrincipalIdealRing`, like `IsDomain`/`IsLocalRing`, has no further
instance argument nested in its own signature (only `[Ring R]`), so the same `toSubring` + `rw`
technique goes through unchanged. But `IsDiscreteValuationRing.not_a_field'` (`maximalIdeal R ≠
⊥`) and the two pieces `IsAdicComplete` extends (`IsHausdorff`, `IsPrecomplete`) all mention
`IsLocalRing.maximalIdeal`, which itself needs a `[IsLocalRing R]` instance argument to even
typecheck — and *that* instance, once baked into an already-elaborated hypothesis (e.g. `inst :
IsHausdorff (maximalIdeal ↥(integralClosure R M)) ↥(integralClosure R M)`), is a **fixed** proof
term referencing the *original*, non-`toSubring` type, not a uniformly-abstracted one. `rw`'s
motive-generalization then tries to abstract the ring type being rewritten out of a term whose
embedded `[IsLocalRing]` argument still concretely mentions the un-abstracted original type, and
fails with "motive is not type correct" — regardless of whether the matching `[IsLocalRing
↥(integralClosure R M).toSubring]` instance is *also* made available in context first (tried, via
`haveI`; ascription via `:=` performs a defeq check against the already-elaborated term, it does
not re-elaborate that term's internal instance arguments against the new hypotheses in scope).
`cases`/`subst` on the underlying type-level equality was tried too, and fails for the same
structural reason (`Dependent elimination failed`) since neither side of the equality is a bare
local variable.

This is a genuine **second**, structurally distinct obstacle from what blocked `IsDomain`/
`IsLocalRing` initially (those two have no such nested `maximalIdeal`-style dependency, which is
exactly why they close) — not a mathematical gap (the underlying fact, that both spellings are DVRs
/ adically complete, is true, since they are literally the same ring), and not closeable by a small
plumbing fix: the principled route (`RingEquiv.subringCongr toSubring_integralClosure_eq`, transport
`IsLocalHom` for both directions of the equivalence, `IsLocalRing.maximalIdeal_comap` to identify the
pushed-forward maximal ideal, then transport `IsHausdorff`/`IsPrecomplete` along the resulting
ring-and-ideal-compatible equivalence) needs a general "`IsHausdorff`/`IsPrecomplete` transport along
a compatible `RingEquiv`" lemma that Mathlib does not provide (checked: no `LinearEquiv`- or
`RingEquiv`-indexed transport lemma for either class exists), i.e. new general infrastructure, not a
few lines. Not attempted further this pass. See `ROADMAP.md` for the precise handoff.
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

/-- **`IsPrincipalIdealRing` transports from `↥(integralClosure R M)` to `↥(integralClosure
(↥(integralClosure R L)) M)`.** Same technique as `isDomain_integralClosure_integralClosure` —
`IsPrincipalIdealRing`, like `IsDomain`/`IsLocalRing`, has no further instance argument nested in
its own signature (only `[Ring R]`), so the `toSubring` + `rw` route stays well-typed. This is the
piece of `IsDiscreteValuationRing` (`extends IsPrincipalIdealRing, IsLocalRing` plus `not_a_field'`)
that *does* close; see the module docstring for why the other two pieces do not. -/
instance isPrincipalIdealRing_integralClosure_integralClosure
    [inst : IsPrincipalIdealRing ↥(integralClosure R M)] :
    IsPrincipalIdealRing ↥(integralClosure (↥(integralClosure R L)) M) := by
  have hpir : IsPrincipalIdealRing ↥(integralClosure R M).toSubring := inst
  rw [toSubring_integralClosure_eq (R := R) (L := L) (M := M)] at hpir
  exact hpir

end IsIntegralClosureTower
