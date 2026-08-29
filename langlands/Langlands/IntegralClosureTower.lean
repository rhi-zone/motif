/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Integral closure commutes with towers: `integralClosure R M` and `integralClosure (integralClosure R L) M`

For a tower of rings `R ⊆ L ⊆ M`, an element of `M` is integral over `R` iff it is integral over
`↥(integralClosure R L)` — no hypothesis on the tower beyond the algebra/scalar-tower structure is
needed. This is a pure consequence of transitivity of integrality: `↥(integralClosure R L)` is
always integral over `R` (`integralClosure.AlgebraIsIntegral`), so `isIntegral_trans` gives the
"only if" direction, and `IsIntegral.tower_top` (integrality only grows as the base ring grows)
gives the "if" direction.

This file exists to check, precisely, the caveat flagged for the Lubin-Tate tower: whether
`O_{K_2} := integralClosure O_{K_1} baseChangeSplittingField` (integral closure over the *intermediate* ring) coincides
with `integralClosure O baseChangeSplittingField` (integral closure over the *base*). The answer is yes, as sets, always
— the two spellings denote the same ring (`toSubring_integralClosure_eq`).

## What this closes

`toSubring_integralClosure_eq` and `isIntegral_iff_isIntegral_integralClosure` are complete,
general, `sorry`-free facts: the caveat itself is resolved — the two `O_{K_2}` spellings are
genuinely the same subring of `baseChangeSplittingField`, unconditionally. `isDomain_integralClosure_integralClosure`
and `isLocalRing_integralClosure_integralClosure` transport those two specific instances across the
two spellings (`↥S` and `↥S.toSubring` are defeq, so a bare instance ascription suffices once the
`Subring`-level equality is rewritten). `isPrincipalIdealRing_integralClosure_integralClosure`
closes the same way.

**`IsDiscreteValuationRing`/`IsAdicComplete` also close, but needed a different technique**, because
`IsDiscreteValuationRing.not_a_field'` (`maximalIdeal R ≠ ⊥`) and the two pieces `IsAdicComplete`
extends (`IsHausdorff`, `IsPrecomplete`) all mention `IsLocalRing.maximalIdeal`, which itself needs a
`[IsLocalRing R]` instance argument to even typecheck. Once such a hypothesis is already elaborated
(e.g. `inst : IsHausdorff (maximalIdeal
↥(integralClosure R M)) ↥(integralClosure R M)`), its embedded `[IsLocalRing]` instance argument is a
**fixed** term referencing the un-abstracted original type — so `rw [toSubring_integralClosure_eq] at
inst` fails with "motive is not type correct" (the motive-generalization cannot abstract the rewritten
subtype out from under the fixed instance term), `haveI`-staging the matching instance first does not
help (term ascription only defeq-checks against the already-elaborated term, it does not re-elaborate
its internal instance arguments), and `cases`/`subst` on the underlying type-level equality fails too
("Dependent elimination failed", neither side is a bare local variable).

The fix that avoids all three failure modes: build an explicit `e : ↥(integralClosure R M).toSubring
≃+* ↥(integralClosure (↥(integralClosure R L)) M).toSubring` via `RingEquiv.subringCongr
toSubring_integralClosure_eq`, then transport `IsHausdorff`/`IsPrecomplete`/`IsAdicComplete` along `e`
directly — **not** by rewriting an already-elaborated hypothesis whose type mentions
`IsLocalRing.maximalIdeal`, but by applying a lemma stated for an *explicit* ideal argument `I : Ideal
R` and only afterward specializing `I := maximalIdeal`. Because `IsHausdorff I M`/`IsPrecomplete I
M`/`IsAdicComplete I M` are themselves defined relative to an explicit `I : Ideal R` (no
`IsLocalRing`-style nested instance argument inside the class signature — confirmed by reading
`Mathlib/RingTheory/AdicCompletion/Basic.lean` directly), the obstruction never arises for these
classes at that level of generality; it only arises when one tries to `rw` an
already-instantiated `maximalIdeal`-headed hypothesis instead of routing through the explicit-ideal
statement.

**Mathlib already provides exactly this transport**: `IsHausdorff.congr_ringEquiv`,
`IsPrecomplete.congr_ringEquiv`, and `IsAdicComplete.congr_ringEquiv` (all in
`Mathlib/RingTheory/AdicCompletion/Topology.lean`, authored 2025) give `IsAdicComplete (I.map e) S ↔
IsAdicComplete I R` (similarly for the two pieces) for any `e : R ≃+* S` — general, no `IsLocalRing`
dependency in the statement. Combined with `IsLocalRing.map_ringEquiv_maximalIdeal` (`(maximalIdeal
R).map e = maximalIdeal S` given `[IsLocalRing R] [IsLocalRing S]`), specializing `I := maximalIdeal`
closes `IsAdicComplete` for the `O_{K_2}`-style transport with no new general infrastructure needed.
`IsDiscreteValuationRing`'s `not_a_field'` field closes the same way, using
`Ideal.map_eq_bot_iff_of_injective` to push `maximalIdeal ≠ ⊥` forward along the (injective, being a
`RingEquiv`) map `e`.
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

/-- **The ring equivalence identifying `↥(integralClosure R M)` with `↥(integralClosure
(↥(integralClosure R L)) M)`**, as a defeq-transparent detour through `Subring M`. This is the
vehicle for transporting instances (`IsAdicComplete`, `IsDiscreteValuationRing`) whose class
signature itself references `IsLocalRing.maximalIdeal` — see the module docstring for why a bare
`rw` on an already-elaborated `maximalIdeal`-headed hypothesis fails, and why routing through this
explicit `RingEquiv` instead avoids the failure. -/
noncomputable def integralClosureRingEquiv :
    ↥(integralClosure R M).toSubring ≃+* ↥(integralClosure (↥(integralClosure R L)) M).toSubring :=
  RingEquiv.subringCongr (toSubring_integralClosure_eq (R := R) (L := L) (M := M))

open IsLocalRing in
/-- **`IsAdicComplete` (at the maximal ideal) transports from `↥(integralClosure R M)` to
`↥(integralClosure (↥(integralClosure R L)) M)`.** Uses Mathlib's `IsAdicComplete.congr_ringEquiv`
(general, stated for an explicit ideal along any `RingEquiv`) specialized via
`IsLocalRing.map_ringEquiv_maximalIdeal` to identify the pushed-forward maximal ideal — see the
module docstring for why this route, rather than `rw`ing the `maximalIdeal`-headed hypothesis
directly, is what makes the transport go through. -/
instance isAdicComplete_integralClosure_integralClosure
    [IsLocalRing ↥(integralClosure R M)]
    [inst : IsAdicComplete (maximalIdeal ↥(integralClosure R M)) ↥(integralClosure R M)] :
    IsAdicComplete (maximalIdeal ↥(integralClosure (↥(integralClosure R L)) M))
      ↥(integralClosure (↥(integralClosure R L)) M) := by
  have e := integralClosureRingEquiv (R := R) (L := L) (M := M)
  haveI hloc1 : IsLocalRing ↥(integralClosure R M).toSubring := inferInstance
  haveI hloc2 : IsLocalRing ↥(integralClosure (↥(integralClosure R L)) M).toSubring :=
    isLocalRing_integralClosure_integralClosure (R := R) (L := L) (M := M)
  have key := IsAdicComplete.congr_ringEquiv
    (I := maximalIdeal ↥(integralClosure R M).toSubring) (e := e)
  rw [IsLocalRing.map_ringEquiv_maximalIdeal e] at key
  exact key.mpr inst

open IsLocalRing in
/-- **`IsDiscreteValuationRing` transports from `↥(integralClosure R M)` to `↥(integralClosure
(↥(integralClosure R L)) M)`.** `IsPrincipalIdealRing`/`IsLocalRing` transport unchanged
(`isPrincipalIdealRing_integralClosure_integralClosure`/`isLocalRing_integralClosure_integralClosure`);
the remaining field, `not_a_field' : maximalIdeal R ≠ ⊥`, transports by pushing the source's
`maximalIdeal ≠ ⊥` forward along the injective ring equivalence `integralClosureRingEquiv`
(`Ideal.map_eq_bot_iff_of_injective`) and then identifying the pushed-forward ideal with the target's
maximal ideal (`IsLocalRing.map_ringEquiv_maximalIdeal`), mirroring
`isAdicComplete_integralClosure_integralClosure`'s technique. -/
instance isDiscreteValuationRing_integralClosure_integralClosure
    [IsDomain ↥(integralClosure R M)] [IsDomain ↥(integralClosure (↥(integralClosure R L)) M)]
    [inst : IsDiscreteValuationRing ↥(integralClosure R M)] :
    IsDiscreteValuationRing ↥(integralClosure (↥(integralClosure R L)) M) := by
  have e := integralClosureRingEquiv (R := R) (L := L) (M := M)
  haveI hloc1 : IsLocalRing ↥(integralClosure R M).toSubring := inferInstance
  haveI hloc2 : IsLocalRing ↥(integralClosure (↥(integralClosure R L)) M).toSubring :=
    isLocalRing_integralClosure_integralClosure (R := R) (L := L) (M := M)
  refine { not_a_field' := ?_ }
  have hne : maximalIdeal ↥(integralClosure R M).toSubring ≠ ⊥ := inst.not_a_field'
  have hmap : (maximalIdeal ↥(integralClosure R M).toSubring).map e ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective e.injective).not.mpr hne
  rwa [IsLocalRing.map_ringEquiv_maximalIdeal e] at hmap

/-!
## The reverse direction: nested → flat

Every instance above transports a fact proved about the **flat** spelling `↥(integralClosure R M)`
to the **nested** one. The Lubin-Tate tower's own monogenicity/residue-field arguments go the other
way: they are proved directly about the nested spelling `↥(integralClosure (↥(integralClosure R L))
M)` (they are inherently relative to the intermediate ring `↥(integralClosure R L)`, e.g. "the
Weierstrass-factor generator's minimal polynomial over `↥(integralClosure R L)` is Eisenstein"), and
a caller that has switched to the flat spelling as its primary representation needs them transported
*to* the flat type instead. Since `integralClosureRingEquiv` is a `RingEquiv` (hence its own
`.symm` is again a `RingEquiv`), the technique is identical, just run backwards; each lemma below
is `.symm` of the corresponding forward instance applied verbatim.

**These are stated as `theorem`s, not `instance`s**, unlike the forward direction: the conclusion
`… ↥(integralClosure R M)` does not mention `L` at all, so instance search would have no way to
determine which intermediate ring `L` to search for a nested hypothesis about — registering these as
`instance`s fails outright with "cannot find synthesization order" (confirmed directly: the natural
`instance` declarations do not elaborate). Callers supply `L` explicitly. -/

/-- **`IsDomain` transports from `↥(integralClosure (↥(integralClosure R L)) M)` to
`↥(integralClosure R M)`** — the reverse of `isDomain_integralClosure_integralClosure`. -/
theorem isDomain_integralClosure_integralClosure_symm
    [inst : IsDomain ↥(integralClosure (↥(integralClosure R L)) M)] :
    IsDomain ↥(integralClosure R M) := by
  have hdom : IsDomain ↥(integralClosure (↥(integralClosure R L)) M).toSubring := inst
  rw [← toSubring_integralClosure_eq (R := R) (L := L) (M := M)] at hdom
  exact hdom

/-- **`IsLocalRing` transports from `↥(integralClosure (↥(integralClosure R L)) M)` to
`↥(integralClosure R M)`** — the reverse of `isLocalRing_integralClosure_integralClosure`. -/
theorem isLocalRing_integralClosure_integralClosure_symm
    [inst : IsLocalRing ↥(integralClosure (↥(integralClosure R L)) M)] :
    IsLocalRing ↥(integralClosure R M) := by
  have hloc : IsLocalRing ↥(integralClosure (↥(integralClosure R L)) M).toSubring := inst
  rw [← toSubring_integralClosure_eq (R := R) (L := L) (M := M)] at hloc
  exact hloc

/-- **`IsPrincipalIdealRing` transports from `↥(integralClosure (↥(integralClosure R L)) M)` to
`↥(integralClosure R M)`** — the reverse of `isPrincipalIdealRing_integralClosure_integralClosure`. -/
theorem isPrincipalIdealRing_integralClosure_integralClosure_symm
    [inst : IsPrincipalIdealRing ↥(integralClosure (↥(integralClosure R L)) M)] :
    IsPrincipalIdealRing ↥(integralClosure R M) := by
  have hpir : IsPrincipalIdealRing ↥(integralClosure (↥(integralClosure R L)) M).toSubring := inst
  rw [← toSubring_integralClosure_eq (R := R) (L := L) (M := M)] at hpir
  exact hpir

open IsLocalRing in
/-- **`IsAdicComplete` (at the maximal ideal) transports from `↥(integralClosure
(↥(integralClosure R L)) M)` to `↥(integralClosure R M)`** — the reverse of
`isAdicComplete_integralClosure_integralClosure`, via `e.symm` in place of `e`. -/
theorem isAdicComplete_integralClosure_integralClosure_symm
    [IsLocalRing ↥(integralClosure (↥(integralClosure R L)) M)]
    [IsLocalRing ↥(integralClosure R M)]
    [inst : IsAdicComplete (maximalIdeal ↥(integralClosure (↥(integralClosure R L)) M))
      ↥(integralClosure (↥(integralClosure R L)) M)] :
    IsAdicComplete (maximalIdeal ↥(integralClosure R M)) ↥(integralClosure R M) := by
  have e := (integralClosureRingEquiv (R := R) (L := L) (M := M)).symm
  haveI hloc1 : IsLocalRing ↥(integralClosure (↥(integralClosure R L)) M).toSubring :=
    inferInstance
  haveI hloc2 : IsLocalRing ↥(integralClosure R M).toSubring := inferInstance
  have key := IsAdicComplete.congr_ringEquiv
    (I := maximalIdeal ↥(integralClosure (↥(integralClosure R L)) M).toSubring) (e := e)
  rw [IsLocalRing.map_ringEquiv_maximalIdeal e] at key
  exact key.mpr inst

open IsLocalRing in
/-- **`IsDiscreteValuationRing` transports from `↥(integralClosure (↥(integralClosure R L)) M)` to
`↥(integralClosure R M)`** — the reverse of `isDiscreteValuationRing_integralClosure_integralClosure`,
via `e.symm` in place of `e`. -/
theorem isDiscreteValuationRing_integralClosure_integralClosure_symm
    [IsDomain ↥(integralClosure R M)]
    [inst : IsDiscreteValuationRing ↥(integralClosure (↥(integralClosure R L)) M)] :
    IsDiscreteValuationRing ↥(integralClosure R M) := by
  have e := (integralClosureRingEquiv (R := R) (L := L) (M := M)).symm
  haveI hloc1 : IsLocalRing ↥(integralClosure (↥(integralClosure R L)) M).toSubring :=
    inferInstance
  haveI hloc2 : IsLocalRing ↥(integralClosure R M).toSubring :=
    isLocalRing_integralClosure_integralClosure_symm (R := R) (L := L) (M := M)
  haveI hpir2 : IsPrincipalIdealRing ↥(integralClosure R M) :=
    isPrincipalIdealRing_integralClosure_integralClosure_symm (R := R) (L := L) (M := M)
      (inst := inst.toIsPrincipalIdealRing)
  refine { not_a_field' := ?_ }
  have hne : maximalIdeal ↥(integralClosure (↥(integralClosure R L)) M).toSubring ≠ ⊥ :=
    inst.not_a_field'
  have hmap : (maximalIdeal ↥(integralClosure (↥(integralClosure R L)) M).toSubring).map e ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective e.injective).not.mpr hne
  rwa [IsLocalRing.map_ringEquiv_maximalIdeal e] at hmap

open IsLocalRing in
/-- **`ResidueField` transports across `integralClosureRingEquiv`** — for a tower `R ⊆ L ⊆ M`,
given `IsLocalRing` on both the flat and nested spellings of `O_M`, their residue fields are
isomorphic. This is the vehicle for carrying a residue-field-preservation fact proved about the
*nested* spelling (e.g. `ResidueField R ≃+* ResidueField ↥(integralClosure (↥(integralClosure R L))
M)`, which is inherently relative to the intermediate ring `↥(integralClosure R L)` and so cannot be
re-derived directly for the flat spelling without redoing the tower-specific generator argument) over
to the flat spelling `↥(integralClosure R M)`, by composing with this equivalence — using Mathlib's
`IsLocalRing.ResidueField.mapEquiv` (a `RingEquiv` between local rings induces a `RingEquiv` of
residue fields) applied to `integralClosureRingEquiv`. `L` is likewise not determined by the
conclusion, so this is a `def`, applied explicitly, not an `instance`. -/
noncomputable def residueFieldEquiv_integralClosure_integralClosure
    [IsLocalRing ↥(integralClosure R M).toSubring]
    [IsLocalRing ↥(integralClosure (↥(integralClosure R L)) M).toSubring] :
    IsLocalRing.ResidueField ↥(integralClosure R M).toSubring ≃+*
      IsLocalRing.ResidueField ↥(integralClosure (↥(integralClosure R L)) M).toSubring :=
  IsLocalRing.ResidueField.mapEquiv (integralClosureRingEquiv (R := R) (L := L) (M := M))

end IsIntegralClosureTower
