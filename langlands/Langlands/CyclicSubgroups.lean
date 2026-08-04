import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Card

/-!
# Subgroups of a finite cyclic group are classified by divisors of its order

Pure group theory, with no connection to the rest of `Langlands` -- a general-purpose fact about
finite cyclic groups: for every divisor `d` of `Nat.card G`, there is a *unique* subgroup of `G` of
order `d`. This is the standard classification of subgroups of a finite cyclic group (e.g. Lidl &
Niederreiter, *Finite Fields*, Theorem 2.6, for the special case of `GF(q^n)`'s subfield lattice;
Dummit & Foote, *Abstract Algebra*, Theorem 14.19, for the general cyclic-group statement).

Not (as far as a Loogle/Mathlib search found) already in Mathlib: `IsCyclic.card_powMonoidHom_ker`
and `IsCyclic.card_powMonoidHom_range` (`Mathlib.GroupTheory.SpecificGroups.Cyclic`) give the
cardinality of the kernel/range of the `d`-th power map on a cyclic group, but nothing in Mathlib
packages this into "existence and uniqueness of a subgroup of each order dividing `Nat.card G`".

## Main result

* `IsCyclic.existsUnique_subgroup_card_eq` : for `G` a finite cyclic group and `d ∣ Nat.card G`,
  there is a unique subgroup `H ≤ G` with `Nat.card H = d`, namely the kernel of the `d`-th power
  endomorphism `powMonoidHom d`.

## Proof idea

Existence: `(powMonoidHom d).ker = {x : G | x ^ d = 1}` has cardinality `(Nat.card G).gcd d = d`
(since `d ∣ Nat.card G`), by `IsCyclic.card_powMonoidHom_ker`.

Uniqueness (`IsCyclic.subgroup_eq_powMonoidHom_ker_of_card_eq`): any subgroup `K ≤ G` of order `d`
consists of solutions to `x ^ d = 1` (Lagrange *within* `K`, via `Subgroup.orderOf_dvd_natCard`,
applied to elements of `G` directly -- this stays entirely within `Nat.card`, never introducing a
`Fintype` instance, since `Fintype.ofFinite`-derived instances are not defeq-canonical and mixing
independently-derived copies for the same type is a common way to make `isDefEq`/`whnf` time out),
i.e. `K ≤ (powMonoidHom d).ker`. Since both are finite of the same cardinality `d`, the inclusion
map `K → (powMonoidHom d).ker` is injective with `Nat.card` of the codomain `≤` that of the domain,
hence bijective (`Function.Injective.bijective_of_nat_card_le`), hence the inclusion of subgroups
is an equality.

**Elaboration gotcha found while proving this** (unrelated to `Fintype`): every occurrence of
`powMonoidHom d` here is annotated `powMonoidHom d (α := G)`. Leaving the implicit type argument
`α` to be inferred silently at some occurrences (relying on unification with `.ker`/`Nat.card` to
pin it down) but not others made `refine`/`exact` calls combining them time out at `isDefEq`/`whnf`
even at several times the default heartbeat budget -- not a slow-but-finite check, but one that
needed genuinely more heartbeats each time the budget was raised, indicative of elaboration going
down a bad (deferred-metavariable) path rather than a merely expensive but convergent one.
Annotating `α` explicitly and consistently everywhere made every occurrence elaborate immediately.
-/

@[expose] public section

namespace IsCyclic

variable {G : Type*} [CommGroup G] [IsCyclic G] [Finite G]

/-- Any subgroup of a finite cyclic group `G` of order `d` (necessarily `d ∣ Nat.card G`, by
Lagrange) equals the kernel of the `d`-th power endomorphism: every element of a subgroup of order
`d` has order dividing `d` (Lagrange applied *inside* the subgroup, `Subgroup.orderOf_dvd_natCard`),
and the kernel has the same (finite) cardinality `d` once `d ∣ Nat.card G`, so the inclusion of
subgroups is an equality. -/
theorem subgroup_eq_powMonoidHom_ker_of_card_eq (K : Subgroup G) {d : ℕ}
    (hd : d ∣ Nat.card G) (hK : Nat.card K = d) : K = (powMonoidHom d (α := G)).ker := by
  have hle : K ≤ (powMonoidHom d (α := G)).ker := by
    intro x hx
    have horder : orderOf x ∣ d := by
      have h := K.orderOf_dvd_natCard hx
      rwa [hK] at h
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    exact orderOf_dvd_iff_pow_eq_one.mp horder
  have hcard : Nat.card (powMonoidHom d (α := G)).ker = d := by
    rw [IsCyclic.card_powMonoidHom_ker]
    exact Nat.gcd_eq_right hd
  have hbij : Function.Bijective (Subgroup.inclusion hle) :=
    (Subgroup.inclusion_injective hle).bijective_of_nat_card_le (by rw [hK, hcard])
  refine le_antisymm hle fun x hx => ?_
  obtain ⟨⟨y, hy⟩, hyx⟩ := hbij.2 ⟨x, hx⟩
  have hxy : y = x := by
    have h := congrArg (fun z : (powMonoidHom d (α := G)).ker => (z : G)) hyx
    simpa [Subgroup.coe_inclusion] using h
  rwa [hxy] at hy

/-- **Classification of subgroups of a finite cyclic group**: for every divisor `d` of `Nat.card G`
there is a unique subgroup of `G` with `Nat.card H = d`. -/
theorem existsUnique_subgroup_card_eq {d : ℕ} (hd : d ∣ Nat.card G) :
    ∃! H : Subgroup G, Nat.card H = d := by
  have hcard : Nat.card (powMonoidHom d (α := G)).ker = d := by
    rw [IsCyclic.card_powMonoidHom_ker]
    exact Nat.gcd_eq_right hd
  refine ExistsUnique.intro (powMonoidHom d (α := G)).ker hcard fun K hK => ?_
  exact subgroup_eq_powMonoidHom_ker_of_card_eq K hd hK

end IsCyclic
