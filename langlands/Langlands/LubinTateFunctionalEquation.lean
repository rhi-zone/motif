import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Langlands.LubinTate

/-!
# Toward the Lubin-Tate functional equation lemma: the residue-field congruence

This file starts the second, genuinely deep stage of the Lubin-Tate thread opened in
`Langlands/LubinTate.lean`: the **functional equation lemma**. That lemma builds, for
`f, g ∈ ℱ_π` and a linear starting form, a power series intertwining `f` and `g` by solving one
linear equation in `O` per total-degree step. This file proves the single load-bearing fact that
makes every one of those steps solvable: reducing mod `π`, `f` and `g` act identically (as the
Frobenius-twisted `q`-th power map) on *any* power series with zero constant term, so the
degree-by-degree obstruction in the functional equation lemma's recursion is *always* divisible by
`π`, unconditionally (not merely once earlier degrees are known to already satisfy the equation).

## Main results

* `residueCharP`, `residueDegree`, `card_residueField_eq` : the residue characteristic `p` and the
  degree `n` with `residueCard O = p ^ n`, packaged the same way `Langlands/WeilGroup.lean` already
  does for `𝓀[K]` (`WeilGroup.residueCharP`/`residueDegree`/`card_residueField_eq`), specialized to
  `ResidueField O`.
* `pow_residueCard_eq_subst_X_pow` : for `h` a power series over the (finite) residue field,
  `h ^ residueCard O = h.subst (X ^ residueCard O)` — the Frobenius/Frobenius-iterate identity
  `h(X)^q = h(X^q)` valid for *any* `h`, coming from `MvPowerSeries.map_iterateFrobenius_expand`
  together with the Fermat/`FiniteField.pow_card` fact that the iterated Frobenius `x ↦ x ^ q` is
  the identity on a field with exactly `q` elements.
* `map_residue_subst_eq_map_residue_subst` : for `f, g ∈ ℱ_π` and any `φ : O⟦X⟧` with
  `coeff 0 φ = 0` (so `f.subst φ` and `φ.subst g` are both defined), reducing mod `π` gives
  `map (residue O) (f.subst φ) = map (residue O) (φ.subst g)`. Both sides reduce to
  `(map (residue O) φ) ^ residueCard O`, using `f ≡ X^q ≡ g (mod π)` on one side and
  `pow_residueCard_eq_subst_X_pow` on the other. Crucially this holds for *every* admissible `φ`,
  not just ones already known to approximately intertwine `f` and `g` — this is what removes the
  need for an interleaved recursion/correctness induction when this lemma is used to build the
  functional equation lemma's intertwining power series degree by degree.
* `uniformizer_dvd_coeff_subst_sub_subst` : the coefficient-wise consequence,
  `π ∣ coeff n (φ.subst g) - coeff n (f.subst φ)` for every `n`, obtained from
  `map_residue_subst_eq_map_residue_subst` via `IsLocalRing.residue_eq_zero_iff` and
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`.

## What this does not yet do

The functional equation lemma's existence half — assembling a power series `φ` satisfying
`f.subst φ = φ.subst g` and `φ ≡ (linear form) mod deg 2`, by choosing `coeff n φ` degree by degree
using `uniformizer_dvd_coeff_subst_sub_subst` to divide by `π` and
`IsLocalRing.isUnit_one_sub_self_of_mem_nonunits` to invert the unit factor `1 - π^(n-1)` in the
degree-`n` coefficient `π - π^n = π·(1 - π^(n-1))` of the recursion — is not attempted in this file.
-/

@[expose] public section

noncomputable section

open PowerSeries IsLocalRing

namespace LubinTate

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

instance : Fintype (ResidueField O) := Fintype.ofFinite _

/-- The residue characteristic of `O`, i.e. the characteristic of `ResidueField O`. Packaged the
same way `WeilGroup.residueCharP` is, specialized to `ResidueField O` in place of `𝓀[K]`. -/
def residueCharP (O : Type*) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] : ℕ :=
  ringChar (ResidueField O)

instance : CharP (ResidueField O) (residueCharP O) := ringChar.charP _

instance residueCharP_fact : Fact (residueCharP O).Prime :=
  ⟨CharP.char_is_prime (ResidueField O) _⟩

instance : ExpChar (ResidueField O) (residueCharP O) :=
  .prime (residueCharP_fact (O := O)).out

/-- The degree of `ResidueField O` over its prime field, i.e. the `n` with
`residueCard O = residueCharP O ^ n` (`card_residueField_eq`). -/
def residueDegree (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] : ℕ+ :=
  (FiniteField.card (ResidueField O) (residueCharP O)).choose

theorem card_residueField_eq :
    residueCard O = (residueCharP O) ^ (residueDegree O : ℕ) := by
  rw [residueCard, Nat.card_eq_fintype_card]
  exact (FiniteField.card (ResidueField O) (residueCharP O)).choose_spec.2

/-- The iterated Frobenius `x ↦ x ^ residueCard O` fixes every element of `ResidueField O`
(Fermat's little theorem for finite fields, `FiniteField.pow_card`), so as a ring homomorphism it
is the identity. -/
theorem iterateFrobenius_residueField_eq_id :
    iterateFrobenius (ResidueField O) (residueCharP O) (residueDegree O : ℕ) =
      RingHom.id (ResidueField O) := by
  have hcard : Fintype.card (ResidueField O) = (residueCharP O) ^ (residueDegree O : ℕ) := by
    rw [← Nat.card_eq_fintype_card]; exact card_residueField_eq
  ext x
  rw [iterateFrobenius_def, RingHom.id_apply, ← hcard]
  exact FiniteField.pow_card x

/-- **The Frobenius/`q`-th-power identity for power series over the residue field.** For *any*
power series `h` over the finite residue field `ResidueField O`, `h(X)^q = h(X^q)` where
`q = residueCard O`: raising `h` to the `q`-th power is the same as substituting `X^q` for `X`.
This is the Frobenius-iterate fact `MvPowerSeries.map_iterateFrobenius_expand`, specialized using
that the iterated Frobenius is the identity on `ResidueField O`
(`iterateFrobenius_residueField_eq_id`). -/
theorem pow_residueCard_eq_subst_X_pow (h : (ResidueField O)⟦X⟧) :
    h ^ residueCard O = PowerSeries.subst (X ^ residueCard O) h := by
  have hp : (residueCharP O) ≠ 0 := (residueCharP_fact (O := O)).out.ne_zero
  have hcard : residueCard O = residueCharP O ^ (residueDegree O : ℕ) := card_residueField_eq
  rw [hcard]
  have key := MvPowerSeries.map_iterateFrobenius_expand (σ := Unit) (R := ResidueField O)
    (residueCharP O) hp h (residueDegree O : ℕ)
  rw [iterateFrobenius_residueField_eq_id, MvPowerSeries.map_id, RingHom.id_apply] at key
  rw [← key]
  exact PowerSeries.expand_apply _ (pow_ne_zero _ hp) h

/-- **The residue-field congruence underlying the functional equation lemma's recursion.** For
`f, g ∈ ℱ_π` (same `π`, `q`) and *any* `φ : O⟦X⟧` with zero constant term, `f(φ(X))` and `φ(g(X))`
agree mod `π`. Both sides reduce, mod `π`, to `(φ mod π) ^ q`: the left via `f ≡ X^q (mod π)`
(direct substitution), the right via `g ≡ X^q (mod π)` together with the Frobenius identity
`pow_residueCard_eq_subst_X_pow`. This holds unconditionally for every admissible `φ`, not only
for `φ` already known to approximately intertwine `f` and `g`. -/
theorem map_residue_subst_eq_map_residue_subst {π : O} {f g φ : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) (hg : IsLubinTatePoly π (residueCard O) g)
    (hφ0 : coeff 0 φ = 0) :
    PowerSeries.map (residue O) (f.subst φ) = PowerSeries.map (residue O) (φ.subst g) := by
  have hφ0' : constantCoeff φ = 0 := by rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hφ0
  have hg0' : constantCoeff g = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hg.1
  have hφ : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero' hφ0'
  have hg' : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' hg0'
  have hgmap : MvPowerSeries.map (residue O) g = (X : (ResidueField O)⟦X⟧) ^ residueCard O :=
    hg.2.2
  have e1 := PowerSeries.map_subst (S := ResidueField O) hφ (h := residue O) f
  have e2 := PowerSeries.map_subst (S := ResidueField O) hg' (h := residue O) φ
  rw [hf.2.2] at e1
  rw [hgmap] at e2
  rw [show PowerSeries.map (residue O) (f.subst φ) = _ from e1,
    show PowerSeries.map (residue O) (φ.subst g) = _ from e2]
  have hφmap0 : MvPowerSeries.constantCoeff (MvPowerSeries.map (residue O) φ) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, show MvPowerSeries.constantCoeff φ = (0 : O) from hφ0',
      map_zero]
  have hφmapSubst : PowerSeries.HasSubst (MvPowerSeries.map (residue O) φ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hφmap0
  rw [PowerSeries.subst_pow hφmapSubst, PowerSeries.subst_X hφmapSubst]
  exact pow_residueCard_eq_subst_X_pow (O := O) (MvPowerSeries.map (residue O) φ)

/-- The coefficient-wise consequence of `map_residue_subst_eq_map_residue_subst`: for `f, g ∈ ℱ_π`
and any admissible `φ`, every coefficient of `φ.subst g - f.subst φ` is divisible by `π`. This is
exactly the solvability fact the functional equation lemma's degree-by-degree recursion needs at
every step, and it holds unconditionally (see the module docstring). -/
theorem uniformizer_dvd_coeff_subst_sub_subst {π : O} (hπ : Irreducible π)
    {f g φ : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    (hg : IsLubinTatePoly π (residueCard O) g) (hφ0 : coeff 0 φ = 0) (n : ℕ) :
    π ∣ (coeff n (φ.subst g) - coeff n (f.subst φ)) := by
  have huni : IsLocalRing.maximalIdeal O = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  rw [← Ideal.mem_span_singleton, ← huni, ← residue_eq_zero_iff]
  have := map_residue_subst_eq_map_residue_subst hf hg hφ0
  have hcoeff : PowerSeries.coeff n (PowerSeries.map (residue O) (φ.subst g)) =
      PowerSeries.coeff n (PowerSeries.map (residue O) (f.subst φ)) := by rw [this]
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map] at hcoeff
  rw [map_sub, hcoeff, sub_self]

end LubinTate

end
