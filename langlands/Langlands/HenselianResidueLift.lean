/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.SimpleRootRigidity
import Langlands.UnramifiedExtension

/-!
# Lifting a residue-field element to a root *inside* a fixed Henselian local ring

`Langlands.UnramifiedExtension` builds an unramified extension realizing a prescribed residue
extension, but it does so inside an *auxiliary* algebraically closed field: its
`HenselianLocalRing.exists_isDiscreteValuationRing_integralClosure_residueField_equiv` produces
`AdjoinRoot f` and embeds it via `IsAlgClosed.exists_root`, so the resulting extension is never
identified with a subobject of a field already fixed by the caller. That is an obstruction for
`Langlands.RamificationFiltration`'s kernel argument, which needs the root to live inside a ring
already fixed by the caller.

This file takes the other route: apply Hensel's lemma **directly to the target ring** — for which
`IsDedekindDomain.HeightOneSpectrum.henselianLocalRing_adicCompletionIntegers`
(`Langlands.RamificationFiltrationAdicCompletion`) supplies
the `HenselianLocalRing` instance — in its *simple-root* form, `HenselianLocalRing.TFAE`'s second
item. No ambient algebraically closed field appears anywhere below, and the root produced is an
element of the given ring `R`, not of some newly built algebra.

## Main results

* `HenselianLocalRing.exists_isRoot_residue_eq` : for `R` Henselian local over a local ring `R₀`
  with compatible residue maps, and `β₀` an element of `ResidueField R` whose minimal polynomial
  over `ResidueField R₀` is separable, there are a monic `f : R₀[X]` lifting that minimal
  polynomial and an `x : R` with `aeval x f = 0`, `residue R x = β₀`, and `aeval x (derivative f)`
  a unit — i.e. `x` is a *simple* root, which is what makes it rigid (see
  `IsLocalRing.eq_of_isRoot_of_residue_eq`).
* `HenselianLocalRing.exists_isRoot_residue_eq_of_finite` : the specialization to finite residue
  fields, where separability is automatic (`PerfectField.ofFinite`) and a generator `β₀` of
  `ResidueField R` over `ResidueField R₀` exists (`Field.exists_primitive_element_of_finite_top`).

## Implementation notes

The compatibility of the two residue maps is taken as an explicit hypothesis (`hsq`) rather than
derived from an `IsLocalHom` instance, because at the intended call site
(`Langlands.RamificationFiltrationAdicCompletion`) the `Algebra (ResidueField K₀) (ResidueField L₀)`
instance is the one built in `Langlands.ResidueFieldNorm` out of `Valuation.HasExtension`, and
`Langlands.ResidueFieldNorm.algebraMap_residueField_residue` is exactly `hsq` for it. Passing it
explicitly avoids re-deriving — and possibly diverging from — that instance.
-/

noncomputable section

open Polynomial IsLocalRing

/-! ### Evaluating a base polynomial in the residue field -/

/-- With compatible residue maps (`hsq`), evaluating the image in `R[X]` of a base polynomial at a
point of `ResidueField R` is the same as evaluating its image in `(ResidueField R₀)[X]`: the two
routes `R₀ → R → ResidueField R` and `R₀ → ResidueField R₀ → ResidueField R` agree. -/
theorem IsLocalRing.aeval_map_residue_eq {R₀ R : Type*} [CommRing R₀] [IsLocalRing R₀] [CommRing R]
    [IsLocalRing R] [Algebra R₀ R] [Algebra (ResidueField R₀) (ResidueField R)]
    (hsq : ∀ a : R₀, algebraMap (ResidueField R₀) (ResidueField R) (residue R₀ a)
      = residue R (algebraMap R₀ R a))
    (p : R₀[X]) (b : ResidueField R) :
    aeval b (p.map (algebraMap R₀ R)) = aeval b (p.map (algebraMap R₀ (ResidueField R₀))) := by
  have hcomp : (algebraMap (ResidueField R₀) (ResidueField R)).comp
      (algebraMap R₀ (ResidueField R₀)) =
      (algebraMap R (ResidueField R)).comp (algebraMap R₀ R) := by
    refine RingHom.ext fun a => ?_
    simpa only [RingHom.coe_comp, Function.comp_apply, ResidueField.algebraMap_eq] using hsq a
  rw [aeval_def, aeval_def, ← Polynomial.eval_map, ← Polynomial.eval_map, Polynomial.map_map,
    Polynomial.map_map, hcomp]

namespace HenselianLocalRing

/-! ### The lift -/

variable {R₀ R : Type*} [CommRing R₀] [IsLocalRing R₀] [CommRing R] [HenselianLocalRing R]
  [Algebra R₀ R] [Algebra (ResidueField R₀) (ResidueField R)]

/-- **A root with prescribed residue, inside the given Henselian local ring `R`.**

Let `R₀` be a local ring, `R` a Henselian local `R₀`-algebra whose residue map is compatible with
that of `R₀` (`hsq`), and `β₀ : ResidueField R` an element integral over `ResidueField R₀` whose
minimal polynomial is separable. Then a monic lift `f : R₀[X]` of that minimal polynomial has a
root `x` in `R` itself with `residue R x = β₀`, and that root is *simple*
(`IsUnit (aeval x (derivative f))`).

The proof is exactly the second item of `HenselianLocalRing.TFAE`: `β₀` is a simple root of the
reduction of `f.map (algebraMap R₀ R)` — simple because `minpoly (ResidueField R₀) β₀` is separable
and so has nonvanishing derivative at its own root (`Polynomial.Separable.aeval_derivative_ne_zero`)
— and Henselianity lifts a simple root of the reduction to an honest root of `f` in `R`. Note that
`R` is *given*, not constructed: nothing here builds a new ring or embeds into an algebraically
closed field. -/
theorem exists_isRoot_residue_eq
    (hsq : ∀ a : R₀, algebraMap (ResidueField R₀) (ResidueField R) (residue R₀ a)
      = residue R (algebraMap R₀ R a))
    {β₀ : ResidueField R} (hβ₀ : IsIntegral (ResidueField R₀) β₀)
    (hsep : (minpoly (ResidueField R₀) β₀).Separable) :
    ∃ f : R₀[X], f.Monic ∧
      f.map (algebraMap R₀ (ResidueField R₀)) = minpoly (ResidueField R₀) β₀ ∧
      ∃ x : R, aeval x f = 0 ∧ residue R x = β₀ ∧ IsUnit (aeval x (derivative f)) := by
  obtain ⟨f, hfmonic, -, hfmap⟩ := HenselianLocalRing.exists_monic_lift_minpoly hβ₀
  refine ⟨f, hfmonic, hfmap, ?_⟩
  have key : ∀ p : R₀[X], aeval β₀ (p.map (algebraMap R₀ R))
      = aeval β₀ (p.map (algebraMap R₀ (ResidueField R₀))) := fun p =>
    IsLocalRing.aeval_map_residue_eq hsq p β₀
  set g : R[X] := f.map (algebraMap R₀ R) with hg
  have hgmonic : g.Monic := hfmonic.map _
  have h1 : aeval β₀ g = 0 := by rw [hg, key f, hfmap]; exact minpoly.aeval _ _
  have hderiv : derivative g = (derivative f).map (algebraMap R₀ R) := by
    rw [hg, Polynomial.derivative_map]
  have h2 : aeval β₀ (derivative g) ≠ 0 := by
    rw [hderiv, key (derivative f), ← Polynomial.derivative_map, hfmap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  have hhens : ∀ p : R[X], p.Monic → ∀ a₀ : ResidueField R, aeval a₀ p = 0 →
      aeval a₀ (derivative p) ≠ 0 → ∃ a : R, p.IsRoot a ∧ residue R a = a₀ :=
    ((HenselianLocalRing.TFAE R).out 0 1).mp ‹HenselianLocalRing R›
  obtain ⟨x, hxroot, hxres⟩ := hhens g hgmonic β₀ h1 h2
  refine ⟨x, ?_, hxres, ?_⟩
  · rw [aeval_def, ← Polynomial.eval_map]; exact hxroot
  · refine IsLocalRing.isUnit_of_residue_ne_zero ?_
    have hev : aeval x (derivative f) = (derivative g).eval x := by
      rw [hderiv, aeval_def, ← Polynomial.eval_map]
    rw [hev, IsLocalRing.residue_eval, hxres]
    exact h2

/-! ### The finite-residue-field case -/

/-- **The finite-residue-field specialization.** If `ResidueField R` is finite, it has a primitive
element `β₀` over `ResidueField R₀` (`Field.exists_primitive_element_of_finite_top`), integrality
and separability of whose minimal polynomial are automatic — `ResidueField R₀` is finite, hence
perfect (`PerfectField.ofFinite`), so every irreducible polynomial over it is separable.

The generation statement is recorded in `Subalgebra` form, `Algebra.adjoin (ResidueField R₀) {β₀} =
⊤` (`IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic` converts), because that is the form
in which it makes the subring `R₀[x] ⊆ R` surject onto `ResidueField R` — the input to the Nakayama
argument of `Langlands.TwoGeneratorMonogenic`. -/
theorem exists_isRoot_residue_eq_of_finite [Finite (ResidueField R)]
    (hsq : ∀ a : R₀, algebraMap (ResidueField R₀) (ResidueField R) (residue R₀ a)
      = residue R (algebraMap R₀ R a)) :
    ∃ (β₀ : ResidueField R),
      Algebra.adjoin (ResidueField R₀) ({β₀} : Set (ResidueField R)) = ⊤ ∧
      ∃ f : R₀[X], f.Monic ∧
        f.map (algebraMap R₀ (ResidueField R₀)) = minpoly (ResidueField R₀) β₀ ∧
        ∃ x : R, aeval x f = 0 ∧ residue R x = β₀ ∧ IsUnit (aeval x (derivative f)) := by
  haveI : Finite (ResidueField R₀) :=
    Finite.of_injective (algebraMap (ResidueField R₀) (ResidueField R))
      (algebraMap (ResidueField R₀) (ResidueField R)).injective
  obtain ⟨β₀, hβ₀top⟩ :=
    Field.exists_primitive_element_of_finite_top (ResidueField R₀) (ResidueField R)
  haveI : PerfectField (ResidueField R₀) := PerfectField.ofFinite
  haveI : Algebra.IsIntegral (ResidueField R₀) (ResidueField R) := Algebra.IsIntegral.of_finite _ _
  have hβ₀ : IsIntegral (ResidueField R₀) β₀ := Algebra.IsIntegral.isIntegral β₀
  have hsep : (minpoly (ResidueField R₀) β₀).Separable :=
    PerfectField.separable_of_irreducible (minpoly.irreducible hβ₀)
  have hadj : Algebra.adjoin (ResidueField R₀) ({β₀} : Set (ResidueField R)) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβ₀.isAlgebraic, hβ₀top,
      IntermediateField.top_toSubalgebra]
  exact ⟨β₀, hadj, exists_isRoot_residue_eq hsq hβ₀ hsep⟩

end HenselianLocalRing

end
