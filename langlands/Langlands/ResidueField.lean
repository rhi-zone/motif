import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The residue field of a valuation subring of an algebraically closed field

This file supplies the two pieces of Mathlib-level infrastructure needed to show that, for `K` a
field, `L` an algebraic closure of `K`, and `A` a `ValuationSubring L` extending `𝒪[K]`, the
residue field of `A` is an algebraic closure of the residue field of `𝒪[K]`:

* `ValuationSubring.residueField_isAlgClosed` : the residue field of *any* valuation subring `A`
  of an algebraically closed field `L` is itself algebraically closed. This is a general fact
  about valuation subrings, independent of any base field `K` or the extension being algebraic:
  given a monic irreducible polynomial `f` over the residue field `k := ResidueField A`, lift it
  to a monic polynomial `g` over `A` (possible since `A → k` is surjective), find a root `r ∈ L`
  of `g` (since `L` is algebraically closed), observe `r` is integral over `A` (witnessed by `g`
  itself) hence `r ∈ A` (since valuation subrings are integrally closed in their fraction field),
  and reduce `r` mod the maximal ideal to get a root of `f` in `k`.

* `ValuationSubring.isIntegral_of_decompositionSubgroup_eq_top` : if `L / K` is normal and
  `A : ValuationSubring L` has decomposition subgroup (over `K`) equal to all of `Gal(L/K)` --
  i.e. every `K`-automorphism of `L` stabilizes `A` setwise -- then every element of `A` is
  integral over `A.comap (algebraMap K L)`. The proof uses that the minimal polynomial of
  `a ∈ A` over `K` has *all* of its roots (in `L`, with multiplicity) lying in `A` again: each
  root is `σ a` for some `σ ∈ Gal(L/K)` (`minpoly.exists_algEquiv_of_root'`, using normality of
  `L/K`), and `σ` stabilizes `A` by hypothesis. Since the roots all lie in `A`, so do the
  (symmetric-function) coefficients of the minimal polynomial, i.e. it lifts along
  `A.comap (algebraMap K L) → A` (`Polynomial.Splits.mem_lift_of_roots_mem_range`), which is
  exactly the integrality of `a` over `A.comap (algebraMap K L)`.

Combining these two (with `A.comap (algebraMap K L) = 𝒪[K]`) gives the two facts needed for
`Langlands.WeilGroup.residueField_isAlgClosed` / `residueField_isAlgebraic`: every element of the
residue field of `A` is (the residue of an element of `A`, which is) integral over `𝒪[K]`, hence
algebraic over `𝓀[K]`; and the residue field of `A` is algebraically closed.

## Main results

* `ValuationSubring.residueField_isAlgClosed`
* `ValuationSubring.isIntegral_of_decompositionSubgroup_eq_top`
* `ValuationSubring.residueField_isAlgebraic_of_decompositionSubgroup_eq_top` : the residue field
  algebraicity statement, packaging the integrality result above with the standard fact that
  integral elements have algebraic residues.
-/

noncomputable section

open Polynomial IsLocalRing

open scoped Pointwise

namespace ValuationSubring

/-! ### The residue field of a valuation subring of an algebraically closed field is algebraically
closed -/

section AlgClosed

variable {L : Type*} [Field L] [IsAlgClosed L]

/-- The residue field of a valuation subring `A` of an algebraically closed field `L` is itself
algebraically closed. A general fact about valuation rings, not needing any base field `K`. -/
theorem residueField_isAlgClosed (A : ValuationSubring L) :
    IsAlgClosed (ResidueField A) := by
  apply IsAlgClosed.of_exists_root
  intro f hfmonic hfirred
  -- Lift `f` to a monic polynomial `g` over `A`, along the (surjective) residue map.
  have hlifts : f ∈ Polynomial.lifts (residue A) :=
    Polynomial.mem_lifts_of_surjective residue_surjective f
  obtain ⟨g, hgmap, hgnatdeg, hgmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts hfmonic
  -- `g`, viewed inside `L`, still has positive degree, hence (being monic) a nonzero degree.
  have hfdeg : 0 < f.degree := Polynomial.degree_pos_of_irreducible hfirred
  have hfnatdeg : 0 < f.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr hfdeg
  have hAL_inj : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  set g' : L[X] := g.map (algebraMap A L) with hg'def
  have hg'natdeg : g'.natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hAL_inj g
  have hg'monic : g'.Monic := hgmonic.map _
  have hg'deg : g'.degree ≠ 0 := by
    have : 0 < g'.natDegree := by rw [hg'natdeg, hgnatdeg]; exact hfnatdeg
    exact (Polynomial.natDegree_pos_iff_degree_pos.mp this).ne'
  -- `L` is algebraically closed, so `g'` has a root `r`.
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root g' hg'deg
  have hr' : (g.map (algebraMap A L)).eval r = 0 := hr
  rw [Polynomial.eval_map] at hr'
  -- `r` is integral over `A` (witnessed by the monic `g`), hence lies in `A` (integrally closed).
  have hrint : IsIntegral A r := ⟨g, hgmonic, hr'⟩
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff L).mp inferInstance hrint
  -- Reduce `y` mod the maximal ideal to get a root of `f`.
  refine ⟨residue A y, ?_⟩
  show f.eval (residue A y) = 0
  have hgy : g.eval₂ (algebraMap A L) (algebraMap A L y) = 0 := hy ▸ hr'
  rw [Polynomial.eval₂_at_apply] at hgy
  have hgy0 : g.eval y = 0 := hAL_inj (by simpa using hgy)
  have : g.eval₂ (residue A) (residue A y) = 0 := by
    rw [Polynomial.eval₂_at_apply, hgy0, map_zero]
  rwa [← Polynomial.eval_map, hgmap] at this

end AlgClosed

/-! ### Integrality of elements of a Galois-stable valuation subring over the base -/

section Integral

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L]

/-- If `A : ValuationSubring L` has decomposition subgroup (over `K`) equal to all of `Gal(L/K)`,
every root (in `L`, with multiplicity) of the minimal polynomial over `K` of an element `a ∈ A`
again lies in `A`: it is `σ a` for some `σ : L ≃ₐ[K] L` (`minpoly.exists_algEquiv_of_root'`, using
that `L / K` is normal), and `σ` stabilizes `A` setwise since the decomposition subgroup is
everything. -/
theorem root_mem_of_decompositionSubgroup_eq_top (A : ValuationSubring L)
    (htop : A.decompositionSubgroup K = ⊤) {a : L} (ha : a ∈ A)
    {r : L} (hr : r ∈ ((minpoly K a).map (algebraMap K L)).roots) : r ∈ A := by
  have haK : IsAlgebraic K a := Algebra.IsAlgebraic.isAlgebraic a
  have hr0 : Polynomial.aeval r (minpoly K a) = 0 := by
    have hmem := (Polynomial.mem_roots'.mp hr).2
    rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hmem
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' haK hr0
  have hσmem : σ ∈ A.decompositionSubgroup K := htop ▸ Subgroup.mem_top σ
  have hstab : σ • A = A := MulAction.mem_stabilizer_iff.mp hσmem
  have hr_smul : σ • a = r := by rw [AlgEquiv.smul_def]; exact hσ
  have hσa : σ⁻¹ • r = a := by rw [← hr_smul, inv_smul_smul]
  have : σ⁻¹ • r ∈ A := hσa ▸ ha
  rwa [← ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hstab] at this

/-- If `A : ValuationSubring L` has decomposition subgroup (over `K`) equal to all of `Gal(L/K)`,
i.e. every `K`-automorphism of `L` stabilizes `A` setwise, then every element of `A` is integral
over `A.comap (algebraMap K L)` -- concretely, this is stated via `RingHom.IsIntegralElem` for the
canonical ring homomorphism `A.comap (algebraMap K L) → K → L` (composing the inclusion of the
comapped valuation subring into `K` with `algebraMap K L`), to avoid needing to fix a particular
`Algebra` instance between `A.comap (algebraMap K L)` and `L`. -/
theorem isIntegralElem_of_decompositionSubgroup_eq_top (A : ValuationSubring L)
    (htop : A.decompositionSubgroup K = ⊤) {a : L} (ha : a ∈ A) :
    RingHom.IsIntegralElem
      ((algebraMap K L).comp (algebraMap (A.comap (algebraMap K L)) K)) a := by
  set O := A.comap (algebraMap K L) with hOdef
  have haK : IsAlgebraic K a := Algebra.IsAlgebraic.isAlgebraic a
  set p : K[X] := minpoly K a with hpdef
  have hpmonic : p.Monic := minpoly.monic haK.isIntegral
  have hpsplits : (p.map (algebraMap K L)).Splits := Normal.splits inferInstance a
  -- `Set.range (algebraMap A L)` is literally the underlying set of `A`.
  have hrangeA : ∀ x : L, x ∈ Set.range (algebraMap A L) ↔ x ∈ A :=
    fun x => ⟨fun ⟨b, hb⟩ => hb ▸ b.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  -- Every root of `p` in `L` lies in `A`.
  have hrootsA : ∀ r ∈ (p.map (algebraMap K L)).roots, r ∈ Set.range (algebraMap A L) :=
    fun r hr => (hrangeA r).mpr (root_mem_of_decompositionSubgroup_eq_top A htop ha hr)
  -- So `p`, mapped to `L`, lifts along `A → L`; hence its coefficients (already known to lie in
  -- `K`) lie in `A ∩ K = O` (as subsets of `L`, via `A.comap (algebraMap K L) = O`).
  have hliftsA : p.map (algebraMap K L) ∈ Polynomial.lifts (algebraMap A L) :=
    hpsplits.mem_lift_of_roots_mem_range (hpmonic.map _) (algebraMap A L) hrootsA
  have hcoeffO : ∀ n, p.coeff n ∈ O := by
    intro n
    have hmem := (Polynomial.lifts_iff_coeff_lifts _).mp hliftsA n
    rw [Polynomial.coeff_map] at hmem
    exact ValuationSubring.mem_comap.mpr ((hrangeA _).mp hmem)
  have hrangeO : ∀ x : K, x ∈ Set.range (algebraMap O K) ↔ x ∈ O :=
    fun x => ⟨fun ⟨b, hb⟩ => hb ▸ b.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hliftsO : p ∈ Polynomial.lifts (algebraMap O K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => (hrangeO _).mpr (hcoeffO n)
  obtain ⟨q, hqmap, _, hqmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hliftsO hpmonic
  refine ⟨q, hqmonic, ?_⟩
  have heval : p.eval₂ (algebraMap K L) a = 0 := by
    rw [← Polynomial.aeval_def]; exact minpoly.aeval K a
  rw [← Polynomial.eval₂_map, hqmap]
  exact heval

end Integral

end ValuationSubring

/-! ### The residue of an integral element is algebraic -/

/-- If `x : S` is integral over a local subring `R` (with the inclusion `R → S` a local
homomorphism), then the residue of `x` is algebraic over the residue field of `R`. Standard
"reduction mod the maximal ideal" fact: a monic polynomial over `R` witnessing integrality of `x`
reduces, mod the maximal ideal, to a monic (in particular nonzero) polynomial over
`ResidueField R` witnessing algebraicity of the residue of `x`. -/
theorem IsIntegral.isAlgebraic_residue {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] {x : S} (hx : IsIntegral R x) :
    IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.residue S x) := by
  have hcomp : (IsLocalRing.residue S).comp (algebraMap R S) =
      (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)).comp
        (IsLocalRing.residue R) :=
    RingHom.ext fun r => (IsLocalRing.ResidueField.algebraMap_residue r).symm
  have hx' := RingHom.IsIntegralElem.map hx (IsLocalRing.residue S)
  rw [hcomp] at hx'
  obtain ⟨q, hqmonic, hqeval⟩ := hx'
  have hqeval' :
      (q.map (IsLocalRing.residue R)).eval₂
        (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
        (IsLocalRing.residue S x) = 0 := by
    rw [Polynomial.eval₂_map]; exact hqeval
  exact ⟨q.map (IsLocalRing.residue R), (hqmonic.map _).ne_zero, by
    rw [Polynomial.aeval_def]; exact hqeval'⟩
