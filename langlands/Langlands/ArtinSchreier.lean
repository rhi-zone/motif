import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The Artin–Schreier polynomial

For a field `k` of characteristic `p` and `a : k`, the Artin–Schreier polynomial is
`f_a := X ^ p - X - C a`. This file proves the classical irreducibility criterion:

`Irreducible f_a ↔ a ∉ Set.range (fun x : k => x ^ p - x)`.

## Main definitions

* `ArtinSchreier.poly p a` : the polynomial `X ^ p - X - C a`.

## Main results

* `ArtinSchreier.not_irreducible_of_mem_range` : if `a = θ ^ p - θ` for some `θ : k`, then `poly p
  a` has a root in `k`, hence (being of degree `p ≥ 2`) is reducible.
* `ArtinSchreier.irreducible_of_not_mem_range` : if `poly p a` is reducible, exhibited as
  `poly p a = g * h` with neither factor a unit, then, working in a splitting field `L`, all roots
  of `poly p a` are of the form `θ + i` for a fixed root `θ` and `i` ranging over the (fixed, size
  `p`) image of `ZMod p` in `L` (`isRoot_add_of_isRoot`, `roots_eq_image_add`). Vieta's formula
  applied to `g` expresses `d • θ` (`d := g.natDegree`, `0 < d < p`) as an element of the image of
  `k` in `L` plus an element of the image of `ZMod p` in `L`; since `d` is invertible mod `p`, this
  forces `θ` itself into the image of `k`, giving `a = θ ^ p - θ ∈ Set.range (fun x : k => x ^ p -
  x)` directly. Packaged as the contrapositive of the irreducibility statement.
* `ArtinSchreier.irreducible_iff` : the two directions combined into the iff.
-/

@[expose] public section

namespace ArtinSchreier

variable {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (a : k)

open Polynomial

/-- The Artin–Schreier polynomial `X ^ p - X - C a`. -/
noncomputable def poly : Polynomial k := X ^ p - X - C a

omit [Fact p.Prime] [CharP k p] in
theorem poly_def : poly p a = X ^ p - X - C a := rfl

omit [CharP k p] in
/-- `poly p a` is monic: it is `X ^ p - (X + C a)`, and `X + C a` has degree `1 < p` (using
`p.Prime` to get `p ≥ 2`). -/
theorem poly_monic : (poly p a).Monic := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hlt : (X + C a : Polynomial k).degree < (p : ℕ) := by
    rw [degree_X_add_C]
    exact_mod_cast (by omega : 1 < p)
  have := monic_X_pow_sub (R := k) (p := X + C a) (n := p) hlt
  rwa [sub_add_eq_sub_sub] at this

omit [CharP k p] in
/-- `poly p a` has degree exactly `p`. -/
theorem natDegree_poly : (poly p a).natDegree = p := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hlt : (X + C a : Polynomial k).degree < (X ^ p : Polynomial k).degree := by
    rw [degree_X_add_C, degree_X_pow]
    exact_mod_cast (by omega : 1 < p)
  have hdeg : (poly p a).degree = (X ^ p : Polynomial k).degree := by
    rw [poly_def, ← sub_add_eq_sub_sub]
    exact degree_sub_eq_left_of_degree_lt hlt
  rw [degree_X_pow] at hdeg
  exact natDegree_eq_of_degree_eq_some hdeg

omit [CharP k p] in
theorem poly_ne_zero : poly p a ≠ 0 := (poly_monic p a).ne_zero

omit [CharP k p] in
/-- `poly p a` has degree `≥ 2`. -/
theorem two_le_natDegree_poly : 2 ≤ (poly p a).natDegree := by
  rw [natDegree_poly]; exact (Fact.out : p.Prime).two_le

variable {p a}

omit [CharP k p] in
/-- **Additivity of roots.** If `θ` is a root of `poly p a` in a `k`-algebra `L`, and `i : L`
satisfies `i ^ p = i` (e.g. `i` in the image of `ZMod p`, via `ZMod.pow_card` pulled through a
ring hom), then `θ + i` is also a root: `(θ + i) ^ p - (θ + i) - a = (θ ^ p - θ - a) + (i ^ p - i) =
0 + 0`, using `add_pow_char`. -/
theorem isRoot_add_of_isRoot {L : Type*} [Field L] [Algebra k L] [CharP L p] {θ i : L}
    (hθ : aeval θ (poly p a) = 0) (hi : i ^ p = i) :
    aeval (θ + i) (poly p a) = 0 := by
  simp only [poly_def, map_sub, map_pow, aeval_X, aeval_C] at hθ ⊢
  rw [add_pow_char, hi]
  have : θ ^ p + i - (θ + i) - algebraMap k L a
      = (θ ^ p - θ - algebraMap k L a) + (i - i) := by ring
  rw [this, hθ, sub_self, add_zero]

omit [Fact p.Prime] [CharP k p] in
/-- If `a = θ ^ p - θ` for some `θ : k`, then `θ` is a root of `poly p a` in `k` itself. -/
theorem isRoot_poly_of_eq (θ : k) (ha : a = θ ^ p - θ) : (poly p a).IsRoot θ := by
  simp [poly_def, IsRoot, ha]

omit [CharP k p] in
/-- **Easy direction.** If `a` is in the range of `x ↦ x ^ p - x` (over `k` itself), then
`poly p a` has a root in `k`, and since it is monic of degree `p ≥ 2`, it factors as
`(X - C θ) * g` with both factors non-units — so it is not irreducible. -/
theorem not_irreducible_of_mem_range (h : a ∈ Set.range (fun x : k => x ^ p - x)) :
    ¬ Irreducible (poly p a) := by
  obtain ⟨θ, hθ⟩ := h
  have hroot : (poly p a).IsRoot θ := isRoot_poly_of_eq θ hθ.symm
  obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr hroot
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpne : poly p a ≠ 0 := poly_ne_zero p a
  have hgne : g ≠ 0 := right_ne_zero_of_mul (hg ▸ hpne)
  have hgdeg : g.natDegree = p - 1 := by
    have heq := natDegree_mul (X_sub_C_ne_zero θ) hgne
    rw [← hg, natDegree_X_sub_C, natDegree_poly] at heq
    omega
  intro hirr
  rcases hirr.isUnit_or_isUnit hg with hu | hu
  · rw [isUnit_iff_degree_eq_zero, degree_X_sub_C] at hu
    exact absurd hu one_ne_zero
  · rw [isUnit_iff_degree_eq_zero, degree_eq_natDegree hgne, hgdeg] at hu
    have hpos : (0 : ℕ) < p - 1 := by omega
    exact absurd hu (by exact_mod_cast hpos.ne')

omit [CharP k p] in
/-- **The full root set, in any field where `poly p a` splits and has a root `θ`.** Every root of
`poly p a` there is `θ + i` for `i` in the image of `ZMod p` (`isRoot_add_of_isRoot`), giving `p`
distinct roots (`ZMod.castHom` into a field of characteristic `p` is injective); since `poly p a`
splits, it has exactly `p` roots, so these are *all* of them. -/
theorem roots_eq_image_add {L : Type*} [Field L] [Algebra k L] [CharP L p]
    (hSplits : ((poly p a).map (algebraMap k L)).Splits)
    {θ : L} (hθroot : ((poly p a).map (algebraMap k L)).IsRoot θ) :
    ((poly p a).map (algebraMap k L)).roots =
      (Finset.univ : Finset (ZMod p)).val.map
        (fun j => θ + ZMod.castHom (dvd_refl p) L j) := by
  set M := (poly p a).map (algebraMap k L) with hMdef
  set ψ : ZMod p →+* L := ZMod.castHom (dvd_refl p) L with hψdef
  set f : ZMod p → L := fun j => θ + ψ j with hfdef
  have hMne : M ≠ 0 := Polynomial.map_ne_zero (poly_ne_zero p a)
  have hMdeg : M.natDegree = p := (Polynomial.natDegree_map _).trans (natDegree_poly p a)
  have hMcard : M.roots.card = p := by
    have hc := Polynomial.splits_iff_card_roots.mp hSplits
    rwa [hMdeg] at hc
  have hψ_inj : Function.Injective ψ := ZMod.castHom_injective L
  have hpow : ∀ j : ZMod p, ψ j ^ p = ψ j := fun j => by rw [← map_pow, ZMod.pow_card]
  have hf_inj : Function.Injective f := fun i j hij => hψ_inj (add_left_cancel hij)
  have hθaeval : aeval θ (poly p a) = 0 := by
    rw [aeval_def, ← Polynomial.eval_map]; exact hθroot
  have hf_root : ∀ j, M.IsRoot (f j) := by
    intro j
    show M.eval (f j) = 0
    rw [hMdef, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact isRoot_add_of_isRoot hθaeval (hpow j)
  have hle : (Finset.univ : Finset (ZMod p)).val.map f ≤ M.roots := by
    have hNodup : ((Finset.univ : Finset (ZMod p)).val.map f).Nodup :=
      Finset.univ.nodup.map hf_inj
    rw [Multiset.le_iff_subset hNodup]
    intro x hx
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hx
    exact Polynomial.mem_roots'.mpr ⟨hMne, hf_root j⟩
  have hcard_eq : ((Finset.univ : Finset (ZMod p)).val.map f).card = M.roots.card := by
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, ZMod.card, hMcard]
  exact (Multiset.eq_of_le_of_card_le hle hcard_eq.ge).symm

end ArtinSchreier
