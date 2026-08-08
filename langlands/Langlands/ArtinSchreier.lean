import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
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

open Polynomial IntermediateField

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

/-- **Hard direction.** If `poly p a` is reducible, `a` lies in the range of `x ↦ x ^ p - x`.
Proved as the contrapositive of `irreducible_of_not_mem_range`. Given `poly p a = g * h'` with
neither factor a unit, work in the splitting field `L`: with `θ` a root and `d := g.natDegree`
(so `0 < d < p`), the roots of `g.map (algebraMap k L)` form a submultiset `t` of the full root set
`{θ + i}` of size exactly `d` (`Polynomial.roots_mul` plus a degree count forces the split between
`g` and `h'`'s roots to match their degrees exactly). Vieta's formula
(`Polynomial.multiset_prod_X_sub_C_coeff_card_pred`) expresses `g.map`'s `(d-1)`-th coefficient as
`-t.sum`; writing `t` as the image under `θ + ψ ·` of a size-`d` multiset `u ⊆ ZMod p` (`ψ` the
canonical map `ZMod p → L`) gives `t.sum = d • θ + ψ u.sum`. Since `g.map`'s `(d-1)`-th coefficient
is `algebraMap k L (g.coeff (d-1))` and `ψ u.sum = algebraMap k L (ψ₀ u.sum)` (`ψ₀` the analogous
map into `k`, agreeing with `ψ` after `algebraMap k L` by `RingHom.ext_zmod`), solving the resulting
linear equation for `θ` — using `c₀ * (d : k) ≠ 0` since `g.leadingCoeff ≠ 0` and `0 < d < p` — puts
`θ` itself in the image of `algebraMap k L`, i.e. `θ = algebraMap k L θ₀`. Then `θ₀` is a root of
`poly p a` in `k` (`Polynomial.aeval_algebraMap_eq_zero_iff_of_injective`), giving
`a = θ₀ ^ p - θ₀ ∈ Set.range (fun x : k => x ^ p - x)`. -/
theorem irreducible_of_not_mem_range (h : a ∉ Set.range (fun x : k => x ^ p - x)) :
    Irreducible (poly p a) := by
  by_contra hnI
  apply h
  have hpne : poly p a ≠ 0 := poly_ne_zero p a
  have hnu : ¬ IsUnit (poly p a) := by
    rw [isUnit_iff_degree_eq_zero, degree_eq_natDegree hpne, natDegree_poly]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hH : ¬ ∀ g h', poly p a = g * h' → IsUnit g ∨ IsUnit h' := fun H => hnI ⟨hnu, H⟩
  push Not at hH
  obtain ⟨g, h', hgh, hgu, hhu⟩ := hH
  have hgne : g ≠ 0 := left_ne_zero_of_mul (hgh ▸ hpne)
  have hhne : h' ≠ 0 := right_ne_zero_of_mul (hgh ▸ hpne)
  have hdedeg : g.natDegree + h'.natDegree = p := by
    have heq := natDegree_mul hgne hhne
    rw [← hgh, natDegree_poly] at heq
    omega
  have hd_pos : 0 < g.natDegree := by
    by_contra hc0
    apply hgu
    rw [isUnit_iff_degree_eq_zero, degree_eq_natDegree hgne]
    have : g.natDegree = 0 := by omega
    simp [this]
  have he_pos : 0 < h'.natDegree := by
    by_contra hc0
    apply hhu
    rw [isUnit_iff_degree_eq_zero, degree_eq_natDegree hhne]
    have : h'.natDegree = 0 := by omega
    simp [this]
  set d := g.natDegree with hddef
  have hd_lt : d < p := by omega
  set L := (poly p a).SplittingField
  set M := (poly p a).map (algebraMap k L) with hMdef
  have hMsplits : M.Splits := Polynomial.SplittingField.splits (poly p a)
  have hMne : M ≠ 0 := Polynomial.map_ne_zero hpne
  have hMdeg : M.natDegree = p := (Polynomial.natDegree_map _).trans (natDegree_poly p a)
  have hMcard : M.roots.card = p := by
    have hc := Polynomial.splits_iff_card_roots.mp hMsplits
    rwa [hMdeg] at hc
  have hMpos : 0 < M.roots.card := by rw [hMcard]; exact (Fact.out : p.Prime).pos
  obtain ⟨θ, hθmem⟩ := Multiset.card_pos_iff_exists_mem.mp hMpos
  have hθroot : M.IsRoot θ := (Polynomial.mem_roots'.mp hθmem).2
  have hθaeval : aeval θ (poly p a) = 0 := by
    rw [aeval_def, ← Polynomial.eval_map]; exact hθroot
  have hMroots_eq := roots_eq_image_add hMsplits hθroot
  set ψ : ZMod p →+* L := ZMod.castHom (dvd_refl p) L with hψdef
  set f : ZMod p → L := fun j => θ + ψ j with hfdef
  have hψ_inj : Function.Injective ψ := ZMod.castHom_injective L
  have hf_inj : Function.Injective f := fun i j hij => hψ_inj (add_left_cancel hij)
  have hgmap_hmap : M = g.map (algebraMap k L) * h'.map (algebraMap k L) := by
    have hcm := congrArg (Polynomial.map (algebraMap k L)) hgh
    rw [Polynomial.map_mul] at hcm
    rw [hMdef]; exact hcm
  have hprod_ne : g.map (algebraMap k L) * h'.map (algebraMap k L) ≠ 0 := hgmap_hmap ▸ hMne
  have hrootsmul : M.roots = (g.map (algebraMap k L)).roots + (h'.map (algebraMap k L)).roots := by
    rw [hgmap_hmap]; exact Polynomial.roots_mul hprod_ne
  have hgdeg_map : (g.map (algebraMap k L)).natDegree = d := Polynomial.natDegree_map _
  have hhdeg_map : (h'.map (algebraMap k L)).natDegree = h'.natDegree := Polynomial.natDegree_map _
  have hgcard_le : (g.map (algebraMap k L)).roots.card ≤ d :=
    hgdeg_map ▸ Polynomial.card_roots' _
  have hhcard_le : (h'.map (algebraMap k L)).roots.card ≤ h'.natDegree :=
    hhdeg_map ▸ Polynomial.card_roots' _
  have hcard_sum :
      (g.map (algebraMap k L)).roots.card + (h'.map (algebraMap k L)).roots.card = p := by
    have hcs := congrArg Multiset.card hrootsmul
    rw [Multiset.card_add, hMcard] at hcs
    omega
  have hgcard_eq : (g.map (algebraMap k L)).roots.card = d := by omega
  set t := (g.map (algebraMap k L)).roots with htdef
  have ht_le : t ≤ M.roots := hrootsmul ▸ Multiset.le_add_right _ _
  have ht_le' : t ≤ (Finset.univ : Finset (ZMod p)).val.map f := hMroots_eq ▸ ht_le
  set u := t.map (Function.invFun f) with hudef
  have hu_card : u.card = d := by rw [hudef, Multiset.card_map, hgcard_eq]
  have hu_map : u.map f = t := by
    rw [hudef, Multiset.map_map]
    have hcongr : Multiset.map (f ∘ Function.invFun f) t = Multiset.map id t := by
      refine Multiset.map_congr rfl fun x hx => ?_
      have hxmem : x ∈ (Finset.univ : Finset (ZMod p)).val.map f := Multiset.mem_of_le ht_le' hx
      obtain ⟨j, -, hjx⟩ := Multiset.mem_map.mp hxmem
      show f (Function.invFun f x) = x
      rw [← hjx]
      exact congrArg f (Function.leftInverse_invFun hf_inj j)
    rw [hcongr, Multiset.map_id]
  have ht_pos : 0 < t.card := by rw [hgcard_eq]; exact hd_pos
  have hvieta := Polynomial.multiset_prod_X_sub_C_coeff_card_pred t ht_pos
  rw [hgcard_eq] at hvieta
  have hsplits_g : (g.map (algebraMap k L)).Splits :=
    Polynomial.splits_iff_card_roots.mpr (by rw [hgcard_eq, hgdeg_map])
  have hsplit_g := Polynomial.Splits.eq_prod_roots hsplits_g
  rw [← htdef] at hsplit_g
  set c := (g.map (algebraMap k L)).leadingCoeff with hcdef
  have hc_def : c = algebraMap k L g.leadingCoeff := Polynomial.leadingCoeff_map _
  have hcoeff_eq : (g.map (algebraMap k L)).coeff (d - 1) = c * (-t.sum) := by
    conv_lhs => rw [hsplit_g]
    rw [Polynomial.coeff_C_mul, hvieta]
  have hcoeff_map : (g.map (algebraMap k L)).coeff (d - 1) =
      algebraMap k L (g.coeff (d - 1)) := Polynomial.coeff_map _ _
  set ψ₀ : ZMod p →+* k := ZMod.castHom (dvd_refl p) k with hψ₀def
  have hψcompat : (algebraMap k L).comp ψ₀ = ψ := RingHom.ext_zmod _ _
  have hψS : ψ u.sum = algebraMap k L (ψ₀ u.sum) := by
    rw [← hψcompat, RingHom.comp_apply]
  have htsum : t.sum = d • θ + ψ u.sum := by
    rw [← hu_map, hfdef, Multiset.sum_map_add]
    congr 1
    · rw [show (fun (_ : ZMod p) => θ) = Function.const (ZMod p) θ from rfl,
        Multiset.map_const, Multiset.sum_replicate, hu_card]
    · exact (map_multiset_sum ψ u).symm
  set c₀ := g.leadingCoeff with hc₀def
  have hc₀ne : c₀ ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hgne
  have hdk_ne : (d : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p d]
    intro hpd
    have := Nat.le_of_dvd hd_pos hpd
    omega
  have hcd_ne : c₀ * (d : k) ≠ 0 := mul_ne_zero hc₀ne hdk_ne
  have hinj : Function.Injective (algebraMap k L) := RingHom.injective _
  have hd_ne_L : algebraMap k L (c₀ * (d : k)) ≠ 0 :=
    fun hz => hcd_ne (hinj (hz.trans (map_zero (algebraMap k L)).symm))
  have hstar : algebraMap k L (g.coeff (d - 1) + c₀ * ψ₀ u.sum) =
      -(algebraMap k L (c₀ * (d : k))) * θ := by
    have heq1 : algebraMap k L (g.coeff (d - 1)) = c * (-t.sum) := hcoeff_map ▸ hcoeff_eq
    rw [htsum, hc_def, nsmul_eq_mul, hψS, ← map_natCast (algebraMap k L) d] at heq1
    rw [map_add, map_mul, map_mul]
    rw [heq1]
    ring
  have hθeq : θ = algebraMap k L ((-(g.coeff (d - 1) + c₀ * ψ₀ u.sum)) / (c₀ * (d : k))) := by
    rw [map_div₀, map_neg, eq_div_iff hd_ne_L]
    rw [hstar]; ring
  set θ₀ : k := (-(g.coeff (d - 1) + c₀ * ψ₀ u.sum)) / (c₀ * (d : k)) with hθ₀def
  have hθ₀aeval : aeval θ₀ (poly p a) = 0 :=
    (Polynomial.aeval_algebraMap_eq_zero_iff_of_injective hinj).mp (hθeq ▸ hθaeval)
  refine ⟨θ₀, ?_⟩
  have hz : θ₀ ^ p - θ₀ - a = 0 := by simpa [poly_def] using hθ₀aeval
  simpa using sub_eq_zero.mp hz

/-- **The Artin–Schreier irreducibility criterion.** `X ^ p - X - C a` is irreducible over `k` iff
`a` is not of the form `x ^ p - x` for `x : k`. -/
theorem irreducible_iff : Irreducible (poly p a) ↔ a ∉ Set.range (fun x : k => x ^ p - x) :=
  ⟨fun hirr h => not_irreducible_of_mem_range h hirr, irreducible_of_not_mem_range⟩

omit [Fact p.Prime] in
/-- **`poly p a` is separable.** Its derivative is the constant `-1` (the `X ^ p` term
contributes `(p : k) • X ^ (p - 1) = 0` since `CharP k p`), which is a unit, hence coprime to
everything, in particular to `poly p a` itself. -/
theorem poly_separable : (poly p a).Separable := by
  have hderiv : (poly p a).derivative = C (-1 : k) := by
    simp [poly_def, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_X, Polynomial.derivative_C]
  rw [Polynomial.separable_def, hderiv]
  obtain ⟨v, hv⟩ := Polynomial.isUnit_C.mpr (isUnit_one.neg : IsUnit (-1 : k))
  exact ⟨0, (↑v⁻¹ : Polynomial k), by rw [zero_mul, zero_add, ← hv]; exact v.inv_mul⟩

/-- **The splitting field of `poly p a` is Galois over `k`.** Separable (`poly_separable`) plus
the splitting field's automatic normality (`Polynomial.SplittingField.instNormal`) gives Galois,
via `IsGalois.of_separable_splitting_field`. -/
instance instIsGalois : IsGalois k (poly p a).SplittingField :=
  IsGalois.of_separable_splitting_field (p := poly p a) poly_separable

/-- **The splitting field of an irreducible `poly p a` has degree exactly `p` over `k`.** A root
`θ` (in the splitting field `L`) has `minpoly k θ = poly p a` (`minpoly.eq_of_irreducible_of_monic`),
so `k⟮θ⟯` already has degree `p`. Every other root is `θ + i` for `i` in the (`k`-rational, via
`ψ`/`ψ₀`) image of `ZMod p`, hence already lies in `k⟮θ⟯`; since `L` is generated over `k` by all
the roots (`Polynomial.SplittingField.adjoin_rootSet`), `k⟮θ⟯ = ⊤`, i.e. `k⟮θ⟯ = L`. -/
theorem finrank_splittingField_eq (hirr : Irreducible (poly p a)) :
    Module.finrank k (poly p a).SplittingField = p := by
  classical
  set L := (poly p a).SplittingField
  set M := (poly p a).map (algebraMap k L) with hMdef
  have hMsplits : M.Splits := Polynomial.SplittingField.splits (poly p a)
  have hMne : M ≠ 0 := Polynomial.map_ne_zero (poly_ne_zero p a)
  have hMdeg : M.natDegree = p := (Polynomial.natDegree_map _).trans (natDegree_poly p a)
  have hMcard : M.roots.card = p := by
    have hc := Polynomial.splits_iff_card_roots.mp hMsplits; rwa [hMdeg] at hc
  have hMpos : 0 < M.roots.card := by rw [hMcard]; exact (Fact.out : p.Prime).pos
  obtain ⟨θ, hθmem⟩ := Multiset.card_pos_iff_exists_mem.mp hMpos
  have hθroot : M.IsRoot θ := (Polynomial.mem_roots'.mp hθmem).2
  have hθaeval : aeval θ (poly p a) = 0 := by
    rw [aeval_def, ← Polynomial.eval_map]; exact hθroot
  have hInt : IsIntegral k θ := ⟨poly p a, poly_monic p a, hθaeval⟩
  have hminpoly : poly p a = minpoly k θ :=
    minpoly.eq_of_irreducible_of_monic hirr hθaeval (poly_monic p a)
  have hfinrank_adj : Module.finrank k (k⟮θ⟯ : IntermediateField k L) = p := by
    rw [IntermediateField.adjoin.finrank hInt, ← hminpoly, natDegree_poly]
  set ψ : ZMod p →+* L := ZMod.castHom (dvd_refl p) L with hψdef
  set ψ₀ : ZMod p →+* k := ZMod.castHom (dvd_refl p) k with hψ₀def
  have hψcompat : (algebraMap k L).comp ψ₀ = ψ := RingHom.ext_zmod _ _
  have hMroots_eq := roots_eq_image_add hMsplits hθroot
  have hrootSet_le : (poly p a).rootSet L ⊆ (k⟮θ⟯ : IntermediateField k L) := by
    intro x hx
    have hxmem : x ∈ M.roots := by
      have hx' : x ∈ (poly p a).aroots L := by
        rwa [Polynomial.rootSet, Finset.mem_coe, Multiset.mem_toFinset] at hx
      rwa [Polynomial.aroots] at hx'
    rw [hMroots_eq] at hxmem
    obtain ⟨j, -, hjx⟩ := Multiset.mem_map.mp hxmem
    rw [← hjx]
    have hψj : ψ j = algebraMap k L (ψ₀ j) := by rw [← hψcompat, RingHom.comp_apply]
    rw [hψj]
    exact add_mem (IntermediateField.mem_adjoin_simple_self k θ)
      (IntermediateField.algebraMap_mem _ _)
  have htop_sub : Algebra.adjoin k ((poly p a).rootSet L) ≤ (k⟮θ⟯ : IntermediateField k L).toSubalgebra :=
    Algebra.adjoin_le hrootSet_le
  have htop : (k⟮θ⟯ : IntermediateField k L).toSubalgebra = ⊤ := by
    rw [Polynomial.SplittingField.adjoin_rootSet] at htop_sub
    exact top_le_iff.mp htop_sub
  have hktheta_top : (k⟮θ⟯ : IntermediateField k L) = ⊤ :=
    IntermediateField.toSubalgebra_injective (htop.trans IntermediateField.top_toSubalgebra.symm)
  have : Module.finrank k L = Module.finrank k (k⟮θ⟯ : IntermediateField k L) := by
    rw [hktheta_top]
    exact (IntermediateField.topEquiv (F := k) (E := L)).symm.toLinearEquiv.finrank_eq
  rw [this, hfinrank_adj]

/-- **The Galois group of the splitting field of an irreducible `poly p a` is cyclic of order
`p`.** `Nat.card Gal(L/k) = Module.finrank k L = p` (`IsGalois.card_aut_eq_finrank`,
`finrank_splittingField_eq`), and every group of prime order is cyclic. -/
theorem isCyclic_gal (hirr : Irreducible (poly p a)) :
    IsCyclic (Gal((poly p a).SplittingField/k)) :=
  isCyclic_of_prime_card
    ((IsGalois.card_aut_eq_finrank k (poly p a).SplittingField).trans
      (finrank_splittingField_eq hirr))

end ArtinSchreier
