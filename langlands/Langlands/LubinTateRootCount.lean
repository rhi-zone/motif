import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Polynomial.Tower
import Langlands.LubinTateEisensteinQ
import Langlands.LubinTateTorsionPoints

/-!
# `|piTorsion hπ hf 1| = q`, given `Q := P.divX` splits completely inside `K`

`ROADMAP.md` §33 closed separability of `Q := P.divX` (`P` the Weierstrass-preparation factor of a
Lubin-Tate power series `f`), given two hypotheses (`IsUnit (P.divX.natDegree : O)`,
`‖algebraMap O K π‖ < 1`), the first of which is now derived in general
(`LubinTate.isUnit_natCast_of_add_one_eq_residueCard`, `Langlands/LubinTate.lean`) and true for
`Q.natDegree = residueCard O - 1` specifically; the second remains an explicit hypothesis (see that
file's docstring for why: no caller instantiating this repo's abstract Lubin-Tate `O`/`K` package
against a concrete `HeightOneSpectrum`/`adicCompletion` pair exists yet, so the fact is genuinely
not available from the currently-standing typeclass package, only from a strictly stronger one).

This file assembles the final root-counting step. `piTorsion hπ hf 1` is a literal `Set K` (not a
subset of some auxiliary splitting field), so the correctly-scoped root-counting hypothesis is that
`Q` **already splits completely inside `K` itself** — `(Q.map (algebraMap O K)).Splits` — rather
than introducing an abstract splitting field `L` disconnected from `piTorsion`'s actual carrier.
This is the design choice flagged as open in the task brief: given the choice between "any
splitting field, treated purely algebraically" and "`K` itself already contains the roots", the
second is the one that actually composes with `piTorsion : Set K` without a further transport step,
and is adopted here. (It specializes the general `L / K` machinery of `LubinTateEisensteinQ.lean` at
`L := K`, using the standing `Algebra.IsAlgebraic K K` instance any field trivially carries over
itself and `spectralNorm_extends`/`Polynomial.coe_aeval_eq_eval` to identify `spectralNorm K K` and
`Polynomial.aeval`-at-`K` with `K`'s own norm and `Polynomial.eval`.)

## Main results

* `Polynomial.roots_toFinset_card_eq_natDegree_of_separable_of_splits` : general, `Q`-independent
  fact — a separable polynomial over a field that splits completely (over that same field) has
  exactly `natDegree` distinct roots. Assembled from Mathlib's `Polynomial.nodup_roots`
  (separability ⟹ no repeated roots) and `Polynomial.Splits.natDegree_eq_card_roots` (splitting ⟹
  root-count-with-multiplicity equals degree).
* `LubinTate.card_piTorsion_one_eq_residueCard` : **`Nat.card (piTorsion hπ hf 1) = residueCard O`**
  — the capstone of this whole thread's root-counting arc. Given a Weierstrass factorization
  `f = P * u`, `Q := P.divX` monic/Eisenstein/associate-constant-term (from
  `LubinTate.divX_isWeaklyEisensteinAt_and_associated`), a tame-degree witness (now automatic:
  `LubinTate.isUnit_natCast_of_add_one_eq_residueCard`), `‖algebraMap O K π‖ < 1` (still an explicit
  hypothesis, see above), and `Q`'s map into `K` splitting completely: `piTorsion hπ hf 1` is
  exactly the union of `{0}` and `Q`'s (nonzero, distinct) roots in `K`, of total size
  `1 + (residueCard O - 1) = residueCard O`.

## What remains

`[K_1 : K] = q - 1` and `Gal(K_1/K) ≅ (O/π)ˣ` are not attempted here: this file only pins down the
*size* of the `π`-torsion point set, not the field extension `K_1 := K(F_π[π])` it generates
(`Langlands.LubinTateFieldTower.K_1`) or its Galois-theoretic structure. See `ROADMAP.md`'s entry
for this pass for the precise next step.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

open Polynomial

/-! ## General splitting-field root-counting -/

/-- **A separable polynomial that splits completely has exactly `natDegree` distinct roots.**
General fact about any field `L`, no Lubin-Tate content: `Polynomial.nodup_roots` (from
separability) says `Qk.roots` has no repeats, so its underlying finset has the same cardinality as
the multiset itself (`Multiset.toFinset_card_of_nodup`); `Polynomial.Splits.natDegree_eq_card_roots`
(from `Qk.Splits`) says that multiset's cardinality is exactly `Qk.natDegree`. -/
theorem Polynomial.roots_toFinset_card_eq_natDegree_of_separable_of_splits
    {L : Type*} [Field L] [DecidableEq L] {Qk : L[X]}
    (hsep : Qk.Separable) (hsplit : Qk.Splits) :
    Qk.roots.toFinset.card = Qk.natDegree := by
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)]
  exact hsplit.natDegree_eq_card_roots.symm

namespace LubinTate

open PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsFractionRing O K]
variable {π : O} {f : O⟦X⟧}

/-! ## Assembling `|piTorsion hπ hf 1| = q` -/

omit [Finite (ResidueField O)] in
/-- **A root of `Q.map (algebraMap O K)` inside `K` automatically lies in the maximal ideal
`‖x‖ < 1`.** Specializes `spectralNorm_eq_of_isLubinTatePoly_root` at `L := K`, using
`Algebra.algebraMap_self`/`spectralNorm_extends` to identify `spectralNorm K K x` with `‖x‖`
directly (`K` is trivially algebraic over itself). Since `Q`'s constant coefficient has norm
`c := ‖algebraMap O K π‖ < 1` (`hπnorm`), the exact identity `spectralNorm K K x = c ^ (1/n : ℝ)`
forces `‖x‖ < 1`. -/
theorem norm_lt_one_of_aeval_divX_eq_zero {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) {f : O⟦X⟧}
    (heq : f = (P : O⟦X⟧) * u) (hf0 : PowerSeries.coeff 0 f = 0) {π : O}
    (hπ : Irreducible π) (hf1 : PowerSeries.coeff 1 f = π)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree)
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπnorm : ‖algebraMap O K π‖ < 1)
    {x : K} (hx : Polynomial.aeval x (P.divX.map (algebraMap O K)) = 0) : ‖x‖ < 1 := by
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf0 hf1 hPdist hPdeg2
  have hkey := spectralNorm_eq_of_isLubinTatePoly_root (L := K) hu heq hf0 hπ hf1 hPdist hPdeg2 hx
  have hxeq : algebraMap K K x = x := by rw [Algebra.algebraMap_self]; rfl
  have hspec : spectralNorm K K x = ‖x‖ := by rw [← hxeq]; exact spectralNorm_extends x
  rw [hspec] at hkey
  have hc0eq : ‖algebraMap O K (P.divX.coeff 0)‖ = ‖algebraMap O K π‖ := by
    obtain ⟨v, hv⟩ := hQ0assoc
    have hmul : algebraMap O K (P.divX.coeff 0) * algebraMap O K (v : O) = algebraMap O K π := by
      rw [← map_mul, hv]
    have hvnorm : ‖algebraMap O K (v : O)‖ = 1 := norm_algebraMap_eq_one_of_isUnit hOK v.isUnit
    have := congrArg norm hmul
    rwa [norm_mul, hvnorm, mul_one] at this
  rw [hkey, hc0eq]
  have hn0 : (0:ℝ) < (1 / (P.divX.natDegree:ℝ)) := by
    apply div_pos one_pos
    exact_mod_cast hQdeg
  exact Real.rpow_lt_one (norm_nonneg _) hπnorm hn0

/-- **The capstone: `Nat.card (piTorsion hπ hf 1) = residueCard O`.** `piTorsion hπ hf 1` is
exactly `insert 0 (Q.map (algebraMap O K)).roots.toFinset` as a subset of `K` (`P = X * Q`,
`Polynomial.X_mul_divX_add`, so `aeval x P = x * aeval x Q`, vanishing iff `x = 0` or `x` is a root
of `Q`'s image; roots are automatically nonzero — `Q`'s constant term is an associate of `π ≠ 0` —
and automatically in the maximal ideal, `norm_lt_one_of_aeval_divX_eq_zero`). Counting: `0` is not
among `Q`'s roots, so the insert adds exactly one element to a set of size
`(Q.map (algebraMap O K)).natDegree = residueCard O - 1`
(`Polynomial.roots_toFinset_card_eq_natDegree_of_separable_of_splits`, fed by `hsplit` and the
separability closed in `LubinTateEisensteinQ.lean`), giving `residueCard O` total. -/
theorem card_piTorsion_one_eq_residueCard
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O)
    (hsplit : (P.divX.map (algebraMap O K)).Splits) :
    Nat.card (piTorsion (K := K) hπ hf 1) = residueCard O := by
  classical
  have hf0 : PowerSeries.coeff 0 f = 0 := hf.1
  have hf1 : PowerSeries.coeff 1 f = π := hf.2.1
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf0 hf1 hPdist hPdeg2
  have hQdegval : P.divX.natDegree = residueCard O - 1 := by
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hPdeg]
  have hQn1 : P.divX.natDegree + 1 = residueCard O := by
    have h2 := two_le_residueCard (O := O); omega
  have hQn : IsUnit ((P.divX.natDegree : O)) := isUnit_natCast_of_add_one_eq_residueCard hQn1
  have hQmapdeg : (P.divX.map (algebraMap O K)).natDegree = P.divX.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective O K) P.divX
  have hQmapdegpos : 0 < (P.divX.map (algebraMap O K)).natDegree := by
    rw [hQmapdeg]; exact hQdeg
  have hQmapdegne : (P.divX.map (algebraMap O K)).degree ≠ 0 :=
    (Polynomial.natDegree_pos_iff_degree_pos.mp hQmapdegpos).ne'
  obtain ⟨a0, ha0⟩ := hsplit.exists_eval_eq_zero hQmapdegne
  have ha0' : Polynomial.aeval a0 (P.divX.map (algebraMap O K)) = 0 := by
    rw [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
    exact ha0
  have hsep : (P.divX.map (algebraMap O K)).Separable :=
    separable_map_of_isWeaklyEisensteinAt_associated hOK hπ hπnorm hQmonic hQweak hQdeg hQ0assoc
      hQn (L := K) ha0'
  have hcard := Polynomial.roots_toFinset_card_eq_natDegree_of_separable_of_splits hsep hsplit
  rw [hQmapdeg, hQdegval] at hcard
  have hQcoeff0eq : (P.divX.map (algebraMap O K)).coeff 0 = algebraMap O K (P.divX.coeff 0) :=
    Polynomial.coeff_map _ _
  have hQ0ne : P.divX.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := hQ0assoc
    rw [h0, zero_mul] at hv
    exact hπ.ne_zero hv.symm
  have hQmapcoeff0ne : (P.divX.map (algebraMap O K)).coeff 0 ≠ 0 := by
    rw [hQcoeff0eq]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hQ0ne
  have hzero_not_root : (0 : K) ∉ (P.divX.map (algebraMap O K)).roots.toFinset := by
    simp only [Multiset.mem_toFinset, Polynomial.mem_roots']
    rintro ⟨-, hroot⟩
    exact hQmapcoeff0ne (by rw [Polynomial.coeff_zero_eq_eval_zero]; exact hroot)
  have hPfact : P = Polynomial.X * P.divX := by
    have hXid := Polynomial.X_mul_divX_add P
    rw [coeff_zero_eq_zero_of_eq_mul hu heq hf0, Polynomial.C_0, add_zero] at hXid
    exact hXid.symm
  set S : Finset K := insert (0 : K) (P.divX.map (algebraMap O K)).roots.toFinset with hSdef
  have hScard : S.card = residueCard O := by
    rw [hSdef, Finset.card_insert_of_notMem hzero_not_root, hcard]
    have h2 := two_le_residueCard (O := O); omega
  have hSmem : ∀ x : K, x ∈ S ↔ x ∈ piTorsion (K := K) hπ hf 1 := by
    intro x
    rw [hSdef, Finset.mem_insert]
    constructor
    · rintro (rfl | hx)
      · exact zero_mem_piTorsion hπ hf 1
      · rw [Multiset.mem_toFinset, Polynomial.mem_roots'] at hx
        obtain ⟨-, hroot⟩ := hx
        have haevalQ : Polynomial.aeval x (P.divX.map (algebraMap O K)) = 0 := by
          rw [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
          exact hroot
        have hxnorm : ‖x‖ < 1 :=
          norm_lt_one_of_aeval_divX_eq_zero hu heq hf0 hπ hf1 hPdist hPdeg2 hOK hπnorm haevalQ
        refine ⟨hxnorm, ?_⟩
        have haevalQO : Polynomial.aeval x P.divX = 0 := by
          rw [← Polynomial.aeval_map_algebraMap K x P.divX]
          exact haevalQ
        have haevalP : Polynomial.aeval x P = 0 := by
          conv_lhs => rw [hPfact]
          rw [map_mul, Polynomial.aeval_X, haevalQO, mul_zero]
        rw [iter_one]
        exact (eval_eq_zero_iff_aeval_eq_zero hOK hu heq hxnorm).mpr haevalP
    · rintro ⟨hxnorm, hxzero⟩
      rw [iter_one] at hxzero
      have haevalP : Polynomial.aeval x P = 0 :=
        (eval_eq_zero_iff_aeval_eq_zero hOK hu heq hxnorm).mp hxzero
      have hprod : x * Polynomial.aeval x P.divX = 0 := by
        rw [← haevalP]
        conv_rhs => rw [hPfact]
        rw [map_mul, Polynomial.aeval_X]
      rcases mul_eq_zero.mp hprod with hx0 | hQ0
      · exact Or.inl hx0
      · refine Or.inr ?_
        have haevalQ : Polynomial.aeval x (P.divX.map (algebraMap O K)) = 0 := by
          rw [Polynomial.aeval_map_algebraMap K x P.divX]
          exact hQ0
        have hroot : Polynomial.eval x (P.divX.map (algebraMap O K)) = 0 := by
          rw [← Polynomial.eval₂_id (p := P.divX.map (algebraMap O K)) (x := x),
            ← Algebra.algebraMap_self (R := K), ← Polynomial.aeval_def]
          exact haevalQ
        rw [Multiset.mem_toFinset, Polynomial.mem_roots']
        exact ⟨(hQmonic.map _).ne_zero, hroot⟩
  rw [← hScard]
  exact Nat.subtype_card S hSmem

end LubinTate
