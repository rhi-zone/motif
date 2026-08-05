import Langlands.HenselianValuation
import Langlands.IdeleGroup
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.FieldTheory.Minpoly.IsConjRoot

/-!
# Local pieces of the idèle norm map

This file assembles the infrastructure the idèle norm map `NumberField.IdeleGroup.normMap`
(`Langlands/IdeleGroup.lean`) needs, filling in the three gaps identified in the survey there:

1. The place-lying-over relation between `HeightOneSpectrum R` and `HeightOneSpectrum S` for a
   ring extension `R → S`: this turns out to already be present in Mathlib, just not under the
   name the previous survey looked for. `IsDedekindDomain.HeightOneSpectrum.under` (in
   `Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas`) restricts a height-one prime `w` of `S` to
   one of `R` (given `Algebra.IsIntegral R S`), and the "lying over" relation itself is
   `w.asIdeal.LiesOver v.asIdeal` (from `Mathlib.RingTheory.Ideal.Over`, applied to the
   underlying ideals) -- indeed `Mathlib.NumberTheory.RamificationInertia.Valuation` already
   states its results in terms of exactly this relation, e.g.
   `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`. `finite_liesOver` below packages the
   finiteness of the set of places lying over a given `v`, via `IsDedekindDomain.primesOver_finite`.
2. Local norm maps between completions of different fields: Mathlib does have (as of a 2026
   addition, `Mathlib.NumberTheory.RamificationInertia.Valuation`) the uniform continuity of
   `algebraMap K L` between the *valued fields* `WithVal (v.valuation K)` and
   `WithVal (w.valuation L)` for `w` lying over `v`
   (`IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver`). Composed with
   `UniformSpace.Completion.mapRingHom` and the identification of `adicCompletion` with the
   completion of the valued field (`adicCompletion.equiv`), this gives an honest ring hom
   `v.adicCompletion K →+* w.adicCompletion L` (`adicCompletionComap` below) -- not a `sorry`.
   The local norm map itself (`localNormMap`) is then `Units.map (Algebra.norm _)` for the
   `Algebra` structure this ring hom induces; also not a `sorry`, though its good behavior
   (matching the classical local norm, being trivial off a finite set of places, etc.) is not
   proved here.
3. A ring hom `AdeleRing S L →+* AdeleRing R K` induced by a finite extension: still missing.
   Assembling the local norms of (2) into a global map on the finite adèles requires knowing the
   local norm map is a *local unit* (valuation `1`) whenever `a_w` is, at all but finitely many
   places -- i.e. that `adicCompletionComap`/`localNormMap` restricts well to
   `adicCompletionIntegers`. This "almost everywhere" implication is proved unconditionally as
   `eventually_localNormMap_mem_units` below, on top of `localNormMap_mem_units` (the local norm
   of a *single* local unit is a local unit -- the standard fact that, for a finite extension of
   complete discretely-valued fields, the ring of integers of the top field is the integral
   closure of the ring of integers of the bottom field). **`localNormMap_mem_units` is now fully
   proved, no `sorry`**, via Galois conjugates in a normal closure (see its docstring and
   `isIntegral_of_mem_of_comap_eq` above it). Still missing beyond this -- and this is a
   *separate*, still-open gap, not something `localNormMap_mem_units` reduces to: the
   archimedean/infinite-place half of the norm map (no local norm map between completions of
   different fields at *infinite* places exists anywhere in Mathlib or this repo;
   `NumberField.InfiniteAdeleRing.instNorm`/`norm_def` is the idèle *content* map, unrelated), and
   the final assembly of both halves into a ring hom on the full adèle rings (no
   `baseChange`/`extensionMap` for `AdeleRing`/`InfiniteAdeleRing` exists in Mathlib; the finite
   half alone would need `RestrictedProduct.mkUnit`, analogous to
   `IdeleGroup.exists_toFractionalIdeal_eq`). `IdeleGroup.normMap` therefore remains a `sorry` for
   this reason, not for lack of the local-unit fact.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionComap` : the ring hom
  `v.adicCompletion K →+* w.adicCompletion L` induced by `algebraMap K L`, for `w` a place of `S`
  lying over `v`.
* `IsDedekindDomain.HeightOneSpectrum.localNormMap` : the local norm map on units,
  `(w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ`.
* `IsDedekindDomain.HeightOneSpectrum.finite_liesOver` : only finitely many places of `S` lie over
  a given place `v` of `R`.
* `IsDedekindDomain.HeightOneSpectrum.localNormMap_mem_units` : the local norm of a local unit is
  a local unit, via uniqueness of the extension of a complete valuation (no `sorry`).
* `IsDedekindDomain.HeightOneSpectrum.eventually_localNormMap_mem_units` : an idèle that is almost
  everywhere a local unit has local norms that are almost everywhere a local unit (no `sorry`).
  This closes the specific gap identified in the original survey for `IdeleGroup.normMap`
  ("an almost-everywhere-unit idèle maps to an almost-everywhere-unit idèle"), but
  `IdeleGroup.normMap` needs strictly more than this (see point 3 above) and remains a `sorry`.
-/

noncomputable section

open IsDedekindDomain
open scoped Pointwise WithZeroTopology

namespace IsDedekindDomain.HeightOneSpectrum

section RankOne

open scoped WithZero NNReal

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F] (v : HeightOneSpectrum A)

/-- **Connecting instance**: the `v`-adic completion of the fraction field of a Dedekind domain
has a rank-one valuation. Mathlib already builds `Valuation.IsRankOneDiscrete` for
`(Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)` completely generally (for *any* Dedekind domain
`A` with fraction field `F`, not just `𝓞 K` for a number field `K`) in
`Mathlib.NumberTheory.NumberField.Completion.FinitePlace` -- it just lives under the
`NumberField` namespace because that is where it happens to have been added, even though its
statement never mentions `NumberField`. That instance is built via
`Valuation.IsRankOneDiscrete.mk'` applied to `v.valuation F`: cyclicity of the value group comes
from `Subgroup.isCyclic` (any subgroup of the cyclic group `ℤᵐ⁰ˣ` is cyclic), nontriviality from
`v.valuation F`'s surjectivity (`HeightOneSpectrum.valuation_surjective`).

What was missing is turning that `IsRankOneDiscrete` fact into an actual `Valuation.RankOne`
*instance* -- the `ℝ≥0`-embedded-value-group structure that `Valued.toNormedField`/`NormedField`
and this session's uniqueness-of-valuation-extension machinery (`Langlands.HenselianValuation`)
need as a hypothesis. `Valuation.IsRankOneDiscrete.rankOne` builds a `RankOne` instance from *any*
real `e > 1`, with no further hypotheses: it does not need the residue field `A ⧸ v.asIdeal` to be
finite (contrast `NumberField.instRankOneAdicCompletion`, which specifically uses
`e = absNorm v.asIdeal` so the resulting norm matches the classical adic absolute value -- a
choice only available when `Module.Finite ℤ A`/`Module.Free ℤ A`, i.e. essentially when `A = 𝓞 K`).
For a bare Dedekind domain with no such finiteness assumption, any fixed `e` (here `e := 2`)
suffices to get an unconditional `RankOne` instance.

This alone does not close `IsDedekindDomain.HeightOneSpectrum.localNormMap_mem_units` below: the
remaining gap there is uniqueness of the extension of a *complete* discrete valuation to a finite
extension of `v.adicCompletion A`, which additionally needs the completion to be algebraic over
its base (not just rank-one) -- a separate blocker, not attempted here. -/
noncomputable instance instRankOneValuedAdicCompletion :
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (by norm_num : (1 : ℝ≥0) < 2)

/-- **`v.adicCompletion F` carries a `ValuativeRel` matching its ambient `Valued` structure.**
Built via `ValuativeRel.ofValuation`, the generic "turn a valuation into a `ValuativeRel`"
constructor from `Mathlib.RingTheory.Valuation.ValuativeRel.Basic`, applied to the already-ambient
`Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰` (`Mathlib`'s
`IsDedekindDomain.HeightOneSpectrum.instValuedAdicCompletion`). This is the first piece of the
`NontriviallyNormedField`/`IsUltrametricDist`/`ValuativeRel`/`Compatible` bridge that
`LocalField.valuationSubring_eq_of_comap_eq` (`Langlands.HenselianValuation`) needs on its base
field: previously this bridge was only built for `K` satisfying `IsNonarchimedeanLocalField K`
(`LocalField.valuationSubring_eq_of_comap_eq_of_isNonarchimedeanLocalField`), which required first
manufacturing a `Valued` instance from an ambient `ValuativeRel`/`TopologicalSpace` (via
`IsTopologicalAddGroup.rightUniformSpace` and friends). Here the direction is reversed and
simpler: `v.adicCompletion F` already has a genuine `Valued` instance from Mathlib, so we only need
to go *forward* to `ValuativeRel`, not backward. -/
noncomputable instance instValuativeRelValuedAdicCompletion :
    ValuativeRel (v.adicCompletion F) :=
  ValuativeRel.ofValuation (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)

/-- The ambient `Valued.v` on `v.adicCompletion F` is `Compatible` with the `ValuativeRel`
instance just built from it (`instValuativeRelValuedAdicCompletion`) -- immediate from
`Valuation.Compatible.ofValuation`, since that `ValuativeRel` instance *is*
`ValuativeRel.ofValuation Valued.v`. -/
instance : (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).Compatible :=
  Valuation.Compatible.ofValuation _

/-- **`v.adicCompletion F` is a nontrivially normed field**, via `Valued.toNontriviallyNormedField`
applied to the ambient `Valued` structure together with `instRankOneValuedAdicCompletion`. -/
noncomputable instance instNontriviallyNormedFieldAdicCompletion :
    NontriviallyNormedField (v.adicCompletion F) :=
  Valued.toNontriviallyNormedField (v.adicCompletion F) ℤᵐ⁰

/-- **Closing the bridge**: the canonical valuation of the `NontriviallyNormedField` structure
just built (`NormedField.valuation`) is `Compatible` with `instValuativeRelValuedAdicCompletion`.
This is the last piece `LocalField.valuationSubring_eq_of_comap_eq` needs, generalizing
`LocalField.valuationSubring_eq_of_comap_eq_of_isNonarchimedeanLocalField`'s bridge (built there
only for `IsNonarchimedeanLocalField K`) to any bare Dedekind-domain adic completion
`v.adicCompletion F`. Proved via `NormedField.valuation_compatible_of_eq_rankOne_hom_comp_restrict`
(`Langlands.HenselianValuation`), whose hypothesis `hnorm` holds by the defining `rfl`
`Valued.coe_valuation_eq_rankOne_hom_comp_valuation` (the `NormedField` structure above is
*literally built from* `Valued.v`, so its canonical valuation agrees with `Valued.v`'s `RankOne`
embedding on the nose). -/
instance : (NormedField.valuation (K := v.adicCompletion F)).Compatible :=
  NormedField.valuation_compatible_of_eq_rankOne_hom_comp_restrict
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
    (fun x => congrFun
      (Valued.coe_valuation_eq_rankOne_hom_comp_valuation (v.adicCompletion F) ℤᵐ⁰) x)

end RankOne

section IntegralClosure

/-! ### Elements of a valuation-ring extension are integral over the base

This section closes the `localNormMap_mem_units` gap: for a finite extension `Lw / Kv` of
complete discretely-valued fields, `Bw` (the ring of integers of `Lw`) equals the integral
closure of `Ov` (the ring of integers of `Kv`) in `Lw`, given `Bw` comaps to `Ov`. Only the
"`Bw ⊆` integral closure" direction is needed here (the converse is the easy, purely formal
half via `IsIntegrallyClosed`). The proof goes via Galois conjugates in a normal closure `N` of
`Lw / Kv`: pass to `N`, where the (unique, since `Kv` is complete) valuation subring `A`
extending `Ov` is fixed setwise by every automorphism of `N / Kv`
(`ValuationSubring.comap_smul_eq` + `LocalField.valuationSubring_eq_of_comap_eq`); every root of
`minpoly Kv x` in `N` is then a Galois conjugate of `x` (`IsConjRoot.exists_algEquiv`, using
normality of `N`), hence lies in `A` too; so the coefficients of `minpoly Kv x`, being polynomial
expressions in those roots, lie in `A ∩ Kv = Ov`. This avoids the elementary-symmetric-function/
Vieta bookkeeping the "obvious" proof would need by working with roots directly rather than
computing coefficients combinatorially. -/

open Polynomial in
/-- If a monic polynomial over a field `N` splits into linear factors with all roots in a
subring `T`, the roots (as elements of `T`) reassemble into a polynomial over `T` mapping back
to the original. Purely formal, by induction on the root multiset. -/
theorem exists_toSubring_of_roots_mem {N : Type*} [Field N] (T : Subring N) (m : Multiset N)
    (hm : ∀ r ∈ m, r ∈ T) : ∃ q : T[X], q.map T.subtype = (m.map (fun r => X - C r)).prod := by
  induction m using Multiset.induction with
  | empty => exact ⟨1, by simp⟩
  | cons a s ih =>
    obtain ⟨q, hq⟩ := ih (fun r hr => hm r (Multiset.mem_cons_of_mem hr))
    refine ⟨(X - C (⟨a, hm a (Multiset.mem_cons_self a s)⟩ : T)) * q, ?_⟩
    simp [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, hq]

open Polynomial in
/-- If a monic polynomial over a field `N` splits with all its roots in a subring `T`, all its
coefficients lie in `T` too (the roots reassemble into a `T`-polynomial via
`exists_toSubring_of_roots_mem`, and `coeff_map` reads off `T`-membership of each coefficient). -/
theorem coeff_mem_subring_of_splits {N : Type*} [Field N] (T : Subring N) {p : N[X]}
    (hpmon : p.Monic) (hp : p.Splits) (hpr : ∀ x, p.IsRoot x → x ∈ T) (i : ℕ) :
    p.coeff i ∈ T := by
  obtain ⟨q, hq⟩ := exists_toSubring_of_roots_mem T p.roots
    (fun r hr => hpr r (Polynomial.mem_roots'.mp hr).2)
  rw [hp.eq_prod_roots_of_monic hpmon, ← hq, Polynomial.coeff_map]
  exact (q.coeff i).2

/-- **Generalized Chevalley extension theorem**: for any field extension `K → L` and any
`ValuationSubring O` of `K` (not just the fixed `(valuation K).valuationSubring` of
`LocalField.exists_valuationSubring_extends`), there is a `ValuationSubring` of `L` whose comap
along `algebraMap K L` is `O`. Verbatim generalization of
`LocalField.exists_valuationSubring_extends` (`Langlands.WeilGroup`), parametrized over an
arbitrary `O` instead of a fixed one -- the proof never used anything about `O` beyond it being a
`ValuationSubring`. -/
theorem exists_valuationSubring_extends' {K L : Type*} [Field K] [Field L] [Algebra K L]
    (O : ValuationSubring K) :
    ∃ A : ValuationSubring L, A.comap (algebraMap K L) = O := by
  set f : ↥O →+* L := (algebraMap K L).comp O.subtype with hf
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  haveI : IsLocalHom (f.codRestrict A.toSubring hA) := hloc
  refine ⟨A, ValuationSubring.ext _ _ fun x => ?_⟩
  rw [ValuationSubring.mem_comap]
  constructor
  · intro hx
    by_contra hxO
    have hx0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
    have hxinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
    set b : ↥O := ⟨x⁻¹, hxinv⟩ with hb
    have hfb : f b ∈ A.toSubring := hA b
    have hfb' : f b = (algebraMap K L x)⁻¹ := by
      show (algebraMap K L) x⁻¹ = (algebraMap K L x)⁻¹
      exact map_inv₀ _ _
    have hne : algebraMap K L x ≠ 0 :=
      (map_ne_zero_iff (algebraMap K L) (algebraMap K L).injective).mpr hx0
    have hub : IsUnit (f.codRestrict A.toSubring hA b) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K L x, hx⟩, Subtype.ext ?_⟩
      show f b * algebraMap K L x = 1
      rw [hfb', inv_mul_cancel₀ hne]
    have hbunit : IsUnit b := IsLocalHom.map_nonunit b hub
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hbunit
    have hcx : (c : K) = x := by
      have hbc : (b : K) * (c : K) = 1 := congrArg Subtype.val hc
      rw [hb] at hbc
      show (c : K) = x
      field_simp at hbc
      rw [hbc]
    exact hxO (hcx ▸ c.2)
  · intro hxO
    exact hA ⟨x, hxO⟩

/-- **Main lemma**: for a finite extension `Lw / Kv` of a complete nontrivially-normed
nonarchimedean field `Kv`, if `B` is a `ValuationSubring` of `Lw` comapping to `Ov := (valuation
Kv).valuationSubring`, every `x ∈ B` is integral over `Ov`. This is the standard fact that the
ring of integers of a finite extension of a complete discretely-valued field is the integral
closure of the base ring of integers (Serre, *Local Fields*, Ch. II §2), proved via Galois
conjugates in a normal closure -- see the section docstring above for the argument. -/
theorem isIntegral_of_mem_of_comap_eq {Kv Lw : Type*} [NontriviallyNormedField Kv]
    [IsUltrametricDist Kv] [ValuativeRel Kv] [(NormedField.valuation (K := Kv)).Compatible]
    [CompleteSpace Kv] [Field Lw] [Algebra Kv Lw] [FiniteDimensional Kv Lw]
    (B : ValuationSubring Lw)
    (hB : B.comap (algebraMap Kv Lw) = (ValuativeRel.valuation Kv).valuationSubring)
    {x : Lw} (hx : x ∈ B) : IsIntegral (ValuativeRel.valuation Kv).valuationSubring x := by
  set O := (ValuativeRel.valuation Kv).valuationSubring with hOdef
  rcases eq_or_ne x 0 with rfl | hx0
  · exact isIntegral_zero
  haveI : Algebra.IsAlgebraic Kv Lw := Algebra.IsAlgebraic.of_finite _ _
  haveI : IsAlgClosure Kv (AlgebraicClosure Lw) :=
    IsAlgClosure.ofAlgebraic Kv Lw (AlgebraicClosure Lw)
  haveI : Normal Kv (AlgebraicClosure Lw) := IsAlgClosure.normal Kv (AlgebraicClosure Lw)
  set N := IntermediateField.normalClosure Kv Lw (AlgebraicClosure Lw) with hN
  haveI : Normal Kv N := normalClosure.normal Kv Lw (AlgebraicClosure Lw)
  letI : Algebra Lw N := normalClosure.algebra Kv Lw (AlgebraicClosure Lw)
  set x' : N := algebraMap Lw N x with hx'def
  have hx'0 : x' ≠ 0 := by
    rw [hx'def, Ne, map_eq_zero_iff _ (algebraMap Lw N).injective]
    exact hx0
  -- The unique valuation subring of `N` extending `O`.
  obtain ⟨A, hA⟩ := exists_valuationSubring_extends' (K := Kv) (L := N) O
  have hAfix : ∀ σ : N ≃ₐ[Kv] N, σ • A = A := by
    intro σ
    have h1 : (σ • A).comap (algebraMap Kv N) = O :=
      (ValuationSubring.comap_smul_eq σ A).trans hA
    exact LocalField.valuationSubring_eq_of_comap_eq Kv h1 hA
  have hcomap_ι : A.comap (algebraMap Lw N) = B := by
    apply LocalField.valuationSubring_eq_of_comap_eq Kv
    · show (A.comap (algebraMap Lw N)).comap (algebraMap Kv Lw) = O
      rw [ValuationSubring.comap_comap]
      have heq : (algebraMap Lw N).comp (algebraMap Kv Lw) = algebraMap Kv N :=
        (IsScalarTower.algebraMap_eq Kv Lw N).symm
      rw [heq, hA]
    · exact hB
  have hx'A : x' ∈ A := by
    rw [← ValuationSubring.mem_comap (A := A) (f := algebraMap Lw N), hcomap_ι]
    exact hx
  have hxi : IsIntegral Kv x' := Algebra.IsIntegral.isIntegral x'
  have hroots : ∀ r : N, ((minpoly Kv x').map (algebraMap Kv N)).IsRoot r → r ∈ A.toSubring := by
    intro r hr
    have hconj : IsConjRoot Kv x' r := by
      apply isConjRoot_of_aeval_eq_zero hxi
      rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hr
    obtain ⟨σ, hσ⟩ := hconj.symm.exists_algEquiv
    have hfix := hAfix σ
    have hiff : (σ x' : N) ∈ σ • A ↔ x' ∈ A := by
      simp [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    rw [hfix] at hiff
    rw [← hσ]
    exact hiff.mpr hx'A
  have hcoeffs : ∀ i, ((minpoly Kv x').map (algebraMap Kv N)).coeff i ∈ A.toSubring :=
    coeff_mem_subring_of_splits A.toSubring ((minpoly.monic hxi).map (algebraMap Kv N))
      (Normal.splits inferInstance x') hroots
  have hcoeffs' : ∀ i, (minpoly Kv x').coeff i ∈ O := by
    intro i
    have hmem := hcoeffs i
    rw [Polynomial.coeff_map] at hmem
    have : (minpoly Kv x').coeff i ∈ A.comap (algebraMap Kv N) :=
      (ValuationSubring.mem_comap (A := A) (f := algebraMap Kv N)).mpr hmem
    rwa [hA] at this
  -- Transfer to `minpoly Kv x` (equal to `minpoly Kv x'` since `algebraMap Lw N` is injective).
  have hminpoly_eq : minpoly Kv x' = minpoly Kv x :=
    minpoly.algHom_eq (IsScalarTower.toAlgHom Kv Lw N) (algebraMap Lw N).injective x
  rw [hminpoly_eq] at hcoeffs'
  -- Assemble the monic polynomial over `O` witnessing integrality.
  have hsub : (↑(minpoly Kv x).coeffs : Set Kv) ⊆ O.toSubring := by
    intro c hc
    simp only [Polynomial.coeffs, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Polynomial.mem_support_iff] at hc
    obtain ⟨n, _, rfl⟩ := hc
    exact hcoeffs' n
  have hxi_x : IsIntegral Kv x := Algebra.IsIntegral.isIntegral x
  refine ⟨(minpoly Kv x).toSubring O.toSubring hsub, ?_, ?_⟩
  · exact (Polynomial.monic_toSubring _ _ _).mpr (minpoly.monic hxi_x)
  · show Polynomial.eval₂ (algebraMap (↥O) Lw) x ((minpoly Kv x).toSubring O.toSubring hsub) = 0
    rw [IsScalarTower.algebraMap_eq (↥O) Kv Lw,
      ← Polynomial.eval₂_map, show algebraMap (↥O) Kv = O.toSubring.subtype from rfl,
      Polynomial.map_toSubring _ O.toSubring hsub]
    exact minpoly.aeval Kv x

end IntegralClosure

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

/-- The ring hom `v.adicCompletion K →+* w.adicCompletion L` induced by `algebraMap K L`, for a
place `w` of `S` lying over a place `v` of `R`. Built by extending the uniformly continuous map
`algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))`
(`uniformContinuous_algebraMap_liesOver`) to the completions, then transporting along the
identification of `adicCompletion` with the completion of the valued field
(`adicCompletion.equiv`). -/
def adicCompletionComap : v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
        (uniformContinuous_algebraMap_liesOver K L v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom)

/-- The `w.adicCompletion L` obtained from `v.adicCompletion K` via `adicCompletionComap`, for a
place `w` of `S` lying over a place `v` of `R`. -/
instance : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (adicCompletionComap K L v w).toAlgebra

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- `adicCompletionComap` is continuous: it is built by composing the (unconditionally
continuous) `UniformSpace.Completion.map` of a uniformly continuous map with the two
homeomorphisms `adicCompletion.equiv`, whose continuity in each direction is
`adicCompletion.continuous_toCompletion` / `adicCompletion.continuous_ofCompletion`. -/
theorem continuous_adicCompletionComap : Continuous (adicCompletionComap K L v w) :=
  (adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v)

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- `adicCompletionComap` agrees, on the image of `K`, with `algebraMap K (w.adicCompletion L)`
composed through `algebraMap K L`. This is the compatibility fact needed for
`IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)`. -/
theorem adicCompletionComap_algebraMap (x : K) :
    adicCompletionComap K L v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  apply (adicCompletion.equiv L w).injective
  simp only [adicCompletionComap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, adicCompletion.equiv_apply,
    algebraMap_adicCompletion_toCompletion, UniformSpace.Completion.algebraMap_def,
    UniformSpace.Completion.coe_mapRingHom,
    UniformSpace.Completion.map_coe (uniformContinuous_algebraMap_liesOver K L v w)]
  exact congrArg _ <|
    (IsScalarTower.algebraMap_apply K (WithVal (v.valuation K)) (WithVal (w.valuation L)) x).symm.trans
      (IsScalarTower.algebraMap_apply K L (WithVal (w.valuation L)) x)

/-- The scalar tower `K → v.adicCompletion K → w.adicCompletion L`, for a place `w` of `S` lying
over a place `v` of `R`. Needed (together with `instContinuousSMulAdicCompletionAdicCompletion`
below) to instantiate Mathlib's `NumberField.HeightOneSpectrum.instModuleFiniteAdicCompletion`-style
finiteness argument in the general Dedekind-domain setting. -/
instance : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x => (adicCompletionComap_algebraMap K L v w x).symm

/-- `v.adicCompletion K` acts continuously on `w.adicCompletion L`, via `adicCompletionComap`. -/
instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) where
  continuous_smul :=
    (continuous_adicCompletionComap K L v w).comp continuous_fst |>.mul continuous_snd

open scoped TensorProduct Valued in
/-- **`w.adicCompletion L` is a finite `v.adicCompletion K`-module.** Mathlib already proves this
(`NumberField.HeightOneSpectrum.instModuleFiniteAdicCompletion` in
`Mathlib.NumberTheory.NumberField.Completion.FinitePlace`), but only under `[NumberField K]
[NumberField L]` hypotheses -- even though the proof itself only uses `Module.Finite K L`
(to get `Kv ⊗[K] L` finite-dimensional over `Kv`) together with the `Algebra`/`ContinuousSMul`/
`IsScalarTower` instances just built above, none of which need `K`/`L` to be number fields. The
proof is otherwise identical: `Φ : Kv ⊗[K] L →ₗ[Kv] Lw` (the multiplication map) has closed,
hence (being finite-dimensional) all of, `Lw` as its range, since its range is dense
(`w.denseRange_algebraMap L`, itself fully general for any Dedekind domain). -/
instance : Module.Finite (v.adicCompletion K) (w.adicCompletion L) :=
  let Φ : v.adicCompletion K ⊗[K] L →ₗ[v.adicCompletion K] w.adicCompletion L :=
    Algebra.TensorProduct.lift (Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
      (w.adicCompletion L)) (Algebra.algHom K L (w.adicCompletion L))
      (fun _ _ => mul_comm ..) |>.toLinearMap
  have h_dense : DenseRange Φ := by
    apply (w.denseRange_algebraMap L).mono
    rintro _ ⟨l, rfl⟩
    exact ⟨1 ⊗ₜ l, by simp [Φ, Algebra.algHom]⟩
  .of_surjective Φ (by
    rw [← Set.range_eq_univ, ← Φ.coe_range, ← Φ.range.closed_of_finiteDimensional.closure_eq]
    exact h_dense.closure_range)

/-- **Algebraicity of `w.adicCompletion L` over `v.adicCompletion K`.** The missing ingredient
`LocalField.valuationSubring_eq_of_comap_eq` (`Langlands.HenselianValuation`) needs to apply
uniqueness-of-valuation-extension to `w.adicCompletion L / v.adicCompletion K`: finite extensions
are algebraic. -/
instance : Algebra.IsAlgebraic (v.adicCompletion K) (w.adicCompletion L) :=
  .of_finite _ _

/-- The local norm map `N_{L_w/K_v} : (w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ`, for a place
`w` of `S` lying over a place `v` of `R`: the norm of the finite (as `L / K` is finite, hence so is
`L_w / K_v`, though this finiteness is not needed for the definition itself) extension
`w.adicCompletion L` of `v.adicCompletion K`, transported to units via `Units.map`. This is the
local factor of the idèle norm map `N_{L/K} a = (∏_{w ∣ v} N_{L_w/K_v}(a_w))_v`. -/
def localNormMap : (w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (Algebra.norm (v.adicCompletion K) : w.adicCompletion L →* v.adicCompletion K)

/-- Only finitely many places `w` of `S` lie over a given place `v` of `R`: the set
`{w // w.asIdeal.LiesOver v.asIdeal}` injects into `v.asIdeal.primesOver S`
(via `w ↦ w.asIdeal`), which is finite since `v.asIdeal` is a nonzero (hence maximal, by
`IsDedekindDomain.HeightOneSpectrum.isMaximal`) ideal of the Dedekind domain `R` and `S / R` is
integral (`IsDedekindDomain.primesOver_finite`). -/
theorem finite_liesOver (v : HeightOneSpectrum R) :
    {w : HeightOneSpectrum S | w.asIdeal.LiesOver v.asIdeal}.Finite := by
  have hsub : (fun w : HeightOneSpectrum S => w.asIdeal) ''
      {w : HeightOneSpectrum S | w.asIdeal.LiesOver v.asIdeal} ⊆ v.asIdeal.primesOver S := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, hw⟩
  exact Set.Finite.of_finite_image
    (Set.Finite.subset (IsDedekindDomain.primesOver_finite v.asIdeal S) hsub)
    (HeightOneSpectrum.asIdeal_injective.injOn)

/-- **The canonical `ValuativeRel.valuation` of `v.adicCompletion K` has the same valuation ring as
`Valued.v`, i.e. as `v.adicCompletionIntegers K`.** Both are `Compatible` with the same ambient
`ValuativeRel` instance (`instValuativeRelValuedAdicCompletion`, built as `ValuativeRel.ofValuation
Valued.v`), hence equivalent (`ValuativeRel.isEquiv`); equivalent valuations share a valuation
subring (`Valuation.isEquiv_iff_valuationSubring`). This lets the generic
`isIntegral_of_mem_of_comap_eq` above (stated in terms of the abstract `ValuativeRel.valuation`)
be applied to the concrete `v.adicCompletionIntegers K`. -/
theorem valuation_valuationSubring_eq_adicCompletionIntegers :
    (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring
      = v.adicCompletionIntegers K := by
  show (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring = Valued.v.valuationSubring
  rw [← Valuation.isEquiv_iff_valuationSubring]
  exact ValuativeRel.isEquiv _ _

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- **The comap-containment fact**: `w.adicCompletionIntegers L` comaps *exactly* to
`v.adicCompletionIntegers K` along `adicCompletionComap`. Proved via continuity + density, not
via the closedness argument originally sketched (`Valued.isClopen_valuationSubring`): the two
continuous maps `y ↦ w-valuation (adicCompletionComap y)` and `y ↦ (v-valuation y) ^ e` (`e` the
ramification index) agree on the dense image of `K` (by `valuation_liesOver`, the corresponding
*exact* identity for elements of `K` itself, not just an inequality), hence agree everywhere
(`DenseRange.equalizer`); raising to the `e`-th power (`e ≠ 0`) preserves the `≤ 1` boundary
(`pow_le_one_iff_of_nonneg`), giving the comap equality directly, in both directions at once. -/
theorem adicCompletionIntegers_comap_eq :
    (w.adicCompletionIntegers L).comap (adicCompletionComap K L v w)
      = v.adicCompletionIntegers K := by
  set e := v.asIdeal.ramificationIdx' w.asIdeal with hedef
  have he0 : e ≠ 0 := Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot
  have hcont1 :
      Continuous (fun y : v.adicCompletion K => Valued.v (adicCompletionComap K L v w y)) :=
    (Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective L w)).comp
      (continuous_adicCompletionComap K L v w)
  have hcont2 : Continuous (fun y : v.adicCompletion K => (Valued.v y) ^ e) :=
    (Valued.continuous_valuation_of_surjective (valuedAdicCompletion_surjective K v)).pow e
  have hden : DenseRange (algebraMap K (v.adicCompletion K)) := denseRange_algebraMap K v
  have hcomp : (fun y : v.adicCompletion K => Valued.v (adicCompletionComap K L v w y))
      ∘ (algebraMap K (v.adicCompletion K)) =
      (fun y : v.adicCompletion K => (Valued.v y) ^ e) ∘ (algebraMap K (v.adicCompletion K)) := by
    funext k
    simp only [Function.comp_apply, adicCompletionComap_algebraMap]
    rw [show (algebraMap L (adicCompletion L w) (algebraMap K L k))
        = ((algebraMap K L k : L) : adicCompletion L w) from rfl,
      show (algebraMap K (adicCompletion K v) k) = ((k : K) : adicCompletion K v) from rfl,
      valuedAdicCompletion_eq_valuation', valuedAdicCompletion_eq_valuation',
      valuation_liesOver L v w]
  have heq : ∀ y : v.adicCompletion K,
      Valued.v (adicCompletionComap K L v w y) = (Valued.v y) ^ e :=
    congrFun (hden.equalizer hcont1 hcont2 hcomp)
  ext y
  rw [ValuationSubring.mem_comap, mem_adicCompletionIntegers, mem_adicCompletionIntegers, heq]
  exact pow_le_one_iff_of_nonneg zero_le he0

omit [Algebra.IsIntegral R S] in
/-- **Key local fact.** The local norm map sends local units to local units: if `a` has
valuation `1` at `w` (i.e. `a ∈ w.adicCompletionIntegers L`, as a unit), its norm
`N_{L_w/K_v}(a)` has valuation `1` at `v`.

Proved via the standard fact from local field theory that, for a finite extension of *complete*
discretely-valued fields, the extension of `v` to `L_w` is unique, so `w.adicCompletionIntegers L`
is exactly the integral closure of `v.adicCompletionIntegers K` in `w.adicCompletion L` (Serre,
*Local Fields*, Ch. II §2) -- `isIntegral_of_mem_of_comap_eq` above, applied via the comap fact
`adicCompletionIntegers_comap_eq` and the bridge `valuation_valuationSubring_eq_adicCompletionIntegers`.
Both `a` and `a⁻¹` are then integral over `v.adicCompletionIntegers K`, so their norms are too
(`Algebra.isIntegral_norm`); since `v.adicCompletionIntegers K` is integrally closed in
`v.adicCompletion K` (`IsIntegrallyClosedIn`, an instance for any `ValuationSubring`), both norms
actually lie in `v.adicCompletionIntegers K`, i.e. `localNormMap K L v w a` is a unit there. -/
theorem localNormMap_mem_units {a : (w.adicCompletion L)ˣ}
    (ha : a ∈ (w.adicCompletionIntegers L).units) :
    localNormMap K L v w a ∈ (v.adicCompletionIntegers K).units := by
  have hbridge := valuation_valuationSubring_eq_adicCompletionIntegers K v
  have hcomap : (w.adicCompletionIntegers L).comap (adicCompletionComap K L v w)
      = (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring := by
    rw [hbridge]; exact adicCompletionIntegers_comap_eq K L v w
  have h1 : IsIntegral (v.adicCompletionIntegers K) (a : w.adicCompletion L) := by
    have := isIntegral_of_mem_of_comap_eq (w.adicCompletionIntegers L) hcomap
      (x := (a : w.adicCompletion L)) (Submonoid.val_mem_of_mem_units _ ha)
    rwa [hbridge] at this
  have h2 : IsIntegral (v.adicCompletionIntegers K)
      ((a⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L) := by
    have := isIntegral_of_mem_of_comap_eq (w.adicCompletionIntegers L) hcomap
      (x := ((a⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L))
      (Submonoid.inv_val_mem_of_mem_units _ ha)
    rwa [hbridge] at this
  have hn1 := Algebra.isIntegral_norm (R := v.adicCompletionIntegers K) (v.adicCompletion K) h1
  have hn2 := Algebra.isIntegral_norm (R := v.adicCompletionIntegers K) (v.adicCompletion K) h2
  obtain ⟨y1, hy1⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hn1
  obtain ⟨y2, hy2⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hn2
  refine Submonoid.mem_units_of_val_mem_inv_val_mem _ ?_ ?_
  · show Algebra.norm (v.adicCompletion K) (a : w.adicCompletion L) ∈
      (v.adicCompletionIntegers K).toSubmonoid
    exact hy1 ▸ y1.2
  · rw [← map_inv]
    show Algebra.norm (v.adicCompletion K) ((a⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L) ∈
      (v.adicCompletionIntegers K).toSubmonoid
    exact hy2 ▸ y2.2

/-- **Main assembly lemma**, and the key missing piece for `IdeleGroup.normMap`
(`Langlands/IdeleGroup.lean`): if a family `a : ∀ w, (w.adicCompletion L)ˣ` of local units at
places of `S` is almost everywhere (in the cofinite filter on `HeightOneSpectrum S`) a genuine
local unit -- the restricted-product condition defining a finite idèle of `L` -- then, for all
but finitely many places `v` of `R`, *every* place `w` lying over `v` has `a w` a local unit,
hence (via `localNormMap_mem_units`) its local norm `N_{L_w/K_v}(a w)` is a local unit at `v`.

The point is that finitely many "bad" places `w` of `S` can only lie over finitely many places
`v` of `R`: each `w` lies over a *unique* `v` (`w.asIdeal.LiesOver v.asIdeal` determines
`v = HeightOneSpectrum.under R w`, `Ideal.LiesOver.over`), so the bad `v`'s are exactly the
(finite) image of the bad `w`'s under `HeightOneSpectrum.under R`; away from that finite set,
every `w` lying over `v` is good. This is what lets the local norm maps be assembled into a
genuine finite idèle of `K` (once the local units are packaged via `RestrictedProduct.mkUnit`,
as in `IdeleGroup.exists_toFractionalIdeal_eq`). -/
theorem eventually_localNormMap_mem_units
    {a : ∀ w : HeightOneSpectrum S, (w.adicCompletion L)ˣ}
    (ha : ∀ᶠ w : HeightOneSpectrum S in Filter.cofinite,
      a w ∈ (w.adicCompletionIntegers L).units) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      ∀ w : HeightOneSpectrum S, ∀ _ : w.asIdeal.LiesOver v.asIdeal,
        localNormMap K L v w (a w) ∈ (v.adicCompletionIntegers K).units := by
  rw [Filter.eventually_cofinite] at ha ⊢
  refine Set.Finite.subset (ha.image (HeightOneSpectrum.under R)) fun v hv => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨w, hw, hcontra⟩ := hv
  haveI := hw
  have hveq : v = HeightOneSpectrum.under R w := HeightOneSpectrum.ext hw.over
  exact ⟨w, mt (localNormMap_mem_units K L v w) hcontra, hveq.symm⟩

end IsDedekindDomain.HeightOneSpectrum

section FiniteIdeleNormMap

/-! ### Assembling the finite-place local norms into a finite idèle norm map

This section builds `NumberField.FiniteIdeleGroup.normMap : FiniteIdeleGroup S L →*
FiniteIdeleGroup R K`, the finite-place half of `IdeleGroup.normMap`
(`Langlands/IdeleGroup.lean`), by taking, at each place `v` of `R`, the product of
`IsDedekindDomain.HeightOneSpectrum.localNormMap` over the (finitely many,
`finite_liesOver`) places `w` of `S` lying over `v`, then checking (via
`eventually_localNormMap_mem_units`) that this assembles into a genuine finite idèle via
`RestrictedProduct.mkUnit`. -/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L)

/-- Membership witness for an element of the `attach`ed `Finset` of places `w` of `S` lying
over a place `v` of `R`, unpacked from `Set.Finite.toFinset` membership into a genuine
`LiesOver` instance. Factored out since inlining `(Set.Finite.mem_toFinset _).mp w.2` directly
at each use site confuses elaboration (the implicit arguments of `Set.Finite.mem_toFinset` are
not determined early enough). -/
theorem mem_liesOver_of_mem_toFinset {v : HeightOneSpectrum R}
    (w : {x : HeightOneSpectrum S // x ∈ (finite_liesOver (R := R) (S := S) v).toFinset}) :
    (w : HeightOneSpectrum S).asIdeal.LiesOver v.asIdeal := by
  have hw := w.2
  rwa [Set.Finite.mem_toFinset] at hw

/-- The `v`-component of the finite-place idèle norm map: the product of the local norms
`N_{L_w/K_v}(a w)` over the (finitely many) places `w` of `S` lying over `v`. -/
noncomputable def finiteNormMapComponent (v : HeightOneSpectrum R)
    (a : ∀ w : HeightOneSpectrum S, (w.adicCompletion L)ˣ) : (v.adicCompletion K)ˣ :=
  ∏ w ∈ (finite_liesOver (R := R) (S := S) v).toFinset.attach,
    haveI := mem_liesOver_of_mem_toFinset w
    localNormMap K L v (w : HeightOneSpectrum S) (a w)

omit [Module.Finite K L] in
theorem finiteNormMapComponent_one (v : HeightOneSpectrum R) :
    finiteNormMapComponent (R := R) (S := S) K L v 1 = 1 := by
  unfold finiteNormMapComponent
  refine Finset.prod_eq_one fun w _ => ?_
  haveI := mem_liesOver_of_mem_toFinset w
  exact map_one _

omit [Module.Finite K L] in
theorem finiteNormMapComponent_mul (v : HeightOneSpectrum R)
    (a b : ∀ w : HeightOneSpectrum S, (w.adicCompletion L)ˣ) :
    finiteNormMapComponent K L v (a * b) =
      finiteNormMapComponent K L v a * finiteNormMapComponent K L v b := by
  unfold finiteNormMapComponent
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  haveI := mem_liesOver_of_mem_toFinset w
  exact map_mul (localNormMap K L v (w : HeightOneSpectrum S)) (a w) (b w)

/-- The finite-place idèle norm map, as a `MonoidHom` on the un-restricted product of local
unit groups; assembled into a genuine `FiniteIdeleGroup` homomorphism below
(`NumberField.FiniteIdeleGroup.normMap`) once its values are shown to satisfy the
restricted-product condition (`eventually_finiteNormMap_mem_units`). -/
def finiteNormMap : (∀ w : HeightOneSpectrum S, (w.adicCompletion L)ˣ) →*
    ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ where
  toFun a v := finiteNormMapComponent K L v a
  map_one' := funext fun v => finiteNormMapComponent_one K L v
  map_mul' a b := funext fun v => finiteNormMapComponent_mul K L v a b

/-- If a family of local units `a` at places of `S` is almost everywhere a genuine local unit
(the restricted-product condition defining a finite idèle of `L`), so is its image under
`finiteNormMap`, at places of `R`: this is `eventually_localNormMap_mem_units` repackaged as a
statement about the assembled product map, using that a finite product of local units is a
local unit (`Subgroup.prod_mem`). -/
theorem eventually_finiteNormMap_mem_units
    {a : ∀ w : HeightOneSpectrum S, (w.adicCompletion L)ˣ}
    (ha : ∀ᶠ w : HeightOneSpectrum S in Filter.cofinite,
      a w ∈ (w.adicCompletionIntegers L).units) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      finiteNormMap K L a v ∈ (v.adicCompletionIntegers K).units := by
  filter_upwards [eventually_localNormMap_mem_units K L ha] with v hv
  unfold finiteNormMap finiteNormMapComponent
  refine Subgroup.prod_mem _ fun w _ => ?_
  exact hv (w : HeightOneSpectrum S) (mem_liesOver_of_mem_toFinset w)

end FiniteIdeleNormMap

namespace NumberField.FiniteIdeleGroup

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L)

/-- `finiteNormMap` repackaged as a `MonoidHom` between restricted products of unit groups
(rather than the un-restricted products it is originally stated on): this is the form that
composes directly with `RestrictedProduct.unitsEquiv` to give the finite idèle norm map below. -/
def finiteNormMapRestricted :
    (Πʳ w : HeightOneSpectrum S, [(w.adicCompletion L)ˣ,
        (Submonoid.ofClass (w.adicCompletionIntegers L)).units]_[Filter.cofinite]) →*
      Πʳ v : HeightOneSpectrum R, [(v.adicCompletion K)ˣ,
        (Submonoid.ofClass (v.adicCompletionIntegers K)).units]_[Filter.cofinite] where
  toFun y := ⟨finiteNormMap K L y.1, eventually_finiteNormMap_mem_units K L y.2⟩
  map_one' := Subtype.ext (map_one (finiteNormMap K L))
  map_mul' y1 y2 := Subtype.ext (map_mul (finiteNormMap K L) y1.1 y2.1)

/-- The finite-place idèle norm map `N_{L/K} : FiniteIdeleGroup S L →* FiniteIdeleGroup R K`,
sending a finite idèle `a` to the finite idèle whose component at each place `v` of `R` is
`∏_{w ∣ v} N_{L_w/K_v}(a w)`. Built by conjugating `finiteNormMapRestricted` by
`RestrictedProduct.unitsEquiv` on each side. -/
noncomputable def normMap : FiniteIdeleGroup S L →* FiniteIdeleGroup R K :=
  (RestrictedProduct.unitsEquiv fun v : HeightOneSpectrum R => v.adicCompletion K).symm.toMonoidHom.comp
    ((finiteNormMapRestricted K L).comp
      (RestrictedProduct.unitsEquiv fun w : HeightOneSpectrum S => w.adicCompletion L).toMonoidHom)

end NumberField.FiniteIdeleGroup

section InfinitePlaceNorm

/-! ### The archimedean local norm map

This section builds `NumberField.InfinitePlace.localNormMap`, the archimedean analogue of
`IsDedekindDomain.HeightOneSpectrum.localNormMap` above. Unlike the finite-place case, this needs
**no** companion "sends units to units" fact: `IsDedekindDomain.HeightOneSpectrum.localNormMap_mem_units`
exists because `FiniteAdeleRing` is a *restricted* product (only elements landing in
`adicCompletionIntegers` at almost every place are genuine finite adèles), so the local norm map
needs to be shown compatible with that support condition. `InfiniteAdeleRing K := (v :
InfinitePlace K) → v.Completion` (`Mathlib.NumberTheory.NumberField.InfiniteAdeleRing`) is a *plain*
(unrestricted) finite product -- there is no archimedean analogue of `adicCompletionIntegers`, no
support condition, and `InfinitePlace K` is a `Fintype` whenever `[NumberField K]`
(`Set.fintypeRange` in `Mathlib.NumberTheory.NumberField.InfinitePlace.Basic`), so the "finitely
many places lie over a given place" fact the assembly (gap 3, see `IdeleGroup.lean`'s survey) needs
is immediate (`Set.toFinite (NumberField.InfinitePlace.placesOver L v)`, already a Mathlib
definition in `Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification`) rather than requiring
its own `IsDedekindDomain.primesOver_finite`-style argument. -/

namespace NumberField.InfinitePlace

open scoped NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1]

/-- The local norm map `N_{L_w/K_v} : (w.Completion)ˣ →* (v.Completion)ˣ` at an infinite place `w`
of `L` lying over an infinite place `v` of `K`: the norm of the (degree-one-or-two, by
`Completion.finrank_eq_one_of_isUnramified` / `Completion.finrank_eq_two_of_isRamified`, though
this finiteness is not needed for the definition itself) extension `w.Completion` of `v.Completion`,
transported to units via `Units.map`. Built via the `Algebra v.Completion w.Completion` instance
that `NumberField.LiesOver.completionMap` (`Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances`)
gives, exactly mirroring `IsDedekindDomain.HeightOneSpectrum.localNormMap` above. -/
noncomputable def localNormMap : (w.Completion)ˣ →* (v.Completion)ˣ :=
  Units.map (Algebra.norm (v.Completion) : w.Completion →* v.Completion)

end NumberField.InfinitePlace

end InfinitePlaceNorm

section InfiniteIdeleNormMap

/-! ### Assembling the archimedean local norms into an infinite idèle norm map

This section builds `NumberField.InfiniteIdeleGroup.normMap : InfiniteIdeleGroup L →*
InfiniteIdeleGroup K`, the archimedean half of `IdeleGroup.normMap`
(`Langlands/IdeleGroup.lean`), mirroring `finiteNormMap`/`FiniteIdeleGroup.normMap` above but
simpler: `InfiniteAdeleRing` is an *unrestricted* product, so there is no analogue of
`eventually_finiteNormMap_mem_units` to prove, and the final assembly uses the plain
`MulEquiv.piUnits` (units of a product = product of units) instead of
`RestrictedProduct.unitsEquiv`. -/

open NumberField NumberField.InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]

omit [NumberField K] in
/-- Membership witness for an element of the `attach`ed `Finset` of places `w` of `L` lying
over a place `v` of `K`, unpacked from `Set.toFinite (placesOver L v)).toFinset` membership
into a genuine `LiesOver` instance -- the archimedean analogue of
`mem_liesOver_of_mem_toFinset` above. -/
theorem mem_liesOver_of_mem_placesOver_toFinset {v : InfinitePlace K}
    (w : {x : InfinitePlace L // x ∈ (Set.toFinite (placesOver L v)).toFinset}) :
    (w : InfinitePlace L).1.LiesOver v.1 := by
  have hw := w.2
  rwa [Set.Finite.mem_toFinset] at hw

/-- The `v`-component of the archimedean idèle norm map: the product of the local norms
`N_{L_w/K_v}(a w)` over the (finitely many) places `w` of `L` lying over `v`. -/
noncomputable def infiniteNormMapComponent (v : InfinitePlace K)
    (a : ∀ w : InfinitePlace L, (w.Completion)ˣ) : (v.Completion)ˣ :=
  ∏ w ∈ (Set.toFinite (placesOver L v)).toFinset.attach,
    haveI := mem_liesOver_of_mem_placesOver_toFinset w
    NumberField.InfinitePlace.localNormMap v (w : InfinitePlace L) (a w)

omit [NumberField K] in
theorem infiniteNormMapComponent_one (v : InfinitePlace K) :
    infiniteNormMapComponent (L := L) v 1 = 1 := by
  unfold infiniteNormMapComponent
  refine Finset.prod_eq_one fun w _ => ?_
  haveI := mem_liesOver_of_mem_placesOver_toFinset w
  exact map_one _

omit [NumberField K] in
theorem infiniteNormMapComponent_mul (v : InfinitePlace K)
    (a b : ∀ w : InfinitePlace L, (w.Completion)ˣ) :
    infiniteNormMapComponent v (a * b) =
      infiniteNormMapComponent v a * infiniteNormMapComponent v b := by
  unfold infiniteNormMapComponent
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  haveI := mem_liesOver_of_mem_placesOver_toFinset w
  exact map_mul (NumberField.InfinitePlace.localNormMap v (w : InfinitePlace L)) (a w) (b w)

/-- The archimedean idèle norm map, as a `MonoidHom` on the plain product of local unit
groups; assembled into a genuine `InfiniteIdeleGroup` homomorphism below
(`NumberField.InfiniteIdeleGroup.normMap`) via `MulEquiv.piUnits`. -/
def infiniteNormMap : (∀ w : InfinitePlace L, (w.Completion)ˣ) →*
    ∀ v : InfinitePlace K, (v.Completion)ˣ where
  toFun a v := infiniteNormMapComponent v a
  map_one' := funext fun v => infiniteNormMapComponent_one v
  map_mul' a b := funext fun v => infiniteNormMapComponent_mul v a b

end InfiniteIdeleNormMap

namespace NumberField.InfiniteIdeleGroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]

variable (K L)

/-- The archimedean idèle norm map `N_{L/K} : InfiniteIdeleGroup L →* InfiniteIdeleGroup K`,
sending an infinite idèle `a` to the infinite idèle whose component at each place `v` of `K` is
`∏_{w ∣ v} N_{L_w/K_v}(a w)`. Built by conjugating `infiniteNormMap` by `MulEquiv.piUnits` on
each side, exactly mirroring `FiniteIdeleGroup.normMap` above (but with `MulEquiv.piUnits` in
place of `RestrictedProduct.unitsEquiv`, since `InfiniteAdeleRing` is an unrestricted
product). -/
noncomputable def normMap : InfiniteIdeleGroup L →* InfiniteIdeleGroup K :=
  (MulEquiv.piUnits (M := fun v : InfinitePlace K => v.Completion)).symm.toMonoidHom.comp
    ((infiniteNormMap (K := K) (L := L)).comp
      (MulEquiv.piUnits (M := fun w : InfinitePlace L => w.Completion)).toMonoidHom)

end NumberField.InfiniteIdeleGroup

end
