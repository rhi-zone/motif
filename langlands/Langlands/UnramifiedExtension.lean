import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Conductor
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Langlands.MonogenicMaximalOrder

/-!
# Unramified extensions and lifting automorphisms of the residue field

Let `K` be a field with a `ValuativeRel`, `L / K` a field extension, and `A : ValuationSubring L`
a valuation subring of `L` extending `𝒪[K]` (i.e. `A.comap (algebraMap K L) = 𝒪[K]`) whose
decomposition subgroup `A.decompositionSubgroup K ≤ Gal(L/K)` acts on the residue field
`IsLocalRing.ResidueField A` through the algebra structure coming from `𝒪[K] → A`.

This file records two facts about this setup:

* `ValuationSubring.decompositionSubgroup_smul_algebraMap_residueField` : elements of the
  decomposition subgroup fix the base residue field `𝓀[K]` pointwise (as embedded in
  `IsLocalRing.ResidueField A` via `algebraMap 𝓀[K] (IsLocalRing.ResidueField A)`). This is a
  purely formal consequence of the fact that the decomposition subgroup consists of `K`-algebra
  automorphisms of `L`, unwound through the residue map (`IsLocalRing.ResidueField.residue_smul`,
  `IsLocalRing.ResidueField.algebraMap_residue`). Proved outright, no `sorry`.

* `ValuationSubring.exists_restrictNormalHom_decompositionSubgroup_surjective` : the
  **unramified lifting theorem** -- for every finite Galois subextension `M` of
  `IsLocalRing.ResidueField A` over `𝓀[K]`, every automorphism of `M/𝓀[K]` is the restriction (to
  `M`) of *some* element of the decomposition subgroup's induced action on the residue field. This
  is the genuinely deep, Hensel's-lemma-flavoured content: given a finite separable extension `M`
  of the residue field `𝓀[K]`, the theory of unramified extensions produces a finite unramified
  extension of `K` (inside `L`, with valuation ring inside `A`) whose residue field is `M`, and
  every automorphism of `M/𝓀[K]` lifts (uniquely, since unramified extensions of a Henselian field
  are classified by, and functorial in, their residue extension) to a `K`-automorphism of that
  unramified extension, hence (extending along `L`'s algebraic closedness / normality) to an
  element of `Gal(L/K)` stabilizing `A`, i.e. of the decomposition subgroup. This is **not** a
  consequence of Mathlib's `InfiniteGalois.restrictNormalHom_surjective` (surjectivity of
  restriction between two normal subextensions of one *fixed* Galois extension `L/K`): here the
  map being shown surjective goes from the decomposition subgroup of `A` (acting on the *residue*
  field of `A`, an a priori unrelated extension) to `Gal(M/𝓀[K])`, not a restriction map between
  intermediate fields of a single extension. Recorded as a `sorry`; not yet in Mathlib.

## Implementation notes

The hypotheses on `A` needed to state `decompositionSubgroup_smul_algebraMap_residueField` are
exactly the ones already established by `Langlands.WeilGroup` for its
`valuationSubringExtension K`: an `Algebra ↥(𝒪[K]) A` instance (`integersAlgebraMap`) compatible
with the ambient inclusion `𝒪[K] → K → L`. Compatibility is recorded as an explicit hypothesis
`hcompat` (rather than an `IsScalarTower ↥(𝒪[K]) A L` instance) to avoid a typeclass-resolution
failure encountered when this file's generic `L` is instantiated with a concrete
`AlgebraicClosure K` at the call site in `WeilGroup.lean`: the automatically-derived
`IsScalarTower` instance there fails Lean's instance-search unification even though it is
definitionally exactly `hcompat`, apparently because of how the discrimination tree indexes the
mangled instance name against the (already-assigned) metavariable for `L`. Passing the same fact
as an ordinary hypothesis sidesteps the issue entirely, since it is then just an ordinary term
provided at the call site (proved there by `rfl`, exactly as here). -/

noncomputable section

open ValuativeRel Valuation IsLocalRing Polynomial

-- **Instance-diamond fix**: `IsLocalRing.ResidueField.algebraOfIsIntegral` (a generic instance
-- giving `Algebra (ResidueField R) k` for any `k` integral over `R`) competes with
-- `IntermediateField.algebra'` for `Algebra 𝓀[K] ↥M` whenever `M` is an intermediate field of a
-- residue-field-flavoured ambient field (as `kbar := IsLocalRing.ResidueField
-- (valuationSubringExtension K)` is in `Langlands.WeilGroup`, since `𝓀[K]` is *itself*
-- `IsLocalRing.ResidueField ↥(𝒪[K])`, and `ResidueField.algebraOfIsIntegral` becomes newly
-- applicable once `Mathlib.RingTheory.DedekindDomain.Different` is imported (transitively enabling
-- the needed `Algebra.IsIntegral 𝒪[K] ↥M` premise). Both give a term of the same type
-- `Algebra 𝓀[K] ↥M`, but they are not defeq, breaking `rfl`-based proofs that implicitly assume the
-- specific `IntermediateField.algebra'` unfolding.
--
-- `IntermediateField.algebra'` is the canonical, structurally-intended instance here (`M` genuinely
-- *is* an intermediate field of `kbar` over `𝓀[K]`, by construction, not merely coincidentally
-- integral over a residue field); `ResidueField.algebraOfIsIntegral` is a more general instance
-- that does not know about this specific tower. Deprioritizing the latter (rather than raising the
-- former, which is not under this project's control to re-declare) makes instance search
-- consistently prefer `IntermediateField.algebra'` whenever both apply.
attribute [instance low] IsLocalRing.ResidueField.algebraOfIsIntegral

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [ValuativeRel K]
  (A : ValuationSubring L) [Algebra ↥(𝒪[K]) A]
  [IsLocalHom (algebraMap ↥(𝒪[K]) A)]

/-- Elements of the decomposition subgroup of `A` (i.e. `K`-algebra automorphisms of `L`
stabilizing `A`) fix the base residue field `𝓀[K]`, embedded in `IsLocalRing.ResidueField A` via
`algebraMap 𝓀[K] (IsLocalRing.ResidueField A)`, pointwise. Concretely: the induced action of
`A.decompositionSubgroup K` on `IsLocalRing.ResidueField A` restricts to the identity on the image
of `𝓀[K]`. A purely formal fact (no Henselian/unramified-extension input needed): every
`σ ∈ Gal(L/K)` fixes `K` pointwise by definition, hence fixes the image of `𝒪[K]` in `A` pointwise
(via `hcompat`, which records that the algebra structure `↥(𝒪[K]) → A` agrees with `↥(𝒪[K]) → K →
L`), hence (taking residues) fixes the image of `𝓀[K]` in `IsLocalRing.ResidueField A` pointwise. -/
theorem decompositionSubgroup_smul_algebraMap_residueField
    (hcompat : ∀ a : ↥(𝒪[K]), (algebraMap ↥(𝒪[K]) A a : L) = algebraMap K L (a : K))
    (σ : A.decompositionSubgroup K) (x : 𝓀[K]) :
    σ • algebraMap 𝓀[K] (IsLocalRing.ResidueField A) x =
      algebraMap 𝓀[K] (IsLocalRing.ResidueField A) x := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := ↥(𝒪[K])) x
  show σ • algebraMap (IsLocalRing.ResidueField ↥(𝒪[K])) (IsLocalRing.ResidueField A)
      (IsLocalRing.residue ↥(𝒪[K]) a) =
    algebraMap (IsLocalRing.ResidueField ↥(𝒪[K])) (IsLocalRing.ResidueField A)
      (IsLocalRing.residue ↥(𝒪[K]) a)
  rw [IsLocalRing.ResidueField.algebraMap_residue (R := ↥(𝒪[K])) (S := A) a,
    ← IsLocalRing.ResidueField.residue_smul (G := A.decompositionSubgroup K) σ
      (algebraMap ↥(𝒪[K]) A a)]
  congr 1
  -- `σ` fixes the image of `𝒪[K]` in `A`, since it fixes `K` pointwise and (by `hcompat`) the
  -- algebra structure on `A` is compatible with the inclusion `𝒪[K] → K → L`.
  apply Subtype.ext
  show (σ : Gal(L/K)) (algebraMap ↥(𝒪[K]) A a : L) = (algebraMap ↥(𝒪[K]) A a : L)
  rw [hcompat a]
  exact (σ : Gal(L/K)).commutes (a : K)

/-- **The unramified lifting theorem** (Hensel's-lemma-flavoured; not yet in Mathlib): for every
finite Galois subextension `M` of `IsLocalRing.ResidueField A / 𝓀[K]`, every automorphism of
`M/𝓀[K]` is realized by (i.e. is the restriction to `M` of) the residue action of *some* element of
the decomposition subgroup `A.decompositionSubgroup K`.

Sketch of the (missing) proof: given `M`, choose a finite separable extension `K' / K` inside `L`
whose residue field (for the valuation subring `A ⊓ K' = A.comap (algebraMap K' L)`, or rather the
unique valuation subring of `K'` lying under `A`) is `M` -- this is the existence half of the
theory of unramified extensions of a Henselian field, itself built on Hensel's lemma (lift a
primitive element of `M/𝓀[K]` to a monic polynomial over `𝒪[K]` via `Polynomial.lifts`, then use
Henselian-ness to find a root generating the corresponding unramified extension). Given an
automorphism `g` of `M/𝓀[K]`, functoriality of this correspondence (unramified extensions of `K`
are classified by, and equivalent as a category to, finite separable extensions of `𝓀[K]`) lifts
`g` to a `K`-automorphism of `K'`; extending this automorphism of `K'` to all of `L` (`L/K'` being
algebraic) via `IsAlgClosed`/normality gives an element of `Gal(L/K)`, which (since it stabilizes
the valuation subring of `K'` lying under `A`, hence -- using uniqueness of extension of the
valuation, i.e. the same Henselian/decomposition-subgroup-is-everything argument as
`LocalField.decompositionSubgroup_eq_top` -- stabilizes `A` itself) lies in the decomposition
subgroup and induces `g` on `M` by construction.

`[IsAlgClosed L]` is stated as an explicit hypothesis (rather than left implicit, as the proof
sketch's informal appeal to "IsAlgClosed/normality" originally left it) precisely to make this
"extend the automorphism of `K'` to all of `L`" step available: extending along a merely normal
(not algebraically closed) `L/K'` would need `Normal K L` instead, which is not assumed here. The
one call site (`LocalField.surjective_restrictNormalHom_comp_residueAction'` in
`Langlands.WeilGroup`) instantiates `L := AlgebraicClosure K`, which already has an `IsAlgClosed`
instance in Mathlib, so this costs nothing there.

**Status (current pass):** the import-diamond previously flagged in
`Langlands.MonogenicMaximalOrder`'s docstring as blocking a direct merge into this file was
re-checked directly (not assumed): this file now imports `Langlands.MonogenicMaximalOrder`
(pulling in `Mathlib.RingTheory.DedekindDomain.Different` / `Mathlib.RingTheory.Conductor`
transitively) and `Langlands.WeilGroup` still builds cleanly against it. So
`Algebra.adjoin_eq_top_of_isUnit_aeval_derivative_minpoly` is now directly usable from here; the
diamond is no longer a reason to keep the two files separate (kept separate anyway, for now, since
splitting the discriminant-unit fact out is still a reasonable modularity boundary on its own
merits).

Everything on the "existence of `K'`" side of the sketch above through the polynomial/`AdjoinRoot`
level is now available (all in this file): `HenselianLocalRing.exists_monic_lift_minpoly`,
`irreducible_lift_minpoly`/`irreducible_map_lift_minpoly`, `separable_lift_minpoly`/
`separable_map_lift_minpoly`, `exists_ringHom_adjoinRoot_map_of_isAlgClosed` (giving a root
`x : L` of the lifted minimal polynomial and an embedding `AdjoinRoot p ↪ L`, `p` the lift mapped to
`K`), `isDomain_adjoinRoot_lift_minpoly`, `isLocalRing_adjoinRoot_lift_minpoly`,
`finrank_adjoinRoot_lift_minpoly`, `residueField_equiv_adjoinRoot_lift_minpoly` (identifying
`IsLocalRing.ResidueField (AdjoinRoot f) ≃+* M`, `f` the monic lift), and `adjoinRootMap`/
`injective_adjoinRootMap`/`injective_comp_adjoinRootMap` (realizing `AdjoinRoot f` itself, not just
its fraction field, as a subring of `L`).

**What is still missing, precisely:** none of the above identifies `AdjoinRoot f`'s image in `L`
with `A.comap (algebraMap K' L)` (`K' := K⟮x⟯ ≤ L`, the intermediate field generated by the root
`x`) -- i.e. with the *valuation subring of `K'` lying under `A`*. That identification is the
missing bridge, needed for two things: (a) to invoke
`Algebra.adjoin_eq_top_of_isUnit_aeval_derivative_minpoly` (needing `IsIntegralClosure
(A.comap (algebraMap K' L)) ↥(𝒪[K]) K'`, i.e. that this valuation subring *is* the integral closure
of `𝒪[K]` in `K'`) to conclude `𝒪[K][x]` is the whole ring of integers, not just a suborder of it;
(b) to then identify `IsLocalRing.ResidueField (A.comap (algebraMap K' L))` with `M` via
`residueField_equiv_adjoinRoot_lift_minpoly` composed with that integral-closure identification.

Checked directly (not assumed): `grep`-ing `Mathlib/RingTheory/Valuation/ValuationSubring.lean` for
`IsIntegral` and loogle-searching for a `ValuationSubring`/integral-closure characterization both
turn up nothing. The underlying fact -- that a valuation subring of an algebraic extension
restricting to a given valuation ring below consists *exactly* of the elements integral over that
base ring, in the presence of a Henselian (hence unique-extension) hypothesis -- is genuine
valuation theory not otherwise available in this project or in Mathlib (sketch: the integral
closure `C` of the Henselian local domain `𝒪[K]` in the finite extension `K'` is itself local, by
Henselian-ness, hence a Dedekind domain that is local, i.e. a DVR/valuation ring of `K'`; general
valuation-ring domination then forces any valuation subring of `K'` containing `C` and sharing its
fraction field to be either `C` or all of `K'`, pinning it down to `C` itself). Not attempted here
-- it is a self-contained undertaking on the same order of size as the polynomial-level work above.

Beyond that bridge, the remaining steps of the sketch (functoriality lifting `g : M ≃ₐ[𝓀[K]] M` to a
`K`-automorphism of `K'` via the residue-field identification above; extending that automorphism of
`K'` to `σ : L ≃ₐ[K] L` via `IsAlgClosed L`; and showing `σ` stabilizes `A` via
`LocalField.valuationSubring_eq_of_comap_eq_of_isNonarchimedeanLocalField`, applied at `K'` rather
than at `L` itself, once `A.comap (algebraMap K' L)` and its `σ`-translate are known to agree with
the unique valuation subring of `K'` over `𝒪[K]`) are also not attempted here. Note also that this
theorem's own hypotheses do not yet include Henselian-ness of `↥(𝒪[K])` (needed to invoke any of the
`HenselianLocalRing` lemmas above) or `IsNonarchimedeanLocalField K` (needed for the
uniqueness-of-valuation-extension step); at the one call site
(`Langlands.WeilGroup.surjective_restrictNormalHom_comp_residueAction'`) both already hold, via the
`henselianLocalRing` instance below and the ambient `IsNonarchimedeanLocalField K` there, so adding
them as explicit hypotheses here (rather than leaving them implicit as before) would cost nothing at
the call site once the proof is actually assembled. -/
theorem exists_restrictNormalHom_decompositionSubgroup_surjective
    (hcompat : ∀ a : ↥(𝒪[K]), (algebraMap ↥(𝒪[K]) A a : L) = algebraMap K L (a : K))
    [IsAlgClosed L] [IsGalois 𝓀[K] (IsLocalRing.ResidueField A)]
    (M : IntermediateField 𝓀[K] (IsLocalRing.ResidueField A))
    [FiniteDimensional 𝓀[K] M] [Normal 𝓀[K] M] :
    Function.Surjective fun σ : A.decompositionSubgroup K =>
      AlgEquiv.restrictNormalHom (F := 𝓀[K]) M
        (AlgEquiv.ofRingEquiv (f := (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
          (IsLocalRing.ResidueField A)) σ)
          (decompositionSubgroup_smul_algebraMap_residueField A hcompat σ)) := by
  sorry

end ValuationSubring

/-! ### `𝒪[K]` is Henselian, for `K` a nonarchimedean local field

The missing ingredient (flagged as an unstated hypothesis gap in
`exists_restrictNormalHom_decompositionSubgroup_surjective` above) needed to actually invoke
Hensel's lemma (`HenselianLocalRing.TFAE`, `IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`) for
the unramified lifting theorem: `𝒪[K]` is a Henselian local ring. This is *not* a new fact -- the
hard work (`IsAdicComplete 𝓂[K] 𝒪[K]`) is already a Mathlib instance
(`Mathlib.NumberTheory.LocalField.Basic`, via compactness of `𝒪[K]` and Noetherianity of the DVR
structure), found by checking whether the `IsAdic`/`T2Space` bridge was already done before
attempting to build it -- it was. `IsAdicComplete.henselianRing` then gives `HenselianRing 𝒪[K]
𝓂[K]` directly, and `HenselianLocalRing.mk` packages this (with the already-available `IsLocalRing
𝒪[K]` from `IsDiscreteValuationRing.toIsLocalRing`) into `HenselianLocalRing 𝒪[K]`.

The only wrinkle: `IsAdicComplete 𝓂[K] 𝒪[K]` is stated for `[UniformSpace K] [IsUniformAddGroup K]`
(a uniformity making the topology compatible with the group structure), which is not automatically
available from `IsNonarchimedeanLocalField K`'s own `[TopologicalSpace K]` -- it is supplied locally
via `IsTopologicalAddGroup.rightUniformSpace K` / `isUniformAddGroup_of_addCommGroup`, exactly the
pattern already used elsewhere in this project (`WeilGroup.decompositionSubgroup_eq_top`). -/

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **`𝒪[K]` is a Dedekind domain**, for `K` a nonarchimedean local field. `𝒪[K]` is already known
to be a discrete valuation ring (`IsDiscreteValuationRing 𝒪[K]`, in
`Mathlib.NumberTheory.LocalField.Basic`); `IsDiscreteValuationRing.TFAE` packages the equivalence
of DVR with several other characterizations, including `IsDedekindDomain`, for a Noetherian local
domain that is not a field. `IsNoetherianRing` comes for free from `IsPrincipalIdealRing` (which
`IsDiscreteValuationRing` extends); `IsLocalRing` likewise; not being a field is
`IsDiscreteValuationRing.not_isField`. -/
instance isDedekindDomain : IsDedekindDomain ↥(𝒪[K]) :=
  ((IsDiscreteValuationRing.TFAE ↥(𝒪[K]) (IsDiscreteValuationRing.not_isField ↥(𝒪[K]))).out 0 2).mp
    (inferInstance : IsDiscreteValuationRing ↥(𝒪[K]))

/-- **`𝒪[K]` is a Henselian local ring**, for `K` a nonarchimedean local field. -/
instance henselianLocalRing : HenselianLocalRing ↥(𝒪[K]) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI : HenselianRing ↥(𝒪[K]) 𝓂[K] := IsAdicComplete.henselianRing _ _
  refine HenselianLocalRing.mk fun f hf a₀ ha₀ hderiv => ?_
  exact HenselianRing.is_henselian f hf a₀ ha₀ (hderiv.map (Ideal.Quotient.mk 𝓂[K]))

/-! ### A monic lift of a minimal polynomial over a Henselian local ring

The first ingredient of the unramified lifting theorem's existence half (see
`ValuationSubring.exists_restrictNormalHom_decompositionSubgroup_surjective`): given a Henselian
local ring `R` with residue field `k := IsLocalRing.ResidueField R`, and an element `β₀` of a field
`l` algebraic over `k`, the (monic) minimal polynomial of `β₀` over `k` lifts to a monic polynomial
over `R` of the same degree, reducing to it mod the maximal ideal.

This is a purely coefficient-wise construction and does *not* yet use Hensel's lemma itself (that
enters at the next step: finding a root of this lift in `R`, via `HenselianLocalRing.TFAE`) --
`Polynomial.mem_lifts_of_surjective` gives *some* lift along the (surjective) residue map, and
`Polynomial.lifts_and_natDegree_eq_and_monic` upgrades this to a monic lift of the same degree,
since the minimal polynomial being lifted is itself monic. Stated for a general
`HenselianLocalRing R` since that is the hypothesis available at the intended call site, though the
construction itself only needs `IsLocalRing R` and surjectivity of the residue map. -/

theorem HenselianLocalRing.exists_monic_lift_minpoly {R : Type*} [CommRing R]
    [HenselianLocalRing R] {l : Type*} [Field l] [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) :
    ∃ f : R[X], f.Monic ∧ f.natDegree = (minpoly (IsLocalRing.ResidueField R) β₀).natDegree ∧
      f.map (algebraMap R (IsLocalRing.ResidueField R)) =
        minpoly (IsLocalRing.ResidueField R) β₀ := by
  have hlifts :=
    Polynomial.mem_lifts_of_surjective (f := algebraMap R (IsLocalRing.ResidueField R))
      IsLocalRing.residue_surjective (minpoly (IsLocalRing.ResidueField R) β₀)
  obtain ⟨f, hf1, hf2, hf3⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts (minpoly.monic hβ₀)
  exact ⟨f, hf3, hf2, hf1⟩

/-! ### The monic lift is irreducible, first over `R` itself, then over the fraction field

The second ingredient of the unramified lifting theorem's existence half: a monic lift `f` of
`β₀`'s (irreducible) minimal polynomial over the residue field `k := IsLocalRing.ResidueField R`
is itself irreducible, not just over `R` but over the fraction field `K` of `R` -- this is what
lets `f` cut out a genuine finite field extension of `K` (rather than merely a monic polynomial
that could factor).

Two Mathlib pieces compose here, both confirmed by loogle against their stated names before use:

* `Polynomial.Monic.irreducible_of_irreducible_map` : a monic polynomial over a domain `R` is
  irreducible (over `R`) if its image under *any* ring hom `R →+* S` (`S` a domain) is irreducible.
  Applied to the residue map `R →+* k`, whose image of `f` is (by hypothesis) `β₀`'s minimal
  polynomial -- irreducible by `minpoly.irreducible`, since `β₀` is integral over `k` (`l` and `k`
  both fields makes `IsDomain` trivial on both sides). This step alone only needs `IsDomain R`, not
  `IsIntegrallyClosed R`, and is recorded as its own lemma (`irreducible_lift_minpoly`, giving
  `Irreducible f` in `R[X]` itself) because the next construction step (`AdjoinRoot f` is a domain,
  via `AdjoinRoot.isDomain_of_prime`) needs exactly this `R[X]`-level fact, not merely its image
  over `Frac(R)`.
* `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` : **Gauss's lemma** for
  integrally closed domains -- a monic polynomial over an integrally closed domain `R` is
  irreducible over `R` iff its image is irreducible over `Frac(R)`. This is exactly where
  `IsIntegrallyClosed R` is needed (true of `𝒪[K]` at the intended call site, being a valuation
  ring), converting "irreducible over `R`" (from the previous bullet) into "irreducible over `K`".
-/

/-- The monic lift `f` (of `β₀`'s minimal polynomial over `k := IsLocalRing.ResidueField R`) is
irreducible already in `R[X]`, before any Gauss's-lemma transfer to a fraction field. Only needs
`IsDomain R` (not `IsIntegrallyClosed R`): `Polynomial.Monic.irreducible_of_irreducible_map` shows a
monic polynomial over a domain is irreducible as soon as *some* image of it under a ring hom into a
domain is irreducible, and here that image (under the residue map) is `minpoly k β₀`, irreducible
since `β₀` is integral over the field `k`. Extracted as its own lemma because the domain-ness of
`AdjoinRoot f` (`AdjoinRoot.isDomain_of_prime`, via `Irreducible f → Prime f` in the UFD `R[X]`)
needs precisely this `R[X]`-level statement, not merely its image over `Frac(R)`. -/
theorem HenselianLocalRing.irreducible_lift_minpoly {R : Type*} [CommRing R] [IsDomain R]
    [HenselianLocalRing R] {l : Type*} [Field l] [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀) :
    Irreducible f := by
  apply Polynomial.Monic.irreducible_of_irreducible_map (algebraMap R (IsLocalRing.ResidueField R))
    f hf
  rw [hfmap]
  exact minpoly.irreducible hβ₀

theorem HenselianLocalRing.irreducible_map_lift_minpoly {R : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [HenselianLocalRing R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] {l : Type*} [Field l] [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀) :
    Irreducible (f.map (algebraMap R K)) :=
  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map hf).mp
    (HenselianLocalRing.irreducible_lift_minpoly hβ₀ hf hfmap)

/-! ### The monic lift `f` is separable, hence so is `p := f.map (algebraMap R K)`

The remaining ingredient needed to discharge `[Algebra.IsSeparable K L]` at the call site of
`Algebra.adjoin_eq_top_of_isUnit_aeval_derivative_minpoly` (`Langlands.MonogenicMaximalOrder`,
kept in its own file for import-diamond reasons -- see that file's docstring): `f` itself is
separable in `R[X]`, hence (`Polynomial.Separable.map`, valid for *any* ring hom out of a
`CommSemiring`, no domain hypotheses needed) `p := f.map (algebraMap R K)` is separable in `K[X]`.

The originally-sketched route via `Algebra.discr` (basis discriminant) does not exist in a
`Polynomial`-level, `map`-compatible form in Mathlib; the actual bridge found by loogle is the
**resultant** of a polynomial and its derivative (`Polynomial.resultant`,
`Mathlib.RingTheory.Polynomial.Resultant.Basic`):
`Polynomial.isUnit_resultant_iff_isCoprime` identifies `IsUnit (f.resultant g)` (for `f` monic)
with `IsCoprime f g`, and `Polynomial.separable_def` identifies `f.Separable` with
`IsCoprime f (derivative f)` -- so separability of a monic polynomial is exactly unit-ness of the
resultant of it and its derivative. This *is* the discriminant, up to a sign/leading-term twist
(see `Polynomial.discr`'s docstring), but the resultant form is what actually has the needed
`map`-compatibility lemma, `Polynomial.resultant_map_map`.

The argument:

1. `k := IsLocalRing.ResidueField R` is finite (hypothesis `[Finite k]`, true at the intended call
   site `R = 𝒪[K]` via the already-existing instance
   `IsNonarchimedeanLocalField.instFiniteResidueField...`), hence perfect (`PerfectField.ofFinite`),
   so `minpoly k β₀` -- irreducible since `β₀` is integral -- is separable
   (`PerfectField.separable_of_irreducible`). Via `hfmap`, this is `(f.map (residue R)).Separable`.
2. Unwinding `Separable`/`isUnit_resultant_iff_isCoprime` at `f.map (residue R)` (monic, since `f`
   is) gives `IsUnit ((f.map (residue R)).resultant (derivative (f.map (residue R))))`, at the
   *default* size parameters (`(f.map (residue R)).natDegree`, `(derivative (f.map (residue R))
   ).natDegree`).
3. **The size-parameter subtlety**: `Polynomial.resultant`'s size arguments `m n` are explicit
   (with `natDegree`-valued `optParam` defaults), and `Polynomial.resultant_map_map` (transporting
   a resultant along a ring hom) holds for *arbitrary* `m n`, not just the natDegree-valued
   defaults of whichever side of the hom they're read off from -- since reducing mod a maximal
   ideal *can* drop the degree of a derivative (e.g. `char k = p ∣ f.natDegree` can kill the
   leading coefficient of `derivative f` upon reduction, even though `R` has characteristic `0` so
   `derivative f` itself doesn't degenerate over `R`), the default-`n` resultant read off from
   `f.map (residue R)`'s own `natDegree`s need not equal the default-`n` resultant read off from
   `f`'s. The fix: since `f` (hence `f.map (residue R)`) is *monic*,
   `Polynomial.resultant_add_right_deg` shows padding the second polynomial's size argument past
   its actual degree multiplies the resultant by (a power of) the *first* polynomial's coefficient
   at the fixed size `m`, which is `1` for a monic polynomial at `m = natDegree` -- so the resultant
   at the (possibly larger) `R`-side padding `(derivative f).natDegree` agrees with the resultant at
   `f.map (residue R)`'s own smaller default size. This lets step 2's fact be re-expressed at the
   padded size compatible with `resultant_map_map`, transporting it back across `R → k` to conclude
   `IsUnit (f.resultant (derivative f))` **in `k`**, i.e. that `(residue R) (f.resultant
   (derivative f))` is nonzero.
4. `(residue R) x ≠ 0 ↔ x ∉ maximalIdeal R` (`IsLocalRing.residue_eq_zero_iff`) `↔ IsUnit x`
   (`IsLocalRing.mem_maximalIdeal`, `mem_nonunits_iff`, `R` local) gives `IsUnit (f.resultant
   (derivative f))` **in `R` itself** (not just its image in `k`) -- this is the fact that would
   let `MonogenicMaximalOrder.lean`'s `hunit` hypothesis (`IsUnit (aeval x (minpoly A x).derivative)`)
   eventually be discharged too, though wiring that up is a separate, further step not attempted
   here.
5. `Polynomial.isUnit_resultant_iff_isCoprime hf` converts this back to `IsCoprime f (derivative
   f)`, i.e. (`Polynomial.separable_def`) `f.Separable`. -/

/-- **Extracted from the proof below**: the monic lift `f` has `IsUnit` resultant with its own
derivative, already **in `R` itself** (`hxunit` in the docstring above), not merely after reducing
to the residue field `k`. This is exactly the "discriminant is a unit" fact needed to discharge
the `hunit` hypothesis of `Algebra.adjoin_eq_top_of_isUnit_aeval_derivative_minpoly`
(`Langlands.MonogenicMaximalOrder`) once wired through a root of `f` in any `R`-algebra -- see
`Polynomial.isUnit_aeval_derivative_of_isUnit_resultant` below for that further step. Extracted as
its own lemma (rather than left inline inside `separable_lift_minpoly`) so both consumers can share
it without duplicating the resultant/size-padding argument. -/
theorem HenselianLocalRing.isUnit_resultant_lift_minpoly {R : Type*} [CommRing R] [IsLocalRing R]
    [Finite (IsLocalRing.ResidueField R)] {l : Type*} [Field l]
    [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀) :
    IsUnit (Polynomial.resultant f (Polynomial.derivative f)) := by
  have hφeq : algebraMap R (IsLocalRing.ResidueField R) = IsLocalRing.residue R :=
    IsLocalRing.ResidueField.algebraMap_eq R
  rw [hφeq] at hfmap
  set φ := IsLocalRing.residue R with hφ
  haveI : PerfectField (IsLocalRing.ResidueField R) := PerfectField.ofFinite
  have hsepbar : (minpoly (IsLocalRing.ResidueField R) β₀).Separable :=
    PerfectField.separable_of_irreducible (minpoly.irreducible hβ₀)
  rw [← hfmap] at hsepbar
  have hcop_bar : IsCoprime (f.map φ) (Polynomial.derivative (f.map φ)) :=
    (Polynomial.separable_def _).mp hsepbar
  have hmonicbar : (f.map φ).Monic := hf.map φ
  have hmbar : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
  have hIsUnitBar : IsUnit (Polynomial.resultant (f.map φ) (Polynomial.derivative (f.map φ))) :=
    (Polynomial.isUnit_resultant_iff_isCoprime hmonicbar).mpr hcop_bar
  have hn0len : (Polynomial.derivative (f.map φ)).natDegree ≤ (Polynomial.derivative f).natDegree :=
    by rw [Polynomial.derivative_map]; exact Polynomial.natDegree_map_le
  obtain ⟨pad, hpadeq⟩ := Nat.le.dest hn0len
  have hpad : Polynomial.resultant (f.map φ) (Polynomial.derivative (f.map φ))
      ((f.map φ).natDegree) ((Polynomial.derivative f).natDegree) =
      Polynomial.resultant (f.map φ) (Polynomial.derivative (f.map φ)) := by
    rw [← hpadeq, Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl, hmonicbar.coeff_natDegree,
      one_pow, one_mul]
  have hIsUnitBar' : IsUnit (Polynomial.resultant (f.map φ) (Polynomial.derivative (f.map φ))
      ((f.map φ).natDegree) ((Polynomial.derivative f).natDegree)) := by
    rw [hpad]; exact hIsUnitBar
  have hderiv_map : Polynomial.derivative (f.map φ) = (Polynomial.derivative f).map φ :=
    Polynomial.derivative_map f φ
  have hresR : Polynomial.resultant (f.map φ) ((Polynomial.derivative f).map φ)
      ((f.map φ).natDegree) ((Polynomial.derivative f).natDegree) =
      φ (Polynomial.resultant f (Polynomial.derivative f) ((f.map φ).natDegree)
        ((Polynomial.derivative f).natDegree)) :=
    Polynomial.resultant_map_map f (Polynomial.derivative f) _ _ φ
  have hIsUnitBar'' : IsUnit (φ (Polynomial.resultant f (Polynomial.derivative f)
      ((f.map φ).natDegree) ((Polynomial.derivative f).natDegree))) := by
    rw [← hresR, ← hderiv_map]; exact hIsUnitBar'
  rw [hmbar] at hIsUnitBar''
  have hx_ne : φ (Polynomial.resultant f (Polynomial.derivative f)) ≠ 0 :=
    isUnit_iff_ne_zero.mp hIsUnitBar''
  have hx_notmem : Polynomial.resultant f (Polynomial.derivative f) ∉ IsLocalRing.maximalIdeal R :=
    fun hmem => hx_ne (IsLocalRing.residue_eq_zero_iff _ |>.mpr hmem)
  by_contra hnu
  exact hx_notmem (IsLocalRing.mem_maximalIdeal _ |>.mpr (mem_nonunits_iff.mpr hnu))

/-- **The monic lift `f` is separable**, given that the residue field `k := IsLocalRing.ResidueField
R` is finite. Now just a thin wrapper around `HenselianLocalRing.isUnit_resultant_lift_minpoly`
(the resultant-based argument, see the section docstring above) composed with
`Polynomial.isUnit_resultant_iff_isCoprime` / `Polynomial.separable_def`. -/
theorem HenselianLocalRing.separable_lift_minpoly {R : Type*} [CommRing R] [IsLocalRing R]
    [Finite (IsLocalRing.ResidueField R)] {l : Type*} [Field l]
    [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀) :
    f.Separable :=
  (Polynomial.separable_def f).mpr <|
    (Polynomial.isUnit_resultant_iff_isCoprime hf).mp
      (HenselianLocalRing.isUnit_resultant_lift_minpoly hβ₀ hf hfmap)

/-- **`p := f.map (algebraMap R K)` is separable**, given `f.Separable` (from
`separable_lift_minpoly` above): `Polynomial.Separable.map` transports separability along *any*
ring hom, no domain/field hypotheses on the target needed. This is the fact that, once wired
through `AdjoinRoot p ≃ₐ[K] K⟮x⟯` (`x` the root produced by
`exists_ringHom_adjoinRoot_map_of_isAlgClosed`), discharges the `[Algebra.IsSeparable K L]`
hypothesis of `Algebra.adjoin_eq_top_of_isUnit_aeval_derivative_minpoly`
(`Langlands.MonogenicMaximalOrder`) at its intended call site -- that wiring itself is a further
step not attempted here. -/
theorem HenselianLocalRing.separable_map_lift_minpoly {R : Type*} [CommRing R] [IsLocalRing R]
    [Finite (IsLocalRing.ResidueField R)] {K : Type*} [Field K] [Algebra R K] {l : Type*} [Field l]
    [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀) :
    (f.map (algebraMap R K)).Separable :=
  (HenselianLocalRing.separable_lift_minpoly hβ₀ hf hfmap).map

/-! ### Transferring "discriminant is a unit" from `R` to a root in any `R`-algebra domain

The remaining ingredient (beyond `isUnit_resultant_lift_minpoly` above) needed to discharge the
`hunit` hypothesis of `Algebra.adjoin_eq_top_of_isUnit_aeval_derivative_minpoly`
(`Langlands.MonogenicMaximalOrder`) at a root `x` of `f` living in some `R`-algebra `C` (not
merely in `R` itself, where `isUnit_resultant_lift_minpoly` already lands the fact): given
`f(x) = 0` in `C`, factor `f.map (algebraMap R C) = (X - C x) * q` (factor theorem,
`Polynomial.dvd_iff_isRoot`), then use multiplicativity of the resultant in its first argument
(`Polynomial.resultant_mul_left`) together with `Res(X - x, g) = g(x)`
(`Polynomial.resultant_X_sub_C_left`) to write

`(algebraMap R C) (Res(f, f')) = Res(f.map .., (f'.map ..)) = f'(x) * Res(q, f'.map ..)`

(`Polynomial.resultant_map_map`, which holds for arbitrary size parameters `m n`, not just
`natDegree`-defaults, so no size-padding subtlety is needed here -- unlike the residue-field
version in `isUnit_resultant_lift_minpoly`, `algebraMap R C` need not be injective for this
identity, though injectivity is not assumed or needed below either). Since the left side is a unit
(the image of `hunit` under `algebraMap R C`) and the ring is commutative, both factors on the
right are units (`isUnit_of_mul_isUnit_left`); in particular `f'(x)` is. -/

/-- **"Discriminant is a unit" transfers to any root.** If `f : R[X]` is monic with
`IsUnit (f.resultant (derivative f))` (e.g. via `HenselianLocalRing.isUnit_resultant_lift_minpoly`),
and `x : C` (`C` a domain `R`-algebra) is a root of `f`, then `aeval x (derivative f)` is a unit in
`C`. See the section docstring above for the factorization argument. -/
theorem Polynomial.isUnit_aeval_derivative_of_isUnit_resultant {R C : Type*} [CommRing R]
    [CommRing C] [IsDomain C] [Algebra R C] {f : R[X]} (hf : f.Monic)
    (hunit : IsUnit (Polynomial.resultant f (Polynomial.derivative f))) {x : C}
    (hx : Polynomial.aeval x f = 0) :
    IsUnit (Polynomial.aeval x (Polynomial.derivative f)) := by
  set φ := algebraMap R C with hφ
  set fC := f.map φ with hfC_def
  set g := (Polynomial.derivative f).map φ with hg_def
  have hfCmonic : fC.Monic := hf.map φ
  have hxroot : fC.IsRoot x := by
    rw [Polynomial.IsRoot.def, hfC_def, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hx
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hxroot
  have hXmonic : (Polynomial.X - Polynomial.C x).Monic := Polynomial.monic_X_sub_C x
  have hqmonic : q.Monic := hXmonic.of_mul_monic_left (hq ▸ hfCmonic)
  have hdegsum : fC.natDegree = 1 + q.natDegree := by
    rw [hq, hXmonic.natDegree_mul hqmonic, Polynomial.natDegree_X_sub_C]
  have hfCdeg : fC.natDegree = f.natDegree := hf.natDegree_map φ
  have hsize : f.natDegree = 1 + q.natDegree := by rw [← hfCdeg]; exact hdegsum
  have hgdeg : g.natDegree ≤ (Polynomial.derivative f).natDegree := Polynomial.natDegree_map_le
  have hmul := Polynomial.resultant_mul_left (Polynomial.X - Polynomial.C x) q g
    (Polynomial.derivative f).natDegree hgdeg
  rw [Polynomial.natDegree_X_sub_C, ← hq, ← hsize] at hmul
  have heval : (Polynomial.X - Polynomial.C x).resultant g 1 (Polynomial.derivative f).natDegree
      = Polynomial.eval x g := Polynomial.resultant_X_sub_C_left g _ x hgdeg
  have heval' : Polynomial.eval x g = Polynomial.aeval x (Polynomial.derivative f) := by
    rw [hg_def, Polynomial.eval_map, ← Polynomial.aeval_def]
  have hmain : fC.resultant g f.natDegree (Polynomial.derivative f).natDegree
      = φ (Polynomial.resultant f (Polynomial.derivative f)) := by
    rw [hfC_def, hg_def]
    exact Polynomial.resultant_map_map f (Polynomial.derivative f) f.natDegree
      (Polynomial.derivative f).natDegree φ
  rw [hmain, heval, heval'] at hmul
  have hunitφ : IsUnit (φ (Polynomial.resultant f (Polynomial.derivative f))) :=
    hunit.map (algebraMap R C)
  rw [hmul] at hunitφ
  exact isUnit_of_mul_isUnit_left hunitφ

/-! ### `AdjoinRoot f`: a finite free, local, domain extension with residue field `l`

The third ingredient (see `ValuationSubring.exists_restrictNormalHom_decompositionSubgroup_surjective`
above): given the monic lift `f` of `β₀`'s minimal polynomial (from `exists_monic_lift_minpoly`,
irreducible in `R[X]` by `irreducible_lift_minpoly`), `R' := AdjoinRoot f` is

1. a finite free `R`-module of rank `n = f.natDegree`, which (given the extra hypothesis that `β₀`
   is a **primitive element**, i.e. `k⟮β₀⟯ = ⊤`, phrased as `IntermediateField.adjoin k {β₀} = ⊤` to
   avoid depending on the scoped `⟮⟯` notation) equals `[l : k]`
   (`finrank_adjoinRoot_lift_minpoly`);
2. a domain (`isDomain_adjoinRoot_lift_minpoly`), via `Irreducible f → Prime f` in the UFD `R[X]`
   (`R[X]` is a UFD whenever `R` is, e.g. `R` a PID at the intended call site `𝒪[K]`); and
3. local, with the ideal `M₀ := Ideal.map (AdjoinRoot.of f) (maximalIdeal R)` as its unique maximal
   ideal (`isLocalRing_adjoinRoot_lift_minpoly`).

**On (3), the "IsLocalRing R'" step**: the route sketched in the task brief (Cohen-Seidenberg
lying-over, via `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` in
`Mathlib.RingTheory.Ideal.GoingUp`) works directly and is what's used below; no more direct packaged
Mathlib lemma ("finite algebra over a local ring with field quotient ⟹ local") was found. The
argument: `M₀` itself is maximal, since `AdjoinRoot f ⧸ M₀ ≅ Polynomial k ⧸ span {f.map (residue R)}
= Polynomial k ⧸ span {minpoly k β₀}` (via `AdjoinRoot.quotEquivQuotMap` and `hfmap`) is a field
(`AdjoinRoot.instField`, since `minpoly k β₀` is irreducible). For *uniqueness*: `R'` is
module-finite over `R` (from the `PowerBasis`), hence integral, so for *any* maximal ideal `I` of
`R'`, `I.comap (algebraMap R R')` is maximal in `R` (Cohen-Seidenberg going-up); since `R` is local
this comap equals `maximalIdeal R`, so (applying `Ideal.map` back and using `Ideal.map_comap_le`)
`M₀ ≤ I`; two maximal ideals with `M₀ ≤ I` forces `M₀ = I` (`Ideal.IsMaximal.eq_of_le`). Hence `M₀`
is the *unique* maximal ideal, and `IsLocalRing.of_unique_max_ideal` applies.

This file also identifies `IsLocalRing.ResidueField (AdjoinRoot f)` with `l` itself, given the
primitive-element hypothesis `k⟮β₀⟯ = ⊤`
(`HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly`, below `isLocalRing_adjoinRoot_lift_minpoly`)
-- see that theorem's docstring for the composition. That equivalence is landed as a plain
`RingEquiv` (`≃+*`), not an `AlgEquiv` over `k`: upgrading to `≃ₐ[k]` would first need a
`k`-`Algebra` structure on `IsLocalRing.ResidueField (AdjoinRoot f)` (there is no free one -- `k` is
the residue field of `R`, not of `AdjoinRoot f`), which itself needs `IsLocalHom (algebraMap R
(AdjoinRoot f))`, plus a proof that the composed equivalence commutes with `algebraMap k _` on both
sides. This is a materially larger undertaking (a new nontrivial instance, not otherwise needed
anywhere else in this file, plus a compatibility proof) than the rest of this section, so it was not
attempted; the `RingEquiv` suffices for identifying the underlying field and is the natural
stopping point here. -/

theorem HenselianLocalRing.isDomain_adjoinRoot_lift_minpoly {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [HenselianLocalRing R] {l : Type*} [Field l]
    [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀) :
    IsDomain (AdjoinRoot f) :=
  AdjoinRoot.isDomain_of_prime <| UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (HenselianLocalRing.irreducible_lift_minpoly hβ₀ hf hfmap)

/-- `AdjoinRoot f` is a finite free `R`-module (via the `PowerBasis` `AdjoinRoot.powerBasis'`, using
only that `f` is monic -- no irreducibility needed for this part) of rank `f.natDegree`, which,
given that `β₀` is a *primitive element* of `l/k` (`hprim : k⟮β₀⟯ = ⊤`, i.e. `k(β₀) = l`), equals
`[l : k]`: `f.natDegree = (f.map (residue R)).natDegree` (mapping a monic polynomial along a ring
hom into a nontrivial ring preserves `natDegree`) `= (minpoly k β₀).natDegree` (by `hfmap`)
`= finrank k k⟮β₀⟯` (`IntermediateField.adjoin.finrank`) `= finrank k l` (transporting along
`hprim`, `IntermediateField.finrank_top'`). -/
theorem HenselianLocalRing.finrank_adjoinRoot_lift_minpoly {R : Type*} [CommRing R]
    [HenselianLocalRing R] {l : Type*} [Field l] [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀)
    (hprim : IntermediateField.adjoin (IsLocalRing.ResidueField R) {β₀} = ⊤) :
    Module.finrank R (AdjoinRoot f) = Module.finrank (IsLocalRing.ResidueField R) l := by
  rw [(AdjoinRoot.powerBasis' hf).finrank, AdjoinRoot.powerBasis'_dim,
    ← hf.natDegree_map (algebraMap R (IsLocalRing.ResidueField R)), hfmap,
    ← IntermediateField.adjoin.finrank hβ₀, hprim, IntermediateField.finrank_top']

/-- **`M₀ := Ideal.map (AdjoinRoot.of f) (maximalIdeal R)` is maximal** in `AdjoinRoot f`. Extracted
from `isLocalRing_adjoinRoot_lift_minpoly`'s proof (see that theorem's docstring for the argument)
so it can be reused directly by `residueField_equiv_adjoinRoot_lift_minpoly`, which needs exactly
this fact (via `IsLocalRing.eq_maximalIdeal`) to identify `M₀` with `maximalIdeal (AdjoinRoot f)`
once locality is known, without needing `IsDomain R` (this step alone doesn't use it). -/
theorem HenselianLocalRing.isMaximal_map_of_lift_minpoly {R : Type*} [CommRing R]
    [HenselianLocalRing R] {l : Type*} [Field l] [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (_hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀) :
    (Ideal.map (AdjoinRoot.of f) (IsLocalRing.maximalIdeal R)).IsMaximal := by
  have hM0field :
      IsField (AdjoinRoot f ⧸ Ideal.map (AdjoinRoot.of f) (IsLocalRing.maximalIdeal R)) := by
    have e := (AdjoinRoot.quotEquivQuotMap f (IsLocalRing.maximalIdeal R)).toRingEquiv.toMulEquiv
    refine MulEquiv.isField ?_ e
    show IsField (Polynomial (IsLocalRing.ResidueField R) ⧸
      Ideal.span {f.map (algebraMap R (IsLocalRing.ResidueField R))})
    rw [hfmap]
    show IsField (AdjoinRoot (minpoly (IsLocalRing.ResidueField R) β₀))
    haveI : Fact (Irreducible (minpoly (IsLocalRing.ResidueField R) β₀)) :=
      ⟨minpoly.irreducible hβ₀⟩
    exact Field.toIsField _
  exact Ideal.Quotient.maximal_of_isField _ hM0field

/-- **`AdjoinRoot f` is local**, with `M₀ := Ideal.map (AdjoinRoot.of f) (maximalIdeal R)` its
unique maximal ideal. See the section docstring above for the full argument: `M₀` is maximal
because `AdjoinRoot f ⧸ M₀ ≅ AdjoinRoot (minpoly k β₀)` (a field, `minpoly k β₀` being irreducible),
and it is the *only* maximal ideal because every maximal ideal of the module-finite (hence integral)
extension `R'/R` contracts to the unique maximal ideal of the local ring `R`, forcing every maximal
ideal to contain (hence, by maximality of both, equal) `M₀`. -/
theorem HenselianLocalRing.isLocalRing_adjoinRoot_lift_minpoly {R : Type*} [CommRing R] [IsDomain R]
    [HenselianLocalRing R] {l : Type*} [Field l] [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀) :
    IsLocalRing (AdjoinRoot f) := by
  have hM0max : (Ideal.map (AdjoinRoot.of f) (IsLocalRing.maximalIdeal R)).IsMaximal :=
    HenselianLocalRing.isMaximal_map_of_lift_minpoly hβ₀ hf hfmap
  refine IsLocalRing.of_unique_max_ideal
    ⟨Ideal.map (AdjoinRoot.of f) (IsLocalRing.maximalIdeal R), hM0max, fun I hI => ?_⟩
  haveI : Module.Finite R (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  haveI : Algebra.IsIntegral R (AdjoinRoot f) := Algebra.IsIntegral.of_finite R (AdjoinRoot f)
  haveI := hI
  have hcomapmax : (I.comap (algebraMap R (AdjoinRoot f))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal I
  have hcomapeq : I.comap (algebraMap R (AdjoinRoot f)) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal hcomapmax
  have hle : Ideal.map (AdjoinRoot.of f) (IsLocalRing.maximalIdeal R) ≤ I := by
    rw [← AdjoinRoot.algebraMap_eq, ← hcomapeq]
    exact Ideal.map_comap_le
  exact (hM0max.eq_of_le hI.ne_top hle).symm

/-! ### The residue field of `AdjoinRoot f` is `l` itself

The remaining gap flagged in the section docstring above: given the primitive-element hypothesis
`hprim : k⟮β₀⟯ = ⊤` and `IsLocalRing (AdjoinRoot f)` (from `isLocalRing_adjoinRoot_lift_minpoly`),
`IsLocalRing.ResidueField (AdjoinRoot f)` is isomorphic to `l` itself, not merely to some field
abstractly identified with `AdjoinRoot (minpoly k β₀)`. The composition:

1. `IsLocalRing.eq_maximalIdeal` applied to `M₀`'s maximality
   (`isMaximal_map_of_lift_minpoly`) gives `M₀ = IsLocalRing.maximalIdeal (AdjoinRoot f)`;
   `Ideal.quotEquivOfEq` turns this into `AdjoinRoot f ⧸ M₀ ≃+* AdjoinRoot f ⧸ maximalIdeal
   (AdjoinRoot f)`, the latter being *definitionally* `IsLocalRing.ResidueField (AdjoinRoot f)`
   (`IsLocalRing.ResidueField R` unfolds to exactly `R ⧸ maximalIdeal R`).
2. `AdjoinRoot.quotEquivQuotMap f (maximalIdeal R)` identifies `AdjoinRoot f ⧸ M₀` with
   `Polynomial k ⧸ span {f.map (algebraMap R k)}`, which (rewriting along `hfmap`) becomes
   `Polynomial k ⧸ span {minpoly k β₀}`, definitionally `AdjoinRoot (minpoly k β₀)`.
3. `IntermediateField.adjoinRootEquivAdjoin k hβ₀` identifies `AdjoinRoot (minpoly k β₀)` with
   `↥k⟮β₀⟯`; `IntermediateField.equivOfEq hprim` (using `hprim : k⟮β₀⟯ = ⊤`) identifies `↥k⟮β₀⟯` with
   `↥(⊤ : IntermediateField k l)`; `IntermediateField.topEquiv` identifies that with `l`.

Steps 2-3 are all `AlgEquiv`s over `k` (`R` for step 2's raw form, but forgotten to a `RingEquiv`
here to compose with step 1, which is necessarily over `R` since `M₀` lives in `AdjoinRoot f` as an
`R`-algebra, not a `k`-algebra) -- see the docstring above (before `isDomain_adjoinRoot_lift_minpoly`)
for why a single `≃ₐ[k]` is not landed here. -/
def HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly {R : Type*} [CommRing R]
    [HenselianLocalRing R] {l : Type*} [Field l] [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀)
    (hprim : IntermediateField.adjoin (IsLocalRing.ResidueField R) {β₀} = ⊤)
    [IsLocalRing (AdjoinRoot f)] :
    IsLocalRing.ResidueField (AdjoinRoot f) ≃+* l := by
  have hM0max : (Ideal.map (AdjoinRoot.of f) (IsLocalRing.maximalIdeal R)).IsMaximal :=
    HenselianLocalRing.isMaximal_map_of_lift_minpoly hβ₀ hf hfmap
  have hM0eq : Ideal.map (AdjoinRoot.of f) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal (AdjoinRoot f) := IsLocalRing.eq_maximalIdeal hM0max
  refine (Ideal.quotEquivOfEq hM0eq).symm.trans
    ((AdjoinRoot.quotEquivQuotMap f (IsLocalRing.maximalIdeal R)).toRingEquiv.trans ?_)
  show (Polynomial (IsLocalRing.ResidueField R) ⧸
    Ideal.span {f.map (algebraMap R (IsLocalRing.ResidueField R))}) ≃+* l
  rw [hfmap]
  exact (((IntermediateField.adjoinRootEquivAdjoin (IsLocalRing.ResidueField R) hβ₀).trans
    (IntermediateField.equivOfEq hprim)).trans IntermediateField.topEquiv).toRingEquiv

/-! ### Embedding `AdjoinRoot (f.map (algebraMap R K))` into an algebraically closed extension `L`

The remaining ingredient toward
`ValuationSubring.exists_restrictNormalHom_decompositionSubgroup_surjective` (see that theorem's
docstring above): the abstract field `Frac(AdjoinRoot f)` needs to be realized as an actual subfield
of the ambient field `L` the theorem works in. At the intended call site (`Langlands.WeilGroup`),
`L = AlgebraicClosure K` is algebraically closed, so `p := f.map (algebraMap R K)` -- irreducible
over `K = Frac(R)` by `irreducible_map_lift_minpoly`, of positive degree since it agrees with
`f.natDegree = (minpoly k β₀).natDegree > 0` -- has a root `x : L` (`IsAlgClosed.exists_root`).
`AdjoinRoot.lift` then gives a ring hom `AdjoinRoot p →+* L` sending the abstract root to `x`,
automatically injective since its domain `AdjoinRoot p` is a field (`Fact (Irreducible p)` gives
`AdjoinRoot.instField`, and any ring hom out of a division ring into a nontrivial ring is injective,
`RingHom.injective`). This lands the **field-level** embedding of `Frac(AdjoinRoot f) ≅ AdjoinRoot p`
into `L`, with image `K(x)`.

**Scope note**: this is the field-level embedding only. Matching the *ring-of-integers* level
statement -- identifying `AdjoinRoot f` itself (not just its fraction field) with the valuation
subring of `K(x)` sitting under the ambient `A : ValuationSubring L`, and hence transporting the
`finrank`/residue-field facts proved above for `AdjoinRoot f` to that valuation subring directly --
is a further step (needing uniqueness of extension of the valuation from a Henselian base, as
flagged in `exists_restrictNormalHom_decompositionSubgroup_surjective`'s proof sketch) not attempted
here. -/

theorem HenselianLocalRing.exists_ringHom_adjoinRoot_map_of_isAlgClosed {R : Type*} [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] [HenselianLocalRing R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] {l : Type*} [Field l] [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀)
    {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L] :
    ∃ x : L, ∃ φ : AdjoinRoot (f.map (algebraMap R K)) →+* L,
      Function.Injective φ ∧ φ (AdjoinRoot.root _) = x ∧
      φ.comp (AdjoinRoot.of (f.map (algebraMap R K))) = algebraMap K L := by
  set p := f.map (algebraMap R K) with hp
  haveI : Fact (Irreducible p) :=
    ⟨HenselianLocalRing.irreducible_map_lift_minpoly hβ₀ hf hfmap⟩
  have hpmonic : p.Monic := hf.map _
  have hdeg1 : p.natDegree = f.natDegree := hf.natDegree_map _
  have hfdeg : f.natDegree = (minpoly (IsLocalRing.ResidueField R) β₀).natDegree := by
    rw [← hf.natDegree_map (algebraMap R (IsLocalRing.ResidueField R)), hfmap]
  have hpos : 0 < (minpoly (IsLocalRing.ResidueField R) β₀).natDegree := minpoly.natDegree_pos hβ₀
  have hdeg2 : (p.map (algebraMap K L)).natDegree = p.natDegree := hpmonic.natDegree_map _
  have hposL : 0 < (p.map (algebraMap K L)).natDegree := by rw [hdeg2, hdeg1, hfdeg]; exact hpos
  have hdegL : (p.map (algebraMap K L)).degree ≠ 0 :=
    (Polynomial.natDegree_pos_iff_degree_pos.mp hposL).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (p.map (algebraMap K L)) hdegL
  rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hx
  exact ⟨x, AdjoinRoot.lift (algebraMap K L) x hx, RingHom.injective _,
    AdjoinRoot.lift_root hx, AdjoinRoot.lift_comp_of hx⟩

/-! ### The ring hom `AdjoinRoot f →+* AdjoinRoot p` and its injectivity

The first ingredient identified toward matching `AdjoinRoot f` (the "ring of integers" side) with
a valuation subring under the ambient `A` (see the previous section's scope note): base change
`R → K` on the quotient by `(f)`/`(p)` (`p := f.map (algebraMap R K)`) gives a natural ring hom
`AdjoinRoot f →+* AdjoinRoot p`, and this hom is injective whenever `R` is a domain, `f` is monic,
and `K` is (a field containing) the fraction field of `R`: `AdjoinRoot.mk f g ↦ AdjoinRoot.mk p
(g.map (algebraMap R K))`, and `AdjoinRoot.mk f g = 0 ↔ f ∣ g` (`AdjoinRoot.mk_eq_zero`) transfers
along `Polynomial.map_dvd_map` (valid since `algebraMap R K` is injective, `f` monic) to `p ∣
g.map (algebraMap R K) ↔ f ∣ g`. Composed with the embedding `φ : AdjoinRoot p →+* L` of
`exists_ringHom_adjoinRoot_map_of_isAlgClosed`, this gives an injective ring hom `AdjoinRoot f →+*
L`, i.e. realizes `AdjoinRoot f` itself (not just its fraction field) inside `L`. -/

/-- `AdjoinRoot f` evaluates to `0` under the composite `R → K → AdjoinRoot p` at the point
`AdjoinRoot.root p` (`p := f.map (algebraMap R K)`), the side condition `AdjoinRoot.lift` needs to
produce the ring hom `AdjoinRoot f →+* AdjoinRoot p`. Purely a rewrite of `Polynomial.eval₂_map`
against `AdjoinRoot.eval₂_root`. -/
theorem HenselianLocalRing.eval₂_root_map {R : Type*} [CommRing R] {K : Type*} [Field K]
    [Algebra R K] (f : R[X]) :
    Polynomial.eval₂ ((AdjoinRoot.of (f.map (algebraMap R K))).comp (algebraMap R K))
      (AdjoinRoot.root (f.map (algebraMap R K))) f = 0 := by
  rw [← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root _

/-- **Base change on `AdjoinRoot`**: the natural ring hom `AdjoinRoot f →+* AdjoinRoot p` (`p :=
f.map (algebraMap R K)`) sending `AdjoinRoot.root f` to `AdjoinRoot.root p`, induced by
`AdjoinRoot.lift` along the composite `R → K → AdjoinRoot p`. -/
noncomputable def HenselianLocalRing.adjoinRootMap {R : Type*} [CommRing R] {K : Type*} [Field K]
    [Algebra R K] (f : R[X]) : AdjoinRoot f →+* AdjoinRoot (f.map (algebraMap R K)) :=
  AdjoinRoot.lift ((AdjoinRoot.of (f.map (algebraMap R K))).comp (algebraMap R K))
    (AdjoinRoot.root (f.map (algebraMap R K))) (HenselianLocalRing.eval₂_root_map f)

/-- `adjoinRootMap` sends `AdjoinRoot.mk f g` to `AdjoinRoot.mk p (g.map (algebraMap R K))` (`p :=
f.map (algebraMap R K)`): unwind `AdjoinRoot.lift_mk`, then identify the resulting `eval₂` with
`AdjoinRoot.mk p (g.map (algebraMap R K))` via `AdjoinRoot.aeval_eq` and `AdjoinRoot.algebraMap_eq`. -/
theorem HenselianLocalRing.adjoinRootMap_mk {R : Type*} [CommRing R] {K : Type*} [Field K]
    [Algebra R K] (f g : R[X]) :
    HenselianLocalRing.adjoinRootMap (K := K) f (AdjoinRoot.mk f g) =
      AdjoinRoot.mk (f.map (algebraMap R K)) (g.map (algebraMap R K)) := by
  show AdjoinRoot.lift _ _ (HenselianLocalRing.eval₂_root_map f) (AdjoinRoot.mk f g) = _
  rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def,
    AdjoinRoot.aeval_eq]

/-- **`adjoinRootMap` is injective**, for `R` a domain, `f` monic, and `K` a fraction field of `R`:
`AdjoinRoot.mk_eq_zero` reduces `adjoinRootMap f (AdjoinRoot.mk f g) = 0` to `f.map (algebraMap R
K) ∣ g.map (algebraMap R K)`, which `Polynomial.map_dvd_map` (using injectivity of `algebraMap R
K`, `IsFractionRing.injective`, and monicity of `f`) is equivalent to `f ∣ g`, i.e. to
`AdjoinRoot.mk f g = 0`. -/
theorem HenselianLocalRing.injective_adjoinRootMap {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {f : R[X]} (hf : f.Monic) :
    Function.Injective (HenselianLocalRing.adjoinRootMap (K := K) f) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih g =>
    rw [HenselianLocalRing.adjoinRootMap_mk, AdjoinRoot.mk_eq_zero] at hx
    rw [AdjoinRoot.mk_eq_zero]
    exact (Polynomial.map_dvd_map (algebraMap R K) (IsFractionRing.injective R K) hf).mp hx

/-- The composite `AdjoinRoot f →+* AdjoinRoot p →+* L` (via `adjoinRootMap` and the embedding
`φ` of `exists_ringHom_adjoinRoot_map_of_isAlgClosed`) is injective: a composite of injective
maps. This realizes `AdjoinRoot f` itself (not just its fraction field) as a subring of `L`. -/
theorem HenselianLocalRing.injective_comp_adjoinRootMap {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {f : R[X]} (hf : f.Monic)
    {L : Type*} [Field L] {φ : AdjoinRoot (f.map (algebraMap R K)) →+* L}
    (hφ : Function.Injective φ) :
    Function.Injective (φ.comp (HenselianLocalRing.adjoinRootMap (K := K) f)) :=
  hφ.comp (HenselianLocalRing.injective_adjoinRootMap hf)
