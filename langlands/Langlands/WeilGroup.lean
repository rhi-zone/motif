import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.LocalSubring
import Langlands.CyclicGaloisSubfields
import Langlands.FiniteIndexSubgroupsZ
import Langlands.HenselianValuation
import Langlands.ResidueField
import Langlands.UnramifiedExtension
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Algebra.CharP.Reduced

/-!
# The Weil group of a nonarchimedean local field

Let `K` be a nonarchimedean local field, with ring of integers `𝒪[K]` and finite residue field
`𝓀[K]`, let `K̄` be an algebraic closure of `K`, and let `G_K = Gal(K̄/K)` be its absolute Galois
group (`Field.absoluteGaloisGroup`).

Fix a valuation subring `𝒪[K̄]` of `K̄` lying over `𝒪[K]`. Since `K` is complete, and hence
Henselian, the valuation extends uniquely to `K̄`, so every element of `G_K` stabilizes `𝒪[K̄]`:
the decomposition subgroup of `𝒪[K̄]` is all of `G_K` (`decompositionSubgroup_eq_top`). This
gives:

* the residue field `𝓀[K̄] := IsLocalRing.ResidueField 𝒪[K̄]`, an algebraic closure of `𝓀[K]`
  (`residueField_isAlgClosed`, `residueField_isAlgebraic`);
* the residue action `ρ : G_K →* RingAut 𝓀[K̄]` (`residueAction`), which surjects onto
  `Gal(𝓀[K̄]/𝓀[K])` (`surjective_residueAction'`);
* the inertia subgroup `I_K = ker ρ` (`inertiaSubgroup`, `residueAction_ker`),

i.e. the exact sequence `1 → I_K → G_K → Gal(𝓀[K̄]/𝓀[K]) → 1`.

The Galois group of a finite field is isomorphic to `ℤ̂`, the profinite completion of `ℤ`, by an
isomorphism carrying the arithmetic Frobenius `x ↦ x ^ #𝓀[K]` to the image of `1`
(`exists_residueGaloisGroup_equiv_Zhat`). Composing with `ρ` yields `toZhatHom : G_K →* ℤ̂`, again
with kernel `I_K` (`toZhatHom_ker`).

The **Weil group** `W_K` is the preimage under `toZhatHom` of the copy of `ℤ` inside `ℤ̂`, that is,
the range of the injective map `toZhat : ℤ → ℤ̂` (`integerSubgroup`, `toZhat_injective`).
Equivalently, `W_K` is the subgroup of those `σ ∈ G_K` inducing an integer power of Frobenius on
`𝓀[K̄]`, rather than an arbitrary element of the profinite closure `ℤ̂` of `⟨Frob⟩`.

`W_K` carries the topology for which `I_K`, with its profinite topology from `G_K`, is an *open*
subgroup; this is strictly finer than the subspace topology from `G_K`, under which `I_K` is
closed but not open, since `⟨Frob⟩ ≅ ℤ` is dense in `Gal(𝓀[K̄]/𝓀[K]) ≅ ℤ̂`. The topology is built
directly as a `GroupFilterBasis` (`groupFilterBasis`) whose basic neighbourhoods of `1` are the
intersections of `I_K` with open subgroups of `G_K`, so that `I_K` is open by construction and
continuity of multiplication, inversion and conjugation is inherited from `G_K`. The quotient
`W_K ⧸ I_K` is then discrete (`discreteTopology_quotient_inertiaSubgroupOf`).

## Main definitions

* `LocalField.valuationSubringExtension K` : a choice of valuation subring `𝒪[K̄]` of a fixed
  algebraic closure of `K` lying over `𝒪[K]`.
* `LocalField.inertiaSubgroup K` : the inertia subgroup `I_K ≤ G_K`, transported along
  `decompositionSubgroup_eq_top` from `ValuationSubring.inertiaSubgroup`.
* `LocalField.residueAction K` : the homomorphism `G_K →* RingAut 𝓀[K̄]` induced by the action on
  the residue field; `LocalField.residueAction' K` is the same map valued in `Gal(𝓀[K̄]/𝓀[K])`.
* `LocalField.Zhat` : the profinite completion `ℤ̂` of `ℤ`, written multiplicatively, via Mathlib's
  categorical profinite completion of groups.
* `LocalField.frobenius K` : the arithmetic Frobenius `x ↦ x ^ #𝓀[K]` of `𝓀[K̄]`, as an element of
  `RingAut 𝓀[K̄]`; `LocalField.frobeniusAlgEquiv K` is the same automorphism as an element of
  `Gal(𝓀[K̄]/𝓀[K])`.
* `LocalField.canonicalDegreeSubfield K n` : the unique subextension of `𝓀[K̄]/𝓀[K]` of degree `n`
  (`eq_canonicalDegreeSubfield`).
* `LocalField.toZhatHomOfAlgEquiv K` : the isomorphism `Gal(𝓀[K̄]/𝓀[K]) ≃* ℤ̂` assembled from the
  degreewise isomorphisms `levelMulEquiv`.
* `LocalField.toZhatHom K` : the composite `G_K →* ℤ̂`, sending `σ` to the profinite power of
  Frobenius it induces on `𝓀[K̄]`.
* `LocalField.WeilGroup K` : the Weil group `W_K ≤ G_K`, the preimage of `integerSubgroup` under
  `toZhatHom`.
* `LocalField.toArt` : the Artin map `W_K →* ℤ`, with kernel `I_K` (`toArt_ker`).
* `LocalField.groupFilterBasis` : the `GroupFilterBasis` on `W_K` making `I_K` open, with the
  resulting `instTopologicalSpace` and `instIsTopologicalGroup`.

## Main results

* `LocalField.decompositionSubgroup_eq_top` : the decomposition subgroup of `𝒪[K̄]` is all of
  `G_K`, by uniqueness of the extension of the valuation of a complete field.
* `LocalField.compactSpace_absoluteGaloisGroup` : `G_K` is compact, proved through the
  isomorphism `Gal(K̄/K) ≃ₜ Gal(K_sep/K)`, which holds even when `K` is imperfect.
* `LocalField.surjective_residueAction'` : `G_K` surjects onto `Gal(𝓀[K̄]/𝓀[K])`.
* `LocalField.exists_residueGaloisGroup_equiv_Zhat` : the range of `residueAction K` is isomorphic
  to `ℤ̂` by an isomorphism sending Frobenius to the image of `1`.
* `LocalField.isOpen_inertiaSubgroupOf` : `I_K` is open in `W_K`.

## Implementation notes

The isomorphism `Gal(𝓀[K̄]/𝓀[K]) ≃ ℤ̂` is built by hand rather than through Mathlib's
`ProfiniteGrp.ProfiniteCompletion.lift`: `Zhat` lives in universe `0` while `𝓀[K̄]` lives in the
universe of `K`, and the categorical profinite-completion API requires the two to agree. Instead,
`levelMulEquiv` matches `Multiplicative ℤ ⧸ H` against `Gal(canonicalDegreeSubfield K H.index/𝓀[K])`
for each finite-index normal subgroup `H ≤ Multiplicative ℤ`, by sending generator to generator;
`levelMulEquiv_symm_naturality` makes these compatible with the transition maps, and
`toZhatHomOfAlgEquiv` assembles them into a map to the limit, shown bijective by
`toZhatHomOfAlgEquiv_injective` and `toZhatHomOfAlgEquiv_surjective`.

Results not available in Mathlib are supplied by the companion files `Langlands.ResidueField`,
`Langlands.HenselianValuation`, `Langlands.UnramifiedExtension`, `Langlands.CyclicSubgroups`,
`Langlands.CyclicGaloisSubfields` and `Langlands.FiniteIndexSubgroupsZ`.

## TODO

* Upgrade `exists_residueGaloisGroup_equiv_Zhat` from an isomorphism of abstract groups to a
  homeomorphism, matching the Krull topology against the profinite topology on `ℤ̂`.
* Show that `toArt` is continuous, and construct the splitting `W_K ≃ I_K × ℤ` exhibiting
  `W_K ≅ I_K ⋊ ℤ` as topological groups.

## References
* J-P. Serre, *Local Fields*, chapter XII (definition of the Weil group).
* J. Tate, *Number theoretic background*, §1, in *Automorphic forms, representations, and
  L-functions* (Corvallis proceedings).
-/

noncomputable section

open ValuativeRel Valuation IsLocalRing CategoryTheory
open scoped Pointwise Topology

namespace LocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A fixed algebraic closure of `K`. -/
local notation "L" => AlgebraicClosure K

/-! ### The valuation subring of `K̄` lying over `𝒪[K]` -/

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- **Chevalley's extension theorem**: the valuation of `K` extends to `L = AlgebraicClosure K`,
i.e. there is a valuation subring of `L` lying over `𝒪[K] = (valuation K).valuationSubring`.
Proved from `IsLocalRing.exists_factor_valuationRing`, which dominates the inclusion
`𝒪[K] → L` by a valuation subring `A` of `L` along a local homomorphism; locality of that
homomorphism is exactly what forces `A ∩ K = 𝒪[K]` rather than a larger subring.
A choice of such an extension is fixed as `valuationSubringExtension`. -/
theorem exists_valuationSubring_extends :
    ∃ A : ValuationSubring L, A.comap (algebraMap K L) = (valuation K).valuationSubring := by
  set O := (valuation K).valuationSubring with hO
  set f : ↥O →+* L := (algebraMap K L).comp O.subtype with hf
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  haveI : IsLocalHom (f.codRestrict A.toSubring hA) := hloc
  refine ⟨A, ValuationSubring.ext _ _ fun x => ?_⟩
  rw [ValuationSubring.mem_comap]
  constructor
  · intro hx
    by_contra hxO
    -- `x ∉ O`, so `x⁻¹ ∈ O` (and `x⁻¹` is a non-unit in `O`, since otherwise `x ∈ O`).
    have hx0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
    have hxinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
    set b : ↥O := ⟨x⁻¹, hxinv⟩ with hb
    have hfb : f b ∈ A.toSubring := hA b
    have hfb' : f b = (algebraMap K L x)⁻¹ := by
      show (algebraMap K L) x⁻¹ = (algebraMap K L x)⁻¹
      exact map_inv₀ _ _
    -- both `algebraMap K L x` and its inverse lie in `A`, so it (equivalently, `f b`) is a unit.
    have hne : algebraMap K L x ≠ 0 := (map_ne_zero_iff (algebraMap K L) (algebraMap K L).injective).mpr hx0
    have hub : IsUnit (f.codRestrict A.toSubring hA b) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K L x, hx⟩, Subtype.ext ?_⟩
      show f b * algebraMap K L x = 1
      rw [hfb', inv_mul_cancel₀ hne]
    have hbunit : IsUnit b := IsLocalHom.map_nonunit b hub
    -- but then `x = (x⁻¹)⁻¹ ∈ O`, contradicting `hxO`.
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

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A choice of valuation subring of `L = AlgebraicClosure K` lying over `𝒪[K]`, i.e. the ring of
integers `𝒪[K̄]` of the algebraic closure for a fixed extension of the valuation. -/
def valuationSubringExtension : ValuationSubring L :=
  (exists_valuationSubring_extends K).choose

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
@[simp]
theorem valuationSubringExtension_comap :
    (valuationSubringExtension K).comap (algebraMap K L) = (valuation K).valuationSubring :=
  (exists_valuationSubring_extends K).choose_spec

/-! ### The decomposition subgroup is everything -/

/-- The decomposition subgroup of `valuationSubringExtension K`, i.e. its stabilizer in `G_K`, is
all of `G_K`. Since `K` is complete, hence Henselian, the valuation on `K` extends uniquely up to
equivalence to any algebraic extension, so every `K`-automorphism of `K̄` stabilizes
`valuationSubringExtension K`.

The proof goes through the normed-field side, via
`LocalField.valuationSubring_eq_of_comap_eq_of_isNonarchimedeanLocalField`
(`Langlands.HenselianValuation`), which rests on Mathlib's
`spectralNorm_unique_field_norm_ext`: for `K` a complete nonarchimedean normed field and `L/K`
algebraic, any multiplicative norm on `L` extending that of `K` is the spectral norm. It is
applied to `valuationSubringExtension K` and its `σ`-translate, which have the same contraction to
`K` by `ValuationSubring.comap_smul_eq`, since `σ` fixes `K` pointwise. -/
theorem decompositionSubgroup_eq_top :
    ValuationSubring.decompositionSubgroup K (valuationSubringExtension K) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro σ
  rw [MulAction.mem_stabilizer_iff]
  apply LocalField.valuationSubring_eq_of_comap_eq_of_isNonarchimedeanLocalField (K := K)
  · rw [ValuationSubring.comap_smul_eq]
    exact valuationSubringExtension_comap K
  · exact valuationSubringExtension_comap K

/-- The isomorphism between `G_K` and the decomposition subgroup of `𝒪[K̄]`, given by
`decompositionSubgroup_eq_top`. -/
def decompositionEquiv :
    Field.absoluteGaloisGroup K ≃*
      ValuationSubring.decompositionSubgroup K (valuationSubringExtension K) :=
  (Subgroup.topEquiv (G := Field.absoluteGaloisGroup K)).symm.trans
    (MulEquiv.subgroupCongr (decompositionSubgroup_eq_top K).symm)

/-! ### The inertia subgroup -/

/-- The inertia subgroup `I_K ≤ G_K`: the kernel of the action of `G_K` on the residue field of
`valuationSubringExtension K`. It is `ValuationSubring.inertiaSubgroup`, pushed forward along the
inclusion of the decomposition subgroup, which is all of `G_K` by
`decompositionSubgroup_eq_top`. -/
def inertiaSubgroup : Subgroup (Field.absoluteGaloisGroup K) :=
  (ValuationSubring.inertiaSubgroup K (valuationSubringExtension K)).map
    (ValuationSubring.decompositionSubgroup K (valuationSubringExtension K)).subtype

/-! ### The residue field extension and the induced Galois action -/

/-- The inclusion `𝒪[K] ↪ 𝒪[K̄] = valuationSubringExtension K`, the restriction of `algebraMap K L`
to rings of integers. Well-defined by `valuationSubringExtension_comap`. -/
def integersAlgebraMap : ↥(𝒪[K]) →+* valuationSubringExtension K :=
  ((algebraMap K L).comp (𝒪[K]).subtype).codRestrict _ fun x => by
    have hx : (x : K) ∈ (valuation K).valuationSubring :=
      (Valuation.mem_valuationSubring_iff _ _).mpr ((Valuation.mem_integer_iff _ _).mp x.2)
    rw [← valuationSubringExtension_comap K] at hx
    exact (ValuationSubring.mem_comap).mp hx

instance : Algebra ↥(𝒪[K]) (valuationSubringExtension K) := (integersAlgebraMap K).toAlgebra

/-- The inclusion `𝒪[K] ↪ 𝒪[K̄]` is a local homomorphism, i.e. reflects units: a unit of a
valuation subring is a nonzero element whose inverse also lies in the subring, and both conditions
descend along `valuationSubringExtension_comap`. -/
instance : IsLocalHom (algebraMap ↥(𝒪[K]) (valuationSubringExtension K)) := by
  refine ⟨fun a ha => ?_⟩
  set A := valuationSubringExtension K
  have hcoe : ((algebraMap ↥(𝒪[K]) A a : A) : L) = algebraMap K L (a : K) := rfl
  rw [Submonoid.isUnit_iff_and, hcoe] at ha
  obtain ⟨hne0, hinv⟩ := ha
  rw [Submonoid.isUnit_iff_and]
  refine ⟨fun h => hne0 (by rw [h]; simp), ?_⟩
  rw [← map_inv₀] at hinv
  have hmem : (a : K)⁻¹ ∈ (valuation K).valuationSubring := by
    rw [← valuationSubringExtension_comap K]
    exact ValuationSubring.mem_comap.mpr hinv
  exact (Valuation.mem_integer_iff _ _).mpr ((Valuation.mem_valuationSubring_iff _ _).mp hmem)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The algebra structure of `valuationSubringExtension K` over `↥(𝒪[K])` is compatible with the
ambient inclusions `↥(𝒪[K]) → K → L`, `integersAlgebraMap` being the restriction of
`algebraMap K L` to integers. This is the hypothesis of the generic lemmas
`ValuationSubring.decompositionSubgroup_smul_algebraMap_residueField` and
`ValuationSubring.exists_restrictNormalHom_decompositionSubgroup_surjective` of
`Langlands.UnramifiedExtension`, which take it explicitly rather than as an `IsScalarTower`
instance. -/
theorem integersAlgebraMap_compat (a : ↥(𝒪[K])) :
    (algebraMap ↥(𝒪[K]) (valuationSubringExtension K) a : L) = algebraMap K L (a : K) := rfl

/-- The residue field of `valuationSubringExtension K`, an algebraic closure of the finite residue
field `𝓀[K]` by `residueField_isAlgClosed` and `residueField_isAlgebraic`. -/
local notation "kbar" => IsLocalRing.ResidueField (valuationSubringExtension K)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The residue field `kbar` of `valuationSubringExtension K` is algebraically closed, a special
case of `ValuationSubring.residueField_isAlgClosed` (`Langlands.ResidueField`): the residue field
of any valuation subring of an algebraically closed field is algebraically closed. -/
theorem residueField_isAlgClosed : IsAlgClosed kbar :=
  ValuationSubring.residueField_isAlgClosed (valuationSubringExtension K)

/-- The residue field `kbar` of `valuationSubringExtension K` is algebraic over `𝓀[K]`. Every
`x : kbar` is the residue of some `b : valuationSubringExtension K`, which is integral over `𝒪[K]`
by `ValuationSubring.isIntegralElem_of_decompositionSubgroup_eq_top`, and the residue of an
integral element is algebraic over the residue field of the base
(`IsIntegral.isAlgebraic_residue`). -/
theorem residueField_isAlgebraic : Algebra.IsAlgebraic 𝓀[K] kbar := by
  set A := valuationSubringExtension K with hAdef
  refine ⟨fun x => ?_⟩
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := A) x
  -- `b`, viewed inside `L`, is integral over `A.comap (algebraMap K L)`.
  have hbint : RingHom.IsIntegralElem
      ((algebraMap K L).comp (algebraMap (A.comap (algebraMap K L)) K)) (b : L) :=
    ValuationSubring.isIntegralElem_of_decompositionSubgroup_eq_top A
      (decompositionSubgroup_eq_top K) b.2
  rw [valuationSubringExtension_comap K] at hbint
  -- `𝒪[K] → K → L` and `𝒪[K] → A → L` agree definitionally, so `hbint` already has the type
  -- needed to descend along the injective map `A → L`.
  have hAL_inj : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have hbint' : RingHom.IsIntegralElem (algebraMap ↥(𝒪[K]) A) b :=
    RingHom.IsIntegralElem.of_map hAL_inj hbint
  exact IsIntegral.isAlgebraic_residue hbint'

instance : Fact (IsAlgClosed kbar) := ⟨residueField_isAlgClosed K⟩

instance : Algebra.IsAlgebraic 𝓀[K] kbar := residueField_isAlgebraic K

/-- `kbar` is an algebraic closure of `𝓀[K]`, packaging `residueField_isAlgClosed` and
`residueField_isAlgebraic` into the `IsAlgClosure` typeclass, which supplies `Normal 𝓀[K] kbar`
via `IsAlgClosure.normal`. -/
instance : IsAlgClosure 𝓀[K] kbar where
  isAlgClosed := residueField_isAlgClosed K
  isAlgebraic := residueField_isAlgebraic K

/-- `kbar/𝓀[K]` is Galois: normal by `IsAlgClosure.normal` and separable by
`Algebra.IsAlgebraic.isSeparable_of_perfectField`, `𝓀[K]` being finite hence perfect. Unlike
Mathlib's `IsAlgClosure.separable` instance this does not require `CharZero 𝓀[K]`, which is false
here, only perfectness. -/
instance residueField_isGalois : IsGalois 𝓀[K] kbar := ⟨⟩

/-- The action of the decomposition subgroup, hence via `decompositionEquiv` of all of `G_K`, on
`valuationSubringExtension K` induces an action on its residue field `kbar`, giving a homomorphism
`G_K →* RingAut kbar`. Its kernel is `inertiaSubgroup K` (`residueAction_ker`) and its range is
all of `Gal(kbar/𝓀[K])` (`surjective_residueAction'`). -/
def residueAction : Field.absoluteGaloisGroup K →* RingAut kbar :=
  (MulSemiringAction.toRingAut
      (ValuationSubring.decompositionSubgroup K (valuationSubringExtension K)) kbar).comp
    (decompositionEquiv K).toMonoidHom

/-- The kernel of the residue action is the inertia subgroup. This holds for any choice of
valuation subring extension: `residueAction` is `ValuationSubring.inertiaSubgroup` composed with
the bijection `decompositionEquiv`. -/
theorem residueAction_ker : (residueAction K).ker = inertiaSubgroup K := by
  ext x
  simp only [residueAction, inertiaSubgroup, MonoidHom.mem_ker, MonoidHom.coe_comp,
    Function.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨decompositionEquiv K x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    have hyx : decompositionEquiv K x = y := by
      apply Subtype.ext
      rw [← hxy]; rfl
    rwa [hyx]

/-! ### The profinite completion `ℤ̂` and Frobenius -/

/-- The profinite completion `ℤ̂` of `ℤ`, written multiplicatively: the
`ProfiniteGrp.ProfiniteCompletion` of `Multiplicative ℤ`. Its `Group`, `TopologicalSpace`,
`IsTopologicalGroup`, `CompactSpace` and `TotallyDisconnectedSpace` instances come from the
`CoeSort` on `ProfiniteGrp`. -/
abbrev Zhat : Type := ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))

/-- The canonical dense homomorphism `ℤ → ℤ̂` (written multiplicatively). -/
def toZhat : Multiplicative ℤ →* Zhat :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (Multiplicative ℤ))).hom

theorem denseRange_toZhat : DenseRange (toZhat) :=
  ProfiniteGrp.ProfiniteCompletion.denseRange (GrpCat.of (Multiplicative ℤ))

/-- `Multiplicative ℤ` is residually finite: for `g ≠ 1`, i.e. `n := g.toAdd ≠ 0`, reduction modulo
any modulus exceeding `|n|` is a homomorphism to a finite group not killing `g`. This is what makes
`toZhat` injective (`toZhat_injective`). -/
instance : Group.ResiduallyFinite (Multiplicative ℤ) := by
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  set n : ℤ := g.toAdd with hn
  have hn0 : n ≠ 0 := fun h => hg (toAdd_eq_zero.mp h)
  refine ⟨Multiplicative (ZMod (n.natAbs + 1)), inferInstance, inferInstance,
    (Int.castAddHom (ZMod (n.natAbs + 1))).toMultiplicative, fun h => hn0 ?_⟩
  have h' : (n : ZMod (n.natAbs + 1)) = 0 := by
    simpa [AddMonoidHom.toMultiplicative, ← hn, toAdd_eq_zero] using h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
  have h'' : ((n.natAbs + 1 : ℕ) : ℤ) ∣ (n.natAbs : ℤ) := Int.dvd_natAbs.mpr h'
  have hpos : (0 : ℤ) < (n.natAbs : ℤ) := by exact_mod_cast Int.natAbs_pos.mpr hn0
  have hle := Int.le_of_dvd hpos h''
  omega

/-- `toZhat` is injective: `ℤ` really does embed into its profinite completion `ℤ̂`. -/
theorem toZhat_injective : Function.Injective (toZhat) :=
  (ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite
    (GrpCat.of (Multiplicative ℤ))).mpr inferInstance

/-- The subgroup `ℤ ≤ ℤ̂`, the range of `toZhat`. -/
def integerSubgroup : Subgroup Zhat := (toZhat).range

/-- The isomorphism `ℤ ≃* integerSubgroup` coming from injectivity of `toZhat`: the subgroup
`integerSubgroup` is a copy of `ℤ` rather than a proper quotient of it. -/
def integerSubgroupEquiv : Multiplicative ℤ ≃* integerSubgroup :=
  MonoidHom.ofInjective toZhat_injective

instance : Fintype 𝓀[K] := Fintype.ofFinite _

/-- The residue characteristic `p` of `K`, i.e. the characteristic of `𝓀[K]`, and hence, along
`algebraMap 𝓀[K] kbar`, of `kbar`. -/
def residueCharP : ℕ := ringChar 𝓀[K]

instance : CharP 𝓀[K] (residueCharP K) := ringChar.charP _

instance residueCharP_fact : Fact (residueCharP K).Prime :=
  ⟨CharP.char_is_prime 𝓀[K] _⟩

/-- The degree of `𝓀[K]` over its prime field, i.e. the `n` with `#𝓀[K] = p ^ n`
(`card_residueField_eq`). -/
def residueDegree : ℕ+ := (FiniteField.card 𝓀[K] (residueCharP K)).choose

theorem card_residueField_eq :
    Fintype.card 𝓀[K] = (residueCharP K) ^ (residueDegree K : ℕ) :=
  (FiniteField.card 𝓀[K] (residueCharP K)).choose_spec.2

instance : CharP kbar (residueCharP K) :=
  charP_of_injective_algebraMap (algebraMap 𝓀[K] kbar).injective _

instance : ExpChar 𝓀[K] (residueCharP K) := .prime (residueCharP_fact K).out

instance : ExpChar kbar (residueCharP K) := .prime (residueCharP_fact K).out

/-- The arithmetic Frobenius automorphism `x ↦ x ^ #𝓀[K]` of `kbar`, a topological generator of
`Gal(kbar/𝓀[K])` (`denseRange_frobeniusZpowersHom`). That it is an automorphism, and not merely an
endomorphism, uses that `kbar` is algebraically closed, hence perfect, so the Frobenius
endomorphism, injective since `kbar` is a field, is also surjective. -/
def frobenius : RingAut kbar :=
  haveI : PerfectField kbar := @IsAlgClosed.perfectField kbar _ (residueField_isAlgClosed K)
  haveI : PerfectRing kbar (residueCharP K) := PerfectField.toPerfectRing (residueCharP K)
  iterateFrobeniusEquiv kbar (residueCharP K) (residueDegree K : ℕ)

/-- Frobenius fixes `𝓀[K]` pointwise: every `x : 𝓀[K]` satisfies `x ^ #𝓀[K] = x`, by
`FiniteField.pow_card`. -/
theorem frobenius_fixes (x : 𝓀[K]) :
    frobenius K (algebraMap 𝓀[K] kbar x) = algebraMap 𝓀[K] kbar x := by
  haveI : PerfectField kbar := @IsAlgClosed.perfectField kbar _ (residueField_isAlgClosed K)
  haveI : PerfectRing kbar (residueCharP K) := PerfectField.toPerfectRing (residueCharP K)
  show iterateFrobeniusEquiv kbar (residueCharP K) (residueDegree K : ℕ)
      (algebraMap 𝓀[K] kbar x) = algebraMap 𝓀[K] kbar x
  rw [iterateFrobeniusEquiv_def, ← map_pow, ← card_residueField_eq, FiniteField.pow_card]

/-- `frobenius K` as an element of `Gal(kbar/𝓀[K]) = kbar ≃ₐ[𝓀[K]] kbar` rather than of
`RingAut kbar`, using `frobenius_fixes` to see that it commutes with `algebraMap 𝓀[K] kbar`. -/
def frobeniusAlgEquiv : kbar ≃ₐ[𝓀[K]] kbar :=
  AlgEquiv.ofRingEquiv (f := frobenius K) (frobenius_fixes K)

@[simp]
theorem frobeniusAlgEquiv_apply (x : kbar) : frobeniusAlgEquiv K x = frobenius K x := rfl

/-- Every automorphism of a finite extension `M` of `𝓀[K]` is a power of the finite-field Frobenius
`x ↦ x ^ #𝓀[K]`. This is `FiniteField.exists_forall_apply_eq_pow` specialized to `k := 𝓀[K]`, and
is the finite-field ingredient behind cyclicity of the Galois group of each finite subextension of
`kbar/𝓀[K]` (`isCyclic_gal_of_finite_normal`). -/
theorem exists_frobenius_pow_eq {M : Type*} [Field M] [Algebra 𝓀[K] M] [Finite M]
    (g : M ≃ₐ[𝓀[K]] M) : ∃ i : ℕ, ∀ x : M, g x = x ^ (Fintype.card 𝓀[K]) ^ i := by
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (k := 𝓀[K]) (p := residueCharP K)
    (l := M) g
  exact ⟨i, fun x => by simpa [Nat.card_eq_fintype_card] using hi x⟩

/-! ### Surjectivity of the residue action -/

/-- `residueAction`, valued in `Gal(kbar/𝓀[K]) = kbar ≃ₐ[𝓀[K]] kbar` rather than in
`RingAut kbar`. Well-defined because the residue action of `decompositionEquiv K σ` fixes `𝓀[K]`
pointwise, by `ValuationSubring.decompositionSubgroup_smul_algebraMap_residueField`
(`Langlands.UnramifiedExtension`). It is surjective (`surjective_residueAction'`). -/
def residueAction' : Field.absoluteGaloisGroup K →* (kbar ≃ₐ[𝓀[K]] kbar) where
  toFun σ := AlgEquiv.ofRingEquiv (f := residueAction K σ) (fun x => by
    show (decompositionEquiv K σ) • algebraMap 𝓀[K] kbar x = algebraMap 𝓀[K] kbar x
    exact ValuationSubring.decompositionSubgroup_smul_algebraMap_residueField
      (K := K) (valuationSubringExtension K) (integersAlgebraMap_compat K)
      (decompositionEquiv K σ) x)
  map_one' := AlgEquiv.ext fun x => by
    show residueAction K 1 x = x
    simp
  map_mul' a b := AlgEquiv.ext fun x => by
    show residueAction K (a * b) x = residueAction K a (residueAction K b x)
    simp

@[simp]
theorem residueAction'_apply (σ : Field.absoluteGaloisGroup K) (x : kbar) :
    residueAction' K σ x = residueAction K σ x := by
  simp [residueAction', AlgEquiv.ofRingEquiv]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- `Field.absoluteGaloisGroup K = Gal(K̄/K)` is compact for the Krull topology.

Mathlib's `CompactSpace Gal(L/k)` instance requires `[IsGalois k L]`, i.e. separability of `L/k`,
which fails for `K̄/K` when `K` is imperfect of positive characteristic, as `𝔽_q((t))` is. The
proof instead exhibits a homeomorphism `Gal(K_sep/K) ≃ₜ Gal(K̄/K)`, where `K_sep` is the separable
closure: restriction to `K_sep` is surjective by `AlgEquiv.restrictNormalHom_surjective` and
continuous by `InfiniteGalois.restrictNormalHom_continuous`, and it is injective because `K̄/K_sep`
is purely inseparable, so a `K_sep`-algebra endomorphism of `K̄` is unique. Continuity of the
inverse is checked on the Krull neighbourhood basis, lifting a finite-dimensional `M ≤ K̄` to the
separable closure of `K` in `M`. -/
theorem compactSpace_absoluteGaloisGroup : CompactSpace (Field.absoluteGaloisGroup K) := by
  classical
  haveI hNormalL : Normal K L := IsAlgClosure.normal K L
  set Ksep : IntermediateField K L := separableClosure K L with hKsepdef
  haveI : IsGalois K Ksep := by rw [hKsepdef]; exact separableClosure.isGalois K L
  set φ : Field.absoluteGaloisGroup K →* (Ksep ≃ₐ[K] Ksep) :=
    AlgEquiv.restrictNormalHom (F := K) (K₁ := L) Ksep with hφdef
  have hφcont : Continuous φ := InfiniteGalois.restrictNormalHom_continuous Ksep
  have hφsurj : Function.Surjective φ :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := Ksep) (E := L)
  haveI hpi : IsPurelyInseparable Ksep L := by
    rw [hKsepdef]; exact separableClosure.isPurelyInseparable K L
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hfix := (AlgEquiv.restrictNormal_eq_one_iff Ksep σ).1 hσ
    let e : L →ₐ[Ksep] L := ⟨σ.toAlgHom.toRingHom, fun x => hfix x x.2⟩
    have he : e = IsScalarTower.toAlgHom Ksep L L := Subsingleton.elim _ _
    have : (e : L → L) = id := by
      have := AlgHom.ext_iff.1 he
      funext x
      simpa using this x
    exact AlgEquiv.ext fun x => congrFun this x
  have hφbij : Function.Bijective φ := ⟨hφinj, hφsurj⟩
  let ψ : Field.absoluteGaloisGroup K ≃* (Ksep ≃ₐ[K] Ksep) := MulEquiv.ofBijective φ hφbij
  have hψsymm_cont : Continuous ψ.symm := by
    apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
    intro W hW
    rw [map_one] at hW
    -- `Field.absoluteGaloisGroup K` is a `def` and not reducible, so `rw` cannot match it against
    -- `krullTopology_mem_nhds_one_iff`'s `Gal(L/K)`-shaped statement, although the two are defeq
    -- and carry the same topology. Applying the `Iff` directly lets defeq bridge the gap.
    obtain ⟨M, hMfd, hMW⟩ := (krullTopology_mem_nhds_one_iff K L W).mp hW
    haveI : FiniteDimensional K M := hMfd
    -- `N0` = separable closure of `K` in `M`.
    set N0 : IntermediateField K M := separableClosure K M with hN0def
    haveI hpiN0 : IsPurelyInseparable N0 M := by
      rw [hN0def]; exact separableClosure.isPurelyInseparable K M
    -- push `N0` into `Ksep` along the inclusion `M ↪ L`.
    let ι : M →ₐ[K] L := IsScalarTower.toAlgHom K M L
    have hle : N0.map ι ≤ Ksep := separableClosure.map_le_of_algHom ι
    let N' : IntermediateField K Ksep := IntermediateField.restrict hle
    haveI hN0fd : FiniteDimensional K N0 := inferInstance
    haveI hN0mapfd : FiniteDimensional K (N0.map ι) :=
      Module.Finite.equiv (N0.equivMap ι).toLinearEquiv
    haveI hN'fd : FiniteDimensional K N' :=
      Module.Finite.equiv (IntermediateField.restrict_algEquiv hle).toLinearEquiv
    rw [krullTopology_mem_nhds_one_iff]
    refine ⟨N', hN'fd, fun σ hσ => ?_⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
    have hliftM : σ.liftNormal L ∈ M.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hyM
      set ym : M := ⟨y, hyM⟩ with hymdef
      obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem N0 (ringExpChar K) ym
      -- `aKsep : Ksep` is the image of `a` under `M ↪ L`, landing in `N'` by construction.
      have haMap : ι (a : M) ∈ N0.map ι := N0.mem_map.2 ⟨a, a.2, rfl⟩
      set aKsep : Ksep := ⟨ι (a : M), hle haMap⟩ with haKsepdef
      have haKsep : aKsep ∈ N' := (IntermediateField.mem_restrict hle aKsep).2 haMap
      have hfixed : σ aKsep = aKsep := hσ aKsep haKsep
      -- `liftNormal` commutes with `algebraMap Ksep L`.
      have hcomm : σ.liftNormal L (algebraMap Ksep L aKsep) =
          algebraMap Ksep L (σ aKsep) := AlgEquiv.liftNormal_commutes σ L aKsep
      have hcommL : σ.liftNormal L ((a : M) : L) = ((a : M) : L) := by
        have hcoe : algebraMap Ksep L aKsep = ((a : M) : L) := rfl
        rw [hcoe, hfixed, hcoe] at hcomm
        exact hcomm
      -- `(a : M) : L = ym ^ q ^ n = y ^ q ^ n`, so `liftNormal` fixes `y ^ q ^ n`.
      have hpow : ((ym : M) : L) ^ (ringExpChar K) ^ n = ((a : M) : L) := by
        have h1 : (a : M) = ym ^ (ringExpChar K) ^ n := ha
        have h2 : ((a : M) : L) = ((ym ^ (ringExpChar K) ^ n : M) : L) := by rw [h1]
        rw [h2]; push_cast; ring
      have hy : y ^ (ringExpChar K) ^ n = ((a : M) : L) := by
        rw [← hpow]
      have hfixpow : σ.liftNormal L y ^ (ringExpChar K) ^ n = y ^ (ringExpChar K) ^ n := by
        have hstep : σ.liftNormal L (y ^ (ringExpChar K) ^ n) = y ^ (ringExpChar K) ^ n := by
          rw [hy]; exact hcommL
        rwa [map_pow] at hstep
      haveI hExpCharL : ExpChar L (ringExpChar K) :=
        expChar_of_injective_algebraMap (algebraMap K L).injective (ringExpChar K)
      have hinj : Function.Injective
          (iterateFrobenius L (ringExpChar K) n) := iterateFrobenius_inj L (ringExpChar K) n
      have : iterateFrobenius L (ringExpChar K) n (σ.liftNormal L y) =
          iterateFrobenius L (ringExpChar K) n y := by
        simpa [iterateFrobenius_def] using hfixpow
      exact hinj this
    have hkey : ψ.symm σ = σ.liftNormal L := by
      have hφeq : φ (σ.liftNormal L) = σ := σ.restrict_liftNormal L
      conv_lhs => rw [← hφeq]
      exact ψ.symm_apply_apply _
    rw [Set.mem_preimage, hkey]
    exact hMW hliftM
  let e : (Ksep ≃ₐ[K] Ksep) ≃ₜ Field.absoluteGaloisGroup K :=
    { toEquiv := ψ.symm.toEquiv, continuous_toFun := hψsymm_cont, continuous_invFun := hφcont }
  exact e.compactSpace

/-- `residueAction' K` is continuous for the Krull topologies on `G_K` and on `Gal(kbar/𝓀[K])`.

Given `W ∈ 𝓝 1`, `krullTopology_mem_nhds_one_iff` gives a finite-dimensional `M ≤ kbar` over
`𝓀[K]` with `M.fixingSubgroup ⊆ W`. Let `β₀` be a primitive element of `M` and `f` a monic lift of
its minimal polynomial to `𝒪[K]` (`HenselianLocalRing.exists_monic_lift_minpoly`); since
`valuationSubringExtension K` is integrally closed in the algebraically closed `L`,
`ValuationSubring.exists_aeval_root_residue_eq` produces a root `y` of `f` in
`valuationSubringExtension K` with residue `β₀`. Set `N := K⟮(y : L)⟯`, finite-dimensional over
`K`. Any `σ` fixing `N` pointwise fixes `y`, hence fixes `β₀` by equivariance of the residue map
(`IsLocalRing.ResidueField.residue_smul`, applicable since `decompositionSubgroup_eq_top`), hence
fixes all of `M` pointwise (`IntermediateField.algHom_ext_of_eq_adjoin`). So
`N.fixingSubgroup ⊆ (residueAction' K) ⁻¹' W`. -/
theorem continuous_residueAction' : Continuous (residueAction' K) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro W hW
  rw [map_one] at hW
  obtain ⟨M, hMfd, hMW⟩ := (krullTopology_mem_nhds_one_iff 𝓀[K] kbar W).mp hW
  haveI := hMfd
  haveI : PerfectField 𝓀[K] := PerfectField.ofFinite
  haveI : Algebra.IsAlgebraic 𝓀[K] M := Algebra.IsAlgebraic.of_finite 𝓀[K] M
  obtain ⟨β₀, hprim⟩ := Field.exists_primitive_element 𝓀[K] M
  have hβ₀ : IsIntegral 𝓀[K] (β₀ : M) := IsIntegral.of_finite 𝓀[K] (β₀ : M)
  obtain ⟨f, hfmonic, -, hfmap⟩ := HenselianLocalRing.exists_monic_lift_minpoly hβ₀
  set A := valuationSubringExtension K with hAdef
  -- `β₀` (viewed in `kbar`) is a root of `f`'s reduction mod `A`'s maximal ideal.
  have ha₀ : (f.map ((IsLocalRing.residue A).comp (algebraMap ↥(𝒪[K]) A))).IsRoot (M.val β₀) := by
    have hcompres : (IsLocalRing.residue A).comp (algebraMap ↥(𝒪[K]) A) =
        (algebraMap 𝓀[K] kbar).comp (algebraMap ↥(𝒪[K]) 𝓀[K]) :=
      RingHom.ext fun a =>
        (IsLocalRing.ResidueField.algebraMap_residue (R := ↥(𝒪[K])) (S := A) a).symm
    rw [Polynomial.IsRoot.def, hcompres, ← Polynomial.map_map, hfmap, Polynomial.eval_map_algebraMap]
    exact minpoly.aeval_algHom 𝓀[K] M.val β₀
  -- `y : A`, a genuine root of `f` in `A`, with residue exactly `β₀`.
  obtain ⟨y, hyf, hyres⟩ := ValuationSubring.exists_aeval_root_residue_eq A hfmonic ha₀
  have hcomp2 : (algebraMap K L).comp (algebraMap ↥(𝒪[K]) K) =
      (algebraMap A L).comp (algebraMap ↥(𝒪[K]) A) :=
    RingHom.ext fun a => (integersAlgebraMap_compat K a).symm
  have hyK_aeval : Polynomial.aeval (y : L) (f.map (algebraMap ↥(𝒪[K]) K)) = 0 := by
    have hstep := Polynomial.hom_eval₂ f (algebraMap ↥(𝒪[K]) A) (algebraMap A L) (y : A)
    rw [← Polynomial.aeval_def, hyf, map_zero, ← hcomp2, ← Polynomial.eval₂_map,
      ← Polynomial.aeval_def] at hstep
    exact hstep.symm
  have hyKint : IsIntegral K (y : L) := ⟨f.map (algebraMap ↥(𝒪[K]) K), hfmonic.map _, hyK_aeval⟩
  set N : IntermediateField K L := IntermediateField.adjoin K {(y : L)} with hNdef
  haveI hNfd : FiniteDimensional K N := IntermediateField.adjoin.finiteDimensional hyKint
  -- As in `compactSpace_absoluteGaloisGroup`, apply `krullTopology_mem_nhds_one_iff` directly
  -- rather than by `rw`, which cannot see through the non-reducible `Field.absoluteGaloisGroup`.
  apply (krullTopology_mem_nhds_one_iff K L (⇑(residueAction' K) ⁻¹' W)).mpr
  refine ⟨N, hNfd, fun σ hσ => ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
  have hyL : (y : L) ∈ N := by rw [hNdef]; exact IntermediateField.subset_adjoin K _ rfl
  have hσy : σ (y : L) = (y : L) := hσ (y : L) hyL
  -- `σ` (via `decompositionEquiv`, since every `σ` stabilizes `A`) fixes `y` as an element of `A`.
  have hσyA : (decompositionEquiv K σ) • y = y := by
    apply Subtype.ext
    show (σ : L ≃ₐ[K] L) (y : L) = (y : L)
    exact hσy
  -- Hence, by equivariance of the residue map, `σ`'s residue action fixes `β₀`.
  have hresidue := IsLocalRing.ResidueField.residue_smul
    (ValuationSubring.decompositionSubgroup K A) (decompositionEquiv K σ) y
  rw [hσyA, hyres] at hresidue
  have hβfix : residueAction' K σ (M.val β₀) = M.val β₀ := by
    rw [residueAction'_apply]
    show (MulSemiringAction.toRingAut (ValuationSubring.decompositionSubgroup K A) kbar
      (decompositionEquiv K σ)) (M.val β₀) = M.val β₀
    rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply_apply]
    exact hresidue.symm
  -- `β₀` generates `M` over `𝓀[K]`, so fixing `β₀` forces `residueAction' K σ` to fix all of `M`.
  apply hMW
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have heq : (residueAction' K σ).toAlgHom.comp (M.val.comp IntermediateField.topEquiv.toAlgHom) =
      M.val.comp IntermediateField.topEquiv.toAlgHom := by
    apply IntermediateField.algHom_ext_of_eq_adjoin 𝓀[K] hprim.symm
    rintro z hz
    simp only [Set.mem_singleton_iff] at hz
    simp only [AlgHom.comp_apply]
    exact hz ▸ hβfix
  have hcongr := DFunLike.congr_fun heq (IntermediateField.topEquiv.symm (⟨x, hx⟩ : M))
  simpa using hcongr

/-- The range of `residueAction' K` as a closed subgroup of `Gal(kbar/𝓀[K])`: it is the continuous
(`continuous_residueAction'`) image of the compact group `G_K`
(`compactSpace_absoluteGaloisGroup`), hence compact, hence closed, `Gal(kbar/𝓀[K])` being Hausdorff
by `krullTopology_t2`. -/
def residueAction'ClosedRange : ClosedSubgroup (kbar ≃ₐ[𝓀[K]] kbar) where
  toSubgroup := (residueAction' K).range
  isClosed' := by
    haveI := compactSpace_absoluteGaloisGroup K
    haveI : T2Space (kbar ≃ₐ[𝓀[K]] kbar) := krullTopology_t2
    have hcompact : IsCompact (Set.range (residueAction' K)) :=
      isCompact_range (continuous_residueAction' K)
    rw [show (residueAction' K).range.carrier = Set.range (residueAction' K) from
      MonoidHom.coe_range (residueAction' K)]
    exact hcompact.isClosed

/-- For every finite Galois subextension `M` of `kbar/𝓀[K]`, every automorphism of `M/𝓀[K]` is the
restriction of `residueAction' K σ` for some `σ ∈ G_K`. Transported from
`ValuationSubring.exists_restrictNormalHom_decompositionSubgroup_surjective`
(`Langlands.UnramifiedExtension`) along `decompositionEquiv K`. -/
theorem surjective_restrictNormalHom_comp_residueAction'
    (M : IntermediateField 𝓀[K] kbar) [FiniteDimensional 𝓀[K] M] [Normal 𝓀[K] M] :
    Function.Surjective fun σ : Field.absoluteGaloisGroup K =>
      AlgEquiv.restrictNormalHom (F := 𝓀[K]) M (residueAction' K σ) := by
  intro g
  obtain ⟨τ, hτ⟩ :=
    ValuationSubring.exists_restrictNormalHom_decompositionSubgroup_surjective
      (K := K) (valuationSubringExtension K) (valuationSubringExtension_comap K)
      (integersAlgebraMap_compat K) M g
  refine ⟨(decompositionEquiv K).symm τ, ?_⟩
  rw [← hτ]
  congr 1

/-- `residueAction' K` is surjective. Surjectivity onto every finite Galois quotient
(`surjective_restrictNormalHom_comp_residueAction'`) and the Galois correspondence
(`InfiniteGalois.restrict_fixedField`) show that the fixed field of the range is `⊥`; the range
being closed (`residueAction'ClosedRange`), `InfiniteGalois.fixingSubgroup_fixedField` then
identifies it with the fixing subgroup of `⊥`, which is everything. -/
theorem surjective_residueAction' : Function.Surjective (residueAction' K) := by
  have hfixed : IntermediateField.fixedField (residueAction'ClosedRange K).toSubgroup = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    -- `x` lies in some finite Galois subextension `M` of `kbar/𝓀[K]`.
    obtain ⟨M, hMfd, hMnormal, hxM⟩ :
        ∃ M : IntermediateField 𝓀[K] kbar, FiniteDimensional 𝓀[K] M ∧ Normal 𝓀[K] M ∧ x ∈ M := by
      classical
      haveI := residueField_isGalois K
      let L' := FiniteGaloisIntermediateField.adjoin 𝓀[K] ({x} : Set kbar)
      exact ⟨L'.toIntermediateField, L'.finiteDimensional, L'.isGalois.to_normal,
        FiniteGaloisIntermediateField.subset_adjoin 𝓀[K] ({x} : Set kbar) rfl⟩
    haveI := hMfd; haveI := hMnormal
    haveI : IsGalois 𝓀[K] M := ⟨⟩
    have hsurj : (residueAction'ClosedRange K).toSubgroup.map (AlgEquiv.restrictNormalHom M) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      obtain ⟨σ, hσ⟩ := surjective_restrictNormalHom_comp_residueAction' K M g
      exact ⟨residueAction' K σ, ⟨σ, rfl⟩, hσ⟩
    have hM : IntermediateField.fixedField (residueAction'ClosedRange K).toSubgroup ⊓ M =
        IntermediateField.lift (IntermediateField.fixedField
          ((residueAction'ClosedRange K).toSubgroup.map (AlgEquiv.restrictNormalHom M))) :=
      InfiniteGalois.restrict_fixedField _ M
    rw [hsurj, InfiniteGalois.fixedField_bot] at hM
    simp only [IntermediateField.lift_bot] at hM
    have hxM' : x ∈ IntermediateField.fixedField (residueAction'ClosedRange K).toSubgroup ⊓ M :=
      ⟨hx, hxM⟩
    rw [hM] at hxM'
    exact hxM'
  have hclosed :
      (residueAction'ClosedRange K).toSubgroup = ⊤ :=
    (InfiniteGalois.fixingSubgroup_fixedField (residueAction'ClosedRange K)).symm.trans
      (by rw [hfixed]; exact IntermediateField.fixingSubgroup_bot)
  intro g
  have : g ∈ (⊤ : Subgroup (kbar ≃ₐ[𝓀[K]] kbar)) := Subgroup.mem_top g
  rw [← hclosed] at this
  exact this

/-! ### Frobenius lies in the range of `residueAction` -/

/-- Frobenius lies in the range of `residueAction`, i.e. is induced by some `σ ∈ G_K`. A direct
consequence of `surjective_residueAction'`, whose content is the local-field-theoretic fact that
every automorphism of `kbar/𝓀[K]` lifts to an automorphism of `K̄/K` stabilizing
`valuationSubringExtension K`. -/
theorem frobenius_mem_residueAction_range : frobenius K ∈ (residueAction K).range := by
  obtain ⟨σ, hσ⟩ := surjective_residueAction' K (frobeniusAlgEquiv K)
  refine ⟨σ, RingEquiv.ext fun x => ?_⟩
  have := AlgEquiv.ext_iff.mp hσ x
  simpa [residueAction'_apply] using this

/-! ### The subextensions of `kbar/𝓀[K]` and the map to `ℤ̂` -/

/-- `frobenius K` raises every element of `kbar`, not only those fixed by `𝓀[K]`, to the
`#𝓀[K]`-th power. This unfolds `iterateFrobeniusEquiv_def`, identifying
`(residueCharP K) ^ (residueDegree K : ℕ)` with `Fintype.card 𝓀[K]` by `card_residueField_eq`. -/
theorem frobenius_apply (x : kbar) : frobenius K x = x ^ Fintype.card 𝓀[K] := by
  haveI : PerfectField kbar := @IsAlgClosed.perfectField kbar _ (residueField_isAlgClosed K)
  haveI : PerfectRing kbar (residueCharP K) := PerfectField.toPerfectRing (residueCharP K)
  show iterateFrobeniusEquiv kbar (residueCharP K) (residueDegree K : ℕ) x = x ^ Fintype.card 𝓀[K]
  rw [iterateFrobeniusEquiv_def, card_residueField_eq]

/-- The restriction of Frobenius to a normal subextension `M ≤ kbar` of `𝓀[K]` is the finite-field
Frobenius `x ↦ x ^ #𝓀[K]` on `M`, by descending `frobenius_apply` along the inclusion
`M ↪ kbar`. -/
theorem restrictNormalHom_frobenius_apply (M : IntermediateField 𝓀[K] kbar) [Normal 𝓀[K] M]
    (x : M) :
    AlgEquiv.restrictNormalHom M (frobeniusAlgEquiv K) x = x ^ Fintype.card 𝓀[K] := by
  have h := AlgEquiv.restrictNormalHom_apply M (frobeniusAlgEquiv K) x
  rw [frobeniusAlgEquiv_apply, frobenius_apply] at h
  exact_mod_cast h

/-- The restriction of `frobenius ^ i` to a normal subextension `M ≤ kbar` of `𝓀[K]` is
`x ↦ x ^ (#𝓀[K]) ^ i`, by induction on `i` from `restrictNormalHom_frobenius_apply`. -/
theorem restrictNormalHom_frobenius_pow_apply (M : IntermediateField 𝓀[K] kbar) [Normal 𝓀[K] M]
    (i : ℕ) (x : M) :
    AlgEquiv.restrictNormalHom M (frobeniusAlgEquiv K ^ i) x =
      x ^ (Fintype.card 𝓀[K]) ^ i := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, map_mul, AlgEquiv.mul_apply, restrictNormalHom_frobenius_apply, ih, ← pow_mul,
      ← pow_succ']

/-- Every finite Galois subextension `M` of `kbar/𝓀[K]` has cyclic Galois group, generated by the
restriction of Frobenius. Given `h : Gal(M/𝓀[K])`, `exists_frobenius_pow_eq` produces `i` with `h`
and the `i`-th power of the restricted Frobenius agreeing pointwise on `M`
(`restrictNormalHom_frobenius_pow_apply`), hence equal. -/
instance isCyclic_gal_of_finite_normal (M : IntermediateField 𝓀[K] kbar)
    [FiniteDimensional 𝓀[K] M] [Normal 𝓀[K] M] : IsCyclic (M ≃ₐ[𝓀[K]] M) := by
  haveI : Finite M := Module.finite_of_finite 𝓀[K]
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨AlgEquiv.restrictNormalHom M (frobeniusAlgEquiv K),
    (Subgroup.eq_top_iff' _).mpr fun h => ?_⟩
  obtain ⟨i, hi⟩ := exists_frobenius_pow_eq K h
  refine ⟨(i : ℤ), ?_⟩
  show AlgEquiv.restrictNormalHom M (frobeniusAlgEquiv K) ^ (i : ℤ) = h
  rw [zpow_natCast, ← map_pow]
  apply AlgEquiv.ext
  intro x
  rw [restrictNormalHom_frobenius_pow_apply]
  exact (hi x).symm

/-- The homomorphism `Multiplicative ℤ →* Gal(kbar/𝓀[K])`, `n ↦ (frobeniusAlgEquiv K) ^ n`. Its
range is dense (`denseRange_frobeniusZpowersHom`). -/
def frobeniusZpowersHom : Multiplicative ℤ →* (kbar ≃ₐ[𝓀[K]] kbar) :=
  zpowersHom _ (frobeniusAlgEquiv K)

@[simp]
theorem frobeniusZpowersHom_apply (n : Multiplicative ℤ) :
    frobeniusZpowersHom K n = frobeniusAlgEquiv K ^ n.toAdd := rfl

/-- Frobenius topologically generates `Gal(kbar/𝓀[K])`: the subgroup it generates is dense.

Given `g` and a neighbourhood `t` of `g`, translating to a neighbourhood of `1`
(`map_mul_left_nhds_one`) produces a finite Galois `M` with `M.fixingSubgroup` inside it
(`InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois`); `exists_frobenius_pow_eq` matches
`g`'s restriction to `M` against a power of the restricted Frobenius
(`restrictNormalHom_frobenius_pow_apply`), and that power of `frobeniusAlgEquiv K` then lies in
`t`. -/
theorem denseRange_frobeniusZpowersHom : Dense (Set.range (frobeniusZpowersHom K)) := by
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_forall fun g => mem_closure_iff_nhds.mpr fun t ht => ?_
  have hW : (g * ·) ⁻¹' t ∈ 𝓝 (1 : kbar ≃ₐ[𝓀[K]] kbar) := by
    rw [← Filter.mem_map, map_mul_left_nhds_one]; exact ht
  obtain ⟨M, hM⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
    ((g * ·) ⁻¹' t)).mp hW
  haveI : Normal 𝓀[K] M.toIntermediateField := M.isGalois.to_normal
  haveI : Finite M.toIntermediateField := Module.finite_of_finite 𝓀[K]
  obtain ⟨i, hi⟩ := exists_frobenius_pow_eq K
    (AlgEquiv.restrictNormalHom M.toIntermediateField g)
  have hker : AlgEquiv.restrictNormalHom M.toIntermediateField
      (g⁻¹ * frobeniusAlgEquiv K ^ i) = 1 := by
    rw [map_mul, _root_.map_inv, inv_mul_eq_one]
    exact AlgEquiv.ext fun x =>
      (hi x).trans (restrictNormalHom_frobenius_pow_apply K M.toIntermediateField i x).symm
  have hmem : g⁻¹ * frobeniusAlgEquiv K ^ i ∈ M.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]; exact hker
  have hmem_t : frobeniusAlgEquiv K ^ i ∈ t := by
    have := hM hmem
    simpa using this
  exact ⟨frobeniusAlgEquiv K ^ i, hmem_t,
    ⟨Multiplicative.ofAdd (i : ℤ), by simp⟩⟩

/-- For every `n ≥ 1` there is a subextension of `kbar/𝓀[K]` of degree `n`: embed
`FiniteField.Extension 𝓀[K] (residueCharP K) n`, an extension of `𝓀[K]` of degree exactly `n` by
`FiniteField.finrank_extension`, into the algebraically closed `kbar` via `IsAlgClosed.lift` and
take its field range. Uniqueness is `eq_of_finrank_eq`, and `canonicalDegreeSubfield` names a
choice with its `FiniteDimensional` and `Normal` instances. -/
theorem exists_intermediateField_finrank_eq (n : ℕ) [NeZero n] :
    ∃ M : IntermediateField 𝓀[K] kbar, Module.finrank 𝓀[K] M = n := by
  haveI := residueField_isAlgClosed K
  let f : FiniteField.Extension 𝓀[K] (residueCharP K) n →ₐ[𝓀[K]] kbar := IsAlgClosed.lift
  refine ⟨f.fieldRange, ?_⟩
  rw [← LinearEquiv.finrank_eq f.equivFieldRange.toLinearEquiv]
  exact FiniteField.finrank_extension 𝓀[K] (residueCharP K) n

/-- Any two finite Galois subextensions of `kbar/𝓀[K]` of the same degree coincide.

They are compared inside their sup `S := M₁ ⊔ M₂`, which is finite-dimensional and normal over
`𝓀[K]` (`IntermediateField.finiteDimensional_sup`, `IntermediateField.normal_sup`), hence Galois
with cyclic Galois group (`isCyclic_gal_of_finite_normal`). Contracting `M₁` and `M₂` into `S`
along `IntermediateField.comap S.val` preserves degrees
(`IntermediateField.finrank_comap_val_of_le`), so the two contractions agree by
`IsGalois.existsUnique_intermediateField_finrank_eq`, and
`IntermediateField.map_comap_eq_self` recovers `M₁ = M₂`. -/
theorem eq_of_finrank_eq (M1 M2 : IntermediateField 𝓀[K] kbar)
    [FiniteDimensional 𝓀[K] M1] [Normal 𝓀[K] M1] [FiniteDimensional 𝓀[K] M2] [Normal 𝓀[K] M2]
    (h : Module.finrank 𝓀[K] M1 = Module.finrank 𝓀[K] M2) : M1 = M2 := by
  set n := Module.finrank 𝓀[K] M1 with hn
  set S := M1 ⊔ M2 with hS
  haveI : FiniteDimensional 𝓀[K] S := IntermediateField.finiteDimensional_sup M1 M2
  haveI : Normal 𝓀[K] S := IntermediateField.normal_sup 𝓀[K] kbar M1 M2
  haveI : IsGalois 𝓀[K] S := ⟨⟩
  have hM1L : M1 ≤ S := le_sup_left
  have hM2L : M2 ≤ S := le_sup_right
  set N1 := IntermediateField.comap S.val M1 with hN1
  set N2 := IntermediateField.comap S.val M2 with hN2
  have hN1card : Module.finrank 𝓀[K] N1 = n :=
    IntermediateField.finrank_comap_val_of_le hM1L
  have hN2card : Module.finrank 𝓀[K] N2 = n := by
    rw [hN2, IntermediateField.finrank_comap_val_of_le hM2L]
    exact h.symm
  have hdvd : n ∣ Module.finrank 𝓀[K] S := by
    rw [← hN1card]
    exact ⟨Module.finrank N1 S, (Module.finrank_mul_finrank 𝓀[K] N1 S).symm⟩
  obtain ⟨N, -, hNuniq⟩ := IsGalois.existsUnique_intermediateField_finrank_eq hdvd
  have hN1eq : N1 = N := hNuniq N1 hN1card
  have hN2eq : N2 = N := hNuniq N2 hN2card
  have hNeq : N1 = N2 := hN1eq.trans hN2eq.symm
  have hmap1 : IntermediateField.map S.val N1 = M1 :=
    IntermediateField.map_comap_eq_self (by rw [IntermediateField.fieldRange_val]; exact hM1L)
  have hmap2 : IntermediateField.map S.val N2 = M2 :=
    IntermediateField.map_comap_eq_self (by rw [IntermediateField.fieldRange_val]; exact hM2L)
  rw [← hmap1, ← hmap2, hNeq]

/-- The embedding `FiniteField.Extension 𝓀[K] (residueCharP K) n →ₐ[𝓀[K]] kbar` underlying
`exists_intermediateField_finrank_eq`, named so that the `FiniteDimensional` and `Normal`
properties of its source can be transported to its field range along
`AlgHom.equivFieldRange`. -/
noncomputable def frobeniusExtensionAlgHom (n : ℕ) [NeZero n] :
    FiniteField.Extension 𝓀[K] (residueCharP K) n →ₐ[𝓀[K]] kbar :=
  haveI := residueField_isAlgClosed K
  IsAlgClosed.lift

/-- The degree-`n` subextension of `kbar/𝓀[K]`, for `n ≥ 1`: the field range of
`frobeniusExtensionAlgHom`. It carries `FiniteDimensional`, `Normal` and `IsGalois` instances
inherited from `FiniteField.Extension 𝓀[K] (residueCharP K) n` along `AlgHom.equivFieldRange`, and
is the unique subextension of its degree (`eq_canonicalDegreeSubfield`). -/
noncomputable def canonicalDegreeSubfield (n : ℕ) [NeZero n] : IntermediateField 𝓀[K] kbar :=
  (frobeniusExtensionAlgHom K n).fieldRange

instance canonicalDegreeSubfield.instFiniteDimensional (n : ℕ) [NeZero n] :
    FiniteDimensional 𝓀[K] (canonicalDegreeSubfield K n) :=
  Module.Finite.equiv (frobeniusExtensionAlgHom K n).equivFieldRange.toLinearEquiv

instance canonicalDegreeSubfield.instNormal (n : ℕ) [NeZero n] :
    Normal 𝓀[K] (canonicalDegreeSubfield K n) :=
  Normal.of_algEquiv (frobeniusExtensionAlgHom K n).equivFieldRange

instance canonicalDegreeSubfield.instIsGalois (n : ℕ) [NeZero n] :
    IsGalois 𝓀[K] (canonicalDegreeSubfield K n) := ⟨⟩

theorem finrank_canonicalDegreeSubfield (n : ℕ) [NeZero n] :
    Module.finrank 𝓀[K] (canonicalDegreeSubfield K n) = n := by
  show Module.finrank 𝓀[K] (frobeniusExtensionAlgHom K n).fieldRange = n
  rw [← LinearEquiv.finrank_eq (frobeniusExtensionAlgHom K n).equivFieldRange.toLinearEquiv]
  exact FiniteField.finrank_extension 𝓀[K] (residueCharP K) n

/-- Any finite Galois subextension of `kbar/𝓀[K]` of degree `n` equals `canonicalDegreeSubfield K
n`, by `eq_of_finrank_eq` and `finrank_canonicalDegreeSubfield`. -/
theorem eq_canonicalDegreeSubfield (M : IntermediateField 𝓀[K] kbar)
    [FiniteDimensional 𝓀[K] M] [Normal 𝓀[K] M] {n : ℕ} [NeZero n]
    (hM : Module.finrank 𝓀[K] M = n) : M = canonicalDegreeSubfield K n :=
  eq_of_finrank_eq K M (canonicalDegreeSubfield K n) (hM.trans (finrank_canonicalDegreeSubfield K n).symm)

/-- The restriction of Frobenius generates the Galois group of a finite Galois subextension `M` of
`kbar/𝓀[K]`. This is the content of `isCyclic_gal_of_finite_normal` in the membership form
required by `mulEquivOfGenerators`. -/
theorem zpowers_restrictNormalHom_frobeniusAlgEquiv_eq_top (M : IntermediateField 𝓀[K] kbar)
    [FiniteDimensional 𝓀[K] M] [Normal 𝓀[K] M] (h : M ≃ₐ[𝓀[K]] M) :
    h ∈ Subgroup.zpowers (AlgEquiv.restrictNormalHom M (frobeniusAlgEquiv K)) := by
  haveI : Finite M := Module.finite_of_finite 𝓀[K]
  obtain ⟨i, hi⟩ := exists_frobenius_pow_eq K h
  refine ⟨(i : ℤ), ?_⟩
  show AlgEquiv.restrictNormalHom M (frobeniusAlgEquiv K) ^ (i : ℤ) = h
  rw [zpow_natCast, ← map_pow]
  apply AlgEquiv.ext
  intro x
  rw [restrictNormalHom_frobenius_pow_apply]
  exact (hi x).symm

/-- The quotient of `Multiplicative ℤ` by a normal subgroup `H` of finite index `n` is isomorphic
to `Gal(canonicalDegreeSubfield K n/𝓀[K])`, matching the image of `Multiplicative.ofAdd 1` with the
restriction of Frobenius. Both groups are cyclic of order `n`, so this is `mulEquivOfGenerators`
(`Langlands.CyclicSubgroups`). -/
noncomputable def levelMulEquiv (H : FiniteIndexNormalSubgroup (Multiplicative ℤ)) :
    haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
    Multiplicative ℤ ⧸ H.toSubgroup ≃*
      (canonicalDegreeSubfield K H.toSubgroup.index ≃ₐ[𝓀[K]] canonicalDegreeSubfield K H.toSubgroup.index) :=
  haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  mulEquivOfGenerators
    (g := QuotientGroup.mk' H.toSubgroup (Multiplicative.ofAdd (1 : ℤ)))
    (g' := AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index) (frobeniusAlgEquiv K))
    (zpowers_quotientGroupMk'_eq_top_of_zpowers_eq_top
      (fun x : Multiplicative ℤ => ⟨x.toAdd, by simp [← ofAdd_zsmul]⟩) H.toSubgroup)
    (zpowers_restrictNormalHom_frobeniusAlgEquiv_eq_top K _)
    (by
      rw [← Subgroup.index_eq_card, IsGalois.card_aut_eq_finrank, finrank_canonicalDegreeSubfield])

/-- For `m ∣ n`, `canonicalDegreeSubfield K m ≤ canonicalDegreeSubfield K n`.

`IsGalois.existsUnique_intermediateField_finrank_eq` applied inside `canonicalDegreeSubfield K n`
gives a degree-`m` subfield `N`, normal over `𝓀[K]` by `IsGalois.normal_of_isMulCommutative`
(`Langlands.CyclicGaloisSubfields`) since the Galois group is cyclic, hence abelian. Its image in
`kbar` under `IntermediateField.map` is a normal subextension of degree `m`, so equals
`canonicalDegreeSubfield K m` by `eq_canonicalDegreeSubfield`. -/
theorem canonicalDegreeSubfield_le_of_dvd {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) :
    canonicalDegreeSubfield K m ≤ canonicalDegreeSubfield K n := by
  set E := canonicalDegreeSubfield K n with hE
  haveI : IsCyclic Gal(E/𝓀[K]) := isCyclic_gal_of_finite_normal K E
  haveI : IsMulCommutative Gal(E/𝓀[K]) := IsCyclic.isMulCommutative
  have hmn : m ∣ Module.finrank 𝓀[K] E := by
    rw [finrank_canonicalDegreeSubfield]; exact h
  obtain ⟨N, hNcard, -⟩ := IsGalois.existsUnique_intermediateField_finrank_eq hmn
  haveI hNnormal : Normal 𝓀[K] N := IsGalois.normal_of_isMulCommutative N
  set M' := IntermediateField.map E.val N with hM'
  have hequiv : N ≃ₐ[𝓀[K]] M' := N.equivMap E.val
  haveI hM'fd : FiniteDimensional 𝓀[K] M' := Module.Finite.equiv hequiv.toLinearEquiv
  haveI hM'normal : Normal 𝓀[K] M' := Normal.of_algEquiv hequiv
  have hM'card : Module.finrank 𝓀[K] M' = m := by
    rw [← LinearEquiv.finrank_eq hequiv.toLinearEquiv]; exact hNcard
  have hM'eq : M' = canonicalDegreeSubfield K m := eq_canonicalDegreeSubfield K M' hM'card
  rw [← hM'eq, hM']
  intro x hx
  obtain ⟨y, -, rfl⟩ := N.mem_map.mp hx
  exact y.2

/-- Every element of `kbar` lies in some `canonicalDegreeSubfield K n`: adjoin `x` to `𝓀[K]` inside
a `FiniteGaloisIntermediateField` and identify the result with `canonicalDegreeSubfield K d`, `d`
its degree over `𝓀[K]`, by `eq_canonicalDegreeSubfield`. -/
theorem exists_mem_canonicalDegreeSubfield (x : kbar) :
    ∃ n : ℕ, ∃ _ : NeZero n, x ∈ canonicalDegreeSubfield K n := by
  classical
  haveI := residueField_isGalois K
  let L' := FiniteGaloisIntermediateField.adjoin 𝓀[K] ({x} : Set kbar)
  haveI := L'.finiteDimensional
  haveI := L'.isGalois.to_normal
  haveI : NeZero (Module.finrank 𝓀[K] L'.toIntermediateField) := ⟨Module.finrank_pos.ne'⟩
  have hxL : x ∈ L'.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin 𝓀[K] ({x} : Set kbar) rfl
  have hLeq : L'.toIntermediateField =
      canonicalDegreeSubfield K (Module.finrank 𝓀[K] L'.toIntermediateField) :=
    eq_canonicalDegreeSubfield K L'.toIntermediateField rfl
  exact ⟨_, inferInstance, hLeq ▸ hxL⟩

/-- An automorphism of `kbar/𝓀[K]` restricting to the identity on every `canonicalDegreeSubfield K
n` is the identity, since every `x : kbar` lies in one of them
(`exists_mem_canonicalDegreeSubfield`). -/
theorem eq_one_of_forall_restrictNormalHom_canonicalDegreeSubfield_eq_one
    (g : kbar ≃ₐ[𝓀[K]] kbar)
    (hg : ∀ (n : ℕ) [NeZero n], AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K n) g = 1) :
    g = 1 := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨n, hn, hxn⟩ := exists_mem_canonicalDegreeSubfield K x
  haveI := hn
  have hgn : AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K n) g = 1 := hg n
  have := AlgEquiv.restrictNormalHom_apply (canonicalDegreeSubfield K n) g ⟨x, hxn⟩
  rw [hgn] at this
  simpa using this.symm

/-- Two automorphisms of `kbar/𝓀[K]` agreeing after restriction to `M` also agree after restriction
to any `M' ≤ M`. Agreement on `M` is pointwise agreement on `M`
(`AlgEquiv.restrictNormalHom_apply`), hence on the subset `M'`; comparing both restrictions against
`kbar` directly avoids composing `AlgEquiv.restrictNormalHom` across a nested scalar tower. -/
theorem restrictNormalHom_eq_of_restrictNormalHom_eq {M M' : IntermediateField 𝓀[K] kbar}
    [FiniteDimensional 𝓀[K] M] [Normal 𝓀[K] M] [FiniteDimensional 𝓀[K] M'] [Normal 𝓀[K] M']
    (hle : M' ≤ M) {g g' : kbar ≃ₐ[𝓀[K]] kbar}
    (heq : AlgEquiv.restrictNormalHom M g = AlgEquiv.restrictNormalHom M g') :
    AlgEquiv.restrictNormalHom M' g = AlgEquiv.restrictNormalHom M' g' := by
  apply AlgEquiv.ext
  intro x
  have hx : (x : kbar) ∈ M := hle x.2
  apply Subtype.ext
  have h1 := AlgEquiv.restrictNormalHom_apply M' g x
  have h2 := AlgEquiv.restrictNormalHom_apply M' g' x
  have h3 := AlgEquiv.restrictNormalHom_apply M g ⟨x, hx⟩
  have h4 := AlgEquiv.restrictNormalHom_apply M g' ⟨x, hx⟩
  rw [h1, h2]
  have : g (x : kbar) = g' (x : kbar) := by
    rw [← h3, ← h4, heq]
  exact this

/-- `levelMulEquiv` is natural in `H`. For `H ≤ H'`, of indices `n` and `n'` with `n' ∣ n`
(`FiniteIndexNormalSubgroup.index_dvd_index_of_le`), the transition map `QuotientGroup.map` on the
`ℤ` side corresponds under `levelMulEquiv` to restriction along
`canonicalDegreeSubfield K n' ≤ canonicalDegreeSubfield K n`.

Writing the restriction of `g` to `canonicalDegreeSubfield K n` as a power `Frob ^ k`
(`zpowers_restrictNormalHom_frobeniusAlgEquiv_eq_top`),
`restrictNormalHom_eq_of_restrictNormalHom_eq` transports the identity down to
`canonicalDegreeSubfield K n'` (`canonicalDegreeSubfield_le_of_dvd`), reducing both sides to the
image of `Frob ^ k`, which is `Multiplicative.ofAdd k` on the `ℤ` side by
`mulEquivOfGenerators_apply_self` and `QuotientGroup.map_mk'`. -/
theorem levelMulEquiv_symm_naturality {H H' : FiniteIndexNormalSubgroup (Multiplicative ℤ)}
    (hle : H ≤ H') (g : kbar ≃ₐ[𝓀[K]] kbar) :
    haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
    haveI : NeZero H'.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
    QuotientGroup.map H.toSubgroup H'.toSubgroup (MonoidHom.id _) hle
        ((levelMulEquiv K H).symm (AlgEquiv.restrictNormalHom
          (canonicalDegreeSubfield K H.toSubgroup.index) g)) =
      (levelMulEquiv K H').symm (AlgEquiv.restrictNormalHom
        (canonicalDegreeSubfield K H'.toSubgroup.index) g) := by
  haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  haveI : NeZero H'.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  have hdvd : H'.toSubgroup.index ∣ H.toSubgroup.index :=
    FiniteIndexNormalSubgroup.index_dvd_index_of_le hle
  have hsub : canonicalDegreeSubfield K H'.toSubgroup.index ≤
      canonicalDegreeSubfield K H.toSubgroup.index := canonicalDegreeSubfield_le_of_dvd K hdvd
  obtain ⟨k, hk⟩ := zpowers_restrictNormalHom_frobeniusAlgEquiv_eq_top K
    (canonicalDegreeSubfield K H.toSubgroup.index)
    (AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index) g)
  have hkpow : AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index) g =
      (AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index)
        (frobeniusAlgEquiv K)) ^ k := hk.symm
  have hkpow' : AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index)
      (frobeniusAlgEquiv K ^ k) =
      AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index) g := by
    rw [map_zpow]; exact hkpow.symm
  have hsmall : AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H'.toSubgroup.index)
      (frobeniusAlgEquiv K ^ k) =
      AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H'.toSubgroup.index) g :=
    restrictNormalHom_eq_of_restrictNormalHom_eq K hsub hkpow'
  rw [← hsmall, hkpow]
  simp only [map_zpow]
  have hH : (levelMulEquiv K H).symm
      (AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index)
        (frobeniusAlgEquiv K)) = QuotientGroup.mk' H.toSubgroup (Multiplicative.ofAdd (1 : ℤ)) :=
    (levelMulEquiv K H).symm_apply_eq.mpr (mulEquivOfGenerators_apply_self _ _ _).symm
  have hH' : (levelMulEquiv K H').symm
      (AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H'.toSubgroup.index)
        (frobeniusAlgEquiv K)) = QuotientGroup.mk' H'.toSubgroup (Multiplicative.ofAdd (1 : ℤ)) :=
    (levelMulEquiv K H').symm_apply_eq.mpr (mulEquivOfGenerators_apply_self _ _ _).symm
  rw [hH, hH']
  erw [QuotientGroup.map_mk']

/-- The homomorphism `Gal(kbar/𝓀[K]) →* ℤ̂` assembled from `levelMulEquiv`: for
`g : kbar ≃ₐ[𝓀[K]] kbar`, the family
`H ↦ (levelMulEquiv H).symm (restrictNormalHom (canonicalDegreeSubfield K H.index) g)` is
compatible with the transition maps by `levelMulEquiv_symm_naturality`, hence is an element of the
limit defining `Zhat`. It is bijective (`toZhatHomOfAlgEquiv_injective`,
`toZhatHomOfAlgEquiv_surjective`) and sends Frobenius to the image of `1`
(`toZhatHomOfAlgEquiv_frobeniusAlgEquiv`). -/
noncomputable def toZhatHomOfAlgEquiv : (kbar ≃ₐ[𝓀[K]] kbar) →* Zhat where
  toFun g := {
    val := fun H =>
      haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
      (levelMulEquiv K H).symm
        (AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index) g)
    property := fun {H H'} π => by
      haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
      haveI : NeZero H'.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
      exact levelMulEquiv_symm_naturality K (leOfHom π) g }
  map_one' := by
    apply Subtype.ext
    funext H
    haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
    show (levelMulEquiv K H).symm
      (AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index) 1) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    apply Subtype.ext
    funext H
    haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
    show (levelMulEquiv K H).symm
        (AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index) (a * b)) =
      (levelMulEquiv K H).symm
          (AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index) a) *
        (levelMulEquiv K H).symm
          (AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index) b)
    rw [map_mul, map_mul]

/-- `toZhatHomOfAlgEquiv` is injective. If `g` maps to `1`, then for each `n` the component at the
unique index-`n` subgroup `H` (`existsUnique_finiteIndexNormalSubgroup_index_eq`) is trivial, so
`g` restricts to the identity on `canonicalDegreeSubfield K n`; then
`eq_one_of_forall_restrictNormalHom_canonicalDegreeSubfield_eq_one` gives `g = 1`. -/
theorem toZhatHomOfAlgEquiv_injective : Function.Injective (toZhatHomOfAlgEquiv K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply eq_one_of_forall_restrictNormalHom_canonicalDegreeSubfield_eq_one K g
  intro n _
  obtain ⟨H, hHn, -⟩ := existsUnique_finiteIndexNormalSubgroup_index_eq (NeZero.ne n)
  haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  have hone : (1 : Zhat).val H = 1 :=
    ProfiniteGrp.limit_one_val (ProfiniteGrp.ProfiniteCompletion.diagram
      (GrpCat.of (Multiplicative ℤ))) H
  have hval : (levelMulEquiv K H).symm
      (AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index) g) = 1 := by
    have hcongr := congrFun (congrArg Subtype.val hg) H
    rw [hone] at hcongr
    exact hcongr
  have h2 : AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index) g = 1 := by
    rw [(levelMulEquiv K H).symm_apply_eq, map_one] at hval
    exact hval
  exact hHn ▸ h2

/-! ### Surjectivity of `toZhatHomOfAlgEquiv` -/

/-- A choice of automorphism of `kbar/𝓀[K]` realizing the `H`-component of `z : Zhat`: a preimage
of `levelMulEquiv K H (z.val H)` under restriction to `canonicalDegreeSubfield K H.index`, which
exists by `AlgEquiv.restrictNormalHom_surjective`. -/
noncomputable def liftLevel (z : Zhat) (H : FiniteIndexNormalSubgroup (Multiplicative ℤ)) :
    kbar ≃ₐ[𝓀[K]] kbar :=
  haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  (AlgEquiv.restrictNormalHom_surjective (F := 𝓀[K])
    (K₁ := canonicalDegreeSubfield K H.toSubgroup.index) kbar (levelMulEquiv K H (z.val H))).choose

theorem restrictNormalHom_liftLevel (z : Zhat) (H : FiniteIndexNormalSubgroup (Multiplicative ℤ)) :
    haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
    AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index) (liftLevel K z H) =
      levelMulEquiv K H (z.val H) :=
  haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  (AlgEquiv.restrictNormalHom_surjective (F := 𝓀[K])
    (K₁ := canonicalDegreeSubfield K H.toSubgroup.index) kbar
    (levelMulEquiv K H (z.val H))).choose_spec

/-- For `H ≤ H'`, the choice `liftLevel K z H` already realizes the `H'`-component of `z` after
restriction to `canonicalDegreeSubfield K H'.index`, by compatibility of `z` across `H ⟶ H'` and
naturality of `levelMulEquiv`. This is what makes the level-by-level choices glue. -/
theorem restrictNormalHom_liftLevel_of_le (z : Zhat)
    {H H' : FiniteIndexNormalSubgroup (Multiplicative ℤ)} (hle : H ≤ H') :
    haveI : NeZero H'.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
    AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H'.toSubgroup.index) (liftLevel K z H) =
      levelMulEquiv K H' (z.val H') := by
  haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  haveI : NeZero H'.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  have hnat := levelMulEquiv_symm_naturality K hle (liftLevel K z H)
  rw [restrictNormalHom_liftLevel K z H, (levelMulEquiv K H).symm_apply_apply] at hnat
  have hzcompat : (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of (Multiplicative ℤ))).map
      (homOfLE hle) (z.val H) = z.val H' := z.property (homOfLE hle)
  have hzcompat' : QuotientGroup.map H.toSubgroup H'.toSubgroup (MonoidHom.id _) hle (z.val H) =
      z.val H' := hzcompat
  rw [hzcompat'] at hnat
  exact (levelMulEquiv K H').symm_apply_eq.mp hnat.symm

/-- The choices `liftLevel K z H` agree on common ground: if `x` lies in both
`canonicalDegreeSubfield K H.index` and `canonicalDegreeSubfield K H'.index`, then
`liftLevel K z H x = liftLevel K z H' x`. Both are compared against the common refinement
`H ⊓ H'` via `restrictNormalHom_liftLevel_of_le`. -/
theorem liftLevel_apply_eq_of_mem (z : Zhat) {H H' : FiniteIndexNormalSubgroup (Multiplicative ℤ)}
    {x : kbar} :
    haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
    haveI : NeZero H'.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
    x ∈ canonicalDegreeSubfield K H.toSubgroup.index →
    x ∈ canonicalDegreeSubfield K H'.toSubgroup.index →
    liftLevel K z H x = liftLevel K z H' x := by
  haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  haveI : NeZero H'.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  intro hxH hxH'
  set N := H ⊓ H' with hN
  have hNH : N ≤ H := inf_le_left
  have hNH' : N ≤ H' := inf_le_right
  have heqH : AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index)
      (liftLevel K z H) =
      AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index)
        (liftLevel K z N) := by
    rw [restrictNormalHom_liftLevel_of_le K z hNH, restrictNormalHom_liftLevel K z H]
  have heqH' : AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H'.toSubgroup.index)
      (liftLevel K z H') =
      AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H'.toSubgroup.index)
        (liftLevel K z N) := by
    rw [restrictNormalHom_liftLevel_of_le K z hNH', restrictNormalHom_liftLevel K z H']
  have h1 := AlgEquiv.restrictNormalHom_apply (canonicalDegreeSubfield K H.toSubgroup.index)
    (liftLevel K z H) ⟨x, hxH⟩
  have h2 := AlgEquiv.restrictNormalHom_apply (canonicalDegreeSubfield K H.toSubgroup.index)
    (liftLevel K z N) ⟨x, hxH⟩
  have h3 := AlgEquiv.restrictNormalHom_apply (canonicalDegreeSubfield K H'.toSubgroup.index)
    (liftLevel K z H') ⟨x, hxH'⟩
  have h4 := AlgEquiv.restrictNormalHom_apply (canonicalDegreeSubfield K H'.toSubgroup.index)
    (liftLevel K z N) ⟨x, hxH'⟩
  have hHN : liftLevel K z H x = liftLevel K z N x := by
    rw [← h1, ← h2, heqH]
  have hH'N : liftLevel K z H' x = liftLevel K z N x := by
    rw [← h3, ← h4, heqH']
  rw [hHN, hH'N]

/-- Every element of `kbar` lies in `canonicalDegreeSubfield K H.index` for some finite-index normal
subgroup `H ≤ Multiplicative ℤ`, by `exists_mem_canonicalDegreeSubfield` and
`existsUnique_finiteIndexNormalSubgroup_index_eq`. -/
theorem exists_finiteIndexNormalSubgroup_mem (x : kbar) :
    ∃ H : FiniteIndexNormalSubgroup (Multiplicative ℤ),
      haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
      x ∈ canonicalDegreeSubfield K H.toSubgroup.index := by
  obtain ⟨n, hn, hx⟩ := exists_mem_canonicalDegreeSubfield K x
  haveI := hn
  obtain ⟨H, hHn, -⟩ := existsUnique_finiteIndexNormalSubgroup_index_eq (NeZero.ne n)
  haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  exact ⟨H, hHn ▸ hx⟩

/-- The gluing of the `liftLevel` choices into a function `kbar → kbar`: at `x`, apply
`liftLevel K z H` for some `H` with `x ∈ canonicalDegreeSubfield K H.index`
(`exists_finiteIndexNormalSubgroup_mem`). Independence of the choice is
`liftLevel_apply_eq_of_mem`. -/
noncomputable def surjLift (z : Zhat) (x : kbar) : kbar :=
  liftLevel K z (exists_finiteIndexNormalSubgroup_mem K x).choose x

/-- `surjLift K z` agrees with `liftLevel K z H` on `canonicalDegreeSubfield K H.index`. -/
theorem surjLift_eq_liftLevel_apply (z : Zhat) (H : FiniteIndexNormalSubgroup (Multiplicative ℤ))
    (x : kbar) :
    haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
    x ∈ canonicalDegreeSubfield K H.toSubgroup.index → surjLift K z x = liftLevel K z H x := by
  haveI : NeZero H.toSubgroup.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  intro hx
  exact liftLevel_apply_eq_of_mem K z (exists_finiteIndexNormalSubgroup_mem K x).choose_spec hx

/-- Any two elements of `kbar` lie in a common `canonicalDegreeSubfield K H.index`: take the meet of
the witnesses given by `exists_finiteIndexNormalSubgroup_mem` and apply
`canonicalDegreeSubfield_le_of_dvd`. -/
theorem exists_finiteIndexNormalSubgroup_mem₂ (x y : kbar) :
    ∃ H : FiniteIndexNormalSubgroup (Multiplicative ℤ),
      x ∈ canonicalDegreeSubfield K H.toSubgroup.index ∧
        y ∈ canonicalDegreeSubfield K H.toSubgroup.index := by
  obtain ⟨Hx, hx⟩ := exists_finiteIndexNormalSubgroup_mem K x
  obtain ⟨Hy, hy⟩ := exists_finiteIndexNormalSubgroup_mem K y
  refine ⟨Hx ⊓ Hy, ?_, ?_⟩
  · exact canonicalDegreeSubfield_le_of_dvd K
      (FiniteIndexNormalSubgroup.index_dvd_index_of_le (inf_le_left (a := Hx) (b := Hy))) hx
  · exact canonicalDegreeSubfield_le_of_dvd K
      (FiniteIndexNormalSubgroup.index_dvd_index_of_le (inf_le_right (a := Hx) (b := Hy))) hy

/-- `surjLift K z` is additive: `x`, `y` and `x + y` lie in a common
`canonicalDegreeSubfield K H.index` (`exists_finiteIndexNormalSubgroup_mem₂`), where `surjLift K z`
agrees with the ring homomorphism `liftLevel K z H`. -/
theorem surjLift_add (z : Zhat) (x y : kbar) :
    surjLift K z (x + y) = surjLift K z x + surjLift K z y := by
  obtain ⟨H, hx, hy⟩ := exists_finiteIndexNormalSubgroup_mem₂ K x y
  have hxy : x + y ∈ canonicalDegreeSubfield K H.toSubgroup.index := add_mem hx hy
  rw [surjLift_eq_liftLevel_apply K z H x hx, surjLift_eq_liftLevel_apply K z H y hy,
    surjLift_eq_liftLevel_apply K z H (x + y) hxy, map_add]

/-- `surjLift K z` is multiplicative, by the argument of `surjLift_add`. -/
theorem surjLift_mul (z : Zhat) (x y : kbar) :
    surjLift K z (x * y) = surjLift K z x * surjLift K z y := by
  obtain ⟨H, hx, hy⟩ := exists_finiteIndexNormalSubgroup_mem₂ K x y
  have hxy : x * y ∈ canonicalDegreeSubfield K H.toSubgroup.index := mul_mem hx hy
  rw [surjLift_eq_liftLevel_apply K z H x hx, surjLift_eq_liftLevel_apply K z H y hy,
    surjLift_eq_liftLevel_apply K z H (x * y) hxy, map_mul]

/-- `surjLift K z` fixes `𝓀[K]` pointwise: `𝓀[K]` lies in every `canonicalDegreeSubfield K n`,
where `surjLift K z` agrees with a `𝓀[K]`-algebra automorphism. -/
theorem surjLift_algebraMap (z : Zhat) (c : 𝓀[K]) :
    surjLift K z (algebraMap 𝓀[K] kbar c) = algebraMap 𝓀[K] kbar c := by
  obtain ⟨H, hx⟩ := exists_finiteIndexNormalSubgroup_mem K (algebraMap 𝓀[K] kbar c)
  rw [surjLift_eq_liftLevel_apply K z H _ hx]
  exact (liftLevel K z H).commutes c

/-- `surjLift K z⁻¹` is a left inverse of `surjLift K z`. Both `x` and `surjLift K z x` lie in a
common `canonicalDegreeSubfield K H.index`, where the two agree with `liftLevel K z H` and
`liftLevel K z⁻¹ H`; these restrict to mutually inverse automorphisms, since
`levelMulEquiv K H (z⁻¹.val H) = (levelMulEquiv K H (z.val H))⁻¹`. -/
theorem surjLift_left_inv (z : Zhat) (x : kbar) : surjLift K z⁻¹ (surjLift K z x) = x := by
  obtain ⟨Hx, hx⟩ := exists_finiteIndexNormalSubgroup_mem K x
  have hgx : surjLift K z x = liftLevel K z Hx x := surjLift_eq_liftLevel_apply K z Hx x hx
  have hy := AlgEquiv.restrictNormalHom_apply (canonicalDegreeSubfield K Hx.toSubgroup.index)
    (liftLevel K z Hx) ⟨x, hx⟩
  rw [restrictNormalHom_liftLevel K z Hx] at hy
  have hgxMem : surjLift K z x ∈ canonicalDegreeSubfield K Hx.toSubgroup.index := by
    rw [hgx, ← hy]
    exact (levelMulEquiv K Hx (z.val Hx) ⟨x, hx⟩).2
  have hinv : liftLevel K z⁻¹ Hx (liftLevel K z Hx x) = x := by
    have hz := AlgEquiv.restrictNormalHom_apply (canonicalDegreeSubfield K Hx.toSubgroup.index)
      (liftLevel K z⁻¹ Hx) (levelMulEquiv K Hx (z.val Hx) ⟨x, hx⟩)
    rw [restrictNormalHom_liftLevel K z⁻¹ Hx] at hz
    have hzinv : z⁻¹.val Hx = (z.val Hx)⁻¹ := rfl
    rw [hzinv] at hz
    have hmulone : levelMulEquiv K Hx (z.val Hx) * levelMulEquiv K Hx ((z.val Hx)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hinvEq : levelMulEquiv K Hx ((z.val Hx)⁻¹) = (levelMulEquiv K Hx (z.val Hx))⁻¹ :=
      eq_inv_of_mul_eq_one_right hmulone
    erw [hinvEq, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply] at hz
    rw [← hy]
    exact hz.symm
  rw [surjLift_eq_liftLevel_apply K z⁻¹ Hx (surjLift K z x) hgxMem, hgx, hinv]

/-- `surjLift K z⁻¹` is a right inverse of `surjLift K z`, by `surjLift_left_inv` applied to
`z⁻¹`. -/
theorem surjLift_right_inv (z : Zhat) (x : kbar) : surjLift K z (surjLift K z⁻¹ x) = x := by
  have := surjLift_left_inv K z⁻¹ x
  rwa [inv_inv] at this

/-- `surjLift K z` as an element of `Gal(kbar/𝓀[K])`. -/
noncomputable def surjLiftAlgEquiv (z : Zhat) : kbar ≃ₐ[𝓀[K]] kbar where
  toFun := surjLift K z
  invFun := surjLift K z⁻¹
  left_inv := surjLift_left_inv K z
  right_inv := surjLift_right_inv K z
  map_mul' := surjLift_mul K z
  map_add' := surjLift_add K z
  commutes' := surjLift_algebraMap K z

/-- `toZhatHomOfAlgEquiv K` is surjective: `surjLiftAlgEquiv K z` maps to `z`, checked level by
level using `surjLift_eq_liftLevel_apply` and `restrictNormalHom_liftLevel`. -/
theorem toZhatHomOfAlgEquiv_surjective : Function.Surjective (toZhatHomOfAlgEquiv K) := by
  intro z
  refine ⟨surjLiftAlgEquiv K z, ?_⟩
  apply Subtype.ext
  funext H
  show (levelMulEquiv K H).symm
      (AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index)
        (surjLiftAlgEquiv K z)) = z.val H
  have heq : AlgEquiv.restrictNormalHom (canonicalDegreeSubfield K H.toSubgroup.index)
      (surjLiftAlgEquiv K z) = levelMulEquiv K H (z.val H) := by
    apply AlgEquiv.ext
    intro x
    have hx : (x : kbar) ∈ canonicalDegreeSubfield K H.toSubgroup.index := x.2
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    show surjLift K z (x : kbar) = _
    rw [surjLift_eq_liftLevel_apply K z H (x : kbar) hx,
      ← AlgEquiv.restrictNormalHom_apply (canonicalDegreeSubfield K H.toSubgroup.index)
        (liftLevel K z H) x,
      restrictNormalHom_liftLevel K z H]
  rw [heq, (levelMulEquiv K H).symm_apply_apply]

/-! ### The absolute Galois group of a finite field

The classical computation: `Gal(kbar/𝓀[K])` is topologically generated by Frobenius
(`denseRange_frobeniusZpowersHom`) and, as an abstract group, isomorphic to `ℤ̂` by
`toZhatHomOfAlgEquiv`, which carries Frobenius to the image of `1`. Transporting along
`galEquivRangeResidueAction : Gal(kbar/𝓀[K]) ≃* (residueAction K).range` gives
`exists_residueGaloisGroup_equiv_Zhat`.
-/

/-- `toZhatHomOfAlgEquiv K` sends Frobenius to the image of `1` under `toZhat`. Every component is
`QuotientGroup.mk' H.toSubgroup (Multiplicative.ofAdd 1)`: on the left because `levelMulEquiv`
matches generators, on the right because the `etaFn` underlying `toZhat` sends `x` to the constant
family `fun _ => QuotientGroup.mk x`. -/
theorem toZhatHomOfAlgEquiv_frobeniusAlgEquiv :
    toZhatHomOfAlgEquiv K (frobeniusAlgEquiv K) = toZhat (Multiplicative.ofAdd (1 : ℤ)) := by
  apply Subtype.ext
  funext H
  have hlhs : (toZhatHomOfAlgEquiv K (frobeniusAlgEquiv K)).val H =
      QuotientGroup.mk' H.toSubgroup (Multiplicative.ofAdd (1 : ℤ)) :=
    (levelMulEquiv K H).symm_apply_eq.mpr (mulEquivOfGenerators_apply_self _ _ _).symm
  have hrhs : (toZhat (Multiplicative.ofAdd (1 : ℤ))).val H =
      QuotientGroup.mk' H.toSubgroup (Multiplicative.ofAdd (1 : ℤ)) := rfl
  rw [hlhs, hrhs]

/-- `AlgEquiv.toRingEquiv` as a monoid homomorphism `Gal(kbar/𝓀[K]) →* RingAut kbar`. The
multiplicativity fields hold by `rfl`, both groups using the convention `ϕ * ψ = ψ.trans ϕ`. -/
def algEquivToRingAut : (kbar ≃ₐ[𝓀[K]] kbar) →* RingAut kbar where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `algEquivToRingAut` is injective: an algebra automorphism is determined by its underlying ring
automorphism. -/
theorem algEquivToRingAut_injective : Function.Injective (algEquivToRingAut K) := by
  intro a b hab
  apply AlgEquiv.ext
  intro x
  exact RingEquiv.congr_fun hab x

/-- `residueAction` factors as `algEquivToRingAut ∘ residueAction'`. -/
theorem residueAction_eq_comp :
    residueAction K = (algEquivToRingAut K).comp (residueAction' K) := by
  apply MonoidHom.ext
  intro σ
  apply RingEquiv.ext
  intro x
  exact (residueAction'_apply K σ x).symm

/-- The range of `residueAction K` is that of `algEquivToRingAut K`, i.e. all of `Gal(kbar/𝓀[K])`
viewed inside `RingAut kbar`: `residueAction' K` is surjective (`surjective_residueAction'`), so
the factorization `residueAction_eq_comp` maps `⊤` onto the whole range. -/
theorem range_residueAction_eq_range_algEquivToRingAut :
    (residueAction K).range = (algEquivToRingAut K).range := by
  rw [residueAction_eq_comp, ← MonoidHom.map_range,
    MonoidHom.range_eq_top_of_surjective _ (surjective_residueAction' K), MonoidHom.range_eq_map]

/-- The identification of `Gal(kbar/𝓀[K])` with `(residueAction K).range`, from injectivity of
`algEquivToRingAut` and `range_residueAction_eq_range_algEquivToRingAut`. -/
noncomputable def galEquivRangeResidueAction :
    (kbar ≃ₐ[𝓀[K]] kbar) ≃* (residueAction K).range :=
  (MonoidHom.ofInjective (algEquivToRingAut_injective K)).trans
    (MulEquiv.subgroupCongr (range_residueAction_eq_range_algEquivToRingAut K).symm)

@[simp]
theorem coe_galEquivRangeResidueAction (σ : kbar ≃ₐ[𝓀[K]] kbar) :
    (galEquivRangeResidueAction K σ : RingAut kbar) = algEquivToRingAut K σ := rfl

/-- The range of `residueAction K`, i.e. the Galois group of the residue extension, is isomorphic
to `ℤ̂` by an isomorphism carrying Frobenius to the image of `1`. This is the isomorphism
`toZhatHomOfAlgEquiv`, transported along `galEquivRangeResidueAction`. It is an isomorphism of
abstract groups; it is not shown here to be a homeomorphism. -/
theorem exists_residueGaloisGroup_equiv_Zhat :
    ∃ e : (residueAction K).range ≃* Zhat,
      e ⟨frobenius K, frobenius_mem_residueAction_range K⟩ = toZhat (Multiplicative.ofAdd 1) := by
  have hbij : Function.Bijective (toZhatHomOfAlgEquiv K) :=
    ⟨toZhatHomOfAlgEquiv_injective K, toZhatHomOfAlgEquiv_surjective K⟩
  refine ⟨(galEquivRangeResidueAction K).symm.trans (MulEquiv.ofBijective (toZhatHomOfAlgEquiv K)
    hbij), ?_⟩
  have hker : galEquivRangeResidueAction K (frobeniusAlgEquiv K) =
      ⟨frobenius K, frobenius_mem_residueAction_range K⟩ := by
    apply Subtype.ext
    rw [coe_galEquivRangeResidueAction]
    rfl
  show (MulEquiv.ofBijective (toZhatHomOfAlgEquiv K) hbij)
      ((galEquivRangeResidueAction K).symm ⟨frobenius K, frobenius_mem_residueAction_range K⟩) =
    toZhat (Multiplicative.ofAdd 1)
  rw [← hker, (galEquivRangeResidueAction K).symm_apply_apply,
    MulEquiv.ofBijective_apply, toZhatHomOfAlgEquiv_frobeniusAlgEquiv]

/-- A fixed choice of the isomorphism of `exists_residueGaloisGroup_equiv_Zhat`, identifying the
range of `residueAction K` with `ℤ̂`. -/
def residueGaloisGroupEquivZhat : (residueAction K).range ≃* Zhat :=
  (exists_residueGaloisGroup_equiv_Zhat K).choose

/-! ### The Weil group -/

/-- The homomorphism `G_K →* ℤ̂` sending `σ` to the profinite power of Frobenius it induces on the
residue field. Its kernel is `I_K` (`toZhatHom_ker`). -/
def toZhatHom : Field.absoluteGaloisGroup K →* Zhat :=
  (residueGaloisGroupEquivZhat K).toMonoidHom.comp (residueAction K).rangeRestrict

/-- The **Weil group** `W_K` of `K`: the subgroup of those `σ ∈ G_K` inducing an integer power of
Frobenius on the residue field, i.e. the preimage of `integerSubgroup` under `toZhatHom`. -/
def WeilGroup : Subgroup (Field.absoluteGaloisGroup K) :=
  Subgroup.comap (toZhatHom K) (integerSubgroup)

/-- The inertia subgroup is contained in the Weil group, its elements mapping to `1`. -/
theorem inertiaSubgroup_le_weilGroup : inertiaSubgroup K ≤ WeilGroup K := by
  rw [← residueAction_ker]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  simp only [WeilGroup, Subgroup.mem_comap, toZhatHom, MonoidHom.coe_comp, Function.comp_apply]
  rw [show (residueAction K).rangeRestrict x = 1 from Subtype.ext hx, map_one]
  exact Subgroup.one_mem _

/-- `inertiaSubgroup K` is normal in `G_K`, being the kernel of `residueAction K`
(`residueAction_ker`). -/
instance inertiaSubgroup_normal : (inertiaSubgroup K).Normal := by
  rw [← residueAction_ker]; infer_instance

/-- The **Artin map** `W_K →* ℤ`, sending `σ ∈ W_K` to the integer `n` with `σ` inducing `Frob ^ n`
on the residue field, read off through `integerSubgroupEquiv`. Its kernel is `I_K`
(`toArt_ker`). -/
def toArt : WeilGroup K →* Multiplicative ℤ :=
  integerSubgroupEquiv.symm.toMonoidHom.comp
    (((toZhatHom K).restrict (WeilGroup K)).codRestrict integerSubgroup
      fun w => Subgroup.mem_comap.mp w.2)

/-- The kernel of `toZhatHom` is `I_K`: `σ` induces the trivial power of Frobenius exactly when it
acts trivially on the residue field, `residueGaloisGroupEquivZhat` being injective. -/
theorem toZhatHom_ker : (toZhatHom K).ker = inertiaSubgroup K := by
  unfold toZhatHom
  rw [MonoidHom.ker_comp_of_injective _ _ (residueGaloisGroupEquivZhat K).injective,
    MonoidHom.ker_rangeRestrict, residueAction_ker]

/-- The kernel of the Artin map is `I_K`, viewed as a subgroup of `W_K`. -/
theorem toArt_ker : (toArt K).ker = (inertiaSubgroup K).subgroupOf (WeilGroup K) := by
  unfold toArt
  rw [MonoidHom.ker_comp_of_injective _ _ integerSubgroupEquiv.symm.injective,
    MonoidHom.ker_codRestrict, MonoidHom.ker_restrict, toZhatHom_ker]

/-! ### The topology on `W_K` -/

/-- The basic neighbourhood of `1` in `W_K` attached to an open subgroup `U ≤ G_K`: the elements of
`W_K` lying in both `U` and the inertia subgroup. As `U` ranges over the open subgroups of `G_K`
these form a filter basis at `1` (`groupFilterBasis`). -/
def basicSubgroup (U : OpenSubgroup (Field.absoluteGaloisGroup K)) : Subgroup (WeilGroup K) :=
  (U.toSubgroup ⊓ inertiaSubgroup K).subgroupOf (WeilGroup K)

/-- The `GroupFilterBasis` on `W_K` with basic neighbourhoods of `1` the `basicSubgroup K U`, for
`U` an open subgroup of `G_K`. Since `I_K = basicSubgroup K ⊤`, it is open for the resulting
topology; continuity of multiplication, inversion and conjugation is inherited from `G_K`. -/
@[implicit_reducible]
def groupFilterBasis : GroupFilterBasis (WeilGroup K) where
  sets := Set.range fun U : OpenSubgroup (Field.absoluteGaloisGroup K) =>
    (basicSubgroup K U : Set (WeilGroup K))
  nonempty := Set.range_nonempty _
  inter_sets := by
    rintro _ _ ⟨U, rfl⟩ ⟨V, rfl⟩
    refine ⟨_, Set.mem_range_self (⟨U.toSubgroup ⊓ V.toSubgroup, U.isOpen.inter V.isOpen⟩ :
      OpenSubgroup (Field.absoluteGaloisGroup K)), fun w hw => ?_⟩
    simp only [basicSubgroup, SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      OpenSubgroup.mem_toSubgroup, Set.mem_inter_iff] at hw ⊢
    tauto
  one' := by rintro _ ⟨U, rfl⟩; exact (basicSubgroup K U).one_mem
  mul' := by
    rintro _ ⟨U, rfl⟩
    exact ⟨_, Set.mem_range_self U, fun w ⟨a, ha, b, hb, hab⟩ => hab ▸ Subgroup.mul_mem _ ha hb⟩
  inv' := by
    rintro _ ⟨U, rfl⟩
    exact ⟨_, Set.mem_range_self U, fun w hw => Subgroup.inv_mem _ hw⟩
  conj' := by
    rintro x₀ _ ⟨U, rfl⟩
    refine ⟨_, Set.mem_range_self (U.comap (MulAut.conj (x₀ : Field.absoluteGaloisGroup K)).toMonoidHom
      (IsTopologicalGroup.continuous_conj _)), fun w hw => ?_⟩
    simp only [Set.mem_preimage, basicSubgroup, SetLike.mem_coe, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf] at hw ⊢
    have hcoe : ((x₀ * w * x₀⁻¹ : WeilGroup K) : Field.absoluteGaloisGroup K) =
        (x₀ : Field.absoluteGaloisGroup K) * (w : Field.absoluteGaloisGroup K) *
          (x₀ : Field.absoluteGaloisGroup K)⁻¹ := by
      simp [Subgroup.coe_mul]
    rw [hcoe]
    refine ⟨?_, (inertiaSubgroup_normal K).conj_mem _ hw.2 _⟩
    simpa [OpenSubgroup.mem_comap, MulAut.conj_apply] using hw.1

/-- The topology on `W_K` making `I_K` an open subgroup, generated by `groupFilterBasis`. It is
strictly finer than the subspace topology inherited from `G_K`. -/
instance instTopologicalSpace : TopologicalSpace (WeilGroup K) := (groupFilterBasis K).topology

/-- `W_K` is a topological group for `instTopologicalSpace`. -/
instance instIsTopologicalGroup : IsTopologicalGroup (WeilGroup K) :=
  (groupFilterBasis K).isTopologicalGroup

/-- `I_K`, as a subgroup of `W_K`, is open. This is the defining property of the Weil group
topology, and is what distinguishes it from the subspace topology from `G_K`. -/
theorem isOpen_inertiaSubgroupOf :
    IsOpen ((inertiaSubgroup K).subgroupOf (WeilGroup K) : Set (WeilGroup K)) := by
  have hmem : ((inertiaSubgroup K).subgroupOf (WeilGroup K) : Set (WeilGroup K)) ∈
      groupFilterBasis K := ⟨⊤, by simp [basicSubgroup, OpenSubgroup.toSubgroup_top]⟩
  exact Subgroup.isOpen_of_mem_nhds _ ((groupFilterBasis K).mem_nhds_one hmem)

/-- The quotient `W_K ⧸ I_K` is discrete, `I_K` being open (`isOpen_inertiaSubgroupOf`). With
`toArt_ker`, this identifies `W_K ⧸ I_K` topologically with the discrete group `ℤ`. -/
theorem discreteTopology_quotient_inertiaSubgroupOf :
    DiscreteTopology (WeilGroup K ⧸ (inertiaSubgroup K).subgroupOf (WeilGroup K)) :=
  QuotientGroup.discreteTopology (isOpen_inertiaSubgroupOf K)

end LocalField
