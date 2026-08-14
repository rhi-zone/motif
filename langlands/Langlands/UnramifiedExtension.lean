import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Langlands.MonogenicMaximalOrder
import Langlands.HenselianValuation

/-!
# Unramified extensions and lifting automorphisms of the residue field

Let `K` be a field with a `ValuativeRel`, `L / K` a field extension, and `A : ValuationSubring L`
a valuation subring lying over `𝒪[K]`, equipped with an `Algebra ↥(𝒪[K]) A` structure compatible
with the inclusion `𝒪[K] → K → L`. The decomposition subgroup `A.decompositionSubgroup K ≤
Gal(L/K)` then acts on the residue field `IsLocalRing.ResidueField A`.

## Main results

* `ValuationSubring.decompositionSubgroup_smul_algebraMap_residueField`: the decomposition subgroup
  fixes the image of the base residue field `𝓀[K]` in `IsLocalRing.ResidueField A` pointwise.

* `ValuationSubring.exists_restrictNormalHom_decompositionSubgroup_surjective`: the unramified
  lifting theorem. For `K` a nonarchimedean local field and `L / K` algebraic and algebraically
  closed, every automorphism of a finite normal subextension `M` of
  `IsLocalRing.ResidueField A / 𝓀[K]` is the restriction to `M` of the residue action of some
  element of the decomposition subgroup.

* `ValuationSubring.exists_aeval_root_residue_eq`: for `L` algebraically closed and `f` monic over
  a ring mapping to `A`, every root of the reduction of `f` modulo the maximal ideal of `A` is the
  residue of a root of `f` in `A` itself. This is what supplies the lifting theorem with roots
  whose residues are prescribed.

* `HenselianLocalRing.exists_isDiscreteValuationRing_integralClosure_residueField_equiv`: for `R` a
  Henselian discrete valuation ring with finite residue field `k`, and `β₀` a primitive element of
  a finite extension `l / k`, the integral closure of `R` in `K⟮x⟯` — where `x` is a root, in an
  algebraically closed `L / K`, of a monic lift of `minpoly k β₀` — is a discrete valuation ring
  with residue field `l`. This is the classical construction of the unramified extension of `K`
  attached to `l / k`; it is a standalone result, not used in the proof of the lifting theorem
  above.

The remaining declarations are the polynomial- and `AdjoinRoot`-level ingredients of that
construction: the monic lift of a minimal polynomial over the residue field
(`HenselianLocalRing.exists_monic_lift_minpoly`), its irreducibility and separability
(`irreducible_lift_minpoly`, `irreducible_map_lift_minpoly`, `isUnit_resultant_lift_minpoly`,
`separable_lift_minpoly`, `separable_map_lift_minpoly`), and the structure of `AdjoinRoot f`
(`isDomain_`, `finrank_`, `isLocalRing_`, and
`residueField_equiv_adjoinRoot_lift_minpoly` with its generator-compatibility lemma).

## Implementation notes

Compatibility of the algebra structure `↥(𝒪[K]) → A` with the inclusion `𝒪[K] → K → L` is carried
as an explicit hypothesis `hcompat` rather than as an `IsScalarTower ↥(𝒪[K]) A L` instance.
Instance search fails to apply the derived scalar-tower instance at the one call site
(`Langlands.WeilGroup`, where `L` is instantiated with `AlgebraicClosure K`) even though the two
statements are definitionally equal; as an ordinary hypothesis it is discharged there by `rfl`. -/

noncomputable section

open ValuativeRel Valuation IsLocalRing Polynomial
open scoped Pointwise

-- Instance-diamond fix. `IsLocalRing.ResidueField.algebraOfIsIntegral` and
-- `IntermediateField.algebra'` both supply `Algebra 𝓀[K] ↥M` whenever `M` is an intermediate field
-- of a residue field over `𝓀[K]` — as at the call site in `Langlands.WeilGroup`, where `𝓀[K]` is
-- itself `IsLocalRing.ResidueField ↥(𝒪[K])` and the `Algebra.IsIntegral ↥(𝒪[K]) ↥M` premise becomes
-- available through `Mathlib.RingTheory.DedekindDomain.Different`. The two instances are not defeq,
-- which breaks `rfl`-based proofs assuming the `IntermediateField.algebra'` unfolding. Since `M` is
-- genuinely an intermediate field there, deprioritizing the more general residue-field instance
-- makes instance search prefer `IntermediateField.algebra'` whenever both apply.
attribute [instance low] IsLocalRing.ResidueField.algebraOfIsIntegral

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [ValuativeRel K]
  (A : ValuationSubring L) [Algebra ↥(𝒪[K]) A]
  [IsLocalHom (algebraMap ↥(𝒪[K]) A)]

/-- Elements of the decomposition subgroup of `A`, i.e. `K`-algebra automorphisms of `L` stabilizing
`A`, fix the image of `𝓀[K]` in `IsLocalRing.ResidueField A` pointwise. Every `σ ∈ Gal(L/K)` fixes
`K` pointwise, hence fixes the image of `𝒪[K]` in `A` pointwise by `hcompat`, hence fixes the image
of `𝓀[K]` in the residue field. -/
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

end ValuationSubring

/-! ### The ring of integers of a nonarchimedean local field -/

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The ring of integers of a nonarchimedean local field is a Dedekind domain. `𝒪[K]` is a discrete
valuation ring (`Mathlib.NumberTheory.LocalField.Basic`), and `IsDiscreteValuationRing.TFAE`
identifies that with `IsDedekindDomain` for a local domain that is not a field. -/
instance isDedekindDomain : IsDedekindDomain ↥(𝒪[K]) :=
  ((IsDiscreteValuationRing.TFAE ↥(𝒪[K]) (IsDiscreteValuationRing.not_isField ↥(𝒪[K]))).out 0 2).mp
    (inferInstance : IsDiscreteValuationRing ↥(𝒪[K]))

/-- The ring of integers of a nonarchimedean local field is a Henselian local ring. `𝒪[K]` is
`𝓂[K]`-adically complete (`IsAdicComplete`, `Mathlib.NumberTheory.LocalField.Basic`), whence
`HenselianRing 𝒪[K] 𝓂[K]` by `IsAdicComplete.henselianRing`. The uniform structure that
`IsAdicComplete` is stated against is supplied locally from the topology on `K`. -/
instance henselianLocalRing : HenselianLocalRing ↥(𝒪[K]) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI : HenselianRing ↥(𝒪[K]) 𝓂[K] := IsAdicComplete.henselianRing _ _
  refine HenselianLocalRing.mk fun f hf a₀ ha₀ hderiv => ?_
  exact HenselianRing.is_henselian f hf a₀ ha₀ (hderiv.map (Ideal.Quotient.mk 𝓂[K]))

/-- The ring of integers of a nonarchimedean local field is `𝓂[K]`-adically complete. This is a
plain Mathlib instance (`Mathlib.NumberTheory.LocalField.Basic`, `IsNonarchimedeanLocalField`'s
`UniformSpace` section) once the uniform structure on `K` compatible with its topology is
supplied; the same local `letI`/`haveI` pair as `henselianLocalRing` produces it. Named
explicitly (rather than left to bare `inferInstance` at call sites) so that
`isAdicComplete_of_valuationSubring` below can transport it by a type-ascription cast, mirroring
how `henselianLocalRing_of_valuationSubring` transports `henselianLocalRing`. -/
instance isAdicComplete : IsAdicComplete 𝓂[K] ↥(𝒪[K]) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

open scoped NormedField Valued in
/-- The `IsNonarchimedeanLocalField K` instance underlying a *lighter-bundle* complete
discretely-valued field with finite residue field. `IsNonarchimedeanLocalField K` packages
`LocallyCompactSpace K`, which is not part of the lighter bundle
`[NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K] [_.Compatible]
[CompleteSpace K] [IsDiscreteValuationRing 𝒪[K]] [Finite 𝓀[K]]`; but a complete discretely-valued
field with finite residue field *is* locally compact
(`Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField`
gives properness, and proper metric spaces are locally compact). Factored out of
`henselianLocalRing_of_valuationSubring` so that `isAdicComplete_of_valuationSubring` can reuse
the same derivation without duplicating it; kept `private` since it is an intermediate step, not
a fact either downstream consumer states directly. -/
private instance isNonarchimedeanLocalField_of_valuationSubring
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
    [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
    [IsDiscreteValuationRing ↥(valuation K).valuationSubring]
    [Finite (IsLocalRing.ResidueField ↥(valuation K).valuationSubring)] :
    IsNonarchimedeanLocalField K := by
  haveI hvt : IsValuativeTopology K :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := K))
      (fun {s} => (NormedField.toValued (K := K)).is_topological_valuation s)
  haveI hnt : ValuativeRel.IsNontrivial K := by
    rw [ValuativeRel.isNontrivial_iff_isNontrivial (ValuativeRel.valuation K)]
    by_contra hn
    have htop := (Valuation.valuationSubring_eq_top_iff (ValuativeRel.valuation K)).mpr hn
    have hnf := IsDiscreteValuationRing.not_isField
      (R := ↥(ValuativeRel.valuation K).valuationSubring)
    apply hnf
    rw [htop]
    exact Field.toIsField _
  haveI hlc : LocallyCompactSpace K := by
    haveI : (Valued.v : Valuation K NNReal).RankOne :=
      inferInstanceAs (Valuation.RankOne (NormedField.valuation (K := K)))
    have hequiv : (NormedField.valuation (K := K)).IsEquiv (ValuativeRel.valuation K) :=
      ValuativeRel.isEquiv (NormedField.valuation (K := K)) (ValuativeRel.valuation K)
    have hsub : (NormedField.valuation (K := K)).valuationSubring
        = (ValuativeRel.valuation K).valuationSubring :=
      (Valuation.isEquiv_iff_valuationSubring _ _).mp hequiv
    have hdvr : IsDiscreteValuationRing ↥(NormedField.valuation (K := K)).valuationSubring := by
      rw [hsub]; infer_instance
    have hfin : Finite (IsLocalRing.ResidueField ↥(NormedField.valuation (K := K)).valuationSubring) := by
      rw [hsub]; infer_instance
    have hproper :=
      (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
          (K := K)).mpr ⟨inferInstance, hdvr, hfin⟩
    have : LocallyCompactSpace K :=
      @locallyCompact_of_proper K (Valued.toNormedField K NNReal).toPseudoMetricSpace hproper
    exact this
  exact ⟨⟩

/-- The ring of integers of a *lighter-bundle* complete discretely-valued field is Henselian,
provided its residue field is finite. See `isNonarchimedeanLocalField_of_valuationSubring` for how
`IsNonarchimedeanLocalField K` is derived from the lighter bundle; this then reuses the existing
`henselianLocalRing` instance. -/
instance henselianLocalRing_of_valuationSubring
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
    [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
    [IsDiscreteValuationRing ↥(valuation K).valuationSubring]
    [Finite (IsLocalRing.ResidueField ↥(valuation K).valuationSubring)] :
    HenselianLocalRing ↥(valuation K).valuationSubring :=
  (henselianLocalRing K : HenselianLocalRing ↥(valuation K).valuationSubring)

/-- The ring of integers of a *lighter-bundle* complete discretely-valued field is
`(maximalIdeal)`-adically complete, provided its residue field is finite. Same derivation as
`henselianLocalRing_of_valuationSubring`, transporting the plain `isAdicComplete` instance instead
of `henselianLocalRing` across the same `↥(𝒪[K]) ≡ ↥(valuation K).valuationSubring` identification
(both unfold to `{x // (valuation K) x ≤ 1}`: `Valuation.valuationSubring` is literally
`{v.integer with mem_or_inv_mem' := ..}`, i.e. `𝒪[K] = Valuation.integer (valuation K)` is the
`Subring` underlying `(valuation K).valuationSubring`, so the type ascription below is a defeq
cast, not a genuine transport lemma). This is the instance
`PowerSeries.exists_isWeierstrassFactorization` needs by name — `HenselianLocalRing` alone is not
a substitute, since Mathlib's Weierstrass preparation is stated for `IsAdicComplete`, not for
merely-Henselian rings. -/
instance isAdicComplete_of_valuationSubring
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
    [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
    [IsDiscreteValuationRing ↥(valuation K).valuationSubring]
    [Finite (IsLocalRing.ResidueField ↥(valuation K).valuationSubring)] :
    IsAdicComplete (IsLocalRing.maximalIdeal ↥(valuation K).valuationSubring)
      ↥(valuation K).valuationSubring :=
  (isAdicComplete K :
    IsAdicComplete (IsLocalRing.maximalIdeal ↥(valuation K).valuationSubring)
      ↥(valuation K).valuationSubring)

/-! ### A monic lift of a minimal polynomial over a Henselian local ring -/

/-- Let `R` be a Henselian local ring with residue field `k := IsLocalRing.ResidueField R`, and let
`β₀` be an element of a `k`-algebra field `l`, integral over `k`. Then `minpoly k β₀` lifts to a
monic polynomial over `R` of the same degree. Only surjectivity of the residue map is used
(`Polynomial.mem_lifts_of_surjective`, `Polynomial.lifts_and_natDegree_eq_and_monic`), so the
hypothesis is `[IsLocalRing R]` rather than `[HenselianLocalRing R]`: the name is kept in the
`HenselianLocalRing` namespace for continuity with its call sites, all of which do carry the
Henselian instance, but `Langlands.HenselianResidueLift` applies it to a *base* ring for which only
locality is available. -/
theorem HenselianLocalRing.exists_monic_lift_minpoly {R : Type*} [CommRing R]
    [IsLocalRing R] {l : Type*} [Field l] [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
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

/-! ### Irreducibility of the monic lift -/

/-- A monic lift `f` of `minpoly k β₀`, `k := IsLocalRing.ResidueField R`, is irreducible in `R[X]`:
its image under the residue map is `minpoly k β₀`, irreducible since `β₀` is integral over the field
`k`, and a monic polynomial over a domain is irreducible as soon as some image of it in a domain is
(`Polynomial.Monic.irreducible_of_irreducible_map`). Only `IsDomain R` is needed. This `R[X]`-level
statement, rather than its image over `Frac R`, is what `isDomain_adjoinRoot_lift_minpoly` consumes,
via `Irreducible f → Prime f` in the unique factorization monoid `R[X]`. -/
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

/-- The image of a monic lift `f` of `minpoly k β₀` in `K[X]`, `K` a fraction field of `R`, is
irreducible. Gauss's lemma for integrally closed domains
(`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`) applied to
`irreducible_lift_minpoly`; this is what makes `f` cut out a finite field extension of `K`. -/
theorem HenselianLocalRing.irreducible_map_lift_minpoly {R : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [HenselianLocalRing R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] {l : Type*} [Field l] [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀) :
    Irreducible (f.map (algebraMap R K)) :=
  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map hf).mp
    (HenselianLocalRing.irreducible_lift_minpoly hβ₀ hf hfmap)

/-! ### Separability of the monic lift

For a monic polynomial, separability is unit-ness of the resultant of the polynomial and its
derivative: `Polynomial.separable_def` identifies `f.Separable` with `IsCoprime f (derivative f)`,
and `Polynomial.isUnit_resultant_iff_isCoprime` identifies the latter with
`IsUnit (f.resultant (derivative f))`. Up to a sign and a leading-coefficient factor this resultant
is the discriminant, but only the resultant carries the `map`-compatibility lemma
`Polynomial.resultant_map_map` used to move the statement between `R` and its residue field. -/

/-- The monic lift `f` of `minpoly k β₀` has unit resultant with its own derivative, in `R` itself
rather than only after reduction to the residue field `k := IsLocalRing.ResidueField R`.

`k` is finite, hence perfect, so the irreducible `minpoly k β₀` is separable; by `hfmap` this makes
the resultant of `f.map (residue R)` and its derivative a unit in `k`. Transporting that back along
`residue R` needs care with `Polynomial.resultant`'s explicit size parameters, since reduction mod
the maximal ideal can lower the degree of `derivative f`: as `f` is monic,
`Polynomial.resultant_add_right_deg` shows the resultant is unchanged by padding the second size
parameter, so it may be read at the size coming from `R`, where `Polynomial.resultant_map_map`
applies. In a local ring, being a unit modulo the maximal ideal is being a unit.

This is the "discriminant is a unit" hypothesis `hunit` of
`Algebra.adjoin_eq_top_of_isUnit_aeval_derivative_minpoly`
(`Langlands.MonogenicMaximalOrder`), which
`Polynomial.isUnit_aeval_derivative_of_isUnit_resultant` transfers to a root of `f`. It is stated
separately from `separable_lift_minpoly` because both consumers need it. -/
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

/-- The monic lift `f` of `minpoly k β₀` is separable, when the residue field
`k := IsLocalRing.ResidueField R` is finite: `isUnit_resultant_lift_minpoly` composed with
`Polynomial.isUnit_resultant_iff_isCoprime` and `Polynomial.separable_def`. -/
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

/-- The image `f.map (algebraMap R K)` of the monic lift is separable in `K[X]`, for any
`R`-algebra field `K`: `Polynomial.Separable.map` transports separability along any ring hom. At a
root `x` of this image, it gives `IsSeparable K x`, hence separability of `K⟮x⟯ / K`, one of the
hypotheses of `Algebra.adjoin_eq_top_of_isUnit_aeval_derivative_minpoly`. -/
theorem HenselianLocalRing.separable_map_lift_minpoly {R : Type*} [CommRing R] [IsLocalRing R]
    [Finite (IsLocalRing.ResidueField R)] {K : Type*} [Field K] [Algebra R K] {l : Type*} [Field l]
    [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀) :
    (f.map (algebraMap R K)).Separable :=
  (HenselianLocalRing.separable_lift_minpoly hβ₀ hf hfmap).map

/-! ### Transferring "the discriminant is a unit" to a root

Factoring `f.map (algebraMap R C) = (X - C x) * q` at a root `x` (`Polynomial.dvd_iff_isRoot`) and
using multiplicativity of the resultant in its first argument (`Polynomial.resultant_mul_left`)
together with `Res(X - x, g) = g(x)` (`Polynomial.resultant_X_sub_C_left`) gives

`(algebraMap R C) (Res(f, f')) = Res(f.map .., f'.map ..) = f'(x) * Res(q, f'.map ..)`,

so a unit on the left forces `f'(x)` to be a unit. `Polynomial.resultant_map_map` is used here at
the size parameters coming from `R`, so no padding argument is needed. -/

/-- If `f : R[X]` is monic with `IsUnit (f.resultant (derivative f))` — e.g. by
`HenselianLocalRing.isUnit_resultant_lift_minpoly` — and `x : C` is a root of `f` in a domain
`R`-algebra `C`, then `aeval x (derivative f)` is a unit in `C`. -/
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

/-! ### The structure of `AdjoinRoot f`

For `f` a monic lift of `minpoly k β₀`, `k := IsLocalRing.ResidueField R`, the ring
`AdjoinRoot f` is a domain, free of rank `f.natDegree` over `R` — equal to `[l : k]` when `β₀` is a
primitive element of `l / k` — and local, with maximal ideal
`Ideal.map (AdjoinRoot.of f) (maximalIdeal R)`.

The primitive-element hypothesis is phrased as `IntermediateField.adjoin k {β₀} = ⊤`, avoiding the
scoped `⟮⟯` notation. -/

/-- `AdjoinRoot f` is a domain: `f` is irreducible in `R[X]` by `irreducible_lift_minpoly`, hence
prime, `R[X]` being a unique factorization monoid. -/
theorem HenselianLocalRing.isDomain_adjoinRoot_lift_minpoly {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [HenselianLocalRing R] {l : Type*} [Field l]
    [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀) :
    IsDomain (AdjoinRoot f) :=
  AdjoinRoot.isDomain_of_prime <| UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (HenselianLocalRing.irreducible_lift_minpoly hβ₀ hf hfmap)

/-- `AdjoinRoot f` is free of rank `f.natDegree` over `R` (`AdjoinRoot.powerBasis'`, needing only
that `f` is monic), and that rank is `[l : k]` when `β₀` is a primitive element of `l / k`:
`f.natDegree = (minpoly k β₀).natDegree = finrank k k⟮β₀⟯ = finrank k l`. -/
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

/-- The ideal `M₀ := Ideal.map (AdjoinRoot.of f) (maximalIdeal R)` is maximal in `AdjoinRoot f`:
the quotient by it is `AdjoinRoot (minpoly k β₀)` (`AdjoinRoot.quotEquivQuotMap` and `hfmap`), a
field since `minpoly k β₀` is irreducible. Stated separately from
`isLocalRing_adjoinRoot_lift_minpoly` so that `residueField_equiv_adjoinRoot_lift_minpoly` can use
it to identify `M₀` with `maximalIdeal (AdjoinRoot f)`; this step alone does not need
`IsDomain R`. -/
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

/-- `AdjoinRoot f` is local, with `M₀ := Ideal.map (AdjoinRoot.of f) (maximalIdeal R)` its unique
maximal ideal. `M₀` is maximal by `isMaximal_map_of_lift_minpoly`, and every maximal ideal of the
module-finite, hence integral, extension `AdjoinRoot f / R` contracts to the maximal ideal of the
local ring `R` (`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`), hence contains `M₀` and, both
being maximal, equals it. -/
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

/-! ### The residue field of `AdjoinRoot f`

Given the primitive-element hypothesis `hprim : k⟮β₀⟯ = ⊤` and locality of `AdjoinRoot f`, the
residue field of `AdjoinRoot f` is `l` itself. The composition is

`ResidueField (AdjoinRoot f) = AdjoinRoot f ⧸ M₀ ≃+* AdjoinRoot (minpoly k β₀) ≃ₐ[k] k⟮β₀⟯ = l`,

using `isMaximal_map_of_lift_minpoly` and `IsLocalRing.eq_maximalIdeal` for the first identification,
`AdjoinRoot.quotEquivQuotMap` with `hfmap` for the second, and
`IntermediateField.adjoinRootEquivAdjoin`, `IntermediateField.equivOfEq hprim`,
`IntermediateField.topEquiv` for the third.

`IsLocalRing.ResidueField R` and `AdjoinRoot p` are definitionally quotient rings, but carry their
own `CommRing` instances rather than the bundled `Ideal.Quotient.commRing`. Composing `RingEquiv`s
across that boundary elaborates the crossing as an opaque cast, after which `rw`/`simp` through
`RingEquiv.trans_apply` fails with "target expression is not type-correct under the `instances`
transparency level". The three `id`-based bridges below make each such crossing transparent, so the
composite can be evaluated point-wise by `simp`.

The identification is landed as a `RingEquiv` rather than a `k`-algebra equivalence: the latter
would first need a `k`-algebra structure on `IsLocalRing.ResidueField (AdjoinRoot f)`, which is not
needed elsewhere in this file. -/

/-- `Polynomial R ⧸ span {p}` and `AdjoinRoot p` are the same ring, as a transparent `RingEquiv`
(`toFun`, `invFun := id`). `AdjoinRoot p` is defined as that quotient but carries its own `CommRing`
instance, so composing equivalences through the raw quotient otherwise produces an opaque cast; see
the section note above. -/
def AdjoinRoot.quotSpanRingEquiv {R : Type*} [CommRing R] (p : R[X]) :
    (Polynomial R ⧸ (Ideal.span {p} : Ideal R[X])) ≃+* AdjoinRoot p where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem AdjoinRoot.quotSpanRingEquiv_apply {R : Type*} [CommRing R] (p : R[X])
    (x : Polynomial R ⧸ (Ideal.span {p} : Ideal R[X])) :
    AdjoinRoot.quotSpanRingEquiv p x = x := rfl

/-- `IsLocalRing.ResidueField R` and `R ⧸ maximalIdeal R` are the same ring, as a transparent
`RingEquiv`: the same kind of bridge as `AdjoinRoot.quotSpanRingEquiv`, for crossings from a generic
`R ⧸ I` statement such as `Ideal.quotEquivOfEq`'s into the named `ResidueField R`. -/
def IsLocalRing.ResidueField.quotEquivRaw {R : Type*} [CommRing R] [IsLocalRing R] :
    IsLocalRing.ResidueField R ≃+* R ⧸ IsLocalRing.maximalIdeal R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem IsLocalRing.ResidueField.quotEquivRaw_apply {R : Type*} [CommRing R] [IsLocalRing R]
    (x : IsLocalRing.ResidueField R) : IsLocalRing.ResidueField.quotEquivRaw x = x := rfl

/-- `Polynomial (R ⧸ maximalIdeal R)` and `Polynomial (IsLocalRing.ResidueField R)` are the same
ring, as a transparent `RingEquiv`. The two `CommRing` instances on the residue field are
`rfl`-equal, but the polynomial semirings built on them differ enough that stating an equality of
ideals across them and rewriting through it fails; this bridge lets proofs cross the boundary by
`simp` instead. -/
def IsLocalRing.ResidueField.polyQuotEquivRaw {R : Type*} [CommRing R] [IsLocalRing R] :
    Polynomial (R ⧸ IsLocalRing.maximalIdeal R) ≃+* Polynomial (IsLocalRing.ResidueField R) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem IsLocalRing.ResidueField.polyQuotEquivRaw_apply {R : Type*} [CommRing R] [IsLocalRing R]
    (x : Polynomial (R ⧸ IsLocalRing.maximalIdeal R)) :
    IsLocalRing.ResidueField.polyQuotEquivRaw x = x := rfl

/-- The residue field of `AdjoinRoot f` is `l`, for `f` a monic lift of `minpoly k β₀` and `β₀` a
primitive element of `l / k`. See the section note above for the composition. -/
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
  -- `hfmap` is stated over `k := IsLocalRing.ResidueField R`, whereas `AdjoinRoot.quotEquivQuotMap`
  -- emits its target ideal over the raw quotient `R ⧸ maximalIdeal R`. Crossing between the two by
  -- a bare ideal equality elaborates as a term but breaks later `rw`/`simp` reasoning through
  -- `RingEquiv.trans_apply`; route it through `polyQuotEquivRaw` and `Ideal.quotientEquiv`, which
  -- carries its own `_mk` application lemma.
  have helem : minpoly (IsLocalRing.ResidueField R) β₀ =
      IsLocalRing.ResidueField.polyQuotEquivRaw
        (f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))) := by
    rw [IsLocalRing.ResidueField.polyQuotEquivRaw_apply]
    exact hfmap.symm
  have hIJ : Ideal.span ({minpoly (IsLocalRing.ResidueField R) β₀} :
        Set (Polynomial (IsLocalRing.ResidueField R))) =
      Ideal.map (↑(IsLocalRing.ResidueField.polyQuotEquivRaw (R := R)) :
          Polynomial (R ⧸ IsLocalRing.maximalIdeal R) →+* Polynomial (IsLocalRing.ResidueField R))
        (Ideal.span ({f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))} :
          Set (Polynomial (R ⧸ IsLocalRing.maximalIdeal R)))) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun p => Ideal.span ({p} : Set (Polynomial (IsLocalRing.ResidueField R))))
      helem
  exact RingEquiv.trans
    (IsLocalRing.ResidueField.quotEquivRaw.trans (Ideal.quotEquivOfEq hM0eq).symm)
    (RingEquiv.trans (AdjoinRoot.quotEquivQuotMap f (IsLocalRing.maximalIdeal R)).toRingEquiv
      (RingEquiv.trans
        (Ideal.quotientEquiv _ _ IsLocalRing.ResidueField.polyQuotEquivRaw hIJ)
        (RingEquiv.trans
          (AdjoinRoot.quotSpanRingEquiv (minpoly (IsLocalRing.ResidueField R) β₀))
          (AlgEquiv.toRingEquiv
            (AlgEquiv.trans
              (AlgEquiv.trans
                (IntermediateField.adjoinRootEquivAdjoin (IsLocalRing.ResidueField R) hβ₀)
                (IntermediateField.equivOfEq hprim))
              IntermediateField.topEquiv)))))

/-- `residueField_equiv_adjoinRoot_lift_minpoly` sends the residue of the canonical generator
`AdjoinRoot.root f` to `β₀`, identifying which point of `l` that residue class corresponds to rather
than only that the two residue fields are abstractly isomorphic. Used by
`exists_isDiscreteValuationRing_integralClosure_residueField_equiv` to track a chosen generator's
residue through the equivalence. -/
theorem HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly_apply_residue_root
    {R : Type*} [CommRing R] [HenselianLocalRing R] {l : Type*} [Field l]
    [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀)
    (hprim : IntermediateField.adjoin (IsLocalRing.ResidueField R) {β₀} = ⊤)
    [IsLocalRing (AdjoinRoot f)] :
    HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly hβ₀ hf hfmap hprim
      (IsLocalRing.residue (AdjoinRoot f) (AdjoinRoot.root f)) = β₀ := by
  unfold HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly
  show _ = β₀
  rw [show IsLocalRing.residue (AdjoinRoot f) (AdjoinRoot.root f) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (AdjoinRoot f)) (AdjoinRoot.root f) from rfl,
    ← AdjoinRoot.mk_X]
  simp only [RingEquiv.trans_apply, IsLocalRing.ResidueField.quotEquivRaw_apply,
    Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk, AlgEquiv.coe_ringEquiv,
    AdjoinRoot.quotEquivQuotMap_apply_mk, Polynomial.map_X, Ideal.quotientEquiv_mk,
    IsLocalRing.ResidueField.polyQuotEquivRaw_apply, AdjoinRoot.quotSpanRingEquiv_apply]
  show (((IntermediateField.adjoinRootEquivAdjoin (IsLocalRing.ResidueField R) hβ₀).trans
        (IntermediateField.equivOfEq hprim)).trans IntermediateField.topEquiv)
      (AdjoinRoot.root (minpoly (IsLocalRing.ResidueField R) β₀)) = β₀
  simp only [AlgEquiv.trans_apply, IntermediateField.adjoinRootEquivAdjoin_apply_root,
    IntermediateField.equivOfEq_apply, IntermediateField.topEquiv_apply,
    IntermediateField.AdjoinSimple.coe_gen]

/-- `residueField_equiv_adjoinRoot_lift_minpoly` is compatible with the structure maps from `R`: it
sends the residue of `algebraMap R (AdjoinRoot f) c` to the image of `residue R c` under
`algebraMap k l`. This is the `he`-shaped compatibility needed to instantiate
`TowerMonogenicConcrete.algebraMap_eq_of_ringEquiv_of_forall` from the residue isomorphism this file
constructs, without an extra hypothesis. Proved by the same unwinding as
`residueField_equiv_adjoinRoot_lift_minpoly_apply_residue_root`, with the constant `Polynomial.C c`
in place of the generator `X`. -/
theorem HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly_apply_residue_algebraMap
    {R : Type*} [CommRing R] [HenselianLocalRing R] {l : Type*} [Field l]
    [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀) {f : R[X]} (hf : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀)
    (hprim : IntermediateField.adjoin (IsLocalRing.ResidueField R) {β₀} = ⊤)
    [IsLocalRing (AdjoinRoot f)] (c : R) :
    HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly hβ₀ hf hfmap hprim
      (IsLocalRing.residue (AdjoinRoot f) (algebraMap R (AdjoinRoot f) c)) =
      algebraMap (IsLocalRing.ResidueField R) l (IsLocalRing.residue R c) := by
  unfold HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly
  show _ = algebraMap (IsLocalRing.ResidueField R) l (IsLocalRing.residue R c)
  have hac : algebraMap R (AdjoinRoot f) c = AdjoinRoot.mk f (Polynomial.C c) := rfl
  rw [show IsLocalRing.residue (AdjoinRoot f) (algebraMap R (AdjoinRoot f) c) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (AdjoinRoot f))
        (algebraMap R (AdjoinRoot f) c) from rfl, hac]
  simp only [RingEquiv.trans_apply, IsLocalRing.ResidueField.quotEquivRaw_apply,
    Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk, AlgEquiv.coe_ringEquiv,
    AdjoinRoot.quotEquivQuotMap_apply_mk, Polynomial.map_C, Ideal.quotientEquiv_mk,
    IsLocalRing.ResidueField.polyQuotEquivRaw_apply, AdjoinRoot.quotSpanRingEquiv_apply]
  show (((IntermediateField.adjoinRootEquivAdjoin (IsLocalRing.ResidueField R) hβ₀).trans
        (IntermediateField.equivOfEq hprim)).trans IntermediateField.topEquiv)
      (AdjoinRoot.mk (minpoly (IsLocalRing.ResidueField R) β₀)
        (Polynomial.C (algebraMap R (IsLocalRing.ResidueField R) c))) =
      algebraMap (IsLocalRing.ResidueField R) l (IsLocalRing.residue R c)
  have hacc : AdjoinRoot.mk (minpoly (IsLocalRing.ResidueField R) β₀)
      (Polynomial.C (algebraMap R (IsLocalRing.ResidueField R) c)) =
      algebraMap (IsLocalRing.ResidueField R)
        (AdjoinRoot (minpoly (IsLocalRing.ResidueField R) β₀))
        (algebraMap R (IsLocalRing.ResidueField R) c) := rfl
  rw [hacc]
  simp only [AlgEquiv.commutes]
  rfl

/-! ### Embedding `AdjoinRoot (f.map (algebraMap R K))` into an algebraically closed extension -/

/-- For `L / K` algebraically closed, the polynomial `p := f.map (algebraMap R K)` — irreducible by
`irreducible_map_lift_minpoly`, of positive degree since `f.natDegree = (minpoly k β₀).natDegree` —
has a root `x : L`, and `AdjoinRoot.lift` embeds `AdjoinRoot p` into `L` over `K`, carrying the
canonical root to `x`. The embedding is injective because `AdjoinRoot p` is a field. This realizes
the fraction field of `AdjoinRoot f` as the subfield `K⟮x⟯` of `L`; the corresponding statement for
`AdjoinRoot f` itself is `injective_comp_adjoinRootMap` below. -/
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

/-! ### Base change `AdjoinRoot f →+* AdjoinRoot (f.map (algebraMap R K))`

Base change along `R → K` gives a natural, injective ring hom between the two quotients. Composed
with the embedding of the previous section it realizes `AdjoinRoot f` itself, and not merely its
fraction field, as a subring of `L`. -/

/-- `f` evaluates to `0` under the composite `R → K → AdjoinRoot p` at `AdjoinRoot.root p`, where
`p := f.map (algebraMap R K)`. This is the side condition `AdjoinRoot.lift` needs in order to
produce `adjoinRootMap`. -/
theorem HenselianLocalRing.eval₂_root_map {R : Type*} [CommRing R] {K : Type*} [Field K]
    [Algebra R K] (f : R[X]) :
    Polynomial.eval₂ ((AdjoinRoot.of (f.map (algebraMap R K))).comp (algebraMap R K))
      (AdjoinRoot.root (f.map (algebraMap R K))) f = 0 := by
  rw [← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root _

/-- The natural ring hom `AdjoinRoot f →+* AdjoinRoot p`, `p := f.map (algebraMap R K)`, sending
`AdjoinRoot.root f` to `AdjoinRoot.root p`, induced by `AdjoinRoot.lift` along the composite
`R → K → AdjoinRoot p`. -/
noncomputable def HenselianLocalRing.adjoinRootMap {R : Type*} [CommRing R] {K : Type*} [Field K]
    [Algebra R K] (f : R[X]) : AdjoinRoot f →+* AdjoinRoot (f.map (algebraMap R K)) :=
  AdjoinRoot.lift ((AdjoinRoot.of (f.map (algebraMap R K))).comp (algebraMap R K))
    (AdjoinRoot.root (f.map (algebraMap R K))) (HenselianLocalRing.eval₂_root_map f)

/-- `adjoinRootMap` sends `AdjoinRoot.mk f g` to `AdjoinRoot.mk p (g.map (algebraMap R K))`, where
`p := f.map (algebraMap R K)`. -/
theorem HenselianLocalRing.adjoinRootMap_mk {R : Type*} [CommRing R] {K : Type*} [Field K]
    [Algebra R K] (f g : R[X]) :
    HenselianLocalRing.adjoinRootMap (K := K) f (AdjoinRoot.mk f g) =
      AdjoinRoot.mk (f.map (algebraMap R K)) (g.map (algebraMap R K)) := by
  show AdjoinRoot.lift _ _ (HenselianLocalRing.eval₂_root_map f) (AdjoinRoot.mk f g) = _
  rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def,
    AdjoinRoot.aeval_eq]

/-- `adjoinRootMap` is injective, for `R` a domain, `f` monic and `K` a fraction field of `R`:
`AdjoinRoot.mk_eq_zero` reduces vanishing to divisibility, and `Polynomial.map_dvd_map` gives
`f.map (algebraMap R K) ∣ g.map (algebraMap R K) ↔ f ∣ g`. -/
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

/-- The composite `AdjoinRoot f →+* AdjoinRoot p →+* L` of `adjoinRootMap` with the embedding `φ` of
`exists_ringHom_adjoinRoot_map_of_isAlgClosed` is injective, realizing `AdjoinRoot f` itself, and
not merely its fraction field, as a subring of `L`. -/
theorem HenselianLocalRing.injective_comp_adjoinRootMap {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {f : R[X]} (hf : f.Monic)
    {L : Type*} [Field L] {φ : AdjoinRoot (f.map (algebraMap R K)) →+* L}
    (hφ : Function.Injective φ) :
    Function.Injective (φ.comp (HenselianLocalRing.adjoinRootMap (K := K) f)) :=
  hφ.comp (HenselianLocalRing.injective_adjoinRootMap hf)

/-! ### The unramified extension of `K` with prescribed residue extension

Let `x : L` be the root of `f` produced by `exists_ringHom_adjoinRoot_map_of_isAlgClosed`, and set
`K' := K⟮x⟯` and `C := integralClosure R K'`. Then `x` is a root of the monic `f` itself, hence
integral over `R`, giving `x' : C`, and:

* `Algebra.adjoin K {x'} = ⊤` as a `Subalgebra K K'`, by transporting
  `IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic` from `L` down along the injective
  inclusion `K' →ₐ[K] L`.
* `f.map (algebraMap R K) = minpoly K x` (`minpoly.eq_of_irreducible`, both being monic), so
  `separable_map_lift_minpoly` gives `IsSeparable K x` and hence `Algebra.IsSeparable K K'`.
* `Algebra.adjoin R {x'} = ⊤` as a `Subalgebra R C`, i.e. `C` is monogenic, by
  `Algebra.adjoin_eq_top_of_isUnit_aeval_derivative_minpoly`
  (`Langlands.MonogenicMaximalOrder`), whose `hunit` hypothesis comes from
  `isUnit_resultant_lift_minpoly` and `Polynomial.isUnit_aeval_derivative_of_isUnit_resultant`.
  Monogenicity makes `AdjoinRoot f →+* C` bijective, transporting the locality and residue-field
  computations of the previous sections to `C`.
* `C` is a Dedekind domain (`integralClosure.isDedekindDomain`, using separability), local, and not
  a field, hence a discrete valuation ring by `IsDiscreteValuationRing.TFAE`.

The residue-field equivalence `e : ResidueField C ≃+* l` in the conclusion is accompanied by two
facts: it carries the residue class of any `y : C` lying over `x` to `β₀` (such a `y` is forced to
equal `x'`, and `e (residue C x')` unwinds to
`residueField_equiv_adjoinRoot_lift_minpoly_apply_residue_root`), and it is compatible with the two
algebra maps from `ResidueField R`, i.e. `e (residue C (algebraMap R C c)) = algebraMap (ResidueField
R) l (residue R c)` for every `c : R` (via `residueField_equiv_adjoinRoot_lift_minpoly_apply_residue_
algebraMap` and `hψof`, the same transport as the root case). This second fact is exactly the `he`
hypothesis `LocalField.algebraMap_eq_of_ringEquiv_of_forall`
(`Langlands/TowerMonogenicConcrete.lean`) needs, so callers no longer have to establish it
separately. -/

/-- **Existence of an unramified extension with prescribed residue extension.** Let `R` be a
Henselian discrete valuation ring with fraction field `K` and finite residue field `k`, let `L / K`
be algebraically closed, let `β₀` be an element of a `k`-algebra field `l`, integral over `k` and
generating `l` over `k`, and let `f : R[X]` be a monic lift of `minpoly k β₀`. Then `f` has a root
`x : L`, integral over `R`, with `f.map (algebraMap R K) = minpoly K x`, such that `K⟮x⟯ / K` is
separable and the integral closure `C` of `R` in `K⟮x⟯` is a discrete valuation ring whose residue
field is isomorphic to `l`, by an isomorphism carrying the residue class of any element of `C` lying
over `x` to `β₀`.

Two further conclusions record that `C / R` is *unramified and monogenic*, in the form Serre's
tower argument for monogenicity of `𝒪_L / 𝒪_K` consumes:

* `∃ β : C, Algebra.adjoin R {β} = ⊤` — `C = R[β]` (the witness is the element of `C` over `x`);
* `Ideal.map (algebraMap R C) (maximalIdeal R) = maximalIdeal C` — `𝔪_R · C = 𝔪_C`.

Both are transported from the `AdjoinRoot f` model along the isomorphism `ψ : AdjoinRoot f ≃+* C`
built in the proof; the first is `Algebra.adjoin_eq_top_of_isUnit_aeval_derivative_minpoly` applied
to `C` directly, the second is `isMaximal_map_of_lift_minpoly` pushed across `ψ`.

A standalone result: it is not used in the proof of
`ValuationSubring.exists_restrictNormalHom_decompositionSubgroup_surjective`, which obtains roots
with prescribed residues from `ValuationSubring.exists_aeval_root_residue_eq` instead. The root `x`
here is an arbitrary choice among the conjugates of the lift, so it does not on its own pin down a
residue in a prescribed valuation subring of `L`. -/
theorem HenselianLocalRing.exists_isDiscreteValuationRing_integralClosure_residueField_equiv
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain R]
    [IsDiscreteValuationRing R] [HenselianLocalRing R] [Finite (IsLocalRing.ResidueField R)]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosed L]
    {l : Type*} [Field l] [Algebra (IsLocalRing.ResidueField R) l] {β₀ : l}
    (hβ₀ : IsIntegral (IsLocalRing.ResidueField R) β₀)
    {f : R[X]} (hfmonic : f.Monic)
    (hfmap : f.map (algebraMap R (IsLocalRing.ResidueField R)) =
      minpoly (IsLocalRing.ResidueField R) β₀)
    (hprim : IntermediateField.adjoin (IsLocalRing.ResidueField R) {β₀} = ⊤) :
    ∃ x : L, ∃ _hxint : IsIntegral R x,
      f.map (algebraMap R K) = minpoly K x ∧
      Algebra.IsSeparable K ↥(IntermediateField.adjoin K {x}) ∧
      ∃ hCloc : IsLocalRing ↥(integralClosure R (IntermediateField.adjoin K {x})),
        IsDiscreteValuationRing ↥(integralClosure R (IntermediateField.adjoin K {x})) ∧
        (∃ β : ↥(integralClosure R (IntermediateField.adjoin K {x})),
          Algebra.adjoin R
            ({β} : Set ↥(integralClosure R (IntermediateField.adjoin K {x}))) = ⊤) ∧
        Ideal.map (algebraMap R ↥(integralClosure R (IntermediateField.adjoin K {x})))
            (IsLocalRing.maximalIdeal R) =
          @IsLocalRing.maximalIdeal _ _ hCloc ∧
        ∃ e : @IsLocalRing.ResidueField _ _ hCloc ≃+* l,
          (∀ y : ↥(integralClosure R (IntermediateField.adjoin K {x})),
            algebraMap ↥(IntermediateField.adjoin K {x}) L
                (algebraMap ↥(integralClosure R (IntermediateField.adjoin K {x}))
                  ↥(IntermediateField.adjoin K {x}) y) = x →
              e (@IsLocalRing.residue _ _ hCloc y) = β₀) ∧
          ∀ c : R, e (@IsLocalRing.residue _ _ hCloc
              (algebraMap R ↥(integralClosure R (IntermediateField.adjoin K {x})) c)) =
            algebraMap (IsLocalRing.ResidueField R) l (IsLocalRing.residue R c) := by
  classical
  obtain ⟨x, φ, hφinj, hφroot, hφcomp⟩ :=
    HenselianLocalRing.exists_ringHom_adjoinRoot_map_of_isAlgClosed (R := R) (K := K) (L := L)
      hβ₀ hfmonic hfmap
  set K' : IntermediateField K L := IntermediateField.adjoin K {x} with hK'
  -- `x` is a root of `p := f.map (algebraMap R K)` over `K`.
  have hpx : Polynomial.aeval x (f.map (algebraMap R K)) = 0 := by
    have h := Polynomial.hom_eval₂ (f.map (algebraMap R K)) (AdjoinRoot.of (f.map (algebraMap R K)))
      φ (AdjoinRoot.root (f.map (algebraMap R K)))
    rw [AdjoinRoot.eval₂_root, map_zero, hφcomp, hφroot] at h
    rw [Polynomial.aeval_def]; exact h.symm
  -- Hence `x` is a root of the monic `f` itself, so `x` is integral over `R`.
  have hfx : Polynomial.aeval x f = 0 := by
    have := hpx
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      ← IsScalarTower.algebraMap_eq R K L, ← Polynomial.aeval_def] at this
    exact this
  have hxint : IsIntegral R x := ⟨f, hfmonic, hfx⟩
  have hxK : IsIntegral K x := hxint.tower_top
  have hK'fd : FiniteDimensional K K' := IntermediateField.adjoin.finiteDimensional hxK
  -- `p := f.map (algebraMap R K)` (monic, irreducible) is `minpoly K x`.
  have hpmonic : (f.map (algebraMap R K)).Monic := hfmonic.map _
  have hpirr : Irreducible (f.map (algebraMap R K)) :=
    HenselianLocalRing.irreducible_map_lift_minpoly (K := K) hβ₀ hfmonic hfmap
  have hminpoly_scaled :
      f.map (algebraMap R K) * Polynomial.C (f.map (algebraMap R K)).leadingCoeff⁻¹ =
        minpoly K x :=
    minpoly.eq_of_irreducible hpirr hpx
  have hminpoly : f.map (algebraMap R K) = minpoly K x := by
    rwa [hpmonic.leadingCoeff, inv_one, Polynomial.C_1, mul_one] at hminpoly_scaled
  -- `p` separable, hence `x` separable, hence `K'/K` separable.
  have hpsep : (f.map (algebraMap R K)).Separable :=
    HenselianLocalRing.separable_map_lift_minpoly hβ₀ hfmonic hfmap
  have hxsep : IsSeparable K x := by show (minpoly K x).Separable; rw [← hminpoly]; exact hpsep
  have hK'sep : Algebra.IsSeparable K K' :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K L (x := x)).mpr hxsep
  -- The generator `x' : K'` of `K'` over `K` generates the whole of `K'` as a `K`-algebra.
  set x' : K' := IntermediateField.AdjoinSimple.gen K x with hx'def
  have hincl_inj : Function.Injective (K'.val : K' →ₐ[K] L) := FaithfulSMul.algebraMap_injective K' L
  have htop_map : Subalgebra.map (K'.val : K' →ₐ[K] L) ⊤ = K'.toSubalgebra := by
    rw [Algebra.map_top]; exact IntermediateField.range_val K'
  have hadjoin_map :
      Subalgebra.map (K'.val : K' →ₐ[K] L) (Algebra.adjoin K ({x'} : Set K')) =
        K'.toSubalgebra := by
    rw [AlgHom.map_adjoin]
    have : (K'.val : K' →ₐ[K] L) '' ({x'} : Set K') = ({x} : Set L) := by
      simp [hx'def]
    rw [this, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hxK.isAlgebraic]
  have hx'top : Algebra.adjoin K ({x'} : Set K') = ⊤ :=
    Subalgebra.map_injective hincl_inj (hadjoin_map.trans htop_map.symm)
  -- `K'` already carries the canonical `R`-algebra structure `IntermediateField.algebra'`
  -- (compatible with `R → K → L`, via `[Algebra R L] [IsScalarTower R K L]`); the only missing
  -- piece is `IsScalarTower R K' L`, which holds by the same compatibility, definitionally.
  haveI hRK'L : IsScalarTower R K' L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- transfer the discriminant-unit fact from `f`/`R` to the root `x'` of `f` inside `C`.
  set C := integralClosure R K' with hCdef
  have hxL : (algebraMap K' L) (x' : K') = x := IntermediateField.AdjoinSimple.algebraMap_gen K x
  have hK'L_inj : Function.Injective (algebraMap K' L) := FaithfulSMul.algebraMap_injective K' L
  have hx'f : Polynomial.aeval (x' : K') f = 0 :=
    hK'L_inj (by rw [map_zero, ← Polynomial.aeval_algebraMap_apply L (x' : K') f, hxL]; exact hfx)
  have hx'Cint : IsIntegral R (x' : K') := ⟨f, hfmonic, hx'f⟩
  set xC : C := ⟨x', hx'Cint⟩ with hxCdef
  have hCK'_inj : Function.Injective (algebraMap C K') := FaithfulSMul.algebraMap_injective C K'
  have hxCroot : Polynomial.aeval xC f = 0 :=
    hCK'_inj (by
      rw [map_zero, ← Polynomial.aeval_algebraMap_apply K' xC f]
      show Polynomial.aeval (x' : K') f = 0
      exact hx'f)
  -- `f = minpoly R xC`: both, mapped to `K`, equal `minpoly K x` (via
  -- `minpoly.isIntegrallyClosed_eq_field_fractions` for the `minpoly R xC` side, `hminpoly` for
  -- the `f` side), and `Polynomial.map (algebraMap R K)` is injective.
  haveI hCfinite : Module.Finite R C := IsIntegralClosure.finite R K K' C
  haveI hCalgint : Algebra.IsIntegral R C := Algebra.IsIntegral.of_finite R C
  have hCxCintegral : IsIntegral R xC := hCalgint.isIntegral xC
  have hminpolyx' : minpoly K (x' : K') = minpoly K x := by
    have h := minpoly.algebraMap_eq (A := K) hK'L_inj (x' : K')
    rw [hxL] at h; exact h.symm
  have hfeqminpoly : f = minpoly R xC := by
    apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
    calc f.map (algebraMap R K) = minpoly K x := hminpoly
      _ = minpoly K (x' : K') := hminpolyx'.symm
      _ = minpoly K (algebraMap C K' xC) := rfl
      _ = Polynomial.map (algebraMap R K) (minpoly R xC) :=
          minpoly.isIntegrallyClosed_eq_field_fractions K K' hCxCintegral
  have hxCunit : IsUnit (Polynomial.aeval xC (minpoly R xC).derivative) := by
    rw [← hfeqminpoly]
    exact Polynomial.isUnit_aeval_derivative_of_isUnit_resultant hfmonic
      (HenselianLocalRing.isUnit_resultant_lift_minpoly hβ₀ hfmonic hfmap) hxCroot
  have hxadjoinK : Algebra.adjoin K {algebraMap C K' xC} = ⊤ := by
    rw [show algebraMap C K' xC = x' from rfl]; exact hx'top
  haveI hCdedekind : IsDedekindDomain C := integralClosure.isDedekindDomain R K K'
  have hK_inj : Function.Injective (algebraMap K K') := FaithfulSMul.algebraMap_injective K K'
  have hRK'_inj : Function.Injective (algebraMap R K') := by
    intro a b hab
    apply IsFractionRing.injective R K
    apply hK_inj
    rwa [IsScalarTower.algebraMap_apply R K K', IsScalarTower.algebraMap_apply R K K'] at hab
  have hRC_inj : Function.Injective (algebraMap R C) := by
    intro a b hab
    apply hRK'_inj
    have h := congrArg (algebraMap C K') hab
    rwa [← IsScalarTower.algebraMap_apply R C K', ← IsScalarTower.algebraMap_apply R C K'] at h
  haveI : Module.IsTorsionFree R C :=
    Module.IsTorsionFree.of_smul_eq_zero fun r c hrc => by
      have heq : algebraMap R C r * c = 0 := by rw [← Algebra.smul_def]; exact hrc
      rcases mul_eq_zero.mp heq with h | h
      · left; exact hRC_inj.eq_iff.mp (h.trans (map_zero (algebraMap R C)).symm)
      · right; exact h
  have hCtop : Algebra.adjoin R ({xC} : Set C) = ⊤ :=
    Algebra.adjoin_eq_top_of_isUnit_aeval_derivative_minpoly R K K' xC hxadjoinK hxCunit
  -- `AdjoinRoot f` surjects onto `C` (sending `root f ↦ xC`), by `hCtop`.
  have hxCroot' : Polynomial.eval₂ (algebraMap R C) xC f = 0 := by
    rw [← Polynomial.aeval_def]; exact hxCroot
  set ψ : AdjoinRoot f →+* C := AdjoinRoot.lift (algebraMap R C) xC hxCroot' with hψdef
  have hψsurj : Function.Surjective ψ := by
    intro c
    have hc : c ∈ Algebra.adjoin R ({xC} : Set C) := by rw [hCtop]; trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hc
    obtain ⟨q, hq⟩ := hc
    refine ⟨AdjoinRoot.mk f q, ?_⟩
    rw [hψdef, AdjoinRoot.lift_mk, ← Polynomial.aeval_def]
    exact hq
  -- `AdjoinRoot f → C ↪ K' ↪ L` agrees with the already-injective composite
  -- `φ ∘ adjoinRootMap f : AdjoinRoot f →+* L`, so `ψ` is injective too.
  set ψ₀ : AdjoinRoot f →+* L := φ.comp (HenselianLocalRing.adjoinRootMap (K := K) f) with hψ₀def
  have hψ₀inj : Function.Injective ψ₀ :=
    HenselianLocalRing.injective_comp_adjoinRootMap hfmonic hφinj
  have hψ₀root : ψ₀ (AdjoinRoot.root f) = x := by
    rw [hψ₀def, RingHom.comp_apply, HenselianLocalRing.adjoinRootMap, AdjoinRoot.lift_root, hφroot]
  have hcompeq : (algebraMap C L).comp ψ = ψ₀ := by
    apply AdjoinRoot.ringHom_ext
    · rw [RingHom.comp_assoc]
      have h1 : ψ.comp (AdjoinRoot.of f) = algebraMap R C := by
        rw [hψdef]; exact AdjoinRoot.lift_comp_of hxCroot'
      rw [h1, ← IsScalarTower.algebraMap_eq R C L, IsScalarTower.algebraMap_eq R K L]
      rw [hψ₀def, RingHom.comp_assoc]
      have h2 : (HenselianLocalRing.adjoinRootMap (K := K) f).comp (AdjoinRoot.of f) =
          (AdjoinRoot.of (f.map (algebraMap R K))).comp (algebraMap R K) := by
        rw [HenselianLocalRing.adjoinRootMap]; exact AdjoinRoot.lift_comp_of _
      rw [h2, ← RingHom.comp_assoc, hφcomp]
    · rw [RingHom.comp_apply]
      show algebraMap C L (ψ (AdjoinRoot.root f)) = ψ₀ (AdjoinRoot.root f)
      rw [hψ₀root, hψdef, AdjoinRoot.lift_root]
      show algebraMap K' L x' = x
      exact IntermediateField.AdjoinSimple.algebraMap_gen K x
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply hψ₀inj
    have h := congrArg (algebraMap C L) hab
    rwa [← RingHom.comp_apply, ← RingHom.comp_apply, hcompeq] at h
  set e : AdjoinRoot f ≃+* C := RingEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩ with hedef
  haveI hCdomain : IsDomain (AdjoinRoot f) :=
    HenselianLocalRing.isDomain_adjoinRoot_lift_minpoly hβ₀ hfmonic hfmap
  haveI hClocal : IsLocalRing (AdjoinRoot f) :=
    HenselianLocalRing.isLocalRing_adjoinRoot_lift_minpoly hβ₀ hfmonic hfmap
  haveI hCisLocalRing : IsLocalRing C := e.isLocalRing
  -- **Unramifiedness of `K' / K`, transported from the `AdjoinRoot f` model to `C`.** The maximal
  -- ideal of `AdjoinRoot f` is generated by that of `R` (the same derivation as in
  -- `residueField_equiv_adjoinRoot_lift_minpoly`); `ψ` is a ring isomorphism onto `C` commuting
  -- with the structure maps from `R`, so the same holds for `C`.
  have hM0eq : Ideal.map (AdjoinRoot.of f) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal (AdjoinRoot f) :=
    IsLocalRing.eq_maximalIdeal
      (HenselianLocalRing.isMaximal_map_of_lift_minpoly hβ₀ hfmonic hfmap)
  have hψof : ψ.comp (AdjoinRoot.of f) = algebraMap R C := by
    rw [hψdef]; exact AdjoinRoot.lift_comp_of hxCroot'
  have hCmapmax : Ideal.map (algebraMap R C) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal C := by
    rw [← hψof, ← Ideal.map_map, hM0eq]
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.IsMaximal.map_bijective ψ ⟨hψinj, hψsurj⟩ (IsLocalRing.maximalIdeal.isMaximal _))
  -- `C` is not a field: `algebraMap R C` is injective and `C` is integral over `R`, so the maximal
  -- ideal of `C` contracts to that of `R`, and `maximalIdeal C = ⊥` would force
  -- `maximalIdeal R = ⊥`, contradicting that `R` is a discrete valuation ring. Being a local
  -- Dedekind domain that is not a field, `C` is then a discrete valuation ring.
  have hCnotField : ¬ IsField C := by
    intro hfield
    have hCmax0 : IsLocalRing.maximalIdeal C = ⊥ :=
      (IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield
    haveI hCfinite : Module.Finite R C := IsIntegralClosure.finite R K K' C
    haveI : Algebra.IsIntegral R C := Algebra.IsIntegral.of_finite R C
    have hcomapmax : (IsLocalRing.maximalIdeal C).comap (algebraMap R C) =
        IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
    rw [hCmax0, Ideal.comap_bot_of_injective _ hRC_inj] at hcomapmax
    exact IsDiscreteValuationRing.not_isField R
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hcomapmax.symm)
  haveI hCdvr : IsDiscreteValuationRing C :=
    ((IsDiscreteValuationRing.TFAE C hCnotField).out 0 2).mpr hCdedekind
  have hCisLocalRing' : IsLocalRing ↥(integralClosure R (IntermediateField.adjoin K {x})) :=
    hCisLocalRing
  refine ⟨x, hxint, hminpoly, hK'sep, hCisLocalRing', hCdvr, ⟨xC, hCtop⟩, hCmapmax,
    (RingEquiv.symm (IsLocalRing.ResidueField.mapEquiv e) : _).trans
      (HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly hβ₀ hfmonic hfmap hprim),
    ?_, ?_⟩
  -- `e (root f) = xC`, unwinding `e := RingEquiv.ofBijective ψ _` and `ψ := AdjoinRoot.lift ... xC _`.
  have heroot : (e : AdjoinRoot f →+* ↥C) (AdjoinRoot.root f) = xC := by
    show ψ (AdjoinRoot.root f) = xC
    rw [hψdef, AdjoinRoot.lift_root]
  · intro y hy
    -- Any `y : C` mapping to `x` under `C → K' → L` is forced to equal the witness `xC`, since that
    -- composite is injective (it factors as the injective `algebraMap C K'` followed by the
    -- injective `algebraMap K' L`).
    have hyxC : y = xC := by
      apply hCK'_inj
      apply hK'L_inj
      rw [hy]
      show x = algebraMap K' L (x' : K')
      exact hxL.symm
    show (RingEquiv.symm (IsLocalRing.ResidueField.mapEquiv e) : _).trans
      (HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly hβ₀ hfmonic hfmap hprim)
      (IsLocalRing.residue C y) = β₀
    rw [hyxC, RingEquiv.trans_apply]
    have hstep : (IsLocalRing.ResidueField.mapEquiv e).symm (IsLocalRing.residue C xC) =
        IsLocalRing.residue (AdjoinRoot f) (AdjoinRoot.root f) := by
      apply (IsLocalRing.ResidueField.mapEquiv e).injective
      rw [RingEquiv.apply_symm_apply, IsLocalRing.ResidueField.mapEquiv_apply,
        IsLocalRing.ResidueField.map_residue, heroot]
    rw [hstep]
    exact HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly_apply_residue_root
      hβ₀ hfmonic hfmap hprim
  · -- **Compatibility with the algebra maps from `R`.** `e (algebraMap R C c) = algebraMap R
    -- (AdjoinRoot f) c` under `ψ`/`hψof`, so this reduces to the generalised residue lemma
    -- (`..._apply_residue_algebraMap`) exactly as the root case above reduces to
    -- `..._apply_residue_root`.
    intro c
    have hec : (e : AdjoinRoot f →+* ↥C) (algebraMap R (AdjoinRoot f) c) = algebraMap R C c := by
      show ψ (algebraMap R (AdjoinRoot f) c) = algebraMap R C c
      rw [AdjoinRoot.algebraMap_eq, ← RingHom.comp_apply, hψof]
    show (RingEquiv.symm (IsLocalRing.ResidueField.mapEquiv e) : _).trans
      (HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly hβ₀ hfmonic hfmap hprim)
      (IsLocalRing.residue C (algebraMap R C c)) =
      algebraMap (IsLocalRing.ResidueField R) l (IsLocalRing.residue R c)
    rw [RingEquiv.trans_apply]
    have hstep2 : (IsLocalRing.ResidueField.mapEquiv e).symm
        (IsLocalRing.residue C (algebraMap R C c)) =
        IsLocalRing.residue (AdjoinRoot f) (algebraMap R (AdjoinRoot f) c) := by
      apply (IsLocalRing.ResidueField.mapEquiv e).injective
      rw [RingEquiv.apply_symm_apply, IsLocalRing.ResidueField.mapEquiv_apply,
        IsLocalRing.ResidueField.map_residue, hec]
    rw [hstep2]
    exact HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly_apply_residue_algebraMap
      hβ₀ hfmonic hfmap hprim c

/-! ### Roots in a valuation subring with prescribed residue

The argument uses neither Hensel's lemma nor any locality or separability hypothesis on the
coefficient ring:

1. `p := f.map (algebraMap R A) : A[X]` is monic, so its image in `L[X]` has exactly `p.natDegree`
   roots in the algebraically closed `L`, counted with multiplicity
   (`IsAlgClosed.card_roots_map_eq_natDegree_of_injective`).
2. Each such root is a root of a monic polynomial with `A`-coefficients, hence integral over `A`,
   hence in the image of `A`, a valuation subring being integrally closed in its fraction field
   `L` (`IsIntegrallyClosed.isIntegral_iff`).
3. Hence `p.roots.card = p.natDegree` (`Polynomial.filter_roots_map_range_eq_map_roots`), i.e. `p`
   already splits into linear factors over `A` itself, not merely over `L`
   (`Polynomial.splits_iff_card_roots`, `Polynomial.Splits.eq_prod_roots_of_monic`).
4. Reducing that factorization along `IsLocalRing.residue A` expresses the reduction of `f` as a
   product of linear factors indexed by the residues of the `A`-roots of `p`. The residue field
   being a field, a prescribed root `a₀` of the reduction annihilates one of those factors
   (`Multiset.prod_eq_zero_iff`), so `a₀` is the residue of an `A`-root of `p`. -/

/-- **A root with prescribed residue.** Let `L` be algebraically closed, `A : ValuationSubring L`,
`R` a commutative ring with an algebra map to `A`, and `f : R[X]` monic. Every root
`a₀ : IsLocalRing.ResidueField A` of the reduction of `f` modulo the maximal ideal of `A` is the
residue of a root of `f` in `A` itself. The hypothesis is phrased as `IsRoot` for the image of `f`
under the composite `(IsLocalRing.residue A).comp (algebraMap R A)`, avoiding a bundled
`Algebra R (IsLocalRing.ResidueField A)` instance. -/
theorem ValuationSubring.exists_aeval_root_residue_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {R : Type*} [CommRing R] [Algebra R A]
    {f : R[X]} (hf : f.Monic) {a₀ : IsLocalRing.ResidueField A}
    (ha₀ : (f.map ((IsLocalRing.residue A).comp (algebraMap R A))).IsRoot a₀) :
    ∃ x : A, Polynomial.aeval x f = 0 ∧ IsLocalRing.residue A x = a₀ := by
  classical
  set p : A[X] := f.map (algebraMap R A) with hpdef
  have hpmonic : p.Monic := hf.map _
  have hpne : p ≠ 0 := hpmonic.ne_zero
  have hinj : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  -- Every `L`-root of `p` (mapped along `A → L`) already lies in the range of `A → L`.
  have hrange : ∀ y ∈ (Polynomial.map (algebraMap A L) p).roots, y ∈ (algebraMap A L).range := by
    intro y hy
    rw [Polynomial.mem_roots_map_of_injective hinj hpne] at hy
    have hyint : IsIntegral A y := ⟨p, hpmonic, hy⟩
    exact (IsIntegrallyClosed.isIntegral_iff (K := L)).mp hyint
  -- Hence `p` itself already splits into linear factors over `A`.
  have hcard : p.roots.card = p.natDegree := by
    have h1 : (Polynomial.map (algebraMap A L) p).roots.card = p.natDegree :=
      IsAlgClosed.card_roots_map_eq_natDegree_of_injective p hinj
    have hfilter : Multiset.filter (· ∈ (algebraMap A L).range)
        (Polynomial.map (algebraMap A L) p).roots = Multiset.map (algebraMap A L) p.roots :=
      Polynomial.filter_roots_map_range_eq_map_roots hinj p
    rw [Multiset.filter_eq_self.mpr hrange] at hfilter
    rw [hfilter, Multiset.card_map] at h1
    exact h1
  have hsplits : p.Splits := Polynomial.splits_iff_card_roots.mpr hcard
  have hprod : p = (Multiset.map (fun r => Polynomial.X - Polynomial.C r) p.roots).prod :=
    hsplits.eq_prod_roots_of_monic hpmonic
  -- Reduce the `A`-factorization mod `A`'s maximal ideal.
  have hfactored : f.map ((IsLocalRing.residue A).comp (algebraMap R A)) =
      (Multiset.map (fun r => Polynomial.X - Polynomial.C (IsLocalRing.residue A r)) p.roots).prod := by
    have step1 : f.map ((IsLocalRing.residue A).comp (algebraMap R A)) =
        p.map (IsLocalRing.residue A) := by rw [hpdef, Polynomial.map_map]
    have step2 : p.map (IsLocalRing.residue A) =
        (Multiset.map (fun r => Polynomial.X - Polynomial.C r) p.roots).prod.map
          (IsLocalRing.residue A) := congrArg (Polynomial.map (IsLocalRing.residue A)) hprod
    have step3 : (Multiset.map (fun r => Polynomial.X - Polynomial.C r) p.roots).prod.map
          (IsLocalRing.residue A) =
        (Multiset.map (Polynomial.map (IsLocalRing.residue A))
          (Multiset.map (fun r => Polynomial.X - Polynomial.C r) p.roots)).prod :=
      Polynomial.map_multiset_prod _ _
    have step4 : (Multiset.map (Polynomial.map (IsLocalRing.residue A))
          (Multiset.map (fun r => Polynomial.X - Polynomial.C r) p.roots)) =
        Multiset.map (fun r => Polynomial.X - Polynomial.C (IsLocalRing.residue A r)) p.roots := by
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro r _
      simp [Function.comp]
    rw [step1, step2, step3, step4]
  -- Evaluate the factorization at `a₀`: one linear factor must vanish.
  have heval : (Multiset.map (fun r => a₀ - IsLocalRing.residue A r) p.roots).prod = 0 := by
    have h : Polynomial.eval a₀
        (Multiset.map (fun r => Polynomial.X - Polynomial.C (IsLocalRing.residue A r)) p.roots).prod
        = 0 := by rw [← hfactored]; exact ha₀
    rwa [Polynomial.eval_multiset_prod, Multiset.map_map, show
        (Polynomial.eval a₀ ∘ fun r => Polynomial.X - Polynomial.C (IsLocalRing.residue A r)) =
        (fun r => a₀ - IsLocalRing.residue A r) from by funext r; simp [Function.comp]] at h
  obtain ⟨d, hdmem, hd0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp heval)
  refine ⟨d, ?_, (sub_eq_zero.mp hd0).symm⟩
  have hdroot : d ∈ p.roots := hdmem
  rw [Polynomial.mem_roots hpne, Polynomial.IsRoot.def] at hdroot
  rwa [hpdef, Polynomial.eval_map_algebraMap] at hdroot

/-! ### The unramified lifting theorem -/

variable {L : Type*} [Field L] [Algebra K L] (A : ValuationSubring L) [Algebra ↥(𝒪[K]) A]
  [IsLocalHom (algebraMap ↥(𝒪[K]) A)]

/-- **The unramified lifting theorem.** Let `K` be a nonarchimedean local field, `L / K` an
algebraic, algebraically closed extension, and `A : ValuationSubring L` lying over `𝒪[K]`
(`hAcomap`, `hcompat`), with `IsLocalRing.ResidueField A / 𝓀[K]` Galois. For every finite normal
subextension `M` of `IsLocalRing.ResidueField A / 𝓀[K]`, every element of `Gal(M/𝓀[K])` is the
restriction to `M` of the action of some element of the decomposition subgroup
`A.decompositionSubgroup K` on `IsLocalRing.ResidueField A`.

This is not an instance of `InfiniteGalois.restrictNormalHom_surjective`, which concerns restriction
between normal subextensions of a single Galois extension: the map shown surjective here goes from
the decomposition subgroup of `A` to `Gal(M/𝓀[K])`, `M` being an extension of the residue field
rather than an intermediate field of `L / K`.

Proof outline. Take a primitive element `β₀` of `M / 𝓀[K]` (`𝓀[K]` is finite, hence perfect) and a
monic lift `f : 𝒪[K][X]` of `minpoly 𝓀[K] β₀`. Since `g` fixes `𝓀[K]`, the same `f` lifts the
minimal polynomial of `g β₀`, so `ValuationSubring.exists_aeval_root_residue_eq` applied twice
yields roots `y, y' : A` of `f` with residues `β₀` and `g β₀`. Both are roots of the irreducible
`f.map (algebraMap ↥(𝒪[K]) K)`, hence share a minimal polynomial over `K`, and the resulting
isomorphism `K⟮y⟯ ≃ₐ[K] K⟮y'⟯` extends to `σ : L ≃ₐ[K] L` by algebraicity and algebraic closedness
of `L`. Both `A` and `σ • A` contract to `𝒪[K]`, so uniqueness of the extension of the valuation
puts `σ` in the decomposition subgroup, and equivariance of the residue map gives `σ • β₀ = g β₀`,
which determines the restriction of `σ` to `M` since `β₀` generates `M`. -/
theorem ValuationSubring.exists_restrictNormalHom_decompositionSubgroup_surjective
    (hAcomap : A.comap (algebraMap K L) = (ValuativeRel.valuation K).valuationSubring)
    (hcompat : ∀ a : ↥(𝒪[K]), (algebraMap ↥(𝒪[K]) A a : L) = algebraMap K L (a : K))
    [IsAlgClosed L] [Algebra.IsAlgebraic K L] [IsGalois 𝓀[K] (IsLocalRing.ResidueField A)]
    (M : IntermediateField 𝓀[K] (IsLocalRing.ResidueField A))
    [FiniteDimensional 𝓀[K] M] [Normal 𝓀[K] M] :
    Function.Surjective fun σ : A.decompositionSubgroup K =>
      AlgEquiv.restrictNormalHom (F := 𝓀[K]) M
        (AlgEquiv.ofRingEquiv (f := (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
          (IsLocalRing.ResidueField A)) σ)
          (ValuationSubring.decompositionSubgroup_smul_algebraMap_residueField A hcompat σ)) := by
  intro g
  -- The ambient algebra structure `↥(𝒪[K]) → K → L`. Constructed locally rather than as a section
  -- instance, for the same instance-resolution reason `hcompat` is a hypothesis (see the module
  -- docstring).
  letI hRLalg : Algebra ↥(𝒪[K]) L := ((algebraMap K L).comp (algebraMap ↥(𝒪[K]) K)).toAlgebra
  haveI hRKLtower : IsScalarTower ↥(𝒪[K]) K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- `M / 𝓀[K]` is separable (`𝓀[K]` is finite, hence perfect) and finite, hence has a primitive
  -- element `β₀`.
  haveI : PerfectField 𝓀[K] := PerfectField.ofFinite
  haveI : Algebra.IsAlgebraic 𝓀[K] M := Algebra.IsAlgebraic.of_finite 𝓀[K] M
  obtain ⟨β₀, hprim⟩ := Field.exists_primitive_element 𝓀[K] M
  have hβ₀ : IsIntegral 𝓀[K] (β₀ : M) := IsIntegral.of_finite 𝓀[K] (β₀ : M)
  -- The monic lift `f` of `β₀`'s minimal polynomial, computed once and shared between the two root
  -- extractions below (for `β₀` and for `g β₀`), so that the two roots produced are roots of the
  -- same polynomial over `K` and hence `K`-conjugate.
  obtain ⟨f, hfmonic, hfdeg, hfmap⟩ := HenselianLocalRing.exists_monic_lift_minpoly hβ₀
  -- `f.map (algebraMap ↥(𝒪[K]) K)` is irreducible over `K`, hence is the minimal polynomial of any
  -- of its roots in `L`, up to the scaling forced by monicity.
  have hpirr : Irreducible (f.map (algebraMap ↥(𝒪[K]) K)) :=
    HenselianLocalRing.irreducible_map_lift_minpoly (K := K) hβ₀ hfmonic hfmap
  -- The composite ring hom `↥(𝒪[K]) → K → L` agrees with `↥(𝒪[K]) → A → L`, by `hcompat`.
  have hcomp2 : (algebraMap K L).comp (algebraMap ↥(𝒪[K]) K) =
      (algebraMap A L).comp (algebraMap ↥(𝒪[K]) A) := RingHom.ext fun a => (hcompat a).symm
  -- For an element of `M` whose minimal polynomial over `𝓀[K]` is lifted by `f`, produce a root of
  -- `f` in `A` whose residue is that element. Applied below to `β₀` and to `g β₀`, sharing `f`.
  have hroot_of_residue : ∀ a₀ : M, f.map (algebraMap ↥(𝒪[K]) 𝓀[K]) = minpoly 𝓀[K] (a₀ : M) →
      ∃ y : A, Polynomial.aeval y f = 0 ∧ IsLocalRing.residue A y = (a₀ : IsLocalRing.ResidueField A) := by
    intro a₀ ha₀map
    apply ValuationSubring.exists_aeval_root_residue_eq A hfmonic
    show (f.map ((IsLocalRing.residue A).comp (algebraMap ↥(𝒪[K]) A))).IsRoot (M.val a₀)
    have hcompres : (IsLocalRing.residue A).comp (algebraMap ↥(𝒪[K]) A) =
        (algebraMap 𝓀[K] (IsLocalRing.ResidueField A)).comp (algebraMap ↥(𝒪[K]) 𝓀[K]) :=
      RingHom.ext fun a => (IsLocalRing.ResidueField.algebraMap_residue (R := ↥(𝒪[K])) (S := A) a).symm
    rw [Polynomial.IsRoot.def, hcompres, ← Polynomial.map_map, ha₀map,
      Polynomial.eval_map_algebraMap]
    exact minpoly.aeval_algHom 𝓀[K] M.val a₀
  -- Applied to `β₀`: a root `y : A` of `f` with `residue A y = β₀`.
  obtain ⟨y, hyf, hyres⟩ := hroot_of_residue β₀ hfmap
  -- `(y : L)` is then a root of `f.map (algebraMap ↥(𝒪[K]) K)` over `K`: push `hyf` through
  -- `algebraMap A L`, using `hcomp2` to identify the two routes `↥(𝒪[K]) → K → L` and
  -- `↥(𝒪[K]) → A → L`.
  have hyK_aeval : Polynomial.aeval (y : L) (f.map (algebraMap ↥(𝒪[K]) K)) = 0 := by
    have hstep := Polynomial.hom_eval₂ f (algebraMap ↥(𝒪[K]) A) (algebraMap A L) (y : A)
    rw [← Polynomial.aeval_def, hyf, map_zero, ← hcomp2, ← Polynomial.eval₂_map,
      ← Polynomial.aeval_def] at hstep
    exact hstep.symm
  have hyKint : IsIntegral K (y : L) := ⟨f.map (algebraMap ↥(𝒪[K]) K), hfmonic.map _, hyK_aeval⟩
  set K' : IntermediateField K L := IntermediateField.adjoin K {(y : L)} with hK'def
  -- `minpoly K y` is (up to the unit-scaling forced by monicity) `f.map (algebraMap ↥(𝒪[K]) K)`.
  have hminpoly_scaled :
      f.map (algebraMap ↥(𝒪[K]) K) *
          Polynomial.C (f.map (algebraMap ↥(𝒪[K]) K)).leadingCoeff⁻¹ = minpoly K (y : L) :=
    minpoly.eq_of_irreducible hpirr hyK_aeval
  have hminpoly : f.map (algebraMap ↥(𝒪[K]) K) = minpoly K (y : L) := by
    rwa [(hfmonic.map (algebraMap ↥(𝒪[K]) K)).leadingCoeff, inv_one, Polynomial.C_1, mul_one]
      at hminpoly_scaled
  -- Since `g` fixes `𝓀[K]` pointwise, `g β₀` has the same minimal polynomial as `β₀`
  -- (`minpoly.algEquiv_eq`), so `f` lifts it too and `hroot_of_residue` applies again, giving a
  -- second root `y' : A` with residue `g β₀`.
  have hβg : IsIntegral 𝓀[K] (g β₀ : M) :=
    (isIntegral_algHom_iff g.toAlgHom g.injective).mpr hβ₀
  have hfmap_g : f.map (algebraMap ↥(𝒪[K]) 𝓀[K]) = minpoly 𝓀[K] (g β₀ : M) :=
    hfmap.trans (minpoly.algEquiv_eq g β₀).symm
  obtain ⟨y', hy'f, hy'res⟩ := hroot_of_residue (g β₀) hfmap_g
  have hy'K_aeval : Polynomial.aeval (y' : L) (f.map (algebraMap ↥(𝒪[K]) K)) = 0 := by
    have hstep := Polynomial.hom_eval₂ f (algebraMap ↥(𝒪[K]) A) (algebraMap A L) (y' : A)
    rw [← Polynomial.aeval_def, hy'f, map_zero, ← hcomp2, ← Polynomial.eval₂_map,
      ← Polynomial.aeval_def] at hstep
    exact hstep.symm
  have hy'Kint : IsIntegral K (y' : L) := ⟨f.map (algebraMap ↥(𝒪[K]) K), hfmonic.map _, hy'K_aeval⟩
  set K'' : IntermediateField K L := IntermediateField.adjoin K {(y' : L)} with hK''def
  have hminpoly'_scaled :
      f.map (algebraMap ↥(𝒪[K]) K) *
          Polynomial.C (f.map (algebraMap ↥(𝒪[K]) K)).leadingCoeff⁻¹ = minpoly K (y' : L) :=
    minpoly.eq_of_irreducible hpirr hy'K_aeval
  have hminpoly' : f.map (algebraMap ↥(𝒪[K]) K) = minpoly K (y' : L) := by
    rwa [(hfmonic.map (algebraMap ↥(𝒪[K]) K)).leadingCoeff, inv_one, Polynomial.C_1, mul_one]
      at hminpoly'_scaled
  -- `y` and `y'` are roots of the same polynomial `f.map (algebraMap ↥(𝒪[K]) K)` over `K`, hence
  -- have the same minimal polynomial, giving a genuine `K`-algebra isomorphism `K' ≃ₐ[K] K''`.
  have hminpolyeq : minpoly K (y : L) = minpoly K (y' : L) := hminpoly.symm.trans hminpoly'
  set e : K' ≃ₐ[K] K'' := minpoly.algEquiv hyKint.isAlgebraic hminpolyeq with hedef
  -- Extend `e` to a `K`-automorphism `σ` of all of `L`, via `IsAlgClosed L` and algebraicity of
  -- `L/K`.
  haveI hK'algL : Algebra.IsAlgebraic K' L := Algebra.IsAlgebraic.tower_top (K := K) K'
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := K) (L := K')
    (M := L) (E := L) (K''.val.comp e.toAlgHom)
  set σ : L ≃ₐ[K] L :=
    AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective (K := K) (L := L) φ) with hσdef
  have hσy : σ (y : L) = (y' : L) := by
    have hgen : φ (algebraMap K' L (IntermediateField.AdjoinSimple.gen K (y : L))) =
        algebraMap K'' L (e (IntermediateField.AdjoinSimple.gen K (y : L))) :=
      DFunLike.congr_fun hφ (IntermediateField.AdjoinSimple.gen K (y : L))
    rw [IntermediateField.AdjoinSimple.algebraMap_gen, hedef,
      minpoly.algEquiv_apply hyKint.isAlgebraic hminpolyeq,
      IntermediateField.AdjoinSimple.algebraMap_gen] at hgen
    show φ (y : L) = (y' : L)
    exact hgen
  -- `σ` lies in the decomposition subgroup of `A`: `σ • A` and `A` both comap (along
  -- `algebraMap K L`) to `𝒪[K]` (for `A`, by hypothesis `hAcomap`; for `σ • A`, since `σ` fixes
  -- `K` pointwise, `ValuationSubring.comap_smul_eq`), so uniqueness of extension of the valuation
  -- from the Henselian base `K` identifies `σ • A` with `A`.
  have hσAcomap : (σ • A).comap (algebraMap K L) = (ValuativeRel.valuation K).valuationSubring :=
    (ValuationSubring.comap_smul_eq σ A).trans hAcomap
  have hσA : σ • A = A :=
    LocalField.valuationSubring_eq_of_comap_eq_of_isNonarchimedeanLocalField hσAcomap hAcomap
  have hσmem : σ ∈ A.decompositionSubgroup K := MulAction.mem_stabilizer_iff.mpr hσA
  -- Two `𝓀[K]`-algebra automorphisms of `M` agreeing at the primitive element `β₀`
  -- (`hprim : 𝓀[K]⟮β₀⟯ = ⊤`) agree everywhere.
  have hgenext : ∀ h1 h2 : M ≃ₐ[𝓀[K]] M, h1 β₀ = h2 β₀ → h1 = h2 := by
    intro h1 h2 hh
    have heq : h1.toAlgHom.comp IntermediateField.topEquiv.toAlgHom =
        h2.toAlgHom.comp IntermediateField.topEquiv.toAlgHom := by
      apply IntermediateField.algHom_ext_of_eq_adjoin 𝓀[K] hprim.symm
      rintro z hz
      simp only [Set.mem_singleton_iff] at hz
      simp only [AlgHom.comp_apply]
      exact hz ▸ hh
    apply AlgEquiv.ext
    intro m
    have hcongr := DFunLike.congr_fun heq (IntermediateField.topEquiv.symm m)
    simpa using hcongr
  refine ⟨⟨σ, hσmem⟩, hgenext _ g ?_⟩
  dsimp only
  -- `σ` sends `y` to `y'` in `A`, the action stabilizing `A`, and `residue A` is equivariant for
  -- that action (`IsLocalRing.ResidueField.residue_smul`), so the induced action of `σ` on
  -- `IsLocalRing.ResidueField A` sends `β₀ = residue A y` to `residue A y' = g β₀`.
  have hσyA : (⟨σ, hσmem⟩ : A.decompositionSubgroup K) • y = y' := by
    apply Subtype.ext
    show (σ : L ≃ₐ[K] L) (y : L) = (y' : L)
    exact hσy
  have hresidue_action :
      (⟨σ, hσmem⟩ : A.decompositionSubgroup K) • (β₀ : IsLocalRing.ResidueField A) =
        (g β₀ : IsLocalRing.ResidueField A) := by
    rw [← hyres, ← hy'res, ← hσyA]
    exact IsLocalRing.ResidueField.residue_smul (A.decompositionSubgroup K) ⟨σ, hσmem⟩ y
  apply Subtype.ext
  rw [AlgEquiv.restrictNormalHom_apply M _ β₀, AlgEquiv.ofRingEquiv_apply,
    MulSemiringAction.toRingAut_apply,
    MulSemiringAction.toRingEquiv_apply_apply]
  exact hresidue_action
