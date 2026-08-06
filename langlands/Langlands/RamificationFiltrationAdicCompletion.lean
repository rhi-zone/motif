import Langlands.RamificationFiltration
import Langlands.AdicCompletionIntegralClosure
import Langlands.HenselianResidueLift
import Langlands.NormMap
import Langlands.TowerBundle
import Langlands.TwoGeneratorMonogenic

/-!
# Ramification filtration for adic completions

Specializes `Langlands.RamificationFiltration`'s general `ValuationSubring.ramificationGroup` to
this repo's adic-completion setting (`Langlands.AdicCompletionIntegralClosure`,
`Langlands.UnramifiedValuationExtension`): `R S` Dedekind domains with fraction fields `K L`,
`v : HeightOneSpectrum R`, `w : HeightOneSpectrum S` with `w.asIdeal.LiesOver v.asIdeal`,
`K₀ := v.adicCompletionIntegers K`, `L₀ := w.adicCompletionIntegers L`. This file supplies no new
mathematical content beyond the general theory of `Langlands.RamificationFiltration`, instantiated
at `A := L₀ : ValuationSubring (w.adicCompletion L)` over the base field `v.adicCompletion K` (the
`Algebra (v.adicCompletion K) (w.adicCompletion L)` instance is supplied by `Langlands.NormMap`,
already in scope via `Langlands.AdicCompletionIntegralClosure`).

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.ramificationGroup` : the `i`-th ramification group in lower
  numbering of `w.adicCompletionIntegers L` over `v.adicCompletion K`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.decompositionSubgroup_eq_top` : the decomposition subgroup
  of `w.adicCompletionIntegers L` in `(w.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.adicCompletion L)`
  is everything — no Galois/normality hypothesis on `w.adicCompletion L / v.adicCompletion K`
  is needed, only completeness of the base field `v.adicCompletion K`. See its docstring.
* `IsDedekindDomain.HeightOneSpectrum.henselianLocalRing_adicCompletionIntegers` :
  `w.adicCompletionIntegers L` is a Henselian local ring.
* `IsDedekindDomain.HeightOneSpectrum.exists_adjoin_pair_eq_top` : `𝒪_L = 𝒪_K[x, π]` for `π` a
  given uniformizer and `x` a Hensel-lifted simple root.
* `IsDedekindDomain.HeightOneSpectrum.mem_ramificationGroup_succ_iff` : Serre's uniformizer
  criterion, `σ ∈ G_{i+1} ↔ σ • π - π ∈ 𝔪 ^ (i + 2)` for `σ` in the inertia group.

## Scope

`mem_ramificationGroup_succ_iff` is the kernel computation that
`Langlands.RamificationFiltration`'s "Scope" docstring records as the blocker for the
associated-graded embeddings. The embeddings themselves — the maps `G_0 →* 𝓀[L]ˣ` and
`G_i / G_{i+1} →+ 𝓀[L]` and their injectivity, and the resulting "the filtration is eventually
trivial" statement — are still not constructed, here or in the general file. What is closed is the
step those constructions were blocked on, not the constructions.
-/

noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

/-- The `i`-th ramification group in lower numbering of `w.adicCompletionIntegers L`, viewed as a
`ValuationSubring (w.adicCompletion L)`, over the base field `v.adicCompletion K`. This is
`ValuationSubring.ramificationGroup` specialized to this repo's adic-completion setting. -/
def ramificationGroup (i : ℕ) :
    Subgroup ((w.adicCompletionIntegers L).decompositionSubgroup (v.adicCompletion K)) :=
  ValuationSubring.ramificationGroup (v.adicCompletion K) (w.adicCompletionIntegers L) i

/-! ### The decomposition subgroup is everything -/

open scoped Pointwise

omit [Algebra.IsIntegral R S] in
/-- The decomposition subgroup of `w.adicCompletionIntegers L` (as a `ValuationSubring
(w.adicCompletion L)`) in `(w.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.adicCompletion L)` is
all of that automorphism group.

No Galois/normality hypothesis on `w.adicCompletion L / v.adicCompletion K` is needed: since
`v.adicCompletion K` is complete (`instCompleteSpaceAdicCompletion`, via
`Mathlib.RingTheory.DedekindDomain.AdicValuation`) and `w.adicCompletion L / v.adicCompletion K` is
algebraic (`Module.Finite`, an existing instance from `Langlands.NormMap`), every algebraic
extension of a complete field has a *unique* extension of the valuation
(`LocalField.valuationSubring_eq_of_comap_eq`, `Langlands.HenselianValuation`, built on Mathlib's
`spectralNorm_unique_field_norm_ext`). Both `w.adicCompletionIntegers L` and any of its
`σ`-translates comap to `v.adicCompletionIntegers K` under `algebraMap (v.adicCompletion K)
(w.adicCompletion L)` (`ValuationSubring.comap_smul_eq` for the translate,
`adicCompletionIntegers_comap_eq` for the base case, bridged to `ValuativeRel.valuation`'s
valuation subring via `valuation_valuationSubring_eq_adicCompletionIntegers`), so uniqueness forces
`σ • (w.adicCompletionIntegers L) = w.adicCompletionIntegers L` for every `σ`. This exactly
parallels `LocalField.decompositionSubgroup_eq_top` (`Langlands.WeilGroup`), which is the same fact
for `L = AlgebraicClosure K` under the packaged `IsNonarchimedeanLocalField K` hypothesis instead of
this file's `v.adicCompletion K`-specific instance chain. -/
theorem decompositionSubgroup_eq_top :
    (w.adicCompletionIntegers L).decompositionSubgroup (v.adicCompletion K) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro σ
  rw [MulAction.mem_stabilizer_iff]
  have hbase : (w.adicCompletionIntegers L).comap (algebraMap (v.adicCompletion K) (w.adicCompletion L))
      = (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring := by
    rw [valuation_valuationSubring_eq_adicCompletionIntegers]
    exact adicCompletionIntegers_comap_eq K L v w
  apply LocalField.valuationSubring_eq_of_comap_eq (K := v.adicCompletion K)
  · rw [ValuationSubring.comap_smul_eq]
    exact hbase
  · exact hbase

/-! ### `w.adicCompletionIntegers L` is Henselian

This is the piece `Langlands.RamificationFiltration`'s docstring flags as missing: Hensel's lemma
applied *inside the actual field `w.adicCompletion L`* (rather than an auxiliary algebraically
closed field), the prerequisite for lifting a residue-field generator to a genuine subfield
`L_0 ⊆ w.adicCompletion L`. -/

omit [Algebra.IsIntegral R S] in
/-- **`w.adicCompletionIntegers L` is a Henselian local ring.**

Combines `decompositionSubgroup_eq_top`'s comap identity (`w.adicCompletionIntegers L` restricts
to `v.adicCompletionIntegers K` under `algebraMap`) with
`LocalField.exists_rankOne_compatible` (`Langlands.HenselianValuation`, giving `RankOne` of the
valuation, since `v.adicCompletion K` is complete and `w.adicCompletion L / v.adicCompletion K` is
algebraic) and `LocalField.henselianLocalRing_of_comap_eq` (`Langlands.TowerBundle`, the `letI`
bundle assembled from those two facts plus finiteness of the residue field). -/
theorem henselianLocalRing_adicCompletionIntegers (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] [Algebra K L] [IsScalarTower R K L] [Module.Finite K L]
    (v : HeightOneSpectrum R) [w.asIdeal.LiesOver v.asIdeal]
    [Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers L))] :
    HenselianLocalRing ↥(w.adicCompletionIntegers L) := by
  have hbase : (w.adicCompletionIntegers L).comap
      (algebraMap (v.adicCompletion K) (w.adicCompletion L))
      = (ValuativeRel.valuation (v.adicCompletion K)).valuationSubring := by
    rw [valuation_valuationSubring_eq_adicCompletionIntegers]
    exact adicCompletionIntegers_comap_eq K L v w
  obtain ⟨hR, -⟩ := LocalField.exists_rankOne_compatible (v.adicCompletion K)
    (w.adicCompletionIntegers L) hbase
  exact LocalField.henselianLocalRing_of_comap_eq (v.adicCompletion K)
    (w.adicCompletionIntegers L) hbase hR ‹_›

/-! ### `𝒪_L = 𝒪_K[x, π]`, and the kernel of the associated-graded map

This is what `Langlands.RamificationFiltration`'s "Scope" docstring has recorded as blocked since
`ROADMAP.md`'s Phase 2b twelfth pass. The route below is *not* the classical one: no maximal
unramified subextension `L_0` is constructed as a subfield, no Eisenstein polynomial appears, and
`𝒪_L` is not shown to be monogenic over anything. Instead

1. `HenselianLocalRing.exists_isRoot_residue_eq_of_finite` (`Langlands.HenselianResidueLift`)
   lifts a primitive element `β₀` of the residue extension to a *simple* root `x` of a monic
   polynomial `f` over `𝒪_K`, inside `𝒪_L` itself — Hensel's lemma applied to
   `henselianLocalRing_adicCompletionIntegers` above, with no auxiliary algebraically closed field;
2. `LocalField.adjoin_pair_eq_top` (`Langlands.TwoGeneratorMonogenic`) shows the *pair* `{x, π}`
   generates `𝒪_L` over `𝒪_K`, by Nakayama;
3. `ValuationSubring.smul_eq_of_isRoot_of_mem_ramificationGroup_zero` shows any `σ ∈ G_0` fixes `x`
   exactly (simple roots are rigid), and
   `ValuationSubring.mem_ramificationGroup_succ_of_adjoin` then propagates the condition at `π`
   to all of `𝒪_L`.
-/

section KernelDirection

variable [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]
  [Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers L))]

omit [Algebra.IsIntegral R S] in
/-- **`𝒪_L` is generated over `𝒪_K` by a uniformizer together with a simple root.**

For `π` a uniformizer of `w.adicCompletionIntegers L`, there are a monic `f` over
`v.adicCompletionIntegers K` and a root `x` of `f` in `w.adicCompletionIntegers L`, simple
(`IsUnit (aeval x f.derivative)`), with `𝒪_K[x, π] = 𝒪_L`.

`x` is the Hensel lift of a primitive element of the residue extension, produced inside
`w.adicCompletionIntegers L` itself by `HenselianLocalRing.exists_isRoot_residue_eq_of_finite`
(the `HenselianLocalRing` instance is `henselianLocalRing_adicCompletionIntegers`, the residue-map
compatibility is `algebraMap_residueField_residue`). That `𝒪_K[x]` surjects onto the residue field
is exactly the primitive-element statement transported along `residue x = β₀`, and
`LocalField.adjoin_pair_eq_top` then gives generation by Nakayama. -/
theorem exists_adjoin_pair_eq_top {π : w.adicCompletionIntegers L}
    (hπ : IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) = Ideal.span {π}) :
    ∃ (f : Polynomial (v.adicCompletionIntegers K)) (x : w.adicCompletionIntegers L),
      Polynomial.aeval x f = 0 ∧ IsUnit (Polynomial.aeval x f.derivative) ∧
        Algebra.adjoin (v.adicCompletionIntegers K)
          ({x, π} : Set (w.adicCompletionIntegers L)) = ⊤ := by
  haveI : HenselianLocalRing (w.adicCompletionIntegers L) :=
    henselianLocalRing_adicCompletionIntegers L w K v
  obtain ⟨β₀, hβ₀top, f, -, -, x, hxroot, hxres, hxunit⟩ :=
    HenselianLocalRing.exists_isRoot_residue_eq_of_finite
      (R₀ := v.adicCompletionIntegers K) (R := w.adicCompletionIntegers L)
      (algebraMap_residueField_residue K L v w)
  refine ⟨f, x, hxroot, hxunit, ?_⟩
  have hinj : Function.Injective
      (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) := by
    intro a b hab
    have h : ((algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) a :
          w.adicCompletionIntegers L) : w.adicCompletion L)
        = ((algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) b :
          w.adicCompletionIntegers L) : w.adicCompletion L) := congrArg _ hab
    rw [coe_algebraMap_adicCompletionIntegers, coe_algebraMap_adicCompletionIntegers] at h
    exact Subtype.ext ((adicCompletionComap K L v w).injective h)
  refine LocalField.adjoin_pair_eq_top hinj hπ ?_
  intro z
  have hz : IsLocalRing.residue (w.adicCompletionIntegers L) z ∈
      Algebra.adjoin (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
        ({β₀} : Set (IsLocalRing.ResidueField (w.adicCompletionIntegers L))) := by
    rw [hβ₀top]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨p, hp⟩ := hz
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective
    (algebraMap (v.adicCompletionIntegers K)
      (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
    (by
      rw [IsLocalRing.ResidueField.algebraMap_eq]
      exact IsLocalRing.residue_surjective) p
  have hkey : IsLocalRing.residue (w.adicCompletionIntegers L) (Polynomial.aeval x q)
      = IsLocalRing.residue (w.adicCompletionIntegers L) z := by
    have h1 : Polynomial.aeval x q
        = (q.map (algebraMap (v.adicCompletionIntegers K)
            (w.adicCompletionIntegers L))).eval x := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    rw [h1, IsLocalRing.residue_eval, hxres,
      IsLocalRing.aeval_map_residue_eq (algebraMap_residueField_residue K L v w) q β₀]
    exact hp
  refine ⟨Polynomial.aeval x q, ?_, ?_⟩
  · rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨q, rfl⟩
  · rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hkey, sub_self]

omit [Algebra.IsIntegral R S] in
/-- **The kernel of the associated-graded map, in the adic-completion setting.**

For `π` a uniformizer of `w.adicCompletionIntegers L` and `σ` in the inertia group
(`ramificationGroup K L v w 0`), the single condition `σ • π - π ∈ 𝔪 ^ (i + 2)` — which is what
the associated-graded map `G_i / G_{i+1} → 𝓀[L]` measures — already forces `σ ∈ G_{i+1}`, i.e.
`σ • y - y ∈ 𝔪 ^ (i + 2)` for *every* `y : 𝒪_L`.

Together with the reverse inclusion (immediate: test the defining property of `G_{i+1}` at `y =
π`), this is the equivalence between Serre's `i_G(σ) = v_L(σ(π_L) - π_L)`-based definition of the
filtration and the "acts trivially on `𝒪_L / 𝔪^{i+1}`" definition used by
`ValuationSubring.ramificationGroup`, in the concrete setting of this file. -/
theorem mem_ramificationGroup_succ_of_smul_sub_mem (i : ℕ) {π : w.adicCompletionIntegers L}
    (hπ : IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) = Ideal.span {π})
    {σ : (w.adicCompletionIntegers L).decompositionSubgroup (v.adicCompletion K)}
    (hσ : σ ∈ ramificationGroup K L v w 0)
    (hπσ : σ • π - π ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ (i + 2)) :
    σ ∈ ramificationGroup K L v w (i + 1) := by
  obtain ⟨f, x, hxroot, hxunit, hgen⟩ := exists_adjoin_pair_eq_top K L v w hπ
  have hfix : ∀ r : v.adicCompletionIntegers K,
      σ • (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) r)
        = algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) r := by
    intro r
    refine Subtype.ext ?_
    show (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
        ((algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) r :
          w.adicCompletionIntegers L) : w.adicCompletion L) = _
    rw [coe_algebraMap_adicCompletionIntegers]
    exact (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L).commutes _
  have hx : σ • x = x :=
    ValuationSubring.smul_eq_of_isRoot_of_mem_ramificationGroup_zero hxroot hxunit hσ hfix
  exact ValuationSubring.mem_ramificationGroup_succ_of_adjoin i hgen hfix hx hπσ

omit [Algebra.IsIntegral R S] in
/-- **Serre's uniformizer criterion for the ramification filtration.** For `σ` in the inertia group
and `π` a uniformizer, `σ ∈ G_{i+1}` iff `σ • π - π ∈ 𝔪 ^ (i + 2)`.

The `→` direction is the defining property of `G_{i+1}` tested at the single point `π`; the `←`
direction is `mem_ramificationGroup_succ_of_smul_sub_mem`. This is the identification of Serre's
`i_G`-based definition of the filtration (*Local Fields*, Ch. IV) with the "acts trivially on
`𝒪_L / 𝔪 ^ (i + 1)`" definition of `ValuationSubring.ramificationGroup`, and hence the statement
that `G_{i+1}` is exactly the kernel of the associated-graded map on `G_i`. -/
theorem mem_ramificationGroup_succ_iff (i : ℕ) {π : w.adicCompletionIntegers L}
    (hπ : IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) = Ideal.span {π})
    {σ : (w.adicCompletionIntegers L).decompositionSubgroup (v.adicCompletion K)}
    (hσ : σ ∈ ramificationGroup K L v w 0) :
    σ ∈ ramificationGroup K L v w (i + 1) ↔
      σ • π - π ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ (i + 2) :=
  ⟨fun h => h π, mem_ramificationGroup_succ_of_smul_sub_mem K L v w i hπ hσ⟩

/-! ### The associated-graded pieces, concretely: kernels and embeddings

Composes `Langlands.RamificationFiltration`'s `gradedZeroHom`/`gradedSuccHom` (bundled
homomorphisms, with kernels identified only as a *point-test* condition at `π` there) with
`mem_ramificationGroup_succ_iff` above (which turns that point test into genuine
`ramificationGroup` membership) to identify the kernels with the actual ramification subgroups, and
hence — via Mathlib's `QuotientGroup.kerLift_injective`, applied with no further work needed — get
the associated-graded *embeddings* `G_0 ⧸ G_1 ↪ 𝓀[L]ˣ` and `G_{i+1} ⧸ G_{i+2} ↪ 𝓀[L]` (additively). -/

omit [Algebra.IsIntegral R S] in
/-- **The kernel of the `i = 0` associated-graded map is exactly `G_1`.** -/
theorem gradedZeroHom_ker_eq {π : w.adicCompletionIntegers L}
    (hπ : IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) = Ideal.span {π}) :
    (ValuationSubring.gradedZeroHom hπ
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ).ne_zero).ker
      = Subgroup.subgroupOf
          (ValuationSubring.ramificationGroup (v.adicCompletion K) (w.adicCompletionIntegers L) 1)
          (ValuationSubring.ramificationGroup (v.adicCompletion K) (w.adicCompletionIntegers L)
            0) := by
  ext σ
  rw [MonoidHom.mem_ker, ValuationSubring.gradedZeroHom_apply_eq_one_iff, Subgroup.mem_subgroupOf,
    show ValuationSubring.ramificationGroup (v.adicCompletion K) (w.adicCompletionIntegers L) 1
        = ramificationGroup K L v w (0 + 1) from rfl,
    mem_ramificationGroup_succ_iff K L v w 0 hπ σ.2]

omit [Algebra.IsIntegral R S] in
/-- **`G_0 ⧸ G_1` embeds into `𝓀[L]ˣ`.** Mathlib's `QuotientGroup.kerLift_injective` applied to
`gradedZeroHom`; `gradedZeroHom_ker_eq` identifies the resulting kernel quotient with `G_0 ⧸ G_1` in
the natural sense. -/
theorem gradedZeroHom_kerLift_injective {π : w.adicCompletionIntegers L}
    (hπ : IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) = Ideal.span {π}) :
    Function.Injective (QuotientGroup.kerLift
      (ValuationSubring.gradedZeroHom (K := v.adicCompletion K) hπ
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ).ne_zero)) :=
  QuotientGroup.kerLift_injective _

omit [Algebra.IsIntegral R S] in
/-- **The kernel of the `i ≥ 1` associated-graded map (indexed as `G_{i+1}`) is exactly
`G_{i+2}`.** -/
theorem gradedSuccHom_ker_eq (i : ℕ) {π : w.adicCompletionIntegers L}
    (hπ : IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) = Ideal.span {π}) :
    (ValuationSubring.gradedSuccHom hπ
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ).ne_zero i).ker
      = Subgroup.subgroupOf
          (ValuationSubring.ramificationGroup (v.adicCompletion K) (w.adicCompletionIntegers L)
            (i + 2))
          (ValuationSubring.ramificationGroup (v.adicCompletion K) (w.adicCompletionIntegers L)
            (i + 1)) := by
  ext σ
  rw [MonoidHom.mem_ker, ValuationSubring.gradedSuccHom_apply_eq_one_iff, Subgroup.mem_subgroupOf,
    show ValuationSubring.ramificationGroup (v.adicCompletion K) (w.adicCompletionIntegers L)
        (i + 2) = ramificationGroup K L v w ((i + 1) + 1) from rfl,
    mem_ramificationGroup_succ_iff K L v w (i + 1) hπ
      (ValuationSubring.ramificationGroup_le_zero (w.adicCompletionIntegers L) (i + 1) σ.2)]

omit [Algebra.IsIntegral R S] in
/-- **`G_{i+1} ⧸ G_{i+2}` embeds additively into `𝓀[L]`** (as `Multiplicative (ResidueField
(w.adicCompletionIntegers L))`). Mathlib's `QuotientGroup.kerLift_injective` applied to
`gradedSuccHom`; `gradedSuccHom_ker_eq` identifies the resulting kernel quotient with
`G_{i+1} ⧸ G_{i+2}` in the natural sense. -/
theorem gradedSuccHom_kerLift_injective (i : ℕ) {π : w.adicCompletionIntegers L}
    (hπ : IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) = Ideal.span {π}) :
    Function.Injective (QuotientGroup.kerLift
      (ValuationSubring.gradedSuccHom (K := v.adicCompletion K) hπ
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ).ne_zero i)) :=
  QuotientGroup.kerLift_injective _

end KernelDirection

end IsDedekindDomain.HeightOneSpectrum

end
