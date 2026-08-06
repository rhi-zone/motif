/-
Copyright (c) 2026 rhizone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Langlands.TowerValuationSubring
import Langlands.TowerMonogenic

/-!
# The concrete tower monogenicity theorem, `𝒪[K] ⊆ 𝒪[M] ⊆ 𝒪[N]`

`Langlands.TowerMonogenic.LocalField.exists_adjoin_eq_top_of_tower_of_isEisensteinAt` is Serre's
tower monogenicity theorem in the abstract, for a generic tower `R ⊆ OM ⊆ ON` of local rings
satisfying eight typeclass hypotheses plus `hunram`/`hEis`/`hgen`. This file instantiates it
concretely on `R := 𝒪[K]`, `OM := ↥(integralClosureValuationSubring 𝒪[K] M)`,
`ON := ↥(integralClosure OM N)` for `K` complete discretely valued, `M / K` finite separable,
`N / M` finite separable — closing five instance-typeclass gaps that the abstract statement leaves
for the caller to discharge.

## The five gaps and how each closes

1. `Algebra R ON` — `Algebra.compHom ON (algebraMap R OM)`, composing the `R → OM` algebra map
   (`LocalField.algebra` from `TowerValuationSubring.lean`) with `OM`'s own algebra structure on
   `ON` (automatic, `ON` being a `Subalgebra OM N`). Ordinary composition-of-instances work, no
   diamond: `Algebra.compHom_algebraMap_eq` gives `algebraMap R ON = (algebraMap OM ON).comp
   (algebraMap R OM)` for free.
2. `IsScalarTower R OM ON` — `IsScalarTower.of_algebraMap_eq`, fed exactly the equation
   `Algebra.compHom_algebraMap_eq` supplies. Ordinary composition-of-instances work.
3. `Module.Finite R ON` — `Module.Finite.trans`, composing `Module.Finite R OM`
   (`LocalField.finite`, already established) with `Module.Finite OM ON`. The latter needs
   `IsIntegralClosure.finite OM M N (integralClosure OM N)`, which in turn needs `OM` domain,
   integrally closed, and Noetherian: `IsDomain` and `IsIntegrallyClosed` are automatic
   (`integralClosure.isIntegrallyClosedOfFiniteExtension`, `OM` being an integral closure inside a
   field), and `IsNoetherianRing OM` follows from `IsNoetherianRing.of_finite R OM` — `R` itself is
   Noetherian because `IsDiscreteValuationRing R → IsPrincipalIdealRing R` is already a Mathlib
   instance (a field of `IsDiscreteValuationRing`) and PIDs are Noetherian. Ordinary
   composition-of-instances work, no diamond.
4. `IsLocalHom (algebraMap R OM)` — from `hunram`, via `(IsLocalRing.local_hom_TFAE
   (algebraMap R OM)).out 2 0`, the `(𝔪_R).map f ≤ 𝔪_OM → IsLocalHom f` direction of the standard
   TFAE for local ring homomorphisms. A genuine (if one-line) application of an existing Mathlib
   lemma, not previously located.
5. `Algebra.IsSeparable (ResidueField R) (ResidueField OM)` — transported from a hypothesised
   residue-field isomorphism `e : ResidueField OM ≃+* l` with `l` separable over `ResidueField R`,
   *provided* `e` is compatible with the two algebra maps from `ResidueField R`
   (`LocalField.algebraMap_eq_of_ringEquiv` below packages this compatibility as an `AlgEquiv` and
   `AlgEquiv.Algebra.isSeparable` transports separability across it). This is real proof content,
   not a diamond, and the compatibility hypothesis `he` still has to be supplied as a hypothesis of
   the headline theorem below — but it is no longer independent proof burden for a caller using
   `Langlands.UnramifiedExtension.HenselianLocalRing.
   exists_isDiscreteValuationRing_integralClosure_residueField_equiv`'s residue-field isomorphism:
   that theorem's conclusion now *includes* the `he`-shaped compatibility for its own `e`
   (`..._apply_residue_algebraMap`, proved by generalising
   `HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly_apply_residue_root` from the
   generator alone to every point of `R`), so such a caller reads `he` straight off that theorem's
   conclusion instead of proving it separately. See the docstring of
   `exists_adjoin_eq_top_of_tower_of_isEisensteinAt_of_valuationSubring` below for what remains
   open in *fully* internalizing the existence theorem's output (removing `e`/`he` as explicit
   hypotheses of this file's headline theorem altogether).

## Main results

* `LocalField.algebraMap_eq_of_ringEquiv` : packages a residue-field isomorphism compatible with
  the two algebra maps from `ResidueField R` as an `AlgEquiv`, transporting separability (item 5).
* `LocalField.exists_adjoin_eq_top_of_tower_of_isEisensteinAt_of_valuationSubring` : the concrete
  tower monogenicity theorem, `𝒪[K] ⊆ 𝒪[M] ⊆ 𝒪[N]`.
-/

open IsLocalRing ValuativeRel

namespace LocalField

section Instances

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(valuation K).valuationSubring]
  (M : Type*) [Field M] [Algebra K M] [FiniteDimensional K M]
  [ValuationRing ↥(integralClosure ↥(valuation K).valuationSubring M)]
  [IsFractionRing ↥(integralClosure ↥(valuation K).valuationSubring M) M]
  [Algebra.IsSeparable K M]
  {N : Type*} [Field N] [Algebra M N] [FiniteDimensional M N] [Algebra.IsSeparable M N]

/-- **Item 1.** `Algebra R ON`, by composing `R → OM` (`LocalField.algebra`) with `OM`'s own,
automatic, algebra structure on `ON` (`ON` being a `Subalgebra OM N`). -/
noncomputable instance algebra_ON :
    Algebra ↥(valuation K).valuationSubring
      ↥(integralClosure (integralClosureValuationSubring
        ↥(valuation K).valuationSubring M) N) :=
  Algebra.compHom _
    (algebraMap ↥(valuation K).valuationSubring
      ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M))

/-- **Item 2.** `IsScalarTower R OM ON`, by the defining property of `algebra_ON`
(`Algebra.compHom_algebraMap_eq`). -/
instance isScalarTower_ON :
    IsScalarTower ↥(valuation K).valuationSubring
      ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M)
      ↥(integralClosure (integralClosureValuationSubring
        ↥(valuation K).valuationSubring M) N) :=
  IsScalarTower.of_algebraMap_eq fun x =>
    RingHom.congr_fun (Algebra.compHom_algebraMap_eq
      ↥(integralClosure (integralClosureValuationSubring ↥(valuation K).valuationSubring M) N)
      (algebraMap ↥(valuation K).valuationSubring
        ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M))) x

omit [IsUltrametricDist K] [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K] in
/-- **Item 3, groundwork.** `OM` is Noetherian: `R` is Noetherian (a discrete valuation ring is a
principal ideal ring, `IsDiscreteValuationRing.toIsPrincipalIdealRing`, and PIDs are Noetherian),
and `Module.Finite R OM` (`LocalField.finite`) transports Noetherianity up
(`IsNoetherianRing.of_finite`). -/
theorem isNoetherianRing_integralClosureValuationSubring :
    IsNoetherianRing ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M) :=
  haveI := LocalField.finite (R := ↥(valuation K).valuationSubring) (M := M) K
  IsNoetherianRing.of_finite ↥(valuation K).valuationSubring
    ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M)

omit [IsUltrametricDist K] [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K] in
/-- **Item 3.** `Module.Finite OM ON`, from `IsIntegralClosure.finite` — `OM` is a domain and
integrally closed automatically (an integral closure inside a field,
`integralClosure.isIntegrallyClosedOfFiniteExtension`) and Noetherian
(`isNoetherianRing_integralClosureValuationSubring`), `IsFractionRing OM M` and
`Algebra.IsSeparable M N` are ambient hypotheses. -/
theorem finite_ON :
    Module.Finite ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M)
      ↥(integralClosure (integralClosureValuationSubring
        ↥(valuation K).valuationSubring M) N) :=
  haveI := isNoetherianRing_integralClosureValuationSubring K M
  haveI := IsIntegralClosure.finite
    ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M) M N
    (integralClosure (integralClosureValuationSubring ↥(valuation K).valuationSubring M) N)
  inferInstanceAs (Module.Finite
    ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M)
    (integralClosure (integralClosureValuationSubring ↥(valuation K).valuationSubring M) N))

omit [IsUltrametricDist K] [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K] in
/-- **Item 3, assembled.** `Module.Finite R ON`, composing `Module.Finite R OM`
(`LocalField.finite`) with `Module.Finite OM ON` (`finite_ON`) via `Module.Finite.trans`. -/
theorem finite_ON' :
    Module.Finite ↥(valuation K).valuationSubring
      ↥(integralClosure (integralClosureValuationSubring
        ↥(valuation K).valuationSubring M) N) :=
  haveI := LocalField.finite (R := ↥(valuation K).valuationSubring) (M := M) K
  haveI := finite_ON K M (N := N)
  Module.Finite.trans ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M)
    ↥(integralClosure (integralClosureValuationSubring ↥(valuation K).valuationSubring M) N)

omit [IsUltrametricDist K] [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
  [IsDiscreteValuationRing ↥(valuation K).valuationSubring] [FiniteDimensional K M]
  [Algebra.IsSeparable K M] in
/-- **Item 4.** `IsLocalHom (algebraMap R OM)` from unramifiedness, via the standard TFAE for
local ring homomorphisms (`IsLocalRing.local_hom_TFAE`): `(𝔪_R).map f ≤ 𝔪_OM` (which `hunram`
gives as an equality, in particular an inequality) implies `IsLocalHom f`. -/
theorem isLocalHom_of_map_maximalIdeal_eq
    (hunram : Ideal.map (algebraMap ↥(valuation K).valuationSubring
        ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M))
        (maximalIdeal ↥(valuation K).valuationSubring) =
      maximalIdeal ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M)) :
    IsLocalHom (algebraMap ↥(valuation K).valuationSubring
      ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M)) :=
  ((IsLocalRing.local_hom_TFAE (algebraMap ↥(valuation K).valuationSubring
    ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M))).out 2 0).mp
    (le_of_eq hunram)

end Instances

/-- **Item 5.** A residue-field isomorphism `e : ResidueField OM ≃+* l` compatible with the two
algebra maps from `ResidueField R` (`he`) transports separability from `l` to `ResidueField OM`:
package `e` as an `AlgEquiv` via `he` (`AlgEquiv.ofRingEquiv`) and transport
(`AlgEquiv.Algebra.isSeparable`) along its inverse. -/
theorem algebraMap_eq_of_ringEquiv {R OM : Type*} [CommRing R] [CommRing OM] [IsLocalRing R]
    [IsLocalRing OM] [Algebra R OM] [IsLocalHom (algebraMap R OM)]
    {l : Type*} [Field l] [Algebra (ResidueField R) l] (e : ResidueField OM ≃+* l)
    (he : ∀ x : ResidueField R, e (algebraMap (ResidueField R) (ResidueField OM) x) =
      algebraMap (ResidueField R) l x) [Algebra.IsSeparable (ResidueField R) l] :
    Algebra.IsSeparable (ResidueField R) (ResidueField OM) :=
  AlgEquiv.Algebra.isSeparable (AlgEquiv.ofRingEquiv he).symm

/-- **Item 5, restated at the level of `R` rather than `ResidueField R`.** The same transport as
`algebraMap_eq_of_ringEquiv`, but with the compatibility hypothesis `he` phrased via elements of
`R` and `residue`/`algebraMap` rather than `algebraMap (ResidueField R) (ResidueField OM)` — this
is the form a concrete instantiation can state without first needing the
`Algebra (ResidueField R) (ResidueField OM)` instance in scope (that instance itself needs
`IsLocalHom (algebraMap R OM)`, which is not yet available at the point `he`'s *type* would
otherwise be elaborated). `IsLocalRing.ResidueField.residue_surjective` reduces the general
statement to this one. -/
theorem algebraMap_eq_of_ringEquiv_of_forall {R OM : Type*} [CommRing R] [CommRing OM]
    [IsLocalRing R] [IsLocalRing OM] [Algebra R OM] [IsLocalHom (algebraMap R OM)]
    {l : Type*} [Field l] [Algebra (ResidueField R) l] (e : ResidueField OM ≃+* l)
    (he : ∀ x : R, e (residue OM (algebraMap R OM x)) =
      algebraMap (ResidueField R) l (residue R x)) [Algebra.IsSeparable (ResidueField R) l] :
    Algebra.IsSeparable (ResidueField R) (ResidueField OM) :=
  algebraMap_eq_of_ringEquiv e (fun x => by
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rw [IsLocalRing.ResidueField.algebraMap_residue]
    exact he x)

/-- **Serre's tower monogenicity theorem, concretely: `𝒪[K] ⊆ 𝒪[M] ⊆ 𝒪[N]`.**

For `K` complete discretely valued, `M / K` finite separable with `𝒪_M` presented as the
`ValuationSubring`-coerced integral closure `integralClosureValuationSubring 𝒪[K] M` (a valuation
ring with fraction field `M`, e.g. as produced by
`Langlands.UnramifiedExtension.HenselianLocalRing.
exists_isDiscreteValuationRing_integralClosure_residueField_equiv`), and `N / M` finite separable,
`𝒪_N := integralClosure 𝒪_M N` is monogenic over `𝒪[K]` whenever:

* `𝒪_M / 𝒪[K]` is unramified (`hunram`) with separable residue extension (`e`, `he`, `l` separable
  over `ResidueField 𝒪[K]`) — the two facts Serre's tower argument needs from the unramified half;
* `𝒪_N = 𝒪_M[π]` for a `π` whose minimal polynomial over `𝒪_M` is Eisenstein at `𝔪_{𝒪_M}` (`hint`,
  `hEis`, `hgen`) — what Serre's tower argument needs from the totally ramified half.

This is `Langlands.TowerMonogenic.LocalField.exists_adjoin_eq_top_of_tower_of_isEisensteinAt`
instantiated at `R := 𝒪[K]`, `OM := ↥(integralClosureValuationSubring 𝒪[K] M)`,
`ON := ↥(integralClosure OM N)`, discharging its eight typeclass hypotheses via `algebra_ON`,
`isScalarTower_ON`, `finite_ON'`, `LocalField.finite`, `isLocalHom_of_map_maximalIdeal_eq`, and
`algebraMap_eq_of_ringEquiv`.

**Status of hypothesis `he`.** This theorem still takes the residue-field isomorphism's
compatibility with the two algebra maps from `ResidueField 𝒪[K]` (`he`) as an explicit hypothesis,
rather than deriving it internally — but the earlier gap in *proving* `he` for a concrete `e` is
closed: `Langlands.UnramifiedExtension.HenselianLocalRing.
exists_isDiscreteValuationRing_integralClosure_residueField_equiv`'s conclusion now states, for its
own constructed `e`, exactly the `he`-shaped compatibility this theorem needs (added via
`HenselianLocalRing.residueField_equiv_adjoinRoot_lift_minpoly_apply_residue_algebraMap`, the
generalisation of `..._apply_residue_root` from the single generator to every point of `R`). A
caller with a concrete `K`, `β₀` in hand runs that existence theorem, obtains `e` together with a
ready-made proof of `he`, and passes both straight into this theorem — no separate `he`
verification step remains.

**What is still open: fully removing `e`/`he`/`l`/`hunram` as explicit parameters of this
theorem.**

The instance gap that previously blocked this — `HenselianLocalRing R` for `R :=
↥(valuation K).valuationSubring` under this file's lighter bundle — is now closed:
`Langlands.UnramifiedExtension.HenselianLocalRing.henselianLocalRing_of_valuationSubring` derives it
from `CompleteSpace K` plus `Finite (ResidueField R)` (via `LocallyCompactSpace K`, using the
proper-space characterization of complete-DVR-valued fields with finite residue field, then
`IsNonarchimedeanLocalField K`, then the pre-existing `henselianLocalRing` instance). So a caller
under this file's lighter bundle, given `Finite (ResidueField R)`, a primitive element `β₀` of a
separable extension `l / ResidueField R`, and its integrality/primitivity data, can now run
`HenselianLocalRing.exists_isDiscreteValuationRing_integralClosure_residueField_equiv` themselves —
something they could not do before, for lack of `HenselianLocalRing R`.

What that existence theorem hands back, though, is not data about an arbitrary caller-supplied `M`:
it *constructs* its own unramified extension `M := K⟮x⟯` (for `x` a root, in an algebraically closed
`L ⊇ K`, of a monic lift of `minpoly (ResidueField R) β₀`) and proves `e`/`he`/`hunram` for that
specific `M`. Wiring this into the present theorem so that `e`/`he`/`l`/`hunram` disappear from the
*signature* — while `M` and `N` remain free, caller-supplied finite separable extensions, exactly as
they are now — is not achievable, and not for a proof-search reason: `hunram` (`𝔪_R · OM = 𝔪_OM`,
i.e. `M / K` unramified) is a genuine mathematical constraint on `M`, not a derivable fact about
finite separable extensions in general. It is false for a ramified example (e.g. `K = ℚ_p`, `M =
ℚ_p(p^{1/2})`, where `𝔪_R · OM = (p) ≠ (p^{1/2}) = 𝔪_OM`), and it is load-bearing in the abstract
theorem's proof (`LocalField.map_maximalIdeal_eq_of_unramified` in `TowerMonogenic.lean`, which
identifies the two candidate `κ_OM`-algebra structures on `ON ⧸ 𝔪_R·ON` and is what the rest of
`exists_adjoin_eq_top_of_tower` is built on) — so it cannot be dropped while `M` stays universally
quantified.

Eliminating it *would* require replacing this theorem's `M` with the internally-constructed `K⟮x⟯`
outright — i.e. restating the whole theorem with the unramified half existentially bound (`∃ x, ...`)
and the totally-ramified half (`N`, `π`, `hint`, `hEis`, `hgen`) universally quantified *inside* that
existential, since `N`'s type and its `Algebra` instance over `M` cannot be declared in the signature
before `x` (hence `M := K⟮x⟯`) is produced. That is a different theorem shape from the one below —
`∃ M, ∀ N, ...` instead of `∀ M, ∀ N, (hypotheses on M including hunram) → ...` — not a term this
theorem's existing statement can be strengthened into by filling in a proof. Investigated and left
open here as a genuine design question (how to state a fully unconditional tower-monogenicity
corollary in this shape), not a lemma-lookup or tactic gap. -/
theorem exists_adjoin_eq_top_of_tower_of_isEisensteinAt_of_valuationSubring
    (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
    [(NormedField.valuation (K := K)).Compatible] [CompleteSpace K]
    [IsDiscreteValuationRing ↥(valuation K).valuationSubring]
    (M : Type*) [Field M] [Algebra K M] [FiniteDimensional K M]
    [ValuationRing ↥(integralClosure ↥(valuation K).valuationSubring M)]
    [IsFractionRing ↥(integralClosure ↥(valuation K).valuationSubring M) M]
    [Algebra.IsSeparable K M]
    (N : Type*) [Field N] [Algebra M N] [FiniteDimensional M N] [Algebra.IsSeparable M N]
    {l : Type*} [Field l]
    [Algebra (ResidueField ↥(valuation K).valuationSubring) l]
    (e : ResidueField ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M) ≃+* l)
    (hunram : Ideal.map
        (algebraMap ↥(valuation K).valuationSubring
          ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M))
        (maximalIdeal ↥(valuation K).valuationSubring) =
      maximalIdeal ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M))
    (he : ∀ x : ↥(valuation K).valuationSubring,
      e (residue ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M)
          (algebraMap ↥(valuation K).valuationSubring
            ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M) x)) =
        algebraMap (ResidueField ↥(valuation K).valuationSubring) l
          (residue ↥(valuation K).valuationSubring x))
    [Algebra.IsSeparable (ResidueField ↥(valuation K).valuationSubring) l]
    {π : ↥(integralClosure
        ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M) N)}
    (hint : IsIntegral ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M) π)
    (hEis : Polynomial.IsEisensteinAt
      (minpoly ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M) π)
      (maximalIdeal ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M)))
    (hgen : Algebra.adjoin ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M)
        ({π} : Set ↥(integralClosure
          ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M) N)) = ⊤) :
    ∃ γ : ↥(integralClosure
        ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M) N),
      Algebra.adjoin ↥(valuation K).valuationSubring ({γ} : Set ↥(integralClosure
        ↥(integralClosureValuationSubring ↥(valuation K).valuationSubring M) N)) = ⊤ :=
  haveI := isLocalHom_of_map_maximalIdeal_eq K M hunram
  haveI := LocalField.finite (R := ↥(valuation K).valuationSubring) (M := M) K
  haveI := finite_ON' K M (N := N)
  haveI := algebraMap_eq_of_ringEquiv_of_forall e he
  exists_adjoin_eq_top_of_tower_of_isEisensteinAt hunram hint hEis hgen

end LocalField
