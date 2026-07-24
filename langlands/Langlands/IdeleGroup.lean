import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The idèle group and idèle class group

This is a first-pass port of the idèle group / idèle class group development from
María Inés de Frutos-Fernández's Lean 3 `ideles` project
(`github.com/mariainesdff/ideles`, files `ideles_R.lean` / `ideles_K.lean`) to Lean 4 /
Mathlib4.

Mathlib4 already contains the adèle ring (`NumberField.AdeleRing`, split as
`InfiniteAdeleRing × FiniteAdeleRing`) together with its topology, its `K`-algebra
structure, and the subgroup of principal adèles (`NumberField.AdeleRing.principalSubgroup`).
What is missing (as of this writing) is everything downstream of the units: the idèle
group itself, the diagonal embedding of `Kˣ`, and the idèle class group as a quotient.

## Main definitions

- `NumberField.IdeleGroup R K` : the idèle group of `K`, defined as the unit group of the
  adèle ring `NumberField.AdeleRing R K`. Here `R` is a Dedekind domain with fraction field
  `K` (the intended use is `R = 𝓞 K`, but as with `AdeleRing` the definition is stated more
  generally to allow e.g. `R = ℤ`, `K = ℚ`).
- `NumberField.IdeleGroup.principalSubgroup R K` : the subgroup of principal idèles
  `(x)ᵥ`, `x ∈ Kˣ`.
- `NumberField.FiniteIdeleGroup R K`, `NumberField.InfiniteIdeleGroup K` : the finite and
  infinite idèle groups, and `NumberField.IdeleGroup.equivProd` : the topological-group
  isomorphism `IdeleGroup R K ≃ₜ* InfiniteIdeleGroup K × FiniteIdeleGroup R K`, together with
  the projections `IdeleGroup.infinitePart` / `IdeleGroup.finitePart`.
- `NumberField.IdeleGroup.toFractionalIdealHom`, `NumberField.IdeleGroup.toClassGroup` : the
  maps from the idèle group to the group of fractional ideals and to the ideal class group
  of `K`.
- `NumberField.IdeleClassGroup R K` : the idèle class group, defined as the quotient of the
  idèle group by the principal idèles.

## Implementation notes

Both `IdeleGroup R K` and `IdeleClassGroup R K` get their topology and topological-group
structure "for free" from general Mathlib instances:

- `Units.instTopologicalSpaceUnits` puts a topology on the units of any topological monoid
  (via the embedding `u ↦ (u, u⁻¹)` into `M × Mᵐᵒᵖ`), and
  `instance [ContinuousMul α] : IsTopologicalGroup αˣ` (in
  `Mathlib.Topology.Algebra.Group.Basic`) upgrades this to a topological group whenever the
  ambient monoid has continuous multiplication -- which `AdeleRing R K` does, being a
  topological ring.
- `QuotientGroup.instTopologicalSpace` and `QuotientGroup.instIsTopologicalGroup` (in
  `Mathlib.Topology.Algebra.Group.Quotient`) give the quotient topology and, since
  `IdeleGroup R K` is commutative (so every subgroup is normal), a topological group
  structure on the quotient.

This means the topological bookkeeping that occupies a significant fraction of the Lean 3
`ideles_R.lean` / `ideles_K.lean` files (`finite_idele_group'.topological_space`,
`finite_idele_group'.topological_group`, `topological_group_quotient`, ...) is essentially
free in Lean 4, since Mathlib4's `AdeleRing` and `RestrictedProduct` infrastructure already
carries the relevant topology and continuity lemmas.

Injectivity of the diagonal embedding `diagonalEmbedding_injective` (the Lean 3
`inj_units_K.injective`) is now proved: it follows directly from injectivity of
`algebraMap K (AdeleRing R K)` (`NumberField.AdeleRing.algebraMap_injective`, already in
Mathlib4) via `Units.map_injective`, with no need for the Lean 3 argument via nonempty
`HeightOneSpectrum R`.

The splitting `IdeleGroup R K ≃ₜ* FiniteIdeleGroup K × (InfiniteAdeleRing K)ˣ` (Lean 3
`I_K.as_prod`) is also done, as `IdeleGroup.equivProd`, together with the projections
`IdeleGroup.infinitePart` / `IdeleGroup.finitePart` (Lean 3 `I_K.fst`). This is transported
directly from the definitional equality `AdeleRing R K = InfiniteAdeleRing K × FiniteAdeleRing R K`
via the general topological-group isomorphism between the units of a product monoid and the
product of the unit groups (`MulEquiv.prodUnits` / `Homeomorph.prodUnits`).

The map from the idèle group to the group of fractional ideals (`IdeleGroup.toFractionalIdealHom`,
Lean 3 `map_to_fractional_ideals`) and its composite with the class group quotient
(`IdeleGroup.toClassGroup`, Lean 3 `I_K.map_to_class_group` / `C_K.map_to_class_group`) send an
idèle `a` to `∏_v v^(exponent a v)`, where `exponent a v` is the `v`-adic valuation of the finite
component of `a`. The two supporting facts (`IdeleGroup.toFractionalIdeal_ne_zero`,
`IdeleGroup.toFractionalIdeal_mul`) are proved via `finprod_ne_zero` (using the `Semifield`
structure on nonzero fractional ideals of a Dedekind domain) and via an auxiliary lemma
`IdeleGroup.exponent_mul` showing `exponent` is additive in the idèle, which itself follows from
multiplicativity of the valuation `Valued.v` at each place `v`.

## References
* María Inés de Frutos-Fernández, *ideles* (Lean 3), `github.com/mariainesdff/ideles`.
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
idèle group, idèle class group, number field
-/

noncomputable section

namespace NumberField

open IsDedekindDomain

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-! ### The idèle group -/

/-- The idèle group of `K` is the unit group of its adèle ring.

As with `NumberField.AdeleRing`, the definition is stated for a Dedekind domain `R` with
fraction field `K`; the intended instantiation is `R = 𝓞 K`. -/
def IdeleGroup := (AdeleRing R K)ˣ
deriving CommGroup, TopologicalSpace

namespace IdeleGroup

/-- The idèle group is a topological group: this comes for free from the fact that units of
any topological ring (here `AdeleRing R K`) form a topological group. -/
instance : IsTopologicalGroup (IdeleGroup R K) :=
  inferInstanceAs (IsTopologicalGroup (AdeleRing R K)ˣ)

instance : Inhabited (IdeleGroup R K) := ⟨1⟩

/-- The diagonal embedding `x ↦ (x)ᵥ` of `Kˣ` into the idèle group of `K`. -/
def diagonalEmbedding : Kˣ →* IdeleGroup R K :=
  Units.map (algebraMap K (AdeleRing R K)).toMonoidHom

@[simp]
theorem coe_diagonalEmbedding_apply (x : Kˣ) :
    Units.val (α := AdeleRing R K) (diagonalEmbedding R K x) =
      algebraMap K (AdeleRing R K) (x : K) := rfl

/-- The subgroup of principal idèles `(x)ᵥ`, `x ∈ Kˣ`. -/
abbrev principalSubgroup : Subgroup (IdeleGroup R K) := (diagonalEmbedding R K).range

/-- The diagonal embedding of `K*` into the idèle group is injective, at least once `K` is a
number field. In the Lean 3 development (`inj_units_K.injective`) this followed from
injectivity of `inj_K : K →+* finite_adele_ring' R K`, which needed `R` to not be a field
(equivalently, `HeightOneSpectrum R` nonempty); here it should follow instead from
`NumberField.AdeleRing.algebraMap_injective`. -/
theorem diagonalEmbedding_injective [NumberField K] :
    Function.Injective (diagonalEmbedding R K) :=
  Units.map_injective (AdeleRing.algebraMap_injective R K)

end IdeleGroup

/-! ### The finite and infinite idèle groups -/

/-- The group of finite idèles of `K`: the unit group of the finite adèle ring
`IsDedekindDomain.FiniteAdeleRing R K`. This is the Lean 3 `finite_idele_group' R K`. -/
def FiniteIdeleGroup := (FiniteAdeleRing R K)ˣ
deriving CommGroup, TopologicalSpace

/-- The group of infinite idèles of `K`: the unit group of the infinite adèle ring
`NumberField.InfiniteAdeleRing K`. -/
def InfiniteIdeleGroup := (InfiniteAdeleRing K)ˣ
deriving CommGroup, TopologicalSpace

namespace FiniteIdeleGroup

instance : IsTopologicalGroup (FiniteIdeleGroup R K) :=
  inferInstanceAs (IsTopologicalGroup (FiniteAdeleRing R K)ˣ)

instance : Inhabited (FiniteIdeleGroup R K) := ⟨1⟩

end FiniteIdeleGroup

namespace InfiniteIdeleGroup

instance : IsTopologicalGroup (InfiniteIdeleGroup K) :=
  inferInstanceAs (IsTopologicalGroup (InfiniteAdeleRing K)ˣ)

instance : Inhabited (InfiniteIdeleGroup K) := ⟨1⟩

end InfiniteIdeleGroup

namespace IdeleGroup

/-- The idèle group splits, as a topological group, as the product of the infinite and finite
idèle groups. This is transported directly from the definitional splitting
`AdeleRing R K = InfiniteAdeleRing K × FiniteAdeleRing R K` via the general fact that the units
of a product monoid are (topologically) the product of the unit groups
(`MulEquiv.prodUnits` / `Homeomorph.prodUnits`). This is the Lean 3 `I_K.as_prod`. -/
def equivProd : IdeleGroup R K ≃ₜ* InfiniteIdeleGroup K × FiniteIdeleGroup R K :=
  ContinuousMulEquiv.mk' Homeomorph.prodUnits (map_mul MulEquiv.prodUnits)

/-- The projection of an idèle onto its infinite component. -/
def infinitePart : IdeleGroup R K →* InfiniteIdeleGroup K :=
  (MonoidHom.fst _ _).comp (equivProd R K).toMonoidHom

/-- The projection of an idèle onto its finite component. This is the Lean 3 `I_K.fst`. -/
def finitePart : IdeleGroup R K →* FiniteIdeleGroup R K :=
  (MonoidHom.snd _ _).comp (equivProd R K).toMonoidHom

end IdeleGroup

/-! ### The map to fractional ideals -/

namespace IdeleGroup

open Filter IsDedekindDomain.HeightOneSpectrum

variable {R K}

/-- The `v`-adic exponent of a finite idèle: if `a` is a finite idèle, `exponent a v` is the
integer `n` such that the `v`-component of `a` has valuation `ϖᵥ ^ (-n)` for a uniformizer `ϖᵥ`,
i.e. the multiplicity of the maximal ideal `v` in the fractional ideal determined by `a`. -/
noncomputable def exponent (a : IdeleGroup R K) (v : IsDedekindDomain.HeightOneSpectrum R) : ℤ :=
  Multiplicative.toAdd
    (WithZero.unzero
      (x := Valued.v ((RestrictedProduct.unitsEquiv _ (finitePart R K a) v : v.adicCompletion K)))
      ((Valued.v.ne_zero_iff).mpr (Units.ne_zero _)))

/-- Only finitely many places `v` have nonzero exponent: this reflects the fact that a finite
idèle lies in the local units `𝒪ᵥˣ` for all but finitely many `v`. -/
theorem exponent_eventually_zero (a : IdeleGroup R K) :
    ∀ᶠ v in cofinite, exponent a v = 0 := by
  filter_upwards [IsDedekindDomain.FiniteAdeleRing.unitsEquiv_finite_valued_eq_one
    (finitePart R K a)] with v hv
  simp only [exponent, toAdd_eq_zero]
  rw [← WithZero.coe_inj, WithZero.coe_unzero, WithZero.coe_one]
  exact hv

/-- The fractional ideal determined by an idèle `a`: the product `∏_v v^(exponent a v)` over the
maximal ideals of `R`, i.e. the ideal-theoretic incarnation of the divisor of `a`. This is the
Lean 3 `map_to_fractional_ideals`. -/
noncomputable def toFractionalIdeal (a : IdeleGroup R K) :
    FractionalIdeal (nonZeroDivisors R) K :=
  ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R,
    (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ exponent a v

theorem toFractionalIdeal_ne_zero (a : IdeleGroup R K) : toFractionalIdeal a ≠ 0 := by
  refine finprod_ne_zero fun v => ?_
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- The `v`-adic exponent is additive in the idèle: `exponent (a * b) v = exponent a v +
exponent b v`. This reflects the multiplicativity of the valuation `Valued.v` at each place. -/
theorem exponent_mul (a b : IdeleGroup R K) (v : IsDedekindDomain.HeightOneSpectrum R) :
    exponent (a * b) v = exponent a v + exponent b v := by
  have hcomp : (RestrictedProduct.unitsEquiv _ (finitePart R K (a * b)) v : v.adicCompletion K) =
      (RestrictedProduct.unitsEquiv _ (finitePart R K a) v : v.adicCompletion K) *
        (RestrictedProduct.unitsEquiv _ (finitePart R K b) v : v.adicCompletion K) := by
    rw [map_mul (finitePart R K)]
    exact congrArg (fun x => (x v : v.adicCompletion K))
      (map_mul (RestrictedProduct.unitsEquiv
        (fun v : IsDedekindDomain.HeightOneSpectrum R => v.adicCompletion K))
        (finitePart R K a) (finitePart R K b))
  have hval : Valued.v ((RestrictedProduct.unitsEquiv _ (finitePart R K (a * b)) v :
      v.adicCompletion K)) =
      Valued.v ((RestrictedProduct.unitsEquiv _ (finitePart R K a) v : v.adicCompletion K)) *
        Valued.v ((RestrictedProduct.unitsEquiv _ (finitePart R K b) v : v.adicCompletion K)) := by
    rw [hcomp, map_mul]
  set h1 : Valued.v ((RestrictedProduct.unitsEquiv _ (finitePart R K (a * b)) v :
      v.adicCompletion K)) ≠ 0 := (Valued.v.ne_zero_iff).mpr (Units.ne_zero _) with hh1
  show (WithZero.unzero h1).toAdd = exponent a v + exponent b v
  rw [WithZero.toAdd_unzero_eq_iff]
  simp only [exponent]
  rw [ofAdd_add, WithZero.coe_mul, ofAdd_toAdd, ofAdd_toAdd, WithZero.coe_unzero,
    WithZero.coe_unzero]
  exact hval

theorem toFractionalIdeal_mul (a b : IdeleGroup R K) :
    toFractionalIdeal (a * b) = toFractionalIdeal a * toFractionalIdeal b := by
  have hfa : Function.HasFiniteMulSupport
      fun v : IsDedekindDomain.HeightOneSpectrum R =>
        (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ exponent a v :=
    Set.Finite.subset (Filter.eventually_cofinite.mp (exponent_eventually_zero a))
      (fun v hv => by simp only [Function.mem_mulSupport] at hv ⊢; exact fun h => hv (by
        rw [h, zpow_zero]))
  have hfb : Function.HasFiniteMulSupport
      fun v : IsDedekindDomain.HeightOneSpectrum R =>
        (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ exponent b v :=
    Set.Finite.subset (Filter.eventually_cofinite.mp (exponent_eventually_zero b))
      (fun v hv => by simp only [Function.mem_mulSupport] at hv ⊢; exact fun h => hv (by
        rw [h, zpow_zero]))
  unfold toFractionalIdeal
  rw [← finprod_mul_distrib hfa hfb]
  refine finprod_congr fun v => ?_
  rw [exponent_mul, zpow_add₀ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)]

/-- The multiplicative map from the idèle group to the group of (nonzero) fractional ideals of
`K`, sending an idèle to the fractional ideal it determines via its valuations at each finite
place. This is the Lean 3 `I_K.map_to_fractional_ideals`. -/
noncomputable def toFractionalIdealHom :
    IdeleGroup R K →* (FractionalIdeal (nonZeroDivisors R) K)ˣ :=
  MonoidHom.mk' (fun a => Units.mk0 (toFractionalIdeal a) (toFractionalIdeal_ne_zero a))
    (fun a b => Units.ext (toFractionalIdeal_mul a b))

/-- The composite map from the idèle group to the ideal class group of `K`, sending an idèle to
the class of the fractional ideal it determines. This is the Lean 3 `I_K.map_to_class_group`. -/
noncomputable def toClassGroup : IdeleGroup R K →* ClassGroup R :=
  (ClassGroup.mk K).comp toFractionalIdealHom

end IdeleGroup

/-! ### The idèle class group -/

/-- The idèle class group of `K` is the quotient of the idèle group of `K` by the subgroup of
principal idèles. -/
def IdeleClassGroup := IdeleGroup R K ⧸ IdeleGroup.principalSubgroup R K

namespace IdeleClassGroup

instance : CommGroup (IdeleClassGroup R K) :=
  inferInstanceAs (CommGroup (IdeleGroup R K ⧸ IdeleGroup.principalSubgroup R K))

instance : TopologicalSpace (IdeleClassGroup R K) :=
  inferInstanceAs (TopologicalSpace (IdeleGroup R K ⧸ IdeleGroup.principalSubgroup R K))

/-- The idèle class group is a topological group. Since `IdeleGroup R K` is commutative every
subgroup (in particular `principalSubgroup`) is normal, so this comes for free from the
general topological-quotient-group instance for commutative topological groups. -/
instance : IsTopologicalGroup (IdeleClassGroup R K) :=
  inferInstanceAs (IsTopologicalGroup (IdeleGroup R K ⧸ IdeleGroup.principalSubgroup R K))

/-- The natural quotient map from the idèle group to the idèle class group. -/
def mk : IdeleGroup R K →* IdeleClassGroup R K := QuotientGroup.mk' _

theorem mk_surjective : Function.Surjective (mk R K) := QuotientGroup.mk'_surjective _

theorem continuous_mk : Continuous (mk R K) := QuotientGroup.continuous_mk

end IdeleClassGroup

end NumberField
