import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Quotient

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

What is genuinely missing and left as `sorry` / future work here:

- The isomorphism `IdeleGroup K ≃ₜ* FiniteIdeleGroup K × (InfiniteAdeleRing K)ˣ` (the Lean 3
  `I_K.as_prod`) and the associated projection `IdeleGroup.fst`.
- Injectivity of the diagonal embedding `Kˣ →* IdeleGroup R K` (Lean 3
  `inj_units_K.injective`), which in Lean 3 needed `HeightOneSpectrum R` to be nonempty (i.e.
  `R` not a field); the Lean 4 proof should go via injectivity of
  `algebraMap K (AdeleRing R K)` (`NumberField.AdeleRing.algebraMap_injective`, which already
  exists in Mathlib4) plus a general fact that `Units.map` of an injective monoid hom between
  cancellative monoids is injective.
- The map from the idèle group to the group of fractional ideals / the ideal class group
  (Lean 3 `map_to_fractional_ideals`, `I_K.map_to_class_group`, `C_K.map_to_class_group`),
  which is the deepest part of the original development and is not attempted here.

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
    Function.Injective (diagonalEmbedding R K) := by
  sorry

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
