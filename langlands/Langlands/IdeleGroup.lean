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
- `NumberField.IdeleClassGroup.toClassGroup` : the descent of `IdeleGroup.toClassGroup` along the
  quotient by principal idèles, since these map to the trivial ideal class
  (`IdeleGroup.toClassGroup_diagonalEmbedding`).
- `NumberField.IdeleGroup.toClassGroup_eq_one_iff` : an idèle maps to the trivial class iff its
  `toFractionalIdeal` is principal, i.e. the kernel of `toClassGroup`.
- `NumberField.IdeleClassGroup.ker_mk`, `NumberField.IdeleClassGroup.mulExact_diagonalEmbedding_mk` :
  the kernel of the quotient map `mk : IdeleGroup R K →* IdeleClassGroup R K` is the principal
  idèles, packaged as the exactness of `1 → Kˣ → IdeleGroup R K → IdeleClassGroup R K → 1`.
- `NumberField.IdeleClassGroup.ker_toClassGroup` : the kernel of the map to `ClassGroup R`,
  as the image under `mk` of `ker IdeleGroup.toClassGroup`.
- `NumberField.IdeleGroup.content` : the idèle norm (content map) `IdeleGroup R K → ℝ`, trivial
  on principal idèles (`content_diagonalEmbedding`, the adelic product formula).
- `NumberField.IdeleGroup.normMap` : the intended type of the idèle norm map for a finite
  extension `L / K`; a `sorry` stub, since the local norm maps it needs are not yet in Mathlib
  (see the survey in the "norm map on idèles" section below).

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

Principal idèles map to the trivial ideal class: `IdeleGroup.toFractionalIdeal_diagonalEmbedding`
shows `toFractionalIdeal (diagonalEmbedding x) = (x⁻¹)` (a principal fractional ideal), from which
`IdeleGroup.toClassGroup_diagonalEmbedding` deduces `toClassGroup (diagonalEmbedding x) = 1` via
`ClassGroup.mk_eq_one_iff`. The identification of `toFractionalIdeal (diagonalEmbedding x)` uses
`FractionalIdeal.finprod_heightOneSpectrum_factorization_principal_fraction` together with the
auxiliary computation `IdeleGroup.exponent_diagonalEmbedding`, which expresses the `v`-adic
exponent of a principal idèle `(x)ᵥ` (for `x = n/d`, `n : R`, `d ∈ R⁰`) as a difference of
`Associates.count` factorization multiplicities, matched against the local valuation via
`IsDedekindDomain.HeightOneSpectrum.valuation_of_mk'` and the exponential/logarithm API for
`WithZero (Multiplicative ℤ)` (`WithZero.log`, `WithZero.log_div`, `WithZero.log_exp`).

This gives `IdeleGroup.principalSubgroup_le_ker_toClassGroup`, so `toClassGroup` descends along
the quotient by `QuotientGroup.lift` to `NumberField.IdeleClassGroup.toClassGroup :
IdeleClassGroup R K →* ClassGroup R`. Surjectivity of this descended map
(`IdeleClassGroup.toClassGroup_surjective`) is proved via `IdeleGroup.exists_toFractionalIdeal_eq`:
every nonzero fractional ideal `I` arises as `toFractionalIdeal a` for some idèle `a`, built with
local finite component at each place `v` a field element of valuation `WithZero.exp (count K v I)`
(furnished by surjectivity of the local valuation,
`IsDedekindDomain.HeightOneSpectrum.valuation_surjective`, applied pointwise via `choose`), which
is a local unit (valuation `1`) at all but finitely many `v` since `count K v I` is eventually `0`
(`FractionalIdeal.finite_factors`), and hence assembles into a genuine unit of the finite adèle
ring via `RestrictedProduct.mkUnit`. Combined with `ClassGroup.mk0_surjective` (every ideal class
is represented by a nonzero integral ideal), this gives surjectivity onto `ClassGroup R`.

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

/-- The local component at `v` of the finite part of an idèle `a`, as an element of the `v`-adic
completion `v.adicCompletion K`. -/
def localComponent (a : IdeleGroup R K) (v : HeightOneSpectrum R) : v.adicCompletion K :=
  (RestrictedProduct.unitsEquiv _ (finitePart R K a) v : v.adicCompletion K)

theorem localComponent_mul (a b : IdeleGroup R K) (v : HeightOneSpectrum R) :
    localComponent (a * b) v = localComponent a v * localComponent b v := by
  show (RestrictedProduct.unitsEquiv _ (finitePart R K (a * b)) v : v.adicCompletion K) = _
  rw [map_mul (finitePart R K)]
  exact congrArg (fun x => (x v : v.adicCompletion K))
    (map_mul (RestrictedProduct.unitsEquiv (fun v : HeightOneSpectrum R => v.adicCompletion K))
      (finitePart R K a) (finitePart R K b))

/-- The `v`-adic exponent of a finite idèle: if `a` is a finite idèle, `exponent a v` is the
integer `n` such that the `v`-component of `a` has valuation `ϖᵥ ^ (-n)` for a uniformizer `ϖᵥ`,
i.e. the multiplicity of the maximal ideal `v` in the fractional ideal determined by `a`. -/
noncomputable def exponent (a : IdeleGroup R K) (v : HeightOneSpectrum R) : ℤ :=
  Multiplicative.toAdd
    (WithZero.unzero (x := Valued.v (localComponent a v))
      ((Valued.v.ne_zero_iff).mpr (Units.ne_zero _)))

theorem exponent_eq_log (a : IdeleGroup R K) (v : HeightOneSpectrum R) :
    exponent a v = WithZero.log (Valued.v (localComponent a v)) := by
  set h : Valued.v (localComponent a v) ≠ 0 := (Valued.v.ne_zero_iff).mpr (Units.ne_zero _) with hh
  rw [← WithZero.coe_unzero h]
  rfl

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
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ exponent a v

theorem toFractionalIdeal_ne_zero (a : IdeleGroup R K) : toFractionalIdeal a ≠ 0 := by
  refine finprod_ne_zero fun v => ?_
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- Only finitely many places `v` contribute a nontrivial factor `v ^ exponent a v` to
`toFractionalIdeal a`: this is `exponent_eventually_zero` repackaged as a `HasFiniteMulSupport`
statement, ready to feed to `finprod_mul_distrib`. -/
theorem exponent_hasFiniteMulSupport (a : IdeleGroup R K) :
    Function.HasFiniteMulSupport
      fun v : HeightOneSpectrum R =>
        (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ exponent a v :=
  Set.Finite.subset (Filter.eventually_cofinite.mp (exponent_eventually_zero a))
    (fun v hv => by simp only [Function.mem_mulSupport] at hv ⊢; exact fun h => hv (by
      rw [h, zpow_zero]))

/-- The `v`-adic exponent is additive in the idèle: `exponent (a * b) v = exponent a v +
exponent b v`. This reflects the multiplicativity of the valuation `Valued.v` at each place. -/
theorem exponent_mul (a b : IdeleGroup R K) (v : HeightOneSpectrum R) :
    exponent (a * b) v = exponent a v + exponent b v := by
  rw [exponent_eq_log, exponent_eq_log, exponent_eq_log, localComponent_mul, map_mul,
    WithZero.log_mul ((Valued.v.ne_zero_iff).mpr (Units.ne_zero _))
      ((Valued.v.ne_zero_iff).mpr (Units.ne_zero _))]

/-- The finite part of a principal idèle `(x)ᵥ` is the diagonal embedding of `x` into the finite
idèle group, i.e. the image of `x` under `Units.map (algebraMap K (FiniteAdeleRing R K))`. -/
theorem finitePart_diagonalEmbedding (x : Kˣ) :
    finitePart R K (diagonalEmbedding R K x) =
      Units.map (algebraMap K (FiniteAdeleRing R K)).toMonoidHom x := by
  apply Units.ext
  rw [show Units.val (finitePart R K (diagonalEmbedding R K x)) =
      (Units.val (diagonalEmbedding R K x)).2 from rfl,
    coe_diagonalEmbedding_apply, Units.coe_map]
  ext v
  rfl

/-- The local component at `v` of the finite part of a principal idèle `(x)ᵥ` is the image of
`x` under the canonical map `K → v.adicCompletion K`. -/
theorem valuation_finitePart_diagonalEmbedding (x : Kˣ) (v : HeightOneSpectrum R) :
    localComponent (diagonalEmbedding R K x) v = ((x : K) : v.adicCompletion K) := by
  show (RestrictedProduct.unitsEquiv _ (finitePart R K (diagonalEmbedding R K x)) v :
      v.adicCompletion K) = _
  rw [RestrictedProduct.unitsEquiv_apply, finitePart_diagonalEmbedding, Units.coe_map]
  exact FiniteAdeleRing.algebraMap_apply R K (x : K) v

theorem exponent_diagonalEmbedding_eq_log (x : Kˣ) (v : HeightOneSpectrum R) :
    exponent (diagonalEmbedding R K x) v = WithZero.log (v.valuation K (x : K)) := by
  rw [exponent_eq_log, valuation_finitePart_diagonalEmbedding,
    valuedAdicCompletion_eq_valuation']

theorem exponent_diagonalEmbedding (x : Kˣ) {n : R} (hn : n ≠ 0) (d : nonZeroDivisors R)
    (hnd : IsLocalization.mk' K n d = (x : K)) (v : HeightOneSpectrum R) :
    exponent (diagonalEmbedding R K x) v =
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(d : R)} : Ideal R)).factors -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n} : Ideal R)).factors := by
  rw [exponent_diagonalEmbedding_eq_log, ← hnd, v.valuation_of_mk',
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero' d),
    v.intValuation_if_neg hn, v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero d),
    WithZero.log_exp, WithZero.log_exp]
  ring

theorem toFractionalIdeal_mul (a b : IdeleGroup R K) :
    toFractionalIdeal (a * b) = toFractionalIdeal a * toFractionalIdeal b := by
  unfold toFractionalIdeal
  rw [← finprod_mul_distrib (exponent_hasFiniteMulSupport a) (exponent_hasFiniteMulSupport b)]
  refine finprod_congr fun v => ?_
  rw [exponent_mul, zpow_add₀ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)]

/-- The fractional ideal determined by a principal idèle `(x)ᵥ` is the (principal) fractional
ideal `(x⁻¹)`. This is the Lean 3 `map_to_fractional_ideals.map_units_K`-type fact underlying
the triviality of `toClassGroup` on principal idèles. -/
theorem toFractionalIdeal_diagonalEmbedding (x : Kˣ) :
    toFractionalIdeal (diagonalEmbedding R K x) =
      FractionalIdeal.spanSingleton (nonZeroDivisors R) ((x : K)⁻¹) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (M := nonZeroDivisors R) (x : K)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact Units.ne_zero x (by rw [← hnd, IsLocalization.mk'_zero])
  have hd0 : (d : R) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  set n' : nonZeroDivisors R := ⟨n, mem_nonZeroDivisors_iff_ne_zero.mpr hn0⟩ with hn'
  have hnd' : IsLocalization.mk' K (d : R) n' = (x : K)⁻¹ := by
    rw [IsFractionRing.mk'_eq_div, ← hnd, IsFractionRing.mk'_eq_div, inv_div]
  unfold toFractionalIdeal
  rw [← hnd', ← FractionalIdeal.finprod_heightOneSpectrum_factorization_principal_fraction hd0 n']
  exact finprod_congr fun v => by rw [exponent_diagonalEmbedding x hn0 d hnd]

/-- Every nonzero fractional ideal `I` is `toFractionalIdeal a` for some idèle `a`: build `a` with
local finite components a uniformizer-like element of valuation `exp (count K v I)` at each place
(using surjectivity of the local valuation `v.valuation_surjective`), which is `1` (a local unit)
at all but finitely many `v` since `count K v I` is eventually `0`
(`FractionalIdeal.finite_factors`). -/
theorem exists_toFractionalIdeal_eq (I : FractionalIdeal (nonZeroDivisors R) K) (hI : I ≠ 0) :
    ∃ a : IdeleGroup R K, toFractionalIdeal a = I := by
  choose k hk using fun v : HeightOneSpectrum R =>
    v.valuation_surjective K (WithZero.exp (FractionalIdeal.count K v I))
  have hk0 : ∀ v, ((k v : K) : v.adicCompletion K) ≠ 0 := fun v => by
    refine (Valued.v.ne_zero_iff).mp ?_
    rw [valuedAdicCompletion_eq_valuation', hk v]
    exact WithZero.exp_ne_zero
  set x : (v : HeightOneSpectrum R) → (v.adicCompletion K)ˣ :=
    fun v => Units.mk0 ((k v : K) : v.adicCompletion K) (hk0 v) with hx
  have hev : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      x v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
    filter_upwards [FractionalIdeal.finite_factors I] with v hv
    have : x v ∈ (v.adicCompletionIntegers K).units := by
      rw [adicCompletionIntegers.mem_units_iff_valued_eq_one]
      show Valued.v ((k v : K) : v.adicCompletion K) = 1
      rw [valuedAdicCompletion_eq_valuation', hk v, hv, WithZero.exp_zero]
    exact this
  set a0 : FiniteIdeleGroup R K := RestrictedProduct.mkUnit x hev with ha0
  set idele : IdeleGroup R K := (equivProd R K).symm (1, a0) with hidele
  have hfinite : finitePart R K idele = a0 := by
    show (equivProd R K idele).2 = a0
    rw [hidele, (equivProd R K).apply_symm_apply]
  refine ⟨idele, ?_⟩
  have hexp : ∀ v, exponent idele v = FractionalIdeal.count K v I := by
    intro v
    rw [exponent_eq_log]
    unfold localComponent
    rw [hfinite]
    show WithZero.log (Valued.v (a0.1 v : v.adicCompletion K)) = _
    have : (a0.1 v : v.adicCompletion K) = (k v : K) := rfl
    rw [this, valuedAdicCompletion_eq_valuation', hk v, WithZero.log_exp]
  rw [show toFractionalIdeal idele = ∏ᶠ v : HeightOneSpectrum R,
      (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ FractionalIdeal.count K v I from
    finprod_congr fun v => by rw [hexp v]]
  exact FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI

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

/-- Principal idèles map to the trivial class in the ideal class group: the fractional ideal
`toFractionalIdeal (diagonalEmbedding x) = (x⁻¹)` is principal, hence trivial in `ClassGroup R`. -/
theorem toClassGroup_diagonalEmbedding (x : Kˣ) : toClassGroup (diagonalEmbedding R K x) = 1 := by
  show (ClassGroup.mk K) (toFractionalIdealHom (diagonalEmbedding R K x)) = 1
  rw [ClassGroup.mk_eq_one_iff]
  exact FractionalIdeal.isPrincipal_iff _ |>.mpr ⟨(x : K)⁻¹, toFractionalIdeal_diagonalEmbedding x⟩

/-- The principal idèles lie in the kernel of `toClassGroup`. -/
theorem principalSubgroup_le_ker_toClassGroup :
    principalSubgroup R K ≤ (toClassGroup (R := R) (K := K)).ker := by
  rintro _ ⟨x, rfl⟩
  exact toClassGroup_diagonalEmbedding x

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

/-- The map from the idèle group to the ideal class group descends to the idèle class group,
since principal idèles map to the trivial ideal class
(`IdeleGroup.principalSubgroup_le_ker_toClassGroup`). This is the Lean 3
`C_K.map_to_class_group`. -/
noncomputable def toClassGroup : IdeleClassGroup R K →* ClassGroup R :=
  QuotientGroup.lift (IdeleGroup.principalSubgroup R K) IdeleGroup.toClassGroup
    IdeleGroup.principalSubgroup_le_ker_toClassGroup

theorem toClassGroup_mk (a : IdeleGroup R K) : toClassGroup R K (mk R K a) =
    IdeleGroup.toClassGroup a := rfl

/-- The map from the idèle class group to the ideal class group is surjective: every ideal
class is represented by some idèle. Every element of `ClassGroup R` is (via
`ClassGroup.mk0_surjective`) the class of some nonzero integral ideal `J`, and
`IdeleGroup.exists_toFractionalIdeal_eq` produces an idèle `a` with
`toFractionalIdeal a = (J : FractionalIdeal R⁰ K)`, whence `toFractionalIdealHom a` and
`FractionalIdeal.mk0 K J` agree as units and `mk R K a` maps to the class of `J`. -/
theorem toClassGroup_surjective : Function.Surjective (toClassGroup R K) := by
  intro c
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective (R := R) c
  have hJ0 : (J : FractionalIdeal (nonZeroDivisors R) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (nonZeroDivisors.coe_ne_zero J)
  obtain ⟨a, ha⟩ :=
    IdeleGroup.exists_toFractionalIdeal_eq (J : FractionalIdeal (nonZeroDivisors R) K) hJ0
  refine ⟨mk R K a, ?_⟩
  rw [toClassGroup_mk]
  show ClassGroup.mk K (IdeleGroup.toFractionalIdealHom a) = c
  have heq : IdeleGroup.toFractionalIdealHom a = FractionalIdeal.mk0 K J := by
    apply Units.ext
    show IdeleGroup.toFractionalIdeal a = _
    rw [ha, FractionalIdeal.coe_mk0]
  rw [heq, ClassGroup.mk_mk0, hJ]

/-- The kernel of `IdeleClassGroup.toClassGroup` is the image, under the quotient map `mk`, of
the kernel of `IdeleGroup.toClassGroup`. This is the general fact about kernels of a
`QuotientGroup.lift` (`QuotientGroup.ker_lift`), specialized to our situation; combined with
`IdeleGroup.toClassGroup_eq_one_iff`, it identifies the classes of idèles whose determined
fractional ideal is principal as exactly the kernel of the map to the class group. -/
theorem ker_toClassGroup : (toClassGroup R K).ker =
    Subgroup.map (mk R K) (IdeleGroup.toClassGroup (R := R) (K := K)).ker :=
  QuotientGroup.ker_lift _ _ _

end IdeleClassGroup

/-! ### The idèle norm (content map)

Mathlib already provides the archimedean half of this: `NumberField.InfiniteAdeleRing.instNorm`
puts a multiplicative `‖·‖` on the infinite adèle ring, given by the product of the normalized
absolute values across infinite places (`InfiniteAdeleRing.norm_def`), and
`InfiniteAdeleRing.coe_norm_eq_abs_norm` shows this restricts to `|Algebra.norm ℚ x|` on
principal elements -- the archimedean half of the product formula. The finite half is the
absolute norm of a fractional ideal, `FractionalIdeal.absNorm : FractionalIdeal R⁰ K →*₀ ℚ`
(Xavier Roblot, `Mathlib.RingTheory.FractionalIdeal.Norm`), which is already exactly
multiplicative and already satisfies the matching principal-element identity
(`FractionalIdeal.absNorm_span_singleton`). Multiplying the two together gives the idèle norm
`‖·‖_𝔸 : IdeleGroup R K →* ℝ` (well, a `MonoidHom`-shaped function -- see `content_mul`),
and the two known principal-element identities combine (via
`IdeleGroup.toFractionalIdeal_diagonalEmbedding` and `Algebra.norm_inv`) to reprove the full
product formula `‖(x)ᵥ‖_𝔸 = 1` as `content_diagonalEmbedding`. -/

namespace IdeleGroup

variable {R K} [NumberField K] [Module.Free ℤ R] [Module.Finite ℤ R]

omit [NumberField K] [Module.Free ℤ R] [Module.Finite ℤ R] in
/-- The infinite part of a principal idèle `(x)ᵥ` is the diagonal embedding of `x` into the
infinite idèle group. -/
theorem infinitePart_diagonalEmbedding (x : Kˣ) :
    infinitePart R K (diagonalEmbedding R K x) =
      Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom x := by
  apply Units.ext
  rw [show Units.val (infinitePart R K (diagonalEmbedding R K x)) =
      (Units.val (diagonalEmbedding R K x)).1 from rfl,
    coe_diagonalEmbedding_apply, Units.coe_map]
  rfl

/-- The idèle norm, or content: the product of the archimedean norm of the infinite part and
the absolute norm of the fractional ideal determined by the finite part. This is the standard
normalized idèle norm `‖·‖_𝔸`, extended multiplicatively from the local normalized absolute
values `|·|ᵥ` (`content_mul`), and trivial on principal idèles (`content_diagonalEmbedding`) --
the adelic form of the product formula. -/
noncomputable def content (a : IdeleGroup R K) : ℝ :=
  ‖Units.val (α := InfiniteAdeleRing K) (infinitePart R K a)‖ *
    (FractionalIdeal.absNorm (toFractionalIdeal a) : ℝ)

theorem content_mul (a b : IdeleGroup R K) : content (a * b) = content a * content b := by
  have h1 : Units.val (α := InfiniteAdeleRing K) (infinitePart R K (a * b)) =
      Units.val (α := InfiniteAdeleRing K) (infinitePart R K a) *
        Units.val (α := InfiniteAdeleRing K) (infinitePart R K b) :=
    map_mul ((Units.coeHom (InfiniteAdeleRing K)).comp (infinitePart R K)) a b
  have h2 : ‖Units.val (α := InfiniteAdeleRing K) (infinitePart R K a) *
      Units.val (α := InfiniteAdeleRing K) (infinitePart R K b)‖ =
      ‖Units.val (α := InfiniteAdeleRing K) (infinitePart R K a)‖ *
        ‖Units.val (α := InfiniteAdeleRing K) (infinitePart R K b)‖ := by
    simp only [InfiniteAdeleRing.norm_def]
    rw [show ∀ x y : InfiniteAdeleRing K, (x * y) = fun v => x v * y v from fun _ _ => rfl]
    simp only [norm_mul, mul_pow]
    exact Finset.prod_mul_distrib
  unfold content
  rw [h1, h2, toFractionalIdeal_mul, map_mul]
  push_cast
  ring

/-- Principal idèles have content `1`: this is the adelic product formula, reassembled from its
archimedean half (`InfiniteAdeleRing.coe_norm_eq_abs_norm`) and non-archimedean half
(`FractionalIdeal.absNorm_span_singleton` applied to
`IdeleGroup.toFractionalIdeal_diagonalEmbedding`). -/
theorem content_diagonalEmbedding (x : Kˣ) : content (diagonalEmbedding R K x) = 1 := by
  have hx : (Algebra.norm ℚ (x : K)) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr (Units.ne_zero x)
  have hinf : Units.val (α := InfiniteAdeleRing K) (infinitePart R K (diagonalEmbedding R K x)) =
      algebraMap K (InfiniteAdeleRing K) (x : K) := by
    rw [infinitePart_diagonalEmbedding]; rfl
  unfold content
  rw [hinf, InfiniteAdeleRing.coe_norm_eq_abs_norm, toFractionalIdeal_diagonalEmbedding,
    FractionalIdeal.absNorm_span_singleton, Algebra.norm_inv, abs_inv]
  push_cast
  rw [mul_inv_cancel₀]
  exact_mod_cast abs_ne_zero.mpr hx

end IdeleGroup

/-! ### The norm map on idèles for a finite extension

**Survey.** For a finite extension `L / K` of number fields (with rings of integers `S / R`),
the classical idèle norm map `N_{L/K} : IdeleGroup S L →* IdeleGroup R K` sends an idèle `a` to
the idèle whose component at each place `v` of `K` is `∏_{w ∣ v} N_{L_w / K_v}(a_w)`, the product
of local norms over the (finitely many) places `w` of `L` lying above `v`.

As of this writing, Mathlib does not have the pieces this needs:

- No relation "`w` (a `HeightOneSpectrum S`) lies over `v` (a `HeightOneSpectrum R`)" for a finite
  ring extension `S / R` of Dedekind domains, analogous to `Ideal.LiesOver` /
  `IsDedekindDomain.HeightOneSpectrum.comap`-under-an-extension. (There is a `comap` along the
  completion/localization equivalence at a *fixed* place, `AdicValuation.lean` line 662, but
  nothing relating the spectra of `R` and `S`.) The infinite-place analogue is closer to
  existing: `NumberField.InfinitePlace.comap` and `ComplexEmbedding.LiesOver` already give a
  restriction map `InfinitePlace L → InfinitePlace K` and a "lies over" relation on embeddings
  (`Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings`), but this file does not attempt
  to build the finite-adèle analogue from only the archimedean half.
- No local norm map `L_w →+* K_v` (or `N_{L_w/K_v} : L_w → K_v` as a monoid hom on units) between
  completions at places of different fields; `Mathlib.RingTheory.Norm` gives `Algebra.norm K x`
  for a finite extension `L / K` acting on `L` itself, not on completions at extended places.
- No ring hom `AdeleRing S L →+* AdeleRing R K` (or its restriction to finite/infinite parts)
  induced by a finite extension `L / K`, from which `IdeleGroup S L →* IdeleGroup R K` could be
  obtained by restriction to units; nothing under the name `baseChange`/`extensionMap` for
  `FiniteAdeleRing` or `InfiniteAdeleRing` was found by grep.

Building `N_{L/K}` correctly therefore requires first formalizing the place-lying-over relation
and the local norm maps it indexes -- genuinely new infrastructure, not a routine extension of
what is already in the file. The declaration below records the intended type signature (matching
the Lean 3 `ideles_K.lean` `norm_idele.map` up to naming) with a `sorry`, so that later work can
fill in the construction without having to re-derive the statement. -/

section NormMap

variable (S L : Type*) [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L]
  [IsScalarTower R S L] [IsScalarTower R K L] [Module.Finite K L]

/-- The idèle norm map for a finite extension `L / K` (of fraction fields of Dedekind domains
`S / R`), sending an idèle of `L` to its norm idèle of `K`. See the module-level survey above:
this requires local norm maps at each extended place, which Mathlib does not yet provide, hence
the `sorry`. -/
noncomputable def IdeleGroup.normMap : IdeleGroup S L →* IdeleGroup R K := sorry

end NormMap

end NumberField
