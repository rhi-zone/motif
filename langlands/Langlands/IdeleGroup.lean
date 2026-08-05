import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The idèle group and idèle class group

Mathlib contains the adèle ring `NumberField.AdeleRing R K`, split as
`InfiniteAdeleRing K × FiniteAdeleRing R K`, together with its topology, its `K`-algebra
structure, and the subgroup of principal adèles `NumberField.AdeleRing.principalSubgroup`. This
file develops the multiplicative side: the idèle group, the diagonal embedding of `Kˣ`, the idèle
class group, and the maps from these to the ideal class group of `K`.

Throughout, `R` is a Dedekind domain with fraction field `K`. The intended instantiation is
`R = 𝓞 K`, but as with `AdeleRing` the definitions are stated generally, so that e.g. `R = ℤ`,
`K = ℚ` is also allowed.

This is a port of María Inés de Frutos-Fernández's Lean 3 `ideles` project
(`github.com/mariainesdff/ideles`, files `ideles_R.lean` / `ideles_K.lean`); Lean 3 names are
recorded in the docstrings below.

## Main definitions

- `NumberField.IdeleGroup R K` : the idèle group of `K`, the unit group of `AdeleRing R K`.
- `NumberField.IdeleGroup.diagonalEmbedding`, `NumberField.IdeleGroup.principalSubgroup R K` :
  the embedding `x ↦ (x)ᵥ` of `Kˣ` and its image, the subgroup of principal idèles.
- `NumberField.FiniteIdeleGroup R K`, `NumberField.InfiniteIdeleGroup K` : the finite and
  infinite idèle groups, with the topological-group isomorphism
  `NumberField.IdeleGroup.equivProd : IdeleGroup R K ≃ₜ* InfiniteIdeleGroup K × FiniteIdeleGroup R K`
  and the projections `IdeleGroup.infinitePart` / `IdeleGroup.finitePart`.
- `NumberField.IdeleGroup.exponent`, `NumberField.IdeleGroup.toFractionalIdeal` : the `v`-adic
  exponent of an idèle and the fractional ideal `∏_v v ^ exponent a v` it determines;
  `NumberField.IdeleGroup.toFractionalIdealHom` and `NumberField.IdeleGroup.toClassGroup` package
  these as maps to the group of nonzero fractional ideals and to `ClassGroup R`.
- `NumberField.IdeleClassGroup R K` : the idèle class group, the quotient of the idèle group by
  the principal idèles, with quotient map `NumberField.IdeleClassGroup.mk`.
- `NumberField.IdeleClassGroup.toClassGroup` : the descent of `IdeleGroup.toClassGroup` along
  that quotient.
- `NumberField.IdeleGroup.content` : the idèle norm `‖·‖_𝔸 : IdeleGroup R K → ℝ`.
- `NumberField.IdeleGroup.normMap` : the idèle norm map of a finite extension `L / K`, defined in
  `Langlands/NormMap.lean` rather than here to avoid a circular import.

## Main results

- `NumberField.IdeleGroup.diagonalEmbedding_injective` : the diagonal embedding of `Kˣ` is
  injective.
- `NumberField.IdeleGroup.toFractionalIdeal_diagonalEmbedding` : a principal idèle `(x)ᵥ`
  determines the principal fractional ideal `(x⁻¹)`; hence
  `NumberField.IdeleGroup.toClassGroup_diagonalEmbedding` and
  `NumberField.IdeleGroup.principalSubgroup_le_ker_toClassGroup`.
- `NumberField.IdeleGroup.exists_toFractionalIdeal_eq` : every nonzero fractional ideal is
  determined by some idèle; hence `NumberField.IdeleClassGroup.toClassGroup_surjective`.
- `NumberField.IdeleClassGroup.ker_toClassGroup` : the kernel of the map to `ClassGroup R` is the
  image under `mk` of `ker IdeleGroup.toClassGroup`.
- `NumberField.IdeleGroup.content_diagonalEmbedding` : principal idèles have content `1`, the
  adelic form of the product formula.

## Implementation notes

`IdeleGroup R K` and `IdeleClassGroup R K` inherit their topology and topological-group structure
from general Mathlib instances: `Units.instTopologicalSpaceUnits` together with
`IsTopologicalGroup αˣ` for a topological monoid with continuous multiplication, and
`QuotientGroup.instTopologicalSpace` / `QuotientGroup.instIsTopologicalGroup` for the quotient
(every subgroup of the commutative group `IdeleGroup R K` being normal). The corresponding Lean 3
constructions (`finite_idele_group'.topological_space`, `topological_group_quotient`, ...) have no
counterpart here.

Likewise `equivProd` is transported from the definitional splitting of `AdeleRing R K` via
`MulEquiv.prodUnits` / `Homeomorph.prodUnits`, and `diagonalEmbedding_injective` follows from
`NumberField.AdeleRing.algebraMap_injective` via `Units.map_injective`, in place of the Lean 3
argument through nonemptiness of `HeightOneSpectrum R`.

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

/-- The diagonal embedding of `Kˣ` into the idèle group is injective, for `K` a number field.
This is the Lean 3 `inj_units_K.injective`. -/
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
ideal `(x⁻¹)`, whence the triviality of `toClassGroup` on principal idèles.

The computation goes through `exponent_diagonalEmbedding`, which for `x = n/d` with `n : R`,
`d ∈ R⁰` expresses the `v`-adic exponent of `(x)ᵥ` as a difference of `Associates.count`
factorization multiplicities, and
`FractionalIdeal.finprod_heightOneSpectrum_factorization_principal_fraction`. -/
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
the kernel of `IdeleGroup.toClassGroup`: the general description of the kernel of a
`QuotientGroup.lift` (`QuotientGroup.ker_lift`). -/
theorem ker_toClassGroup : (toClassGroup R K).ker =
    Subgroup.map (mk R K) (IdeleGroup.toClassGroup (R := R) (K := K)).ker :=
  QuotientGroup.ker_lift _ _ _

end IdeleClassGroup

/-! ### The idèle norm (content map)

The idèle norm `‖·‖_𝔸` is the product of two halves already available in Mathlib.
The archimedean half is `NumberField.InfiniteAdeleRing.instNorm`, the product of the normalized
absolute values across the infinite places (`InfiniteAdeleRing.norm_def`), which restricts to
`|Algebra.norm ℚ x|` on principal elements (`InfiniteAdeleRing.coe_norm_eq_abs_norm`). The finite
half is the absolute norm of a fractional ideal,
`FractionalIdeal.absNorm : FractionalIdeal R⁰ K →*₀ ℚ`, which is multiplicative and satisfies the
matching identity `FractionalIdeal.absNorm_span_singleton` on principal ideals. Multiplicativity
of the product is `content_mul`, and the two principal-element identities combine to give the
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

For a finite extension `L / K` of fraction fields of Dedekind domains `S / R`, the idèle norm map
`N_{L/K} : IdeleGroup S L →* IdeleGroup R K` sends an idèle `a` to the idèle whose component at a
place `v` of `K` is `∏_{w ∣ v} N_{L_w/K_v}(a_w)`, the product of the local norms over the finitely
many places `w` of `L` above `v`. It is the Lean 3 `ideles_K.lean` `norm_idele.map`.

The construction is `NumberField.IdeleGroup.normMap`, in `Langlands/NormMap.lean`: the local norm
maps at the finite and infinite places are assembled into
`NumberField.FiniteIdeleGroup.normMap` and `NumberField.InfiniteIdeleGroup.normMap`, which are
combined via `IdeleGroup.equivProd`. It is defined there rather than here to avoid a circular
import. -/

end NumberField
