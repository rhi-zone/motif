import Langlands.UnramifiedValuationExtension
import Langlands.NormMap
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# The compatibility square: `localNormMap` reduces mod the maximal ideal to the residue norm

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, let `v` be a
place of `R` and `w` a place of `S` lying over `v`, and write `K₀ := v.adicCompletionIntegers K`,
`L₀ := w.adicCompletionIntegers L`. `Langlands.NormMap` builds the local norm map `localNormMap :
(w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ` as `Units.map (Algebra.norm (v.adicCompletion
K))`. `Langlands.ResidueFieldNorm` builds the abstract residue-field norm `Algebra.norm 𝓀[K] :
𝓀[L] → 𝓀[K]` and proves it surjective. This file closes the gap between them: under `IsUnramified`
(`Langlands.UnramifiedValuationExtension`), `localNormMap` reduces mod the maximal ideal to exactly
that residue-field norm.

## Route

1. `residue_norm_eq_norm_residue` (general, no valuation content): for any `IsLocalRing R` with `S`
   a finite free `R`-algebra, `Algebra.norm` commutes with reduction mod the maximal ideal —
   `residue R (Algebra.norm R x) = Algebra.norm (R ⧸ 𝔪) (mk (Ideal.map (algebraMap R S) 𝔪) x)`.
   Proved via `IsLocalRing.basisQuotient` (the Nakayama-type fact that a basis of a finite free
   module over a local ring reduces to a basis of the quotient) plus `RingHom.map_det`.
2. Specializing (1) to `R := K₀`, `S := L₀` and using `IsUnramified` to identify the quotient
   `L₀ ⧸ 𝔪_K·L₀` with `𝓀[L] = L₀ ⧸ 𝔪_L` gives `residue_norm_eq_norm_residue_of_isUnramified`: the
   *ring*-norm `Algebra.norm K₀ : L₀ → K₀` reduces mod `𝔪_K` to `Algebra.norm 𝓀[K] : 𝓀[L] → 𝓀[K]`.
3. `algebraMap_norm_eq_norm_algebraMap` connects that ring-norm to the *field* norm used inside
   `localNormMap`: `algebraMap K₀ K (Algebra.norm K₀ x) = Algebra.norm K (algebraMap L₀ L x)`, via
   `Algebra.algebraMap_intNorm` (general norm/fraction-field compatibility) together with
   `Algebra.intNorm_eq_norm` (`intNorm` agrees with `Algebra.norm` for finite free extensions).
4. `localNormMap_reduce` combines (2) and (3): for `a : (w.adicCompletion L)ˣ` with
   `(a : w.adicCompletion L) ∈ w.adicCompletionIntegers L`, the residue of `localNormMap K L v w a`
   (valued in `K₀`, via `localNormMap_mem_units`) is `Algebra.norm 𝓀[K]` of the residue of `a`.

## Main results

* `IsLocalRing.residue_norm_eq_norm_residue`
* `IsDedekindDomain.HeightOneSpectrum.residue_norm_eq_norm_residue_of_isUnramified`
* `IsDedekindDomain.HeightOneSpectrum.algebraMap_norm_eq_norm_algebraMap`
* `IsDedekindDomain.HeightOneSpectrum.localNormMap_reduce`
-/

noncomputable section

open IsDedekindDomain IsLocalRing

open scoped WithZero

/-! ### General fact: `Algebra.norm` commutes with reduction mod the maximal ideal -/

namespace IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
  [Module.Finite R S] [Module.Free R S]

/-- For `S` a finite free algebra over a local ring `R`, the norm `Algebra.norm R : S → R`
commutes with reduction mod the maximal ideal: reducing the norm mod `𝔪_R` agrees with taking the
norm, over the residue field `R ⧸ 𝔪_R`, of the reduction of the element mod `𝔪_R · S`.

Proved via `IsLocalRing.basisQuotient` (a basis of `S` reduces to a basis of `S ⧸ 𝔪_R·S`) and
`RingHom.map_det` (determinants commute with ring homomorphisms applied entrywise). -/
theorem residue_norm_eq_norm_residue (x : S) :
    Ideal.Quotient.mk (maximalIdeal R) (Algebra.norm R x) =
      Algebra.norm (R ⧸ maximalIdeal R)
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)) x) := by
  classical
  let b := Module.Free.chooseBasis R S
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det (basisQuotient b),
    RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [basisQuotient_apply, ← map_mul, basisQuotient_repr]

/-- A version of `residue_norm_eq_norm_residue` for an arbitrary ideal `I` of `S` known equal to
`Ideal.map (algebraMap R S) (maximalIdeal R)`, and an arbitrary `Algebra (R ⧸ maximalIdeal R)
(S ⧸ I)` instance, as long as that instance's `algebraMap` agrees with the natural one
(`hcompat`). This lets the statement target a *pre-existing* algebra structure on `S ⧸ I` (e.g.
one built from `Valuation.HasExtension`, as in `Langlands.ResidueFieldNorm`) rather than the
`Ideal.Quotient.algebraQuotientMapQuotient` instance baked into `basisQuotient`, sidestepping the
need to transport `Algebra.norm` along a type-level rewrite of the ideal (which does not
type-check via plain `rw`, the algebra instance argument depending on the exact syntactic form of
the ideal). -/
theorem residue_norm_eq_norm_residue_of_eq_map {I : Ideal S}
    (hI : I = Ideal.map (algebraMap R S) (maximalIdeal R))
    [inst : Algebra (R ⧸ maximalIdeal R) (S ⧸ I)]
    (hcompat : ∀ r : R, algebraMap (R ⧸ maximalIdeal R) (S ⧸ I) (Ideal.Quotient.mk _ r) =
        Ideal.Quotient.mk I (algebraMap R S r))
    (x : S) :
    Ideal.Quotient.mk (maximalIdeal R) (Algebra.norm R x) =
      Algebra.norm (R ⧸ maximalIdeal R) (Ideal.Quotient.mk I x) := by
  subst hI
  have hinst : inst = Ideal.Quotient.algebraQuotientMapQuotient := by
    refine Algebra.algebra_ext _ _ fun r => ?_
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [hcompat, Ideal.Quotient.algebraMap_quotient_map_quotient]
  rw [hinst]
  exact residue_norm_eq_norm_residue x

end IsLocalRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

/-! ### The residue-field level compatibility, under `IsUnramified` -/

variable [Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]

omit [Algebra.IsIntegral R S] in
/-- Under `IsUnramified`, the ring-norm `Algebra.norm K₀ : L₀ → K₀` reduces mod `𝔪_K` to the
abstract residue-field norm `Algebra.norm 𝓀[K] : 𝓀[L] → 𝓀[K]` of `Langlands.ResidueFieldNorm`.

This is `IsLocalRing.residue_norm_eq_norm_residue` specialized to `R := K₀`, `S := L₀`, with the
quotient `L₀ ⧸ Ideal.map (algebraMap K₀ L₀) 𝔪_K` identified with `𝓀[L] = L₀ ⧸ 𝔪_L` via the
`IsUnramified` hypothesis `𝔪_K·L₀ = 𝔪_L`. -/
theorem residue_norm_eq_norm_residue_of_isUnramified
    (hU : IsUnramified K L v w) (x : w.adicCompletionIntegers L) :
    residue (v.adicCompletionIntegers K) (Algebra.norm (v.adicCompletionIntegers K) x) =
      Algebra.norm (ResidueField (v.adicCompletionIntegers K))
        (residue (w.adicCompletionIntegers L) x) :=
  IsLocalRing.residue_norm_eq_norm_residue_of_eq_map (R := v.adicCompletionIntegers K)
    (S := w.adicCompletionIntegers L) hU.symm
    (fun r => algebraMap_residueField_residue K L v w r) x

/-! ### The field-level compatibility, connecting `Algebra.norm K₀` to `localNormMap` -/

omit [Algebra.IsIntegral R S] in
/-- `w.adicCompletionIntegers L` is a domain: `ValuationSubring.instIsDomainSubtypeMem`, restated
through the unfolding `adicCompletionIntegers = Valued.v.valuationSubring`. -/
instance : IsDomain (w.adicCompletionIntegers L) :=
  inferInstanceAs (IsDomain (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰).valuationSubring)

omit [Algebra.IsIntegral R S] in
instance : IsDomain (v.adicCompletionIntegers K) :=
  inferInstanceAs (IsDomain (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring)

omit [Algebra.IsIntegral R S] in
instance : IsIntegrallyClosed (w.adicCompletionIntegers L) :=
  inferInstanceAs (IsIntegrallyClosed
    (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰).valuationSubring)

omit [Algebra.IsIntegral R S] in
instance : IsIntegrallyClosed (v.adicCompletionIntegers K) :=
  inferInstanceAs (IsIntegrallyClosed
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring)

omit [Algebra.IsIntegral R S] in
instance : IsFractionRing (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  inferInstanceAs (IsFractionRing
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).valuationSubring (v.adicCompletion K))

instance : Algebra.IsIntegral (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  Algebra.IsIntegral.of_finite _ _

omit [Algebra.IsIntegral R S] in
/-- `w.adicCompletionIntegers L` is a torsion-free `v.adicCompletionIntegers K`-module: the
algebra map `K₀ → L₀` is injective, since its composite with the injective inclusion `L₀ ↪
w.adicCompletion L` is the algebra map `K₀ → w.adicCompletion L`, already known injective
(`Langlands.AdicCompletionIntegralClosure`'s torsion-freeness of `K₀` over the ambient field). -/
instance : Module.IsTorsionFree (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  have hinj : Function.Injective
      (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) := by
    intro x y hxy
    have h : (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) x :
          w.adicCompletion L) =
        (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) y :
          w.adicCompletion L) := congrArg _ hxy
    rw [coe_algebraMap_adicCompletionIntegers, coe_algebraMap_adicCompletionIntegers] at h
    exact Subtype.ext ((adicCompletionComap K L v w).injective h)
  exact .of_smul_eq_zero fun r x hrx => by
    rw [Algebra.smul_def] at hrx
    rcases mul_eq_zero.mp hrx with h | h
    · exact Or.inl (hinj (by rwa [map_zero]))
    · exact Or.inr h

omit [Algebra.IsIntegral R S] in
/-- The ring-norm `Algebra.norm K₀ : L₀ → K₀` and the field-norm `Algebra.norm K : L → K` (the
one underlying `localNormMap`) agree, in the sense that the former maps to the latter under the
respective inclusions into the fields. This is `Algebra.algebraMap_intNorm` (norm/fraction-field
compatibility, general) together with `Algebra.intNorm_eq_norm` (`intNorm` agrees with the ring
norm `Algebra.norm` once the extension is finite free, which `L₀ / K₀` is). -/
theorem algebraMap_norm_eq_norm_algebraMap (x : w.adicCompletionIntegers L) :
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        (Algebra.norm (v.adicCompletionIntegers K) x) =
      Algebra.norm (v.adicCompletion K)
        (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) x) := by
  have h := Algebra.algebraMap_intNorm (A := v.adicCompletionIntegers K) (K := v.adicCompletion K)
    (L := w.adicCompletion L) (B := w.adicCompletionIntegers L) x
  rwa [Algebra.intNorm_eq_norm] at h

/-! ### The compatibility square -/

omit [Algebra.IsIntegral R S] in
/-- **The compatibility square.** Under `IsUnramified`, `localNormMap` reduces mod the maximal
ideal to the abstract residue-field norm of `Langlands.ResidueFieldNorm`: for a unit `a` of
`w.adicCompletion L` landing in `w.adicCompletionIntegers L`, the residue (in `𝓀[K]`) of
`localNormMap K L v w a` (which lands in `v.adicCompletionIntegers K`, by
`localNormMap_mem_units`) equals `Algebra.norm 𝓀[K]` of the residue of `a`. -/
theorem localNormMap_reduce (hU : IsUnramified K L v w) {a : (w.adicCompletion L)ˣ}
    (ha : a ∈ (w.adicCompletionIntegers L).units) :
    residue (v.adicCompletionIntegers K)
        ⟨(localNormMap K L v w a : v.adicCompletion K),
          Submonoid.val_mem_of_mem_units _ (localNormMap_mem_units K L v w ha)⟩ =
      Algebra.norm (ResidueField (v.adicCompletionIntegers K))
        (residue (w.adicCompletionIntegers L)
          ⟨(a : w.adicCompletion L), Submonoid.val_mem_of_mem_units _ ha⟩) := by
  set x : w.adicCompletionIntegers L :=
    ⟨(a : w.adicCompletion L), Submonoid.val_mem_of_mem_units _ ha⟩ with hx
  have hval : (localNormMap K L v w a : v.adicCompletion K) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        (Algebra.norm (v.adicCompletionIntegers K) x) := by
    rw [algebraMap_norm_eq_norm_algebraMap K L v w x]
    rfl
  have heq : (⟨(localNormMap K L v w a : v.adicCompletion K),
        Submonoid.val_mem_of_mem_units _ (localNormMap_mem_units K L v w ha)⟩ :
      v.adicCompletionIntegers K) = Algebra.norm (v.adicCompletionIntegers K) x :=
    Subtype.ext hval
  rw [heq]
  exact residue_norm_eq_norm_residue_of_isUnramified K L v w hU x

end IsDedekindDomain.HeightOneSpectrum

end
