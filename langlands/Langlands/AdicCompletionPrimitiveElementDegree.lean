import Langlands.AdicCompletionIntegralClosure

/-!
# Separability and full degree at a completion, from a primitive element

Let `L / K` be a finite extension of fraction fields of Dedekind domains `S / R`, `v` a place of
`R`, `w` a place of `S` lying over `v`. This file isolates the *generic* structure underlying
`Langlands.TotallyRamifiedArtinSchreierConcreteExample`'s completed-level `Algebra.IsSeparable
(v.adicCompletion K) (w.adicCompletion L)` / `finrank` argument: given a primitive element `theta :
L` (`IntermediateField.adjoin K {theta} = ⊤`) whose minimal polynomial *stays irreducible* after
base-changing along `algebraMap K (v.adicCompletion K)`, the completions satisfy
`Module.finrank (v.adicCompletion K) (w.adicCompletion L) = Module.finrank K L` and
`Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)` — with no reference to what
`theta`'s minimal polynomial actually *is*.

This was extracted from the Artin–Schreier file's from-scratch construction (which built this
argument by hand for its specific Artin–Schreier generator, `theta` a root of `X ^ p - X - a`)
after confirming its proof only used this "primitive element with irreducible base change" shape,
never anything about the Artin–Schreier polynomial itself: the density argument
(`Kv⟮thetaw⟯` closed and dense, hence `= ⊤`) only needs `thetaw` integral over `Kv` and
`Module.finrank Kv Kv⟮thetaw⟯ = Module.finrank K L`, and the latter, together with separability of
`thetaw` over `Kv`, follows from `Irreducible (gPoly)` for `gPoly := (minpoly K theta).map
(algebraMap K (v.adicCompletion K))` alone.

## Main result

* `IsDedekindDomain.HeightOneSpectrum.finrank_and_isSeparable_of_primitiveElement` : given a
  primitive element `theta : L` and irreducibility of its minimal polynomial's base change to
  `v.adicCompletion K`, conclude the exact `finrank` and separability of the completions.
-/

noncomputable section

open Polynomial

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S K L : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] [Algebra R S] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite K L] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S]

variable (K L) (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

omit [Module.Finite K L] [Algebra.IsIntegral R S] in
/-- **The main result.** A primitive element `theta` of `L / K` (`htop`) whose minimal polynomial's
base change to `Kv := v.adicCompletion K` remains irreducible (`hirr`) forces `Lw :=
w.adicCompletion L` to equal `Kv⟮thetaw⟯` (`thetaw` the image of `theta` in `Lw`), giving both the
exact `finrank` and separability of the completions.

Proof shape (identical to `Langlands.TotallyRamifiedArtinSchreierConcreteExample`'s from-scratch
argument, generalized): `gPoly := (minpoly K theta).map (algebraMap K Kv)` is monic with `thetaw` as
a root, so `hirr` identifies it with `minpoly Kv thetaw` exactly, pinning
`finrank Kv Kv⟮thetaw⟯ = natDegree gPoly = natDegree (minpoly K theta) = finrank K L` (the last step
using that `theta` is primitive). Separability transports the same way (`Algebra.IsSeparable K L`
makes `minpoly K theta` separable, hence so is its base change `gPoly`). Finally,
`Kv⟮thetaw⟯` is finite-dimensional (hence closed) over `Kv` and contains the dense image of `L`
(`w.denseRange_algebraMap L`), so `Kv⟮thetaw⟯ = ⊤`, giving `finrank Kv Lw = finrank K L` and
`Algebra.IsSeparable Kv Lw` by transport along `IntermediateField.topEquiv`. -/
theorem finrank_and_isSeparable_of_primitiveElement [Algebra.IsSeparable K L] {theta : L}
    (hInt : IsIntegral K theta) (htop : IntermediateField.adjoin K ({theta} : Set L) = ⊤)
    (hirr : Irreducible ((minpoly K theta).map (algebraMap K (v.adicCompletion K)))) :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) = Module.finrank K L ∧
      Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L) := by
  set Kv := v.adicCompletion K
  set Lw := w.adicCompletion L
  set gPoly : Polynomial Kv := (minpoly K theta).map (algebraMap K Kv) with hgPolyDef
  set thetaw : Lw := algebraMap L Lw theta with hthetawDef
  have gPoly_monic : gPoly.Monic := (minpoly.monic hInt).map _
  have aeval_thetaw_gPoly : Polynomial.aeval thetaw gPoly = 0 := by
    rw [hgPolyDef, Polynomial.aeval_map_algebraMap Kv thetaw (minpoly K theta), hthetawDef,
      Polynomial.aeval_algebraMap_apply Lw theta (minpoly K theta), minpoly.aeval, map_zero]
  have isIntegral_thetaw : IsIntegral Kv thetaw := ⟨gPoly, gPoly_monic, aeval_thetaw_gPoly⟩
  -- `minpoly Kv thetaw = gPoly` exactly, via irreducibility.
  have hminpoly := minpoly.eq_of_irreducible hirr aeval_thetaw_gPoly
  have hminpolyeq : minpoly Kv thetaw = gPoly := by
    rw [← hminpoly, gPoly_monic.leadingCoeff, inv_one, map_one, mul_one]
  have hnatDegree : (minpoly Kv thetaw).natDegree = Module.finrank K L := by
    rw [hminpolyeq, hgPolyDef, Polynomial.natDegree_map_eq_of_injective
      (algebraMap K Kv).injective, ← IntermediateField.adjoin.finrank hInt, htop]
    exact LinearEquiv.finrank_eq (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv
  have hfinrank_adjoin : Module.finrank Kv
      (IntermediateField.adjoin Kv ({thetaw} : Set Lw)) = Module.finrank K L := by
    rw [IntermediateField.adjoin.finrank isIntegral_thetaw, hnatDegree]
  -- The density argument: `Kv⟮thetaw⟯` is finite-dimensional (hence closed) and contains the
  -- dense image of `L`, so it is all of `Lw`.
  have htopalg : Algebra.adjoin K ({theta} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hInt.isAlgebraic,
      htop, IntermediateField.top_toSubalgebra]
  have htopK : IntermediateField.adjoin Kv ({thetaw} : Set Lw) = ⊤ := by
    haveI : FiniteDimensional Kv (IntermediateField.adjoin Kv ({thetaw} : Set Lw)) :=
      IntermediateField.adjoin.finiteDimensional isIntegral_thetaw
    have hMclosed : IsClosed
        ((IntermediateField.adjoin Kv ({thetaw} : Set Lw)).toSubalgebra.toSubmodule : Set Lw) :=
      Submodule.closed_of_finiteDimensional _
    have hsub : Set.range (algebraMap L Lw) ⊆
        ((IntermediateField.adjoin Kv ({thetaw} : Set Lw)) : Set Lw) := by
      rintro _ ⟨l, rfl⟩
      have hl : l ∈ Algebra.adjoin K ({theta} : Set L) := htopalg ▸ Algebra.mem_top
      induction hl using Algebra.adjoin_induction with
      | mem x hx =>
        rw [Set.mem_singleton_iff.mp hx]
        exact IntermediateField.subset_adjoin _ _ (Set.mem_singleton thetaw)
      | algebraMap r =>
        have heq : algebraMap L Lw (algebraMap K L r) = algebraMap Kv Lw (algebraMap K Kv r) :=
          (IsDedekindDomain.HeightOneSpectrum.adicCompletionComap_algebraMap K L v w r).symm
        rw [heq]
        exact IntermediateField.algebraMap_mem _ _
      | add x y' hx hy' ihx ihy' =>
        rw [map_add]
        exact (IntermediateField.adjoin Kv ({thetaw} : Set Lw)).add_mem ihx ihy'
      | mul x y' hx hy' ihx ihy' =>
        rw [map_mul]
        exact (IntermediateField.adjoin Kv ({thetaw} : Set Lw)).mul_mem ihx ihy'
    have hdense : Dense (Set.range (algebraMap L Lw)) := w.denseRange_algebraMap L
    have htopset : (Set.univ : Set Lw) ⊆ ((IntermediateField.adjoin Kv ({thetaw} : Set Lw)) : Set Lw) := by
      rw [← hdense.closure_eq]
      exact closure_minimal hsub hMclosed
    rw [eq_top_iff]
    intro z _
    exact htopset (Set.mem_univ z)
  have hfinrankeq : Module.finrank Kv Lw = Module.finrank K L := by
    rw [← LinearEquiv.finrank_eq (IntermediateField.topEquiv (F := Kv) (E := Lw)).toLinearEquiv,
      ← htopK]
    exact hfinrank_adjoin
  refine ⟨hfinrankeq, ?_⟩
  have hisSepThetaw : IsSeparable Kv thetaw := by
    rw [IsSeparable, hminpolyeq, hgPolyDef]
    have hsepK : (minpoly K theta).Separable := Algebra.IsSeparable.isSeparable K theta
    exact hsepK.map
  haveI htopSep : Algebra.IsSeparable Kv ↥(⊤ : IntermediateField Kv Lw) :=
    htopK ▸ (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable Kv Lw).mpr hisSepThetaw
  exact AlgEquiv.Algebra.isSeparable (IntermediateField.topEquiv (F := Kv) (E := Lw))

end IsDedekindDomain.HeightOneSpectrum

end
