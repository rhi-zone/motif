import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.FieldTheory.Galois.Basic
import Langlands.LubinTateSplittingFieldTorsion

/-!
# `[K_1 : K] = q - 1` — the degree of the Lubin-Tate splitting field

This file closes the headline degree computation of the Lubin-Tate arc:

**`Module.finrank K (K_1 P) = residueCard O - 1`**, for `K_1 P := (P.divX.map (algebraMap O
K)).SplittingField` (`Langlands.LubinTateSplittingField`), `P` the Weierstrass distinguished factor
of a Lubin-Tate series `f` (`f = P * u`, `P.natDegree = residueCard O`).

Writing `q := residueCard O` and `Q := P.divX`, the statement is the classical `[K(F_π[π]) : K] =
q - 1`: adjoining the `π`-torsion of the Lubin-Tate formal group to the base field gives a totally
ramified extension of degree `q - 1`, the degree of the Eisenstein polynomial `Q`.

## The route

1. **A nonzero root.** `Q`'s image splits in `K_1` by construction (`splits_divX_map_K_1`), so it has
   a root `α` there (`Polynomial.Splits.exists_eval_eq_zero`); `α ≠ 0` because `Q.coeff 0` is an
   associate of `π ≠ 0` (`ne_zero_of_aeval_divX_map_eq_zero`).
2. **`K⟮α⟯` has degree `q - 1`.** `Qk := Q.map (algebraMap O K)` is monic and irreducible over `K`
   (Gauss's lemma for the weakly-Eisenstein `Q`, `Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated`
   — this is the one place the standing `[IsFractionRing O K]` on the **base** field is used), hence
   `Qk = minpoly K α` and `IntermediateField.adjoin.finrank` gives
   `Module.finrank K K⟮α⟯ = Qk.natDegree = q - 1`.
3. **`K⟮α⟯ = ⊤`.** `K_1 P` is a splitting field of `Qk` (`K_1.instIsSplittingField`), so it is
   generated over `K` by `Qk.rootSet (K_1 P)` (`Polynomial.IsSplittingField.adjoin_rootSet`). Every
   root of `Qk` in `K_1` is a nonzero `π`-torsion point (`mem_piTorsion_one_of_root_divX_map`), and
   the `(ResidueField O)ˣ`-action on the nonzero `π`-torsion is transitive
   (`orbit_image_eq_piTorsion_sdiff_zero_K_1`), so every such root is `[u]_F(α) =
   eval (phiU hπ hf u) α` for some `u : Oˣ`. Step 4 puts that back inside `K⟮α⟯`.
4. **`eval (phiU hπ hf u) α ∈ K⟮α⟯`** (`eval_phiU_mem_adjoin`) — the only genuinely analytic step.
   `eval` is a `tsum`, not a polynomial expression, so membership is *not* a finite algebraic
   computation: each summand `algebraMap O (K_1 P) (coeff n g) * α ^ n` lies in `K⟮α⟯` (the `O`-image
   factors through `K` by the scalar tower), and `K⟮α⟯` is a finite-dimensional `K`-subspace of
   `K_1 P`, hence **closed** (`Submodule.closed_of_finiteDimensional`, available because
   `K_1.instNormedSpace` supplies `ContinuousSMul K (K_1 P)`), so the limit of the partial sums stays
   in it. The general form of that last move is `Submodule.mem_of_hasSum_of_finiteDimensional` below.

## The general lemma

`Submodule.mem_of_hasSum` / `Submodule.mem_of_hasSum_of_finiteDimensional`: a `HasSum` all of whose
terms lie in a closed (resp. finite-dimensional) submodule has its sum there too. Stated for an
arbitrary index type and with no reference to this file's setting — `HasSum` is by definition a
limit of finite partial sums, each of which is in the submodule, so the closed set contains the
limit.

## Scope

Only `n = 1` is treated: this is `[K_1 : K]`, not the full tower `[K_n : K] = q^(n-1)(q - 1)`. The
higher levels need the `π^n`-torsion analogue of the root count and of transitivity, neither of
which exists in this repo yet.
-/

@[expose] public section

noncomputable section

open scoped Polynomial IntermediateField

/-! ## A `HasSum` inside a closed submodule -/

section HasSumSubmodule

variable {ι R M : Type*} [Semiring R] [AddCommMonoid M] [TopologicalSpace M] [Module R M]

/-- **A `HasSum` whose terms all lie in a closed submodule has its sum there too.** `HasSum g a`
*is* the statement that the net of finite partial sums `∑ i ∈ s, g i` converges to `a`; each such
partial sum lies in `S` (`Submodule.sum_mem`), so a closed `S` contains the limit
(`IsClosed.mem_of_tendsto`). No summability, completeness, or topological-module hypothesis is
needed beyond `S` being closed. -/
theorem Submodule.mem_of_hasSum {S : Submodule R M} (hS : IsClosed (S : Set M)) {g : ι → M} {a : M}
    (hg : HasSum g a) (hmem : ∀ i, g i ∈ S) : a ∈ S :=
  hS.mem_of_tendsto hg (Filter.Eventually.of_forall fun _ ↦ S.sum_mem fun i _ ↦ hmem i)

end HasSumSubmodule

section HasSumFiniteDimensional

variable {ι 𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [AddCommGroup E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [Module 𝕜 E] [ContinuousSMul 𝕜 E] [T2Space E]

/-- **A `HasSum` whose terms all lie in a finite-dimensional subspace has its sum there too.**
`Submodule.mem_of_hasSum` fed `Submodule.closed_of_finiteDimensional`: over a complete nontrivially
normed field, a finite-dimensional subspace of a topological vector space is automatically closed, so
no closedness hypothesis has to be supplied by hand. -/
theorem Submodule.mem_of_hasSum_of_finiteDimensional (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S]
    {g : ι → E} {a : E} (hg : HasSum g a) (hmem : ∀ i, g i ∈ S) : a ∈ S :=
  Submodule.mem_of_hasSum S.closed_of_finiteDimensional hg hmem

end HasSumFiniteDimensional

namespace LubinTate

open NonarchimedeanPowerSeriesEval PowerSeries IsLocalRing Polynomial MulAction

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsFractionRing O K]
variable {π : O} {f : O⟦X⟧}

/-! ## Roots of `Q`'s image in `K_1` are nonzero -/

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Every root of `Q := P.divX`'s image is nonzero.** `Q.coeff 0` is an associate of the
uniformizer `π ≠ 0` (`divX_isWeaklyEisensteinAt_and_associated`), and `algebraMap O (K_1 P)` is
injective (`K_1.instFaithfulSMul`), so `Q`'s image has nonzero constant term — and `0` is a root of a
polynomial exactly when its constant term vanishes. -/
theorem ne_zero_of_aeval_divX_map_eq_zero {π : O} (hπ : Irreducible π) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O) {α : K_1 (K := K) P}
    (hα : Polynomial.aeval α (P.divX.map (algebraMap O K)) = 0) : α ≠ 0 := by
  obtain ⟨-, -, -, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf.1 hf.2.1 hPdist
      (hPdeg ▸ two_le_residueCard)
  rintro rfl
  rw [aeval_K_divX_eq_eval_K_1, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_map] at hα
  have hQ0 : P.divX.coeff 0 = 0 :=
    FaithfulSMul.algebraMap_injective O (K_1 (K := K) P) (by rw [hα, map_zero])
  exact hπ.ne_zero ((associated_zero_iff_eq_zero π).mp (hQ0 ▸ hQ0assoc).symm)

/-! ## The analytic step: `[u]_F(α)` stays inside `K⟮α⟯` -/

omit [IsFractionRing O K] in
/-- **`eval (phiU hπ hf w) α ∈ K⟮α⟯`.** The Lubin-Tate `Oˣ`-action `[w]_F` is given by an honest
power series, so `[w]_F(α)` is a convergent infinite sum, not a polynomial in `α` — membership in
`K⟮α⟯` is therefore a limit statement, not an algebraic identity. Each summand `algebraMap O (K_1 P)
(coeff n (phiU hπ hf w)) * α ^ n` lies in `K⟮α⟯` (the coefficient's image factors as `algebraMap K
(K_1 P) ∘ algebraMap O K` through the scalar tower, so it lies in `K`'s image, and `α ∈ K⟮α⟯`), and
`K⟮α⟯` is finite-dimensional over `K` inside the finite extension `K_1 P`, hence closed
(`Submodule.mem_of_hasSum_of_finiteDimensional`). `hasSum_eval` supplies the `HasSum`, using
`K_1.hOK_transport` for the coefficient bound and `‖α‖ < 1` for convergence. -/
theorem eval_phiU_mem_adjoin (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (P : O[X]) (w : Oˣ) {α : K_1 (K := K) P}
    (hα : ‖α‖ < 1) : eval (phiU hπ hf w) α ∈ K⟮α⟯ := by
  have hbd : ∀ n, ‖algebraMap O (K_1 (K := K) P) (PowerSeries.coeff n (phiU hπ hf w))‖ ≤ 1 :=
    fun n ↦ K_1.hOK_transport P hOK _
  have hmem : ∀ n : ℕ, evalSummand (phiU hπ hf w) α n ∈
      Subalgebra.toSubmodule (K⟮α⟯ : IntermediateField K (K_1 (K := K) P)).toSubalgebra := by
    intro n
    rw [Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra]
    refine mul_mem ?_ (pow_mem (IntermediateField.mem_adjoin_simple_self K α) n)
    rw [show algebraMap O (K_1 (K := K) P) (PowerSeries.coeff n (phiU hπ hf w)) =
        algebraMap K (K_1 (K := K) P) (algebraMap O K (PowerSeries.coeff n (phiU hπ hf w))) from
      congrFun (K_1.algebraMap_O_eq (K := K) P) _]
    exact IntermediateField.algebraMap_mem _ _
  have hsum := Submodule.mem_of_hasSum_of_finiteDimensional
    (Subalgebra.toSubmodule (K⟮α⟯ : IntermediateField K (K_1 (K := K) P)).toSubalgebra)
    (hasSum_eval hbd hα) hmem
  rwa [Subalgebra.mem_toSubmodule, IntermediateField.mem_toSubalgebra] at hsum

/-! ## The generator -/

/-- **`K_1 P` is generated over `K` by a single nonzero `π`-torsion point.** There is an `α : K_1 P`
which is (i) a root of `Qk := P.divX.map (algebraMap O K)`, (ii) a `π`-torsion point of the
Lubin-Tate formal group, (iii) nonzero, and (iv) a primitive element: `K⟮α⟯ = ⊤`.

This is steps 1, 3 and 4 of `finrank_K_1_eq_residueCard_sub_one`'s route (see this file's module
docstring), factored out because everything downstream that needs to *name* the generator — in
particular the `Gal(K_1/K) ≃* (ResidueField O)ˣ` construction, which sends a Galois automorphism
`σ` to the unit `u` with `σ α = [u]_F(α)` — needs `α` itself, not just the degree it forces.

`α` is a root of `Qk` because `Qk` splits in `K_1 P` by construction (`splits_divX_map_K_1`);
nonzero because `Qk`'s constant term is an associate of `π ≠ 0`
(`ne_zero_of_aeval_divX_map_eq_zero`); `π`-torsion by `mem_piTorsion_one_of_root_divX_map`; and
generating because `K_1 P` is generated over `K` by `Qk`'s roots
(`Polynomial.IsSplittingField.adjoin_rootSet`), each of which — by transitivity of the
`(ResidueField O)ˣ`-action on nonzero `π`-torsion (`orbit_image_eq_piTorsion_sdiff_zero_K_1`) — is
`[w]_F(α)` for some `w : Oˣ`, hence lies in `K⟮α⟯` by `eval_phiU_mem_adjoin`. -/
theorem exists_generator_K_1
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O) :
    ∃ α : K_1 (K := K) P,
      Polynomial.aeval α (P.divX.map (algebraMap O K)) = 0 ∧
      α ∈ piTorsion (K := K_1 (K := K) P) hπ hf 1 ∧ α ≠ 0 ∧
      (K⟮α⟯ : IntermediateField K (K_1 (K := K) P)) = ⊤ := by
  classical
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf.1 hf.2.1 hPdist hPdeg2
  set Qk : K[X] := P.divX.map (algebraMap O K) with hQkdef
  have hmapne : (P.divX.map (algebraMap O (K_1 (K := K) P))) ≠ 0 := (hQmonic.map _).ne_zero
  have hmapdeg : (P.divX.map (algebraMap O (K_1 (K := K) P))).natDegree = P.divX.natDegree :=
    hQmonic.natDegree_map _
  have hdegne : (P.divX.map (algebraMap O (K_1 (K := K) P))).degree ≠ 0 :=
    (Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [hmapdeg]; exact hQdeg)).ne'
  obtain ⟨α, hαeval⟩ := (splits_divX_map_K_1 (K := K) P).exists_eval_eq_zero hdegne
  have hαroot : Polynomial.aeval α Qk = 0 := by rw [hQkdef, aeval_K_divX_eq_eval_K_1]; exact hαeval
  have hα0 : α ≠ 0 := ne_zero_of_aeval_divX_map_eq_zero hπ hf hu heq hPdist hPdeg hαroot
  have hmemroots : ∀ {β : K_1 (K := K) P},
      Polynomial.aeval β Qk = 0 → β ∈ piTorsion (K := K_1 (K := K) P) hπ hf 1 := by
    intro β hβ
    refine mem_piTorsion_one_of_root_divX_map (K_1.hOK_transport P hOK) hπ
      (K_1.hπnorm_transport P hπnorm) hf hu heq hPdist hPdeg2 ?_
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hmapne, Polynomial.IsRoot.def,
      ← aeval_K_divX_eq_eval_K_1]
    exact hβ
  have hαmem : α ∈ piTorsion (K := K_1 (K := K) P) hπ hf 1 := hmemroots hαroot
  refine ⟨α, hαroot, hαmem, hα0, ?_⟩
  have horbit := orbit_image_eq_piTorsion_sdiff_zero_K_1 (K := K) hOK hπ hπnorm hf hu heq hPdist
    hPdeg hαmem hα0
  have hroots : (Qk.rootSet (K_1 (K := K) P)) ⊆
      ((K⟮α⟯ : IntermediateField K (K_1 (K := K) P)).toSubalgebra : Set (K_1 (K := K) P)) := by
    intro β hβ
    obtain ⟨-, hβroot⟩ := Polynomial.mem_rootSet'.mp hβ
    have hβmem : β ∈ piTorsion (K := K_1 (K := K) P) hπ hf 1 := hmemroots hβroot
    have hβ0 : β ≠ 0 := ne_zero_of_aeval_divX_map_eq_zero hπ hf hu heq hPdist hPdeg hβroot
    have hβsdiff : β ∈ piTorsion (K := K_1 (K := K) P) hπ hf 1 \ {0} := ⟨hβmem, hβ0⟩
    obtain ⟨y, hyorb, hy⟩ := horbit.symm ▸ hβsdiff
    obtain ⟨u', hu'⟩ := hyorb
    have hyval : (y.1 : K_1 (K := K) P) =
        eval (phiU hπ hf (Function.surjInv residueUnitsMap_surjective u'))
          ((⟨α, hαmem⟩ : ↥(piTorsion (K := K_1 (K := K) P) hπ hf 1)) : K_1 (K := K) P) := by
      rw [← hu']
      exact coe_residuePiTorsion_smul (K_1.hOK_transport P hOK) hπ
        (K_1.hπnorm_transport P hπnorm) hf hu heq hPdist hPdeg2 u' ⟨α, hαmem⟩
    have : β = eval (phiU hπ hf (Function.surjInv residueUnitsMap_surjective u')) α := by
      rw [← hy, hyval]
    rw [SetLike.mem_coe, IntermediateField.mem_toSubalgebra, this]
    exact eval_phiU_mem_adjoin hOK hπ hf P _ hαmem.1
  have hle : (⊤ : Subalgebra K (K_1 (K := K) P)) ≤
      (K⟮α⟯ : IntermediateField K (K_1 (K := K) P)).toSubalgebra := by
    rw [← Polynomial.IsSplittingField.adjoin_rootSet (K_1 (K := K) P) Qk]
    exact Algebra.adjoin_le hroots
  refine eq_top_iff.mpr fun x _ ↦ ?_
  exact (IntermediateField.mem_toSubalgebra _ x).mp (hle Algebra.mem_top)

/-! ## The degree -/

/-- **`Module.finrank K (K_1 P) = residueCard O - 1`** — the headline degree of the Lubin-Tate
splitting field, `[K(F_π[π]) : K] = q - 1`.

The hypotheses are exactly the standing ones of this arc: `K` is a complete nonarchimedean field
receiving `O` in its closed unit ball (`hOK`) with `π` a uniformizer of strictly smaller norm
(`hπnorm`), `f` is a Lubin-Tate series for `π` (`hf`), and `f = P * u` is its Weierstrass
factorization with `P` distinguished of degree `q` (`hu`, `heq`, `hPdist`, `hPdeg`). No `hsplit`
hypothesis appears — `K_1 P` is *constructed* as the splitting field — and `[IsFractionRing O K]` is
required only of the **base** `K` (where it is what makes `Q` irreducible, hence pins the degree
down), never of `K_1 P`, where it is false.

Proof: `α` a root of `Qk := P.divX.map (algebraMap O K)` in `K_1 P` (`splits_divX_map_K_1`) is
nonzero (`ne_zero_of_aeval_divX_map_eq_zero`) and has `Qk` as its minimal polynomial (`Qk` monic
irreducible over `K`), so `Module.finrank K K⟮α⟯ = Qk.natDegree = q - 1`. `K_1 P` is generated over
`K` by `Qk`'s roots (`Polynomial.IsSplittingField.adjoin_rootSet`), each of which is a nonzero
`π`-torsion point and hence — by transitivity of the `(ResidueField O)ˣ`-action,
`orbit_image_eq_piTorsion_sdiff_zero_K_1` — of the form `eval (phiU hπ hf w) α`, which
`eval_phiU_mem_adjoin` places back inside `K⟮α⟯`. So `K⟮α⟯ = ⊤`. -/
theorem finrank_K_1_eq_residueCard_sub_one
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O) :
    Module.finrank K (K_1 (K := K) P) = residueCard O - 1 := by
  classical
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf.1 hf.2.1 hPdist hPdeg2
  set Qk : K[X] := P.divX.map (algebraMap O K) with hQkdef
  have hQkmonic : Qk.Monic := hQmonic.map _
  have hQkirr : Irreducible Qk :=
    Polynomial.irreducible_map_of_isWeaklyEisensteinAt_associated hπ hQmonic hQweak hQdeg hQ0assoc
  have hQkdeg : Qk.natDegree = residueCard O - 1 := by
    rw [hQkdef, hQmonic.natDegree_map, Polynomial.natDegree_divX_eq_natDegree_tsub_one, hPdeg]
  -- Steps 1, 3, 4: a nonzero `π`-torsion root `α` of `Qk` generating `K_1 P` over `K`.
  obtain ⟨α, hαroot, -, -, htop⟩ :=
    exists_generator_K_1 hOK hπ hπnorm hf hu heq hPdist hPdeg
  -- Step 2: `Qk` is `α`'s minimal polynomial, so `K⟮α⟯` has degree `q - 1`.
  have hαint : IsIntegral K α := ⟨Qk, hQkmonic, hαroot⟩
  have hmin : Qk = minpoly K α := minpoly.eq_of_irreducible_of_monic hQkirr hαroot hQkmonic
  have hfin : Module.finrank K K⟮α⟯ = residueCard O - 1 := by
    rw [IntermediateField.adjoin.finrank hαint, ← hmin, hQkdeg]
  -- Step 5: conclude.
  rw [← IntermediateField.finrank_top' (F := K) (E := K_1 (K := K) P), ← htop]
  exact hfin

/-! ## `K_1 P` is Galois over `K` -/

/-- **`K_1 P / K` is a Galois extension.** `K_1 P` is a splitting field of `Qk := P.divX.map
(algebraMap O K)` over `K` by construction (`K_1.instIsSplittingField`), and `Qk` is separable
(`separable_divX_map_K`, a Gauss's-lemma fact over the base `K`) — the two ingredients
`IsGalois.of_separable_splitting_field` needs. -/
theorem isGalois_K_1
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O) :
    IsGalois K (K_1 (K := K) P) :=
  IsGalois.of_separable_splitting_field (p := P.divX.map (algebraMap O K))
    (separable_divX_map_K hOK hπ hπnorm hf hu heq hPdist hPdeg)

end LubinTate

end
