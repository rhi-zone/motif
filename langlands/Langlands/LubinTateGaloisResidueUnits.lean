import Langlands.LubinTateSplittingFieldDegree

/-!
# `Gal(K_1/K) ≃* (O/π)ˣ` — the Lubin-Tate reciprocity isomorphism at level `1`

This file closes the capstone of the Lubin-Tate arc: the Galois group of the level-`1` Lubin-Tate
splitting field over the base is **canonically the unit group of the residue field**,

**`Nonempty ((K_1 P ≃ₐ[K] K_1 P) ≃* (ResidueField O)ˣ)`**

(`LubinTate.nonempty_mulEquiv_gal_K_1_residueUnits`), for `K_1 P := (P.divX.map (algebraMap O
K)).SplittingField` and `P` the Weierstrass distinguished factor of a Lubin-Tate series `f` for the
uniformizer `π`. In Mathlib's notation `Gal(E/F)` *is* `E ≃ₐ[F] E`
(`Mathlib/FieldTheory/Galois/Notation.lean`), so this is literally `Gal(K_1/K) ≃* (O/π)ˣ` with
`IsLocalRing.ResidueField O` as this repo's model of `O/π`.

The statement is `Nonempty` rather than a bare `MulEquiv` because the isomorphism depends on a
choice of primitive `π`-torsion point `α` (`exists_generator_K_1`); different `α` give isomorphisms
differing by an inner-automorphism-free relabelling. Nothing downstream needs a *canonical* map
before the reciprocity map itself is built, so the existential form is what is proved here rather
than a choice-dependent `def`.

## The route

Fix a generator `α` — a nonzero `π`-torsion point of `K_1 P` with `K⟮α⟯ = ⊤`, supplied by
`exists_generator_K_1` (`Langlands/LubinTateSplittingFieldDegree.lean`). The map is `σ ↦ u(σ)`, the
unique residue unit with `σ α = [u(σ)]_F(α)`.

1. **Well-definedness** (`exists_unique_galUnit`). `σ` fixes `K` pointwise, so it permutes the roots
   of `Qk := P.divX.map (algebraMap O K)` (`Polynomial.aeval_algEquiv`); every such root is a
   `π`-torsion point (`mem_piTorsion_one_of_root_divX_map`) and `σ α ≠ 0` since `σ` is injective.
   *Existence* of `u(σ)` is then transitivity of the `(ResidueField O)ˣ`-action on the nonzero
   `π`-torsion (`orbit_image_eq_piTorsion_sdiff_zero_K_1`); *uniqueness* is freeness, in the sharp
   form `dvd_sub_of_eval_phiU_eq` (`Langlands/LubinTateResidueUnitsFreeness.lean`).
2. **Homomorphism property.** The one analytic step. `[u]_F` is a power series, so `σ ([w]_F(α)) =
   [w]_F(σ α)` is *not* an algebraic identity — it is the statement that the continuous map `σ`
   commutes with an infinite sum. `σ` is continuous because it is `K`-linear out of a
   finite-dimensional space over a complete field (`LinearMap.continuous_of_finiteDimensional`; no
   norm-preservation/`spectralNorm` argument is needed), so `HasSum.map` transports `hasSum_eval`
   along it — that is `NonarchimedeanPowerSeriesEval.map_eval_of_continuous` below, stated for an
   arbitrary continuous ring hom fixing the coefficient ring's image. Combined with
   `[u]_F ∘ [v]_F = [uv]_F` (`phiU_subst_phiU_eq_phiU_mul`, via `piTorsionMulAction`'s `mul_smul`)
   this gives `u(σ τ) = u(τ) u(σ) = u(σ) u(τ)`, the last step because `(ResidueField O)ˣ` is
   commutative — so the construction is a homomorphism regardless of which of the two composition
   conventions `AlgEquiv`'s `Mul` uses (it is `(σ * τ) x = σ (τ x)`, `AlgEquiv.mul_apply`).
3. **Injectivity.** `σ α = τ α` forces `σ = τ`, because `K⟮α⟯ = ⊤` makes `α` generate `K_1 P` as a
   `K`-algebra (`IntermediateField.adjoin_toSubalgebra`, available since `K_1 P/K` is algebraic) and
   a `K`-algebra hom is determined by its values on algebra generators
   (`AlgHom.ext_of_adjoin_eq_top`).
4. **Surjectivity by counting**, not by construction. `K_1 P/K` is Galois (`isGalois_K_1`) and
   finite-dimensional, so `Nat.card Gal(K_1/K) = finrank K (K_1 P) = residueCard O - 1`
   (`IsGalois.card_aut_eq_finrank`, `finrank_K_1_eq_residueCard_sub_one`), which is exactly
   `Nat.card (ResidueField O)ˣ` (`Nat.card_units`, a `GroupWithZero` fact). An injective map between
   finite types of equal cardinality is bijective (`Nat.bijective_iff_injective_and_card`). This
   avoids having to *build* a Galois automorphism from a residue unit — the degree theorem already
   paid for that.
5. **Packaging**: `MulEquiv.ofBijective` applied to the `MonoidHom` of step 2.

## Scope

Level `n = 1` only, matching `finrank_K_1_eq_residueCard_sub_one`. The tower `K_n` needs `π^n`-torsion
analogues of the root count and of transitivity, neither of which exists in this repo yet.
-/

@[expose] public section

noncomputable section

open scoped Polynomial IntermediateField

/-! ## A continuous ring hom commutes with `eval` -/

namespace NonarchimedeanPowerSeriesEval

variable {R L : Type*} [CommRing R] [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  [Algebra R L]

/-- **A continuous ring endomorphism fixing `R`'s image commutes with `eval`.** `eval g x` is a
`tsum`, so this is not an algebraic identity: it is `HasSum.map` applied to `hasSum_eval`, using
continuity of `σ` to move it inside the limit of partial sums, plus `σ (algebraMap R L c) =
algebraMap R L c` and multiplicativity to identify `σ (evalSummand g x n)` with
`evalSummand g (σ x) n` termwise.

Note that `‖σ x‖ < 1` is *not* required: the transported `HasSum` already exhibits
`σ (eval g x)` as the sum of `evalSummand g (σ x)`, and `eval g (σ x)` is by definition that sum's
`tsum`, so `HasSum.tsum_eq` closes it whether or not the series at `σ x` would converge on its own
account. -/
theorem map_eval_of_continuous {G : Type*} [FunLike G L L] [RingHomClass G L L]
    {g : PowerSeries R} (hg : ∀ n, ‖algebraMap R L (PowerSeries.coeff n g)‖ ≤ 1) {x : L}
    (hx : ‖x‖ < 1) (σ : G) (hσc : Continuous σ)
    (hσa : ∀ c : R, σ (algebraMap R L c) = algebraMap R L c) :
    σ (eval g x) = eval g (σ x) := by
  have hfun : (fun n ↦ σ (evalSummand g x n)) = evalSummand g (σ x) := by
    funext n
    simp only [evalSummand, map_mul, map_pow, hσa]
  have h1 : HasSum (evalSummand g (σ x)) (σ (eval g x)) := by
    rw [← hfun]
    simpa only [Function.comp_def] using (hasSum_eval hg hx).map σ hσc
  exact h1.tsum_eq.symm

end NonarchimedeanPowerSeriesEval

namespace LubinTate

open NonarchimedeanPowerSeriesEval PowerSeries IsLocalRing Polynomial MulAction

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsFractionRing O K]
variable {π : O} {f : O⟦X⟧}

/-! ## Galois automorphisms of `K_1` are continuous and commute with `eval` -/

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **Every `K`-algebra automorphism of `K_1 P` is continuous.** `K_1 P` is a finite-dimensional
normed `K`-vector space (`K_1.instFiniteDimensional`, `K_1.instNormedSpace`) over the complete field
`K`, and *any* linear map out of such a space is automatically continuous
(`LinearMap.continuous_of_finiteDimensional`) — no norm-preservation argument for Galois elements is
needed. -/
theorem continuous_of_algEquiv_K_1 {P : O[X]} (σ : K_1 (K := K) P ≃ₐ[K] K_1 (K := K) P) :
    Continuous σ :=
  σ.toLinearMap.continuous_of_finiteDimensional.congr fun _ ↦ rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsFractionRing O K] in
/-- **A `K`-algebra automorphism of `K_1 P` commutes with `eval` of an `O`-power series.**
`map_eval_of_continuous` specialised: `σ` is continuous (`continuous_of_algEquiv_K_1`) and fixes
`algebraMap O (K_1 P)`'s image, because that map factors through `K` (`K_1.algebraMap_O_eq`) and
`σ` fixes `K` pointwise (`AlgEquiv.commutes`). -/
theorem algEquiv_eval_K_1 {P : O[X]} (σ : K_1 (K := K) P ≃ₐ[K] K_1 (K := K) P) {g : O⟦X⟧}
    (hg : ∀ n, ‖algebraMap O (K_1 (K := K) P) (PowerSeries.coeff n g)‖ ≤ 1)
    {x : K_1 (K := K) P} (hx : ‖x‖ < 1) :
    σ (eval g x) = eval g (σ x) := by
  refine map_eval_of_continuous hg hx σ (continuous_of_algEquiv_K_1 σ) fun c ↦ ?_
  rw [show algebraMap O (K_1 (K := K) P) c
      = algebraMap K (K_1 (K := K) P) (algebraMap O K c) from
    congrFun (K_1.algebraMap_O_eq (K := K) P) c]
  exact σ.commutes _

/-! ## Roots of `Qk` in `K_1` are `π`-torsion points -/

/-- **Every root of `Qk := P.divX.map (algebraMap O K)` in `K_1 P` is a `π`-torsion point.** The
`hmemroots` step of `exists_generator_K_1`, as a standalone fact: `mem_piTorsion_one_of_root_divX_map`
fed the root through `aeval_K_divX_eq_eval_K_1`. -/
theorem mem_piTorsion_of_aeval_divX_map_eq_zero (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O) {β : K_1 (K := K) P}
    (hβ : Polynomial.aeval β (P.divX.map (algebraMap O K)) = 0) :
    β ∈ piTorsion (K := K_1 (K := K) P) hπ hf 1 := by
  classical
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  obtain ⟨hQmonic, -, -, -⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf.1 hf.2.1 hPdist hPdeg2
  have hmapne : (P.divX.map (algebraMap O (K_1 (K := K) P))) ≠ 0 := (hQmonic.map _).ne_zero
  refine mem_piTorsion_one_of_root_divX_map (K_1.hOK_transport P hOK) hπ
    (K_1.hπnorm_transport P hπnorm) hf hu heq hPdist hPdeg2 ?_
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hmapne, Polynomial.IsRoot.def,
    ← aeval_K_divX_eq_eval_K_1]
  exact hβ

/-! ## Step 1: well-definedness of `σ ↦ u(σ)` -/

/-- **Well-definedness of `σ ↦ u(σ)`.** For a generator `α` (a nonzero root of `Qk`) and any
`K`-algebra automorphism `σ` of `K_1 P`, there is **exactly one** residue unit `w` with
`[w]_F(α) = σ α`.

*Existence*: `σ α` is again a root of `Qk` (`σ` fixes `K`, `Polynomial.aeval_algEquiv`), hence a
`π`-torsion point (`mem_piTorsion_of_aeval_divX_map_eq_zero`), and nonzero (`σ` injective); the
`(ResidueField O)ˣ`-action on nonzero `π`-torsion is transitive
(`orbit_image_eq_piTorsion_sdiff_zero_K_1`), so some `w` moves `α` to it.

*Uniqueness*: if `[w]_F(α) = [w']_F(α)` with `α` nonzero torsion, then `π ∣ (w - w')` upstairs in
`Oˣ` (`dvd_sub_of_eval_phiU_eq` — freeness), i.e. `w = w'` in `(ResidueField O)ˣ`
(`residueUnitsMap_eq_iff_dvd_sub`). -/
theorem exists_unique_galUnit (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O) {α : K_1 (K := K) P}
    (hαroot : Polynomial.aeval α (P.divX.map (algebraMap O K)) = 0)
    (hαmem : α ∈ piTorsion (K := K_1 (K := K) P) hπ hf 1) (hα0 : α ≠ 0)
    (σ : K_1 (K := K) P ≃ₐ[K] K_1 (K := K) P) :
    ∃! w : (ResidueField O)ˣ,
      eval (phiU hπ hf (Function.surjInv residueUnitsMap_surjective w)) α = σ α := by
  classical
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  -- `σ α` is a nonzero `π`-torsion point.
  have hσroot : Polynomial.aeval (σ α) (P.divX.map (algebraMap O K)) = 0 := by
    rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply, hαroot, map_zero]
  have hσmem : σ α ∈ piTorsion (K := K_1 (K := K) P) hπ hf 1 :=
    mem_piTorsion_of_aeval_divX_map_eq_zero hOK hπ hπnorm hf hu heq hPdist hPdeg hσroot
  have hσ0 : σ α ≠ 0 := by simpa using σ.injective.ne hα0
  -- Existence, from transitivity.
  have horbit := orbit_image_eq_piTorsion_sdiff_zero_K_1 (K := K) hOK hπ hπnorm hf hu heq hPdist
    hPdeg hαmem hα0
  have hσsdiff : σ α ∈ piTorsion (K := K_1 (K := K) P) hπ hf 1 \ {0} := ⟨hσmem, hσ0⟩
  obtain ⟨y, hyorb, hy⟩ := horbit.symm ▸ hσsdiff
  obtain ⟨w, hw⟩ := hyorb
  have hyval : (y.1 : K_1 (K := K) P) =
      eval (phiU hπ hf (Function.surjInv residueUnitsMap_surjective w))
        ((⟨α, hαmem⟩ : ↥(piTorsion (K := K_1 (K := K) P) hπ hf 1)) : K_1 (K := K) P) := by
    rw [← hw]
    exact coe_residuePiTorsion_smul (K_1.hOK_transport P hOK) hπ
      (K_1.hπnorm_transport P hπnorm) hf hu heq hPdist hPdeg2 w ⟨α, hαmem⟩
  have hwval : eval (phiU hπ hf (Function.surjInv residueUnitsMap_surjective w)) α = σ α := by
    rw [← hy, hyval]
  -- Uniqueness, from freeness.
  refine ⟨w, hwval, fun v hv ↦ ?_⟩
  have heval : eval (phiU hπ hf (Function.surjInv residueUnitsMap_surjective v)) α =
      eval (phiU hπ hf (Function.surjInv residueUnitsMap_surjective w)) α := by
    rw [hv, hwval]
  have hdvd := dvd_sub_of_eval_phiU_eq (K_1.hOK_transport P hOK) hπ hf hαmem hα0 heval
  have hmapeq := (residueUnitsMap_eq_iff_dvd_sub hπ).mpr hdvd
  rwa [Function.rightInverse_surjInv residueUnitsMap_surjective v,
    Function.rightInverse_surjInv residueUnitsMap_surjective w] at hmapeq

/-! ## The isomorphism -/

/-- **`Gal(K_1/K) ≃* (O/π)ˣ`** — the capstone of the Lubin-Tate arc.

The Galois group of the level-`1` Lubin-Tate splitting field over the base is isomorphic, as a
group, to the unit group of the residue field: `Nonempty ((K_1 P ≃ₐ[K] K_1 P) ≃* (ResidueField O)ˣ)`.
`K_1 P ≃ₐ[K] K_1 P` is exactly what Mathlib's `Gal(K_1 P/K)` notation abbreviates, and
`ResidueField O` is this repo's model of `O/π`.

Hypotheses are the standing ones of the arc, unchanged from
`finrank_K_1_eq_residueCard_sub_one` and `isGalois_K_1`: `K` a complete nonarchimedean field
receiving `O` in its closed unit ball (`hOK`) with `π` a uniformizer of strictly smaller norm
(`hπnorm`), `f` a Lubin-Tate series for `π` (`hf`) with Weierstrass factorization `f = P * u`, `P`
distinguished of degree `q := residueCard O` (`hu`, `heq`, `hPdist`, `hPdeg`). No `hsplit`: `K_1 P`
is *constructed* as the splitting field.

See this file's module docstring for the five-step route. The construction is choice-dependent (it
fixes a primitive `π`-torsion point `α`), hence the `Nonempty`. -/
theorem nonempty_mulEquiv_gal_K_1_residueUnits (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O}
    (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O) :
    Nonempty ((K_1 (K := K) P ≃ₐ[K] K_1 (K := K) P) ≃* (ResidueField O)ˣ) := by
  classical
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  obtain ⟨α, hαroot, hαmem, hα0, htop⟩ :=
    exists_generator_K_1 hOK hπ hπnorm hf hu heq hPdist hPdeg
  choose F hF hFuniq using fun σ ↦
    exists_unique_galUnit hOK hπ hπnorm hf hu heq hPdist hPdeg hαroot hαmem hα0 σ
  -- Coefficient bound for every `[z]_F`, inside `K_1 P`.
  have hbd : ∀ (z : Oˣ) (n : ℕ),
      ‖algebraMap O (K_1 (K := K) P) (PowerSeries.coeff n (phiU hπ hf z))‖ ≤ 1 :=
    fun _ _ ↦ K_1.hOK_transport P hOK _
  -- `[a]_F ∘ [b]_F = [ab]_F`, evaluated at `α`.
  have hstep : ∀ a b : Oˣ, eval (phiU hπ hf (a * b)) α
      = eval (phiU hπ hf a) (eval (phiU hπ hf b) α) := by
    intro a b
    letI := piTorsionMulAction (K_1.hOK_transport P hOK) hπ hf 1
    exact congrArg Subtype.val
      (mul_smul a b (⟨α, hαmem⟩ : ↥(piTorsion (K := K_1 (K := K) P) hπ hf 1)))
  -- Step 2: `F` is a homomorphism.
  have hmul : ∀ σ τ : K_1 (K := K) P ≃ₐ[K] K_1 (K := K) P, F (σ * τ) = F σ * F τ := by
    intro σ τ
    have hcomp : eval (phiU hπ hf
        (Function.surjInv residueUnitsMap_surjective (F τ) *
          Function.surjInv residueUnitsMap_surjective (F σ))) α = (σ * τ) α := by
      rw [hstep, hF σ, ← algEquiv_eval_K_1 σ (hbd _) hαmem.1, hF τ, AlgEquiv.mul_apply]
    have hfib : residueUnitsMap (Function.surjInv residueUnitsMap_surjective
        (residueUnitsMap (Function.surjInv residueUnitsMap_surjective (F τ) *
          Function.surjInv residueUnitsMap_surjective (F σ))))
        = residueUnitsMap (Function.surjInv residueUnitsMap_surjective (F τ) *
          Function.surjInv residueUnitsMap_surjective (F σ)) :=
      Function.rightInverse_surjInv residueUnitsMap_surjective _
    have hkey : eval (phiU hπ hf (Function.surjInv residueUnitsMap_surjective
        (residueUnitsMap (Function.surjInv residueUnitsMap_surjective (F τ) *
          Function.surjInv residueUnitsMap_surjective (F σ))))) α = (σ * τ) α := by
      rw [piTorsionSMul_eq_of_residueUnitsMap_eq (K_1.hOK_transport P hOK) hπ
        (K_1.hπnorm_transport P hπnorm) hf hu heq hPdist hPdeg2 hfib hαmem]
      exact hcomp
    have huniq := hFuniq (σ * τ) _ hkey
    rw [← huniq, map_mul, Function.rightInverse_surjInv residueUnitsMap_surjective (F τ),
      Function.rightInverse_surjInv residueUnitsMap_surjective (F σ)]
    exact mul_comm _ _
  -- Step 3: `F` is injective — `α` generates `K_1 P` as a `K`-algebra.
  have hadj : Algebra.adjoin K ({α} : Set (K_1 (K := K) P)) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra (F := K) ({α} : Set (K_1 (K := K) P)), htop,
      IntermediateField.top_toSubalgebra]
  have hinj : Function.Injective F := by
    intro σ τ hστ
    have hval : σ α = τ α := by rw [← hF σ, ← hF τ, hστ]
    have heqon : Set.EqOn (σ : K_1 (K := K) P →ₐ[K] K_1 (K := K) P)
        (τ : K_1 (K := K) P →ₐ[K] K_1 (K := K) P) ({α} : Set (K_1 (K := K) P)) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hval
    have hhom : (σ : K_1 (K := K) P →ₐ[K] K_1 (K := K) P)
        = (τ : K_1 (K := K) P →ₐ[K] K_1 (K := K) P) :=
      AlgHom.ext_of_adjoin_eq_top hadj heqon
    exact AlgEquiv.ext fun x ↦ DFunLike.congr_fun hhom x
  -- Step 4: surjectivity by counting.
  haveI : IsGalois K (K_1 (K := K) P) := isGalois_K_1 hOK hπ hπnorm hf hu heq hPdist hPdeg
  have hcard : Nat.card (K_1 (K := K) P ≃ₐ[K] K_1 (K := K) P) = Nat.card (ResidueField O)ˣ := by
    rw [IsGalois.card_aut_eq_finrank K (K_1 (K := K) P),
      finrank_K_1_eq_residueCard_sub_one hOK hπ hπnorm hf hu heq hPdist hPdeg,
      Nat.card_units (ResidueField O)]
  have hbij : Function.Bijective F :=
    (Nat.bijective_iff_injective_and_card F).mpr ⟨hinj, hcard⟩
  -- Step 5: package.
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' F hmul) hbij⟩

end LubinTate

end
