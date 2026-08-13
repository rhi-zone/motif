import Langlands.LubinTateUnitsEndomorphism
import Langlands.LubinTateTorsionGroup

/-!
# The `Oˣ`-action on `π^n`-torsion points

`ROADMAP.md` §28 built `phiU hπ hf u` (`[u]_F`, `u : Oˣ`) as a formal endomorphism of the
Lubin-Tate formal group law `F_π`, but left evaluation, torsion-point closure, and the action laws
open. This file closes all four: `[u]_F` evaluated at concrete points respects `F_π`-addition,
maps `π^n`-torsion into itself, `[1]_F` is the identity, `[u]_F ∘ [v]_F = [uv]_F`, and the four
facts assemble into a genuine `MulAction Oˣ ↥(piTorsion hπ hf n)` — the algebraic content behind
`Gal(K_1/K) ≅ (O/π)ˣ`.

## The recurring footgun

Every composition-closure argument below involving **two univariate power series** (`solvesFunctionalEq_subst_univ`,
`subst_iter_eq_iter_subst` in `Langlands.LubinTateIterate`, and every `have`/`calc` step built from
them) is written in the prefix form `PowerSeries.subst a g` rather than dot notation `g.subst a`.
With both substitutand and substituted series univariate, nested dot notation elaborates against
`MvPowerSeries.subst` (whose namespace also matches `R⟦X⟧`'s reducible head) and the resulting
unification diverges (`deterministic timeout at whnf`) rather than failing cleanly — reproduced
directly (not guessed at) while drafting `subst_iter_eq_iter_subst`, then routed around by
switching to prefix form throughout, exactly as `Langlands.LubinTateIterate.iter_succ'`/`iter_add`
already do. Mixed-arity compositions (univariate into multivariate or vice versa, as in
`eval_phiU_FPiEval` below) do **not** trigger this — the multivariate side pins the notation
resolution unambiguously — so those are written in the repo's usual dot-notation style.

## Route

* **Step 1** (`eval_phiU_FPiEval`): transports `subst_Phi_phiU_eq_phiU_subst_Phi` (`[u]_F` is a
  formal endomorphism of `Φ`) through `evalMv`, via the identical technique
  `Langlands.LubinTateTorsionPoints.eval_iter_FPiEval` uses for `iter f n` — `phiU hπ hf u`
  embedded diagonally is *literally* `NonarchimedeanMvPowerSeriesEvalFin2.diagEmbed (phiU hπ hf
  u)`, so `eval_subst_A`/`eval_subst_S` ("Lemma A"/"Lemma S") apply unchanged.
* **Step 2** (`mem_piTorsion_eval_phiU`): needs `[u]_F` to commute with `iter f n` under
  substitution — a fact about the *univariate* functional equation, not `Φ`, so it does not go
  through Step 1 at all. `Langlands.LubinTateIterate.subst_iter_eq_iter_subst` (new, fully generic:
  any series commuting with `f` commutes with every iterate of `f`) propagates
  `subst_phiU_eq_phiU_subst` from `f` to `iter f n`; two applications of
  `Langlands.NonarchimedeanPowerSeriesEvalSubst.eval_subst` (univariate/univariate) then transport
  that through `eval`, landing on `eval (phiU hπ hf u) 0 = 0`
  (`NonarchimedeanPowerSeriesEval.eval_zero_of_coeff_zero_eq_zero`, new, fully generic).
* **Step 3** (`phiU_one_eq_X`): `X` satisfies the same univariate functional equation as `phiU hπ
  hf 1` with the same linear coefficient `1`, so `LubinTateFunctionalEquation
  .eq_of_coeff_zero_eq_zero_of_coeff_one_eq_of_subst_eq` (the intertwining series's uniqueness
  theorem) identifies them directly — no new machinery.
* **Step 4** (`solvesFunctionalEq_subst_univ`, `phiU_subst_phiU_eq_phiU_mul`): the third
  composition-closure fact `ROADMAP.md` anticipated, univariate-into-univariate this time (unlike
  `solvesFunctionalEq_subst_embed`/`_outer`'s multivariate shapes): if `h1`, `h2` both commute with
  `f`, so does `h1 ∘ h2`. Same six-line `subst_comp_subst_apply` reassociation chain as the other
  two composition-closure facts, in prefix form throughout per the footgun note above. Combined
  with uniqueness (linear coefficients multiply, `LubinTateIterate.coeff_one_subst`), this
  identifies `[u]_F ∘ [v]_F` with `[uv]_F`.
* **The action** (`piTorsionSMul`, `piTorsionMulAction`): assembles Steps 2–4 into a genuine
  `MulAction Oˣ ↥(piTorsion hπ hf n)`, mirroring `Langlands.LubinTateTorsionGroup`'s
  `piTorsionAddCommGroup` pattern exactly (`@[reducible] def`s, not instances, since they depend on
  the non-instance hypotheses `hOK`/`hπ`/`hf`).

## What this does not do

Step 1 (`eval_phiU_FPiEval`) is not needed to build the `MulAction` itself — it shows `[u]_F`
respects `F_π`-addition (i.e. acts by group endomorphisms of `piTorsionAddCommGroup`), which is
extra content proved here because it is independently meaningful for the eventual Galois-module
structure, but upgrading `piTorsionMulAction` to a `DistribMulAction` (bundling that compatibility)
is not attempted this pass. No size computation (`|piTorsion hπ hf 1| = q`), no `Gal(K_1/K) ↪ Oˣ`
— see `ROADMAP.md`.
-/

@[expose] public section

noncomputable section

namespace LubinTate

open NonarchimedeanPowerSeriesEval NonarchimedeanMvPowerSeriesEvalFin2 PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
variable {π : O} {f : O⟦X⟧}

/-! ### Step 1: `[u]_F` respects `F_π`-addition, at the level of concrete evaluation -/

/-- **`[u]_F` respects `F_π`-addition**: `eval (phiU u) (F_π(a, b)) = F_π(eval (phiU u) a, eval
(phiU u) b)`. Transports `subst_Phi_phiU_eq_phiU_subst_Phi` through `evalMv`, identically to
`Langlands.LubinTateTorsionPoints.eval_iter_FPiEval`'s treatment of `iter f n` — `phiU hπ hf u`
embedded along each axis (`fun i ↦ (phiU hπ hf u).subst (X i)`) is definitionally
`NonarchimedeanMvPowerSeriesEvalFin2.diagEmbed (phiU hπ hf u)`, so the same "Lemma A"/"Lemma S"
pair applies unchanged. -/
theorem eval_phiU_FPiEval (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (u : Oˣ) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    eval (phiU hπ hf u) (FPiEval hπ hf a b) =
      FPiEval hπ hf (eval (phiU hπ hf u) a) (eval (phiU hπ hf u) b) := by
  have hΦ : ∀ m, ‖algebraMap O K (MvPowerSeries.coeff m (Phi hπ hf))‖ ≤ 1 :=
    norm_algebraMap_coeff_Phi_le_one hOK hπ hf
  have hΦ0 : MvPowerSeries.constantCoeff (Phi hπ hf) = 0 := constantCoeff_Phi hπ hf
  have hφu0 : PowerSeries.constantCoeff (phiU hπ hf u) = 0 := constantCoeff_phiU hπ hf u
  have hφu : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (phiU hπ hf u))‖ ≤ 1 := fun k ↦ hOK _
  have hab0 : ‖(![a, b] : Fin 2 → K) 0‖ < 1 := by simpa using ha
  have hab1 : ‖(![a, b] : Fin 2 → K) 1‖ < 1 := by simpa using hb
  have hFPiEval_lt : ‖FPiEval hπ hf a b‖ < 1 := norm_FPiEval_lt hOK hπ hf ha hb
  have keyDiag : PowerSeries.subst (Phi hπ hf) (phiU hπ hf u) =
      MvPowerSeries.subst (diagEmbed (phiU hπ hf u)) (Phi hπ hf) :=
    (subst_Phi_phiU_eq_phiU_subst_Phi hπ hf u).symm
  have hLHS : evalMv (PowerSeries.subst (Phi hπ hf) (phiU hπ hf u)) ![a, b] =
      eval (phiU hπ hf u) (FPiEval hπ hf a b) :=
    (eval_subst_A hφu hΦ0 hΦ hab0 hab1 hFPiEval_lt).symm
  have hRHS : evalMv (MvPowerSeries.subst (diagEmbed (phiU hπ hf u)) (Phi hπ hf)) ![a, b] =
      FPiEval hπ hf (eval (phiU hπ hf u) a) (eval (phiU hπ hf u) b) := by
    rw [eval_subst_S hφu0 hφu hΦ hab0 hab1]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [← hLHS, keyDiag]
  exact hRHS

/-! ### Step 2: `[u]_F` maps `π^n`-torsion into itself -/

/-- **`eval (phiU hπ hf u)` maps `F_π[π^n]` into itself.** `[u]_F` commutes with `f` under
substitution (`subst_phiU_eq_phiU_subst`), hence with every iterate of `f`
(`Langlands.LubinTateIterate.subst_iter_eq_iter_subst`); transporting that commutation through
`eval_subst` (applied twice, once each direction) reduces `eval (iter f n) (eval (phiU hπ hf u)
x)` to `eval (phiU hπ hf u) (eval (iter f n) x) = eval (phiU hπ hf u) 0 = 0`. -/
theorem mem_piTorsion_eval_phiU (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) (u : Oˣ) {x : K}
    (hx : x ∈ piTorsion (K := K) hπ hf n) :
    eval (phiU hπ hf u) x ∈ piTorsion (K := K) hπ hf n := by
  obtain ⟨hxnorm, hxzero⟩ := hx
  have hφu0 : PowerSeries.constantCoeff (phiU hπ hf u) = 0 := constantCoeff_phiU hπ hf u
  have hφu : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (phiU hπ hf u))‖ ≤ 1 := fun k ↦ hOK _
  have hxEvalNorm : ‖eval (phiU hπ hf u) x‖ < 1 :=
    lt_of_le_of_lt (norm_eval_le hφu hφu0 hxnorm) hxnorm
  refine ⟨hxEvalNorm, ?_⟩
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hf.1
  have hcomm : PowerSeries.subst (phiU hπ hf u) f = PowerSeries.subst f (phiU hπ hf u) :=
    subst_phiU_eq_phiU_subst hπ hf u
  have hcommIter := subst_iter_eq_iter_subst hf0 hφu0 hcomm n
  have hfn0 : PowerSeries.constantCoeff (iter f n) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact (isLubinTatePoly_iter hf n).1
  have hfn : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (iter f n))‖ ≤ 1 := fun k ↦ hOK _
  have step1 : eval (PowerSeries.subst (phiU hπ hf u) (iter f n)) x =
      eval (iter f n) (eval (phiU hπ hf u) x) :=
    eval_subst hfn hφu0 hφu hxnorm hxEvalNorm
  have step2 : eval (PowerSeries.subst (iter f n) (phiU hπ hf u)) x =
      eval (phiU hπ hf u) (eval (iter f n) x) :=
    eval_subst hφu hfn0 hfn hxnorm (by rw [hxzero]; simp)
  have key : eval (iter f n) (eval (phiU hπ hf u) x) = eval (phiU hπ hf u) (eval (iter f n) x) := by
    rw [← step1, hcommIter]; exact step2
  rw [key, hxzero]
  exact eval_zero_of_coeff_zero_eq_zero
    (by rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact hφu0)

/-! ### Step 3: `[1]_F` is the identity -/

/-- **`[1]_F = X`**: `X` satisfies the same univariate functional equation as `phiU hπ hf 1`, with
the same linear coefficient `1`, so `eq_of_coeff_zero_eq_zero_of_coeff_one_eq_of_subst_eq`
identifies them. -/
theorem phiU_one_eq_X (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) :
    phiU hπ hf (1 : Oˣ) = (PowerSeries.X : O⟦X⟧) := by
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hf.1
  have hf' : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hφ0 : PowerSeries.coeff 0 (phiU hπ hf (1 : Oˣ)) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact constantCoeff_phiU hπ hf 1
  have hφ1 : PowerSeries.coeff 1 (phiU hπ hf (1 : Oˣ)) = (1 : O) := by
    rw [coeff_one_phiU]; simp
  have heqφ : PowerSeries.subst (phiU hπ hf (1 : Oˣ)) f = PowerSeries.subst f (phiU hπ hf (1 : Oˣ)) :=
    subst_phiU_eq_phiU_subst hπ hf 1
  have hψ0 : PowerSeries.coeff 0 (PowerSeries.X : O⟦X⟧) = 0 := by simp
  have hψ1 : PowerSeries.coeff 1 (PowerSeries.X : O⟦X⟧) = (1 : O) := by simp
  have heqψ : PowerSeries.subst (PowerSeries.X : O⟦X⟧) f = PowerSeries.subst f (PowerSeries.X : O⟦X⟧) := by
    rw [PowerSeries.X_subst, PowerSeries.subst_X hf']
  exact eq_of_coeff_zero_eq_zero_of_coeff_one_eq_of_subst_eq hπ hf hf (1 : O) hφ0 hφ1 heqφ hψ0 hψ1 heqψ

/-! ### Step 4: composition, `[u]_F ∘ [v]_F = [uv]_F` -/

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- **The third composition-closure fact**: if `h1` and `h2` both commute with `f` under
substitution, so does `h1 ∘ h2` (`PowerSeries.subst h2 h1`, i.e. `h1.subst h2` — apply `h2` first,
then `h1`). Univariate-into-univariate, so written in prefix `PowerSeries.subst` form throughout
per this file's footgun note; same six-line `subst_comp_subst_apply` reassociation chain as
`Langlands.LubinTateUnitsEndomorphism.solvesFunctionalEq_subst_embed`/`_outer`. -/
theorem solvesFunctionalEq_subst_univ (hf0 : PowerSeries.constantCoeff f = 0)
    {h1 h2 : PowerSeries O} (hh10 : PowerSeries.constantCoeff h1 = 0)
    (hh1 : PowerSeries.subst h1 f = PowerSeries.subst f h1)
    (hh20 : PowerSeries.constantCoeff h2 = 0)
    (hh2 : PowerSeries.subst h2 f = PowerSeries.subst f h2) :
    PowerSeries.subst (PowerSeries.subst h2 h1) f = PowerSeries.subst f (PowerSeries.subst h2 h1) := by
  have hf' : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hh1' : PowerSeries.HasSubst h1 := PowerSeries.HasSubst.of_constantCoeff_zero' hh10
  have hh2' : PowerSeries.HasSubst h2 := PowerSeries.HasSubst.of_constantCoeff_zero' hh20
  calc PowerSeries.subst (PowerSeries.subst h2 h1) f
      = PowerSeries.subst h2 (PowerSeries.subst h1 f) :=
        (PowerSeries.subst_comp_subst_apply hh1' hh2' f).symm
    _ = PowerSeries.subst h2 (PowerSeries.subst f h1) := by rw [hh1]
    _ = PowerSeries.subst (PowerSeries.subst h2 f) h1 :=
        PowerSeries.subst_comp_subst_apply hf' hh2' h1
    _ = PowerSeries.subst (PowerSeries.subst f h2) h1 := by rw [hh2]
    _ = PowerSeries.subst f (PowerSeries.subst h2 h1) :=
        (PowerSeries.subst_comp_subst_apply hh2' hf' h1).symm

/-- **`[u]_F ∘ [v]_F = [uv]_F`**: `PowerSeries.subst (phiU v) (phiU u)` (apply `[v]_F` first, then
`[u]_F`) satisfies the same functional equation as `phiU hπ hf (u * v)`, with the same linear
coefficient `u * v` (`LubinTateIterate.coeff_one_subst`, `Units.val_mul`), so uniqueness identifies
them. -/
theorem phiU_subst_phiU_eq_phiU_mul (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f)
    (u v : Oˣ) :
    PowerSeries.subst (phiU hπ hf v) (phiU hπ hf u) = phiU hπ hf (u * v) := by
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hf.1
  have hu0 : PowerSeries.constantCoeff (phiU hπ hf u) = 0 := constantCoeff_phiU hπ hf u
  have hv0 : PowerSeries.constantCoeff (phiU hπ hf v) = 0 := constantCoeff_phiU hπ hf v
  have hv0z : PowerSeries.coeff 0 (phiU hπ hf v) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact hv0
  have hueq : PowerSeries.subst (phiU hπ hf u) f = PowerSeries.subst f (phiU hπ hf u) :=
    subst_phiU_eq_phiU_subst hπ hf u
  have hveq : PowerSeries.subst (phiU hπ hf v) f = PowerSeries.subst f (phiU hπ hf v) :=
    subst_phiU_eq_phiU_subst hπ hf v
  have hΨeq : PowerSeries.subst (PowerSeries.subst (phiU hπ hf v) (phiU hπ hf u)) f =
      PowerSeries.subst f (PowerSeries.subst (phiU hπ hf v) (phiU hπ hf u)) :=
    solvesFunctionalEq_subst_univ hf0 hu0 hueq hv0 hveq
  have hΨ0 : PowerSeries.coeff 0 (PowerSeries.subst (phiU hπ hf v) (phiU hπ hf u)) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact PowerSeries.constantCoeff_subst_eq_zero hv0 (phiU hπ hf u) hu0
  have hΨ1 : PowerSeries.coeff 1 (PowerSeries.subst (phiU hπ hf v) (phiU hπ hf u)) =
      ((u * v : Oˣ) : O) := by
    rw [coeff_one_subst hv0z (phiU hπ hf u), coeff_one_phiU, coeff_one_phiU, Units.val_mul]
  have hτ0 : PowerSeries.coeff 0 (phiU hπ hf (u * v)) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact constantCoeff_phiU hπ hf (u * v)
  have hτ1 : PowerSeries.coeff 1 (phiU hπ hf (u * v)) = ((u * v : Oˣ) : O) :=
    coeff_one_phiU hπ hf (u * v)
  have hτeq : PowerSeries.subst (phiU hπ hf (u * v)) f = PowerSeries.subst f (phiU hπ hf (u * v)) :=
    subst_phiU_eq_phiU_subst hπ hf (u * v)
  exact eq_of_coeff_zero_eq_zero_of_coeff_one_eq_of_subst_eq hπ hf hf ((u * v : Oˣ) : O)
    hΨ0 hΨ1 hΨeq hτ0 hτ1 hτeq

/-! ### The `Oˣ`-action on `F_π[π^n]` -/

/-- **The `Oˣ`-action on `F_π[π^n]`**: `u • x := eval (phiU hπ hf u) x`, well-defined by
`mem_piTorsion_eval_phiU`. Mirrors `Langlands.LubinTateTorsionGroup.piTorsionAdd`'s pattern exactly
— a `@[reducible] def`, not an instance, since it depends on the non-instance hypotheses
`hOK`/`hπ`/`hf`. -/
@[reducible] def piTorsionSMul (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) :
    SMul Oˣ ↥(piTorsion (K := K) hπ hf n) :=
  ⟨fun u x ↦ ⟨eval (phiU hπ hf u) x, mem_piTorsion_eval_phiU hOK hπ hf n u x.2⟩⟩

/-- **`F_π[π^n]` is a genuine `Oˣ`-action**: `[1]_F = id` (`phiU_one_eq_X` + `eval_X`) and
`[u]_F ∘ [v]_F = [uv]_F` (`phiU_subst_phiU_eq_phiU_mul` transported through `eval_subst`) are
exactly `MulAction`'s `one_smul`/`mul_smul` laws — the algebraic content behind `Gal(K_1/K) ≅
(O/π)ˣ`. -/
@[reducible] def piTorsionMulAction (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) :
    MulAction Oˣ ↥(piTorsion (K := K) hπ hf n) :=
  letI := piTorsionSMul hOK hπ hf n
  { one_smul := fun x ↦ Subtype.ext (by
      show eval (phiU hπ hf 1) (x : K) = (x : K)
      rw [phiU_one_eq_X hπ hf]
      exact eval_X _)
    mul_smul := fun u v x ↦ Subtype.ext (by
      show eval (phiU hπ hf (u * v)) (x : K) =
        eval (phiU hπ hf u) (eval (phiU hπ hf v) (x : K))
      rw [← phiU_subst_phiU_eq_phiU_mul hπ hf u v]
      have hu : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (phiU hπ hf u))‖ ≤ 1 := fun k ↦ hOK _
      have hv0 : PowerSeries.constantCoeff (phiU hπ hf v) = 0 := constantCoeff_phiU hπ hf v
      have hv : ∀ k, ‖algebraMap O K (PowerSeries.coeff k (phiU hπ hf v))‖ ≤ 1 := fun k ↦ hOK _
      have hxnorm : ‖(x : K)‖ < 1 := x.2.1
      have hvxnorm : ‖eval (phiU hπ hf v) (x : K)‖ < 1 :=
        lt_of_le_of_lt (norm_eval_le hv hv0 hxnorm) hxnorm
      exact eval_subst hu hv0 hv hxnorm hvxnorm) }

/-- **The action really is `[u]_F`, evaluated** (true by definition). -/
theorem coe_piTorsion_smul (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) (u : Oˣ)
    (x : ↥(piTorsion (K := K) hπ hf n)) :
    letI := piTorsionMulAction hOK hπ hf n
    ((u • x : ↥(piTorsion (K := K) hπ hf n)) : K) = eval (phiU hπ hf u) (x : K) := rfl

end LubinTate

end
