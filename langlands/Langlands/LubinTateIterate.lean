import Langlands.LubinTateFunctionalEquationBivariate

/-!
# Iterates of a Lubin-Tate polynomial: the `[π^n]`-multiplication endomorphisms of `F_π`

`Langlands/LubinTateFunctionalEquationBivariate.lean` closed the construction of the Lubin-Tate
formal group law `F_π = Phi hπ hf` and packaged it as a Mathlib `FormalGroup O`
(`LubinTateFormalGroup`), together with the functional equation
`f.subst Φ = Φ.subst (fun i ↦ f.subst (X i))` — i.e. `f` is an endomorphism of `F_π`, the one
classically written `[π]`. This file iterates that: the `n`-fold composite `f^{(n)}` is an
endomorphism of `F_π` too, the one classically written `[π^n]`, and its two defining congruences
are the *same* two congruences with `π` replaced by `π^n` and `q` by `q^n`.

## Composition convention

`iter f (n + 1) = f.subst (iter f n)` — i.e. `f^{(n+1)} = f ∘ f^{(n)}`, new copy of `f` on the
*outside*. `iter_succ'` proves the two conventions agree (`f ∘ f^{(n)} = f^{(n)} ∘ f`), so nothing
downstream depends on the choice; the outer convention is used because in
`subst_iter_Phi`'s induction step the outer `f` is exactly the one
`subst_Phi_eq_Phi_subst` applies to, so that step consumes the already-proved base fact
directly rather than after a commutation.

## Main results

* `coeff_one_subst` : the linear coefficient of a composite is the product of the linear
  coefficients (any commutative ring, inner series with zero constant term).
* `iter` : the `n`-fold iterate, with `iter_zero`, `iter_succ`, `iter_succ'`,
  `constantCoeff_iter`, `hasSubst_iter`.
* `iter_add` : `f^{(m + n)} = f^{(m)} ∘ f^{(n)}` — the filtration fact underlying
  `F_π[π^n] ⊆ F_π[π^(m+n)]`.
* `coeff_one_iter` : `coeff 1 (f^{(n)}) = π ^ n`.
* `map_residue_iter` : `f^{(n)} ≡ X ^ (q ^ n) (mod 𝔪)`.
* `isLubinTatePoly_iter` : **`IsLubinTatePoly (π ^ n) (q ^ n) (f^{(n)})`** — the correct analogue
  of the original predicate. Note this is *not* `IsLubinTatePoly π q (f^{(n)})`: the linear
  coefficient of an `n`-fold composite is `π ^ n`, not `π`, and the mod-`𝔪` reduction is
  `X ^ (q ^ n)`, not `X ^ q`. Both defining congruences of `LubinTate.IsLubinTatePoly` survive
  verbatim under this substitution of parameters — `IsLubinTatePoly` itself imposes no
  irreducibility or primality condition on its `π`/`q` arguments, so `π ^ n` and `q ^ n` are
  legitimate arguments even though `π ^ n` is not a uniformizer for `n ≥ 2`.
* `subst_iter_Phi` : **`f^{(n)}` is an endomorphism of `F_π`** —
  `(iter f n).subst Φ = Φ.subst (fun i ↦ (iter f n).subst (X i))`, i.e.
  `f^{(n)}(F_π(X, Y)) = F_π(f^{(n)}(X), f^{(n)}(Y))`, by induction from
  `subst_Phi_eq_Phi_subst`.
-/

@[expose] public section

noncomputable section

open PowerSeries IsLocalRing

/-- **Substituting the identity family into a multivariate power series is the identity.**
The multivariate analogue of Mathlib's `PowerSeries.X_subst`, proved the same way (via
`MvPowerSeries.map_algebraMap_eq_subst_X` with `S := R`). -/
@[simp] theorem MvPowerSeries.X_subst {σ R : Type*} [CommRing R] (F : MvPowerSeries σ R) :
    MvPowerSeries.subst MvPowerSeries.X F = F := by
  rw [← MvPowerSeries.map_algebraMap_eq_subst_X (S := R), Algebra.algebraMap_self]
  exact DFunLike.congr_fun MvPowerSeries.map_id F

namespace LubinTate

section General

variable {S : Type*} [CommRing S]

/-- **The linear coefficient of a composite is the product of the linear coefficients.**
For `b` with zero constant term, `coeff 1 (g ∘ b) = coeff 1 g * coeff 1 b`: in
`PowerSeries.coeff_subst'`'s expansion `∑ᶠ d, coeff d g • coeff 1 (b ^ d)` only `d = 1` survives —
`d = 0` because `coeff 1 (1 : S⟦X⟧) = 0`, and `d ≥ 2` because `b ^ d` has order at least `d > 1`
(`PowerSeries.le_order_pow_of_constantCoeff_eq_zero`). -/
theorem coeff_one_subst {b : S⟦X⟧} (hb0 : PowerSeries.coeff 0 b = 0) (g : S⟦X⟧) :
    PowerSeries.coeff 1 (g.subst b) = PowerSeries.coeff 1 g * PowerSeries.coeff 1 b := by
  have hconst : PowerSeries.constantCoeff b = 0 := by
    rwa [← PowerSeries.coeff_zero_eq_constantCoeff]
  have hbs : PowerSeries.HasSubst b := PowerSeries.HasSubst.of_constantCoeff_zero' hconst
  rw [PowerSeries.coeff_subst' hbs, finsum_eq_single _ 1]
  · simp
  · intro d hd
    match d, hd with
    | 0, _ => simp
    | 1, hd => exact absurd rfl hd
    | (d + 2), _ =>
      have horder : ((d + 2 : ℕ) : ℕ∞) ≤ (b ^ (d + 2)).order :=
        PowerSeries.le_order_pow_of_constantCoeff_eq_zero _ hconst
      have h1 : (1 : ℕ∞) < (b ^ (d + 2)).order :=
        lt_of_lt_of_le (by exact_mod_cast (show 1 < d + 2 by omega)) horder
      rw [PowerSeries.coeff_of_lt_order 1 h1, smul_zero]

/-- **The `n`-fold iterate `f^{(n)}`** of a power series with zero constant term:
`f^{(0)} = X`, `f^{(n+1)} = f ∘ f^{(n)}`. (The definition itself makes sense for any `f`; the
composition is only the intended one when `f` has zero constant term, which is where every lemma
below assumes it.) -/
noncomputable def iter (f : S⟦X⟧) : ℕ → S⟦X⟧
  | 0 => PowerSeries.X
  | n + 1 => f.subst (iter f n)

@[simp] theorem iter_zero (f : S⟦X⟧) : iter f 0 = (PowerSeries.X : S⟦X⟧) := rfl

theorem iter_succ (f : S⟦X⟧) (n : ℕ) : iter f (n + 1) = f.subst (iter f n) := rfl

theorem constantCoeff_iter {f : S⟦X⟧} (hf0 : PowerSeries.constantCoeff f = 0) :
    ∀ n, PowerSeries.constantCoeff (iter f n) = 0
  | 0 => by simp
  | n + 1 => by
      rw [iter_succ]
      exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_iter hf0 n) f hf0

theorem hasSubst_iter {f : S⟦X⟧} (hf0 : PowerSeries.constantCoeff f = 0) (n : ℕ) :
    PowerSeries.HasSubst (iter f n) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_iter hf0 n)

/-- **The two composition conventions agree**: `f ∘ f^{(n)} = f^{(n)} ∘ f`. Induction on `n`, using
`PowerSeries.subst_comp_subst_apply` at the step and `PowerSeries.X_subst`/`PowerSeries.subst_X` at
the base.

Written in the prefix form `PowerSeries.subst a g` rather than `g.subst a` throughout, for the
reason `Langlands/PowerSeriesExpLog.lean`'s `eq_substInv_of_subst_eq_X` already documents: with
both substitutand and substituted series univariate, nested dot notation elaborates against
`MvPowerSeries.subst` (whose namespace also matches `R⟦X⟧`'s reducible head), and the resulting
unification diverges rather than failing cleanly. -/
theorem iter_succ' {f : S⟦X⟧} (hf0 : PowerSeries.constantCoeff f = 0) (n : ℕ) :
    iter f (n + 1) = PowerSeries.subst f (iter f n) := by
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  induction n with
  | zero => rw [iter_succ, iter_zero, PowerSeries.X_subst, PowerSeries.subst_X hfs]
  | succ n ih =>
      have hcomp : PowerSeries.subst f (PowerSeries.subst (iter f n) f)
          = PowerSeries.subst (PowerSeries.subst f (iter f n)) f :=
        PowerSeries.subst_comp_subst_apply (hasSubst_iter hf0 n) hfs f
      calc iter f (n + 1 + 1)
          = PowerSeries.subst (iter f (n + 1)) f := iter_succ f (n + 1)
        _ = PowerSeries.subst (PowerSeries.subst f (iter f n)) f := by rw [ih]
        _ = PowerSeries.subst f (PowerSeries.subst (iter f n) f) := hcomp.symm
        _ = PowerSeries.subst f (iter f (n + 1)) := by rw [iter_succ]

/-- **Iterates compose additively**: `f^{(m + n)} = f^{(m)} ∘ f^{(n)}`. Induction on `m`, from
`PowerSeries.subst_comp_subst_apply`; the base case is `PowerSeries.subst_X`. This is the
filtration fact the `π^n`-torsion tower rests on — once evaluation at a concrete element is
available, `f^{(n)}(x) = 0` immediately gives `f^{(m + n)}(x) = f^{(m)}(0) = 0`, i.e. the
`π^n`-torsion sits inside the `π^(m+n)`-torsion. Written in prefix `PowerSeries.subst` form for
the reason recorded at `iter_succ'`. -/
theorem iter_add {f : S⟦X⟧} (hf0 : PowerSeries.constantCoeff f = 0) (n : ℕ) :
    ∀ m, iter f (m + n) = PowerSeries.subst (iter f n) (iter f m) := by
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  intro m
  induction m with
  | zero => rw [Nat.zero_add, iter_zero, PowerSeries.subst_X (hasSubst_iter hf0 n)]
  | succ m ih =>
      have hidx : m + 1 + n = m + n + 1 := by omega
      have hcomp : PowerSeries.subst (iter f n) (PowerSeries.subst (iter f m) f)
          = PowerSeries.subst (PowerSeries.subst (iter f n) (iter f m)) f :=
        PowerSeries.subst_comp_subst_apply (hasSubst_iter hf0 m) (hasSubst_iter hf0 n) f
      calc iter f (m + 1 + n)
          = iter f (m + n + 1) := by rw [hidx]
        _ = PowerSeries.subst (iter f (m + n)) f := iter_succ f (m + n)
        _ = PowerSeries.subst (PowerSeries.subst (iter f n) (iter f m)) f := by rw [ih]
        _ = PowerSeries.subst (iter f n) (PowerSeries.subst (iter f m) f) := hcomp.symm
        _ = PowerSeries.subst (iter f n) (iter f (m + 1)) := by rw [iter_succ]

/-- The linear coefficient of the `n`-fold iterate is `π ^ n`. -/
theorem coeff_one_iter {f : S⟦X⟧} {π : S} (hf0 : PowerSeries.coeff 0 f = 0)
    (hf1 : PowerSeries.coeff 1 f = π) : ∀ n, PowerSeries.coeff 1 (iter f n) = π ^ n
  | 0 => by simp
  | n + 1 => by
      have hconst : PowerSeries.constantCoeff f = 0 := by
        rwa [← PowerSeries.coeff_zero_eq_constantCoeff]
      have h0 : PowerSeries.coeff 0 (iter f n) = 0 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact constantCoeff_iter hconst n
      rw [iter_succ, coeff_one_subst h0 f, hf1, coeff_one_iter hf0 hf1 n]
      ring

end General

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

variable {π : O} {f : O⟦X⟧}

/-- Reducing the `n`-fold iterate mod `𝔪` gives exactly `X ^ (q ^ n)`: `PowerSeries.map_subst`
turns the reduction of a composite into the composite of the reductions, the inductive hypothesis
and `f`'s own congruence identify those as `X ^ q` and `X ^ (q ^ n)`, and
`PowerSeries.subst_pow`/`PowerSeries.subst_X` evaluate `(X ^ q) ∘ (X ^ (q ^ n)) =
(X ^ (q ^ n)) ^ q = X ^ (q ^ (n + 1))`. -/
theorem map_residue_iter (hf : IsLubinTatePoly π (residueCard O) f) :
    ∀ n, PowerSeries.map (residue O) (iter f n)
      = (PowerSeries.X : (ResidueField O)⟦X⟧) ^ (residueCard O ^ n)
  | 0 => by simp
  | n + 1 => by
      have hconst : PowerSeries.constantCoeff f = 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hf.1
      have hq2 : 2 ≤ residueCard O := two_le_residueCard
      have hqn : residueCard O ^ n ≠ 0 := by positivity
      have key : PowerSeries.map (residue O) (f.subst (iter f n))
          = (PowerSeries.map (residue O) f).subst
              (PowerSeries.map (residue O) (iter f n)) :=
        PowerSeries.map_subst (hasSubst_iter hconst n) f
      rw [iter_succ, key, hf.2.2,
        map_residue_iter hf n,
        PowerSeries.subst_pow (PowerSeries.HasSubst.X_pow hqn) _ _,
        PowerSeries.subst_X (PowerSeries.HasSubst.X_pow hqn), ← pow_mul, ← pow_succ]

/-- **The correct analogue of `IsLubinTatePoly` for the `n`-fold iterate.** `f^{(n)}` satisfies
the two Lubin-Tate defining congruences with parameters `π ^ n` and `q ^ n` in place of `π` and
`q`: zero constant term, linear coefficient exactly `π ^ n`, and mod-`𝔪` reduction exactly
`X ^ (q ^ n)`. This is *the* statement to carry downstream — `f^{(n)}` is the `[π^n]`
endomorphism, not another `[π]`. -/
theorem isLubinTatePoly_iter (hf : IsLubinTatePoly π (residueCard O) f) (n : ℕ) :
    IsLubinTatePoly (π ^ n) (residueCard O ^ n) (iter f n) := by
  have hconst : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hf.1
  refine ⟨?_, coeff_one_iter hf.1 hf.2.1 n, map_residue_iter hf n⟩
  rw [PowerSeries.coeff_zero_eq_constantCoeff]
  exact constantCoeff_iter hconst n

/-- **`f^{(n)}` is an endomorphism of the Lubin-Tate formal group law `F_π`**:
`f^{(n)}(F_π(X, Y)) = F_π(f^{(n)}(X), f^{(n)}(Y))`. This is the `[π^n]`-multiplication
endomorphism whose kernel is the `π^n`-torsion of `F_π`.

Induction on `n`. The base case is `MvPowerSeries.X_subst` after `PowerSeries.subst_X` rewrites
each `X ∘ X i` to `X i`. The step chains: `PowerSeries.subst_comp_subst_apply` peels the outer `f`
off `f^{(n+1)} ∘ Φ`; the inductive hypothesis rewrites the inner `f^{(n)} ∘ Φ`;
`subst_subst_mv` (from `Langlands/LubinTateFunctionalEquationBivariate.lean`) moves the outer `f`
back across the multivariate substitution; `subst_Phi_eq_Phi_subst` applies to the resulting
`f ∘ Φ`; `MvPowerSeries.subst_comp_subst_apply` merges the two multivariate substitutions; and
each merged component `(f ∘ X i) ∘ (f^{(n)} ∘ X)` collapses back to `f^{(n+1)} ∘ X i`. -/
theorem subst_iter_Phi (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) :
    ∀ n, (iter f n).subst (Phi hπ hf) =
      (Phi hπ hf).subst (fun i ↦ (iter f n).subst (MvPowerSeries.X i))
  | 0 => by
      have hΦ : PowerSeries.HasSubst (Phi hπ hf) :=
        PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_Phi hπ hf)
      have hfam : (fun i : Fin 2 ↦ (PowerSeries.X : O⟦X⟧).subst (MvPowerSeries.X i))
          = (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) O) :=
        funext fun i ↦ PowerSeries.subst_X (PowerSeries.HasSubst.X i)
      rw [iter_zero, PowerSeries.subst_X hΦ, hfam, MvPowerSeries.X_subst]
  | n + 1 => by
      have hconst : PowerSeries.constantCoeff f = 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hf.1
      have hΦ : PowerSeries.HasSubst (Phi hπ hf) :=
        PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_Phi hπ hf)
      have ha₁ : MvPowerSeries.HasSubst
          (fun i : Fin 2 ↦ f.subst (MvPowerSeries.X i) : Fin 2 → MvPowerSeries (Fin 2) O) :=
        MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦
          PowerSeries.constantCoeff_subst_eq_zero (by simp) f hconst
      have haₙ : MvPowerSeries.HasSubst
          (fun i : Fin 2 ↦ (iter f n).subst (MvPowerSeries.X i) :
            Fin 2 → MvPowerSeries (Fin 2) O) :=
        MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦
          PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (constantCoeff_iter hconst n)
      calc (iter f (n + 1)).subst (Phi hπ hf)
          = f.subst ((iter f n).subst (Phi hπ hf)) := by
            rw [iter_succ, PowerSeries.subst_comp_subst_apply (hasSubst_iter hconst n) hΦ f]
        _ = f.subst (MvPowerSeries.subst
              (fun i ↦ (iter f n).subst (MvPowerSeries.X i)) (Phi hπ hf)) := by
            rw [subst_iter_Phi hπ hf n]
        _ = MvPowerSeries.subst (fun i ↦ (iter f n).subst (MvPowerSeries.X i))
              (f.subst (Phi hπ hf)) :=
            (subst_subst_mv f hΦ haₙ).symm
        _ = MvPowerSeries.subst (fun i ↦ (iter f n).subst (MvPowerSeries.X i))
              (MvPowerSeries.subst (fun i ↦ f.subst (MvPowerSeries.X i)) (Phi hπ hf)) := by
            rw [subst_Phi_eq_Phi_subst hπ hf]
        _ = MvPowerSeries.subst
              (fun i ↦ MvPowerSeries.subst (fun j ↦ (iter f n).subst (MvPowerSeries.X j))
                (f.subst (MvPowerSeries.X i))) (Phi hπ hf) :=
            MvPowerSeries.subst_comp_subst_apply ha₁ haₙ _
        _ = (Phi hπ hf).subst (fun i ↦ (iter f (n + 1)).subst (MvPowerSeries.X i)) := by
            refine congrArg (fun c ↦ MvPowerSeries.subst c (Phi hπ hf)) (funext fun i ↦ ?_)
            rw [subst_subst_mv f (PowerSeries.HasSubst.X i) haₙ]
            simp only [MvPowerSeries.subst_X haₙ i]
            rw [iter_succ, PowerSeries.subst_comp_subst_apply (hasSubst_iter hconst n)
              (PowerSeries.HasSubst.X i) f]

end LubinTate

end

end
