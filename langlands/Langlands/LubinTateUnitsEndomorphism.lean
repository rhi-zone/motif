import Langlands.LubinTateFunctionalEquationBivariate

/-!
# The units endomorphism `[u]_F` of `F_π`, for `u ∈ Oˣ`

`ROADMAP.md` §27's pointer-forward names `Gal(K_n/K) ↪ (O/π^n)ˣ` as the eventual target of the
Lubin-Tate tower. The `Oˣ`-action on the tower ultimately comes from evaluating, for each
`u ∈ Oˣ`, the power series `[u]_F` that is *the* endomorphism of `F_π` with linear coefficient
`u` — this file constructs `[u]_F` and proves it commutes with `F_π`'s formal group law, at the
level of formal power series (no evaluation yet).

## Route

`Langlands.LubinTateFunctionalEquation.phiState`/`phiCoeff` (`ROADMAP.md` §8–§10) already builds,
for *any* `f, g ∈ ℱ_π` and *any* linear starting coefficient `a : O`, the unique power series
intertwining `f` and `g` with that linear coefficient. Specializing `g := f` and `a := (u : O)`
for `u : Oˣ` gives `phiU hπ hf u := PowerSeries.mk (phiCoeff hπ (u : O) hf hf)`, satisfying
`f.subst (phiU hπ hf u) = (phiU hπ hf u).subst f` (`subst_phiU_eq_phiU_subst`) unconditionally —
the univariate functional equation lemma's linear coefficient was already fully general, not
specialized to `1`.

**`[u]_F` is `phiU hπ hf u` viewed as an endomorphism of `Φ := Phi hπ hf`**: the claim is
`Φ.subst (fun i ↦ (phiU hπ hf u).subst (X i)) = (phiU hπ hf u).subst Φ`, i.e. `Φ(u·X, u·Y) =
u·Φ(X, Y)` order-by-order (`u` acting diagonally on the left, then substituted into `Φ`, versus
`Φ` substituted into `u`'s power series). Both sides are elements of `MvPowerSeries (Fin 2) O`
with zero constant term and linear part `u·X + u·Y`; `Langlands.LubinTateFunctionalEquationBivariate.
eq_of_subst_eq_mv` identifies any two such series once each is shown to solve the bivariate
functional equation `f.subst Ψ = Ψ.subst (fun i ↦ f.subst (X i))` — its `hlin` hypothesis only
asks the two candidates' linear coefficients to match *each other*, not to be literally `1`, so it
applies here with `u` in place of `1`.

Each side solving the functional equation needs a composition-closure fact in a shape not yet in
the repo:

* `solvesFunctionalEq_subst_embed` : if a univariate `h` solves `f.subst h = h.subst f`, then
  `h.subst (X i)` (`h` embedded along one axis of a multivariate index type) solves the
  multivariate-embedded functional equation. The general-`h` version of
  `Langlands.LubinTateFunctionalEquationBivariate.solvesFunctionalEq_X` (the `h = X` case).
  Combined with `Langlands.LubinTateFunctionalEquationBivariate.solvesFunctionalEq_subst`
  (multivariate-outer, family-inner closure), this handles the left side
  `Φ.subst (fun i ↦ (phiU hπ hf u).subst (X i))`.
* `solvesFunctionalEq_subst_outer` : if a univariate `h` solves `f.subst h = h.subst f` and a
  multivariate `Ψ` solves the multivariate functional equation, then `h.subst Ψ` (univariate `h`
  substituted with the multivariate `Ψ`) again solves the multivariate functional equation. This
  is the composition order `solvesFunctionalEq_subst` does *not* cover (that one is multivariate
  outer, family inner; this one is univariate outer, multivariate inner) — it handles the right
  side `(phiU hπ hf u).subst Φ`.

Both closure facts are proved the same way: unfold to `PowerSeries.subst_comp_subst_apply`
(univariate/univariate-into-multivariate reassociation) and
`Langlands.LubinTateFunctionalEquationBivariate.subst_subst_mv` (univariate-outer,
multivariate-inner-then-family reassociation), chaining through the hypothesis that `h` solves its
own equation — no new coefficient recursion, purely substitution algebra.

## Main results

* `phiU`, `constantCoeff_phiU`, `coeff_one_phiU` : `[u]_F`'s underlying univariate power series and
  its two base coefficients (`0`, `u`).
* `subst_phiU_eq_phiU_subst` : `phiU` intertwines `f` with itself (the univariate functional
  equation, specialized).
* `solvesFunctionalEq_subst_embed`, `solvesFunctionalEq_subst_outer` : the two new
  composition-closure facts described above.
* `subst_Phi_phiU_eq_phiU_subst_Phi` : **`[u]_F` is a genuine endomorphism of the formal group law
  `F_π`**: `Φ.subst (fun i ↦ (phiU hπ hf u).subst (X i)) = (phiU hπ hf u).subst Φ`.

## What this does not do

No evaluation at concrete torsion points, and no group structure on `Oˣ` acting on `piTorsion` —
see `ROADMAP.md`'s entry for this pass for the precise state of that next step.
-/

@[expose] public section

noncomputable section

namespace LubinTate

open IsLocalRing PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {π : O} {f : O⟦X⟧}

/-! ### The two composition-closure facts -/

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- **Two univariate substitutions compose the same way when the second one lands in a
multivariate ring**: `(w.subst a).subst b = w.subst (a.subst b)` for `w : PowerSeries R`,
`a : PowerSeries S` (univariate) and `b : MvPowerSeries υ T` (possibly multivariate). This is
`PowerSeries.subst_comp_subst_apply`'s statement, reproved directly through
`PowerSeries.subst_def`/`MvPowerSeries.subst_comp_subst_apply`: Mathlib's own version carries an
extra base-ring implicit (from its enclosing section, needed only for its `HasSubst` API, not for
this statement) that is left fully unconstrained by the conclusion, so instance search gets stuck
whenever `b` is genuinely multivariate. -/
theorem subst_subst_univ_mv {R S T υ : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (w : PowerSeries R) {a : PowerSeries S} (ha : PowerSeries.HasSubst a)
    {b : MvPowerSeries υ T} (hb : PowerSeries.HasSubst b) :
    PowerSeries.subst b (PowerSeries.subst a w) = PowerSeries.subst (PowerSeries.subst b a) w := by
  simp only [PowerSeries.subst_def]
  rw [MvPowerSeries.subst_comp_subst_apply ha.const hb.const]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- **A solution of the univariate functional equation, embedded along one axis of a multivariate
index type, solves the embedded functional equation.** The general-`h` version of
`solvesFunctionalEq_X` (which is the special case `h = X`). Proved by unfolding both sides via
`subst_subst_univ_mv` (twice, using `hh` in the middle) and `subst_subst_mv`/`MvPowerSeries.subst_X`
(once), matching the six-step chain `f.subst (h.subst (X i)) = (f.subst h).subst (X i) =
(h.subst f).subst (X i) = h.subst (f.subst (X i)) = h.subst ((X i).subst (fun j ↦ f.subst (X j)))
= (h.subst (X i)).subst (fun j ↦ f.subst (X j))`. -/
theorem solvesFunctionalEq_subst_embed {σ : Type*} [Finite σ]
    (hf0 : PowerSeries.constantCoeff f = 0) {h : PowerSeries O}
    (hh0 : PowerSeries.constantCoeff h = 0) (hh : f.subst h = h.subst f) (i : σ) :
    f.subst (h.subst (MvPowerSeries.X i) : MvPowerSeries σ O) =
      (h.subst (MvPowerSeries.X i) : MvPowerSeries σ O).subst
        (fun j ↦ f.subst (MvPowerSeries.X j)) := by
  have hh' : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  have hf' : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hXi : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ O) :=
    PowerSeries.HasSubst.X i
  have hd0 : ∀ j : σ, MvPowerSeries.constantCoeff
      (f.subst (MvPowerSeries.X j) (S := O) (τ := σ)) = 0 :=
    fun j ↦ PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0
  have hd : MvPowerSeries.HasSubst
      (fun j ↦ f.subst (MvPowerSeries.X j) (S := O) (τ := σ)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hd0
  have step1 : f.subst (h.subst (MvPowerSeries.X i) : MvPowerSeries σ O) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ O) (f.subst h) :=
    (subst_subst_univ_mv f hh' hXi).symm
  have step2 : PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ O) (f.subst h) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ O) (h.subst f) := by rw [hh]
  have step3 : PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ O) (h.subst f) =
      h.subst (f.subst (MvPowerSeries.X i) : MvPowerSeries σ O) :=
    subst_subst_univ_mv h hf' hXi
  have step4 : h.subst (f.subst (MvPowerSeries.X i) : MvPowerSeries σ O) =
      (h.subst (MvPowerSeries.X i) : MvPowerSeries σ O).subst
        (fun j ↦ f.subst (MvPowerSeries.X j)) := by
    have key : MvPowerSeries.subst (fun j ↦ f.subst (MvPowerSeries.X j))
        (h.subst (MvPowerSeries.X i) : MvPowerSeries σ O) =
        h.subst (MvPowerSeries.subst (fun j ↦ f.subst (MvPowerSeries.X j))
          (MvPowerSeries.X i : MvPowerSeries σ O)) :=
      subst_subst_mv h hXi hd
    rw [MvPowerSeries.subst_X hd i] at key
    exact key.symm
  rw [step1, step2, step3, step4]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] in
/-- **A solution of the univariate functional equation, substituted with a solution of the
multivariate functional equation, again solves the multivariate functional equation.** The
composition order `solvesFunctionalEq_subst` does not cover: there, the *multivariate* series `Ψ`
is outer and a *family* is substituted in; here, a *univariate* series `h` is outer and a single
*multivariate* series `Ψ` is substituted in. Proved by the same six-step reassociation chain as
`solvesFunctionalEq_subst_embed`, with `Ψ` in place of `X i` throughout (using `hΨ`, `Ψ`'s own
functional equation, in place of `MvPowerSeries.subst_X`'s coordinate identity). -/
theorem solvesFunctionalEq_subst_outer {σ : Type*} [Finite σ]
    (hf0 : PowerSeries.constantCoeff f = 0) {h : PowerSeries O}
    (hh0 : PowerSeries.constantCoeff h = 0) (hh : f.subst h = h.subst f)
    {Ψ : MvPowerSeries σ O} (hΨ0 : MvPowerSeries.constantCoeff Ψ = 0)
    (hΨ : f.subst Ψ = Ψ.subst (fun i ↦ f.subst (MvPowerSeries.X i))) :
    f.subst (h.subst Ψ) = (h.subst Ψ).subst (fun i ↦ f.subst (MvPowerSeries.X i)) := by
  have hh' : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  have hf' : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hΨ' : PowerSeries.HasSubst Ψ := PowerSeries.HasSubst.of_constantCoeff_zero hΨ0
  have hd0 : ∀ i : σ, MvPowerSeries.constantCoeff
      (f.subst (MvPowerSeries.X i) (S := O) (τ := σ)) = 0 :=
    fun i ↦ PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0
  have hd : MvPowerSeries.HasSubst
      (fun i ↦ f.subst (MvPowerSeries.X i) (S := O) (τ := σ)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hd0
  have step1 : f.subst (h.subst Ψ) = PowerSeries.subst Ψ (f.subst h) :=
    (subst_subst_univ_mv f hh' hΨ').symm
  have step2 : PowerSeries.subst Ψ (f.subst h) = PowerSeries.subst Ψ (h.subst f) := by rw [hh]
  have step3 : PowerSeries.subst Ψ (h.subst f) = h.subst (f.subst Ψ) :=
    subst_subst_univ_mv h hf' hΨ'
  have step4 : h.subst (f.subst Ψ) = h.subst (Ψ.subst (fun i ↦ f.subst (MvPowerSeries.X i))) := by
    rw [hΨ]
  have step5 : h.subst (Ψ.subst (fun i ↦ f.subst (MvPowerSeries.X i))) =
      (h.subst Ψ).subst (fun i ↦ f.subst (MvPowerSeries.X i)) :=
    (subst_subst_mv h hΨ' hd).symm
  rw [step1, step2, step3, step4, step5]

/-! ### `phiU`, the univariate series underlying `[u]_F` -/

variable {u : Oˣ}

/-- **`[u]_F`'s underlying univariate power series**: the functional equation lemma's
intertwining series for `f` with itself, with linear coefficient `u`. -/
def phiU (hπ : Irreducible π) (hf : IsLubinTatePoly π (residueCard O) f) (u : Oˣ) : O⟦X⟧ :=
  PowerSeries.mk (phiCoeff hπ (u : O) hf hf)

@[simp] theorem constantCoeff_phiU (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (u : Oˣ) :
    PowerSeries.constantCoeff (phiU hπ hf u) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, phiU, PowerSeries.coeff_mk, phiCoeff_zero]

@[simp] theorem coeff_one_phiU (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (u : Oˣ) :
    PowerSeries.coeff 1 (phiU hπ hf u) = (u : O) := by
  rw [phiU, PowerSeries.coeff_mk, phiCoeff_one]

/-- **`phiU` intertwines `f` with itself**: the univariate functional equation lemma's existence
half (`subst_phi_eq_phi_subst`), specialized to `g := f`, `a := (u : O)`. -/
theorem subst_phiU_eq_phiU_subst (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (u : Oˣ) :
    f.subst (phiU hπ hf u) = (phiU hπ hf u).subst f :=
  subst_phi_eq_phi_subst hπ (u : O) hf hf

/-! ### `[u]_F` is an endomorphism of `F_π` -/

/-- **`phiU hπ hf u` embedded along one axis of `Φ`'s two variables solves the bivariate functional
equation.** The family `c i := (phiU hπ hf u).subst (X i)` used to build the left side of
`subst_Phi_phiU_eq_phiU_subst_Phi`. -/
theorem constantCoeff_phiU_subst_X (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (u : Oˣ) (i : Fin 2) :
    MvPowerSeries.constantCoeff
      ((phiU hπ hf u).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) O)) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) (phiU hπ hf u) (constantCoeff_phiU hπ hf u)

/-- **`[u]_F` is a genuine endomorphism of the Lubin-Tate formal group law `F_π`**: `Φ(u·X, u·Y) =
u·Φ(X, Y)`, i.e. embedding `phiU hπ hf u` along each of `Φ`'s two variables and substituting into
`Φ` gives the same series as substituting `Φ` into `phiU hπ hf u` directly. Both sides solve the
bivariate functional equation (`solvesFunctionalEq_subst` + `solvesFunctionalEq_subst_embed` for
the left side, `solvesFunctionalEq_subst_outer` for the right side) and agree in total degree `1`
(both have every degree-`1` coefficient equal to `(u : O)`), so `eq_of_subst_eq_mv` identifies
them. -/
theorem subst_Phi_phiU_eq_phiU_subst_Phi (hπ : Irreducible π)
    (hf : IsLubinTatePoly π (residueCard O) f) (u : Oˣ) :
    (Phi hπ hf).subst (fun i ↦ (phiU hπ hf u).subst (MvPowerSeries.X i)) =
      (phiU hπ hf u).subst (Phi hπ hf) := by
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hf.1
  have hφu0 : PowerSeries.constantCoeff (phiU hπ hf u) = 0 := constantCoeff_phiU hπ hf u
  have hφueq : f.subst (phiU hπ hf u) = (phiU hπ hf u).subst f := subst_phiU_eq_phiU_subst hπ hf u
  have hΦ0 : MvPowerSeries.constantCoeff (Phi hπ hf) = 0 := constantCoeff_Phi hπ hf
  have hΦeq : f.subst (Phi hπ hf) =
      (Phi hπ hf).subst (fun i ↦ f.subst (MvPowerSeries.X i)) := subst_Phi_eq_Phi_subst hπ hf
  set c : Fin 2 → MvPowerSeries (Fin 2) O := fun i ↦ (phiU hπ hf u).subst (MvPowerSeries.X i)
    with hcdef
  have hc0 : ∀ i, MvPowerSeries.constantCoeff (c i) = 0 :=
    fun i ↦ constantCoeff_phiU_subst_X hπ hf u i
  have hc : MvPowerSeries.HasSubst c := MvPowerSeries.hasSubst_of_constantCoeff_zero hc0
  have hcsolve : ∀ i, f.subst (c i) = (c i).subst (fun j ↦ f.subst (MvPowerSeries.X j)) :=
    fun i ↦ solvesFunctionalEq_subst_embed hf0 hφu0 hφueq i
  have hΨAeq : f.subst ((Phi hπ hf).subst c) =
      ((Phi hπ hf).subst c).subst (fun j ↦ f.subst (MvPowerSeries.X j)) :=
    solvesFunctionalEq_subst hf0 hΦ0 hΦeq hc hcsolve
  have hΨBeq : f.subst ((phiU hπ hf u).subst (Phi hπ hf)) =
      ((phiU hπ hf u).subst (Phi hπ hf)).subst (fun j ↦ f.subst (MvPowerSeries.X j)) :=
    solvesFunctionalEq_subst_outer hf0 hφu0 hφueq hΦ0 hΦeq
  have hΨA0 : MvPowerSeries.constantCoeff ((Phi hπ hf).subst c) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hc hc0 hΦ0
  have hΨB0 : MvPowerSeries.constantCoeff ((phiU hπ hf u).subst (Phi hπ hf)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hΦ0 (phiU hπ hf u) hφu0
  have hΦ' : PowerSeries.HasSubst (Phi hπ hf) := PowerSeries.HasSubst.of_constantCoeff_zero hΦ0
  have hφu' : PowerSeries.HasSubst (phiU hπ hf u) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hφu0
  have hlin : ∀ m : Fin 2 →₀ ℕ, m.degree = 1 →
      MvPowerSeries.coeff m ((Phi hπ hf).subst c) =
        MvPowerSeries.coeff m ((phiU hπ hf u).subst (Phi hπ hf)) := by
    intro m hm
    have hnd : m.degree ≤ 1 := le_of_eq hm
    have hdeg : m 0 + m 1 = 1 := by rw [← degree_fin_two]; exact hm
    -- right side: (phiU hπ hf u).subst Φ, via truncation invariance (inner position)
    have hR : MvPowerSeries.coeff m ((phiU hπ hf u).subst (Phi hπ hf)) = (u : O) := by
      rw [coeff_subst_eq_of_coeff_eq_mv (phiU hπ hf u) hΦ'
          (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_PhiPartialSum hπ hf 1))
          (fun j hj ↦ coeff_Phi_eq_coeff_PhiPartialSum hπ hf 1 j hj) hnd,
        PhiPartialSum_one, PowerSeries.coeff_subst_X_zero_add_X_one, hdeg, coeff_one_phiU]
      rcases Nat.eq_zero_or_pos (m 0) with h0 | h0
      · simp [h0]
      · have h0' : m 0 = 1 := by omega
        simp [h0']
    -- left side: Φ.subst c, via truncation invariance (outer position)
    have hL : MvPowerSeries.coeff m ((Phi hπ hf).subst c) = (u : O) := by
      rw [coeff_subst_eq_of_coeff_eq_outer_mv hc hc0
          (fun j hj ↦ coeff_Phi_eq_coeff_PhiPartialSum hπ hf 1 j hj) hnd,
        PhiPartialSum_one, MvPowerSeries.subst_add hc, MvPowerSeries.subst_X hc,
        MvPowerSeries.subst_X hc, map_add]
      show MvPowerSeries.coeff m (c 0) + MvPowerSeries.coeff m (c 1) = _
      rw [hcdef]
      show MvPowerSeries.coeff m ((phiU hπ hf u).subst (MvPowerSeries.X 0)) +
        MvPowerSeries.coeff m ((phiU hπ hf u).subst (MvPowerSeries.X 1)) = _
      rw [PowerSeries.coeff_subst_single, PowerSeries.coeff_subst_single]
      rcases Nat.eq_zero_or_pos (m 0) with h0 | h0
      · have h1 : m 1 = 1 := by omega
        have hns : m = Finsupp.single 1 1 := finsupp_fin_two_ext (by simp [h0]) (by simp [h1])
        rw [if_neg (by rw [hns]; exact finsupp_fin_two_ne 1 (by simp)),
          if_pos (by rw [hns]; simp), h1, coeff_one_phiU]
        simp
      · have h0' : m 0 = 1 := by omega
        have h1 : m 1 = 0 := by omega
        have hns : m = Finsupp.single 0 1 := finsupp_fin_two_ext (by simp [h0']) (by simp [h1])
        rw [if_pos (by rw [hns]; simp),
          if_neg (by rw [hns]; exact finsupp_fin_two_ne 0 (by simp)),
          h0', coeff_one_phiU]
        simp
    rw [hL, hR]
  exact eq_of_subst_eq_mv hπ hf hΨA0 hΨB0 hlin hΨAeq hΨBeq

end LubinTate

end
