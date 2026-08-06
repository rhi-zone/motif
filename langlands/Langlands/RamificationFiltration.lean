import Langlands.SimpleRootRigidity
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Higher ramification groups in lower numbering

This file extends `Mathlib.RingTheory.Valuation.RamificationGroup` with the higher ramification
groups in lower numbering, closing that file's own stated `TODO`.

For `K L : Type*` fields, `[Algebra K L]`, and `A : ValuationSubring L`, `Mathlib` already
supplies:

* `A.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)`, the stabilizer of `A`;
* the `MulSemiringAction (A.decompositionSubgroup K) A` induced on `A` itself;
* `A.inertiaSubgroup K : Subgroup (A.decompositionSubgroup K)`, the kernel of the action on the
  residue field of `A`.

## Indexing convention

Serre (*Local Fields*, Ch. IV) numbers the ramification filtration `G_{-1} ⊇ G_0 ⊇ G_1 ⊇ ⋯` with
`G_{-1} = D` (the decomposition group) and `G_0 = I` (the inertia group). Since `D` and `I` already
exist here as `A.decompositionSubgroup K` and `A.inertiaSubgroup K` and don't need to be redefined,
`ramificationGroup K A i` below is index-shifted by one relative to Serre: it defines Serre's `G_i`
for `i : ℕ` starting at `i = 0`, i.e. `ramificationGroup K A i` *is* Serre's `G_i`, and there is no
`ramificationGroup K A (-1)` — that role is played by `A.decompositionSubgroup K` itself (`⊤` as a
subgroup of itself), not by a new definition. So the correspondence is:

* Serre's `G_{-1} = D` ↦ `A.decompositionSubgroup K` (no new object).
* Serre's `G_0 = I` ↦ `A.inertiaSubgroup K`, proved equal to `ramificationGroup K A 0` below
  (`ValuationSubring.ramificationGroup_zero`).
* Serre's `G_i` for `i ≥ 1` ↦ `ramificationGroup K A i`.

## Main definitions

* `ValuationSubring.ramificationGroup` : the `i`-th ramification group in lower numbering,
  `σ ∈ ramificationGroup K A i ↔ ∀ x : A, σ • x - x ∈ 𝔪_A ^ (i + 1)`.

## Main results

* `ValuationSubring.ramificationGroup_succ_le` : the filtration is decreasing,
  `ramificationGroup K A (i + 1) ≤ ramificationGroup K A i`.
* `ValuationSubring.ramificationGroup_zero` : `ramificationGroup K A 0 = A.inertiaSubgroup K`,
  matching Serre's `G_0 = I`.
* `ValuationSubring.ramificationGroup_normal` : `ramificationGroup K A i` is a normal subgroup of
  the *full* decomposition group `A.decompositionSubgroup K`, not merely of the inertia subgroup.
* `ValuationSubring.smul_eq_of_isRoot_of_mem_ramificationGroup_zero` : an element of `G_0` fixes
  *exactly* (not merely modulo `𝔪_A`) any simple root, in `A`, of a polynomial over a base ring it
  fixes pointwise.
* `ValuationSubring.mem_ramificationGroup_succ_of_adjoin` : the `⊆` direction of the kernel
  computation, from a two-element generating set `{x, π}` of `A` over such a base ring.

## Scope

**Associated-graded embeddings, attempted and blocked (2026-08-05).** The classical structure
theory of the filtration attaches to a uniformizer `π` of `A` (`hπ : IsLocalRing.maximalIdeal A =
Ideal.span {π}`) two maps: `σ ↦ σ(π)/π mod 𝔪_A` (a homomorphism `ramificationGroup K A 0 →*
(ResidueField A)ˣ`, since `σ(π)` and `π` generate the same ideal `𝔪_A` — this part goes through
cleanly, with no error term, using only that ring automorphisms preserve `𝔪_A` setwise
(`smul_mem_pow_maximalIdeal` above) and that ideal generators of a principal ideal are associates
(`Ideal.span_singleton_eq_span_singleton`, needs `A` a domain, which it is as a subring of a
field), and `σ` acts trivially on the residue field for `σ ∈ ramificationGroup K A 0 =
A.inertiaSubgroup K`), and for `i ≥ 1`, `σ ↦ (σ(π) - π)/π mod 𝔪_A^{i+1}` (additive, valued in
`𝔪_A^i / 𝔪_A^{i+1} ≅ ResidueField A`).

Both maps are well-defined as functions on `ramificationGroup K A i` (the `i + 1`-power membership
needed for well-definedness is exactly the defining property of `ramificationGroup K A i` tested at
`x = π`), and a direct computation (tracked in this session, not committed as Lean since it
motivated the search below rather than completing it) confirms the **homomorphism property holds**:
for `σ, τ ∈ ramificationGroup K A i` (`i ≥ 1`), writing `σ(π) - π = π^{i+1} c_σ`, the identity
`(στ)(π) - π = π^{i+1}(c_σ + σ(c_τ)) + d·σ(c_τ)` with `d = σ(π)^{i+1} - π^{i+1} - (i+1)π^{2i}(σ(π)
- π)`-type remainder lying in `𝔪_A^{2i+1} ⊆ 𝔪_A^{i+2}` for `i ≥ 1` (using `x = π^i c_σ ∈ 𝔪_A^i` and
that `(1+x)^{i+1} - 1 - (i+1)x` is divisible by `x^2`, a generic commutative-ring identity provable
by induction) gives `c_{στ} ≡ c_σ + σ(c_τ) mod 𝔪_A`, and `σ(c_τ) ≡ c_τ mod 𝔪_A` since `σ ∈
ramificationGroup K A i ≤ ramificationGroup K A 0 = A.inertiaSubgroup K` acts trivially on the
residue field — so the composite class is additive.

**The wall was the *kernel* direction, not the homomorphism property; it is now closed
(2026-08-06).** The task is to show the kernel of the restriction of this map to
`ramificationGroup K A i` is *exactly* `ramificationGroup K A (i + 1)`. The `⊇` inclusion is
immediate (test the `∀ x` defining property of `G_{i+1}` at `x = π`). The `⊆` inclusion needs the
converse: `σ(π) - π ∈ 𝔪_A^{i+2}` (a condition tested only at the single point `π`) must imply
`σ(x) - x ∈ 𝔪_A^{i+2}` for *every* `x : A` (Serre, *Local Fields*, Ch. IV, the equivalence between
his `i_G(σ) = v_L(σ(π_L) - π_L)`-based definition and the "acts trivially on `O_L / 𝔪_L^{i+1}`"
definition used by this file's `ramificationGroup`).

Classically this step goes through monogenicity of `O_L` over `O_{L_0}` for `L_0` the maximal
unramified subextension, by an Eisenstein-polynomial argument. That route was blocked for a
concrete reason recorded across `ROADMAP.md`'s Phase 2b passes twelve to thirty-four: this repo can
only build `L_0` inside an *auxiliary* algebraically closed field, never as a subfield of the
already-fixed `L`. The two lemmas at the end of this file take a different route, which does not
need `L_0`, a single generator, an Eisenstein polynomial, or the ramification index:

* `smul_eq_of_isRoot_of_mem_ramificationGroup_zero` — an element of `G_0` fixes a *simple* root
  `x : A` of a polynomial over a pointwise-fixed base ring `R₀` exactly, because simple roots are
  rigid (`IsLocalRing.eq_of_isRoot_of_residue_eq`). This is what the classical argument was using
  `L_0` for.
* `mem_ramificationGroup_succ_of_adjoin` — given `A = R₀[x, π]`, the condition at `π` propagates to
  all of `A`, since `{y | σ • y - y ∈ 𝔪_A^{i+2}}` is an `R₀`-subalgebra.

Both are stated over an arbitrary `A : ValuationSubring L`, with `x`, `π` and the generation
hypothesis supplied by the caller. `Langlands.RamificationFiltrationAdicCompletion` discharges all
three in the adic-completion setting — `x` from `Langlands.HenselianResidueLift`, the generation
statement from `Langlands.TwoGeneratorMonogenic` — giving
`IsDedekindDomain.HeightOneSpectrum.mem_ramificationGroup_succ_iff`, the kernel computation in
concrete form.

**Still not attempted.** The associated-graded maps themselves (`G_0 →* (ResidueField A)ˣ`,
`G_i / G_{i+1} →+ ResidueField A`) are not constructed as bundled homomorphisms, and neither is
their injectivity as a statement about those bundled objects; only the kernel *characterization*
they were blocked on is proved. The classical "eventually trivial" finiteness fact (the filtration
hits `⊥` past some `N`) is likewise untouched. See `ROADMAP.md`, Phase 2b.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

section MaximalIdealInvariance

variable {A : ValuationSubring L}

/-- Each `σ` in the decomposition subgroup fixes the maximal ideal of `A` setwise: `σ` acts on `A`
as a ring automorphism (`MulSemiringAction.toRingEquiv`), and ring automorphisms of a local ring
fix its unique maximal ideal setwise (`IsLocalRing.maximalIdeal_comap`, applied to the surjective,
hence local, ring hom underlying the automorphism). -/
theorem mem_maximalIdeal_smul_iff (σ : A.decompositionSubgroup K) (x : A) :
    σ • x ∈ IsLocalRing.maximalIdeal A ↔ x ∈ IsLocalRing.maximalIdeal A := by
  set e : A →+* A := (MulSemiringAction.toRingEquiv (A.decompositionSubgroup K) A σ : A →+* A)
    with hedef
  haveI : IsLocalHom e :=
    IsLocalHom.of_surjective e (MulSemiringAction.toRingEquiv (A.decompositionSubgroup K) A σ).surjective
  have hcomap : (IsLocalRing.maximalIdeal A).comap e = IsLocalRing.maximalIdeal A :=
    IsLocalRing.maximalIdeal_comap e
  have hex : e x = σ • x := MulSemiringAction.toRingEquiv_apply_apply _ _ σ x
  rw [← hex, ← Ideal.mem_comap, hcomap]

/-- Each `σ` in the decomposition subgroup fixes every power of the maximal ideal of `A` setwise
(one direction, which is all that's needed to build the ramification-group subgroup structure):
if `x ∈ 𝔪_A ^ n` then `σ • x ∈ 𝔪_A ^ n`. This upgrades `mem_maximalIdeal_smul_iff` from `𝔪_A` to
`𝔪_A ^ n` via `Ideal.map_pow` applied to the ring-automorphism view of `σ`. -/
theorem smul_mem_pow_maximalIdeal (σ : A.decompositionSubgroup K) (n : ℕ) {x : A}
    (hx : x ∈ IsLocalRing.maximalIdeal A ^ n) :
    σ • x ∈ IsLocalRing.maximalIdeal A ^ n := by
  set e := MulSemiringAction.toRingEquiv (A.decompositionSubgroup K) A σ with hedef
  have hmap : (IsLocalRing.maximalIdeal A ^ n).map e = IsLocalRing.maximalIdeal A ^ n := by
    rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
  have hmem : e x ∈ (IsLocalRing.maximalIdeal A ^ n).map e := Ideal.mem_map_of_mem e hx
  rw [hmap] at hmem
  have hex : e x = σ • x := MulSemiringAction.toRingEquiv_apply_apply _ _ σ x
  rwa [hex] at hmem

end MaximalIdealInvariance

/-! ### The ramification filtration -/

/-- The `i`-th ramification group in lower numbering: `σ` fixes every element of `A` modulo
`𝔪_A ^ (i + 1)`. This is Serre's `G_i` for `i : ℕ` — see the module docstring for the indexing
convention (there is no separate `i = -1` case; that role is played by `A.decompositionSubgroup K`
itself). -/
def ramificationGroup (A : ValuationSubring L) (i : ℕ) : Subgroup (A.decompositionSubgroup K) where
  carrier := {σ | ∀ x : A, σ • x - x ∈ IsLocalRing.maximalIdeal A ^ (i + 1)}
  one_mem' x := by simp
  mul_mem' {σ τ} hσ hτ x := by
    have hτx : τ • x - x ∈ IsLocalRing.maximalIdeal A ^ (i + 1) := hτ x
    have hσmap : σ • (τ • x - x) ∈ IsLocalRing.maximalIdeal A ^ (i + 1) :=
      smul_mem_pow_maximalIdeal K σ (i + 1) hτx
    have hσx : σ • x - x ∈ IsLocalRing.maximalIdeal A ^ (i + 1) := hσ x
    have hsplit : (σ * τ) • x - x = σ • (τ • x - x) + (σ • x - x) := by
      rw [mul_smul, smul_sub]; ring
    rw [hsplit]
    exact Ideal.add_mem _ hσmap hσx
  inv_mem' {σ} hσ x := by
    have h := hσ (σ⁻¹ • x)
    rw [smul_smul, mul_inv_cancel, one_smul] at h
    have hneg := Submodule.neg_mem _ h
    rwa [neg_sub] at hneg

variable {K}

/-- The ramification filtration is decreasing: `G_{i+1} ≤ G_i`, since `𝔪_A ^ (i + 2) ≤ 𝔪_A ^ (i + 1)`
(ideal powers are decreasing). -/
theorem ramificationGroup_succ_le (A : ValuationSubring L) (i : ℕ) :
    ramificationGroup K A (i + 1) ≤ ramificationGroup K A i := by
  intro σ hσ x
  exact Ideal.pow_le_pow_right (Nat.le_succ _) (hσ x)

/-- `ramificationGroup K A 0` is Serre's `G_0`, the inertia group: `σ` fixes `A` modulo `𝔪_A`
(the `i = 0` case, `𝔪_A ^ 1 = 𝔪_A`) exactly when `σ` acts trivially on the residue field
`A ⧸ 𝔪_A`, which is the defining condition of `A.inertiaSubgroup K`. -/
theorem ramificationGroup_zero (A : ValuationSubring L) :
    ramificationGroup K A 0 = A.inertiaSubgroup K := by
  ext σ
  simp only [ramificationGroup, inertiaSubgroup, Subgroup.mem_mk, zero_add,
    pow_one, MonoidHom.mem_ker]
  have hstep : ∀ y : IsLocalRing.ResidueField A,
      (MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) σ) y
        = σ • y := by
    intro y
    change (MulSemiringAction.toRingEquiv (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A) σ) y = σ • y
    exact MulSemiringAction.toRingEquiv_apply_apply _ _ σ y
  constructor
  · intro h
    ext y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := A) y
    rw [hstep, RingAut.one_apply,
      ← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    exact h x
  · intro h x
    have hy := RingEquiv.congr_fun h (IsLocalRing.residue A x)
    rw [hstep, RingAut.one_apply,
      ← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff] at hy
    exact hy

/-- Each `ramificationGroup K A i` is normal not merely in the inertia subgroup but in the *full*
decomposition group: for `τ` in `A.decompositionSubgroup K` and `σ ∈ ramificationGroup K A i`,
`τστ⁻¹ • x - x = τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x)`, which lies in `𝔪_A ^ (i + 1)` by
`smul_mem_pow_maximalIdeal` applied to `σ`'s defining property at the point `τ⁻¹ • x` — no
membership hypothesis on `τ` itself is needed. -/
theorem ramificationGroup_normal (A : ValuationSubring L) (i : ℕ) :
    (ramificationGroup K A i).Normal where
  conj_mem σ hσ τ x := by
    have hσy : σ • (τ⁻¹ • x) - τ⁻¹ • x ∈ IsLocalRing.maximalIdeal A ^ (i + 1) := hσ (τ⁻¹ • x)
    have hτmap : τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) ∈ IsLocalRing.maximalIdeal A ^ (i + 1) :=
      smul_mem_pow_maximalIdeal K τ (i + 1) hσy
    have hsplit : (τ * σ * τ⁻¹) • x - x = τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) := by
      simp [mul_smul, smul_sub, smul_inv_smul]
    rwa [hsplit]

/-! ### Rigidity of a simple root, and the kernel direction

The two lemmas below are the general-theory half of the associated-graded kernel argument the
module docstring's "Scope" section flags as blocked. They isolate exactly what the blocked step
needs from the arithmetic input, and what it does *not*:

* it does **not** need `A` to be monogenic over the ring of integers of a maximal unramified
  subextension realized as a subfield, nor an Eisenstein polynomial, nor completeness;
* it **does** need a *pair* of generators — a simple root `x` of a polynomial over the base
  (which the inertia group then fixes exactly, by `IsLocalRing.eq_of_isRoot_of_residue_eq`) and
  the uniformizer `π` — generating `A` as an algebra over the base.

`Langlands.RamificationFiltrationAdicCompletion` discharges both inputs in the adic-completion
setting: the root comes from `Langlands.HenselianResidueLift` and the generation statement from a
Nakayama argument. -/

/-- **An element of `G_0` fixes a simple root of a base-field polynomial exactly.**

Let `R₀` be any base ring mapping into `A` whose image `σ` fixes pointwise (`hfix`), let `f : R₀[X]`
and let `x : A` be a root of `f` at which `f`'s derivative is a unit. If `σ ∈ ramificationGroup K A
0` — equivalently `σ` acts trivially on the residue field of `A`, by `ramificationGroup_zero` —
then `σ • x = x` *exactly*, not merely modulo `𝔪_A`.

The mechanism: `σ • x` is again a root of `f`, since `σ` fixes the coefficients; it has the same
residue as `x`, since `σ` is in the inertia group; and a simple root is determined by its residue
(`IsLocalRing.eq_of_isRoot_of_residue_eq`, Mathlib's `stacks 06RR` in residue-field form). This is
the step that replaces "`L_0` is a subfield fixed by inertia" in the classical argument: no
intermediate field is constructed, only the single element `x`. -/
theorem smul_eq_of_isRoot_of_mem_ramificationGroup_zero {A : ValuationSubring L} {R₀ : Type*}
    [CommRing R₀] [Algebra R₀ A] {f : R₀[X]} {x : A} (hx : Polynomial.aeval x f = 0)
    (hd : IsUnit (Polynomial.aeval x (f.derivative)))
    {σ : A.decompositionSubgroup K} (hσ : σ ∈ ramificationGroup K A 0)
    (hfix : ∀ r : R₀, σ • (algebraMap R₀ A r) = algebraMap R₀ A r) :
    σ • x = x := by
  set e := MulSemiringAction.toRingEquiv (A.decompositionSubgroup K) A σ with he
  have hex : ∀ y : A, e y = σ • y := fun y =>
    MulSemiringAction.toRingEquiv_apply_apply _ _ σ y
  set q : A[X] := f.map (algebraMap R₀ A) with hq
  have hcoeff : (e : A →+* A).comp (algebraMap R₀ A) = algebraMap R₀ A :=
    RingHom.ext fun r => by
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [show (e : A →+* A) (algebraMap R₀ A r) = e (algebraMap R₀ A r) from rfl, hex]
      exact hfix r
  have hqe : q.map (e : A →+* A) = q := by rw [hq, Polynomial.map_map, hcoeff]
  have h1 : q.eval x = 0 := by rw [hq, Polynomial.eval_map, ← Polynomial.aeval_def]; exact hx
  have h2 : q.eval (σ • x) = 0 := by
    have hmap := Polynomial.eval_map_apply (f := (e : A →+* A)) (p := q) x
    rw [hqe] at hmap
    rw [show (σ • x : A) = (e : A →+* A) x from (hex x).symm, hmap, h1, map_zero]
  have h3 : IsLocalRing.residue A x = IsLocalRing.residue A (σ • x) := by
    have hm : σ • x - x ∈ IsLocalRing.maximalIdeal A := by simpa using hσ x
    rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hm
  have h4 : IsUnit ((q.derivative).eval x) := by
    rw [hq, Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hd
  exact (IsLocalRing.eq_of_isRoot_of_residue_eq h1 h2 h3 h4).symm

/-- **The kernel direction of the associated-graded embedding, from a two-element generating set.**

If `A` is generated as an `R₀`-algebra by `x` and `π`, `σ` fixes `R₀` and `x`, and moves `π` by an
element of `𝔪_A ^ (i + 2)`, then `σ ∈ ramificationGroup K A (i + 1)` — i.e. `σ` moves *every*
element of `A` by an element of `𝔪_A ^ (i + 2)`.

This is the `⊆` inclusion the module docstring's "Scope" section records as the wall: the defining
condition of `ramificationGroup K A (i + 1)` is a condition on all of `A`, whereas the
associated-graded map only sees `σ (π) - π`. The proof is that
`{y : A | σ • y - y ∈ 𝔪_A ^ (i + 2)}` is an `R₀`-subalgebra of `A` (a two-line computation from
`σ • (a * b) - a * b = σ • a * (σ • b - b) + (σ • a - a) * b`), so containing the generating set
`{x, π}` makes it everything.

Note that `σ ∈ ramificationGroup K A i` is *not* among the hypotheses: it is not needed. What is
needed is `σ • x = x`, which `smul_eq_of_isRoot_of_mem_ramificationGroup_zero` supplies from
`σ ∈ ramificationGroup K A 0` alone (and `ramificationGroup K A i ≤ ramificationGroup K A 0` by
`ramificationGroup_succ_le`). -/
theorem mem_ramificationGroup_succ_of_adjoin {A : ValuationSubring L} (i : ℕ) {R₀ : Type*}
    [CommRing R₀] [Algebra R₀ A] {x π : A}
    (hgen : Algebra.adjoin R₀ ({x, π} : Set A) = ⊤) {σ : A.decompositionSubgroup K}
    (hfix : ∀ r : R₀, σ • (algebraMap R₀ A r) = algebraMap R₀ A r) (hx : σ • x = x)
    (hπ : σ • π - π ∈ IsLocalRing.maximalIdeal A ^ (i + 2)) :
    σ ∈ ramificationGroup K A (i + 1) := by
  set I : Ideal A := IsLocalRing.maximalIdeal A ^ (i + 2) with hI
  let S : Subalgebra R₀ A :=
    { carrier := {y : A | σ • y - y ∈ I}
      mul_mem' := by
        intro a b ha hb
        have hsplit : σ • (a * b) - a * b = (σ • a) * (σ • b - b) + (σ • a - a) * b := by
          rw [smul_mul']; ring
        show σ • (a * b) - a * b ∈ I
        rw [hsplit]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_right _ _ ha)
      one_mem' := by show σ • (1 : A) - 1 ∈ I; simp
      add_mem' := by
        intro a b ha hb
        have hsplit : σ • (a + b) - (a + b) = (σ • a - a) + (σ • b - b) := by
          rw [smul_add]; ring
        show σ • (a + b) - (a + b) ∈ I
        rw [hsplit]
        exact Ideal.add_mem _ ha hb
      zero_mem' := by show σ • (0 : A) - 0 ∈ I; simp
      algebraMap_mem' := by
        intro r
        show σ • algebraMap R₀ A r - algebraMap R₀ A r ∈ I
        rw [hfix r, sub_self]
        exact Ideal.zero_mem _ }
  have hsub : Algebra.adjoin R₀ ({x, π} : Set A) ≤ S := by
    refine Algebra.adjoin_le ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · show σ • y - y ∈ I
      rw [hx, sub_self]
      exact Ideal.zero_mem _
    · exact hπ
  intro y
  exact (hgen ▸ hsub : (⊤ : Subalgebra R₀ A) ≤ S) Algebra.mem_top

end ValuationSubring
