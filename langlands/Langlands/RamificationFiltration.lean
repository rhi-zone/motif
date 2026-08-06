import Langlands.SimpleRootRigidity
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.Algebra.Ring.GeomSum

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

/-! ### The ramification filtration is antitone -/

/-- The ramification filtration is antitone in `i`: `G_j ≤ G_i` for `i ≤ j`. Follows from
`ramificationGroup_succ_le` by induction. -/
theorem ramificationGroup_antitone (A : ValuationSubring L) :
    Antitone (fun i => ramificationGroup K A i) :=
  antitone_nat_of_succ_le (ramificationGroup_succ_le A)

/-- Every ramification group is contained in `G_0`. -/
theorem ramificationGroup_le_zero (A : ValuationSubring L) (i : ℕ) :
    ramificationGroup K A i ≤ ramificationGroup K A 0 :=
  ramificationGroup_antitone A (Nat.zero_le i)

/-! ### The associated-graded pieces, as bundled homomorphisms

This section builds the two maps `Langlands.RamificationFiltration`'s "Scope" docstring records as
not yet constructed: `σ ↦ σ(π)/π mod 𝔪` (a `MonoidHom` on `G_0`, valued in `(ResidueField A)ˣ`) and,
for each `i : ℕ`, `σ ↦ (σ(π) - π)/π^(i+2) mod 𝔪` (a `MonoidHom` on `G_{i+1}`, valued in
`Multiplicative (ResidueField A)`, i.e. additive once unwrapped). What is proved here is the
homomorphism property and its kernel as a *point-test condition at `π`* — content genuinely not
present in `mem_ramificationGroup_succ_iff`'s kernel characterization, which this file (imported by
the file that proves that characterization) cannot itself state. `Langlands.
RamificationFiltrationAdicCompletion` composes the two: the point-test kernel proved here, with
`mem_ramificationGroup_succ_iff` translating the point-test condition into genuine `ramificationGroup`
membership, to get the full `G_i ⧸ G_{i+1} ↪ 𝓀` statements.

The additive case's homomorphism property needs a degree estimate on the "error term" of
`σ(π) ^ (i+2) - π ^ (i+2)`: writing `σ(π) - π = c_σ · π^(i+2)` for `σ ∈ ramificationGroup K A (i+1)`,
the two-variable geometric-sum factorization `x^n - y^n = (∑ x^k y^(n-1-k)) · (x - y)` gives an error
term lying in `𝔪_A^(i+2) · 𝔪_A^(i+1) = 𝔪_A^(2i+3)`, comfortably inside the target precision
`𝔪_A^(i+3)` for every `i : ℕ` — no extra hypothesis on `i` is needed, unlike the `i = 0` multiplicative
case, which needs a separate (simpler, no error term) argument. -/

section AssociatedGraded

variable {A : ValuationSubring L} {π : A}

/-- Every term of the geometric-sum expansion of `x^(n+1) - y^(n+1)` lies in `𝔪_A^n`, provided both
`x` and `y` lie in `𝔪_A`. -/
theorem geomSum₂_mem_pow_maximalIdeal {x y : A} (hx : x ∈ IsLocalRing.maximalIdeal A)
    (hy : y ∈ IsLocalRing.maximalIdeal A) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n - k)) ∈ IsLocalRing.maximalIdeal A ^ n := by
  refine Ideal.sum_mem _ fun k hk => ?_
  have hle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hmem : x ^ k * y ^ (n - k) ∈
      IsLocalRing.maximalIdeal A ^ k * IsLocalRing.maximalIdeal A ^ (n - k) :=
    Ideal.mul_mem_mul (Ideal.pow_mem_pow hx k) (Ideal.pow_mem_pow hy (n - k))
  rwa [← pow_add, Nat.add_sub_cancel' hle] at hmem

variable (hπ : IsLocalRing.maximalIdeal A = Ideal.span ({(π : A)} : Set A)) (hπ0 : (π : A) ≠ 0)

include hπ hπ0

omit hπ0 in
/-- `π` lies in `𝔪_A` (it generates it). -/
theorem mem_maximalIdeal_of_uniformizer : (π : A) ∈ IsLocalRing.maximalIdeal A :=
  hπ ▸ Ideal.mem_span_singleton_self _

/-! #### The `i = 0` case: `σ ↦ σ(π)/π mod 𝔪`, a `MonoidHom` on `G_0` -/

/-- **Any `σ` in the decomposition subgroup scales `π` by a unit of `A`.** `σ` fixes `𝔪_A` setwise
(hence `Ideal.map`s `span {π}` to itself), so `σ • π` and `π` generate the same ideal; extracting
both containments via `Ideal.mem_span_singleton'` and cancelling `π` (nonzero, `A` a domain) shows
the two witnessing coefficients are mutually inverse. -/
theorem exists_isUnit_smul_eq_mul (σ : A.decompositionSubgroup K) :
    ∃ c : A, IsUnit c ∧ σ • π = c * π := by
  set e := MulSemiringAction.toRingEquiv (A.decompositionSubgroup K) A σ with hedef
  have hmapEq : (IsLocalRing.maximalIdeal A).map e = IsLocalRing.maximalIdeal A :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  have hex : e π = σ • π := MulSemiringAction.toRingEquiv_apply_apply _ _ σ π
  have himg : e '' ({(π : A)} : Set A) = ({(σ • π : A)} : Set A) := by
    rw [Set.image_singleton, hex]
  have hspan : Ideal.span ({(σ • π : A)} : Set A) = Ideal.span ({(π : A)} : Set A) := by
    rw [← himg, ← Ideal.map_span, ← hπ, hmapEq]
  have h1 : (σ • π : A) ∈ Ideal.span ({(π : A)} : Set A) := by
    rw [← hspan]; exact Ideal.mem_span_singleton_self _
  have h2 : (π : A) ∈ Ideal.span ({(σ • π : A)} : Set A) := by
    rw [hspan]; exact Ideal.mem_span_singleton_self _
  obtain ⟨c1, hc1⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨c2, hc2⟩ := Ideal.mem_span_singleton'.mp h2
  have heq : c2 * c1 * π = π := by rw [mul_assoc, hc1]; exact hc2
  have heq1 : c2 * c1 = 1 := mul_right_cancel₀ hπ0 (heq.trans (one_mul π).symm)
  exact ⟨c1, IsUnit.of_mul_eq_one c2 (by rw [mul_comm]; exact heq1), hc1.symm⟩

/-- The unit coefficient `c_σ` of `exists_isUnit_smul_eq_mul`, chosen once and for all. -/
noncomputable def gradedZeroCoeff (σ : A.decompositionSubgroup K) : A :=
  (exists_isUnit_smul_eq_mul hπ hπ0 σ).choose

theorem gradedZeroCoeff_isUnit (σ : A.decompositionSubgroup K) :
    IsUnit (gradedZeroCoeff hπ hπ0 σ) :=
  (exists_isUnit_smul_eq_mul hπ hπ0 σ).choose_spec.1

theorem gradedZeroCoeff_spec (σ : A.decompositionSubgroup K) :
    σ • π = gradedZeroCoeff hπ hπ0 σ * π :=
  (exists_isUnit_smul_eq_mul hπ hπ0 σ).choose_spec.2

theorem gradedZeroCoeff_ne_zero (σ : A.decompositionSubgroup K) :
    IsLocalRing.residue A (gradedZeroCoeff hπ hπ0 σ) ≠ 0 := by
  rw [Ne, IsLocalRing.residue_eq_zero_iff]
  exact IsLocalRing.notMem_maximalIdeal.mpr (gradedZeroCoeff_isUnit hπ hπ0 σ)

/-- The coefficient is multiplicative: `c_{στ} = σ(c_τ) · c_σ`, by cancelling `π` in
`(στ) • π = σ • (τ • π) = σ(c_τ) · σ(π) = σ(c_τ) · c_σ · π`. -/
theorem gradedZeroCoeff_mul (σ τ : A.decompositionSubgroup K) :
    gradedZeroCoeff hπ hπ0 (σ * τ)
      = σ • gradedZeroCoeff hπ hπ0 τ * gradedZeroCoeff hπ hπ0 σ := by
  have hlhs : gradedZeroCoeff hπ hπ0 (σ * τ) * π = (σ * τ) • π :=
    (gradedZeroCoeff_spec hπ hπ0 (σ * τ)).symm
  have hrhs : (σ • gradedZeroCoeff hπ hπ0 τ * gradedZeroCoeff hπ hπ0 σ) * π = (σ * τ) • π := by
    rw [mul_smul, gradedZeroCoeff_spec hπ hπ0 τ, smul_mul', gradedZeroCoeff_spec hπ hπ0 σ]; ring
  exact mul_right_cancel₀ hπ0 (hlhs.trans hrhs.symm)

/-- **The `i = 0` associated-graded map, as a `MonoidHom`.** `σ ↦ σ(π)/π mod 𝔪`, valued in
`(ResidueField A)ˣ`, defined on `G_0 = ramificationGroup K A 0`: for `σ ∈ G_0`, `σ` fixes the
residue field pointwise, so `residue (σ • c_τ) = residue c_τ`, which is exactly what makes
`residue ∘ gradedZeroCoeff` multiplicative on `G_0` (`gradedZeroCoeff_mul` plus commutativity of the
residue field). -/
noncomputable def gradedZeroHom :
    (ramificationGroup K A 0) →* (IsLocalRing.ResidueField A)ˣ where
  toFun σ := Units.mk0 (IsLocalRing.residue A (gradedZeroCoeff hπ hπ0 (σ : A.decompositionSubgroup K)))
    (gradedZeroCoeff_ne_zero hπ hπ0 (σ : A.decompositionSubgroup K))
  map_one' := by
    refine Units.ext ?_
    rw [Units.val_mk0, Units.val_one, (ramificationGroup K A 0).coe_one]
    have h1 : gradedZeroCoeff hπ hπ0 (1 : A.decompositionSubgroup K) * π
        = (1 : A.decompositionSubgroup K) • π := (gradedZeroCoeff_spec hπ hπ0 1).symm
    rw [one_smul] at h1
    rw [mul_right_cancel₀ hπ0 (h1.trans (one_mul π).symm), map_one]
  map_mul' σ τ := by
    refine Units.ext ?_
    rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_mk0,
      (ramificationGroup K A 0).coe_mul, gradedZeroCoeff_mul]
    have hσ0 : (σ : A.decompositionSubgroup K) ∈ ramificationGroup K A 0 := σ.2
    have hres : IsLocalRing.residue A
        ((σ : A.decompositionSubgroup K) • gradedZeroCoeff hπ hπ0 (τ : A.decompositionSubgroup K))
        = IsLocalRing.residue A (gradedZeroCoeff hπ hπ0 (τ : A.decompositionSubgroup K)) := by
      have hσπ := hσ0 (gradedZeroCoeff hπ hπ0 (τ : A.decompositionSubgroup K))
      rw [zero_add, pow_one] at hσπ
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact hσπ
    rw [map_mul, hres, mul_comm]

theorem gradedZeroHom_coe (σ : ramificationGroup K A 0) :
    (gradedZeroHom hπ hπ0 σ : IsLocalRing.ResidueField A)
      = IsLocalRing.residue A (gradedZeroCoeff hπ hπ0 (σ : A.decompositionSubgroup K)) :=
  rfl

/-- **The kernel of `gradedZeroHom`, as a point-test condition at `π`.** `σ ↦ 1` under
`gradedZeroHom` unwinds (via `Units.mk0`/`IsLocalRing.residue`) to `c_σ ≡ 1 mod 𝔪`, which is exactly
`σ • π - π ∈ 𝔪_A ^ 2`. This is stated as a point-test condition, not as `σ ∈ ramificationGroup K A 1`
directly, because turning the point test into full `ramificationGroup` membership needs
`mem_ramificationGroup_succ_iff`, proved downstream of this file (it needs a generating pair `{x, π}`
not available at this level of generality); see `Langlands.RamificationFiltrationAdicCompletion` for
the composed statement. -/
theorem gradedZeroHom_apply_eq_one_iff (σ : ramificationGroup K A 0) :
    gradedZeroHom hπ hπ0 σ = 1 ↔
      (σ : A.decompositionSubgroup K) • π - π ∈ IsLocalRing.maximalIdeal A ^ 2 := by
  set c := gradedZeroCoeff hπ hπ0 (σ : A.decompositionSubgroup K) with hc
  have hval : (σ : A.decompositionSubgroup K) • π - π = (c - 1) * π := by
    rw [hc, gradedZeroCoeff_spec hπ hπ0 (σ : A.decompositionSubgroup K)]; ring
  have hspan2 : IsLocalRing.maximalIdeal A ^ 2 = Ideal.span ({π ^ 2} : Set A) := by
    rw [hπ, Ideal.span_singleton_pow]
  have hB : (σ : A.decompositionSubgroup K) • π - π ∈ IsLocalRing.maximalIdeal A ^ 2
      ↔ IsLocalRing.residue A c = 1 := by
    rw [hval, hspan2, Ideal.mem_span_singleton, sq π, mul_comm (c - 1) π,
      mul_dvd_mul_iff_left hπ0, ← Ideal.mem_span_singleton, ← hπ,
      ← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
  have hA : gradedZeroHom hπ hπ0 σ = 1 ↔ IsLocalRing.residue A c = 1 := by
    rw [Units.ext_iff, gradedZeroHom_coe, Units.val_one, ← hc]
  rw [hA, hB]

/-! #### The `i ≥ 1` case: `σ ↦ (σ(π) - π)/π^(i+2) mod 𝔪`, a `MonoidHom` on `G_{i+1}` -/

omit hπ0 in
/-- `𝔪_A ^ n = span {π ^ n}`, for any `n`. -/
theorem maximalIdeal_pow_eq (n : ℕ) :
    IsLocalRing.maximalIdeal A ^ n = Ideal.span ({π ^ n} : Set A) := by
  rw [hπ, Ideal.span_singleton_pow]

variable (i : ℕ)

/-- The coefficient `c_σ` with `σ • π - π = c_σ · π^(i+2)`, for `σ ∈ ramificationGroup K A (i+1)`
(the `(i+1)+1 = i+2`-power membership is exactly the defining property of `ramificationGroup K A
(i+1)`, tested at `π`). -/
theorem exists_smul_sub_eq_mul_pow (σ : ramificationGroup K A (i + 1)) :
    ∃ c : A, (σ : A.decompositionSubgroup K) • π - π = c * π ^ (i + 2) := by
  have hmem : (σ : A.decompositionSubgroup K) • π - π ∈ IsLocalRing.maximalIdeal A ^ (i + 1 + 1) :=
    σ.2 π
  rw [maximalIdeal_pow_eq hπ (i + 2)] at hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨c, hc.symm⟩

/-- The coefficient of `exists_smul_sub_eq_mul_pow`, chosen once and for all. -/
noncomputable def succCoeff (σ : ramificationGroup K A (i + 1)) : A :=
  (exists_smul_sub_eq_mul_pow hπ hπ0 i σ).choose

theorem succCoeff_spec (σ : ramificationGroup K A (i + 1)) :
    (σ : A.decompositionSubgroup K) • π - π = succCoeff hπ hπ0 i σ * π ^ (i + 2) :=
  (exists_smul_sub_eq_mul_pow hπ hπ0 i σ).choose_spec

/-- **The coefficient is additive modulo `𝔪`.** The exact identity is
`c_{στ} = c_σ + σ(c_τ) + σ(c_τ) · S · c_σ`, where `S` is the geometric-sum factor of
`σ(π)^(i+2) - π^(i+2)`; since `S ∈ 𝔪_A` (it is a sum of terms each visibly in `𝔪_A^(i+1) ⊆ 𝔪_A`,
`geomSum₂_mem_pow_maximalIdeal`), the error term vanishes after taking residues. -/
theorem succCoeff_residue_add (σ τ : ramificationGroup K A (i + 1)) :
    IsLocalRing.residue A (succCoeff hπ hπ0 i (σ * τ))
      = IsLocalRing.residue A (succCoeff hπ hπ0 i σ) + IsLocalRing.residue A (succCoeff hπ hπ0 i τ) := by
  have hSσ := succCoeff_spec hπ hπ0 i σ
  have hSτ := succCoeff_spec hπ hπ0 i τ
  have hSστ := succCoeff_spec hπ hπ0 i (σ * τ)
  rw [(ramificationGroup K A (i + 1)).coe_mul, mul_smul] at hSστ
  have hτeq : (τ : A.decompositionSubgroup K) • π = π + succCoeff hπ hπ0 i τ * π ^ (i + 2) := by
    rw [← hSτ]; ring
  have hσeq : (σ : A.decompositionSubgroup K) • π = π + succCoeff hπ hπ0 i σ * π ^ (i + 2) := by
    rw [← hSσ]; ring
  have step1 : (σ : A.decompositionSubgroup K) • ((τ : A.decompositionSubgroup K) • π)
      = (σ : A.decompositionSubgroup K) • π
        + (σ : A.decompositionSubgroup K) • succCoeff hπ hπ0 i τ
          * ((σ : A.decompositionSubgroup K) • π) ^ (i + 2) := by
    rw [hτeq, smul_add, smul_mul', smul_pow']
  have hxmem : (σ : A.decompositionSubgroup K) • π ∈ IsLocalRing.maximalIdeal A := by
    have h1 : π ∈ IsLocalRing.maximalIdeal A ^ 1 := by
      rw [pow_one]; exact mem_maximalIdeal_of_uniformizer hπ
    have h2 := smul_mem_pow_maximalIdeal K (σ : A.decompositionSubgroup K) 1 h1
    rwa [pow_one] at h2
  have hymem : (π : A) ∈ IsLocalRing.maximalIdeal A := mem_maximalIdeal_of_uniformizer hπ
  have hSmem : (∑ k ∈ Finset.range (i + 2),
      ((σ : A.decompositionSubgroup K) • π) ^ k * π ^ (i + 1 - k)) ∈ IsLocalRing.maximalIdeal A := by
    have h := Ideal.pow_le_pow_right (Nat.le_add_left 1 i)
      (geomSum₂_mem_pow_maximalIdeal hxmem hymem (i + 1))
    rwa [pow_one] at h
  have hgeom := geom_sum₂_mul ((σ : A.decompositionSubgroup K) • π) π (i + 2)
  have hxy : ((σ : A.decompositionSubgroup K) • π) ^ (i + 2) - π ^ (i + 2)
      = (∑ k ∈ Finset.range (i + 2), ((σ : A.decompositionSubgroup K) • π) ^ k * π ^ (i + 1 - k))
        * ((σ : A.decompositionSubgroup K) • π - π) := hgeom.symm
  have hxpow : ((σ : A.decompositionSubgroup K) • π) ^ (i + 2)
      = π ^ (i + 2)
        + (∑ k ∈ Finset.range (i + 2), ((σ : A.decompositionSubgroup K) • π) ^ k * π ^ (i + 1 - k))
          * (succCoeff hπ hπ0 i σ * π ^ (i + 2)) := by
    rw [hSσ] at hxy; linear_combination hxy
  have key : succCoeff hπ hπ0 i (σ * τ) * π ^ (i + 2)
      = (succCoeff hπ hπ0 i σ + (σ : A.decompositionSubgroup K) • succCoeff hπ hπ0 i τ
          + (σ : A.decompositionSubgroup K) • succCoeff hπ hπ0 i τ
            * (∑ k ∈ Finset.range (i + 2),
                ((σ : A.decompositionSubgroup K) • π) ^ k * π ^ (i + 1 - k))
            * succCoeff hπ hπ0 i σ) * π ^ (i + 2) := by
    rw [← hSστ, step1, hxpow, hσeq]; ring
  have hcancel : succCoeff hπ hπ0 i (σ * τ)
      = succCoeff hπ hπ0 i σ + (σ : A.decompositionSubgroup K) • succCoeff hπ hπ0 i τ
        + (σ : A.decompositionSubgroup K) • succCoeff hπ hπ0 i τ
          * (∑ k ∈ Finset.range (i + 2), ((σ : A.decompositionSubgroup K) • π) ^ k * π ^ (i + 1 - k))
          * succCoeff hπ hπ0 i σ :=
    mul_right_cancel₀ (pow_ne_zero (i + 2) hπ0) key
  have hσfix : IsLocalRing.residue A ((σ : A.decompositionSubgroup K) • succCoeff hπ hπ0 i τ)
      = IsLocalRing.residue A (succCoeff hπ hπ0 i τ) := by
    have hσ0 : (σ : A.decompositionSubgroup K) ∈ ramificationGroup K A 0 :=
      ramificationGroup_le_zero A (i + 1) σ.2
    have h := hσ0 (succCoeff hπ hπ0 i τ)
    rw [zero_add, pow_one] at h
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact h
  rw [hcancel, map_add, map_add, map_mul, map_mul, hσfix,
    (IsLocalRing.residue_eq_zero_iff _).mpr hSmem, mul_zero, zero_mul, add_zero]

/-- **The `i ≥ 1` associated-graded map, as a `MonoidHom`.** `σ ↦ (σ(π) - π)/π^(i+2) mod 𝔪`,
defined on `G_{i+1} = ramificationGroup K A (i + 1)`, valued in `Multiplicative (ResidueField A)`
(i.e. additive once unwrapped): `succCoeff_residue_add` is exactly its `map_mul'`. -/
noncomputable def gradedSuccHom :
    (ramificationGroup K A (i + 1)) →* Multiplicative (IsLocalRing.ResidueField A) where
  toFun σ := Multiplicative.ofAdd (IsLocalRing.residue A (succCoeff hπ hπ0 i σ))
  map_one' := by
    apply Multiplicative.toAdd.injective
    show IsLocalRing.residue A (succCoeff hπ hπ0 i (1 : ramificationGroup K A (i + 1))) = 0
    have hspec := succCoeff_spec hπ hπ0 i (1 : ramificationGroup K A (i + 1))
    rw [(ramificationGroup K A (i + 1)).coe_one, one_smul, sub_self] at hspec
    have hz : succCoeff hπ hπ0 i (1 : ramificationGroup K A (i + 1)) = 0 :=
      mul_right_cancel₀ (pow_ne_zero (i + 2) hπ0) (hspec.symm.trans (zero_mul _).symm)
    rw [hz, map_zero]
  map_mul' σ τ := by
    apply Multiplicative.toAdd.injective
    exact succCoeff_residue_add hπ hπ0 i σ τ

theorem gradedSuccHom_coe (σ : ramificationGroup K A (i + 1)) :
    Multiplicative.toAdd (gradedSuccHom hπ hπ0 i σ)
      = IsLocalRing.residue A (succCoeff hπ hπ0 i σ) :=
  rfl

/-- **The kernel of `gradedSuccHom`, as a point-test condition at `π`.** Mirrors
`gradedZeroHom_apply_eq_one_iff`: `σ ↦ 1` unwinds to `c_σ ≡ 0 mod 𝔪`, i.e. `σ • π - π ∈ 𝔪_A^(i+3)`.
Stated as a point-test condition for the same reason: turning it into full `ramificationGroup`
membership needs `mem_ramificationGroup_succ_iff`, downstream of this file. -/
theorem gradedSuccHom_apply_eq_one_iff (σ : ramificationGroup K A (i + 1)) :
    gradedSuccHom hπ hπ0 i σ = 1 ↔
      (σ : A.decompositionSubgroup K) • π - π ∈ IsLocalRing.maximalIdeal A ^ (i + 3) := by
  set c := succCoeff hπ hπ0 i σ with hc
  have hval : (σ : A.decompositionSubgroup K) • π - π = c * π ^ (i + 2) := succCoeff_spec hπ hπ0 i σ
  have hspan3 : IsLocalRing.maximalIdeal A ^ (i + 3) = Ideal.span ({π ^ (i + 3)} : Set A) :=
    maximalIdeal_pow_eq hπ (i + 3)
  have hB : (σ : A.decompositionSubgroup K) • π - π ∈ IsLocalRing.maximalIdeal A ^ (i + 3)
      ↔ IsLocalRing.residue A c = 0 := by
    rw [hval, hspan3, Ideal.mem_span_singleton,
      show π ^ (i + 3) = π ^ (i + 2) * π from by ring, mul_comm c (π ^ (i + 2)),
      mul_dvd_mul_iff_left (pow_ne_zero (i + 2) hπ0), ← Ideal.mem_span_singleton, ← hπ,
      IsLocalRing.residue_eq_zero_iff]
  have hA : gradedSuccHom hπ hπ0 i σ = 1 ↔ IsLocalRing.residue A c = 0 := by
    rw [← toAdd_eq_zero, gradedSuccHom_coe, ← hc]
  rw [hA, hB]

end AssociatedGraded

end ValuationSubring

/-! ### A decreasing filtration of subgroups of a finite group is eventually constant

Pure group theory, independent of everything above: the combinatorial half of "the ramification
filtration is eventually trivial." The other half — that the filtration's intersection is `⊥` — is
specific to the valuation-ring setting and is supplied by the caller (see
`Langlands.RamificationFiltrationAdicCompletion`). -/

/-- **An antitone `ℕ`-indexed family of subgroups of a finite group is eventually constant.**
Since `Subgroup G` is finite (`G` finite), the fiber of `f` over some value `v` is infinite
(`Finite.exists_infinite_fiber`); picking `N` in that fiber and, for any `i ≥ N`, a later index `j`
in the fiber with `j ≥ i` sandwiches `f i` between `f j = v` and `f N = v` via antitonicity. -/
theorem Subgroup.exists_eventually_eq_of_antitone {G : Type*} [Group G] [Finite G]
    (f : ℕ → Subgroup G) (hf : Antitone f) :
    ∃ N, ∀ i ≥ N, f i = f N := by
  haveI : Finite (Subgroup G) := Finite.of_injective (SetLike.coe : Subgroup G → Set G)
    SetLike.coe_injective
  obtain ⟨v, hv⟩ := Finite.exists_infinite_fiber f
  rw [Set.infinite_coe_iff] at hv
  obtain ⟨N, hN⟩ := hv.nonempty
  have hiN : f N = v := hN
  refine ⟨N, fun i hi => ?_⟩
  obtain ⟨j, hj, hji⟩ := hv.exists_gt (max i N)
  have hjv : f j = v := hj
  have h1 : f j ≤ f i := hf (le_trans (le_max_left i N) hji.le)
  have h3 : f i ≤ f N := hf hi
  have hFN_le : f N ≤ f i := by rw [hiN, ← hjv]; exact h1
  exact le_antisymm h3 hFN_le
