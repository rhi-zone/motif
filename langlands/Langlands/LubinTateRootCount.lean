import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Polynomial.Tower
import Langlands.LubinTateEisensteinQ
import Langlands.LubinTateTorsionPoints

/-!
# ⚠️ `card_piTorsion_one_eq_residueCard` is VACUOUS whenever `residueCard O ≥ 3`

**`hsplit`, the hypothesis this file's capstone theorem `card_piTorsion_one_eq_residueCard` takes,
can never be discharged for a genuine ramified extension.** `Langlands/LubinTateHsplitVacuity.lean`
proves `hsplit : (P.divX.map (algebraMap O K)).Splits` is jointly unsatisfiable with this file's own
standing `[IsFractionRing O K]` whenever `P.divX.natDegree ≥ 2` (`residueCard O ≥ 3`): that typeclass
forces `K` to already be `Frac(O)`, in which `Q := P.divX`'s image is irreducible (Gauss's lemma),
hence cannot also split completely. `card_piTorsion_one_eq_residueCard` remains a logically valid
`hsplit → …` implication but asserts nothing about any actual instantiation with a nontrivial residue
field. **Do not build further theorems on `hsplit`**; see `Langlands.LubinTateSplittingField` for the
replacement (`K_1` built as `Polynomial.SplittingField`, in which `Q` splits by construction) and
`ROADMAP.md` for the full status. This warning does **not** apply to the rest of this file —
`norm_lt_one_of_aeval_divX_eq_zero`, `mem_piTorsion_one_of_root_divX_map`,
`aeval_divX_map_eq_zero_of_mem_piTorsion_one_ne_zero`, and `norm_eq_rpow_of_mem_piTorsion_one_ne_zero`
take no `hsplit` hypothesis and remain genuine, non-vacuous facts, reusable for `K_1` as-is.

**Only `card_piTorsion_one_eq_residueCard` still carries `[IsFractionRing O K]`.** The rest of the
file (and the whole spacing/mod-`π`/action/freeness chain built on it) now requires only
`[FaithfulSMul O K]` — `algebraMap O K` injective. The root-valuation lemmas used to obtain the
exact norm of a torsion point from `spectralNorm` via `Q`'s *irreducibility over `K`* (Gauss's
lemma, hence `K = Frac(O)`); they now obtain it from `Langlands.EisensteinRootNorm`'s purely
ultrametric Eisenstein-polygon computation, which needs no irreducibility and therefore survives in
a *proper* extension of `Frac(O)` — in particular inside `Q`'s splitting field, where `Q` splits and
irreducibility is false. That is exactly what makes the machinery reusable at
`Langlands.LubinTateSplittingField.K_1`.

# `|piTorsion hπ hf 1| = q`, given `Q := P.divX` splits completely inside `K`

`ROADMAP.md` §33 closed separability of `Q := P.divX` (`P` the Weierstrass-preparation factor of a
Lubin-Tate power series `f`), given two hypotheses (`IsUnit (P.divX.natDegree : O)`,
`‖algebraMap O K π‖ < 1`), the first of which is now derived in general
(`LubinTate.isUnit_natCast_of_add_one_eq_residueCard`, `Langlands/LubinTate.lean`) and true for
`Q.natDegree = residueCard O - 1` specifically; the second remains an explicit hypothesis (see that
file's docstring for why: no caller instantiating this repo's abstract Lubin-Tate `O`/`K` package
against a concrete `HeightOneSpectrum`/`adicCompletion` pair exists yet, so the fact is genuinely
not available from the currently-standing typeclass package, only from a strictly stronger one).

This file assembles the final root-counting step. `piTorsion hπ hf 1` is a literal `Set K` (not a
subset of some auxiliary splitting field), so the correctly-scoped root-counting hypothesis is that
`Q` **already splits completely inside `K` itself** — `(Q.map (algebraMap O K)).Splits` — rather
than introducing an abstract splitting field `L` disconnected from `piTorsion`'s actual carrier.
This is the design choice flagged as open in the task brief: given the choice between "any
splitting field, treated purely algebraically" and "`K` itself already contains the roots", the
second is the one that actually composes with `piTorsion : Set K` without a further transport step,
and is adopted here. (It specializes the general `L / K` machinery of `LubinTateEisensteinQ.lean` at
`L := K`, using the standing `Algebra.IsAlgebraic K K` instance any field trivially carries over
itself and `spectralNorm_extends`/`Polynomial.coe_aeval_eq_eval` to identify `spectralNorm K K` and
`Polynomial.aeval`-at-`K` with `K`'s own norm and `Polynomial.eval`.)

## Main results

* `Polynomial.roots_toFinset_card_eq_natDegree_of_separable_of_splits` : general, `Q`-independent
  fact — a separable polynomial over a field that splits completely (over that same field) has
  exactly `natDegree` distinct roots. Assembled from Mathlib's `Polynomial.nodup_roots`
  (separability ⟹ no repeated roots) and `Polynomial.Splits.natDegree_eq_card_roots` (splitting ⟹
  root-count-with-multiplicity equals degree).
* `LubinTate.card_piTorsion_one_eq_residueCard` : **`Nat.card (piTorsion hπ hf 1) = residueCard O`**
  — the capstone of this whole thread's root-counting arc. Given a Weierstrass factorization
  `f = P * u`, `Q := P.divX` monic/Eisenstein/associate-constant-term (from
  `LubinTate.divX_isWeaklyEisensteinAt_and_associated`), a tame-degree witness (now automatic:
  `LubinTate.isUnit_natCast_of_add_one_eq_residueCard`), `‖algebraMap O K π‖ < 1` (still an explicit
  hypothesis, see above), and `Q`'s map into `K` splitting completely: `piTorsion hπ hf 1` is
  exactly the union of `{0}` and `Q`'s (nonzero, distinct) roots in `K`, of total size
  `1 + (residueCard O - 1) = residueCard O`.

## What remains

`[K_1 : K] = q - 1` and `Gal(K_1/K) ≅ (O/π)ˣ` are not attempted here: this file only pins down the
*size* of the `π`-torsion point set, not the field extension `K_1 := K(F_π[π])` it generates
(`Langlands.LubinTateFieldTower.K_1`) or its Galois-theoretic structure. See `ROADMAP.md`'s entry
for this pass for the precise next step.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

open Polynomial

/-! ## General splitting-field root-counting -/

/-- **A separable polynomial that splits completely has exactly `natDegree` distinct roots.**
General fact about any field `L`, no Lubin-Tate content: `Polynomial.nodup_roots` (from
separability) says `Qk.roots` has no repeats, so its underlying finset has the same cardinality as
the multiset itself (`Multiset.toFinset_card_of_nodup`); `Polynomial.Splits.natDegree_eq_card_roots`
(from `Qk.Splits`) says that multiset's cardinality is exactly `Qk.natDegree`. -/
theorem Polynomial.roots_toFinset_card_eq_natDegree_of_separable_of_splits
    {L : Type*} [Field L] [DecidableEq L] {Qk : L[X]}
    (hsep : Qk.Separable) (hsplit : Qk.Splits) :
    Qk.roots.toFinset.card = Qk.natDegree := by
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)]
  exact hsplit.natDegree_eq_card_roots.symm

namespace LubinTate

open PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [FaithfulSMul O K]
variable {π : O} {f : O⟦X⟧}

/-! ## Assembling `|piTorsion hπ hf 1| = q` -/

omit [Finite (ResidueField O)] in
/-- **A root of `Q := P.divX`'s image in `K` is a root of an Eisenstein-shaped monic polynomial**,
in the sense `Langlands.EisensteinRootNorm` needs: `Q`'s image is monic of the same degree, its
constant coefficient has norm exactly `c := ‖algebraMap O K π‖` (`0 < c < 1`), and every lower
coefficient has norm `≤ c`. Bridges `aeval`-at-`K` to `Polynomial.eval` (they agree for a
polynomial already over `K`, `Algebra.algebraMap_self`) so the general lemmas apply directly. -/
theorem isEisensteinShape_divX_map {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) {f : O⟦X⟧}
    (heq : f = (P : O⟦X⟧) * u) (hf0 : PowerSeries.coeff 0 f = 0) {π : O}
    (hπ : Irreducible π) (hf1 : PowerSeries.coeff 1 f = π)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree)
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) :
    (P.divX.map (algebraMap O K)).Monic ∧
      0 < (P.divX.map (algebraMap O K)).natDegree ∧
      (P.divX.map (algebraMap O K)).natDegree = P.divX.natDegree ∧
      0 < ‖algebraMap O K π‖ ∧
      ‖(P.divX.map (algebraMap O K)).coeff 0‖ = ‖algebraMap O K π‖ ∧
      ∀ i < (P.divX.map (algebraMap O K)).natDegree,
        ‖(P.divX.map (algebraMap O K)).coeff i‖ ≤ ‖algebraMap O K π‖ := by
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf0 hf1 hPdist hPdeg2
  obtain ⟨hmonic, hdegeq, hc0, hc0eq, hweak⟩ :=
    norm_coeff_map_of_isWeaklyEisensteinAt_associated (K := K) hOK hπ hQmonic hQweak hQ0assoc
  exact ⟨hmonic, by rw [hdegeq]; exact hQdeg, hdegeq, hc0, hc0eq, hweak⟩

omit [Finite (ResidueField O)] in
/-- **A root of `Q.map (algebraMap O K)` inside `K` automatically lies in the maximal ideal
`‖x‖ < 1`.** Via `Polynomial.norm_lt_one_of_isEisensteinShape_of_root`
(`Langlands.EisensteinRootNorm`): `Q`'s image is Eisenstein-shaped with sharp constant-term norm
`c := ‖algebraMap O K π‖ < 1` (`isEisensteinShape_divX_map`), and a root of such a polynomial has
norm `< 1` by the ultrametric inequality alone.

**This route replaces the earlier `spectralNorm`-based one and is why this theorem no longer needs
`[IsFractionRing O K]`.** The old proof specialized `spectralNorm_eq_of_isLubinTatePoly_root` at
`L := K`, which required `Q`'s image to be *irreducible over `K`* (Gauss's lemma, hence
`K = Frac(O)`); the ultrametric argument needs no irreducibility at all, so it survives in a proper
extension of `Frac(O)` — in particular inside `Q`'s splitting field, where `Q` splits. -/
theorem norm_lt_one_of_aeval_divX_eq_zero {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) {f : O⟦X⟧}
    (heq : f = (P : O⟦X⟧) * u) (hf0 : PowerSeries.coeff 0 f = 0) {π : O}
    (hπ : Irreducible π) (hf1 : PowerSeries.coeff 1 f = π)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree)
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) (hπnorm : ‖algebraMap O K π‖ < 1)
    {x : K} (hx : Polynomial.aeval x (P.divX.map (algebraMap O K)) = 0) : ‖x‖ < 1 := by
  obtain ⟨hmonic, hdegpos, -, hc0, hc0eq, hweak⟩ :=
    isEisensteinShape_divX_map (K := K) hu heq hf0 hπ hf1 hPdist hPdeg2 hOK
  exact Polynomial.norm_lt_one_of_isEisensteinShape_of_root hmonic hdegpos hπnorm hc0 hweak
    (by rw [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] at hx; exact hx)

omit [Finite (ResidueField O)] in
/-- **A root of `Q := P.divX`'s image in `K` lies in `piTorsion hπ hf 1`.** The root-membership
half of `piTorsion hπ hf 1 = {0} ∪ (Q.map (algebraMap O K)).roots.toFinset` (the `hSmem` block
inside `card_piTorsion_one_eq_residueCard`'s proof below), extracted standalone: it needs only that
`x` is a root of `Q`'s image, not that `Q` splits completely (`hsplit` is never used here — the
proof only uses `norm_lt_one_of_aeval_divX_eq_zero`, `X_mul_divX_add`, and
`eval_eq_zero_iff_aeval_eq_zero`). Reused by `card_piTorsion_one_eq_residueCard`'s own proof, and by
`Langlands.LubinTateFieldTower`'s transport of `hsplit` down to `K_1 := K(F_π[π])`
(`ROADMAP.md`'s `hsplit`/`K_1` framing question: `K_1`'s generators are exactly `Q`'s roots once
`hsplit` holds for `K`, so this is the fact that makes those generators already lie in
`piTorsion hπ hf 1`, hence — trivially — in `K_1` itself). -/
theorem mem_piTorsion_one_of_root_divX_map [DecidableEq K]
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree)
    {x : K} (hx : x ∈ (P.divX.map (algebraMap O K)).roots.toFinset) :
    x ∈ piTorsion (K := K) hπ hf 1 := by
  classical
  have hf0 : PowerSeries.coeff 0 f = 0 := hf.1
  have hf1 : PowerSeries.coeff 1 f = π := hf.2.1
  rw [Multiset.mem_toFinset, Polynomial.mem_roots'] at hx
  obtain ⟨-, hroot⟩ := hx
  have haevalQ : Polynomial.aeval x (P.divX.map (algebraMap O K)) = 0 := by
    rw [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
    exact hroot
  have hxnorm : ‖x‖ < 1 :=
    norm_lt_one_of_aeval_divX_eq_zero hu heq hf0 hπ hf1 hPdist hPdeg2 hOK hπnorm haevalQ
  refine ⟨hxnorm, ?_⟩
  have haevalQO : Polynomial.aeval x P.divX = 0 := by
    rw [← Polynomial.aeval_map_algebraMap K x P.divX]
    exact haevalQ
  have hPfact : P = Polynomial.X * P.divX := by
    have hXid := Polynomial.X_mul_divX_add P
    rw [coeff_zero_eq_zero_of_eq_mul hu heq hf0, Polynomial.C_0, add_zero] at hXid
    exact hXid.symm
  have haevalP : Polynomial.aeval x P = 0 := by
    conv_lhs => rw [hPfact]
    rw [map_mul, Polynomial.aeval_X, haevalQO, mul_zero]
  rw [iter_one]
  exact (eval_eq_zero_iff_aeval_eq_zero hOK hu heq hxnorm).mpr haevalP

omit [Finite (ResidueField O)] [FaithfulSMul O K] in
/-- **A nonzero element of `piTorsion hπ hf 1` is a root of `Q := P.divX`'s image in `K`.** The
reverse of `mem_piTorsion_one_of_root_divX_map`'s root-membership direction, extracted from the
`hSmem` block of `card_piTorsion_one_eq_residueCard`'s proof: unlike that theorem, this needs no
splitting hypothesis (`hsplit`) at all — `P = X * Q` (`Polynomial.X_mul_divX_add`) makes `aeval x P
= x * aeval x Q`, so a nonzero root of `P` (which `x` is, `eval_eq_zero_iff_aeval_eq_zero`) forces
`aeval x Q = 0` directly. -/
theorem aeval_divX_map_eq_zero_of_mem_piTorsion_one_ne_zero
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) {x : K} (hx : x ∈ piTorsion (K := K) hπ hf 1) (hx0 : x ≠ 0) :
    Polynomial.aeval x (P.divX.map (algebraMap O K)) = 0 := by
  obtain ⟨hxnorm, hxzero⟩ := hx
  have hf0 : PowerSeries.coeff 0 f = 0 := hf.1
  rw [iter_one] at hxzero
  have haevalP : Polynomial.aeval x P = 0 :=
    (eval_eq_zero_iff_aeval_eq_zero hOK hu heq hxnorm).mp hxzero
  have hPfact : P = Polynomial.X * P.divX := by
    have hXid := Polynomial.X_mul_divX_add P
    rw [coeff_zero_eq_zero_of_eq_mul hu heq hf0, Polynomial.C_0, add_zero] at hXid
    exact hXid.symm
  have hprod : x * Polynomial.aeval x P.divX = 0 := by
    rw [← haevalP]
    conv_rhs => rw [hPfact]
    rw [map_mul, Polynomial.aeval_X]
  rcases mul_eq_zero.mp hprod with hx0' | hQ0
  · exact absurd hx0' hx0
  · rw [Polynomial.aeval_map_algebraMap K x P.divX]; exact hQ0

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **A root of `Q := P.divX`'s image in `K` is nonzero**, at any field `K` satisfying
`[FaithfulSMul O K]` — not tied to a specific field such as `K_1 P`. `Q.coeff 0` is an associate of
the uniformizer `π ≠ 0` (`divX_isWeaklyEisensteinAt_and_associated`), and `algebraMap O K` is
injective, so `Q`'s image has nonzero constant term, hence `0` is not among its roots. Generalizes
`LubinTateSplittingFieldDegree.ne_zero_of_aeval_divX_map_eq_zero` (which fixes `K := K_1 P`) to an
arbitrary field, needed to run the same root-nonvanishing argument at `K := K_2` as well. -/
theorem ne_zero_of_root_of_aeval_divX_map_eq_zero {π : O} (hπ : Irreducible π) {f : O⟦X⟧}
    (hf : IsLubinTatePoly π (residueCard O) f) {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u)
    (heq : f = (P : O⟦X⟧) * u) (hPdist : P.IsDistinguishedAt (maximalIdeal O))
    (hPdeg : P.natDegree = residueCard O) {x : K}
    (hx : Polynomial.aeval x (P.divX.map (algebraMap O K)) = 0) : x ≠ 0 := by
  obtain ⟨-, -, -, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf.1 hf.2.1 hPdist (hPdeg ▸ two_le_residueCard)
  rintro rfl
  rw [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
    ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at hx
  have hQ0 : P.divX.coeff 0 = 0 := FaithfulSMul.algebraMap_injective O K (by rw [hx, map_zero])
  exact hπ.ne_zero ((associated_zero_iff_eq_zero π).mp (hQ0 ▸ hQ0assoc).symm)

/-- **`piTorsion hπ hf 1`, minus `0`, is exactly the set of roots of `Q := P.divX`'s image**, at any
field `K` satisfying the standing `hOK`/`hπnorm` hypotheses. Combines the two halves already proved
generically: `mem_piTorsion_one_of_root_divX_map` (a root of `Q`'s image is `π`-torsion) and
`aeval_divX_map_eq_zero_of_mem_piTorsion_one_ne_zero` (nonzero `π`-torsion is a root of `Q`'s image),
with `ne_zero_of_aeval_divX_map_eq_zero` supplying the "roots are automatically nonzero" half needed
to match up `piTorsion hπ hf 1 \ {0}` (not all of `piTorsion hπ hf 1`) with the root set. Reusable
verbatim at any two fields related by an algebra map that preserves `piTorsion` membership, which is
exactly what the `K_1 P → K_2` invariance argument (`ROADMAP.md` item 6) needs, instantiated once at
each end. -/
theorem piTorsion_one_sdiff_zero_eq_roots_toFinset [DecidableEq K]
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O) :
    (piTorsion (K := K) hπ hf 1 \ {0} : Set K) =
      ↑((P.divX.map (algebraMap O K)).roots.toFinset) := by
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  ext x
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_coe, Multiset.mem_toFinset,
    Polynomial.mem_roots']
  constructor
  · rintro ⟨hx, hx0⟩
    refine ⟨(divX_isWeaklyEisensteinAt_and_associated hu heq hf.1 hf.2.1 hPdist hPdeg2).1.map _
      |>.ne_zero, ?_⟩
    have haeval := aeval_divX_map_eq_zero_of_mem_piTorsion_one_ne_zero hOK hπ hf hu heq hx hx0
    rwa [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
      ← Polynomial.IsRoot.def] at haeval
  · rintro ⟨-, hroot⟩
    have hx : x ∈ (P.divX.map (algebraMap O K)).roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots']
      exact ⟨(divX_isWeaklyEisensteinAt_and_associated hu heq hf.1 hf.2.1 hPdist hPdeg2).1.map _
        |>.ne_zero, hroot⟩
    have haeval : Polynomial.aeval x (P.divX.map (algebraMap O K)) = 0 := by
      rw [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
      exact hroot
    exact ⟨mem_piTorsion_one_of_root_divX_map hOK hπ hπnorm hf hu heq hPdist hPdeg2 hx,
      ne_zero_of_root_of_aeval_divX_map_eq_zero hπ hf hu heq hPdist hPdeg haeval⟩

omit [Finite (ResidueField O)] in
/-- **The exact norm of a nonzero element of `piTorsion hπ hf 1`.** Combines
`aeval_divX_map_eq_zero_of_mem_piTorsion_one_ne_zero` (nonzero torsion is a root of `Q`'s image)
with `Polynomial.norm_eq_rpow_of_isEisensteinShape_of_root` (`Langlands.EisensteinRootNorm`, the
exact root-valuation fact for an Eisenstein-shaped polynomial) — every nonzero element of
`piTorsion hπ hf 1` has the *same* norm, `‖algebraMap O K π‖ ^ (1 / Q.natDegree : ℝ)`, no splitting
hypothesis needed. The load-bearing "same exact valuation" fact behind the minimum-spacing argument.

As with `norm_lt_one_of_aeval_divX_eq_zero`, the ultrametric route replaces the earlier
`spectralNorm`/irreducibility one and is what drops `[IsFractionRing O K]` here; the cost is that
`hπnorm` (`0 < c < 1`, needed for the Eisenstein polygon to have the right slope) becomes an
explicit hypothesis, where the `spectralNorm` route got it for free from `minpoly`. -/
theorem norm_eq_rpow_of_mem_piTorsion_one_ne_zero
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1)
    {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg2 : 2 ≤ P.natDegree)
    {x : K} (hx : x ∈ piTorsion (K := K) hπ hf 1) (hx0 : x ≠ 0) :
    ‖x‖ = ‖algebraMap O K π‖ ^ (1 / (P.divX.natDegree : ℝ)) := by
  have hf0 : PowerSeries.coeff 0 f = 0 := hf.1
  have hf1 : PowerSeries.coeff 1 f = π := hf.2.1
  have hα : Polynomial.aeval x (P.divX.map (algebraMap O K)) = 0 :=
    aeval_divX_map_eq_zero_of_mem_piTorsion_one_ne_zero hOK hπ hf hu heq hx hx0
  obtain ⟨hmonic, hdegpos, hdegeq, hc0, hc0eq, hweak⟩ :=
    isEisensteinShape_divX_map (K := K) hu heq hf0 hπ hf1 hPdist hPdeg2 hOK
  have hkey := Polynomial.norm_eq_rpow_of_isEisensteinShape_of_root hmonic hdegpos hπnorm hc0
    hc0eq hweak (by rw [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] at hα; exact hα)
  rwa [hdegeq] at hkey

/-- **The counting core: `Nat.card (piTorsion hπ hf 1) = residueCard O`, given `Q := P.divX`'s
image is separable and splits.** `piTorsion hπ hf 1` is exactly
`insert 0 (Q.map (algebraMap O K)).roots.toFinset` as a subset of `K` (`P = X * Q`,
`Polynomial.X_mul_divX_add`, so `aeval x P = x * aeval x Q`, vanishing iff `x = 0` or `x` is a root
of `Q`'s image; roots are automatically nonzero — `Q`'s constant term is an associate of `π ≠ 0` —
and automatically in the maximal ideal, `norm_lt_one_of_aeval_divX_eq_zero`). Counting: `0` is not
among `Q`'s roots, so the insert adds exactly one element to a set of size
`(Q.map (algebraMap O K)).natDegree = residueCard O - 1`
(`Polynomial.roots_toFinset_card_eq_natDegree_of_separable_of_splits`), giving `residueCard O`.

`hsep` is taken as a *hypothesis* rather than derived here, and `[IsFractionRing O K]` is
correspondingly absent: separability of `Q`'s image is proved over the *base* field via Gauss's
lemma + tame ramification (`separable_map_divX_of_isLubinTatePoly`), and then transported along a
field embedding (`Polynomial.Separable.map`) into whatever field actually contains the roots. That
splits the argument at exactly the point where the base field and the root-containing field stop
being the same — which is what `Langlands.LubinTateSplittingField.K_1` needs. See
`card_piTorsion_one_eq_residueCard` for the same-field corollary. -/
theorem card_piTorsion_one_eq_residueCard_of_separable_of_splits
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O)
    (hsep : (P.divX.map (algebraMap O K)).Separable)
    (hsplit : (P.divX.map (algebraMap O K)).Splits) :
    Nat.card (piTorsion (K := K) hπ hf 1) = residueCard O := by
  classical
  have hf0 : PowerSeries.coeff 0 f = 0 := hf.1
  have hf1 : PowerSeries.coeff 1 f = π := hf.2.1
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf0 hf1 hPdist hPdeg2
  have hQdegval : P.divX.natDegree = residueCard O - 1 := by
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hPdeg]
  have hQmapdeg : (P.divX.map (algebraMap O K)).natDegree = P.divX.natDegree :=
    hQmonic.natDegree_map _
  have hcard := Polynomial.roots_toFinset_card_eq_natDegree_of_separable_of_splits hsep hsplit
  rw [hQmapdeg, hQdegval] at hcard
  have hQcoeff0eq : (P.divX.map (algebraMap O K)).coeff 0 = algebraMap O K (P.divX.coeff 0) :=
    Polynomial.coeff_map _ _
  have hQ0ne : P.divX.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := hQ0assoc
    rw [h0, zero_mul] at hv
    exact hπ.ne_zero hv.symm
  have hQmapcoeff0ne : (P.divX.map (algebraMap O K)).coeff 0 ≠ 0 := by
    rw [hQcoeff0eq]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).mpr hQ0ne
  have hzero_not_root : (0 : K) ∉ (P.divX.map (algebraMap O K)).roots.toFinset := by
    simp only [Multiset.mem_toFinset, Polynomial.mem_roots']
    rintro ⟨-, hroot⟩
    exact hQmapcoeff0ne (by rw [Polynomial.coeff_zero_eq_eval_zero]; exact hroot)
  have hPfact : P = Polynomial.X * P.divX := by
    have hXid := Polynomial.X_mul_divX_add P
    rw [coeff_zero_eq_zero_of_eq_mul hu heq hf0, Polynomial.C_0, add_zero] at hXid
    exact hXid.symm
  set S : Finset K := insert (0 : K) (P.divX.map (algebraMap O K)).roots.toFinset with hSdef
  have hScard : S.card = residueCard O := by
    rw [hSdef, Finset.card_insert_of_notMem hzero_not_root, hcard]
    have h2 := two_le_residueCard (O := O); omega
  have hSmem : ∀ x : K, x ∈ S ↔ x ∈ piTorsion (K := K) hπ hf 1 := by
    intro x
    rw [hSdef, Finset.mem_insert]
    constructor
    · rintro (rfl | hx)
      · exact zero_mem_piTorsion hπ hf 1
      · exact mem_piTorsion_one_of_root_divX_map hOK hπ hπnorm hf hu heq hPdist hPdeg2 hx
    · rintro ⟨hxnorm, hxzero⟩
      rw [iter_one] at hxzero
      have haevalP : Polynomial.aeval x P = 0 :=
        (eval_eq_zero_iff_aeval_eq_zero hOK hu heq hxnorm).mp hxzero
      have hprod : x * Polynomial.aeval x P.divX = 0 := by
        rw [← haevalP]
        conv_rhs => rw [hPfact]
        rw [map_mul, Polynomial.aeval_X]
      rcases mul_eq_zero.mp hprod with hx0 | hQ0
      · exact Or.inl hx0
      · refine Or.inr ?_
        have haevalQ : Polynomial.aeval x (P.divX.map (algebraMap O K)) = 0 := by
          rw [Polynomial.aeval_map_algebraMap K x P.divX]
          exact hQ0
        have hroot : Polynomial.eval x (P.divX.map (algebraMap O K)) = 0 := by
          rw [← Polynomial.eval₂_id (p := P.divX.map (algebraMap O K)) (x := x),
            ← Algebra.algebraMap_self (R := K), ← Polynomial.aeval_def]
          exact haevalQ
        rw [Multiset.mem_toFinset, Polynomial.mem_roots']
        exact ⟨(hQmonic.map _).ne_zero, hroot⟩
  rw [← hScard]
  exact Nat.subtype_card S hSmem

/-- **⚠️ VACUOUS whenever `residueCard O ≥ 3` — see this file's module docstring.** The
same-ambient-field corollary of `card_piTorsion_one_eq_residueCard_of_separable_of_splits`:
with `[IsFractionRing O K]`, separability of `Q`'s image comes from
`separable_map_of_isWeaklyEisensteinAt_associated` (Gauss's lemma over `K = Frac(O)` plus tame
ramification), fed a root extracted from `hsplit` itself. But `hsplit` and `[IsFractionRing O K]`
are jointly unsatisfiable for `residueCard O ≥ 3` (`Langlands.LubinTateHsplitVacuity`), so this
statement has no non-degenerate instantiation. Retained only because it is what the pre-existing
`LubinTateRootCountConcrete`/`LubinTateResidueUnitsTransitivity` callers cite; new work should use
the `_of_separable_of_splits` form above, at a field where `Q` genuinely splits. -/
theorem card_piTorsion_one_eq_residueCard [IsFractionRing O K]
    (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπnorm : ‖algebraMap O K π‖ < 1) {f : O⟦X⟧} (hf : IsLubinTatePoly π (residueCard O) f)
    {P : O[X]} {u : O⟦X⟧} (hu : IsUnit u) (heq : f = (P : O⟦X⟧) * u)
    (hPdist : P.IsDistinguishedAt (maximalIdeal O)) (hPdeg : P.natDegree = residueCard O)
    (hsplit : (P.divX.map (algebraMap O K)).Splits) :
    Nat.card (piTorsion (K := K) hπ hf 1) = residueCard O := by
  have hf0 : PowerSeries.coeff 0 f = 0 := hf.1
  have hf1 : PowerSeries.coeff 1 f = π := hf.2.1
  have hPdeg2 : 2 ≤ P.natDegree := hPdeg ▸ two_le_residueCard
  obtain ⟨hQmonic, hQweak, hQdeg, hQ0assoc⟩ :=
    divX_isWeaklyEisensteinAt_and_associated hu heq hf0 hf1 hPdist hPdeg2
  have hQn1 : P.divX.natDegree + 1 = residueCard O := by
    have hQdegval : P.divX.natDegree = residueCard O - 1 := by
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hPdeg]
    have h2 := two_le_residueCard (O := O); omega
  have hQn : IsUnit ((P.divX.natDegree : O)) := isUnit_natCast_of_add_one_eq_residueCard hQn1
  have hQmapdeg : (P.divX.map (algebraMap O K)).natDegree = P.divX.natDegree :=
    hQmonic.natDegree_map _
  have hQmapdegne : (P.divX.map (algebraMap O K)).degree ≠ 0 :=
    (Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [hQmapdeg]; exact hQdeg)).ne'
  obtain ⟨a0, ha0⟩ := hsplit.exists_eval_eq_zero hQmapdegne
  have ha0' : Polynomial.aeval a0 (P.divX.map (algebraMap O K)) = 0 := by
    rw [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
    exact ha0
  have hsep : (P.divX.map (algebraMap O K)).Separable :=
    separable_map_of_isWeaklyEisensteinAt_associated hOK hπ hπnorm hQmonic hQweak hQdeg hQ0assoc
      hQn (L := K) ha0'
  exact card_piTorsion_one_eq_residueCard_of_separable_of_splits hOK hπ hπnorm hf hu heq hPdist
    hPdeg hsep hsplit

end LubinTate
