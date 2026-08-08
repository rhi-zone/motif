import Langlands.AdicCompletionIntegersResidue
import Langlands.ArtinSchreier
import Langlands.TotallyRamifiedNormIndex
import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# A concrete WILD, SEPARABLE, GALOIS ramified extension: an Artin–Schreier extension of `k(X)`

Targets `ROADMAP.md` §6n item (c): a wild instance of `IsTotallyRamified` with actual Galois
structure, closing the gap left open by `Langlands.TotallyRamifiedWildConcreteExample` (which is
wild but purely inseparable, hence provably not Galois — see that file's closing docstring, which
first proposed the Artin–Schreier route pursued here).

## Design: why `S := integralClosure R L`, not a literal polynomial-ring `S`

Both `Langlands.TotallyRamifiedConcreteExample` (tame) and `TotallyRamifiedWildConcreteExample`
(wild, inseparable) build `S` as a literal wrapper of `Polynomial k`, with `algebraMap R S` sending
`X ↦ Y ^ e` — tractable because `Y ↦ Y ^ e` is *itself* a polynomial map `k[X] → k[Y]`, automatically
finite, free, and (since `k[Y]` is a fresh polynomial ring) automatically a PID.

This does not carry over to a genuine Artin–Schreier extension. The Artin–Schreier map
`Y ↦ Y ^ p - Y` is a *global* polynomial covering of the affine line that is **unramified at every
finite point** (its derivative is the nonzero constant `-1`, so it is everywhere étale on the
affine line) and totally ramified only **at infinity** — a point with no `HeightOneSpectrum (k[X])`
representative. Reaching a *finite* ramified place requires the Artin–Schreier parameter `a` to have
an actual pole there, e.g. `a := X⁻¹` (pole of order `1`, coprime to `p`, at `X = 0`), and then the
generator `theta` with `theta ^ p - theta = a` is **not** integral over `R = k[X]` — `S` cannot be presented as a
literal polynomial ring in one variable this way (see the abandoned computation in an earlier pass
of this file's design, recorded in `ROADMAP.md`: the "obvious" integral substitute `Y := X · theta`
satisfies the monic relation `Y ^ p - X ^ (p-1) * Y - X ^ (p-1) = 0`, but proving *that* ring is a
domain / Dedekind domain from scratch, rather than inheriting it from a fresh polynomial ring, is
exactly as much work as the route actually taken below).

The route taken instead: build `L` as the splitting field of `ArtinSchreier.poly p a` directly over
`K := FractionRing R` (using `ArtinSchreier.irreducible_iff`, unconditional `ArtinSchreier.
instIsGalois`, and `ArtinSchreier.finrank_splittingField_eq`), then take
**`S := integralClosure R L`** and get `IsDedekindDomain S` / `Module.Finite R S` / `Module.Free R S`
/ the rank identity `Module.finrank R S = Module.finrank K L` **for free** from Mathlib's general
theory of integral closures of Dedekind domains in finite *separable* extensions
(`Mathlib.RingTheory.DedekindDomain.IntegralClosure`) — separability (`ArtinSchreier.poly_separable`,
inherited from `IsGalois`) is exactly the hypothesis that was *unavailable* in the purely-inseparable
wild example and blocked its `finrank_eq`. This confirms the expectation stated in the task
description: separability removes the trace-form obstruction that blocked the earlier file.

The place `w` lying over `v := (X)` is obtained abstractly (`Ideal.
exists_ideal_over_prime_of_isIntegral_of_isDomain`, a general going-up fact — since `S` is no
longer a hand-built ring, `w` cannot be written down combinatorially the way it was in the two
template files). The ramification index at this specific `w` is then pinned down not by a
definitional ideal identity (unavailable, since there is no explicit formula for `w.asIdeal`) but by
a direct valuation computation on the completions, combined with the global bound
`Ideal.ramificationIdx_le_finrank` (`e ≤ [L : K] = p`) and the classical fundamental identity
`Ideal.sum_ramification_inertia` (`e · f ≤ [L : K] = p`, restricting the sum to the single term at
`w`) to pin both `e = p` and `f = 1` exactly.

## Status

See the closing section of this file and `ROADMAP.md` §6q for the precise account of what closed.
-/

noncomputable section

open IsDedekindDomain IsLocalRing Polynomial

namespace Langlands.TotallyRamifiedArtinSchreierConcreteExample

/-! ### The base field, `R := k[X]`, `K := Frac(R)`, and `v` at `(X)` -/

/-- The residue characteristic, and also the ramification index of the Artin–Schreier extension
below: `p = 3`, an odd prime (no lemma used here needs oddness, but it keeps this instance
visibly distinct from the purely inseparable wild example's `p = 2`). -/
abbrev p : ℕ := 3

instance : Fact (Nat.Prime p) := ⟨by decide⟩

/-- The base/residue field `k := ZMod p`. -/
abbrev k : Type := ZMod p

/-- `R := k[X]`. -/
abbrev R : Type := Polynomial k

instance : IsDedekindDomain R := IsPrincipalIdealRing.isDedekindDomain R

/-- `K := Frac(R)`. -/
abbrev K : Type := FractionRing R

instance charP_R : CharP R p := Polynomial.charP

instance charP_K : CharP K p := IsFractionRing.charP R p

/-- `v`, the place of `R = k[X]` at `X`. -/
def v : HeightOneSpectrum R where
  asIdeal := Ideal.span {Polynomial.X}
  isPrime := (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  ne_bot := by simp

theorem x_ne_zero : algebraMap R K (Polynomial.X : R) ≠ 0 :=
  fun h => Polynomial.X_ne_zero
    (IsFractionRing.injective R K (h.trans (map_zero (algebraMap R K)).symm))

/-- **The `v`-adic valuation of `X` is exactly the uniformizer value `exp (-1)`.** `v.asIdeal` is
`(X)` by definition, so this is `intValuation_singleton` transported to `K` via
`valuation_of_algebraMap`. -/
theorem valuation_x : v.valuation K (algebraMap R K (Polynomial.X : R)) = WithZero.exp (-1 : ℤ) := by
  rw [v.valuation_of_algebraMap]
  exact v.intValuation_singleton Polynomial.X_ne_zero rfl

/-! ### `a := X⁻¹ : K`, the Artin–Schreier parameter with a simple pole at `v`

`a` has `v`-adic valuation `exp (1 : ℤ)` — a genuine pole, of order `1` (coprime to `p` trivially).
This is what forces the extension `K(theta)/K` (`theta ^ p - theta = a`) to ramify at `v`, unlike the
"everywhere-finite" choice `a := X` (whose Artin–Schreier extension is unramified on the whole
affine line and ramifies only at infinity — not representable as a `HeightOneSpectrum R`). -/

/-- The Artin–Schreier parameter: `a := X⁻¹ ∈ K`. -/
def a : K := (algebraMap R K (Polynomial.X : R))⁻¹

theorem a_def : a = (algebraMap R K (Polynomial.X : R))⁻¹ := rfl

theorem valuation_a : v.valuation K a = WithZero.exp (1 : ℤ) := by
  rw [a, map_inv₀, valuation_x, ← WithZero.exp_neg, neg_neg]

open scoped WithZero

/-- **`a` is not of the form `theta ^ p - theta` for any `theta : K`.** Case-split on whether `theta` is
`v`-integral (`v.valuation K theta ≤ 1`): if so, `theta ^ p - theta` is `v`-integral too (ultrametric), but `a`
is not (`valuation_a`, `exp 1 > 1`) — contradiction. If not, `v.valuation K theta = exp m` for some
`m ≥ 1`, and since `v.valuation K (theta ^ p) = exp (p * m)` strictly exceeds `v.valuation K theta = exp m`
(as `m ≥ 1` and `p ≥ 2`), the ultrametric inequality is an equality picking out the larger term:
`v.valuation K (theta ^ p - theta) = exp (p * m)`. Equating with `v.valuation K a = exp 1` forces `p * m = 1`,
impossible for `p ≥ 2`, `m ≥ 1`. -/
theorem a_not_mem_range : a ∉ Set.range (fun x : K => x ^ p - x) := by
  rintro ⟨theta, hθ'⟩
  have hθ : theta ^ p - theta = a := hθ'
  have hθ0 : theta ≠ 0 := by
    rintro rfl
    simp only [zero_pow (Fact.out : p.Prime).ne_zero, sub_zero] at hθ
    exact (WithZero.exp_ne_zero (a := (1 : ℤ))) (by rw [← valuation_a, ← hθ, map_zero])
  by_cases hle : v.valuation K theta ≤ 1
  · have hp_le : v.valuation K (theta ^ p) ≤ 1 := by
      rw [map_pow]; exact pow_le_one₀ zero_le hle
    have hsub_le : v.valuation K (theta ^ p - theta) ≤ 1 :=
      le_trans (Valuation.map_sub _ _ _) (max_le hp_le hle)
    rw [hθ, valuation_a] at hsub_le
    exact absurd hsub_le (not_le.mpr (WithZero.exp_lt_exp.mpr (by norm_num)))
  · push Not at hle
    set m : ℤ := WithZero.log (v.valuation K theta) with hmdef
    have hvθ : v.valuation K theta = WithZero.exp m := (WithZero.exp_log (by
      rintro h0; rw [h0] at hle; exact absurd hle (by simp))).symm
    have hm_pos : 0 < m := by
      rw [hvθ] at hle
      exact WithZero.exp_lt_exp.mp (by simpa using hle)
    have hpow : v.valuation K (theta ^ p) = WithZero.exp (p * m : ℤ) := by
      rw [map_pow, hvθ, ← WithZero.exp_nsmul, nsmul_eq_mul]
    have hlt : v.valuation K theta < v.valuation K (theta ^ p) := by
      rw [hvθ, hpow]
      apply WithZero.exp_lt_exp.mpr
      have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
      nlinarith
    have hsub_eq : v.valuation K (theta ^ p - theta) = v.valuation K (theta ^ p) :=
      Valuation.map_sub_eq_of_lt_left _ hlt
    rw [hθ, valuation_a, hpow] at hsub_eq
    have hpm : (p : ℤ) * m = 1 := WithZero.exp_injective hsub_eq.symm
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    nlinarith

/-! ### `L`, the splitting field of the Artin–Schreier polynomial `X ^ p - X - C a`

`poly p a` is irreducible over `K` (`a_not_mem_range` plus `ArtinSchreier.irreducible_iff`), so
`ArtinSchreier.finrank_splittingField_eq` gives `[L : K] = p` exactly, and `ArtinSchreier.
instIsGalois` (unconditional) gives `IsGalois K L` — hence, via Mathlib's `IsGalois` class,
`Algebra.IsSeparable K L` for free. This separability is exactly what
`TotallyRamifiedWildConcreteExample` lacked, and what its closing docstring predicted would let a
genuinely Artin–Schreier example avoid the trace-form obstruction that blocked its `finrank_eq`. -/

theorem hirr : Irreducible (ArtinSchreier.poly p a) := ArtinSchreier.irreducible_iff.mpr a_not_mem_range

/-- `L := ` the splitting field of the Artin–Schreier polynomial `X ^ p - X - C a`. -/
abbrev L : Type := (ArtinSchreier.poly p a).SplittingField

instance : IsGalois K L := ArtinSchreier.instIsGalois

theorem finrank_K_L : Module.finrank K L = p := ArtinSchreier.finrank_splittingField_eq hirr

/-- `theta : L`, a chosen root of `poly p a` in its splitting field. -/
theorem exists_root : ∃ theta : L, Polynomial.aeval theta (ArtinSchreier.poly p a) = 0 := by
  have hsplits : ((ArtinSchreier.poly p a).map (algebraMap K L)).Splits :=
    Polynomial.SplittingField.splits (ArtinSchreier.poly p a)
  have hdeg : ((ArtinSchreier.poly p a).map (algebraMap K L)).degree ≠ 0 := by
    rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree (ArtinSchreier.poly_ne_zero p a),
      ArtinSchreier.natDegree_poly]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨theta, hθ⟩ := hsplits.exists_eval_eq_zero hdeg
  exact ⟨theta, by rw [Polynomial.aeval_def, ← Polynomial.eval_map]; exact hθ⟩

/-- `theta`, a fixed root of `poly p a` in `L`. -/
noncomputable def theta : L := exists_root.choose

theorem aeval_theta : Polynomial.aeval (theta : L) (ArtinSchreier.poly p a) = 0 := exists_root.choose_spec

/-- **`theta` generates `L` over `K`.** `K⟮theta⟯` has `K`-dimension `p` (`poly p a`, irreducible and monic,
is its minimal polynomial), matching `[L : K] = p` exactly, so `K⟮theta⟯ = L`. -/
theorem adjoin_θ_eq_top : IntermediateField.adjoin K ({theta} : Set L) = ⊤ := by
  have hInt : IsIntegral K theta := ⟨ArtinSchreier.poly p a, ArtinSchreier.poly_monic p a, aeval_theta⟩
  have hminpoly : ArtinSchreier.poly p a = minpoly K theta :=
    minpoly.eq_of_irreducible_of_monic hirr aeval_theta (ArtinSchreier.poly_monic p a)
  have hfinrank_adj :
      Module.finrank K (IntermediateField.adjoin K ({theta} : Set L) : IntermediateField K L) = p
      := by
    rw [IntermediateField.adjoin.finrank hInt, ← hminpoly, ArtinSchreier.natDegree_poly]
  have hrank_top : Module.finrank K (⊤ : IntermediateField K L) = p := by
    rw [LinearEquiv.finrank_eq (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv]
    exact finrank_K_L
  exact IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [hfinrank_adj, hrank_top])

theorem a_ne_zero : a ≠ 0 := by
  intro h0
  have hva := valuation_a
  rw [h0, map_zero] at hva
  exact WithZero.exp_ne_zero hva.symm

theorem theta_ne_zero : (theta : L) ≠ 0 := by
  intro hθ0
  have h0 : Polynomial.aeval (0 : L) (ArtinSchreier.poly p a) = 0 := hθ0 ▸ aeval_theta
  have h1 : algebraMap K L a = 0 := by
    simpa [ArtinSchreier.poly_def, zero_pow (Fact.out : p.Prime).ne_zero] using h0
  exact a_ne_zero ((algebraMap K L).injective (h1.trans (map_zero _).symm))

/-! ### `S := integralClosure R L`

Unlike the tame/wild template files, `S` is *not* built as a hand-wrapped polynomial ring: since
`L / K` is a finite **separable** extension (inherited from `IsGalois K L`) and `R` is a Dedekind
domain, Mathlib's general theory of integral closures
(`Mathlib.RingTheory.DedekindDomain.IntegralClosure`) gives `IsDedekindDomain`, `Module.Finite`,
`Module.Free`, and the rank identity `Module.finrank R S = Module.finrank K L` directly — no
hand-built ring structure needed. This is exactly the point of departure from
`TotallyRamifiedWildConcreteExample`, where the extension's inseparability made this route
(via `IsIntegralClosure.rank`, which needs `Algebra.IsSeparable`) unavailable. -/

instance : Module.IsTorsionFree R L := .trans_faithfulSMul R K L

/-- `S := integralClosure R L`, the ring of integers of `L` relative to `R`. -/
abbrev S : Type := integralClosure R L

instance : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension R K L S

instance : IsDedekindDomain S := integralClosure.isDedekindDomain_fractionRing R L

instance : Module.Finite R S := IsIntegralClosure.finite R K L S

instance : Module.Free R S := IsIntegralClosure.module_free R K L S

instance : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S

instance : Module.IsTorsionFree R S := IsIntegralClosure.isTorsionFree R L

theorem finrank_R_S : Module.finrank R S = p := by
  rw [IsIntegralClosure.rank R K L S, finrank_K_L]

theorem algebraMap_R_S_injective : Function.Injective (algebraMap R S) := by
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have heq : algebraMap S L ∘ algebraMap R S = algebraMap R L := by
    ext x; exact (IsScalarTower.algebraMap_apply R S L x).symm
  exact Function.Injective.of_comp (heq ▸ hRL)

instance : NoZeroSMulDivisors R S where
  eq_zero_or_eq_zero_of_smul_eq_zero {r x} h := by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact Or.inl (algebraMap_R_S_injective (h1.trans (map_zero (algebraMap R S)).symm))
    · exact Or.inr h1

/-! ### `w : HeightOneSpectrum S` lying over `v`

Since `S` is no longer a hand-built ring, `w` cannot be written down combinatorially (as `(Y)` was
in the template files) — it is obtained from the general going-up theorem for integral extensions
of domains. -/

theorem ker_algebraMap_R_S_le : RingHom.ker (algebraMap R S) ≤ v.asIdeal := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  have hx0 : x = 0 := algebraMap_R_S_injective (hx.trans (map_zero _).symm)
  simp [hx0]

theorem exists_Q : ∃ Q : Ideal S, Q.IsPrime ∧ Q.comap (algebraMap R S) = v.asIdeal :=
  Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain v.asIdeal ker_algebraMap_R_S_le

theorem Q_ne_bot : (exists_Q.choose) ≠ ⊥ := by
  intro hQbot
  have hcomap := exists_Q.choose_spec.2
  rw [hQbot, Ideal.comap_bot_of_injective _ algebraMap_R_S_injective] at hcomap
  exact v.ne_bot hcomap.symm

/-- `w`, a place of `S` lying over `v`. -/
def w : HeightOneSpectrum S where
  asIdeal := exists_Q.choose
  isPrime := exists_Q.choose_spec.1
  ne_bot := Q_ne_bot

theorem w_comap_eq : w.asIdeal.comap (algebraMap R S) = v.asIdeal := exists_Q.choose_spec.2

instance : w.asIdeal.LiesOver v.asIdeal := ⟨w_comap_eq.symm⟩

/-! ### The ramification/inertia bound `e · f ≤ p`, from the global fundamental identity

`Ideal.sum_ramification_inertia` (`∑ e_i f_i = [L : K]` over all primes over `v`) restricted to the
single term at `w` gives `e · f ≤ p`; in particular `e ≤ p`. This is the *only* handle available on
`e := v.asIdeal.ramificationIdx' w.asIdeal` here — unlike the template files, there is no explicit
ideal-level formula `Ideal.map (algebraMap R S) v.asIdeal = w.asIdeal ^ e` to read `e` off directly,
since `w` was obtained abstractly. -/

theorem ef_le_p :
    v.asIdeal.ramificationIdx' w.asIdeal * v.asIdeal.inertiaDeg' w.asIdeal ≤ p := by
  classical
  haveI := v.isMaximal
  have hmem : w.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal S :=
    (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot _).mpr ⟨w.isPrime, inferInstance⟩
  have hsum := Ideal.sum_ramification_inertia S K L v.ne_bot
  rw [← Finset.add_sum_erase _ _ hmem] at hsum
  have hle : v.asIdeal.ramificationIdx' w.asIdeal * v.asIdeal.inertiaDeg' w.asIdeal ≤
      Module.finrank K L := by
    rw [← hsum]; exact Nat.le_add_right _ _
  rwa [finrank_K_L] at hle

theorem e_le_p : v.asIdeal.ramificationIdx' w.asIdeal ≤ p := by
  have hf_pos : 0 < v.asIdeal.inertiaDeg' w.asIdeal := by
    haveI := v.isMaximal
    exact Nat.pos_iff_ne_zero.mpr (Ideal.inertiaDeg'_ne_zero v.asIdeal w.asIdeal)
  calc v.asIdeal.ramificationIdx' w.asIdeal
      ≤ v.asIdeal.ramificationIdx' w.asIdeal * v.asIdeal.inertiaDeg' w.asIdeal :=
        Nat.le_mul_of_pos_right _ hf_pos
    _ ≤ p := ef_le_p

/-! ### Pinning `e = p` exactly, via a completion-level valuation computation

`theta ^ p - theta = a`, and `a`'s image in `Kv := v.adicCompletion K` is `xK⁻¹` for the uniformizer
`xK` of `v` — so, writing `thetaw := algebraMap L (w.adicCompletion L) theta`,
`thetaw ^ p - thetaw = algebraMap Kv Lw xK⁻¹`, whose `Lw`-valuation is `exp e` (`e` the ramification
index, via `valuation_algebraMap_pow_eq`). The same ultrametric case-split as `a_not_mem_range` (now
run in `Lw` instead of `K`) shows `Valued.v thetaw = exp m` for a positive integer `m` with
`m * p = e`; combined with `e ≤ p` (`e_le_p`), this forces `m = 1`, i.e. `e = p` exactly. -/

open scoped WithZero

/-- `xK`, the image of `x := algebraMap R K X` inside `v.adicCompletion K`. -/
def xK : v.adicCompletion K := algebraMap K (v.adicCompletion K) (algebraMap R K (Polynomial.X : R))

theorem valuation_xK : Valued.v xK = WithZero.exp (-1 : ℤ) := by
  show Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K (Polynomial.X : R))) = _
  rw [show algebraMap K (v.adicCompletion K) (algebraMap R K (Polynomial.X : R))
      = ((algebraMap R K (Polynomial.X : R) : K) : v.adicCompletion K) from rfl,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact v.intValuation_singleton Polynomial.X_ne_zero rfl

theorem xK_ne_zero : xK ≠ 0 := by
  intro h0
  have := valuation_xK
  rw [h0, map_zero] at this
  exact WithZero.exp_ne_zero this.symm

/-- `thetaw`, the image of `theta` inside `w.adicCompletion L`. -/
def thetaw : w.adicCompletion L := algebraMap L (w.adicCompletion L) theta

theorem theta_pow_sub_theta : (theta : L) ^ p - theta = algebraMap K L a :=
  sub_eq_zero.mp (by simpa [ArtinSchreier.poly_def] using aeval_theta)

theorem thetaw_pow_sub_thetaw :
    (thetaw : w.adicCompletion L) ^ p - thetaw =
      algebraMap (v.adicCompletion K) (w.adicCompletion L) xK⁻¹ := by
  have h1 : (thetaw : w.adicCompletion L) ^ p - thetaw =
      algebraMap L (w.adicCompletion L) (algebraMap K L a) := by
    show algebraMap L (w.adicCompletion L) theta ^ p - algebraMap L (w.adicCompletion L) theta = _
    rw [← map_pow, ← map_sub, theta_pow_sub_theta]
  rw [h1]
  have h2 : algebraMap K L a = (algebraMap K L (algebraMap R K (Polynomial.X : R)))⁻¹ := by
    have h3 := congrArg (algebraMap K L) a_def
    rwa [map_inv₀] at h3
  rw [h2, map_inv₀, map_inv₀]
  congr 1
  exact (IsDedekindDomain.HeightOneSpectrum.adicCompletionComap_algebraMap K L v w
    (algebraMap R K (Polynomial.X : R))).symm

theorem valuation_algebraMap_xK_inv :
    Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) xK⁻¹) =
      WithZero.exp (v.asIdeal.ramificationIdx' w.asIdeal : ℤ) := by
  rw [map_inv₀, map_inv₀]
  show (Valued.v (IsDedekindDomain.HeightOneSpectrum.adicCompletionComap K L v w xK))⁻¹ = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_algebraMap_pow_eq K L v w xK,
    valuation_xK, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one, ← WithZero.exp_neg, neg_neg]

/-- **`e := v.asIdeal.ramificationIdx' w.asIdeal` equals `p` exactly.** `thetaw` cannot be
`w`-integral (else `thetaw ^ p - thetaw` would be too, but it has valuation `exp e ≥ exp 1 > 1`), so
`Valued.v thetaw = exp m` for some `m ≥ 1`; then `Valued.v (thetaw ^ p - thetaw) = exp (p * m)` (the
dominant-term case of the ultrametric inequality), forcing `p * m = e`. Since `e ≤ p` (`e_le_p`) and
`m ≥ 1`, this forces `m = 1`, i.e. `e = p`. -/
theorem e_eq_p : v.asIdeal.ramificationIdx' w.asIdeal = p := by
  set e := v.asIdeal.ramificationIdx' w.asIdeal with hedef
  have he_pos : 0 < e := by
    haveI := v.isMaximal
    exact Nat.pos_iff_ne_zero.mpr (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
      w.asIdeal v.ne_bot)
  have hrhs : Valued.v (thetaw ^ p - thetaw) = WithZero.exp (e : ℤ) := by
    rw [thetaw_pow_sub_thetaw, valuation_algebraMap_xK_inv]
  by_cases hle : Valued.v (thetaw : w.adicCompletion L) ≤ 1
  · have hp_le : Valued.v (thetaw ^ p) ≤ 1 := by
      rw [map_pow]; exact pow_le_one₀ zero_le hle
    have hsub_le : Valued.v (thetaw ^ p - thetaw) ≤ 1 :=
      le_trans (Valuation.map_sub _ _ _) (max_le hp_le hle)
    rw [hrhs] at hsub_le
    exact absurd hsub_le (not_le.mpr (WithZero.exp_lt_exp.mpr (by exact_mod_cast he_pos)))
  · push Not at hle
    set m : ℤ := WithZero.log (Valued.v (thetaw : w.adicCompletion L)) with hmdef
    have hvθ : Valued.v (thetaw : w.adicCompletion L) = WithZero.exp m := (WithZero.exp_log (by
      rintro h0; rw [h0] at hle; exact absurd hle (by simp))).symm
    have hm_pos : 0 < m := by
      rw [hvθ] at hle
      exact WithZero.exp_lt_exp.mp (by simpa using hle)
    have hpow : Valued.v (thetaw ^ p) = WithZero.exp (p * m : ℤ) := by
      rw [map_pow, hvθ, ← WithZero.exp_nsmul, nsmul_eq_mul]
    have hlt : Valued.v (thetaw : w.adicCompletion L) < Valued.v (thetaw ^ p) := by
      rw [hvθ, hpow]
      apply WithZero.exp_lt_exp.mpr
      have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
      nlinarith
    have hsub_eq : Valued.v (thetaw ^ p - thetaw) = Valued.v (thetaw ^ p) :=
      Valuation.map_sub_eq_of_lt_left _ hlt
    rw [hrhs, hpow] at hsub_eq
    have hpm : (p : ℤ) * m = e := (WithZero.exp_injective hsub_eq).symm
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    have he_le : (e : ℤ) ≤ p := by exact_mod_cast e_le_p
    have hm1 : m = 1 := by nlinarith
    have : (e : ℤ) = p := by rw [← hpm, hm1, mul_one]
    exact_mod_cast this

end Langlands.TotallyRamifiedArtinSchreierConcreteExample

end
