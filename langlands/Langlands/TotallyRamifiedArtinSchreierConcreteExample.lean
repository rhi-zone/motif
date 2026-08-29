import Langlands.AdicCompletionIntegersResidue
import Langlands.AdicCompletionIntegralClosure
import Langlands.AdicCompletionPrimitiveElementDegree
import Langlands.ArtinSchreier
import Langlands.TotallyRamifiedNormIndex
import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# A concrete WILD, SEPARABLE, GALOIS ramified extension: an Artin–Schreier extension of `k(X)`

A wild instance of `IsTotallyRamified` with actual Galois structure, filling the gap left by
`Langlands.TotallyRamifiedWildConcreteExample` (which is wild but purely inseparable, hence
provably not Galois).

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
literal polynomial ring in one variable this way. (The "obvious" integral substitute
`Y := X · theta` satisfies the monic relation `Y ^ p - X ^ (p-1) * Y - X ^ (p-1) = 0`, but proving
*that* ring is a domain / Dedekind domain from scratch, rather than inheriting it from a fresh
polynomial ring, is exactly as much work as the route actually taken below.)

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

See the closing section of this file for the precise statement proved.
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

/-- **`e := v.asIdeal.ramificationIdx' w.asIdeal` equals `p` exactly, and `Valued.v thetaw = exp
1`.** `thetaw` cannot be `w`-integral (else `thetaw ^ p - thetaw` would be too, but it has valuation
`exp e ≥ exp 1 > 1`), so `Valued.v thetaw = exp m` for some `m ≥ 1`; then `Valued.v (thetaw ^ p -
thetaw) = exp (p * m)` (the dominant-term case of the ultrametric inequality), forcing `p * m = e`.
Since `e ≤ p` (`e_le_p`) and `m ≥ 1`, this forces `m = 1`, i.e. `e = p` — and, as a byproduct,
`thetaw` itself has valuation exactly `exp 1` (a genuine simple pole at `w`, so `thetaw⁻¹` is a
uniformizer — used below for field 1). -/
theorem e_eq_p_and_valuation_thetaw :
    v.asIdeal.ramificationIdx' w.asIdeal = p ∧
      Valued.v (thetaw : w.adicCompletion L) = WithZero.exp (1 : ℤ) := by
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
    have he_eq : (e : ℤ) = p := by rw [← hpm, hm1, mul_one]
    exact ⟨by exact_mod_cast he_eq, by rw [hvθ, hm1]⟩

theorem e_eq_p : v.asIdeal.ramificationIdx' w.asIdeal = p := e_eq_p_and_valuation_thetaw.1

theorem valuation_thetaw : Valued.v (thetaw : w.adicCompletion L) = WithZero.exp (1 : ℤ) :=
  e_eq_p_and_valuation_thetaw.2

/-! ### `Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)`, and `finrank Kv Lw = p`

Needed as an explicit hypothesis by `Langlands.AdicCompletionIntegralClosure`'s
`instModuleFiniteAdicCompletionIntegers` / `instModuleFreeAdicCompletionIntegers` (it is *not*
derived automatically from the global `Algebra.IsSeparable K L`). Built exactly as in
`TotallyRamifiedConcreteExample`: `gPoly := ArtinSchreier.poly p (algebraMap K Kv a)` is irreducible
(the same ultrametric argument as `a_not_mem_range`, run in `Kv` via `Valued.v`), hence *is*
`minpoly Kv thetaw`, pinning `finrank Kv Kv⟮thetaw⟯ = p` exactly; combined with the density argument
`Kv⟮thetaw⟯ = ⊤` this gives `finrank Kv Lw = p`. Separability of `gPoly` itself is free
(`ArtinSchreier.poly_separable`), transporting to `Algebra.IsSeparable Kv Lw` the same way. -/

theorem algebraMap_K_Kv_a_eq : algebraMap K (v.adicCompletion K) a = xK⁻¹ := by
  have h3 := congrArg (algebraMap K (v.adicCompletion K)) a_def
  rwa [map_inv₀] at h3

theorem xK_inv_not_mem_range :
    xK⁻¹ ∉ Set.range (fun x : v.adicCompletion K => x ^ p - x) := by
  rintro ⟨θ, hθ'⟩
  have hθ : θ ^ p - θ = xK⁻¹ := hθ'
  have hxK_val : Valued.v (xK⁻¹ : v.adicCompletion K) = WithZero.exp (1 : ℤ) := by
    rw [map_inv₀, valuation_xK, ← WithZero.exp_neg, neg_neg]
  by_cases hle : Valued.v θ ≤ 1
  · have hp_le : Valued.v (θ ^ p) ≤ 1 := by
      rw [map_pow]; exact pow_le_one₀ zero_le hle
    have hsub_le : Valued.v (θ ^ p - θ) ≤ 1 :=
      le_trans (Valuation.map_sub _ _ _) (max_le hp_le hle)
    rw [hθ, hxK_val] at hsub_le
    exact absurd hsub_le (not_le.mpr (WithZero.exp_lt_exp.mpr (by norm_num)))
  · push Not at hle
    set m : ℤ := WithZero.log (Valued.v θ) with hmdef
    have hvθ : Valued.v θ = WithZero.exp m := (WithZero.exp_log (by
      rintro h0; rw [h0] at hle; exact absurd hle (by simp))).symm
    have hm_pos : 0 < m := by
      rw [hvθ] at hle
      exact WithZero.exp_lt_exp.mp (by simpa using hle)
    have hpow : Valued.v (θ ^ p) = WithZero.exp (p * m : ℤ) := by
      rw [map_pow, hvθ, ← WithZero.exp_nsmul, nsmul_eq_mul]
    have hlt : Valued.v θ < Valued.v (θ ^ p) := by
      rw [hvθ, hpow]
      apply WithZero.exp_lt_exp.mpr
      have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
      nlinarith
    have hsub_eq : Valued.v (θ ^ p - θ) = Valued.v (θ ^ p) :=
      Valuation.map_sub_eq_of_lt_left _ hlt
    rw [hθ, hxK_val, hpow] at hsub_eq
    have hpm : (p : ℤ) * m = 1 := WithZero.exp_injective hsub_eq.symm
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    nlinarith

instance charP_Kv : CharP (v.adicCompletion K) p :=
  (RingHom.charP_iff_charP (algebraMap K (v.adicCompletion K)) p).mp charP_K

/-- The candidate minimal polynomial witness for `thetaw` over `Kv := v.adicCompletion K`. -/
def gPoly : Polynomial (v.adicCompletion K) := ArtinSchreier.poly p (algebraMap K (v.adicCompletion K) a)

theorem gPoly_monic : gPoly.Monic := ArtinSchreier.poly_monic p _

theorem gPoly_irreducible : Irreducible gPoly :=
  ArtinSchreier.irreducible_iff.mpr (algebraMap_K_Kv_a_eq ▸ xK_inv_not_mem_range)

theorem isIntegral_theta : IsIntegral K theta :=
  ⟨ArtinSchreier.poly p a, ArtinSchreier.poly_monic p a, aeval_theta⟩

/-- `minpoly K theta` is exactly `ArtinSchreier.poly p a` — `hirr` (irreducibility of the latter,
already established for `a_not_mem_range`) identifies the two directly. -/
theorem minpoly_K_theta_eq : minpoly K theta = ArtinSchreier.poly p a :=
  (minpoly.eq_of_irreducible_of_monic hirr aeval_theta (ArtinSchreier.poly_monic p a)).symm

/-- **The base-changed minimal polynomial of `theta` is exactly `gPoly`.** Both sides are the
same substitution of `a`/`algebraMap K Kv a` into the same polynomial shape `X ^ p - X - C _`. -/
theorem map_minpoly_K_theta_eq_gPoly :
    (minpoly K theta).map (algebraMap K (v.adicCompletion K)) = gPoly := by
  rw [minpoly_K_theta_eq, gPoly, ArtinSchreier.poly_def, ArtinSchreier.poly_def,
    Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]

/-- **`finrank Kv Lw = p` and `Algebra.IsSeparable Kv Lw`, via
`Langlands.AdicCompletionPrimitiveElementDegree`'s generic primitive-element criterion.** `theta`
is a primitive element of `L / K` (`adjoin_θ_eq_top`) whose minimal polynomial's base change to
`Kv` is irreducible (`map_minpoly_K_theta_eq_gPoly` identifies it with the already-irreducible
`gPoly`), which is exactly the generic lemma's hypothesis. -/
theorem finrank_Kv_Lw_and_isSeparable :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) = Module.finrank K L ∧
      Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L) :=
  IsDedekindDomain.HeightOneSpectrum.finrank_and_isSeparable_of_primitiveElement K L v w
    isIntegral_theta adjoin_θ_eq_top (map_minpoly_K_theta_eq_gPoly ▸ gPoly_irreducible)

theorem finrank_Kv_Lw : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = p := by
  rw [finrank_Kv_Lw_and_isSeparable.1, finrank_K_L]

instance : Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L) :=
  finrank_Kv_Lw_and_isSeparable.2

theorem finrank_K₀_L₀ :
    Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) = p := by
  rw [IsIntegralClosure.rank (v.adicCompletionIntegers K) (v.adicCompletion K)
    (w.adicCompletion L) (w.adicCompletionIntegers L), finrank_Kv_Lw]

theorem finrank_eq :
    Module.finrank (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      v.asIdeal.ramificationIdx' w.asIdeal := by
  rw [finrank_K₀_L₀, e_eq_p]

/-! ### Field 1 of `IsTotallyRamified`: `map_maximalIdeal_eq`

Unlike the template files, there is no definitional identity `Ideal.map (algebraMap R S) v.asIdeal
= w.asIdeal ^ e` to fall back on (`w` is abstract). Instead: `pi := thetaw⁻¹` is an *exact*
uniformizer of `w` (`Valued.v thetaw = exp 1` exactly, `e_eq_p_and_valuation_thetaw`), and algebra
gives `algebraMap Kv Lw xK = pi ^ p * u` for the unit `u := (1 - pi ^ (p - 1))⁻¹` — an honest
algebraic identity (not merely a valuation coincidence), obtained by clearing denominators in
`thetaw ^ p - thetaw = algebraMap Kv Lw xK⁻¹`. The unit factor does not affect the ideal identity:
`span {pi ^ p * u} = span {pi ^ p} = span {pi} ^ p = maximalIdeal L₀ ^ p = maximalIdeal L₀ ^ e`. -/

theorem thetaw_ne_zero : (thetaw : w.adicCompletion L) ≠ 0 :=
  fun h => theta_ne_zero ((algebraMap L (w.adicCompletion L)).injective (h.trans (map_zero _).symm))

/-- `pi`, the image of `thetaw⁻¹` — an exact uniformizer of `w.adicCompletion L`. -/
def pi : w.adicCompletion L := thetaw⁻¹

theorem valuation_pi : Valued.v (pi : w.adicCompletion L) = WithZero.exp (-1 : ℤ) := by
  rw [pi, map_inv₀, valuation_thetaw, ← WithZero.exp_neg]

theorem pi_pow_sub_one_lt_one : Valued.v ((pi : w.adicCompletion L) ^ (p - 1)) < 1 := by
  rw [map_pow, valuation_pi, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one, ← WithZero.exp_zero]
  apply WithZero.exp_lt_exp.mpr
  have hp2 : 1 < p := (Fact.out : p.Prime).one_lt
  have : (0 : ℕ) < p - 1 := Nat.sub_pos_of_lt hp2
  exact_mod_cast (neg_lt_zero).mpr (by exact_mod_cast this)

/-- **A generic field identity** (stated over a fresh field/element/exponent, deliberately not
mentioning `p`/`L`/`w` etc., to avoid `rw`-ing the ambient `p : ℕ` — since `L`'s *type* is defined in
terms of `p`, `rw`-ing `p` inside any goal mentioning `L`-derived types breaks Lean's motive
well-typedness check): `x * x ^ (n - 1) = x ^ n` for `n ≥ 1`. -/
theorem pow_one_mul_pow_pred_eq {F : Type*} [Monoid F] {x : F} {n : ℕ} (hn : 1 ≤ n) :
    x * x ^ (n - 1) = x ^ n := by
  rw [← pow_succ']
  congr 1
  omega

/-- **The key algebraic identity**: `algebraMap Kv Lw xK = pi ^ p * u`, for a genuine unit
`u := (1 - pi ^ (p - 1))⁻¹` of `w.adicCompletion L`. Derived purely algebraically from
`thetaw ^ p - thetaw = algebraMap Kv Lw xK⁻¹` (`thetaw_pow_sub_thetaw`) by factoring
`thetaw ^ p - thetaw = thetaw ^ p * (1 - pi ^ (p - 1))` and inverting both sides. -/
theorem algebraMap_xK_eq :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) xK =
      (pi : w.adicCompletion L) ^ p * (1 - pi ^ (p - 1))⁻¹ := by
  show algebraMap (v.adicCompletion K) (w.adicCompletion L) xK =
      (thetaw : w.adicCompletion L)⁻¹ ^ p * (1 - (thetaw : w.adicCompletion L)⁻¹ ^ (p - 1))⁻¹
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hkey : (thetaw : w.adicCompletion L) =
      thetaw ^ p * (thetaw : w.adicCompletion L)⁻¹ ^ (p - 1) := by
    rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ thetaw_ne_zero)]
    exact pow_one_mul_pow_pred_eq hp1
  have hfactor : (thetaw : w.adicCompletion L) ^ p - thetaw =
      thetaw ^ p * (1 - (thetaw : w.adicCompletion L)⁻¹ ^ (p - 1)) := by
    rw [mul_sub, mul_one, ← hkey]
  have hstar : algebraMap (v.adicCompletion K) (w.adicCompletion L) xK *
      (thetaw ^ p * (1 - (thetaw : w.adicCompletion L)⁻¹ ^ (p - 1))) = 1 := by
    rw [← hfactor, thetaw_pow_sub_thetaw, ← map_mul, mul_inv_cancel₀ xK_ne_zero, map_one]
  have h4 : algebraMap (v.adicCompletion K) (w.adicCompletion L) xK =
      (thetaw ^ p * (1 - (thetaw : w.adicCompletion L)⁻¹ ^ (p - 1)))⁻¹ :=
    eq_inv_of_mul_eq_one_left hstar
  rw [h4, mul_inv, ← inv_pow]

/-- `xK`, viewed as an element of `v.adicCompletionIntegers K`. -/
def xK₀ : v.adicCompletionIntegers K :=
  ⟨xK, by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K v, valuation_xK,
      ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)⟩

/-- `pi`, viewed as an element of `w.adicCompletionIntegers L`. -/
def π₀ : w.adicCompletionIntegers L :=
  ⟨pi, by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers S L w, valuation_pi,
      ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)⟩

theorem isUniformizer_xK₀ : Valuation.IsUniformizer Valued.v (xK₀ : v.adicCompletion K) := by
  rw [Valuation.IsUniformizer.iff, show (xK₀ : v.adicCompletion K) = xK from rfl, valuation_xK,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K v)]
  rfl

theorem isUniformizer_π₀ : Valuation.IsUniformizer Valued.v (π₀ : w.adicCompletion L) := by
  rw [Valuation.IsUniformizer.iff, show (π₀ : w.adicCompletion L) = pi from rfl, valuation_pi,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective L w)]
  rfl

theorem maximalIdeal_K₀_eq : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)
    = Ideal.span {(xK₀ : v.adicCompletionIntegers K)} :=
  isUniformizer_xK₀.is_generator

theorem maximalIdeal_L₀_eq : IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)
    = Ideal.span {(π₀ : w.adicCompletionIntegers L)} :=
  isUniformizer_π₀.is_generator

theorem valuation_one_sub_pi_pow : Valued.v (1 - (pi : w.adicCompletion L) ^ (p - 1)) = 1 := by
  have h := Valuation.map_sub_eq_of_lt_left (v := Valued.v) (x := (1 : w.adicCompletion L))
    (y := (pi : w.adicCompletion L) ^ (p - 1)) (by rw [map_one]; exact pi_pow_sub_one_lt_one)
  rwa [map_one] at h

theorem one_sub_pi_pow_ne_zero : (1 - (pi : w.adicCompletion L) ^ (p - 1)) ≠ 0 := by
  intro h0
  have hcopy := valuation_one_sub_pi_pow
  rw [h0, Valuation.map_zero] at hcopy
  exact absurd hcopy (by norm_num)

/-- `u₀`, the unit `(1 - pi ^ (p - 1))⁻¹` of `w.adicCompletionIntegers L`. -/
def u₀ : w.adicCompletionIntegers L :=
  ⟨(1 - (pi : w.adicCompletion L) ^ (p - 1))⁻¹, by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers S L w, map_inv₀,
      valuation_one_sub_pi_pow, inv_one]⟩

theorem u₀_isUnit : IsUnit (u₀ : w.adicCompletionIntegers L) := by
  refine IsUnit.of_mul_eq_one
    (⟨(1 - (pi : w.adicCompletion L) ^ (p - 1)), by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers S L w,
        valuation_one_sub_pi_pow]⟩) ?_
  apply Subtype.ext
  show (1 - (pi : w.adicCompletion L) ^ (p - 1))⁻¹ * (1 - (pi : w.adicCompletion L) ^ (p - 1)) = 1
  exact inv_mul_cancel₀ one_sub_pi_pow_ne_zero

/-- **The key identity, descended to `L₀ := w.adicCompletionIntegers L`.** -/
theorem algebraMap_xK₀_eq :
    algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
        (xK₀ : v.adicCompletionIntegers K) =
      (π₀ : w.adicCompletionIntegers L) ^ p * u₀ := by
  apply Subtype.ext
  show algebraMap (v.adicCompletion K) (w.adicCompletion L) xK = _
  rw [algebraMap_xK_eq]; rfl

theorem map_maximalIdeal_eq :
    Ideal.map (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L))
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) =
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^
        (v.asIdeal.ramificationIdx' w.asIdeal) := by
  rw [maximalIdeal_K₀_eq, Ideal.map_span, Set.image_singleton, algebraMap_xK₀_eq,
    Ideal.span_singleton_mul_right_unit u₀_isUnit,
    ← Ideal.span_singleton_pow, ← maximalIdeal_L₀_eq, e_eq_p]

/-! ### Field 3 of `IsTotallyRamified`: `exists_sub_algebraMap_mem_maximalIdeal`

The residue extension `R ⧸ v.asIdeal → S ⧸ w.asIdeal` is trivial (`f := v.asIdeal.inertiaDeg'
w.asIdeal = 1`), obtained the same way as `e = p`: from `ef_le_p` (`e · f ≤ p`) with `e = p` already
known, `p · f ≤ p` forces `f ≤ 1`, and `f ≥ 1` always (`Ideal.inertiaDeg'_ne_zero`). Since both
quotients are fields and the residue extension has degree exactly `1`, `algebraMap (R ⧸ v.asIdeal)
(S ⧸ w.asIdeal)` is surjective (`finrank_eq_one_iff_of_nonzero'` applied to `1`); this is the
`S`-level analogue of the completed-integers-level statement `IsTotallyRamified` actually needs, and
transports to it via `Langlands.AdicCompletionIntegersResidue`'s general single-place density fact
exactly as in the template files. -/

theorem f_eq_one : v.asIdeal.inertiaDeg' w.asIdeal = 1 := by
  haveI := v.isMaximal
  have hf_pos : 0 < v.asIdeal.inertiaDeg' w.asIdeal :=
    Nat.pos_iff_ne_zero.mpr (Ideal.inertiaDeg'_ne_zero v.asIdeal w.asIdeal)
  have hef := ef_le_p
  rw [e_eq_p] at hef
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hle : v.asIdeal.inertiaDeg' w.asIdeal ≤ 1 :=
    Nat.le_of_mul_le_mul_left (by rwa [mul_one]) hp_pos
  omega

attribute [local instance] Ideal.Quotient.field

theorem residue_surjective :
    Function.Surjective (algebraMap (R ⧸ v.asIdeal) (S ⧸ w.asIdeal)) := by
  haveI := v.isMaximal
  haveI := w.isMaximal
  have hfin : Module.finrank (R ⧸ v.asIdeal) (S ⧸ w.asIdeal) = 1 := by
    rw [← Ideal.inertiaDeg'_algebraMap]; exact f_eq_one
  have h1 : (1 : S ⧸ w.asIdeal) ≠ 0 := one_ne_zero
  have hspan := (finrank_eq_one_iff_of_nonzero' (1 : S ⧸ w.asIdeal) h1).mp hfin
  intro y
  obtain ⟨c, hc⟩ := hspan y
  exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩

/-- **The naturality square `R → K₀ → L₀ = R → S → L₀`.** -/
theorem algebraMap_R_K₀_L₀_eq (r : R) :
    algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
        (algebraMap R (v.adicCompletionIntegers K) r) =
      algebraMap S (w.adicCompletionIntegers L) (algebraMap R S r) := by
  apply Subtype.ext
  rw [IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_adicCompletionIntegers]
  show IsDedekindDomain.HeightOneSpectrum.adicCompletionComap K L v w
      (algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletion K) = _
  rw [show (algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletion K)
        = algebraMap K (v.adicCompletion K) (algebraMap R K r) from rfl,
    IsDedekindDomain.HeightOneSpectrum.adicCompletionComap_algebraMap]
  show algebraMap L (w.adicCompletion L) (algebraMap K L (algebraMap R K r)) =
      algebraMap L (w.adicCompletion L) (algebraMap S L (algebraMap R S r))
  rw [← IsScalarTower.algebraMap_apply R K L, ← IsScalarTower.algebraMap_apply R S L]

theorem exists_sub_algebraMap_mem_maximalIdeal :
    ∀ y : w.adicCompletionIntegers L, ∃ r : v.adicCompletionIntegers K,
      y - algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) r ∈
        IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) := by
  intro y
  obtain ⟨s, hs⟩ := w.exists_algebraMap_sub_mem_maximalIdeal y
  obtain ⟨c, hc⟩ := residue_surjective (Ideal.Quotient.mk w.asIdeal s)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨algebraMap R (v.adicCompletionIntegers K) r, ?_⟩
  have hmem : s - algebraMap R S r ∈ w.asIdeal := by
    have heq : Ideal.Quotient.mk w.asIdeal (algebraMap R S r) = Ideal.Quotient.mk w.asIdeal s := by
      rw [← Ideal.Quotient.algebraMap_mk_of_liesOver (p := v.asIdeal) (P := w.asIdeal) r, hr, hc]
    rwa [Ideal.Quotient.eq, ← neg_mem_iff, neg_sub] at heq
  have hsc : (y : w.adicCompletionIntegers L) -
      algebraMap S (w.adicCompletionIntegers L) (algebraMap R S r) =
      ((y : w.adicCompletionIntegers L) - algebraMap S (w.adicCompletionIntegers L) s) +
        algebraMap S (w.adicCompletionIntegers L) (s - algebraMap R S r) := by
    rw [map_sub]; ring
  rw [algebraMap_R_K₀_L₀_eq, hsc]
  refine (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).add_mem hs ?_
  have hval_lt : w.valuation L (algebraMap S L (s - algebraMap R S r)) < 1 :=
    (w.valuation_lt_one_iff_mem (s - algebraMap R S r)).mpr hmem
  have hValued_lt : Valued.v (algebraMap S (w.adicCompletionIntegers L)
      (s - algebraMap R S r) : w.adicCompletion L) < 1 := by
    rw [show (algebraMap S (w.adicCompletionIntegers L) (s - algebraMap R S r) :
        w.adicCompletion L) = (algebraMap S L (s - algebraMap R S r) : w.adicCompletion L) from rfl,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hval_lt
  exact IsDedekindDomain.HeightOneSpectrum.mem_maximalIdeal_of_valued_lt_one w hValued_lt

/-- **`IsTotallyRamified K L v w` for this concrete instance.** Assembled from `map_maximalIdeal_eq`,
`finrank_eq`, and `exists_sub_algebraMap_mem_maximalIdeal` above — a genuine wild (`p ∣ e`),
Galois (`IsGalois K L`), *separable* Artin–Schreier extension. -/
theorem isTotallyRamified : IsDedekindDomain.HeightOneSpectrum.IsTotallyRamified K L v w where
  map_maximalIdeal_eq := map_maximalIdeal_eq
  finrank_eq := finrank_eq
  exists_sub_algebraMap_mem_maximalIdeal := exists_sub_algebraMap_mem_maximalIdeal

/-! ### Step 3 (`expEquiv` / `norm_exp_eq_exp_trace`): structurally inapplicable, not merely hard

`IsGalois K L` holds unconditionally here (`ArtinSchreier.instIsGalois`), so this instance *is*
genuinely Galois, wild, and separable. But
`Langlands.AdicCompletionNormExpTrace.norm_exp_eq_exp_trace` additionally requires
`[CharZero K] [CharZero L]` (see its signature), and
`Langlands.NonarchimedeanExponentialUnitsIso.expEquiv` is built on the same `NonarchimedeanExponential`
machinery, whose `exp` series `∑ xⁿ / n!` is only well-defined when division by `n!` makes sense for
all `n` — i.e. genuinely needs characteristic `0` (or at least characteristic `> n` for every `n`
appearing, which fails identically for *every* `n ≥ p` in any characteristic-`p` field). This
repo's exp/log thread targets **mixed-characteristic** local fields (finite extensions of `ℚ_p`,
characteristic `0` with residue characteristic `p`) — exactly the classical setting where the
`p`-adic exponential converges.

This concrete instance is **equal-characteristic**: `K := FractionRing (k[X])` has `CharP K p`
(`charP_K`), not `CharZero K` — it is a function field, not a `p`-adic field. This is not an
accident of this particular choice of `R`; it is inherent to using `k[X]` (`k` a field of
characteristic `p`) as the base Dedekind domain at all. Reaching a *mixed*-characteristic wild
Galois instance (needed to actually exercise `expEquiv`/`norm_exp_eq_exp_trace`) would require
starting from a genuine `p`-adic base ring (e.g. `ℤ_p` or the ring of integers of a finite extension
of `ℚ_p`) with an Artin–Schreier-*style* wildly ramified extension built over it — a different, and
non-trivial, construction problem in its own right, not a continuation of this file's approach.
**Conclusion: step 3 does not apply to this instance by construction, not because of any remaining
proof difficulty** — `IsTotallyRamified` (step 2) is the complete, correct milestone this file
delivers. -/

end Langlands.TotallyRamifiedArtinSchreierConcreteExample

end
