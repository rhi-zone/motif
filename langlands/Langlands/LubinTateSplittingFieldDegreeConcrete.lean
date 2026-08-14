import Mathlib.NumberTheory.Padics.RingHoms
import Langlands.LubinTateSplittingFieldDegree
import Langlands.LubinTateWeierstrassPreparation
import Langlands.LubinTateRootCountConcrete

/-!
# Non-vacuity certificate for `finrank_K_1_eq_residueCard_sub_one`

`Langlands.LubinTate.finrank_K_1_eq_residueCard_sub_one`
(`Langlands/LubinTateSplittingFieldDegree.lean`) proves `[K_1 : K] = q - 1` from a package of
hypotheses. An **earlier** version of that arc carried an extra hypothesis `hsplit :
(P.divX.map (algebraMap O K)).Splits`, and `Langlands/LubinTateHsplitVacuity.lean` shows `hsplit` is
jointly unsatisfiable with the standing `[IsFractionRing O K]` whenever `residueCard O ≥ 3` — so
that earlier statement, though a valid implication, had no instances at any interesting residue
cardinality. This file certifies, in Lean, that the current statement does not repeat that failure:
its hypothesis package is **jointly satisfiable with `residueCard O = 3`**, by an explicit,
hypothesis-free instantiation.

## What is certified

* `LubinTate.exists_finrank_K_1_eq_residueCard_sub_one` — the abstract certificate: over an
  `m`-adically complete `O` (`[IsAdicComplete (maximalIdeal O) O]`, needed only for Weierstrass
  preparation), for *any* uniformizer `π`, the whole data package `(f, P, u)` **exists**, and its
  `K_1` has `finrank K (K_1 P) = residueCard O - 1`. `f := π • X + X ^ q`
  (`LubinTate.exists_isLubinTatePoly`, no constraint on `q`) and `(P, u)` its Weierstrass
  factorization (`LubinTate.exists_isWeierstrassFactorization_of_isLubinTatePoly`).
* `LubinTate.exists_finrank_K_1_eq_padic_sub_one` — the same at `O := ℤ_[p]`, `K := ℚ_[p]`, `π := p`,
  with **every** typeclass and hypothesis discharged from Mathlib: `finrank ℚ_[p] (K_1 P) = p - 1`.
* `LubinTate.exists_finrank_K_1_eq_two_padic_three` — the punchline: at `p = 3`,
  `residueCard ℤ_[3] = 3` and `finrank ℚ_[3] (K_1 P) = 2`, with **no hypotheses at all**. This is a
  genuine, non-degenerate instance of the theorem at `residueCard O = 3`, i.e. exactly in the range
  `LubinTateHsplitVacuity.lean` rules out for the old `hsplit`-carrying statement.
* `IsDedekindDomain.HeightOneSpectrum.exists_finrank_K_1_eq_residueCard_sub_one_of_adicCompletion` —
  the same certificate at the repo's usual concrete package `O := v.adicCompletionIntegers F`,
  `K := v.adicCompletion F` (the pattern of `Langlands/LubinTateRootCountConcrete.lean`), which
  covers function fields as well as number fields. See the `IsAdicComplete` caveat below.

## Why the old contradiction can no longer be derived

`LubinTateHsplitVacuity.false_of_hsplit_of_two_le_divX_natDegree` derives `False` from exactly two
ingredients: (i) `Qk := P.divX.map (algebraMap O K)` is *irreducible over `K`* (Gauss's lemma for the
weakly-Eisenstein `P.divX`, using `[IsFractionRing O K]`), and (ii) `hsplit`, which says `Qk` splits
**inside `K` itself**. An irreducible polynomial of degree `≥ 2` has no root in its own base field,
so (i) and (ii) collide as soon as `Qk.natDegree = residueCard O - 1 ≥ 2`.

Ingredient (i) is still present in `finrank_K_1_eq_residueCard_sub_one` — indeed it is what pins the
degree down. Ingredient (ii) is **gone**: there is no `hsplit` hypothesis, because `K_1 P` is
*constructed* as `Qk.SplittingField` (`Langlands.LubinTate.K_1`), a genuine extension of `K`, and
`Qk` splits there by construction (`splits_K_1`), not in `K`. Irreducibility over `K` and splitting
over the splitting field of `Qk` are simultaneously true for every irreducible `Qk` — that is what
being a splitting field means — so no contradiction is available.

Correspondingly, **nothing in the hypothesis package constrains `residueCard O`.** Reading the
package hypothesis by hypothesis: `[Finite (ResidueField O)]` bounds `residueCard O` above by
finiteness only; `hOK`/`hπnorm` are statements about the norms of `O`'s image and of `π`, with no
reference to the residue field; `hπ : Irreducible π` likewise; `hf : IsLubinTatePoly π (residueCard
O) f` is satisfiable for *every* `q = residueCard O ≥ 2` by the explicit `π • X + X ^ q`
(`exists_isLubinTatePoly`, which takes no hypothesis on `q` beyond `2 ≤ residueCard O`, itself
automatic from `Finite (ResidueField O)`); and `(hu, heq, hPdist, hPdeg)` are supplied wholesale by
Weierstrass preparation from `hf`. The `p = 3` instance below is the certificate that this reading
is right rather than merely plausible: it exhibits the entire package satisfied with `residueCard =
3`.

## The `IsAdicComplete` caveat

Weierstrass preparation (`exists_isWeierstrassFactorization_of_isLubinTatePoly`, hence Mathlib's
`PowerSeries.exists_isWeierstrassFactorization`) requires `[IsAdicComplete (maximalIdeal O) O]`.

* At `O := ℤ_[p]` this is a Mathlib instance
  (`Mathlib/NumberTheory/Padics/PadicIntegers.lean`), so the p-adic certificates below carry **no**
  hypothesis of any kind.
* At `O := v.adicCompletionIntegers F` it is *not* available. It is mathematically true — the
  valuation ring of a complete discretely-valued field is `m`-adically complete — but no such
  instance or lemma exists in this Mathlib: the `IsAdicComplete` instances present are for Artinian
  local rings, for `ℤ_[p]`, for `AdicCompletion I R` itself, and for `𝒪[K]` with `K` carrying the
  `ValuativeRel`-based `IsNonarchimedeanLocalField` bundle (`Mathlib/NumberTheory/LocalField/Basic.lean`)
  — none of which applies to `v.adicCompletionIntegers F` as this repo instantiates it. The generic
  bridge that would close it, `IsAdic.isPrecomplete_iff` (`Mathlib/RingTheory/AdicCompletion/Topology.lean`),
  needs `IsAdic (maximalIdeal O)` for the subspace topology — i.e. that the valuation topology on
  the integers is the `m`-adic one — and Mathlib has no `IsAdic` lemma for valuation topologies at
  all (its only `IsAdic` lemmas are `is_ideal_adic_pow` and the discreteness criterion). Proving it
  is a self-contained development that is *not* attempted here; the hypothesis is therefore left
  explicit in the `adicCompletion` statement.

Leaving it explicit is honest with respect to this file's purpose: `IsAdicComplete (maximalIdeal
(v.adicCompletionIntegers F)) (v.adicCompletionIntegers F)` is a property of the completion alone,
mentioning neither `residueCard` nor any Lubin-Tate datum, so it cannot be what makes the package
vacuous — and the `ℤ_[p]` certificates, where it *is* discharged, settle the satisfiability question
outright.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

open IsLocalRing PowerSeries

namespace LubinTate

/-! ## The abstract certificate -/

section Abstract

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsFractionRing O K]

/-- **The hypothesis package of `finrank_K_1_eq_residueCard_sub_one` is satisfiable**, for any
uniformizer `π` of an `m`-adically complete `O`: the Lubin-Tate series `f` and its Weierstrass
factorization `f = P * u` all exist, and the resulting splitting field has degree `residueCard O -
1`. `f := π • X + X ^ q` comes from `exists_isLubinTatePoly` (which constrains `q` not at all) and
`(P, u)` from `exists_isWeierstrassFactorization_of_isLubinTatePoly`; the degree is then the
headline theorem applied to that data. -/
theorem exists_finrank_K_1_eq_residueCard_sub_one (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) :
    ∃ (f : O⟦X⟧) (P : O[X]) (u : O⟦X⟧), IsLubinTatePoly π (residueCard O) f ∧ IsUnit u ∧
      f = (P : O⟦X⟧) * u ∧ P.IsDistinguishedAt (maximalIdeal O) ∧
      P.natDegree = residueCard O ∧
      Module.finrank K (K_1 (K := K) P) = residueCard O - 1 := by
  obtain ⟨f, hf⟩ := exists_isLubinTatePoly hπ
  obtain ⟨P, u, hPdist, hu, heq, hPdeg⟩ := exists_isWeierstrassFactorization_of_isLubinTatePoly hf
  exact ⟨f, P, u, hf, hu, heq, hPdist, hPdeg,
    finrank_K_1_eq_residueCard_sub_one hOK hπ hπnorm hf hu heq hPdist hPdeg⟩

/-- **The hypothesis package of `isGalois_K_1` is satisfiable too**, by the *same* data package: the
Lubin-Tate series `f` and its Weierstrass factorization `f = P * u` exist, the resulting splitting
field has degree `residueCard O - 1`, **and** `K_1 P / K` is a genuine Galois extension.

`isGalois_K_1` takes exactly the argument list of `finrank_K_1_eq_residueCard_sub_one`, so its
non-vacuity *could* be inferred from that theorem's certificate; this states it as its own
conclusion instead, so the `IsGalois K (K_1 P)` term is actually built and type-checked at the
witness rather than argued for on paper. -/
theorem exists_isGalois_K_1 (hOK : ∀ c : O, ‖algebraMap O K c‖ ≤ 1)
    {π : O} (hπ : Irreducible π) (hπnorm : ‖algebraMap O K π‖ < 1) :
    ∃ (f : O⟦X⟧) (P : O[X]) (u : O⟦X⟧), IsLubinTatePoly π (residueCard O) f ∧ IsUnit u ∧
      f = (P : O⟦X⟧) * u ∧ P.IsDistinguishedAt (maximalIdeal O) ∧
      P.natDegree = residueCard O ∧
      Module.finrank K (K_1 (K := K) P) = residueCard O - 1 ∧
      IsGalois K (K_1 (K := K) P) := by
  obtain ⟨f, hf⟩ := exists_isLubinTatePoly hπ
  obtain ⟨P, u, hPdist, hu, heq, hPdeg⟩ := exists_isWeierstrassFactorization_of_isLubinTatePoly hf
  exact ⟨f, P, u, hf, hu, heq, hPdist, hPdeg,
    finrank_K_1_eq_residueCard_sub_one hOK hπ hπnorm hf hu heq hPdist hPdeg,
    isGalois_K_1 hOK hπ hπnorm hf hu heq hPdist hPdeg⟩

end Abstract

/-! ## The fully concrete instance: `O := ℤ_[p]`, `K := ℚ_[p]` -/

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- `ResidueField ℤ_[p]` is finite, being `ZMod p` (`PadicInt.residueField`). -/
instance instFiniteResidueFieldPadicInt : Finite (ResidueField ℤ_[p]) :=
  Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv

/-- **`residueCard ℤ_[p] = p`**, from `PadicInt.residueField : ResidueField ℤ_[p] ≃+* ZMod p`. -/
theorem residueCard_padicInt : residueCard ℤ_[p] = p :=
  (Nat.card_congr (PadicInt.residueField (p := p)).toEquiv).trans (Nat.card_zmod p)

/-- **`hOK` at `ℤ_[p] → ℚ_[p]`**: `algebraMap ℤ_[p] ℚ_[p]` is the coercion, which is norm-preserving
(`PadicInt.padic_norm_e_of_padicInt`), and `ℤ_[p]` is by definition the closed unit ball. -/
theorem norm_algebraMap_padicInt_le_one (c : ℤ_[p]) : ‖algebraMap ℤ_[p] ℚ_[p] c‖ ≤ 1 := by
  rw [PadicInt.algebraMap_apply, PadicInt.padic_norm_e_of_padicInt]
  exact c.norm_le_one

/-- **`hπnorm` at `π := p`**: `‖(p : ℚ_[p])‖ = p⁻¹ < 1` (`Padic.norm_p_lt_one`). -/
theorem norm_algebraMap_padicInt_p_lt_one : ‖algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p])‖ < 1 := by
  rw [PadicInt.algebraMap_apply]
  simpa using Padic.norm_p_lt_one (p := p)

/-- **The certificate, with every hypothesis discharged**: at `O := ℤ_[p]`, `K := ℚ_[p]`, `π := p`,
the data `(f, P, u)` of `finrank_K_1_eq_residueCard_sub_one` exists and
`Module.finrank ℚ_[p] (K_1 P) = p - 1`. Nothing is assumed beyond `p` being prime — in particular
`[IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p]]` is a Mathlib instance here, not a hypothesis. -/
theorem exists_finrank_K_1_eq_padic_sub_one :
    ∃ (f : ℤ_[p]⟦X⟧) (P : ℤ_[p][X]) (u : ℤ_[p]⟦X⟧),
      IsLubinTatePoly (p : ℤ_[p]) (residueCard ℤ_[p]) f ∧ IsUnit u ∧
      f = (P : ℤ_[p]⟦X⟧) * u ∧ P.IsDistinguishedAt (maximalIdeal ℤ_[p]) ∧
      P.natDegree = residueCard ℤ_[p] ∧
      Module.finrank ℚ_[p] (K_1 (K := ℚ_[p]) P) = p - 1 := by
  obtain ⟨f, P, u, hf, hu, heq, hPdist, hPdeg, hfinrank⟩ :=
    exists_finrank_K_1_eq_residueCard_sub_one (K := ℚ_[p]) (norm_algebraMap_padicInt_le_one p)
      PadicInt.irreducible_p (norm_algebraMap_padicInt_p_lt_one p)
  exact ⟨f, P, u, hf, hu, heq, hPdist, hPdeg, by rwa [residueCard_padicInt] at hfinrank⟩

/-- **The Galois certificate at `O := ℤ_[p]`, `K := ℚ_[p]`, `π := p`, every hypothesis discharged**:
the data `(f, P, u)` exists with `finrank ℚ_[p] (K_1 P) = p - 1` and `IsGalois ℚ_[p] (K_1 P)`. -/
theorem exists_isGalois_K_1_padic :
    ∃ (f : ℤ_[p]⟦X⟧) (P : ℤ_[p][X]) (u : ℤ_[p]⟦X⟧),
      IsLubinTatePoly (p : ℤ_[p]) (residueCard ℤ_[p]) f ∧ IsUnit u ∧
      f = (P : ℤ_[p]⟦X⟧) * u ∧ P.IsDistinguishedAt (maximalIdeal ℤ_[p]) ∧
      P.natDegree = residueCard ℤ_[p] ∧
      Module.finrank ℚ_[p] (K_1 (K := ℚ_[p]) P) = p - 1 ∧
      IsGalois ℚ_[p] (K_1 (K := ℚ_[p]) P) := by
  obtain ⟨f, P, u, hf, hu, heq, hPdist, hPdeg, hfinrank, hgal⟩ :=
    exists_isGalois_K_1 (K := ℚ_[p]) (norm_algebraMap_padicInt_le_one p)
      PadicInt.irreducible_p (norm_algebraMap_padicInt_p_lt_one p)
  exact ⟨f, P, u, hf, hu, heq, hPdist, hPdeg, by rwa [residueCard_padicInt] at hfinrank, hgal⟩

end Padic

/-- **`IsGalois ℚ_[3] (K_1 P)` at a genuine degree-`2` witness, with no hypotheses at all.** The
companion to `exists_finrank_K_1_eq_two_padic_three` for `isGalois_K_1`: at `p = 3` the extension
`K_1 P / ℚ_[3]` is Galois *and* has degree `2` — so the `IsGalois` conclusion is certified at a
witness where `K_1 P ≠ K`, not at a degenerate one. Built by instantiating `isGalois_K_1` directly
at this data (via `exists_isGalois_K_1`), not inferred from `finrank_K_1_eq_residueCard_sub_one`'s
certificate sharing its hypothesis list. -/
theorem exists_isGalois_K_1_padic_three :
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    residueCard ℤ_[3] = 3 ∧
    ∃ (f : ℤ_[3]⟦X⟧) (P : ℤ_[3][X]) (u : ℤ_[3]⟦X⟧),
      IsLubinTatePoly (3 : ℤ_[3]) (residueCard ℤ_[3]) f ∧ IsUnit u ∧
      f = (P : ℤ_[3]⟦X⟧) * u ∧ P.IsDistinguishedAt (maximalIdeal ℤ_[3]) ∧
      P.natDegree = residueCard ℤ_[3] ∧
      Module.finrank ℚ_[3] (K_1 (K := ℚ_[3]) P) = 2 ∧
      IsGalois ℚ_[3] (K_1 (K := ℚ_[3]) P) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨residueCard_padicInt 3, ?_⟩
  obtain ⟨f, P, u, hf, hu, heq, hPdist, hPdeg, hfinrank, hgal⟩ := exists_isGalois_K_1_padic 3
  exact ⟨f, P, u, by exact_mod_cast hf, hu, heq, hPdist, hPdeg, hfinrank, hgal⟩

/-- **Non-vacuity at `residueCard O = 3`, with no hypotheses whatsoever.** At `p = 3` the package of
`finrank_K_1_eq_residueCard_sub_one` is satisfied with `residueCard ℤ_[3] = 3` and
`Module.finrank ℚ_[3] (K_1 P) = 2` — a genuinely ramified degree-`2` extension, not the trivial
`K_1 = K` case. This is exactly the range (`residueCard O ≥ 3`) in which
`Langlands/LubinTateHsplitVacuity.lean` proves the *old*, `hsplit`-carrying form of the arc has no
instances at all; the current form does. -/
theorem exists_finrank_K_1_eq_two_padic_three :
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    residueCard ℤ_[3] = 3 ∧
    ∃ (f : ℤ_[3]⟦X⟧) (P : ℤ_[3][X]) (u : ℤ_[3]⟦X⟧),
      IsLubinTatePoly (3 : ℤ_[3]) (residueCard ℤ_[3]) f ∧ IsUnit u ∧
      f = (P : ℤ_[3]⟦X⟧) * u ∧ P.IsDistinguishedAt (maximalIdeal ℤ_[3]) ∧
      P.natDegree = residueCard ℤ_[3] ∧
      Module.finrank ℚ_[3] (K_1 (K := ℚ_[3]) P) = 2 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨residueCard_padicInt 3, ?_⟩
  obtain ⟨f, P, u, hf, hu, heq, hPdist, hPdeg, hfinrank⟩ := exists_finrank_K_1_eq_padic_sub_one 3
  exact ⟨f, P, u, by exact_mod_cast hf, hu, heq, hPdist, hPdeg, hfinrank⟩

end LubinTate

/-! ## The certificate at `O := v.adicCompletionIntegers F`, `K := v.adicCompletion F` -/

namespace IsDedekindDomain.HeightOneSpectrum

open LubinTate

variable {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F] (v : HeightOneSpectrum A)

/-- **The certificate at the repo's usual concrete package.** For `v` a height-one place with finite
residue field and `π` a uniformizer of `v.adicCompletionIntegers F`, the whole data package of
`finrank_K_1_eq_residueCard_sub_one` exists and the splitting field has degree `residueCard - 1`.
`hOK` and `hπnorm` are discharged exactly as in `Langlands/LubinTateRootCountConcrete.lean`
(`norm_algebraMap_adicCompletionIntegers_le_one`,
`norm_algebraMap_adicCompletion_uniformizer_lt_one`).

`[IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F)]` remains
an explicit hypothesis: it is true but unavailable in this Mathlib (see this file's module docstring
for exactly what is missing). It constrains only the completion, never `residueCard`, so it is not
what would make the package vacuous — and `LubinTate.exists_finrank_K_1_eq_two_padic_three` closes
the satisfiability question with no hypotheses at all. -/
theorem exists_finrank_K_1_eq_residueCard_sub_one_of_adicCompletion [Finite (A ⧸ v.asIdeal)]
    [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F))
      (v.adicCompletionIntegers F)]
    {π : v.adicCompletionIntegers F} (hπ : Irreducible π) :
    ∃ (f : (v.adicCompletionIntegers F)⟦X⟧) (P : (v.adicCompletionIntegers F)[X])
      (u : (v.adicCompletionIntegers F)⟦X⟧),
      IsLubinTatePoly π (residueCard (v.adicCompletionIntegers F)) f ∧ IsUnit u ∧
      f = (P : (v.adicCompletionIntegers F)⟦X⟧) * u ∧
      P.IsDistinguishedAt (maximalIdeal (v.adicCompletionIntegers F)) ∧
      P.natDegree = residueCard (v.adicCompletionIntegers F) ∧
      Module.finrank (v.adicCompletion F) (K_1 (K := v.adicCompletion F) P) =
        residueCard (v.adicCompletionIntegers F) - 1 :=
  exists_finrank_K_1_eq_residueCard_sub_one (norm_algebraMap_adicCompletionIntegers_le_one v) hπ
    (norm_algebraMap_adicCompletion_uniformizer_lt_one F v hπ)

end IsDedekindDomain.HeightOneSpectrum

end
