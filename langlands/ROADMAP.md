# Roadmap: Formalizing the Langlands Program in Lean 4 / Mathlib

Scope: get to the point where the **core Langlands conjectures can be formally
stated** (local and global correspondence, functoriality, Artin's conjecture),
then prove whatever is in reach. Grounded against Mathlib as vendored at
`langlands/.lake/packages/mathlib` (tagged for Lean toolchain in this project,
"v4.32.1" per the task brief). All claims below are backed by `find`/`grep`
against that source tree, not memory — file paths are cited so they can be
re-checked.

---

## 1. What Mathlib already has

### 1.1 Algebraic number theory (number fields, rings of integers, completions, valuations)

**Strong.** `Mathlib/NumberTheory/NumberField/` is a large, actively developed
directory:
- `Basic.lean` — `NumberField` class, ring of integers `𝓞 K`.
- `InfinitePlace/{Basic,Embeddings,Ramification,TotallyRealComplex}.lean`,
  `InfinitePlace/Completion.lean` — archimedean places and their completions.
- `Completion/{FinitePlace,InfinitePlace,LiesOverInstances,Ramification}.lean`
  — completions at all places, uniform treatment.
- `FinitePlaces.lean`, `RamificationInertia.lean` (in `NumberTheory/`) —
  non-archimedean places, ramification/inertia degrees.
- `Ideal/{Basic,Asymptotics,KummerDedekind}.lean` — ideal theory,
  Kummer–Dedekind.
- `Discriminant/{Defs,Basic,Different}.lean`, `ClassNumber.lean`,
  `Units/{Basic,Regulator,DirichletTheorem}.lean` — discriminant, class group,
  unit group, Dirichlet's unit theorem.
- `CanonicalEmbedding/*`, `FractionalIdeal.lean`, `Norm.lean`,
  `ProductFormula.lean`, `CMField.lean`, `Cyclotomic/*`, `DedekindZeta.lean`.
- Valuations: `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` (used by
  the finite adèle ring), `Mathlib/RingTheory/Valuation/Discrete/Basic.lean`.
- `Mathlib/RingTheory/Frobenius.lean` (2025, Andrew Yang) — **arithmetic
  Frobenius elements** for a finite Galois extension, built on
  `Mathlib/RingTheory/Invariant/{Basic,Profinite}.lean`. This is a genuinely
  load-bearing result for Langlands (Frobenius conjugacy classes are exactly
  what a Galois representation is decorated with).

**Missing:** no notion of "Frobenius element well-defined up to conjugacy as a
function of the Galois representation", no Chebotarev density statement tying
Frobenius distribution to L-functions.

### 1.2 p-adic numbers and local fields

**Partial.** `Mathlib/NumberTheory/Padics/` has `PadicNumbers.lean`,
`PadicIntegers.lean`, `PadicNorm.lean`, `Hensel.lean`, `ProperSpace.lean`,
`ValuativeRel.lean`, `WithVal.lean`, `RingHoms.lean`, `HeightOneSpectrum.lean`,
`Complex.lean` (ℂ_p), `Measure/{Basic,Topology}.lean` (Haar measure on ℚ_p /
ℤ_p already exists via general Haar-measure machinery), `AddChar.lean`
(additive characters of ℚ_p — directly useful for Tate's thesis / local
L-factors).

`Mathlib/NumberTheory/LocalField/Basic.lean` exists but is thin (one file) —
general local fields (finite extensions of ℚ_p or 𝔽_q((t))) are not developed
as a first-class abstraction the way number fields are; what's available is
via `NumberField.Completion.FinitePlace`, i.e. completions of number fields
at finite places, rather than a standalone "local field" typeclass hierarchy
with local class field theory attached.

**Missing:** local class field theory (local Artin map), local
Langlands-relevant structure (no smooth/admissible representations of
`GL_n(local field)`, see §1.5).

### 1.3 Adeles and ideles

**Present, additive side only.**
- `Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean` (María Inés de
  Frutos-Fernández) — finite adèle ring of a Dedekind domain as a restricted
  product, built on `Mathlib/Topology/Algebra/RestrictedProduct/*`.
- `Mathlib/NumberTheory/NumberField/InfiniteAdeleRing.lean` — infinite adèle
  ring (product over archimedean completions).
- `Mathlib/NumberTheory/NumberField/AdeleRing.lean` — full adèle ring
  `AdeleRing (𝓞 K) K` = infinite × finite, with `principalSubgroup` (the
  diagonal embedding of `K`).
- Restricted-product infrastructure: `Topology/Algebra/RestrictedProduct/
  {Basic,TopologicalSpace,Units}.lean`, `Topology/Algebra/IsOpenUnits.lean`
  (needed to give the units of a restricted product, i.e. ideles, their
  correct topology).

**Update — built in this project (Phase 0, now complete):** `IdeleGroup` and
`IdeleClassGroup` are defined in `Langlands/IdeleGroup.lean` (this repo, not
upstreamed to Mathlib), with `toClassGroup` and its kernel computed,
sorry-free. This closes the gap noted originally against Mathlib itself
(Mathlib upstream still has no such definition). Also landed this project:
the local norm map at finite places (`Langlands/NormMap.lean`, via
`HeightOneSpectrum`) and at archimedean places (`NumberField.InfinitePlace`),
plus the full idele-group norm map.

**Still missing:** no compactness of `𝔸ₖ/K` or of the norm-one idele class
group; no strong approximation theorem (`grep` for "strong approximation" is
empty); no self-dual Haar measure / Tate's thesis setup beyond the raw
`AddChar` and Haar-measure primitives.

### 1.4 Algebraic groups (linear, reductive, split, ...)

**Essentially absent as a theory.** What exists:
- Concrete classical groups over a ring/field: `Mathlib/LinearAlgebra/
  GeneralLinearGroup/`, `Matrix/GeneralLinearGroup/`, `SpecialLinearGroup.lean`,
  `Matrix/SpecialLinearGroup.lean`, `Matrix/ProjectiveSpecialLinearGroup.lean`.
  These give `GL_n`, `SL_n`, `PSL_n` as abstract/matrix groups (used already
  by the modular forms library for `SL(2,ℤ)`), but with no group-scheme
  structure, no functor-of-points perspective, no algebraicity/rationality
  theory attached.
- Root systems and Weyl groups exist as **combinatorial/Lie-theoretic**
  objects: `Mathlib/LinearAlgebra/RootSystem/{Base,Hom,WeylGroup,
  Finite/CanonicalBilinear,Finite/Nondegenerate,GeckConstruction/Basic}.lean`,
  `Mathlib/Algebra/Lie/Weights/RootSystem.lean`. This is exactly the
  combinatorial data (root datum) that classifies split reductive groups —
  genuinely reusable — but there is no bridge from "abstract root system" to
  "reductive group scheme with that root datum."
- Group schemes: `grep` for "group scheme" only turns up
  `Mathlib/AlgebraicGeometry/Group/{Abelian,Smooth}.lean` (about group objects
  in the category of schemes generically, e.g. abelian varieties/smooth
  group schemes) and `Mathlib/RingTheory/HopfAlgebra/MonoidAlgebra.lean`. No
  torus, no notion of split/quasi-split/reductive/semisimple group scheme, no
  Chevalley classification, no dual group (Langlands dual) construction.
- `Mathlib/Algebra/BrauerGroup/{Defs,...}` exists (relevant to inner forms of
  reductive groups and to local class field theory via `H^2`, but not
  connected to anything algebraic-group-shaped yet).

**This is the single largest gap for Langlands.** Even *stating* "let G be a
split reductive group over a number field, ^L G its Langlands dual" requires
a theory of reductive groups that does not exist in Mathlib today. The
closest reusable ingredient is the root-system/Weyl-group library plus the
raw matrix groups `GL_n`/`SL_n` for the archetypal case.

### 1.5 Representation theory (finite groups, topological groups, p-adic groups)

**Good for finite/general abstract groups, essentially absent for the
smooth/admissible p-adic representation theory Langlands actually needs.**
- `Mathlib/RepresentationTheory/` is rich: `Basic.lean`, `Character.lean`,
  `FDRep.lean`, `Rep/{Basic,Iso,Res}.lean`, `Semisimple.lean`,
  `Irreducible.lean`, `Induced.lean`, `Coinduced.lean`, `Intertwining.lean`,
  `Maschke.lean`, `Tannaka.lean`, `AlgebraRepresentation/Basic.lean`.
- `Mathlib/RepresentationTheory/Continuous/{Basic,TopRep}.lean` — continuous
  representations of topological groups exist as a category (`TopRep`). This
  is a real foothold: admissible/smooth representations of `GL_n(ℚ_p)` are a
  further specialization (locally constant vectors under compact open
  subgroups) that is not yet formalized but has a plausible landing spot.
- `Mathlib/RepresentationTheory/Homological/` — group cohomology
  (`GroupCohomology/{Basic,Functoriality,Shapiro,Hilbert90,
  LongExactSequence,LowDegree,FiniteCyclic}.lean`), group homology, **Tate
  cohomology** (`TateCohomology/Basic.lean`), and **continuous cohomology**
  (`ContCohomology/{Basic,LowDegree,Functoriality}.lean`) for profinite/
  topological-group coefficients. `Hilbert90.lean` is present and is a
  genuine class-field-theory-adjacent result already proved.

**Missing:** no smooth representations, no admissible representations, no
Jacquet modules, no parabolic induction, no supercuspidal
representations/support, no Bernstein decomposition — i.e. none of the
representation-theoretic vocabulary the local Langlands correspondence is
stated in.

### 1.6 Automorphic forms

**Absent for the general notion; present only for the classical GL_2/SL_2(ℤ)
special case under a different name (modular forms).** `grep -rli
"automorphic"` across all of Mathlib returns only incidental hits
(`Algebra/Quandle.lean`, `NumberTheory/HeckeRing/Defs.lean` use the word
informally, not as a defined concept). What *does* exist and is directly
reusable as the motivating example:
- `Mathlib/NumberTheory/ModularForms/` — a substantial library: `Basic.lean`,
  `SlashActions.lean`, `SlashInvariantForms.lean`, `CongruenceSubgroups.lean`,
  `ArithmeticSubgroups.lean`, `Cusps.lean`, `BoundedAtCusp.lean`,
  `QExpansion.lean`, `CuspFormSubmodule.lean`, `Petersson.lean` (inner
  product), `EisensteinSeries/*` (a full sub-library), `LevelOne/*`
  (dimension formulas), `JacobiTheta/*`, `Delta.lean`, `DedekindEta.lean`.
- `Mathlib/NumberTheory/HeckeRing/Defs.lean` — an abstract Hecke ring, but
  this is the double-coset-algebra formalism, not Hecke *operators* acting on
  a specific space of modular forms with eigenform theory attached (`grep`
  for Hecke-operator-specific names like `HeckeOperator`/`T_p` found nothing
  relevant).

**Missing:** automorphic forms/representations for a general reductive group
`G(𝔸_K)`, cusp forms in that generality, Hecke operators as an algebra acting
on automorphic forms (only the abstract ring, not the action), Satake
isomorphism, Langlands' automorphic representation ↔ classical modular form
dictionary (the modular-forms library never leaves the classical, concrete
`SL(2,ℤ)` picture).

### 1.7 L-functions (Dirichlet, Hecke, Artin, automorphic)

**Strong for Dirichlet/Riemann zeta, absent for Hecke/Artin/automorphic.**
`Mathlib/NumberTheory/LSeries/` is large: `Basic.lean`, `Convergence.lean`,
`Linearity.lean`, `Convolution.lean`, `Dirichlet.lean`,
`DirichletContinuation.lean`, `RiemannZeta.lean`, `ZetaZeros.lean`,
`HurwitzZeta{Even,Odd,Values}.lean`, `AbstractFuncEq.lean` (an abstract
functional-equation framework — potentially reusable scaffolding for other
L-functions), `Nonvanishing.lean`, `Positivity.lean`, `PrimesInAP.lean`,
`MellinEqDirichlet.lean`, `SumCoeff.lean`, `Deriv.lean`, `Injectivity.lean`,
`ZMod.lean`. Plus `Mathlib/NumberTheory/NumberField/DedekindZeta.lean`
(Dedekind zeta function of a number field) and
`Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean`.

**Missing:** Hecke L-functions (of a Hecke character on the idele class
group — blocked on §1.3's missing idele class group), Artin L-functions (of
a Galois representation — blocked on §1.8), automorphic L-functions (blocked
on §1.6). The `AbstractFuncEq.lean` framework is the most promising reusable
piece: it's plausible Artin/automorphic L-functions could eventually plug
into it once their Euler products/coefficients are defined.

### 1.8 Galois representations

**Absent as a defined concept.** `grep -rli "galois representation"` finds
nothing; the closest hit, `CategoryTheory/Galois/Decomposition.lean`, is
about Grothendieck's categorical Galois theory (fiber functors, decomposition
groups for the category-theoretic Galois formalism), not about
`ρ : Gal(K̄/K) → GL_n(F)`. Ingredients that *are* present and directly
prerequisite:
- `Mathlib/FieldTheory/AbsoluteGaloisGroup.lean` — the absolute Galois group
  itself.
- `Mathlib/FieldTheory/Galois/Profinite.lean`,
  `Mathlib/Topology/Algebra/Category/ProfiniteGrp/`,
  `Mathlib/Topology/Category/{Profinite,LightProfinite}/` — profinite-group
  category theory, needed since Galois groups are profinite and a
  representation must be continuous.
- `Mathlib/CategoryTheory/Galois/*` (`Basic`, `Action`, `Equivalence`,
  `EssSurj`, `Full`, `GaloisObjects`, `IsFundamentalgroup`,
  `Prorepresentability`, `Topology`) — Grothendieck's Galois theory, giving
  an abstract fiber-functor formalism that generalizes the classical
  Gal(L/K)-action; reusable as scaffolding.
- `RingTheory/Frobenius.lean` (§1.1) and `RepresentationTheory/Continuous/*`
  (§1.5) are exactly the two ingredients that would need to be combined:
  continuous representations + Frobenius elements = the statement "a Galois
  representation is unramified at p and sends Frob_p to [specified conjugacy
  class]."

**Missing:** the actual definition
`GaloisRepresentation := ContinuousRepresentation (Gal(K̄/K)) F V` (or
similar), unramifiedness, local Galois representations at each place,
compatible systems of ℓ-adic representations.

**Update — Weil group and Weil–Deligne group both now built in this project
(Phase 1, complete):** `grep` for "weil group"/"WeilGroup" still finds
nothing in Mathlib itself, but this project's own `Langlands/WeilGroup.lean`
fully constructs `W_K` as the preimage of ℤ in ℤ̂ under `toZhatHom`, with the
decomposition subgroup (everything), the inertia subgroup, the arithmetic
Frobenius, and `Gal(k̄/𝓀[K]) ≅ ℤ̂` sending Frobenius to 1. On top of that,
`Langlands/WeilDeligneRepresentation.lean` lands
`LocalField.WeilDeligneRepresentation K V`: a structure bundling a
representation `ρ : Representation ℂ (WeilGroup K) V`, a nilpotent
`N : V →ₗ[ℂ] V`, and the intertwining relation
`ρ w ∘ₗ N ∘ₗ ρ w⁻¹ = weilNormChar K w • N`, plus `ofRepresentation`/`trivial`
constructors — all sorry-free. This closes the hard blocker for local
Langlands and for Artin/Weil L-functions at ramified places.

### 1.9 Class field theory

**Not present as a theorem, but real prerequisite infrastructure exists.**
`grep -rli "class field theory\|artin reciprocity"` turns up nothing on
point. What is present and is a genuine down payment:
- `Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean` —
  Hilbert's Theorem 90, a classical stepping stone to local CFT via
  cohomological methods.
- `Mathlib/Algebra/BrauerGroup/*` — the Brauer group, which is where local
  CFT's `H²(Gal(L/K), L^×) ≅ ℚ/ℤ` statement lives.
- `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean`.
- `RingTheory/Frobenius.lean` (Frobenius elements, §1.1) is precisely the
  input to the (global) Artin map on unramified primes.

**Missing:** the Artin reciprocity map itself
(`Idele class group → Gal(K^ab/K)`), local reciprocity, the existence
theorem, everything tying Brauer-group `H²` to an explicit reciprocity
isomorphism.

### 1.10 Modular forms and modularity

Covered in §1.6 — this is Mathlib's most mature "Langlands-adjacent" corner.
Notably absent: any formal statement or partial result toward the modularity
theorem (elliptic curve ↔ weight-2 newform) or the Serre conjecture (odd
irreducible 2-dim mod-p Galois reps ↔ mod-p modular forms) — both are
"blocked on Galois representations" (§1.8) plus an elliptic-curve L-function
side that does exist in some form (`Mathlib/NumberTheory/FLT/` directory
exists, worth checking separately for Fermat's Last Theorem groundwork, which
is adjacent but a different project).

### 1.11 Homological algebra (group cohomology, Galois cohomology)

**Good, and directly useful.** Beyond what's cited in §1.5/§1.9: this is
arguably Mathlib's *strongest* Langlands-adjacent area after number fields —
group cohomology, group homology, Tate cohomology, and continuous cohomology
of topological/profinite groups are all present with functoriality,
long-exact-sequence, Shapiro's lemma, and low-degree (H⁰/H¹/H²) computations.
Galois cohomology specifically (i.e. continuous cohomology specialized to
`Gal(L/K)`-modules) is not packaged as its own named theory but is a thin
wrapper away given `ContCohomology` + `AbsoluteGaloisGroup` +
`ProfiniteGrp`.

### 1.12 Category theory (derived categories, sheaves)

**Broad and mature**, though this is general-purpose Mathlib category theory
rather than anything Langlands-specific: `CategoryTheory/Sites/*` (sheaves,
`SheafCohomology/{Basic,Cech,MayerVietoris}`,
`NonabelianCohomology/H1.lean`), `AlgebraicGeometry/Sites/
ElladicCohomology.lean` (a stub/start on étale-style ℓ-adic cohomology —
worth a closer look if the geometric Langlands / étale-cohomology route is
ever pursued), derived-category and homological-algebra scaffolding under
`Algebra/Homology/*`. Not a near-term bottleneck for *stating* the arithmetic
Langlands conjectures, but will matter for any proof that goes through étale
cohomology of Shimura varieties.

---

## 2. Prerequisites to formally *state* the core conjectures

### 2.1 Local Langlands correspondence (for `GL_n`, then general reductive `G`)

To state "there is a bijection between (a) `L`-parameters
`Gal(K̄_v/K_v) → ^L G` (or Weil-Deligne group → `^L G`) up to conjugacy, and
(b) packets of irreducible admissible representations of `G(K_v)`" you need,
at minimum:
1. A local field `K_v` (§1.2 — partial: have completions, not a clean local-field abstraction).
2. The absolute Galois group / Weil group of `K_v`, continuous (§1.8 — Galois group yes; Weil group and Weil-Deligne group both now built in this project's `Langlands/WeilGroup.lean` and `Langlands/WeilDeligneRepresentation.lean`, Phase 1, complete).
3. A reductive group `G` over `K_v` and its Langlands dual `^L G` (§1.4 — **missing entirely**, hardest gap).
4. Admissible (or at least smooth) representations of `G(K_v)` (§1.5 — **missing**; have continuous reps, not smoothness/admissibility over a locally profinite group).
5. `L`-parameters as continuous, Frobenius-semisimple homomorphisms
   `W_{K_v} → ^L G(ℂ)` (needs 2 and 3).

For `GL_n` specifically, steps 3–4 simplify (dual group of `GL_n` is `GL_n`;
"reductive group" can be replaced by literal matrix group `GL_n` from
§1.4's classical-groups library), which is why `GL_n` is the right entry
point rather than general `G`.

### 2.2 Global Langlands correspondence (automorphic ↔ Galois)

Needs: number field `K` (have, §1.1); adele ring `𝔸_K` (have, §1.3); a
reductive group `G/K`; automorphic representations of `G(𝔸_K)` (§1.6 —
missing in general, have the `GL_2`/classical special case); a global Galois
representation or compatible system (§1.8 — missing); and the local
correspondence at every place to state compatibility. Strictly harder than
2.1 since it needs 2.1 at every place plus a global automorphic theory.

### 2.3 Functoriality

Needs a map of `L`-groups `^L H → ^L G` (needs §1.4's dual-group
construction) inducing a transfer of automorphic representations/L-parameters
— i.e. depends on everything in 2.1/2.2 already existing for *two* groups
`H`, `G` plus the dual-group functor being contravariant-composable.
Strictly the hardest to even state, since it quantifies over pairs of
reductive groups and a homomorphism of their duals.

### 2.4 Artin's conjecture (Artin L-functions are automorphic)

Needs: Artin L-function of a Galois representation (needs §1.8 Galois reps +
§1.7's L-function framework, specifically factoring in local factors at
ramified primes via the **Weil-Deligne group** — now built in this project,
§1.8, `Langlands/WeilDeligneRepresentation.lean`); and the
`n = 1` global Langlands correspondence for `GL_n` (§2.2) to state "is
automorphic." This is *more* tractable to fully state than 2.2/2.3 in one
respect — it only needs `GL_n` — and the Artin L-function side's Weil-Deligne
prerequisite is now in place in this project (nothing in Mathlib upstream
touches it yet).

**Cross-cutting observation:** all four conjectures bottleneck on the same
three missing primitives: **(a)** reductive groups + Langlands dual group,
**(b)** the Weil–Deligne group (now built in this project — both
`Langlands/WeilGroup.lean` and `Langlands/WeilDeligneRepresentation.lean`,
Phase 1 complete), **(c)** smooth/admissible representations of `p`-adic and
adelic groups. Sequencing the roadmap around building these three first, in
the cheapest special case (`GL_n`) before the general case, is the only path
that avoids stalling on (a).

---

## 3. Dependency-ordered roadmap

### Phase 0 — Idele class group (extends existing adele infrastructure) — **COMPLETE**
- **Status:** done, sorry-free. `IdeleGroup K := (AdeleRing (𝓞 K) K)ˣ` and
  `IdeleClassGroup K := IdeleGroup K ⧸ K^×` are built in
  `Langlands/IdeleGroup.lean`, with `toClassGroup` and its kernel computed.
  Also landed alongside it: the local norm map at finite places
  (`Langlands/NormMap.lean`, via `HeightOneSpectrum`) and at archimedean
  places (`NumberField.InfinitePlace`), the full idele-group norm map, the
  Kedlaya–Sutherland unramified-extension correspondence
  (`Langlands/UnramifiedExtension.lean`), and rank-one valuation
  compatibility (`Langlands/HenselianValuation.lean`).
- **Depended on:** `NumberField.AdeleRing` (have),
  `Topology/Algebra/RestrictedProduct/Units.lean` (have),
  `IsOpenUnits.lean` (have).
- **Not yet done:** not upstreamed to Mathlib; compactness of the norm-one
  idele class group and strong approximation remain open (§1.3).
- **Upstreamable:** yes, cleanly — natural next file in
  `Mathlib/NumberTheory/NumberField/`, same authors' territory
  (de Frutos-Fernández, Mercuri have prior art here).

### Phase 1 — Weil group and Weil–Deligne group — **COMPLETE**
- **Status:** done, sorry-free. The plain Weil group is built in
  `Langlands/WeilGroup.lean`: `W_K` as the preimage of ℤ in ℤ̂ under
  `toZhatHom`, the decomposition subgroup (everything), the inertia
  subgroup, the arithmetic Frobenius, and
  `Gal(k̄/𝓀[K]) ≅ ℤ̂` sending Frobenius to 1. On top of that,
  `Langlands/WeilDeligneRepresentation.lean` lands
  `LocalField.WeilDeligneRepresentation K V`: a structure bundling a
  representation `ρ : Representation ℂ (WeilGroup K) V`, a nilpotent
  `N : V →ₗ[ℂ] V`, and the intertwining relation
  `ρ w ∘ₗ N ∘ₗ ρ w⁻¹ = weilNormChar K w • N`, with `ofRepresentation`/
  `trivial` constructors. This matches the phase's original description
  (extension of `Gal(K̄_v/K_v)` by ℤ via valuation/Frobenius, plus the
  `(ρ, N)` pair formalism with nilpotent-intertwining condition, chosen
  over the `W_K × SL_2` alternative).
- **Depended on:** absolute Galois group (have, `AbsoluteGaloisGroup.lean`),
  profinite group category (have, `ProfiniteGrp`, plus a new
  universe-bridging instance landed this session), local field valuation
  (have, `Padics`/completions, plus new rank-one valuation compatibility in
  `Langlands/HenselianValuation.lean`), Frobenius elements (have,
  `RingTheory/Frobenius.lean`). Also newly available as general-purpose
  infrastructure: cyclic-subgroup-by-divisor classification,
  ℤ-subgroup-by-index classification.
- **Not yet done:** not upstreamed to Mathlib.
- **Upstreamable:** yes — this is a standalone, well-defined object useful
  far beyond Langlands (local class field theory, Artin L-functions,
  local epsilon factors).

### Phase 2 — Local class field theory: local Artin map
- **Build:** the local reciprocity map `K_v^× → Gal(K_v^ab/K_v)` (or its
  Weil-group refinement `K_v^× ≅ W_{K_v}^ab`).
- **Depends on:** Phase 1 (Weil group — **now complete**), `RingTheory/
  Frobenius.lean`, `Algebra/BrauerGroup/*` (have — this is where the `H²`
  computation that proves the existence theorem lives),
  `GroupCohomology/Hilbert90.lean` (have).
- **Size:** large. This is a genuine theorem (not just a definition) with a
  real proof burden (local existence theorem, norm groups, Brauer group
  computation over local fields).
- **Scope correction (review):** "`BrauerGroup + Hilbert90`" in the
  dependency list above is the route marker, not the distance covered. The
  local Artin map is not just an isomorphism `K_v^× ≅ W_{K_v}^ab` — it needs
  to be *characterized*: norm functoriality (the map is compatible with norm
  maps for finite extensions), Frobenius compatibility (uniformizers map to
  Frobenius lifts on unramified extensions), and the existence theorem
  (open subgroups of finite index in `K_v^×` correspond to abelian
  extensions). Getting from the raw Brauer-group `H²` computation to an
  Artin map *with these characterizing properties* is the bulk of Serre's
  *Local Fields*, chapters VIII–XIII — this is comparable in size to
  everything else in Phase 2 combined, not a footnote to it.
- **New prerequisites now available (this project):** the local norm map at
  finite places (`Langlands/NormMap.lean`) and archimedean places, the full
  idele-group norm map, and the Kedlaya–Sutherland unramified-extension
  correspondence (`Langlands/UnramifiedExtension.lean`) — these are direct
  down payments on the "norm functoriality" and "Frobenius compatibility on
  unramified extensions" characterizing properties described above, though
  the reciprocity map itself and the existence theorem are still not
  started.
- **Upstreamable:** yes, high-value — local CFT is a named, citable theorem
  many other projects would want.
- **Note:** not strictly required to *state* the four core conjectures (they
  can be stated with the Artin map as an assumed/axiomatized black box), but
  required to make any of Phase 3+ meaningful rather than vacuous.
- **Before building: check for prior formalization.** Of every phase in this
  roadmap, Phase 2 is the likeliest to already exist in some form elsewhere
  — local/global class field theory is a natural target for other
  formalization efforts (e.g. community CFT work adjacent to the
  Mathlib `FLT` project, `Mathlib/NumberTheory/FLT/`, §1.10). Check that
  effort, and any Zulip/roadmap discussion around it, before writing new CFT
  proofs in-repo — duplicating an in-flight class field theory formalization
  would be the single most wasteful outcome in this whole plan.

### Phase 2a — Unramified norm-group surjectivity (scoped first milestone, 2026-08-05)
- **Why this exists:** Phase 2 as written has no small starting task — its
  "first move" jumps straight to the full reciprocity map, sized comparable
  to Serre's *Local Fields* Ch. VIII–XIII combined. This subsection scopes a
  genuinely smaller first cut: the classical fact that for `L/K` the
  **unramified** extension of local fields of degree `n`, the norm map is
  as surjective as it can possibly be — this is the "easy half" of local
  CFT (Serre Ch. V §2–3); the ramified/Lubin–Tate half is the hard part
  Phase 2 is really about.
- **Statement, full version (the classical theorem):** `N_{L/K}(L^×) =
  ⟨π⟩^n · O_K^×` for `L/K` unramified of degree `n`, `π` any uniformizer of
  `K` (also a uniformizer of `L`, since unramified). Equivalently the norm
  map is surjective on unit groups `O_L^× ↠ O_K^×`.
- **Investigated 2026-08-05 (research agent, read-only):** what's already in
  place and what's missing, ingredient by ingredient:
  - **Have, exactly what's needed:** a single-extension local norm map
    `IsDedekindDomain.HeightOneSpectrum.localNormMap : (w.adicCompletion
    L)ˣ →* (v.adicCompletion K)ˣ` in `Langlands/NormMap.lean` (built from
    `Algebra.norm`, already proven to send local units to local units via
    `localNormMap_mem_units`) — this had been an open question (is there a
    *single-extension* norm map, as opposed to only the idele-level one?);
    confirmed yes.
  - **Have, residue-field level:** `Mathlib.FieldTheory.Finite.GaloisField.
    norm_surjective` (norm `𝔽_{q^n} → 𝔽_q` is surjective) and
    `ValuationSubring.surjective_unitGroupToResidueFieldUnits` (reduction
    `O_L^× ↠ 𝓀[L]^×` is surjective, general valuation theory, no
    completeness needed, kernel = `principalUnitGroup`). Composing these
    with the residue-field correspondence already built in
    `Langlands/UnramifiedExtension.lean` gives, essentially for free: **the
    norm map on residue fields `𝓀[L]^× → 𝓀[K]^×` is surjective for the
    unramified extension.**
  - **Missing — real new content, not wiring:** closing the gap from
    "surjective mod principal units" to "surjective on all of `O_K^×`"
    needs lifting through the principal-units filtration `1 + π^i O_L`,
    which classically requires (a) a graded/log isomorphism of successive
    quotients `(1+π^iO_L)/(1+π^{i+1}O_L)` with the residue field
    (additively), (b) the fact the norm acts there via the *trace* map
    (`Mathlib.RingTheory.Trace.Basic.Algebra.trace_surjective` exists and is
    the right trace-surjectivity ingredient, but nothing connects it to
    norm-on-principal-units), and (c) a completeness/limit argument to
    piece the filtration together into full unit-group surjectivity. None
    of (a)–(c) exists in Mathlib or this repo — this is genuinely the
    mathematical content Serre spends real pages on, not a missing lemma
    name.
- **Scoped milestone (what to actually build first):** stop at the
  residue-field-level statement — `𝓀[L]^× → 𝓀[K]^×` is surjective for the
  unramified extension, proved by composing the three pieces above (finite
  field norm surjectivity + residue reduction surjectivity + the existing
  `UnramifiedExtension.lean` residue correspondence) — plus, if the
  `localNormMap`-reduces-to-residue-norm compatibility lemma turns out
  tractable, `O_L^× ↠ O_K^×` **modulo principal units**
  (`O_K^×/(1+𝔪_K)`). This is a clean, citable sub-theorem and an honest
  stopping point that does not require the principal-units filtration
  machinery.
- **Explicitly deferred to a later phase:** the full unramified norm-group
  theorem (`N_{L/K}(L^×) = ⟨π⟩^n · O_K^×`) needs the principal-units
  filtration graded isomorphism first — that filtration machinery is itself
  a legitimate next milestone after this one lands, not part of it.
- **Depends on:** `Langlands/NormMap.lean` (have, single-extension local
  norm map), `Langlands/UnramifiedExtension.lean` (have, residue-field
  correspondence), `Mathlib.FieldTheory.Finite.GaloisField.norm_surjective`
  (have), `ValuationSubring.surjective_unitGroupToResidueFieldUnits` (have).
- **Size:** small for the residue-field-level statement itself, **but the
  `localNormMap`-reduces-to-residue-norm compatibility square does not
  compose from existing pieces** — attempted 2026-08-05 and stopped
  (no file written, no `sorry`) after confirming via loogle against vendored
  Mathlib that no lemma connects `Algebra.norm` (`LinearMap.det (lmul R S
  x)`, `Mathlib/RingTheory/Norm/Defs.lean:64`) to a norm computed after
  reducing mod an ideal/maximal ideal — searches for
  `Algebra.norm (?A ⧸ ?I)`, `LinearMap.det, Ideal.Quotient.mk`, and
  base-change-style norm lemmas all returned nothing on point. Two viable
  routes to close it, both real sub-developments, not one-lemma glue:
  1. **Determinant/basis route.** Establish `Module.Free` for
     `w.adicCompletionIntegers L` over `v.adicCompletionIntegers K`
     (plausible via `Module.free_of_finite_type_torsion_free'`,
     `Mathlib/LinearAlgebra/FreeModule/PID.lean`, needing
     `IsPrincipalIdealRing`/`Module.Finite`/`Module.IsTorsionFree` instances
     for these adic-completion subrings not yet in this repo); lift that
     basis to the residue fields via
     `IsLocalRing.linearCombination_bijective_of_flat`
     (`Mathlib/RingTheory/LocalRing/Module.lean:292`, a genuine
     Nakayama/flatness tool that already exists and is on point); push the
     matrix of `lmul` through `RingHom.map_det`
     (`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`, confirmed to
     exist) to match entrywise reduction.
  2. **Galois/Frobenius route.** Use `Algebra.norm_eq_prod_automorphisms`
     (`Mathlib/RingTheory/Norm/Transitivity.lean`) and
     `prod_galRestrict_eq_norm`
     (`Mathlib/RingTheory/IntegralClosure/IntegralRestrict.lean`) to express
     the norm as a product over `Gal(L/K)` acting on the integral closure
     directly, then match that action to Frobenius on residue fields. Needs
     an `IsGalois` instance for the specific unramified completion
     extension and an `IsIntegralClosure` instance linking
     `w.adicCompletionIntegers L` to `v.adicCompletionIntegers K` — neither
     exists yet; `UnramifiedExtension.lean`'s decomposition-subgroup
     machinery is close but not packaged this way, and reconciling its
     action with `galRestrict`'s is itself nontrivial.
  Either route is comparable in size to what's already in
  `Langlands/UnramifiedExtension.lean` — a legitimate follow-on milestone in
  its own right, not a same-session composition on top of Phase 2a.
- **Next concrete step (for whoever picks this up):** pick route 1 or 2
  above and build the missing instance(s) it needs first, in isolation,
  before attempting the compatibility square itself.
- **Upstreamable:** the residue-field composition itself is likely too thin
  to be its own Mathlib PR, but is a real building block toward an
  upstreamable unramified-norm-group theorem once the principal-units
  filtration exists.

#### Status 2026-08-05 (second attempt) — residue-field half **CLOSED**, compatibility square still open

- **Built:** `Langlands/ResidueFieldNorm.lean` (new, 165 lines, zero
  `sorry`, `lake build Langlands.ResidueFieldNorm` green). Not yet in
  `Langlands.lean`'s import list — consistent with `NormMap.lean`,
  `HenselianValuation.lean`, `UnramifiedExtension.lean`, which are also
  built module-by-module rather than from the root target.
- **Key structural find (supersedes the prior session's "build `Module.Free`
  first" framing for the *structure*, not for the square):**
  `Valuation.HasExtension` (`Mathlib/RingTheory/Valuation/Extension.lean`)
  is exactly the right abstraction, and `NormMap.lean`'s
  `adicCompletionIntegers_comap_eq` (`Langlands/NormMap.lean:424`) is
  literally its hypothesis in disguise —
  `Valuation.isEquiv_iff_val_le_one` (`Mathlib/RingTheory/Valuation/
  Basic.lean:913`) turns the comap-of-valuation-subrings equation into
  `HasExtension`'s `val_isEquiv_comap`. Note `HasExtension` asks only for
  `IsEquiv`, not equality, so the ramification-index factor `e` in the
  valuation relation is harmless.
  - `ResidueFieldNorm.lean:72` `hasExtension_valued_adicCompletion` —
    `(Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).HasExtension
    (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)`.
  - That single instance yields, from `Extension.lean`'s
    `instAlgebra_valuationSubring` / `instIsLocalHomValuationInteger` /
    `IsLocalRing.ResidueField`'s `Ideal.Quotient.algebraOfLiesOver`:
    `Algebra K₀ L₀`, `IsLocalHom (algebraMap K₀ L₀)`,
    `(maximalIdeal L₀).LiesOver (maximalIdeal K₀)`, and
    **`Algebra 𝓀[K] 𝓀[L]`** — the instance whose absence previously made
    the residue-field norm unstatable in the `adicCompletion` setting.
    Re-stated in `adicCompletionIntegers` form at `ResidueFieldNorm.lean:92,
    100, 108` via `inferInstanceAs`, because `adicCompletionIntegers`
    (`Mathlib/RingTheory/DedekindDomain/AdicValuation.lean:809`) is a
    non-reducible `def` for `Valued.v.valuationSubring` and instance search
    does not see through it.
  - `ResidueFieldNorm.lean:118` `coe_algebraMap_adicCompletionIntegers` and
    `:127` `algebraMap_residueField_residue` (both `rfl`) pin these
    instances to `adicCompletionComap`, so the structure is provably the
    intended one and not something else instance search happened to find.
- **Proved:** for `[Finite 𝓀[L]]`,
  - `ResidueFieldNorm.lean:146` `residueField_norm_surjective` —
    `Function.Surjective (Algebra.norm 𝓀[K] (S := 𝓀[L]))`;
  - `ResidueFieldNorm.lean:157` `residueField_units_norm_surjective` —
    `Function.Surjective (Units.map (Algebra.norm 𝓀[K]))`, i.e.
    **`𝓀[L]^× ↠ 𝓀[K]^×`**.
  Both are `FiniteField.norm_surjective` / `FiniteField.unitsMap_norm_surjective`
  (`Mathlib.FieldTheory.Finite.GaloisField` — namespace `FiniteField`, not
  `GaloisField` as the note above says; fully general in `Algebra K K'` with
  `[Finite K']`, not tied to `GaloisField`) applied to the new instance.
  `Finite 𝓀[L]` is a hypothesis: `R`, `S` here are arbitrary Dedekind
  domains, so residue finiteness is not derivable.
- **Scope caveat, stated in the file's docstrings:** these are the
  **abstract** residue-field norm `Algebra.norm 𝓀[K] : 𝓀[L] → 𝓀[K]`. They
  are *not* the reduction of `localNormMap` (`NormMap.lean:386`). The
  unramifiedness of `w | v` is nowhere used and nowhere assumed.
- **Compatibility square: still open, not attempted in code.** Verified this
  session, via loogle against the vendored Mathlib:
  - `IsLocalRing.residue, Algebra.norm` → 0 hits;
    `Algebra.norm, Ideal.Quotient.mk` → 0 hits. No norm-mod-ideal lemma
    exists, confirming the prior session's finding.
  - `Module.Finite, Valuation.integer` → 0 hits;
    `Module.Free, Valuation.integer` → 0 hits;
    `Module.Finite, ValuationSubring` → 0 hits. So route 1's basis is not
    available: `Module.Finite`/`Module.Free` for `L₀` over `K₀` would have
    to be built from scratch (finiteness of the integral closure over a
    complete DVR), which is the bulk of that route.
  - Correction to route 1 above: `IsLocalRing.linearCombination_bijective_of_flat`
    **does not exist** (loogle: unknown identifier; no grep hit in vendored
    Mathlib). The on-point Nakayama-style tools that do exist are
    `Module.exists_basis_of_basis_baseChange` and
    `IsLocalRing.span_eq_top_of_tmul_eq_basis`, but both require
    `Module.FinitePresentation K₀ L₀` — i.e. they need the finiteness above
    as input, they do not supply it.
  - `IsDiscreteValuationRing (v.adicCompletionIntegers K)` *does* exist as a
    Mathlib instance
    (`instIsDiscreteValuationRingSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegers`),
    so once `Module.Finite` + torsion-freeness land, PID-freeness follows.
  - **Additional blocker not previously named:** even with a basis, the
    reduction step needs `𝔪_K · L₀ = 𝔪_L`, i.e. *unramifiedness*. There is
    currently no way to even state that in `NormMap.lean`'s setting — its
    `w | v` has arbitrary ramification index `e`, and Mathlib has no
    `Algebra.IsUnramified` for valuation-ring extensions (only
    `Algebra.IsUnramifiedAt`/`IsUnramifiedIn` for Dedekind-domain primes and
    `IsUnramifiedAtInfinitePlaces`). So route 1 needs *three* new pieces,
    not one: finiteness/freeness, an unramifiedness formulation, and the
    determinant reduction.
  - **The `AdjoinRoot`-basis shortcut was checked and does not apply.**
    `AdjoinRoot.powerBasisAux'` does exist and does work over an arbitrary
    `CommRing` (unlike `AdjoinRoot.powerBasis`), so it would give a free
    basis for free — but only for a ring of the form `AdjoinRoot f`.
    `HenselianLocalRing.exists_isDiscreteValuationRing_integralClosure_residueField_equiv`
    (`Langlands/UnramifiedExtension.lean:715`) does not expose the internal
    `AdjoinRoot f ≃+* C` isomorphism in its statement, and more decisively
    its setting is the wrong one: it produces
    `integralClosure R (IntermediateField.adjoin K {x})` inside an
    **algebraically closed** ambient `L` (`[IsAlgClosed L]` is a hypothesis),
    whereas `localNormMap` lives on `w.adicCompletion L`, which is not
    algebraically closed and is not given as `K_v⟮x⟯`. Bridging the two
    would require proving the completion extension is monogenic over
    `K₀` — i.e. proving unramified-implies-monogenic in the completion
    setting, which is itself the missing content, not a way around it.
- **Honest summary of Phase 2a status:** `𝓀[L]^× ↠ 𝓀[K]^×` is **closed as
  an abstract finite-field fact** in the correct `adicCompletion` setting,
  with the residue-field algebra structure now genuinely present and pinned
  to `adicCompletionComap`. It is **not** closed as the reduction of
  `localNormMap`; that remains the gate to `O_L^× ↠ O_K^×` mod principal
  units, and is a milestone-sized development (three pieces above), not
  session-sized glue.

#### Status 2026-08-05 (third pass) — re-verification confirms no drift; one new route considered and closed

- **Re-verified against live files and current vendored Mathlib** (still
  commit `520045a` per `.lake/packages/mathlib` git log, unchanged since the
  second-pass session — `langlands/flake.lock` has not moved since the
  original project-skeleton commit `6df4f72`, so this is the *same* Mathlib
  checkout, not a newer one). `Langlands/ResidueFieldNorm.lean` (165 lines),
  `Langlands/NormMap.lean` (763 lines), `Langlands/UnramifiedExtension.lean`
  (1211 lines) all match the second-pass description exactly.
  `lake build Langlands.ResidueFieldNorm` green (3412 jobs).
  `grep -rn sorry langlands/Langlands/` empty.
- **All prior loogle findings re-run fresh, all still 0 hits, confirming no
  Mathlib drift on this specific gap:** `Algebra.norm (?A ⧸ ?I)`,
  `LinearMap.det, Ideal.Quotient.mk`, `IsLocalRing.residue, Algebra.norm`,
  `Algebra.norm, Ideal.Quotient.mk`, `Module.Finite, Valuation.integer`,
  `Module.Free, Valuation.integer`, `Module.Finite, ValuationSubring`,
  `Module.Free, ValuationSubring`, `IsDiscreteValuationRing, Module.Finite`,
  `Valuation.Integers, Module.Finite` — all 0 hits.
  `IsLocalRing.linearCombination_bijective_of_flat` still does not exist
  (unknown identifier). `Module.exists_basis_of_basis_baseChange` and
  `IsLocalRing.span_eq_top_of_tmul_eq_basis` still exist, still need
  `Module.FinitePresentation`/`Module.Finite K₀ L₀` as *input*.
- **New candidate route considered this session (route 3): finiteness via
  `IsIntegralClosure.finite` instead of via `Module.Free`/PID theory.**
  `IsIntegralClosure.finite` (`Mathlib/RingTheory/DedekindDomain/
  IntegralClosure.lean`) gives `Module.Finite A C` for `C` the integral
  closure of a Noetherian integrally-closed domain `A` in a finite separable
  extension `L` of `Frac(A)`. `v.adicCompletionIntegers K` already has
  `IsDiscreteValuationRing` (hence Noetherian, hence — via
  `Valuation.Integers.isIntegrallyClosed_integers` — integrally closed), so
  the two domain-side hypotheses on `A` are already satisfied. This looked
  like a shortcut around building `Module.Free` from PID theory from
  scratch. **It is not**, because it needs `[IsIntegralClosure C A L]` as an
  *instance* — i.e. it needs `w.adicCompletionIntegers L` to actually **be**
  the integral closure of `v.adicCompletionIntegers K` in `w.adicCompletion
  L`, and that fact does not exist in Mathlib for general valuation-ring
  extensions:
  - `ValuationRing, IsIntegralClosure` → 0 hits;
    `Valuation.integer, IsIntegralClosure` → 0 hits;
    `Valuation.HasExtension, IsIntegral` → 0 hits;
    `FiniteDimensional, ValuationSubring, IsIntegral` → 0 hits. No lemma
    connects a `Valuation.HasExtension` pair (which this repo already has,
    `ResidueFieldNorm.lean:72`) to the statement that the top valuation
    subring equals the integral closure of the bottom one.
  - Two directions would be needed to build this fact by hand: (i)
    integral-over-`K₀` elements of `L` land in `L₀` — a standard
    non-archimedean argument (dominant-term bound on a monic relation) that
    does *not* need completeness, but is not in Mathlib in this generality
    either; (ii) elements of `L₀` are integral over `K₀` — the hard
    direction, which genuinely needs completeness of `K` (uniqueness of the
    valuation extension to a finite extension of a complete field), and is
    itself the kind of fact `IsIntegralClosure.finite` was supposed to
    shortcut around, not a corollary of it. Proving only (i) would not
    unlock `IsIntegralClosure.finite`, which needs the full `IsIntegralClosure`
    instance (both directions), so a partial result here wires nothing
    downstream.
  - Checked whether Mathlib's separate non-archimedean-analysis
    normed-field development (`Mathlib/Analysis/Normed/Unbundled/
    SpectralNorm.lean`, `spectralNorm`/`isNonarchimedean_spectralNorm`,
    the de Frutos-Fernández et al. formalization of unique norm extension
    on complete fields) could supply direction (ii) via a
    spectral-norm-equals-valuation identification. It is disconnected from
    this repo's `Valued`/`adicCompletion` framework: `spectralNorm,
    integralClosure` → 0 hits; no lemma equates `spectralNorm` with a
    `Valuation`/`Valued.v` instance anywhere in vendored Mathlib. Bridging
    the two formalizations would itself be new work, not a shortcut.
  - `UnramifiedExtension.lean:808,901` already uses `IsIntegralClosure.finite
    R K K' C` — but in the `[IsAlgClosed L]`/`K⟮x⟯` setting checked and
    rejected in the second-pass session (line 715's theorem doesn't expose
    the needed isomorphism and isn't in the `adicCompletion` setting), not
    the `w.adicCompletionIntegers L` setting needed here. Confirms this is
    the same wall from a different angle, not a way around it.
- **Conclusion: no route to `Module.Finite`/`Module.Free` for
  `w.adicCompletionIntegers L` over `v.adicCompletionIntegers K` is
  buildable from existing Mathlib pieces without first proving, from
  scratch, that a valuation subring extending another (in the
  `Valuation.HasExtension` sense) equals the integral closure of the base in
  a finite extension of a complete field.** That fact is itself genuine
  local-field theory (uses completeness essentially, via uniqueness of
  valuation extension) and is not present under any of the three
  formalizations checked (`Valuation`/`ValuationSubring`,
  `IsIntegralClosure`, `spectralNorm`). No code was written this session —
  every candidate stopped at a landscape check, not a proof attempt, so
  there is nothing partial to leave as `sorry` and nothing was.
- **Status unchanged from second pass**: residue-field half closed
  (`ResidueFieldNorm.lean`), compatibility square open, routes 1 and 2 as
  scoped in the second-pass entry above still stand, route 3 is now also
  ruled out for the same reason as route 1 (needs the same missing
  integral-closure-equals-valuation-ring fact, just reached via a different
  Mathlib lemma). Next session should not re-run any of the loogle queries
  listed above — they are confirmed stable across two independent sessions
  on the same Mathlib commit.

#### Status 2026-08-05 (fourth pass) — the missing integral-closure fact was already in this repo; primitives (1) and (2) both closed

- **Correction to the third-pass conclusion.** The third pass concluded no
  route to `Module.Finite`/`Module.Free` was buildable without proving, from
  scratch, that `w.adicCompletionIntegers L` equals the integral closure of
  `v.adicCompletionIntegers K` in `w.adicCompletion L` (the "hard
  direction": elements of the top valuation ring are integral over the
  base, which needs completeness). **That hard direction had already been
  proved in this repo**, one session earlier than the third pass, as
  `IsDedekindDomain.HeightOneSpectrum.isIntegral_of_mem_of_comap_eq`
  (`NormMap.lean:214`, landed in commit `be81faa`, "close
  `localNormMap_mem_units` via Galois-conjugate integrality argument") — via
  a normal-closure-plus-Galois-conjugates argument that genuinely uses
  `LocalField.valuationSubring_eq_of_comap_eq` (completeness/uniqueness of
  valuation extension). It was used only pointwise, to show local units
  have unit norms, in `localNormMap_mem_units`; nobody had recognized it as
  the general integral-closure fact three sessions had been searching for.
  This is a **process finding**, not just a math one: the third-pass
  loogle-based search strategy (querying vendored Mathlib for "is this
  connected to `IsIntegralClosure`/`spectralNorm`/etc.") never checked
  whether the fact already existed *in this repo's own files* under a
  different name/framing.
- **Primitive (1) — `Module.Finite`/`Module.Free` for
  `w.adicCompletionIntegers L` over `v.adicCompletionIntegers K` —
  CLOSED.** New file `langlands/Langlands/AdicCompletionIntegralClosure.lean`
  (commit `106870a`), zero `sorry`, `lake build
  Langlands.AdicCompletionIntegralClosure` and full `lake build` both green
  (8670 jobs). Content:
  - `Valuation.isIntegral_imp_map_le_one` (`:67`): the genuinely missing
    "easy direction" — a standalone generalization of the forward direction
    of `Valuation.Integers.isIntegral_iff_v_le_one`
    (`Mathlib/RingTheory/Valuation/Integral.lean`) that drops its bundled
    `exists_of_le_one` surjectivity field (false here: `v.adicCompletionIntegers
    K` is a proper subring of `w.adicCompletionIntegers L` in general, not
    all of it). Proof is the same dominant-term/ultrametric argument as the
    Mathlib original, ported by hand since the `Valuation.Integers`
    structure itself doesn't apply.
  - `isIntegral_iff_mem_adicCompletionIntegers` (`:163`): combines the easy
    direction with `isIntegral_of_mem_of_comap_eq` (`NormMap.lean`) to get
    the full iff.
  - `instIsIntegralClosureAdicCompletionIntegers` (`:187`): the
    `IsIntegralClosure (w.adicCompletionIntegers L) (v.adicCompletionIntegers
    K) (w.adicCompletion L)` instance this unlocks.
  - `instModuleFiniteAdicCompletionIntegers` / `instModuleFreeAdicCompletionIntegers`
    (`:198`, `:204`): from `IsIntegralClosure.finite`/`.module_free`
    (`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`), under an
    added `[Algebra.IsSeparable (v.adicCompletion K) (w.adicCompletion L)]`
    hypothesis — those two Mathlib lemmas are themselves scoped to finite
    *separable* extensions, so this repo's instances inherit that scope.
    Separability is automatic in characteristic `0` (number fields, this
    project's primary target) but not attempted in general (positive
    characteristic local fields can have inseparable extensions).
  - Building this also required constructing, from scratch,
    `Algebra (v.adicCompletionIntegers K) (w.adicCompletion L)` (the
    composite through `v.adicCompletion K`), the matching `IsScalarTower`
    instances, and `Module.IsTorsionFree (v.adicCompletionIntegers K)
    (w.adicCompletion L)` (from injectivity of the algebra map into a field)
    — none of these existed prior to this file, and `IsIntegralClosure.module_free`
    needs the torsion-free instance as a hypothesis.
- **Primitive (2) — formulate unramifiedness for valuation-ring extensions
  (general `e`) — CLOSED (formulation only, not connected to anything
  downstream yet).** New file
  `langlands/Langlands/UnramifiedValuationExtension.lean` (commit `61eab9b`),
  zero `sorry`, builds green. `IsUnramified K L v w : Prop` is defined as
  `𝔪_K · O_L = 𝔪_L` (`Ideal.map (algebraMap K₀ L₀) (maximalIdeal K₀) =
  maximalIdeal L₀`), directly on the algebra structure from primitive (1).
  `map_maximalIdeal_le` proves the containment `𝔪_K · O_L ≤ 𝔪_L` holds
  unconditionally (`IsLocalRing.map_maximalIdeal_le`, using the `IsLocalHom`
  instance already in `ResidueFieldNorm.lean`), so `isUnramified_iff_le`
  reduces `IsUnramified` to the one nontrivial reverse containment. This was
  a much smaller piece than primitive (1) — `Ideal.ramificationIdx'`
  (`Mathlib/NumberTheory/RamificationInertia/Ramification.lean`) turned out
  to already be stated generally enough (any `CommRing`s with an `Algebra`
  instance and any two ideals) to apply directly to `K₀ → L₀`, no new
  ramification-index theory was needed, only the packaging.
- **Compatibility square (does `localNormMap` reduce mod the maximal ideal
  to the `ResidueFieldNorm.lean` residue norm?) — NOT attempted this
  session, per the task's own instruction not to force it.** With
  primitives (1) and (2) now in hand, the determinant/basis route sketched
  in the second-pass entry above is substantially more tractable than it
  was: `Module.Free` (primitive 1) gives an integral basis of `L₀` over
  `K₀`; for a *finite free* module over a local ring, a basis always
  reduces (mod the maximal ideal) to a basis of the quotient — a standard
  Nakayama-type fact, not yet located/proved in this repo. The quotient
  `L₀ ⧸ 𝔪_K·L₀` only equals `𝓀[L] = L₀ ⧸ 𝔪_L` (the residue field target of
  `ResidueFieldNorm.lean`'s norm) **under `IsUnramified`** (primitive 2) —
  this is precisely why unramifiedness is the natural hypothesis for this
  square, matching Serre's scoping of the "easy half" of local CFT. The
  remaining gap, concretely: (a) locate or prove "basis of finite free
  module over local ring reduces to basis of quotient by maximal ideal"
  (Nakayama consequence, likely exists in Mathlib under
  `Module.Free`/`IsLocalRing` somewhere, not checked this session); (b)
  under `IsUnramified`, identify `L₀ ⧸ 𝔪_K·L₀` with `𝓀[L]`; (c) show
  `Algebra.norm K L` (the determinant of the multiplication matrix in the
  chosen basis) reduces mod `𝔪_K` to `Algebra.norm 𝓀[K]` of the reduced
  element in the reduced basis — a determinant-reduces-mod-ideal argument.
  None of (a)-(c) attempted; this is the concrete next-session starting
  point, smaller in scope than the second-pass entry's "route 1" since (1)
  and (2) are now discharged prerequisites rather than open blockers.
- **Full build status**: `grep -rn sorry langlands/Langlands/` empty across
  the whole `Langlands/` tree; full `lake build` green, 8670 jobs.
- **Mathlib-upstreaming candidate flagged** (not attempted, see
  `/home/me/git/rhizone/motif/TODO.md`): `Valuation.isIntegral_imp_map_le_one`
  and the general pattern "a valuation subring extending a base valuation
  ring, in the `Valuation.HasExtension` sense, over a *complete* base field
  in a finite extension, equals the integral closure of the base" look like
  a genuine gap in Mathlib's own `Valuation`/`ValuationSubring` API, not
  specific to this project's `HeightOneSpectrum`/adele setup.

### Phase 2.5 — Satake isomorphism for unramified `GL_n` (new milestone, review addition)
- **Build:** the unramified Hecke algebra `H(GL_n(K_v), GL_n(𝒪_v))` (the
  double-coset convolution algebra of `GL_n(K_v)` relative to the maximal
  compact `GL_n(𝒪_v)`) and the Satake isomorphism identifying it with the
  ring of symmetric polynomials in `n` variables (equivalently, with
  representations of the dual torus/Weyl-invariant functions on it — for
  `GL_n` the dual group is again `GL_n`, so this needs none of Phase 3).
- **Why it goes here:** this is the best value-per-effort item in the whole
  roadmap. It is **self-contained** — needs only `GL_n(K_v)`'s double-coset
  structure, the existing `HeckeRing/Defs.lean` abstract Hecke-ring formalism
  (have, §1.6), and Mathlib's polynomial-ring/symmetric-function library
  (not audited above but standard Mathlib territory) — and it **yields a
  provable theorem**, not just a stated conjecture: the unramified local
  Langlands correspondence (Satake parameters ↔ unramified irreducible
  admissible representations) drops out of the Satake isomorphism directly,
  giving the roadmap its first genuine, non-vacuous local Langlands result
  well before the general Phase 5 statement is reachable.
- **Depends on:** `NumberTheory/HeckeRing/Defs.lean` (have), Phase 4's
  `GL_n`-track admissible representations (for the unramified-representations
  side of the correspondence), `GeneralLinearGroup` (have). Does **not**
  depend on Phase 3.
- **Feeds:** the unramified case of Phase 5's local Langlands statement
  (directly, as a proved special case rather than a stated conjecture), and
  Phase 8's restricted tensor products (an automorphic representation is
  unramified — i.e. has a fixed vector under the maximal compact — at almost
  all places, and the Satake isomorphism is exactly what controls the local
  factor at those places).
- **Size:** medium. Bounded, classical, and well-documented in standard
  references (Bump's *Automorphic Forms*, Gelbart's `GL_2` notes generalize
  cleanly to `GL_n`).
- **Upstreamable:** yes — the Satake isomorphism is a named, citable result
  independent of the rest of Langlands.

### Phase 3 — Reductive groups over a field (the dual-group blocker)
- **Build, in order:**
  1. Algebraic tori (split first: `𝔾_m^n` with a Galois action for
     non-split), as group schemes or as functor-of-points objects.
  2. Root data: pair a torus with the existing `RootSystem` combinatorial
     library (`Mathlib/LinearAlgebra/RootSystem/*` — have) via cocharacter/
     character lattices.
  3. Split reductive groups classified by root data (Chevalley); construct
     `GL_n`, `SL_n`, `Sp_{2n}`, `SO_n` as the running examples on top of the
     existing concrete matrix groups (have, §1.4) to validate the
     abstraction against known cases.
  4. The Langlands dual group `^L G` as the reductive group with dual root
     datum (roots ↔ coroots swapped); for split `G`, `^L G` needs no Galois
     action, for quasi-split/general `G` the dual carries an action of
     `Gal(K̄/K)` on the based root datum (needs Phase 1's Galois group +
     pinnings/automorphisms of the root datum — new).
- **Depends on:** `LinearAlgebra/RootSystem/*` (have), `GeneralLinearGroup`/
  `SpecialLinearGroup` (have, as validation targets), `AbsoluteGaloisGroup`
  (have, for step 4), essentially nothing else in Mathlib — this is mostly
  new development on top of the root-system library.
- **Size:** huge. This is comparable in scope to formalizing a chapter of
  Springer's *Linear Algebraic Groups* or Conrad's reductive-groups notes.
  Plausibly the single biggest piece of the entire roadmap. Can be
  meaningfully de-scoped: build split reductive groups classified by root
  data first (skip general algebraic-group/scheme foundations, skip
  non-split forms), which is enough to state local/global Langlands for
  quasi-split groups — the case almost all conjecture *statements* (not
  proofs) are given in.
- **Upstreamable:** yes, extremely high-value — Mathlib has no reductive
  group theory at all; this would be a foundational new area, not a
  patch to an existing one. Also the piece most likely to already be
  wanted by other Mathlib contributors (algebraic geometry / Lie theory
  communities) — worth checking Mathlib's Zulip/roadmap for parallel effort
  before starting, since duplicating a large in-flight project would be
  the worst outcome here.
- **Reframing (review):** this is not a project phase in the same sense as
  the others in this roadmap — it is a **Mathlib-core campaign**. The dual
  group `^L G` needs Chevalley existence/uniqueness for reductive groups
  built from root data, and that is Mathlib's largest relevant crater: as of
  this writing there is no settled maintainer consensus even on the base
  definitions (what a "reductive group" *is* as a Mathlib structure — scheme-
  theoretic vs. functor-of-points vs. combinatorial-root-datum-first — is an
  open design question upstream, not just an unfilled gap). Treating Phase 3
  as a phase this project completes on its own timeline is the wrong frame;
  treating it as an upstream Mathlib contribution this project seeds and
  budgets for indefinite duration is the right one.
  - **Mitigation (a) — decouple the Galois layer from group existence.**
    Define `^L G` *combinatorially* now: a dual root datum, built directly on
    the existing `RootSystem` API (have, §1.4), with the Galois action on it
    given by an action on the abstract based root datum (needed anyway for
    step 4 above). This lets everything downstream that only needs `^L G` as
    a group *with a root datum* (L-parameters, functoriality maps between
    dual sides) proceed without waiting on Chevalley's theorem — i.e. without
    waiting on `G` itself existing as a bona fide reductive group object.
    Only the "transfer of representations of `G(K_v)` itself" side of local
    Langlands needs `G`, not `^L G`, to exist as a group scheme.
  - **Mitigation (b) — budget, don't schedule.** Treat full Phase 3 (Chevalley
    existence + uniqueness for general reductive groups) as an upstream
    Mathlib contribution with its own review cycle and timeline, not a task
    this roadmap can complete unilaterally. Phase 7 (Galois cohomology
    packaging) correctly feeds only the non-split-forms case of Phase 3 and
    can lag indefinitely without blocking anything else in this roadmap.

### Phase 4 — Smooth and admissible representations of `p`-adic / adelic groups
- **Build:** for a locally profinite group `H` (e.g. `G(K_v)` once Phase 3
  exists, or concretely `GL_n(K_v)` before Phase 3 lands), a smooth
  representation = a representation on which every vector is fixed by some
  compact open subgroup; admissible = smooth + finite-dimensional fixed
  spaces under every compact open subgroup.
- **Depends on:** `RepresentationTheory/Continuous/{Basic,TopRep}.lean`
  (have — specialize `TopRep` to locally profinite groups and add the
  smoothness condition), `ProfiniteGrp`/compact-open-subgroup topology
  (have, for `GL_n` over `Padics`, §1.2).
- **Size:** medium–large for the `GL_n`-only version (usable immediately,
  doesn't wait on Phase 3); large again for the general-`G` version once
  Phase 3 exists (parabolic induction, Jacquet modules, supercuspidal
  support, Bernstein decomposition needed for the *full* local Langlands
  statement with L-packets, though the bijection can be *stated* for
  `GL_n` without any of that extra machinery, since local Langlands for
  `GL_n` is a clean bijection with no packets).
- **Upstreamable:** yes — smooth/admissible representation theory of
  `p`-adic groups is foundational and wanted independently of Langlands.

### Phase 4.5 — Local L-factors and ε-factors (review addition — vacuity fix for Phase 5)
- **Why this phase exists:** a bare bijection between `L`-parameters and
  irreducible admissible representations of `GL_n(K_v)`, with no further
  structure, is **vacuously true by cardinality** — both sides are countably
  infinite sets, so *some* bijection trivially exists with no mathematical
  content. The actual content of local Langlands for `GL_n` (this is
  Henniart's uniqueness theorem territory) lives in the correspondence being
  the *unique* bijection compatible with: twisting by characters, duality
  (contragredient ↔ dual representation), central characters
  (determinant ↔ central character under class field theory), and
  **preservation of L-factors and ε-factors of pairs** under the
  correspondence. Without this phase, Phase 5 cannot distinguish a genuine
  statement of local Langlands from a cardinality triviality.
- **Build:** local L-factors `L(s, ρ)` and Deligne–Langlands ε-factors
  `ε(s, ρ, ψ)` for Weil–Deligne representations `ρ`, and their representation-
  theoretic counterparts (Rankin–Selberg / Godement–Jacquet local factors)
  for admissible representations of `GL_n(K_v)` and `GL_n(K_v) × GL_m(K_v)`
  pairs.
- **New prerequisites, confirmed missing:** additive characters of `K_v`
  (have for `K_v = ℚ_p` via `Padics/AddChar.lean`, §1.2, but not for general
  local fields), a Haar measure normalization convention (Tate's thesis
  requires a self-dual measure with respect to the chosen additive
  character — flagged as missing in §1.3), and the local functional equation
  relating `L(s, ρ)` to `L(1-s, ρ^∨)` via the ε-factor.
- **Convention hazard, flagged for whoever picks this up:** Tate's original
  thesis normalization and Deligne's later ε-factor formalism (*Les
  constantes des équations fonctionnelles des fonctions L*, Antwerp II)
  diverge in bookkeeping conventions (choice of additive character, measure
  normalization, and sign/exponent conventions on the local root number) —
  this is a well-known source of errors in the literature, so the Lean
  definitions must pin down *which* convention is being formalized and state
  it explicitly rather than silently inheriting one source's choices.
- **Depends on:** Phase 1 (Weil–Deligne group, for the Galois side), Phase 4
  (admissible representations of `GL_n(K_v)`, for the automorphic side),
  `Padics/AddChar.lean` and `Padics/Measure/*` (have, for `ℚ_p`; need
  extending to general local fields), `NumberTheory/LSeries/
  AbstractFuncEq.lean` (have, potential scaffold for the functional
  equation).
- **Size:** large — this is a full local-constants theory, comparable in
  scope to a chapter of Bushnell–Henniart's *The Local Langlands Conjecture
  for GL(2)* or Tate's Corvallis article.
- **Upstreamable:** yes — local L- and ε-factors are foundational and wanted
  independently (Tate's thesis itself is a natural, self-contained Mathlib
  target).

### Phase 5 — Statement of local Langlands for `GL_n`
- **Build:** the conjecture-as-a-`Prop`: a bijection between (continuous,
  Frobenius-semisimple, Weil–Deligne) `n`-dimensional representations of
  `W_{K_v}` and irreducible admissible representations of `GL_n(K_v)`,
  compatible with L-functions and ε-factors on both sides (the compatibility
  clause can initially be omitted/stubbed to get the bare bijection
  statement first).
- **Vacuity caveat (review) — acceptance test:** per Phase 4.5 above, a bare
  bijection is **not an acceptable formalization goal on its own** — both
  sides are countably infinite, so a bijection exists trivially by
  cardinality with zero mathematical content. Two ways to avoid shipping a
  vacuous statement:
  1. Do the full version: require Phase 4.5's L-factor/ε-factor compatibility
     clauses (plus twisting, duality, central-character compatibility) as
     part of the `Prop`, so the bijection is characterized, not just
     asserted. This is Henniart's uniqueness theorem and is the
     mathematically honest statement of local Langlands for `GL_n`.
  2. Or explicitly scope Phase 5 as "the bijection statement up to
     characterization" — i.e. keep the bare bijection as an intentionally
     weaker placeholder, but **label it as such in the `Prop`'s
     documentation** (e.g. a doc-comment noting "this statement, absent the
     compatibility clauses of Phase 4.5, is a cardinality triviality and
     should not be cited as a formalization of local Langlands without
     them"), so nobody downstream mistakes the placeholder for the theorem.
  Either path is acceptable; shipping the bare bijection *without* one of
  these two markers is not — that is exactly the failure mode this
  correction targets.
- **Depends on:** Phase 1 (Weil–Deligne group), Phase 4's `GL_n`-only track
  (admissible reps of `GL_n(K_v)`), Phase 4.5 (L-/ε-factors, for the
  non-vacuous version), existing `GeneralLinearGroup` (have).
  **Does not need Phase 3** — this is exactly why `GL_n` is the right first
  target: its own dual group is itself.
- **Size:** small, once Phases 1 and 4 (`GL_n` track) exist, *for the bare
  bijection*; the non-vacuous version additionally needs Phase 4.5, which is
  large. This phase is "just" writing the `Prop` only in the weak sense —
  writing the `Prop` that is actually worth writing is gated on Phase 4.5.
- **Upstreamable:** yes, as a formalized *conjecture statement* (a `Prop`/
  axiom-free `def`, not a `sorry`-laden proof) — valuable in its own right
  as a landmark for the Mathlib number theory community, independent of any
  progress toward proving it, **provided** the vacuity caveat above is
  respected.

### Phase 6 — Statement of Artin's conjecture
- **Build:** Artin `L`-function of an `n`-dimensional Galois representation
  `ρ : Gal(K̄/K) → GL_n(ℂ)` (Euler product over unramified primes using
  Frobenius eigenvalues from `RingTheory/Frobenius.lean`, plus local factors
  at ramified primes needing the **inertia-invariants** of `ρ` restricted to
  `W_{K_v}` — needs Phase 1); state "`L(s, ρ)` equals `L(s, π)` for some
  automorphic representation `π` of `GL_n(𝔸_K)`" (needs Phase 8's global
  automorphic-representation notion, or can be stated over `GL_1` alone
  first, which reduces to classical Hecke-character CFT and needs only
  Phase 0 + Phase 2).
- **Depends on:** Phase 1, Phase 2 (for the `n=1` reduction — Artin's
  conjecture for 1-dim reps is essentially class field theory, already a
  theorem, not a conjecture, once Phase 2 lands), `NumberTheory/LSeries/
  AbstractFuncEq.lean` (have, as a scaffold for the L-function's analytic
  side), Phase 8 for `n > 1`.
- **Size:** medium for `n=1` statement/proof (mostly repackaging Phase 0/2);
  large for general `n` statement (needs Phase 8).
- **Upstreamable:** yes — Artin `L`-functions are independently notable.

### Phase 7 — Galois cohomology packaging (parallel track, low risk)
- **Build:** name and package `Gal(L/K)`-module cohomology as "Galois
  cohomology" explicitly (thin wrapper over `ContCohomology` +
  `AbsoluteGaloisGroup`), including inflation-restriction, and connect
  `Hilbert90.lean` to the `H^1(Gal, GL_n)`-classifies-forms statement
  (relevant to inner forms / non-quasi-split reductive groups in Phase 3).
- **Depends on:** `RepresentationTheory/Homological/ContCohomology/*`
  (have), `AbsoluteGaloisGroup` (have), `GroupCohomology/Hilbert90.lean`
  (have).
- **Size:** small–medium. Can run **in parallel** with Phases 0–2; no
  dependency either direction except that Phase 3's non-split forms will
  eventually want it.
- **Upstreamable:** yes, cheap win — Mathlib already has all the pieces,
  just not the "Galois cohomology" framing/API surface.

### Phase 8 — Automorphic representations of `G(𝔸_K)` and statement of global Langlands
- **Build:** automorphic forms/representations for general reductive `G`
  (functions on `G(K)\G(𝔸_K)` satisfying finiteness/growth/smoothness
  conditions, decomposed into irreducible representations of `G(𝔸_K)`);
  reconcile with the classical modular-forms library (§1.6) for `G = GL_2`
  as the validating special case; state the global correspondence as a
  `Prop` relating automorphic representations to (compatible systems of)
  Galois representations, using local Langlands (Phase 5, generalized via
  Phase 3+4) at each place for compatibility.
- **Depends on:** Phase 0 (adeles/idele class group), Phase 3 (reductive
  groups, for general `G`; `GL_2` case can lean on existing modular forms
  instead), Phase 4 (admissible representations, adelic/restricted-tensor-
  product version — new content: an automorphic representation is a
  restricted tensor product of local admissible representations, which
  needs its own "almost all factors unramified" bookkeeping).
- **Acceptance criteria (review) — vacuity test:** "automorphic
  representations" defined as a bare restricted tensor product of local
  admissible representations, with no further structure, is a definition
  with no theorem in it — it says nothing about which restricted tensor
  products actually arise from genuine automorphic forms. The content that
  must be present before this phase counts as done:
  - **Cuspidality:** the subspace of cusp forms (vanishing constant terms
    along all proper parabolics) must be identified, since the cuspidal
    spectrum is where the representation theory is discrete and where local
    Langlands packets are meant to land; without it, "automorphic
    representation" has no home for the actual correspondence.
  - **Multiplicity:** the multiplicity of an irreducible representation in
    the (cuspidal) automorphic spectrum must be at least stated as a
    quantity (finite for cuspidal, by a Gelfand-pair/discrete-spectrum
    argument), even if multiplicity-one (known for `GL_n`, false in general)
    is deferred as a separate theorem.
  - **L² structure:** the decomposition of `L²(G(K)\G(𝔸_K))` (or its
    central-character-twisted variant) into a direct sum/integral of
    irreducibles — discrete spectrum (cuspidal + residual) plus continuous
    (Eisenstein) spectrum — needs to be at least stated, since "automorphic
    representation" without reference to this decomposition is just "some
    representation of `G(𝔸_K))`," not the object Langlands' conjectures are
    about.
  Absent these three, Phase 8 produces a restricted tensor product with no
  theorem attached to it — a definition that type-checks but proves nothing
  and characterizes nothing. These three items should be treated as the
  minimum bar for calling Phase 8 "done" rather than "stated."
- **Size:** huge — the single most mathematically demanding phase, on par
  with or larger than Phase 3. Realistically this is where "prove what we
  can" gives way to "state what we can" for the foreseeable future.
- **Upstreamable:** yes, high-value, but high risk of drift/duplication
  with any parallel effort elsewhere (geometric Langlands formalization
  projects exist outside Mathlib, e.g. in other proof assistants and in
  active math research — worth a literature/community check before
  committing large effort here specifically).

### Phase 9 — Functoriality statement
- **Build:** given `L`-map `^L H → ^L G` (a homomorphism of dual groups from
  Phase 3), state functorial transfer of automorphic representations
  (Phase 8) and/or of L-parameters (Phase 5, generalized).
- **Depends on:** Phase 3 (dual groups + homs between them), Phase 5/8
  generalized to arbitrary reductive `G`.
- **Size:** small once Phases 3, 5 (generalized), and 8 exist — again,
  "just" the `Prop`, but it sits at the end of the longest dependency chain
  in the whole roadmap.
- **Upstreamable:** yes.

---

## 4. Roadmap dependency graph (summary)

```
Phase 0 (idele class group) — COMPLETE ────────────────┐
   built: IdeleGroup/IdeleClassGroup, norm maps          │
   (finite + archimedean places), unramified-ext.        │
   correspondence, Henselian valuation compat.           ▼
Phase 1 (Weil/Weil–Deligne group) — COMPLETE            Phase 2 (local CFT / Artin map)
   built: WeilGroup, WeilDeligneRepresentation             depends on: Phase 1 (done), BrauerGroup
   depends on: AbsoluteGaloisGroup (have),        (have), Hilbert90 (have) — scope: also norm
   ProfiniteGrp (have), Frobenius (have)          functoriality + Frobenius compat (Serre
        │                                          Local Fields VIII–XIII); norm maps +
        │                                          unramified-ext. correspondence now available
        │                                          (Phase 0) as down payment; check FLT-adjacent
        │                                          CFT formalization before building
        │                                                │
        │                                                ▼
        │                                       Phase 2.5 (Satake isomorphism for
        │                                       unramified GL_n — new, self-contained,
        │                                       first PROVABLE unramified LLC)
        ├──────────────┬─────────────────────────────────┘
        ▼              ▼
Phase 4.5 (local L-/ε-factors — new, fixes  Phase 6 (state Artin conj., n=1 track
Phase 5 vacuity; needs additive characters,   reduces to Phase 0+2; n>1 needs Phase 8)
Haar normalization, functional equation;
Tate-vs-Deligne convention hazard flagged)
        │
        ▼
Phase 5 (state local Langlands for GL_n —
bare bijection is VACUOUS by cardinality;
needs Phase 4.5's compatibility clauses or
an explicit "up to characterization" label)
        ▲
        │
Phase 4 (smooth/admissible reps; GL_n track needs no Phase 3)
        ▲
        │
Phase 3 (reductive groups + dual group)  ◄── Mathlib-CORE CAMPAIGN, not a project
   depends on: RootSystem (have), GeneralLinearGroup (have), AbsoluteGaloisGroup (have)   phase: Chevalley existence/uniqueness has
        │                                                                                  no settled upstream maintainer consensus.
        ▼                                                                                  Mitigation: define ^L G combinatorially now
Phase 4 (general-G track)  ──►  Phase 8 (automorphic reps, global Langlands —              via dual root datum (decouples from Chevalley);
acceptance test: needs cuspidality,           ──►  Phase 9 (functoriality)                 budget rest as upstream PR, not in-repo work.
multiplicity, L² structure — bare restricted
tensor product has no theorem in it)
                                        ▲
                                        │
                                 Phase 0 (idele class group)

Phase 7 (Galois cohomology packaging) — parallel, low-risk, feeds Phase 3's non-split-forms case only, can lag indefinitely.
```

Everything downstream of Phase 3 for **general `G`** is gated on Phase 3.
Everything needed to state local/global Langlands **for `GL_n` specifically**
(Phases 0, 1, 2, 2.5, 4-GL_n-track, 4.5, 5, 6-n=1-track) can proceed without
ever touching Phase 3 — this is the practical route to "formally state the
core conjectures" fastest, deferring the huge, contested Phase 3 (general
reductive groups, reframed above as a Mathlib-core campaign rather than a
project phase) and Phase 8 (general automorphic representations) until later
or indefinitely, while still landing a real, citable formal statement of
local Langlands for `GL_n` and (via Phase 2) a fully *proved* class field
theory. Phase 2.5 (Satake for unramified `GL_n`) is flagged separately as
the single best value-per-effort item in the graph: self-contained, needs no
Phase 3, and yields an actually-provable theorem rather than another stated
conjecture.

---

## 5. The first move

**Status update: Phase 0 (idele class group) and Phase 1 (Weil group /
Weil–Deligne group) are both done.** `IdeleGroup`/`IdeleClassGroup` are
built in `Langlands/IdeleGroup.lean`, sorry-free, along with local norm maps
at finite and archimedean places, the idele-group norm map, the
Kedlaya–Sutherland unramified-extension correspondence, and rank-one
valuation compatibility. The Weil group is built in `Langlands/WeilGroup.lean`,
and the Weil–Deligne representation formalism — `LocalField.
WeilDeligneRepresentation K V`, bundling `ρ`, nilpotent `N`, and the
intertwining relation — is built in `Langlands/WeilDeligneRepresentation.lean`.
Both are sorry-free (see Phase 0 and Phase 1 status above).

**Next move: begin Phase 2 (local class field theory / the local Artin
map).**

Concretely: build the local reciprocity map `K_v^× → Gal(K_v^ab/K_v)` (or
its Weil-group refinement `K_v^× ≅ W_{K_v}^ab`), on top of the now-complete
`WeilGroup`, drawing on this project's norm-map and unramified-extension
infrastructure (`Langlands/NormMap.lean`, `Langlands/UnramifiedExtension.lean`)
as a down payment on the norm-functoriality and Frobenius-compatibility
characterizing properties the map needs (see Phase 2's scope correction
above). Before writing new proofs, check for prior formalization of local/
global CFT elsewhere (e.g. around the Mathlib `FLT` project) — duplicating
an in-flight effort would be the most wasteful outcome available here.

This is the correct next move because:
- It is **the only remaining prerequisite gate before Phase 3+ becomes
  meaningful** — every phase in this roadmap can already be *stated* with
  the Artin map axiomatized, but Phase 2 is required to make any of it
  *proved* rather than vacuous (see Phase 2's note above).
- It has **more prerequisites in place than any point so far** — Phase 1
  (Weil group), the Brauer group, and Hilbert's Theorem 90 are all
  available in Mathlib, and this project's own norm-map and
  unramified-extension infrastructure is a direct down payment on Phase 2's
  hardest characterizing properties.
- It is **independently upstreamable and high-value** — local class field
  theory is a named, citable theorem many other formalization efforts would
  want, the same way the Weil group, Weil–Deligne representation, and idele
  class group already are.
- It carries a **real risk of duplicated effort** that's cheap to check for
  up front but expensive to discover after building — hence checking for
  prior/in-flight CFT formalization is the first concrete step, not an
  afterthought.
