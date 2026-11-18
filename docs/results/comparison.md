# Comparison with Mathlib and Tau Ceti

What each headline and each part of the books in this release adds to [Mathlib](https://github.com/leanprover-community/mathlib4)
and to [Tau Ceti](https://github.com/TauCetiProject/TauCeti). The comparison was made on 2026-11-07 by reading the
statements (not only the names) in Mathlib master at commit `df6966d0d` and Tau Ceti main at commit `d7b47803c`.
This library is built on Mathlib v4.35.0; Tau Ceti uses a later Lean and Mathlib and cannot be imported here, so the
Tau Ceti files this library needs are ported (`NumberFieldKB/TauCetiPort/`, see `NOTICE`).

The class field theory headlines (three in release 0.2.0; Theorem VIII.2.6, local Kronecker–Weber, Eisenstein reciprocity and Furtwängler's theorem, below, were library theorems in 0.2.0 and are headlines from 0.2.1) were compared on 2026-11-08 with Tau Ceti at commit
`686d0d7f` and Mathlib at `df6966d`, again by reading statements. Tau Ceti now has global and local class field
theory (`NumberTheory/ClassFieldTheory/`: the global Artin map and reciprocity, global and local existence, the
Kronecker–Weber theorem, ray class fields, the inequalities), so those theorems are not headlines here.

The headlines of Milne's *Elliptic Curves* (new in 0.3.0) were compared on 2026-11-15 with Mathlib master at commit
`4cf60f1d` and Tau Ceti main at commit `4caf68dc`. Mathlib master adds no elliptic-curve declaration to v4.35.0. Tau
Ceti proves much of the arithmetic of the book (Mordell–Weil over every number field, finiteness of Selmer groups, the
Néron–Tate height, the Weil pairing, the torsion structure, the Hasse bound and the zeta function over finite fields,
Nagell–Lutz, complex uniformization, Tate's algorithm); those results are cited in the map, not re-proved, and are not
headlines here. The statements of Birch and Swinnerton-Dyer were compared with
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) at commit `e028240a`, whose definitions
are vendored (`NumberFieldKB/FormalConjectures/`).

The headlines new in 0.4.0 were compared on 2026-11-17 with Mathlib master at commit `d9a73ae1` and Tau Ceti main at
commit `7b4d5f70`. Mathlib master still adds nothing on the arithmetic of elliptic curves to v4.35.0 (it has heights,
`NumberTheory/Height/EllipticCurve.lean`). Tau Ceti main has, besides the results listed above, Tate's algorithm with
the local Tamagawa number (`WeierstrassCurve.tamagawaNumber_eq_tateLocalIndex`), the real period as an integral
(`WeierstrassCurve.realPeriod`), its own statement of Birch and Swinnerton-Dyer (`WeierstrassCurve.BirchSwinnertonDyer`),
and the explicit unramified local Artin map (`TauCeti.ClassFieldTheory.localArtinMap_eq_frobenius_pow_valuation`); it has no measure of
$`E(\mathbb Q_p)`$, no lattice of the real period, no Tate–Shafarevich group of a specific curve and no list of the
torsion groups that occur.

The headlines new in 0.4.1 were compared on 2026-11-18 with Mathlib master at commit `ce8351d4` and Tau Ceti main at
commit `cd41bffc`. Mathlib master has the Tate–Shafarevich group of a Galois module
(`RepresentationTheory/Homological/ContCohomology/Sha.lean`), nothing on the arithmetic of elliptic curves beyond
v4.35.0. Tau Ceti main has its own Tate–Shafarevich and Selmer groups over number fields (with their independence of
the chosen embedding of separable closures), the Kummer map $E(K)/mE(K) \to H^1(K, E[m])$ and its own statement of
Birch and Swinnerton-Dyer; it has no comparison of these with Milne's or Formal Conjectures' formalizations, no
injectivity of $H^1(\operatorname{Gal}(\bar K_v/K_v), E(\bar K)) \to H^1(\operatorname{Gal}(\bar K_v/K_v), E(\bar K_v))$,
and no approximation of local points by algebraic points.

A search of two large libraries can miss a result stated under another name or in another form; corrections are
welcome.

## Headlines

| headline | Mathlib | Tau Ceti | this release |
|---|---|---|---|
| `kummer_regular` | Fermat's Last Theorem for the exponents 3 and 4 (`fermatLastTheoremThree`, `fermatLastTheoremFour`) | — | new: the first case of Fermat's Last Theorem for every regular prime (Kummer, Milne Theorem 6.8). Outside both libraries, the flt-regular project formalized Fermat's Last Theorem for regular primes on an earlier Mathlib. |
| `dedekind_factorizationType` | — | over $\mathbb Q$: for $f \in \mathbb Z[X]$ monic and $p \nmid \operatorname{disc} f$, some Galois element has the factorization type of $f \bmod p$ (`exists_gal_fullCycleType_eq_factorizationType`, `NumberTheory/NumberField/Frobenius/CycleType.lean`) | stronger: over every number field $K$, for $f$ monic over $\mathcal O_K$ and every prime $\mathfrak p$ with $f \bmod \mathfrak p$ squarefree |
| `ostrowski_numberField` | Ostrowski's theorem over $\mathbb Q$ (`Rat.AbsoluteValue.equiv_real_or_padic`) and over $k(t)$ (`NumberTheory/RatFunc/Ostrowski.lean`) | the absolute values of a finite extension lying over a given finite place (`NumberField.existsUnique_finitePlace_rpow_inv_eq_of_liesOver`) | new: the places of every number field are its primes and its real and complex embeddings up to conjugation (a bijection onto the classes of nontrivial absolute values) |
| `adeles_selfDual` | the adele ring | the adeles, $K$ discrete in $\mathbb A_K$ with compact quotient (`NumberTheory/NumberField/Global/Adeles/`) | new: every character of $\mathbb A_K$ is $x \mapsto \chi(ax)$ for a unique $a$, and the annihilator of $K$ is $K$ |
| `idele_classes_finite` | finiteness of the class group | the $S$-ideles and their Herbrand quotient (class field theory) | new in Weil's form: $\mathbb A_K^\times / K^\times\Omega(P)$ is finite |
| `zeta_functionField` | — | the zeta function of an elliptic curve over a finite field (`AlgebraicGeometry/EllipticCurve/Isogeny/Frobenius/Zeta.lean`); finiteness of the divisor class number of a function field (`FieldTheory/FunctionField/RiemannRoch/ClassNumber.lean`) | new: rationality, $Z(u)(1-u)(1-qu) = P(u)$ with $\deg P = 2g$, $P(0) = 1$, $P(1) = h$, and the functional equation, for every function field of one variable over a finite field |
| `heckeL_functionField_polynomial` | — | — | new: the Hecke L-function of a ramified character of a function field is a polynomial of degree $2g - 2 + \deg\mathfrak f$ |
| `tate_globalZeta_functionalEquation` | — | — | new: Tate's main theorem, meromorphic continuation and functional equation of the global zeta integral $Z(\Phi, \chi, s)$ |
| `tate_globalZeta_residues` | — | — | new: the poles and residues of the global zeta integral |
| `heckeL_functionalEquation` | Dirichlet L-functions over $\mathbb Q$: continuation and functional equation (`DirichletCharacter.completedLFunction_one_sub`) | Hecke L-functions of ray class characters defined as the canonical meromorphic continuation, with comparisons between presentations (`LFunctions.heckeLFunctionC`); no continuation is proved and no functional equation is stated | stronger: continuation, holomorphy and functional equation $\Lambda(s,\chi) = W(\chi)\Lambda(1-s,\chi^{-1})$ with $\lvert W(\chi)\rvert = 1$ for the Hecke characters of every number field |
| `dedekindZeta_continuation` | the limit of $(s-1)\zeta_K(s)$ at $s = 1$ (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) | continuation to $\operatorname{Re} s > 1 - 1/[K:\mathbb Q]$ (`exists_differentiableOn_eq_dedekindZeta_sub`); continuation to $\mathbb C \setminus \{1\}$ for quadratic fields, as $\zeta \cdot L(\chi)$ (`LFunctions.dedekindZetaC_eq_riemannZeta_mul_LFunction`) | stronger: continuation to $\mathbb C \setminus \{1\}$ for every number field, with a simple pole of residue Mathlib's `dedekindZeta_residue` |
| `completedDedekindZeta_functionalEquation` | the completed Riemann zeta function ($K = \mathbb Q$) | as above | new: $\Lambda_K(1-s) = \Lambda_K(s)$ for every number field |
| `pontryaginDuality` | the Pontryagin dual; duality for finite abelian groups | Bochner's theorem, uniqueness of measures from their transforms, the Peter–Weyl theorem (all three ported here); no duality theorem | new: $G \to G^{**}$ is an isomorphism of topological groups for every locally compact abelian group |
| `fourierInversion_dualMeasure` | Fourier inversion on finite-dimensional real inner product spaces | — | new: the dual Haar measure and Fourier inversion on every locally compact abelian group |
| `pontryagin_closedSubgroups` | — | — | new: annihilators of closed subgroups ($H^{**} = H$, $H \cong (G^*/H^*)^*$, open/compact and compact/open correspondences, $G/H$ compact iff $H^*$ discrete) |
| `compact_iff_dual_discrete` | the directions from $G$ to $G^*$ (instances in `Topology/Algebra/PontryaginDual.lean`) | — | extends: the converses, so both are equivalences |
| `genus_X0` | — | the index $[\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N)]$, the numbers of elliptic points and cusps of $\Gamma_0(N)$, the topological Riemann–Hurwitz formula, the genus 0 of $X(1)$ | new: the genus formula $12g = 12 + \mu - 3\nu_2 - 4\nu_3 - 6\nu_\infty$ for $X_0(N)$ over $\mathbb Q$, with $g$ the genus in the sense of Riemann's theorem |
| `modularPolynomial_rational` | — | — | new: the modular polynomial $F_N$ has rational coefficients, degree $[\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N)]$ and is minimal |
| `modularFunctions_Gamma0` | — | the $j$-function on the upper half plane (`Analysis/Complex/ModularForms/LevelOne/JInputs.lean`) | new: the modular functions for $\Gamma_0(N)$ are the rational functions of $j$ and $j_N$ |
| `cuspForms_weightTwo_finrank` | the spaces of cusp forms (`CuspForm`, used in the statement) | relations between the dimensions of modular forms and cusp forms for $\Gamma_1(N)$ (`EisensteinSeries/Dimension.lean`) | new: $\dim S_2(\Gamma_0(N)) = g(X_0(N))$ |
| `grunwaldWang` | — | — (no Grunwald–Wang theorem; the idele congruence subgroups used in the proof are ported from Tau Ceti) | new: characters of $C_K$ with prescribed local components at finitely many places, of the least possible order outside Wang's special case (Milne VIII.2.4) |
| `centralDivisionAlgebra_cyclic` | central simple algebras and the Brauer group of a field | the fundamental exact sequence $0 \to \mathrm{Br}\,K \to \bigoplus_v \mathrm{Br}\,K_v \to \mathbb Q/\mathbb Z \to 0$ for the cohomological Brauer group (`brLocalization_injective`, `range_brLocalization`, `sumLocalInv_surjective`, `NumberTheory/ClassFieldTheory/Global/Brauer/`); cyclic classes of relative Brauer groups (`relBrInfl_cyclicClass`) | new: period equals index and every central division algebra over a number field is cyclic (Albert, Brauer–Hasse–Noether; Milne VIII.2.6) |
| `localKroneckerWeber_lubinTate` | — | local class field theory without Lubin–Tate theory: the local Artin map, local existence (`localExistence`, `NumberTheory/ClassFieldTheory/LocalExistence/Existence.lean`), the cyclotomic Artin symbol over $\mathbb Q_p$; no Lubin–Tate formal groups | new in Milne's form: $K^{\mathrm{ab}} = K_\pi K^{\mathrm{un}}$ for every nonarchimedean local field and every prime element, with the Lubin–Tate tower (Milne I.4.8). The Lubin–Tate extension theorem (Milne I.3.6) is proved from a port of N. Yamaguchi's class field theory library, whose local Kronecker–Weber theorem is over $\mathbb Q_p$ |
| `eisensteinReciprocity` | quadratic reciprocity (Legendre and Jacobi symbols) | the Eisenstein-primary normalisation and Stickelberger preliminaries (`IsEisensteinPrimary`, `NumberTheory/NumberField/Cyclotomic/EisensteinPrimary.lean`); cubic reciprocity (`IsPrimaryEisenstein.cubic_reciprocity`); no general Eisenstein law | new: Eisenstein reciprocity for every odd prime $p$ |
| `furtwangler_fermat` | Fermat's Last Theorem for the exponents 3 and 4 | — (its `Furtwängler` files are the transfer theorem behind the principal ideal theorem, a different result) | new: Furtwängler's congruence $q^{p-1} \equiv 1 \pmod{p^2}$ for primes dividing a first-case solution (Milne VIII.5.14) |
| `gauss_cubicCurve_count` | Jacobi sums (`jacobiSum_mul_jacobiSum_inv`) | Jacobi sums are Eisenstein-primary (`isPrimaryEisenstein_jacobiSum`) | new: Gauss's count of the points of $X^3 + Y^3 + Z^3 = 0$ over $\mathbb F_p$ |
| `weberL_continuation` | $L(1,\chi) \ne 0$ for Dirichlet characters over $\mathbb Q$ (`DirichletCharacter.LFunction_apply_one_ne_zero`) | Hecke $L$-functions of ray class characters as the canonical meromorphic continuation (`heckeLFunctionC`), analytic on $\operatorname{Re} s > 1$, with no continuation proved; non-vanishing at $s = 1$ assuming a continuation (`ne_zero_of_eqOn_LSeries_galoisCharacterWeight`) | stronger: for every number field and every nontrivial ray class character, the Weber series continues to $\operatorname{Re} s > 0$ (in fact the continuation is entire) and $L(1,\chi) \ne 0$ (Milne V.2.4(b), corrected) |
| `bezout` | resultants (`Polynomial.resultant`); no intersection numbers of plane curves | — | new: Bézout's theorem for projective plane curves over every field, with intersection numbers over $k^{\mathrm{al}}$ (Milne I.1.18) |
| `chordTangent_assoc` | the group law of a Weierstrass curve (`WeierstrassCurve.Affine.Point`) | the group law of Weierstrass curves | new: associativity of the chord–tangent law on every nonsingular plane cubic, not necessarily in Weierstrass form (Milne I.3.1) |
| `rank_bound_twoDescent` | — | Mordell–Weil over every number field (`WeierstrassCurve.Affine.fg_point_of_numberField`) and finiteness of Selmer groups (`WeierstrassCurve.finite_selmerGroup`); no explicit rank bound | new: the rank bound $r \le 2\,\#\{p \mid 2\Delta\}$ of explicit 2-descent (Milne IV.5.5), with finite generation proved by Milne's descent |
| `points_x3_sub_x` | — | Nagell–Lutz (`WeierstrassCurve.lutz_nagell`), which bounds torsion, not the rank | new: $E(\mathbb Q) \cong (\mathbb Z/2)^2$ for $y^2 = x^3 - x$ (Milne IV.5.7) |
| `one_not_congruent` | Fermat's Last Theorem for the exponent 4 (`fermatLastTheoremFour`), a classically equivalent statement in another form | — | new in this form: no right triangle with rational sides has area 1 |
| `lang_H1_eq_zero` | Galois cohomology in low degrees | the Frobenius endomorphism of $E$ over a finite field; no vanishing of $H^1$ | new: $H^1(k, E) = 0$ over every finite field $k$ (Lang; Milne IV.9.2) |
| `bsd_milne_iff_strongBSD` (conditional) | the $L$-series of an elliptic curve as a Dirichlet series | a statement of the conjecture (`BirchSwinnertonDyer`) | new: Milne's Conjecture IV.10.5 (standard normalization) is equivalent to Formal Conjectures' `StrongBSD`, given three named comparisons |
| `selmer_sha_x3_add_px` (new in 0.4.0) | — | Selmer groups and $Ш$ over every number field, finiteness of $Ш[m]$ (`WeierstrassCurve.finite_torsionBy_sha`); no Selmer or Tate–Shafarevich group of a specific curve | new: for $y^2 = x^3 + px$, $p \equiv 1 \pmod 8$: $S^{(2)} \cong (\mathbb Z/2)^3$, and rank 0 with $Ш[2] \cong (\mathbb Z/2)^2$ when 2 is not a fourth power mod $p$ (Milne IV.8.1, IV.8.2; Silverman X.6.2) |
| `omega_measure_zeroComponent` (new in 0.4.0) | Haar measure on $\mathbb Q_p$; minimal models and reduction types | Tamagawa numbers and Tate's algorithm (`tamagawaNumber_eq_tateLocalIndex`); no measure on $E(\mathbb Q_p)$ | new: $\int_{E_0(\mathbb Q_p)}\lvert\omega\rvert = N_p/p$ for every reduction type, $p$ odd (Milne IV.10.6 (a), second step) |
| `omega_measure_goodReduction` (new in 0.4.0) | as above | as above | new: $\int_{E(\mathbb Q_p)}\lvert\omega\rvert = c_p N_p/p$ at good reduction, $p$ odd |
| `realPeriod_eq_latticePeriod` (new in 0.4.0) | the Weierstrass $\wp$-function of a lattice (`PeriodPair`) | the real period as an integral, its behaviour under isogenies (`WeierstrassCurve.realPeriod`); no lattice | new: the real period is the least positive real period of the lattice times the number of real components |
| `mazur_torsion_realized` (new in 0.4.0) | — | Nagell–Lutz; torsion of a few worked examples (`MordellWeil/WorkedExamples/`) | new: each of Mazur's fifteen groups is $E(\mathbb Q)_{\mathrm{tors}}$ for an explicit curve (Milne II.5.11, the realization half) |
| `bsd_milne_iff_strongBSD_rat` (conditional, new in 0.4.0) | as for `bsd_milne_iff_strongBSD` | a statement of the conjecture (`WeierstrassCurve.BirchSwinnertonDyer`); Mordell–Weil over number fields | new: the equivalence with `StrongBSD` over $\mathbb Q$ with Mordell–Weil proved, given one named local statement (`LocalPointsInjective`) |
| `omega_measure_of_zeroComponentIndex` (conditional, new in 0.4.0) | as for `omega_measure_zeroComponent` | as above | new: $\int_{E(\mathbb Q_p)}\lvert\omega\rvert = c_p N_p/p$ at every reduction type, $p$ odd, given Milne's translation step (`ZeroComponentIndex`) |
| `bsd_milne_iff_strongBSD_unconditional` (new in 0.4.1) | as for `bsd_milne_iff_strongBSD` | its own statement of the conjecture (`WeierstrassCurve.BirchSwinnertonDyer`), not compared with Milne's or Formal Conjectures' | new: for every elliptic curve over $\mathbb Q$ with a minimal equation, Milne's Conjecture IV.10.5 (standard normalization) is equivalent to `StrongBSD`, with no named input |
| `bsd_milne_printed_iff_strongBSD_rank_zero` (new in 0.4.1) | as above | as above | new: in rank 0, Conjecture IV.10.5 as printed is equivalent to `StrongBSD` |
| `strongBSD_refutes_milne_printed_positive_rank` (new in 0.4.1) | as above | as above | new: in positive rank, `StrongBSD` refutes Conjecture IV.10.5 as printed |
| `sha_milne_equiv_formalConjectures` (new in 0.4.1) | the Tate–Shafarevich group of a Galois module (`ContCohomology/Sha.lean`, master) | its own $Ш$ over number fields; no comparison with other formalizations | new: Milne's $Ш(E/\mathbb Q)$ and Formal Conjectures' are isomorphic for every elliptic curve over $\mathbb Q$ |
| `localPoints_injective_rat` (new in 0.4.1) | continuous group cohomology | restriction maps of $H^1$ along field extensions; no local injectivity | new: $H^1(\operatorname{Gal}(\bar{\mathbb Q}_v/\mathbb Q_v), E(\bar{\mathbb Q})) \to H^1(\operatorname{Gal}(\bar{\mathbb Q}_v/\mathbb Q_v), E(\bar{\mathbb Q}_v))$ is injective at every place of $\mathbb Q$ (Milne, *Arithmetic Duality Theorems*, I.3.10) |
| `kummer_approx_padic` (new in 0.4.1) | Hensel's lemma; division polynomials | the Kummer map; no approximation by algebraic points | new: $E(\mathbb Q_p) = \ell E(\mathbb Q_p) + \{\text{algebraic points}\}$ for every elliptic curve over $\mathbb Q$, every $p$ (including 2) and every prime $\ell$ |

## Results of the books that are proved here but are not headlines, because Tau Ceti has them

| result | here | Tau Ceti |
|---|---|---|
| Chebotarev's density theorem with natural density (Milne, Theorem 8.31) | `MilneANT.theorem8_31` | `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet` (`NumberTheory/Chebotarev/PrimeCounting/FrobeniusPrimeCount.lean`) |
| Dirichlet's theorem with natural density $1/\varphi(n)$ (Milne, Example 8.34) | `MilneANT.example_8_34'` | `NumberField.Chebotarev.hasNaturalDensity_primesCongruent` |
| Hermite–Minkowski with ramification in a finite set $S$ (Milne, Theorem 8.42) | `MilneANT.theorem8_42` | `TauCeti.NumberField.finite_of_finrank_le_of_ramifiedSupport_subset` |
| The $S$-unit theorem (Weil, IV.§4, Theorem 9) | `WeilBNT.weil_IV_4_thm9` | `TauCeti.NumberField.SUnit.exist_unique_eq_mul_prod` |
| The Riemann–Roch theorem for function fields (Weil, VI.§2, Theorem 2) | `WeilBNT.FF.weil_VI_2_thm2` | `isRiemannRochDivisor_*` (`FieldTheory/FunctionField/`) |
| The global reciprocity law (Milne V.5.3, idelic form) | `MilneCFT.idelicReciprocity` (from the Tau Ceti port) | `globalArtinMap` and its properties (`NumberTheory/ClassFieldTheory/Global/Reciprocity.lean`) |
| The existence theorem (Milne V.3.6) | `MilneCFT.existenceTheoremArtin` (from the Tau Ceti port) | `globalExistence`, `globalAbelianExistence` (`GlobalExistence/Existence.lean`) |
| Local reciprocity and local existence (Milne I.1.1) | `MilneCFT.LocalCFT.localReciprocityExistence` (from the Tau Ceti and Yamaguchi ports) | `localExistence`, the local Artin map (`LocalExistence/`, `Local/`) |
| The Kronecker–Weber theorem | `MilneCFT.LocalCFT.kroneckerWeber` (from the Tau Ceti port) | `kroneckerWeber` (`ClassFields/KroneckerWeber.lean`) |
| The Hasse norm theorem for cyclic extensions (Milne VIII.3.1) | `MilneCFT.Ch8.hasseNormTheorem` | `isGlobalNorm_iff_isLocalNormEverywhere`, `cyclicHasseNorm` |
| The fundamental exact sequence of Brauer groups (Milne VIII.4.2) | `MilneCFT.Ch8.theorem_4_2'` (for Mathlib's Brauer group of central simple algebras) | `brLocalization_injective`, `range_brLocalization`, `sumLocalInv_surjective` (for the cohomological Brauer group) |
| Cubic reciprocity (Milne VIII, Example 5.13) | `MilneCFT.Ch8.example5_13` | `IsPrimaryEisenstein.cubic_reciprocity` |
| The Chebotarev density theorem with Dirichlet density (Milne V.2.5) | `Chebotarev.chebotarev_unconditional` | `hasDirichletDensity_frobeniusPrimeSet` |
| The Lutz–Nagell theorem (Milne, *Elliptic Curves*, II.5) | `MilneEC.II.theorem_5_1` | `WeierstrassCurve.lutz_nagell` |
| Uniformization of complex elliptic curves (Milne, *Elliptic Curves*, III) | `MilneEC.III.thm_3_10` | `exists_periodPair_nonempty_addEquiv` |
| Rationality of the zeta function of an elliptic curve over a finite field (Milne, *Elliptic Curves*, IV.9.10), here by Milne's count of positive divisors | `MilneEC.theorem_9_10_unconditional` | `WeierstrassCurve.zetaFunction_eq_mul_inv` |
| Mordell's theorem for elliptic curves over $\mathbb Q$ with rational 2-torsion, by explicit descent | `MilneEC.fg_cubicCurve` | over every number field: `WeierstrassCurve.Affine.fg_point_of_numberField` |
| Mordell–Weil over $\mathbb Q$ by Milne's descent (new in 0.4.0) | `MilneEC.mordell_weil_rat` | over every number field: `WeierstrassCurve.Affine.fg_point_of_numberField` |
| Finiteness of the Selmer groups and of $Ш[n]$ over $\mathbb Q$ (Milne IV.3.1 for $K = \mathbb Q$; new in 0.4.0) | `MilneEC.thm_3_1_selmer_rat`, `MilneEC.finite_sha_torsion` | over every number field: `WeierstrassCurve.finite_selmerGroup`, `WeierstrassCurve.finite_torsionBy_sha` |
| The explicit unramified local Artin map $a \mapsto \mathrm{Frob}^{\operatorname{ord}(a)}$ (Milne CFT I.1.1, III.3.7; new in 0.4.0) | `MilneCFT.LocalUnramified.tauCetiArtin_eq_unramifiedArtin` | `TauCeti.ClassFieldTheory.localArtinMap_eq_frobenius_pow_valuation` |

## By book and chapter

The book maps ([books/](books/README.md)) give every item; *in Mathlib* there means that Mathlib v4.35.0 has the
result. Below, for each chapter: how many items Mathlib already has, how many this library proves, and what Tau Ceti
has in the same area where it was checked ("not checked": no search was made for that chapter).

### Milne, *Algebraic Number Theory*

| chapter | in Mathlib | proved here | Tau Ceti (checked) |
|---|---|---|---|
| 1. Preliminaries from commutative algebra | 13 | 4 | not checked |
| 2. Rings of integers | 28 | 14 | not checked |
| 3. Dedekind domains; factorization | 26 | 19 | not checked |
| 4. The finiteness of the class number | 17 | 7 | not checked |
| 5. The unit theorem | 8 | 6 | the $S$-unit theorem |
| 6. Cyclotomic extensions; Fermat's Last Theorem | 4 | 7 | no theorem on regular primes |
| 7. Absolute values; local fields | 16 | 38 | absolute values over a given finite place |
| 8. Global fields | 3 | 33 | Chebotarev and Dirichlet with natural density; Hermite–Minkowski with $S$; Dedekind's factorization theorem over $\mathbb Q$ |
| definitions given in prose | 64 | 4 (and 16 definitions) | not checked |

Most of Chapters 1–5 is in Mathlib; this library adds the remaining items, Chapters 6–8 (Kummer's theorem, Ostrowski's
theorem for number fields, the local theory, Chebotarev and its consequences) and Dedekind's theorem over every number
field.

### Milne, *Class Field Theory*

Mathlib has Galois cohomology in low degrees, central simple algebras, local fields and the adeles, but no class field
theory. Tau Ceti (checked at `686d0d7f`) has Tate cohomology, class formations, local and global class field theory
(reciprocity, existence, the Kronecker–Weber theorem, ray class fields), the Hasse norm theorem, the Brauer group of a
number field and Chebotarev's theorem; the corresponding items of Milne are proved here partly from ports of those Tau
Ceti files and of N. Yamaguchi's class field theory library (`NumberFieldKB/TauCetiPort/`,
`NumberFieldKB/YamaguchiPort/`). New here: Lubin–Tate theory in Milne's form (the Lubin–Tate extensions, the
independence of the prime element, $K^{\mathrm{ab}} = K_\pi K^{\mathrm{un}}$), the Grunwald–Wang theorem, the cyclicity
of central division algebras over number fields, the Eisenstein reciprocity law and Furtwängler's theorem, Gauss's
point count, Weber $L$-series of ray class characters (continuation and $L(1,\chi) \ne 0$), and the item-by-item
statements of the book. Three statements of Chapter V are errata of the book; the map
([books/milne-cft.md](books/milne-cft.md)) shows the corrected forms, proved, and the counterexamples to the printed
forms.

### Weil, *Basic Number Theory* (Chapters I–VII)

| chapter | in Mathlib | proved here | Tau Ceti (checked) |
|---|---|---|---|
| I. Locally compact fields | 10 | 46 | (audit of 2026-11-04) Teichmüller representatives, commutative case; one item of I.§4 (the invariant map of the Brauer group) is only in Tau Ceti |
| II. Lattices and duality over local fields | 13 | 36 | (audit of 2026-11-04) lattices over local fields, commutative case |
| III. Places of A-fields | 21 | 20 | not checked |
| IV. Adeles | 7 | 45 | adeles: discreteness and compact quotient; the $S$-unit theorem |
| V. Algebraic number-fields | 19 | 24 | not checked |
| VI. The theorem of Riemann–Roch | 0 | 18 | the Riemann–Roch theorem for divisors of a function field (Weil's coherent systems and adelic form are not there) |
| VII. Zeta-functions of A-fields | 4 | 83 | the zeta function of an elliptic curve over a finite field |

Of the proved items, 16 are proved in the quadratic-forms library that this release depends on (local Fourier
analysis, self-dual measures and adelic Poisson summation).

### Tate's thesis

Neither Mathlib nor Tau Ceti has Tate's local and global zeta integrals, their functional equations, or the
continuation of Hecke L-functions of a general number field. Mathlib has Dirichlet L-functions over $\mathbb Q$ and
the residue of the Dedekind zeta function; Tau Ceti has Hecke characters, ray class characters, the Dedekind zeta
function on a half-plane past $\operatorname{Re} s = 1$, and definitions of the continued Hecke L-functions.

### Pontryagin duality

Mathlib has the Pontryagin dual of a topological group, the duality for finite abelian groups, and the instances
"compact implies discrete dual" and "discrete implies compact dual". Tau Ceti has Bochner's theorem and the Peter–Weyl
theorem (both ported here and used in the proof), but not the duality theorem, Fourier inversion on a general locally
compact abelian group, or the dual measure. Everything in [the Pontryagin map](books/pontryagin.md) beyond these is new.

### Milne, *Elliptic Curves*

Mathlib (v4.35.0 and master) has Weierstrass curves with the group law, changes of variables, minimal models and
reduction, division polynomials, the $L$-series as a Dirichlet series, the Weierstrass $\wp$-function, Eisenstein series
and the level-one dimension formula; no isogenies, torsion structure, Mordell–Weil, heights, Hasse bound or Tate module.
Tau Ceti (checked at `4caf68dc`) has the results listed above; the map ([books/milne-ec.md](books/milne-ec.md)) names
the Tau Ceti declaration for each item proved there and not here. New here: the plane-curve foundations of Chapter I
(intersection numbers, Bézout, the nine-point lemma, associativity on every cubic), Milne's explicit 2-descent and its
examples, Lemma IV.2.1 in every characteristic (Tau Ceti: $n$ prime to the characteristic), Lang's theorem, the zeta
function through point counts and divisor counts, and Milne's conjectures of Chapter IV as statements compared with
Formal Conjectures. New in 0.4.0: Milne's descent over $\mathbb Q$ by unramified extensions (Lemma IV.3.5,
Proposition IV.3.6) and Mordell–Weil over $\mathbb Q$ by it, the explicit Selmer and Tate–Shafarevich groups of IV §8,
the local Tamagawa measure of Remark IV.10.6, the real period through the lattice, the realization of Mazur's torsion
groups, and the comparison of Milne's period, Tamagawa numbers and Tate–Shafarevich group with Formal Conjectures'.
New in 0.4.1: Kummer approximation over $\mathbb Q_p$ (every $p$) and $\mathbb R$, local injectivity of $H^1$ at every
place of $\mathbb Q$, and with them the comparison of the Tate–Shafarevich groups and of Conjecture IV.10.5 with
`StrongBSD` without named inputs.
Not formalized anywhere checked: Nagell's reduction of a plane cubic to Weierstrass form and the Eichler–Shimura
theory of Chapter V.

### The modular curves $X_0(N)$ (Milne, *Elliptic Curves*, Chapter V)

Mathlib has modular forms, cusp forms and congruence subgroups; Tau Ceti has, in addition, the $j$-function, the
index and the elliptic points and cusps of $\Gamma_0(N)$, Riemann surface charts on quotients of the upper half plane,
the topological Riemann–Hurwitz formula and the genus of $X(1)$. The function field of $X_0(N)$ over $\mathbb Q$, the
modular polynomial over $\mathbb Q$, the genus formula for $X_0(N)$ and $\dim S_2(\Gamma_0(N)) = g$ are new here.
