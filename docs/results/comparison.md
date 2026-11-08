# Comparison with Mathlib and Tau Ceti

What each headline and each part of the books in this release adds to [Mathlib](https://github.com/leanprover-community/mathlib4)
and to [Tau Ceti](https://github.com/TauCetiProject/TauCeti). The comparison was made on 2026-11-07 by reading the
statements (not only the names) in Mathlib master at commit `df6966d0d` and Tau Ceti main at commit `d7b47803c`.
This library is built on Mathlib v4.35.0; Tau Ceti uses a later Lean and Mathlib and cannot be imported here, so the
Tau Ceti files this library needs are ported (`NumberFieldKB/TauCetiPort/`, see `NOTICE`).

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

## Results of the books that are proved here but are not headlines, because Tau Ceti has them

| result | here | Tau Ceti |
|---|---|---|
| Chebotarev's density theorem with natural density (Milne, Theorem 8.31) | `MilneANT.theorem8_31` | `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet` (`NumberTheory/Chebotarev/PrimeCounting/FrobeniusPrimeCount.lean`) |
| Dirichlet's theorem with natural density $1/\varphi(n)$ (Milne, Example 8.34) | `MilneANT.example_8_34'` | `NumberField.Chebotarev.hasNaturalDensity_primesCongruent` |
| Hermite–Minkowski with ramification in a finite set $S$ (Milne, Theorem 8.42) | `MilneANT.theorem8_42` | `TauCeti.NumberField.finite_of_finrank_le_of_ramifiedSupport_subset` |
| The $S$-unit theorem (Weil, IV.§4, Theorem 9) | `WeilBNT.weil_IV_4_thm9` | `TauCeti.NumberField.SUnit.exist_unique_eq_mul_prod` |
| The Riemann–Roch theorem for function fields (Weil, VI.§2, Theorem 2) | `WeilBNT.FF.weil_VI_2_thm2` | `isRiemannRochDivisor_*` (`FieldTheory/FunctionField/`) |

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

### The modular curves $X_0(N)$ (Milne, *Elliptic Curves*, Chapter V)

Mathlib has modular forms, cusp forms and congruence subgroups; Tau Ceti has, in addition, the $j$-function, the
index and the elliptic points and cusps of $\Gamma_0(N)$, Riemann surface charts on quotients of the upper half plane,
the topological Riemann–Hurwitz formula and the genus of $X(1)$. The function field of $X_0(N)$ over $\mathbb Q$, the
modular polynomial over $\mathbb Q$, the genus formula for $X_0(N)$ and $\dim S_2(\Gamma_0(N)) = g$ are new here.
