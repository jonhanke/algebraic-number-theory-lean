# Algebraic number theory in Lean 4

[![Lean build](https://github.com/jonhanke/algebraic-number-theory-lean/actions/workflows/build.yml/badge.svg)](https://github.com/jonhanke/algebraic-number-theory-lean/actions/workflows/build.yml) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24047657.svg)](https://doi.org/10.5281/zenodo.24047657)

A Lean 4 library (built on Mathlib v4.35.0) that formalizes seven texts of algebraic number theory item by item:
Milne's *Algebraic Number Theory*, *Class Field Theory* and *Elliptic Curves*, Weil's *Basic Number Theory* (number
fields and function fields over finite fields), Tate's thesis, Pontryagin duality for locally compact abelian groups,
and the modular curves $`X_0(N)`$ of Chapter V of Milne's *Elliptic Curves* (a map of its own). The Lean library is
called `NumberFieldKB`. It depends on
[quadratic-forms-lean](https://github.com/jonhanke/quadratic-forms-lean) (release v0.3.0, a Lake dependency) for local
Fourier analysis, self-dual measures, adelic Poisson summation and local zeta integrals.

- **Book maps**: for each book, a table from every item (theorem, proposition, lemma, definition, result stated in
  the text) to the Lean declaration that formalizes it and its status: [docs/results/books/](docs/results/books/README.md).
- **Literature statements**: each result from a book or paper is a Lean declaration tagged
  `@[kb "<source key>" "<locator>"]`, with the keys of [`references.bib`](references.bib).
- **What is proved**: every theorem is checked by the Lean kernel; the only `sorry`s in the repository are the
  deliberate ones in [`Challenge.lean`](Challenge.lean), which states the headline results without proofs. The CI
  workflow builds the library, checks that the headline theorems depend only on the standard axioms `propext`,
  `Classical.choice` and `Quot.sound` ([scripts/check_axioms.lean](scripts/check_axioms.lean)), and runs
  `lake comparator` once per book (`Challenge_<book>.lean` against `Solution_<book>.lean`) to check the proved
  statements.
- **Comparison**: [docs/results/comparison.md](docs/results/comparison.md) says, for each headline and each chapter,
  what Mathlib and [Tau Ceti](https://github.com/TauCetiProject/TauCeti) already have and what this library adds.

## What's new in 0.4.1

The comparison of Milne's form of the conjecture of Birch and Swinnerton-Dyer with Formal Conjectures' `StrongBSD`
is now unconditional:

- **Kummer approximation at every prime, $`p = 2`$ included:** for every elliptic curve $`E`$ over $`\mathbb{Q}`$,
  every prime $`p`$ and every prime $`\ell`$, $`E(\mathbb{Q}_p) = \ell E(\mathbb{Q}_p) + \{\text{points algebraic over } \mathbb{Q}\}`$
  (`kummer_approx_padic`). Multiplication by $`m \ne 0`$ is onto the points with $`\lVert x\rVert > \lVert m\rVert^{-4}`$,
  by Hensel's lemma on the division polynomials as in Milne's Corollary II.4.2 (no formal group), and the algebraic
  points are dense. At the real place, points with large $`x`$ are doubles and the algebraic points are dense.
- **Local injectivity at every place of $`\mathbb{Q}`$:** the map
  $`H^1(\operatorname{Gal}(\bar{\mathbb{Q}}_v/\mathbb{Q}_v), E(\bar{\mathbb{Q}})) \to H^1(\operatorname{Gal}(\bar{\mathbb{Q}}_v/\mathbb{Q}_v), E(\bar{\mathbb{Q}}_v))`$
  is injective on continuous classes (`localPoints_injective_rat`; the named input `LocalPointsInjective` of 0.4.0, now
  proved, from Kummer approximation rather than Greenberg approximation).
- **The two Tate–Shafarevich groups agree:** Milne's $`Ш(E/\mathbb{Q})`$ and Formal Conjectures' are isomorphic for
  every elliptic curve over $`\mathbb{Q}`$ (`sha_milne_equiv_formalConjectures`; the named input `ShaComparison` of
  0.3.0, now proved).
- **Birch and Swinnerton-Dyer, compared with no named input:** for every elliptic curve over $`\mathbb{Q}`$ given by a
  minimal equation, Milne's Conjecture IV.10.5 with the standard normalization of the height pairing is equivalent to
  `StrongBSD` (`bsd_milne_iff_strongBSD_unconditional`); in rank 0 the printed form is equivalent to `StrongBSD`
  (`bsd_milne_printed_iff_strongBSD_rank_zero`); in positive rank `StrongBSD` refutes the printed form
  (`strongBSD_refutes_milne_printed_positive_rank`). No conjecture is assumed.
- **Headlines:** six new unconditional (47 in all: 44 unconditional, 3 conditional). The 41 headlines of 0.4.0 are
  unchanged, statement for statement; the conditional `bsd_milne_iff_strongBSD_rat` of 0.4.0 is kept as it was (it is
  still true, and its input is now proved).

## What's new in 0.4.0

The arithmetic of elliptic curves over $`\mathbb{Q}`$ (Milne's *Elliptic Curves*, Chapter IV), toward the conjecture
of Birch and Swinnerton-Dyer:

- **The 2-Selmer group and $`Ш[2]`$ of $`y^2 = x^3 + px`$ (Propositions IV.8.1 and IV.8.2):** for a prime
  $`p \equiv 1 \pmod 8`$ the 2-Selmer group is $`(\mathbb{Z}/2)^3`$, and when 2 is not a fourth power modulo $`p`$
  the rank is 0 and $`Ш(E/\mathbb{Q})[2] \cong (\mathbb{Z}/2)^2`$, proved on the Galois-cohomological Selmer group by
  Kummer theory and the local conditions at $`2`$, $`p`$ and $`\infty`$.
- **The local Tamagawa measure (Remark IV.10.6):** for an odd prime $`p`$ and a minimal equation, the measure of
  $`E_0(\mathbb{Q}_p)`$ for $`|\omega|`$ is $`N_p/p`$ at every reduction type, and at good reduction
  $`\int_{E(\mathbb{Q}_p)}|\omega| = c_p N_p/p = L_p(E, 1)^{-1}`$; at every reduction type the formula
  $`\int_{E(\mathbb{Q}_p)}|\omega| = c_p N_p/p`$ is proved from one named input (Milne's translation step). The point
  counts $`N_p = p - 1, p + 1, p`$ at split, non-split and additive reduction are proved for every prime.
- **The real period:** Formal Conjectures' real period of an elliptic curve over $`\mathbb{R}`$ is the least positive
  real period of its lattice times the number of connected components of $`E(\mathbb{R})`$, through the
  uniformization of Chapter III.
- **Mazur's fifteen groups occur:** each group of Mazur's list is the torsion of $`E(\mathbb{Q})`$ for an explicit
  curve (the realization half of Remark II.5.11; Mazur's theorem itself is not formalized).
- **Mordell–Weil over $`\mathbb{Q}`$ by Milne's descent:** Lemmas IV.3.2 and IV.3.5 and Proposition IV.3.6 at every
  prime (divisibility read on the reduction, over unramified extensions of $`\mathbb{Q}_p`$), the finiteness of the
  Selmer groups over $`\mathbb{Q}`$ (Theorem IV.3.1 for $`K = \mathbb{Q}`$), the finite generation of $`E(\mathbb{Q})`$
  for every elliptic curve over $`\mathbb{Q}`$ (`NumberFieldKB.MilneEC.mordell_weil_rat`), the finiteness of
  $`Ш(E/\mathbb{Q})[n]`$, the rank bound by the $`p`$-Selmer group, and Propositions IV.5.5, IV.5.6 and Remark IV.5.2
  over $`\mathbb{Q}`$ without hypotheses. Tau Ceti has Mordell–Weil over every number field, so these are not
  headlines.
- **Birch and Swinnerton-Dyer, compared:** Milne's period and his product of Tamagawa numbers are proved equal to
  Formal Conjectures' (the named comparisons `PeriodComparison` and `TamagawaComparison` of 0.3.0 are now theorems),
  the degree-one continuous cohomology of a discrete module is identified with continuous crossed homomorphisms, and
  the comparison of the two Tate–Shafarevich groups is reduced to one local statement (`LocalPointsInjective`). With
  Mordell–Weil proved, Milne's Conjecture IV.10.5 is equivalent to Formal Conjectures' `StrongBSD` given only that
  statement (a new conditional theorem).
- **Also new:** Exercise IV.5.9, Remark IV.8.4 (the quartic $`Y^2 = 2 - 2pX^4`$ is everywhere locally soluble), the
  convergence of $`\zeta(V, s)`$ for $`\operatorname{Re} s > n + 1`$ ($`V \subset \mathbb{P}^n`$) and of $`L(E, s)`$ for
  $`\operatorname{Re} s > 2`$, Tate's algorithm and Ogg's formula
  as named inputs citing Tau Ceti, and, in class field theory, the explicit unramified local Artin map
  $`a \mapsto \mathrm{Frob}^{\operatorname{ord}(a)}`$ compared with the library's local Artin map (Tau Ceti has the
  same formula for its map, so it is not a headline).
- **Headlines:** five new unconditional and two new conditional (41 in all); the 34 headlines of 0.3.0 are unchanged,
  statement for statement. The comparator runs once per book, as before.

## The books

| book | rows | proved | definitions | in Mathlib | conditional | other |
|---|---|---|---|---|---|---|
| J. S. Milne, *Algebraic Number Theory* | 328 | 132 | 17 | 179 | 0 | 0 |
| J. S. Milne, *Class Field Theory* | 513 | 348 | 59 | 105 | 0 | 1 |
| J. S. Milne, *Elliptic Curves* | 318 | 230 | 44 | 10 | 5 | 29 |
| A. Weil, *Basic Number Theory* (number fields and function fields) | 371 | 272 | 24 | 74 | 0 | 1 |
| J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions* (Cassels–Fröhlich, Chapter XV) | 80 | 57 | 23 | 0 | 0 | 0 |
| [Pontryagin duality (Folland, *A Course in Abstract Harmonic Analysis*, Chapter 4; Weil II.§5, VII.§2)](docs/results/books/pontryagin.md) | 24 | 22 | 2 | 0 | 0 | 0 |
| The modular curves $X_0(N)$ (Milne, *Elliptic Curves*, Chapter V) | 43 | 29 | 4 | 1 | 1 | 8 |

*Proved* counts the items proved in Lean with only the standard axioms and no unproved input; *in Mathlib* the items
that Mathlib already has (the map names the Mathlib declaration); rows that are definitions, items in Tau Ceti only,
items not formalized, and items outside this release are counted in the maps. Rows that are not results (examples,
history, comments) are omitted.

## Highlights

Every result listed here is a headline theorem of [`Challenge.lean`](Challenge.lean): it is checked by the Lean kernel
with only the standard axioms and depends on no unproved input. Headlines are only results that are in neither Mathlib
nor Tau Ceti, or that are stronger here ([comparison](docs/results/comparison.md)). The statements have **not yet been
reviewed by a human** (see Provenance).

**Milne, *Algebraic Number Theory***

- **Kummer's theorem:** if $`p`$ is an odd prime not dividing the class number of $`\mathbb{Q}(\zeta_p)`$, then $`x^p + y^p = z^p`$ has no integer solution with $`p \nmid xyz`$ (`kummer_regular`).
- **Dedekind's theorem over every number field:** if a monic $`f`$ over the ring of integers $`\mathcal{O}_K`$ is squarefree modulo a prime $`\mathfrak{p}`$, the degrees of its irreducible factors modulo $`\mathfrak{p}`$ are the cycle type of an element of the Galois group of $`f`$ over $`K`$ (`dedekind_factorizationType`; Tau Ceti has it over $`\mathbb{Q}`$).
- **Ostrowski's theorem for number fields:** every nontrivial absolute value on a number field is equivalent to exactly one absolute value given by a prime ideal, a real embedding or a pair of complex conjugate embeddings (`ostrowski_numberField`).

**Milne, *Class Field Theory***

- **The Grunwald–Wang theorem:** for finitely many places $`v`$ of a number field $`K`$ and characters $`\chi_v`$ of finite order of $`K_v^\times`$, there is a character of the idele class group with these local components, of order $`\operatorname{lcm}(\operatorname{ord}\chi_v)`$ outside Wang's special case (`grunwaldWang`).
- **Central division algebras over a number field:** the order of $`[D]`$ in $`\operatorname{Br}(K)`$ is $`\sqrt{[D:K]}`$, and $`D`$ is a cyclic algebra (`centralDivisionAlgebra_cyclic`).
- **Local Kronecker–Weber in Lubin–Tate form:** for a nonarchimedean local field $`K`$ and a prime element $`\pi`$, every finite abelian extension of $`K`$ lies in $`K_\pi K^{\mathrm{un}}`$ (`localKroneckerWeber_lubinTate`).
- **Eisenstein reciprocity:** $`(\alpha/a)_p = (a/\alpha)_p`$ for an odd prime $`p`$, $`a \in \mathbb{Z}`$ prime to $`p`$ and $`\alpha`$ a primary non-unit of $`\mathbb{Z}[\zeta_p]`$ prime to $`a`$ (`eisensteinReciprocity`).
- **Furtwängler's theorem:** if $`x^p + y^p = z^p`$ with $`x, y, z`$ coprime and $`p \nmid xyz`$, then $`q^{p-1} \equiv 1 \pmod{p^2}`$ for every prime $`q \mid xyz`$ (`furtwangler_fermat`).
- **Gauss's point count:** $`x^3 + y^3 + z^3 = 0`$ has $`p + 1`$ points over $`\mathbb{F}_p`$ if $`p \not\equiv 1 \pmod 3`$, and $`p + 1 + A`$ if $`p \equiv 1 \pmod 3`$, where $`4p = A^2 + 27B^2`$ and $`A \equiv 1 \pmod 3`$ (`gauss_cubicCurve_count`).
- **Weber $`L`$-series:** for a nontrivial character $`\chi`$ of a ray class group, $`L(s, \chi)`$ extends to a holomorphic function on $`\operatorname{Re} s > 0`$ with $`L(1, \chi) \neq 0`$ (`weberL_continuation`; Milne's Theorem V.2.4(b), whose "converges" is an erratum for "extends").

**Milne, *Elliptic Curves***

- **Bézout's theorem:** two projective plane curves $`F`$, $`G`$ over a field $`k`$ with no common component meet in finitely many points of $`\mathbb{P}^2(k^{\mathrm{al}})`$, and the intersection numbers add up to $`\deg F \cdot \deg G`$ (`bezout`).
- **The group law on every plane cubic:** for a nonsingular projective plane cubic over a perfect field, not necessarily in Weierstrass form, and any rational point $`O`$, the chord–tangent addition is associative (`chordTangent_assoc`; Mathlib has the group law for Weierstrass curves).
- **Explicit 2-descent:** for distinct integers $`\alpha, \beta, \gamma`$, the rational points of $`y^2 = (x - \alpha)(x - \beta)(x - \gamma)`$ form a finitely generated group of rank at most $`2\,\#\{p \mid 2\Delta\}`$, by Milne's descent with the map $`x - T`$ and the canonical height, with no Selmer group (`rank_bound_twoDescent`; Tau Ceti has finite generation over every number field, not the rank bound).
- **The curve $`y^2 = x^3 - x`$:** its group of rational points is $`(\mathbb{Z}/2)^2`$ (`points_x3_sub_x`), so **1 is not a congruent number**: no right triangle with rational sides has area 1 (`one_not_congruent`).
- **Lang's theorem:** for an elliptic curve $`E`$ over a finite field $`k`$, $`H^1(k, E) = 0`$ (`lang_H1_eq_zero`).
- **$`y^2 = x^3 + px`$** (new in 0.4.0): for a prime $`p \equiv 1 \pmod 8`$ the 2-Selmer group is $`(\mathbb{Z}/2)^3`$; if 2 is not a fourth power modulo $`p`$, the rank is 0 and $`Ш(E/\mathbb{Q})[2] \cong (\mathbb{Z}/2)^2`$ (`selmer_sha_x3_add_px`).
- **The local Tamagawa measure** (new in 0.4.0): for an odd prime $`p`$ and a minimal equation over $`\mathbb{Q}_p`$, $`\int_{E_0(\mathbb{Q}_p)}|\omega| = N_p/p`$ at every reduction type (`omega_measure_zeroComponent`), and $`\int_{E(\mathbb{Q}_p)}|\omega| = c_p N_p/p`$ at good reduction (`omega_measure_goodReduction`).
- **The real period** (new in 0.4.0): for an elliptic curve over $`\mathbb{R}`$, $`\int_{E(\mathbb{R})}|\omega|`$ is the least positive real period of the lattice of its uniformization times the number of connected components of $`E(\mathbb{R})`$ (`realPeriod_eq_latticePeriod`; Tau Ceti has the real period as an integral, not its lattice).
- **Mazur's groups occur** (new in 0.4.0): each of the fifteen groups $`\mathbb{Z}/m`$ ($`m \le 10`$ or $`m = 12`$) and $`\mathbb{Z}/2 \times \mathbb{Z}/2m`$ ($`m \le 4`$) is $`E(\mathbb{Q})_{\mathrm{tors}}`$ for some elliptic curve over $`\mathbb{Q}`$ (`mazur_torsion_realized`).
- **Milne's Birch and Swinnerton-Dyer conjecture is `StrongBSD`** (new in 0.4.1): for every elliptic curve $`E`$ over $`\mathbb{Q}`$ given by a minimal equation, Milne's Conjecture IV.10.5 with the standard normalization of the height pairing (`Conjecture10_5Corrected`) holds if and only if the statement `StrongBSD` of [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) holds, with no named input and with $`E(\mathbb{Q})`$ finitely generated by the library's Mordell–Weil theorem (`bsd_milne_iff_strongBSD_unconditional`). In rank 0 the printed form is equivalent to `StrongBSD` (`bsd_milne_printed_iff_strongBSD_rank_zero`); in positive rank `StrongBSD` refutes it (`strongBSD_refutes_milne_printed_positive_rank`).
- **The Tate–Shafarevich groups agree** (new in 0.4.1): for every elliptic curve over $`\mathbb{Q}`$, Milne's $`Ш(E/\mathbb{Q})`$ (Galois cohomology, locally trivial in $`E(\bar{\mathbb{Q}}_v)`$) is isomorphic to Formal Conjectures' (locally trivial in $`E(\bar{\mathbb{Q}})`$) (`sha_milne_equiv_formalConjectures`).
- **Local injectivity** (new in 0.4.1): at every place $`v`$ of $`\mathbb{Q}`$, a continuous class of $`\operatorname{Gal}(\bar{\mathbb{Q}}_v/\mathbb{Q}_v)`$ with values in $`E(\bar{\mathbb{Q}})`$ that is trivial in $`E(\bar{\mathbb{Q}}_v)`$ is trivial (`localPoints_injective_rat`; Milne, *Arithmetic Duality Theorems*, Remark I.3.10).
- **Kummer approximation** (new in 0.4.1): for every elliptic curve $`E`$ over $`\mathbb{Q}`$, every prime $`p`$ (including 2) and every prime $`\ell`$, every point of $`E(\mathbb{Q}_p)`$ is $`\ell S + T`$ with $`S \in E(\mathbb{Q}_p)`$ and $`T`$ algebraic over $`\mathbb{Q}`$ (`kummer_approx_padic`).

**Weil, *Basic Number Theory*: number fields**

- **Self-duality of the adeles:** every continuous character of $`\mathbb{A}_K`$ is $`x \mapsto \chi(ax)`$ for a unique $`a \in \mathbb{A}_K`$, and the annihilator of $`K`$ is $`K`$ (`adeles_selfDual`).
- **Finiteness of idele classes:** $`\mathbb{A}_K^\times / K^\times \Omega(P)`$ is finite for every set $`P`$ of places containing the infinite ones; for $`P`$ the infinite places this is the finiteness of the class number (`idele_classes_finite`).

**Weil, *Basic Number Theory*: function fields over finite fields**

- **The zeta function:** $`Z(u)(1 - u)(1 - qu)`$ is a polynomial $`P`$ of degree $`2g`$ with $`P(0) = 1`$, $`P(1) = h`$ and $`P(u) = q^g u^{2g} P(1/qu)`$ (`zeta_functionField`).
- **Hecke $`L`$-functions:** for a ramified quasicharacter $`\omega`$ of conductor $`\mathfrak{f}`$, $`L(u, \omega)`$ is a polynomial of degree exactly $`2g - 2 + \deg \mathfrak{f}`$ (`heckeL_functionField_polynomial`).

**Tate's thesis, over every number field**

- **Tate's main theorem:** the global zeta integral $`Z(\Phi, \chi, s)`$ continues to a meromorphic function with $`Z(\Phi, \chi, 1 - s) = Z(\hat{\Phi}, \chi^{-1}, s)`$, for every Schwartz–Bruhat function $`\Phi`$ and Hecke character $`\chi`$ (`tate_globalZeta_functionalEquation`).
- **Poles and residues:** for $`\chi = \|\cdot\|^c`$ the residues at $`s = 1 - c`$ and $`s = -c`$ are $`\hat{\Phi}(0)\rho_F`$ and $`-\Phi(0)\rho_F`$ (`tate_globalZeta_residues`).
- **Hecke $`L`$-functions:** $`\Lambda(s, \chi) = W(\chi)\Lambda(1 - s, \chi^{-1})`$, holomorphic away from the poles, with $`|W(\chi)| = 1`$ for unitary $`\chi`$ (`heckeL_functionalEquation`; Mathlib has Dirichlet $`L`$-functions over $`\mathbb{Q}`$).
- **The Dedekind zeta function:** $`\zeta_F`$ continues to $`\mathbb{C} \setminus \{1\}`$ with residue $`2^{r_1}(2\pi)^{r_2} h_F R_F / (w_F \sqrt{|d_F|})`$ at $`s = 1`$ (`dedekindZeta_continuation`; Mathlib has the residue as a limit, Tau Ceti a continuation past $`\operatorname{Re} s = 1`$ and quadratic fields).
- **Its functional equation:** $`\Lambda_F(s) = |d_F|^{s/2}\Gamma_{\mathbb{R}}(s)^{r_1}\Gamma_{\mathbb{C}}(s)^{r_2}\zeta_F(s)`$ satisfies $`\Lambda_F(1 - s) = \Lambda_F(s)`$ (`completedDedekindZeta_functionalEquation`).

**Pontryagin duality**

- **Pontryagin duality:** for every locally compact commutative Hausdorff group $`G`$, the canonical map $`G \to G^{**}`$ is an isomorphism of topological groups (`pontryaginDuality`).
- **Fourier inversion:** every Haar measure on $`G`$ has a dual Haar measure on $`G^*`$ for which Fourier inversion holds (`fourierInversion_dualMeasure`).
- **Closed subgroups:** for a closed subgroup $`H`$ with annihilator $`H^*`$: $`H^{**} = H`$, $`H \cong (G^*/H^*)^*`$, $`H`$ is open if and only if $`H^*`$ is compact, compact if and only if $`H^*`$ is open, and $`G/H`$ is compact if and only if $`H^*`$ is discrete (`pontryagin_closedSubgroups`).
- **Compact and discrete groups:** $`G`$ is compact if and only if $`G^*`$ is discrete, and discrete if and only if $`G^*`$ is compact (`compact_iff_dual_discrete`).

**The modular curves $`X_0(N)`$ (Milne, *Elliptic Curves*, Chapter V)**

- **The genus formula:** $`12g = 12 + \mu - 3\nu_2 - 4\nu_3 - 6\nu_\infty`$ for the genus $`g`$ of $`X_0(N)`$ over $`\mathbb{Q}`$, with the classical closed forms of $`\mu`$, $`\nu_2`$, $`\nu_3`$, $`\nu_\infty`$ (`genus_X0`).
- **The modular polynomial:** the minimal polynomial of $`j(Nz)`$ over $`\mathbb{C}(j)`$ has rational coefficients and degree $`[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)]`$ (`modularPolynomial_rational`).
- **Modular functions:** every modular function for $`\Gamma_0(N)`$ is a rational function of $`j(z)`$ and $`j(Nz)`$ (`modularFunctions_Gamma0`).
- **Cusp forms of weight 2:** $`\dim S_2(\Gamma_0(N)) = g(X_0(N))`$ (`cuspForms_weightTwo_finrank`).

**Main statements.** To check what is claimed, read one file: [`Challenge.lean`](Challenge.lean) states the results
above and the conditional theorems below, with a docstring for each and a list of the library definitions the statements use; every proof there is a
deliberate `sorry`. [`Solution.lean`](Solution.lean) proves the same statements by appeal to the library theorems, and
`lake comparator`, run once per book (the per-book files `Challenge_<book>.lean` and `Solution_<book>.lean` and the
configurations in [`comparator/`](comparator/), listed in [`comparator.json`](comparator.json)), checks that each
proved statement is exactly the one in `Challenge.lean` and uses only the standard axioms. [`formalization.yaml`](formalization.yaml) records the
scope, sources, divergences from the literature, provenance and review status in the
[formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) format.

**Also proved here, not headlines because Tau Ceti has them:** Chebotarev's density theorem and Dirichlet's theorem
with natural density, Hermite–Minkowski with ramification in a finite set of primes, the $`S`$-unit theorem, the
Riemann–Roch theorem for function fields, and the main theorems of global and local class field theory (reciprocity,
existence, the Kronecker–Weber theorem), the Hasse norm theorem and the exact sequence of Brauer groups of a number
field; for elliptic curves, the Lutz–Nagell theorem, the uniformization of complex elliptic curves, the rationality of
the zeta function of an elliptic curve over a finite field (here by Milne's count of positive divisors),
Mordell–Weil for elliptic curves over $`\mathbb{Q}`$ by Milne's descent, with the finiteness of the Selmer groups and of
$`Ш(E/\mathbb{Q})[n]`$ (Tau Ceti: over every number field), and the explicit unramified local Artin map
$`a \mapsto \mathrm{Frob}^{\operatorname{ord}(a)}`$ (see the [comparison](docs/results/comparison.md)).

**Errata of Milne's *Class Field Theory*.** Three statements of Chapter V are false as printed: Theorem 2.4(b) (the
series need not converge on $`\operatorname{Re} s > 0`$; it extends there), Exercise 3.15 (the existence clause needs
the primes of $`S`$ in $`H`$) and Remark 4.8 (the first sentence needs $`G`$ complete; the second also needs the
character to be trivial on the identity component of $`K_\infty^\times`$). The corrected forms are proved, and the
printed forms of Exercise 3.15 and Remark 4.8 are refuted in Lean; the map of the book
marks these rows.

**A normalization in Milne's *Elliptic Curves*.** In Conjecture IV.10.5 (Birch and Swinnerton-Dyer) the height
pairing is $`\langle P, Q\rangle = \hat h(P + Q) - \hat h(P) - \hat h(Q)`$, twice the pairing of the standard
regulator, so the printed leading coefficient is $`2^r`$ times the standard one (Milne's footnote to §IV.6 warns that
normalizations differ by a factor 2). The identity is proved (`NumberFieldKB.MilneEC.regulatorQuotient_eq_two_pow_mul_regulator`),
and the statements below use both forms.

## Conditional theorems

A conditional theorem is proved in Lean with only the standard axioms, from hypotheses that are **named inputs**: Lean
structures that state a result of the literature which is not formalized here. A named input is never definitionally
equal to the conclusion, and nothing assumes a conjecture. These three are headlines of `Challenge.lean` (checked by
the comparator with the others of their book).

**Milne, *Elliptic Curves***

- **Milne's form of the conjecture of Birch and Swinnerton-Dyer is Formal Conjectures' `StrongBSD`:** for an elliptic
  curve $`E`$ over $`\mathbb{Q}`$ given by a minimal equation, Milne's Conjecture IV.10.5 with the standard
  normalization of the pairing (`Conjecture10_5Corrected`) holds if and only if the statement `StrongBSD` of
  [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) holds (`bsd_milne_iff_strongBSD`).
  Named inputs: `ShaComparison` (the two formalizations of the Tate–Shafarevich group over $`\mathbb{Q}`$ are
  isomorphic), `PeriodComparison` (Milne's $`\Omega = \int_{E(\mathbb{R})}|\omega|`$ is the global period of Formal
  Conjectures for a minimal equation) and `TamagawaComparison` (Milne's product of the Tamagawa numbers $`c_p`$ at the
  bad primes is Formal Conjectures' Tamagawa product). Finite generation of $`E(\mathbb{Q})`$ is an instance argument,
  as in Formal Conjectures. With the same inputs, in positive rank `StrongBSD` refutes the printed form of
  Conjecture IV.10.5 (`NumberFieldKB.MilneEC.not_conjecture10_5_of_strongBSD`). Kept as in 0.3.0; all three of its
  inputs are now proved (`NumberFieldKB.MilneEC.periodComparison`, `NumberFieldKB.MilneEC.tamagawaComparison` in 0.4.0,
  `NumberFieldKB.MilneEC.shaComparison` in 0.4.1), and the unconditional headline
  `bsd_milne_iff_strongBSD_unconditional` needs neither them nor the instance argument.
- **The same equivalence over $`\mathbb{Q}`$ with Mordell–Weil proved and one local input** (new in 0.4.0): for an
  elliptic curve $`E`$ over $`\mathbb{Q}`$ given by a minimal equation, `Conjecture10_5Corrected` holds if and only if
  `StrongBSD` holds, with the finite generation of $`E(\mathbb{Q})`$ supplied by the library's Mordell–Weil theorem
  (`bsd_milne_iff_strongBSD_rat`). Named input: `LocalPointsInjective` (at every place $`v`$ of $`\mathbb{Q}`$, a
  continuous class of $`\operatorname{Gal}(\bar{\mathbb{Q}}_v/\mathbb{Q}_v)`$ with values in $`E(\bar{\mathbb{Q}})`$ that
  is trivial in $`E(\bar{\mathbb{Q}}_v)`$ is trivial; Milne, *Arithmetic Duality Theorems*, Remark I.3.10, by Greenberg
  approximation), from which the comparison of the two Tate–Shafarevich groups is proved. Formal Conjectures' group
  embeds in Milne's unconditionally. Kept as in 0.4.0; its input is now proved (`localPoints_injective_rat`, new in
  0.4.1, from Kummer approximation), and the same equivalence without it is the headline
  `bsd_milne_iff_strongBSD_unconditional`.
- **The local Tamagawa measure at every reduction type** (new in 0.4.0): for an odd prime $`p`$ and a minimal
  equation of an elliptic curve over $`\mathbb{Q}_p`$, $`\int_{E(\mathbb{Q}_p)}|\omega| = c_p N_p/p`$, with $`c_p`$ Formal
  Conjectures' local Tamagawa number (`omega_measure_of_zeroComponentIndex`). Named input: `ZeroComponentIndex`
  (Milne's first step: $`\int_{E(\mathbb{Q}_p)}|\omega| = c_p\int_{E_0(\mathbb{Q}_p)}|\omega|`$, by translation invariance
  of $`|\omega|`$ and $`[E(\mathbb{Q}_p) : E_0(\mathbb{Q}_p)] = c_p`$); the second step is the headline
  `omega_measure_zeroComponent`.

## Statements of conjectures

Conjectures are stated as Lean definitions of type `Prop`. They are **never assumed**: no theorem of the library has
one among its hypotheses except the comparisons listed here, which prove relations between statements.

**Milne, *Elliptic Curves*, Chapter IV** (namespace `NumberFieldKB.MilneEC`)

- Conjecture IV.5.3: the Tate–Shafarevich group of an elliptic curve over a number field is finite (`Conjecture5_3`).
- Conjecture IV.10.1: $`\prod_{p \le P,\ p \text{ good}} N_p/p \sim C(\log P)^r`$, $`r`$ the rank of
  $`E(\mathbb{Q})`$ (`Conjecture10_1`).
- Conjecture IV.10.2 (Hasse–Weil): the zeta function of a nonsingular projective variety over $`\mathbb{Q}`$ continues
  meromorphically to $`\mathbb{C}`$; stated for complete intersections, without the functional equation, which the
  book does not specify (`Conjecture10_2`).
- Conjecture IV.10.3: $`\Lambda(E, s) = N^{s/2}(2\pi)^{-s}\Gamma(s)L(E, s)`$ continues meromorphically with
  $`\Lambda(E, s) = \pm\Lambda(E, 2 - s)`$ (`Conjecture10_3`). Proved comparisons: it implies the meromorphic
  continuation statement of Formal Conjectures over $`\mathbb{Q}`$ (`conjecture10_3_existsMeromorphicContinuationRat`), as
  does Formal Conjectures' analytic one (`existsAnalyticContinuationRat_completedL`).
- Conjecture IV.10.5 (Birch and Swinnerton-Dyer, leading term): as printed (`Conjecture10_5`, for one curve;
  `Conjecture10_5All`, for all curves over $`\mathbb{Q}`$ given by minimal equations) and with the standard
  normalization (`Conjecture10_5Corrected`). Proved comparisons: the two forms agree in rank 0
  (`conjecture10_5_iff_corrected_of_rank_eq_zero`) and contradict each other in positive rank
  (`not_conjecture10_5_and_corrected`); for the comparison with `StrongBSD` see the Highlights (unconditional) and
  the conditional theorems above.

**Formal Conjectures** (vendored definitions, namespace `NumberFieldKB.FormalConjectures`, Apache 2.0; see
[NOTICE](NOTICE)): `WeakBSD`, `StrongBSD` (with `bsdQuotient`, `regulator`, `tamagawaProduct`, `period`,
`tateShafarevich`), `ExistsAnalyticContinuationRat` and `ExistsMeromorphicContinuationRat`. Only the definitions
are vendored; the conjectures stated there with `sorry` are not, and the instance of finite generation that
Formal Conjectures proves by `sorry` is an explicit instance argument here.

## Known restrictions

Restrictions of the statements of this release beyond those of the sources, and inputs the headlines above rely on:

- Weil, *Basic Number Theory*, Chapters IV and VII: 29 items of Chapter IV and 10 of Chapter VII, stated by Weil in
  the general setting (function fields, or the noncommutative case), are formalized for number fields only (the book
  maps list them).
- Milne, *Elliptic Curves*, Conjecture IV.10.5 as printed: the leading coefficient is off by $`2^r`$ (the
  normalization above); both forms are stated.
- The named input `ZeroComponentIndex` of the conditional local Tamagawa measure theorem is not proved here. The
  inputs of the two conditional comparisons with `StrongBSD` (`ShaComparison`, `PeriodComparison`,
  `TamagawaComparison`, `LocalPointsInjective`) are all proved now; those two theorems are kept, unchanged, next to the
  unconditional `bsd_milne_iff_strongBSD_unconditional`.
- The measure $`\int_{E(\mathbb{Q}_p)}|\omega|`$ is defined by its formula on the $`x`$-line (the push-forward of
  $`|\omega|`$ to the $`x`$-coordinate, as for Formal Conjectures' real period), not as a measure on the $`p`$-adic
  manifold $`E(\mathbb{Q}_p)`$, which Mathlib does not have; the measure formula at $`p = 2`$ is a named input.
- Theorem IV.3.1 (finiteness of the Selmer groups) is proved over $`\mathbb{Q}`$ only, not over every number field;
  Mordell's theorem for nonsingular plane cubics (Theorem I.2.1) remains a named statement (it needs Nagell's
  reduction to Weierstrass form).
- Conjecture IV.10.3 and Formal Conjectures' analytic continuation statement are not logically equivalent (10.3 has a
  functional equation and allows poles); only the continuation halves are compared.
- Conjecture IV.10.2 is stated for complete intersections and without a functional equation.
- In Conjectures IV.10.3 and IV.10.5 the conductor is existentially quantified among the integers satisfying Milne's
  description (Ogg's formula at 2 and 3 is not formalized), and finite generation of $`E(\mathbb{Q})`$ is an instance
  argument of the statements; the comparisons `bsd_milne_iff_strongBSD_rat` and
  `bsd_milne_iff_strongBSD_unconditional` (and the two in rank 0 and in positive rank) supply it from Mordell–Weil.
- Kummer approximation (`kummer_approx_padic`) and local injectivity are proved for elliptic curves over
  $`\mathbb{Q}`$ only, not over every number field; Kummer approximation at the finite places is stated for prime
  $`\ell`$ (the library proves every $`\ell \ge 1`$ over $`\mathbb{Q}_p`$).
- In the statements of `localPoints_injective_rat` and `kummer_approx_padic`, the completions of $`\mathbb{Q}`$ carry
  their own $`\mathbb{Q}`$-algebra structure (the generic one of a division ring of characteristic zero is switched
  off, as in the library); the two structures are equal, so this only fixes the term that is written.

## Layout

```
Challenge.lean          the headline statements (proofs: deliberate sorry)
Solution.lean           the same statements, proved from the library
comparator.json         the per-book `lake comparator` checks (configurations in comparator/)
Challenge_<book>.lean   the headline statements of one book (generated from Challenge.lean; Solution_<book>.lean likewise)
formalization.yaml      scope, sources, divergences, provenance, review (formalization.yaml v0.4)
docs/results/books/     the book maps; docs/results/comparison.md: comparison with Mathlib and Tau Ceti
NumberFieldKB/
  MilneANT/             Milne, Algebraic Number Theory
  MilneCFT/             Milne, Class Field Theory
  WeilBNT/              Weil, Basic Number Theory (number fields; FunctionField/: function fields)
  Ideles/, HeckeCharacter/, LocalZeta/, GlobalZeta/, HeckeL/
                        Tate's thesis: ideles, Hecke characters, local and global zeta integrals,
                        Hecke L-functions and the Dedekind zeta function
  Pontryagin/           Pontryagin duality, Fourier inversion, the dual measure
  ModularCurves/        the modular curves X_0(N) over ℚ
  TauCetiPort/          files ported from Tau Ceti (Apache 2.0), see its README
  YamaguchiPort/        files ported from N. Yamaguchi's class field theory library (Apache 2.0), see its README
  PNTPort/              the strong prime number theorem, ported from PrimeNumberTheoremAnd (Apache 2.0)
  MilneEC/              Milne, Elliptic Curves (Chapter V, §§1–3 with ModularCurves/)
  FormalConjectures/    definitions vendored from Formal Conjectures (Apache 2.0): the statements of Birch and
                        Swinnerton-Dyer and of the continuation of L(E, s)
  Chebotarev/, NonVanishing/, HilbertClassField/
                        supporting files outside this release's books (see below)
references.bib          bibliography; the keys used by @[kb]
scripts/check_axioms.lean  prints the axioms of the headline theorems (run in CI)
scripts/verify-comparator.sh  runs `lake comparator` with the toolchain's kernels (run in CI)
scripts/check_map_names.lean  checks that every Lean name in the book maps exists (run in CI)
```

**Supporting files outside this release's books.** The books import 19 files on
the Chebotarev density theorem, 10 on the non-vanishing of $`L`$-functions on $`\operatorname{Re} s = 1`$ and 4 on the
Hilbert class field. They are shipped so that the library builds; those topics are not part of this release, and some
of their files state named results of those books without proof (no headline and no row marked *proved* in the book
maps depends on them).

## Usage

```bash
lake exe cache get       # once: download prebuilt Mathlib
lake build               # build and check everything
lake env lean scripts/check_axioms.lean   # axioms of the headline theorems
./scripts/verify-comparator.sh MilneCFT   # one book's Solution against its Challenge (Linux; needs bubblewrap)
```

The quadratic-forms dependency and this library are built from source (about 4,000 modules besides Mathlib's
prebuilt cache, most of them the ported class field theory files). A cold build took about two hours on 8 cores, with
at most 9.8 GB of memory in use (the largest single Lean process 7.9 GB); the CI workflow adds swap space to GitHub's
runner (4 cores, 16 GB), where it takes longer. `lake comparator` took 4 to 17 minutes per book on 8 cores (at most
8.1 GB of memory; Milne's *Elliptic Curves*, with 20 headlines, the longest), except for Milne's *Class Field Theory*:
about 38 minutes and 9.5 GB, most of it in the Lean kernel's replay of the class field theory behind its headlines.

## Provenance

NumberFieldKB was written by AI, with Claude Code (Anthropic): almost entirely by Claude Opus 5.5, with a share by
Claude Sonnet 5.5, in October and November 2026. Jonathan Hanke designed and directed it: he chose the books, the
results, the conventions and the proof routes. The files under `NumberFieldKB/TauCetiPort/` are by the Tau Ceti
contributors (see their headers), and those under `NumberFieldKB/YamaguchiPort/` and `NumberFieldKB/PNTPort/` by
N. Yamaguchi and by the PrimeNumberTheoremAnd contributors; each port lists its changes in its README. The
definitions under `NumberFieldKB/FormalConjectures/` are vendored from Formal Conjectures (Google DeepMind), with the
changes listed in the file header.
The proofs are checked by the Lean kernel, and CI checks that the headline theorems use only the standard axioms.
The 47 headline statements of this release in `Challenge.lean` (44 unconditional, 3 conditional), the conjecture
statements and the definitions they use have **not yet been
reviewed** by a human; that review is planned for a later release. `lake comparator` (once per book) checks that
`Solution.lean` proves exactly the statements of `Challenge.lean`. The rest of the library (its other definitions and intermediate
results, and the book maps) has not been reviewed by a human; as with any AI-written formalization, treat it as
untrustworthy until checked against the literature. Corrections and reports of mis-formalizations are very welcome.

## Releases

Releases are tagged with semantic versions; `main` continues to develop. The DOI [10.5281/zenodo.24047657](https://doi.org/10.5281/zenodo.24047657) always resolves to the latest release. To cite a specific version, use its release page or the "Cite this repository" button.

- **[v0.1.0](https://github.com/jonhanke/algebraic-number-theory-lean/releases/tag/v0.1.0)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.24047658](https://doi.org/10.5281/zenodo.24047658): the first release: five book maps and 20 headline statements.
- **[v0.2.0](https://github.com/jonhanke/algebraic-number-theory-lean/releases/tag/v0.2.0)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.24092975](https://doi.org/10.5281/zenodo.24092975): Milne's *Class Field Theory* as a
  sixth book (its map, with the three errata of Chapter V marked and their corrected forms proved) and three new
  headline statements; the 20 headlines of v0.1.0 are unchanged. Four further results of the book are proved in the
  library and become headlines in a later release, once their comparator checks fit a standard machine (the Lean
  kernel's replay of their long chains of class field theory takes more memory than the checks are allowed; each
  file of those chains re-checks quickly on its own): Theorem VIII.2.6, every central division algebra over a number
  field is cyclic (`NumberFieldKB.MilneCFT.Ch8.T26.theorem2_6`); local Kronecker–Weber in Lubin–Tate form
  (`NumberFieldKB.MilneCFT.LocalCFT.localKroneckerWeber`); Eisenstein reciprocity
  (`NumberFieldKB.MilneCFT.Ch8.Eisenstein.eisensteinReciprocity`); and Furtwängler's theorem
  (`NumberFieldKB.MilneCFT.Ch8.Eisenstein.theorem5_14`). The comparator now runs once per book.
- **[v0.2.1](https://github.com/jonhanke/algebraic-number-theory-lean/releases/tag/v0.2.1)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.24128217](https://doi.org/10.5281/zenodo.24128217): the four results of Milne's *Class Field Theory* held back in v0.2.0 are
  headlines again (27 in all): Theorem VIII.2.6 (`centralDivisionAlgebra_cyclic`), local Kronecker–Weber in
  Lubin–Tate form (`localKroneckerWeber_lubinTate`), Eisenstein reciprocity (`eisensteinReciprocity`) and
  Furtwängler's theorem (`furtwangler_fermat`), with the same statements as in v0.2.0's library. The kernel's replay
  of their proofs had exploded because one definition (the unramified extension of a local field) unfolded during
  type checking; it is now irreducible, and each of the four replays in at most about 20 minutes and 9 GB. Book-map
  rows completed: Lemmas VII.8.5, VII.8.6 and VIII.4.6 (stated in the map as Tau Ceti only in v0.2.0) and Example
  VIII.10.1 (a cubic Hecke character of $`\mathbb{Q}(\zeta_3)`$) are proved; Theorem V.3.33 is marked as stated
  in the book without proof; more rows of the $`X_0(N)`$ map are proved (Exercise 1.10 (a), (b); (c) conditional on
  a named input). No file of the library imports all of Mathlib any more: each imports the Mathlib modules it uses.
- **[v0.3.0](https://github.com/jonhanke/algebraic-number-theory-lean/releases/tag/v0.3.0)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.24283324](https://doi.org/10.5281/zenodo.24283324):
  Milne's *Elliptic Curves* as a seventh book (see "What's new in 0.3.0"): its map, six new unconditional headlines
  (Bézout's theorem, associativity of the group law on every plane cubic, the rank bound of explicit 2-descent,
  $`y^2 = x^3 - x`$ and the congruent number 1, Lang's theorem), a conditional theorem comparing Milne's form of the
  conjecture of Birch and Swinnerton-Dyer with Formal Conjectures' `StrongBSD`, and the conjectures of Chapter IV
  as statements; the 27 headlines of v0.2.1 are unchanged.
- **[v0.4.0](https://github.com/jonhanke/algebraic-number-theory-lean/releases/tag/v0.4.0)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.24317205](https://doi.org/10.5281/zenodo.24317205):
  the arithmetic of elliptic curves over $`\mathbb{Q}`$ (see "What's new in 0.4.0"): five new unconditional headlines
  ($`Ш[2] \cong (\mathbb{Z}/2)^2`$ and the 2-Selmer group of $`y^2 = x^3 + px`$, the local Tamagawa measure of
  $`E_0(\mathbb{Q}_p)`$ at every reduction type and of $`E(\mathbb{Q}_p)`$ at good reduction, the real period through the
  lattice, and Mazur's fifteen torsion groups realized), two new conditional theorems (Milne's Birch and
  Swinnerton-Dyer conjecture equivalent to `StrongBSD` with Mordell–Weil proved and one local input; the local
  Tamagawa measure at every reduction type), and Mordell–Weil over $`\mathbb{Q}`$ by Milne's descent; the 34 headlines
  of v0.3.0 are unchanged.
- **[v0.4.1](https://github.com/jonhanke/algebraic-number-theory-lean/releases/tag/v0.4.1)** (Lean and Mathlib v4.35.0), archived on Zenodo as [doi:10.5281/zenodo.24344156](https://doi.org/10.5281/zenodo.24344156):
  the comparison with `StrongBSD` made unconditional (see "What's new in 0.4.1"): six new unconditional headlines
  (Kummer approximation over $`\mathbb{Q}_p`$ at every prime including 2, local injectivity at every place of
  $`\mathbb{Q}`$, the isomorphism of the two Tate–Shafarevich groups, and, for every elliptic curve over $`\mathbb{Q}`$
  with a minimal equation and no named input, Milne's corrected Conjecture IV.10.5 equivalent to `StrongBSD`, the
  printed form equivalent to it in rank 0 and refuted by it in positive rank); the 41 headlines of v0.4.0 are
  unchanged.

**Not in this release** (planned for a later release): an item-by-item audit of Tate's thesis and of Folland's
Chapter 4 (their maps are built from the library's citations).

## License

Apache License 2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE). Files ported from Tau Ceti are Apache 2.0,
copyright the Tau Ceti contributors; files ported from N. Yamaguchi's library are Apache 2.0, copyright Naganori
Yamaguchi; files ported from PrimeNumberTheoremAnd are Apache 2.0, copyright its contributors; the definitions
vendored from Formal Conjectures are Apache 2.0, copyright the Formal Conjectures authors.
