# Algebraic number theory in Lean 4

[![Lean build](https://github.com/jonhanke/algebraic-number-theory-lean/actions/workflows/build.yml/badge.svg)](https://github.com/jonhanke/algebraic-number-theory-lean/actions/workflows/build.yml) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24047657.svg)](https://doi.org/10.5281/zenodo.24047657)

A Lean 4 library (built on Mathlib v4.35.0) that formalizes six texts of algebraic number theory item by item:
Milne's *Algebraic Number Theory* and *Class Field Theory*, Weil's *Basic Number Theory* (number fields and function fields over finite
fields), Tate's thesis, Pontryagin duality for locally compact abelian groups, and the modular curves $`X_0(N)`$ of
Milne's *Elliptic Curves*. The Lean library is called `NumberFieldKB`. It depends on
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

## The books

| book | rows | proved | definitions | in Mathlib | conditional | other |
|---|---|---|---|---|---|---|
| [J. S. Milne, *Algebraic Number Theory*](docs/results/books/milne-ant.md) | 328 | 132 | 17 | 179 | 0 | 0 |
| [J. S. Milne, *Class Field Theory*](docs/results/books/milne-cft.md) | 513 | 348 | 58 | 105 | 0 | 2 |
| [A. Weil, *Basic Number Theory* (number fields and function fields)](docs/results/books/weil-bnt.md) | 371 | 272 | 24 | 74 | 0 | 1 |
| [J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions* (Cassels–Fröhlich, Chapter XV)](docs/results/books/tate-thesis.md) | 80 | 57 | 23 | 0 | 0 | 0 |
| [Pontryagin duality (Folland, *A Course in Abstract Harmonic Analysis*, Chapter 4; Weil II.§5, VII.§2)](docs/results/books/pontryagin.md) | 24 | 22 | 2 | 0 | 0 | 0 |
| [The modular curves $X_0(N)$ (Milne, *Elliptic Curves*, Chapter V)](docs/results/books/modular-curves.md) | 43 | 29 | 3 | 1 | 1 | 9 |

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
above, with a docstring for each and a list of the library definitions the statements use; every proof there is a
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
field (see the [comparison](docs/results/comparison.md)).

**Errata of Milne's *Class Field Theory*.** Three statements of Chapter V are false as printed: Theorem 2.4(b) (the
series need not converge on $`\operatorname{Re} s > 0`$; it extends there), Exercise 3.15 (the existence clause needs
the primes of $`S`$ in $`H`$) and Remark 4.8 (the first sentence needs $`G`$ complete; the second also needs the
character to be trivial on the identity component of $`K_\infty^\times`$). The corrected forms are proved, and the
printed forms of Exercise 3.15 and Remark 4.8 are refuted in Lean; the [map of the book](docs/results/books/milne-cft.md)
marks these rows.

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
  MilneEC/              Milne, Elliptic Curves: Chapter V, §§1–3 (with ModularCurves/), and supporting files
  Chebotarev/, NonVanishing/, HilbertClassField/
                        supporting files outside this release's books (see below)
references.bib          bibliography; the keys used by @[kb]
scripts/check_axioms.lean  prints the axioms of the headline theorems (run in CI)
scripts/verify-comparator.sh  runs `lake comparator` with the toolchain's kernels (run in CI)
scripts/check_map_names.lean  checks that every Lean name in the book maps exists (run in CI)
```

**Supporting files outside this release's books.** The books import 39 files of the library's elliptic curve topic
(Milne, *Elliptic Curves*; the files of Chapter V, §§1–3 among them carry the $`X_0(N)`$ map), 19 files on
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
prebuilt cache, most of them the ported class field theory files). A cold build took about two hours on 8 cores,
with at most 9.6 GB of memory in use (the largest single Lean process 8.3 GB); the CI workflow adds swap space to GitHub's runner (4 cores, 16 GB), where it takes
longer. `lake comparator` took 5 to 11 minutes per book on 8 cores (at most 7.6 GB of memory), except for Milne's
*Class Field Theory*: about 39 minutes and 9.6 GB, most of it in the Lean kernel's replay of the class field theory
behind its headlines.

## Provenance

NumberFieldKB was written by AI, with Claude Code (Anthropic): almost entirely by Claude Opus 5.5, with a share by
Claude Sonnet 5.5, in October and November 2026. Jonathan Hanke designed and directed it: he chose the books, the
results, the conventions and the proof routes. The files under `NumberFieldKB/TauCetiPort/` are by the Tau Ceti
contributors (see their headers), and those under `NumberFieldKB/YamaguchiPort/` and `NumberFieldKB/PNTPort/` by
N. Yamaguchi and by the PrimeNumberTheoremAnd contributors; each port lists its changes in its README.
The proofs are checked by the Lean kernel, and CI checks that the headline theorems use only the standard axioms.
The 27 headline statements of this release in `Challenge.lean`, and the definitions they use, have **not yet been
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

**Not in this release** (planned for a later release): the rest of *Elliptic Curves* as a book; an item-by-item audit of Tate's thesis and of Folland's Chapter 4 (their maps are built from the library's
citations).

## License

Apache License 2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE). Files ported from Tau Ceti are Apache 2.0,
copyright the Tau Ceti contributors; files ported from N. Yamaguchi's library are Apache 2.0, copyright Naganori
Yamaguchi; files ported from PrimeNumberTheoremAnd are Apache 2.0, copyright its contributors.
