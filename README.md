# Algebraic number theory in Lean 4

[![Lean build](https://github.com/jonhanke/algebraic-number-theory-lean/actions/workflows/build.yml/badge.svg)](https://github.com/jonhanke/algebraic-number-theory-lean/actions/workflows/build.yml)

A Lean 4 library (built on Mathlib v4.35.0) that formalizes five texts of algebraic number theory item by item:
Milne's *Algebraic Number Theory*, Weil's *Basic Number Theory* (number fields and function fields over finite
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
  `lake comparator` to check the proved statements against [`Challenge.lean`](Challenge.lean).
- **Comparison**: [docs/results/comparison.md](docs/results/comparison.md) says, for each headline and each chapter,
  what Mathlib and [Tau Ceti](https://github.com/TauCetiProject/TauCeti) already have and what this library adds.

## The books

| book | rows | proved | definitions | in Mathlib | conditional | other |
|---|---|---|---|---|---|---|
| [J. S. Milne, *Algebraic Number Theory*](docs/results/books/milne-ant.md) | 328 | 132 | 17 | 179 | 0 | 0 |
| [A. Weil, *Basic Number Theory* (number fields and function fields)](docs/results/books/weil-bnt.md) | 371 | 272 | 24 | 74 | 0 | 1 |
| [J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions* (Cassels–Fröhlich, Chapter XV)](docs/results/books/tate-thesis.md) | 80 | 57 | 23 | 0 | 0 | 0 |
| [Pontryagin duality (Folland, *A Course in Abstract Harmonic Analysis*, Chapter 4; Weil II.§5, VII.§2)](docs/results/books/pontryagin.md) | 24 | 22 | 2 | 0 | 0 | 0 |
| [The modular curves $X_0(N)$ (Milne, *Elliptic Curves*, Chapter V)](docs/results/books/modular-curves.md) | 43 | 20 | 2 | 1 | 2 | 18 |

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
`lake comparator` (configured by [`comparator.json`](comparator.json)) checks that each proved statement is exactly
the one in `Challenge.lean` and uses only the standard axioms. [`formalization.yaml`](formalization.yaml) records the
scope, sources, divergences from the literature, provenance and review status in the
[formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) format.

**Also proved here, not headlines because Tau Ceti has them:** Chebotarev's density theorem and Dirichlet's theorem
with natural density, Hermite–Minkowski with ramification in a finite set of primes, the $`S`$-unit theorem, and the
Riemann–Roch theorem for function fields (see the [comparison](docs/results/comparison.md)).

## Layout

```
Challenge.lean          the headline statements (proofs: deliberate sorry)
Solution.lean           the same statements, proved from the library
comparator.json         configuration for `lake comparator` (Solution against Challenge)
formalization.yaml      scope, sources, divergences, provenance, review (formalization.yaml v0.4)
docs/results/books/     the book maps; docs/results/comparison.md: comparison with Mathlib and Tau Ceti
NumberFieldKB/
  MilneANT/             Milne, Algebraic Number Theory
  WeilBNT/              Weil, Basic Number Theory (number fields; FunctionField/: function fields)
  Ideles/, HeckeCharacter/, LocalZeta/, GlobalZeta/, HeckeL/
                        Tate's thesis: ideles, Hecke characters, local and global zeta integrals,
                        Hecke L-functions and the Dedekind zeta function
  Pontryagin/           Pontryagin duality, Fourier inversion, the dual measure
  ModularCurves/        the modular curves X_0(N) over ℚ
  TauCetiPort/          files ported from Tau Ceti (Apache 2.0), see its README
  MilneEC/              Milne, Elliptic Curves: Chapter V, §§1–3 (with ModularCurves/), and supporting files
  MilneCFT/, Chebotarev/, NonVanishing/, HilbertClassField/
                        supporting files outside this release's books (see below)
references.bib          bibliography; the keys used by @[kb]
scripts/check_axioms.lean  prints the axioms of the headline theorems (run in CI)
scripts/verify-comparator.sh  runs `lake comparator` with the toolchain's kernels (run in CI)
```

**Supporting files outside this release's books.** The books import 39 files of the library's class field theory
(Milne, *Class Field Theory*) and elliptic curves (Milne, *Elliptic Curves*) topics, 19 files on the Chebotarev density
theorem, 10 on the non-vanishing of $`L`$-functions on $`\operatorname{Re} s = 1`$ and 3 on the Hilbert class field
They are shipped so that the library builds; those topics are not part of this release, and some of their files state named results of those books
without proof (no headline and no row marked *proved* in the book maps depends on them).

## Usage

```bash
lake exe cache get       # once: download prebuilt Mathlib
lake build               # build and check everything
lake env lean scripts/check_axioms.lean   # axioms of the headline theorems
./scripts/verify-comparator.sh            # Solution against Challenge (Linux; needs bubblewrap)
```

The quadratic-forms dependency and this library are built from source (about 1,600 modules besides Mathlib's
prebuilt cache). A cold build took about 40 minutes on 8 cores, with at most 8 GB of memory in use (the largest
single Lean process 8.2 GB); the CI workflow adds swap space to GitHub's runner (4 cores, 16 GB), where it takes
longer.

## Provenance

NumberFieldKB was written by AI, with Claude Code (Anthropic): almost entirely by Claude Opus 5.5, with a share by
Claude Sonnet 5.5, in October and November 2026. Jonathan Hanke designed and directed it: he chose the books, the
results, the conventions and the proof routes. The files under `NumberFieldKB/TauCetiPort/` are by the Tau Ceti
contributors (see their headers), ported with the changes listed in that directory's README.
The proofs are checked by the Lean kernel, and CI checks that the headline theorems use only the standard axioms.
The 20 headline statements of this release in `Challenge.lean`, and the definitions they use, have **not yet been
reviewed** by a human; that review is planned for a later release. `lake comparator` checks that `Solution.lean`
proves exactly the statements of `Challenge.lean`. The rest of the library (its other definitions and intermediate
results, and the book maps) has not been reviewed by a human; as with any AI-written formalization, treat it as
untrustworthy until checked against the literature. Corrections and reports of mis-formalizations are very welcome.

## Releases

Releases are tagged with semantic versions; `main` continues to develop.

- **v0.1.0** (Lean and Mathlib v4.35.0): the first release: five book maps and the 20 headline statements above.

**Not in this release** (planned for a later release): Milne's *Class Field Theory* and the rest of *Elliptic Curves*
as books; an item-by-item audit of Tate's thesis and of Folland's Chapter 4 (their maps are built from the library's
citations).

## License

Apache License 2.0; see [LICENSE](LICENSE). Files ported from Tau Ceti are Apache 2.0, copyright the Tau Ceti
contributors.
