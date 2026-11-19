# Book maps

> Item-by-item maps of books that are not openly licensed are kept privately until licensing is confirmed (2026-11-18). The Lean code and its citations to each book stay here; the counts below are from the full maps.

For each book in the scope of this release, a table from the items of the book to the Lean declarations and their status (generated from the coverage tables and the kernel-level input audit of the source repository).

| book | rows | proved | definitions | in Mathlib | conditional | other |
|---|---|---|---|---|---|---|
| J. S. Milne, *Algebraic Number Theory* | 328 | 132 | 17 | 179 | 0 | 0 |
| J. S. Milne, *Class Field Theory* | 513 | 348 | 59 | 105 | 0 | 1 |
| J. S. Milne, *Elliptic Curves* | 318 | 230 | 44 | 10 | 5 | 29 |
| A. Weil, *Basic Number Theory* (number fields and function fields) | 371 | 272 | 24 | 74 | 0 | 1 |
| J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions* (Cassels–Fröhlich, Chapter XV) | 80 | 57 | 23 | 0 | 0 | 0 |
| [Pontryagin duality (Folland, *A Course in Abstract Harmonic Analysis*, Chapter 4; Weil II.§5, VII.§2)](pontryagin.md) | 24 | 22 | 2 | 0 | 0 | 0 |
| The modular curves $X_0(N)$ (Milne, *Elliptic Curves*, Chapter V) | 43 | 29 | 4 | 1 | 1 | 8 |

*Proved*: proved with only the standard axioms and no unproved input (in this library, in the quadratic-forms dependency, or in a file ported from Tau Ceti). *Definitions*: items that are definitions, formalized as Lean definitions. *Other*: proved in part, in Tau Ceti only, not formalized, stated in the book without proof, or formalized in the source library but not in this release (see each map). Rows that are not results are omitted from the maps.
