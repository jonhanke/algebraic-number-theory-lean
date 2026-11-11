# Book maps

For each book in the scope of this release, a table from the items of the book to the Lean declarations and their status (generated from the coverage tables and the kernel-level input audit of the source repository).

| book | rows | proved | definitions | in Mathlib | conditional | other |
|---|---|---|---|---|---|---|
| [J. S. Milne, *Algebraic Number Theory*](milne-ant.md) | 328 | 132 | 17 | 179 | 0 | 0 |
| [J. S. Milne, *Class Field Theory*](milne-cft.md) | 513 | 348 | 58 | 105 | 0 | 2 |
| [A. Weil, *Basic Number Theory* (number fields and function fields)](weil-bnt.md) | 371 | 272 | 24 | 74 | 0 | 1 |
| [J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions* (Cassels–Fröhlich, Chapter XV)](tate-thesis.md) | 80 | 57 | 23 | 0 | 0 | 0 |
| [Pontryagin duality (Folland, *A Course in Abstract Harmonic Analysis*, Chapter 4; Weil II.§5, VII.§2)](pontryagin.md) | 24 | 22 | 2 | 0 | 0 | 0 |
| [The modular curves $X_0(N)$ (Milne, *Elliptic Curves*, Chapter V)](modular-curves.md) | 43 | 29 | 3 | 1 | 1 | 9 |

*Proved*: proved with only the standard axioms and no unproved input (in this library, in the quadratic-forms dependency, or in a file ported from Tau Ceti). *Definitions*: items that are definitions, formalized as Lean definitions. *Other*: proved in part, in Tau Ceti only, not formalized, stated in the book without proof, or formalized in the source library but not in this release (see each map). Rows that are not results are omitted from the maps.
