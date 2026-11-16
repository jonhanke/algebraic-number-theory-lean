import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import QuadFormsKB.Citation

/-!
# Milne, Elliptic Curves, Chapter III: definitions that are in Mathlib

Source tags for the definitions in the prose of Chapter III of Milne, *Elliptic Curves*
(`milne2006ec`) that Mathlib already has in the book's form.

* Riemann surface (pdf p. 97): a connected Hausdorff second-countable space with a complex
  structure is, in Mathlib, a `ChartedSpace ℂ X` with `IsManifold 𝓘(ℂ) ω X` (analytic transition
  maps; Mathlib uses the maximal atlas instead of Milne's equivalence class of coordinate
  coverings, which is the same thing).
* Algebraic integer and the ring `𝓞_K` of a number field (pdf p. 104): `IsIntegral ℤ`,
  `NumberField.RingOfIntegers`.
* Algebraic and transcendental complex numbers (pdf p. 106): `IsAlgebraic ℚ`, `Transcendental ℚ`.
-/

attribute [kb "milne2006ec" "Ch. III, §3, def. of Riemann surface (complex structure), pdf p. 97"]
  ChartedSpace IsManifold

attribute [kb "milne2006ec" "Ch. III, §3, def. of algebraic integer and O_K, pdf p. 104"]
  IsIntegral NumberField.RingOfIntegers

attribute [kb "milne2006ec" "Ch. III, Aside 3.19, def. of algebraic and transcendental numbers, pdf p. 106"]
  IsAlgebraic Transcendental
