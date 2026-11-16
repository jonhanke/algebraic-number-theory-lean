import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.NumberTheory.ModularForms.LFunction
import QuadFormsKB.Citation

/-!
# Milne, *Elliptic Curves*, Chapter V §§1–4: definitions that are in Mathlib

Source tags for the definitions of Chapter V §§1–4 of Milne, *Elliptic Curves* (`milne2006ec`) that Mathlib has in
the book's form (up to normalisation; the comparisons are proved in `Ch5ModularForms` and `Ch5LSeries`).

* Modular forms and cusp forms (Definition 3.1, pdf p. 198): `ModularForm`, `CuspForm`, with Mathlib's integer
  weight $w$ for Milne's $2k$ (comparison: `NumberFieldKB.MilneEC.V.def_3_1`).
* The $L$-series of an elliptic curve over $\mathbb Q$ (pdf p. 202): `WeierstrassCurve.LFunction` (a formal
  Dirichlet series, the Euler product over primes with Milne's local factors) and `WeierstrassCurve.LSeries`.
* The Mellin transform (pdf p. 205): `mellin`; the $L$-function of a cusp form, with and without its
  $\Gamma$-factor: `ModularForm.Λ`, `ModularForm.L`.
-/

attribute [kb "milne2006ec" "Ch. V, Definition 3.1 (modular and cusp forms), pdf p. 198"]
  ModularForm CuspForm

attribute [kb "milne2006ec" "Ch. V, §4, the L-series L(E,s) of an elliptic curve (definition in prose), pdf p. 202"]
  WeierstrassCurve.LFunction WeierstrassCurve.LSeries

attribute [kb "milne2006ec" "Ch. V, §4, Mellin transform and L(f,s) (definition in prose), pdf p. 205"]
  mellin ModularForm.Λ ModularForm.L
