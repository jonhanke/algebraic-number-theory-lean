import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiNFMain
import QuadFormsKB.Literature.HasseNorm.Main
import QuadFormsKB.Lattices.SACorrection
import QuadFormsKB.Witt.Represents
import QuadFormsKB.Lattices.KneserLocal
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Literature.LocalGlobal.HasseIsometryNF
import QuadFormsKB.Lattices.StrongApproximationProof
import QuadFormsKB.Tamagawa.LocalRankFive
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain
import QuadFormsKB.Tamagawa.FormClassNF
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationNF
import QuadFormsKB.Literature.LocalGlobal.PrescribedNF
import QuadFormsKB.Literature.Classical.SumsOfSquares
import QuadFormsKB.Witt.Extension
import QuadFormsKB.Witt.Cancellation
import QuadFormsKB.Literature.LocalGlobal.HasseConventionsNF
import NumberFieldKB.HeckeL.Basic
import NumberFieldKB.MilneCFT.Intro.RayClass

/-!
# Milne, *Class Field Theory*, Chapter VIII: items formalized elsewhere (citations)

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII,
printed pp. 250–263 (printed page = pdf page − 9).

The declarations below are proved in QuadFormsKB, NumberFieldKB or Mathlib in the book's form (up to the
conventions noted); they receive the `milne2020cft` tag here. The items whose form differs from the book's are restated
in `Quadratic.lean` and `QuadraticForms.lean`.

* **Proposition 6.1** (p. 251): `QuadFormsKB.QuadForm.exists_isometric_diag_cons` — a nondegenerate form representing
  $a \ne 0$ is isometric to $\langle a\rangle \perp r$ (matrix form, characteristic $0$; Milne: characteristic
  $\ne 2$).
* Symmetries (definition in prose, p. 251): `QuadraticForm.Witt.reflection` (formula `reflection_apply`).
* Consequence of 6.2 (cancellation, p. 251): `QuadraticForm.equivalent_of_prod_equivalent_prod_of_associated`.
* Equivalence of quadratic forms (definition in prose, p. 251): `QuadFormsKB.QuadForm.IsometricIn`.
* **Theorem 6.3** (Hasse–Minkowski, p. 252): `QuadFormsKB.Tamagawa.FormClassNF.isometricIn_of_everywhere_nf`
  (nondegenerate forms; Milne reduces to that case).
* **Remark 6.6** (p. 253): `QuadFormsKB.NFPlace.hasseOMeara_eq_negOne` ($S = \varepsilon\cdot(-1,d)$).
* **Proposition 6.7** (p. 253): `QuadFormsKB.NFPlace.hasseOMeara_isometric` (diagonal forms with coefficients in
  $F$, at every place of a number field).
* **Proposition 6.9** (p. 254): `QuadFormsKB.PadicClass.represents_two_iff`, `QuadFormsKB.PadicClass.represents_three_iff`,
  `QuadFormsKB.PadicClass.represents_of_four_le` (fields with the local Hilbert symbol axioms, Serre's $\varepsilon$).
* **Theorem 6.10** (p. 255): `QuadFormsKB.NFPlace.isometric_iff_hasseOMeara` (Milne's $S$, all places of a number
  field).
* Forms over $\mathbb C$ and $\mathbb R$ (p. 252): Mathlib's `QuadraticForm.equivalent_of_isAlgClosed` (rank) and
  `QuadraticForm.equivalent_one_neg_one_weighted_sum_squared` (Sylvester).
* **Proposition 6.14** (Gauss, p. 258): `QuadFormsKB.Grosswald.legendre_three_squares`.
* Hecke $L$-series (definition in prose, p. 262): `NumberFieldKB.HeckeL.heckeL` with Euler factors
  `NumberFieldKB.HeckeL.localL` (factor $1$ at ramified primes; characters need not be unitary).
-/

attribute [kb "milne2020cft" "Ch. VIII, Proposition 6.1, p. 251"] QuadFormsKB.QuadForm.exists_isometric_diag_cons
attribute [kb "milne2020cft" "Ch. VIII, §6, p. 251 (symmetry with respect to y)"] QuadraticForm.Witt.reflection
attribute [kb "milne2020cft" "Ch. VIII, §6, p. 251 (Witt cancellation, from Proposition 6.2)"]
  QuadraticForm.equivalent_of_prod_equivalent_prod_of_associated
attribute [kb "milne2020cft" "Ch. VIII, §6, p. 251 (equivalence of quadratic forms)"] QuadFormsKB.QuadForm.IsometricIn
attribute [kb "milne2020cft" "Ch. VIII, Theorem 6.3, p. 252 (Hasse-Minkowski)"]
  QuadFormsKB.Tamagawa.FormClassNF.isometricIn_of_everywhere_nf
attribute [kb "milne2020cft" "Ch. VIII, Remark 6.6, p. 253"] QuadFormsKB.NFPlace.hasseOMeara_eq_negOne
attribute [kb "milne2020cft" "Ch. VIII, Proposition 6.7, p. 253"] QuadFormsKB.NFPlace.hasseOMeara_isometric
attribute [kb "milne2020cft" "Ch. VIII, Proposition 6.9 (b), p. 254"] QuadFormsKB.PadicClass.represents_two_iff
attribute [kb "milne2020cft" "Ch. VIII, Proposition 6.9 (c), p. 254"] QuadFormsKB.PadicClass.represents_three_iff
attribute [kb "milne2020cft" "Ch. VIII, Proposition 6.9 (d), p. 254"] QuadFormsKB.PadicClass.represents_of_four_le
attribute [kb "milne2020cft" "Ch. VIII, Theorem 6.10, p. 255"] QuadFormsKB.NFPlace.isometric_iff_hasseOMeara
attribute [kb "milne2020cft" "Ch. VIII, Proposition 6.14, p. 258 (Gauss)"] QuadFormsKB.Grosswald.legendre_three_squares
attribute [kb "milne2020cft" "Ch. VIII, §10, p. 262 (Hecke L-series)"] NumberFieldKB.HeckeL.heckeL
attribute [kb "milne2020cft" "Ch. VIII, §3, p. 235 (nondegenerate quadratic form)"] QuadFormsKB.QuadForm.Nondegenerate
attribute [kb "milne2020cft" "Ch. VIII, §10, p. 261 (Artin L-series)"] NumberFieldKB.MilneCFT.artinLFunction
attribute [kb "milne2020cft" "Ch. VIII, Example 5.6, p. 246 ((a,b) = 1 iff the ternary form represents 0)"]
  QuadFormsKB.hilbertSymbol_eq_one_iff_isotropic
attribute [kb "milne2020cft" "Ch. VIII, Example 5.6, p. 246 ((a,b) = 1 iff the conic has a point)"]
  QuadFormsKB.hilbertSymbol_eq_one_iff_conic
attribute [kb "milne2020cft" "Ch. VIII, Example 5.6, p. 246 ((a,b) = 1 iff b is a norm from K[√a])"]
  QuadFormsKB.HasseNorm.norm_tensor_iff_hilbert
attribute [kb "milne2020cft" "Ch. VIII, §6, p. 252 (forms over an algebraically closed field are classified by rank)"]
  QuadraticForm.equivalent_of_isAlgClosed
attribute [kb "milne2020cft" "Ch. VIII, §6, p. 252 (Sylvester's theorem over R)"]
  QuadraticForm.equivalent_one_neg_one_weighted_sum_squared
