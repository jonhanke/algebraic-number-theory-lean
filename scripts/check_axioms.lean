/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Solution

/-!
# Axiom check for the headline theorems

`lake env lean scripts/check_axioms.lean` prints the axioms each headline theorem depends on.
Every line should list only `propext`, `Classical.choice` and `Quot.sound`; the CI workflow
fails if any other axiom (in particular `sorryAx`) appears.
-/

-- Milne, *Algebraic Number Theory*
#print axioms NumberFieldKB.Headlines.kummer_regular
#print axioms NumberFieldKB.Headlines.dedekind_factorizationType
#print axioms NumberFieldKB.Headlines.ostrowski_numberField

-- Weil, *Basic Number Theory*: number fields
#print axioms NumberFieldKB.Headlines.adeles_selfDual
#print axioms NumberFieldKB.Headlines.idele_classes_finite

-- Weil, *Basic Number Theory*: function fields
#print axioms NumberFieldKB.Headlines.zeta_functionField
#print axioms NumberFieldKB.Headlines.heckeL_functionField_polynomial

-- Tate's thesis
#print axioms NumberFieldKB.Headlines.tate_globalZeta_functionalEquation
#print axioms NumberFieldKB.Headlines.tate_globalZeta_residues
#print axioms NumberFieldKB.Headlines.heckeL_functionalEquation
#print axioms NumberFieldKB.Headlines.dedekindZeta_continuation
#print axioms NumberFieldKB.Headlines.completedDedekindZeta_functionalEquation

-- Pontryagin duality
#print axioms NumberFieldKB.Headlines.pontryaginDuality
#print axioms NumberFieldKB.Headlines.fourierInversion_dualMeasure
#print axioms NumberFieldKB.Headlines.pontryagin_closedSubgroups
#print axioms NumberFieldKB.Headlines.compact_iff_dual_discrete

-- The modular curves X₀(N)
#print axioms NumberFieldKB.Headlines.genus_X0
#print axioms NumberFieldKB.Headlines.modularPolynomial_rational
#print axioms NumberFieldKB.Headlines.modularFunctions_Gamma0
#print axioms NumberFieldKB.Headlines.cuspForms_weightTwo_finrank

-- Milne, *Class Field Theory*
#print axioms NumberFieldKB.Headlines.grunwaldWang
#print axioms NumberFieldKB.Headlines.centralDivisionAlgebra_cyclic
#print axioms NumberFieldKB.Headlines.localKroneckerWeber_lubinTate
#print axioms NumberFieldKB.Headlines.eisensteinReciprocity
#print axioms NumberFieldKB.Headlines.furtwangler_fermat
#print axioms NumberFieldKB.Headlines.gauss_cubicCurve_count
#print axioms NumberFieldKB.Headlines.weberL_continuation
