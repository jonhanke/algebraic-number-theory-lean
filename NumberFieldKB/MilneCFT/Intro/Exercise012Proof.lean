import NumberFieldKB.MilneCFT.Intro.ExercisesProofs
import NumberFieldKB.MilneANT.Ch4Example46

/-!
# Proof of Milne, *CFT*, Introduction, Exercise 0.12

`NumberFieldKB.MilneCFT.exercise012_of_classNumber` (`Intro/ExercisesProofs.lean`) proves Exercise 0.12 from
`h(ℚ[√-5]) = 2`; this file supplies it from `NumberFieldKB.MilneANT.Q5.class_number_two`
(`MilneANT/Ch4Example46.lean`, Milne *ANT* Example 4.6).
-/

open NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT

/-- **Exercise 0.12** (proved; Milne, *CFT*, Introduction): `ℚ[√5, √-1]` is the Hilbert class field of `ℚ[√-5]`.
The extension `E/F` is unramified at every finite prime (the different contains `2i` and `√5`, and `2`, `5` generate the
unit ideal) and at the infinite places (`F` is totally complex); it is abelian of degree `2`, so Artin reciprocity
gives a Frobenius-compatible homomorphism `Cl(F) → Gal(E/F)`, which is onto (Chebotarev) between groups of order `2`
(`class_number_two`). -/
@[kb "milne2020cft" "Introduction, Exercise 0.12"]
theorem exercise012 : Exercise012 :=
  exercise012_of_classNumber fun F _ _ hF ⟨s, hs⟩ =>
    MilneANT.Q5.class_number_two hF ⟨s, MilneANT.isIntegral_of_sq_eq (-5) s (by rw [hs]; simp)⟩
      (RingOfIntegers.ext (by push_cast; exact hs))

end NumberFieldKB.MilneCFT
