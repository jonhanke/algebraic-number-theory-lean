import NumberFieldKB.MilneCFT.Ch7.FirstInequality
import NumberFieldKB.MilneCFT.Ch7.Cohomology
import NumberFieldKB.MilneCFT.Ch7.KummerSetting
import NumberFieldKB.MilneCFT.Ch7.IdeleNormComparison
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Milne, *Class Field Theory*, Chapter VII: how the named statements combine

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

* `firstInequality_of_theorem4_3`: Theorem 4.3 gives the hypothesis `FirstInequality` of Lemma 4.5 (Corollary 4.4).
* `lemma_4_5_of_theorem4_3`: Lemma 4.5 from Theorem 4.3 (Proposition 2.8 is proved, `prop2_8`, so it is no longer
  a hypothesis).
-/

open IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable (K : Type) [Field K] [NumberField K]

/-- Theorem 4.3 implies the first inequality for all cyclic extensions (Corollary 4.4). -/
theorem firstInequality_of_theorem4_3 (h43 : Theorem4_3 K) : FirstInequality K :=
  fun L _ _ _ _ hc => cor_4_4 K L h43 hc

/-- **Lemma 4.5 from Theorem 4.3** (Milne, *CFT*, Chapter VII, p. 211); Proposition 2.8 is `prop2_8`. -/
@[kb "milne2020cft" "Ch. VII, Lemma 4.5 (from Thm. 4.3)"]
theorem lemma_4_5_of_theorem4_3 (h43 : Theorem4_3 K)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (hsolv : Group.IsSolvable Gal(L/K))
    (D : Subgroup (IdeleGroup (𝓞 K) K)) (hD : D ≤ normIdeles K L)
    (hdense : Dense ((IdeleGroup.principalSubgroup (𝓞 K) K ⊔ D : Subgroup (IdeleGroup (𝓞 K) K)) :
      Set (IdeleGroup (𝓞 K) K))) :
    Module.finrank K L = 1 :=
  lemma_4_5 K (firstInequality_of_theorem4_3 K h43) (prop2_8 K) L hsolv D hD hdense

end NumberFieldKB.MilneCFT.Ch7
