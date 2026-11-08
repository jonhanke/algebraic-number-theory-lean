import NumberFieldKB.MilneCFT.GlobalUnconditional
import NumberFieldKB.MilneCFT.Ch7.ArtinInertiaTauCeti

/-!
# Milne, *Class Field Theory*, Chapter V §5: Remark 5.8, unconditional

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter V, Remark 5.8, p. 180.

Remark 5.8 (`Remark5_8`) says that the idèlic theorems (Theorems 5.3 and 5.5) imply the ideal-theoretic ones
(Theorems 3.5 and 3.6). Both ideal-theoretic theorems are now proved unconditionally in this library
(`reciprocityLaw_ideal`, from the idèlic reciprocity law of the Tau Ceti port, and `existenceTheoremArtin`), so the
implications hold.
-/

namespace NumberFieldKB.MilneCFT

variable (K : Type) [Field K] [NumberField K]

/-- **Remark 5.8** (Milne, *CFT*, V, Remark 5.8, p. 180): the idèlic reciprocity law implies the ideal-theoretic one,
and with the idèlic existence theorem it implies the existence theorem (in the form with the Artin map). Both
conclusions are proved unconditionally (`reciprocityLaw_ideal`, `existenceTheoremArtin`). -/
@[kb "milne2020cft" "Ch. V, Remark 5.8, p. 180"]
theorem remark5_8 : Remark5_8 K :=
  ⟨fun _ => reciprocityLaw_ideal K, fun _ _ => existenceTheoremArtin K⟩

end NumberFieldKB.MilneCFT
