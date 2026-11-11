import NumberFieldKB.MilneCFT.Ch5Characters
import NumberFieldKB.MilneANT.Ch8Thm831
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Milne, *Class Field Theory*, Chapter V, Remark 3.26(d), unconditionally

`remark_3_26d` (`Ch5Characters.lean`) takes the named statement `MilneANT.Theorem8_31` (Chebotarev with natural
density) as a hypothesis. That statement is proved (`MilneANT.theorem8_31`, `MilneANT/Ch8Thm831.lean`, from the ported
Tau Ceti `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet`), so the remark holds unconditionally.
-/

open NumberField IsDedekindDomain
open NumberFieldKB.Chebotarev

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-- **Remark 3.26(d)** (Milne, *CFT*, V, p. 165), unconditional: the Chebotarev density theorem holds for natural
densities. -/
@[kb "milne2020cft" "Ch. V, Remark 3.26(d)"]
theorem remark_3_26d' (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (C : ConjClasses Gal(L/K)) :
    MilneANT.HasNaturalDensity (frobSet K L C) (Nat.card C.carrier / Nat.card Gal(L/K)) :=
  remark_3_26d MilneANT.theorem8_31 L C

end NumberFieldKB.MilneCFT
