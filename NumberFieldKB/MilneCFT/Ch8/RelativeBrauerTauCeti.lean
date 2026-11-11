import NumberFieldKB.MilneCFT.Ch8.RelativeBrauer
import NumberFieldKB.MilneCFT.Ch4BrauerTauCeti
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Milne, *Class Field Theory*, VIII Theorem 4.2 and Corollary 4.3 from Tau Ceti

Theorem 4.2 (= IV, Example 2.14(e)) is proved from Tau Ceti's fundamental exact sequence and the comparison
`Ch4.BrauerBaseChangeTauCeti K`, which is now proved (`Ch4.brauerBaseChangeTauCeti`), so Theorem 4.2 is unconditional
(`Ch8.theorem_4_2'`). Corollary 4.3 remains conditional on the two local-to-global inputs `LocalRelBrOrder` and
`RelativeHasse`. The earlier forms with the comparison as a hypothesis are kept; the originals are unchanged.
-/

namespace NumberFieldKB.MilneCFT.Ch8

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

/-- **Theorem 4.2** (Milne, *CFT*, VIII, Theorem 4.2, p. 240): the fundamental exact sequence, from Tau Ceti and the
comparison `Ch4.BrauerBaseChangeTauCeti K`. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Thm. 4.2, p. 240"]
theorem theorem_4_2_of_brauerBaseChange (hB : Ch4.BrauerBaseChangeTauCeti K) : Ch4.Example2_14e K :=
  Ch4.example2_14e_of_brauerBaseChange hB

/-- **Theorem 4.2, unconditional** (Milne, *CFT*, VIII, Theorem 4.2, p. 240): for every number field $K$ the sequence
$0\to\mathrm{Br}(K)\to\bigoplus_v\mathrm{Br}(K_v)\to\mathbb Q/\mathbb Z\to0$ is exact. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Thm. 4.2, p. 240"]
theorem theorem_4_2' : Ch4.Example2_14e K :=
  Ch4.example2_14e K

/-- **Corollary 4.3** (Milne, *CFT*, VIII, Cor. 4.3, p. 241), with Theorem 4.2 replaced by the comparison
`Ch4.BrauerBaseChangeTauCeti K`; still conditional on `LocalRelBrOrder` and `RelativeHasse`. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Cor. 4.3, p. 241 (proof)"]
theorem corollary4_3_of_brauerBaseChange [IsGalois K L] (hB : Ch4.BrauerBaseChangeTauCeti K)
    (hloc : LocalRelBrOrder K L) (hH : RelativeHasse K L) : Corollary4_3 K L :=
  corollary4_3_of K L (Ch4.example2_14e_of_brauerBaseChange hB) hloc hH

/-- **Corollary 4.3** (Milne, *CFT*, VIII, Cor. 4.3, p. 241), with Theorem 4.2 proved: conditional only on the
local orders `LocalRelBrOrder` and the Hasse principle for $L$ read over $K$ (`RelativeHasse`). -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Cor. 4.3, p. 241 (proof)"]
theorem corollary4_3' [IsGalois K L] (hloc : LocalRelBrOrder K L) (hH : RelativeHasse K L) :
    Corollary4_3 K L :=
  corollary4_3_of K L (Ch4.example2_14e K) hloc hH

end NumberFieldKB.MilneCFT.Ch8
