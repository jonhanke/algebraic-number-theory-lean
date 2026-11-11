import NumberFieldKB.MilneCFT.Ch5Remark48Extend
import NumberFieldKB.MilneCFT.Ch5Remark48Converse
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Milne, *Class Field Theory*, Chapter V, Remark 4.8: the corrected remark, proved

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter V, Remark 4.8, p. 174.
See `Ch5Remark48Corrected.lean` for the statement `Remark4_8Corrected` and the proof outline.
-/

open NumberField IsDedekindDomain Topology
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

variable (K) in
/-- **Remark 4.8, corrected**, proved. -/
@[kb "milne2020cft" "Ch. V, Remark 4.8 (corrected form, proved)"]
theorem remark4_8_corrected : Remark4_8Corrected K :=
  ⟨fun G _ _ _ _ _ S ψ hS hψ => remark4_8_extend G S ψ hS hψ,
    fun G _ _ _ _ hG φ hφ hK hinf => remark4_8_converse G hG φ hφ hK hinf⟩

end NumberFieldKB.MilneCFT
