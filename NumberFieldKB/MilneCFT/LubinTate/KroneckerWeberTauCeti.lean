import NumberFieldKB.MilneCFT.LubinTate.KroneckerWeber
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.ClassFields.KroneckerWeber

/-!
# Milne, *Class Field Theory*, Chapter I, Theorem 4.16 (Kronecker–Weber), proved from Tau Ceti

The named statement `NumberFieldKB.MilneCFT.LocalCFT.KroneckerWeber` is proved here (`LocalCFT.kroneckerWeber`) from
Tau Ceti's `TauCeti.ClassFieldTheory.kroneckerWeber` (ported,
`NumberFieldKB/TauCetiPort/NumberTheory/ClassFieldTheory/ClassFields/KroneckerWeber.lean`; Apache 2.0, the Tau Ceti
contributors), which is proved there from global class field theory (the conductor of an abelian extension of
$\mathbb Q$ and the Artin map of $\mathbb Q(\zeta_n)$). The statements have the same shape; ours asks for a Galois
extension with commuting Galois group, Tau Ceti's for Mathlib's `IsAbelianGalois`.
-/

namespace NumberFieldKB.MilneCFT.LocalCFT

/-- **Theorem 4.16 (Kronecker–Weber), proved** (Milne, *CFT*, I, Theorem 4.16): every finite abelian extension of
$\mathbb Q$ embeds in a cyclotomic field $\mathbb Q(\zeta_n)$. From Tau Ceti's `kroneckerWeber` (ported). -/
@[kb "milne2020cft" "Ch. I, Theorem 4.16"]
theorem kroneckerWeber : KroneckerWeber := by
  refine ⟨fun L _ _ _ hab => ?_⟩
  have : IsAbelianGalois ℚ L := { toIsGalois := inferInstance, toIsMulCommutative := ⟨⟨hab⟩⟩ }
  obtain ⟨n, hn, h⟩ := TauCeti.ClassFieldTheory.kroneckerWeber L
  exact ⟨n, Nat.pos_of_ne_zero hn, h⟩

end NumberFieldKB.MilneCFT.LocalCFT
