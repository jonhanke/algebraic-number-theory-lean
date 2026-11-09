import NumberFieldKB.MilneCFT.LubinTate.KroneckerWeber
import NumberFieldKB.YamaguchiPort.ClassFieldTheory.KroneckerWeber.LocalCyclotomicEmbedding

/-!
# Local Kronecker–Weber over $\mathbb Q_p$, from Yamaguchi (Milne, *CFT*, I, Corollary 4.12)

Yamaguchi's class field theory library proves that every finite abelian extension of $\mathbb Q_p$ embeds in a
cyclotomic extension $\mathbb Q_p(\zeta_m)$, $m > 0$ (`KroneckerWeber.exists_localCyclotomicEmbedding`, ported under
`NumberFieldKB/YamaguchiPort/` from Yamaguchi main `fbd320cd`, Apache 2.0; its proof goes through Lubin–Tate theory and
local class field theory in Yamaguchi's library). The cyclotomic field there is Mathlib's `CyclotomicField m ℚ_[p]`,
the same type as in our named statement; the hypothesis there is Mathlib's `IsAbelianGalois`, which our hypotheses
(Galois with commuting Galois group) give. Yamaguchi's conclusion is stronger (a primitive $m$-th root of unity generates
the cyclotomic field); we keep the embedding.
-/

namespace NumberFieldKB.MilneCFT.LocalCFT

/-- **Corollary 4.12 (local Kronecker–Weber for $\mathbb Q_p$), proved** (Milne, *CFT*, I, Corollary 4.12): the named
statement `LocalKroneckerWeberQp p` holds, from Yamaguchi's `KroneckerWeber.exists_localCyclotomicEmbedding`
(ported). -/
@[kb "milne2020cft" "Ch. I, Corollary 4.12"]
theorem localKroneckerWeberQp (p : ℕ) [Fact p.Prime] : LocalKroneckerWeberQp p := by
  refine ⟨fun L _ _ _ _ hcomm => ?_⟩
  have : IsMulCommutative Gal(L/ℚ_[p]) := ⟨⟨hcomm⟩⟩
  have : IsAbelianGalois ℚ_[p] L := ⟨⟩
  obtain ⟨m, hm, -, -, -, hi⟩ := KroneckerWeber.exists_localCyclotomicEmbedding p L
  exact ⟨m, hm, hi⟩

end NumberFieldKB.MilneCFT.LocalCFT
