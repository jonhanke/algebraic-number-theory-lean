import NumberFieldKB.MilneCFT.Ch8.Reciprocity
import NumberFieldKB.MilneCFT.Ch5Characters
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Class Field Theory*: Chapter V's power residue criterion, from Chapter VIII, 5.2 and 5.3

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter V, p. 166, and
Chapter VIII, 5.2–5.3. Chapter V (`Ch5Characters`) defines the power residue symbol through the Artin symbol and
states the criterion "$(a/\mathfrak p)_n = 1$ iff $a$ is an $n$th power modulo $\mathfrak p$" as a named statement;
it is proved here.

`Ch5Complements` and Chapter II's `Ch2Tate` both declared `Remark3_12`; Chapter V's is now `Ch5Remark3_12`, so this file
joins `Ch8.lean`.
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {K : Type} [Field K] [NumberField K]

/-- Chapter V's named `PowerResidueCriterion` holds: it follows from 5.2 and 5.3 (comparison of Chapter V's Artin-symbol
definition `powerResidueSymbol` with the residue definition). -/
@[kb "milne2020cft" "Ch. V, §3, p. 166 ((a/p)_n = 1 iff a is an n-th power mod p)"]
theorem powerResidueCriterion : PowerResidueCriterion K := by
  refine ⟨fun n ζ hζ L _ _ _ _ α a hα hgen v hnv hav => ?_⟩
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (by simp) hnv
    · exact h
  have ha0 : (a : K) ≠ 0 := by
    rintro h0
    exact hav (by rw [show a = 0 from Subtype.ext h0]; exact zero_mem _)
  have hv : v ∉ Sset n {(a : K)} := by
    rw [notMem_Sset_iff]
    exact ⟨hnv, (v.valuation_eq_one_iff_notMem (K := K)).2 hav⟩
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hα
    exact ha0 ((algebraMap K L).injective (by simpa using hα.symm))
  obtain ⟨-, h53⟩ := item_5_3 n hn ζ hζ (a : K) ha0 L α hα hgen v hv
  have hsym : powerResidueSymbol L α v = algebraMap K L (powerResidue n (a : K) v) := by
    rw [powerResidueSymbol, h53]; field_simp
  have h52 := (item_5_2 n hn ζ hζ (a : K) v hv).out 1 2
  rw [hsym, ← map_one (algebraMap K L), (algebraMap K L).injective.eq_iff, h52]
  refine exists_congr fun x => ?_
  rw [← v.valuation_lt_one_iff_mem (K := K)]
  simp

end NumberFieldKB.MilneCFT.Ch8
