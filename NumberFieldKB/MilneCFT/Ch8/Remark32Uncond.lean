import NumberFieldKB.MilneCFT.Ch8.Remark32Local
import NumberFieldKB.MilneCFT.Ch8.Remark32Global

/-!
# Milne, *Class Field Theory*, Remark VIII.3.2, unconditional

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, Remark 3.2,
p. 234 (citing Cassels–Fröhlich, Exercise 5.3).

The named statement `Ch8.Remark3_2` (the Hasse norm theorem fails for the non-cyclic extension
$L = \mathbb Q(\sqrt{13}, \sqrt{17})$: $25$ is a local norm at every place but not a global norm) is proved here
(`R32.remark3_2`) from `R32.isLocalNorm_25`, `R32.isLocalNormInf_25` (local half) and `R32.not_exists_norm_eq_25`
(global half, by Hilbert reciprocity over $\mathbb Q$ from QuadFormsKB).
-/

namespace NumberFieldKB.MilneCFT.Ch8.R32

/-- **Remark VIII.3.2, unconditional** (Milne, *CFT*, VIII, Remark 3.2, p. 234): for every number field $L$ generated
over $\mathbb Q$ by square roots of $13$ and $17$, the rational $25$ is a local norm from $L$ at every finite and
infinite place of $\mathbb Q$, but not the norm of an element of $L$. -/
@[kb "milne2020cft" "Ch. VIII, Remark 3.2, p. 234"]
theorem remark3_2 : Remark3_2 where
  counterexample _ _ _ _ _ hs ht hgen :=
    ⟨isLocalNorm_25 hs ht hgen, isLocalNormInf_25 hs ht hgen, not_exists_norm_eq_25 hs ht hgen⟩

end NumberFieldKB.MilneCFT.Ch8.R32
