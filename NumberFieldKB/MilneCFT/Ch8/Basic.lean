import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, *Class Field Theory*, Chapter VIII: shared definitions

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII.

* `IsLocalPow n a v`: $a \in K$ is an $n$th power in the completion $K_v$ at a finite prime $v$ (Milne, VIII, §1 and
  5.2 (c)).
-/

open NumberField IsDedekindDomain

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {K : Type} [Field K] [NumberField K]

/-- $a \in K$ is an $n$th power in the completion $K_v$ at the finite prime $v$ (Milne, *CFT*, VIII, §1, p. 229). -/
def IsLocalPow (n : ℕ) (a : K) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ x : v.adicCompletion K, x ^ n = algebraMap K (v.adicCompletion K) a

end NumberFieldKB.MilneCFT.Ch8
