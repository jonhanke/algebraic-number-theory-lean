import NumberFieldKB.MilneCFT.Ch7.Lemma66
import NumberFieldKB.MilneCFT.Ch7.Prop68TauCeti
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Milne, *Class Field Theory*, Chapter VII §6: the lemmas made unconditional

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, Chapter VII, §6
(pp. 214–219).

* **Lemma 6.6, unconditional** (`lemma6_6`): from `lemma_6_6_of_prop_6_8` (this library) and Proposition 6.8, now
  proved from the Tau Ceti port (`prop6_8`).

Lemma 6.7 follows likewise from Lemma 6.9 and Proposition 6.10 (`lemma_6_7_of_lemma_6_9`), which remain open.
-/

open IsDedekindDomain NumberField

namespace NumberFieldKB.MilneCFT.Ch7

/-- **Lemma 6.6, unconditional** (Milne, *CFT*, Chapter VII, p. 217): in Milne's setting,
$(\mathbb I_{S\cup T} : E) = p^{2s}$. -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.6"]
theorem lemma6_6 (K : Type) [Field K] [NumberField K] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type)
    [Field M] [NumberField M] [Algebra K M] [IsGalois K M] : Lemma6_6 p S M :=
  lemma_6_6_of_prop_6_8 (prop6_8 K) p S M

end NumberFieldKB.MilneCFT.Ch7
