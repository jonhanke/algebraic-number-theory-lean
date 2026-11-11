import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch8ProductFormula
import NumberFieldKB.MilneANT.Ch8Aside89Packing
import NumberFieldKB.MilneANT.Ch8Aside89Char0
import NumberFieldKB.MilneANT.Ch8Aside89CharP
import NumberFieldKB.MilneANT.Ch8Aside89NF
import NumberFieldKB.MilneANT.Ch8Aside89FF

/-!
# Milne, *Algebraic Number Theory*, Aside 8.9 (Artin–Whaples), proved

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Aside 8.9, p. 138; bib key `milne2020ant`.
E. Artin and G. Whaples, Bull. Amer. Math. Soc. 51 (1945); E. Artin, *Algebraic Numbers and Algebraic Functions*,
Ch. 12.

* **Globality.** The locally compact completion gives a packing bound (`packingBound`, `Ch8Aside89Packing.lean`); with
  the product formula (`one_le_prod`) Artin's counting argument bounds the dimension over `ℚ` in characteristic `0`
  (`finiteDimensional_rat`, `Ch8Aside89Char0.lean`) and over `𝔽_p(t)` in characteristic `p`
  (`exists_ratFunc_finiteDimensional`, `Ch8Aside89CharP.lean`).
* **Completeness.** Number fields: units (Dirichlet) force the archimedean exponents to be proportional to the
  multiplicities, and a generator of `𝔭^h` forces every finite place into `V`
  (`exists_mem_isEquiv_of_productFormula`, `Ch8Aside89NF.lean`). Function fields: every nontrivial absolute value
  comes from a place (Stichtenoth 1.1.6, ported from Tau Ceti), and the finiteness of the degree-zero class group
  gives a function with divisor supported on two given places (`exists_mem_isEquiv_of_productFormula_FF`,
  `Ch8Aside89FF.lean`).
-/

namespace NumberFieldKB.MilneANT

open Aside89 in
/-- **Aside 8.9** (Artin–Whaples), proved. -/
@[kb "milne2020ant" "v3.08, Aside 8.9, p. 138"]
theorem aside8_9 : Aside8_9 where
  global := by
    intro K _ V hnt hineq hprod hlc
    obtain ⟨v₀, hv₀, hlc₀⟩ := hlc
    have hV : AWAxioms V := ⟨hnt, hineq, hprod⟩
    have hpack : PackingBound v₀ := packingBound v₀ (hnt v₀ hv₀)
    have hglob : Nonempty (NumberField K) ∨ ∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq)
        (_ : Algebra (RatFunc Fq) K), FiniteDimensional (RatFunc Fq) K := by
      obtain ⟨p, hp⟩ := CharP.exists K
      rcases CharP.char_is_prime_or_zero K p with hpp | rfl
      · have : Fact p.Prime := ⟨hpp⟩
        obtain ⟨_, hfd⟩ := exists_ratFunc_finiteDimensional p hV hv₀ hpack
        exact Or.inr ⟨ZMod p, inferInstance, inferInstance, _, hfd⟩
      · have : CharZero K := CharP.charP_to_charZero K
        have := finiteDimensional_rat hV hv₀ hpack
        exact Or.inl ⟨⟨⟩⟩
    refine ⟨hglob, ?_⟩
    rcases hglob with ⟨⟨hK⟩⟩ | ⟨Fq, _, _, _, _⟩
    · exact @exists_mem_isEquiv_of_productFormula K _ hK V hnt hineq hprod ⟨v₀, hv₀⟩
    · exact exists_mem_isEquiv_of_productFormula_FF (Fq := Fq) V hV ⟨v₀, hv₀⟩

end NumberFieldKB.MilneANT
