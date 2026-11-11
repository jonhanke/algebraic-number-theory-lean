import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch8Dedekind
import NumberFieldKB.MilneANT.Ch8Rem840cFactor
import NumberFieldKB.MilneANT.Ch8Rem840cNoIso
import NumberFieldKB.MilneANT.Ch8Rem840cDiscrM

/-!
# Milne, *Algebraic Number Theory*, Remark 8.40(c), p. 150: proved

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Remark 8.40(c), p. 150; bib key `milne2020ant`.

Corollary 8.39 fails without the Galois hypothesis. The witnesses are Perlis's pair `L = ℚ(⁸√3)`, `M = ℚ(⁸√48)`
(R. Perlis, J. Number Theory 9 (1977)), and the proof is elementary (no Galois theory):

* same degree 8 (`finrank_eq`);
* not isomorphic (`isEmpty_ringEquiv'`, `Ch8Rem840cNoIso.lean`: an isomorphism would put `√2` in `L`, which is
  impossible modulo the prime `(3, ⁸√3)` of residue field `𝔽₃`);
* the same discriminant `-2²⁴·3⁷` (`discr_L`, `Ch8Rem840cDiscr.lean`: `𝓞_L = ℤ[⁸√3]`; `discr_M`,
  `Ch8Rem840cDiscrM.lean`: an explicit triangular integral basis);
* every prime `p ∤ 6` decomposes the same way (`ncard_eq`, `Ch8Rem840cFactor.lean`): `16` is an eighth power modulo
  every odd prime, so `X⁸ - 3` and `X⁸ - 48` factor the same way modulo `p`, and Kummer–Dedekind (Mathlib
  `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`) applies.
-/

open NumberField

namespace NumberFieldKB.MilneANT

open Rem840c in
/-- **Remark 8.40(c)**, proved: `ℚ(⁸√3)` and `ℚ(⁸√48)` are non-isomorphic, of the same degree and discriminant, and
every prime not dividing the discriminant decomposes the same way in both. -/
@[kb "milne2020ant" "v3.08, Rem. 8.40(c), p. 150"]
theorem remark8_40c : Remark8_40c where
  exists_pair := by
    refine ⟨L, M, inferInstance, inferInstance, inferInstance, inferInstance, isEmpty_ringEquiv',
      (finrank_eq 3).trans (finrank_eq 48).symm, discr_L.trans discr_M.symm, ?_⟩
    intro p hp hpd e f
    rw [discr_L] at hpd
    refine ncard_eq p hp ?_ ?_ e f
    · rintro rfl
      exact hpd ⟨-(2 ^ 23 * 3 ^ 7), by norm_num⟩
    · rintro rfl
      exact hpd ⟨-(2 ^ 24 * 3 ^ 6), by norm_num⟩

end NumberFieldKB.MilneANT
