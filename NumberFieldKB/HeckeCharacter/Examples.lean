import NumberFieldKB.HeckeCharacter.InfinityType

/-!
# Example: the norm character $\|\cdot\|^s$

$F$ is a number field and $s\in\mathbb C$. The norm character $\|\cdot\|^s$ (`HeckeCharacter.normPow F s`) has

* local components $u\mapsto\|u\|_v^s$ at every finite place (`finiteComponent_normPow`), so it is unramified
  everywhere (`isUnramifiedAt_normPow`) and its conductor is $(1)$ (`conductor_normPow`);
* shift $\operatorname{Re}s$ (`shift_normPow`, in `Basic.lean`);
* infinity type: exponent $s$ and sign $+1$ at every real place (`realExponent_normPow`, `realSign_normPow`),
  exponent $2s$ and frequency $0$ at every complex place (`complexExponent_normPow`, `complexFrequency_normPow`).

A Dirichlet character over $\mathbb Q$ as a Hecke character is **not** done here: Mathlib v4.35.0 has no
description of $C_{\mathbb Q} = \mathbb R_{>0}\times\hat{\mathbb Z}^\times$, so the construction is not short (Tau Ceti's
`HeckeCharacter/Dirichlet.lean` goes through its ray class groups and moduli).
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace

namespace NumberFieldKB

noncomputable section

variable {F : Type} [Field F] [NumberField F]

open Ideles

namespace HeckeCharacter

/-- At a finite place the norm character is $u\mapsto\|u\|_v^s$. -/
theorem finiteComponent_normPow (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    ((normPow F s).finiteComponent v u : ℂ) = ((‖(u : v.adicCompletion F)‖ : ℝ) : ℂ) ^ s := by
  rw [finiteComponent_apply, normPow_apply, ideleClassNorm_mk, coe_ideleGroupNorm_ofAdicCompletion]

/-- **The norm character is unramified everywhere.** -/
theorem isUnramifiedAt_normPow (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) : (normPow F s).IsUnramifiedAt v := by
  intro u hu
  apply Units.ext
  rw [finiteComponent_normPow, Valued.toNormedField.norm_eq_one_iff.mpr hu, Complex.ofReal_one, Complex.one_cpow,
    Units.val_one]

/-- **The conductor of the norm character is $(1)$.** -/
theorem conductor_normPow (s : ℂ) : (normPow F s).conductor = ⊤ :=
  (conductor_eq_top_iff _).mpr (isUnramifiedAt_normPow s)

/-- At an infinite place the norm character is $u\mapsto(\|u\|_w^{m_w})^s$. -/
theorem infiniteComponent_normPow (s : ℂ) (w : InfinitePlace F) (u : w.Completionˣ) :
    ((normPow F s).infiniteComponent w u : ℂ) = (((‖(u : w.Completion)‖ ^ w.mult : ℝ)) : ℂ) ^ s := by
  rw [infiniteComponent_apply, normPow_apply, ideleClassNorm_mk, coe_ideleGroupNorm_ofCompletion]

/-- At a real place the norm character has exponent $s$. -/
theorem realExponent_normPow (s : ℂ) {w : InfinitePlace F} (hw : w.IsReal) :
    (normPow F s).realExponent hw = s := by
  refine realExponent_unique _ hw fun x hx => ?_
  change ((normPow F s).infiniteComponent w _ : ℂ) = _
  rw [infiniteComponent_normPow, mult, ite_eq_left_of_eq_true _ _ (eq_true hw), pow_one]
  erw [norm_completionMulEquivReal_symm hw]
  rw [Real.norm_of_nonneg hx.le]

/-- At a real place the norm character has sign $+1$. -/
theorem realSign_normPow (s : ℂ) {w : InfinitePlace F} (hw : w.IsReal) : (normPow F s).realSign hw = 1 := by
  change ((normPow F s).infiniteComponent w _ : ℂ) = 1
  rw [infiniteComponent_normPow]
  erw [norm_completionMulEquivReal_symm hw]
  simp

/-- At a complex place the norm character has exponent $2s$ and frequency $0$ (the normalized absolute value at a
complex place is the square of the usual one). -/
theorem complexComponent_normPow (s : ℂ) {w : InfinitePlace F} (hw : w.IsComplex) :
    (normPow F s).complexExponent hw = 2 * s ∧ (normPow F s).complexFrequency hw = 0 := by
  refine complexComponent_unique _ hw fun z => ?_
  change ((normPow F s).infiniteComponent w _ : ℂ) = _
  rw [infiniteComponent_normPow, mult,
    ite_eq_right_of_eq_false _ _ (eq_false (not_isReal_iff_isComplex.mpr hw))]
  rw [zpow_zero, mul_one]
  erw [norm_completionMulEquivComplex_symm hw]
  have hn : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (pow_pos hn 2).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne'), ← Complex.ofReal_log (pow_pos hn 2).le,
    ← Complex.ofReal_log hn.le, Real.log_pow]
  push_cast
  ring_nf

theorem complexExponent_normPow (s : ℂ) {w : InfinitePlace F} (hw : w.IsComplex) :
    (normPow F s).complexExponent hw = 2 * s := (complexComponent_normPow s hw).1

theorem complexFrequency_normPow (s : ℂ) {w : InfinitePlace F} (hw : w.IsComplex) :
    (normPow F s).complexFrequency hw = 0 := (complexComponent_normPow s hw).2

end HeckeCharacter

end

end NumberFieldKB
