import NumberFieldKB.HeckeCharacter.Local
import NumberFieldKB.HeckeCharacter.ArchimedeanCharacters

/-!
# The infinity type of a Hecke character

$F$ is a number field and $\chi$ a Hecke character. At an infinite place $w$, the component
$\chi_w = \chi|_{F_w^\times}$ (`HeckeCharacter.infiniteComponent`) is transported to $\mathbb R^\times$ or
$\mathbb C^\times$ along Mathlib's identification $F_w\cong\mathbb R$ (real $w$) or $F_w\cong\mathbb C$ (complex $w$,
through the embedding `w.embedding` that Mathlib chooses; the other choice replaces $k_w$ by $-k_w$). Then:

* at a real place, $\chi_w(x) = |x|^{s_w}\,\epsilon_w^{[x<0]}$ with $s_w\in\mathbb C$ unique (`realExponent`) and
  $\epsilon_w = \chi_w(-1)\in\{\pm1\}$ (`realSign`): `realComponent_apply`, `realExponent_unique`, `realSign_eq`;
* at a complex place, $\chi_w(z) = |z|^{s_w}\,(z/|z|)^{k_w}$ with $s_w\in\mathbb C$, $k_w\in\mathbb Z$ unique
  (`complexExponent`, `complexFrequency`): `complexComponent_apply`, `complexComponent_unique`;
* the real parts are fixed by the shift $\sigma$ of $\chi$: $\operatorname{Re}s_w = \sigma$ at a real place and
  $2\sigma$ at a complex place (`re_realExponent`, `re_complexExponent`), because $|\chi| = \|\cdot\|^\sigma$ and the
  normalized absolute value at a complex place is the square of the usual one.

These parameters are the **infinity type** of $\chi$. The classification of the characters of $\mathbb R^\times$ and
$\mathbb C^\times$ is in `ArchimedeanCharacters.lean`.

Adapted from Tau Ceti (`TauCeti/NumberTheory/NumberField/Global/HeckeCharacter/InfinityType.lean`, commit a57def64,
Copyright (c) 2026 The Tau Ceti contributors, released under the Apache 2.0 license): the definitions
`realComponent`, `complexComponent` and the statements `re_realExponent_infinityType`,
`re_complexExponent_infinityType`. We do not port Tau Ceti's `ContinuousInfinityType` structure; the parameters are
separate functions of the place.
-/

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

namespace NumberFieldKB

noncomputable section

variable {F : Type} [Field F] [NumberField F]

namespace Ideles

/-- Mathlib's isomorphism $F_w\cong\mathbb R$ at a real place, as an isomorphism of topological groups. -/
def completionMulEquivReal {w : InfinitePlace F} (hw : w.IsReal) : w.Completion ≃ₜ* ℝ :=
  let e : w.Completion ≃ᵢ ℝ :=
    { toEquiv := (ringEquivRealOfIsReal hw).toEquiv
      isometry_toFun := by
        convert isometry_extensionEmbeddingOfIsReal hw using 1
        funext x
        exact ringEquivRealOfIsReal_apply hw x }
  { toMulEquiv := (ringEquivRealOfIsReal hw).toMulEquiv
    continuous_toFun := e.continuous
    continuous_invFun := e.symm.continuous }

/-- Mathlib's isomorphism $F_w\cong\mathbb C$ at a complex place (extending `w.embedding`), as an isomorphism of
topological groups. -/
def completionMulEquivComplex {w : InfinitePlace F} (hw : w.IsComplex) : w.Completion ≃ₜ* ℂ :=
  let e : w.Completion ≃ᵢ ℂ :=
    { toEquiv := (ringEquivComplexOfIsComplex hw).toEquiv
      isometry_toFun := by
        convert isometry_extensionEmbedding w using 1
        funext x
        exact ringEquivComplexOfIsComplex_apply hw x }
  { toMulEquiv := (ringEquivComplexOfIsComplex hw).toMulEquiv
    continuous_toFun := e.continuous
    continuous_invFun := e.symm.continuous }

omit [NumberField F] in
theorem norm_completionMulEquivReal_symm {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ‖(completionMulEquivReal hw).symm x‖ = ‖x‖ := by
  conv_rhs => rw [← (completionMulEquivReal hw).apply_symm_apply x]
  change _ = ‖extensionEmbeddingOfIsReal hw _‖
  exact ((isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _).symm

omit [NumberField F] in
theorem norm_completionMulEquivComplex_symm {w : InfinitePlace F} (hw : w.IsComplex) (z : ℂ) :
    ‖(completionMulEquivComplex hw).symm z‖ = ‖z‖ := by
  conv_rhs => rw [← (completionMulEquivComplex hw).apply_symm_apply z]
  change _ = ‖extensionEmbedding w _‖
  exact ((isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm

end Ideles

open Ideles HeckeCharacters

namespace HeckeCharacter

/-! ### Real places -/

/-- The component of $\chi$ at a real place, as a character of $\mathbb R^\times$. -/
def realComponent (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsReal) : ℝˣ →ₜ* ℂˣ :=
  (χ.infiniteComponent w).comp
    { toMonoidHom := (Units.mapContinuousMulEquiv (completionMulEquivReal hw)).symm.toMulEquiv.toMonoidHom
      continuous_toFun := (Units.mapContinuousMulEquiv (completionMulEquivReal hw)).symm.continuous }

/-- **The exponent at a real place**: $s_w$ with $\chi_w(x) = |x|^{s_w}\epsilon_w^{[x<0]}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.3 [unverified locator] (quasi-characters of R^×: |x|^s or sgn(x)|x|^s)"]
def realExponent (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsReal) : ℂ :=
  (exists_realUnits_character (χ.realComponent hw)).choose

/-- **The sign at a real place**: $\epsilon_w = \chi_w(-1)$. -/
def realSign (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsReal) : ℂ := χ.realComponent hw (-1)

/-- **The component at a real place**: $\chi_w(x) = |x|^{s_w}\,\epsilon_w^{[x<0]}$. -/
theorem realComponent_apply (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsReal) (x : ℝˣ) :
    (χ.realComponent hw x : ℂ) =
      ((|(x : ℝ)| : ℝ) : ℂ) ^ χ.realExponent hw * (if (x : ℝ) < 0 then χ.realSign hw else 1) :=
  (exists_realUnits_character (χ.realComponent hw)).choose_spec x

theorem realSign_eq (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsReal) :
    χ.realSign hw = 1 ∨ χ.realSign hw = -1 :=
  realUnits_character_neg_one _

/-- **Uniqueness of the real exponent.** -/
theorem realExponent_unique (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsReal) {s : ℂ}
    (h : ∀ x : ℝˣ, 0 < (x : ℝ) → (χ.realComponent hw x : ℂ) = ((x : ℝ) : ℂ) ^ s) : χ.realExponent hw = s := by
  refine eq_of_forall_exp_mul_eq fun t => ?_
  have hx : 0 < ((Units.mk0 (Real.exp t) (Real.exp_pos t).ne' : ℝˣ) : ℝ) := Real.exp_pos t
  have h1 := h _ hx
  rw [realComponent_apply, abs_of_pos hx] at h1
  simp only [Units.val_mk0] at h1
  simp only [not_lt.mpr (Real.exp_pos t).le, ↓reduceIte, mul_one] at h1
  rwa [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
    ← Complex.ofReal_log (Real.exp_pos t).le,
    Real.log_exp, mul_comm _ (χ.realExponent hw), mul_comm _ s] at h1

/-- **The real part of the exponent at a real place is the shift** $\sigma$. -/
theorem re_realExponent (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsReal) :
    (χ.realExponent hw).re = χ.shift := by
  have h2 : 0 < ((Units.mk0 2 two_ne_zero : ℝˣ) : ℝ) := two_pos
  have h := χ.realComponent_apply hw (Units.mk0 2 two_ne_zero)
  have hn := χ.norm_infiniteComponent_apply w
    ((Units.mapContinuousMulEquiv (completionMulEquivReal hw)).symm (Units.mk0 2 two_ne_zero))
  change ‖(χ.realComponent hw (Units.mk0 2 two_ne_zero) : ℂ)‖ = _ at hn
  rw [h, abs_of_pos h2] at hn
  simp only [not_lt.mpr h2.le, ↓reduceIte, mul_one] at hn
  rw [Complex.norm_cpow_eq_rpow_re_of_pos h2] at hn
  simp only [Units.symm_mapContinuousMulEquiv, Units.mapContinuousMulEquiv_apply, Units.coe_map,
    MonoidHom.coe_ofClass, Units.val_mk0] at hn
  erw [norm_completionMulEquivReal_symm hw] at hn
  rw [mult, ite_eq_left_of_eq_true _ _ (eq_true hw), pow_one, Real.norm_two] at hn
  exact (Real.rpow_right_inj two_pos (by norm_num)).mp hn

/-! ### Complex places -/

/-- The component of $\chi$ at a complex place, as a character of $\mathbb C^\times$. -/
def complexComponent (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsComplex) : ℂˣ →ₜ* ℂˣ :=
  (χ.infiniteComponent w).comp
    { toMonoidHom := (Units.mapContinuousMulEquiv (completionMulEquivComplex hw)).symm.toMulEquiv.toMonoidHom
      continuous_toFun := (Units.mapContinuousMulEquiv (completionMulEquivComplex hw)).symm.continuous }

/-- **The exponent at a complex place**: $s_w$ with $\chi_w(z) = |z|^{s_w}(z/|z|)^{k_w}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.3 [unverified locator] (quasi-characters of C^×: |z|^s (z/|z|)^n)"]
def complexExponent (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsComplex) : ℂ :=
  (exists_complexUnits_character (χ.complexComponent hw)).choose

/-- **The frequency at a complex place**: $k_w\in\mathbb Z$ with $\chi_w(z) = |z|^{s_w}(z/|z|)^{k_w}$. -/
def complexFrequency (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsComplex) : ℤ :=
  (exists_complexUnits_character (χ.complexComponent hw)).choose_spec.choose

/-- **The component at a complex place**: $\chi_w(z) = |z|^{s_w}\,(z/|z|)^{k_w}$. -/
theorem complexComponent_apply (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsComplex) (z : ℂˣ) :
    (χ.complexComponent hw z : ℂ) =
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ χ.complexExponent hw * ((z : ℂ) / ‖(z : ℂ)‖) ^ χ.complexFrequency hw :=
  (exists_complexUnits_character (χ.complexComponent hw)).choose_spec.choose_spec z

/-- **Uniqueness of the complex parameters.** -/
theorem complexComponent_unique (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsComplex) {s : ℂ} {k : ℤ}
    (h : ∀ z : ℂˣ, (χ.complexComponent hw z : ℂ) = ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ s * ((z : ℂ) / ‖(z : ℂ)‖) ^ k) :
    χ.complexExponent hw = s ∧ χ.complexFrequency hw = k :=
  complexUnits_character_unique fun z => (χ.complexComponent_apply hw z).symm.trans (h z)

/-- **The real part of the exponent at a complex place is twice the shift.** -/
theorem re_complexExponent (χ : HeckeCharacter F) {w : InfinitePlace F} (hw : w.IsComplex) :
    (χ.complexExponent hw).re = 2 * χ.shift := by
  have h2 : (0 : ℝ) < 2 := two_pos
  have h := χ.complexComponent_apply hw (Units.mk0 2 two_ne_zero)
  have hn := χ.norm_infiniteComponent_apply w
    ((Units.mapContinuousMulEquiv (completionMulEquivComplex hw)).symm (Units.mk0 2 two_ne_zero))
  change ‖(χ.complexComponent hw (Units.mk0 2 two_ne_zero) : ℂ)‖ = _ at hn
  simp only [Units.val_mk0, Complex.norm_two, Complex.ofReal_ofNat, div_self (two_ne_zero (α := ℂ)), one_zpow,
    mul_one] at h
  have e2 : ‖(2 : ℂ) ^ χ.complexExponent hw‖ = 2 ^ (χ.complexExponent hw).re := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos h2 (χ.complexExponent hw)
  rw [h, e2] at hn
  simp only [Units.symm_mapContinuousMulEquiv, Units.mapContinuousMulEquiv_apply, Units.coe_map,
    MonoidHom.coe_ofClass, Units.val_mk0] at hn
  erw [norm_completionMulEquivComplex_symm hw] at hn
  rw [mult, ite_eq_right_of_eq_false _ _ (eq_false (not_isReal_iff_isComplex.mpr hw)), Complex.norm_two,
    ← Real.rpow_natCast, ← Real.rpow_mul h2.le] at hn
  rw [(Real.rpow_right_inj h2 (by norm_num)).mp hn]
  norm_num

end HeckeCharacter

end

end NumberFieldKB
