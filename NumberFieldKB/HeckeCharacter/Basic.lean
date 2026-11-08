import NumberFieldKB.Ideles.Compact
import NumberFieldKB.HeckeCharacter.Units

/-!
# Hecke characters

$F$ is a number field, $C_F = \mathbb A_F^\times/F^\times$ = Mathlib's `IdeleClassGroup (𝓞 F) F`.

* **`HeckeCharacter F`**: a Hecke (quasi-)character, a continuous homomorphism $C_F\to\mathbb C^\times$
  (Tate's "quasi-character"; unitarity is not assumed).
* **`HeckeCharacter.IsUnitary`**: the values have absolute value $1$ (Tate's "character").
* **`ideleClassNorm F`**: the idele norm $\|\cdot\|$ on $C_F$ (Mathlib's norm, through `ideleGroupNorm`),
  continuous (`continuous_ideleClassNorm`) and onto $\mathbb R_{>0}$ (`ideleClassNorm_diagIdele`).
* **`HeckeCharacter.normPow F s`**: the norm character $c\mapsto\|c\|^s$, $s\in\mathbb C$.
* **`HeckeCharacter.shift`**: the unique real $\sigma$ with $|\chi(c)| = \|c\|^\sigma$
  (`norm_apply_eq_rpow_shift`, `shift_eq_of_norm_apply_eq_rpow`).
* **`HeckeCharacter.unitaryPart`**: $\chi_0 = \chi\cdot\|\cdot\|^{-\sigma}$; the decomposition $\chi = \chi_0\,\|\cdot\|^\sigma$
  with $\chi_0$ unitary and $\sigma$ real, and its uniqueness (`existsUnique_isUnitary_mul_normPow`).

The proof that $|\chi|$ is a power of the norm: $|\chi|$ is trivial on the compact group $C_F^1$
(`IdeleClassGroup.compactSpace_normOne` and `ContinuousMonoidHom.norm_eq_one_of_compactSpace`), and along the section
$t\mapsto(e^t,\dots,e^t;1,1,\dots)$ of the norm, $\log|\chi|$ is a continuous additive function of $t$, hence linear.

Adapted from Tau Ceti (`TauCeti/NumberTheory/NumberField/Global/HeckeCharacter/Basic.lean` and `Shift.lean`, commit
a57def64, Copyright (c) 2026 The Tau Ceti contributors, released under the Apache 2.0 license): the definition
`HeckeCharacter`, and the statements and proof outline of `normPow`, `shift`, `unitaryPart` and their lemmas. Rewritten
for Mathlib v4.35.0 on the norm `ideleGroupNorm` and compactness (`IdeleClassGroup.compactSpace_normOne`).
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding Module
open scoped NNReal

namespace NumberFieldKB

noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- **A Hecke (quasi-)character** of the number field $F$: a continuous homomorphism from the idele class group
$C_F = \mathbb A_F^\times/F^\times$ to $\mathbb C^\times$ (Tate's "quasi-character"; no unitarity assumed). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §3.1 [unverified locator] (quasi-characters of J/k^×)"]
abbrev HeckeCharacter := ContinuousMonoidHom (IdeleClassGroup (𝓞 F) F) ℂˣ

namespace Ideles

/-! ### The norm on the idele class group -/

/-- **The idele norm on $C_F$**: `ideleGroupNorm` (Mathlib's norm) is trivial on $F^\times$ by the product
formula, so it descends to the idele class group. -/
def ideleClassNorm : IdeleClassGroup (𝓞 F) F →* ℝ≥0 :=
  QuotientGroup.lift _ (ideleGroupNorm F) fun _ hx => ideleGroupNorm_eq_one_of_mem_principalSubgroup hx

variable {F}

@[simp] theorem ideleClassNorm_mk (x : IdeleGroup (𝓞 F) F) :
    ideleClassNorm F (x : IdeleClassGroup (𝓞 F) F) = ideleGroupNorm F x := rfl

theorem continuous_ideleClassNorm : Continuous (ideleClassNorm F) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr continuous_ideleGroupNorm

theorem ideleClassNorm_ne_zero (c : IdeleClassGroup (𝓞 F) F) : ideleClassNorm F c ≠ 0 :=
  ((Group.isUnit c).map (ideleClassNorm F)).ne_zero

theorem coe_ideleClassNorm_pos (c : IdeleClassGroup (𝓞 F) F) : 0 < (ideleClassNorm F c : ℝ) :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (ideleClassNorm_ne_zero c))

/-- $C_F^1$ is the kernel of the norm on $C_F$. -/
theorem IdeleClassGroup.mem_normOne_iff (c : IdeleClassGroup (𝓞 F) F) :
    c ∈ IdeleClassGroup.normOne F ↔ ideleClassNorm F c = 1 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  rw [IdeleClassGroup.mem_normOne_mk, ideleClassNorm_mk, ideleGroupOne, MonoidHom.mem_ker]

/-! ### A section of the norm: the diagonal idele $(e^t,\dots,e^t;1,1,\dots)$ -/

variable (F) in
/-- The adele with component $e^t$ at every infinite place and $1$ at every finite place. -/
def diagIdeleVal (t : ℝ) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ (mixedSpace F) (Real.exp t)), 1)

theorem diagIdeleVal_add (t u : ℝ) : diagIdeleVal F (t + u) = diagIdeleVal F t * diagIdeleVal F u := by
  refine Prod.ext ?_ ?_
  · change _ = (diagIdeleVal F t).1 * (diagIdeleVal F u).1
    simp only [diagIdeleVal, Real.exp_add, map_mul]
  · change (1 : FiniteAdeleRing (𝓞 F) F) = 1 * 1
    rw [mul_one]

theorem diagIdeleVal_zero : diagIdeleVal F 0 = 1 := by
  refine Prod.ext ?_ ?_
  · change _ = (1 : InfiniteAdeleRing F)
    simp only [diagIdeleVal, Real.exp_zero, map_one]
  · rfl

variable (F) in
/-- **The diagonal idele** $e(t) = (e^t,\dots,e^t;1,1,\dots)$, of norm $e^{nt}$ with $n = [F:\mathbb Q]$
(`ideleGroupNorm_diagIdele`); $t\mapsto e(t)$ is a continuous section of the norm up to rescaling. -/
def diagIdele (t : ℝ) : IdeleGroup (𝓞 F) F where
  val := diagIdeleVal F t
  inv := diagIdeleVal F (-t)
  val_inv := by rw [← diagIdeleVal_add, add_neg_cancel, diagIdeleVal_zero]
  inv_val := by rw [← diagIdeleVal_add, neg_add_cancel, diagIdeleVal_zero]

theorem diagIdele_add (t u : ℝ) : diagIdele F (t + u) = diagIdele F t * diagIdele F u :=
  Units.ext (diagIdeleVal_add t u)

theorem diagIdele_zero : diagIdele F 0 = 1 := Units.ext diagIdeleVal_zero

theorem continuous_diagIdeleVal : Continuous (diagIdeleVal F) :=
  ((continuous_ringEquiv_mixedSpace_symm F).comp
    ((continuous_algebraMap ℝ (mixedSpace F)).comp Real.continuous_exp)).prodMk continuous_const

theorem continuous_diagIdele : Continuous (diagIdele F) :=
  Units.continuous_iff.mpr ⟨continuous_diagIdeleVal, continuous_diagIdeleVal.comp continuous_neg⟩

/-- The norm of the diagonal idele: $\|e(t)\| = e^{nt}$, $n = [F:\mathbb Q]$. -/
theorem coe_ideleGroupNorm_diagIdele (t : ℝ) :
    (ideleGroupNorm F (diagIdele F t) : ℝ) = Real.exp (finrank ℚ F * t) := by
  rw [coe_ideleGroupNorm, AdeleRing.norm_apply_of_isUnit (diagIdele F t).isUnit]
  have hfin : ∏ᶠ v, ‖((diagIdele F t : AdeleRing (𝓞 F) F)).2 v‖ = 1 := by
    have h1 : ∀ v, ‖((diagIdele F t : AdeleRing (𝓞 F) F)).2 v‖ = 1 := fun v => by
      change ‖(1 : FiniteAdeleRing (𝓞 F) F) v‖ = 1
      exact norm_one
    simp only [h1, finprod_one]
  rw [hfin, mul_one, ← NumberField.InfiniteAdeleRing.norm_def, InfiniteAdeleRing.norm_eq_norm_ringEquiv_mixedSpace]
  change mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ (mixedSpace F) (Real.exp t)))) = _
  rw [RingEquiv.apply_symm_apply, Algebra.algebraMap_eq_smul_one, mixedEmbedding.norm_smul, map_one, mul_one,
    abs_of_pos (Real.exp_pos t), ← Real.exp_nat_mul]

/-- **The norm on $C_F$ is onto $\mathbb R_{>0}$**: $\|e(\log r/n)\| = r$. -/
theorem ideleClassNorm_diagIdele {r : ℝ} (hr : 0 < r) :
    (ideleClassNorm F (diagIdele F (Real.log r / finrank ℚ F) : IdeleClassGroup (𝓞 F) F) : ℝ) = r := by
  have hn : (finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  rw [ideleClassNorm_mk, coe_ideleGroupNorm_diagIdele, mul_div_cancel₀ _ hn, Real.exp_log hr]

end Ideles

open Ideles

namespace HeckeCharacter

variable {F}

/-- A Hecke character is **unitary** if its values have absolute value $1$ (Tate's "character"). -/
def IsUnitary (χ : HeckeCharacter F) : Prop := ∀ c, ‖(χ c : ℂ)‖ = 1

/-! ### The norm characters $\|\cdot\|^s$ -/

variable (F) in
/-- **The norm character** $c\mapsto\|c\|^s$ of $C_F$, for $s\in\mathbb C$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §3.1 [unverified locator] (the quasi-characters |·|^s)"]
def normPow (s : ℂ) : HeckeCharacter F where
  toFun c := Units.mk0 (((ideleClassNorm F c : ℝ) : ℂ) ^ s) (by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (coe_ideleClassNorm_pos c).ne')]
    exact Complex.exp_ne_zero _)
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by
    simp only [map_mul, NNReal.coe_mul, Complex.ofReal_mul, Units.val_mk0, Units.val_mul]
    exact Complex.mul_cpow_ofReal_nonneg (coe_ideleClassNorm_pos a).le (coe_ideleClassNorm_pos b).le s)
  continuous_toFun := by
    have hval : Continuous fun c : IdeleClassGroup (𝓞 F) F => (((ideleClassNorm F c : ℝ) : ℂ) ^ s) :=
      (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp continuous_ideleClassNorm)).cpow
        continuous_const fun c => Complex.ofReal_mem_slitPlane.mpr (coe_ideleClassNorm_pos c)
    refine Units.continuous_iff.mpr ⟨hval, ?_⟩
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    exact hval.inv₀ fun c => by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (coe_ideleClassNorm_pos c).ne')]
      exact Complex.exp_ne_zero _

@[simp] theorem normPow_apply (s : ℂ) (c : IdeleClassGroup (𝓞 F) F) :
    ((normPow F s c : ℂˣ) : ℂ) = ((ideleClassNorm F c : ℝ) : ℂ) ^ s := rfl

theorem norm_normPow_apply (s : ℂ) (c : IdeleClassGroup (𝓞 F) F) :
    ‖((normPow F s c : ℂˣ) : ℂ)‖ = (ideleClassNorm F c : ℝ) ^ s.re := by
  rw [normPow_apply, Complex.norm_cpow_eq_rpow_re_of_pos (coe_ideleClassNorm_pos c)]

@[simp] theorem normPow_zero : normPow F 0 = 1 := by
  ext c
  simp

theorem normPow_add (s t : ℂ) : normPow F (s + t) = normPow F s * normPow F t := by
  ext c
  simp only [normPow_apply, ContinuousMonoidHom.mul_apply, Units.val_mul]
  exact Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (coe_ideleClassNorm_pos c).ne')

theorem normPow_neg (s : ℂ) : normPow F (-s) = (normPow F s)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← normPow_add, neg_add_cancel, normPow_zero])

/-- $\|\cdot\|^s$ is unitary exactly when $s$ is purely imaginary. -/
theorem isUnitary_normPow_iff (s : ℂ) : (normPow F s).IsUnitary ↔ s.re = 0 := by
  constructor
  · intro h
    have h2 := h (diagIdele F (Real.log 2 / finrank ℚ F) : IdeleClassGroup (𝓞 F) F)
    rw [norm_normPow_apply, ideleClassNorm_diagIdele two_pos, Real.rpow_def_of_pos two_pos,
      Real.exp_eq_one_iff, mul_eq_zero] at h2
    exact h2.resolve_left (Real.log_pos one_lt_two).ne'
  · intro h c
    rw [norm_normPow_apply, h, Real.rpow_zero]

/-! ### The shift: $|\chi| = \|\cdot\|^\sigma$ -/

/-- The absolute value of a Hecke character is a real power of the norm. -/
theorem exists_norm_apply_eq_rpow (χ : HeckeCharacter F) :
    ∃ σ : ℝ, ∀ c, ‖(χ c : ℂ)‖ = (ideleClassNorm F c : ℝ) ^ σ := by
  -- `|χ|` is trivial on the compact group `C_F¹`.
  have hone (c : IdeleClassGroup (𝓞 F) F) (hc : c ∈ IdeleClassGroup.normOne F) : ‖(χ c : ℂ)‖ = 1 :=
    ContinuousMonoidHom.norm_eq_one_of_compactSpace
      ⟨(χ : IdeleClassGroup (𝓞 F) F →* ℂˣ).comp (IdeleClassGroup.normOne F).subtype,
        χ.continuous.comp continuous_subtype_val⟩ ⟨c, hc⟩
  let e : ℝ → IdeleClassGroup (𝓞 F) F := fun t => (diagIdele F t : IdeleClassGroup (𝓞 F) F)
  have hχe (t : ℝ) : ‖(χ (e t) : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (χ (e t)).ne_zero
  -- Along `e`, `log |χ|` is a continuous additive map `ℝ → ℝ`, hence linear.
  let ψ : ℝ →+ ℝ :=
    { toFun t := Real.log ‖(χ (e t) : ℂ)‖
      map_zero' := by simp [e, diagIdele_zero]
      map_add' t u := by
        simp only [e, diagIdele_add, QuotientGroup.mk_mul, map_mul, Units.val_mul, norm_mul]
        exact Real.log_mul (hχe t) (hχe u) }
  have hψ : Continuous ψ :=
    (continuous_norm.comp (Units.continuous_val.comp
      (χ.continuous.comp (QuotientGroup.continuous_mk.comp continuous_diagIdele)))).log hχe
  have hψ_apply (t : ℝ) : ψ t = Real.log ‖(χ (e t) : ℂ)‖ := rfl
  have hlin (t : ℝ) : ψ t = t * ψ 1 := by simpa using map_real_smul ψ hψ t 1
  have hn : (0 : ℝ) < finrank ℚ F := Nat.cast_pos.mpr finrank_pos
  refine ⟨ψ 1 / finrank ℚ F, fun c => ?_⟩
  -- Compare `c` with the point of the section with the same norm.
  set t := Real.log (ideleClassNorm F c : ℝ) / finrank ℚ F
  have hnorm : (ideleClassNorm F (e t) : ℝ) = ideleClassNorm F c :=
    ideleClassNorm_diagIdele (coe_ideleClassNorm_pos c)
  have hmem : c * (e t)⁻¹ ∈ IdeleClassGroup.normOne F := by
    rw [IdeleClassGroup.mem_normOne_iff, map_mul, map_inv, mul_inv_eq_one₀ (ideleClassNorm_ne_zero _)]
    exact NNReal.eq hnorm.symm
  have hc : ‖(χ c : ℂ)‖ = ‖(χ (e t) : ℂ)‖ := by
    have := hone _ hmem
    rwa [map_mul, map_inv, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv,
      mul_inv_eq_one₀ (hχe t)] at this
  rw [hc, ← Real.exp_log (norm_pos_iff.mpr (χ (e t)).ne_zero), Real.rpow_def_of_pos (coe_ideleClassNorm_pos c),
    ← hψ_apply, hlin t]
  congr 1
  simp only [t]
  field_simp

/-- **The shift of a Hecke character**: the unique real number $\sigma$ with $|\chi(c)| = \|c\|^\sigma$ for every
idele class $c$ (`norm_apply_eq_rpow_shift`, `shift_eq_of_norm_apply_eq_rpow`). -/
def shift (χ : HeckeCharacter F) : ℝ := (exists_norm_apply_eq_rpow χ).choose

/-- **The absolute value of a Hecke character is a power of the norm**: $|\chi(c)| = \|c\|^\sigma$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §3.1 [unverified locator] (|c| = ‖·‖^σ, σ real)"]
theorem norm_apply_eq_rpow_shift (χ : HeckeCharacter F) (c : IdeleClassGroup (𝓞 F) F) :
    ‖(χ c : ℂ)‖ = (ideleClassNorm F c : ℝ) ^ χ.shift :=
  (exists_norm_apply_eq_rpow χ).choose_spec c

/-- **Uniqueness of the shift.** -/
theorem shift_eq_of_norm_apply_eq_rpow {χ : HeckeCharacter F} {σ : ℝ}
    (h : ∀ c, ‖(χ c : ℂ)‖ = (ideleClassNorm F c : ℝ) ^ σ) : χ.shift = σ := by
  set c : IdeleClassGroup (𝓞 F) F := (diagIdele F (Real.log 2 / finrank ℚ F) : IdeleClassGroup (𝓞 F) F)
  have h2 : (ideleClassNorm F c : ℝ) = 2 := ideleClassNorm_diagIdele two_pos
  have := (norm_apply_eq_rpow_shift χ c).symm.trans (h c)
  rwa [h2, Real.rpow_right_inj two_pos (by norm_num)] at this

@[simp] theorem shift_normPow (s : ℂ) : (normPow F s).shift = s.re :=
  shift_eq_of_norm_apply_eq_rpow (norm_normPow_apply s)

@[simp] theorem shift_one : (1 : HeckeCharacter F).shift = 0 :=
  shift_eq_of_norm_apply_eq_rpow fun c => by simp

@[simp] theorem shift_mul (χ ψ : HeckeCharacter F) : (χ * ψ).shift = χ.shift + ψ.shift :=
  shift_eq_of_norm_apply_eq_rpow fun c => by
    rw [ContinuousMonoidHom.mul_apply, Units.val_mul, norm_mul, norm_apply_eq_rpow_shift,
      norm_apply_eq_rpow_shift, ← Real.rpow_add (coe_ideleClassNorm_pos c)]

@[simp] theorem shift_inv (χ : HeckeCharacter F) : χ⁻¹.shift = -χ.shift := by
  rw [eq_neg_iff_add_eq_zero, ← shift_mul, inv_mul_cancel, shift_one]

/-- **The shift vanishes exactly for unitary characters.** -/
theorem shift_eq_zero_iff (χ : HeckeCharacter F) : χ.shift = 0 ↔ χ.IsUnitary := by
  refine ⟨fun h c => by rw [norm_apply_eq_rpow_shift, h, Real.rpow_zero], fun h => ?_⟩
  exact shift_eq_of_norm_apply_eq_rpow fun c => by rw [h c, Real.rpow_zero]

/-! ### The unitary part and the decomposition $\chi = \chi_0\,\|\cdot\|^\sigma$ -/

/-- **The unitary part** $\chi_0 = \chi\cdot\|\cdot\|^{-\sigma}$ of a Hecke character, $\sigma$ its shift. -/
def unitaryPart (χ : HeckeCharacter F) : HeckeCharacter F := χ * normPow F (-χ.shift)

theorem unitaryPart_apply (χ : HeckeCharacter F) (c : IdeleClassGroup (𝓞 F) F) :
    ((χ.unitaryPart c : ℂˣ) : ℂ) = (χ c : ℂ) * ((ideleClassNorm F c : ℝ) : ℂ) ^ (-(χ.shift : ℂ)) := by
  rw [unitaryPart, ContinuousMonoidHom.mul_apply, Units.val_mul, normPow_apply]

@[simp] theorem shift_unitaryPart (χ : HeckeCharacter F) : χ.unitaryPart.shift = 0 := by
  simp [unitaryPart]

theorem isUnitary_unitaryPart (χ : HeckeCharacter F) : χ.unitaryPart.IsUnitary :=
  (shift_eq_zero_iff _).mp (shift_unitaryPart χ)

/-- **The decomposition** $\chi = \chi_0\,\|\cdot\|^\sigma$, with $\chi_0$ unitary and $\sigma$ real. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §3.1 [unverified locator] (c = c₀|·|^σ, c₀ a character)"]
theorem unitaryPart_mul_normPow_shift (χ : HeckeCharacter F) : χ.unitaryPart * normPow F χ.shift = χ := by
  rw [unitaryPart, mul_assoc χ, ← normPow_add, neg_add_cancel, normPow_zero, mul_one χ]

/-- **Uniqueness of the decomposition**: the unitary part of $\psi\,\|\cdot\|^\sigma$, for $\psi$ unitary and
$\sigma$ real, is $\psi$. -/
theorem unitaryPart_mul_normPow {ψ : HeckeCharacter F} (hψ : ψ.IsUnitary) (σ : ℝ) :
    (ψ * normPow F σ).unitaryPart = ψ := by
  rw [unitaryPart, shift_mul, shift_normPow, (shift_eq_zero_iff ψ).mpr hψ, zero_add, Complex.ofReal_re, mul_assoc ψ,
    ← normPow_add, add_neg_cancel, normPow_zero, mul_one ψ]

/-- **A Hecke character is uniquely a unitary one times a real power of the norm.** -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §3.1 [unverified locator] (c = c₀|·|^σ, c₀ a character)"]
theorem existsUnique_isUnitary_mul_normPow (χ : HeckeCharacter F) :
    ∃! p : HeckeCharacter F × ℝ, p.1.IsUnitary ∧ χ = p.1 * normPow F p.2 := by
  refine ⟨(χ.unitaryPart, χ.shift), ⟨isUnitary_unitaryPart χ, (unitaryPart_mul_normPow_shift χ).symm⟩, ?_⟩
  rintro ⟨ψ, σ⟩ ⟨hψ, rfl⟩
  have hσ : (ψ * normPow F σ).shift = σ := by
    rw [shift_mul, shift_normPow, (shift_eq_zero_iff ψ).mpr hψ, zero_add, Complex.ofReal_re]
  simp only [unitaryPart_mul_normPow hψ, hσ]

end HeckeCharacter

end

end NumberFieldKB
