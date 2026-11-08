import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch4Thm429Inj

/-!
# Milne, *Algebraic Number Theory*, Theorem 4.29, p. 82: surjectivity

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Theorem 4.29, p. 82; bib key `milne2020ant`.

Every integral binary quadratic form `f = (a, b, c)` of discriminant `d_K` (positive definite if `d_K < 0`) is
`formOf 𝔞 b` for an oriented basis `b` of a fractional ideal `𝔞` (`exists_of_form`). For `a > 0` the ideal is
`(a, (b - δ)/2)` with basis `(a, (b - δ)/2)`; for `a < 0` (so `d_K > 0`) it is `δ` times that ideal.
-/

open NumberField Polynomial Module
open scoped nonZeroDivisors

namespace NumberFieldKB.MilneANT.Thm429

section Surj

variable {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (σ : K ≃ₐ[ℚ] K)
  (hσ : σ ≠ 1) (δ : K) (hδ : δ ^ 2 = (NumberField.discr K : K))

include hK hσ hδ in
theorem sigma_delta : σ δ = -δ := by
  obtain ⟨b, hb⟩ := exists_oriented_basis hK σ hσ δ hδ 1
  have hN1 : N (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = 1 := by
    unfold N; rw [Units.val_one, FractionalIdeal.absNorm_one]; simp
  have ho : orient σ (b 0) (b 1) = δ := by rw [hb, hN1, mul_one]
  have h2 : σ (orient σ (b 0) (b 1)) = -orient σ (b 0) (b 1) := by
    unfold orient; simp only [map_sub, map_mul, sigma_sigma hK σ hσ]; ring
  rw [ho] at h2; exact h2

variable (qa qb qc : ℤ) (hq : qb ^ 2 - 4 * qa * qc = NumberField.discr K)

/-- The root `(b - δ)/2` of `a t² ... `: `θ² = bθ - ac`. -/
def theta : K := ((qb : K) - δ) / 2

include hδ hq in
theorem theta_sq : theta δ qb * theta δ qb = qb * theta δ qb - qa * qc := by
  have hdK : δ ^ 2 = (qb : K) ^ 2 - 4 * qa * qc := by
    rw [hδ, ← hq]; push_cast; ring
  unfold theta
  linear_combination (1 / 4 : K) * hdK

include hK hσ hδ in
theorem sigma_theta : σ (theta δ qb) = ((qb : K) + δ) / 2 := by
  unfold theta
  have h2 : σ (2 : K) = 2 := map_ofNat σ 2
  rw [map_div₀, map_sub, sigma_delta hK σ hσ δ hδ, h2, map_intCast]
  ring

include hK hσ hδ in
theorem theta_add_sigma : theta δ qb + σ (theta δ qb) = qb := by
  rw [sigma_theta hK σ hσ δ hδ]; unfold theta; ring

include hK hσ hδ hq in
theorem theta_mul_sigma : theta δ qb * σ (theta δ qb) = qa * qc := by
  have hdK : δ ^ 2 = (qb : K) ^ 2 - 4 * qa * qc := by
    rw [hδ, ← hq]; push_cast; ring
  rw [sigma_theta hK σ hσ δ hδ]; unfold theta
  linear_combination (-1 / 4 : K) * hdK

include hδ hq in
theorem theta_isIntegral : IsIntegral ℤ (theta δ qb) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C qb * Polynomial.X + Polynomial.C (qa * qc), ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, Polynomial.eval₂_pow]
    simp only [algebraMap_int_eq, eq_intCast]
    push_cast
    linear_combination theta_sq δ hδ qa qb qc hq

include hK hσ hδ hq in
/-- `𝓞 K = ℤ + ℤθ`: every element of `𝓞 K` is `m + nθ`. -/
theorem mem_one_comb (y : K) (hy : y ∈ (((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) : FractionalIdeal (𝓞 K)⁰ K)) :
    ∃ m n : ℤ, y = (m : K) + (n : K) * theta δ qb := by
  obtain ⟨b, hb⟩ := exists_oriented_basis hK σ hσ δ hδ 1
  have hN1 : N (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = 1 := by
    unfold N; rw [Units.val_one, FractionalIdeal.absNorm_one]; simp
  have hθ1 : theta δ qb ∈ (((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [Units.val_one, FractionalIdeal.mem_one_iff]
    exact ⟨⟨theta δ qb, theta_isIntegral δ hδ qa qb qc hq⟩, rfl⟩
  have h1 : (1 : K) ∈ (((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [Units.val_one, FractionalIdeal.mem_one_iff]
    exact ⟨1, map_one _⟩
  obtain ⟨m1, n1, e1⟩ := (mem_iff_exists_int 1 b 1).1 h1
  obtain ⟨m2, n2, e2⟩ := (mem_iff_exists_int 1 b _).1 hθ1
  have hor : orient σ 1 (theta δ qb) = δ := by
    unfold orient; rw [sigma_theta hK σ hσ δ hδ, map_one]; unfold theta; ring
  have hcomb := orient_comb σ m1 n1 m2 n2 (b 0 : K) (b 1 : K)
  rw [← e1, ← e2, hor, hb, hN1, mul_one] at hcomb
  have hδ0 := delta_ne_zero δ hδ
  have hD : (m1 : K) * n2 - n1 * m2 = 1 := by
    have h2 : (((m1 * n2 - n1 * m2 : ℤ) : K) - 1) * δ = 0 := by linear_combination -hcomb
    rcases mul_eq_zero.1 h2 with h3 | h3
    · push_cast at h3; linear_combination h3
    · exact absurd h3 hδ0
  have hb0 : (b 0 : K) = n2 - n1 * theta δ qb := by
    linear_combination (-(n2 : K)) * e1 + (n1 : K) * e2 - (b 0 : K) * hD
  have hb1 : (b 1 : K) = -m2 + m1 * theta δ qb := by
    linear_combination (m2 : K) * e1 - (m1 : K) * e2 - (b 1 : K) * hD
  obtain ⟨m, n, rfl⟩ := (mem_iff_exists_int 1 b y).1 hy
  refine ⟨m * n2 - n * m2, -(m * n1) + n * m1, ?_⟩
  rw [hb0, hb1]; push_cast; ring

/-- `θ` as an element of `𝓞 K`. -/
def thetaO : 𝓞 K := ⟨theta δ qb, theta_isIntegral δ hδ qa qb qc hq⟩

theorem algebraMap_thetaO : algebraMap (𝓞 K) K (thetaO δ hδ qa qb qc hq) = theta δ qb := rfl

/-- The integral ideal `(a, θ)` of `𝓞 K`. -/
noncomputable def idealM : FractionalIdeal (𝓞 K)⁰ K :=
  ((Ideal.span {((qa : ℤ) : 𝓞 K), thetaO δ hδ qa qb qc hq} :
    Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)

include hK hσ hδ hq in
theorem mem_idealM (y : K) :
    y ∈ idealM δ hδ qa qb qc hq ↔ ∃ m n : ℤ, y = (m : K) * qa + (n : K) * theta δ qb := by
  have hθc := algebraMap_thetaO δ hδ qa qb qc hq
  unfold idealM
  rw [FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, d, rfl⟩ := Ideal.mem_span_pair.1 hx
    obtain ⟨m, n, hmn⟩ := mem_one_comb hK σ hσ δ hδ qa qb qc hq (c : K)
      (by rw [Units.val_one, FractionalIdeal.mem_one_iff]; exact ⟨c, rfl⟩)
    obtain ⟨m', n', hmn'⟩ := mem_one_comb hK σ hσ δ hδ qa qb qc hq (d : K)
      (by rw [Units.val_one, FractionalIdeal.mem_one_iff]; exact ⟨d, rfl⟩)
    have hsq := theta_sq δ hδ qa qb qc hq
    refine ⟨m - n' * qc, n * qa + m' + n' * qb, ?_⟩
    have : (algebraMap (𝓞 K) K) (c * (qa : 𝓞 K) + d * thetaO δ hδ qa qb qc hq)
        = (c : K) * qa + (d : K) * theta δ qb := by
      rw [map_add, map_mul, map_mul, hθc]; simp
    rw [this, hmn, hmn']
    push_cast
    linear_combination (n' : K) * hsq
  · rintro ⟨m, n, rfl⟩
    refine ⟨(m : 𝓞 K) * qa + (n : 𝓞 K) * thetaO δ hδ qa qb qc hq,
      Ideal.mem_span_pair.2 ⟨m, n, rfl⟩, ?_⟩
    rw [map_add, map_mul, map_mul, hθc]; simp

variable (hqa : qa ≠ 0)

include hK hσ hδ hq hqa in
theorem idealM_ne_zero : idealM δ hδ qa qb qc hq ≠ 0 := by
  intro h
  have := (mem_idealM hK σ hσ δ hδ qa qb qc hq (qa : K)).2 ⟨1, 0, by simp⟩
  rw [h, FractionalIdeal.mem_zero_iff] at this
  exact hqa (by exact_mod_cast this)

/-- The unit of fractional ideals `(a, θ)`. -/
noncomputable def mUnit : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (idealM δ hδ qa qb qc hq) (idealM_ne_zero hK σ hσ δ hδ qa qb qc hq hqa)

include hK hσ hδ hq hqa in
theorem mem_mUnit (y : K) :
    y ∈ ((mUnit hK σ hσ δ hδ qa qb qc hq hqa : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) ↔ ∃ m n : ℤ, y = (m : K) * qa + (n : K) * theta δ qb :=
  mem_idealM hK σ hσ δ hδ qa qb qc hq y

include hK hσ hδ hq hqa in
theorem qa_mem_mUnit :
    (qa : K) ∈ ((mUnit hK σ hσ δ hδ qa qb qc hq hqa : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) :=
  (mem_mUnit hK σ hσ δ hδ qa qb qc hq hqa _).2 ⟨1, 0, by simp⟩

include hK hσ hδ hq hqa in
theorem theta_mem_mUnit :
    theta δ qb ∈ ((mUnit hK σ hσ δ hδ qa qb qc hq hqa : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) :=
  (mem_mUnit hK σ hσ δ hδ qa qb qc hq hqa _).2 ⟨0, 1, by simp⟩

/-- The pair `(a, θ)` as elements of `(a, θ)`. -/
noncomputable def mVec : Fin 2 → (((mUnit hK σ hσ δ hδ qa qb qc hq hqa : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
  ![⟨(qa : K), qa_mem_mUnit hK σ hσ δ hδ qa qb qc hq hqa⟩,
    ⟨theta δ qb, theta_mem_mUnit hK σ hσ δ hδ qa qb qc hq hqa⟩]

include hK hσ hδ hq hqa in
theorem mVec_li : LinearIndependent ℤ (mVec hK σ hσ δ hδ qa qb qc hq hqa) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h := congrArg (fun z : (((mUnit hK σ hσ δ hδ qa qb qc hq hqa : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) => (z : K)) hg
  simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_zero] at h
  have e1 : (g 0 : K) * qa + (g 1 : K) * theta δ qb = 0 := by
    simpa [mVec, zsmul_eq_mul] using h
  have e2 : (g 0 : K) * qa + (g 1 : K) * σ (theta δ qb) = 0 := by
    have := congrArg σ e1
    simpa [map_add, map_mul, map_intCast] using this
  have hδ0 := delta_ne_zero δ hδ
  have e3 : (g 1 : K) * δ = 0 := by
    unfold theta at e1
    rw [sigma_theta hK σ hσ δ hδ] at e2
    linear_combination e2 - e1
  have hg1 : g 1 = 0 := by
    rcases mul_eq_zero.1 e3 with h3 | h3
    · exact_mod_cast h3
    · exact absurd h3 hδ0
  have hg0 : g 0 = 0 := by
    rw [hg1] at e1
    simp at e1
    rcases e1 with h3 | h3
    · exact_mod_cast h3
    · exact absurd (by exact_mod_cast h3) hqa
  intro i
  fin_cases i
  · exact hg0
  · exact hg1

/-- The `ℤ`-basis `(a, θ)` of `(a, θ)`. -/
noncomputable def mBasis : Basis (Fin 2) ℤ (((mUnit hK σ hσ δ hδ qa qb qc hq hqa :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
  Basis.mk (mVec_li hK σ hσ δ hδ qa qb qc hq hqa) (by
    intro z _
    obtain ⟨m, n, h⟩ := (mem_mUnit hK σ hσ δ hδ qa qb qc hq hqa _).1 z.2
    have hz : z = m • mVec hK σ hσ δ hδ qa qb qc hq hqa 0 + n • mVec hK σ hσ δ hδ qa qb qc hq hqa 1 := by
      apply Subtype.ext
      simpa [mVec, zsmul_eq_mul] using h
    rw [hz]
    exact Submodule.add_mem _ (Submodule.smul_mem _ m (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ n (Submodule.subset_span ⟨1, rfl⟩)))

theorem mBasis_zero : ((mBasis hK σ hσ δ hδ qa qb qc hq hqa 0 : _) : K) = qa := by
  simp [mBasis, mVec]

theorem mBasis_one : ((mBasis hK σ hσ δ hδ qa qb qc hq hqa 1 : _) : K) = theta δ qb := by
  simp [mBasis, mVec]

include hK hσ hδ hq hqa in
theorem orient_mBasis : orient σ (mBasis hK σ hσ δ hδ qa qb qc hq hqa 0 : K)
    (mBasis hK σ hσ δ hδ qa qb qc hq hqa 1 : K) = qa * δ := by
  rw [mBasis_zero, mBasis_one]
  unfold orient
  rw [sigma_theta hK σ hσ δ hδ, map_intCast]
  unfold theta; ring

include hK hσ hδ hq hqa in
theorem absNorm_mUnit :
    FractionalIdeal.absNorm ((mUnit hK σ hσ δ hδ qa qb qc hq hqa : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = |(qa : ℚ)| := by
  have h := orient_sq hK σ hσ (mUnit hK σ hσ δ hδ qa qb qc hq hqa) (mBasis hK σ hσ δ hδ qa qb qc hq hqa)
  rw [orient_mBasis hK σ hσ δ hδ qa qb qc hq hqa] at h
  have hd0 : (NumberField.discr K : K) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero K
  have h2 : (((FractionalIdeal.absNorm ((mUnit hK σ hσ δ hδ qa qb qc hq hqa : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K)) ^ 2 : ℚ) : K) = (((qa : ℚ) ^ 2 : ℚ) : K) := by
    apply mul_right_cancel₀ hd0
    push_cast
    unfold N at h
    linear_combination -h + (qa : K) ^ 2 * hδ
  have h3 : (FractionalIdeal.absNorm ((mUnit hK σ hσ δ hδ qa qb qc hq hqa : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K)) ^ 2 = (qa : ℚ) ^ 2 := Rat.cast_injective h2
  rw [← sq_abs (qa : ℚ)] at h3
  exact (sq_eq_sq₀ (FractionalIdeal.absNorm_nonneg _) (abs_nonneg _)).1 h3

include hK hσ hδ hq in
theorem norm_comb (x y : ℚ) :
    Algebra.norm ℚ ((qa : K) * (x : K) + theta δ qb * (y : K)) =
      (qa : ℚ) * ((qa : ℚ) * x ^ 2 + qb * (x * y) + qc * y ^ 2) := by
  apply Rat.cast_injective (α := K)
  rw [norm_eq_mul_sigma hK σ hσ]
  have hS := theta_add_sigma hK σ hσ δ hδ qb
  have hP := theta_mul_sigma hK σ hσ δ hδ qa qb qc hq
  simp only [map_add, map_mul, map_intCast, map_ratCast]
  push_cast
  linear_combination ((qa : K) * x * y) * hS + (y : K) ^ 2 * hP

theorem formOf_eq_of_values (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
    (f : QuadFormsKB.BinQF)
    (h : ∀ x y : ℤ, idealNormForm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (b 0) (b 1) x y =
      (QuadFormsKB.BinQF.eval f x y : ℚ)) : formOf hK 𝔞 b = f := by
  apply QuadFormsKB.BinQF.ext_of_eval
  intro x y
  apply Int.cast_injective (α := ℚ)
  rw [formOf_eval, h]

include hK hσ in
theorem orient_smul' (α u v : K) :
    orient σ (α * u) (α * v) = ((Algebra.norm ℚ α : ℚ) : K) * orient σ u v := by
  rw [norm_eq_mul_sigma hK σ hσ]
  unfold orient; simp only [map_mul]; ring

include hK hσ hδ in
theorem norm_delta : Algebra.norm ℚ δ = -(NumberField.discr K : ℚ) := by
  apply Rat.cast_injective (α := K)
  rw [norm_eq_mul_sigma hK σ hσ, sigma_delta hK σ hσ δ hδ]
  push_cast
  linear_combination -hδ

theorem absNorm_mul_spanUnit_abs (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α : K) (hα0 : α ≠ 0) :
    FractionalIdeal.absNorm ((𝔞 * spanUnit α hα0 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) * |Algebra.norm ℚ α| := by
  rw [Units.val_mul, map_mul]
  congr 1
  show FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) = _
  rw [FractionalIdeal.absNorm_span_singleton]

include hK hσ hδ in
/-- **Surjectivity** in Milne Thm. 4.29: every form of discriminant `d_K` (positive definite if `d_K < 0`) is the
form of an oriented basis of a fractional ideal. -/
@[kb "milne2020ant" "v3.08, Thm. 4.29, p. 82"]
theorem exists_of_form (f : FormsOfDisc (NumberField.discr K)) :
    ∃ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
      (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)),
      orient σ (b 0) (b 1) = δ * N 𝔞 ∧ formOf hK 𝔞 b = f.1 := by
  obtain ⟨f, hdisc, hpos⟩ := f
  have hq : f.b ^ 2 - 4 * f.a * f.c = NumberField.discr K := hdisc
  have hδ0 := delta_ne_zero δ hδ
  have hsd := sigma_delta hK σ hσ δ hδ
  have hqa : f.a ≠ 0 := by
    intro h0
    rw [h0] at hq
    have hdK : δ ^ 2 = (f.b : K) ^ 2 := by rw [hδ, ← hq]; push_cast; ring
    have hmul : (δ - f.b) * (δ + f.b) = 0 := by linear_combination hdK
    apply hδ0
    rcases mul_eq_zero.1 hmul with h | h
    · have h' : δ = f.b := sub_eq_zero.1 h
      have h2 : -δ = f.b := by rw [← hsd, h', map_intCast]
      linear_combination (1 / 2 : K) * h' - (1 / 2 : K) * h2
    · have h' : δ = -(f.b : K) := eq_neg_of_add_eq_zero_left h
      have h2 : -δ = -(f.b : K) := by rw [← hsd, h', map_neg, map_intCast]
      linear_combination (1 / 2 : K) * h - (1 / 2 : K) * h2
  show ∃ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
      (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)),
      orient σ (b 0) (b 1) = δ * N 𝔞 ∧ formOf hK 𝔞 b = f
  rcases lt_or_gt_of_ne hqa with hneg | hposa
  · -- `a < 0`: then `d_K > 0`; use `δ · (a, θ)`
    have hd : 0 < NumberField.discr K := by
      rcases lt_trichotomy (NumberField.discr K) 0 with h | h | h
      · exact absurd (hpos h) (not_lt.2 hneg.le)
      · exact absurd h (NumberField.discr_ne_zero K)
      · exact h
    have hdQ : (0 : ℚ) < (NumberField.discr K : ℚ) := by exact_mod_cast hd
    have haQ : (f.a : ℚ) < 0 := by exact_mod_cast hneg
    have hN : FractionalIdeal.absNorm ((mUnit hK σ hσ δ hδ f.a f.b f.c hq hqa * spanUnit δ hδ0 :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
        -(f.a : ℚ) * (NumberField.discr K : ℚ) := by
      rw [absNorm_mul_spanUnit_abs, absNorm_mUnit hK σ hσ δ hδ f.a f.b f.c hq hqa,
        norm_delta hK σ hσ δ hδ, abs_of_neg haQ, abs_neg, abs_of_pos hdQ]
    refine ⟨mUnit hK σ hσ δ hδ f.a f.b f.c hq hqa * spanUnit δ hδ0,
      smulBasis _ δ hδ0 (mBasis hK σ hσ δ hδ f.a f.b f.c hq hqa), ?_, ?_⟩
    · rw [smulBasis_apply, smulBasis_apply, orient_smul' hK σ hσ, norm_delta hK σ hσ δ hδ,
        orient_mBasis hK σ hσ δ hδ f.a f.b f.c hq hqa]
      unfold N
      rw [hN]
      push_cast
      ring
    · apply formOf_eq_of_values
      intro x y
      unfold idealNormForm
      rw [hN, smulBasis_apply, smulBasis_apply, mBasis_zero, mBasis_one]
      have h1 : δ * (f.a : K) * ((x : ℚ) : K) + δ * theta δ f.b * ((y : ℚ) : K) =
          δ * ((f.a : K) * ((x : ℚ) : K) + theta δ f.b * ((y : ℚ) : K)) := by ring
      rw [h1, map_mul, norm_comb hK σ hσ δ hδ f.a f.b f.c hq, norm_delta hK σ hσ δ hδ,
        QuadFormsKB.BinQF.eval_eq]
      push_cast
      field_simp
  · refine ⟨mUnit hK σ hσ δ hδ f.a f.b f.c hq hqa, mBasis hK σ hσ δ hδ f.a f.b f.c hq hqa, ?_, ?_⟩
    · rw [orient_mBasis hK σ hσ δ hδ f.a f.b f.c hq hqa]
      unfold N
      rw [absNorm_mUnit hK σ hσ δ hδ f.a f.b f.c hq hqa, abs_of_pos (by exact_mod_cast hposa)]
      push_cast
      ring
    · apply formOf_eq_of_values
      intro x y
      unfold idealNormForm
      rw [absNorm_mUnit hK σ hσ δ hδ f.a f.b f.c hq hqa, mBasis_zero, mBasis_one,
        norm_comb hK σ hσ δ hδ f.a f.b f.c hq, abs_of_pos (by exact_mod_cast hposa),
        QuadFormsKB.BinQF.eval_eq]
      have : (f.a : ℚ) ≠ 0 := by exact_mod_cast hqa
      push_cast
      field_simp

end Surj

end NumberFieldKB.MilneANT.Thm429
