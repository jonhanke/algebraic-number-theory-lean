import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import QuadFormsKB.Citation
import Mathlib.Data.Int.Range
import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc

/-!
# Milne, *Algebraic Number Theory*, Lemma 5.13: a lower bound for the fundamental unit of a cubic field

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

* **Lemma 5.13** (`lemma_5_13`): for a cubic field $K$ with negative discriminant and fundamental unit
  $\varepsilon > 1$ (for the unique real embedding), $\lvert\Delta_K\rvert < 4\varepsilon^3 + 24$.
-/

open NumberField

open Matrix Module

namespace NumberFieldKB.MilneANT


/-- Polynomial inequality, case $r < 2s$ (a sum of squares). -/
lemma ineq2a (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) (h : r < 2 * s) :
    ((1 + r ^ 2) + 2 * s * r) ^ 2 * (1 - s ^ 2) < 1 + 6 * r ^ 2 := by
  nlinarith [sq_nonneg ((1+r^2)*s - 2*r + 2*r*s^2), mul_pos (sq_pos_of_pos hr) (by nlinarith : 0 < 4*s^2 - r^2)]

/-- Polynomial inequality, case $0 \le 2s \le r$. -/
lemma ineq2b (r s : ℝ) (hr : 0 < r) (hr1 : r < 1) (hs : 0 ≤ s) (h : 2 * s ≤ r) :
    ((1 + r ^ 2) + 2 * s * r) ^ 2 * (1 - s ^ 2) < 1 + 6 * r ^ 2 := by
  have h1 : 0 < 1 - r := by linarith
  have hsr : s ≤ r / 2 := by linarith
  have hm : 0 ≤ 2*r - s*(1+r^2) - 2*r*s^2 := by nlinarith [mul_nonneg hs hr.le]
  nlinarith [mul_nonneg hs hr.le, mul_pos hr h1, mul_nonneg hm hs, mul_nonneg hm hr.le, sq_nonneg (r*s), mul_nonneg hs h1.le, mul_nonneg (mul_nonneg hs hr.le) h1.le, mul_nonneg (sub_nonneg.2 hsr) hr.le]

/-- Polynomial inequality, case $s < 0$. -/
lemma ineq2c (r s : ℝ) (hr : 0 < r) (hr1 : r < 1) (hs : s ^ 2 ≤ 1) (hs0 : s < 0) :
    ((1 + r ^ 2) + 2 * s * r) ^ 2 * (1 - s ^ 2) < 1 + 6 * r ^ 2 := by
  have h1 : -1 ≤ s := by nlinarith
  have hQ0 : 0 < 1 + r ^ 2 + 2 * s * r := by nlinarith [sq_nonneg (1 - r)]
  have hQ : 1 + r ^ 2 + 2 * s * r ≤ 1 + r ^ 2 := by nlinarith
  have hQ2 : (1 + r ^ 2 + 2 * s * r) ^ 2 ≤ (1 + r ^ 2) ^ 2 := by nlinarith
  have h1s : 1 - s ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
  have h1s' : 0 ≤ 1 - s ^ 2 := by linarith
  have : (1 + r ^ 2 + 2 * s * r) ^ 2 * (1 - s ^ 2) ≤ (1 + r ^ 2) ^ 2 := by
    calc _ ≤ (1 + r ^ 2 + 2 * s * r) ^ 2 * 1 := by gcongr
      _ ≤ _ := by linarith
  nlinarith [mul_pos hr hr, mul_pos (mul_pos hr hr) (sub_pos.2 hr1), sq_nonneg r]

/-- The real inequality behind Lemma 5.13: if $e > 1$ and $e(a^2+b^2) = 1$ then $((e-a)^2+b^2)^2\cdot 4b^2 < 4e^3+24$. -/
lemma real_ineq (e a b : ℝ) (he : 1 < e) (h : e * (a ^ 2 + b ^ 2) = 1) :
    ((e - a) ^ 2 + b ^ 2) ^ 2 * (4 * b ^ 2) < 4 * e ^ 3 + 24 := by
  obtain ⟨u, hu0, hue⟩ : ∃ u : ℝ, 0 < u ∧ u ^ 2 = e := ⟨Real.sqrt e, Real.sqrt_pos.2 (by linarith), Real.sq_sqrt (by linarith)⟩
  have hu1 : 1 < u := by nlinarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = -(a * u) := ⟨_, rfl⟩
  have ha : a = -s / u := by rw [hs]; field_simp
  have hb2 : b ^ 2 = (1 - s ^ 2) / u ^ 2 := by
    rw [eq_div_iff (by positivity), hs]
    rw [← hue] at h
    nlinarith
  have hs2 : s ^ 2 ≤ 1 := by
    have : 0 ≤ b ^ 2 := sq_nonneg b
    rw [hb2] at this
    have := (div_nonneg_iff.1 this)
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · nlinarith [sq_nonneg u]
  set r : ℝ := 1 / u ^ 3 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one (by positivity)]
    nlinarith [sq_nonneg u]
  have hkey : ((1 + r ^ 2) + 2 * s * r) ^ 2 * (1 - s ^ 2) < 1 + 6 * r ^ 2 := by
    rcases lt_or_ge s 0 with hs0 | hs0
    · exact ineq2c r s hr0 hr1 hs2 hs0
    · rcases lt_or_ge r (2 * s) with h1 | h1
      · exact ineq2a r s hr0 hs0 h1
      · exact ineq2b r s hr0 hr1 hs0 h1
  have hL : ((e - a) ^ 2 + b ^ 2) ^ 2 * (4 * b ^ 2) =
      4 * u ^ 6 * (((1 + r ^ 2) + 2 * s * r) ^ 2 * (1 - s ^ 2)) := by
    rw [hb2, ha, ← hue, hr]
    field_simp
    ring
  have hR : 4 * e ^ 3 + 24 = 4 * u ^ 6 * (1 + 6 * r ^ 2) := by
    rw [← hue, hr]
    field_simp
    ring
  rw [hL, hR]
  have : 0 < 4 * u ^ 6 := by positivity
  exact mul_lt_mul_of_pos_left hkey this

/-- If $1, x, x^2$ is a power basis consisting of algebraic integers, its discriminant is a nonzero integer square times the discriminant of the number field. -/
lemma abs_discr_le_of_integral {K : Type*} [Field K] [NumberField K] (pb : PowerBasis ℚ K)
    (hint : ∀ j, ∃ y : 𝓞 K, pb.basis j = algebraMap (𝓞 K) K y) :
    ∃ n : ℤ, n ≠ 0 ∧ Algebra.discr ℚ pb.basis = (n : ℚ) ^ 2 * (NumberField.discr K : ℚ) := by
  classical
  let B := (integralBasis K).reindex ((integralBasis K).indexEquiv pb.basis)
  have hB : Algebra.discr ℚ B = (NumberField.discr K : ℚ) := by
    rw [NumberField.coe_discr, Basis.coe_reindex, Algebra.discr_reindex]
  let P := B.toMatrix pb.basis
  have hP : ∀ i j, ∃ z : ℤ, P i j = algebraMap ℤ ℚ z := by
    intro i j
    obtain ⟨y, hy⟩ := hint j
    refine ⟨(RingOfIntegers.basis K).repr y ((integralBasis K).indexEquiv pb.basis |>.symm i), ?_⟩
    show B.repr (pb.basis j) i = _
    rw [hy, Basis.repr_reindex_apply, integralBasis_repr_apply]
  choose Q hQ using hP
  have hPQ : P = (Matrix.of Q).map (algebraMap ℤ ℚ) := by
    ext i j; simp [hQ]
  have hdet : P.det = ((Matrix.of Q).det : ℚ) := by
    rw [hPQ]
    have := RingHom.map_det (algebraMap ℤ ℚ) (Matrix.of Q)
    simpa [RingHom.mapMatrix_apply] using this.symm
  have hrel : Algebra.discr ℚ pb.basis = P.det ^ 2 * Algebra.discr ℚ B := by
    rw [← Algebra.discr_of_matrix_vecMul B P]
    rw [show B ᵥ* P.map (algebraMap ℚ K) = pb.basis from B.toMatrix_map_vecMul pb.basis]
  have hne : Algebra.discr ℚ pb.basis ≠ 0 := Algebra.discr_not_zero_of_basis ℚ pb.basis
  rw [hrel, hB, hdet] at hne ⊢
  refine ⟨(Matrix.of Q).det, ?_, rfl⟩
  intro h; apply hne; simp [h]


/-- A unit whose image under a real embedding exceeds one is not rational. -/
lemma not_mem_range_of_one_lt {K : Type*} [Field K] [NumberField K] (ε : (𝓞 K)ˣ) (φ : K →+* ℝ)
    (hε : 1 < φ ((ε : 𝓞 K) : K)) :
    ((ε : 𝓞 K) : K) ∉ (algebraMap ℚ K).range := by
  rintro ⟨q, hq⟩
  have hq1 : 1 < (q : ℝ) := by
    have : φ (algebraMap ℚ K q) = (q : ℝ) := by simp
    rw [← this, hq]; exact hε
  have hq0 : q ≠ 0 := by
    intro h
    have : (q : ℝ) = 0 := by exact_mod_cast h
    linarith
  -- the inverse is an algebraic integer, hence q⁻¹ is an integer
  have hint : IsIntegral ℤ (((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) := (((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K)).isIntegral_coe
  have hinv : (((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = algebraMap ℚ K q⁻¹ := by
    have h1 : ((ε : 𝓞 K) : K) * (((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = 1 := by
      simp
    rw [map_inv₀, hq]
    exact eq_inv_of_mul_eq_one_right h1
  rw [hinv] at hint
  have hint' : IsIntegral ℤ q⁻¹ := isIntegral_algebraMap_iff.1 hint
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
  have hm' : (m : ℚ) = q⁻¹ := by simpa using hm
  have hm0 : m ≠ 0 := by
    intro h; rw [h] at hm'; simp at hm'; exact hq0 hm'.symm
  have : (1 : ℚ) ≤ |(m : ℚ)| := by exact_mod_cast Int.one_le_abs hm0
  rw [hm', abs_inv] at this
  have hq2 : (1 : ℚ) < q := by exact_mod_cast hq1
  rw [abs_of_pos (by linarith)] at this
  have := (one_le_inv₀ (by linarith)).1 this
  linarith

/-- In a cubic number field, an element outside the rationals is the generator of a power basis of dimension three. -/
lemma exists_powerBasis_of_not_mem_range {K : Type*} [Field K] [NumberField K]
    (h3 : Module.finrank ℚ K = 3) (x : K) (hx : x ∉ (algebraMap ℚ K).range) :
    ∃ pb : PowerBasis ℚ K, pb.gen = x ∧ pb.dim = 3 := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have h2 : 2 ≤ (minpoly ℚ x).natDegree := (minpoly.two_le_natDegree_iff hint).2 hx
  have hdvd : (minpoly ℚ x).natDegree ∣ 3 := by
    rw [← h3, ← IntermediateField.adjoin.finrank hint]
    exact ⟨_, (Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ {x}) K).symm⟩
  have h33 : (minpoly ℚ x).natDegree = 3 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : (minpoly ℚ x).natDegree
    · omega
    · rfl
  have htop : IntermediateField.adjoin ℚ {x} = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [IntermediateField.adjoin.finrank hint, h33, IntermediateField.finrank_top', h3]
  exact ⟨PowerBasis.ofAdjoinSimpleEqTop hint htop, by simp, by simp [h33]⟩


/-- Product over pairs for an index type of size three. -/
lemma prod3_pairs (n : ℕ) (h : n = 3) (F : Fin n → Fin n → ℂ) :
    ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, F i j =
      F ⟨0, by omega⟩ ⟨1, by omega⟩ * F ⟨0, by omega⟩ ⟨2, by omega⟩ * F ⟨1, by omega⟩ ⟨2, by omega⟩ := by
  subst h
  have h0 : Finset.Ioi (0 : Fin 3) = {1, 2} := by decide
  have h1 : Finset.Ioi (1 : Fin 3) = {2} := by decide
  have h2 : Finset.Ioi (2 : Fin 3) = ∅ := by decide
  rw [Fin.prod_univ_three]
  show (∏ j ∈ Finset.Ioi (0 : Fin 3), _) * (∏ j ∈ Finset.Ioi (1 : Fin 3), _) * (∏ j ∈ Finset.Ioi (2 : Fin 3), _) = _
  rw [h0, h1, h2]
  simp

/-- Product over an index type of size three. -/
lemma prod3_single (n : ℕ) (h : n = 3) (F : Fin n → ℂ) :
    ∏ i : Fin n, F i = F ⟨0, by omega⟩ * F ⟨1, by omega⟩ * F ⟨2, by omega⟩ := by
  subst h
  simp [Fin.prod_univ_three]

/-- The discriminant of a cubic power basis as the square of a product of differences of conjugates. -/
lemma disc_formula {K : Type*} [Field K] [NumberField K] (pb : PowerBasis ℚ K) (hdim : pb.dim = 3)
    (e : Fin pb.dim ≃ (K →ₐ[ℚ] ℂ)) :
    algebraMap ℚ ℂ (Algebra.discr ℚ pb.basis) =
      ((e ⟨1, by omega⟩ pb.gen - e ⟨0, by omega⟩ pb.gen) * (e ⟨2, by omega⟩ pb.gen - e ⟨0, by omega⟩ pb.gen) *
        (e ⟨2, by omega⟩ pb.gen - e ⟨1, by omega⟩ pb.gen)) ^ 2 := by
  rw [Algebra.discr_powerBasis_eq_prod ℚ ℂ pb e]
  refine (prod3_pairs pb.dim hdim (fun i j => (e j pb.gen - e i pb.gen) ^ 2)).trans ?_
  ring

/-- Discriminant of a cubic power basis with one real embedding and a complex conjugate pair, written in real coordinates of the complex conjugate. -/
lemma cubic_disc_formula {K : Type*} [Field K] [NumberField K] (pb : PowerBasis ℚ K)
    (hdim : pb.dim = 3) (φ : K →+* ℝ) (hpos : 0 < φ pb.gen)
    (hnorm : Algebra.norm ℚ pb.gen = 1 ∨ Algebra.norm ℚ pb.gen = -1)
    (hneg : Algebra.discr ℚ pb.basis < 0) :
    ∃ a b : ℝ, φ pb.gen * (a ^ 2 + b ^ 2) = 1 ∧
      ((Algebra.discr ℚ pb.basis : ℚ) : ℝ) = -(((φ pb.gen - a) ^ 2 + b ^ 2) ^ 2 * (4 * b ^ 2)) := by
  classical
  set g := pb.gen with hg
  have hcard : Fintype.card (Fin pb.dim) = Fintype.card (K →ₐ[ℚ] ℂ) := by
    rw [Fintype.card_fin, AlgHom.card, ← PowerBasis.finrank pb]
  -- Step 1: some embedding has a non-real value at the generator.
  have hnonreal : ∃ σ : K →ₐ[ℚ] ℂ, (σ g).im ≠ 0 := by
    by_contra hall
    push Not at hall
    let e0 : Fin pb.dim ≃ (K →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq hcard
    have hform := disc_formula pb hdim e0
    set t := (e0 ⟨1, by omega⟩ g - e0 ⟨0, by omega⟩ g) * (e0 ⟨2, by omega⟩ g - e0 ⟨0, by omega⟩ g) *
        (e0 ⟨2, by omega⟩ g - e0 ⟨1, by omega⟩ g) with ht
    have htim : t.im = 0 := by
      simp [ht, Complex.mul_im, Complex.sub_im, Complex.sub_re, hall]
    have htt : t ^ 2 = ((t.re ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im, htim]
    have h1 : ((Algebra.discr ℚ pb.basis : ℚ) : ℂ) = (((Algebra.discr ℚ pb.basis : ℚ) : ℝ) : ℂ) := by
      simp
    have h2 : (((Algebra.discr ℚ pb.basis : ℚ) : ℝ)) = t.re ^ 2 := by
      apply Complex.ofReal_injective
      rw [← h1]
      exact hform.trans htt
    have : (Algebra.discr ℚ pb.basis : ℝ) < 0 := by exact_mod_cast hneg
    nlinarith [sq_nonneg t.re]
  obtain ⟨σ, hσ⟩ := hnonreal
  set z := σ g with hz
  let φt : K →ₐ[ℚ] ℂ := (Complex.ofRealHom.comp φ).toRatAlgHom
  let σ' : K →ₐ[ℚ] ℂ := ((starRingEnd ℂ).comp σ.toRingHom).toRatAlgHom
  have hφt : φt g = ((φ g : ℝ) : ℂ) := by simp [φt]
  have hσ' : σ' g = (starRingEnd ℂ) z := by simp [σ', hz]
  have hz1 : z ≠ ((φ g : ℝ) : ℂ) := fun h => hσ (by rw [h]; simp)
  have hz2 : (starRingEnd ℂ) z ≠ ((φ g : ℝ) : ℂ) := fun h => hσ (by
    have := congrArg Complex.im h; simp at this; exact this)
  have hz3 : z ≠ (starRingEnd ℂ) z := fun h => hσ (by
    have := congrArg Complex.im h; simp at this; linarith)
  let f : Fin pb.dim → (K →ₐ[ℚ] ℂ) := fun i => if i.val = 0 then φt else if i.val = 1 then σ else σ'
  have hinj : Function.Injective f := by
    intro i j hij
    have h := congrArg (fun τ => τ g) hij
    simp only [f] at h
    apply Fin.ext
    have hi : i.val < 3 := by omega
    have hj : j.val < 3 := by omega
    rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with h1 | h1 | h1 <;>
    rcases (by omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with h2 | h2 | h2 <;>
    simp [h1, h2, hφt, hσ', ← hz, hz1, hz2, hz3, hz1.symm, hz2.symm, hz3.symm] at h ⊢
  let e : Fin pb.dim ≃ (K →ₐ[ℚ] ℂ) :=
    Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩)
  have he0 : e ⟨0, by omega⟩ g = ((φ g : ℝ) : ℂ) := by simp [e, f, hφt]
  have he1 : e ⟨1, by omega⟩ g = z := by simp [e, f] ; exact hz.symm
  have he2 : e ⟨2, by omega⟩ g = (starRingEnd ℂ) z := by simp [e, f, hσ']
  have hform := disc_formula pb hdim e
  rw [he0, he1, he2] at hform
  -- the norm
  have hn1 : algebraMap ℚ ℂ (Algebra.norm ℚ g) = ((φ g : ℝ) : ℂ) * z * (starRingEnd ℂ) z := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ g]
    rw [← Fintype.prod_equiv e (fun i => e i g) (fun τ => τ g) (fun _ => rfl)]
    rw [prod3_single pb.dim hdim, he0, he1, he2]
  have hzpos : 0 < Complex.normSq z := by
    rw [Complex.normSq_pos]; intro h; apply hσ; rw [h]; simp
  have hn2 : φ g * Complex.normSq z = 1 := by
    have hc : ((φ g * Complex.normSq z : ℝ) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ g) := by
      rw [hn1]; push_cast; rw [mul_assoc, Complex.mul_conj]
    rcases hnorm with h | h
    · rw [h, map_one] at hc; exact_mod_cast hc
    · rw [h, map_neg, map_one] at hc
      have : φ g * Complex.normSq z = -1 := by exact_mod_cast hc
      nlinarith [mul_pos hpos hzpos]
  refine ⟨z.re, z.im, ?_, ?_⟩
  · rw [Complex.normSq_apply] at hn2; ring_nf at hn2 ⊢; linarith
  · apply Complex.ofReal_injective
    have h1 : (((Algebra.discr ℚ pb.basis : ℚ) : ℝ) : ℂ) = algebraMap ℚ ℂ (Algebra.discr ℚ pb.basis) := by
      simp
    rw [h1, hform]
    apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- **Lemma 5.13.** Let $K$ be a cubic extension of $\mathbb Q$ with negative discriminant, and let $\varepsilon$ be
a fundamental unit ($U_K = \{\pm\varepsilon^m\}$) with $\varepsilon > 1$ under the real embedding $\varphi$. Then
$\lvert\Delta_K\rvert < 4\varepsilon^3 + 24$. The hypothesis `hfund` (Milne's) is not used by the proof: the bound
holds for every unit $\varepsilon$ with $\varphi(\varepsilon) > 1$. -/
@[kb "milne2020ant" "v3.08, Lemma 5.13, p. 92"]
theorem lemma_5_13 {K : Type*} [Field K] [NumberField K] (h3 : Module.finrank ℚ K = 3) (hd : discr K < 0)
    (ε : (𝓞 K)ˣ) (hfund : ∀ u : (𝓞 K)ˣ, ∃ m : ℤ, u = ε ^ m ∨ u = -ε ^ m) (φ : K →+* ℝ)
    (hε : 1 < φ ((ε : 𝓞 K) : K)) :
    (|discr K| : ℝ) < 4 * φ ((ε : 𝓞 K) : K) ^ 3 + 24 := by
  set x : K := ((ε : 𝓞 K) : K) with hx
  obtain ⟨pb, hgen, hdim⟩ := exists_powerBasis_of_not_mem_range h3 x
    (not_mem_range_of_one_lt ε φ hε)
  have hint : ∀ j, ∃ y : 𝓞 K, pb.basis j = algebraMap (𝓞 K) K y := by
    intro j
    refine ⟨ε ^ (j : ℕ), ?_⟩
    rw [PowerBasis.coe_basis, hgen]
    simp [hx]
  obtain ⟨n, hn0, hrel⟩ := abs_discr_le_of_integral pb hint
  have hdq : (NumberField.discr K : ℚ) < 0 := by exact_mod_cast hd
  have hn2 : (0 : ℚ) < (n : ℚ) ^ 2 := by
    have : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
    positivity
  have hneg : Algebra.discr ℚ pb.basis < 0 := by
    rw [hrel]; exact mul_neg_of_pos_of_neg hn2 hdq
  have hnorm : Algebra.norm ℚ pb.gen = 1 ∨ Algebra.norm ℚ pb.gen = -1 := by
    have hu : IsUnit (Algebra.norm ℤ (ε : 𝓞 K)) := ε.isUnit.map (Algebra.norm ℤ)
    rcases Int.isUnit_iff.1 hu with h | h
    · left
      rw [hgen, hx, ← Algebra.coe_norm_int, h]; simp
    · right
      rw [hgen, hx, ← Algebra.coe_norm_int, h]; simp
  have hpos : 0 < φ pb.gen := by rw [hgen]; exact lt_trans zero_lt_one hε
  obtain ⟨a, b, hab, hform⟩ := cubic_disc_formula pb hdim φ hpos hnorm hneg
  have he1 : 1 < φ pb.gen := by rw [hgen]; exact hε
  have hineq := real_ineq (φ pb.gen) a b he1 hab
  -- |discr K| ≤ |Δ₀|
  have hle : (|(NumberField.discr K : ℚ)| : ℚ) ≤ |Algebra.discr ℚ pb.basis| := by
    rw [hrel, abs_mul, abs_pow]
    have h1 : (1 : ℚ) ≤ |(n : ℚ)| := by exact_mod_cast Int.one_le_abs hn0
    have h2 : (1 : ℚ) ≤ |(n : ℚ)| ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h2 (abs_nonneg (NumberField.discr K : ℚ))]
  have hleR : (|(NumberField.discr K : ℝ)| : ℝ) ≤ |((Algebra.discr ℚ pb.basis : ℚ) : ℝ)| := by
    have := (Rat.cast_le (K := ℝ)).2 hle
    simpa using this
  have habs : |((Algebra.discr ℚ pb.basis : ℚ) : ℝ)| = ((φ pb.gen - a) ^ 2 + b ^ 2) ^ 2 * (4 * b ^ 2) := by
    rw [hform, abs_neg]
    exact abs_of_nonneg (by positivity)
  rw [habs] at hleR
  have hgx : φ pb.gen = φ ((ε : 𝓞 K) : K) := by rw [hgen]
  rw [hgx] at hineq
  rw [← hgx] at hineq ⊢
  exact lt_of_le_of_lt hleR hineq

end NumberFieldKB.MilneANT
