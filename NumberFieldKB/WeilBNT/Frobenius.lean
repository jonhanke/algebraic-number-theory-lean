import Mathlib.Algebra.QuaternionBasis
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Frobenius' theorem: the finite-dimensional real division algebras

Weil, *Basic Number Theory*, I.§3, text p. 12, uses (and defers to Chap. IX-4) the theorem of Frobenius: a division
algebra of finite dimension over $\mathbb R$ is isomorphic to $\mathbb R$, $\mathbb C$ or the quaternions
$\mathbb H$.

* **`frobenius_real_divisionAlgebra`**: a division ring $D$ which is a finite-dimensional $\mathbb R$-algebra is
  isomorphic as an $\mathbb R$-algebra to $\mathbb R$, to $\mathbb C$ or to $\mathbb H=$ `Quaternion ℝ`.

*Proof.* Every $x\in D$ has an irreducible minimal polynomial over $\mathbb R$, of degree $\le2$; if $D\ne\mathbb R$ this
gives $i\in D$ with $i^2=-1$. An element commuting with $i$ lies in $\mathbb R(i)$ (it also squares to a negative
real after a real shift, and the two square roots of $-1$ commuting with each other agree up to sign).
Conjugation by $i$ is an
involution, so $D=D_+\oplus D_-$ with $D_+=\mathbb R(i)$ and $D_-=\{y:iy=-yi\}$. If $D_-=0$ then $D\cong\mathbb C$.
Otherwise a nonzero $y\in D_-$ has $y^2$ commuting with $i$ and with $y$, so $y^2\in\mathbb R$, and $y^2<0$; rescaling
gives $j$ with $j^2=-1$, $ij=-ji$, and $z\mapsto zj^{-1}$ maps $D_-$ onto $D_+$, so $1,i,j,ij$ is a basis and the
quaternion basis $(i,j,ij)$ gives an isomorphism $\mathbb H\to D$.
-/

noncomputable section

namespace NumberFieldKB.WeilBNT.Frobenius

section Aux

variable {D : Type*} [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D]

/-- Every element of a finite-dimensional real division algebra is either a real multiple of one, or
satisfies $(x-a)^2=-c^2$ for some real $a$ and positive real $c$ (its minimal polynomial is an irreducible
quadratic). -/
lemma quad_dichotomy (x : D) :
    (∃ r : ℝ, x = r • (1 : D)) ∨
      ∃ a c : ℝ, 0 < c ∧ (x - a • (1 : D)) * (x - a • (1 : D)) = -((c ^ 2) • (1 : D)) := by
  have hint : IsIntegral ℝ x := Algebra.IsIntegral.isIntegral x
  have hirr := minpoly.irreducible hint
  have hle := hirr.natDegree_le_two
  have hpos := minpoly.natDegree_pos hint
  by_cases h1 : (minpoly ℝ x).natDegree = 1
  · left
    obtain ⟨r, hr⟩ := minpoly.natDegree_eq_one_iff.mp h1
    exact ⟨r, by rw [← hr, Algebra.algebraMap_eq_smul_one]⟩
  · right
    have h2 : (minpoly ℝ x).natDegree = 2 := by omega
    have hmon : (minpoly ℝ x).Monic := minpoly.monic hint
    have hz := minpoly.aeval ℝ x
    rw [Polynomial.aeval_eq_sum_range, h2] at hz
    have hc2 : (minpoly ℝ x).coeff 2 = 1 := by
      have := hmon.coeff_natDegree
      rwa [h2] at this
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, hc2, pow_zero, pow_one,
      pow_two, zero_add, one_smul] at hz
    set b0 := (minpoly ℝ x).coeff 0
    set b1 := (minpoly ℝ x).coeff 1
    have key : (x - (-(b1 / 2)) • (1 : D)) * (x - (-(b1 / 2)) • (1 : D)) =
        (b1 ^ 2 / 4 - b0) • (1 : D) := by
      simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
      linear_combination (norm := module) hz
    rcases lt_or_ge (b1 ^ 2 / 4 - b0) 0 with hs | hs
    · refine ⟨-(b1 / 2), Real.sqrt (-(b1 ^ 2 / 4 - b0)), Real.sqrt_pos.mpr (by linarith), ?_⟩
      rw [key, Real.sq_sqrt (by linarith), neg_smul, neg_neg]
    · exfalso
      set t := Real.sqrt (b1 ^ 2 / 4 - b0) with ht
      have htt : t * t = b1 ^ 2 / 4 - b0 := Real.mul_self_sqrt hs
      have hprod : (x - (-(b1 / 2) + t) • (1 : D)) * (x - (-(b1 / 2) - t) • (1 : D)) = 0 := by
        have : (x - (-(b1 / 2) + t) • (1 : D)) * (x - (-(b1 / 2) - t) • (1 : D)) =
            (x - (-(b1 / 2)) • (1 : D)) * (x - (-(b1 / 2)) • (1 : D)) - (t * t) • (1 : D) := by
          simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
          module
        rw [this, key, htt, sub_self]
      have hnot : ∀ r : ℝ, x ≠ r • (1 : D) := by
        intro r hr
        have : (minpoly ℝ x).natDegree = 1 :=
          minpoly.natDegree_eq_one_iff.mpr ⟨r, by rw [Algebra.algebraMap_eq_smul_one, hr]⟩
        omega
      rcases mul_eq_zero.mp hprod with h | h
      · exact hnot _ (sub_eq_zero.mp h)
      · exact hnot _ (sub_eq_zero.mp h)

/-- If $i^2=-1$ and $z$ commutes with $i$, then $z=a+bi$ for real $a,b$. -/
lemma mem_span_of_commute {i z : D} (hi : i * i = -1) (hz : z * i = i * z) :
    ∃ a b : ℝ, z = a • (1 : D) + b • i := by
  rcases quad_dichotomy z with ⟨r, hr⟩ | ⟨a, c, hc, h⟩
  · exact ⟨r, 0, by simp [hr]⟩
  · set u := z - a • (1 : D) with hu
    have hui : u * i = i * u := by
      simp only [hu, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hz]
    have hprod : (c • i - u) * (c • i + u) = 0 := by
      have : (c • i - u) * (c • i + u) = (c * c) • (i * i) + c • (i * u) - c • (u * i) - u * u := by
        simp only [mul_add, sub_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
        module
      rw [this, hui, h, hi]
      module
    rcases mul_eq_zero.mp hprod with h' | h'
    · refine ⟨a, c, ?_⟩
      have : u = c • i := (sub_eq_zero.mp h').symm
      rw [← this, hu]; abel
    · refine ⟨a, -c, ?_⟩
      have : u = -(c • i) := eq_neg_of_add_eq_zero_right h'
      rw [neg_smul, ← this, hu]; abel

/-- Splitting into the parts commuting and anticommuting with $i$. -/
lemma decomp {i : D} (hi : i * i = -1) (y : D) :
    ∃ yp ym : D, y = yp + ym ∧ yp * i = i * yp ∧ i * ym = -(ym * i) := by
  have e1 : i * y * i * i = -(i * y) := by rw [mul_assoc, hi]; simp
  have e2 : i * (i * y * i) = -(y * i) := by rw [← mul_assoc, ← mul_assoc, hi]; simp
  refine ⟨(1 / 2 : ℝ) • (y - i * y * i), (1 / 2 : ℝ) • (y + i * y * i), ?_, ?_, ?_⟩
  · module
  · simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, e1, e2]
    module
  · simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, e1, e2]
    module

/-- If $i^2=-1$ and $yi=0$ then $y=0$. -/
lemma eq_zero_of_mul_eq_zero {i y : D} (hi : i * i = -1) (h : y * i = 0) : y = 0 := by
  have : y * (i * i) = 0 := by rw [← mul_assoc, h, zero_mul]
  rw [hi] at this
  simpa using this

/-- If some element is not a real multiple of one, there is a square root of $-1$. -/
lemma exists_sq_eq_neg_one (h : ∃ x : D, ∀ r : ℝ, x ≠ r • (1 : D)) : ∃ i : D, i * i = -1 := by
  obtain ⟨x, hx⟩ := h
  rcases quad_dichotomy x with ⟨r, hr⟩ | ⟨a, c, hc, h⟩
  · exact absurd hr (hx r)
  · refine ⟨c⁻¹ • (x - a • (1 : D)), ?_⟩
    rw [smul_mul_smul_comm, h, smul_neg, smul_smul]
    have : c⁻¹ * c⁻¹ * c ^ 2 = 1 := by field_simp
    rw [this, one_smul]

/-- A nonzero element anticommuting with $i$ yields $j$ with $j^2=-1$ anticommuting with $i$. -/
lemma exists_anticommuting {i y : D} (hi : i * i = -1) (hy0 : y ≠ 0) (hy : i * y = -(y * i)) :
    ∃ j : D, j * j = -1 ∧ i * j = -(j * i) := by
  have hyy : (y * y) * i = i * (y * y) := by
    calc y * y * i = y * (y * i) := by rw [mul_assoc]
      _ = -(y * (i * y)) := by rw [hy]; simp
      _ = -((y * i) * y) := by rw [mul_assoc]
      _ = (i * y) * y := by rw [hy]; simp
      _ = i * (y * y) := by rw [mul_assoc]
  obtain ⟨a, b, hab⟩ := mem_span_of_commute hi hyy
  have hb : b = 0 := by
    by_contra hb
    have hc : y * (y * y) = (y * y) * y := by rw [← mul_assoc]
    rw [hab] at hc
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul] at hc
    rw [hy] at hc
    have h2 : (2 * b) • (y * i) = 0 := by
      have : (2 * b) • (y * i) = (a • y + b • (y * i)) - (a • y + b • -(y * i)) := by
        rw [smul_neg]; module
      rw [this]
      exact sub_eq_zero.mpr hc
    rcases smul_eq_zero.mp h2 with h | h
    · exact hb (by linarith)
    · exact hy0 (eq_zero_of_mul_eq_zero hi h)
  rw [hb, zero_smul, add_zero] at hab
  have ha : a < 0 := by
    by_contra ha
    push_neg at ha
    have htt := Real.mul_self_sqrt ha
    have hprod : (y - Real.sqrt a • (1 : D)) * (y + Real.sqrt a • (1 : D)) = 0 := by
      have : (y - Real.sqrt a • (1 : D)) * (y + Real.sqrt a • (1 : D)) =
          y * y - (Real.sqrt a * Real.sqrt a) • (1 : D) := by
        simp only [mul_add, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
        module
      rw [this, hab, htt, sub_self]
    have hcomm : ∀ r : ℝ, y = r • (1 : D) → y = 0 := by
      intro r hr
      have h1 : y * i = i * y := by rw [hr]; simp
      rw [hy] at h1
      have h2 : y * i = 0 := by
        have : (2 : ℝ) • (y * i) = 0 := by
          have : (2 : ℝ) • (y * i) = (y * i) - (-(y * i)) := by module
          rw [this]; exact sub_eq_zero.mpr h1
        simpa using this
      exact eq_zero_of_mul_eq_zero hi h2
    rcases mul_eq_zero.mp hprod with h | h
    · exact hy0 (hcomm _ (sub_eq_zero.mp h))
    · refine hy0 (hcomm (-Real.sqrt a) ?_)
      rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h
  have hs : 0 < Real.sqrt (-a) := Real.sqrt_pos.mpr (by linarith)
  refine ⟨(Real.sqrt (-a))⁻¹ • y, ?_, ?_⟩
  · rw [smul_mul_smul_comm, hab, smul_smul]
    have h1 : (Real.sqrt (-a))⁻¹ * (Real.sqrt (-a))⁻¹ * a = -1 := by
      have := Real.mul_self_sqrt (show 0 ≤ -a by linarith)
      field_simp
      linarith
    rw [h1]; simp
  · simp only [mul_smul_comm, smul_mul_assoc, hy, smul_neg]

/-- Quaternion case: if $i^2=j^2=-1$ and $ij=-ji$ and $1,i,j,ij$ span, then $D\cong\mathbb H$. -/
lemma quaternion_case {i j : D} (hi : i * i = -1) (hj : j * j = -1) (hij : i * j = -(j * i))
    (hspan : ∀ z : D, ∃ a b c d : ℝ, z = a • (1 : D) + b • i + c • j + d • (i * j)) :
    Nonempty (D ≃ₐ[ℝ] Quaternion ℝ) := by
  let B : QuaternionAlgebra.Basis D (-1 : ℝ) 0 (-1 : ℝ) :=
    { i := i
      j := j
      k := i * j
      i_mul_i := by simp [hi]
      j_mul_j := by simp [hj]
      i_mul_j := rfl
      j_mul_i := by simp [hij] }
  have hinj : Function.Injective B.liftHom := (B.liftHom : Quaternion ℝ →+* D).injective
  have hsurj : Function.Surjective B.liftHom := by
    intro z
    obtain ⟨a, b, c, d, rfl⟩ := hspan z
    refine ⟨⟨a, b, c, d⟩, ?_⟩
    simp [QuaternionAlgebra.Basis.lift, B, Algebra.algebraMap_eq_smul_one, add_assoc]
  exact ⟨(AlgEquiv.ofBijective B.liftHom ⟨hinj, hsurj⟩).symm⟩

/-- Complex case: if $i^2=-1$ and nothing nonzero anticommutes with $i$, then $D\cong\mathbb C$. -/
lemma complex_case {i : D} (hi : i * i = -1) (hall : ∀ y : D, i * y = -(y * i) → y = 0) :
    Nonempty (D ≃ₐ[ℝ] ℂ) := by
  have hinj : Function.Injective (Complex.liftAux i hi) :=
    (Complex.liftAux i hi : ℂ →+* D).injective
  have hsurj : Function.Surjective (Complex.liftAux i hi) := by
    intro y
    obtain ⟨yp, ym, rfl, hp, hm⟩ := decomp hi y
    obtain ⟨a, b, hab⟩ := mem_span_of_commute hi hp
    refine ⟨⟨a, b⟩, ?_⟩
    rw [hall ym hm, add_zero, hab, Complex.liftAux_apply, Algebra.algebraMap_eq_smul_one]
  exact ⟨(AlgEquiv.ofBijective (Complex.liftAux i hi) ⟨hinj, hsurj⟩).symm⟩

end Aux

/-- **Frobenius' theorem.** A division ring of finite dimension over $\mathbb R$ is isomorphic, as an
$\mathbb R$-algebra, to $\mathbb R$, $\mathbb C$ or the quaternions $\mathbb H$. -/
theorem frobenius_real_divisionAlgebra (D : Type*) [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D] :
    Nonempty (D ≃ₐ[ℝ] ℝ) ∨ Nonempty (D ≃ₐ[ℝ] ℂ) ∨ Nonempty (D ≃ₐ[ℝ] Quaternion ℝ) := by
  by_cases hall : ∃ x : D, ∀ r : ℝ, x ≠ r • (1 : D)
  · right
    obtain ⟨i, hi⟩ := exists_sq_eq_neg_one hall
    by_cases hneg : ∀ y : D, i * y = -(y * i) → y = 0
    · left
      exact complex_case hi hneg
    · right
      push_neg at hneg
      obtain ⟨y, hy, hy0⟩ := hneg
      obtain ⟨j, hj, hij⟩ := exists_anticommuting hi hy0 hy
      refine quaternion_case hi hj hij ?_
      intro z
      obtain ⟨zp, zm, rfl, hp, hm⟩ := decomp hi z
      obtain ⟨a, b, hab⟩ := mem_span_of_commute hi hp
      have hw : (zm * j) * i = i * (zm * j) := by
        calc zm * j * i = zm * (j * i) := by rw [mul_assoc]
          _ = -(zm * (i * j)) := by rw [hij]; simp
          _ = -((zm * i) * j) := by rw [mul_assoc]
          _ = (i * zm) * j := by rw [hm]; simp
          _ = i * (zm * j) := by rw [mul_assoc]
      obtain ⟨a', b', hw'⟩ := mem_span_of_commute hi hw
      have hzm : zm = -((zm * j) * j) := by
        rw [mul_assoc, hj]; simp
      refine ⟨a, b, -a', -b', ?_⟩
      rw [hab]
      conv_lhs => rw [hzm, hw']
      simp only [add_mul, smul_mul_assoc, one_mul, mul_assoc, neg_smul]
      module
  · left
    push_neg at hall
    have hinj : Function.Injective (Algebra.ofId ℝ D) := (Algebra.ofId ℝ D : ℝ →+* D).injective
    have hsurj : Function.Surjective (Algebra.ofId ℝ D) := by
      intro x
      obtain ⟨r, hr⟩ := hall x
      exact ⟨r, by simp [hr, Algebra.algebraMap_eq_smul_one]⟩
    exact ⟨(AlgEquiv.ofBijective (Algebra.ofId ℝ D) ⟨hinj, hsurj⟩).symm⟩

end NumberFieldKB.WeilBNT.Frobenius
