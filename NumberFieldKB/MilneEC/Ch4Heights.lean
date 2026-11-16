import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import QuadFormsKB.Citation
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.Data.Int.Range
import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Milne, Elliptic Curves, Chapter IV: introduction and §4 (heights; the finite basis theorem)

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, the introduction and
Section 4 ("Heights; completion of the proof of the finite basis theorem").  Locators give the pdf page of the
text `ectext6` (printed page = pdf page − 8).

Conventions and deviations.
* Milne works with $E : Y^2Z = X^3 + aXZ^2 + bZ^3$ over $\mathbb{Q}$ and says (Remark 4.12) that everything
  extends to number fields with the product-formula height.  Here the results are stated for a Weierstrass
  curve `W` (general Weierstrass equation, Mathlib's `WeierstrassCurve.Affine`) over a field `K` with an
  admissible family of absolute values (`Height.AdmissibleAbsValues K`: number fields, and `ℚ`), with the
  Northcott property where finiteness is needed; this contains Milne's case.
* Milne's height of a point of $E(\mathbb{Q})$ (pdf p. 128) is $H(P) = H((x : z))$, $H(O) = 1$, and
  $h = \log H$.  This is Mathlib's `WeierstrassCurve.Affine.Point.naiveHeight` (the logarithmic height of
  `xRep P`, which is `![x, 1]` for an affine point and `![1, 0]` for the point at infinity); see
  `naiveHeight_some_rat` and `naiveHeight_zero`.
* Points of $\mathbb{P}^n$ are represented by nonzero vectors; Mathlib's heights of vectors are invariant under
  scaling (`remark_4_12`).
-/

open WeierstrassCurve WeierstrassCurve.Affine Height Filter Topology

namespace NumberFieldKB.MilneEC

/-! ## Heights on projective space over `ℚ` -/

/-- Milne's height of a point of $\mathbb{P}^n(\mathbb{Q})$ (pdf p. 125): for a primitive representative
$(a_0, \dots, a_n)$ (integers with greatest common divisor 1), $H(P) = \max_i |a_i|$.  Mathlib's
multiplicative height (defined by the product formula, Remark 4.12) agrees with it
(Mathlib: `Rat.mulHeight_eq_max_abs_of_gcd_eq_one`). -/
@[kb "milne2006ec" "Ch. IV, §4, definition of the height H(P) of a point of P^n(Q), pdf p. 125"]
theorem mulHeight_rat_eq_max_abs {n : ℕ} (a : Fin (n + 1) → ℤ) (ha : Finset.univ.gcd a = 1) :
    mulHeight (((↑) : ℤ → ℚ) ∘ a) = ⨆ i, |a i| :=
  Rat.mulHeight_eq_max_abs_of_gcd_eq_one ha

/-- **Remark 4.12** (pdf p. 133), the part used: the product-formula height of a point of $\mathbb{P}^n(K)$ does
not depend on the representative (Mathlib: `Height.mulHeight_smul_eq_mulHeight`).  The remark's other claim
(that all results of §4 extend to number fields) is realized by the statements of this file, which are made
over every field with an admissible family of absolute values. -/
@[kb "milne2006ec" "Ch. IV, Remark 4.12, pdf p. 133"]
theorem remark_4_12 {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Finite ι]
    (x : ι → K) {c : K} (hc : c ≠ 0) : mulHeight (c • x) = mulHeight x :=
  mulHeight_smul_eq_mulHeight x hc

/-- The homogeneous component of degree $n + m$ of $aF$, for $F$ homogeneous of degree $m$, is the
homogeneous component of degree $n$ of $a$ times $F$. -/
theorem homogeneousComponent_mul_of_isHomogeneous {K σ : Type*} [Field K] {m : ℕ} {F : MvPolynomial σ K}
    (hF : F.IsHomogeneous m) (a : MvPolynomial σ K) (n : ℕ) :
    MvPolynomial.homogeneousComponent (n + m) (a * F)
      = MvPolynomial.homogeneousComponent n a * F := by
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent a]
  rw [Finset.sum_mul, map_sum]
  have hoff : ∀ i, i ≠ n → MvPolynomial.homogeneousComponent (n + m)
      (MvPolynomial.homogeneousComponent i a * F) = 0 := by
    intro i hi
    have hh : (MvPolynomial.homogeneousComponent i a * F).IsHomogeneous (i + m) :=
      (MvPolynomial.homogeneousComponent_isHomogeneous i a).mul hF
    rw [MvPolynomial.homogeneousComponent_of_mem
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr hh)]
    split_ifs with h
    · omega
    · rfl
  by_cases hn : n ∈ Finset.range (a.totalDegree + 1)
  · rw [Finset.sum_eq_single n (fun i _ hi => hoff i hi) (fun h => absurd hn h)]
    exact MvPolynomial.homogeneousComponent_eq_self
      ((MvPolynomial.homogeneousComponent_isHomogeneous n a).mul hF)
  · rw [Finset.sum_eq_zero (fun i hi => hoff i (fun h => hn (h ▸ hi))),
      MvPolynomial.homogeneousComponent_eq_zero _ _ (by simpa using hn), zero_mul]

/-- **Proposition 4.1** (pdf p. 126).  Let $F, G$ be homogeneous of degree $m$ in two variables without a
common zero in $\mathbb{P}^1(K^{\mathrm{al}})$.  Then there is a constant $B$ with
$|h(\varphi(P)) - m\,h(P)| \le B$ for all $P \in \mathbb{P}^1(K)$, where $\varphi(P) = (F(P) : G(P))$.
Milne states it for $K = \mathbb{Q}$; points of $\mathbb{P}^1(K)$ are given by nonzero vectors. -/
@[kb "milne2006ec" "Ch. IV, Prop. 4.1, pdf p. 126"]
theorem prop_4_1 {K : Type*} [Field K] [AdmissibleAbsValues K] {m : ℕ}
    {F G : MvPolynomial (Fin 2) K} (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous m)
    (hFG : ∀ x : Fin 2 → AlgebraicClosure K, x ≠ 0 →
      ¬ (MvPolynomial.aeval x F = 0 ∧ MvPolynomial.aeval x G = 0)) :
    ∃ B : ℝ, ∀ x : Fin 2 → K, x ≠ 0 →
      |logHeight ![F.eval x, G.eval x] - m * logHeight x| ≤ B := by
  classical
  let I : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {F, G}
  have hrad : ∀ i : Fin 2, ∃ c, (MvPolynomial.X i : MvPolynomial (Fin 2) K) ^ c ∈ I := by
    intro i
    have : (MvPolynomial.X i : MvPolynomial (Fin 2) K) ∈
        MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus (AlgebraicClosure K) I) := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro x hx
      have hx0 : x = 0 := by
        by_contra hne
        exact hFG x hne ⟨hx F (Ideal.subset_span (by simp)), hx G (Ideal.subset_span (by simp))⟩
      simp [hx0]
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at this
    exact this
  obtain ⟨c0, hc0⟩ := hrad 0
  obtain ⟨c1, hc1⟩ := hrad 1
  have hX : ∀ i : Fin 2, ∃ a b : MvPolynomial (Fin 2) K,
      a * F + b * G = (MvPolynomial.X i) ^ ((c0 + c1) + m) := by
    intro i
    have hmem : (MvPolynomial.X i : MvPolynomial (Fin 2) K) ^ ((c0 + c1) + m) ∈ I := by
      fin_cases i
      · have : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ ((c0 + c1) + m)
            = MvPolynomial.X 0 ^ (c1 + m) * MvPolynomial.X 0 ^ c0 := by
          rw [← pow_add]; congr 1; omega
        simp only [Fin.zero_eta]
        rw [this]
        exact I.mul_mem_left _ hc0
      · have : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ ((c0 + c1) + m)
            = MvPolynomial.X 1 ^ (c0 + m) * MvPolynomial.X 1 ^ c1 := by
          rw [← pow_add]; congr 1; omega
        simp only [Fin.mk_one]
        rw [this]
        exact I.mul_mem_left _ hc1
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
    exact ⟨a, b, hab⟩
  choose a b hab using hX
  set M := c0 + c1 with hM
  let q : Fin 2 × Fin 2 → MvPolynomial (Fin 2) K :=
    fun kj => MvPolynomial.homogeneousComponent M (![a kj.1, b kj.1] kj.2)
  have hq : ∀ kj, (q kj).IsHomogeneous M := fun kj =>
    MvPolynomial.homogeneousComponent_isHomogeneous _ _
  let p : Fin 2 → MvPolynomial (Fin 2) K := ![F, G]
  have hp : ∀ i, (p i).IsHomogeneous m := by
    intro i; fin_cases i
    · exact hF
    · exact hG
  have hpoly : ∀ k, q (k, 0) * F + q (k, 1) * G = MvPolynomial.X k ^ (M + m) := by
    intro k
    have h1 := congrArg (MvPolynomial.homogeneousComponent (M + m)) (hab k)
    rw [map_add, homogeneousComponent_mul_of_isHomogeneous hF, homogeneousComponent_mul_of_isHomogeneous hG,
      MvPolynomial.homogeneousComponent_eq_self (MvPolynomial.isHomogeneous_X_pow k (M + m))] at h1
    exact h1
  have hid : ∀ (x : Fin 2 → K) (k : Fin 2),
      ∑ j, (q (k, j)).eval x * (p j).eval x = (x k) ^ (M + m) := by
    intro x k
    have := congrArg (MvPolynomial.eval x) (hpoly k)
    simp only [map_add, map_mul, MvPolynomial.eval_X, map_pow] at this
    rw [Fin.sum_univ_two]
    exact this
  obtain ⟨C₁, hC₁⟩ := logHeight_eval_le' (N := m) hp
  obtain ⟨C₂, hC₂⟩ := logHeight_eval_ge' (M := M) (N := m) hq
  refine ⟨max C₁ (-C₂), fun x _ => ?_⟩
  have e : (fun j => (p j).eval x) = ![F.eval x, G.eval x] := by
    funext j; fin_cases j <;> rfl
  have u := hC₁ x
  have l := hC₂ p (x := x) (hid x)
  rw [e] at u l
  rw [abs_le]
  constructor
  · have := le_max_right C₁ (-C₂)
    linarith
  · have := le_max_left C₁ (-C₂)
    linarith


/-- The gcd of a pair of integers, as a gcd over `Fin 2`. -/
theorem gcd_fin_two (a b : ℤ) (h : Int.gcd a b = 1) : Finset.univ.gcd ![a, b] = 1 := by
  simp [Finset.univ_fin2, ← Int.coe_gcd]
  rcases Int.associated_iff.mp (normalize_associated b) with h' | h' <;> simpa [h'] using h

/-- Every nonzero vector of $\mathbb{Q}^2$ is a nonzero rational multiple of a primitive integer vector. -/
theorem prim_rep (x : Fin 2 → ℚ) (hx : x ≠ 0) :
    ∃ (s : ℚ) (y : Fin 2 → ℤ), s ≠ 0 ∧ x = s • (((↑) : ℤ → ℚ) ∘ y) ∧
      IsCoprime (y 0) (y 1) := by
  have hd0 : ((x 0).den : ℚ) ≠ 0 := by exact_mod_cast (x 0).den_nz
  have hd1 : ((x 1).den : ℚ) ≠ 0 := by exact_mod_cast (x 1).den_nz
  set u0 : ℤ := (x 0).num * (x 1).den with hu0
  set u1 : ℤ := (x 1).num * (x 0).den with hu1
  set D : ℚ := ((x 0).den : ℚ) * (x 1).den with hD
  have hD0 : D ≠ 0 := mul_ne_zero hd0 hd1
  have e0 : D * x 0 = u0 := by
    have := Rat.mul_den_eq_num (x 0)
    rw [hD, hu0]; push_cast
    rw [← this]; ring
  have e1 : D * x 1 = u1 := by
    have := Rat.mul_den_eq_num (x 1)
    rw [hD, hu1]; push_cast
    rw [← this]; ring
  have hne : u0 ≠ 0 ∨ u1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    fin_cases i
    · have : D * x 0 = 0 := by rw [e0]; exact_mod_cast h.1
      simpa [hD0] using this
    · have : D * x 1 = 0 := by rw [e1]; exact_mod_cast h.2
      simpa [hD0] using this
  have hg : 0 < Int.gcd u0 u1 := Int.gcd_pos_iff.mpr hne
  obtain ⟨g, m', n', hg0, hmn, h0, h1⟩ := Int.exists_gcd_one' hg
  refine ⟨(g : ℚ) / D, ![m', n'], div_ne_zero (by exact_mod_cast hg0.ne') hD0, ?_,
    Int.isCoprime_iff_gcd_eq_one.mpr hmn⟩
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Pi.smul_apply, Function.comp_apply, Matrix.cons_val_zero,
      smul_eq_mul]
    have : (u0 : ℚ) = m' * g := by exact_mod_cast h0
    field_simp
    linear_combination e0 + this
  · simp only [Fin.mk_one, Pi.smul_apply, Function.comp_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, smul_eq_mul]
    have : (u1 : ℚ) = n' * g := by exact_mod_cast h1
    field_simp
    linear_combination e1 + this

/-- If $(a, b)$ and $(c, d)$ are coprime pairs then $(ac, ad + bc, bd)$ is a primitive vector. -/
theorem gcd_three (a b c d : ℤ) (h1 : IsCoprime a b) (h2 : IsCoprime c d) :
    Finset.univ.gcd ![a * c, a * d + b * c, b * d] = 1 := by
  obtain ⟨u, v, huv⟩ := h1
  obtain ⟨s, t, hst⟩ := h2
  set g := Finset.univ.gcd ![a * c, a * d + b * c, b * d] with hg
  have d1 : g ∣ a * c := Finset.gcd_dvd (f := ![a * c, a * d + b * c, b * d]) (Finset.mem_univ 0)
  have d2 : g ∣ a * d + b * c :=
    Finset.gcd_dvd (f := ![a * c, a * d + b * c, b * d]) (Finset.mem_univ 1)
  have d3 : g ∣ b * d := Finset.gcd_dvd (f := ![a * c, a * d + b * c, b * d]) (Finset.mem_univ 2)
  have m1 : g ∣ a ^ 2 * c ^ 2 := by
    have : a ^ 2 * c ^ 2 = (a * c) * (a * c) := by ring
    rw [this]; exact d1.mul_right _
  have m2 : g ∣ a ^ 2 * (c * d) := by
    have : a ^ 2 * (c * d) = (a * c) * (a * d) := by ring
    rw [this]; exact d1.mul_right _
  have m3 : g ∣ a ^ 2 * d ^ 2 := by
    have : a ^ 2 * d ^ 2 = (a * d) * (a * d + b * c) - (a * c) * (b * d) := by ring
    rw [this]; exact dvd_sub (d2.mul_left _) (d1.mul_right _)
  have m4 : g ∣ (a * b) * c ^ 2 := by
    have : (a * b) * c ^ 2 = (a * c) * (b * c) := by ring
    rw [this]; exact d1.mul_right _
  have m5 : g ∣ (a * b) * (c * d) := by
    have : (a * b) * (c * d) = (a * c) * (b * d) := by ring
    rw [this]; exact d1.mul_right _
  have m6 : g ∣ (a * b) * d ^ 2 := by
    have : (a * b) * d ^ 2 = (b * d) * (a * d) := by ring
    rw [this]; exact d3.mul_right _
  have m7 : g ∣ b ^ 2 * c ^ 2 := by
    have : b ^ 2 * c ^ 2 = (b * c) * (a * d + b * c) - (a * c) * (b * d) := by ring
    rw [this]; exact dvd_sub (d2.mul_left _) (d1.mul_right _)
  have m8 : g ∣ b ^ 2 * (c * d) := by
    have : b ^ 2 * (c * d) = (b * d) * (b * c) := by ring
    rw [this]; exact d3.mul_right _
  have m9 : g ∣ b ^ 2 * d ^ 2 := by
    have : b ^ 2 * d ^ 2 = (b * d) * (b * d) := by ring
    rw [this]; exact d3.mul_right _
  have key : (1 : ℤ) = u^2*s^2*(a^2*c^2) + 2*u^2*s*t*(a^2*(c*d)) + u^2*t^2*(a^2*d^2)
      + 2*u*v*s^2*((a*b)*c^2) + 4*u*v*s*t*((a*b)*(c*d)) + 2*u*v*t^2*((a*b)*d^2)
      + v^2*s^2*(b^2*c^2) + 2*v^2*s*t*(b^2*(c*d)) + v^2*t^2*(b^2*d^2) := by
    have h1 : (u*a+v*b)^2*(s*c+t*d)^2 = 1 := by rw [huv, hst]; norm_num
    rw [← h1]; ring
  have hdvd : g ∣ 1 := by
    rw [key]
    repeat' apply dvd_add
    all_goals (apply Dvd.dvd.mul_left; assumption)
  have hu : IsUnit g := isUnit_of_dvd_one hdvd
  have hn : normalize g = g := Finset.normalize_gcd
  rw [← hn]
  exact normalize_eq_one.mpr hu

/-- Supremum over `Fin 2` of integers. -/
theorem iSup_fin_two_int (f : Fin 2 → ℤ) : ⨆ i, f i = max (f 0) (f 1) := by
  apply le_antisymm
  · exact ciSup_le fun i => by fin_cases i <;> simp
  · exact max_le (le_ciSup (Finite.bddAbove_range f) 0) (le_ciSup (Finite.bddAbove_range f) 1)

/-- Supremum over `Fin 3` of integers. -/
theorem iSup_fin_three_int (f : Fin 3 → ℤ) : ⨆ i, f i = max (max (f 0) (f 1)) (f 2) := by
  apply le_antisymm
  · exact ciSup_le fun i => by fin_cases i <;> simp
  · exact max_le (max_le (le_ciSup (Finite.bddAbove_range f) 0)
      (le_ciSup (Finite.bddAbove_range f) 1)) (le_ciSup (Finite.bddAbove_range f) 2)

/-- Key estimate for Lemma 4.2: $|ad| \le 2M$ when $M$ bounds the three coordinates $ac$,
$ad + bc$, $bd$. -/
theorem key_ineq (a b c d M : ℤ) (h1 : |a * c| ≤ M) (h2 : |a * d + b * c| ≤ M)
    (h3 : |b * d| ≤ M) : |a * d| ≤ 2 * M := by
  by_contra h
  push Not at h
  have hM : 0 ≤ M := (abs_nonneg _).trans h1
  have hbc : M < |b * c| := by
    have e : |a * d| ≤ |a * d + b * c| + |b * c| := by
      calc |a * d| = |(a * d + b * c) - b * c| := by ring_nf
        _ ≤ |a * d + b * c| + |b * c| := abs_sub _ _
    linarith
  have hpq : |a * c| * |b * d| ≤ M * M :=
    mul_le_mul h1 h3 (abs_nonneg _) hM
  have heq : |a * c| * |b * d| = |a * d| * |b * c| := by
    rw [← abs_mul, ← abs_mul]; congr 1; ring
  have hlt : M * M < |a * d| * |b * c| :=
    mul_lt_mul'' (by linarith) hbc hM hM
  linarith

/-- Lower estimate in Lemma 4.2, for integers. -/
theorem ineq_lower (a b c d : ℤ) :
    max |a| |b| * max |c| |d| ≤ 2 * max (max |a * c| |a * d + b * c|) |b * d| := by
  set M := max (max |a * c| |a * d + b * c|) |b * d| with hM
  have h1 : |a * c| ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have h2 : |a * d + b * c| ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have h3 : |b * d| ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := (abs_nonneg _).trans h1
  have k1 : |a * d| ≤ 2 * M := key_ineq a b c d M h1 h2 h3
  have k2 : |b * c| ≤ 2 * M :=
    key_ineq b a d c M h3 (by rwa [add_comm]) h1
  have p1 : |a| * |c| ≤ 2 * M := by rw [← abs_mul]; omega
  have p2 : |a| * |d| ≤ 2 * M := by rw [← abs_mul]; exact k1
  have p3 : |b| * |c| ≤ 2 * M := by rw [← abs_mul]; exact k2
  have p4 : |b| * |d| ≤ 2 * M := by rw [← abs_mul]; omega
  rcases max_cases |a| |b| with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
    rcases max_cases |c| |d| with ⟨e2, _⟩ | ⟨e2, _⟩ <;> rw [e1, e2] <;> assumption

/-- Upper estimate in Lemma 4.2, for integers. -/
theorem ineq_upper (a b c d : ℤ) :
    max (max |a * c| |a * d + b * c|) |b * d| ≤ 2 * (max |a| |b| * max |c| |d|) := by
  have ha : |a| ≤ max |a| |b| := le_max_left _ _
  have hb : |b| ≤ max |a| |b| := le_max_right _ _
  have hc : |c| ≤ max |c| |d| := le_max_left _ _
  have hd : |d| ≤ max |c| |d| := le_max_right _ _
  have hA : 0 ≤ max |a| |b| := (abs_nonneg _).trans ha
  have hC : 0 ≤ max |c| |d| := (abs_nonneg _).trans hc
  refine max_le (max_le ?_ ?_) ?_
  · rw [abs_mul]; nlinarith [mul_le_mul ha hc (abs_nonneg _) hA, abs_nonneg a, abs_nonneg c]
  · calc |a * d + b * c| ≤ |a * d| + |b * c| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul]
        nlinarith [mul_le_mul ha hd (abs_nonneg _) hA, mul_le_mul hb hc (abs_nonneg _) hA]
  · rw [abs_mul]; nlinarith [mul_le_mul hb hd (abs_nonneg _) hA, abs_nonneg b, abs_nonneg d]

/-- **Lemma 4.2** (pdf p. 127).  For $P = (a : b)$ and $Q = (c : d)$ in $\mathbb{P}^1(\mathbb{Q})$ let
$R = (ac : ad + bc : bd)$ be their image under the Veronese map.  Then
$\tfrac12 \le H(R)/(H(P)H(Q)) \le 2$. -/
@[kb "milne2006ec" "Ch. IV, Lemma 4.2, pdf p. 127"]
theorem lemma_4_2 (P Q : Fin 2 → ℚ) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    1 / 2 * (mulHeight P * mulHeight Q) ≤
        mulHeight ![P 0 * Q 0, P 0 * Q 1 + P 1 * Q 0, P 1 * Q 1] ∧
      mulHeight ![P 0 * Q 0, P 0 * Q 1 + P 1 * Q 0, P 1 * Q 1] ≤ 2 * (mulHeight P * mulHeight Q) := by
  obtain ⟨s, y, hs, hPy, hy⟩ := prim_rep P hP
  obtain ⟨t, z, ht, hQz, hz⟩ := prim_rep Q hQ
  have hyg : Finset.univ.gcd y = 1 := by
    have : y = ![y 0, y 1] := by funext i; fin_cases i <;> rfl
    rw [this]; exact gcd_fin_two _ _ (Int.isCoprime_iff_gcd_eq_one.mp hy)
  have hzg : Finset.univ.gcd z = 1 := by
    have : z = ![z 0, z 1] := by funext i; fin_cases i <;> rfl
    rw [this]; exact gcd_fin_two _ _ (Int.isCoprime_iff_gcd_eq_one.mp hz)
  have hwg := gcd_three (y 0) (y 1) (z 0) (z 1) hy hz
  have hHP : mulHeight P = ((max |y 0| |y 1| : ℤ) : ℝ) := by
    rw [hPy, mulHeight_smul_eq_mulHeight _ hs, Rat.mulHeight_eq_max_abs_of_gcd_eq_one hyg,
      iSup_fin_two_int]
  have hHQ : mulHeight Q = ((max |z 0| |z 1| : ℤ) : ℝ) := by
    rw [hQz, mulHeight_smul_eq_mulHeight _ ht, Rat.mulHeight_eq_max_abs_of_gcd_eq_one hzg,
      iSup_fin_two_int]
  have hR : ![P 0 * Q 0, P 0 * Q 1 + P 1 * Q 0, P 1 * Q 1]
      = (s * t) • (((↑) : ℤ → ℚ) ∘ ![y 0 * z 0, y 0 * z 1 + y 1 * z 0, y 1 * z 1]) := by
    have e0 : P 0 = s * y 0 := congrFun hPy 0
    have e1 : P 1 = s * y 1 := congrFun hPy 1
    have f0 : Q 0 = t * z 0 := congrFun hQz 0
    have f1 : Q 1 = t * z 1 := congrFun hQz 1
    funext i
    fin_cases i
    · simp [e0, f0]; ring
    · simp [e0, e1, f0, f1]; ring
    · simp [e1, f1]; ring
  have hHR : mulHeight ![P 0 * Q 0, P 0 * Q 1 + P 1 * Q 0, P 1 * Q 1]
      = ((max (max |y 0 * z 0| |y 0 * z 1 + y 1 * z 0|) |y 1 * z 1| : ℤ) : ℝ) := by
    rw [hR, mulHeight_smul_eq_mulHeight _ (mul_ne_zero hs ht),
      Rat.mulHeight_eq_max_abs_of_gcd_eq_one hwg, iSup_fin_three_int]
    simp
  rw [hHP, hHQ, hHR]
  have lo := ineq_lower (y 0) (y 1) (z 0) (z 1)
  have up := ineq_upper (y 0) (y 1) (z 0) (z 1)
  have lo' : (((max |y 0| |y 1| * max |z 0| |z 1| : ℤ)) : ℝ) ≤
      ((2 * max (max |y 0 * z 0| |y 0 * z 1 + y 1 * z 0|) |y 1 * z 1| : ℤ) : ℝ) :=
    Int.cast_le.mpr lo
  have up' : ((max (max |y 0 * z 0| |y 0 * z 1 + y 1 * z 0|) |y 1 * z 1| : ℤ) : ℝ) ≤
      ((2 * (max |y 0| |y 1| * max |z 0| |z 1|) : ℤ) : ℝ) := Int.cast_le.mpr up
  push_cast at lo' up' ⊢
  constructor <;> linarith

/-! ## Heights on an elliptic curve -/

section Curve

variable {K : Type*} [Field K] [AdmissibleAbsValues K] (W : Affine K)

/-- Milne's height of the point at infinity (pdf p. 128): $H(O) = 1$, so $h(O) = 0$. -/
@[kb "milne2006ec" "Ch. IV, §4, definition of the height h(P) on E(Q), pdf p. 128"]
theorem naiveHeight_zero : (0 : W.Point).naiveHeight = 0 := by
  simp [Point.naiveHeight, Point.xRep_zero]

/-- Milne's height of an affine point $P = (x : y : 1)$ of $E(\mathbb{Q})$ (pdf p. 128):
$h(P) = \log H((x : 1)) = \log \max(|\mathrm{num}(x)|, \mathrm{den}(x))$.  So Milne's $h$ is Mathlib's
`Point.naiveHeight`. -/
@[kb "milne2006ec" "Ch. IV, §4, definition of the height h(P) on E(Q), pdf p. 128"]
theorem naiveHeight_some_rat {W : Affine ℚ} {x y : ℚ} (h : W.Nonsingular x y) :
    (Point.some x y h).naiveHeight = Real.log (max (x.num.natAbs : ℝ) (x.den : ℝ)) := by
  rw [Point.naiveHeight_eq_logHeight₁]
  simp [Point.xRep_some, Rat.logHeight₁_eq_log_max]

/-- **Lemma 4.3** (pdf p. 128).  For every constant $B$ only finitely many points of $E(K)$ have height
$h(P) < B$ (Mathlib: `WeierstrassCurve.Affine.finite_naiveHeight_le`, with $\le$). -/
@[kb "milne2006ec" "Ch. IV, Lemma 4.3, pdf p. 128"]
theorem lemma_4_3 [Northcott (logHeight₁ (K := K))] (B : ℝ) :
    {P : W.Point | P.naiveHeight < B}.Finite :=
  (finite_naiveHeight_le W B).subset fun P (hP : P.naiveHeight < B) => (le_of_lt hP : P.naiveHeight ≤ B)

variable [W.IsElliptic] [DecidableEq K]

/-- **Proposition 4.4** (pdf p. 128).  There is a constant $A$ with $|h(2P) - 4h(P)| \le A$ on $E(K)$.
(Proved here from Mathlib's approximate parallelogram law rather than from Proposition 4.1 and the duplication
formula.) -/
@[kb "milne2006ec" "Ch. IV, Prop. 4.4, pdf p. 128"]
theorem prop_4_4 : ∃ A : ℝ, ∀ P : W.Point, |(2 • P).naiveHeight - 4 * P.naiveHeight| ≤ A := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  refine ⟨C, fun P => ?_⟩
  have := hC P P
  rw [sub_self, naiveHeight_zero] at this
  have e : (2 • P).naiveHeight - 4 * P.naiveHeight
      = (P + P).naiveHeight + 0 - 2 * (P.naiveHeight + P.naiveHeight) := by
    rw [two_smul]; ring
  rw [e]; exact this

/-- A **Néron–Tate height function** (pdf p. 129): a function $\hat h : E(K) \to \mathbb{R}$ with
(a) $\hat h - h$ bounded on $E(K)$ and (b) $\hat h(2P) = 4\hat h(P)$. -/
@[kb "milne2006ec" "Ch. IV, §4, definition of a Néron-Tate height function, pdf p. 129"]
def IsNeronTateHeight (hh : W.Point → ℝ) : Prop :=
  (∃ B : ℝ, ∀ P : W.Point, |hh P - P.naiveHeight| ≤ B) ∧ ∀ P : W.Point, hh (2 • P) = 4 * hh P

/-- The multiple $2^{n+1}P$ is $2(2^nP)$. -/
theorem two_pow_succ_smul (P : W.Point) (n : ℕ) : (2 ^ (n + 1)) • P = 2 • ((2 ^ n) • P) := by
  rw [pow_succ', mul_smul]

/-- A function with $\hat h(2P) = 4\hat h(P)$ satisfies $\hat h(2^nP) = 4^n\hat h(P)$. -/
theorem doubling_pow_smul {hh : W.Point → ℝ} (H : ∀ P : W.Point, hh (2 • P) = 4 * hh P)
    (P : W.Point) (n : ℕ) : hh ((2 ^ n) • P) = 4 ^ n * hh P := by
  induction n with
  | zero => simp
  | succ n ih => rw [two_pow_succ_smul, H, ih, pow_succ]; ring

/-- **Proposition 4.5** (pdf p. 129), the formula from its proof: a function satisfying (a) and (b) is the limit
of $h(2^nP)/4^n$. -/
@[kb "milne2006ec" "Ch. IV, Prop. 4.5, pdf p. 129"]
theorem prop_4_5_tendsto {hh : W.Point → ℝ} (H : IsNeronTateHeight W hh) (P : W.Point) :
    Tendsto (fun n : ℕ => ((2 ^ n) • P).naiveHeight / 4 ^ n) atTop (𝓝 (hh P)) := by
  obtain ⟨⟨B, hB⟩, h2⟩ := H
  have h4 : ∀ n : ℕ, (0 : ℝ) < 4 ^ n := fun n => by positivity
  have hlim : Tendsto (fun n : ℕ => B * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num)
      (by norm_num)).const_mul B
    simpa using this
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hlim
  have := hB ((2 ^ n) • P)
  rw [doubling_pow_smul W h2 P n] at this
  rw [Real.dist_eq]
  have e : ((2 ^ n) • P).naiveHeight / 4 ^ n - hh P
      = -((hh ((2 ^ n) • P) - ((2 ^ n) • P).naiveHeight) / 4 ^ n) := by
    rw [doubling_pow_smul W h2 P n]; field_simp; ring
  rw [e, abs_neg, abs_div, abs_of_pos (h4 n), div_le_iff₀ (h4 n)]
  rw [doubling_pow_smul W h2 P n] at *
  have e2 : B * (1 / 4 : ℝ) ^ n * 4 ^ n = B := by
    rw [mul_assoc, ← mul_pow]; norm_num
  rw [e2]; exact this

/-- **Proposition 4.5** (pdf p. 129).  There is at most one function $\hat h : E(K) \to \mathbb{R}$ such that
(a) $\hat h - h$ is bounded and (b) $\hat h(2P) = 4 \hat h(P)$. -/
@[kb "milne2006ec" "Ch. IV, Prop. 4.5, pdf p. 129"]
theorem prop_4_5 {h₁ h₂ : W.Point → ℝ} (H₁ : IsNeronTateHeight W h₁) (H₂ : IsNeronTateHeight W h₂) :
    h₁ = h₂ := by
  funext P
  exact tendsto_nhds_unique (prop_4_5_tendsto W H₁ P) (prop_4_5_tendsto W H₂ P)

/-- One doubling step of the sequence $h(2^nP)/4^n$ moves it by at most $(A/4)\,4^{-n}$. -/
theorem step_bound {A : ℝ} (hA : ∀ P : W.Point, |(2 • P).naiveHeight - 4 * P.naiveHeight| ≤ A)
    (P : W.Point) (n : ℕ) :
    |((2 ^ (n + 1)) • P).naiveHeight / 4 ^ (n + 1) - ((2 ^ n) • P).naiveHeight / 4 ^ n|
      ≤ A / 4 * (1 / 4 : ℝ) ^ n := by
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have := hA ((2 ^ n) • P)
  rw [← two_pow_succ_smul] at this
  have e : ((2 ^ (n + 1)) • P).naiveHeight / 4 ^ (n + 1) - ((2 ^ n) • P).naiveHeight / 4 ^ n
      = (((2 ^ (n + 1)) • P).naiveHeight - 4 * ((2 ^ n) • P).naiveHeight) / 4 ^ (n + 1) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ (n + 1)), div_le_iff₀ (by positivity)]
  have e2 : A / 4 * (1 / 4 : ℝ) ^ n * 4 ^ (n + 1) = A := by
    rw [pow_succ, one_div, inv_pow]; field_simp
  rw [e2]; exact this

/-- **Lemma 4.6** (pdf p. 129).  For every $P \in E(K)$ the sequence $h(2^nP)/4^n$ is Cauchy. -/
@[kb "milne2006ec" "Ch. IV, Lemma 4.6, pdf p. 129"]
theorem lemma_4_6 (P : W.Point) :
    CauchySeq fun n : ℕ => ((2 ^ n) • P).naiveHeight / 4 ^ n := by
  obtain ⟨A, hA⟩ := prop_4_4 W
  refine cauchySeq_of_le_geometric (1 / 4 : ℝ) (A / 4) (by norm_num) fun n => ?_
  rw [Real.dist_eq, abs_sub_comm]
  exact step_bound W hA P n

/-- Telescoped bound: every term $h(2^nP)/4^n$ is within $A/3$ of the first term $h(P)$. -/
theorem telescoped_bound {A : ℝ}
    (hA : ∀ P : W.Point, |(2 • P).naiveHeight - 4 * P.naiveHeight| ≤ A)
    (P : W.Point) (n : ℕ) :
    |((2 ^ n) • P).naiveHeight / 4 ^ n - P.naiveHeight| ≤ A / 3 := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have key : ∀ n : ℕ, |((2 ^ n) • P).naiveHeight / 4 ^ n - P.naiveHeight|
      ≤ A / 3 * (1 - (1 / 4 : ℝ) ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := step_bound W hA P n
      have hx : (1 / 4 : ℝ) ^ (n + 1) = (1 / 4 : ℝ) ^ n / 4 := by rw [pow_succ]; ring
      have := abs_sub_le (((2 ^ (n + 1)) • P).naiveHeight / 4 ^ (n + 1))
        (((2 ^ n) • P).naiveHeight / 4 ^ n) P.naiveHeight
      rw [hx]
      nlinarith
  refine (key n).trans ?_
  have : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
  nlinarith

/-- The **canonical (Néron–Tate) height** (pdf p. 130): $\hat h(P) = \lim_n h(2^nP)/4^n$. -/
@[kb "milne2006ec" "Ch. IV, §4, definition of the canonical height, pdf p. 130"]
noncomputable def canonicalHeight (P : W.Point) : ℝ :=
  limUnder atTop fun n : ℕ => ((2 ^ n) • P).naiveHeight / 4 ^ n

/-- The defining limit of the canonical height (Lemma 4.6). -/
theorem tendsto_canonicalHeight (P : W.Point) :
    Tendsto (fun n : ℕ => ((2 ^ n) • P).naiveHeight / 4 ^ n) atTop (𝓝 (canonicalHeight W P)) :=
  (lemma_4_6 W P).tendsto_limUnder

/-- The canonical height differs from the naive height by a bounded amount. -/
theorem canonicalHeight_sub_le :
    ∃ B : ℝ, ∀ P : W.Point, |canonicalHeight W P - P.naiveHeight| ≤ B := by
  obtain ⟨A, hA⟩ := prop_4_4 W
  refine ⟨A / 3, fun P => ?_⟩
  have ht : Tendsto (fun n : ℕ => |((2 ^ n) • P).naiveHeight / 4 ^ n - P.naiveHeight|) atTop
      (𝓝 |canonicalHeight W P - P.naiveHeight|) :=
    ((tendsto_canonicalHeight W P).sub tendsto_const_nhds).abs
  exact le_of_tendsto' ht fun n => telescoped_bound W hA P n

/-- The canonical height is multiplied by $4$ under doubling. -/
theorem canonicalHeight_two_smul (P : W.Point) :
    canonicalHeight W (2 • P) = 4 * canonicalHeight W P := by
  have h1 : Tendsto (fun n : ℕ => 4 * (((2 ^ (n + 1)) • P).naiveHeight / 4 ^ (n + 1))) atTop
      (𝓝 (4 * canonicalHeight W P)) :=
    ((tendsto_canonicalHeight W P).comp (tendsto_add_atTop_nat 1)).const_mul 4
  refine tendsto_nhds_unique (tendsto_canonicalHeight W (2 • P)) (h1.congr fun n => ?_)
  rw [pow_succ', mul_smul, pow_succ]
  field_simp
  rw [smul_comm]

/-- The canonical height of $2^nP$ is $4^n\hat h(P)$. -/
theorem canonicalHeight_two_pow_smul (P : W.Point) (n : ℕ) :
    canonicalHeight W ((2 ^ n) • P) = 4 ^ n * canonicalHeight W P :=
  doubling_pow_smul W (canonicalHeight_two_smul W) P n

/-- **Theorem 4.7** (pdf p. 130), first assertion: $\hat h$ is a Néron–Tate height function. -/
@[kb "milne2006ec" "Ch. IV, Thm. 4.7, pdf p. 130"]
theorem thm_4_7 : IsNeronTateHeight W (canonicalHeight W) :=
  ⟨canonicalHeight_sub_le W, canonicalHeight_two_smul W⟩

/-- **Theorem 4.7 (a)** (pdf p. 130): for every constant $C$ the set of $P$ with $\hat h(P) \le C$ is finite.
(Milne writes "for any $C \ge 0$"; the statement for all real $C$ is the same.) -/
@[kb "milne2006ec" "Ch. IV, Thm. 4.7 (a), pdf p. 130"]
theorem thm_4_7_a [Northcott (logHeight₁ (K := K))] (C : ℝ) :
    {P : W.Point | canonicalHeight W P ≤ C}.Finite := by
  obtain ⟨B, hB⟩ := canonicalHeight_sub_le W
  refine (finite_naiveHeight_le W (C + B)).subset fun P hP => ?_
  have := (abs_le.mp (hB P)).1
  have hP : canonicalHeight W P ≤ C := hP
  show P.naiveHeight ≤ C + B
  linarith

/-- **Theorem 4.7 (b)** (pdf p. 130), first half: $\hat h(P) \ge 0$. -/
@[kb "milne2006ec" "Ch. IV, Thm. 4.7 (b), pdf p. 130"]
theorem canonicalHeight_nonneg (P : W.Point) : 0 ≤ canonicalHeight W P :=
  ge_of_tendsto' (tendsto_canonicalHeight W P) fun n =>
    div_nonneg (Height.logHeight_nonneg _) (by positivity)

/-- The parallelogram law for the canonical height (proof of Lemma 4.11, placed early so that Theorem 4.7 (b)
can use it): apply the approximate law to $2^nP$, $2^nQ$, divide by $4^n$, and let $n \to \infty$. -/
theorem canonicalHeight_parallelogram (P Q : W.Point) :
    canonicalHeight W (P + Q) + canonicalHeight W (P - Q) =
      2 * canonicalHeight W P + 2 * canonicalHeight W Q := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  have hlim : Tendsto (fun n : ℕ => C * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num)
      (by norm_num)).const_mul C
    simpa using this
  have h1 : Tendsto (fun n : ℕ =>
      ((2 ^ n) • (P + Q)).naiveHeight / 4 ^ n + ((2 ^ n) • (P - Q)).naiveHeight / 4 ^ n
        - 2 * (((2 ^ n) • P).naiveHeight / 4 ^ n + ((2 ^ n) • Q).naiveHeight / 4 ^ n)) atTop
      (𝓝 (canonicalHeight W (P + Q) + canonicalHeight W (P - Q)
        - 2 * (canonicalHeight W P + canonicalHeight W Q))) :=
    (((tendsto_canonicalHeight W (P + Q)).add (tendsto_canonicalHeight W (P - Q))).sub
      (((tendsto_canonicalHeight W P).add (tendsto_canonicalHeight W Q)).const_mul 2))
  have h2 : Tendsto (fun n : ℕ =>
      ((2 ^ n) • (P + Q)).naiveHeight / 4 ^ n + ((2 ^ n) • (P - Q)).naiveHeight / 4 ^ n
        - 2 * (((2 ^ n) • P).naiveHeight / 4 ^ n + ((2 ^ n) • Q).naiveHeight / 4 ^ n)) atTop
      (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) hlim
    have := hC ((2 ^ n) • P) ((2 ^ n) • Q)
    rw [← smul_add, ← smul_sub] at this
    have h4 : (0 : ℝ) < 4 ^ n := by positivity
    have e : ((2 ^ n) • (P + Q)).naiveHeight / 4 ^ n + ((2 ^ n) • (P - Q)).naiveHeight / 4 ^ n
        - 2 * (((2 ^ n) • P).naiveHeight / 4 ^ n + ((2 ^ n) • Q).naiveHeight / 4 ^ n)
        = (((2 ^ n) • (P + Q)).naiveHeight + ((2 ^ n) • (P - Q)).naiveHeight
          - 2 * (((2 ^ n) • P).naiveHeight + ((2 ^ n) • Q).naiveHeight)) / 4 ^ n := by
      field_simp
    dsimp only [Function.comp_apply]
    rw [e, abs_div, abs_of_pos h4, div_le_iff₀ h4]
    have e2 : C * (1 / 4 : ℝ) ^ n * 4 ^ n = C := by
      rw [mul_assoc, ← mul_pow]; norm_num
    rw [e2]; exact this
  have := tendsto_nhds_unique h1 h2
  linarith

/-- The canonical height of the origin is zero. -/
theorem canonicalHeight_zero : canonicalHeight W 0 = 0 := by
  have := canonicalHeight_two_smul W (0 : W.Point)
  rw [smul_zero] at this
  linarith

/-- **Theorem 4.7 (b)** (pdf p. 130): $\hat h(P) = 0$ if and only if $P$ has finite order. -/
@[kb "milne2006ec" "Ch. IV, Thm. 4.7 (b), pdf p. 130"]
theorem thm_4_7_b [Northcott (logHeight₁ (K := K))] (P : W.Point) :
    canonicalHeight W P = 0 ↔ IsOfFinAddOrder P := by
  constructor
  · intro h0
    have key : ∀ n : ℕ, canonicalHeight W (n • P) = 0 ∧ canonicalHeight W ((n + 1) • P) = 0 := by
      intro n
      induction n with
      | zero => simp [canonicalHeight_zero, h0]
      | succ n ih =>
        refine ⟨ih.2, ?_⟩
        have := canonicalHeight_parallelogram W ((n + 1) • P) P
        have e1 : (n + 1) • P + P = (n + 1 + 1) • P := (succ_nsmul P (n + 1)).symm
        have e2 : (n + 1) • P - P = n • P := by rw [succ_nsmul, add_sub_cancel_right]
        rw [e1, e2, ih.1, ih.2, h0] at this
        linarith
    have hfin : {Q : W.Point | canonicalHeight W Q ≤ 0}.Finite := thm_4_7_a W 0
    obtain ⟨a, b, hab, hE⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
      (f := fun n : ℕ => n • P) (fun n => (le_of_eq (key n).1 : canonicalHeight W (n • P) ≤ 0))
      hfin
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨b - a, by omega, ?_⟩
    have : (b - a) • P + a • P = a • P := by
      rw [← add_smul, Nat.sub_add_cancel hab.le]; exact hE.symm
    simpa using this
  · intro hP
    have hpos : 0 < addOrderOf P := hP.addOrderOf_pos
    have hfin : (Set.range fun k : ℕ => (2 ^ k) • P).Finite := by
      refine ((Set.finite_Iio (addOrderOf P)).image fun m : ℕ => m • P).subset ?_
      rintro _ ⟨k, rfl⟩
      exact ⟨(2 ^ k) % addOrderOf P, Nat.mod_lt _ hpos, mod_addOrderOf_nsmul P _⟩
    obtain ⟨B, hB⟩ := (hfin.image (canonicalHeight W)).bddAbove
    by_contra hne
    have hlt : 0 < canonicalHeight W P := lt_of_le_of_ne (canonicalHeight_nonneg W P) (Ne.symm hne)
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (B / canonicalHeight W P) (by norm_num : (1 : ℝ) < 4)
    have h1 := hB ⟨(2 ^ k) • P, ⟨k, rfl⟩, rfl⟩
    rw [canonicalHeight_two_pow_smul] at h1
    rw [div_lt_iff₀ hlt] at hk
    linarith

end Curve

/-! ## Quadratic forms on abelian groups -/

section Quadratic

variable {M : Type*} [AddCommGroup M] {F : Type*} [Field F]

/-- The associated pairing $B(x, y) = f(x + y) - f(x) - f(y)$ of a function $f : M \to F$ (pdf p. 131). -/
def polarPairingFun (f : M → F) (x y : M) : F := f (x + y) - f x - f y

/-- Milne's **quadratic form** on an abelian group (pdf p. 131): a function $f : M \to F$ to a field of
characteristic $\ne 2$ with $f(2x) = 4f(x)$ and $B(x, y) = f(x+y) - f(x) - f(y)$ bi-additive.  (The
characteristic hypothesis is carried by the theorems.)  Compared with Mathlib's `QuadraticMap ℤ M F` in
`isQuadraticForm_iff_exists_quadraticMap`. -/
@[kb "milne2006ec" "Ch. IV, §4, definition of a quadratic form on an abelian group, pdf p. 131"]
def IsQuadraticForm (f : M → F) : Prop :=
  (∀ x : M, f (2 • x) = 4 * f x) ∧
    (∀ x y z : M, polarPairingFun f (x + y) z = polarPairingFun f x z + polarPairingFun f y z) ∧
      ∀ x y z : M, polarPairingFun f x (y + z) = polarPairingFun f x y + polarPairingFun f x z

/-- The pairing of any function to a field is symmetric. -/
theorem polarPairingFun_comm (f : M → F) (x y : M) : polarPairingFun f x y = polarPairingFun f y x := by
  unfold polarPairingFun
  rw [add_comm x y]
  ring

/-- For a quadratic form (in particular, when $f(2x) = 4f(x)$) one has $2f(x) = B(x, x)$. -/
theorem IsQuadraticForm.two_mul_self {f : M → F} (hf : IsQuadraticForm f) (x : M) :
    2 * f x = polarPairingFun f x x := by
  have h := hf.1 x
  unfold polarPairingFun
  rw [← two_smul ℕ x, h]
  ring

/-- Multiples in the first variable of the pairing of a quadratic form. -/
theorem IsQuadraticForm.polarPairingFun_zsmul_left {f : M → F} (hf : IsQuadraticForm f) (a : ℤ)
    (x y : M) : polarPairingFun f (a • x) y = a * polarPairingFun f x y := by
  let g : M →+ F := AddMonoidHom.mk' (fun x => polarPairingFun f x y) (fun u v => hf.2.1 u v y)
  have := map_zsmul g a x
  simpa [g] using this

/-- Multiples in the second variable of the pairing of a quadratic form. -/
theorem IsQuadraticForm.polarPairingFun_zsmul_right {f : M → F} (hf : IsQuadraticForm f) (a : ℤ)
    (x y : M) : polarPairingFun f x (a • y) = a * polarPairingFun f x y := by
  let g : M →+ F := AddMonoidHom.mk' (fun y => polarPairingFun f x y) (fun u v => hf.2.2 x u v)
  have := map_zsmul g a y
  simpa [g] using this

/-- Milne's quadratic forms on an abelian group are exactly Mathlib's quadratic maps over `ℤ`
(for a field of characteristic $\ne 2$). -/
@[kb "milne2006ec" "Ch. IV, §4, definition of a quadratic form on an abelian group, pdf p. 131"]
theorem isQuadraticForm_iff_exists_quadraticMap (hF : ringChar F ≠ 2) (f : M → F) :
    IsQuadraticForm f ↔ ∃ Q : QuadraticMap ℤ M F, ⇑Q = f := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  constructor
  · intro hf
    have hself : ∀ x, f x = polarPairingFun f x x / 2 := fun x => by
      rw [eq_div_iff h2, mul_comm, hf.two_mul_self]
    refine ⟨QuadraticMap.ofPolar f (fun a x => ?_) (fun x x' y => hf.2.1 x x' y)
      (fun a x y => ?_), rfl⟩
    · rw [hself (a • x), hself x, hf.polarPairingFun_zsmul_left, hf.polarPairingFun_zsmul_right,
        zsmul_eq_mul]
      push_cast
      ring
    · exact (hf.polarPairingFun_zsmul_left a x y).trans (zsmul_eq_mul _ _).symm
  · rintro ⟨Q, rfl⟩
    refine ⟨fun x => ?_, fun x y z => QuadraticMap.polar_add_left Q x y z,
      fun x y z => QuadraticMap.polar_add_right Q x y z⟩
    rw [two_smul, QuadraticMap.map_add_self]
    norm_num

/-- Milne (pdf p. 131): the pairing $B$ of a quadratic form is symmetric and $f(x) = \tfrac12 B(x, x)$. -/
@[kb "milne2006ec" "Ch. IV, §4, the pairing of a quadratic form, pdf p. 131"]
theorem IsQuadraticForm.polarPairingFun_symm_and_self (hF : ringChar F ≠ 2) {f : M → F}
    (hf : IsQuadraticForm f) :
    (∀ x y : M, polarPairingFun f x y = polarPairingFun f y x) ∧ ∀ x : M, f x = polarPairingFun f x x / 2 := by
  refine ⟨polarPairingFun_comm f, fun x => ?_⟩
  rw [eq_div_iff (Ring.two_ne_zero hF), mul_comm, hf.two_mul_self]

/-- **Lemma 4.8** (pdf p. 131).  A function $f$ from an abelian group to a field of characteristic $\ne 2$
satisfying the parallelogram law $f(x+y) + f(x-y) = 2f(x) + 2f(y)$ is a quadratic form. -/
@[kb "milne2006ec" "Ch. IV, Lemma 4.8, pdf p. 131"]
theorem lemma_4_8 (hF : ringChar F ≠ 2) {f : M → F}
    (hpar : ∀ x y : M, f (x + y) + f (x - y) = 2 * f x + 2 * f y) : IsQuadraticForm f := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h0 : f 0 = 0 := by
    have := hpar 0 0
    simp only [add_zero, sub_zero] at this
    have h : (2 : F) * f 0 = 0 := by linear_combination -this
    exact (mul_eq_zero.mp h).resolve_left h2
  have hdouble : ∀ x : M, f (2 • x) = 4 * f x := fun x => by
    have := hpar x x
    rw [sub_self, h0, add_zero] at this
    rw [two_smul, this]
    ring
  have key : ∀ x y z : M, f (x + y + z) + f x + f y + f z = f (x + y) + f (x + z) + f (y + z) := by
    intro x y z
    have e2 : f (x + y + z) + f (x - y + z) = 2 * f (x + z) + 2 * f y := by
      have := hpar (x + z) y
      rwa [show x + z + y = x + y + z by abel, show x + z - y = x - y + z by abel] at this
    have e3 : f (x + y + z) + f (-x + y + z) = 2 * f (y + z) + 2 * f x := by
      have := hpar (y + z) x
      rwa [show y + z + x = x + y + z by abel, show y + z - x = -x + y + z by abel] at this
    have e4 : f (x - y + z) + f (-x + y + z) = 2 * f z + 2 * f (x - y) := by
      have := hpar z (x - y)
      rwa [show z + (x - y) = x - y + z by abel, show z - (x - y) = -x + y + z by abel] at this
    have e5 : f (x + y) + f (x - y) = 2 * f x + 2 * f y := hpar x y
    have h : (2 : F) * (f (x + y + z) + f x + f y + f z - (f (x + y) + f (x + z) + f (y + z))) = 0 := by
      linear_combination e2 + e3 - e4 - 2 * e5
    have := (mul_eq_zero.mp h).resolve_left h2
    linear_combination this
  have hleft : ∀ x y z : M, polarPairingFun f (x + y) z = polarPairingFun f x z + polarPairingFun f y z := by
    intro x y z
    unfold polarPairingFun
    linear_combination key x y z
  refine ⟨hdouble, hleft, fun x y z => ?_⟩
  rw [polarPairingFun_comm f x (y + z), hleft, polarPairingFun_comm f y x, polarPairingFun_comm f z x]

end Quadratic

section CurveQuadratic

variable {K : Type*} [Field K] [AdmissibleAbsValues K] (W : Affine K) [W.IsElliptic] [DecidableEq K]

/-- **Lemma 4.10** (pdf p. 132).  There is a constant $C$ with
$H(P_1 + P_2)\,H(P_1 - P_2) \le C\,H(P_1)^2 H(P_2)^2$ for all $P_1, P_2 \in E(K)$; here
$H(P) = $ `mulHeight P.xRep`.  (A one-sided consequence of Mathlib's
`WeierstrassCurve.Affine.approx_parallelogram_law`.) -/
@[kb "milne2006ec" "Ch. IV, Lemma 4.10, pdf p. 132"]
theorem lemma_4_10 : ∃ C : ℝ, ∀ P₁ P₂ : W.Point,
    mulHeight (P₁ + P₂).xRep * mulHeight (P₁ - P₂).xRep ≤
      C * mulHeight P₁.xRep ^ 2 * mulHeight P₂.xRep ^ 2 := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  refine ⟨Real.exp C, fun P₁ P₂ => ?_⟩
  have h := (abs_le.mp (hC P₁ P₂)).2
  simp only [Point.naiveHeight_eq_logHeight, logHeight_eq_log_mulHeight] at h
  have ha : 0 < mulHeight (P₁ + P₂).xRep := zero_lt_one.trans_le (one_le_mulHeight _)
  have hb : 0 < mulHeight (P₁ - P₂).xRep := zero_lt_one.trans_le (one_le_mulHeight _)
  have hc : 0 < mulHeight P₁.xRep := zero_lt_one.trans_le (one_le_mulHeight _)
  have hd : 0 < mulHeight P₂.xRep := zero_lt_one.trans_le (one_le_mulHeight _)
  rw [← Real.log_le_log_iff (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow, Real.log_pow]
  push_cast
  linarith

/-- **Lemma 4.11** (pdf p. 132).  The canonical height satisfies the parallelogram law
$\hat h(P + Q) + \hat h(P - Q) = 2\hat h(P) + 2\hat h(Q)$. -/
@[kb "milne2006ec" "Ch. IV, Lemma 4.11, pdf p. 132"]
theorem lemma_4_11 (P Q : W.Point) :
    canonicalHeight W (P + Q) + canonicalHeight W (P - Q) =
      2 * canonicalHeight W P + 2 * canonicalHeight W Q := by
  exact canonicalHeight_parallelogram W P Q

/-- **Proposition 4.9** (pdf p. 131).  The canonical height $\hat h : E(K) \to \mathbb{R}$ is a quadratic
form. -/
@[kb "milne2006ec" "Ch. IV, Prop. 4.9, pdf p. 131"]
theorem prop_4_9 : IsQuadraticForm (canonicalHeight W) :=
  lemma_4_8 (by rw [ringChar.eq ℝ 0]; norm_num) (lemma_4_11 W)

/-- **Proposition 4.13** (pdf p. 133).  Let $C > 0$ be such that $S = \{P \in E(K) \mid \hat h(P) \le C\}$
contains a set of coset representatives for $2E(K)$ in $E(K)$.  Then $S$ generates $E(K)$. -/
@[kb "milne2006ec" "Ch. IV, Prop. 4.13, pdf p. 133"]
theorem prop_4_13 [Northcott (logHeight₁ (K := K))] {C : ℝ} (hC : 0 < C)
    (hS : ∀ Q : W.Point, ∃ P : W.Point, canonicalHeight W P ≤ C ∧ ∃ R : W.Point, Q = P + 2 • R) :
    AddSubgroup.closure {P : W.Point | canonicalHeight W P ≤ C} = ⊤ := by
  set U := AddSubgroup.closure {P : W.Point | canonicalHeight W P ≤ C} with hU
  by_contra hne
  have hne' : (Uᶜ : Set W.Point).Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    exact hne (AddSubgroup.coe_eq_univ.mp h)
  have : Northcott (canonicalHeight W) := ⟨thm_4_7_a W⟩
  obtain ⟨Q, hQ, hmin⟩ := Northcott.exists_min_image (canonicalHeight W) _ hne'
  have hQU : Q ∉ U := hQ
  obtain ⟨P, hP, R, hR⟩ := hS Q
  have hPU : P ∈ U := AddSubgroup.subset_closure hP
  have hRU : R ∉ U := by
    intro hRU
    exact hQU (by rw [hR]; exact U.add_mem hPU (by simpa [two_smul] using U.add_mem hRU hRU))
  have hCQ : C < canonicalHeight W Q := by
    by_contra h
    exact hQU (AddSubgroup.subset_closure (not_lt.mp h))
  have hpar := canonicalHeight_parallelogram W Q P
  have hQP : Q - P = 2 • R := by rw [hR]; abel
  have h2R := canonicalHeight_two_smul W R
  rw [hQP, h2R] at hpar
  have := canonicalHeight_nonneg W (Q + P)
  have := hmin R hRU
  linarith

end CurveQuadratic

/-! ## The finite basis theorem (introduction to Chapter IV) -/

/-- The subgroup $nM$ of an abelian group $M$, for an integer $n$. -/
abbrev multiples (M : Type*) [AddCommGroup M] (n : ℤ) : AddSubgroup M := (zsmulAddGroupHom (α := M) n).range

/-- Introduction to Chapter IV (pdf p. 109): if $M$ is finitely generated then $M/nM$ is finite for every
$n \ne 0$ (Milne writes $n > 1$). -/
@[kb "milne2006ec" "Ch. IV, introduction, finitely generated implies M/nM finite, pdf p. 109"]
theorem finite_quotient_multiples_of_fg {M : Type*} [AddCommGroup M] [AddGroup.FG M] {n : ℤ}
    (hn : n ≠ 0) : Finite (M ⧸ multiples M n) := by
  have h := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg M (n := n.natAbs)
    (Int.natAbs_ne_zero.mpr hn)
  have e : multiples M n = (nsmulAddMonoidHom (α := M) n.natAbs).range := by
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · ext x
      simp
    · ext x
      simp only [AddMonoidHom.mem_range, zsmulAddGroupHom_apply, nsmulAddMonoidHom_apply,
        Int.natAbs_neg, Int.natAbs_natCast]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨-y, by simp⟩
      · rintro ⟨y, rfl⟩
        exact ⟨-y, by simp⟩
  rw [e]
  exact AddSubgroup.finiteIndex_iff_finite_quotient.mp h

/-- Introduction to Chapter IV (pdf p. 109): the converse fails: $\mathbb{Q} = n\mathbb{Q}$ for every $n \ne 0$,
but $\mathbb{Q}$ is not finitely generated. -/
@[kb "milne2006ec" "Ch. IV, introduction, Q = nQ but Q is not finitely generated, pdf p. 109"]
theorem rat_multiples_eq_top_and_not_fg :
    (∀ n : ℤ, n ≠ 0 → multiples ℚ n = ⊤) ∧ ¬ AddGroup.FG ℚ := by
  refine ⟨fun n hn => ?_, fun h => ?_⟩
  · rw [eq_top_iff]
    intro q _
    have : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    exact ⟨q / n, by simp; field_simp⟩
  · have : Module.Finite ℤ ℚ := Module.Finite.iff_addGroup_fg.mpr h
    have hi : IsIntegral ℤ (1 / 2 : ℚ) := Algebra.IsIntegral.isIntegral _
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := ℤ) hi
    have : (z : ℚ) = 1 / 2 := hz
    have h1 : (z : ℚ) * 2 = 1 := by rw [this]; norm_num
    have h2 : z * 2 = 1 := by exact_mod_cast h1
    omega

/-- Introduction to Chapter IV (pdf pp. 109–110; completed in §4, pdf p. 133): the descent argument.  For an
elliptic curve over a field with an admissible family of absolute values and the Northcott property (a number
field, for instance), if $E(K)/2E(K)$ is finite then $E(K)$ is finitely generated.  The finite basis theorem
(`NumberFieldKB.MilneEC.finite_basis`) combines this with the weak finite basis theorem. -/
@[kb "milne2006ec" "Ch. IV, introduction, the descent argument, pdf p. 110"]
theorem fg_of_finite_quotient_two {K : Type*} [Field K] [AdmissibleAbsValues K]
    [Northcott (logHeight₁ (K := K))] [DecidableEq K] (W : Affine K) [W.IsElliptic]
    (h : Finite (W.Point ⧸ multiples W.Point 2)) : AddGroup.FG W.Point := by
  have : Northcott (canonicalHeight W) := ⟨thm_4_7_a W⟩
  have e : multiples W.Point 2 = (nsmulAddMonoidHom (α := W.Point) 2).range := by
    ext x
    simp [two_smul]
  have H₁ : (nsmulAddMonoidHom (α := W.Point) 2).range.FiniteIndex := by
    rw [← e]
    exact AddSubgroup.finiteIndex_iff_finite_quotient.mpr h
  refine AddCommGroup.fg_of_descent' (C := 0) H₁ (canonicalHeight_nonneg W) fun x y => ?_
  rw [lemma_4_11 W x y]
  have : 2 * canonicalHeight W x + 2 * canonicalHeight W y
      - 2 * (canonicalHeight W x + canonicalHeight W y) = 0 := by ring
  rw [this, abs_zero]

end NumberFieldKB.MilneEC
