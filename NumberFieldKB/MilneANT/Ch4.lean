import Mathlib.Algebra.QuadraticAlgebra.Discriminant
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import QuadFormsKB.Citation
import QuadFormsKB.Binary.ClassBijection
import NumberFieldKB.HilbertClassField.Artin
import NumberFieldKB.MilneANT.Ch4Dirichlet
import NumberFieldKB.MilneANT.Ch4Example46
import NumberFieldKB.MilneANT.Ch4Example48
import NumberFieldKB.MilneANT.Ch4Remark411
import NumberFieldKB.MilneANT.Ch4NormForm

/-!
# Milne, *Algebraic Number Theory*, Chapter 4: the items not in Mathlib

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), bib key `milne2020ant`; printed page numbers.

* **Example 4.6** (`example_4_6`): $\mathbb Q(\sqrt{-5})$ has class number $2$; $\mathfrak p = (2, 1 + \sqrt{-5})$ is
  not principal and $\mathfrak p^2 = (2)$.
* **Example 4.7** (`example_4_7_a`; named statement `Example47ClassGroup`): cubic fields with
  $-49 \le \Delta_K < 0$ have class number $1$; the stem field of $X^3 + 10X + 1$ has cyclic class group of order $6$.
* **Example 4.8** (`example_4_8`): for a root $\alpha$ of $X^5 - X + 1$, $\mathcal O_{\mathbb Q(\alpha)} = \mathbb Z[\alpha]$ is
  a principal ideal domain.
* **Corollary 4.10** (`cor_4_10`): no monic irreducible integer polynomial of degree $> 1$ has discriminant $\pm 1$.
* **Remark 4.11** (`remark_4_11_hilbert`, `remark_4_11_example`): the Hilbert class field (from the named inputs of
  `NumberFieldKB.HilbertClassField.Artin`), and $\mathbb Q(\sqrt{-1}, \sqrt 5)$ is unramified over $\mathbb Q(\sqrt{-5})$.
* **Lemma 4.23** (`lemma_4_23`): the Dirichlet integral.
* **Theorem 4.29** (`thm_4_29_imaginary` from QuadFormsKB; named statement `QuadraticFormsIdealClasses` for the full
  statement including real quadratic fields), and the norm form $Q_{a_1,a_2}$ of a basis of a fractional ideal
  (`idealNormForm`, a definition in prose, with `idealNormForm_integral`).
-/

open NumberField Polynomial Module
open scoped nonZeroDivisors

namespace NumberFieldKB.MilneANT

/-- **The Minkowski constant** (Milne p. 70, a definition in prose): for a number field $K$ of degree $n$ with $s$
complex places, $C_K = \frac{n!}{n^n}\left(\frac 4\pi\right)^s$. Mathlib has the Minkowski bound
$C_K\sqrt{|\Delta_K|}$ only as a local notation `M K` in `Mathlib/NumberTheory/NumberField/ClassNumber.lean`; see
`exists_ideal_in_class_of_norm_le_minkowskiConstant`. -/
@[kb "milne2020ant" "v3.08, Ch. 4, definition in prose (Minkowski constant), p. 70"]
noncomputable def minkowskiConstant (K : Type*) [Field K] [NumberField K] : ℝ :=
  (finrank ℚ K).factorial / (finrank ℚ K : ℝ) ^ finrank ℚ K * (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K

/-- Theorem 4.3 in terms of the Minkowski constant: every ideal class of $\mathcal O_K$ contains a nonzero integral
ideal $\mathfrak a$ with $N\mathfrak a \le C_K\sqrt{|\Delta_K|}$. Restates Mathlib's
`NumberField.exists_ideal_in_class_of_norm_le`. -/
@[kb "milne2020ant" "v3.08, Thm. 4.3, p. 70"]
theorem exists_ideal_in_class_of_norm_le_minkowskiConstant (K : Type*) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) : ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ minkowskiConstant K * Real.sqrt |(discr K : ℝ)| := by
  obtain ⟨I, hI, hle⟩ := NumberField.exists_ideal_in_class_of_norm_le (K := K) C
  refine ⟨I, hI, le_of_le_of_eq hle ?_⟩
  unfold minkowskiConstant
  ring

-- Prose definitions D074–D076 (integral binary quadratic form, its discriminant, proper equivalence), formalized in
-- QuadFormsKB: `BinQF` (coefficients `a`, `b`, `c` in ℤ), `BinQF.disc` ($b^2 - 4ac$), and `Binary.SLEquiv`
-- ($\mathrm{SL}_2(\mathbb Z)$-equivalence).
attribute [kb "milne2020ant" "v3.08, Ch. 4, definition in prose (integral binary quadratic form), p. 81"]
  QuadFormsKB.BinQF
attribute [kb "milne2020ant" "v3.08, Ch. 4, definition in prose (discriminant of a binary form), p. 81"]
  QuadFormsKB.BinQF.disc
attribute [kb "milne2020ant" "v3.08, Ch. 4, definition in prose (equivalence of binary forms), p. 81"]
  QuadFormsKB.Binary.SLEquiv

/-- **Example 4.6.** Let $K$ be a quadratic field containing $\sqrt{-5}$ (i.e. $K = \mathbb Q(\sqrt{-5})$). Then the
class number of $K$ is $2$, the ideal $\mathfrak p = (2, 1 + \sqrt{-5})$ of $\mathcal O_K$ is not principal, and
$\mathfrak p^2 = (2)$; so $\mathcal O_K$ and $\mathfrak p$ represent the two ideal classes. -/
@[kb "milne2020ant" "v3.08, Example 4.6, p. 71"]
theorem example_4_6 (K : Type*) [Field K] [NumberField K] (hK : finrank ℚ K = 2) (s : 𝓞 K) (hs : s ^ 2 = -5) :
    classNumber K = 2 ∧ ¬ (Ideal.span {2, 1 + s} : Ideal (𝓞 K)).IsPrincipal ∧
      (Ideal.span {2, 1 + s} : Ideal (𝓞 K)) ^ 2 = Ideal.span {2} :=
  ⟨Q5.class_number_two hK s hs, Q5.P_not_principal hK s hs, Q5.P_sq s hs⟩

/-- **Example 4.7**, first claim. A cubic number field with discriminant $-49 \le \Delta_K < 0$ has class number $1$
(the Minkowski bound is $< 2$). -/
@[kb "milne2020ant" "v3.08, Example 4.7, p. 71"]
theorem example_4_7_a (K : Type*) [Field K] [NumberField K] (hK : finrank ℚ K = 3) (hΔ : -49 ≤ discr K)
    (hΔ' : discr K < 0) : classNumber K = 1 := by
  rw [classNumber_eq_one_iff]
  have hs : InfinitePlace.nrComplexPlaces K = 1 := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h2 := NumberField.sign_discr K
    rw [Int.sign_eq_neg_one_of_neg hΔ'] at h2
    rcases Nat.lt_or_ge (InfinitePlace.nrComplexPlaces K) 1 with h | h
    · have : InfinitePlace.nrComplexPlaces K = 0 := by omega
      rw [this] at h2
      simp at h2
    · omega
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [hs, hK]
  have hpi := Real.pi_gt_d2
  have h49 : |(discr K : ℝ)| ≤ 49 := by
    rw [abs_le]
    constructor
    · exact_mod_cast (by linarith : (-49 : ℤ) ≤ discr K)
    · have : (discr K : ℝ) < 0 := by exact_mod_cast hΔ'
      linarith
  rw [← Int.cast_abs] at h49
  refine lt_of_le_of_lt h49 ?_
  norm_num [Nat.factorial]
  nlinarith

/-- **Example 4.7**, second claim (named statement). For the stem field $K = \mathbb Q(\alpha)$ of $X^3 + 10X + 1$
(discriminant $-4027$), the class group of $\mathcal O_K$ is cyclic of order $6$, generated by the class of
$\mathfrak p = (2, 1 + \alpha)$. (Milne: "requires some hard work if you do it by hand"; he refers to Artin 1959 and
PARI.) -/
@[kb "milne2020ant" "v3.08, Example 4.7, p. 71"]
structure Example47ClassGroup : Prop where
  cyclic_six : ∀ (K : Type) [Field K] [NumberField K] (α : 𝓞 K), α ^ 3 + 10 * α + 1 = 0 →
    IntermediateField.adjoin ℚ {(α : K)} = ⊤ →
    IsCyclic (ClassGroup (𝓞 K)) ∧ classNumber K = 6

/-- **Example 4.8.** Let $\alpha$ be a root of $X^5 - X + 1$ generating the number field $K$. Then
$\mathcal O_K = \mathbb Z[\alpha]$ and $\mathcal O_K$ is a principal ideal domain.

Milne refers to Example 2.39 for irreducibility and the discriminant $19 \cdot 151$, which concerns
$X^5 - X - 1$; the two polynomials have the same roots up to sign ($-\alpha$ is a root of $X^5 - X - 1$), hence the
same stem field and discriminant. -/
@[kb "milne2020ant" "v3.08, Example 4.8, p. 72"]
theorem example_4_8 (K : Type*) [Field K] [NumberField K] (α : 𝓞 K) (hα : α ^ 5 - α + 1 = 0)
    (hgen : IntermediateField.adjoin ℚ {(α : K)} = ⊤) :
    Algebra.adjoin ℤ {α} = ⊤ ∧ IsPrincipalIdealRing (𝓞 K) :=
  Q8.example_4_8' K α hα hgen

private lemma cast_discr' {K : Type*} [Field K] [NumberField K] {n : ℕ} (v : Fin n → 𝓞 K) :
    ((Algebra.discr ℤ v : ℤ) : ℚ) = Algebra.discr ℚ (fun i : Fin n => (v i : K)) := by
  rw [Algebra.discr_def, Algebra.discr_def, ← eq_intCast (Int.castRingHom ℚ), RingHom.map_det]
  congr 1
  ext i j
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.coe_trace_int]

private lemma discr_eq_det_sq' {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (𝓞 K)) (v : Fin n → 𝓞 K) :
    Algebra.discr ℤ v = (b.toMatrix v).det ^ 2 * discr K := by
  have := Algebra.discr_of_matrix_vecMul b (b.toMatrix v)
  rw [Module.Basis.toMatrix_map_vecMul] at this
  rw [this, discr_eq_discr K b]

/-- **Corollary 4.10.** There is no monic irreducible $f \in \mathbb Z[X]$ of degree $> 1$ with discriminant $\pm 1$.
Stated, as in Milne's proof, for a root $\alpha \in \mathcal O_K$ of $f$ generating the number field
$K = \mathbb Q(\alpha)$ of degree $n > 1$: $D(1, \alpha, \dots, \alpha^{n-1}) \ne \pm 1$. (The discriminant of $f$ is
Milne's $D(1, \alpha, \dots, \alpha^{n-1})$, Proposition 2.34.) -/
@[kb "milne2020ant" "v3.08, Cor. 4.10, p. 72"]
theorem cor_4_10 (K : Type*) [Field K] [NumberField K] (α : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(α : K)} = ⊤) (hn : 1 < finrank ℚ K) :
    Algebra.discr ℚ (fun i : Fin (finrank ℚ K) => (α : K) ^ (i : ℕ)) ≠ 1 ∧
      Algebra.discr ℚ (fun i : Fin (finrank ℚ K) => (α : K) ^ (i : ℕ)) ≠ -1 := by
  have hrk : Module.finrank ℤ (𝓞 K) = finrank ℚ K := RingOfIntegers.rank K
  let b : Module.Basis (Fin (finrank ℚ K)) ℤ (𝓞 K) := Module.finBasisOfFinrankEq ℤ (𝓞 K) hrk
  let v : Fin (finrank ℚ K) → 𝓞 K := fun i => α ^ (i : ℕ)
  have h1 := discr_eq_det_sq' b v
  have h3 := cast_discr' v
  have h2 := abs_discr_gt_two hn
  have key : ∀ d : ℤ, (d = 1 ∨ d = -1) →
      Algebra.discr ℚ (fun i : Fin (finrank ℚ K) => (α : K) ^ (i : ℕ)) ≠ d := by
    intro d hd heq
    have h4 : Algebra.discr ℤ v = d := by
      have : ((Algebra.discr ℤ v : ℤ) : ℚ) = d := by
        rw [h3]; simpa [v] using heq
      exact_mod_cast this
    have h5 : discr K ∣ d := by
      rw [← h4, h1]; exact Dvd.intro_left _ rfl
    have h6 : |discr K| ≤ |d| := by
      have hd0 : d ≠ 0 := by rcases hd with rfl | rfl <;> norm_num
      exact Int.le_of_dvd (abs_pos.2 hd0) ((abs_dvd_abs _ _).2 h5)
    have : |d| = 1 := by rcases hd with rfl | rfl <;> norm_num
    omega
  exact ⟨by simpa using key 1 (Or.inl rfl), by simpa using key (-1) (Or.inr rfl)⟩

/-- **Remark 4.11**, class field theory. Given the named inputs of `NumberFieldKB.HilbertClassField.Artin`
(Artin reciprocity for unramified abelian extensions, and the existence of an unramified abelian extension of degree
$h_K$), $K$ has a Hilbert class field: an abelian extension unramified at all places whose Galois group is
isomorphic to $\mathrm{Cl}(\mathcal O_K)$ via the Artin map. Restates
`NumberFieldKB.HilbertClassField.hilbertClassFieldExists_of_inputs`. -/
@[kb "milne2020ant" "v3.08, Remark 4.11, p. 72"]
theorem remark_4_11_hilbert (K : Type) [Field K] [NumberField K]
    (hA : NumberFieldKB.HilbertClassField.UnramifiedArtinReciprocityInput K)
    (hB : NumberFieldKB.HilbertClassField.HilbertClassFieldDegreeInput K) :
    NumberFieldKB.HilbertClassField.HilbertClassFieldExists K :=
  NumberFieldKB.HilbertClassField.hilbertClassFieldExists_of_inputs hA hB

/-- **Remark 4.11**, example. Let $K = \mathbb Q(\sqrt{-5})$ and $L = \mathbb Q(\sqrt{-1}, \sqrt 5) \supseteq K$
(a quadratic extension of $K$ containing square roots of $-1$ and $5$). Then $L$ is unramified over $K$ at every
finite prime: no prime of $\mathcal O_L$ is ramified over $\mathcal O_K$. -/
@[kb "milne2020ant" "v3.08, Remark 4.11, p. 72"]
theorem remark_4_11_example (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hK : finrank ℚ K = 2) (hL : finrank K L = 2) (s : K) (hs : s ^ 2 = -5) (i r : L) (hi : i ^ 2 = -1)
    (hr : r ^ 2 = 5) (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) : Algebra.IsUnramifiedAt (𝓞 K) P :=
  Rem411.remark_4_11_example' K L hK hL s hs i r hi hr P hP

/-- **Lemma 4.23** (Dirichlet's integral). For real numbers $a_1, \dots, a_m \ge 0$ and $t > 0$, with
$Z(t) = \{x \in \mathbb R^m \mid x_i \ge 0, \sum x_i \le t\}$,
$$\int_{Z(t)} x_1^{a_1}\cdots x_m^{a_m}\,dx_1\cdots dx_m
  = t^{\sum a_i + m}\,\frac{\Gamma(a_1+1)\cdots\Gamma(a_m+1)}{\Gamma(\sum a_i + m + 1)}.$$

*Update:* Milne assumes $a_i > 0$ but applies the lemma (in the proof of Lemma 4.22) with $a_i = 0$; the formula holds
for all $a_i \ge 0$ (indeed for $a_i > -1$), which is the hypothesis here. Indices are $0$-based. -/
@[kb "milne2020ant" "v3.08, Lemma 4.23, p. 78"]
theorem lemma_4_23 (m : ℕ) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (t : ℝ) (ht : 0 < t) :
    ∫ x in {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ t}, ∏ i, x i ^ a i =
      t ^ (∑ i, a i + m) * (∏ i, Real.Gamma (a i + 1)) / Real.Gamma (∑ i, a i + m + 1) :=
  Dirichlet4.lemma_4_23_aux m a ha t ht

/-- **The norm form of a basis of a fractional ideal** (Milne p. 82, a definition in prose). For a quadratic field
$K$, a fractional ideal $\mathfrak a$ of $\mathcal O_K$ with $\mathbb Z$-basis $a_1, a_2$, the form
$$Q_{a_1,a_2}(X, Y) = N\mathfrak a^{-1}\,\mathrm{Nm}_{K/\mathbb Q}(a_1X + a_2Y),$$
as a function on $\mathbb Q^2$. Here $N\mathfrak a$ is Mathlib's `FractionalIdeal.absNorm`. Milne's choice of the
order of $a_1, a_2$ (making $\det\begin{pmatrix} a_1 & a_2\\ \sigma a_1 & \sigma a_2\end{pmatrix} = \sqrt{d_K}\,N\mathfrak a$) is
not part of the definition. -/
@[kb "milne2020ant" "v3.08, Ch. 4, definition in prose (norm form Q_{a1,a2}), p. 82"]
noncomputable def idealNormForm {K : Type*} [Field K] [NumberField K] (a : FractionalIdeal (𝓞 K)⁰ K)
    (a₁ a₂ : K) (X Y : ℚ) : ℚ :=
  (FractionalIdeal.absNorm a)⁻¹ * Algebra.norm ℚ (a₁ * X + a₂ * Y)

/-- The norm form $Q_{a_1,a_2}$ of a $\mathbb Z$-basis of a fractional ideal of a quadratic field $K$ is an integral
binary quadratic form with discriminant $d_K = \mathrm{disc}(\mathcal O_K/\mathbb Z)$ (Milne p. 82). -/
@[kb "milne2020ant" "v3.08, Ch. 4, p. 82 (Q_{a1,a2} is integral of discriminant d_K)"]
theorem idealNormForm_integral {K : Type*} [Field K] [NumberField K] (hK : finrank ℚ K = 2)
    (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : Basis (Fin 2) ℤ ((a : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    ∃ f : QuadFormsKB.BinQF, f.disc = discr K ∧ ∀ x y : ℤ,
      (QuadFormsKB.BinQF.eval f x y : ℚ) = idealNormForm (a : FractionalIdeal (𝓞 K)⁰ K) (b 0) (b 1) x y := by
  have hn0 : FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact a.ne_zero
  have m0 : (b 0 : K) ∈ (a : FractionalIdeal (𝓞 K)⁰ K) := (b 0).2
  have m1 : (b 1 : K) ∈ (a : FractionalIdeal (𝓞 K)⁰ K) := (b 1).2
  have ms : (b 0 : K) + (b 1 : K) ∈ (a : FractionalIdeal (𝓞 K)⁰ K) := by
    simpa using (b 0 + b 1).2
  obtain ⟨z0, h0⟩ := NormForm.norm_div_absNorm_int a _ m0
  obtain ⟨z1, h1⟩ := NormForm.norm_div_absNorm_int a _ m1
  obtain ⟨zs, hs⟩ := NormForm.norm_div_absNorm_int a _ ms
  set n : ℚ := FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) with hn
  have hdisc := NormForm.discr_frac hK (a : FractionalIdeal (𝓞 K)⁰ K) b
  have hid := NormForm.quad_disc_id hK (b 0 : K) (b 1 : K)
  have hD : Algebra.discr ℚ (fun i => (b i : K)) =
      Algebra.trace ℚ K ((b 0 : K) * b 0) * Algebra.trace ℚ K ((b 1 : K) * b 1)
        - Algebra.trace ℚ K ((b 0 : K) * b 1) ^ 2 := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, mul_comm (b 1 : K) (b 0 : K)]
    ring
  refine ⟨QuadFormsKB.BinQF.mk z0 (zs - z0 - z1) z1, ?_, ?_⟩
  · unfold QuadFormsKB.BinQF.disc
    simp only [QuadFormsKB.BinQF.a_mk, QuadFormsKB.BinQF.b_mk, QuadFormsKB.BinQF.c_mk]
    have key : n ^ 2 * (((zs - z0 - z1 : ℤ) : ℚ) ^ 2 - 4 * z0 * z1) = n ^ 2 * (discr K : ℚ) := by
      rw [← hdisc, hD, ← hid, hs, h0, h1]
      push_cast
      ring
    have := mul_left_cancel₀ (pow_ne_zero 2 hn0) key
    exact_mod_cast this
  · intro x y
    have hP := NormForm.quad_trace_mul hK (b 0 : K) (b 1 : K)
    unfold idealNormForm
    rw [QuadFormsKB.BinQF.eval_eq, NormForm.norm_expand hK, hP, hs, h0, h1]
    simp only [QuadFormsKB.BinQF.a_mk, QuadFormsKB.BinQF.b_mk, QuadFormsKB.BinQF.c_mk]
    field_simp
    push_cast
    ring

/-- **Theorem 4.29**, imaginary quadratic case, from QuadFormsKB. For a fundamental discriminant $D < 0$ the
$\mathrm{SL}_2(\mathbb Z)$-classes of primitive positive definite integral binary quadratic forms of discriminant $D$
are in bijection with $\mathrm{Cl}(\mathcal O_{K})$, $K = \mathbb Q(\sqrt D)$ (for $D < 0$, $\mathrm{Cl}^+ = \mathrm{Cl}$).
Restates `QuadFormsKB.Binary.slClassEquiv` (Cox, Thm. 7.7), which goes from forms to ideals; Milne's map
$\mathfrak a \mapsto Q_{a_1,a_2}$ goes the other way. For $D < 0$ only positive definite forms occur (Milne's
"equivalence classes of integral binary quadratic forms with discriminant $d_K$" counts each definite class once up to
sign). -/
@[kb "milne2020ant" "v3.08, Thm. 4.29 (imaginary quadratic case), p. 82"]
theorem thm_4_29_imaginary (D : ℤ) [QuadFormsKB.Binary.IsQuadDisc D] (hD : D < 0) :
    Nonempty (Quotient (QuadFormsKB.Binary.slSetoid D) ≃ ClassGroup (𝓞 (QuadFormsKB.Binary.QField D))) :=
  ⟨QuadFormsKB.Binary.slClassEquiv hD⟩

/-- The subgroup $P^+(K)$ of $\mathrm{Id}(\mathcal O_K)$ generated by the principal fractional ideals $(\alpha)$ with
$\alpha$ totally positive ($\varphi(\alpha) > 0$ for every real embedding $\varphi$; for an imaginary quadratic field
every nonzero $\alpha$ qualifies). -/
def totallyPositivePrincipal (K : Type*) [Field K] [NumberField K] : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Subgroup.closure {u | ∃ α : K, α ≠ 0 ∧ (∀ φ : K →+* ℝ, 0 < φ α) ∧
    (u : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ α}

/-- The narrow class group $\mathrm{Cl}^+(K) = \mathrm{Id}(\mathcal O_K)/P^+(K)$ (Milne p. 82, for quadratic fields;
for an imaginary quadratic field it is the class group). -/
abbrev NarrowClassGroup (K : Type*) [Field K] [NumberField K] : Type _ :=
  (FractionalIdeal (𝓞 K)⁰ K)ˣ ⧸ totallyPositivePrincipal K

/-- Integral binary quadratic forms of discriminant $D$, required to be positive definite when $D < 0$. -/
def FormsOfDisc (D : ℤ) : Type := {f : QuadFormsKB.BinQF // f.disc = D ∧ (D < 0 → 0 < f.a)}

/-- **Theorem 4.29** (named statement; Milne cites Fröhlich–Taylor VII.2). Let $K$ be a quadratic field with
discriminant $d_K$, $\sigma$ the nontrivial automorphism, $\varphi : K \to \mathbb C$ an embedding and
$\delta \in K$ with $\delta^2 = d_K$ chosen so that $\varphi(\delta) > 0$ if $d_K > 0$ and
$\mathrm{Im}\,\varphi(\delta) > 0$ if $d_K < 0$ (Milne's $\sqrt{d_K}$). For a fractional ideal $\mathfrak a$ with a
$\mathbb Z$-basis $a_1, a_2$ ordered so that $a_1\sigma(a_2) - a_2\sigma(a_1) = \delta\,N\mathfrak a$, the class of
the norm form $Q_{a_1,a_2}$ depends only on the image of $\mathfrak a$ in $\mathrm{Cl}^+(K)$, and
$\mathfrak a \mapsto [Q_{a_1,a_2}]$ is a bijection from $\mathrm{Cl}^+(K)$ onto the set of
$\mathrm{SL}_2(\mathbb Z)$-classes of integral binary quadratic forms of discriminant $d_K$.

*Erratum:* for $d_K < 0$ the forms $Q_{a_1,a_2}$ are positive definite, so the target must be the classes of
**positive definite** forms (Milne says "integral binary quadratic forms with discriminant $d_K$"; the negative
definite ones are not in the image). `FormsOfDisc` imposes this. -/
@[kb "milne2020ant" "v3.08, Thm. 4.29, p. 82"]
structure QuadraticFormsIdealClasses : Prop where
  bijection : ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 →
    ∀ (σ : K ≃ₐ[ℚ] K), σ ≠ 1 → ∀ (φ : K →+* ℂ) (δ : K), δ ^ 2 = discr K →
    (0 < discr K → 0 < (φ δ).re) → (discr K < 0 → 0 < (φ δ).im) →
    ∃ Φ : NarrowClassGroup K ≃ Quot (fun f g : FormsOfDisc (discr K) => QuadFormsKB.Binary.SLEquiv f.1 g.1),
      ∀ (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
        (b : Basis (Fin 2) ℤ ((a : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)),
        ((b 0 : K) * σ (b 1) - (b 1 : K) * σ (b 0) = δ * (FractionalIdeal.absNorm (a : FractionalIdeal (𝓞 K)⁰ K) : K)) →
        ∀ f : FormsOfDisc (discr K), (∀ x y : ℤ, (QuadFormsKB.BinQF.eval f.1 x y : ℚ) =
          idealNormForm (a : FractionalIdeal (𝓞 K)⁰ K) (b 0) (b 1) x y) →
        Φ (QuotientGroup.mk a) = Quot.mk _ f

end NumberFieldKB.MilneANT
