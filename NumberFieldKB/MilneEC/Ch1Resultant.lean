import NumberFieldKB.MilneEC.Ch1Affine
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Milne, Elliptic Curves, Chapter I, Section 1, Appendix: resultants

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, §1, "Appendix: resultants" (pdf pp. 22–25):
the definition of the resultant, Proposition 1.22, Example 1.23, Proposition 1.24, Corollary 1.25,
Proposition 1.26.

**Resultant.** Milne's $\mathrm{Res}(f, g)$ for $f = s_0X^m + \cdots + s_m$, $g = t_0X^n + \cdots + t_n$
(with $s_0$, $t_0$ allowed to vanish) is Mathlib's `Polynomial.resultant f g m n`, the determinant of
`Polynomial.sylvester f g m n`.  Mathlib's matrix is the transpose of Milne's with the order of the rows
and of the columns reversed, so the two determinants are equal.

**Two variables.** For Proposition 1.24, `yPolyEquiv` identifies `k[X, Y]` (here
`MvPolynomial (Fin 2) k`, $X$ = `X 0`, $Y$ = `X 1`) with $k[X][Y]$, a polynomial in $Y$ with coefficients in
$k[X]$; `degY f` is the degree in $Y$ and `resultantY f g` the resultant in $Y$, an element of $k[X]$.

**Degenerate cases.** Milne tacitly assumes the formal degrees are not both 0: for $m = n = 0$ the
Sylvester matrix is empty, its determinant is 1, and Proposition 1.22 (a) can hold without the resultant
vanishing.  The statements below assume $m + n > 0$ where this matters.  Proposition 1.24 (b) needs a
correction: a common factor lying in $k[X]$ (degree 0 in $Y$) does not make the resultant in $Y$ vanish
(`prop_1_24_b_counterexample`); the correct statement asks for a common factor of positive degree in $Y$.
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC

variable {k : Type*} [Field k]

-- Definition of the resultant (p. 22): Milne's determinant is Mathlib's `Polynomial.resultant f g m n`
-- of the matrix `Polynomial.sylvester f g m n` (the transpose of Milne's matrix, with rows and columns
-- in reverse order, which has the same determinant).
attribute [kb "milne2006ec" "Ch. I, §1, Appendix, Def. of the resultant, pdf p. 22"]
  Polynomial.resultant Polynomial.sylvester

/-- **Proposition 1.22** (p. 23), the parenthetical form of (b): `f` and `g` have a common root in
$k^{\mathrm{al}}$ if and only if they have a common factor (a common divisor which is not a unit) in
`k[X]`. -/
@[kb "milne2006ec" "Ch. I, Prop. 1.22 (b), pdf p. 23"]
theorem prop_1_22_common_root_iff (f g : Polynomial k) :
    (∃ α : AlgebraicClosure k, (f.map (algebraMap k _)).eval α = 0 ∧
        (g.map (algebraMap k _)).eval α = 0) ↔
      ∃ h : Polynomial k, ¬ IsUnit h ∧ h ∣ f ∧ h ∣ g := by
  constructor
  · rintro ⟨α, hf, hg⟩
    refine ⟨minpoly k α, minpoly.not_isUnit k α, ?_, ?_⟩
    · apply minpoly.dvd; rwa [Polynomial.aeval_def, ← Polynomial.eval_map]
    · apply minpoly.dvd; rwa [Polynomial.aeval_def, ← Polynomial.eval_map]
  · rintro ⟨h, hu, hf, hg⟩
    by_cases h0 : h = 0
    · subst h0
      rw [zero_dvd_iff] at hf hg
      exact ⟨0, by simp [hf, hg]⟩
    · have hd : (h.map (algebraMap k (AlgebraicClosure k))).degree ≠ 0 := by
        rw [Polynomial.degree_map]
        intro h'
        exact hu (Polynomial.isUnit_iff_degree_eq_zero.mpr h')
      obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hd
      refine ⟨α, ?_, ?_⟩
      · obtain ⟨c, rfl⟩ := hf
        simp [Polynomial.eval_mul, Polynomial.IsRoot.def.mp hα]
      · obtain ⟨c, rfl⟩ := hg
        simp [Polynomial.eval_mul, Polynomial.IsRoot.def.mp hα]

/-- Helper: a common root in the algebraic closure exists iff `f` and `g` are not coprime. -/
lemma commonRoot_iff_not_isCoprime (f g : Polynomial k) :
    (∃ α : AlgebraicClosure k, (f.map (algebraMap k _)).eval α = 0 ∧
        (g.map (algebraMap k _)).eval α = 0) ↔ ¬ IsCoprime f g := by
  rw [prop_1_22_common_root_iff]
  constructor
  · rintro ⟨h, hu, hf, hg⟩ hc
    exact hu (hc.isUnit_of_dvd' hf hg)
  · intro hc
    by_contra hne
    have hne' : ∀ h : Polynomial k, ¬ IsUnit h → h ∣ f → h ∣ g → False :=
      fun h a b c => hne ⟨h, a, b, c⟩
    apply hc
    by_cases h0 : f = 0 ∧ g = 0
    · obtain ⟨rfl, rfl⟩ := h0
      exact (hne' 0 not_isUnit_zero dvd_rfl dvd_rfl).elim
    · exact isCoprime_of_prime_dvd h0 fun z hz hzf hzg =>
        (hne' z hz.not_isUnit hzf hzg).elim

/-- **Proposition 1.22** (p. 23), in Milne's form with formal degrees: let `f`, `g` have degrees at most
`m`, `n` (with $m + n > 0$), and leading formal coefficients $s_0$ = `f.coeff m`, $t_0$ = `g.coeff n`.
Then $\mathrm{Res}(f, g) = 0$ if and only if (a) $s_0 = t_0 = 0$, or (b) `f` and `g` have a common root in
$k^{\mathrm{al}}$. -/
@[kb "milne2006ec" "Ch. I, Prop. 1.22, pdf p. 23"]
theorem prop_1_22 (f g : Polynomial k) {m n : ℕ} (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hmn : 0 < m + n) :
    f.resultant g m n = 0 ↔
      (f.coeff m = 0 ∧ g.coeff n = 0) ∨
      ∃ α : AlgebraicClosure k, (f.map (algebraMap k _)).eval α = 0 ∧
        (g.map (algebraMap k _)).eval α = 0 := by
  rw [commonRoot_iff_not_isCoprime]
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hf
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hg
  have key : f.resultant g (f.natDegree + a) (g.natDegree + b) =
      (-1) ^ ((g.natDegree + b) * a) * g.coeff (g.natDegree + b) ^ a *
        (f.coeff f.natDegree ^ b * f.resultant g f.natDegree g.natDegree) := by
    rw [Polynomial.resultant_add_left_deg _ _ _ _ _ le_rfl,
      Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl]
  have hlf : f.coeff f.natDegree = 0 ↔ f = 0 := by
    rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_eq_zero]
  have hlg : g.coeff g.natDegree = 0 ↔ g = 0 := by
    rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_eq_zero]
  have hz : f.resultant g f.natDegree g.natDegree = 0 ↔ (f ≠ 0 ∨ g ≠ 0) ∧ ¬ IsCoprime f g :=
    Polynomial.resultant_eq_zero_iff
  have hnc : f = 0 → g = 0 → ¬ IsCoprime f g := by
    rintro rfl rfl
    simp [isCoprime_zero_left]
  rcases Nat.eq_zero_or_pos a with rfl | ha <;> rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp only [add_zero] at hmn ⊢
    rw [hz, hlf, hlg]
    by_cases hf0 : f = 0
    · by_cases hg0 : g = 0
      · subst hf0; subst hg0; simp at hmn
      · simp [hf0, hg0]
    · simp [hf0]
  · have hg' : g.coeff (g.natDegree + b) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have key' : f.resultant g f.natDegree (g.natDegree + b) =
        f.coeff f.natDegree ^ b * f.resultant g f.natDegree g.natDegree := by
      simpa using key
    simp only [add_zero]
    rw [key', mul_eq_zero, pow_eq_zero_iff hb.ne', hlf, hz]
    by_cases hf0 : f = 0
    · simp [hf0, hg']
    · simp [hf0, hg']
  · have hf' : f.coeff (f.natDegree + a) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have key' : f.resultant g (f.natDegree + a) g.natDegree =
        (-1) ^ (g.natDegree * a) * g.coeff g.natDegree ^ a *
          f.resultant g f.natDegree g.natDegree := by
      simpa using key
    simp only [add_zero]
    rw [key', mul_eq_zero, mul_eq_zero, pow_eq_zero_iff ha.ne', hlg, hz]
    by_cases hg0 : g = 0
    · simp [hg0, hf']
    · simp [hg0, hf']
  · have hg' : g.coeff (g.natDegree + b) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hf' : f.coeff (f.natDegree + a) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [key, hg']
    simp [ha.ne', hf', hg']

/-- **Example 1.23** (p. 23): for a monic polynomial `f` of degree $m \geq 1$,
$\mathrm{Res}(f, f') = (-1)^{m(m-1)/2}\,\mathrm{disc}(f)$.  Restates Mathlib's `Polynomial.resultant_deriv`
(stated there with the leading coefficient, which is 1 here); `f'` is given the formal degree $m - 1$. -/
@[kb "milne2006ec" "Ch. I, Ex. 1.23, pdf p. 23"]
theorem example_1_23 {f : Polynomial k} (hmonic : f.Monic) (hdeg : 0 < f.degree) :
    f.resultant (Polynomial.derivative f) f.natDegree (f.natDegree - 1) =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
  rw [Polynomial.resultant_deriv hdeg, hmonic.leadingCoeff, mul_one]

/-- The identification of `k[X, Y]` with $k[X][Y]$ (polynomials in $Y$ = `X 1` with coefficients in
$k[X]$, $X$ = `X 0`). -/
noncomputable def yPolyEquiv : MvPolynomial (Fin 2) k ≃ₐ[k] Polynomial (Polynomial k) :=
  (renameEquiv k (Equiv.swap 0 1)).trans
    ((finSuccEquiv k 1).trans (Polynomial.mapAlgEquiv (uniqueAlgEquiv k (Fin 1))))

/-- The degree in $Y$ of a polynomial in `k[X, Y]`. -/
noncomputable def degY (f : MvPolynomial (Fin 2) k) : WithBot ℕ := (yPolyEquiv f).degree

/-- The resultant in $Y$ of two polynomials of `k[X, Y]` (Proposition 1.24): the resultant of `f` and
`g` regarded as polynomials in $Y$ with coefficients in $k[X]$, with their actual degrees in $Y$. -/
noncomputable def resultantY (f g : MvPolynomial (Fin 2) k) : Polynomial k :=
  (yPolyEquiv f).resultant (yPolyEquiv g)

/-- A polynomial in $X$ alone, regarded as an element of `k[X, Y]`. -/
noncomputable def ofX (r : Polynomial k) : MvPolynomial (Fin 2) k := Polynomial.aeval (X 0) r

/-- Helper: `yPolyEquiv` sends `Y` to the variable of the outer polynomial ring. -/
@[simp] lemma yPolyEquiv_X_one :
    yPolyEquiv (X 1 : MvPolynomial (Fin 2) k) = Polynomial.X := by
  simp [yPolyEquiv, MvPolynomial.finSuccEquiv_apply]

/-- Helper: `yPolyEquiv` sends `X` to the constant polynomial `X`. -/
@[simp] lemma yPolyEquiv_X_zero :
    yPolyEquiv (X 0 : MvPolynomial (Fin 2) k) = Polynomial.C Polynomial.X := by
  have h1 : (Fin.cases Polynomial.X (fun k_1 => Polynomial.C (X k_1)) (1 : Fin 2) :
      Polynomial (MvPolynomial (Fin 1) k)) = Polynomial.C (X 0) := rfl
  simp [yPolyEquiv, MvPolynomial.finSuccEquiv_apply, h1]

/-- Helper: `yPolyEquiv` sends a constant to the corresponding constant. -/
@[simp] lemma yPolyEquiv_C (c : k) :
    yPolyEquiv (C c : MvPolynomial (Fin 2) k) = Polynomial.C (Polynomial.C c) := by
  simp [yPolyEquiv, MvPolynomial.finSuccEquiv_apply]

/-- Helper: `yPolyEquiv` sends a polynomial in `X` alone to the corresponding constant. -/
@[simp] lemma yPolyEquiv_ofX (r : Polynomial k) : yPolyEquiv (ofX r) = Polynomial.C r := by
  unfold ofX
  induction r using Polynomial.induction_on' with
  | add p q hp hq => simp_all
  | monomial n c => simp [← Polynomial.C_mul_X_pow_eq_monomial]

/-- Helper: `yPolyEquiv` commutes with extension of the base field. -/
lemma yPolyEquiv_baseChange {K : Type*} [Field K] [Algebra k K] (f : MvPolynomial (Fin 2) k) :
    yPolyEquiv (baseChange K f) =
      (yPolyEquiv f).map (Polynomial.mapRingHom (algebraMap k K)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.map_add]
  | mul_X p i hp =>
    fin_cases i <;> simp [hp]

/-- Helper: the resultant (with actual degrees) commutes with an injective ring homomorphism. -/
lemma resultant_map_of_injective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (f g : Polynomial R) :
    (f.map φ).resultant (g.map φ) = φ (f.resultant g) := by
  rw [Polynomial.natDegree_map_eq_of_injective hφ f, Polynomial.natDegree_map_eq_of_injective hφ g]
  exact Polynomial.resultant_map_map f g f.natDegree g.natDegree φ

/-- Helper (Gauss's lemma): a common divisor of positive degree over the fraction field of `k[X]`
yields a common divisor of positive degree over `k[X]`. -/
lemma exists_common_factor_of_fractionRing (F G : Polynomial (Polynomial k))
    (h' : Polynomial (FractionRing (Polynomial k))) (hdeg : 0 < h'.degree)
    (hF : h' ∣ F.map (algebraMap (Polynomial k) (FractionRing (Polynomial k))))
    (hG : h' ∣ G.map (algebraMap (Polynomial k) (FractionRing (Polynomial k)))) :
    ∃ H : Polynomial (Polynomial k), 0 < H.degree ∧ H ∣ F ∧ H ∣ G := by
  let _ : NormalizedGCDMonoid (Polynomial k) := Nonempty.some inferInstance
  set ι := algebraMap (Polynomial k) (FractionRing (Polynomial k)) with hι
  have hinj : Function.Injective ι := IsFractionRing.injective _ _
  have h0 : h' ≠ 0 := by rintro rfl; simp at hdeg
  obtain ⟨b, hb0, hb⟩ := IsLocalization.integerNormalization_spec
    (nonZeroDivisors (Polynomial k)) h'
  set P := IsLocalization.integerNormalization (nonZeroDivisors (Polynomial k)) h' with hP
  have hbne : b ≠ 0 := nonZeroDivisors.ne_zero hb0
  have hbK : ι b ≠ 0 := (map_ne_zero_iff ι hinj).mpr hbne
  have hb' : P.map ι = Polynomial.C (ι b) * h' := by
    rw [hb, ← algebraMap_smul (FractionRing (Polynomial k)) b h', Polynomial.smul_eq_C_mul]
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero] at hb'
    rcases mul_eq_zero.mp hb'.symm with h | h
    · exact hbK (Polynomial.C_eq_zero.mp h)
    · exact h0 h
  have hc0 : P.content ≠ 0 := fun h => hP0 (Polynomial.content_eq_zero_iff.mp h)
  have hcK : ι P.content ≠ 0 := (map_ne_zero_iff ι hinj).mpr hc0
  have hpp : P.primPart.IsPrimitive := Polynomial.isPrimitive_primPart P
  have hmap : Polynomial.C (ι P.content) * P.primPart.map ι = Polynomial.C (ι b) * h' := by
    rw [← hb']
    conv_rhs => rw [P.eq_C_content_mul_primPart]
    simp
  have e : h' = Polynomial.C ((ι b)⁻¹ * ι P.content) * P.primPart.map ι := by
    calc h' = Polynomial.C (ι b)⁻¹ * (Polynomial.C (ι b) * h') := by
          rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hbK, Polynomial.C_1, one_mul]
      _ = _ := by rw [← hmap, ← mul_assoc, ← Polynomial.C_mul]
  have hdvd : P.primPart.map ι ∣ h' := Dvd.intro_left _ e.symm
  refine ⟨P.primPart, ?_, ?_, ?_⟩
  · have hne : (ι b)⁻¹ * ι P.content ≠ 0 := mul_ne_zero (inv_ne_zero hbK) hcK
    have hd : h'.degree = (P.primPart.map ι).degree := by
      conv_lhs => rw [e]
      rw [Polynomial.degree_C_mul hne]
    rw [← Polynomial.degree_map_eq_of_injective hinj, ← hd]
    exact hdeg
  · exact hpp.dvd_of_fraction_map_dvd_fraction_map (hdvd.trans hF)
  · exact hpp.dvd_of_fraction_map_dvd_fraction_map (hdvd.trans hG)

/-- Helper: for `F` nonzero and `G` in `k[X][Y]`, the resultant vanishes if and only if there is a
common divisor of positive degree in `Y`. -/
lemma resultant_eq_zero_iff_exists_common_factor {F G : Polynomial (Polynomial k)} (hF : F ≠ 0) :
    F.resultant G = 0 ↔ ∃ H : Polynomial (Polynomial k), 0 < H.degree ∧ H ∣ F ∧ H ∣ G := by
  set ι := algebraMap (Polynomial k) (FractionRing (Polynomial k)) with hι
  have hinj : Function.Injective ι := IsFractionRing.injective _ _
  have hFm : F.map ι ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hF
  have h1 : F.resultant G = 0 ↔ (F.map ι).resultant (G.map ι) = 0 := by
    rw [resultant_map_of_injective ι hinj]
    exact (map_eq_zero_iff ι hinj).symm
  rw [h1, Polynomial.resultant_eq_zero_iff]
  simp only [hFm, ne_eq, not_false_eq_true, true_or, true_and]
  constructor
  · intro hnc
    by_contra hno
    apply hnc
    apply isCoprime_of_prime_dvd (by simp [hFm])
    intro z hz hzF hzG
    have hz0 : z ≠ 0 := hz.ne_zero
    have hzd : 0 < z.degree := by
      rcases (Polynomial.zero_le_degree_iff.mpr hz0).lt_or_eq with h | h
      · exact h
      · exact absurd (Polynomial.isUnit_iff_degree_eq_zero.mpr h.symm) hz.not_isUnit
    obtain ⟨H, hH⟩ := exists_common_factor_of_fractionRing F G z hzd hzF hzG
    exact hno ⟨H, hH⟩
  · rintro ⟨H, hHd, hHF, hHG⟩ hc
    have hu := hc.isUnit_of_dvd' (Polynomial.map_dvd ι hHF) (Polynomial.map_dvd ι hHG)
    rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_map_eq_of_injective hinj] at hu
    rw [hu] at hHd
    exact lt_irrefl _ hHd

/-- **Proposition 1.24 (a)** (p. 24): there exist $a, b \in k[X, Y]$ with $af + bg = r(X)$, the resultant
in $Y$, and $\deg_Y a < \deg_Y g$, $\deg_Y b < \deg_Y f$ (degrees in $Y$, with the zero polynomial of degree
$-\infty$; `f`, `g` nonzero and at least one of them of positive degree in $Y$). -/
@[kb "milne2006ec" "Ch. I, Prop. 1.24 (a), pdf p. 24"]
theorem prop_1_24_a {f g : MvPolynomial (Fin 2) k} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : 0 < degY f ∨ 0 < degY g) :
    ∃ a b : MvPolynomial (Fin 2) k, a * f + b * g = ofX (resultantY f g) ∧
      degY a < degY g ∧ degY b < degY f := by
  have hF : yPolyEquiv f ≠ 0 := (map_ne_zero_iff _ yPolyEquiv.injective).mpr hf
  have hG : yPolyEquiv g ≠ 0 := (map_ne_zero_iff _ yPolyEquiv.injective).mpr hg
  have hH : (yPolyEquiv f).natDegree ≠ 0 ∨ (yPolyEquiv g).natDegree ≠ 0 := by
    rcases h with h | h
    · exact Or.inl (Polynomial.natDegree_pos_iff_degree_pos.mpr h).ne'
    · exact Or.inr (Polynomial.natDegree_pos_iff_degree_pos.mpr h).ne'
  obtain ⟨p, q, hp, hq, e⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    (yPolyEquiv f) (yPolyEquiv g) le_rfl le_rfl hH
  refine ⟨yPolyEquiv.symm p, yPolyEquiv.symm q, ?_, ?_, ?_⟩
  · apply yPolyEquiv.injective
    rw [map_add, map_mul, map_mul, yPolyEquiv_ofX, AlgEquiv.apply_symm_apply,
      AlgEquiv.apply_symm_apply]
    unfold resultantY
    rw [← e]
    ring
  · show (yPolyEquiv (yPolyEquiv.symm p)).degree < (yPolyEquiv g).degree
    rw [AlgEquiv.apply_symm_apply, Polynomial.degree_eq_natDegree hG]
    exact hp
  · show (yPolyEquiv (yPolyEquiv.symm q)).degree < (yPolyEquiv f).degree
    rw [AlgEquiv.apply_symm_apply, Polynomial.degree_eq_natDegree hF]
    exact hq

/-- **Proposition 1.24 (b)** (p. 24), corrected: for nonzero $f, g \in k[X, Y]$, the resultant in $Y$
vanishes if and only if `f` and `g` have a common factor in `k[X, Y]` of positive degree in $Y$.
(Milne's statement omits "of positive degree in $Y$"; see `prop_1_24_b_counterexample`.) -/
@[kb "milne2006ec" "Ch. I, Prop. 1.24 (b), pdf p. 24"]
theorem prop_1_24_b {f g : MvPolynomial (Fin 2) k} (hf : f ≠ 0) (hg : g ≠ 0) :
    resultantY f g = 0 ↔ ∃ h : MvPolynomial (Fin 2) k, 0 < degY h ∧ h ∣ f ∧ h ∣ g := by
  have hF : yPolyEquiv f ≠ 0 := (map_ne_zero_iff _ yPolyEquiv.injective).mpr hf
  unfold resultantY
  rw [resultant_eq_zero_iff_exists_common_factor hF]
  constructor
  · rintro ⟨H, hH, hHF, hHG⟩
    refine ⟨yPolyEquiv.symm H, ?_, ?_, ?_⟩
    · show 0 < (yPolyEquiv (yPolyEquiv.symm H)).degree
      rwa [AlgEquiv.apply_symm_apply]
    · simpa using map_dvd yPolyEquiv.symm hHF
    · simpa using map_dvd yPolyEquiv.symm hHG
  · rintro ⟨h, hh, hhf, hhg⟩
    exact ⟨yPolyEquiv h, hh, map_dvd yPolyEquiv hhf, map_dvd yPolyEquiv hhg⟩

/-- Proposition 1.24 (b) as printed fails for common factors in `k[X]`: $f = g = X$ have the common
factor $X$, but their resultant in $Y$ (two polynomials of degree 0 in $Y$) is 1. -/
theorem prop_1_24_b_counterexample :
    resultantY (X 0 : MvPolynomial (Fin 2) k) (X 0) ≠ 0 ∧
      ∃ h : MvPolynomial (Fin 2) k, ¬ IsUnit h ∧ h ∣ X 0 ∧ h ∣ X 0 := by
  refine ⟨?_, X 0, ?_, dvd_rfl, dvd_rfl⟩
  · simp [resultantY]
  · intro hu
    have := hu.map yPolyEquiv
    simp at this
    exact Polynomial.not_isUnit_X this

/-- Helper: Corollary 1.25 in terms of polynomials in `Y` with coefficients in `k[X]`. -/
lemma corollary_core {K : Type*} [Field K] [Algebra k K] (F G : Polynomial (Polynomial k))
    (hk : ∀ D : Polynomial (Polynomial k), D ∣ F → D ∣ G → IsUnit D) :
    ∀ D : Polynomial (Polynomial K),
      D ∣ F.map (Polynomial.mapRingHom (algebraMap k K)) →
      D ∣ G.map (Polynomial.mapRingHom (algebraMap k K)) → IsUnit D := by
  set φ := Polynomial.mapRingHom (algebraMap k K) with hφ
  have hφinj : Function.Injective φ :=
    Polynomial.map_injective _ (algebraMap k K).injective
  intro D hDF hDG
  by_cases hF0 : F = 0
  · subst hF0
    have hu : IsUnit G := hk G (dvd_zero G) dvd_rfl
    exact isUnit_of_dvd_unit hDG (hu.map (Polynomial.mapRingHom φ))
  by_cases hG0 : G = 0
  · subst hG0
    have hu : IsUnit F := hk F dvd_rfl (dvd_zero F)
    exact isUnit_of_dvd_unit hDF (hu.map (Polynomial.mapRingHom φ))
  have hFm : F.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr hF0
  by_cases hdeg : 0 < D.degree
  · exfalso
    have h1 := (resultant_eq_zero_iff_exists_common_factor hFm).mpr ⟨D, hdeg, hDF, hDG⟩
    rw [resultant_map_of_injective φ hφinj] at h1
    have h2 : F.resultant G = 0 := (map_eq_zero_iff φ hφinj).mp h1
    obtain ⟨H, hH, hHF, hHG⟩ := (resultant_eq_zero_iff_exists_common_factor hF0).mp h2
    have := Polynomial.degree_eq_zero_of_isUnit (hk H hHF hHG)
    rw [this] at hH
    exact lt_irrefl _ hH
  · have hD : D = Polynomial.C (D.coeff 0) := Polynomial.eq_C_of_degree_le_zero (not_lt.mp hdeg)
    set r := D.coeff 0 with hr
    rw [hD] at hDF hDG ⊢
    rw [Polynomial.isUnit_C]
    let S : Set (Polynomial k) := Set.range F.coeff ∪ Set.range G.coeff
    let I : Ideal (Polynomial k) := Ideal.span S
    obtain ⟨c, hc⟩ : ∃ c, I = Ideal.span {c} :=
      ⟨_, (Ideal.span_singleton_generator I).symm⟩
    have hcdvd : ∀ s ∈ S, c ∣ s := fun s hs =>
      Ideal.mem_span_singleton.mp (hc ▸ Ideal.subset_span hs)
    have hcF : Polynomial.C c ∣ F := (Polynomial.C_dvd_iff_dvd_coeff c F).mpr fun i =>
      hcdvd _ (Or.inl ⟨i, rfl⟩)
    have hcG : Polynomial.C c ∣ G := (Polynomial.C_dvd_iff_dvd_coeff c G).mpr fun i =>
      hcdvd _ (Or.inr ⟨i, rfl⟩)
    have hcu : IsUnit c := Polynomial.isUnit_C.mp (hk _ hcF hcG)
    have hItop : I = ⊤ := by rw [hc]; exact Ideal.span_singleton_eq_top.mpr hcu
    have hmap : Ideal.map φ I ≤ Ideal.span {r} := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨s, hs, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_span_singleton]
      rcases hs with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · have := (Polynomial.C_dvd_iff_dvd_coeff r _).mp hDF i
        rwa [Polynomial.coeff_map] at this
      · have := (Polynomial.C_dvd_iff_dvd_coeff r _).mp hDG i
        rwa [Polynomial.coeff_map] at this
    rw [hItop, Ideal.map_top] at hmap
    exact Ideal.span_singleton_eq_top.mp (top_le_iff.mp hmap)

/-- **Corollary 1.25** (p. 24): if `f` and `g` have no common factor in `k[X, Y]`, then they have no
common factor in `K[X, Y]` for any field `K` containing `k`. -/
@[kb "milne2006ec" "Ch. I, Cor. 1.25, pdf p. 24"]
theorem corollary_1_25 {f g : MvPolynomial (Fin 2) k}
    (h : ∀ d : MvPolynomial (Fin 2) k, d ∣ f → d ∣ g → IsUnit d) (K : Type*) [Field K]
    [Algebra k K] :
    ∀ d : MvPolynomial (Fin 2) K, d ∣ baseChange K f → d ∣ baseChange K g → IsUnit d := by
  intro d hdf hdg
  have hk : ∀ D : Polynomial (Polynomial k), D ∣ yPolyEquiv f → D ∣ yPolyEquiv g → IsUnit D := by
    intro D h1 h2
    have := h (yPolyEquiv.symm D) (by simpa using map_dvd yPolyEquiv.symm h1)
      (by simpa using map_dvd yPolyEquiv.symm h2)
    simpa using this.map yPolyEquiv
  have := corollary_core (K := K) (yPolyEquiv f) (yPolyEquiv g) hk (yPolyEquiv (k := K) d)
    (by rw [← yPolyEquiv_baseChange]; exact map_dvd _ hdf)
    (by rw [← yPolyEquiv_baseChange]; exact map_dvd _ hdg)
  simpa using this.map (yPolyEquiv (k := K)).symm

/-- The binary form $F(X, Y) = s_0X^m + s_1X^{m-1}Y + \cdots + s_mY^m$ of degree `m` attached to a
polynomial $f(T) = s_0T^m + \cdots + s_m$ of degree at most `m`, evaluated at `(x, y)`:
$F(x, y) = \sum_i f_i\, x^i y^{m - i}$, $f_i$ the coefficient of $T^i$. -/
noncomputable def binaryForm {K : Type*} [CommRing K] (f : Polynomial K) (m : ℕ) (x y : K) : K :=
  ∑ i ∈ Finset.range (m + 1), f.coeff i * x ^ i * y ^ (m - i)

/-- Helper: the binary form at `(x, 0)`. -/
lemma binaryForm_zero_right {K : Type*} [CommRing K] (f : Polynomial K) (m : ℕ) (x : K) :
    binaryForm f m x 0 = f.coeff m * x ^ m := by
  unfold binaryForm
  rw [Finset.sum_eq_single m]
  · simp
  · intro i hi him
    have : m - i ≠ 0 := by simp at hi; omega
    simp [this]
  · simp

/-- Helper: the binary form at `(x, 1)` is the value of the polynomial at `x`. -/
lemma binaryForm_one_right {K : Type*} [CommRing K] (f : Polynomial K) {m : ℕ}
    (hf : f.natDegree ≤ m) (x : K) : binaryForm f m x 1 = f.eval x := by
  unfold binaryForm
  rw [Polynomial.eval_eq_sum_range' (n := m + 1) (by omega)]
  simp [mul_comm]

/-- Helper: the binary form at `(x, y)` with `y` nonzero is `y ^ m` times the value at `x / y`. -/
lemma binaryForm_of_ne_zero {K : Type*} [Field K] (f : Polynomial K) {m : ℕ}
    (hf : f.natDegree ≤ m) (x : K) {y : K} (hy : y ≠ 0) :
    binaryForm f m x y = y ^ m * f.eval (x / y) := by
  unfold binaryForm
  rw [Polynomial.eval_eq_sum_range' (n := m + 1) (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := by simp at hi; omega
  have : y ^ m = y ^ i * y ^ (m - i) := by rw [← pow_add]; congr 1; omega
  rw [div_pow, this]
  field_simp

/-- **Proposition 1.26** (p. 25): the resultant of two binary forms $F$, $G$ of degrees `m`, `n`
(with $m + n > 0$) vanishes if and only if they have a common nontrivial zero in
$\mathbb P^1(k^{\mathrm{al}})$.  The forms are given by their dehomogenizations `f`, `g`
(`binaryForm`), and $\mathrm{Res}(F, G)$ is `f.resultant g m n`. -/
@[kb "milne2006ec" "Ch. I, Prop. 1.26, pdf p. 25"]
theorem prop_1_26 (f g : Polynomial k) {m n : ℕ} (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hmn : 0 < m + n) :
    f.resultant g m n = 0 ↔
      ∃ x y : AlgebraicClosure k, (x, y) ≠ (0, 0) ∧
        binaryForm (f.map (algebraMap k _)) m x y = 0 ∧
        binaryForm (g.map (algebraMap k _)) n x y = 0 := by
  have hf' : (f.map (algebraMap k (AlgebraicClosure k))).natDegree ≤ m :=
    (Polynomial.natDegree_map_le).trans hf
  have hg' : (g.map (algebraMap k (AlgebraicClosure k))).natDegree ≤ n :=
    (Polynomial.natDegree_map_le).trans hg
  have hinj : Function.Injective (algebraMap k (AlgebraicClosure k)) :=
    (algebraMap k (AlgebraicClosure k)).injective
  rw [prop_1_22 f g hf hg hmn]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨α, hα1, hα2⟩)
    · refine ⟨1, 0, by simp, ?_, ?_⟩
      · rw [binaryForm_zero_right, Polynomial.coeff_map, h1]; simp
      · rw [binaryForm_zero_right, Polynomial.coeff_map, h2]; simp
    · refine ⟨α, 1, by simp, ?_, ?_⟩
      · rw [binaryForm_one_right _ hf']; exact hα1
      · rw [binaryForm_one_right _ hg']; exact hα2
  · rintro ⟨x, y, hxy, h1, h2⟩
    by_cases hy : y = 0
    · subst hy
      left
      have hx : x ≠ 0 := by
        rintro rfl; exact hxy rfl
      rw [binaryForm_zero_right, Polynomial.coeff_map] at h1 h2
      refine ⟨?_, ?_⟩
      · exact hinj (by simpa [hx] using h1)
      · exact hinj (by simpa [hx] using h2)
    · right
      refine ⟨x / y, ?_, ?_⟩
      · rw [binaryForm_of_ne_zero _ hf' x hy] at h1
        simpa [hy] using h1
      · rw [binaryForm_of_ne_zero _ hg' x hy] at h2
        simpa [hy] using h2

end NumberFieldKB.MilneEC
