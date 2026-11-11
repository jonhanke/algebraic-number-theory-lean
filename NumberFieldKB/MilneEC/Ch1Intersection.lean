import NumberFieldKB.MilneEC.Ch1Affine
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Group.Translate
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Milne, Elliptic Curves, Chapter I, Section 1: intersection numbers

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, §1, subsection "Intersection numbers"
(pdf pp. 16–19): Proposition 1.8 (characterization of the intersection number by five properties),
Remark 1.9, Examples 1.10 and 1.12, Lemma 1.11, the intersection number at a point, Remark 1.13.

Conventions as in `Ch1Affine`: polynomials in `MvPolynomial (Fin 2) k`, $X$ = `X 0`, $Y$ = `X 1`; the
origin is the point `0 : Fin 2 → k`.

* `NoCommonFactorAtOrigin f g` is Milne's condition $(f, g) \in \mathcal F(k)$: `f` and `g` have no
  common factor `h` with $h(0,0) = 0$.
* `IsIntersectionNumber I` says that a function `I` satisfies Milne's properties (a)–(e) on
  $\mathcal F(k)$.  The functions are defined on all pairs; only their values on $\mathcal F(k)$ matter.
* `localIntersectionNumber f g` is the concrete candidate of the proof of Proposition 1.8 (after Fulton):
  the dimension of $k[X,Y]_{(X,Y)}/(f, g)$ as a `k`-vector space (`Module.finrank`, which is 0 when the
  dimension is infinite).
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC

variable {k : Type*} [Field k]

/-- Milne's $\mathcal F(k)$ (p. 16): the pairs `(f, g)` of polynomials in `k[X, Y]` having no common
factor `h` with $h(0, 0) = 0$. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of F(k), pdf p. 16"]
def NoCommonFactorAtOrigin (f g : MvPolynomial (Fin 2) k) : Prop :=
  ∀ h : MvPolynomial (Fin 2) k, h ∣ f → h ∣ g → eval 0 h ≠ 0

/-- Milne's properties (a)–(e) of Proposition 1.8 (p. 16) for a function
$I : \mathcal F(k) \to \mathbb N$, given as a function on all pairs. -/
@[kb "milne2006ec" "Ch. I, Prop. 1.8, properties (a)-(e), pdf p. 16"]
structure IsIntersectionNumber (I : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ) : Prop where
  /-- (a) $I(X, Y) = 1$. -/
  X_Y : I (X 0) (X 1) = 1
  /-- (b) $I(f, g) = I(g, f)$. -/
  symm : ∀ f g, NoCommonFactorAtOrigin f g → I f g = I g f
  /-- (c) $I(f, gh) = I(f, g) + I(f, h)$ for $(f, g), (f, h) \in \mathcal F(k)$. -/
  mul_right : ∀ f g h, NoCommonFactorAtOrigin f g → NoCommonFactorAtOrigin f h →
    I f (g * h) = I f g + I f h
  /-- (d) $I(f, g + hf) = I(f, g)$. -/
  add_mul_right : ∀ f g h, NoCommonFactorAtOrigin f g → I f (g + h * f) = I f g
  /-- (e) $I(f, g) = 0$ if $g(0, 0) \neq 0$. -/
  eq_zero : ∀ f g, NoCommonFactorAtOrigin f g → eval 0 g ≠ 0 → I f g = 0

/-- The maximal ideal $(X, Y)$ of `k[X, Y]`: the polynomials vanishing at the origin. -/
noncomputable def originIdeal (k : Type*) [Field k] : Ideal (MvPolynomial (Fin 2) k) :=
  RingHom.ker (eval (0 : Fin 2 → k))

instance originIdeal_isPrime : (originIdeal k).IsPrime :=
  RingHom.ker_isPrime _

/-- The local ring $k[X, Y]_{(0,0)}$ of the plane at the origin (p. 17). -/
abbrev LocalRingAtOrigin (k : Type*) [Field k] := Localization.AtPrime (originIdeal k)

/-- The quotient $k[X, Y]_{(0,0)}/(f, g)$. -/
abbrev LocalQuotient (f g : MvPolynomial (Fin 2) k) :=
  LocalRingAtOrigin k ⧸ Ideal.span {algebraMap _ (LocalRingAtOrigin k) f,
    algebraMap _ (LocalRingAtOrigin k) g}

/-- The intersection number at the origin as a dimension (proof of Proposition 1.8 and Remark 1.9,
p. 17, after Fulton): $\dim_k k[X, Y]_{(0,0)}/(f, g)$. -/
@[kb "milne2006ec" "Ch. I, Prop. 1.8 (proof) and Rem. 1.9, I(f,g) = dim k[X,Y]_(0,0)/(f,g), pdf p. 17"]
noncomputable def localIntersectionNumber (f g : MvPolynomial (Fin 2) k) : ℕ :=
  Module.finrank k (LocalQuotient f g)

/-- **Proposition 1.8, existence part, and the formula of Remark 1.9**, as a named statement (Milne
refers to Fulton 1969, III §3): for every field `k`, the dimension
$\dim_k k[X, Y]_{(0,0)}/(f, g)$ is finite for $(f, g) \in \mathcal F(k)$, and the function
`localIntersectionNumber` satisfies the properties (a)–(e). -/
@[kb "milne2006ec" "Ch. I, Prop. 1.8 (existence) and Rem. 1.9, pdf pp. 16-17"]
structure Prop1_8 : Prop where
  finite : ∀ (k : Type) [Field k] (f g : MvPolynomial (Fin 2) k), NoCommonFactorAtOrigin f g →
    Module.Finite k (LocalQuotient f g)
  isIntersectionNumber : ∀ (k : Type) [Field k],
    IsIntersectionNumber (localIntersectionNumber (k := k))

/-! ### Helper lemmas on `NoCommonFactorAtOrigin` -/

theorem NoCommonFactorAtOrigin.symm {f g : MvPolynomial (Fin 2) k}
    (h : NoCommonFactorAtOrigin f g) : NoCommonFactorAtOrigin g f :=
  fun d hg hf => h d hf hg

/-- Divisors of the second entry of a pair in $\mathcal F(k)$ stay in $\mathcal F(k)$. -/
theorem NoCommonFactorAtOrigin.of_dvd_right {f g g' : MvPolynomial (Fin 2) k}
    (h : NoCommonFactorAtOrigin f g) (hd : g' ∣ g) : NoCommonFactorAtOrigin f g' :=
  fun d hf hg' => h d hf (hg'.trans hd)

/-- Divisors of the first entry of a pair in $\mathcal F(k)$ stay in $\mathcal F(k)$. -/
theorem NoCommonFactorAtOrigin.of_dvd_left {f f' g : MvPolynomial (Fin 2) k}
    (h : NoCommonFactorAtOrigin f g) (hd : f' ∣ f) : NoCommonFactorAtOrigin f' g :=
  fun d hf' hg => h d (hf'.trans hd) hg

/-- Adding a multiple of the first entry does not change membership in $\mathcal F(k)$. -/
theorem ncf_add_mul_iff (f g h : MvPolynomial (Fin 2) k) :
    NoCommonFactorAtOrigin f (g + h * f) ↔ NoCommonFactorAtOrigin f g := by
  constructor
  · intro H d hf hg
    exact H d hf (dvd_add hg (hf.mul_left h))
  · intro H d hf hg
    exact H d hf ((dvd_add_left (hf.mul_left h)).mp hg)

theorem eval_zero_ne_zero_of_isUnit {d : MvPolynomial (Fin 2) k} (hd : IsUnit d) :
    eval (0 : Fin 2 → k) d ≠ 0 :=
  (hd.map (eval (0 : Fin 2 → k))).ne_zero

/-- If the variable `X i` does not divide `g`, then `(X i, g)` lies in $\mathcal F(k)$. -/
theorem ncf_X_of_not_dvd (i : Fin 2) {g : MvPolynomial (Fin 2) k} (hg : ¬ X i ∣ g) :
    NoCommonFactorAtOrigin (X i) g := by
  intro d hdX hdg
  obtain ⟨e, he⟩ := hdX
  rcases (X_prime (σ := Fin 2) (R := k) (i := i)).irreducible.isUnit_or_isUnit he with hu | hu
  · exact eval_zero_ne_zero_of_isUnit hu
  · exact absurd (by rw [he]; exact hu.mul_right_dvd.mpr hdg) hg

theorem eval_aeval_X_zero (v : Fin 2 → k) (p : Polynomial k) :
    eval v (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) k) p) = p.eval (v 0) := by
  have h := Polynomial.aeval_algHom_apply (aeval v : MvPolynomial (Fin 2) k →ₐ[k] k)
    (X 0 : MvPolynomial (Fin 2) k) p
  rw [← MvPolynomial.coe_aeval_eq_eval]
  change (aeval v) _ = _
  rw [← h]
  simp [Polynomial.aeval_def]

/-- Division by the monic polynomial $Y - p(X)$: $Y - p(X)$ divides $g(X, Y) - g(X, p(X))$. -/
theorem X1_sub_dvd (p : Polynomial k) (g : MvPolynomial (Fin 2) k) :
    (X 1 - Polynomial.aeval (X 0) p) ∣
      g - Polynomial.aeval (X 0) (aeval ![Polynomial.X, p] g) := by
  set φ : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
    (Polynomial.aeval (X 0 : MvPolynomial (Fin 2) k)).comp (aeval ![Polynomial.X, p]) with hφ
  change (X 1 - Polynomial.aeval (X 0) p) ∣ g - φ g
  induction g using MvPolynomial.induction_on with
  | C a => simp [hφ]
  | add f g hf hg =>
    have := dvd_add hf hg
    rw [map_add]
    convert this using 1
    ring
  | mul_X f i hf =>
    have hi : (X 1 - Polynomial.aeval (X 0) p) ∣ X i - φ (X i) := by
      fin_cases i
      · simp [hφ]
      · simp [hφ]
    have : f * X i - φ (f * X i) = (f - φ f) * X i + φ f * (X i - φ (X i)) := by
      rw [map_mul]; ring
    rw [this]
    exact dvd_add (hf.mul_right _) (hi.mul_left _)

theorem ncf_Y_sub_X_poly {p : Polynomial k} (hp : p.eval 0 = 0) :
    NoCommonFactorAtOrigin (X 0) (X 1 - Polynomial.aeval (X 0 : MvPolynomial (Fin 2) k) p) := by
  apply ncf_X_of_not_dvd
  intro hd
  have := map_dvd (eval (![0, 1] : Fin 2 → k)) hd
  rw [map_sub, eval_aeval_X_zero] at this
  simp [hp] at this

/-- Core of Lemma 1.11, for any `I` with properties (a)–(e). -/
theorem lemma_1_11_aux {I : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ}
    (hI : IsIntersectionNumber I) (p : Polynomial k) (hp : p.eval 0 = 0)
    (g : MvPolynomial (Fin 2) k) (hF : NoCommonFactorAtOrigin (X 1 - Polynomial.aeval (X 0) p) g) :
    I (X 1 - Polynomial.aeval (X 0) p) g =
      Polynomial.rootMultiplicity 0 (aeval ![Polynomial.X, p] g) := by
  set F : MvPolynomial (Fin 2) k := X 1 - Polynomial.aeval (X 0) p with hFdef
  set q : Polynomial k := aeval ![Polynomial.X, p] g with hq
  set s : MvPolynomial (Fin 2) k := Polynomial.aeval (X 0) q with hs
  obtain ⟨h, hh⟩ := X1_sub_dvd p g
  have hgs : g + (-h) * F = s := by linear_combination hh
  have hFs : NoCommonFactorAtOrigin F s := by
    rw [← hgs]; exact (ncf_add_mul_iff F g (-h)).mpr hF
  have hIs : I F g = I F s := by
    rw [← hgs]; exact (hI.add_mul_right F g (-h) hF).symm
  have hevF : eval (0 : Fin 2 → k) F = 0 := by
    rw [hFdef, map_sub, eval_aeval_X_zero]; simp [hp]
  have hq0 : q ≠ 0 := by
    intro h0
    have : s = 0 := by rw [hs, h0, map_zero]
    exact hFs F dvd_rfl (this ▸ dvd_zero F) hevF
  obtain ⟨u, hqu, hu⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq0 0
  set m := Polynomial.rootMultiplicity 0 q with hm
  simp only [map_zero, sub_zero] at hqu hu
  have hsU : s = X 0 ^ m * Polynomial.aeval (X 0) u := by
    rw [hs, hqu]; simp
  have hevU : eval (0 : Fin 2 → k) (Polynomial.aeval (X 0) u) ≠ 0 := by
    rw [eval_aeval_X_zero]
    intro h0
    exact hu (Polynomial.X_dvd_iff.mpr (by simpa [Polynomial.coeff_zero_eq_eval_zero] using h0))
  have hX0 : NoCommonFactorAtOrigin F (X 0 ^ m) :=
    hFs.of_dvd_right (by rw [hsU]; exact dvd_mul_right _ _)
  have hU : NoCommonFactorAtOrigin F (Polynomial.aeval (X 0) u) :=
    hFs.of_dvd_right (by rw [hsU]; exact dvd_mul_left _ _)
  have hpow : ∀ j : ℕ, NoCommonFactorAtOrigin F (X 0 ^ j) → I F (X 0 ^ j) = j * I F (X 0) := by
    intro j
    induction j with
    | zero =>
      intro hj
      simp only [pow_zero, zero_mul]
      exact hI.eq_zero F 1 hj (by simp)
    | succ j ih =>
      intro hj
      have h1 : NoCommonFactorAtOrigin F (X 0 ^ j) := hj.of_dvd_right (pow_dvd_pow _ (by omega))
      have h2 : NoCommonFactorAtOrigin F (X 0) := hj.of_dvd_right (dvd_pow_self _ (by omega))
      rw [pow_succ, hI.mul_right F _ _ h1 h2, ih h1]
      ring
  have hN : NoCommonFactorAtOrigin (X 0) F := ncf_Y_sub_X_poly hp
  have hI1 : I F (X 0) = 1 := by
    rw [hI.symm F _ hN.symm]
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr
      (by simpa [Polynomial.coeff_zero_eq_eval_zero] using hp : p.coeff 0 = 0)
    have hFe : F = X 1 + (-(Polynomial.aeval (X 0) r)) * X 0 := by
      rw [hFdef, hr]; simp; ring
    rw [hFe] at hN ⊢
    rw [hI.add_mul_right (X 0) (X 1) _ ((ncf_add_mul_iff _ _ _).mp hN)]
    exact hI.X_Y
  rw [hIs, hsU, hI.mul_right F _ _ hX0 hU, hpow m hX0, hI.eq_zero F _ hU hevU, hI1]
  simp

/-- Substituting $Y = 0$: $f(X, 0) \in k[X]$. -/
noncomputable def setYZero : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k :=
  aeval ![Polynomial.X, 0]

theorem eval_setYZero (f : MvPolynomial (Fin 2) k) :
    (setYZero f).eval 0 = eval (0 : Fin 2 → k) f := by
  have h : (Polynomial.aeval (0 : k)).comp (setYZero : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k) =
      aeval (0 : Fin 2 → k) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [setYZero]
  have := congrArg (fun φ => φ f) h
  simp only [AlgHom.comp_apply] at this
  rw [← MvPolynomial.coe_aeval_eq_eval]
  change _ = (aeval (0 : Fin 2 → k)) f
  rw [← this]
  simp [Polynomial.aeval_def, Polynomial.coeff_zero_eq_eval_zero]

theorem Y_dvd_of_setYZero_eq_zero {f : MvPolynomial (Fin 2) k} (h : setYZero f = 0) : X 1 ∣ f := by
  have := X1_sub_dvd (0 : Polynomial k) f
  have h' : aeval ![Polynomial.X, (0 : Polynomial k)] f = 0 := h
  simpa [h'] using this

section Unique

variable {I J : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ}

theorem IsIntersectionNumber.mul_left {T : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ}
    (hT : IsIntersectionNumber T) {a b g : MvPolynomial (Fin 2) k}
    (h : NoCommonFactorAtOrigin (a * b) g) : T (a * b) g = T a g + T b g := by
  have ha : NoCommonFactorAtOrigin g a := (h.of_dvd_left (dvd_mul_right a b)).symm
  have hb : NoCommonFactorAtOrigin g b := (h.of_dvd_left (dvd_mul_left b a)).symm
  rw [hT.symm _ _ h, hT.mul_right _ _ _ ha hb, hT.symm _ _ ha.symm, hT.symm _ _ hb.symm]

theorem IsIntersectionNumber.Y_value {T : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ}
    (hT : IsIntersectionNumber T) {g : MvPolynomial (Fin 2) k}
    (h : NoCommonFactorAtOrigin (X 1) g) :
    T (X 1) g = Polynomial.rootMultiplicity 0 (setYZero g) := by
  simpa [setYZero] using lemma_1_11_aux hT (0 : Polynomial k) (by simp) g (by simpa using h)

/-- The case where `f` is divisible by `Y`, in the induction of the uniqueness proof. -/
theorem unique_zero_case (hI : IsIntersectionNumber I) (hJ : IsIntersectionNumber J) (n : ℕ)
    (IH : ∀ m < n, ∀ f g, NoCommonFactorAtOrigin f g → J f g = m → I f g = J f g)
    {f g : MvPolynomial (Fin 2) k} (hfg : NoCommonFactorAtOrigin f g) (hn : J f g = n)
    (hg0 : eval (0 : Fin 2 → k) g = 0) (hz : setYZero f = 0) : I f g = J f g := by
  obtain ⟨h, rfl⟩ := Y_dvd_of_setYZero_eq_zero hz
  have hY : NoCommonFactorAtOrigin (X 1) g := hfg.of_dvd_left (dvd_mul_right _ _)
  have hh : NoCommonFactorAtOrigin h g := hfg.of_dvd_left (dvd_mul_left _ _)
  have hne : setYZero g ≠ 0 := by
    intro h0
    have := Y_dvd_of_setYZero_eq_zero h0
    have := hfg (X 1) (dvd_mul_right _ _) this
    simp at this
  have hroot : Polynomial.IsRoot (setYZero g) 0 := by
    rw [Polynomial.IsRoot, eval_setYZero, hg0]
  have hpos := (Polynomial.rootMultiplicity_pos hne).mpr hroot
  rw [hI.mul_left hfg, hI.Y_value hY] at *
  rw [hJ.mul_left hfg, hJ.Y_value hY] at hn ⊢
  rw [IH (J h g) (by omega) h g hh rfl]

/-- The Euclidean step of the uniqueness proof: `f(X, 0)` and `g(X, 0)` are nonzero with
`deg f(X, 0) ≤ deg g(X, 0)`. -/
theorem unique_euclid_step (hI : IsIntersectionNumber I) (hJ : IsIntersectionNumber J) (n : ℕ)
    (IH : ∀ m < n, ∀ f g, NoCommonFactorAtOrigin f g → J f g = m → I f g = J f g)
    (N : ℕ)
    (IHN : ∀ M < N, ∀ f g, NoCommonFactorAtOrigin f g → J f g = n →
      (setYZero f).natDegree + (setYZero g).natDegree = M → I f g = J f g)
    {f g : MvPolynomial (Fin 2) k} (hfg : NoCommonFactorAtOrigin f g) (hn : J f g = n)
    (hf0 : eval (0 : Fin 2 → k) f = 0) (hg0 : eval (0 : Fin 2 → k) g = 0)
    (hf : setYZero f ≠ 0) (hg : setYZero g ≠ 0)
    (hle : (setYZero f).natDegree ≤ (setYZero g).natDegree)
    (hN : (setYZero f).natDegree + (setYZero g).natDegree = N) : I f g = J f g := by
  set r := (setYZero f).natDegree with hr
  set s := (setYZero g).natDegree with hs
  set c : k := (setYZero g).leadingCoeff / (setYZero f).leadingCoeff with hc
  have hc0 : c ≠ 0 := div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg)
    (Polynomial.leadingCoeff_ne_zero.mpr hf)
  set a : MvPolynomial (Fin 2) k := C c * X 0 ^ (s - r) with ha
  set g' : MvPolynomial (Fin 2) k := g + (-a) * f with hg'
  have hfg' : NoCommonFactorAtOrigin f g' := (ncf_add_mul_iff f g (-a)).mpr hfg
  have hIg' : I f g' = I f g := hI.add_mul_right f g (-a) hfg
  have hJg' : J f g' = J f g := hJ.add_mul_right f g (-a) hfg
  rw [← hIg', ← hJg']
  have hg'0 : eval (0 : Fin 2 → k) g' = 0 := by rw [hg', map_add, map_mul, hf0, hg0]; simp
  by_cases hz : setYZero g' = 0
  · have h1 := unique_zero_case hI hJ n IH hfg'.symm (by rw [hJ.symm _ _ hfg'.symm, hJg']; exact hn)
      hf0 hz
    rw [hI.symm _ _ hfg', hJ.symm _ _ hfg']
    exact h1
  · set q : Polynomial k := Polynomial.C c * Polynomial.X ^ (s - r) * setYZero f with hq
    have hsg' : setYZero g' = setYZero g - q := by
      simp [hg', ha, hq, sub_eq_add_neg, setYZero]
    have hCX : (Polynomial.C c * Polynomial.X ^ (s - r) : Polynomial k) ≠ 0 := by
      simp [hc0]
    have hqnd : q.natDegree = s := by
      rw [hq, Polynomial.natDegree_mul hCX hf, Polynomial.natDegree_C_mul_X_pow _ _ hc0]
      omega
    have hq0 : q ≠ 0 := mul_ne_zero hCX hf
    have hqlc : q.leadingCoeff = (setYZero g).leadingCoeff := by
      rw [hq, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C_mul_X_pow, hc]
      have hlf := Polynomial.leadingCoeff_ne_zero.mpr hf
      field_simp
    have hdeg : (setYZero g).degree = q.degree := by
      rw [Polynomial.degree_eq_natDegree hg, Polynomial.degree_eq_natDegree hq0, hqnd]
    have hlt := Polynomial.degree_sub_lt_left hdeg hg hqlc.symm
    rw [← hsg'] at hlt
    have hlt' : (setYZero g').natDegree < s :=
      Polynomial.natDegree_lt_natDegree hz hlt
    exact IHN (r + (setYZero g').natDegree) (by omega) f g' hfg' (by rw [hJg']; exact hn) rfl

/-- Uniqueness in Proposition 1.8: two functions with properties (a)–(e) agree on $\mathcal F(k)$.
Fulton's induction: on the value of `J`, then on the degrees of $f(X, 0)$ and $g(X, 0)$.
Unconditional (no named statement is used). -/
@[kb "milne2006ec" "Ch. I, Prop. 1.8 (uniqueness), pdf p. 16"]
theorem intersectionNumber_unique (hI : IsIntersectionNumber I) (hJ : IsIntersectionNumber J) :
    ∀ f g, NoCommonFactorAtOrigin f g → I f g = J f g := by
  suffices H : ∀ n N : ℕ, ∀ f g, NoCommonFactorAtOrigin f g → J f g = n →
      (setYZero f).natDegree + (setYZero g).natDegree = N → I f g = J f g by
    intro f g h
    exact H _ _ f g h rfl rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  have IH' : ∀ m < n, ∀ f g, NoCommonFactorAtOrigin f g → J f g = m → I f g = J f g :=
    fun m hm f g h hJm => IH m hm _ f g h hJm rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IHN =>
  intro f g hfg hn hN
  by_cases hf0 : eval (0 : Fin 2 → k) f ≠ 0
  · rw [hI.symm _ _ hfg, hJ.symm _ _ hfg, hI.eq_zero g f hfg.symm hf0, hJ.eq_zero g f hfg.symm hf0]
  by_cases hg0 : eval (0 : Fin 2 → k) g ≠ 0
  · rw [hI.eq_zero f g hfg hg0, hJ.eq_zero f g hfg hg0]
  have hf0 := not_not.mp hf0
  have hg0 := not_not.mp hg0
  by_cases hz : setYZero f = 0
  · exact unique_zero_case hI hJ n IH' hfg hn hg0 hz
  by_cases hz' : setYZero g = 0
  · rw [hI.symm _ _ hfg, hJ.symm _ _ hfg]
    exact unique_zero_case hI hJ n IH' hfg.symm (by rw [← hJ.symm _ _ hfg]; exact hn) hf0 hz'
  rcases le_total (setYZero f).natDegree (setYZero g).natDegree with hle | hle
  · exact unique_euclid_step hI hJ n IH' N IHN hfg hn hf0 hg0 hz hz' hle hN
  · rw [hI.symm _ _ hfg, hJ.symm _ _ hfg]
    exact unique_euclid_step hI hJ n IH' N
      (fun M hM f g h hJn hM' => by
        rw [hI.symm _ _ h, hJ.symm _ _ h]
        exact IHN M hM g f h.symm (by rw [← hJ.symm _ _ h]; exact hJn) (by omega))
      hfg.symm (by rw [← hJ.symm _ _ hfg]; exact hn) hg0 hf0 hz' hz hle (by omega)

end Unique

/-- **Proposition 1.8** (p. 16): there is a unique map $I : \mathcal F(k) \to \mathbb N$ with the
properties (a)–(e).  Existence is the named statement `Prop1_8` (the dimension of the local quotient);
uniqueness is `intersectionNumber_unique`, proved from the axioms alone. -/
@[kb "milne2006ec" "Ch. I, Prop. 1.8, pdf p. 16"]
theorem prop_1_8 (h : Prop1_8) (k : Type) [Field k] :
    (∃ I : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ, IsIntersectionNumber I) ∧
    ∀ I J : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ,
      IsIntersectionNumber I → IsIntersectionNumber J →
      ∀ f g, NoCommonFactorAtOrigin f g → I f g = J f g :=
  ⟨⟨_, h.isIntersectionNumber k⟩, fun _ _ hI hJ => intersectionNumber_unique hI hJ⟩

/-- **Lemma 1.11** (p. 18): if $f(0) = 0$, then $I(Y - f(X), g(X, Y)) = m$, where $X^m$ is the exact
power of $X$ dividing $g(X, f(X))$.  Proved for every function `I` with the properties (a)–(e). Here
`f` is a one-variable polynomial `p`, $Y - f(X)$ is `X 1 - Polynomial.aeval (X 0) p`, $g(X, f(X))$ is
`aeval ![Polynomial.X, p] g`, and `m` is its root multiplicity at 0. -/
@[kb "milne2006ec" "Ch. I, Lem. 1.11, pdf p. 18"]
theorem lemma_1_11 {I : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ}
    (hI : IsIntersectionNumber I) (p : Polynomial k) (hp : p.eval 0 = 0)
    (g : MvPolynomial (Fin 2) k) (hF : NoCommonFactorAtOrigin (X 1 - Polynomial.aeval (X 0) p) g) :
    I (X 1 - Polynomial.aeval (X 0) p) g =
      Polynomial.rootMultiplicity 0 (aeval ![Polynomial.X, p] g) :=
  lemma_1_11_aux hI p hp g hF

/-- **Example 1.10** (p. 17): $I(Y^2 - X^2(X + 1), X) = I(Y^2, X) = 2$, for every function with the
properties (a)–(e). -/
@[kb "milne2006ec" "Ch. I, Ex. 1.10, pdf p. 17"]
theorem example_1_10 {I : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ}
    (hI : IsIntersectionNumber I) :
    I (X 1 ^ 2 - X 0 ^ 2 * (X 0 + 1)) (X 0) = 2 := by
  have hN : NoCommonFactorAtOrigin (X 0) (X 1 ^ 2 - X 0 ^ 2 * (X 0 + 1) : MvPolynomial (Fin 2) k) := by
    apply ncf_X_of_not_dvd
    intro hd
    have := map_dvd (eval (![0, 1] : Fin 2 → k)) hd
    simp at this
  have hN2 : NoCommonFactorAtOrigin (X 0) (X 1 ^ 2 : MvPolynomial (Fin 2) k) := by
    have e : (X 1 ^ 2 - X 0 ^ 2 * (X 0 + 1) : MvPolynomial (Fin 2) k) =
        X 1 ^ 2 + (-(X 0 * (X 0 + 1))) * X 0 := by ring
    rw [e] at hN
    exact (ncf_add_mul_iff _ _ _).mp hN
  have hY : NoCommonFactorAtOrigin (X 0) (X 1 : MvPolynomial (Fin 2) k) :=
    hN2.of_dvd_right (dvd_pow_self _ (by norm_num))
  rw [hI.symm _ _ hN.symm]
  have e : (X 1 ^ 2 - X 0 ^ 2 * (X 0 + 1) : MvPolynomial (Fin 2) k) =
      X 1 ^ 2 + (-(X 0 * (X 0 + 1))) * X 0 := by ring
  rw [e, hI.add_mul_right _ _ _ hN2, pow_two, hI.mul_right _ _ _ hY hY, hI.X_Y]

/-- The intersection number $I(P, C_f \cap C_g)$ of two affine plane curves at a point $P = (a, b)$
(p. 18): $I(f(X + a, Y + b), g(X + a, Y + b))$, computed over the field `K` of definition of `P`. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of I(P, C_f ∩ C_g), pdf p. 18"]
noncomputable def intersectionNumberAt (f g : MvPolynomial (Fin 2) k) {K : Type*} [Field K]
    [Algebra k K] (P : K × K) : ℕ :=
  localIntersectionNumber (translate f P) (translate g P)

/-- `P` is an **isolated point** of $C_f \cap C_g$ (p. 18): `f` and `g` have no common factor vanishing
at `P` (over the field `K` of `P`). -/
@[kb "milne2006ec" "Ch. I, §1, Def. of isolated point of C_f ∩ C_g, pdf p. 18"]
def IsIsolatedPoint (f g : MvPolynomial (Fin 2) k) {K : Type*} [Field K] [Algebra k K]
    (P : K × K) : Prop :=
  NoCommonFactorAtOrigin (translate f P) (translate g P)

/-- **Cusp** (Example 1.12, p. 18): a double point `P` with only one tangent line `L` (over the
algebraic closure of the field of `P`), and $I(P, L \cap C) = 3$. The line is given by a linear form in
the translated coordinates, so $I(P, L \cap C)$ is the intersection number at the origin of `L` and the
Taylor expansion of `f` at `P`. -/
@[kb "milne2006ec" "Ch. I, Ex. 1.12, Def. of cusp, pdf p. 18"]
def IsCusp (f : MvPolynomial (Fin 2) k) {K : Type*} [Field K] [Algebra k K] (P : K × K) : Prop :=
  IsSingularPoint f P ∧ multiplicityAt f P = 2 ∧
    ∃ L : MvPolynomial (Fin 2) (AlgebraicClosure K), IsTangentAt f P L ∧
      (∀ L', IsTangentAt f P L' → Associated L' L) ∧
      localIntersectionNumber L (baseChange (AlgebraicClosure K) (translate f P)) = 3

theorem ncf_Y_cusp : NoCommonFactorAtOrigin (X 1) (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) := by
  apply ncf_X_of_not_dvd
  intro hd
  have := map_dvd (eval (![1, 0] : Fin 2 → k)) hd
  simp at this

/-- The homogeneous components of $Y^2 - X^3$. -/
theorem homogeneousComponent_cusp (i : ℕ) :
    homogeneousComponent i (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) =
      (if i = 2 then X 1 ^ 2 else 0) - (if i = 3 then X 0 ^ 3 else 0) := by
  have h1 : (X 1 ^ 2 : MvPolynomial (Fin 2) k) ∈ homogeneousSubmodule (Fin 2) k 2 := by
    simpa using (isHomogeneous_X k (1 : Fin 2)).pow 2
  have h0 : (X 0 ^ 3 : MvPolynomial (Fin 2) k) ∈ homogeneousSubmodule (Fin 2) k 3 := by
    simpa using (isHomogeneous_X k (0 : Fin 2)).pow 3
  rw [map_sub, homogeneousComponent_of_mem h1, homogeneousComponent_of_mem h0]

/-- The origin has multiplicity two on $Y^2 = X^3$, and the lowest form is $Y^2$. -/
theorem order_cusp : order (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) = 2 := by
  have h2 : 2 ∈ {i | homogeneousComponent i (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) ≠ 0} := by
    simp only [Set.mem_ofPred_eq, homogeneousComponent_cusp]
    simp
  refine le_antisymm (Nat.sInf_le h2) (le_csInf ⟨2, h2⟩ ?_)
  intro i hi
  by_contra hlt
  simp only [Set.mem_ofPred_eq, homogeneousComponent_cusp] at hi
  apply hi
  have : i ≠ 2 := by omega
  have : i ≠ 3 := by omega
  simp [*]

/-- **Example 1.12** (p. 18), the computation: $I(Y^2 - X^3, Y) = I(X^3, Y) = 3$, for every function
with the properties (a)–(e). -/
@[kb "milne2006ec" "Ch. I, Ex. 1.12, pdf p. 18"]
theorem example_1_12 {I : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ}
    (hI : IsIntersectionNumber I) :
    I (X 1 ^ 2 - X 0 ^ 3) (X 1) = 3 := by
  have hN : NoCommonFactorAtOrigin (X 1) (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) :=
    ncf_Y_cusp
  rw [hI.symm _ _ hN.symm]
  have := lemma_1_11_aux hI (0 : Polynomial k) (by simp) (X 1 ^ 2 - X 0 ^ 3)
    (by simpa using hN)
  simp at this
  have e : (-Polynomial.X ^ 3 : Polynomial k) =
      (Polynomial.X - Polynomial.C 0) ^ 3 * Polynomial.C (-1) := by simp
  rw [this, e, Polynomial.rootMultiplicity_mul (by simp), Polynomial.rootMultiplicity_X_sub_C_pow,
    Polynomial.rootMultiplicity_eq_zero (by simp)]

/-- **Example 1.12** (p. 18): the origin is a cusp of $Y^2 = X^3$ (given the named statement
`Prop1_8`, which makes the dimension satisfy (a)–(e)). -/
@[kb "milne2006ec" "Ch. I, Ex. 1.12, pdf p. 18"]
theorem example_1_12_isCusp (h : Prop1_8) (k : Type) [Field k] :
    IsCusp (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) ((0, 0) : k × k) := by
  have htr : translate (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) ((0, 0) : k × k) =
      X 1 ^ 2 - X 0 ^ 3 := by
    simp [translate]
  have hlow : lowestForm (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) = X 1 ^ 2 := by
    rw [lowestForm, order_cusp, homogeneousComponent_cusp]
    simp
  refine ⟨?_, ?_, X 1, ?_, ?_, ?_⟩
  · simp [IsSingularPoint, affinePoints, evalAt, dX, dY]
  · rw [multiplicityAt, htr, order_cusp]
  · refine ⟨X_ne_zero 1, isHomogeneous_X _ _, ?_⟩
    rw [htr, hlow]
    simp
  · intro L' hL'
    obtain ⟨hne, hhom, hdvd⟩ := hL'
    rw [htr, hlow] at hdvd
    simp only [map_pow, map_X] at hdvd
    obtain ⟨i, hi, hass⟩ := (dvd_prime_pow (X_prime (σ := Fin 2)
      (R := AlgebraicClosure k) (i := 1)) 2).mp hdvd
    obtain ⟨u, hu⟩ := hass
    have hdeg := hhom.totalDegree hne
    obtain ⟨c, hcu, hc⟩ := (isUnit_iff_eq_C_of_isReduced).mp u.isUnit
    have hc0 : c ≠ 0 := hcu.ne_zero
    have h3 := congrArg totalDegree hu
    rw [hc, totalDegree_mul_of_isDomain hne (by simpa using hc0)] at h3
    simp [hdeg] at h3
    have : i = 1 := by omega
    subst this
    exact ⟨u, by simpa using hu⟩
  · rw [htr]
    have hI := h.isIntersectionNumber (AlgebraicClosure k)
    have e : baseChange (AlgebraicClosure k) (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) =
        X 1 ^ 2 - X 0 ^ 3 := by simp
    rw [e, hI.symm _ _ ncf_Y_cusp]
    exact example_1_12 hI

/-- **Remark 1.13** (p. 19), as a named statement (Milne refers to Fulton 1969, p. 75). Let `P` be an
isolated point of $C_f \cap C_g$, with coordinates in `K`; tangent lines are taken over the algebraic
closure of `K`. Then (i) $I(P, C \cap D) = 1$ if and only if `P` is nonsingular on both curves and the
tangent lines there are distinct; (ii) $I(P, C \cap D) \geq m_P(C)\, m_P(D)$, with equality if and only if
`C` and `D` have no tangent line in common at `P`. -/
@[kb "milne2006ec" "Ch. I, Rem. 1.13, pdf p. 19"]
structure Remark1_13 : Prop where
  eq_one_iff : ∀ (k : Type) [Field k] (K : Type) [Field K] [Algebra k K]
    (f g : MvPolynomial (Fin 2) k) (P : K × K), P ∈ affinePoints f K → P ∈ affinePoints g K →
    IsIsolatedPoint f g P →
    (intersectionNumberAt f g P = 1 ↔ IsNonsingularPoint f P ∧ IsNonsingularPoint g P ∧
      ¬ Associated (tangentLine f P) (tangentLine g P))
  ge_mul : ∀ (k : Type) [Field k] (K : Type) [Field K] [Algebra k K]
    (f g : MvPolynomial (Fin 2) k) (P : K × K), P ∈ affinePoints f K → P ∈ affinePoints g K →
    IsIsolatedPoint f g P →
    multiplicityAt f P * multiplicityAt g P ≤ intersectionNumberAt f g P ∧
    (intersectionNumberAt f g P = multiplicityAt f P * multiplicityAt g P ↔
      ¬ ∃ L : MvPolynomial (Fin 2) (AlgebraicClosure K), IsTangentAt f P L ∧ IsTangentAt g P L)

end NumberFieldKB.MilneEC
