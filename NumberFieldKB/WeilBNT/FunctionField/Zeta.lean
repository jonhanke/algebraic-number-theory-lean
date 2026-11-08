import NumberFieldKB.WeilBNT.FunctionField.Divisor
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The zeta function of a global function field (Weil VI, VII.§6 Thm. 4)

$k$ is a global function field over $\mathbb F_q$ whose field of constants is $\mathbb F_q$
(`IsConstantField Fq k`: every element of $k$ algebraic over $\mathbb F_q$ is in $\mathbb F_q$).

* **`riemannRochSpace a`** $=A(\mathfrak a)=\{\xi\in k:\xi=0\text{ or }\operatorname{div}\xi+\mathfrak a\succ0\}$
  (Weil VI.§2, text p. 100, $L(\mathfrak a)$ in the divisor case, $E=k$), an $\mathbb F_q$-subspace;
  **`ell a`** $=\lambda(\mathfrak a)$ its dimension.
* **`principalDivisors`**, the degree-zero class group **`ClassGroup0`** $D_0(k)/P(k)$ and the class number `h`.
* **`effCount n`** $=A_n$, the number of effective divisors of degree $n$, and the zeta series
  **`zetaSeries`** $Z(u)=\sum_n A_nu^n\in\mathbb Z[[u]]$, so that $\zeta_k(s)=Z(q^{-s})$ (Weil VII.§6, p. 130: the
  Dirichlet series $\sum_{\mathfrak a\succ0}q^{-s\deg\mathfrak a}$ of the integral divisors).

**`WeilZetaInputs Fq k`** is a *named input* bundling four results that are proved elsewhere or later in Weil:
Riemann–Roch for divisors (Weil VI.§2 Thm. 2, Tau Ceti `isRiemannRochDivisor_weilDifferentialDivisor`), finiteness of
the class number (Weil VI.§1 text p. 97, Tau Ceti `finite_ker_degreeClass`), finiteness of the effective divisors of
given degree (Tau Ceti `finite_setOf_isEffective_degree_le`), the existence of a divisor of degree $1$ (Weil
VII.§5 Cor. 5, F. K. Schmidt), and that principal divisors have degree $0$ (Weil VI.§1 text p. 97, from the product
formula IV.§4 Thm. 5; Tau Ceti `Divisor/ProductFormula.lean`). It is not equivalent to the conclusion: it says nothing about the zeta function.

* **`weil_VII_6_thm4`** (Weil VII.§6 Thm. 4): there is $P\in\mathbb Z[u]$ of degree $2g$ with
  $Z(u)(1-u)(1-qu)=P(u)$, $P(0)=1$, $P(1)=h$, and $P(u)=q^gu^{2g}P(1/qu)$ (in coefficients:
  $c_{2g-i}\,q^i=q^g\,c_i$).
-/

open scoped Polynomial
open IsDedekindDomain

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable (Fq k : Type*) [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

/-- $\mathbb F_q$ is the full field of constants of $k$: it is algebraically closed in $k$. -/
def IsConstantField : Prop := ∀ y : k, IsAlgebraic Fq y → y ∈ Set.range (algebraMap Fq k)

variable {Fq k}

namespace Divisor

theorem rr_cond_iff (a : Divisor Fq k) (f : k) :
    (f = 0 ∨ ∀ v : Place Fq k, -a v ≤ v.ord f) ↔
      ∀ v : Place Fq k, v.valuation f ≤ WithZero.exp (a v) := by
  by_cases hf : f = 0
  · subst hf
    simp
  · have key : ∀ v : Place Fq k, (-a v ≤ v.ord f ↔ v.valuation f ≤ WithZero.exp (a v)) := by
      intro v
      have hv : v.valuation f ≠ 0 := by simpa using hf
      rw [← WithZero.log_le_iff_le_exp hv, Place.ord]
      omega
    simp [hf, key]

/-- **The space $A(\mathfrak a)$** of $\xi\in k$ with $\xi=0$ or $\operatorname{ord}_v\xi\ge-a(v)$ for all $v$. -/
def riemannRochSpace (a : Divisor Fq k) : Submodule Fq k where
  carrier := {f | f = 0 ∨ ∀ v : Place Fq k, -a v ≤ v.ord f}
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq, rr_cond_iff] at hf hg ⊢
    intro v
    exact (v.valuation.map_add f g).trans (max_le (hf v) (hg v))
  zero_mem' := Or.inl rfl
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq, rr_cond_iff] at hf ⊢
    intro v
    rw [Algebra.smul_def, map_mul]
    have h1 : v.valuation (algebraMap Fq k c) ≤ 1 := v.algebraMap_mem_integers c
    calc v.valuation (algebraMap Fq k c) * v.valuation f ≤ 1 * v.valuation f :=
          mul_le_mul_left h1 _
      _ ≤ _ := by rw [one_mul]; exact hf v

theorem mem_riemannRochSpace_iff (a : Divisor Fq k) (f : k) :
    f ∈ a.riemannRochSpace ↔ ∀ v : Place Fq k, v.valuation f ≤ WithZero.exp (a v) :=
  rr_cond_iff a f

/-- $\lambda(\mathfrak a)=\dim_{\mathbb F_q}A(\mathfrak a)$. -/
def ell (a : Divisor Fq k) : ℕ := Module.finrank Fq a.riemannRochSpace

end Divisor

variable (Fq k) in
/-- The principal divisors $P(k)$. -/
def principalDivisors : AddSubgroup (Divisor Fq k) :=
  AddMonoidHom.range
    { toFun := fun f : Additive kˣ => Divisor.div (Additive.toMul f)
      map_zero' := Divisor.div_one
      map_add' := fun f g => Divisor.div_mul _ _ }

variable (Fq k) in
/-- The group $D_0(k)/P(k)$ of divisor classes of degree $0$. -/
abbrev ClassGroup0 : Type _ :=
  (Divisor.deg (Fq := Fq) (k := k)).ker ⧸ (principalDivisors Fq k).addSubgroupOf Divisor.deg.ker

variable (Fq k) in
/-- $A_n$, the number of effective divisors of degree $n$. -/
def effCount (n : ℕ) : ℕ := Nat.card {a : Divisor Fq k // 0 ≤ a ∧ Divisor.deg a = n}

variable (Fq k) in
/-- **The zeta series** $Z(u)=\sum_{n\ge0}A_nu^n$, so that $\zeta_k(s)=Z(q^{-s})$. -/
def zetaSeries : PowerSeries ℤ := PowerSeries.mk fun n => (effCount Fq k n : ℤ)

variable (Fq k) in
/-- **Named input** for Weil VII.§6 Thm. 4: Riemann–Roch with genus $g$ and a canonical divisor $\mathfrak c$
(Weil VI.§2 Thm. 2), finite-dimensionality of the $A(\mathfrak a)$, finiteness of $D_0(k)/P(k)$ (VI.§1 p. 97), finiteness
of the effective divisors of each degree, a divisor of degree $1$ (VII.§5 Cor. 5), and $\deg\operatorname{div}\xi=0$
(VI.§1 p. 97). -/
structure WeilZetaInputs : Prop where
  riemannRoch : ∃ (g : ℕ) (c : Divisor Fq k), ∀ a : Divisor Fq k,
    (a.ell : ℤ) = Divisor.deg a + 1 - g + (c - a).ell
  finiteDimensional : ∀ a : Divisor Fq k, FiniteDimensional Fq a.riemannRochSpace
  finite_classGroup0 : Finite (ClassGroup0 Fq k)
  finite_effective : ∀ n : ℤ, {a : Divisor Fq k | 0 ≤ a ∧ Divisor.deg a = n}.Finite
  exists_deg_one : ∃ a : Divisor Fq k, Divisor.deg a = 1
  deg_div : ∀ f : kˣ, Divisor.deg (Divisor.div f : Divisor Fq k) = 0

/-- The genus: the integer $g$ of Riemann–Roch (Weil VI.§2 Def. 1), from the inputs. -/
def WeilZetaInputs.genus (H : WeilZetaInputs Fq k) : ℕ := H.riemannRoch.choose

/-! ### The algebraic part: from the shape of `A_n` to the polynomial `P` -/

/-- The coefficient `A m - (q+1) A (m-1) + q A (m-2)` of `Z(u)(1-u)(1-qu)`. -/
def ppCoeff (q : ℕ) (A : ℤ → ℤ) (m : ℤ) : ℤ := A m - (q + 1) * A (m - 1) + q * A (m - 2)

/-- The numerical properties of `A_n = #{effective divisors of degree n}` that suffice for the
rationality and functional equation. -/
structure ZetaAlg (q g h : ℕ) (A : ℤ → ℤ) : Prop where
  two_le : 2 ≤ q
  neg : ∀ n : ℤ, n < 0 → A n = 0
  zero : A 0 = 1
  big : ∀ n : ℤ, 2 * (g : ℤ) - 1 ≤ n →
    ((q : ℚ) - 1) * (A n : ℚ) = h * ((q : ℚ) ^ (n + 1 - (g : ℤ)) - 1)
  sym : ∀ n : ℤ, ((q : ℚ) - 1) * (A n : ℚ) =
    (q : ℚ) ^ (n + 1 - (g : ℤ)) * (((q : ℚ) - 1) * (A (2 * (g : ℤ) - 2 - n) : ℚ)) +
      h * ((q : ℚ) ^ (n + 1 - (g : ℤ)) - 1)

section Alg

variable {q g h : ℕ} {A : ℤ → ℤ}

theorem ZetaAlg.pp_eq_zero (hd : ZetaAlg q g h A) (m : ℤ) (hm : 2 * (g : ℤ) + 1 ≤ m) :
    ppCoeff q A m = 0 := by
  have hx : (1 : ℚ) < q := by exact_mod_cast hd.two_le
  have hx0 : (q : ℚ) ≠ 0 := by positivity
  have h1 := hd.big m (by omega)
  have h2 := hd.big (m - 1) (by omega)
  have h3 := hd.big (m - 2) (by omega)
  have e1 : (q : ℚ) ^ (m + 1 - (g : ℤ)) = (q : ℚ) ^ (m - 2 + 1 - (g : ℤ)) * q * q := by
    rw [show m + 1 - (g : ℤ) = (m - 2 + 1 - g) + 1 + 1 by ring, zpow_add_one₀ hx0, zpow_add_one₀ hx0]
  have e2 : (q : ℚ) ^ (m - 1 + 1 - (g : ℤ)) = (q : ℚ) ^ (m - 2 + 1 - (g : ℤ)) * q := by
    rw [show m - 1 + 1 - (g : ℤ) = (m - 2 + 1 - g) + 1 by ring, zpow_add_one₀ hx0]
  rw [e1] at h1
  rw [e2] at h2
  have : ((q : ℚ) - 1) * (ppCoeff q A m : ℚ) = 0 := by
    unfold ppCoeff
    push_cast
    linear_combination h1 - ((q : ℚ) + 1) * h2 + (q : ℚ) * h3
  have h0 : ((q : ℚ) - 1) ≠ 0 := by linarith
  have : (ppCoeff q A m : ℚ) = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h0
    · exact h
  exact_mod_cast this

theorem ZetaAlg.pp_symm (hd : ZetaAlg q g h A) (i : ℕ) (hi : i ≤ 2 * g) :
    ppCoeff q A (2 * (g : ℤ) - i) * (q : ℤ) ^ i = (q : ℤ) ^ g * ppCoeff q A i := by
  have hx : (1 : ℚ) < q := by exact_mod_cast hd.two_le
  have hx0 : (q : ℚ) ≠ 0 := by positivity
  have s0 := hd.sym (2 * (g : ℤ) - i)
  have s1 := hd.sym (2 * (g : ℤ) - i - 1)
  have s2 := hd.sym (2 * (g : ℤ) - i - 2)
  rw [show 2 * (g : ℤ) - 2 - (2 * g - i) = i - 2 by ring] at s0
  rw [show 2 * (g : ℤ) - 2 - (2 * g - i - 1) = i - 1 by ring] at s1
  rw [show 2 * (g : ℤ) - 2 - (2 * g - i - 2) = i by ring] at s2
  rw [show (2 * (g : ℤ) - i) + 1 - g = ((g : ℤ) - 1 - i) + 1 + 1 by ring, zpow_add_one₀ hx0,
    zpow_add_one₀ hx0] at s0
  rw [show (2 * (g : ℤ) - i - 1) + 1 - g = ((g : ℤ) - 1 - i) + 1 by ring, zpow_add_one₀ hx0] at s1
  rw [show (2 * (g : ℤ) - i - 2) + 1 - g = ((g : ℤ) - 1 - i) by ring] at s2
  have hg : (q : ℚ) ^ g = (q : ℚ) ^ i * ((q : ℚ) ^ ((g : ℤ) - 1 - i) * q) := by
    rw [← zpow_add_one₀ hx0, ← zpow_natCast (q : ℚ) i, ← zpow_add₀ hx0, ← zpow_natCast (q : ℚ) g]
    congr 1
    ring
  have key : ((q : ℚ) - 1) * ((ppCoeff q A (2 * (g : ℤ) - i) * (q : ℤ) ^ i : ℤ) : ℚ) =
      ((q : ℚ) - 1) * (((q : ℤ) ^ g * ppCoeff q A i : ℤ) : ℚ) := by
    unfold ppCoeff
    push_cast
    rw [hg]
    linear_combination (q : ℚ) ^ i * (s0 - ((q : ℚ) + 1) * s1 + (q : ℚ) * s2)
  have h0 : ((q : ℚ) - 1) ≠ 0 := by linarith
  have := mul_left_cancel₀ h0 key
  exact_mod_cast this

theorem ZetaAlg.sum_pp (hd : ZetaAlg q g h A) (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), ppCoeff q A m = A N - q * A ((N : ℤ) - 1) := by
  induction N with
  | zero =>
    simp [ppCoeff, hd.neg (-1) (by norm_num), hd.neg (-2) (by norm_num)]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    unfold ppCoeff
    push_cast
    have : (N : ℤ) + 1 - 2 = (N : ℤ) - 1 := by ring
    rw [this]
    ring

theorem ZetaAlg.coeff_mul (hd : ZetaAlg q g h A) (Z : PowerSeries ℤ)
    (hZ : ∀ n : ℕ, PowerSeries.coeff n Z = A n) (m : ℕ) :
    PowerSeries.coeff m (Z * ((1 - PowerSeries.X) * (1 - (q : PowerSeries ℤ) * PowerSeries.X))) =
      ppCoeff q A m := by
  have e : Z * ((1 - PowerSeries.X) * (1 - (q : PowerSeries ℤ) * PowerSeries.X)) =
      Z - ((q : ℤ) + 1) • (Z * PowerSeries.X ^ 1) + (q : ℤ) • (Z * PowerSeries.X ^ 2) := by
    rw [zsmul_eq_mul, zsmul_eq_mul]
    push_cast
    ring
  rw [e]
  simp only [map_sub, map_add, map_zsmul, smul_eq_mul, PowerSeries.coeff_mul_X_pow']
  unfold ppCoeff
  rcases m with _ | _ | m
  · simp [hZ, hd.neg (-1) (by norm_num), hd.neg (-2) (by norm_num)]
  · simp [hZ, hd.neg (-1) (by norm_num)]
  · have h3 : (m : ℤ) + 1 + 1 - 2 = m := by ring
    simp [hZ, h3]

theorem ZetaAlg.exists_poly (hd : ZetaAlg q g h A) (Z : PowerSeries ℤ)
    (hZ : ∀ n : ℕ, PowerSeries.coeff n Z = A n) :
    ∃ P : ℤ[X], P.natDegree = 2 * g ∧ P.eval 0 = 1 ∧ P.eval 1 = h ∧
      Z * ((1 - PowerSeries.X) * (1 - (q : PowerSeries ℤ) * PowerSeries.X)) = (P : PowerSeries ℤ) ∧
      ∀ i ≤ 2 * g, P.coeff (2 * g - i) * (q : ℤ) ^ i = (q : ℤ) ^ g * P.coeff i := by
  set P : ℤ[X] := ∑ m ∈ Finset.range (2 * g + 1), Polynomial.monomial m (ppCoeff q A m) with hP
  have hcoeff : ∀ j : ℕ, P.coeff j = ppCoeff q A j := by
    intro j
    rw [hP, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    by_cases hj : j ≤ 2 * g
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · intro hj'; exact absurd (Finset.mem_range.mpr (by omega)) hj'
    · rw [Finset.sum_eq_zero]
      · exact (hd.pp_eq_zero j (by omega)).symm
      · intro b hb
        have : b ≠ j := by
          have := Finset.mem_range.mp hb
          omega
        simp [this]
  have hx : (1 : ℚ) < q := by exact_mod_cast hd.two_le
  have hq0 : (q : ℤ) ≠ 0 := by
    have := hd.two_le
    omega
  have hpp0 : ppCoeff q A 0 = 1 := by
    unfold ppCoeff
    simp [hd.zero, hd.neg (-1) (by norm_num), hd.neg (-2) (by norm_num)]
  have hsymm : ∀ i ≤ 2 * g, P.coeff (2 * g - i) * (q : ℤ) ^ i = (q : ℤ) ^ g * P.coeff i := by
    intro i hi
    rw [hcoeff, hcoeff]
    have := hd.pp_symm i hi
    rw [show ((2 * g - i : ℕ) : ℤ) = 2 * (g : ℤ) - i by omega]
    exact this
  refine ⟨P, ?_, ?_, ?_, ?_, hsymm⟩
  · apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · rw [hP]
      refine (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := 2 * g) ?_)
      intro m hm
      exact (Polynomial.natDegree_monomial_le _).trans (by have := Finset.mem_range.mp hm; omega)
    · rw [hcoeff]
      have := hd.pp_symm 0 (by omega)
      simp only [Nat.cast_zero, sub_zero, pow_zero, mul_one] at this
      rw [show ((2 * g : ℕ) : ℤ) = 2 * (g : ℤ) by push_cast; ring, this, hpp0, mul_one]
      exact pow_ne_zero _ hq0
  · rw [← Polynomial.coeff_zero_eq_eval_zero, hcoeff]
    simpa using hpp0
  · have hs := hd.sum_pp (2 * g + 1)
    rw [Finset.sum_range_succ, hd.pp_eq_zero _ (by push_cast; omega), add_zero] at hs
    have : P.eval 1 = ∑ m ∈ Finset.range (2 * g + 1), ppCoeff q A m := by
      rw [hP, Polynomial.eval_finset_sum]
      simp
    rw [this, hs]
    have h1 := hd.big ((2 * g + 1 : ℕ) : ℤ) (by push_cast; omega)
    have h2 := hd.big (((2 * g + 1 : ℕ) : ℤ) - 1) (by push_cast; omega)
    have hx0 : (q : ℚ) ≠ 0 := by positivity
    rw [show ((2 * g + 1 : ℕ) : ℤ) + 1 - g = ((g : ℤ) + 1) + 1 by push_cast; ring,
      zpow_add_one₀ hx0, zpow_add_one₀ hx0] at h1
    rw [show ((2 * g + 1 : ℕ) : ℤ) - 1 + 1 - g = ((g : ℤ) + 1) by push_cast; ring,
      zpow_add_one₀ hx0] at h2
    have h0 : ((q : ℚ) - 1) ≠ 0 := by linarith
    apply Int.cast_injective (α := ℚ)
    apply mul_left_cancel₀ h0
    push_cast at h1 h2 hs ⊢
    linear_combination h1 - (q : ℚ) * h2
  · ext m
    rw [hd.coeff_mul Z hZ m, Polynomial.coeff_coe, hcoeff]

end Alg

/-! ### Degrees, effective divisors, and the count of effective divisors in a class -/

theorem card_ne_zero_subtype (V : Type*) [AddCommGroup V] [Finite V] :
    Nat.card {x : V // x ≠ 0} = Nat.card V - 1 := by
  classical
  haveI := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]

theorem natCard_eq_pow_finrank (V : Type*) [AddCommGroup V] [Module Fq V] [Finite V] :
    Nat.card V = Nat.card Fq ^ Module.finrank Fq V := by
  classical
  haveI := Fintype.ofFinite Fq
  haveI := Fintype.ofFinite V
  simpa only [Nat.card_eq_fintype_card] using Module.card_eq_pow_finrank (K := Fq) (V := V)

namespace Divisor

theorem deg_eq_sum (a : Divisor Fq k) : deg a = ∑ v ∈ a.support, a v * (v.degree : ℤ) := by
  conv_lhs => rw [← Finsupp.sum_single a]
  rw [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl (fun v _ => deg_single v (a v))

theorem deg_nonneg {a : Divisor Fq k} (ha : 0 ≤ a) : 0 ≤ deg a := by
  rw [deg_eq_sum]
  exact Finset.sum_nonneg (fun v _ => mul_nonneg (by simpa using ha v) (Nat.cast_nonneg _))

theorem eq_zero_of_deg_eq_zero {a : Divisor Fq k} (ha : 0 ≤ a) (h : deg a = 0) : a = 0 := by
  rw [deg_eq_sum] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun v _ => mul_nonneg (by simpa using ha v) (Nat.cast_nonneg _))).mp h
  ext v
  by_contra hv
  have h2 := this v (Finsupp.mem_support_iff.mpr hv)
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hv (by simpa using h3)
  · exact absurd h3 (by exact_mod_cast v.degree_pos.ne')

end Divisor

theorem mem_principalDivisors_iff (x : Divisor Fq k) :
    x ∈ principalDivisors Fq k ↔ ∃ u : kˣ, Divisor.div u = x := by
  unfold principalDivisors
  rw [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Additive.toMul y, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨Additive.ofMul u, rfl⟩

theorem nonneg_add_div_iff (a : Divisor Fq k) (u : kˣ) :
    0 ≤ a + Divisor.div u ↔ (u : k) ∈ a.riemannRochSpace := by
  have : (u : k) ∈ a.riemannRochSpace ↔ ∀ v : Place Fq k, -a v ≤ v.ord (u : k) := by
    show ((u : k) = 0 ∨ _) ↔ _
    simp [u.ne_zero]
  rw [this]
  constructor
  · intro h v
    have := h v
    simp at this
    omega
  · intro h v
    have := h v
    simp
    omega

theorem Divisor.ell_eq_zero_of_deg_neg (H : WeilZetaInputs Fq k) {a : Divisor Fq k}
    (ha : Divisor.deg a < 0) : a.ell = 0 := by
  have hb : a.riemannRochSpace = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro f hf
    by_contra hne
    have h1 : 0 ≤ a + Divisor.div (Units.mk0 f hne) :=
      (nonneg_add_div_iff a (Units.mk0 f hne)).mpr hf
    have h2 := Divisor.deg_nonneg h1
    rw [map_add, H.deg_div] at h2
    omega
  haveI := H.finiteDimensional a
  unfold Divisor.ell
  exact Submodule.finrank_eq_zero.mpr hb

variable (Fq k) in
/-- The number of effective divisors of degree `n : ℤ`. -/
def effCountInt (n : ℤ) : ℕ := Nat.card {a : Divisor Fq k // 0 ≤ a ∧ Divisor.deg a = n}

/-- The number of effective divisors in the divisor class of `a`. -/
def effClassCount (a : Divisor Fq k) : ℕ :=
  Nat.card {b : Divisor Fq k // 0 ≤ b ∧ b - a ∈ principalDivisors Fq k}

/-- The number of effective divisors in the class of $\mathfrak a$: $(q-1)\cdot\#+1=q^{\lambda(\mathfrak a)}$, given that
$A(\mathfrak a)$ is finite-dimensional. -/
theorem effClassCount_spec_of_fd (hc : IsConstantField Fq k) (a : Divisor Fq k)
    (hfd : FiniteDimensional Fq a.riemannRochSpace) :
    (Nat.card Fq - 1) * effClassCount a + 1 = Nat.card Fq ^ a.ell := by
  classical
  haveI : Finite a.riemannRochSpace := Module.finite_of_finite Fq
  let Xu := {u : kˣ // (u : k) ∈ a.riemannRochSpace}
  let S := {b : Divisor Fq k // 0 ≤ b ∧ b - a ∈ principalDivisors Fq k}
  let ψ : Xu → S := fun u => ⟨a + Divisor.div u.1, (nonneg_add_div_iff a u.1).mpr u.2,
    by rw [add_sub_cancel_left]; exact (mem_principalDivisors_iff _).mpr ⟨u.1, rfl⟩⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨b, hb0, hb⟩
    obtain ⟨u, hu⟩ := (mem_principalDivisors_iff _).mp hb
    have hb' : b = a + Divisor.div u := by rw [hu]; abel
    exact ⟨⟨u, (nonneg_add_div_iff a u).mp (hb' ▸ hb0)⟩, Subtype.ext hb'.symm⟩
  haveI : Finite Xu := Finite.of_injective
    (fun u : Xu => (⟨(u.1 : k), u.2⟩ : a.riemannRochSpace))
    (by intro x y h; exact Subtype.ext (Units.ext (congrArg Subtype.val h)))
  haveI : Finite S := Finite.of_surjective ψ hψ
  haveI := Fintype.ofFinite S
  have hfib : ∀ b : S, Nat.card {u : Xu // ψ u = b} = Nat.card Fq - 1 := by
    intro b
    obtain ⟨u₀, hu₀⟩ := hψ b
    have hb : a + Divisor.div u₀.1 = b.1 := congrArg Subtype.val hu₀
    rw [← Nat.card_units Fq]
    symm
    let m : Fqˣ → Xu := fun l => ⟨Units.map (algebraMap Fq k : Fq →* k) l * u₀.1, by
      have := a.riemannRochSpace.smul_mem l u₀.2
      rw [Algebra.smul_def] at this
      simpa using this⟩
    have hm : ∀ l, ψ (m l) = b := by
      intro l
      apply Subtype.ext
      show a + Divisor.div (Units.map (algebraMap Fq k : Fq →* k) l * u₀.1) = b.1
      rw [Divisor.div_mul, (Divisor.div_eq_zero_iff _).mpr (isAlgebraic_algebraMap l.1), zero_add, hb]
    refine Nat.card_congr (Equiv.ofBijective (fun l => (⟨m l, hm l⟩ : {u : Xu // ψ u = b})) ⟨?_, ?_⟩)
    · intro l l' h
      have h1 : (m l).1 = (m l').1 := congrArg (fun x : {u : Xu // ψ u = b} => x.1.1) h
      have h2 : Units.map (algebraMap Fq k : Fq →* k) l = Units.map (algebraMap Fq k : Fq →* k) l' :=
        mul_right_cancel h1
      exact Units.map_injective (algebraMap Fq k).injective h2
    · rintro ⟨u, hu⟩
      have h1 : a + Divisor.div u.1 = b.1 := congrArg Subtype.val hu
      have h2 : Divisor.div u.1 = Divisor.div u₀.1 := add_left_cancel (h1.trans hb.symm)
      have h3 : (Divisor.div (u.1 * u₀.1⁻¹) : Divisor Fq k) = 0 := by
        have : (Divisor.div (u.1 * u₀.1⁻¹ * u₀.1) : Divisor Fq k) = Divisor.div (u₀.1) := by
          rw [inv_mul_cancel_right]; exact h2
        rw [Divisor.div_mul] at this
        simpa using this
      obtain ⟨c, hc'⟩ := hc _ ((Divisor.div_eq_zero_iff (Fq := Fq) _).mp h3)
      have hc0 : c ≠ 0 := by
        rintro rfl
        simp at hc'
      refine ⟨Units.mk0 c hc0, Subtype.ext (Subtype.ext (Units.ext ?_))⟩
      show (algebraMap Fq k c) * (u₀.1 : k) = u.1
      rw [hc']
      simp
  have hX : Nat.card Xu = (Nat.card Fq - 1) * Nat.card S := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv ψ), Nat.card_sigma,
      Finset.sum_congr rfl (fun b _ => hfib b), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, smul_eq_mul, mul_comm]
  have hX2 : Nat.card Xu = Nat.card a.riemannRochSpace - 1 := by
    rw [← card_ne_zero_subtype]
    refine Nat.card_congr
      { toFun := fun u => ⟨⟨u.1, u.2⟩, fun h => u.1.ne_zero (congrArg Subtype.val h)⟩
        invFun := fun f => ⟨Units.mk0 f.1.1 (fun h => f.2 (Subtype.ext h)), f.1.2⟩
        left_inv := fun u => Subtype.ext (Units.ext rfl)
        right_inv := fun f => rfl }
  have hpos : 0 < Nat.card a.riemannRochSpace := Nat.card_pos
  have := natCard_eq_pow_finrank (Fq := Fq) a.riemannRochSpace
  unfold effClassCount
  show (Nat.card Fq - 1) * Nat.card S + 1 = _
  unfold Divisor.ell
  omega

theorem effClassCount_spec (hc : IsConstantField Fq k) (H : WeilZetaInputs Fq k)
    (a : Divisor Fq k) :
    (Nat.card Fq - 1) * effClassCount a + 1 = Nat.card Fq ^ a.ell :=
  effClassCount_spec_of_fd hc a (H.finiteDimensional a)

theorem effClassCount_spec_int (hc : IsConstantField Fq k) (H : WeilZetaInputs Fq k)
    (a : Divisor Fq k) :
    ((Nat.card Fq : ℤ) - 1) * (effClassCount a : ℤ) = (Nat.card Fq : ℤ) ^ a.ell - 1 := by
  have h1 : 1 ≤ Nat.card Fq := Nat.card_pos
  have := congrArg (Nat.cast : ℕ → ℤ) (effClassCount_spec hc H a)
  push_cast [Nat.cast_sub h1] at this
  linarith

theorem Divisor.ell_congr (hc : IsConstantField Fq k) (H : WeilZetaInputs Fq k)
    {a a' : Divisor Fq k} (h : a - a' ∈ principalDivisors Fq k) : a.ell = a'.ell := by
  have hN : effClassCount a = effClassCount a' := by
    unfold effClassCount
    refine Nat.card_congr (Equiv.subtypeEquivRight fun b => and_congr_right fun _ => ?_)
    constructor
    · intro hb
      have : b - a' = (b - a) + (a - a') := by abel
      rw [this]; exact add_mem hb h
    · intro hb
      have : b - a = (b - a') - (a - a') := by abel
      rw [this]; exact sub_mem hb h
  have h1 := effClassCount_spec hc H a
  have h2 := effClassCount_spec hc H a'
  rw [hN] at h1
  have hq : 2 ≤ Nat.card Fq := Finite.one_lt_card
  exact Nat.pow_right_injective hq (h1.symm.trans h2)

theorem deg_eq_zero_of_mem_principal (H : WeilZetaInputs Fq k) {x : Divisor Fq k}
    (hx : x ∈ principalDivisors Fq k) : Divisor.deg x = 0 := by
  obtain ⟨u, rfl⟩ := (mem_principalDivisors_iff x).mp hx
  exact H.deg_div u

theorem deg_canonical (g : ℕ) (c : Divisor Fq k)
    (hRR : ∀ a : Divisor Fq k, (a.ell : ℤ) = Divisor.deg a + 1 - g + (c - a).ell) :
    Divisor.deg c = 2 * g - 2 := by
  have e1 := hRR 0
  have e2 := hRR c
  simp only [sub_zero, sub_self, map_zero] at e1 e2
  omega

theorem exists_zetaAlg (hc : IsConstantField Fq k) (H : WeilZetaInputs Fq k) :
    ZetaAlg (Nat.card Fq) H.genus (Nat.card (ClassGroup0 Fq k))
      (fun n => (effCountInt Fq k n : ℤ)) := by
  classical
  obtain ⟨b₁, hb₁⟩ := H.exists_deg_one
  set g := H.genus with hg
  set c : Divisor Fq k := H.riemannRoch.choose_spec.choose with hcdef
  have hRR : ∀ a : Divisor Fq k, (a.ell : ℤ) = Divisor.deg a + 1 - g + (c - a).ell :=
    H.riemannRoch.choose_spec.choose_spec
  have hdc := deg_canonical g c hRR
  have hq2 : 2 ≤ Nat.card Fq := Finite.one_lt_card
  haveI hGfin : Finite (ClassGroup0 Fq k) := H.finite_classGroup0
  haveI : Fintype (ClassGroup0 Fq k) := Fintype.ofFinite _
  let K : AddSubgroup (Divisor Fq k) := (Divisor.deg (Fq := Fq) (k := k)).ker
  let rep : ClassGroup0 Fq k → K := Function.surjInv QuotientAddGroup.mk_surjective
  have hrep : ∀ C, (QuotientAddGroup.mk (rep C) : ClassGroup0 Fq k) = C :=
    fun C => Function.surjInv_eq QuotientAddGroup.mk_surjective C
  have hrepdeg : ∀ C, Divisor.deg (rep C : Divisor Fq k) = 0 := fun C =>
    AddMonoidHom.mem_ker.mp (rep C).2
  let base : ℤ → ClassGroup0 Fq k → Divisor Fq k := fun n C => n • b₁ + (rep C : Divisor Fq k)
  have hbasedeg : ∀ n C, Divisor.deg (base n C) = n := by
    intro n C
    simp [base, hb₁, hrepdeg]
  -- the fibre decomposition
  let Φ : (n : ℤ) → {b : Divisor Fq k // 0 ≤ b ∧ Divisor.deg b = n} → ClassGroup0 Fq k :=
    fun n b => QuotientAddGroup.mk (⟨b.1 - n • b₁, by
      apply AddMonoidHom.mem_ker.mpr
      rw [map_sub, map_zsmul, hb₁, b.2.2]; simp⟩ : K)
  have hΦ : ∀ n x C, Φ n x = C ↔ x.1 - base n C ∈ principalDivisors Fq k := by
    intro n x C
    rw [show (Φ n x = C) = (Φ n x = QuotientAddGroup.mk (rep C)) by rw [hrep]]
    show (QuotientAddGroup.mk _ : ClassGroup0 Fq k) = QuotientAddGroup.mk (rep C) ↔ _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have : x.1 - base n C = -((-(x.1 - n • b₁)) + (rep C : Divisor Fq k)) := by
      simp only [base]; abel
    rw [this, neg_mem_iff]
    simp
  have hfibEq : ∀ n C, Nat.card {x // Φ n x = C} = effClassCount (base n C) := by
    intro n C
    unfold effClassCount
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2.1, (hΦ n x.1 C).mp x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1, by
          have := deg_eq_zero_of_mem_principal H y.2.2
          rw [map_sub, hbasedeg] at this
          omega⟩, (hΦ n _ C).mpr y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hfiber : ∀ n, effCountInt Fq k n = ∑ C, effClassCount (base n C) := by
    intro n
    haveI : Finite {b : Divisor Fq k // 0 ≤ b ∧ Divisor.deg b = n} :=
      (H.finite_effective n).to_subtype
    unfold effCountInt
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (Φ n)), Nat.card_sigma]
    exact Finset.sum_congr rfl (fun C _ => hfibEq n C)
  have hsumQ : ∀ n : ℤ, ((Nat.card Fq : ℚ) - 1) * (effCountInt Fq k n : ℚ) =
      ∑ C, ((Nat.card Fq : ℚ) ^ (base n C).ell - 1) := by
    intro n
    rw [hfiber n]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun C _ => ?_)
    have := effClassCount_spec_int hc H (base n C)
    exact_mod_cast this
  have hcardG : (Finset.univ : Finset (ClassGroup0 Fq k)).card = Nat.card (ClassGroup0 Fq k) := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
  have hellbig : ∀ n C, 2 * (g : ℤ) - 1 ≤ n → ((base n C).ell : ℤ) = n + 1 - g := by
    intro n C hn
    have h1 := hRR (base n C)
    have h2 : (c - base n C).ell = 0 :=
      Divisor.ell_eq_zero_of_deg_neg H (by rw [map_sub, hbasedeg, hdc]; omega)
    rw [hbasedeg, h2] at h1
    simpa using h1
  have hx0 : (Nat.card Fq : ℚ) ≠ 0 := by
    have : 0 < Nat.card Fq := Nat.card_pos
    positivity
  have hk0 : c - ((2 * (g : ℤ) - 2) • b₁) ∈ K := by
    apply AddMonoidHom.mem_ker.mpr
    rw [map_sub, map_zsmul, hb₁, hdc]; simp
  let κ : ClassGroup0 Fq k := QuotientAddGroup.mk ⟨_, hk0⟩
  have hφ : ∀ n C, ((base n C).ell : ℤ) = n + 1 - g + (base (2 * g - 2 - n) (κ - C)).ell := by
    intro n C
    rw [hRR (base n C), hbasedeg]
    have hmem : (⟨_, hk0⟩ - rep C - rep (κ - C) : K) ∈
        (principalDivisors Fq k).addSubgroupOf K := by
      rw [← QuotientAddGroup.eq_zero_iff]
      rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_sub, hrep, hrep]
      show κ - C - (κ - C) = 0
      exact sub_self _
    have hmem' := AddSubgroup.mem_addSubgroupOf.mp hmem
    have e : c - base n C - base (2 * g - 2 - n) (κ - C) =
        ((⟨_, hk0⟩ - rep C - rep (κ - C) : K) : Divisor Fq k) := by
      simp only [base, AddSubgroup.coe_sub]
      have hsm : ((2 * (g : ℤ) - 2) • b₁) = n • b₁ + (2 * (g : ℤ) - 2 - n) • b₁ := by
        rw [← add_smul]; congr 1; ring
      rw [hsm]; abel
    have := Divisor.ell_congr hc H (a := c - base n C) (a' := base (2 * g - 2 - n) (κ - C))
      (by rw [e]; exact hmem')
    rw [this]
  refine ⟨hq2, ?_, ?_, ?_, ?_⟩
  · intro n hn
    show (effCountInt Fq k n : ℤ) = 0
    have : effCountInt Fq k n = 0 := by
      unfold effCountInt
      haveI : IsEmpty {a : Divisor Fq k // 0 ≤ a ∧ Divisor.deg a = n} :=
        ⟨fun x => by have := Divisor.deg_nonneg x.2.1; rw [x.2.2] at this; omega⟩
      exact Nat.card_of_isEmpty
    simp [this]
  · show (effCountInt Fq k 0 : ℤ) = 1
    have : effCountInt Fq k 0 = 1 := by
      unfold effCountInt
      haveI : Unique {a : Divisor Fq k // 0 ≤ a ∧ Divisor.deg a = 0} :=
        { default := ⟨0, le_refl _, map_zero _⟩
          uniq := fun x => Subtype.ext (Divisor.eq_zero_of_deg_eq_zero x.2.1 x.2.2) }
      exact Nat.card_unique
    simp [this]
  · intro n hn
    show ((Nat.card Fq : ℚ) - 1) * ((effCountInt Fq k n : ℤ) : ℚ) = _
    rw [Int.cast_natCast, hsumQ n]
    have : ∀ C, (Nat.card Fq : ℚ) ^ (base n C).ell = (Nat.card Fq : ℚ) ^ (n + 1 - (g : ℤ)) := by
      intro C
      rw [← zpow_natCast, hellbig n C hn]
    simp_rw [this]
    rw [Finset.sum_const, hcardG, nsmul_eq_mul]
  · intro n
    show ((Nat.card Fq : ℚ) - 1) * ((effCountInt Fq k n : ℤ) : ℚ) =
      _ * (((Nat.card Fq : ℚ) - 1) * ((effCountInt Fq k (2 * g - 2 - n) : ℤ) : ℚ)) + _
    rw [Int.cast_natCast, Int.cast_natCast, hsumQ n, hsumQ (2 * g - 2 - n)]
    have hpow : ∀ C, (Nat.card Fq : ℚ) ^ (base n C).ell =
        (Nat.card Fq : ℚ) ^ (n + 1 - (g : ℤ)) *
          (Nat.card Fq : ℚ) ^ (base (2 * g - 2 - n) (κ - C)).ell := by
      intro C
      rw [← zpow_natCast, ← zpow_natCast (Nat.card Fq : ℚ) (base _ _).ell, ← zpow_add₀ hx0, hφ n C]
    simp_rw [hpow]
    have hcomp := Equiv.sum_comp (Equiv.subLeft κ)
      (fun C => (Nat.card Fq : ℚ) ^ (base (2 * g - 2 - n) C).ell)
    simp only [Equiv.subLeft_apply] at hcomp
    have L : ∑ C : ClassGroup0 Fq k, ((Nat.card Fq : ℚ) ^ (n + 1 - (g : ℤ)) *
        (Nat.card Fq : ℚ) ^ (base (2 * g - 2 - n) (κ - C)).ell - 1) =
        (Nat.card Fq : ℚ) ^ (n + 1 - (g : ℤ)) *
          ∑ C : ClassGroup0 Fq k, (Nat.card Fq : ℚ) ^ (base (2 * g - 2 - n) C).ell -
          (Nat.card (ClassGroup0 Fq k) : ℚ) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcomp, Finset.sum_const, hcardG,
        nsmul_eq_mul, mul_one]
    have R : ∑ C : ClassGroup0 Fq k, ((Nat.card Fq : ℚ) ^ (base (2 * g - 2 - n) C).ell - 1) =
        ∑ C : ClassGroup0 Fq k, (Nat.card Fq : ℚ) ^ (base (2 * g - 2 - n) C).ell -
          (Nat.card (ClassGroup0 Fq k) : ℚ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, hcardG, nsmul_eq_mul, mul_one]
    rw [L, R]
    ring

/-- **Weil VII.§6 Thm. 4**: rationality and functional equation of the zeta function of a function field with
constant field $\mathbb F_q$, conditional on `WeilZetaInputs`. -/
@[kb "weil1973bnt" "Ch. VII, §6, Thm. 4 (p. 130), conditional on WeilZetaInputs"]
theorem weil_VII_6_thm4 (hc : IsConstantField Fq k) (H : WeilZetaInputs Fq k) :
    ∃ P : ℤ[X], P.natDegree = 2 * H.genus ∧ P.eval 0 = 1 ∧
      P.eval 1 = Nat.card (ClassGroup0 Fq k) ∧
      zetaSeries Fq k * ((1 - PowerSeries.X) * (1 - (Nat.card Fq : PowerSeries ℤ) * PowerSeries.X)) =
        (P : PowerSeries ℤ) ∧
      ∀ i ≤ 2 * H.genus,
        P.coeff (2 * H.genus - i) * (Nat.card Fq : ℤ) ^ i = (Nat.card Fq : ℤ) ^ H.genus * P.coeff i :=
  (exists_zetaAlg hc H).exists_poly (zetaSeries Fq k) (fun n => by simp [zetaSeries, effCount, effCountInt])

end NumberFieldKB.WeilBNT.FF
