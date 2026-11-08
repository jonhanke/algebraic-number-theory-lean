import NumberFieldKB.WeilBNT.FunctionField.WeilDifferential

/-!
# Consequences of Riemann–Roch (Weil VI.§2, Cor. 1–3 of Thm. 2; IV.§4, Cor. of Thm. 8)

* **`ell_zero`**: if $\mathbb F_q$ is the field of constants, $\lambda(0)=1$; then **`genusInt_eq_index_zero`**:
  $g=i(0)\ge0$ (`genus`, a natural number).
* **`weil_VI_2_cor1`**: $\deg\mathfrak c=2g-2$ and $\lambda(\mathfrak c)=g$.
* **`weil_VI_2_cor2`**: $\lambda(\mathfrak a)=\deg\mathfrak a-g+1$ if $\deg\mathfrak a>2g-2$.
* **`weil_VI_2_cor3`**: $\mathbb A=U(\mathfrak a)+k$ (repartitions) if $\deg\mathfrak a>2g-2$; more generally
  **`weil_VI_1_thm1_cor2`**: $\mathbb A=U(\mathfrak a)+k$ iff $\lambda(\mathfrak c-\mathfrak a)=0$.
* **`canonical_class`**: the divisors of nonzero Weil differentials form one divisor class (Weil VI.§2, text p. 100).
* **`finite_constants`**: the algebraic closure of $\mathbb F_q$ in $k$ is finite (Weil IV.§4, Cor. of Thm. 8).
-/

open scoped Polynomial
open Module

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

open Divisor Rep

/-- $A(0)$ is the algebraic closure of $\mathbb F_q$ in $k$: the elements without poles are the constants. -/
theorem mem_riemannRochSpace_zero_iff (f : k) : f ∈ (0 : Divisor Fq k).riemannRochSpace ↔ IsAlgebraic Fq f := by
  rw [mem_riemannRochSpace_iff]
  constructor
  · intro h
    exact isAlgebraic_of_forall_valuation_le_one f (fun v => by simpa using h v)
  · intro h v
    by_cases hf : f = 0
    · subst hf; simp
    · have hv : v.valuation f = 1 := by
        by_contra hne
        exact Valuation.transcendental_of_ne_one (v := v.valuation) Fq f hf hne h
      simp [hv]

/-- **The field of constants is finite** (Weil IV.§4, Cor. of Thm. 8, and text p. 77): the elements of $k$ algebraic
over $\mathbb F_q$ form a finite set. -/
@[kb "weil1973bnt" "Ch. IV, §4, Cor. of Thm. 8 (p. 77), function fields: the constants form a finite field"]
theorem finite_constants : {f : k | IsAlgebraic Fq f}.Finite := by
  haveI : Finite (0 : Divisor Fq k).riemannRochSpace := Module.finite_of_finite Fq
  have : {f : k | IsAlgebraic Fq f} = ((0 : Divisor Fq k).riemannRochSpace : Set k) := by
    ext f
    simp [mem_riemannRochSpace_zero_iff]
  rw [this]
  exact Set.toFinite _

/-- **$\lambda(0)=1$** when $\mathbb F_q$ is the field of constants. -/
theorem ell_zero (hc : IsConstantField Fq k) : (0 : Divisor Fq k).ell = 1 := by
  have h : (0 : Divisor Fq k).riemannRochSpace = Submodule.span Fq {1} := by
    ext f
    rw [mem_riemannRochSpace_zero_iff, Submodule.mem_span_singleton]
    constructor
    · intro hf
      obtain ⟨c, rfl⟩ := hc f hf
      exact ⟨c, by rw [Algebra.smul_def, mul_one]⟩
    · rintro ⟨c, rfl⟩
      rw [Algebra.smul_def, mul_one]
      exact isAlgebraic_algebraMap c
  unfold ell
  rw [h, finrank_span_singleton one_ne_zero]

/-- **$g=i(0)\ge0$** when $\mathbb F_q$ is the field of constants. -/
theorem genusInt_eq_index_zero (hc : IsConstantField Fq k) : genusInt Fq k = index Fq k 0 := by
  have := ell_sub_index (0 : Divisor Fq k)
  rw [ell_zero hc, map_zero] at this
  omega

theorem genusInt_nonneg (hc : IsConstantField Fq k) : 0 ≤ genusInt Fq k := by
  rw [genusInt_eq_index_zero hc]; positivity

/-- **Weil VI.§2, Cor. 1 of Thm. 2**: $\deg\mathfrak c=2g-2$ and $\lambda(\mathfrak c)=g$. -/
@[kb "weil1973bnt" "Ch. VI, Cor. 1 (Thm. 2) (p. 101), deg c = 2g - 2 and l(c) = g"]
theorem weil_VI_2_cor1 (hc : IsConstantField Fq k) :
    deg (canonical Fq k) = 2 * genusInt Fq k - 2 ∧ ((canonical Fq k).ell : ℤ) = genusInt Fq k := by
  have h1 := weil_VI_2_thm2 (0 : Divisor Fq k)
  have h2 := weil_VI_2_thm2 (canonical Fq k)
  rw [ell_zero hc, map_zero, sub_zero] at h1
  rw [sub_self, ell_zero hc] at h2
  constructor <;> omega

/-- **Weil VI.§2, Cor. 2 of Thm. 2**: $\lambda(\mathfrak a)=\deg\mathfrak a-g+1$ if $\deg\mathfrak a>2g-2$. -/
@[kb "weil1973bnt" "Ch. VI, Cor. 2 (Thm. 2) (p. 101), l(a) = deg a - g + 1 for deg a > 2g - 2"]
theorem weil_VI_2_cor2 (hc : IsConstantField Fq k) {a : Divisor Fq k}
    (ha : 2 * genusInt Fq k - 2 < deg a) : (a.ell : ℤ) = deg a - genusInt Fq k + 1 := by
  have h := weil_VI_2_thm2 a
  have hcd := (weil_VI_2_cor1 hc).1
  have h0 : (canonical Fq k - a).ell = 0 := ell_eq_zero_of_deg_neg' (by rw [map_sub]; omega)
  rw [h0] at h
  push_cast at h
  omega

/-- **Weil VI.§1, Cor. 2 of Thm. 1** (for $E=k$, repartition form): $\mathbb A=U(\mathfrak a)+k$ iff
$\lambda(\mathfrak c-\mathfrak a)=0$. -/
@[kb "weil1973bnt" "Ch. VI, Cor. 2 (Thm. 1) (p. 100), E = k, repartitions"]
theorem weil_VI_1_thm1_cor2 (a : Divisor Fq k) : S Fq k a = ⊤ ↔ (canonical Fq k - a).ell = 0 := by
  rw [← index_eq_ell_canonical_sub]
  unfold index
  rw [Module.finrank_zero_iff, Submodule.Quotient.subsingleton_iff]

/-- **Weil VI.§2, Cor. 3 of Thm. 2** (repartition form): if $\deg\mathfrak a>2g-2$ then $\mathbb A=U(\mathfrak a)+k$. -/
@[kb "weil1973bnt" "Ch. VI, Cor. 3 (Thm. 2) (p. 101), repartitions"]
theorem weil_VI_2_cor3 (hc : IsConstantField Fq k) {a : Divisor Fq k}
    (ha : 2 * genusInt Fq k - 2 < deg a) : S Fq k a = ⊤ := by
  rw [weil_VI_1_thm1_cor2]
  apply ell_eq_zero_of_deg_neg'
  rw [map_sub, (weil_VI_2_cor1 hc).1]
  omega

/-- The divisor of $\xi\omega$ is $(\omega)+\operatorname{div}\xi$. -/
theorem divisor_xω {ω : Module.Dual Fq (Rep Fq k)} {W : Divisor Fq k}
    (hW : ∀ a, ω ∈ Omega Fq k a ↔ a ≤ W) (f : kˣ) (a : Divisor Fq k) :
    xω (f : k) ω ∈ Omega Fq k a ↔ a ≤ W + Divisor.div f := by
  rw [mem_Omega_xω, hW]
  constructor
  · intro h v; have := h v; simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply] at *
    omega
  · intro h v; have := h v; simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply] at *
    omega

/-- **The canonical class** (Weil VI.§2, text p. 100): the divisor of any nonzero Weil differential is linearly
equivalent to $\mathfrak c$. -/
@[kb "weil1973bnt" "Ch. VI, text p.100 (the canonical class), Weil differentials"]
theorem canonical_class {ω : Module.Dual Fq (Rep Fq k)} (hω0 : ω ≠ 0) {W : Divisor Fq k}
    (hW : ∀ a, ω ∈ Omega Fq k a ↔ a ≤ W) : W - canonical Fq k ∈ principalDivisors Fq k := by
  obtain ⟨x, hx⟩ := exists_eq_xω hω0 weilDifferential₀_ne_zero ⟨W, (hW W).2 le_rfl⟩ weilDifferential₀_mem
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hω0 (by rw [hx, xω_zero_left])
  have hdiv := divisor_xω (fun a => mem_Omega_canonical_iff (Fq := Fq) (k := k) a) (Units.mk0 x hx0)
  have hEq : W = canonical Fq k + Divisor.div (Units.mk0 x hx0) := by
    apply le_antisymm
    · exact (hdiv W).1 (by rw [Units.val_mk0, ← hx]; exact (hW W).2 le_rfl)
    · rw [← hW, hx]
      exact (hdiv _).2 le_rfl
  rw [hEq, add_sub_cancel_left]
  exact (mem_principalDivisors_iff _).2 ⟨_, rfl⟩

end NumberFieldKB.WeilBNT.FF
