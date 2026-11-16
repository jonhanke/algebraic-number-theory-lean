import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import QuadFormsKB.Citation


/-!
# Milne, *Elliptic Curves*, Chapter II, Theorem 2.4 (b): isomorphisms are changes of variables

Source: J. S. Milne, *Elliptic Curves*, second edition (course notes `ectext6`, 2006), bib key `milne2006ec`.
Locators give pdf pages (printed page = pdf page − 8).

Isomorphisms of pointed Weierstrass curves are modelled by their comorphisms on affine coordinate rings (see the
module docstring of `Ch2Iso.lean`). Milne's proof: $x \circ \varphi$ has a double pole at $O'$ and no other pole,
so it lies in $L(2O') = \langle 1, x' \rangle$; similarly $y \circ \varphi \in L(3O')$. Here the pole order at $O$
of $p(x) + q(x)y$ is $\max(2\deg p, 2\deg q + 3)$, the degree of its norm to $k[x]$ (Mathlib's
`degree_norm_smul_basis`), and it is recovered intrinsically as $\dim_k k[E]/(f)$.
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve Polynomial

variable {k : Type*} [Field k]

/-- The degree of the norm to `k[X]` is preserved by `k`-algebra isomorphisms of affine coordinate rings. -/
lemma natDegree_norm_algEquiv (E E' : WeierstrassCurve k)
    (σ : E.toAffine.CoordinateRing ≃ₐ[k] E'.toAffine.CoordinateRing)
    {f : E.toAffine.CoordinateRing} (hf : f ≠ 0) :
    (Algebra.norm k[X] (σ f)).natDegree = (Algebra.norm k[X] f).natDegree := by
  have hσf : σ f ≠ 0 := by simpa using hf
  rw [← finrank_quotient_span_eq_natDegree_norm (Affine.CoordinateRing.basis E') hσf,
    ← finrank_quotient_span_eq_natDegree_norm (Affine.CoordinateRing.basis E) hf]
  have h : Ideal.span {σ f} = (Ideal.span {f}).map (σ : _ →+* _) := by
    rw [Ideal.map_span]; simp
  exact (Ideal.quotientEquivAlg _ _ σ h).toLinearEquiv.finrank_eq.symm

/-- The class of `X` is `X • 1`. -/
lemma mk_C_X_eq (E : WeierstrassCurve k) :
    Affine.CoordinateRing.mk E (Polynomial.C X) = (X : k[X]) • (1 : E.toAffine.CoordinateRing) := by
  rw [Affine.CoordinateRing.smul, mul_one]

/-- The norm of `x` has degree `2`. -/
lemma natDegree_norm_x (E : WeierstrassCurve k) :
    (Algebra.norm k[X] (Affine.CoordinateRing.mk E (Polynomial.C X))).natDegree = 2 := by
  have h := Affine.CoordinateRing.degree_norm_smul_basis (W' := E) (X : k[X]) 0
  rw [mk_C_X_eq]
  simp only [zero_smul, add_zero] at h
  rw [natDegree_eq_of_degree_eq_some (n := 2)]
  rw [h]; simp

/-- The norm of `y` has degree `3`. -/
lemma natDegree_norm_y (E : WeierstrassCurve k) :
    (Algebra.norm k[X] (Affine.CoordinateRing.mk E X)).natDegree = 3 := by
  have h := Affine.CoordinateRing.degree_norm_smul_basis (W' := E) (0 : k[X]) 1
  simp only [zero_smul, one_smul, zero_add] at h
  rw [natDegree_eq_of_degree_eq_some (n := 3)]
  rw [h]; simp

/-- The structure map from the base field in terms of the quotient map. -/
lemma algebraMap_eq_mk (E : WeierstrassCurve k) (c : k) :
    algebraMap k E.toAffine.CoordinateRing c = Affine.CoordinateRing.mk E (Polynomial.C (Polynomial.C c)) := rfl

/-- Scalar multiples of `1` by polynomials in `X`, in terms of the quotient map. -/
lemma smul_one_eq (E : WeierstrassCurve k) (p : k[X]) :
    p • (1 : E.toAffine.CoordinateRing) = Affine.CoordinateRing.mk E (Polynomial.C p) := by
  rw [Affine.CoordinateRing.smul, mul_one]

/-- An element whose norm has degree `2` is `α x' + β` with `α ≠ 0`. -/
lemma shape_of_natDegree_norm_two (E : WeierstrassCurve k) (a : E.toAffine.CoordinateRing)
    (ha : (Algebra.norm k[X] a).natDegree = 2) :
    ∃ α β : k, α ≠ 0 ∧ a = algebraMap k _ α * Affine.CoordinateRing.mk E (Polynomial.C X) +
      algebraMap k _ β := by
  obtain ⟨p, q, rfl⟩ := Affine.CoordinateRing.exists_smul_basis_eq a
  have h := Affine.CoordinateRing.degree_norm_smul_basis (W' := E) p q
  rw [degree_eq_natDegree (by rintro h0; rw [h0] at ha; simp at ha), ha] at h
  have hq : q = 0 := by
    by_contra hq
    rw [degree_eq_natDegree hq] at h
    have key : (2 • (q.natDegree : WithBot ℕ) + 3) = ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) := by
      norm_cast
    have h2 : ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) ≤ ((2 : ℕ) : WithBot ℕ) := by
      rw [← key, h]; exact le_max_right _ _
    have h3 : 2 * q.natDegree + 3 ≤ 2 := by exact_mod_cast h2
    omega
  subst hq
  have hp : p ≠ 0 := by
    rintro rfl
    rw [degree_zero] at h
    simp at h
  rw [degree_eq_natDegree hp, degree_zero] at h
  simp at h
  have hp1 : p.natDegree = 1 := by
    have h3 : (2 : ℕ) = 2 * p.natDegree := by exact_mod_cast h
    omega
  refine ⟨p.coeff 1, p.coeff 0, ?_, ?_⟩
  · have := leadingCoeff_ne_zero.mpr hp
    rwa [leadingCoeff, hp1] at this
  · rw [smul_one_eq, zero_smul, add_zero]
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hp1.le]
    rw [algebraMap_eq_mk, algebraMap_eq_mk]
    simp [map_add, map_mul]

/-- An element whose norm has degree `3` is `γ y' + δ x' + ε` with `γ ≠ 0`. -/
lemma shape_of_natDegree_norm_three (E : WeierstrassCurve k) (a : E.toAffine.CoordinateRing)
    (ha : (Algebra.norm k[X] a).natDegree = 3) :
    ∃ γ δ ε : k, γ ≠ 0 ∧ a = algebraMap k _ γ * Affine.CoordinateRing.mk E X +
      algebraMap k _ δ * Affine.CoordinateRing.mk E (Polynomial.C X) + algebraMap k _ ε := by
  obtain ⟨p, q, rfl⟩ := Affine.CoordinateRing.exists_smul_basis_eq a
  have h := Affine.CoordinateRing.degree_norm_smul_basis (W' := E) p q
  have hne : Algebra.norm k[X] (p • (1 : E.toAffine.CoordinateRing) + q • Affine.CoordinateRing.mk E X) ≠ 0 := by
    intro h0; rw [h0] at ha; simp at ha
  rw [degree_eq_natDegree hne, ha] at h
  have hq : q ≠ 0 := by
    rintro rfl
    rw [degree_zero] at h
    by_cases hp : p = 0
    · subst hp; rw [degree_zero] at h; simp at h
    · rw [degree_eq_natDegree hp] at h
      simp at h
      have h3 : (3 : ℕ) = 2 * p.natDegree := by exact_mod_cast h
      omega
  rw [degree_eq_natDegree hq] at h
  have key : (2 • (q.natDegree : WithBot ℕ) + 3) = ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) := by
    norm_cast
  have h2 : ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) ≤ ((3 : ℕ) : WithBot ℕ) := by
    rw [← key, h]; exact le_max_right _ _
  have h3 : 2 * q.natDegree + 3 ≤ 3 := by exact_mod_cast h2
  have hq0 : q.natDegree = 0 := by omega
  have hp1 : p.natDegree ≤ 1 := by
    by_cases hp : p = 0
    · subst hp; simp
    · have h4 : (2 • p.degree) ≤ ((3 : ℕ) : WithBot ℕ) := by
        rw [h]; exact le_max_left _ _
      rw [degree_eq_natDegree hp] at h4
      have h5 : 2 * p.natDegree ≤ 3 := by
        have : (2 • (p.natDegree : WithBot ℕ)) = ((2 * p.natDegree : ℕ) : WithBot ℕ) := by norm_cast
        rw [this] at h4
        exact_mod_cast h4
      omega
  refine ⟨q.coeff 0, p.coeff 1, p.coeff 0, ?_, ?_⟩
  · have := leadingCoeff_ne_zero.mpr hq
    rwa [leadingCoeff, hq0] at this
  · rw [smul_one_eq, Affine.CoordinateRing.smul]
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hp1, eq_C_of_natDegree_eq_zero hq0]
    rw [algebraMap_eq_mk, algebraMap_eq_mk, algebraMap_eq_mk]
    simp [map_add, map_mul]
    ring

/-- The Weierstrass equation holds in the affine coordinate ring. -/
lemma weierstrass_relation (E : WeierstrassCurve k) :
    (Affine.CoordinateRing.mk E X) ^ 2 +
        algebraMap k _ E.a₁ * Affine.CoordinateRing.mk E (Polynomial.C X) * Affine.CoordinateRing.mk E X +
        algebraMap k _ E.a₃ * Affine.CoordinateRing.mk E X =
      Affine.CoordinateRing.mk E (Polynomial.C X) ^ 3 +
        algebraMap k _ E.a₂ * Affine.CoordinateRing.mk E (Polynomial.C X) ^ 2 +
        algebraMap k _ E.a₄ * Affine.CoordinateRing.mk E (Polynomial.C X) + algebraMap k _ E.a₆ := by
  have h : Affine.CoordinateRing.mk E E.toAffine.polynomial = 0 := AdjoinRoot.mk_self
  simp only [Affine.polynomial, map_sub, map_add, map_mul, map_pow, algebraMap_eq_mk] at h ⊢
  linear_combination h

/-- Comparing coefficients in the basis `{1, y'}` after substituting a change of variables into the
Weierstrass equation of `E`. -/
lemma coeff_equations (E E' : WeierstrassCurve k) (α β γ δ ε : k)
    (h : (algebraMap k E'.toAffine.CoordinateRing γ * Affine.CoordinateRing.mk E' X +
          algebraMap k _ δ * Affine.CoordinateRing.mk E' (Polynomial.C X) + algebraMap k _ ε) ^ 2 +
        algebraMap k _ E.a₁ * (algebraMap k _ α * Affine.CoordinateRing.mk E' (Polynomial.C X) + algebraMap k _ β) *
          (algebraMap k E'.toAffine.CoordinateRing γ * Affine.CoordinateRing.mk E' X +
          algebraMap k _ δ * Affine.CoordinateRing.mk E' (Polynomial.C X) + algebraMap k _ ε) +
        algebraMap k _ E.a₃ * (algebraMap k E'.toAffine.CoordinateRing γ * Affine.CoordinateRing.mk E' X +
          algebraMap k _ δ * Affine.CoordinateRing.mk E' (Polynomial.C X) + algebraMap k _ ε) =
      (algebraMap k _ α * Affine.CoordinateRing.mk E' (Polynomial.C X) + algebraMap k _ β) ^ 3 +
        algebraMap k _ E.a₂ * (algebraMap k _ α * Affine.CoordinateRing.mk E' (Polynomial.C X) + algebraMap k _ β) ^ 2 +
        algebraMap k _ E.a₄ * (algebraMap k _ α * Affine.CoordinateRing.mk E' (Polynomial.C X) + algebraMap k _ β) +
        algebraMap k _ E.a₆) :
    γ ^ 2 = α ^ 3 ∧
    δ ^ 2 + E.a₁ * α * δ - 3 * α ^ 2 * β - E.a₂ * α ^ 2 + γ ^ 2 * E'.a₂ = 0 ∧
    2 * δ * ε + E.a₁ * (α * ε + β * δ) + E.a₃ * δ - 3 * α * β ^ 2 - 2 * E.a₂ * α * β - E.a₄ * α
      + γ ^ 2 * E'.a₄ = 0 ∧
    ε ^ 2 + E.a₁ * β * ε + E.a₃ * ε - β ^ 3 - E.a₂ * β ^ 2 - E.a₄ * β - E.a₆ + γ ^ 2 * E'.a₆ = 0 ∧
    2 * γ * δ + E.a₁ * γ * α - γ ^ 2 * E'.a₁ = 0 ∧
    2 * γ * ε + E.a₁ * γ * β + E.a₃ * γ - γ ^ 2 * E'.a₃ = 0 := by
  have hr := weierstrass_relation E'
  have key : (C (γ ^ 2 - α ^ 3) * X ^ 3 +
      C (δ ^ 2 + E.a₁ * α * δ - 3 * α ^ 2 * β - E.a₂ * α ^ 2 + γ ^ 2 * E'.a₂) * X ^ 2 +
      C (2 * δ * ε + E.a₁ * (α * ε + β * δ) + E.a₃ * δ - 3 * α * β ^ 2 - 2 * E.a₂ * α * β - E.a₄ * α
        + γ ^ 2 * E'.a₄) * X +
      C (ε ^ 2 + E.a₁ * β * ε + E.a₃ * ε - β ^ 3 - E.a₂ * β ^ 2 - E.a₄ * β - E.a₆ + γ ^ 2 * E'.a₆)) •
        (1 : E'.toAffine.CoordinateRing) +
      (C (2 * γ * δ + E.a₁ * γ * α - γ ^ 2 * E'.a₁) * X +
        C (2 * γ * ε + E.a₁ * γ * β + E.a₃ * γ - γ ^ 2 * E'.a₃)) • Affine.CoordinateRing.mk E' X = 0 := by
    rw [smul_one_eq, Affine.CoordinateRing.smul]
    simp only [map_add, map_mul, map_pow, map_sub, map_ofNat, ← algebraMap_eq_mk]
    linear_combination h - algebraMap k E'.toAffine.CoordinateRing γ ^ 2 * hr
  obtain ⟨hP, hQ⟩ := Affine.CoordinateRing.smul_basis_eq_zero key
  have c3 := congrArg (fun f => f.coeff 3) hP
  have c2 := congrArg (fun f => f.coeff 2) hP
  have c1 := congrArg (fun f => f.coeff 1) hP
  have c0 := congrArg (fun f => f.coeff 0) hP
  have d1 := congrArg (fun f => f.coeff 1) hQ
  have d0 := congrArg (fun f => f.coeff 0) hQ
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at c3 c2 c1 c0 d1 d0
  norm_num at c3 c2 c1 c0 d1 d0
  exact ⟨by linear_combination c3, by linear_combination c2, by linear_combination c1,
    by linear_combination c0, by linear_combination d1, by linear_combination d0⟩

/-- If `γ² = α³` with `α, γ` nonzero, there is a unit `u` with `u² = α` and `u³ = γ`. -/
lemma exists_unit_sq_cube (α γ : k) (hα : α ≠ 0) (hγ : γ ≠ 0) (h : γ ^ 2 = α ^ 3) :
    ∃ u : kˣ, (u : k) ^ 2 = α ∧ (u : k) ^ 3 = γ := by
  refine ⟨Units.mk0 (γ / α) (div_ne_zero hγ hα), ?_, ?_⟩
  · simp only [Units.val_mk0]; field_simp; linear_combination h
  · simp only [Units.val_mk0]
    rw [div_pow, show γ ^ 3 = γ * α ^ 3 by rw [← h]; ring]
    field_simp

/-- An element whose norm has positive degree is nonzero. -/
lemma natDegree_norm_ne_zero {E : WeierstrassCurve k} {a : E.toAffine.CoordinateRing} {n : ℕ}
    (hn : n ≠ 0) (h : (Algebra.norm k[X] a).natDegree = n) : a ≠ 0 := by
  rintro rfl
  have := Module.Finite.of_basis (Affine.CoordinateRing.basis E)
  rw [Algebra.norm_zero] at h
  simp at h
  omega

/-- **Theorem 2.4 (b)** (pdf p. 61). Every isomorphism of elliptic curves in Weierstrass form sending $O'$ to
$O$ is a change of variables: if $\sigma : k[E] \to k[E']$ is a $k$-algebra isomorphism of the affine coordinate
rings (the comorphism of $\varphi : E' \to E$, see the module docstring), then there are $u \in k^\times$,
$r, s, t \in k$ with `C • E = E'` (Milne's five equations, `variableChange_eq_iff`) and
$\sigma(x) = u^2x' + r$, $\sigma(y) = u^3y' + su^2x' + t$. -/
@[kb "milne2006ec" "Ch. II, Theorem 2.4 (b), pdf p. 61"]
theorem theorem_2_4_b (E E' : WeierstrassCurve k) [E.IsElliptic] [E'.IsElliptic]
    (σ : E.toAffine.CoordinateRing ≃ₐ[k] E'.toAffine.CoordinateRing) :
    ∃ C : VariableChange k, C • E = E' ∧
      σ (Affine.CoordinateRing.mk E (Polynomial.C X)) =
        algebraMap k _ ((C.u : k) ^ 2) * Affine.CoordinateRing.mk E' (Polynomial.C X) + algebraMap k _ C.r ∧
      σ (Affine.CoordinateRing.mk E X) =
        algebraMap k _ ((C.u : k) ^ 3) * Affine.CoordinateRing.mk E' X +
          algebraMap k _ (C.s * (C.u : k) ^ 2) * Affine.CoordinateRing.mk E' (Polynomial.C X) + algebraMap k _ C.t := by
  have hx0 := natDegree_norm_ne_zero (E := E) (by norm_num : (2 : ℕ) ≠ 0) (natDegree_norm_x E)
  have hy0 := natDegree_norm_ne_zero (E := E) (by norm_num : (3 : ℕ) ≠ 0) (natDegree_norm_y E)
  obtain ⟨α, β, hα, hx⟩ := shape_of_natDegree_norm_two E' _
    (by rw [natDegree_norm_algEquiv E E' σ hx0, natDegree_norm_x])
  obtain ⟨γ, δ, ε, hγ, hy⟩ := shape_of_natDegree_norm_three E' _
    (by rw [natDegree_norm_algEquiv E E' σ hy0, natDegree_norm_y])
  have hrel := congrArg σ (weierstrass_relation E)
  simp only [map_add, map_mul, map_pow, AlgEquiv.commutes, hx, hy] at hrel
  obtain ⟨e3, e2, e1, e0, q1, q0⟩ := coeff_equations E E' α β γ δ ε hrel
  obtain ⟨u, hu2, hu3⟩ := exists_unit_sq_cube α γ hα hγ e3
  obtain ⟨s, rfl⟩ : ∃ s, δ = s * α := ⟨δ / α, by field_simp⟩
  have hu : (u : k) ≠ 0 := u.ne_zero
  subst hu2 hu3
  have h1 : (u : k) * E'.a₁ = E.a₁ + 2 * s := by
    refine mul_left_cancel₀ (pow_ne_zero 5 hu) ?_
    linear_combination (-1 : k) * q1
  have h2 : (u : k) ^ 2 * E'.a₂ = E.a₂ - s * E.a₁ + 3 * β - s ^ 2 := by
    refine mul_left_cancel₀ (pow_ne_zero 4 hu) ?_
    linear_combination e2
  have h3 : (u : k) ^ 3 * E'.a₃ = E.a₃ + β * E.a₁ + 2 * ε := by
    refine mul_left_cancel₀ (pow_ne_zero 3 hu) ?_
    linear_combination (-1 : k) * q0
  have h4 : (u : k) ^ 4 * E'.a₄ = E.a₄ - s * E.a₃ + 2 * β * E.a₂ - (ε + β * s) * E.a₁ + 3 * β ^ 2
      - 2 * s * ε := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hu) ?_
    linear_combination e1
  have h6 : (u : k) ^ 6 * E'.a₆ = E.a₆ + β * E.a₄ + β ^ 2 * E.a₂ + β ^ 3 - ε * E.a₃ - ε ^ 2
      - β * ε * E.a₁ := by
    linear_combination e0
  refine ⟨⟨u, β, s, ε⟩, ?_, hx, hy⟩
  ext
  · rw [variableChange_a₁]; simp only [Units.val_inv_eq_inv_val]; field_simp; linear_combination (-1 : k) * h1
  · rw [variableChange_a₂]; simp only [Units.val_inv_eq_inv_val]; field_simp; linear_combination (-1 : k) * h2
  · rw [variableChange_a₃]; simp only [Units.val_inv_eq_inv_val]; field_simp; linear_combination (-1 : k) * h3
  · rw [variableChange_a₄]; simp only [Units.val_inv_eq_inv_val]; field_simp; linear_combination (-1 : k) * h4
  · rw [variableChange_a₆]; simp only [Units.val_inv_eq_inv_val]; field_simp; linear_combination (-1 : k) * h6

end NumberFieldKB.MilneEC.II
