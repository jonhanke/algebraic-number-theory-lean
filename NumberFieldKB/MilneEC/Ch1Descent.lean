import NumberFieldKB.MilneEC.Ch1Maps
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Algebra.Order.Star.Real

/-!
# Milne, Elliptic Curves, Chapter I, Section 5: defining algebraic curves over subfields

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, §5 (pdf pp. 50–52): base change of curves,
Example 5.1, descent systems and models, Propositions 5.2, 5.3, Remark 5.4 (named statements) and
Proposition 5.5 (deduced from them).

**Scope.** Curves are nonsingular projective plane curves.  Milne works with any $\Omega \supseteq k$
whose automorphisms $\Gamma = \mathrm{Aut}(\Omega/k)$ fix exactly `k`; we take $\Omega$ algebraically closed
(the setting of Proposition 5.5).  Then, as in Milne's proof of 5.5, a descent system on `C` is the same as a
*regular action* of $\Gamma$ on $C(\Omega)$: an action $(\sigma, P) \mapsto \sigma P$ such that each map
$P \mapsto \sigma P : ({}^\sigma C)(\Omega) \to C(\Omega)$ is regular (here: given locally by polynomials over
$\Omega$, `IsPointRegular`).  Maps between curves over $\Omega$ are taken on $\Omega$-points, which determine
them since $\Omega$ is algebraically closed.
-/

open MvPolynomial
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace NumberFieldKB.MilneEC

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- The conjugate ${}^\sigma C$ of a curve over $\Omega$ (p. 51): apply `σ` to the coefficients. -/
@[kb "milne2006ec" "Ch. I, §5, Def. of the conjugate curve σC, pdf p. 51"]
def conjCurve (σ : Ω ≃ₐ[k] Ω) (F : MvPolynomial (Fin 3) Ω) : MvPolynomial (Fin 3) Ω :=
  map (σ : Ω →+* Ω) F

/-- `σ` applied to the coordinates of a point of $\mathbb P^2(\Omega)$. -/
def conjPoint (σ : Ω ≃ₐ[k] Ω) (P : ℙ Ω (Fin 3 → Ω)) : ℙ Ω (Fin 3 → Ω) :=
  Projectivization.map
    ({ toFun := fun v i => σ (v i)
       map_add' := fun v w => by ext i; simp
       map_smul' := fun c v => by ext i; simp } : (Fin 3 → Ω) →ₛₗ[(σ : Ω →+* Ω)] (Fin 3 → Ω))
    (fun v w h => by
      funext i
      exact σ.injective (congrFun h i)) P

/-- A map of $\Omega$-points $C_F(\Omega) \to \mathbb P^2(\Omega)$ is **regular** (p. 51): near every point of
$C_F(\Omega)$ it is given by homogeneous polynomials over $\Omega$ of one degree, not all vanishing. -/
def IsPointRegular (F : MvPolynomial (Fin 3) Ω) (g : ℙ Ω (Fin 3 → Ω) → ℙ Ω (Fin 3 → Ω)) : Prop :=
  ∀ P ∈ projectivePoints F Ω, ∃ (d : ℕ) (G : Fin 3 → MvPolynomial (Fin 3) Ω),
    (∀ i, (G i).IsHomogeneous d) ∧ (fun i => eval P.rep (G i)) ≠ 0 ∧
    ∀ Q ∈ projectivePoints F Ω, ∀ hQ : (fun i => eval Q.rep (G i)) ≠ 0,
      g Q = Projectivization.mk Ω _ hQ

/-- An **isomorphism** $C_F \to C_{F'}$ on $\Omega$-points: a regular bijection $C_F(\Omega) \to C_{F'}(\Omega)$
with regular inverse. -/
def IsPointIso (F F' : MvPolynomial (Fin 3) Ω) (g : ℙ Ω (Fin 3 → Ω) → ℙ Ω (Fin 3 → Ω)) : Prop :=
  IsPointRegular F g ∧ Set.MapsTo g (projectivePoints F Ω) (projectivePoints F' Ω) ∧
    ∃ g', IsPointRegular F' g' ∧ Set.MapsTo g' (projectivePoints F' Ω) (projectivePoints F Ω) ∧
      (∀ P ∈ projectivePoints F Ω, g' (g P) = P) ∧ ∀ Q ∈ projectivePoints F' Ω, g (g' Q) = Q

/-- Being an isomorphism on points only depends on the values of the map on the points of the curve. -/
theorem isPointIso_congr {F F' : MvPolynomial (Fin 3) Ω} {g g' : ℙ Ω (Fin 3 → Ω) → ℙ Ω (Fin 3 → Ω)}
    (h : IsPointIso F F' g) (hgg : ∀ P ∈ projectivePoints F Ω, g' P = g P) : IsPointIso F F' g' := by
  obtain ⟨hreg, hmaps, h', hreg', hmaps', hl, hr⟩ := h
  refine ⟨?_, ?_, h', hreg', hmaps', ?_, ?_⟩
  · intro P hP
    obtain ⟨d, G, hG, hne, hQ⟩ := hreg P hP
    exact ⟨d, G, hG, hne, fun Q hQm hQne => by rw [hgg Q hQm]; exact hQ Q hQm hQne⟩
  · intro P hP
    rw [hgg P hP]; exact hmaps hP
  · intro P hP
    rw [hgg P hP]; exact hl P hP
  · intro Q hQ
    rw [hgg _ (hmaps' hQ)]; exact hr Q hQ

/-- A **regular action** of $\Gamma = \mathrm{Aut}(\Omega/k)$ on $C_F(\Omega)$ (p. 51), given as a function
`act σ P`: an action, preserving $C(\Omega)$, with each $Q \mapsto \sigma(\sigma^{-1}_* Q)$ (that is,
$P \mapsto \sigma P$ read on ${}^\sigma C(\Omega)$) an isomorphism ${}^\sigma C \to C$ on points.  This is a
descent system (Milne, proof of Proposition 5.5). -/
@[kb "milne2006ec" "Ch. I, §5, Def. of descent system / regular action, pdf p. 51"]
structure RegularAction (F : MvPolynomial (Fin 3) Ω)
    (act : (Ω ≃ₐ[k] Ω) → ℙ Ω (Fin 3 → Ω) → ℙ Ω (Fin 3 → Ω)) : Prop where
  maps_to : ∀ σ, Set.MapsTo (act σ) (projectivePoints F Ω) (projectivePoints F Ω)
  one_act : ∀ P ∈ projectivePoints F Ω, act 1 P = P
  mul_act : ∀ σ τ, ∀ P ∈ projectivePoints F Ω, act (σ * τ) P = act σ (act τ P)
  regular : ∀ σ, IsPointIso (conjCurve σ F) F (fun Q => act σ (conjPoint σ⁻¹ Q))

/-- The action is **continuous** (p. 52): the stabilizer of each point contains the subgroup fixing a
subfield finitely generated over `k`. -/
def IsContinuousAction (F : MvPolynomial (Fin 3) Ω)
    (act : (Ω ≃ₐ[k] Ω) → ℙ Ω (Fin 3 → Ω) → ℙ Ω (Fin 3 → Ω)) : Prop :=
  ∀ P ∈ projectivePoints F Ω, ∃ S : Finset Ω, ∀ σ : Ω ≃ₐ[k] Ω, (∀ x ∈ S, σ x = x) → act σ P = P

/-- The natural action of $\Gamma$ on $C_{0\Omega}(\Omega)$ for a curve $C_0$ over `k` (p. 51): `σ` acts on
coordinates. -/
def naturalAction (σ : Ω ≃ₐ[k] Ω) (P : ℙ Ω (Fin 3 → Ω)) : ℙ Ω (Fin 3 → Ω) := conjPoint σ P

/-- A finite set `S` of points **rigidifies** `C` (p. 51): the only automorphism of `C` fixing every point
of `S` is the identity. -/
@[kb "milne2006ec" "Ch. I, §5, Def. of a rigidifying set, pdf p. 51"]
def Rigidifies (F : MvPolynomial (Fin 3) Ω) (S : Finset (ℙ Ω (Fin 3 → Ω))) : Prop :=
  ∀ g, IsPointIso F F g → (∀ P ∈ S, g P = P) → ∀ P ∈ projectivePoints F Ω, g P = P

/-- A **model** of `C` over `k` that **splits** the action (p. 51): a curve $C_0 = C_{F_0}$ over `k` and an
isomorphism $C \to C_{0\Omega}$ on points carrying the given action to the natural one. -/
@[kb "milne2006ec" "Ch. I, §5, Def. of a model splitting a descent system; effective, pdf p. 51"]
def IsSplitBy (F : MvPolynomial (Fin 3) Ω) (act : (Ω ≃ₐ[k] Ω) → ℙ Ω (Fin 3 → Ω) → ℙ Ω (Fin 3 → Ω))
    (F₀ : MvPolynomial (Fin 3) k) : Prop :=
  ∃ g, IsPointIso F (baseChange Ω F₀) g ∧
    ∀ σ, ∀ P ∈ projectivePoints F Ω, g (act σ P) = naturalAction σ (g P)

/-- The value of a regular function given by a polynomial `p` is `p` evaluated at the point. -/
theorem evalCoord_mk' {g : MvPolynomial (Fin 2) k} {K : Type*} [Field K] [Algebra k K] {P : K × K}
    (hP : P ∈ affinePoints g K) (p : MvPolynomial (Fin 2) k) :
    evalCoord hP (Ideal.Quotient.mk _ p) = aeval ![P.1, P.2] p := by
  unfold evalCoord
  rw [Ideal.Quotient.lift_mk]; rfl

/-- **Example 5.1 (a)** (p. 50): the curves $X^2 + Y^2 = 1$ and $X^2 + Y^2 = -1$ are not isomorphic over
$\mathbb R$ — there is not even a regular map from the first to the second, which has no real points — but
$(x, y) \mapsto (ix, iy)$ and its inverse $(x, y) \mapsto (-ix, -iy)$ are inverse regular maps over
$\mathbb C$. -/
@[kb "milne2006ec" "Ch. I, Ex. 5.1 (a), pdf p. 50"]
theorem example_5_1_a :
    (¬ ∃ f, IsAffineRegularMap (X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) ℝ)
      (X 0 ^ 2 + X 1 ^ 2 + 1) f) ∧
    IsAffineRegularMap (X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) ℂ) (X 0 ^ 2 + X 1 ^ 2 + 1)
      ![Ideal.Quotient.mk _ (C Complex.I * X 0), Ideal.Quotient.mk _ (C Complex.I * X 1)] ∧
    IsAffineRegularMap (X 0 ^ 2 + X 1 ^ 2 + 1 : MvPolynomial (Fin 2) ℂ) (X 0 ^ 2 + X 1 ^ 2 - 1)
      ![Ideal.Quotient.mk _ (-C Complex.I * X 0), Ideal.Quotient.mk _ (-C Complex.I * X 1)] := by
  have hI (K : Type) [Field K] [Algebra ℂ K] : (algebraMap ℂ K Complex.I) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨f, h⟩
    have hP : ((1 : ℝ), (0 : ℝ)) ∈
        affinePoints (X 0 ^ 2 + X 1 ^ 2 - 1 : MvPolynomial (Fin 2) ℝ) ℝ := by
      simp [affinePoints, evalAt]
    have := h ℝ (1, 0) hP
    simp only [affinePoints, evalAt, Set.mem_ofPred_eq, map_add, map_pow, aeval_X, map_one,
      Matrix.cons_val_zero, Matrix.cons_val_one] at this
    nlinarith [sq_nonneg (evalCoord hP (f 0)), sq_nonneg (evalCoord hP (f 1))]
  · intro K _ _ P hP
    simp only [affinePoints, evalAt, Set.mem_ofPred_eq, map_add, map_sub, map_pow, aeval_X, map_one,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hP
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, evalCoord_mk']
    simp only [affinePoints, evalAt, Set.mem_ofPred_eq, map_add, map_mul, map_pow, aeval_X, aeval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_one]
    linear_combination (algebraMap ℂ K Complex.I ^ 2) * hP + hI K
  · intro K _ _ P hP
    simp only [affinePoints, evalAt, Set.mem_ofPred_eq, map_add, map_pow, aeval_X, map_one,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hP
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, evalCoord_mk']
    simp only [affinePoints, evalAt, Set.mem_ofPred_eq, map_add, map_sub, map_neg, map_mul, map_pow,
      aeval_X, aeval_C, map_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (algebraMap ℂ K Complex.I ^ 2) * hP - hI K

/-- **Example 5.1 (b)** (p. 50): an elliptic curve `E` over an algebraically closed field $\Omega \supseteq k$
arises from an elliptic curve over `k` (is isomorphic over $\Omega$ to the base change of one) if and only if
$j(E) \in k$.  Stated with Mathlib's Weierstrass curves, isomorphisms being changes of variables.  (Milne
does not say $\Omega$ is algebraically closed; for other $\Omega$ the "if" direction fails, because of twists.) -/
@[kb "milne2006ec" "Ch. I, Ex. 5.1 (b), pdf p. 50"]
theorem example_5_1_b [IsAlgClosed Ω] (E : WeierstrassCurve Ω) [E.IsElliptic] :
    (∃ (E₀ : WeierstrassCurve k) (_ : E₀.IsElliptic) (C : WeierstrassCurve.VariableChange Ω),
      C • E₀.baseChange Ω = E) ↔ E.j ∈ Set.range (algebraMap k Ω) := by
  classical
  constructor
  · rintro ⟨E₀, hE₀, C, hC⟩
    have : (E₀.baseChange Ω).IsElliptic :=
      inferInstanceAs ((E₀.map (algebraMap k Ω)).IsElliptic)
    have hj : E.j = algebraMap k Ω E₀.j := by
      subst hC
      have h1 : (E₀.baseChange Ω).j = algebraMap k Ω E₀.j :=
        WeierstrassCurve.map_j E₀ (algebraMap k Ω)
      rw [← h1]
      convert WeierstrassCurve.variableChange_j (E₀.baseChange Ω) C
    exact ⟨E₀.j, hj.symm⟩
  · rintro ⟨j₀, hj₀⟩
    have hE₀ : (WeierstrassCurve.ofJ j₀).IsElliptic := inferInstance
    have : ((WeierstrassCurve.ofJ j₀).baseChange Ω).IsElliptic :=
      inferInstanceAs (((WeierstrassCurve.ofJ j₀).map (algebraMap k Ω)).IsElliptic)
    have h1 : ((WeierstrassCurve.ofJ j₀).baseChange Ω).j = E.j := by
      rw [← hj₀]
      have := WeierstrassCurve.map_j (WeierstrassCurve.ofJ j₀) (algebraMap k Ω)
      rw [WeierstrassCurve.ofJ_j] at this
      exact this
    obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq
      ((WeierstrassCurve.ofJ j₀).baseChange Ω) E h1
    exact ⟨WeierstrassCurve.ofJ j₀, hE₀, C, hC⟩

/-- The fixed field of $\Gamma$ is `k` (p. 51): Milne's standing assumption $\Omega^\Gamma = k$. -/
def FixedFieldIsBase (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] : Prop :=
  ∀ x : Ω, (∀ σ : Ω ≃ₐ[k] Ω, σ x = x) → x ∈ Set.range (algebraMap k Ω)

/-- **Proposition 5.2** (p. 51), as a named statement (Milne, AG 16.16), in the form for algebraically closed
$\Omega$: (full faithfulness) every regular map $C_{0\Omega}(\Omega) \to C'_{0\Omega}(\Omega)$ commuting with the
natural actions comes from a unique regular map $C_0 \to C_0'$ over `k`; (essential image) a curve over $\Omega$
with a regular action is in the image (up to isomorphism) exactly when the action is split by a model —
which is the definition of an effective descent system, so only full faithfulness is recorded. -/
@[kb "milne2006ec" "Ch. I, Prop. 5.2, pdf p. 51"]
structure Prop5_2 : Prop where
  fully_faithful : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω],
    FixedFieldIsBase k Ω → ∀ F₀ F₀' : MvPolynomial (Fin 3) k,
    IsProjectivePlaneCurve F₀ → IsNonsingularProjCurve F₀ →
    IsProjectivePlaneCurve F₀' → IsNonsingularProjCurve F₀' →
    ∀ g : ℙ Ω (Fin 3 → Ω) → ℙ Ω (Fin 3 → Ω), IsPointRegular (baseChange Ω F₀) g →
      Set.MapsTo g (projectivePoints F₀ Ω) (projectivePoints F₀' Ω) →
      (∀ σ : Ω ≃ₐ[k] Ω, ∀ P ∈ projectivePoints F₀ Ω, g (naturalAction σ P) = naturalAction σ (g P)) →
      ∃ φ : ProjRegularMap F₀ F₀', (∀ P, (φ.toFun Ω P).1 = g P.1) ∧
        ∀ ψ : ProjRegularMap F₀ F₀', (∀ P, (ψ.toFun Ω P).1 = g P.1) →
          ∀ (K : Type) [Field K] [Algebra k K], ψ.toFun K = φ.toFun K

/-- **Proposition 5.3** (p. 51), as a named statement (Milne, AG 16.33), for algebraically closed $\Omega$: a
regular action on $C(\Omega)$ is effective (split by a model over `k`) if there is a finite set `S` of points
rigidifying `C` and a subfield of $\Omega$ finitely generated over `k` (generated by a finite set `T`) such that
$\sigma P = P$ for every $P \in S$ and every `σ` fixing it. -/
@[kb "milne2006ec" "Ch. I, Prop. 5.3, pdf p. 51"]
structure Prop5_3 : Prop where
  effective : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω],
    FixedFieldIsBase k Ω → ∀ (F : MvPolynomial (Fin 3) Ω) act,
    IsProjectivePlaneCurve F → IsNonsingularProjCurve F → RegularAction (k := k) F act →
    ∀ (S : Finset (ℙ Ω (Fin 3 → Ω))) (T : Finset Ω), Rigidifies F S →
      (∀ σ : Ω ≃ₐ[k] Ω, (∀ x ∈ T, σ x = x) → ∀ P ∈ S, act σ P = P) →
      ∃ F₀ : MvPolynomial (Fin 3) k, IsProjectivePlaneCurve F₀ ∧ IsNonsingularProjCurve F₀ ∧
        IsSplitBy F act F₀

/-- **Remark 5.4** (p. 52), as a named statement (genus 0: automorphisms of $\mathbb P^1$ are fractional linear;
genus 1: finitely many automorphisms fix a point, II §2 and IV 7.13; genus > 1: finitely many automorphisms,
Hartshorne IV Ex. 5.2): every nonsingular projective (plane) curve over an algebraically closed field is
rigidified by a finite set of points. -/
@[kb "milne2006ec" "Ch. I, Rem. 5.4, pdf p. 52"]
structure Remark5_4 : Prop where
  rigidified : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (F : MvPolynomial (Fin 3) Ω),
    IsProjectivePlaneCurve F → IsNonsingularProjCurve F → ∃ S, Rigidifies F S

/-- **Proposition 5.5** (p. 52), essential image: for $\Omega$ algebraically closed, a nonsingular projective
curve over $\Omega$ with a continuous regular action of $\Gamma$ has a model over `k` splitting the action.
Deduced, as in Milne's proof, from the named statements `Prop5_3` and `Remark5_4`. -/
@[kb "milne2006ec" "Ch. I, Prop. 5.5, pdf p. 52"]
theorem prop_5_5 (h₃ : Prop5_3) (h₄ : Remark5_4) [IsAlgClosed Ω] (hfix : FixedFieldIsBase k Ω)
    (F : MvPolynomial (Fin 3) Ω) (act : (Ω ≃ₐ[k] Ω) → ℙ Ω (Fin 3 → Ω) → ℙ Ω (Fin 3 → Ω))
    (hF : IsProjectivePlaneCurve F) (hns : IsNonsingularProjCurve F) (hact : RegularAction F act)
    (hcont : IsContinuousAction F act) :
    ∃ F₀ : MvPolynomial (Fin 3) k, IsProjectivePlaneCurve F₀ ∧ IsNonsingularProjCurve F₀ ∧
      IsSplitBy F act F₀ := by
  classical
  obtain ⟨S, hS⟩ := h₄.rigidified Ω F hF hns
  have hrig : Rigidifies F (S.filter (· ∈ projectivePoints F Ω)) := by
    intro g hg hfix P hP
    set g' : ℙ Ω (Fin 3 → Ω) → ℙ Ω (Fin 3 → Ω) :=
      fun Q => if Q ∈ projectivePoints F Ω then g Q else Q with hg'
    have hg'eq : ∀ Q ∈ projectivePoints F Ω, g' Q = g Q := fun Q hQ => by simp [hg', hQ]
    have hfix' : ∀ Q ∈ S, g' Q = Q := by
      intro Q hQ
      by_cases hQp : Q ∈ projectivePoints F Ω
      · rw [hg'eq Q hQp]; exact hfix Q (Finset.mem_filter.mpr ⟨hQ, hQp⟩)
      · simp [hg', hQp]
    rw [← hg'eq P hP]
    exact hS g' (isPointIso_congr hg hg'eq) hfix' P hP
  choose f hf using fun P : ℙ Ω (Fin 3 → Ω) =>
    (by
      by_cases hP : P ∈ projectivePoints F Ω
      · obtain ⟨T, hT⟩ := hcont P hP
        exact ⟨T, fun _ => hT⟩
      · exact ⟨∅, fun h => absurd h hP⟩ : ∃ T : Finset Ω, P ∈ projectivePoints F Ω →
        ∀ σ : Ω ≃ₐ[k] Ω, (∀ x ∈ T, σ x = x) → act σ P = P)
  refine h₃.effective k Ω hfix F act hF hns hact _ ((S.filter (· ∈ projectivePoints F Ω)).biUnion f)
    hrig ?_
  intro σ hσ P hP
  have hPm := (Finset.mem_filter.mp hP)
  exact hf P hPm.2 σ fun x hx => hσ x (Finset.mem_biUnion.mpr ⟨P, hP, hx⟩)

/-- Applying an automorphism to the coordinates of a nonzero vector gives a nonzero vector. -/
theorem conj_ne_zero (σ : Ω ≃ₐ[k] Ω) {v : Fin 3 → Ω} (hv : v ≠ 0) : (fun i => σ (v i)) ≠ 0 := by
  intro h
  apply hv
  funext i
  exact σ.injective (by simpa using congrFun h i)

/-- `conjPoint` on a point given by a nonzero vector. -/
theorem conjPoint_mk (σ : Ω ≃ₐ[k] Ω) (v : Fin 3 → Ω) (hv : v ≠ 0) :
    conjPoint σ (Projectivization.mk Ω v hv) =
      Projectivization.mk Ω (fun i => σ (v i)) (conj_ne_zero σ hv) := rfl

/-- `conjPoint` on a point, in terms of its chosen representative. -/
theorem conjPoint_rep (σ : Ω ≃ₐ[k] Ω) (P : ℙ Ω (Fin 3 → Ω)) :
    conjPoint σ P = Projectivization.mk Ω (fun i => σ (P.rep i)) (conj_ne_zero σ P.rep_nonzero) := by
  conv_lhs => rw [← Projectivization.mk_rep P]
  rfl

/-- A nonzero vector equal to the chosen representative of `P` represents `P`. -/
theorem mk_eq_of_eq_rep {P : ℙ Ω (Fin 3 → Ω)} {w : Fin 3 → Ω} (hw : w ≠ 0) (h : w = P.rep) :
    Projectivization.mk Ω w hw = P := by
  subst h
  exact Projectivization.mk_rep P

theorem conjPoint_one (P : ℙ Ω (Fin 3 → Ω)) : conjPoint (1 : Ω ≃ₐ[k] Ω) P = P := by
  induction P using Projectivization.ind with
  | h v hv => exact conjPoint_mk 1 v hv

theorem conjPoint_mul (σ τ : Ω ≃ₐ[k] Ω) (P : ℙ Ω (Fin 3 → Ω)) :
    conjPoint (σ * τ) P = conjPoint σ (conjPoint τ P) := by
  induction P using Projectivization.ind with
  | h v hv => rfl

/-- The natural action preserves the points of a curve defined over `k`. -/
theorem conjPoint_mem {F₀ : MvPolynomial (Fin 3) k} {d : ℕ} (hF₀ : F₀.IsHomogeneous d)
    (σ : Ω ≃ₐ[k] Ω) {P : ℙ Ω (Fin 3 → Ω)} (hP : P ∈ projectivePoints (baseChange Ω F₀) Ω) :
    conjPoint σ P ∈ projectivePoints (baseChange Ω F₀) Ω := by
  have hh : (baseChange Ω F₀).IsHomogeneous d := hF₀.map _
  induction P using Projectivization.ind with
  | h v hv =>
    rw [mem_projectivePoints_mk hh] at hP
    rw [conjPoint_mk, mem_projectivePoints_mk hh]
    rw [aeval_map_algebraMap] at hP ⊢
    have h := comp_aeval_apply (f := v) (σ : Ω →ₐ[k] Ω) F₀
    rw [hP, map_zero] at h
    exact h.symm

/-- The conjugate of a curve defined over `k` is the curve itself. -/
theorem conjCurve_baseChange (σ : Ω ≃ₐ[k] Ω) (F₀ : MvPolynomial (Fin 3) k) :
    conjCurve σ (baseChange Ω F₀) = baseChange Ω F₀ := by
  unfold conjCurve
  rw [map_map]
  have : (σ : Ω →+* Ω).comp (algebraMap k Ω) = algebraMap k Ω :=
    RingHom.ext fun x => σ.commutes x
  rw [this]

/-- The identity is an isomorphism of a curve with itself on points. -/
theorem isPointIso_id (F : MvPolynomial (Fin 3) Ω) : IsPointIso F F id := by
  classical
  have hreg : IsPointRegular F id := by
    intro P _
    refine ⟨1, fun i => X i, fun i => isHomogeneous_X _ _, ?_, ?_⟩
    · simpa using P.rep_nonzero
    · intro Q _ hQ
      exact (mk_eq_of_eq_rep hQ (by funext i; simp)).symm
  exact ⟨hreg, fun P hP => hP, id, hreg, fun P hP => hP, fun P _ => rfl, fun Q _ => rfl⟩

/-- **Proposition 5.5** (p. 52), the other half of the essential image: for a curve $C_0$ over `k`, the natural
action of $\Gamma$ on $C_{0\Omega}(\Omega)$ is a continuous regular action. -/
@[kb "milne2006ec" "Ch. I, Prop. 5.5, pdf p. 52"]
theorem prop_5_5_natural (F₀ : MvPolynomial (Fin 3) k) (hF₀ : F₀.IsHomogeneous F₀.totalDegree) :
    RegularAction (baseChange Ω F₀) (naturalAction (k := k)) ∧
      IsContinuousAction (baseChange Ω F₀) (naturalAction (k := k)) := by
  have hh : (baseChange Ω F₀).IsHomogeneous F₀.totalDegree := hF₀.map _
  refine ⟨⟨fun σ P hP => conjPoint_mem hF₀ σ hP, fun P _ => conjPoint_one P,
    fun σ τ P _ => conjPoint_mul σ τ P, fun σ => ?_⟩, ?_⟩
  · rw [conjCurve_baseChange]
    have : (fun Q => naturalAction σ (conjPoint σ⁻¹ Q)) = id := by
      funext Q
      simp only [naturalAction, id]
      rw [← conjPoint_mul, mul_inv_cancel, conjPoint_one]
    rw [this]
    exact isPointIso_id _
  · classical
    intro P _
    refine ⟨Finset.univ.image P.rep, fun σ hσ => ?_⟩
    show conjPoint σ P = P
    rw [conjPoint_rep]
    apply mk_eq_of_eq_rep
    funext i
    exact hσ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

end NumberFieldKB.MilneEC

end
