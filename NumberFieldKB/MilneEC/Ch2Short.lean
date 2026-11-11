import Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import QuadFormsKB.Citation

/-!
# Milne, *Elliptic Curves*, Chapter II §2: the curves $E(a, b)$ (characteristic not 2 or 3)

Source: J. S. Milne, *Elliptic Curves*, second edition (course notes `ectext6`, 2006), bib key `milne2006ec`.
Locators give pdf pages (printed page = pdf page − 8).

Milne's curve $E(a, b) : Y^2Z = X^3 + aXZ^2 + bZ^3$ (equation (13)) is Mathlib's Weierstrass curve
`shortCurve a b = ⟨0, 0, 0, a, b⟩`. Milne's "discriminant" of $E(a, b)$ is $4a^3 + 27b^2$; Mathlib's `Δ` is
$-16(4a^3 + 27b^2)$ (`Δ_shortCurve`).

An isomorphism of elliptic curves in Weierstrass form sending $O$ to $O'$ is a change of variables
$x = u^2x' + r$, $y = u^3y' + su^2x' + t$ (Theorem 2.4 (b), `Ch2Iso.lean`); Mathlib's `VariableChange` uses the
same convention: `C • W` is the curve $W'$ in the primed coordinates. So "$E(a', b') \cong E(a, b)$ compatibly with
$O$" is `∃ C, C • shortCurve a b = shortCurve a' b'`.

Contents.
* Theorem 2.1 (a), (b), (c). In (b) Milne's exponents are inverted: the map
  $(x : y : z) \mapsto (c^2x : c^3y : z)$ sends $E(a', b')$ to $E(a, b)$ iff $a = c^4a'$, $b = c^6b'$, not
  $a' = c^4a$, $b' = c^6b$ (`theorem_2_1_b_literal_false`).
* Remark 2.2, which needs $b \neq 0$: for $b = 0$ and $-c$ a square the twist is isomorphic
  (`remark_2_2_counterexample`).
* Remark 2.3 (Milne's three curves with prescribed $j$).
* The addition and duplication formulas (p. 52).
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve

variable {k : Type*} [Field k]

/-- Milne's curve $E(a, b) : Y^2Z = X^3 + aXZ^2 + bZ^3$ (Chapter II, equation (13)) as a Mathlib Weierstrass
curve with $a_1 = a_2 = a_3 = 0$, $a_4 = a$, $a_6 = b$. -/
@[kb "milne2006ec" "Ch. II, Theorem 2.1, equation (13), pdf p. 58"]
def shortCurve (a b : k) : WeierstrassCurve k := ⟨0, 0, 0, a, b⟩

@[simp] lemma shortCurve_a₁ (a b : k) : (shortCurve a b).a₁ = 0 := rfl
@[simp] lemma shortCurve_a₂ (a b : k) : (shortCurve a b).a₂ = 0 := rfl
@[simp] lemma shortCurve_a₃ (a b : k) : (shortCurve a b).a₃ = 0 := rfl
@[simp] lemma shortCurve_a₄ (a b : k) : (shortCurve a b).a₄ = a := rfl
@[simp] lemma shortCurve_a₆ (a b : k) : (shortCurve a b).a₆ = b := rfl

/-- Mathlib's discriminant of $E(a, b)$ is $-16$ times Milne's $4a^3 + 27b^2$. -/
theorem Δ_shortCurve (a b : k) : (shortCurve a b).Δ = -16 * (4 * a ^ 3 + 27 * b ^ 2) := by
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, shortCurve]
  ring

/-- The curve $E(a, b)$ is elliptic in Mathlib's sense iff $4a^3 + 27b^2 \neq 0$, in characteristic $\neq 2$. -/
theorem isElliptic_shortCurve_iff [NeZero (2 : k)] (a b : k) :
    (shortCurve a b).IsElliptic ↔ 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, Δ_shortCurve]
  have h16 : (16 : k) ≠ 0 := by
    have : (16 : k) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero _ (NeZero.ne 2)
  constructor
  · intro h h0; apply h; rw [h0]; ring
  · intro h h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · apply h16; linear_combination -h1
    · exact h h1

/-- Milne's $j$-invariant $j(E) = 1728 \cdot 4a^3 / (4a^3 + 27b^2)$ of $E(a, b)$ (Theorem 2.1 (c)) is Mathlib's
`j`. -/
@[kb "milne2006ec" "Ch. II, Theorem 2.1 (c), definition of j, pdf p. 59"]
theorem j_shortCurve (a b : k) [(shortCurve a b).IsElliptic] :
    (shortCurve a b).j = 1728 * (4 * a ^ 3) / (4 * a ^ 3 + 27 * b ^ 2) := by
  have hΔ := (shortCurve a b).Δ'.ne_zero
  rw [coe_Δ', Δ_shortCurve] at hΔ
  have h2 : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 := fun h => hΔ (by rw [h]; ring)
  rw [WeierstrassCurve.j_eq, Δ_shortCurve]
  have hc : (shortCurve a b).c₄ = -48 * a := by
    simp only [c₄, b₂, b₄, shortCurve]; ring
  rw [hc]
  have h16 : (16 : k) ≠ 0 := fun h => hΔ (by rw [h]; ring)
  field_simp
  ring

/-- A projective Weierstrass curve is *nonsingular* (Milne, Chapter I §1 and Definition 1.1 (c)) if every point
of the projective curve with coordinates in an algebraic closure of $k$ is nonsingular. -/
def IsNonsingularCurve (W : WeierstrassCurve k) : Prop :=
  ∀ P : Fin 3 → AlgebraicClosure k, P ≠ 0 →
    (W.baseChange (AlgebraicClosure k)).toProjective.Equation P →
      (W.baseChange (AlgebraicClosure k)).toProjective.Nonsingular P

/-- **Theorem 2.1 (a)**, first statement (pdf p. 58). In characteristic $\neq 2, 3$ every elliptic curve in
Weierstrass form (12) is isomorphic, by a change of variables fixing $O = (0 : 1 : 0)$, to some $E(a, b)$.
(That every elliptic curve has a Weierstrass equation is Theorem 2.4 (a).) -/
@[kb "milne2006ec" "Ch. II, Theorem 2.1 (a), pdf p. 58"]
theorem theorem_2_1_a [NeZero (2 : k)] [NeZero (3 : k)] (W : WeierstrassCurve k) :
    ∃ (C : VariableChange k) (a b : k), C • W = shortCurve a b := by
  have : Invertible (2 : k) := invertibleOfNonzero (NeZero.ne 2)
  have : Invertible (3 : k) := invertibleOfNonzero (NeZero.ne 3)
  obtain ⟨C, hC⟩ := W.exists_variableChange_isShortNF
  refine ⟨C, (C • W).a₄, (C • W).a₆, ?_⟩
  ext <;> simp [shortCurve, a₂_of_isShortNF]

/-- Base change of $E(a, b)$ is $E$ of the images of $a$ and $b$. -/
lemma baseChange_shortCurve (a b : k) :
    (shortCurve a b).baseChange (AlgebraicClosure k) =
      shortCurve (algebraMap k (AlgebraicClosure k) a) (algebraMap k (AlgebraicClosure k) b) := by
  ext <;> simp [shortCurve, WeierstrassCurve.baseChange]

/-- **Theorem 2.1 (a)**, converse (pdf p. 58). In characteristic $\neq 2, 3$, $E(a, b)$ is nonsingular iff
$4a^3 + 27b^2 \neq 0$. -/
@[kb "milne2006ec" "Ch. II, Theorem 2.1 (a), pdf p. 58"]
theorem theorem_2_1_a_nonsingular [NeZero (2 : k)] [NeZero (3 : k)] (a b : k) :
    IsNonsingularCurve (shortCurve a b) ↔ 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 := by
  have hI := isElliptic_shortCurve_iff a b
  unfold IsNonsingularCurve
  rw [baseChange_shortCurve]
  have h2 : (2 : AlgebraicClosure k) ≠ 0 := by
    have := (algebraMap k (AlgebraicClosure k)).injective.ne (NeZero.ne (2 : k))
    rwa [map_ofNat, map_zero] at this
  have h3 : (3 : AlgebraicClosure k) ≠ 0 := by
    have := (algebraMap k (AlgebraicClosure k)).injective.ne (NeZero.ne (3 : k))
    rwa [map_ofNat, map_zero] at this
  have h4 : (4 : AlgebraicClosure k) ≠ 0 := by
    have : (4 : AlgebraicClosure k) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  constructor
  · intro H h0
    have hAB : 4 * (algebraMap k (AlgebraicClosure k) a) ^ 3 +
        27 * (algebraMap k (AlgebraicClosure k) b) ^ 2 = 0 := by
      have := congrArg (algebraMap k (AlgebraicClosure k)) h0
      simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at this
      exact this
    generalize algebraMap k (AlgebraicClosure k) a = A at hAB H
    generalize algebraMap k (AlgebraicClosure k) b = B at hAB H
    obtain ⟨x0, hx1, hx2, hx3⟩ : ∃ x0 : AlgebraicClosure k,
        x0 ^ 3 + A * x0 + B = 0 ∧ 3 * x0 ^ 2 + A = 0 ∧ 2 * A * x0 + 3 * B = 0 := by
      by_cases hA : A = 0
      · have hB : B = 0 := by
          have : 27 * B ^ 2 = 0 := by rw [hA] at hAB; linear_combination hAB
          have h27 : (27 : AlgebraicClosure k) ≠ 0 := by
            have : (27 : AlgebraicClosure k) = 3 ^ 3 := by norm_num
            rw [this]; exact pow_ne_zero _ h3
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h h27
          · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
        subst hA hB
        exact ⟨0, by simp, by simp, by simp⟩
      · have hx2 : 3 * (-3 * B / (2 * A)) ^ 2 + A = 0 := by
          have : 3 * (-3 * B / (2 * A)) ^ 2 + A = (4 * A ^ 3 + 27 * B ^ 2) / (4 * A ^ 2) := by
            field_simp; ring
          rw [this, hAB, zero_div]
        have hx3 : 2 * A * (-3 * B / (2 * A)) + 3 * B = 0 := by
          field_simp; ring
        refine ⟨-3 * B / (2 * A), ?_, hx2, hx3⟩
        have : 3 * ((-3 * B / (2 * A)) ^ 3 + A * (-3 * B / (2 * A)) + B) = 0 := by
          linear_combination (-3 * B / (2 * A)) * hx2 + hx3
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h h3
        · exact h
    have hP : (![x0, 0, 1] : Fin 3 → AlgebraicClosure k) ≠ 0 := by
      intro h
      have := congrFun h 2
      simp at this
    have hEq : (shortCurve A B).toProjective.Equation ![x0, 0, 1] := by
      rw [Projective.equation_some, Affine.equation_iff]
      simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄, shortCurve_a₆]
      linear_combination -hx1
    have hS := H _ hP hEq
    rw [Projective.nonsingular_iff] at hS
    simp only [shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄, shortCurve_a₆,
      Projective.fin3_def_ext] at hS
    obtain ⟨-, hS⟩ := hS
    rcases hS with hS | hS | hS
    · apply hS; linear_combination -hx2
    · apply hS; ring
    · apply hS; linear_combination -hx3
  · intro h P hP hEq
    have hE : (shortCurve (algebraMap k (AlgebraicClosure k) a)
        (algebraMap k (AlgebraicClosure k) b)).IsElliptic := by
      rw [← baseChange_shortCurve]
      have := (hI.2 h)
      exact inferInstanceAs ((shortCurve a b).map (algebraMap k (AlgebraicClosure k))).IsElliptic
    by_cases hz : P 2 ≠ 0
    · rw [Projective.nonsingular_of_Z_ne_zero hz]
      exact (Affine.equation_iff_nonsingular).1 ((Projective.equation_of_Z_ne_zero hz).1 hEq)
    · push Not at hz
      rw [Projective.nonsingular_of_Z_eq_zero hz]
      refine ⟨hEq, Or.inr ?_⟩
      have hx : P 0 = 0 := Projective.X_eq_zero_of_Z_eq_zero hEq hz
      have hy : P 1 ≠ 0 := by
        intro hy
        apply hP
        ext i
        fin_cases i <;> simp [hx, hy, hz]
      simp [hx, hy]

/-- **Theorem 2.1 (b)** (pdf pp. 58–59), corrected. In characteristic $\neq 2, 3$, a change of variables carrying
$E(a, b)$ to $E(a', b')$ has $r = s = t = 0$, and with $c = u$ one has $a = c^4a'$, $b = c^6b'$; the map
$E(a', b') \to E(a, b)$ is $(x : y : z) \mapsto (c^2x : c^3y : z)$. Milne prints $a' = c^4a$, $b' = c^6b$. -/
@[kb "milne2006ec" "Ch. II, Theorem 2.1 (b), pdf p. 58"]
theorem theorem_2_1_b [NeZero (2 : k)] [NeZero (3 : k)] {a b a' b' : k} (C : VariableChange k)
    (hC : C • shortCurve a b = shortCurve a' b') :
    C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ a = (C.u : k) ^ 4 * a' ∧ b = (C.u : k) ^ 6 * b' := by
  have h1 := congrArg WeierstrassCurve.a₁ hC
  have h2 := congrArg WeierstrassCurve.a₂ hC
  have h3 := congrArg WeierstrassCurve.a₃ hC
  have h4 := congrArg WeierstrassCurve.a₄ hC
  have h6 := congrArg WeierstrassCurve.a₆ hC
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄,
    shortCurve_a₆] at h1 h2 h3 h4 h6
  have h2' : (2 : k) ≠ 0 := NeZero.ne 2
  have h3' : (3 : k) ≠ 0 := NeZero.ne 3
  have hu : ((C.u⁻¹ : kˣ) : k) ≠ 0 := (C.u⁻¹).ne_zero
  have hu0 : (C.u : k) ≠ 0 := C.u.ne_zero
  have hs : C.s = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hu
    · simpa [h2'] using h
  have ht : C.t = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h (pow_ne_zero _ hu)
    · simpa [h2', hs] using h
  have hr : C.r = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (pow_ne_zero _ hu)
    · simpa [h3', hs] using h
  refine ⟨hr, hs, ht, ?_, ?_⟩
  · rw [hr, hs, ht] at h4
    rw [← h4]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
    ring
  · rw [hr, ht] at h6
    rw [← h6]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
    ring

/-- **Theorem 2.1 (b)**, converse (pdf p. 59), corrected: if $a = c^4a'$ and $b = c^6b'$ then
$(x : y : z) \mapsto (c^2x : c^3y : z)$, the change of variables $(u, r, s, t) = (c, 0, 0, 0)$, carries
$E(a, b)$ to $E(a', b')$. -/
@[kb "milne2006ec" "Ch. II, Theorem 2.1 (b), converse, pdf p. 59"]
theorem theorem_2_1_b_converse {a b a' b' : k} (c : kˣ) (ha : a = (c : k) ^ 4 * a')
    (hb : b = (c : k) ^ 6 * b') : (⟨c, 0, 0, 0⟩ : VariableChange k) • shortCurve a b = shortCurve a' b' := by
  have hc : (c : k) ≠ 0 := c.ne_zero
  ext
  · simp [variableChange_a₁]
  · simp [variableChange_a₂]
  · simp [variableChange_a₃]
  · simp only [variableChange_a₄, shortCurve_a₄, shortCurve_a₃, shortCurve_a₂, shortCurve_a₁,
      Units.val_inv_eq_inv_val, ha]
    field_simp
    simp
  · simp only [variableChange_a₆, shortCurve_a₄, shortCurve_a₆, shortCurve_a₃, shortCurve_a₂,
      shortCurve_a₁, Units.val_inv_eq_inv_val, hb]
    field_simp
    simp

/-- Theorem 2.1 (b) as printed is false: over $\mathbb Q$ with $c = 2$, $(a, b) = (1, 0)$, $(a', b') = (16, 0)$
satisfy $a' = c^4a$, $b' = c^6b$, but $(x : y : z) \mapsto (c^2x : c^3y : z)$ does not carry $E(a', b')$ to
$E(a, b)$: the change of variables $(c, 0, 0, 0)$ carries $E(1, 0)$ to $E(1/16, 0)$, not to $E(16, 0)$. -/
theorem theorem_2_1_b_literal_false :
    (⟨Units.mk0 2 two_ne_zero, 0, 0, 0⟩ : VariableChange ℚ) • shortCurve (1 : ℚ) 0 ≠ shortCurve (2 ^ 4 * 1) (2 ^ 6 * 0) := by
  intro h
  have := congrArg WeierstrassCurve.a₄ h
  simp only [variableChange_a₄, shortCurve_a₄, shortCurve_a₃, shortCurve_a₂, shortCurve_a₁,
    Units.val_inv_eq_inv_val] at this
  norm_num at this

/-- **Theorem 2.1 (c)** (pdf p. 59), first part: $j$ depends only on the isomorphism class. -/
@[kb "milne2006ec" "Ch. II, Theorem 2.1 (c), pdf p. 59"]
theorem theorem_2_1_c_invariant (W : WeierstrassCurve k) [W.IsElliptic] (C : VariableChange k) :
    (C • W).j = W.j :=
  variableChange_j W C

/-- **Theorem 2.1 (c)** (pdf p. 59), second part: two elliptic curves become isomorphic over an algebraic
closure of $k$ iff they have the same $j$-invariant. -/
@[kb "milne2006ec" "Ch. II, Theorem 2.1 (c), pdf p. 59"]
theorem theorem_2_1_c (E E' : WeierstrassCurve k) [E.IsElliptic] [E'.IsElliptic] :
    (∃ C : VariableChange (AlgebraicClosure k),
        C • E.baseChange (AlgebraicClosure k) = E'.baseChange (AlgebraicClosure k)) ↔ E.j = E'.j := by
  have : (E.baseChange (AlgebraicClosure k)).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap k (AlgebraicClosure k))).IsElliptic)
  have : (E'.baseChange (AlgebraicClosure k)).IsElliptic :=
    inferInstanceAs ((E'.map (algebraMap k (AlgebraicClosure k))).IsElliptic)
  have hE : (E.baseChange (AlgebraicClosure k)).j =algebraMap k (AlgebraicClosure k) E.j :=
    WeierstrassCurve.map_j E (algebraMap k (AlgebraicClosure k))
  have hE' : (E'.baseChange (AlgebraicClosure k)).j = algebraMap k (AlgebraicClosure k) E'.j :=
    WeierstrassCurve.map_j E' (algebraMap k (AlgebraicClosure k))
  constructor
  · rintro ⟨C, hC⟩
    have h : (E'.baseChange (AlgebraicClosure k)).j = (E.baseChange (AlgebraicClosure k)).j := by
      simp_rw [← hC]
      exact variableChange_j _ C
    rw [hE, hE'] at h
    exact ((algebraMap k (AlgebraicClosure k)).injective h).symm
  · intro h
    apply WeierstrassCurve.exists_variableChange_of_j_eq
    rw [hE, hE', h]

/-- **Remark 2.2** (pdf p. 60), with the hypothesis $b \neq 0$ that it needs. In characteristic $\neq 2, 3$, if
$c$ is not a square in $k$ then $Y^2Z = X^3 + ac^2XZ^2 + bc^3Z^3$ is not isomorphic to $E(a, b)$ (it has the same
$j$-invariant, `remark_2_2_j`). -/
@[kb "milne2006ec" "Ch. II, Remark 2.2, pdf p. 60"]
theorem remark_2_2 [NeZero (2 : k)] [NeZero (3 : k)] {a b c : k} (hb : b ≠ 0) (hc : ¬IsSquare c) :
    ¬∃ C : VariableChange k, C • shortCurve a b = shortCurve (a * c ^ 2) (b * c ^ 3) := by
  rintro ⟨C, hC⟩
  obtain ⟨-, -, -, -, hb6⟩ := theorem_2_1_b C hC
  have h : (C.u : k) ^ 6 * c ^ 3 = 1 := by
    have : b * (1 - (C.u : k) ^ 6 * c ^ 3) = 0 := by linear_combination hb6
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hb
    · linear_combination -h
  exact hc ⟨c ^ 2 * (C.u : k) ^ 3, by linear_combination (-c) * h⟩

/-- Remark 2.2: the twist has the same $j$-invariant. -/
@[kb "milne2006ec" "Ch. II, Remark 2.2, pdf p. 60"]
theorem remark_2_2_j {a b c : k} [(shortCurve a b).IsElliptic]
    [(shortCurve (a * c ^ 2) (b * c ^ 3)).IsElliptic] :
    (shortCurve (a * c ^ 2) (b * c ^ 3)).j = (shortCurve a b).j := by
  have hne : ∀ a b : k, (shortCurve a b).IsElliptic → 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 := by
    intro a b _ h
    have hΔ := (shortCurve a b).Δ'.ne_zero
    rw [coe_Δ', Δ_shortCurve] at hΔ
    exact hΔ (by rw [h]; ring)
  have h1 := hne a b inferInstance
  have h2 := hne (a * c ^ 2) (b * c ^ 3) inferInstance
  rw [j_shortCurve, j_shortCurve, div_eq_div_iff h2 h1]
  ring

/-- Remark 2.2 fails for $b = 0$: over $\mathbb Q$, $c = -1$ is not a square, and the "twist" of $E(1, 0)$ by
$c$ is $E(1, 0)$ itself. -/
theorem remark_2_2_counterexample :
    ¬IsSquare (-1 : ℚ) ∧ ∃ C : VariableChange ℚ,
      C • shortCurve (1 : ℚ) 0 = shortCurve (1 * (-1) ^ 2) (0 * (-1) ^ 3) := by
  refine ⟨?_, ⟨1, 0, 0, 0⟩, ?_⟩
  · rintro ⟨r, hr⟩
    nlinarith [mul_self_nonneg r]
  · exact theorem_2_1_b_converse (1 : ℚˣ) (by norm_num) (by norm_num)

/-- **Remark 2.3** (pdf p. 60): $Y^2Z = X^3 + Z^3$ has $j = 0$ (characteristic $\neq 2, 3$). -/
@[kb "milne2006ec" "Ch. II, Remark 2.3, pdf p. 60"]
theorem remark_2_3_zero [NeZero (2 : k)] [NeZero (3 : k)] :
    ∃ _ : (shortCurve (0 : k) 1).IsElliptic, (shortCurve (0 : k) 1).j = 0 := by
  have hE : (shortCurve (0 : k) 1).IsElliptic :=
    (isElliptic_shortCurve_iff _ _).2 (by
      have h27 : (27 : k) ≠ 0 := by
        have : (27 : k) = 3 ^ 3 := by norm_num
        rw [this]; exact pow_ne_zero _ (NeZero.ne 3)
      simpa using h27)
  refine ⟨hE, ?_⟩
  rw [j_shortCurve]
  simp

/-- **Remark 2.3** (pdf p. 60): $Y^2Z = X^3 + XZ^2$ has $j = 1728$ (characteristic $\neq 2, 3$). -/
@[kb "milne2006ec" "Ch. II, Remark 2.3, pdf p. 60"]
theorem remark_2_3_1728 [NeZero (2 : k)] [NeZero (3 : k)] :
    ∃ _ : (shortCurve (1 : k) 0).IsElliptic, (shortCurve (1 : k) 0).j = 1728 := by
  have h : 4 * (1 : k) ^ 3 + 27 * 0 ^ 2 ≠ 0 := by
    simpa using (NeZero.ne (2 : k)) |> fun h2 => (show (4 : k) ≠ 0 by
      have : (4 : k) = 2 ^ 2 := by norm_num
      rw [this]; exact pow_ne_zero _ h2)
  have hE : (shortCurve (1 : k) 0).IsElliptic := (isElliptic_shortCurve_iff _ _).2 h
  refine ⟨hE, ?_⟩
  rw [j_shortCurve, div_eq_iff h]
  ring

/-- **Remark 2.3** (pdf p. 60): for $j \neq 0, 1728$, $Y^2Z = X^3 - \frac{27j}{4(j - 1728)}XZ^2 -
\frac{27j}{4(j - 1728)}Z^3$ has $j$-invariant $j$ (characteristic $\neq 2, 3$). -/
@[kb "milne2006ec" "Ch. II, Remark 2.3, pdf p. 60"]
theorem remark_2_3 [NeZero (2 : k)] [NeZero (3 : k)] (j : k) (h0 : j ≠ 0) (h1728 : j ≠ 1728) :
    ∃ _ : (shortCurve (-(27 * j / (4 * (j - 1728)))) (-(27 * j / (4 * (j - 1728))))).IsElliptic,
      (shortCurve (-(27 * j / (4 * (j - 1728)))) (-(27 * j / (4 * (j - 1728))))).j = j := by
  have h2 : (2 : k) ≠ 0 := NeZero.ne 2
  have h3 : (3 : k) ≠ 0 := NeZero.ne 3
  have h4 : (4 : k) ≠ 0 := by
    have : (4 : k) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  have h27 : (27 : k) ≠ 0 := by
    have : (27 : k) = 3 ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero _ h3
  have h1728k : (1728 : k) ≠ 0 := by
    have : (1728 : k) = 2 ^ 6 * 3 ^ 3 := by norm_num
    rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  have hd : j - 1728 ≠ 0 := sub_ne_zero.2 h1728
  set a : k := -(27 * j / (4 * (j - 1728))) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]; exact neg_ne_zero.2 (div_ne_zero (mul_ne_zero h27 h0) (mul_ne_zero h4 hd))
  have h4a : 4 * a + 27 ≠ 0 := by
    have : 4 * a + 27 = -(27 * 1728) / (j - 1728) := by
      rw [ha]; field_simp; ring
    rw [this]
    exact div_ne_zero (neg_ne_zero.2 (mul_ne_zero h27 h1728k)) hd
  have hne : 4 * a ^ 3 + 27 * a ^ 2 ≠ 0 := by
    have : 4 * a ^ 3 + 27 * a ^ 2 = a ^ 2 * (4 * a + 27) := by ring
    rw [this]; exact mul_ne_zero (pow_ne_zero _ ha0) h4a
  have hE : (shortCurve a a).IsElliptic := (isElliptic_shortCurve_iff _ _).2 hne
  refine ⟨hE, ?_⟩
  rw [j_shortCurve, div_eq_iff hne]
  rw [ha]
  field_simp
  ring

/-- The affine equation of $E(a, b)$ in the form $y^2 = x^3 + ax + b$. -/
lemma shortCurve_equation {a b x y : k} (h : (shortCurve a b).toAffine.Equation x y) :
    y ^ 2 = x ^ 3 + a * x + b := by
  have := (Affine.equation_iff x y).1 h
  simpa using this

/-- **Addition formula** (pdf p. 52). On $E(a, b)$, if $P_1 = (x_1, y_1)$ and $P_2 = (x_2, y_2)$ with
$x_1 \neq x_2$ and $P_1 + P_2 = (x, y)$, then $x(x_1 - x_2)^2 = x_1x_2^2 + x_1^2x_2 - 2y_1y_2 + a(x_1 + x_2) + 2b$
and $y(x_1 - x_2)^3 = W_2y_2 - W_1y_1$. -/
@[kb "milne2006ec" "Ch. II, §2, addition formula, pdf p. 60"]
theorem addition_formula [DecidableEq k] {a b x₁ y₁ x₂ y₂ x y : k}
    (h₁ : (shortCurve a b).toAffine.Nonsingular x₁ y₁) (h₂ : (shortCurve a b).toAffine.Nonsingular x₂ y₂)
    (h : (shortCurve a b).toAffine.Nonsingular x y) (hx : x₁ ≠ x₂)
    (hadd : Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂ = Affine.Point.some x y h) :
    x * (x₁ - x₂) ^ 2 = x₁ * x₂ ^ 2 + x₁ ^ 2 * x₂ - 2 * y₁ * y₂ + a * (x₁ + x₂) + 2 * b ∧
      y * (x₁ - x₂) ^ 3 = (3 * x₁ ^ 2 * x₂ + x₁ ^ 3 + a * (3 * x₁ + x₂) + 4 * b) * y₂ -
        (3 * x₁ * x₂ ^ 2 + x₂ ^ 3 + a * (x₁ + 3 * x₂) + 4 * b) * y₁ := by
  have e₁ := shortCurve_equation h₁.1
  have e₂ := shortCurve_equation h₂.1
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
  rw [Affine.Point.add_of_X_ne hx, Affine.Point.some.injEq] at hadd
  obtain ⟨hxe, hye⟩ := hadd
  have hℓ : (Affine.slope (shortCurve a b).toAffine x₁ x₂ y₁ y₂) * (x₁ - x₂) = y₁ - y₂ := by
    rw [Affine.slope_of_X_ne hx]; exact div_mul_cancel₀ _ hd
  generalize Affine.slope (shortCurve a b).toAffine x₁ x₂ y₁ y₂ = ℓ at hℓ hxe hye
  simp only [Affine.addX, Affine.addY, Affine.negY, Affine.negAddY, shortCurve_a₁, shortCurve_a₂,
    shortCurve_a₃] at hxe hye
  subst hxe hye
  constructor
  · linear_combination ((ℓ * (x₁ - x₂) + (y₁ - y₂))) * hℓ + e₁ + e₂
  · linear_combination (-(ℓ ^ 2 * (x₁ - x₂) ^ 2 + ℓ * (x₁ - x₂) * (y₁ - y₂) + (y₁ - y₂) ^ 2)
      + (2 * x₁ + x₂) * (x₁ - x₂) ^ 2) * hℓ - (y₁ - 3 * y₂) * e₁ - (3 * y₁ - y₂) * e₂

/-- **Addition formula**, degenerate cases (pdf p. 52): if $x_1 = x_2$ and $y_1 = -y_2$ then $P_1 + P_2 = O$. -/
@[kb "milne2006ec" "Ch. II, §2, addition formula, pdf p. 60"]
theorem addition_formula_neg [DecidableEq k] {a b x₁ y₁ : k} (h₁ : (shortCurve a b).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve a b).toAffine.Nonsingular x₁ (-y₁)) :
    Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₁ (-y₁) h₂ = 0 := by
  exact Affine.Point.add_of_Y_eq rfl (by simp)

/-- **Duplication formula** (pdf p. 52). On $E(a, b)$ in characteristic $\neq 2$: if $y = 0$ then $2P = O$;
otherwise $2P = (x_2, y_2)$ with $x_2 = ((3x^2 + a)^2 - 8xy^2)/4y^2 = (x^4 - 2ax^2 - 8bx + a^2)/4(x^3 + ax + b)$
and $y_2 = (x^6 + 5ax^4 + 20bx^3 - 5a^2x^2 - 4abx - a^3 - 8b^2)/(2y)^3$. -/
@[kb "milne2006ec" "Ch. II, §2, duplication formula, pdf p. 60"]
theorem duplication_formula [NeZero (2 : k)] [DecidableEq k] {a b x y x₂ y₂ : k}
    (h : (shortCurve a b).toAffine.Nonsingular x y) (h₂ : (shortCurve a b).toAffine.Nonsingular x₂ y₂)
    (hdbl : Affine.Point.some x y h + Affine.Point.some x y h = Affine.Point.some x₂ y₂ h₂) :
    y ≠ 0 ∧ x₂ = ((3 * x ^ 2 + a) ^ 2 - 8 * x * y ^ 2) / (4 * y ^ 2) ∧
      x₂ = (x ^ 4 - 2 * a * x ^ 2 - 8 * b * x + a ^ 2) / (4 * (x ^ 3 + a * x + b)) ∧
      y₂ = (x ^ 6 + 5 * a * x ^ 4 + 20 * b * x ^ 3 - 5 * a ^ 2 * x ^ 2 - 4 * a * b * x - a ^ 3 - 8 * b ^ 2) /
        (2 * y) ^ 3 := by
  have e := shortCurve_equation h.1
  have h2 : (2 : k) ≠ 0 := NeZero.ne 2
  have hy : y ≠ 0 := by
    intro hy0
    have : Affine.Point.some x y h + Affine.Point.some x y h = 0 :=
      Affine.Point.add_self_of_Y_eq (by simp [hy0])
    rw [this] at hdbl
    exact Affine.Point.some_ne_zero h₂ hdbl.symm
  have hy' : y ≠ (shortCurve a b).toAffine.negY x y := by
    intro h'
    simp only [Affine.negY, shortCurve_a₁, shortCurve_a₃] at h'
    apply hy
    have : 2 * y = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 h2
    · exact h0
  have h2y : 2 * y ≠ 0 := mul_ne_zero h2 hy
  have h4 : (4 : k) ≠ 0 := by
    have : (4 : k) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  rw [Affine.Point.add_self_of_Y_ne hy', Affine.Point.some.injEq] at hdbl
  obtain ⟨hxe, hye⟩ := hdbl
  have hℓ : (Affine.slope (shortCurve a b).toAffine x x y y) * (2 * y) = 3 * x ^ 2 + a := by
    rw [Affine.slope_of_Y_ne rfl hy']
    simp only [Affine.negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄]
    have : y - (-y - 0 * x - 0) = 2 * y := by ring
    rw [this]
    simp only [mul_zero, zero_mul, add_zero, sub_zero]
    exact div_mul_cancel₀ _ h2y
  generalize Affine.slope (shortCurve a b).toAffine x x y y = ℓ at hℓ hxe hye
  simp only [Affine.addX, Affine.addY, Affine.negY, Affine.negAddY, shortCurve_a₁, shortCurve_a₂,
    shortCurve_a₃] at hxe hye
  have hℓ' : ℓ = (3 * x ^ 2 + a) / (2 * y) := by
    rw [eq_div_iff h2y]; exact hℓ
  have hx2 : x₂ = ((3 * x ^ 2 + a) ^ 2 - 8 * x * y ^ 2) / (4 * y ^ 2) := by
    rw [← hxe, hℓ']
    field_simp
    ring
  refine ⟨hy, hx2, ?_, ?_⟩
  · have h4 : 4 * (x ^ 3 + a * x + b) = 4 * y ^ 2 := by rw [e]
    rw [h4, hx2]
    congr 1
    linear_combination (-8 * x) * e
  · rw [← hye, eq_div_iff (pow_ne_zero 3 h2y)]
    linear_combination (-((ℓ * (2 * y)) ^ 2 + ℓ * (2 * y) * (3 * x ^ 2 + a) + (3 * x ^ 2 + a) ^ 2)
      + 3 * x * (2 * y) ^ 2) * hℓ + (12 * x * (3 * x ^ 2 + a) - 8 * (y ^ 2 + (x ^ 3 + a * x + b))) * e

/-- **Duplication formula**, the case $y = 0$ (pdf p. 52): then $2P = O$. -/
@[kb "milne2006ec" "Ch. II, §2, duplication formula, pdf p. 60"]
theorem duplication_formula_zero [DecidableEq k] {a b x : k} (h : (shortCurve a b).toAffine.Nonsingular x 0) :
    Affine.Point.some x 0 h + Affine.Point.some x 0 h = 0 := by
  exact Affine.Point.add_self_of_Y_eq (by simp)

end NumberFieldKB.MilneEC.II
