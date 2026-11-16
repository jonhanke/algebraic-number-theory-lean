import Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch4bTwists

/-!
# Milne, Elliptic Curves, Chapter IV §7: the classification of curves of genus 1 over $\mathbb Q$ (7.21–7.22)

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, §7, pdf p. 150.  Conventions as in
`NumberFieldKB.MilneEC.Ch4bTwists`.  7.23 and 7.24 (curves of genus 1 and their jacobians) are not formalized: Mathlib
has no curves of genus 1.

## Proved
* `statement_7_21`: every rational number is the $j$-invariant of an elliptic curve over $\mathbb Q$, and two elliptic
  curves over $\mathbb Q$ have the same $j$-invariant if and only if they become isomorphic over $\mathbb Q^{\mathrm{al}}$
  (Mathlib's `WeierstrassCurve.ofJ_j` and `WeierstrassCurve.exists_variableChange_of_j_eq`).
* `statement_7_22`: for $j \neq 0, 1728$, $d \bmod k^{\times 2} \mapsto E_d$ is a bijection from $k^\times/k^{\times 2}$
  onto the isomorphism classes of elliptic curves over $k$ with $j$-invariant $j$ (characteristic not $2$ or $3$; Milne
  states it for $k = \mathbb Q$).
-/

open WeierstrassCurve

namespace NumberFieldKB.MilneEC

/-- The base change of an elliptic curve over $\mathbb Q$ to $\mathbb Q^{\mathrm{al}}$ is elliptic. -/
instance instIsEllipticBaseChangeQ (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E.baseChange (AlgebraicClosure ℚ)).IsElliptic :=
  inferInstanceAs (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).IsElliptic

/-- **7.21** (pdf p. 150): every element of $\mathbb Q$ is the $j$-invariant of an elliptic curve over $\mathbb Q$,
and two elliptic curves over $\mathbb Q$ have the same $j$-invariant if and only if they become isomorphic over
$\mathbb Q^{\mathrm{al}}$. -/
@[kb "milne2006ec" "Ch. IV, 7.21, pdf p. 150"]
theorem statement_7_21 :
    (∀ j : ℚ, ∃ (E : WeierstrassCurve ℚ) (_ : E.IsElliptic), E.j = j) ∧
    (∀ (E E' : WeierstrassCurve ℚ) [E.IsElliptic] [E'.IsElliptic], E.j = E'.j ↔
      ∃ C : VariableChange (AlgebraicClosure ℚ),
        C • E.baseChange (AlgebraicClosure ℚ) = E'.baseChange (AlgebraicClosure ℚ)) := by
  refine ⟨fun j => ⟨ofJ j, inferInstance, ofJ_j j⟩, ?_⟩
  intro E E' _ _
  have : IsSepClosed (AlgebraicClosure ℚ) := inferInstance
  have hj : ∀ (F : WeierstrassCurve ℚ) [F.IsElliptic], (F.baseChange (AlgebraicClosure ℚ)).j =
      algebraMap ℚ (AlgebraicClosure ℚ) F.j := fun F _ => map_j _ _
  constructor
  · intro h
    exact exists_variableChange_of_j_eq (E := E.baseChange (AlgebraicClosure ℚ))
      (E' := E'.baseChange (AlgebraicClosure ℚ)) (by rw [hj, hj, h])
  · rintro ⟨C, hC⟩
    apply (algebraMap ℚ (AlgebraicClosure ℚ)).injective
    rw [← hj, ← hj]
    exact (variableChange_j (E.baseChange (AlgebraicClosure ℚ)) C).symm.trans (by congr 1)

/-- **7.22** (pdf p. 150), for $j \neq 0, 1728$, over a field $k$ of characteristic not $2$ or $3$ (Milne: $k = \mathbb Q$):
fix $E = E(a,b)$ with $j(E) = j$.  The quadratic twists $E_d$ ($d \in k^\times$, Example 7.12) satisfy
$E_d \cong E_{d'}$ over $k$ if and only if $d'/d \in k^{\times 2}$, and every elliptic curve over $k$ that becomes
isomorphic to $E$ over $k^{\mathrm{al}}$ is isomorphic over $k$ to some $E_d$ (`cor_7_16`): so $d \mapsto E_d$ is a
bijection $k^\times/k^{\times 2} \to \{\text{curves with } j(E') = j\}/\!\cong$.  ($\operatorname{Aut}(E, O) = \mu_2$ is
`prop_7_13`.) -/
@[kb "milne2006ec" "Ch. IV, 7.22, pdf p. 150"]
theorem statement_7_22 {k : Type*} [Field k] [NeZero (2 : k)] [NeZero (3 : k)] (a b : k) [(shortW a b).IsElliptic]
    (hj0 : (shortW a b).j ≠ 0) (hj1728 : (shortW a b).j ≠ 1728) :
    (∀ d d' : k, d ≠ 0 → d' ≠ 0 →
      ((∃ C : VariableChange k, C • quadTwist a b d = quadTwist a b d') ↔ IsSquare (d' / d))) ∧
    (∀ a' b' : k, (∃ C : VariableChange (AlgebraicClosure k),
        C • (shortW a b).baseChange (AlgebraicClosure k) = (shortW a' b').baseChange (AlgebraicClosure k)) →
      ∃ d : k, d ≠ 0 ∧ ∃ C : VariableChange k, C • quadTwist a b d = shortW a' b') := by
  have ha : a ≠ 0 := fun h => hj0 ((shortW_j_zero_iff a b).2 h)
  have hb : b ≠ 0 := fun h => hj1728 ((shortW_j_1728_iff a b).2 h)
  refine ⟨?_, fun a' b' h => cor_7_16 a b a' b' hj0 hj1728 (AlgebraicClosure k) h⟩
  intro d d' hd hd'
  constructor
  · rintro ⟨C, hC⟩
    rw [quadTwist, quadTwist, smul_shortW_eq_iff] at hC
    obtain ⟨-, -, -, h4, h6⟩ := hC
    set v : k := ((C.u⁻¹ : kˣ) : k) with hv
    have hw2 : (d' / d) ^ 2 = v ^ 4 := by
      field_simp
      apply mul_right_cancel₀ ha
      linear_combination -h4
    have hw3 : (d' / d) ^ 3 = v ^ 6 := by
      field_simp
      apply mul_right_cancel₀ hb
      linear_combination -h6
    have hw : d' / d ≠ 0 := div_ne_zero hd' hd
    refine ⟨v, ?_⟩
    apply mul_right_cancel₀ (pow_ne_zero 2 hw)
    rw [← pow_succ', hw3, hw2]; ring
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact div_ne_zero hd' hd (by simpa using hc)
    have hd'' : d' = d * (c * c) := by
      field_simp at hc
      linear_combination hc
    refine ⟨⟨(Units.mk0 c hc0)⁻¹, 0, 0, 0⟩, ?_⟩
    rw [quadTwist, quadTwist, smul_shortW_eq_iff]
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · simp only [inv_inv, Units.val_mk0, hd'']; ring
    · simp only [inv_inv, Units.val_mk0, hd'']; ring

end NumberFieldKB.MilneEC
