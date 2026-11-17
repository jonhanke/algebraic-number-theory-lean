import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.Coset.Card
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch2Reduction
import NumberFieldKB.MilneEC.Ch2Torsion

/-!
# Milne, *Elliptic Curves*, Chapter II, Remark 5.11: realization of the Mazur groups, part B

Source: J. S. Milne, *Elliptic Curves*, second edition (2006), bib key `milne2006ec`, Remark 5.11 (pdf p. 76).

Part B is the upper-bound machinery. For $E : Y^2 = X^3 + aX + b$ with $a, b \in \mathbb Z$ and a prime
$p \ne 2$ not dividing $4a^3 + 27b^2$, reduction mod $p$ is an injective group homomorphism
$E(\mathbb Q)_{\mathrm{tors}} \to \bar E(\mathbb F_p)$ (`torsionReduce`; Corollary 5.7 and `red_add`), so
$|E(\mathbb Q)_{\mathrm{tors}}|$ divides $|\bar E(\mathbb F_p)|$, which is $1 + \#\{(x, y) \in \mathbb F_p^2 :
y^2 = x^3 + ax + b\}$ (`card_torsion_dvd`), a quantity computable by `decide`.
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve

namespace MazurReal

variable (p : ℕ) [Fact p.Prime]

/-- The number of points of $y^2 = x^3 + Ax + B$ over $\mathbb F_p$ (including $O$) as a type. -/
abbrev FpPts (A B : ZMod p) : Type := Option {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 + A * xy.1 + B}

lemma card_point (A B : ZMod p) [(shortCurve A B).IsElliptic] :
    Nat.card (shortCurve A B).toAffine.Point = Nat.card (FpPts p A B) := by
  refine Nat.card_congr
    { toFun := fun P => match P with
        | .zero => none
        | .some x y h => some ⟨(x, y), by
            have := (Affine.equation_iff (W := (shortCurve A B).toAffine) x y).1 h.1
            simp [shortCurve] at this
            linear_combination this⟩
      invFun := fun P => match P with
        | none => 0
        | some ⟨(x, y), h⟩ => Affine.Point.some x y
            ((Affine.equation_iff_nonsingular (W := (shortCurve A B).toAffine)).1
              (by rw [Affine.equation_iff]; simp [shortCurve]; linear_combination h))
      left_inv := ?_
      right_inv := ?_ }
  · rintro (_ | ⟨x, y, h⟩) <;> rfl
  · rintro (_ | ⟨⟨x, y⟩, h⟩) <;> rfl

lemma isElliptic_curveFp {a b : ℤ} (hp2 : p ≠ 2) (hgood : ¬(p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2) :
    (shortCurve (a : ZMod p) (b : ZMod p)).IsElliptic := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have : NeZero (2 : ZMod p) := ⟨h2⟩
  rw [isElliptic_shortCurve_iff]
  intro h0
  apply hgood
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact h0

/-- Reduction mod $p$ is an injective homomorphism $E(\mathbb Q)_{\mathrm{tors}} \to \bar E(\mathbb F_p)$. -/
theorem exists_torsionReduce {a b : ℤ} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (hp2 : p ≠ 2)
    (hgood : ¬(p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2) :
    ∃ f : AddCommGroup.torsion (curveQ a b).toAffine.Point →+
        (curveFp (a : ℤ_[p]) (b : ℤ_[p])).toAffine.Point, Function.Injective f := by
  have hmem : ∀ P : AddCommGroup.torsion (curveQ a b).toAffine.Point,
      toQp p a b (P : (curveQ a b).toAffine.Point) ∈ E0 (a : ℤ_[p]) (b : ℤ_[p]) := fun P =>
    torsion_mem_E0 p hΔ hp2 hgood ((AddCommGroup.mem_torsion _).1 P.2)
  choose F hF using fun P => (mem_E0_iff_exists _).1 (hmem P)
  have hadd : ∀ P Q, F (P + Q) = F P + F Q := fun P Q => by
    apply toProjCoords_injective p
    rw [hF (P + Q), (red_add (hF P) (hF Q))]
    simp [map_add]
  refine ⟨{ toFun := F, map_zero' := ?_, map_add' := hadd }, ?_⟩
  · apply toProjCoords_injective p
    rw [hF 0]
    simp only [ZeroMemClass.coe_zero, map_zero]
    rfl
  · intro P Q h
    have h' : toProjCoords (F P) = toProjCoords (F Q) := congrArg _ h
    rw [hF P, hF Q] at h'
    have := corollary_5_7_unconditional p hΔ hp2 hgood
      ((AddCommGroup.mem_torsion _).1 P.2) ((AddCommGroup.mem_torsion _).1 Q.2) h'
    exact Subtype.ext this

/-- **The upper bound by reduction.** For $p \ne 2$ of good reduction, $|E(\mathbb Q)_{\mathrm{tors}}|$ divides
$1 + \#\{(x, y) \in \mathbb F_p^2 : y^2 = x^3 + ax + b\}$. -/
theorem card_torsion_dvd {a b : ℤ} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (hp2 : p ≠ 2)
    (hgood : ¬(p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2) :
    Nat.card (AddCommGroup.torsion (curveQ a b).toAffine.Point) ∣
      Nat.card (FpPts p (a : ZMod p) (b : ZMod p)) := by
  obtain ⟨f, hf⟩ := exists_torsionReduce p hΔ hp2 hgood
  have h1 := AddSubgroup.card_dvd_of_injective f hf
  have := isElliptic_curveFp p (a := a) (b := b) hp2 hgood
  have hfp : curveFp (a : ℤ_[p]) (b : ℤ_[p]) = shortCurve (a : ZMod p) (b : ZMod p) := by
    simp [curveFp]
  rw [hfp] at h1
  rwa [card_point] at h1

lemma card_FpPts (A B : ZMod p) :
    Nat.card (FpPts p A B) =
      1 + (Finset.univ.filter (fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 + A * xy.1 + B)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_subtype]
  ring

end MazurReal

end NumberFieldKB.MilneEC.II
