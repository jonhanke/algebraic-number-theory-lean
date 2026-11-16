import NumberFieldKB.MilneEC.Ch2Reduction
import NumberFieldKB.MilneEC.Ch2Corollary42

/-!
# Milne, *Elliptic Curves*, Chapter IV, Lemma 3.2 for short Weierstrass models

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter IV, Lemma 3.2 (pdf p. 119): for an elliptic curve
over $\mathbb Q_p$ with good reduction and $p \nmid n$, a point $P$ is in $nE(\mathbb Q_p)$ if and only if its
reduction $\bar P$ is in $n\bar E(\mathbb F_p)$.  Milne's proof: reduction $E(\mathbb Q_p) \to \bar E(\mathbb F_p)$ is a
surjective homomorphism with kernel $E^1(\mathbb Q_p)$ (Chapter II, Theorem 4.1 (b), with $E^0 = E$ for good
reduction), and $n$ is bijective on $E^1(\mathbb Q_p)$ (Chapter II, Corollary 4.2).

This file proves it for a short model $Y^2 = X^3 + aX + b$ with $a, b \in \mathbb Z_p$, $p \ne 2$ and
$4a^3 + 27b^2$ a unit (`lemma_3_2_short`), from `theorem_4_1_b` and `corollary_4_2`.  The named statement `Lemma3_2`
(an arbitrary integral Weierstrass model with unit discriminant, every $p$) stays open: Chapter II's $p$-adic theory
in this library is for short models only.
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve

attribute [local instance] Classical.propDecidable

variable {p : ℕ} [Fact p.Prime]

/-- For good reduction ($p \ne 2$, $4a^3 + 27b^2$ a unit) every point of $E(\mathbb Q_p)$ has nonsingular reduction:
$E^0(\mathbb Q_p) = E(\mathbb Q_p)$. -/
theorem mem_E0_of_good (hp : p ≠ 2) (a b : ℤ_[p]) (hΔ : IsUnit (4 * a ^ 3 + 27 * b ^ 2))
    (P : (curveQp a b).toAffine.Point) : P ∈ E0 a b := by
  rw [mem_E0_iff_exists]
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  by_cases hx : ‖x‖ ≤ 1
  · obtain ⟨X, Y, rfl, rfl, hXY⟩ := int_lift h hx
    have heq : (PadicInt.toZMod Y) ^ 2 = (PadicInt.toZMod X) ^ 3 + PadicInt.toZMod a * PadicInt.toZMod X +
        PadicInt.toZMod b := by
      have := congrArg PadicInt.toZMod hXY
      simpa using this
    have hns : (curveFp a b).toAffine.Nonsingular (PadicInt.toZMod X) (PadicInt.toZMod Y) := by
      rw [shortCurve_nonsingular_iff]
      refine ⟨heq, ?_⟩
      by_contra hc
      push_neg at hc
      obtain ⟨h1, h2⟩ := hc
      have h2' : (2 : ZMod p) ≠ 0 := by
        intro h0
        have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
        rw [ZMod.natCast_eq_zero_iff] at this
        exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)
      have hy0 : PadicInt.toZMod Y = 0 := by
        rcases mul_eq_zero.1 h2 with h | h
        · exact absurd h h2'
        · exact h
      have hD : PadicInt.toZMod (4 * a ^ 3 + 27 * b ^ 2) = 0 := by
        rw [hy0] at heq
        simp only [map_add, map_mul, map_pow, map_ofNat]
        linear_combination (4 * (PadicInt.toZMod a) ^ 2 + 15 * (PadicInt.toZMod X) ^ 2 * PadicInt.toZMod a +
          9 * (PadicInt.toZMod X) ^ 4) * h1 - 27 * (PadicInt.toZMod b - (PadicInt.toZMod X) ^ 3 -
          PadicInt.toZMod a * PadicInt.toZMod X) * heq
      exact (hΔ.map PadicInt.toZMod).ne_zero hD
    refine ⟨Affine.Point.some _ _ hns, ?_⟩
    rw [reducePoint_some_of_le hx, residue_coe, residue_coe]
    rfl
  · exact ⟨0, by rw [reducePoint_some_of_gt (not_le.1 hx)]; rfl⟩

/-- **Lemma 3.2** (Milne, pdf p. 119) for a short model with good reduction: for $p \nmid n$, a point $P$ of
$E(\mathbb Q_p)$ is $n$ times a point of $E(\mathbb Q_p)$ if and only if its reduction $P'$ is $n$ times a point of
$\bar E(\mathbb F_p)$. -/
@[kb "milne2006ec" "Ch. IV, Lemma 3.2, pdf p. 119"]
theorem lemma_3_2_short (hp : p ≠ 2) (a b : ℤ_[p]) (hΔ : IsUnit (4 * a ^ 3 + 27 * b ^ 2)) {n : ℤ}
    (hn : ¬(p : ℤ) ∣ n) (P : (curveQp a b).toAffine.Point) (P' : (curveFp a b).toAffine.Point)
    (hPP' : toProjCoords P' = reducePoint P) :
    (∃ Q, n • Q = P) ↔ ∃ Q', n • Q' = P' := by
  have hΔ0 : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 := hΔ.ne_zero
  obtain ⟨G, hG, ρ, hρ, hsurj, hker⟩ := theorem_4_1_b.iso p a b hΔ0
  have hall : ∀ R : (curveQp a b).toAffine.Point, R ∈ G := fun R => by
    rw [← SetLike.mem_coe, hG]; exact mem_E0_of_good hp a b hΔ R
  have hPP : ρ ⟨P, hall P⟩ = P' := toProjCoords_injective p (by rw [hρ, hPP'])
  constructor
  · rintro ⟨Q, rfl⟩
    refine ⟨ρ ⟨Q, hall Q⟩, ?_⟩
    rw [← hPP, ← map_zsmul]
    rfl
  · rintro ⟨Q', hQ'⟩
    obtain ⟨R, hR⟩ := hsurj Q'
    have hD : ρ (⟨P, hall P⟩ - n • R) = 0 := by rw [map_sub, map_zsmul, hR, hQ', hPP, sub_self]
    have hE1 : (P - n • (R : (curveQp a b).toAffine.Point)) ∈ E1 a b := (hker _).1 hD
    obtain ⟨S, hS, hSeq⟩ := (corollary_4_2.bij p a b hΔ0 n hn).surjOn hE1
    refine ⟨R + S, ?_⟩
    simp only at hSeq
    rw [zsmul_add, hSeq]
    abel

end NumberFieldKB.MilneEC.II
