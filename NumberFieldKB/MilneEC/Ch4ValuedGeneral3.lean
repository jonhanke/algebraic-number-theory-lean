import NumberFieldKB.MilneEC.Ch4ValuedGeneral2

/-!
# Lemma 3.2 over a Henselian valuation ring, for general Weierstrass models

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter II §4 (Corollary 4.2, pdf p. 71) and
Chapter IV, Lemma 3.2 (pdf p. 119).  Continuation of `Ch4ValuedGeneral2.lean`.

* `exists_zsmul_eq_of_redPt_eq_zero`: for $n$ a unit of $R$, every point of the kernel of reduction is $nQ$ with
  $Q$ in the kernel.  The $x$-coordinate comes from `exists_x_of_hensel_valued`; for $y$ one adjoins a root of
  the quadratic $Y^2 + (a_1x_1 + a_3)Y - (x_1^3 + \cdots + a_6)$ and uses the conjugation
  (`exists_y_aux_gen`), which forces $2P = O$.  The case $2P = O$ is handled directly: if $2$ is a unit of
  $R$ then $P = O$ by `eq_zero_of_zsmul_eq_zero`, otherwise $n$ is odd and $nP = P$.
* `lemma_3_2_valued`: $P \in nE(K)$ if and only if $\bar P \in n\bar E(k)$.
-/

namespace NumberFieldKB.MilneEC.II.ValuedGen

open WeierstrassCurve Polynomial IsLocalRing

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {W : WeierstrassCurve R}

/-- **Corollary 4.2** over $R$ (Milne, pdf p. 71), surjectivity: for $n$ a unit of $R$, every point of
$E^1(K)$ is $n$ times a point of $E^1(K)$ (general Weierstrass model, unit discriminant). -/
theorem exists_zsmul_eq_of_redPt_eq_zero [HenselianLocalRing R] (hΔ : IsUnit W.Δ) {n : ℤ}
    (hn : IsUnit (n : R)) {P : (curveK K W).toAffine.Point} (hP : redPt W hΔ P = 0) :
    ∃ Q, redPt W hΔ Q = 0 ∧ n • Q = P := by
  cases P with
  | zero => exact ⟨0, rfl, zsmul_zero n⟩
  | some xP yP hPns =>
    have hx := (redPt_eq_zero_iff hΔ _).1 hP xP yP hPns rfl
    by_cases h2 : (2 : ℕ) • Affine.Point.some xP yP hPns = 0
    · by_cases hu : IsUnit (2 : R)
      · exfalso
        have h2z : (2 : ℤ) • Affine.Point.some xP yP hPns = 0 := by
          rw [two_zsmul]; rw [two_nsmul] at h2; exact h2
        exact Affine.Point.some_ne_zero hPns
          (eq_zero_of_zsmul_eq_zero hΔ (n := 2) (by simpa using hu) hP h2z)
      · have h2z : (2 : ℤ) • Affine.Point.some xP yP hPns = 0 := by
          rw [two_zsmul]; rw [two_nsmul] at h2; exact h2
        refine ⟨_, hP, ?_⟩
        rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
        · exfalso
          apply hu
          have h1 : IsUnit ((k + k : ℤ) : R) := hk ▸ hn
          have h2k : ((k + k : ℤ) : R) = 2 * (k : R) := by push_cast; ring
          rw [h2k] at h1
          exact isUnit_of_mul_isUnit_left h1
        · have hk2 : (k * 2) • Affine.Point.some xP yP hPns = 0 := by
            rw [← smul_smul, h2z, smul_zero]
          rw [hk, add_zsmul, one_zsmul, mul_comm 2 k, hk2, zero_add]
    · obtain ⟨x₁, hx₁, h₁⟩ := exists_x_of_hensel_valued (K := K) W hn hx
      have hΔK := curveK_Δ_ne_zero (K := K) W hΔ
      obtain ⟨y₁, hy₁⟩ := exists_y_aux_gen (curveK K W) hΔK hPns h2 h₁
      have hQ := (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔK).1 hy₁
      rcases smul_eq_of_eval (curveK K W) hΔK hPns hQ h₁ with e | e
      · exact ⟨_, redPt_some_of_not_isInt hΔ hQ hx₁, e⟩
      · obtain ⟨h', hneg⟩ : ∃ h', -Affine.Point.some x₁ y₁ hQ =
            Affine.Point.some x₁ ((curveK K W).toAffine.negY x₁ y₁) h' := ⟨_, Affine.Point.neg_some hQ⟩
        rw [hneg] at e
        exact ⟨_, redPt_some_of_not_isInt hΔ h' hx₁, e⟩

/-- **Lemma 3.2** over a Henselian valuation ring (Milne, pdf p. 119), general Weierstrass model with unit
discriminant: for $n$ a unit of $R$, a point $P \in E(K)$ is in $nE(K)$ if and only if its reduction is in
$n\bar E(k)$. -/
theorem lemma_3_2_valued [HenselianLocalRing R] (hΔ : IsUnit W.Δ) {n : ℤ} (hn : IsUnit (n : R))
    (P : (curveK K W).toAffine.Point) :
    (∃ Q, n • Q = P) ↔ ∃ Q', n • Q' = redPt W hΔ P := by
  constructor
  · rintro ⟨Q, rfl⟩
    exact ⟨redPt W hΔ Q, by rw [← redHom_apply, ← redHom_apply, map_zsmul]⟩
  · rintro ⟨Q', hQ'⟩
    obtain ⟨R₀, hR₀⟩ := redPt_surjective (K := K) hΔ Q'
    have hD : redPt W hΔ (P - n • R₀) = 0 := by
      rw [← redHom_apply, map_sub, map_zsmul, redHom_apply, redHom_apply, hR₀, hQ', sub_self]
    obtain ⟨S, -, hS⟩ := exists_zsmul_eq_of_redPt_eq_zero hΔ hn hD
    exact ⟨R₀ + S, by rw [zsmul_add, hS]; abel⟩

end NumberFieldKB.MilneEC.II.ValuedGen
