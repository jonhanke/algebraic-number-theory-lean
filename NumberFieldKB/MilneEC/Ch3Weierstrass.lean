import NumberFieldKB.MilneEC.Ch3Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.LFunction

/-!
# Milne, Elliptic Curves, Chapter III §2–§3: ℘, Eisenstein series, `E(Λ)`, the `j`-invariant

Items of Milne, *Elliptic Curves* (`milne2006ec`) about the Weierstrass function and the curve
`E(Λ)`:

* Lemma 2.3, Proposition 2.4, the definition of `℘` and Proposition 2.6 are in Mathlib
  (`PeriodPair`, Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean); they are tagged
  and restated in the book's form.
* Proposition 2.5 (`G_{2k}(z)` is holomorphic on `ℍ`) from Mathlib's Eisenstein series.
* Lemma 3.6 (`4X³ - g₄X - g₆` has distinct roots) is proved here from Mathlib's discriminant
  modular form `Δ = η²⁴ ≠ 0` and `Δ = (E₄³ - E₆²)/1728`, not by Milne's argument (which uses
  Proposition 2.1).
* The `j`-invariant and Theorem 3.10 are in `Ch3JInvariant.lean`.

Milne's `g₄`, `g₆` are Mathlib's `PeriodPair.g₂`, `PeriodPair.g₃` (Mathlib follows the
classical names `g₂ = 60 G₄`, `g₃ = 140 G₆`).
-/

open Complex Set Filter Topology Real UpperHalfPlane ModularForm EisensteinSeries
open scoped MatrixGroups

namespace NumberFieldKB.MilneEC.III

/-! ### Lemma 2.3, Proposition 2.4, the definition of `℘`, Proposition 2.6 (Mathlib) -/

/-- Lemma 2.3 (Milne, pdf p. 92): for a lattice `Λ ⊂ ℂ`, `∑_{ω ≠ 0} 1/|ω|³` converges.
(The term `ω = 0` is `0⁻¹ = 0` in Lean.)  From Mathlib's `ZLattice.summable_norm_pow_inv`
(rank `2 < 3`). -/
@[kb "milne2006ec" "Ch. III, Lemma 2.3, pdf p. 92"]
theorem lemma_2_3 (L : PeriodPair) : Summable fun ω : L.lattice => ‖(ω : ℂ)‖⁻¹ ^ 3 :=
  ZLattice.summable_norm_pow_inv L.lattice 3 (by simp)

-- Proposition 2.4 (pdf p. 93): the series for `℘` and `℘'` converge locally uniformly (Milne:
-- normally on compact sets) to doubly periodic meromorphic functions with `℘' = d℘/dz`.
attribute [kb "milne2006ec" "Ch. III, Prop. 2.4, pdf p. 93"]
  PeriodPair.hasSumLocallyUniformly_weierstrassP PeriodPair.hasSumLocallyUniformly_derivWeierstrassP
  PeriodPair.periodic_weierstrassP PeriodPair.periodic_derivWeierstrassP
  PeriodPair.meromorphic_weierstrassP PeriodPair.meromorphic_derivWeierstrassP
  PeriodPair.deriv_weierstrassP

-- Definition of `℘` and `℘'` (pdf p. 93).  Mathlib sums `1/(z - ω)² - 1/ω²` over all `ω ∈ Λ`;
-- the term `ω = 0` is `1/z² - 0`, Milne's `z⁻²`.
attribute [kb "milne2006ec" "Ch. III, §2, def. of the Weierstrass function, pdf p. 93"]
  PeriodPair.weierstrassP PeriodPair.derivWeierstrassP

-- Definition of the Eisenstein series of a lattice `G_{2k}(Λ) = ∑_{ω ≠ 0} ω^{-2k}` (pdf p. 94).
attribute [kb "milne2006ec" "Ch. III, §2, def. of Eisenstein series G_2k(Λ), pdf p. 94"] PeriodPair.G

-- Proposition 2.6 (pdf p. 94) and Exercise 3.24 (b) (pdf p. 108; Mathlib's proof is by the
-- Laurent expansion at `0`, as the exercise asks).
attribute [kb "milne2006ec" "Ch. III, Prop. 2.6, pdf p. 94"] PeriodPair.derivWeierstrassP_sq
attribute [kb "milne2006ec" "Ch. III, Prop. 2.6, g₄ = 60G₄, g₆ = 140G₆, pdf p. 94"]
  PeriodPair.g₂ PeriodPair.g₃

/-- Proposition 2.6 (Milne, pdf p. 94) in the book's notation:
`℘'(z)² = 4℘(z)³ - g₄℘(z) - g₆` with `g₄ = 60 G₄(Λ)`, `g₆ = 140 G₆(Λ)`, for `z ∉ Λ`. -/
@[kb "milne2006ec" "Ch. III, Prop. 2.6, pdf p. 94"]
theorem prop_2_6 (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    L.derivWeierstrassP z ^ 2 =
      4 * L.weierstrassP z ^ 3 - 60 * L.G 4 * L.weierstrassP z - 140 * L.G 6 := by
  rw [L.derivWeierstrassP_sq z hz]
  simp [PeriodPair.g₂, PeriodPair.g₃]

/-- Homogeneity (Milne, pdf p. 94): `G_{k}(cΛ) = c^{-k} G_{k}(Λ)`. -/
@[kb "milne2006ec" "Ch. III, §2, G_2k(cΛ) = c^(-2k) G_2k(Λ), pdf p. 94"]
theorem G_of_lattice_eq_smul {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : L'.lattice = (Submodule.span ℤ {c * L.ω₁, c * L.ω₂})) (k : ℕ) :
    L'.G k = (c ^ k)⁻¹ * L.G k := by
  have hinj : Function.Injective (LinearMap.mulLeft ℤ c : ℂ →ₗ[ℤ] ℂ) := fun a b hab =>
    mul_left_cancel₀ hc hab
  have hmap : L.lattice.map (LinearMap.mulLeft ℤ c : ℂ →ₗ[ℤ] ℂ) = L'.lattice := by
    rw [h, PeriodPair.lattice, Submodule.map_span, Set.image_pair]
    simp
  let e : L.lattice ≃ L'.lattice :=
    ((Submodule.equivMapOfInjective _ hinj L.lattice).trans (LinearEquiv.ofEq _ _ hmap)).toEquiv
  have he : ∀ l, ((e l : L'.lattice) : ℂ) = c * l := fun l => rfl
  unfold PeriodPair.G
  rw [← e.tsum_eq]
  simp_rw [he, mul_pow, mul_inv]
  rw [tsum_mul_left]

/-! ### Eisenstein series on the upper half-plane (Proposition 2.5) -/

/-- The lattice `ℤτ + ℤ` of `τ ∈ ℍ`. -/
noncomputable def periodPairOf (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.im h
    have h2 := congrArg Complex.re h
    simp at h1 h2
    have hτ := τ.im_pos
    have hs : s = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hτ.ne'
    subst hs
    simp at h2
    exact ⟨rfl, h2⟩

/-- Milne's `G_{2k}(z) = ∑_{(m,n) ≠ (0,0)} (mz + n)^{-2k}` (pdf p. 94), as a function on `ℂ`
(the term `(0,0)` is `0⁻¹ = 0`).  Here `k` is the weight (Milne's `2k`). -/
@[kb "milne2006ec" "Ch. III, §2, def. of Eisenstein series G_2k(z), pdf p. 94"]
noncomputable def eisensteinG (k : ℕ) (z : ℂ) : ℂ := ∑' v : ℤ × ℤ, ((v.1 * z + v.2) ^ k)⁻¹

/-- Milne (pdf p. 94): `G_{2k}(z) = G_{2k}(ℤz + ℤ)`. -/
theorem eisensteinG_eq_G (k : ℕ) (τ : ℍ) : eisensteinG k τ = (periodPairOf τ).G k := by
  unfold eisensteinG PeriodPair.G
  rw [← (periodPairOf τ).latticeEquivProd.symm.toEquiv.tsum_eq]
  refine tsum_congr fun v => ?_
  have := (periodPairOf τ).latticeEquiv_symm_apply v
  simp only [LinearEquiv.coe_toEquiv, this]
  simp [periodPairOf]

/-- Comparison with Mathlib's normalised Eisenstein series: `G_k(τ) = 2 ζ(k) E_k(τ)`. -/
theorem eisensteinG_eq_E {k : ℕ} (hk : 3 ≤ k) (τ : ℍ) :
    eisensteinG k τ = 2 * riemannZeta k * E hk τ := by
  have h1 : eisensteinG k τ = ∑' v : Fin 2 → ℤ, eisSummand k v τ := by
    unfold eisensteinG
    rw [← (finTwoArrowEquiv ℤ).symm.tsum_eq]
    refine tsum_congr fun v => ?_
    simp [eisSummand, zpow_neg]
  have h2 : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl
  rw [h1, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk, h2]
  ring

/-- Proposition 2.5 (Milne, pdf p. 94): for every integer `k ≥ 2`, `G_{2k}(z)` converges to a
holomorphic function on `ℍ`. -/
@[kb "milne2006ec" "Ch. III, Prop. 2.5, pdf p. 94"]
theorem prop_2_5 (k : ℕ) (hk : 2 ≤ k) :
    (∀ z : ℂ, 0 < z.im → Summable fun v : ℤ × ℤ => ((v.1 * z + v.2) ^ (2 * k))⁻¹) ∧
      DifferentiableOn ℂ (eisensteinG (2 * k)) {z | 0 < z.im} := by
  have hk3 : 3 ≤ 2 * k := by omega
  refine ⟨fun z hz => ?_, ?_⟩
  · have := summable_prod_eisSummand hk3 ⟨z, hz⟩
    refine this.congr fun v => ?_
    simp only [eisSummand, zpow_neg, zpow_natCast, Matrix.cons_val_zero, Matrix.cons_val_one]
  · have hd := (UpperHalfPlane.mdifferentiable_iff.mp (E hk3).holo').const_mul
      (2 * riemannZeta (2 * k : ℕ))
    refine hd.congr fun z hz => ?_
    have hz' : 0 < z.im := hz
    have := eisensteinG_eq_E hk3 ⟨z, hz'⟩
    simp only [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    exact this

/-! ### Lemma 3.6 and the curve `E(Λ)` -/

/-- The discriminant of `E(Λ)` is `g₄³ - 27g₆²`. -/
theorem curveOf_Δ (L : PeriodPair) : (curveOf L).Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curveOf]
  ring

/-- `ζ(6) = π⁶/945`. -/
theorem riemannZeta_six : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have hb : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, Nat.choose, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four, h5]
  have := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  norm_num [Nat.factorial, bernoulli_eq_bernoulli'_of_ne_one, hb] at this
  rw [this]
  ring

/-- For `τ ∈ ℍ`, `g₂³ - 27 g₃² ≠ 0` for the lattice `ℤτ + ℤ`. -/
lemma g₂_cube_sub_g₃_sq_ne_zero_of_upper (τ : ℍ) :
    (60 * (periodPairOf τ).G 4) ^ 3 - 27 * (140 * (periodPairOf τ).G 6) ^ 2 ≠ 0 := by
  rw [← eisensteinG_eq_G, ← eisensteinG_eq_G]
  have h4 := eisensteinG_eq_E (k := 4) (by norm_num) τ
  have h6 := eisensteinG_eq_E (k := 6) (by norm_num) τ
  have hd := discriminant_eq_E₄_cube_sub_E₆_sq τ
  have hne := discriminant_ne_zero τ
  have hz4 : riemannZeta ((4 : ℕ) : ℂ) = π ^ 4 / 90 := by
    rw [Nat.cast_ofNat]; exact riemannZeta_four
  have hz6 : riemannZeta ((6 : ℕ) : ℂ) = π ^ 6 / 945 := by
    rw [Nat.cast_ofNat]; exact riemannZeta_six
  rw [hz4] at h4
  rw [hz6] at h6
  rw [h4, h6]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have : (60 * (2 * (π ^ 4 / 90 : ℂ) * E₄ τ)) ^ 3 - 27 * (140 * (2 * (π ^ 6 / 945 : ℂ) * E₆ τ)) ^ 2
      = (64 / 27) * π ^ 12 * (E₄ τ ^ 3 - E₆ τ ^ 2) := by ring
  rw [this]
  have h1728 : E₄ τ ^ 3 - E₆ τ ^ 2 = 1728 * discriminant τ := by rw [hd]; ring
  rw [h1728]
  have : (π : ℂ) ^ 12 ≠ 0 := pow_ne_zero _ hπ
  simp [this, hne]

/-- `g₄(Λ)³ - 27 g₆(Λ)² ≠ 0` for every lattice.  Proof: by homogeneity reduce to `ℤτ + ℤ`; there
`g₄ = (4π⁴/3) E₄`, `g₆ = (8π⁶/27) E₆`, so `g₄³ - 27g₆² = (64π¹²/27)(E₄³ - E₆²) = 64π¹² · 64 Δ`
with Mathlib's `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`, `discriminant_ne_zero`. -/
theorem g₂_cube_sub_g₃_sq_ne_zero (L : PeriodPair) : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := by
  -- reduction to `ℤτ + ℤ` for `τ ∈ ℍ`
  have key : ∀ (c : ℂ) (τ : ℍ), c ≠ 0 →
      L.lattice = Submodule.span ℤ {c * (periodPairOf τ).ω₁, c * (periodPairOf τ).ω₂} →
      L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := by
    intro c τ hc h
    have h4 := G_of_lattice_eq_smul (L := periodPairOf τ) (L' := L) hc h 4
    have h6 := G_of_lattice_eq_smul (L := periodPairOf τ) (L' := L) hc h 6
    have hne := g₂_cube_sub_g₃_sq_ne_zero_of_upper τ
    have : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 =
        ((c ^ 12)⁻¹) * ((60 * (periodPairOf τ).G 4) ^ 3 - 27 * (140 * (periodPairOf τ).G 6) ^ 2) := by
      unfold PeriodPair.g₂ PeriodPair.g₃
      rw [h4, h6]
      field_simp
    rw [this]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hc)) hne
  have hind := L.indep
  rw [LinearIndependent.pair_iff] at hind
  have hω₂ : L.ω₂ ≠ 0 := by
    intro h
    have := hind 0 1 (by simp [h])
    simp at this
  have hω₁ : L.ω₁ ≠ 0 := by
    intro h
    have := hind 1 0 (by simp [h])
    simp at this
  have him : (L.ω₁ / L.ω₂).im ≠ 0 := by
    intro h
    have hr : L.ω₁ / L.ω₂ = ((L.ω₁ / L.ω₂).re : ℂ) := Complex.ext (by simp) (by simpa using h)
    have h1 : L.ω₁ = ((L.ω₁ / L.ω₂).re : ℂ) * L.ω₂ := by
      rw [← hr]; exact (div_eq_iff hω₂).1 rfl
    have := hind 1 (-(L.ω₁ / L.ω₂).re) (by
      simp only [Complex.real_smul, Complex.ofReal_one, one_mul, Complex.ofReal_neg]
      linear_combination h1)
    simp at this
  rcases lt_or_gt_of_ne him with hlt | hgt
  · -- ω₂/ω₁ ∈ ℍ
    have hpos : 0 < (L.ω₂ / L.ω₁).im := by
      have : L.ω₂ / L.ω₁ = (L.ω₁ / L.ω₂)⁻¹ := by rw [inv_div]
      rw [this, Complex.inv_im]
      have : 0 < Complex.normSq (L.ω₁ / L.ω₂) := Complex.normSq_pos.2 (div_ne_zero hω₁ hω₂)
      rw [neg_div]; exact neg_pos.2 (div_neg_of_neg_of_pos hlt this)
    refine key L.ω₁ ⟨L.ω₂ / L.ω₁, hpos⟩ hω₁ ?_
    simp only [periodPairOf, PeriodPair.lattice]
    rw [Set.pair_comm]
    congr 2 <;> simp [mul_div_cancel₀ _ hω₁]
  · refine key L.ω₂ ⟨L.ω₁ / L.ω₂, hgt⟩ hω₂ ?_
    simp only [periodPairOf, PeriodPair.lattice]
    have e1 : L.ω₂ * ((⟨L.ω₁ / L.ω₂, hgt⟩ : ℍ) : ℂ) = L.ω₁ := by
      show L.ω₂ * (L.ω₁ / L.ω₂) = L.ω₁
      field_simp
    rw [e1, mul_one]

/-- Lemma 3.6 (Milne, pdf p. 99): the polynomial `4X³ - g₄(Λ)X - g₆(Λ)` has distinct roots
(equivalently, over `ℂ`, it is separable). -/
@[kb "milne2006ec" "Ch. III, Lemma 3.6, pdf p. 99"]
theorem lemma_3_6 (L : PeriodPair) :
    (4 * Polynomial.X ^ 3 - Polynomial.C L.g₂ * Polynomial.X - Polynomial.C L.g₃ :
      Polynomial ℂ).Separable := by
  have hΔ := g₂_cube_sub_g₃_sq_ne_zero L
  set a := L.g₂
  set b := L.g₃
  unfold Polynomial.Separable
  have hd : Polynomial.derivative (4 * Polynomial.X ^ 3 - Polynomial.C a * Polynomial.X
      - Polynomial.C b : Polynomial ℂ) = 12 * Polynomial.X ^ 2 - Polynomial.C a := by
    simp [Polynomial.derivative_sub, Polynomial.derivative_mul]
    rw [show (Polynomial.C (2 : ℂ)) = 2 from map_ofNat _ 2]
    ring
  rw [hd]
  refine ⟨Polynomial.C (a ^ 3 - 27 * b ^ 2)⁻¹ * (-9 * (2 * Polynomial.C a * Polynomial.X
      - 3 * Polynomial.C b)),
    Polynomial.C (a ^ 3 - 27 * b ^ 2)⁻¹ * (-Polynomial.C a ^ 2 + 3 * (2 * Polynomial.C a *
      Polynomial.X - 3 * Polynomial.C b) * Polynomial.X), ?_⟩
  have hC : Polynomial.C (a ^ 3 - 27 * b ^ 2)⁻¹ * Polynomial.C (a ^ 3 - 27 * b ^ 2) = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hΔ, Polynomial.C_1]
  have hC' : Polynomial.C (a ^ 3 - 27 * b ^ 2) = Polynomial.C a ^ 3 - 27 * Polynomial.C b ^ 2 := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]
  rw [hC'] at hC
  linear_combination hC

/-- By Lemma 3.6, `E(Λ)` is an elliptic curve (Milne, pdf p. 100). -/
instance (L : PeriodPair) : (curveOf L).IsElliptic :=
  ⟨isUnit_iff_ne_zero.2 (by rw [curveOf_Δ]; exact g₂_cube_sub_g₃_sq_ne_zero L)⟩

/-- The point `z ↦ (℘(z) : ℘'(z) : 1)` (`z ∉ Λ`), `z ↦ (0 : 1 : 0)` (`z ∈ Λ`) of Milne's
Proposition 3.7 (pdf p. 100), as a point of Mathlib's `E(Λ)` (coordinates `(℘(z), ℘'(z)/2)`,
see `curveOf`). -/
noncomputable def toCurve (L : PeriodPair) (z : ℂ) : (curveOf L).toAffine.Point := by
  classical
  exact if hz : z ∈ L.lattice then 0 else
    .some (x := L.weierstrassP z) (y := L.derivWeierstrassP z / 2) (by
      have hsq := L.derivWeierstrassP_sq z hz
      refine (WeierstrassCurve.Affine.equation_iff_nonsingular).mp ?_
      rw [WeierstrassCurve.Affine.equation_iff]
      simp only [curveOf]
      linear_combination (1 / 4 : ℂ) * hsq)

/-! ### Remark 3.11 (first part) -/

/-- Remark 3.11 (Milne, pdf p. 102), first part: under `z ↦ (℘(z), ℘'(z))`, `dx/y = ℘'(z)dz/℘'(z)
= dz`; i.e. `(d℘/dz)/℘' = 1` wherever `℘'(z) ≠ 0`. -/
@[kb "milne2006ec" "Ch. III, Rem. 3.11, dx/y = dz, pdf p. 102"]
theorem remark_3_11_dx_div_y (L : PeriodPair) (z : ℂ) (hz : L.derivWeierstrassP z ≠ 0) :
    deriv L.weierstrassP z / L.derivWeierstrassP z = 1 := by
  rw [PeriodPair.deriv_weierstrassP, div_self hz]

end NumberFieldKB.MilneEC.III
