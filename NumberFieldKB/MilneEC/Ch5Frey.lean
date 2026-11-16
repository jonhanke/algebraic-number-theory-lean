import NumberFieldKB.MilneEC.Ch5LSeries
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat

/-!
# Milne, *Elliptic Curves*, Chapter V, Exercise 4.21: the Frey curve

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, Exercise 4.21, pdf pp. 215–216.

For nonzero pairwise coprime integers $\alpha$, $\beta$, $\gamma$ with $\alpha^\ell + \beta^\ell = \gamma^\ell$,
$\ell \ge 5$ prime, the curve $E : Y^2Z = X(X - \alpha^\ell Z)(X - \gamma^\ell Z)$, i.e. the Weierstrass equation
$y^2 = x^3 - (\alpha^\ell + \gamma^\ell)x^2 + \alpha^\ell\gamma^\ell x$. (The second root is unreadable in our
copy of the text; $\gamma^\ell$ is the reading consistent with (a) and with the hint, which takes $\gamma$ even.)

Reduction types are Mathlib's (`WeierstrassCurve.HasGoodReduction`, `HasMultiplicativeReduction` for a minimal
model over $\mathbb Z_p$); "at worst nodal" is "good or multiplicative". For (d) Milne first reorders
$\alpha, \beta, \gamma$ (so that $\gamma$ is even and $\alpha^\ell \equiv -1 \bmod 4$); reordering changes the curve,
so (d) is stated under these normalisations.
-/

open Complex

namespace NumberFieldKB.MilneEC.V

section MinimalGeneral
open WeierstrassCurve IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Comparison of an integral model with the minimal model. -/
lemma minimal_compare (W₀ : WeierstrassCurve K) (C₀ : VariableChange K)
    (hint : IsIntegral R (C₀ • W₀)) :
    ∃ D : VariableChange K, D • (W₀.minimal R) = C₀ • W₀ ∧
      valuation K (maximalIdeal R) (C₀ • W₀).Δ ≤ valuation K (maximalIdeal R) (W₀.minimal R).Δ := by
  obtain ⟨C, hC⟩ : ∃ C : VariableChange K, W₀.minimal R = C • W₀ := ⟨_, rfl⟩
  have hD : (C₀ * C⁻¹) • (W₀.minimal R) = C₀ • W₀ := by rw [hC, ← mul_smul]; simp
  refine ⟨C₀ * C⁻¹, hD, ?_⟩
  have hmin := (IsMinimal.val_Δ_maximal (R := R) (W := W₀.minimal R))
  have hj : IsIntegral R ((C₀ * C⁻¹) • (W₀.minimal R)) := by rw [hD]; exact hint
  have h1 : IsIntegral R (W₀.minimal R) := by simpa using hmin.1
  have key : valuation_Δ_aux R ((C₀ * C⁻¹) • W₀.minimal R) ≤
      valuation_Δ_aux R ((1 : VariableChange K) • W₀.minimal R) := by
    rcases le_total (valuation_Δ_aux R ((1 : VariableChange K) • W₀.minimal R))
      (valuation_Δ_aux R ((C₀ * C⁻¹) • W₀.minimal R)) with h | h
    · exact hmin.2 hj h
    · exact h
  rw [hD, one_smul] at key
  have e1 := valuation_Δ_aux_eq_of_isIntegral R (C₀ • W₀)
  have e2 := valuation_Δ_aux_eq_of_isIntegral R (W₀.minimal R)
  rw [← e1, ← e2]
  exact key

/-- An integral model has discriminant of valuation at most $1$. -/
lemma val_le_one_of_isIntegral_Δ (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.Δ ≤ 1 := by
  obtain ⟨r, hr⟩ := Δ_integral_of_isIntegral R W
  rw [← hr]; exact valuation_le_one (maximalIdeal R) r

/-- An integral model has $c_4$ of valuation at most $1$. -/
lemma val_le_one_of_isIntegral_c₄ (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.c₄ ≤ 1 := by
  rw [← integralModel_c₄_eq R W]; exact valuation_le_one (maximalIdeal R) _

/-- If some integral model of `W₀` has unit discriminant, the minimal model has good reduction. -/
lemma hasGoodReduction_minimal_of_integral (W₀ : WeierstrassCurve K) (C₀ : VariableChange K)
    (hint : IsIntegral R (C₀ • W₀)) (hΔ : valuation K (maximalIdeal R) (C₀ • W₀).Δ = 1) :
    (W₀.minimal R).HasGoodReduction R := by
  obtain ⟨D, -, hle⟩ := minimal_compare (R := R) W₀ C₀ hint
  have h1 := val_le_one_of_isIntegral_Δ (R := R) (W₀.minimal R)
  exact HasGoodReduction.mk (le_antisymm h1 (hΔ ▸ hle))

/-- If some integral model of `W₀` has `0 ≠ Δ` of valuation `< 1` and unit `c₄`, the minimal model has
multiplicative reduction. -/
lemma hasMultiplicativeReduction_minimal_of_integral (W₀ : WeierstrassCurve K) (C₀ : VariableChange K)
    (hint : IsIntegral R (C₀ • W₀)) (hΔ0 : (C₀ • W₀).Δ ≠ 0)
    (hΔ : valuation K (maximalIdeal R) (C₀ • W₀).Δ < 1)
    (hc : valuation K (maximalIdeal R) (C₀ • W₀).c₄ = 1) :
    (W₀.minimal R).HasMultiplicativeReduction R := by
  obtain ⟨D, hD, hle⟩ := minimal_compare (R := R) W₀ C₀ hint
  rw [← hD] at hΔ0 hΔ hc hle
  rw [variableChange_Δ] at hΔ0 hΔ hle
  rw [variableChange_c₄] at hc
  set v := valuation K (maximalIdeal R)
  set a := v ((D.u⁻¹ : Kˣ) : K) with ha
  have h4 := val_le_one_of_isIntegral_c₄ (R := R) (W₀.minimal R)
  have hΔ' : (W₀.minimal R).Δ ≠ 0 := fun h => hΔ0 (by simp [h])
  have hvΔ' : v (W₀.minimal R).Δ ≠ 0 := by simpa using hΔ'
  simp only [map_mul, map_pow] at hΔ hle hc
  have ha4 : 1 ≤ a ^ 4 := by
    by_contra hlt
    rw [not_le] at hlt
    have : a ^ 4 * v (W₀.minimal R).c₄ < 1 :=
      lt_of_le_of_lt (mul_le_mul' le_rfl h4) (by simpa using hlt)
    exact this.ne hc
  have ha12 : a ^ 12 ≤ 1 := by
    have : a ^ 12 * v (W₀.minimal R).Δ ≤ 1 * v (W₀.minimal R).Δ := by rwa [one_mul]
    exact (mul_le_mul_iff_left₀ (zero_lt_iff.mpr hvΔ')).mp this
  have ha4' : a ^ 4 = 1 := by
    by_contra hne
    have : 1 < a ^ 4 := lt_of_le_of_ne ha4 (Ne.symm hne)
    have := one_lt_pow₀ this (n := 3) (by norm_num)
    rw [← pow_mul] at this
    exact absurd ha12 (not_le.mpr this)
  have ha12' : a ^ 12 = 1 := by
    have : a ^ 12 = (a ^ 4) ^ 3 := by rw [← pow_mul]
    rw [this, ha4']; simp
  refine HasMultiplicativeReduction.mk ?_ ?_
  · rw [ha12', one_mul] at hΔ; exact hΔ
  · rw [ha4', one_mul] at hc; exact hc
end MinimalGeneral

section FreyLocal
open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
variable (p : ℕ) [Fact p.Prime]

/-- An integer $n$ has $p$-adic valuation $< 1$ if and only if $p \mid n$. -/
lemma val_intCast_lt_one_iff (n : ℤ) :
    valuation ℚ_[p] (maximalIdeal ℤ_[p]) (n : ℚ_[p]) < 1 ↔ (p : ℤ) ∣ n := by
  have : (n : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (n : ℤ_[p]) := by simp
  rw [this, valuation_lt_one_iff_mem]
  show (n : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PadicInt.isUnit_iff, ← PadicInt.norm_int_lt_one_iff_dvd]
  have := PadicInt.norm_le_one (n : ℤ_[p])
  constructor
  · intro h; exact lt_of_le_of_ne this h
  · intro h; exact h.ne

/-- An integer $n$ has $p$-adic valuation $1$ if and only if $p \nmid n$. -/
lemma val_intCast_eq_one_iff (n : ℤ) :
    valuation ℚ_[p] (maximalIdeal ℤ_[p]) (n : ℚ_[p]) = 1 ↔ ¬ (p : ℤ) ∣ n := by
  rw [← val_intCast_lt_one_iff]
  have : (n : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (n : ℤ_[p]) := by simp
  have h2 : valuation ℚ_[p] (maximalIdeal ℤ_[p]) (n : ℚ_[p]) ≤ 1 := by
    rw [this]; exact valuation_le_one (K := ℚ_[p]) (maximalIdeal ℤ_[p]) (n : ℤ_[p])
  rw [not_lt]; exact h2.ge_iff_eq.symm

end FreyLocal

/-- The Frey curve $y^2 = x(x - \alpha^\ell)(x - \gamma^\ell)$ over $\mathbb Q$. -/
@[kb "milne2006ec" "Ch. V, Exercise 4.21 (the Frey curve), pdf p. 215"]
def freyCurve (α γ : ℤ) (ℓ : ℕ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -((α : ℚ) ^ ℓ + (γ : ℚ) ^ ℓ)
  a₃ := 0
  a₄ := (α : ℚ) ^ ℓ * (γ : ℚ) ^ ℓ
  a₆ := 0

/-- The hypotheses of Exercise 4.21: $\alpha, \beta, \gamma$ nonzero, pairwise coprime, $\alpha^\ell + \beta^\ell =
\gamma^\ell$, $\ell$ a prime $\ne 2, 3$. -/
structure FreyHyp (α β γ : ℤ) (ℓ : ℕ) : Prop where
  prime : ℓ.Prime
  five_le : 5 ≤ ℓ
  α_ne : α ≠ 0
  β_ne : β ≠ 0
  γ_ne : γ ≠ 0
  coprime_αβ : IsCoprime α β
  coprime_αγ : IsCoprime α γ
  coprime_βγ : IsCoprime β γ
  fermat : α ^ ℓ + β ^ ℓ = γ ^ ℓ

/-- **Exercise 4.21** (a) (pdf p. 215): $\Delta = 16\alpha^{2\ell}\beta^{2\ell}\gamma^{2\ell}$. -/
@[kb "milne2006ec" "Ch. V, Exercise 4.21 (a), pdf p. 215"]
theorem exercise_4_21_a {α β γ : ℤ} {ℓ : ℕ} (h : FreyHyp α β γ ℓ) :
    (freyCurve α γ ℓ).Δ = 16 * ((α : ℚ) ^ (2 * ℓ) * (β : ℚ) ^ (2 * ℓ) * (γ : ℚ) ^ (2 * ℓ)) := by
  have hB : (β : ℚ) ^ ℓ = (γ : ℚ) ^ ℓ - (α : ℚ) ^ ℓ := by
    have := congrArg (Int.cast : ℤ → ℚ) h.fermat
    push_cast at this
    linarith
  rw [pow_mul' (α : ℚ), pow_mul' (β : ℚ), pow_mul' (γ : ℚ), hB]
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, freyCurve]
  ring

/-- The Frey curve is an elliptic curve ($\Delta \ne 0$). -/
theorem freyCurve_isElliptic {α β γ : ℤ} {ℓ : ℕ} (h : FreyHyp α β γ ℓ) : (freyCurve α γ ℓ).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, exercise_4_21_a h]
  have := h.α_ne
  have := h.β_ne
  have := h.γ_ne
  exact (by positivity : (16 : ℚ) * ((α : ℚ) ^ (2 * ℓ) * (β : ℚ) ^ (2 * ℓ) * (γ : ℚ) ^ (2 * ℓ)) ≠ 0).isUnit

section FreyReduction

/-- The Frey curve is an integral Weierstrass model over $\mathbb Z_p$. -/
lemma frey_baseChange_isIntegral (α γ : ℤ) (ℓ : ℕ) (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve.IsIntegral ℤ_[p] ((freyCurve α γ ℓ).baseChange ℚ_[p]) := by
  refine WeierstrassCurve.isIntegral_of_exists_lift _ ⟨0, by simp [freyCurve, WeierstrassCurve.baseChange]⟩
    ⟨-((α : ℤ_[p]) ^ ℓ + (γ : ℤ_[p]) ^ ℓ), by simp [freyCurve, WeierstrassCurve.baseChange]⟩
    ⟨0, by simp [freyCurve, WeierstrassCurve.baseChange]⟩
    ⟨(α : ℤ_[p]) ^ ℓ * (γ : ℤ_[p]) ^ ℓ, by simp [freyCurve, WeierstrassCurve.baseChange]⟩
    ⟨0, by simp [freyCurve, WeierstrassCurve.baseChange]⟩

/-- Over $\mathbb Q_p$ the Frey curve has discriminant $16(\alpha\beta\gamma)^{2\ell}$. -/
lemma frey_baseChange_Δ {α β γ : ℤ} {ℓ : ℕ} (h : FreyHyp α β γ ℓ) (p : ℕ) [Fact p.Prime] :
    ((freyCurve α γ ℓ).baseChange ℚ_[p]).Δ = ((16 * (α * β * γ) ^ (2 * ℓ) : ℤ) : ℚ_[p]) := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, exercise_4_21_a h]
  simp [mul_pow]

/-- Over $\mathbb Q_p$ the Frey curve has $c_4 = 16(\alpha^{2\ell} - \alpha^\ell\gamma^\ell + \gamma^{2\ell})$. -/
lemma frey_baseChange_c₄ (α γ : ℤ) (ℓ : ℕ) (p : ℕ) [Fact p.Prime] :
    ((freyCurve α γ ℓ).baseChange ℚ_[p]).c₄ =
      ((16 * ((α ^ ℓ) ^ 2 - α ^ ℓ * γ ^ ℓ + (γ ^ ℓ) ^ 2) : ℤ) : ℚ_[p]) := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄]
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, freyCurve]
  simp
  ring

/-- Under the Frey hypotheses the product $\alpha\beta\gamma$ is even. -/
lemma frey_even_prod {α β γ : ℤ} {ℓ : ℕ} (h : FreyHyp α β γ ℓ) : (2 : ℤ) ∣ α * β * γ := by
  by_contra hn
  simp only [← even_iff_two_dvd, Int.even_mul, not_or] at hn
  obtain ⟨⟨hα, hβ⟩, hγ⟩ := hn
  rw [Int.not_even_iff_odd] at hα hβ hγ
  have h1 : Even (α ^ ℓ + β ^ ℓ) := (hα.pow).add_odd (hβ.pow)
  rw [h.fermat] at h1
  exact (Int.not_even_iff_odd.mpr hγ.pow) h1

/-- An odd prime $p \ne 2$ does not divide $16$. -/
lemma not_dvd_sixteen {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : ¬ (p : ℤ) ∣ 16 := by
  intro hd
  have h1 : p ∣ 2 ^ 4 := by
    have : (p : ℤ) ∣ ((2 ^ 4 : ℕ) : ℤ) := by exact_mod_cast hd
    exact Int.natCast_dvd_natCast.mp this
  have h2 := (Fact.out : p.Prime).dvd_of_dvd_pow h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h2)

/-- A prime dividing $\alpha\beta\gamma$ does not divide $\alpha^{2\ell} - \alpha^\ell\gamma^\ell + \gamma^{2\ell}$. -/
lemma frey_c4_not_dvd {α β γ : ℤ} {ℓ : ℕ} (h : FreyHyp α β γ ℓ) {q : ℤ} (hq : Prime q)
    (hdiv : q ∣ α * β * γ) : ¬ q ∣ (α ^ ℓ) ^ 2 - α ^ ℓ * γ ^ ℓ + (γ ^ ℓ) ^ 2 := by
  have hl : ℓ ≠ 0 := h.prime.ne_zero
  have cop : ∀ {x y : ℤ}, IsCoprime x y → q ∣ x → q ∣ y → False :=
    fun hc hx hy => hq.not_isUnit (hc.isUnit_of_dvd' hx hy)
  have hpow : ∀ x : ℤ, q ∣ x ^ ℓ → q ∣ x := fun x hx => hq.dvd_of_dvd_pow hx
  have hB : β ^ ℓ = γ ^ ℓ - α ^ ℓ := by linarith [h.fermat]
  intro hn
  rcases hq.dvd_or_dvd hdiv with h1 | hγ
  · rcases hq.dvd_or_dvd h1 with hα | hβ
    · have hA : q ∣ α ^ ℓ := dvd_pow hα hl
      have e : (γ ^ ℓ) ^ 2 = ((α ^ ℓ) ^ 2 - α ^ ℓ * γ ^ ℓ + (γ ^ ℓ) ^ 2) - α ^ ℓ * (α ^ ℓ - γ ^ ℓ) := by
        ring
      have : q ∣ (γ ^ ℓ) ^ 2 := by rw [e]; exact dvd_sub hn (dvd_mul_of_dvd_left hA _)
      exact cop h.coprime_αγ hα (hpow _ (hq.dvd_of_dvd_pow this))
    · have hBq : q ∣ β ^ ℓ := dvd_pow hβ hl
      rw [hB] at hBq
      have e : α ^ ℓ * γ ^ ℓ = ((α ^ ℓ) ^ 2 - α ^ ℓ * γ ^ ℓ + (γ ^ ℓ) ^ 2) - (γ ^ ℓ - α ^ ℓ) ^ 2 := by
        ring
      have : q ∣ α ^ ℓ * γ ^ ℓ := by rw [e]; exact dvd_sub hn (dvd_pow hBq two_ne_zero)
      rcases hq.dvd_or_dvd this with hA | hC
      · exact cop h.coprime_αβ (hpow _ hA) hβ
      · exact cop h.coprime_βγ hβ (hpow _ hC)
  · have hC : q ∣ γ ^ ℓ := dvd_pow hγ hl
    have e : (α ^ ℓ) ^ 2 = ((α ^ ℓ) ^ 2 - α ^ ℓ * γ ^ ℓ + (γ ^ ℓ) ^ 2) - γ ^ ℓ * (γ ^ ℓ - α ^ ℓ) := by
      ring
    have : q ∣ (α ^ ℓ) ^ 2 := by rw [e]; exact dvd_sub hn (dvd_mul_of_dvd_left hC _)
    exact cop h.coprime_αγ (hpow _ (hq.dvd_of_dvd_pow this)) hγ

/-- If $A \equiv 3 \pmod 4$ and $C = 32c'$ then $4 \mid A + C + 1$ and $A^2 - AC + C^2$ is odd. -/
lemma frey_two_arith (A C c' : ℤ) (hA : A % 4 = 3) (hC : C = 32 * c') :
    ∃ k : ℤ, A + C + 1 = 4 * k ∧ Odd (A ^ 2 - A * C + C ^ 2) := by
  obtain ⟨m, hm⟩ : ∃ m, A = 4 * m + 3 := ⟨A / 4, by omega⟩
  refine ⟨m + 1 + 8 * c', by omega, 8 * m ^ 2 + 12 * m + 4 - 64 * m * c' - 48 * c' + 512 * c' ^ 2, ?_⟩
  subst hm hC
  ring

end FreyReduction

/-- **Exercise 4.21** (b) (pdf p. 215): if $p \nmid \alpha\beta\gamma$, $E$ has good reduction at $p$. -/
@[kb "milne2006ec" "Ch. V, Exercise 4.21 (b), pdf p. 215"]
theorem exercise_4_21_b {α β γ : ℤ} {ℓ : ℕ} (h : FreyHyp α β γ ℓ) (p : ℕ) [Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ α * β * γ) : HasGoodReductionAt (freyCurve α γ ℓ) p := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hp (by simpa using frey_even_prod h)
  have hq : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have := frey_baseChange_isIntegral α γ ℓ p
  unfold HasGoodReductionAt
  refine hasGoodReduction_minimal_of_integral (R := ℤ_[p]) _ 1 (by simpa using this) ?_
  rw [one_smul, frey_baseChange_Δ h, val_intCast_eq_one_iff]
  intro hd
  rcases hq.dvd_or_dvd hd with h16 | h2
  · exact not_dvd_sixteen hp2 h16
  · exact hp (hq.dvd_of_dvd_pow h2)

/-- **Exercise 4.21** (c) (pdf p. 215): if $p$ is an odd prime dividing $\alpha\beta\gamma$, $E$ has (at worst
nodal, here exactly) multiplicative reduction at $p$. -/
@[kb "milne2006ec" "Ch. V, Exercise 4.21 (c), pdf p. 215"]
theorem exercise_4_21_c {α β γ : ℤ} {ℓ : ℕ} (h : FreyHyp α β γ ℓ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : (p : ℤ) ∣ α * β * γ) :
    ((freyCurve α γ ℓ |>.baseChange ℚ_[p]).minimal ℤ_[p]).HasMultiplicativeReduction ℤ_[p] := by
  have hq : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have := frey_baseChange_isIntegral α γ ℓ p
  refine hasMultiplicativeReduction_minimal_of_integral (R := ℤ_[p]) _ 1 (by simpa using this) ?_ ?_ ?_
  · rw [one_smul, frey_baseChange_Δ h]
    have := h.α_ne
    have := h.β_ne
    have := h.γ_ne
    exact_mod_cast (by positivity : (16 : ℤ) * (α * β * γ) ^ (2 * ℓ) ≠ 0)
  · rw [one_smul, frey_baseChange_Δ h, val_intCast_lt_one_iff]
    exact dvd_mul_of_dvd_right (dvd_pow hp (by have := h.prime.pos; omega)) _
  · rw [one_smul, frey_baseChange_c₄, val_intCast_eq_one_iff]
    intro hd
    rcases hq.dvd_or_dvd hd with h16 | h2
    · exact not_dvd_sixteen hp2 h16
    · exact frey_c4_not_dvd h hq hp h2

/-- **Exercise 4.21** (d) (pdf p. 215), with the normalisation of the hint ($\gamma$ even,
$\alpha^\ell \equiv -1 \bmod 4$): the minimal model of $E$ at $2$ has multiplicative (nodal) reduction. The hint's
change of variables $x = 4X$, $y = 8Y + 4X$ gives an integral model with odd $c_4$. -/
@[kb "milne2006ec" "Ch. V, Exercise 4.21 (d), pdf p. 215"]
theorem exercise_4_21_d {α β γ : ℤ} {ℓ : ℕ} (h : FreyHyp α β γ ℓ) (hγ : Even γ) (hα : α ^ ℓ % 4 = 3) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    ((freyCurve α γ ℓ |>.baseChange ℚ_[2]).minimal ℤ_[2]).HasMultiplicativeReduction ℤ_[2] := by
  obtain ⟨g, hg'⟩ := hγ
  have hg : γ = 2 * g := by omega
  obtain ⟨c', hc'⟩ : ∃ c' : ℤ, γ ^ ℓ = 32 * c' := by
    have h1 : (32 : ℤ) ∣ 2 ^ ℓ := by
      have := pow_dvd_pow (2 : ℤ) h.five_le
      simpa using this
    refine (h1.trans ?_)
    rw [hg, mul_pow]
    exact dvd_mul_right _ _
  obtain ⟨k, hk, hodd⟩ := frey_two_arith (α ^ ℓ) (γ ^ ℓ) c' hα hc'
  have hB : β ^ ℓ = γ ^ ℓ - α ^ ℓ := by linarith [h.fermat]
  have hc0 : c' ≠ 0 := by
    rintro rfl
    have := h.γ_ne
    simp at hc'
    exact this hc'.1
  have hA0 : α ^ ℓ ≠ 0 := pow_ne_zero _ h.α_ne
  have hB0 : β ^ ℓ ≠ 0 := pow_ne_zero _ h.β_ne
  have hZ : (16 * (α * β * γ) ^ (2 * ℓ) : ℤ) = 4096 * (4 * (α ^ ℓ * c' * β ^ ℓ) ^ 2) := by
    have : (α * β * γ) ^ (2 * ℓ) = (α ^ ℓ * β ^ ℓ * γ ^ ℓ) ^ 2 := by
      rw [pow_mul']
      ring
    rw [this, hc']
    ring
  have := frey_baseChange_isIntegral α γ ℓ 2
  let C₀ : WeierstrassCurve.VariableChange ℚ_[2] := ⟨Units.mk0 2 two_ne_zero, 0, 1, 0⟩
  have hk' : ((α : ℚ_[2]) ^ ℓ + (γ : ℚ_[2]) ^ ℓ + 1) = 4 * k := by exact_mod_cast hk
  have hc'' : ((γ : ℚ_[2]) ^ ℓ) = 32 * c' := by exact_mod_cast hc'
  have hint : WeierstrassCurve.IsIntegral ℤ_[2] (C₀ • (freyCurve α γ ℓ |>.baseChange ℚ_[2])) := by
    refine WeierstrassCurve.isIntegral_of_exists_lift _ ⟨1, ?_⟩ ⟨-k, ?_⟩ ⟨0, ?_⟩
      ⟨((2 * α ^ ℓ * c' : ℤ) : ℤ_[2]), ?_⟩ ⟨0, ?_⟩
    all_goals
      simp [WeierstrassCurve.variableChange_def, C₀, freyCurve, WeierstrassCurve.baseChange]
    case refine_2 => linear_combination (1 / 4 : ℚ_[2]) * hk'
    case refine_4 =>
      have h2 : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := by exact_mod_cast PadicInt.coe_natCast (p := 2) 2
      linear_combination (-(α : ℚ_[2]) ^ ℓ / 16) * hc'' + ((α : ℚ_[2]) ^ ℓ * c') * h2
  have hΔ : (C₀ • (freyCurve α γ ℓ |>.baseChange ℚ_[2])).Δ =
      ((4 * (α ^ ℓ * c' * β ^ ℓ) ^ 2 : ℤ) : ℚ_[2]) := by
    rw [WeierstrassCurve.variableChange_Δ, frey_baseChange_Δ h, hZ]
    simp only [C₀, Units.val_inv_eq_inv_val, Units.val_mk0]
    push_cast
    ring
  have hc4 : (C₀ • (freyCurve α γ ℓ |>.baseChange ℚ_[2])).c₄ =
      (((α ^ ℓ) ^ 2 - α ^ ℓ * γ ^ ℓ + (γ ^ ℓ) ^ 2 : ℤ) : ℚ_[2]) := by
    rw [WeierstrassCurve.variableChange_c₄, frey_baseChange_c₄]
    simp only [C₀, Units.val_inv_eq_inv_val, Units.val_mk0]
    push_cast
    ring
  refine hasMultiplicativeReduction_minimal_of_integral (R := ℤ_[2]) _ C₀ hint ?_ ?_ ?_
  · rw [hΔ]
    have : (4 * (α ^ ℓ * c' * β ^ ℓ) ^ 2 : ℤ) ≠ 0 := by positivity
    exact_mod_cast this
  · rw [hΔ, val_intCast_lt_one_iff]
    exact Dvd.dvd.mul_right (by norm_num) _
  · rw [hc4, val_intCast_eq_one_iff]
    intro hd
    exact (Int.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (by exact_mod_cast hd))

/-- After Exercise 4.21 (pdf p. 216): by (b)–(d), $E$ is semistable: at every prime it has good or multiplicative
reduction (so its conductor divides $\prod_{p \mid \alpha\beta\gamma}p$). -/
@[kb "milne2006ec" "Ch. V, Exercise 4.21, the conductor divides ∏ p (running text), pdf p. 216"]
theorem freyCurve_semistable {α β γ : ℤ} {ℓ : ℕ} (h : FreyHyp α β γ ℓ) (hγ : Even γ) (hα : α ^ ℓ % 4 = 3)
    (p : ℕ) [Fact p.Prime] :
    HasGoodReductionAt (freyCurve α γ ℓ) p ∨
      ((freyCurve α γ ℓ |>.baseChange ℚ_[p]).minimal ℤ_[p]).HasMultiplicativeReduction ℤ_[p] := by
  by_cases hp : (p : ℤ) ∣ α * β * γ
  · right
    rcases eq_or_ne p 2 with rfl | hp2
    · exact exercise_4_21_d h hγ hα
    · exact exercise_4_21_c h p hp2 hp
  · left
    exact exercise_4_21_b h p hp

end NumberFieldKB.MilneEC.V
