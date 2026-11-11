import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import QuadFormsKB.Citation

/-!
# Milne, *Elliptic Curves*, Chapter V, Exercise 4.21: the Frey curve

Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, Exercise 4.21 (pdf pp. 215–216). Let $\alpha, \beta, \gamma$ be
nonzero relatively prime integers with $\alpha^\ell + \beta^\ell = \gamma^\ell$, $\ell$ a prime $\ne 2, 3$, and
$E : Y^2 Z = X(X - \alpha^\ell Z)(X - \gamma^\ell Z)$ (`freyCurve`; in Weierstrass form
$a_1 = a_3 = a_6 = 0$, $a_2 = -(\alpha^\ell + \gamma^\ell)$, $a_4 = \alpha^\ell\gamma^\ell$).

* (a) `exercise_4_21_a`: $\Delta = 16\alpha^{2\ell}\beta^{2\ell}\gamma^{2\ell}$.
* (b) `exercise_4_21_b`: good reduction at every prime $p \nmid \alpha\beta\gamma$.
* (c) `exercise_4_21_c`: at worst nodal (good or multiplicative) reduction at every odd prime $p \mid \alpha\beta\gamma$.
* (d) `exercise_4_21_d`: after reordering so that $\gamma$ is even and $\alpha^\ell \equiv -1 \pmod 4$ (Milne's hint), at
  worst nodal reduction at $2$; the change of variables $x = 4X$, $y = 8Y + 4X$ of the hint gives an integral
  equation (`freyCurve_two`, `exercise_4_21_d_integral`).

Reduction types at $p$ are those of Mathlib's minimal model of $E$ over $\mathbb Q_p$ (`HasGoodReductionAt`,
`HasMultiplicativeReductionAt`); "at worst nodal" means good or multiplicative (Milne, IV.2).

The text's curve has two lost glyphs in the source used here ("$X(X - \alpha^\ell Z)(X - {?}^\ell Z)$"); the third root
is $\gamma^\ell$: this is the only reading for which (a) holds.
-/

open WeierstrassCurve IsLocalRing IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace NumberFieldKB.MilneEC.Vb

/-- An elliptic curve $E$ over $\mathbb Q$ has **good reduction at $p$**: its minimal model over $\mathbb Q_p$ has good
reduction (Mathlib's `WeierstrassCurve.HasGoodReduction` over $\mathbb Z_p$). -/
def HasGoodReductionAt (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  ((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasGoodReduction ℤ_[p]

/-- An elliptic curve $E$ over $\mathbb Q$ has **multiplicative (nodal) reduction at $p$**. -/
def HasMultiplicativeReductionAt (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  ((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasMultiplicativeReduction ℤ_[p]

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A minimal equation has the largest discriminant valuation among integral equations isomorphic
to it. -/
theorem val_Δ_le_of_isMinimal {M E : WeierstrassCurve K} [IsMinimal R M] (j : VariableChange K)
    (hj : j • M = E) [hE : IsIntegral R E] :
    valuation K (IsDiscreteValuationRing.maximalIdeal R) E.Δ ≤
      valuation K (IsDiscreteValuationRing.maximalIdeal R) M.Δ := by
  subst hj
  have hM := (IsMinimal.val_Δ_maximal (R := R) (W := M))
  have key : valuation_Δ_aux R (j • M) ≤ valuation_Δ_aux R ((1 : VariableChange K) • M) := by
    rcases le_total (valuation_Δ_aux R ((1 : VariableChange K) • M)) (valuation_Δ_aux R (j • M))
      with h | h
    · exact hM.2 hE h
    · exact h
  have : IsIntegral R ((1 : VariableChange K) • M) := hM.1
  have k2 := Subtype.coe_le_coe.2 key
  rw [one_smul] at k2
  rw [valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral] at k2
  exact k2

theorem val_le_one_of_isIntegral (E : WeierstrassCurve K) [IsIntegral R E] :
    valuation K (IsDiscreteValuationRing.maximalIdeal R) E.Δ ≤ 1 := by
  obtain ⟨r, hr⟩ := Δ_integral_of_isIntegral R E
  rw [← hr]
  exact valuation_le_one _ r

/-- If an integral model has unit discriminant, the minimal model has good reduction. -/
theorem hasGoodReduction_of_model {M E : WeierstrassCurve K} [IsMinimal R M] (j : VariableChange K)
    (hj : j • M = E) [IsIntegral R E]
    (h : valuation K (IsDiscreteValuationRing.maximalIdeal R) E.Δ = 1) :
    M.HasGoodReduction R := by
  refine { goodReduction := ?_ }
  have h1 := val_Δ_le_of_isMinimal (R := R) j hj
  have h2 := val_le_one_of_isIntegral (R := R) M
  exact le_antisymm h2 (h ▸ h1)

/-- If an integral model has unit `c₄` and nonzero discriminant, the minimal model has good or
multiplicative reduction. -/
theorem hasGoodReduction_or_mult_of_model {M E : WeierstrassCurve K} [IsMinimal R M]
    (j : VariableChange K) (hj : j • M = E) [IsIntegral R E]
    (hc : valuation K (IsDiscreteValuationRing.maximalIdeal R) E.c₄ = 1) (hΔ : E.Δ ≠ 0) :
    M.HasGoodReduction R ∨ M.HasMultiplicativeReduction R := by
  set v := valuation K (IsDiscreteValuationRing.maximalIdeal R) with hv
  have h1 := val_Δ_le_of_isMinimal (R := R) j hj
  have hM : M = j⁻¹ • E := by rw [← hj]; simp
  have hMΔ : M.Δ = (j⁻¹).u⁻¹ ^ 12 * E.Δ := by rw [hM, variableChange_Δ]
  have hMc : M.c₄ = (j⁻¹).u⁻¹ ^ 4 * E.c₄ := by rw [hM, variableChange_c₄]
  set b := v (((j⁻¹).u⁻¹ : Kˣ) : K) with hb
  have hMΔ' : v M.Δ = (b ^ 4) ^ 3 * v E.Δ := by
    rw [hMΔ, map_mul, map_pow, ← pow_mul]
  have hMc' : v M.c₄ = b ^ 4 := by
    rw [hMc, map_mul, map_pow, hc, mul_one]
  have hle : v M.c₄ ≤ 1 := by
    rw [← integralModel_c₄_eq R M]; exact valuation_le_one _ _
  have hvΔ : v E.Δ ≠ 0 := by simpa using hΔ
  have hge : 1 ≤ (b ^ 4) ^ 3 := by
    rw [hMΔ'] at h1
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_right hlt (zero_lt_iff.2 hvΔ)
    rw [one_mul] at this
    exact absurd h1 (not_le.2 this)
  have hb4 : b ^ 4 = 1 := by
    by_contra hne
    have hlt : b ^ 4 < 1 := lt_of_le_of_ne (hMc' ▸ hle) hne
    have := pow_lt_one₀ (zero_le) hlt (by norm_num : 3 ≠ 0)
    exact absurd hge (not_le.2 this)
  have hMc1 : v M.c₄ = 1 := by rw [hMc', hb4]
  rcases (val_le_one_of_isIntegral (R := R) M).eq_or_lt with h | h
  · exact Or.inl { goodReduction := h }
  · exact Or.inr { badReduction := h, multiplicativeReduction := hMc1 }

end Generic


section Padic

variable (p : ℕ) [Fact p.Prime]

/-- The valuation of an integer prime to `p` is one. -/
theorem valuation_intCast_eq_one {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    valuation ℚ_[p] (IsDiscreteValuationRing.maximalIdeal ℤ_[p]) (n : ℚ_[p]) = 1 := by
  have : (n : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (n : ℤ_[p]) := by simp
  rw [this, valuation_eq_one_iff_notMem]
  intro hmem
  have hmem' : (n : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := hmem
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PadicInt.isUnit_iff] at hmem'
  apply hn
  rw [← PadicInt.norm_int_lt_one_iff_dvd]
  exact lt_of_le_of_ne (PadicInt.norm_le_one _) hmem'

theorem isIntegral_map_int (W : WeierstrassCurve ℤ) :
    IsIntegral ℤ_[p] ((W.map (algebraMap ℤ ℚ)).baseChange ℚ_[p]) := by
  refine ⟨W.map (algebraMap ℤ ℤ_[p]), ?_⟩
  ext <;> simp [baseChange]

theorem exists_smul_minimal (E E' : WeierstrassCurve ℚ) (Cq : VariableChange ℚ) (h : Cq • E = E') :
    ∃ j : VariableChange ℚ_[p], j • ((E.baseChange ℚ_[p]).minimal ℤ_[p]) = E'.baseChange ℚ_[p] := by
  obtain ⟨C0, hC0⟩ : ∃ C0 : VariableChange ℚ_[p],
      (E.baseChange ℚ_[p]).minimal ℤ_[p] = C0 • E.baseChange ℚ_[p] := ⟨_, rfl⟩
  refine ⟨(Cq.map (algebraMap ℚ ℚ_[p])) * C0⁻¹, ?_⟩
  rw [hC0, mul_smul, inv_smul_smul]
  rw [← h]
  exact map_variableChange E Cq (algebraMap ℚ ℚ_[p])

theorem hasGoodReductionAt_of_model (E E' : WeierstrassCurve ℚ) (Cq : VariableChange ℚ)
    (h : Cq • E = E') (W : WeierstrassCurve ℤ) (hW : W.map (algebraMap ℤ ℚ) = E')
    (hΔ : ¬ (p : ℤ) ∣ W.Δ) : HasGoodReductionAt E p := by
  obtain ⟨j, hj⟩ := exists_smul_minimal p E E' Cq h
  subst hW
  have := isIntegral_map_int p W
  refine hasGoodReduction_of_model (R := ℤ_[p]) j hj ?_
  have : ((W.map (algebraMap ℤ ℚ)).baseChange ℚ_[p]).Δ = ((W.Δ : ℤ) : ℚ_[p]) := by
    simp [baseChange, map_Δ]
  rw [this]
  exact valuation_intCast_eq_one p hΔ

theorem hasGoodReduction_or_mult_AtOfModel (E E' : WeierstrassCurve ℚ) (Cq : VariableChange ℚ)
    (h : Cq • E = E') (W : WeierstrassCurve ℤ) (hW : W.map (algebraMap ℤ ℚ) = E')
    (hΔ : W.Δ ≠ 0) (hc : ¬ (p : ℤ) ∣ W.c₄) :
    HasGoodReductionAt E p ∨ HasMultiplicativeReductionAt E p := by
  obtain ⟨j, hj⟩ := exists_smul_minimal p E E' Cq h
  subst hW
  have := isIntegral_map_int p W
  refine hasGoodReduction_or_mult_of_model (R := ℤ_[p]) j hj ?_ ?_
  · have : ((W.map (algebraMap ℤ ℚ)).baseChange ℚ_[p]).c₄ = ((W.c₄ : ℤ) : ℚ_[p]) := by
      simp [baseChange, map_c₄]
    rw [this]
    exact valuation_intCast_eq_one p hc
  · have : ((W.map (algebraMap ℤ ℚ)).baseChange ℚ_[p]).Δ = ((W.Δ : ℤ) : ℚ_[p]) := by
      simp [baseChange, map_Δ]
    rw [this]
    exact_mod_cast hΔ

end Padic

/-- The Frey curve $Y^2 = X(X - \alpha^\ell)(X - \gamma^\ell)$ over $\mathbb Q$. -/
def freyCurve (α γ : ℤ) (ℓ : ℕ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -((α : ℚ) ^ ℓ + (γ : ℚ) ^ ℓ)
  a₃ := 0
  a₄ := (α : ℚ) ^ ℓ * (γ : ℚ) ^ ℓ
  a₆ := 0

/-- **Exercise 4.21(a)** (Milne, *EC*, V, Exercise 4.21(a), p. 215): the Frey curve has discriminant
$\Delta = 16\alpha^{2\ell}\beta^{2\ell}\gamma^{2\ell}$ (only $\alpha^\ell + \beta^\ell = \gamma^\ell$ is used). -/
@[kb "milne2006ec" "Ch. V, Exercise 4.21(a) (pdf p. 215)"]
theorem exercise_4_21_a {α β γ : ℤ} {ℓ : ℕ} (h : α ^ ℓ + β ^ ℓ = γ ^ ℓ) :
    (freyCurve α γ ℓ).Δ = 16 * (α : ℚ) ^ (2 * ℓ) * (β : ℚ) ^ (2 * ℓ) * (γ : ℚ) ^ (2 * ℓ) := by

  have h' : (α : ℚ) ^ ℓ + (β : ℚ) ^ ℓ = (γ : ℚ) ^ ℓ := by exact_mod_cast h
  have hB : (β : ℚ) ^ ℓ = (γ : ℚ) ^ ℓ - (α : ℚ) ^ ℓ := by linarith
  simp only [pow_mul', hB]
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, freyCurve]
  ring

/-- The Frey curve with integer coefficients. -/
def freyW (α γ : ℤ) (ℓ : ℕ) : WeierstrassCurve ℤ :=
  ⟨0, -(α ^ ℓ + γ ^ ℓ), 0, α ^ ℓ * γ ^ ℓ, 0⟩

theorem freyW_map (α γ : ℤ) (ℓ : ℕ) : (freyW α γ ℓ).map (algebraMap ℤ ℚ) = freyCurve α γ ℓ := by
  ext <;> simp [freyW, freyCurve]

theorem freyW_Δ {α β γ : ℤ} {ℓ : ℕ} (h : α ^ ℓ + β ^ ℓ = γ ^ ℓ) :
    (freyW α γ ℓ).Δ = 16 * α ^ (2 * ℓ) * β ^ (2 * ℓ) * γ ^ (2 * ℓ) := by
  have := exercise_4_21_a h
  rw [← freyW_map, map_Δ] at this
  simp only [eq_intCast] at this
  exact_mod_cast this

theorem freyW_c₄ (α γ : ℤ) (ℓ : ℕ) :
    (freyW α γ ℓ).c₄ = 16 * ((α ^ ℓ) ^ 2 - α ^ ℓ * γ ^ ℓ + (γ ^ ℓ) ^ 2) := by
  simp only [WeierstrassCurve.c₄, b₂, b₄, freyW]
  ring

theorem not_dvd_two_of_not_dvd {α β γ : ℤ} {ℓ : ℕ} (h : α ^ ℓ + β ^ ℓ = γ ^ ℓ)
    (hp : ¬ (2 : ℤ) ∣ α * β * γ) : False := by
  have ha : ¬ (2 : ℤ) ∣ α := fun h' => hp (Dvd.dvd.mul_right (Dvd.dvd.mul_right h' _) _)
  have hb : ¬ (2 : ℤ) ∣ β := fun h' => hp (Dvd.dvd.mul_right (Dvd.dvd.mul_left h' _) _)
  have hg : ¬ (2 : ℤ) ∣ γ := fun h' => hp (Dvd.dvd.mul_left h' _)
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · norm_num at h
  · have hℓ' : ℓ ≠ 0 := hℓ.ne'
    have h1 : Even (α ^ ℓ + β ^ ℓ) ↔ Even (γ ^ ℓ) := by rw [h]
    rw [Int.even_add, Int.even_pow' hℓ', Int.even_pow' hℓ', Int.even_pow' hℓ'] at h1
    simp only [even_iff_two_dvd] at h1
    tauto


/-- Exercise 4.21(b) for the Frey curve (helper). -/
theorem hasGoodReductionAt_freyCurve {α β γ : ℤ} {ℓ : ℕ} (h : α ^ ℓ + β ^ ℓ = γ ^ ℓ) (p : ℕ) [Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ α * β * γ) : HasGoodReductionAt (freyCurve α γ ℓ) p := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  refine hasGoodReductionAt_of_model p _ _ 1 (one_smul _ _) (freyW α γ ℓ) (freyW_map α γ ℓ) ?_
  rw [freyW_Δ h]
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact not_dvd_two_of_not_dvd h (by exact_mod_cast hp)
  have h16 : ¬ (p : ℤ) ∣ 16 := by
    intro hd
    have : (p : ℤ) ∣ 2 ^ 4 := by norm_num; exact hd
    have h2 := hpr.dvd_of_dvd_pow this
    have h2' : p ∣ 2 := by exact_mod_cast h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2')
  have hpow : ∀ x : ℤ, (p : ℤ) ∣ x ∨ True → ∀ n, ¬ (p : ℤ) ∣ x → ¬ (p : ℤ) ∣ x ^ n ∨ n = 0 := by
    intro x _ n hx
    by_cases hn : n = 0
    · exact Or.inr hn
    · exact Or.inl fun hd => hx (hpr.dvd_of_dvd_pow hd)
  have hα : ¬ (p : ℤ) ∣ α := fun d => hp (Dvd.dvd.mul_right (Dvd.dvd.mul_right d _) _)
  have hβ : ¬ (p : ℤ) ∣ β := fun d => hp (Dvd.dvd.mul_right (Dvd.dvd.mul_left d _) _)
  have hγ : ¬ (p : ℤ) ∣ γ := fun d => hp (Dvd.dvd.mul_left d _)
  intro hd
  rcases hpr.dvd_or_dvd hd with hd | hd
  · rcases hpr.dvd_or_dvd hd with hd | hd
    · rcases hpr.dvd_or_dvd hd with hd | hd
      · exact h16 hd
      · exact hα (hpr.dvd_of_dvd_pow hd)
    · exact hβ (hpr.dvd_of_dvd_pow hd)
  · exact hγ (hpr.dvd_of_dvd_pow hd)

/-- **Exercise 4.21(b)** (Milne, *EC*, V, Exercise 4.21(b), p. 215): if $p \nmid \alpha\beta\gamma$, the Frey curve
has good reduction at $p$. -/
@[kb "milne2006ec" "Ch. V, Exercise 4.21(b) (pdf p. 215)"]
theorem exercise_4_21_b {α β γ : ℤ} {ℓ : ℕ} (h : α ^ ℓ + β ^ ℓ = γ ^ ℓ) (p : ℕ) [Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ α * β * γ) : HasGoodReductionAt (freyCurve α γ ℓ) p :=
  hasGoodReductionAt_freyCurve h p hp

/-- Two coprime integers have no common prime divisor. -/
theorem no_common {a b : ℤ} (hab : IsCoprime a b) (p : ℕ) [Fact p.Prime] (ha : (p : ℤ) ∣ a)
    (hb : (p : ℤ) ∣ b) : False := by
  have := Int.isUnit_iff.mp (hab.isUnit_of_dvd' ha hb)
  have h1 := (Fact.out : p.Prime).one_lt
  omega

/-- Exercise 4.21(c) when $\alpha\beta\gamma \ne 0$ (helper). -/
theorem nodal_freyCurve_of_ne_zero {α β γ : ℤ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (h : α ^ ℓ + β ^ ℓ = γ ^ ℓ)
    (hαβ : IsCoprime α β) (hαγ : IsCoprime α γ) (_hβγ : IsCoprime β γ) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hp : (p : ℤ) ∣ α * β * γ) (h0 : α * β * γ ≠ 0) :
    HasGoodReductionAt (freyCurve α γ ℓ) p ∨ HasMultiplicativeReductionAt (freyCurve α γ ℓ) p := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hα0 : α ≠ 0 := fun e => h0 (by simp [e])
  have hβ0 : β ≠ 0 := fun e => h0 (by simp [e])
  have hγ0 : γ ≠ 0 := fun e => h0 (by simp [e])
  refine hasGoodReduction_or_mult_AtOfModel p _ _ 1 (one_smul _ _) (freyW α γ ℓ) (freyW_map α γ ℓ)
    ?_ ?_
  · rw [freyW_Δ h]
    positivity
  · rw [freyW_c₄]
    intro hd
    have h16 : ¬ (p : ℤ) ∣ 16 := by
      intro hd
      have : (p : ℤ) ∣ 2 ^ 4 := by norm_num; exact hd
      have h2 := hpr.dvd_of_dvd_pow this
      have h2' : p ∣ 2 := by exact_mod_cast h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2')
    have hℓ0 : ℓ ≠ 0 := by omega
    have hC : γ ^ ℓ = α ^ ℓ + β ^ ℓ := h.symm
    rcases hpr.dvd_or_dvd hd with hd | hq
    · exact h16 hd
    rcases hpr.dvd_or_dvd hp with hp' | hγ
    · rcases hpr.dvd_or_dvd hp' with hα | hβ
      · have hA : (p : ℤ) ∣ α ^ ℓ := dvd_pow hα hℓ0
        have : (p : ℤ) ∣ (γ ^ ℓ) ^ 2 := by
          have := dvd_sub hq (Dvd.dvd.mul_right hA (α ^ ℓ - γ ^ ℓ))
          convert this using 1; ring
        exact no_common hαγ p hα (hpr.dvd_of_dvd_pow (hpr.dvd_of_dvd_pow this))
      · have hB : (p : ℤ) ∣ β ^ ℓ := dvd_pow hβ hℓ0
        rw [hC] at hq
        have : (p : ℤ) ∣ (α ^ ℓ) ^ 2 := by
          have := dvd_sub hq (Dvd.dvd.mul_right hB (α ^ ℓ + β ^ ℓ))
          convert this using 1; ring
        exact no_common hαβ p (hpr.dvd_of_dvd_pow (hpr.dvd_of_dvd_pow this)) hβ
    · have hC' : (p : ℤ) ∣ γ ^ ℓ := dvd_pow hγ hℓ0
      have : (p : ℤ) ∣ (α ^ ℓ) ^ 2 := by
        have := dvd_sub hq (Dvd.dvd.mul_left hC' (γ ^ ℓ - α ^ ℓ))
        convert this using 1; ring
      exact no_common hαγ p (hpr.dvd_of_dvd_pow (hpr.dvd_of_dvd_pow this)) hγ

/-- **Exercise 4.21(c)** (Milne, *EC*, V, Exercise 4.21(c), p. 215): if $p$ is an odd prime dividing $\alpha\beta\gamma$
($\alpha, \beta, \gamma$ nonzero and relatively prime, $\alpha^\ell + \beta^\ell = \gamma^\ell$, $\ell \ge 1$), the Frey curve has at
worst nodal reduction at $p$. -/
@[kb "milne2006ec" "Ch. V, Exercise 4.21(c) (pdf p. 215)"]
theorem exercise_4_21_c {α β γ : ℤ} {ℓ : ℕ} (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hγ0 : γ ≠ 0) (hℓ : 1 ≤ ℓ)
    (h : α ^ ℓ + β ^ ℓ = γ ^ ℓ)
    (hαβ : IsCoprime α β) (hαγ : IsCoprime α γ) (hβγ : IsCoprime β γ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : (p : ℤ) ∣ α * β * γ) :
    HasGoodReductionAt (freyCurve α γ ℓ) p ∨ HasMultiplicativeReductionAt (freyCurve α γ ℓ) p :=
  nodal_freyCurve_of_ne_zero hℓ h hαβ hαγ hβγ p hp2 hp (by simp [hα0, hβ0, hγ0])

/-- The model of the hint to Exercise 4.21(d): substituting $x = 4X$, $y = 8Y + 4X$ in
$y^2 = x(x - A)(x - C)$ ($A = \alpha^\ell$, $C = \gamma^\ell$) gives $Y^2 + XY = X^3 - \tfrac{A + C + 1}{4}X^2 +
\tfrac{AC}{16}X$. -/
def freyCurve_two (α γ : ℤ) (ℓ : ℕ) : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := -(((α : ℚ) ^ ℓ + (γ : ℚ) ^ ℓ + 1) / 4)
  a₃ := 0
  a₄ := (α : ℚ) ^ ℓ * (γ : ℚ) ^ ℓ / 16
  a₆ := 0

/-- The variable change of the hint ($u = 2$, $r = 0$, $s = 1$, $t = 0$ in Mathlib's convention
$x = u^2x' + r$, $y = u^3y' + su^2x' + t$) carries the Frey curve to `freyCurve_two`. -/
@[kb "milne2006ec" "Ch. V, Exercise 4.21(d), hint (pdf p. 215): change of variables"]
theorem freyCurve_two_eq (α γ : ℤ) (ℓ : ℕ) :
    (⟨Units.mk0 2 two_ne_zero, 0, 1, 0⟩ : VariableChange ℚ) • freyCurve α γ ℓ = freyCurve_two α γ ℓ := by
  ext <;> simp [variableChange_def, freyCurve, freyCurve_two] <;> field_simp <;> ring


/-- Variant of `exercise_4_21_d_integral` recording `a₁ = 1`, `a₃ = 0` of the integral model. -/
theorem exists_integral_model_two {α γ : ℤ} {ℓ : ℕ} (hℓ : 4 ≤ ℓ) (hγ : Even γ) (hα : α ^ ℓ ≡ -1 [ZMOD 4]) :
    ∃ W : WeierstrassCurve ℤ, W.map (algebraMap ℤ ℚ) = freyCurve_two α γ ℓ ∧ W.a₁ = 1 ∧ W.a₃ = 0 := by
  obtain ⟨k, hk⟩ := hγ
  have h16 : (16 : ℤ) ∣ γ ^ ℓ := by
    have : γ = 2 * k := by omega
    subst this
    rw [mul_pow]
    exact Dvd.dvd.mul_right ((by norm_num : (16 : ℤ) ∣ 2 ^ 4).trans (pow_dvd_pow 2 hℓ)) _
  obtain ⟨c, hc⟩ := h16
  have h4 : (4 : ℤ) ∣ α ^ ℓ + γ ^ ℓ + 1 := by
    have := hα.symm.dvd
    rw [hc]; omega
  obtain ⟨m, hm⟩ := h4
  refine ⟨⟨1, -m, 0, α ^ ℓ * c, 0⟩, ?_, rfl, rfl⟩
  have hm' : ((α : ℚ) ^ ℓ + (γ : ℚ) ^ ℓ + 1) = 4 * m := by exact_mod_cast hm
  have hc' : (γ : ℚ) ^ ℓ = 16 * c := by exact_mod_cast hc
  ext <;> simp [freyCurve_two]
  · rw [hm']; ring
  · rw [hc']; ring

/-- Exercise 4.21(d), hint (Milne, *EC*, V, p. 215): if $\gamma$ is even, $\alpha^\ell \equiv -1 \pmod 4$ and
$\ell \ge 4$, the equation `freyCurve_two` has integer coefficients. -/
@[kb "milne2006ec" "Ch. V, Exercise 4.21(d), hint (pdf p. 215): integral model"]
theorem exercise_4_21_d_integral {α γ : ℤ} {ℓ : ℕ} (hℓ : 4 ≤ ℓ) (hγ : Even γ) (hα : α ^ ℓ ≡ -1 [ZMOD 4]) :
    ∃ W : WeierstrassCurve ℤ, W.map (algebraMap ℤ ℚ) = freyCurve_two α γ ℓ := by
  obtain ⟨W, hW, -, -⟩ := exists_integral_model_two hℓ hγ hα
  exact ⟨W, hW⟩

/-- Exercise 4.21(d) when $\alpha\beta\gamma \ne 0$ (helper). -/
theorem nodal_freyCurve_two_of_ne_zero {α β γ : ℤ} {ℓ : ℕ} (hℓ : 4 ≤ ℓ) (h : α ^ ℓ + β ^ ℓ = γ ^ ℓ)
    (hγ : Even γ) (hα : α ^ ℓ ≡ -1 [ZMOD 4]) [Fact (Nat.Prime 2)] (h0 : α * β * γ ≠ 0) :
    HasGoodReductionAt (freyCurve α γ ℓ) 2 ∨ HasMultiplicativeReductionAt (freyCurve α γ ℓ) 2 := by
  obtain ⟨W, hW, ha1, ha3⟩ := exists_integral_model_two hℓ hγ hα
  refine hasGoodReduction_or_mult_AtOfModel 2 _ _ _ (freyCurve_two_eq α γ ℓ) W hW ?_ ?_
  · intro h0'
    have h1 : ((W.Δ : ℤ) : ℚ) = ((⟨Units.mk0 2 two_ne_zero, 0, 1, 0⟩ : VariableChange ℚ) •
        freyCurve α γ ℓ).Δ := by
      rw [freyCurve_two_eq, ← hW, map_Δ]
      simp
    rw [variableChange_Δ, h0', exercise_4_21_a h] at h1
    have hα0 : α ≠ 0 := fun e => h0 (by simp [e])
    have hβ0 : β ≠ 0 := fun e => h0 (by simp [e])
    have hγ0 : γ ≠ 0 := fun e => h0 (by simp [e])
    revert h1
    simp
    exact ⟨⟨fun e => absurd e hα0, fun e => absurd e hβ0⟩, fun e => absurd e hγ0⟩
  · simp only [WeierstrassCurve.c₄, b₂, b₄, ha1, ha3]
    generalize W.a₂ = x
    generalize W.a₄ = y
    rintro ⟨k, hk⟩
    push_cast at hk
    have e : (1 : ℤ) = 2 * (k - (4 * x + 8 * x ^ 2 - 24 * y)) := by linear_combination hk
    omega

/-- **Exercise 4.21(d)** (Milne, *EC*, V, Exercise 4.21(d), p. 215): with $\alpha, \beta, \gamma$ nonzero and relatively
prime, $\alpha^\ell + \beta^\ell = \gamma^\ell$, $\ell \ge 4$, and (after the reordering of the hint) $\gamma$ even and
$\alpha^\ell \equiv -1 \pmod 4$, the minimal equation of the Frey curve has at worst nodal reduction at $2$. -/
@[kb "milne2006ec" "Ch. V, Exercise 4.21(d) (pdf p. 215)"]
theorem exercise_4_21_d {α β γ : ℤ} {ℓ : ℕ} (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hγ0 : γ ≠ 0) (hℓ : 4 ≤ ℓ)
    (h : α ^ ℓ + β ^ ℓ = γ ^ ℓ)
    (_hαβ : IsCoprime α β) (_hαγ : IsCoprime α γ) (_hβγ : IsCoprime β γ) (hγ : Even γ)
    (hα : α ^ ℓ ≡ -1 [ZMOD 4]) [Fact (Nat.Prime 2)] :
    HasGoodReductionAt (freyCurve α γ ℓ) 2 ∨ HasMultiplicativeReductionAt (freyCurve α γ ℓ) 2 :=
  nodal_freyCurve_two_of_ne_zero hℓ h hγ hα (by simp [hα0, hβ0, hγ0])

end NumberFieldKB.MilneEC.Vb
