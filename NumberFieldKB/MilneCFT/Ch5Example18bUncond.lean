import NumberFieldKB.MilneCFT.Ch5Extra
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Quadratic.RingOfIntegers

/-!
# Milne, *Class Field Theory*, V, Example 1.8 (b): the table, unconditionally

For $d = 2, 3, 5, 6$ and a quadratic field $K \ni s$ with $s^2 = d$:
* the class number of $K$ is $1$ (Minkowski bound: $|\Delta_K| = 8, 12, 5 < 16$; for $d = 6$, $\Delta_K = 24$, the
  bound is $\sqrt{24}/2 < 3$ and the unique prime above $2$ is $(2 + s)$);
* $\varepsilon = 1 + s$, $2 + s$, $(1 + s)/2$, $5 + 2s$ is a fundamental unit (every unit is $\pm\varepsilon^k$), of
  norm $-1, 1, -1, 1$;
* the narrow class number is $1, 2, 1, 2$ (`example_1_8b_quadratic`).

The unit computation uses the real embedding $\varphi$ with $\varphi(s) = \sqrt d$: a unit $u$ with $\varphi(u) > 1$
has positive coordinates (its conjugate has absolute value $< 1$), which bounds it below by $\varphi(\varepsilon)$
(`le_of_one_lt`); then $\varphi(\pm u)\,\varphi(\varepsilon)^{-k} \in [1, \varphi(\varepsilon))$ forces
$\pm u = \varepsilon^k$.

Main result: `example_1_8b_table : Example1_8b_table`.
-/

open NumberField Polynomial Module NumberField.InfinitePlace

noncomputable section

namespace NumberFieldKB.MilneCFT.Ex18b

variable {K : Type} [Field K] [NumberField K]

/-! ## The presentation $K = \mathbb Q(s)$ -/

theorem not_mem_range_of_sq {d : ℤ} {s : K} (hs : s ^ 2 = (d : K)) (hsq : ¬ IsSquare (d : ℚ)) :
    s ∉ Set.range (algebraMap ℚ K) := by
  rintro ⟨q, rfl⟩
  apply hsq
  refine ⟨q, ?_⟩
  apply (algebraMap ℚ K).injective
  rw [map_mul, ← pow_two, hs]
  simp

/-- The integral generator $\theta = s$ of $K$, with minimal polynomial $X^2 - d$. -/
theorem exists_gen (hK : finrank ℚ K = 2) {d : ℤ} {s : K} (hs : s ^ 2 = (d : K))
    (hsq : ¬ IsSquare (d : ℚ)) :
    ∃ θ : 𝓞 K, (θ : K) = s ∧ minpoly ℤ θ = X ^ 2 - C d ∧ Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have hzQ := not_mem_range_of_sq hs hsq
  have hpz : aeval s (X ^ 2 - C d : ℤ[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hs, algebraMap_int_eq, eq_intCast, sub_self]
  have hint : IsIntegral ℤ s := ⟨_, monic_X_pow_sub_C _ two_ne_zero, hpz⟩
  refine ⟨⟨s, hint⟩, RingOfIntegers.map_mk s hint, ?_, ?_⟩
  · set θ : 𝓞 K := ⟨s, hint⟩
    have hθ : IsIntegral ℤ θ := RingOfIntegers.isIntegral θ
    have hpθ : aeval θ (X ^ 2 - C d) = 0 :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K <| by
        rw [← aeval_algebraMap_apply, map_zero]
        exact hpz
    refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hθ)
      (monic_X_pow_sub_C _ two_ne_zero) (minpoly.isIntegrallyClosed_dvd hθ hpθ) ?_).symm
    have hrat := minpoly.isIntegrallyClosed_eq_field_fractions ℚ K hθ
    have hpos := minpoly.natDegree_pos (hint.tower_top (A := ℚ))
    have hne : (minpoly ℚ s).natDegree ≠ 1 := fun h => hzQ (minpoly.natDegree_eq_one_iff.mp h)
    have hθz : algebraMap (𝓞 K) K θ = s := RingOfIntegers.map_mk s hint
    rw [natDegree_X_pow_sub_C, ← (minpoly.monic hθ).natDegree_map (algebraMap ℤ ℚ), ← hrat, hθz]
    omega
  · rw [eq_top_iff]
    intro w _
    obtain ⟨p, q, rfl⟩ :=
      Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul ℚ K hzQ w
    exact add_mem (Subalgebra.algebraMap_mem _ q)
      (mul_mem (Subalgebra.algebraMap_mem _ p) (Algebra.self_mem_adjoin_singleton ℚ _))

/-! ## The real embedding $s \mapsto \sqrt d$ -/

/-- A real embedding of $K$ sending $s$ to $\sqrt d$. -/
theorem exists_embedding (hK : finrank ℚ K = 2) {d : ℤ} (hd : 0 < d) {s : K} (hs : s ^ 2 = (d : K))
    (hsq : ¬ IsSquare (d : ℚ)) : ∃ φ : K →+* ℝ, φ s = Real.sqrt d := by
  obtain ⟨θ, hθs, hmin, hgen⟩ := exists_gen hK hs hsq
  have hint : IsIntegral ℚ (θ : K) := θ.isIntegral_coe.tower_top
  set pb := PowerBasis.ofAdjoinEqTop' hint hgen
  have hpbgen : pb.gen = (θ : K) := PowerBasis.ofAdjoinEqTop'_gen hint hgen
  have hy : aeval (Real.sqrt d) (minpoly ℚ pb.gen) = 0 := by
    rw [hpbgen, minpoly_rat_quadratic hmin]
    simp only [map_sub, map_pow, aeval_X, aeval_C, eq_ratCast, Rat.cast_intCast]
    rw [Real.sq_sqrt (by exact_mod_cast hd.le), sub_self]
  refine ⟨(pb.lift _ hy).toRingHom, ?_⟩
  show pb.lift _ hy s = _
  rw [← hθs, ← hpbgen, PowerBasis.lift_gen]

/-! ## Units -/

/-- A unit of norm $\pm1$ greater than $1$ has positive coordinates: if $x = (A + B\sqrt d)/2 > 1$ and
$A^2 - dB^2 = \pm 4$, then $A, B > 0$. -/
theorem pos_coords {d : ℤ} (hd : 0 < d) {A B : ℤ} (hN : A ^ 2 - d * B ^ 2 = 4 ∨ A ^ 2 - d * B ^ 2 = -4)
    (hx : 1 < ((A : ℝ) + B * Real.sqrt d) / 2) : 0 < A ∧ 0 < B := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd'.le
  have hspos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd'
  set x : ℝ := ((A : ℝ) + B * Real.sqrt d) / 2
  set y : ℝ := ((A : ℝ) - B * Real.sqrt d) / 2
  have hxy : x * y = 1 ∨ x * y = -1 := by
    rcases hN with h | h
    · left
      have h' : (A : ℝ) ^ 2 - d * B ^ 2 = 4 := by exact_mod_cast h
      simp only [x, y]
      nlinarith
    · right
      have h' : (A : ℝ) ^ 2 - d * B ^ 2 = -4 := by exact_mod_cast h
      simp only [x, y]
      nlinarith
  have hy : |y| < 1 := by
    have hx0 : 0 < x := by linarith
    have : |x * y| = 1 := by rcases hxy with h | h <;> rw [h] <;> simp
    rw [abs_mul, abs_of_pos hx0] at this
    by_contra hcon
    push Not at hcon
    nlinarith
  rw [abs_lt] at hy
  have hA : (0 : ℝ) < A := by
    have : (A : ℝ) = x + y := by simp only [x, y]; ring
    linarith
  have hB : (0 : ℝ) < B * Real.sqrt d := by
    have : (B : ℝ) * Real.sqrt d = x - y := by simp only [x, y]; ring
    linarith
  exact ⟨by exact_mod_cast hA, by exact_mod_cast (pos_of_mul_pos_left hB hspos.le)⟩

/-- The norm of a unit is $\pm1$. -/
theorem norm_unit (u : (𝓞 K)ˣ) : Algebra.norm ℚ ((u : 𝓞 K) : K) = 1 ∨
    Algebra.norm ℚ ((u : 𝓞 K) : K) = -1 := by
  have hu : IsUnit (Algebra.norm ℤ (u : 𝓞 K)) := (u.isUnit).map _
  rw [← Algebra.coe_norm_int]
  rcases Int.isUnit_iff.mp hu with h | h <;> rw [h] <;> simp

/-- **Descent.** If $\varphi(\varepsilon) > 1$ and every unit $v$ with $\varphi(v) > 1$ has
$\varphi(v) \ge \varphi(\varepsilon)$, then every unit is $\pm\varepsilon^k$. -/
theorem units_eq_of_min (φ : K →+* ℝ) (ε : (𝓞 K)ˣ) (hε : 1 < φ ((ε : 𝓞 K) : K))
    (hmin : ∀ v : (𝓞 K)ˣ, 1 < φ ((v : 𝓞 K) : K) → φ ((ε : 𝓞 K) : K) ≤ φ ((v : 𝓞 K) : K))
    (u : (𝓞 K)ˣ) : ∃ k : ℤ, u = ε ^ k ∨ u = -ε ^ k := by
  have hval : ∀ (w : (𝓞 K)ˣ) (k : ℤ), φ (((w ^ k : (𝓞 K)ˣ) : 𝓞 K) : K) = φ ((w : 𝓞 K) : K) ^ k := by
    intro w k
    have : (((w ^ k : (𝓞 K)ˣ) : 𝓞 K) : K) = (((w : 𝓞 K) : K)) ^ k := by
      have h1 : (((w ^ k : (𝓞 K)ˣ) : 𝓞 K) : K) = ((Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) w ^ k :
          Kˣ) : K) := by
        rw [← map_zpow]; rfl
      rw [h1, Units.val_zpow_eq_zpow_val]
      rfl
    rw [this, map_zpow₀]
  have hne : ∀ w : (𝓞 K)ˣ, φ ((w : 𝓞 K) : K) ≠ 0 := by
    intro w h
    rw [map_eq_zero_iff φ φ.injective] at h
    exact (Units.ne_zero w) (by exact_mod_cast h)
  -- pick the sign
  obtain ⟨v, hv, hvpos⟩ : ∃ v : (𝓞 K)ˣ, (v = u ∨ v = -u) ∧ 0 < φ ((v : 𝓞 K) : K) := by
    rcases lt_or_gt_of_ne (hne u) with h | h
    · refine ⟨-u, Or.inr rfl, ?_⟩
      have : (((-u : (𝓞 K)ˣ) : 𝓞 K) : K) = -(((u : 𝓞 K)) : K) := by push_cast; rfl
      rw [this, map_neg]
      linarith
    · exact ⟨u, Or.inl rfl, h⟩
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow hvpos hε
  set w := v * ε ^ (-k)
  have hw : φ ((w : 𝓞 K) : K) = φ ((v : 𝓞 K) : K) * φ ((ε : 𝓞 K) : K) ^ (-k) := by
    rw [← hval]
    simp [w]
  have hεpos : 0 < φ ((ε : 𝓞 K) : K) := by linarith
  have hpk : 0 < φ ((ε : 𝓞 K) : K) ^ k := zpow_pos hεpos k
  have hw1 : 1 ≤ φ ((w : 𝓞 K) : K) := by
    rw [hw, zpow_neg, ← div_eq_mul_inv, le_div_iff₀ hpk, one_mul]
    exact hk1
  have hw2 : φ ((w : 𝓞 K) : K) < φ ((ε : 𝓞 K) : K) := by
    rw [hw, zpow_neg, ← div_eq_mul_inv, div_lt_iff₀ hpk, ← zpow_one_add₀ hεpos.ne', add_comm]
    exact hk2
  have hweq : φ ((w : 𝓞 K) : K) = 1 := by
    rcases eq_or_lt_of_le hw1 with h | h
    · exact h.symm
    · exact absurd (hmin w h) (not_le.mpr hw2)
  have hw' : w = 1 := by
    have : ((w : 𝓞 K) : K) = 1 := φ.injective (by rw [hweq, map_one])
    apply Units.ext
    apply RingOfIntegers.coe_injective
    exact this.trans (by simp)
  have hvk : v = ε ^ k := by
    have : v = w * ε ^ k := by simp [w, mul_assoc]
    rw [this, hw', one_mul]
  refine ⟨k, ?_⟩
  rcases hv with rfl | rfl
  · exact Or.inl hvk
  · right
    rw [← hvk, neg_neg]

/-! ## Coordinates of units -/

theorem squarefree_int {d : ℕ} (h : Squarefree d) : Squarefree (d : ℤ) :=
  Int.squarefree_natCast.mpr h

/-- Norm of $(A + Bs)/2$. -/
theorem norm_half_coords {d : ℤ} {s : K} (hK : finrank ℚ K = 2) (hs : s ^ 2 = (d : K))
    (hsq : ¬ IsSquare (d : ℚ)) (A B : ℚ) :
    Algebra.norm ℚ (algebraMap ℚ K A + algebraMap ℚ K B * s) = A ^ 2 - B ^ 2 * d := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have hs' : s ^ 2 = algebraMap ℚ K (d : ℚ) := by rw [hs]; simp
  exact Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul_of_sq_eq
    (not_mem_range_of_sq hs hsq) hs' B A

/-- A unit $u = (A + Bs)/2$ with $\varphi(u) > 1$ has $A, B > 0$ and $A^2 - dB^2 = \pm4$. -/
theorem unit_coords {d : ℤ} (hd : 0 < d) {s : K} (hK : finrank ℚ K = 2) (hs : s ^ 2 = (d : K))
    (hsq : ¬ IsSquare (d : ℚ)) (φ : K →+* ℝ) (hφ : φ s = Real.sqrt d) (u : (𝓞 K)ˣ) (A B : ℤ)
    (hu : ((u : 𝓞 K) : K) = (A + B * s) / 2) (h1 : 1 < φ ((u : 𝓞 K) : K)) :
    0 < A ∧ 0 < B ∧ (A ^ 2 - d * B ^ 2 = 4 ∨ A ^ 2 - d * B ^ 2 = -4) := by
  have hu' : ((u : 𝓞 K) : K) = algebraMap ℚ K ((A : ℚ) / 2) + algebraMap ℚ K ((B : ℚ) / 2) * s := by
    rw [hu]; simp only [map_div₀, map_intCast, map_ofNat]; ring
  have hN := norm_unit u
  rw [hu', norm_half_coords hK hs hsq] at hN
  have hN' : A ^ 2 - d * B ^ 2 = 4 ∨ A ^ 2 - d * B ^ 2 = -4 := by
    rcases hN with h | h
    · left
      have : ((A ^ 2 - d * B ^ 2 : ℤ) : ℚ) = 4 := by push_cast; linear_combination 4 * h
      exact_mod_cast this
    · right
      have : ((A ^ 2 - d * B ^ 2 : ℤ) : ℚ) = -4 := by push_cast; linear_combination 4 * h
      exact_mod_cast this
  have hx : 1 < ((A : ℝ) + B * Real.sqrt d) / 2 := by
    have : φ ((u : 𝓞 K) : K) = ((A : ℝ) + B * Real.sqrt d) / 2 := by
      rw [hu, map_div₀, map_add, map_mul, hφ, map_intCast, map_intCast, map_ofNat]
    rwa [this] at h1
  exact ⟨(pos_coords hd hN' hx).1, (pos_coords hd hN' hx).2, hN'⟩

/-- Integer coordinates when $\mathcal O_K = \mathbb Z[s]$: every algebraic integer is $A + Bs$. -/
theorem int_coords {d : ℤ} {s : K} {θ : 𝓞 K} (hθs : (θ : K) = s) (hs : s ^ 2 = (d : K))
    (hadj : Algebra.adjoin ℤ {θ} = (⊤ : Subalgebra ℤ (𝓞 K))) (z : 𝓞 K) :
    ∃ A B : ℤ, (z : K) = A + B * s := by
  have hz : z ∈ Algebra.adjoin ℤ {θ} := hadj ▸ Algebra.mem_top
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by rw [hx, hθs]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, B, hAB⟩ := hx
    obtain ⟨A', B', hAB'⟩ := hy
    exact ⟨A + A', B + B', by push_cast [hAB, hAB']; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨A, B, hAB⟩ := hx
    obtain ⟨A', B', hAB'⟩ := hy
    refine ⟨A * A' + d * B * B', A * B' + A' * B, ?_⟩
    push_cast [hAB, hAB']
    linear_combination (B * B' : K) * hs

/-- Half-integer coordinates when $\mathcal O_K = \mathbb Z[(1+s)/2]$ ($d = 4c + 1$): every algebraic integer is
$(A + Bs)/2$. -/
theorem half_coords {d c : ℤ} (hc : d = 4 * c + 1) {s : K} {ω : 𝓞 K} (hω : (ω : K) = (1 + s) / 2)
    (hadj : Algebra.adjoin ℤ {ω} = (⊤ : Subalgebra ℤ (𝓞 K))) (hs : s ^ 2 = (d : K)) (z : 𝓞 K) :
    ∃ A B : ℤ, (z : K) = (A + B * s) / 2 := by
  have hz : z ∈ Algebra.adjoin ℤ {ω} := hadj ▸ Algebra.mem_top
  have hω2 : (ω : K) ^ 2 = ω + c := by
    rw [hω]
    have : (d : K) = 4 * c + 1 := by rw [hc]; push_cast; ring
    linear_combination (1 / 4 : K) * hs + (1 / 4 : K) * this
  have key : ∃ k l : ℤ, (z : K) = k + l * ω := by
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by rw [hx]; simp⟩
    | algebraMap r => exact ⟨r, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨A, B, hAB⟩ := hx
      obtain ⟨A', B', hAB'⟩ := hy
      exact ⟨A + A', B + B', by push_cast [hAB, hAB']; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨A, B, hAB⟩ := hx
      obtain ⟨A', B', hAB'⟩ := hy
      refine ⟨A * A' + B * B' * c, A * B' + A' * B + B * B', ?_⟩
      push_cast [hAB, hAB']
      linear_combination (B * B' : K) * hω2
  obtain ⟨k, l, h⟩ := key
  exact ⟨2 * k + l, l, by rw [h, hω]; push_cast; ring⟩

/-- **Fundamental unit, generic form.** If every algebraic integer is $(A + Bs)/2$ with $P(A, B)$, $\varepsilon =
(A_0 + B_0 s)/2$ is a unit with $\varphi(\varepsilon) > 1$, and $(A_0 + B_0\sqrt d)/2 \le (A + B\sqrt d)/2$ for all
$A, B > 0$ with $P(A, B)$ and $A^2 - dB^2 = \pm 4$, then every unit is $\pm\varepsilon^k$. -/
theorem units_generic {d : ℤ} (hd : 0 < d) {s : K} (hK : finrank ℚ K = 2) (hs : s ^ 2 = (d : K))
    (hsq : ¬ IsSquare (d : ℚ)) (φ : K →+* ℝ) (hφ : φ s = Real.sqrt d) (P : ℤ → ℤ → Prop)
    (hcoords : ∀ z : 𝓞 K, ∃ A B : ℤ, P A B ∧ (z : K) = (A + B * s) / 2) (A0 B0 : ℤ)
    (hmin : ∀ A B : ℤ, P A B → 0 < A → 0 < B → (A ^ 2 - d * B ^ 2 = 4 ∨ A ^ 2 - d * B ^ 2 = -4) →
      ((A0 : ℝ) + B0 * Real.sqrt d) / 2 ≤ ((A : ℝ) + B * Real.sqrt d) / 2)
    (ε : (𝓞 K)ˣ) (hε : ((ε : 𝓞 K) : K) = (A0 + B0 * s) / 2)
    (hε1 : 1 < ((A0 : ℝ) + B0 * Real.sqrt d) / 2) (u : (𝓞 K)ˣ) :
    ∃ k : ℤ, u = ε ^ k ∨ u = -ε ^ k := by
  have hval : ∀ A B : ℤ, φ ((A + B * s) / 2) = ((A : ℝ) + B * Real.sqrt d) / 2 := by
    intro A B
    rw [map_div₀, map_add, map_mul, hφ, map_intCast, map_intCast, map_ofNat]
  refine units_eq_of_min φ ε (by rw [hε, hval]; exact hε1) (fun v hv => ?_) u
  obtain ⟨A, B, hP, hAB⟩ := hcoords v
  rw [hAB, hval] at hv
  obtain ⟨hA, hB, hN⟩ := unit_coords hd hK hs hsq φ hφ v A B hAB (by rw [hAB, hval]; exact hv)
  rw [hε, hAB, hval, hval]
  exact hmin A B hP hA hB hN

/-- The norm of $a + bs$ is $a^2 - b^2d$. -/
theorem norm_coords {d : ℤ} {s : K} (hK : finrank ℚ K = 2) (hs : s ^ 2 = (d : K))
    (hsq : ¬ IsSquare (d : ℚ)) (a b : ℚ) :
    Algebra.norm ℚ ((a : K) + (b : K) * s) = a ^ 2 - b ^ 2 * d := by
  rw [← norm_half_coords hK hs hsq a b]
  simp [eq_ratCast]

/-! ## Total reality and the class number -/

theorem nrComplexPlaces_eq_zero (hK : finrank ℚ K = 2) (hΔ : 0 < discr K) : nrComplexPlaces K = 0 := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  have h2 := NumberField.sign_discr K
  rw [Int.sign_eq_one_of_pos hΔ] at h2
  rw [hK] at h1
  rcases Nat.lt_or_ge (nrComplexPlaces K) 1 with h | h
  · omega
  · have : nrComplexPlaces K = 1 := by omega
    rw [this] at h2
    norm_num at h2

theorem isReal_all (hK : finrank ℚ K = 2) (hΔ : 0 < discr K) : ∀ v : InfinitePlace K, v.IsReal :=
  (nrComplexPlaces_eq_zero_iff.mp (nrComplexPlaces_eq_zero hK hΔ)).isReal

theorem classNumber_eq_one_of_discr (hK : finrank ℚ K = 2) (hΔ : 0 < discr K) (h16 : discr K < 16) :
    classNumber K = 1 := by
  rw [classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [nrComplexPlaces_eq_zero hK hΔ, hK]
  have : |(discr K : ℝ)| < 16 := by
    rw [abs_lt]; constructor
    · have : (0 : ℝ) < discr K := by exact_mod_cast hΔ
      linarith
    · exact_mod_cast h16
  norm_num
  linarith

/-- **$d = 6$.** Here $\Delta_K = 24$ and the Minkowski bound is $\sqrt{24}/2 < 3$; the only prime of norm $\le 2$ is
the prime above $2$, which is $(2 + s)$ since $(2 + s)(2 - s) = -2$. -/
theorem classNumber_six (hK : finrank ℚ K = 2) {s : K} (hs : s ^ 2 = ((6 : ℤ) : K))
    (hsq : ¬ IsSquare (((6 : ℤ)) : ℚ)) {θ : 𝓞 K} (hθs : (θ : K) = s) (hΔ : discr K = 24) :
    classNumber K = 1 := by
  rw [classNumber_eq_one_iff]
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
  intro I hIp hIle
  have hΔ' : 0 < discr K := by rw [hΔ]; norm_num
  rw [nrComplexPlaces_eq_zero hK hΔ', hK, hΔ] at hIle
  have hs24 : Real.sqrt 24 < 6 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hle : (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) < 3 := by
    refine lt_of_le_of_lt hIle ?_
    norm_num
    linarith
  have hle' : Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 2 := by
    have : Ideal.absNorm (I : Ideal (𝓞 K)) < 3 := by exact_mod_cast hle
    omega
  have hne0 : Ideal.absNorm (I : Ideal (𝓞 K)) ≠ 0 := Ideal.absNorm_ne_zero_of_nonZeroDivisors I
  have hne1 : Ideal.absNorm (I : Ideal (𝓞 K)) ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hIp.ne_top
  have h2 : Ideal.absNorm (I : Ideal (𝓞 K)) = 2 := by omega
  -- `2 ∈ I` and `2 + θ ∈ I`
  have h2mem : (2 : 𝓞 K) ∈ (I : Ideal (𝓞 K)) := by
    have := Ideal.absNorm_mem (I : Ideal (𝓞 K))
    rw [h2] at this
    exact_mod_cast this
  have hθ2 : θ ^ 2 = 6 := by
    apply RingOfIntegers.coe_injective
    push_cast [hθs, hs]
    rfl
  have hprod : (2 + θ) * (2 - θ) = -2 := by linear_combination -hθ2
  have hmem : 2 + θ ∈ (I : Ideal (𝓞 K)) := by
    have : (2 + θ) * (2 - θ) ∈ (I : Ideal (𝓞 K)) := by
      rw [hprod]; exact (I : Ideal (𝓞 K)).neg_mem h2mem
    rcases hIp.mem_or_mem this with h | h
    · exact h
    · have : 2 + θ = (2 - θ) + 2 * θ := by ring
      rw [this]
      exact Ideal.add_mem _ h (Ideal.mul_mem_right _ _ h2mem)
  -- the norm of `(2 + θ)` is `2`
  have hnorm : Algebra.norm ℤ (2 + θ) = -2 := by
    have h := norm_coords hK hs hsq 2 1
    have hc : (((2 : ℚ) : K) + ((1 : ℚ) : K) * s) = ((2 + θ : 𝓞 K) : K) := by
      have e1 : ((2 + θ : 𝓞 K) : K) = 2 + s := by
        rw [← hθs]; rfl
      rw [e1]; norm_num
    rw [hc, ← Algebra.coe_norm_int] at h
    have : ((Algebra.norm ℤ (2 + θ) : ℤ) : ℚ) = ((-2 : ℤ) : ℚ) := by rw [h]; norm_num
    exact_mod_cast this
  set J : Ideal (𝓞 K) := Ideal.span {2 + θ}
  have hJ : Ideal.absNorm J = 2 := by
    simp only [J, Ideal.absNorm_span_singleton, hnorm]
    rfl
  have hJp : J.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hJ]; exact Nat.prime_two)
  have hJne : J ≠ ⊥ := by
    intro h; rw [h, Ideal.absNorm_bot] at hJ; norm_num at hJ
  have hJmax : J.IsMaximal := hJp.isMaximal hJne
  have hJI : J ≤ (I : Ideal (𝓞 K)) := (Ideal.span_singleton_le_iff_mem _).mpr hmem
  have hEq : J = (I : Ideal (𝓞 K)) := hJmax.eq_of_le hIp.ne_top hJI
  exact ⟨⟨2 + θ, hEq.symm⟩⟩

/-! ## The rows of the table -/

/-- Fundamental unit when $\mathcal O_K = \mathbb Z[s]$. -/
theorem fundamental_int {d : ℤ} (hd : 0 < d) {s : K} (hK : finrank ℚ K = 2) (hs : s ^ 2 = (d : K))
    (hsq : ¬ IsSquare (d : ℚ)) {θ : 𝓞 K} (hθs : (θ : K) = s)
    (hadj : Algebra.adjoin ℤ {θ} = (⊤ : Subalgebra ℤ (𝓞 K))) (a0 b0 e : ℤ)
    (he : a0 ^ 2 - d * b0 ^ 2 = e) (he1 : e = 1 ∨ e = -1) (hε1 : 1 < (a0 : ℝ) + b0 * Real.sqrt d)
    (hmin : ∀ a b : ℤ, 0 < a → 0 < b → (a ^ 2 - d * b ^ 2 = 1 ∨ a ^ 2 - d * b ^ 2 = -1) →
      (a0 : ℝ) + b0 * Real.sqrt d ≤ a + b * Real.sqrt d) :
    ∃ ε : (𝓞 K)ˣ, ((ε : 𝓞 K) : K) = a0 + b0 * s ∧ ∀ u : (𝓞 K)ˣ, ∃ k : ℤ, u = ε ^ k ∨ u = -ε ^ k := by
  have hθ2 : θ ^ 2 = d := by
    apply RingOfIntegers.coe_injective
    push_cast [hθs, hs]
    rfl
  have hee : e * e = 1 := by rcases he1 with rfl | rfl <;> norm_num
  have hxy : (a0 + b0 * θ) * (e * (a0 - b0 * θ)) = 1 := by
    have : ((a0 : 𝓞 K) + b0 * θ) * (a0 - b0 * θ) = e := by
      rw [← he]; push_cast; linear_combination (-(b0 : 𝓞 K) ^ 2) * hθ2
    calc _ = ((a0 : 𝓞 K) + b0 * θ) * (a0 - b0 * θ) * e := by ring
      _ = 1 := by rw [this]; exact_mod_cast hee
  let ε : (𝓞 K)ˣ := ⟨a0 + b0 * θ, e * (a0 - b0 * θ), hxy, by rw [mul_comm]; exact hxy⟩
  have hεv : ((ε : 𝓞 K) : K) = a0 + b0 * s := by
    show (((a0 : 𝓞 K) + b0 * θ : 𝓞 K) : K) = _
    push_cast [hθs]; rfl
  obtain ⟨φ, hφ⟩ := exists_embedding hK hd hs hsq
  refine ⟨ε, hεv, units_generic hd hK hs hsq φ hφ (fun A B => Even A ∧ Even B) ?_ (2 * a0) (2 * b0)
    ?_ ε ?_ ?_⟩
  · intro z
    obtain ⟨A, B, h⟩ := int_coords hθs hs hadj z
    exact ⟨2 * A, 2 * B, ⟨even_two_mul A, even_two_mul B⟩, by rw [h]; push_cast; ring⟩
  · rintro A B ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ hA hB hN
    have h := hmin a b (by omega) (by omega) (by rcases hN with h | h <;> [left; right] <;> nlinarith)
    push_cast
    linarith
  · rw [hεv]; push_cast; ring
  · push_cast; linarith

theorem sqrt_bounds (d : ℝ) (hd : 0 ≤ d) : Real.sqrt d ^ 2 = d ∧ 0 ≤ Real.sqrt d :=
  ⟨Real.sq_sqrt hd, Real.sqrt_nonneg d⟩

/-- Common data for $d \in \{2, 3, 6\}$ ($d \not\equiv 1 \bmod 4$). -/
theorem data_int {d : ℕ} (hd : 0 < d) (hsf : Squarefree d) (hd4 : (d : ℤ) % 4 ≠ 1)
    (hsq : ¬ IsSquare ((d : ℤ) : ℚ)) (hK : finrank ℚ K = 2) {s : K} (hs : s ^ 2 = ((d : ℤ) : K)) :
    ∃ θ : 𝓞 K, (θ : K) = s ∧ minpoly ℤ θ = X ^ 2 - C (d : ℤ) ∧ Algebra.adjoin ℚ {(θ : K)} = ⊤ ∧
      Algebra.adjoin ℤ {θ} = (⊤ : Subalgebra ℤ (𝓞 K)) ∧ discr K = 4 * d := by
  obtain ⟨θ, hθs, hmin, hgen⟩ := exists_gen hK hs hsq
  have hsf' : Squarefree (d : ℤ) := squarefree_int hsf
  exact ⟨θ, hθs, hmin, hgen, adjoin_gen_eq_top_of_mod_four_ne_one hmin hgen hsf' hd4,
    discr_eq_four_mul_of_mod_four_ne_one hmin hgen hsf' hd4⟩

theorem not_isSquare_int {d : ℕ} (hd : d ∈ ({2, 3, 5, 6} : Finset ℕ)) : ¬ IsSquare ((d : ℕ) : ℤ) := by
  rintro ⟨r, hr⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  have h6 : (d : ℤ) ≤ 6 := by rcases hd with rfl | rfl | rfl | rfl <;> norm_num
  have : r ≤ 3 := by nlinarith
  have : -3 ≤ r := by nlinarith
  rcases hd with rfl | rfl | rfl | rfl <;> (push_cast at hr; interval_cases r <;> omega)

/-- The value $a + bs$ with integer $a, b$, as rationals. -/
theorem val_cast (a b : ℤ) (s : K) : ((a : ℚ) : K) + ((b : ℚ) : K) * s = (a : K) + (b : K) * s := by
  push_cast; rfl

theorem row2 (hK : finrank ℚ K = 2) {s : K} (hs : s ^ 2 = ((2 : ℤ) : K)) :
    classNumber K = 1 ∧
      (∃ ε : (𝓞 K)ˣ, ((ε : 𝓞 K) : K) = ((1 : ℚ) : K) + ((1 : ℚ) : K) * s ∧
        Algebra.norm ℚ ((ε : 𝓞 K) : K) = ((-1 : ℤ) : ℚ) ∧
        ∀ u : (𝓞 K)ˣ, ∃ k : ℤ, u = ε ^ k ∨ u = -ε ^ k) ∧
      (Nat.card (RayClassGroup (narrowModulus K)) : ℤ) = 1 := by
  have hsq : ¬ IsSquare (((2 : ℕ) : ℤ) : ℚ) := by
    rw [Rat.isSquare_intCast_iff]
    exact not_isSquare_int (by norm_num)
  obtain ⟨θ, hθs, hmin, hgen, hadj, hΔ⟩ := data_int (d := 2) (by norm_num)
    Nat.prime_two.prime.squarefree (by decide) hsq hK
    (by exact_mod_cast hs)
  have hΔ' : discr K = 8 := by rw [hΔ]; norm_num
  have hcl : classNumber K = 1 :=
    classNumber_eq_one_of_discr hK (by rw [hΔ']; norm_num) (by rw [hΔ']; norm_num)
  have hs' : s ^ 2 = (((2 : ℕ) : ℤ) : K) := by exact_mod_cast hs
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ (((2 : ℕ) : ℤ) : ℝ) by norm_num)
  have h2' := Real.sqrt_nonneg (((2 : ℕ) : ℤ) : ℝ)
  obtain ⟨ε, hεv, hgenε⟩ := fundamental_int (by norm_num) hK hs' hsq hθs hadj 1 1 (-1) (by norm_num)
    (Or.inr rfl) (by push_cast at h2 h2' ⊢; nlinarith) (by
      intro a b ha hb _
      have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
      push_cast at h2 h2' ⊢
      nlinarith)
  have hnorm : Algebra.norm ℚ ((ε : 𝓞 K) : K) = -1 := by
    have := norm_coords hK hs' hsq 1 1
    rw [hεv]
    push_cast at this ⊢
    rw [this]; norm_num
  refine ⟨hcl, ⟨ε, by rw [hεv]; push_cast; ring, by rw [hnorm]; norm_num, hgenε⟩, ?_⟩
  rw [(example_1_8b_quadratic hK (isReal_all hK (by rw [hΔ']; norm_num))).2 ⟨ε, hnorm⟩, hcl]
  rfl

theorem squarefree_six : Squarefree (6 : ℕ) := by
  have : (6 : ℕ) = 2 * 3 := by norm_num
  rw [this, Nat.squarefree_mul_iff]
  exact ⟨by norm_num, Nat.prime_two.prime.squarefree, Nat.prime_three.prime.squarefree⟩

/-- All units have norm $1$ when $3 \mid d$. -/
theorem norm_units_one {d : ℤ} {θ : 𝓞 K} (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) (h3 : (3 : ℤ) ∣ d) (u : (𝓞 K)ˣ) :
    Algebra.norm ℚ ((u : 𝓞 K) : K) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases norm_unit u with h | h
  · exact h
  · exact absurd h (TauCeti.NumberField.norm_ne_neg_one_of_prime_dvd hmin hgen hsf (p := 3)
      (by norm_num) (by exact_mod_cast h3) (u : 𝓞 K))

theorem row3 (hK : finrank ℚ K = 2) {s : K} (hs : s ^ 2 = ((3 : ℤ) : K)) :
    classNumber K = 1 ∧
      (∃ ε : (𝓞 K)ˣ, ((ε : 𝓞 K) : K) = ((2 : ℚ) : K) + ((1 : ℚ) : K) * s ∧
        Algebra.norm ℚ ((ε : 𝓞 K) : K) = ((1 : ℤ) : ℚ) ∧
        ∀ u : (𝓞 K)ˣ, ∃ k : ℤ, u = ε ^ k ∨ u = -ε ^ k) ∧
      (Nat.card (RayClassGroup (narrowModulus K)) : ℤ) = 2 := by
  have hsq : ¬ IsSquare (((3 : ℕ) : ℤ) : ℚ) := by
    rw [Rat.isSquare_intCast_iff]
    exact not_isSquare_int (by decide)
  obtain ⟨θ, hθs, hmin, hgen, hadj, hΔ⟩ := data_int (d := 3) (by norm_num)
    Nat.prime_three.prime.squarefree (by decide) hsq hK (by exact_mod_cast hs)
  have hΔ' : discr K = 12 := by rw [hΔ]; norm_num
  have hcl : classNumber K = 1 :=
    classNumber_eq_one_of_discr hK (by rw [hΔ']; norm_num) (by rw [hΔ']; norm_num)
  have hs' : s ^ 2 = (((3 : ℕ) : ℤ) : K) := by exact_mod_cast hs
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ (((3 : ℕ) : ℤ) : ℝ) by norm_num)
  have h2' := Real.sqrt_nonneg (((3 : ℕ) : ℤ) : ℝ)
  push_cast at h2 h2'
  have h1 : (1 : ℝ) ≤ Real.sqrt 3 := by nlinarith
  obtain ⟨ε, hεv, hgenε⟩ := fundamental_int (by norm_num) hK hs' hsq hθs hadj 2 1 1 (by norm_num)
    (Or.inl rfl) (by push_cast; nlinarith) (by
      intro a b ha hb hN
      push_cast at hN ⊢
      have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
      rcases (show 2 ≤ a ∨ 2 ≤ b by
        by_contra hc
        push Not at hc
        have : a = 1 := by omega
        have : b = 1 := by omega
        subst a b
        norm_num at hN) with h | h
      · have : (2 : ℝ) ≤ a := by exact_mod_cast h
        nlinarith
      · have : (2 : ℝ) ≤ b := by exact_mod_cast h
        nlinarith)
  have hnorm : Algebra.norm ℚ ((ε : 𝓞 K) : K) = 1 :=
    norm_units_one hmin hgen (squarefree_int Nat.prime_three.prime.squarefree) (by norm_num) ε
  refine ⟨hcl, ⟨ε, by rw [hεv]; push_cast; ring, by rw [hnorm]; norm_num, hgenε⟩, ?_⟩
  rw [(example_1_8b_quadratic hK (isReal_all hK (by rw [hΔ']; norm_num))).1
    (norm_units_one hmin hgen (squarefree_int Nat.prime_three.prime.squarefree) (by norm_num)), hcl]
  rfl

theorem row6 (hK : finrank ℚ K = 2) {s : K} (hs : s ^ 2 = ((6 : ℤ) : K)) :
    classNumber K = 1 ∧
      (∃ ε : (𝓞 K)ˣ, ((ε : 𝓞 K) : K) = ((5 : ℚ) : K) + ((2 : ℚ) : K) * s ∧
        Algebra.norm ℚ ((ε : 𝓞 K) : K) = ((1 : ℤ) : ℚ) ∧
        ∀ u : (𝓞 K)ˣ, ∃ k : ℤ, u = ε ^ k ∨ u = -ε ^ k) ∧
      (Nat.card (RayClassGroup (narrowModulus K)) : ℤ) = 2 := by
  have hsq : ¬ IsSquare (((6 : ℕ) : ℤ) : ℚ) := by
    rw [Rat.isSquare_intCast_iff]
    exact not_isSquare_int (by decide)
  obtain ⟨θ, hθs, hmin, hgen, hadj, hΔ⟩ := data_int (d := 6) (by norm_num)
    squarefree_six (by decide) hsq hK (by exact_mod_cast hs)
  have hΔ' : discr K = 24 := by rw [hΔ]; norm_num
  have hcl : classNumber K = 1 :=
    classNumber_six hK hs (by exact_mod_cast hsq) hθs hΔ'
  have hs' : s ^ 2 = (((6 : ℕ) : ℤ) : K) := by exact_mod_cast hs
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ (((6 : ℕ) : ℤ) : ℝ) by norm_num)
  have h2' := Real.sqrt_nonneg (((6 : ℕ) : ℤ) : ℝ)
  push_cast at h2 h2'
  have h1 : (2 : ℝ) ≤ Real.sqrt 6 := by nlinarith
  obtain ⟨ε, hεv, hgenε⟩ := fundamental_int (by norm_num) hK hs' hsq hθs hadj 5 2 1 (by norm_num)
    (Or.inl rfl) (by push_cast; nlinarith) (by
      intro a b ha hb hN
      push_cast at hN ⊢
      have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
      by_cases hb4 : 4 ≤ b
      · have : (4 : ℝ) ≤ b := by exact_mod_cast hb4
        nlinarith
      · have hb3 : b ≤ 3 := by omega
        have ha7 : a ≤ 7 := by rcases hN with h | h <;> nlinarith
        interval_cases b <;> interval_cases a <;> first | (exfalso; norm_num at hN; done) | norm_num)
  have hsf6 := squarefree_int squarefree_six
  have hnorm : Algebra.norm ℚ ((ε : 𝓞 K) : K) = 1 :=
    norm_units_one hmin hgen hsf6 (by norm_num) ε
  refine ⟨hcl, ⟨ε, by rw [hεv]; push_cast; ring, by rw [hnorm]; norm_num, hgenε⟩, ?_⟩
  rw [(example_1_8b_quadratic hK (isReal_all hK (by rw [hΔ']; norm_num))).1
    (norm_units_one hmin hgen hsf6 (by norm_num)), hcl]
  rfl

theorem row5 (hK : finrank ℚ K = 2) {s : K} (hs : s ^ 2 = ((5 : ℤ) : K)) :
    classNumber K = 1 ∧
      (∃ ε : (𝓞 K)ˣ, ((ε : 𝓞 K) : K) = ((1 / 2 : ℚ) : K) + ((1 / 2 : ℚ) : K) * s ∧
        Algebra.norm ℚ ((ε : 𝓞 K) : K) = ((-1 : ℤ) : ℚ) ∧
        ∀ u : (𝓞 K)ˣ, ∃ k : ℤ, u = ε ^ k ∨ u = -ε ^ k) ∧
      (Nat.card (RayClassGroup (narrowModulus K)) : ℤ) = 1 := by
  have hsq : ¬ IsSquare ((5 : ℤ) : ℚ) := by
    rw [Rat.isSquare_intCast_iff]
    exact not_isSquare_int (d := 5) (by decide)
  obtain ⟨θ, hθs, hmin, hgen⟩ := exists_gen hK hs hsq
  have hsf : Squarefree (5 : ℤ) := squarefree_int (d := 5) Nat.prime_five.prime.squarefree
  have hd4 : (5 : ℤ) % 4 = 1 := by norm_num
  set ω := halfGen hmin hd4
  have hω : (ω : K) = (1 + s) / 2 := by rw [coe_halfGen, hθs]
  have hadj := adjoin_halfGen_eq_top_of_mod_four_eq_one hmin hgen hsf hd4
  have hΔ : discr K = 5 := discr_eq_of_squarefree_of_mod_four_eq_one hmin hgen hsf hd4
  have hcl : classNumber K = 1 :=
    classNumber_eq_one_of_discr hK (by rw [hΔ]; norm_num) (by rw [hΔ]; norm_num)
  have hωω : ω * (ω - 1) = 1 := by
    apply RingOfIntegers.coe_injective
    show ((ω * (ω - 1) : 𝓞 K) : K) = ((1 : 𝓞 K) : K)
    push_cast
    have key : ∀ x : K, x = (1 + s) / 2 → x * (x - 1) = 1 := by
      intro x hx
      rw [hx]
      have h5 : ((5 : ℤ) : K) = 5 := by norm_num
      linear_combination (1 / 4 : K) * hs + (1 / 4 : K) * h5
    exact key _ hω
  let ε : (𝓞 K)ˣ := ⟨ω, ω - 1, hωω, by rw [mul_comm]; exact hωω⟩
  have hεv : ((ε : 𝓞 K) : K) = (((1 : ℤ) : K) + ((1 : ℤ) : K) * s) / 2 := by
    show (ω : K) = _
    rw [hω]; push_cast; ring
  obtain ⟨φ, hφ⟩ := exists_embedding hK (by norm_num) hs hsq
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ ((5 : ℤ) : ℝ) by norm_num)
  have h2' := Real.sqrt_nonneg ((5 : ℤ) : ℝ)
  have hgenε := units_generic (d := 5) (by norm_num) hK hs hsq φ hφ (fun _ _ => True)
    (fun z => by
      obtain ⟨A, B, h⟩ := half_coords (c := 1) (by norm_num) hω hadj hs z
      exact ⟨A, B, trivial, h⟩) 1 1 (by
      intro A B _ hA hB _
      have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
      have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
      push_cast at h2' ⊢
      nlinarith) ε hεv (by push_cast at h2 h2' ⊢; nlinarith)
  have hnorm : Algebra.norm ℚ ((ε : 𝓞 K) : K) = -1 := by
    have := norm_coords hK hs hsq (1 / 2) (1 / 2)
    have e : ((ε : 𝓞 K) : K) = ((1 / 2 : ℚ) : K) + ((1 / 2 : ℚ) : K) * s := by
      rw [hεv]; push_cast; ring
    rw [e, this]; norm_num
  refine ⟨hcl, ⟨ε, by rw [hεv]; push_cast; ring, by rw [hnorm]; norm_num, hgenε⟩, ?_⟩
  rw [(example_1_8b_quadratic hK (isReal_all hK (by rw [hΔ]; norm_num))).2 ⟨ε, hnorm⟩, hcl]
  rfl

end NumberFieldKB.MilneCFT.Ex18b

namespace NumberFieldKB.MilneCFT

open Ex18b in
/-- **Example 1.8 (b), the table** (Milne, *CFT*, V, Example 1.8(b), p. 151), unconditionally: class numbers,
fundamental units with their norms, and narrow class numbers of $\mathbb Q(\sqrt d)$ for $d = 2, 3, 5, 6$. -/
@[kb "milne2020cft" "Ch. V, Example 1.8(b) (the table for d = 2, 3, 5, 6)"]
theorem example_1_8b_table : Example1_8b_table := by
  refine ⟨fun K _ _ d s hK hs a b n hn hmem => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact row2 hK hs
  · exact row3 hK hs
  · exact row5 hK hs
  · exact row6 hK hs

end NumberFieldKB.MilneCFT
