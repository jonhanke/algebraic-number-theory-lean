import NumberFieldKB.ModularCurves.ComplexQExp
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Quotients of $q$-expansions vanishing at $i\infty$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, Proposition 3.3 and Corollary 3.4 (pdf p. 199): the analytic
step at the cusps for the converse of Corollary 3.4. If $F\,B = A$ on $\mathbb H$, where $A, B$ have $q$-expansions,
$B \ne 0$, and $\operatorname{ord}_q \hat A \ge \operatorname{ord}_q \hat B + 1$, then $F \to 0$ at $i\infty$
(`isZeroAtImInfty_of_mul_eq`). Proof: $A = q^{k+1} t_A$, $B = q^k t_B$ with $t_A, t_B$ given by $q$-series
(`HasSum.exists_hasSum_smul_of_apply_eq_zero`), $t_B \to b_k \ne 0$, so $F = q\, t_A/t_B \to 0$.
-/

open UpperHalfPlane hiding I
open Filter Topology
open scoped WithZero

noncomputable section

local notation "𝕢" => Function.Periodic.qParam

namespace NumberFieldKB.ModularCurves

/-- **A quotient of $q$-expansions with a zero of order $\ge 1$ tends to $0$ at $i\infty$.** -/
theorem isZeroAtImInfty_of_mul_eq {A B F : ℍ → ℂ} (hA : IsQExp A) (hB : IsQExp B) (hB0 : qHat B ≠ 0)
    (hFB : ∀ z, F z * B z = A z)
    (hv : Valued.v (qHat A) ≤ WithZero.exp (-1 : ℤ) * Valued.v (qHat B)) : IsZeroAtImInfty F := by
  classical
  have hex : ∃ n, (qExpansion 1 B).coeff n ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hB0
    have : qExpansion 1 B = 0 := by ext n; simp [hcon n]
    simp [qHat, this]
  set k := Nat.find hex with hk
  have hk1 : (qExpansion 1 B).coeff k ≠ 0 := Nat.find_spec hex
  have hk2 : ∀ i < k, (qExpansion 1 B).coeff i = 0 := fun i hi => by
    have := Nat.find_min hex hi
    simpa using this
  have hvB := valuation_ofPowerSeries hk1 hk2
  have hvB' : Valued.v (qHat B) = WithZero.exp (-(k : ℤ)) := hvB
  have hv' : Valued.v (qHat A) ≤ WithZero.exp (-((k + 1 : ℕ) : ℤ)) := by
    rw [hvB'] at hv
    refine hv.trans (le_of_eq ?_)
    rw [← WithZero.exp_add]
    congr 1
    push_cast; ring
  rw [LaurentSeries.valuation_le_iff_coeff_lt_eq_zero] at hv'
  have hA0 : ∀ i < k + 1, (qExpansion 1 A).coeff i = 0 := by
    intro i hi
    have := hv' (i : ℤ) (by exact_mod_cast hi)
    rwa [qHat, HahnSeries.ofPowerSeries_apply_coeff] at this
  have hsA := fun τ => hasSum_qExpansion (h := 1) one_pos hA.periodic hA.mdiff hA.bounded τ
  have hsB := fun τ => hasSum_qExpansion (h := 1) one_pos hB.periodic hB.mdiff hB.bounded τ
  have key : ∀ τ : ℍ, ∃ tA tB : ℂ, A τ = 𝕢 1 τ ^ (k + 1) * tA ∧ B τ = 𝕢 1 τ ^ k * tB ∧
      HasSum (fun m : ℕ => (qExpansion 1 A).coeff (m + (k + 1)) • 𝕢 1 τ ^ m) tA ∧
      HasSum (fun m : ℕ => (qExpansion 1 B).coeff (m + k) • 𝕢 1 τ ^ m) tB := by
    intro τ
    obtain ⟨tA, h1, h2⟩ := HasSum.exists_hasSum_smul_of_apply_eq_zero
      (z := 𝕢 1 τ) (n := k + 1) (a := fun m => (qExpansion 1 A).coeff m)
      (by simpa [smul_eq_mul, mul_comm] using hsA τ) hA0
    obtain ⟨tB, h3, h4⟩ := HasSum.exists_hasSum_smul_of_apply_eq_zero
      (z := 𝕢 1 τ) (n := k) (a := fun m => (qExpansion 1 B).coeff m)
      (by simpa [smul_eq_mul, mul_comm] using hsB τ) hk2
    refine ⟨tA, tB, ?_, ?_, ?_, ?_⟩
    · rw [← h1]; simp
    · rw [← h3]; simp
    · simpa [smul_eq_mul, mul_comm] using h2
    · simpa [smul_eq_mul, mul_comm] using h4
  choose tA tB hAe hBe hsA' hsB' using key
  have hTA : Tendsto tA atImInfty (𝓝 ((qExpansion 1 A).coeff (k + 1))) := by
    have := tendsto_atImInfty_of_hasSum_qExpansion (h := 1) (f := tA)
      (c := fun m => (qExpansion 1 A).coeff (m + (k + 1))) one_pos hsA'
    simpa using this
  have hTB : Tendsto tB atImInfty (𝓝 ((qExpansion 1 B).coeff k)) := by
    have := tendsto_atImInfty_of_hasSum_qExpansion (h := 1) (f := tB)
      (c := fun m => (qExpansion 1 B).coeff (m + k)) one_pos hsB'
    simpa using this
  have hq := qParam_tendsto_atImInfty (h := 1) one_pos
  have hlim : Tendsto (fun τ : ℍ => 𝕢 1 τ * tA τ / tB τ) atImInfty (𝓝 0) := by
    have h := (hq.mul hTA).div hTB hk1
    have h0 : (0 : ℂ) * (qExpansion 1 A).coeff (k + 1) / (qExpansion 1 B).coeff k = 0 := by simp
    rw [h0] at h
    exact h
  refine hlim.congr' ?_
  filter_upwards [hTB.eventually_ne hk1] with τ hτ
  have hq0 : 𝕢 1 τ ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hBne : B τ ≠ 0 := by rw [hBe τ]; exact mul_ne_zero (pow_ne_zero _ hq0) hτ
  have := hFB τ
  rw [hAe τ, hBe τ] at this
  rw [div_eq_iff hτ]
  refine mul_left_cancel₀ (pow_ne_zero k hq0) ?_
  linear_combination -this

end NumberFieldKB.ModularCurves
