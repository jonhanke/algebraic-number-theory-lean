import NumberFieldKB.PNTPort.StrongPNT
import NumberFieldKB.MilneCFT.Ch6.Remark42aDirichlet
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Milne, *Class Field Theory*, VI, Remark 4.2 (a), unconditionally: the error-term prime number theorem

This file proves the named input `R42.PNTError` (`pntError`),
$$|\pi(x) - x/\log x| \le C\,x/\log^2 x\qquad(x\ge2),$$
and hence `Remark4_2a` (`remark_4_2a`, both halves) without hypotheses.

Route (partial summation from $\psi$ through $\theta$):
1. **Strong prime number theorem** (`NumberFieldKB.PNTPort.StrongPNT`, ported from PrimeNumberTheoremAnd):
   $\psi(x) - x = O(x e^{-c\sqrt{\log x}})$ for some $c > 0$.
2. $\psi(x) - \theta(x) = O(\sqrt x)$ (Mathlib `Chebyshev.isBigO_psi_sub_theta_sqrt`), and both $x e^{-c\sqrt{\log x}}$
   and $\sqrt x$ are $O(x/\log x)$, so $\theta(x) - x = O(x/\log x)$ (`theta_sub_isBigO`).
3. Abel summation (Mathlib `Chebyshev.primeCounting_sub_theta_div_log_isBigO`):
   $\pi(x) - \theta(x)/\log x = O(x/\log^2 x)$; with step 2, $\pi(x) - x/\log x = O(x/\log^2 x)$
   (`primeCounting_sub_isBigO`).
4. The asymptotic bound becomes a bound for all $x \ge 2$ since both sides are bounded on compact ranges
   (`pntError`), after identifying `MilneANT.primeCount` over $\mathbb Q$ with `Nat.primeCounting`
   (`primeCount_univ_eq`).

The stronger form $\pi(x) = \mathrm{li}(x) + O(x e^{-c\sqrt{\log x}})$ is not needed: `R42.PNTError` is stated with the
main term $x/\log x$, which is what the proof of Remark 4.2 (a) uses.
-/

open Filter Asymptotics Real IsDedekindDomain NumberField
open scoped Chebyshev

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch6.R42

/-- Over $\mathbb Q$, the number of primes of norm at most $x$ is $\pi(\lfloor x\rfloor)$. -/
theorem primeCount_univ_eq (x : ℝ) :
    NumberFieldKB.MilneANT.primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))) x =
      Nat.primeCounting ⌊x⌋₊ := by
  classical
  rw [← Nat.primesLE_card_eq_primeCounting, NumberFieldKB.MilneANT.primeCount, ← Set.ncard_coe_finset]
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm v.asIdeal)
      {v | v ∈ Set.univ ∧ (Ideal.absNorm v.asIdeal : ℝ) ≤ x} := by
    intro v _ w _ h
    apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
    apply Subtype.ext
    simp only [Rat.HeightOneSpectrum.absNorm_asIdeal] at h
    exact h
  rw [← hinj.ncard_image]
  congr 1
  ext p
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_univ, true_and, Finset.mem_coe,
    Nat.mem_primesLE]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hp : (Ideal.absNorm v.asIdeal).Prime := by
      rw [Rat.HeightOneSpectrum.absNorm_asIdeal]
      exact Rat.HeightOneSpectrum.prime_natGenerator v
    exact ⟨(Nat.le_floor_iff' hp.ne_zero).mpr hv, hp⟩
  · rintro ⟨hle, hp⟩
    obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
    exact ⟨v, by rw [hv]; exact (Nat.le_floor_iff' hp.ne_zero).mp hle, hv⟩

/-- $\log x = O(e^{c\sqrt{\log x}})$ for $c > 0$. -/
theorem log_isBigO_exp_sqrt_log {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => Real.log x) =O[atTop] fun x => Real.exp (c * Real.log x ^ ((1 : ℝ) / 2)) := by
  have hu : Tendsto (fun x : ℝ => Real.log x ^ ((1 : ℝ) / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  have h := ((isLittleO_pow_exp_pos_mul_atTop 2 hc).comp_tendsto hu).isBigO
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  simp only [Function.comp_apply]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hl]
  norm_num

/-- $x e^{-c\sqrt{\log x}} = O(x/\log x)$ for $c > 0$. -/
theorem strong_error_isBigO {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 2))) =O[atTop] fun x => x / Real.log x := by
  have h := (log_isBigO_exp_sqrt_log hc).inv_rev (by
    filter_upwards [eventually_gt_atTop 1] with x hx h0
    exact absurd h0 (Real.log_pos hx).ne')
  have h2 := (isBigO_refl (fun x : ℝ => x) atTop).mul h
  refine h2.congr (fun x => ?_) (fun x => ?_)
  · simp only [neg_mul, Real.exp_neg]
  · simp only [div_eq_mul_inv]

/-- $\sqrt x = O(x/\log x)$. -/
theorem sqrt_isBigO_div_log : (fun x : ℝ => Real.sqrt x) =O[atTop] fun x => x / Real.log x := by
  have h1 : (fun x : ℝ => Real.log x) =O[atTop] fun x => Real.sqrt x := by
    refine (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).isBigO.congr_right ?_
    intro x
    rw [Real.sqrt_eq_rpow]
  have h := h1.inv_rev (by
    filter_upwards [eventually_gt_atTop 1] with x hx h0
    exact absurd h0 (Real.log_pos hx).ne')
  have h2 := (isBigO_refl (fun x : ℝ => x) atTop).mul h
  refine h2.congr' ?_ (Eventually.of_forall fun x => by simp only [div_eq_mul_inv])
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  rw [inv_eq_one_div, mul_one_div, div_eq_iff hs.ne', Real.mul_self_sqrt hx.le]

/-- **Chebyshev's $\theta$ from the strong prime number theorem**: $\theta(x) - x = O(x/\log x)$. -/
theorem theta_sub_isBigO :
    (fun x : ℝ => θ x - x) =O[atTop] fun x => x / Real.log x := by
  obtain ⟨c, hc, h⟩ := NumberFieldKB.PNTPort.StrongPNT
  have h1 : (fun x : ℝ => ψ x - x) =O[atTop] fun x => x / Real.log x :=
    (h.trans (strong_error_isBigO hc)).congr_left fun x => by simp [NumberFieldKB.PNTPort.ChebyshevPsi]
  have h2 : (fun x : ℝ => ψ x - θ x) =O[atTop] fun x => x / Real.log x :=
    Chebyshev.isBigO_psi_sub_theta_sqrt.trans sqrt_isBigO_div_log
  exact (h1.sub h2).congr_left fun x => by ring

/-- $\pi(x) - x/\log x = O(x/\log^2 x)$. -/
theorem primeCounting_sub_isBigO :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x) =O[atTop]
      fun x => x / Real.log x ^ 2 := by
  have h1 := Chebyshev.primeCounting_sub_theta_div_log_isBigO
  have h2 : (fun x : ℝ => (θ x - x) * (Real.log x)⁻¹) =O[atTop] fun x => x / Real.log x ^ 2 :=
    (theta_sub_isBigO.mul (isBigO_refl (fun x : ℝ => (Real.log x)⁻¹) atTop)).congr_right fun x => by ring
  exact (h1.add h2).congr_left fun x => by ring

/-- An $O(x/\log^2 x)$ bound at infinity for a function bounded on compact ranges is a bound on $[2,\infty)$. -/
theorem bound_of_isBigO {f : ℝ → ℝ} (hf : f =O[atTop] fun x => x / Real.log x ^ 2)
    (hb : ∀ X : ℝ, ∃ B : ℝ, ∀ x, 2 ≤ x → x ≤ X → |f x| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → |f x| ≤ C * x / Real.log x ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := hf.bound
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hC₀
  set X := max X₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  obtain ⟨B, hB⟩ := hb X
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 2 le_rfl hX2)
  have hlX : 0 < Real.log X := Real.log_pos (by linarith)
  refine ⟨max C₀ 0 + B * Real.log X ^ 2 / 2, by positivity, fun x hx => ?_⟩
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hg : 0 ≤ x / Real.log x ^ 2 := by positivity
  have hsplit : (max C₀ 0 + B * Real.log X ^ 2 / 2) * x / Real.log x ^ 2 =
      max C₀ 0 * (x / Real.log x ^ 2) + B * Real.log X ^ 2 / 2 * (x / Real.log x ^ 2) := by ring
  rw [hsplit]
  rcases le_or_gt X x with hxX | hxX
  · have h := hX₀ x ((le_max_left _ _).trans hxX)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hg] at h
    have : C₀ * (x / Real.log x ^ 2) ≤ max C₀ 0 * (x / Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hg
    have : 0 ≤ B * Real.log X ^ 2 / 2 * (x / Real.log x ^ 2) := by positivity
    have : 0 ≤ max C₀ 0 * (x / Real.log x ^ 2) := by positivity
    linarith
  · have h := hB x hx hxX.le
    have hlx : Real.log x ≤ Real.log X := Real.log_le_log (by linarith) hxX.le
    have key : 1 ≤ Real.log X ^ 2 / 2 * (x / Real.log x ^ 2) := by
      rw [div_mul_div_comm, le_div_iff₀ (by positivity), one_mul]
      have : Real.log x ^ 2 ≤ Real.log X ^ 2 := pow_le_pow_left₀ hl.le hlx 2
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg (Real.log X))]
    have : B ≤ B * Real.log X ^ 2 / 2 * (x / Real.log x ^ 2) := by
      have := mul_le_mul_of_nonneg_left key hB0
      linarith [show B * (Real.log X ^ 2 / 2 * (x / Real.log x ^ 2)) =
        B * Real.log X ^ 2 / 2 * (x / Real.log x ^ 2) by ring]
    have : 0 ≤ max C₀ 0 * (x / Real.log x ^ 2) := by positivity
    linarith

/-- **The prime number theorem with error term** (`R42.PNTError`), unconditionally: from the ported strong prime
number theorem (`NumberFieldKB.PNTPort.StrongPNT`) by partial summation through $\theta$. -/
@[kb "milne2020cft" "Ch. VI, Remark 4.2 (a) (prime number theorem with error term, proved)"]
theorem pntError : PNTError := by
  obtain ⟨C, hC, hbound⟩ := bound_of_isBigO primeCounting_sub_isBigO fun X => by
    refine ⟨Nat.primeCounting ⌊X⌋₊ + X / Real.log 2, fun x hx hxX => ?_⟩
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have hpi : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ Nat.primeCounting ⌊X⌋₊ := by
      exact_mod_cast Nat.monotone_primeCounting (Nat.floor_le_floor hxX)
    have hdiv : x / Real.log x ≤ X / Real.log 2 :=
      div_le_div₀ (by linarith) hxX hl2 hlx
    have hdiv0 : 0 ≤ x / Real.log x := div_nonneg (by linarith) (by linarith)
    rw [abs_le]
    constructor <;> linarith [(Nat.cast_nonneg (Nat.primeCounting ⌊x⌋₊) : (0 : ℝ) ≤ _)]
  exact ⟨⟨C, hC, fun x hx => by rw [primeCount_univ_eq]; exact hbound x hx⟩⟩

end NumberFieldKB.MilneCFT.Ch6.R42

namespace NumberFieldKB.MilneCFT.Ch6

/-- **Remark 4.2 (a)** (Milne, *CFT*, VI, p. 194), unconditionally: the primes with leading decimal digit $1$ have
Dirichlet density $\log_{10}2$ (in Milne's bounded-difference sense) and no natural density. -/
@[kb "milne2020cft" "Ch. VI, Remark 4.2 (a) (unconditional)"]
theorem remark_4_2a : Remark4_2a :=
  remark_4_2a_of_pntError R42.pntError

end NumberFieldKB.MilneCFT.Ch6
