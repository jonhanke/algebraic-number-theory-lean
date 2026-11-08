import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Continuous characters of $\mathbb R^\times$ and $\mathbb C^\times$

The classification behind the infinity type of a Hecke character:

* **`exists_eq_exp_mul_of_continuous`**: a continuous homomorphism $(\mathbb R,+)\to\mathbb C^\times$ is
  $t\mapsto e^{st}$ for a unique $s\in\mathbb C$ (`eq_of_forall_exp_mul_eq`). Proof: lift through the covering map
  $\exp:\mathbb C\to\mathbb C\setminus\{0\}$ (Mathlib's `Complex.isCoveringMap_exp`); the lift is additive by uniqueness
  of lifts, hence $\mathbb R$-linear.
* **`exists_realUnits_character`**: a continuous character of $\mathbb R^\times$ is $x\mapsto|x|^s\,\epsilon^{[x<0]}$ with
  $s\in\mathbb C$ and $\epsilon = \chi(-1)\in\{\pm1\}$.
* **`exists_complexUnits_character`**: a continuous character of $\mathbb C^\times$ is
  $z\mapsto|z|^s\,(z/|z|)^k$ with $s\in\mathbb C$, $k\in\mathbb Z$; both are unique (`complexUnits_character_unique`).

Tau Ceti has these classifications in `TauCeti/Analysis/SpecialFunctions/Complex/ArchimedeanCharacter.lean`, which is
not used here; the proofs here are our own.
-/

open Complex Topology

namespace NumberFieldKB.HeckeCharacters

noncomputable section

/-- **Uniqueness of the exponent**: if $e^{dt} = e^{d't}$ for every real $t$, then $d = d'$ (differentiate at $0$). -/
theorem eq_of_forall_exp_mul_eq {d d' : ℂ} (h : ∀ t : ℝ, exp (d * t) = exp (d' * t)) : d = d' := by
  have hderiv : HasDerivAt (fun t : ℝ => exp ((d - d') * t)) (exp ((d - d') * (0 : ℝ)) * (d - d')) 0 :=
    (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (d - d')).cexp |>.congr_deriv (by simp)
  have hconst : (fun t : ℝ => exp ((d - d') * t)) = fun _ => 1 := by
    funext t
    rw [sub_mul, exp_sub, h t, div_self (exp_ne_zero _)]
  rw [hconst] at hderiv
  have := hderiv.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
  simpa [sub_eq_zero] using this

/-- **Continuous homomorphisms $(\mathbb R,+)\to\mathbb C^\times$ are exponentials**: $\varphi(t) = e^{st}$. -/
theorem exists_eq_exp_mul_of_continuous (φ : ℝ → ℂˣ) (hφ : Continuous φ) (h0 : φ 0 = 1)
    (hadd : ∀ a b, φ (a + b) = φ a * φ b) : ∃ s : ℂ, ∀ t : ℝ, (φ t : ℂ) = exp (s * t) := by
  have hf : Continuous fun t => (φ t : ℂ) := Units.continuous_val.comp hφ
  let f : C(ℝ, {z : ℂ // z ≠ 0}) := ⟨fun t => ⟨φ t, (φ t).ne_zero⟩, hf.subtype_mk _⟩
  obtain ⟨L, ⟨hL0, hL⟩, huniq⟩ := IsCoveringMap.existsUnique_continuousMap_lifts Complex.isCoveringMap_exp
    f 0 0 (by ext; simp [f, h0])
  have hexpL (t : ℝ) : exp (L t) = φ t := congrArg Subtype.val (congrFun hL t)
  -- The lift is additive: `t ↦ L (a + t) - L a` is another lift of `φ` through `0`.
  have hLadd (a t : ℝ) : L (a + t) = L a + L t := by
    let M : C(ℝ, ℂ) := ⟨fun t => L (a + t) - L a, ((L.continuous.comp (continuous_const.add continuous_id)).sub
      continuous_const)⟩
    have hM : M = L := huniq M ⟨by simp [M], by
      funext t
      apply Subtype.ext
      change exp (L (a + t) - L a) = φ t
      rw [exp_sub, hexpL, hexpL, hadd, Units.val_mul, mul_div_cancel_left₀ _ (φ a).ne_zero]⟩
    have := congrArg (fun F : C(ℝ, ℂ) => F t) hM
    simp only [M, ContinuousMap.coe_mk] at this
    rw [← this]
    ring
  let ℓ : ℝ →+ ℂ := { toFun := L, map_zero' := hL0, map_add' := hLadd }
  refine ⟨L 1, fun t => ?_⟩
  have hlin := map_real_smul ℓ L.continuous t 1
  simp only [smul_eq_mul, mul_one, Complex.real_smul] at hlin
  change L t = t * L 1 at hlin
  rw [← hexpL, hlin, mul_comm]

/-- $\exp$ as a continuous map $\mathbb R\to\mathbb R^\times$. -/
private def realExpUnit (t : ℝ) : ℝˣ := Units.mk0 (Real.exp t) (Real.exp_pos t).ne'

private theorem continuous_realExpUnit : Continuous realExpUnit :=
  Units.continuous_iff.mpr ⟨Real.continuous_exp, by
    simp only [realExpUnit, Units.val_inv_eq_inv_val, Units.val_mk0]
    exact Real.continuous_exp.inv₀ fun t => (Real.exp_pos t).ne'⟩

/-- On positive reals a continuous character of $\mathbb R^\times$ is $x\mapsto x^s$. -/
private theorem exists_realUnits_pos (χ : ℝˣ →ₜ* ℂˣ) :
    ∃ s : ℂ, ∀ x : ℝˣ, 0 < (x : ℝ) → (χ x : ℂ) = ((x : ℝ) : ℂ) ^ s := by
  obtain ⟨s, hs⟩ := exists_eq_exp_mul_of_continuous (fun t => χ (realExpUnit t))
    ((map_continuous χ).comp continuous_realExpUnit)
    (by rw [show realExpUnit 0 = 1 from Units.ext (by simp [realExpUnit]), map_one])
    (fun a b => by rw [← map_mul]; congr 1; exact Units.ext (by simp [realExpUnit, Real.exp_add]))
  refine ⟨s, fun x hx => ?_⟩
  have hx' : realExpUnit (Real.log x) = x := Units.ext (by simp [realExpUnit, Real.exp_log hx])
  have h := hs (Real.log x)
  rw [hx'] at h
  rw [h, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ← ofReal_log hx.le, mul_comm]

/-- **Continuous characters of $\mathbb R^\times$**: $\chi(x) = |x|^s\cdot\chi(-1)^{[x<0]}$, with $\chi(-1) = \pm1$. -/
theorem exists_realUnits_character (χ : ℝˣ →ₜ* ℂˣ) :
    ∃ s : ℂ, ∀ x : ℝˣ, (χ x : ℂ) = ((|(x : ℝ)| : ℝ) : ℂ) ^ s * (if (x : ℝ) < 0 then (χ (-1) : ℂ) else 1) := by
  obtain ⟨s, hs⟩ := exists_realUnits_pos χ
  refine ⟨s, fun x => ?_⟩
  by_cases hx : (x : ℝ) < 0
  · have hpos : 0 < ((-x : ℝˣ) : ℝ) := by simpa using hx
    have hmul : χ x = χ (-1) * χ (-x) := by rw [← map_mul]; congr 1; simp
    simp only [hx, ↓reduceIte]
    rw [hmul, Units.val_mul, hs _ hpos, mul_comm, Units.val_neg, abs_of_neg hx]
  · have hpos : 0 < (x : ℝ) := lt_of_le_of_ne (not_lt.mp hx) (Ne.symm x.ne_zero)
    simp only [hx, ↓reduceIte]
    rw [mul_one, hs x hpos, abs_of_pos hpos]

/-- The sign value of a character of $\mathbb R^\times$: $\chi(-1)\in\{1,-1\}$. -/
theorem realUnits_character_neg_one (χ : ℝˣ →ₜ* ℂˣ) : (χ (-1) : ℂ) = 1 ∨ (χ (-1) : ℂ) = -1 := by
  have h : (χ (-1) : ℂ) * χ (-1) = 1 := by
    rw [← Units.val_mul, ← map_mul, neg_one_mul, neg_neg, map_one, Units.val_one]
  exact mul_self_eq_one_iff.mp h

/-- The unit $e^{i\theta}\in\mathbb C^\times$. -/
private def circleUnit (θ : ℝ) : ℂˣ := Units.mk0 (exp (θ * I)) (exp_ne_zero _)

private theorem continuous_circleUnit : Continuous circleUnit :=
  Units.continuous_iff.mpr ⟨by fun_prop, by
    simp only [circleUnit, Units.val_inv_eq_inv_val, Units.val_mk0]
    exact (by fun_prop : Continuous fun θ : ℝ => exp (θ * I)).inv₀ fun _ => exp_ne_zero _⟩

/-- The unit $r\in\mathbb C^\times$ for real $r>0$, as $e^t$. -/
private def complexExpUnit (t : ℝ) : ℂˣ := Units.mk0 (Real.exp t : ℂ) (ofReal_ne_zero.mpr (Real.exp_pos t).ne')

private theorem continuous_complexExpUnit : Continuous complexExpUnit :=
  Units.continuous_iff.mpr ⟨by simp only [Function.comp_def, complexExpUnit, Units.val_mk0]; fun_prop, by
    simp only [complexExpUnit, Units.val_inv_eq_inv_val, Units.val_mk0]
    exact (by fun_prop : Continuous fun t : ℝ => (Real.exp t : ℂ)).inv₀
      fun t => ofReal_ne_zero.mpr (Real.exp_pos t).ne'⟩

/-- **Continuous characters of $\mathbb C^\times$**: $\chi(z) = |z|^s\,(z/|z|)^k$ with $s\in\mathbb C$, $k\in\mathbb Z$. -/
theorem exists_complexUnits_character (χ : ℂˣ →ₜ* ℂˣ) :
    ∃ s : ℂ, ∃ k : ℤ, ∀ z : ℂˣ, (χ z : ℂ) = ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ s * ((z : ℂ) / ‖(z : ℂ)‖) ^ k := by
  -- The radial part.
  obtain ⟨s, hs⟩ := exists_eq_exp_mul_of_continuous (fun t => χ (complexExpUnit t))
    ((map_continuous χ).comp continuous_complexExpUnit)
    (by rw [show complexExpUnit 0 = 1 from Units.ext (by simp [complexExpUnit]), map_one])
    (fun a b => by
      rw [← map_mul]; congr 1; exact Units.ext (by simp [complexExpUnit, Real.exp_add]))
  -- The angular part.
  obtain ⟨c, hc⟩ := exists_eq_exp_mul_of_continuous (fun θ => χ (circleUnit θ))
    ((map_continuous χ).comp continuous_circleUnit)
    (by rw [show circleUnit 0 = 1 from Units.ext (by simp [circleUnit]), map_one])
    (fun a b => by
      rw [← map_mul]; congr 1; exact Units.ext (by simp [circleUnit, add_mul, exp_add]))
  have h2π : circleUnit (2 * Real.pi) = 1 := Units.ext (by simp [circleUnit, exp_two_pi_mul_I])
  have hc2π := hc (2 * Real.pi)
  rw [h2π, map_one, Units.val_one, eq_comm, exp_eq_one_iff] at hc2π
  obtain ⟨k, hk⟩ := hc2π
  have hck : c = k * I := by
    have hπ : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (mul_pos two_pos Real.pi_pos).ne'
    apply mul_right_cancel₀ hπ
    push_cast at hk
    linear_combination hk
  refine ⟨s, k, fun z => ?_⟩
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hn : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr hz
  have hsplit : z = complexExpUnit (Real.log ‖(z : ℂ)‖) * circleUnit (arg z) :=
    Units.ext (by simp [complexExpUnit, circleUnit, Real.exp_log hn, norm_mul_exp_arg_mul_I])
  have harg : (z : ℂ) / ‖(z : ℂ)‖ = exp (arg z * I) := by
    rw [div_eq_iff (ofReal_ne_zero.mpr hn.ne'), mul_comm, norm_mul_exp_arg_mul_I]
  have hχz : (χ z : ℂ) = exp (s * (Real.log ‖(z : ℂ)‖ : ℝ)) * exp (k * I * (arg z : ℝ)) := by
    conv_lhs => rw [hsplit]
    rw [map_mul, Units.val_mul, hs, hc, hck]
  rw [hχz, harg, ← exp_int_mul, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hn.ne'), ← ofReal_log hn.le,
    mul_comm (↑(Real.log _) : ℂ) s, show (k : ℂ) * (arg z * I) = k * I * arg z by ring]

/-- **Uniqueness** of $(s, k)$ for a character of $\mathbb C^\times$. -/
theorem complexUnits_character_unique {s s' : ℂ} {k k' : ℤ}
    (h : ∀ z : ℂˣ, ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ s * ((z : ℂ) / ‖(z : ℂ)‖) ^ k =
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ s' * ((z : ℂ) / ‖(z : ℂ)‖) ^ k') : s = s' ∧ k = k' := by
  have hs : s = s' := by
    refine eq_of_forall_exp_mul_eq fun t => ?_
    have := h (complexExpUnit t)
    simp only [complexExpUnit, Units.val_mk0, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t),
      div_self (ofReal_ne_zero.mpr (Real.exp_pos t).ne'), one_zpow, mul_one] at this
    rwa [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
      cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos t).ne'), ← ofReal_log (Real.exp_pos t).le,
      Real.log_exp, mul_comm _ s, mul_comm _ s'] at this
  refine ⟨hs, ?_⟩
  have hk : (k : ℂ) * I = k' * I := by
    refine eq_of_forall_exp_mul_eq fun θ => ?_
    have := h (circleUnit θ)
    simp only [circleUnit, Units.val_mk0, norm_exp_ofReal_mul_I, ofReal_one, one_cpow, one_mul, div_one,
      hs] at this
    rw [← exp_int_mul, ← exp_int_mul] at this
    rw [show (k : ℂ) * I * θ = k * (θ * I) by ring, show (k' : ℂ) * I * θ = k' * (θ * I) by ring]
    exact this
  exact_mod_cast mul_right_cancel₀ I_ne_zero hk

end

end NumberFieldKB.HeckeCharacters
