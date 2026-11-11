import NumberFieldKB.ModularCurves.EllipticCount
import NumberFieldKB.TauCetiPort.NumberTheory.LegendreSymbol.QuadraticCongruence
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The numbers of elliptic points of $\Gamma_0(N)$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (the genus formula, pdf p. 196); G. Shimura,
*Introduction to the Arithmetic Theory of Automorphic Functions*, Proposition 1.43; F. Diamond and J. Shurman,
*A First Course in Modular Forms*, §3.7.

The cosets $c = \gamma\Gamma_0(N)$ fixed by $S$ (resp. $ST$) are those with $\gamma^{-1} S \gamma \in \Gamma_0(N)$, that is
$N \mid c^2 + d^2$ (resp. $N \mid c^2 - cd + d^2$) for the bottom row $(c, d)$ of $\gamma^{-1}$; then $d$ is a unit mod
$N$ and $x = c/d$ is a root of $x^2 + 1$ (resp. $x^2 - x + 1$) in $\mathbb Z/N$, a complete invariant of the coset
(`nu2_eq_card`, `nu3_eq_card`, as Tau Ceti's `TauCeti.gamma0OrderTwoEllipticEquiv`). The closed forms
(`nu2_eq_prod`, `nu3_eq_prod`) are Tau Ceti's root counts `TauCeti.ZMod.natCard_sq_add_one_eq_zero`,
`TauCeti.ZMod.natCard_sq_sub_self_add_one_eq_zero` (ported in `NumberFieldKB/TauCetiPort/`).
-/

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

namespace NumberFieldKB.ModularCurves

variable (N : ℕ) [NeZero N]

/-! Helper lemmas, adapted from Tau Ceti Elliptic/Gamma0.lean (Apache 2.0). -/

section Helpers

variable {N}
set_option linter.unusedSectionVars false

/-- The conjugate `δ S δ⁻¹` lies in `Γ₀(N)` iff `N ∣ c² + d²`, for `(c, d)` the bottom row of `δ`. -/
theorem conj_S_mem_Gamma0_iff (δ : SL(2, ℤ)) :
    δ * ModularGroup.S * δ⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      (N : ℤ) ∣ δ 1 0 ^ 2 + δ 1 1 ^ 2 := by
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  convert Iff.rfl using 2
  simp [coe_mul, coe_inv, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The conjugate `δ (S T) δ⁻¹` lies in `Γ₀(N)` iff `N ∣ c² - c d + d²`. -/
theorem conj_ST_mem_Gamma0_iff (δ : SL(2, ℤ)) :
    δ * (ModularGroup.S * ModularGroup.T) * δ⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      (N : ℤ) ∣ δ 1 0 ^ 2 - δ 1 0 * δ 1 1 + δ 1 1 ^ 2 := by
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  convert Iff.rfl using 2
  simp [coe_mul, coe_inv, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The bottom row of `γ` is proportional to `(x, 1)` modulo `N`: `c ≡ x d`. -/
private def IsRatio (x : ZMod N) (γ : SL(2, ℤ)) : Prop :=
  ((γ 1 0 : ℤ) : ZMod N) = x * (γ 1 1 : ℤ)

private theorem det_cast (γ : SL(2, ℤ)) :
    ((γ 0 0 : ℤ) : ZMod N) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at h
  exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) h

private theorem IsRatio.eq {x y : ZMod N} {γ : SL(2, ℤ)} (hx : IsRatio x γ) (hy : IsRatio y γ) :
    x = y := by
  have hdet := det_cast (N := N) γ
  unfold IsRatio at hx hy
  rw [hx] at hdet
  have e : x * ((γ 1 1 : ℤ) : ZMod N) = y * (γ 1 1 : ℤ) := hx.symm.trans hy
  linear_combination ((γ 0 0 : ℤ) - (γ 0 1 : ℤ) * x : ZMod N) * e - (x - y) * hdet

private theorem IsRatio.mul_left {x : ZMod N} {g γ : SL(2, ℤ)}
    (hg : g ∈ CongruenceSubgroup.Gamma0 N) (h : IsRatio x γ) : IsRatio x (g * γ) := by
  have hg0 : ((g 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.mp hg
  unfold IsRatio at *
  simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul, hg0, h]
  ring

/-- The lower-triangular matrix `[1, 0; x, 1]`, whose residue is `x`. -/
private def lowerRep (x : ZMod N) : SL(2, ℤ) :=
  ⟨!![1, 0; (x.cast : ℤ), 1], by simp [Matrix.det_fin_two_of]⟩

private theorem isRatio_lowerRep (x : ZMod N) : IsRatio x (lowerRep x) := by
  simp [IsRatio, lowerRep]

/-- If `x` is the residue of `γ⁻¹`, then `lowerRep x * γ ∈ Γ₀(N)`. -/
private theorem lowerRep_mul_mem {x : ZMod N} {γ : SL(2, ℤ)} (h : IsRatio x γ⁻¹) :
    lowerRep x * γ ∈ CongruenceSubgroup.Gamma0 N := by
  unfold IsRatio at h
  rw [CongruenceSubgroup.Gamma0_mem]
  simp only [coe_inv, adjugate_fin_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h
  push_cast at h
  rw [coe_mul]
  simp [lowerRep, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination -h

open scoped Classical in
/-- Generic count: if fixing by `g` is equivalent to having a residue satisfying `P`, then the
fixed cosets are counted by the solutions of `P`. -/
private theorem card_fixed_eq (g : SL(2, ℤ)) (P : ZMod N → Prop)
    (hcond : ∀ δ : SL(2, ℤ), δ * g * δ⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      ∃ x, P x ∧ IsRatio x δ) :
    (Finset.univ.filter fun c : Cosets N => g • c = c).card = Nat.card {x : ZMod N // P x} := by
  classical
  have key : ∀ γ : SL(2, ℤ), g • (γ : Cosets N) = (γ : Cosets N) ↔
      ∃ x, P x ∧ IsRatio x γ⁻¹ := by
    intro γ
    rw [← hcond γ⁻¹, show g • (γ : Cosets N) = ((g * γ : SL(2, ℤ)) : Cosets N) from rfl,
      eq_comm, QuotientGroup.eq, inv_inv, mul_assoc]
  let f : {x : ZMod N // P x} → {c : Cosets N // g • c = c} := fun x =>
    ⟨((lowerRep x.1)⁻¹ : SL(2, ℤ)), (key _).mpr ⟨x.1, x.2, by
      rw [inv_inv]; exact isRatio_lowerRep x.1⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun ⟨c, hc⟩ => ?_⟩
    · have h := QuotientGroup.eq.mp (congrArg Subtype.val hxy)
      have h2 := (isRatio_lowerRep y.1).mul_left h
      rw [show ((lowerRep x.1)⁻¹)⁻¹ * (lowerRep y.1)⁻¹ * lowerRep y.1 = lowerRep x.1 by group] at h2
      exact Subtype.ext ((isRatio_lowerRep x.1).eq h2)
    · induction c using QuotientGroup.induction_on with | _ γ =>
      obtain ⟨x, hx, hr⟩ := (key γ).mp hc
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      show (((lowerRep x)⁻¹ : SL(2, ℤ)) : Cosets N) = (γ : Cosets N)
      rw [QuotientGroup.eq, inv_inv]
      exact lowerRep_mul_mem hr
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

end Helpers

/-- $\nu_2$ is the number of square roots of $-1$ in $\mathbb Z/N$. -/
theorem nu2_eq_card : nu2 N = Nat.card {x : ZMod N // x ^ 2 + 1 = 0} := by
  refine card_fixed_eq ModularGroup.S _ fun δ => ?_
  rw [conj_S_mem_Gamma0_iff, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hdet := det_cast (N := N) δ
  unfold IsRatio
  set a : ZMod N := ((δ 0 0 : ℤ) : ZMod N)
  set b : ZMod N := ((δ 0 1 : ℤ) : ZMod N)
  set c : ZMod N := ((δ 1 0 : ℤ) : ZMod N)
  set d : ZMod N := ((δ 1 1 : ℤ) : ZMod N)
  constructor
  · intro h
    set u := a - a * b * c - b ^ 2 * d
    have hu : d * u = 1 := by linear_combination (1 - b * c) * hdet - b ^ 2 * h
    exact ⟨c * u, by linear_combination u ^ 2 * h - (d * u + 1) * hu,
      by linear_combination (-c) * hu⟩
  · rintro ⟨x, hx, hc⟩
    linear_combination (c + x * d) * hc + d ^ 2 * hx

/-- $\nu_3$ is the number of roots of $x^2 - x + 1$ in $\mathbb Z/N$. -/
theorem nu3_eq_card : nu3 N = Nat.card {x : ZMod N // x ^ 2 - x + 1 = 0} := by
  refine card_fixed_eq (ModularGroup.S * ModularGroup.T) _ fun δ => ?_
  rw [conj_ST_mem_Gamma0_iff, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hdet := det_cast (N := N) δ
  unfold IsRatio
  set a : ZMod N := ((δ 0 0 : ℤ) : ZMod N)
  set b : ZMod N := ((δ 0 1 : ℤ) : ZMod N)
  set c : ZMod N := ((δ 1 0 : ℤ) : ZMod N)
  set d : ZMod N := ((δ 1 1 : ℤ) : ZMod N)
  constructor
  · intro h
    set u := a - a * b * c + b ^ 2 * c - b ^ 2 * d
    have hu : d * u = 1 := by linear_combination (1 - b * c) * hdet - b ^ 2 * h
    exact ⟨c * u, by linear_combination u ^ 2 * h + (c * u - d * u - 1) * hu,
      by linear_combination (-c) * hu⟩
  · rintro ⟨x, hx, hc⟩
    linear_combination (c + x * d - d) * hc + d ^ 2 * hx

/-- **$\nu_2 = \prod_{p \mid N}(1 + \chi_4(p))$ if $4 \nmid N$, and $0$ if $4 \mid N$**
(Milne, Ch. V, §2, pdf p. 196; $\chi_4(p) = (-1 \mid p)$ for odd $p$, $\chi_4(2) = 0$). -/
@[kb "milne2006ec" "Ch. V, §2, the number nu_2 of elliptic points of order 2 of Gamma_0(N), pdf p. 196"]
theorem nu2_eq_prod :
    (nu2 N : ℤ) = if 4 ∣ N then 0 else ∏ p ∈ N.primeFactors, (1 + ZMod.χ₄ p) := by
  rw [nu2_eq_card]
  exact TauCeti.ZMod.natCard_sq_add_one_eq_zero N

/-- **$\nu_3 = \prod_{p \mid N}(1 + (p \mid 3))$ if $9 \nmid N$, and $0$ if $9 \mid N$** (Milne, Ch. V, §2,
pdf p. 196; $(p \mid 3)$ is the Legendre symbol, equal to $(-3 \mid p)$ for $p \ne 3$). -/
@[kb "milne2006ec" "Ch. V, §2, the number nu_3 of elliptic points of order 3 of Gamma_0(N), pdf p. 196"]
theorem nu3_eq_prod :
    (nu3 N : ℤ) = if 9 ∣ N then 0 else ∏ p ∈ N.primeFactors, (1 + legendreSym 3 p) := by
  rw [nu3_eq_card]
  exact TauCeti.ZMod.natCard_sq_sub_self_add_one_eq_zero N

end NumberFieldKB.ModularCurves
