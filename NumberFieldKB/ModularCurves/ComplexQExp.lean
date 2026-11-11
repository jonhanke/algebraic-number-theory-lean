import NumberFieldKB.ModularCurves.QExpTransfer
import Mathlib.RingTheory.LaurentSeries
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Complex polynomial identities and Laurent expansions

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2–3. The complex-coefficient version of the transfer in
`QExpTransfer.lean`: in the ring `qMerD d hd` of functions $f$ with $d^n f$ having a $q$-expansion, constants
(`constMerD`), quotients $A/B$ of functions with $q$-expansions, $B \mid d$ (`divMerD`, with expansion
$\hat A/\hat B$, `qMerDHom_divMerD`), and polynomials $G(x, y)$ with complex coefficients (`evalMerD`) are
compatible with the Laurent expansion `qMerDHom` (`qMerDHom_evalMerD`).
-/

open Polynomial
open scoped UpperHalfPlane

noncomputable section

namespace NumberFieldKB.ModularCurves

variable {d : ℍ → ℂ} (hd : IsQExp d) (hd0 : ∀ z, d z ≠ 0)

/-- Complex constants in `qMerD d hd`. -/
def constMerD : ℂ →+* qMerD d hd where
  toFun c := ⟨fun _ => c, 0, by simpa using IsQExp.const c⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem qHat_const (c : ℂ) : qHat (fun _ : ℍ => c) = HahnSeries.C c := by
  have h : (fun _ : ℍ => c) = c • (1 : ℍ → ℂ) := by funext z; simp
  rw [h, qHat, UpperHalfPlane.qExpansion_smul IsQExp.one.analytic, UpperHalfPlane.qExpansion_one]
  rw [PowerSeries.smul_eq_C_mul, mul_one, HahnSeries.ofPowerSeries_C]

include hd0 in
theorem qMerDHom_constMerD (c : ℂ) : qMerDHom hd hd0 (constMerD hd c) = HahnSeries.C c := by
  change qMerDFun hd (constMerD hd c) = _
  rw [qMerDFun_of_isQExp hd hd0 _ (IsQExp.const c)]
  exact qHat_const c

/-- $G(x, y)$ in `qMerD d hd`, for $G \in \mathbb C[X][Y]$. -/
def evalMerD (x y : qMerD d hd) : ℂ[X][X] →+* qMerD d hd :=
  eval₂RingHom (eval₂RingHom (constMerD hd) x) y

include hd0 in
/-- **Laurent expansions commute with complex polynomials.** -/
theorem qMerDHom_evalMerD (x y : qMerD d hd) (G : ℂ[X][X]) :
    qMerDHom hd hd0 (evalMerD hd x y G) =
      G.eval₂ (eval₂RingHom HahnSeries.C (qMerDHom hd hd0 x)) (qMerDHom hd hd0 y) := by
  rw [evalMerD, coe_eval₂RingHom, Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp [qMerDHom_constMerD hd hd0]
  · simp

theorem coe_evalMerD (x y : qMerD d hd) (G : ℂ[X][X]) (z : ℍ) :
    (evalMerD hd x y G).1 z = (G.map (evalRingHom (x.1 z))).eval (y.1 z) := by
  have h := Polynomial.hom_eval₂ G (eval₂RingHom (constMerD hd) x)
    ((Pi.evalRingHom (fun _ : ℍ => ℂ) z).comp (qMerD d hd).val.toRingHom) y
  change ((Pi.evalRingHom (fun _ : ℍ => ℂ) z).comp (qMerD d hd).val.toRingHom) (evalMerD hd x y G) = _
  rw [evalMerD, coe_eval₂RingHom, h, Polynomial.eval_map]
  congr 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp [constMerD]
  · simp

/-- $A/B$ in `qMerD d hd` when $d = B B'$ with $B'$ having a $q$-expansion. -/
def divMerD {A B B' : ℍ → ℂ} (hA : IsQExp A) (hB' : IsQExp B') (hdB : d = B * B') (hB0 : ∀ z, B z ≠ 0) :
    qMerD d hd :=
  ⟨A / B, 1, by
    have : d ^ 1 * (A / B) = A * B' := by
      funext z; have := hB0 z; rw [hdB]; simp; field_simp
    rw [this]; exact hA.mul hB'⟩

include hd0 in
theorem qMerDHom_divMerD {A B B' : ℍ → ℂ} (hA : IsQExp A) (hB : IsQExp B) (hB' : IsQExp B') (hdB : d = B * B')
    (hB0 : ∀ z, B z ≠ 0) : qMerDHom hd hd0 (divMerD hd hA hB' hdB hB0) = qHat A / qHat B := by
  have e : d ^ 1 * (A / B) = A * B' := by
    funext z; have := hB0 z; rw [hdB]; simp; field_simp
  change qMerDFun hd _ = _
  rw [qMerDFun_eq hd hd0 _ (n := 1) (by show IsQExp (d ^ 1 * (A / B)); rw [e]; exact hA.mul hB')]
  show qHat (d ^ 1 * (A / B)) / qHat d ^ 1 = _
  have hB'0 : qHat B' ≠ 0 := by
    have := qHat_ne_zero_of_nowhere hd hd0
    rw [hdB, qHat_mul hB hB'] at this
    exact right_ne_zero_of_mul this
  have hB0' : qHat B ≠ 0 := qHat_ne_zero_of_nowhere hB hB0
  rw [e, qHat_mul hA hB', pow_one, hdB, qHat_mul hB hB']
  field_simp

end NumberFieldKB.ModularCurves
