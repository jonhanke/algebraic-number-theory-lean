/-
Copyright (c) the PrimeNumberTheoremAnd contributors (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd).
Released under Apache 2.0 license as described in the file LICENSE of that repository.
Authors: the PrimeNumberTheoremAnd contributors
-/
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace NumberFieldKB.PNTPort

open Filter Real

open Real in
/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem _root_.Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end NumberFieldKB.PNTPort
