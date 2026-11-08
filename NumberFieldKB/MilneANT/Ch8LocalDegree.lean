import NumberFieldKB.MilneANT.Ch8LocalDegreeLower
import NumberFieldKB.MilneANT.Ch8Remark83

/-!
# The local degree formula and Remark 8.3, unconditionally

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), bib key `milne2020ant`, Remark 8.3, p. 136.

Combines the lower bound $e f \le [L_w : K_{\mathfrak p}]$ (`ramificationIdx_mul_inertiaDeg_le_finrank`,
`Ch8LocalDegreeLower.lean`) with the counting argument of `Ch8Remark83.lean`
($\sum_w [L_w : K_{\mathfrak p}] = [L : K] = \sum_{\mathfrak P \mid \mathfrak p} e f$): for the extension $w$ of
$\lVert\cdot\rVert_{\mathfrak p}$ attached to $\mathfrak P$, $[L_w : K_{\mathfrak p}] = e(\mathfrak P/\mathfrak p)
f(\mathfrak P/\mathfrak p)$, and the named statement `Remark8_3` holds.
-/

open NumberField IsDedekindDomain

namespace NumberFieldKB.MilneANT

/-- The lower bound $e f \le [L_w : K_{\mathfrak p}]$ holds. -/
theorem localDegreeLowerBound : LocalDegreeLowerBound :=
  fun K L _ _ _ _ _ 𝔭 P _ w hw => ramificationIdx_mul_inertiaDeg_le_finrank K L 𝔭 P w hw

/-- **The local degree formula** (Milne, Remark 8.3 and the discussion of p. 136): for number fields $L/K$, a prime
$\mathfrak P$ of $L$ over $\mathfrak p$ and the extension $w$ of $\lVert\cdot\rVert_{\mathfrak p}$ equivalent to the
$\mathfrak P$-adic absolute value, $[L_w : K_{\mathfrak p}] = e(\mathfrak P/\mathfrak p) f(\mathfrak P/\mathfrak p)$. -/
@[kb "milne2020ant" "v3.08, Rem. 8.3, p. 136"]
theorem finrank_completion_eq_ramificationIdx_mul_inertiaDeg (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (𝔭 : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver 𝔭.asIdeal] (w : Extensions L (FinitePlace.mk 𝔭).1)
    (hw : w.1.IsEquiv (FinitePlace.mk P).1) :
    letI := extAlgebra (FinitePlace.mk 𝔭).1 w
    Module.finrank (FinitePlace.mk 𝔭).1.Completion w.1.Completion =
      P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) :=
  Remark83.finrank_completion_of_lowerBound localDegreeLowerBound 𝔭 P w hw

/-- **Remark 8.3** (Milne, p. 136), unconditionally: discharges the named statement `Remark8_3`. -/
@[kb "milne2020ant" "v3.08, Rem. 8.3, p. 136"]
theorem remark_8_3 : Remark8_3 :=
  remark_8_3_of_lowerBound localDegreeLowerBound

end NumberFieldKB.MilneANT
