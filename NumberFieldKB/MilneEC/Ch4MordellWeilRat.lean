import NumberFieldKB.MilneEC.Ch4Thm31
import NumberFieldKB.MilneEC.Ch4TwoDescent

/-!
# Milne, *Elliptic Curves*, Chapter IV: consequences of Theorem 3.1 over $\mathbb Q$ without hypotheses

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter IV, Remark 5.2 (pdf p. 135), Proposition 5.5
(pdf p. 137), Proposition 5.6 (pdf p. 137), Example 5.7 (pdf p. 138).

The statements of Chapter IV §5 were proved from the named statements `Lemma2_1` and `Thm3_1_Selmer`
(`Ch4Rank.lean`).  Here they are re-exported over $\mathbb Q$ along Milne's own route, with `lemma2_1` and the
Selmer finiteness `thm_3_1_selmer_rat` / Mordell–Weil `mordell_weil_rat` in place of the named statements.
(For Propositions 5.5, 5.6 and Example 5.7 the library also has the forms of `Ch4TwoDescent.lean`, which use the
2-descent of Remark 3.7 directly instead of Theorem 3.1.)
-/

namespace NumberFieldKB.MilneEC

open WeierstrassCurve

/-- **Remark 5.2** (pdf p. 135) over $\mathbb Q$, with Lemma 2.1 and Theorem 3.1 proved. -/
@[kb "milne2006ec" "Ch. IV, Remark 5.2, pdf p. 135"]
theorem remark_5_2_rat (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hdiv : ∀ z ∈ tateShafarevich ℚ W, (∃ k : ℕ, (2 : ℤ) ^ k • z = 0) →
      (∀ n : ℕ, ∃ y ∈ tateShafarevich ℚ W, (2 : ℤ) ^ n • y = z) → z = 0) :
    {z | z ∈ tateShafarevich ℚ W ∧ ∃ k : ℕ, (2 : ℤ) ^ k • z = 0}.Finite ∧
      ∃ m₀ : ℕ, ∀ m ≥ m₀, selmerImage W m = (kummerMap W lemma2_1 2 two_ne_zero).range :=
  remark_5_2_of_finite W lemma2_1 (thm_3_1_selmer_rat W 2 two_ne_zero) hdiv

/-- **Proposition 5.5** (pdf p. 137), by Milne's route: Mordell–Weil over $\mathbb Q$ and Remark 3.7. -/
@[kb "milne2006ec" "Ch. IV, Prop. 5.5, pdf p. 137"]
theorem prop_5_5_rank_rat {α β γ : ℤ} (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α) :
    rank (cubicCurve α β γ) ≤ 2 * (2 * cubicDisc α β γ).natAbs.primeFactors.card := by
  haveI : (cubicCurve α β γ).IsElliptic := (cubicCurve_isElliptic_iff α β γ).2 ⟨hαβ, hβγ, hγα⟩
  haveI : AddGroup.FG (cubicCurve α β γ).toAffine.Point :=
    Module.Finite.iff_addGroup_fg.1 (mordell_weil_rat (cubicCurve α β γ))
  exact prop_5_5_rank_of_fg remark_3_7 hαβ hβγ hγα

/-- **Proposition 5.6** (pdf p. 137), by Milne's route: Mordell–Weil over $\mathbb Q$, Remark 3.7 and the local
statements (a)–(c). -/
@[kb "milne2006ec" "Ch. IV, Prop. 5.6, pdf p. 137"]
theorem prop_5_6_rat {α β γ : ℤ} (hαβ : α < β) (hβγ : β < γ) :
    rank (cubicCurve α β γ) + 1 ≤ (nodalPrimes α β γ).card + 2 * (cuspidalPrimes α β γ).card := by
  haveI : (cubicCurve α β γ).IsElliptic :=
    (cubicCurve_isElliptic_iff α β γ).2 ⟨hαβ.ne, hβγ.ne, (lt_trans hαβ hβγ).ne'⟩
  haveI : AddGroup.FG (cubicCurve α β γ).toAffine.Point :=
    Module.Finite.iff_addGroup_fg.1 (mordell_weil_rat (cubicCurve α β γ))
  exact prop_5_6_of_fg remark_3_7 prop_5_6_local hαβ hβγ

/-- **Example 5.7** (pdf p. 138), by Milne's route: $E : Y^2 = X^3 - X$ has rank $0$ and $E(\mathbb Q)$ is
finite. -/
@[kb "milne2006ec" "Ch. IV, Example 5.7, pdf p. 138"]
theorem example_5_7_rat :
    rank (cubicCurve (-1) 0 1) = 0 ∧ Finite (cubicCurve (-1) 0 1).toAffine.Point := by
  haveI : (cubicCurve (-1) 0 1).IsElliptic :=
    (cubicCurve_isElliptic_iff (-1) 0 1).2 ⟨by norm_num, by norm_num, by norm_num⟩
  haveI : AddGroup.FG (cubicCurve (-1) 0 1).toAffine.Point :=
    Module.Finite.iff_addGroup_fg.1 (mordell_weil_rat (cubicCurve (-1) 0 1))
  exact example_5_7_of_fg remark_3_7 prop_5_6_local

end NumberFieldKB.MilneEC
