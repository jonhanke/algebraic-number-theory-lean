import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Equiv.Hilbert
import QuadFormsKB.Literature.LocalGlobal.HilbertReciprocity
import QuadFormsKB.Literature.HasseNorm.Reciprocity
import QuadFormsKB.Literature.HasseNorm.LocalIndexTwo
import QuadFormsKB.Tamagawa.SquareClassDuality
import QuadFormsKB.Tamagawa.Quaternion

/-!
# Milne, *Class Field Theory*, Chapter III §4: the quadratic Hilbert symbol (citations)

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

For $n = 2$ the Hilbert symbol of §4 is QuadFormsKB's `QuadFormsKB.hilbertSymbol` ($(a,b) = 1$ iff
$z^2 = ax^2 + by^2$ has a nontrivial solution), defined over any field. The results below restate the QuadFormsKB
theorems in Milne's form and tag them with Milne's locators. Milne's general symbol (any $n$, through cup products
of Kummer classes) is in `Ch3Hilbert`.
-/

namespace NumberFieldKB.MilneCFT.Ch3

open QuadFormsKB

open Classical in
/-- **The Hilbert symbol over $\mathbb Q_p$** (Milne, p. 110, definition in prose, "a very special case"): for
$a, b \in \mathbb Q_p^\times$, $(a,b)_p = 1$ if $z^2 = ax^2 + by^2$ has a nontrivial solution in $\mathbb Q_p$, and
$-1$ otherwise. This is QuadFormsKB's `hilbertSymbol ℚ_[p]`. -/
@[kb "milne2020cft" "v4.03, Ch. III, §4, the Hilbert symbol (a,b)_p over Q_p, p. 110"]
theorem hilbertSymbol_padic_def (p : ℕ) [Fact p.Prime] (a b : ℚ_[p]) :
    hilbertSymbol ℚ_[p] a b =
      if ∃ x y z : ℚ_[p], (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 then 1 else -1 := rfl

/-- **Aside 4.2** (p. 111): the Hilbert symbol is also defined for $\mathbb R$ ($(a,b)_\infty = -1$ iff $a, b < 0$),
and Hilbert's product formula (34) $\prod_{p \le \infty} (a,b)_p = 1$ holds for $a, b \in \mathbb Q^\times$: the
symbol is $-1$ at finitely many places, an even number of them. -/
@[kb "milne2020cft" "v4.03, Ch. III, Aside 4.2 and (34), p. 111"]
theorem aside_4_2 (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (hilbertSymbol ℝ a b = -1 ↔ (a : ℝ) < 0 ∧ (b : ℝ) < 0) ∧
      {v : RatPlace | v.hilbert a b = -1}.Finite ∧ Even {v : RatPlace | v.hilbert a b = -1}.ncard :=
  ⟨hilbertSymbol_real a b (by exact_mod_cast ha) (by exact_mod_cast hb), hilbert_product_formula a b ha hb⟩

open IsDedekindDomain NumberField in
/-- **Theorem 4.4 for $n = 2$** (p. 113), for the completion $K = F_v$ of a number field at a finite place:
(a) $(aa', b) = (a, b)(a', b)$; (b) $(b, a) = (a, b)^{-1}$ $(= (a, b)$, the values being $\pm 1)$; (c) if
$(a, b) = 1$ for all $b$ then $a$ is a square; (d) $(a, b) = 1$ iff $b$ is a norm from $K[\sqrt a]$, i.e.
$b = x_0^2 - a x_1^2$. (Milne's theorem is for every local field containing the $n$-th roots of $1$; the general-$n$
statement is the named `Thm4_4` in `Ch3Hilbert`.) -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 4.4 (n = 2), p. 113"]
theorem theorem_4_4_two {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (∀ a a' b : v.adicCompletion F, a ≠ 0 → a' ≠ 0 → b ≠ 0 →
      hilbertSymbol _ (a * a') b = hilbertSymbol _ a b * hilbertSymbol _ a' b) ∧
    (∀ a b : v.adicCompletion F, hilbertSymbol _ b a = hilbertSymbol _ a b) ∧
    (∀ a : v.adicCompletion F, a ≠ 0 → (∀ b : v.adicCompletion F, b ≠ 0 → hilbertSymbol _ a b = 1) →
      IsSquare a) ∧
    (∀ a b : v.adicCompletion F, a ≠ 0 →
      (hilbertSymbol _ a b = 1 ↔ ∃ x₀ x₁ : v.adicCompletion F, b = x₀ ^ 2 - a * x₁ ^ 2)) := by
  refine ⟨fun a a' b ha ha' hb => HN.hilbertSymbol_mul_left_finite_nf v a a' b ha ha' hb,
    fun a b => hilbertSymbol_comm _ b a, fun a ha h => ?_, fun a b ha => ?_⟩
  · by_contra hns
    have hy : (QuotientGroup.mk (Units.mk0 a ha) : SqDual.SqCl (v.adicCompletion F)) ≠ 1 := fun h1 =>
      hns ((SqDual.mk_eq_one_iff_isSquare _ _).mp h1)
    obtain ⟨x, hx⟩ := SqDual.hilbCl_nondeg_fin v _ hy
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [SqDual.hilbCl_mk, hilbertSymbol_comm] at hx
      have := h u u.ne_zero
      simp only [Units.val_mk0] at hx
      rw [this] at hx
      norm_num at hx
  · have h2 : (2 : v.adicCompletion F) ≠ 0 := two_ne_zero
    exact HN.hilbertSymbol_eq_one_iff_norm _ h2 ha

open Quaternion in
/-- **Remark 4.7 for $n = 2$** (p. 115): the Hilbert symbol $(a, b)$ corresponds to the class of the quaternion
algebra $H(a, b)$ in the Brauer group; in the form available: $(a, b) = -1$ iff $H(a, b)$ is a division algebra
($2 \ne 0$, $a, b \ne 0$). -/
@[kb "milne2020cft" "v4.03, Ch. III, Remark 4.7 (n = 2), p. 115"]
theorem remark_4_7_two {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol K a b = -1 ↔ ∀ x : ℍ[K,a,b], x ≠ 0 → IsUnit x :=
  Quat.hilbertSymbol_eq_neg_one_iff_division h2 ha hb

/-- **Remark 4.8 for $n = 2$** (p. 115): the Hilbert symbol is defined for $K = \mathbb R$, and the product formula
holds for every number field $F$: for $a, b \in F^\times$, $(a, b)_v = -1$ at finitely many places $v$ of $F$, an
even number of them. -/
@[kb "milne2020cft" "v4.03, Ch. III, Remark 4.8 (n = 2), p. 115"]
theorem remark_4_8_two {F : Type} [Field F] [NumberField F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : NFPlace F | v.hilbert a b = -1}.Finite ∧ Even {v : NFPlace F | v.hilbert a b = -1}.ncard :=
  HN.hilbert_product_formula_nf a b ha hb

end NumberFieldKB.MilneCFT.Ch3
