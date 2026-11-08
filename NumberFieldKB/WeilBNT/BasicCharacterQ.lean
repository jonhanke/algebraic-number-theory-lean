import QuadFormsKB.Analysis.GlobalCharacter

/-!
# Weil, *Basic Number Theory*, IV.§2, text p. 66–67: the basic character of $\mathbb Q_{\mathbb A}$

Weil's basic character $\chi$ of $\mathbb Q_{\mathbb A}$ (proof of Thm. 3 for $E=k=\mathbb Q$) is characterized by: it is
trivial on $\mathbb Q$, $\chi_p$ is trivial on $\mathbb Z_p$ for every prime $p$, and $\chi_\infty(x)=e(-x)$ on
$\mathbb R$ ($e(t)=e^{2\pi it}$, Mathlib's `𝐞`). Then $\chi_p(\xi)=e(\xi)$ for $\xi\in\mathbb Q(p)$ (the rationals with
$p$-power denominator, `IsPFrac p`) and the kernel of $\chi_p$ is $\mathbb Z_p$ ("$\chi_p$ is of order $0$").

Weil's local characters are the complex conjugates of QuadFormsKB's `psiP` (Tate's normalization
$\psi_p(x)=e(-\{x\}_p)$, $\psi_\infty=e$): `weilChiP p x = psiP (-x)` and `weilChiInf x = 𝐞 (-x)`.

* `weilChiP_pFrac`: $\chi_p(\xi)=e(\xi)$ for $\xi\in\mathbb Q(p)$.
* `weilChiP_eq_one_iff`: $\ker\chi_p=\mathbb Z_p$.
* `weilChiP_unique`: $\chi_p$ is the only character of $\mathbb Q_p$ trivial on $\mathbb Z_p$ with $\chi_p(\xi)=e(\xi)$ on
  $\mathbb Q(p)$ (Weil: "by lemma 1, $\chi_p$ is completely determined by this").
* **`weil_IV_2_text66_basicChar`**: the product $\chi_\infty(r)\prod_p\chi_p(r)$ is $1$ for every $r\in\mathbb Q$
  (from QuadFormsKB's `fourierChar_mul_finprod_psiP`), together with the three properties above.
-/

open QuadFormsKB.Analysis
open scoped Real FourierTransform

noncomputable section

namespace NumberFieldKB.WeilBNT

/-- Weil's $\chi_\infty(x)=e(-x)$ on $\mathbb R$. -/
def weilChiInf : AddChar ℝ Circle := (𝐞 : AddChar ℝ Circle).compAddMonoidHom (-AddMonoidHom.id ℝ)

theorem weilChiInf_apply (x : ℝ) : weilChiInf x = 𝐞 (-x) := rfl

variable (p : ℕ) [Fact p.Prime]

/-- Weil's $\chi_p$ on $\mathbb Q_p$: $\chi_p(x)=\psi_p(-x)=e(\{x\}_p)$. -/
def weilChiP : AddChar ℚ_[p] Circle := (psiP (p := p)).compAddMonoidHom (-AddMonoidHom.id ℚ_[p])

variable {p}

theorem weilChiP_apply (x : ℚ_[p]) : weilChiP p x = psiP (p := p) (-x) := rfl

/-- $\chi_p(\xi)=e(\xi)$ for $\xi\in\mathbb Q(p)$. -/
theorem weilChiP_pFrac {r : ℚ} (hr : IsPFrac p r) : weilChiP p (r : ℚ_[p]) = 𝐞 (r : ℝ) := by
  rw [weilChiP_apply, ← Rat.cast_neg, psiP_pFrac hr.neg]
  push_cast; rw [neg_neg]

/-- The kernel of $\chi_p$ is $\mathbb Z_p$. -/
theorem weilChiP_eq_one_iff (x : ℚ_[p]) : weilChiP p x = 1 ↔ ‖x‖ ≤ 1 := by
  rw [weilChiP_apply, psiP_eq_one_iff, norm_neg]

/-- $\chi_p$ is determined by being trivial on $\mathbb Z_p$ and equal to $e(\xi)$ on $\mathbb Q(p)$. -/
theorem weilChiP_unique (χ : AddChar ℚ_[p] Circle) (h1 : ∀ x : ℚ_[p], ‖x‖ ≤ 1 → χ x = 1)
    (h2 : ∀ r : ℚ, IsPFrac p r → χ (r : ℚ_[p]) = 𝐞 (r : ℝ)) : χ = weilChiP p := by
  ext x
  obtain ⟨hr, hxr⟩ := padicFract_spec x
  have hx : x = (padicFract x : ℚ_[p]) + (x - padicFract x) := by ring
  rw [hx, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h1 _ hxr, (weilChiP_eq_one_iff _).2 hxr,
    h2 _ hr, weilChiP_pFrac hr]

/-- **Weil, IV.§2, text p. 66–67** (the basic character of $\mathbb Q_{\mathbb A}$): $\chi_\infty(x)=e(-x)$, each
$\chi_p$ has kernel $\mathbb Z_p$ and equals $e(\xi)$ on $\mathbb Q(p)$, and $\chi=\chi_\infty\prod_p\chi_p$ is trivial on
$\mathbb Q$ (only finitely many factors differ from $1$). -/
@[kb "weil1973bnt" "Ch. IV, §2, text p.66-68 (the basic character of the adeles of Q; Q case)"]
theorem weil_IV_2_text66_basicChar :
    (∀ x : ℝ, weilChiInf x = 𝐞 (-x)) ∧
    (∀ (p : Nat.Primes) (x : ℚ_[p]), weilChiP p x = 1 ↔ ‖x‖ ≤ 1) ∧
    (∀ (p : Nat.Primes) (r : ℚ), IsPFrac p r → weilChiP p (r : ℚ_[p]) = 𝐞 (r : ℝ)) ∧
    ∀ r : ℚ, weilChiInf (r : ℝ) * ∏ᶠ p : Nat.Primes, weilChiP p (r : ℚ_[p]) = 1 := by
  refine ⟨fun _ => rfl, fun p x => weilChiP_eq_one_iff x, fun p r hr => weilChiP_pFrac hr, fun r => ?_⟩
  have h := fourierChar_mul_finprod_psiP (-r)
  have e : ∀ p : Nat.Primes, psiP (p := p) (((-r : ℚ)) : ℚ_[p]) = weilChiP p (r : ℚ_[p]) := by
    intro p; rw [weilChiP_apply]; push_cast; rfl
  simp only [e] at h
  rw [weilChiInf_apply]
  simpa using h

end NumberFieldKB.WeilBNT
