import Mathlib.LinearAlgebra.SpecialLinearGroup
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Ring.Lemmas
import QuadFormsKB.Citation

/-!
# Milne, *Elliptic Curves*, Chapter V, Lemma 4.15: Hermite normal form of $2 \times 2$ integer matrices

Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, Lemma 4.15 (pdf p. 211).

**Deviation.** As printed, the lemma reads "For any $A \in M_2(\mathbb Z)$
there exists a $U \in M_2(\mathbb Z)$ such that $UA = \begin{pmatrix} a & b \\ 0 & d\end{pmatrix}$, $ad = n$,
$a \ge 1$, $0 \le b < d$; moreover $a, b, d$ are uniquely determined": the hypothesis $\det A = n$ ($n \ge 1$) and the
condition that $U$ be invertible ($\det U = 1$, as in the proof) are missing. Without them the uniqueness fails
(take $U$ of determinant $2$). The statement below has $\det A = n \ge 1$ and $U \in \mathrm{SL}_2(\mathbb Z)$.
-/

open Matrix

namespace NumberFieldKB.MilneEC.Vb

/-- The triples $(a, b, d)$ of Milne, *EC*, V, Lemma 4.15: $ad = n$, $a \ge 1$, $0 \le b < d$. -/
def HermiteTriple (n : ℕ) (t : ℤ × ℤ × ℤ) : Prop :=
  t.1 * t.2.2 = n ∧ 1 ≤ t.1 ∧ 0 ≤ t.2.1 ∧ t.2.1 < t.2.2

/-- The upper triangular matrix $\begin{pmatrix} a & b \\ 0 & d\end{pmatrix}$ of a triple $(a, b, d)$. -/
def hermiteMatrix (t : ℤ × ℤ × ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![t.1, t.2.1; 0, t.2.2]

/-- **Lemma 4.15, existence** (Milne, *EC*, V, Lemma 4.15, p. 211): for $A \in M_2(\mathbb Z)$ with
$\det A = n \ge 1$ there is $U \in \mathrm{SL}_2(\mathbb Z)$ with $UA = \begin{pmatrix} a & b \\ 0 & d\end{pmatrix}$,
$ad = n$, $a \ge 1$, $0 \le b < d$. (Hypothesis $\det A = n$ and $U$ unimodular added; see the module docstring.) -/
@[kb "milne2006ec" "Ch. V, Lemma 4.15 (pdf p. 211): existence"]
theorem lemma_4_15_exists {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det = n) :
    ∃ (U : SpecialLinearGroup (Fin 2) ℤ) (t : ℤ × ℤ × ℤ), HermiteTriple n t ∧ (U : Matrix (Fin 2) (Fin 2) ℤ) * A =
      hermiteMatrix t := by
  rw [Matrix.eta_fin_two A] at hA ⊢
  generalize A 0 0 = a at *
  generalize A 0 1 = b at *
  generalize A 1 0 = c at *
  generalize A 1 1 = d at *
  rw [Matrix.det_fin_two_of] at hA
  have hg : (a.gcd c : ℤ) ≠ 0 := by
    intro h
    have h' := Int.gcd_eq_zero_iff.mp (by exact_mod_cast h)
    rw [h'.1, h'.2] at hA
    have : (n : ℤ) = 0 := by linarith
    omega
  have hgpos : 0 < (a.gcd c : ℤ) := lt_of_le_of_ne (by positivity) (Ne.symm hg)
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left (a := a) (b := c)
  obtain ⟨c', hc'⟩ := Int.gcd_dvd_right (a := a) (b := c)
  have hbez := Int.gcd_eq_gcd_ab a c
  generalize (a.gcd c : ℤ) = g at *
  generalize Int.gcdA a c = r at *
  generalize Int.gcdB a c = s at *
  have h1 : r * a' + s * c' = 1 := by
    apply mul_left_cancel₀ hg
    rw [ha', hc'] at hbez
    linarith
  have hdet : g * (a' * d - c' * b) = n := by
    rw [← hA, ha', hc']; ring
  have hd : 0 < a' * d - c' * b := by
    have : (0:ℤ) < n := by exact_mod_cast hn
    by_contra hh
    push Not at hh
    nlinarith
  generalize hd' : a' * d - c' * b = d' at *
  subst ha' hc'
  let U₀ : SpecialLinearGroup (Fin 2) ℤ := ⟨!![r, s; -c', a'], by
    rw [Matrix.det_fin_two_of]; linarith⟩
  let q : ℤ := (r * b + s * d) / d'
  let M2 : SpecialLinearGroup (Fin 2) ℤ := ⟨!![1, -q; 0, 1], by
    rw [Matrix.det_fin_two_of]; ring⟩
  refine ⟨M2 * U₀, (g, (r * b + s * d) % d', d'), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa [mul_comm] using hdet
  · show 1 ≤ g
    omega
  · exact Int.emod_nonneg _ hd.ne'
  · exact Int.emod_lt_of_pos _ hd
  · have hq : (r * b + s * d) % d' = r * b + s * d - d' * q := by
      simp only [q]; rw [Int.emod_def]
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M2, U₀, hermiteMatrix, Matrix.mul_apply, Fin.sum_univ_two, hq] <;>
      first | ring1 | linear_combination g * h1 | linear_combination (-q) * hd' |
        linear_combination q * hd' | linear_combination hd' 

/-- **Lemma 4.15, uniqueness** (Milne, *EC*, V, Lemma 4.15, p. 211): the integers $a, b, d$ are uniquely
determined by $A$: if $UA$ and $U'A$ ($U, U' \in \mathrm{SL}_2(\mathbb Z)$) are both of the stated form, the
triples coincide. -/
@[kb "milne2006ec" "Ch. V, Lemma 4.15 (pdf p. 211): uniqueness"]
theorem lemma_4_15_unique {n : ℕ} (A : Matrix (Fin 2) (Fin 2) ℤ) (_hA : A.det = n)
    (U U' : SpecialLinearGroup (Fin 2) ℤ) {t t' : ℤ × ℤ × ℤ} (ht : HermiteTriple n t) (ht' : HermiteTriple n t')
    (hU : (U : Matrix (Fin 2) (Fin 2) ℤ) * A = hermiteMatrix t)
    (hU' : (U' : Matrix (Fin 2) (Fin 2) ℤ) * A = hermiteMatrix t') : t = t' := by
  obtain ⟨h1, h2, h3, h4⟩ := ht
  obtain ⟨h1', h2', h3', h4'⟩ := ht'
  obtain ⟨a, b, d⟩ := t
  obtain ⟨a', b', d'⟩ := t'
  simp only at h1 h2 h3 h4 h1' h2' h3' h4'
  have hV : (U' * U⁻¹ : SpecialLinearGroup (Fin 2) ℤ).1 * hermiteMatrix (a, b, d)
      = hermiteMatrix (a', b', d') := by
    rw [← hU, ← hU', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.adjugate _)]
    have : Matrix.adjugate (U : Matrix (Fin 2) (Fin 2) ℤ) * (U : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [Matrix.adjugate_mul, U.2]; simp
    rw [this, Matrix.one_mul]
  have hdet := (U' * U⁻¹ : SpecialLinearGroup (Fin 2) ℤ).2
  generalize (U' * U⁻¹ : SpecialLinearGroup (Fin 2) ℤ).1 = V at hV hdet
  rw [Matrix.eta_fin_two V] at hV hdet
  generalize V 0 0 = p at *
  generalize V 0 1 = q at *
  generalize V 1 0 = r at *
  generalize V 1 1 = s at *
  rw [Matrix.det_fin_two_of] at hdet
  simp only [hermiteMatrix] at hV
  have e00 := congrFun (congrFun hV 0) 0
  have e01 := congrFun (congrFun hV 0) 1
  have e10 := congrFun (congrFun hV 1) 0
  have e11 := congrFun (congrFun hV 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hr : r = 0 := by
    rcases e10 with h | h
    · exact h
    · omega
  subst hr
  have hps : p * s = 1 := by linarith
  have hp : p = 1 := by
    have : 0 < p := by
      by_contra hh; push Not at hh; nlinarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hps with h | h <;> omega
  subst hp
  have hs : s = 1 := by linarith
  subst hs
  have hq : q = 0 := by
    by_contra hh
    rcases lt_or_gt_of_ne hh with h | h <;> nlinarith
  subst hq
  simp only [Prod.mk.injEq]
  refine ⟨by linarith, by linarith, by linarith⟩

end NumberFieldKB.MilneEC.Vb
