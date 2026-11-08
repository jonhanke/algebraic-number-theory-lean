import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Chapter 7: Newton's polygon

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Setting (Milne p. 125): $K$ is complete with respect to a discrete (nonarchimedean) absolute value, and
$\operatorname{ord}$ is extended to an algebraic closure $K^{\mathrm{al}}$. Here $K$ is a complete nontrivially normed
field with ultrametric norm, $K^{\mathrm{al}}$ is `AlgebraicClosure K` with the unique extension of the norm, the
spectral norm (`spectralNorm K (AlgebraicClosure K)`, Mathlib), and $\operatorname{ord}(x) = -\log|x|$. Milne's
$\operatorname{ord}$ is normalized ($\operatorname{ord}(\pi) = 1$); ours is a positive multiple of it, which multiplies
every slope by the same constant and changes nothing in the statements. Milne writes
$f = a_0 X^n + a_1 X^{n-1} + \dots + a_n$ with $a_0 = 1$, so $a_i$ is the coefficient of $X^{n-i}$ and the points are
$P_i = (i, \operatorname{ord} a_i)$.

* **Newton polygon** (prose definition, p. 125; `newtonPolygon`): the lower convex hull of the points $P_i$.
* `newtonSegmentLength f s`: the $x$-length of the segment of slope $s$ of the Newton polygon ($0$ if there is none):
  the supporting line of slope $s$ touches the points $P_i$ with $i$ in an interval $[i_0, i_1]$, and the length is
  $i_1 - i_0$.
* **Proposition 7.44** (`prop_7_44`).
-/

open Polynomial
open scoped Classical

namespace NumberFieldKB.MilneANT

variable {K : Type*} [NontriviallyNormedField K]

/-- The indices $i \in \{0, \dots, n\}$ with $a_i \ne 0$, where $a_i$ is the coefficient of $X^{n-i}$ in $f$ and
$n = \deg f$. -/
noncomputable def newtonIndices (f : K[X]) : Finset ℕ :=
  (Finset.range (f.natDegree + 1)).filter fun i => f.coeff (f.natDegree - i) ≠ 0

/-- $\operatorname{ord}(a_i) = -\log|a_i|$ for the coefficient $a_i$ of $X^{n-i}$. -/
noncomputable def newtonOrd (f : K[X]) (i : ℕ) : ℝ := -Real.log ‖f.coeff (f.natDegree - i)‖

/-- **Newton polygon** (prose definition, Milne p. 125): the lower convex hull of the points
$P_i = (i, \operatorname{ord} a_i)$, $a_i \ne 0$, as a function on $[0, n]$: the supremum of the affine functions
$x \mapsto \lambda x + c$ lying below every $P_i$. -/
@[kb "milne2020ant" "v3.08, Ch. 7, definition of the Newton polygon, p. 125"]
noncomputable def newtonPolygon (f : K[X]) (x : ℝ) : ℝ :=
  ⨆ ℓ : {ℓ : ℝ × ℝ // ∀ i ∈ newtonIndices f, ℓ.1 * i + ℓ.2 ≤ newtonOrd f i}, ℓ.1.1 * x + ℓ.1.2

/-- The $x$-length of the segment of slope $s$ of the Newton polygon of $f$ (Milne p. 125): with
$m = \min_i (\operatorname{ord} a_i - s i)$, the supporting line $y = sx + m$ meets the points $P_i$ for $i$ in a set
$J$, and the length is $\max J - \min J$ ($0$ when the line meets the polygon in a single vertex). -/
noncomputable def newtonSegmentLength (f : K[X]) (s : ℝ) : ℕ :=
  if h : (newtonIndices f).Nonempty then
    let m := (newtonIndices f).inf' h fun i => newtonOrd f i - s * i
    let J := (newtonIndices f).filter fun i => newtonOrd f i - s * i = m
    if hJ : J.Nonempty then J.max' hJ - J.min' hJ else 0
  else 0

variable [IsUltrametricDist K] [CompleteSpace K]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Computing `newtonSegmentLength` from the extremal indices `A ≤ B` of the supporting line. -/
private lemma newtonSegmentLength_eq (f : K[X]) (s : ℝ) (A B : ℕ) (m : ℝ)
    (hA : A ∈ newtonIndices f) (hB : B ∈ newtonIndices f)
    (hAm : newtonOrd f A - s * A = m) (hBm : newtonOrd f B - s * B = m)
    (hge : ∀ i ∈ newtonIndices f, m ≤ newtonOrd f i - s * i)
    (hin : ∀ i ∈ newtonIndices f, newtonOrd f i - s * i = m → A ≤ i ∧ i ≤ B) :
    newtonSegmentLength f s = B - A := by
  have hne : (newtonIndices f).Nonempty := ⟨A, hA⟩
  have hinf : (newtonIndices f).inf' hne (fun i => newtonOrd f i - s * i) = m := by
    apply le_antisymm
    · exact hAm ▸ Finset.inf'_le _ hA
    · exact (Finset.le_inf'_iff hne _).2 hge
  have hAJ : A ∈ (newtonIndices f).filter fun i => newtonOrd f i - s * i = m := by
    simp [hA, hAm]
  have hBJ : B ∈ (newtonIndices f).filter fun i => newtonOrd f i - s * i = m := by
    simp [hB, hBm]
  have hJ : ((newtonIndices f).filter fun i => newtonOrd f i - s * i = m).Nonempty := ⟨A, hAJ⟩
  have hmin : ((newtonIndices f).filter fun i => newtonOrd f i - s * i = m).min' hJ = A := by
    apply le_antisymm (Finset.min'_le _ _ hAJ)
    apply Finset.le_min'
    intro i hi
    simp only [Finset.mem_filter] at hi
    exact (hin i hi.1 hi.2).1
  have hmax : ((newtonIndices f).filter fun i => newtonOrd f i - s * i = m).max' hJ = B := by
    apply le_antisymm
    · apply Finset.max'_le
      intro i hi
      simp only [Finset.mem_filter] at hi
      exact (hin i hi.1 hi.2).2
    · exact Finset.le_max' _ _ hBJ
  unfold newtonSegmentLength
  simp only [hne, ↓reduceDIte]
  simp only [hinf]
  simp only [hJ, ↓reduceDIte, hmin, hmax]

section Abstract

/-- Ultrametric strict bound for a finite sum. -/
private lemma norm_sum_lt_of_forall_lt {L : Type*} [AddCommMonoid L] {N : L → ℝ}
    (hna : IsNonarchimedean N) (h0 : N 0 = 0) {ι : Type*} (s : Finset ι) (g : ι → L) {c : ℝ}
    (hc : 0 < c) (h : ∀ j ∈ s, N (g j) < c) : N (∑ j ∈ s, g j) < c := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa [h0] using hc
  · exact lt_of_le_of_lt (hna.apply_sum_le_sup hne) ((Finset.sup'_lt_iff hne).2 h)

/-- Ultrametric bound for a finite sum. -/
private lemma norm_sum_le_of_forall_le {L : Type*} [AddCommMonoid L] {N : L → ℝ}
    (hna : IsNonarchimedean N) (h0 : N 0 = 0) {ι : Type*} (s : Finset ι) (g : ι → L) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ j ∈ s, N (g j) ≤ c) : N (∑ j ∈ s, g j) ≤ c := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa [h0] using hc
  · exact le_trans (hna.apply_sum_le_sup hne) ((Finset.sup'_le_iff hne _).2 h)

/-- Comparison of partial sums of `u` with the sum over the positive part `T`. -/
private lemma sum_cmp {ι : Type*} [Fintype ι] (u : ι → ℝ) (T T' : Finset ι)
    (hT : ∀ j, j ∈ T ↔ 0 < u j) (hT' : ∀ j, j ∈ T' ↔ 0 ≤ u j) (S : Finset ι) :
    ∑ j ∈ T', u j = ∑ j ∈ T, u j ∧ ∑ j ∈ S, u j ≤ ∑ j ∈ T, u j ∧
      (¬ T ⊆ S → ∑ j ∈ S, u j < ∑ j ∈ T, u j) ∧
      (¬ S ⊆ T' → ∑ j ∈ S, u j < ∑ j ∈ T, u j) := by
  classical
  have hsub : T ⊆ T' := fun j hj => (hT' j).2 (le_of_lt ((hT j).1 hj))
  have hTT' : ∑ j ∈ T', u j = ∑ j ∈ T, u j := by
    symm
    apply Finset.sum_subset hsub
    intro j hj hjT
    have h1 := (hT' j).1 hj
    have h2 : ¬ 0 < u j := fun h => hjT ((hT j).2 h)
    linarith [not_lt.1 h2]
  have e : ∀ A : Finset ι, ∑ j ∈ A, u j = ∑ j, if j ∈ A then u j else 0 := by
    intro A
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hle : ∀ B : Finset ι, (∀ j, j ∈ B → 0 ≤ u j) → (∀ j, j ∉ B → u j ≤ 0) →
      ∑ j ∈ S, u j ≤ ∑ j ∈ B, u j := by
    intro B h1 h2
    rw [e S, e B]
    apply Finset.sum_le_sum
    intro j _
    by_cases hS : j ∈ S <;> by_cases hB : j ∈ B <;> simp [hS, hB]
    · exact h2 j hB
    · exact h1 j hB
  have hT0 : ∀ j, j ∈ T → 0 ≤ u j := fun j hj => le_of_lt ((hT j).1 hj)
  have hT1 : ∀ j, j ∉ T → u j ≤ 0 := fun j hj => not_lt.1 (fun h => hj ((hT j).2 h))
  have hT'0 : ∀ j, j ∈ T' → 0 ≤ u j := fun j hj => (hT' j).1 hj
  have hT'1 : ∀ j, j ∉ T' → u j ≤ 0 := fun j hj => le_of_lt (not_le.1 (fun h => hj ((hT' j).2 h)))
  refine ⟨hTT', hle T hT0 hT1, ?_, ?_⟩
  · intro hns
    obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.1 hns
    rw [e S, e T]
    apply Finset.sum_lt_sum
    · intro k _
      by_cases hS : k ∈ S <;> by_cases hB : k ∈ T <;> simp [hS, hB]
      · exact hT1 k hB
      · exact hT0 k hB
    · refine ⟨j, Finset.mem_univ _, ?_⟩
      simp [hjS, hjT]
      exact (hT j).1 hjT
  · intro hns
    obtain ⟨j, hjS, hjT⟩ := Finset.not_subset.1 hns
    rw [← hTT', e S, e T']
    apply Finset.sum_lt_sum
    · intro k _
      by_cases hS : k ∈ S <;> by_cases hB : k ∈ T' <;> simp [hS, hB]
      · exact hT'1 k hB
      · exact hT'0 k hB
    · refine ⟨j, Finset.mem_univ _, ?_⟩
      simp [hjS, hjT]
      exact not_le.1 (fun h => hjT ((hT' j).2 h))

/-- Dominant-term bounds for the elementary symmetric functions of elements `v j` of a field with a
nonarchimedean multiplicative norm `N`, relative to a threshold `t > 0`: with `T = {N (v j) > t}` and
`T' = {N (v j) ≥ t}`, `N (e_i) ≤ t^i e^M`, with strict inequality for `i < #T` or `i > #T'`, and
equality for `i = #T` and `i = #T'`. -/
private lemma esymm_norm_bounds {L : Type*} [Field L] {N : L → ℝ}
    (hna : IsNonarchimedean N) (h0 : N 0 = 0) (hneg : ∀ a, N (-a) = N a)
    (hmul : ∀ a b, N (a * b) = N a * N b) (hpos : ∀ a, a ≠ 0 → 0 < N a)
    {ι : Type*} [Fintype ι] (v : ι → L) (hv : ∀ j, v j ≠ 0) {t : ℝ} (ht : 0 < t) :
    ∃ M : ℝ,
      (∀ i, N ((Finset.univ.val.map v).esymm i) ≤ t ^ i * Real.exp M) ∧
      (∀ i, (i < (Finset.univ.filter fun j => t < N (v j)).card ∨
          (Finset.univ.filter fun j => t ≤ N (v j)).card < i) →
        N ((Finset.univ.val.map v).esymm i) < t ^ i * Real.exp M) ∧
      N ((Finset.univ.val.map v).esymm (Finset.univ.filter fun j => t < N (v j)).card) =
        t ^ (Finset.univ.filter fun j => t < N (v j)).card * Real.exp M ∧
      N ((Finset.univ.val.map v).esymm (Finset.univ.filter fun j => t ≤ N (v j)).card) =
        t ^ (Finset.univ.filter fun j => t ≤ N (v j)).card * Real.exp M := by
  classical
  set T : Finset ι := Finset.univ.filter fun j => t < N (v j) with hTdef
  set T' : Finset ι := Finset.univ.filter fun j => t ≤ N (v j) with hT'def
  set u : ι → ℝ := fun j => Real.log (N (v j)) - Real.log t with hu
  have hNpos : ∀ j, 0 < N (v j) := fun j => hpos _ (hv j)
  have hT : ∀ j, j ∈ T ↔ 0 < u j := by
    intro j
    simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and, hu, sub_pos]
    exact (Real.log_lt_log_iff ht (hNpos j)).symm
  have hT' : ∀ j, j ∈ T' ↔ 0 ≤ u j := by
    intro j
    simp only [hT'def, Finset.mem_filter, Finset.mem_univ, true_and, hu, sub_nonneg]
    exact (Real.log_le_log_iff ht (hNpos j)).symm
  have hN1 : N 1 = 1 := by
    have h := hmul 1 1
    have hp := hpos 1 one_ne_zero
    simp only [mul_one] at h
    nlinarith
  have hprod : ∀ S : Finset ι, N (∏ j ∈ S, v j) = ∏ j ∈ S, N (v j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [hN1]
    | insert a S ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, hmul, ih]
  have hS : ∀ S : Finset ι, N (∏ j ∈ S, v j) = t ^ S.card * Real.exp (∑ j ∈ S, u j) := by
    intro S
    rw [hprod, Real.exp_sum, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    simp only [hu]
    rw [Real.exp_sub, Real.exp_log (hNpos j), Real.exp_log ht]
    field_simp
  have hes : ∀ i, (Finset.univ.val.map v).esymm i =
      ∑ S ∈ Finset.univ.powersetCard i, ∏ j ∈ S, v j := fun i => Finset.esymm_map_val v _ i
  refine ⟨∑ j ∈ T, u j, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hes]
    apply norm_sum_le_of_forall_le hna h0 _ _ (by positivity)
    intro S hSm
    rw [hS, (Finset.mem_powersetCard.1 hSm).2]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (sum_cmp u T T' hT hT' S).2.1) (by positivity)
  · intro i hi
    rw [hes]
    apply norm_sum_lt_of_forall_lt hna h0 _ _ (by positivity)
    intro S hSm
    have hc := (Finset.mem_powersetCard.1 hSm).2
    rw [hS, hc]
    have hlt : ∑ j ∈ S, u j < ∑ j ∈ T, u j := by
      rcases hi with hi | hi
      · apply (sum_cmp u T T' hT hT' S).2.2.1
        intro hsub
        have := Finset.card_le_card hsub
        omega
      · apply (sum_cmp u T T' hT hT' S).2.2.2
        intro hsub
        have := Finset.card_le_card hsub
        omega
    have := Real.exp_lt_exp.2 hlt
    have ht' : 0 < t ^ i := by positivity
    nlinarith
  · rw [hes]
    have := Finset.mem_powersetCard.2 (⟨Finset.subset_univ T, rfl⟩ : T ⊆ Finset.univ ∧ T.card = T.card)
    rw [hna.apply_sum_eq_of_lt (fun S => ∏ j ∈ S, v j) hneg this]
    · rw [hS]
    · intro S hSm hne
      have hc := (Finset.mem_powersetCard.1 hSm).2
      rw [hS, hS, hc]
      have hlt : ∑ j ∈ S, u j < ∑ j ∈ T, u j := by
        apply (sum_cmp u T T' hT hT' S).2.2.1
        intro hsub
        exact hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
      have := Real.exp_lt_exp.2 hlt
      have ht' : 0 < t ^ T.card := by positivity
      nlinarith
  · rw [hes]
    have := Finset.mem_powersetCard.2 (⟨Finset.subset_univ T', rfl⟩ : T' ⊆ Finset.univ ∧ T'.card = T'.card)
    rw [hna.apply_sum_eq_of_lt (fun S => ∏ j ∈ S, v j) hneg this]
    · rw [hS, (sum_cmp u T T' hT hT' T).1]
    · intro S hSm hne
      have hc := (Finset.mem_powersetCard.1 hSm).2
      rw [hS, hS, hc]
      have hlt : ∑ j ∈ S, u j < ∑ j ∈ T', u j := by
        rw [(sum_cmp u T T' hT hT' S).1]
        apply (sum_cmp u T T' hT hT' S).2.2.2
        intro hsub
        exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))
      have := Real.exp_lt_exp.2 hlt
      have ht' : 0 < t ^ T'.card := by positivity
      nlinarith

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Grouping roots by irreducible factors: for a predicate `P` depending only on the minimal
polynomial, the product of `X - α` over the roots satisfying `P` is defined over `K`. -/
private lemma exists_poly_of_filter_roots (f : K[X]) (hf : f.Monic)
    (P : AlgebraicClosure K → Prop) (hP : ∀ α β, minpoly K α = minpoly K β → (P α ↔ P β)) :
    ∃ g : K[X], g.map (algebraMap K (AlgebraicClosure K)) =
      (((f.map (algebraMap K (AlgebraicClosure K))).roots.filter P).map
        (fun α => X - C α)).prod := by
  have key : ∀ Q : Multiset K[X], (∀ q ∈ Q, q.Monic ∧ Irreducible q) →
      ∃ g : K[X], g.map (algebraMap K (AlgebraicClosure K)) =
        ((((Q.map fun (q : K[X]) => q.map (algebraMap K (AlgebraicClosure K))).prod).roots.filter P).map
          (fun α => X - C α)).prod := by
    intro Q
    induction Q using Multiset.induction with
    | empty => intro _; exact ⟨1, by simp⟩
    | cons q Q ih =>
      intro hQ
      obtain ⟨g, hg⟩ := ih (fun r hr => hQ r (Multiset.mem_cons_of_mem hr))
      obtain ⟨hqm, hqi⟩ := hQ q (Multiset.mem_cons_self _ _)
      have hqm' : (q.map (algebraMap K (AlgebraicClosure K))).Monic := hqm.map _
      have hrm : ((Q.map fun (q : K[X]) => q.map (algebraMap K (AlgebraicClosure K))).prod).Monic := by
        exact Polynomial.monic_multiset_prod_of_monic _ _
          (fun r hr => (hQ r (Multiset.mem_cons_of_mem hr)).1.map _)
      rw [Multiset.map_cons, Multiset.prod_cons,
        Polynomial.roots_mul (mul_ne_zero hqm'.ne_zero hrm.ne_zero), Multiset.filter_add,
        Multiset.map_add, Multiset.prod_add, ← hg]
      by_cases h : ∃ α ∈ (q.map (algebraMap K (AlgebraicClosure K))).roots, P α
      · obtain ⟨α, hα, hPα⟩ := h
        have hmin : ∀ β ∈ (q.map (algebraMap K (AlgebraicClosure K))).roots,
            minpoly K β = minpoly K α := by
          intro β hβ
          have h1 := (Polynomial.mem_roots hqm'.ne_zero).1 hβ
          have h2 := (Polynomial.mem_roots hqm'.ne_zero).1 hα
          rw [Polynomial.IsRoot, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def] at h1 h2
          exact (minpoly.eq_of_irreducible_of_monic hqi h1 hqm).symm.trans
            (minpoly.eq_of_irreducible_of_monic hqi h2 hqm)
        have hall : (q.map (algebraMap K (AlgebraicClosure K))).roots.filter P =
            (q.map (algebraMap K (AlgebraicClosure K))).roots := by
          apply Multiset.filter_eq_self.2
          intro β hβ
          exact (hP β α (hmin β hβ)).2 hPα
        refine ⟨q * g, ?_⟩
        rw [hall, Polynomial.map_mul, hg]
        congr 1
        exact (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hqm'
          (Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _))).symm
      · refine ⟨g, ?_⟩
        have hnone : (q.map (algebraMap K (AlgebraicClosure K))).roots.filter P = 0 := by
          apply Multiset.filter_eq_nil.2
          intro β hβ hPβ
          exact h ⟨β, hβ, hPβ⟩
        rw [hnone, hg]
        simp
  have hf0 : f ≠ 0 := hf.ne_zero
  have hQ : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors f, q.Monic ∧ Irreducible q := by
    intro q hq
    refine ⟨?_, UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq⟩
    have hq0 : q ≠ 0 := (UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq).ne_zero
    rw [← UniqueFactorizationMonoid.normalize_normalized_factor q hq]
    exact Polynomial.monic_normalize hq0
  have hprod : (UniqueFactorizationMonoid.normalizedFactors f).prod = f := by
    apply Polynomial.eq_of_monic_of_associated _ hf
      (UniqueFactorizationMonoid.prod_normalizedFactors hf0)
    rw [← Multiset.map_id (UniqueFactorizationMonoid.normalizedFactors f)]
    exact Polynomial.monic_multiset_prod_of_monic _ _ (fun q hq => (hQ q hq).1)
  obtain ⟨g, hg⟩ := key _ hQ
  refine ⟨g, ?_⟩
  rw [hg, ← Polynomial.map_multiset_prod, hprod]

end Abstract

/-- **Proposition 7.44.** Let $K$ (complete for a discrete absolute value) have characteristic zero and let
$f \in K[X]$ be monic. If the Newton polygon of $f$ has a segment of $x$-length $n_i$ and slope $s_i$, then $f$ has
exactly $n_i$ roots $\alpha$ in $K^{\mathrm{al}}$ (with multiplicity) with $\operatorname{ord}(\alpha) = s_i$; and the
polynomial $f_i = \prod_{\operatorname{ord}\alpha = s_i} (X - \alpha)$ has coefficients in $K$.

Stated for every slope $s$ (both sides are $0$ when $s$ is not a slope). Hypothesis made explicit: $f(0) \ne 0$
(Milne's points $P_i$ need $\operatorname{ord}(a_n) < \infty$; a root $0$ has $\operatorname{ord} = \infty$). The
hypothesis that the absolute value is discrete is not needed. -/
@[kb "milne2020ant" "v3.08, Prop. 7.44, p. 125"]
theorem prop_7_44 [CharZero K] (f : K[X]) (hf : f.Monic) (h0 : f.coeff 0 ≠ 0) (s : ℝ) :
    ((f.map (algebraMap K (AlgebraicClosure K))).roots.filter
        (fun α => -Real.log (spectralNorm K (AlgebraicClosure K) α) = s)).card = newtonSegmentLength f s ∧
    ∃ g : K[X], g.map (algebraMap K (AlgebraicClosure K)) =
      (((f.map (algebraMap K (AlgebraicClosure K))).roots.filter
        (fun α => -Real.log (spectralNorm K (AlgebraicClosure K) α) = s)).map (fun α => X - C α)).prod := by
  classical
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  set N : L → ℝ := spectralNorm K L with hN
  have hna : IsNonarchimedean N := isNonarchimedean_spectralNorm
  have hN0 : N 0 = 0 := spectralNorm_zero
  have hneg : ∀ a, N (-a) = N a := fun a => spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)
  have hmul : ∀ a b, N (a * b) = N a * N b := fun a b => spectralAlgNorm_mul a b
  have hpos : ∀ a, a ≠ 0 → 0 < N a :=
    fun a ha => spectralNorm_zero_lt ha (Algebra.IsAlgebraic.isAlgebraic _)
  have hext : ∀ a : K, N (ι a) = ‖a‖ := fun a => spectralNorm_extends a
  have hmin : ∀ α β : L, minpoly K α = minpoly K β → N α = N β := by
    intro α β h
    simp only [hN, spectralNorm, h]
  -- the predicate
  set P : L → Prop := fun α => -Real.log (N α) = s with hPdef
  -- Part A
  have hA : ∃ g : K[X], g.map ι = (((f.map ι).roots.filter P).map (fun α => X - C α)).prod := by
    apply exists_poly_of_filter_roots f hf P
    intro α β h
    simp only [hPdef, hmin α β h]
  refine ⟨?_, hA⟩
  -- Part B
  have hmon : (f.map ι).Monic := hf.map _
  have hcard : Multiset.card (f.map ι).roots = f.natDegree := by
    rw [← hf.natDegree_map ι]
    exact Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _)
  have hrootne : ∀ α ∈ (f.map ι).roots, α ≠ 0 := by
    intro α hα h
    subst h
    have h1 := (Polynomial.mem_roots hmon.ne_zero).1 hα
    rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at h1
    exact h0 ((map_eq_zero ι).1 h1)
  -- enumerate the roots
  set l : List L := (f.map ι).roots.toList with hl
  set v : Fin l.length → L := l.get with hv
  have hR : (f.map ι).roots = Finset.univ.val.map v := by
    rw [Fin.univ_val_map, hv, List.ofFn_get]
    simp [hl]
  have hvne : ∀ j, v j ≠ 0 := by
    intro j
    apply hrootne
    rw [← Multiset.mem_toList]
    exact List.get_mem _ _
  have hn : Fintype.card (Fin l.length) = f.natDegree := by
    simp [hl, hcard]
  set t : ℝ := Real.exp (-s) with htdef
  have ht : 0 < t := Real.exp_pos _
  have hPt : ∀ j, P (v j) ↔ N (v j) = t := by
    intro j
    simp only [hPdef]
    constructor
    · intro h
      have : Real.log (N (v j)) = -s := by linarith
      rw [htdef, ← this, Real.exp_log (hpos _ (hvne j))]
    · intro h
      rw [h, htdef, Real.log_exp]; ring
  obtain ⟨M, hb1, hb2, hb3, hb4⟩ := esymm_norm_bounds hna hN0 hneg hmul hpos v hvne ht
  set T : Finset (Fin l.length) := Finset.univ.filter fun j => t < N (v j) with hTdef
  set T' : Finset (Fin l.length) := Finset.univ.filter fun j => t ≤ N (v j) with hT'def
  set E : Finset (Fin l.length) := Finset.univ.filter fun j => N (v j) = t with hEdef
  have hU : T' = T ∪ E := by
    ext j
    simp only [hTdef, hT'def, hEdef, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro h
      rcases h.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact h.le
      · exact h.ge
  have hdisj : Disjoint T E := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [hTdef, hEdef, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    linarith
  have hcardE : E.card = T'.card - T.card := by
    rw [hU, Finset.card_union_of_disjoint hdisj]; omega
  have hfilt : ((f.map ι).roots.filter P).card = E.card := by
    rw [hR, Multiset.filter_map, Multiset.card_map, hEdef, Finset.card_def, Finset.filter_val]
    congr 1
    apply Multiset.filter_congr
    intro j _
    exact hPt j
  rw [hfilt, hcardE]
  -- coefficients
  have hcoef : ∀ i ≤ f.natDegree, ‖f.coeff (f.natDegree - i)‖ =
      N ((Finset.univ.val.map v).esymm i) := by
    intro i hi
    have hsp : (f.map ι).Splits := IsAlgClosed.splits _
    have hV := Polynomial.coeff_eq_esymm_roots_of_splits hsp (k := f.natDegree - i)
      (by rw [hf.natDegree_map ι]; omega)
    rw [hf.natDegree_map ι, hmon.leadingCoeff, Polynomial.coeff_map,
      show f.natDegree - (f.natDegree - i) = i by omega, hR, one_mul] at hV
    rw [← hext, hV]
    rcases neg_one_pow_eq_or L i with h | h
    · rw [h, one_mul]
    · rw [h, neg_one_mul, hneg]
  have hlogt : ∀ i : ℕ, Real.log (t ^ i * Real.exp M) = -s * i + M := by
    intro i
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, htdef, Real.log_exp,
      Real.log_exp]
    ring
  have hle : ∀ i ∈ newtonIndices f, -M ≤ newtonOrd f i - s * i := by
    intro i hi
    simp only [newtonIndices, Finset.mem_filter, Finset.mem_range] at hi
    have hc := hcoef i (by omega)
    have hcpos : 0 < ‖f.coeff (f.natDegree - i)‖ := norm_pos_iff.2 hi.2
    have := hb1 i
    rw [← hc] at this
    have := Real.log_le_log hcpos this
    rw [hlogt] at this
    unfold newtonOrd
    linarith
  have hlt : ∀ i ∈ newtonIndices f, (i < T.card ∨ T'.card < i) → -M < newtonOrd f i - s * i := by
    intro i hi hio
    simp only [newtonIndices, Finset.mem_filter, Finset.mem_range] at hi
    have hc := hcoef i (by omega)
    have hcpos : 0 < ‖f.coeff (f.natDegree - i)‖ := norm_pos_iff.2 hi.2
    have := hb2 i hio
    rw [← hc] at this
    have := Real.log_lt_log hcpos this
    rw [hlogt] at this
    unfold newtonOrd
    linarith
  have hTn : T.card ≤ f.natDegree := by
    rw [← hn]; exact (Finset.card_le_univ _)
  have hT'n : T'.card ≤ f.natDegree := by
    rw [← hn]; exact (Finset.card_le_univ _)
  have hTle : T.card ≤ T'.card := Finset.card_le_card (by rw [hU]; exact Finset.subset_union_left)
  have hmem : ∀ k, k ≤ f.natDegree → N ((Finset.univ.val.map v).esymm k) = t ^ k * Real.exp M →
      k ∈ newtonIndices f ∧ newtonOrd f k - s * k = -M := by
    intro k hk hEq
    have hc := hcoef k hk
    have hcpos : 0 < ‖f.coeff (f.natDegree - k)‖ := by
      rw [hc, hEq]; positivity
    have hne : f.coeff (f.natDegree - k) ≠ 0 := norm_pos_iff.1 hcpos
    refine ⟨by simp [newtonIndices, hne]; omega, ?_⟩
    have := congrArg Real.log (hc.trans hEq)
    rw [hlogt] at this
    unfold newtonOrd
    linarith
  obtain ⟨hAi, hAm⟩ := hmem _ hTn hb3
  obtain ⟨hBi, hBm⟩ := hmem _ hT'n hb4
  exact (newtonSegmentLength_eq f s T.card T'.card (-M) hAi hBi hAm hBm hle
    (fun i hi he => by
      by_contra hcon
      have := hlt i hi (by omega)
      linarith)).symm

end NumberFieldKB.MilneANT
