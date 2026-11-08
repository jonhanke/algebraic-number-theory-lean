import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Lemma 2.44 and Remark 2.45: triangular and Hermite normal forms

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), pp. 41–42; bib key `milne2020ant`.

* `IsElementaryRowOp`: the matrices of Milne's row operations (r1) "add a multiple of one row to another" (a
  transvection `Matrix.transvection i j c`, $i \ne j$, which adds $c$ times row $j$ to row $i$ when multiplied on the
  left) and (r2) "swap two rows" (the permutation matrix of a transposition).
* **Lemma 2.44** (`lemma_2_44`): over a Euclidean domain every square matrix becomes upper triangular after
  finitely many operations (r1), (r2).
* **Remark 2.45 (a)** (`remark_2_45_a_upper`, `remark_2_45_a_lower`): $UM$ upper triangular, and $MU$ lower
  triangular, for some invertible $U$.
* **Hermite normal form** (`IsHermiteNormalForm`, a definition in prose) and **Remark 2.45 (b)**
  (`remark_2_45_b_exists`, `remark_2_45_b_unique`): for $M \in M_n(\mathbb Z)$ with $\det M \ne 0$ there is a unique
  $T = UM$, $U \in \mathrm{GL}_n(\mathbb Z)$, that is upper triangular with $t_{ii} > 0$ and
  $0 \le t_{ij} < t_{jj}$ for $i < j$.

Upper triangular is Mathlib's `Matrix.BlockTriangular M id` ($M_{ij} = 0$ for $j < i$); lower triangular is
`Matrix.BlockTriangular M OrderDual.toDual`. Indices are $0$-based (`Fin n`).

*Erratum:* in Remark 2.45 (b) Milne writes "It is called the Hermite normal form of $A$"; it is the Hermite normal
form of the matrix $M$ ($A$ there denotes the ring $\mathbb Z$).
-/

open Matrix

namespace NumberFieldKB.MilneANT

/-- The matrices of Milne's elementary row operations of types (r1) and (r2) on $n \times n$ matrices over a ring
$A$: a transvection $1 + cE_{ij}$ with $i \ne j$ (left multiplication adds $c$ times row $j$ to row $i$), or the
permutation matrix of a transposition $(i\ j)$ (left multiplication swaps rows $i$ and $j$). -/
def IsElementaryRowOp {n : ℕ} {A : Type*} [CommRing A] (E : Matrix (Fin n) (Fin n) A) : Prop :=
  (∃ (i j : Fin n) (c : A), i ≠ j ∧ E = transvection i j c) ∨
    ∃ i j : Fin n, E = (Equiv.swap i j).permMatrix A

section Aux

variable {n : ℕ} {A : Type*} [EuclideanDomain A]

/-- `N` is reached from `M` by finitely many elementary row operations. -/
private def Reach (M N : Matrix (Fin n) (Fin n) A) : Prop :=
  ∃ l : List (Matrix (Fin n) (Fin n) A), (∀ E ∈ l, IsElementaryRowOp E) ∧ l.prod * M = N

private lemma Reach.refl (M : Matrix (Fin n) (Fin n) A) : Reach M M := ⟨[], by simp, by simp⟩

private lemma Reach.trans {M N P : Matrix (Fin n) (Fin n) A} (h1 : Reach M N) (h2 : Reach N P) :
    Reach M P := by
  obtain ⟨l1, a1, rfl⟩ := h1
  obtain ⟨l2, a2, rfl⟩ := h2
  refine ⟨l2 ++ l1, ?_, by simp [Matrix.mul_assoc]⟩
  intro E hE
  rcases List.mem_append.1 hE with h | h
  · exact a2 E h
  · exact a1 E h

private lemma Reach.transv (M : Matrix (Fin n) (Fin n) A) {i j : Fin n} (hij : i ≠ j) (c : A) :
    Reach M (transvection i j c * M) :=
  ⟨[transvection i j c], by
    intro E hE
    simp only [List.mem_singleton] at hE
    subst hE
    exact Or.inl ⟨i, j, c, hij, rfl⟩, by simp⟩

private lemma Reach.swap (M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    Reach M (M.submatrix (Equiv.swap i j) id) :=
  ⟨[(Equiv.swap i j).permMatrix A], by
    intro E hE
    simp only [List.mem_singleton] at hE
    subst hE
    exact Or.inr ⟨i, j, rfl⟩, by
    rw [List.prod_singleton]
    exact PEquiv.toMatrix_toPEquiv_mul _ _⟩

/-- Columns `< k` are already zero below the diagonal. -/
private def Inv (k : ℕ) (N : Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ i j : Fin n, j.val < k → j < i → N i j = 0

private lemma Inv.transv {k : ℕ} {N : Matrix (Fin n) (Fin n) A} (h : Inv k N) {i j : Fin n}
    (hi : k ≤ i.val) (hj : k ≤ j.val) (c : A) : Inv k (transvection i j c * N) := by
  intro a b hb hba
  by_cases ha : a = i
  · subst ha
    rw [transvection_mul_apply_same, h a b hb hba, h j b hb (by rw [Fin.lt_def]; omega)]
    simp
  · rw [transvection_mul_apply_of_ne i j a b ha]
    exact h a b hb hba

private lemma Inv.swap {k : ℕ} {N : Matrix (Fin n) (Fin n) A} (h : Inv k N) {i j : Fin n}
    (hi : k ≤ i.val) (hj : k ≤ j.val) : Inv k (N.submatrix (Equiv.swap i j) id) := by
  intro a b hb hba
  simp only [Matrix.submatrix_apply, id]
  apply h _ _ hb
  by_cases h1 : a = i
  · rw [h1, Equiv.swap_apply_left, Fin.lt_def]; omega
  by_cases h2 : a = j
  · rw [h2, Equiv.swap_apply_right, Fin.lt_def]; omega
  · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hba

private lemma clear_col (k : ℕ) (hk : k < n) (N : Matrix (Fin n) (Fin n) A) (hN : Inv k N) :
    ∃ N', Reach N N' ∧ Inv (k + 1) N' := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : Fin n, p.val = k := ⟨⟨k, hk⟩, rfl⟩
  have key : ∀ a : A, a ≠ 0 → ∀ (s : ℕ) (N : Matrix (Fin n) (Fin n) A), Inv k N → N p p = a →
      (Finset.univ.filter (fun i => p < i ∧ N i p ≠ 0)).card = s →
      ∃ N', Reach N N' ∧ Inv k N' ∧ ∀ i, p < i → N' i p = 0 := by
    intro a
    induction a using (@EuclideanDomain.r_wellFounded A _).induction with
    | _ a ih =>
    intro ha s
    induction s using Nat.strong_induction_on with
    | _ s ihs =>
    intro N hN hpa hcard
    by_cases hall : ∀ i, p < i → N i p = 0
    · exact ⟨N, Reach.refl N, hN, hall⟩
    push_neg at hall
    obtain ⟨i, hpi, hb⟩ := hall
    have hip : i ≠ p := hpi.ne'
    have hki : k ≤ i.val := by have := Fin.lt_def.1 hpi; omega
    obtain ⟨N1, hN1⟩ : ∃ N1, N1 = transvection i p (-(N i p / a)) * N := ⟨_, rfl⟩
    have hR1 : Reach N N1 := hN1 ▸ Reach.transv N hip _
    have hI1 : Inv k N1 := hN1 ▸ hN.transv hki (by omega) _
    have hN1p : N1 p p = a := by
      rw [hN1, transvection_mul_apply_of_ne i p p p hip.symm]; exact hpa
    have hN1i : N1 i p = N i p % a := by
      rw [hN1, transvection_mul_apply_same, hpa, EuclideanDomain.mod_eq_sub_mul_div]; ring
    have hN1o : ∀ r, r ≠ i → N1 r p = N r p := fun r hr => by
      rw [hN1, transvection_mul_apply_of_ne i p r p hr]
    by_cases hz : N i p % a = 0
    · have hsub : Finset.univ.filter (fun r => p < r ∧ N1 r p ≠ 0) ⊆
          Finset.univ.filter (fun r => p < r ∧ N r p ≠ 0) := by
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
        refine ⟨hr.1, ?_⟩
        by_cases hri : r = i
        · rw [hri]; exact hb
        · rw [← hN1o r hri]; exact hr.2
      have hcard1 : (Finset.univ.filter (fun r => p < r ∧ N1 r p ≠ 0)).card < s := by
        rw [← hcard]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset hsub]
        refine ⟨i, ?_, ?_⟩
        · simp [hpi, hb]
        · simp [hN1i, hz]
      obtain ⟨N', hR, hI, h0⟩ := ihs _ hcard1 N1 hI1 hN1p rfl
      exact ⟨N', hR1.trans hR, hI, h0⟩
    · obtain ⟨N2, hN2⟩ : ∃ N2, N2 = N1.submatrix (Equiv.swap p i) id := ⟨_, rfl⟩
      have hR2 : Reach N1 N2 := hN2 ▸ Reach.swap N1 p i
      have hI2 : Inv k N2 := hN2 ▸ hI1.swap (by omega) hki
      have hN2p : N2 p p = N i p % a := by
        rw [hN2, Matrix.submatrix_apply, Equiv.swap_apply_left]; exact hN1i
      have hlt := EuclideanDomain.mod_lt (N i p) ha
      obtain ⟨N', hR, hI, h0⟩ := ih _ hlt hz _ N2 hI2 hN2p rfl
      exact ⟨N', hR1.trans (hR2.trans hR), hI, h0⟩
  have C : ∃ N', Reach N N' ∧ Inv k N' ∧ ∀ i, p < i → N' i p = 0 := by
    by_cases hall : ∀ i, p < i → N i p = 0
    · exact ⟨N, Reach.refl N, hN, hall⟩
    push_neg at hall
    obtain ⟨i, hpi, hb⟩ := hall
    by_cases hz : N p p = 0
    · have hki : k ≤ i.val := by have := Fin.lt_def.1 hpi; omega
      obtain ⟨N2, hN2⟩ : ∃ N2, N2 = N.submatrix (Equiv.swap p i) id := ⟨_, rfl⟩
      have hN2p : N2 p p = N i p := by
        rw [hN2, Matrix.submatrix_apply, Equiv.swap_apply_left]; rfl
      have hI2 : Inv k N2 := hN2 ▸ hN.swap (by omega) hki
      obtain ⟨N', hR, hI, h0⟩ := key (N i p) hb _ N2 hI2 hN2p rfl
      exact ⟨N', (hN2 ▸ Reach.swap N p i : Reach N N2).trans hR, hI, h0⟩
    · exact key (N p p) hz _ N hN rfl rfl
  obtain ⟨N', hR, hI, h0⟩ := C
  refine ⟨N', hR, ?_⟩
  intro a b hb hba
  by_cases hbk : b.val < k
  · exact hI a b hbk hba
  · have hbp : b = p := Fin.ext (by omega)
    rw [hbp] at hba ⊢
    exact h0 a hba

private lemma tri_aux (M : Matrix (Fin n) (Fin n) A) :
    ∀ k, k ≤ n → ∃ N, Reach M N ∧ Inv k N := by
  intro k
  induction k with
  | zero => intro _; exact ⟨M, Reach.refl M, fun i j h => absurd h (by omega)⟩
  | succ k ih =>
    intro hk
    obtain ⟨N, hR, hI⟩ := ih (by omega)
    obtain ⟨N', hR', hI'⟩ := clear_col k (by omega) N hI
    exact ⟨N', hR.trans hR', hI'⟩

private lemma Inv.blockTri {N : Matrix (Fin n) (Fin n) A} (h : Inv n N) : N.BlockTriangular id :=
  fun i j hji => h i j j.isLt hji

private lemma isUnit_det_elem {E : Matrix (Fin n) (Fin n) A} (h : IsElementaryRowOp E) :
    IsUnit E.det := by
  rcases h with ⟨i, j, c, hij, rfl⟩ | ⟨i, j, rfl⟩
  · rw [det_transvection_of_ne _ _ hij]; exact isUnit_one
  · rw [det_permutation]; exact (Units.isUnit _).map (Int.castRingHom A)

private lemma isUnit_det_prod (l : List (Matrix (Fin n) (Fin n) A))
    (h : ∀ E ∈ l, IsElementaryRowOp E) : IsUnit l.prod.det := by
  induction l with
  | nil => simp
  | cons E l ih =>
    rw [List.prod_cons, det_mul]
    exact (isUnit_det_elem (h E (by simp))).mul (ih fun E' hE' => h E' (by simp [hE']))

end Aux

/-- **Lemma 2.44.** Let $A$ be a Euclidean domain and $M$ an $n \times n$ matrix over $A$. Then $M$ can be put into
upper triangular form by finitely many elementary row operations of the types (r1) (add a multiple of one row to
another) and (r2) (swap two rows): there are elementary matrices $E_1, \dots, E_k$ with $E_1 \cdots E_k M$ upper
triangular. -/
@[kb "milne2020ant" "v3.08, Lemma 2.44, p. 41"]
theorem lemma_2_44 {n : ℕ} {A : Type*} [EuclideanDomain A] (M : Matrix (Fin n) (Fin n) A) :
    ∃ l : List (Matrix (Fin n) (Fin n) A), (∀ E ∈ l, IsElementaryRowOp E) ∧
      (l.prod * M).BlockTriangular id := by
  obtain ⟨N, ⟨l, hl, hlN⟩, hI⟩ := tri_aux M n le_rfl
  exact ⟨l, hl, by rw [hlN]; exact hI.blockTri⟩

/-- **Remark 2.45 (a)**, rows. Over a Euclidean domain, for every square matrix $M$ there is an invertible matrix
$U$ (unit determinant) with $UM$ upper triangular. -/
@[kb "milne2020ant" "v3.08, Remark 2.45 (a), p. 42"]
theorem remark_2_45_a_upper {n : ℕ} {A : Type*} [EuclideanDomain A] (M : Matrix (Fin n) (Fin n) A) :
    ∃ U : Matrix (Fin n) (Fin n) A, IsUnit U.det ∧ (U * M).BlockTriangular id := by
  obtain ⟨l, hl, hT⟩ := lemma_2_44 M
  exact ⟨l.prod, isUnit_det_prod l hl, hT⟩

/-- **Remark 2.45 (a)**, columns. Over a Euclidean domain, for every square matrix $M$ there is an invertible matrix
$U$ (unit determinant) with $MU$ lower triangular. -/
@[kb "milne2020ant" "v3.08, Remark 2.45 (a), p. 42"]
theorem remark_2_45_a_lower {n : ℕ} {A : Type*} [EuclideanDomain A] (M : Matrix (Fin n) (Fin n) A) :
    ∃ U : Matrix (Fin n) (Fin n) A, IsUnit U.det ∧ (M * U).BlockTriangular OrderDual.toDual := by
  obtain ⟨U, hU, hT⟩ := remark_2_45_a_upper Mᵀ
  refine ⟨Uᵀ, by rwa [det_transpose], ?_⟩
  have h := hT.transpose
  rwa [transpose_mul, transpose_transpose] at h

/-- **Hermite normal form** (Milne, Remark 2.45 (b), a definition in prose). An integer $n \times n$ matrix $T$ is in
(row) Hermite normal form if it is upper triangular, its diagonal entries are positive, $t_{ii} > 0$, and the
entries above each diagonal entry are reduced modulo it: $0 \le t_{ij} < t_{jj}$ for $i < j$. Mathlib has no such
notion (its `Hermite` files concern Hermite polynomials). -/
@[kb "milne2020ant" "v3.08, Remark 2.45 (b) (definition in prose: Hermite normal form), p. 42"]
def IsHermiteNormalForm {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  T.BlockTriangular id ∧ (∀ i, 0 < T i i) ∧ ∀ i j, i < j → 0 ≤ T i j ∧ T i j < T j j

section HAux

/-- `N` is obtained from `M` by left multiplication with a matrix of unit determinant. -/
private def Equivd {R : Type*} [CommRing R] {n : ℕ} (M N : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) R, IsUnit U.det ∧ U * M = N

private lemma Equivd.refl {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    Equivd M M := ⟨1, by simp, by simp⟩

private lemma Equivd.trans {R : Type*} [CommRing R] {n : ℕ} {M N P : Matrix (Fin n) (Fin n) R}
    (h1 : Equivd M N) (h2 : Equivd N P) : Equivd M P := by
  obtain ⟨U1, u1, rfl⟩ := h1
  obtain ⟨U2, u2, rfl⟩ := h2
  exact ⟨U2 * U1, by rw [det_mul]; exact u2.mul u1, by rw [Matrix.mul_assoc]⟩

variable {n : ℕ}

private def Red (N : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : Prop :=
  0 ≤ N i j ∧ N i j < N j j

private def ColsDone (c : ℕ) (N : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ b : Fin n, b.val < c → ∀ i, i < b → Red N i b

private lemma reduce_step (N : Matrix (Fin n) (Fin n) ℤ) (hN : N.BlockTriangular id)
    {i jj : Fin n} (hij : i < jj) :
    ∃ N1, Equivd N N1 ∧ (∀ a b, b < jj → N1 a b = N a b) ∧ (∀ a b, a ≠ i → N1 a b = N a b) ∧
      N1 i jj = N i jj % N jj jj ∧ N1.BlockTriangular id ∧ (∀ c, N1 c c = N c c) := by
  obtain ⟨N1, hN1⟩ : ∃ N1, N1 = transvection i jj (-(N i jj / N jj jj)) * N := ⟨_, rfl⟩
  have e2 : ∀ a b, a ≠ i → N1 a b = N a b := fun a b ha => by
    rw [hN1, transvection_mul_apply_of_ne i jj a b ha]
  have e1 : ∀ a b, b < jj → N1 a b = N a b := by
    intro a b hb
    by_cases ha : a = i
    · subst ha
      rw [hN1, transvection_mul_apply_same, hN (show id b < id jj from hb)]; simp
    · exact e2 a b ha
  refine ⟨N1, ⟨_, ?_, hN1.symm⟩, e1, e2, ?_, ?_, ?_⟩
  · rw [det_transvection_of_ne _ _ hij.ne]; exact isUnit_one
  · rw [hN1, transvection_mul_apply_same, Int.emod_def]; ring
  · intro a b hba
    by_cases ha : a = i
    · subst ha
      rw [e1 a b (lt_trans hba hij)]; exact hN hba
    · rw [e2 a b ha]; exact hN hba
  · intro c
    by_cases hc : c = i
    · subst hc; exact e1 c c hij
    · exact e2 c c hc

private lemma col_reduce (jj : Fin n) : ∀ m : ℕ, ∀ N : Matrix (Fin n) (Fin n) ℤ,
    N.BlockTriangular id → (∀ c, 0 < N c c) → ColsDone jj.val N →
    ∃ N', Equivd N N' ∧ N'.BlockTriangular id ∧ (∀ c, 0 < N' c c) ∧ ColsDone jj.val N' ∧
      ∀ i : Fin n, i.val < m → i < jj → Red N' i jj := by
  intro m
  induction m with
  | zero =>
    intro N h1 h2 h3
    exact ⟨N, Equivd.refl N, h1, h2, h3, fun i hi => absurd hi (by omega)⟩
  | succ m ih =>
    intro N h1 h2 h3
    obtain ⟨N', hE, hU, hP, hC, hR⟩ := ih N h1 h2 h3
    by_cases hm : m < n
    · by_cases hlt : (⟨m, hm⟩ : Fin n) < jj
      · obtain ⟨N1, hE1, e1, e2, e3, e4, e5⟩ := reduce_step N' hU hlt
        refine ⟨N1, hE.trans hE1, e4, fun c => by rw [e5]; exact hP c, ?_, ?_⟩
        · intro b hb i hib
          have hbj : b < jj := Fin.lt_def.2 hb
          obtain ⟨r1, r2⟩ := hC b hb i hib
          unfold Red
          rw [e1 i b hbj, e1 b b hbj]
          exact ⟨r1, r2⟩
        · intro i hi hij
          unfold Red
          by_cases him : i.val = m
          · have hie : i = ⟨m, hm⟩ := Fin.ext him
            subst hie
            rw [e3, e5 jj]
            exact ⟨Int.emod_nonneg _ (hP jj).ne', Int.emod_lt_of_pos _ (hP jj)⟩
          · have hie : i ≠ ⟨m, hm⟩ := fun h => him (by rw [h])
            obtain ⟨r1, r2⟩ := hR i (by omega) hij
            rw [e2 i jj hie, e5 jj]
            exact ⟨r1, r2⟩
      · refine ⟨N', hE, hU, hP, hC, ?_⟩
        intro i hi hij
        have : i.val < m := by
          by_contra hcon
          have hie : i = ⟨m, hm⟩ := Fin.ext (by show i.val = m; omega)
          exact hlt (hie ▸ hij)
        exact hR i this hij
    · refine ⟨N', hE, hU, hP, hC, ?_⟩
      intro i hi hij
      exact hR i (by have := i.isLt; omega) hij

private lemma hnf_aux (T : Matrix (Fin n) (Fin n) ℤ) (hT : T.BlockTriangular id)
    (hP : ∀ c, 0 < T c c) :
    ∀ c, c ≤ n → ∃ N, Equivd T N ∧ N.BlockTriangular id ∧ (∀ c, 0 < N c c) ∧ ColsDone c N := by
  intro c
  induction c with
  | zero =>
    intro _
    exact ⟨T, Equivd.refl T, hT, hP, fun b hb => absurd hb (by omega)⟩
  | succ c ih =>
    intro hc
    obtain ⟨N, hE, hU, hP', hC⟩ := ih (by omega)
    obtain ⟨N', hE', hU', hP'', hC', hR⟩ := col_reduce ⟨c, by omega⟩ n N hU hP' hC
    refine ⟨N', hE.trans hE', hU', hP'', ?_⟩
    intro b hb i hib
    by_cases hbc : b.val < c
    · exact hC' b hbc i hib
    · have hcn : c < n := by omega
      have hbe : b = ⟨c, hcn⟩ := Fin.ext (by show b.val = c; omega)
      have := hR i i.isLt (by rw [← hbe]; exact hib)
      rw [hbe]; exact this

private lemma hnf_exists (T : Matrix (Fin n) (Fin n) ℤ) (hT : T.BlockTriangular id)
    (hd : ∀ i, T i i ≠ 0) : ∃ V : Matrix (Fin n) (Fin n) ℤ, IsUnit V.det ∧ IsHermiteNormalForm (V * T) := by
  classical
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n) (Fin n) ℤ,
      D = diagonal (fun i => if 0 < T i i then 1 else -1) := ⟨_, rfl⟩
  have hDu : IsUnit D.det := by
    rw [hD, det_diagonal]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one ?_
    intro i _
    split_ifs
    · exact isUnit_one
    · exact isUnit_one.neg
  have hDT : ∀ i j, (D * T) i j = (if 0 < T i i then 1 else -1) * T i j := by
    intro i j; rw [hD, diagonal_mul]
  have hT1 : (D * T).BlockTriangular id := by
    intro i j hji
    rw [hDT, hT hji, mul_zero]
  have hP1 : ∀ c, 0 < (D * T) c c := by
    intro c
    rw [hDT]
    have := hd c
    split_ifs with h <;> omega
  obtain ⟨N, ⟨W, hW, hWN⟩, hU, hP, hC⟩ := hnf_aux (D * T) hT1 hP1 n le_rfl
  refine ⟨W * D, by rw [det_mul]; exact hW.mul hDu, ?_⟩
  rw [Matrix.mul_assoc, hWN]
  exact ⟨hU, hP, fun i j hij => hC j j.isLt i hij⟩

private lemma hnf_unique_aux (T1 T2 V : Matrix (Fin n) (Fin n) ℤ) (hV : IsUnit V.det)
    (hVT : V * T1 = T2) (h1 : IsHermiteNormalForm T1) (h2 : IsHermiteNormalForm T2) :
    T1 = T2 := by
  obtain ⟨p1, q1, r1⟩ := h1
  obtain ⟨p2, q2, r2⟩ := h2
  subst hVT
  have hVup : ∀ a b : Fin n, b < a → V a b = 0 := by
    intro a b
    induction b using WellFoundedLT.induction with
    | _ b ih =>
    intro hba
    have e : (V * T1) a b = 0 := p2 (show id b < id a from hba)
    rw [Matrix.mul_apply, Finset.sum_eq_single b] at e
    · rcases mul_eq_zero.1 e with h | h
      · exact h
      · exact absurd h (q1 b).ne'
    · intro x _ hx
      rcases lt_or_gt_of_ne hx with h | h
      · rw [ih x h (lt_trans h hba), zero_mul]
      · rw [p1 (show id b < id x from h), mul_zero]
    · intro h; exact absurd (Finset.mem_univ b) h
  have hdiag : ∀ i, (V * T1) i i = V i i * T1 i i := by
    intro i
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single i
    · intro x _ hx
      rcases lt_or_gt_of_ne hx with h | h
      · rw [hVup i x h, zero_mul]
      · rw [p1 (show id i < id x from h), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hdetV : V.det = ∏ i, V i i := det_of_isUpperTriangular (fun a b h => hVup a b h)
  have hVii : ∀ i, V i i = 1 := by
    intro i
    have hprod : IsUnit (∏ k, V k k) := by rw [← hdetV]; exact hV
    have hu : IsUnit (V i i) :=
      isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun k => V k k) (Finset.mem_univ i)) hprod
    rcases Int.isUnit_iff.1 hu with h | h
    · exact h
    · exfalso
      have h3 := hdiag i
      rw [h] at h3
      have := q1 i
      have := q2 i
      omega
  have hVoff : ∀ b a : Fin n, a < b → V a b = 0 := by
    intro b
    induction b using WellFoundedLT.induction with
    | _ b ih =>
    intro a hab
    have e : (V * T1) a b = V a a * T1 a b + V a b * T1 b b := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_add_of_mem a b (Finset.mem_univ a) (Finset.mem_univ b) hab.ne ?_
      intro x _ ⟨hxa, hxb⟩
      rcases lt_or_gt_of_ne hxa with h | h
      · rw [hVup a x h, zero_mul]
      · rcases lt_or_gt_of_ne hxb with h' | h'
        · rw [ih x h' a h, zero_mul]
        · rw [p1 (show id b < id x from h'), mul_zero]
    rw [hVii a] at e
    have hb := hdiag b
    rw [hVii b] at hb
    obtain ⟨s1, s2⟩ := r1 a b hab
    obtain ⟨s3, s4⟩ := r2 a b hab
    have hd := q1 b
    rcases lt_trichotomy (V a b) 0 with h | h | h
    · exfalso; nlinarith
    · exact h
    · exfalso; nlinarith
  have hV1 : V = 1 := by
    ext a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hVoff b a h, Matrix.one_apply_ne h.ne]
    · subst h; rw [hVii, Matrix.one_apply_eq]
    · rw [hVup a b h, Matrix.one_apply_ne h.ne']
  rw [hV1, Matrix.one_mul]

end HAux

/-- **Remark 2.45 (b)**, existence. For an integer matrix $M$ with $\det M \ne 0$ there is $U \in \mathrm{GL}_n(\mathbb Z)$
with $UM$ in Hermite normal form (Milne: using the operations (r1), (r2), (r3) "multiply a row by $-1$"). -/
@[kb "milne2020ant" "v3.08, Remark 2.45 (b), p. 42"]
theorem remark_2_45_b_exists {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hM : M.det ≠ 0) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ, IsUnit U.det ∧ IsHermiteNormalForm (U * M) := by
  obtain ⟨U0, hU0, hT0⟩ := remark_2_45_a_upper M
  have hdet : (U0 * M).det ≠ 0 := by
    rw [det_mul]; exact mul_ne_zero hU0.ne_zero hM
  have hprod : ∏ i, (U0 * M) i i ≠ 0 := by
    rw [← det_of_isUpperTriangular hT0]; exact hdet
  have hd : ∀ i, (U0 * M) i i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.1 hprod i (Finset.mem_univ i)
  obtain ⟨V, hV, hH⟩ := hnf_exists (U0 * M) hT0 hd
  exact ⟨V * U0, by rw [det_mul]; exact hV.mul hU0, by rw [Matrix.mul_assoc]; exact hH⟩

/-- **Remark 2.45 (b)**, uniqueness. The Hermite normal form is unique: if $U_1M$ and $U_2M$ are both in Hermite
normal form, with $U_1, U_2 \in \mathrm{GL}_n(\mathbb Z)$ and $\det M \neq 0$, then $U_1M = U_2M$. -/
@[kb "milne2020ant" "v3.08, Remark 2.45 (b), p. 42"]
theorem remark_2_45_b_unique {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hM : M.det ≠ 0)
    (U₁ U₂ : Matrix (Fin n) (Fin n) ℤ) (hU₁ : IsUnit U₁.det) (hU₂ : IsUnit U₂.det)
    (h₁ : IsHermiteNormalForm (U₁ * M)) (h₂ : IsHermiteNormalForm (U₂ * M)) : U₁ * M = U₂ * M := by
  have hinv : U₁⁻¹ * U₁ = 1 := Matrix.nonsing_inv_mul _ hU₁
  have hVu : IsUnit (U₂ * U₁⁻¹).det := by
    rw [det_mul]
    refine hU₂.mul (IsUnit.of_mul_eq_one U₁.det ?_)
    rw [← det_mul, hinv, det_one]
  refine hnf_unique_aux _ _ (U₂ * U₁⁻¹) hVu ?_ h₁ h₂
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc U₁⁻¹, hinv, Matrix.one_mul]

end NumberFieldKB.MilneANT
