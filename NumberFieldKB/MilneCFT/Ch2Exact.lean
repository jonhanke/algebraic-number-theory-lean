import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import QuadFormsKB.Citation
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Milne, *Class Field Theory*, Chapter II §3: Lemma 3.7

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory

/-! ## Lemma 3.7 -/

lemma card_eq_ker_mul_range {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]
    [Finite M] (f : M →ₗ[ℤ] N) :
    Nat.card M = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  have h := Nat.card_congr (f.quotKerEquivRange).toEquiv
  have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker f).toAddSubgroup
  rw [h2, mul_comm]
  congr 1

lemma altprod_aux (c : ℕ → ℕ) (m : ℕ) :
    ((∏ i ∈ Finset.range (2 * m), if Even i then c i * c (i + 1) else 1) = ∏ j ∈ Finset.range (2 * m), c j) ∧
    ((∏ i ∈ Finset.range (2 * m), if Odd i then c i * c (i + 1) else 1) * c 0
      = ∏ j ∈ Finset.range (2 * m + 1), c j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [e, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ (fun j => c j),
      Finset.prod_range_succ (fun j => c j)]
    have o1 : Even (2 * m) := ⟨m, by ring⟩
    have o2 : ¬ Even (2 * m + 1) := by simp
    have o3 : Odd (2 * m + 1) := by simp
    have o4 : ¬ Odd (2 * m) := by simp
    simp only [o1, o2, o3, o4, ite_true, ite_false, mul_one, Finset.prod_range_succ] at *
    constructor
    · rw [h1]; ring
    · rw [mul_right_comm, h2]; ring


lemma altprod (c : ℕ → ℕ) (n : ℕ) (h0 : c 0 = 1) (hn : c n = 1) :
    (∏ i ∈ Finset.range n, if Even i then c i * c (i + 1) else 1) =
      ∏ i ∈ Finset.range n, if Odd i then c i * c (i + 1) else 1 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨h1, h2⟩ := altprod_aux c m
    rw [Finset.prod_range_succ, hn, h0] at h2
    rw [h1]; simpa using h2.symm
  · obtain ⟨h1, h2⟩ := altprod_aux c m
    have o1 : Even (2 * m) := ⟨m, by ring⟩
    have o4 : ¬ Odd (2 * m) := by simp
    rw [Finset.prod_range_succ (fun i => if Even i then c i * c (i + 1) else 1) (2 * m),
      Finset.prod_range_succ (fun i => if Odd i then c i * c (i + 1) else 1) (2 * m),
      h1]
    simp only [o1, o4, ite_true, ite_false, mul_one]
    rw [h0, mul_one] at h2
    rw [h2, Finset.prod_range_succ (fun j => c j) (2 * m)]
    simp [hn]

/-- **Lemma 3.7** (p. 82). Let $0 \to A_0 \to A_1 \to \cdots \to A_r \to 0$ be an exact sequence of finite
(abelian) groups. Then $|A_0| \cdot |A_2| \cdots = |A_1| \cdot |A_3| \cdots$. The sequence is
`A : ComposableArrows (ModuleCat ℤ) r`, exact, with first map injective and last map surjective. -/
@[kb "milne2020cft" "v4.03, Ch. II, Lemma 3.7, p. 82"]
theorem lemma_3_7 (r : ℕ) (A : ComposableArrows (ModuleCat ℤ) (r + 1)) (hA : A.Exact)
    (h₀ : Mono (A.map' 0 1)) (h₁ : Epi (A.map' r (r + 1))) (hfin : ∀ i, Finite (A.obj i)) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin (r + 2) => Even (i : ℕ)), Nat.card (A.obj i) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin (r + 2) => Odd (i : ℕ)), Nat.card (A.obj i) := by
  classical
  have := hfin
  let K : ℕ → ℕ := fun j => if h : j ≤ r then
    Nat.card (LinearMap.range (A.map' j (j + 1) (by omega) (by omega)).hom) else 1
  let c : ℕ → ℕ := fun j => if j = 0 then 1 else K (j - 1)
  have hK : ∀ j (hj : j ≤ r), K j = Nat.card (LinearMap.range (A.map' j (j + 1) (by omega) (by omega)).hom) := by
    intro j hj; simp [K, hj]
  have key : ∀ i (hi : i ≤ r + 1), Nat.card (A.obj ⟨i, by omega⟩) = c i * c (i + 1) := by
    intro i hi
    have hc1 : c (i + 1) = K i := by simp [c]
    rw [hc1]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have hc0 : c 0 = 1 := by simp [c]
      rw [hc0, one_mul, hK 0 (by omega)]
      have hinj : Function.Injective (A.map' 0 1).hom :=
        (ModuleCat.mono_iff_injective (A.map' 0 1)).1 h₀
      have h := card_eq_ker_mul_range (A.map' 0 1).hom
      have : LinearMap.ker (A.map' 0 1).hom = ⊥ := LinearMap.ker_eq_bot.2 hinj
      rw [this] at h
      have h1 : Nat.card (⊥ : Submodule ℤ (A.obj ⟨0, by omega⟩)) = 1 := Nat.card_unique
      rw [h1, one_mul] at h
      exact h
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hcj : c (j + 1) = K j := by simp [c]
      rw [hcj]
      by_cases hjr : j + 1 ≤ r
      · have h := card_eq_ker_mul_range (A.map' (j + 1) (j + 1 + 1) (by omega) (by omega)).hom
        have hex := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (hA.exact' j (j + 1) (j + 2))
        rw [hK (j + 1) hjr, hK j (by omega)]
        simp only [ComposableArrows.sc'] at hex
        rw [← hex] at h
        rw [h, mul_comm]
      · have hj : j = r := by omega
        subst hj
        have hK1 : K (j + 1) = 1 := by simp [K]
        rw [hK1, mul_one, hK j le_rfl]
        have hsurj : Function.Surjective (A.map' j (j + 1)).hom :=
          (ModuleCat.epi_iff_surjective (A.map' j (j + 1))).1 h₁
        have : LinearMap.range (A.map' j (j + 1)).hom = ⊤ := LinearMap.range_eq_top.2 hsurj
        rw [this]
        simp
  have hpr : ∀ P : ℕ → Prop, [DecidablePred P] →
      ∏ i ∈ Finset.univ.filter (fun i : Fin (r + 2) => P (i : ℕ)), Nat.card (A.obj i) =
        ∏ i ∈ Finset.range (r + 2), if P i then c i * c (i + 1) else 1 := by
    intro P _
    rw [Finset.prod_filter, ← Fin.prod_univ_eq_prod_range (fun i => if P i then c i * c (i + 1) else 1)]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · exact key i (by omega)
    · rfl
  rw [hpr Even, hpr Odd]
  have c0 : c 0 = 1 := by simp [c]
  have cl : c (r + 2) = 1 := by simp [c, K]
  exact altprod c (r + 2) c0 cl

end NumberFieldKB.MilneCFT
