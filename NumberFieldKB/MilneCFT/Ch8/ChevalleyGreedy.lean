import Mathlib.Algebra.Torsor.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Generating a finite group by elements attached to distinct indices

If, for every finite set `S` of indices, the elements `g` attached (via a relation `R i g`) to some index `i ∉ S`
generate a finite group `G`, then finitely many of them, attached to pairwise distinct indices, already generate `G`
(greedy choice: while the current closure is a proper subgroup, some element attached to a new index lies outside it).
Used for Frobenius elements at distinct places (step 2 of the proof of Chevalley's theorem).
-/

namespace NumberFieldKB.MilneCFT.Ch8

/-- **Greedy generation at distinct indices.** -/
theorem exists_finset_closure_eq_top {G ι : Type*} [Group G] [Finite G] (R : ι → G → Prop)
    (h : ∀ S : Finset ι, Subgroup.closure {g | ∃ i ∉ S, R i g} = ⊤) :
    ∃ (T : Finset ι) (σ : T → G), (∀ i : T, R i (σ i)) ∧ Subgroup.closure (Set.range σ) = ⊤ := by
  classical
  have key : ∀ n : ℕ, ∃ (T : Finset ι) (σ : T → G), (∀ i : T, R i (σ i)) ∧
      (Subgroup.closure (Set.range σ) = ⊤ ∨ n < Nat.card (Subgroup.closure (Set.range σ))) := by
    intro n
    induction n with
    | zero =>
      refine ⟨∅, fun i => (Finset.notMem_empty _ i.2).elim,
        fun i => (Finset.notMem_empty _ i.2).elim, Or.inr ?_⟩
      exact Nat.card_pos
    | succ n ih =>
      obtain ⟨T, σ, hσ, hc⟩ := ih
      rcases hc with hc | hc
      · exact ⟨T, σ, hσ, Or.inl hc⟩
      by_cases htop : Subgroup.closure (Set.range σ) = ⊤
      · exact ⟨T, σ, hσ, Or.inl htop⟩
      have hns : ¬ {g | ∃ i ∉ T, R i g} ⊆ (Subgroup.closure (Set.range σ) : Set G) := by
        intro hsub
        apply htop
        rw [eq_top_iff, ← h T, Subgroup.closure_le]
        exact hsub
      obtain ⟨g, ⟨i, hiT, hR⟩, hg⟩ := Set.not_subset.mp hns
      let σ' : ↥(insert i T) → G := fun j =>
        if hj : (j : ι) = i then g else σ ⟨j, by
          have := j.2
          rw [Finset.mem_insert] at this
          exact this.resolve_left hj⟩
      have hσ'i : σ' ⟨i, Finset.mem_insert_self _ _⟩ = g := by simp [σ']
      have hσ'T : ∀ j : T, σ' ⟨j, Finset.mem_insert_of_mem j.2⟩ = σ j := by
        intro j
        have : (j : ι) ≠ i := fun e => hiT (e ▸ j.2)
        simp [σ', this]
      refine ⟨insert i T, σ', ?_, Or.inr ?_⟩
      · intro j
        by_cases hj : (j : ι) = i
        · have : σ' j = g := by simp [σ', hj]
          rw [this, hj]
          exact hR
        · have := j.2
          rw [Finset.mem_insert] at this
          have hjT := this.resolve_left hj
          have e : j = ⟨(⟨j, hjT⟩ : T), Finset.mem_insert_of_mem hjT⟩ := rfl
          rw [e, hσ'T]
          exact hσ ⟨j, hjT⟩
      · have hle : Subgroup.closure (Set.range σ) ≤ Subgroup.closure (Set.range σ') := by
          apply Subgroup.closure_mono
          rintro _ ⟨j, rfl⟩
          exact ⟨_, hσ'T j⟩
        have hgmem : g ∈ Subgroup.closure (Set.range σ') :=
          Subgroup.subset_closure ⟨_, hσ'i⟩
        have hlt : Subgroup.closure (Set.range σ) < Subgroup.closure (Set.range σ') :=
          lt_of_le_of_ne hle (fun e => hg (by rw [e]; exact hgmem))
        have := Subgroup.card_lt_of_lt hlt
        omega
  obtain ⟨T, σ, hσ, hc⟩ := key (Nat.card G)
  refine ⟨T, σ, hσ, ?_⟩
  rcases hc with hc | hc
  · exact hc
  · exact absurd (Subgroup.card_le_card_group _) (not_le.mpr hc)

end NumberFieldKB.MilneCFT.Ch8
