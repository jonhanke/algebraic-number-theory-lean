import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Algebra.Order.Star.Real
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Aside 8.9 (Artin–Whaples): the axioms

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Aside 8.9, p. 138; bib key `milne2020ant`.
E. Artin and G. Whaples, *Axiomatic characterization of fields by the product formula for valuations*,
Bull. Amer. Math. Soc. 51 (1945), 469–492; E. Artin, *Algebraic Numbers and Algebraic Functions*, Ch. 12.

`AWAxioms V` packages Milne's Axiom I for a set `V` of pairwise inequivalent nontrivial absolute values (the
hypotheses of `NumberFieldKB.MilneANT.Aside8_9`). The proof that a field satisfying the axioms, with one locally
compact completion, is a global field follows Artin's counting argument, organized as:

* `totallyBounded_ball` (P1): if the completion `K_v` is locally compact, the unit ball of `K` for `v` is totally
  bounded;
* `PackingBound v` (P2): the number of `ε`-separated points of `K` in the `v`-ball of radius `R` is at most
  `C (R/ε)^κ`, obtained from P1 by scaling (`packingBound_of_totallyBounded`);
* `one_le_prod` (P3): the product formula gives `1 ≤ ∏_{v ∈ T} v x` for `x ≠ 0` and any finite `T ⊆ V` outside of
  which `v x ≤ 1`.
-/

open scoped BigOperators

namespace NumberFieldKB.MilneANT.Aside89

variable {K : Type*} [Field K]

/-- **Axiom I** of Artin–Whaples for a set `V` of absolute values (Milne, Aside 8.9): the members are nontrivial and
pairwise inequivalent, and for `a ≠ 0` only finitely many `v ∈ V` have `v a ≠ 1` and `∏_{v ∈ V} v a = 1`. -/
structure AWAxioms (V : Set (AbsoluteValue K ℝ)) : Prop where
  nontrivial : ∀ v ∈ V, v.IsNontrivial
  ineq : ∀ v ∈ V, ∀ w ∈ V, v.IsEquiv w → v = w
  prod : ∀ a : K, a ≠ 0 → {v ∈ V | v a ≠ 1}.Finite ∧ ∏ᶠ (v ∈ V), v a = 1

/-- The **packing bound** for an absolute value `v`: there are `C > 0` and `κ ≥ 0` such that every finite set of
points of `K` in the ball of radius `R` that are pairwise at distance at least `ε` (`0 < ε ≤ R`) has at most
`C (R/ε)^κ` elements. -/
def PackingBound (v : AbsoluteValue K ℝ) : Prop :=
  ∃ C κ : ℝ, 0 < C ∧ 0 ≤ κ ∧ ∀ R ε : ℝ, 0 < ε → ε ≤ R → ∀ S : Finset K,
    (∀ x ∈ S, v x ≤ R) → (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε ≤ v (x - y)) → (S.card : ℝ) ≤ C * (R / ε) ^ κ

open Classical in
/-- **P3** (the product formula as a lower bound): for `x ≠ 0` and a finite `T ⊆ V` such that `v x ≤ 1` for every
`v ∈ V` outside `T`, `1 ≤ ∏_{v ∈ T} v x`. -/
@[kb "milne2020ant" "v3.08, Aside 8.9, p. 138"]
theorem one_le_prod {V : Set (AbsoluteValue K ℝ)} (hV : AWAxioms V) {x : K} (hx : x ≠ 0)
    (T : Finset (AbsoluteValue K ℝ)) (hT : (T : Set (AbsoluteValue K ℝ)) ⊆ V)
    (hout : ∀ v ∈ V, v ∉ T → v x ≤ 1) : 1 ≤ ∏ v ∈ T, v x := by
  obtain ⟨hfin, hprod⟩ := hV.prod x hx
  set U : Finset (AbsoluteValue K ℝ) := T ∪ hfin.toFinset with hU
  have hUV : (U : Set (AbsoluteValue K ℝ)) ⊆ V := by
    intro v hv
    rw [hU, Finset.coe_union, Set.Finite.coe_toFinset] at hv
    rcases hv with hv | hv
    · exact hT hv
    · exact hv.1
  have h1 : ∏ᶠ (v ∈ V), v x = ∏ v ∈ U, v x := by
    refine finprod_mem_eq_prod_of_subset _ ?_ hUV
    intro v ⟨hv, hs⟩
    rw [hU, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inr ⟨hv, hs⟩
  have hTU : T ⊆ U := Finset.subset_union_left
  have h2 := Finset.prod_sdiff (f := fun v : AbsoluteValue K ℝ => v x) hTU
  have hB : ∏ v ∈ U \ T, v x ≤ 1 := by
    refine Finset.prod_le_one₀ (fun v _ => v.nonneg x) (fun v hv => ?_)
    rw [Finset.mem_sdiff] at hv
    exact hout v (hUV hv.1) hv.2
  have hB0 : 0 ≤ ∏ v ∈ U \ T, v x := Finset.prod_nonneg (fun v _ => v.nonneg x)
  have hA0 : 0 ≤ ∏ v ∈ T, v x := Finset.prod_nonneg (fun v _ => v.nonneg x)
  have h3 : (∏ v ∈ U \ T, v x) * ∏ v ∈ T, v x = 1 := by rw [h2, ← h1, hprod]
  nlinarith

end NumberFieldKB.MilneANT.Aside89
