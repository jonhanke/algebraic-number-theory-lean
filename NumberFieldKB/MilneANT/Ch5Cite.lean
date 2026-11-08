import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Chapter 5: citations of the results in Mathlib

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (pdf page − 2).

When Mathlib states a result in Milne's form, the Mathlib declaration is tagged (`attribute [kb ...]`); when the
forms differ, a short theorem restates it in Milne's form. The other Chapter 5 items are in `Ch5Units.lean`,
`Ch5Cubic.lean` and `Ch5CubicBound.lean`.

* Theorem 5.1 (`theorem_5_1`), Lemma 5.2 (`lemma_5_2`), Proposition 5.5 (`proposition_5_5`), Lemma 5.10
  (`lemma_5_10`): restated.
* Corollary 5.6, Proposition 5.8, Theorem 5.9, Proposition 5.12 and the prose definitions of Chapter 5 (rank of a
  finitely generated abelian group, $r$ and $s$, fundamental system of units, ring of $S$-integers, group of
  $S$-units, continued fractions, regulator): tagged Mathlib declarations.
-/

open NumberField NumberField.InfinitePlace NumberField.Units Polynomial

namespace NumberFieldKB.MilneANT

/-- **Theorem 5.1** (Dirichlet's unit theorem). The group of units of a number field $K$ is finitely generated,
of rank $r + s - 1$ ($r$ real embeddings, $2s$ nonreal complex embeddings). The rank of a finitely generated
abelian group (the number $t$ in $A \cong A_{\mathrm{tors}} \oplus \mathbb Z^t$) is `Module.finrank ℤ` of the
additive group. Mathlib: `NumberField.Units.finrank_eq`, `NumberField.Units.rank`. -/
@[kb "milne2020ant" "v3.08, Theorem 5.1, p. 85"]
theorem theorem_5_1 (K : Type*) [Field K] [NumberField K] :
    Group.FG (𝓞 K)ˣ ∧
      (Module.finrank ℤ (Additive (𝓞 K)ˣ) : ℤ) = nrRealPlaces K + nrComplexPlaces K - 1 := by
  refine ⟨Group.fg_iff_monoid_fg.2 inferInstance, ?_⟩
  rw [NumberField.Units.finrank_eq, NumberField.Units.rank]
  have h1 := card_eq_nrRealPlaces_add_nrComplexPlaces K
  have h2 : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
  omega

/-- **Lemma 5.2.** An element $\alpha \in K$ is a unit (of $\mathcal O_K$) if and only if $\alpha \in \mathcal O_K$
and $\operatorname{Nm}_{K/\mathbb Q}\alpha = \pm 1$. Mathlib: `NumberField.isUnit_iff_norm`. -/
@[kb "milne2020ant" "v3.08, Lemma 5.2, p. 86"]
theorem lemma_5_2 {K : Type*} [Field K] [NumberField K] (α : K) :
    (∃ u : (𝓞 K)ˣ, ((u : 𝓞 K) : K) = α) ↔
      IsIntegral ℤ α ∧ (Algebra.norm ℚ α = 1 ∨ Algebra.norm ℚ α = -1) := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨(u : 𝓞 K).isIntegral_coe, ?_⟩
    exact (abs_eq zero_le_one).1 (NumberField.Units.norm K u)
  · rintro ⟨hi, hn⟩
    let x : 𝓞 K := ⟨α, hi⟩
    have hx : IsUnit x := by
      rw [NumberField.isUnit_iff_norm, RingOfIntegers.coe_norm]
      show |Algebra.norm ℚ α| = 1
      rcases hn with h | h <;> simp [h]
    exact ⟨hx.unit, rfl⟩

/-- **Proposition 5.5.** For any integer $m$ and real $M$, the set of algebraic integers $\alpha \in \mathbb C$ of
degree $\le m$ all of whose conjugates $\alpha'$ (the roots in $\mathbb C$ of the minimal polynomial of $\alpha$)
satisfy $\lvert\alpha'\rvert < M$ is finite. Mathlib states the version for a fixed number field
(`NumberField.Embeddings.finite_of_norm_le`); the proof here is Milne's (bounded integer coefficients,
`Polynomial.coeff_bdd_of_roots_le`, `Polynomial.bUnion_roots_finite`). -/
@[kb "milne2020ant" "v3.08, Proposition 5.5, p. 87"]
theorem proposition_5_5 (m : ℕ) (M : ℝ) :
    {α : ℂ | IsIntegral ℤ α ∧ (minpoly ℚ α).natDegree ≤ m ∧
      ∀ β ∈ (minpoly ℚ α).aroots ℂ, ‖β‖ < M}.Finite := by
  classical
  let C := Nat.ceil (max M 1 ^ m * m.choose (m / 2))
  have hfin := bUnion_roots_finite (algebraMap ℤ ℂ) m (Set.finite_Icc (-C : ℤ) C)
  refine hfin.subset fun x hx => ?_
  simp_rw [Set.mem_iUnion]
  obtain ⟨hint, hdeg, hroots⟩ := hx
  have hmap := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hdegZ : (minpoly ℤ x).natDegree ≤ m := by
    rw [← (minpoly.monic hint).natDegree_map (algebraMap ℤ ℚ), ← hmap]
    exact hdeg
  have hcomp : (minpoly ℤ x).map (algebraMap ℤ ℂ) = (minpoly ℚ x).map (algebraMap ℚ ℂ) := by
    rw [hmap, Polynomial.map_map]
    congr 1
  refine ⟨minpoly ℤ x, ⟨hdegZ, fun i => ?_⟩, Polynomial.mem_rootSet.2 ⟨minpoly.ne_zero hint, minpoly.aeval ℤ x⟩⟩
  rw [Set.mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
  have hb := coeff_bdd_of_roots_le (B := M) (algebraMap ℤ ℂ) (minpoly.monic hint)
    (IsAlgClosed.splits _) hdegZ (fun z hz => ?_) i
  · refine le_trans (le_of_eq ?_) (hb.trans (Nat.le_ceil _))
    rw [Polynomial.coeff_map, eq_intCast, Complex.norm_intCast, Int.cast_abs]
  · rw [hcomp] at hz
    exact (hroots z hz).le

attribute [kb "milne2020ant" "v3.08, Corollary 5.6, p. 87"]
  NumberField.Embeddings.pow_eq_one_of_norm_eq_one

attribute [kb "milne2020ant" "v3.08, Proposition 5.8, p. 87 (L(U) is a lattice)"]
  NumberField.Units.instZLattice_unitLattice
attribute [kb "milne2020ant" "v3.08, Proposition 5.8, p. 87 (the kernel of L is μ(K))"]
  NumberField.Units.dirichletUnitTheorem.logEmbedding_ker

attribute [kb "milne2020ant" "v3.08, Theorem 5.9, p. 88 (L(U) is a full lattice)"]
  NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top
attribute [kb "milne2020ant" "v3.08, Theorem 5.9, p. 88 (rank r + s - 1)"]
  NumberField.Units.unitLattice_rank

/-- **Lemma 5.10.** A real $m \times m$ matrix $(a_{ij})$ with $a_{ij} < 0$ for $i \ne j$ and
$\sum_j a_{ij} > 0$ for every $i$ is invertible. Mathlib has the Gershgorin form (strict diagonal dominance,
`det_ne_zero_of_sum_row_lt_diag`), from which this follows. -/
@[kb "milne2020ant" "v3.08, Lemma 5.10, p. 89"]
theorem lemma_5_10 {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hoff : ∀ i j, i ≠ j → A i j < 0)
    (hrow : ∀ i, 0 < ∑ j, A i j) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  refine det_ne_zero_of_sum_row_lt_diag fun k => ?_
  have h := hrow k
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at h
  have e : ∑ j ∈ Finset.univ.erase k, ‖A k j‖ = -∑ j ∈ Finset.univ.erase k, A k j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Real.norm_eq_abs, abs_of_neg (hoff k j (Finset.ne_of_mem_erase hj).symm)]
  have hnn : 0 ≤ ∑ j ∈ Finset.univ.erase k, -A k j :=
    Finset.sum_nonneg fun j hj => (neg_pos.2 (hoff k j (Finset.ne_of_mem_erase hj).symm)).le
  rw [e, Real.norm_eq_abs, abs_of_pos (by rw [Finset.sum_neg_distrib] at hnn; linarith)]
  linarith

attribute [kb "milne2020ant" "v3.08, Proposition 5.12, p. 90"]
  NumberField.IsCMField.indexRealUnits_eq_one_or_two

/-! ### Prose definitions of Chapter 5 -/

attribute [kb "milne2020ant" "v3.08, Ch. 5, rank of a finitely generated abelian group, p. 85"]
  NumberField.Units.finrank_eq
attribute [kb "milne2020ant" "v3.08, Ch. 5, the numbers r and s, p. 85"]
  NumberField.InfinitePlace.nrRealPlaces NumberField.InfinitePlace.nrComplexPlaces
attribute [kb "milne2020ant" "v3.08, Ch. 5, fundamental system of units, p. 85"]
  NumberField.Units.fundSystem NumberField.Units.exist_unique_eq_mul_prod
attribute [kb "milne2020ant" "v3.08, Ch. 5, ring of S-integers, p. 90"] Set.integer
attribute [kb "milne2020ant" "v3.08, Ch. 5, group of S-units, p. 90"] Set.unit Set.unitEquivUnitsInteger
attribute [kb "milne2020ant" "v3.08, Ch. 5, continued fractions, quotients and convergents, p. 91"]
  GenContFract GenContFract.convs
attribute [kb "milne2020ant" "v3.08, Ch. 5, regulator, p. 94"] NumberField.Units.regulator

end NumberFieldKB.MilneANT
