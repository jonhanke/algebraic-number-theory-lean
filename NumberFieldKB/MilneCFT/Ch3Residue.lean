import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Herbrand

/-!
# Milne, *Class Field Theory*, Chapter III §1: the cohomology of the residue fields

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

For a finite extension of finite fields $l/k$ with (cyclic) Galois group $G$, Lemma 1.4 says that the Tate groups
of $l^\times$ vanish, and Lemma 1.5 that the Tate groups of $l$ vanish. Both are proved here from Chapter II
(Hilbert's Theorem 90, the Herbrand quotient of a finite module, periodicity, and the normal basis theorem).

Milne states the lemmas for the residue fields $l$, $k$ of an unramified extension of local fields $L/K$, with
$G = \operatorname{Gal}(L/K) \simeq \operatorname{Gal}(l/k)$; the statements below are about $\operatorname{Gal}(l/k)$
itself, for every finite extension of finite fields.
-/

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT

section Cyclic

variable {G : Type} [Group G] [Fintype G]

/-- For a finite cyclic group, a module whose Tate groups vanish in degrees $0$ and $1$ has vanishing Tate groups
in all degrees (periodicity, Chapter II, Proposition 3.4). -/
theorem tate_isZero_of_cyclic [IsCyclic G] (M : Rep ℤ G) (h0 : IsZero (tateCohomology M 0))
    (h1 : IsZero (tateCohomology M 1)) (r : ℤ) : IsZero (tateCohomology M r) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have key : ∀ e : ℤ, IsZero (tateCohomology M e) → ∀ k : ℤ, IsZero (tateCohomology M (e + 2 * k)) := by
    intro e he k
    induction k using Int.induction_on with
    | zero => simpa using he
    | succ k ih =>
      have := ih.of_iso (periodicity g hg M (e + 2 * k)).symm
      rwa [show e + 2 * k + 2 = e + 2 * (k + 1) by ring] at this
    | pred k ih =>
      have h' : IsZero (tateCohomology M (e + 2 * (-(k : ℤ) - 1) + 2)) := by
        rwa [show e + 2 * (-(k : ℤ) - 1) + 2 = e + 2 * -(k : ℤ) by ring]
      exact h'.of_iso (periodicity g hg M (e + 2 * (-(k : ℤ) - 1)))
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' r
  · simpa [hk] using key 0 h0 k
  · rw [hk, add_comm]; exact key 1 h1 k

end Cyclic

section FiniteFields

variable (k l : Type) [Field k] [Field l] [Finite l] [Algebra k l]

omit [Finite l] in
/-- $H^1_T(G, l^\times) = 0$ for a finite Galois extension $l/k$ (Hilbert's Theorem 90, Chapter II, Proposition
1.22; Mathlib's `groupCohomology.H1ofAutOnUnitsUnique`). -/
theorem tate_one_units_isZero [FiniteDimensional k l] [IsGalois k l] :
    IsZero (tateCohomology (Rep.ofAlgebraAutOnUnits k l) 1) := by
  refine IsZero.of_iso ?_ ((TateCohomology.isoGroupCohomology (R := ℤ) (G := l ≃ₐ[k] l) 1).app _)
  exact @ModuleCat.isZero_of_subsingleton _ _ (H1 (Rep.ofAlgebraAutOnUnits k l)) inferInstance

/-- **Lemma 1.4** (p. 98). Let $l/k$ be a finite extension of finite fields with Galois group $G$. Then
$H^r_T(G, l^\times) = 0$ for all $r \in \mathbb Z$. Milne's proof: $H^1 = 0$ by Hilbert's Theorem 90, $h(l^\times)
= 1$ because $l^\times$ is finite (Chapter II, Proposition 3.8), so $H^2 = H^0_T = 0$; then periodicity. -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 1.4, p. 98"]
theorem lemma_1_4 (r : ℤ) : IsZero (tateCohomology (Rep.ofAlgebraAutOnUnits k l) r) := by
  have : Finite k := Finite.of_injective _ (algebraMap k l).injective
  have : FiniteDimensional k l := Module.Finite.of_finite
  have : Finite (Rep.ofAlgebraAutOnUnits k l) := inferInstanceAs (Finite (Additive lˣ))
  have hcyc : IsCyclic (l ≃ₐ[k] l) := inferInstance
  have h1 := tate_one_units_isZero k l
  obtain ⟨⟨hfin0, hfin1⟩, hq⟩ := prop_3_8 (Rep.ofAlgebraAutOnUnits k l)
  have hc1 : Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits k l) 1) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨ModuleCat.subsingleton_of_isZero h1, ⟨0⟩⟩
  unfold herbrandQuotient at hq
  rw [hc1, Nat.cast_one, div_one, Nat.cast_eq_one] at hq
  have h0 : IsZero (tateCohomology (Rep.ofAlgebraAutOnUnits k l) 0) := by
    rw [Nat.card_eq_one_iff_unique] at hq
    have := hq.1
    exact ModuleCat.isZero_of_subsingleton _
  exact tate_isZero_of_cyclic _ h0 h1 r

/-- **Lemma 1.4** (p. 98), the consequence: the norm map $l^\times \to k^\times$ is surjective. This is Mathlib's
`FiniteField.unitsMap_norm_surjective` (which Milne obtains from the vanishing of $H^0_T$). -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 1.4 (the norm is surjective), p. 98"]
theorem lemma_1_4_norm [Finite k] : Function.Surjective (Units.map (Algebra.norm k (S := l))) :=
  FiniteField.unitsMap_norm_surjective k l

/-- **Lemma 1.5** (p. 98). Let $l/k$ be a finite Galois extension with group $G$ (Milne: of finite fields). Then
$H^r_T(G, l) = 0$ for all $r \in \mathbb Z$: by the normal basis theorem $l$ is an induced $G$-module
(`isInduced_ofAlgebraAut`, Chapter II, Proposition 1.24), so all its Tate groups vanish (Chapter II, Proposition
3.1). Milne deduces the case $r \le 0$ from $r > 0$ by periodicity; the proof here needs neither finiteness nor
cyclicity. -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 1.5, p. 98"]
theorem lemma_1_5 (k l : Type) [Field k] [Field l] [Algebra k l] [FiniteDimensional k l] [IsGalois k l] (r : ℤ) :
    IsZero (tateCohomology (Rep.ofAlgebraAut k l) r) :=
  prop_3_1 (isInduced_ofAlgebraAut k l) r

/-- **Lemma 1.5** (p. 98), the consequence: the trace map $l \to k$ is surjective (Mathlib's
`Algebra.trace_surjective`, for finite separable extensions). -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 1.5 (the trace is surjective), p. 98"]
theorem lemma_1_5_trace (k l : Type) [Field k] [Field l] [Algebra k l] [FiniteDimensional k l]
    [Algebra.IsSeparable k l] : Function.Surjective (Algebra.trace k l) :=
  Algebra.trace_surjective k l

end FiniteFields

end NumberFieldKB.MilneCFT.Ch3
