import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch8Aside89Basic
import NumberFieldKB.TauCetiPort.FieldTheory.FunctionField.Place.OfValuationSubring
import NumberFieldKB.WeilBNT.FunctionField.RiemannInequality

/-!
# Milne, *Algebraic Number Theory*, Aside 8.9 (Artin–Whaples): the function field case

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Aside 8.9, p. 138; bib key `milne2020ant`.
H. Stichtenoth, *Algebraic Function Fields and Codes*, Theorem 1.1.6 (Tau Ceti port,
`TauCeti.Place.ofValuationSubring`); A. Weil, *Basic Number Theory*, Ch. VI, §1 (finiteness of `D₀(k)/P(k)`).

If `K` is a finite extension of `𝔽_q(t)` and `V` satisfies the Artin–Whaples axioms (`AWAxioms`), every nontrivial
absolute value `w` of `K` is equivalent to a member of `V`. Proof: `w` is nonarchimedean (finite constant field), its
valuation ring is a proper valuation subring containing `𝔽_q`, hence the ring of a place `P_w`
(`placeOf`, Stichtenoth 1.1.6). If `w` were inequivalent to every `v ∈ V`, take `v₀ ∈ V` and a function `f` with
divisor supported on `{P_{v₀}, P_w}` and nonzero order at `P_{v₀}` (finiteness of the class group `D₀/P`);
then `v f = 1` for `v ≠ v₀` in `V`, `v₀ f ≠ 1`, contradicting the product formula.
-/

open NumberFieldKB.WeilBNT.FF

namespace NumberFieldKB.MilneANT.Aside89

section Generic

variable (Fq : Type*) {K : Type*} [Field Fq] [Finite Fq] [Field K] [Algebra Fq K]

lemma abv_algebraMap_le_one (w : AbsoluteValue K ℝ) (c : Fq) : w (algebraMap Fq K c) ≤ 1 := by
  haveI := Fintype.ofFinite Fq
  by_cases hc : c = 0
  · simp [hc]
  · have h1 : c ^ (Fintype.card Fq - 1) = 1 := FiniteField.pow_card_sub_one_eq_one c hc
    have h2 : (algebraMap Fq K c) ^ (Fintype.card Fq - 1) = 1 := by
      rw [← map_pow, h1, map_one]
    have hp : Fintype.card Fq - 1 ≠ 0 := by
      have := Fintype.one_lt_card (α := Fq)
      omega
    have := congrArg w h2
    rw [map_pow, map_one] at this
    exact ((pow_eq_one_iff_of_nonneg (w.nonneg _) hp).1 this).le

include Fq in
lemma abv_isNonarch (w : AbsoluteValue K ℝ) (x y : K) : w (x + y) ≤ max (w x) (w y) := by
  let _ : NormedField K := w.toNormedField
  have : IsUltrametricDist K :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one (fun n => by
      have h : (n : K) = algebraMap Fq K (n : Fq) := by simp
      show w (n : K) ≤ 1
      rw [h]
      exact abv_algebraMap_le_one Fq w _)
  exact IsUltrametricDist.isNonarchimedean_norm x y

/-- The valuation subring `{x | w x ≤ 1}` of a (necessarily nonarchimedean) absolute value. -/
def abvSubring (w : AbsoluteValue K ℝ) : ValuationSubring K where
  carrier := {x | w x ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_mul] at *
    nlinarith [w.nonneg a, w.nonneg b]
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (abv_isNonarch Fq w a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha
  mem_or_inv_mem' := fun x => by
    by_cases hx : w x ≤ 1
    · exact Or.inl hx
    · right
      push_neg at hx
      show w x⁻¹ ≤ 1
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ hx.le

lemma mem_abvSubring (w : AbsoluteValue K ℝ) (x : K) : x ∈ abvSubring Fq w ↔ w x ≤ 1 := Iff.rfl

lemma abvSubring_ne_top (w : AbsoluteValue K ℝ) (hw : w.IsNontrivial) : abvSubring Fq w ≠ ⊤ := by
  obtain ⟨x, hx0, hx1⟩ := hw
  intro h
  have hx : x ∈ abvSubring Fq w := h ▸ trivial
  have hxi : x⁻¹ ∈ abvSubring Fq w := h ▸ trivial
  rw [mem_abvSubring] at hx hxi
  rw [map_inv₀] at hxi
  have hpos : 0 < w x := w.pos hx0
  have : 1 ≤ w x := by
    rwa [inv_le_one₀ hpos] at hxi
  exact hx1 (le_antisymm hx this)

end Generic

section FF

variable {Fq K : Type*} [Field Fq] [Finite Fq] [Field K] [Algebra Fq K]

/-- The place of `K` attached to a nontrivial absolute value (Stichtenoth, Theorem 1.1.6). -/
noncomputable def placeOf (hF : TauCeti.IsFunctionField Fq K) (w : AbsoluteValue K ℝ)
    (hw : w.IsNontrivial) : Place Fq K :=
  let P := TauCeti.Place.ofValuationSubring (A := abvSubring Fq w) hF
    (fun c => (mem_abvSubring Fq w _).2 (abv_algebraMap_le_one Fq w c)) (abvSubring_ne_top Fq w hw)
  ⟨P.valuation, P.valuation_surjective, P.isTrivialOn⟩

lemma placeOf_mem_integers (hF : TauCeti.IsFunctionField Fq K) (w : AbsoluteValue K ℝ)
    (hw : w.IsNontrivial) (x : K) : x ∈ (placeOf hF w hw).integers ↔ w x ≤ 1 := by
  have h := TauCeti.Place.integers_ofValuationSubring (A := abvSubring Fq w) hF
    (fun c => (mem_abvSubring Fq w _).2 (abv_algebraMap_le_one Fq w c)) (abvSubring_ne_top Fq w hw)
  have h2 : x ∈ (TauCeti.Place.ofValuationSubring (A := abvSubring Fq w) hF
    (fun c => (mem_abvSubring Fq w _).2 (abv_algebraMap_le_one Fq w c))
    (abvSubring_ne_top Fq w hw)).integers ↔ w x ≤ 1 := by
    rw [h]; exact mem_abvSubring Fq w x
  exact h2

lemma placeOf_one_lt (hF : TauCeti.IsFunctionField Fq K) (w : AbsoluteValue K ℝ)
    (hw : w.IsNontrivial) (x : K) : 1 < w x ↔ 1 < (placeOf hF w hw).valuation x := by
  have h := placeOf_mem_integers hF w hw x
  rw [Place.mem_integers_iff] at h
  rw [← not_le, ← not_le, h]

lemma placeOf_lt_one (hF : TauCeti.IsFunctionField Fq K) (w : AbsoluteValue K ℝ)
    (hw : w.IsNontrivial) {x : K} (hx : x ≠ 0) : w x < 1 ↔ (placeOf hF w hw).valuation x < 1 := by
  have h := placeOf_one_lt hF w hw x⁻¹
  rw [map_inv₀, map_inv₀] at h
  have hwpos : 0 < w x := w.pos hx
  have hvpos : 0 < (placeOf hF w hw).valuation x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx)
  rwa [one_lt_inv₀ hwpos, one_lt_inv₀ hvpos] at h

lemma placeOf_eq_one (hF : TauCeti.IsFunctionField Fq K) (w : AbsoluteValue K ℝ)
    (hw : w.IsNontrivial) {x : K} (hx : x ≠ 0) : w x = 1 ↔ (placeOf hF w hw).valuation x = 1 := by
  have h1 := placeOf_lt_one hF w hw hx
  have h2 := placeOf_one_lt hF w hw x
  constructor
  · intro h
    rcases lt_trichotomy ((placeOf hF w hw).valuation x) 1 with h3 | h3 | h3
    · exact absurd (h1.2 h3) (by rw [h]; exact lt_irrefl _)
    · exact h3
    · exact absurd (h2.2 h3) (by rw [h]; exact lt_irrefl _)
  · intro h
    rcases lt_trichotomy (w x) 1 with h3 | h3 | h3
    · exact absurd (h1.1 h3) (by rw [h]; exact lt_irrefl _)
    · exact h3
    · exact absurd (h2.1 h3) (by rw [h]; exact lt_irrefl _)

lemma isEquiv_of_placeOf_eq (hF : TauCeti.IsFunctionField Fq K) (a b : AbsoluteValue K ℝ)
    (ha : a.IsNontrivial) (hb : b.IsNontrivial) (h : placeOf hF a ha = placeOf hF b hb) :
    a.IsEquiv b := by
  rw [AbsoluteValue.isEquiv_iff_lt_one_iff]
  intro x
  by_cases hx : x = 0
  · subst hx; simp
  · rw [placeOf_lt_one hF a ha hx, placeOf_lt_one hF b hb hx, h]

variable [Algebra (RatFunc Fq) K] [IsScalarTower Fq (RatFunc Fq) K] [FunctionField Fq K]

lemma exists_unit_div (P Q : Place Fq K) (hPQ : P ≠ Q) :
    ∃ f : Kˣ, Divisor.div f P ≠ 0 ∧ ∀ R, R ≠ P → R ≠ Q → Divisor.div f R = 0 := by
  classical
  set D : Divisor Fq K :=
    (Q.degree : ℤ) • Finsupp.single P (1 : ℤ) - (P.degree : ℤ) • Finsupp.single Q (1 : ℤ) with hD
  have hdeg : Divisor.deg D = 0 := by
    simp only [hD, map_sub, map_zsmul, Divisor.deg_single]
    simp only [smul_eq_mul]
    ring
  let d : (Divisor.deg (Fq := Fq) (k := K)).ker := ⟨D, hdeg⟩
  haveI := finite_classGroup0 (Fq := Fq) (k := K)
  let c : ClassGroup0 Fq K := QuotientAddGroup.mk d
  have hfin : IsOfFinAddOrder c := isOfFinAddOrder_of_finite c
  have hn : 0 < addOrderOf c := hfin.addOrderOf_pos
  have hc : addOrderOf c • c = 0 := addOrderOf_nsmul_eq_zero c
  have hmem : addOrderOf c • d ∈ (principalDivisors Fq K).addSubgroupOf Divisor.deg.ker := by
    rw [← QuotientAddGroup.eq_zero_iff]
    simpa [c] using hc
  have hmem' : ((addOrderOf c • d : Divisor.deg.ker) : Divisor Fq K) ∈ principalDivisors Fq K :=
    (AddSubgroup.mem_addSubgroupOf).1 hmem
  obtain ⟨u, hu⟩ := (mem_principalDivisors_iff _).1 hmem'
  have hval : ∀ R, Divisor.div u R = (addOrderOf c : ℤ) * (
      (Q.degree : ℤ) * (Finsupp.single P (1 : ℤ)) R - (P.degree : ℤ) * (Finsupp.single Q (1 : ℤ)) R) := by
    intro R
    have h : ((addOrderOf c • d : Divisor.deg.ker) : Divisor Fq K) = addOrderOf c • D :=
      AddSubgroup.coe_nsmul _ _ _
    rw [hu, h]
    simp only [hD, Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul]
    ring
  refine ⟨u, ?_, ?_⟩
  · rw [hval]
    simp only [Finsupp.single_eq_same, Finsupp.single_apply, if_neg hPQ.symm, if_neg hPQ]
    have := Q.degree_pos
    have := hn
    simp only [mul_one, mul_zero, sub_zero]
    positivity
  · intro R h1 h2
    rw [hval]
    simp [Finsupp.single_apply, Ne.symm h1, Ne.symm h2]

variable (Fq K) in
lemma isFunctionField_of_functionField : TauCeti.IsFunctionField Fq K :=
  (TauCeti.isFunctionField_iff_functionField).2 inferInstance

end FF

/-- **Artin–Whaples, function field case** (Milne ANT v3.08, Aside 8.9, p. 138). -/
@[kb "milne2020ant" "v3.08, Aside 8.9, p. 138"]
theorem exists_mem_isEquiv_of_productFormula_FF {K : Type} [Field K] {Fq : Type} [Field Fq] [Finite Fq]
    [Algebra (RatFunc Fq) K] [FiniteDimensional (RatFunc Fq) K] (V : Set (AbsoluteValue K ℝ)) (hV : AWAxioms V)
    (hne : V.Nonempty) : ∀ w : AbsoluteValue K ℝ, w.IsNontrivial → ∃ v ∈ V, w.IsEquiv v := by
  classical
  letI : Algebra Fq K := ((algebraMap (RatFunc Fq) K).comp (algebraMap Fq (RatFunc Fq))).toAlgebra
  haveI : IsScalarTower Fq (RatFunc Fq) K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FunctionField Fq K := inferInstanceAs (FiniteDimensional (RatFunc Fq) K)
  have hF : TauCeti.IsFunctionField Fq K := isFunctionField_of_functionField Fq K
  intro w hw
  by_contra hcon
  push_neg at hcon
  obtain ⟨v₀, hv₀⟩ := hne
  have hnt0 := hV.nontrivial v₀ hv₀
  have hPQ : placeOf hF v₀ hnt0 ≠ placeOf hF w hw := by
    intro h
    exact hcon v₀ hv₀ (isEquiv_of_placeOf_eq hF v₀ w hnt0 hw h).symm
  obtain ⟨f, hf0, hf⟩ := exists_unit_div (placeOf hF v₀ hnt0) (placeOf hF w hw) hPQ
  have hfne : (f : K) ≠ 0 := f.ne_zero
  have hother : ∀ v ∈ V, v ≠ v₀ → v f = 1 := by
    intro v hv hvne
    have hnt := hV.nontrivial v hv
    have h1 : placeOf hF v hnt ≠ placeOf hF v₀ hnt0 := by
      intro h
      exact hvne (hV.ineq v hv v₀ hv₀ (isEquiv_of_placeOf_eq hF v v₀ hnt hnt0 h))
    have h2 : placeOf hF v hnt ≠ placeOf hF w hw := by
      intro h
      exact hcon v hv (isEquiv_of_placeOf_eq hF v w hnt hw h).symm
    have h3 := hf _ h1 h2
    rw [Divisor.div_apply, Place.ord] at h3
    have h4 : (placeOf hF v hnt).valuation (f : K) = 1 := by
      have h5 := Divisor.valuation_eq_exp_neg_ord (placeOf hF v hnt) hfne
      rw [h5]
      have : (placeOf hF v hnt).ord (f : K) = 0 := h3
      rw [this]; simp
    exact (placeOf_eq_one hF v hnt hfne).2 h4
  have hv0 : v₀ f ≠ 1 := by
    intro h
    have h4 := (placeOf_eq_one hF v₀ hnt0 hfne).1 h
    apply hf0
    rw [Divisor.div_apply]
    have h5 := Divisor.valuation_eq_exp_neg_ord (placeOf hF v₀ hnt0) hfne
    rw [h4] at h5
    have : WithZero.exp (-(placeOf hF v₀ hnt0).ord (f : K)) = WithZero.exp 0 := by
      rw [← h5]; simp
    have := WithZero.exp_injective this
    omega
  have hprod := (hV.prod (f : K) hfne).2
  have hsub : ({v₀} : Finset (AbsoluteValue K ℝ)) ⊆ {v₀} := subset_rfl
  have : ∏ᶠ (v ∈ V), v (f : K) = ∏ v ∈ ({v₀} : Finset (AbsoluteValue K ℝ)), v (f : K) := by
    refine finprod_mem_eq_prod_of_subset _ ?_ (by simpa using hv₀)
    intro v ⟨hv, hs⟩
    by_contra hvn
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hvn
    exact hs (hother v hv hvn)
  rw [this, Finset.prod_singleton] at hprod
  exact hv0 hprod

end NumberFieldKB.MilneANT.Aside89
