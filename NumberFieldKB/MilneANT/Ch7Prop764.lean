import NumberFieldKB.MilneANT.Ch7NormOfDVR
import NumberFieldKB.MilneANT.Ch7Krasner
import NumberFieldKB.MilneANT.Ch7RamificationFields

/-!
# Milne, *Algebraic Number Theory*, Prop. 7.64 (finiteness of totally ramified extensions of given degree)

Proof following Milne: Eisenstein coefficient vectors `eisSet` form a compact set (`isCompact_eisSet`, from
`Ch7NormOfDVR`); Krasner-type `prop_7_63` gives a neighbourhood of each such polynomial on which the generated
fields agree; a finite subcover and `prop_7_55` conclude (`prop_7_64_pos`, positive degrees).
-/

open IsLocalRing Polynomial

universe u v

namespace NumberFieldKB.MilneANT

section Poly

variable {R : Type*} [CommRing R]

/-- The monic polynomial `X^(d+1) + ∑ cᵢ Xⁱ`. -/
noncomputable def eisPoly (d : ℕ) (c : Fin (d + 1) → R) : R[X] :=
  X ^ (d + 1) + ∑ i : Fin (d + 1), C (c i) * X ^ (i : ℕ)

lemma eisPoly_coeff (d : ℕ) (c : Fin (d + 1) → R) (j : ℕ) :
    (eisPoly d c).coeff j =
      if h : j < d + 1 then c ⟨j, h⟩ else if j = d + 1 then 1 else 0 := by
  unfold eisPoly
  rw [coeff_add, finset_sum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  by_cases h : j < d + 1
  · rw [dif_pos h, if_neg (by omega)]
    rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ j := fun h' => hb (Fin.ext h')
      simp [this.symm]
    · simp
  · rw [dif_neg h]
    rw [Finset.sum_eq_zero]
    · by_cases h2 : j = d + 1 <;> simp [h2]
    · intro b _
      have : j ≠ (b : ℕ) := by have := b.2; omega
      simp [this]

lemma eisPoly_monic (d : ℕ) (c : Fin (d + 1) → R) : (eisPoly d c).Monic := by
  unfold eisPoly
  apply Polynomial.monic_X_pow_add
  exact degree_sum_fin_lt c

lemma eisPoly_map {S : Type*} [CommRing S] (f : R →+* S) (d : ℕ) (c : Fin (d + 1) → R) :
    (eisPoly d c).map f = eisPoly d (f ∘ c) := by
  simp [eisPoly, Polynomial.map_sum]

lemma eisPoly_natDegree [Nontrivial R] (d : ℕ) (c : Fin (d + 1) → R) : (eisPoly d c).natDegree = d + 1 :=
  by
  unfold eisPoly
  rw [natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt c)]
  simp

end Poly

section PolyK

variable {K : Type v} [NontriviallyNormedField K]

lemma polyNorm_eisPoly_sub_le (d : ℕ) (c c' : Fin (d + 1) → K) :
    polyNorm (eisPoly d c - eisPoly d c') ≤ dist c c' := by
  unfold polyNorm
  refine ciSup_le fun j => ?_
  rw [coeff_sub, eisPoly_coeff, eisPoly_coeff]
  by_cases h : j < d + 1
  · simp only [h, dite_true]
    rw [← dist_eq_norm]
    exact dist_le_pi_dist c c' ⟨j, h⟩
  · simp only [h, dite_false, sub_self, norm_zero]
    exact dist_nonneg

end PolyK

set_option linter.unusedSectionVars false

section Core

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
  {K : Type v} [NontriviallyNormedField K] [Algebra A K] [IsFractionRing A K]

/-- The set of coefficient vectors of Eisenstein polynomials, in terms of the norm. -/
def eisSet (ρ : ℝ) (d : ℕ) : Set (Fin (d + 1) → K) :=
  {c | (∀ i, ‖c i‖ ≤ ρ) ∧ ρ ≤ ‖c 0‖}

lemma isCompact_eisSet (hn : ∀ x : K, ‖x‖ = dvrAbv A K x) [Finite (ResidueField A)] {ρ : ℝ} (hρ : ρ ≤ 1)
    (d : ℕ) : IsCompact (eisSet ρ d : Set (Fin (d + 1) → K)) := by
  have := dvr_isUltrametricDist hn
  have h1 := isCompact_univ_pi (fun _ : Fin (d + 1) => dvr_isCompact_closedBall hn)
  have hclosed : IsClosed (eisSet ρ d : Set (Fin (d + 1) → K)) := by
    have : eisSet ρ d = (⋂ i, {c : Fin (d + 1) → K | ‖c i‖ ≤ ρ}) ∩ {c | ρ ≤ ‖c 0‖} := by
      ext c; simp [eisSet]
    rw [this]
    exact IsClosed.inter (isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const)
      (isClosed_le continuous_const (by fun_prop))
  refine h1.of_isClosed_subset hclosed ?_
  intro c hc i _
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (hc.1 i).trans hρ

lemma irreducible_eisPoly (hn : ∀ x : K, ‖x‖ = dvrAbv A K x) {π : A} (hπ : Irreducible π) (d : ℕ)
    {c : Fin (d + 1) → K} (hc : c ∈ eisSet ‖algebraMap A K π‖ d) : Irreducible (eisPoly d c) := by
  have hρ0 := dvr_norm_pi_pos hn hπ
  have hρ1 := dvr_norm_pi_lt_one hn hπ
  have hcA : ∀ i, ∃ a : A, algebraMap A K a = c i := fun i =>
    dvr_exists_of_norm_le_one hn _ ((hc.1 i).trans hρ1.le)
  choose a ha using hcA
  have hcomp : c = algebraMap A K ∘ a := funext fun i => (ha i).symm
  have hmem : ∀ i, a i ∈ maximalIdeal A := fun i => by
    rw [← dvr_norm_lt_one_iff (K := K) hn, ha]; exact (hc.1 i).trans_lt hρ1
  have hnot : a 0 ∉ maximalIdeal A ^ 2 := by
    intro h
    have h2 := (dvr_norm_le_pow_iff (K := K) hn hπ (a 0) 2).2 h
    rw [ha] at h2
    have := hc.2
    nlinarith
  have hQ : (eisPoly d a).IsEisensteinAt (maximalIdeal A) :=
    { leading := by
        rw [(eisPoly_monic d a).leadingCoeff]
        exact (IsLocalRing.notMem_maximalIdeal.2 isUnit_one)
      mem := fun {n} hn' => by
        rw [eisPoly_natDegree] at hn'
        rw [eisPoly_coeff, dif_pos hn']
        exact hmem _
      notMem := by
        rw [eisPoly_coeff, dif_pos (by omega)]
        exact hnot }
  have hirr : Irreducible (eisPoly d a) :=
    hQ.irreducible inferInstance (eisPoly_monic d a).isPrimitive
      (by rw [eisPoly_natDegree]; omega)
  have := (Monic.irreducible_iff_irreducible_map_fraction_map (K := K) (eisPoly_monic d a)).1 hirr
  rwa [eisPoly_map, ← hcomp] at this

open IntermediateField in
lemma exists_eisPoly_of_totallyRamified [CharZero K] (hn : ∀ x : K, ‖x‖ = dvrAbv A K x) {π : A}
    (hπ : Irreducible π) (d : ℕ) (E : IntermediateField K (AlgebraicClosure K))
    (hE : Module.finrank K E = d + 1) (htr : IsTotallyRamifiedMilne A K E) :
    ∃ c ∈ eisSet ‖algebraMap A K π‖ d,
      ∃ β ∈ ((eisPoly d c).map (algebraMap K (AlgebraicClosure K))).roots, E = K⟮β⟯ := by
  have hfin : FiniteDimensional K E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨α, hα, f, hf, h0⟩ := (prop_7_55 A K E).1 htr
  have hρ0 := dvr_norm_pi_pos hn hπ
  have hρ1 := dvr_norm_pi_lt_one hn hπ
  have hlcu : IsUnit f.leadingCoeff := IsLocalRing.notMem_maximalIdeal.mp hf.leading
  have hinjA : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hinjE : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A K E]; exact (algebraMap K E).injective.comp hinjA
  have hd : f.natDegree ≠ 0 := by
    intro h
    have hC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero h
    rw [hC, aeval_C] at h0
    have h00 : f.coeff 0 = 0 := hinjE (h0.trans (map_zero _).symm)
    exact hf.notMem (by simp [h00])
  have hprim : f.IsPrimitive := by
    intro r hr
    obtain ⟨g, hg⟩ := hr
    refine isUnit_of_dvd_unit ?_ hlcu
    rw [hg, leadingCoeff_mul, leadingCoeff_C]
    exact dvd_mul_right _ _
  have hirr : Irreducible f := hf.irreducible inferInstance hprim (Nat.pos_of_ne_zero hd)
  set f₀ : K[X] := f.map (algebraMap A K) with hf₀
  have hirr0 : Irreducible f₀ :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := K)).1 hirr
  have hlc0 : f₀.leadingCoeff = algebraMap A K f.leadingCoeff := leadingCoeff_map_of_injective hinjA f
  have hlc0ne : f₀.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hirr0.ne_zero
  set g : K[X] := f₀ * C f₀.leadingCoeff⁻¹ with hg
  have hgmon : g.Monic := monic_mul_leadingCoeff_inv hirr0.ne_zero
  have hgirr : Irreducible g :=
    (irreducible_mul_isUnit (isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero hlc0ne)))).2 hirr0
  have hroot : aeval α g = 0 := by
    rw [hg, map_mul, hf₀, aeval_map_algebraMap K α f, h0, zero_mul]
  have hmin : g = minpoly K α := minpoly.eq_of_irreducible_of_monic hgirr hroot hgmon
  have hdeg : g.natDegree = d + 1 := by
    rw [hmin, ← hE]
    have hint : IsIntegral K α := .of_finite K α
    rw [← IntermediateField.adjoin.finrank hint, hα]
    exact IntermediateField.finrank_top'
  have hfd : f.natDegree = d + 1 := by
    rw [← hdeg, hg, natDegree_mul_C (inv_ne_zero hlc0ne), hf₀, natDegree_map_eq_of_injective hinjA]
  have hnorm_lc : ‖f₀.leadingCoeff⁻¹‖ = 1 := by
    rw [norm_inv, hlc0, (dvr_norm_eq_one_iff hn _).2 hlcu, inv_one]
  have hcoeff : ∀ i, ‖g.coeff i‖ = ‖algebraMap A K (f.coeff i)‖ := by
    intro i
    rw [hg, coeff_mul_C, norm_mul, hnorm_lc, mul_one, hf₀, coeff_map]
  set c : Fin (d + 1) → K := fun i => g.coeff i with hc
  have hgc : g = eisPoly d c := by
    ext j
    rw [eisPoly_coeff]
    split_ifs with h1 h2
    · rfl
    · rw [h2, ← hdeg, hgmon.coeff_natDegree]
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hcmem : c ∈ eisSet ‖algebraMap A K π‖ d := by
    refine ⟨fun i => ?_, ?_⟩
    · simp only [hc]
      rw [hcoeff]
      have := (dvr_norm_le_pow_iff (K := K) hn hπ (f.coeff i) 1).2
        (by rw [pow_one]; exact hf.mem (by omega))
      simpa using this
    · simp only [hc]
      rw [hcoeff]
      exact (dvr_norm_eq_of_mem_not_mem_sq hn hπ (hf.mem (by omega)) hf.notMem).ge
  refine ⟨c, hcmem, (α : AlgebraicClosure K), ?_, ?_⟩
  · rw [← hgc, mem_roots (hgmon.map _).ne_zero, IsRoot, eval_map_algebraMap]
    have := aeval_algHom_apply E.val α g
    rw [hroot, map_zero] at this
    exact this
  · have hmap : (IntermediateField.adjoin K {α}).map E.val = K⟮(α : AlgebraicClosure K)⟯ := by
      rw [IntermediateField.adjoin_map]; simp
    rw [hα] at hmap
    rw [← hmap]
    ext x
    simp

end Core

section Main

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]

open IntermediateField in
/-- **Proposition 7.64.** Let $K$ have characteristic zero and finite residue field. For each degree
$n = d + 1 \ge 1$ there are only finitely many totally ramified extensions of $K$ of degree $n$ inside $K^{\mathrm{al}}$.
Milne's proof: Eisenstein generators (Prop. 7.55) have coefficients in a compact set, and Prop. 7.63 (Krasner) makes
the set of fields locally constant on it.

This is Milne's statement ("extensions of degree $n$" are finite); it discharges the corrected named statement
`Prop7_64` (`prop_7_64`, `Ch7Prop764Zero.lean`; erratum for $n = 0$ in `Ch7Prop764Erratum.lean`). -/
@[kb "milne2020ant" "v3.08, Prop. 7.64, p. 133"]
theorem prop_7_64_pos [CharZero K] [Finite (ResidueField A)] (d : ℕ) :
    {E : IntermediateField K (AlgebraicClosure K) |
      Module.finrank K E = d + 1 ∧ IsTotallyRamifiedMilne A K E}.Finite := by
  letI : NontriviallyNormedField K := dvrNontriviallyNormedField A K
  have hn : ∀ x : K, ‖x‖ = dvrAbv A K x := fun _ => rfl
  haveI := dvr_isUltrametricDist hn
  haveI := dvr_completeSpace hn
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hρ1 := dvr_norm_pi_lt_one hn hπ
  have hcomp := isCompact_eisSet hn hρ1.le d
  have hδ : ∀ c : Fin (d + 1) → K, ∃ δ : ℝ, 0 < δ ∧ (c ∈ eisSet ‖algebraMap A K π‖ d →
      ∀ g : K[X], g.Monic → Irreducible g → polyNorm (eisPoly d c - g) < δ →
        {E | ∃ α ∈ ((eisPoly d c).map (algebraMap K (AlgebraicClosure K))).roots, E = K⟮α⟯} =
          {E | ∃ β ∈ (g.map (algebraMap K (AlgebraicClosure K))).roots, E = K⟮β⟯}) := by
    intro c
    by_cases hc : c ∈ eisSet ‖algebraMap A K π‖ d
    · obtain ⟨δ, hδ, H⟩ := prop_7_63 (eisPoly d c) (eisPoly_monic d c) (irreducible_eisPoly hn hπ d hc)
      exact ⟨δ, hδ, fun _ g hg hirr h => (H g hg hirr h).2⟩
    · exact ⟨1, one_pos, fun h => absurd h hc⟩
  choose δ hδpos hδ using hδ
  obtain ⟨t, htT, hcover⟩ := hcomp.elim_nhds_subcover (fun c => Metric.ball c (δ c))
    (fun c _ => Metric.ball_mem_nhds c (hδpos c))
  have hfin : ∀ f : K[X], {E | ∃ α ∈ (f.map (algebraMap K (AlgebraicClosure K))).roots,
      E = K⟮α⟯}.Finite := by
    intro f
    classical
    refine ((f.map (algebraMap K (AlgebraicClosure K))).roots.toFinset.finite_toSet.image
      (fun α => K⟮α⟯)).subset ?_
    rintro E ⟨α, hα, rfl⟩
    exact ⟨α, Multiset.mem_toFinset.2 hα, rfl⟩
  refine (t.finite_toSet.biUnion fun c _ => hfin (eisPoly d c)).subset ?_
  rintro E ⟨hE, htr⟩
  obtain ⟨c, hc, β, hβ, hEβ⟩ := exists_eisPoly_of_totallyRamified hn hπ d E hE htr
  obtain ⟨c', hc't, hcc'⟩ := Set.mem_iUnion₂.1 (hcover hc)
  have hd : dist c' c < δ c' := by rw [dist_comm]; exact Metric.mem_ball.1 hcc'
  have := hδ c' (htT c' hc't) (eisPoly d c) (eisPoly_monic d c) (irreducible_eisPoly hn hπ d hc)
    ((polyNorm_eisPoly_sub_le d c' c).trans_lt hd)
  refine Set.mem_iUnion₂.2 ⟨c', hc't, ?_⟩
  show E ∈ {E | ∃ α ∈ ((eisPoly d c').map (algebraMap K (AlgebraicClosure K))).roots, E = K⟮α⟯}
  rw [this]
  exact ⟨β, hβ, hEβ⟩

end Main


end NumberFieldKB.MilneANT
