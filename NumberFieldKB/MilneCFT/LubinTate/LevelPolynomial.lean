import NumberFieldKB.MilneCFT.LubinTate.TorsionYamaguchi

/-!
# The level polynomial of a Lubin-Tate extension (Milne, *CFT*, I, §3)

Write `f = π X + X^q` for the Lubin-Tate polynomial and `f^{(n)}` for its `n`-fold composite.  Since
`f(Y) = Y (Y^{q-1} + π)`, the next composite factors as `f^{(n+1)} = f^{(n)} · Q_n`, where
`Q_n = (f^{(n)})^{q-1} + π` (`ltPrim`).  This file shows:

* `Q_n` is monic of degree `(q-1) q^n`, all of its non-leading coefficients lie in the maximal ideal, and its
  constant coefficient is `π`; so it is an Eisenstein polynomial (`ltPrim_isDistinguishedAt`);
* an Eisenstein polynomial over a discrete valuation ring stays irreducible over the fraction field
  (`irreducible_map_of_eisenstein`), hence `Q_n` is irreducible over the fraction field of every discrete valuation
  ring in which `π` stays irreducible, in particular over `K` itself;
* inside a separable closure, the primitive torsion point `x₀` of level `n + 1` has minimal polynomial `Q_n`
  (`minpoly_x0_eq_ltPrim`), every root of `Q_n` is a torsion point of level `n + 1`, and every root of `Q_n`
  generates the whole field `K_{π,n+1}` (`ltField_eq_adjoin_of_root`).
-/

open scoped ValuativeRel
open Polynomial

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- `Q_n = (f^{(n)})^{q-1} + π`: `f^{(n+1)} = f^{(n)} · Q_n`. -/
def ltPrim (π : 𝒪[K]) (n : ℕ) : 𝒪[K][X] := ltPolyIter π n ^ (resCard K - 1) + C π

theorem ltPolyIter_succ_eq_mul_ltPrim {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    ltPolyIter π (n + 1) = ltPolyIter π n * ltPrim π n := by
  have hq : 2 ≤ resCard K := (lubinTateHyp_of_isNonarchimedeanLocalField K hπ).one_lt
  obtain ⟨r, hr⟩ : ∃ r, resCard K = r + 1 := ⟨resCard K - 1, by omega⟩
  rw [ltPolyIter_succ, ltPrim]
  simp only [ltPoly, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
    Polynomial.X_pow_comp, hr, Nat.add_sub_cancel]
  ring

theorem ltPolyIter_eval_zero {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) : (ltPolyIter π n).coeff 0 = 0 := by
  have hq : 2 ≤ resCard K := (lubinTateHyp_of_isNonarchimedeanLocalField K hπ).one_lt
  induction n with
  | zero => simp [ltPolyIter]
  | succ n ih =>
    rw [coeff_zero_eq_eval_zero] at ih ⊢
    rw [ltPolyIter_succ, eval_comp, ih]
    simp [ltPoly, show resCard K ≠ 0 by omega]

theorem ltPrim_coeff_zero {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) : (ltPrim π n).coeff 0 = π := by
  have hq : 2 ≤ resCard K := (lubinTateHyp_of_isNonarchimedeanLocalField K hπ).one_lt
  rw [ltPrim, coeff_add, coeff_zero_eq_eval_zero (ltPolyIter π n ^ _), eval_pow,
    ← coeff_zero_eq_eval_zero, ltPolyIter_eval_zero hπ, zero_pow (by omega), zero_add, coeff_C_zero]

theorem ltPrim_monic {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) : (ltPrim π n).Monic := by
  have hq : 2 ≤ resCard K := (lubinTateHyp_of_isNonarchimedeanLocalField K hπ).one_lt
  have hm : (ltPolyIter π n ^ (resCard K - 1)).Monic := (ltPolyIter_aux hπ n).1.pow _
  have hd : (ltPolyIter π n ^ (resCard K - 1)).natDegree = (resCard K - 1) * resCard K ^ n := by
    rw [natDegree_pow, ltPolyIter_natDegree hπ]
  have hpos : 0 < (resCard K - 1) * resCard K ^ n := Nat.mul_pos (by omega) (by positivity)
  refine hm.add_of_left (lt_of_le_of_lt degree_C_le ?_)
  rw [degree_eq_natDegree hm.ne_zero, hd]
  exact_mod_cast hpos

theorem ltPrim_natDegree {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    (ltPrim π n).natDegree = (resCard K - 1) * resCard K ^ n := by
  have hq : 2 ≤ resCard K := (lubinTateHyp_of_isNonarchimedeanLocalField K hπ).one_lt
  have hd : (ltPolyIter π n ^ (resCard K - 1)).natDegree = (resCard K - 1) * resCard K ^ n := by
    rw [natDegree_pow, ltPolyIter_natDegree hπ]
  have hpos : 0 < (resCard K - 1) * resCard K ^ n := Nat.mul_pos (by omega) (by positivity)
  rw [ltPrim, natDegree_add_eq_left_of_natDegree_lt, hd]
  rw [hd]
  exact (natDegree_C _).trans_lt hpos

theorem ltPrim_isDistinguishedAt {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    (ltPrim π n).IsDistinguishedAt 𝓂[K] := by
  have hq : 2 ≤ resCard K := (lubinTateHyp_of_isNonarchimedeanLocalField K hπ).one_lt
  refine ⟨⟨fun {i} hi => ?_⟩, ltPrim_monic hπ n⟩
  have hπm : π ∈ 𝓂[K] := by
    rw [hπ.maximalIdeal_eq]; exact Ideal.subset_span rfl
  have hmap : (ltPrim π n).map (Ideal.Quotient.mk 𝓂[K]) = X ^ ((resCard K - 1) * resCard K ^ n) := by
    rw [ltPrim, Polynomial.map_add, Polynomial.map_pow, (ltPolyIter_aux hπ n).2.2, Polynomial.map_C,
      (Ideal.Quotient.eq_zero_iff_mem.2 hπm), C_0, add_zero, ← pow_mul, mul_comm]
  have := congrArg (fun p => p.coeff i) hmap
  simp only [coeff_map, coeff_X_pow] at this
  rw [ltPrim_natDegree hπ] at hi
  rw [← Ideal.Quotient.eq_zero_iff_mem, this]
  simp [show i ≠ (resCard K - 1) * resCard K ^ n by omega]

/-- Generic Eisenstein criterion over a discrete valuation ring, read in the fraction field. -/
theorem irreducible_map_of_eisenstein {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {F : Type*} [Field F] [Algebra B F] [IsFractionRing B F] {Q : B[X]} (hm : Q.Monic) (hd : 0 < Q.natDegree)
    (hcoeff : ∀ i < Q.natDegree, Q.coeff i ∈ IsLocalRing.maximalIdeal B)
    (hconst : Q.coeff 0 ∉ IsLocalRing.maximalIdeal B ^ 2) :
    Irreducible (Q.map (algebraMap B F)) := by
  have hlead : Q.leadingCoeff ∉ IsLocalRing.maximalIdeal B := by
    rw [hm.leadingCoeff]
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hE : Q.IsEisensteinAt (IsLocalRing.maximalIdeal B) :=
    ⟨hlead,
      fun {i} hi => hcoeff i hi, hconst⟩
  have hirr : Irreducible Q :=
    hE.irreducible (IsLocalRing.maximalIdeal.isMaximal B).isPrime hm.isPrimitive hd
  exact (hm.irreducible_iff_irreducible_map_fraction_map).1 hirr

theorem ltPrim_map_irreducible {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra 𝒪[K] B] {F : Type*} [Field F] [Algebra B F] [IsFractionRing B F] {π : 𝒪[K]} (hπ : Irreducible π)
    (hB : Irreducible (algebraMap 𝒪[K] B π)) (n : ℕ) :
    Irreducible ((ltPrim π n).map ((algebraMap B F).comp (algebraMap 𝒪[K] B))) := by
  rw [← Polynomial.map_map]
  set Q := (ltPrim π n).map (algebraMap 𝒪[K] B) with hQ
  have hm : Q.Monic := (ltPrim_monic hπ n).map _
  have hdeg : Q.natDegree = (resCard K - 1) * resCard K ^ n := by
    rw [hQ, (ltPrim_monic hπ n).natDegree_map, ltPrim_natDegree hπ]
  have hq : 2 ≤ resCard K := (lubinTateHyp_of_isNonarchimedeanLocalField K hπ).one_lt
  have hpos : 0 < (resCard K - 1) * resCard K ^ n := Nat.mul_pos (by omega) (by positivity)
  have hπB : algebraMap 𝒪[K] B π ∈ IsLocalRing.maximalIdeal B := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hB.not_isUnit
  refine irreducible_map_of_eisenstein hm (hdeg ▸ hpos) (fun i hi => ?_) ?_
  · rw [hQ, coeff_map]
    have := (ltPrim_isDistinguishedAt hπ n).mem (n := i) (by rw [ltPrim_natDegree hπ]; rwa [hdeg] at hi)
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    rw [hc, map_mul]
    exact Ideal.mul_mem_right _ _ hπB
  · rw [hQ, coeff_map, ltPrim_coeff_zero hπ]
    intro h
    rw [hB.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    have h1 : algebraMap 𝒪[K] B π * 1 = algebraMap 𝒪[K] B π * (algebraMap 𝒪[K] B π * c) := by
      rw [mul_one, ← mul_assoc, ← pow_two]; exact hc
    exact hB.not_isUnit (isUnit_iff_exists_inv.2 ⟨c, (mul_left_cancel₀ hB.ne_zero h1).symm⟩)

theorem ltPrim_map_irreducible_K {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    Irreducible ((ltPrim π n).map (algebraMap 𝒪[K] K)) := by
  have := ltPrim_map_irreducible (B := 𝒪[K]) (F := K) hπ (by simpa using hπ) n
  simpa using this

variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem aeval_x0_ltPrim {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    aeval (x0 Ω hπ n) ((ltPrim π n).map (algebraMap 𝒪[K] K)) = 0 := by
  have h1 : aeval (x0 Ω hπ n) ((ltPolyIter π (n + 1)).map (algebraMap 𝒪[K] K)) = 0 := by
    have := x0_mem Ω hπ n
    rw [ltTorsion, mem_rootSet] at this
    exact this.2
  rw [ltPolyIter_succ_eq_mul_ltPrim hπ, Polynomial.map_mul, map_mul] at h1
  have h2 : aeval (x0 Ω hπ n) ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) ≠ 0 := by
    have := aeval_iter_ltAct_x0 Ω hπ n n 1
    rw [ltAct_one_x0, mul_one] at this
    rw [this]
    intro h
    rw [← ltAct_zero_x0 Ω hπ n, ltAct_x0_eq_iff, sub_zero] at h
    exact (by
      rw [Ideal.mem_span_singleton] at h
      obtain ⟨c, hc⟩ := h
      have h1 : π ^ n * 1 = π ^ n * (π * c) := by rw [mul_one]; exact hc.trans (by ring)
      exact hπ.not_isUnit (isUnit_iff_exists_inv.2 ⟨c, (mul_left_cancel₀ (pow_ne_zero n hπ.ne_zero) h1).symm⟩) :
        False)
  exact (mul_eq_zero.1 h1).resolve_left h2

theorem minpoly_x0_eq_ltPrim {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    minpoly K (x0 Ω hπ n) = (ltPrim π n).map (algebraMap 𝒪[K] K) :=
  (minpoly.eq_of_irreducible_of_monic (ltPrim_map_irreducible_K hπ n) (aeval_x0_ltPrim Ω hπ n)
    ((ltPrim_monic hπ n).map _)).symm

/-- The roots of `Q_n` are torsion points of level `n + 1`. -/
theorem mem_ltTorsion_of_root {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) {β : Ω}
    (hβ : aeval β ((ltPrim π n).map (algebraMap 𝒪[K] K)) = 0) : β ∈ ltTorsion Ω π (n + 1) := by
  rw [ltTorsion, mem_rootSet]
  refine ⟨((ltPolyIter_aux hπ (n + 1)).1.map _).ne_zero, ?_⟩
  rw [ltPolyIter_succ_eq_mul_ltPrim hπ, Polynomial.map_mul, map_mul, hβ, mul_zero]

/-- Every root of `Q_n` in `Ω` generates `K_{π,n+1}`. -/
theorem ltField_eq_adjoin_of_root {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) {β : Ω}
    (hβ : aeval β ((ltPrim π n).map (algebraMap 𝒪[K] K)) = 0) :
    ltField Ω π (n + 1) = IntermediateField.adjoin K {β} := by
  have hirr := ltPrim_map_irreducible_K hπ n
  have hmon : ((ltPrim π n).map (algebraMap 𝒪[K] K)).Monic := (ltPrim_monic hπ n).map _
  have hdeg : ((ltPrim π n).map (algebraMap 𝒪[K] K)).natDegree = (resCard K - 1) * resCard K ^ n := by
    rw [(ltPrim_monic hπ n).natDegree_map, ltPrim_natDegree hπ]
  have hxfield : ltField Ω π (n + 1) = IntermediateField.adjoin K {x0 Ω hπ n} := by
    apply le_antisymm
    · rw [ltField, IntermediateField.adjoin_le_iff]
      intro α hα
      obtain ⟨a, rfl⟩ := exists_ltAct_x0 Ω hπ n α hα
      exact IntermediateField.algebra_adjoin_le_adjoin K _ (Polynomial.aeval_mem_adjoin_singleton K _)
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact mem_ltField (x0_mem Ω hπ n)
  have hminβ : minpoly K β = (ltPrim π n).map (algebraMap 𝒪[K] K) :=
    (minpoly.eq_of_irreducible_of_monic hirr hβ hmon).symm
  have hintβ : IsIntegral K β := ⟨_, hmon, by rw [← aeval_def]; exact hβ⟩
  have hintx : IsIntegral K (x0 Ω hπ n) := ⟨_, hmon, by rw [← aeval_def]; exact aeval_x0_ltPrim Ω hπ n⟩
  have hle : IntermediateField.adjoin K {β} ≤ ltField Ω π (n + 1) := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact mem_ltField (mem_ltTorsion_of_root Ω hπ n hβ)
  have : FiniteDimensional K (ltField Ω π (n + 1)) := by
    rw [hxfield]; exact IntermediateField.adjoin.finiteDimensional hintx
  symm
  apply IntermediateField.eq_of_le_of_finrank_eq hle
  rw [hxfield, IntermediateField.adjoin.finrank hintx, IntermediateField.adjoin.finrank hintβ, hminβ,
    minpoly_x0_eq_ltPrim Ω hπ n]

end NumberFieldKB.MilneCFT.LocalCFT
