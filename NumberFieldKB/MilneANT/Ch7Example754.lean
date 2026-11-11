import NumberFieldKB.MilneANT.Ch7Remark753
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Algebraic Number Theory*, Example 7.54: the unramified extensions of a local field

Source: J. S. Milne, *Algebraic Number Theory*, v3.08, Example 7.54, p. 129 (bib key `milne2020ant`).
All four parts of `Example7_54` are derived from Remark 7.53 (`remark_7_53`).
-/

open IsLocalRing Polynomial

universe u v w

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneANT

namespace Example754

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] [Finite (ResidueField A)]
  (L : Type v) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]

include K in
theorem finrank_res (hL : IsUnramifiedMilne A K L) :
    Module.finrank (ResidueField A) (ResidueField (integralClosure A L)) = Module.finrank K L := by
  rw [← Thm758aFixed.resDeg_eq_finrank]; exact hL

include K in
theorem exists_mulEquiv (hL : IsUnramifiedMilne A K L) :
    ∃ ψ : (L ≃ₐ[K] L) ≃* (ResidueField (integralClosure A L) ≃ₐ[ResidueField A]
        ResidueField (integralClosure A L)),
      ∀ (τ : L ≃ₐ[K] L) (b b' : integralClosure A L), (b' : L) = τ b →
        ψ τ (residue _ b) = residue _ b' := by
  classical
  have : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L _
  obtain ⟨Φ, hΦ⟩ := Remark753.hom_equiv A K L L hL hL
  let f : (L ≃ₐ[K] L) →* (ResidueField (integralClosure A L) ≃ₐ[ResidueField A]
        ResidueField (integralClosure A L)) :=
    { toFun := fun τ => AlgEquiv.ofBijective (Φ τ.toAlgHom) (AlgHom.bijective _)
      map_one' := by
        refine AlgEquiv.ext fun x => ?_
        obtain ⟨b, rfl⟩ := residue_surjective x
        exact hΦ (1 : L ≃ₐ[K] L).toAlgHom b b rfl
      map_mul' := by
        intro σ τ
        refine AlgEquiv.ext fun x => ?_
        obtain ⟨b, rfl⟩ := residue_surjective x
        have h1 := hΦ τ.toAlgHom b (Remark753.mapB A K L L τ.toAlgHom b) rfl
        have h2 := hΦ σ.toAlgHom (Remark753.mapB A K L L τ.toAlgHom b)
          (Remark753.mapB A K L L (σ * τ).toAlgHom b) rfl
        have h3 := hΦ (σ * τ).toAlgHom b (Remark753.mapB A K L L (σ * τ).toAlgHom b) rfl
        show Φ (σ * τ).toAlgHom _ = Φ σ.toAlgHom (Φ τ.toAlgHom _)
        rw [h1, h2, h3] }
  have hf : Function.Bijective f := by
    constructor
    · intro τ τ' h
      have : Φ τ.toAlgHom = Φ τ'.toAlgHom := AlgHom.ext fun x => congrArg (fun e => e x) h
      exact AlgEquiv.coe_toAlgHom_injective (Φ.injective this)
    · intro ρ
      let t : L →ₐ[K] L := Φ.symm ρ.toAlgHom
      refine ⟨AlgEquiv.ofBijective t (AlgHom.bijective _), ?_⟩
      refine AlgEquiv.ext fun x => ?_
      show Φ t x = ρ x
      simp [t]
  refine ⟨MulEquiv.ofBijective f hf, fun τ b b' hb' => ?_⟩
  exact hΦ τ.toAlgHom b b' hb'

include K in
theorem frobenius_part (hL : IsUnramifiedMilne A K L) :
    IsGalois K L ∧ ∃ σ : L ≃ₐ[K] L,
      (∀ b b' : integralClosure A L, (b' : L) = σ b →
        b' - b ^ Nat.card (ResidueField A) ∈ maximalIdeal (integralClosure A L)) ∧
      orderOf σ = Module.finrank K L ∧ Subgroup.zpowers σ = ⊤ ∧
      ∀ τ : L ≃ₐ[K] L, (∀ b b' : integralClosure A L, (b' : L) = τ b →
        b' - b ^ Nat.card (ResidueField A) ∈ maximalIdeal (integralClosure A L)) → τ = σ := by
  classical
  have hfinB : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L _
  have : Module.Finite (ResidueField A) (ResidueField (integralClosure A L)) := inferInstance
  have : Finite (ResidueField (integralClosure A L)) := Module.finite_of_finite (ResidueField A)
  have : Fintype (ResidueField A) := Fintype.ofFinite _
  have : Fintype (ResidueField (integralClosure A L)) := Fintype.ofFinite _
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv A K L hL
  have hfr := finrank_res A K L hL
  set frob := FiniteField.frobeniusAlgEquivOfAlgebraic (ResidueField A)
    (ResidueField (integralClosure A L)) with hfrob
  have hfrobx : ∀ x, frob x = x ^ Nat.card (ResidueField A) := by
    intro x
    have := congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic (ResidueField A)
      (ResidueField (integralClosure A L))) x
    rw [Nat.card_eq_fintype_card]
    exact this
  have key : ∀ τ : L ≃ₐ[K] L, (∀ b b' : integralClosure A L, (b' : L) = τ b →
        b' - b ^ Nat.card (ResidueField A) ∈ maximalIdeal (integralClosure A L)) ↔ ψ τ = frob := by
    intro τ
    constructor
    · intro h
      refine AlgEquiv.ext fun x => ?_
      obtain ⟨b, rfl⟩ := residue_surjective x
      have hb := h b ⟨τ b, (Remark753.mapB A K L L τ.toAlgHom b).2⟩ rfl
      rw [hψ τ b ⟨τ b, (Remark753.mapB A K L L τ.toAlgHom b).2⟩ rfl, hfrobx, ← map_pow]
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero] at hb
      exact hb
    · intro h b b' hb'
      rw [← residue_eq_zero_iff, map_sub, map_pow, sub_eq_zero, ← hψ τ b b' hb', h, hfrobx]
  have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := by
    rw [Nat.card_congr ψ.toEquiv, ← hfr, ← IsGalois.card_aut_eq_finrank]
  refine ⟨IsGalois.of_card_aut_eq_finrank K L hcard, ψ.symm frob, ?_, ?_, ?_, ?_⟩
  · exact (key _).2 (by simp)
  · rw [← MulEquiv.orderOf_eq ψ, MulEquiv.apply_symm_apply, hfrob,
      FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hfr]
  · rw [eq_top_iff]
    intro τ _
    obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ResidueField A)
      (ResidueField (integralClosure A L))).2 (ψ τ)
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(i.1 : ℤ), ψ.injective ?_⟩
    simp only [zpow_natCast, map_pow, MulEquiv.apply_symm_apply]
    exact hi
  · intro τ hτ
    exact ψ.injective (by rw [MulEquiv.apply_symm_apply]; exact (key τ).1 hτ)

include K in
/-- If the residue of `γ ∈ B` generates `l` over `k`, then `γ` generates `L` over `K`. -/
theorem gen_of_residue (hL : IsUnramifiedMilne A K L) (γ : integralClosure A L)
    (h : IntermediateField.adjoin (ResidueField A) {residue (integralClosure A L) γ} = ⊤) :
    IntermediateField.adjoin K {(γ : L)} = ⊤ := by
  classical
  have hfinB : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L _
  have : Module.Finite (ResidueField A) (ResidueField (integralClosure A L)) := inferInstance
  have hfr := finrank_res A K L hL
  have hint0 : IsIntegral A (γ : L) := γ.2
  have hgm := minpoly.monic hint0
  have hKdeg : (minpoly K (γ : L)).natDegree = (minpoly A (γ : L)).natDegree := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hint0, hgm.natDegree_map]
  have haev0 : aeval γ (minpoly A (γ : L)) = 0 := by
    have h1 := Polynomial.aeval_algHom_apply (integralClosure A L).val γ (minpoly A (γ : L))
    have h' : aeval (γ : L) (minpoly A (γ : L)) = 0 := minpoly.aeval A (γ : L)
    exact Subtype.ext (h1.symm.trans h')
  have hroot : aeval (residue _ γ) ((minpoly A (γ : L)).map (algebraMap A (ResidueField A))) = 0 := by
    rw [Polynomial.aeval_map_algebraMap (ResidueField A), Remark753.aeval_residue A L γ _, haev0, map_zero]
  have hdvd := minpoly.dvd (ResidueField A) (residue _ γ) hroot
  have hminpoly_deg : (minpoly (ResidueField A) (residue _ γ)).natDegree = Module.finrank K L := by
    rw [← hfr, ← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _), h,
      IntermediateField.finrank_top']
  have hle : Module.finrank K L ≤ (minpoly K (γ : L)).natDegree := by
    rw [hKdeg, ← hminpoly_deg]
    exact (Polynomial.natDegree_le_of_dvd hdvd (hgm.map _).ne_zero).trans_eq (hgm.natDegree_map _)
  apply IntermediateField.eq_of_le_of_finrank_eq
  · exact le_top
  · rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _), IntermediateField.finrank_top']
    exact le_antisymm (minpoly.natDegree_le _) hle

include K in
theorem unique_part (L' : Type v) [Field L'] [Algebra K L'] [Algebra A L'] [IsScalarTower A K L']
    [FiniteDimensional K L'] (hn : Module.finrank K L = Module.finrank K L')
    (hL : IsUnramifiedMilne A K L) (hL' : IsUnramifiedMilne A K L') : Nonempty (L ≃ₐ[K] L') := by
  classical
  have hfinB : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L _
  have hfinB' : Module.Finite A (integralClosure A L') := IsIntegralClosure.finite A K L' _
  have : Module.Finite (ResidueField A) (ResidueField (integralClosure A L)) := inferInstance
  have : Module.Finite (ResidueField A) (ResidueField (integralClosure A L')) := inferInstance
  have : Finite (ResidueField (integralClosure A L')) := Module.finite_of_finite (ResidueField A)
  have h1 := finrank_res A K L hL
  have h2 := finrank_res A K L' hL'
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ResidueField A)
    (K := ResidueField (integralClosure A L)) (L := ResidueField (integralClosure A L'))
    (by rw [h1, h2, hn])
  obtain ⟨Φ, _⟩ := Remark753.hom_equiv A K L L' hL hL'
  let σ : L →ₐ[K] L' := Φ.symm f
  have hinj : Function.Injective σ := σ.toRingHom.injective
  have hbij : Function.Bijective σ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hn (f := σ.toLinearMap)).1 hinj⟩
  exact ⟨AlgEquiv.ofBijective σ hbij⟩

include K in
theorem isSplittingField_part (_hn : 0 < Module.finrank K L) (hL : IsUnramifiedMilne A K L) :
    IsSplittingField K L (X ^ (Nat.card (ResidueField A) ^ Module.finrank K L) - X) := by
  classical
  have hsep : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hfinB : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L _
  have : Module.Finite (ResidueField A) (ResidueField (integralClosure A L)) := inferInstance
  have : Finite (ResidueField (integralClosure A L)) := Module.finite_of_finite (ResidueField A)
  have : Fintype (ResidueField (integralClosure A L)) := Fintype.ofFinite _
  have hfr := finrank_res A K L hL
  set m := Nat.card (ResidueField A) ^ Module.finrank K L with hmdef
  have hcard : Fintype.card (ResidueField (integralClosure A L)) = m := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ResidueField A), hfr]
  have hm1 : 1 < m := hcard ▸ Fintype.one_lt_card
  -- lifting roots by Hensel
  have hlift : ∀ r : ResidueField (integralClosure A L), ∃ a : integralClosure A L,
      a ^ m - a = 0 ∧ residue (integralClosure A L) a = r := by
    intro r
    obtain ⟨b, rfl⟩ := residue_surjective r
    have hmon : ((X ^ m - X : (integralClosure A L)[X])).Monic :=
      Polynomial.monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hm1)
    have h1 : ((X ^ m - X : (integralClosure A L)[X])).eval b ∈ maximalIdeal (integralClosure A L) := by
      rw [← residue_eq_zero_iff]
      simp only [eval_sub, eval_pow, eval_X, map_sub, map_pow]
      rw [← hcard, FiniteField.pow_card, sub_self]
    have h2 : IsUnit (((X ^ m - X : (integralClosure A L)[X])).derivative.eval b) := by
      rw [← notMem_maximalIdeal]
      intro hm
      have h0 := (residue_eq_zero_iff _).2 hm
      have hc : ((m : ℕ) : ResidueField (integralClosure A L)) = 0 := by
        rw [← hcard]; exact FiniteField.cast_card_eq_zero _
      simp only [derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_pow, eval_X,
        eval_natCast, eval_one, map_sub, map_mul, map_natCast, map_one] at h0
      rw [hc, zero_mul, zero_sub, neg_eq_zero] at h0
      exact one_ne_zero h0
    obtain ⟨a, ha, hab⟩ := Remark753.hensel_integralClosure A K L hL _ hmon b h1 h2
    refine ⟨a, ?_, ?_⟩
    · simpa using ha
    · exact (Ideal.Quotient.eq (I := maximalIdeal (integralClosure A L))).2 hab
  choose a ha hres using hlift
  have hPL : (X ^ m - X : K[X]).map (algebraMap K L) = (X ^ m - X : L[X]) := by simp
  have hdeg : (X ^ m - X : L[X]).natDegree = m := FiniteField.X_pow_card_sub_X_natDegree_eq L hm1
  have hne : (X ^ m - X : L[X]) ≠ 0 := by
    intro h; rw [h] at hdeg; simp at hdeg; omega
  have hroots : ∀ r, ((a r : integralClosure A L) : L) ∈ (X ^ m - X : L[X]).roots := by
    intro r
    rw [mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X]
    have := congrArg Subtype.val (ha r)
    simpa [sub_eq_zero] using this
  have hsplit : Splits ((X ^ m - X : K[X]).map (algebraMap K L)) := by
    rw [hPL, Polynomial.splits_iff_card_roots, hdeg]
    apply le_antisymm
    · exact (Polynomial.card_roots' (X ^ m - X : L[X])).trans hdeg.le
    · have hinj : Function.Injective (fun r => ((a r : integralClosure A L) : L)) := by
        intro r r' h
        rw [← hres r, ← hres r', Subtype.ext h]
      have := Multiset.toFinset_card_le (X ^ m - X : L[X]).roots
      have h2 : (Finset.univ.image (fun r => ((a r : integralClosure A L) : L))).card ≤
          (X ^ m - X : L[X]).roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 hx
        exact Multiset.mem_toFinset.2 (hroots r)
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard] at h2
      exact h2.trans this
  refine ⟨hsplit, ?_⟩
  obtain ⟨β, -, hβk, -⟩ := Remark753.exists_generator A K L hL
  have hgen := gen_of_residue A K L hL (a (residue _ β)) (by rw [hres]; exact hβk)
  have hadj : Algebra.adjoin K {((a (residue _ β) : integralClosure A L) : L)} = ⊤ := by
    have := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsIntegral.isIntegral (R := K) ((a (residue _ β) : integralClosure A L) : L)).isAlgebraic
    rw [← this, hgen]; exact IntermediateField.top_toSubalgebra
  rw [eq_top_iff, ← hadj]
  apply Algebra.adjoin_mono
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  rw [Polynomial.mem_rootSet]
  refine ⟨?_, ?_⟩
  · intro h; have := congrArg natDegree h
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hm1] at this; simp at this; omega
  · have := (mem_roots hne).1 (hroots (residue _ β))
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hPL]
    exact this

end Example754

open Example754 in
/-- **Example 7.54.** Discharges the named statement `Example7_54`. -/
@[kb "milne2020ant" "v3.08, Example 7.54, p. 129"]
theorem example_7_54 (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    [CharZero K] [Finite (ResidueField A)] : Example7_54 A K := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    have : NeZero n := ⟨hn.ne'⟩
    have : Fact (ringChar (ResidueField A)).Prime := ⟨CharP.char_is_prime (ResidueField A) (ringChar (ResidueField A))⟩
    let E := ULift.{u} (FiniteField.Extension (ResidueField A) (ringChar (ResidueField A)) n)
    have : FiniteDimensional (ResidueField A) E :=
      Module.Finite.equiv (ULift.moduleEquiv (R := ResidueField A)).symm
    have : Algebra.IsSeparable (ResidueField A) E := Algebra.IsAlgebraic.isSeparable_of_perfectField
    have hE : Module.finrank (ResidueField A) E = n :=
      (LinearEquiv.finrank_eq (ULift.moduleEquiv (R := ResidueField A))).trans
        (FiniteField.finrank_extension _ _ n)
    obtain ⟨L, F, a1, a2, a3, hfd, hU, ⟨e⟩⟩ := Remark753.exists_lift A K E
    refine ⟨L, F, a1, a2, a3, ?_, hU⟩
    have := Thm758aFixed.resDeg_eq_finrank A L
    have h2 : resDegMilne A L = Module.finrank K L := hU
    rw [← h2, this, LinearEquiv.finrank_eq e.toLinearEquiv, hE]
  · intro L _ _ _ _ L' _ _ _ _ hn hpos hL hL'
    have : FiniteDimensional K L := Module.finite_of_finrank_pos hpos
    have : FiniteDimensional K L' := Module.finite_of_finrank_pos (hn ▸ hpos)
    exact unique_part A K L L' hn hL hL'
  · intro L _ _ _ _ hpos hL
    have : FiniteDimensional K L := Module.finite_of_finrank_pos hpos
    exact isSplittingField_part A K L hpos hL
  · intro L _ _ _ _ hpos hL
    have : FiniteDimensional K L := Module.finite_of_finrank_pos hpos
    exact frobenius_part A K L hL

end NumberFieldKB.MilneANT
