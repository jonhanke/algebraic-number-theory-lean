import NumberFieldKB.MilneANT.Ch7Extensions
import NumberFieldKB.MilneANT.Ch7ResidueSub
import NumberFieldKB.MilneANT.Ch7HenselExt

/-!
# Milne, *Algebraic Number Theory*, Proposition 7.50, p. 127

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

Discharges the named statement `Prop7_50` (`prop_7_50`). The key construction is `Prop750.construct`: a finite
`k' ⊂ l` with primitive element `ā` is the residue field of `K⟮α⟯`, where `α ∈ B` is the Hensel lift of `ā` to a root
of a monic lift `g ∈ A[X]` of `minpoly k ā`; it is minimal among the `K''` whose residue field contains `ā`
(`Prop750.mem_of_residue`).
-/

open IsLocalRing Polynomial

universe u v w

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneANT

namespace Prop750

open ResidueSub

/-- Over a perfect field, an algebraic extension is separable. -/
theorem sep_of_perfect (F : Type*) [Field F] [PerfectField F] (E : Type*) [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] : Algebra.IsSeparable F E := Algebra.IsAlgebraic.isSeparable_of_perfectField

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

section Lift

variable [PerfectField K] [PerfectField (ResidueField A)] [Algebra.IsAlgebraic K L]

include K

/-- A Hensel lift of an integral element `a` of the residue field `l` to a root of a monic lift of its minimal
polynomial. -/
theorem exists_root (a : ResidueField (integralClosure A L)) (ha : IsIntegral (ResidueField A) a) :
    ∃ (g : A[X]) (α : integralClosure A L), g.Monic ∧
      g.natDegree = (minpoly (ResidueField A) a).natDegree ∧
      aeval α g = 0 ∧ residue (integralClosure A L) α = a ∧ IsUnit (aeval α (derivative g)) := by
  classical
  have hsepL : Algebra.IsSeparable K L := sep_of_perfect K L
  have hg₀m := minpoly.monic ha
  have hlift : minpoly (ResidueField A) a ∈ Polynomial.lifts (algebraMap A (ResidueField A)) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => residue_surjective _
  obtain ⟨g, hgmap, hgdeg, hgmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hg₀m
  have hsep : (minpoly (ResidueField A) a).Separable :=
    PerfectField.separable_of_irreducible (minpoly.irreducible ha)
  obtain ⟨b, hb⟩ := residue_surjective a
  have hroot : aeval a (minpoly (ResidueField A) a) = 0 := minpoly.aeval _ _
  have hga : aeval a g = 0 := by
    rw [← Polynomial.aeval_map_algebraMap (ResidueField A), hgmap]; exact hroot
  have hgder : aeval a (derivative g) ≠ 0 := by
    have := hsep.aeval_derivative_ne_zero hroot
    rwa [← hgmap, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap] at this
  have h1 : aeval b g ∈ maximalIdeal (integralClosure A L) := by
    rw [← residue_eq_zero_iff, ← Remark753.aeval_residue A L b, hb]; exact hga
  have h2 : IsUnit (aeval b (derivative g)) := by
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, ← Remark753.aeval_residue A L b, hb]; exact hgder
  obtain ⟨α, hα, hαb⟩ := HenselExt.hensel_of_algebraic A K L g hgmon b h1 h2
  have hres : residue (integralClosure A L) α = a := by
    rw [← hb]; exact ((Ideal.Quotient.eq (I := maximalIdeal (integralClosure A L))).2 hαb)
  refine ⟨g, α, hgmon, by rw [hgdeg], hα, hres, ?_⟩
  rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, ← Remark753.aeval_residue A L α, hres]
  exact hgder

theorem mem_residueField'_iff (K' : IntermediateField K L) (x : ResidueField (integralClosure A L)) :
    x ∈ residueField' A K L K' ↔ x ∈ residueRange A K L K' := by
  rw [← residueField'_toSubring A K L K']; rfl

theorem residue_mem_residueField' (K' : IntermediateField K L) (b : integralClosure A L) (hb : (b : L) ∈ K') :
    residue (integralClosure A L) b ∈ residueField' A K L K' := by
  rw [mem_residueField'_iff]; exact Subring.mem_map.2 ⟨b, hb, rfl⟩

theorem residueField'_eq_of_range (K' : IntermediateField K L)
    (k' : IntermediateField (ResidueField A) (ResidueField (integralClosure A L)))
    (h : residueRange A K L K' = k'.toSubalgebra.toSubring) : residueField' A K L K' = k' := by
  apply IntermediateField.toSubalgebra_injective
  apply Subalgebra.toSubring_injective
  rw [residueField'_toSubring, h]

theorem resDeg_le_finrank (E : Type w) [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    resDegMilne A E ≤ Module.finrank K E := by
  have hef := cor_7_42 A K E
  have hn : 0 < Module.finrank K E := Module.finrank_pos
  rw [← hef]
  refine Nat.le_mul_of_pos_left _ ?_
  rcases Nat.eq_zero_or_pos (ramIdxMilne A E) with h | h
  · rw [h, zero_mul] at hef; omega
  · exact h

theorem exists_gen (k' : IntermediateField (ResidueField A) (ResidueField (integralClosure A L)))
    [FiniteDimensional (ResidueField A) k'] :
    ∃ a ∈ k', IntermediateField.adjoin (ResidueField A) {a} = k' := by
  have : Algebra.IsSeparable (ResidueField A) k' := sep_of_perfect _ k'
  obtain ⟨γ, hγ⟩ := Field.exists_primitive_element (ResidueField A) k'
  refine ⟨(γ : _), γ.2, ?_⟩
  have h := IntermediateField.lift_adjoin_simple (ResidueField A) k' γ
  rw [hγ, IntermediateField.lift_top] at h
  exact h.symm

/-- **Key uniqueness**: if the residue field of a finite `K''` contains the residue `ā` of a Hensel root `α` of `g`,
then `α ∈ K''`. -/
theorem mem_of_residue (g : A[X]) (α : integralClosure A L) (hgm : g.Monic) (hα : aeval α g = 0)
    (hu : IsUnit (aeval α (derivative g))) (K'' : IntermediateField K L) [FiniteDimensional K K'']
    (hmem : residue (integralClosure A L) α ∈ residueField' A K L K'') : (α : L) ∈ K'' := by
  have hsep'' : Algebra.IsSeparable K K'' := sep_of_perfect K K''
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨c, rfl⟩ := residue_surjective y
  have hresInj := resIncl_injective A K L K''
  have key : ∀ p : A[X], resIncl A K L K'' (aeval (residue _ c) p) = aeval (residue _ α) p := by
    intro p
    have := Polynomial.aeval_algHom_apply ((resIncl A K L K'').restrictScalars A) (residue _ c) p
    have hy' : (resIncl A K L K'') (residue _ c) = residue _ α := hy
    simp only [AlgHom.coe_restrictScalars'] at this
    rw [hy'] at this
    exact this.symm
  have h1 : aeval c g ∈ maximalIdeal (integralClosure A K'') := by
    rw [← residue_eq_zero_iff, ← Remark753.aeval_residue A K'' c]
    apply hresInj
    rw [key, Remark753.aeval_residue A L, hα, map_zero, map_zero]
  have h2 : IsUnit (aeval c (derivative g)) := by
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, ← Remark753.aeval_residue A K'' c]
    intro h0
    have h3 : aeval (residue (integralClosure A L) α) (derivative g) = 0 := by
      rw [← key, h0, map_zero]
    exact (notMem_maximalIdeal.2 hu) ((residue_eq_zero_iff _).1
      (by rw [← Remark753.aeval_residue A L]; exact h3))
  obtain ⟨α'', hα'', hαc⟩ := HenselExt.hensel_of_algebraic A K K'' g hgm c h1 h2
  have hroot : aeval (incl A K L K'' α'') g = 0 := by
    have := Polynomial.aeval_algHom_apply (incl A K L K'') α'' g
    rw [hα'', map_zero] at this
    exact this
  have hres : residue (integralClosure A L) (incl A K L K'' α'') = residue _ α := by
    have h4 : residue (integralClosure A K'') α'' = residue _ c :=
      (Ideal.Quotient.eq (I := maximalIdeal (integralClosure A K''))).2 hαc
    rw [← resIncl_residue A K L K'' α'', h4]
    exact hy
  have hdiff : α - incl A K L K'' α'' ∈ maximalIdeal (integralClosure A L) :=
    (Ideal.Quotient.eq (I := maximalIdeal (integralClosure A L))).1 hres.symm
  have heq : α = incl A K L K'' α'' := by
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := g.map (algebraMap A (integralClosure A L)))
      ?_ ?_ ?_ ?_
    · rw [Polynomial.eval_map_algebraMap]; exact hα
    · rw [Polynomial.eval_map_algebraMap]; exact hroot
    · exact (mem_nonunits_iff).1 ((IsLocalRing.mem_maximalIdeal _).1 hdiff)
    · rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]; exact hu
  rw [heq]
  exact (α'' : K'').2

/-- **Key construction** (Milne, proof of Prop. 7.50): every finite `k' ⊂ l` is the residue field of a finite
unramified `K0 ⊂ L`, which is moreover the smallest `K''` whose residue field contains `k'`. -/
theorem construct (k' : IntermediateField (ResidueField A) (ResidueField (integralClosure A L)))
    [FiniteDimensional (ResidueField A) k'] :
    ∃ K0 : IntermediateField K L, FiniteDimensional K K0 ∧ IsUnramifiedMilne A K K0 ∧
      residueField' A K L K0 = k' ∧
      ∀ K'' : IntermediateField K L, FiniteDimensional K K'' →
        k' ≤ residueField' A K L K'' → K0 ≤ K'' := by
  classical
  obtain ⟨a, hak, hgen⟩ := exists_gen A K L k'
  have haint : IsIntegral (ResidueField A) a :=
    (Algebra.IsIntegral.isIntegral (R := ResidueField A) (⟨a, hak⟩ : k')).map k'.val
  obtain ⟨g, α, hgm, hgdeg, hα, hres, hu⟩ := exists_root A K L a haint
  have hαint : IsIntegral K (α : L) := Algebra.IsIntegral.isIntegral _
  set K0 := IntermediateField.adjoin K {(α : L)} with hK0
  have : FiniteDimensional K K0 := IntermediateField.adjoin.finiteDimensional hαint
  have : Algebra.IsSeparable K K0 := sep_of_perfect K K0
  have hn : Module.finrank K K0 ≤ g.natDegree := by
    rw [hK0, IntermediateField.adjoin.finrank hαint]
    have hroot : aeval (α : L) (g.map (algebraMap A K)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap, Remark753.aeval_val A L α, hα]; rfl
    have hd := minpoly.dvd K (α : L) hroot
    exact (Polynomial.natDegree_le_of_dvd hd (hgm.map _).ne_zero).trans_eq (hgm.natDegree_map _)
  have haK0 : a ∈ residueField' A K L K0 := by
    rw [← hres]
    exact residue_mem_residueField' A K L K0 α (IntermediateField.subset_adjoin K _ rfl)
  have hle : k' ≤ residueField' A K L K0 := by
    rw [← hgen]; exact IntermediateField.adjoin_simple_le_iff.2 haK0
  have hkdeg : Module.finrank (ResidueField A) k' = g.natDegree := by
    rw [← hgen, IntermediateField.adjoin.finrank haint, hgdeg]
  have hf := finrank_residueField' A K L K0
  have hfle := resDeg_le_finrank A K K0
  have hmono : Module.finrank (ResidueField A) k' ≤ Module.finrank (ResidueField A) (residueField' A K L K0) :=
    IntermediateField.finrank_le_of_le_right hle
  have hU : IsUnramifiedMilne A K K0 := by
    rw [isUnramified_iff_finrank A K L K0]; omega
  have heq : residueField' A K L K0 = k' :=
    (IntermediateField.eq_of_le_of_finrank_eq hle (by omega)).symm
  refine ⟨K0, inferInstance, hU, heq, fun K'' hK'' hk => ?_⟩
  have hmem : residue (integralClosure A L) α ∈ residueField' A K L K'' := by
    rw [hres]; exact hk hak
  have := hK''
  exact IntermediateField.adjoin_simple_le_iff.2 (mem_of_residue A K L g α hgm hα hu K'' hmem)

theorem eq_of_le_of_residue (K0 K' : IntermediateField K L) [FiniteDimensional K K0] [FiniteDimensional K K']
    (hle : K0 ≤ K') (h0 : IsUnramifiedMilne A K K0) (h' : IsUnramifiedMilne A K K')
    (hr : residueField' A K L K0 = residueField' A K L K') : K0 = K' := by
  have : Algebra.IsSeparable K K0 := sep_of_perfect K K0
  have : Algebra.IsSeparable K K' := sep_of_perfect K K'
  have e0 := (isUnramified_iff_finrank A K L K0).1 h0
  have e1 := (isUnramified_iff_finrank A K L K').1 h'
  rw [hr] at e0
  exact IntermediateField.eq_of_le_of_finrank_eq hle (by omega)

/-! ## Galois part -/

theorem aut_mulEquiv (E : Type w) [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [FiniteDimensional K E] (hL : IsUnramifiedMilne A K E) :
    ∃ ψ : (E ≃ₐ[K] E) ≃* (ResidueField (integralClosure A E) ≃ₐ[ResidueField A]
        ResidueField (integralClosure A E)),
      ∀ (τ : E ≃ₐ[K] E) (b b' : integralClosure A E), (b' : E) = τ b →
        ψ τ (residue _ b) = residue _ b' := by
  classical
  have : Algebra.IsSeparable K E := sep_of_perfect K E
  have : Module.Finite A (integralClosure A E) := IsIntegralClosure.finite A K E _
  obtain ⟨Φ, hΦ⟩ := Remark753.hom_equiv A K E E hL hL
  let f : (E ≃ₐ[K] E) →* (ResidueField (integralClosure A E) ≃ₐ[ResidueField A]
        ResidueField (integralClosure A E)) :=
    { toFun := fun τ => AlgEquiv.ofBijective (Φ τ.toAlgHom) (AlgHom.bijective _)
      map_one' := by
        refine AlgEquiv.ext fun x => ?_
        obtain ⟨b, rfl⟩ := residue_surjective x
        exact hΦ (1 : E ≃ₐ[K] E).toAlgHom b b rfl
      map_mul' := by
        intro σ τ
        refine AlgEquiv.ext fun x => ?_
        obtain ⟨b, rfl⟩ := residue_surjective x
        have h1 := hΦ τ.toAlgHom b (Remark753.mapB A K E E τ.toAlgHom b) rfl
        have h2 := hΦ σ.toAlgHom (Remark753.mapB A K E E τ.toAlgHom b)
          (Remark753.mapB A K E E (σ * τ).toAlgHom b) rfl
        have h3 := hΦ (σ * τ).toAlgHom b (Remark753.mapB A K E E (σ * τ).toAlgHom b) rfl
        show Φ (σ * τ).toAlgHom _ = Φ σ.toAlgHom (Φ τ.toAlgHom _)
        rw [h1, h2, h3] }
  have hf : Function.Bijective f := by
    constructor
    · intro τ τ' h
      have : Φ τ.toAlgHom = Φ τ'.toAlgHom := AlgHom.ext fun x => congrArg (fun e => e x) h
      exact AlgEquiv.coe_toAlgHom_injective (Φ.injective this)
    · intro ρ
      let t : E →ₐ[K] E := Φ.symm ρ.toAlgHom
      refine ⟨AlgEquiv.ofBijective t (AlgHom.bijective _), ?_⟩
      refine AlgEquiv.ext fun x => ?_
      show Φ t x = ρ x
      simp [t]
  refine ⟨MulEquiv.ofBijective f hf, fun τ b b' hb' => ?_⟩
  exact hΦ τ.toAlgHom b b' hb'

/-- Reduction identifies `Aut_K(K')` with `Aut_k(k')`, compatibly with residues. -/
theorem galEquiv_core (K' : IntermediateField K L) [FiniteDimensional K K'] (hU : IsUnramifiedMilne A K K') :
    ∃ φ : (K' ≃ₐ[K] K') ≃* (residueField' A K L K' ≃ₐ[ResidueField A] residueField' A K L K'),
      ∀ (σ : K' ≃ₐ[K] K') (b : integralClosure A L) (hb : (b : L) ∈ K') (b' : integralClosure A L),
        (b' : L) = (σ ⟨b, hb⟩ : L) → ∀ hmem : residue _ b ∈ residueField' A K L K',
          ((φ σ ⟨residue _ b, hmem⟩ : residueField' A K L K') : ResidueField (integralClosure A L)) =
            residue _ b' := by
  obtain ⟨ψ, hψ⟩ := aut_mulEquiv A K K' hU
  refine ⟨ψ.trans (AlgEquiv.autCongr (residueEquiv A K L K')), fun σ b hb b' hb' hmem => ?_⟩
  have hbint : IsIntegral A (⟨(b : L), hb⟩ : K') := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom A K' L) (algebraMap K' L).injective]
    exact b.2
  let bb : integralClosure A K' := ⟨⟨(b : L), hb⟩, hbint⟩
  let bb' : integralClosure A K' := Remark753.mapB A K K' K' σ.toAlgHom bb
  have h1 : residueEquiv A K L K' (residue _ bb) = ⟨residue _ b, hmem⟩ :=
    Subtype.ext (by
      show resIncl A K L K' (residue _ bb) = residue _ b
      rw [resIncl_residue]; rfl)
  have h2 := hψ σ bb bb' rfl
  have h3 : incl A K L K' bb' = b' := Subtype.ext hb'.symm
  have h5 : ∀ x, (ψ.trans (AlgEquiv.autCongr (residueEquiv A K L K'))) σ x =
      residueEquiv A K L K' (ψ σ ((residueEquiv A K L K').symm x)) := fun x => rfl
  rw [h5, ← h1, AlgEquiv.symm_apply_apply, h2]
  show resIncl A K L K' (residue _ bb') = _
  rw [resIncl_residue, h3]

theorem isGalois_core (K' : IntermediateField K L) [FiniteDimensional K K'] (hU : IsUnramifiedMilne A K K') :
    IsGalois K K' ↔ IsGalois (ResidueField A) (residueField' A K L K') := by
  have : Algebra.IsSeparable K K' := sep_of_perfect K K'
  obtain ⟨ψ, -⟩ := aut_mulEquiv A K K' hU
  let φ := ψ.trans (AlgEquiv.autCongr (residueEquiv A K L K'))
  have hcard : Nat.card (K' ≃ₐ[K] K') = Nat.card (residueField' A K L K' ≃ₐ[ResidueField A]
      residueField' A K L K') := Nat.card_congr φ.toEquiv
  have hdeg := (isUnramified_iff_finrank A K L K').1 hU
  constructor
  · intro h
    exact IsGalois.of_card_aut_eq_finrank (ResidueField A) _ (by
      rw [← hcard, hdeg, IsGalois.card_aut_eq_finrank])
  · intro h
    exact IsGalois.of_card_aut_eq_finrank K _ (by
      rw [hcard, IsGalois.card_aut_eq_finrank, hdeg])

/-! ## The named statement -/

theorem prop_7_50_aux : Prop7_50 A K L where
  exists_unique := fun k' hk' => by
    have := hk'
    obtain ⟨K0, hfin, hU, hr, hmin⟩ := construct A K L k'
    refine ⟨K0, ⟨hfin, hU, by rw [← residueField'_toSubring, hr]⟩, ?_⟩
    rintro K'' ⟨hfin'', hU'', hr''⟩
    have hr2 := residueField'_eq_of_range A K L K'' k' hr''
    have hle : K0 ≤ K'' := hmin K'' hfin'' hr2.ge
    exact (eq_of_le_of_residue A K L K0 K'' hle hU hU'' (hr.trans hr2.symm)).symm
  residueRange_finite := fun K' hf hU => by
    have : Algebra.IsSeparable K K' := sep_of_perfect K K'
    exact ⟨residueField' A K L K', inferInstance, (residueField'_toSubring A K L K').symm⟩
  le_iff := fun K' K'' hf hU hf'' hU'' => by
    refine ⟨residueRange_mono A K L, fun hle => ?_⟩
    have : Algebra.IsSeparable K K' := sep_of_perfect K K'
    obtain ⟨K0, hfin0, hU0, hr0, hmin⟩ := construct A K L (residueField' A K L K')
    have h1 : K0 ≤ K'' := hmin K'' hf'' (fun x hx =>
      (mem_residueField'_iff A K L K'' x).2 (hle ((mem_residueField'_iff A K L K' x).1 hx)))
    have h2 : K0 ≤ K' := hmin K' hf le_rfl
    have : K0 = K' := eq_of_le_of_residue A K L K0 K' h2 hU0 hU hr0
    rw [← this]; exact h1
  isGalois_iff := fun K' k' hf hU hr => by
    have h := residueField'_eq_of_range A K L K' k' hr
    subst h
    exact isGalois_core A K L K' hU
  galEquiv := fun K' k' hf hU hr _ => by
    have h := residueField'_eq_of_range A K L K' k' hr
    subst h
    exact galEquiv_core A K L K' hU

end Lift

end Prop750

/-- **Proposition 7.50** (Milne, p. 127). Discharges the named statement `Prop7_50`. -/
@[kb "milne2020ant" "v3.08, Prop. 7.50, p. 127"]
theorem prop_7_50 (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [PerfectField K] [PerfectField (ResidueField A)] [Algebra.IsAlgebraic K L] : Prop7_50 A K L :=
  Prop750.prop_7_50_aux A K L

end NumberFieldKB.MilneANT
