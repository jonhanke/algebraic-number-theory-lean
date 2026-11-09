import NumberFieldKB.MilneCFT.Ch8.ReciprocityLaw

/-!
# Milne, *Class Field Theory*, VIII, 5.7 (auxiliary): a common abelian extension of two Kummer extensions

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §5 (p. 246).
For $\zeta_n \in K$, two Kummer extensions $K(\alpha)$, $K(\beta)$ ($\alpha^n = a$, $\beta^n = b$) both embed in the
splitting field of $(X^n - a)(X^n - b)$, an abelian extension of $K$ (`exists_common`).
-/

open NumberField IsDedekindDomain NumberFieldKB.MilneCFT Polynomial
open scoped IsMulCommutative

set_option linter.unusedSectionVars false

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

namespace Item57

variable {K : Type} [Field K] [NumberField K]

/-! ## A common abelian extension -/

section Common

variable {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
include hn hζ

omit hn hζ in
/-- If `L = K⟮α⟯` and the minimal polynomial of `α` divides a nonzero `q` splitting in `M`, then `L` embeds in `M`. -/
theorem embed_of_dvd {La : Type} [Field La] [NumberField La] [Algebra K La] (α : La)
    (hαg : IntermediateField.adjoin K {α} = ⊤) (M : Type) [Field M] [Algebra K M] (q : Polynomial K)
    (hq0 : q ≠ 0) (hq : (q.map (algebraMap K M)).Splits) (hdvd : minpoly K α ∣ q) :
    Nonempty (La →ₐ[K] M) := by
  have hint : IsIntegral K α := IsIntegral.of_finite K α
  have hm0 : (minpoly K α).map (algebraMap K M) ∣ q.map (algebraMap K M) := Polynomial.map_dvd _ hdvd
  have hsp : ((minpoly K α).map (algebraMap K M)).Splits :=
    Polynomial.Splits.of_dvd hq (Polynomial.map_ne_zero hq0) hm0
  have hdeg : ((minpoly K α).map (algebraMap K M)).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact (minpoly.degree_pos hint).ne'
  obtain ⟨y, hy⟩ := hsp.exists_eval_eq_zero hdeg
  let pb := IntermediateField.adjoin.powerBasis hint
  have hy' : Polynomial.aeval y (minpoly K pb.gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, Polynomial.aeval_def,
      ← Polynomial.eval_map]
    exact hy
  let e : La ≃ₐ[K] IntermediateField.adjoin K {α} :=
    IntermediateField.topEquiv.symm.trans (IntermediateField.equivOfEq hαg.symm)
  exact ⟨(pb.lift y hy').comp e.toAlgHom⟩

/-- Two Kummer extensions $K(\alpha)$, $K(\beta)$ ($\alpha^n = a$, $\beta^n = b$) embed in one abelian extension. -/
theorem exists_common (La : Type) [Field La] [NumberField La] [Algebra K La]
    (Lb : Type) [Field Lb] [NumberField Lb] [Algebra K Lb]
    (a b : Kˣ) (α : La) (β : Lb) (hα : α ^ n = algebraMap K La a) (hβ : β ^ n = algebraMap K Lb b)
    (hαg : IntermediateField.adjoin K {α} = ⊤) (hβg : IntermediateField.adjoin K {β} = ⊤) :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra K M) (_ : IsAbelianGalois K M),
      Nonempty (La →ₐ[K] M) ∧ Nonempty (Lb →ₐ[K] M) := by
  classical
  have hcast : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  set pa : Polynomial K := Polynomial.X ^ n - Polynomial.C (a : K) with hpa
  set pb : Polynomial K := Polynomial.X ^ n - Polynomial.C (b : K) with hpb
  set p : Polynomial K := pa * pb with hp
  have hpa0 : pa ≠ 0 := (Polynomial.X_pow_sub_C_ne_zero hn _)
  have hpb0 : pb ≠ 0 := (Polynomial.X_pow_sub_C_ne_zero hn _)
  have hp0 : p ≠ 0 := mul_ne_zero hpa0 hpb0
  have : NumberField p.SplittingField := NumberField.of_module_finite K p.SplittingField
  have hG : IsGalois K p.SplittingField := inferInstance
  have hsplit : (p.map (algebraMap K p.SplittingField)).Splits := Polynomial.SplittingField.splits p
  -- roots
  have hroot : ∀ r ∈ p.rootSet p.SplittingField,
      r ^ n = algebraMap K p.SplittingField (a : K) ∨ r ^ n = algebraMap K p.SplittingField (b : K) := by
    intro r hr
    rw [Polynomial.mem_rootSet] at hr
    have h := hr.2
    simp only [hp, hpa, hpb, map_mul, Polynomial.aeval_def,Polynomial.eval₂_sub,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  have hcomm : IsMulCommutative Gal(p.SplittingField/K) := by
    refine ⟨⟨fun σ τ => ?_⟩⟩
    have hgen : Algebra.adjoin K (p.rootSet p.SplittingField : Set p.SplittingField) = ⊤ :=
      Polynomial.IsSplittingField.adjoin_rootSet _ _
    have key : ∀ r ∈ p.rootSet p.SplittingField, σ (τ r) = τ (σ r) := by
      intro r hr
      have hz : ∀ (ρ : Gal(p.SplittingField/K)) (c : Kˣ),
          r ^ n = algebraMap K p.SplittingField (c : K) → ∃ j < n,
            ρ r = algebraMap K p.SplittingField (ζ ^ j) * r := fun ρ c h =>
        kummer_zeta hn hζ (c : K) c.ne_zero p.SplittingField r h ρ
      have hz' : ∀ ρ : Gal(p.SplittingField/K), ∃ j < n,
          ρ r = algebraMap K p.SplittingField (ζ ^ j) * r := by
        intro ρ
        rcases hroot r hr with h | h
        · exact hz ρ a h
        · exact hz ρ b h
      obtain ⟨j, -, hj⟩ := hz' σ
      obtain ⟨k, -, hk⟩ := hz' τ
      rw [hk, hj, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hj, hk]
      ring
    have : (σ * τ : Gal(p.SplittingField/K)).toAlgHom = (τ * σ).toAlgHom := by
      refine AlgHom.ext_of_adjoin_eq_top hgen ?_
      intro r hr
      exact key r hr
    exact AlgEquiv.coe_toAlgHom_injective this
  refine ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact { }
  · refine embed_of_dvd α hαg p.SplittingField p hp0 hsplit ?_
    refine (minpoly.dvd K α ?_).trans (dvd_mul_right pa pb)
    simp [hpa, hα]
  · refine embed_of_dvd β hβg p.SplittingField p hp0 hsplit ?_
    refine (minpoly.dvd K β ?_).trans (dvd_mul_left pb pa)
    simp [hpb, hβ]

end Common

end Item57

end NumberFieldKB.MilneCFT.Ch8
