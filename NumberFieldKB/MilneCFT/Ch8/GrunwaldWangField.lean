import NumberFieldKB.MilneCFT.Ch8.Theorem23Uncond
import NumberFieldKB.MilneCFT.Ch7.LocalNormTauCeti
import NumberFieldKB.MilneCFT.GlobalUnconditional
import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangChar

/-!
# Grunwald–Wang: the cyclic extension cut out by a character of `C_K`

**Proved here:** `GW.exists_field_of_char`: a continuous character `ψ` of `C_K` of finite order `n` cuts out a cyclic
extension `L/K` of degree `n` (existence theorem `Ch7.theorem9_5` for `U = ker ψ`; `Gal(L/K) ≅ C_K/U` by Tau Ceti's
global Artin map, `TauCeti.ClassFieldTheory.globalArtinEquiv`; `C_K/U ≅ im ψ` is a finite subgroup of `ℂ^×`, hence
cyclic) whose local degree `e f` at a finite place `v` is the order of `ψ|_{K_v^×}` (local–global compatibility
`T23.mem_normClasses_finite_iff` and `Ch7.localNormInput`'s `index_eq`) and which ramifies at an infinite place `w`
exactly when `ψ|_{K_w^×}` has order `2` (`T23.mem_normClasses_infinite_iff`, `index_inf`).
-/

open IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.GW

variable {K : Type} [Field K] [NumberField K]

theorem finite_range {G : Type*} [Group G] (χ : G →* ℂˣ) (hf : IsOfFinOrder χ) : Finite χ.range := by
  obtain ⟨k, hk, hχk⟩ := hf.exists_pow_eq_one
  have hrange : (χ.range : Set ℂˣ) ⊆ (rootsOfUnity k ℂ : Set ℂˣ) := by
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, mem_rootsOfUnity]
    have := congrArg (fun f : G →* ℂˣ => f g) hχk
    simpa using this
  haveI : NeZero k := ⟨hk.ne'⟩
  have : Finite (rootsOfUnity k ℂ) := inferInstance
  exact Finite.of_injective (fun x : χ.range => (⟨x.1, hrange x.2⟩ : rootsOfUnity k ℂ))
    (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))

/-- The index of the kernel of a character of finite order is its order. -/
theorem index_ker_eq_orderOf {G : Type*} [Group G] (χ : G →* ℂˣ) (hf : IsOfFinOrder χ) :
    χ.ker.index = orderOf χ := by
  obtain ⟨k, hk, hχk⟩ := hf.exists_pow_eq_one
  have hrange : (χ.range : Set ℂˣ) ⊆ (rootsOfUnity k ℂ : Set ℂˣ) := by
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, mem_rootsOfUnity]
    have := congrArg (fun f : G →* ℂˣ => f g) hχk
    simpa using this
  haveI : NeZero k := ⟨hk.ne'⟩
  haveI hfin : Finite χ.range := by
    have : Finite (rootsOfUnity k ℂ) := inferInstance
    exact Finite.of_injective (fun x : χ.range => (⟨x.1, hrange x.2⟩ : rootsOfUnity k ℂ))
      (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
  haveI : IsCyclic χ.range := inferInstance
  have h1 : χ.ker.index = Nat.card χ.range := by
    rw [← Subgroup.index_ker]
  rw [h1, ← IsCyclic.exponent_eq_card]
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨_, g, rfl⟩
    apply Subtype.ext
    have := DFunLike.congr_fun (pow_orderOf_eq_one χ) g
    rw [MonoidHom.pow_apply] at this
    simpa using this
  · rw [orderOf_dvd_iff_pow_eq_one]
    refine MonoidHom.ext fun g => ?_
    have := Monoid.pow_exponent_eq_one (⟨χ g, g, rfl⟩ : χ.range)
    rw [MonoidHom.pow_apply]
    exact congrArg Subtype.val this

/-- **The cyclic extension of a character.** -/
theorem exists_field_of_char (ψ : IdeleClassGroup (𝓞 K) K →* ℂˣ) (hc : Continuous ψ) {n : ℕ} (hn : 0 < n)
    (hψ : orderOf ψ = n) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsGalois K L),
      IsCyclic Gal(L/K) ∧ Module.finrank K L = n ∧
      (∀ (v : HeightOneSpectrum (𝓞 K)) (Q : v.asIdeal.primesOver (𝓞 L)),
        Q.1.ramificationIdx (𝓞 K) * Q.1.inertiaDeg (𝓞 K) =
          orderOf (ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v)))) ∧
      ∀ w : InfinitePlace K, (InfinitePlace.RamifiesIn L w ↔
        orderOf (ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofCompletion (𝓞 K) K w))) = 2) := by
  classical
  have hfo : IsOfFinOrder ψ := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hψ ▸ pow_orderOf_eq_one ψ⟩
  obtain ⟨hUo, hUf⟩ := isOpen_ker_and_finiteIndex ψ hc hfo
  obtain ⟨L, _, _, _, _, hab, hUL⟩ := (Ch7.theorem9_5 K).isNormGroup ψ.ker hUo hUf
  haveI : IsMulCommutative Gal(L/K) := ⟨⟨hab⟩⟩
  have hcomp : ∀ {H : Type} [Group H] (f : H →* IdeleClassGroup (𝓞 K) K),
      IsOfFinOrder (ψ.comp f) := by
    intro H _ f
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, ?_⟩
    refine MonoidHom.ext fun x => ?_
    have := DFunLike.congr_fun (pow_orderOf_eq_one ψ) (f x)
    rw [hψ, MonoidHom.pow_apply] at this
    rw [MonoidHom.pow_apply]
    exact this
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ι⟩ := T23.exists_embedding (K := K) L
    have hrange : ψ.ker = (TauCeti.GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range :=
      hUL.trans (Ch7.normClasses_eq_tauCeti K L)
    haveI : IsCyclic ψ.range := by
      haveI : Finite ψ.range := finite_range ψ hfo
      infer_instance
    have hq : IsCyclic (IdeleClassGroup (𝓞 K) K ⧸ (TauCeti.GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range) := by
      have e := (QuotientGroup.quotientKerEquivRange ψ).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hrange)
      exact isCyclic_of_surjective e.toMonoidHom e.surjective
    haveI := isAddCyclic_additive_iff.2 hq
    have h2 : IsAddCyclic (Additive (Abelianization Gal(L/K))) :=
      isAddCyclic_of_surjective
        (TauCeti.ClassFieldTheory.globalArtinEquiv K L ι).toAddMonoidHom
        (TauCeti.ClassFieldTheory.globalArtinEquiv K L ι).surjective
    haveI := isAddCyclic_additive_iff.1 h2
    letI : CommGroup Gal(L/K) := { (inferInstance : Group Gal(L/K)) with mul_comm := hab }
    exact isCyclic_of_surjective (Abelianization.equivOfComm (H := Gal(L/K))).symm.toMonoidHom
      (Abelianization.equivOfComm (H := Gal(L/K))).symm.surjective
  · rw [← Ch7.index_normClasses' L hab, ← hUL, ← hψ]
    exact index_ker_eq_orderOf ψ hfo
  · intro v Q
    have hker : Ch7.localNormGroup L v =
        (ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v))).ker := by
      ext x
      rw [← T23.mem_normClasses_finite_iff L v x, ← hUL]
      rfl
    rw [← (Ch7.localNormInput K).index_eq L hab v Q, hker]
    exact index_ker_eq_orderOf _ (hcomp _)
  · intro w
    have hker : Ch7.localNormGroupInf L w =
        (ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofCompletion (𝓞 K) K w))).ker := by
      ext x
      rw [← T23.mem_normClasses_infinite_iff L w x, ← hUL]
      rfl
    have hidx := (Ch7.localNormInput K).index_inf L w
    rw [hker, index_ker_eq_orderOf _ (hcomp _)] at hidx
    rw [hidx]
    split_ifs with h <;> simp [h]

end NumberFieldKB.MilneCFT.Ch8.GW
