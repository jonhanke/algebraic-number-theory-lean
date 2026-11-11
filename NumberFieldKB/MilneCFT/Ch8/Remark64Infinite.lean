import NumberFieldKB.MilneCFT.Ch8.Remark64
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Remark VIII.6.4: the local Galois data at the infinite places

For a finite Galois extension $L/K$ of number fields and an infinite place $v$ of $K$, `exists_infiniteDatum` gives a
`LocalGaloisDatum K L K_v` (Remark64.lean) whose group is the stabilizer $D_w$ of a place $w \mid v$ of $L$.
Construction: an embedding $\varphi : L \to \mathbb C$ extending $v$, $w = $ `mk φ`.
* $w$ unramified over $v$ ($D_w = 1$, `IsUnramified.stabilizer_eq_bot`): $E = K_v$, $L \to K_v$ through $\varphi$ and
  `extensionEmbedding` (for real $v$ the place $w$ is real, so $\varphi(L) \subseteq \mathbb R$).
* $w$ ramified ($v$ real, $w$ complex, $D_w = \{1, c\}$ with $c$ the complex conjugation, `IsConj φ c`):
  $E = \mathbb C$ as a $K_v$-algebra through `extensionEmbedding v` (image $\mathbb R$), $c$ acting by conjugation;
  the fixed field $\mathbb R$ is the image of $K_v$.
This is $L_w \supseteq K_v$ with $\operatorname{Gal}(L_w/K_v) = D_w$ at the archimedean places (Weil, *Basic Number
Theory*, III.§4, Cor. 4 of Thm. 4, infinite places).
-/

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

namespace NumberFieldKB.MilneCFT.Ch8

section Aux

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : InfinitePlace K)

private lemma extEmb_algebraMap (k : K) :
    extensionEmbedding v (algebraMap K v.Completion k) = v.embedding k := by
  have := extensionEmbedding_coe v ((WithAbs.equiv v.1).symm k)
  simpa using this

private lemma exists_embedding_over :
    ∃ φ : L →+* ℂ, φ.comp (algebraMap K L) = v.embedding := by
  obtain ⟨w0, hw0⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
  have h : mk (w0.embedding.comp (algebraMap K L)) = mk v.embedding := by
    rw [← comap_mk, mk_embedding]
    exact hw0.trans (mk_embedding v).symm
  rcases mk_eq_iff.1 h with h | h
  · exact ⟨w0.embedding, h⟩
  · exact ⟨ComplexEmbedding.conjugate w0.embedding, h⟩

private theorem exists_datum_unram [IsGalois K L] (φ : L →+* ℂ)
    (hφ : φ.comp (algebraMap K L) = v.embedding) (hu : (mk φ).IsUnramified K) :
    ∃ d : LocalGaloisDatum K L v.Completion,
      d.D = MulAction.stabilizer (L ≃ₐ[K] L) (mk φ) := by
  have hrange : ∀ x, φ x ∈ (extensionEmbedding v).range := by
    intro x
    by_cases hv : v.IsComplex
    · exact surjective_extensionEmbedding_of_isComplex hv (φ x)
    · have hvr : v.IsReal := not_isComplex_iff_isReal.1 hv
      have hwr : (mk φ).IsReal := by
        by_contra hw
        have := hu.eq
        rw [comap_mk, hφ, mk_embedding] at this
        simp [InfinitePlace.mult, hvr, hw] at this
      have hreal := isReal_mk_iff.1 hwr
      have hc : (starRingEnd ℂ) (φ x) = φ x := by
        have := congrArg (fun f : L →+* ℂ => f x) hreal
        simpa [ComplexEmbedding.conjugate_coe_eq] using this
      obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 hc
      obtain ⟨s, hs⟩ := surjective_extensionEmbeddingOfIsReal hvr r
      refine ⟨s, ?_⟩
      rw [hr, ← extensionEmbeddingOfIsReal_apply hvr s, hs]
  let e := extensionEmbedding v
  choose g hg using hrange
  let emb : L →+* v.Completion :=
    { toFun := g
      map_one' := e.injective (by rw [hg, map_one, map_one])
      map_mul' := fun x y => e.injective (by rw [hg, map_mul, map_mul, hg, hg])
      map_zero' := e.injective (by rw [hg, map_zero, map_zero])
      map_add' := fun x y => e.injective (by rw [hg, map_add, map_add, hg, hg]) }
  have hemb : ∀ x, e (emb x) = φ x := hg
  have hstab : MulAction.stabilizer (L ≃ₐ[K] L) (mk φ) = ⊥ := hu.stabilizer_eq_bot
  refine ⟨{ E := v.Completion
            instField := inferInstance
            instAlg := Algebra.id _
            emb := emb
            emb_algebraMap := ?_
            D := MulAction.stabilizer (L ≃ₐ[K] L) (mk φ)
            act := 1
            act_emb := ?_
            fixed := ?_ }, rfl⟩
  · intro k
    apply e.injective
    rw [hemb, ← RingHom.comp_apply φ, hφ]
    simp [e, extEmb_algebraMap]
  · intro σ x
    have : (σ : L ≃ₐ[K] L) = 1 :=
      Subgroup.mem_bot.1 ((SetLike.ext_iff.1 hstab _).1 σ.2)
    simp [this]
  · intro y _
    exact ⟨y, rfl⟩

private theorem exists_datum_ram [IsGalois K L] (φ : L →+* ℂ)
    (hφ : φ.comp (algebraMap K L) = v.embedding) (hr : (mk φ).IsRamified K) :
    ∃ d : LocalGaloisDatum K L v.Completion,
      d.D = MulAction.stabilizer (L ≃ₐ[K] L) (mk φ) := by
  obtain ⟨c, hc⟩ := exists_isConj_of_isRamified hr
  have hvr : v.IsReal := by
    have := (isRamified_iff.1 hr).2
    rwa [comap_mk, hφ, mk_embedding] at this
  have hwc : (mk φ).IsComplex := (isRamified_iff.1 hr).1
  have hcne : c ≠ 1 := by
    intro h
    subst h
    have : (mk φ).IsReal := isReal_mk_iff.2 (ComplexEmbedding.isConj_one_iff.1 hc)
    exact (not_isReal_iff_isComplex.2 hwc) this
  have hcc : c * c = 1 := by
    have : c = c⁻¹ := hc.ext hc.symm
    exact mul_eq_one_iff_eq_inv.2 this
  letI : Algebra v.Completion ℂ := (extensionEmbedding v).toAlgebra
  have hreal : ∀ s : v.Completion, (starRingEnd ℂ) (algebraMap v.Completion ℂ s) =
      algebraMap v.Completion ℂ s := by
    intro s
    show (starRingEnd ℂ) (extensionEmbedding v s) = extensionEmbedding v s
    rw [← extensionEmbeddingOfIsReal_apply hvr s, Complex.conj_ofReal]
  let conjAlg : ℂ ≃ₐ[v.Completion] ℂ :=
    AlgEquiv.ofRingEquiv (f := Complex.conjAe.toRingEquiv) (fun s => hreal s)
  have conjAlg_apply : ∀ z, conjAlg z = (starRingEnd ℂ) z := fun z => rfl
  have hD : ∀ σ : MulAction.stabilizer (L ≃ₐ[K] L) (mk φ),
      (σ : L ≃ₐ[K] L) = 1 ∨ ComplexEmbedding.IsConj φ (σ : L ≃ₐ[K] L) := fun σ =>
    (mem_stabilizer_mk_iff (k := K) φ (σ : L ≃ₐ[K] L)).1 σ.2
  have hne : ∀ σ : MulAction.stabilizer (L ≃ₐ[K] L) (mk φ), (σ : L ≃ₐ[K] L) ≠ 1 →
      (σ : L ≃ₐ[K] L) = c := fun σ h => by
    rcases hD σ with h' | h'
    · exact absurd h' h
    · exact h'.ext hc
  classical
  let act : MulAction.stabilizer (L ≃ₐ[K] L) (mk φ) →* (ℂ ≃ₐ[v.Completion] ℂ) :=
    MonoidHom.mk' (fun σ => if (σ : L ≃ₐ[K] L) = 1 then 1 else conjAlg) (by
      intro σ τ
      have hconj2 : conjAlg * conjAlg = 1 := by
        refine AlgEquiv.ext fun z => ?_
        show conjAlg (conjAlg z) = z
        rw [conjAlg_apply, conjAlg_apply, Complex.conj_conj]
      show (if ((σ * τ : MulAction.stabilizer (L ≃ₐ[K] L) (mk φ)) : L ≃ₐ[K] L) = 1 then 1
          else conjAlg) = (if (σ : L ≃ₐ[K] L) = 1 then 1 else conjAlg) *
            (if (τ : L ≃ₐ[K] L) = 1 then 1 else conjAlg)
      rw [Subgroup.coe_mul]
      by_cases h1 : (σ : L ≃ₐ[K] L) = 1 <;> by_cases h2 : (τ : L ≃ₐ[K] L) = 1
      · rw [if_pos (by rw [h1, h2, mul_one]), if_pos h1, if_pos h2, mul_one]
      · rw [if_neg (by rw [h1, one_mul]; exact h2), if_pos h1, if_neg h2, one_mul]
      · rw [if_neg (by rw [h2, mul_one]; exact h1), if_neg h1, if_pos h2, mul_one]
      · have e1 := hne σ h1
        have e2 := hne τ h2
        have : (σ : L ≃ₐ[K] L) * τ = 1 := by rw [e1, e2, hcc]
        rw [if_pos this, if_neg h1, if_neg h2, hconj2])
  have hact : ∀ σ : MulAction.stabilizer (L ≃ₐ[K] L) (mk φ), (σ : L ≃ₐ[K] L) ≠ 1 →
      act σ = conjAlg := fun σ h => by
    show (if (σ : L ≃ₐ[K] L) = 1 then 1 else conjAlg) = conjAlg
    exact if_neg h
  have hact1 : ∀ σ : MulAction.stabilizer (L ≃ₐ[K] L) (mk φ), (σ : L ≃ₐ[K] L) = 1 →
      act σ = 1 := fun σ h => by
    show (if (σ : L ≃ₐ[K] L) = 1 then 1 else conjAlg) = 1
    exact if_pos h
  refine ⟨{ E := ℂ
            instField := inferInstance
            instAlg := (extensionEmbedding v).toAlgebra
            emb := φ
            emb_algebraMap := ?_
            D := MulAction.stabilizer (L ≃ₐ[K] L) (mk φ)
            act := act
            act_emb := ?_
            fixed := ?_ }, rfl⟩
  · intro k
    rw [← RingHom.comp_apply φ, hφ]
    show _ = extensionEmbedding v (algebraMap K v.Completion k)
    rw [extEmb_algebraMap]
  · intro σ x
    by_cases h : (σ : L ≃ₐ[K] L) = 1
    · rw [hact1 σ h]; simp [h]
    · rw [hact σ h, conjAlg_apply]
      have := (hne σ h ▸ hc : ComplexEmbedding.IsConj φ (σ : L ≃ₐ[K] L)).eq x
      simp [this]
  · intro y hy
    have hcmem : c ∈ MulAction.stabilizer (L ≃ₐ[K] L) (mk φ) :=
      (mem_stabilizer_mk_iff φ c).2 (Or.inr hc)
    have := hy ⟨c, hcmem⟩
    rw [hact ⟨c, hcmem⟩ hcne, conjAlg_apply] at this
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 this
    obtain ⟨s, hs⟩ := surjective_extensionEmbeddingOfIsReal hvr r
    refine ⟨s, ?_⟩
    show extensionEmbedding v s = y
    rw [← extensionEmbeddingOfIsReal_apply hvr s, hs, hr]

end Aux

theorem exists_infiniteDatum (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (v : InfinitePlace K) :
    ∃ (d : LocalGaloisDatum K L v.Completion) (w : InfinitePlace L),
      w.comap (algebraMap K L) = v ∧ d.D = MulAction.stabilizer (L ≃ₐ[K] L) w := by
  obtain ⟨φ, hφ⟩ := exists_embedding_over (K := K) (L := L) v
  refine ?_
  have hw : (mk φ).comap (algebraMap K L) = v := by
    rw [comap_mk, hφ, mk_embedding]
  by_cases hu : (mk φ).IsUnramified K
  · obtain ⟨d, hd⟩ := exists_datum_unram v φ hφ hu
    exact ⟨d, mk φ, hw, hd⟩
  · have hr : (mk φ).IsRamified K := isRamified_iff.2 (not_isUnramified_iff.1 hu)
    obtain ⟨d, hd⟩ := exists_datum_ram v φ hφ hr
    exact ⟨d, mk φ, hw, hd⟩

end NumberFieldKB.MilneCFT.Ch8
