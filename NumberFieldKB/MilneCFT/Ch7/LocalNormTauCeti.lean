import NumberFieldKB.MilneCFT.Ch8.HasseNormTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.ExponentNorms
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.LocalArtin.FinitePlace
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Local.Reciprocity
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Units
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.InfinitePlace.Completion.Norm

/-!
# Milne, *Class Field Theory*, Chapter I, Theorem 1.1 (b) and Chapter III, Proposition 1.2 at completions of number
fields, from the Tau Ceti port

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter I, Theorem 1.1 (b),
Chapter III, Proposition 1.2, as used in Chapter VII.

The named statement `LocalNormInput` is proved here (`localNormInput`) from the ported Tau Ceti development
(`NumberFieldKB/TauCetiPort/`, Apache 2.0, the Tau Ceti contributors). Milne's local norm groups
`localNormGroup`, `localNormGroupInf` are the ranges of the norm of the étale algebra $K_v\otimes_KL$
(`Ch8.mem_localNormGroup_iff`, `Ch8.mem_localNormGroupInf_iff`), and Tau Ceti's
`TauCeti.mem_range_normUnits_adicCompletion_iff` writes such a norm as a product of norms from the completions
$L_w$, $w\mid v$. The four fields are obtained as follows.

* `pow_le`: `TauCeti.ClassFieldTheory.pow_mem_range_normUnits_adicCompletion`.
* `units_le`: `TauCeti.exists_unit_preimages_of_isUnramifiedAt` (units at an unramified place are local norms).
* `index_eq`: for $L/K$ abelian the local norm group is the kernel of Tau Ceti's local Artin symbol
  `TauCeti.ClassFieldTheory.localArtinAt` (via `localArtinAt_eq_one_iff_mem_normGroup`); its image is the
  decomposition group (`range_localArtinAt`), of order $e f$
  (`HeightOneSpectrum.card_stabilizer_eq_finrank_adicCompletion`, `HeightOneSpectrum.finrank_adicCompletion`).
* `index_inf`: if $w$ does not ramify, some $L_{w'}$ has degree one
  (`TauCeti.mem_range_normUnits_completion_of_finrank_eq_one`) and every element is a norm; if it ramifies, all places
  above are complex (Galois conjugates) and the norm group is the set of positive reals
  (`NumberField.InfinitePlace.Completion.mem_normGroup_iff_of_isRamified`), of index $2$.
-/

open IsDedekindDomain NumberField IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct AdicCompletionExtension NumberField.LiesOver Classical IsMulCommutative

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

section Aux

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- For abelian $L/K$ the local norm group at $v$ is the kernel of the local Artin symbol. -/
theorem localNormGroup_eq_ker_localArtinAt [IsMulCommutative Gal(L/K)] (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    localNormGroup L v = (TauCeti.ClassFieldTheory.localArtinAt K L v).ker := by
  classical
  ext x
  rw [Ch8.mem_localNormGroup_iff, TauCeti.mem_range_normUnits_adicCompletion_iff, MonoidHom.mem_ker]
  constructor
  · rintro ⟨u, rfl⟩
    refine finprod_induction (fun y => TauCeti.ClassFieldTheory.localArtinAt K L v y = 1) (map_one _)
      (fun a b ha hb => by rw [map_mul, ha, hb, one_mul]) (fun w' => ?_)
    haveI := w'.2
    exact (TauCeti.ClassFieldTheory.localArtinAt_eq_one_iff_mem_normGroup v w'.1 _).2
      (TauCeti.mem_normGroup_iff.2 ⟨u w', rfl⟩)
  · intro hx
    obtain ⟨b, hb⟩ := TauCeti.mem_normGroup_iff.1
      ((TauCeti.ClassFieldTheory.localArtinAt_eq_one_iff_mem_normGroup v w x).1 hx)
    let W : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} := ⟨w, inferInstance⟩
    refine ⟨Pi.mulSingle W b, ?_⟩
    rw [finprod_eq_single _ W fun w' hw' => by simp [Pi.mulSingle_eq_of_ne hw']]
    rw [Pi.mulSingle_eq_same]
    ext
    simp [hb]

theorem index_eq_aux (hab : ∀ σ τ : Gal(L/K), σ * τ = τ * σ) (v : HeightOneSpectrum (𝓞 K))
    (Q : v.asIdeal.primesOver (𝓞 L)) :
    (localNormGroup L v).index = Q.1.ramificationIdx (𝓞 K) * Q.1.inertiaDeg (𝓞 K) := by
  haveI : IsMulCommutative Gal(L/K) := ⟨⟨hab⟩⟩
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot Q.2⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := Q.2.2
  have hinj : Function.Injective (Abelianization.of : Gal(L/K) → Abelianization Gal(L/K)) := by
    have h := (Abelianization.equivOfComm (H := Gal(L/K))).injective
    have e : (Abelianization.of : Gal(L/K) → Abelianization Gal(L/K)) =
        ⇑(Abelianization.equivOfComm (H := Gal(L/K))) := by
      funext a
      first | rfl | simp
    rw [e]
    exact h
  rw [localNormGroup_eq_ker_localArtinAt K L v w, Subgroup.index_ker,
    TauCeti.ClassFieldTheory.range_localArtinAt v w]
  rw [Subgroup.card_map_of_injective hinj]
  rw [HeightOneSpectrum.card_stabilizer_eq_finrank_adicCompletion v w,
    HeightOneSpectrum.finrank_adicCompletion]

theorem units_le_aux (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ NumberFieldKB.Chebotarev.unramifiedPrimes K L) :
    localUnits K v ≤ localNormGroup L v := by
  intro x hx
  have hval := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.1 hx
  rw [Ch8.mem_localNormGroup_iff, TauCeti.mem_range_normUnits_adicCompletion_iff]
  obtain ⟨u, hu, -⟩ := TauCeti.exists_unit_preimages_of_isUnramifiedAt K L v _ hval (by
    obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
    have hP0 := Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hP.isPrime, hPv⟩
    exact ⟨⟨⟨P, hP.isPrime, hP0⟩, hPv⟩, hv P hP.isPrime hPv⟩)
  exact ⟨u, hu⟩

theorem pow_le_aux (n : ℕ) (hn : ∀ σ : Gal(L/K), σ ^ n = 1) (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : x ^ n ∈ localNormGroup L v := by
  rw [Ch8.mem_localNormGroup_iff]
  exact TauCeti.ClassFieldTheory.pow_mem_range_normUnits_adicCompletion K L
    (Monoid.exponent_dvd_of_forall_pow_eq_one hn) v x

theorem index_inf_aux (v : InfinitePlace K) :
    (localNormGroupInf L v).index = if InfinitePlace.RamifiesIn L v then 2 else 1 := by
  classical
  have hmem : ∀ x, x ∈ localNormGroupInf L v ↔ ∃ u : (w : {w : InfinitePlace L // w.LiesOver v}) →
      w.1.Completionˣ, (∏ᶠ w, TauCeti.Algebra.normUnits v.Completion (u w)) = x := fun x =>
    (Ch8.mem_localNormGroupInf_iff K L v x).trans (TauCeti.mem_range_normUnits_completion_iff K L v x)
  obtain ⟨w0, hw0⟩ := InfinitePlace.comap_surjective (k := K) (K := L) v
  have hw0l : w0.LiesOver v := by subst hw0; infer_instance
  by_cases h : InfinitePlace.RamifiesIn L v
  · rw [if_pos h]
    obtain ⟨hv, w1, hw1, hc⟩ := h
    have hall : ∀ w : {w : InfinitePlace L // w.LiesOver v}, w.1.IsRamified K := fun w ↦ by
      have hcomap := (InfinitePlace.liesOver_iff_comap_eq).1 w.2
      obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq (k := K)
        (hw1.trans hcomap.symm)
      refine InfinitePlace.isRamified_iff.2 ⟨?_, by rw [hcomap]; exact hv⟩
      rw [← hσ]
      exact InfinitePlace.isComplex_smul_iff.2 hc
    have hpos : ∀ x : v.Completionˣ, x ∈ localNormGroupInf L v ↔
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (x : v.Completion) := by
      intro x
      rw [hmem]
      constructor
      · rintro ⟨u, rfl⟩
        refine finprod_induction (fun y : v.Completionˣ =>
          0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (y : v.Completion)) (by simp)
          (fun a b ha hb => by simpa using mul_pos ha hb) (fun w' => ?_)
        haveI := w'.2
        exact (InfinitePlace.Completion.mem_normGroup_iff_of_isRamified (hall w') hv).1
          (TauCeti.mem_normGroup_iff.2 ⟨u w', rfl⟩)
      · intro hx
        haveI := hw0l
        obtain ⟨b, hb⟩ := TauCeti.mem_normGroup_iff.1
          ((InfinitePlace.Completion.mem_normGroup_iff_of_isRamified (hall ⟨w0, hw0l⟩) hv).2 hx)
        let W : {w : InfinitePlace L // w.LiesOver v} := ⟨w0, hw0l⟩
        refine ⟨Pi.mulSingle W b, ?_⟩
        rw [finprod_eq_single _ W fun w' hw' => by simp [Pi.mulSingle_eq_of_ne hw']]
        rw [Pi.mulSingle_eq_same]
        ext
        simp [hb]
    rw [Subgroup.index_eq_two_iff]
    refine ⟨-1, fun b => ?_⟩
    have hb0 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (b : v.Completion) ≠ 0 :=
      (map_ne_zero _).2 b.ne_zero
    rw [hpos, hpos]
    have : InfinitePlace.Completion.extensionEmbeddingOfIsReal hv ((b * -1 : v.Completionˣ) : v.Completion) =
        -InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (b : v.Completion) := by simp
    rw [this]
    rcases lt_or_gt_of_ne hb0 with h1 | h1
    · simp [h1, h1.le, not_lt.2 h1.le]
    · simp [h1, not_lt.2 h1.le]
  · rw [if_neg h]
    have hfin : Module.finrank v.Completion w0.Completion = 1 := by
      haveI := hw0l
      have hcomap := (InfinitePlace.liesOver_iff_comap_eq).1 hw0l
      refine InfinitePlace.IsUnramified.finrank_eq_one v (InfinitePlace.isUnramified_iff.2 ?_)
      rcases v.isReal_or_isComplex with hv | hv
      · left
        rcases w0.isReal_or_isComplex with hw | hw
        · exact hw
        · exact absurd ⟨hv, w0, hcomap, hw⟩ h
      · right
        rw [hcomap]
        exact hv
    rw [Subgroup.index_eq_one, eq_top_iff]
    intro x _
    rw [Ch8.mem_localNormGroupInf_iff]
    exact TauCeti.mem_range_normUnits_completion_of_finrank_eq_one K L v ⟨⟨w0, hw0l⟩, hfin⟩ x

end Aux

/-- **Local class field theory at the completions, unconditional** (Milne, *CFT*, Chapter I, Theorem 1.1 (b),
Chapter III, Proposition 1.2): from the ported Tau Ceti local and semilocal norm theory. -/
@[kb "milne2020cft" "Ch. I, Thm. 1.1 (b), Ch. III, Prop. 1.2 (at completions of number fields)"]
theorem localNormInput (K : Type) [Field K] [NumberField K] : LocalNormInput K where
  index_eq := fun L _ _ _ _ hab v Q => index_eq_aux K L hab v Q
  units_le := fun L _ _ _ _ v hv => units_le_aux K L v hv
  index_inf := fun L _ _ _ _ w => index_inf_aux K L w
  pow_le := fun L _ _ _ _ _ n hn v x => pow_le_aux K L n hn v x

end NumberFieldKB.MilneCFT.Ch7
