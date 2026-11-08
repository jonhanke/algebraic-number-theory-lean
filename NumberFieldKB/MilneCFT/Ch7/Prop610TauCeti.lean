import NumberFieldKB.MilneCFT.Ch7.KummerTauCeti
import NumberFieldKB.MilneCFT.Ch7.Lemma67
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.Kummer.Index
import NumberFieldKB.TauCetiPort.FieldTheory.Kummer.Cyclic

/-!
# Milne, *Class Field Theory*, Chapter VII, Proposition 6.10 and Lemma 6.7 from the Tau Ceti port

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VII, §6
(pp. 215-219).

* `isPow_of_prime`: the conclusion of the named statement `Prop6_10` for a **prime** exponent `p`, proved from Tau
  Ceti's `TauCeti.ClassFieldTheory.unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_iff`.
* `lemma6_7`: **Lemma 6.7** unconditionally (it only needs `Prop6_10` at a prime exponent).
* `isPow_of_pos`, `prop6_10`: **Proposition 6.10** for every `n ≥ 1`, replaying Tau Ceti's Kummer-field argument
  with `Gal(K(a^{1/n})/K)` cyclic (`TauCeti.isCyclic_of_pow_eq_of_adjoin_eq_top`) and the first inequality.
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.Ch7

variable {K : Type} [Field K] [NumberField K]

/-- Our `sUnitsToLocalQuot` surjectivity gives Tau Ceti's `unitLocalPowerClassMap` surjectivity (converse of
`sUnitsToLocalQuot_surjective_of`). -/
theorem unitLocalPowerClassMap_surjective_of {S T : Set (HeightOneSpectrum (𝓞 K))} (hST : Disjoint S T)
    {n : ℕ} (hsurj : Function.Surjective (sUnitsToLocalQuot S T hST n)) :
    Function.Surjective (Set.unitLocalPowerClassMap S T hST n) := by
  intro x
  choose g hg using fun v : T => QuotientGroup.mk_surjective (x v)
  have hgv : ∀ v : T, ((g v).1 : (v.1.adicCompletion K)ˣ) ∈ localUnits K v.1 := fun v =>
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2
      ((HeightOneSpectrum.mem_unitFiltration_zero_adicCompletion_iff v.1).1 (g v).2)
  obtain ⟨u, hu⟩ := hsurj fun v => QuotientGroup.mk ⟨(g v).1, hgv v⟩
  refine ⟨u, funext fun v => ?_⟩
  rw [← hg v, Set.unitLocalPowerClassMap_apply]
  have h1 := congrFun hu v
  obtain ⟨b, hb⟩ := QuotientGroup.eq.1 h1
  refine QuotientGroup.eq.2 ⟨⟨b.1, (HeightOneSpectrum.mem_unitFiltration_zero_adicCompletion_iff v.1).2
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.1 b.2)⟩, ?_⟩
  have hb' := congrArg Subtype.val hb
  exact Subtype.ext hb'

/-- **Proposition 6.10 for a prime exponent** (Milne, *CFT*, Chapter VII, p. 219): the conclusion of
`Prop6_10.isPow` with `n = p` prime, proved from Tau Ceti's
`TauCeti.ClassFieldTheory.unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_iff`. -/
theorem isPow_of_prime (p : ℕ) (hp : p.Prime) (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (S T : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (hT : T.Finite) (hST : Disjoint S T)
    (hdvd : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hcl : Subgroup.closure ((fun v => primeClass K v) '' S) = ⊤)
    (hsurj : Function.Surjective (sUnitsToLocalQuot S T hST p))
    (b : Kˣ) (hinf : ∀ w : InfinitePlace K, IsPowAtInf w p (b : K))
    (hfin : ∀ v ∈ S, IsPowAt v p (b : K))
    (hunit : ∀ v, v ∉ S → v ∉ T → v.valuation K (b : K) = 1) : ∃ c : Kˣ, c ^ p = b := by
  obtain ⟨S', rfl⟩ : ∃ S' : Finset (HeightOneSpectrum (𝓞 K)), (S' : Set _) = S :=
    ⟨hS.toFinset, hS.coe_toFinset⟩
  obtain ⟨T', rfl⟩ : ∃ T' : Finset (HeightOneSpectrum (𝓞 K)), (T' : Set _) = T :=
    ⟨hT.toFinset, hT.coe_toFinset⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hζ
  have : HasEnoughRootsOfUnity K p := .of_card_le hζ.card_rootsOfUnity.ge
  have hcl' : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S' : Set (HeightOneSpectrum (𝓞 K)))) = ⊤ := by
    have hfun : (fun v => primeClass K v) =
        (HeightOneSpectrum.classGroupMk : HeightOneSpectrum (𝓞 K) → ClassGroup (𝓞 K)) :=
      funext fun v => (HeightOneSpectrum.classGroupMk_eq_mk0 v).symm
    rw [← hfun]
    exact hcl
  have hsurj' := unitLocalPowerClassMap_surjective_of hST hsurj
  have hmem : IdeleGroup.unitEmbedding (𝓞 K) K b ∈
      TauCeti.ClassFieldTheory.auxiliaryKummerIdeleSubgroup S' T' p := by
    rw [TauCeti.ClassFieldTheory.mem_auxiliaryKummerIdeleSubgroup_iff]
    refine ⟨fun v hv => ?_, fun w => ?_, fun v hvS hvT => ?_⟩
    · obtain ⟨y, hy⟩ := hfin v hv
      have hy' : y ^ p = algebraMap K (v.adicCompletion K) (b : K) := hy
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero] at hy'
        exact b.ne_zero ((map_eq_zero (algebraMap K (v.adicCompletion K))).1 hy'.symm)
      refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
      rw [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding]
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map]
      exact hy'
    · obtain ⟨y, hy⟩ := hinf w
      have hy' : y ^ p = algebraMap K w.Completion (b : K) := hy
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero] at hy'
        exact b.ne_zero ((map_eq_zero (algebraMap K w.Completion)).1 hy'.symm)
      refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
      rw [InfinitePlace.ideleInfiniteCoord_unitEmbedding]
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map]
      exact hy'
    · rw [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding]
      show Valued.v (((b : K) : v.adicCompletion K)) = 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) (v := v) (b : K)]
      exact hunit v hvS hvT
  have := (TauCeti.ClassFieldTheory.unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_iff hp hST hcl'
    hdvd hsurj' b).1 hmem
  obtain ⟨c, hc⟩ := this.2
  exact ⟨c, hc⟩

/-- **Lemma 6.7** (Milne, *CFT*, Chapter VII, pp. 217-218), unconditionally: from Lemma 6.9
(`lemma6_9`), Proposition 6.10 for the prime exponent `p` (`isPow_of_prime`) and the `S`-unit index
(`sUnitIndex`). -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.7"]
theorem lemma6_7 (K : Type) [Field K] [NumberField K] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K)))
    (M : Type) [Field M] [NumberField M] [Algebra K M] [IsGalois K M] : Lemma6_7 p S M := by
  classical
  have hSU := sUnitIndex K
  have h69 := lemma6_9 K p S M
  refine ⟨fun hset L T Q hTS hunr hF => ?_⟩
  have hp : 0 < p := hset.prime.pos
  set f := IdeleGroup.unitEmbedding (𝓞 K) K with hf
  have hmem : ∀ (a : Kˣ) (S' : Set (HeightOneSpectrum (𝓞 K))),
      (∀ v, v ∉ S' → Valued.v ((f a : AdeleRing (𝓞 K) K).2 v) = 1) ↔ a ∈ S'.unit K := by
    intro a S'
    refine ⟨fun h v hv => ?_, fun h v hv => ?_⟩
    · have := h v hv
      change Valued.v (((a : K) : v.adicCompletion K)) = 1 at this
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact this
    · have := h v hv
      change Valued.v (((a : K) : v.adicCompletion K)) = 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) (v := v) (a : K)]
      exact this
  have hsurj := h69.surjective hset L T Q hTS hunr hF
  have hdisj : Disjoint S (T : Set (HeightOneSpectrum (𝓞 K))) := hTS.symm
  have hcomap : (kummerE S T p).comap f = (powMonoidHom p : Kˣ →* Kˣ).range ⊓ (S ∪ T).unit K := by
    ext c
    constructor
    · intro hc
      obtain ⟨h1, h2, h3⟩ := hc
      have hcU : c ∈ (S ∪ (T : Set (HeightOneSpectrum (𝓞 K)))).unit K := by
        rw [← hmem]
        intro v hv
        exact h3 v (fun h => hv (Or.inl h)) (fun h => hv (Or.inr h))
      refine ⟨?_, hcU⟩
      obtain ⟨d, hd⟩ := isPow_of_prime p hset.prime hset.zeta S T hset.finite T.finite_toSet hdisj hset.dvd
        hset.classGroup hsurj c
        (fun w => by obtain ⟨y, hy⟩ := h1 w; exact ⟨y, hy⟩)
        (fun v hv => by obtain ⟨y, hy⟩ := h2 v hv; exact ⟨y, hy⟩)
        (fun v hvS hvT => by
          have := h3 v hvS hvT
          change Valued.v (((c : K) : v.adicCompletion K)) = 1 at this
          rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) (v := v) (c : K)] at this)
      exact ⟨d, hd⟩
    · rintro ⟨⟨d, rfl⟩, hcU⟩
      refine ⟨fun w => ⟨ideleInfAt (f d) w, ?_⟩, fun v _ => ⟨ideleFinAt (f d) v, ?_⟩, fun v hvS hvT => ?_⟩
      · show _ = (↑(f (d ^ p)) : AdeleRing (𝓞 K) K).1 w
        rw [map_pow, Units.val_pow_eq_pow_val]; rfl
      · show _ = (↑(f (d ^ p)) : AdeleRing (𝓞 K) K).2 v
        rw [map_pow, Units.val_pow_eq_pow_val]; rfl
      · exact (hmem _ (S ∪ T)).2 hcU v (by rintro (h | h) <;> contradiction)
  rw [hcomap, Subgroup.inf_relIndex_right]
  have hfin : (S ∪ (T : Set (HeightOneSpectrum (𝓞 K)))).Finite := hset.finite.union T.finite_toSet
  rw [hSU.index p _ hset.prime hset.zeta hfin,
    Set.ncard_union_eq hdisj hset.finite T.finite_toSet, Set.ncard_coe_finset]
  congr 1
  omega

/-! ## Proposition 6.10 for arbitrary `n`

Tau Ceti's proof of `unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_iff` goes through for any exponent `n` (the
Kummer field of `zpowers a` is cyclic over `K` of degree dividing `n`); we replay it with `n` composite. -/

/-- The Kummer field of the cyclic group generated by `a` is cyclic over `K`, when `K` contains the `n`-th roots of
unity. -/
theorem isCyclic_kummerField_zpowers {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (a : Kˣ)
    [(powMonoidHom n : Kˣ →* Kˣ).range.IsFiniteRelIndex (Subgroup.zpowers a)]
    [HasEnoughRootsOfUnity K n] :
    IsCyclic (TauCeti.kummerField (AlgebraicClosure K) n (Subgroup.zpowers a) ≃ₐ[K]
      TauCeti.kummerField (AlgebraicClosure K) n (Subgroup.zpowers a)) := by
  set M := TauCeti.kummerField (AlgebraicClosure K) n (Subgroup.zpowers a)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (a : K))
    (NeZero.pos n)
  let s : M := ⟨x, TauCeti.mem_kummerField_of_pow_eq (Subgroup.mem_zpowers a) hx⟩
  have hs : s ^ n = algebraMap K M (a : K) := Subtype.ext (by simpa using hx)
  have hs0 : s ≠ 0 := TauCeti.ne_zero_of_pow_eq_algebraMap hs
  have hgen : IntermediateField.adjoin K {s} = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← TauCeti.adjoin_pow_eq_algebraMap_kummerField_eq_top (K := K) (E := AlgebraicClosure K)
      (n := n) (Δ := Subgroup.zpowers a), IntermediateField.adjoin_le_iff]
    rintro y ⟨c, hc, hy⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    have hyk : y ^ n = (s ^ k) ^ n := by
      rw [hy, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs]
      simp [map_zpow₀]
      rfl
    obtain ⟨z, hz⟩ := TauCeti.exists_eq_algebraMap_mul_of_pow_eq (K := K) hyk
    rw [hz]
    exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _)
      (zpow_mem (IntermediateField.mem_adjoin_simple_self K s) k)
  exact TauCeti.isCyclic_of_pow_eq_of_adjoin_eq_top hζ a.ne_zero hs hgen

/-- Replay of Tau Ceti's private `mem_range_powMonoidHom_of_unitEmbedding_mem_auxiliaryKummerIdeleSubgroup`
for an arbitrary exponent `n`. -/
theorem mem_range_pow_of_unitEmbedding_mem_aux {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    {S T : Finset (HeightOneSpectrum (𝓞 K))}
    (hST : Disjoint (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K))))
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hsurj : Function.Surjective
      (Set.unitLocalPowerClassMap (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set _) hST n))
    {a : Kˣ}
    (ha : IdeleGroup.unitEmbedding (𝓞 K) K a ∈ TauCeti.ClassFieldTheory.auxiliaryKummerIdeleSubgroup S T n) :
    a ∈ (powMonoidHom n : Kˣ →* Kˣ).range := by
  have : NeZero n := ⟨hn.ne'⟩
  have : HasEnoughRootsOfUnity K n := .of_card_le hζ.card_rootsOfUnity.ge
  have hmem := (TauCeti.ClassFieldTheory.mem_auxiliaryKummerIdeleSubgroup_iff S T n _).1 ha
  set Δ := Subgroup.zpowers a
  have hdvd : (powMonoidHom n : Kˣ →* Kˣ).range.relIndex Δ ∣ n := by
    have h := Subgroup.relIndex_dvd_of_le_left Δ
      (Subgroup.zpowers_le.2 ⟨a, (zpow_natCast a n).symm⟩ :
        Subgroup.zpowers (a ^ (n : ℤ)) ≤ (powMonoidHom n : Kˣ →* Kˣ).range)
    rw [Subgroup.relIndex_zpowers_zpow, Int.gcd_natCast_natCast] at h
    exact h.trans (Nat.gcd_dvd_left _ _)
  have : (powMonoidHom n : Kˣ →* Kˣ).range.IsFiniteRelIndex Δ :=
    ⟨fun h ↦ hn.ne' (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))⟩
  have hpow {M : Type} [CommMonoid M] (f : Kˣ →* Mˣ)
      (hf : f a ∈ (powMonoidHom n : Mˣ →* Mˣ).range) (b : Kˣ) (hb : b ∈ Δ) :
      f b ∈ (powMonoidHom n : Mˣ →* Mˣ).range :=
    Subgroup.zpowers_le.2 (Subgroup.mem_comap.2 hf) hb
  have hroots (b : Kˣ) (_ : b ∈ Δ) : ∃ x : AlgebraicClosure K, x ^ n = algebraMap K _ b :=
    IsAlgClosed.exists_pow_nat_eq _ hn
  have hdeg := TauCeti.finrank_kummerField hroots
  have : IsCyclic (TauCeti.kummerField (AlgebraicClosure K) n Δ ≃ₐ[K]
      TauCeti.kummerField (AlgebraicClosure K) n Δ) := isCyclic_kummerField_zpowers hζ a
  have hnorm := TauCeti.ClassFieldTheory.ideleClassNormMap_kummerField_surjective_of_forall_exists_mem_unit
    (E := AlgebraicClosure K) S T (Finset.disjoint_coe.1 hST) hcl hnS
    (Subgroup.zpowers_le.2 <|
      (TauCeti.ClassFieldTheory.unitEmbedding_mem_auxiliaryKummerIdeleSubgroup_one_iff S T a).1 <|
        TauCeti.ClassFieldTheory.auxiliaryKummerIdeleSubgroup_le_one S T n ha)
    (fun v hv b hb ↦ by
      obtain ⟨c, hc⟩ := hpow _ (HeightOneSpectrum.ideleFiniteCoord_unitEmbedding v a ▸ hmem.1 v hv)
        b hb
      exact ⟨c, by simpa using congrArg Units.val hc⟩)
    (fun w b hb ↦ by
      obtain ⟨c, hc⟩ := hpow _
        (InfinitePlace.ideleInfiniteCoord_unitEmbedding (R := 𝓞 K) w a ▸ hmem.2.1 w) b hb
      exact ⟨c, by simpa using congrArg Units.val hc⟩)
    (hdeg ▸ hdvd) (Set.exists_mem_unit_of_unitLocalPowerClassMap_surjective _ _ _ hsurj)
  have h1 := TauCeti.ClassFieldTheory.finrank_eq_one_of_surjective_ideleClassNormMap K _ hnorm
  rw [hdeg, Subgroup.relIndex_eq_one] at h1
  exact h1 (Subgroup.mem_zpowers a)

/-- The conclusion of `Prop6_10.isPow` for every exponent `n > 0`. -/
theorem isPow_of_pos (n : ℕ) (hn : 0 < n) (hζ : ∃ ζ : K, IsPrimitiveRoot ζ n)
    (S T : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (hT : T.Finite) (hST : Disjoint S T)
    (hdvd : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hcl : Subgroup.closure ((fun v => primeClass K v) '' S) = ⊤)
    (hsurj : Function.Surjective (sUnitsToLocalQuot S T hST n))
    (b : Kˣ) (hinf : ∀ w : InfinitePlace K, IsPowAtInf w n (b : K))
    (hfin : ∀ v ∈ S, IsPowAt v n (b : K))
    (hunit : ∀ v, v ∉ S → v ∉ T → v.valuation K (b : K) = 1) : ∃ c : Kˣ, c ^ n = b := by
  obtain ⟨S', rfl⟩ : ∃ S' : Finset (HeightOneSpectrum (𝓞 K)), (S' : Set _) = S :=
    ⟨hS.toFinset, hS.coe_toFinset⟩
  obtain ⟨T', rfl⟩ : ∃ T' : Finset (HeightOneSpectrum (𝓞 K)), (T' : Set _) = T :=
    ⟨hT.toFinset, hT.coe_toFinset⟩
  obtain ⟨ζ, hζ⟩ := hζ
  have hcl' : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S' : Set (HeightOneSpectrum (𝓞 K)))) = ⊤ := by
    have hfun : (fun v => primeClass K v) =
        (HeightOneSpectrum.classGroupMk : HeightOneSpectrum (𝓞 K) → ClassGroup (𝓞 K)) :=
      funext fun v => (HeightOneSpectrum.classGroupMk_eq_mk0 v).symm
    rw [← hfun]
    exact hcl
  have hsurj' := unitLocalPowerClassMap_surjective_of hST hsurj
  have hmem : IdeleGroup.unitEmbedding (𝓞 K) K b ∈
      TauCeti.ClassFieldTheory.auxiliaryKummerIdeleSubgroup S' T' n := by
    rw [TauCeti.ClassFieldTheory.mem_auxiliaryKummerIdeleSubgroup_iff]
    refine ⟨fun v hv => ?_, fun w => ?_, fun v hvS hvT => ?_⟩
    · obtain ⟨y, hy⟩ := hfin v hv
      have hy' : y ^ n = algebraMap K (v.adicCompletion K) (b : K) := hy
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [zero_pow hn.ne'] at hy'
        exact b.ne_zero ((map_eq_zero (algebraMap K (v.adicCompletion K))).1 hy'.symm)
      refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
      rw [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding]
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map]
      exact hy'
    · obtain ⟨y, hy⟩ := hinf w
      have hy' : y ^ n = algebraMap K w.Completion (b : K) := hy
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [zero_pow hn.ne'] at hy'
        exact b.ne_zero ((map_eq_zero (algebraMap K w.Completion)).1 hy'.symm)
      refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
      rw [InfinitePlace.ideleInfiniteCoord_unitEmbedding]
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map]
      exact hy'
    · rw [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding]
      show Valued.v (((b : K) : v.adicCompletion K)) = 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) (v := v) (b : K)]
      exact hunit v hvS hvT
  obtain ⟨c, hc⟩ := mem_range_pow_of_unitEmbedding_mem_aux hn hζ hST hcl' hdvd hsurj' hmem
  exact ⟨c, hc⟩

/-- **Proposition 6.10** (Milne, *CFT*, Chapter VII, p. 219), for every `n ≥ 1` with a primitive `n`-th root of
unity in `K`: the named statement `Prop6_10`, proved by replaying Tau Ceti's Kummer-field argument for composite
`n`. -/
@[kb "milne2020cft" "Ch. VII, Prop. 6.10"]
theorem prop6_10 (K : Type) [Field K] [NumberField K] : Prop6_10 K where
  isPow n hn hζ S T hS hT hST hdvd hcl hsurj b hinf hfin hunit :=
    isPow_of_pos n hn hζ S T hS hT hST hdvd hcl hsurj b hinf hfin hunit

end NumberFieldKB.MilneCFT.Ch7
