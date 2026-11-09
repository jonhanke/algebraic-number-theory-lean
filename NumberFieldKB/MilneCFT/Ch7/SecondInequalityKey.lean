import NumberFieldKB.MilneCFT.Ch7.Lemma67

/-!
# Milne, *Class Field Theory*, Chapter VII §6: the key case of the second inequality

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, Chapter VII, §6
(pp. 215–217). In the Kummer setting, for $L\subseteq M$ and $T$ as in Lemma 6.2, the boxed formula
$(\mathbb I_K : K^\times E) = p^r = [L:K]$ gives $(\mathbb I_K : K^\times\mathrm{Nm}\,\mathbb I_L)\mid[L:K]$.
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable {K : Type} [Field K] [NumberField K]
variable {M : Type} [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

/-- $(\mathbb I_K : K^\times E)\cdot p^t = p^s$ (Lemmas 4.2, 6.5, 6.6, 6.7), $E = E(S,T)$, $t = |T|$. -/
theorem index_kummerE_T_sup (h68 : Prop6_8 K) {p : ℕ} {S : Set (HeightOneSpectrum (𝓞 K))}
    (h67 : Lemma6_7 p S M) (hset : KummerSetting p S M) (L : IntermediateField K M)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (Q : ∀ v : T, v.1.asIdeal.primesOver (𝓞 M))
    (hTS : Disjoint (T : Set (HeightOneSpectrum (𝓞 K))) S)
    (hTun : ∀ v ∈ T, v ∈ unramifiedPrimes K M) (hF : FrobBasis p L T Q) :
    (kummerE S (T : Set (HeightOneSpectrum (𝓞 K))) p ⊔ IdeleGroup.principalSubgroup (𝓞 K) K).index * p ^ T.card =
      p ^ (S.ncard + Fintype.card (InfinitePlace K)) := by
  classical
  have hp : 0 < p := hset.prime.pos
  set A := idelesS (S ∪ (T : Set (HeightOneSpectrum (𝓞 K)))) with hA
  set B := kummerE S (T : Set (HeightOneSpectrum (𝓞 K))) p with hB
  set C := IdeleGroup.principalSubgroup (𝓞 K) K with hC
  set f := IdeleGroup.unitEmbedding (𝓞 K) K with hf
  have hBA : B ≤ A := fun x hx v hv => hx.2.2 v (fun h => hv (Or.inl h)) (fun h => hv (Or.inr h))
  have h65 := lemma_6_5 (C := C) hBA
  have hAC : A ⊔ C = ⊤ := by
    rw [sup_comm]
    refine lemma_4_2 K _ ?_
    rw [eq_top_iff, ← hset.classGroup]
    exact Subgroup.closure_mono (Set.image_mono Set.subset_union_left)
  have h66 : B.relIndex A = p ^ (2 * (S.ncard + Fintype.card (InfinitePlace K))) :=
    (lemma_6_6_of_prop_6_8 h68 p S M).index hset T hTS
  have hfinj : Function.Injective f := (item_4_2 (K := K)).1
  have hCrange : C = f.range := rfl
  have hinfC : A ⊓ C = ((S ∪ (T : Set (HeightOneSpectrum (𝓞 K)))).unit K).map f := by
    ext x
    constructor
    · rintro ⟨hxA, c, rfl⟩
      refine ⟨c, fun v hv => ?_, rfl⟩
      have := hxA v hv
      change Valued.v (((c : K) : v.adicCompletion K)) = 1 at this
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact this
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun v hv => ?_, c, rfl⟩
      have := hc v hv
      change Valued.v (((c : K) : v.adicCompletion K)) = 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) (v := v) (c : K)]
      exact this
  have hBC : B ⊓ C = (B.comap f).map f := by
    rw [Subgroup.map_comap_eq, hCrange, inf_comm]
  have hrel2 : (B ⊓ C).relIndex (A ⊓ C) = p ^ (S.ncard + Fintype.card (InfinitePlace K) + T.card) := by
    rw [hinfC, hBC, Subgroup.relIndex_map_map_of_injective _ _ hfinj]
    exact h67.index hset L T Q hTS hTun hF
  rw [hAC, Subgroup.relIndex_top_right, hrel2, h66] at h65
  have hpos : 0 < p ^ (S.ncard + Fintype.card (InfinitePlace K)) := pow_pos hp _
  have h2s : p ^ (2 * (S.ncard + Fintype.card (InfinitePlace K))) =
      p ^ (S.ncard + Fintype.card (InfinitePlace K)) * p ^ (S.ncard + Fintype.card (InfinitePlace K)) := by
    rw [two_mul, pow_add]
  rw [h2s, pow_add] at h65
  have h65' : p ^ (S.ncard + Fintype.card (InfinitePlace K)) *
      ((kummerE S (T : Set (HeightOneSpectrum (𝓞 K))) p ⊔ C).index * p ^ T.card) =
      p ^ (S.ncard + Fintype.card (InfinitePlace K)) * p ^ (S.ncard + Fintype.card (InfinitePlace K)) := by
    rw [← h65]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos h65'

/-- From a Frobenius basis, $[M:L] = p^{|T|}$ ($\mathrm{Gal}(M/L)\cong\mathbb F_p^T$). -/
theorem finrank_fixing_eq {p : ℕ} (hp : p.Prime) (L : IntermediateField K M)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (Q : ∀ v : T, v.1.asIdeal.primesOver (𝓞 M))
    (hF : FrobBasis p L T Q) : Module.finrank L M = p ^ T.card := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : Nat.card L.fixingSubgroup = Nat.card (T → ZMod p) := by
    have e := hF.equiv _
    rw [Nat.card_congr (Equiv.Set.univ (T → ZMod p)).symm]
    exact (Nat.card_congr e).symm.trans (Nat.card_congr (Equiv.refl _))
  rw [← IsGalois.card_fixingSubgroup_eq_finrank L, h1, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_coe]

/-- **Second inequality, key case** (Milne, *CFT*, Chapter VII, §6, pp. 216–217): in the Kummer setting with
$[M:K] = p^s$, for every intermediate field $L$ (with $T$ as in Lemma 6.2),
$(\mathbb I_K : K^\times\mathrm{Nm}\,\mathbb I_L)$ is finite and divides $[L:K]$. -/
@[kb "milne2020cft" "Ch. VII, §6, second inequality in the Kummer case (from Lemmas 6.4, 6.6, 6.7)"]
theorem secondInequality_key {p : ℕ} {S : Set (HeightOneSpectrum (𝓞 K))} (h64 : Lemma6_4 p S M)
    (h68 : Prop6_8 K) (h67 : Lemma6_7 p S M) (hset : KummerSetting p S M)
    (hdeg : Module.finrank K M = p ^ (S.ncard + Fintype.card (InfinitePlace K)))
    (L : IntermediateField K M) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (Q : ∀ v : T, v.1.asIdeal.primesOver (𝓞 M)) (hTS : Disjoint (T : Set (HeightOneSpectrum (𝓞 K))) S)
    (hTun : ∀ v ∈ T, v ∈ unramifiedPrimes K M) (hF : FrobBasis p L T Q) :
    (principalNormIdeles K L).FiniteIndex ∧ (principalNormIdeles K L).index ∣ Module.finrank K L := by
  have hp := hset.prime
  have hle : kummerE S (T : Set (HeightOneSpectrum (𝓞 K))) p ⊔ IdeleGroup.principalSubgroup (𝓞 K) K ≤
      principalNormIdeles K L :=
    sup_le (le_sup_of_le_right (h64.le hset L T Q hTS hTun hF)) le_sup_left
  have h1 := index_kummerE_T_sup h68 h67 hset L T Q hTS hTun hF
  have h2 := finrank_fixing_eq hp L T Q hF
  have h3 : Module.finrank K L * Module.finrank L M = Module.finrank K M := Module.finrank_mul_finrank K L M
  rw [h2, hdeg] at h3
  have hpos : 0 < p ^ T.card := pow_pos hp.pos _
  have h4 : (kummerE S (T : Set (HeightOneSpectrum (𝓞 K))) p ⊔
      IdeleGroup.principalSubgroup (𝓞 K) K).index = Module.finrank K L :=
    Nat.eq_of_mul_eq_mul_right hpos (h1.trans h3.symm)
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [h4] at hdvd
  refine ⟨⟨?_⟩, hdvd⟩
  intro h0
  rw [h0] at hdvd
  have := Nat.eq_zero_of_zero_dvd hdvd
  have hfin : 0 < Module.finrank K L := Module.finrank_pos
  omega

/-- As `secondInequality_key`, with $T$ obtained from Lemma 6.2. -/
@[kb "milne2020cft" "Ch. VII, §6, second inequality in the Kummer case (from Lemmas 6.2, 6.4, 6.6, 6.7)"]
theorem secondInequality_key' {p : ℕ} {S : Set (HeightOneSpectrum (𝓞 K))} (h62 : Lemma6_2 p S M)
    (h64 : Lemma6_4 p S M) (h68 : Prop6_8 K) (h67 : Lemma6_7 p S M) (hset : KummerSetting p S M)
    (hdeg : Module.finrank K M = p ^ (S.ncard + Fintype.card (InfinitePlace K)))
    (L : IntermediateField K M) :
    (principalNormIdeles K L).FiniteIndex ∧ (principalNormIdeles K L).index ∣ Module.finrank K L := by
  obtain ⟨T, Q, hTS, hTun, hF⟩ := h62.exists_T hset L
  exact secondInequality_key h64 h68 h67 hset hdeg L T Q hTS hTun hF

/-- **The second inequality in the Kummer case** (Milne, *CFT*, Chapter VII, §6, pp. 215–218): conditional on
Lemmas 6.2, 6.4, 6.9, Propositions 6.8, 6.10 and Kummer theory (`KummerAppendix`), for $p$ prime, $\zeta_p\in K$
and $S$ finite containing the primes over $p$ and generators of the class group, there is
$M = K[U(S)^{1/p}]$ (Galois, abelian, in Milne's setting) such that every intermediate field $L$ satisfies
$(\mathbb I_K : K^\times\mathrm{Nm}(\mathbb I_L))\mid[L:K]$. Lemma 6.6 (from 6.8), Lemma 6.7 (from 6.9, 6.10) and the
$S$-unit index are proved. -/
@[kb "milne2020cft" "Ch. VII, §6, second inequality for subfields of K[U(S)^(1/p)] (from Lemmas 6.2, 6.4, 6.9, Props 6.8, 6.10, App. A.3)"]
theorem secondInequality_kummer (h62 : ∀ (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [Field M]
      [NumberField M] [Algebra K M] [IsGalois K M], Lemma6_2 p S M)
    (h64 : ∀ (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [Field M]
      [NumberField M] [Algebra K M] [IsGalois K M], Lemma6_4 p S M)
    (h69 : ∀ (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [Field M]
      [NumberField M] [Algebra K M] [IsGalois K M], Lemma6_9 p S M)
    (h68 : Prop6_8 K) (h610 : Prop6_10 K) (hKum : KummerAppendix K)
    (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (hp : p.Prime) (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (hS : S.Finite) (hdvd : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hcl : Subgroup.closure ((fun v => primeClass K v) '' S) = ⊤) :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra K M) (_ : IsGalois K M),
      (∀ σ τ : Gal(M/K), σ * τ = τ * σ) ∧ KummerSetting p S M ∧
      ∀ L : IntermediateField K M,
        (principalNormIdeles K L).FiniteIndex ∧ (principalNormIdeles K L).index ∣ Module.finrank K L := by
  obtain ⟨M, _, _, _, _, hc, hset, hdeg⟩ := hKum.exists_ext p S hp hζ hS hdvd hcl
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, hc, hset, fun L => ?_⟩
  rw [(sUnitIndex K).index p S hp hζ hS] at hdeg
  exact secondInequality_key' (h62 p S M) (h64 p S M) h68
    (lemma_6_7_of_lemma_6_9 h610 (h69 p S M)) hset hdeg L

end NumberFieldKB.MilneCFT.Ch7
