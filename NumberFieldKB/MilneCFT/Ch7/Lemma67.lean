import NumberFieldKB.MilneCFT.Ch7.SUnitIndex

/-!
# Milne, *Class Field Theory*, Chapter VII, Lemma 6.7 (from Lemma 6.9, Proposition 6.10 and the $S$-unit theorem)

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VII, Lemma 6.7
(pp. 217-218). Following Milne: $K^\times\cap E\supseteq U(S\cup T)^p$ is clear; conversely an element of
$K^\times\cap E$ is a $p$-th power at the infinite places and at $v\in S$ and a unit outside $S\cup T$, so by
Lemma 6.9 and Proposition 6.10 it is a $p$-th power. Then the $S$-unit theorem gives the index.
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable {K : Type} [Field K] [NumberField K]

/-- **Lemma 6.7** (Milne, *CFT*, Chapter VII, pp. 217-218), as a reduction to Lemma 6.9, Proposition 6.10 and the
$S$-unit index. -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.7 (from Lemma 6.9, Prop. 6.10 and the S-unit theorem)"]
theorem lemma_6_7_of_prop_6_10 {p : ℕ} {S : Set (HeightOneSpectrum (𝓞 K))} {M : Type} [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] (h610 : Prop6_10 K) (hSU : SUnitIndex K) (h69 : Lemma6_9 p S M) :
    Lemma6_7 p S M := by
  classical
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
      obtain ⟨d, hd⟩ := h610.isPow p hp hset.zeta S T hset.finite T.finite_toSet hdisj hset.dvd hset.classGroup
        hsurj c
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

/-- **Lemma 6.7** (Milne, *CFT*, Chapter VII, pp. 217-218) from Lemma 6.9 and Proposition 6.10 alone: the $S$-unit
index is proved (`sUnitIndex`). -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.7 (from Lemma 6.9 and Prop. 6.10)"]
theorem lemma_6_7_of_lemma_6_9 {p : ℕ} {S : Set (HeightOneSpectrum (𝓞 K))} {M : Type} [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] (h610 : Prop6_10 K) (h69 : Lemma6_9 p S M) : Lemma6_7 p S M :=
  lemma_6_7_of_prop_6_10 h610 (sUnitIndex K) h69

end NumberFieldKB.MilneCFT.Ch7
