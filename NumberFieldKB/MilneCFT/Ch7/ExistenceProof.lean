import NumberFieldKB.MilneCFT.Ch7.Existence

/-!
# Milne, *Class Field Theory*, Chapter VII §9: Theorem 9.5 from Lemmas 9.3 and 9.4

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, p. 226.
Induction on the index $n=(C_K:U)$, simultaneously for all number fields.
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

theorem normal_of_ideleClass (F : Type) [Field F] [NumberField F]
    (U : Subgroup (IdeleClassGroup (𝓞 F) F)) : U.Normal :=
  ⟨fun n hn g => by rw [mul_comm g n, mul_inv_cancel_right]; exact hn⟩

/-- A finite abelian group of order divisible by a prime $p$ surjects onto $\mathbb Z/p$. -/
theorem exists_surjective_zmod (G : Type) [CommGroup G] [Finite G] (p : ℕ) (hp : p.Prime)
    (hd : p ∣ Nat.card G) : ∃ f : G →* Multiplicative (ZMod p), Function.Surjective f := by
  classical
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  have hcard : Nat.card G = ∏ i, n i := by
    rw [Nat.card_congr e.toEquiv, Nat.card_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    haveI : NeZero (n i) := ⟨by have := hn i; omega⟩
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [hcard] at hd
  obtain ⟨i, -, hi⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp hd
  let g : Multiplicative (ZMod (n i)) →* Multiplicative (ZMod p) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom hi (ZMod p)).toAddMonoidHom
  refine ⟨g.comp ((Pi.evalMonoidHom (fun j => Multiplicative (ZMod (n j))) i).comp e.toMonoidHom),
    ?_⟩
  have h1 : Function.Surjective g := fun y => by
    obtain ⟨x, hx⟩ := ZMod.ringHom_surjective (ZMod.castHom hi (ZMod p)) (Multiplicative.toAdd y)
    exact ⟨Multiplicative.ofAdd x, Multiplicative.toAdd.injective (by simpa [g] using hx)⟩
  have h2 : Function.Surjective (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (n j))) i) :=
    fun y => ⟨Pi.mulSingle i y, by simp⟩
  exact h1.comp (h2.comp e.surjective)

/-- In a commutative group, a finite-index subgroup whose index is divisible by a prime $p$ lies in a subgroup of
index $p$ (all of whose elements' $p$-th powers... i.e. every $p$-th power lies in it). -/
theorem exists_index_prime_overgroup (C : Type) [CommGroup C] (U : Subgroup C) (p : ℕ) (hp : p.Prime)
    [U.FiniteIndex] (hd : p ∣ U.index) :
    ∃ U₁ : Subgroup C, U ≤ U₁ ∧ U₁.index = p ∧ ∀ c : C, c ^ p ∈ U₁ := by
  haveI : Finite (C ⧸ U) := inferInstance
  obtain ⟨f, hf⟩ := exists_surjective_zmod (C ⧸ U) p hp hd
  let π := f.comp (QuotientGroup.mk' U)
  have hle : U ≤ π.ker := fun x hx => by
    simp [π, (QuotientGroup.eq_one_iff x).mpr hx]
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcardp : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  refine ⟨π.ker, hle, ?_, fun c => ?_⟩
  · have hπ : Function.Surjective π := hf.comp (QuotientGroup.mk'_surjective U)
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hπ, Subgroup.card_top, hcardp]
  · rw [MonoidHom.mem_ker, map_pow]
    have h : (π c) ^ p = (π c) ^ Nat.card (Multiplicative (ZMod p)) := by rw [hcardp]
    rw [h]
    exact pow_card_eq_one'

/-- **Theorem 9.5 from Lemmas 9.3 and 9.4** (Milne, *CFT*, Chapter VII, p. 226: induction on the index). -/
@[kb "milne2020cft" "Ch. VII, Thm. 9.5 (proof from Lemmas 9.3, 9.4)"]
theorem theorem9_5_of_lemmas
    (h93 : ∀ (F : Type) [Field F] [NumberField F], Lemma9_3 F)
    (hR : ∀ (F : Type) [Field F] [NumberField F], ReciprocityLaw F)
    (hNL : ∀ (F : Type) [Field F] [NumberField F], NormLimitation F)
    (K : Type) [Field K] [NumberField K] : Theorem9_5 K := by
  refine ⟨fun U hUo hUf => ?_⟩
  have key : ∀ n : ℕ, ∀ (F : Type) [Field F] [NumberField F]
      (U : Subgroup (IdeleClassGroup (𝓞 F) F)), IsOpen (U : Set (IdeleClassGroup (𝓞 F) F)) →
      U.FiniteIndex → U.index = n → IsNormGroup F U := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    -- the step in a field containing a primitive `p`-th root of unity
    have step : ∀ (p : ℕ), p.Prime → p ∣ n → ∀ (F : Type) [Field F] [NumberField F],
        (∃ ζ : F, IsPrimitiveRoot ζ p) →
        ∀ (U : Subgroup (IdeleClassGroup (𝓞 F) F)), IsOpen (U : Set (IdeleClassGroup (𝓞 F) F)) →
        U.FiniteIndex → U.index = n → IsNormGroup F U := by
      intro p hp hpn F _ _ hζ U hUo hUf hUn
      have hn0 : n ≠ 0 := by rw [← hUn]; exact hUf.index_ne_zero
      obtain ⟨U₁, hle, hU1i, hpow⟩ := exists_index_prime_overgroup (IdeleClassGroup (𝓞 F) F) U p hp
        (by rw [hUn]; exact hpn)
      have hU1o : IsOpen (U₁ : Set (IdeleClassGroup (𝓞 F) F)) := Subgroup.isOpen_mono hle hUo
      haveI hU1f : U₁.FiniteIndex := ⟨by rw [hU1i]; exact hp.ne_zero⟩
      obtain ⟨L, iF, iN, iA, iG, hc, hU1⟩ :=
        (h93 F).isNormGroup p hp hζ U₁ hU1o hU1f hpow
      have hcont : Continuous (ideleClassNorm F L) :=
        (NumberFieldKB.Ideles.ideleClassRelNorm (Module.finBasis F L)).continuous
      have hm : (U.comap (ideleClassNorm F L)).index * p = n := by
        rw [Subgroup.index_comap]
        have : (ideleClassNorm F L).range = U₁ := by rw [hU1]; rfl
        rw [this, ← hU1i, Subgroup.relIndex_mul_index hle, hUn]
      have hm0 : (U.comap (ideleClassNorm F L)).index ≠ 0 := by
        intro h; rw [h] at hm; omega
      have hlt : (U.comap (ideleClassNorm F L)).index < n := by
        have := hp.two_le
        have := Nat.pos_of_ne_zero hm0
        nlinarith
      have hU'' := ih _ hlt L (U.comap (ideleClassNorm F L)) (hUo.preimage hcont) ⟨hm0⟩ rfl
      exact lemma_9_4 F (hR F) (hNL F) U L hU''
    intro F _ _ U hUo hUf hUn
    by_cases h1 : n = 1
    · subst h1
      have hU : U = ⊤ := Subgroup.index_eq_one.mp hUn
      obtain ⟨W, hW, -⟩ := (hNL F).contains F F
      rw [hU]
      exact lemma_9_1 F (hR F) hW le_top
    · have hn0 : n ≠ 0 := by rw [← hUn]; exact hUf.index_ne_zero
      set p := n.minFac with hpdef
      have hp : p.Prime := Nat.minFac_prime h1
      have hpn : p ∣ n := Nat.minFac_dvd n
      let F' := CyclotomicField p F
      haveI : NeZero p := ⟨hp.ne_zero⟩
      haveI : NumberField F' := IsCyclotomicExtension.numberField {p} F F'
      have hcont : Continuous (ideleClassNorm F F') :=
        (NumberFieldKB.Ideles.ideleClassRelNorm (Module.finBasis F F')).continuous
      have hdvd : (U.comap (ideleClassNorm F F')).index ∣ n := by
        haveI : U.Normal := normal_of_ideleClass F U
        rw [Subgroup.index_comap, ← hUn]
        exact Subgroup.relIndex_dvd_index_of_normal _ _
      have hU'o := hUo.preimage hcont
      have hU'f : (U.comap (ideleClassNorm F F')).FiniteIndex := by
        refine ⟨fun h => ?_⟩
        rw [h] at hdvd
        exact hn0 (zero_dvd_iff.mp hdvd)
      have hU' : IsNormGroup F' (U.comap (ideleClassNorm F F')) := by
        rcases (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd).lt_or_eq with hlt | heq
        · exact ih _ hlt F' _ hU'o hU'f rfl
        · exact step p hp hpn F' ⟨_, IsCyclotomicExtension.zeta_spec p F F'⟩ _ hU'o hU'f heq
      exact lemma_9_4 F (hR F) (hNL F) U F' hU'
  exact key _ K U hUo hUf rfl

end NumberFieldKB.MilneCFT.Ch7
