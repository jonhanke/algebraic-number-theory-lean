import NumberFieldKB.MilneCFT.Ch8.ExistsUUncond
import NumberFieldKB.MilneCFT.Ch8.ChevalleyDescent
import NumberFieldKB.MilneCFT.Ch8.ChevalleyKummer
import NumberFieldKB.MilneCFT.Ch8.ChevalleyTorsion

/-!
# Chevalley's congruence theorem for `S`-units, unconditionally

**Proved here:** `chevalleyCongruence : ChevalleyCongruence K` (the named statement of `Theorem23Uncond.lean`),
hence `existsU : ExistsU K` and `theorem2_3 : Theorem2_3 K` (Milne, *CFT*, VIII, Theorem 2.3).

## Proof
Let `E` be the `S`-units, `H ≤ E` of finite index `m` (so `E^m ≤ H`), `w` the number of roots of unity of `K`,
`n = m w`, `N = n w`, `K' = K(μ_N)`.
1. Kummer step (`exists_places_pow_eq`): finitely many places `T` outside `S ∪ B ∪ {v ∣ N}` such that an
   `S`-unit `≡ 1` at `T` is an `N`-th power in `K'`.
2. Descent (`exists_eq_mul_pow_of_pow_eq`): such an `a` is `ξ b^n` with `b ∈ K`, `ξ^w = 1`; `b` is an `S`-unit.
3. Torsion (`exists_place_not_pow`): for every prime `ℓ ∣ w` a place `q_ℓ` (outside the same set) at which a
   primitive `w`-th root of unity is not an `ℓ`-th power. If `a ≡ 1` at `q_ℓ`, then `ξ` is an `n`-th power at
   `q_ℓ` (Hensel), so `ℓ ∤ ord ξ` (`exists_pow_prime_eq_of_pow_eq`). Hence `ξ = 1` and `a = (b^w)^m ∈ H`.
`P = T ∪ {q_ℓ}`.
-/

open IsDedekindDomain NumberField
open scoped Classical

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.Chevalley

variable {K : Type} [Field K] [NumberField K]

/-- The roots of unity of a number field: a primitive `w`-th root of unity whose order is a multiple of the order
of every root of unity. -/
theorem exists_isPrimitiveRoot_max (K : Type) [Field K] [NumberField K] :
    ∃ w : ℕ, 0 < w ∧ (∃ ζ : K, IsPrimitiveRoot ζ w) ∧
      ∀ (e : ℕ) (x : K), 0 < e → IsPrimitiveRoot x e → e ∣ w := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := NumberField.Units.torsion K)
  refine ⟨NumberField.Units.torsionOrder K, NumberField.Units.torsionOrder_pos K, ⟨((g : (𝓞 K)ˣ) : K), ?_⟩, ?_⟩
  · rw [IsPrimitiveRoot.coe_coe_iff]
    have h1 : orderOf g = NumberField.Units.torsionOrder K := orderOf_eq_card_of_forall_mem_zpowers hg
    rw [← h1, ← orderOf_submonoid g]
    exact IsPrimitiveRoot.orderOf _
  · intro e x he hx
    have hint : IsIntegral ℤ x := hx.isIntegral he
    let x0 : 𝓞 K := ⟨x, hint⟩
    have hx0 : x0 ^ e = 1 := RingOfIntegers.ext (by push_cast; exact hx.pow_eq_one)
    let u : (𝓞 K)ˣ := ⟨x0, x0 ^ (e - 1), by rw [← pow_succ', Nat.sub_add_cancel he, hx0],
      by rw [← pow_succ, Nat.sub_add_cancel he, hx0]⟩
    have hu : u ∈ NumberField.Units.torsion K := by
      rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨e, he, Units.ext hx0⟩
    have hue : IsPrimitiveRoot u e := by
      rw [← IsPrimitiveRoot.coe_coe_iff]
      exact hx
    have h2 := orderOf_dvd_natCard (⟨u, hu⟩ : NumberField.Units.torsion K)
    rw [← orderOf_submonoid] at h2
    rw [hue.eq_orderOf]
    exact h2

/-- The finitely many places containing a nonzero natural number. -/
theorem finite_places_dvd {N : ℕ} (hN : N ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | (N : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have hn0 : ((N : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hN
  refine (Ideal.finite_factors (Ideal.span_singleton_eq_bot.not.mpr hn0)).subset fun v hv => ?_
  exact (Ideal.dvd_span_singleton).2 hv

/-- An element whose `n`-th power is an `S`-unit is an `S`-unit. -/
theorem mem_unit_of_pow_mem {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ} (hn : n ≠ 0) (b : Kˣ)
    (hb : b ^ n ∈ S.unit K) : b ∈ S.unit K := by
  intro v hv
  have h := hb v hv
  rw [Units.val_pow_eq_pow_val, map_pow] at h
  exact (pow_eq_one_iff_of_nonneg zero_le hn).1 h

/-- **Chevalley's congruence theorem**, unconditionally. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 2.3, p. 232 (Chevalley's congruence theorem for S-units)"]
theorem chevalleyCongruence : ChevalleyCongruence K := by
  refine ⟨fun S H hHE hidx B => ?_⟩
  set E := (S : Set (HeightOneSpectrum (𝓞 K))).unit K with hE
  set m := H.relIndex E with hm
  obtain ⟨w, hw, ⟨ζw, hζw⟩, hmaxw⟩ := exists_isPrimitiveRoot_max K
  have hm0 : 0 < m := Nat.pos_of_ne_zero hidx
  set n := m * w with hn
  have hn0 : 0 < n := Nat.mul_pos hm0 hw
  set N := n * w with hN
  have hN0 : 0 < N := Nat.mul_pos hn0 hw
  have : NeZero N := ⟨hN0.ne'⟩
  let K' := CyclotomicField N K
  have : IsGalois K K' := IsCyclotomicExtension.isGalois {N} K K'
  have : FiniteDimensional K K' := IsCyclotomicExtension.finiteDimensional {N} K K'
  have hζ' : IsPrimitiveRoot (IsCyclotomicExtension.zeta N K K') N :=
    IsCyclotomicExtension.zeta_spec N K K'
  have hint : IsIntegral ℤ (IsCyclotomicExtension.zeta N K K') := hζ'.isIntegral hN0
  let ζO : 𝓞 K' := ⟨_, hint⟩
  have hζO : IsPrimitiveRoot ζO N :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 K') K') hζ'
      (FaithfulSMul.algebraMap_injective (𝓞 K') K')
  let A0 : Finset (HeightOneSpectrum (𝓞 K)) := (finite_places_dvd (K := K) hN0.ne').toFinset
  let A : Finset (HeightOneSpectrum (𝓞 K)) := B ∪ A0
  have hA : ∀ v : HeightOneSpectrum (𝓞 K), (N : 𝓞 K) ∈ v.asIdeal → v ∈ A := fun v hv =>
    Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 hv)
  obtain ⟨T, hTdisj, hT⟩ := exists_places_pow_eq hN0 hζO S A hA
  have hq : ∀ ℓ : w.primeFactors, ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ A ∧
      (((ℓ : ℕ) * w : ℕ) : 𝓞 K) ∉ v.asIdeal ∧
      ¬ ∃ b : v.adicCompletion K, b ^ (ℓ : ℕ) = algebraMap K (v.adicCompletion K) ζw := by
    intro ℓ
    have hℓ := Nat.prime_of_mem_primeFactors ℓ.2
    refine exists_place_not_pow hw hℓ (Nat.dvd_of_mem_primeFactors ℓ.2) hζw (fun x hx => ?_) (S ∪ A)
    have h1 := hmaxw _ x (Nat.mul_pos hℓ.pos hw) hx
    have h2 : (ℓ : ℕ) ∣ 1 := Nat.dvd_of_mul_dvd_mul_right hw (by simpa using h1)
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 h2)
  choose q hqS hqN hqpow using hq
  have hBA : S ∪ B ⊆ S ∪ A := Finset.union_subset_union (le_refl S) Finset.subset_union_left
  refine ⟨T ∪ Finset.univ.image q, ?_, ?_⟩
  · refine Finset.disjoint_union_left.2 ⟨hTdisj.mono_right hBA, Finset.disjoint_left.2 ?_⟩
    intro v hv hvSB
    obtain ⟨ℓ, -, rfl⟩ := Finset.mem_image.1 hv
    exact hqS ℓ (hBA hvSB)
  intro a ha hcong
  obtain ⟨c, hc⟩ := hT a ha fun v hv => hcong v (Finset.mem_union_left _ hv)
  have hab : ∀ σ τ : K' ≃ₐ[K] K', σ * τ = τ * σ := fun σ τ =>
    (IsCyclotomicExtension.isMulCommutative {N} K K').is_comm.comm σ τ
  have hfix : ∀ e : ℕ, e ∣ n * w → (∀ σ : K' ≃ₐ[K] K',
      σ (IsCyclotomicExtension.zeta N K K' ^ (n * w / e)) =
        IsCyclotomicExtension.zeta N K K' ^ (n * w / e)) → e ∣ w := by
    intro e he hfixe
    have he0 : 0 < e := Nat.pos_of_dvd_of_pos he hN0
    have hx := (IsGalois.mem_bot_iff_fixed _).2 hfixe
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 hx
    have hprim : IsPrimitiveRoot (IsCyclotomicExtension.zeta N K K' ^ (N / e)) e := by
      have := hζ'.pow_of_dvd (p := N / e) (Nat.div_pos (Nat.le_of_dvd hN0 he) he0).ne'
        (Nat.div_dvd_of_dvd he)
      rwa [Nat.div_div_self he hN0.ne'] at this
    exact hmaxw e y he0 (IsPrimitiveRoot.of_map_of_injective (f := algebraMap K K') (by rwa [hy])
      (algebraMap K K').injective)
  obtain ⟨b, ξ, hξ, habξ⟩ := exists_eq_mul_pow_of_pow_eq hab hn0 hw hζ' hfix a.ne_zero hc
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply a.ne_zero
    rw [habξ, zero_pow hn0.ne', mul_zero]
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    apply a.ne_zero
    rw [habξ, zero_mul]
  let bu : Kˣ := Units.mk0 b hb0
  let ξu : Kˣ := Units.mk0 ξ hξ0
  have hξE : ξu ∈ E := mem_unit_of_pow_mem hw.ne' ξu (by
    have : ξu ^ w = 1 := Units.ext (by simp [ξu, hξ])
    rw [this]; exact one_mem _)
  have hauξ : a = ξu * bu ^ n := Units.ext (by simp [ξu, bu, habξ])
  have hbE : bu ∈ E := mem_unit_of_pow_mem hn0.ne' bu (by
    have : bu ^ n = ξu⁻¹ * a := by rw [hauξ]; group
    rw [this]; exact mul_mem (inv_mem hξE) ha)
  have hξ1 : ξ = 1 := by
    by_contra hne
    have hord : orderOf ξ ∣ w := orderOf_dvd_of_pow_eq_one hξ
    have hord1 : orderOf ξ ≠ 1 := by rwa [ne_eq, orderOf_eq_one_iff]
    obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hord1
    have hℓw : ℓ ∈ w.primeFactors := Nat.mem_primeFactors.2 ⟨hℓ, dvd_trans hℓd hord, hw.ne'⟩
    set v := q ⟨ℓ, hℓw⟩ with hv
    have hcv := hcong v (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
    have hnv : (n : 𝓞 K) ∉ v.asIdeal := by
      intro h
      apply hqS ⟨ℓ, hℓw⟩
      refine Finset.mem_union_right _ (hA v ?_)
      rw [hN, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ h
    obtain ⟨y, hy⟩ := exists_pow_eq_of_valued_sub_one_lt v hnv hcv
    have hb' : algebraMap K (v.adicCompletion K) b ≠ 0 := by
      rwa [ne_eq, map_eq_zero_iff _ (algebraMap K (v.adicCompletion K)).injective]
    have hyn : (y / algebraMap K (v.adicCompletion K) b) ^ n = algebraMap K (v.adicCompletion K) ξ := by
      rw [div_pow, hy, habξ, map_mul, map_pow]
      field_simp
    have hξw : (algebraMap K (v.adicCompletion K) ξ) ^ w = 1 := by rw [← map_pow, hξ, map_one]
    have hordι : orderOf (algebraMap K (v.adicCompletion K) ξ) = orderOf ξ :=
      orderOf_injective (algebraMap K (v.adicCompletion K)).toMonoidHom
        (algebraMap K (v.adicCompletion K)).injective ξ
    obtain ⟨z, hz⟩ := exists_pow_prime_eq_of_pow_eq hw hℓ
      (hζw.map_of_injective (algebraMap K (v.adicCompletion K)).injective)
      (Dvd.intro_left _ rfl : w ∣ n) hξw hyn (hordι ▸ hℓd)
    exact hqpow ⟨ℓ, hℓw⟩ ⟨z, hz⟩
  have hkey : ∀ x ∈ E, x ^ m ∈ H := fun x hx => by
    have := Subgroup.pow_index_mem (H.subgroupOf E) (⟨x, hx⟩ : E)
    rw [Subgroup.mem_subgroupOf] at this
    simpa [hm, Subgroup.relIndex] using this
  have : a = (bu ^ w) ^ m := by
    have hξu : ξu = 1 := Units.ext (by simp [ξu, hξ1])
    rw [hauξ, hξu, one_mul, ← pow_mul, hn, mul_comm]
  rw [this]
  exact hkey _ (pow_mem hbE _)

end NumberFieldKB.MilneCFT.Ch8.Chevalley

namespace NumberFieldKB.MilneCFT.Ch8

variable (K : Type) [Field K] [NumberField K]

/-- **An open subgroup of `C_K` with prescribed local traces** (the global input `ExistsU` of Theorem VIII.2.3),
unconditionally. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 2.3, p. 232 (open subgroup with prescribed local traces)"]
theorem existsU : ExistsU K := existsU_of_chevalley K Chevalley.chevalleyCongruence

/-- **Milne, CFT, VIII, Theorem 2.3** (abelian extensions with prescribed local norm groups at finitely many
places), unconditionally. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 2.3, p. 232"]
theorem theorem2_3 : Theorem2_3 K := theorem2_3_of_chevalley K Chevalley.chevalleyCongruence

end NumberFieldKB.MilneCFT.Ch8
