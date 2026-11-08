import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangSpecial
import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangValuation
import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangLocalChar
import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangField

/-!
# Milne, *CFT*, VIII, Corollary 2.5, unconditionally (including the special case)

**Proved here:** `GW.corollary2_5 : Corollary2_5 K`: for local degrees `n_v` at finitely many places (`n_w ∈ {1, 2}` at
real places, `1` at complex ones) there is a cyclic extension of degree `n = lcm n_v` with these local degrees.

Proof (Artin–Tate X §2). Let `S' = S ∪ {v ∣ n}`. By Remark 1.5 (a) (`R15a.remark1_5a`), `P(n, S') ⊆ K^{×n} ∪ a₀K^{×n}`
for some `a₀ ∈ P(n, S')`. Local characters of order exactly `n_v` killing `a₀`:
* at a finite `v` not above `2`, the unramified character of order `n_v` (`v(a₀) ≡ 0 mod n` by
  `GW.exists_valuation_eq_of_mem_powSet`);
* at `v ∣ 2`, with `n_v = 2^k m'` (`m'` odd): the unramified character of order `m'` (`a₀` is an `m`-th power, `m` the
  odd part of `n`, `R15a.powSet_odd`) times a character of order `2^k` killing `a₀` (`GW.exists_char_two_pow`);
* at a real place with `n_w = 2`, the sign character (`a₀` is a square: `P(2, S') = K^{×2}`).
`GW.exists_char_pow_eq_one_of_mem` gives `ψ` with these components and `ψ^n = 1`, hence of order `n`, and
`GW.exists_field_of_char` the cyclic extension.
-/

open IsDedekindDomain NumberField TauCeti.GlobalNumberFields
open scoped Classical

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.GW

open ExistsUAux

variable {K : Type} [Field K] [NumberField K]

local notation "ι" => IdeleGroup.unitEmbedding (𝓞 K) K

/-- `K(ζ_{2^t})/K` is trivial, hence cyclic, for `t ≤ 1`. -/
theorem isCyclic_cyclotomic_two_pow_of_le_one {t : ℕ} (ht : t ≤ 1) :
    IsCyclic (CyclotomicField (2 ^ t) K ≃ₐ[K] CyclotomicField (2 ^ t) K) := by
  haveI : NeZero (2 ^ t) := ⟨by positivity⟩
  haveI : NeZero ((2 ^ t : ℕ) : K) := ⟨by exact_mod_cast (pow_ne_zero t two_ne_zero)⟩
  have hζ := IsCyclotomicExtension.zeta_spec (2 ^ t) K (CyclotomicField (2 ^ t) K)
  have hsub : Subsingleton (ZMod (2 ^ t))ˣ := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ht with rfl | rfl
    · exact ⟨fun a b => Units.ext (Subsingleton.elim (α := ZMod 1) _ _)⟩
    · exact Fintype.card_le_one_iff_subsingleton.1 (by rw [ZMod.card_units_eq_totient]; decide)
  haveI : Subsingleton (CyclotomicField (2 ^ t) K ≃ₐ[K] CyclotomicField (2 ^ t) K) :=
    ⟨fun a b => hζ.autToPow_injective K (Subsingleton.elim _ _)⟩
  infer_instance

/-- Elements of `P(n, S)`, `n` even, are squares. -/
theorem sq_of_mem_powSet {n : ℕ} (h2 : 2 ∣ n) {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) {a : Kˣ}
    (ha : a ∈ powSet n S) : ∃ b : Kˣ, b ^ 2 = a := by
  refine powSet_subset_of_isCyclic two_pos hS (fun t ht => isCyclic_cyclotomic_two_pow_of_le_one ?_) a
    (R15a.mem_powSet_of_dvd h2 ha)
  have h := Nat.le_of_dvd two_pos ht
  by_contra hlt
  have : 2 ^ 2 ≤ 2 ^ t := Nat.pow_le_pow_right two_pos (by omega)
  omega

/-- `v(c^m) ≡ 0 mod m`. -/
theorem valuation_pow_eq (v : HeightOneSpectrum (𝓞 K)) (c : Kˣ) (m : ℕ) :
    ∃ k : ℤ, v.valuation K ((c ^ m : Kˣ) : K) = WithZero.exp ((m : ℤ) * k) := by
  have h0 : v.valuation K (c : K) ≠ 0 := by simp
  refine ⟨WithZero.log (v.valuation K (c : K)), ?_⟩
  rw [Units.val_pow_eq_pow_val, map_pow, ← nsmul_eq_mul, WithZero.exp_nsmul, WithZero.exp_log h0]

/-- The order of a restriction of a character divides the order of the character. -/
theorem orderOf_comp_dvd {G H : Type*} [Group G] [Group H] (ψ : G →* ℂˣ) (f : H →* G) :
    orderOf (ψ.comp f) ∣ orderOf ψ := by
  refine orderOf_dvd_of_pow_eq_one (MonoidHom.ext fun y => ?_)
  rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, pow_orderOf_eq_one,
    MonoidHom.one_apply, MonoidHom.one_apply]

/-- **Milne, CFT, VIII, Corollary 2.5** (cyclic extensions with prescribed local degrees), unconditionally. -/
@[kb "milne2020cft" "Ch. VIII, Corollary 2.5, p. 232"]
theorem corollary2_5 : Corollary2_5 K := by
  refine ⟨fun S T nv nw hpos hT n h1 h2 hmin => ?_⟩
  have hnw : ∀ w ∈ T, 0 < nw w := fun w hw => by rcases hT w hw with h | ⟨-, h⟩ <;> omega
  have hn : 0 < n := by
    set m := (∏ v ∈ S, nv v) * ∏ w ∈ T, nw w
    have hm0 : m ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v hv => (hpos v hv).ne')
      (Finset.prod_ne_zero_iff.2 fun w hw => (hnw w hw).ne')
    have := hmin m (fun v hv => dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hv) _)
      (fun w hw => dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hw) _)
    exact Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hm0 this)
  have hn0 : ((n : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hn.ne'
  have hD : {v : HeightOneSpectrum (𝓞 K) | (n : 𝓞 K) ∈ v.asIdeal}.Finite :=
    (Ideal.finite_factors (Ideal.span_singleton_eq_bot.not.mpr hn0)).subset fun v hv =>
      (Ideal.dvd_span_singleton).2 hv
  set S' : Finset (HeightOneSpectrum (𝓞 K)) := S ∪ hD.toFinset with hS'
  set T' : Set (HeightOneSpectrum (𝓞 K)) := (S' : Set _) ∪ {v | (n : 𝓞 K) ∈ v.asIdeal} with hT'
  have hT'f : T'.Finite := S'.finite_toSet.union hD
  obtain ⟨a₀, ha₀mem, ha₀⟩ : ∃ a₀ : Kˣ, a₀ ∈ powSet n T' ∧
      ∀ a ∈ powSet n T', ∃ b : Kˣ, a = b ^ n ∨ a = a₀ * b ^ n := by
    rcases (R15a.remark1_5a (K := K)).dichotomy n hn T' hT'f with h | ⟨a₀, h⟩
    · refine ⟨1, R15a.one_mem_powSet n T', fun a ha => ?_⟩
      rw [h] at ha
      obtain ⟨b, rfl⟩ := ha
      exact ⟨b, Or.inl rfl⟩
    · refine ⟨a₀, ?_, fun a ha => ?_⟩
      · rw [h]
        exact Or.inr ⟨1, by simp⟩
      · rw [h] at ha
        rcases ha with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · exact ⟨b, Or.inl rfl⟩
        · exact ⟨b, Or.inr rfl⟩
  obtain ⟨r, mo, hmo, hnr⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  obtain ⟨c, hc⟩ := R15a.powSet_odd hT'f mo hmo a₀
    (R15a.mem_powSet_of_dvd (Dvd.intro_left _ hnr.symm) ha₀mem)
  -- local characters at the finite places of `S`
  have hloc : ∀ v ∈ S, ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ, Continuous χ ∧ orderOf χ = nv v ∧
      χ (v.ideleFiniteCoord (ι a₀)) = 1 := by
    intro v hv
    by_cases h2v : (2 : 𝓞 K) ∈ v.asIdeal
    · obtain ⟨k, m', hm', hnv⟩ := Nat.exists_eq_two_pow_mul_odd (hpos v hv).ne'
      obtain ⟨χ1, hc1, ho1, hk1⟩ := exists_unramified_char v hm'.pos
      obtain ⟨χ2, hc2, ho2, hk2⟩ := exists_char_two_pow v h2v k (v.ideleFiniteCoord (ι a₀))
      have hcop : Nat.Coprime m' (2 ^ k) := (Nat.coprime_two_right.2 hm').pow_right k
      refine ⟨χ1 * χ2, hc1.mul hc2, ?_, ?_⟩
      · rw [(Commute.all χ1 χ2).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ho1, ho2]; exact hcop),
          ho1, ho2, hnv, mul_comm]
      · have hm'mo : m' ∣ mo := by
          have hd : 2 ^ k * m' ∣ 2 ^ r * mo := hnv ▸ hnr ▸ h1 v hv
          have hd' : m' ∣ 2 ^ r * mo := dvd_trans (Dvd.intro_left _ rfl) hd
          exact ((Nat.coprime_two_right.2 hm').pow_right r).dvd_of_dvd_mul_left hd'
        obtain ⟨d, hd⟩ := hm'mo
        obtain ⟨j, hj⟩ := valuation_pow_eq v c mo
        have h1' : χ1 (v.ideleFiniteCoord (ι a₀)) = 1 := by
          refine hk1 _ ⟨d * j, ?_⟩
          rw [valued_coord_unitEmbedding, ← hc, hj, hd]
          push_cast
          ring_nf
        rw [MonoidHom.mul_apply, h1', hk2, one_mul]
    · obtain ⟨χ1, hc1, ho1, hk1⟩ := exists_unramified_char v (hpos v hv)
      refine ⟨χ1, hc1, ho1, hk1 _ ?_⟩
      obtain ⟨j, hj⟩ := exists_valuation_eq_of_mem_powSet hn hT'f ha₀mem v h2v
      obtain ⟨d, hd⟩ := h1 v hv
      refine ⟨d * j, ?_⟩
      rw [valued_coord_unitEmbedding, hj, hd]
      push_cast
      ring_nf
  -- local characters at the infinite places of `T`
  have hinf : ∀ w ∈ T, ∃ χ : w.Completionˣ →* ℂˣ, Continuous χ ∧ orderOf χ = nw w ∧
      χ (w.ideleInfiniteCoord (ι a₀)) = 1 := by
    intro w hw
    rcases hT w hw with h | ⟨hreal, h⟩
    · exact ⟨1, continuous_const, by rw [h, orderOf_one], rfl⟩
    · obtain ⟨χ, hcχ, ho⟩ := exists_sign_char w hreal
      have h2n : 2 ∣ n := h ▸ h2 w hw
      obtain ⟨b, hb⟩ := sq_of_mem_powSet h2n hT'f ha₀mem
      refine ⟨χ, hcχ, by rw [ho, h], ?_⟩
      have hχ2 : χ ^ 2 = 1 := ho ▸ pow_orderOf_eq_one χ
      rw [← hb, map_pow, map_pow (w.ideleInfiniteCoord), map_pow χ, ← MonoidHom.pow_apply, hχ2,
        MonoidHom.one_apply]
  choose! χ hχc hχo hχk using hloc
  choose! χ' hχc' hχo' hχk' using hinf
  let χS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ := fun v => if v ∈ S then χ v else 1
  have hχS : ∀ v ∈ S, χS v = χ v := fun v hv => if_pos hv
  have hχS' : ∀ v ∉ S, χS v = 1 := fun v hv => if_neg hv
  have hS'c : ∀ v ∈ S', Continuous (χS v) ∧ IsOfFinOrder (χS v) := by
    intro v _
    by_cases hv : v ∈ S
    · rw [hχS v hv]
      exact ⟨hχc v hv, orderOf_pos_iff.1 (by rw [hχo v hv]; exact hpos v hv)⟩
    · rw [hχS' v hv]
      exact ⟨continuous_const, isOfFinOrder_iff_pow_eq_one.2 ⟨1, one_pos, by ext; simp⟩⟩
  have hT'c : ∀ w ∈ T, Continuous (χ' w) ∧ IsOfFinOrder (χ' w) := fun w hw =>
    ⟨hχc' w hw, orderOf_pos_iff.1 (by rw [hχo' w hw]; exact hnw w hw)⟩
  have hχn : ∀ v ∈ S', χS v ^ n = 1 := by
    intro v _
    by_cases hv : v ∈ S
    · rw [hχS v hv]
      exact orderOf_dvd_iff_pow_eq_one.1 (show orderOf (χ v) ∣ n by rw [hχo v hv]; exact h1 v hv)
    · rw [hχS' v hv]; ext; simp
  have hχn' : ∀ w ∈ T, χ' w ^ n = 1 := fun w hw =>
    orderOf_dvd_iff_pow_eq_one.1 (show orderOf (χ' w) ∣ n by rw [hχo' w hw]; exact h2 w hw)
  have hS₀ : ∀ v ∈ S', χS v (v.ideleFiniteCoord (ι a₀)) = 1 := by
    intro v _
    by_cases hv : v ∈ S
    · rw [hχS v hv]; exact hχk v hv
    · rw [hχS' v hv, MonoidHom.one_apply]
  obtain ⟨ψ, hψc, hψS, hψT, hψn⟩ :=
    exists_char_pow_eq_one_of_mem S' T χS χ' hS'c hT'c hn hχn hχn' a₀ ha₀ hS₀ hχk'
  have hψS1 : ∀ v ∈ S, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v)) = χ v :=
    fun v hv => (hψS v (Finset.mem_union_left _ hv)).trans (hχS v hv)
  have hord : orderOf ψ = n := by
    refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hψn) (hmin _ (fun v hv => ?_) (fun w hw => ?_))
    · rw [← hχo v hv, ← hψS1 v hv]
      exact orderOf_comp_dvd ψ _
    · rw [← hχo' w hw, ← hψT w hw]
      exact orderOf_comp_dvd ψ _
  obtain ⟨L, _, _, _, _, hcyc, hdeg, hlocL, hinfL⟩ := exists_field_of_char ψ hψc hn hord
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hcyc, hdeg, fun v hv Q => ?_,
    fun w hw => ?_⟩
  · rw [hlocL v Q, hψS1 v hv, hχo v hv]
  · rw [hinfL w, hψT w hw, hχo' w hw]

end NumberFieldKB.MilneCFT.Ch8.GW
