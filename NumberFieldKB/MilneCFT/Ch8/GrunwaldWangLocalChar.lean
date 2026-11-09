import NumberFieldKB.MilneCFT.Ch7.Prop68TauCeti
import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangChar
import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# Grunwald–Wang: local characters of prescribed order

**Proved here** (`GW` namespace):
* `GW.exists_unramified_char`: at a finite place `v`, for `m ≥ 1`, a continuous character of `K_v^×` of order exactly
  `m` killing every `x` with `v(x) ≡ 0 mod m` (`x ↦ ζ_m^{v(x)}`).
* `GW.exists_char_two_pow`: at a finite place `v` above `2`, for every `k` and every `a ∈ K_v^×`, a continuous
  character of `K_v^×` of order exactly `2^k` with `χ(a) = 1`. Proof: `A = K_v^×/K_v^{×2^k}` is finite of order
  `2^k |μ_{2^k}| q^{v(2^k)}` (Tau Ceti `card_powerClasses`); if `A/⟨a⟩` had exponent `< 2^k`, then
  `A^{2^{k-1}} ⊆ ⟨a⟩` would be a group of exponent `2` of order `2 · (|μ_{2^k}|/|μ_{2^{k-1}}|) · q^{v(2)} ≥ 4` inside a cyclic
  group, impossible; a finite abelian group has a character of order its exponent.
* `GW.exists_sign_char`: at a real place, a continuous character of `K_w^× ≅ ℝ^×` of order exactly `2`.
-/

open IsDedekindDomain NumberField ValuativeRel

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.GW

variable {K : Type} [Field K] [NumberField K]

/-- Abstract: a finite quotient with an element of order `N` has a character of order `N`. -/
theorem exists_char_of_quotient {G : Type*} [CommGroup G] (H : Subgroup G) [H.FiniteIndex] {N : ℕ}
    (hN : ∀ g : G, g ^ N ∈ H) (hord : ∃ q : G ⧸ H, orderOf q = N) :
    ∃ χ : G →* ℂˣ, orderOf χ = N ∧ ∀ h ∈ H, χ h = 1 := by
  obtain ⟨q, hq⟩ := hord
  have : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  have : NeZero ((Monoid.exponent (G ⧸ H) : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  have e := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (G ⧸ H) ℂ).some
  have hexp : Monoid.exponent (G ⧸ H) = N := by
    apply Nat.dvd_antisymm
    · apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro g
      induction g using QuotientGroup.induction_on with
      | _ g => rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hN g
    · rw [← hq]; exact Monoid.order_dvd_exponent q
  have : Finite ((G ⧸ H) →* ℂˣ) := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨φ, hφ⟩ := Monoid.exists_orderOf_eq_exponent (G := (G ⧸ H) →* ℂˣ)
    (Monoid.exponent_ne_zero.1 (by rw [Monoid.exponent_eq_of_mulEquiv e]; exact Monoid.exponent_ne_zero_of_finite))
  rw [Monoid.exponent_eq_of_mulEquiv e, hexp] at hφ
  refine ⟨φ.comp (QuotientGroup.mk' H), ?_, ?_⟩
  · rw [← hφ]
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      ext g
      simp only [MonoidHom.pow_apply, MonoidHom.one_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      rw [← MonoidHom.pow_apply, pow_orderOf_eq_one]; rfl
    · apply orderOf_dvd_of_pow_eq_one
      refine MonoidHom.ext fun x => ?_
      induction x using QuotientGroup.induction_on with
      | _ g =>
        exact congrArg (fun f : G →* ℂˣ => f g) (pow_orderOf_eq_one (φ.comp (QuotientGroup.mk' H)))
  · intro h hh
    simp [(QuotientGroup.eq_one_iff h).2 hh]



/-- valuation hom -/
def valHom (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* Multiplicative ℤ :=
  (WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom.comp
    (Units.map (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom)

theorem coe_valHom (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((valHom v x : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = Valued.v (x : v.adicCompletion K) := by
  simp [valHom]

theorem valHom_eq (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) (n : ℤ)
    (h : Valued.v (x : v.adicCompletion K) = WithZero.exp n) : valHom v x = Multiplicative.ofAdd n := by
  have := coe_valHom v x
  rw [h] at this
  have h' : ((valHom v x : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [this]; rfl
  exact WithZero.coe_injective h'

theorem eventually_valHom (v : HeightOneSpectrum (𝓞 K)) :
    ∀ᶠ x in nhds (1 : (v.adicCompletion K)ˣ), valHom v x = 1 := by
  have h1 : {y : v.adicCompletion K | Valued.v (y - 1) < 1} ∈ nhds (1 : v.adicCompletion K) := by
    rw [Valued.mem_nhds]
    exact ⟨1, by simp⟩
  have h2 := (Units.continuous_val.continuousAt (x := (1 : (v.adicCompletion K)ˣ))).eventually_mem
    (by simpa using h1)
  filter_upwards [h2] with x hx
  have : Valued.v (x : v.adicCompletion K) = 1 := by
    have := Valuation.map_one_sub_of_lt (Valued.v : Valuation (v.adicCompletion K) _) (x := 1 - (x : v.adicCompletion K))
      (by rwa [Valuation.map_sub_swap] at hx)
    simpa using this
  have h3 := valHom_eq v x 0 (by simpa using this)
  simpa using h3

open NumberFieldKB.MilneCFT.Ch7 in
theorem natCastValuation_two_pow (v : HeightOneSpectrum (𝓞 K)) (i : ℕ) :
    TauCeti.natCastValuation (v.adicCompletion K) (2 ^ i)
        (natCast_adicCompletion_ne_zero v (by positivity)) =
      i * TauCeti.natCastValuation (v.adicCompletion K) 2
        (natCast_adicCompletion_ne_zero v (by norm_num)) := by
  have h1 := TauCeti.normalizedValuationWithZero_natCast (v.adicCompletion K) (2 ^ i)
    (natCast_adicCompletion_ne_zero v (by positivity))
  have h2 := TauCeti.normalizedValuationWithZero_natCast (v.adicCompletion K) 2
    (natCast_adicCompletion_ne_zero v (by norm_num))
  rw [Nat.cast_pow, map_pow, h2, ← WithZero.exp_nsmul] at h1
  have := WithZero.exp_injective h1
  simp only [nsmul_eq_mul] at this
  exact_mod_cast this.symm

open NumberFieldKB.MilneCFT.Ch7 in
theorem natCastValuation_two_pos (v : HeightOneSpectrum (𝓞 K)) (hv : (2 : 𝓞 K) ∈ v.asIdeal) :
    0 < TauCeti.natCastValuation (v.adicCompletion K) 2
        (natCast_adicCompletion_ne_zero v (by norm_num)) := by
  have h1 := TauCeti.normalizedValuationWithZero_natCast (v.adicCompletion K) 2
    (natCast_adicCompletion_ne_zero v (by norm_num))
  rw [HeightOneSpectrum.normalizedValuationWithZero_adicCompletion] at h1
  have h2 : (Valued.v ((2 : ℕ) : v.adicCompletion K) : WithZero (Multiplicative ℤ)) =
      v.intValuation ((2 : ℕ) : 𝓞 K) := by
    rw [← map_natCast (algebraMap K (v.adicCompletion K)) 2, HeightOneSpectrum.algebraMap_adicCompletion,
      Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      Algebra.algebraMap_self_apply, ← map_natCast (algebraMap (𝓞 K) K),
      HeightOneSpectrum.valuation_of_algebraMap]
  have h3 : v.intValuation ((2 : ℕ) : 𝓞 K) < 1 := by
    rw [v.intValuation_lt_one_iff_mem]; simpa using hv
  rw [h2] at h1
  by_contra hcon
  have h0 : TauCeti.natCastValuation (v.adicCompletion K) 2
        (natCast_adicCompletion_ne_zero v (by norm_num)) = 0 := by omega
  rw [h0] at h1
  have h4 := inv_eq_one.1 (h1.trans (by simp))
  rw [h4] at h3
  exact lt_irrefl _ h3

open NumberFieldKB.MilneCFT.Ch7 in
theorem card_two_pow_classes (v : HeightOneSpectrum (𝓞 K)) (i : ℕ) :
    haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    (powMonoidHom (2 ^ i) : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index =
      2 ^ i * Nat.card (rootsOfUnity (2 ^ i) (v.adicCompletion K)) *
        Nat.card 𝓀[v.adicCompletion K] ^
          (i * TauCeti.natCastValuation (v.adicCompletion K) 2
            (natCast_adicCompletion_ne_zero v (by norm_num))) := by
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  rw [Subgroup.index_eq_card, TauCeti.card_powerClasses
    (natCast_adicCompletion_ne_zero v (n := 2 ^ i) (by positivity)), natCastValuation_two_pow]

open NumberFieldKB.MilneCFT.Ch7 in
theorem not_forall_pow_mem (v : HeightOneSpectrum (𝓞 K)) (hv : (2 : 𝓞 K) ∈ v.asIdeal) (j : ℕ)
    (a : (v.adicCompletion K)ˣ) :
    ¬ ∀ g : (v.adicCompletion K)ˣ, g ^ (2 ^ j) ∈ Subgroup.zpowers a ⊔
      (powMonoidHom (2 ^ (j + 1)) : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range := by
  intro hall
  let P2 := (powMonoidHom (2 ^ (j + 1)) : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range
  let R := (powMonoidHom (2 ^ j) : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range
  have hPR : P2 ≤ R := by
    rintro _ ⟨g, rfl⟩
    refine ⟨g ^ 2, ?_⟩
    show (g ^ 2) ^ (2 ^ j) = g ^ (2 ^ (j + 1))
    rw [← pow_mul, pow_succ, mul_comm]
  have hRH : R ≤ Subgroup.zpowers a ⊔ P2 := by
    rintro _ ⟨g, rfl⟩
    exact hall g
  let π := QuotientGroup.mk' P2
  let R' := R.map π
  have hR'le : R' ≤ Subgroup.zpowers (π a) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 (hRH hx)
    have hz1 : π z = 1 := (QuotientGroup.eq_one_iff z).2 hz
    have : π x = π y := by rw [← hyz, map_mul, hz1]; exact mul_one (π y)
    rw [this]
    obtain ⟨i, rfl⟩ := hy
    exact ⟨i, by simp⟩
  haveI : IsCyclic R' := Subgroup.isCyclic_of_le hR'le
  have hdvd : Nat.card R' ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨_, x, ⟨g, rfl⟩, rfl⟩
    apply Subtype.ext
    show (π (g ^ (2 ^ j))) ^ 2 = 1
    rw [← map_pow, ← pow_mul, ← pow_succ]
    exact (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
  have hle : Nat.card R' ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hidx : R'.index = R.index := by
    rw [Subgroup.index_map, QuotientGroup.ker_mk', sup_eq_left.2 hPR]
    simp [π]
  have hmul : Nat.card R' * R.index = P2.index := by
    rw [← hidx, Subgroup.card_mul_index, Subgroup.index_eq_card]
  have e2 := card_two_pow_classes v (j + 1)
  have e1 := card_two_pow_classes v j
  have hs := natCastValuation_two_pos v hv
  have hq : 1 < Nat.card 𝓀[v.adicCompletion K] := Finite.one_lt_card
  have hm : Nat.card (rootsOfUnity (2 ^ j) (v.adicCompletion K)) ≤
      Nat.card (rootsOfUnity (2 ^ (j + 1)) (v.adicCompletion K)) :=
    Subgroup.card_le_of_le (rootsOfUnity_le_of_dvd (pow_dvd_pow 2 (Nat.le_succ j)))
  have hm0 : 0 < Nat.card (rootsOfUnity (2 ^ j) (v.adicCompletion K)) := Nat.card_pos
  generalize Nat.card (rootsOfUnity (2 ^ j) (v.adicCompletion K)) = m1 at *
  generalize Nat.card (rootsOfUnity (2 ^ (j + 1)) (v.adicCompletion K)) = m2 at *
  generalize Nat.card 𝓀[v.adicCompletion K] = qq at *
  generalize TauCeti.natCastValuation (v.adicCompletion K) 2
            (natCast_adicCompletion_ne_zero v (by norm_num)) = s at *
  have h1 : R.index = 2 ^ j * m1 * qq ^ (j * s) := e1
  have h2 : P2.index = 2 ^ (j + 1) * m2 * qq ^ ((j + 1) * s) := e2
  rw [h1, h2] at hmul
  generalize Nat.card R' = c at *
  have hX : 2 ≤ qq ^ s := le_trans hq (Nat.le_self_pow hs.ne' qq)
  have hpow : qq ^ ((j + 1) * s) = qq ^ (j * s) * qq ^ s := by rw [add_mul, one_mul, pow_add]
  rw [hpow, pow_succ] at hmul
  have hT : 0 < qq ^ (j * s) := pow_pos (by omega) _
  have hW : 0 < 2 ^ j := by positivity
  generalize qq ^ (j * s) = T at *
  generalize qq ^ s = X at *
  generalize 2 ^ j = W at *
  have h3 : c * (W * m1 * T) ≤ 2 * (W * m1 * T) := Nat.mul_le_mul_right _ hle
  have h4 : (2 * W * T) * (m2 * X) ≤ (2 * W * T) * m1 := by nlinarith
  have h5 := Nat.le_of_mul_le_mul_left h4 (by positivity)
  nlinarith

/-- The sign character of `ℝˣ`. -/
def signHomR : ℝˣ →* ℂˣ where
  toFun x := if 0 < (x : ℝ) then 1 else -1
  map_one' := by simp
  map_mul' x y := by
    have hx := x.ne_zero
    have hy := y.ne_zero
    rcases lt_or_gt_of_ne hx with hx' | hx' <;> rcases lt_or_gt_of_ne hy with hy' | hy'
    · have : 0 < (x : ℝ) * y := by nlinarith
      simp [not_lt.2 hx'.le, not_lt.2 hy'.le, this]
    · have : ¬ 0 < (x : ℝ) * y := by nlinarith
      simp [not_lt.2 hx'.le, hy', this]
    · have : ¬ 0 < (x : ℝ) * y := by nlinarith
      simp [hx', not_lt.2 hy'.le, this]
    · simp [hx', hy', mul_pos hx' hy']

theorem continuous_signHomR : Continuous signHomR := by
  apply continuous_of_continuousAt_one
  have : Filter.EventuallyEq (nhds (1 : ℝˣ)) (fun _ => signHomR 1) signHomR := by
    have h : ∀ᶠ x : ℝˣ in nhds (1 : ℝˣ), (0 : ℝ) < (x : ℝ) :=
      (Units.continuous_val.continuousAt (x := (1 : ℝˣ))).eventually_mem
        (Ioi_mem_nhds (show (0 : ℝ) < ((1 : ℝˣ) : ℝ) by simp))
    filter_upwards [h] with x hx
    simp [signHomR, hx]
  exact tendsto_const_nhds.congr' this

/-- **Unramified characters of order `m`.** -/
theorem exists_unramified_char (v : HeightOneSpectrum (𝓞 K)) {m : ℕ} (hm : 0 < m) :
    ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ, Continuous χ ∧ orderOf χ = m ∧
      ∀ x : (v.adicCompletion K)ˣ, (∃ k : ℤ, Valued.v (x : v.adicCompletion K) = WithZero.exp ((m : ℤ) * k)) →
        χ x = 1 := by
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / m)) m :=
    Complex.isPrimitiveRoot_exp m hm.ne'
  set z := Complex.exp (2 * Real.pi * Complex.I / m)
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  set ζ : ℂˣ := Units.mk0 z hz0
  have hζ : IsPrimitiveRoot ζ m :=
    IsPrimitiveRoot.of_map_of_injective (f := Units.coeHom ℂ) (by simpa [ζ] using hz)
      (fun a b h => Units.ext h)
  let χ : (v.adicCompletion K)ˣ →* ℂˣ := (zpowersHom ℂˣ ζ).comp (valHom v)
  have hχ : ∀ x, χ x = ζ ^ (Multiplicative.toAdd (valHom v x)) := fun x => rfl
  have hker : ∀ x : (v.adicCompletion K)ˣ,
      (∃ k : ℤ, Valued.v (x : v.adicCompletion K) = WithZero.exp ((m : ℤ) * k)) → χ x = 1 := by
    rintro x ⟨k, hk⟩
    rw [hχ, valHom_eq v x _ hk, toAdd_ofAdd, zpow_mul]
    simp [hζ.pow_eq_one]
  refine ⟨χ, ?_, ?_, hker⟩
  · apply continuous_of_continuousAt_one
    have : Filter.EventuallyEq (nhds (1 : (v.adicCompletion K)ˣ)) (fun _ => χ 1) χ := by
      filter_upwards [eventually_valHom v] with x hx
      have h1 : χ x = 1 := by rw [hχ, hx]; simp
      rw [h1, map_one]
    exact (tendsto_const_nhds.congr' this)
  · apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      ext x
      simp only [MonoidHom.pow_apply, MonoidHom.one_apply, hχ]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [hζ.pow_eq_one]
    · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
      have hv : Valued.v ((π : K) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ
      have hne : ((π : K) : v.adicCompletion K) ≠ 0 := by
        intro h; rw [h, map_zero] at hv; exact (WithZero.exp_ne_zero) hv.symm
      have hu := valHom_eq v (Units.mk0 _ hne) (-1) (by simpa using hv)
      have h1 : χ (Units.mk0 _ hne) = ζ ^ (-1 : ℤ) := by rw [hχ, hu]; simp
      have h2 : (χ (Units.mk0 _ hne)) ^ (orderOf χ) = 1 := by
        rw [← MonoidHom.pow_apply, pow_orderOf_eq_one]; rfl
      rw [h1, ← zpow_natCast, ← zpow_mul] at h2
      have h3 : ζ ^ ((orderOf χ : ℤ)) = 1 := by
        have := congrArg (fun t => t⁻¹) h2
        simpa [mul_comm, zpow_neg] using this
      rw [zpow_natCast] at h3
      exact hζ.dvd_of_pow_eq_one _ h3

open NumberFieldKB.MilneCFT.Ch7 in
/-- **Characters of order `2^k` killing a given element, at a place above `2`.** -/
theorem exists_char_two_pow (v : HeightOneSpectrum (𝓞 K)) (hv : (2 : 𝓞 K) ∈ v.asIdeal) (k : ℕ)
    (a : (v.adicCompletion K)ˣ) :
    ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ, Continuous χ ∧ orderOf χ = 2 ^ k ∧ χ a = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, continuous_const, by simp, by simp⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  let P := (powMonoidHom (2 ^ (j + 1)) : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range
  have hPfin : P.FiniteIndex := by
    haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    refine ⟨?_⟩
    have h := card_two_pow_classes v (j + 1)
    have h1 : P.index = _ := h
    rw [h1]
    have : 0 < Nat.card (rootsOfUnity (2 ^ (j + 1)) (v.adicCompletion K)) := Nat.card_pos
    have : 0 < Nat.card 𝓀[v.adicCompletion K] := Nat.card_pos
    positivity
  let H : Subgroup (v.adicCompletion K)ˣ := Subgroup.zpowers a ⊔ P
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_le (le_sup_right : P ≤ H)
  have hPle : P ≤ H := le_sup_right
  have haH : a ∈ H := (le_sup_left : Subgroup.zpowers a ≤ H) (Subgroup.mem_zpowers a)
  have hPH : ∀ g : (v.adicCompletion K)ˣ, g ^ (2 ^ (j + 1)) ∈ H :=
    fun g => hPle (⟨g, rfl⟩ : g ^ (2 ^ (j + 1)) ∈ P)
  have hex : ∃ q : (v.adicCompletion K)ˣ ⧸ H, orderOf q = 2 ^ (j + 1) := by
    haveI : Finite ((v.adicCompletion K)ˣ ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
    obtain ⟨q, hq⟩ := Monoid.exists_orderOf_eq_exponent
      (G := (v.adicCompletion K)ˣ ⧸ H) (Monoid.ExponentExists.of_finite (G := (v.adicCompletion K)ˣ ⧸ H))
    have hdvd : Monoid.exponent ((v.adicCompletion K)ˣ ⧸ H) ∣ 2 ^ (j + 1) := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro g
      induction g using QuotientGroup.induction_on with
      | _ g => rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hPH g
    obtain ⟨i, hi, hE⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rcases hi.lt_or_eq with hlt | heq
    · exfalso
      apply not_forall_pow_mem v hv j a
      intro g
      have hd : Monoid.exponent ((v.adicCompletion K)ˣ ⧸ H) ∣ 2 ^ j := by
        rw [hE]; exact pow_dvd_pow 2 (by omega)
      have h1 : ((g : (v.adicCompletion K)ˣ ⧸ H)) ^ (2 ^ j) = 1 := by
        obtain ⟨t, ht⟩ := hd
        rw [ht, pow_mul, Monoid.pow_exponent_eq_one, one_pow]
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
      exact h1
    · exact ⟨q, by rw [hq, hE, heq]⟩
  obtain ⟨χ, hord, hker⟩ := exists_char_of_quotient H hPH hex
  refine ⟨χ, ?_, hord, hker a haH⟩
  apply continuous_of_continuousAt_one
  have hopen : IsOpen (P : Set (v.adicCompletion K)ˣ) :=
    TauCeti.isOpen_range_powMonoidHom (natCast_adicCompletion_ne_zero v (by positivity))
  have : Filter.EventuallyEq (nhds (1 : (v.adicCompletion K)ˣ)) (fun _ => χ 1) χ := by
    filter_upwards [hopen.mem_nhds P.one_mem] with x hx
    rw [hker x (hPle hx), map_one]
  exact tendsto_const_nhds.congr' this

/-- **The sign character at a real place.** -/
theorem exists_sign_char (w : InfinitePlace K) (hw : w.IsReal) :
    ∃ χ : w.Completionˣ →* ℂˣ, Continuous χ ∧ orderOf χ = 2 := by
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
  have hhomeo : Continuous e := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).continuous
  let f : w.Completionˣ →* ℂˣ := signHomR.comp (Units.map e.toMonoidHom)
  have hcont : Continuous f := continuous_signHomR.comp (Units.continuous_map hhomeo)
  refine ⟨f, hcont, orderOf_eq_prime ?_ ?_⟩
  · ext x
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, f, MonoidHom.comp_apply]
    simp only [signHomR, MonoidHom.coe_mk, OneHom.coe_mk]
    split_ifs <;> simp
  · intro h
    have := congrArg (fun g : w.Completionˣ →* ℂˣ => g (Units.map e.symm.toMonoidHom (-1))) h
    simp [f, signHomR] at this

end NumberFieldKB.MilneCFT.Ch8.GW
