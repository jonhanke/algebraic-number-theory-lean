import NumberFieldKB.MilneCFT.Ch5ConductorUncond
import NumberFieldKB.MilneCFT.Ch5Characters
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.Ramification
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic

/-!
# Milne, *Class Field Theory*, Chapter V, §3, p. 165: primitive characters, unconditional

`primitiveCharacters`: every class of cotrained Dirichlet characters contains a unique primitive character.

The proof is by descent: if $\chi$ (on $I^S$, trivial on $K_{\mathfrak m,1}$) and $\chi'$ (on $I^{S'}$, trivial on
$K_{\mathfrak m',1}$) agree on $I^{S''}$, they are both pulled back from a character $\xi$ of $C_\mathfrak g$,
$\mathfrak g = \gcd(\mathfrak m,\mathfrak m')$ (`exists_descent`).  This rests on
* a weak approximation lemma with prescribed congruences, valuations and signs (`chr_approx`),
* `chr_surj`: every class of $C_\mathfrak m$ has a representative in $I^{S''}$ for any finite $S''$,
* `chr_split`: an element $a\in K_{\mathfrak g,1}$ prime to $S''$ is a product $bc$ with $b\in K_{\mathfrak m,1}$,
  $c\in K_{\mathfrak m',1}$, both prime to $S''$.
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-! ## Weak approximation with congruences and signs -/

theorem chr_exp_le_of_lt {x : WithZero (Multiplicative ℤ)} {n : ℤ} (h : x < WithZero.exp (n + 1)) :
    x ≤ WithZero.exp n := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]; omega

theorem chr_approx (P : Finset (HeightOneSpectrum (𝓞 K))) (t : HeightOneSpectrum (𝓞 K) → K)
    (k : HeightOneSpectrum (𝓞 K) → ℕ)
    (ht : ∀ v ∈ P, WithZero.exp (-(k v : ℤ)) < v.valuation K (t v)) (Θ : Finset (InfinitePlace K))
    (e : InfinitePlace K → ℝ) (he : ∀ w, e w ≠ 0) :
    ∃ b : K, b ≠ 0 ∧ (∀ v ∈ P, v.valuation K (b - t v) ≤ WithZero.exp (-(k v : ℤ))) ∧
      ∀ w ∈ Θ, ∀ hw : w.IsReal, 0 < InfinitePlace.embedding_of_isReal hw b * e w := by
  classical
  set q : InfinitePlace K → K := fun w => if 0 < e w then 2 else -2 with hq
  obtain ⟨b, hb1, hb2⟩ := exists_approx P Θ t (fun v => WithZero.exp (-(k v : ℤ) + 1))
    (fun _ _ => WithZero.exp_ne_zero) q
  have hv : ∀ v ∈ P, v.valuation K (b - t v) ≤ WithZero.exp (-(k v : ℤ)) :=
    fun v hv => chr_exp_le_of_lt (hb1 v hv)
  have hs : ∀ w ∈ Θ, ∀ hw : w.IsReal, 0 < InfinitePlace.embedding_of_isReal hw b * e w := by
    intro w hwΘ hw
    have h1 := hb2 w hwΘ
    rw [← InfinitePlace.norm_embedding_of_isReal hw, map_sub, Real.norm_eq_abs, abs_lt] at h1
    by_cases hp : 0 < e w
    · simp only [hq, if_pos hp, map_ofNat] at h1
      exact mul_pos (by linarith [h1.1]) hp
    · have hn : e w < 0 := lt_of_le_of_ne (not_lt.1 hp) (he w)
      simp only [hq, if_neg hp, map_neg, map_ofNat] at h1
      exact mul_pos_of_neg_of_neg (by linarith [h1.2]) hn
  by_cases hb0 : b = 0
  · refine ⟨1, one_ne_zero, fun v hvP => ?_, fun w hwΘ hw => ?_⟩
    · exfalso
      have := hv v hvP
      rw [hb0, zero_sub, Valuation.map_neg] at this
      exact absurd (ht v hvP) (not_lt.2 this)
    · exfalso
      have := hs w hwΘ hw
      rw [hb0, map_zero, zero_mul] at this
      exact lt_irrefl _ this
  · exact ⟨b, hb0, hv, hs⟩

/-! ## Representatives prime to a finite set -/

/-- Every class of $C_\mathfrak m$ has a representative in $I^{S''}$ for any finite $S''\supseteq S(\mathfrak m)$: for
$J\in I^{S(\mathfrak m)}$ there is $a\in K_{\mathfrak m,1}$ with $(a)J\in I^{S''}$. -/
theorem chr_surj (m : Modulus K) (S'' : Set (HeightOneSpectrum (𝓞 K))) (hS'' : S''.Finite)
    (hsub : m.finiteSupport ⊆ S'') (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hJ : J ∈ coprimeIdeals m) :
    ∃ a : Kˣ, a ∈ congruenceSubgroup m ∧ toPrincipalIdeal (𝓞 K) K a * J ∈ sIdeals S'' := by
  classical
  choose π hπ using fun v : HeightOneSpectrum (𝓞 K) => v.valuation_exists_uniformizer K
  let n : HeightOneSpectrum (𝓞 K) → ℤ := fun v => FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)
  let t : HeightOneSpectrum (𝓞 K) → K := fun v => if v ∈ m.finiteSupport then 1 else (π v) ^ (-(n v))
  let k : HeightOneSpectrum (𝓞 K) → ℕ := fun v =>
    if v ∈ m.finiteSupport then m.ord v else (-(n v)).toNat + 1
  have hπ0 : ∀ v, π v ≠ 0 := fun v h => by
    have := hπ v
    rw [h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have hval : ∀ v, v.valuation K ((π v) ^ (-(n v))) = WithZero.exp (n v) := by
    intro v
    rw [map_zpow₀, hπ v, ← WithZero.exp_zsmul]
    congr 1; simp
  have ht : ∀ v ∈ hS''.toFinset, WithZero.exp (-(k v : ℤ)) < v.valuation K (t v) := by
    intro v _
    by_cases hv : v ∈ m.finiteSupport
    · simp only [t, k, if_pos hv, map_one]
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      have := one_le_ord m v hv
      omega
    · simp only [t, k, if_neg hv]
      rw [hval, WithZero.exp_lt_exp]
      omega
  obtain ⟨a, ha0, ha1, ha2⟩ := chr_approx hS''.toFinset t k ht
    ((Set.toFinite m.infinite).toFinset) (fun _ => 1) (fun _ => one_ne_zero)
  have hv : ∀ v ∈ S'', v.valuation K a = v.valuation K (t v) := by
    intro v hvS
    have h1 := ha1 v (hS''.mem_toFinset.2 hvS)
    have h2 := ht v (hS''.mem_toFinset.2 hvS)
    have : v.valuation K (a - t v) < v.valuation K (t v) := h1.trans_lt h2
    exact Valuation.map_eq_of_sub_lt (v.valuation K) (x := t v) (y := a) this
  refine ⟨Units.mk0 a ha0, ⟨fun w hw => ?_, fun v hvm => ?_⟩, ?_⟩
  · have := ha2 w ((Set.toFinite m.infinite).mem_toFinset.2 hw) (m.isReal_of_mem w hw)
    unfold IsPositiveAt
    simpa using this
  · have hvS : v ∈ m.finiteSupport := hvm
    have := ha1 v (hS''.mem_toFinset.2 (hsub hvS))
    simpa [t, k, hvS] using this
  · intro v hvS
    have hJv : FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) = n v := rfl
    show FractionalIdeal.count K v ((toPrincipalIdeal (𝓞 K) K (Units.mk0 a ha0) * J :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = 0
    rw [Units.val_mul, FractionalIdeal.count_mul K v (Units.ne_zero _) J.ne_zero]
    have e1 := valuation_eq_exp_neg_count v (Units.mk0 a ha0)
    rw [Units.val_mk0, hv v hvS] at e1
    by_cases hm : v ∈ m.finiteSupport
    · have : n v = 0 := hJ v hm
      simp only [t, if_pos hm, map_one] at e1
      rw [← WithZero.exp_zero, WithZero.exp_inj] at e1
      rw [hJv, this]
      have : (FractionalIdeal.count K v (toPrincipalIdeal (𝓞 K) K (Units.mk0 a ha0) :
          FractionalIdeal (𝓞 K)⁰ K) : ℤ) = 0 := by omega
      omega
    · simp only [t, if_neg hm] at e1
      rw [hval, WithZero.exp_inj] at e1
      rw [hJv]
      omega

/-! ## Splitting an element of $K_{\gcd,1}$ -/

theorem chr_sub_le {R : Type*} [Field R] (v : Valuation R (WithZero (Multiplicative ℤ))) {x z : R} (y : R)
    {γ : WithZero (Multiplicative ℤ)} (h1 : v (x - y) ≤ γ) (h2 : v (y - z) ≤ γ) : v (x - z) ≤ γ := by
  have : x - z = (x - y) + (y - z) := by ring
  rw [this]; exact (Valuation.map_add _ _ _).trans (max_le h1 h2)

theorem chr_val_one_of_mem {S : Set (HeightOneSpectrum (𝓞 K))} {a : Kˣ}
    (ha : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) :
    v.valuation K (a : K) = 1 := by
  rw [valuation_eq_exp_neg_count v a, ha v hv]; simp

theorem chr_mem_of_val_one {S : Set (HeightOneSpectrum (𝓞 K))} {a : Kˣ}
    (h : ∀ v ∈ S, v.valuation K (a : K) = 1) : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S := by
  intro v hv
  have h' := valuation_eq_exp_neg_count v a
  rw [h v hv, eq_comm, ← WithZero.exp_zero, WithZero.exp_inj] at h'
  omega

theorem chr_split (m m' : Modulus K) (S'' : Set (HeightOneSpectrum (𝓞 K))) (hS'' : S''.Finite)
    (hsub : m.finiteSupport ∪ m'.finiteSupport ⊆ S'') (a : Kˣ)
    (ha : a ∈ congruenceSubgroup (Modulus.gcd m m')) (haS : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S'') :
    ∃ b c : Kˣ, a = b * c ∧ b ∈ congruenceSubgroup m ∧ c ∈ congruenceSubgroup m' ∧
      toPrincipalIdeal (𝓞 K) K b ∈ sIdeals S'' ∧ toPrincipalIdeal (𝓞 K) K c ∈ sIdeals S'' := by
  classical
  let t : HeightOneSpectrum (𝓞 K) → K := fun v => if m'.ord v ≤ m.ord v then 1 else (a : K)
  let k : HeightOneSpectrum (𝓞 K) → ℕ := fun v => max (max (m.ord v) (m'.ord v)) 1
  have hk1 : ∀ v, m.ord v ≤ k v := fun v => (le_max_left _ _).trans (le_max_left _ _)
  have hk2 : ∀ v, m'.ord v ≤ k v := fun v => (le_max_right _ _).trans (le_max_left _ _)
  have hk3 : ∀ v, 1 ≤ k v := fun v => le_max_right _ _
  have hlt1 : ∀ v : HeightOneSpectrum (𝓞 K), ∀ n : ℕ, 1 ≤ n → (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) < 1 := by
    intro v n hn
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have ht : ∀ v ∈ hS''.toFinset, WithZero.exp (-(k v : ℤ)) < v.valuation K (t v) := by
    intro v hv
    have hv' := hS''.mem_toFinset.1 hv
    have : v.valuation K (t v) = 1 := by
      by_cases h : m'.ord v ≤ m.ord v
      · simp [t, h]
      · simp only [t, if_neg h]; exact chr_val_one_of_mem haS hv'
    rw [this]; exact hlt1 v _ (hk3 v)
  let e : InfinitePlace K → ℝ := fun w =>
    if hw : w.IsReal then (if w ∈ m.infinite then 1 else InfinitePlace.embedding_of_isReal hw (a : K)) else 1
  have he : ∀ w, e w ≠ 0 := by
    intro w
    by_cases hw : w.IsReal
    · by_cases hm : w ∈ m.infinite
      · simp [e, hw, hm]
      · simp only [e, dif_pos hw, if_neg hm]
        exact (map_ne_zero _).2 a.ne_zero
    · simp [e, hw]
  obtain ⟨b0, hb0, hb1, hb2⟩ := chr_approx hS''.toFinset t k ht
    ((Set.toFinite (m.infinite ∪ m'.infinite)).toFinset) e he
  have hbv : ∀ v ∈ S'', v.valuation K b0 = 1 := by
    intro v hv
    have h1 := hb1 v (hS''.mem_toFinset.2 hv)
    have h2 := ht v (hS''.mem_toFinset.2 hv)
    have h3 : v.valuation K (t v) = 1 := by
      by_cases h : m'.ord v ≤ m.ord v
      · simp [t, h]
      · simp only [t, if_neg h]; exact chr_val_one_of_mem haS hv
    have h4 : v.valuation K (b0 - t v) < v.valuation K (t v) := h1.trans_lt h2
    have := Valuation.map_eq_of_sub_lt (v.valuation K) (x := t v) (y := b0) h4
    rw [this, h3]
  set b : Kˣ := Units.mk0 b0 hb0 with hb
  have hbS : toPrincipalIdeal (𝓞 K) K b ∈ sIdeals S'' := chr_mem_of_val_one fun v hv => hbv v hv
  have hcS : toPrincipalIdeal (𝓞 K) K (a * b⁻¹) ∈ sIdeals S'' := by
    rw [map_mul, map_inv]; exact (sIdeals S'').mul_mem haS ((sIdeals S'').inv_mem hbS)
  refine ⟨b, a * b⁻¹, by rw [mul_comm a b⁻¹, ← mul_assoc, mul_inv_cancel, one_mul], ?_, ?_, hbS, hcS⟩
  · refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · have hr := m.isReal_of_mem w hw
      have h := hb2 w (by simp [hw]) hr
      have he1 : e w = 1 := by simp [e, hr, hw]
      rw [he1, mul_one] at h
      exact h
    · have hvS : v ∈ S'' := hsub (Or.inl hv)
      have h1 := hb1 v (hS''.mem_toFinset.2 hvS)
      show v.valuation K (b0 - 1) ≤ _
      by_cases h : m'.ord v ≤ m.ord v
      · simp only [t, if_pos h] at h1
        exact h1.trans (WithZero.exp_le_exp.2 (by have := hk1 v; omega))
      · simp only [t, if_neg h] at h1
        have hlt : m.ord v ≤ m'.ord v := by omega
        obtain ⟨hvg, hog⟩ := Modulus.gcd_aux hv hlt
        have h2 := ha.2 v hvg
        refine chr_sub_le (v.valuation K) (y := (a : K)) (h1.trans (WithZero.exp_le_exp.2 ?_))
          (h2.trans (WithZero.exp_le_exp.2 ?_))
        · have := hk1 v; omega
        · omega
  · refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · have hr := m'.isReal_of_mem w hw
      have hbpos : ∀ hm : w ∈ m.infinite, 0 < InfinitePlace.embedding_of_isReal hr b0 := by
        intro hm
        have h := hb2 w (by simp [hm]) hr
        have he1 : e w = 1 := by simp [e, hr, hm]
        rw [he1, mul_one] at h
        exact h
      have hb0ne : InfinitePlace.embedding_of_isReal hr b0 ≠ 0 := by simpa using hb0
      unfold IsPositiveAt
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
      show 0 < InfinitePlace.embedding_of_isReal (m'.isReal_of_mem w hw) (a : K) *
        (InfinitePlace.embedding_of_isReal (m'.isReal_of_mem w hw) b0)⁻¹
      by_cases hm : w ∈ m.infinite
      · have hapos := ha.1 w ⟨hm, hw⟩
        unfold IsPositiveAt at hapos
        exact mul_pos hapos (inv_pos.2 (hbpos hm))
      · have h := hb2 w (by simp [hw]) hr
        have he1 : e w = InfinitePlace.embedding_of_isReal hr (a : K) := by simp [e, hr, hm]
        rw [he1] at h
        have : InfinitePlace.embedding_of_isReal hr (a : K) * (InfinitePlace.embedding_of_isReal hr b0)⁻¹ =
            (InfinitePlace.embedding_of_isReal hr b0 * InfinitePlace.embedding_of_isReal hr (a : K)) *
              ((InfinitePlace.embedding_of_isReal hr b0)⁻¹) ^ 2 := by
          field_simp
        rw [this]
        positivity
    · have hvS : v ∈ S'' := hsub (Or.inr hv)
      have h1 := hb1 v (hS''.mem_toFinset.2 hvS)
      have hcm1 : ((a * b⁻¹ : Kˣ) : K) - 1 = ((a : K) - b0) * b0⁻¹ := by
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, hb, Units.val_mk0]
        field_simp
      rw [hcm1, map_mul, map_inv₀, hbv v hvS, inv_one, mul_one]
      by_cases h : m'.ord v ≤ m.ord v
      · simp only [t, if_pos h] at h1
        obtain ⟨hvg, hog⟩ := Modulus.gcd_aux' hv h
        have h2 := ha.2 v hvg
        refine chr_sub_le (v.valuation K) (y := 1) (h2.trans (WithZero.exp_le_exp.2 ?_)) ?_
        · omega
        · rw [Valuation.map_sub_swap]
          exact h1.trans (WithZero.exp_le_exp.2 (by have := hk2 v; omega))
      · simp only [t, if_neg h] at h1
        rw [Valuation.map_sub_swap]
        exact h1.trans (WithZero.exp_le_exp.2 (by have := hk2 v; omega))

/-! ## Descent of cotrained Dirichlet characters to the gcd -/

theorem chr_gcd_support_subset_left (m m' : Modulus K) :
    (Modulus.gcd m m').finiteSupport ⊆ m.finiteSupport := fun v hv =>
  Ideal.dvd_iff_le.2 (le_sup_left.trans (Ideal.dvd_iff_le.1 hv))

theorem chr_gcd_support_subset_right (m m' : Modulus K) :
    (Modulus.gcd m m').finiteSupport ⊆ m'.finiteSupport := fun v hv =>
  Ideal.dvd_iff_le.2 (le_sup_right.trans (Ideal.dvd_iff_le.1 hv))

theorem chr_descent {S S' S'' : Set (HeightOneSpectrum (𝓞 K))} (hS'' : S''.Finite) (hsub : S ∪ S' ⊆ S'')
    (m m' : Modulus K) (hm : m.finiteSupport = S) (hm' : m'.finiteSupport = S')
    (χ : sIdeals S →* ℂˣ) (χ' : sIdeals S' →* ℂˣ)
    (hχ : ∀ a : Kˣ, a ∈ congruenceSubgroup m → ∀ h : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S, χ ⟨_, h⟩ = 1)
    (hχ' : ∀ a : Kˣ, a ∈ congruenceSubgroup m' → ∀ h : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S', χ' ⟨_, h⟩ = 1)
    (hagree : ∀ a ∈ sIdeals S'', ∀ (h : a ∈ sIdeals S) (h' : a ∈ sIdeals S'), χ ⟨a, h⟩ = χ' ⟨a, h'⟩) :
    ∃ (T : Set (HeightOneSpectrum (𝓞 K))) (_ : T ⊆ S) (_ : T ⊆ S') (_ : ∀ v, v ∈ S → v ∈ S' → v ∈ T)
      (ξ : sIdeals T →* ℂˣ), (∃ g : Modulus K, g.finiteSupport = T ∧
        ∀ a : Kˣ, a ∈ congruenceSubgroup g → ∀ h : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals T, ξ ⟨_, h⟩ = 1) ∧
      ∀ a ∈ sIdeals S'', ∀ (h : a ∈ sIdeals S) (h' : a ∈ sIdeals T), χ ⟨a, h⟩ = ξ ⟨a, h'⟩ := by
  classical
  set g := Modulus.gcd m m' with hg
  have hSS : S ⊆ S'' := Set.subset_union_left.trans hsub
  have hS'S : S' ⊆ S'' := Set.subset_union_right.trans hsub
  have hgS'' : g.finiteSupport ⊆ S'' := fun v hv => hSS (hm ▸ chr_gcd_support_subset_left m m' hv)
  have hincl : sIdeals S'' ≤ sIdeals S := fun _ hI v hv => hI v (hSS hv)
  set φ : sIdeals S'' →* ℂˣ := χ.comp (Subgroup.inclusion hincl) with hφ
  set ι := sIdealsToRay g S'' hgS'' with hι
  have hsurj : Function.Surjective ι := by
    intro c
    induction c using QuotientGroup.induction_on with | H J => ?_
    obtain ⟨a, ha, haJ⟩ := chr_surj g S'' hS'' hgS'' J.1 J.2
    refine ⟨⟨toPrincipalIdeal (𝓞 K) K a * J.1, haJ⟩, ?_⟩
    show (QuotientGroup.mk _ : RayClassGroup g) = QuotientGroup.mk J
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine ⟨a⁻¹, (congruenceSubgroup g).inv_mem ha, ?_⟩
    show _ = (toPrincipalIdeal (𝓞 K) K a * J.1)⁻¹ * J.1
    rw [map_inv, mul_inv_rev, mul_comm (J.1⁻¹), mul_assoc, inv_mul_cancel, mul_one]
  have hker : ι.ker ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [MonoidHom.mem_ker]
    simp only [hι, sIdealsToRay, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hx
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    obtain ⟨a, ha, hax⟩ := hx
    have haS : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S'' := by
      rw [show toPrincipalIdeal (𝓞 K) K a = (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) from hax]
      exact x.2
    obtain ⟨b, c, habc, hb, hc, hbS, hcS⟩ :=
      chr_split m m' S'' hS'' (by rw [hm, hm']; exact hsub) a ha haS
    have hbS' : toPrincipalIdeal (𝓞 K) K b ∈ sIdeals S := hincl hbS
    have hcS' : toPrincipalIdeal (𝓞 K) K c ∈ sIdeals S := hincl hcS
    have hcS'' : toPrincipalIdeal (𝓞 K) K c ∈ sIdeals S' := fun v hv => hcS v (hS'S hv)
    have hxe : (⟨(x : (FractionalIdeal (𝓞 K)⁰ K)ˣ), hincl x.2⟩ : sIdeals S) =
        ⟨toPrincipalIdeal (𝓞 K) K b, hbS'⟩ * ⟨toPrincipalIdeal (𝓞 K) K c, hcS'⟩ := by
      refine Subtype.ext ?_
      show (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = toPrincipalIdeal (𝓞 K) K b * toPrincipalIdeal (𝓞 K) K c
      rw [show (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = toPrincipalIdeal (𝓞 K) K a from hax.symm, habc, map_mul]
    show χ ⟨(x : (FractionalIdeal (𝓞 K)⁰ K)ˣ), hincl x.2⟩ = 1
    rw [hxe, map_mul, hχ b hb hbS', hagree _ hcS hcS' hcS'', hχ' c hc hcS'', one_mul]
  set ψ : RayClassGroup g →* ℂˣ := ι.liftOfRightInverse (Function.surjInv hsurj)
    (Function.rightInverse_surjInv hsurj) ⟨φ, hker⟩ with hψ
  have hψι : ∀ x : sIdeals S'', ψ (ι x) = φ x := fun x =>
    ι.liftOfRightInverse_comp_apply (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨φ, hker⟩ x
  refine ⟨g.finiteSupport, fun v hv => hm ▸ chr_gcd_support_subset_left m m' hv,
    fun v hv => hm' ▸ chr_gcd_support_subset_right m m' hv,
    fun v hv hv' => ?_, ψ.comp (toRayClass g), ⟨g, rfl, fun a ha h => ?_⟩, ?_⟩
  · rw [← hm] at hv; rw [← hm'] at hv'
    exact Modulus.mem_gcd_finiteSupport hv hv'
  · show ψ (QuotientGroup.mk (⟨toPrincipalIdeal (𝓞 K) K a, h⟩ : coprimeIdeals g)) = 1
    have : (QuotientGroup.mk (⟨toPrincipalIdeal (𝓞 K) K a, h⟩ : coprimeIdeals g) : RayClassGroup g) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact ⟨a, ha, rfl⟩
    rw [this, map_one]
  · intro a ha h h'
    exact (hψι ⟨a, ha⟩).symm

/-! ## Two Dirichlet characters agreeing on $I^{S''}$ agree -/

theorem chr_agree {S₁ S₂ S'' : Set (HeightOneSpectrum (𝓞 K))} (hS'' : S''.Finite) (h₁ : S₁ ⊆ S'')
    (hS : S₁ = S₂) (g g' : Modulus K) (hg : g.finiteSupport = S₁) (hg' : g'.finiteSupport = S₂)
    (ξ : sIdeals S₁ →* ℂˣ) (ξ' : sIdeals S₂ →* ℂˣ)
    (hξ : ∀ a : Kˣ, a ∈ congruenceSubgroup g → ∀ h : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S₁, ξ ⟨_, h⟩ = 1)
    (hξ' : ∀ a : Kˣ, a ∈ congruenceSubgroup g' → ∀ h : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S₂, ξ' ⟨_, h⟩ = 1)
    (hagree : ∀ a ∈ sIdeals S'', ∀ (h : a ∈ sIdeals S₁) (h' : a ∈ sIdeals S₂), ξ ⟨a, h⟩ = ξ' ⟨a, h'⟩) :
    ∀ a : sIdeals S₁, ξ a = ξ' ⟨a, hS ▸ a.2⟩ := by
  subst hS
  intro J
  let mm : Modulus K := ⟨g.finite * g'.finite, mul_ne_zero g.finite_ne_bot g'.finite_ne_bot,
    g.infinite ∪ g'.infinite, fun w hw => hw.elim (g.isReal_of_mem w) (g'.isReal_of_mem w)⟩
  have hdg : g.Dvd mm := ⟨dvd_mul_right _ _, Set.subset_union_left⟩
  have hdg' : g'.Dvd mm := ⟨dvd_mul_left _ _, Set.subset_union_right⟩
  have hmm : mm.finiteSupport = S₁ := by
    ext v
    constructor
    · intro hv
      rcases v.prime.dvd_mul.1 (show v.asIdeal ∣ g.finite * g'.finite from hv) with h | h
      · rw [← hg]; exact h
      · rw [← hg']; exact h
    · intro hv
      rw [← hg] at hv
      exact dvd_mul_of_dvd_left hv _
  have hJ : (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ coprimeIdeals mm := fun v hv => J.2 v (hmm ▸ hv)
  obtain ⟨a, ha, haJ⟩ := chr_surj mm S'' hS'' (hmm ▸ h₁) J.1 hJ
  have haS : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S₁ := hmm ▸ rayPrincipal_le mm ⟨a, ha, rfl⟩
  have e1 := hξ a (congruenceSubgroup_le_of_dvd hdg ha) haS
  have e2 := hξ' a (congruenceSubgroup_le_of_dvd hdg' ha) haS
  have hprod : (⟨toPrincipalIdeal (𝓞 K) K a * J.1, (sIdeals S₁).mul_mem haS J.2⟩ : sIdeals S₁) =
      ⟨toPrincipalIdeal (𝓞 K) K a, haS⟩ * J := rfl
  have key := hagree _ haJ ((sIdeals S₁).mul_mem haS J.2) ((sIdeals S₁).mul_mem haS J.2)
  rw [hprod, map_mul, map_mul, e1, e2, one_mul, one_mul] at key
  exact key

/-! ## Primitive characters -/

/-- **Primitive characters, unconditional** (Milne, *CFT*, V, p. 165): every class of cotrained Dirichlet characters
contains a unique primitive character. -/
@[kb "milne2020cft" "Ch. V, §3, p. 165 (primitive characters)"]
theorem primitiveCharacters (K : Type) [Field K] [NumberField K] : PrimitiveCharacters K where
  exists_primitive χ hχ := by
    classical
    let P : ℕ → Prop := fun n => ∃ χ₁ : IdealChar K, IsDirichletCharOn χ₁.S χ₁.χ ∧
      CharCotrained χ.χ χ₁.χ ∧ χ₁.S.ncard = n
    have hP : ∃ n, P n := ⟨_, χ, hχ, charCotrained_equivalence.refl χ, rfl⟩
    obtain ⟨χ₁, hD, hC, hn⟩ := Nat.find_spec hP
    refine ⟨χ₁, ⟨hD, fun χ' hD' hC' => ?_⟩, hC⟩
    obtain ⟨m, hm, hmt⟩ := hD
    obtain ⟨m', hm', hmt'⟩ := hD'
    obtain ⟨S'', hfin, hsub, hag⟩ := hC'
    obtain ⟨T, hTS, hTS', hST, ξ, ⟨g, hgT, hgξ⟩, hξagree⟩ :=
      chr_descent hfin hsub m m' hm hm' χ₁.χ χ'.χ hmt hmt' hag
    let χT : IdealChar K := ⟨T, χ₁.finite.subset hTS, ξ⟩
    have hDT : IsDirichletCharOn χT.S χT.χ := ⟨g, hgT, hgξ⟩
    have hCT : CharCotrained χ₁.χ χT.χ :=
      ⟨S'', hfin, fun v hv => hv.elim (fun h => (Set.subset_union_left.trans hsub) h)
        (fun h => (hTS'.trans Set.subset_union_right |>.trans hsub) h), hξagree⟩
    have hCχT : CharCotrained χ.χ χT.χ := charCotrained_equivalence.trans hC hCT
    have hle : Nat.find hP ≤ χT.S.ncard := Nat.find_min' hP ⟨χT, hDT, hCχT, rfl⟩
    have hTeq : T = χ₁.S :=
      Set.eq_of_subset_of_ncard_le hTS (by rw [hn] at *; exact hle) χ₁.finite
    exact hTeq ▸ hTS'
  unique χ₁ χ₂ h₁ h₂ hC := by
    obtain ⟨hD1, hP1⟩ := h₁
    obtain ⟨hD2, hP2⟩ := h₂
    obtain ⟨m, hm, hmt⟩ := hD1
    obtain ⟨m', hm', hmt'⟩ := hD2
    obtain ⟨S'', hfin, hsub, hag⟩ := hC
    obtain ⟨T, hTS, hTS', hST, ξ, ⟨g, hgT, hgξ⟩, hξagree⟩ :=
      chr_descent hfin hsub m m' hm hm' χ₁.χ χ₂.χ hmt hmt' hag
    let χT : IdealChar K := ⟨T, χ₁.finite.subset hTS, ξ⟩
    have hDT : IsDirichletCharOn χT.S χT.χ := ⟨g, hgT, hgξ⟩
    have h1S : χ₁.S ⊆ S'' := Set.subset_union_left.trans hsub
    have h2S : χ₂.S ⊆ S'' := Set.subset_union_right.trans hsub
    have hC1 : CharCotrained χ₁.χ χT.χ :=
      ⟨S'', hfin, fun v hv => hv.elim (fun h => h1S h) (fun h => h2S (hTS' h)), hξagree⟩
    have hC2 : CharCotrained χ₂.χ χT.χ :=
      ⟨S'', hfin, fun v hv => hv.elim (fun h => h2S h) (fun h => h2S (hTS' h)), fun a ha h2 h' =>
        (hag a ha (fun v hv => ha v (h1S hv)) h2).symm.trans (hξagree a ha (fun v hv => ha v (h1S hv)) h')⟩
    have hS1 : χ₁.S ⊆ T := hP1 χT hDT hC1
    have hS2 : χ₂.S ⊆ T := hP2 χT hDT hC2
    have hT1 : T = χ₁.S := Set.Subset.antisymm hTS hS1
    have hS : χ₁.S = χ₂.S := Set.Subset.antisymm (hS1.trans hTS') (hS2.trans hTS)
    refine ⟨hS, fun a => ?_⟩
    clear_value χT
    subst hT1
    have e1 := chr_agree hfin h1S rfl m g hm hgT χ₁.χ ξ hmt hgξ hξagree a
    have e2 := chr_agree hfin h1S hS g m' hgT hm' ξ χ₂.χ hgξ hmt'
      (fun b hb h h' => (hξagree b hb (fun v hv => hb v (h1S hv)) h).symm.trans
        (hag b hb (fun v hv => hb v (h1S hv)) h')) a
    exact e1.trans e2

/-! ## Remark 3.28 -/

section Remark328

variable (hR : IdelicReciprocity K) (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- A version of `idelesW_le_ker_of_artinFactorsThrough` with weaker input: the Artin map is only assumed trivial on
the principal ideals $(b)$, $b\in K_{\mathfrak m,1}$, prime to $\mathfrak m_0$ and to a finite set $\Sigma$ (no
ramification hypothesis). -/
theorem idelesW_le_ker_of_hyp (m : Modulus K) (Sg : Set (HeightOneSpectrum (𝓞 K))) (hSg : Sg.Finite)
    (H : ∀ b : Kˣ, b ∈ congruenceSubgroup m →
      toPrincipalIdeal (𝓞 K) K b ∈ sIdeals (m.finiteSupport ∪ Sg) →
        artinTot L (toPrincipalIdeal (𝓞 K) K b) = 1) :
    idelesW m ≤ (idelicArtinOf hR L).ker := by
  classical
  obtain ⟨M, hMs, hMinf, hMW⟩ := exists_modulus_idelesW_le_ker hR L
  let m'' : Modulus K := ⟨m.finite * M.finite, mul_ne_zero m.finite_ne_bot M.finite_ne_bot,
    m.infinite ∪ M.infinite, fun w hw => hw.elim (m.isReal_of_mem w) (M.isReal_of_mem w)⟩
  let m' : Modulus K := m''.adjoin hSg.toFinset
  have hdm : m.Dvd m' := ⟨(dvd_mul_right _ _).trans (dvd_mul_right _ _), Set.subset_union_left⟩
  have hdM : M.Dvd m' := ⟨(dvd_mul_left _ _).trans (dvd_mul_right _ _), Set.subset_union_right⟩
  have hm' : ∀ v, v ∉ m'.finiteSupport → v ∈ unramifiedPrimes K L := fun v hv => by
    by_contra hc
    have hvM : v ∈ M.finiteSupport := by rw [hMs]; exact hc
    exact hv ((show v.asIdeal ∣ M.finite from hvM).trans hdM.1)
  have hW' : idelesW m' ≤ (idelicArtinOf hR L).ker := (idelesW_le_of_dvd hdM).trans hMW
  have hsupp : m.finiteSupport ∪ Sg ⊆ m'.finiteSupport := by
    intro v hv
    rcases hv with hv | hv
    · exact (show v.asIdeal ∣ m.finite from hv).trans hdm.1
    · exact (Modulus.mem_finiteSupport_adjoin m'' hSg.toFinset v).2 (Or.inr (hSg.mem_toFinset.2 hv))
  intro x hx
  obtain ⟨b, hb⟩ := exists_unitEmbedding_mul_mem_idelesMod m' x
  set y := IdeleGroup.unitEmbedding (𝓞 K) K b * x with hy
  have hφy := idelicArtinOf_eq_artinTot hR L m' hm' hW' y hb
  have hx1 : ideleToIdeal K x = 1 := (item_4_1 (K := K)).2 x |>.2 (idelesW_unit hx)
  have hyid : ideleToIdeal K y = toPrincipalIdeal (𝓞 K) K b := by
    rw [hy, map_mul, ideleToIdeal_unitEmbedding, hx1, mul_one]
  have hbm : b ∈ congruenceSubgroup m := by
    rw [mem_congruenceSubgroup_iff_mem_idelesMod]
    have : IdeleGroup.unitEmbedding (𝓞 K) K b = y * x⁻¹ := by rw [hy]; group
    rw [this]
    exact mul_mem (idelesMod_le_of_dvd hdm hb) (inv_mem hx.1)
  have hmem : toPrincipalIdeal (𝓞 K) K b ∈ sIdeals (m.finiteSupport ∪ Sg) := by
    have := ideleToIdeal_mem_coprimeIdeals m' y hb
    rw [hyid] at this
    exact fun v hv => this v (hsupp hv)
  have h2 := H b hbm hmem
  rw [MonoidHom.mem_ker]
  have h3 : idelicArtinOf hR L y = idelicArtinOf hR L x := by
    rw [hy, map_mul, (idelicArtinOf_spec hR L).2.1 b, one_mul]
  rw [← h3, hφy, hyid]
  exact h2

open scoped AdicCompletionExtension in
open TauCeti.GlobalNumberFields in
/-- If the idèlic Artin map is trivial on $W_\mathfrak m$, then $L$ is unramified outside $\mathfrak m$ (local units at
a prime not dividing $\mathfrak m$ have trivial local Artin symbol, hence conductor exponent $0$). -/
theorem isUnramifiedAt_of_idelesW (m : Modulus K) (hW : idelesW m ≤ (idelicArtinTauCeti L).ker)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ m.finiteSupport) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  have hc : TauCeti.ClassFieldTheory.conductorExponent (v.adicCompletion K) (w.adicCompletion L) ≤ 0 := by
    refine (TauCeti.ClassFieldTheory.conductorExponent_le_iff _ _).2 fun u hu => ?_
    have hu1 : Valued.v (u : v.adicCompletion K) = 1 :=
      ((HeightOneSpectrum.mem_unitFiltration_adicCompletion_iff v).1 hu).1
    have hx : IdeleGroup.ofAdicCompletion (𝓞 K) K v u ∈ idelesW m := by
      refine ⟨⟨fun w' hw' => ?_, fun v' hv' => ?_⟩, fun v' _ => ?_⟩
      · unfold IsPosAt; rw [ideleInfAt_ofAdic]; simp
      · have hne : v' ≠ v := fun h => hv (h ▸ hv')
        rw [ideleFinAt_ofAdic_ne hne]; simp
      · by_cases hvv : v' = v
        · subst hvv; rw [ideleFinAt_ofAdic_self]; exact hu1
        · rw [ideleFinAt_ofAdic_ne hvv]; exact map_one _
    have hArt := (idelicArtinTauCeti_eq_one_iff L _).1 (MonoidHom.mem_ker.1 (hW hx))
    rw [TauCeti.ClassFieldTheory.globalArtinMap_local, ofMul_eq_zero] at hArt
    exact (TauCeti.ClassFieldTheory.localArtinAt_eq_one_iff_mem_normGroup v w u).1 hArt
  have hc0 : TauCeti.ClassFieldTheory.conductorExponent (v.adicCompletion K) (w.adicCompletion L) = 0 :=
    Nat.eq_zero_of_le_zero hc
  rw [TauCeti.ClassFieldTheory.conductorExponent_eq_zero_iff,
    TauCeti.isUnramified_iff_ramificationIndex_eq_one,
    HeightOneSpectrum.ramificationIndex_adicCompletion] at hc0
  exact Ideal.ramificationIdx_eq_one_iff.1 hc0

theorem unramified_of_idelesW (m : Modulus K) (hW : idelesW m ≤ (idelicArtinTauCeti L).ker)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ m.finiteSupport) : v ∈ unramifiedPrimes K L := by
  intro Q hQ hlies
  exact isUnramifiedAt_of_idelesW L m hW hv
    ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩

end Remark328

/-- Moving an element of $K_{\mathfrak m,1}$ prime to $S_1$ to one prime to a bigger finite set $S''$ without changing
the value of a Dirichlet character $\chi_1$ on $I^{S_1}$ (with $S(\mathfrak m)\subseteq S_1$). -/
theorem chr_transfer {S₁ S'' : Set (HeightOneSpectrum (𝓞 K))} (hS'' : S''.Finite) (h₁ : S₁ ⊆ S'')
    (m₁ m : Modulus K) (hm₁ : m₁.finiteSupport = S₁) (hms : m.finiteSupport ⊆ S₁) (χ₁ : sIdeals S₁ →* ℂˣ)
    (hχ₁ : ∀ a : Kˣ, a ∈ congruenceSubgroup m₁ → ∀ h : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S₁, χ₁ ⟨_, h⟩ = 1)
    (a : Kˣ) (ha : a ∈ congruenceSubgroup m) (haS : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S₁) :
    ∃ a' : Kˣ, a' ∈ congruenceSubgroup m ∧ toPrincipalIdeal (𝓞 K) K a' ∈ sIdeals S'' ∧
      ∃ h : toPrincipalIdeal (𝓞 K) K a' ∈ sIdeals S₁, χ₁ ⟨_, h⟩ = χ₁ ⟨_, haS⟩ := by
  let mm : Modulus K := ⟨m.finite * m₁.finite, mul_ne_zero m.finite_ne_bot m₁.finite_ne_bot,
    m.infinite ∪ m₁.infinite, fun w hw => hw.elim (m.isReal_of_mem w) (m₁.isReal_of_mem w)⟩
  have hdm : m.Dvd mm := ⟨dvd_mul_right _ _, Set.subset_union_left⟩
  have hdm₁ : m₁.Dvd mm := ⟨dvd_mul_left _ _, Set.subset_union_right⟩
  have hmm : mm.finiteSupport = S₁ := by
    ext v
    constructor
    · intro hv
      rcases v.prime.dvd_mul.1 (show v.asIdeal ∣ m.finite * m₁.finite from hv) with h | h
      · exact hms h
      · rw [← hm₁]; exact h
    · intro hv
      rw [← hm₁] at hv
      exact dvd_mul_of_dvd_right hv _
  have hJ : toPrincipalIdeal (𝓞 K) K a ∈ coprimeIdeals mm := fun v hv => haS v (hmm ▸ hv)
  obtain ⟨c, hc, hcJ⟩ := chr_surj mm S'' hS'' (hmm ▸ h₁) _ hJ
  have hcS : toPrincipalIdeal (𝓞 K) K c ∈ sIdeals S₁ := hmm ▸ rayPrincipal_le mm ⟨c, hc, rfl⟩
  refine ⟨c * a, mul_mem (congruenceSubgroup_le_of_dvd hdm hc) ha, by rw [map_mul]; exact hcJ,
    by rw [map_mul]; exact (sIdeals S₁).mul_mem hcS haS, ?_⟩
  have e : (⟨toPrincipalIdeal (𝓞 K) K (c * a), by rw [map_mul]; exact (sIdeals S₁).mul_mem hcS haS⟩ :
      sIdeals S₁) = ⟨toPrincipalIdeal (𝓞 K) K c, hcS⟩ * ⟨toPrincipalIdeal (𝓞 K) K a, haS⟩ := by
    refine Subtype.ext ?_
    show toPrincipalIdeal (𝓞 K) K (c * a) = toPrincipalIdeal (𝓞 K) K c * toPrincipalIdeal (𝓞 K) K a
    rw [map_mul]
  rw [e, map_mul, hχ₁ c (congruenceSubgroup_le_of_dvd hdm₁ hc) hcS, one_mul]

/-- Restriction to the fixed field of $\ker\chi$ is trivial on $\sigma$ iff $\chi(\sigma)=1$. -/
theorem restrictNormalHom_fixedField_eq_one_iff (L : Type) [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (χ : Gal(L/K) →* ℂˣ) (σ : Gal(L/K)) :
    AlgEquiv.restrictNormalHom (IntermediateField.fixedField χ.ker) σ = 1 ↔ χ σ = 1 := by
  have hfix : IntermediateField.fixingSubgroup (IntermediateField.fixedField χ.ker) = χ.ker :=
    IntermediateField.fixingSubgroup_fixedField χ.ker
  have hiff : χ σ = 1 ↔ σ ∈ IntermediateField.fixingSubgroup (IntermediateField.fixedField χ.ker) := by
    rw [hfix]; exact MonoidHom.mem_ker.symm
  rw [hiff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := AlgEquiv.restrictNormal_commutes σ (IntermediateField.fixedField χ.ker) ⟨x, hx⟩
    have h' : σ.restrictNormal (IntermediateField.fixedField χ.ker) = 1 := h
    rw [h'] at this
    simpa using this.symm
  · intro h
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    have := AlgEquiv.restrictNormal_commutes σ (IntermediateField.fixedField χ.ker) x
    have h2 := h x x.2
    simp only [AlgEquiv.restrictNormalHom_apply] at *
    simpa [h2] using this

/-- **Remark 3.28, unconditional** (Milne, *CFT*, V, Remark 3.28, p. 165): for a character $\chi$ of $G$ with kernel
$H$, $\mathfrak f(\chi\circ\psi_{L/K}) = \mathfrak f(L^H/K)$. -/
@[kb "milne2020cft" "Ch. V, Remark 3.28"]
theorem remark3_28 (K : Type) [Field K] [NumberField K] : Remark3_28 K where
  conductor_eq L _ _ _ _ χ f g hf hg := by
    classical
    obtain ⟨χ₁, ⟨⟨m₁, hm₁, hm₁t⟩, -⟩, ⟨S'', hfin, hsub, hag⟩, ⟨hfS, hftriv⟩, hmin⟩ := hf
    set F := IntermediateField.fixedField χ.ker with hF
    have hSL : (unramifiedPrimes K L)ᶜ ⊆ S'' := Set.subset_union_left.trans hsub
    have hS1 : χ₁.S ⊆ S'' := Set.subset_union_right.trans hsub
    have hunr : ∀ v, v ∉ S'' → v ∈ unramifiedPrimes K L := fun v hv => by
      by_contra h; exact hv (hSL h)
    have key : ∀ a : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ (ha : a ∈ sIdeals S'') (h1 : a ∈ sIdeals χ₁.S),
        χ₁.χ ⟨a, h1⟩ = 1 ↔ artinTot F a = 1 := by
      intro a ha h1
      have hSL' : a ∈ sIdeals (unramifiedPrimes K L)ᶜ := fun v hv => ha v (hSL hv)
      have e1 : χ (artinTot L a) = χ₁.χ ⟨a, h1⟩ := hag a ha hSL' h1
      have e2 : artinTot F a = AlgEquiv.restrictNormalHom F (artinTot L a) :=
        artinMap_restrict F L S'' hunr ⟨a, ha⟩
      rw [← e1, e2, restrictNormalHom_fixedField_eq_one_iff L χ]
    -- triviality transfer
    have triv_of_aft : ∀ m : Modulus K, m.finiteSupport ⊆ χ₁.S → ArtinFactorsThrough F m →
        ∀ a : Kˣ, a ∈ congruenceSubgroup m → ∀ h : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals χ₁.S,
          χ₁.χ ⟨_, h⟩ = 1 := by
      intro m hms hAFT a ha h
      obtain ⟨a', ha', ha'S'', h', he⟩ := chr_transfer hfin hS1 m₁ m hm₁ hms χ₁.χ hm₁t a ha h
      rw [← he]
      refine (key _ ha'S'' h').2 ?_
      exact hAFT.2 a' ha' (fun v hv => ha'S'' v (hS1 (hms hv)))
    -- f factors the Artin map of F
    have hW : idelesW f ≤ (idelicArtinOf (idelicReciprocity K) F).ker := by
      refine idelesW_le_ker_of_hyp (idelicReciprocity K) F f S'' hfin (fun b hb hbS => ?_)
      have hbS'' : toPrincipalIdeal (𝓞 K) K b ∈ sIdeals S'' := fun v hv => hbS v (Or.inr hv)
      have hbS1 : toPrincipalIdeal (𝓞 K) K b ∈ sIdeals χ₁.S := fun v hv => hbS'' v (hS1 hv)
      exact (key _ hbS'' hbS1).1 (hftriv b hb hbS1)
    have hW' : idelesW f ≤ (idelicArtinTauCeti F).ker := by
      rw [← idelicArtinOf_idelicReciprocity F]; exact hW
    have hFf : ArtinFactorsThrough F f :=
      (artinFactorsThrough_iff (idelicReciprocity K) F f).2
        ⟨fun v hv => unramified_of_idelesW F f hW' hv, hW⟩
    have hgf : g.Dvd f := hg.2 f hFf
    have hgS : g.finiteSupport ⊆ χ₁.S := fun v hv =>
      hfS ((show v.asIdeal ∣ g.finite from hv).trans hgf.1)
    have hfg : f.Dvd g := hmin g hgS (triv_of_aft g hgS hg.1)
    have h1 : f.finite = g.finite :=
      le_antisymm (Ideal.dvd_iff_le.1 hgf.1) (Ideal.dvd_iff_le.1 hfg.1)
    have h2 : f.infinite = g.infinite := Set.Subset.antisymm hfg.2 hgf.2
    cases f
    cases g
    simp only at h1 h2
    subst h1 h2
    rfl

end NumberFieldKB.MilneCFT
