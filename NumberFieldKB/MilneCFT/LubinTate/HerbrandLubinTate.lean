import NumberFieldKB.MilneCFT.LubinTate.Jumps

/-!
# Example 4.2 from Proposition 4.1 (Milne, *Class Field Theory*, Chapter I, Example 4.2)

For $L = K_{\pi,n}$, the step structure of the lower ramification filtration (Proposition 4.1 and the
ramification quotient bounds) gives $(G_0 : G_t) = (q-1)q^{k-1}$ for $q^{k-1} - 1 < t \le q^k - 1$, hence
$\varphi(q^i - 1) = i$ and $G^i = G_{q^i - 1}$.
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem units_map_mk_surjective (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (Units.map (Ideal.Quotient.mk (𝓂[K] ^ n)).toMonoidHom) := by
  have : Nontrivial (𝒪[K] ⧸ 𝓂[K] ^ n) := by
    apply Ideal.Quotient.nontrivial_iff.2
    intro htop
    have : 𝓂[K] ^ n ≤ 𝓂[K] := Ideal.pow_le_self (by omega)
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (htop ▸ this))
  exact IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective
    (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective)

theorem unitFiltrationMod_zero (n : ℕ) (hn : 1 ≤ n) : unitFiltrationMod (K := K) n 0 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨u, rfl⟩ := units_map_mk_surjective (K := K) n hn x
  exact ⟨u, rfl, by simp⟩

theorem index_unitFiltrationMod (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    (unitFiltrationMod (K := K) n k).index = if k = 0 then 1 else (resCard K - 1) * resCard K ^ (k - 1) := by
  split_ifs with h0
  · subst h0; rw [unitFiltrationMod_zero n hn]; exact Subgroup.index_top
  · let r : (𝒪[K] ⧸ 𝓂[K] ^ n)ˣ →* (𝒪[K] ⧸ 𝓂[K] ^ k)ˣ :=
      Units.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right hk)).toMonoidHom
    have hrs : Function.Surjective r := by
      intro y
      obtain ⟨u, rfl⟩ := units_map_mk_surjective (K := K) k (by omega) y
      refine ⟨Units.map (Ideal.Quotient.mk (𝓂[K] ^ n)).toMonoidHom u, ?_⟩
      ext; simp [r]
    have hker : r.ker = unitFiltrationMod n k := by
      ext x
      constructor
      · intro hx
        rw [MonoidHom.mem_ker] at hx
        obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x : 𝒪[K] ⧸ 𝓂[K] ^ n)
        have h1 : Ideal.Quotient.mk (𝓂[K] ^ k) a = 1 := by
          have := congrArg (fun y : (𝒪[K] ⧸ 𝓂[K] ^ k)ˣ => (y : 𝒪[K] ⧸ 𝓂[K] ^ k)) hx
          simp only [r, Units.coe_map, Units.val_one, ← ha] at this
          simpa using this
        have h2 : a - 1 ∈ 𝓂[K] ^ k := by
          rw [← map_one (Ideal.Quotient.mk (𝓂[K] ^ k))] at h1
          exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 h1
        have h3 : IsUnit a := by
          by_contra hna
          have ha' : a ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal a).2 hna
          have h2' : a - 1 ∈ 𝓂[K] := Ideal.pow_le_self h0 h2
          have : (1 : 𝒪[K]) ∈ 𝓂[K] := by
            have := Ideal.sub_mem _ ha' h2'
            simp at this
          exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 this)
        refine ⟨h3.unit, ?_, h2⟩
        ext
        simp [ha]
      · rintro ⟨u, rfl, hu⟩
        rw [MonoidHom.mem_ker]
        ext
        simp only [r, Units.coe_map, Units.val_one]
        show Ideal.Quotient.factor _ (Ideal.Quotient.mk _ (u : 𝒪[K])) = 1
        rw [Ideal.Quotient.factor_mk, ← map_one (Ideal.Quotient.mk (𝓂[K] ^ k))]
        exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 hu
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hrs]
    rw [Subgroup.card_top]
    exact card_units_quot_maximalIdeal_pow k (by omega)


/-- The lower filtration of $K_{\pi,n}/K$ is constant on $[q^k, q^{k+1} - 1]$ for $k < n$ (the step structure
extracted from the proof of `example_4_7`). -/
theorem lt_step_const (h : LubinTateExtensionTheorem K Ω) (h41 : LubinTateLowerFiltration K Ω h)
    (hRQ : RamificationQuotientBounds K Ω) {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    ∀ k < n, ∀ j, resCard K ^ k ≤ j → j ≤ resCard K ^ (k + 1) - 1 →
      ramificationGroup (ltField Ω π n) j = ramificationGroup (ltField Ω π n) (resCard K ^ (k + 1) - 1) := by
  have := ltField_isGalois h hπ hn
  set L := ltField Ω π n with hL
  set q := resCard K with hq
  have hq2 : 2 ≤ q := two_le_resCard K
  obtain ⟨χ, hχ⟩ := h.galois hπ n hn
  have hmap := h41.map_eq hπ n hn χ hχ
  have hnot := h41.not_mem hπ n hn χ hχ
  have hk0 : ramificationGroup L 1 ≤ ramificationGroup L (q - 1) := by
    obtain ⟨f, -, hf⟩ := hRQ.residue_card L
    have hG : ramificationGroup L (q - 1) = (unitFiltrationMod n 1).map χ.toMonoidHom := by
      rw [hmap 1 hn, pow_one]
    have hidx : (ramificationGroup L (q - 1)).index ∣ q - 1 := by
      rw [hG, ← Subgroup.index_comap_of_surjective _ (f := χ.toMonoidHom) χ.surjective,
        Subgroup.comap_map_eq_self_of_injective χ.injective]
      exact index_unitFiltrationMod_one_dvd n hn
    have hle : ramificationGroup L (q - 1) ≤ ramificationGroup L 1 :=
      ramificationGroup_antitone L (by omega)
    have h1 : (ramificationGroup L (q - 1)).relIndex (ramificationGroup L 1) ∣ q - 1 :=
      (Subgroup.relIndex_dvd_index_of_le hle).trans hidx
    have h2 : (ramificationGroup L (q - 1)).relIndex (ramificationGroup L 1) ∣ (q ^ f) ^ (q - 2) := by
      have := relIndex_one_dvd hRQ L (q - 2)
      rwa [show q - 2 + 1 = q - 1 by omega, hf] at this
    have hcop : Nat.Coprime ((q ^ f) ^ (q - 2)) (q - 1) := by
      apply Nat.Coprime.pow_left
      apply Nat.Coprime.pow_left
      have : Nat.Coprime (q - 1 + 1) (q - 1) := by simp
      rwa [Nat.sub_add_cancel (by omega)] at this
    exact Subgroup.relIndex_eq_one.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h1)
  have hstep : ∀ k < n, ramificationGroup L (q ^ k) ≤ ramificationGroup L (q ^ (k + 1) - 1) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0'
    · simpa using hk0
    intro σ hσ
    have hσ' : σ ∈ ramificationGroup L (q ^ k - 1) := ramificationGroup_antitone L (by omega) hσ
    rw [← hmap k (by omega)] at hσ'
    obtain ⟨x, hx, rfl⟩ := hσ'
    rw [← hmap (k + 1) (by omega)]
    by_cases hx1 : x ∈ unitFiltrationMod n (k + 1)
    · exact ⟨x, hx1, rfl⟩
    · exact absurd hσ (hnot k hk0' hk x hx hx1)
  exact fun k hk j h1 h2 => le_antisymm ((ramificationGroup_antitone L h1).trans (hstep k hk))
      (ramificationGroup_antitone L h2)

/-- $G_0 = G$ and $(G_0 : G_{q^k - 1}) = (q-1)q^{k-1}$ for $1 \le k \le n$. -/
theorem lt_relIndex (h : LubinTateExtensionTheorem K Ω) (h41 : LubinTateLowerFiltration K Ω h)
    {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (hk : k ≤ n) :
    (ramificationGroup (ltField Ω π n) (resCard K ^ k - 1)).relIndex (ramificationGroup (ltField Ω π n) 0) =
      if k = 0 then 1 else (resCard K - 1) * resCard K ^ (k - 1) := by
  have := ltField_isGalois h hπ hn
  obtain ⟨χ, hχ⟩ := h.galois hπ n hn
  have hmap := h41.map_eq hπ n hn χ hχ
  have h0 : ramificationGroup (ltField Ω π n) 0 = ⊤ := by
    have := hmap 0 (Nat.zero_le n)
    rw [pow_zero, Nat.sub_self, unitFiltrationMod_zero n hn, Subgroup.map_top] at this
    rw [← this]
    exact MonoidHom.range_eq_top.2 χ.surjective
  rw [h0, Subgroup.relIndex_top_right, ← hmap k hk]
  exact (Subgroup.index_map_equiv (unitFiltrationMod n k) χ).trans (index_unitFiltrationMod n k hn hk)


open MeasureTheory in
/-- Pure real analysis: a function which is the constant `1/((q-1)q^k)` on `(q^k - 1, q^(k+1) - 1]` for `k < n`
has `∫_0^{q^i - 1} f = i` for `i ≤ n`, and is interval integrable there. -/
theorem phi_aux (q : ℝ) (hq : 2 ≤ q) (n : ℕ) (f : ℝ → ℝ)
    (hf : ∀ k < n, ∀ t ∈ Set.Ioc (q ^ k - 1) (q ^ (k + 1) - 1), f t = 1 / ((q - 1) * q ^ k)) :
    ∀ i ≤ n, IntervalIntegrable f volume 0 (q ^ i - 1) ∧ ∫ x in (0 : ℝ)..(q ^ i - 1), f x = i := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hqi : 1 ≤ q ^ i := one_le_pow₀ (by linarith)
    have hlt : q ^ i - 1 ≤ q ^ (i + 1) - 1 := by
      have : q ^ i ≤ q ^ (i + 1) := pow_le_pow_right₀ (by linarith) (by omega)
      linarith
    have heq : ∀ t ∈ Set.uIoc (q ^ i - 1) (q ^ (i + 1) - 1), f t = 1 / ((q - 1) * q ^ i) := by
      rw [Set.uIoc_of_le hlt]
      exact fun t ht => hf i (by omega) t ht
    have hI : IntervalIntegrable f volume (q ^ i - 1) (q ^ (i + 1) - 1) :=
      (intervalIntegrable_const (c := 1 / ((q - 1) * q ^ i))).congr (fun t ht => (heq t ht).symm)
    refine ⟨ih1.trans hI, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals ih1 hI, ih2,
      intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => heq t ht), intervalIntegral.integral_const]
    have hq1 : q - 1 ≠ 0 := by intro h; linarith
    have hqp : q ^ i ≠ 0 := by positivity
    simp only [smul_eq_mul]
    push_cast
    field_simp
    ring


/-- On `(q^k - 1, q^(k+1) - 1]` (`k < n`) the Herbrand integrand of `K_{π,n}` is `1/((q-1)q^k)`. -/
theorem lt_integrand (h : LubinTateExtensionTheorem K Ω) (h41 : LubinTateLowerFiltration K Ω h)
    (hRQ : RamificationQuotientBounds K Ω) {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ} (hn : 1 ≤ n) :
    ∀ k < n, ∀ t ∈ Set.Ioc ((resCard K : ℝ) ^ k - 1) ((resCard K : ℝ) ^ (k + 1) - 1),
      1 / (((ramificationGroupReal (ltField Ω π n) t).relIndex (ramificationGroup (ltField Ω π n) 0) : ℕ) : ℝ) =
        1 / (((resCard K : ℝ) - 1) * (resCard K : ℝ) ^ k) := by
  intro k hk t ht
  have := ltField_isGalois h hπ hn
  have hq2 : 2 ≤ resCard K := two_le_resCard K
  have hqk : 1 ≤ resCard K ^ k := Nat.one_le_pow _ _ (by omega)
  have hqkR : (1 : ℝ) ≤ (resCard K : ℝ) ^ k := by exact_mod_cast hqk
  obtain ⟨ht1, ht2⟩ := ht
  have hnle : ¬ t ≤ -1 := by linarith
  have hc1 : resCard K ^ k ≤ ⌈t⌉₊ := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : ((⌈t⌉₊ : ℕ) : ℝ) ≤ (resCard K : ℝ) ^ k - 1 := by
      have : ⌈t⌉₊ + 1 ≤ resCard K ^ k := hlt
      have h' : ((⌈t⌉₊ + 1 : ℕ) : ℝ) ≤ ((resCard K ^ k : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      linarith
    linarith [Nat.le_ceil t]
  have hc2 : ⌈t⌉₊ ≤ resCard K ^ (k + 1) - 1 := by
    rw [Nat.ceil_le, Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
    exact ht2
  have hG := lt_step_const h h41 hRQ hπ hn k hk ⌈t⌉₊ hc1 hc2
  have hR : ramificationGroupReal (ltField Ω π n) t =
      ramificationGroup (ltField Ω π n) (resCard K ^ (k + 1) - 1) := by
    rw [ramificationGroupReal]
    simp only [hnle, ↓reduceIte, hG]
  rw [hR, lt_relIndex h h41 hπ hn (k + 1) (by omega)]
  simp only [show k + 1 ≠ 0 by omega, ↓reduceIte]
  rw [Nat.add_sub_cancel]
  push_cast [Nat.cast_sub (show 1 ≤ resCard K by omega)]
  rfl

/-- The Herbrand integrand is positive. -/
theorem lt_integrand_pos (L : IntermediateField K Ω) [FiniteDimensional K L] (t : ℝ) :
    0 < 1 / (((ramificationGroupReal L t).relIndex (ramificationGroup L 0) : ℕ) : ℝ) := by
  have : (ramificationGroupReal L t).relIndex (ramificationGroup L 0) ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have : 0 < (((ramificationGroupReal L t).relIndex (ramificationGroup L 0) : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero this
  positivity


/-- **Example 4.2 from Proposition 4.1** (Milne, *CFT*, I, Example 4.2): $\varphi(q^i - 1) = i$ and
$G^i = G_{q^i - 1}$ for $L = K_{\pi,n}$, $0 \le i \le n$. -/
theorem lubinTateHerbrand_of (h : LubinTateExtensionTheorem K Ω) (h41 : LubinTateLowerFiltration K Ω h)
    (hRQ : RamificationQuotientBounds K Ω) : LubinTateHerbrand K Ω := by
  have hphi : ∀ {π : 𝒪[K]}, Irreducible π → ∀ n : ℕ, 1 ≤ n → ∀ i ≤ n,
      IntervalIntegrable (fun t : ℝ => 1 / (((ramificationGroupReal (ltField Ω π n) t).relIndex
        (ramificationGroup (ltField Ω π n) 0) : ℕ) : ℝ)) MeasureTheory.volume 0 ((resCard K : ℝ) ^ i - 1) ∧
      herbrandPhi (ltField Ω π n) ((resCard K : ℝ) ^ i - 1) = i := by
    intro π hπ n hn
    have hq2 : (2 : ℝ) ≤ resCard K := by exact_mod_cast two_le_resCard K
    exact phi_aux (resCard K : ℝ) hq2 n _ (lt_integrand h h41 hRQ hπ hn)
  refine ⟨fun hπ n i hn hi => (hphi hπ n hn i hi).2, fun {π} hπ n i hn hi => ?_⟩
  have := ltField_isGalois h hπ hn
  set L := ltField Ω π n with hL
  have hq2 : (2 : ℝ) ≤ resCard K := by exact_mod_cast two_le_resCard K
  have hqi : (1 : ℝ) ≤ (resCard K : ℝ) ^ i := one_le_pow₀ (by linarith)
  obtain ⟨hint, hval⟩ := hphi hπ n hn i hi
  have hS : sInf {u : ℝ | 0 ≤ u ∧ (i : ℝ) ≤ herbrandPhi L u} = (resCard K : ℝ) ^ i - 1 := by
    apply IsLeast.csInf_eq
    refine ⟨⟨by linarith, hval.ge⟩, fun u ⟨hu0, hu⟩ => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have hi1 : IntervalIntegrable (fun t : ℝ => 1 / (((ramificationGroupReal L t).relIndex
        (ramificationGroup L 0) : ℕ) : ℝ)) MeasureTheory.volume 0 u :=
      hint.mono_set (by
        rw [Set.uIcc_of_le hu0, Set.uIcc_of_le (by linarith)]
        exact Set.Icc_subset_Icc le_rfl hlt.le)
    have hi2 : IntervalIntegrable (fun t : ℝ => 1 / (((ramificationGroupReal L t).relIndex
        (ramificationGroup L 0) : ℕ) : ℝ)) MeasureTheory.volume u ((resCard K : ℝ) ^ i - 1) :=
      hint.mono_set (by
        rw [Set.uIcc_of_le hlt.le, Set.uIcc_of_le (by linarith)]
        exact Set.Icc_subset_Icc hu0 le_rfl)
    have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on hi2
      (fun x _ => lt_integrand_pos L x) hlt
    have hsub := intervalIntegral.integral_interval_sub_left hint hi1
    have : herbrandPhi L ((resCard K : ℝ) ^ i - 1) - herbrandPhi L u > 0 := by
      unfold herbrandPhi; rw [hsub]; exact hpos
    linarith
  unfold upperRamificationGroup
  have hnl : ¬ ((resCard K : ℝ) ^ i - 1 ≤ -1) := by linarith
  rw [hS, ramificationGroupReal]
  simp only [hnl, ↓reduceIte]
  congr 1
  have : (resCard K : ℝ) ^ i - 1 = ((resCard K ^ i - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by have := two_le_resCard K; omega)), Nat.cast_pow, Nat.cast_one]
  rw [this, Nat.ceil_natCast]

end NumberFieldKB.MilneCFT.LocalCFT