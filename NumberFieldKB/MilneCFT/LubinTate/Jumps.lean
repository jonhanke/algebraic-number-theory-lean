import NumberFieldKB.MilneCFT.LubinTate.Complements

/-!
# Example 4.7: the jumps of $K_{\pi,n}/K$ (Milne, *Class Field Theory*, Chapter I, §4)

For $L = K_{\pi,n}$ ($n \ge 1$), if $G_i \ne G_{i+1}$ then $i = q^k - 1$ for some $0 \le k \le n - 1$, and
$\varphi(i) = k$; in particular the jumps are integers (the Hasse–Arf theorem for $K_{\pi,n}/K$).

Proof (Milne's computation, from Proposition 4.1, Example 4.2 and the bounds on p. 44): by Proposition 4.1,
$G_{q^k - 1} = \chi(U^{(k)})$ for $k \le n$, so $G_{q^n - 1} = 1$, and for $1 \le k < n$ an element of $U^{(k)}$ not in
$U^{(k+1)}$ maps outside $G_{q^k}$, so $G_{q^k} = G_{q^{k+1} - 1}$: $G_i$ is constant on $[q^k, q^{k+1} - 1]$. For
$k = 0$: $(G_1 : G_{q-1})$ divides $(G : \chi(U^{(1)})) = q - 1$ and is a product of indices $(G_j : G_{j+1})$
($j \ge 1$), each dividing $|l|$, a power of $q$; so it is $1$.

**Erratum.** Milne lists $i = 0, q - 1, \dots, q^n - 1$ with $\varphi$-values $1, 2, \dots, n$; the correct list is
$i = q^k - 1$ for $0 \le k \le n - 1$ with values $0, 1, \dots, n - 1$ ($\varphi(q^k - 1) = k$ by Example 4.2, and
$G_{q^n - 1} = 1$).
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- The lower ramification groups decrease: $G_j \subseteq G_i$ for $i \le j$. -/
theorem ramificationGroup_antitone (L : IntermediateField K Ω) [FiniteDimensional K L] {i j : ℕ} (hij : i ≤ j) :
    ramificationGroup L j ≤ ramificationGroup L i := by
  intro σ hσ a ha
  obtain ⟨b, hb, hba⟩ := hσ a ha
  exact ⟨b, Ideal.pow_le_pow_right (by omega) hb, hba⟩

/-- $U^{(n)}/U^{(n)} = 1$. -/
theorem unitFiltrationMod_self (n : ℕ) : unitFiltrationMod (K := K) n n = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨u, rfl, hu⟩
  rw [Subgroup.mem_bot]
  ext
  simp only [Units.coe_map, Units.val_one]
  rw [← map_one (Ideal.Quotient.mk (𝓂[K] ^ n))]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 hu

/-- The index of $U^{(1)}/U^{(n)}$ in $(A/\mathfrak m^n)^\times$ divides $q - 1$ (it is the kernel of reduction to
$(A/\mathfrak m)^\times$). -/
theorem index_unitFiltrationMod_one_dvd (n : ℕ) (hn : 1 ≤ n) :
    (unitFiltrationMod (K := K) n 1).index ∣ resCard K - 1 := by
  let r : (𝒪[K] ⧸ 𝓂[K] ^ n)ˣ →* (𝒪[K] ⧸ 𝓂[K] ^ 1)ˣ :=
    Units.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right hn)).toMonoidHom
  have hker : r.ker ≤ unitFiltrationMod n 1 := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x : 𝒪[K] ⧸ 𝓂[K] ^ n)
    have h1 : Ideal.Quotient.mk (𝓂[K] ^ 1) a = 1 := by
      have := congrArg (fun y : (𝒪[K] ⧸ 𝓂[K] ^ 1)ˣ => (y : 𝒪[K] ⧸ 𝓂[K] ^ 1)) hx
      simp only [r, Units.coe_map, Units.val_one, ← ha] at this
      simpa using this
    have h2 : a - 1 ∈ 𝓂[K] ^ 1 := by
      rw [← map_one (Ideal.Quotient.mk (𝓂[K] ^ 1))] at h1
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 h1
    have h3 : IsUnit a := by
      by_contra hna
      have ha' : a ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal a).2 hna
      have : (1 : 𝒪[K]) ∈ 𝓂[K] := by
        have := Ideal.sub_mem _ ha' (by simpa using h2)
        simp at this
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 this)
    refine ⟨h3.unit, ?_, h2⟩
    ext
    simp [ha]
  have hdvd : r.ker.index ∣ resCard K - 1 := by
    rw [Subgroup.index_ker]
    have h := card_units_quot_maximalIdeal_pow (K := K) 1 le_rfl
    simp only [Nat.sub_self, pow_zero, mul_one] at h
    rw [← h]
    exact Subgroup.card_subgroup_dvd_card r.range
  exact (Subgroup.index_dvd_of_le hker).trans hdvd

/-- $(G_1 : G_j)$ divides $|l|^{j-1}$ for $j \ge 1$ (each $(G_i : G_{i+1})$, $i \ge 1$, divides $|l|$). -/
theorem relIndex_one_dvd (hRQ : RamificationQuotientBounds K Ω) (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsGalois K L] (j : ℕ) :
    (ramificationGroup L (j + 1)).relIndex (ramificationGroup L 1) ∣ Nat.card (residueFieldL L) ^ j := by
  induction j with
  | zero => simp only [zero_add, pow_zero, Subgroup.relIndex_self, dvd_refl]
  | succ j ih =>
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ (ramificationGroup_antitone L (Nat.le_succ _))
      (ramificationGroup_antitone L (by omega)), pow_succ']
    exact Nat.mul_dvd_mul (hRQ.index_succ_dvd L (j + 1) (by omega)) ih

variable (K) in
theorem two_le_resCard : 2 ≤ resCard K := by
  have : Nontrivial 𝓀[K] := inferInstance
  have : Finite 𝓀[K] := inferInstance
  exact Finite.one_lt_card

/-- **Example 4.7** (Milne, *CFT*, I, Example 4.7; proved from Theorem 3.6, Proposition 4.1, Example 4.2 and the
ramification quotient bounds of p. 44): for $L = K_{\pi,n}$ ($n \ge 1$), if $G_i \ne G_{i+1}$ then $i = q^k - 1$ with
$0 \le k \le n - 1$, and $\varphi(i) = k$. **Erratum**: Milne lists $i = 0, q - 1, \dots, q^n - 1$ with values
$1, \dots, n$ (off by one; see the module docstring). -/
@[kb "milne2020cft" "Ch. I, Example 4.7"]
theorem example_4_7 (h : LubinTateExtensionTheorem K Ω) (h41 : LubinTateLowerFiltration K Ω h)
    (h42 : LubinTateHerbrand K Ω) (hRQ : RamificationQuotientBounds K Ω) {π : 𝒪[K]} (hπ : Irreducible π)
    {n : ℕ} (hn : 1 ≤ n) (i : ℕ)
    (hi : ramificationGroup (ltField Ω π n) i ≠ ramificationGroup (ltField Ω π n) (i + 1)) :
    ∃ k < n, i = resCard K ^ k - 1 ∧ herbrandPhi (ltField Ω π n) i = k := by
  have := ltField_isGalois h hπ hn
  set L := ltField Ω π n with hL
  set q := resCard K with hq
  have hq2 : 2 ≤ q := two_le_resCard K
  obtain ⟨χ, hχ⟩ := h.galois hπ n hn
  have hmap := h41.map_eq hπ n hn χ hχ
  have hnot := h41.not_mem hπ n hn χ hχ
  -- `G_{q^n - 1} = 1`
  have hbot : ∀ j, q ^ n - 1 ≤ j → ramificationGroup L j = ⊥ := by
    intro j hj
    rw [eq_bot_iff, ← Subgroup.map_bot χ.toMonoidHom, ← unitFiltrationMod_self n, hmap n le_rfl]
    exact ramificationGroup_antitone L hj
  -- `G_1 ≤ G_{q - 1}`
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
  -- `G_{q^k} ≤ G_{q^{k+1} - 1}` for `k < n`
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
  -- `G_j` is constant on `[q^k, q^{k+1} - 1]`
  have hconst : ∀ k < n, ∀ j, q ^ k ≤ j → j ≤ q ^ (k + 1) - 1 →
      ramificationGroup L j = ramificationGroup L (q ^ (k + 1) - 1) :=
    fun k hk j h1 h2 => le_antisymm ((ramificationGroup_antitone L h1).trans (hstep k hk))
      (ramificationGroup_antitone L h2)
  have hphi : ∀ k ≤ n, herbrandPhi L ((q ^ k - 1 : ℕ) : ℝ) = k := by
    intro k hk
    have : ((q ^ k - 1 : ℕ) : ℝ) = (q : ℝ) ^ k - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
    rw [this]
    exact h42.phi_eq hπ n k hn hk
  have hqk : ∀ k, 1 ≤ q ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  by_cases hin : q ^ n - 1 ≤ i
  · exact absurd ((hbot i hin).trans (hbot (i + 1) (by omega)).symm) hi
  rw [not_le] at hin
  set k := Nat.log q (i + 1) with hk
  have hk1 : q ^ k ≤ i + 1 := Nat.pow_log_le_self q (by omega)
  have hk2 : i + 1 < q ^ (k + 1) := Nat.lt_pow_succ_log_self (by omega) _
  have hkn : k < n := by
    by_contra hkn
    rw [not_lt] at hkn
    have : q ^ n ≤ q ^ k := Nat.pow_le_pow_right (by omega) hkn
    have := hqk n
    omega
  by_cases hik : q ^ k ≤ i
  · exact absurd ((hconst k hkn i hik (by omega)).trans (hconst k hkn (i + 1) (by omega) (by omega)).symm) hi
  · have hi' : i = q ^ k - 1 := by omega
    refine ⟨k, hkn, hi', ?_⟩
    rw [hi']
    exact hphi k hkn.le

/-- **Example 4.7, Hasse–Arf for $K_{\pi,n}$** (Milne, *CFT*, I, Example 4.7: "we have verified the Hasse–Arf theorem
for all these extensions"): the jumps of $K_{\pi,n}/K$ are integers. -/
@[kb "milne2020cft" "Ch. I, Example 4.7 (Hasse-Arf for K_{π,n})"]
theorem example_4_7_hasseArf (h : LubinTateExtensionTheorem K Ω) (h41 : LubinTateLowerFiltration K Ω h)
    (h42 : LubinTateHerbrand K Ω) (hRQ : RamificationQuotientBounds K Ω) {π : 𝒪[K]} (hπ : Irreducible π)
    {n : ℕ} (hn : 1 ≤ n) (i : ℕ)
    (hi : ramificationGroup (ltField Ω π n) i ≠ ramificationGroup (ltField Ω π n) (i + 1)) :
    ∃ k : ℤ, herbrandPhi (ltField Ω π n) i = k := by
  obtain ⟨k, -, -, hk⟩ := example_4_7 h h41 h42 hRQ hπ hn i hi
  exact ⟨k, by rw [hk]; norm_cast⟩

end NumberFieldKB.MilneCFT.LocalCFT
