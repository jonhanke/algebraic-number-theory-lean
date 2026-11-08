import NumberFieldKB.WeilBNT.FieldClassification
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-!
# Weil, *Basic Number Theory*, I.§4, Thm. 6 and its Corollaries 1–4: structure of $p$-fields

$K$ is a $p$-field (I.§3, Def. 2: a nondiscrete locally compact division ring, commutative or not, with
$\operatorname{mod}_K(p\cdot1_K)<1$), `hK : IsPField K p`.

* `pR hK`: the subring $R=\{x:\operatorname{mod}_K(x)\le1\}$; `pP`: the set $P=\{x:\operatorname{mod}_K(x)<1\}$.
* `weil_I_4_thm6_isCompact`, `weil_I_4_thm6_isOpen`, `weil_I_4_thm6_maximal`: $R$ is a compact open subring,
  containing every multiplicatively closed relatively compact subset of $K$ (the unique maximal compact subring).
* `weil_I_4_thm6_units`: $R^\times=\{x:\operatorname{mod}_K(x)=1\}$ is the group of invertible elements of $R$.
* `weil_I_4_thm6_prime`: there is $\pi\in K^\times$ with $P=\pi R=R\pi$ (so $P$ is a two-sided ideal; it is the unique
  maximal left, right or two-sided ideal of $R$ because $R\setminus P=R^\times$).
* `weil_I_4_thm6_residue`: $q=[R:P]$ (the number of elements of $k=R/P$) is a power $p^f$, $f\ge1$, of $p$;
  `weil_I_4_thm6_modK_prime`: $\operatorname{mod}_K(\pi)=q^{-1}$; `weil_I_4_thm6_range`: every value of the module on
  $K^\times$ is a power $q^n$, $n\in\mathbb Z$. ($k$ is a finite field of characteristic $p$: a finite division ring is
  commutative by Wedderburn's theorem, Mathlib `littleWedderburn`; we record $q$ as an index of additive groups.)
* `weil_I_4_cor1_thm6`: Cor. 1, a series whose terms tend to $0$ is (unconditionally) summable.
* `weil_I_4_cor3_thm6`: Cor. 3, a ring automorphism of $K$ which is a homeomorphism maps $R$ onto $R$ and $P$ onto
  $P$, and preserves the module ($\operatorname{mod}_K(\sigma x)=\operatorname{mod}_K(x)$, equivalently it has module
  $1$ as an automorphism of the additive group of $K$: `weil_I_4_cor3_thm6_measure`).
* `weil_I_4_cor4_thm6`: Cor. 4 for $p$-fields, $x\mapsto ax$ and $x\mapsto xa$ have the same module.
-/

open MeasureTheory Topology Filter
open scoped NNReal ENNReal Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ}

/-- The module of an integer power of a nonzero element. -/
theorem modK_zpow {x : K} (hx : x ≠ 0) (n : ℤ) : modK K (x ^ n) = modK K x ^ n := by
  rcases n with n | n
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact modK_pow x n
  · rw [zpow_negSucc, zpow_negSucc, modK_inv (pow_ne_zero _ hx), modK_pow]

/-- The maximal compact subring $R=\{x:\operatorname{mod}_K(x)\le1\}$ of a $p$-field (I.§4, Thm. 6). -/
def pR (hK : IsPField K p) : Subring K where
  carrier := {x | modK K x ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, modK_mul] at *
    exact mul_le_one' ha hb
  one_mem' := by simp
  add_mem' {a b} ha hb :=
    (isUltrametricMod_of_isPField hK a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, modK_neg] at *; exact ha

/-- $P=\{x:\operatorname{mod}_K(x)<1\}$. -/
def pP (_hK : IsPField K p) : Set K := {x | modK K x < 1}

theorem mem_pR {hK : IsPField K p} {x : K} : x ∈ pR hK ↔ modK K x ≤ 1 := Iff.rfl

theorem mem_pP {hK : IsPField K p} {x : K} : x ∈ pP hK ↔ modK K x < 1 := Iff.rfl

/-- The values of the module below $1$ are bounded away from $1$ (the image of the module is discrete). -/
theorem exists_gap (hK : IsPField K p) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x : K, modK K x < 1 → (modK K x : ℝ) ≤ c := by
  obtain ⟨ε, hε, h⟩ := discrete_range_of_isUltrametricMod (isUltrametricMod_of_isPField hK)
  have hm1 := min_le_left ε (1 / 2)
  have hm2 := min_le_right ε (1 / 2)
  have hm3 : 0 < min ε (1 / 2) := lt_min hε (by norm_num)
  refine ⟨1 - min ε (1 / 2), by linarith, by linarith, fun x hx => ?_⟩
  by_cases h0 : x = 0
  · subst h0
    simp only [modK_zero, NNReal.coe_zero]
    linarith
  · by_contra hlt
    push Not at hlt
    have hx' : (modK K x : ℝ) < 1 := by exact_mod_cast hx
    have habs : |(modK K ((Units.mk0 x h0 : Kˣ) : K) : ℝ) - 1| < ε := by
      rw [abs_lt]
      constructor
      · show -ε < (modK K x : ℝ) - 1
        linarith
      · show (modK K x : ℝ) - 1 < ε
        linarith
    have := h _ habs
    exact absurd this (ne_of_lt hx)

/-- A power of a generator of the values below $1$ gives every value of the module. -/
theorem exists_zpow_of_gen {π : K} (hπ0 : π ≠ 0) (hπ1 : modK K π < 1)
    (hmax : ∀ x : K, modK K x < 1 → modK K x ≤ modK K π) {x : K} (hx : x ≠ 0) :
    ∃ n : ℤ, modK K x = modK K π ^ n := by
  set g := modK K π with hg
  have hgpos : 0 < g := modK_pos_iff.2 hπ0
  have hg0 : g ≠ 0 := hgpos.ne'
  have hinv : 1 < g⁻¹ := (one_lt_inv₀ hgpos).2 hπ1
  have htpos : 0 < modK K x := modK_pos_iff.2 hx
  obtain ⟨m, hm1, hm2⟩ := NNReal.exists_mem_Ico_zpow htpos.ne' hinv
  have hu : 0 < g ^ m := zpow_pos hgpos m
  rw [inv_zpow] at hm1
  rw [inv_zpow, zpow_add_one₀ hg0] at hm2
  have h1 : 1 ≤ modK K x * g ^ m :=
    calc (1 : ℝ≥0) = (g ^ m)⁻¹ * g ^ m := (inv_mul_cancel₀ hu.ne').symm
      _ ≤ modK K x * g ^ m := mul_le_mul' hm1 le_rfl
  have h2 : modK K x * g ^ m * g < 1 :=
    calc modK K x * g ^ m * g = modK K x * (g ^ m * g) := mul_assoc _ _ _
      _ < (g ^ m * g)⁻¹ * (g ^ m * g) := mul_lt_mul_of_pos_right hm2 (mul_pos hu hgpos)
      _ = 1 := inv_mul_cancel₀ (mul_pos hu hgpos).ne'
  have hy0 : x * π ^ m ≠ 0 := mul_ne_zero hx (zpow_ne_zero m hπ0)
  have hy : modK K (x * π ^ m) = modK K x * g ^ m := by
    rw [modK_mul, modK_zpow hπ0]
  have ha : modK K x * g ^ m = 1 := by
    by_contra hne
    have hgt : 1 < modK K x * g ^ m := lt_of_le_of_ne h1 (Ne.symm hne)
    have h3 : modK K (x * π ^ m)⁻¹ < 1 := by
      rw [modK_inv hy0, hy]
      exact inv_lt_one_of_one_lt₀ hgt
    have h4 := hmax _ h3
    rw [modK_inv hy0, hy] at h4
    have h5 : 1 ≤ g * (modK K x * g ^ m) :=
      calc (1 : ℝ≥0) = (modK K x * g ^ m)⁻¹ * (modK K x * g ^ m) :=
            (inv_mul_cancel₀ (by positivity)).symm
        _ ≤ g * (modK K x * g ^ m) := mul_le_mul' h4 le_rfl
    rw [mul_comm g] at h5
    exact absurd h2 (not_lt.2 h5)
  refine ⟨-m, ?_⟩
  rw [zpow_neg]
  exact eq_inv_of_mul_eq_one_left ha

/-- There is a generator of the values of the module below $1$ (Weil's proof of Thm. 6). -/
theorem exists_gen (hK : IsPField K p) :
    ∃ π : K, π ≠ 0 ∧ modK K π < 1 ∧ (∀ x : K, modK K x < 1 → modK K x ≤ modK K π) := by
  obtain ⟨c, hc0, hc1, hc⟩ := exists_gap hK
  set T : Set ℝ≥0 := Set.range (modK K) ∩ {v | (v : ℝ) ≤ c} with hT
  have hTc : IsClosed T :=
    isClosed_range_modK.inter (isClosed_le NNReal.continuous_coe continuous_const)
  have hT0 : T.Nonempty := ⟨0, ⟨0, modK_zero⟩, by simpa using hc0⟩
  have hTb : BddAbove T := ⟨1, fun v hv => by
    have h1 : (v : ℝ) ≤ c := hv.2
    have : (v : ℝ) ≤ 1 := by linarith
    exact_mod_cast this⟩
  have hmem := hTc.csSup_mem hT0 hTb
  obtain ⟨π, hπ⟩ := hmem.1
  have hup : ∀ x : K, modK K x < 1 → modK K x ≤ sSup T := fun x hx =>
    le_csSup hTb ⟨⟨x, rfl⟩, hc x hx⟩
  obtain ⟨a, ha0, ha1⟩ := exists_modK_pos_lt (K := K) (ε := 1) one_pos
  have hpos : 0 < modK K π := by
    rw [hπ]
    exact lt_of_lt_of_le ha0 (hup a ha1)
  refine ⟨π, modK_pos_iff.1 hpos, ?_, fun x hx => by rw [hπ]; exact hup x hx⟩
  have h1 : ((sSup T : ℝ≥0) : ℝ) ≤ c := hmem.2
  rw [hπ]
  exact_mod_cast lt_of_le_of_lt h1 hc1

theorem pP_eq_left {hK : IsPField K p} {π : K} (hπ0 : π ≠ 0) (hπ1 : modK K π < 1)
    (hmax : ∀ x : K, modK K x < 1 → modK K x ≤ modK K π) :
    pP hK = (fun r => π * r) '' (pR hK : Set K) := by
  ext x
  constructor
  · intro hx
    refine ⟨π⁻¹ * x, ?_, mul_inv_cancel_left₀ hπ0 x⟩
    show modK K (π⁻¹ * x) ≤ 1
    rw [modK_mul, modK_inv hπ0, inv_mul_le_iff₀ (modK_pos_iff.2 hπ0), mul_one]
    exact hmax x hx
  · rintro ⟨r, hr, rfl⟩
    show modK K (π * r) < 1
    rw [modK_mul]
    calc modK K π * modK K r ≤ modK K π * 1 := mul_le_mul' le_rfl hr
      _ < 1 := by simpa using hπ1

theorem pP_eq_right {hK : IsPField K p} {π : K} (hπ0 : π ≠ 0) (hπ1 : modK K π < 1)
    (hmax : ∀ x : K, modK K x < 1 → modK K x ≤ modK K π) :
    pP hK = (fun r => r * π) '' (pR hK : Set K) := by
  ext x
  constructor
  · intro hx
    refine ⟨x * π⁻¹, ?_, inv_mul_cancel_right₀ hπ0 x⟩
    show modK K (x * π⁻¹) ≤ 1
    rw [modK_mul, modK_inv hπ0, mul_inv_le_iff₀ (modK_pos_iff.2 hπ0), one_mul]
    exact hmax x hx
  · rintro ⟨r, hr, rfl⟩
    show modK K (r * π) < 1
    rw [modK_mul]
    calc modK K r * modK K π ≤ 1 * modK K π := mul_le_mul' hr le_rfl
      _ < 1 := by simpa using hπ1

@[kb "weil1973bnt" "Ch. I, §4, Thm. 6 (R is compact)"]
theorem weil_I_4_thm6_isCompact (hK : IsPField K p) : IsCompact (pR hK : Set K) :=
  isCompact_modK_le 1

@[kb "weil1973bnt" "Ch. I, §4, Thm. 6 (R and P are open)"]
theorem weil_I_4_thm6_isOpen (hK : IsPField K p) : IsOpen (pR hK : Set K) ∧ IsOpen (pP hK) := by
  refine ⟨?_, isOpen_lt continuous_modK continuous_const⟩
  exact AddSubgroup.isOpen_of_mem_nhds (pR hK).toAddSubgroup
    (hasBasis_nhds_zero_modK.mem_of_mem one_pos)

@[kb "weil1973bnt" "Ch. I, §4, Thm. 6 (R is the maximal compact subring)"]
theorem weil_I_4_thm6_maximal (hK : IsPField K p) {S : Set K} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (hc : IsCompact (closure S)) : S ⊆ pR hK := by
  intro x hx
  by_contra hxR
  have h1 : 1 < modK K x := not_le.1 hxR
  obtain ⟨M, hM⟩ := (hc.image continuous_modK).bddAbove
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h1
  have hmem : ∀ n : ℕ, x ^ (n + 1) ∈ S := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ]; exact hS _ ih _ hx
  have h2 := hM ⟨x ^ (n + 1), subset_closure (hmem n), rfl⟩
  rw [modK_pow] at h2
  have h3 : modK K x ^ n ≤ modK K x ^ (n + 1) := pow_le_pow_right₀ h1.le (Nat.le_succ n)
  exact absurd (hn.trans_le (h3.trans h2)) (lt_irrefl _)

@[kb "weil1973bnt" "Ch. I, §4, Thm. 6 (the units of R)"]
theorem weil_I_4_thm6_units (hK : IsPField K p) (x : K) :
    (x ∈ pR hK ∧ x⁻¹ ∈ pR hK ∧ x ≠ 0) ↔ modK K x = 1 := by
  constructor
  · rintro ⟨h1, h2, h0⟩
    have h1' : modK K x ≤ 1 := h1
    have h2' : modK K x⁻¹ ≤ 1 := h2
    rw [modK_inv h0] at h2'
    have hpos := modK_pos_iff.2 h0
    exact le_antisymm h1' (by simpa [inv_le_one₀ hpos] using h2')
  · intro h
    have h0 : x ≠ 0 := by
      rintro rfl
      simp at h
    refine ⟨h.le, ?_, h0⟩
    show modK K x⁻¹ ≤ 1
    rw [modK_inv h0, h]
    simp

@[kb "weil1973bnt" "Ch. I, §4, Thm. 6 (P = πR = Rπ)"]
theorem weil_I_4_thm6_prime (hK : IsPField K p) :
    ∃ π : K, π ≠ 0 ∧ pP hK = (fun r => π * r) '' (pR hK : Set K) ∧
      pP hK = (fun r => r * π) '' (pR hK : Set K) := by
  obtain ⟨π, hπ0, hπ1, hmax⟩ := exists_gen hK
  exact ⟨π, hπ0, pP_eq_left hπ0 hπ1 hmax, pP_eq_right hπ0 hπ1 hmax⟩

/-- $P$ as an additive subgroup of $R$. -/
def pPAdd (hK : IsPField K p) : AddSubgroup (pR hK) where
  carrier := {x | modK K (x : K) < 1}
  add_mem' {a b} ha hb :=
    lt_of_le_of_lt (isUltrametricMod_of_isPField hK a b) (max_lt ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, NegMemClass.coe_neg, modK_neg] at *
    exact ha

/-- Weil's $q$, the module of $K$ (Def. 3): the number of elements of $k=R/P$. -/
def pq (hK : IsPField K p) : ℕ := (pPAdd hK).index

/-- $P$ is open in $R$. -/
theorem isOpen_pPAdd (hK : IsPField K p) : IsOpen ((pPAdd hK : AddSubgroup (pR hK)) : Set (pR hK)) :=
  isOpen_lt (continuous_modK.comp continuous_subtype_val) continuous_const

/-- The quotient $R/P$ is finite since $R$ is compact and $P$ is open. -/
theorem finite_quotient_pPAdd (hK : IsPField K p) : Finite (↥(pR hK) ⧸ pPAdd hK) := by
  haveI : CompactSpace (pR hK) := isCompact_iff_compactSpace.1 (weil_I_4_thm6_isCompact hK)
  exact (pPAdd hK).quotient_finite_of_isOpen (isOpen_pPAdd hK)

/-- $R$ is the disjoint union of $q$ translates of $P$, hence $\alpha(R)=q\,\alpha(P)$. -/
theorem measure_pR_eq [MeasurableSpace K] [BorelSpace K] (hK : IsPField K p) (μ : Measure K)
    [μ.IsAddHaarMeasure] : μ (pR hK : Set K) = (pq hK : ℝ≥0∞) * μ (pP hK) := by
  haveI := finite_quotient_pPAdd hK
  haveI : Fintype (↥(pR hK) ⧸ pPAdd hK) := Fintype.ofFinite _
  let A : (↥(pR hK) ⧸ pPAdd hK) → Set K := fun a =>
    (fun x : K => -(((a.out : pR hK)) : K) + x) ⁻¹' (pP hK)
  have hPopen : IsOpen (pP hK) := (weil_I_4_thm6_isOpen hK).2
  have hAmeas : ∀ a, MeasurableSet (A a) := fun a =>
    (hPopen.preimage (continuous_const.add continuous_id)).measurableSet
  have hAeq : ∀ a, μ (A a) = μ (pP hK) := fun a => measure_preimage_add μ _ _
  have hcover : (pR hK : Set K) = ⋃ a, A a := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      refine ⟨QuotientAddGroup.mk (⟨x, hx⟩ : pR hK), ?_⟩
      have h := (QuotientAddGroup.eq (s := pPAdd hK)).1
        (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (⟨x, hx⟩ : pR hK) : ↥(pR hK) ⧸ pPAdd hK))
      exact h
    · rintro ⟨a, ha⟩
      have h1 : modK K (-(((a.out : pR hK)) : K) + x) ≤ 1 := le_of_lt ha
      have h2 : x = ((a.out : pR hK) : K) + (-(((a.out : pR hK)) : K) + x) := by abel
      rw [h2]
      exact (pR hK).add_mem (a.out : pR hK).2 h1
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    apply hab
    have hxa' : modK K (-(((a.out : pR hK)) : K) + x) < 1 := hxa
    have hxb' : modK K (-(((b.out : pR hK)) : K) + x) < 1 := hxb
    have hmem : (-(a.out : pR hK) + (b.out : pR hK)) ∈ pPAdd hK := by
      show modK K ((-(a.out : pR hK) + (b.out : pR hK) : pR hK) : K) < 1
      have e : (((-(a.out : pR hK) + (b.out : pR hK) : pR hK)) : K) =
          (-(((a.out : pR hK)) : K) + x) + -(-(((b.out : pR hK)) : K) + x) := by
        push_cast
        abel
      rw [e]
      exact lt_of_le_of_lt (isUltrametricMod_of_isPField hK _ _)
        (max_lt hxa' (by rw [modK_neg]; exact hxb'))
    have := (QuotientAddGroup.eq (s := pPAdd hK)).2 hmem
    rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this
  rw [hcover, measure_iUnion hdisj hAmeas, tsum_fintype]
  simp only [hAeq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  simp [pq, AddSubgroup.index, Nat.card_eq_fintype_card]

@[kb "weil1973bnt" "Ch. I, §4, Thm. 6 (the residue field has q = p^f elements)"]
theorem weil_I_4_thm6_residue (hK : IsPField K p) : ∃ f : ℕ, 1 ≤ f ∧ pq hK = p ^ f := by
  haveI := finite_quotient_pPAdd hK
  haveI : Fintype (↥(pR hK) ⧸ pPAdd hK) := Fintype.ofFinite _
  haveI hpf : Fact p.Prime := ⟨hK.1⟩
  have hkill : ∀ g : ↥(pR hK) ⧸ pPAdd hK, p • g = 0 := by
    intro g
    induction g using QuotientAddGroup.induction_on with
    | H x =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      show modK K ((p • x : pR hK) : K) < 1
      have e : ((p • x : pR hK) : K) = (p : K) * (x : K) := by simp
      rw [e, modK_mul]
      calc modK K (p : K) * modK K (x : K) ≤ modK K (p : K) * 1 := mul_le_mul' le_rfl x.2
        _ < 1 := by simpa using hK.2
  have hcard0 : Nat.card (↥(pR hK) ⧸ pPAdd hK) ≠ 0 := Nat.card_pos.ne'
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hcard0 (p := p) (fun {d} hd hdvd => by
    haveI : Fact d.Prime := ⟨hd⟩
    rw [Nat.card_eq_fintype_card] at hdvd
    obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card d hdvd
    have : d ∣ p := hg ▸ addOrderOf_dvd_of_nsmul_eq_zero (hkill g)
    exact (Nat.prime_dvd_prime_iff_eq hd hK.1).1 this)
  obtain ⟨f, hq⟩ : ∃ f : ℕ, pq hK = p ^ f := ⟨_, hpow⟩
  refine ⟨f, ?_, hq⟩
  by_contra hf
  have hf0 : f = 0 := by omega
  rw [hf0, pow_zero] at hq
  have htop := AddSubgroup.index_eq_one.1 hq
  have h1 : (1 : pR hK) ∈ pPAdd hK := by rw [htop]; trivial
  have h2 : modK K ((1 : pR hK) : K) < 1 := h1
  simp at h2

@[kb "weil1973bnt" "Ch. I, §4, Thm. 6 (mod π = 1/q)"]
theorem weil_I_4_thm6_modK_prime (hK : IsPField K p) {π : K} (hπ : π ≠ 0)
    (hP : pP hK = (fun r => π * r) '' (pR hK : Set K)) : (modK K π : ℝ≥0) = (pq hK : ℝ≥0)⁻¹ := by
  borelize K
  let μ : Measure K := Measure.addHaar
  have hRo := (weil_I_4_thm6_isOpen hK).1
  have hRpos : μ (pR hK : Set K) ≠ 0 := (hRo.measure_pos μ ⟨0, (pR hK).zero_mem⟩).ne'
  have hRtop : μ (pR hK : Set K) ≠ ∞ := (weil_I_4_thm6_isCompact hK).measure_lt_top.ne
  have h1 := measure_pR_eq hK μ
  have h2 : μ (pP hK) = modK K π * μ (pR hK : Set K) := by
    have e : (fun r => π * r) '' (pR hK : Set K) = π • (pR hK : Set K) := rfl
    rw [hP, e, modK_mul_measure μ hπ]
  rw [h2] at h1
  have h3 : μ (pR hK : Set K) * ((pq hK : ℝ≥0∞) * modK K π) = μ (pR hK : Set K) * 1 := by
    rw [mul_one]
    nth_rewrite 2 [h1]
    ring
  have h4 := (ENNReal.mul_right_inj hRpos hRtop).1 h3
  have h5 : (pq hK : ℝ≥0) * modK K π = 1 := by exact_mod_cast h4
  exact eq_inv_of_mul_eq_one_right h5

@[kb "weil1973bnt" "Ch. I, §4, Thm. 6 (the image of the module is generated by q)"]
theorem weil_I_4_thm6_range (hK : IsPField K p) {x : K} (hx : x ≠ 0) :
    ∃ n : ℤ, modK K x = (pq hK : ℝ≥0) ^ n := by
  obtain ⟨π, hπ0, hπ1, hmax⟩ := exists_gen hK
  have hq := weil_I_4_thm6_modK_prime hK hπ0 (pP_eq_left hπ0 hπ1 hmax)
  obtain ⟨n, hn⟩ := exists_zpow_of_gen hπ0 hπ1 hmax hx
  exact ⟨-n, by rw [hn, hq, inv_zpow']⟩

@[kb "weil1973bnt" "Ch. I, §4, Cor. 1 of Thm. 6"]
theorem weil_I_4_cor1_thm6 (hK : IsPField K p) {x : ℕ → K} (hx : Tendsto x atTop (𝓝 0)) :
    Summable x := by
  have hU := isUltrametricMod_of_isPField hK
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace K := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace K
  haveI : NonarchimedeanAddGroup K := ⟨fun U hUn => by
    obtain ⟨m, hm, hsub⟩ := hasBasis_nhds_zero_modK.mem_iff.1 hUn
    let H : AddSubgroup K :=
      { carrier := {y : K | modK K y ≤ m}
        add_mem' := fun {a b} ha hb => (hU a b).trans (max_le ha hb)
        zero_mem' := by simp
        neg_mem' := fun {a} ha => by
          show modK K (-a) ≤ m
          rw [modK_neg]; exact ha }
    have hHo : IsOpen (H : Set K) :=
      AddSubgroup.isOpen_of_mem_nhds H (hasBasis_nhds_zero_modK.mem_of_mem hm)
    exact ⟨⟨H, hHo⟩, hsub⟩⟩
  exact NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by rwa [Nat.cofinite_eq_atTop])

/-- A continuous ring endomorphism maps $R$ into $R$ (the image of $R$ is compact and multiplicatively
closed). -/
theorem map_pR_le (hK : IsPField K p) (f : K →+* K) (hf : Continuous f) {x : K}
    (hx : modK K x ≤ 1) : modK K (f x) ≤ 1 := by
  have hc : IsCompact (f '' (pR hK : Set K)) := (weil_I_4_thm6_isCompact hK).image hf
  have := weil_I_4_thm6_maximal hK (S := f '' (pR hK : Set K))
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact ⟨a * b, (pR hK).mul_mem ha hb, map_mul f a b⟩)
    (by rw [hc.isClosed.closure_eq]; exact hc) ⟨x, hx, rfl⟩
  exact this

theorem modK_σ_le (hK : IsPField K p) (σ : K ≃+* K) (hσ : Continuous σ) (hσ' : Continuous σ.symm)
    (x : K) : modK K (σ x) ≤ 1 ↔ modK K x ≤ 1 := by
  refine ⟨fun h => ?_, map_pR_le hK σ.toRingHom hσ⟩
  have := map_pR_le hK σ.symm.toRingHom hσ' h
  simpa using this

theorem modK_σ_eq_one (hK : IsPField K p) (σ : K ≃+* K) (hσ : Continuous σ)
    (hσ' : Continuous σ.symm) (x : K) : modK K (σ x) = 1 ↔ modK K x = 1 := by
  rw [← weil_I_4_thm6_units hK, ← weil_I_4_thm6_units hK]
  have e : σ x⁻¹ = (σ x)⁻¹ := map_inv₀ σ x
  have h1 := modK_σ_le hK σ hσ hσ' x
  have h2 := modK_σ_le hK σ hσ hσ' x⁻¹
  rw [e] at h2
  simp only [mem_pR]
  rw [h1, h2, map_ne_zero]

theorem modK_σ_lt (hK : IsPField K p) (σ : K ≃+* K) (hσ : Continuous σ) (hσ' : Continuous σ.symm)
    (x : K) : modK K (σ x) < 1 ↔ modK K x < 1 := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, modK_σ_le hK σ hσ hσ', ne_eq, ne_eq, modK_σ_eq_one hK σ hσ hσ' x]

@[kb "weil1973bnt" "Ch. I, §4, Cor. 3 of Thm. 6 (the module is preserved)"]
theorem weil_I_4_cor3_thm6 (hK : IsPField K p) (σ : K ≃+* K) (hσ : Continuous σ) (hσ' : Continuous σ.symm)
    (x : K) : modK K (σ x) = modK K x := by
  obtain ⟨π, hπ0, hπ1, hmax⟩ := exists_gen hK
  have hσπ0 : σ π ≠ 0 := by simpa using hπ0
  have hlt := modK_σ_lt hK σ hσ hσ'
  -- `σ π` has the same module as `π`
  have hge : modK K π ≤ modK K (σ π) := by
    have h1 : modK K (σ.symm π) < 1 := by
      rw [← hlt, σ.apply_symm_apply]; exact hπ1
    have h2 : σ.symm π ∈ pP hK := h1
    rw [pP_eq_left (hK := hK) hπ0 hπ1 hmax] at h2
    obtain ⟨r, hr, hrπ⟩ := h2
    have h3 : π = σ π * σ r := by
      have := congrArg σ hrπ
      simpa using this.symm
    have h4 : modK K (σ r) ≤ 1 := (modK_σ_le hK σ hσ hσ' r).2 hr
    calc modK K π = modK K (σ π) * modK K (σ r) := by rw [← modK_mul, ← h3]
      _ ≤ modK K (σ π) * 1 := mul_le_mul' le_rfl h4
      _ = modK K (σ π) := mul_one _
  have hσπ : modK K (σ π) = modK K π := le_antisymm (hmax _ ((hlt π).2 hπ1)) hge
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨n, hn⟩ := exists_zpow_of_gen hπ0 hπ1 hmax hx
  have hu : modK K (x * π ^ (-n)) = 1 := by
    rw [modK_mul, modK_zpow hπ0, hn, zpow_neg]
    exact mul_inv_cancel₀ (zpow_ne_zero n (modK_pos_iff.2 hπ0).ne')
  have hxe : x = (x * π ^ (-n)) * π ^ n := by
    rw [mul_assoc, ← zpow_add₀ hπ0]; simp
  have hσu := (modK_σ_eq_one hK σ hσ hσ' _).2 hu
  calc modK K (σ x) = modK K (σ (x * π ^ (-n)) * (σ π) ^ n) := by
        conv_lhs => rw [hxe]
        rw [map_mul, map_zpow₀]
    _ = modK K x := by
        rw [modK_mul, hσu, one_mul, modK_zpow hσπ0, hσπ, ← hn]

@[kb "weil1973bnt" "Ch. I, §4, Cor. 3 of Thm. 6 (R and P are preserved)"]
theorem weil_I_4_cor3_thm6_RP (hK : IsPField K p) (σ : K ≃+* K) (hσ : Continuous σ)
    (hσ' : Continuous σ.symm) : σ '' (pR hK : Set K) = pR hK ∧ σ '' pP hK = pP hK := by
  have h := weil_I_4_cor3_thm6 hK σ hσ hσ'
  constructor
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show modK K (σ x) ≤ 1
      rw [h]; exact hx
    · intro hy
      refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
      show modK K (σ.symm y) ≤ 1
      have := h (σ.symm y)
      rw [σ.apply_symm_apply] at this
      rw [← this]; exact hy
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show modK K (σ x) < 1
      rw [h]; exact hx
    · intro hy
      refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
      show modK K (σ.symm y) < 1
      have := h (σ.symm y)
      rw [σ.apply_symm_apply] at this
      rw [← this]; exact hy

@[kb "weil1973bnt" "Ch. I, §4, Cor. 3 of Thm. 6 (module 1 as an additive automorphism)"]
theorem weil_I_4_cor3_thm6_measure (hK : IsPField K p) [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [μ.IsAddHaarMeasure] [μ.Regular] (σ : K ≃+* K) (hσ : Continuous σ) (hσ' : Continuous σ.symm)
    (s : Set K) : μ (σ '' s) = μ s := by
  let φ : K ≃ₜ+ K := { σ.toAddEquiv with continuous_toFun := hσ, continuous_invFun := hσ' }
  have hφ : ∀ X : Set K, (addEquivAddHaarChar φ : ℝ≥0∞) * μ (σ ⁻¹' X) = μ X := fun X => by
    have := addEquivAddHaarChar_smul_preimage μ (X := X) φ
    rwa [ENNReal.smul_def, smul_eq_mul] at this
  have hR : σ ⁻¹' (pR hK : Set K) = pR hK := by
    ext x
    show modK K (σ x) ≤ 1 ↔ modK K x ≤ 1
    rw [weil_I_4_cor3_thm6 hK σ hσ hσ']
  have hRo := (weil_I_4_thm6_isOpen hK).1
  have hRpos : μ (pR hK : Set K) ≠ 0 := (hRo.measure_pos μ ⟨0, (pR hK).zero_mem⟩).ne'
  have hRtop : μ (pR hK : Set K) ≠ ∞ := (weil_I_4_thm6_isCompact hK).measure_lt_top.ne
  have hc : (addEquivAddHaarChar φ : ℝ≥0∞) = 1 := by
    have := hφ (pR hK : Set K)
    rw [hR] at this
    rw [mul_comm] at this
    exact (ENNReal.mul_right_inj hRpos hRtop).1 (by rw [this, mul_one])
  have := hφ (σ '' s)
  rw [hc, one_mul, σ.injective.preimage_image] at this
  exact this.symm

/-- Cor. 4 for $p$-fields: $\alpha(Xa)=\operatorname{mod}_K(a)\,\alpha(X)$, i.e. right multiplication by $a$ has the
same module as left multiplication. -/
@[kb "weil1973bnt" "Ch. I, §4, Cor. 4 of Thm. 6 (p-fields)"]
theorem weil_I_4_cor4_thm6 (hK : IsPField K p) [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [μ.IsAddHaarMeasure] [μ.Regular] {a : K} (ha : a ≠ 0) (s : Set K) :
    μ ((fun x => x * a) '' s) = modK K a * μ s := by
  let σ : K ≃+* K :=
    { toFun := fun x => a⁻¹ * x * a
      invFun := fun x => a * x * a⁻¹
      left_inv := fun x => by simp [mul_assoc, ha]
      right_inv := fun x => by simp [mul_assoc, ha]
      map_mul' := fun x y => by simp [mul_assoc, ha]
      map_add' := fun x y => by simp [mul_add, add_mul] }
  have hσ : Continuous σ := by
    show Continuous (fun x : K => a⁻¹ * x * a)
    fun_prop
  have hσ' : Continuous σ.symm := by
    show Continuous (fun x : K => a * x * a⁻¹)
    fun_prop
  have hset : (fun x => x * a) '' s = a • (σ '' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨σ x, ⟨x, hx, rfl⟩, ?_⟩
      show a * (a⁻¹ * x * a) = x * a
      simp [mul_assoc, ha]
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      show x * a = a * (a⁻¹ * x * a)
      simp [mul_assoc, ha]
  rw [hset, ← modK_mul_measure μ ha, weil_I_4_cor3_thm6_measure hK μ σ hσ hσ']

end NumberFieldKB.WeilBNT.FieldModule
