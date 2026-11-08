import NumberFieldKB.WeilBNT.PField
import NumberFieldKB.WeilBNT.FieldVectorSpaces
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Weil, *Basic Number Theory*, I.§4, Cor. 2, 5, 6 of Thm. 6 and Def. 4: expansions and division algebras

$K$ is a $p$-field (`PField`).

* `weil_I_4_cor2_thm6`: Cor. 2. Let $\zeta\in P$, $\zeta\ne0$, $n=\operatorname{ord}(\zeta)$, and $A$ a full set of
  representatives of $R$ modulo $P^n$. For every $\nu\in\mathbb Z$, every $x\in P^{n\nu}$ is in one and only one way a
  convergent sum $\sum_{i\ge0}a_i\zeta^{i+\nu}$ with all $a_i\in A$.
* `weil_I_4_cor5_thm6`, `weil_I_4_cor5_thm6_aut`, `weil_I_4_cor5_thm6_R`, `weil_I_4_cor5_thm6_P`: Cor. 5. A division
  algebra $K'$ of finite dimension over a commutative $p$-field $K$, with its natural topology (any Hausdorff topology
  making it a topological division ring and a topological vector space over $K$; it is unique by I.§2 Cor. 1 of Thm. 3),
  is a $p$-field; every automorphism of $K'$ over $K$ is a homeomorphism; $R=K\cap R'$ and $P=K\cap P'$.
* `weil_I_4_cor6_thm6`: Cor. 6 and Def. 4. $q'=q^f$ with $f\ge1$ (the modular degree), and $[K':K]=ef$ where $e$ is
  the order of ramification: $\operatorname{mod}_{K'}(\pi)=q'^{-e}$ for a prime element $\pi$ of $K$.
-/

open Topology Filter
open scoped NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

section Cor2

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ}

/-- The residue count $q$ of a $p$-field is at least $2$. -/
theorem two_le_pq (hK : IsPField K p) : 2 ≤ pq hK := by
  obtain ⟨f, hf, hqf⟩ := weil_I_4_thm6_residue hK
  rw [hqf]
  exact hK.1.two_le.trans (Nat.le_self_pow (by omega) p)

/-- $P$ as a left ideal of the ring $R$. -/
def pIdeal (hK : IsPField K p) : Ideal (pR hK) :=
  { (pPAdd hK).toAddSubmonoid with
    smul_mem' := fun c x hx => by
      have hx' : modK K (x : K) < 1 := hx
      show modK K ((c : K) * (x : K)) < 1
      rw [modK_mul]
      exact lt_of_le_of_lt (mul_le_mul' (mem_pR.1 c.2) le_rfl) (by simpa using hx') }

/-- The closed ball $\{x:\operatorname{mod}_K(x)\le m\}$ as an additive submonoid (ultrametric case). -/
def ballAdd (hU : IsUltrametricMod K) (m : ℝ≥0) : AddSubmonoid K where
  carrier := {x | modK K x ≤ m}
  add_mem' {a b} ha hb := (hU a b).trans (max_le ha hb)
  zero_mem' := by simp

/-- A convergent sum of terms of module at most $m$ has module at most $m$. -/
theorem modK_le_of_hasSum (hU : IsUltrametricMod K) {m : ℝ≥0} {f : ℕ → K} {s : K}
    (h : HasSum f s) (hf : ∀ i, modK K (f i) ≤ m) : modK K s ≤ m := by
  have hcl : IsClosed {x : K | modK K x ≤ m} := isClosed_le continuous_modK continuous_const
  exact hcl.mem_of_tendsto h.tendsto_sum_nat
    (Eventually.of_forall fun n => (ballAdd hU m).sum_mem fun i _ => hf i)

/-- Terms bounded by powers of $c<1$ tend to zero. -/
theorem tendsto_zero_of_modK_le_pow {f : ℕ → K} {c : ℝ≥0} (hc : c < 1)
    (hf : ∀ i, modK K (f i) ≤ c ^ i) : Tendsto f atTop (𝓝 0) := by
  rw [hasBasis_nhds_zero_modK.tendsto_right_iff]
  intro m hm
  have h1 : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one zero_le hc
  exact (h1.eventually (gt_mem_nhds hm)).mono fun n hn => (hf n).trans hn.le

/-- Cor. 2 for $\nu=0$, stated for a general bound $c=\operatorname{mod}_K(\zeta)<1$. -/
theorem cor2_core (hK : IsPField K p) {ζ : K} (hζ0 : ζ ≠ 0) {c : ℝ≥0} (hc0 : 0 < c) (hc1 : c < 1)
    (hζ : modK K ζ = c) {A : Set K} (hA : ∀ a ∈ A, modK K a ≤ 1)
    (hrep : ∀ x : K, modK K x ≤ 1 → ∃! a, a ∈ A ∧ modK K (x - a) ≤ c) {y : K}
    (hy : modK K y ≤ 1) :
    ∃! a : ℕ → K, (∀ i, a i ∈ A) ∧ HasSum (fun i : ℕ => a i * ζ ^ i) y := by
  classical
  have hU := isUltrametricMod_of_isPField hK
  have hterm : ∀ (a : ℕ → K), (∀ i, a i ∈ A) → ∀ i, modK K (a i * ζ ^ i) ≤ c ^ i := by
    intro a ha i
    rw [modK_mul, modK_pow, hζ]
    calc modK K (a i) * c ^ i ≤ 1 * c ^ i := mul_le_mul' (hA _ (ha i)) le_rfl
      _ = c ^ i := one_mul _
  have hcle : c ≤ 1 := hc1.le
  -- uniqueness, by induction on the number of digits compared
  have huniq : ∀ N : ℕ, ∀ (y : K) (a b : ℕ → K), (∀ i, a i ∈ A) → (∀ i, b i ∈ A) →
      HasSum (fun i : ℕ => a i * ζ ^ i) y → HasSum (fun i : ℕ => b i * ζ ^ i) y →
      ∀ i < N, a i = b i := by
    intro N
    induction N with
    | zero => intro y a b _ _ _ _ i hi; omega
    | succ N ih =>
      intro y a b ha hb hsa hsb
      -- the tail of a sum
      have tail : ∀ (a : ℕ → K), (∀ i, a i ∈ A) → HasSum (fun i : ℕ => a i * ζ ^ i) y →
          HasSum (fun n : ℕ => a (n + 1) * ζ ^ n) ((y - a 0) * ζ⁻¹) := by
        intro a ha hs
        have h1 := (hasSum_nat_add_iff' 1).2 hs
        simp only [Finset.sum_range_one, pow_zero, mul_one] at h1
        have h2 := h1.mul_right ζ⁻¹
        convert h2 using 1
        funext n
        rw [mul_assoc, pow_succ, mul_assoc, mul_inv_cancel₀ hζ0, mul_one]
      have hyR : modK K y ≤ 1 :=
        modK_le_of_hasSum hU hsa fun i => (hterm a ha i).trans (pow_le_one₀ zero_le hcle)
      have hdiff : ∀ (a : ℕ → K), (∀ i, a i ∈ A) → HasSum (fun i : ℕ => a i * ζ ^ i) y →
          modK K (y - a 0) ≤ c := by
        intro a ha hs
        have h1 := (hasSum_nat_add_iff' 1).2 hs
        simp only [Finset.sum_range_one, pow_zero, mul_one] at h1
        refine modK_le_of_hasSum hU h1 fun n => ?_
        refine (hterm a ha (n + 1)).trans ?_
        calc c ^ (n + 1) = c ^ n * c := pow_succ _ _
          _ ≤ 1 * c := mul_le_mul' (pow_le_one₀ zero_le hcle) le_rfl
          _ = c := one_mul _
      have h0 : a 0 = b 0 := by
        obtain ⟨z, _, hz⟩ := hrep y hyR
        have h1 := hz (a 0) ⟨ha 0, hdiff a ha hsa⟩
        have h2 := hz (b 0) ⟨hb 0, hdiff b hb hsb⟩
        rw [h1, h2]
      have hta := tail a ha hsa
      have htb := tail b hb hsb
      rw [← h0] at htb
      have ih' := ih ((y - a 0) * ζ⁻¹) (fun n => a (n + 1)) (fun n => b (n + 1))
        (fun n => ha _) (fun n => hb _) hta htb
      intro i hi
      rcases i with _ | i
      · exact h0
      · exact ih' i (by omega)
  have hr : ∀ z : K, modK K z ≤ 1 → ∃ a, a ∈ A ∧ modK K (z - a) ≤ c :=
    fun z hz => (hrep z hz).exists
  let r : K → K := fun z => if h : modK K z ≤ 1 then (hr z h).choose else 0
  have hr1 : ∀ z, modK K z ≤ 1 → r z ∈ A ∧ modK K (z - r z) ≤ c := by
    intro z hz
    simp only [r, hz, ↓reduceDIte]
    exact (hr z hz).choose_spec
  let Y : ℕ → K := fun N => Nat.rec y (fun _ yN => (yN - r yN) * ζ⁻¹) N
  have hYs : ∀ N, Y (N + 1) = (Y N - r (Y N)) * ζ⁻¹ := fun N => rfl
  have hYR : ∀ N, modK K (Y N) ≤ 1 := by
    intro N
    induction N with
    | zero => exact hy
    | succ N ih =>
      rw [hYs, modK_mul, modK_inv hζ0, hζ]
      calc modK K (Y N - r (Y N)) * c⁻¹ ≤ c * c⁻¹ := mul_le_mul' (hr1 _ ih).2 le_rfl
        _ = 1 := mul_inv_cancel₀ hc0.ne'
  have hYsum : ∀ N, y = ∑ i ∈ Finset.range N, r (Y i) * ζ ^ i + Y N * ζ ^ N := by
    intro N
    induction N with
    | zero => simp [Y]
    | succ N ih =>
      have h : Y N * ζ ^ N = r (Y N) * ζ ^ N + Y (N + 1) * ζ ^ (N + 1) := by
        rw [hYs, pow_succ', mul_assoc, inv_mul_cancel_left₀ hζ0, sub_mul]
        abel
      rw [Finset.sum_range_succ, add_assoc, ← h]
      exact ih
  have haA : ∀ i, r (Y i) ∈ A := fun i => (hr1 _ (hYR i)).1
  have hlim : Tendsto (fun N => Y N * ζ ^ N) atTop (𝓝 0) := by
    refine tendsto_zero_of_modK_le_pow hc1 fun N => ?_
    rw [modK_mul, modK_pow, hζ]
    calc modK K (Y N) * c ^ N ≤ 1 * c ^ N := mul_le_mul' (hYR N) le_rfl
      _ = c ^ N := one_mul _
  have hsumm : Summable (fun i => r (Y i) * ζ ^ i) :=
    weil_I_4_cor1_thm6 hK (tendsto_zero_of_modK_le_pow hc1 (hterm _ haA))
  have hhas : HasSum (fun i => r (Y i) * ζ ^ i) y := by
    rw [hsumm.hasSum_iff_tendsto_nat]
    have h1 : Tendsto (fun N => y - Y N * ζ ^ N) atTop (𝓝 (y - 0)) :=
      tendsto_const_nhds.sub hlim
    rw [sub_zero] at h1
    refine Tendsto.congr (fun N => ?_) h1
    rw [sub_eq_iff_eq_add]
    exact hYsum N
  exact ⟨fun i => r (Y i), ⟨haA, hhas⟩, fun b ⟨hb, hsb⟩ =>
    funext fun i => huniq (i + 1) y b _ hb haA hsb hhas i (by omega)⟩

@[kb "weil1973bnt" "Ch. I, §4, Cor. 2 of Thm. 6"]
theorem weil_I_4_cor2_thm6 (hK : IsPField K p) {ζ : K} (hζ0 : ζ ≠ 0) {n : ℕ} (hn : 1 ≤ n)
    (hζ : modK K ζ = ((pq hK : ℝ≥0) ^ n)⁻¹) {A : Set K} (hA : A ⊆ pR hK)
    (hrep : ∀ x ∈ pR hK, ∃! a, a ∈ A ∧ modK K (x - a) ≤ ((pq hK : ℝ≥0) ^ n)⁻¹) (ν : ℤ) {x : K}
    (hx : modK K x ≤ ((pq hK : ℝ≥0) ^ ((n : ℤ) * ν))⁻¹) :
    ∃! a : ℕ → K, (∀ i, a i ∈ A) ∧ HasSum (fun i : ℕ => a i * ζ ^ ((i : ℤ) + ν)) x := by
  have hq1 : (1 : ℝ≥0) < (pq hK : ℝ≥0) := by exact_mod_cast two_le_pq hK
  set Q : ℝ≥0 := (pq hK : ℝ≥0) ^ n with hQ
  have hQ1 : 1 < Q := one_lt_pow₀ hq1 (by omega)
  have hQ0 : 0 < Q := lt_trans one_pos hQ1
  have hc0 : 0 < Q⁻¹ := inv_pos.2 hQ0
  have hc1 : Q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hQ1
  have hQν : (pq hK : ℝ≥0) ^ ((n : ℤ) * ν) = Q ^ ν := by
    rw [zpow_mul, zpow_natCast]
  rw [hQν] at hx
  have hy : modK K (x * ζ ^ (-ν)) ≤ 1 := by
    rw [modK_mul, modK_zpow hζ0, hζ, inv_zpow', neg_neg]
    calc modK K x * Q ^ ν ≤ (Q ^ ν)⁻¹ * Q ^ ν := mul_le_mul' hx le_rfl
      _ = 1 := inv_mul_cancel₀ (zpow_pos hQ0 ν).ne'
  have hequiv : ∀ a : ℕ → K, HasSum (fun i : ℕ => a i * ζ ^ ((i : ℤ) + ν)) x ↔
      HasSum (fun i : ℕ => a i * ζ ^ i) (x * ζ ^ (-ν)) := by
    intro a
    constructor
    · intro h
      convert h.mul_right (ζ ^ (-ν)) using 2 with i
      rw [mul_assoc, ← zpow_add₀ hζ0]
      simp
    · intro h
      have h2 := h.mul_right (ζ ^ ν)
      rw [mul_assoc, ← zpow_add₀ hζ0, neg_add_cancel, zpow_zero, mul_one] at h2
      convert h2 using 2 with i
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hζ0]
  obtain ⟨a, ⟨ha, hs⟩, huniq⟩ := cor2_core hK hζ0 hc0 hc1 hζ (A := A)
    (fun a h => mem_pR.1 (hA h)) (fun z hz => hrep z (mem_pR.2 hz)) hy
  exact ⟨a, ⟨ha, (hequiv a).2 hs⟩, fun b ⟨hb, hsb⟩ => huniq b ⟨hb, (hequiv b).1 hsb⟩⟩

end Cor2

section Cor5

open scoped Pointwise
open MeasureTheory

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ}
  {K' : Type*} [DivisionRing K'] [Algebra K K'] [FiniteDimensional K K'] [TopologicalSpace K']
  [IsTopologicalDivisionRing K'] [T2Space K'] [ContinuousSMul K K']

variable (K K') in
/-- The linear isomorphism of `K'` with `Kᵈ` given by a basis. -/
def piEquivK : (Fin (Module.finrank K K') → K) ≃ₗ[K] K' := (Module.finBasis K K').equivFun.symm

theorem isHomeomorph_piEquivK : IsHomeomorph (piEquivK K K') := weil_I_2_thm3_cor1 _

theorem finrank_ne_zero_aux : Module.finrank K K' ≠ 0 := Module.finrank_pos.ne'

/-- The module of $K'$ on $K$ (I.§2, Cor. 2 of Thm. 3), with the hypotheses of `modK_algebraMap`; it is stated
first so that it can be used in Cor. 5. -/
theorem modK_algebraMap_aux [LocallyCompactSpace K'] [(𝓝[≠] (0 : K')).NeBot] (x : K) :
    modK K' (algebraMap K K' x) = modK K x ^ Module.finrank K K' := by
  by_cases hx : x = 0
  · subst hx
    simp [finrank_ne_zero_aux (K := K) (K' := K')]
  have hg0 : algebraMap K K' x ≠ 0 := by simpa using hx
  let u : Kˣ := Units.mk0 x hx
  let g : K'ˣ := Units.mk0 (algebraMap K K' x) hg0
  have h1 : modK K' (algebraMap K K' x) = distribHaarChar K' g := modK_units g
  have h2 : distribHaarChar K' u = modK K x ^ Module.finrank K K' := by
    have := weil_I_2_thm3_cor2_mod (K := K) (V := K') u
    simpa [u] using this
  rw [h1, ← h2]
  borelize K'
  obtain ⟨C, hCc, hC0⟩ := exists_compact_mem_nhds (0 : K')
  let μ : Measure K' := Measure.addHaar
  have hs0 : μ C ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior μ ⟨0, mem_interior_iff_mem_nhds.2 hC0⟩).ne'
  have hs : μ C ≠ ⊤ := hCc.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := C) hs0 hs ?_
  have hset : g • C = u • C := by
    ext y
    simp only [Set.mem_smul_set, Units.smul_def]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, by simp [g, u, Algebra.smul_def]⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, by simp [g, u, Algebra.smul_def]⟩
  rw [hset, ← distribHaarChar_mul μ u C]

/-- Cor. 5: $K'$ is locally compact and nondiscrete, and a $p$-field. -/
@[kb "weil1973bnt" "Ch. I, §4, Cor. 5 of Thm. 6 (K' is a p-field)"]
theorem weil_I_4_cor5_thm6 (hK : IsPField K p) :
    ∃ (_ : LocallyCompactSpace K') (_ : (𝓝[≠] (0 : K')).NeBot), IsPField K' p := by
  have hlc : LocallyCompactSpace K' :=
    (isHomeomorph_piEquivK (K := K) (K' := K')).homeomorph.symm.isOpenEmbedding.locallyCompactSpace
  have hnb : (𝓝[≠] (0 : K')).NeBot := by
    have hcont : Continuous (algebraMap K K') := continuous_algebraMap K K'
    have h : Tendsto (algebraMap K K') (𝓝[≠] (0 : K)) (𝓝[≠] (0 : K')) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := hcont.tendsto 0
        rw [map_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        have : algebraMap K K' x ≠ 0 := by simpa using hx
        exact this
    exact h.neBot
  refine ⟨hlc, hnb, hK.1, ?_⟩
  have := hlc
  have := hnb
  have e : (p : K') = algebraMap K K' (p : K) := (map_natCast _ p).symm
  rw [e, modK_algebraMap_aux]
  exact pow_lt_one₀ zero_le hK.2 (finrank_ne_zero_aux (K := K) (K' := K'))

@[kb "weil1973bnt" "Ch. I, §4, Cor. 5 of Thm. 6 (automorphisms over K are continuous)"]
theorem weil_I_4_cor5_thm6_aut (σ : K' ≃ₐ[K] K') : Continuous σ := by
  let e2 : (Fin (Module.finrank K K') → K) ≃ₗ[K] K' := (piEquivK K K').trans σ.toLinearEquiv
  have h2 : Continuous e2 := (weil_I_2_thm3_cor1 e2).continuous
  have h1 : Continuous (piEquivK K K').symm := by
    have hh := isHomeomorph_piEquivK (K := K) (K' := K')
    convert hh.homeomorph.symm.continuous using 1
    funext y
    have h := hh.homeomorph.apply_symm_apply y
    change (piEquivK K K') (hh.homeomorph.symm y) = y at h
    rw [LinearEquiv.symm_apply_eq]
    exact h.symm
  have : (σ : K' → K') = e2 ∘ (piEquivK K K').symm := by
    funext y
    simp [e2]
  rw [this]
  exact h2.comp h1

/-- Cor. 5, $R=K\cap R'$ (in terms of modules: $\operatorname{mod}_{K'}(x)\le1$ iff $\operatorname{mod}_K(x)\le1$ for
$x\in K$; Weil's identification of $K$ with $K\cdot1_{K'}$). -/
@[kb "weil1973bnt" "Ch. I, §4, Cor. 5 of Thm. 6 (R = K ∩ R')"]
theorem weil_I_4_cor5_thm6_R [LocallyCompactSpace K'] [(𝓝[≠] (0 : K')).NeBot] (x : K) :
    modK K' (algebraMap K K' x) ≤ 1 ↔ modK K x ≤ 1 := by
  rw [modK_algebraMap_aux]
  exact pow_le_one_iff_of_nonneg zero_le (finrank_ne_zero_aux (K := K) (K' := K'))

@[kb "weil1973bnt" "Ch. I, §4, Cor. 5 of Thm. 6 (P = K ∩ P')"]
theorem weil_I_4_cor5_thm6_P [LocallyCompactSpace K'] [(𝓝[≠] (0 : K')).NeBot] (x : K) :
    modK K' (algebraMap K K' x) < 1 ↔ modK K x < 1 := by
  rw [modK_algebraMap_aux]
  exact pow_lt_one_iff_of_nonneg zero_le (finrank_ne_zero_aux (K := K) (K' := K'))

/-- The module of $K'$ on $K$: $\operatorname{mod}_{K'}(x)=\operatorname{mod}_K(x)^{[K':K]}$ (I.§2, Cor. 2 of
Thm. 3, used in Cor. 6). -/
theorem modK_algebraMap [LocallyCompactSpace K'] [(𝓝[≠] (0 : K')).NeBot] (x : K) :
    modK K' (algebraMap K K' x) = modK K x ^ Module.finrank K K' :=
  modK_algebraMap_aux x

/-- The residue field of $K'$ is a vector space over that of $K$, so $q'=q^f$. -/
theorem pq_eq_pow_of_algebra [LocallyCompactSpace K'] [(𝓝[≠] (0 : K')).NeBot] (hK : IsPField K p)
    (hK' : IsPField K' p) : ∃ f : ℕ, pq hK' = pq hK ^ f := by
  classical
  let φ : pR hK →+* pR hK' :=
    { toFun := fun x =>
        ⟨algebraMap K K' x, mem_pR.2 ((weil_I_4_cor5_thm6_R (x : K)).2 (mem_pR.1 x.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hmax : (pIdeal hK).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h => ?_, fun J x hIJ hx hxJ => ?_⟩
    · have h' : modK K ((1 : pR hK) : K) < 1 := h
      simp at h'
    · have hx1 : ¬ modK K (x : K) < 1 := hx
      have hxle : modK K (x : K) ≤ 1 := mem_pR.1 x.2
      have h1 : modK K (x : K) = 1 := le_antisymm hxle (not_lt.1 hx1)
      obtain ⟨-, hinv, hx0⟩ := (weil_I_4_thm6_units hK (x : K)).2 h1
      have := J.mul_mem_left ⟨(x : K)⁻¹, hinv⟩ hxJ
      convert this using 1
      exact Subtype.ext (by simp [hx0])
  let _ : Field (pR hK ⧸ pIdeal hK) := Ideal.Quotient.field _
  let _ : Module (pR hK) (pR hK' ⧸ pIdeal hK') := Module.compHom _ φ
  have htors : Module.IsTorsionBySet (pR hK) (pR hK' ⧸ pIdeal hK') (pIdeal hK) := by
    intro g a
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ g
    have ha : modK K ((a : pR hK) : K) < 1 := a.2
    show (Submodule.Quotient.mk (φ a * r) : pR hK' ⧸ pIdeal hK') = 0
    rw [Submodule.Quotient.mk_eq_zero]
    show modK K' ((algebraMap K K' ((a : pR hK) : K)) * (r : K')) < 1
    rw [modK_mul]
    exact lt_of_le_of_lt (mul_le_mul' le_rfl (mem_pR.1 r.2))
      (by simpa using (weil_I_4_cor5_thm6_P (K' := K') ((a : pR hK) : K)).2 ha)
  let _ : Module (pR hK ⧸ pIdeal hK) (pR hK' ⧸ pIdeal hK') := htors.module
  have : Finite (pR hK ⧸ pIdeal hK) := finite_quotient_pPAdd hK
  have : Finite (pR hK' ⧸ pIdeal hK') := finite_quotient_pPAdd hK'
  let _ := Fintype.ofFinite (pR hK ⧸ pIdeal hK)
  let _ := Fintype.ofFinite (pR hK' ⧸ pIdeal hK')
  refine ⟨Module.finrank (pR hK ⧸ pIdeal hK) (pR hK' ⧸ pIdeal hK'), ?_⟩
  have := Module.card_eq_pow_finrank (K := pR hK ⧸ pIdeal hK) (V := pR hK' ⧸ pIdeal hK')
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at this
  exact this

/-- Cor. 6 and Def. 4: $q'=q^f$, $f\ge1$, and $[K':K]=ef$ where $\operatorname{mod}_{K'}(\pi)=q'^{-e}$, $e\ge1$. -/
@[kb "weil1973bnt" "Ch. I, §4, Cor. 6 of Thm. 6 and Def. 4"]
theorem weil_I_4_cor6_thm6 [LocallyCompactSpace K'] [(𝓝[≠] (0 : K')).NeBot] (hK : IsPField K p)
    (hK' : IsPField K' p) {π : K} (hπ0 : π ≠ 0) (hπ : pP hK = (fun r => π * r) '' (pR hK : Set K)) :
    ∃ e f : ℕ, 1 ≤ e ∧ 1 ≤ f ∧ pq hK' = pq hK ^ f ∧
      modK K' (algebraMap K K' π) = ((pq hK' : ℝ≥0) ^ e)⁻¹ ∧ Module.finrank K K' = e * f := by
  obtain ⟨f, hf⟩ := pq_eq_pow_of_algebra (K := K) (K' := K') hK hK'
  have hd : Module.finrank K K' ≠ 0 := finrank_ne_zero_aux
  have hQ1 : (1 : ℝ≥0) < (pq hK : ℝ≥0) := by exact_mod_cast two_le_pq hK
  have hQ0 : (0 : ℝ≥0) < (pq hK : ℝ≥0) := lt_trans one_pos hQ1
  have hπ' : algebraMap K K' π ≠ 0 := by simpa using hπ0
  obtain ⟨n, hn⟩ := weil_I_4_thm6_range hK' hπ'
  have h1 : modK K' (algebraMap K K' π) = ((pq hK : ℝ≥0)⁻¹) ^ Module.finrank K K' := by
    rw [modK_algebraMap_aux, weil_I_4_thm6_modK_prime hK hπ0 hπ]
  rw [hf] at hn
  have h2 : (pq hK : ℝ≥0) ^ (-(Module.finrank K K' : ℤ)) = (pq hK : ℝ≥0) ^ ((f : ℤ) * n) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, ← h1, hn, zpow_mul, Nat.cast_pow, zpow_natCast]
  have h3 : -(Module.finrank K K' : ℤ) = (f : ℤ) * n :=
    zpow_right_injective₀ hQ0 hQ1.ne' h2
  have hfpos : 1 ≤ f := by
    by_contra hf0
    have : f = 0 := by omega
    subst this
    have h4 := two_le_pq hK'
    rw [hf] at h4
    simp at h4
  have hnneg : n < 0 := by
    by_contra hn0
    have : 0 ≤ (f : ℤ) * n := mul_nonneg (by positivity) (not_lt.1 hn0)
    have : 0 < (Module.finrank K K' : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    omega
  obtain ⟨e, he⟩ : ∃ e : ℕ, n = -(e : ℤ) := ⟨(-n).toNat, by omega⟩
  refine ⟨e, f, by omega, hfpos, hf, ?_, ?_⟩
  · rw [hn, he, zpow_neg, zpow_natCast]
    simp [hf]
  · have : (Module.finrank K K' : ℤ) = (e : ℤ) * f := by rw [he] at h3; linarith
    exact_mod_cast this

end Cor5

end NumberFieldKB.WeilBNT.FieldModule
