import NumberFieldKB.WeilBNT.PField
import NumberFieldKB.WeilBNT.FieldVectorSpaces
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Weil, *Basic Number Theory*, II.§1: norms on vector spaces over a $p$-field

$K$ is a $p$-field (`hK : IsPField K p`, commutative or not; `PField`), $V$ a left vector space of finite dimension over
$K$ with its natural topology (any Hausdorff topological vector space structure; it is unique by I.§2, Cor. 1 of
Thm. 3, `FieldVectorSpaces`).

* `IsKNorm`: Def. 1, a $K$-norm: $N(v)=0$ iff $v=0$, $N(xv)=\operatorname{mod}_K(x)N(v)$, ultrametric.
* `weil_II_1_prop1`: Prop. 1, a $K$-norm is continuous, the balls $N(v)\le r$ ($r>0$) are compact and form a basis of
  neighbourhoods of $0$ (so $N$ defines the natural topology).
* `weil_II_1_cor1_prop1`: Cor. 1, a compact subset of $V\setminus\{0\}$ meets every line through $0$.
* `weil_II_1_cor2_prop1`: Cor. 2, a continuous function on $V\setminus\{0\}$ invariant under $K^\times$ has a maximum.
* `weil_II_1_cor3_prop1`, `weil_II_1_cor3_prop1_dualNorm`: Cor. 3, the supremum of
  $\operatorname{mod}_K(f(v))/N(v)$ is attained, and is the least $c$ with $\operatorname{mod}_K(f(v))\le cN(v)$.
* `IsNOrthogonal`: text p. 25–26, $N$-orthogonal subspaces; `weil_II_1_prop2`: Prop. 2.
* `weil_II_1_prop3`, `weil_II_1_prop3_flag`: Prop. 3 (a splitting into lines for which $N$ is the sup-norm, adapted to
  a given flag); `weil_II_1_cor_prop3`: its Corollary; `weil_II_1_prop4`: Prop. 4 (two norms are simultaneously
  diagonalizable).
-/

open Topology Filter
open scoped NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ}
  {V : Type*} [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul K V] [T2Space V] [FiniteDimensional K V]

/-- Def. 1: a $K$-norm on $V$. -/
structure IsKNorm (N : V → ℝ≥0) : Prop where
  eq_zero_iff : ∀ v, N v = 0 ↔ v = 0
  smul : ∀ (x : K) (v : V), N (x • v) = modK K x * N v
  add_le : ∀ v w, N (v + w) ≤ max (N v) (N w)

/-- The module of a $p$-field exceeds one. -/
theorem one_lt_pq_norms (hK : IsPField K p) : (1 : ℝ≥0) < (pq hK : ℝ≥0) := by
  obtain ⟨f, hf, h⟩ := weil_I_4_thm6_residue hK
  have : 1 < pq hK := by rw [h]; exact Nat.one_lt_pow (by omega) hK.1.one_lt
  exact_mod_cast this

/-- Scaling a positive number into the interval `[q⁻¹, 1]` by a value of the module. -/
theorem exists_scale (hK : IsPField K p) {t : ℝ≥0} (ht : 0 < t) :
    ∃ a : K, a ≠ 0 ∧ (pq hK : ℝ≥0)⁻¹ ≤ modK K a * t ∧ modK K a * t ≤ 1 := by
  have hq := one_lt_pq_norms hK
  have hq0 : (pq hK : ℝ≥0) ≠ 0 := (zero_lt_one.trans hq).ne'
  obtain ⟨π, hπ0, hP, -⟩ := weil_I_4_thm6_prime hK
  have hmod := weil_I_4_thm6_modK_prime hK hπ0 hP
  obtain ⟨n, hn⟩ := NNReal.exists_mem_Ico_zpow (inv_ne_zero ht.ne') hq
  refine ⟨π ^ (-n), zpow_ne_zero _ hπ0, ?_⟩
  have hm : modK K (π ^ (-n)) = (pq hK : ℝ≥0) ^ n := by
    rw [modK_zpow hπ0, hmod, inv_zpow', neg_neg]
  rw [hm]
  refine ⟨?_, ?_⟩
  · have h2 := mul_lt_mul_of_pos_right hn.2 ht
    rw [inv_mul_cancel₀ ht.ne', zpow_add_one₀ hq0] at h2
    calc ((pq hK : ℝ≥0))⁻¹ = ((pq hK : ℝ≥0))⁻¹ * 1 := (mul_one _).symm
      _ ≤ ((pq hK : ℝ≥0))⁻¹ * ((pq hK : ℝ≥0) ^ n * (pq hK : ℝ≥0) * t) := by gcongr
      _ = (pq hK : ℝ≥0) ^ n * t := by field_simp
  · calc (pq hK : ℝ≥0) ^ n * t ≤ t⁻¹ * t := mul_le_mul_of_nonneg_right hn.1 (zero_le)
      _ = 1 := inv_mul_cancel₀ ht.ne'

namespace IsKNorm

variable {N : V → ℝ≥0}

theorem map_zero' (hN : IsKNorm (K := K) N) : N 0 = 0 := (hN.eq_zero_iff 0).2 rfl

theorem map_neg' (hN : IsKNorm (K := K) N) (v : V) : N (-v) = N v := by
  have h := hN.smul (-1 : K) v
  rwa [neg_one_smul, modK_neg, modK_one, one_mul] at h

theorem pos (hN : IsKNorm (K := K) N) {v : V} (hv : v ≠ 0) : 0 < N v :=
  pos_iff_ne_zero.2 fun h => hv ((hN.eq_zero_iff v).1 h)

/-- The ultrametric inequality for finite sums. -/
theorem sum_le (hN : IsKNorm (K := K) N) {ι : Type*} (s : Finset ι) (w : ι → V) :
    N (∑ i ∈ s, w i) ≤ s.sup fun i => N (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hN.map_zero']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sup_insert]
    exact (hN.add_le _ _).trans (sup_le_sup le_rfl ih)

theorem add_eq_of_lt (hN : IsKNorm (K := K) N) {v w : V} (h : N w < N v) : N (v + w) = N v := by
  apply le_antisymm
  · exact (hN.add_le v w).trans (max_le le_rfl h.le)
  · have := hN.add_le (v + w) (-w)
    rw [add_neg_cancel_right, hN.map_neg'] at this
    rcases le_max_iff.1 this with h1 | h1
    · exact h1
    · exact absurd h (not_lt.2 h1)

theorem continuous_of_continuousAt_zero (hN : IsKNorm (K := K) N) (h0 : ContinuousAt N 0) :
    Continuous N := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · rw [hx]; exact h0
  · have hpos := hN.pos hx
    have hlim : Tendsto (fun y : V => y - x) (𝓝 x) (𝓝 0) := by
      simpa using (continuous_sub_right x).tendsto x
    have h0' : Tendsto N (𝓝 0) (𝓝 0) := by
      have := h0
      rwa [ContinuousAt, hN.map_zero'] at this
    have hev : ∀ᶠ y in 𝓝 x, N (y - x) < N x :=
      (h0'.comp hlim).eventually (gt_mem_nhds hpos)
    refine (continuousAt_const (y := N x)).congr (hev.mono fun y hy => ?_)
    have := hN.add_eq_of_lt hy
    rw [add_sub_cancel] at this
    exact this.symm

end IsKNorm

/-- A linear isomorphism from `Kⁿ` onto `V` is a homeomorphism (Cor. 1 of Thm. 3), with the inverse
continuous. -/
theorem exists_equiv_cont :
    ∃ (n : ℕ) (e : (Fin n → K) ≃ₗ[K] V), Continuous e ∧ Continuous e.symm := by
  refine ⟨Module.finrank K V, (Module.finBasis K V).equivFun.symm, ?_⟩
  set e : (Fin (Module.finrank K V) → K) ≃ₗ[K] V := (Module.finBasis K V).equivFun.symm
  have he : IsHomeomorph e := weil_I_2_thm3_cor1 e
  refine ⟨he.continuous, ?_⟩
  have h : ∀ y, e.symm y = he.homeomorph.symm y := fun y =>
    e.injective (by rw [e.apply_symm_apply]; exact (he.homeomorph.apply_symm_apply y).symm)
  have : (⇑e.symm) = ⇑he.homeomorph.symm := funext h
  rw [this]
  exact he.homeomorph.symm.continuous

theorem box_mem_nhds {n : ℕ} {m : ℝ≥0} (hm : 0 < m) :
    {x : Fin n → K | ∀ i, modK K (x i) ≤ m} ∈ 𝓝 (0 : Fin n → K) := by
  have : ∀ i : Fin n, ∀ᶠ x in 𝓝 (0 : Fin n → K), modK K (x i) ≤ m := fun i => by
    have h1 : {y : K | modK K y ≤ m} ∈ 𝓝 (0 : K) := hasBasis_nhds_zero_modK.mem_of_mem hm
    exact (continuous_apply i : Continuous fun x : Fin n → K => x i).continuousAt.preimage_mem_nhds
      (t := {y : K | modK K y ≤ m}) h1
  exact Filter.eventually_all.2 this

theorem exists_box {n : ℕ} {s : Set (Fin n → K)} (hs : s ∈ 𝓝 (0 : Fin n → K)) :
    ∃ m : ℝ≥0, 0 < m ∧ ∀ x : Fin n → K, (∀ i, modK K (x i) ≤ m) → x ∈ s := by
  rw [nhds_pi, Filter.mem_pi] at hs
  obtain ⟨I, hI, t, ht, hIU⟩ := hs
  have h1 : ∀ i, ∃ m : ℝ≥0, 0 < m ∧ {y : K | modK K y ≤ m} ⊆ t i := fun i =>
    hasBasis_nhds_zero_modK.mem_iff.1 (by simpa using ht i)
  choose m hm hsub using h1
  refine ⟨(∑ i, (m i)⁻¹ + 1)⁻¹, by positivity, fun x hx => hIU fun i _ => hsub i ?_⟩
  refine (hx i).trans ?_
  rw [inv_le_comm₀ (by positivity) (hm i)]
  exact (Finset.single_le_sum (f := fun j => (m j)⁻¹) (fun j _ => zero_le) (Finset.mem_univ i)).trans le_self_add

/-- A coordinate expansion `e x = ∑ xᵢ • e(eᵢ)`. -/
theorem equiv_apply_eq_sum {n : ℕ} (e : (Fin n → K) ≃ₗ[K] V) (x : Fin n → K) :
    e x = ∑ i, x i • e (Pi.single i 1) := by
  have h1 : ∑ i, x i • (Pi.single i (1 : K) : Fin n → K) = x := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [← h1]
  simp [map_sum]

/-- Upper bound: `N (∑ xᵢ vᵢ) ≤ C * m` when all `modK xᵢ ≤ m`. -/
theorem norm_le_mul {N : V → ℝ≥0} (hN : IsKNorm (K := K) N) {n : ℕ} (e : (Fin n → K) ≃ₗ[K] V) :
    ∃ C : ℝ≥0, ∀ (x : Fin n → K) (m : ℝ≥0), (∀ i, modK K (x i) ≤ m) → N (e x) ≤ C * m := by
  refine ⟨Finset.univ.sup fun i => N (e (Pi.single i 1)), fun x m hx => ?_⟩
  rw [equiv_apply_eq_sum]
  refine (hN.sum_le _ _).trans (Finset.sup_le fun i _ => ?_)
  rw [hN.smul, mul_comm]
  exact mul_le_mul' (Finset.le_sup (f := fun i => N (e (Pi.single i 1))) (Finset.mem_univ i)) (hx i)

theorem continuous_of_equiv {N : V → ℝ≥0} (hN : IsKNorm (K := K) N) {n : ℕ}
    (e : (Fin n → K) ≃ₗ[K] V) (hes : Continuous e.symm) : Continuous N := by
  obtain ⟨C, hC⟩ := norm_le_mul hN e
  refine hN.continuous_of_continuousAt_zero ?_
  rw [ContinuousAt, hN.map_zero']
  rw [tendsto_order]
  refine ⟨fun a ha => absurd ha (not_lt_zero), fun a ha => ?_⟩
  obtain ⟨m, hm, hCm⟩ := exists_pos_mul_lt ha C
  have hB := box_mem_nhds (K := K) (n := n) hm
  have hB' : ∀ᶠ v in 𝓝 (0 : V), e.symm v ∈ {x : Fin n → K | ∀ i, modK K (x i) ≤ m} := by
    have := hes.continuousAt (x := 0)
    rw [ContinuousAt, map_zero] at this
    exact this.eventually_mem hB
  refine hB'.mono fun v hv => ?_
  have := hC (e.symm v) m hv
  rw [e.apply_symm_apply] at this
  exact this.trans_lt hCm

/-- Lower bound: `c * modK xᵢ ≤ N (e x)`. -/
theorem exists_lower {N : V → ℝ≥0} (hN : IsKNorm (K := K) N) {n : ℕ} (e : (Fin n → K) ≃ₗ[K] V)
    (hcont : Continuous fun x => N (e x)) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (x : Fin n → K) (i : Fin n), c * modK K (x i) ≤ N (e x) := by
  have hSc := isCompact_unitSphere (K := K) n
  obtain ⟨c, hc, hS⟩ : ∃ c : ℝ≥0, 0 < c ∧ ∀ y ∈ unitSphere K n, c ≤ N (e y) := by
    rcases (unitSphere K n).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨y0, hy0, hmin⟩ := hSc.exists_isMinOn h hcont.continuousOn
      refine ⟨N (e y0), hN.pos ?_, fun y hy => hmin hy⟩
      intro h0
      have : y0 = 0 := e.injective (by rw [h0, map_zero])
      obtain ⟨_, i, hi⟩ := hy0
      simp [this] at hi
  refine ⟨c, hc, fun x i => ?_⟩
  by_cases hxi : x i = 0
  · simp [hxi]
  obtain ⟨h, -, hh⟩ := Finset.exists_max_image Finset.univ (fun i => modK K (x i))
    ⟨i, Finset.mem_univ _⟩
  have hpos0 : 0 < modK K (x i) := modK_pos_iff.2 hxi
  have hpos : 0 < modK K (x h) := lt_of_lt_of_le hpos0 (hh i (Finset.mem_univ _))
  have hxh : x h ≠ 0 := modK_pos_iff.1 hpos
  set y : Fin n → K := (x h)⁻¹ • x with hy
  have hyS : y ∈ unitSphere K n := by
    refine ⟨fun j => ?_, h, ?_⟩
    · simp only [hy, Pi.smul_apply, smul_eq_mul, modK_mul, modK_inv hxh]
      rw [← div_eq_inv_mul]
      exact (div_le_one hpos).2 (hh j (Finset.mem_univ _))
    · simp only [hy, Pi.smul_apply, smul_eq_mul, modK_mul, modK_inv hxh]
      exact (inv_mul_cancel₀ hpos.ne').ge
  have h1 := hS y hyS
  rw [hy, map_smul, hN.smul, modK_inv hxh, le_inv_mul_iff₀ hpos] at h1
  calc c * modK K (x i) ≤ c * modK K (x h) := mul_le_mul_of_nonneg_left (hh i (Finset.mem_univ _)) (zero_le)
    _ = modK K (x h) * c := mul_comm _ _
    _ ≤ N (e x) := h1

/-- Every finite-dimensional space carries a $K$-norm (the sup norm in a basis). -/
theorem exists_kNorm (hK : IsPField K p) : ∃ N : V → ℝ≥0, IsKNorm (K := K) N := by
  obtain ⟨n, e, -, -⟩ := exists_equiv_cont (K := K) (V := V)
  refine ⟨fun v => Finset.univ.sup fun i => modK K (e.symm v i), ?_, ?_, ?_⟩
  · intro v
    constructor
    · intro h
      have : e.symm v = 0 := funext fun i => modK_eq_zero_iff.1 (le_antisymm
        (h ▸ Finset.le_sup (f := fun i => modK K (e.symm v i)) (Finset.mem_univ i)) zero_le)
      simpa using congrArg e this
    · rintro rfl
      simp
  · intro a v
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, modK_mul]
    rw [NNReal.mul_finset_sup]
  · intro v w
    refine Finset.sup_le fun i _ => ?_
    simp only [map_add, Pi.add_apply]
    exact (isUltrametricMod_of_isPField hK _ _).trans (max_le_max
      (Finset.le_sup (f := fun i => modK K (e.symm v i)) (Finset.mem_univ i))
      (Finset.le_sup (f := fun i => modK K (e.symm w i)) (Finset.mem_univ i)))

@[kb "weil1973bnt" "Ch. II, §1, Prop. 1"]
theorem weil_II_1_prop1 (hK : IsPField K p) {N : V → ℝ≥0} (hN : IsKNorm (K := K) N) :
    Continuous N ∧ (∀ r : ℝ≥0, IsCompact {v | N v ≤ r}) ∧
      (𝓝 (0 : V)).HasBasis (fun r : ℝ≥0 => 0 < r) (fun r => {v | N v ≤ r}) := by
  obtain ⟨n, e, he, hes⟩ := exists_equiv_cont (K := K) (V := V)
  have hNc : Continuous N := continuous_of_equiv hN e hes
  obtain ⟨c, hc, hcl⟩ := exists_lower hN e (hNc.comp he)
  refine ⟨hNc, fun r => ?_, ?_⟩
  · have hcompact : IsCompact {x : Fin n → K | N (e x) ≤ r} := by
      refine (isCompact_univ_pi (fun _ : Fin n => isCompact_modK_le (K := K) (r / c))).of_isClosed_subset
        (isClosed_le (hNc.comp he) continuous_const) ?_
      intro x hx i _
      show modK K (x i) ≤ r / c
      rw [le_div_iff₀ hc, mul_comm]
      exact (hcl x i).trans hx
    have : {v : V | N v ≤ r} = e '' {x | N (e x) ≤ r} := by
      ext v
      constructor
      · intro hv
        exact ⟨e.symm v, by simpa using hv, by simp⟩
      · rintro ⟨x, hx, rfl⟩
        exact hx
    rw [this]
    exact hcompact.image he
  · refine ⟨fun t => ⟨fun ht => ?_, fun ⟨r, hr, hsub⟩ => ?_⟩⟩
    · have hpre : e ⁻¹' t ∈ 𝓝 (0 : Fin n → K) := by
        have := he.continuousAt (x := 0)
        rw [ContinuousAt, map_zero] at this
        exact this ht
      obtain ⟨m, hm, hmt⟩ := exists_box hpre
      refine ⟨c * m, mul_pos hc hm, fun v hv => ?_⟩
      have := hmt (e.symm v) (fun i => ?_)
      · simpa using this
      · have h1 := hcl (e.symm v) i
        rw [e.apply_symm_apply] at h1
        have : c * modK K (e.symm v i) ≤ c * m := h1.trans hv
        exact le_of_mul_le_mul_left this hc
    · have : {v : V | N v < r} ∈ 𝓝 (0 : V) :=
        (isOpen_lt hNc continuous_const).mem_nhds (by simpa [hN.map_zero'] using hr)
      exact Filter.mem_of_superset (Filter.mem_of_superset this
        (fun v (hv : N v < r) => (le_of_lt hv : N v ≤ r))) hsub

/-- Linear forms on a finite-dimensional space are continuous (via Thm. 3). -/
theorem continuous_linearForm (f : V →ₗ[K] K) : Continuous f := by
  obtain ⟨n, e, he, hes⟩ := exists_equiv_cont (K := K) (V := V)
  have h : Continuous fun x : Fin n → K => f (e x) := by
    have : (fun x : Fin n → K => f (e x)) = fun x => ∑ i, x i * f (e (Pi.single i 1)) := by
      funext x
      rw [equiv_apply_eq_sum, map_sum]
      simp
    rw [this]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
  have : (f : V → K) = (fun x : Fin n → K => f (e x)) ∘ e.symm := by
    funext v; simp
  rw [this]
  exact h.comp hes

@[kb "weil1973bnt" "Ch. II, §1, Cor. 1 of Prop. 1"]
theorem weil_II_1_cor1_prop1 (hK : IsPField K p) :
    ∃ A : Set V, IsCompact A ∧ (0 : V) ∉ A ∧ ∀ v : V, v ≠ 0 → ∃ a : K, a ≠ 0 ∧ a • v ∈ A := by
  obtain ⟨N, hN⟩ := exists_kNorm (K := K) (V := V) hK
  obtain ⟨hNc, hcpt, -⟩ := weil_II_1_prop1 hK hN
  have hq := one_lt_pq_norms hK
  have hqi : 0 < ((pq hK : ℝ≥0))⁻¹ := inv_pos.2 (zero_lt_one.trans hq)
  refine ⟨{v | ((pq hK : ℝ≥0))⁻¹ ≤ N v ∧ N v ≤ 1}, ?_, ?_, ?_⟩
  · have h1 : IsClosed {v : V | ((pq hK : ℝ≥0))⁻¹ ≤ N v} :=
      isClosed_le (f := fun _ : V => ((pq hK : ℝ≥0))⁻¹) (g := N) continuous_const hNc
    have h2 : IsClosed {v : V | N v ≤ 1} :=
      isClosed_le (f := N) (g := fun _ : V => (1 : ℝ≥0)) hNc continuous_const
    exact (hcpt 1).of_isClosed_subset (h1.inter h2) fun v hv => hv.2
  · rintro ⟨h, -⟩
    rw [hN.map_zero'] at h
    exact absurd h (not_le.2 hqi)
  · intro v hv
    obtain ⟨a, ha0, h1, h2⟩ := exists_scale hK (hN.pos hv)
    exact ⟨a, ha0, by rw [Set.mem_ofPred_eq, hN.smul]; exact ⟨h1, h2⟩⟩

@[kb "weil1973bnt" "Ch. II, §1, Cor. 2 of Prop. 1"]
theorem weil_II_1_cor2_prop1 (hK : IsPField K p) [Nontrivial V] {φ : V → ℝ}
    (hφ : ContinuousOn φ {0}ᶜ) (hinv : ∀ (a : K) (v : V), a ≠ 0 → v ≠ 0 → φ (a • v) = φ v) :
    ∃ v₁ : V, v₁ ≠ 0 ∧ ∀ v, v ≠ 0 → φ v ≤ φ v₁ := by
  obtain ⟨A, hAc, hA0, hAs⟩ := weil_II_1_cor1_prop1 (K := K) (V := V) hK
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨a, ha, haA⟩ := hAs v hv
  have hAne : A.Nonempty := ⟨_, haA⟩
  have hsub : A ⊆ {0}ᶜ := fun x hx h => hA0 (by rw [Set.mem_singleton_iff] at h; exact h ▸ hx)
  obtain ⟨v₁, hv₁, hmax⟩ := hAc.exists_isMaxOn hAne (hφ.mono hsub)
  refine ⟨v₁, fun h => hA0 (h ▸ hv₁), fun v hv => ?_⟩
  obtain ⟨a, ha, haA⟩ := hAs v hv
  have : φ (a • v) ≤ φ v₁ := hmax haA
  rw [hinv a v ha hv] at this
  exact this

@[kb "weil1973bnt" "Ch. II, §1, Cor. 3 of Prop. 1"]
theorem weil_II_1_cor3_prop1 (hK : IsPField K p) [Nontrivial V] {N : V → ℝ≥0} (hN : IsKNorm (K := K) N)
    (f : V →ₗ[K] K) :
    ∃ v₁ : V, v₁ ≠ 0 ∧ ∀ v, v ≠ 0 → modK K (f v) / N v ≤ modK K (f v₁) / N v₁ := by
  obtain ⟨hNc, -, -⟩ := weil_II_1_prop1 hK hN
  have hφ : ContinuousOn (fun v => ((modK K (f v) / N v : ℝ≥0) : ℝ)) {0}ᶜ := by
    have : ContinuousOn (fun v => modK K (f v) / N v) {0}ᶜ :=
      ((continuous_modK.comp (continuous_linearForm f)).continuousOn).div hNc.continuousOn
        (fun v hv => (hN.pos hv).ne')
    exact NNReal.continuous_coe.comp_continuousOn this
  obtain ⟨v₁, hv₁, hmax⟩ := weil_II_1_cor2_prop1 hK
    (φ := fun v => ((modK K (f v) / N v : ℝ≥0) : ℝ)) hφ (by
      intro a v ha hv
      simp only [map_smul, smul_eq_mul, modK_mul, hN.smul]
      rw [mul_div_mul_left _ _ (modK_pos_iff.2 ha).ne'])
  exact ⟨v₁, hv₁, fun v hv => by exact_mod_cast hmax v hv⟩

/-- Cor. 3, second part: $N^*(f)=\sup_v\operatorname{mod}_K(f(v))/N(v)$ is the least $c$ with
$\operatorname{mod}_K(f(v))\le c\,N(v)$ for all $v$. -/
@[kb "weil1973bnt" "Ch. II, §1, Cor. 3 of Prop. 1 (the dual norm)"]
theorem weil_II_1_cor3_prop1_dualNorm (hK : IsPField K p) [Nontrivial V] {N : V → ℝ≥0}
    (hN : IsKNorm (K := K) N) (f : V →ₗ[K] K) :
    ∃ c : ℝ≥0, (∀ v, modK K (f v) ≤ c * N v) ∧ ∀ c' : ℝ≥0, (∀ v, modK K (f v) ≤ c' * N v) → c ≤ c' := by
  obtain ⟨v₁, hv₁, hmax⟩ := weil_II_1_cor3_prop1 hK hN f
  have hpos := hN.pos hv₁
  refine ⟨modK K (f v₁) / N v₁, fun v => ?_, fun c' hc' => ?_⟩
  · by_cases hv : v = 0
    · simp [hv]
    · rw [← div_le_iff₀ (hN.pos hv)]
      exact hmax v hv
  · rw [div_le_iff₀ hpos]
    exact hc' v₁

/-- Text p. 26: subspaces $V',V''$ are $N$-orthogonal if $V=V'\oplus V''$ and $N(v'+v'')=\sup(N(v'),N(v''))$. -/
def IsNOrthogonal (N : V → ℝ≥0) (W W' : Submodule K V) : Prop :=
  IsCompl W W' ∧ ∀ w ∈ W, ∀ w' ∈ W', N (w + w') = max (N w) (N w')

theorem IsNOrthogonal.symm {N : V → ℝ≥0} {W W' : Submodule K V} (h : IsNOrthogonal N W W') :
    IsNOrthogonal N W' W := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1.symm, fun w' hw' w hw => by rw [add_comm, max_comm]; exact h2 w hw w' hw'⟩

theorem exists_decomp {f : V →ₗ[K] K} {w₁ : V} (hfw : f w₁ ≠ 0) (v : V) :
    ∃ h ∈ LinearMap.ker f, ∃ c : K, v = h + c • w₁ := by
  refine ⟨v - (f v * (f w₁)⁻¹) • w₁, ?_, f v * (f w₁)⁻¹, by abel⟩
  simp [LinearMap.mem_ker, mul_assoc, inv_mul_cancel₀ hfw]

theorem isCompl_ker_span {f : V →ₗ[K] K} {w₁ : V} (hfw : f w₁ ≠ 0) :
    IsCompl (LinearMap.ker f) (K ∙ w₁) := by
  refine ⟨Submodule.disjoint_def.2 fun x hx hx' => ?_, Submodule.codisjoint_iff_exists_add_eq.2 fun z => ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx'
    have h0 : f (a • w₁) = 0 := hx
    rw [map_smul, smul_eq_mul] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · simp [h]
    · exact absurd h hfw
  · obtain ⟨h, hh, c, hc⟩ := exists_decomp hfw z
    exact ⟨h, c • w₁, hh, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), hc.symm⟩

/-- Prop. 2: the hyperplane $\ker f$ and the line $Kw_1$ are $N$-orthogonal iff $w_1$ maximizes
$\operatorname{mod}_K(f(v))/N(v)$ (Weil's definition of orthogonality on p. 25). -/
@[kb "weil1973bnt" "Ch. II, §1, Prop. 2"]
theorem weil_II_1_prop2 (hK : IsPField K p) {N : V → ℝ≥0} (hN : IsKNorm (K := K) N) {f : V →ₗ[K] K}
    (hf : f ≠ 0) {w₁ : V} (hw₁ : w₁ ≠ 0) :
    (∀ v, v ≠ 0 → modK K (f v) / N v ≤ modK K (f w₁) / N w₁) ↔
      IsNOrthogonal N (LinearMap.ker f) (K ∙ w₁) := by
  have hNw₁ := hN.pos hw₁
  constructor
  · intro hmax
    have hfw : f w₁ ≠ 0 := by
      intro h0
      apply hf
      ext v
      by_contra hv
      have hv0 : v ≠ 0 := fun h => hv (by simp [h])
      have h1 := hmax v hv0
      rw [h0, modK_zero, zero_div, nonpos_iff_eq_zero, div_eq_zero_iff] at h1
      rcases h1 with h1 | h1
      · exact hv (modK_eq_zero_iff.1 h1)
      · exact (hN.pos hv0).ne' h1
    have hm : 0 < modK K (f w₁) := modK_pos_iff.2 hfw
    refine ⟨isCompl_ker_span hfw, ?_⟩
    intro h hh w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    by_cases hc : c = 0
    · simp [hc, hN.map_zero']
    have hfh : f h = 0 := hh
    have hfv : f (h + c • w₁) = c * f w₁ := by simp [hfh]
    have hv0 : h + c • w₁ ≠ 0 := by
      intro h0
      have := congrArg f h0
      rw [hfv, map_zero] at this
      rcases mul_eq_zero.1 this with h | h
      · exact hc h
      · exact hfw h
    have hvpos := hN.pos hv0
    have key := hmax _ hv0
    rw [hfv, modK_mul, div_le_div_iff₀ hvpos hNw₁] at key
    have hNw : N (c • w₁) ≤ N (h + c • w₁) := by
      rw [hN.smul]
      have : modK K (f w₁) * (modK K c * N w₁) ≤ modK K (f w₁) * N (h + c • w₁) := by
        calc modK K (f w₁) * (modK K c * N w₁) = modK K c * modK K (f w₁) * N w₁ := by ring
          _ ≤ _ := key
      exact le_of_mul_le_mul_left this hm
    have hNh : N h ≤ N (h + c • w₁) := by
      have := hN.add_le (h + c • w₁) (-(c • w₁))
      rw [add_neg_cancel_right, hN.map_neg'] at this
      exact this.trans (max_le le_rfl hNw)
    exact le_antisymm (hN.add_le _ _) (max_le hNh hNw)
  · rintro ⟨hcompl, hn⟩ v hv
    have hfw : f w₁ ≠ 0 := by
      intro h0
      have h1 : w₁ ∈ LinearMap.ker f := h0
      have h2 : w₁ ∈ K ∙ w₁ := Submodule.mem_span_singleton_self w₁
      exact hw₁ (Submodule.disjoint_def.1 hcompl.disjoint w₁ h1 h2)
    have hm : 0 < modK K (f w₁) := modK_pos_iff.2 hfw
    obtain ⟨h, hh, c, rfl⟩ := exists_decomp hfw v
    have hfh : f h = 0 := hh
    have hfv : f (h + c • w₁) = c * f w₁ := by simp [hfh]
    rw [hfv, modK_mul]
    by_cases hc : c = 0
    · simp [hc]
    have hcm : 0 < modK K c := modK_pos_iff.2 hc
    have h3 := hn h hh (c • w₁) (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    have hNv : modK K c * N w₁ ≤ N (h + c • w₁) := by
      rw [h3, ← hN.smul]; exact le_max_right _ _
    calc modK K c * modK K (f w₁) / N (h + c • w₁)
        ≤ modK K c * modK K (f w₁) / (modK K c * N w₁) :=
          div_le_div_of_nonneg_left (zero_le) (mul_pos hcm hNw₁) hNv
      _ = modK K (f w₁) / N w₁ := mul_div_mul_left _ _ hcm.ne'

universe u

variable (K) in
/-- A sequence `b₀, …, bₙ₋₁` is `N`-orthogonal if `N` is the supremum norm for it. -/
abbrev IsNOrthSeq (N : V → ℝ≥0) (n : ℕ) (b : ℕ → V) : Prop :=
  ∀ c : ℕ → K, N (∑ i ∈ Finset.range n, c i • b i) = (Finset.range n).sup fun i => N (c i • b i)

theorem sup_range_succ' {α : Type*} [SemilatticeSup α] [OrderBot α] (f : ℕ → α) (n : ℕ) :
    (Finset.range (n + 1)).sup f = f 0 ⊔ (Finset.range n).sup fun i => f (i + 1) := by
  apply le_antisymm
  · refine Finset.sup_le fun i hi => ?_
    cases i with
    | zero => exact le_sup_left
    | succ k =>
      exact le_sup_of_le_right (Finset.le_sup (f := fun i => f (i + 1))
        (Finset.mem_range.2 (by simpa using hi)))
  · exact sup_le (Finset.le_sup (Finset.mem_range.2 (by omega)))
      (Finset.sup_le fun i hi => Finset.le_sup (Finset.mem_range.2 (by simp at hi ⊢; omega)))

theorem sup_range_eq_univ {α : Type*} [SemilatticeSup α] [OrderBot α] (f : ℕ → α) (n : ℕ) :
    (Finset.range n).sup f = Finset.univ.sup fun i : Fin n => f i := by
  apply le_antisymm
  · exact Finset.sup_le fun i hi => Finset.le_sup (f := fun i : Fin n => f i)
      (Finset.mem_univ ⟨i, Finset.mem_range.1 hi⟩)
  · exact Finset.sup_le fun i _ => Finset.le_sup (Finset.mem_range.2 i.2)

/-- The sequence `v₀, b₀, b₁, …`. -/
def consNat (v₀ : V) (b : ℕ → V) : ℕ → V
  | 0 => v₀
  | k + 1 => b k

theorem consNat_image (v₀ : V) (b : ℕ → V) (a n : ℕ) :
    consNat v₀ b '' Set.Ico (a + 1) (n + 1) = b '' Set.Ico a n := by
  ext y
  simp only [Set.mem_image, Set.mem_Ico]
  constructor
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
    cases k with
    | zero => omega
    | succ k => exact ⟨k, ⟨by omega, by omega⟩, rfl⟩
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
    exact ⟨k + 1, ⟨by omega, by omega⟩, rfl⟩

theorem consNat_image_zero (v₀ : V) (b : ℕ → V) (n : ℕ) :
    consNat v₀ b '' Set.Ico 0 (n + 1) = insert v₀ (b '' Set.Ico 0 n) := by
  ext y
  simp only [Set.mem_image, Set.mem_Ico, Set.mem_insert_iff]
  constructor
  · rintro ⟨k, ⟨-, h2⟩, rfl⟩
    cases k with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr ⟨k, ⟨by omega, by omega⟩, rfl⟩
  · rintro (rfl | ⟨k, ⟨h1, h2⟩, rfl⟩)
    · exact ⟨0, ⟨le_rfl, by omega⟩, rfl⟩
    · exact ⟨k + 1, ⟨by omega, by omega⟩, rfl⟩

theorem IsNOrthSeq.cons {N : V → ℝ≥0} {U : Submodule K V} {v₀ : V}
    (hO : IsNOrthogonal N U (K ∙ v₀)) {n : ℕ} {b : ℕ → V} (hbU : ∀ i, b i ∈ U)
    (hb : IsNOrthSeq K N n b) : IsNOrthSeq K N (n + 1) (consNat v₀ b) := by
  intro c
  rw [Finset.sum_range_succ', sup_range_succ']
  simp only [consNat]
  obtain ⟨-, h2⟩ := hO
  have hmem : ∑ i ∈ Finset.range n, c (i + 1) • b i ∈ U :=
    U.sum_mem fun i _ => U.smul_mem _ (hbU i)
  rw [h2 _ hmem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)),
    hb (fun i => c (i + 1)), max_comm]

theorem IsNOrthSeq.of_subtype {N : V → ℝ≥0} {U : Submodule K V} {n : ℕ} {b' : ℕ → U}
    (h : IsNOrthSeq K (fun x : U => N x) n b') : IsNOrthSeq K N n (fun i => (b' i : V)) := by
  intro c
  have := h c
  simpa [Submodule.coe_sum, Submodule.coe_smul] using this

theorem IsKNorm.comap_subtype {N : V → ℝ≥0} (hN : IsKNorm (K := K) N) (U : Submodule K V) :
    IsKNorm (K := K) (fun x : U => N x) where
  eq_zero_iff x := by rw [hN.eq_zero_iff]; exact Submodule.coe_eq_zero
  smul a x := hN.smul a x
  add_le x y := hN.add_le x y

theorem sub_eq_of_subsingleton {E : Type*} [AddCommGroup E] [Module K E] [Subsingleton E]
    (A B : Submodule K E) : A = B := by
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => B.zero_mem, fun _ => A.zero_mem⟩

theorem finrank_ker_of_ne_zero {n : ℕ} (hn : Module.finrank K V = n + 1) {f : V →ₗ[K] K}
    (hf : f ≠ 0) : Module.finrank K (LinearMap.ker f) = n := by
  have hsurj : Function.Surjective f := fun c => by
    obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
      by_contra h
      push_neg at h
      exact hf (LinearMap.ext h)
    exact ⟨(c * (f v)⁻¹) • v, by simp [mul_assoc, inv_mul_cancel₀ hv]⟩
  have := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self, hn] at this
  omega

theorem span_cons_eq_top {U : Submodule K V} {v₀ : V} (hc : IsCompl U (K ∙ v₀)) {n : ℕ}
    {b' : ℕ → U} (hs : Submodule.span K (b' '' Set.Ico 0 n) = ⊤) :
    Submodule.span K (consNat v₀ (fun i => (b' i : V)) '' Set.Ico 0 (n + 1)) = ⊤ := by
  rw [consNat_image_zero, Submodule.span_insert]
  have h : Submodule.span K ((fun i => (b' i : V)) '' Set.Ico 0 n) = U := by
    have := Submodule.map_span U.subtype (b' '' Set.Ico 0 n)
    rw [hs, Submodule.map_top, Submodule.range_subtype, Set.image_image] at this
    exact this.symm
  rw [h]
  exact hc.symm.sup_eq_top

/-- Coefficients of an element of the span of a block of an indexed family. -/
theorem exists_coeffs_of_mem_span_Ico {b : ℕ → V} {a e e' : ℕ} (hee' : e ≤ e') {x : V}
    (hx : x ∈ Submodule.span K (b '' Set.Ico a e)) :
    ∃ c : ℕ → K, (∀ i, i ∉ Set.Ico a e → c i = 0) ∧ x = ∑ i ∈ Finset.range e', c i • b i := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination K).1 hx
  refine ⟨l, fun i hi => ?_, ?_⟩
  · by_contra h
    exact hi ((Finsupp.mem_supported K l).1 hl (Finsupp.mem_support_iff.2 h))
  · rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset l (s := Finset.range e') ?_ (fun i a => a • b i) (by simp)]
    intro i hi
    have := (Finsupp.mem_supported K l).1 hl hi
    exact Finset.mem_range.2 (lt_of_lt_of_le this.2 hee')

theorem isNOrthogonal_of_orthSeq {N : V → ℝ≥0} (hN : IsKNorm (K := K) N) {n : ℕ} {b : ℕ → V}
    (hspan : Submodule.span K (b '' Set.Ico 0 n) = ⊤) (hO : IsNOrthSeq K N n b) {m : ℕ} (hm : m ≤ n) :
    IsNOrthogonal N (Submodule.span K (b '' Set.Ico m n)) (Submodule.span K (b '' Set.Ico 0 m)) := by
  have key : ∀ p ∈ Submodule.span K (b '' Set.Ico m n), ∀ q ∈ Submodule.span K (b '' Set.Ico 0 m),
      N (p + q) = max (N p) (N q) := by
    intro p hp q hq
    obtain ⟨c, hc, rfl⟩ := exists_coeffs_of_mem_span_Ico (le_refl n) hp
    obtain ⟨d, hd, rfl⟩ := exists_coeffs_of_mem_span_Ico hm hq
    have hsum : ∑ i ∈ Finset.range n, c i • b i + ∑ i ∈ Finset.range n, d i • b i =
        ∑ i ∈ Finset.range n, (c i + d i) • b i := by
      rw [← Finset.sum_add_distrib]
      simp [add_smul]
    have disj : ∀ i, c i = 0 ∨ d i = 0 := by
      intro i
      by_contra h
      push_neg at h
      have h1 : i ∈ Set.Ico m n := by
        by_contra h1
        exact h.1 (hc i h1)
      have h2 : i ∈ Set.Ico 0 m := by
        by_contra h2
        exact h.2 (hd i h2)
      simp only [Set.mem_Ico] at h1 h2
      omega
    rw [hsum, hO (fun i => c i + d i), hO c, hO d]
    apply le_antisymm
    · refine Finset.sup_le fun i hi => ?_
      rw [add_smul]
      exact (hN.add_le _ _).trans (max_le_max
        (Finset.le_sup (f := fun i => N (c i • b i)) hi) (Finset.le_sup (f := fun i => N (d i • b i)) hi))
    · refine max_le (Finset.sup_le fun i hi => ?_) (Finset.sup_le fun i hi => ?_)
      · refine le_trans ?_ (Finset.le_sup (f := fun i => N ((c i + d i) • b i)) hi)
        rcases disj i with h | h
        · simp [h, hN.map_zero']
        · simp [h]
      · refine le_trans ?_ (Finset.le_sup (f := fun i => N ((c i + d i) • b i)) hi)
        rcases disj i with h | h
        · simp [h]
        · simp [h, hN.map_zero']
  refine ⟨⟨Submodule.disjoint_def.2 fun x hx hx' => ?_, ?_⟩, key⟩
  · have := key x hx (-x) (Submodule.neg_mem _ hx')
    rw [add_neg_cancel, hN.map_zero', hN.map_neg'] at this
    exact (hN.eq_zero_iff x).1 (by simpa using this.symm)
  · rw [codisjoint_iff, ← Submodule.span_union, ← Set.image_union]
    have : Set.Ico m n ∪ Set.Ico 0 m = Set.Ico 0 n := by
      ext i
      simp only [Set.mem_union, Set.mem_Ico]
      omega
    rw [this]
    exact hspan

theorem fin_orth {N : V → ℝ≥0} {n : ℕ} {b : ℕ → V} (hO : IsNOrthSeq K N n b) (c : Fin n → K) :
    N (∑ i, c i • b i) = Finset.univ.sup fun i : Fin n => N (c i • b i) := by
  obtain ⟨c', hc'⟩ : ∃ c' : ℕ → K, ∀ i : Fin n, c' i = c i :=
    ⟨fun j => if h : j < n then c ⟨j, h⟩ else 0, fun i => by simp [i.2]⟩
  have := hO c'
  rw [Finset.sum_range, sup_range_eq_univ] at this
  simpa [hc'] using this

theorem exists_basis_of_orthSeq {n : ℕ} {b : ℕ → V} (hn : Module.finrank K V = n)
    (hspan : Submodule.span K (b '' Set.Ico 0 n) = ⊤) :
    ∃ B : Module.Basis (Fin n) K V, ∀ i : Fin n, B i = b i := by
  have hr : Set.range (fun i : Fin n => b i) = b '' Set.Ico 0 n := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, ⟨Nat.zero_le _, i.2⟩, rfl⟩
    · rintro ⟨j, ⟨-, hj⟩, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  have hle : ⊤ ≤ Submodule.span K (Set.range (fun i : Fin n => b i)) := by rw [hr, hspan]
  have hcard : Fintype.card (Fin n) = Module.finrank K V := by simp [hn]
  exact ⟨Module.Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank hle hcard) hle,
    fun i => by simp⟩

/-- The inductive construction behind Prop. 3 (Weil's proof): an `N`-orthogonal sequence adapted to a
decreasing sequence of subspaces. -/
theorem exists_orth_seq (hK : IsPField K p) : ∀ (n : ℕ) (E : Type u) [AddCommGroup E] [Module K E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E]
    [FiniteDimensional K E], Module.finrank K E = n → ∀ N : E → ℝ≥0, IsKNorm (K := K) N →
    ∀ W : ℕ → Submodule K E, Antitone W →
    ∃ b : ℕ → E, IsNOrthSeq K N n b ∧ Submodule.span K (b '' Set.Ico 0 n) = ⊤ ∧
      ∀ i, W i = Submodule.span K (b '' Set.Ico (n - Module.finrank K (W i)) n) := by
  intro n
  induction n with
  | zero =>
    intro E _ _ _ _ _ _ _ hn N hN W hW
    have : Subsingleton E :=
      ⟨fun x y => by rw [finrank_zero_iff_forall_zero.1 hn x, finrank_zero_iff_forall_zero.1 hn y]⟩
    refine ⟨fun _ => 0, ?_, sub_eq_of_subsingleton _ _, fun i => sub_eq_of_subsingleton _ _⟩
    intro c
    simp [hN.map_zero']
  | succ n ih =>
    intro E _ _ _ _ _ _ _ hn N hN W hW
    have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := K) (M := E) (by omega)
    obtain ⟨q, hq, hWq⟩ : ∃ q : Submodule K E, q < ⊤ ∧ ∀ i, W i ≠ ⊤ → W i ≤ q := by
      classical
      by_cases h : ∃ i, W i ≠ ⊤
      · refine ⟨W (Nat.find h), lt_top_iff_ne_top.2 (Nat.find_spec h), fun i hi => hW ?_⟩
        exact Nat.find_min' h hi
      · push_neg at h
        exact ⟨⊥, bot_lt_top, fun i hi => absurd (h i) hi⟩
    obtain ⟨f, hf, hfq⟩ := Submodule.exists_le_ker_of_lt_top q hq
    have hH : Module.finrank K (LinearMap.ker f) = n := finrank_ker_of_ne_zero hn hf
    obtain ⟨v₀, hv₀, hmax⟩ := weil_II_1_cor3_prop1 hK hN f
    have hO : IsNOrthogonal N (LinearMap.ker f) (K ∙ v₀) :=
      (weil_II_1_prop2 hK hN hf hv₀).1 hmax
    obtain ⟨b', hb'O, hb'span, hb'W⟩ := ih (LinearMap.ker f) hH (fun x => N x)
      (hN.comap_subtype _) (fun i => (W i).comap (LinearMap.ker f).subtype)
      (fun i j hij => Submodule.comap_mono (hW hij))
    have hspan := span_cons_eq_top hO.1 hb'span
    refine ⟨consNat v₀ (fun i => (b' i : E)),
      IsNOrthSeq.cons hO (fun i => (b' i).2) hb'O.of_subtype, hspan, fun i => ?_⟩
    by_cases hWi : W i = ⊤
    · rw [hWi, finrank_top, hn, Nat.sub_self]
      exact hspan.symm
    · have hle : W i ≤ LinearMap.ker f := (hWq i hWi).trans hfq
      have hfr : Module.finrank K ((W i).comap (LinearMap.ker f).subtype) = Module.finrank K (W i) :=
        (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
      have hd : Module.finrank K (W i) ≤ n := hH ▸ Submodule.finrank_mono hle
      have h1 : (W i).comap (LinearMap.ker f).subtype = Submodule.span K (b' '' Set.Ico
          (n - Module.finrank K ((W i).comap (LinearMap.ker f).subtype)) n) := hb'W i
      rw [hfr] at h1
      have h2 : W i = Submodule.map (LinearMap.ker f).subtype
          ((W i).comap (LinearMap.ker f).subtype) := by
        rw [Submodule.map_comap_subtype, inf_eq_right.2 hle]
      calc W i = Submodule.map (LinearMap.ker f).subtype ((W i).comap (LinearMap.ker f).subtype) := h2
        _ = Submodule.map (LinearMap.ker f).subtype
              (Submodule.span K (b' '' Set.Ico (n - Module.finrank K (W i)) n)) := by rw [← h1]
        _ = Submodule.span K (consNat v₀ (fun i => (b' i : E)) ''
              Set.Ico (n - Module.finrank K (W i) + 1) (n + 1)) := by
            rw [consNat_image, Submodule.map_span, Set.image_image]
            rfl
        _ = _ := by rw [show n + 1 - Module.finrank K (W i) = n - Module.finrank K (W i) + 1 by omega]

@[kb "weil1973bnt" "Ch. II, §1, Prop. 3"]
theorem weil_II_1_prop3 (hK : IsPField K p) {N : V → ℝ≥0} (hN : IsKNorm (K := K) N) :
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      ∀ c : Fin (Module.finrank K V) → K, N (∑ i, c i • b i) = Finset.univ.sup fun i => N (c i • b i) := by
  obtain ⟨b, hO, hspan, -⟩ := exists_orth_seq hK (Module.finrank K V) V rfl N hN (fun _ => ⊥)
    (fun _ _ _ => le_rfl)
  obtain ⟨B, hB⟩ := exists_basis_of_orthSeq rfl hspan
  exact ⟨B, fun c => by simpa [hB] using fin_orth hO c⟩

/-- Prop. 3, flag version: if $W_0=V\supset W_1\supset\cdots$ with $\dim W_i=n-i$, the basis may be chosen with
$W_i$ spanned by $b_i,\dots,b_{n-1}$ (0-based indices: Weil's $W_{i+1}$ is `W i`). -/
@[kb "weil1973bnt" "Ch. II, §1, Prop. 3 (adapted to a flag)"]
theorem weil_II_1_prop3_flag (hK : IsPField K p) {N : V → ℝ≥0} (hN : IsKNorm (K := K) N)
    (W : Fin (Module.finrank K V) → Submodule K V) (hW0 : ∀ h : 0 < Module.finrank K V, W ⟨0, h⟩ = ⊤)
    (hWmono : ∀ i j : Fin (Module.finrank K V), i ≤ j → W j ≤ W i)
    (hWdim : ∀ i : Fin (Module.finrank K V), Module.finrank K (W i) = Module.finrank K V - i) :
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      (∀ c : Fin (Module.finrank K V) → K, N (∑ i, c i • b i) = Finset.univ.sup fun i => N (c i • b i)) ∧
      ∀ i, W i = Submodule.span K (b '' {j | i ≤ j}) := by
  let Wt : ℕ → Submodule K V := fun i => if h : i < Module.finrank K V then W ⟨i, h⟩ else ⊥
  have hanti : Antitone Wt := by
    intro i j hij
    by_cases hj : j < Module.finrank K V
    · have hi : i < Module.finrank K V := lt_of_le_of_lt hij hj
      simp only [Wt, dif_pos hi, dif_pos hj]
      exact hWmono ⟨i, hi⟩ ⟨j, hj⟩ hij
    · simp only [Wt, dif_neg hj]
      exact bot_le
  obtain ⟨b, hO, hspan, hW⟩ := exists_orth_seq hK (Module.finrank K V) V rfl N hN Wt hanti
  obtain ⟨B, hB⟩ := exists_basis_of_orthSeq rfl hspan
  refine ⟨B, fun c => by simpa [hB] using fin_orth hO c, fun i => ?_⟩
  have h1 := hW i
  have hWt : Wt i = W i := by simp [Wt, i.2]
  rw [hWt, hWdim i] at h1
  have e : Module.finrank K V - (Module.finrank K V - (i : ℕ)) = i := Nat.sub_sub_self i.2.le
  rw [e] at h1
  have hset : B '' {j | i ≤ j} = b '' Set.Ico (i : ℕ) (Module.finrank K V) := by
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, ⟨hj, j.2⟩, (hB j).symm⟩
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨j, h2⟩, h1, hB _⟩
  rw [hset]
  exact h1

@[kb "weil1973bnt" "Ch. II, §1, Cor. of Prop. 3"]
theorem weil_II_1_cor_prop3 (hK : IsPField K p) {N : V → ℝ≥0} (hN : IsKNorm (K := K) N)
    (W : Submodule K V) : ∃ W' : Submodule K V, IsNOrthogonal N W W' := by
  obtain ⟨b, hO, hspan, hW⟩ := exists_orth_seq hK (Module.finrank K V) V rfl N hN (fun _ => W)
    (fun _ _ _ => le_rfl)
  have h0 : W = Submodule.span K (b '' Set.Ico (Module.finrank K V - Module.finrank K W)
      (Module.finrank K V)) := hW 0
  have := isNOrthogonal_of_orthSeq hN hspan hO (Nat.sub_le (Module.finrank K V) (Module.finrank K W))
  rw [← h0] at this
  exact ⟨_, this⟩

/-- The inductive construction behind Prop. 4: two norms with a common orthogonal sequence. -/
theorem exists_orth_seq_two (hK : IsPField K p) : ∀ (n : ℕ) (E : Type u) [AddCommGroup E]
    [Module K E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E]
    [FiniteDimensional K E], Module.finrank K E = n → ∀ N N' : E → ℝ≥0, IsKNorm (K := K) N →
    IsKNorm (K := K) N' → ∃ b : ℕ → E, IsNOrthSeq K N n b ∧ IsNOrthSeq K N' n b ∧
      Submodule.span K (b '' Set.Ico 0 n) = ⊤ := by
  intro n
  induction n with
  | zero =>
    intro E _ _ _ _ _ _ _ hn N N' hN hN'
    have : Subsingleton E :=
      ⟨fun x y => by rw [finrank_zero_iff_forall_zero.1 hn x, finrank_zero_iff_forall_zero.1 hn y]⟩
    refine ⟨fun _ => 0, ?_, ?_, sub_eq_of_subsingleton _ _⟩
    · intro c
      simp [hN.map_zero']
    · intro c
      simp [hN'.map_zero']
  | succ n ih =>
    intro E _ _ _ _ _ _ _ hn N N' hN hN'
    have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := K) (M := E) (by omega)
    obtain ⟨hNc, -, -⟩ := weil_II_1_prop1 hK hN
    obtain ⟨hN'c, -, -⟩ := weil_II_1_prop1 hK hN'
    have hφ : ContinuousOn (fun v => ((N v / N' v : ℝ≥0) : ℝ)) {0}ᶜ := by
      have : ContinuousOn (fun v => N v / N' v) {0}ᶜ :=
        hNc.continuousOn.div hN'c.continuousOn (fun v hv => (hN'.pos hv).ne')
      exact NNReal.continuous_coe.comp_continuousOn this
    obtain ⟨v₁, hv₁, hmax⟩ := weil_II_1_cor2_prop1 hK
      (φ := fun v => ((N v / N' v : ℝ≥0) : ℝ)) hφ (by
        intro a v ha hv
        simp only [hN.smul, hN'.smul]
        rw [mul_div_mul_left _ _ (modK_pos_iff.2 ha).ne'])
    obtain ⟨W', hW'⟩ := weil_II_1_cor_prop3 hK hN (K ∙ v₁)
    have hdim : Module.finrank K W' = n := by
      have := Submodule.finrank_add_eq_of_isCompl hW'.1
      rw [finrank_span_singleton hv₁, hn] at this
      omega
    have hlt : W' < ⊤ := lt_top_iff_ne_top.2 fun h => by
      rw [h, finrank_top, hn] at hdim
      omega
    obtain ⟨f, hf, hfW⟩ := Submodule.exists_le_ker_of_lt_top W' hlt
    have hH : Module.finrank K (LinearMap.ker f) = n := finrank_ker_of_ne_zero hn hf
    have hker : W' = LinearMap.ker f :=
      Submodule.eq_of_le_of_finrank_eq hfW (by rw [hdim, hH])
    subst hker
    have hO : IsNOrthogonal N (LinearMap.ker f) (K ∙ v₁) := hW'.symm
    have hmaxN := (weil_II_1_prop2 hK hN hf hv₁).2 hO
    have hmaxN' : ∀ v, v ≠ 0 → modK K (f v) / N' v ≤ modK K (f v₁) / N' v₁ := by
      intro v hv
      have h1 := hmaxN v hv
      have h2 : N v / N' v ≤ N v₁ / N' v₁ := by exact_mod_cast hmax v hv
      have hNv : N v ≠ 0 := (hN.pos hv).ne'
      have hNv₁ : N v₁ ≠ 0 := (hN.pos hv₁).ne'
      calc modK K (f v) / N' v = (modK K (f v) / N v) * (N v / N' v) := by
            rw [div_mul_div_cancel₀ hNv]
        _ ≤ (modK K (f v₁) / N v₁) * (N v₁ / N' v₁) := mul_le_mul' h1 h2
        _ = modK K (f v₁) / N' v₁ := by rw [div_mul_div_cancel₀ hNv₁]
    have hO' : IsNOrthogonal N' (LinearMap.ker f) (K ∙ v₁) :=
      (weil_II_1_prop2 hK hN' hf hv₁).1 hmaxN'
    obtain ⟨b', hb'O, hb'O', hb'span⟩ := ih (LinearMap.ker f) hH (fun x => N x) (fun x => N' x)
      (hN.comap_subtype _) (hN'.comap_subtype _)
    exact ⟨consNat v₁ (fun i => (b' i : E)),
      IsNOrthSeq.cons hO (fun i => (b' i).2) hb'O.of_subtype,
      IsNOrthSeq.cons hO' (fun i => (b' i).2) hb'O'.of_subtype, span_cons_eq_top hO.1 hb'span⟩

@[kb "weil1973bnt" "Ch. II, §1, Prop. 4"]
theorem weil_II_1_prop4 (hK : IsPField K p) {N N' : V → ℝ≥0} (hN : IsKNorm (K := K) N)
    (hN' : IsKNorm (K := K) N') :
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      (∀ c : Fin (Module.finrank K V) → K, N (∑ i, c i • b i) = Finset.univ.sup fun i => N (c i • b i)) ∧
      (∀ c : Fin (Module.finrank K V) → K, N' (∑ i, c i • b i) = Finset.univ.sup fun i => N' (c i • b i)) := by
  obtain ⟨b, hO, hO', hspan⟩ := exists_orth_seq_two hK (Module.finrank K V) V rfl N N' hN hN'
  obtain ⟨B, hB⟩ := exists_basis_of_orthSeq rfl hspan
  exact ⟨B, fun c => by simpa [hB] using fin_orth hO c, fun c => by simpa [hB] using fin_orth hO' c⟩

end NumberFieldKB.WeilBNT.FieldModule
