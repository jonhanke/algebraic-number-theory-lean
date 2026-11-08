import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Topology.Algebra.Field
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, I.§2: the module in a locally compact field

$K$ is a nondiscrete locally compact field in Weil's sense: a division ring (commutative or not) with a Hausdorff,
locally compact topology for which addition, multiplication and inversion are continuous, and in which $\{0\}$ is not
open. In Lean: `[DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [LocallyCompactSpace K]
[T2Space K] [(𝓝[≠] (0 : K)).NeBot]`.

**Weil's module.** For $a\in K^\times$, $\operatorname{mod}_K(a)$ is the module of the automorphism $x\mapsto ax$ of the
additive group of $K$: $\alpha(aX)=\operatorname{mod}_K(a)\,\alpha(X)$ for a Haar measure $\alpha$. Mathlib's
`distribHaarChar K` is exactly this number for the action of $K^\times$ on $K$ by left multiplication
(`distribHaarChar_mul`); `modK` extends it by $\operatorname{mod}_K(0)=0$, as Weil does.

* `modK_mul` and `continuous_modK`: Prop. 1.
* `not_compactSpace`, `exists_modK_pos_lt`, `exists_modK_gt`: text p. 4 (the module takes arbitrarily small and large
  values; $K$ is not compact).
* `isCompact_modK_le`: Prop. 2 ($B_m=\{x:\operatorname{mod}_K(x)\le m\}$ is compact).
* `hasBasis_nhds_zero_modK`: Cor. 1 of Prop. 2; `tendsto_pow_atTop_nhds_zero_iff_modK`: Cor. 2;
  `finite_of_discreteTopology`: Cor. 3 (a discrete subfield is finite).
* `isClosed_range_modK`, `modK_units_isOpenHom`: Prop. 3.
* `weilConst`, `modK_add_le`, `weilConst_le`, `discrete_range_of_weilConst_eq_one`: Thm. 4;
  `modK_add_eq_of_lt`: its Corollary; `IsUltrametricMod`: Def. 1.
-/

open MeasureTheory Topology Filter
open scoped NNReal ENNReal Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K]

variable (K) in
/-- Weil's module $\operatorname{mod}_K(a)$ (I.§2, p. 4): the module of $x\mapsto ax$ for $a\ne0$, and $0$ for
$a=0$. -/
def modK (a : K) : ℝ≥0 :=
  open scoped Classical in
  if h : a = 0 then 0 else distribHaarChar K (Units.mk0 a h)

@[simp] theorem modK_zero : modK K 0 = 0 := by simp [modK]

open scoped Classical in
theorem modK_def (a : K) : modK K a = if h : a = 0 then 0 else distribHaarChar K (Units.mk0 a h) := rfl

theorem modK_units (u : Kˣ) : modK K (u : K) = distribHaarChar K u := by
  simp [modK, u.ne_zero]

@[simp] theorem modK_one : modK K 1 = 1 := by
  simpa using modK_units (K := K) 1

theorem modK_pos_iff {a : K} : 0 < modK K a ↔ a ≠ 0 := by
  constructor
  · intro h ha; simp [ha] at h
  · intro ha
    rw [show a = ((Units.mk0 a ha : Kˣ) : K) from rfl, modK_units]
    exact distribHaarChar_pos

theorem modK_eq_zero_iff {a : K} : modK K a = 0 ↔ a = 0 := by
  rw [← not_iff_not, ← ne_eq, ← pos_iff_ne_zero, modK_pos_iff]

/-- Defining property: $\alpha(aX)=\operatorname{mod}_K(a)\alpha(X)$ for every (regular) Haar measure $\alpha$. -/
theorem modK_mul_measure [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
    [μ.Regular] {a : K} (ha : a ≠ 0) (s : Set K) : (modK K a : ℝ≥0∞) * μ s = μ (a • s) := by
  rw [show a = ((Units.mk0 a ha : Kˣ) : K) from rfl, modK_units]
  exact distribHaarChar_mul μ (Units.mk0 a ha) s

@[kb "weil1973bnt" "Ch. I, §2, Prop. 1 (multiplicativity)"]
theorem modK_mul (a b : K) : modK K (a * b) = modK K a * modK K b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have e : ((Units.mk0 a ha * Units.mk0 b hb : Kˣ) : K) = a * b := rfl
  rw [← e, modK_units, map_mul]
  exact congrArg₂ (· * ·) (modK_units (Units.mk0 a ha)).symm (modK_units (Units.mk0 b hb)).symm

variable [(𝓝[≠] (0 : K)).NeBot]

theorem modK_inv {x : K} (hx : x ≠ 0) : modK K x⁻¹ = (modK K x)⁻¹ := by
  have h := modK_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, modK_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- The defining property of the module extended to `a = 0` for nonempty sets. -/
theorem modK_mul_measure_of_nonempty [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [μ.IsAddHaarMeasure] [μ.Regular] (a : K) {s : Set K} (hs : s.Nonempty) :
    (modK K a : ℝ≥0∞) * μ s = μ (a • s) := by
  by_cases ha : a = 0
  · subst ha
    rw [Set.zero_smul_set hs, ← Set.singleton_zero]
    simp
  · exact modK_mul_measure μ ha s

/-- Upper semicontinuity of the module (the first half of Prop. 1). -/
theorem eventually_modK_lt (a : K) {c : ℝ≥0} (hc : modK K a < c) : ∀ᶠ x in 𝓝 a, modK K x < c := by
  borelize K
  let μ : Measure K := Measure.addHaar
  obtain ⟨X, hXc, hX0⟩ := exists_compact_mem_nhds (0 : K)
  have hXne : X.Nonempty := ⟨0, mem_of_mem_nhds hX0⟩
  have hXpos : μ X ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hX0).ne'
  have hXtop : μ X ≠ ∞ := hXc.measure_lt_top.ne
  have hmul := fun x : K => modK_mul_measure_of_nonempty μ x hXne
  have h1 : μ (a • X) < c * μ X := by
    rw [← hmul]
    exact (ENNReal.mul_lt_mul_iff_left hXpos hXtop).2 (by exact_mod_cast hc)
  obtain ⟨U, haU, hUo, hU⟩ := (a • X).exists_isOpen_lt_of_lt _ h1
  have ev : ∀ᶠ x in 𝓝 a, ∀ y ∈ X, x * y ∈ U :=
    hXc.eventually_forall_of_forall_eventually fun y hy =>
      (continuous_mul.tendsto (a, y)).eventually (hUo.mem_nhds (haU (Set.smul_mem_smul_set hy)))
  filter_upwards [ev] with x hx
  have hsub : x • X ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact hx y hy
  have h2 := (measure_mono hsub).trans_lt hU
  rw [← hmul] at h2
  exact_mod_cast (ENNReal.mul_lt_mul_iff_left hXpos hXtop).1 h2

/-- Lower semicontinuity of the module, obtained from the upper semicontinuity by inversion. -/
theorem eventually_lt_modK (a : K) {c : ℝ≥0} (hc : c < modK K a) : ∀ᶠ x in 𝓝 a, c < modK K x := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hc
  have hxne : ∀ᶠ x in 𝓝 a, x ≠ 0 := isOpen_ne.mem_nhds ha
  by_cases hc0 : c = 0
  · filter_upwards [hxne] with x hx
    rw [hc0]
    exact modK_pos_iff.2 hx
  · have hcpos : 0 < c := pos_iff_ne_zero.2 hc0
    have h1 : modK K a⁻¹ < c⁻¹ := by
      rw [modK_inv ha]
      exact (inv_lt_inv₀ (modK_pos_iff.2 ha) hcpos).2 hc
    have h2 := eventually_modK_lt a⁻¹ h1
    have h3 : Tendsto (fun x : K => x⁻¹) (𝓝 a) (𝓝 a⁻¹) := tendsto_inv₀ ha
    filter_upwards [h3.eventually h2, hxne] with x hx hx0
    rw [modK_inv hx0] at hx
    exact (inv_lt_inv₀ (modK_pos_iff.2 hx0) hcpos).1 hx

@[kb "weil1973bnt" "Ch. I, §2, Prop. 1 (continuity)"]
theorem continuous_modK : Continuous (modK K) := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  exact tendsto_order.2 ⟨fun c hc => eventually_lt_modK a hc, fun c hc => eventually_modK_lt a hc⟩

@[kb "weil1973bnt" "Ch. I, §2, text p. 4 (small values of the module)"]
theorem exists_modK_pos_lt {ε : ℝ≥0} (hε : 0 < ε) : ∃ a : K, 0 < modK K a ∧ modK K a < ε := by
  have h : ∀ᶠ x in 𝓝 (0 : K), modK K x < ε :=
    (continuous_modK.tendsto 0).eventually (gt_mem_nhds (by simpa using hε))
  have h' : ∀ᶠ x in 𝓝[≠] (0 : K), modK K x < ε ∧ x ≠ 0 :=
    (eventually_nhdsWithin_of_eventually_nhds h).and self_mem_nhdsWithin
  obtain ⟨a, ha, ha0⟩ := Filter.Eventually.exists (f := 𝓝[≠] (0 : K)) h'
  exact ⟨a, modK_pos_iff.2 ha0, ha⟩

@[kb "weil1973bnt" "Ch. I, §2, text p. 4 (large values of the module)"]
theorem exists_modK_gt (M : ℝ≥0) : ∃ b : K, M < modK K b := by
  obtain ⟨a, ha, ha1⟩ := exists_modK_pos_lt (K := K) (ε := (M + 1)⁻¹) (by positivity)
  have ha0 : a ≠ 0 := modK_pos_iff.1 ha
  refine ⟨a⁻¹, ?_⟩
  rw [modK_inv ha0]
  have : M + 1 < (modK K a)⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) ha]
    exact ha1
  exact lt_of_le_of_lt (by simp) this

variable (K) in
@[kb "weil1973bnt" "Ch. I, §2, text p. 4 (a nondiscrete locally compact field is not compact)"]
theorem not_compactSpace : ¬ CompactSpace K := by
  intro h
  obtain ⟨M, hM⟩ := (isCompact_univ (X := K)).image (continuous_modK (K := K)) |>.bddAbove
  obtain ⟨b, hb⟩ := exists_modK_gt (K := K) M
  exact absurd (hM ⟨b, Set.mem_univ _, rfl⟩) (not_le.2 hb)

theorem modK_pow (a : K) (n : ℕ) : modK K (a ^ n) = modK K a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, modK_mul, ih, pow_succ]

/-- Prop. 2 for a positive bound `m`. -/
theorem isCompact_modK_le_of_pos {m : ℝ≥0} (hm : 0 < m) : IsCompact {x : K | modK K x ≤ m} := by
  obtain ⟨V, hVc, hV0⟩ := exists_compact_mem_nhds (0 : K)
  -- a neighbourhood `W` of `0` with `W * V ⊆ V`
  have hW : ∀ᶠ x in 𝓝 (0 : K), ∀ y ∈ V, x * y ∈ V :=
    hVc.eventually_forall_of_forall_eventually fun y _ =>
      (continuous_mul.tendsto (0, y)).eventually (by simpa using hV0)
  have e3 : ∀ᶠ x in 𝓝 (0 : K), modK K x < 1 :=
    (continuous_modK.tendsto 0).eventually (gt_mem_nhds (by simp))
  have hr : ∀ᶠ x in 𝓝[≠] (0 : K), (x ∈ V ∧ (∀ y ∈ V, x * y ∈ V) ∧ modK K x < 1) ∧ x ≠ 0 :=
    (eventually_nhdsWithin_of_eventually_nhds ((show ∀ᶠ x in 𝓝 (0 : K), x ∈ V from hV0).and (hW.and e3))).and self_mem_nhdsWithin
  obtain ⟨r, ⟨hrV, hrW, hr1⟩, hr0⟩ := Filter.Eventually.exists (f := 𝓝[≠] (0 : K)) hr
  have hrpow : ∀ n : ℕ, r ^ (n + 1) ∈ V := by
    intro n
    induction n with
    | zero => rw [zero_add, pow_one]; exact hrV
    | succ n ih => rw [pow_succ' r (n + 1)]; exact hrW _ ih
  have hlim : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    refine hVc.tendsto_nhds_of_unique_mapClusterPt (Filter.Eventually.of_forall hrpow) ?_
    intro z _ hcl
    have h1 : MapClusterPt (modK K z) atTop (modK K ∘ fun n : ℕ => r ^ (n + 1)) :=
      hcl.continuousAt_comp continuous_modK.continuousAt
    have h2 : Tendsto (modK K ∘ fun n : ℕ => r ^ (n + 1)) atTop (𝓝 0) := by
      have : (modK K ∘ fun n : ℕ => r ^ (n + 1)) = fun n => (modK K r) ^ (n + 1) := by
        funext n; simp [modK_pow]
      rw [this]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one zero_le hr1).comp (tendsto_add_atTop_nat 1)
    rw [← modK_eq_zero_iff]
    by_contra hne
    have hpos : 0 < modK K z := pos_iff_ne_zero.2 hne
    have hfreq := h1.frequently (Ioi_mem_nhds (half_lt_self hpos))
    have hev := h2.eventually (gt_mem_nhds (half_pos hpos))
    obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hev).exists
    exact absurd hn1 (not_lt.2 hn2.le)
  -- the preimage of `V` under multiplication by `r⁻¹`
  set rV : Set K := (fun x => r⁻¹ * x) ⁻¹' V with hrVdef
  have hrV0 : rV ∈ 𝓝 (0 : K) :=
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hV0)
  set X : Set K := closure (V \ rV) with hXdef
  have hXc : IsCompact X :=
    hVc.of_isClosed_subset isClosed_closure (closure_minimal Set.sdiff_subset hVc.isClosed)
  have h0X : (0 : K) ∉ X := by
    intro h
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.1 h _ hrV0
    exact hy2.2 hy1
  obtain ⟨δ, hδ, hδX⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ ∀ x ∈ X, δ ≤ modK K x := by
    rcases X.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨x0, hx0, hmin⟩ := hXc.exists_isMinOn h continuous_modK.continuousOn
      exact ⟨modK K x0, modK_pos_iff.2 (fun h0 => h0X (h0 ▸ hx0)), fun x hx => hmin hx⟩
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hδ hm) hr1
  have hcover : ∀ x : K, modK K x ≤ m → ∃ n ≤ N, r ^ n * x ∈ V := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have hev : ∃ n : ℕ, r ^ n * x ∈ V := by
      have := (hlim.mul_const x)
      rw [zero_mul] at this
      exact (this.eventually hV0).exists
    classical
    have hνN : N < Nat.find hev := by
      by_contra h
      exact hcon _ (not_lt.1 h) (Nat.find_spec hev)
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hev = k + 1 := ⟨Nat.find hev - 1, by omega⟩
    have hkV : r ^ k * x ∉ V := Nat.find_min hev (by omega)
    have hmem : r ^ Nat.find hev * x ∈ X := by
      refine subset_closure ⟨Nat.find_spec hev, fun h => hkV ?_⟩
      have e : r⁻¹ * (r ^ Nat.find hev * x) = r ^ k * x := by
        rw [hk, pow_succ', mul_assoc, inv_mul_cancel_left₀ hr0]
      simpa [hrVdef, e] using h
    have h1 := hδX _ hmem
    rw [modK_mul, modK_pow] at h1
    have h2 : modK K r ^ Nat.find hev ≤ modK K r ^ N :=
      pow_le_pow_of_le_one zero_le hr1.le hνN.le
    have h3 : modK K r ^ N * m < δ := (lt_div_iff₀ hm).1 hN
    exact absurd (lt_of_le_of_lt (h1.trans (mul_le_mul' h2 hx)) h3) (lt_irrefl _)
  have hcpt : IsCompact (⋃ n ∈ Finset.range (N + 1), (fun x : K => (r ^ n)⁻¹ * x) '' V) :=
    (Finset.range (N + 1)).isCompact_biUnion fun n _ =>
      hVc.image (continuous_const.mul continuous_id)
  refine hcpt.of_isClosed_subset (isClosed_le continuous_modK continuous_const) ?_
  intro x hx
  obtain ⟨n, hn, hnV⟩ := hcover x hx
  simp only [Set.mem_iUnion]
  exact ⟨n, Finset.mem_range.2 (Nat.lt_succ_of_le hn), _, hnV,
    inv_mul_cancel_left₀ (pow_ne_zero n hr0) x⟩

@[kb "weil1973bnt" "Ch. I, §2, Prop. 2"]
theorem isCompact_modK_le (m : ℝ≥0) : IsCompact {x : K | modK K x ≤ m} := by
  have hmono : {x : K | modK K x ≤ m} ⊆ {x : K | modK K x ≤ m + 1} := fun x (hx : modK K x ≤ m) => show modK K x ≤ m + 1 from
    le_trans hx le_self_add
  exact IsCompact.of_isClosed_subset (isCompact_modK_le_of_pos (by positivity))
    (isClosed_le continuous_modK continuous_const) hmono

@[kb "weil1973bnt" "Ch. I, §2, Cor. 1 of Prop. 2"]
theorem hasBasis_nhds_zero_modK :
    (𝓝 (0 : K)).HasBasis (fun m : ℝ≥0 => 0 < m) (fun m => {x : K | modK K x ≤ m}) := by
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨m, hm, hsub⟩ => ?_⟩⟩
  · obtain ⟨V, ⟨hV0, hVc⟩, hVt⟩ := (compact_basis_nhds (0 : K)).mem_iff.1 ht
    obtain ⟨M0, hM0⟩ := (hVc.image continuous_modK).bddAbove
    have hMpos : 0 < M0 + 1 := by positivity
    have hXc : IsCompact (closure ({x : K | modK K x ≤ M0 + 1} \ V)) :=
      (isCompact_modK_le (M0 + 1)).of_isClosed_subset isClosed_closure
        (closure_minimal Set.sdiff_subset (isClosed_le continuous_modK continuous_const))
    have h0X : (0 : K) ∉ closure ({x : K | modK K x ≤ M0 + 1} \ V) := by
      intro h
      obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.1 h V hV0
      exact hy2.2 hy1
    obtain ⟨δ, hδ, hδX⟩ : ∃ δ : ℝ≥0, 0 < δ ∧
        ∀ x ∈ closure ({x : K | modK K x ≤ M0 + 1} \ V), δ ≤ modK K x := by
      rcases (closure ({x : K | modK K x ≤ M0 + 1} \ V)).eq_empty_or_nonempty with h | h
      · exact ⟨1, one_pos, by simp [h]⟩
      · obtain ⟨x0, hx0, hmin⟩ := hXc.exists_isMinOn h continuous_modK.continuousOn
        exact ⟨modK K x0, modK_pos_iff.2 (fun h0 => h0X (h0 ▸ hx0)), fun x hx => hmin hx⟩
    refine ⟨min (δ / 2) (M0 + 1), lt_min (half_pos hδ) hMpos, fun x hx => hVt ?_⟩
    by_contra hxV
    have hxM : modK K x ≤ M0 + 1 := hx.trans (min_le_right _ _)
    have h1 := hδX x (subset_closure ⟨hxM, hxV⟩)
    have h2 : modK K x ≤ δ / 2 := hx.trans (min_le_left _ _)
    exact absurd (h1.trans h2) (not_le.2 (half_lt_self hδ))
  · refine Filter.mem_of_superset (Filter.mem_of_superset
      ((isOpen_lt continuous_modK continuous_const).mem_nhds (by simpa using hm))
      (fun x (hx : modK K x < m) => hx.le)) hsub

@[kb "weil1973bnt" "Ch. I, §2, Cor. 2 of Prop. 2"]
theorem tendsto_pow_atTop_nhds_zero_iff_modK (a : K) :
    Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) ↔ modK K a < 1 := by
  constructor
  · intro h
    by_contra hge
    have h1 : Tendsto (modK K ∘ fun n : ℕ => a ^ n) atTop (𝓝 0) := by
      simpa using (continuous_modK.tendsto 0).comp h
    have h2 := h1.eventually (gt_mem_nhds (show (0 : ℝ≥0) < 1 from one_pos))
    obtain ⟨n, hn⟩ := h2.exists
    simp only [Function.comp_apply, modK_pow] at hn
    exact absurd hn (not_lt.2 (one_le_pow₀ (not_lt.1 hge)))
  · intro h
    have h1 : Tendsto (fun n : ℕ => modK K (a ^ n)) atTop (𝓝 0) := by
      simp_rw [modK_pow]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one zero_le h
    rw [hasBasis_nhds_zero_modK.tendsto_right_iff]
    intro m hm
    exact (h1.eventually (gt_mem_nhds hm)).mono fun n hn => hn.le

@[kb "weil1973bnt" "Ch. I, §2, Cor. 3 of Prop. 2"]
theorem finite_of_discreteTopology (L : Subfield K) [DiscreteTopology L] : Finite L := by
  have hle : ∀ a ∈ (L : Set K), modK K a ≤ 1 := by
    intro a ha
    by_contra hgt
    rw [not_le] at hgt
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hgt
    have hb : modK K a⁻¹ < 1 := by
      rw [modK_inv ha0]
      exact inv_lt_one_of_one_lt₀ hgt
    have ht := (tendsto_pow_atTop_nhds_zero_iff_modK a⁻¹).2 hb
    have hbL : ∀ n : ℕ, a⁻¹ ^ n ∈ L := fun n => L.pow_mem (L.inv_mem ha) n
    have ht' : Tendsto (fun n : ℕ => (⟨a⁻¹ ^ n, hbL n⟩ : L)) atTop (𝓝 0) := by
      rw [tendsto_subtype_rng]
      exact ht
    have hopen : ({0} : Set L) ∈ 𝓝 (0 : L) := (isOpen_discrete _).mem_nhds rfl
    obtain ⟨n, hn⟩ := (ht'.eventually hopen).exists
    have h0 : a⁻¹ ^ n = 0 := congrArg Subtype.val hn
    simp at h0
    exact ha0 h0.1
  have hcl : IsClosed (L : Set K) := AddSubgroup.isClosed_of_discreteTopology (U := L.toAddSubgroup)
  have hc : IsCompact (L : Set K) := (isCompact_modK_le 1).of_isClosed_subset hcl hle
  exact (hc.finite DiscreteTopology.isDiscrete).to_subtype

@[kb "weil1973bnt" "Ch. I, §2, Prop. 3 (the image of the module is closed)"]
theorem isClosed_range_modK : IsClosed (Set.range (modK K)) := by
  refine isClosed_of_closure_subset fun y hy => ?_
  have hU : IsOpen (Set.Iio (y + 1)) := isOpen_Iio
  have h1 : y ∈ Set.Iio (y + 1) ∩ closure (Set.range (modK K)) :=
    ⟨by simp, hy⟩
  have h2 := hU.inter_closure h1
  have hsub : Set.Iio (y + 1) ∩ Set.range (modK K) ⊆ modK K '' {x : K | modK K x ≤ y + 1} := by
    rintro _ ⟨hlt, x, rfl⟩
    exact ⟨x, show modK K x ≤ y + 1 from le_of_lt hlt, rfl⟩
  have hcl : IsClosed (modK K '' {x : K | modK K x ≤ y + 1}) :=
    ((isCompact_modK_le (y + 1)).image continuous_modK).isClosed
  have h3 := closure_minimal hsub hcl h2
  obtain ⟨x, _, hx⟩ := h3
  exact ⟨x, hx⟩

/-- Prop. 3, openness: the homomorphism $\operatorname{mod}_K:K^\times\to\mathbb R_+^\times$ is open onto its image;
equivalently (it is a homomorphism), the image of every neighbourhood $V$ of $1$ contains all values of the module
close enough to $1$. -/
@[kb "weil1973bnt" "Ch. I, §2, Prop. 3 (openness)"]
theorem modK_units_isOpenHom {V : Set Kˣ} (hV : V ∈ 𝓝 (1 : Kˣ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : Kˣ, |(modK K (u : K) : ℝ) - 1| < ε → ∃ w ∈ V, modK K (w : K) = modK K u := by
  obtain ⟨N, hN, hNV⟩ : ∃ N ∈ 𝓝 (1 : K), ∀ u : Kˣ, (u : K) ∈ N → u ∈ V := by
    have h := (Units.isEmbedding_val₀ (G₀ := K)).isInducing.nhds_eq_comap (1 : Kˣ)
    rw [h] at hV
    obtain ⟨N, hN, hNV⟩ := Filter.mem_comap.1 hV
    exact ⟨N, by simpa using hN, fun u hu => hNV hu⟩
  by_contra hcon
  push Not at hcon
  have hn : ∀ n : ℕ, ∃ u : Kˣ, |(modK K (u : K) : ℝ) - 1| < 1 / ((n : ℝ) + 1) ∧
      ∀ w ∈ V, modK K (w : K) ≠ modK K u := fun n => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose u hu1 hu2 using hn
  have hle2 : ∀ n, (u n : K) ∈ {x : K | modK K x ≤ 2} := by
    intro n
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h2 := (abs_lt.1 ((hu1 n).trans_le h1)).2
    show modK K (u n : K) ≤ 2
    have : (modK K (u n : K) : ℝ) ≤ 2 := by linarith
    exact_mod_cast this
  obtain ⟨a, _, ha⟩ := (isCompact_modK_le (K := K) 2).exists_mapClusterPt
    (f := atTop) (u := fun n => (u n : K)) (Filter.tendsto_principal.2 (Eventually.of_forall hle2))
  have htend : Tendsto (fun n : ℕ => modK K (u n : K)) atTop (𝓝 1) := by
    rw [← NNReal.tendsto_coe, tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.dist_eq]
    exact (hu1 n).le
  have hma : modK K a = 1 := by
    have h1 := ha.continuousAt_comp continuous_modK.continuousAt
    by_contra hne
    obtain ⟨U, W, hUo, hWo, hmU, h1W, hdisj⟩ := t2_separation hne
    obtain ⟨n, hn1, hn2⟩ := ((h1.frequently (hUo.mem_nhds hmU)).and_eventually
      (htend.eventually (hWo.mem_nhds h1W))).exists
    exact Set.disjoint_left.1 hdisj hn1 hn2
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hma
  have hS : {x : K | a⁻¹ * x ∈ N} ∈ 𝓝 a := by
    refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
    simpa [ha0] using hN
  obtain ⟨n, hn⟩ := (ha.frequently hS).exists
  have hw := hNV (Units.mk0 a⁻¹ (inv_ne_zero ha0) * u n) (by simpa using hn)
  apply hu2 n _ hw
  rw [Units.val_mul, modK_mul]
  show modK K a⁻¹ * modK K (u n : K) = _
  rw [modK_inv ha0, hma]
  simp

variable (K) in
/-- Weil's constant $A=\sup_{\operatorname{mod}_K(x)\le1}\operatorname{mod}_K(1+x)$ of Thm. 4. -/
def weilConst : ℝ≥0 := sSup ((fun x : K => modK K (1 + x)) '' {x | modK K x ≤ 1})

theorem bddAbove_weilConst : BddAbove ((fun x : K => modK K (1 + x)) '' {x | modK K x ≤ 1}) := by
  refine ((isCompact_modK_le (K := K) 1).image ?_).bddAbove
  exact continuous_modK.comp (continuous_const.add continuous_id)

/-- The inequality (3) when `y` is no larger than `x`. -/
theorem modK_add_le_of_le (x y : K) (hxy : modK K y ≤ modK K x) :
    modK K (x + y) ≤ weilConst K * modK K x := by
  by_cases hx : x = 0
  · have hy : y = 0 := modK_eq_zero_iff.1 (le_antisymm (by simpa [hx] using hxy) zero_le)
    simp [hx, hy]
  · have hz : modK K (y * x⁻¹) ≤ 1 := by
      rw [modK_mul, modK_inv hx]
      have hpos : 0 < modK K x := modK_pos_iff.2 hx
      rw [← div_eq_mul_inv]
      exact (div_le_one hpos).2 hxy
    have h1 : modK K (1 + y * x⁻¹) ≤ weilConst K :=
      le_csSup bddAbove_weilConst ⟨y * x⁻¹, hz, rfl⟩
    have e : x + y = (1 + y * x⁻¹) * x := by
      rw [add_mul, one_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one, add_comm]
    rw [e, modK_mul]
    exact mul_le_mul' h1 le_rfl

@[kb "weil1973bnt" "Ch. I, §2, Thm. 4 (the inequality (3))"]
theorem modK_add_le (x y : K) : modK K (x + y) ≤ weilConst K * max (modK K x) (modK K y) := by
  rcases le_total (modK K y) (modK K x) with h | h
  · rw [max_eq_left h]
    exact modK_add_le_of_le x y h
  · rw [max_eq_right h, add_comm]
    exact modK_add_le_of_le y x h

@[kb "weil1973bnt" "Ch. I, §2, Thm. 4 (the best constant)"]
theorem weilConst_le {A : ℝ≥0} (hA : ∀ x y : K, modK K (x + y) ≤ A * max (modK K x) (modK K y)) :
    weilConst K ≤ A := by
  refine csSup_le ⟨_, 0, by simp, rfl⟩ ?_
  rintro _ ⟨x, hx, rfl⟩
  have := hA 1 x
  rw [max_eq_left (by simpa using hx)] at this
  simpa using this

variable (K) in
/-- Def. 1: $K$ (or $\operatorname{mod}_K$) is ultrametric if (3) holds with $A=1$. -/
def IsUltrametricMod : Prop := ∀ x y : K, modK K (x + y) ≤ max (modK K x) (modK K y)

@[kb "weil1973bnt" "Ch. I, §2, Thm. 4 (if A = 1 the image of the module is discrete)"]
theorem discrete_range_of_isUltrametricMod (h : IsUltrametricMod K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : Kˣ, |(modK K (u : K) : ℝ) - 1| < ε → modK K (u : K) = 1 := by
  -- the units whose value lies in `1 + B₁` form a neighbourhood of `1`
  have hB : {x : K | modK K x ≤ 1} ∈ 𝓝 (0 : K) :=
    hasBasis_nhds_zero_modK.mem_of_mem one_pos
  have hN : (fun x : K => x - 1) ⁻¹' {x : K | modK K x ≤ 1} ∈ 𝓝 (1 : K) := by
    refine (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds ?_
    simpa using hB
  have hV : (fun u : Kˣ => (u : K)) ⁻¹' ((fun x : K => x - 1) ⁻¹' {x : K | modK K x ≤ 1}) ∈
      𝓝 (1 : Kˣ) :=
    (Units.continuous_val.continuousAt).preimage_mem_nhds (by simpa using hN)
  obtain ⟨ε, hε, hεV⟩ := modK_units_isOpenHom hV
  have hle1 : ∀ u : Kˣ, |(modK K (u : K) : ℝ) - 1| < ε → modK K (u : K) ≤ 1 := by
    intro u hu
    obtain ⟨w, hw, hwu⟩ := hεV u hu
    rw [← hwu]
    have hw' : modK K ((w : K) - 1) ≤ 1 := hw
    have := h 1 ((w : K) - 1)
    rw [add_sub_cancel, modK_one, max_eq_left hw'] at this
    exact this
  refine ⟨min (ε / 2) (1 / 2), lt_min (half_pos hε) (by norm_num), fun u hu => ?_⟩
  have hu1 : |(modK K (u : K) : ℝ) - 1| < ε / 2 := hu.trans_le (min_le_left _ _)
  have hu2 : |(modK K (u : K) : ℝ) - 1| < 1 / 2 := hu.trans_le (min_le_right _ _)
  have h1 : modK K (u : K) ≤ 1 := hle1 u (by linarith)
  set t : ℝ := (modK K (u : K) : ℝ) with ht
  have ht1 : t ≤ 1 := by exact_mod_cast h1
  have htpos : 1 / 2 < t := by
    have := (abs_lt.1 hu2).1
    linarith
  have hinv : modK K ((u⁻¹ : Kˣ) : K) = (modK K (u : K))⁻¹ := by
    rw [Units.val_inv_eq_inv_val, modK_inv u.ne_zero]
  have h2 : modK K ((u⁻¹ : Kˣ) : K) ≤ 1 := by
    refine hle1 u⁻¹ ?_
    rw [hinv, NNReal.coe_inv, ← ht]
    have e : t⁻¹ - 1 = (1 - t) / t := by field_simp
    rw [e, abs_div, abs_of_pos (by linarith : 0 < t), div_lt_iff₀ (by linarith)]
    have : |1 - t| = |t - 1| := abs_sub_comm _ _
    rw [this]
    have h3 : |t - 1| * t ≤ |t - 1| := mul_le_of_le_one_right (abs_nonneg _) ht1
    nlinarith [abs_nonneg (t - 1)]
  rw [hinv] at h2
  have : 1 ≤ modK K (u : K) := by
    have hpos : 0 < modK K (u : K) := modK_pos_iff.2 u.ne_zero
    simpa [inv_le_one₀ hpos] using h2
  exact le_antisymm h1 this

@[kb "weil1973bnt" "Ch. I, §2, Cor. of Thm. 4"]
theorem modK_add_eq_of_lt (h : IsUltrametricMod K) {x y : K} (hxy : modK K y < modK K x) :
    modK K (x + y) = modK K x := by
  have hneg : modK K (-1) = 1 := by
    have h1 : modK K (-1) ^ 2 = 1 := by
      rw [← modK_pow]
      simp
    exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num)).1 h1
  have hy : modK K (-y) = modK K y := by
    rw [← neg_one_mul, modK_mul, hneg, one_mul]
  refine le_antisymm ((h x y).trans (max_eq_left hxy.le).le) ?_
  have h2 := h (x + y) (-y)
  rw [add_neg_cancel_right, hy] at h2
  rcases le_max_iff.1 h2 with h3 | h3
  · exact h3
  · exact absurd hxy (not_lt.2 h3)

end NumberFieldKB.WeilBNT.FieldModule
