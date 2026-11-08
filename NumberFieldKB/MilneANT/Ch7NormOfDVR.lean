import Mathlib

/-!
# The absolute value of a discrete valuation ring, and its completeness and compactness

Bridge for Milne, *Algebraic Number Theory* v3.08, Prop. 7.64: for a discrete valuation ring `A` with fraction
field `K`, the `𝔪`-adic absolute value `dvrAbv A K` (with base `2`) makes `K` a nontrivially normed field
(`dvrNontriviallyNormedField`), with `‖x‖ ≤ 1` exactly on the image of `A`. If `A` is `𝔪`-adically complete,
`K` is a complete space (`dvr_completeSpace`), and if moreover the residue field is finite, the closed unit ball is
compact (`dvr_isCompact_closedBall`). The lemmas are stated for an arbitrary normed field structure `hn : ‖x‖ = dvrAbv A K x`.
-/

open IsLocalRing

universe u v

namespace NumberFieldKB.MilneANT

section DVRNorm

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]

noncomputable def dvrAbv : AbsoluteValue K ℝ :=
  (IsDiscreteValuationRing.maximalIdeal A).adicAbv (b := 2) (by norm_num)

@[instance_reducible] noncomputable def dvrNormedField : NormedField K := (dvrAbv A K).toNormedField

variable {A K}

lemma dvrAbv_le_one (a : A) : dvrAbv A K (algebraMap A K a) ≤ 1 :=
  IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one _ _ _

lemma dvrAbv_lt_one_iff (a : A) : dvrAbv A K (algebraMap A K a) < 1 ↔ a ∈ maximalIdeal A :=
  IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_lt_one_iff _ _ _

lemma dvrAbv_eq_one_iff (a : A) : dvrAbv A K (algebraMap A K a) = 1 ↔ IsUnit a := by
  rw [dvrAbv, IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_eq_one_iff]
  simp [IsDiscreteValuationRing.maximalIdeal, mem_maximalIdeal, mem_nonunits_iff]

lemma dvrAbv_isNonarch : IsNonarchimedean (dvrAbv A K) :=
  IsDedekindDomain.HeightOneSpectrum.isNonarchimedean_adicAbv _ _

/-- an element of norm ≤ 1 comes from A -/
lemma exists_of_dvrAbv_le_one (x : K) (hx : dvrAbv A K x ≤ 1) : ∃ a : A, algebraMap A K a = x := by
  rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact ⟨a, ha⟩
  · by_cases hx0 : x = 0
    · exact ⟨0, by simp [hx0]⟩
    have hb1 : 1 ≤ dvrAbv A K (algebraMap A K b) := by
      rw [hb, map_inv₀, one_le_inv₀ (by simpa using hx0)]
      exact hx
    have hb2 : dvrAbv A K (algebraMap A K b) = 1 :=
      le_antisymm (dvrAbv_le_one b) hb1
    rw [dvrAbv_eq_one_iff] at hb2
    refine ⟨↑hb2.unit⁻¹, ?_⟩
    have : x = (algebraMap A K b)⁻¹ := by rw [hb, inv_inv]
    rw [this]
    simp

variable {π : A} (hπ : Irreducible π)
include hπ

lemma dvrAbv_pi_pos : 0 < dvrAbv A K (algebraMap A K π) := by
  simpa using hπ.ne_zero

lemma dvrAbv_pi_lt_one : dvrAbv A K (algebraMap A K π) < 1 := by
  rw [dvrAbv_lt_one_iff]
  exact (mem_maximalIdeal _).2 hπ.not_isUnit

lemma dvrAbv_le_pow_iff (a : A) (k : ℕ) :
    dvrAbv A K (algebraMap A K a) ≤ dvrAbv A K (algebraMap A K π) ^ k ↔ a ∈ maximalIdeal A ^ k := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · intro h
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have hu : dvrAbv A K (algebraMap A K (u : A)) = 1 := (dvrAbv_eq_one_iff _).2 u.isUnit
    simp only [map_mul, map_pow, hu, one_mul] at h
    have := (pow_le_pow_iff_right_of_lt_one₀ (dvrAbv_pi_pos hπ) (dvrAbv_pi_lt_one hπ)).1 h
    exact Dvd.dvd.mul_left (pow_dvd_pow π this) _
  · rintro ⟨c, rfl⟩
    simp only [map_mul, map_pow]
    calc _ ≤ dvrAbv A K (algebraMap A K π) ^ k * 1 := by
          gcongr; exact dvrAbv_le_one c
      _ = _ := mul_one _


end DVRNorm

section NormLemmas

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {K : Type v} [NormedField K] [Algebra A K] [IsFractionRing A K]
  (hn : ∀ x : K, ‖x‖ = dvrAbv A K x)
include hn

lemma dvr_isUltrametricDist : IsUltrametricDist K := by
  refine IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm ?_
  intro x y
  simp only [hn]
  exact dvrAbv_isNonarch x y

lemma dvr_norm_le_one (a : A) : ‖algebraMap A K a‖ ≤ 1 := by
  rw [hn]; exact dvrAbv_le_one a

lemma dvr_norm_lt_one_iff (a : A) : ‖algebraMap A K a‖ < 1 ↔ a ∈ maximalIdeal A := by
  rw [hn]; exact dvrAbv_lt_one_iff a

lemma dvr_exists_of_norm_le_one (x : K) (hx : ‖x‖ ≤ 1) : ∃ a : A, algebraMap A K a = x :=
  exists_of_dvrAbv_le_one x (by rwa [← hn])

variable {π : A} (hπ : Irreducible π)
include hπ

lemma dvr_norm_pi_pos : 0 < ‖algebraMap A K π‖ := by
  rw [hn]; exact dvrAbv_pi_pos hπ

lemma dvr_norm_pi_lt_one : ‖algebraMap A K π‖ < 1 := by
  rw [hn]; exact dvrAbv_pi_lt_one hπ

lemma dvr_norm_le_pow_iff (a : A) (k : ℕ) :
    ‖algebraMap A K a‖ ≤ ‖algebraMap A K π‖ ^ k ↔ a ∈ maximalIdeal A ^ k := by
  simp only [hn]; exact dvrAbv_le_pow_iff hπ a k

omit hπ in
lemma dvr_norm_eq_one_iff (a : A) : ‖algebraMap A K a‖ = 1 ↔ IsUnit a := by
  rw [hn]; exact dvrAbv_eq_one_iff a

/-- An element of `𝔪 ∖ 𝔪²` has norm exactly `‖π‖`. -/
lemma dvr_norm_eq_of_mem_not_mem_sq {a : A} (h1 : a ∈ maximalIdeal A) (h2 : a ∉ maximalIdeal A ^ 2) :
    ‖algebraMap A K a‖ = ‖algebraMap A K π‖ := by
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at h1
  obtain ⟨b, rfl⟩ := h1
  have hb : IsUnit b := by
    by_contra hb
    apply h2
    have hbm : b ∈ maximalIdeal A := (mem_maximalIdeal _).2 hb
    rw [pow_two]
    exact Ideal.mul_mem_mul hbm (hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  rw [map_mul, norm_mul, (dvr_norm_eq_one_iff hn b).2 hb, one_mul]

omit hπ in
lemma dvr_nontrivial : ∃ x : K, 1 < ‖x‖ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  refine ⟨(algebraMap A K π)⁻¹, ?_⟩
  rw [norm_inv]
  exact one_lt_inv₀ (dvr_norm_pi_pos hn hπ) |>.2 (dvr_norm_pi_lt_one hn hπ)


omit hπ in
lemma dvr_completeSpace [IsAdicComplete (maximalIdeal A) A] : CompleteSpace K := by
  have hU := dvr_isUltrametricDist hn
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  set ρ : K := algebraMap A K π with hρ
  have hρ0 : 0 < ‖ρ‖ := dvr_norm_pi_pos hn hπ
  have hρ1 : ‖ρ‖ < 1 := dvr_norm_pi_lt_one hn hπ
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hu.isBounded_range
  have hC' : 0 < |C| + 1 := by positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hC') hρ1
  have hv : ∀ n, ‖ρ ^ m * u n‖ ≤ 1 := by
    intro n
    rw [norm_mul, norm_pow]
    have h1 : ‖u n‖ ≤ |C| + 1 := (hC _ ⟨n, rfl⟩).trans (by linarith [le_abs_self C])
    calc ‖ρ‖ ^ m * ‖u n‖ ≤ ‖ρ‖ ^ m * (|C| + 1) := by gcongr
      _ ≤ 1 := by
        calc ‖ρ‖ ^ m * (|C| + 1) ≤ (|C| + 1)⁻¹ * (|C| + 1) := by gcongr
          _ = 1 := inv_mul_cancel₀ hC'.ne'
  choose a ha using fun n => dvr_exists_of_norm_le_one hn _ (hv n)
  have hdiff : ∀ n n', ‖algebraMap A K (a n - a n')‖ ≤ dist (u n) (u n') := by
    intro n n'
    rw [map_sub, ha, ha, ← mul_sub, norm_mul, norm_pow, ← dist_eq_norm]
    calc ‖ρ‖ ^ m * dist (u n) (u n') ≤ 1 * dist (u n) (u n') := by
          gcongr; exact pow_le_one₀ hρ0.le hρ1.le
      _ = _ := one_mul _
  have hN : ∀ k, ∃ N : ℕ, ∀ n ≥ N, ∀ n' ≥ N, dist (u n) (u n') < ‖ρ‖ ^ k := fun k =>
    Metric.cauchySeq_iff.1 hu _ (pow_pos hρ0 k)
  choose N hN using hN
  set M : ℕ → ℕ := fun k => k + ∑ j ∈ Finset.range (k + 1), N j with hMdef
  have hMN : ∀ j k, j ≤ k → N j ≤ M k := by
    intro j k hjk
    have : N j ≤ ∑ i ∈ Finset.range (k + 1), N i :=
      Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
    simp only [hMdef]; omega
  have hMtend : Filter.Tendsto M Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun k => Nat.le_add_right k _) Filter.tendsto_id
  have hf : ∀ {j k : ℕ}, j ≤ k →
      (fun i => a (M i)) j ≡ (fun i => a (M i)) k [SMOD ((maximalIdeal A) ^ j • ⊤ : Submodule A A)] := by
    intro j k hjk
    rw [SModEq.sub_mem]
    have h1 := (hdiff (M j) (M k)).trans (hN j _ (hMN j j le_rfl) _ (hMN j k hjk)).le
    have := (dvr_norm_le_pow_iff hn hπ _ j).1 h1
    simpa using this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := maximalIdeal A) (M := A) inferInstance hf
  have hρne : ρ ≠ 0 := hρ0.ne' |> fun h => norm_pos_iff.1 hρ0 
  refine ⟨(ρ ^ m)⁻¹ * algebraMap A K L, tendsto_nhds_of_cauchySeq_of_subseq hu hMtend ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
    (by simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).const_mul ((‖ρ‖ ^ m)⁻¹)))
  have e : (u ∘ M) k - (ρ ^ m)⁻¹ * algebraMap A K L = (ρ ^ m)⁻¹ * algebraMap A K (a (M k) - L) := by
    rw [map_sub, ha]; simp only [Function.comp]; field_simp
  rw [e, norm_mul, norm_inv, norm_pow]
  gcongr
  have := (SModEq.sub_mem.1 (hL k))
  have h2 := (dvr_norm_le_pow_iff hn hπ (a (M k) - L) k).2 (by simpa using this)
  exact h2

omit hπ in
lemma dvr_isCompact_closedBall [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)] :
    IsCompact (Metric.closedBall (0 : K) 1) := by
  have := dvr_completeSpace hn
  rw [isCompact_iff_totallyBounded_isComplete]
  refine ⟨?_, Metric.isClosed_closedBall.isComplete⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (dvr_norm_pi_lt_one hn hπ)
  have : Finite (A ⧸ maximalIdeal A ^ k) := inferInstance
  refine ⟨Set.range (fun q : A ⧸ maximalIdeal A ^ k => algebraMap A K (Quotient.out q)),
    Set.finite_range _, ?_⟩
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  obtain ⟨b, rfl⟩ := dvr_exists_of_norm_le_one hn x hx
  simp only [Set.mem_iUnion, Metric.mem_ball, Set.mem_range, exists_prop]
  refine ⟨_, ⟨Ideal.Quotient.mk (maximalIdeal A ^ k) b, rfl⟩, ?_⟩
  have h1 : Ideal.Quotient.mk (maximalIdeal A ^ k) (Quotient.out (Ideal.Quotient.mk (maximalIdeal A ^ k) b))
      = Ideal.Quotient.mk (maximalIdeal A ^ k) b := Quotient.out_eq _
  rw [Ideal.Quotient.eq] at h1
  rw [dist_comm, dist_eq_norm, ← map_sub]
  exact lt_of_le_of_lt ((dvr_norm_le_pow_iff hn hπ _ k).2 h1) hk

end NormLemmas

section Instances

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]

/-- The nontrivially normed field structure on `K` from the (2-adic) absolute value of the DVR `A`. -/
@[instance_reducible] noncomputable def dvrNontriviallyNormedField : NontriviallyNormedField K :=
  { dvrNormedField A K with
    non_trivial := by
      let _ := dvrNormedField A K
      exact dvr_nontrivial (A := A) (K := K) (fun _ => rfl) }

end Instances


end NumberFieldKB.MilneANT
