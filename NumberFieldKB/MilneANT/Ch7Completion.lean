import NumberFieldKB.MilneANT.Ch7Basic
import Mathlib.Computability.Reduce
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Connected.Separation
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Milne, *Algebraic Number Theory*, Chapter 7: completions in the nonarchimedean case

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Setting (Milne p. 116): a field with a discrete nonarchimedean absolute value. Here $K$ is a normed field with an
ultrametric norm (`IsUltrametricDist K`); its absolute value is `NormedField.toAbsoluteValue K` and the completion
$\hat K$ is `UniformSpace.Completion K` (a normed field). The ring $A = \{|a| \le 1\}$ is the valuation subring
`absValuationSubring` of Proposition 7.6, written `unitBall K`.

* **Lemma 7.25** (`lemma_7_25`): $A/\mathfrak m^n \to \hat A/\hat{\mathfrak m}^n$ is an isomorphism.
* **Proposition 7.26** (`prop_7_26`): every element of $\hat K$ has a unique expansion
  $\sum_{i \ge -n} a_i \pi^i$ with digits $a_i$ in a set of representatives of $A/\mathfrak m$.
* **Example 7.28** (`example_7_28`): $-1$ is a square in $\mathbb Q_5$.
* **Example 7.29** (`example_7_29_tendsto_iff`, `example_7_29_summable`): convergence of the $p$-adic exponential.
* **Aside 7.30** (`aside_7_30`): for the discrete valuation ring $A$, $\varprojlim A/\mathfrak m^n \cong \hat A$.
-/

open IsLocalRing Filter Topology

namespace NumberFieldKB.MilneANT

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- An ultrametric norm is a nonarchimedean absolute value. -/
theorem isNonarchimedean_toAbsoluteValue : IsNonarchimedean (NormedField.toAbsoluteValue K) := by
  intro x y
  exact IsUltrametricDist.norm_add_le_max x y

/-- The completion of a field with an ultrametric norm is ultrametric. -/
instance instIsUltrametricDistCompletion : IsUltrametricDist (UniformSpace.Completion K) := by
  apply IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih a b =>
    rw [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    exact IsUltrametricDist.norm_add_le_max a b

/-- The ring $A = \{a \in K : |a| \le 1\}$ (Milne p. 116), the valuation subring of Proposition 7.6. -/
noncomputable abbrev unitBall : ValuationSubring K :=
  absValuationSubring (NormedField.toAbsoluteValue K) (isNonarchimedean_toAbsoluteValue K)

/-- The inclusion $A \to \hat A$ of the unit ball of $K$ into the unit ball of the completion $\hat K$. -/
noncomputable def unitBallCompletionHom : unitBall K →+* unitBall (UniformSpace.Completion K) :=
  RingHom.codRestrict (((UniformSpace.Completion.coeRingHom : K →+* UniformSpace.Completion K)).comp
    (unitBall K).subtype) (unitBall (UniformSpace.Completion K)).toSubring (by
      intro a
      show ‖((a : K) : UniformSpace.Completion K)‖ ≤ 1
      rw [UniformSpace.Completion.norm_coe]
      exact a.2)

/-- Elements of the maximal ideal of `unitBall L` are those of norm `< 1`. -/
theorem mem_maximalIdeal_unitBall_iff {L : Type*} [NormedField L] [IsUltrametricDist L]
    (a : unitBall L) : a ∈ maximalIdeal (unitBall L) ↔ ‖(a : L)‖ < 1 := by
  have ha : ‖(a : L)‖ ≤ 1 := a.2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h
    by_contra h1
    have h1' : ‖(a : L)‖ = 1 := le_antisymm ha (not_lt.mp h1)
    apply h
    have h0 : (a : L) ≠ 0 := by
      intro h0; rw [h0] at h1'; simp at h1'
    have hinv : ‖(a : L)⁻¹‖ ≤ 1 := by simp [h1']
    exact IsUnit.of_mul_eq_one (⟨(a : L)⁻¹, hinv⟩ : unitBall L) (Subtype.ext (mul_inv_cancel₀ h0))
  · intro h hu
    obtain ⟨b, hab⟩ := hu.exists_right_inv
    have hb : ‖(b : L)‖ ≤ 1 := b.2
    have h3 : ‖(a : L)‖ * ‖(b : L)‖ = 1 := by
      rw [← norm_mul]
      have := congrArg (fun w : unitBall L => (w : L)) hab
      rw [show (a : L) * (b : L) = 1 by simpa using this, norm_one]
    nlinarith [norm_nonneg (a : L), norm_nonneg (b : L)]

theorem pow_maximalIdeal_le_comap (n : ℕ) :
    maximalIdeal (unitBall K) ^ n ≤
      (maximalIdeal (unitBall (UniformSpace.Completion K)) ^ n).comap (unitBallCompletionHom K) := by
  have h : (maximalIdeal (unitBall K)).map (unitBallCompletionHom K) ≤
      maximalIdeal (unitBall (UniformSpace.Completion K)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal_unitBall_iff]
    rw [mem_maximalIdeal_unitBall_iff] at ha
    show ‖((a : K) : UniformSpace.Completion K)‖ < 1
    rwa [UniformSpace.Completion.norm_coe]
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono h n

/-- Ultrametric inequality for differences. -/
theorem norm_sub_le_max' {L : Type*} [NormedField L] [IsUltrametricDist L] (x y : L) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg]
  simpa using IsUltrametricDist.norm_add_le_max x (-y)

/-- In an ultrametric normed group, `‖x - y‖ < ‖x‖` forces `‖y‖ = ‖x‖`. -/
theorem norm_eq_of_norm_sub_lt {L : Type*} [NormedField L] [IsUltrametricDist L] {x y : L}
    (h : ‖x - y‖ < ‖x‖) : ‖y‖ = ‖x‖ := by
  apply le_antisymm
  · have : y = x - (x - y) := by ring
    rw [this, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max x (-(x - y))).trans (max_le le_rfl ?_)
    rw [norm_neg]; exact h.le
  · have : x = y + (x - y) := by ring
    have h2 : ‖x‖ ≤ max ‖y‖ ‖x - y‖ := by
      calc ‖x‖ = ‖y + (x - y)‖ := by rw [← this]
        _ ≤ _ := IsUltrametricDist.norm_add_le_max _ _
    rcases max_cases ‖y‖ ‖x - y‖ with ⟨h3, _⟩ | ⟨h3, _⟩
    · rwa [h3] at h2
    · rw [h3] at h2; linarith

/-- If `π` has norm `< 1` and has the largest norm among elements of norm `< 1`, it generates the
maximal ideal of `unitBall L`. -/
theorem maximalIdeal_eq_span {L : Type*} [NormedField L] [IsUltrametricDist L] (π : unitBall L)
    (h1 : ‖(π : L)‖ < 1) (h2 : ∀ y : L, ‖y‖ < 1 → ‖y‖ ≤ ‖(π : L)‖) :
    maximalIdeal (unitBall L) = Ideal.span {π} := by
  apply le_antisymm
  · intro a ha
    rw [mem_maximalIdeal_unitBall_iff] at ha
    have hle := h2 _ ha
    rw [Ideal.mem_span_singleton']
    by_cases hπ : (π : L) = 0
    · refine ⟨0, ?_⟩
      have : (a : L) = 0 := by
        rw [hπ, norm_zero] at hle
        exact norm_le_zero_iff.mp hle
      exact Subtype.ext (by simp [this, hπ])
    · have hc : ‖(a : L) / (π : L)‖ ≤ 1 := by
        rw [norm_div, div_le_one (norm_pos_iff.2 hπ)]; exact hle
      refine ⟨⟨(a : L) / (π : L), hc⟩, Subtype.ext ?_⟩
      show (a : L) / (π : L) * (π : L) = a
      field_simp
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (mem_maximalIdeal_unitBall_iff π).2 h1

/-- Membership in a power of the maximal ideal in terms of the norm. -/
theorem mem_maximalIdeal_pow_iff {L : Type*} [NormedField L] [IsUltrametricDist L] (π : unitBall L)
    (hπ : maximalIdeal (unitBall L) = Ideal.span {π}) (a : unitBall L) (n : ℕ) :
    a ∈ maximalIdeal (unitBall L) ^ n ↔ ‖(a : L)‖ ≤ ‖(π : L)‖ ^ n := by
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    have hc : ‖(c : L)‖ ≤ 1 := c.2
    show ‖(c : L) * (π : L) ^ n‖ ≤ _
    rw [norm_mul, norm_pow]
    calc ‖(c : L)‖ * ‖(π : L)‖ ^ n ≤ 1 * ‖(π : L)‖ ^ n := by gcongr
      _ = _ := one_mul _
  · intro h
    by_cases hπ0 : (π : L) = 0
    · have hπ0' : π = 0 := Subtype.ext hπ0
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact ⟨a, by simp⟩
      · refine ⟨0, ?_⟩
        have : (a : L) = 0 := by
          rw [hπ0, norm_zero, zero_pow hn.ne'] at h
          exact norm_le_zero_iff.mp h
        exact Subtype.ext (by simp [this, hπ0'])
    · have hc : ‖(a : L) / (π : L) ^ n‖ ≤ 1 := by
        rw [norm_div, norm_pow, div_le_one (pow_pos (norm_pos_iff.2 hπ0) n)]; exact h
      refine ⟨⟨(a : L) / (π : L) ^ n, hc⟩, Subtype.ext ?_⟩
      show (a : L) / (π : L) ^ n * (π : L) ^ n = a
      field_simp

/-- A discrete absolute value has a gap around `1`. -/
theorem discrete_gap (hd : IsDiscreteAbv (NormedField.toAbsoluteValue K)) :
    ∃ ε > 0, ∀ a : K, a ≠ 0 → |‖a‖ - 1| < ε → ‖a‖ = 1 := by
  have h1 : IsOpen ({⟨1, ⟨1, by simp [NormedField.toAbsoluteValue]⟩⟩} :
      Set (Set.range fun x : Kˣ => (NormedField.toAbsoluteValue K) (x : K))) := by
    exact @isOpen_discrete _ _ hd _
  obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.1 h1
  have h1t : (1 : ℝ) ∈ t := by
    have : (⟨1, ⟨1, by simp [NormedField.toAbsoluteValue]⟩⟩ :
      Set.range fun x : Kˣ => (NormedField.toAbsoluteValue K) (x : K)) ∈ Subtype.val ⁻¹' t := by
      rw [hpre]; rfl
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 ht 1 h1t
  refine ⟨ε, hε, fun a ha hlt => ?_⟩
  have hmem : ‖a‖ ∈ Set.range fun x : Kˣ => (NormedField.toAbsoluteValue K) (x : K) :=
    ⟨Units.mk0 a ha, rfl⟩
  have : (⟨‖a‖, hmem⟩ : Set.range fun x : Kˣ => (NormedField.toAbsoluteValue K) (x : K)) ∈
      Subtype.val ⁻¹' t := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    exact hlt
  rw [hpre] at this
  exact congrArg Subtype.val this

/-- For a discrete absolute value, the maximal ideal of `A` is principal. -/
theorem exists_generator (hd : IsDiscreteAbv (NormedField.toAbsoluteValue K)) :
    ∃ π : unitBall K, maximalIdeal (unitBall K) = Ideal.span {π} := by
  obtain ⟨ε, hε, hgap⟩ := discrete_gap K hd
  by_cases hnt : ∃ a : K, a ≠ 0 ∧ ‖a‖ < 1
  · set T : Set ℝ := {t | ∃ a : K, a ≠ 0 ∧ ‖a‖ < 1 ∧ ‖a‖ = t} with hT
    obtain ⟨a0, ha0, ha01⟩ := hnt
    have hTne : T.Nonempty := ⟨‖a0‖, a0, ha0, ha01, rfl⟩
    have hTbdd : BddAbove T := ⟨1, by rintro t ⟨a, -, ha, rfl⟩; exact ha.le⟩
    have hs : 0 < sSup T :=
      lt_of_lt_of_le (norm_pos_iff.2 ha0) (le_csSup hTbdd ⟨a0, ha0, ha01, rfl⟩)
    obtain ⟨t, ⟨b, hb0, hb1, rfl⟩, hlt⟩ :=
      exists_lt_of_lt_csSup hTne (show sSup T * (1 - ε) < sSup T by nlinarith)
    have hmax : ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ‖b‖ := by
      intro a ha
      by_contra hcon
      push Not at hcon
      have ha0' : a ≠ 0 := by
        intro h; rw [h, norm_zero] at hcon; exact absurd hcon (not_lt.2 (norm_nonneg b))
      have hba : ‖b / a‖ < 1 := by
        rw [norm_div, div_lt_one (norm_pos_iff.2 ha0')]; exact hcon
      have hr : ‖b / a‖ ≤ 1 - ε := by
        by_contra hr
        push Not at hr
        have := hgap (b / a) (div_ne_zero hb0 ha0') (by
          rw [abs_lt]; constructor <;> linarith)
        linarith
      have hpos : 0 < ‖b / a‖ := norm_pos_iff.2 (div_ne_zero hb0 ha0')
      rw [norm_div, div_le_iff₀ (norm_pos_iff.2 ha0')] at hr
      have hle : ‖a‖ ≤ sSup T := le_csSup hTbdd ⟨a, ha0', ha, rfl⟩
      have h1ε : 0 < 1 - ε := by
        have := hpos; rw [norm_div] at this; nlinarith [norm_pos_iff.2 ha0', norm_pos_iff.2 hb0]
      nlinarith
    exact ⟨⟨b, hb1.le⟩, maximalIdeal_eq_span _ hb1 hmax⟩
  · push Not at hnt
    refine ⟨0, maximalIdeal_eq_span _ (by simp) ?_⟩
    intro y hy
    by_cases hy0 : y = 0
    · simp [hy0]
    · exact absurd hy (not_lt.2 (hnt y hy0))

/-- Elements of `K` approximate elements of the completion arbitrarily well. -/
theorem exists_approx (y : UniformSpace.Completion K) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : K, ‖y - (a : UniformSpace.Completion K)‖ < ε := by
  obtain ⟨a, ha⟩ := (UniformSpace.Completion.denseRange_coe (α := K)).exists_dist_lt y hε
  exact ⟨a, by rwa [dist_eq_norm] at ha⟩

/-- Elements of the completion of norm `< 1` have norm at most `‖π‖`. -/
theorem completion_norm_le (π : unitBall K) (hπ : maximalIdeal (unitBall K) = Ideal.span {π})
    (y : UniformSpace.Completion K) (hy : ‖y‖ < 1) : ‖y‖ ≤ ‖(π : K)‖ := by
  by_cases hy0 : y = 0
  · simp [hy0]
  obtain ⟨a, ha⟩ := exists_approx K y (norm_pos_iff.2 hy0)
  have h1 : ‖(a : UniformSpace.Completion K)‖ = ‖y‖ := norm_eq_of_norm_sub_lt ha
  rw [UniformSpace.Completion.norm_coe] at h1
  have ha1 : ‖a‖ ≤ 1 := by rw [h1]; exact hy.le
  have hmem : (⟨a, ha1⟩ : unitBall K) ∈ maximalIdeal (unitBall K) ^ 1 := by
    rw [pow_one, mem_maximalIdeal_unitBall_iff]
    show ‖a‖ < 1
    rw [h1]; exact hy
  rw [mem_maximalIdeal_pow_iff π hπ, pow_one] at hmem
  rw [← h1]; exact hmem

/-- The maximal ideal of `Â` is generated by the image of a generator of that of `A`. -/
theorem maximalIdeal_completion (π : unitBall K) (hπ : maximalIdeal (unitBall K) = Ideal.span {π}) :
    maximalIdeal (unitBall (UniformSpace.Completion K)) = Ideal.span {unitBallCompletionHom K π} := by
  have hπm : π ∈ maximalIdeal (unitBall K) := by
    rw [hπ]; exact Ideal.mem_span_singleton_self π
  rw [mem_maximalIdeal_unitBall_iff] at hπm
  apply maximalIdeal_eq_span
  · show ‖((π : K) : UniformSpace.Completion K)‖ < 1
    rwa [UniformSpace.Completion.norm_coe]
  · intro y hy
    show ‖y‖ ≤ ‖((π : K) : UniformSpace.Completion K)‖
    rw [UniformSpace.Completion.norm_coe]
    exact completion_norm_le K π hπ y hy

/-- Elements of `Â` are approximated by elements of `A` modulo `π^n`. -/
theorem exists_approx_pow (π : unitBall K) (hπ : maximalIdeal (unitBall K) = Ideal.span {π})
    (y : unitBall (UniformSpace.Completion K)) (n : ℕ) :
    ∃ a : unitBall K, ‖((y : UniformSpace.Completion K)) - ((a : K) : UniformSpace.Completion K)‖ ≤
      ‖(π : K)‖ ^ n := by
  have hy : ‖(y : UniformSpace.Completion K)‖ ≤ 1 := y.2
  have hπm : π ∈ maximalIdeal (unitBall K) := by
    rw [hπ]; exact Ideal.mem_span_singleton_self π
  rw [mem_maximalIdeal_unitBall_iff] at hπm
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, by simpa using hy⟩
  have hint : ∀ a : K, ‖(y : UniformSpace.Completion K) - (a : UniformSpace.Completion K)‖ < 1 →
      ‖a‖ ≤ 1 := by
    intro a ha
    have : ‖(a : UniformSpace.Completion K)‖ ≤ 1 := by
      have e : (a : UniformSpace.Completion K) = (y : UniformSpace.Completion K) -
          ((y : UniformSpace.Completion K) - (a : UniformSpace.Completion K)) := by ring
      rw [e]
      refine (norm_sub_le_max' _ _).trans (max_le hy ha.le)
    rwa [UniformSpace.Completion.norm_coe] at this
  by_cases hπ0 : ‖(π : K)‖ = 0
  · obtain ⟨a, ha⟩ := exists_approx K (y : UniformSpace.Completion K) one_pos
    refine ⟨⟨a, hint a ha⟩, ?_⟩
    have := completion_norm_le K π hπ _ ha
    rw [hπ0, zero_pow hn.ne']
    rw [hπ0] at this
    exact this
  · have hpos : 0 < ‖(π : K)‖ ^ n := pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hπ0)) n
    obtain ⟨a, ha⟩ := exists_approx K (y : UniformSpace.Completion K) hpos
    have hle1 : ‖(π : K)‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hπm.le
    exact ⟨⟨a, hint a (ha.trans_le hle1)⟩, ha.le⟩

/-- **Lemma 7.25.** Let $|\cdot|$ be a discrete nonarchimedean absolute value on $K$, with ring $A$ and maximal ideal
$\mathfrak m$, and let $\hat A$, $\hat{\mathfrak m}$ be the corresponding objects for the completion $\hat K$. For every
$n \in \mathbb N$ the map $A/\mathfrak m^n \to \hat A/\hat{\mathfrak m}^n$ is an isomorphism. -/
@[kb "milne2020ant" "v3.08, Lemma 7.25, p. 116"]
theorem lemma_7_25 (hd : IsDiscreteAbv (NormedField.toAbsoluteValue K)) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap (maximalIdeal (unitBall (UniformSpace.Completion K)) ^ n)
      (unitBallCompletionHom K) (pow_maximalIdeal_le_comap K n)) := by
  obtain ⟨π, hπ⟩ := exists_generator K hd
  have hπ' := maximalIdeal_completion K π hπ
  have hnorm : ‖((unitBallCompletionHom K π : unitBall (UniformSpace.Completion K)) :
      UniformSpace.Completion K)‖ = ‖(π : K)‖ := UniformSpace.Completion.norm_coe _
  constructor
  · apply Ideal.quotientMap_injective'
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal_pow_iff _ hπ'] at ha
    rw [mem_maximalIdeal_pow_iff π hπ]
    rw [hnorm] at ha
    have e : ‖((unitBallCompletionHom K a : unitBall (UniformSpace.Completion K)) :
        UniformSpace.Completion K)‖ = ‖(a : K)‖ := UniformSpace.Completion.norm_coe _
    rwa [e] at ha
  · intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := exists_approx_pow K π hπ y n
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, mem_maximalIdeal_pow_iff _ hπ', hnorm]
    show ‖((a : K) : UniformSpace.Completion K) - (y : UniformSpace.Completion K)‖ ≤ _
    rw [norm_sub_rev]
    exact ha

/-- For a nontrivial absolute value, a generator of the maximal ideal has positive norm. -/
theorem norm_gen_pos (hnt : (NormedField.toAbsoluteValue K).IsNontrivial) (π : unitBall K)
    (hπ : maximalIdeal (unitBall K) = Ideal.span {π}) : 0 < ‖(π : K)‖ := by
  by_contra h
  have hπ0 : (π : K) = 0 := norm_le_zero_iff.1 (not_lt.1 h)
  obtain ⟨x, hx0, hx1⟩ := hnt
  have hx1' : ‖x‖ ≠ 1 := hx1
  have key : ∃ y : K, y ≠ 0 ∧ ‖y‖ < 1 := by
    rcases lt_or_gt_of_ne hx1' with h | h
    · exact ⟨x, hx0, h⟩
    · exact ⟨x⁻¹, inv_ne_zero hx0, by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h⟩
  obtain ⟨y, hy0, hy1⟩ := key
  have hmem : (⟨y, hy1.le⟩ : unitBall K) ∈ maximalIdeal (unitBall K) ^ 1 := by
    rw [pow_one, mem_maximalIdeal_unitBall_iff]; exact hy1
  rw [mem_maximalIdeal_pow_iff π hπ] at hmem
  rw [hπ0] at hmem
  simp only [norm_zero, pow_one] at hmem
  exact hy0 (norm_le_zero_iff.1 hmem)

/-- Norm of the `i`-th term of an expansion. -/
theorem norm_term_le (π : unitBall K) (a : unitBall K) (i : ℤ) (hq : 0 < ‖(π : K)‖) :
    ‖(((a : K) : UniformSpace.Completion K)) * ((π : K) : UniformSpace.Completion K) ^ i‖ ≤
      ‖(π : K)‖ ^ i := by
  rw [norm_mul, norm_zpow, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  calc ‖(a : K)‖ * ‖(π : K)‖ ^ i ≤ 1 * ‖(π : K)‖ ^ i := by
        gcongr
        exact a.2
    _ = _ := one_mul _

/-- Series with digits vanishing for small index converge. -/
theorem summable_expansion (π : unitBall K) (hπlt : ‖(π : K)‖ < 1) (hq : 0 < ‖(π : K)‖)
    (a : ℤ → unitBall K) (N : ℤ) (ha : ∀ i < N, a i = 0) :
    Summable fun i : ℤ => (((a i : K) : UniformSpace.Completion K)) *
      ((π : K) : UniformSpace.Completion K) ^ i := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε hπlt
  rw [Filter.eventually_cofinite]
  refine (Set.finite_Icc N (M : ℤ)).subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq, dist_zero_right, not_lt] at hi
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    rw [ha i hlt] at hi
    simp at hi
    linarith
  · by_contra hlt
    rw [not_le] at hlt
    have h1 := (norm_term_le K π (a i) i hq).trans (zpow_le_zpow_right_of_le_one₀ hq hπlt.le hlt.le)
    rw [zpow_natCast] at h1
    linarith

/-- Distinct elements of a set of representatives differ by a unit. -/
theorem norm_sub_eq_one_of_ne (S : Set (unitBall K)) (hS : Set.BijOn (residue (unitBall K)) S Set.univ)
    {u v : unitBall K} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) : ‖((u : K) - (v : K))‖ = 1 := by
  have hres : residue (unitBall K) u ≠ residue (unitBall K) v := fun h => huv (hS.injOn hu hv h)
  have hnm : u - v ∉ maximalIdeal (unitBall K) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hres
  rw [mem_maximalIdeal_unitBall_iff, not_lt] at hnm
  have h1 : ‖((u - v : unitBall K) : K)‖ ≤ 1 := (u - v).2
  exact le_antisymm h1 hnm

/-- Uniqueness of expansions. -/
theorem expansion_unique (S : Set (unitBall K)) (hS : Set.BijOn (residue (unitBall K)) S Set.univ)
    (π : unitBall K) (hπlt : ‖(π : K)‖ < 1) (hq : 0 < ‖(π : K)‖)
    (a b : ℤ → unitBall K) (ha : ∀ i, a i ∈ S) (hb : ∀ i, b i ∈ S) (Na Nb : ℤ)
    (ha0 : ∀ i < Na, a i = 0) (hb0 : ∀ i < Nb, b i = 0) (x : UniformSpace.Completion K)
    (hxa : HasSum (fun i : ℤ => (((a i : K) : UniformSpace.Completion K)) *
      ((π : K) : UniformSpace.Completion K) ^ i) x)
    (hxb : HasSum (fun i : ℤ => (((b i : K) : UniformSpace.Completion K)) *
      ((π : K) : UniformSpace.Completion K) ^ i) x) : a = b := by
  by_contra hne
  have hD : ∃ i, a i ≠ b i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  classical
  obtain ⟨j, hj, hjmin⟩ := Int.exists_least_of_bdd (P := fun i => a i ≠ b i)
    ⟨min Na Nb, fun z hz => by
      by_contra hlt
      rw [not_le] at hlt
      apply hz
      rw [ha0 z (lt_of_lt_of_le hlt (min_le_left _ _)), hb0 z (lt_of_lt_of_le hlt (min_le_right _ _))]⟩ hD
  set c : ℤ → UniformSpace.Completion K := fun i =>
    ((((a i : K) : UniformSpace.Completion K)) * ((π : K) : UniformSpace.Completion K) ^ i) -
    ((((b i : K) : UniformSpace.Completion K)) * ((π : K) : UniformSpace.Completion K) ^ i) with hcdef
  have hc : HasSum c 0 := by
    have := hxa.sub hxb
    rwa [sub_self] at this
  have hupd := hc.update j 0
  have hbound : ∀ i, ‖Function.update c j 0 i‖ ≤ ‖(π : K)‖ ^ (j + 1) := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self, norm_zero]
      positivity
    · rw [Function.update_of_ne hij]
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have : a i = b i := by
          by_contra hne'
          exact absurd (hjmin i hne') (not_le.2 hlt)
        simp [hcdef, this]
        positivity
      · have h1 : ‖c i‖ ≤ ‖(π : K)‖ ^ i := by
          refine (norm_sub_le_max' _ _).trans (max_le (norm_term_le K π (a i) i hq)
            (norm_term_le K π (b i) i hq))
        exact h1.trans (zpow_le_zpow_right_of_le_one₀ hq hπlt.le (by omega))
  have hnorm := IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) hbound
  rw [hupd.tsum_eq] at hnorm
  have hcj : ‖c j‖ = ‖(π : K)‖ ^ j := by
    have : c j = (((a j : K) - (b j : K) : K) : UniformSpace.Completion K) *
        ((π : K) : UniformSpace.Completion K) ^ j := by
      simp only [hcdef, UniformSpace.Completion.coe_sub]; ring
    rw [this, norm_mul, norm_zpow, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe,
      norm_sub_eq_one_of_ne K S hS (ha j) (hb j) hj, one_mul]
  rw [zero_sub, add_zero, norm_neg, hcj] at hnorm
  rw [zpow_add_one₀ hq.ne'] at hnorm
  have hpos : 0 < ‖(π : K)‖ ^ j := zpow_pos hq j
  nlinarith

/-- Every element of the unit ball of `Â` is congruent to an element of `S` modulo `m̂`. -/
theorem digit_exists (S : Set (unitBall K)) (hS : Set.BijOn (residue (unitBall K)) S Set.univ)
    (π : unitBall K) (hπ : maximalIdeal (unitBall K) = Ideal.span {π}) (hπlt : ‖(π : K)‖ < 1)
    (y : UniformSpace.Completion K) (hy : ‖y‖ ≤ 1) :
    ∃ s ∈ S, ‖y - ((s : K) : UniformSpace.Completion K)‖ < 1 := by
  obtain ⟨a0, ha0⟩ := exists_approx_pow K π hπ ⟨y, hy⟩ 1
  rw [pow_one] at ha0
  obtain ⟨s, hsS, hsres⟩ := hS.surjOn (Set.mem_univ (residue (unitBall K) a0))
  refine ⟨s, hsS, ?_⟩
  have hm : a0 - s ∈ maximalIdeal (unitBall K) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hsres, sub_self]
  rw [mem_maximalIdeal_unitBall_iff] at hm
  have e : y - ((s : K) : UniformSpace.Completion K) =
      (y - ((a0 : K) : UniformSpace.Completion K)) + (((a0 - s : unitBall K) : K) : UniformSpace.Completion K) := by
    have : (((a0 - s : unitBall K) : K)) = (a0 : K) - (s : K) := rfl
    rw [this, UniformSpace.Completion.coe_sub]; ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (lt_of_le_of_lt ha0 hπlt) ?_)
  rw [UniformSpace.Completion.norm_coe]; exact hm

/-- The `k`-th digit in the greedy expansion. -/
private noncomputable def expDig (S : Set (unitBall K)) (π : unitBall K) (N : ℤ) (k : ℕ)
    (y : UniformSpace.Completion K) : unitBall K :=
  open Classical in
  if h : ∃ s ∈ S, ‖y / ((π : K) : UniformSpace.Completion K) ^ (N + k) -
      ((s : K) : UniformSpace.Completion K)‖ < 1 then h.choose else 0

/-- The remainders in the greedy expansion. -/
private noncomputable def expRem (S : Set (unitBall K)) (π : unitBall K) (N : ℤ)
    (x : UniformSpace.Completion K) : ℕ → UniformSpace.Completion K
  | 0 => x
  | k + 1 => expRem S π N x k - (((expDig K S π N k (expRem S π N x k) : unitBall K) : K) :
      UniformSpace.Completion K) * ((π : K) : UniformSpace.Completion K) ^ (N + k)

private theorem expDig_mem (S : Set (unitBall K)) (h0 : (0 : unitBall K) ∈ S) (π : unitBall K) (N : ℤ)
    (k : ℕ) (y : UniformSpace.Completion K) : expDig K S π N k y ∈ S := by
  unfold expDig
  split_ifs with h
  · exact h.choose_spec.1
  · exact h0

private theorem expDig_spec (S : Set (unitBall K)) (hS : Set.BijOn (residue (unitBall K)) S Set.univ)
    (π : unitBall K) (hπ : maximalIdeal (unitBall K) = Ideal.span {π}) (hπlt : ‖(π : K)‖ < 1)
    (hq : 0 < ‖(π : K)‖) (N : ℤ) (k : ℕ) (y : UniformSpace.Completion K)
    (hy : ‖y‖ ≤ ‖(π : K)‖ ^ (N + k)) :
    ‖y / ((π : K) : UniformSpace.Completion K) ^ (N + k) -
      (((expDig K S π N k y : unitBall K) : K) : UniformSpace.Completion K)‖ < 1 := by
  have hex : ∃ s ∈ S, ‖y / ((π : K) : UniformSpace.Completion K) ^ (N + k) -
      ((s : K) : UniformSpace.Completion K)‖ < 1 := by
    apply digit_exists K S hS π hπ hπlt
    rw [norm_div, norm_zpow, UniformSpace.Completion.norm_coe,
      div_le_one (zpow_pos hq _)]
    exact hy
  unfold expDig
  rw [dif_pos hex]
  exact hex.choose_spec.2

private theorem expRem_norm (S : Set (unitBall K)) (hS : Set.BijOn (residue (unitBall K)) S Set.univ)
    (π : unitBall K) (hπ : maximalIdeal (unitBall K) = Ideal.span {π}) (hπlt : ‖(π : K)‖ < 1)
    (hq : 0 < ‖(π : K)‖) (N : ℤ) (x : UniformSpace.Completion K) (hx : ‖x‖ ≤ ‖(π : K)‖ ^ N) (k : ℕ) :
    ‖expRem K S π N x k‖ ≤ ‖(π : K)‖ ^ (N + k) := by
  induction k with
  | zero => simpa [expRem] using hx
  | succ k ih =>
    have hspec := expDig_spec K S hS π hπ hπlt hq N k _ ih
    have hnorm : ‖((π : K) : UniformSpace.Completion K)‖ = ‖(π : K)‖ := UniformSpace.Completion.norm_coe _
    have hne : ((π : K) : UniformSpace.Completion K) ≠ 0 := by
      intro h; rw [h, norm_zero] at hnorm; exact hq.ne hnorm
    have hle := completion_norm_le K π hπ _ hspec
    set d := (((expDig K S π N k (expRem K S π N x k) : unitBall K) : K) : UniformSpace.Completion K)
    have e : expRem K S π N x (k + 1) =
        (expRem K S π N x k / ((π : K) : UniformSpace.Completion K) ^ (N + k) - d) *
          ((π : K) : UniformSpace.Completion K) ^ (N + k) := by
      show expRem K S π N x k - d * ((π : K) : UniformSpace.Completion K) ^ (N + k) = _
      field_simp
    rw [e, norm_mul, norm_zpow, hnorm]
    have : (N + ((k + 1 : ℕ) : ℤ)) = (N + k) + 1 := by push_cast; ring
    rw [this, zpow_add_one₀ hq.ne']
    calc _ ≤ ‖(π : K)‖ * ‖(π : K)‖ ^ (N + k) := by gcongr
      _ = _ := mul_comm _ _

/-- Existence of expansions. -/
theorem expansion_exists (S : Set (unitBall K)) (hS : Set.BijOn (residue (unitBall K)) S Set.univ)
    (h0 : (0 : unitBall K) ∈ S) (π : unitBall K) (hπ : maximalIdeal (unitBall K) = Ideal.span {π})
    (hπlt : ‖(π : K)‖ < 1) (hq : 0 < ‖(π : K)‖) (x : UniformSpace.Completion K) :
    ∃ a : ℤ → unitBall K, (∀ i, a i ∈ S) ∧ (∃ N : ℤ, ∀ i < N, a i = 0) ∧
      HasSum (fun i : ℤ => (((a i : K) : UniformSpace.Completion K)) *
        ((π : K) : UniformSpace.Completion K) ^ i) x := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ‖x‖ ≤ ‖(π : K)‖ ^ N := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖x‖ ((one_lt_inv₀ hq).2 hπlt)
    refine ⟨-(n : ℤ), ?_⟩
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact hn.le
  let A : ℤ → unitBall K := fun i =>
    if N ≤ i then expDig K S π N (i - N).toNat (expRem K S π N x (i - N).toNat) else 0
  have hA0 : ∀ i < N, A i = 0 := by
    intro i hi
    simp [A, not_le.2 hi]
  refine ⟨A, ?_, ⟨N, hA0⟩, ?_⟩
  · intro i
    by_cases h : N ≤ i
    · simp only [A, if_pos h]
      exact expDig_mem K S h0 π N _ _
    · simp only [A, if_neg h]
      exact h0
  · obtain ⟨s, hs⟩ := summable_expansion K π hπlt hq A N hA0
    suffices hsx : s = x by rw [hsx] at hs; exact hs
    let g : ℕ → ℤ := fun k => N + k
    have hg : Function.Injective g := by
      intro a b h
      simpa [g] using h
    have hs' : HasSum ((fun i : ℤ => (((A i : K) : UniformSpace.Completion K)) *
        ((π : K) : UniformSpace.Completion K) ^ i) ∘ g) s := by
      refine (hg.hasSum_iff (fun i hi => ?_)).2 hs
      have : i < N := by
        by_contra h
        rw [not_lt] at h
        exact hi ⟨(i - N).toNat, by simp only [g]; omega⟩
      simp [hA0 i this]
    have ht1 := hs'.tendsto_sum_nat
    have hterm : ∀ k : ℕ, ((fun i : ℤ => (((A i : K) : UniformSpace.Completion K)) *
        ((π : K) : UniformSpace.Completion K) ^ i) ∘ g) k =
        (((expDig K S π N k (expRem K S π N x k) : unitBall K) : K) : UniformSpace.Completion K) *
          ((π : K) : UniformSpace.Completion K) ^ (N + k) := by
      intro k
      have h1 : (N + (k : ℤ) - N).toNat = k := by omega
      have h2 : N ≤ N + (k : ℤ) := by omega
      simp only [Function.comp, g, A, if_pos h2, h1]
    have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range n, ((fun i : ℤ => (((A i : K) : UniformSpace.Completion K)) *
        ((π : K) : UniformSpace.Completion K) ^ i) ∘ g) k = x - expRem K S π N x n := by
      intro n
      induction n with
      | zero => simp [expRem]
      | succ n ih =>
        rw [Finset.sum_range_succ, ih, hterm n]
        show _ = x - (expRem K S π N x n - _)
        ring
    have hrem : Filter.Tendsto (fun n => expRem K S π N x n) Filter.atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun n : ℕ => ‖(π : K)‖ ^ N * ‖(π : K)‖ ^ n)
        (fun n => ?_) ?_
      · have := expRem_norm K S hS π hπ hπlt hq N x hN n
        rwa [zpow_add₀ hq.ne', zpow_natCast] at this
      · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hπlt).const_mul (‖(π : K)‖ ^ N)
    have ht2 : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
        ((fun i : ℤ => (((A i : K) : UniformSpace.Completion K)) *
        ((π : K) : UniformSpace.Completion K) ^ i) ∘ g) k) Filter.atTop (𝓝 x) := by
      simp_rw [hpart]
      simpa using (tendsto_const_nhds (x := x)).sub hrem
    exact tendsto_nhds_unique ht1 ht2

/-- **Proposition 7.26.** Let $|\cdot|$ be a nontrivial discrete nonarchimedean absolute value on $K$, let $S \subset A$
be a set of representatives for $A/\mathfrak m$ containing $0$, and let $\pi$ generate $\mathfrak m$. Every series
$\sum_{i \ge -n} a_i \pi^i$ with $a_i \in S$ converges in $\hat K$, and every element of $\hat K$ is the sum of exactly
one such series. Series are indexed by $i \in \mathbb Z$ with $a_i = 0$ for $i$ small; Milne's convention that the
representatives contain $0$ is implicit in his uniqueness argument ("$\sum a_i\pi^i = 0$ only if all $a_i = 0$"). -/
@[kb "milne2020ant" "v3.08, Prop. 7.26, p. 116"]
theorem prop_7_26 (hd : IsDiscreteAbv (NormedField.toAbsoluteValue K))
    (hnt : (NormedField.toAbsoluteValue K).IsNontrivial) (S : Set (unitBall K))
    (hS : Set.BijOn (residue (unitBall K)) S Set.univ) (h0 : (0 : unitBall K) ∈ S) (π : unitBall K)
    (hπ : maximalIdeal (unitBall K) = Ideal.span {π}) :
    (∀ a : ℤ → unitBall K, (∀ i, a i ∈ S) → (∃ N : ℤ, ∀ i < N, a i = 0) →
      Summable fun i : ℤ => (((a i : K) : UniformSpace.Completion K)) * ((π : K) : UniformSpace.Completion K) ^ i) ∧
    ∀ x : UniformSpace.Completion K, ∃! a : ℤ → unitBall K, (∀ i, a i ∈ S) ∧ (∃ N : ℤ, ∀ i < N, a i = 0) ∧
      HasSum (fun i : ℤ => (((a i : K) : UniformSpace.Completion K)) * ((π : K) : UniformSpace.Completion K) ^ i) x := by
  have hq := norm_gen_pos K hnt π hπ
  have hπlt : ‖(π : K)‖ < 1 := by
    have hπm : π ∈ maximalIdeal (unitBall K) := by
      rw [hπ]; exact Ideal.mem_span_singleton_self π
    exact (mem_maximalIdeal_unitBall_iff π).1 hπm
  refine ⟨fun a _ ⟨N, hN⟩ => summable_expansion K π hπlt hq a N hN, fun x => ?_⟩
  obtain ⟨a, haS, ⟨Na, ha0⟩, hsum⟩ := expansion_exists K S hS h0 π hπ hπlt hq x
  refine ⟨a, ⟨haS, ⟨Na, ha0⟩, hsum⟩, ?_⟩
  rintro b ⟨hbS, ⟨Nb, hb0⟩, hbsum⟩
  exact expansion_unique K S hS π hπlt hq b a hbS haS Nb Na hb0 ha0 x hbsum hsum

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **Example 7.28.** $-1$ is a square in $\mathbb Q_5$. (Milne constructs the $5$-adic digits by hand; the general
statement is QuadFormsKB's `QuadFormsKB.Binary.exists_sq_padic_odd`.) -/
@[kb "milne2020ant" "v3.08, Example 7.28, p. 118"]
theorem example_7_28 : ∃ x : ℚ_[5], x ^ 2 = -1 := by
  have h5 : ‖((5:ℕ) : ℤ_[5])‖ = 5⁻¹ := PadicInt.norm_p (p := 5)
  have h4 : ‖((4:ℕ) : ℤ_[5])‖ = 1 := by
    rw [PadicInt.norm_natCast_eq_one_iff]; norm_num
  have e1 : Polynomial.aeval (2:ℤ_[5]) (Polynomial.X ^ 2 + 1 : Polynomial ℤ) = ((5:ℕ) : ℤ_[5]) := by
    simp; norm_num
  have e2 : Polynomial.aeval (2:ℤ_[5]) (Polynomial.derivative (Polynomial.X ^ 2 + 1 : Polynomial ℤ)) =
      ((4:ℕ) : ℤ_[5]) := by
    simp [map_ofNat]; norm_num
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := (Polynomial.X ^ 2 + 1 : Polynomial ℤ)) (a := (2 : ℤ_[5])) (by
    rw [e1, e2, h5, h4]; norm_num)
  refine ⟨(z : ℚ_[5]), ?_⟩
  simp at hz
  have hz' : z ^ 2 = -1 := eq_neg_of_add_eq_zero_left hz
  have := congrArg (fun w : ℤ_[5] => (w : ℚ_[5])) hz'
  simpa using this

/-- The `p`-adic norm of `n!`. -/
private theorem norm_factorial_padic (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ‖(n.factorial : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n.factorial : ℤ)) := by
  have h : (n.factorial : ℚ_[p]) = ((n.factorial : ℚ) : ℚ_[p]) := by push_cast; rfl
  rw [h, Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast n.factorial_ne_zero),
    padicValRat.of_nat]
  push_cast
  rfl

/-- Norm of the terms of the exponential series. -/
private theorem norm_exp_term (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (n : ℕ) :
    ‖x ^ n / (n.factorial : ℚ_[p])‖ =
      (‖x‖ * (p : ℝ) ^ (1 / ((p : ℝ) - 1))) ^ n * ((p : ℝ) ^ (1 / ((p : ℝ) - 1))) ^ (-(((p.digits n).sum : ℕ) : ℝ)) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  set t : ℝ := (p : ℝ) ^ (1 / ((p : ℝ) - 1)) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hp0 _
  have key := sub_one_mul_padicValNat_factorial (p := p) n
  have hle : (p.digits n).sum ≤ n := Nat.digit_sum_le p n
  have key' : ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) = (n : ℝ) - (((p.digits n).sum : ℕ) : ℝ) := by
    have : ((p - 1 : ℕ) : ℝ) * (padicValNat p n.factorial : ℝ) = ((n - (p.digits n).sum : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) key
    rw [Nat.cast_sub hle, Nat.cast_sub (Fact.out : p.Prime).one_le] at this
    simpa using this
  have hpv : (p : ℝ) ^ (padicValNat p n.factorial : ℝ) = t ^ ((n : ℝ) - (((p.digits n).sum : ℕ) : ℝ)) := by
    rw [ht, ← Real.rpow_mul hp0.le, ← key']
    congr 1
    field_simp
  have h2 : (p : ℝ) ^ (padicValNat p n.factorial) = t ^ n * t ^ (-(((p.digits n).sum : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, hpv, sub_eq_add_neg, Real.rpow_add ht0, Real.rpow_natCast]
  rw [norm_div, norm_pow, norm_factorial_padic, zpow_neg, div_inv_eq_mul, zpow_natCast, h2, mul_pow]
  ring

private theorem digits_sum_pow (p k : ℕ) (hp : 1 < p) : (p.digits (p ^ k)).sum = 1 := by
  have := Nat.digits_base_pow_mul (b := p) (k := k) (m := 1) hp one_pos
  rw [mul_one] at this
  rw [this]
  simp [Nat.digits_of_lt p 1 one_ne_zero hp]

private theorem lt_rpow_iff (p : ℕ) [Fact p.Prime] (r : ℝ) :
    r < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) ↔ r * (p : ℝ) ^ (1 / ((p : ℝ) - 1)) < 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have ht0 : 0 < (p : ℝ) ^ (1 / ((p : ℝ) - 1)) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith), ← one_div, lt_div_iff₀ ht0]

/-- **Example 7.29**, the criterion: for $x \in \mathbb Q_p$, $x^n/n! \to 0$ iff $\operatorname{ord}_p(x) > 1/(p-1)$,
i.e. iff $|x|_p < p^{-1/(p-1)}$. Milne's proof uses Legendre's formula
$\operatorname{ord}_p(n!) = (n - \sum a_i)/(p-1)$ (Mathlib: `sub_one_mul_padicValNat_factorial`). -/
@[kb "milne2020ant" "v3.08, Example 7.29, p. 118"]
theorem example_7_29_tendsto_iff (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    Tendsto (fun n : ℕ => x ^ n / (n.factorial : ℚ_[p])) atTop (𝓝 0) ↔
      ‖x‖ < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have ht0 : 0 < (p : ℝ) ^ (1 / ((p : ℝ) - 1)) := Real.rpow_pos_of_pos (by linarith) _
  have ht1 : 1 ≤ (p : ℝ) ^ (1 / ((p : ℝ) - 1)) :=
    Real.one_le_rpow hp.le (by
      have : 0 < (p : ℝ) - 1 := by linarith
      positivity)
  rw [lt_rpow_iff, tendsto_zero_iff_norm_tendsto_zero]
  set t : ℝ := (p : ℝ) ^ (1 / ((p : ℝ) - 1)) with ht
  constructor
  · intro h
    by_contra hq
    have hq' : 1 ≤ ‖x‖ * t := not_lt.mp hq
    have hpos : 0 < t ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos ht0 _
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds hpos))
    have := hN (p ^ N) (by
      have := Nat.lt_pow_self (Fact.out : p.Prime).one_lt (n := N)
      omega)
    rw [norm_exp_term, digits_sum_pow p N (Fact.out : p.Prime).one_lt] at this
    have h1 : 1 ≤ (‖x‖ * t) ^ (p ^ N) := one_le_pow₀ hq'
    push_cast at this
    nlinarith
  · intro hq
    have hq0 : 0 ≤ ‖x‖ * t := by positivity
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq)
    rw [norm_exp_term]
    have : t ^ (-(((p.digits n).sum : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht1 (by
        have := Nat.cast_nonneg (α := ℝ) (p.digits n).sum
        linarith)
    have h0 : 0 ≤ (‖x‖ * t) ^ n := by positivity
    nlinarith

/-- **Example 7.29.** The exponential series $\exp(x) = \sum x^n/n!$ converges in $\mathbb Q_p$ for
$\operatorname{ord}_p(x) > 1/(p-1)$. -/
@[kb "milne2020ant" "v3.08, Example 7.29, p. 119"]
theorem example_7_29_summable (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : ‖x‖ < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) :
    Summable fun n : ℕ => x ^ n / (n.factorial : ℚ_[p]) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by
    rw [Nat.cofinite_eq_atTop]
    exact (example_7_29_tendsto_iff p x).mpr hx)

/-- Membership of `y - a` in a power of the maximal ideal of `Â`, in terms of norms. -/
theorem sub_mem_pow_completion_iff (π : unitBall K) (hπ : maximalIdeal (unitBall K) = Ideal.span {π})
    (y : unitBall (UniformSpace.Completion K)) (a : unitBall K) (n : ℕ) :
    y - unitBallCompletionHom K a ∈ maximalIdeal (unitBall (UniformSpace.Completion K)) ^ n ↔
      ‖(y : UniformSpace.Completion K) - ((a : K) : UniformSpace.Completion K)‖ ≤ ‖(π : K)‖ ^ n := by
  rw [mem_maximalIdeal_pow_iff _ (maximalIdeal_completion K π hπ)]
  have : ((unitBallCompletionHom K π : unitBall (UniformSpace.Completion K)) :
      UniformSpace.Completion K) = ((π : K) : UniformSpace.Completion K) := rfl
  rw [this, UniformSpace.Completion.norm_coe]
  rfl

/-- **Aside 7.30.** For the discrete valuation ring $A$ of a discrete nonarchimedean absolute value, the
$\mathfrak m$-adic completion $\varprojlim A/\mathfrak m^n$ (Mathlib's `AdicCompletion`) agrees with the completion
$\hat A$ for the absolute value: there is a ring isomorphism compatible with the maps from $A$. -/
@[kb "milne2020ant" "v3.08, Aside 7.30, p. 119"]
theorem aside_7_30 (hd : IsDiscreteAbv (NormedField.toAbsoluteValue K)) :
    ∃ e : unitBall (UniformSpace.Completion K) ≃+* AdicCompletion (maximalIdeal (unitBall K)) (unitBall K),
      ∀ a : unitBall K, e (unitBallCompletionHom K a) = algebraMap _ _ a := by
  obtain ⟨π, hπ⟩ := exists_generator K hd
  have hπlt : ‖(π : K)‖ < 1 := by
    have hπm : π ∈ maximalIdeal (unitBall K) := by
      rw [hπ]; exact Ideal.mem_span_singleton_self π
    exact (mem_maximalIdeal_unitBall_iff π).1 hπm
  let eqv : ∀ n : ℕ, (unitBall K ⧸ maximalIdeal (unitBall K) ^ n) ≃+*
      (unitBall (UniformSpace.Completion K) ⧸ maximalIdeal (unitBall (UniformSpace.Completion K)) ^ n) :=
    fun n => RingEquiv.ofBijective _ (lemma_7_25 K hd n)
  let f : ∀ n : ℕ, unitBall (UniformSpace.Completion K) →+*
      unitBall K ⧸ maximalIdeal (unitBall K) ^ n :=
    fun n => (eqv n).symm.toRingHom.comp (Ideal.Quotient.mk _)
  have hspec : ∀ n y a, y - unitBallCompletionHom K a ∈
      maximalIdeal (unitBall (UniformSpace.Completion K)) ^ n → f n y = Ideal.Quotient.mk _ a := by
    intro n y a h
    have h1 : eqv n (Ideal.Quotient.mk (maximalIdeal (unitBall K) ^ n) a) =
        Ideal.Quotient.mk (maximalIdeal (unitBall (UniformSpace.Completion K)) ^ n) y := by
      show Ideal.quotientMap (maximalIdeal (unitBall (UniformSpace.Completion K)) ^ n)
        (unitBallCompletionHom K) (pow_maximalIdeal_le_comap K n)
        (Ideal.Quotient.mk (maximalIdeal (unitBall K) ^ n) a) = _
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
      simpa using neg_mem h
    show (eqv n).symm (Ideal.Quotient.mk _ y) = _
    rw [← h1]; simp
  have happrox : ∀ n y, ∃ a : unitBall K, y - unitBallCompletionHom K a ∈
      maximalIdeal (unitBall (UniformSpace.Completion K)) ^ n := by
    intro n y
    obtain ⟨a, ha⟩ := exists_approx_pow K π hπ y n
    exact ⟨a, (sub_mem_pow_completion_iff K π hπ y a n).2 ha⟩
  have hcompat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal (unitBall K)) hle).comp (f n) = f m := by
    intro m n hle
    ext y
    obtain ⟨a, ha⟩ := happrox n y
    have ha' : y - unitBallCompletionHom K a ∈
        maximalIdeal (unitBall (UniformSpace.Completion K)) ^ m :=
      Ideal.pow_le_pow_right hle ha
    rw [RingHom.comp_apply, hspec n y a ha, hspec m y a ha']
    rfl
  let Φ := AdicCompletion.liftRingHom (maximalIdeal (unitBall K)) f hcompat
  have hΦ : ∀ n y, AdicCompletion.evalₐ (maximalIdeal (unitBall K)) n (Φ y) = f n y :=
    fun n y => AdicCompletion.evalₐ_liftRingHom _ f hcompat n y
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have hπ' := maximalIdeal_completion K π hπ
    have hn : ∀ n : ℕ, ‖(y : UniformSpace.Completion K)‖ ≤ ‖(π : K)‖ ^ n := by
      intro n
      have h1 : f n y = 0 := by
        rw [← hΦ, hy, map_zero]
      have h2 : Ideal.Quotient.mk (maximalIdeal (unitBall (UniformSpace.Completion K)) ^ n) y = 0 := by
        have : (eqv n).symm (Ideal.Quotient.mk (maximalIdeal (unitBall (UniformSpace.Completion K)) ^ n) y)
            = 0 := h1
        simpa using this
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_maximalIdeal_pow_iff _ hπ'] at h2
      have e : ‖((unitBallCompletionHom K π : unitBall (UniformSpace.Completion K)) :
          UniformSpace.Completion K)‖ = ‖(π : K)‖ := UniformSpace.Completion.norm_coe _
      rwa [e] at h2
    have h0 : ‖(y : UniformSpace.Completion K)‖ ≤ 0 :=
      ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπlt) hn
    exact Subtype.ext (norm_le_zero_iff.1 h0)
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective (maximalIdeal (unitBall K)) (unitBall K) z
    let v : ℕ → UniformSpace.Completion K := fun n => ((x.val n : unitBall K) : K)
    have hv : ∀ m n, m ≤ n → ‖v m - v n‖ ≤ ‖(π : K)‖ ^ m := by
      intro m n hmn
      have h1 := (x.property hmn)
      rw [SModEq.sub_mem] at h1
      have h2 : x.val m - x.val n ∈ maximalIdeal (unitBall K) ^ m := by
        have hh : (maximalIdeal (unitBall K) ^ m • ⊤ : Ideal (unitBall K)) =
            maximalIdeal (unitBall K) ^ m := by ext x; simp
        rwa [hh] at h1
      rw [mem_maximalIdeal_pow_iff π hπ] at h2
      have e1 : (((x.val m - x.val n : unitBall K) : K)) = (x.val m : K) - (x.val n : K) := rfl
      have : v m - v n = (((x.val m - x.val n : unitBall K) : K) : UniformSpace.Completion K) := by
        rw [e1, UniformSpace.Completion.coe_sub]
      rw [this, UniformSpace.Completion.norm_coe]
      exact h2
    have hcau : CauchySeq v := by
      refine cauchySeq_of_le_geometric (‖(π : K)‖) 1 hπlt (fun n => ?_)
      rw [dist_eq_norm, one_mul]
      exact hv n (n + 1) (Nat.le_succ n)
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcau
    have hy1 : ‖y‖ ≤ 1 := by
      refine le_of_tendsto' (hy.norm) (fun n => ?_)
      show ‖((x.val n : K) : UniformSpace.Completion K)‖ ≤ 1
      rw [UniformSpace.Completion.norm_coe]; exact (x.val n).2
    refine ⟨⟨y, hy1⟩, ?_⟩
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [hΦ, AdicCompletion.evalₐ_mk]
    apply hspec
    rw [sub_mem_pow_completion_iff K π hπ]
    show ‖y - v n‖ ≤ _
    refine le_of_tendsto (hy.sub_const (v n)).norm ?_
    rw [eventually_atTop]
    refine ⟨n, fun k hk => ?_⟩
    rw [norm_sub_rev]
    exact hv n k hk
  refine ⟨RingEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun a => ?_⟩
  apply AdicCompletion.ext_evalₐ
  intro n
  show AdicCompletion.evalₐ _ n (Φ (unitBallCompletionHom K a)) = _
  rw [hΦ, hspec n _ a (by simp), AdicCompletion.algebraMap_apply]
  simp


end NumberFieldKB.MilneANT
