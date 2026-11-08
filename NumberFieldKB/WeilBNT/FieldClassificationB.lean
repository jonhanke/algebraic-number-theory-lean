import NumberFieldKB.WeilBNT.FieldClassification
import NumberFieldKB.WeilBNT.FieldVectorSpaces
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Weil, *Basic Number Theory*, I.§3, Thm. 5 (b) and its Corollary

$K$ is a nondiscrete locally compact division ring of characteristic $0$ (`FieldModule`).

* **`weil_I_3_thm5_b`**: Thm. 5 (b). $K$ is a division algebra of finite dimension $\delta$ over a field $\mathbb Q_v$
  ($v$ a prime $p$, $\mathbb Q_v=\mathbb Q_p$, or $v=\infty$, $\mathbb Q_v=\mathbb R$): there is a continuous ring
  homomorphism $f:\mathbb Q_v\to K$ with central image and a basis $b_1,\dots,b_\delta$ of $K$ over $f(\mathbb Q_v)$, and
  (Corollary) $\operatorname{mod}_K(f(x))=\lvert x\rvert_v^{\delta}$ for $x\in\mathbb Q_v$.

Finite dimension over $f(\mathbb Q_v)$ is expressed without an algebra instance: $(c_i)\mapsto\sum_if(c_i)b_i$ is a
bijection $\mathbb Q_v^\delta\to K$.

*Proof* (Weil's). By Thm. 5 (description of $F$, `weil_I_3_thm5_charZero`) $\operatorname{mod}_K$ induces
$x\mapsto\lvert x\rvert_v^\lambda$ on $\mathbb Q$, so by Cor. 1 of I.§2 Prop. 2 the topology induced on $\mathbb Q$ is the
$v$-adic one; $K$ is complete, so the inclusion of $\mathbb Q$ extends to $\mathbb Q_v$ (the closure of $\mathbb Q$),
which is central. $K$ is a locally compact vector space over $\mathbb Q_v$, finite-dimensional by I.§2 Cor. 2 of Thm. 3,
and $\operatorname{mod}_K=\operatorname{mod}_{\mathbb Q_v}^\delta$ there.
-/

open Topology Filter MeasureTheory
open scoped NNReal ENNReal Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot]

/-- The module of the real numbers is the absolute value. -/
theorem modK_real (x : ℝ) : (modK ℝ x : ℝ) = |x| := by
  by_cases hx : x = 0
  · simp [hx]
  have h := modK_mul_measure (volume : Measure ℝ) hx (Set.Icc (0 : ℝ) 1)
  rw [Measure.addHaar_smul] at h
  simp only [Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one, pow_one,
    Module.finrank_self] at h
  have h2 : ((modK ℝ x : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal |x| := by simpa using h
  have := congrArg ENNReal.toReal h2
  simpa [ENNReal.toReal_ofReal (abs_nonneg x)] using this

/-- In `ℚ_[p]` the module of `p` is `p⁻¹`: the unit ball is the disjoint union of `p` translates of
`p` times the unit ball. -/
theorem modK_padic_p (p : ℕ) [Fact p.Prime] : modK ℚ_[p] (p : ℚ_[p]) = (p : ℝ≥0)⁻¹ := by
  borelize ℚ_[p]
  let μ : Measure ℚ_[p] := Measure.addHaar
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  let B : Set ℚ_[p] := Metric.closedBall 0 1
  let C : ℕ → Set ℚ_[p] := fun i => Metric.closedBall (i : ℚ_[p]) (p : ℝ)⁻¹
  have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsm : (p : ℚ_[p]) • B = C 0 := by
    simp only [B, C]
    rw [smul_closedBall _ _ zero_le_one]
    simp [Padic.norm_p]
  have hCtr : ∀ i : ℕ, μ (C i) = μ (C 0) := by
    intro i
    have : C i = (fun x => -(i : ℚ_[p]) + x) ⁻¹' (C 0) := by
      ext x
      simp [C, dist_eq_norm, add_comm, sub_eq_add_neg]
    rw [this]
    exact measure_preimage_add μ _ _
  have hcov : B = ⋃ i ∈ Finset.range p, C i := by
    ext x
    simp only [B, C, Set.mem_iUnion, Finset.mem_range, Metric.mem_closedBall,
      dist_eq_norm, sub_zero, exists_prop]
    constructor
    · intro hx
      obtain ⟨z, hz⟩ : ∃ z : ℤ_[p], (z : ℚ_[p]) = x := ⟨⟨x, hx⟩, rfl⟩
      obtain ⟨n, hn, hmem⟩ := PadicInt.exists_mem_range z
      refine ⟨n, hn, ?_⟩
      simp only [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
        ← PadicInt.norm_lt_one_iff_dvd] at hmem
      have h1 : ‖x - (n : ℚ_[p])‖ < 1 := by
        rw [PadicInt.norm_def] at hmem
        rw [PadicInt.coe_sub, PadicInt.coe_natCast, hz] at hmem
        exact hmem
      have := (Padic.norm_le_pow_iff_norm_lt_pow_add_one (x - (n : ℚ_[p])) (-1)).2 (by simpa using h1)
      simpa using this
    · rintro ⟨n, hn, h⟩
      have h1 : ‖(n : ℚ_[p])‖ ≤ 1 := by
        simpa using Padic.norm_int_le_one (p := p) (n : ℤ)
      have h2 : ‖x - n‖ ≤ 1 := h.trans (inv_le_one_of_one_le₀ hp1.le)
      calc ‖x‖ = ‖(x - n) + n‖ := by ring_nf
        _ ≤ max ‖x - n‖ ‖(n : ℚ_[p])‖ := Padic.nonarchimedean _ _
        _ ≤ 1 := max_le h2 h1
  have hdisj : (↑(Finset.range p) : Set ℕ).PairwiseDisjoint C := by
    intro i hi j hj hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hxi hxj
    simp only [C, Metric.mem_closedBall, dist_eq_norm] at hxi hxj
    have h3 : ‖((((i : ℤ) - j : ℤ)) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
      calc ‖((((i : ℤ) - j : ℤ)) : ℚ_[p])‖ = ‖(x - j) - (x - i)‖ :=
            congrArg norm (by push_cast; ring)
        _ ≤ max ‖x - j‖ ‖x - i‖ := by
          rw [sub_eq_add_neg]
          refine (Padic.nonarchimedean _ _).trans ?_
          rw [norm_neg]
        _ ≤ _ := max_le hxj hxi
    have h4 : ‖((((i : ℤ) - j : ℤ)) : ℚ_[p])‖ < 1 := h3.trans_lt (inv_lt_one_of_one_lt₀ hp1)
    rw [Padic.norm_intCast_lt_one_iff] at h4
    have hi' : i < p := Finset.mem_range.1 hi
    have hj' : j < p := Finset.mem_range.1 hj
    apply hij
    have := (Int.modEq_iff_dvd.2 h4)
    have h5 : (j : ℤ) ≡ i [ZMOD p] := this
    have h6 : j ≡ i [MOD p] := by exact_mod_cast h5
    rw [Nat.ModEq, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at h6
    exact h6.symm
  have hmeasure : μ B = p * μ (C 0) := by
    rw [hcov, measure_biUnion_finset hdisj (fun i _ => measurableSet_closedBall)]
    simp [hCtr]
  have hBpos : μ B ≠ 0 := (Measure.measure_pos_of_mem_nhds μ
    (Metric.closedBall_mem_nhds (0 : ℚ_[p]) one_pos)).ne'
  have hBtop : μ B ≠ ⊤ := (isCompact_closedBall (0 : ℚ_[p]) 1).measure_lt_top.ne
  have key := modK_mul_measure μ hpne B
  rw [hsm] at key
  have h7 : μ B = (p : ℝ≥0∞) * (modK ℚ_[p] (p : ℚ_[p]) : ℝ≥0∞) * μ B := by
    rw [mul_assoc, key]; exact hmeasure
  have h8 : (p : ℝ≥0∞) * (modK ℚ_[p] (p : ℚ_[p]) : ℝ≥0∞) = 1 := by
    refine (ENNReal.mul_eq_right hBpos hBtop).1 ?_
    nth_rewrite 2 [h7]; rfl
  rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul, ENNReal.coe_eq_one] at h8
  exact eq_inv_of_mul_eq_one_right h8

/-- If the module on the natural numbers is `‖m‖ ^ l`, the same holds on the rational numbers. -/
theorem modK_ratCast_eq [CharZero K] {Q : Type*} [NormedField Q] [CharZero Q] {l : ℝ}
    (hnat : ∀ m : ℕ, (modK K (m : K) : ℝ) = ‖(m : Q)‖ ^ l) (q : ℚ) :
    (modK K (q : K) : ℝ) = ‖(q : Q)‖ ^ l := by
  have hden : ((q.den : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  have hn : ∀ z : ℤ, (modK K (z.natAbs : K) : ℝ) = ‖(z : Q)‖ ^ l := by
    intro z
    have : ‖((z.natAbs : ℕ) : Q)‖ = ‖(z : Q)‖ := by
      obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z <;> simp
    rw [hnat, this]
  rw [Rat.cast_def, Rat.cast_def, div_eq_mul_inv, div_eq_mul_inv, modK_intCast_mul, modK_inv hden,
    NNReal.coe_mul, NNReal.coe_inv, hn, hnat, norm_mul, norm_inv, Real.mul_rpow (norm_nonneg _)
    (inv_nonneg.2 (norm_nonneg _)), Real.inv_rpow (norm_nonneg _)]

/-- Weil's argument: the inclusion of the rational numbers in `K` extends to a continuous ring
homomorphism from a normed field `Q` in which the rational numbers are dense, provided the module
of `K` induces a power of the norm on the rational numbers. -/
theorem exists_continuous_ringHom_of_modK [CharZero K] {Q : Type*} [NormedField Q] [CharZero Q]
    (hdense : DenseRange ((↑) : ℚ → Q)) {l : ℝ} (hl : 0 < l)
    (hq : ∀ q : ℚ, (modK K (q : K) : ℝ) = ‖(q : Q)‖ ^ l) :
    ∃ f : Q →+* K, Continuous f ∧ (∀ q : ℚ, f q = q) ∧ ∀ x y, f x * y = y * f x := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace K := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace K
  letI uQ : UniformSpace ℚ := UniformSpace.comap (Rat.castHom Q) inferInstance
  have ue : IsUniformInducing (Rat.castHom Q) := ⟨rfl⟩
  have dr : DenseRange (Rat.castHom Q) := hdense
  haveI : IsUniformAddGroup ℚ := IsUniformAddGroup.comap (Rat.castHom Q)
  have hg : UniformContinuous (Rat.castHom K) := by
    apply uniformContinuous_of_continuousAt_zero (Rat.castHom K).toAddMonoidHom
    suffices h : Tendsto (Rat.castHom K) (𝓝 0) (𝓝 0) by simpa [ContinuousAt] using h
    rw [hasBasis_nhds_zero_modK.tendsto_right_iff]
    intro m hm
    have h1 : Tendsto (fun x : Q => ‖x‖ ^ l) (𝓝 0) (𝓝 0) := by
      have h := ((Real.continuous_rpow_const hl.le).tendsto (‖(0 : Q)‖)).comp
        (continuous_norm.tendsto (0 : Q))
      simpa [Function.comp_def, Real.zero_rpow hl.ne'] using h
    have h2 : ∀ᶠ x in 𝓝 (0 : Q), ‖x‖ ^ l < m := h1.eventually (gt_mem_nhds (by exact_mod_cast hm))
    have h3 : ∀ᶠ q in 𝓝 (0 : ℚ), ‖((Rat.castHom Q) q)‖ ^ l < m := by
      rw [nhds_induced, map_zero]
      exact Filter.Eventually.comap (by simpa using h2) _
    filter_upwards [h3] with q hq3
    show modK K (q : K) ≤ m
    rw [← NNReal.coe_le_coe, hq q]
    exact_mod_cast hq3.le
  have hc : Continuous (IsDenseInducing.extendRingHom ue dr hg) :=
    (uniformContinuous_uniformly_extend ue dr hg).continuous
  have hext : ∀ q : ℚ, IsDenseInducing.extendRingHom ue dr hg (q : Q) = (q : K) := fun q =>
    (ue.isDenseInducing dr).extend_eq hg.continuous q
  refine ⟨IsDenseInducing.extendRingHom ue dr hg, hc, hext, fun x y => ?_⟩
  refine dr.induction_on x (isClosed_eq (hc.mul continuous_const) (continuous_const.mul hc)) ?_
  intro q
  have : (Rat.castHom Q q) = (q : Q) := rfl
  rw [this, hext]
  exact (Rat.cast_commute q y).eq

/-- The module of `ℚ_[p]` is the `p`-adic norm. -/
theorem modK_padic (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) : (modK ℚ_[p] x : ℝ) = ‖x‖ := by
  have hp := modK_padic_p p
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hnat : ∀ m : ℕ, (modK ℚ_[p] (m : ℚ_[p]) : ℝ) = ‖(m : ℚ_[p])‖ ^ (1 : ℝ) := by
    rcases weil_I_3_thm5_charZero (K := ℚ_[p]) with ⟨p', hp', l, hl, h⟩ | ⟨l, hl, h⟩
    · haveI : Fact p'.Prime := ⟨hp'⟩
      have h1 : (p : ℝ)⁻¹ = (padicNorm p' (p : ℕ) : ℝ) ^ l := by
        have := congrArg NNReal.toReal (h p)
        rw [hp] at this
        have h' : (((p : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) = (padicNorm p' (p : ℕ) : ℝ) ^ l := this
        simpa using h'
      have hpp : p' = p := by
        by_contra hne
        rw [padicNorm.padicNorm_of_prime_of_ne hne] at h1
        simp only [Rat.cast_one, Real.one_rpow] at h1
        have : (1 : ℝ) < (p : ℝ)⁻¹ ⁻¹ := by rwa [inv_inv]
        linarith [inv_lt_one_of_one_lt₀ hp1, h1.symm ▸ (le_refl (1 : ℝ))]
      rw [hpp] at h1 h
      have hl1 : l = 1 := by
        rw [padicNorm.padicNorm_p_of_prime] at h1
        have h2 : ((p : ℝ)⁻¹) ^ l = (p : ℝ)⁻¹ := by simpa using h1.symm
        have h3 := congrArg Real.log h2
        rw [Real.log_rpow (by positivity)] at h3
        have h4 : Real.log (p : ℝ)⁻¹ ≠ 0 :=
          Real.log_ne_zero_of_pos_of_ne_one (by positivity) (inv_lt_one_of_one_lt₀ hp1).ne
        have : l * Real.log (p : ℝ)⁻¹ = 1 * Real.log (p : ℝ)⁻¹ := by rw [one_mul]; exact h3
        exact mul_right_cancel₀ h4 this
      subst hl1
      intro m
      have := congrArg NNReal.toReal (h m)
      rw [this]
      have h5 : ‖(m : ℚ_[p])‖ = padicNorm p m := by
        simpa using Padic.eq_padicNorm (p := p) (m : ℚ)
      rw [h5]
      rfl
    · exfalso
      have h1 := congrArg NNReal.toReal (h p)
      rw [hp] at h1
      have h2 : (1 : ℝ) ≤ (p : ℝ) ^ l := Real.one_le_rpow hp1.le hl.le
      have h3 : ((p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
      simp at h1
      linarith
  have hq := modK_ratCast_eq (K := ℚ_[p]) (Q := ℚ_[p]) hnat
  simp only [Real.rpow_one] at hq
  refine (Padic.denseRange_ratCast (p := p)).induction_on x
    (isClosed_eq (NNReal.continuous_coe.comp continuous_modK) continuous_norm) ?_
  intro q
  exact hq q

/-- `K` is a finite-dimensional vector space over `Q` via a continuous ring homomorphism `f`, and
the module of `K` on `f x` is the `δ`-th power of the module of `Q` (Cor. 2 of Thm. 3 of I.§2). -/
theorem exists_basis_of_ringHom {Q : Type*} [NontriviallyNormedField Q] [LocallyCompactSpace Q]
    (hmodQ : ∀ x : Q, (modK Q x : ℝ) = ‖x‖) (f : Q →+* K) (hf : Continuous f) :
    ∃ (δ : ℕ) (b : Fin δ → K), Function.Bijective (fun c : Fin δ → Q => ∑ i, f (c i) * b i) ∧
      ∀ x : Q, (modK K (f x) : ℝ) = ‖x‖ ^ δ := by
  letI : Module Q K := Module.compHom K f
  have hsmul : ∀ (c : Q) (x : K), c • x = f c * x := fun _ _ => rfl
  haveI : ContinuousSMul Q K :=
    ⟨by simp_rw [hsmul]; exact (hf.comp continuous_fst).mul continuous_snd⟩
  haveI : FiniteDimensional Q K := weil_I_2_thm3_cor2_finiteDimensional (K := Q) (V := K)
  haveI : Nontrivial K := inferInstance
  refine ⟨Module.finrank Q K, Module.finBasis Q K, ?_, ?_⟩
  · have := (Module.finBasis Q K).equivFun.symm.bijective
    convert this using 2
    simp [Module.Basis.equivFun_symm_apply, hsmul]
  · intro x
    by_cases hx : x = 0
    · subst hx
      have hpos : 0 < Module.finrank Q K := Module.finrank_pos
      simp [zero_pow hpos.ne']
    · set a : Qˣ := Units.mk0 x hx
      have hmod := weil_I_2_thm3_cor2_mod (K := Q) (V := K) a
      have hcompat : distribHaarChar K a = modK K (f x) := by
        borelize K
        obtain ⟨X, hXc, hX0⟩ := exists_compact_mem_nhds (0 : K)
        let μ : Measure K := Measure.addHaar
        have hXpos : μ X ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hX0).ne'
        have hXtop : μ X ≠ ⊤ := hXc.measure_lt_top.ne
        have hfx : f x ≠ 0 := by simpa using hx
        have h1 := distribHaarChar_mul μ a X
        have h2 := modK_mul_measure μ hfx X
        have h3 : a • X = (f x) • X := by
          ext y
          simp [Set.mem_smul_set, Units.smul_def, hsmul, a]
        rw [h3, ← h2] at h1
        have := (ENNReal.mul_left_inj hXpos hXtop).1 h1
        exact_mod_cast this
      have : modK K (f x) = modK Q x ^ Module.finrank Q K := by rw [← hcompat, hmod]; rfl
      rw [this, NNReal.coe_pow, hmodQ]

@[kb "weil1973bnt" "Ch. I, §3, Thm. 5 (b) and its Corollary"]
theorem weil_I_3_thm5_b [CharZero K] :
    (∃ (p : ℕ) (_ : Fact p.Prime) (f : ℚ_[p] →+* K) (δ : ℕ) (b : Fin δ → K),
      Continuous f ∧ (∀ x y, f x * y = y * f x) ∧
      Function.Bijective (fun c : Fin δ → ℚ_[p] => ∑ i, f (c i) * b i) ∧
      ∀ x : ℚ_[p], (modK K (f x) : ℝ) = ‖x‖ ^ δ) ∨
    (∃ (f : ℝ →+* K) (δ : ℕ) (b : Fin δ → K),
      Continuous f ∧ (∀ x y, f x * y = y * f x) ∧
      Function.Bijective (fun c : Fin δ → ℝ => ∑ i, f (c i) * b i) ∧
      ∀ x : ℝ, (modK K (f x) : ℝ) = |x| ^ δ) := by
  rcases weil_I_3_thm5_charZero (K := K) with ⟨p, hp, l, hl, h⟩ | ⟨l, hl, h⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    have hnat : ∀ m : ℕ, (modK K (m : K) : ℝ) = ‖(m : ℚ_[p])‖ ^ l := by
      intro m
      have h5 : ‖(m : ℚ_[p])‖ = padicNorm p m := by
        simpa using Padic.eq_padicNorm (p := p) (m : ℚ)
      rw [h5]
      exact congrArg NNReal.toReal (h m)
    obtain ⟨f, hfc, -, hcomm⟩ := exists_continuous_ringHom_of_modK
      (Padic.denseRange_ratCast (p := p)) hl (modK_ratCast_eq hnat)
    obtain ⟨δ, b, hb, hmod⟩ := exists_basis_of_ringHom (modK_padic p) f hfc
    exact Or.inl ⟨p, ⟨hp⟩, f, δ, b, hfc, hcomm, hb, hmod⟩
  · have hnat : ∀ m : ℕ, (modK K (m : K) : ℝ) = ‖(m : ℝ)‖ ^ l := by
      intro m
      rw [h m]
      simp
    obtain ⟨f, hfc, -, hcomm⟩ := exists_continuous_ringHom_of_modK
      Rat.denseRange_cast hl (modK_ratCast_eq hnat)
    obtain ⟨δ, b, hb, hmod⟩ := exists_basis_of_ringHom (fun x => by rw [modK_real, Real.norm_eq_abs]) f hfc
    exact Or.inr ⟨f, δ, b, hfc, hcomm, hb, fun x => by rw [hmod, Real.norm_eq_abs]⟩


end NumberFieldKB.WeilBNT.FieldModule
