import NumberFieldKB.WeilBNT.SUnits

/-!
# Weil, *Basic Number Theory*, IV.§4: the corollary of Theorem 9, and $E(P)$ as the units of $k(P)$

Notation of `SUnits.lean`. Weil puts $U=\prod_vU_v$ ($U_v=\{\lvert x\rvert_v=1\}$), $G=\Omega(P)/U$ and
$G_1=\Omega^1(P)/U$. The logarithmic map `ideleLog` identifies $G$ with its image in $\mathbb R^P$ (its kernel on
$\Omega(P)$ is $U$), so here $G_1$ is the subgroup `omegaOneLog K S` of $\mathbb R^P$, the image of $\Omega^1(P)$.

* **`mem_omegaOneLog_iff`**: $G_1=\{y:\sum_vy_v=0,\ y_v\in\mathbb Z\log N(v)\ (v\in S)\}$; in particular $G_1$ is
  closed (`isClosed_omegaOneLog`);
* **`weil_IV_4_thm9_cor`** (Weil, Cor. of Thm. 9, p. 79): the image $\Gamma$ of $E(P)$ lies in $G_1$, is discrete, and
  $G_1/\Gamma$ is compact;
* **`weil_IV_4_EP_units`** (Weil, p. 77–78): $E(P)$ is the group of units of the ring
  $k(P)=\{e\in k:\lvert e\rvert_v\le1\ (v\notin P)\}$.
-/

open IsDedekindDomain NumberField Filter Topology
open NumberFieldKB.Ideles QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K] {S : Finset (HeightOneSpectrum (𝓞 K))}

/-- $\log\lvert z\rvert_v=\mathrm{ord}\cdot\log N(v)$ for a nonzero $z\in k_v$ ($v$ finite). -/
theorem log_norm_adicCompletion (v : HeightOneSpectrum (𝓞 K)) {z : v.adicCompletion K} (hz : z ≠ 0) :
    Real.log ‖z‖ = ((WithZero.log (Valued.v z) : ℤ) : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply
    (NumberField.HeightOneSpectrum.absNorm_ne_zero v) ((Valuation.ne_zero_iff _).mpr hz)]
  push_cast
  rw [Real.log_zpow]

variable (K S) in
/-- Weil's $G_1=\Omega^1(P)/U$, realized as the image of $\Omega^1(P)=\Omega(P)\cap k^1$ under `ideleLog`. -/
def omegaOneLog : AddSubgroup (PlP K S → ℝ) where
  carrier := {y | ∃ x ∈ omega K (S : Set (HeightOneSpectrum (𝓞 K))), x ∈ ideleGroupOne K ∧ ideleLog S x = y}
  add_mem' := by
    rintro _ _ ⟨x, hx, hx1, rfl⟩ ⟨y, hy, hy1, rfl⟩
    exact ⟨x * y, mul_mem hx hy, mul_mem hx1 hy1, ideleLog_mul x y⟩
  zero_mem' := ⟨1, one_mem _, one_mem _, by
    have h := ideleLog_mul (S := S) (1 : IdeleGroup (𝓞 K) K) 1
    rw [mul_one] at h
    exact (add_eq_left.mp h.symm)⟩
  neg_mem' := by
    rintro _ ⟨x, hx, hx1, rfl⟩
    exact ⟨x⁻¹, inv_mem hx, inv_mem hx1, ideleLog_inv x⟩

/-- **Description of $G_1$**: $y\in G_1$ iff $\sum_{v\in P}y_v=0$ and $y_v\in\mathbb Z\log N(v)$ for $v\in S$. -/
theorem mem_omegaOneLog_iff {y : PlP K S → ℝ} :
    y ∈ omegaOneLog K S ↔ ∑ i, y i = 0 ∧
      ∀ v : S, ∃ k : ℤ, y (.inr v) = k * Real.log (Ideal.absNorm v.1.asIdeal) := by
  classical
  constructor
  · rintro ⟨x, hxΩ, hx1, rfl⟩
    refine ⟨?_, fun v => ⟨WithZero.log (Valued.v ((x : AdeleRing (𝓞 K) K).2 v.1)), ?_⟩⟩
    · rw [← log_ideleGroupNorm_eq_sum hxΩ]
      have h1 : (ideleGroupNorm K x : ℝ) = 1 := by
        have : ideleGroupNorm K x = 1 := hx1
        exact_mod_cast this
      rw [h1, Real.log_one]
    · exact log_norm_adicCompletion v.1 (idele_fin_ne_zero x v.1)
  · rintro ⟨hy, hk⟩
    choose k hk using hk
    choose π hπ using fun v : HeightOneSpectrum (𝓞 K) => v.valuation_exists_uniformizer K
    have hπ0 : ∀ v, (π v : v.adicCompletion K) ≠ 0 := fun v h => by
      have h' := congrArg Valued.v h
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ v, map_zero] at h'
      exact WithZero.exp_ne_zero h'
    let b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K := fun v =>
      if hv : v ∈ S then (π v : v.adicCompletion K) ^ (-k ⟨v, hv⟩) else 1
    have hb0 : ∀ v, b v ≠ 0 := fun v => by
      by_cases hv : v ∈ S
      · simp only [b, hv, ↓reduceDIte]; exact zpow_ne_zero _ (hπ0 v)
      · simp only [b, hv, ↓reduceDIte]; exact one_ne_zero
    have hbS : ∀ v, v ∉ S → b v = 1 := fun v hv => by simp only [b, hv, ↓reduceDIte]
    choose a ha0 ha using fun w : InfinitePlace K =>
      exists_norm_completion' w (Real.exp (y (.inl w))) (Real.exp_pos _)
    set x := mkIdele S a b ha0 hb0 hbS
    have hxΩ := mkIdele_mem_omega (S := S) a b ha0 hb0 hbS
    have hlog : ideleLog S x = y := by
      funext i
      rcases i with w | v
      · change (w.mult : ℝ) * Real.log ‖a w‖ = y (.inl w)
        rw [← Real.log_pow, ha w, Real.log_exp]
      · change Real.log ‖b v.1‖ = y (.inr v)
        simp only [b, v.2, ↓reduceDIte, norm_zpow, Real.log_zpow, norm_uniformizer v.1 (hπ v.1), hk v]
        push_cast
        ring
    refine ⟨x, hxΩ, ?_, hlog⟩
    have hl := log_ideleGroupNorm_eq_sum hxΩ
    rw [hlog, hy] at hl
    show ideleGroupNorm K x = 1
    have hpos : (0 : ℝ) < ideleGroupNorm K x := by exact_mod_cast ideleGroupNorm_pos x
    rcases Real.log_eq_zero.mp hl with h | h | h
    · exact absurd h hpos.ne'
    · exact_mod_cast h
    · linarith

/-- $G_1$ is closed in $\mathbb R^P$. -/
theorem isClosed_omegaOneLog : IsClosed (omegaOneLog K S : Set (PlP K S → ℝ)) := by
  have hset : (omegaOneLog K S : Set (PlP K S → ℝ)) =
      {y | ∑ i, y i = 0} ∩ ⋂ v : S, (fun y : PlP K S → ℝ => y (.inr v)) ⁻¹'
        (AddSubgroup.zmultiples (Real.log (Ideal.absNorm v.1.asIdeal)) : Set ℝ) := by
    ext y
    simp only [SetLike.mem_coe, mem_omegaOneLog_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter,
      Set.mem_preimage, AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]
    exact and_congr Iff.rfl (forall_congr' fun v => ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩)
  rw [hset]
  refine IsClosed.inter (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
    (isClosed_iInter fun v => ?_)
  exact (AddSubgroup.isClosed_of_discreteTopology).preimage (continuous_apply _)

/-- $\Gamma\subseteq G_1$. -/
theorem gammaLattice_le_omegaOneLog : (gammaLattice K S).toAddSubgroup ≤ omegaOneLog K S := by
  rintro _ ⟨η, hη, rfl⟩
  refine mem_omegaOneLog_iff.mpr ⟨sum_logEmb_eq_zero hη, fun v => ⟨WithZero.log (v.1.valuation K (η : K)), ?_⟩⟩
  have h := log_norm_adicCompletion v.1 (z := ((η : K) : v.1.adicCompletion K)) (fun h0 => by
    have h' := congrArg Valued.v h0
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_zero] at h'
    exact (Valuation.ne_zero_iff _).mpr η.ne_zero h')
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  change Real.log (FinitePlace.mk v.1 (η : K)) = _
  rw [FinitePlace.mk_apply]
  exact h

/-- **Weil, IV.§4, Corollary of Theorem 9** (p. 79), number field case: in $G_1=\Omega^1(P)/U$ (realized in
$\mathbb R^P$ by the logarithms, `omegaOneLog`), the image $\Gamma$ of $E(P)$ is discrete and $G_1/\Gamma$ is compact.
$G_1$ is closed, and a compact $C\subseteq G_1$ has $G_1=C+\Gamma$. -/
@[kb "weil1973bnt" "Ch. IV, §4, Cor. of Thm. 9 (p. 79), number field case"]
theorem weil_IV_4_thm9_cor :
    IsClosed (omegaOneLog K S : Set (PlP K S → ℝ)) ∧
      (gammaLattice K S : Set (PlP K S → ℝ)) ⊆ omegaOneLog K S ∧
      DiscreteTopology (gammaLattice K S) ∧
      ∃ C : Set (PlP K S → ℝ), IsCompact C ∧ C ⊆ omegaOneLog K S ∧
        ∀ g ∈ omegaOneLog K S, ∃ c ∈ C, ∃ γ ∈ gammaLattice K S, g = c + γ := by
  obtain ⟨R, hR⟩ := exists_sUnit_near_hyperplane (K := K) (S := S)
  refine ⟨isClosed_omegaOneLog, fun γ hγ => gammaLattice_le_omegaOneLog hγ, inferInstance,
    (omegaOneLog K S : Set _) ∩ Metric.closedBall 0 (max R 0),
    (isCompact_closedBall _ _).inter_left isClosed_omegaOneLog, Set.inter_subset_left, fun g hg => ?_⟩
  obtain ⟨η, hη, hηg⟩ := hR g (mem_omegaOneLog_iff.mp hg).1
  have hγ := logEmb_mem_gammaLattice hη
  refine ⟨g - logEmb K S (η : K), ⟨sub_mem hg (gammaLattice_le_omegaOneLog hγ), ?_⟩, _, hγ, by abel⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (le_max_right R 0)).mpr fun i =>
    (Real.norm_eq_abs _ ▸ (hηg i).trans (le_max_left R 0))

/-- The quotient form of the corollary: $G_1/\Gamma$ is a compact space. -/
theorem compactSpace_omegaOneLog_quot :
    CompactSpace (omegaOneLog K S ⧸ (gammaLattice K S).toAddSubgroup.addSubgroupOf (omegaOneLog K S)) := by
  obtain ⟨-, -, -, C, hC, hCG, hcov⟩ := weil_IV_4_thm9_cor (K := K) (S := S)
  set G := omegaOneLog K S
  have hC' : IsCompact (Subtype.val ⁻¹' C : Set G) := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    have himC : Subtype.val '' (Subtype.val ⁻¹' C : Set G) = C := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, hCG hx⟩, hx, rfl⟩
    rw [himC]
    exact hC
  refine ⟨?_⟩
  have himg := hC'.image (QuotientAddGroup.continuous_mk (N :=
    (gammaLattice K S).toAddSubgroup.addSubgroupOf G))
  convert himg
  symm
  refine Set.eq_univ_of_forall fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨c, hc, γ, hγ, hg⟩ := hcov g g.2
  have hcG : c ∈ G := hCG hc
  refine ⟨⟨c, hcG⟩, hc, ?_⟩
  rw [QuotientAddGroup.eq]
  rw [AddSubgroup.mem_addSubgroupOf]
  have : (-(⟨c, hcG⟩ : G) + g : G) = (γ : PlP K S → ℝ) := by
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, hg]
    abel
  rw [this]
  exact hγ

/-! ### $E(P)$ is the group of units of $k(P)$ (Weil, p. 77–78) -/

variable (K S) in
/-- Weil's ring $k(P)=\{e\in k:\lvert e\rvert_v\le1\ \text{for } v\notin P\}$, $P=P_\infty\cup S$. -/
def ringKP : Subring K where
  carrier := {e | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v.valuation K e ≤ 1}
  mul_mem' {a b} ha hb v hv := by
    rw [map_mul]; exact mul_le_one' (ha v hv) (hb v hv)
  one_mem' v _ := by simp
  add_mem' {a b} ha hb v hv := (Valuation.map_add _ a b).trans (max_le (ha v hv) (hb v hv))
  zero_mem' v _ := by simp
  neg_mem' {a} ha v hv := by rw [Valuation.map_neg]; exact ha v hv

/-- **Weil, p. 77–78**: $E(P)$ consists of the units of $k(P)$: $e\in E(P)$ iff $e$ and $e^{-1}$ lie in $k(P)$. -/
@[kb "weil1973bnt" "Ch. IV, §4, text p. 77-78 ($E(P)$ is the unit group of $k(P)$), number field case"]
theorem weil_IV_4_EP_units (e : Kˣ) :
    e ∈ sUnits K S ↔ (e : K) ∈ ringKP K S ∧ ((e⁻¹ : Kˣ) : K) ∈ ringKP K S := by
  constructor
  · intro he
    refine ⟨fun v hv => (he v hv).le, fun v hv => ?_⟩
    rw [Units.val_inv_eq_inv_val, map_inv₀, he v hv, inv_one]
  · rintro ⟨h1, h2⟩ v hv
    have a := h1 v hv
    have b := h2 v hv
    rw [Units.val_inv_eq_inv_val, map_inv₀] at b
    have hne : v.valuation K (e : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr e.ne_zero
    exact le_antisymm a (by
      by_contra hlt
      push Not at hlt
      have := one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hne, hlt⟩
      exact absurd b (not_le.mpr this))

end NumberFieldKB.WeilBNT

end
