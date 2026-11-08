import NumberFieldKB.WeilBNT.SUnitsLog
import NumberFieldKB.WeilBNT.IdeleClassFiniteness

/-!
# Weil, *Basic Number Theory*, IV.§4, Theorem 9: the $P$-unit theorem

Second half of Weil's proof (p. 78–79). Notation of `SUnitsLog.lean`: $E(P)$ = `sUnits K S`, the logarithmic embedding
`logEmb K S`, $\Gamma$ its image, $G_1$ the hyperplane $\sum_{v\in P}y_v=0$ of $\mathbb R^P$.

Weil: $\Omega^1(P)/E(P)$ is isomorphic to an open subgroup of the compact group $k^1/k^\times$, hence compact; the log map
sends $\Omega^1(P)$ onto a cocompact subgroup of $G_1$; so $\Gamma$ is discrete and cocompact in $G_1$, and Lemma 5 gives
$\Gamma\cong\mathbb Z^{s}$, $s=\lvert P\rvert-1$. Here:

* **`ideleLog`**: $x\mapsto(\log\lvert x_v\rvert_v)_{v\in P}$ on ideles, continuous in each coordinate, multiplicative,
  equal to `logEmb` on principal ideles;
* **`exists_sUnit_near`** (the compactness of $\Omega^1(P)/E(P)$, in the form used): there is $R$ such that every
  $x\in\Omega^1(P)$ has $\lvert\log\lvert x_v\rvert_v-\log\lvert\eta\rvert_v\rvert\le R$ ($v\in P$) for some
  $\eta\in E(P)$;
* **`exists_sUnit_near_hyperplane`**: every point of $G_1$ is within a fixed distance of $\Gamma$.
-/

open IsDedekindDomain NumberField Filter Topology
open NumberFieldKB.Ideles QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K] {S : Finset (HeightOneSpectrum (𝓞 K))}

/-! ### The logarithmic map on ideles -/

theorem idele_inf_ne_zero (x : IdeleGroup (𝓞 K) K) (w : InfinitePlace K) :
    (x : AdeleRing (𝓞 K) K).1 w ≠ 0 := by
  intro h
  have h1 : ((x : AdeleRing (𝓞 K) K) * ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)).1 w = 1 := by
    rw [Units.mul_inv]; rfl
  have h2 : ((x : AdeleRing (𝓞 K) K) * ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)).1 w =
      (x : AdeleRing (𝓞 K) K).1 w * ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).1 w := rfl
  rw [h2, h, zero_mul] at h1
  exact zero_ne_one h1

theorem idele_fin_ne_zero (x : IdeleGroup (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    (x : AdeleRing (𝓞 K) K).2 v ≠ 0 := by
  intro h
  have h1 : ((x : AdeleRing (𝓞 K) K) * ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)).2 v = 1 := by
    rw [Units.mul_inv]; rfl
  have h2 : ((x : AdeleRing (𝓞 K) K) * ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)).2 v =
      (x : AdeleRing (𝓞 K) K).2 v * ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 v := rfl
  rw [h2, h, zero_mul] at h1
  exact zero_ne_one h1

variable (S) in
/-- The logarithms of the absolute values of an idele at the places of $P$ (Weil's normalization). -/
def ideleLog (x : IdeleGroup (𝓞 K) K) : PlP K S → ℝ
  | .inl w => w.mult * Real.log ‖(x : AdeleRing (𝓞 K) K).1 w‖
  | .inr v => Real.log ‖(x : AdeleRing (𝓞 K) K).2 v.1‖

theorem ideleLog_mul (x y : IdeleGroup (𝓞 K) K) : ideleLog S (x * y) = ideleLog S x + ideleLog S y := by
  funext i
  rcases i with w | v
  · simp only [ideleLog, Units.val_mul, Pi.add_apply]
    rw [Prod.fst_mul, Pi.mul_apply, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (idele_inf_ne_zero x w)) (norm_ne_zero_iff.mpr (idele_inf_ne_zero y w))]
    ring
  · simp only [ideleLog, Units.val_mul, Pi.add_apply]
    have : ((x : AdeleRing (𝓞 K) K) * (y : AdeleRing (𝓞 K) K)).2 v.1 =
      (x : AdeleRing (𝓞 K) K).2 v.1 * (y : AdeleRing (𝓞 K) K).2 v.1 := rfl
    rw [this, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (idele_fin_ne_zero x v.1))
      (norm_ne_zero_iff.mpr (idele_fin_ne_zero y v.1))]

theorem ideleLog_inv (x : IdeleGroup (𝓞 K) K) : ideleLog S x⁻¹ = - ideleLog S x := by
  have h := ideleLog_mul (S := S) x⁻¹ x
  have h1 : ideleLog S (1 : IdeleGroup (𝓞 K) K) = 0 := by
    funext i
    rcases i with w | v
    · change (w.mult : ℝ) * Real.log ‖(1 : w.Completion)‖ = 0
      simp
    · change Real.log ‖(1 : v.1.adicCompletion K)‖ = 0
      simp
  rw [inv_mul_cancel, h1] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem ideleLog_unitEmbedding (ξ : Kˣ) :
    ideleLog S (IdeleGroup.unitEmbedding (𝓞 K) K ξ) = logEmb K S (ξ : K) := by
  funext i
  rcases i with w | v
  · change (w.mult : ℝ) * Real.log ‖((ξ : K) : w.Completion)‖ = (w.mult : ℝ) * Real.log (w (ξ : K))
    rw [InfinitePlace.Completion.norm_coe]
    rfl
  · change Real.log ‖((ξ : K) : v.1.adicCompletion K)‖ = Real.log (FinitePlace.mk v.1 (ξ : K))
    rw [FinitePlace.mk_apply]
    rfl

theorem continuous_ideleLog (i : PlP K S) : Continuous fun x : IdeleGroup (𝓞 K) K => ideleLog S x i := by
  rcases i with w | v
  · have hev : Continuous (fun a : InfiniteAdeleRing K => a w) := continuous_apply w
    have hfst : Continuous (Prod.fst : AdeleRing (𝓞 K) K → InfiniteAdeleRing K) := continuous_fst
    have hval : Continuous (fun x : IdeleGroup (𝓞 K) K => (x : AdeleRing (𝓞 K) K)) := Units.continuous_val
    exact continuous_const.mul
      (Continuous.log ((hev.comp hfst).comp hval).norm fun x => norm_ne_zero_iff.mpr (idele_inf_ne_zero x w))
  · have hev : Continuous (fun a : FiniteAdeleRing (𝓞 K) K => a v.1) := RestrictedProduct.continuous_eval v.1
    have hsnd : Continuous (Prod.snd : AdeleRing (𝓞 K) K → FiniteAdeleRing (𝓞 K) K) := continuous_snd
    have hval : Continuous (fun x : IdeleGroup (𝓞 K) K => (x : AdeleRing (𝓞 K) K)) := Units.continuous_val
    exact Continuous.log ((hev.comp hsnd).comp hval).norm fun x => norm_ne_zero_iff.mpr (idele_fin_ne_zero x v.1)

/-! ### A compact set of representatives of $k^1/k^\times$ (Weil, IV.§4 Thm. 6) -/

/-- There is a compact set $C$ of ideles with $k^1\subseteq C\,k^\times$ (from QuadFormsKB's
`exists_isCompact_ideleOne_mul_mem`, transported as in `IdeleClassGroup.isCompact_normOne`). -/
theorem exists_isCompact_ideleGroupOne :
    ∃ C : Set (IdeleGroup (𝓞 K) K), IsCompact C ∧
      ∀ x ∈ ideleGroupOne K, ∃ z ∈ C, ∃ ξ : Kˣ, x = z * IdeleGroup.unitEmbedding (𝓞 K) K ξ := by
  obtain ⟨C, hC, hCx⟩ := exists_isCompact_ideleOne_mul_mem K
  refine ⟨(ideleGroupEquiv K).symm '' (Subtype.val '' C),
    (hC.image continuous_subtype_val).image (ideleGroupEquiv K).symm.continuous, fun x hx => ?_⟩
  have hg : ideleGroupEquiv K x ∈ ideleOne K := mem_ideleGroupOne_iff_mem_ideleOne.mp hx
  obtain ⟨γ, hγ, hmem⟩ := hCx ⟨_, hg⟩
  obtain ⟨ξ, hξ⟩ := (Subgroup.mem_subgroupOf.mp hγ : (γ : (Adeles K)ˣ) ∈ diagUnitsSub K)
  set z : (Adeles K)ˣ := ((γ⁻¹ * ⟨_, hg⟩ : ideleOne K) : (Adeles K)ˣ) with hz
  refine ⟨(ideleGroupEquiv K).symm z, Set.mem_image_of_mem _ ⟨_, hmem, rfl⟩, ξ, ?_⟩
  apply (ideleGroupEquiv K).injective
  have hz' : z = (γ : (Adeles K)ˣ)⁻¹ * ideleGroupEquiv K x := rfl
  rw [map_mul, ideleGroupEquiv_unitEmbedding, hξ, ContinuousMulEquiv.apply_symm_apply, hz', mul_comm, ← mul_assoc,
    mul_inv_cancel, one_mul]

/-- A principal idele lies in $\Omega(P)$ exactly when its generator is a $P$-unit. -/
theorem unitEmbedding_mem_omega_iff (ξ : Kˣ) :
    IdeleGroup.unitEmbedding (𝓞 K) K ξ ∈ omega K (S : Set (HeightOneSpectrum (𝓞 K))) ↔ ξ ∈ sUnits K S := by
  rw [mem_omega_iff]
  refine forall₂_congr fun v _ => ?_
  change Valued.v ((ξ : K) : v.adicCompletion K) = 1 ↔ _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-! ### $\Omega^1(P)/E(P)$ is compact (Weil, proof of Thm. 9) -/

/-- **Weil, proof of Thm. 9**: $\Omega^1(P)/E(P)$ is compact, in the form: there is $R$ such that for every
$x\in\Omega^1(P)$ some $\eta\in E(P)$ has $\lvert\log\lvert x_v\rvert_v-\log\lvert\eta\rvert_v\rvert\le R$ for all
$v\in P$. Weil: $\Omega^1(P)/E(P)$ is an open subgroup of the compact group $k^1/k^\times$. Here: a compact set $C$ of
representatives of $k^1/k^\times$ meets finitely many cosets $c\,\Omega(P)$; one principal idele $\xi_c$ per coset
corrects the representative into $\Omega(P)$, and the log map is bounded on $C$. -/
theorem exists_sUnit_near : ∃ R : ℝ, ∀ x ∈ omega K (S : Set (HeightOneSpectrum (𝓞 K))), x ∈ ideleGroupOne K →
    ∃ η ∈ sUnits K S, ∀ i, |ideleLog S x i - logEmb K S (η : K) i| ≤ R := by
  classical
  obtain ⟨C, hC, hCx⟩ := exists_isCompact_ideleGroupOne (K := K)
  set Ω := omega K (S : Set (HeightOneSpectrum (𝓞 K)))
  -- finitely many cosets cover $C$
  obtain ⟨J, hJ⟩ := hC.elim_finite_subcover (fun c : IdeleGroup (𝓞 K) K => (fun y => c⁻¹ * y) ⁻¹' (Ω : Set _))
    (fun c => (isOpen_omega _).preimage (continuous_const.mul continuous_id))
    (fun y _ => Set.mem_iUnion.mpr ⟨y, by simp [Ω]⟩)
  -- one correcting principal idele per coset
  let g : IdeleGroup (𝓞 K) K → Kˣ := fun c =>
    if h : ∃ ξ : Kˣ, c * IdeleGroup.unitEmbedding (𝓞 K) K ξ ∈ Ω then h.choose else 1
  have hg : ∀ c, (∃ ξ : Kˣ, c * IdeleGroup.unitEmbedding (𝓞 K) K ξ ∈ Ω) →
      c * IdeleGroup.unitEmbedding (𝓞 K) K (g c) ∈ Ω := by
    intro c h
    simp only [g, h, ↓reduceDIte]
    exact h.choose_spec
  -- bounds
  have hbdd : ∀ i, ∃ R₁, ∀ z ∈ C, |ideleLog S z i| ≤ R₁ := fun i => by
    obtain ⟨R₁, hR₁⟩ := hC.exists_bound_of_continuousOn (continuous_ideleLog (S := S) i).continuousOn
    exact ⟨R₁, fun z hz => by simpa [Real.norm_eq_abs] using hR₁ z hz⟩
  choose R₁ hR₁ using hbdd
  refine ⟨∑ i, R₁ i + ∑ c ∈ J, ∑ i, |logEmb K S (g c : K) i|, fun x hxΩ hx1 => ?_⟩
  obtain ⟨z, hzC, ξ, rfl⟩ := hCx x hx1
  obtain ⟨c, hcJ, hzc⟩ : ∃ c ∈ J, c⁻¹ * z ∈ Ω := by
    have := hJ hzC
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
    obtain ⟨c, hc, h⟩ := this
    exact ⟨c, hc, h⟩
  have hcξ : c * IdeleGroup.unitEmbedding (𝓞 K) K ξ ∈ Ω := by
    have : c * IdeleGroup.unitEmbedding (𝓞 K) K ξ = (c⁻¹ * z)⁻¹ * (z * IdeleGroup.unitEmbedding (𝓞 K) K ξ) := by
      rw [mul_inv_rev, inv_inv, mul_comm z⁻¹ c, mul_assoc, inv_mul_cancel_left]
    rw [this]
    exact mul_mem (inv_mem hzc) hxΩ
  have hgc := hg c ⟨ξ, hcξ⟩
  refine ⟨ξ * (g c)⁻¹, ?_, fun i => ?_⟩
  · rw [← unitEmbedding_mem_omega_iff, map_mul, map_inv, ← div_eq_mul_inv, ← mul_div_mul_left_eq_div _ _ c]
    exact div_mem hcξ hgc
  · have hlog : ideleLog S (z * IdeleGroup.unitEmbedding (𝓞 K) K ξ) i - logEmb K S ((ξ * (g c)⁻¹ : Kˣ) : K) i =
        ideleLog S z i + logEmb K S (g c : K) i := by
      rw [ideleLog_mul, ideleLog_unitEmbedding, Units.val_mul, logEmb_mul ξ.ne_zero (g c)⁻¹.ne_zero,
        ← ideleLog_unitEmbedding (S := S) (g c)⁻¹, map_inv, ideleLog_inv, ideleLog_unitEmbedding]
      simp only [Pi.add_apply, Pi.neg_apply]
      ring
    rw [hlog]
    calc |ideleLog S z i + logEmb K S (g c : K) i| ≤ |ideleLog S z i| + |logEmb K S (g c : K) i| := abs_add_le _ _
      _ ≤ ∑ i, R₁ i + ∑ c ∈ J, ∑ i, |logEmb K S (g c : K) i| := by
        gcongr
        · exact (hR₁ i z hzC).trans (Finset.single_le_sum (f := R₁) (fun j _ => (abs_nonneg _).trans (hR₁ j z hzC))
            (Finset.mem_univ i))
        · calc |logEmb K S (g c : K) i| ≤ ∑ i, |logEmb K S (g c : K) i| :=
                Finset.single_le_sum (f := fun j => |logEmb K S (g c : K) j|) (fun j _ => abs_nonneg _)
                  (Finset.mem_univ i)
            _ ≤ ∑ c ∈ J, ∑ i, |logEmb K S (g c : K) i| :=
                Finset.single_le_sum (f := fun c => ∑ i, |logEmb K S (g c : K) i|)
                  (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hcJ

/-! ### Ideles with prescribed components -/

theorem eventually_mem_of_eq_one (b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    (hS : ∀ v, v ∉ S → b v = 1) : ∀ᶠ v in cofinite, b v ∈ v.adicCompletionIntegers K := by
  refine Filter.eventually_cofinite.mpr ((S.finite_toSet).subset fun v hv => ?_)
  by_contra h
  exact hv (by rw [hS v h]; exact one_mem _)

variable (S) in
/-- The idele with components $a_w$ at the infinite places, $b_v$ at the finite places, $b_v=1$ outside $S$. -/
def mkIdele (a : ∀ w : InfinitePlace K, w.Completion) (b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    (ha : ∀ w, a w ≠ 0) (hb : ∀ v, b v ≠ 0) (hS : ∀ v, v ∉ S → b v = 1) : IdeleGroup (𝓞 K) K where
  val := (show InfiniteAdeleRing K from a, ⟨b, eventually_mem_of_eq_one b hS⟩)
  inv := (show InfiniteAdeleRing K from fun w => (a w)⁻¹,
    ⟨fun v => (b v)⁻¹, eventually_mem_of_eq_one (S := S) _ fun v hv => by simp [hS v hv]⟩)
  val_inv := Prod.ext (funext fun w => mul_inv_cancel₀ (ha w)) (FiniteAdeleRing.ext K fun v => mul_inv_cancel₀ (hb v))
  inv_val := Prod.ext (funext fun w => inv_mul_cancel₀ (ha w)) (FiniteAdeleRing.ext K fun v => inv_mul_cancel₀ (hb v))

theorem mkIdele_mem_omega (a : ∀ w : InfinitePlace K, w.Completion) (b : ∀ v : HeightOneSpectrum (𝓞 K),
    v.adicCompletion K) (ha : ∀ w, a w ≠ 0) (hb : ∀ v, b v ≠ 0) (hS : ∀ v, v ∉ S → b v = 1) :
    mkIdele S a b ha hb hS ∈ omega K (S : Set (HeightOneSpectrum (𝓞 K))) := by
  rw [mem_omega_iff]
  intro v hv
  change Valued.v (b v) = 1
  rw [hS v hv, map_one]

/-- For $x\in\Omega(P)$: $\log\lvert x\rvert_{\mathbb A}=\sum_{v\in P}\log\lvert x_v\rvert_v$. -/
theorem log_ideleGroupNorm_eq_sum {x : IdeleGroup (𝓞 K) K} (hx : x ∈ omega K (S : Set (HeightOneSpectrum (𝓞 K)))) :
    Real.log (ideleGroupNorm K x) = ∑ i, ideleLog S x i := by
  have hunit : IsUnit (x : AdeleRing (𝓞 K) K).2 :=
    (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).toMonoidHom x).isUnit
  have hfin : ∏ᶠ v, ‖(x : AdeleRing (𝓞 K) K).2 v‖ = ∏ v ∈ S, ‖(x : AdeleRing (𝓞 K) K).2 v‖ := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvS
    apply hv
    show ‖(x : AdeleRing (𝓞 K) K).2 v‖ = 1
    rw [FinitePlace.norm_def, (mem_omega_iff.mp hx) v hvS, map_one, NNReal.coe_one]
  rw [coe_ideleGroupNorm, AdeleRing.norm_def, InfiniteAdeleRing.norm_def,
    FiniteAdeleRing.norm_eq_finprod_of_isUnit hunit, hfin,
    Real.log_mul (Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (idele_inf_ne_zero x w)))
      (Finset.prod_ne_zero_iff.mpr fun v _ => norm_ne_zero_iff.mpr (idele_fin_ne_zero x v)),
    Real.log_prod (fun w _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (idele_inf_ne_zero x w))),
    Real.log_prod (fun v _ => norm_ne_zero_iff.mpr (idele_fin_ne_zero x v)), Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.log_pow]
    rfl
  · exact (Finset.sum_coe_sort S fun v => Real.log ‖(x : AdeleRing (𝓞 K) K).2 v‖).symm

/-- The norm of a uniformizer: $\lvert\pi_v\rvert_v=N(v)^{-1}$. -/
theorem norm_uniformizer (v : HeightOneSpectrum (𝓞 K)) {π : K} (hπ : v.valuation K π = WithZero.exp (-1 : ℤ)) :
    Real.log ‖(π : v.adicCompletion K)‖ = - Real.log (Ideal.absNorm v.asIdeal) := by
  have h : ‖(π : v.adicCompletion K)‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ := by
    rw [show (π : v.adicCompletion K) = FinitePlace.embedding v π from rfl, FinitePlace.norm_embedding', hπ,
      WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero), WithZero.log_exp]
    push_cast
    rw [zpow_neg, zpow_one]
  rw [h, Real.log_inv]

/-- **$\log\lvert\Omega^1(P)\rvert$ is cocompact in $G_1$** (Weil: $G\cong\mathbb R^r\times\mathbb Z^{s+1-r}$ and
$V_1/G_1$ compact): every $y\in\mathbb R^P$ with $\sum_vy_v=0$ is within $\sum_{v\in S}\log N(v)$ of
$\log\lvert x\rvert$ for some $x\in\Omega^1(P)$. -/
theorem exists_idele_near (y : PlP K S → ℝ) (hy : ∑ i, y i = 0) :
    ∃ x ∈ omega K (S : Set (HeightOneSpectrum (𝓞 K))), x ∈ ideleGroupOne K ∧
      ∀ i, |ideleLog S x i - y i| ≤ ∑ v ∈ S, Real.log (Ideal.absNorm v.asIdeal) := by
  classical
  set ℓ : HeightOneSpectrum (𝓞 K) → ℝ := fun v => Real.log (Ideal.absNorm v.asIdeal) with hℓ
  have hℓpos : ∀ v : HeightOneSpectrum (𝓞 K), 0 < ℓ v := fun v =>
    Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
  set R0 := ∑ v ∈ S, ℓ v
  have hℓR : ∀ v ∈ S, ℓ v ≤ R0 := fun v hv =>
    Finset.single_le_sum (f := ℓ) (fun v _ => (hℓpos v).le) hv
  -- uniformizers and finite components
  choose π hπ using fun v : HeightOneSpectrum (𝓞 K) => v.valuation_exists_uniformizer K
  have hπ0 : ∀ v, (π v : v.adicCompletion K) ≠ 0 := fun v h => by
    have h' := congrArg Valued.v h
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ v, map_zero] at h'
    exact WithZero.exp_ne_zero h'
  let n : ∀ v, v ∈ S → ℤ := fun v hv => -⌊y (.inr ⟨v, hv⟩) / ℓ v⌋
  let b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K := fun v =>
    if hv : v ∈ S then (π v : v.adicCompletion K) ^ n v hv else 1
  have hb0 : ∀ v, b v ≠ 0 := fun v => by
    by_cases hv : v ∈ S
    · simp only [b, hv, ↓reduceDIte]; exact zpow_ne_zero _ (hπ0 v)
    · simp only [b, hv, ↓reduceDIte]; exact one_ne_zero
  have hbS : ∀ v, v ∉ S → b v = 1 := fun v hv => by simp only [b, hv, ↓reduceDIte]
  have hlogb : ∀ v (hv : v ∈ S), Real.log ‖b v‖ = ⌊y (.inr ⟨v, hv⟩) / ℓ v⌋ * ℓ v := fun v hv => by
    simp only [b, hv, ↓reduceDIte, n, norm_zpow, Real.log_zpow, norm_uniformizer v (hπ v)]
    push_cast
    ring
  have hberr : ∀ v (hv : v ∈ S), |Real.log ‖b v‖ - y (.inr ⟨v, hv⟩)| ≤ ℓ v := fun v hv => by
    rw [hlogb v hv]
    have h1 := Int.floor_le (y (.inr ⟨v, hv⟩) / ℓ v)
    have h2 := Int.lt_floor_add_one (y (.inr ⟨v, hv⟩) / ℓ v)
    have hl := hℓpos v
    rw [abs_le]
    constructor
    · have : (y (.inr ⟨v, hv⟩) / ℓ v - 1) * ℓ v ≤ ⌊y (.inr ⟨v, hv⟩) / ℓ v⌋ * ℓ v :=
        mul_le_mul_of_nonneg_right (by linarith) hl.le
      rw [sub_mul, div_mul_cancel₀ _ hl.ne', one_mul] at this
      linarith
    · have : (⌊y (.inr ⟨v, hv⟩) / ℓ v⌋ : ℝ) * ℓ v ≤ y (.inr ⟨v, hv⟩) / ℓ v * ℓ v :=
        mul_le_mul_of_nonneg_right h1 hl.le
      rw [div_mul_cancel₀ _ hl.ne'] at this
      linarith
  -- the correction at one infinite place
  set δ := ∑ v : S, (Real.log ‖b v.1‖ - y (.inr v)) with hδ
  have hδR : |δ| ≤ R0 := by
    calc |δ| ≤ ∑ v : S, |Real.log ‖b v.1‖ - y (.inr v)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v : S, ℓ v.1 := Finset.sum_le_sum fun v _ => hberr v.1 v.2
      _ = R0 := Finset.sum_coe_sort S ℓ
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  let t : InfinitePlace K → ℝ := fun w => if w = w₀ then y (.inl w) - δ else y (.inl w)
  choose a ha0 ha using fun w : InfinitePlace K => exists_norm_completion' w (Real.exp (t w)) (Real.exp_pos _)
  have hloga : ∀ w, (w.mult : ℝ) * Real.log ‖a w‖ = t w := fun w => by
    rw [← Real.log_pow, ha w, Real.log_exp]
  set x := mkIdele S a b ha0 hb0 hbS
  have hxΩ := mkIdele_mem_omega (S := S) a b ha0 hb0 hbS
  have hlx_inl : ∀ w, ideleLog S x (.inl w) = t w := fun w => hloga w
  have hlx_inr : ∀ v : S, ideleLog S x (.inr v) = Real.log ‖b v.1‖ := fun v => rfl
  refine ⟨x, hxΩ, ?_, fun i => ?_⟩
  · -- norm one
    have hsum : ∑ i, ideleLog S x i = 0 := by
      rw [Fintype.sum_sum_type]
      simp only [hlx_inl, hlx_inr]
      have ht : ∑ w, t w = ∑ w, y (.inl w) - δ := by
        have h' : ∀ w, t w = y (.inl w) - if w = w₀ then δ else 0 := by
          intro w; simp only [t]; split_ifs <;> ring
        rw [Finset.sum_congr rfl (fun w _ => h' w), Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ w₀]
        simp
      rw [ht, hδ, Finset.sum_sub_distrib]
      have hy' := hy
      rw [Fintype.sum_sum_type] at hy'
      linarith
    have hlog := log_ideleGroupNorm_eq_sum hxΩ
    rw [hsum] at hlog
    show ideleGroupNorm K x = 1
    have hpos := ideleGroupNorm_pos x
    rcases Real.log_eq_zero.mp hlog with h | h | h
    · exact absurd (by exact_mod_cast h) hpos.ne'
    · exact_mod_cast h
    · have : (0 : ℝ) < ideleGroupNorm K x := by exact_mod_cast hpos
      linarith
  · rcases i with w | v
    · rw [hlx_inl]
      by_cases hw : w = w₀
      · simp only [t, hw, ↓reduceIte, sub_sub_cancel_left, abs_neg]
        exact hδR
      · simp only [t, hw, ↓reduceIte, sub_self, abs_zero]
        exact Finset.sum_nonneg fun v _ => (hℓpos v).le
    · rw [hlx_inr]
      exact (hberr v.1 v.2).trans (hℓR v.1 v.2)

/-- **$\Gamma$ is cocompact in $G_1$** (Weil, proof of Thm. 9): there is $R$ such that every $y\in\mathbb R^P$ with
$\sum_vy_v=0$ is within $R$ (in each coordinate) of $\log\lvert\eta\rvert$ for some $\eta\in E(P)$. -/
theorem exists_sUnit_near_hyperplane : ∃ R : ℝ, ∀ y : PlP K S → ℝ, ∑ i, y i = 0 →
    ∃ η ∈ sUnits K S, ∀ i, |y i - logEmb K S (η : K) i| ≤ R := by
  obtain ⟨R, hR⟩ := exists_sUnit_near (K := K) (S := S)
  refine ⟨R + ∑ v ∈ S, Real.log (Ideal.absNorm v.asIdeal), fun y hy => ?_⟩
  obtain ⟨x, hxΩ, hx1, hx⟩ := exists_idele_near y hy
  obtain ⟨η, hη, hηx⟩ := hR x hxΩ hx1
  refine ⟨η, hη, fun i => ?_⟩
  calc |y i - logEmb K S (η : K) i| = |(ideleLog S x i - logEmb K S (η : K) i) - (ideleLog S x i - y i)| := by
        ring_nf
    _ ≤ |ideleLog S x i - logEmb K S (η : K) i| + |ideleLog S x i - y i| := abs_sub _ _
    _ ≤ R + ∑ v ∈ S, Real.log (Ideal.absNorm v.asIdeal) := add_le_add (hηx i) (hx i)

/-! ### $\Gamma$ is a lattice in $G_1$ (Weil, Lemma 5) and Theorem 9 -/

/-- $\log\lvert a^m\rvert=m\log\lvert a\rvert$. -/
theorem logEmb_zpow (a : Kˣ) (m : ℤ) : logEmb K S ((a ^ m : Kˣ) : K) = m • logEmb K S (a : K) := by
  have hnat : ∀ k : ℕ, logEmb K S ((a ^ k : Kˣ) : K) = (k : ℤ) • logEmb K S (a : K) := by
    intro k
    induction k with
    | zero => simp [logEmb_one]
    | succ k ih =>
      rw [pow_succ, Units.val_mul, logEmb_mul (a ^ k).ne_zero a.ne_zero, ih]
      push_cast
      rw [add_smul, one_smul]
  rcases m with k | k
  · simpa using hnat k
  · rw [zpow_negSucc]
    have h0 : logEmb K S ((a ^ (k + 1) : Kˣ) : K) + logEmb K S (((a ^ (k + 1))⁻¹ : Kˣ) : K) = 0 := by
      rw [← logEmb_mul (a ^ (k + 1)).ne_zero (a ^ (k + 1))⁻¹.ne_zero, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, logEmb_one]
    rw [eq_neg_of_add_eq_zero_right h0, hnat (k + 1), Int.negSucc_eq, neg_smul]
    push_cast
    ring_nf

variable (K S) in
/-- $\Gamma$, the image of $E(P)$ under the logarithmic embedding, as a $\mathbb Z$-submodule of $\mathbb R^P$. -/
def gammaLattice : Submodule ℤ (PlP K S → ℝ) where
  carrier := {γ | ∃ η ∈ sUnits K S, logEmb K S (η : K) = γ}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, by rw [Units.val_mul, logEmb_mul a.ne_zero b.ne_zero]⟩
  zero_mem' := ⟨1, one_mem _, by rw [Units.val_one, logEmb_one]⟩
  smul_mem' := by
    rintro n _ ⟨a, ha, rfl⟩
    exact ⟨a ^ n, zpow_mem ha n, logEmb_zpow a n⟩

theorem logEmb_mem_gammaLattice {η : Kˣ} (hη : η ∈ sUnits K S) : logEmb K S (η : K) ∈ gammaLattice K S :=
  ⟨η, hη, rfl⟩

/-- $\Gamma$ is discrete. -/
instance discreteTopology_gammaLattice : DiscreteTopology (gammaLattice K S) := by
  classical
  have hT : {γ | γ ∈ gammaLattice K S ∧ ∀ i, |γ i| ≤ 1}.Finite := by
    refine ((finite_logEmb_bounded (K := K) (S := S) 1).image fun e : Kˣ => logEmb K S (e : K)).subset ?_
    rintro γ ⟨⟨η, hη, rfl⟩, hb⟩
    exact ⟨η, ⟨hη, hb⟩, rfl⟩
  obtain ⟨ε, hε, hεT⟩ : ∃ ε > (0 : ℝ), ∀ γ ∈ hT.toFinset, γ ≠ 0 → ε ≤ ‖γ‖ := by
    by_cases h : (hT.toFinset.filter (· ≠ 0)).Nonempty
    · obtain ⟨γ₀, hγ₀, hmin⟩ := Finset.exists_min_image _ (fun γ => ‖γ‖) h
      refine ⟨‖γ₀‖, norm_pos_iff.mpr (Finset.mem_filter.mp hγ₀).2, fun γ hγ hγ0 => hmin γ ?_⟩
      exact Finset.mem_filter.mpr ⟨hγ, hγ0⟩
    · exact ⟨1, one_pos, fun γ hγ hγ0 => absurd ⟨γ, Finset.mem_filter.mpr ⟨hγ, hγ0⟩⟩ h⟩
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have : ({0} : Set (gammaLattice K S)) = Subtype.val ⁻¹' Metric.ball (0 : PlP K S → ℝ) (min ε 1) := by
    ext ⟨γ, hγ⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · intro h
      have h0 : γ = 0 := congrArg Subtype.val h
      subst h0
      simp [hε]
    · intro h
      by_contra hne
      have hγ0 : γ ≠ 0 := fun h0 => hne (Subtype.ext h0)
      have hcube : ∀ i, |γ i| ≤ 1 := fun i =>
        ((norm_le_pi_norm γ i).trans (h.le.trans (min_le_right _ _)) : ‖γ i‖ ≤ 1)
      have := hεT γ (hT.mem_toFinset.mpr ⟨hγ, hcube⟩) hγ0
      linarith [min_le_left ε 1]
  rw [this]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

variable (K S) in
/-- The hyperplane $G_1=\{y\in\mathbb R^P:\sum_vy_v=0\}$. -/
def hyperplane : Submodule ℝ (PlP K S → ℝ) := LinearMap.ker (∑ i, LinearMap.proj i)

theorem mem_hyperplane {y : PlP K S → ℝ} : y ∈ hyperplane K S ↔ ∑ i, y i = 0 := by
  simp [hyperplane, LinearMap.mem_ker]

theorem finrank_hyperplane : Module.finrank ℝ (hyperplane K S) = Fintype.card (PlP K S) - 1 := by
  classical
  set f : (PlP K S → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have hsurj : Function.Surjective f := fun c => ⟨Pi.single (.inl w₀) c, by
    simp [f, Fintype.sum_sum_type, Pi.single_apply]⟩
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at h
  show Module.finrank ℝ (LinearMap.ker f) = _
  omega

/-- $\Gamma$ spans $G_1$: it lies in $G_1$ (product formula) and is cocompact there. -/
theorem span_gammaLattice : Submodule.span ℝ (gammaLattice K S : Set (PlP K S → ℝ)) = hyperplane K S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨η, hη, rfl⟩
    exact mem_hyperplane.mpr (sum_logEmb_eq_zero hη)
  · intro y hy
    set W := Submodule.span ℝ (gammaLattice K S : Set (PlP K S → ℝ))
    obtain ⟨R, hR⟩ := exists_sUnit_near_hyperplane (K := K) (S := S)
    have hWc : IsClosed (W : Set (PlP K S → ℝ)) := W.closed_of_finiteDimensional
    change y ∈ (W : Set (PlP K S → ℝ))
    rw [← hWc.closure_eq]
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    set R' := max R 0
    set t : ℝ := (R' + 1) / ε
    have ht : 0 < t := div_pos (by positivity) hε
    obtain ⟨η, hη, hηy⟩ := hR (t • y) (by
      rw [← mem_hyperplane]
      exact (hyperplane K S).smul_mem t hy)
    refine ⟨t⁻¹ • logEmb K S (η : K), W.smul_mem _ (Submodule.subset_span (logEmb_mem_gammaLattice hη)), ?_⟩
    have hnorm : ‖t • y - logEmb K S (η : K)‖ ≤ R' :=
      (pi_norm_le_iff_of_nonneg (le_max_right R 0)).mpr fun i =>
        (hηy i).trans (le_max_left R 0)
    rw [dist_eq_norm]
    have : y - t⁻¹ • logEmb K S (η : K) = t⁻¹ • (t • y - logEmb K S (η : K)) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    rw [this, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
    calc t⁻¹ * ‖t • y - logEmb K S (η : K)‖ ≤ t⁻¹ * R' := mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ < ε := by
        rw [inv_mul_lt_iff₀ ht]
        simp only [t]
        rw [div_mul_cancel₀ _ hε.ne']
        linarith

/-- **$\Gamma\cong\mathbb Z^s$ with $s=\lvert P\rvert-1$** (Weil, Lemma 5 applied to $\Gamma\subset G_1$): the rank of
the free $\mathbb Z$-module $\Gamma$. -/
theorem finrank_gammaLattice : Module.finrank ℤ (gammaLattice K S) = Fintype.card (PlP K S) - 1 := by
  have h := Real.finrank_eq_int_finrank_of_discrete (s := (gammaLattice K S : Set (PlP K S → ℝ)))
    (by rw [Submodule.span_eq]; infer_instance)
  rw [Set.finrank, Set.finrank, span_gammaLattice, finrank_hyperplane, Submodule.span_eq] at h
  exact h.symm

/-- **Weil, IV.§4, Theorem 9** (the $P$-unit theorem, number field case): with $s=\lvert P\rvert-1$ (here
$\lvert P\rvert$ = number of infinite places + $\lvert S\rvert$) there are $e_1,\dots,e_s\in E(P)$ such that every
$\eta\in E(P)$ is uniquely $\zeta\,e_1^{n_1}\cdots e_s^{n_s}$ with $\zeta$ a root of unity and $n_i\in\mathbb Z$: $E(P)$ is
the direct product of the group of roots of unity of $k$ and of a free abelian group of rank $s$. -/
@[kb "weil1973bnt" "Ch. IV, §4, Thm. 9 (p. 78), number field case"]
theorem weil_IV_4_thm9 :
    ∃ e : Fin (Fintype.card (InfinitePlace K) + S.card - 1) → Kˣ, (∀ i, e i ∈ sUnits K S) ∧
      ∀ η ∈ sUnits K S, ∃! p : Kˣ × (Fin (Fintype.card (InfinitePlace K) + S.card - 1) → ℤ),
        (∃ n : ℕ, 0 < n ∧ (p.1 : K) ^ n = 1) ∧ η = p.1 * ∏ i, e i ^ p.2 i := by
  classical
  set s := Fintype.card (InfinitePlace K) + S.card - 1
  have hcard : Fintype.card (PlP K S) = Fintype.card (InfinitePlace K) + S.card := by
    simp [PlP, Fintype.card_sum]
  have hrank : Module.finrank ℤ (gammaLattice K S) = s := by rw [finrank_gammaLattice, hcard]
  let b : Module.Basis (Fin s) ℤ (gammaLattice K S) := Module.finBasisOfFinrankEq ℤ _ hrank
  have hb : ∀ i, ∃ η ∈ sUnits K S, logEmb K S (η : K) = (b i : PlP K S → ℝ) := fun i => (b i).2
  choose e he hel using hb
  have hlogprod : ∀ (ζ : Kˣ) (n : Fin s → ℤ),
      logEmb K S ((ζ * ∏ i, e i ^ n i : Kˣ) : K) = logEmb K S (ζ : K) + ∑ i, n i • (b i : PlP K S → ℝ) := by
    intro ζ n
    have hprod : ∀ T : Finset (Fin s),
        logEmb K S ((∏ i ∈ T, e i ^ n i : Kˣ) : K) = ∑ i ∈ T, n i • (b i : PlP K S → ℝ) := by
      intro T
      induction T using Finset.induction_on with
      | empty => simp [logEmb_one]
      | insert j T hj ih =>
        rw [Finset.prod_insert hj, Finset.sum_insert hj, Units.val_mul,
          logEmb_mul (e j ^ n j).ne_zero (∏ i ∈ T, e i ^ n i).ne_zero, ih, logEmb_zpow, hel]
    rw [Units.val_mul, logEmb_mul ζ.ne_zero (∏ i, e i ^ n i).ne_zero, hprod]
  have hsU : ∀ (n : Fin s → ℤ), (∏ i, e i ^ n i) ∈ sUnits K S :=
    fun n => Subgroup.prod_mem _ fun i _ => zpow_mem (he i) _
  refine ⟨e, he, fun η hη => ?_⟩
  set c : Fin s → ℤ := fun i => b.repr ⟨logEmb K S (η : K), logEmb_mem_gammaLattice hη⟩ i
  have hsum : ∑ i, c i • (b i : PlP K S → ℝ) = logEmb K S (η : K) := by
    have h := b.sum_repr ⟨logEmb K S (η : K), logEmb_mem_gammaLattice hη⟩
    have h' := congrArg Subtype.val h
    rw [Submodule.coe_sum] at h'
    exact h'
  set ζ : Kˣ := η * (∏ i, e i ^ c i)⁻¹
  have hζU : ζ ∈ sUnits K S := mul_mem hη (inv_mem (hsU c))
  have hηζ : η = ζ * ∏ i, e i ^ c i := by simp [ζ]
  have hζlog : logEmb K S (ζ : K) = 0 := by
    have h := hlogprod ζ c
    rw [← hηζ, ← hsum] at h
    exact (add_eq_right.mp h.symm)
  refine ⟨(ζ, c), ⟨(logEmb_eq_zero_iff hζU).mp hζlog, hηζ⟩, ?_⟩
  rintro ⟨ζ', c'⟩ ⟨hζ', hηeq⟩
  have hζ'U : ζ' ∈ sUnits K S := by
    have : ζ' = η * (∏ i, e i ^ c' i)⁻¹ := by rw [hηeq]; simp
    rw [this]; exact mul_mem hη (inv_mem (hsU c'))
  have hζ'log : logEmb K S (ζ' : K) = 0 := (logEmb_eq_zero_iff hζ'U).mpr hζ'
  have hcc : c' = c := by
    have h1 := hlogprod ζ' c'
    rw [← hηeq, hζ'log, zero_add, ← hsum] at h1
    have h2 : ∑ i, c' i • b i = ∑ i, c i • b i := by
      apply Subtype.ext
      simpa [Submodule.coe_sum, Submodule.coe_smul] using h1.symm
    funext i
    have := congrArg (fun z => b.repr z i) h2
    simpa [map_sum, Module.Basis.repr_self, Finsupp.single_apply] using this
  subst hcc
  have : ζ' = ζ := by
    have h1 : ζ' * ∏ i, e i ^ c i = ζ * ∏ i, e i ^ c i := by rw [← hηeq, ← hηζ]
    exact mul_right_cancel h1
  rw [this]

end NumberFieldKB.WeilBNT

end
