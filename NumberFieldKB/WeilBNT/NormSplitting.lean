import NumberFieldKB.WeilBNT.IdeleClassFiniteness
import Mathlib.Algebra.Order.Positive.Field

/-!
# Weil, *Basic Number Theory*, Chapter IV, §4: Corollary 2 of Theorem 5 and Theorem 6 (splitting)

$k$ is a number field of degree $n$ over $\mathbb Q$. Weil (IV.§4, Cor. 2 of Thm. 5, p. 75–76) calls $Z(\lambda)$, for
$\lambda\in\mathbb R_+^\times$, the idele with $Z(\lambda)_v=1$ at every finite place $v$ and $Z(\lambda)_w=\lambda$ at
every infinite place $w$, and proves:

* $\lambda\mapsto Z(\lambda)$ is an isomorphism of $\mathbb R_+^\times$ onto a closed subgroup $M$ of $k_{\mathbb A}^\times$
  (`weil_IV_4_thm5_cor2_isClosedEmbedding`), with $\lvert Z(\lambda)\rvert_{\mathbb A}=\lambda^n$
  (`ideleGroupNorm_weilZ`);
* $k_{\mathbb A}^\times$ is the direct product of $k^1$ and $M$ (`weil_IV_4_thm5_cor2`, a topological group isomorphism
  $k^1\times\mathbb R_+^\times\to k_{\mathbb A}^\times$, $(a,\lambda)\mapsto aZ(\lambda)$).

Theorem 6 (p. 76) then adds that $k_{\mathbb A}^\times/k^\times$ is the direct product of the compact group $k^1/k^\times$
and a group isomorphic to $\mathbb R_+^\times$ (`weil_IV_4_thm6`, again a topological group isomorphism; the other
assertions of Theorem 6, discreteness of $k^\times$ and compactness of $k^1/k^\times$, are NumberFieldKB's
`IdeleClassGroup.isCompact_normOne` and QuadFormsKB's `discreteTopology_diagUnitsSub`).

At an infinite place $w$, "$\lambda$" means the image of $\lambda$ under the canonical embedding
$\mathbb R\to k_w$ (`realToCompletion`): $k_w\cong\mathbb R$ or $\mathbb C$ by Mathlib's `ringEquivRealOfIsReal`,
`ringEquivComplexOfIsComplex`. The module of $\lambda$ at a complex place is $\lambda^2$ (Mathlib's normalisation of the
adelic norm, `InfiniteAdeleRing.norm_def`), which is why the total is $\lambda^n$ (`InfinitePlace.sum_mult_eq`).
-/

open IsDedekindDomain NumberField Topology
open NumberFieldKB.Ideles
open scoped NNReal

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

/-! ### The real numbers inside a completion at an infinite place -/

/-- The canonical embedding $\mathbb R\to k_w$ at an infinite place $w$ (through $k_w\cong\mathbb R$ or
$k_w\cong\mathbb C$). -/
def realToCompletion (w : InfinitePlace K) : ℝ →+* w.Completion :=
  open scoped Classical in
  if h : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm.toRingHom
  else (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (InfinitePlace.not_isReal_iff_isComplex.1 h)).symm.toRingHom.comp Complex.ofRealHom

omit [NumberField K] in
theorem norm_realToCompletion (w : InfinitePlace K) (t : ℝ) : ‖realToCompletion w t‖ = |t| := by
  unfold realToCompletion
  split_ifs with h
  · set e := InfinitePlace.Completion.isometryEquivRealOfIsReal h
    have he : ∀ y, ‖e y‖ = ‖y‖ := fun y => (e.isometry.norm_map_of_map_zero (map_zero
      (InfinitePlace.Completion.ringEquivRealOfIsReal h)) y)
    have h1 := he ((InfinitePlace.Completion.ringEquivRealOfIsReal h).symm t)
    have h2 : e ((InfinitePlace.Completion.ringEquivRealOfIsReal h).symm t) = t :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal h).apply_symm_apply t
    rw [h2, Real.norm_eq_abs] at h1
    exact h1.symm
  · have hc := InfinitePlace.not_isReal_iff_isComplex.1 h
    set e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc
    have he : ∀ y, ‖e y‖ = ‖y‖ := fun y => (e.isometry.norm_map_of_map_zero (map_zero
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc)) y)
    have h1 := he ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm (t : ℂ))
    have h2 : e ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm (t : ℂ)) = (t : ℂ) :=
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).apply_symm_apply _
    rw [h2, Complex.norm_real, Real.norm_eq_abs] at h1
    exact h1.symm

omit [NumberField K] in
theorem isometry_realToCompletion (w : InfinitePlace K) : Isometry (realToCompletion w) :=
  AddMonoidHomClass.isometry_of_norm _ fun t => by rw [norm_realToCompletion, Real.norm_eq_abs]

omit [NumberField K] in
theorem continuous_realToCompletion (w : InfinitePlace K) : Continuous (realToCompletion w) :=
  (isometry_realToCompletion w).continuous

/-! ### Weil's ideles $Z(\lambda)$ -/

/-- The positive reals $\mathbb R_+^\times$ as units of $\mathbb R$. -/
def posToUnits : {t : ℝ // 0 < t} →* ℝˣ where
  toFun t := Units.mk0 t t.2.ne'
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

variable (K) in
/-- The adele that is $t$ at every infinite place and $1$ at every finite place, as a multiplicative map. -/
def realToAdele : ℝ →* AdeleRing (𝓞 K) K :=
  MonoidHom.prod (RingHom.pi fun w => realToCompletion w).toMonoidHom 1

variable (K) in
/-- **Weil's $Z(\lambda)$** (IV.§4, Cor. 2 of Thm. 5): the idele equal to $\lambda$ at every infinite place and to $1$ at
every finite place. -/
def weilZ : {t : ℝ // 0 < t} →* IdeleGroup (𝓞 K) K :=
  (Units.map (realToAdele K)).comp posToUnits

@[simp] theorem weilZ_fst (t : {t : ℝ // 0 < t}) (w : InfinitePlace K) :
    ((weilZ K t : AdeleRing (𝓞 K) K)).1 w = realToCompletion w t := rfl

@[simp] theorem weilZ_snd (t : {t : ℝ // 0 < t}) : ((weilZ K t : AdeleRing (𝓞 K) K)).2 = 1 := rfl

/-- $\lvert Z(\lambda)\rvert_{\mathbb A}=\lambda^n$, $n=[k:\mathbb Q]$ (Weil, p. 76). -/
theorem ideleGroupNorm_weilZ (t : {t : ℝ // 0 < t}) :
    (ideleGroupNorm K (weilZ K t) : ℝ) = (t : ℝ) ^ Module.finrank ℚ K := by
  rw [coe_ideleGroupNorm, AdeleRing.norm_def, InfiniteAdeleRing.norm_def, weilZ_snd]
  have h2 : ‖(1 : FiniteAdeleRing (𝓞 K) K)‖ = 1 := by
    have h : ∀ v : HeightOneSpectrum (𝓞 K), ‖(1 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := fun v => norm_one
    simp [FiniteAdeleRing.norm_def, h]
  rw [h2, mul_one]
  simp only [weilZ_fst, norm_realToCompletion, abs_of_pos t.2]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

theorem weilZ_injective : Function.Injective (weilZ K) := by
  intro s t h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have h1 := congrArg (fun x : IdeleGroup (𝓞 K) K => ‖(x : AdeleRing (𝓞 K) K).1 w‖) h
  simp only [weilZ_fst, norm_realToCompletion, abs_of_pos s.2, abs_of_pos t.2] at h1
  exact Subtype.ext h1

theorem continuous_weilZ : Continuous (weilZ K) := by
  have hA : Continuous (realToAdele K) := by
    refine Continuous.prodMk (continuous_pi fun w => ?_) continuous_const
    exact (continuous_realToCompletion w)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hA.comp continuous_subtype_val
  · have : (fun t : {t : ℝ // 0 < t} => (((weilZ K t)⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)) =
        fun t : {t : ℝ // 0 < t} => realToAdele K ((t : ℝ)⁻¹) := by
      funext t
      rfl
    rw [this]
    exact hA.comp (continuous_subtype_val.inv₀ fun t => t.2.ne')

/-- $Z(\lambda)\in\Omega(P)$ for every $P$ (Weil: $M$ is a subgroup of $k_{\mathbb A}(P_\infty)^\times$). -/
theorem weilZ_mem_omega (S : Set (HeightOneSpectrum (𝓞 K))) (t : {t : ℝ // 0 < t}) : weilZ K t ∈ omega K S := by
  rw [mem_omega_iff]
  intro v _
  rw [weilZ_snd]
  exact map_one _

variable (K) in
/-- **The positive part of the norm**: $x\mapsto\lvert x\rvert_{\mathbb A}^{1/n}$, so that
$\lvert Z(\lvert x\rvert^{1/n})\rvert_{\mathbb A}=\lvert x\rvert_{\mathbb A}$. -/
def normRoot : IdeleGroup (𝓞 K) K →* {t : ℝ // 0 < t} where
  toFun x := ⟨((ideleGroupNorm K x : ℝ≥0) ^ ((Module.finrank ℚ K : ℝ)⁻¹) : ℝ≥0), by
    have := ideleGroupNorm_pos x
    positivity⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [NNReal.mul_rpow]

theorem coe_normRoot (x : IdeleGroup (𝓞 K) K) :
    (normRoot K x : ℝ) = (ideleGroupNorm K x : ℝ) ^ ((Module.finrank ℚ K : ℝ)⁻¹) := by
  simp [normRoot]

theorem continuous_normRoot : Continuous (normRoot K) := by
  refine Continuous.subtype_mk ?_ _
  refine NNReal.continuous_coe.comp ?_
  exact (NNReal.continuous_rpow_const (by positivity)).comp continuous_ideleGroupNorm

theorem ideleGroupNorm_weilZ_normRoot (x : IdeleGroup (𝓞 K) K) :
    ideleGroupNorm K (weilZ K (normRoot K x)) = ideleGroupNorm K x := by
  apply NNReal.coe_injective
  rw [ideleGroupNorm_weilZ, coe_normRoot, ← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _),
    inv_mul_cancel₀ (by exact_mod_cast Module.finrank_pos.ne'), Real.rpow_one]

theorem normRoot_weilZ (t : {t : ℝ // 0 < t}) : normRoot K (weilZ K t) = t := by
  ext
  rw [coe_normRoot, ideleGroupNorm_weilZ, ← Real.rpow_natCast, ← Real.rpow_mul t.2.le,
    mul_inv_cancel₀ (by exact_mod_cast Module.finrank_pos.ne'), Real.rpow_one]

theorem normRoot_eq_one_of_mem {x : IdeleGroup (𝓞 K) K} (hx : x ∈ ideleGroupOne K) : normRoot K x = 1 := by
  ext
  rw [coe_normRoot, (MonoidHom.mem_ker).1 hx]
  simp

/-- The idele group is Hausdorff. (Mathlib has no `T2Space` instance for `AdeleRing`; the finite adele ring is Hausdorff
because it injects continuously into the product of the completions.) -/
theorem t2Space_ideleGroup : T2Space (IdeleGroup (𝓞 K) K) := by
  have : ∀ v : HeightOneSpectrum (𝓞 K), T2Space (v.adicCompletion K) := fun v => by
    have : T0Space (v.adicCompletion K) := inferInstance
    infer_instance
  have : T2Space (FiniteAdeleRing (𝓞 K) K) :=
    .of_injective_continuous DFunLike.coe_injective RestrictedProduct.continuous_coe
  have : T2Space (InfiniteAdeleRing K) := inferInstanceAs (T2Space ((v : InfinitePlace K) → v.Completion))
  have : T2Space (AdeleRing (𝓞 K) K) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
  exact Units.isEmbedding_embedProduct.t2Space

variable (K) in
/-- Weil's closed subgroup $M=\{Z(\lambda)\}$ of $k_{\mathbb A}^\times$. -/
def weilM : Subgroup (IdeleGroup (𝓞 K) K) := (weilZ K).range

/-- **Weil, IV.§4, Corollary 2 of Theorem 5, first assertion**: $\lambda\mapsto Z(\lambda)$ is an isomorphism of
$\mathbb R_+^\times$ onto a closed subgroup $M$ of $k_{\mathbb A}^\times$ (a closed embedding of topological groups). -/
@[kb "weil1973bnt" "Ch. IV, §4, Cor. 2 of Thm. 5 (p. 75–76), number field case"]
theorem weil_IV_4_thm5_cor2_isClosedEmbedding : IsClosedEmbedding (weilZ K) := by
  have hleft : ∀ t, normRoot K (weilZ K t) = t := normRoot_weilZ
  have hcomp : normRoot K ∘ weilZ K = id := funext hleft
  have hemb : IsEmbedding (weilZ K) :=
    IsEmbedding.of_comp continuous_weilZ continuous_normRoot (by rw [hcomp]; exact IsEmbedding.id)
  refine ⟨hemb, ?_⟩
  have : Set.range (weilZ K) = {x | weilZ K (normRoot K x) = x} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      simp [hleft]
    · intro hx
      exact ⟨_, hx⟩
  rw [this]
  have := t2Space_ideleGroup (K := K)
  exact isClosed_eq (continuous_weilZ.comp continuous_normRoot) continuous_id

theorem isClosed_weilM : IsClosed (weilM K : Set (IdeleGroup (𝓞 K) K)) :=
  weil_IV_4_thm5_cor2_isClosedEmbedding.isClosed_range

/-- The $k^1$-component $x\,Z(\lvert x\rvert^{1/n})^{-1}$ of an idele. -/
theorem mul_weilZ_normRoot_inv_mem (x : IdeleGroup (𝓞 K) K) :
    x * (weilZ K (normRoot K x))⁻¹ ∈ ideleGroupOne K := by
  show ideleGroupNorm K _ = 1
  rw [map_mul, map_inv, ideleGroupNorm_weilZ_normRoot, mul_inv_cancel₀ (ideleGroupNorm_pos x).ne']

variable (K) in
/-- **Weil, IV.§4, Corollary 2 of Theorem 5, second assertion**: $k_{\mathbb A}^\times$ is the direct product of $k^1$ and
$M$: $(a,\lambda)\mapsto a\,Z(\lambda)$ is an isomorphism of topological groups $k^1\times\mathbb R_+^\times\to
k_{\mathbb A}^\times$. -/
@[kb "weil1973bnt" "Ch. IV, §4, Cor. 2 of Thm. 5 (p. 75–76), number field case"]
def weil_IV_4_thm5_cor2 : (ideleGroupOne K × {t : ℝ // 0 < t}) ≃ₜ* IdeleGroup (𝓞 K) K where
  toFun p := (p.1 : IdeleGroup (𝓞 K) K) * weilZ K p.2
  invFun x := (⟨x * (weilZ K (normRoot K x))⁻¹, mul_weilZ_normRoot_inv_mem x⟩, normRoot K x)
  left_inv p := by
    have h : normRoot K ((p.1 : IdeleGroup (𝓞 K) K) * weilZ K p.2) = p.2 := by
      rw [map_mul, normRoot_eq_one_of_mem p.1.2, one_mul, normRoot_weilZ]
    ext
    · simp only [h, mul_inv_cancel_right]
    · exact congrArg Subtype.val h
  right_inv x := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul]
    exact mul_mul_mul_comm _ _ _ _
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (continuous_weilZ.comp continuous_snd)
  continuous_invFun := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_normRoot
    exact continuous_id.mul (continuous_weilZ.comp continuous_normRoot).inv

@[simp] theorem weil_IV_4_thm5_cor2_apply (p : ideleGroupOne K × {t : ℝ // 0 < t}) :
    weil_IV_4_thm5_cor2 K p = (p.1 : IdeleGroup (𝓞 K) K) * weilZ K p.2 := rfl

@[simp] theorem weil_IV_4_thm5_cor2_symm_apply (x : IdeleGroup (𝓞 K) K) :
    (weil_IV_4_thm5_cor2 K).symm x =
      (⟨x * (weilZ K (normRoot K x))⁻¹, mul_weilZ_normRoot_inv_mem x⟩, normRoot K x) := rfl

/-! ### Theorem 6: $k_{\mathbb A}^\times/k^\times\cong(k^1/k^\times)\times\mathbb R_+^\times$ -/

variable (K) in
/-- The map $k_{\mathbb A}^\times\to(k^1/k^\times)\times\mathbb R_+^\times$,
$x\mapsto\bigl(x\,Z(\lvert x\rvert^{1/n})^{-1}\bmod k^\times,\ \lvert x\rvert^{1/n}\bigr)$. -/
def classSplitAux : IdeleGroup (𝓞 K) K →* IdeleClassGroup.normOne K × {t : ℝ // 0 < t} :=
  (((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)).subgroupMap (ideleGroupOne K)).prodMap
    (MonoidHom.id _)).comp (weil_IV_4_thm5_cor2 K).symm.toMonoidHom

theorem classSplitAux_apply (x : IdeleGroup (𝓞 K) K) :
    classSplitAux K x = (⟨((x * (weilZ K (normRoot K x))⁻¹ : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K),
      x * (weilZ K (normRoot K x))⁻¹, mul_weilZ_normRoot_inv_mem x, rfl⟩, normRoot K x) := rfl

theorem principalSubgroup_le_ker_classSplitAux :
    IdeleGroup.principalSubgroup (𝓞 K) K ≤ (classSplitAux K).ker := by
  intro x hx
  have h1 : normRoot K x = 1 := normRoot_eq_one_of_mem (principalSubgroup_le_ideleGroupOne hx)
  rw [MonoidHom.mem_ker, classSplitAux_apply]
  ext
  · simp only [h1, map_one, inv_one, mul_one]
    exact (QuotientGroup.eq_one_iff x).2 hx
  · simp [h1]

variable (K) in
/-- The quotient map $k_{\mathbb A}^\times/k^\times\to(k^1/k^\times)\times\mathbb R_+^\times$. -/
def classSplit : IdeleClassGroup (𝓞 K) K →* IdeleClassGroup.normOne K × {t : ℝ // 0 < t} :=
  QuotientGroup.lift _ (classSplitAux K) principalSubgroup_le_ker_classSplitAux

variable (K) in
/-- The inverse map $(c,\lambda)\mapsto c\cdot Z(\lambda)$. -/
def classUnsplit : IdeleClassGroup.normOne K × {t : ℝ // 0 < t} →* IdeleClassGroup (𝓞 K) K where
  toFun p := (p.1 : IdeleClassGroup (𝓞 K) K) * ((weilZ K p.2 : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K)
  map_one' := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul, QuotientGroup.mk_mul]
    exact mul_mul_mul_comm (G := IdeleClassGroup (𝓞 K) K) _ _ _ _

theorem continuous_classSplitAux : Continuous (classSplitAux K) := by
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_normRoot
  exact QuotientGroup.continuous_mk.comp (continuous_id.mul (continuous_weilZ.comp continuous_normRoot).inv)

theorem classSplit_classUnsplit (p : IdeleClassGroup.normOne K × {t : ℝ // 0 < t}) :
    classSplit K (classUnsplit K p) = p := by
  obtain ⟨⟨c, a, ha, rfl⟩, t⟩ := p
  have h : normRoot K (a * weilZ K t) = t := by
    rw [map_mul, normRoot_eq_one_of_mem ha, one_mul, normRoot_weilZ]
  have h2 : classUnsplit K (⟨_, a, ha, rfl⟩, t) =
      ((a * weilZ K t : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K) := rfl
  rw [h2, classSplit, QuotientGroup.lift_mk, classSplitAux_apply]
  ext
  · simp only [h, mul_inv_cancel_right]
    rfl
  · exact congrArg Subtype.val h

theorem classUnsplit_classSplit (x : IdeleClassGroup (𝓞 K) K) : classUnsplit K (classSplit K x) = x := by
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [classSplit, QuotientGroup.lift_mk, classSplitAux_apply]
    show ((x * (weilZ K (normRoot K x))⁻¹ : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K) *
      ((weilZ K (normRoot K x) : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K) = x
    rw [← QuotientGroup.mk_mul, inv_mul_cancel_right]

variable (K) in
/-- **Weil, IV.§4, Theorem 6, last assertion** (number field case): $k_{\mathbb A}^\times/k^\times$ is the direct product
of the compact group $k^1/k^\times$ (NumberFieldKB `IdeleClassGroup.isCompact_normOne`) and of a group isomorphic to
$\mathbb R_+^\times$, the image of $M$: $(c,\lambda)\mapsto c\cdot Z(\lambda)$ is an isomorphism of topological groups
$(k^1/k^\times)\times\mathbb R_+^\times\to k_{\mathbb A}^\times/k^\times$. -/
@[kb "weil1973bnt" "Ch. IV, §4, Thm. 6 (p. 76), number field case, splitting"]
def weil_IV_4_thm6 :
    (IdeleClassGroup.normOne K × {t : ℝ // 0 < t}) ≃ₜ* IdeleClassGroup (𝓞 K) K where
  toFun := classUnsplit K
  invFun := classSplit K
  left_inv := classSplit_classUnsplit
  right_inv := classUnsplit_classSplit
  map_mul' := map_mul _
  continuous_toFun := by
    refine Continuous.mul (continuous_subtype_val.comp
      (@continuous_fst (IdeleClassGroup.normOne K) {t : ℝ // 0 < t} _ _)) ?_
    exact ((QuotientGroup.continuous_mk (N := IdeleGroup.principalSubgroup (𝓞 K) K)).comp
      continuous_weilZ).comp continuous_snd
  continuous_invFun := by
    refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    exact continuous_classSplitAux

@[simp] theorem weil_IV_4_thm6_apply (p : IdeleClassGroup.normOne K × {t : ℝ // 0 < t}) :
    weil_IV_4_thm6 K p = (p.1 : IdeleClassGroup (𝓞 K) K) * ((weilZ K p.2 : IdeleGroup (𝓞 K) K) :
      IdeleClassGroup (𝓞 K) K) := rfl

end NumberFieldKB.WeilBNT
