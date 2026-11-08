import NumberFieldKB.Pontryagin.Bochner
import NumberFieldKB.Pontryagin.Annihilator
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.UrysohnsLemma

/-!
# The characters of a locally compact commutative group separate points (Gelfand–Raikov), given Bochner

$G$ is a locally compact commutative Hausdorff group with a left-invariant measure $\mu$ that is finite on compact
sets (a Haar measure).

* `autocorr μ u` $=u\star\tilde u$, $x\mapsto\int u(y)\overline{u(x^{-1}y)}\,d\mu(y)$, for $u$ continuous with compact
  support: continuous (`continuous_autocorr`), positive definite (`isPositiveDefinite_autocorr`;
  $\sum_{i,j}c_i\overline{c_j}(u\star\tilde u)(v_iv_j^{-1})=\int|\sum_ic_i\overline{u(v_i^{-1}z)}|^2dz$), with
  $(u\star\tilde u)(1)=\|u\|_2^2$ and $(u\star\tilde u)(x)=0$ when $\operatorname{supp}u\cap x\operatorname{supp}u=\emptyset$.
* **`charactersSeparate_of_bochner`** (Gelfand–Raikov for commutative groups; Folland, *A Course in Abstract Harmonic
  Analysis*, 2nd ed., Theorem 4.19 / Corollary 4.20, there via Bochner's theorem as here): every $x\ne1$ has a character
  $\chi$ with $\chi(x)\ne1$. Proof: take $u\ge0$ supported in a neighbourhood $V$ of $1$ with $x\notin VV^{-1}$; by
  Bochner $u\star\tilde u=\int\chi\,d\mu_u$; if $\chi(x)=1$ for all $\chi$ then
  $0=(u\star\tilde u)(x)=\mu_u(G^*)=(u\star\tilde u)(1)>0$.
* Consequences: `dualEval_injective_of_bochner`; `doubleAnnihilator_eq_of_bochner` ($H^{**}=H$ for every closed
  subgroup); `pontryaginDuality_compact_of_bochner` (compact groups, without Peter–Weyl);
  `discreteTopology_of_compactSpace_dual` ($G^*$ compact ⇒ $G$ discrete).
-/

open MeasureTheory Topology ComplexConjugate ComplexOrder

noncomputable section

namespace NumberFieldKB.Pontryagin

universe u

section Autocorrelation

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- The autocorrelation $u\star\tilde u(x)=\int u(y)\overline{u(x^{-1}y)}\,d\mu(y)$. -/
def autocorr (μ : Measure G) (u : G → ℂ) (x : G) : ℂ := ∫ y, u y * conj (u (x⁻¹ * y)) ∂μ

variable {μ : Measure G} {u : G → ℂ}

lemma continuous_conj_comp {f : G → ℂ} (hf : Continuous f) : Continuous fun y => conj (f y) :=
  Complex.continuous_conj.comp hf

/-- The autocorrelation of a continuous compactly supported function is continuous. -/
theorem continuous_autocorr [IsFiniteMeasureOnCompacts μ] (hu : Continuous u) (hc : HasCompactSupport u) :
    Continuous (autocorr μ u) := by
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support (k := tsupport u) hc
  · exact (Continuous.continuousOn (by
      exact (hu.comp continuous_snd).mul
        (Complex.continuous_conj.comp (hu.comp (continuous_fst.inv.mul continuous_snd)))))
  · intro x y _ hy
    simp [image_eq_zero_of_notMem_tsupport hy]

lemma integrable_mul_conj_comp [IsFiniteMeasureOnCompacts μ] (hu : Continuous u) (hc : HasCompactSupport u)
    (a b : G) : Integrable (fun z => u (a * z) * conj (u (b * z))) μ := by
  have hc' : HasCompactSupport fun z => u (a * z) := by
    have := hc.comp_homeomorph (Homeomorph.mulLeft a)
    exact this
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hu.comp (continuous_const.mul continuous_id)).mul
      (Complex.continuous_conj.comp (hu.comp (continuous_const.mul continuous_id)))
  · exact hc'.mul_right

/-- **The autocorrelation is positive definite**: $\sum_{i,j}c_i\overline{c_j}(u\star\tilde u)(v_iv_j^{-1})
=\int|\sum_ic_i\overline{u(v_i^{-1}z)}|^2\,dz\ge0$. -/
theorem isPositiveDefinite_autocorr [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] (hu : Continuous u)
    (hc : HasCompactSupport u) : IsPositiveDefinite (autocorr μ u) := by
  intro n c v
  -- each value is `∫ u(v_j⁻¹ z) conj u(v_i⁻¹ z) dz`
  have hval : ∀ i j, autocorr μ u (v i * (v j)⁻¹) =
      ∫ z, u ((v j)⁻¹ * z) * conj (u ((v i)⁻¹ * z)) ∂μ := by
    intro i j
    unfold autocorr
    rw [← integral_mul_left_eq_self _ (v j)⁻¹]
    congr 1 with z
    congr 3
    rw [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel_comm]
  set S : G → ℂ := fun z => ∑ i, c i * conj (u ((v i)⁻¹ * z)) with hS
  have hsum : ∑ i, ∑ j, c i * conj (c j) * autocorr μ u (v i * (v j)⁻¹) = ∫ z, S z * conj (S z) ∂μ := by
    simp_rw [hval]
    have hint : ∀ i j, Integrable (fun z => c i * conj (c j) *
        (u ((v j)⁻¹ * z) * conj (u ((v i)⁻¹ * z)))) μ :=
      fun i j => (integrable_mul_conj_comp hu hc _ _).const_mul _
    simp_rw [← integral_const_mul]
    have e1 : ∀ i, ∑ j, ∫ z, c i * conj (c j) * (u ((v j)⁻¹ * z) * conj (u ((v i)⁻¹ * z))) ∂μ =
        ∫ z, ∑ j, c i * conj (c j) * (u ((v j)⁻¹ * z) * conj (u ((v i)⁻¹ * z))) ∂μ :=
      fun i => (integral_finsetSum _ (fun j _ => hint i j)).symm
    rw [Finset.sum_congr rfl (fun i _ => e1 i),
      ← integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    congr 1 with z
    simp only [hS, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum]
  have : ∀ z, S z * conj (S z) = ((‖S z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.mul_conj']; push_cast; rfl
  simp_rw [this, integral_complex_ofReal]
  exact Complex.zero_le_real.mpr (integral_nonneg fun _ => by positivity)

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
/-- The autocorrelation vanishes at $x$ when $u(y)u(x^{-1}y)=0$ for all $y$. -/
lemma autocorr_eq_zero {x : G} (h : ∀ y, u y = 0 ∨ u (x⁻¹ * y) = 0) : autocorr μ u x = 0 := by
  unfold autocorr
  have : (fun y => u y * conj (u (x⁻¹ * y))) = 0 := by
    funext y
    rcases h y with h | h <;> simp [h]
  rw [this]; simp

end Autocorrelation

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G]

/-- **A positive-definite bump at $1$**: for every neighbourhood $U$ of $1$ there is a continuous positive-definite
function $\varphi$ (an autocorrelation $u\star\tilde u$) with $\varphi(1)=c>0$ real and $\varphi=0$ off $U$. -/
theorem exists_posDef_bump {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ (φ : G → ℂ) (c : ℝ), Continuous φ ∧ IsPositiveDefinite φ ∧ 0 < c ∧ φ 1 = c ∧ ∀ x ∉ U, φ x = 0 := by
  let _ : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  -- a neighbourhood `W` of `1` with `W * W⁻¹ ⊆ U`
  obtain ⟨V, hVo, hV1, hVx⟩ := exists_open_nhds_one_split hU
  set W := V ∩ V⁻¹ with hW
  have hWo : IsOpen W := hVo.inter hVo.inv
  have hW1 : (1 : G) ∈ W := ⟨hV1, by simpa using hV1⟩
  have hWx : ∀ a ∈ W, ∀ b ∈ W, a * b⁻¹ ∈ U := by
    intro a ha b hb
    exact hVx a ha.1 b⁻¹ (by simpa using hb.2)
  -- a bump function supported in `W`
  obtain ⟨f, hf1, hfc, hfW, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    isCompact_singleton hWo (Set.singleton_subset_iff.mpr hW1)
  set u : G → ℂ := fun y => ((f y : ℝ) : ℂ) with hu
  have huc : Continuous u := Complex.continuous_ofReal.comp f.continuous
  have hus : HasCompactSupport u := by
    refine HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) ?_ Complex.ofReal_zero
    exact hfc
  refine ⟨autocorr μ u, ∫ y, f y * f y ∂μ, continuous_autocorr huc hus, isPositiveDefinite_autocorr huc hus,
    ?_, ?_, ?_⟩
  · refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (f.continuous.mul f.continuous) (show HasCompactSupport f from hfc).mul_left
      (fun y => mul_self_nonneg _) ?_
    have : f 1 = 1 := hf1 rfl
    simp [this]
  · rw [← integral_complex_ofReal]
    unfold autocorr
    congr 1 with y
    simp [hu, Complex.conj_ofReal]
  · intro x hx
    apply autocorr_eq_zero
    intro y
    by_contra hy
    push Not at hy
    have hy1 : y ∈ W := hfW (subset_tsupport _ (fun h => hy.1 (by simp [hu, h])))
    have hy2 : x⁻¹ * y ∈ W := hfW (subset_tsupport _ (fun h => hy.2 (by simp [hu, h])))
    exact hx (by simpa using hWx y hy1 (x⁻¹ * y) hy2)

/-- **The characters of a locally compact commutative Hausdorff group separate points** (Gelfand–Raikov; Folland,
Corollary 4.20), given Bochner's theorem. -/
theorem charactersSeparate_of_bochner (hB : BochnerTheorem.{u}) : CharactersSeparate G := by
  intro x hx
  let _ : MeasurableSpace (PontryaginDual G) := borel _
  have : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨φ, c, hφc, hφpd, hc, hφ1, hφU⟩ :=
    exists_posDef_bump (isOpen_compl_singleton.mem_nhds (Ne.symm hx : (1 : G) ≠ x))
  obtain ⟨ν, -, -, hν⟩ := hB.exists_measure G φ hφpd hφc.continuousAt
  by_contra hall
  push Not at hall
  -- `φ x = φ 1` since every character is trivial at `x`
  have h1 : φ x = φ 1 := by
    rw [← hν, ← hν]
    unfold fourierStieltjes
    congr 1 with χ
    rw [hall χ, map_one]
  rw [hφU x (by simp), hφ1] at h1
  have := congrArg Complex.re h1
  simp only [Complex.zero_re, Complex.ofReal_re] at this
  linarith

/-- The canonical map $G\to G^{**}$ is injective, given Bochner's theorem. -/
theorem dualEval_injective_of_bochner (hB : BochnerTheorem.{u}) : Function.Injective (dualEval G) :=
  dualEval_injective_iff.mpr (charactersSeparate_of_bochner hB)

omit [T2Space G] in
/-- **Weil II.§5, p. 38**: for every closed subgroup $H$, the subgroup of $G$ associated with $H^*$ is $H$ itself,
given Bochner's theorem. -/
theorem doubleAnnihilator_eq_of_bochner (hB : BochnerTheorem.{u}) (H : Subgroup G) [IsClosed (H : Set G)] :
    {g : G | ∀ χ ∈ annihilator H, χ g = 1} = H :=
  doubleAnnihilator_eq H (charactersSeparate_of_bochner hB)

end NumberFieldKB.Pontryagin
