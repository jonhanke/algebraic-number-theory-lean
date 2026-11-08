import NumberFieldKB.Pontryagin.GelfandRaikov
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.LocallyClosed

/-!
# The canonical map $G\to G^{**}$ is a closed embedding, given Bochner

$G$ is a locally compact commutative Hausdorff group.

* `exists_isCompact_of_mem_nhds`: for every neighbourhood $U$ of $1$ there is a compact $K\subset G^*$ such that
  $|\chi(x)-1|<1/4$ for all $\chi\in K$ forces $x\in U$ (given Bochner). Proof: Bochner's measure $\nu$ of a
  positive-definite bump $\varphi$ at $1$ (`exists_posDef_bump`) is inner regular, so $\nu(G^*\setminus K)<\varphi(1)/4$
  for a compact $K$; then $|\varphi(x)-\varphi(1)|<\varphi(1)$, so $\varphi(x)\ne0$ and $x\in U$.
* **`isInducing_dualEval`**: $G$ carries the topology induced from $G^{**}$ (Folland, *A Course in Abstract Harmonic
  Analysis*, 2nd ed., proof of Theorem 4.32, first step).
* **`isClosedEmbedding_dualEval`**: $G\to G^{**}$ is a closed embedding (a locally compact subgroup of a Hausdorff group
  is closed).

What remains of the duality theorem is the surjectivity, equivalently (by the above) the density of the image
(`pontryaginDualityStatement_of_denseRange`).
-/

open MeasureTheory Topology Filter

noncomputable section

namespace NumberFieldKB.Pontryagin

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G]

/-- The value of the Fourier–Stieltjes transform at $1$ is the total mass. -/
lemma fourierStieltjes_one [MeasurableSpace (PontryaginDual G)] (ν : Measure (PontryaginDual G)) :
    fourierStieltjes ν (1 : G) = ((ν.real Set.univ : ℝ) : ℂ) := by
  simp [fourierStieltjes, map_one]

lemma continuous_apply_dual (x : G) : Continuous fun χ : PontryaginDual G => ((χ x : Circle) : ℂ) :=
  continuous_subtype_val.comp (dualEval G x).continuous

/-- **Neighbourhoods of $1$ come from compact sets of characters** (given Bochner). -/
theorem exists_isCompact_of_mem_nhds (hB : BochnerTheorem.{u}) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : Set (PontryaginDual G), IsCompact K ∧
      ∀ x : G, (∀ χ ∈ K, ‖((χ x : Circle) : ℂ) - 1‖ < 1 / 4) → x ∈ U := by
  let _ : MeasurableSpace (PontryaginDual G) := borel _
  have : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨φ, c, hφc, hφpd, hc, hφ1, hφU⟩ := exists_posDef_bump hU
  obtain ⟨ν, hνf, hνr, hν⟩ := hB.exists_measure G φ hφpd hφc.continuousAt
  have hmass : ν.real Set.univ = c := by
    have := hν 1
    rw [fourierStieltjes_one, hφ1] at this
    exact_mod_cast this
  -- a compact set carrying all but `c / 4` of the mass
  obtain ⟨K, -, hK, hνK⟩ := MeasurableSet.univ.exists_lt_isCompact (μ := ν)
    (r := ENNReal.ofReal (3 * c / 4)) (by
      rw [← ofReal_measureReal (measure_ne_top ν _), hmass]
      exact ENNReal.ofReal_lt_ofReal_iff hc |>.mpr (by linarith))
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hνK' : 3 * c / 4 < ν.real K := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (measure_ne_top ν K)).mp hνK
    exact this
  have hcompl : ν.real Kᶜ < c / 4 := by
    have := measureReal_add_measureReal_compl (μ := ν) hKm
    rw [hmass] at this
    linarith
  refine ⟨K, hK, fun x hx => ?_⟩
  by_contra hxU
  have h0 := hφU x hxU
  -- `|φ x - φ 1| ≤ ∫ |χ x - χ 1| dν < c`
  have hint : ∀ y : G, Integrable (fun χ : PontryaginDual G => ((χ y : Circle) : ℂ)) ν := fun y =>
    Integrable.of_bound (continuous_apply_dual y).aestronglyMeasurable 1
      (Eventually.of_forall fun χ => by simp)
  have hg : Integrable (fun χ : PontryaginDual G => 1 / 4 + Kᶜ.indicator (fun _ => (2 : ℝ)) χ) ν :=
    (integrable_const _).add ((integrable_const _).indicator hKm.compl)
  have hb : ‖φ x - φ 1‖ ≤ c / 4 + 2 * ν.real Kᶜ := by
    rw [← hν x, ← hν 1]
    unfold fourierStieltjes
    rw [← integral_sub (hint x) (hint 1)]
    refine (norm_integral_le_of_norm_le hg (Eventually.of_forall fun χ => ?_)).trans_eq ?_
    · by_cases hχ : χ ∈ K
      · rw [Set.indicator_of_notMem (by simpa using hχ), add_zero]
        have := hx χ hχ
        rw [map_one, Circle.coe_one]
        exact this.le
      · rw [Set.indicator_of_mem (show χ ∈ Kᶜ from hχ)]
        calc ‖((χ x : Circle) : ℂ) - ((χ 1 : Circle) : ℂ)‖
            ≤ ‖((χ x : Circle) : ℂ)‖ + ‖((χ 1 : Circle) : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by simp; norm_num
          _ ≤ 1 / 4 + 2 := by norm_num
    · rw [integral_add (integrable_const _) ((integrable_const _).indicator hKm.compl),
        integral_const, integral_indicator_const _ hKm.compl, hmass]
      simp only [smul_eq_mul]
      ring
  rw [h0, hφ1, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at hb
  linarith

/-- **$G$ carries the topology induced from $G^{**}$** (given Bochner). -/
theorem isInducing_dualEval (hB : BochnerTheorem.{u}) : IsInducing (dualEval G) := by
  rw [IsTopologicalGroup.isInducing_iff_nhds_one]
  refine le_antisymm ?_ fun U hU => ?_
  · have h : Tendsto (dualEval G) (𝓝 1) (𝓝 (dualEval G 1)) := (dualEval G).continuous.tendsto (1 : G)
    rw [show dualEval G 1 = 1 from map_one _] at h
    exact h.le_comap
  obtain ⟨K, hK, hKU⟩ := exists_isCompact_of_mem_nhds hB hU
  set S : Set Circle := {z | ‖(z : ℂ) - 1‖ < 1 / 4}
  have hS : IsOpen S := isOpen_lt (continuous_subtype_val.sub continuous_const).norm continuous_const
  set N : Set (PontryaginDual (PontryaginDual G)) :=
    (fun ω : PontryaginDual (PontryaginDual G) => (ω : PontryaginDual G →ₜ* Circle).toContinuousMap) ⁻¹'
      {f : C(PontryaginDual G, Circle) | Set.MapsTo f K S}
  have hN : IsOpen N := (ContinuousMap.isOpen_setOfPred_mapsTo hK hS).preimage
    (ContinuousMonoidHom.isInducing_toContinuousMap _ Circle).continuous
  have h1N : (1 : PontryaginDual (PontryaginDual G)) ∈ N := by
    intro χ _
    show ‖(((1 : PontryaginDual (PontryaginDual G)) χ : Circle) : ℂ) - 1‖ < 1 / 4
    simp
  refine Filter.mem_comap.mpr ⟨N, hN.mem_nhds h1N, fun x hx => hKU x fun χ hχ => ?_⟩
  exact hx hχ

/-- **$G\to G^{**}$ is a closed embedding** (given Bochner). -/
theorem isClosedEmbedding_dualEval (hB : BochnerTheorem.{u}) : IsClosedEmbedding (dualEval G) := by
  have hind := isInducing_dualEval (G := G) hB
  refine ⟨⟨hind, dualEval_injective_of_bochner hB⟩, ?_⟩
  let H : Subgroup (PontryaginDual (PontryaginDual G)) := (dualEval G).toMonoidHom.range
  have hH : (H : Set (PontryaginDual (PontryaginDual G))) = Set.range (dualEval G) := rfl
  rw [← hH]
  refine H.isClosed_of_isLocallyClosedAt H.one_mem (isLocallyClosedAt_iff_exists_inter_closure_subset.mpr ?_)
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  rw [IsTopologicalGroup.isInducing_iff_nhds_one.mp hind] at hC1
  obtain ⟨O', hO', hO'C⟩ := Filter.mem_comap.mp hC1
  refine ⟨interior O', interior_mem_nhds.mpr hO', ?_⟩
  have hsub : interior O' ∩ (H : Set _) ⊆ dualEval G '' C := by
    rintro ω ⟨hω, x, rfl⟩
    exact ⟨x, hO'C (show dualEval G x ∈ O' from interior_subset hω), rfl⟩
  have hCc : IsClosed (dualEval G '' C) := (hC.image (dualEval G).continuous).isClosed
  calc interior O' ∩ closure (H : Set _) ⊆ closure (interior O' ∩ (H : Set _)) :=
        isOpen_interior.inter_closure
    _ ⊆ dualEval G '' C := closure_minimal hsub hCc
    _ ⊆ H := by rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩

/-- **Reduction of the duality theorem to the density of the image** (given Bochner): if $G\to G^{**}$ has dense
image, it is an isomorphism of topological groups. -/
theorem pontryaginDualityStatement_of_denseRange (hB : BochnerTheorem.{u}) (hd : DenseRange (dualEval G)) :
    PontryaginDualityStatement G := by
  have he := isClosedEmbedding_dualEval (G := G) hB
  have hr : Set.range (dualEval G) = Set.univ := by
    rw [← he.isClosed_range.closure_eq]; exact hd.closure_range
  have hs : Function.Surjective (dualEval G) := Set.range_eq_univ.mp hr
  exact pontryaginDualityStatement_of_bijective_of_isOpenMap ⟨he.injective, hs⟩
    (he.isInducing.isOpenMap (by rw [hr]; exact isOpen_univ))

omit [T2Space G] in
/-- The image of $G\to G^{**}$ is dense if every character of $G^{**}$ trivial on it is trivial (given Bochner,
which supplies the separation of points of $G^{**}/\overline{G}$). -/
theorem denseRange_dualEval_of_annihilator (hB : BochnerTheorem.{u})
    (h : ∀ Ψ : PontryaginDual (PontryaginDual (PontryaginDual G)), (∀ x : G, Ψ (dualEval G x) = 1) → Ψ = 1) :
    DenseRange (dualEval G) := by
  let H : Subgroup (PontryaginDual (PontryaginDual G)) := (dualEval G).toMonoidHom.range.topologicalClosure
  have hHc : IsClosed (H : Set (PontryaginDual (PontryaginDual G))) :=
    (dualEval G).toMonoidHom.range.isClosed_topologicalClosure
  have : IsClosed (H : Set (PontryaginDual (PontryaginDual G))) := hHc
  intro ω
  by_contra hω
  have hωH : ω ∉ H := by
    rwa [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
  have hq : (QuotientGroup.mk ω : PontryaginDual (PontryaginDual G) ⧸ H) ≠ 1 := by
    rwa [ne_eq, QuotientGroup.eq_one_iff]
  obtain ⟨ψ, hψ⟩ := charactersSeparate_of_bochner hB _ hq
  have h1 := h (quotientDualMap H ψ) fun x => by
    rw [quotientDualMap_apply]
    have : (QuotientGroup.mk (dualEval G x) : PontryaginDual (PontryaginDual G) ⧸ H) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.le_topologicalClosure _ ⟨x, rfl⟩)
    rw [this, map_one]
  apply hψ
  have := congrArg (fun Ψ : PontryaginDual (PontryaginDual (PontryaginDual G)) => Ψ ω) h1
  simpa [quotientDualMap_apply] using this

end NumberFieldKB.Pontryagin
