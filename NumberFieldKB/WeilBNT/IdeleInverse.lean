import NumberFieldKB.WeilBNT.AdeleBoxes
import NumberFieldKB.MilneEC.Ch4Cohomology
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int

/-!
# Weil, *Basic Number Theory*, Chapter IV, §3, text p. 71: inversion is not continuous for the adelic topology

$k$ is a number field. Weil (IV.§3, p. 71) observes, before Definition 2, that already for the algebra $\mathcal A=k$
the map $x\mapsto x^{-1}$ is not continuous on the group $k_{\mathbb A}^\times$ of invertible adeles for the topology
induced by that of $k_{\mathbb A}$; this is why the idele group gets the coarsest topology making both the injection
into $k_{\mathbb A}$ and $x\mapsto x^{-1}$ continuous (Mathlib's units topology on `IdeleGroup (𝓞 K) K`).

* **`weil_IV_3_text71`**: `Ring.inverse` is not continuous on the set of units of `AdeleRing (𝓞 K) K` (subspace
  topology).

*Proof.* For a finite place $v$ let $a^{(v)}$ be the idele with component a uniformizer $\pi_v\in k$ at $v$ and $1$
elsewhere (`IdeleGroup.ofAdicCompletion`). As $v$ runs through the finite places (cofinite filter; there are infinitely
many, `NumberFieldKB.MilneEC.infinite_heightOneSpectrum`), $a^{(v)}\to1$ in $k_{\mathbb A}$: in the open subring
$\prod_w r_w$ with its product topology, each coordinate is eventually $1$. But $(a^{(v)})^{-1}$ has the component
$\pi_v^{-1}\notin r_v$, so it never lies in the open neighbourhood $k_\infty\times\prod_w r_w$ of $1$
(`AdeleRing.box K ∅`, open by `weil_IV_1_prop1`).
-/

open IsDedekindDomain NumberField Filter Topology

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

/-- **Weil, IV.§3, text p. 71** (case $\mathcal A=k$, $k$ a number field): $x\mapsto x^{-1}$ is not continuous on the
invertible adeles for the topology induced by $k_{\mathbb A}$. -/
@[kb "weil1973bnt" "Ch. IV, §3, text p. 71 (inversion not continuous for the adelic topology), number field case"]
theorem weil_IV_3_text71 :
    ¬ ContinuousOn (Ring.inverse : AdeleRing (𝓞 K) K → AdeleRing (𝓞 K) K) {x | IsUnit x} := by
  classical
  intro hcont
  have : Infinite (HeightOneSpectrum (𝓞 K)) := NumberFieldKB.MilneEC.infinite_heightOneSpectrum K
  choose π hπ using fun v : HeightOneSpectrum (𝓞 K) => v.valuation_exists_uniformizer K
  let u : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K := fun v => ((π v : K) : v.adicCompletion K)
  have hu : ∀ v, Valued.v (u v) = WithZero.exp (-1 : ℤ) := fun v => by
    simp only [u]
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hu0 : ∀ v, u v ≠ 0 := fun v h => by
    have := hu v
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hule : ∀ v, u v ∈ v.adicCompletionIntegers K := fun v => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
    exact WithZero.exp_le_exp.mpr (by norm_num)
  have huinv : ∀ v, (u v)⁻¹ ∉ v.adicCompletionIntegers K := fun v => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu, not_le]
    rw [← WithZero.exp_neg]
    simp only [neg_neg]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  let a : HeightOneSpectrum (𝓞 K) → IdeleGroup (𝓞 K) K := fun v =>
    IdeleGroup.ofAdicCompletion (𝓞 K) K v (Units.mk0 (u v) (hu0 v))
  have ha_fst : ∀ v, ((a v : AdeleRing (𝓞 K) K)).1 = 1 := fun v => rfl
  have ha_snd : ∀ v w, ((a v : AdeleRing (𝓞 K) K)).2 w = Pi.mulSingle v (u v) w := fun v w => by
    simp [a, FiniteAdeleRing.ofAdicCompletion]
    rfl
  have hinv_snd : ∀ v w, (Ring.inverse (a v : AdeleRing (𝓞 K) K)).2 w = Pi.mulSingle v (u v)⁻¹ w := fun v w => by
    rw [Ring.inverse_unit]
    simp [a, FiniteAdeleRing.ofAdicCompletion]
    rfl
  let b : HeightOneSpectrum (𝓞 K) → Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K :=
    fun v => Pi.mulSingle v ⟨u v, hule v⟩
  have hb : ∀ v w, (RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w => w.adicCompletionIntegers K) cofinite (b v) : FiniteAdeleRing (𝓞 K) K) w
        = Pi.mulSingle v (u v) w := fun v w => by
    by_cases h : w = v
    · subst h
      simp [b]
    · simp [b, h]
  have hbt : Tendsto b cofinite (𝓝 1) := by
    refine tendsto_pi_nhds.2 fun w => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_cofinite_ne w] with v hv
    simp [b, hv.symm]
  have hcm : Continuous (RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w => w.adicCompletionIntegers K) cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have hT : Tendsto (fun v => (a v : AdeleRing (𝓞 K) K)) cofinite (𝓝 1) := by
    have h1 := (tendsto_const_nhds (x := (1 : InfiniteAdeleRing K))).prodMk_nhds
      ((hcm.tendsto 1).comp hbt)
    have e : ∀ v, (a v : AdeleRing (𝓞 K) K) = (1, RestrictedProduct.structureMap
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
        (fun w => w.adicCompletionIntegers K) cofinite (b v)) := fun v =>
      Prod.ext (ha_fst v) (by apply RestrictedProduct.ext; intro w; exact (ha_snd v w).trans (hb v w).symm)
    simp_rw [e]
    exact h1
  have hU : IsOpen (AdeleRing.box K ∅ : Set (AdeleRing (𝓞 K) K)) := (weil_IV_1_prop1 (K := K)).1 ∅
  have h1U : (1 : AdeleRing (𝓞 K) K) ∈ (AdeleRing.box K ∅ : Set (AdeleRing (𝓞 K) K)) := one_mem _
  have hcw : ContinuousWithinAt Ring.inverse {x : AdeleRing (𝓞 K) K | IsUnit x} 1 :=
    hcont 1 isUnit_one
  have hinv1 : (Ring.inverse (1 : AdeleRing (𝓞 K) K)) = 1 := Ring.inverse_one _
  have hT' : Tendsto (fun v => (a v : AdeleRing (𝓞 K) K)) cofinite (𝓝[{x | IsUnit x}] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨hT, Eventually.of_forall fun v => (a v).isUnit⟩
  have hfin : Tendsto (fun v => Ring.inverse (a v : AdeleRing (𝓞 K) K)) cofinite (𝓝 1) := by
    have := hcw.tendsto.comp hT'
    rw [hinv1] at this
    exact this
  obtain ⟨v, hv⟩ := (hfin.eventually (hU.mem_nhds h1U)).exists
  have := hv v (by simp)
  change (Ring.inverse (a v : AdeleRing (𝓞 K) K)).2 v ∈ _ at this
  rw [hinv_snd, Pi.mulSingle_eq_same] at this
  exact huinv v this

end NumberFieldKB.WeilBNT
