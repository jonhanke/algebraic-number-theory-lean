import NumberFieldKB.WeilBNT.AdeleBoxes
import QuadFormsKB.Tamagawa.Measure.Weil.SL2Approx

/-!
# Weil, *Basic Number Theory*, V.§2, Cor. 1 of Theorem 1: $\mathfrak r$ is dense in $\prod_v r_v$

$k$ is a number field, $\mathfrak r$ its ring of integers, $r_v$ the ring of integers of $k_v$ at a finite place $v$.

* **`weil_V_2_cor1`** (Weil, p. 83): the diagonal image $\psi(\mathfrak r)$ is dense in $\prod_v r_v$ (product over all
  finite places, product topology);
* **`weil_V_2_cor1_partial`**: the same in every partial product $\prod_{v\in T}r_v$;
* **`weil_V_2_cor1_closure`**: $r_v$ is the closure of $\mathfrak r$ in $k_v$.
* **`weil_V_2_cor2`** (Cor. 2, p. 83): the maximal order of a finite extension $k'$ is the integral closure of
  $\mathfrak r$ in $k'$.

Weil derives this from Lemma 1 and Theorem 1 of V.§2 (the image of $k$ in $k_{\mathbb A}$). Here the density of $k$ in the
finite adeles (QuadFormsKB `denseRange_algebraMap_finiteAdele`, strong approximation away from the infinite places) is
combined with the fact that $\prod_vr_v$ is open in the finite adeles (Mathlib `isOpenEmbedding_structureMap`) and that
$k\cap\prod_vr_v=\mathfrak r$.
-/

open IsDedekindDomain NumberField Filter Topology

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

variable (K) in
/-- Weil's $\psi$: the diagonal map $\mathfrak r\to\prod_v r_v$ over all finite places. -/
def psiIntegers (a : 𝓞 K) : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K :=
  fun v => algebraMap (𝓞 K) (v.adicCompletionIntegers K) a

/-- **Weil, V.§2, Cor. 1 of Thm. 1** (p. 83): $\psi(\mathfrak r)$ is dense in $\prod_v r_v$. -/
@[kb "weil1973bnt" "Ch. V, §2, Cor. 1 of Thm. 1 (p. 83), density in the full product"]
theorem weil_V_2_cor1 : DenseRange (psiIntegers K) := by
  have hopen : ∀ v : HeightOneSpectrum (𝓞 K), IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun _ => Valued.isOpen_valuationSubring _
  set ι := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) cofinite with hι
  have hemb : IsOpenEmbedding ι := RestrictedProduct.isOpenEmbedding_structureMap hopen
  rw [DenseRange, dense_iff_inter_open]
  intro U hU ⟨u₀, hu₀⟩
  have hdense := QuadFormsKB.Tamagawa.Measure.Weil.denseRange_algebraMap_finiteAdele (F := K)
  obtain ⟨_, ⟨u, hu, hux⟩, x, rfl⟩ :=
    hdense.inter_open_nonempty (ι '' U) (hemb.isOpenMap U hU) ⟨ι u₀, u₀, hu₀, rfl⟩
  have hcomp : ∀ v : HeightOneSpectrum (𝓞 K), ((u v : v.adicCompletion K)) = (x : v.adicCompletion K) := fun v =>
    congrArg (fun a : FiniteAdeleRing (𝓞 K) K => a v) hux
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K x fun v => by
    have h : Valued.v ((x : K) : HeightOneSpectrum.adicCompletion K v) ≤ 1 := by
      have h0 := (u v).2
      rw [hcomp v] at h0
      exact h0
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  refine ⟨u, hu, r, ?_⟩
  funext v
  apply Subtype.ext
  change ((algebraMap (𝓞 K) K r : K) : v.adicCompletion K) = _
  rw [hr, hcomp v]

/-- **Weil, V.§2, Cor. 1 of Thm. 1**: $\psi(\mathfrak r)$ is dense in every partial product $\prod_{v\in T}r_v$. -/
@[kb "weil1973bnt" "Ch. V, §2, Cor. 1 of Thm. 1 (p. 83), partial products"]
theorem weil_V_2_cor1_partial (T : Set (HeightOneSpectrum (𝓞 K))) :
    DenseRange (fun a : 𝓞 K => fun v : T => psiIntegers K a v.1) := by
  have hproj : Continuous (fun y : (∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) =>
      fun v : T => y v.1) := continuous_pi fun v => continuous_apply v.1
  have hsurj : Function.Surjective (fun y : (∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) =>
      fun v : T => y v.1) := by
    classical
    intro z
    exact ⟨fun v => if hv : v ∈ T then z ⟨v, hv⟩ else 0, funext fun v => by simp [v.2]⟩
  exact hsurj.denseRange.comp weil_V_2_cor1 hproj

/-- **Weil, V.§2, Cor. 1 of Thm. 1**: $r_v$ is the closure of $\mathfrak r$ in $k_v$. -/
@[kb "weil1973bnt" "Ch. V, §2, Cor. 1 of Thm. 1 (p. 83), closure in one completion"]
theorem weil_V_2_cor1_closure (v : HeightOneSpectrum (𝓞 K)) :
    closure (Set.range fun a : 𝓞 K => ((a : K) : v.adicCompletion K)) =
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  have hclosed : IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Valued.isClosed_valuationSubring _
  apply le_antisymm
  · refine closure_minimal ?_ hclosed
    rintro _ ⟨a, rfl⟩
    exact (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a).2
  · -- the image of $\mathfrak r$ is dense in $r_v$: project the density in $\prod_w r_w$
    intro y hy
    classical
    set p : (∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K) → v.adicCompletion K :=
      fun z => (z v : v.adicCompletion K)
    have hp : Continuous p := continuous_subtype_val.comp (continuous_apply v)
    have hz : p (Pi.single v ⟨y, hy⟩) = y := by simp [p]
    have h := mem_closure_image hp.continuousAt (weil_V_2_cor1 (K := K) (Pi.single v ⟨y, hy⟩))
    rw [← Set.range_comp, hz] at h
    exact h

omit [NumberField K] in
/-- **Weil, V.§2, Cor. 2 of Theorem 1** (p. 83): for a finite extension $k'/k$ of number fields, the maximal order
$\mathfrak r'$ of $k'$ is the integral closure in $k'$ of the maximal order $\mathfrak r$ of $k$. (Weil: $\mathfrak r'$
is the integral closure of $\mathbb Z$ in $k'$, and an element integral over $\mathfrak r$ is integral over
$\mathbb Z$; this is Mathlib's instance `RingOfIntegers.instIsIntegralClosure`.) -/
@[kb "weil1973bnt" "Ch. V, §2, Cor. 2 of Thm. 1 (p. 83)"]
theorem weil_V_2_cor2 (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] :
    IsIntegralClosure (𝓞 K') (𝓞 K) K' :=
  RingOfIntegers.instIsIntegralClosure K K'

end NumberFieldKB.WeilBNT

end
