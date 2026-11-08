import NumberFieldKB.Pontryagin.Annihilator
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Bruhat functions for a discrete cocompact subgroup

$G$ is a locally compact commutative Hausdorff group and $\Gamma\subset G$ a discrete subgroup with $G/\Gamma$ compact
(Weil, *Basic Number Theory*, VII.§2, p. 105). A **Bruhat function** for $\Gamma$ is a continuous, non-negative,
compactly supported $h$ on $G$ with $\sum_{\gamma\in\Gamma}h(g\gamma)=1$ for every $g$ (F. Bruhat, *Distributions sur
un groupe localement compact et applications à l'étude des représentations des groupes p-adiques*, Bull. Soc. Math.
France 89 (1961), §8; G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., Lemma 2.47). It is the tool
that turns integrals over $G/\Gamma$ into integrals over $G$, used in `NumberFieldKB.Pontryagin.QuotientMeasure`.

## Main declarations
* `finite_setOf_mul_mem`: for compact $K,L\subset G$, only finitely many $\gamma\in\Gamma$ have
  $K\gamma\cap L\neq\emptyset$.
* `IsBruhat Γ h`, `exists_isBruhat`: Bruhat functions exist when $G/\Gamma$ is compact.
* `periodize Γ f`: the function $\Gamma g\mapsto\sum_{\gamma}f(g\gamma)$ on $G/\Gamma$.
* `tendstoUniformlyOn_sum_of_hasCompactSupport`: for $f$ with compact support the series $\sum_\gamma f(g\gamma)$
  converges uniformly on compact sets (it is locally finite).
-/

open Topology Filter Set

noncomputable section

namespace NumberFieldKB.Pontryagin

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ]

omit [LocallyCompactSpace G] in
open scoped Pointwise in
/-- For compact $K,L\subset G$, only finitely many $\gamma\in\Gamma$ satisfy $k\gamma\in L$ for some $k\in K$. -/
theorem finite_setOf_mul_mem {K L : Set G} (hK : IsCompact K) (hL : IsCompact L) :
    {γ : Γ | ∃ k ∈ K, k * (γ : G) ∈ L}.Finite := by
  have : IsClosed (Γ : Set G) := inferInstance
  have hc : IsCompact (K⁻¹ * L : Set G) := hK.inv.mul hL
  have hemb : Topology.IsClosedEmbedding (Subtype.val : Γ → G) := this.isClosedEmbedding_subtypeVal
  have hfin : (Subtype.val ⁻¹' (K⁻¹ * L) : Set Γ).Finite :=
    (hemb.isCompact_preimage hc).finite_of_discrete
  refine hfin.subset ?_
  rintro γ ⟨k, hk, hkL⟩
  exact ⟨k⁻¹, by simpa using hk, _, hkL, by simp⟩

/-- A **Bruhat function** for $\Gamma$: continuous, non-negative, compactly supported, with
$\sum_{\gamma\in\Gamma}h(g\gamma)=1$ for every $g\in G$. -/
structure IsBruhat (h : G → ℝ) : Prop where
  continuous : Continuous h
  hasCompactSupport : HasCompactSupport h
  nonneg : ∀ g, 0 ≤ h g
  tsum_eq_one : ∀ g, ∑' γ : Γ, h (g * γ) = 1

omit [LocallyCompactSpace G] in
/-- The translates $\gamma\mapsto f(g\gamma)$ of a compactly supported $f$ have finite support. -/
theorem finite_support_mul {E : Type*} [Zero E] {f : G → E} (hf : HasCompactSupport f) (g : G) :
    (Function.support fun γ : Γ => f (g * γ)).Finite := by
  refine (finite_setOf_mul_mem Γ (isCompact_singleton (x := g)) hf).subset ?_
  intro γ hγ
  exact ⟨g, rfl, subset_tsupport _ hγ⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ] in
/-- The sum $\sum_{\gamma\in\Gamma}f(g\gamma)$ is unchanged when $g$ is replaced by $g\gamma_0$, $\gamma_0\in\Gamma$. -/
theorem tsum_mul_mul_eq {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (f : G → E) (g : G) (γ₀ : Γ) :
    ∑' γ : Γ, f (g * γ₀ * γ) = ∑' γ : Γ, f (g * γ) := by
  rw [← (Equiv.mulLeft γ₀).tsum_eq (fun γ : Γ => f (g * γ))]
  refine tsum_congr fun γ => ?_
  simp [mul_assoc]

/-- The **periodization** of $f$: the function $\Gamma g\mapsto\sum_{\gamma\in\Gamma}f(g\gamma)$ on $G/\Gamma$. -/
def periodize {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (f : G → E) : G ⧸ Γ → E :=
  Quotient.lift (fun g : G => ∑' γ : Γ, f (g * γ)) fun a b hab => by
    obtain ⟨γ₀, rfl⟩ : ∃ γ₀ : Γ, b = a * γ₀ := by
      have := QuotientGroup.leftRel_apply.mp hab
      exact ⟨⟨a⁻¹ * b, this⟩, by simp⟩
    exact (tsum_mul_mul_eq Γ f a γ₀).symm

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ] in
@[simp]
theorem periodize_mk {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (f : G → E) (g : G) :
    periodize Γ f (g : G ⧸ Γ) = ∑' γ : Γ, f (g * γ) := rfl

omit [LocallyCompactSpace G] in
/-- For a compactly supported $f$, the partial sums of $\sum_\gamma f(g\gamma)$ converge uniformly on every compact
set (they are eventually constant there). -/
theorem tendstoUniformlyOn_sum_of_hasCompactSupport {E : Type*} [NormedAddCommGroup E] {f : G → E}
    (hf : HasCompactSupport f) {K : Set G} (hK : IsCompact K) :
    TendstoUniformlyOn (fun (s : Finset Γ) (g : G) => ∑ γ ∈ s, f (g * γ)) (fun g => ∑' γ : Γ, f (g * γ))
      atTop K := by
  have hfin := finite_setOf_mul_mem Γ hK hf
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_ge_atTop hfin.toFinset] with s hs g hg
  have : ∑' γ : Γ, f (g * γ) = ∑ γ ∈ s, f (g * γ) := by
    refine tsum_eq_sum fun γ hγ => ?_
    by_contra hne
    exact hγ (hs (by simpa using ⟨g, hg, subset_tsupport _ hne⟩))
  rw [this, dist_self]
  exact hε

/-- Helper: $g\mapsto\sum_\gamma f(g\gamma)$ is continuous for continuous compactly supported $f$. -/
private theorem continuous_tsum_mul {E : Type*} [NormedAddCommGroup E] {f : G → E} (hfc : Continuous f)
    (hf : HasCompactSupport f) : Continuous fun g : G => ∑' γ : Γ, f (g * γ) := by
  rw [continuous_iff_continuousAt]
  intro g
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds g
  have h := tendstoUniformlyOn_sum_of_hasCompactSupport Γ hf hKc
  have hco : ContinuousOn (fun g : G => ∑' γ : Γ, f (g * γ)) K :=
    h.continuousOn (Eventually.of_forall fun s =>
      (continuous_finsetSum _ fun γ _ => hfc.comp (continuous_id.mul continuous_const)).continuousOn).frequently
  exact hco.continuousAt hKn

/-- The periodization of a continuous compactly supported function is continuous. -/
theorem continuous_periodize {E : Type*} [NormedAddCommGroup E] {f : G → E} (hfc : Continuous f)
    (hf : HasCompactSupport f) : Continuous (periodize Γ f) := by
  exact ((QuotientGroup.isQuotientMap_mk Γ).continuous_iff).2 (continuous_tsum_mul Γ hfc hf)

/-- **Bruhat functions exist** for a discrete subgroup $\Gamma$ with $G/\Gamma$ compact. -/
theorem exists_isBruhat [CompactSpace (G ⧸ Γ)] : ∃ h : G → ℝ, IsBruhat Γ h := by
  have : IsClosed (Γ : Set G) := inferInstance
  obtain ⟨L, hLc, hL⟩ := exists_isCompact_image_eq Γ (isCompact_univ : IsCompact (Set.univ : Set (G ⧸ Γ)))
  obtain ⟨h0, h1, hsupp, -, hmem⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (X := G) hLc isOpen_univ (Set.subset_univ L)
  have hcs : HasCompactSupport (h0 : G → ℝ) := hsupp
  have h0nn : ∀ g, 0 ≤ h0 g := fun g => (hmem g).1
  set H : G → ℝ := fun g => ∑' γ : Γ, h0 (g * γ) with hH
  have hHc : Continuous H := continuous_tsum_mul Γ h0.continuous hcs
  have hHpos : ∀ g, 1 ≤ H g := by
    intro g
    have : (g : G ⧸ Γ) ∈ (QuotientGroup.mk : G → G ⧸ Γ) '' L := by rw [hL]; trivial
    obtain ⟨l, hl, hlg⟩ := this
    obtain ⟨γ, hγ⟩ : ∃ γ : Γ, l = g * γ := by
      have := QuotientGroup.leftRel_apply.mp (Quotient.exact hlg)
      exact ⟨⟨g⁻¹ * l, by simpa using Γ.inv_mem this⟩, by simp⟩
    have hsum : Summable fun γ : Γ => h0 (g * γ) :=
      summable_of_ne_finset_zero (s := (finite_support_mul Γ hcs g).toFinset) fun γ hγ => by simpa using hγ
    calc (1 : ℝ) = h0 (g * γ) := by rw [← hγ]; simpa using (h1 hl).symm
      _ ≤ H g := hsum.le_tsum γ (fun j _ => h0nn _)
  have hHne : ∀ g, H g ≠ 0 := fun g => by have := hHpos g; positivity
  refine ⟨fun g => h0 g / H g, ?_, ?_, ?_, ?_⟩
  · exact h0.continuous.div hHc hHne
  · exact hcs.mono (by
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h; exact hx (by simp [h]))
  · intro g
    exact div_nonneg (h0nn g) (by linarith [hHpos g])
  · intro g
    have e : ∀ γ : Γ, H (g * γ) = H g := fun γ => tsum_mul_mul_eq Γ h0 g γ
    simp only [e]
    rw [tsum_div_const]
    exact div_self (hHne g)

/-- A chosen Bruhat function. -/
def bruhat [CompactSpace (G ⧸ Γ)] : G → ℝ := Classical.choose (exists_isBruhat Γ)

theorem isBruhat_bruhat [CompactSpace (G ⧸ Γ)] : IsBruhat Γ (bruhat Γ) :=
  Classical.choose_spec (exists_isBruhat Γ)

end NumberFieldKB.Pontryagin
