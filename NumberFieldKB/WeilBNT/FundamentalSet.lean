import QuadFormsKB.Tamagawa.Measure.Weil.AdditiveAdele

/-!
# Weil, *Basic Number Theory*, Chapter V, §4, Proposition 6: a fundamental set for $k$ in $k_{\mathbb A}$

$k$ is a number field of degree $n$, $\mathfrak r$ its ring of integers, $\{e_1,\dots,e_n\}$ a set of generators of
$\mathfrak r$ which is a basis of $k$ over $\mathbb Q$ (here: a $\mathbb Z$-basis `b` of `𝓞 k`, indexed by any finite type;
Weil's $e_1,\dots,e_n$ are `b i`), and $\theta(u)=\sum_iu_ie_i$ the induced isomorphism $\mathbb R^n\to k_\infty$.

**Prop. 6** (p. 89): with $I=[0,1)$, the set $\theta(I^n)\times\prod_vr_v$ is a fundamental set of $k_{\mathbb A}$
modulo $k$: every adele is $x_0+\xi$ with $x_0$ in the set and $\xi\in k$, in exactly one way.

The adeles are QuadFormsKB's `Adeles k` $=k_\infty\times\mathbb A_f$ ($k_\infty$ = Mathlib's mixed space), $k$ embedded by
`diag`, and $\prod_vr_v$ is `OHat`. QuadFormsKB proves the same statement for one chosen basis
(`existsUnique_vadd_mem_fundDom`); here the basis is arbitrary, as in Weil. Weil's proof is followed: $k+k_\infty$ is dense
and $k_\infty\times\prod_vr_v$ is open, so $x-\eta\in k_\infty\times\prod_vr_v$ for some $\eta\in k$, unique up to
$\mathfrak r$ (QuadFormsKB `exists_sub_mem_OHat`, `algebraMap_mem_OHat_iff`); then the integer parts $a_i$ of the
coordinates $u_i$ of $y_\infty=\theta(u)$ are the unique correction.

* **`thetaBox b`**: $\theta(I^n)=\{\sum_iu_ie_i : 0\le u_i<1\}\subset k_\infty$;
* **`weil_V_4_prop6`**: every adele $x$ has exactly one $\xi\in k$ with $x-\xi\in\theta(I^n)\times\prod_vr_v$;
* **`measurableSet_thetaBox_prod`**: the set is measurable (Weil: "it is obviously measurable").
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory
open QuadFormsKB.Tamagawa.Measure.Weil
open scoped nonZeroDivisors Classical

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

/-- Weil's $\theta(I^n)$ for the $\mathbb Z$-basis $b=(e_i)$ of $\mathfrak r$: the half-open parallelotope
$\{\sum_iu_ie_i : 0\le u_i<1\}$ in $k_\infty$. -/
def thetaBox (b : Module.Basis ι ℤ (𝓞 F)) : Set (mixedSpace F) :=
  {y | ∃ u : ι → ℝ, (∀ i, u i ∈ Set.Ico (0 : ℝ) 1) ∧ y = ∑ i, u i • mixedEmbedding F (b i : F)}

local notation "L∞" => mixedEmbedding.idealLattice F (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

variable (F) in
/-- The $\mathbb Z$-linear isomorphism $\mathcal O_F\to\mathcal O_F$-lattice $L_\infty\subset F_\infty$. -/
def linfEquiv : 𝓞 F ≃ₗ[ℤ] L∞ :=
  LinearEquiv.ofBijective
    ({ toFun := fun a : 𝓞 F => (⟨mixedEmbedding F (a : F), (mem_Linf_iff _).mpr ⟨a, rfl⟩⟩ : L∞)
       map_add' := fun a b => Subtype.ext (by simp)
       map_smul' := fun n a => Subtype.ext (by simp) } : 𝓞 F →ₗ[ℤ] L∞)
    ⟨fun a b h => RingOfIntegers.coe_injective
        (mixedEmbedding_injective F (congrArg Subtype.val h)),
     fun y => by
      obtain ⟨a, ha⟩ := (mem_Linf_iff _).mp y.2
      exact ⟨a, Subtype.ext ha⟩⟩

theorem coe_linfEquiv (a : 𝓞 F) : ((linfEquiv F a : L∞) : mixedSpace F) = mixedEmbedding F (a : F) := rfl

/-- The $\mathbb R$-basis $\theta(e_i)$ of $F_\infty$. -/
def thetaBasis (b : Module.Basis ι ℤ (𝓞 F)) : Module.Basis ι ℝ (mixedSpace F) :=
  (b.map (linfEquiv F)).ofZLatticeBasis ℝ L∞

omit [Fintype ι] in
theorem thetaBasis_apply (b : Module.Basis ι ℤ (𝓞 F)) (i : ι) :
    thetaBasis b i = mixedEmbedding F (b i : F) := by
  simp [thetaBasis, coe_linfEquiv]

theorem thetaBox_eq (b : Module.Basis ι ℤ (𝓞 F)) :
    thetaBox b = ZSpan.fundamentalDomain (thetaBasis b) := by
  ext y
  simp only [thetaBox, ZSpan.mem_fundamentalDomain]
  change (∃ u : ι → ℝ, _) ↔ _
  constructor
  · rintro ⟨u, hu, rfl⟩ i
    have : (∑ i, u i • mixedEmbedding F (b i : F)) = (thetaBasis b).equivFun.symm u := by
      rw [Module.Basis.equivFun_symm_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [thetaBasis_apply]
    rw [this]
    have h := (thetaBasis b).equivFun.apply_symm_apply u
    exact (congrFun h i ▸ hu i : _)
  · intro h
    refine ⟨fun i => (thetaBasis b).repr y i, h, ?_⟩
    conv_lhs => rw [← (thetaBasis b).sum_repr y]
    exact Finset.sum_congr rfl fun i _ => by rw [thetaBasis_apply]

omit [Fintype ι] in
theorem span_thetaBasis (b : Module.Basis ι ℤ (𝓞 F)) :
    Submodule.span ℤ (Set.range (thetaBasis b)) = L∞ :=
  Module.Basis.ofZLatticeBasis_span ℝ L∞ _

/-- Every $y \in F_\infty$ has a unique $\mathcal O_F$-translate in $\theta(I^n)$. -/
theorem existsUnique_add_mem_thetaBox (b : Module.Basis ι ℤ (𝓞 F)) (y : mixedSpace F) :
    ∃! a : 𝓞 F, mixedEmbedding F (a : F) + y ∈ thetaBox b := by
  simp only [thetaBox_eq]
  obtain ⟨ℓ, hℓ, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (thetaBasis b) y
  have hℓL : (ℓ : mixedSpace F) ∈ L∞ := (span_thetaBasis b).le ℓ.2
  obtain ⟨a, ha⟩ := (mem_Linf_iff _).mp hℓL
  refine ⟨a, ?_, fun c hc => ?_⟩
  · show mixedEmbedding F (a : F) + y ∈ _
    rw [ha]; exact hℓ
  · have hcL : mixedEmbedding F (c : F) ∈ Submodule.span ℤ (Set.range (thetaBasis b)) := by
      rw [span_thetaBasis]; exact (mem_Linf_iff _).mpr ⟨c, rfl⟩
    have := huniq ⟨_, hcL⟩ hc
    have h2 : mixedEmbedding F (c : F) = mixedEmbedding F (a : F) := by
      rw [ha]; exact congrArg Subtype.val this
    exact RingOfIntegers.coe_injective (mixedEmbedding_injective F h2)

/-- **Weil, V.§4, Prop. 6** (p. 89): $\theta(I^n)\times\prod_vr_v$ is a fundamental set of $k_{\mathbb A}$ modulo $k$:
every adele $x$ can be written as $x_0+\xi$ with $x_0\in\theta(I^n)\times\prod_vr_v$ and $\xi\in k$ in one and only
one way. -/
@[kb "weil1973bnt" "Ch. V, §4, Prop. 6 (p. 89)"]
theorem weil_V_4_prop6 (b : Module.Basis ι ℤ (𝓞 F)) (x : Adeles F) :
    ∃! ξ : F, x - diag F ξ ∈ thetaBox b ×ˢ OHat := by
  obtain ⟨ξ₀, hξ₀⟩ := exists_sub_mem_OHat x.2
  obtain ⟨a, ha, huniq⟩ := existsUnique_add_mem_thetaBox b (x.1 - mixedEmbedding F ξ₀)
  have hA : ∀ c : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (c : F) ∈ OHat :=
    fun c => (algebraMap_mem_OHat_iff _).mpr ⟨c, rfl⟩
  refine ⟨ξ₀ - (a : F), ⟨?_, ?_⟩, ?_⟩
  · change x.1 - mixedEmbedding F (ξ₀ - (a : F)) ∈ thetaBox b
    have : x.1 - mixedEmbedding F (ξ₀ - (a : F)) =
        mixedEmbedding F (a : F) + (x.1 - mixedEmbedding F ξ₀) := by
      rw [map_sub]; abel
    rw [this]; exact ha
  · change x.2 - algebraMap F _ (ξ₀ - (a : F)) ∈ OHat
    have : x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ₀ - (a : F)) =
        algebraMap F _ (a : F) + (x.2 - algebraMap F _ ξ₀) := by
      rw [map_sub]; abel
    rw [this]; exact add_mem_OHat (hA a) hξ₀
  · intro ξ' ⟨h1, h2⟩
    change x.1 - mixedEmbedding F ξ' ∈ thetaBox b at h1
    change x.2 - algebraMap F _ ξ' ∈ OHat at h2
    have hmem : algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ₀ - ξ') ∈ OHat := by
      have := sub_mem_OHat h2 hξ₀
      rw [map_sub]
      convert this using 1
      abel
    obtain ⟨c, hc⟩ := (algebraMap_mem_OHat_iff _).mp hmem
    have hc' : (c : F) = ξ₀ - ξ' := hc
    have : c = a := huniq c (by
      have e : mixedEmbedding F (c : F) + (x.1 - mixedEmbedding F ξ₀) = x.1 - mixedEmbedding F ξ' := by
        rw [hc', map_sub]; abel
      show mixedEmbedding F (c : F) + (x.1 - mixedEmbedding F ξ₀) ∈ thetaBox b
      rw [e]; exact h1)
    subst this
    rw [hc']; ring

/-- The fundamental set of Prop. 6 is measurable. -/
theorem measurableSet_thetaBox_prod (b : Module.Basis ι ℤ (𝓞 F)) :
    MeasurableSet (thetaBox b ×ˢ OHat : Set (Adeles F)) := by
  rw [thetaBox_eq]
  exact (ZSpan.fundamentalDomain_measurableSet _).prod measurableSet_OHat

end NumberFieldKB.WeilBNT
