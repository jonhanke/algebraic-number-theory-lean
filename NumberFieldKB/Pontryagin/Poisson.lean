import NumberFieldKB.Pontryagin.QuotientMeasure
import NumberFieldKB.Pontryagin.Unconditional

/-!
# The abstract Poisson summation formula (Weil VII.§2, pp. 105–106)

$G$ is a locally compact commutative Hausdorff group with a regular Haar measure $\alpha$, $\Gamma\subset G$ a discrete
subgroup with $G/\Gamma$ compact, and $\Gamma^*\subset G^*$ its annihilator (`NumberFieldKB.Pontryagin.annihilator`),
a discrete group isomorphic to the dual of $G/\Gamma$ (`annihilatorEquiv`). Groups are written multiplicatively (Weil
writes them additively), and Weil's Fourier transform is
`NumberFieldKB.WeilBNT.AbstractFourier.fourierLCA α Φ`, $\Phi^*(g^*)=\int_G\Phi(g)\langle g,g^*\rangle\,d\alpha(g)$.

* `IsAdmissibleFor α β Γ Φ` (Weil, p. 105): $\Phi$ is admissible for $(G,\Gamma)$: admissible for $G$
  (`AbstractFourier.IsAdmissible`), and the series $\sum_{\gamma\in\Gamma}\Phi(g\gamma)$ and
  $\sum_{\gamma^*\in\Gamma^*}\Phi^*(g^*\gamma^*)$ converge absolutely, and uniformly on every compact set.
  (We read "converge absolutely and uniformly on every compact set" as: absolutely at every point, and uniformly on
  compact sets. The stronger reading, uniform convergence of the series of absolute values, implies this one.)
* **`poisson_summation`** (Weil, p. 106, formula (1)): if $\alpha(G/\Gamma)=1$ (the quotient measure
  `quotientMeasure Γ α`, `NumberFieldKB/Pontryagin/QuotientMeasure.lean`) and $\Phi$ is admissible for
  $(G,\Gamma)$, then $\sum_{\gamma\in\Gamma}\Phi(\gamma)=\sum_{\gamma^*\in\Gamma^*}\Phi^*(\gamma^*)$.

Proof (Weil's): $\Psi(\Gamma g)=\sum_\gamma\Phi(g\gamma)$ is continuous on the compact group $G/\Gamma$; unfolding
the quotient measure gives its Fourier coefficients, $\hat\Psi(\psi)=\Phi^*(\psi\circ\pi)$; they are absolutely
summable, so Fourier inversion on $G/\Gamma$ (`Unconditional.isDualMeasure_count_of_compact`, whose completeness of
characters comes from Bochner's theorem) at the identity is the formula.

The number-field instance $(G,\Gamma)=(\mathbb A_F,F)$ is QuadFormsKB's `QuadFormsKB.Analysis.adelicPoisson`.
-/

open MeasureTheory Topology Filter Set
open NumberFieldKB.WeilBNT.AbstractFourier

noncomputable section

namespace NumberFieldKB.Pontryagin

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace (PontryaginDual G)]

/-- **Weil, VII.§2, p. 105**: $\Phi$ is **admissible for $(G,\Gamma)$**: admissible for $G$, and the series
$\sum_{\gamma\in\Gamma}\Phi(g\gamma)$ and $\sum_{\gamma^*\in\Gamma^*}\Phi^*(g^*\gamma^*)$ converge absolutely, and
uniformly on every compact subset of $G$, resp. $G^*$. -/
structure IsAdmissibleFor (α : Measure G) (β : Measure (PontryaginDual G)) (Γ : Subgroup G) (Φ : G → ℂ) :
    Prop where
  /-- $\Phi$ is admissible for $G$: continuous, integrable, with integrable Fourier transform. -/
  isAdmissible : IsAdmissible α β Φ
  /-- $\sum_\gamma\Phi(g\gamma)$ converges absolutely at every $g$. -/
  summable_norm : ∀ g : G, Summable fun γ : Γ => ‖Φ (g * γ)‖
  /-- $\sum_\gamma\Phi(g\gamma)$ converges uniformly on every compact set. -/
  summableUniformlyOn : ∀ K : Set G, IsCompact K → SummableUniformlyOn (fun (γ : Γ) (g : G) => Φ (g * γ)) K
  /-- $\sum_{\gamma^*}\Phi^*(g^*\gamma^*)$ converges absolutely at every $g^*$. -/
  summable_norm_dual : ∀ χ : PontryaginDual G,
    Summable fun γ : annihilator Γ => ‖fourierLCA α Φ (χ * γ)‖
  /-- $\sum_{\gamma^*}\Phi^*(g^*\gamma^*)$ converges uniformly on every compact set. -/
  summableUniformlyOn_dual : ∀ K : Set (PontryaginDual G), IsCompact K →
    SummableUniformlyOn (fun (γ : annihilator Γ) (χ : PontryaginDual G) => fourierLCA α Φ (χ * γ)) K

variable (Γ : Subgroup G) [DiscreteTopology Γ]

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace (PontryaginDual G)]
  [DiscreteTopology Γ] in
/-- The periodization of a function whose translates sum uniformly on compact sets is continuous on $G$. -/
theorem continuous_tsum_mul_of_tendstoUniformlyOn {Φ : G → ℂ} (hΦc : Continuous Φ)
    (hu : ∀ K : Set G, IsCompact K → TendstoUniformlyOn (fun (s : Finset Γ) (g : G) => ∑ γ ∈ s, Φ (g * γ))
      (fun g => ∑' γ : Γ, Φ (g * γ)) atTop K) :
    Continuous fun g => ∑' γ : Γ, Φ (g * γ) := by
  refine continuous_iff_continuousAt.mpr fun g => ?_
  obtain ⟨K, hK, hKg⟩ := exists_compact_mem_nhds g
  refine ((hu K hK).continuousOn (Eventually.of_forall fun s => ?_).frequently).continuousAt hKg
  exact (continuous_finsetSum s fun _ _ => hΦc.comp (continuous_id.mul continuous_const)).continuousOn

/-- Multiplying the terms of a uniformly convergent series of functions by a fixed function of absolute value one
preserves uniform convergence. -/
theorem tendstoUniformlyOn_mul_unit {X ι : Type*} {F : ι → X → ℂ} {f : X → ℂ} {l : Filter ι} {K : Set X}
    (hF : TendstoUniformlyOn F f l K) (c : X → ℂ) (hc : ∀ g, ‖c g‖ = 1) :
    TendstoUniformlyOn (fun i g => F i g * c g) (fun g => f g * c g) l K := by
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro ε hε
  filter_upwards [hF ε hε] with i hi g hg
  rw [dist_eq_norm, ← sub_mul, norm_mul, hc, mul_one, ← dist_eq_norm]
  exact hi g hg

variable [CompactSpace (G ⧸ Γ)] [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

omit [MeasurableSpace (PontryaginDual G)] in
/-- **The Fourier coefficients of the periodization**: for $\psi\in(G/\Gamma)^*$, the Fourier transform on
$G/\Gamma$ (for the quotient measure) of $\Gamma g\mapsto\sum_\gamma\Phi(g\gamma)$ at $\psi$ is
$\Phi^*(\psi\circ\pi)$. -/
theorem fourierLCA_periodize (α : Measure G) [α.IsHaarMeasure] [α.Regular] {Φ : G → ℂ} (hΦc : Continuous Φ)
    (hΦi : Integrable Φ α)
    (hu : ∀ K : Set G, IsCompact K → TendstoUniformlyOn (fun (s : Finset Γ) (g : G) => ∑ γ ∈ s, Φ (g * γ))
      (fun g => ∑' γ : Γ, Φ (g * γ)) atTop K)
    (ψ : PontryaginDual (G ⧸ Γ)) :
    fourierLCA (quotientMeasure Γ α) (periodize Γ Φ) ψ = fourierLCA α Φ (annihilatorEquiv Γ ψ).1 := by
  have hh := isBruhat_bruhat Γ
  set χ : PontryaginDual G := (annihilatorEquiv Γ ψ).1
  have hχ : ∀ g, ((χ g : Circle) : ℂ) = ((ψ (g : G ⧸ Γ) : Circle) : ℂ) := fun g => rfl
  have hχγ : ∀ (g : G) (γ : Γ), ((χ (g * γ) : Circle) : ℂ) = ((χ g : Circle) : ℂ) := by
    intro g γ
    rw [hχ, hχ, QuotientGroup.mk_mul, QuotientGroup.eq_one_iff (γ : G) |>.mpr γ.2, mul_one]
  have hΨc : Continuous (periodize Γ Φ) :=
    (continuous_tsum_mul_of_tendstoUniformlyOn Γ hΦc hu).quotient_lift _
  have hψc : Continuous fun x : G ⧸ Γ => ((ψ x : Circle) : ℂ) := continuous_subtype_val.comp ψ.continuous
  have hχc : Continuous fun g : G => ((χ g : Circle) : ℂ) := continuous_subtype_val.comp χ.continuous
  unfold fourierLCA
  rw [integral_quotientMeasure Γ α hh (P := fun x => periodize Γ Φ x * ((ψ x : Circle) : ℂ)) (hΨc.mul hψc)]
  -- unfold along `Γ` with `F = Φ χ`
  have hsums : (fun (s : Finset Γ) (g : G) => ∑ γ ∈ s, Φ (g * γ) * ((χ (g * γ) : Circle) : ℂ)) =
      fun (s : Finset Γ) (g : G) => (∑ γ ∈ s, Φ (g * γ)) * ((χ g : Circle) : ℂ) := by
    funext s g
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun γ _ => by rw [hχγ]
  have hlim : (fun g : G => ∑' γ : Γ, Φ (g * γ) * ((χ (g * γ) : Circle) : ℂ)) =
      fun g => (∑' γ : Γ, Φ (g * γ)) * ((χ g : Circle) : ℂ) := by
    funext g
    rw [← tsum_mul_right]
    exact tsum_congr fun γ => by rw [hχγ]
  have hFi : Integrable (fun g => Φ g * ((χ g : Circle) : ℂ)) α :=
    hΦi.norm.mono' (hΦc.mul hχc).aestronglyMeasurable (Eventually.of_forall fun g => by simp)
  have hFu : TendstoUniformlyOn (fun (s : Finset Γ) (g : G) => ∑ γ ∈ s, Φ (g * γ) * ((χ (g * γ) : Circle) : ℂ))
      (fun g => ∑' γ : Γ, Φ (g * γ) * ((χ (g * γ) : Circle) : ℂ)) atTop (tsupport (bruhat Γ)) := by
    rw [hsums, hlim]
    exact tendstoUniformlyOn_mul_unit (hu _ hh.hasCompactSupport) _ fun g => by simp
  have key := integral_eq_integral_mul_tsum Γ α hh (F := fun g => Φ g * ((χ g : Circle) : ℂ))
    (hΦc.mul hχc) hFi hFu
  refine Eq.trans ?_ key.symm
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  exact congrArg (fun z => (bruhat Γ g : ℂ) * z) (congrFun hlim g).symm

/-- **The abstract Poisson summation formula** (Weil, *Basic Number Theory*, VII.§2, p. 106, formula (1)): if
$\Gamma$ is a discrete subgroup of $G$ with $G/\Gamma$ compact, the Haar measure $\alpha$ gives $G/\Gamma$ measure $1$,
and $\Phi$ is admissible for $(G,\Gamma)$, then $\sum_{\gamma\in\Gamma}\Phi(\gamma)=\sum_{\gamma^*\in\Gamma^*}
\Phi^*(\gamma^*)$. -/
theorem poisson_summation (α : Measure G) [α.IsHaarMeasure] [α.Regular] (β : Measure (PontryaginDual G))
    (hα : quotientMeasure Γ α univ = 1) {Φ : G → ℂ} (hΦ : IsAdmissibleFor α β Γ Φ) :
    ∑' γ : Γ, Φ γ = ∑' χ : annihilator Γ, fourierLCA α Φ χ := by
  have hu : ∀ K : Set G, IsCompact K → TendstoUniformlyOn (fun (s : Finset Γ) (g : G) => ∑ γ ∈ s, Φ (g * γ))
      (fun g => ∑' γ : Γ, Φ (g * γ)) atTop K := fun K hK =>
    (hΦ.summableUniformlyOn K hK).hasSumUniformlyOn.tendstoUniformlyOn
  obtain ⟨hΦc, hΦi, -⟩ := hΦ.isAdmissible
  have : IsProbabilityMeasure (quotientMeasure Γ α) := ⟨hα⟩
  let _ : MeasurableSpace (PontryaginDual (G ⧸ Γ)) := ⊤
  have : MeasurableSingletonClass (PontryaginDual (G ⧸ Γ)) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hΨc : Continuous (periodize Γ Φ) :=
    (continuous_tsum_mul_of_tendstoUniformlyOn Γ hΦc hu).quotient_lift _
  have hcoef := fourierLCA_periodize Γ α hΦc hΦi hu
  have hsum : Summable fun χ : annihilator Γ => ‖fourierLCA α Φ χ‖ := by
    simpa using hΦ.summable_norm_dual 1
  have hsum' : Summable fun ψ : PontryaginDual (G ⧸ Γ) => ‖fourierLCA (quotientMeasure Γ α) (periodize Γ Φ) ψ‖ := by
    simp_rw [hcoef]
    exact (annihilatorEquiv Γ).toEquiv.summable_iff.mpr hsum
  have hadm : IsAdmissible (quotientMeasure Γ α) Measure.count (periodize Γ Φ) :=
    ⟨hΨc, hΨc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
      integrable_count_iff.mpr hsum'⟩
  have hinv := Unconditional.isDualMeasure_count_of_compact (quotientMeasure Γ α) _ hadm 1
  have hint : Integrable (fun ψ : PontryaginDual (G ⧸ Γ) =>
      fourierLCA (quotientMeasure Γ α) (periodize Γ Φ) ψ * ((ψ (1 : G ⧸ Γ)⁻¹ : Circle) : ℂ)) Measure.count := by
    rw [integrable_count_iff]
    simpa using hsum'
  rw [integral_count_eq_tsum hint] at hinv
  simp only [inv_one, map_one, Circle.coe_one, mul_one] at hinv
  have h1 : periodize Γ Φ (1 : G ⧸ Γ) = ∑' γ : Γ, Φ γ := by
    rw [← QuotientGroup.mk_one, periodize_mk]
    simp
  rw [← h1, hinv]
  simp_rw [hcoef]
  exact (annihilatorEquiv Γ).toEquiv.tsum_eq (fun χ : annihilator Γ => fourierLCA α Φ χ)

end NumberFieldKB.Pontryagin
