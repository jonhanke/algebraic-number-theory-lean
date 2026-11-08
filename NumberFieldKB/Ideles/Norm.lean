import NumberFieldKB.Ideles.Bridge
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleIdeal

/-!
# The idele norms agree

$F$ is a number field. Three normalizations of the idele norm $\|x\|_{\mathbb A} = \prod_v|x_v|_v$ are in use:

* Mathlib's `Norm` on `AdeleRing (𝓞 F) F`: $\|x\| = \prod_{v\mid\infty}\|x_v\|^{m_v}\cdot\prod_{v\nmid\infty}\|x_v\|$ with
  $m_v\in\{1,2\}$ and the finite-place norm $\|x_v\| = N(v)^{-\operatorname{ord}_v x_v}$ (`AdeleRing.norm_apply_of_isUnit`);
  Tau Ceti's bundled `ideleNorm` on `IdeleGroup (𝓞 F) F` is this norm (Tau Ceti `coe_ideleNorm` [unverified]; Tau Ceti
  is on a newer Lean and is not imported);
* QuadFormsKB's `ideleNorm F` $= |\det(g_\infty\cdot)|\cdot\prod_v\Delta_v(g_v)$, with $\Delta_v$ the Haar modulus of $F_v$,
  and the Haar modulus `ideleNormHom F` of the whole adele ring (`coe_ideleNormHom`).

* **`norm_eq_ideleNorm`**: for an idele $x$ of Mathlib, $\|x\| = $ `ideleNorm F (ideleGroupEquiv F x)`;
* **`ideleGroupNorm F`**: the norm on Mathlib's idele group as a continuous homomorphism to $\mathbb R_{\ge0}$
  (`coe_ideleGroupNorm`, `continuous_ideleGroupNorm`), trivial on principal ideles (`ideleGroupNorm_unitEmbedding`,
  the product formula).

The local inputs: at a finite place the Haar modulus of $u\in F_v^\times$ is $\|u\|$ (`distribHaarChar_adicCompletion`,
from QuadFormsKB's `WeilRep.modK_eq_norm`); at the infinite places $|\det(t\cdot)| = N(t)$ on the mixed space
(`abs_det_mulLeft_eq_norm`).
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open QuadFormsKB.Tamagawa.Measure.Weil
open scoped NNReal

namespace NumberFieldKB.Ideles

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-- On the mixed space, $|\det_{\mathbb R}(t\cdot)| = N(t) = \prod_{\text{real}}|t_w|\prod_{\text{complex}}|t_w|^2$. -/
theorem abs_det_mulLeft_eq_norm (t : mixedSpace F) :
    |LinearMap.det (LinearMap.mulLeft ℝ t)| = mixedEmbedding.norm t := by
  rw [det_mulLeft_mixedSpace, mixedEmbedding.norm_apply, prod_eq_prod_mul_prod, abs_mul,
    Finset.abs_prod, Finset.abs_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mixedEmbedding.normAtPlace_apply_of_isReal w.2, mult, ite_eq_left w.2, pow_one, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [abs_of_nonneg (Complex.normSq_nonneg _), mixedEmbedding.normAtPlace_apply_of_isComplex w.2, mult,
      ite_eq_right (not_isReal_iff_isComplex.mpr w.2), Complex.sq_norm]

/-- **At a finite place the Haar modulus is Mathlib's norm**: $\Delta_v(u) = \|u\|$ for $u\in F_v^\times$. -/
theorem distribHaarChar_adicCompletion (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    (MeasureTheory.distribHaarChar (v.adicCompletion F) u : ℝ) = ‖(u : v.adicCompletion F)‖ := by
  have h := QuadFormsKB.WeilRep.modK_eq_norm v u.ne_zero
  rwa [QuadFormsKB.Analysis.Weil.modK_of_ne u.ne_zero, Units.mk0_val] at h

/-- **The idele norms agree**: Mathlib's norm of an idele is QuadFormsKB's `ideleNorm` of its image. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §3.3 [unverified locator] (the idele absolute value |a| = ∏_p |a_p|_p)"]
theorem norm_eq_ideleNorm (x : IdeleGroup (𝓞 F) F) :
    ‖(x : AdeleRing (𝓞 F) F)‖ = ideleNorm F (ideleGroupEquiv F x) := by
  rw [AdeleRing.norm_apply_of_isUnit x.isUnit, ideleNorm]
  congr 1
  · rw [← NumberField.InfiniteAdeleRing.norm_def, InfiniteAdeleRing.norm_eq_norm_ringEquiv_mixedSpace,
      ← abs_det_mulLeft_eq_norm]
    rfl
  · refine finprod_congr fun v => ?_
    rw [modAt, distribHaarChar_adicCompletion]
    rfl

/-- **The norm on Mathlib's idele group** as a homomorphism to $\mathbb R_{\ge0}$: QuadFormsKB's Haar modulus
`ideleNormHom F` through `ideleGroupEquiv F`; its value is Mathlib's norm (`coe_ideleGroupNorm`). -/
def ideleGroupNorm (F : Type) [Field F] [NumberField F] : IdeleGroup (𝓞 F) F →* ℝ≥0 :=
  (ideleNormHom F).comp (ideleGroupEquiv F : IdeleGroup (𝓞 F) F →* (Adeles F)ˣ)

theorem ideleGroupNorm_apply (x : IdeleGroup (𝓞 F) F) :
    ideleGroupNorm F x = ideleNormHom F (ideleGroupEquiv F x) := rfl

@[simp] theorem coe_ideleGroupNorm (x : IdeleGroup (𝓞 F) F) :
    (ideleGroupNorm F x : ℝ) = ‖(x : AdeleRing (𝓞 F) F)‖ := by
  rw [ideleGroupNorm_apply, coe_ideleNormHom, norm_eq_ideleNorm]

theorem continuous_ideleGroupNorm : Continuous (ideleGroupNorm F) :=
  continuous_ideleNormHom.comp (ideleGroupEquiv F).continuous

/-- **The product formula** on Mathlib's ideles, from QuadFormsKB's measure-theoretic proof `ideleNorm_diagUnits`
(Mathlib has it independently as `AdeleRing.norm_algebraMap_eq_one_of_ne_zero`). -/
theorem ideleGroupNorm_unitEmbedding (ξ : Fˣ) : ideleGroupNorm F (IdeleGroup.unitEmbedding (𝓞 F) F ξ) = 1 := by
  apply NNReal.coe_injective
  rw [ideleGroupNorm_apply, coe_ideleNormHom, ideleGroupEquiv_unitEmbedding, ideleNorm_diagUnits, NNReal.coe_one]

theorem ideleGroupNorm_eq_one_of_mem_principalSubgroup {x : IdeleGroup (𝓞 F) F}
    (hx : x ∈ IdeleGroup.principalSubgroup (𝓞 F) F) : ideleGroupNorm F x = 1 := by
  obtain ⟨ξ, rfl⟩ := hx
  exact ideleGroupNorm_unitEmbedding ξ

end

end NumberFieldKB.Ideles
