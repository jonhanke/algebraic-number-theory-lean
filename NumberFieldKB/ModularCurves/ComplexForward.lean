import NumberFieldKB.ModularCurves.ComplexEval
import NumberFieldKB.ModularCurves.ComplexFiniteCriterion
import NumberFieldKB.ModularCurves.ModularQuotient
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# From weight 2 cusp forms to $\mathbb C(X_0(N))$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, Proposition 3.3 and Corollary 3.4 (pdf p. 199). For
$f \in S_2(\Gamma_0(N))$, $f/j'$ is a modular function (`isModularFunction_div_jD`), hence by Theorem 2.3 (`thm2_3`)
equal off a discrete set to $P(j, j_N)/Q(j, j_N)$; its class $h_f \in \mathbb C(X_0(N))$ is characterized by
`IsRep f h`: at every $\tau \in \mathbb H$ the germ $\sigma_{c_0}(h)\,j'$ is the germ of $f$ (`exists_isRep`,
`IsRep.unique`). Since $f$ is holomorphic, $h_f$ satisfies the conditions of $L(W)$ at the finite places
(`IsRep.forall_finite`).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped WithZero MatrixGroups Manifold

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

theorem tendsto_ofComplex_nhdsNE (τ : ℍ) : Tendsto ofComplex (𝓝[≠] (τ : ℂ)) (𝓝[≠] τ) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hc : ContinuousAt ofComplex (τ : ℂ) := ofComplex.continuousAt (by exact ⟨τ, Set.mem_univ _, rfl⟩)
    rw [ContinuousAt, ofComplex_apply] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with w hw him
    intro h
    apply hw
    have : ((ofComplex w : ℍ) : ℂ) = w := by rw [ofComplex_apply_of_im_pos him]
    rw [← this, show ofComplex w = τ from h]
    rfl

/-- An eventual statement off a discrete subset of $\mathbb H$ holds near every point, in the coordinate of
$\mathbb C$. -/
theorem eventually_nhdsNE_of_codiscrete {p : ℍ → Prop} (h : ∀ᶠ z in codiscrete ℍ, p z) (τ : ℍ) :
    ∀ᶠ w in 𝓝[≠] (τ : ℂ), p (ofComplex w) :=
  (tendsto_ofComplex_nhdsNE τ).eventually ((eventually_codiscrete_iff_forall_eventually_nhdsNE.1 h) τ)

variable (N : ℕ) [NeZero N]

/-- **$h$ represents $f$**: at every point the germ of $h\,j'$ is the germ of $f$. -/
def IsRep (f : ℍ → ℂ) (hf : MDiff f) (h : X0C N) : Prop :=
  ∀ τ : ℍ, finEmbC τ N (cosetOne N) h * jDerivGerm τ =
    MeroGerm.mk (f ∘ ofComplex) (analyticAt_comp_ofComplex hf τ).meromorphicAt

theorem jDerivGerm_ne_zero (τ : ℍ) : jDerivGerm τ ≠ 0 := by
  intro h0
  have := finVal_jDerivGerm τ
  rw [h0, map_zero] at this
  exact WithZero.exp_ne_zero this.symm

/-- **Uniqueness of the representative.** -/
theorem IsRep.unique {f : ℍ → ℂ} {hf : MDiff f} {h h' : X0C N} (H : IsRep N f hf h) (H' : IsRep N f hf h') :
    h = h' := by
  have e := (H UpperHalfPlane.I).trans (H' UpperHalfPlane.I).symm
  have e' := mul_right_cancel₀ (jDerivGerm_ne_zero UpperHalfPlane.I) e
  exact (finEmbC UpperHalfPlane.I N (cosetOne N)).toRingHom.injective e'

theorem jD_eq_comp (z : ℍ) : jD z = deriv (jFun ∘ ofComplex) (z : ℂ) := rfl

/-- The germ of $G(j, j_N)$ with $c_0$ the trivial coset. -/
theorem polyFun2_one (G : ℂ[X][X]) (z : ℂ) :
    polyFun2 N G (cosetOne N) z = evalJJN N G (ofComplex z) := by
  rw [polyFun2, evalJJN, cosetOne, cosetRoot_mk (one_le_N N), inv_one, one_smul]

theorem evalJJNC_apply (G : ℂ[X][X]) (z : ℍ) : evalJJNC N G z = evalJJN N G z := by
  rw [evalJJNHom_apply, mapRingHom_id, Polynomial.map_id]

theorem mdiff_jD : MDiff jD := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro x hx
  refine ((analyticAt_jFun ⟨x, hx⟩).deriv.differentiableAt.differentiableWithinAt).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with w hw
    simp only [Function.comp_apply, jD]
    rw [ofComplex_apply_of_im_pos hw]
  · simp only [Function.comp_apply, jD]
    rw [ofComplex_apply_of_im_pos hx]

theorem jD_ne_zero : jD ≠ 0 := by
  obtain ⟨τ, hτ⟩ := jFun_surjective 1
  intro h
  have h0 : jFun τ ≠ 0 := by rw [hτ]; norm_num
  have h1 : jFun τ ≠ 1728 := by rw [hτ]; norm_num
  have hd := (analyticAt_jFun τ).analyticOrderAt_deriv_add_one
  have hτ' : (jFun ∘ ofComplex) (τ : ℂ) = jFun τ := by simp [ofComplex_apply]
  rw [hτ', analyticOrderAt_jFun_sub_eq_one τ h0 h1] at hd
  have hz : analyticOrderAt (deriv (jFun ∘ ofComplex)) (τ : ℂ) = 0 := by
    generalize ha : analyticOrderAt (deriv (jFun ∘ ofComplex)) (τ : ℂ) = a at hd
    induction a using ENat.recTopCoe with
    | top => simp at hd
    | coe n =>
      have : n + 1 = 1 := by exact_mod_cast hd
      have hn : n = 0 := by omega
      rw [hn]; rfl
  rw [analyticOrderAt_eq_zero] at hz
  rcases hz with hna | hne
  · exact hna (analyticAt_jFun τ).deriv
  · exact hne (by simpa [jD] using congrFun h τ)

/-- **Existence of the representative** (Theorem 2.3 applied to $f/j'$). -/
theorem exists_isRep {f : ℍ → ℂ} (hf : IsCuspFormMilne (CongruenceSubgroup.Gamma0 N) 1 f) :
    ∃ P Q : ℂ[X][X], mkC N Q ≠ 0 ∧ IsRep N f hf.1 (mkC N P / mkC N Q) := by
  obtain ⟨P, Q, ⟨z0, hz0⟩, hPQ⟩ := thm2_3.rational N (one_le_N N) _ (isModularFunction_div_jD hf)
  have hQ : mkC N Q ≠ 0 := by
    rw [Ne, mkC_eq_zero_iff]
    intro h
    apply hz0
    rw [← evalJJNC_apply, h]
    rfl
  refine ⟨P, Q, hQ, fun τ => ?_⟩
  have hb : finEmbC τ N (cosetOne N) (mkC N Q) ≠ 0 :=
    (map_ne_zero_iff _ (finEmbC τ N (cosetOne N)).toRingHom.injective).2 hQ
  rw [map_div₀, div_mul_eq_mul_div, div_eq_iff hb, finEmbC_mkC, finEmbC_mkC, polyGerm2, polyGerm2, jDerivGerm,
    ← MeroGerm.mk_mul, ← MeroGerm.mk_mul, MeroGerm.mk_eq_mk]
  -- the identity $P(j, j_N)\,j' = f\,Q(j, j_N)$ off a discrete set
  have hQne : ∀ᶠ z in codiscrete ℍ, evalJJN N Q z ≠ 0 := by
    have hmd : MDiff (evalJJNC N Q) := mdifferentiable_evalJJNHom (N := N) (RingHom.id ℂ) (one_le_N N) Q
    have hne : evalJJNC N Q ≠ 0 := fun h => hz0 (by rw [← evalJJNC_apply, h]; rfl)
    filter_upwards [eventually_codiscrete_ne_zero hmd hne] with z hz
    rwa [← evalJJNC_apply]
  have hjne : ∀ᶠ z in codiscrete ℍ, jD z ≠ 0 := eventually_codiscrete_ne_zero mdiff_jD jD_ne_zero
  have hid : ∀ᶠ z in codiscrete ℍ, evalJJN N P z * jD z = f z * evalJJN N Q z := by
    filter_upwards [hPQ, hQne, hjne] with z hz hq hj
    have hz' : f z / jD z = evalJJN N P z / evalJJN N Q z := hz
    field_simp at hz'
    linear_combination -hz'
  filter_upwards [eventually_nhdsNE_of_codiscrete hid τ,
    nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with w hw him
  simp only [Pi.mul_apply, Function.comp_apply, polyFun2_one]
  have hjw : jD (ofComplex w) = deriv (jFun ∘ ofComplex) w := by
    rw [jD, ofComplex_apply_of_im_pos him]
  rw [← hjw]
  exact hw

/-- The germ of a holomorphic function has valuation at most $1$. -/
theorem finVal_mk_le_one {τ : ℍ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g (τ : ℂ)) :
    finVal τ (MeroGerm.mk g hg.meromorphicAt) ≤ 1 := by
  rw [finVal, ordVal_mk]
  have h := toVal_antitone hg.meromorphicOrderAt_nonneg
  rwa [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, toVal_coe, neg_zero, WithZero.exp_zero] at h

/-- **A representative of a cusp form satisfies the conditions of $L(W)$ at the finite places.** -/
theorem IsRep.forall_finite {f : ℍ → ℂ} {hf : MDiff f} {h : X0C N} (H : IsRep N f hf h) (hh : h ≠ 0) :
    ∀ P' : Place ℂ (X0C N), P'.restrict ℂ (RatFunc ℂ) ≠ Place.infty ℂ → -(canonicalW N).coeff P' ≤ P'.ord h :=
  (forall_finite_iff N hh).2 fun τ => by
    rw [H τ]
    exact finVal_mk_le_one (analyticAt_comp_ofComplex hf τ)

end NumberFieldKB.ModularCurves
