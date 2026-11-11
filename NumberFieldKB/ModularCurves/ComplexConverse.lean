import NumberFieldKB.ModularCurves.ComplexCuspLink
import Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-!
# From $L(W)$ to holomorphic weight 2 forms for $\Gamma_0(N)$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, Corollary 3.4 (pdf p. 199), the converse direction at the
points of $\mathbb H$. For $0 \ne h \in L(W)$, $h = P(j, j_N)/d(j)$, the function $\varphi = P(j,j_N)\,j'/d(j)$ is
meromorphic on $\mathbb H$ with germ $\sigma_{c_0}(h)\,j'$ at every $\tau$, of order $\ge 0$ (`forall_finite_iff`);
its normal form (Mathlib `toMeromorphicNFOn`) is holomorphic, and gives $f$ with `IsRep N f _ h`
(`exists_isRep_of_mem`). Every function with a representative is invariant of weight 2 under $\Gamma_0(N)$
(`IsRep.slash_eq`), by the identity $P(j,j_N)\,j' = f\,Q(j,j_N)$ (`rep_identity`) and the invariance of $j, j_N$, $j'$
(`jD_smul`).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped WithZero MatrixGroups Manifold ModularForm

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

theorem toVal_le_one_iff {a : WithTop ℤ} : toVal a ≤ 1 ↔ 0 ≤ a := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    rw [toVal_coe, ← WithZero.exp_zero, WithZero.exp_le_exp]
    constructor
    · intro h; exact_mod_cast (by omega : (0 : ℤ) ≤ n)
    · intro h; have : (0 : ℤ) ≤ n := by exact_mod_cast h
      omega

/-- A meromorphic function of order $\ge 0$ at every point of $U$ agrees, on punctured neighbourhoods, with a function
analytic at every point of $U$ (its normal form). -/
theorem exists_analyticAt_eq_of_order_nonneg {φ : ℂ → ℂ} {U : Set ℂ} (hφ : MeromorphicOn φ U)
    (h0 : ∀ z ∈ U, 0 ≤ meromorphicOrderAt φ z) :
    ∃ g : ℂ → ℂ, (∀ z ∈ U, AnalyticAt ℂ g z) ∧ ∀ z ∈ U, g =ᶠ[𝓝[≠] z] φ := by
  refine ⟨toMeromorphicNFOn φ U, fun z hz => ?_, fun z hz => hφ.toMeromorphicNFOn_eq_self_on_nhdsNE hz⟩
  refine (meromorphicNFOn_toMeromorphicNFOn φ U hz).meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
  rw [meromorphicOrderAt_congr (hφ.toMeromorphicNFOn_eq_self_on_nhdsNE hz)]
  exact h0 z hz

variable (N : ℕ) [NeZero N]

omit [NeZero N] in
theorem evalJJN_C (d : ℂ[X]) (z : ℍ) : evalJJN N (C d) z = d.eval (jFun z) := by
  simp [evalJJN]

theorem evalJJN_smul {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (G : ℂ[X][X]) (z : ℍ) :
    evalJJN N G (γ • z) = evalJJN N G z := by
  rw [evalJJN, evalJJN, jFun_smul, jN_smul (one_le_N N) hγ]

theorem mkC_C_ne_zero {d : ℂ[X]} (hd : d ≠ 0) : mkC N (C d) ≠ 0 := by
  rw [mkC_C]
  exact (_root_.map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).2 hd)

/-- **An element of $L(W)$ is the representative of a holomorphic function.** -/
theorem exists_isRep_of_mem {h : X0C N} (hW : h ∈ riemannRochSpace (canonicalW N)) :
    ∃ (f : ℍ → ℂ) (hf : MDiff f), IsRep N f hf h := by
  rcases eq_or_ne h 0 with rfl | hh
  · refine ⟨0, mdifferentiable_const, fun τ => ?_⟩
    rw [map_zero, zero_mul]
    exact (MeroGerm.mk_zero (x := (τ : ℂ))).symm
  have hfin := (forall_finite_iff N hh).1 fun P' hP => (mem_riemannRochSpace_iff_neg_le_ord hh).1 hW P'
  obtain ⟨P, d, hd, rfl⟩ := exists_eq_div_mkC N h
  set U : Set ℂ := {z | 0 < z.im}
  set φ : ℂ → ℂ := polyFun2 N P (cosetOne N) * deriv (jFun ∘ ofComplex) / polyFun2 N (C d) (cosetOne N)
  have hmer : ∀ τ : ℍ, MeromorphicAt φ (τ : ℂ) := fun τ =>
    ((analyticAt_polyFun2 N P _ τ).meromorphicAt.mul (analyticAt_deriv_jFun τ).meromorphicAt).div
      (analyticAt_polyFun2 N (C d) _ τ).meromorphicAt
  -- the germ of `φ` at `τ` is `σ_{c₀}(h) j'`
  have hgerm : ∀ τ : ℍ, finEmbC τ N (cosetOne N) (mkC N P / mkC N (C d)) * jDerivGerm τ =
      MeroGerm.mk φ (hmer τ) := by
    intro τ
    have hb : finEmbC τ N (cosetOne N) (mkC N (C d)) ≠ 0 :=
      (map_ne_zero_iff _ (finEmbC τ N (cosetOne N)).toRingHom.injective).2 (mkC_C_ne_zero N hd)
    rw [map_div₀, div_mul_eq_mul_div, div_eq_iff hb, finEmbC_mkC, finEmbC_mkC, polyGerm2, polyGerm2, jDerivGerm,
      ← MeroGerm.mk_mul, ← MeroGerm.mk_mul, MeroGerm.mk_eq_mk]
    rw [finEmbC_mkC, polyGerm2, Ne, MeroGerm.mk_eq_zero_iff] at hb
    have hne := ((analyticAt_polyFun2 N (C d) (cosetOne N) τ).meromorphicAt.eventually_eq_zero_or_eventually_ne_zero
      ).resolve_left hb
    filter_upwards [hne] with w hw
    simp only [φ, Pi.mul_apply, Pi.div_apply]
    field_simp
  have hU : ∀ z ∈ U, (z : ℂ) = ((ofComplex z : ℍ) : ℂ) := fun z hz => by
    rw [ofComplex_apply_of_im_pos hz]
  obtain ⟨g, hg, hgφ⟩ := exists_analyticAt_eq_of_order_nonneg (φ := φ) (U := U)
    (fun z hz => by rw [hU z hz]; exact hmer _) (fun z hz => by
      rw [hU z hz]
      have := hfin (ofComplex z)
      rw [hgerm, finVal, ordVal_mk] at this
      exact toVal_le_one_iff.1 this)
  set f : ℍ → ℂ := fun z => g z
  have hfg : ∀ τ : ℍ, f ∘ ofComplex =ᶠ[𝓝 (τ : ℂ)] g := fun τ => by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
    simp only [f, Function.comp_apply]
    rw [ofComplex_apply_of_im_pos hw]
  have hf : MDiff f := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    intro w hw
    refine ((hg w hw).differentiableAt.differentiableWithinAt).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact (hfg ⟨v, hv⟩).eq_of_nhds
    · exact (hfg ⟨w, hw⟩).eq_of_nhds
  refine ⟨f, hf, fun τ => ?_⟩
  rw [hgerm, MeroGerm.mk_eq_mk]
  exact (hgφ τ τ.im_pos).symm.trans (Filter.EventuallyEq.filter_mono (hfg τ) nhdsWithin_le_nhds).symm

/-- **A function with a representative is invariant of weight 2 under $\Gamma_0(N)$.** -/
theorem IsRep.slash_eq {f : ℍ → ℂ} {hf : MDiff f} {h : X0C N} (H : IsRep N f hf h) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : f ∣[(2 : ℤ)] γ = f := by
  obtain ⟨P, d, hd, rfl⟩ := exists_eq_div_mkC N h
  have hQ := mkC_C_ne_zero N hd
  set G : ℍ → ℂ := f ∣[(2 : ℤ)] γ - f
  have hG : MDiff G := (MDifferentiable.slash hf 2 (Matrix.SpecialLinearGroup.mapGL ℝ γ)).sub hf
  have hzero : ∀ z, G z * d.eval (jFun z) = 0 := by
    intro z
    have h1 := rep_identity N hf hQ H (γ • z)
    have h2 := rep_identity N hf hQ H z
    rw [evalJJN_smul N hγ, evalJJN_smul N hγ, evalJJN_C] at h1
    rw [evalJJN_C] at h2
    have hj := jD_smul γ z
    simp only [G, Pi.sub_apply, ← pullback_eq_slash]
    linear_combination -deriv (moebiusC γ) (z : ℂ) * h1 + h2 + evalJJN N P z * hj
  suffices hG0 : G = 0 by funext z; simpa [G, sub_eq_zero] using congrFun hG0 z
  refine UpperHalfPlane.eq_zero_of_frequently hG (τ := UpperHalfPlane.I) ?_
  have hev := (eventually_codiscrete_iff_forall_eventually_nhdsNE.1
    (eventually_codiscrete_eval_jFun_ne_zero hd)) UpperHalfPlane.I
  refine (hev.mono fun z hz => ?_).frequently
  exact (mul_eq_zero.1 (hzero z)).resolve_right hz

end NumberFieldKB.ModularCurves
