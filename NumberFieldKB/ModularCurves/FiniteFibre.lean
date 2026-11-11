import NumberFieldKB.ModularCurves.JLocal
import NumberFieldKB.ModularCurves.MeroGerm
import NumberFieldKB.ModularCurves.CuspFibre
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The embeddings of $\mathbb Q(X_0(N))$ into the meromorphic germs at a point of $\mathbb H$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (the ramification of $j : X_0(N) \to X_0(1)$, pdf p. 196).
For a point $\tau_0 \in \mathbb H$ and a coset $c = \gamma\Gamma_0(N)$, the map $f \mapsto f \circ \gamma^{-1}$ defines an
embedding $\sigma_c$ of $\mathbb Q(X_0(N))$ into the field `MeroGerm τ₀` of meromorphic germs at $\tau_0$: $j \mapsto j$,
$j_N \mapsto j_N \circ \gamma^{-1}$ (`finEmb`). The $\mu$ embeddings are distinct (`finEmb_injective`).

If $j(\tau_0)$ is a root of an irreducible $q \in \mathbb Q[X]$ and $j - j(\tau_0)$ has order $m$ at $\tau_0$, the order
valuation at $\tau_0$ induces $v_q^m$ on $\mathbb Q(j)$ (`ordVal_ratToMero`), the hypothesis of `FibreCount.lean`.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped Manifold MatrixGroups WithZero

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-! ### From $\mathbb C$-neighbourhoods to $\mathbb H$-neighbourhoods -/

theorem tendsto_coe_nhdsNE (τ : ℍ) : Tendsto (fun z : ℍ => (z : ℂ)) (𝓝[≠] τ) (𝓝[≠] (τ : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · exact (UpperHalfPlane.continuous_coe.tendsto τ).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact fun h => hz (UpperHalfPlane.ext h)

theorem eventually_of_comp_ofComplex {τ : ℍ} {p : ℍ → Prop}
    (h : ∀ᶠ w in 𝓝[≠] (τ : ℂ), p (ofComplex w)) : ∀ᶠ z in 𝓝[≠] τ, p z := by
  filter_upwards [(tendsto_coe_nhdsNE τ).eventually h] with z hz
  simpa [ofComplex_apply] using hz

/-! ### $\mathbb Q(j)$ in the germs at $\tau_0$ -/

/-- $p \mapsto (z \mapsto p(j(z)))$. -/
def polyFun : ℚ[X] →+* (ℂ → ℂ) :=
  eval₂RingHom ((Pi.constRingHom ℂ ℂ).comp (algebraMap ℚ ℂ)) (jFun ∘ ofComplex)

theorem polyFun_apply (p : ℚ[X]) (z : ℂ) : polyFun p z = aeval (jFun (ofComplex z)) p := by
  have h := Polynomial.hom_eval₂ p ((Pi.constRingHom ℂ ℂ).comp (algebraMap ℚ ℂ))
    (Pi.evalRingHom (fun _ : ℂ => ℂ) z) (jFun ∘ ofComplex)
  rw [aeval_def]
  exact h

theorem analyticAt_polyFun (p : ℚ[X]) (τ : ℍ) : AnalyticAt ℂ (polyFun p) (τ : ℂ) := by
  have : polyFun p = fun z => aeval ((jFun ∘ ofComplex) z) p := funext fun z => polyFun_apply p z
  rw [this]
  exact (analyticAt_jFun τ).aeval_polynomial p

variable (τ₀ : ℍ)

/-- $\mathbb Q[j] \to$ `MeroGerm τ₀`. -/
def polyToMero : ℚ[X] →+* MeroGerm (τ₀ : ℂ) :=
  ((Filter.Germ.coeRingHom (𝓝[≠] (τ₀ : ℂ))).comp polyFun).codRestrict (meroSubring (τ₀ : ℂ))
    fun p => ⟨polyFun p, (analyticAt_polyFun p τ₀).meromorphicAt, rfl⟩

theorem polyToMero_eq_mk (p : ℚ[X]) :
    polyToMero τ₀ p = MeroGerm.mk (polyFun p) (analyticAt_polyFun p τ₀).meromorphicAt := rfl

theorem polyToMero_injective : Function.Injective (polyToMero τ₀) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  rw [polyToMero_eq_mk, MeroGerm.mk_eq_zero_iff] at hp
  have h1 : ∀ᶠ z in 𝓝[≠] τ₀, (p.map (algebraMap ℚ ℂ)).eval (jFun z) = 0 := by
    refine eventually_of_comp_ofComplex (p := fun z => (p.map (algebraMap ℚ ℂ)).eval (jFun z) = 0) ?_
    filter_upwards [hp] with w hw
    rw [eval_map_algebraMap, ← polyFun_apply]
    exact hw
  by_contra hp0
  have hQ : p.map (algebraMap ℚ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).2 hp0
  have h2 := (eventually_codiscrete_iff_forall_eventually_nhdsNE.1
    (eventually_codiscrete_eval_jFun_ne_zero hQ)) τ₀
  exact (h1.and h2).exists.elim fun _ h => h.2 h.1

/-- $\mathbb Q(j) \to$ `MeroGerm τ₀`. -/
def ratToMero : RatFunc ℚ →+* MeroGerm (τ₀ : ℂ) :=
  RatFunc.liftRingHom (polyToMero τ₀)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyToMero_injective τ₀))

theorem ratToMero_algebraMap (p : ℚ[X]) : ratToMero τ₀ (algebraMap ℚ[X] (RatFunc ℚ) p) = polyToMero τ₀ p := by
  rw [ratToMero, RatFunc.liftRingHom_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

/-- The germs at $\tau_0$ as a $\mathbb Q(j)$-algebra (a type synonym). -/
abbrev FinField (τ₀ : ℍ) : Type := MeroGerm (τ₀ : ℂ)

instance : Algebra (RatFunc ℚ) (FinField τ₀) := (ratToMero τ₀).toAlgebra

/-- The order valuation at $\tau_0$ on `FinField τ₀`. -/
def finVal : Valuation (FinField τ₀) ℤᵐ⁰ := ordVal (τ₀ : ℂ)

theorem algebraMap_finField (x : RatFunc ℚ) : algebraMap (RatFunc ℚ) (FinField τ₀) x = ratToMero τ₀ x := rfl

/-! ### The embeddings $\sigma_c$ -/

variable (N : ℕ) [NeZero N]

/-- The germ of $j_N \circ \gamma_c^{-1}$ at $\tau_0$. -/
def rootGerm (c : Cosets N) : FinField τ₀ :=
  MeroGerm.mk (cosetRoot N c ∘ ofComplex)
    (analyticAt_comp_ofComplex (cosetRoot_mdiff (one_le_N N) c) τ₀).meromorphicAt

/-- Evaluating a polynomial in two variables at germs is evaluating pointwise. -/
theorem val_eval₂_polyToMero (G : ℚ[X][X]) (b : ℂ → ℂ) (hb : MeromorphicAt b (τ₀ : ℂ)) :
    ((G.eval₂ (polyToMero τ₀) (MeroGerm.mk b hb) : MeroGerm (τ₀ : ℂ)) : PGerm (τ₀ : ℂ)) =
      ((fun z => evalQ2 G (jFun (ofComplex z)) (b z) : ℂ → ℂ) : PGerm (τ₀ : ℂ)) := by
  have h := Polynomial.hom_eval₂ G (polyToMero τ₀) (meroSubring (τ₀ : ℂ)).subtype (MeroGerm.mk b hb)
  rw [Subring.coe_subtype] at h
  change ((G.eval₂ (polyToMero τ₀) (MeroGerm.mk b hb) : MeroGerm (τ₀ : ℂ)) : PGerm (τ₀ : ℂ)) = _ at h
  rw [h]
  have hc : (meroSubring (τ₀ : ℂ)).subtype.comp (polyToMero τ₀) =
      (Filter.Germ.coeRingHom (𝓝[≠] (τ₀ : ℂ))).comp polyFun := RingHom.ext fun p => rfl
  rw [hc]
  have hb' : ((MeroGerm.mk b hb : MeroGerm (τ₀ : ℂ)) : PGerm (τ₀ : ℂ)) = Filter.Germ.coeRingHom _ b := rfl
  rw [hb', ← Polynomial.hom_eval₂]
  change ((G.eval₂ polyFun b : ℂ → ℂ) : PGerm (τ₀ : ℂ)) = _
  congr 1
  funext z
  have h2 := Polynomial.hom_eval₂ G polyFun (Pi.evalRingHom (fun _ : ℂ => ℂ) z) b
  rw [Pi.evalRingHom_apply] at h2
  rw [h2, evalQ2]
  congr 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp [polyFun]
  · simp [polyFun]

/-- $j_N \circ \gamma_c^{-1}$ is a root of $F_N(j, Y)$ in the germs. -/
theorem aeval_rootGerm (c : Cosets N) :
    ((modPolyQ (prop2_4' N)).map (algebraMap ℚ[X] (RatFunc ℚ))).eval₂ (algebraMap (RatFunc ℚ) (FinField τ₀))
      (rootGerm τ₀ N c) = 0 := by
  have hcomp : (algebraMap (RatFunc ℚ) (FinField τ₀)).comp (algebraMap ℚ[X] (RatFunc ℚ)) = polyToMero τ₀ :=
    RingHom.ext fun p => ratToMero_algebraMap τ₀ p
  rw [Polynomial.eval₂_map, hcomp]
  apply Subtype.ext
  rw [rootGerm, val_eval₂_polyToMero]
  have : (fun z => evalQ2 (modPolyQ (prop2_4' N)) (jFun (ofComplex z)) ((cosetRoot N c ∘ ofComplex) z)) =
      (0 : ℂ → ℂ) := by
    funext z
    exact evalQ2_modPolyQ_cosetRoot N c _
  rw [this]
  rfl

/-- **The embedding $\sigma_c$ at $\tau_0$**: $j \mapsto j$, $j_N \mapsto j_N \circ \gamma_c^{-1}$. -/
def finEmb (c : Cosets N) : X0 N →ₐ[RatFunc ℚ] FinField τ₀ :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId (RatFunc ℚ) (FinField τ₀)) (rootGerm τ₀ N c) (aeval_rootGerm τ₀ N c)

theorem finEmb_root (c : Cosets N) : finEmb τ₀ N c (AdjoinRoot.root _) = rootGerm τ₀ N c :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- **The $\mu$ embeddings at $\tau_0$ are distinct.** -/
theorem finEmb_injective : Function.Injective (finEmb τ₀ N) := by
  intro c c' h
  have hy : rootGerm τ₀ N c = rootGerm τ₀ N c' := by rw [← finEmb_root, ← finEmb_root, h]
  rw [rootGerm, rootGerm, MeroGerm.mk_eq_mk] at hy
  apply cosetRoot_injective (one_le_N N)
  have hd : MDiff (cosetRoot N c - cosetRoot N c') :=
    (cosetRoot_mdiff (one_le_N N) c).sub (cosetRoot_mdiff (one_le_N N) c')
  have h0 : ∀ᶠ z in 𝓝[≠] τ₀, (cosetRoot N c - cosetRoot N c') z = 0 := by
    refine eventually_of_comp_ofComplex (p := fun z => (cosetRoot N c - cosetRoot N c') z = 0) ?_
    filter_upwards [hy] with w hw
    simp only [Pi.sub_apply]
    exact sub_eq_zero.2 hw
  exact sub_eq_zero.1 (UpperHalfPlane.eq_zero_of_frequently hd h0.frequently)

end NumberFieldKB.ModularCurves
