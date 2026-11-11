import NumberFieldKB.ModularCurves.ComplexLocal
import NumberFieldKB.ModularCurves.ComplexCuspDeriv
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Polynomials in $j, j_N$ inside $\mathbb C(X_0(N))$, their germs and expansions

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2–3 (pdf pp. 192–199). `mkC N G` is the class of
$G(j, j_N)$ in $\mathbb C(X_0(N))$ for $G \in \mathbb C[X][Y]$; it vanishes iff $G(j, j_N) = 0$ on $\mathbb H$
(`mkC_eq_zero_iff`), every element is $G(j,j_N)/d(j)$ (`exists_eq_div_mkC`), the germ of $\sigma_c(G(j,j_N))$ at
$\tau$ is the germ of $G(j, j_N \circ \gamma_c^{-1})$ (`finEmbC_mkC`), and its expansion at the cusp is
$G(J(q^N), Y_c)$ (`cuspEmbC_mkC`).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped WithZero

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable (N : ℕ) [NeZero N]

/-- $G \mapsto G(j, j_N)$, $\mathbb C[X][Y] \to \mathbb C(X_0(N))$. -/
def mkC : ℂ[X][X] →+* X0C N :=
  (AdjoinRoot.mk _).comp (mapRingHom (algebraMap ℂ[X] (RatFunc ℂ)))

theorem mkC_apply (G : ℂ[X][X]) : mkC N G = AdjoinRoot.mk _ (G.map (algebraMap ℂ[X] (RatFunc ℂ))) := rfl

/-- **$G(j, j_N) = 0$ in $\mathbb C(X_0(N))$ iff $G(j, j_N) = 0$ on $\mathbb H$.** -/
theorem mkC_eq_zero_iff (G : ℂ[X][X]) : mkC N G = 0 ↔ evalJJNC N G = 0 := by
  rw [show evalJJNC N G = 0 ↔ G ∈ RingHom.ker (evalJJNC N) from RingHom.mem_ker.symm, ker_evalJJNC_eq,
    Ideal.mem_span_singleton, mkC_apply, AdjoinRoot.mk_eq_zero]
  have hm := modPolyQC_monic N
  have hinj : Function.Injective (algebraMap ℂ[X] (RatFunc ℂ)) := IsFractionRing.injective _ _
  constructor
  · intro hx
    have h1 : (G %ₘ modPolyQC N).map (algebraMap ℂ[X] (RatFunc ℂ)) = 0 := by
      rw [map_modByMonic _ hm]
      exact (modByMonic_eq_zero_iff_dvd (hm.map _)).2 hx
    have h2 : G %ₘ modPolyQC N = 0 := by
      rw [← Polynomial.map_zero (algebraMap ℂ[X] (RatFunc ℂ))] at h1
      exact Polynomial.map_injective _ hinj h1
    exact (modByMonic_eq_zero_iff_dvd hm).1 h2
  · intro h
    exact Polynomial.map_dvd _ h

theorem mkC_C_C (a : ℂ) : mkC N (C (C a)) = algebraMap ℂ (X0C N) a := by
  rw [mkC_apply, Polynomial.map_C, AdjoinRoot.mk_C, IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) (X0C N),
    AdjoinRoot.algebraMap_eq]
  congr 1

theorem mkC_C (d : ℂ[X]) : mkC N (C d) = algebraMap (RatFunc ℂ) (X0C N) (algebraMap ℂ[X] (RatFunc ℂ) d) := by
  rw [mkC_apply, Polynomial.map_C, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

/-- **Every element of $\mathbb C(X_0(N))$ is $G(j, j_N)/d(j)$.** -/
theorem exists_eq_div_mkC (z : X0C N) : ∃ (G : ℂ[X][X]) (d : ℂ[X]), d ≠ 0 ∧ z = mkC N G / mkC N (C d) := by
  induction z using AdjoinRoot.induction_on with
  | ih P =>
    obtain ⟨b, hb, hG⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℂ[X]) P
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    refine ⟨IsLocalization.integerNormalization (nonZeroDivisors ℂ[X]) P, b, hb0, ?_⟩
    have hof : mkC N (C b) ≠ 0 := by
      rw [mkC_C]
      exact (_root_.map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).2 hb0)
    rw [eq_div_iff hof, mkC_C, mkC_apply N (IsLocalization.integerNormalization _ P), hG, Algebra.smul_def, map_mul,
      mul_comm, Polynomial.algebraMap_apply, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

/-! ### Germs and expansions -/

/-- $z \mapsto G(j(z), j_N(\gamma_c^{-1} z))$, in the coordinate $z \in \mathbb C$. -/
def polyFun2 (G : ℂ[X][X]) (c : Cosets N) (z : ℂ) : ℂ :=
  (G.map (evalRingHom (jFun (ofComplex z)))).eval (cosetRoot N c (ofComplex z))

theorem polyFun2_eq_sum (G : ℂ[X][X]) (c : Cosets N) :
    polyFun2 N G c = fun z => ∑ i ∈ Finset.range (G.natDegree + 1),
      (G.coeff i).eval (jFun (ofComplex z)) * cosetRoot N c (ofComplex z) ^ i := by
  funext z
  rw [polyFun2, eval_eq_sum_range' (lt_of_le_of_lt (natDegree_map_le) (Nat.lt_succ_self _))]
  simp only [coeff_map, coe_evalRingHom]

theorem analyticAt_polyFun2 (G : ℂ[X][X]) (c : Cosets N) (τ : ℍ) : AnalyticAt ℂ (polyFun2 N G c) (τ : ℂ) := by
  rw [polyFun2_eq_sum]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  refine AnalyticAt.mul ?_ ?_
  · exact ((Polynomial.differentiable (G.coeff i)).analyticAt _).comp (analyticAt_jFun τ)
  · exact (analyticAt_comp_ofComplex (cosetRoot_mdiff (one_le_N N) c) τ).pow i

/-- The germ of $G(j, j_N \circ \gamma_c^{-1})$ at $\tau$. -/
def polyGerm2 (G : ℂ[X][X]) (c : Cosets N) (τ : ℍ) : FinField τ :=
  MeroGerm.mk (polyFun2 N G c) (analyticAt_polyFun2 N G c τ).meromorphicAt

/-- **The germ of $\sigma_c(G(j, j_N))$ at $\tau$ is the germ of $G(j, j_N \circ \gamma_c^{-1})$.** -/
theorem finEmbC_mkC (τ : ℍ) (c : Cosets N) (G : ℂ[X][X]) : finEmbC τ N c (mkC N G) = polyGerm2 N G c τ := by
  have hcomp : (algebraMap (RatFunc ℂ) (FinField τ)).comp (algebraMap ℂ[X] (RatFunc ℂ)) = polyToMeroC τ :=
    RingHom.ext fun p => ratToMeroC_algebraMap τ p
  have e1 : finEmbC τ N c (mkC N G) = G.eval₂ (polyToMeroC τ) (rootGerm τ N c) := by
    rw [mkC_apply, ← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, finEmbC_root, Polynomial.aeval_def,
      Polynomial.eval₂_map, hcomp]
  rw [e1]
  apply Subtype.ext
  have h := Polynomial.hom_eval₂ G (polyToMeroC τ) (meroSubring (τ : ℂ)).subtype (rootGerm τ N c)
  rw [Subring.coe_subtype] at h
  change ((G.eval₂ (polyToMeroC τ) (rootGerm τ N c) : MeroGerm (τ : ℂ)) : PGerm (τ : ℂ)) = _ at h
  rw [h]
  have hc : (meroSubring (τ : ℂ)).subtype.comp (polyToMeroC τ) =
      (Filter.Germ.coeRingHom (𝓝[≠] (τ : ℂ))).comp polyFunC := RingHom.ext fun p => rfl
  have hr : ((rootGerm τ N c : MeroGerm (τ : ℂ)) : PGerm (τ : ℂ)) =
      Filter.Germ.coeRingHom _ (cosetRoot N c ∘ ofComplex) := rfl
  rw [hc, hr, ← Polynomial.hom_eval₂]
  change ((G.eval₂ polyFunC (cosetRoot N c ∘ ofComplex) : ℂ → ℂ) : PGerm (τ : ℂ)) = ((polyFun2 N G c : ℂ → ℂ) : _)
  congr 1
  funext z
  have h2 := Polynomial.hom_eval₂ G polyFunC (Pi.evalRingHom (fun _ : ℂ => ℂ) z) (cosetRoot N c ∘ ofComplex)
  rw [Pi.evalRingHom_apply] at h2
  rw [h2, polyFun2, Polynomial.eval_map]
  congr 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp [polyFunC]
  · simp [polyFunC]

/-- **The expansion of $\sigma_c(G(j, j_N))$ at the cusp is $G(J(q^N), Y_c)$.** -/
theorem cuspEmbC_mkC (c : Cosets N) (G : ℂ[X][X]) :
    @Eq (CuspField N) (cuspEmbC N c (mkC N G)) (G.eval₂ (polyToLaurentC (jNSer N)) (ySer N c)) := by
  have hcomp : (algebraMap (RatFunc ℂ) (CuspField N)).comp (algebraMap ℂ[X] (RatFunc ℂ)) =
      polyToLaurentC (jNSer N) :=
    RingHom.ext fun p => ratFuncToLaurentC_algebraMap (valuation_jNSer' N) (one_le_N N) p
  rw [mkC_apply, ← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, cuspEmbC_root, Polynomial.aeval_def,
    Polynomial.eval₂_map, hcomp]

end NumberFieldKB.ModularCurves
