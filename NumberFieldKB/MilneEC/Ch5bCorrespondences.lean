import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Algebra.Module.StablyFree.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch1MapsCounterexample

/-!
# Milne, Elliptic Curves, Chapter V §7: correspondences of curves

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter V, Section 7, "The ring of
correspondences of a curve", Remarks 7.1 and 7.2, pdf pp. 224–225.

A correspondence $T\colon X \vdash X'$ of nonsingular projective curves is a pair of finite surjective regular maps
$X \xleftarrow{\alpha} Y \xrightarrow{\beta} X'$.

## Remark 7.1 (extension from open subsets)
Milne: a regular map $U \to U'$ of curves with finitely many points removed extends uniquely to $X \to X'$; applying
this twice, a correspondence $U \vdash U'$ extends uniquely to $X \vdash X'$.  Here the curves are nonsingular
projective plane curves and $U = X \cap \{Z \neq 0\}$ (the setting of the named statement `Prop4_18`, Chapter I 4.18,
to which Milne refers): `remark_7_1` proves the extension of correspondences from `Prop4_18`.

## Remark 7.2 (pulling back functions)
In terms of function fields, $\alpha$ and $\beta$ are embeddings $\alpha^*\colon k(X) \to k(Y)$ (finite) and
$\beta^*\colon k(X') \to k(Y)$, and Milne's $T(f)(P) = \sum_i f(\beta Q_i)$ (the $Q_i$ the points of
$\alpha^{-1}(P)$ with multiplicity) is $T(f) = \operatorname{Tr}_{k(Y)/k(X)}(\beta^* f)$: the trace is the sum of the
values over the fibre.  `pullbackFun` is this map.  Proved:
* `pullbackFun` is $k$-linear, and on constants $T(c) = \deg(\alpha)\, c$ (`pullbackFun_algebraMap`; on a projective
  curve the regular functions are the constants).
* `remark_7_2_regular`: $T(f)$ is regular at a point $P$ of $X$ (lies in the valuation ring $\mathcal O_P$) whenever
  $\beta^* f$ is regular at every point of $Y$ over $P$, i.e. integral over $\mathcal O_P$ (the integral closure of
  $\mathcal O_P$ in $k(Y)$ is the intersection of the $\mathcal O_Q$ for $Q$ over $P$).

Not formalized: the action on holomorphic differentials and on divisors (and hence the ring of correspondences
$A(X) \subseteq \operatorname{End}(J(X))$, which needs the pullback of divisors along $\alpha$).
-/

universe u

namespace NumberFieldKB.MilneEC

open MvPolynomial

/-! ## Remark 7.1 -/

/-- **Remark 7.1** (pdf p. 225), for nonsingular projective plane curves and their affine pieces $Z \neq 0$, from
Proposition 4.18 (named statement `Prop4_18`): a correspondence $U \vdash U'$ given by regular maps
$f\colon Y \cap U_2 \to X \cap U_2$ and $g\colon Y \cap U_2 \to X' \cap U_2$ extends to a correspondence
$X \vdash X'$ of the projective curves, uniquely on points. -/
@[kb "milne2006ec" "Ch. V, Remark 7.1, pdf p. 225"]
theorem remark_7_1 (h : Prop4_18) (k : Type) [Field k] [PerfectField k] (G F F' : MvPolynomial (Fin 3) k)
    (hG : IsProjectivePlaneCurve G) (hGn : IsNonsingularProjCurve G) (hF : IsProjectivePlaneCurve F)
    (hFn : IsNonsingularProjCurve F) (hF' : IsProjectivePlaneCurve F') (hFn' : IsNonsingularProjCurve F')
    (hGX : ¬ G ∣ X 2) (hFX : ¬ F ∣ X 2) (hFX' : ¬ F' ∣ X 2)
    (f : Fin 2 → coordinateRing (dehomogenize 2 G)) (hf : IsAffineRegularMap (dehomogenize 2 G) (dehomogenize 2 F) f)
    (g : Fin 2 → coordinateRing (dehomogenize 2 G))
    (hg : IsAffineRegularMap (dehomogenize 2 G) (dehomogenize 2 F') g) :
    ∃ (α : ProjRegularMap G F) (β : ProjRegularMap G F'), α.Extends f ∧ β.Extends g ∧
      (∀ α' : ProjRegularMap G F, α'.Extends f → ∀ (K : Type) [Field K] [Algebra k K], α'.toFun K = α.toFun K) ∧
      (∀ β' : ProjRegularMap G F', β'.Extends g → ∀ (K : Type) [Field K] [Algebra k K], β'.toFun K = β.toFun K) := by
  obtain ⟨α, hα, hαu⟩ := h.extends_unique k G F hG hGn hF hFn hGX hFX f hf
  obtain ⟨β, hβ, hβu⟩ := h.extends_unique k G F' hG hGn hF' hFn' hGX hFX' g hg
  exact ⟨α, β, hα, hβ, hαu, hβu⟩

/-- **Remark 7.1, corrected** (pdf p. 225), from the corrected Proposition 4.18 (`Prop4_18Corrected`; the named
statement `Prop4_18` used by `remark_7_1` is false as stated, `not_prop4_18`): the correspondence extends, uniquely on
the points over algebraically closed fields. -/
@[kb "milne2006ec" "Ch. V, Remark 7.1, pdf p. 225 (from the corrected Prop. I.4.18)"]
theorem remark_7_1_corrected (h : Prop4_18Corrected) (k : Type) [Field k] [PerfectField k]
    (G F F' : MvPolynomial (Fin 3) k)
    (hG : IsProjectivePlaneCurve G) (hGn : IsNonsingularProjCurve G) (hF : IsProjectivePlaneCurve F)
    (hFn : IsNonsingularProjCurve F) (hF' : IsProjectivePlaneCurve F') (hFn' : IsNonsingularProjCurve F')
    (hGX : ¬ G ∣ X 2) (hFX : ¬ F ∣ X 2) (hFX' : ¬ F' ∣ X 2)
    (f : Fin 2 → coordinateRing (dehomogenize 2 G)) (hf : IsAffineRegularMap (dehomogenize 2 G) (dehomogenize 2 F) f)
    (g : Fin 2 → coordinateRing (dehomogenize 2 G))
    (hg : IsAffineRegularMap (dehomogenize 2 G) (dehomogenize 2 F') g) :
    ∃ (α : ProjRegularMap G F) (β : ProjRegularMap G F'), α.Extends f ∧ β.Extends g ∧
      (∀ α' : ProjRegularMap G F, α'.Extends f →
        ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra k K], α'.toFun K = α.toFun K) ∧
      (∀ β' : ProjRegularMap G F', β'.Extends g →
        ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra k K], β'.toFun K = β.toFun K) := by
  obtain ⟨α, hα, hαu⟩ := h.extends_unique k G F hG hGn hF hFn hGX hFX f hf
  obtain ⟨β, hβ, hβu⟩ := h.extends_unique k G F' hG hGn hF' hFn' hGX hFX' g hg
  exact ⟨α, β, hα, hβ, hαu, hβu⟩

/-! ## Remark 7.2 -/

section Pullback

variable (k : Type*) [Field k] (K K' L : Type*) [Field K] [Field K'] [Field L] [Algebra k K] [Algebra k K']
  [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L]

/-- **The pullback of functions by a correspondence** (Remark 7.2, pdf p. 225): for $X \xleftarrow{\alpha} Y
\xrightarrow{\beta} X'$ with $\alpha^*\colon K = k(X) \to L = k(Y)$ finite (the `Algebra K L` structure) and
$\beta^*\colon K' = k(X') \to L$, $T(f) = \operatorname{Tr}_{L/K}(\beta^* f)$, the sum of the values
$f(\beta Q_i)$ over the fibre $\alpha^{-1}(P)$. -/
@[kb "milne2006ec" "Ch. V, Remark 7.2, T(f) = Σ f(βQ_i), pdf p. 225"]
noncomputable def pullbackFun (β : K' →ₐ[k] L) : K' →ₗ[k] K :=
  ((Algebra.trace K L).restrictScalars k).comp β.toLinearMap

variable {k K K' L}

omit [FiniteDimensional K L] in
theorem pullbackFun_apply (β : K' →ₐ[k] L) (f : K') :
    pullbackFun k K K' L β f = Algebra.trace K L (β f) := rfl

/-- On constants, $T(c) = \deg(\alpha)\,c$ (pdf p. 225: the fibre $\alpha^{-1}(P)$ has $\deg \alpha$ points with
multiplicity). -/
theorem pullbackFun_algebraMap (β : K' →ₐ[k] L) (c : k) :
    pullbackFun k K K' L β (algebraMap k K' c) = (Module.finrank K L : K) * algebraMap k K c := by
  rw [pullbackFun_apply, AlgHom.commutes, IsScalarTower.algebraMap_apply k K L, Algebra.trace_algebraMap,
    nsmul_eq_mul]

/-- **Remark 7.2, regularity** (pdf p. 225): if $\beta^* f$ is regular at every point of $Y$ above the point $P$ of
$X$, i.e. integral over the valuation ring $\mathcal O_P \subseteq K$ (the integral closure of $\mathcal O_P$ in $L$
is the intersection of the valuation rings above it), then $T(f)$ is regular at $P$. -/
@[kb "milne2006ec" "Ch. V, Remark 7.2, T(f) is regular, pdf p. 225"]
theorem remark_7_2_regular (O : ValuationSubring K) (β : K' →ₐ[k] L) (f : K')
    (hf : letI : Algebra O L := ((algebraMap K L).comp (algebraMap O K)).toAlgebra
      IsIntegral O (β f)) :
    pullbackFun k K K' L β f ∈ O := by
  let _ : Algebra O L := ((algebraMap K L).comp (algebraMap O K)).toAlgebra
  have : IsScalarTower O K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hint : IsIntegral O (Algebra.trace K L (β f)) := Algebra.isIntegral_trace hf
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [pullbackFun_apply, ← hy]
  exact y.2

end Pullback

end NumberFieldKB.MilneEC
