import NumberFieldKB.ModularCurves.Y0
import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Ramification in $Y_0(M) \to Y_0(N)$: the fundamental identity

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2–§4. For $N \mid M$ the map $z \mapsto z$ gives a finite
morphism $Y_0(M) \to Y_0(N)$ of smooth affine curves over $\mathbb Q$ (`degeneracyY0_isIntegral`). Here
$\mathcal O(Y_0(M))$ is made a finite flat $\mathcal O(Y_0(N))$-algebra (`forgetY0Algebra`), and the fundamental
identity $\sum_{Q \mid P} e(Q/P) f(Q/P) = (\Gamma_0(N) : \Gamma_0(M))$ is proved for every closed point $P$ of
$Y_0(N)$ (`sum_ramification_inertia_forget`). For $N = 1$ the degree is $(\Gamma_0(1) : \Gamma_0(M))$, the number
$\mu$ in the genus formula.
-/

open Polynomial

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- $\mathcal O(Y_0(M))$ as an algebra over $\mathcal O(Y_0(N))$ via $z \mapsto z$, for $N \mid M$. -/
noncomputable abbrev forgetY0Algebra (N M : ℕ) [NeZero N] [NeZero M] (h : 1 * N ∣ M) :
    Algebra (Y0Ring N) (Y0Ring M) :=
  (degeneracyY0 N M 1 h).toAlgebra

/-- The map $z \mapsto z$ is compatible with $j$ on the coordinate rings. -/
theorem degeneracyY0_one_comp_algebraMap (h : 1 * N ∣ M) :
    (degeneracyY0 N M 1 h).comp (algebraMap ℚ[X] (Y0Ring N)) = algebraMap ℚ[X] (Y0Ring M) := by
  refine RingHom.ext fun p => Subtype.ext ?_
  change degeneracy N M 1 h (algebraMap ℚ[X] (X0 N) p) = algebraMap ℚ[X] (X0 M) p
  rw [← RingHom.comp_apply, degeneracy_comp_algebraMap, jNElt_one, algebraMap_polyX0_eq]

theorem isScalarTower_forgetY0 (h : 1 * N ∣ M) :
    letI := forgetY0Algebra N M h
    IsScalarTower ℚ[X] (Y0Ring N) (Y0Ring M) := by
  letI := forgetY0Algebra N M h
  exact IsScalarTower.of_algebraMap_eq fun r =>
    (RingHom.congr_fun (degeneracyY0_one_comp_algebraMap h) r).symm

/-- $\mathcal O(Y_0(M))$ is a finite $\mathcal O(Y_0(N))$-module. -/
theorem finite_forgetY0 (h : 1 * N ∣ M) :
    letI := forgetY0Algebra N M h
    Module.Finite (Y0Ring N) (Y0Ring M) := by
  letI := forgetY0Algebra N M h
  haveI := isScalarTower_forgetY0 h
  exact Module.Finite.of_restrictScalars_finite ℚ[X] (Y0Ring N) (Y0Ring M)

/-- $\mathcal O(Y_0(M))$ is a torsion-free (hence flat) $\mathcal O(Y_0(N))$-module. -/
theorem isTorsionFree_forgetY0 (h : 1 * N ∣ M) :
    letI := forgetY0Algebra N M h
    Module.IsTorsionFree (Y0Ring N) (Y0Ring M) := by
  letI := forgetY0Algebra N M h
  exact Module.isTorsionFree_iff_algebraMap_injective.2 (degeneracyY0_injective h)

/-- The rank of $\mathcal O(Y_0(M))$ over $\mathcal O(Y_0(N))$ is the degree $(\Gamma_0(N) : \Gamma_0(M))$. -/
theorem finrank_forgetY0 (h : 1 * N ∣ M) :
    letI := forgetY0Algebra N M h
    Module.finrank (Y0Ring N) (Y0Ring M) =
      (CongruenceSubgroup.Gamma0 M).relIndex (CongruenceSubgroup.Gamma0 N) := by
  letI := forgetY0Algebra N M h
  letI := forgetAlgebra N M h
  letI : Algebra (Y0Ring N) (X0 M) :=
    ((algebraMap (X0 N) (X0 M)).comp (algebraMap (Y0Ring N) (X0 N))).toAlgebra
  have t1 : @IsScalarTower (Y0Ring N) (X0 N) (X0 M) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have t2 : @IsScalarTower (Y0Ring N) (Y0Ring M) (X0 M) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← @IsFractionRing.finrank_eq (Y0Ring N) (X0 N) (Y0Ring M) (X0 M) _ _ _ _ _ _ _ _ _ t1 t2 _ _,
    finrank_forget h]

/-- There are finitely many closed points of $Y_0(M)$ above a closed point of $Y_0(N)$. -/
@[instance_reducible]
noncomputable def fintypePrimesOverY0 (h : 1 * N ∣ M) (P : Y0Point N) :
    letI := forgetY0Algebra N M h
    Fintype (P.asIdeal.primesOver (Y0Ring M)) := by
  letI := forgetY0Algebra N M h
  haveI := finite_forgetY0 h
  haveI : Algebra.IsIntegral (Y0Ring N) (Y0Ring M) := Algebra.IsIntegral.of_finite _ _
  haveI := P.isMaximal
  haveI := isTorsionFree_forgetY0 h
  exact Set.Finite.fintype (IsDedekindDomain.primesOver_finite P.asIdeal (Y0Ring M))

/-- **The fundamental identity for $Y_0(M) \to Y_0(N)$** ($N \mid M$): for every closed point $P$ of $Y_0(N)$,
$\sum_{Q \mid P} e(Q/P)\, f(Q/P) = (\Gamma_0(N) : \Gamma_0(M))$, the sum over the closed points $Q$ of $Y_0(M)$
above $P$. -/
@[kb "milne2006ec" "Ch. V, §2, the degree of X_0(N) → X_0(1) as a sum of ramification indices (running text), pdf p. 196"]
theorem sum_ramification_inertia_forget (h : 1 * N ∣ M) (P : Y0Point N) :
    letI := forgetY0Algebra N M h
    letI := fintypePrimesOverY0 h P
    ∑ Q : P.asIdeal.primesOver (Y0Ring M), Q.1.ramificationIdx (Y0Ring N) * Q.1.inertiaDeg (Y0Ring N) =
      (CongruenceSubgroup.Gamma0 M).relIndex (CongruenceSubgroup.Gamma0 N) := by
  letI := forgetY0Algebra N M h
  letI := fintypePrimesOverY0 h P
  haveI := finite_forgetY0 h
  haveI := P.isMaximal
  haveI := isTorsionFree_forgetY0 h
  rw [Ideal.sum_ramification_inertia_eq_finrank, finrank_forgetY0]

end NumberFieldKB.ModularCurves
