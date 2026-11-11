import NumberFieldKB.ModularCurves.Places
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The chart of $X_0(N)$ at the cusps: the integral closure of $\mathbb Q[1/j]$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf p. 195). The nonsingular projective curve $X_0(N)$
over $\mathbb Q$ is covered by two smooth affine curves: $Y_0(N)$, with coordinate ring the integral closure of
$\mathbb Q[j]$ (`Y0Ring N`), and the chart at the cusps, with coordinate ring the integral closure of
$\mathbb Q[1/j]$ (`cuspRing N`). To make $\mathbb Q(X_0(N))$ an algebra over $\mathbb Q(t)$ via $t \mapsto 1/j$
without clashing with $t \mapsto j$, the field is copied to the type `XInf N`.

* `invXEquiv`: the automorphism $t \mapsto 1/t$ of $\mathbb Q(t)$.
* `XInf N` is a function field over $\mathbb Q$ via $t \mapsto 1/j$ (`functionField_XInf`), so `cuspRing N` is a
  Dedekind domain with field of fractions $\mathbb Q(X_0(N))$.
-/

open Polynomial IsDedekindDomain

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC

/-! ### The automorphism $t \mapsto 1/t$ of $\mathbb Q(t)$ -/

/-- An element `t` of a field `L` of characteristic zero with $\mathbb Q[X] \to L$, $X \mapsto t$, injective
gives $\mathbb Q(t) \to L$, $t \mapsto t$. -/
noncomputable def ratFuncLift {L : Type*} [Field L] [CharZero L] (t : L)
    (ht : Function.Injective (eval₂RingHom (Rat.castHom L) t)) : RatFunc ℚ →+* L :=
  RatFunc.liftRingHom (eval₂RingHom (Rat.castHom L) t)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ ht)

theorem ratFuncLift_algebraMap {L : Type*} [Field L] [CharZero L] (t : L)
    (ht : Function.Injective (eval₂RingHom (Rat.castHom L) t)) (p : ℚ[X]) :
    ratFuncLift t ht (algebraMap ℚ[X] (RatFunc ℚ) p) = eval₂ (Rat.castHom L) t p := by
  have h := RatFunc.liftRingHom_apply_div (φ := eval₂RingHom (Rat.castHom L) t)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ ht) p 1
  rw [map_one, div_one, map_one, div_one] at h
  exact h

theorem ratFuncLift_X {L : Type*} [Field L] [CharZero L] (t : L)
    (ht : Function.Injective (eval₂RingHom (Rat.castHom L) t)) : ratFuncLift t ht RatFunc.X = t := by
  rw [← RatFunc.algebraMap_X, ratFuncLift_algebraMap, eval₂_X]

/-- Ring maps out of $\mathbb Q(t)$ agree if they agree on $t$. -/
theorem ratFunc_ringHom_ext {L : Type*} [CommRing L] {f g : RatFunc ℚ →+* L} (h : f RatFunc.X = g RatFunc.X) :
    f = g := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors ℚ[X])
  apply Polynomial.ringHom_ext
  · intro a
    exact RingHom.congr_fun (RingHom.ext_rat ((f.comp (algebraMap ℚ[X] (RatFunc ℚ))).comp C)
      ((g.comp (algebraMap ℚ[X] (RatFunc ℚ))).comp C)) a
  · simpa [RatFunc.algebraMap_X] using h

/-- For a ring map `f` out of $\mathbb Q(t)$, evaluation at $f(t)$ is `f` on polynomials. -/
theorem eval₂RingHom_eq_comp {L : Type*} [Field L] [CharZero L] (f : RatFunc ℚ →+* L) :
    eval₂RingHom (Rat.castHom L) (f RatFunc.X) = f.comp (algebraMap ℚ[X] (RatFunc ℚ)) := by
  apply Polynomial.ringHom_ext
  · intro a
    exact RingHom.congr_fun (RingHom.ext_rat ((eval₂RingHom (Rat.castHom L) (f RatFunc.X)).comp C)
      ((f.comp (algebraMap ℚ[X] (RatFunc ℚ))).comp C)) a
  · simp [RatFunc.algebraMap_X]

theorem injective_eval₂RingHom {L : Type*} [Field L] [CharZero L] (f : RatFunc ℚ →+* L) :
    Function.Injective (eval₂RingHom (Rat.castHom L) (f RatFunc.X)) := by
  rw [eval₂RingHom_eq_comp]
  exact f.injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))

theorem injective_eval₂RingHom_inv_X :
    Function.Injective (eval₂RingHom (Rat.castHom (RatFunc ℚ)) RatFunc.X⁻¹) := by
  letI : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
  have ht : Transcendental ℚ (RatFunc.X⁻¹ : RatFunc ℚ) := fun h =>
    RatFunc.transcendental_X (IsAlgebraic.inv_iff.1 h)
  have e : eval₂RingHom (Rat.castHom (RatFunc ℚ)) RatFunc.X⁻¹ = (aeval (RatFunc.X⁻¹ : RatFunc ℚ)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      exact RingHom.congr_fun (RingHom.ext_rat ((eval₂RingHom (Rat.castHom (RatFunc ℚ)) RatFunc.X⁻¹).comp C)
        ((aeval (RatFunc.X⁻¹ : RatFunc ℚ)).toRingHom.comp C)) a
    · simp
  rw [e]
  exact transcendental_iff_injective.1 ht

/-- The map $t \mapsto 1/t$ of $\mathbb Q(t)$. -/
noncomputable def invXHom : RatFunc ℚ →+* RatFunc ℚ := ratFuncLift _ injective_eval₂RingHom_inv_X

theorem invXHom_X : invXHom RatFunc.X = RatFunc.X⁻¹ := ratFuncLift_X _ _

theorem invXHom_invXHom (f : RatFunc ℚ) : invXHom (invXHom f) = f := by
  have : (invXHom.comp invXHom) = RingHom.id _ := by
    apply ratFunc_ringHom_ext
    simp [invXHom_X]
  exact RingHom.congr_fun this f

/-- **The automorphism $t \mapsto 1/t$ of $\mathbb Q(t)$.** -/
noncomputable def invXEquiv : RatFunc ℚ ≃+* RatFunc ℚ where
  toFun := invXHom
  invFun := invXHom
  left_inv := invXHom_invXHom
  right_inv := invXHom_invXHom
  map_mul' := map_mul _
  map_add' := map_add _

/-! ### $\mathbb Q(X_0(N))$ over $\mathbb Q(1/j)$ -/

variable {N : ℕ} [NeZero N]

instance (N : ℕ) [NeZero N] : CharZero (X0 N) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (X0 N)).injective

theorem injective_eval₂RingHom_jX0_inv :
    Function.Injective (eval₂RingHom (Rat.castHom (X0 N)) (jX0 (prop2_4' N))⁻¹) := by
  have e : (jX0 (prop2_4' N))⁻¹ = ((algebraMap (RatFunc ℚ) (X0 N)).comp invXHom) RatFunc.X := by
    rw [RingHom.comp_apply, invXHom_X, map_inv₀, algebraMap_X_X0]
  rw [e]
  exact injective_eval₂RingHom _

/-- $\mathbb Q(X_0(N))$, to be viewed as an algebra over $\mathbb Q(t)$ via $t \mapsto 1/j$. -/
def XInf (N : ℕ) [NeZero N] : Type := X0 N

noncomputable instance : Field (XInf N) := inferInstanceAs (Field (X0 N))

noncomputable instance : Algebra ℚ (XInf N) := inferInstanceAs (Algebra ℚ (X0 N))

/-- The identity $\mathbb Q(X_0(N)) \to$ `XInf N`. -/
noncomputable def toXInf : X0 N ≃ₐ[ℚ] XInf N := AlgEquiv.refl

noncomputable instance algebraRatFuncXInf : Algebra (RatFunc ℚ) (XInf N) :=
  (ratFuncLift (L := X0 N) _ injective_eval₂RingHom_jX0_inv).toAlgebra

noncomputable instance algebraPolyXInf : Algebra ℚ[X] (XInf N) :=
  ((algebraMap (RatFunc ℚ) (XInf N)).comp (algebraMap ℚ[X] (RatFunc ℚ))).toAlgebra

instance : IsScalarTower ℚ[X] (RatFunc ℚ) (XInf N) := IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem algebraMap_XInf_X : algebraMap (RatFunc ℚ) (XInf N) RatFunc.X = toXInf (jX0 (prop2_4' N))⁻¹ :=
  ratFuncLift_X (L := X0 N) _ _

/-- $\mathbb Q(X_0(N))$ is finite over $\mathbb Q(1/j) = \mathbb Q(j)$. -/
theorem functionField_XInf : FunctionField ℚ (XInf N) := by
  haveI : Module.Finite (RatFunc ℚ) (X0 N) := functionField_X0
  refine Module.Finite.of_equiv_equiv invXEquiv toXInf.toRingEquiv ?_
  apply ratFunc_ringHom_ext
  change algebraMap (RatFunc ℚ) (XInf N) (invXHom RatFunc.X) = toXInf (algebraMap (RatFunc ℚ) (X0 N) RatFunc.X)
  rw [invXHom_X, map_inv₀, algebraMap_XInf_X, algebraMap_X_X0, map_inv₀, inv_inv]

instance : FunctionField ℚ (XInf N) := functionField_XInf

/-- **The coordinate ring of the chart of $X_0(N)$ at the cusps**: the integral closure of $\mathbb Q[1/j]$ in
$\mathbb Q(X_0(N))$. -/
@[kb "milne2006ec" "Ch. V, §2, X_0(N) as the nonsingular projective curve over Q (running text), pdf p. 195"]
abbrev cuspRing (N : ℕ) [NeZero N] : Type := FunctionField.ringOfIntegers ℚ (XInf N)

example : IsDedekindDomain (cuspRing N) := inferInstance

example : IsFractionRing (cuspRing N) (XInf N) := inferInstance

end NumberFieldKB.ModularCurves
