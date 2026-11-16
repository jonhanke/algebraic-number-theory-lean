import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.Normed.Field.Lemmas
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch4bFiniteFields
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Milne, Elliptic Curves, Chapter IV §9: zeta functions of affine curves and the rationality of $Z(E, T)$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Section 9, pdf pp. 159–164.

**The Euler product.** For a finitely generated $\mathbb F_p$-algebra $R$ (for an affine plane curve $C : f = 0$,
$R = \mathbb F_p[x, y] = \mathbb F_p[X, Y]/(f)$), Milne's (32) is the formal product
$Z(C, T) = \prod_{\mathfrak p} (1 + T^{\deg \mathfrak p} + T^{2\deg \mathfrak p} + \cdots)$ over the maximal ideals
$\mathfrak p$ of $R$, $\deg \mathfrak p = [R/\mathfrak p : \mathbb F_p]$.  Multiplied out, the coefficient of $T^m$ is
the number of finitely supported families $(n_{\mathfrak p})$ of natural numbers with
$\sum n_{\mathfrak p} \deg \mathfrak p = m$ (positive divisors of degree $m$); this is the definition `eulerZeta`.

## Named statements
* `Prop9_8` (Proposition 9.8, pdf p. 162): $Z(C, T) = \exp\bigl(\sum_{m \ge 1} N_m T^m/m\bigr)$ with
  $N_m = \#C(\mathbb F_{p^m})$ the number of $\mathbb F_p$-algebra maps $R \to \mathbb F_{p^m}$.  Milne proves it
  (logarithmic derivative and counting homomorphisms); the proof is not formalized here.
* `Prop9_9` (Proposition 9.9, pdf p. 162): an elliptic curve over $\mathbb F_p$ has $N_1 (p^m - 1)/(p - 1)$ positive
  divisors of degree $m \ge 1$ (Riemann–Roch).

## Proved
* `example_9_7` (from `Prop9_8`): $Z(\mathbb A^1, T) = 1/(1 - pT)$.
* `theorem_9_10` (from `Prop9_8` and `Prop9_9`, Milne's proof): Theorem 9.10, so the input `Theorem9_10` of
  `Ch4bFiniteFields` follows from these two.
-/

open PowerSeries

namespace NumberFieldKB.MilneEC

variable {p : ℕ} [Fact p.Prime]

/-- The degree $[R/\mathfrak p : \mathbb F_p]$ of a maximal ideal. -/
noncomputable def maxDeg (R : Type*) [CommRing R] [Algebra (ZMod p) R] (𝔭 : MaximalSpectrum R) : ℕ :=
  Module.finrank (ZMod p) (R ⧸ 𝔭.asIdeal)

/-- **The zeta function of an affine curve as an Euler product** (pdf p. 160, (32)), multiplied out: the coefficient
of $T^m$ is the number of positive divisors $\sum n_{\mathfrak p}\mathfrak p$ of degree $m$. -/
@[kb "milne2006ec" "Ch. IV, §9, zeta function of an affine plane curve, pdf p. 159"]
noncomputable def eulerZeta (R : Type*) [CommRing R] [Algebra (ZMod p) R] : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    (Nat.card {D : MaximalSpectrum R →₀ ℕ // D.sum (fun 𝔭 n => n * maxDeg (p := p) R 𝔭) = m} : ℚ)

/-- $N_m(R) = \#\operatorname{Hom}_{\mathbb F_p}(R, \mathbb F_{p^m})$; for $R = \mathbb F_p[X, Y]/(f)$ this is
$\#C(\mathbb F_{p^m})$ (pdf p. 161). -/
noncomputable def homCount (R : Type*) [CommRing R] [Algebra (ZMod p) R] (m : ℕ) : ℕ :=
  Nat.card (R →ₐ[ZMod p] GaloisField p m)

/-- $\exp\bigl(\sum_{m \ge 1} a_m T^m / m\bigr)$. -/
noncomputable def expSeries (a : ℕ → ℚ) : PowerSeries ℚ :=
  (exp ℚ).subst (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else a m / m)

/-- The coordinate ring $\mathbb F_p[x, y] = \mathbb F_p[X][Y]/(f)$ of the affine plane curve $f = 0$ (bivariate
polynomials as Mathlib's `R[X][Y]`, as for Weierstrass curves). -/
abbrev planeCurveRing (p : ℕ) [Fact p.Prime] (f : Polynomial (Polynomial (ZMod p))) : Type :=
  Polynomial (Polynomial (ZMod p)) ⧸ Ideal.span {f}

/-- **Proposition 9.8** (named statement; pdf p. 162): for an affine plane curve $C : f(X, Y) = 0$ over $\mathbb F_p$
($f \neq 0$), $Z(C, T) = \exp\bigl(\sum_{m \ge 1} N_m T^m / m\bigr)$, $N_m = \#C(\mathbb F_{p^m})$, the number of
$\mathbb F_p$-algebra maps $\mathbb F_p[x, y] \to \mathbb F_{p^m}$. -/
@[kb "milne2006ec" "Ch. IV, Proposition 9.8, pdf p. 162 (input)"]
structure Prop9_8 (p : ℕ) [Fact p.Prime] : Prop where
  eq_exp : ∀ f : Polynomial (Polynomial (ZMod p)), f ≠ 0 →
    eulerZeta (p := p) (planeCurveRing p f) = expSeries fun m => (homCount (p := p) (planeCurveRing p f) m : ℚ)

/-! ### Calculus of the series `expSeries` -/

/-- $\sum_{m \ge 1} a_m T^m$. -/
noncomputable def logDerivSeries (a : ℕ → ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else a m

theorem logDerivSeries_add (a b : ℕ → ℚ) :
    logDerivSeries (fun m => a m + b m) = logDerivSeries a + logDerivSeries b := by
  ext n; simp only [logDerivSeries, coeff_mk, map_add]; split_ifs <;> simp

theorem constantCoeff_expArg (a : ℕ → ℚ) :
    constantCoeff (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else a m / m) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]; simp

theorem hasSubst_expArg (a : ℕ → ℚ) :
    HasSubst (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else a m / m) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_expArg a)

theorem constantCoeff_expSeries (a : ℕ → ℚ) : constantCoeff (expSeries a) = 1 := by
  have h := constantCoeff_subst_of_constantCoeff_zero
    (a := PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else a m / m)
    (constantCoeff_expArg a) (exp ℚ)
  unfold expSeries
  exact h.trans (by simp)

theorem expSeries_ode (a : ℕ → ℚ) :
    X * d⁄dX (expSeries a) = expSeries a * logDerivSeries a := by
  have hg := hasSubst_expArg a
  have hZ' : d⁄dX (expSeries a) = expSeries a *
      d⁄dX (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else a m / m) := by
    unfold expSeries
    rw [derivative_subst hg, derivative_exp]
  have hXS : X * d⁄dX (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else a m / m) =
      logDerivSeries a := by
    ext n
    cases n with
    | zero => simp [logDerivSeries]
    | succ n =>
      rw [coeff_succ_X_mul, coeff_derivative, logDerivSeries, coeff_mk, coeff_mk]
      simp only [Nat.succ_ne_zero, ite_false]
      push_cast
      field_simp
  rw [hZ', ← hXS]; ring

/-- A power series with constant coefficient `c` and `T Y' = Y * g`, `g(0) = 0`, is determined. -/
theorem ode_unique (g : PowerSeries ℚ) (hg : constantCoeff g = 0) {Y₁ Y₂ : PowerSeries ℚ}
    (h₀ : constantCoeff Y₁ = constantCoeff Y₂)
    (h₁ : X * d⁄dX Y₁ = Y₁ * g) (h₂ : X * d⁄dX Y₂ = Y₂ * g) : Y₁ = Y₂ := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simpa using h₀
    | succ k =>
      have e1 := congrArg (coeff (k + 1)) h₁
      have e2 := congrArg (coeff (k + 1)) h₂
      rw [coeff_succ_X_mul, coeff_derivative, coeff_mul] at e1 e2
      have hs : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), coeff x.1 Y₁ * coeff x.2 g =
          ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), coeff x.1 Y₂ * coeff x.2 g := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        by_cases h0 : x.2 = 0
        · have : coeff x.2 g = 0 := by rw [h0, coeff_zero_eq_constantCoeff_apply]; exact hg
          rw [this]; simp
        · rw [ih x.1 (by omega)]
      have : coeff (k + 1) Y₁ * ((k : ℚ) + 1) = coeff (k + 1) Y₂ * ((k : ℚ) + 1) := by
        rw [e1, e2]; exact hs
      exact mul_right_cancel₀ (by positivity) this

theorem expSeries_add (a b : ℕ → ℚ) :
    expSeries a * expSeries b = expSeries (fun m => a m + b m) := by
  refine ode_unique (logDerivSeries (fun m => a m + b m)) (by simp [logDerivSeries]) ?_ ?_ ?_
  · simp [constantCoeff_expSeries]
  · rw [Derivation.leibniz, logDerivSeries_add]
    simp only [smul_eq_mul]
    have h1 := expSeries_ode a
    have h2 := expSeries_ode b
    calc X * (expSeries a * d⁄dX (expSeries b) + expSeries b * d⁄dX (expSeries a))
        = expSeries a * (X * d⁄dX (expSeries b)) + expSeries b * (X * d⁄dX (expSeries a)) := by ring
      _ = _ := by rw [h1, h2]; ring
  · exact expSeries_ode _

theorem expSeries_congr (a b : ℕ → ℚ) (h : ∀ m, 1 ≤ m → a m = b m) : expSeries a = expSeries b := by
  have : (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else a m / m) =
      PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else b m / m := by
    ext m
    simp only [coeff_mk]
    split_ifs with h0
    · rfl
    · rw [h m (by omega)]
  unfold expSeries
  rw [this]

/-- The geometric series $\sum_{m \ge 1} u^m T^m$ over a commutative ring. -/
noncomputable def geomSer {R : Type*} [CommRing R] (u : R) : PowerSeries R :=
  PowerSeries.mk fun m => if m = 0 then 0 else u ^ m

theorem geomSer_mul {R : Type*} [CommRing R] (u : R) : geomSer u * (1 - C u * X) = C u * X := by
  ext n
  cases n with
  | zero => simp [geomSer]
  | succ n =>
    have e : geomSer u * (1 - C u * X) = geomSer u - C u * (geomSer u * X) := by ring
    rw [e, map_sub, coeff_C_mul, coeff_succ_mul_X, coeff_C_mul, coeff_X]
    cases n with
    | zero => simp [geomSer]
    | succ n => simp [geomSer]; ring

theorem expSeries_geom (c : ℚ) :
    expSeries (fun m => c ^ m) * (1 - C c * X) = 1 := by
  set Z := expSeries (fun m => c ^ m) with hZ
  have hode := expSeries_ode (fun m => c ^ m)
  have hL : logDerivSeries (fun m => c ^ m) = geomSer c := rfl
  rw [hL, ← hZ] at hode
  have hV : X * d⁄dX (Z * (1 - C c * X)) = 0 := by
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, map_sub, Derivation.map_one_eq_zero, derivative_X, Derivation.leibniz,
      derivative_C]
    have hg := geomSer_mul c
    calc _ = (X * d⁄dX Z) * (1 - C c * X) - C c * X * Z := by simp; ring
      _ = 0 := by rw [hode]; calc _ = Z * (geomSer c * (1 - C c * X)) - C c * X * Z := by ring
                                _ = 0 := by rw [hg]; ring
  have hV' : d⁄dX (Z * (1 - C c * X)) = 0 := by
    rcases mul_eq_zero.1 hV with h | h
    · exact absurd h X_ne_zero
    · exact h
  refine derivative.ext (by rw [hV', Derivation.map_one_eq_zero]) ?_
  simp [hZ, constantCoeff_expSeries]

/-! ### Algebra maps out of a plane curve ring -/

section PlaneHom

variable {K : Type*} [Field K] [Algebra (ZMod p) K]

/-- Evaluation of a bivariate polynomial at a point $(x, y)$, as an $\mathbb F_p$-algebra map. -/
noncomputable def evalPair (x y : K) :
    Polynomial (Polynomial (ZMod p)) →ₐ[ZMod p] K :=
  { Polynomial.eval₂RingHom (Polynomial.aeval x : Polynomial (ZMod p) →ₐ[ZMod p] K).toRingHom y with
    commutes' := fun c => by
      show Polynomial.eval₂ (Polynomial.aeval x : Polynomial (ZMod p) →ₐ[ZMod p] K).toRingHom y
        (algebraMap (ZMod p) (Polynomial (Polynomial (ZMod p))) c) = algebraMap (ZMod p) K c
      rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply]
      simp }

theorem evalPair_C (x y : K) (a : Polynomial (ZMod p)) : evalPair x y (Polynomial.C a) =
    Polynomial.aeval x a := by
  show Polynomial.eval₂ _ y (Polynomial.C a) = _
  simp

theorem evalPair_X (x y : K) : evalPair x y (Polynomial.X : Polynomial (Polynomial (ZMod p))) = y := by
  show Polynomial.eval₂ _ y Polynomial.X = _
  simp

theorem algHom_ext_pair {ψ₁ ψ₂ : Polynomial (Polynomial (ZMod p)) →ₐ[ZMod p] K}
    (hC : ψ₁ (Polynomial.C Polynomial.X) = ψ₂ (Polynomial.C Polynomial.X))
    (hX : ψ₁ Polynomial.X = ψ₂ Polynomial.X) : ψ₁ = ψ₂ := by
  have hc : ∀ c : ZMod p, ψ₁ (Polynomial.C (Polynomial.C c)) = ψ₂ (Polynomial.C (Polynomial.C c)) := by
    intro c
    have : (Polynomial.C (Polynomial.C c) : Polynomial (Polynomial (ZMod p))) =
        algebraMap (ZMod p) _ c := by
      rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply]; rfl
    rw [this, ψ₁.commutes, ψ₂.commutes]
  have hi : ∀ a : Polynomial (ZMod p), ψ₁ (Polynomial.C a) = ψ₂ (Polynomial.C a) := by
    intro a
    induction a using Polynomial.induction_on' with
    | add f g hf hg => rw [Polynomial.C_add, map_add, map_add, hf, hg]
    | monomial n c =>
      have : (Polynomial.C (Polynomial.monomial n c) : Polynomial (Polynomial (ZMod p))) =
          Polynomial.C (Polynomial.C c) * (Polynomial.C Polynomial.X) ^ n := by
        rw [← Polynomial.C_pow, ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial]
      rw [this, map_mul, map_mul, map_pow, map_pow, hc, hC]
  refine AlgHom.ext fun g => ?_
  induction g using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow, hi, hX]

/-- $\mathbb F_p$-algebra maps from $\mathbb F_p[X][Y]/(f)$ to a field $K$ are the points $(x, y) \in K^2$ with
$f(x, y) = 0$. -/
noncomputable def planeHomEquiv (f : Polynomial (Polynomial (ZMod p))) :
    (planeCurveRing p f →ₐ[ZMod p] K) ≃ {z : K × K // evalPair z.1 z.2 f = 0} where
  toFun φ := ⟨(φ (Ideal.Quotient.mk _ (Polynomial.C Polynomial.X)), φ (Ideal.Quotient.mk _ Polynomial.X)), by
    have h : evalPair (φ (Ideal.Quotient.mk _ (Polynomial.C Polynomial.X)))
        (φ (Ideal.Quotient.mk _ Polynomial.X)) = φ.comp (Ideal.Quotient.mkₐ (ZMod p) (Ideal.span {f})) := by
      refine algHom_ext_pair ?_ ?_
      · simp [evalPair_C]
      · simp [evalPair_X]
    show evalPair _ _ f = 0
    rw [h]
    show φ (Ideal.Quotient.mk _ f) = 0
    have h0 : Ideal.Quotient.mk (Ideal.span {f}) f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self f)
    rw [h0, map_zero]⟩
  invFun z := Ideal.Quotient.liftₐ (Ideal.span {f}) (evalPair z.1.1 z.1.2) (by
    intro g hg
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    rw [map_mul, z.2, mul_zero])
  left_inv φ := by
    refine Ideal.Quotient.algHom_ext (ZMod p) (algHom_ext_pair ?_ ?_)
    · show evalPair _ _ (Polynomial.C Polynomial.X) = _
      rw [evalPair_C]; simp
    · show evalPair _ _ Polynomial.X = _
      rw [evalPair_X]; rfl
  right_inv z := by
    apply Subtype.ext
    show (evalPair z.1.1 z.1.2 (Polynomial.C Polynomial.X), evalPair z.1.1 z.1.2 Polynomial.X) = z.1
    rw [evalPair_C, evalPair_X]; simp

end PlaneHom

/-! ### Algebra maps out of the coordinate ring of a Weierstrass curve -/

section WeierstrassHom

open WeierstrassCurve

variable (W : WeierstrassCurve (ZMod p)) {K : Type*} [Field K] [Algebra (ZMod p) K]

theorem evalPair_polynomial_eq_zero_iff (x y : K) :
    evalPair x y W.toAffine.polynomial = 0 ↔ (W.baseChange K).toAffine.Equation x y := by
  rw [Affine.equation_iff']
  unfold Affine.polynomial
  simp [evalPair_C, evalPair_X]
  exact ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩

variable [W.IsElliptic]

/-- Affine points over $\mathbb F_{p^m}$ are the algebra maps out of the coordinate ring, plus the point at infinity:
$N_m = \#\operatorname{Hom}(\mathbb F_p[x, y], \mathbb F_{p^m}) + 1$. -/
theorem homCount_add_one (m : ℕ) (hm : 1 ≤ m) :
    homCount (p := p) W.toAffine.CoordinateRing m + 1 = numPoints W m := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : (W.baseChange (GaloisField p m)).IsElliptic :=
    inferInstanceAs ((W.map (algebraMap (ZMod p) (GaloisField p m))).IsElliptic)
  have e1 : (W.toAffine.CoordinateRing →ₐ[ZMod p] GaloisField p m) ≃
      {xy : GaloisField p m × GaloisField p m // (W.baseChange (GaloisField p m)).toAffine.Equation xy.1 xy.2} :=
    (planeHomEquiv (p := p) W.toAffine.polynomial).trans
      (Equiv.subtypeEquivRight fun z => evalPair_polynomial_eq_zero_iff W z.1 z.2)
  unfold homCount numPoints
  rw [Nat.card_congr e1,
    Nat.card_congr (Affine.pointEquiv (W.baseChange (GaloisField p m)).toAffine)]
  exact (Finite.card_option (α := {xy : GaloisField p m × GaloisField p m //
    (W.baseChange (GaloisField p m)).toAffine.Equation xy.1 xy.2})).symm

end WeierstrassHom

/-! ### Finiteness of the sets of divisors of a given degree -/

section Finiteness

variable (R : Type*) [CommRing R] [Algebra (ZMod p) R] [Algebra.FiniteType (ZMod p) R]

include p

/-- The residue field of a maximal ideal of a finitely generated $\mathbb F_p$-algebra is a finite set. -/
theorem finite_residue (𝔭 : MaximalSpectrum R) : Finite (R ⧸ 𝔭.asIdeal) := by
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  letI : Field (R ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  haveI : Module.Finite (ZMod p) (R ⧸ 𝔭.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing (ZMod p) (R ⧸ 𝔭.asIdeal)
  exact Module.finite_of_finite (ZMod p)

theorem one_le_maxDeg (𝔭 : MaximalSpectrum R) : 1 ≤ maxDeg (p := p) R 𝔭 := by
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  letI : Field (R ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  haveI : Module.Finite (ZMod p) (R ⧸ 𝔭.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing (ZMod p) (R ⧸ 𝔭.asIdeal)
  exact Module.finrank_pos

theorem natCard_residue (𝔭 : MaximalSpectrum R) :
    Nat.card (R ⧸ 𝔭.asIdeal) = p ^ maxDeg (p := p) R 𝔭 := by
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  letI : Field (R ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  haveI : Module.Finite (ZMod p) (R ⧸ 𝔭.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing (ZMod p) (R ⧸ 𝔭.asIdeal)
  haveI := finite_residue (p := p) R 𝔭
  rw [Module.natCard_eq_pow_finrank (K := ZMod p)]
  simp [maxDeg]


/-- A finitely generated algebra has finitely many algebra maps to a finite field. -/
theorem finite_algHom {K : Type*} [Field K] [Algebra (ZMod p) K] [Finite K] :
    Finite (R →ₐ[ZMod p] K) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType (ZMod p) R)
  refine Finite.of_injective (fun φ : R →ₐ[ZMod p] K => fun i : Fin n => φ (f (MvPolynomial.X i))) ?_
  intro φ ψ h
  have : φ.comp f = ψ.comp f := MvPolynomial.algHom_ext fun i => congrFun h i
  exact (AlgHom.cancel_right hf).1 this

/-- A finitely generated $\mathbb F_p$-algebra has finitely many maximal ideals of residue degree at most $k$. -/
theorem finite_maxDeg_le (k : ℕ) :
    {𝔭 : MaximalSpectrum R | maxDeg (p := p) R 𝔭 ≤ k}.Finite := by
  have key : ∀ j : ℕ, Set.Finite (⋃ _ : 1 ≤ j, Set.range
      (fun φ : R →ₐ[ZMod p] GaloisField p j => (RingHom.ker φ : Ideal R))) := by
    intro j
    by_cases hj : 1 ≤ j
    · haveI : NeZero j := ⟨by omega⟩
      haveI := finite_algHom (p := p) R (K := GaloisField p j)
      simpa [hj] using Set.finite_range _
    · simp [hj]
  have hfin : Set.Finite (⋃ j ∈ Finset.range (k + 1), ⋃ _ : 1 ≤ j, Set.range
      (fun φ : R →ₐ[ZMod p] GaloisField p j => (RingHom.ker φ : Ideal R))) :=
    Set.Finite.biUnion (Finset.range (k + 1)).finite_toSet fun j _ => key j
  refine (hfin.preimage (f := fun 𝔭 : MaximalSpectrum R => 𝔭.asIdeal)
    (fun a _ b _ h => MaximalSpectrum.ext h)).subset ?_
  intro 𝔭 h𝔭
  have hle : maxDeg (p := p) R 𝔭 ≤ k := h𝔭
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  letI : Field (R ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  haveI := finite_residue (p := p) R 𝔭
  let e : (R ⧸ 𝔭.asIdeal) ≃ₐ[ZMod p] GaloisField p (maxDeg (p := p) R 𝔭) :=
    GaloisField.algEquivGaloisField p _ (natCard_residue (p := p) R 𝔭)
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_range]
  refine ⟨maxDeg (p := p) R 𝔭, Finset.mem_range.2 (by omega), one_le_maxDeg (p := p) R 𝔭,
    (e.toAlgHom).comp (Ideal.Quotient.mkₐ (ZMod p) 𝔭.asIdeal), ?_⟩
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem, e.injective.eq_iff, map_eq_zero_iff _ e.injective]

/-- For each $k$, finitely many positive divisors have degree $k$. -/
theorem finite_divisors (k : ℕ) :
    Finite {D : MaximalSpectrum R →₀ ℕ // D.sum (fun 𝔭 n => n * maxDeg (p := p) R 𝔭) = k} := by
  have hT := finite_maxDeg_le (p := p) R k
  haveI : Finite {𝔭 : MaximalSpectrum R | maxDeg (p := p) R 𝔭 ≤ k} := hT.to_subtype
  have hbound : ∀ D : {D : MaximalSpectrum R →₀ ℕ //
      D.sum (fun 𝔭 n => n * maxDeg (p := p) R 𝔭) = k}, ∀ 𝔭, D.1 𝔭 * maxDeg (p := p) R 𝔭 ≤ k := by
    intro D 𝔭
    by_cases h : 𝔭 ∈ D.1.support
    · exact le_of_le_of_eq (Finset.single_le_sum (f := fun 𝔮 => D.1 𝔮 * maxDeg (p := p) R 𝔮)
        (fun _ _ => Nat.zero_le _) h) D.2
    · rw [Finsupp.notMem_support_iff.1 h]; simp
  have hdeg := one_le_maxDeg (p := p) R
  refine Finite.of_injective
    (fun D : {D : MaximalSpectrum R →₀ ℕ // D.sum (fun 𝔭 n => n * maxDeg (p := p) R 𝔭) = k} =>
      fun 𝔭 : {𝔭 : MaximalSpectrum R | maxDeg (p := p) R 𝔭 ≤ k} =>
        (⟨D.1 𝔭, Nat.lt_succ_of_le (le_trans (Nat.le_mul_of_pos_right _ (hdeg 𝔭)) (hbound D 𝔭))⟩ :
          Fin (k + 1))) ?_
  intro D₁ D₂ h
  refine Subtype.ext (Finsupp.ext fun 𝔭 => ?_)
  by_cases h𝔭 : maxDeg (p := p) R 𝔭 ≤ k
  · have := congrFun h ⟨𝔭, h𝔭⟩
    exact congrArg Fin.val this
  · have h1 : D₁.1 𝔭 = 0 := by
      by_contra hne
      have := hbound D₁ 𝔭
      have : maxDeg (p := p) R 𝔭 ≤ D₁.1 𝔭 * maxDeg (p := p) R 𝔭 :=
        Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
      omega
    have h2 : D₂.1 𝔭 = 0 := by
      by_contra hne
      have := hbound D₂ 𝔭
      have : maxDeg (p := p) R 𝔭 ≤ D₂.1 𝔭 * maxDeg (p := p) R 𝔭 :=
        Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
      omega
    rw [h1, h2]


/-- Positive divisors of degree $m$ with a multiple of the point at infinity: decomposition by the degree of the
affine part. -/
theorem natCard_divisors_infinity (m : ℕ) :
    Nat.card {x : (MaximalSpectrum R →₀ ℕ) × ℕ //
      x.1.sum (fun 𝔭 n => n * maxDeg (p := p) R 𝔭) + x.2 = m} =
    ∑ k ∈ Finset.range (m + 1),
      Nat.card {D : MaximalSpectrum R →₀ ℕ // D.sum (fun 𝔭 n => n * maxDeg (p := p) R 𝔭) = k} := by
  haveI : ∀ k, Finite {D : MaximalSpectrum R →₀ ℕ // D.sum (fun 𝔭 n => n * maxDeg (p := p) R 𝔭) = k} :=
    fun k => finite_divisors (p := p) R k
  let e : {x : (MaximalSpectrum R →₀ ℕ) × ℕ //
      x.1.sum (fun 𝔭 n => n * maxDeg (p := p) R 𝔭) + x.2 = m} ≃
      Σ k : Fin (m + 1), {D : MaximalSpectrum R →₀ ℕ //
        D.sum (fun 𝔭 n => n * maxDeg (p := p) R 𝔭) = k.1} :=
    { toFun := fun x => ⟨⟨x.1.1.sum (fun 𝔭 n => n * maxDeg (p := p) R 𝔭), by have := x.2; omega⟩,
        ⟨x.1.1, rfl⟩⟩
      invFun := fun y => ⟨(y.2.1, m - y.1.1), by have := y.2.2; have := y.1.2; simp only at *; omega⟩
      left_inv := fun x => by
        apply Subtype.ext
        refine Prod.ext rfl ?_
        have := x.2
        show m - x.1.1.sum (fun 𝔭 n => n * maxDeg (p := p) R 𝔭) = x.1.2
        omega
      right_inv := fun y => by
        obtain ⟨⟨k, hk⟩, ⟨D, hD⟩⟩ := y
        simp only at hD
        subst hD
        rfl }
  rw [Nat.card_congr e, Nat.card_sigma, ← Fin.sum_univ_eq_sum_range
    (fun k => Nat.card {D : MaximalSpectrum R →₀ ℕ // D.sum (fun 𝔭 n => n * maxDeg (p := p) R 𝔭) = k})]

/-- The series of positive divisors with a multiple of infinity is the Euler product times $1/(1-T)$. -/
theorem posDiv_series_eq :
    (PowerSeries.mk fun m => (Nat.card {x : (MaximalSpectrum R →₀ ℕ) × ℕ //
      x.1.sum (fun 𝔭 n => n * maxDeg (p := p) R 𝔭) + x.2 = m} : ℚ)) =
    eulerZeta (p := p) R * PowerSeries.mk fun _ => (1 : ℚ) := by
  ext m
  rw [coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    natCard_divisors_infinity (p := p) R m]
  push_cast
  simp [eulerZeta]

end Finiteness

/-- **Example 9.7** (pdf p. 160): the affine line, realized as the plane curve $Y = 0$, has
$Z(\mathbb A^1, T) = 1/(1 - pT)$ (from Proposition 9.8: $N_m = p^m$). -/
@[kb "milne2006ec" "Ch. IV, Example 9.7, pdf p. 160"]
theorem example_9_7 (h98 : Prop9_8 p) :
    eulerZeta (p := p) (planeCurveRing p Polynomial.X) * (1 - C (p : ℚ) * X) = 1 := by
  have hcount : ∀ m, 1 ≤ m → (homCount (p := p) (planeCurveRing p Polynomial.X) m : ℚ) = (p : ℚ) ^ m := by
    intro m hm
    have e : (planeCurveRing p (Polynomial.X : Polynomial (Polynomial (ZMod p))) →ₐ[ZMod p] GaloisField p m) ≃
        GaloisField p m :=
      (planeHomEquiv _).trans
        { toFun := fun z => z.1.1
          invFun := fun x => ⟨(x, 0), by rw [evalPair_X]⟩
          left_inv := fun z => by
            apply Subtype.ext
            have := z.2
            rw [evalPair_X] at this
            exact Prod.ext rfl this.symm
          right_inv := fun x => rfl }
    unfold homCount
    rw [Nat.card_congr e, GaloisField.card p m (by omega)]
    push_cast; rfl
  rw [h98.eq_exp _ Polynomial.X_ne_zero, expSeries_congr _ (fun m => (p : ℚ) ^ m) hcount]
  exact expSeries_geom (p : ℚ)

/-- The number of positive divisors of degree $m$ on an elliptic curve $E$ over $\mathbb F_p$ (pdf p. 162): a positive
divisor is $D + nO$ with $D$ a positive divisor on the affine part $E^{\mathrm{aff}}$ (maximal ideals of its coordinate
ring) and $O$ the point at infinity, of degree $1$. -/
noncomputable def posDivCount (W : WeierstrassCurve (ZMod p)) (m : ℕ) : ℕ :=
  Nat.card {x : (MaximalSpectrum W.toAffine.CoordinateRing →₀ ℕ) × ℕ //
    x.1.sum (fun 𝔭 n => n * maxDeg (p := p) W.toAffine.CoordinateRing 𝔭) + x.2 = m}

/-- **Proposition 9.9** (named statement; pdf p. 162): on an elliptic curve $E$ over $\mathbb F_p$ there are exactly
$\#E(\mathbb F_p)(p^m - 1)/(p - 1)$ positive divisors of degree $m \ge 1$ (Milne's proof: Riemann–Roch and
$E(\mathbb F_p) \cong \operatorname{Pic}^0(E)$, not formalized). -/
@[kb "milne2006ec" "Ch. IV, Proposition 9.9, pdf p. 162 (input)"]
structure Prop9_9 (W : WeierstrassCurve (ZMod p)) : Prop where
  count : ∀ m : ℕ, 1 ≤ m → posDivCount W m * (p - 1) = numPoints W 1 * (p ^ m - 1)

/-- **Theorem 9.10** (pdf p. 163), Milne's proof: from Proposition 9.8 for the affine part
$E^{\mathrm{aff}}$ (so $Z(E, T) = Z(E^{\mathrm{aff}}, T)/(1 - T) = \sum_m d_m T^m$, $d_m$ the number of positive
divisors of degree $m$) and Proposition 9.9 ($d_m = N_1(p^m - 1)/(p - 1)$). -/
@[kb "milne2006ec" "Ch. IV, Theorem 9.10, pdf p. 163"]
theorem theorem_9_10 (h98 : Prop9_8 p) (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] (h99 : Prop9_9 W) :
    Theorem9_10 W := by
  haveI : Algebra.FiniteType (ZMod p) W.toAffine.CoordinateRing := by
    haveI : Algebra.FiniteType (ZMod p) (Polynomial (Polynomial (ZMod p))) := inferInstance
    exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (ZMod p) (Ideal.span {W.toAffine.polynomial}))
      Ideal.Quotient.mk_surjective
  have hE : eulerZeta (p := p) W.toAffine.CoordinateRing =
      expSeries fun m => (homCount (p := p) W.toAffine.CoordinateRing m : ℚ) :=
    h98.eq_exp W.toAffine.polynomial WeierstrassCurve.Affine.polynomial_ne_zero
  -- the series 1/(1 - T)
  have hU : expSeries (fun m => (1 : ℚ) ^ m) = PowerSeries.mk fun _ => (1 : ℚ) := by
    have h1 := expSeries_geom (1 : ℚ)
    have h2 : (PowerSeries.mk fun _ => (1 : ℚ)) * (1 - C (1 : ℚ) * X) = 1 := by
      have : (PowerSeries.mk fun _ => (1 : ℚ)) = 1 + geomSer (1 : ℚ) := by
        ext m; cases m <;> simp [geomSer]
      rw [this]
      have := geomSer_mul (1 : ℚ)
      linear_combination this
    have hne : (1 - C (1 : ℚ) * X : PowerSeries ℚ) ≠ 0 := by
      intro h0
      have := congrArg constantCoeff h0
      simp at this
    exact mul_right_cancel₀ hne (h1.trans h2.symm)
  have hZ : zetaSeries W = eulerZeta (p := p) W.toAffine.CoordinateRing *
      PowerSeries.mk fun _ => (1 : ℚ) := by
    rw [← hU, hE, expSeries_add]
    unfold zetaSeries
    change expSeries _ = expSeries _
    refine expSeries_congr _ _ fun m hm => ?_
    have := homCount_add_one W m hm
    rw [← this]; push_cast; ring
  have hd : zetaSeries W = PowerSeries.mk fun m => (posDivCount W m : ℚ) :=
    hZ.trans (posDiv_series_eq (p := p) W.toAffine.CoordinateRing).symm
  -- closed form of the divisor-count series
  set c : ℚ := (numPoints W 1 : ℚ) / ((p : ℚ) - 1) with hc
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hcc : c * ((p : ℚ) - 1) = numPoints W 1 := by
    rw [hc]; field_simp [(sub_pos.2 hp1).ne']
  have hform : zetaSeries W = C (1 : ℚ) + C c * (geomSer (p : ℚ) - geomSer (1 : ℚ)) := by
    ext m
    cases m with
    | zero =>
      have h0 : constantCoeff (zetaSeries W) = 1 := constantCoeff_expSeries _
      simpa [geomSer] using h0
    | succ m =>
      rw [hd, coeff_mk]
      have h := h99.count (m + 1) (by omega)
      have hpm : 1 ≤ p ^ (m + 1) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
      have hp1' : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
      have h' := congrArg (Nat.cast : ℕ → ℚ) h
      push_cast [Nat.cast_sub hp1', Nat.cast_sub hpm] at h'
      simp only [map_add, map_mul, map_sub, coeff_C, geomSer, coeff_mk, coeff_C_mul]
      simp only [Nat.succ_ne_zero, ite_false, one_pow]
      have hne : ((p : ℚ) - 1) ≠ 0 := (sub_pos.2 hp1).ne'
      rw [hc]
      field_simp
      linear_combination h'
  refine ⟨?_⟩
  rw [hform]
  have hgp := geomSer_mul (p : ℚ)
  have hg1 := geomSer_mul (1 : ℚ)
  have hCc : C (c) * (C (p : ℚ) - 1) = C (numPoints W 1 : ℚ) := by
    rw [← hcc]; simp [map_mul, map_sub]
  simp only [map_one] at hg1 ⊢
  simp only [map_sub, map_add, map_one]
  linear_combination (C c * (1 - X)) * hgp - (C c * (1 - C (p : ℚ) * X)) * hg1 + X * hCc

end NumberFieldKB.MilneEC
