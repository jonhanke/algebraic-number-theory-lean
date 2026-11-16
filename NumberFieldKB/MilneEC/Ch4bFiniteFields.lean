import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Num.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch4bTorsors
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Topology.Filter

/-!
# Milne, Elliptic Curves, Chapter IV §9: elliptic curves over finite fields

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Section 9, pdf pp. 155–168.
Locators give the pdf page of the text `ectext6` (printed page = pdf page − 8).

**Conventions.** $\mathbb F_p$ is `ZMod p`; Milne's $\mathbb F$ (an algebraic closure) is `AlgebraicClosure k` for a
finite field $k$, and $\Gamma = \operatorname{Gal}(\mathbb F/k)$ with the Krull topology.  Results Milne states over
$\mathbb F_p$ but whose proofs work verbatim over any finite field $k$ (Proposition 9.2, Corollary 9.3) are stated for
$k$; $k = \mathbb F_p$ is the case Milne states.  $\#E(\mathbb F_{p^m})$ is the number of points of Mathlib's
Weierstrass curve over `GaloisField p m` (affine points and the point at infinity).

## Proved
* `frobenius_mem_curve` (the Frobenius map of a plane curve over $\mathbb F_p$, pdf p. 156).
* `prop_9_2` (from the named statement `LangFrobenius`): $H^1(k, E) = 0$.
* `cor_9_3` (from `LangFrobenius`): a principal homogeneous space for $E$ over $k$ (Galois-set form of Chapter IV §7)
  has a $k$-point.
* `remark_9_11_a` (from `Theorem9_10`): $N_m = 1 + p^m - \alpha^m - \beta^m$.
* `remark_9_11_b`: for $\alpha, \beta$ the roots of $T^2 + bT + p$, $|\alpha| = |\beta| = \sqrt p$ if and only if
  $|b| \le 2\sqrt p$; with `Theorem9_10` this is Milne's equivalence of the Riemann hypothesis for $\zeta(E, s)$ with the
  bound of Theorem 9.4.

## Named statements (inputs)
* `LangFrobenius`: for an elliptic curve over a finite field $k$, $P \mapsto \varphi(P) - P$ is surjective on
  $E(\mathbb F)$ (Milne, pdf p. 157, from Chapter I, 4.23: a nonconstant regular map of curves is surjective).
* `Theorem9_4`: the Hasse bound $|\#E(\mathbb F_p) - (p + 1)| \le 2\sqrt p$.
* `Theorem9_10`: $Z(E, T) = \dfrac{1 + (N_1 - p - 1)T + pT^2}{(1 - T)(1 - pT)}$.
-/

open WeierstrassCurve PowerSeries

namespace NumberFieldKB.MilneEC

/-! ## The Frobenius map (pdf p. 156) -/

/-- **The Frobenius map** of a projective plane curve $C : F(X, Y, Z) = 0$ over $\mathbb F_p$ (pdf p. 156):
$(x : y : z) \mapsto (x^p : y^p : z^p)$ maps $C(K)$ to itself for every field $K$ of characteristic $p$, because
raising $F(x, y, z) = 0$ to the $p$-th power and using $a^p = a$ on $\mathbb F_p$ gives $F(x^p, y^p, z^p) = 0$. -/
@[kb "milne2006ec" "Ch. IV, §9, the Frobenius map, pdf p. 156"]
theorem frobenius_mem_curve (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [Algebra (ZMod p) K]
    (F : MvPolynomial (Fin 3) (ZMod p)) (v : Fin 3 → K) (hv : MvPolynomial.aeval v F = 0) :
    MvPolynomial.aeval (fun i => v i ^ p) F = 0 := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  let ψ : K →ₐ[ZMod p] K :=
    { frobenius K p with
      commutes' := fun r => by
        show algebraMap (ZMod p) K r ^ p = algebraMap (ZMod p) K r
        rw [← map_pow, ZMod.pow_card] }
  have h := congrArg ψ hv
  rw [map_zero, MvPolynomial.comp_aeval_apply] at h
  exact h

/-! ## The Galois module $E(\mathbb F)$ -/

section Galois

variable (k : Type*) [Field k] [Fintype k] (W : WeierstrassCurve k)

open Classical in
/-- Decidable equality on $\mathbb F$ (needed for the group law on points). -/
noncomputable instance : DecidableEq (AlgebraicClosure k) := Classical.decEq _

/-- $\Gamma = \operatorname{Gal}(\mathbb F/k)$ acts on $E(\mathbb F)$ through coordinates. -/
noncomputable instance galPointsAction :
    DistribMulAction (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (W.toAffine.baseChange (AlgebraicClosure k)).Point where
  smul σ P := Affine.Point.map (W' := W.toAffine) (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k) P
  one_smul P := Affine.Point.map_id (W' := W.toAffine) P
  mul_smul σ τ P := (Affine.Point.map_map (W' := W.toAffine) (τ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k)
    (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k) P).symm
  smul_zero σ := map_zero _
  smul_add σ P Q := map_add _ P Q

/-- $E(\mathbb F)$ is a discrete $\Gamma$-module: every point has coordinates in a finite extension of $k$, so its
stabilizer is open. -/
theorem isOpen_stabilizer_points (P : (W.toAffine.baseChange (AlgebraicClosure k)).Point) :
    IsOpen (MulAction.stabilizer (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) P :
      Set (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) := by
  rcases P with _ | ⟨x, y, h⟩
  · have : (MulAction.stabilizer (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
        (0 : (W.toAffine.baseChange (AlgebraicClosure k)).Point) :
        Set (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) = Set.univ := by
      ext σ
      simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_univ, iff_true]
      exact Affine.Point.map_zero (W' := W.toAffine) (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k)
    change IsOpen (MulAction.stabilizer (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
        (0 : (W.toAffine.baseChange (AlgebraicClosure k)).Point) :
        Set (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k))
    rw [this]; exact isOpen_univ
  · have hx := stabilizer_isOpen_of_isIntegral (K := k) (L := AlgebraicClosure k) x
    have hy := stabilizer_isOpen_of_isIntegral (K := k) (L := AlgebraicClosure k) y
    refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer _ x ⊓ MulAction.stabilizer _ y) ?_ (hx.inter hy)
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff]
    have h1 : σ x = x := hσ.1
    have h2 : σ y = y := hσ.2
    show Affine.Point.map (W' := W.toAffine) (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k)
      (Affine.Point.some x y h) = Affine.Point.some x y h
    simp only [Affine.Point.map_some, Affine.Point.some.injEq]
    exact ⟨h1, h2⟩

/-- The Frobenius map $\varphi : E(\mathbb F) \to E(\mathbb F)$, $(x, y) \mapsto (x^q, y^q)$, $q = \#k$
(for $k = \mathbb F_p$ Milne's map of pdf p. 156). -/
noncomputable def frobeniusPoints :
    (W.toAffine.baseChange (AlgebraicClosure k)).Point →+ (W.toAffine.baseChange (AlgebraicClosure k)).Point :=
  Affine.Point.map (W' := W.toAffine) (FiniteField.frobeniusAlgHom k (AlgebraicClosure k))

/-- **Named statement** (Milne, pdf p. 157, proof of Proposition 9.2, citing Chapter I, 4.23): for an elliptic curve
$E$ over a finite field $k$, $\varphi - \mathrm{id}_E$ is a nonconstant regular map $E \to E$, so
$P \mapsto \varphi(P) - P$ is surjective on $E(\mathbb F)$ (Lang's theorem for $E$). -/
@[kb "milne2006ec" "Ch. IV, proof of Proposition 9.2, pdf p. 157 (input)"]
structure LangFrobenius : Prop where
  surjective : ∀ Q : (W.toAffine.baseChange (AlgebraicClosure k)).Point,
    ∃ P, frobeniusPoints k W P - P = Q

/-- The powers $\varphi^n$ ($n \ge 0$) of the Frobenius automorphism meet every neighbourhood of every element of
$\Gamma$: its powers are dense in $\Gamma$ (a finite field extension of $k$ has cyclic Galois group generated by
the Frobenius automorphism). -/
theorem frobenius_pow_mem_nhds (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (s : Set (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) (hs : s ∈ nhds σ) :
    ∃ n : ℕ, (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)) ^ n ∈ s := by
  set Fr := FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) with hFr
  have ht : {g | σ * g ∈ s} ∈ nhds (1 : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) := by
    have : Continuous (fun g : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k => σ * g) :=
      continuous_const.mul continuous_id
    exact this.continuousAt.preimage_mem_nhds (by simpa using hs)
  obtain ⟨E, hfin, hE⟩ := (krullTopology_mem_nhds_one_iff k (AlgebraicClosure k) _).1 ht
  have : Finite E := Module.finite_of_finite k
  obtain ⟨⟨n, _⟩, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k E).2
    (σ.restrictNormal E)
  refine ⟨n, ?_⟩
  have hmem : σ⁻¹ * Fr ^ n ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h1 := congrArg (fun φ : E ≃ₐ[k] E => ((φ ⟨x, hx⟩ : E) : AlgebraicClosure k)) hn
    simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      AlgEquiv.restrictNormal_commutes] at h1
    have h2 : (Fr ^ n) x = x ^ (Fintype.card k ^ n) := by
      rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    have h3 : σ x = x ^ (Fintype.card k ^ n) :=
      (AlgEquiv.restrictNormal_commutes σ E ⟨x, hx⟩).symm.trans h1.symm
    rw [AlgEquiv.mul_apply, h2, ← h3]
    simp
  have := hE hmem
  simpa using this

/-- **Proposition 9.2** (pdf p. 157): for an elliptic curve $E$ over $k$ ($k = \mathbb F_p$ in Milne),
$H^1(k, E) = 0$: every continuous crossed homomorphism $\Gamma \to E(\mathbb F)$ is principal.  Milne's proof: the
Frobenius automorphism generates a dense subgroup of $\Gamma$, and `LangFrobenius` solves
$f(\mathrm{Frob}) = \varphi(P) - P$. -/
@[kb "milne2006ec" "Ch. IV, Proposition 9.2, pdf p. 157"]
theorem prop_9_2 [W.IsElliptic] (hLang : LangFrobenius k W)
    (c : ContH1 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (W.toAffine.baseChange (AlgebraicClosure k)).Point) :
    c = 0 := by
  obtain ⟨f, rfl⟩ := ContH1.mk_surjective c
  rw [ContH1.mk_eq_zero_iff]
  set Fr := FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) with hFr
  have hcoc : groupCohomology.IsCocycle₁ (f : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (W.toAffine.baseChange (AlgebraicClosure k)).Point) := f.2.1
  have hlc := f.2.2
  obtain ⟨P, hP⟩ := hLang.surjective ((f : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (W.toAffine.baseChange (AlgebraicClosure k)).Point) Fr)
  have hFP : ∀ Q, Fr • Q = frobeniusPoints k W Q := fun Q => rfl
  have hf1 : (f : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (W.toAffine.baseChange (AlgebraicClosure k)).Point) 1 = 0 := by
    have h := hcoc 1 1
    rw [mul_one, one_smul] at h
    simpa using h
  have hu : ∀ n : ℕ, (f : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (W.toAffine.baseChange (AlgebraicClosure k)).Point) (Fr ^ n) = Fr ^ n • P - P := by
    intro n
    induction n with
    | zero => simp [hf1]
    | succ n ih =>
      rw [pow_succ', hcoc, ih, mul_smul, smul_sub, ← hP, ← hFP]
      abel
  refine ⟨P, fun σ => ?_⟩
  have hl : IsLocallyConstant (fun g : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k =>
      (f : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
        (W.toAffine.baseChange (AlgebraicClosure k)).Point) g - (g • P - P)) :=
    hlc.sub ((GaloisTorsor.isLocallyConstant_orbit (isOpen_stabilizer_points k W) P).sub (IsLocallyConstant.const P))
  have hopen := hl.isOpen_fiber ((fun g : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k =>
      (f : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
        (W.toAffine.baseChange (AlgebraicClosure k)).Point) g - (g • P - P)) σ)
  obtain ⟨n, hn⟩ := frobenius_pow_mem_nhds k σ _ (hopen.mem_nhds rfl)
  have hn' : (f : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (W.toAffine.baseChange (AlgebraicClosure k)).Point) (Fr ^ n) - (Fr ^ n • P - P) =
      (f : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) →
      (W.toAffine.baseChange (AlgebraicClosure k)).Point) σ - (σ • P - P) := hn
  rw [hu n, sub_self] at hn'
  exact (sub_eq_zero.1 hn'.symm).symm

/-- **Corollary 9.3** (pdf p. 157), Galois-set form: a principal homogeneous space for an elliptic curve $E$ over a
finite field $k$ has a point with coordinates in $k$.  (Milne states it for every nonsingular projective curve of
genus 1, which by Theorem 7.19 is a principal homogeneous space for its jacobian; Theorem 7.19 and curves of genus 1
are not formalized.) -/
@[kb "milne2006ec" "Ch. IV, Corollary 9.3, pdf p. 157"]
theorem cor_9_3 [W.IsElliptic] (hLang : LangFrobenius k W)
    (T : GaloisTorsor (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (W.toAffine.baseChange (AlgebraicClosure k)).Point) :
    T.rationalPoints.Nonempty := by
  have h0 : T.cls = 0 := by
    rw [GaloisTorsor.cls_eq_mk_cocycleAt T (Classical.arbitrary T)]
    exact prop_9_2 k W hLang _
  exact (GaloisTorsor.statement_7_6 T).1 ((GaloisTorsor.cls_eq_zero_iff T).1 h0)

end Galois

/-! ## The Hasse bound (pdf p. 157) -/

/-- **Theorem 9.4** (named statement; pdf p. 157, the congruence Riemann hypothesis, Hasse 1933/34): for an
elliptic curve $E$ over $\mathbb F_p$, $|\#E(\mathbb F_p) - (p + 1)| \le 2\sqrt p$.  Milne's proof uses the Frobenius
endomorphism on the Tate module (Chapter III, 3.23), not formalized. -/
@[kb "milne2006ec" "Ch. IV, Theorem 9.4, pdf p. 157 (input)"]
structure Theorem9_4 : Prop where
  bound : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    |(Nat.card W.toAffine.Point : ℝ) - (p + 1)| ≤ 2 * Real.sqrt p

/-! ## Zeta functions (pdf pp. 162–165) -/

section Zeta

variable {p : ℕ} [Fact p.Prime]

/-- $N_m = \#E(\mathbb F_{p^m})$ (pdf p. 162), for $m \ge 1$. -/
noncomputable def numPoints (W : WeierstrassCurve (ZMod p)) (m : ℕ) : ℕ :=
  Nat.card (W.baseChange (GaloisField p m)).toAffine.Point

/-- **The zeta function of a projective plane curve over $\mathbb F_p$**, here an elliptic curve (pdf p. 162):
$Z(E, T) = \exp\bigl(\sum_{m \ge 1} N_m T^m / m\bigr) \in \mathbb Q[[T]]$. -/
@[kb "milne2006ec" "Ch. IV, §9, zeta function of a projective plane curve, pdf p. 162"]
noncomputable def zetaSeries (W : WeierstrassCurve (ZMod p)) : PowerSeries ℚ :=
  (exp ℚ).subst (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else (numPoints W m : ℚ) / m)

/-- **Theorem 9.10** (named statement; pdf p. 163): for an elliptic curve $E$ over $\mathbb F_p$,
$Z(E, T) = \dfrac{1 + (N_1 - p - 1)T + pT^2}{(1 - T)(1 - pT)}$, stated with denominators cleared.  Milne's proof counts
positive divisors of degree $m$ (Proposition 9.9, Riemann–Roch), not formalized. -/
@[kb "milne2006ec" "Ch. IV, Theorem 9.10, pdf p. 163 (input)"]
structure Theorem9_10 (W : WeierstrassCurve (ZMod p)) : Prop where
  rational : zetaSeries W * ((1 - X) * (1 - C (p : ℚ) * X)) =
    1 + C ((numPoints W 1 : ℚ) - p - 1) * X + C (p : ℚ) * X ^ 2

/-- Logarithmic derivative of the zeta series: if $Z = \exp(\sum_m N_m T^m/m)$ and
$Z (1-T)(1-qT) = 1 + bT + qT^2$ then, writing $D = (1-T)(1-qT)$ and $\mathrm{Num} = 1 + bT + qT^2$,
$\mathrm{Num} \cdot (\sum_m N_m T^m) \cdot D + T \cdot \mathrm{Num} \cdot D' = T \cdot \mathrm{Num}' \cdot D$. -/
theorem key_identity (N : ℕ → ℚ) (b q : ℚ)
    (h : (exp ℚ).subst (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else N m / m) *
      ((1 - X) * (1 - C q * X)) = 1 + C b * X + C q * X ^ 2) :
    (1 + C b * X + C q * X ^ 2) * (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else N m) *
      ((1 - X) * (1 - C q * X)) + X * (1 + C b * X + C q * X ^ 2) * (C (-(1 + q)) + C (2 * q) * X) =
    X * (C b + C (2 * q) * X) * ((1 - X) * (1 - C q * X)) := by
  set S : ℚ⟦X⟧ := PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else N m / m with hS
  have hg : HasSubst S := HasSubst.of_constantCoeff_zero' (by simp [hS])
  have hZ' : d⁄dX ((exp ℚ).subst S) = (exp ℚ).subst S * d⁄dX S := by
    rw [derivative_subst hg, derivative_exp]
  have hXS : X * d⁄dX S = (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else N m) := by
    ext n
    cases n with
    | zero => simp
    | succ n =>
      rw [coeff_succ_X_mul, coeff_derivative, hS, coeff_mk, coeff_mk]
      simp only [Nat.succ_ne_zero, ite_false]
      push_cast
      field_simp
  have hD : d⁄dX ((1 - X) * (1 - C q * X) : ℚ⟦X⟧) = C (-(1 + q)) + C (2 * q) * X := by
    simp only [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero, derivative_X, derivative_C,
      smul_eq_mul, map_neg, map_add, map_mul, map_one]
    simp only [map_neg, map_add, map_mul, map_one, map_ofNat, Nat.cast_ofNat]
    ring
  have hN : d⁄dX (1 + C b * X + C q * X ^ 2 : ℚ⟦X⟧) = C b + C (2 * q) * X := by
    simp only [Derivation.leibniz, map_add, Derivation.map_one_eq_zero, derivative_X, derivative_C,
      smul_eq_mul, derivative_pow]
    simp only [map_neg, map_add, map_mul, map_one, map_ofNat, Nat.cast_ofNat]
    ring
  rw [← hD, ← hN]
  generalize hNum : (1 + C b * X + C q * X ^ 2 : ℚ⟦X⟧) = Num at *
  generalize hDD : ((1 - X) * (1 - C q * X) : ℚ⟦X⟧) = D at *
  generalize hZ : (exp ℚ).subst S = Z at *
  have hd := congrArg (d⁄dX) h
  rw [Derivation.leibniz, hZ'] at hd
  rw [← hXS, ← hd, ← h]
  simp only [smul_eq_mul]
  ring

/-- The geometric series $\sum_{m \ge 1} u^m T^m$. -/
noncomputable def geomSeries (u : ℂ) : ℂ⟦X⟧ := PowerSeries.mk fun m => if m = 0 then 0 else u ^ m

/-- $(\sum_{m \ge 1} u^m T^m)(1 - uT) = uT$. -/
theorem geomSeries_mul (u : ℂ) : geomSeries u * (1 - C u * X) = C u * X := by
  ext n
  cases n with
  | zero => simp [geomSeries]
  | succ n =>
    have e : geomSeries u * (1 - C u * X) = geomSeries u - C u * (geomSeries u * X) := by ring
    rw [e, map_sub, coeff_C_mul, coeff_succ_mul_X, coeff_C_mul, coeff_X]
    cases n with
    | zero => simp [geomSeries]
    | succ n => simp [geomSeries]; ring

/-- Computation of the coefficients from `key_identity`: if $\alpha + \beta = -b$ and $\alpha\beta = q$ then
$N_m = 1 + q^m - \alpha^m - \beta^m$ for $m \ge 1$. -/
theorem complex_step (N : ℕ → ℚ) (b q : ℚ) (α β : ℂ) (hsum : α + β = -(b : ℂ)) (hprod : α * β = q)
    (h : (exp ℚ).subst (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else N m / m) *
      ((1 - X) * (1 - C q * X)) = 1 + C b * X + C q * X ^ 2) (m : ℕ) (hm : 1 ≤ m) :
    (N m : ℂ) = 1 + (q : ℂ) ^ m - α ^ m - β ^ m := by
  have hk := congrArg (map (Rat.castHom ℂ)) (key_identity N b q h)
  have hmapN : map (Rat.castHom ℂ) (PowerSeries.mk fun m => if m = 0 then (0 : ℚ) else N m) =
      PowerSeries.mk fun m => if m = 0 then (0 : ℂ) else (N m : ℂ) := by
    ext n; simp only [coeff_map, coeff_mk]; split_ifs <;> simp
  have hCb : C ((b : ℚ) : ℂ) = -(C α + C β) := by rw [← map_add, hsum]; simp
  have hCq : C ((q : ℚ) : ℂ) = C α * C β := by rw [← map_mul, hprod]
  have hC2 : C (((2 * q : ℚ)) : ℂ) = 2 * (C α * C β) := by
    rw [Rat.cast_mul, Rat.cast_ofNat, map_mul, map_ofNat, hCq]
  have hC3 : C (((-(1 + q) : ℚ)) : ℂ) = -(1 + C α * C β) := by
    rw [← hCq]; push_cast; simp [map_neg, map_add]
  simp only [map_add, map_mul, map_sub, map_one, map_pow, map_X, map_C, hmapN, Rat.coe_castHom,
    hCb, hCq, hC2, hC3, Rat.cast_ofNat, Nat.cast_ofNat, map_ofNat] at hk
  have g1 := geomSeries_mul 1
  have gp := geomSeries_mul (q : ℂ)
  have ga := geomSeries_mul α
  have gc := geomSeries_mul β
  rw [map_one, one_mul] at g1
  rw [hCq] at gp
  have hne : ((1 - X) * (1 - C α * C β * X) * ((1 - C α * X) * (1 - C β * X)) : ℂ⟦X⟧) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp at this
  have hNT : (PowerSeries.mk fun m => if m = 0 then (0 : ℂ) else (N m : ℂ)) =
      geomSeries 1 + geomSeries (q : ℂ) - geomSeries α - geomSeries β := by
    refine mul_right_cancel₀ hne ?_
    linear_combination hk - (1 - C α * C β * X) * ((1 - C α * X) * (1 - C β * X)) * g1
      - (1 - X) * ((1 - C α * X) * (1 - C β * X)) * gp
      + (1 - X) * (1 - C α * C β * X) * (1 - C β * X) * ga
      + (1 - X) * (1 - C α * C β * X) * (1 - C α * X) * gc
  have := congrArg (coeff m) hNT
  simp [geomSeries, coeff_mk, show m ≠ 0 by omega] at this
  linear_combination this

/-- **Remark 9.11(a)** (pdf p. 164): write $1 + (N_1 - p - 1)T + pT^2 = (1 - \alpha T)(1 - \beta T)$; then
$N_m = 1 + p^m - \alpha^m - \beta^m$ for every $m \ge 1$ (from Theorem 9.10). -/
@[kb "milne2006ec" "Ch. IV, Remark 9.11(a), pdf p. 164"]
theorem remark_9_11_a (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] (h : Theorem9_10 W) (α β : ℂ)
    (hsum : α + β = p + 1 - numPoints W 1) (hprod : α * β = p) (m : ℕ) (hm : 1 ≤ m) :
    (numPoints W m : ℂ) = 1 + (p : ℂ) ^ m - α ^ m - β ^ m := by
  have h1 := complex_step (fun m => (numPoints W m : ℚ)) ((numPoints W 1 : ℚ) - p - 1) (p : ℚ) α β
    (by rw [hsum]; push_cast; ring) (by rw [hprod]; push_cast; rfl) h.rational m hm
  simpa using h1

/-- **Remark 9.11(b)** (pdf p. 165): let $\alpha, \beta$ be the roots of $T^2 + bT + p$ (so that
$1 + bT + pT^2 = (1 - \alpha T)(1 - \beta T)$), $p > 0$, $b$ real.  Then $|\alpha| = |\beta| = \sqrt p$ if and only if
$|b| \le 2\sqrt p$.  With $b = N_1 - p - 1$ and Theorem 9.10, the zeros of $\zeta(E, s)$ lie on $\Re(s) = 1/2$ if and
only if the bound of Theorem 9.4 holds. -/
@[kb "milne2006ec" "Ch. IV, Remark 9.11(b), pdf p. 165"]
theorem remark_9_11_b (p b : ℝ) (hp : 0 < p) (α β : ℂ) (hsum : α + β = -b) (hprod : α * β = p) :
    (‖α‖ = Real.sqrt p ∧ ‖β‖ = Real.sqrt p) ↔ |b| ≤ 2 * Real.sqrt p := by
  constructor
  · rintro ⟨h1, h2⟩
    have h : ‖α + β‖ ≤ ‖α‖ + ‖β‖ := norm_add_le α β
    rw [hsum, h1, h2] at h
    have : ‖(-(b : ℂ))‖ = |b| := by rw [norm_neg]; exact Complex.norm_real b |>.trans (Real.norm_eq_abs b)
    rw [this] at h
    linarith
  · intro hb
    have hre := congrArg Complex.re hsum
    have him := congrArg Complex.im hsum
    have hre' := congrArg Complex.re hprod
    have him' := congrArg Complex.im hprod
    simp only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im] at hre him hre' him'
    have hb2 : b ^ 2 ≤ 4 * p := by
      have h0 := Real.sq_sqrt hp.le
      have := sq_abs b
      have h3 : |b| ^ 2 ≤ (2 * Real.sqrt p) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      nlinarith
    have key : β.re = α.re ∧ β.im = -α.im := by
      have hy : β.im = -α.im := by linarith
      refine ⟨?_, hy⟩
      by_cases hv : α.im = 0
      · have hy0 : β.im = 0 := by rw [hy, hv]; simp
        rw [hv, hy0] at hre'
        have hs : (α.re + β.re) ^ 2 = b ^ 2 := by rw [hre]; ring
        have : (α.re - β.re) ^ 2 ≤ 0 := by nlinarith
        nlinarith [sq_nonneg (α.re - β.re)]
      · rw [hy] at him'
        have : α.im * (β.re - α.re) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hv
        · linarith
    have hn : ∀ z : ℂ, z.re ^ 2 + z.im ^ 2 = p → ‖z‖ = Real.sqrt p := by
      intro z hz
      rw [← hz, Complex.norm_def, Complex.normSq_apply]
      congr 1; ring
    have hα : α.re ^ 2 + α.im ^ 2 = p := by
      rw [key.1, key.2] at hre'; nlinarith
    refine ⟨hn α hα, hn β ?_⟩
    rw [key.1, key.2]; nlinarith

/-- $\#E(\mathbb F_{p^1})$, computed over `GaloisField p 1`, is $\#E(\mathbb F_p)$ (the points over the two
isomorphic fields correspond under the base change map). -/
theorem numPoints_one (W : WeierstrassCurve (ZMod p)) :
    numPoints W 1 = Nat.card W.toAffine.Point := by
  have hinj : Function.Injective (algebraMap (ZMod p) (GaloisField p 1)) :=
    (algebraMap (ZMod p) (GaloisField p 1)).injective
  have hbij : Function.Bijective (algebraMap (ZMod p) (GaloisField p 1)) := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_zmod, GaloisField.card p 1 one_ne_zero, pow_one]
  classical
  symm
  refine Nat.card_congr (Equiv.ofBijective (Affine.Point.baseChange (W' := W.toAffine) (ZMod p) (GaloisField p 1))
    ⟨Affine.Point.map_injective _, ?_⟩)
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, rfl⟩
  · obtain ⟨a, rfl⟩ := hbij.2 x
    obtain ⟨b, rfl⟩ := hbij.2 y
    exact ⟨Affine.Point.some a b ((Affine.baseChange_nonsingular (W := W.toAffine) (f := Algebra.ofId (ZMod p) (GaloisField p 1)) hinj a b).mp h), rfl⟩

/-- The Hasse bound (`Theorem9_4`) with Theorem 9.10 gives the Riemann hypothesis for $E$ (Remark 9.11(b)): the
reciprocal roots $\alpha, \beta$ have absolute value $\sqrt p$. -/
@[kb "milne2006ec" "Ch. IV, Remark 9.11(b), pdf p. 165"]
theorem riemannHypothesis_of_hasse (h94 : Theorem9_4) (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] (α β : ℂ)
    (hsum : α + β = p + 1 - numPoints W 1) (hprod : α * β = p) :
    ‖α‖ = Real.sqrt p ∧ ‖β‖ = Real.sqrt p := by
  have h1 := h94.bound p W
  rw [← numPoints_one] at h1
  refine (remark_9_11_b (p : ℝ) ((numPoints W 1 : ℝ) - p - 1) (by exact_mod_cast (Fact.out : p.Prime).pos)
    α β ?_ ?_).2 ?_
  · rw [hsum]; push_cast; ring
  · rw [hprod]; simp
  · have : |(numPoints W 1 : ℝ) - p - 1| = |(numPoints W 1 : ℝ) - (p + 1)| := by ring_nf
    rw [this]; exact h1

end Zeta

end NumberFieldKB.MilneEC
