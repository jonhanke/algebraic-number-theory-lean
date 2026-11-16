/-
Vendored from Formal Conjectures (Google DeepMind), <https://github.com/google-deepmind/formal-conjectures>,
commit `e028240a`. Copyright 2026 The Formal Conjectures Authors, licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). The regulator definitions there are adapted from Tau Ceti
(copyright (c) 2026 The Tau Ceti contributors, Apache-2.0).

Changes for this library (2026-11-15):
* all declarations moved into the namespace `NumberFieldKB.FormalConjectures` (Mathlib v4.35.0 already has
  `WeierstrassCurve.Affine.Point.naiveHeight`, which would clash);
* the `module` / `public import` / `@[expose]` headers and the `category` attributes removed;
* `ContinuousCohomology.tateShafarevich` is taken from Mathlib v4.35.0, which contains it verbatim;
* Formal Conjectures' `bsdQuotient` and `StrongBSD` use the local instance `EllipticCurveRank.mordell_weil`, a
  theorem proved there by `sorry`. Here finite generation of $E(K)$ is an explicit instance argument
  `[Module.Finite ℤ E.Point]` instead; no `sorry` is used;
* the `sorry`-proved conjectures themselves (`weakBSD`, `strongBSD`, `exists_hasAnalyticContinuation_rat`, ...) are
  **not** vendored: only the `Prop`-valued definitions are, and nothing here assumes them.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.NumberTheory.Height.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RepresentationTheory.Homological.ContCohomology.Sha
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Norm.Defs
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Topology.Order.Basic

/-!
# Formal Conjectures: the invariants and statements of the Birch and Swinnerton-Dyer conjecture

The definitions of Formal Conjectures' files
`FormalConjecturesForMathlib/AlgebraicGeometry/EllipticCurve/{TateShafarevich, Regulator, Tamagawa,
MinimalDiscriminant, GlobalPeriod}.lean`, `FormalConjectures/Wikipedia/HasseWeil.lean` (the predicates only) and
`FormalConjectures/Millennium/BSD.lean` (the predicates only), with the changes listed in the header. They are the
reference statements against which Milne's Conjectures IV.10.3 and IV.10.5 are compared in
`NumberFieldKB.MilneEC.Ch4BSD`.

* `galoisRepresentation`, `tateShafarevich`: $Ш(E/K)$ as a subgroup of continuous $H^1$ of the discrete module
  $E(\bar K)$.
* `canonicalHeight`, `neronTatePairing`, `regulator`: $\hat h(P) = \lim 4^{-n} h_x(2^nP)$, the pairing
  $(\hat h(P+Q) - \hat h(P) - \hat h(Q))/2$ (note the factor $1/2$), and the absolute determinant of its Gram matrix
  on lifts of a basis of $E(K)/E(K)_{\mathrm{tors}}$.
* `nonsingularReduction`, `tamagawaNumber`, `tamagawaProduct`: $c_v = (E(K_v) : E_0(K_v))$ and $\prod_v c_v$.
* `minimalDiscriminant`, `realPeriod`, `complexPeriod`, `period`: the global period $\Omega(E)$.
* `HasMeromorphicContinuation`, `HasAnalyticContinuation`: continuations of `E.LSeries` from $\Re s > 3/2$.
* `WeakBSD`, `bsdQuotient`, `StrongBSD`: the conjecture following Dokchitser–Dokchitser 2010, Conjecture 2.1.
-/

open WeierstrassCurve IsDedekindDomain NumberField

namespace NumberFieldKB.FormalConjectures

/-! ## The Tate–Shafarevich group (`TateShafarevich.lean`) -/

section TateShafarevich

open WeierstrassCurve.Affine

variable {K : Type} [Field K] (W : Affine K)

@[simp]
lemma absoluteGaloisGroup_one_toAlgHom :
    (1 : Field.absoluteGaloisGroup K).toAlgHom = AlgHom.id K (AlgebraicClosure K) := rfl

@[simp]
lemma absoluteGaloisGroup_mul_toAlgHom (σ τ : Field.absoluteGaloisGroup K) :
    (σ * τ).toAlgHom = σ.toAlgHom.comp τ.toAlgHom := rfl

/-- The geometric non-singular points as a topological space (discrete). -/
local instance instTopPoint : TopologicalSpace (W⁄(AlgebraicClosure K)).Point := ⊥

local instance instDiscretePoint : DiscreteTopology (W⁄(AlgebraicClosure K)).Point := ⟨rfl⟩

@[simp]
lemma point_map_id' {R S F : Type*} [CommRing R] [CommRing S]
    [Field F] {W' : WeierstrassCurve.Affine R} [DecidableEq F] [Algebra R S] [Algebra R F]
    [Algebra S F] [IsScalarTower R S F] (P : (W'.baseChange F).Point) :
    WeierstrassCurve.Affine.Point.map (AlgHom.id S F) P = P := by
  cases P <;> rfl

lemma continuousLinearMap_mk_apply {R S M M₂ : Type*} [Semiring R] [Semiring S]
    {σ : R →+* S} [TopologicalSpace M] [AddCommMonoid M] [TopologicalSpace M₂]
    [AddCommMonoid M₂] [Module R M] [Module S M₂] (toLinearMap : M →ₛₗ[σ] M₂)
    (cont : Continuous toLinearMap.toFun) (m : M) :
    ContinuousLinearMap.mk toLinearMap cont m = toLinearMap m := rfl

open scoped Classical in
/-- The natural Galois action on geometric non-singular points with their discrete topology (Formal Conjectures'
`WeierstrassCurve.Affine.galoisRepresentation`). -/
noncomputable def galoisRepresentation : TopRep ℤ (Field.absoluteGaloisGroup K) := .of <|
  .ofMonoidHom {
    toFun σ := { __ := (Affine.Point.map (W' := W) σ.toAlgHom).toIntLinearMap }
    map_one' := by ext; simp
    map_mul' σ τ := by ext; simp [continuousLinearMap_mk_apply _, Point.map_map] }

/-- Formal Conjectures' **Tate–Shafarevich group** `WeierstrassCurve.Affine.tateShafarevich`: the classes of the
first continuous Galois cohomology group of $E(\bar K)$ whose restrictions vanish at every infinite and finite
place. -/
noncomputable def tateShafarevich [NumberField K] :
    AddSubgroup (continuousCohomology 1 (galoisRepresentation W)) :=
  ContinuousCohomology.tateShafarevich
      (fun v : InfinitePlace K ↦ v.Completion) (galoisRepresentation W) 1 ⊓
    ContinuousCohomology.tateShafarevich
      (fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K) (galoisRepresentation W) 1

end TateShafarevich

/-! ## Heights and the regulator (`Regulator.lean`) -/

section Regulator

open WeierstrassCurve.Affine

variable {K : Type*} [DecidableEq K] [Field K] [Height.AdmissibleAbsValues K] {W : Affine K}

/-- The logarithmic height $h_x$ of the $x$-coordinate, with value zero at infinity. -/
noncomputable def naiveHeight : W.Point → ℝ
  | .zero => 0
  | .some x .. => Height.logHeight₁ x

/-- The canonical height $\lim_n 4^{-n} h_x(2^nP)$. -/
noncomputable def canonicalHeight (P : W.Point) : ℝ :=
  Filter.atTop.limUnder fun n : ℕ ↦ naiveHeight (2 ^ n • P) / 4 ^ n

/-- The Néron–Tate height pairing, by polarisation of the canonical height: $(\hat h(P+Q) - \hat h(P) - \hat h(Q))/2$. -/
noncomputable def neronTatePairing (P Q : W.Point) : ℝ :=
  (canonicalHeight (P + Q) - canonicalHeight P - canonicalHeight Q) / 2

/-- The Gram matrix of the Néron–Tate height pairing on a family of points. -/
noncomputable def neronTateMatrix {ι : Type*} (P : ι → W.Point) : Matrix ι ι ℝ :=
  fun i j => neronTatePairing (P i) (P j)

variable (W) in
/-- The absolute determinant of the height pairing on lifts of a finite basis of $E(K)$ modulo torsion
(the non-normalised regulator). -/
noncomputable def regulator [Module.Finite ℤ (W.Point ⧸ Submodule.torsion ℤ W.Point)] : ℝ :=
  |(neronTateMatrix (Quotient.out ∘ Module.finBasis ℤ (W.Point ⧸ Submodule.torsion ℤ W.Point))).det|

end Regulator

/-! ## Tamagawa numbers (`Tamagawa.lean`) -/

section Tamagawa

open WeierstrassCurve.Projective

/-- The points with an integral projective representative whose reduction is non-singular. -/
def nonsingularReduction {R : Type*} [CommRing R] [IsLocalRing R] (K : Type*) [CommRing K]
    [Algebra R K] (W : Projective R) : Set (W⁄K).Point :=
  {P : (W⁄K).Point | ∃ q : Fin 3 → R, P.point = ⟦(algebraMap R K <| q ·)⟧ ∧
    (W.map <| IsLocalRing.residue R).Nonsingular (IsLocalRing.residue R <| q ·)}

/-- The local Tamagawa number attached to an integral model; $0$ if there are infinitely many translates. -/
noncomputable def tamagawaNumber {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type*)
    [Field K] [Algebra R K] [IsFractionRing R K] (W : Projective R) : ℕ :=
  Nat.card <| Set.range fun P : (W⁄K).Point ↦ (P + ·) '' nonsingularReduction K W

/-- The product of local Tamagawa numbers of minimal integral models at all non-archimedean completions. -/
noncomputable def tamagawaProduct {K : Type*} [Field K] [NumberField K] (W : Projective K) : ℕ :=
  ∏ᶠ v : HeightOneSpectrum (RingOfIntegers K), tamagawaNumber (v.adicCompletion K)
    (W⁄(v.adicCompletion K) |>.minimal (v.adicCompletionIntegers K) |>.integralModel <|
      v.adicCompletionIntegers K)

end Tamagawa

/-! ## Minimal discriminant and period (`MinimalDiscriminant.lean`, `GlobalPeriod.lean`) -/

section Period

variable {K : Type*} [Field K] [NumberField K]

/-- The exponent of `v` in the minimal discriminant ideal of `W`. -/
noncomputable def minimalDiscriminantExponent (W : WeierstrassCurve K) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (-WithZero.log ((IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers K)).valuation
    (v.adicCompletion K) ((W⁄(v.adicCompletion K)).minimal (v.adicCompletionIntegers K)).Δ)).toNat

/-- The minimal discriminant ideal $\prod_v v^{n_v}$. -/
noncomputable def minimalDiscriminant (W : WeierstrassCurve K) : Ideal (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ minimalDiscriminantExponent W v

/-- The density $1/\sqrt{4x^3 + b_2x^2 + 2b_4x + b_6}$ on the real $x$-line, $0$ where the cubic is not positive. -/
noncomputable def realPeriodIntegrand (W : WeierstrassCurve ℝ) (x : ℝ) : ℝ := (√(W.Ψ₂Sq.eval x))⁻¹

/-- **The real period**: $\int_{E(\mathbb R)} |\omega| = 2\int_{\mathbb R} dx/\sqrt{F(x)}$. -/
noncomputable def realPeriod (W : WeierstrassCurve ℝ) : ℝ := 2 * ∫ x, realPeriodIntegrand W x

/-- The density $1/|\Psi_2^2(x)|$ on the complex $x$-line. -/
noncomputable def complexPeriodIntegrand (W : WeierstrassCurve ℂ) (x : ℂ) : ℝ := ‖W.Ψ₂Sq.eval x‖⁻¹

/-- **The complex period**: $4\int_{\mathbb C} dA(x)/|\Psi_2^2(x)|$. -/
noncomputable def complexPeriod (W : WeierstrassCurve ℂ) : ℝ := 4 * ∫ x : ℂ, complexPeriodIntegrand W x

open scoped Classical in
/-- The **global period** $\Omega(E) = (|N_{K/\mathbb Q}(\Delta_E)| / N(\mathfrak D_{E/K}))^{1/12}\prod_v\Omega_v(E)$. -/
noncomputable def period (E : WeierstrassCurve K) : ℝ :=
  (|(Algebra.norm ℚ E.Δ : ℝ)| / (minimalDiscriminant E).absNorm) ^ (1 / 12 : ℝ) *
    ∏ v : NumberField.InfinitePlace K,
      if hv : v.IsReal then realPeriod (E.map <| NumberField.InfinitePlace.embedding_of_isReal hv)
        else complexPeriod (E.map v.embedding)

end Period

/-! ## Continuations of the $L$-series (`HasseWeil.lean`, predicates only) -/

section HasseWeil

variable {K : Type*} [Field K] [NumberField K]

/-- `L` is meromorphic on $\mathbb C$ and agrees with `E.LSeries` on $\Re s > 3/2$. -/
def HasMeromorphicContinuation (E : WeierstrassCurve K) (L : ℂ → ℂ) : Prop :=
  Meromorphic L ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- `L` is analytic on $\mathbb C$ and agrees with `E.LSeries` on $\Re s > 3/2$. -/
def HasAnalyticContinuation (E : WeierstrassCurve K) (L : ℂ → ℂ) : Prop :=
  (∀ z, AnalyticAt ℂ L z) ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- An analytic continuation is a meromorphic continuation. -/
theorem HasAnalyticContinuation.hasMeromorphicContinuation {E : WeierstrassCurve K} {L : ℂ → ℂ}
    (hL : HasAnalyticContinuation E L) : HasMeromorphicContinuation E L :=
  ⟨fun z ↦ (hL.1 z).meromorphicAt, hL.2⟩

open scoped Topology in
/-- A meromorphic continuation is unique away from isolated points: two meromorphic continuations of the
$L$-series of `E` agree on a punctured neighbourhood of every point (Formal Conjectures'
`HasMeromorphicContinuation.unique`). -/
theorem HasMeromorphicContinuation.unique {E : WeierstrassCurve K} {L L' : ℂ → ℂ}
    (hL : HasMeromorphicContinuation E L) (hL' : HasMeromorphicContinuation E L') (x : ℂ) :
    L =ᶠ[𝓝[≠] x] L' := by
  have h2 : meromorphicOrderAt (L - L') 2 = ⊤ := meromorphicOrderAt_eq_top_iff.2 <|
    Filter.eventually_of_mem (nhdsWithin_le_nhds <| (Complex.isOpen_re_gt (3 / 2)).mem_nhds
      (by norm_num)) fun s hs ↦ sub_eq_zero.2 ((hL.2 s hs).trans (hL'.2 s hs).symm)
  have key : meromorphicOrderAt (L - L') x = ⊤ := not_not.1 fun hx ↦
    (hL.1.sub hL'.1).exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨x, hx⟩ 2 h2
  exact (meromorphicOrderAt_eq_top_iff.1 key).mono fun s hs ↦ sub_eq_zero.1 hs

/-- The statement of Formal Conjectures' `HasseWeil.exists_hasAnalyticContinuation_rat` (there proved by `sorry`;
"research solved" by modularity), as a `Prop`. -/
def ExistsAnalyticContinuationRat : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ∃ L, HasAnalyticContinuation E L

/-- The statement of Formal Conjectures' `HasseWeil.exists_hasMeromorphicContinuation` over $\mathbb Q$. -/
def ExistsMeromorphicContinuationRat : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ∃ L, HasMeromorphicContinuation E L

end HasseWeil

/-! ## The Birch and Swinnerton-Dyer conjecture (`BSD.lean`, predicates only) -/

section BSD

open WeierstrassCurve.Affine

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] (E : Affine K)

/-- The **weak Birch and Swinnerton-Dyer conjecture** for `E`: a meromorphic continuation of the $L$-series has
order $\operatorname{rk} E(K)$ at $s = 1$. -/
def WeakBSD : Prop :=
  ∃ L : ℂ → ℂ, HasMeromorphicContinuation E L ∧ meromorphicOrderAt L 1 = Module.finrank ℤ E.Point

/-- The *BSD quotient* of Dokchitser–Dokchitser 2010. The finite generation of $E(K)$ (Mordell–Weil, a `sorry`ed
instance in Formal Conjectures) is an instance argument here. -/
noncomputable def bsdQuotient [E.IsElliptic] [Module.Finite ℤ E.Point] : ℝ :=
  period (E : WeierstrassCurve K) * regulator E * Nat.card (tateShafarevich E) *
      tamagawaProduct (E : WeierstrassCurve K).toProjective /
    (|(discr K : ℝ)|.sqrt * (Nat.card <| AddCommGroup.torsion E.Point) ^ 2 : ℝ)

/-- The **strong Birch and Swinnerton-Dyer conjecture** for `E`: a meromorphic continuation of its $L$-series has
order $\operatorname{rk} E(K)$ at $s = 1$, $Ш(E/K)$ is finite, and the leading coefficient is `bsdQuotient E`. -/
def StrongBSD [E.IsElliptic] [Module.Finite ℤ E.Point] : Prop := ∃ L : ℂ → ℂ,
  HasMeromorphicContinuation E L ∧ meromorphicOrderAt L 1 = Module.finrank ℤ E.Point ∧
    Finite (tateShafarevich E) ∧ meromorphicTrailingCoeffAt L 1 = bsdQuotient E

/-- Strong implies weak. -/
theorem StrongBSD.weakBSD [E.IsElliptic] [Module.Finite ℤ E.Point] (h : StrongBSD E) : WeakBSD E :=
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1⟩

end BSD

end NumberFieldKB.FormalConjectures
