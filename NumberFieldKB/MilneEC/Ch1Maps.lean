import NumberFieldKB.MilneEC.Ch1Functions
import NumberFieldKB.MilneEC.Ch1Examples
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.TotallySplit
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star

/-!
# Milne, Elliptic Curves, Chapter I, Section 4: regular maps of curves

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, §4, subsection "Regular maps of curves"
(pdf pp. 46–50): regular maps of affine plane curves (Lemma 4.15, Proposition 4.16), regular maps of
projective plane curves, Example 4.17, Proposition 4.18 and Remark 4.19 (named statements), Example 4.20,
Definition 4.21, Propositions 4.23, 4.24 (named statements), the degree of a map, Example 4.25, Remark 4.26
(named statement).

**Universes.** Milne quantifies over "all fields `K` containing `k`"; here over all fields `K` in the
universe of `k`.

**Regular maps of projective plane curves.** Milne gives no precise definition ("Rather than give a
precise definition (see AG, 6)", p. 47): a regular map is given locally by homogeneous polynomials of the
same degree not all vanishing.  `ProjRegularMap F F'` is a family of maps $C(K) \to C'(K)$, one for each
field `K ⊇ k`, such that every point has a neighbourhood $\{G_0, G_1, G_2 \text{ not all } 0\}$ on which the
map is $Q \mapsto (G_0(Q) : G_1(Q) : G_2(Q))$, with $G_i \in k[X, Y, Z]$ homogeneous of one degree.

**Pullback of functions.** For the degree of a map (p. 49), a $k$-embedding $\iota : k(C') \to k(C)$ is a
pullback along $\varphi$ if $\iota(h)$ takes the value $h(\varphi(P))$ at every point `P` where `h` is defined
at $\varphi(P)$ (`IsPullback`); the degree is $[k(C) : \iota k(C')]$.
-/

open MvPolynomial
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace NumberFieldKB.MilneEC

universe u

variable {k : Type u} [Field k]

/-! ### Regular maps of affine plane curves -/

/-- The value at a point `P ∈ C_g(K)` of a regular function $\varphi \in k[C_g]$. -/
def evalCoord {g : MvPolynomial (Fin 2) k} {K : Type*} [Field K] [Algebra k K] {P : K × K}
    (hP : P ∈ affinePoints g K) (φ : coordinateRing g) : K :=
  Ideal.Quotient.lift (Ideal.span {g}) (aeval ![P.1, P.2]).toRingHom
    (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul]
      have : aeval ![P.1, P.2] g = 0 := hP
      rw [this, mul_zero]) φ

/-- A **regular map** $C_{g_1} \to C_{g_2}$ of affine plane curves (p. 46): a pair $(f_1, f_2)$ of regular
functions on $C_{g_1}$ sending $C_{g_1}(K)$ into $C_{g_2}(K)$ for every field `K` containing `k`. -/
@[kb "milne2006ec" "Ch. I, §4, Def. of regular map of affine plane curves, pdf p. 46"]
def IsAffineRegularMap (g₁ g₂ : MvPolynomial (Fin 2) k) (f : Fin 2 → coordinateRing g₁) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] (P : K × K) (hP : P ∈ affinePoints g₁ K),
    (evalCoord hP (f 0), evalCoord hP (f 1)) ∈ affinePoints g₂ K

/-- Applying a `k`-linear retraction of `k → K` to the coefficients of a polynomial over `K`. -/
def retractCoeff {σ K : Type*} [Field K] [Algebra k K] (l : K →ₗ[k] k) (q : MvPolynomial σ K) :
    MvPolynomial σ k :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange l l.map_zero q.coeff)

theorem coeff_retractCoeff {σ K : Type*} [Field K] [Algebra k K] (l : K →ₗ[k] k)
    (q : MvPolynomial σ K) (s : σ →₀ ℕ) :
    (retractCoeff l q).coeff s = l (q.coeff s) :=
  Finsupp.mapRange_apply (f := l) (hf := l.map_zero) (a := s) (g := q.coeff)

theorem retractCoeff_mul {σ K : Type*} [Field K] [Algebra k K] (l : K →ₗ[k] k)
    (p : MvPolynomial σ k) (q : MvPolynomial σ K) :
    retractCoeff l (map (algebraMap k K) p * q) = p * retractCoeff l q := by
  classical
  ext u
  rw [coeff_retractCoeff, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_retractCoeff, ← Algebra.smul_def, map_smul, smul_eq_mul]

/-- Divisibility descends along a field extension: if `p` divides `g` after extending scalars to `K`,
then `p` divides `g`. -/
theorem dvd_of_map_dvd {σ K : Type*} [Field K] [Algebra k K] {p g : MvPolynomial σ k}
    (h : map (algebraMap k K) p ∣ map (algebraMap k K) g) : p ∣ g := by
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k K)
    (by simp [LinearMap.ker_eq_bot, Function.Injective])
  have hl' : ∀ c : k, l (algebraMap k K c) = c := fun c => LinearMap.congr_fun hl c
  obtain ⟨q, hq⟩ := h
  refine ⟨retractCoeff l q, ?_⟩
  rw [← retractCoeff_mul l, ← hq]
  ext u
  rw [coeff_retractCoeff, coeff_map, hl']

/-- Nullstellensatz for a squarefree equation: a polynomial over `k` vanishing on the points of
$C_{g_1}(k^{\mathrm{al}})$ is divisible by `g₁`, if `g₁` has no repeated factor over $k^{\mathrm{al}}$. -/
theorem dvd_of_vanishes_squarefree {g₁ : MvPolynomial (Fin 2) k} (hg₁ : IsAffinePlaneCurve g₁)
    (g : MvPolynomial (Fin 2) k)
    (H : ∀ P ∈ affinePoints g₁ (AlgebraicClosure k), evalAt g P = 0) : g₁ ∣ g := by
  apply dvd_of_map_dvd (K := AlgebraicClosure k)
  have hpt : ∀ x : Fin 2 → AlgebraicClosure k, (![x 0, x 1] : Fin 2 → AlgebraicClosure k) = x := by
    intro x
    funext i
    fin_cases i <;> rfl
  have hg : map (algebraMap k (AlgebraicClosure k)) g ∈
      vanishingIdeal (AlgebraicClosure k) (zeroLocus (AlgebraicClosure k)
        (Ideal.span {map (algebraMap k (AlgebraicClosure k)) g₁} :
          Ideal (MvPolynomial (Fin 2) (AlgebraicClosure k)))) := by
    intro x hx
    have hfx : aeval x (map (algebraMap k (AlgebraicClosure k)) g₁) = 0 :=
      hx _ (Ideal.subset_span rfl)
    have hmem : ((x 0, x 1) : AlgebraicClosure k × AlgebraicClosure k) ∈
        affinePoints g₁ (AlgebraicClosure k) := by
      show evalAt g₁ (x 0, x 1) = 0
      simp only [evalAt]
      rw [hpt x, ← aeval_map_algebraMap (AlgebraicClosure k)]
      exact hfx
    have := H _ hmem
    simp only [evalAt] at this
    rw [hpt x] at this
    rw [aeval_map_algebraMap]
    exact this
  rw [vanishingIdeal_zeroLocus_eq_radical] at hg
  obtain ⟨n, hn⟩ := hg
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp only [pow_zero, Ideal.mem_span_singleton] at hn
    exact (hn.trans (one_dvd _)).trans (one_dvd _)
  · exact (hg₁.2.dvd_pow_iff_dvd hn0.ne').mp (Ideal.mem_span_singleton.mp hn)

theorem evalCoord_mk {g : MvPolynomial (Fin 2) k} {K : Type*} [Field K] [Algebra k K] {P : K × K}
    (hP : P ∈ affinePoints g K) (φ : MvPolynomial (Fin 2) k) :
    evalCoord hP (Ideal.Quotient.mk (Ideal.span {g}) φ) = evalAt φ P := rfl

theorem evalAt_aeval {K : Type*} [Field K] [Algebra k K] (F : Fin 2 → MvPolynomial (Fin 2) k)
    (g : MvPolynomial (Fin 2) k) (P : K × K) :
    evalAt (aeval F g) P = evalAt g (evalAt (F 0) P, evalAt (F 1) P) := by
  have : (aeval ![P.1, P.2] : MvPolynomial (Fin 2) k →ₐ[k] K).comp (aeval F) =
      aeval ![evalAt (F 0) P, evalAt (F 1) P] := by
    ext i
    fin_cases i <;> simp [evalAt]
  simp only [evalAt]
  exact (AlgHom.congr_fun this g)

/-- **Lemma 4.15** (p. 47): a pair $(f_1, f_2)$ of regular functions on the curve $C_{g_1}$ maps
$C_{g_1}(K)$ into $C_{g_2}(K)$ for all fields `K ⊇ k` if and only if $g_2(f_1, f_2) = 0$ in $k[C_{g_1}]$. -/
@[kb "milne2006ec" "Ch. I, Lem. 4.15, pdf p. 47"]
theorem lemma_4_15 {g₁ : MvPolynomial (Fin 2) k} (hg₁ : IsAffinePlaneCurve g₁)
    (g₂ : MvPolynomial (Fin 2) k) (f : Fin 2 → coordinateRing g₁) :
    IsAffineRegularMap g₁ g₂ f ↔ aeval f g₂ = 0 := by
  obtain ⟨F, hF⟩ : ∃ F : Fin 2 → MvPolynomial (Fin 2) k,
      f = fun i => Ideal.Quotient.mk (Ideal.span {g₁}) (F i) :=
    ⟨fun i => (Ideal.Quotient.mk_surjective (f i)).choose,
      funext fun i => ((Ideal.Quotient.mk_surjective (f i)).choose_spec).symm⟩
  subst hF
  have key : aeval (fun i => (Ideal.Quotient.mk (Ideal.span {g₁}) (F i))) g₂ =
      Ideal.Quotient.mk (Ideal.span {g₁}) (aeval F g₂) := by
    have : (Ideal.Quotient.mkₐ k (Ideal.span {g₁})).comp (aeval F) =
        aeval (fun i => (Ideal.Quotient.mk (Ideal.span {g₁}) (F i))) := by
      ext i; simp
    exact (AlgHom.congr_fun this g₂).symm
  rw [key, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  constructor
  · intro hf
    apply dvd_of_vanishes_squarefree hg₁
    intro P hP
    rw [evalAt_aeval]
    exact hf (AlgebraicClosure k) P hP
  · rintro ⟨q, hq⟩ K _ _ P hP
    have h0 : evalAt g₁ P = 0 := hP
    have : evalAt (aeval F g₂) P = 0 := by
      rw [hq]
      simp only [evalAt] at h0 ⊢
      rw [map_mul, h0, zero_mul]
    rw [evalAt_aeval] at this
    exact this

/-- **Proposition 4.16** (p. 47): for absolutely irreducible affine plane curves, regular maps
$C_{g_1} \to C_{g_2}$ (a), pairs $(f_1, f_2)$ with $g_2(f_1, f_2) = 0$ (b), and homomorphisms of
`k`-algebras $k[C_{g_2}] \to k[C_{g_1}]$ (d) correspond: (a) ⟺ (b) is Lemma 4.15; the bijection
(b) ≃ (d) sends `ψ` to the images of the coordinate functions $x, y$.  For (c): the functorial maps on
points determine the pair (`affineRegularMap_ext`). -/
@[kb "milne2006ec" "Ch. I, Prop. 4.16, pdf p. 47"]
def prop_4_16 (g₁ g₂ : MvPolynomial (Fin 2) k) :
    (coordinateRing g₂ →ₐ[k] coordinateRing g₁) ≃ {f : Fin 2 → coordinateRing g₁ // aeval f g₂ = 0} where
  toFun ψ := ⟨fun i => ψ (Ideal.Quotient.mk _ (X i)), by
    have h : ψ.comp (Ideal.Quotient.mkₐ k (Ideal.span {g₂})) =
        aeval (fun i => ψ (Ideal.Quotient.mk _ (X i))) := by
      ext i; simp
    have h2 := AlgHom.congr_fun h g₂
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h2
    have h3 : (Ideal.Quotient.mk (Ideal.span {g₂})) g₂ = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [← h2, h3, map_zero]⟩
  invFun f := Ideal.Quotient.liftₐ (Ideal.span {g₂}) (aeval f.1) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp only [map_mul, f.2, mul_zero])
  left_inv ψ := by
    apply Ideal.Quotient.algHom_ext
    ext i
    exact aeval_X _ i
  right_inv f := by
    apply Subtype.ext
    funext i
    exact aeval_X _ i

theorem prop_4_16_apply (g₁ g₂ : MvPolynomial (Fin 2) k) (ψ : coordinateRing g₂ →ₐ[k] coordinateRing g₁)
    (i : Fin 2) : (prop_4_16 g₁ g₂ ψ).1 i = ψ (Ideal.Quotient.mk _ (X i)) := rfl

/-- **Proposition 4.16 (c)** (p. 47): a regular map is determined by the maps it induces on points (for
an absolutely irreducible curve $C_{g_1}$; points over $k^{\mathrm{al}}$ suffice). -/
@[kb "milne2006ec" "Ch. I, Prop. 4.16 (c), pdf p. 47"]
theorem affineRegularMap_ext {g₁ : MvPolynomial (Fin 2) k} (hg₁ : IsAffinePlaneCurve g₁)
    (f f' : Fin 2 → coordinateRing g₁)
    (h : ∀ (P : AlgebraicClosure k × AlgebraicClosure k) (hP : P ∈ affinePoints g₁ _) (i : Fin 2),
      evalCoord hP (f i) = evalCoord hP (f' i)) : f = f' := by
  funext i
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (f i)
  obtain ⟨a', ha'⟩ := Ideal.Quotient.mk_surjective (f' i)
  rw [← ha, ← ha']
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  apply dvd_of_vanishes_squarefree hg₁
  intro P hP
  have := h P hP i
  rw [← ha, ← ha', evalCoord_mk, evalCoord_mk] at this
  simp only [evalAt] at this ⊢
  rw [map_sub, this, sub_self]

/-! ### Regular maps of projective plane curves -/

/-- A **regular map** $C_F \to C_{F'}$ of projective plane curves over `k` (p. 47; see the module
docstring): maps $C(K) \to C'(K)$ for all fields `K ⊇ k`, given near every point by homogeneous polynomials
$G_0, G_1, G_2 \in k[X, Y, Z]$ of one degree not all vanishing there. -/
@[kb "milne2006ec" "Ch. I, §4, regular maps of projective plane curves, pdf p. 47"]
structure ProjRegularMap (F F' : MvPolynomial (Fin 3) k) where
  /-- The map on points with coordinates in `K`. -/
  toFun : ∀ (K : Type u) [Field K] [Algebra k K], projectivePoints F K → projectivePoints F' K
  /-- Locally given by polynomials. -/
  locally_polynomial : ∀ (K : Type u) [Field K] [Algebra k K] (P : projectivePoints F K),
    ∃ (d : ℕ) (G : Fin 3 → MvPolynomial (Fin 3) k), (∀ i, (G i).IsHomogeneous d) ∧
      (fun i => aeval P.1.rep (G i)) ≠ 0 ∧
      ∀ (Q : projectivePoints F K) (hQ : (fun i => aeval Q.1.rep (G i)) ≠ 0),
        (toFun K Q).1 = Projectivization.mk K _ hQ

theorem aeval_aeval_vec {K : Type*} [Field K] [Algebra k K] (G : Fin 3 → MvPolynomial (Fin 3) k)
    (H : MvPolynomial (Fin 3) k) (v : Fin 3 → K) :
    aeval v (aeval G H) = aeval (fun j => aeval v (G j)) H :=
  comp_aeval_apply _ _ _

/-- The composite of regular maps. -/
def ProjRegularMap.comp {F F' F'' : MvPolynomial (Fin 3) k} (ψ : ProjRegularMap F' F'')
    (φ : ProjRegularMap F F') : ProjRegularMap F F'' where
  toFun K _ _ Q := ψ.toFun K (φ.toFun K Q)
  locally_polynomial K _ _ P := by
    obtain ⟨d, G, hG, hGP, hGloc⟩ := φ.locally_polynomial K P
    obtain ⟨d', H, hH, hHP, hHloc⟩ := ψ.locally_polynomial K (φ.toFun K P)
    refine ⟨d * d', fun i => aeval G (H i), fun i => (hH i).aeval G hG, ?_, ?_⟩
    · obtain ⟨c, hc, hcv⟩ := exists_smul_rep (fun j => aeval P.1.rep (G j)) hGP
      have hy : (φ.toFun K P).1 = Projectivization.mk K _ hGP := hGloc P hGP
      rw [← hy] at hcv
      intro hzero
      apply hHP
      funext i
      have h1 := congr_fun hzero i
      simp only [aeval_aeval_vec, Pi.zero_apply] at h1
      rw [hcv, aeval_smul_of_isHomogeneous (hH i)] at h1
      have : c ^ d' ≠ 0 := pow_ne_zero _ hc
      simpa [this] using h1
    · intro Q hQ
      obtain ⟨c, hcv⟩ : ∃ c : K, (fun j => aeval Q.1.rep (G j)) = c • (φ.toFun K Q).1.rep := by
        by_cases h0 : (fun j => aeval Q.1.rep (G j)) = 0
        · exact ⟨0, by rw [h0, zero_smul]⟩
        · obtain ⟨c, hc, hcv⟩ := exists_smul_rep _ h0
          have : (φ.toFun K Q).1 = Projectivization.mk K _ h0 := hGloc Q h0
          rw [← this] at hcv
          exact ⟨c, hcv⟩
      have hvec : (fun i => aeval Q.1.rep (aeval G (H i))) =
          c ^ d' • fun i => aeval (φ.toFun K Q).1.rep (H i) := by
        funext i
        simp only [aeval_aeval_vec, Pi.smul_apply, smul_eq_mul]
        rw [hcv, aeval_smul_of_isHomogeneous (hH i)]
      have hcd : c ^ d' ≠ 0 ∧ (fun i => aeval (φ.toFun K Q).1.rep (H i)) ≠ 0 := by
        constructor
        · intro h0; apply hQ; rw [hvec, h0, zero_smul]
        · intro h0; apply hQ; rw [hvec, h0, smul_zero]
      have := hHloc (φ.toFun K Q) hcd.2
      show (ψ.toFun K (φ.toFun K Q)).1 = _
      rw [this, Projectivization.mk_eq_mk_iff]
      refine ⟨(Units.mk0 _ hcd.1)⁻¹, ?_⟩
      rw [hvec]
      simp [Units.smul_def, smul_smul, hcd.1]

/-- An **isomorphism** of projective plane curves: regular maps in both directions, inverse on points. -/
def IsProjIso {F F' : MvPolynomial (Fin 3) k} (φ : ProjRegularMap F F') : Prop :=
  ∃ ψ : ProjRegularMap F' F, ∀ (K : Type u) [Field K] [Algebra k K],
    (∀ P, ψ.toFun K (φ.toFun K P) = P) ∧ ∀ Q, φ.toFun K (ψ.toFun K Q) = Q

section Conic

variable (K : Type*) [Field K]

/-- A nonzero vector in any index type is a nonzero scalar multiple of the chosen representative. -/
theorem exists_smul_rep_pi {ι : Type*} (v : ι → K) (hv : v ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ v = c • (Projectivization.mk K v hv).rep := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K v _ hv
    (Projectivization.mk K v hv).rep_nonzero).mp
    (Projectivization.mk_rep (Projectivization.mk K v hv)).symm
  exact ⟨a, a.ne_zero, ha.symm⟩

/-- The vector $(a^2, ab, b^2)$ attached to $(a, b)$. -/
def conicVec (r : Fin 2 → K) : Fin 3 → K := ![r 0 ^ 2, r 0 * r 1, r 1 ^ 2]

theorem conicVec_ne_zero {r : Fin 2 → K} (hr : r ≠ 0) : conicVec K r ≠ 0 := by
  intro h
  apply hr
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  simp [conicVec] at h0 h2
  funext i
  fin_cases i <;> simp [h0, h2]

theorem conicVec_smul (c : K) (r : Fin 2 → K) : conicVec K (c • r) = c ^ 2 • conicVec K r := by
  funext i
  fin_cases i <;> simp [conicVec] <;> ring

theorem conicPoly_isHomogeneous : (X 0 * X 2 - X 1 ^ 2 : MvPolynomial (Fin 3) K).IsHomogeneous 2 :=
  ((isHomogeneous_X K 0).mul (isHomogeneous_X K 2)).sub (isHomogeneous_X_pow (R := K) 1 2)

theorem aeval_conicPoly (v : Fin 3 → K) :
    aeval v (X 0 * X 2 - X 1 ^ 2 : MvPolynomial (Fin 3) K) = v 0 * v 2 - v 1 ^ 2 := by
  simp

/-- The map $\mathbb P^1 \to C$, $(a : b) \mapsto (a^2 : ab : b^2)$. -/
def conicFwd (P : ℙ K (Fin 2 → K)) :
    projectivePoints (X 0 * X 2 - X 1 ^ 2 : MvPolynomial (Fin 3) K) K :=
  ⟨Projectivization.mk K (conicVec K P.rep) (conicVec_ne_zero K P.rep_nonzero), by
    rw [mem_projectivePoints_mk (conicPoly_isHomogeneous K), aeval_conicPoly]
    simp [conicVec]
    ring⟩

theorem conicFwd_mk (v : Fin 2 → K) (hv : v ≠ 0) :
    (conicFwd K (Projectivization.mk K v hv)).1 =
      Projectivization.mk K (conicVec K v) (conicVec_ne_zero K hv) := by
  obtain ⟨c, hc, hvc⟩ := exists_smul_rep_pi K v hv
  unfold conicFwd
  simp only
  rw [Projectivization.mk_eq_mk_iff]
  refine ⟨(Units.mk0 (c ^ 2) (pow_ne_zero 2 hc))⁻¹, ?_⟩
  conv_lhs => rw [hvc, conicVec_smul]
  simp [Units.smul_def, smul_smul, hc]

theorem conicFwd_injective : Function.Injective (conicFwd K) := by
  intro P P' h
  have h1 : (conicFwd K P).1 = (conicFwd K P').1 := congrArg Subtype.val h
  unfold conicFwd at h1
  simp only at h1
  rw [Projectivization.mk_eq_mk_iff] at h1
  obtain ⟨a, ha⟩ := h1
  have e0 : (a : K) * P'.rep 0 ^ 2 = P.rep 0 ^ 2 := by
    simpa [conicVec, Units.smul_def] using congrFun ha 0
  have e1 : (a : K) * (P'.rep 0 * P'.rep 1) = P.rep 0 * P.rep 1 := by
    simpa [conicVec, Units.smul_def] using congrFun ha 1
  have e2 : (a : K) * P'.rep 1 ^ 2 = P.rep 1 ^ 2 := by
    simpa [conicVec, Units.smul_def] using congrFun ha 2
  rw [← Projectivization.mk_rep P, ← Projectivization.mk_rep P', Projectivization.mk_eq_mk_iff]
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  by_cases hv0 : P.rep 0 = 0
  · have hv1 : P.rep 1 ≠ 0 := by
      intro h1
      apply P.rep_nonzero
      funext i
      fin_cases i <;> simp [hv0, h1]
    have hw0 : P'.rep 0 = 0 := by
      have : (a : K) * P'.rep 0 ^ 2 = 0 := by rw [e0, hv0]; ring
      have := (mul_eq_zero.mp this).resolve_left ha0
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have hw1 : P'.rep 1 ≠ 0 := by
      intro h1
      rw [h1] at e2
      apply hv1
      have : P.rep 1 ^ 2 = 0 := by rw [← e2]; ring
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    refine ⟨Units.mk0 (P.rep 1 / P'.rep 1) (div_ne_zero hv1 hw1), ?_⟩
    funext i
    fin_cases i
    · simp [hv0, hw0]
    · simp [Units.smul_def]
      field_simp
  · have hw0 : P'.rep 0 ≠ 0 := by
      intro h0
      rw [h0] at e0
      apply hv0
      have : P.rep 0 ^ 2 = 0 := by rw [← e0]; ring
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have hcross : P.rep 0 * P'.rep 1 = P'.rep 0 * P.rep 1 := by
      have : P.rep 0 * (P.rep 0 * P'.rep 1 - P'.rep 0 * P.rep 1) = 0 := by
        linear_combination (-(P'.rep 1)) * e0 + P'.rep 0 * e1
      have := (mul_eq_zero.mp this).resolve_left hv0
      linear_combination this
    refine ⟨Units.mk0 (P.rep 0 / P'.rep 0) (div_ne_zero hv0 hw0), ?_⟩
    funext i
    fin_cases i
    · simp [Units.smul_def]
      field_simp
    · simp [Units.smul_def]
      field_simp
      linear_combination hcross

theorem conicFwd_surjective : Function.Surjective (conicFwd K) := by
  rintro ⟨Q, hQ⟩
  have hq : aeval Q.rep (X 0 * X 2 - X 1 ^ 2 : MvPolynomial (Fin 3) K) = 0 := hQ
  rw [aeval_conicPoly] at hq
  by_cases h0 : Q.rep 0 = 0
  · have h1 : Q.rep 1 = 0 := by
      have : Q.rep 1 ^ 2 = 0 := by rw [h0] at hq; linear_combination -hq
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have h2 : Q.rep 2 ≠ 0 := by
      intro h2
      apply Q.rep_nonzero
      funext i
      fin_cases i <;> simp [h0, h1, h2]
    have hne : (![0, 1] : Fin 2 → K) ≠ 0 := by
      intro h
      have := congrFun h 1
      simp at this
    refine ⟨Projectivization.mk K ![0, 1] hne, Subtype.ext ?_⟩
    rw [conicFwd_mk]
    refine Eq.trans ?_ (Projectivization.mk_rep Q)
    rw [Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 (Q.rep 2)⁻¹ (inv_ne_zero h2), ?_⟩
    funext i
    fin_cases i
    · simp [conicVec, h0]
    · simp [conicVec, h1]
    · simp [conicVec, Units.smul_def, h2]
  · have hne : (![Q.rep 0, Q.rep 1] : Fin 2 → K) ≠ 0 := by
      intro h
      have := congrFun h 0
      simp at this
      exact h0 this
    refine ⟨Projectivization.mk K ![Q.rep 0, Q.rep 1] hne, Subtype.ext ?_⟩
    rw [conicFwd_mk]
    refine Eq.trans ?_ (Projectivization.mk_rep Q)
    rw [Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 (Q.rep 0) h0, ?_⟩
    funext i
    fin_cases i
    · simp [conicVec, Units.smul_def, sq]
    · simp [conicVec, Units.smul_def]
    · simp [conicVec, Units.smul_def]
      linear_combination hq

end Conic

/-- The change of variables $(X, Y, Z) \mapsto (X + iY, Z, X - iY)$ as a linear map. -/
def circleT : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v := ![v 0 + Complex.I * v 1, v 2, v 0 - Complex.I * v 1]
  map_add' v w := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> simp <;> ring

/-- The inverse change of variables. -/
def circleTinv : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun w := ![(w 0 + w 2) / 2, (w 0 - w 2) / (2 * Complex.I), w 1]
  map_add' v w := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> simp <;> ring

theorem circleTinv_circleT (v : Fin 3 → ℂ) : circleTinv (circleT v) = v := by
  funext i
  fin_cases i
  · simp [circleT, circleTinv]
  · simp [circleT, circleTinv]
    field_simp
    ring
  · simp [circleT, circleTinv]

theorem circleT_circleTinv (w : Fin 3 → ℂ) : circleT (circleTinv w) = w := by
  funext i
  fin_cases i
  · simp [circleT, circleTinv]
    field_simp
    ring
  · simp [circleT, circleTinv]
  · simp [circleT, circleTinv]
    field_simp
    ring

theorem circleT_injective : Function.Injective circleT := fun v w h => by
  have := congrArg circleTinv h
  rwa [circleTinv_circleT, circleTinv_circleT] at this

theorem circleTinv_injective : Function.Injective circleTinv := fun v w h => by
  have := congrArg circleT h
  rwa [circleT_circleTinv, circleT_circleTinv] at this

/-- The bijection of the projective plane induced by the change of variables. -/
def circleEquiv : ℙ ℂ (Fin 3 → ℂ) ≃ ℙ ℂ (Fin 3 → ℂ) where
  toFun := Projectivization.map circleT circleT_injective
  invFun := Projectivization.map circleTinv circleTinv_injective
  left_inv P := by
    induction P using Projectivization.ind with | h v hv =>
    simp only [Projectivization.map_mk]
    rw [Projectivization.mk_eq_mk_iff]
    exact ⟨1, by simp [circleTinv_circleT]⟩
  right_inv P := by
    induction P using Projectivization.ind with | h v hv =>
    simp only [Projectivization.map_mk]
    rw [Projectivization.mk_eq_mk_iff]
    exact ⟨1, by simp [circleT_circleTinv]⟩

theorem circle_isHomogeneous : (X 0 ^ 2 + X 1 ^ 2 - X 2 ^ 2 : MvPolynomial (Fin 3) ℂ).IsHomogeneous 2 :=
  (((isHomogeneous_X_pow (R := ℂ) 0 2).add (isHomogeneous_X_pow (R := ℂ) 1 2)).sub
    (isHomogeneous_X_pow (R := ℂ) 2 2))

theorem circleEquiv_mem (P : ℙ ℂ (Fin 3 → ℂ)) :
    P ∈ projectivePoints (X 0 ^ 2 + X 1 ^ 2 - X 2 ^ 2 : MvPolynomial (Fin 3) ℂ) ℂ ↔
      circleEquiv P ∈ projectivePoints (X 0 * X 2 - X 1 ^ 2 : MvPolynomial (Fin 3) ℂ) ℂ := by
  induction P using Projectivization.ind with | h v hv =>
  have hT0 : circleT v ≠ 0 := fun h => hv (circleT_injective (h.trans (map_zero circleT).symm))
  have hm : circleEquiv (Projectivization.mk ℂ v hv) = Projectivization.mk ℂ (circleT v) hT0 := rfl
  rw [hm, mem_projectivePoints_mk circle_isHomogeneous,
    mem_projectivePoints_mk (conicPoly_isHomogeneous ℂ)]
  rw [aeval_conicPoly]
  simp only [map_sub, map_add, map_pow, aeval_X]
  have : (circleT v) 0 * (circleT v) 2 - (circleT v) 1 ^ 2 = v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2 := by
    simp [circleT]
    linear_combination (-(v 1) ^ 2) * Complex.I_sq
  rw [this]

/-- **Example 4.17** (p. 48): the conic $XZ = Y^2$ is isomorphic to $\mathbb P^1$: the map
$(a : b) \mapsto (a^2 : ab : b^2)$ is a bijection $\mathbb P^1(K) \to C(K)$ for every field `K`, with inverse
$(a : b : c) \mapsto (a : b)$ if $a \neq 0$, $(b : c)$ if $b \neq 0$ (both given by polynomials). -/
@[kb "milne2006ec" "Ch. I, Ex. 4.17, pdf p. 48"]
theorem example_4_17 (K : Type*) [Field K] :
    ∃ e : ℙ K (Fin 2 → K) ≃ projectivePoints (X 0 * X 2 - X 1 ^ 2 : MvPolynomial (Fin 3) K) K,
      ∀ (a b : K) (h : ![a, b] ≠ 0) (h' : ![a ^ 2, a * b, b ^ 2] ≠ 0),
        (e (Projectivization.mk K ![a, b] h)).1 = Projectivization.mk K ![a ^ 2, a * b, b ^ 2] h' := by
  have hb : Function.Bijective (conicFwd K) := ⟨conicFwd_injective K, conicFwd_surjective K⟩
  refine ⟨Equiv.ofBijective (conicFwd K) hb, ?_⟩
  intro a b h h'
  show (conicFwd K _).1 = _
  rw [conicFwd_mk]
  rfl

/-- **Example 4.17** (p. 48): over $\mathbb C$, the circle $X^2 + Y^2 = Z^2$ becomes $XZ = Y^2$ after the
change of variables $(X, Y, Z) \mapsto (X + iY, Z, X - iY)$; so its points are in bijection with
$\mathbb P^1(\mathbb C)$. -/
@[kb "milne2006ec" "Ch. I, Ex. 4.17, pdf p. 48"]
theorem example_4_17_circle :
    Nonempty (ℙ ℂ (Fin 2 → ℂ) ≃ projectivePoints (X 0 ^ 2 + X 1 ^ 2 - X 2 ^ 2 : MvPolynomial (Fin 3) ℂ) ℂ) := by
  obtain ⟨e, _⟩ := example_4_17 ℂ
  exact ⟨e.trans (Equiv.subtypeEquiv circleEquiv circleEquiv_mem).symm⟩

/-- The affine coordinates of the piece $U_2$, as a point of the affine curve `dehomogenize 2 F`. -/
theorem pieceCoords_mem {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d)
    {K : Type*} [Field K] [Algebra k K] (P : projectivePoints F K) (hP : P.1.rep 2 ≠ 0) :
    pieceCoords 2 P.1.rep ∈ affinePoints (dehomogenize 2 F) K :=
  (aeval_eq_zero_iff_mem_piece hF 2 P.1.rep hP).mp P.2

/-- A regular map of projective curves **extends** the regular map `f` of the affine pieces $C \cap U_2$,
$C' \cap U_2$: on points of $U_2$ it is `f` in affine coordinates. -/
def ProjRegularMap.Extends {F F' : MvPolynomial (Fin 3) k} (φ : ProjRegularMap F F')
    (f : Fin 2 → coordinateRing (dehomogenize 2 F)) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] (P : projectivePoints F K) (hP : P.1.rep 2 ≠ 0)
    (hP' : pieceCoords 2 P.1.rep ∈ affinePoints (dehomogenize 2 F) K),
    (φ.toFun K P).1.rep 2 ≠ 0 ∧
      pieceCoords 2 (φ.toFun K P).1.rep = (evalCoord hP' (f 0), evalCoord hP' (f 1))

/-- **Proposition 4.18** (p. 48), as a named statement (Milne: via function fields, Fulton 1969, Chap. 7,
p. 180), for the affine pieces $C_L$ with $L = Z$: a regular map $C \cap U_2 \to C' \cap U_2$ of the affine
pieces of nonsingular projective plane curves extends uniquely to a regular map $C \to C'$.  (Milne allows
any nonzero linear forms `L`, `L'`; a linear change of coordinates reduces to $L = L' = Z$, which is the case
stated.)

**False as stated** (`not_prop4_18`, file `Ch1MapsCounterexample`): uniqueness is asked on the points over every
field `K`, and a `ProjRegularMap` imposes no compatibility between fields; over $\mathbb F_3$ a curve with no affine
$\mathbb F_3$-point gives two extensions. The corrected statement is `Prop4_18Corrected` (uniqueness over
algebraically closed fields). -/
@[kb "milne2006ec" "Ch. I, Prop. 4.18, pdf p. 48"]
structure Prop4_18 : Prop where
  extends_unique : ∀ (k : Type) [Field k] [PerfectField k] (F F' : MvPolynomial (Fin 3) k),
    IsProjectivePlaneCurve F → IsNonsingularProjCurve F → IsProjectivePlaneCurve F' →
    IsNonsingularProjCurve F' → ¬ F ∣ X 2 → ¬ F' ∣ X 2 →
    ∀ f, IsAffineRegularMap (dehomogenize 2 F) (dehomogenize 2 F') f →
      ∃ φ : ProjRegularMap F F', φ.Extends f ∧
        ∀ ψ : ProjRegularMap F F', ψ.Extends f → ∀ (K : Type) [Field K] [Algebra k K], ψ.toFun K = φ.toFun K

/-- **Remark 4.19** (p. 48), as a named statement: Proposition 4.18 holds also for singular absolutely
irreducible projective plane curves whose singular points (over $k^{\mathrm{al}}$) lie in the affine pieces.
(The extension to arbitrary nonsingular projective curves, not necessarily plane, is not formalized.) -/
@[kb "milne2006ec" "Ch. I, Rem. 4.19, pdf p. 48"]
structure Remark4_19 : Prop where
  extends_unique : ∀ (k : Type) [Field k] [PerfectField k] (F F' : MvPolynomial (Fin 3) k),
    IsProjectivePlaneCurve F → Irreducible (baseChange (AlgebraicClosure k) F) →
    IsProjectivePlaneCurve F' → Irreducible (baseChange (AlgebraicClosure k) F') →
    (∀ P ∈ projectivePoints F (AlgebraicClosure k), ¬ IsNonsingularProjPoint F P → P.rep 2 ≠ 0) →
    (∀ P ∈ projectivePoints F' (AlgebraicClosure k), ¬ IsNonsingularProjPoint F' P → P.rep 2 ≠ 0) →
    ¬ F ∣ X 2 → ¬ F' ∣ X 2 →
    ∀ f, IsAffineRegularMap (dehomogenize 2 F) (dehomogenize 2 F') f →
      ∃ φ : ProjRegularMap F F', φ.Extends f ∧
        ∀ ψ : ProjRegularMap F F', ψ.Extends f → ∀ (K : Type) [Field K] [Algebra k K], ψ.toFun K = φ.toFun K

/-- A prime factor of a coordinate variable vanishes wherever that coordinate does. -/
theorem aeval_eq_zero_of_irreducible_dvd_X {σ : Type*} {i : MvPolynomial σ k} (hi : Irreducible i)
    (j : σ) (hd : i ∣ X j) (v : σ → k) (hv : v j = 0) : aeval v i = 0 := by
  obtain ⟨u, hu⟩ := hd
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hdeg := totalDegree_mul_of_isDomain hi.ne_zero hu0
  rw [← hu, totalDegree_X] at hdeg
  have hi1 := totalDegree_ne_zero_of_not_isUnit hi.ne_zero hi.not_isUnit
  have hu1 : u.totalDegree = 0 := by omega
  rw [totalDegree_eq_zero_iff_eq_C] at hu1
  have hc : u.coeff 0 ≠ 0 := by
    intro h
    apply hu0
    rw [hu1, h, C_0]
  have := congrArg (aeval v) hu
  rw [hu1] at this
  simp only [map_mul, aeval_X, hv, aeval_C] at this
  have h2 : aeval v i * algebraMap k k (u.coeff 0) = 0 := this.symm
  rw [Algebra.algebraMap_self_apply] at h2
  exact (mul_eq_zero.mp h2).resolve_right hc

/-- The Weierstrass cubic has no repeated factor in characteristic not 2: a repeated prime factor
would divide $\partial F/\partial Y = 2YZ$, hence be a multiple of `Y` or `Z`, but $F(1, 0, 0) = -1$. -/
theorem squarefree_weierstrassCubic (h2 : (2 : k) ≠ 0) (a b : k) :
    Squarefree (weierstrassCubic a b) := by
  intro y hy
  by_contra hyu
  have hF0 : weierstrassCubic a b ≠ 0 := by
    intro h
    have := congrArg (aeval (![1, 0, 0] : Fin 3 → k)) h
    simp [weierstrassCubic] at this
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [mul_zero, zero_dvd_iff] at hy
    exact hF0 hy
  obtain ⟨i, hi, hiy⟩ := WfDvdMonoid.exists_irreducible_factor hyu hy0
  have hii : i * i ∣ weierstrassCubic a b := (mul_dvd_mul hiy hiy).trans hy
  obtain ⟨q, hq⟩ := hii
  have hd : i ∣ pderiv 1 (weierstrassCubic a b) :=
    ⟨pderiv 1 i * q + pderiv 1 i * q + i * pderiv 1 q, by
      rw [hq]; simp only [pderiv_mul]; ring⟩
  have hF' : pderiv 1 (weierstrassCubic a b) = C 2 * (X 1 * X 2) := by
    simp [weierstrassCubic, pderiv_X]
    rw [show (C 2 : MvPolynomial (Fin 3) k) = 2 from map_ofNat C 2]
    ring
  rw [hF'] at hd
  have hunit : IsUnit (C 2 : MvPolynomial (Fin 3) k) := (IsUnit.mk0 2 h2).map C
  have hd' : i ∣ X 1 * X 2 := (hunit.dvd_mul_left).mp hd
  have hv : aeval (![1, 0, 0] : Fin 3 → k) i = 0 := by
    rcases hi.prime.dvd_or_dvd hd' with h | h
    · exact aeval_eq_zero_of_irreducible_dvd_X hi 1 h _ (by simp)
    · exact aeval_eq_zero_of_irreducible_dvd_X hi 2 h _ (by simp)
  have := congrArg (aeval (![1, 0, 0] : Fin 3 → k)) hq
  simp only [map_mul, hv, zero_mul] at this
  simp [weierstrassCubic] at this

theorem weierstrassCubic_ne_zero (a b : k) : weierstrassCubic a b ≠ 0 := by
  intro h
  have := congrArg (aeval (![1, 0, 0] : Fin 3 → k)) h
  simp [weierstrassCubic] at this

theorem weierstrassCubic_totalDegree (a b : k) : (weierstrassCubic a b).totalDegree = 3 :=
  (weierstrassCubic_isHomogeneous a b).totalDegree (weierstrassCubic_ne_zero a b)

/-- The Weierstrass cubic is a projective plane curve when the characteristic is not 2. -/
theorem isProjectivePlaneCurve_weierstrass (hk : ringChar k ≠ 2) (a b : k) :
    IsProjectivePlaneCurve (weierstrassCubic a b) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [weierstrassCubic_totalDegree]; exact weierstrassCubic_isHomogeneous a b
  · rw [weierstrassCubic_totalDegree]; norm_num
  · have h2 : (2 : AlgebraicClosure k) ≠ 0 := by
      have := Ring.two_ne_zero hk
      intro h
      apply this
      apply (algebraMap k (AlgebraicClosure k)).injective
      rw [map_ofNat, map_zero]
      exact h
    have : baseChange (AlgebraicClosure k) (weierstrassCubic a b) =
        weierstrassCubic (algebraMap k (AlgebraicClosure k) a) (algebraMap k (AlgebraicClosure k) b) := by
      simp [weierstrassCubic]
    rw [this]
    exact squarefree_weierstrassCubic h2 _ _

/-- The Weierstrass cubic is nonsingular when the characteristic is not 2 and $4a^3 + 27b^2 \neq 0$:
the affine piece is Example 1.5 and the point at infinity is checked with $\partial F/\partial Z$. -/
theorem isNonsingularProjCurve_weierstrass (hk : ringChar k ≠ 2) {a b : k}
    (hab : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) : IsNonsingularProjCurve (weierstrassCubic a b) := by
  intro P hP
  by_cases h2 : P.rep 2 = 0
  · have hinf := (example_1_15 a b _ P).mp ⟨hP, h2⟩
    rw [isNonsingularProjPoint_iff (weierstrassCubic_isHomogeneous a b) P hP]
    subst hinf
    obtain ⟨h0, h2', h1⟩ := pointAtInfinity_rep (AlgebraicClosure k)
    intro hall
    have := hall 2
    simp [weierstrassCubic, h0, h2'] at this
    exact h1 this
  · have hns := (example_1_5 hk a b).2.mpr hab
    have hmem := (aeval_eq_zero_iff_mem_piece (weierstrassCubic_isHomogeneous a b) 2 P.rep h2).mp hP
    have hpi : pieceIndex P.rep = 2 := by simp [pieceIndex, h2]
    have e : dehomogenize 2 (weierstrassCubic a b) = shortWeierstrass a b :=
      (example_1_16.{_, 0} a b).1
    unfold IsNonsingularProjPoint
    rw [hpi, e]
    rw [e] at hmem
    exact hns _ hmem

theorem weierstrassCubic_not_dvd_X (a b : k) : ¬ weierstrassCubic a b ∣ X 2 := by
  rintro ⟨q, hq⟩
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have := totalDegree_mul_of_isDomain (weierstrassCubic_ne_zero a b) hq0
  rw [← hq, totalDegree_X, weierstrassCubic_totalDegree] at this
  omega

/-- **Example 4.20** (p. 49), first part: every regular map $E(a, b)^{\mathrm{aff}} \to E(a', b')^{\mathrm{aff}}$ of
affine Weierstrass curves extends uniquely to $E(a, b) \to E(a', b')$ (from the named statement `Prop4_18`;
the curves are assumed nonsingular: characteristic not 2 and $4a^3 + 27b^2 \neq 0$). -/
@[kb "milne2006ec" "Ch. I, Ex. 4.20, pdf p. 49"]
theorem example_4_20 (h : Prop4_18) {k : Type} [Field k] [PerfectField k] (hk : ringChar k ≠ 2)
    {a b a' b' : k} (hab : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (hab' : 4 * a' ^ 3 + 27 * b' ^ 2 ≠ 0)
    (f : Fin 2 → coordinateRing (dehomogenize 2 (weierstrassCubic a b)))
    (hf : IsAffineRegularMap (dehomogenize 2 (weierstrassCubic a b))
      (dehomogenize 2 (weierstrassCubic a' b')) f) :
    ∃ φ : ProjRegularMap (weierstrassCubic a b) (weierstrassCubic a' b'), φ.Extends f ∧
      ∀ ψ : ProjRegularMap (weierstrassCubic a b) (weierstrassCubic a' b'), ψ.Extends f →
        ∀ (K : Type) [Field K] [Algebra k K], ψ.toFun K = φ.toFun K :=
  h.extends_unique k _ _ (isProjectivePlaneCurve_weierstrass hk a b)
    (isNonsingularProjCurve_weierstrass hk hab) (isProjectivePlaneCurve_weierstrass hk a' b')
    (isNonsingularProjCurve_weierstrass hk hab') (weierstrassCubic_not_dvd_X a b)
    (weierstrassCubic_not_dvd_X a' b') f hf

/-- **Example 4.20** (p. 49), second part, as a named statement: if the affine map sends vertical lines to
vertical lines ($x \circ \varphi$ is a polynomial in `x` alone, not constant), its extension sends the point at
infinity $(0 : 1 : 0)$ to the point at infinity. -/
@[kb "milne2006ec" "Ch. I, Ex. 4.20, point at infinity, pdf p. 49"]
structure Example4_20 : Prop where
  infinity : ∀ (k : Type) [Field k] [PerfectField k] (a b a' b' : k)
    (φ : ProjRegularMap (weierstrassCubic a b) (weierstrassCubic a' b'))
    (f : Fin 2 → coordinateRing (dehomogenize 2 (weierstrassCubic a b))), φ.Extends f →
    (∃ r : Polynomial k, 0 < r.natDegree ∧
      f 0 = Ideal.Quotient.mk _ (Polynomial.aeval (X 0) r)) →
    ∀ (K : Type) [Field K] [Algebra k K] (hP : pointAtInfinity K ∈ projectivePoints (weierstrassCubic a b) K),
      (φ.toFun K ⟨pointAtInfinity K, hP⟩).1 = pointAtInfinity K

/-! ### Constant, dominating and surjective maps; degree -/

/-- **Definition 4.21** (p. 49) (a): `φ` is **constant** if for every field `K ⊇ k` the image of `φ(K)` is
a single point (when $C(K)$ is nonempty). -/
@[kb "milne2006ec" "Ch. I, Def. 4.21 (a), pdf p. 49"]
def ProjRegularMap.IsConstant {F F' : MvPolynomial (Fin 3) k} (φ : ProjRegularMap F F') : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K], (Set.range (φ.toFun K)).Subsingleton

/-- **Definition 4.21** (p. 49) (b): `φ` is **dominating** if the image of $\varphi(k^{\mathrm{al}})$ omits only
finitely many points of $C'(k^{\mathrm{al}})$. -/
@[kb "milne2006ec" "Ch. I, Def. 4.21 (b), pdf p. 49"]
def ProjRegularMap.IsDominating {F F' : MvPolynomial (Fin 3) k} (φ : ProjRegularMap F F') : Prop :=
  (Set.range (φ.toFun (AlgebraicClosure k)))ᶜ.Finite

/-- **Definition 4.21** (p. 49) (c): `φ` is **surjective** if $\varphi(k^{\mathrm{al}})$ is surjective. -/
@[kb "milne2006ec" "Ch. I, Def. 4.21 (c), pdf p. 49"]
def ProjRegularMap.IsSurjective {F F' : MvPolynomial (Fin 3) k} (φ : ProjRegularMap F F') : Prop :=
  Function.Surjective (φ.toFun (AlgebraicClosure k))

/-- **Proposition 4.23** (p. 49), as a named statement (Fulton 1969, Problem 8-18 for (b)): (a) a regular
map of geometrically irreducible curves is dominating or constant; (b) a dominating regular map of
projective curves is surjective. -/
@[kb "milne2006ec" "Ch. I, Prop. 4.23, pdf p. 49"]
structure Prop4_23 : Prop where
  dominating_or_constant : ∀ (k : Type) [Field k] [PerfectField k] (F F' : MvPolynomial (Fin 3) k),
    IsProjectivePlaneCurve F → Irreducible (baseChange (AlgebraicClosure k) F) →
    IsProjectivePlaneCurve F' → Irreducible (baseChange (AlgebraicClosure k) F') →
    ∀ φ : ProjRegularMap F F', φ.IsDominating ∨ φ.IsConstant
  surjective : ∀ (k : Type) [Field k] [PerfectField k] (F F' : MvPolynomial (Fin 3) k),
    IsProjectivePlaneCurve F → Irreducible (baseChange (AlgebraicClosure k) F) →
    IsProjectivePlaneCurve F' → Irreducible (baseChange (AlgebraicClosure k) F') →
    ∀ φ : ProjRegularMap F F', φ.IsDominating → φ.IsSurjective

/-- A rational function `h ∈ k(C)` is defined at `P ∈ C(K)` with value `v` (p. 39): $h = G/H$ with `G`, `H`
homogeneous of one degree, $H(P) \neq 0$, and $v = G(P)/H(P)$. -/
def HasValueAt (F : MvPolynomial (Fin 3) k) [Fact (Prime F)] (h : projFunctionField F) {K : Type*}
    [Field K] [Algebra k K] (P : ℙ K (Fin 3 → K)) (v : K) : Prop :=
  ∃ (d : ℕ) (G H : MvPolynomial (Fin 3) k), G.IsHomogeneous d ∧ H.IsHomogeneous d ∧
    aeval P.rep H ≠ 0 ∧ (h : FractionRing (homogCoordRing F)) = homogFrac F G / homogFrac F H ∧
    v = aeval P.rep G / aeval P.rep H

/-- `ι : k(C') → k(C)` is the **pullback** of functions along `φ` (p. 49): $\iota(h)(P) = h(\varphi(P))$
wherever the right side is defined. -/
def ProjRegularMap.IsPullback {F F' : MvPolynomial (Fin 3) k} [Fact (Prime F)] [Fact (Prime F')]
    (φ : ProjRegularMap F F') (ι : projFunctionField F' →ₐ[k] projFunctionField F) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] (P : projectivePoints F K) (h : projFunctionField F') (v : K),
    HasValueAt F' h (φ.toFun K P).1 v → HasValueAt F (ι h) P.1 v

/-- The **degree** of a dominating map with pullback `ι` (p. 49): $[k(C) : \iota(k(C'))]$. -/
@[kb "milne2006ec" "Ch. I, §4, Def. of the degree of a dominating map, pdf p. 49"]
def pullbackDegree {F F' : MvPolynomial (Fin 3) k} [Fact (Prime F)] [Fact (Prime F')]
    (ι : projFunctionField F' →ₐ[k] projFunctionField F) : ℕ :=
  letI := ι.toRingHom.toAlgebra
  Module.finrank (projFunctionField F') (projFunctionField F)

/-- **Proposition 4.24** (p. 49), as a named statement (Fulton 1969, Problem 8.36 and Chap. 7, Thm. 3):
let $\varphi : C \to C'$ be dominating with pullback `ι` and degree `n`.  (a) If $k(C)/\iota k(C')$ is separable,
then $\varphi(k^{\mathrm{al}})$ is `n`-to-1 outside a finite set; (b) if `n = 1` and `C`, `C'` are nonsingular
projective curves, `φ` is an isomorphism. -/
@[kb "milne2006ec" "Ch. I, Prop. 4.24, pdf p. 49"]
structure Prop4_24 : Prop where
  card_fiber : ∀ (k : Type) [Field k] [PerfectField k] (F F' : MvPolynomial (Fin 3) k)
    [Fact (Prime F)] [Fact (Prime F')], IsProjectivePlaneCurve F → Irreducible (baseChange (AlgebraicClosure k) F) →
    IsProjectivePlaneCurve F' → Irreducible (baseChange (AlgebraicClosure k) F') →
    ∀ (φ : ProjRegularMap F F') (ι : projFunctionField F' →ₐ[k] projFunctionField F),
      φ.IsDominating → φ.IsPullback ι →
      (letI := ι.toRingHom.toAlgebra; Algebra.IsSeparable (projFunctionField F') (projFunctionField F)) →
      ∃ S : Set (projectivePoints F' (AlgebraicClosure k)), S.Finite ∧
        ∀ Q ∉ S, Nat.card (φ.toFun _ ⁻¹' {Q}) = pullbackDegree ι
  iso_of_degree_one : ∀ (k : Type) [Field k] [PerfectField k] (F F' : MvPolynomial (Fin 3) k)
    [Fact (Prime F)] [Fact (Prime F')], IsProjectivePlaneCurve F → Irreducible (baseChange (AlgebraicClosure k) F) →
    IsNonsingularProjCurve F → IsProjectivePlaneCurve F' →
    Irreducible (baseChange (AlgebraicClosure k) F') → IsNonsingularProjCurve F' →
    ∀ (φ : ProjRegularMap F F') (ι : projFunctionField F' →ₐ[k] projFunctionField F),
      φ.IsDominating → φ.IsPullback ι → pullbackDegree ι = 1 → IsProjIso φ

/-- The coordinate function `x` in the function field of $Y^2 = X^3 + aX + b$. -/
abbrev coordFunX (a b : k) [Fact (Prime (shortWeierstrass a b))] : functionField (shortWeierstrass a b) :=
  algebraMap (coordinateRing (shortWeierstrass a b)) _
    (Ideal.Quotient.mk (Ideal.span {shortWeierstrass a b}) (X 0))

/-- The coordinate function `y` in the function field of $Y^2 = X^3 + aX + b$. -/
abbrev coordFunY (a b : k) [Fact (Prime (shortWeierstrass a b))] : functionField (shortWeierstrass a b) :=
  algebraMap (coordinateRing (shortWeierstrass a b)) _
    (Ideal.Quotient.mk (Ideal.span {shortWeierstrass a b}) (X 1))

/-- The coordinate `x` is transcendental over `k`: the polynomial ring `k[X]` embeds into the coordinate
ring of $Y^2 = X^3 + aX + b$ (via the map to the ring obtained by adjoining a square root of the cubic
to `k[X]`). -/
theorem aeval_coordX_injective (a b : k) :
    Function.Injective (Polynomial.aeval (Ideal.Quotient.mk (Ideal.span {shortWeierstrass a b})
      (X 0 : MvPolynomial (Fin 2) k)) : Polynomial k →ₐ[k] coordinateRing (shortWeierstrass a b)) := by
  set g : Polynomial (Polynomial k) := Polynomial.X ^ 2 - Polynomial.C (shortCubic a b) with hg
  let Ψ : MvPolynomial (Fin 2) k →ₐ[k] AdjoinRoot g :=
    aeval ![AdjoinRoot.of g Polynomial.X, AdjoinRoot.root g]
  have hr : (AdjoinRoot.root g) ^ 2 = AdjoinRoot.of g (shortCubic a b) := by
    have := AdjoinRoot.eval₂_root g
    simp only [hg, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at this
    linear_combination this
  have hΨ : Ψ (shortWeierstrass a b) = 0 := by
    have h1 : ∀ c : k, algebraMap k (AdjoinRoot g) c = AdjoinRoot.of g (Polynomial.C c) := by
      intro c
      rw [IsScalarTower.algebraMap_apply k (Polynomial k) (AdjoinRoot g)]
      rfl
    simp only [Ψ, shortWeierstrass, map_sub, map_pow, map_add, map_mul, aeval_X, aeval_C, h1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hr, shortCubic]
    simp only [map_add, map_mul, map_pow]
    ring
  let Ψ' : coordinateRing (shortWeierstrass a b) →ₐ[k] AdjoinRoot g :=
    Ideal.Quotient.liftₐ _ Ψ (by
      intro c hc
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      simp [hΨ])
  have hcomp : Ψ'.comp (Polynomial.aeval (Ideal.Quotient.mk (Ideal.span {shortWeierstrass a b})
      (X 0 : MvPolynomial (Fin 2) k))) = IsScalarTower.toAlgHom k (Polynomial k) (AdjoinRoot g) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X]
    show (aeval ![AdjoinRoot.of g Polynomial.X, AdjoinRoot.root g] (X 0) : AdjoinRoot g) = _
    simp
  have hinj : Function.Injective (IsScalarTower.toAlgHom k (Polynomial k) (AdjoinRoot g)) := by
    have : Function.Injective (AdjoinRoot.of g) := by
      apply AdjoinRoot.of.injective_of_degree_ne_zero
      rw [hg, Polynomial.degree_X_pow_sub_C (by norm_num)]
      norm_num
    exact this
  intro p q hpq
  apply hinj
  rw [← hcomp]
  simp only [AlgHom.comp_apply, hpq]

theorem aeval_coordFunX_injective (a b : k) [Fact (Prime (shortWeierstrass a b))] :
    Function.Injective (Polynomial.aeval (coordFunX a b) : Polynomial k →ₐ[k]
      functionField (shortWeierstrass a b)) := by
  intro p q hpq
  apply aeval_coordX_injective a b
  apply IsFractionRing.injective (coordinateRing (shortWeierstrass a b))
    (functionField (shortWeierstrass a b))
  simpa [Polynomial.aeval_algebraMap_apply] using hpq

set_option synthInstance.maxHeartbeats 200000 in
theorem coordFunY_sq (a b : k) [Fact (Prime (shortWeierstrass a b))] :
    coordFunY a b ^ 2 = Polynomial.aeval (coordFunX a b) (shortCubic a b) := by
  have h0 : Ideal.Quotient.mk (Ideal.span {shortWeierstrass a b}) (shortWeierstrass a b) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have h1 : algebraMap (coordinateRing (shortWeierstrass a b))
      (functionField (shortWeierstrass a b)) (Ideal.Quotient.mk (Ideal.span {shortWeierstrass a b})
        (X 1 ^ 2 - (X 0 ^ 3 + C a * X 0 + C b))) = 0 := by
    have h := congrArg (algebraMap (coordinateRing (shortWeierstrass a b))
      (functionField (shortWeierstrass a b))) h0
    rw [map_zero] at h
    exact h
  have hC : ∀ c : k, algebraMap (coordinateRing (shortWeierstrass a b))
      (functionField (shortWeierstrass a b)) (Ideal.Quotient.mk (Ideal.span {shortWeierstrass a b})
        (C c)) = algebraMap k _ c := fun c =>
    (IsScalarTower.algebraMap_apply k (coordinateRing (shortWeierstrass a b))
      (functionField (shortWeierstrass a b)) c).symm
  simp only [map_sub, map_pow, map_add, map_mul, hC] at h1
  simp only [shortCubic, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
  linear_combination h1

set_option synthInstance.maxHeartbeats 200000 in
/-- The function field of $Y^2 = X^3 + aX + b$ has degree 2 over `k(x)` (proof of `example_4_25`): it is
generated over `k(x)` by `y`, and `y` is not in `k(x)` because `x` is transcendental and the cubic has odd
degree. -/
theorem example_4_25_aux (a b : k) [Fact (Prime (shortWeierstrass a b))] :
    Module.finrank (IntermediateField.adjoin k (Set.singleton (coordFunX a b)))
      (functionField (shortWeierstrass a b)) = 2 := by
  set L := functionField (shortWeierstrass a b)
  set A := coordinateRing (shortWeierstrass a b)
  set E := IntermediateField.adjoin k (Set.singleton (coordFunX a b)) with hE
  have hxE : coordFunX a b ∈ E := IntermediateField.subset_adjoin k _ rfl
  have hcubic : (shortCubic a b).natDegree = 3 := by
    unfold shortCubic; compute_degree!
  have hy2 := coordFunY_sq a b
  have hy_ne : coordFunY a b ≠ 0 := by
    intro h
    rw [h] at hy2
    have : Polynomial.aeval (coordFunX a b) (shortCubic a b) = 0 := by rw [← hy2]; ring
    have := aeval_coordFunX_injective a b (this.trans (map_zero _).symm)
    rw [this] at hcubic
    simp at hcubic
  set xE : E := ⟨coordFunX a b, hxE⟩ with hxE_def
  set c : E := Polynomial.aeval xE (shortCubic a b) with hc_def
  have hc : algebraMap E L c = Polynomial.aeval (coordFunX a b) (shortCubic a b) := by
    rw [hc_def, ← Polynomial.aeval_algebraMap_apply]
    rfl
  set p : Polynomial E := Polynomial.X ^ 2 - Polynomial.C c with hp_def
  have hmonic : p.Monic := Polynomial.monic_X_pow_sub_C c (by norm_num)
  have hp : Polynomial.aeval (coordFunY a b) p = 0 := by
    simp only [hp_def, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hy2]
    linear_combination (-1 : L) * hc
  have hint : IsIntegral E (coordFunY a b) := ⟨p, hmonic, by rw [← Polynomial.aeval_def]; exact hp⟩
  have hnotin : coordFunY a b ∉ (algebraMap E L).range := by
    rintro ⟨e, he⟩
    have he' : (e : L) ∈ IntermediateField.adjoin k {coordFunX a b} := e.2
    obtain ⟨r, s, hrs⟩ :=
      (IntermediateField.mem_adjoin_simple_iff (F := k) (α := coordFunX a b) (e : L)).mp he'
    have hye : (e : L) = coordFunY a b := he
    rw [hye] at hrs
    have hs : Polynomial.aeval (coordFunX a b) s ≠ 0 := by
      intro h0
      rw [h0, div_zero] at hrs
      exact hy_ne hrs
    have hrs' : Polynomial.aeval (coordFunX a b) r =
        coordFunY a b * Polynomial.aeval (coordFunX a b) s := by
      rw [hrs]; field_simp
    have hpoly : Polynomial.aeval (coordFunX a b) (shortCubic a b * s ^ 2) =
        Polynomial.aeval (coordFunX a b) (r ^ 2) := by
      simp only [map_mul, map_pow, hrs', mul_pow, hy2]
    have hpoly' := aeval_coordFunX_injective a b hpoly
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs
    have hc0 : shortCubic a b ≠ 0 := by intro h; rw [h] at hcubic; simp at hcubic
    have h1 := congrArg Polynomial.natDegree hpoly'
    rw [Polynomial.natDegree_mul hc0 (pow_ne_zero _ hs0), Polynomial.natDegree_pow,
      Polynomial.natDegree_pow, hcubic] at h1
    omega
  have h2 : 2 ≤ (minpoly E (coordFunY a b)).natDegree :=
    (minpoly.two_le_natDegree_iff hint).mpr hnotin
  have h2' : (minpoly E (coordFunY a b)).natDegree ≤ 2 := by
    have hp0 : p ≠ 0 := hmonic.ne_zero
    have := minpoly.degree_le_of_ne_zero E (coordFunY a b) hp0 hp
    have hdeg : p.degree = 2 := Polynomial.degree_X_pow_sub_C (by norm_num) c
    rw [hdeg] at this
    exact Polynomial.natDegree_le_of_degree_le this
  have htop : IntermediateField.adjoin E {coordFunY a b} = ⊤ := by
    set S := IntermediateField.adjoin E {coordFunY a b} with hS
    have hxS : coordFunX a b ∈ S.restrictScalars k := S.algebraMap_mem xE
    have hyS : coordFunY a b ∈ S.restrictScalars k := IntermediateField.subset_adjoin E _ rfl
    have hmem : ∀ q : MvPolynomial (Fin 2) k,
        algebraMap A L (Ideal.Quotient.mk (Ideal.span {shortWeierstrass a b}) q) ∈
          S.restrictScalars k := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C c =>
        have : algebraMap A L (Ideal.Quotient.mk (Ideal.span {shortWeierstrass a b}) (C c)) =
            algebraMap k L c := (IsScalarTower.algebraMap_apply k A L c).symm
        rw [this]
        exact (S.restrictScalars k).algebraMap_mem c
      | add p q hp hq =>
        rw [map_add, map_add]
        exact add_mem hp hq
      | mul_X p i hp =>
        rw [map_mul, map_mul]
        refine mul_mem hp ?_
        fin_cases i
        · exact hxS
        · exact hyS
    refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective v
    exact div_mem (hmem p) (hmem q)
  calc Module.finrank E L = Module.finrank E (⊤ : IntermediateField E L) :=
        (IntermediateField.finrank_top').symm
    _ = Module.finrank E (IntermediateField.adjoin E {coordFunY a b}) := by rw [htop]
    _ = (minpoly E (coordFunY a b)).natDegree := IntermediateField.adjoin.finrank hint
    _ = 2 := le_antisymm h2' h2

/-- Membership of a point in the short Weierstrass curve, in terms of the cubic polynomial. -/
theorem mem_affinePoints_shortWeierstrass_iff (a b : k) {K : Type*} [Field K] [Algebra k K]
    (x y : K) :
    (x, y) ∈ affinePoints (shortWeierstrass a b) K ↔
      y ^ 2 = ((shortCubic a b).map (algebraMap k K)).eval x := by
  simp only [affinePoints, Set.mem_ofPred_eq, evalAt, shortWeierstrass, shortCubic, map_sub, map_pow,
    map_add, map_mul, aeval_X, aeval_C, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
  simp

/-- **Example 4.25** (p. 50): the projection $(x, y) \mapsto x$ of $E : Y^2 = X^3 + aX + b$ has degree 2:
$k(x, y) = k(x)[\sqrt{x^3 + ax + b}]$, i.e. the function field of the affine curve has degree 2 over the
subfield $k(x)$ generated by the coordinate function `x`. -/
@[kb "milne2006ec" "Ch. I, Ex. 4.25, pdf p. 50"]
theorem example_4_25 (a b : k) [Fact (Prime (shortWeierstrass a b))] :
    Module.finrank (IntermediateField.adjoin k (Set.singleton (coordFunX a b)))
      (functionField (shortWeierstrass a b)) = 2 :=
  example_4_25_aux a b

/-- **Example 4.25** (p. 50), on points: if the characteristic is not 2, the projection
$(x, y) \mapsto x$ of $E(k^{\mathrm{al}})$ is 2-to-1 except over the roots of $X^3 + aX + b$; in characteristic
2 it is 1-to-1. -/
@[kb "milne2006ec" "Ch. I, Ex. 4.25, on points, pdf p. 50"]
theorem example_4_25_points (a b : k) :
    (ringChar k ≠ 2 → ∀ x : AlgebraicClosure k,
      ((shortCubic a b).map (algebraMap k (AlgebraicClosure k))).eval x ≠ 0 →
        Nat.card {y : AlgebraicClosure k // (x, y) ∈ affinePoints (shortWeierstrass a b) _} = 2) ∧
    (ringChar k = 2 → ∀ x : AlgebraicClosure k,
        Nat.card {y : AlgebraicClosure k // (x, y) ∈ affinePoints (shortWeierstrass a b) _} = 1) := by
  constructor
  · intro hk x hx
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
      (((shortCubic a b).map (algebraMap k (AlgebraicClosure k))).eval x) (n := 2) (by norm_num)
    have h2 : (2 : AlgebraicClosure k) ≠ 0 := by
      intro h
      apply hk
      have : (2 : k) = 0 := by
        apply (algebraMap k (AlgebraicClosure k)).injective
        rw [map_ofNat, map_zero]
        exact h
      have hd : ringChar k ∣ 2 := (ringChar.spec k 2).mp (by exact_mod_cast this)
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
      · exact absurd h1 CharP.ringChar_ne_one
      · exact h1
    have hs0 : s ≠ 0 := by
      rintro rfl
      apply hx
      rw [← hs]; ring
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨s, ?_⟩, ⟨-s, ?_⟩, ?_, ?_⟩
    · rw [mem_affinePoints_shortWeierstrass_iff, hs]
    · rw [mem_affinePoints_shortWeierstrass_iff, ← hs]; ring
    · intro h
      have := congrArg Subtype.val h
      simp only at this
      apply hs0
      have : (2 : AlgebraicClosure k) * s = 0 := by linear_combination this
      exact (mul_eq_zero.mp this).resolve_left h2
    · ext ⟨y, hy⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true, Subtype.mk.injEq]
      rw [mem_affinePoints_shortWeierstrass_iff, ← hs] at hy
      exact sq_eq_sq_iff_eq_or_eq_neg.mp hy
  · intro hk x
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
      (((shortCubic a b).map (algebraMap k (AlgebraicClosure k))).eval x) (n := 2) (by norm_num)
    have h2 : (2 : AlgebraicClosure k) = 0 := by
      have : (2 : k) = 0 := by
        have := (ringChar.spec k 2).mpr (by rw [hk])
        exact_mod_cast this
      rw [← map_ofNat (algebraMap k (AlgebraicClosure k)) 2, this, map_zero]
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨s, ?_⟩, ?_⟩
    · rw [mem_affinePoints_shortWeierstrass_iff, hs]
    · rintro ⟨y, hy⟩
      rw [mem_affinePoints_shortWeierstrass_iff, ← hs] at hy
      apply Subtype.ext
      simp only
      have : (y - s) ^ 2 = 0 := by linear_combination hy + (s ^ 2 - y * s) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)

/-- **Remark 4.26 (a)** (p. 50), as a named statement: a surjective regular map $\varphi : C \to C'$ of
nonsingular projective curves, with pullback `ι`, multiplies degrees of divisors by $\deg \varphi$: when one
counts multiplicities, every fibre $\varphi^{-1}(Q)$, $Q \in C'(k^{\mathrm{al}})$, has $\deg \varphi$ points.
The multiplicity at `P` is the ramification index $\operatorname{ord}_P(\iota(t_Q))$ of a uniformizer $t_Q$
at `Q` (local rings as in `IsLocalRingAt`). -/
@[kb "milne2006ec" "Ch. I, Rem. 4.26 (a), pdf p. 50"]
structure Remark4_26 : Prop where
  sum_ramification : ∀ (k : Type) [Field k] [IsAlgClosed k] (F F' : MvPolynomial (Fin 3) k)
    [Fact (Prime F)] [Fact (Prime F')], IsProjectivePlaneCurve F → IsNonsingularProjCurve F →
    IsProjectivePlaneCurve F' → IsNonsingularProjCurve F' →
    ∀ (φ : ProjRegularMap F F') (ι : projFunctionField F' →ₐ[k] projFunctionField F),
      φ.IsSurjective → φ.IsPullback ι →
      ∀ (ψ : ℙ k (Fin 3 → k) → PrimeDivisor k (projFunctionField F)),
        (∀ P ∈ projectivePoints F k, IsLocalRingAt F (ψ P) P) →
      ∀ (ψ' : ℙ k (Fin 3 → k) → PrimeDivisor k (projFunctionField F')),
        (∀ Q ∈ projectivePoints F' k, IsLocalRingAt F' (ψ' Q) Q) →
      ∀ Q ∈ projectivePoints F' k,
        ∃ S : Finset (ℙ k (Fin 3 → k)),
          (∀ P, P ∈ S ↔ ∃ hP : P ∈ projectivePoints F k, (φ.toFun k ⟨P, hP⟩).1 = Q) ∧
          ∑ P ∈ S, (ψ P).ord (ι ((ψ' Q).unif)) = pullbackDegree ι

end NumberFieldKB.MilneEC

end
