import NumberFieldKB.MilneEC.Ch4bZetaAffine
import NumberFieldKB.TauCetiPort.AlgebraicGeometry.EllipticCurve.Affine.Point.ToClass
import NumberFieldKB.TauCetiPort.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Milne, Elliptic Curves, Chapter IV §9: the Riemann–Roch count on an elliptic curve over $\mathbb F_p$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, proof of Proposition 9.9,
pdf p. 162.  Milne's proof of Proposition 9.9 uses the Riemann–Roch theorem on $E$ in the form
$\ell(D) = \deg D$ for $\deg D \ge 1$.  This file proves the form of it that the count needs, in the affine
coordinate ring $R = \mathbb F_p[x, y]$ of $E$ (the point at infinity $O$ is the only point not in the affine part).

**Weights.** For $f \in R$ write $\operatorname{wt}(f) = \deg_x N(f)$, the degree of its norm to $\mathbb F_p[x]$: this
is the order of the pole of $f$ at $O$ ($x$ has weight 2, $y$ weight 3, and
$\operatorname{wt}(a(x) + b(x) y) = \max(2 \deg a, 2 \deg b + 3)$).  So $L(nO) = V_n$, the functions of weight at most
$n$, and for a nonzero ideal $J$ of $R$ (an effective divisor $D$ prime to $O$, of degree $c = \dim R/J$),
$L(nO - D) = J \cap V_n$.

**Riemann–Roch** (`card_inf_Vn`): $\#(J \cap V_n) = p^{n - c}$ for $n \ge c + 1$.  The proof: it holds for $J = R$
($\dim V_n = n$ for $n \ge 1$, `card_Vn`) and for the ideal of a rational point (`card_XYIdeal_inf_Vn`); and every
nonzero ideal satisfies $f J = g J_0$ with $J_0$ one of these (the surjectivity of the map from points to the ideal
class group, `WeierstrassCurve.Affine.Point.toClass_surjective`, ported from Tau Ceti/AINTLIB), which shifts both
sides by $\operatorname{wt}(g) - \operatorname{wt}(f)$ (`codim_mul_span`, `card_inf_Vn_transfer`).

## Main results
* `card_quotient_span`: $\#R/(f) = p^{\operatorname{wt}(f)}$; `wt_mul`.
* `mem_Vn_iff`, `card_Vn`: $V_n$ and its size $p^n$ ($n \ge 1$).
* `card_inf_Vn`: Riemann–Roch for $L(nO - D)$, $\deg(nO - D) \ge 1$.
* `isUnit_iff_wt_eq_zero`, `exists_const_of_isUnit`: the units of $R$ are the nonzero constants.
-/

open Polynomial WeierstrassCurve

namespace NumberFieldKB.MilneEC

variable {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve (ZMod p))

/-- The weight $\operatorname{wt}(f) = \deg_x N_{R/\mathbb F_p[x]}(f)$ of $f \in R = \mathbb F_p[x, y]$: the order of
the pole of $f$ at the point at infinity. -/
noncomputable def wt (f : W.toAffine.CoordinateRing) : ℕ :=
  (Algebra.norm (ZMod p)[X] f).natDegree

/-- The codimension $\dim_{\mathbb F_p} R/J$ of an ideal (the degree of the corresponding effective divisor). -/
noncomputable def codim (J : Ideal W.toAffine.CoordinateRing) : ℕ :=
  Module.finrank (ZMod p) (W.toAffine.CoordinateRing ⧸ J)

/-- $V_n = L(nO)$: the functions $a(x) + b(x) y$ with $2 \deg a \le n$ and $2 \deg b + 3 \le n$, i.e.
$\deg a < \lfloor n/2 \rfloor + 1$ and $\deg b < \lfloor (n-1)/2 \rfloor$. -/
noncomputable def Vn (n : ℕ) : Submodule (ZMod p) W.toAffine.CoordinateRing :=
  LinearMap.range (LinearMap.coprod
    (((LinearMap.toSpanSingleton (ZMod p)[X] W.toAffine.CoordinateRing 1).restrictScalars (ZMod p)).comp
      (Polynomial.degreeLT (ZMod p) (n / 2 + 1)).subtype)
    (((LinearMap.toSpanSingleton (ZMod p)[X] W.toAffine.CoordinateRing
      (Affine.CoordinateRing.mk W.toAffine Polynomial.X)).restrictScalars (ZMod p)).comp
      (Polynomial.degreeLT (ZMod p) ((n - 1) / 2)).subtype))

/-! ### Weights -/

/-- A nonzero ideal has finite codimension (adapted from TauCetiPort
`.../Affine/Point/ToClass.lean`, `finiteDimensional_quotient_of_ne_bot`). -/
private theorem finDim_quotient (I : Ideal W.toAffine.CoordinateRing) (hI : I ≠ ⊥) :
    FiniteDimensional (ZMod p) (W.toAffine.CoordinateRing ⧸ I) := by
  classical
  let hFin : ∀ i, Module.Finite (ZMod p)
      ((ZMod p)[X] ⧸ Ideal.span
        ({Ideal.smithCoeffs (Affine.CoordinateRing.basis W.toAffine) I hI i} : Set (ZMod p)[X])) :=
    fun i => inferInstance
  exact Module.Finite.equiv
    (Ideal.quotientEquivDirectSum (ZMod p) (Affine.CoordinateRing.basis W.toAffine) hI).symm

/-- The cardinality of a finite-dimensional $\mathbb F_p$-vector space. -/
private theorem natCard_eq_pow (V : Type*) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] : Nat.card V = p ^ Module.finrank (ZMod p) V := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

/-- $\#R/(f) = p^{\operatorname{wt}(f)}$ for $f \neq 0$. -/
theorem card_quotient_span {f : W.toAffine.CoordinateRing} (hf : f ≠ 0) :
    Nat.card (W.toAffine.CoordinateRing ⧸ Ideal.span {f}) = p ^ wt W f := by
  have hne : (Ideal.span {f} : Ideal W.toAffine.CoordinateRing) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have := finDim_quotient W _ hne
  rw [natCard_eq_pow (p := p), wt,
    finrank_quotient_span_eq_natDegree_norm (Affine.CoordinateRing.basis W.toAffine) hf]

theorem wt_mul [W.IsElliptic] {f g : W.toAffine.CoordinateRing} (hf : f ≠ 0) (hg : g ≠ 0) :
    wt W (f * g) = wt W f + wt W g := by
  unfold wt
  rw [map_mul, Polynomial.natDegree_mul (Algebra.norm_ne_zero_iff.mpr hf)
    (Algebra.norm_ne_zero_iff.mpr hg)]

/-- The weight of $1$ is $0$. -/
private theorem wt_one : wt W 1 = 0 := by
  simp [wt]

/-- The linear map whose range is $V_n$. -/
private noncomputable def VnMap (n : ℕ) :
    (Polynomial.degreeLT (ZMod p) (n / 2 + 1) × Polynomial.degreeLT (ZMod p) ((n - 1) / 2)) →ₗ[ZMod p]
      W.toAffine.CoordinateRing :=
  LinearMap.coprod
    (((LinearMap.toSpanSingleton (ZMod p)[X] W.toAffine.CoordinateRing 1).restrictScalars (ZMod p)).comp
      (Polynomial.degreeLT (ZMod p) (n / 2 + 1)).subtype)
    (((LinearMap.toSpanSingleton (ZMod p)[X] W.toAffine.CoordinateRing
      (Affine.CoordinateRing.mk W.toAffine Polynomial.X)).restrictScalars (ZMod p)).comp
      (Polynomial.degreeLT (ZMod p) ((n - 1) / 2)).subtype)

private theorem Vn_eq (n : ℕ) : Vn W n = LinearMap.range (VnMap W n) := rfl

private theorem VnMap_apply (n : ℕ) (a : Polynomial.degreeLT (ZMod p) (n / 2 + 1))
    (b : Polynomial.degreeLT (ZMod p) ((n - 1) / 2)) :
    VnMap W n (a, b) = (a : (ZMod p)[X]) • (1 : W.toAffine.CoordinateRing) +
      (b : (ZMod p)[X]) • Affine.CoordinateRing.mk W.toAffine Polynomial.X := rfl

private theorem two_smul_degree_le_iff (a : (ZMod p)[X]) (n : ℕ) :
    2 • a.degree ≤ (n : WithBot ℕ) ↔ a.degree < ((n / 2 + 1 : ℕ) : WithBot ℕ) := by
  by_cases h : a = 0
  · simp [h]
  · rw [Polynomial.degree_eq_natDegree h, nsmul_eq_mul]
    norm_cast
    omega

private theorem two_smul_degree_add_three_le_iff (b : (ZMod p)[X]) (n : ℕ) :
    2 • b.degree + 3 ≤ (n : WithBot ℕ) ↔ b.degree < (((n - 1) / 2 : ℕ) : WithBot ℕ) := by
  by_cases h : b = 0
  · simp [h]
  · rw [Polynomial.degree_eq_natDegree h, nsmul_eq_mul]
    norm_cast
    omega

private theorem mem_Vn_smul_iff (n : ℕ) (a b : (ZMod p)[X]) :
    a • (1 : W.toAffine.CoordinateRing) + b • Affine.CoordinateRing.mk W.toAffine Polynomial.X ∈ Vn W n ↔
      a.degree < ((n / 2 + 1 : ℕ) : WithBot ℕ) ∧ b.degree < (((n - 1) / 2 : ℕ) : WithBot ℕ) := by
  rw [Vn_eq, LinearMap.mem_range]
  constructor
  · rintro ⟨⟨a', b'⟩, h⟩
    rw [VnMap_apply] at h
    have h2 : ((a' : (ZMod p)[X]) - a) • (1 : W.toAffine.CoordinateRing) +
        ((b' : (ZMod p)[X]) - b) • Affine.CoordinateRing.mk W.toAffine Polynomial.X = 0 := by
      calc _ = ((a' : (ZMod p)[X]) • (1 : W.toAffine.CoordinateRing) +
            (b' : (ZMod p)[X]) • Affine.CoordinateRing.mk W.toAffine Polynomial.X) -
            (a • (1 : W.toAffine.CoordinateRing) +
              b • Affine.CoordinateRing.mk W.toAffine Polynomial.X) := by
            rw [sub_smul, sub_smul]; abel
        _ = 0 := sub_eq_zero.mpr h
    obtain ⟨h3, h4⟩ := Affine.CoordinateRing.smul_basis_eq_zero h2
    rw [sub_eq_zero] at h3 h4
    rw [← h3, ← h4]
    exact ⟨Polynomial.mem_degreeLT.mp a'.2, Polynomial.mem_degreeLT.mp b'.2⟩
  · rintro ⟨ha, hb⟩
    exact ⟨(⟨a, Polynomial.mem_degreeLT.mpr ha⟩, ⟨b, Polynomial.mem_degreeLT.mpr hb⟩), rfl⟩

/-- $f \in V_n$ if and only if $f = 0$ or $\operatorname{wt}(f) \le n$. -/
theorem mem_Vn_iff (n : ℕ) (f : W.toAffine.CoordinateRing) : f ∈ Vn W n ↔ f = 0 ∨ wt W f ≤ n := by
  obtain ⟨a, b, rfl⟩ := Affine.CoordinateRing.exists_smul_basis_eq (W' := W.toAffine) f
  rw [mem_Vn_smul_iff]
  by_cases h : a • (1 : W.toAffine.CoordinateRing) +
      b • Affine.CoordinateRing.mk W.toAffine Polynomial.X = 0
  · obtain ⟨rfl, rfl⟩ := Affine.CoordinateRing.smul_basis_eq_zero h
    simp
  · rw [or_iff_right h, wt, Polynomial.natDegree_le_iff_degree_le,
      Affine.CoordinateRing.degree_norm_smul_basis, max_le_iff, two_smul_degree_le_iff,
      two_smul_degree_add_three_le_iff]

/-- $\dim V_n = n$ for $n \ge 1$ (the functions $1, x, y, x^2, xy, \dots$ of weights $0, 2, 3, 4, 5, \dots$). -/
theorem card_Vn (n : ℕ) (hn : 1 ≤ n) : Nat.card (Vn W n) = p ^ n := by
  have hinj : Function.Injective (VnMap W n) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ h
    rw [VnMap_apply] at h
    obtain ⟨h1, h2⟩ := Affine.CoordinateRing.smul_basis_eq_zero h
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have e := (LinearEquiv.ofInjective (VnMap W n) hinj).toEquiv
  rw [Vn_eq, ← Nat.card_congr e, Nat.card_prod]
  have hdeg (m : ℕ) : Nat.card (Polynomial.degreeLT (ZMod p) m) = p ^ m := by
    rw [Nat.card_congr (Polynomial.degreeLTEquiv (ZMod p) m).toEquiv]
    simp [Nat.card_eq_fintype_card]
  rw [hdeg, hdeg, ← pow_add]
  congr 1
  omega

/-- A nonzero element of weight $0$ is a nonzero constant. -/
private theorem exists_const_of_wt_eq_zero {u : W.toAffine.CoordinateRing} (hu : u ≠ 0)
    (h : wt W u = 0) :
    ∃ c : ZMod p, c ≠ 0 ∧ u = algebraMap (ZMod p) W.toAffine.CoordinateRing c := by
  obtain ⟨a, b, rfl⟩ := Affine.CoordinateRing.exists_smul_basis_eq (W' := W.toAffine) u
  have hm := (mem_Vn_iff W 0 _).mpr (Or.inr h.le)
  rw [mem_Vn_smul_iff] at hm
  obtain ⟨ha, hb⟩ := hm
  have hb' : b.degree < 0 := by simpa using hb
  have hb0 : b = 0 := by
    by_contra hne
    exact absurd (Polynomial.zero_le_degree_iff.mpr hne) (not_le.mpr hb')
  have ha' : a.degree ≤ 0 := Nat.WithBot.lt_one_iff_le_zero.mp (by simpa using ha)
  subst hb0
  rw [Polynomial.eq_C_of_degree_le_zero ha'] at hu ⊢
  refine ⟨a.coeff 0, ?_, ?_⟩
  · intro hc
    apply hu
    rw [hc]
    simp
  · rw [zero_smul, add_zero, Algebra.smul_def, mul_one,
      IsScalarTower.algebraMap_apply (ZMod p) (ZMod p)[X] W.toAffine.CoordinateRing,
      Polynomial.algebraMap_eq]

/-- The units of $R$ are the elements of weight $0$. -/
theorem isUnit_iff_wt_eq_zero [W.IsElliptic] {u : W.toAffine.CoordinateRing} (hu : u ≠ 0) :
    IsUnit u ↔ wt W u = 0 := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_right_inv
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have := wt_mul W hu hv0
    rw [hv, wt_one] at this
    omega
  · intro h
    obtain ⟨c, hc, rfl⟩ := exists_const_of_wt_eq_zero W hu h
    exact (isUnit_iff_ne_zero.mpr hc).map _

/-- The units of $R$ are the nonzero constants. -/
theorem exists_const_of_isUnit [W.IsElliptic] {u : W.toAffine.CoordinateRing} (hu : IsUnit u) :
    ∃ c : ZMod p, c ≠ 0 ∧ u = algebraMap (ZMod p) W.toAffine.CoordinateRing c :=
  exists_const_of_wt_eq_zero W hu.ne_zero ((isUnit_iff_wt_eq_zero W hu.ne_zero).mp hu)

/-! ### Codimensions -/

/-- A nonzero ideal has finite codimension, and $\#R/J = p^{\operatorname{codim} J}$. -/
theorem card_quotient (J : Ideal W.toAffine.CoordinateRing) (hJ : J ≠ ⊥) :
    Nat.card (W.toAffine.CoordinateRing ⧸ J) = p ^ codim W J := by
  have := finDim_quotient W J hJ
  exact natCard_eq_pow _

/-- $R$ is infinite. -/
private instance infinite_coordinateRing : Infinite W.toAffine.CoordinateRing :=
  Infinite.of_injective (algebraMap (ZMod p)[X] W.toAffine.CoordinateRing)
    (FaithfulSMul.algebraMap_injective _ _)

/-- $\operatorname{codim}(IJ) = \operatorname{codim} I + \operatorname{codim} J$ for nonzero ideals ($R$ is a
Dedekind domain). -/
theorem codim_mul [W.IsElliptic] (I J : Ideal W.toAffine.CoordinateRing) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    codim W (I * J) = codim W I + codim W J := by
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  have h := cardQuot_mul I J
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply,
    card_quotient W _ hIJ, card_quotient W _ hI, card_quotient W _ hJ, ← pow_add] at h
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h

theorem codim_mul_span [W.IsElliptic] (J : Ideal W.toAffine.CoordinateRing) (hJ : J ≠ ⊥)
    {f : W.toAffine.CoordinateRing} (hf : f ≠ 0) :
    codim W (Ideal.span {f} * J) = wt W f + codim W J := by
  have hne : (Ideal.span {f} : Ideal W.toAffine.CoordinateRing) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [codim_mul W _ _ hne hJ]
  congr 1
  have h1 := card_quotient_span W hf
  rw [card_quotient W _ hne] at h1
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h1

/-! ### Riemann–Roch for $L(nO - D)$ -/

/-- Finite dimensionality of $V_n$. -/
private instance finite_Vn (n : ℕ) : Module.Finite (ZMod p) (Vn W n) := by
  rw [Vn_eq]
  have hd (m : ℕ) : Module.Finite (ZMod p) (Polynomial.degreeLT (ZMod p) m) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv (ZMod p) m).symm
  have := hd (n / 2 + 1)
  have := hd ((n - 1) / 2)
  infer_instance

/-- Riemann's inequality: $\#(J \cap V_n) \cdot \#(R/J) \ge \#V_n$. -/
theorem card_inf_Vn_mul_ge (J : Ideal W.toAffine.CoordinateRing) (hJ : J ≠ ⊥) (n : ℕ) :
    Nat.card (Vn W n) ≤
      Nat.card ↥(J.restrictScalars (ZMod p) ⊓ Vn W n) * p ^ codim W J := by
  have hq := finDim_quotient W J hJ
  let φ : Vn W n →ₗ[ZMod p] W.toAffine.CoordinateRing ⧸ J :=
    ((Submodule.mkQ J).restrictScalars (ZMod p)).comp (Vn W n).subtype
  have hker : Nat.card (LinearMap.ker φ) =
      Nat.card ↥(J.restrictScalars (ZMod p) ⊓ Vn W n) :=
    Nat.card_congr
      { toFun := fun v => ⟨v.1.1, by
          have h := LinearMap.mem_ker.mp v.2
          have h' : v.1.1 ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp h
          exact ⟨h', v.1.2⟩⟩
        invFun := fun w => ⟨⟨w.1, w.2.2⟩,
          LinearMap.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr w.2.1)⟩
        left_inv := fun v => rfl
        right_inv := fun w => rfl }
  have hfin : Module.Finite (ZMod p) ↥(J.restrictScalars (ZMod p) ⊓ Vn W n) :=
    Submodule.finiteDimensional_inf_right _ _
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  have hle : Module.finrank (ZMod p) (LinearMap.range φ) ≤ codim W J :=
    Submodule.finrank_le _
  have hkfin : Module.Finite (ZMod p) (LinearMap.ker φ) := inferInstance
  rw [natCard_eq_pow (p := p) (Vn W n), ← hker, natCard_eq_pow (p := p) (LinearMap.ker φ),
    ← pow_add]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)

/-- The ideal of a rational point: $\#(J_P \cap V_n) = p^{n - 1}$ for $n \ge 1$. -/
theorem card_XYIdeal_inf_Vn {x y : ZMod p} (h : W.toAffine.Equation x y) (n : ℕ) (hn : 1 ≤ n) :
    Nat.card ↥((Affine.CoordinateRing.XYIdeal W.toAffine x (C y)).restrictScalars (ZMod p) ⊓ Vn W n) =
      p ^ (n - 1) := by
  have hne : Affine.CoordinateRing.XYIdeal W.toAffine x (C y) ≠ ⊥ :=
    Affine.CoordinateRing.XYIdeal_ne_bot x (C y)
  have hmax : (Affine.CoordinateRing.XYIdeal W.toAffine x (C y)).IsMaximal :=
    Affine.CoordinateRing.XYIdeal_isMaximal_of_equation h
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hfin : Module.Finite (ZMod p)
      ↥((Affine.CoordinateRing.XYIdeal W.toAffine x (C y)).restrictScalars (ZMod p) ⊓ Vn W n) :=
    Submodule.finiteDimensional_inf_right _ _
  have h1 := card_inf_Vn_mul_ge W _ hne n
  have hcod : codim W (Affine.CoordinateRing.XYIdeal W.toAffine x (C y)) = 1 :=
    Affine.CoordinateRing.finrank_quotient_eq_one_iff.mpr ⟨x, y, h, rfl⟩
  rw [card_Vn W n hn, hcod, natCard_eq_pow (p := p)
    ↥((Affine.CoordinateRing.XYIdeal W.toAffine x (C y)).restrictScalars (ZMod p) ⊓ Vn W n),
    ← pow_add] at h1
  rw [natCard_eq_pow (p := p)
    ↥((Affine.CoordinateRing.XYIdeal W.toAffine x (C y)).restrictScalars (ZMod p) ⊓ Vn W n)]
  have h1V : (1 : W.toAffine.CoordinateRing) ∈ Vn W n :=
    (mem_Vn_iff W n 1).mpr (Or.inr (by rw [wt_one]; exact Nat.zero_le _))
  have hlt : (Affine.CoordinateRing.XYIdeal W.toAffine x (C y)).restrictScalars (ZMod p) ⊓ Vn W n <
      Vn W n :=
    IsConcreteLE.lt_iff_le_and_exists.mpr ⟨inf_le_right, 1, h1V,
      fun hm => hmax.ne_top ((Ideal.eq_top_iff_one _).mpr hm.1)⟩
  have hk := Submodule.finrank_lt_finrank_of_lt hlt
  have hv : Module.finrank (ZMod p) (Vn W n) = n := by
    have := card_Vn W n hn
    rw [natCard_eq_pow (p := p) (Vn W n)] at this
    exact Nat.pow_right_injective hp this
  have h2 := (Nat.pow_le_pow_iff_right hp).mp h1
  congr 1
  omega

theorem codim_XYIdeal {x y : ZMod p} (h : W.toAffine.Equation x y) :
    codim W (Affine.CoordinateRing.XYIdeal W.toAffine x (C y)) = 1 :=
  Affine.CoordinateRing.finrank_quotient_eq_one_iff.mpr ⟨x, y, h, rfl⟩

/-- One direction of the transfer: multiplication by $f$ followed by division by $g$ injects
$J \cap V_n$ into $J_0 \cap V_{n + \operatorname{wt} f - \operatorname{wt} g}$. -/
private theorem card_inf_Vn_transfer_le [W.IsElliptic] (J J₀ : Ideal W.toAffine.CoordinateRing)
    {f g : W.toAffine.CoordinateRing} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : Ideal.span {f} * J = Ideal.span {g} * J₀) (n : ℕ) (hn : wt W g ≤ n + wt W f) :
    Nat.card ↥(J.restrictScalars (ZMod p) ⊓ Vn W n) ≤
      Nat.card ↥(J₀.restrictScalars (ZMod p) ⊓ Vn W (n + wt W f - wt W g)) := by
  have hfin : Module.Finite (ZMod p)
      ↥(J₀.restrictScalars (ZMod p) ⊓ Vn W (n + wt W f - wt W g)) :=
    Submodule.finiteDimensional_inf_right _ _
  have hfinite : Finite ↥(J₀.restrictScalars (ZMod p) ⊓ Vn W (n + wt W f - wt W g)) :=
    Module.finite_of_finite (ZMod p)
  have key : ∀ h : ↥(J.restrictScalars (ZMod p) ⊓ Vn W n),
      ∃ z : ↥(J₀.restrictScalars (ZMod p) ⊓ Vn W (n + wt W f - wt W g)),
        g * (z : W.toAffine.CoordinateRing) = f * (h : W.toAffine.CoordinateRing) := by
    intro h
    have hJ : (h : W.toAffine.CoordinateRing) ∈ J := h.2.1
    have hmem : f * (h : W.toAffine.CoordinateRing) ∈ Ideal.span {g} * J₀ := by
      rw [← hfg]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) hJ
    obtain ⟨z, hz, hzeq⟩ := Ideal.mem_span_singleton_mul.mp hmem
    refine ⟨⟨z, hz, ?_⟩, hzeq⟩
    refine (mem_Vn_iff W _ z).mpr ?_
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · right
      have hh0 : (h : W.toAffine.CoordinateRing) ≠ 0 := by
        intro h0
        apply hz0
        rw [h0, mul_zero] at hzeq
        exact (mul_eq_zero.mp hzeq).resolve_left hg
      have e1 := wt_mul W hg hz0
      have e2 := wt_mul W hf hh0
      rw [hzeq] at e1
      have hwh := ((mem_Vn_iff W n _).mp h.2.2).resolve_left hh0
      omega
  choose T hT using key
  refine Nat.card_le_card_of_injective T (fun a b hab => ?_)
  have : f * (a : W.toAffine.CoordinateRing) = f * (b : W.toAffine.CoordinateRing) := by
    rw [← hT a, ← hT b, hab]
  exact Subtype.ext (mul_left_cancel₀ hf this)

/-- Transfer along $f J = g J_0$: $J \cap V_n \cong J_0 \cap V_{n + \operatorname{wt} f - \operatorname{wt} g}$. -/
theorem card_inf_Vn_transfer [W.IsElliptic] (J J₀ : Ideal W.toAffine.CoordinateRing)
    {f g : W.toAffine.CoordinateRing} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : Ideal.span {f} * J = Ideal.span {g} * J₀) (n : ℕ) (hn : wt W g ≤ n + wt W f) :
    Nat.card ↥(J.restrictScalars (ZMod p) ⊓ Vn W n) =
      Nat.card ↥(J₀.restrictScalars (ZMod p) ⊓ Vn W (n + wt W f - wt W g)) := by
  refine le_antisymm (card_inf_Vn_transfer_le W J J₀ hf hg hfg n hn) ?_
  have h := card_inf_Vn_transfer_le W J₀ J hg hf hfg.symm (n + wt W f - wt W g) (by omega)
  have e : n + wt W f - wt W g + wt W g - wt W f = n := by omega
  rwa [e] at h

/-- Every nonzero ideal is equivalent to $R$ or to the ideal of a rational point (from
`WeierstrassCurve.Affine.Point.toClass_surjective`). -/
theorem exists_equiv_rep [W.IsElliptic] (J : Ideal W.toAffine.CoordinateRing) (hJ : J ≠ ⊥) :
    ∃ (J₀ : Ideal W.toAffine.CoordinateRing) (f g : W.toAffine.CoordinateRing), f ≠ 0 ∧ g ≠ 0 ∧
      Ideal.span {f} * J = Ideal.span {g} * J₀ ∧
      (J₀ = ⊤ ∨ ∃ x y : ZMod p, W.toAffine.Equation x y ∧
        J₀ = Affine.CoordinateRing.XYIdeal W.toAffine x (C y)) := by
  classical
  have hJ' : J ∈ nonZeroDivisors (Ideal W.toAffine.CoordinateRing) :=
    mem_nonZeroDivisors_of_ne_zero hJ
  obtain ⟨P, hP⟩ := WeierstrassCurve.Affine.Point.toClass_surjective (W := W.toAffine)
    (Additive.ofMul (ClassGroup.mk0 ⟨J, hJ'⟩))
  cases P with
  | zero =>
    rw [← WeierstrassCurve.Affine.Point.zero_def,
      WeierstrassCurve.Affine.Point.toClass_zero] at hP
    have h1 : ClassGroup.mk0 ⟨J, hJ'⟩ = 1 := (Additive.ofMul.injective hP).symm
    have : Submodule.IsPrincipal J := (ClassGroup.mk0_eq_one_iff hJ').mp h1
    obtain ⟨g, hg⟩ := Submodule.IsPrincipal.principal J
    have hg0 : g ≠ 0 := by
      rintro rfl
      apply hJ
      rw [hg]
      simp
    refine ⟨⊤, 1, g, one_ne_zero, hg0, ?_, Or.inl rfl⟩
    rw [Ideal.span_singleton_one, Ideal.top_mul, Ideal.mul_top]
    exact hg
  | some x y h =>
    rw [WeierstrassCurve.Affine.Point.toClass_some_eq_ofMul_mk0 h] at hP
    obtain ⟨a, b, ha, hb, hab⟩ := ClassGroup.mk0_eq_mk0_iff.mp (Additive.ofMul.injective hP)
    exact ⟨_, b, a, hb, ha, hab.symm, Or.inr ⟨x, y, h.1, rfl⟩⟩

/-- **Riemann–Roch on $E$ for $L(nO - D)$** (used in Milne's proof of Proposition 9.9, pdf p. 162): for a nonzero
ideal $J$ of $R$ (an effective divisor $D$ prime to $O$) and $n \ge \deg D + 1$,
$\#\{f \in J : f = 0 \text{ or } \operatorname{wt}(f) \le n\} = p^{n - \deg D}$, i.e.
$\ell(nO - D) = n - \deg D$. -/
@[kb "milne2006ec" "Ch. IV, proof of Proposition 9.9 (Riemann–Roch on E), pdf p. 162"]
theorem card_inf_Vn [W.IsElliptic] (J : Ideal W.toAffine.CoordinateRing) (hJ : J ≠ ⊥) (n : ℕ)
    (hn : codim W J + 1 ≤ n) :
    Nat.card ↥(J.restrictScalars (ZMod p) ⊓ Vn W n) = p ^ (n - codim W J) := by
  obtain ⟨J₀, f, g, hf, hg, hfg, hJ₀⟩ := exists_equiv_rep W J hJ
  have hfne : (Ideal.span {f} : Ideal W.toAffine.CoordinateRing) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hJ₀ne : J₀ ≠ ⊥ := by
    rintro rfl
    have h0 : Ideal.span {f} * J = ⊥ := by rw [hfg, Ideal.mul_bot]
    exact mul_ne_zero hfne hJ h0
  have hc := codim_mul_span W J hJ hf
  rw [hfg, codim_mul_span W J₀ hJ₀ne hg] at hc
  rcases hJ₀ with rfl | ⟨x, y, hxy, rfl⟩
  · have hsub : Subsingleton (W.toAffine.CoordinateRing ⧸ (⊤ : Ideal W.toAffine.CoordinateRing)) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    have h0 : codim W ⊤ = 0 := Module.finrank_zero_of_subsingleton
    have e : (⊤ : Ideal W.toAffine.CoordinateRing).restrictScalars (ZMod p) ⊓
        Vn W (n + wt W f - wt W g) = Vn W (n + wt W f - wt W g) := by
      simp
    rw [card_inf_Vn_transfer W J ⊤ hf hg hfg n (by omega), e, card_Vn W _ (by omega)]
    congr 1
    omega
  · rw [codim_XYIdeal W hxy] at hc
    rw [card_inf_Vn_transfer W J _ hf hg hfg n (by omega), card_XYIdeal_inf_Vn W hxy _ (by omega)]
    congr 1
    omega

end NumberFieldKB.MilneEC
