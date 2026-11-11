import NumberFieldKB.MilneEC.Ch5ModularForms
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# Milne, *Elliptic Curves*, Chapter V §4: $L$-series of elliptic curves and of modular forms

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §4, pdf pp. 201–206: Dirichlet series, the
$L$-series of an elliptic curve (Mathlib's `WeierstrassCurve.LFunction`), $L$-series and isogeny classes
(Theorem 4.1, Corollary 4.2 and Ramanujan's conjecture are cited results, not part of this release), the $L$-series of a cusp form (Mathlib's `ModularForm.L`),
Remark 4.3, the involution $w_N$ and Hecke's Theorem 4.4 (proved from Mathlib's functional equation for
`WeakFEPair`s), the Ramanujan function $\tau$.

Isogenies: Mathlib has no regular maps of curves. As in Chapter II §1,
"$E$ and $E'$ are isogenous" is the existence of a $\mathbb Q$-algebra homomorphism
$\mathbb Q(E') \to \mathbb Q(E)$ of function fields (nonconstant maps of nonsingular projective curves
correspond to embeddings of function fields); `Isogenous` below is the same proposition over $\mathbb Q$.
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Matrix.SpecialLinearGroup
open scoped MatrixGroups Real Manifold Pointwise

namespace NumberFieldKB.MilneEC.V

/-! ### Dirichlet series -/

/-- The partial sum $\sum_{m \le n} a(m)$ of a sequence. -/
noncomputable def dsPartial (a : ℕ → ℂ) (n : ℕ) : ℂ := ∑ m ∈ Finset.Icc 1 n, a m

/-- The partial sums satisfy $s_{n+1} = s_n + a_{n+1}$. -/
lemma dsPartial_succ (a : ℕ → ℂ) (n : ℕ) : dsPartial a (n + 1) = dsPartial a n + a (n + 1) := by
  simp [dsPartial, Finset.sum_Icc_succ_top]

/-- Abel summation (summation by parts) for finite sums. -/
lemma abel_partial (a g : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, a n * g n =
      dsPartial a N * g (N + 1) +
        ∑ n ∈ Finset.range N, dsPartial a (n + 1) * (g (n + 1) - g (n + 1 + 1)) := by
  induction N with
  | zero => simp [dsPartial]
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, dsPartial_succ]
    ring

/-- The difference of consecutive terms $m^{-s} - (m+1)^{-s}$ is bounded by $|s|m^{-\sigma-1}$. -/
lemma cpow_neg_sub_le {s : ℂ} (hs : 0 ≤ s.re) {m : ℕ} (hm : 1 ≤ m) :
    ‖(m : ℂ) ^ (-s) - ((m + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * (m : ℝ) ^ (-s.re - 1) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set f : ℝ → ℂ := fun t => (t : ℂ) ^ (-s) with hf
  have hd : ∀ t ∈ Set.Icc (m : ℝ) (m + 1),
      HasDerivWithinAt f (-s * (t : ℂ) ^ (-s - 1)) (Set.Icc (m : ℝ) (m + 1)) t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hm' ht.1
    have h1 : (t : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.2 ht0
    exact (((hasStrictDerivAt_cpow_const (c := -s) h1).hasDerivAt).comp_ofReal).hasDerivWithinAt
  have hb : ∀ t ∈ Set.Icc (m : ℝ) (m + 1),
      ‖-s * (t : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * (m : ℝ) ^ (-s.re - 1) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hm' ht.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [sub_re, neg_re, one_re]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hm' ht.1 (by linarith))
      (norm_nonneg _)
  have := (convex_Icc (m : ℝ) (m + 1)).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (x := (m : ℝ)) (y := m + 1) ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
  rw [norm_sub_rev]
  simpa [hf] using this

/-- From the growth hypothesis on `x ↦ ∑_{n ≤ x} a n` for large real `x`, a uniform bound
`‖∑_{m ≤ n} a m‖ ≤ K n^b` for all positive integers `n`. -/
lemma exists_partial_bound (a : ℕ → ℂ) {A b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ᶠ x : ℝ in atTop, ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤ A * x ^ b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n → ‖dsPartial a n‖ ≤ K * (n : ℝ) ^ b := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 hA
  set M := ⌈X⌉₊ with hM
  set B := ∑ m ∈ Finset.range (M + 1), ‖dsPartial a m‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨max A B, hB0.trans (le_max_right _ _), fun n hn => ?_⟩
  have hn0 : 0 ≤ (n : ℝ) ^ b := by positivity
  have hn1 : 1 ≤ (n : ℝ) ^ b := Real.one_le_rpow (by exact_mod_cast hn) hb
  rcases le_or_gt M n with h | h
  · have hx : X ≤ (n : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast h)
    have := hX n hx
    rw [Nat.floor_natCast] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hn0)
  · have h1 : ‖dsPartial a n‖ ≤ B :=
      Finset.single_le_sum (f := fun m => ‖dsPartial a m‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.2 (by omega))
    calc _ ≤ B := h1
      _ ≤ B * (n : ℝ) ^ b := le_mul_of_one_le_right hB0 hn1
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hn0

/-- The terms of the series obtained by Abel summation of a Dirichlet series. -/
noncomputable def dsTerm (a : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  dsPartial a (n + 1) * (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 1 + 1 : ℕ) : ℂ) ^ (-s))

/-- A bound on the norm of the terms of the Dirichlet series. -/
lemma norm_dsTerm_le {a : ℕ → ℂ} {b K : ℝ}
    (hK : ∀ n : ℕ, 1 ≤ n → ‖dsPartial a n‖ ≤ K * (n : ℝ) ^ b) {s : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    ‖dsTerm a s n‖ ≤ K * ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (b - s.re - 1) := by
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h1 := hK (n + 1) (by omega)
  have h2 := cpow_neg_sub_le hs (m := n + 1) (by omega)
  unfold dsTerm
  rw [norm_mul]
  calc _ ≤ (K * ((n + 1 : ℕ) : ℝ) ^ b) * (‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
    _ = _ := by
        rw [show b - s.re - 1 = b + (-s.re - 1) by ring, Real.rpow_add hpos]; ring

/-- The terms of the Dirichlet series are summable. -/
lemma summable_dsTerm {a : ℕ → ℂ} {b K : ℝ}
    (hK : ∀ n : ℕ, 1 ≤ n → ‖dsPartial a n‖ ≤ K * (n : ℝ) ^ b) {s : ℂ} (hs : b < s.re)
    (hb : 0 ≤ b) : Summable (dsTerm a s) := by
  have hs0 : 0 ≤ s.re := by linarith
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => K * ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (b - s.re - 1)) ?_ (norm_dsTerm_le hK hs0)
  refine Summable.mul_left _ ?_
  exact (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith))

/-- The partial sums of the Dirichlet series converge. -/
lemma tendsto_dsPartial {a : ℕ → ℂ} {b K : ℝ} (hb : 0 ≤ b)
    (hK : ∀ n : ℕ, 1 ≤ n → ‖dsPartial a n‖ ≤ K * (n : ℝ) ^ b) {s : ℂ} (hs : b < s.re) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) ^ s) atTop
      (𝓝 (∑' n, dsTerm a s n)) := by
  have h1 : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) ^ s =
      dsPartial a N * ((N + 1 : ℕ) : ℂ) ^ (-s) + ∑ n ∈ Finset.range N, dsTerm a s n := by
    intro N
    have := abel_partial a (fun n : ℕ => (n : ℂ) ^ (-s)) N
    simp only [div_eq_mul_inv, ← cpow_neg]
    exact this
  have h2 : Tendsto (fun N : ℕ ↦ dsPartial a N * ((N + 1 : ℕ) : ℂ) ^ (-s)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ ↦ K * (N : ℝ) ^ (b - s.re)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (show 0 < s.re - b by linarith)).comp
        tendsto_natCast_atTop_atTop
      simpa [neg_sub, mul_zero] using this.const_mul K
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), neg_re]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    calc ‖dsPartial a N‖ * ((N + 1 : ℕ) : ℝ) ^ (-s.re)
        ≤ (K * (N : ℝ) ^ b) * (N : ℝ) ^ (-s.re) := by
          refine mul_le_mul (hK N hN) ?_ (by positivity) (le_trans (norm_nonneg _) (hK N hN))
          exact Real.rpow_le_rpow_of_nonpos hN0 (by push_cast; linarith) (by linarith)
      _ = K * (N : ℝ) ^ (b - s.re) := by
          rw [sub_eq_add_neg, Real.rpow_add hN0]; ring
  have h3 : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, dsTerm a s n) atTop
      (𝓝 (∑' n, dsTerm a s n)) := (summable_dsTerm hK hs hb).hasSum.tendsto_sum_nat
  rw [show (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) ^ s) = _ from funext h1]
  simpa using h2.add h3

/-- The sum of the terms of the Dirichlet series is differentiable on the region of convergence. -/
lemma differentiableOn_dsTerm_tsum {a : ℕ → ℂ} {b K : ℝ} (hb : 0 ≤ b) (hK0 : 0 ≤ K)
    (hK : ∀ n : ℕ, 1 ≤ n → ‖dsPartial a n‖ ≤ K * (n : ℝ) ^ b) :
    DifferentiableOn ℂ (fun s ↦ ∑' n, dsTerm a s n) {s | b < s.re} := by
  intro s0 hs0
  have hs0' : b < s0.re := hs0
  set ε := (s0.re - b) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set R := ‖s0‖ + 1 with hR
  have hR0 : 0 < R := by rw [hR]; positivity
  let U : Set ℂ := {s | b + ε < s.re} ∩ Metric.ball 0 R
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : s0 ∈ U := ⟨by show b + ε < s0.re; rw [hε]; linarith, by simp [hR]⟩
  have hsum : Summable (fun n : ℕ ↦ K * R * ((n + 1 : ℕ) : ℝ) ^ (-(1 + ε))) := by
    refine Summable.mul_left _ ?_
    exact (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith))
  have hdiff : DifferentiableOn ℂ (fun s ↦ ∑' n, dsTerm a s n) U := by
    refine differentiableOn_tsum_of_summable_norm hsum (fun n ↦ ?_) hU (fun n s hsU ↦ ?_)
    · have hc1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hc2 : ((n + 1 + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
      have d1 : Differentiable ℂ (fun s : ℂ ↦ ((n + 1 : ℕ) : ℂ) ^ (-s)) :=
        differentiable_id.neg.const_cpow (Or.inl hc1)
      have d2 : Differentiable ℂ (fun s : ℂ ↦ ((n + 1 + 1 : ℕ) : ℂ) ^ (-s)) :=
        differentiable_id.neg.const_cpow (Or.inl hc2)
      exact ((d1.sub d2).const_mul _).differentiableOn
    · obtain ⟨hsU1, hsU2⟩ := hsU
      have hs1 : b + ε < s.re := hsU1
      have hs2 : ‖s‖ < R := by simpa using hsU2
      refine (norm_dsTerm_le hK (by linarith : 0 ≤ s.re) n).trans ?_
      have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      have : ((n + 1 : ℕ) : ℝ) ^ (b - s.re - 1) ≤ ((n + 1 : ℕ) : ℝ) ^ (-(1 + ε)) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      calc K * ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (b - s.re - 1)
          ≤ K * R * ((n + 1 : ℕ) : ℝ) ^ (-(1 + ε)) := by
            apply mul_le_mul _ this (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hs2.le hK0
        _ = _ := rfl
  exact (hdiff.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt

/-- Running text (pdf p. 201): if $|\sum_{n\le x}a(n)| \le Ax^b$ for all large $x$, the Dirichlet series
$\sum a(n)n^{-s}$ converges on $\Re s > b$ (Milne: "to an analytic function"; the analyticity of the limit is
`dirichletSeries_analytic`). -/
@[kb "milne2006ec" "Ch. V, §4, convergence of Dirichlet series (running text), pdf p. 201"]
theorem dirichletSeries_converges (a : ℕ → ℂ) {A b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ᶠ x : ℝ in atTop, ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤ A * x ^ b) {s : ℂ} (hs : b < s.re) :
    ∃ L : ℂ, Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) ^ s) atTop (𝓝 L) := by
  obtain ⟨K, -, hK⟩ := exists_partial_bound a hb hA
  exact ⟨_, tendsto_dsPartial hb hK hs⟩

/-- Running text (pdf p. 201): under the same hypothesis the sum of the Dirichlet series is an analytic function
of $s$ on $\Re s > b$. -/
@[kb "milne2006ec" "Ch. V, §4, convergence of Dirichlet series (running text), pdf p. 201"]
theorem dirichletSeries_analytic (a : ℕ → ℂ) {A b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ᶠ x : ℝ in atTop, ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤ A * x ^ b) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {s | b < s.re} ∧ ∀ s : ℂ, b < s.re →
      Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) ^ s) atTop (𝓝 (F s)) := by
  obtain ⟨K, hK0, hK⟩ := exists_partial_bound a hb hA
  exact ⟨fun s ↦ ∑' n, dsTerm a s n, differentiableOn_dsTerm_tsum hb hK0 hK,
    fun s hs ↦ tendsto_dsPartial hb hK hs⟩

/-- Running text (pdf p. 201): a Dirichlet series determines its coefficients: if $\sum a(n)n^{-s}$ and
$\sum b(n)n^{-s}$ converge (absolutely) somewhere and agree as functions, then $a(n) = b(n)$ for all $n \ge 1$
(Mathlib's `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`). -/
@[kb "milne2006ec" "Ch. V, §4, a Dirichlet series determines its coefficients (running text), pdf p. 201"]
theorem dirichletSeries_coeff_unique {a b : ℕ → ℂ} (ha : LSeries.abscissaOfAbsConv a < ⊤)
    (hb : LSeries.abscissaOfAbsConv b < ⊤) (h : LSeries a = LSeries b) : ∀ n, 1 ≤ n → a n = b n :=
  fun n hn ↦ (LSeries_eq_iff_of_abscissaOfAbsConv_lt_top ha hb).1 h n (by omega)

/-! ### $L$-series and isogeny classes -/

/-- The number $N_p = \#E(\mathbb F_p)$ of points (with the point at infinity) of the reduction modulo $p$ of a
minimal model of $E$ over $\mathbb Z_p$ (Mathlib's `WeierstrassCurve.reduction`); meaningful at primes of good
reduction. Mathlib's $L$-function uses $a_p = p + 1 - N_p$ (`WeierstrassCurve.localPolynomial`). -/
noncomputable def numPoints (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : ℕ :=
  Nat.card (((E.baseChange ℚ_[p]).minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point

/-- $E$ has good reduction at $p$ (Mathlib's `WeierstrassCurve.HasGoodReduction` for a minimal model over
$\mathbb Z_p$). -/
def HasGoodReductionAt (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  ((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasGoodReduction ℤ_[p]

/-- Elliptic curves $E$, $E'$ over $\mathbb Q$ are *isogenous* (pdf p. 203, recalled from Chapter II, p. 57) if
there is a nonconstant regular map $E \to E'$, i.e. a $\mathbb Q$-embedding of function fields
$\mathbb Q(E') \to \mathbb Q(E)$ (see the module docstring). -/
@[kb "milne2006ec" "Ch. V, §4, isogenous elliptic curves (definition in prose), pdf p. 203"]
def Isogenous (E E' : WeierstrassCurve ℚ) : Prop :=
  Nonempty (E'.toAffine.FunctionField →ₐ[ℚ] E.toAffine.FunctionField)

/-- Isogeny is reflexive (the identity map). -/
theorem Isogenous.refl (E : WeierstrassCurve ℚ) : Isogenous E E := ⟨AlgHom.id ℚ _⟩

/-! ### The $L$-series of a cusp form -/

variable {N : ℕ} [NeZero N]

/-- The width of the cusp $\infty$ of $\Gamma_0(N)$ is $1$: $f(z + 1) = f(z)$ for $f$ of level $\Gamma_0(N)$, so
the $q$-expansion is in $q = e^{2\pi iz}$ (pdf p. 204). -/
theorem strictWidthInfty_Gamma0GL : (Gamma0GL N).strictWidthInfty = 1 := by
  simp

/-- Running text (pdf pp. 204–205): for a cusp form $f = \sum c(n)q^n$ of weight $2k$ for $\Gamma_0(N)$,
$|c(n)| \le Cn^k$ for a constant $C$, so $L(f, s) = \sum c(n)n^{-s}$ converges for $\Re s > k + 1$; Mathlib's
`ModularForm.L` is its sum there. -/
@[kb "milne2006ec" "Ch. V, §4, the L-series of a cusp form (running text), pdf p. 204"]
theorem cuspForm_coeff_bound_and_hasSum_L {k : ℕ} (hk : 0 < k) (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) :
    (∃ C : ℝ, ∀ n : ℕ, ‖(qExpansion 1 f).coeff n‖ ≤ C * (n : ℝ) ^ k) ∧
    ∀ s : ℂ, (k : ℝ) + 1 < s.re →
      HasSum (fun n : ℕ ↦ (qExpansion 1 f).coeff n / (n : ℂ) ^ s)
        (ModularForm.L (by positivity : (0 : ℤ) < 2 * k) f s) := by
  have hw : (Gamma0GL N).strictWidthInfty = 1 := strictWidthInfty_Gamma0GL
  have hp : (1 : ℝ) ∈ (Gamma0GL N).strictPeriods :=
    hw ▸ (Gamma0GL N).strictWidthInfty_mem_strictPeriods
  have hO := CuspFormClass.qExpansion_isBigO f
  rw [hw] at hO
  have hc0 : (qExpansion 1 f).coeff 0 = 0 := by
    rw [qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos hp)
      (SlashInvariantFormClass.periodic_comp_ofComplex f hp)]
    exact (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero
  refine ⟨?_, fun s hs ↦ ?_⟩
  · obtain ⟨C0, hC0⟩ := hO.bound
    obtain ⟨M, hM⟩ := eventually_atTop.1 hC0
    have hexp : (((2 * k : ℤ) : ℝ) / 2) = (k : ℝ) := by push_cast; ring
    simp only [hexp, Real.rpow_natCast, Real.norm_eq_abs] at hM
    set B := ∑ m ∈ Finset.range M, ‖(qExpansion 1 f).coeff m‖ with hB
    refine ⟨max C0 B, fun n ↦ ?_⟩
    have hn0 : 0 ≤ (n : ℝ) ^ k := by positivity
    rcases lt_or_ge n M with hn | hn
    · rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp [hc0, hk.ne']
      · have h1 : ‖(qExpansion 1 f).coeff n‖ ≤ B :=
          Finset.single_le_sum (f := fun m ↦ ‖(qExpansion 1 f).coeff m‖)
            (fun _ _ ↦ norm_nonneg _) (Finset.mem_range.2 hn)
        have h2 : (1 : ℝ) ≤ (n : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hpos)
        have hB0 : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
        calc _ ≤ B := h1
          _ ≤ B * (n : ℝ) ^ k := le_mul_of_one_le_right hB0 h2
          _ ≤ max C0 B * (n : ℝ) ^ k := mul_le_mul_of_nonneg_right (le_max_right _ _) hn0
    · have := hM n hn
      rw [abs_of_nonneg hn0] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hn0)
  · have hk' : (((2 * k : ℤ) : ℝ) / 2) + 1 < s.re := by push_cast; linarith
    have := CuspForm.hasSum_L (by positivity : (0 : ℤ) < 2 * k) f hk'
    rw [hw] at this
    simpa using this

/-- **Remark 4.3** (pdf p. 205): the Mellin transform $g(s) = \int_0^\infty f(iy)y^s\,dy/y$ of a cusp form is
$(2\pi)^{-s}\Gamma(s)L(f, s)$ (for $\Re s > k + 1$, where everything converges). -/
@[kb "milne2006ec" "Ch. V, Remark 4.3, pdf p. 205"]
theorem remark_4_3 {k : ℕ} (hk : 0 < k) (f : CuspForm (Gamma0GL N) (2 * k : ℤ)) {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    mellin (fun y : ℝ ↦ f (ofComplex (I * y))) s =
      (2 * π) ^ (-s) * Gamma s * ModularForm.L (by positivity : (0 : ℤ) < 2 * k) f s := by
  have hpos : 0 < s.re := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h1 := congrFun (CuspForm.Λ_eq_mellin (by positivity : (0 : ℤ) < 2 * k) f) s
  have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hpos
  have h2 : (2 * π : ℂ) ^ (-s) ≠ 0 := by
    simp [Complex.cpow_eq_zero_iff, Real.pi_ne_zero]
  rw [← h1]
  unfold ModularForm.L
  rw [Complex.Gammaℂ_def]
  field_simp

/-! ### The Ramanujan $\tau$-function -/

/-- The Ramanujan function (pdf p. 206): $q\prod_{n\ge1}(1 - q^n)^{24} = \sum_{n\ge1}\tau(n)q^n$, the $q$-expansion
coefficients of Mathlib's `ModularForm.discriminant` $= (2\pi)^{-12}\Delta$. -/
@[kb "milne2006ec" "Ch. V, §4, the Ramanujan τ-function (definition in prose), pdf p. 206"]
noncomputable def tau (n : ℕ) : ℂ := (qExpansion 1 ModularForm.discriminant).coeff n

/-- The defining identity of $\tau$: $\sum_n \tau(n)q^n = q\prod_{n\ge1}(1-q^n)^{24}$. -/
theorem hasSum_tau (z : ℍ) :
    HasSum (fun n : ℕ ↦ tau n * cexp (2 * π * I * z) ^ n)
      (cexp (2 * π * I * z) * ∏' n : ℕ, (1 - cexp (2 * π * I * z) ^ (n + 1)) ^ 24) := by
  have h := ModularForm.hasSum_qExpansion (f := CuspForm.discriminant) one_pos
    one_mem_strictPeriods_SL z
  have h2 := ModularForm.discriminant_eq_q_prod z
  simp only [Function.Periodic.qParam, ofReal_one, div_one, ModularForm.eta_q] at h h2
  have h3 : CuspForm.discriminant z = cexp (2 * π * I * z) *
      ∏' (n : ℕ), (1 - cexp (2 * π * I * z) ^ (n + 1)) ^ 24 := h2
  rw [← h3]
  exact h

/-- The $q$-expansion coefficient of index $2$ of the Eisenstein series $E_4$. -/
lemma E₄_coeff_two : (qExpansion 1 E₄).coeff 2 = 2160 := by
  norm_num [EisensteinSeries.E_qExpansion_coeff _ ⟨2, rfl⟩,
    show bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply,
    show Nat.divisors 2 = {1, 2} by decide +kernel]

/-- The $q$-expansion coefficient of index $2$ of the Eisenstein series $E_6$. -/
lemma E₆_coeff_two : (qExpansion 1 E₆).coeff 2 = -16632 := by
  norm_num [EisensteinSeries.E_qExpansion_coeff _ ⟨3, rfl⟩,
    show bernoulli 6 = 1 / 42 by decide +kernel, ArithmeticFunction.sigma_apply,
    show Nat.divisors 2 = {1, 2} by decide +kernel]

/-- $\tau(0) = 0$, $\tau(1) = 1$, $\tau(2) = -24$. -/
theorem tau_small : tau 0 = 0 ∧ tau 1 = 1 ∧ tau 2 = -24 := by
  refine ⟨?_, discriminant_qExpansion_coeff_one, ?_⟩
  · have := (CuspFormClass.zero_at_infty (CuspForm.discriminant)).valueAtInfty_eq_zero
    unfold tau
    change (qExpansion 1 ⇑CuspForm.discriminant).coeff 0 = 0
    rw [qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
        one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
        one_mem_strictPeriods_SL)]
    exact this
  · let F : ModularForm 𝒮ℒ 12 := (1 / 1728 : ℂ) •
      (ModularForm.mcast (by decide) (E₄.pow 3) -
        ModularForm.mcast (by decide) (E₆.pow 2))
    have hF : (F : ℍ → ℂ) = ModularForm.discriminant := by
      funext z
      have := discriminant_eq_E₄_cube_sub_E₆_sq z
      simp only [F, FunLike.coe_smul, FunLike.coe_sub, coe_mcast, ModularForm.coe_pow,
        Pi.smul_apply, Pi.sub_apply, Pi.pow_apply, smul_eq_mul]
      rw [this]; ring
    have hq : qExpansion 1 ModularForm.discriminant = (1 / 1728 : ℂ) •
        (qExpansion 1 E₄ * qExpansion 1 E₄ *
          qExpansion 1 E₄ -
          qExpansion 1 E₆ * qExpansion 1 E₆) := by
      rw [← hF]
      have e1 := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (1 / 1728 : ℂ)
        (ModularForm.mcast (by decide) (E₄.pow 3) -
          ModularForm.mcast (by decide) (E₆.pow 2) : ModularForm 𝒮ℒ 12)
      have e2 := ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL
        (ModularForm.mcast (by decide) (E₄.pow 3) : ModularForm 𝒮ℒ 12)
        (ModularForm.mcast (by decide) (E₆.pow 2) : ModularForm 𝒮ℒ 12)
      have e3 := ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL
        E₄ 3
      have e4 := ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL
        E₆ 2
      refine e1.trans ?_
      refine congrArg _ (e2.trans ?_)
      simp only [ModularForm.qExpansion_mcast, e3, e4]
      ring
    unfold tau
    rw [hq]
    simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_coeff_two, E₆_coeff_two,
      E₄_qExpansion_coeff_one, E₆_qExpansion_coeff_one,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
    norm_num

end NumberFieldKB.MilneEC.V
