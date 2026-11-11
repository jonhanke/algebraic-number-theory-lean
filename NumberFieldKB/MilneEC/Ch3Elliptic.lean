import NumberFieldKB.MilneEC.Ch3Lattice
import NumberFieldKB.MilneEC.Ch3Residue
import Mathlib.Computability.Reduce
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Milne, Elliptic Curves, Chapter III §2: elliptic functions

Proposition 2.1, Corollary 2.2, Proposition 2.7 and the isomorphism `ℂ[x, y] ≅ ℂ[℘, ℘']` of
Milne, *Elliptic Curves* (`milne2006ec`, pdf pp. 91–97).

Conventions.
* A fundamental domain for `Λ` in Milne's sense is a period parallelogram `D` of some basis of
  `Λ` (pdf p. 90); a basis of `Λ` is a `PeriodPair` `L` with `L.lattice = Λ`, and
  `D = periodParallelogram L.ω₁ L.ω₂ z₀`.
* Mathlib's meromorphic functions are total functions whose values at poles are arbitrary, so
  "`f` is not identically zero" is `∃ z, meromorphicOrderAt f z ≠ ⊤`, "`f` has no zero or pole
  at `P`" is `meromorphicOrderAt f P = 0`, and "`f` is constant" is "`f` agrees with a constant
  on a punctured neighbourhood of every point".  Identities between meromorphic functions are
  stated off a discrete set (`Filter.codiscrete ℂ`).
-/

open Complex Set Filter Topology

namespace NumberFieldKB.MilneEC.III

/-! ### Helpers on `℘` near `0` -/

lemma neg_two_lt_zero' : (-2 : WithTop ℤ) < 0 := by
  have : ((-2 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ) := WithTop.coe_lt_coe.mpr (by norm_num)
  simpa using this

lemma wp_tendsto_cobounded (L : PeriodPair) :
    Tendsto L.weierstrassP (𝓝[≠] 0) (Bornology.cobounded ℂ) :=
  tendsto_cobounded_of_meromorphicOrderAt_neg
    (by rw [L.order_weierstrassP 0 (zero_mem _)]; exact neg_two_lt_zero')

lemma eventually_not_mem_lattice (L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  have := L.compl_lattice_sdiff_singleton_mem_nhds 0
  filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with z hz hz0
  intro hzl
  exact hz ⟨hzl, hz0⟩

lemma eventually_derivWP_ne_zero (L : PeriodPair) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), L.derivWeierstrassP z ≠ 0 := by
  have h := meromorphicOrderAt_deriv_eq_sub_one (f := L.weierstrassP) (x := (0 : ℂ)) (n := -2)
    (by norm_num) (by rw [L.order_weierstrassP 0 (zero_mem _)]; rfl)
  rw [PeriodPair.deriv_weierstrassP] at h
  have hm : MeromorphicAt L.derivWeierstrassP 0 := L.meromorphic_derivWeierstrassP 0
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hm).1
    (by rw [h]; exact WithTop.coe_ne_top)

lemma transc_aux (L : PeriodPair) (R : Polynomial ℂ)
    (hR : ∀ᶠ z in 𝓝[≠] (0 : ℂ), R.eval (L.weierstrassP z) = 0) : R = 0 := by
  by_contra hR0
  have hfin : (R.roots.toFinset : Set ℂ).Finite := R.roots.toFinset.finite_toSet
  obtain ⟨B, hB⟩ := (hfin.image norm).bddAbove
  have h2 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖L.weierstrassP z‖ > B :=
    (tendsto_norm_atTop_iff_cobounded.mpr (wp_tendsto_cobounded L)).eventually
      (eventually_gt_atTop B)
  obtain ⟨z, hz2, hz3⟩ := (h2.and hR).exists
  have hmem : L.weierstrassP z ∈ (R.roots.toFinset : Set ℂ) := by
    simp [Polynomial.mem_roots hR0, hz3]
  have := hB ⟨_, hmem, rfl⟩
  linarith

/-! ### Infrastructure for Proposition 2.1 -/

-- RECT_CORE_BLOCK_START
/-- Points where `g` is analytic and nonzero. -/
def rcGood (g : ℂ → ℂ) (x : ℂ) : Prop := AnalyticAt ℂ g x ∧ g x ≠ 0

lemma rc_eventually_good {g : ℂ → ℂ} (hmer : Meromorphic g)
    (hord : ∀ z, meromorphicOrderAt g z ≠ ⊤) (x : ℂ) : ∀ᶠ y in 𝓝[≠] x, rcGood g y := by
  filter_upwards [(hmer x).eventually_analyticAt,
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmer x)).1 (hord x)] with y h1 h2
  exact ⟨h1, h2⟩

lemma rc_isOpen_good {g : ℂ → ℂ} : IsOpen {x | rcGood g x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  filter_upwards [hx.1.eventually_analyticAt, hx.1.continuousAt.eventually_ne hx.2] with y h1 h2
  exact ⟨h1, h2⟩

lemma rc_finite_bad {g : ℂ → ℂ} (hmer : Meromorphic g) (hord : ∀ z, meromorphicOrderAt g z ≠ ⊤)
    {K : Set ℂ} (hK : IsCompact K) : (K ∩ {x | ¬ rcGood g x}).Finite := by
  by_contra hinf
  obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hK inter_subset_left
  have h1 := accPt_iff_frequently.1 hx
  have h2 := eventually_nhdsWithin_iff.1 (rc_eventually_good hmer hord x)
  obtain ⟨y, ⟨hyx, hyC⟩, hg⟩ := (h1.and_eventually h2).exists
  exact hyC.2 (hg hyx)

lemma rc_countable_bad {g : ℂ → ℂ} (hmer : Meromorphic g)
    (hord : ∀ z, meromorphicOrderAt g z ≠ ⊤) : {x | ¬ rcGood g x}.Countable := by
  have h : {x | ¬ rcGood g x} ⊆ ⋃ n : ℕ, ({x | ¬ rcGood g x} ∩ Metric.closedBall (0 : ℂ) n) := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact mem_iUnion.2 ⟨n, hx, by simpa using hn⟩
  refine Countable.mono h (countable_iUnion fun n => ?_)
  rw [inter_comm]
  exact (rc_finite_bad hmer hord (isCompact_closedBall _ _)).countable

lemma rc_good_add {g : ℂ → ℂ} {c : ℂ} (hc : ∀ w, g (w + c) = g w) {z : ℂ} (h : rcGood g z) :
    rcGood g (z + c) := by
  have e : g = fun w => g (w - c) := by
    funext w
    have := hc (w - c)
    simp only [sub_add_cancel] at this
    exact this
  refine ⟨?_, by rw [hc]; exact h.2⟩
  have h3 : AnalyticAt ℂ g ((fun w : ℂ => w - c) (z + c)) := by simpa using h.1
  have h2 := AnalyticAt.comp (f := fun w : ℂ => w - c) h3 (by fun_prop)
  have h4 : AnalyticAt ℂ (fun w => g (w - c)) (z + c) := h2
  rwa [← e] at h4

lemma rc_good_sub {g : ℂ → ℂ} {c : ℂ} (hc : ∀ w, g (w + c) = g w) {z : ℂ}
    (h : rcGood g (z + c)) : rcGood g z := by
  have hc' : ∀ w, g (w + -c) = g w := by
    intro w
    have := hc (w + -c)
    simp only [neg_add_cancel_right] at this
    exact this.symm
  simpa using rc_good_add hc' h

lemma rc_order_zero_of_good {g : ℂ → ℂ} {x : ℂ} (h : rcGood g x) :
    meromorphicOrderAt g x = 0 := by
  rw [h.1.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr h.2)]
  simp

lemma rc_not_good_of_order {g : ℂ → ℂ} {x : ℂ} (h : meromorphicOrderAt g x ≠ 0) :
    ¬ rcGood g x := fun hg => h (rc_order_zero_of_good hg)

lemma rc_continuousAt_logDeriv {g : ℂ → ℂ} {x : ℂ} (h : rcGood g x) :
    ContinuousAt (logDeriv g) x := by
  have : AnalyticAt ℂ (logDeriv g) x := by
    show AnalyticAt ℂ (fun x => deriv g x / g x) x
    exact h.1.deriv.div h.1 h.2
  exact this.continuousAt

lemma rc_exists_unique_int (u c s : ℝ) (hs : 0 < s) (hne : ∀ k : ℤ, u + k * s ≠ c) :
    ∃! k : ℤ, c < u + k * s ∧ u + k * s < c + s := by
  set q := (c - u) / s with hq
  have hqs : q * s = c - u := by rw [hq]; field_simp
  have f1 := Int.floor_le q
  have f2 := Int.lt_floor_add_one q
  refine ⟨⌊q⌋ + 1, ⟨?_, ?_⟩, ?_⟩
  · push_cast
    nlinarith
  · push_cast
    have hne' := hne ⌊q⌋
    have : u + (⌊q⌋ + 1) * s ≤ c + s := by nlinarith
    exact lt_of_le_of_ne this (fun h => hne' (by linarith))
  · rintro k ⟨h1, h2⟩
    have a1 : q < k := by
      by_contra hh
      have hh := not_lt.mp hh
      nlinarith
    have a2 : (k : ℝ) < q + 1 := by
      by_contra hh
      have hh := not_lt.mp hh
      nlinarith
    have b1 : ⌊q⌋ < k := by exact_mod_cast (lt_of_le_of_lt f1 a1)
    have b2 : k ≤ ⌊q⌋ + 1 := by
      have : (k : ℝ) < ⌊q⌋ + 2 := by linarith
      have : k < ⌊q⌋ + 2 := by exact_mod_cast this
      omega
    omega

lemma rc_exp_integral {g : ℂ → ℂ} {P v : ℂ} (hgood : ∀ s : ℝ, rcGood g (P + s * v)) (s0 s1 : ℝ) :
    Complex.exp (∫ s in s0..s1, v * logDeriv g (P + s * v)) =
      g (P + s1 * v) / g (P + s0 * v) := by
  set ℓc : ℝ → ℂ := fun s => v * logDeriv g (P + s * v) with hℓc
  have hcont : Continuous ℓc := by
    rw [continuous_iff_continuousAt]
    intro s
    have h1 : ContinuousAt (logDeriv g) (P + (s:ℂ) * v) := rc_continuousAt_logDeriv (hgood s)
    have h2 : ContinuousAt (fun s : ℝ => P + (s:ℂ) * v) s := by fun_prop
    exact continuousAt_const.mul
      (ContinuousAt.comp (g := logDeriv g) (f := fun s : ℝ => P + (s:ℂ) * v) h1 h2)
  set Φ : ℝ → ℂ := fun s => ∫ r in s0..s, ℓc r with hΦ
  have hΦd : ∀ s, HasDerivAt Φ (ℓc s) s := fun s =>
    (hcont.integral_hasStrictDerivAt s0 s).hasDerivAt
  have hG : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g (P + s * v)) (deriv g (P + s * v) * v) s := by
    intro s
    have hd : HasDerivAt g (deriv g (P + (s:ℂ) * v)) (P + (s:ℂ) * v) :=
      (hgood s).1.differentiableAt.hasDerivAt
    have he : HasDerivAt (fun w : ℂ => g (P + w * v)) (deriv g (P + (s:ℂ) * v) * v) (s:ℂ) := by
      have := HasDerivAt.comp (s:ℂ) hd (((hasDerivAt_id (s:ℂ)).mul_const v).const_add P)
      exact HasDerivAt.congr_deriv this (by simp)
    exact he.comp_ofReal
  have hH : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g (P + s * v) * Complex.exp (-Φ s)) 0 s := by
    intro s
    have := (hG s).mul ((hΦd s).neg.cexp)
    refine this.congr_deriv ?_
    have hne := (hgood s).2
    simp only [hℓc, logDeriv_apply]
    field_simp
    ring
  have hdiff : Differentiable ℝ (fun s : ℝ => g (P + s * v) * Complex.exp (-Φ s)) :=
    fun s => (hH s).differentiableAt
  have key := is_const_of_deriv_eq_zero hdiff (fun s => (hH s).deriv) s1 s0
  have h0 : Φ s0 = 0 := by simp [hΦ]
  simp only [h0, neg_zero, Complex.exp_zero, mul_one] at key
  have hne0 : g (P + s0 * v) ≠ 0 := (hgood s0).2
  rw [eq_div_iff hne0]
  rw [Complex.exp_neg] at key
  have hexp : Complex.exp (Φ s1) ≠ 0 := Complex.exp_ne_zero _
  show Complex.exp (Φ s1) * g (P + s0 * v) = g (P + s1 * v)
  rw [← key]
  field_simp

lemma rc_horizontal (k : ℝ → ℂ) (hk : Continuous k) (hk1 : ∀ u, k (u + 1) = k u)
    (a b t h : ℝ) (τ : ℂ) (hτ : τ = t + h * I) :
    (∫ x in a..a + 1, ((x : ℂ) + b * I) * k x) -
        (∫ x in a..a + 1, ((x : ℂ) + ((b + h : ℝ) : ℂ) * I) * k (x - t)) =
      (∫ u in (a - t)..a, k u) - τ * ∫ u in a..a + 1, k u := by
  set F : ℝ → ℂ := fun u => ((u : ℂ) + b * I) * k u with hF
  have hFc : Continuous F := by simp only [hF]; fun_prop
  have h2 : ∀ x : ℝ, ((x : ℂ) + ((b + h : ℝ) : ℂ) * I) * k (x - t) =
      F (x - t) + τ * k (x - t) := by
    intro x; simp only [hF, hτ]; push_cast; ring
  simp_rw [h2]
  have i1 : IntervalIntegrable (fun x : ℝ => F (x - t)) MeasureTheory.volume a (a + 1) :=
    (hFc.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => τ * k (x - t)) MeasureTheory.volume a (a + 1) :=
    (continuous_const.mul (hk.comp (continuous_id.sub continuous_const))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right F t, intervalIntegral.integral_comp_sub_right k t]
  have e : a + 1 - t = a - t + 1 := by ring
  rw [e]
  have hper : Function.Periodic k 1 := hk1
  have hp := hper.intervalIntegral_add_eq (a - t) a
  have tele : (∫ x in a..a + 1, F x) - ∫ x in (a - t)..(a - t) + 1, F x = ∫ u in (a - t)..a, k u := by
    set c := a - t with hc
    have s1 : ∫ x in c..a + 1, F x = (∫ x in c..a, F x) + ∫ x in a..a + 1, F x :=
      (intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable _ _)
        (hFc.intervalIntegrable _ _)).symm
    have s2 : ∫ x in c..a + 1, F x = (∫ x in c..c + 1, F x) + ∫ x in c + 1..a + 1, F x :=
      (intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable _ _)
        (hFc.intervalIntegrable _ _)).symm
    have s3 : ∫ x in c..a, F (x + 1) = ∫ x in c + 1..a + 1, F x :=
      intervalIntegral.integral_comp_add_right F 1
    have s4 : ∫ x in c..a, F (x + 1) = (∫ x in c..a, F x) + ∫ x in c..a, k x := by
      rw [← intervalIntegral.integral_add (hFc.intervalIntegrable _ _) (hk.intervalIntegrable _ _)]
      apply intervalIntegral.integral_congr
      intro x _
      simp only [hF, hk1]
      push_cast
      ring
    linear_combination s2 - s1 - s3 + s4
  rw [← hp]
  linear_combination tele

lemma rc_rect_phi {g : ℂ → ℂ} {τ : ℂ} (a b : ℝ)
    (h1 : ∀ z, logDeriv g (z + 1) = logDeriv g z) (hτ : ∀ z, logDeriv g (z + τ) = logDeriv g z)
    (hGb : ∀ x : ℝ, rcGood g (x + b * I)) (hGa : ∀ y : ℝ, rcGood g (a + y * I)) :
    rectIntegral (fun z => z * logDeriv g z) (a + b * I) (a + 1 + (b + τ.im) * I) =
      ((∫ u : ℝ in (a - τ.re)..a, logDeriv g (u + b * I)) +
        I * ∫ y : ℝ in b..b + τ.im, logDeriv g (a + y * I)) -
        τ * ∫ u : ℝ in a..a + 1, logDeriv g (u + b * I) := by
  unfold rectIntegral
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
    add_im, mul_im, zero_add, one_re, one_im]
  set k : ℝ → ℂ := fun u => logDeriv g (u + b * I) with hk
  set lv : ℝ → ℂ := fun y => logDeriv g (a + y * I) with hlv
  have hkc : Continuous k := by
    rw [continuous_iff_continuousAt]; intro u
    exact ContinuousAt.comp (g := logDeriv g) (f := fun u : ℝ => (u : ℂ) + b * I)
      (rc_continuousAt_logDeriv (hGb u)) (by fun_prop)
  have hlc : Continuous lv := by
    rw [continuous_iff_continuousAt]; intro y
    exact ContinuousAt.comp (g := logDeriv g) (f := fun y : ℝ => (a : ℂ) + y * I)
      (rc_continuousAt_logDeriv (hGa y)) (by fun_prop)
  have hk1 : ∀ u, k (u + 1) = k u := by
    intro u
    simp only [hk]
    have : ((u + 1 : ℝ) : ℂ) + b * I = ((u : ℂ) + b * I) + 1 := by push_cast; ring
    rw [this, h1]
  have etop : ∀ x : ℝ, logDeriv g ((x : ℂ) + ((b + τ.im : ℝ) : ℂ) * I) = k (x - τ.re) := by
    intro x
    simp only [hk]
    have : (x : ℂ) + ((b + τ.im : ℝ) : ℂ) * I = (((x - τ.re : ℝ) : ℂ) + b * I) + τ := by
      apply Complex.ext <;> simp
    rw [this, hτ]
  have ev : ∀ y : ℝ, logDeriv g (((a + 1 : ℝ) : ℂ) + y * I) = lv y := by
    intro y
    simp only [hlv]
    have : ((a + 1 : ℝ) : ℂ) + y * I = ((a : ℂ) + y * I) + 1 := by push_cast; ring
    rw [this, h1]
  have top : (∫ x : ℝ in a..a + 1, ((x : ℂ) + ((b + τ.im : ℝ) : ℂ) * I) *
        logDeriv g ((x : ℂ) + ((b + τ.im : ℝ) : ℂ) * I)) =
      ∫ x : ℝ in a..a + 1, ((x : ℂ) + ((b + τ.im : ℝ) : ℂ) * I) * k (x - τ.re) :=
    intervalIntegral.integral_congr (fun x _ => by rw [etop x])
  have vert1 : (∫ y : ℝ in b..b + τ.im, (((a + 1 : ℝ) : ℂ) + y * I) *
        logDeriv g (((a + 1 : ℝ) : ℂ) + y * I)) =
      ∫ y : ℝ in b..b + τ.im, (((a + 1 : ℝ) : ℂ) + y * I) * lv y :=
    intervalIntegral.integral_congr (fun y _ => by rw [ev y])
  have hc1 : Continuous fun y : ℝ => (((a + 1 : ℝ) : ℂ) + y * I) * lv y := by
    have := hlc; fun_prop
  have hc2 : Continuous fun y : ℝ => ((a : ℂ) + y * I) * lv y := by
    have := hlc; fun_prop
  have hv : (I • ∫ y : ℝ in b..b + τ.im, (((a + 1 : ℝ) : ℂ) + y * I) * lv y) -
      I • ∫ y : ℝ in b..b + τ.im, ((a : ℂ) + y * I) * lv y =
      I * ∫ y : ℝ in b..b + τ.im, lv y := by
    rw [← smul_sub, ← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _), smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro y _
    push_cast
    ring
  have hh := rc_horizontal k hkc hk1 a b τ.re τ.im τ (by apply Complex.ext <;> simp)
  rw [top, vert1]
  linear_combination hh + hv

lemma rc_logDeriv_periodic {g : ℂ → ℂ} {c : ℂ} (hc : ∀ w, g (w + c) = g w) (z : ℂ) :
    logDeriv g (z + c) = logDeriv g z := by
  have h := deriv_comp_add_const (f := g) (a := c) (x := z)
  rw [show (fun x => g (x + c)) = g from funext hc] at h
  rw [logDeriv_apply, logDeriv_apply, hc z, ← h]

lemma rc_phi_mem {g : ℂ → ℂ} {τ : ℂ} (a b : ℝ)
    (hg1 : ∀ z, g (z + 1) = g z) (hgτ : ∀ z, g (z + τ) = g z)
    (hGb : ∀ x : ℝ, rcGood g (x + b * I)) (hGa : ∀ y : ℝ, rcGood g (a + y * I)) :
    ∃ m n : ℤ, rectIntegral (fun z => z * logDeriv g z) (a + b * I) (a + 1 + (b + τ.im) * I) =
      2 * Real.pi * I * (m + n * τ) := by
  have R := rc_rect_phi (g := g) (τ := τ) a b (rc_logDeriv_periodic hg1) (rc_logDeriv_periodic hgτ)
    hGb hGa
  -- horizontal pieces
  have hH : ∀ s0 s1 : ℝ, Complex.exp (∫ u : ℝ in s0..s1, logDeriv g (u + b * I)) =
      g (s1 + b * I) / g (s0 + b * I) := by
    intro s0 s1
    have := rc_exp_integral (g := g) (P := (b : ℂ) * I) (v := 1)
      (fun s => by simpa [add_comm] using hGb s) s0 s1
    simpa [add_comm] using this
  have hV := rc_exp_integral (g := g) (P := (a : ℂ)) (v := I) (fun s => hGa s) b (b + τ.im)
  rw [intervalIntegral.integral_const_mul] at hV
  have hA := hH (a - τ.re) a
  have hK := hH a (a + 1)
  have e1 : Complex.exp ((∫ u : ℝ in (a - τ.re)..a, logDeriv g (u + b * I)) +
      I * ∫ y : ℝ in b..b + τ.im, logDeriv g (a + y * I)) = 1 := by
    rw [Complex.exp_add, hA, hV]
    have ex : (a : ℂ) + ((b + τ.im : ℝ) : ℂ) * I = (((a - τ.re : ℝ) : ℂ) + b * I) + τ := by
      apply Complex.ext <;> simp
    rw [ex, hgτ]
    have h1 := (hGb (a - τ.re)).2
    have h2 := (hGb a).2
    field_simp
  have e2 : Complex.exp (∫ u : ℝ in a..a + 1, logDeriv g (u + b * I)) = 1 := by
    rw [hK]
    have : ((a + 1 : ℝ) : ℂ) + b * I = ((a : ℂ) + b * I) + 1 := by push_cast; ring
    rw [this, hg1]
    exact div_self (hGb a).2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 e1
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 e2
  refine ⟨n, -m, ?_⟩
  rw [R, hn, hm]
  push_cast
  ring

lemma rc_residue_thm {F : ℂ → ℂ} (hF : Meromorphic F) (a b h : ℝ) (hh : 0 < h) (S : Finset ℂ)
    (hS : ∀ p ∈ S, p ∈ (Ioo a (a + 1)) ×ℂ (Ioo b (b + h)))
    (hpole : ∀ x ∈ (Icc a (a + 1)) ×ℂ (Icc b (b + h)), x ∉ S → 0 ≤ meromorphicOrderAt F x) :
    rectIntegral F (a + b * I) (a + 1 + (b + h) * I) =
      2 * Real.pi * I * ∑ p ∈ S, residue F p := by
  have := rectIntegral_eq_two_pi_I_mul_sum_residue (f := F) (z := a + b * I)
    (w := a + 1 + (b + h) * I) (by simp) (by simpa using hh) (S := S) (by simpa using hS)
    (fun x _ => hF x) (by simpa using hpole)
  exact this

lemma rc_finsum_eq {M : Type*} [AddCommMonoid M] (R : Set ℂ) (q : ℂ → Prop) (w : ℂ → M)
    (hw : ∀ P, ¬ q P → w P = 0) (hfin : {P | P ∈ R ∧ q P}.Finite) :
    ∑ᶠ (P) (_ : P ∈ R), w P = ∑ p ∈ hfin.toFinset, w p := by
  apply finsum_mem_eq_sum_of_inter_support_eq
  ext P
  simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe, hfin.mem_toFinset, Set.mem_ofPred_eq,
    ]
  constructor
  · rintro ⟨hP, hw'⟩
    exact ⟨⟨hP, by_contra fun hq => hw' (hw P hq)⟩, hw'⟩
  · rintro ⟨⟨hP, -⟩, hw'⟩
    exact ⟨hP, hw'⟩

/-- Core of Proposition 2.1 for the lattice `ℤ + ℤτ`: a rectangle `[a, a+1] × [b, b+Im τ]` with
no zeros or poles on its boundary (and not meeting the "bad" set of a function periodic for
`1` and `τ`), such that the open rectangle is a fundamental domain for the zeros and poles, and
the sums of residues, orders, and `ord · P` over it have the stated values. -/
theorem rect_core {g : ℂ → ℂ} {τ : ℂ} (hτ : 0 < τ.im) (hmer : Meromorphic g)
    (h1 : ∀ z, g (z + 1) = g z) (hτp : ∀ z, g (z + τ) = g z)
    (hord : ∀ z, meromorphicOrderAt g z ≠ ⊤) :
    ∃ a b : ℝ,
      (∀ P : ℂ, meromorphicOrderAt g P ≠ 0 →
        ∃! mn : ℤ × ℤ,
          P + (mn.1 : ℂ) + (mn.2 : ℂ) * τ ∈ (Ioo a (a + 1)) ×ℂ (Ioo b (b + τ.im))) ∧
      {P ∈ (Ioo a (a + 1)) ×ℂ (Ioo b (b + τ.im)) | meromorphicOrderAt g P ≠ 0}.Finite ∧
      ∑ᶠ (P) (_ : P ∈ (Ioo a (a + 1)) ×ℂ (Ioo b (b + τ.im))), residue g P = 0 ∧
      ∑ᶠ (P) (_ : P ∈ (Ioo a (a + 1)) ×ℂ (Ioo b (b + τ.im))), ord g P = 0 ∧
      ∃ m n : ℤ, ∑ᶠ (P) (_ : P ∈ (Ioo a (a + 1)) ×ℂ (Ioo b (b + τ.im))), (ord g P : ℂ) * P =
        m + n * τ := by
  have hbad := rc_countable_bad hmer hord
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a ∉ Complex.re '' {x | ¬ rcGood g x} := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact Set.not_countable_univ (α := ℝ) ((hbad.image Complex.re).mono fun x _ => hcon x)
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b ∉ Complex.im '' {x | ¬ rcGood g x} := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact Set.not_countable_univ (α := ℝ) ((hbad.image Complex.im).mono fun x _ => hcon x)
  have hRe : ∀ z : ℂ, z.re = a → rcGood g z := fun z hz => by
    by_contra hn
    exact ha ⟨z, hn, hz⟩
  have hIm : ∀ z : ℂ, z.im = b → rcGood g z := fun z hz => by
    by_contra hn
    exact hb ⟨z, hn, hz⟩
  have hbd : ∀ x : ℂ, (x.re = a ∨ x.re = a + 1 ∨ x.im = b ∨ x.im = b + τ.im) → rcGood g x := by
    rintro x (hx | hx | hx | hx)
    · exact hRe x hx
    · have := rc_good_add h1 (hRe (x - 1) (by simp [hx]))
      simpa using this
    · exact hIm x hx
    · have := rc_good_add hτp (hIm (x - τ) (by simp [hx]))
      simpa using this
  have hGa : ∀ y : ℝ, rcGood g (a + y * I) := fun y => hRe _ (by simp)
  have hGb : ∀ x : ℝ, rcGood g (x + b * I) := fun x => hIm _ (by simp)
  have hint : ∀ (m n : ℤ) (w : ℂ), g (w + ((m : ℂ) + n * τ)) = g w := by
    intro m n w
    have hp1 : Function.Periodic g 1 := h1
    have hp2 : Function.Periodic g τ := hτp
    have e1 := (hp1.int_mul m) (w + n * τ)
    have e2 := (hp2.int_mul n) w
    have : w + ((m : ℂ) + n * τ) = (w + n * τ) + (m * 1) := by ring
    rw [this, e1, e2]
  have hngood : ∀ P : ℂ, ¬ rcGood g P → ∀ m n : ℤ, ¬ rcGood g (P + m + n * τ) := by
    intro P hP m n hgood
    apply hP
    apply rc_good_sub (hint m n)
    rwa [← add_assoc]
  have hpart1 : ∀ P : ℂ, meromorphicOrderAt g P ≠ 0 →
      ∃! mn : ℤ × ℤ, P + (mn.1 : ℂ) + (mn.2 : ℂ) * τ ∈ (Ioo a (a + 1)) ×ℂ (Ioo b (b + τ.im)) := by
    intro P hP
    have hng := hngood P (rc_not_good_of_order hP)
    have hre : ∀ m n : ℤ, (P + m + n * τ).re = P.re + n * τ.re + m * 1 := by
      intro m n; simp; ring
    have him : ∀ m n : ℤ, (P + m + n * τ).im = P.im + n * τ.im := by intro m n; simp
    obtain ⟨n0, ⟨hn1, hn2⟩, hn3⟩ := rc_exists_unique_int P.im b τ.im hτ (fun k hk =>
      hng 0 k (hIm _ (by rw [him]; exact hk)))
    obtain ⟨m0, ⟨hm1, hm2⟩, hm3⟩ := rc_exists_unique_int (P.re + n0 * τ.re) a 1 one_pos
      (fun k hk => hng k n0 (hRe _ (by rw [hre]; exact hk)))
    refine ⟨(m0, n0), ?_, ?_⟩
    · show _ ∈ _
      rw [mem_reProdIm]
      refine ⟨?_, ?_⟩
      · rw [hre]; exact ⟨hm1, by simpa using hm2⟩
      · rw [him]; exact ⟨hn1, hn2⟩
    · rintro ⟨m, n⟩ hmn
      rw [mem_reProdIm] at hmn
      obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := hmn
      simp only [him, hre] at r1 r2 i1 i2
      have hn : n = n0 := hn3 n ⟨i1, i2⟩
      subst hn
      have hm : m = m0 := hm3 m ⟨r1, by simpa using r2⟩
      subst hm
      rfl
  have hfin : {P | P ∈ (Ioo a (a + 1)) ×ℂ (Ioo b (b + τ.im)) ∧
      meromorphicOrderAt g P ≠ 0}.Finite := by
    refine (rc_finite_bad hmer hord
      (isCompact_closedBall (0 : ℂ) (|a| + 1 + (|b| + τ.im)))).subset ?_
    rintro P ⟨hP, hne⟩
    refine ⟨?_, rc_not_good_of_order hne⟩
    rw [mem_reProdIm] at hP
    obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := hP
    rw [mem_closedBall_zero_iff]
    refine (Complex.norm_le_abs_re_add_abs_im P).trans ?_
    have e1 : |P.re| ≤ |a| + 1 := abs_le.2 ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩
    have e2 : |P.im| ≤ |b| + τ.im :=
      abs_le.2 ⟨by linarith [neg_abs_le b], by linarith [le_abs_self b]⟩
    linarith
  have S_in : ∀ p ∈ hfin.toFinset, p ∈ (Ioo a (a + 1)) ×ℂ (Ioo b (b + τ.im)) :=
    fun p hp => (hfin.mem_toFinset.1 hp).1
  have hzero : ∀ x ∈ (Icc a (a + 1)) ×ℂ (Icc b (b + τ.im)), x ∉ hfin.toFinset →
      meromorphicOrderAt g x = 0 := by
    intro x hx hxS
    rw [mem_reProdIm] at hx
    by_cases hxR : x ∈ (Ioo a (a + 1)) ×ℂ (Ioo b (b + τ.im))
    · by_contra hne
      exact hxS (hfin.mem_toFinset.2 ⟨hxR, hne⟩)
    · apply rc_order_zero_of_good
      apply hbd
      rw [mem_reProdIm] at hxR
      obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := hx
      rcases r1.eq_or_lt with h | h
      · exact Or.inl h.symm
      rcases r2.eq_or_lt with h' | h'
      · exact Or.inr (Or.inl h')
      rcases i1.eq_or_lt with k | k
      · exact Or.inr (Or.inr (Or.inl k.symm))
      rcases i2.eq_or_lt with k' | k'
      · exact Or.inr (Or.inr (Or.inr k'))
      exact absurd ⟨⟨h, h'⟩, ⟨k, k'⟩⟩ hxR
  have two : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hordz : ∀ P, ¬ meromorphicOrderAt g P ≠ 0 → ord g P = 0 := by
    intro P hP
    have := not_not.1 hP
    simp [ord, this]
  refine ⟨a, b, hpart1, hfin, ?_, ?_, ?_⟩
  · have hr := rc_residue_thm hmer a b τ.im hτ hfin.toFinset S_in
      (fun x hx hxS => (hzero x hx hxS).ge)
    rw [rectIntegral_eq_zero_of_periodic h1 hτp a b] at hr
    have hsum : ∑ p ∈ hfin.toFinset, residue g p = 0 := by
      rcases mul_eq_zero.1 hr.symm with h | h
      · exact absurd h two
      · exact h
    rw [rc_finsum_eq _ (fun P => meromorphicOrderAt g P ≠ 0) _ ?_ hfin]
    · exact hsum
    · intro P hP
      exact residue_eq_zero_of_nonneg_order (hmer P) (not_not.1 hP).ge
  · have hlm : Meromorphic (logDeriv g) := hmer.logDeriv
    have hr := rc_residue_thm hlm a b τ.im hτ hfin.toFinset S_in
      (fun x hx hxS => meromorphicOrderAt_logDeriv_nonneg (hmer x) (hzero x hx hxS))
    rw [rectIntegral_eq_zero_of_periodic (rc_logDeriv_periodic h1) (rc_logDeriv_periodic hτp)
      a b] at hr
    have hres : ∀ p ∈ hfin.toFinset, residue (logDeriv g) p = (ord g p : ℂ) :=
      fun p _ => residue_logDeriv (hmer p) (hord p)
    rw [Finset.sum_congr rfl hres] at hr
    have hsum : ∑ p ∈ hfin.toFinset, (ord g p : ℂ) = 0 := by
      rcases mul_eq_zero.1 hr.symm with h | h
      · exact absurd h two
      · exact h
    have hsumZ : ∑ p ∈ hfin.toFinset, ord g p = 0 := by exact_mod_cast hsum
    rw [rc_finsum_eq _ (fun P => meromorphicOrderAt g P ≠ 0) _ hordz hfin]
    exact hsumZ
  · obtain ⟨m, n, hmn⟩ := rc_phi_mem (g := g) (τ := τ) a b h1 hτp hGb hGa
    have hφ : Meromorphic (fun z : ℂ => z * logDeriv g z) := by
      intro x
      exact (analyticAt_id.meromorphicAt).mul (hmer.logDeriv x)
    have hr := rc_residue_thm hφ a b τ.im hτ hfin.toFinset S_in (fun x hx hxS => by
      have h0 := hzero x hx hxS
      have hid : MeromorphicAt (fun z : ℂ => z) x := analyticAt_id.meromorphicAt
      show 0 ≤ meromorphicOrderAt ((fun z : ℂ => z) * logDeriv g) x
      rw [meromorphicOrderAt_mul hid (hmer.logDeriv x)]
      exact add_nonneg (analyticAt_id.meromorphicOrderAt_nonneg)
        (meromorphicOrderAt_logDeriv_nonneg (hmer x) h0))
    rw [hmn] at hr
    have hres : ∀ p ∈ hfin.toFinset, residue (fun z : ℂ => z * logDeriv g z) p =
        p * (ord g p : ℂ) := fun p _ => residue_id_mul_logDeriv (hmer p) (hord p)
    rw [Finset.sum_congr rfl hres] at hr
    have hsum : ∑ p ∈ hfin.toFinset, p * (ord g p : ℂ) = m + n * τ :=
      (mul_left_cancel₀ two hr).symm
    refine ⟨m, n, ?_⟩
    rw [rc_finsum_eq _ (fun P => meromorphicOrderAt g P ≠ 0) _ ?_ hfin]
    · rw [← hsum]
      exact Finset.sum_congr rfl fun p _ => mul_comm _ _
    · intro P hP
      simp [hordz P hP]
-- RECT_CORE_BLOCK_END

-- GENERIC_Z0_BLOCK_START
lemma exists_notMem_of_countable {s : Set ℝ} (hs : s.Countable) : ∃ x : ℝ, x ∉ s := by
  by_contra h
  push Not at h
  exact Cardinal.not_countable_real (hs.mono (fun x _ => h x))

/-- Zeros and poles of a nonzero meromorphic function meet each compact set in a finite set. -/
lemma finite_order_ne_zero_inter {f : ℂ → ℂ} (hf : Meromorphic f)
    (hord : ∀ z, meromorphicOrderAt f z ≠ ⊤) {K : Set ℂ} (hK : IsCompact K) :
    {P ∈ K | meromorphicOrderAt f P ≠ 0}.Finite := by
  have hmer : MeromorphicOn f K := fun x _ => hf x
  refine ((MeromorphicOn.divisor f K).finiteSupport hK).subset ?_
  intro P ⟨hPK, hP0⟩
  rw [Function.mem_support, MeromorphicOn.divisor_apply hmer hPK]
  intro h
  rw [WithTop.untop₀_eq_zero] at h
  rcases h with h | h
  · exact hP0 h
  · exact hord P h

lemma countable_order_ne_zero {f : ℂ → ℂ} (hf : Meromorphic f)
    (hord : ∀ z, meromorphicOrderAt f z ≠ ⊤) :
    {P | meromorphicOrderAt f P ≠ 0}.Countable := by
  have : {P | meromorphicOrderAt f P ≠ 0} ⊆
      ⋃ n : ℕ, {P ∈ Metric.closedBall (0 : ℂ) n | meromorphicOrderAt f P ≠ 0} := by
    intro P hP
    obtain ⟨n, hn⟩ := exists_nat_ge ‖P‖
    exact mem_iUnion.2 ⟨n, by simpa using hn, hP⟩
  refine Countable.mono this (countable_iUnion fun n => ?_)
  exact (finite_order_ne_zero_inter hf hord (isCompact_closedBall _ _)).countable

lemma repr_comb' (L : PeriodPair) (s t : ℝ) (i : Fin 2) :
    L.basis.repr ((s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂) i = if i = 0 then s else t := by
  have h1 : ((s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂) = s • L.basis 0 + t • L.basis 1 := by
    simp [Complex.real_smul]
  rw [h1, map_add, map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]
  fin_cases i <;> simp

/-- A base point `z₀` for which the boundary of the period parallelogram avoids the zeros and
poles of `f` (they are countable, the boundary depends on `z₀` through two real parameters). -/
theorem exists_generic_z0 (L : PeriodPair) {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (hord : ∀ z, meromorphicOrderAt f z ≠ ⊤) :
    ∃ z₀ : ℂ, ∀ P ∈ frontier (periodParallelogram L.ω₁ L.ω₂ z₀), meromorphicOrderAt f P = 0 := by
  set Q := {P | meromorphicOrderAt f P ≠ 0} with hQ
  have hQc : Q.Countable := countable_order_ne_zero hf.1 hord
  have hC : ∀ i : Fin 2, ∃ u : ℝ, ∀ P ∈ Q, u ≠ L.basis.repr P i ∧ u ≠ L.basis.repr P i - 1 := by
    intro i
    have hc : ((fun P => L.basis.repr P i) '' Q ∪ (fun P => L.basis.repr P i - 1) '' Q).Countable :=
      (hQc.image _).union (hQc.image _)
    obtain ⟨u, hu⟩ := exists_notMem_of_countable hc
    refine ⟨u, fun P hP => ⟨?_, ?_⟩⟩
    · intro h; exact hu (Or.inl ⟨P, hP, h.symm⟩)
    · intro h; exact hu (Or.inr ⟨P, hP, h.symm⟩)
  obtain ⟨u, hu⟩ := hC 0
  obtain ⟨v, hv⟩ := hC 1
  refine ⟨(u : ℂ) * L.ω₁ + (v : ℂ) * L.ω₂, fun P hP => ?_⟩
  by_contra hP0
  have hPQ : P ∈ Q := hP0
  rw [frontier_periodParallelogram] at hP
  obtain ⟨⟨s, t, hs, ht, hPe⟩, hPn⟩ := hP
  have hrepr : ∀ i : Fin 2, L.basis.repr P i = (if i = 0 then u + s else v + t) := by
    intro i
    have : P = ((u + s : ℝ) : ℂ) * L.ω₁ + ((v + t : ℝ) : ℂ) * L.ω₂ := by
      rw [hPe]; push_cast; ring
    rw [this, repr_comb']
  have hr0 : L.basis.repr P 0 = u + s := by simpa using hrepr 0
  have hr1 : L.basis.repr P 1 = v + t := by simpa using hrepr 1
  have hnot : ¬ (s ∈ Ioo (0:ℝ) 1 ∧ t ∈ Ioo (0:ℝ) 1) := fun ⟨h1, h2⟩ => hPn ⟨s, t, h1, h2, hPe⟩
  rw [not_and_or] at hnot
  rcases hnot with h | h
  · have : s = 0 ∨ s = 1 := by
      by_contra hh
      push Not at hh
      exact h ⟨lt_of_le_of_ne hs.1 (Ne.symm hh.1), lt_of_le_of_ne hs.2 hh.2⟩
    rcases this with rfl | rfl
    · exact (hu P hPQ).1 (by rw [hr0]; ring)
    · exact (hu P hPQ).2 (by rw [hr0]; ring)
  · have : t = 0 ∨ t = 1 := by
      by_contra hh
      push Not at hh
      exact h ⟨lt_of_le_of_ne ht.1 (Ne.symm hh.1), lt_of_le_of_ne ht.2 hh.2⟩
    rcases this with rfl | rfl
    · exact (hv P hPQ).1 (by rw [hr1]; ring)
    · exact (hv P hPQ).2 (by rw [hr1]; ring)
-- GENERIC_Z0_BLOCK_END

/-! ### Periodicity of orders and residues -/

lemma ord_add_lattice {Λ : Submodule ℤ ℂ} {f : ℂ → ℂ} (hf : IsPeriodicFor Λ f) {ω : ℂ}
    (hω : ω ∈ Λ) (P : ℂ) : meromorphicOrderAt f (P + ω) = meromorphicOrderAt f P := by
  have h : (f ∘ (· + ω)) = f := funext fun z => hf ω hω z
  have := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (f := f) (x := P) (c := ω)
  rw [h] at this
  exact this.symm

lemma ord_add_lattice' {Λ : Submodule ℤ ℂ} {f : ℂ → ℂ} (hf : IsPeriodicFor Λ f) {ω : ℂ}
    (hω : ω ∈ Λ) (P : ℂ) : ord f (P + ω) = ord f P := by
  unfold ord; rw [ord_add_lattice hf hω]

lemma residue_add_lattice {Λ : Submodule ℤ ℂ} {f : ℂ → ℂ} (hf : IsDoublyPeriodic Λ f) {ω : ℂ}
    (hω : ω ∈ Λ) (P : ℂ) : residue f (P + ω) = residue f P := by
  have h : (fun z => f (z + ω)) = f := funext fun z => hf.2 ω hω z
  have := residue_comp_add (f := f) (p := P) ω (hf.1 _)
  rw [h] at this
  exact this.symm

/-! ### Fundamental-domain comparison of sums -/

lemma fd_exists_sigma {Λ : Submodule ℤ ℂ} {Z A B : Set ℂ} (hZ : ∀ P ∈ Z, ∀ ω ∈ Λ, P + ω ∈ Z)
    (hA : ∀ P ∈ Z, ∃! ω, ω ∈ Λ ∧ P + ω ∈ A) (hB : ∀ P ∈ Z, ∃! ω, ω ∈ Λ ∧ P + ω ∈ B) :
    ∃ σ : ℂ → ℂ, (∀ P ∈ Z, σ P ∈ Λ ∧ P + σ P ∈ B) ∧
      Set.BijOn (fun P => P + σ P) (Z ∩ A) (Z ∩ B) := by
  classical
  choose! σ hσ using fun P (hP : P ∈ Z) => (hB P hP).exists
  refine ⟨σ, hσ, ?_, ?_, ?_⟩
  · rintro P ⟨hPZ, hPA⟩
    exact ⟨hZ P hPZ _ (hσ P hPZ).1, (hσ P hPZ).2⟩
  · rintro P ⟨hPZ, hPA⟩ Q ⟨hQZ, hQA⟩ hPQ
    have hPQ' : Q = P + (σ P - σ Q) := by
      have : P + σ P = Q + σ Q := hPQ
      linear_combination -this
    obtain ⟨ω0, -, hω0⟩ := hA P hPZ
    have h1 : (0 : ℂ) = ω0 := hω0 0 ⟨Λ.zero_mem, by simpa using hPA⟩
    have h2 : σ P - σ Q = ω0 := hω0 _ ⟨Λ.sub_mem (hσ P hPZ).1 (hσ Q hQZ).1, by rw [← hPQ']; exact hQA⟩
    have h3 : σ P - σ Q = 0 := by rw [h2, ← h1]
    rw [hPQ', h3, add_zero]
  · rintro Q ⟨hQZ, hQB⟩
    obtain ⟨ω', hω', -⟩ := hA Q hQZ
    have hPZ : Q + ω' ∈ Z := hZ Q hQZ ω' hω'.1
    obtain ⟨ω0, -, hω0⟩ := hB (Q + ω') hPZ
    have h1 : σ (Q + ω') = ω0 := hω0 _ (hσ _ hPZ)
    have h2 : -ω' = ω0 := hω0 _ ⟨Λ.neg_mem hω'.1, by simpa [add_assoc] using hQB⟩
    refine ⟨Q + ω', ⟨hPZ, hω'.2⟩, ?_⟩
    show Q + ω' + σ (Q + ω') = Q
    rw [h1, ← h2]; ring

lemma fd_finsum {M : Type*} [AddCommMonoid M] {Λ : Submodule ℤ ℂ} {Z A B : Set ℂ}
    (hZ : ∀ P ∈ Z, ∀ ω ∈ Λ, P + ω ∈ Z)
    (hA : ∀ P ∈ Z, ∃! ω, ω ∈ Λ ∧ P + ω ∈ A) (hB : ∀ P ∈ Z, ∃! ω, ω ∈ Λ ∧ P + ω ∈ B)
    {h : ℂ → M} (hper : ∀ P, ∀ ω ∈ Λ, h (P + ω) = h P) (hsupp : ∀ P ∉ Z, h P = 0) :
    ∑ᶠ P ∈ A, h P = ∑ᶠ P ∈ B, h P := by
  obtain ⟨σ, hσ, hbij⟩ := fd_exists_sigma hZ hA hB
  have e1 : ∀ S : Set ℂ, ∑ᶠ P ∈ S, h P = ∑ᶠ P ∈ Z ∩ S, h P := by
    intro S
    apply finsum_mem_inter_support_eq
    ext P
    simp only [mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨hS, hP⟩
      exact ⟨⟨by_contra fun hZ' => hP (hsupp P hZ'), hS⟩, hP⟩
    · rintro ⟨⟨_, hS⟩, hP⟩; exact ⟨hS, hP⟩
  rw [e1 A, e1 B]
  exact finsum_mem_eq_of_bijOn (fun P => P + σ P) hbij
    (fun P hP => (hper P _ (hσ P hP.1).1).symm)

lemma fd_finite {Λ : Submodule ℤ ℂ} {Z A B : Set ℂ} (hZ : ∀ P ∈ Z, ∀ ω ∈ Λ, P + ω ∈ Z)
    (hA : ∀ P ∈ Z, ∃! ω, ω ∈ Λ ∧ P + ω ∈ A) (hB : ∀ P ∈ Z, ∃! ω, ω ∈ Λ ∧ P + ω ∈ B) :
    (Z ∩ A).Finite ↔ (Z ∩ B).Finite := by
  obtain ⟨σ, hσ, hbij⟩ := fd_exists_sigma hZ hA hB
  exact hbij.finite_iff_finite

/-- The `ord`-weighted sum of positions changes by an element of `Λ`. -/
lemma fd_weighted {Λ : Submodule ℤ ℂ} {Z A B : Set ℂ} (hZ : ∀ P ∈ Z, ∀ ω ∈ Λ, P + ω ∈ Z)
    (hA : ∀ P ∈ Z, ∃! ω, ω ∈ Λ ∧ P + ω ∈ A) (hB : ∀ P ∈ Z, ∃! ω, ω ∈ Λ ∧ P + ω ∈ B)
    (hfin : (Z ∩ A).Finite) {o : ℂ → ℤ} (hper : ∀ P, ∀ ω ∈ Λ, o (P + ω) = o P)
    (hsupp : ∀ P ∉ Z, o P = 0) :
    (∑ᶠ P ∈ B, (o P : ℂ) * P) - ∑ᶠ P ∈ A, (o P : ℂ) * P ∈ Λ := by
  obtain ⟨σ, hσ, hbij⟩ := fd_exists_sigma hZ hA hB
  have e1 : ∀ S : Set ℂ, ∑ᶠ P ∈ S, (o P : ℂ) * P = ∑ᶠ P ∈ Z ∩ S, (o P : ℂ) * P := by
    intro S
    apply finsum_mem_inter_support_eq
    ext P
    simp only [mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨hS, hP⟩
      refine ⟨⟨by_contra fun hZ' => hP (by simp [hsupp P hZ']), hS⟩, hP⟩
    · rintro ⟨⟨_, hS⟩, hP⟩; exact ⟨hS, hP⟩
  rw [e1 A, e1 B]
  have e2 : ∑ᶠ P ∈ Z ∩ A, (o (P + σ P) : ℂ) * (P + σ P) = ∑ᶠ Q ∈ Z ∩ B, (o Q : ℂ) * Q :=
    finsum_mem_eq_of_bijOn (fun P => P + σ P) hbij (fun P hP => rfl)
  rw [← e2]
  have e3 : ∀ P ∈ Z ∩ A, (o (P + σ P) : ℂ) * (P + σ P) =
      (o P : ℂ) * P + (o P : ℂ) * σ P := by
    intro P hP
    rw [hper P _ (hσ P hP.1).1]; ring
  rw [finsum_mem_congr rfl e3, finsum_mem_add_distrib hfin, add_sub_cancel_left]
  apply finsum_mem_induction (fun x : ℂ => x ∈ Λ) Λ.zero_mem (fun x y hx hy => Λ.add_mem hx hy)
  intro P hP
  have := Λ.smul_mem (o P) (hσ P hP.1).1
  simpa [zsmul_eq_mul] using this

/-! ### The normalized lattice -/

lemma period_ne_zero (L : PeriodPair) : L.ω₂ ≠ 0 := by
  have := L.indep.ne_zero 1
  simpa using this

lemma exists_tau (L : PeriodPair) :
    ∃ τ : ℂ, 0 < τ.im ∧ ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ L.ω₁ = (ε : ℂ) * L.ω₂ * τ := by
  have h2 := period_ne_zero L
  set r := L.ω₁ / L.ω₂ with hr
  have hω1 : L.ω₁ = r * L.ω₂ := by rw [hr]; field_simp
  have him : r.im ≠ 0 := by
    intro h0
    have hre : r = (r.re : ℂ) := Complex.ext (by simp) (by simpa using h0)
    have hli := (LinearIndependent.pair_iff.1 L.indep) 1 (-r.re) (by
      have hω1' : L.ω₁ = (r.re : ℂ) * L.ω₂ := by
        calc L.ω₁ = r * L.ω₂ := hω1
          _ = (r.re : ℂ) * L.ω₂ := by rw [← hre]
      simp only [Complex.real_smul]
      push_cast
      rw [hω1']; ring)
    simpa using hli.1
  rcases lt_or_gt_of_ne him with h | h
  · refine ⟨-r, by simpa using h, -1, Or.inr rfl, ?_⟩
    rw [hω1]; push_cast; ring
  · exact ⟨r, h, 1, Or.inl rfl, by rw [hω1]; push_cast; ring⟩

lemma mem_lattice_iff_tau (L : PeriodPair) {τ : ℂ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hτ : L.ω₁ = (ε : ℂ) * L.ω₂ * τ) (x : ℂ) :
    x ∈ L.lattice ↔ ∃ m n : ℤ, x = L.ω₂ * ((m : ℂ) + n * τ) := by
  have hε2 : ((ε : ℂ)) * ε = 1 := by rcases hε with rfl | rfl <;> simp
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨n, m * ε, ?_⟩
    rw [hτ]; push_cast; ring
  · rintro ⟨m, n, rfl⟩
    refine ⟨n * ε, m, ?_⟩
    rw [hτ]; push_cast; linear_combination ((n : ℂ) * L.ω₂ * τ) * hε2

/-- The rescaled function `z ↦ f (ω₂ z)` has periods `1` and `τ`. -/
lemma scaled_periodic (L : PeriodPair) {f : ℂ → ℂ} (hf : IsPeriodicFor L.lattice f) {τ : ℂ}
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hτ : L.ω₁ = (ε : ℂ) * L.ω₂ * τ) :
    (∀ z, f (L.ω₂ * (z + 1)) = f (L.ω₂ * z)) ∧ (∀ z, f (L.ω₂ * (z + τ)) = f (L.ω₂ * z)) := by
  constructor
  · intro z
    have := hf L.ω₂ L.ω₂_mem_lattice (L.ω₂ * z)
    rw [← this]; congr 1; ring
  · intro z
    have h := (mem_lattice_iff_tau L hε hτ (L.ω₂ * τ)).2 ⟨0, 1, by simp⟩
    have := hf _ h (L.ω₂ * z)
    rw [← this]; congr 1; ring

lemma scaled_meromorphic {f : ℂ → ℂ} (hf : Meromorphic f) {c : ℂ} (hc : c ≠ 0) :
    Meromorphic (fun z => f (c * z)) := by
  intro x
  have := (meromorphicAt_comp_iff_of_deriv_ne_zero (f := f) (g := fun z => c * z) (x := x)
    (by fun_prop) (by simpa using hc)).2 (hf (c * x))
  exact this

lemma scaled_order {f : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) (z : ℂ) :
    meromorphicOrderAt (fun z => f (c * z)) z = meromorphicOrderAt f (c * z) := by
  have := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) (g := fun z => c * z) (x := z)
    (by fun_prop) (by simpa using hc)
  exact this

/-! ### Proposition 2.1 -/

/-- Proposition 2.1 (Milne, pdf p. 91): let `f` be a doubly periodic function for `Λ`, not
identically zero, and let `D` be a fundamental domain for `Λ` such that `f` has no zeros or poles
on the boundary of `D`.  Then `f` has finitely many zeros and poles in `D`, and
(a) `∑_{P ∈ D} Res_P(f) = 0`; (b) `∑_{P ∈ D} ord_P(f) = 0`;
(c) `∑_{P ∈ D} ord_P(f) · P ≡ 0 mod Λ`.
(The sums are finite sums over the points of `D`; their terms vanish off the zeros and poles.) -/
@[kb "milne2006ec" "Ch. III, Prop. 2.1, pdf p. 91"]
theorem prop_2_1 (L : PeriodPair) {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (hf0 : ∃ z, meromorphicOrderAt f z ≠ ⊤) (z₀ : ℂ)
    (hD : ∀ P ∈ frontier (periodParallelogram L.ω₁ L.ω₂ z₀), meromorphicOrderAt f P = 0) :
    {P ∈ periodParallelogram L.ω₁ L.ω₂ z₀ | meromorphicOrderAt f P ≠ 0}.Finite ∧
      ∑ᶠ (P) (_ : P ∈ periodParallelogram L.ω₁ L.ω₂ z₀), residue f P = 0 ∧
      ∑ᶠ (P) (_ : P ∈ periodParallelogram L.ω₁ L.ω₂ z₀), ord f P = 0 ∧
      (∑ᶠ (P) (_ : P ∈ periodParallelogram L.ω₁ L.ω₂ z₀), (ord f P : ℂ) * P) ∈ L.lattice := by
  have hord : ∀ z, meromorphicOrderAt f z ≠ ⊤ :=
    hf.1.exists_meromorphicOrderAt_ne_top_iff_forall.1 hf0
  obtain ⟨τ, hτ, ε, hε, hτe⟩ := exists_tau L
  have hlat := mem_lattice_iff_tau L hε hτe
  have hω : L.ω₂ ≠ 0 := period_ne_zero L
  obtain ⟨hp1, hpτ⟩ := scaled_periodic L hf.2 hε hτe
  have hgmer : Meromorphic (fun z => f (L.ω₂ * z)) := scaled_meromorphic hf.1 hω
  have hgord : ∀ z, meromorphicOrderAt (fun z => f (L.ω₂ * z)) z ≠ ⊤ := fun z => by
    rw [scaled_order hω]; exact hord _
  obtain ⟨a, b, hfd, hfin, hres, hordsum, m, n, hc⟩ :=
    rect_core hτ hgmer hp1 hpτ hgord
  set R : Set ℂ := (Ioo a (a + 1)) ×ℂ (Ioo b (b + τ.im)) with hR
  set B : Set ℂ := (fun z => L.ω₂ * z) '' R with hB
  set D := periodParallelogram L.ω₁ L.ω₂ z₀ with hDdef
  set Z : Set ℂ := {P | meromorphicOrderAt f P ≠ 0} with hZdef
  have hZ : ∀ P ∈ Z, ∀ ω ∈ L.lattice, P + ω ∈ Z := by
    intro P hP ω hω'
    show meromorphicOrderAt f (P + ω) ≠ 0
    rw [ord_add_lattice hf.2 hω']; exact hP
  have hAD : ∀ P ∈ Z, ∃! ω, ω ∈ L.lattice ∧ P + ω ∈ D := by
    intro P hP
    apply existsUnique_add_mem_periodParallelogram
    intro ω hω' hfr
    apply hP
    rw [← ord_add_lattice hf.2 hω']
    exact hD _ hfr
  have hBD : ∀ P ∈ Z, ∃! ω, ω ∈ L.lattice ∧ P + ω ∈ B := by
    intro P hP
    have hP' : meromorphicOrderAt (fun z => f (L.ω₂ * z)) (P / L.ω₂) ≠ 0 := by
      rw [scaled_order hω, mul_div_cancel₀ _ hω]; exact hP
    obtain ⟨mn, hmn, hmnu⟩ := hfd _ hP'
    have hmem : L.ω₂ * ((mn.1 : ℂ) + mn.2 * τ) ∈ L.lattice := (hlat _).2 ⟨mn.1, mn.2, rfl⟩
    refine ⟨L.ω₂ * ((mn.1 : ℂ) + mn.2 * τ), ⟨hmem, P / L.ω₂ + mn.1 + mn.2 * τ, hmn, ?_⟩, ?_⟩
    · field_simp; ring
    · rintro ω'' ⟨hω'', z, hz, hzeq⟩
      obtain ⟨m', n', hmn'⟩ := (hlat _).1 hω''
      have hz' : z = P / L.ω₂ + m' + n' * τ := by
        field_simp
        have hzeq' : L.ω₂ * z = P + ω'' := hzeq
        linear_combination hzeq' + hmn'
      have := hmnu (m', n') (by simpa [← hz'] using hz)
      have h1 : m' = mn.1 := congrArg Prod.fst this
      have h2 : n' = mn.2 := congrArg Prod.snd this
      rw [hmn', h1, h2]
  have hfinZ : (Z ∩ B).Finite := by
    refine (hfin.image (fun z => L.ω₂ * z)).subset ?_
    rintro P ⟨hPZ, z, hz, rfl⟩
    refine ⟨z, ⟨hz, ?_⟩, rfl⟩
    show meromorphicOrderAt (fun z => f (L.ω₂ * z)) z ≠ 0
    rw [scaled_order hω]; exact hPZ
  have hfinD : (Z ∩ D).Finite := (fd_finite hZ hAD hBD).2 hfinZ
  have hinj : Set.InjOn (fun z => L.ω₂ * z) R := fun x _ y _ h => mul_left_cancel₀ hω h
  have hordeq : ∀ z, ord f (L.ω₂ * z) = ord (fun z => f (L.ω₂ * z)) z := by
    intro z; unfold ord; rw [scaled_order hω]
  refine ⟨hfinD.subset (fun P hP => ⟨hP.2, hP.1⟩), ?_, ?_, ?_⟩
  · -- (a)
    rw [fd_finsum hZ hAD hBD (h := residue f) (fun P ω hω' => residue_add_lattice hf hω' P)
      (fun P hP => residue_eq_zero_of_nonneg_order (hf.1 P) (by
        have : meromorphicOrderAt f P = 0 := by simpa [hZdef] using hP
        rw [this]))]
    rw [hB, finsum_mem_image hinj]
    have : ∀ z, residue f (L.ω₂ * z) = L.ω₂ * residue (fun z => f (L.ω₂ * z)) z := by
      intro z
      rw [residue_comp_mul hω (hf.1 _)]
      field_simp
    simp_rw [this]
    rw [← mul_finsum_mem, hres, mul_zero]
  · -- (b)
    rw [fd_finsum hZ hAD hBD (h := ord f) (fun P ω hω' => ord_add_lattice' hf.2 hω' P)
      (fun P hP => by
        have : meromorphicOrderAt f P = 0 := by simpa [hZdef] using hP
        simp [ord, this])]
    rw [hB, finsum_mem_image hinj]
    simp_rw [hordeq]
    exact hordsum
  · -- (c)
    have hper : ∀ P, ∀ ω ∈ L.lattice, ord f (P + ω) = ord f P :=
      fun P ω hω' => ord_add_lattice' hf.2 hω' P
    have hsupp : ∀ P ∉ Z, ord f P = 0 := fun P hP => by
      have : meromorphicOrderAt f P = 0 := by simpa [hZdef] using hP
      simp [ord, this]
    have hw := fd_weighted hZ hAD hBD hfinD hper hsupp
    have hBsum : ∑ᶠ P ∈ B, (ord f P : ℂ) * P ∈ L.lattice := by
      rw [hB, finsum_mem_image hinj]
      simp_rw [hordeq]
      have : ∀ z, ((ord (fun z => f (L.ω₂ * z)) z : ℂ)) * (L.ω₂ * z) =
          L.ω₂ * ((ord (fun z => f (L.ω₂ * z)) z : ℂ) * z) := fun z => by ring
      simp_rw [this]
      rw [← mul_finsum_mem, hc]
      exact (hlat _).2 ⟨m, n, rfl⟩
    have := L.lattice.sub_mem hBsum hw
    simpa using this

/-! ### Corollary 2.2 -/

/-- Milne, proof of Corollary 2.2 (pdf p. 91): a holomorphic doubly periodic function is bounded,
hence constant by Liouville's theorem. -/
@[kb "milne2006ec" "Ch. III, proof of Cor. 2.2, holomorphic doubly periodic ⇒ constant, pdf p. 91"]
theorem isDoublyPeriodic_const_of_nonneg_order (L : PeriodPair) {f : ℂ → ℂ}
    (hf : IsDoublyPeriodic L.lattice f) (hpole : ∀ z, 0 ≤ meromorphicOrderAt f z) :
    ∃ c : ℂ, ∀ z, f =ᶠ[𝓝[≠] z] fun _ => c := by
  have hmer : MeromorphicOn f univ := (meromorphicOn_univ.2 hf.1)
  set F := toMeromorphicNFOn f univ with hFdef
  have hFan : ∀ z, AnalyticAt ℂ F z := by
    intro z
    have h := meromorphicNFOn_toMeromorphicNFOn f univ (mem_univ z)
    refine h.meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
    rw [meromorphicOrderAt_toMeromorphicNFOn hmer (mem_univ z)]
    exact hpole z
  have heq : ∀ z, F =ᶠ[𝓝[≠] z] f := fun z => hmer.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)
  have hFper : ∀ ω ∈ L.lattice, ∀ z, F (z + ω) = F z := by
    intro ω hω z
    have hG : ∀ᶠ w in 𝓝[≠] z, F (w + ω) = F w := by
      have h1 : ∀ᶠ w in 𝓝[≠] z, F (w + ω) = f (w + ω) := by
        have : Tendsto (fun w => w + ω) (𝓝[≠] z) (𝓝[≠] (z + ω)) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
          · exact (((continuous_id.add continuous_const : Continuous fun w : ℂ => w + ω).tendsto z)).mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with w hw
            simpa using hw
        exact this.eventually (heq (z + ω))
      filter_upwards [h1, heq z] with w h1 h2
      rw [h1, hf.2 ω hω w, h2]
    have c1 : ContinuousAt (fun w => F (w + ω)) z :=
      (hFan (z + ω)).continuousAt.comp (f := fun w => w + ω) (continuousAt_id.add continuousAt_const)
    have c2 := (hFan z).continuousAt
    exact tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] z)
      (c1.tendsto.mono_left nhdsWithin_le_nhds) (c2.tendsto.mono_left nhdsWithin_le_nhds) hG
  have hdiff : Differentiable ℂ F := fun z => (hFan z).differentiableAt
  have hcomp := IsZLattice.isCompact_range_of_periodic L.lattice F hdiff.continuous
    (fun z w hw => hFper w hw z)
  have hconst : ∀ z, F z = F 0 := fun z =>
    hdiff.apply_eq_apply_of_bounded hcomp.isBounded z 0
  refine ⟨F 0, fun z => ?_⟩
  filter_upwards [heq z] with w hw
  rw [← hw, hconst w]

/-- A function not locally constant has finite order everywhere. -/
lemma order_ne_top_of_not_const {f : ℂ → ℂ} (hf : Meromorphic f)
    (hnc : ¬ ∃ c : ℂ, ∀ z, f =ᶠ[𝓝[≠] z] fun _ => c) : ∀ z, meromorphicOrderAt f z ≠ ⊤ := by
  intro z hz
  apply hnc
  refine ⟨0, fun w => ?_⟩
  have hw : meromorphicOrderAt f w = ⊤ :=
    (meromorphicOn_univ.2 hf).meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ (mem_univ z) (mem_univ w) hz
  exact meromorphicOrderAt_eq_top_iff.1 hw

lemma order_eq_coe_ord {f : ℂ → ℂ} {P : ℂ} (h : meromorphicOrderAt f P ≠ ⊤) :
    meromorphicOrderAt f P = (ord f P : WithTop ℤ) := by
  unfold ord
  exact (WithTop.coe_untop₀_of_ne_top h).symm

/-- The residue at a simple pole is nonzero. -/
lemma residue_ne_zero_of_simple_pole {f : ℂ → ℂ} {P : ℂ} (hf : MeromorphicAt f P)
    (ho : meromorphicOrderAt f P = ((-1 : ℤ) : WithTop ℤ)) : residue f P ≠ 0 := by
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 ho
  have hd : AnalyticAt ℂ (dslope g P) P := by
    obtain ⟨ps, hps⟩ := hg
    exact (hps.has_fpower_series_dslope_fslope).analyticAt
  have := residue_eq_of_principalPart (f := f) (p := P) (n := 1) (c := fun _ => g P)
    (h := dslope g P) one_pos hd (by
      filter_upwards [hfg, self_mem_nhdsWithin] with z hz hz2
      have hz0 : z - P ≠ 0 := sub_ne_zero.mpr hz2
      rw [hz]
      have h2 := sub_smul_dslope g P z
      rw [smul_eq_mul] at h2
      simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, smul_eq_mul]
      have h3 : g z = g P + (z - P) * dslope g P z := by linear_combination -h2
      rw [zpow_neg_one, h3, mul_add, ← mul_assoc, inv_mul_cancel₀ hz0]
      ring)
  rw [this]
  exact hg0

/-- Corollary 2.2 (Milne, pdf p. 91): a nonconstant doubly periodic function has at least two
poles (or one double pole) modulo `Λ`. -/
@[kb "milne2006ec" "Ch. III, Cor. 2.2, pdf p. 91"]
theorem cor_2_2 (L : PeriodPair) {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (hnc : ¬ ∃ c : ℂ, ∀ z, f =ᶠ[𝓝[≠] z] fun _ => c) :
    (∃ P, ord f P ≤ -2) ∨ ∃ P Q, P - Q ∉ L.lattice ∧ ord f P < 0 ∧ ord f Q < 0 := by
  have hord := order_ne_top_of_not_const hf.1 hnc
  by_contra hcon
  push Not at hcon
  obtain ⟨h2, h3⟩ := hcon
  obtain ⟨z₀, hz₀⟩ := exists_generic_z0 L hf hord
  obtain ⟨hfin, hres, -, -⟩ := prop_2_1 L hf ⟨0, hord 0⟩ z₀ hz₀
  set D := periodParallelogram L.ω₁ L.ω₂ z₀ with hDdef
  -- poles
  have hpole_iff : ∀ P, ord f P < 0 ↔ meromorphicOrderAt f P < 0 := by
    intro P
    rw [order_eq_coe_ord (hord P)]
    exact_mod_cast Iff.rfl
  have hex : ∃ P₀, ord f P₀ < 0 := by
    by_contra hno
    push Not at hno
    apply hnc
    apply isDoublyPeriodic_const_of_nonneg_order L hf
    intro z
    have := hno z
    rw [order_eq_coe_ord (hord z)]
    exact_mod_cast this
  obtain ⟨P₀, hP₀⟩ := hex
  have hAD : ∀ P, meromorphicOrderAt f P ≠ 0 → ∃! ω, ω ∈ L.lattice ∧ P + ω ∈ D := by
    intro P hP
    apply existsUnique_add_mem_periodParallelogram
    intro ω hω' hfr
    apply hP
    rw [← ord_add_lattice hf.2 hω']
    exact hz₀ _ hfr
  have hne : ∀ P, ord f P < 0 → meromorphicOrderAt f P ≠ 0 := by
    intro P hP h0
    rw [(hpole_iff P)] at hP
    rw [h0] at hP
    exact lt_irrefl _ hP
  obtain ⟨ω₀, ⟨hω₀, hP⟩, -⟩ := hAD P₀ (hne P₀ hP₀)
  set P := P₀ + ω₀ with hPdef
  have hPord : ord f P < 0 := by
    have := ord_add_lattice hf.2 hω₀ P₀
    rw [hpole_iff] at hP₀ ⊢
    rw [hPdef, this]; exact hP₀
  -- uniqueness of the pole in D
  have huniq : ∀ Q ∈ D, ord f Q < 0 → Q = P := by
    intro Q hQ hQord
    have hPQ : P - Q ∈ L.lattice := by
      by_contra hn
      have := h3 P Q hn hPord
      omega
    obtain ⟨ω1, -, hω1⟩ := hAD Q (hne Q hQord)
    have e1 : (0 : ℂ) = ω1 := hω1 0 ⟨L.lattice.zero_mem, by simpa using hQ⟩
    have e2 : P - Q = ω1 := hω1 _ ⟨hPQ, by simpa using hP⟩
    have : P - Q = 0 := by rw [e2, ← e1]
    exact (sub_eq_zero.1 this).symm
  have hsum : ∑ᶠ (Q) (_ : Q ∈ D), residue f Q = residue f P := by
    have : ∑ᶠ (Q) (_ : Q ∈ D), residue f Q = ∑ᶠ (Q) (_ : Q ∈ ({P} : Set ℂ)), residue f Q := by
      apply finsum_mem_inter_support_eq'
      intro Q hQ
      constructor
      · intro hQD
        by_contra hQP
        apply hQ
        apply residue_eq_zero_of_nonneg_order (hf.1 Q)
        by_contra hneg
        push Not at hneg
        exact hQP (huniq Q hQD ((hpole_iff Q).2 hneg))
      · intro hQP
        rw [mem_singleton_iff] at hQP
        rw [hQP]; exact hP
    rw [this, finsum_mem_singleton]
  rw [hsum] at hres
  have h1 : ord f P = -1 := by
    have := h2 P
    omega
  apply residue_ne_zero_of_simple_pole (hf.1 P) _ hres
  rw [order_eq_coe_ord (hord P), h1]

/-! ### Proposition 2.7 -/

/-! #### Helpers for Proposition 2.7 (prefix `ev_`) -/

/-- Evaluation of a quotient of polynomials at a point where the denominator does not vanish. -/
lemma ev_eval_div (P Q : Polynomial ℂ) (hQ : Q ≠ 0) (a : ℂ) (ha : Q.eval a ≠ 0) :
    ((algebraMap (Polynomial ℂ) (RatFunc ℂ) P) / (algebraMap (Polynomial ℂ) (RatFunc ℂ) Q)).eval
      (RingHom.id ℂ) a = P.eval a / Q.eval a := by
  set x := (algebraMap (Polynomial ℂ) (RatFunc ℂ) P) / (algebraMap (Polynomial ℂ) (RatFunc ℂ) Q)
    with hx
  have hdv : x.denom ∣ Q := RatFunc.denom_div_dvd P Q
  have hden : (x.denom).eval a ≠ 0 := by
    intro h0
    apply ha
    obtain ⟨c, hc⟩ := hdv
    rw [hc, Polynomial.eval_mul, h0, zero_mul]
  have heq : x.num * Q = P * x.denom := (RatFunc.num_mul_eq_mul_denom_iff hQ).2 hx
  have := congrArg (Polynomial.eval a) heq
  simp only [Polynomial.eval_mul] at this
  unfold RatFunc.eval
  simp only [Polynomial.eval₂_id]
  field_simp
  linear_combination this

lemma ev_order_period (L : PeriodPair) {F : ℂ → ℂ} (hF : IsPeriodicFor L.lattice F) {ω : ℂ}
    (hω : ω ∈ L.lattice) (x : ℂ) :
    meromorphicOrderAt F (x + ω) = meromorphicOrderAt F x := by
  have h : (F ∘ (· + ω)) = F := funext (hF ω hω)
  have := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (f := F) (x := x) (c := ω)
  rw [h] at this
  exact this.symm

lemma ev_wp_sub_ne (L : PeriodPair) (c : ℂ) (x : ℂ) :
    ∀ᶠ z in 𝓝[≠] x, L.weierstrassP z - c ≠ 0 := by
  have hm : Meromorphic (fun z => L.weierstrassP z - c) :=
    L.meromorphic_weierstrassP.sub (Meromorphic.const c)
  have h0 : meromorphicOrderAt (fun z => L.weierstrassP z - c) 0 ≠ ⊤ := by
    rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm 0)]
    have : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖L.weierstrassP z‖ > ‖c‖ :=
      (tendsto_norm_atTop_iff_cobounded.mpr (wp_tendsto_cobounded L)).eventually
        (eventually_gt_atTop ‖c‖)
    filter_upwards [this] with z hz h
    have : L.weierstrassP z = c := sub_eq_zero.mp h
    rw [this] at hz
    exact lt_irrefl _ hz
  have := (hm.exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨0, h0⟩) x
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm x)).1 this

lemma ev_tendsto_neg : Tendsto (fun z : ℂ => -z) (𝓝[≠] 0) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_neg.tendsto' 0 0 neg_zero).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz

lemma ev_even_order {F h : ℂ → ℂ} (N : ℕ) (hF : ∀ z, F (-z) = F z) (hh : AnalyticAt ℂ h 0)
    (hh0 : h 0 ≠ 0)
    (heq : F =ᶠ[𝓝[≠] 0] fun z => (z - 0) ^ (-(N : ℤ)) • h z) : Even N := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hneg := ev_tendsto_neg.eventually heq
  have key : ∀ᶠ z in 𝓝[≠] (0 : ℂ), h (-z) = - h z := by
    filter_upwards [heq, hneg, self_mem_nhdsWithin] with z h1 h2 h3
    have hz : z ≠ 0 := h3
    simp only [smul_eq_mul, sub_zero, zpow_neg, zpow_natCast, sub_zero] at h1 h2
    rw [hF, h1, hodd.neg_pow] at h2
    have hzN : z ^ N ≠ 0 := pow_ne_zero N hz
    field_simp at h2
    linear_combination h2
  have t1 : Tendsto (fun z => h (-z)) (𝓝[≠] 0) (𝓝 (h 0)) :=
    ((hh.continuousAt.tendsto).comp (continuous_neg.tendsto' 0 0 neg_zero)).mono_left
      nhdsWithin_le_nhds
  have t2 : Tendsto (fun z => - h z) (𝓝[≠] 0) (𝓝 (-h 0)) :=
    (hh.continuousAt.tendsto.neg).mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique_of_eventuallyEq t1 t2 key
  apply hh0
  have h2 : (2 : ℂ) * h 0 = 0 := by linear_combination this
  simpa using h2

/-- An even `Λ`-periodic meromorphic function with no poles off `Λ` and a pole of order at most
`m` at `0` is a polynomial in `℘` (away from a discrete set). -/
lemma ev_poly (L : PeriodPair) : ∀ (m : ℕ) (F : ℂ → ℂ), Meromorphic F →
    IsPeriodicFor L.lattice F → (∀ z, F (-z) = F z) →
    (∀ z, z ∉ L.lattice → 0 ≤ meromorphicOrderAt F z) →
    (((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F 0) →
    ∃ P : Polynomial ℂ, ∀ x, F =ᶠ[𝓝[≠] x] fun z => P.eval (L.weierstrassP z) := by
  intro m
  induction m with
  | zero =>
    intro F hF hper hev hoff h0
    have hall : ∀ z, 0 ≤ meromorphicOrderAt F z := by
      intro z
      by_cases hz : z ∈ L.lattice
      · have := ev_order_period L hper hz 0
        rw [zero_add] at this
        rw [this]; simpa using h0
      · exact hoff z hz
    obtain ⟨c, hc⟩ := isDoublyPeriodic_const_of_nonneg_order L ⟨hF, hper⟩ hall
    exact ⟨Polynomial.C c, fun x => by simpa using hc x⟩
  | succ m ih =>
    intro F hF hper hev hoff h0
    by_cases hm : (((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F 0)
    · exact ih F hF hper hev hoff hm
    · push Not at hm
      have hne : meromorphicOrderAt F 0 ≠ ⊤ := ne_top_of_lt hm
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
      rw [← hn] at hm h0
      have h1 : n < -(m : ℤ) := WithTop.coe_lt_coe.1 hm
      have h2 : -((m + 1 : ℕ) : ℤ) ≤ n := WithTop.coe_le_coe.1 h0
      have hn' : n = -((m + 1 : ℕ) : ℤ) := by push_cast at h2 ⊢; omega
      obtain ⟨h, hh, hh0, hFh⟩ := (meromorphicOrderAt_eq_int_iff (hF 0)).1 hn.symm
      subst hn'
      obtain ⟨k, hk⟩ := ev_even_order (m + 1) hev hh hh0 hFh
      have hord2 : meromorphicOrderAt L.weierstrassP 0 = ((-2 : ℤ) : WithTop ℤ) := by
        rw [L.order_weierstrassP 0 (zero_mem _)]; rfl
      obtain ⟨u, hu, hu0, hwp⟩ :=
        (meromorphicOrderAt_eq_int_iff (L.meromorphic_weierstrassP 0)).1 hord2
      set c : ℂ := h 0 / (u 0) ^ k with hc
      let G : ℂ → ℂ := fun z => F z + -(c * L.weierstrassP z ^ k)
      have hw : AnalyticAt ℂ (fun z => h z - c * u z ^ k) 0 := by fun_prop
      have hw0 : h 0 - c * u 0 ^ k = 0 := by
        rw [hc, div_mul_cancel₀ _ (pow_ne_zero k hu0), sub_self]
      have hGeq : G =ᶠ[𝓝[≠] 0] fun z => (z - 0) ^ (-((m + 1 : ℕ) : ℤ)) * (h z - c * u z ^ k) := by
        filter_upwards [hFh, hwp, self_mem_nhdsWithin] with z h1 h2 h3
        have hz : z ≠ 0 := h3
        simp only [smul_eq_mul, sub_zero] at h1 h2 ⊢
        have hexp : (-((m + 1 : ℕ) : ℤ)) = (-2) * (k : ℤ) := by rw [hk]; push_cast; ring
        have hp : (z ^ (-2 : ℤ)) ^ k = z ^ ((-2 : ℤ) * k) := by
          rw [← zpow_natCast, ← zpow_mul]
        simp only [G]
        rw [h1, h2, mul_pow, hp, hexp]
        ring
      have hordG : (((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt G 0) := by
        rw [meromorphicOrderAt_congr hGeq]
        have hmz : MeromorphicAt (fun z : ℂ => (z - 0) ^ (-((m + 1 : ℕ) : ℤ))) 0 := by fun_prop
        have hmul := meromorphicOrderAt_mul hmz hw.meromorphicAt
        refine le_of_le_of_eq ?_ hmul.symm
        have hz1 : meromorphicOrderAt (fun z : ℂ => (z - 0) ^ (-((m + 1 : ℕ) : ℤ))) 0 =
            ((-((m + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
          have := @meromorphicOrderAt_zpow_id_sub_const ℂ _ (0 : ℂ) (-((m + 1 : ℕ) : ℤ))
          exact this
        rw [hz1]
        have hwo : (1 : WithTop ℤ) ≤ meromorphicOrderAt (fun z => h z - c * u z ^ k) 0 := by
          rw [hw.meromorphicOrderAt_eq]
          have hne : analyticOrderAt (fun z => h z - c * u z ^ k) 0 ≠ 0 := by
            rw [Ne, analyticOrderAt_eq_zero]; push Not; exact ⟨hw, hw0⟩
          generalize analyticOrderAt (fun z => h z - c * u z ^ k) 0 = a at hne
          induction a using ENat.recTopCoe with
          | top => simp
          | coe n =>
            have : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by simpa using hne)
            show ((1 : ℤ) : WithTop ℤ) ≤ ((n : ℤ) : WithTop ℤ)
            exact WithTop.coe_le_coe.2 (by exact_mod_cast this)
        calc (((-(m : ℤ) : ℤ) : WithTop ℤ)) = ((-((m + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) + 1 := by
              rw [← WithTop.coe_one, ← WithTop.coe_add]; congr 1; push_cast; ring
          _ ≤ _ := add_le_add_right hwo _
      have hGm : Meromorphic G := by
        have := L.meromorphic_weierstrassP
        fun_prop
      have hGper : IsPeriodicFor L.lattice G := by
        intro ω hω z
        simp only [G]
        rw [hper ω hω z, L.weierstrassP_add_coe z ⟨ω, hω⟩]
      have hGev : ∀ z, G (-z) = G z := by
        intro z
        simp only [G]
        rw [hev, L.weierstrassP_neg]
      have hGoff : ∀ z, z ∉ L.lattice → 0 ≤ meromorphicOrderAt G z := by
        intro z hz
        have han : AnalyticAt ℂ (fun z => -(c * L.weierstrassP z ^ k)) z := by
          have := L.analyticOnNhd_weierstrassP z (by simpa using hz)
          fun_prop
        refine le_trans ?_ (meromorphicOrderAt_add (hF z) han.meromorphicAt)
        exact le_min (hoff z hz) han.meromorphicOrderAt_nonneg
      obtain ⟨P, hP⟩ := ih G hGm hGper hGev hGoff hordG
      refine ⟨P + Polynomial.C c * Polynomial.X ^ k, fun x => ?_⟩
      filter_upwards [hP x] with z hz
      simp only [G] at hz
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      linear_combination hz

lemma ev_order_ge_one {w : ℂ → ℂ} {x : ℂ} (hw : AnalyticAt ℂ w x) (hw0 : w x = 0) :
    (1 : WithTop ℤ) ≤ meromorphicOrderAt w x := by
  rw [hw.meromorphicOrderAt_eq]
  have hne : analyticOrderAt w x ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]; push Not; exact ⟨hw, hw0⟩
  generalize analyticOrderAt w x = a at hne
  induction a using ENat.recTopCoe with
  | top => simp
  | coe n =>
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by simpa using hne)
    show ((1 : ℤ) : WithTop ℤ) ≤ ((n : ℤ) : WithTop ℤ)
    exact WithTop.coe_le_coe.2 (by exact_mod_cast this)

lemma ev_order_pow_ge {B : ℂ → ℂ} {x : ℂ} (hB : AnalyticAt ℂ B x) (hB0 : B x = 0) (e : ℕ) :
    ((e : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun z => B z ^ e) x := by
  have h1 := ev_order_ge_one hB hB0
  induction e with
  | zero =>
    have : AnalyticAt ℂ (fun z => B z ^ 0) x := by simpa using (analyticAt_const (v := (1 : ℂ)))
    simpa using this.meromorphicOrderAt_nonneg
  | succ e ih =>
    have hm : meromorphicOrderAt ((fun z => B z ^ e) * B) x =
        meromorphicOrderAt (fun z => B z ^ e) x + meromorphicOrderAt B x :=
      meromorphicOrderAt_mul (hB.pow e).meromorphicAt hB.meromorphicAt
    have hfe : (fun z => B z ^ (e + 1)) = (fun z => B z ^ e) * B := by
      funext z; simp [pow_succ]
    rw [hfe, hm]
    calc (((e + 1 : ℕ) : ℤ) : WithTop ℤ) = ((e : ℤ) : WithTop ℤ) + 1 := by norm_cast
      _ ≤ _ := add_le_add ih h1

lemma ev_exists_m (o : WithTop ℤ) : ∃ m : ℕ, ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ o := by
  induction o using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe n => exact ⟨(-n).toNat, WithTop.coe_le_coe.2 (by omega)⟩

/-- An even doubly periodic function of nowhere-infinite order is a rational function of `℘`
(Milne, pdf p. 95): multiply by `∏ (℘ - ℘ Q)^{N_Q}` over the pole orbits `Q` to remove the
poles off `Λ`, apply `ev_poly`, and divide. -/
lemma ev_even_core (L : PeriodPair) {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (heven : ∀ z, f (-z) = f z) (hord : ∀ z, meromorphicOrderAt f z ≠ ⊤) :
    ∃ R : RatFunc ℂ, ∀ x, f =ᶠ[𝓝[≠] x] fun z => R.eval (RingHom.id ℂ) (L.weierstrassP z) := by
  classical
  obtain ⟨z₀, hz₀⟩ := exists_generic_z0 L hf hord
  obtain ⟨hfin, -⟩ := prop_2_1 L hf ⟨0, hord 0⟩ z₀ hz₀
  set T := hfin.toFinset with hT
  let e : ℂ → ℕ := fun Q => (-(ord f Q)).toNat
  let A : ℂ → ℂ → ℂ := fun Q z => (L.weierstrassP z - L.weierstrassP Q) ^ e Q
  let F : ℂ → ℂ := fun z => f z * ∏ Q ∈ T, A Q z
  have hAan : ∀ Q x, x ∉ L.lattice → AnalyticAt ℂ (A Q) x := by
    intro Q x hx
    have := L.analyticOnNhd_weierstrassP x (by simpa using hx)
    simp only [A]; fun_prop
  have hPan : ∀ S : Finset ℂ, ∀ x, x ∉ L.lattice →
      AnalyticAt ℂ (fun z => ∏ Q ∈ S, A Q z) x :=
    fun S x hx => Finset.analyticAt_fun_prod S (fun Q _ => hAan Q x hx)
  have hAm : ∀ Q x, MeromorphicAt (A Q) x := by
    intro Q x
    have := L.meromorphic_weierstrassP x
    simp only [A]; fun_prop
  have hFm : Meromorphic F := fun x =>
    (hf.1 x).mul (MeromorphicAt.fun_prod fun Q _ => hAm Q x)
  have hFper : IsPeriodicFor L.lattice F := by
    intro ω hω z
    simp only [F, A]
    rw [hf.2 ω hω z]
    congr 1
    apply Finset.prod_congr rfl
    intro Q _
    rw [L.weierstrassP_add_coe z ⟨ω, hω⟩]
  have hFev : ∀ z, F (-z) = F z := by
    intro z
    simp only [F, A]
    rw [heven z, L.weierstrassP_neg]
  have hoff : ∀ x, x ∉ L.lattice → 0 ≤ meromorphicOrderAt F x := by
    intro x hx
    have hfx := hf.1 x
    by_cases hneg : meromorphicOrderAt f x < 0
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hord x)
      have hn0 : n < 0 := by rw [← hn] at hneg; exact_mod_cast hneg
      obtain ⟨ω, ⟨hωΛ, hωD⟩, -⟩ := existsUnique_add_mem_periodParallelogram L z₀ x (by
          intro ω hω hfr
          have h1 := hz₀ _ hfr
          rw [ev_order_period L hf.2 hω] at h1
          rw [h1] at hneg; exact lt_irrefl _ hneg)
      have hQord : meromorphicOrderAt f (x + ω) = ↑n := by
        rw [ev_order_period L hf.2 hωΛ, hn]
      have hQT : x + ω ∈ T := by
        rw [hT, Set.Finite.mem_toFinset]
        refine ⟨hωD, ?_⟩
        rw [hQord]
        exact_mod_cast hn0.ne
      have hordQ : ord f (x + ω) = n := by simp [ord, hQord]
      have heQ : (e (x + ω) : ℤ) = -n := by
        simp only [e, hordQ]; omega
      have hBx : L.weierstrassP x - L.weierstrassP (x + ω) = 0 := by
        rw [L.weierstrassP_add_coe x ⟨ω, hωΛ⟩, sub_self]
      have hBan : AnalyticAt ℂ (fun z => L.weierstrassP z - L.weierstrassP (x + ω)) x := by
        have := L.analyticOnNhd_weierstrassP x (by simpa using hx)
        fun_prop
      have hA := ev_order_pow_ge hBan hBx (e (x + ω))
      have hF' : F = (fun z => f z * A (x + ω) z) * fun z => ∏ R ∈ T.erase (x + ω), A R z := by
        funext z
        simp only [F, Pi.mul_apply]
        rw [← Finset.mul_prod_erase T (fun R => A R z) hQT]
        ring
      rw [hF']
      have h1 : 0 ≤ meromorphicOrderAt (fun z => f z * A (x + ω) z) x := by
        have hm : meromorphicOrderAt (f * A (x + ω)) x =
            meromorphicOrderAt f x + meromorphicOrderAt (A (x + ω)) x :=
          meromorphicOrderAt_mul hfx (hAm _ x)
        show 0 ≤ meromorphicOrderAt (f * A (x + ω)) x
        rw [hm, ← hn]
        have hA' : ((-n : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (A (x + ω)) x := by
          rw [← heQ]; exact hA
        calc (0 : WithTop ℤ) = ((n : ℤ) : WithTop ℤ) + ((-n : ℤ) : WithTop ℤ) := by
              rw [← WithTop.coe_add]; simp
          _ ≤ _ := add_le_add_right hA' _
      have h2 : 0 ≤ meromorphicOrderAt (fun z => ∏ R ∈ T.erase (x + ω), A R z) x :=
        (hPan _ x hx).meromorphicOrderAt_nonneg
      have hm : meromorphicOrderAt ((fun z => f z * A (x + ω) z) *
          fun z => ∏ R ∈ T.erase (x + ω), A R z) x =
          meromorphicOrderAt (fun z => f z * A (x + ω) z) x +
          meromorphicOrderAt (fun z => ∏ R ∈ T.erase (x + ω), A R z) x :=
        meromorphicOrderAt_mul (hfx.mul (hAm _ x)) (MeromorphicAt.fun_prod fun R _ => hAm R x)
      rw [hm]
      exact add_nonneg h1 h2
    · push Not at hneg
      have hm : meromorphicOrderAt (f * fun z => ∏ Q ∈ T, A Q z) x =
          meromorphicOrderAt f x + meromorphicOrderAt (fun z => ∏ Q ∈ T, A Q z) x :=
        meromorphicOrderAt_mul hfx (MeromorphicAt.fun_prod fun R _ => hAm R x)
      show 0 ≤ meromorphicOrderAt (f * fun z => ∏ Q ∈ T, A Q z) x
      rw [hm]
      exact add_nonneg hneg (hPan _ x hx).meromorphicOrderAt_nonneg
  obtain ⟨m, hm⟩ := ev_exists_m (meromorphicOrderAt F 0)
  obtain ⟨P, hP⟩ := ev_poly L m F hFm hFper hFev hoff hm
  let Qp : Polynomial ℂ := ∏ Q ∈ T, (Polynomial.X - Polynomial.C (L.weierstrassP Q)) ^ e Q
  have hQp : Qp ≠ 0 := by
    apply Finset.prod_ne_zero_iff.2
    intro Q _
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  have hQev : ∀ z, Qp.eval (L.weierstrassP z) = ∏ Q ∈ T, A Q z := by
    intro z
    simp [Qp, A, Polynomial.eval_prod]
  refine ⟨(algebraMap (Polynomial ℂ) (RatFunc ℂ) P) / (algebraMap (Polynomial ℂ) (RatFunc ℂ) Qp),
    fun x => ?_⟩
  have hne : ∀ᶠ z in 𝓝[≠] x, ∀ Q ∈ T, L.weierstrassP z - L.weierstrassP Q ≠ 0 :=
    (Filter.eventually_all_finset T).2 fun Q _ => ev_wp_sub_ne L _ x
  filter_upwards [hP x, hne] with z hz hz'
  have hQne : Qp.eval (L.weierstrassP z) ≠ 0 := by
    rw [hQev]
    apply Finset.prod_ne_zero_iff.2
    intro Q hQ
    exact pow_ne_zero _ (hz' Q hQ)
  rw [ev_eval_div P Qp hQp _ hQne, ← hz]
  simp only [F]
  rw [← hQev]
  field_simp

lemma ev_even_codisc (L : PeriodPair) {f : ℂ → ℂ}
    (hf : IsDoublyPeriodic L.lattice f) (heven : ∀ z, f (-z) = f z) :
    ∃ R : RatFunc ℂ, ∀ᶠ z in codiscrete ℂ, f z = R.eval (RingHom.id ℂ) (L.weierstrassP z) := by
  by_cases hord : ∀ z, meromorphicOrderAt f z ≠ ⊤
  · obtain ⟨R, hR⟩ := ev_even_core L hf heven hord
    exact ⟨R, eventually_codiscrete_iff_forall_eventually_nhdsNE.2 hR⟩
  · push Not at hord
    obtain ⟨z, hz⟩ := hord
    have hall := hf.1.exists_meromorphicOrderAt_eq_top_iff_forall.1 ⟨z, hz⟩
    refine ⟨0, eventually_codiscrete_iff_forall_eventually_nhdsNE.2 fun x => ?_⟩
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 (hall x)] with w hw
    simp [hw]

lemma ev_derivWP_codisc (L : PeriodPair) : ∀ᶠ z in codiscrete ℂ, L.derivWeierstrassP z ≠ 0 := by
  have hm : Meromorphic L.derivWeierstrassP := L.meromorphic_derivWeierstrassP
  have h0 : meromorphicOrderAt L.derivWeierstrassP 0 ≠ ⊤ :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm 0)).2 (eventually_derivWP_ne_zero L)
  have hall := hm.exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨0, h0⟩
  refine eventually_codiscrete_iff_forall_eventually_nhdsNE.2 fun x => ?_
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm x)).1 (hall x)

lemma ev_prop_2_7 (L : PeriodPair) {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f) :
    ∃ R S : RatFunc ℂ, ∀ᶠ z in codiscrete ℂ,
      f z = R.eval (RingHom.id ℂ) (L.weierstrassP z) +
        L.derivWeierstrassP z * S.eval (RingHom.id ℂ) (L.weierstrassP z) := by
  have hfneg : Meromorphic (fun z => f (-z)) := fun x =>
    (hf.1 (-x)).comp_analyticAt (g := fun z => -z) (by fun_prop)
  have hfnegper : IsPeriodicFor L.lattice (fun z => f (-z)) := by
    intro ω hω z
    have : -(z + ω) = -z + (-ω) := by ring
    simp only [this]
    exact hf.2 (-ω) (neg_mem hω) (-z)
  have hdp := L.meromorphic_derivWeierstrassP
  have hf₁ : IsDoublyPeriodic L.lattice (fun z => (f z + f (-z)) / 2) := by
    refine ⟨fun x => ((hf.1 x).add (hfneg x)).div (MeromorphicAt.const _ x), ?_⟩
    intro ω hω z
    simp only [hf.2 ω hω z, hfnegper ω hω z]
  have hf₂ : IsDoublyPeriodic L.lattice
      (fun z => (f z - f (-z)) / (2 * L.derivWeierstrassP z)) := by
    refine ⟨fun x => ((hf.1 x).sub (hfneg x)).div ((MeromorphicAt.const _ x).mul (hdp x)), ?_⟩
    intro ω hω z
    simp only [hf.2 ω hω z, hfnegper ω hω z, L.derivWeierstrassP_add_coe z ⟨ω, hω⟩]
  obtain ⟨R, hR⟩ := ev_even_codisc L hf₁ (fun z => by simp [add_comm])
  obtain ⟨S, hS⟩ := ev_even_codisc L hf₂ (fun z => by
    simp only [neg_neg, L.derivWeierstrassP_neg]
    rw [show f (-z) - f z = -(f z - f (-z)) by ring, mul_neg, neg_div_neg_eq])
  refine ⟨R, S, ?_⟩
  filter_upwards [hR, hS, ev_derivWP_codisc L] with z h1 h2 h3
  have h4 : f z = (f z + f (-z)) / 2 + L.derivWeierstrassP z * ((f z - f (-z)) /
      (2 * L.derivWeierstrassP z)) := by
    field_simp
    ring
  rw [h4, h1, h2]

/-- Proposition 2.7 (Milne, pdf p. 95): every doubly periodic meromorphic function is a rational
function of `℘` and `℘'`; in the form of Milne's proof, `f = R(℘) + ℘' S(℘)` with `R, S ∈ ℂ(X)`
(away from a discrete set).  The converse inclusion `ℂ(℘, ℘') ⊆ {doubly periodic}` is Mathlib's
`PeriodPair.periodic_weierstrassP`, `PeriodPair.periodic_derivWeierstrassP`. -/
@[kb "milne2006ec" "Ch. III, Prop. 2.7, pdf p. 95"]
theorem prop_2_7 (L : PeriodPair) {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f) :
    ∃ R S : RatFunc ℂ, ∀ᶠ z in codiscrete ℂ,
      f z = R.eval (RingHom.id ℂ) (L.weierstrassP z) +
        L.derivWeierstrassP z * S.eval (RingHom.id ℂ) (L.weierstrassP z) :=
  ev_prop_2_7 L hf

/-- Milne, proof of Proposition 2.7 (pdf p. 95), first step: an even doubly periodic function is
a rational function of `℘`. -/
@[kb "milne2006ec" "Ch. III, proof of Prop. 2.7, even functions lie in C(℘), pdf p. 95"]
theorem even_mem_ratFunc_weierstrassP (L : PeriodPair) {f : ℂ → ℂ}
    (hf : IsDoublyPeriodic L.lattice f) (heven : ∀ z, f (-z) = f z) :
    ∃ R : RatFunc ℂ, ∀ᶠ z in codiscrete ℂ, f z = R.eval (RingHom.id ℂ) (L.weierstrassP z) :=
  ev_even_codisc L hf heven

/-! ### `ℂ[x, y] ≅ ℂ[℘, ℘']` (pdf pp. 96–97) -/

/-- Milne (pdf p. 96): `℘` is transcendental over `ℂ`: no nonzero polynomial vanishes on all
values `℘(z)`, `z ∉ Λ`. -/
@[kb "milne2006ec" "Ch. III, §2, ℘ is transcendental over C, pdf p. 96"]
theorem weierstrassP_transcendental (L : PeriodPair) (R : Polynomial ℂ)
    (hR : ∀ z ∉ L.lattice, R.eval (L.weierstrassP z) = 0) : R = 0 := by
  exact transc_aux L R ((eventually_not_mem_lattice L).mono hR)

/-- The polynomial `Y² - 4X³ + g₄X + g₆ ∈ ℂ[X][Y]` (Milne, pdf p. 96). -/
noncomputable def weierstrassPolynomial (L : PeriodPair) : Polynomial (Polynomial ℂ) :=
  Polynomial.X ^ 2 - Polynomial.C (4 * Polynomial.X ^ 3 - Polynomial.C L.g₂ * Polynomial.X -
    Polynomial.C L.g₃)

/-- Milne (pdf p. 96): `(X, Y) ↦ (℘, ℘')` induces an isomorphism
`ℂ[X, Y]/(Y² - 4X³ + g₄X + g₆) ≅ ℂ[℘, ℘']`: a polynomial `g(X, Y)` satisfies `g(℘, ℘') = 0` if
and only if it is divisible by `Y² - 4X³ + g₄X + g₆`.  (Polynomials in `X, Y` are
`Polynomial (Polynomial ℂ)`, the outer variable being `Y`.) -/
@[kb "milne2006ec" "Ch. III, §2, C[x,y] ≅ C[℘,℘'], pdf p. 96"]
theorem eval_weierstrassP_eq_zero_iff (L : PeriodPair) (g : Polynomial (Polynomial ℂ)) :
    (∀ z ∉ L.lattice, g.evalEval (L.weierstrassP z) (L.derivWeierstrassP z) = 0) ↔
      weierstrassPolynomial L ∣ g := by
  have hW : ∀ z ∉ L.lattice,
      (weierstrassPolynomial L).evalEval (L.weierstrassP z) (L.derivWeierstrassP z) = 0 := by
    intro z hz
    have := L.derivWeierstrassP_sq z hz
    simp only [weierstrassPolynomial, Polynomial.evalEval_sub, Polynomial.evalEval_pow,
      Polynomial.evalEval_X, Polynomial.evalEval_C, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
    rw [this]; ring
  have hmonic : (weierstrassPolynomial L).Monic := by
    unfold weierstrassPolynomial
    exact Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hdeg : (weierstrassPolynomial L).natDegree = 2 := by
    unfold weierstrassPolynomial
    exact Polynomial.natDegree_X_pow_sub_C
  constructor
  · intro hg
    set r := g %ₘ weierstrassPolynomial L with hr
    have hdecomp := Polynomial.modByMonic_add_div g (weierstrassPolynomial L)
    have hr_eval : ∀ z ∉ L.lattice, r.evalEval (L.weierstrassP z) (L.derivWeierstrassP z) = 0 := by
      intro z hz
      have := hg z hz
      rw [← hdecomp, Polynomial.evalEval_add, Polynomial.evalEval_mul, hW z hz, zero_mul,
        add_zero] at this
      exact this
    have hrdeg : r.natDegree ≤ 1 := by
      have h : r.natDegree < (weierstrassPolynomial L).natDegree :=
        Polynomial.natDegree_modByMonic_lt g hmonic (by intro h1; rw [h1] at hdeg; simp at hdeg)
      omega
    have hr' := Polynomial.eq_X_add_C_of_natDegree_le_one hrdeg
    set b := r.coeff 1
    set a := r.coeff 0
    have key : ∀ z ∉ L.lattice, b.eval (L.weierstrassP z) * L.derivWeierstrassP z +
        a.eval (L.weierstrassP z) = 0 := by
      intro z hz
      have := hr_eval z hz
      rw [hr'] at this
      simpa [Polynomial.evalEval] using this
    have ha : a = 0 := by
      apply weierstrassP_transcendental L
      intro z hz
      have h1 := key z hz
      have h2 := key (-z) (by simpa using hz)
      rw [L.weierstrassP_neg, L.derivWeierstrassP_neg] at h2
      have : 2 * a.eval (L.weierstrassP z) = 0 := by linear_combination h1 + h2
      simpa using this
    have hb : b = 0 := by
      apply transc_aux L
      filter_upwards [eventually_not_mem_lattice L, eventually_derivWP_ne_zero L] with z hz hz'
      have := key z hz
      rw [ha] at this
      simp at this
      rcases this with h | h
      · exact h
      · exact absurd h hz'
    have : r = 0 := by rw [hr', ha, hb]; simp
    rw [← Polynomial.modByMonic_eq_zero_iff_dvd hmonic]
    exact this
  · rintro ⟨q, rfl⟩ z hz
    rw [Polynomial.evalEval_mul, hW z hz, zero_mul]

end NumberFieldKB.MilneEC.III
