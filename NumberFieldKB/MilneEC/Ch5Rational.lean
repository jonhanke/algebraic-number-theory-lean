import NumberFieldKB.MilneEC.Ch5JFunction
import Mathlib.Computability.Reduce
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Milne, *Elliptic Curves*, Chapter V §2: the meromorphic functions on $X_0(1)$ are $\mathbb C(j)$

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, Proposition 2.2, last sentence (pdf p. 191).
Proved here, so the named statement `Prop2_2Rational` holds: a modular function for $\mathrm{SL}_2(\mathbb Z)$ has
finitely many poles modulo $\mathrm{SL}_2(\mathbb Z)$; multiplying by a polynomial in $j$ vanishing at them gives a
holomorphic modular function, which is a polynomial in $j$
(`holomorphic_modularFunction_eq_polynomial_jFun`).
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Matrix.SpecialLinearGroup
open scoped MatrixGroups Real Manifold

namespace NumberFieldKB.MilneEC.V

/-- A function `g` on the upper half plane has a *removable singularity* at `z` if on a punctured neighbourhood
it agrees with a function holomorphic near `z`. -/
def Removable (g : ℍ → ℂ) (z : ℍ) : Prop :=
  ∃ h : ℍ → ℂ, (∀ᶠ w in 𝓝 z, MDiffAt h w) ∧ g =ᶠ[𝓝[≠] z] h

/-- A function holomorphic near `z` has a removable singularity at `z`. -/
lemma Removable.of_eventually_mdiffAt {g : ℍ → ℂ} {z : ℍ} (h : ∀ᶠ w in 𝓝 z, MDiffAt g w) :
    Removable g z :=
  ⟨g, h, EventuallyEq.rfl⟩

/-- Multiplying by a function holomorphic near `z` preserves removable singularities. -/
lemma Removable.mul {a g : ℍ → ℂ} {z : ℍ} (ha : ∀ᶠ w in 𝓝 z, MDiffAt a w) (hg : Removable g z) :
    Removable (fun w => a w * g w) z := by
  obtain ⟨h, hh, he⟩ := hg
  exact ⟨fun w => a w * h w, by filter_upwards [ha, hh] with w h1 h2 using h1.mul h2,
    he.mono fun w hw => by simp [hw]⟩

/-- Each element of $\mathrm{SL}_2(\mathbb Z)$ acts holomorphically on $\mathbb H$. -/
lemma mdiffAt_smul_SL (γ : SL(2, ℤ)) (z : ℍ) : MDiffAt (fun w : ℍ => γ • w) z := by
  have := mdifferentiable_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ γ) (by simp)
  exact this z

/-- The action of $\mathrm{SL}_2(\mathbb Z)$ on $\mathbb H$ is continuous. -/
instance instContinuousConstSMulSL : ContinuousConstSMul SL(2, ℤ) ℍ :=
  ⟨fun γ => MDifferentiable.continuous (fun z => mdiffAt_smul_SL γ z)⟩

/-- For an $\mathrm{SL}_2(\mathbb Z)$-invariant function, removability at `z` implies removability at `γ • z`. -/
lemma Removable.smul {g : ℍ → ℂ} (hg : ∀ (γ : SL(2, ℤ)) (z : ℍ), g (γ • z) = g z) {z : ℍ}
    (h : Removable g z) (γ : SL(2, ℤ)) : Removable g (γ • z) := by
  obtain ⟨h, hh, he⟩ := h
  refine ⟨fun w => h (γ⁻¹ • w), ?_, ?_⟩
  · have h1 : ∀ᶠ w in 𝓝 (γ⁻¹ • γ • z), MDiffAt h w := by rwa [inv_smul_smul]
    have h2 : Tendsto (fun w : ℍ => γ⁻¹ • w) (𝓝 (γ • z)) (𝓝 (γ⁻¹ • γ • z)) :=
      (continuous_const_smul γ⁻¹).continuousAt.tendsto
    filter_upwards [h2.eventually h1] with w hw
    exact hw.comp w (mdiffAt_smul_SL γ⁻¹ w)
  · have e : 𝓝[≠] (γ • z) = map (fun w : ℍ => γ • w) (𝓝[≠] z) :=
      ((Homeomorph.smul γ).map_punctured_nhds_eq z).symm
    rw [e, EventuallyEq, eventually_map]
    filter_upwards [he] with w hw
    simp only [inv_smul_smul]
    rw [hg, hw]

/-- The limit along punctured neighbourhoods of a function agreeing there with a function continuous at `z`. -/
lemma limUnder_eq_of_eventuallyEq {g h : ℍ → ℂ} {z : ℍ} (he : g =ᶠ[𝓝[≠] z] h)
    (hc : ContinuousAt h z) : limUnder (𝓝[≠] z) g = h z :=
  (Tendsto.congr' he.symm (hc.tendsto.mono_left nhdsWithin_le_nhds)).limUnder_eq

/-- An invariant function with removable singularities everywhere equals, off a discrete set, an invariant
holomorphic function (the limit along punctured neighbourhoods). -/
lemma Removable.exists_extension {g : ℍ → ℂ} (hg : ∀ z, Removable g z)
    (hinv : ∀ (γ : SL(2, ℤ)) (z : ℍ), g (γ • z) = g z) :
    ∃ g' : ℍ → ℂ, MDiff g' ∧ (∀ (γ : SL(2, ℤ)) (z : ℍ), g' (γ • z) = g' z) ∧
      (∀ z, g =ᶠ[𝓝[≠] z] g') ∧ (∀ z, (∀ᶠ w in 𝓝 z, MDiffAt g w) → g' z = g z) := by
  have key : ∀ z, ∃ h : ℍ → ℂ, (∀ᶠ w in 𝓝 z, MDiffAt h w) ∧ g =ᶠ[𝓝[≠] z] h ∧
      (fun w => limUnder (𝓝[≠] w) g) =ᶠ[𝓝 z] h := by
    intro z
    obtain ⟨h, hh, he⟩ := hg z
    refine ⟨h, hh, he, ?_⟩
    have h1 : ∀ᶠ w in 𝓝 z, w ≠ z → g w = h w := eventually_nhdsWithin_iff.mp he
    have h2 := h1.eventually_nhds
    filter_upwards [h2, hh, h1] with w hw hhw _
    by_cases hwz : w = z
    · subst hwz
      exact limUnder_eq_of_eventuallyEq he hhw.continuousAt
    · have h3 : ∀ᶠ y in 𝓝 w, y ≠ z := isOpen_ne.mem_nhds hwz
      have : g =ᶠ[𝓝[≠] w] h := by
        refine Filter.EventuallyEq.filter_mono (l := 𝓝 w) ?_ nhdsWithin_le_nhds
        filter_upwards [hw, h3] with y h4 h5 using h4 h5
      exact limUnder_eq_of_eventuallyEq this hhw.continuousAt
  refine ⟨fun w => limUnder (𝓝[≠] w) g, ?_, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨h, hh, -, he⟩ := key z
    exact (hh.self_of_nhds.congr_of_eventuallyEq he)
  · intro γ z
    have e : 𝓝[≠] (γ • z) = map (fun w : ℍ => γ • w) (𝓝[≠] z) :=
      ((Homeomorph.smul γ).map_punctured_nhds_eq z).symm
    simp only [limUnder, e, map_map]
    congr 2
    funext w
    exact hinv γ w
  · intro z
    obtain ⟨h, hh, h1, he⟩ := key z
    exact h1.trans (he.filter_mono nhdsWithin_le_nhds).symm
  · intro z hz
    exact limUnder_eq_of_eventuallyEq EventuallyEq.rfl hz.self_of_nhds.continuousAt

local notation "Δ" => ModularForm.discriminant

/-- A modular function has no poles (and no junk values) high in the upper half plane. -/
lemma exists_im_gt_mdiffAt {f : ℍ → ℂ} (hmod : IsModularFunction ⊤ f) :
    ∃ Y : ℝ, ∀ z : ℍ, Y < z.im → ∀ᶠ w in 𝓝 z, MDiffAt f w := by
  have hmer : IsMeromorphicAtImInfty f := by simpa using hmod.meromorphic_cusps 1
  obtain ⟨h, hh, hper, hm⟩ := hmer
  have hev := eventually_nhdsWithin_iff.mp hm.eventually_analyticAt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hq : ∀ᶠ z : ℍ in atImInfty, ‖Function.Periodic.qParam h (z : ℂ)‖ < ε := by
    have := (UpperHalfPlane.qParam_tendsto_atImInfty (h := h) hh)
    have := this.eventually (Metric.ball_mem_nhds 0 hε)
    simpa using this
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hq
  have key : ∀ z : ℍ, A ≤ z.im → MDiffAt f z := by
    intro z hz
    have hqz := hA z hz
    have han : AnalyticAt ℂ (cuspFunction h f) (Function.Periodic.qParam h (z : ℂ)) :=
      hball (by simpa [dist_eq_norm] using hqz) (by simp [Function.Periodic.qParam])
    have : f = fun w : ℍ => cuspFunction h f (Function.Periodic.qParam h (w : ℂ)) :=
      funext fun w => (UpperHalfPlane.eq_cuspFunction w hh.ne' hper).symm
    rw [this]
    have hq' : MDiffAt (fun w : ℍ => Function.Periodic.qParam h (w : ℂ)) z :=
      (Function.Periodic.differentiable_qParam (h := h) (z : ℂ)).comp_mdifferentiableAt
        (UpperHalfPlane.mdifferentiable_coe z)
    exact DifferentiableAt.comp_mdifferentiableAt (f := fun w : ℍ => Function.Periodic.qParam h (w : ℂ)) han.differentiableAt hq'
  refine ⟨A, fun z hz => ?_⟩
  have hopen : IsOpen {w : ℍ | A < w.im} := isOpen_lt continuous_const UpperHalfPlane.continuous_im
  filter_upwards [hopen.mem_nhds hz] with w hw using key w (le_of_lt hw)

/-- The polynomial $Q(j)\Delta^{\deg Q}$ is bounded at the cusp, since $j\Delta = E_4^3$. -/
lemma isBoundedAtImInfty_poly_jFun_mul_disc_pow (Q : Polynomial ℂ) :
    IsBoundedAtImInfty (fun z => Q.eval (jFun z) * Δ z ^ Q.natDegree) := by
  have hE : IsBoundedAtImInfty (E₄ : ℍ → ℂ) := ModularFormClass.bdd_at_infty E₄
  have hD : IsBoundedAtImInfty (Δ : ℍ → ℂ) := ModularFormClass.bdd_at_infty CuspForm.discriminant
  have hE' : (E₄ : ℍ → ℂ) ∈ boundedAtImInftySubalgebra ℂ := hE
  have hD' : (Δ : ℍ → ℂ) ∈ boundedAtImInftySubalgebra ℂ := hD
  set d := Q.natDegree with hd
  have hfun : (fun z => Q.eval (jFun z) * Δ z ^ d) =
      ∑ i ∈ Finset.range (d + 1),
        Q.coeff i • ((E₄ : ℍ → ℂ) ^ (3 * i) * (Δ : ℍ → ℂ) ^ (d - i)) := by
    funext z
    simp only [Polynomial.eval_eq_sum_range, Finset.sum_mul, Finset.sum_apply, Pi.smul_apply,
      Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ d := by simpa [Nat.lt_succ_iff] using hi
    have e1 : jFun z ^ i * Δ z ^ d = (jFun z * Δ z) ^ i * Δ z ^ (d - i) := by
      rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' hi']
    rw [mul_assoc, e1, jFun_mul_disc, ← pow_mul]
  rw [hfun]
  exact Subalgebra.sum_mem _ fun i _ =>
    Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hE' _)
      (Subalgebra.pow_mem _ hD' _)) _

/-- A function meromorphic at `x` (on `ℂ`) with non-negative order has a removable singularity. -/
lemma Removable.of_order_nonneg {g : ℍ → ℂ} {z : ℍ} (hm : MeromorphicAt (g ∘ ofComplex) (z : ℂ))
    (ho : 0 ≤ meromorphicOrderAt (g ∘ ofComplex) (z : ℂ)) : Removable g z := by
  obtain ⟨h, han, he⟩ := (hm.meromorphicOrderAt_nonneg_iff).mp ho
  refine ⟨fun w => h w, ?_, ?_⟩
  · have hc : Tendsto (fun w : ℍ => (w : ℂ)) (𝓝 z) (𝓝 (z : ℂ)) :=
      (UpperHalfPlane.continuous_coe).continuousAt.tendsto
    filter_upwards [hc.eventually han.eventually_analyticAt] with w hw
    exact hw.differentiableAt.comp_mdifferentiableAt (f := fun w : ℍ => (w : ℂ))
      (UpperHalfPlane.mdifferentiable_coe w)
  · have hc : Tendsto (fun w : ℍ => (w : ℂ)) (𝓝[≠] z) (𝓝[≠] (z : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨(UpperHalfPlane.continuous_coe).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact fun h => hw (UpperHalfPlane.coe_injective h)
    filter_upwards [hc.eventually he] with w hw
    simpa using hw

/-- Poles of a function meromorphic on the upper half plane in a compact subset form a finite set. -/
lemma finite_poles_of_isCompact {F : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ {z : ℂ | 0 < z.im}) (hF : MeromorphicOn F {z : ℂ | 0 < z.im}) :
    {x ∈ K | meromorphicOrderAt F x < 0}.Finite := by
  by_contra hinf
  obtain ⟨x, hxK, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hK (fun y hy => hy.1)
  have hev := (hF x (hKU hxK)).eventually_analyticAt
  rw [accPt_iff_frequently_nhdsNE] at hx
  obtain ⟨y, hy1, hy2⟩ := (hx.and_eventually hev).exists
  exact (not_lt.mpr hy2.meromorphicOrderAt_nonneg) hy1.2

/-- Every extended order is bounded below by a negative natural number. -/
lemma exists_nat_add_order_nonneg (o : WithTop ℤ) : ∃ m : ℕ, 0 ≤ (m : WithTop ℤ) + o := by
  cases o with
  | top => exact ⟨0, by simp⟩
  | coe n =>
    refine ⟨(-n).toNat, ?_⟩
    have : (-n) ≤ ((-n).toNat : ℤ) := Int.self_le_toNat (-n)
    have h2 : (0 : ℤ) ≤ ((-n).toNat : ℤ) + n := by omega
    exact_mod_cast h2

/-- Multiplying by a high power of a function vanishing at `x` removes a pole of order at most the
exponent. -/
lemma meromorphicOrderAt_pow_mul_nonneg {F a : ℂ → ℂ} {x : ℂ} (hF : MeromorphicAt F x)
    (ha : AnalyticAt ℂ a x) (ha0 : a x = 0) {m M : ℕ} (hm : m ≤ M)
    (hmF : 0 ≤ (m : WithTop ℤ) + meromorphicOrderAt F x) :
    0 ≤ meromorphicOrderAt (fun u => a u ^ M * F u) x := by
  have hpos : 0 < meromorphicOrderAt a x := by
    rw [← tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt]
    have := ha.continuousAt.tendsto
    rw [ha0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h1 : (1 : WithTop ℤ) ≤ meromorphicOrderAt a x := by
    cases h : meromorphicOrderAt a x with
    | top => exact le_top
    | coe n =>
      rw [h] at hpos
      have : (0 : ℤ) < n := by exact_mod_cast hpos
      exact_mod_cast (show (1 : ℤ) ≤ n by omega)
  have hMo : (M : WithTop ℤ) ≤ (M : WithTop ℤ) * meromorphicOrderAt a x := by
    cases h : meromorphicOrderAt a x with
    | top =>
      cases M with
      | zero => simp
      | succ k =>
        have hk : ((k + 1 : ℕ) : WithTop ℤ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
        rw [WithTop.mul_top hk]
        exact le_top
    | coe n =>
      rw [h] at h1
      have : (1 : ℤ) ≤ n := by exact_mod_cast h1
      have h3 : (M : ℤ) ≤ M * n := by nlinarith [Int.natCast_nonneg M]
      exact_mod_cast h3
  have e : (fun u => a u ^ M * F u) = a ^ M * F := rfl
  rw [e, meromorphicOrderAt_mul (ha.meromorphicAt.pow M) hF,
    meromorphicOrderAt_pow ha.meromorphicAt]
  calc (0 : WithTop ℤ) ≤ (m : WithTop ℤ) + meromorphicOrderAt F x := hmF
    _ ≤ (M : WithTop ℤ) + meromorphicOrderAt F x := by
        gcongr
    _ ≤ (M : WithTop ℤ) * meromorphicOrderAt a x + meromorphicOrderAt F x := by
        gcongr

/-- A polynomial in an analytic function is analytic. -/
lemma analyticAt_eval_comp {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (Q : Polynomial ℂ) :
    AnalyticAt ℂ (fun u => Q.eval (g u)) x := by
  simpa using hg.aeval_polynomial Q

/-- A polynomial in $j$ is holomorphic. -/
lemma mdiffAt_eval_jFun (Q : Polynomial ℂ) (z : ℍ) : MDiffAt (fun w => Q.eval (jFun w)) z :=
  DifferentiableAt.comp_mdifferentiableAt (f := jFun) (Q.differentiable.differentiableAt)
    (jFun_mdifferentiable z)

/-- Multiplying a modular function by a suitable nonzero polynomial in $j$ removes all its poles. -/
lemma exists_clearing {f : ℍ → ℂ} (hmod : IsModularFunction ⊤ f) :
    ∃ Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ z : ℍ, Removable (fun w => Q.eval (jFun w) * f w) z := by
  classical
  obtain ⟨Y, hY⟩ := exists_im_gt_mdiffAt hmod
  set F : ℂ → ℂ := f ∘ ofComplex with hF
  have hFm : MeromorphicOn F {z : ℂ | 0 < z.im} := hmod.meromorphic
  have hK : IsCompact (UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain Y) :=
    (ModularGroup.isCompact_truncatedFundamentalDomain Y).image UpperHalfPlane.continuous_coe
  have hfin := finite_poles_of_isCompact hK (by rintro _ ⟨z, -, rfl⟩; exact z.im_pos) hFm
  set Pf := hfin.toFinset with hPf
  choose m hm using fun x : ℂ => exists_nat_add_order_nonneg (meromorphicOrderAt F x)
  set M := Pf.sup m with hM
  set jc : ℂ → ℂ := fun u => jFun (ofComplex u) with hjc
  have hjan : ∀ x : ℂ, 0 < x.im → AnalyticAt ℂ jc x := fun x hx =>
    (UpperHalfPlane.mdifferentiable_iff.mp jFun_mdifferentiable).analyticAt
      (isOpen_upperHalfPlaneSet.mem_nhds hx)
  set Q : Polynomial ℂ := ∏ x ∈ Pf, (Polynomial.X - Polynomial.C (jc x)) ^ M with hQ
  refine ⟨Q, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun x _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  intro z
  have hinv : ∀ (δ : SL(2, ℤ)) (u : ℍ),
      Q.eval (jFun (δ • u)) * f (δ • u) = Q.eval (jFun u) * f u := by
    intro δ u
    rw [jFun_smul, hmod.invariant δ (Subgroup.mem_top δ)]
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd z
  have hw : Removable (fun w => Q.eval (jFun w) * f w) (γ • z) := by
    set w := γ • z with hwdef
    by_cases hy : Y < w.im
    · refine Removable.of_eventually_mdiffAt ?_
      filter_upwards [hY w hy] with u hu
      exact (mdiffAt_eval_jFun Q u).mul hu
    · have hwK : (w : ℂ) ∈ UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain Y :=
        ⟨w, ⟨hγ, not_lt.mp hy⟩, rfl⟩
      have hwU : 0 < (w : ℂ).im := w.im_pos
      have hjw : AnalyticAt ℂ jc (w : ℂ) := hjan _ hwU
      have hFw : MeromorphicAt F (w : ℂ) := hFm _ hwU
      refine Removable.of_order_nonneg ?_ ?_
      · exact (analyticAt_eval_comp hjw Q).meromorphicAt.mul hFw
      · by_cases hp : meromorphicOrderAt F (w : ℂ) < 0
        · have hmem : (w : ℂ) ∈ Pf := hfin.mem_toFinset.mpr ⟨hwK, hp⟩
          set Q' : Polynomial ℂ :=
            ∏ x ∈ Pf.erase (w : ℂ), (Polynomial.X - Polynomial.C (jc x)) ^ M with hQ'
          have hQe : ∀ t, Q.eval t = (t - jc (w : ℂ)) ^ M * Q'.eval t := by
            intro t
            rw [hQ, ← Finset.mul_prod_erase Pf _ hmem]
            simp [hQ', Polynomial.eval_mul, Polynomial.eval_pow]
          have e : ((fun w => Q.eval (jFun w) * f w) ∘ ofComplex) =
              fun u => (jc u - jc (w : ℂ)) ^ M * (Q'.eval (jc u) * F u) := by
            funext u
            simp only [Function.comp, hQe, hjc, hF, mul_assoc]
          rw [e]
          have hF' : MeromorphicAt (fun u => Q'.eval (jc u) * F u) (w : ℂ) :=
            (analyticAt_eval_comp hjw Q').meromorphicAt.mul hFw
          have hord : meromorphicOrderAt F (w : ℂ) ≤
              meromorphicOrderAt (fun u => Q'.eval (jc u) * F u) (w : ℂ) := by
            have e2 : (fun u => Q'.eval (jc u) * F u) = (fun u => Q'.eval (jc u)) * F := rfl
            rw [e2, meromorphicOrderAt_mul (analyticAt_eval_comp hjw Q').meromorphicAt hFw]
            exact le_add_of_nonneg_left (analyticAt_eval_comp hjw Q').meromorphicOrderAt_nonneg
          refine meromorphicOrderAt_pow_mul_nonneg hF' (hjw.sub analyticAt_const) (sub_self _)
            (m := m (w : ℂ)) (Finset.le_sup hmem) ?_
          exact (hm (w : ℂ)).trans (by gcongr)
        · have hnn : 0 ≤ meromorphicOrderAt F (w : ℂ) := not_lt.mp hp
          have e : ((fun w => Q.eval (jFun w) * f w) ∘ ofComplex) =
              (fun u => Q.eval (jc u)) * F := rfl
          rw [e, meromorphicOrderAt_mul (analyticAt_eval_comp hjw Q).meromorphicAt hFw]
          exact add_nonneg (analyticAt_eval_comp hjw Q).meromorphicOrderAt_nonneg hnn
  have := hw.smul hinv γ⁻¹
  simpa using this

/-- The last sentence of Proposition 2.2 (pdf p. 191). -/
@[kb "milne2006ec" "Ch. V, Proposition 2.2 (meromorphic functions on X₀(1) are ℂ(j)), pdf p. 191"]
theorem prop2_2Rational : Prop2_2Rational := by
  refine ⟨fun f hmod => ?_⟩
  obtain ⟨Q, hQ0, hrem⟩ := exists_clearing hmod
  set G : ℍ → ℂ := fun w => Q.eval (jFun w) * f w with hG
  have hGinv : ∀ (γ : SL(2, ℤ)) (z : ℍ), G (γ • z) = G z := by
    intro γ z
    simp only [hG, jFun_smul, hmod.invariant γ (Subgroup.mem_top γ)]
  obtain ⟨G', hG'd, hG'inv, hGeq, hGeq2⟩ := Removable.exists_extension hrem hGinv
  have hmer : IsMeromorphicAtImInfty f := by simpa using hmod.meromorphic_cusps 1
  obtain ⟨n, hn⟩ := exists_pow_disc_bounded hmer
  have hb := isBoundedAtImInfty_poly_jFun_mul_disc_pow Q
  obtain ⟨Y, hY⟩ := exists_im_gt_mdiffAt hmod
  have hprod : IsBoundedAtImInfty
      (fun z => (f z * Δ z ^ n) * (Q.eval (jFun z) * Δ z ^ Q.natDegree)) :=
    (boundedAtImInftySubalgebra ℂ).mul_mem (show _ ∈ boundedAtImInftySubalgebra ℂ from hn)
      (show _ ∈ boundedAtImInftySubalgebra ℂ from hb)
  have hbd : IsBoundedAtImInfty (fun z => G' z * Δ z ^ (n + Q.natDegree)) := by
    refine Asymptotics.IsBigO.congr' hprod ?_ EventuallyEq.rfl
    have : {z : ℍ | (f z * Δ z ^ n) * (Q.eval (jFun z) * Δ z ^ Q.natDegree) =
        G' z * Δ z ^ (n + Q.natDegree)} ∈ atImInfty := by
      rw [atImInfty_mem]
      refine ⟨Y + 1, fun z hz => ?_⟩
      have h1 : G' z = G z := hGeq2 z ((hY z (by linarith)).mono fun u hu => (mdiffAt_eval_jFun Q u).mul hu)
      show _ = _
      simp only [h1, hG, pow_add]
      ring
    exact this
  obtain ⟨P, -, hP⟩ := key_poly (n + Q.natDegree) G' hG'd (law_zero_of_invariant hG'inv) hbd
  refine ⟨P, Q, hQ0, ?_⟩
  rw [eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE]
  intro z
  have hnz : ∀ᶠ w in 𝓝[≠] z, Q.eval (jFun w) ≠ 0 := by
    by_contra hcon
    have hfreq : ∃ᶠ w in 𝓝[≠] z, Q.eval (jFun w) = 0 :=
      (not_eventually.mp hcon).mono fun w hw => not_not.mp hw
    have h0 := UpperHalfPlane.eq_zero_of_frequently
      (fun w => mdiffAt_eval_jFun Q w) hfreq
    apply hQ0
    refine Polynomial.funext fun t => ?_
    obtain ⟨w, rfl⟩ := jFun_surjective t
    simpa using congrFun h0 w
  filter_upwards [hGeq z, hnz] with w hw hw0
  simp only [hG] at hw
  rw [eq_div_iff hw0, ← hP w, ← hw]
  ring

end NumberFieldKB.MilneEC.V
