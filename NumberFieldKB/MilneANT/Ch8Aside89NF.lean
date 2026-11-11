import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.Shrink
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch7Ostrowski

/-!
# Milne, *Algebraic Number Theory*, Aside 8.9 (completeness part, number fields)

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`,
Aside 8.9, p. 138; the underlying theorem is due to Artin and Whaples (1945).

Let `V` be a set of pairwise inequivalent nontrivial absolute values of a number field `K` such that for every
`a ≠ 0` only finitely many `v ∈ V` have `v a ≠ 1` and `∏_{v ∈ V} v a = 1`. If `V` is nonempty, every nontrivial
absolute value of `K` is equivalent to a member of `V` (`exists_mem_isEquiv_of_productFormula`).

Proof (following the classical argument). By Theorem 7.14 (`theorem7_14`, here reproved in every universe as
`theorem7_14_univ`) every member of `V` is equivalent to a finite or an infinite place.
* Write the archimedean members as `v = w ^ t_w` for infinite places `w`, and put `s w = t_w` (`expo`), `0` if
  there is none. Units have value `1` at all finite places, so the product formula at a unit `u` gives
  `∑ s w log (w u) = 0`; by Dirichlet's unit theorem `s w = c * mult w` (`exists_const_of_units`).
* If `c = 0` there is no archimedean member, and an element supported at the finite place of a member of `V`
  (`exists_supported`, from finiteness of the class group) contradicts the product formula.
* If `c ≠ 0`, every infinite place is represented in `V`; a nontrivial `w` not equivalent to any member is
  then a finite place `𝔭` not represented, and an element `a` supported at `𝔭` contradicts the product formula
  (`|N a| ≠ 1`).
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneANT.Aside89

variable {K : Type*} [Field K] [NumberField K]

/-! ## An element supported at a single finite place -/

/-- For a finite place `𝔭` there is a nonzero `a` with `𝔭 a < 1` and `𝔮 a = 1` at every other finite place `𝔮`
(a generator of `𝔓 ^ h`, where `h` is the order of the class of the prime `𝔓`). -/
theorem exists_supported (𝔭 : FinitePlace K) :
    ∃ a : K, a ≠ 0 ∧ 𝔭 a < 1 ∧ ∀ 𝔮 : FinitePlace K, 𝔮 ≠ 𝔭 → 𝔮 a = 1 := by
  set 𝔓 := FinitePlace.maximalIdeal 𝔭 with h𝔓
  have hmem : 𝔓.asIdeal ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero 𝔓.ne_bot
  set h := orderOf (ClassGroup.mk0 (R := 𝓞 K) ⟨𝔓.asIdeal, hmem⟩) with hh
  have hpos : 0 < h := orderOf_pos _
  have h1 : ClassGroup.mk0 (R := 𝓞 K) ⟨𝔓.asIdeal ^ h, pow_mem hmem h⟩ = 1 := by
    have : (⟨𝔓.asIdeal ^ h, pow_mem hmem h⟩ : (Ideal (𝓞 K))⁰) = ⟨𝔓.asIdeal, hmem⟩ ^ h := rfl
    rw [this, map_pow]; exact pow_orderOf_eq_one _
  obtain ⟨g, hg⟩ := ((ClassGroup.mk0_eq_one_iff _).1 h1).principal
  have hgI : 𝔓.asIdeal ^ h = Ideal.span {g} := hg
  have hpow_ne : 𝔓.asIdeal ^ h ≠ ⊥ := pow_ne_zero _ 𝔓.ne_bot
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply hpow_ne
    rw [hgI]; simp
  have hgmem : g ∈ 𝔓.asIdeal ^ h := by rw [hgI]; exact Ideal.mem_span_singleton_self g
  have hgP : g ∈ 𝔓.asIdeal := Ideal.pow_le_self hpos.ne' hgmem
  refine ⟨algebraMap (𝓞 K) K g, by simpa using hg0, ?_, ?_⟩
  · have : 𝔭 = FinitePlace.mk 𝔓 := (FinitePlace.mk_maximalIdeal 𝔭).symm
    rw [this, FinitePlace.mk_apply]
    exact (FinitePlace.norm_lt_one_iff_mem K 𝔓 g).2 hgP
  · intro 𝔮 hq
    set 𝔔 := FinitePlace.maximalIdeal 𝔮
    have hne : 𝔔 ≠ 𝔓 := by
      intro e
      apply hq
      rw [← FinitePlace.mk_maximalIdeal 𝔮, ← FinitePlace.mk_maximalIdeal 𝔭]
      exact congrArg _ e
    have : 𝔮 = FinitePlace.mk 𝔔 := (FinitePlace.mk_maximalIdeal 𝔮).symm
    rw [this, FinitePlace.mk_apply]
    refine (FinitePlace.norm_eq_one_iff_notMem K 𝔔 g).2 fun hgQ => hne ?_
    have hle : 𝔓.asIdeal ^ h ≤ 𝔔.asIdeal := by
      rw [hgI, Ideal.span_le]; simpa using hgQ
    have hle' : 𝔓.asIdeal ≤ 𝔔.asIdeal := (Ideal.IsPrime.pow_le_iff hpos.ne').1 hle
    have := 𝔓.isMaximal.eq_of_le 𝔔.isPrime.ne_top hle'
    exact HeightOneSpectrum.ext this.symm

/-! ## Exponents vanishing on units are proportional to the multiplicities (Dirichlet) -/

section Dirichlet

open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace

/-- If `∑ s w log (w u) = 0` for every unit `u`, then `s w = c * mult w` for a constant `c`. -/
theorem exists_const_of_units (s : InfinitePlace K → ℝ)
    (hs : ∀ u : (𝓞 K)ˣ, ∑ w, s w * Real.log (w (u : K)) = 0) :
    ∃ c : ℝ, ∀ w : InfinitePlace K, s w = c * w.mult := by
  classical
  set w₀ : InfinitePlace K := dirichletUnitTheorem.w₀ with hw₀
  have hm : ∀ w : InfinitePlace K, (w.mult : ℝ) ≠ 0 := fun w => by
    exact_mod_cast w.mult_pos.ne'
  refine ⟨s w₀ / w₀.mult, ?_⟩
  set c := s w₀ / w₀.mult with hc
  set t : InfinitePlace K → ℝ := fun w => s w / w.mult - c with ht
  have ht0 : t w₀ = 0 := by simp [ht, hc]
  let f : logSpace K →ₗ[ℝ] ℝ := ∑ w : {w : InfinitePlace K // w ≠ w₀}, t w.1 • LinearMap.proj w
  have hf : ∀ x : logSpace K, f x = ∑ w : {w : InfinitePlace K // w ≠ w₀}, t w.1 * x w := by
    intro x; simp [f]
  have hker : Submodule.span ℝ (unitLattice K : Set (logSpace K)) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u : (𝓞 K)ˣ, x = Additive.ofMul u := ⟨x.toMul, rfl⟩
    show f (logEmbedding K x) = 0
    rw [hu]
    rw [hf]
    have h1 := Fintype.sum_eq_add_sum_subtype_ne
      (fun w : InfinitePlace K => t w * (w.mult * Real.log (w (u : K)))) w₀
    simp only [ht0, zero_mul, zero_add] at h1
    simp only [logEmbedding_component]
    rw [← h1]
    have h2 : ∀ w : InfinitePlace K, t w * (w.mult * Real.log (w (u : K))) =
        s w * Real.log (w (u : K)) - c * (w.mult * Real.log (w (u : K))) := by
      intro w
      simp only [ht]
      field_simp [hm w]
    simp only [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_mult_mul_log u, hs u]
    simp
  rw [unitLattice_span_eq_top] at hker
  have hall : ∀ x : logSpace K, f x = 0 := fun x => hker (Submodule.mem_top (x := x))
  intro w
  by_cases hw : w = w₀
  · rw [hw]
    simp only [hc]; field_simp [hm w₀]
  · have := hall (Pi.single ⟨w, hw⟩ 1)
    rw [hf, Finset.sum_eq_single ⟨w, hw⟩] at this
    · simp only [Pi.single_eq_same, mul_one, ht] at this
      have h3 : s w / w.mult = c := by linarith
      rw [div_eq_iff (hm w)] at h3
      exact h3
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp

end Dirichlet

/-! ## Auxiliary facts on equivalent absolute values and places -/

theorem rpow_eq_one {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) (h : x ^ c = 1) : x = 1 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact (Real.rpow_lt_one hx h1 hc).ne h
  · exact (Real.one_lt_rpow h1 hc).ne' h

theorem eq_one_iff_of_isEquiv {v u : AbsoluteValue K ℝ} (h : v.IsEquiv u) (x : K) :
    v x = 1 ↔ u x = 1 := by
  obtain ⟨c, hc, hx⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 h
  have hx' : v x ^ c = u x := congrFun hx x
  constructor
  · intro h1; rw [← hx', h1, Real.one_rpow]
  · intro h1; rw [← hx'] at h1; exact rpow_eq_one (v.nonneg x) hc h1

/-- Units have value `1` at every finite place. -/
theorem finitePlace_unit (𝔮 : FinitePlace K) (u : (𝓞 K)ˣ) : 𝔮 (u : K) = 1 := by
  rw [← FinitePlace.mk_maximalIdeal 𝔮, FinitePlace.mk_apply]
  have := (FinitePlace.norm_eq_one_iff_notMem K (FinitePlace.maximalIdeal 𝔮) (u : 𝓞 K)).2
    (fun hu => (FinitePlace.maximalIdeal 𝔮).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu u.isUnit))
  exact this

/-! ## Exponents attached to the archimedean members of `V` -/

variable (V : Set (AbsoluteValue K ℝ))

open Classical in
/-- Choice of a member of `V` equivalent to the infinite place `w`, with the exponent relating them. -/
noncomputable def pick (w : InfinitePlace K) : AbsoluteValue K ℝ × ℝ :=
  if h : ∃ p : AbsoluteValue K ℝ × ℝ, p.1 ∈ V ∧ 0 < p.2 ∧ ∀ x, w x ^ p.2 = p.1 x then h.choose
  else (w.1, 0)

/-- The chosen member of `V` at `w`. -/
noncomputable def G (w : InfinitePlace K) : AbsoluteValue K ℝ := (pick V w).1

/-- The chosen exponent at `w`. -/
noncomputable def expo (w : InfinitePlace K) : ℝ := (pick V w).2

variable {V}

theorem exists_pick {w : InfinitePlace K} (hw : ∃ v ∈ V, w.1.IsEquiv v) :
    ∃ p : AbsoluteValue K ℝ × ℝ, p.1 ∈ V ∧ 0 < p.2 ∧ ∀ x, w x ^ p.2 = p.1 x := by
  obtain ⟨v, hv, he⟩ := hw
  obtain ⟨c, hc, hx⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  exact ⟨(v, c), hv, hc, fun x => congrFun hx x⟩

theorem pick_spec {w : InfinitePlace K} (hw : ∃ v ∈ V, w.1.IsEquiv v) :
    G V w ∈ V ∧ 0 < expo V w ∧ ∀ x, w x ^ expo V w = G V w x := by
  have h := exists_pick hw
  unfold G expo pick
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

theorem expo_eq_zero {w : InfinitePlace K} (hw : ¬ ∃ v ∈ V, w.1.IsEquiv v) : expo V w = 0 := by
  have h : ¬ ∃ p : AbsoluteValue K ℝ × ℝ, p.1 ∈ V ∧ 0 < p.2 ∧ ∀ x, w x ^ p.2 = p.1 x := by
    intro h
    apply hw
    obtain ⟨p, hp, hc, hx⟩ := h
    exact ⟨p.1, hp, AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨p.2, hc, funext hx⟩⟩
  unfold expo pick
  simp only [h, ↓reduceDIte]

theorem isEquiv_G {w : InfinitePlace K} (hw : ∃ v ∈ V, w.1.IsEquiv v) : w.1.IsEquiv (G V w) := by
  obtain ⟨h1, h2, h3⟩ := pick_spec hw
  exact AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨_, h2, funext h3⟩

theorem G_eq (hineq : ∀ v ∈ V, ∀ w ∈ V, v.IsEquiv w → v = w) {w : InfinitePlace K} {v}
    (hv : v ∈ V) (hwv : w.1.IsEquiv v) : G V w = v := by
  have hw : ∃ v ∈ V, w.1.IsEquiv v := ⟨v, hv, hwv⟩
  exact hineq _ (pick_spec hw).1 _ hv ((isEquiv_G hw).symm.trans hwv)

theorem ex_of_expo_ne {w : InfinitePlace K} (h : expo V w ≠ 0) : ∃ v ∈ V, w.1.IsEquiv v := by
  by_contra hw
  exact h (expo_eq_zero hw)

/-! ## The product over `V`, rewritten over the infinite places -/

theorem finprod_eq_prod_expo (h7 : Theorem7_14 K) (hnt : ∀ v ∈ V, v.IsNontrivial)
    (hineq : ∀ v ∈ V, ∀ w ∈ V, v.IsEquiv w → v = w) {a : K}
    (hF : ∀ v ∈ V, ∀ 𝔮 : FinitePlace K, v.IsEquiv 𝔮.1 → v a = 1) :
    ∏ᶠ v ∈ V, v a = ∏ w : InfinitePlace K, (w a) ^ expo V w := by
  classical
  set P : Finset (InfinitePlace K) := Finset.univ.filter (fun w => expo V w ≠ 0) with hP
  have h1 : ∏ w : InfinitePlace K, (w a) ^ expo V w = ∏ w ∈ P, (w a) ^ expo V w := by
    refine (Finset.prod_filter_of_ne ?_).symm
    intro w _ hw h0
    apply hw; rw [h0, Real.rpow_zero]
  have h2 : ∏ w ∈ P, (w a) ^ expo V w = ∏ w ∈ P, (G V w) a := by
    refine Finset.prod_congr rfl fun w hw => ?_
    have hw' : expo V w ≠ 0 := (Finset.mem_filter.1 hw).2
    exact (pick_spec (ex_of_expo_ne hw')).2.2 a
  have hinj : Set.InjOn (G V) P := by
    intro w hw w' hw' hww
    have e1 := isEquiv_G (ex_of_expo_ne (Finset.mem_filter.1 hw).2)
    have e2 := isEquiv_G (ex_of_expo_ne (Finset.mem_filter.1 hw').2)
    rw [hww] at e1
    exact InfinitePlace.eq_iff_isEquiv.2 (e1.trans e2.symm)
  have h3 : ∏ w ∈ P, (G V w) a = ∏ v ∈ P.image (G V), v a :=
    (Finset.prod_image (f := fun v : AbsoluteValue K ℝ => v a) hinj).symm
  have h4 : ∏ᶠ v ∈ V, v a = ∏ v ∈ P.image (G V), v a := by
    refine finprod_cond_eq_prod_of_cond_iff (fun v : AbsoluteValue K ℝ => v a) (fun {v} hv1 => ?_)
    constructor
    · intro hvV
      rcases h7.exists_isEquiv v (hnt v hvV) with ⟨𝔮, h𝔮⟩ | ⟨w, hw⟩
      · exact absurd (hF v hvV 𝔮 h𝔮) hv1
      · have hGw : G V w = v := G_eq hineq hvV hw.symm
        have hpos := (pick_spec ⟨v, hvV, hw.symm⟩).2.1
        exact Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ _, hpos.ne'⟩, hGw⟩
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
      exact (pick_spec (ex_of_expo_ne (Finset.mem_filter.1 hw).2)).1
  rw [h4, ← h3, ← h2, ← h1]

theorem sum_expo_log (h7 : Theorem7_14 K) (hnt : ∀ v ∈ V, v.IsNontrivial)
    (hineq : ∀ v ∈ V, ∀ w ∈ V, v.IsEquiv w → v = w)
    (hprod : ∀ a : K, a ≠ 0 → {v ∈ V | v a ≠ 1}.Finite ∧ ∏ᶠ (v ∈ V), v a = 1) {a : K} (ha : a ≠ 0)
    (hF : ∀ v ∈ V, ∀ 𝔮 : FinitePlace K, v.IsEquiv 𝔮.1 → v a = 1) :
    ∑ w : InfinitePlace K, expo V w * Real.log (w a) = 0 := by
  have h := finprod_eq_prod_expo h7 hnt hineq hF
  rw [(hprod a ha).2] at h
  have hpos : ∀ w : InfinitePlace K, 0 < w a := fun w => InfinitePlace.pos_iff.2 ha
  calc ∑ w : InfinitePlace K, expo V w * Real.log (w a)
      = ∑ w : InfinitePlace K, Real.log ((w a) ^ expo V w) :=
        Finset.sum_congr rfl fun w _ => (Real.log_rpow (hpos w) _).symm
    _ = Real.log (∏ w : InfinitePlace K, (w a) ^ expo V w) :=
        (Real.log_prod fun w _ => (Real.rpow_pos_of_pos (hpos w) _).ne').symm
    _ = 0 := by rw [← h, Real.log_one]

/-- The main argument, given the existence part of Theorem 7.14 for `K`. -/
theorem core (h7 : Theorem7_14 K) (hnt : ∀ v ∈ V, v.IsNontrivial)
    (hineq : ∀ v ∈ V, ∀ w ∈ V, v.IsEquiv w → v = w)
    (hprod : ∀ a : K, a ≠ 0 → {v ∈ V | v a ≠ 1}.Finite ∧ ∏ᶠ (v ∈ V), v a = 1)
    (hne : V.Nonempty) :
    ∀ w : AbsoluteValue K ℝ, w.IsNontrivial → ∃ v ∈ V, w.IsEquiv v := by
  intro w hw
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hunit : ∀ u : (𝓞 K)ˣ, ∑ w' : InfinitePlace K, expo V w' * Real.log (w' (u : K)) = 0 := by
    intro u
    refine sum_expo_log h7 hnt hineq hprod (NumberField.Units.coe_ne_zero u) ?_
    intro v _ 𝔮 h𝔮
    exact (eq_one_iff_of_isEquiv h𝔮 _).2 (finitePlace_unit 𝔮 u)
  obtain ⟨c, hc⟩ := exists_const_of_units (expo V) hunit
  by_cases hc0 : c = 0
  · have hz : ∀ w' : InfinitePlace K, expo V w' = 0 := fun w' => by rw [hc w', hc0, zero_mul]
    obtain ⟨v0, hv0⟩ := hne
    rcases h7.exists_isEquiv v0 (hnt v0 hv0) with ⟨𝔮, h𝔮⟩ | ⟨w', hw'⟩
    · obtain ⟨a, ha0, ha1, ha2⟩ := exists_supported 𝔮
      have hpa := (hprod a ha0).2
      have hfin : ∏ᶠ v ∈ V, v a = ∏ v ∈ ({v0} : Finset (AbsoluteValue K ℝ)), v a := by
        classical
        refine finprod_cond_eq_prod_of_cond_iff (fun v : AbsoluteValue K ℝ => v a) (fun {v} hv1 => ?_)
        simp only [Finset.mem_singleton]
        constructor
        · intro hvV
          rcases h7.exists_isEquiv v (hnt v hvV) with ⟨𝔮', h𝔮'⟩ | ⟨w', hw'⟩
          · by_cases e : 𝔮' = 𝔮
            · rw [e] at h𝔮'
              exact hineq _ hvV _ hv0 (h𝔮'.trans h𝔮.symm)
            · exact absurd ((eq_one_iff_of_isEquiv h𝔮' a).2 (ha2 𝔮' e)) hv1
          · have := (pick_spec ⟨v, hvV, hw'.symm⟩).2.1
            rw [hz] at this; exact absurd this (lt_irrefl _)
        · intro h; rw [h]; exact hv0
      rw [hfin, Finset.prod_singleton] at hpa
      have : v0 a < 1 := h𝔮.lt_one_iff.2 ha1
      linarith
    · have := (pick_spec ⟨v0, hv0, hw'.symm⟩).2.1
      rw [hz] at this; exact absurd this (lt_irrefl _)
  · have hall : ∀ w' : InfinitePlace K, ∃ v ∈ V, w'.1.IsEquiv v := fun w' => by
      apply ex_of_expo_ne; rw [hc w']
      exact mul_ne_zero hc0 (Nat.cast_ne_zero.2 w'.mult_pos.ne')
    rcases h7.exists_isEquiv w hw with ⟨𝔭, h𝔭⟩ | ⟨w', hw'⟩
    · obtain ⟨a, ha0, ha1, ha2⟩ := exists_supported 𝔭
      have hF : ∀ v ∈ V, ∀ 𝔮 : FinitePlace K, v.IsEquiv 𝔮.1 → v a = 1 := by
        intro v hv 𝔮 h𝔮
        by_cases e : 𝔮 = 𝔭
        · exfalso; rw [e] at h𝔮; exact hcon v hv (h𝔭.trans h𝔮.symm)
        · exact (eq_one_iff_of_isEquiv h𝔮 a).2 (ha2 𝔮 e)
      have hs := sum_expo_log h7 hnt hineq hprod ha0 hF
      have hs' : ∑ w' : InfinitePlace K, (w'.mult : ℝ) * Real.log (w' a) = 0 := by
        have : ∑ w' : InfinitePlace K, expo V w' * Real.log (w' a) =
            c * ∑ w' : InfinitePlace K, (w'.mult : ℝ) * Real.log (w' a) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w' _ => ?_
          rw [hc w']; ring
        rw [this] at hs
        exact (mul_eq_zero.1 hs).resolve_left hc0
      have hpf := NumberField.prod_abs_eq_one ha0
      rw [finprod_eq_single _ 𝔭 (fun 𝔮 h => ha2 𝔮 h)] at hpf
      have hpos : ∀ w' : InfinitePlace K, 0 < w' a := fun w' => InfinitePlace.pos_iff.2 ha0
      have hprodpos : 0 < ∏ w' : InfinitePlace K, (w' a) ^ w'.mult :=
        Finset.prod_pos fun w' _ => pow_pos (hpos w') _
      have hlog : Real.log (∏ w' : InfinitePlace K, (w' a) ^ w'.mult) = 0 := by
        rw [Real.log_prod fun w' _ => (pow_pos (hpos w') _).ne']
        simpa [Real.log_pow] using hs'
      have h1 := Real.eq_one_of_pos_of_log_eq_zero hprodpos hlog
      rw [h1, one_mul] at hpf
      linarith
    · obtain ⟨v, hv, hv'⟩ := hall w'
      exact hcon v hv (hw'.trans hv')

/-! ## Theorem 7.14 in every universe

`theorem7_14` is stated for `K : Type`; the headline is universe polymorphic, so we transport along
`Shrink` (a number field is small, being finite dimensional over `ℚ`). -/

theorem exists_infinitePlace_isEquiv_univ (v : AbsoluteValue K ℝ) (hna : ¬ IsNonarchimedean v) :
    ∃ w : InfinitePlace K, v.IsEquiv w.1 := by
  have : Small.{0} K := Module.Finite.small ℚ K
  let e : Shrink.{0} K ≃+* K := Shrink.ringEquiv K
  have : NumberField (Shrink.{0} K) := NumberField.of_ringEquiv _ _ e.symm
  let v' : AbsoluteValue (Shrink.{0} K) ℝ := v.comp (f := e.toRingHom) e.injective
  have hna' : ¬ IsNonarchimedean v' := by
    intro h; apply hna; intro x y
    have := h (e.symm x) (e.symm y)
    simpa [v'] using this
  obtain ⟨w', hw'⟩ := exists_infinitePlace_isEquiv_of_remark_7_49a remark_7_49a v' hna'
  refine ⟨w'.comap e.symm.toRingHom, ?_⟩
  obtain ⟨c, hc, hx⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 hw'
  refine AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨c, hc, funext fun x => ?_⟩
  have := congrFun hx (e.symm x)
  have h3 : (w'.comap e.symm.toRingHom).1 x = w'.1 (e.symm x) := InfinitePlace.comap_apply _ _ _
  show v x ^ c = (w'.comap e.symm.toRingHom).1 x
  rw [h3, ← hx]
  simp [v']

/-- **Theorem 7.14, existence part**, for number fields in an arbitrary universe. -/
theorem theorem7_14_univ : Theorem7_14 K where
  exists_isEquiv v hv := by
    by_cases hna : IsNonarchimedean v
    · exact .inl (exists_finitePlace_isEquiv v hv hna)
    · exact .inr (exists_infinitePlace_isEquiv_univ v hna)

/-- **Aside 8.9, completeness part, number fields**: if a set `V` of pairwise inequivalent nontrivial absolute values
of a number field satisfies the product formula (and is nonempty), every nontrivial absolute value is equivalent to
one in `V`. -/
@[kb "milne2020ant" "v3.08, Aside 8.9, p. 138"]
theorem exists_mem_isEquiv_of_productFormula {K : Type*} [Field K] [NumberField K] (V : Set (AbsoluteValue K ℝ))
    (hnt : ∀ v ∈ V, v.IsNontrivial) (hineq : ∀ v ∈ V, ∀ w ∈ V, v.IsEquiv w → v = w)
    (hprod : ∀ a : K, a ≠ 0 → {v ∈ V | v a ≠ 1}.Finite ∧ ∏ᶠ (v ∈ V), v a = 1)
    (hne : V.Nonempty) :
    ∀ w : AbsoluteValue K ℝ, w.IsNontrivial → ∃ v ∈ V, w.IsEquiv v :=
  core theorem7_14_univ hnt hineq hprod hne

end NumberFieldKB.MilneANT.Aside89
