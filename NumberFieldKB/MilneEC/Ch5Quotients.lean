import NumberFieldKB.MilneEC.Ch5ModularForms
import Mathlib.NumberTheory.Modular
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Nat.Dist

/-!
# Milne, *Elliptic Curves*, Chapter V §1: the Riemann surfaces $X_0(N)$

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §1 (pdf pp. 181–189).

Formalized: Example 1.1 ($q = e^{2\pi iz}$ identifies $\mathbb C/\mathbb Z$ with $\mathbb C^\times$), fundamental
domains (definition in prose) with Milne's two examples, Example 1.2 for rotation groups, Proposition 1.3 (from
Mathlib's `ModularGroup.fd`), Remark 1.4 (first part; the second part is a named statement), Proposition 1.5,
Corollary 1.6, the running-text claims on stabilizers and on the neighbourhood $\{\Im z > 2\}$ of $\infty$, and the
cusps.

Not in this file: the topology of $\mathbb H^* = \mathbb H \cup \mathbb P^1(\mathbb Q)$ and Proposition 1.7, the complex
structure on $\Gamma_0(N)\backslash\mathbb H^*$ and Proposition 1.8 (Mathlib has no Riemann surface structure on a
quotient by a non-free action). The genus of $X_0(N)$ is computed algebraically in `NumberFieldKB/ModularCurves/`.
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups Real Manifold Pointwise Modular

namespace NumberFieldKB.MilneEC.V

/-- **Example 1.1** (pdf p. 181): $q(z) = e^{2\pi iz}$ identifies $\mathbb C/\mathbb Z$ with $\mathbb C^\times$:
$q(z) = q(w)$ if and only if $w - z \in \mathbb Z$, and $q$ takes every nonzero value. -/
@[kb "milne2006ec" "Ch. V, Example 1.1, pdf p. 181"]
theorem example_1_1 :
    (∀ z w : ℂ, cexp (2 * π * I * z) = cexp (2 * π * I * w) ↔ ∃ n : ℤ, w = z + n) ∧
      Set.range (fun z : ℂ ↦ cexp (2 * π * I * z)) = {0}ᶜ := by
  have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  constructor
  · intro z w
    rw [Complex.exp_eq_exp_iff_exists_int]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      have : 2 * π * I * (w - z) = 2 * π * I * (-n : ℤ) := by
        push_cast; linear_combination -hn
      have := mul_left_cancel₀ hpi this
      linear_combination this
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      rw [hn]; push_cast; ring
  · ext w
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, rfl⟩; exact Complex.exp_ne_zero _
    · intro hw
      obtain ⟨u, hu⟩ := (Complex.range_exp ▸ (show w ∈ ({0}ᶜ : Set ℂ) from hw) : w ∈ Set.range Complex.exp)
      exact ⟨u / (2 * π * I), by rw [mul_div_cancel₀ _ hpi]; exact hu⟩

/-- A *fundamental domain* (pdf p. 182) for an action on $X$, given by its orbit relation $r$ ($r\,x\,y$: $y$ is
in the orbit of $x$): a connected open subset $D$ of $X$ such that (a) no two points of $D$ lie in the same
orbit, (b) the closure of $D$ contains at least one element of each orbit. -/
@[kb "milne2006ec" "Ch. V, §1, fundamental domain (definition in prose), pdf p. 182"]
structure IsFundamentalDomainFor {X : Type*} [TopologicalSpace X] (r : X → X → Prop) (D : Set X) : Prop where
  isOpen : IsOpen D
  isConnected : IsConnected D
  no_two : ∀ x ∈ D, ∀ y ∈ D, r x y → x = y
  closure_meets : ∀ x, ∃ y ∈ closure D, r x y

/-- The orbit relation of a group action. -/
def orbitRelation (G X : Type*) [SMul G X] (x y : X) : Prop := ∃ g : G, g • x = y

/-- Example (pdf p. 182): $\{0 < \Re z < 1\}$ is a fundamental domain for $\mathbb Z$ acting on $\mathbb C$ by
translations. -/
@[kb "milne2006ec" "Ch. V, §1, fundamental domain for ℤ acting on ℂ (running text), pdf p. 182"]
theorem isFundamentalDomain_strip :
    IsFundamentalDomainFor (fun z w : ℂ ↦ ∃ n : ℤ, w = z + n) {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  have hset : {z : ℂ | 0 < z.re ∧ z.re < 1} = Complex.re ⁻¹' Set.Ioo 0 1 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hset]; exact isOpen_Ioo.preimage Complex.continuous_re
  · refine ⟨⟨((1 / 2 : ℝ) : ℂ), by simp; norm_num⟩, ?_⟩
    · apply Convex.isPreconnected
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.smul_re, smul_eq_mul] at hx hy ⊢
      have h1 := mul_le_mul_of_nonneg_left (min_le_left x.re y.re) ha
      have h2 := mul_le_mul_of_nonneg_left (min_le_right x.re y.re) hb
      have h3 := mul_le_mul_of_nonneg_left (le_max_left x.re y.re) ha
      have h4 := mul_le_mul_of_nonneg_left (le_max_right x.re y.re) hb
      have h5 : 0 < min x.re y.re := lt_min hx.1 hy.1
      have h6 : max x.re y.re < 1 := max_lt hx.2 hy.2
      constructor <;> nlinarith
  · rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ ⟨n, rfl⟩
    simp only [Complex.add_re, Complex.intCast_re] at hy0 hy1
    have h1 : (n : ℝ) < 1 := by linarith
    have h2 : (-1 : ℝ) < n := by linarith
    have : n = 0 := by
      have a : n < 1 := by exact_mod_cast h1
      have b : -1 < n := by exact_mod_cast h2
      lia
    simp [this]
  · intro x
    refine ⟨x - (⌊x.re⌋ : ℤ), ?_, -⌊x.re⌋, by push_cast; ring⟩
    set y : ℂ := x - (⌊x.re⌋ : ℤ) with hy
    have hre : y.re = x.re - ⌊x.re⌋ := by simp [hy]
    have h0 : 0 ≤ y.re := by rw [hre]; linarith [Int.floor_le x.re]
    have h1 : y.re < 1 := by rw [hre]; linarith [Int.lt_floor_add_one x.re]
    let f : ℝ → ℂ := fun s ↦ y + (s : ℂ) * ((1 / 2 : ℂ) - y)
    have hf : Continuous f := by fun_prop
    have ht : Tendsto f (𝓝[>] 0) (𝓝 y) := by
      have := hf.tendsto 0
      simp only [f, Complex.ofReal_zero, zero_mul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    simp only [f, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im, zero_mul, sub_zero]
    norm_num
    constructor <;> nlinarith [hs.1, hs.2]

/-- Polar coordinates: the point of modulus `ρ` and argument `θ`. -/
noncomputable def polarPt (ρ θ : ℝ) : ℂ := (ρ : ℂ) * Complex.exp (θ * I)

/-- The modulus of a point given by polar coordinates. -/
lemma norm_polarPt (ρ θ : ℝ) : ‖polarPt ρ θ‖ = |ρ| := by
  simp [polarPt, Complex.norm_exp_ofReal_mul_I]

/-- The argument of a point given by polar coordinates with positive modulus. -/
lemma arg_polarPt {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : θ ∈ Set.Ioc (-π) π) : arg (polarPt ρ θ) = θ := by
  unfold polarPt
  rw [Complex.exp_mul_I]
  exact arg_mul_cos_add_sin_mul_I hρ hθ

/-- Polar coordinates depend continuously on the modulus and the argument. -/
lemma continuous_polarPt : Continuous (fun p : ℝ × ℝ ↦ polarPt p.1 p.2) := by
  unfold polarPt; fun_prop

/-- Example (pdf p. 182): the sector $\{0 < \arg z < 2\pi/m\}$ of the unit disk is a fundamental domain for
$\mathbb Z/m\mathbb Z$ (the $m$-th roots of unity) acting on the disk by rotations. With Mathlib's
$\arg \in (-\pi, \pi]$ the sector is open only for $m \ge 2$ (for $m = 1$ Milne's sector is the disk cut along
$[0, 1)$, with $\arg \in [0, 2\pi)$). -/
@[kb "milne2006ec" "Ch. V, §1, fundamental domain for ℤ/mℤ acting on the disk (running text), pdf p. 182"]
theorem isFundamentalDomain_sector {m : ℕ} (hm : 2 ≤ m) :
    IsFundamentalDomainFor (fun z w : Metric.ball (0 : ℂ) 1 ↦ ∃ ζ : ℂ, ζ ^ m = 1 ∧ (w : ℂ) = ζ * z)
      {z | 0 < arg (z : ℂ) ∧ arg (z : ℂ) < 2 * π / m} := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hc0 : 0 < 2 * π / m := by positivity
  have hcπ : 2 * π / m ≤ π := by
    rw [div_le_iff₀ hmpos]; nlinarith [Real.pi_pos]
  set c : ℝ := 2 * π / m with hc
  set D : Set (Metric.ball (0 : ℂ) 1) := {z | 0 < arg (z : ℂ) ∧ arg (z : ℂ) < c} with hD
  -- points given by polar coordinates
  have key : ∀ ρ θ : ℝ, 0 < ρ → ρ < 1 → 0 < θ → θ < c →
      ∃ hz : polarPt ρ θ ∈ Metric.ball (0 : ℂ) 1, (⟨polarPt ρ θ, hz⟩ : Metric.ball (0 : ℂ) 1) ∈ D := by
    intro ρ θ hρ hρ1 hθ hθc
    have hz : polarPt ρ θ ∈ Metric.ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_polarPt, abs_of_pos hρ]; exact hρ1
    refine ⟨hz, ?_⟩
    have := arg_polarPt hρ (θ := θ) ⟨by linarith [Real.pi_pos], by linarith⟩
    simp only [hD, Set.mem_ofPred_eq]
    rw [this]; exact ⟨hθ, hθc⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- open
    let S : Set ℂ := {z | 0 < arg z ∧ arg z < c}
    have hS : IsOpen S := by
      rw [isOpen_iff_mem_nhds]
      intro z hz
      have hslit : z ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff_arg]
        refine ⟨by have := hz.2; intro h; rw [h] at this; linarith, ?_⟩
        intro h; have h1 := hz.1; rw [h, Complex.arg_zero] at h1; exact lt_irrefl _ h1
      have hcont := Complex.continuousAt_arg hslit
      exact hcont.preimage_mem_nhds (Ioo_mem_nhds hz.1 hz.2)
    exact hS.preimage continuous_subtype_val
  · -- connected
    have himg : Subtype.val '' D = (fun p : ℝ × ℝ ↦ polarPt p.1 p.2) '' (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo 0 c) := by
      ext z
      constructor
      · rintro ⟨⟨z, hzb⟩, ⟨h1, h2⟩, rfl⟩
        have hz0 : z ≠ 0 := by rintro rfl; simp at h1
        refine ⟨(‖z‖, arg z), ⟨⟨norm_pos_iff.mpr hz0, ?_⟩, h1, h2⟩, ?_⟩
        · simpa using hzb
        · simp [polarPt]
      · rintro ⟨⟨ρ, θ⟩, ⟨⟨hρ, hρ1⟩, hθ, hθc⟩, rfl⟩
        obtain ⟨hz, hzD⟩ := key ρ θ hρ hρ1 hθ hθc
        exact ⟨_, hzD, rfl⟩
    have hconn : IsConnected (Subtype.val '' D) := by
      rw [himg]
      exact (isConnected_Ioo (by norm_num : (0 : ℝ) < 1) |>.prod (isConnected_Ioo hc0)).image _
        continuous_polarPt.continuousOn
    refine ⟨?_, ?_⟩
    · obtain ⟨z, w, hw, -⟩ := hconn.nonempty
      exact ⟨w, hw⟩
    · exact (Topology.IsInducing.subtypeVal.isPreconnected_image).mp hconn.isPreconnected
  · -- no two points in one orbit
    rintro x hx y hy ⟨ζ, hζ, hyx⟩
    have hx0 : (x : ℂ) ≠ 0 := by
      intro h; have h1 := hx.1; rw [h, Complex.arg_zero] at h1; exact lt_irrefl _ h1
    have hζ0 : ζ ≠ 0 := by
      rintro rfl; rw [zero_pow (by omega)] at hζ; exact zero_ne_one hζ
    have : NeZero m := ⟨by omega⟩
    have hζu : Units.mk0 ζ hζ0 ∈ rootsOfUnity m ℂ := by
      rw [_root_.mem_rootsOfUnity']; exact hζ
    obtain ⟨k, hk, hkζ⟩ := (Complex.mem_rootsOfUnity m (Units.mk0 ζ hζ0)).mp hζu
    simp only [Units.val_mk0] at hkζ
    set φ : ℝ := 2 * π * k / m with hφ
    have hζφ : ζ = Complex.exp (φ * I) := by
      rw [← hkζ]; congr 1; simp only [hφ]; push_cast; ring
    have hφ0 : 0 ≤ φ := by positivity
    have hk' : (k : ℝ) + 1 ≤ m := by exact_mod_cast hk
    have hφc : φ + c = 2 * π * ((k : ℝ) + 1) / m := by
      simp only [hφ, hc]; field_simp
    have hφ1 : φ + c ≤ 2 * π := by
      rw [hφc, div_le_iff₀ hmpos]; nlinarith [Real.pi_pos]
    have hφc2 : φ - c = 2 * π * ((k : ℝ) - 1) / m := by
      simp only [hφ, hc]; field_simp
    have hα := hx
    have hβ := hy
    simp only [hD, Set.mem_ofPred_eq] at hα hβ
    -- angles
    have hargζ : ((arg ζ : ℝ) : Real.Angle) = (φ : Real.Angle) := by
      rw [hζφ, Complex.arg_exp_mul_I]
      exact Real.Angle.coe_toIocMod _ _
    have h1 := Complex.arg_mul_coe_angle hζ0 hx0
    rw [← hyx, hargζ] at h1
    have h2 : ((arg (y : ℂ) : ℝ) : Real.Angle) = ((φ + arg (x : ℂ) : ℝ) : Real.Angle) := by
      rw [Real.Angle.coe_add]; exact h1
    obtain ⟨j, hj⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h2
    have hj1 : (j : ℝ) < 1 := by
      by_contra hcon
      push Not at hcon
      nlinarith [Real.pi_pos, hα.1, hα.2, hβ.1, hβ.2]
    have hj2 : (-1 : ℝ) < j := by
      by_contra hcon
      push Not at hcon
      nlinarith [Real.pi_pos, hα.1, hα.2, hβ.1, hβ.2]
    have hj0 : j = 0 := by
      have a1 : j < 1 := by exact_mod_cast hj1
      have a2 : -1 < j := by exact_mod_cast hj2
      omega
    rw [hj0] at hj
    have hk0 : k = 0 := by
      by_contra hne
      have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.pos_of_ne_zero hne
      have : 0 ≤ φ - c := by rw [hφc2]; apply div_nonneg <;> nlinarith [Real.pi_pos]
      push_cast at hj
      nlinarith [hα.1, hβ.2]
    subst hk0
    have hζ1 : ζ = 1 := by rw [← hkζ]; simp
    apply Subtype.ext
    rw [hyx, hζ1, one_mul]
  · -- every orbit meets the closure
    have haux : ∀ ρ θ : ℝ, 0 ≤ ρ → ρ < 1 → 0 ≤ θ → θ < c →
        polarPt ρ θ ∈ closure (Subtype.val '' D) := by
      intro ρ θ hρ hρ1 hθ hθc
      let f : ℝ → ℂ := fun s ↦ polarPt ((1 - s) * ρ + s / 2) ((1 - s) * θ + s * (c / 2))
      have hf : Continuous f := by
        unfold f polarPt; fun_prop
      have ht : Tendsto f (𝓝[>] 0) (𝓝 (polarPt ρ θ)) := by
        have := hf.tendsto 0
        have h0 : f 0 = polarPt ρ θ := by simp [f]
        rw [h0] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto ht ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
      obtain ⟨hz, hzD⟩ := key ((1 - s) * ρ + s / 2) ((1 - s) * θ + s * (c / 2))
        (by nlinarith [hs.1, hs.2]) (by nlinarith [hs.1, hs.2]) (by nlinarith [hs.1, hs.2])
        (by nlinarith [hs.1, hs.2])
      exact ⟨_, hzD, rfl⟩
    intro x
    set t : ℝ := arg (x : ℂ) * m / (2 * π) with ht
    set n : ℤ := ⌊t⌋ with hn
    set ψ : ℝ := 2 * π * n / m with hψ
    have hxt : arg (x : ℂ) = c * t := by
      simp only [ht, hc]; field_simp
    have hθ0 : 0 ≤ arg (x : ℂ) - ψ := by
      have : arg (x : ℂ) - ψ = c * (t - n) := by
        rw [hxt]; simp only [hψ, hc]; field_simp
      rw [this]
      exact mul_nonneg hc0.le (by have := Int.floor_le t; linarith)
    have hθc : arg (x : ℂ) - ψ < c := by
      have : arg (x : ℂ) - ψ = c * (t - n) := by
        rw [hxt]; simp only [hψ, hc]; field_simp
      rw [this]
      have : t - n < 1 := by have := Int.lt_floor_add_one t; linarith
      nlinarith
    set ζ : ℂ := Complex.exp (((-ψ : ℝ) : ℂ) * I) with hζ
    have hζm : ζ ^ m = 1 := by
      rw [hζ, ← Complex.exp_nat_mul]
      have : (m : ℂ) * (((-ψ : ℝ) : ℂ) * I) = ((-n : ℤ) : ℂ) * (2 * π * I) := by
        have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
        simp only [hψ]; push_cast; field_simp
      rw [this]
      exact Complex.exp_int_mul_two_pi_mul_I _
    have hζn : ‖ζ‖ = 1 := by rw [hζ]; exact Complex.norm_exp_ofReal_mul_I _
    have hyb : ζ * (x : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_mul, hζn, one_mul]; exact mem_ball_zero_iff.mp x.2
    have hpt : ζ * (x : ℂ) = polarPt ‖(x : ℂ)‖ (arg (x : ℂ) - ψ) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (x : ℂ)]
      simp only [polarPt, hζ]
      rw [show ∀ A B C : ℂ, A * (B * C) = B * (A * C) from fun A B C => by ring, ← Complex.exp_add]
      congr 2
      push_cast; ring
    refine ⟨⟨ζ * (x : ℂ), hyb⟩, ?_, ζ, hζm, rfl⟩
    rw [closure_subtype]
    show ζ * (x : ℂ) ∈ closure (Subtype.val '' D)
    rw [hpt]
    exact haux _ _ (norm_nonneg _) (mem_ball_zero_iff.mp x.2) hθ0 hθc

/-- A finite subgroup of `ℂˣ` of order `m` is the group of `m`-th roots of unity. -/
lemma subgroup_eq_rootsOfUnity (Γ : Subgroup ℂˣ) [Finite Γ] :
    have : NeZero (Nat.card Γ) := ⟨Nat.card_pos.ne'⟩
    Γ = rootsOfUnity (Nat.card Γ) ℂ := by
  have : NeZero (Nat.card Γ) := ⟨Nat.card_pos.ne'⟩
  have hle : Γ ≤ rootsOfUnity (Nat.card Γ) ℂ := by
    intro g hg
    rw [_root_.mem_rootsOfUnity]
    have := pow_card_eq_one' (x := (⟨g, hg⟩ : Γ))
    exact congrArg Subtype.val this
  have hfin : Finite (rootsOfUnity (Nat.card Γ) ℂ) := by
    have := Complex.card_rootsOfUnity (Nat.card Γ)
    exact Nat.finite_of_card_ne_zero (by rw [this]; exact NeZero.ne _)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Complex.card_rootsOfUnity])

/-- **Example 1.2** (pdf p. 182), for a finite group $\Gamma$ of rotations of the unit disk $D$ (a finite subgroup of
$\mathbb C^\times$): $\Gamma$ is cyclic, say of order $m$; $z \mapsto z^m$ separates the orbits and maps $D$ onto
$D$. (Milne's "$\mathrm{Aut}(D) = \{|z| = 1\}$" holds for the automorphisms fixing $0$; a finite group of
automorphisms of $D$ fixes a point and is conjugate to such a group.) -/
@[kb "milne2006ec" "Ch. V, Example 1.2, pdf p. 182"]
theorem example_1_2 (Γ : Subgroup ℂˣ) [Finite Γ] :
    IsCyclic Γ ∧ (∀ z w : ℂ, z ^ Nat.card Γ = w ^ Nat.card Γ ↔ ∃ g ∈ Γ, w = (g : ℂ) * z) ∧
      (fun z : ℂ ↦ z ^ Nat.card Γ) '' Metric.ball 0 1 = Metric.ball 0 1 := by
  have : NeZero (Nat.card Γ) := ⟨Nat.card_pos.ne'⟩
  have hΓ := subgroup_eq_rootsOfUnity Γ
  refine ⟨?_, ?_, ?_⟩
  · rw [hΓ]; infer_instance
  · intro z w
    constructor
    · intro h
      by_cases hz : z = 0
      · subst hz
        have : w ^ Nat.card Γ = 0 := by rw [← h]; simp [NeZero.ne]
        have hw : w = 0 := pow_eq_zero_iff (NeZero.ne _) |>.mp this
        exact ⟨1, Subgroup.one_mem _, by simp [hw]⟩
      · have hw : w ≠ 0 := by
          rintro rfl
          exact hz (pow_eq_zero_iff (NeZero.ne _) |>.mp (by rw [h]; simp [NeZero.ne]))
        refine ⟨Units.mk0 (w / z) (div_ne_zero hw hz), ?_, by simp [hz]⟩
        rw [hΓ, _root_.mem_rootsOfUnity']
        simp only [Units.val_mk0]
        rw [div_pow, ← h, div_self (pow_ne_zero _ hz)]
    · rintro ⟨g, hg, rfl⟩
      have h1 : (g : ℂ) ^ Nat.card Γ = 1 := by
        rw [hΓ, _root_.mem_rootsOfUnity'] at hg
        exact hg
      rw [mul_pow, h1, one_mul]
  · ext w
    simp only [Set.mem_image, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hz (NeZero.ne _)
    · intro hw
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq w (Nat.card_pos (α := Γ))
      refine ⟨z, ?_, hz⟩
      by_contra hcon
      replace hcon := not_lt.mp hcon
      have : 1 ≤ ‖z‖ ^ Nat.card Γ := one_le_pow₀ hcon
      rw [← norm_pow, hz] at this
      linarith

/-- **Example 1.2** (pdf p. 182): the holomorphic functions on the disk invariant under the rotations by $m$-th
roots of unity are the functions $h(z^m)$ with $h$ holomorphic on the disk. -/
@[kb "milne2006ec" "Ch. V, Example 1.2 (invariant holomorphic functions), pdf p. 182"]
theorem example_1_2_invariant {m : ℕ} (hm : 1 ≤ m) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hinv : ∀ ζ : ℂ, ζ ^ m = 1 → ∀ z ∈ Metric.ball (0 : ℂ) 1, f (ζ * z) = f z) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 1) ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, f z = h (z ^ m) := by
  have hm0 : m ≠ 0 := by omega
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
  -- two points of the disk with equal `m`-th powers have the same value
  have L : ∀ s ∈ Metric.ball (0 : ℂ) 1, ∀ t ∈ Metric.ball (0 : ℂ) 1, s ^ m = t ^ m → f s = f t := by
    intro s hs t ht hst
    by_cases h0 : s = 0
    · subst h0
      have : t ^ m = 0 := by rw [← hst]; simp [hm0]
      have : t = 0 := pow_eq_zero_iff hm0 |>.mp this
      rw [this]
    · have hζ : (t / s) ^ m = 1 := by rw [div_pow, ← hst, div_self (pow_ne_zero _ h0)]
      have := hinv (t / s) hζ s hs
      rw [div_mul_cancel₀ _ h0] at this
      exact this.symm
  -- membership in the disk from the `m`-th power
  have hball : ∀ s : ℂ, s ^ m ∈ Metric.ball (0 : ℂ) 1 → s ∈ Metric.ball (0 : ℂ) 1 := by
    intro s hs
    rw [mem_ball_zero_iff, norm_pow] at hs
    rw [mem_ball_zero_iff]
    by_contra hcon
    have := one_le_pow₀ (n := m) (not_lt.mp hcon)
    linarith
  let r : ℂ → ℂ := fun w ↦ w ^ ((m : ℂ)⁻¹)
  have hr : ∀ w, (r w) ^ m = w := fun w ↦ Complex.cpow_nat_inv_pow w hm0
  refine ⟨fun w ↦ f (r w), ?_, ?_⟩
  · rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 0) (s := Metric.ball 0 1)
      (Metric.ball_mem_nhds _ one_pos)]
    constructor
    · intro w0 hw0
      have hw0' : w0 ∈ Metric.ball (0 : ℂ) 1 := hw0.1
      have hw0ne : w0 ≠ 0 := hw0.2
      refine DifferentiableAt.differentiableWithinAt ?_
      set α := Complex.arg w0 with hα
      let c : ℂ := Complex.exp ((α / m : ℝ) * Complex.I)
      let b : ℂ → ℂ := fun w ↦ c * (w * Complex.exp (-(α * Complex.I))) ^ ((m : ℂ)⁻¹)
      have hc : c ^ m = Complex.exp (α * Complex.I) := by
        simp only [c, ← Complex.exp_nat_mul]
        congr 1
        push_cast
        field_simp
      have hb : ∀ w, (b w) ^ m = w := by
        intro w
        simp only [b, mul_pow, hc, Complex.cpow_nat_inv_pow _ hm0]
        rw [mul_comm, mul_assoc, ← Complex.exp_add]
        simp
      have hslit : w0 * Complex.exp (-(α * Complex.I)) ∈ Complex.slitPlane := by
        have : w0 * Complex.exp (-(α * Complex.I)) = ((‖w0‖ : ℝ) : ℂ) := by
          conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w0]
          rw [mul_assoc, ← Complex.exp_add]
          simp [hα]
        rw [this]
        exact Complex.ofReal_mem_slitPlane.mpr (norm_pos_iff.mpr hw0ne)
      have hbd : DifferentiableAt ℂ b w0 := by
        refine DifferentiableAt.const_mul ?_ c
        exact (differentiableAt_id.mul_const _).cpow_const hslit
      have hbball : b w0 ∈ Metric.ball (0 : ℂ) 1 := hball _ (by rw [hb]; exact hw0')
      have hfd : DifferentiableAt ℂ f (b w0) := hf.differentiableAt (Metric.isOpen_ball.mem_nhds hbball)
      have heq : (fun w ↦ f (b w)) =ᶠ[𝓝 w0] (fun w ↦ f (r w)) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hw0'] with w hw
        have h1 : b w ∈ Metric.ball (0 : ℂ) 1 := hball _ (by rw [hb]; exact hw)
        have h2 : r w ∈ Metric.ball (0 : ℂ) 1 := hball _ (by rw [hr]; exact hw)
        exact L _ h1 _ h2 (by rw [hb, hr])
      exact (hfd.comp w0 hbd).congr_of_eventuallyEq heq.symm
    · have hr0 : r 0 = 0 := by simp [r, hmC]
      have hrc : ContinuousAt r 0 :=
        Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by
          have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
          have : ((m : ℂ)⁻¹) = (((m : ℝ)⁻¹ : ℝ) : ℂ) := by simp
          rw [this, Complex.ofReal_re]; positivity)
      have hfc : ContinuousAt f (r 0) := by
        rw [hr0]; exact (hf.differentiableAt (Metric.ball_mem_nhds _ one_pos)).continuousAt
      exact hfc.comp hrc
  · intro z hz
    have hzm : z ^ m ∈ Metric.ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff] at hz ⊢
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hz hm0
    have h2 : r (z ^ m) ∈ Metric.ball (0 : ℂ) 1 := hball _ (by rw [hr]; exact hzm)
    exact L _ hz _ h2 (by rw [hr])

/-- Running text (pdf p. 183): $S^2 = 1$ and $(ST)^3 = 1$ in $\mathrm{SL}_2(\mathbb Z)/\{\pm I\}$; in
$\mathrm{SL}_2(\mathbb Z)$, $S^2 = (ST)^3 = -I$. -/
@[kb "milne2006ec" "Ch. V, §1, S² = (ST)³ = 1 in SL₂(ℤ)/{±I} (running text), pdf p. 183"]
theorem S_sq_ST_cube : S ^ 2 = -1 ∧ (S * T) ^ 3 = -1 := by
  constructor <;> decide

/-- The open fundamental domain `𝒟ᵒ` is connected: it is the continuous image of the connected set
$(-1/2, 1/2) \times (0, \infty)$ under $(x, t) \mapsto x + i(\sqrt{1 - x^2} + t)$. -/
theorem isConnected_fdo : IsConnected (𝒟ᵒ : Set ℍ) := by
  let f : ℝ × ℝ → ℂ := fun p ↦ (p.1 : ℂ) + ((√(1 - p.1 ^ 2) + p.2 : ℝ) : ℂ) * Complex.I
  have hf : Continuous f := by fun_prop
  have hconn : IsConnected (Set.Ioo (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.Ioi (0 : ℝ)) :=
    isConnected_Ioo (by norm_num) |>.prod isConnected_Ioi
  have himg : ((↑) : ℍ → ℂ) '' 𝒟ᵒ = f '' (Set.Ioo (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.Ioi (0 : ℝ)) := by
    rw [ModularGroup.coe_fdo]
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Ioo, Set.mem_Ioi, Prod.exists]
    constructor
    · rintro ⟨him, hn, hre⟩
      rw [abs_lt] at hre
      have hsq : 1 < z.re ^ 2 + z.im ^ 2 := by
        have : 1 < ‖z‖ ^ 2 := by nlinarith
        rwa [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq] at this
      refine ⟨z.re, z.im - √(1 - z.re ^ 2), ⟨⟨by linarith [hre.1], hre.2⟩, ?_⟩, ?_⟩
      · rw [sub_pos, Real.sqrt_lt' him]; nlinarith
      · apply Complex.ext <;> simp [f]
    · rintro ⟨x, t, ⟨hx, ht⟩, rfl⟩
      have h1 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
      have h2 : √(1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt h1.le
      have h3 : 0 ≤ √(1 - x ^ 2) := Real.sqrt_nonneg _
      refine ⟨by simp [f]; positivity, ?_, ?_⟩
      · have : 1 < ‖f (x, t)‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp [f]
          nlinarith
        nlinarith [norm_nonneg (f (x, t))]
      · simp [f, abs_lt]; constructor <;> linarith [hx.1, hx.2]
  have h2 : IsConnected (((↑) : ℍ → ℂ) '' 𝒟ᵒ) := by
    rw [himg]; exact hconn.image f hf.continuousOn
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz⟩ := h2.nonempty
    obtain ⟨w, hw, -⟩ := hz
    exact ⟨w, hw⟩
  · exact (UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image).mp h2.isPreconnected

/-- **Proposition 1.3** (a) (pdf p. 183): $D = \{|z| > 1, |\Re z| < 1/2\}$ (Mathlib's `ModularGroup.fdo`) is a
fundamental domain for $\mathrm{SL}_2(\mathbb Z)$. -/
@[kb "milne2006ec" "Ch. V, Proposition 1.3 (a), pdf p. 183"]
theorem prop_1_3_a : IsFundamentalDomainFor (orbitRelation SL(2, ℤ) ℍ) 𝒟ᵒ := by
  refine ⟨isOpen_fdo, isConnected_fdo, ?_, ?_⟩
  · rintro x hx y hy ⟨g, rfl⟩
    exact eq_smul_self_of_mem_fdo_mem_fdo hx hy
  · intro x
    obtain ⟨g, hg⟩ := exists_smul_mem_fd x
    exact ⟨g • x, by rw [← fd_eq_closure_fdo]; exact hg, g, rfl⟩

/-- The real part of Mathlib's $\rho$ is $-1/2$. -/
lemma re_ρ : (ρ : ℍ).re = -1 / 2 := by simp [ρ]

/-- The real part of $1 + \rho$ is $1/2$. -/
lemma re_ρ' : (((1 : ℝ) +ᵥ ρ : ℍ)).re = 1 / 2 := by
  norm_num [← coe_re, coe_vadd, ρ]

/-- **Proposition 1.3** (a) (pdf p. 183), boundary identifications: two distinct points $z$, $z'$ of the closure
$\bar D$ (Mathlib's `ModularGroup.fd`) are in the same orbit if and only if $\Re z = \pm 1/2$ and
$z' = z \mp 1$, or $|z| = 1$ and $z' = -1/z$. -/
@[kb "milne2006ec" "Ch. V, Proposition 1.3 (a), pdf p. 183"]
theorem prop_1_3_a_boundary {z z' : ℍ} (hz : z ∈ 𝒟) (hz' : z' ∈ 𝒟) (hne : z ≠ z') :
    (∃ g : SL(2, ℤ), g • z = z') ↔
      (z.re = -1 / 2 ∧ z' = T • z) ∨ (z.re = 1 / 2 ∧ z' = T⁻¹ • z) ∨ (‖(z : ℂ)‖ = 1 ∧ z' = S • z) := by
  have hST : (S * T) • ρ = ρ := (stabilizer_ρ.mpr (by simp))
  have hTS : (T⁻¹ * S) • ρ = ρ := (stabilizer_ρ.mpr (by simp))
  have hT1 : T • ρ = (1 : ℝ) +ᵥ ρ := modular_T_smul ρ
  have hSρ : S • ρ = T • ρ := by
    have := hTS
    rw [mul_smul, inv_smul_eq_iff] at this
    exact this
  have hSTρ : S • T • ρ = ρ := by rw [← mul_smul]; exact hST
  have hneg : ∀ g h : SL(2, ℤ), (g = h ∨ g = -h) → ∀ w : ℍ, g • w = h • w := by
    rintro g h (rfl | rfl) w
    · rfl
    · exact SL_neg_smul h w
  constructor
  · rintro ⟨g, rfl⟩
    rcases cases_of_mem_fd_smul_mem_fd hz hz' with h | ⟨h, hre⟩ | ⟨h, hre⟩ | ⟨h, hn⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exfalso; apply hne
      rw [hneg g 1 h]; simp
    · exact Or.inl ⟨hre, hneg g T h z⟩
    · exact Or.inr (Or.inl ⟨hre, hneg g T⁻¹ h z⟩)
    · exact Or.inr (Or.inr ⟨hn, hneg g S h z⟩)
    · exfalso; apply hne
      rw [hneg g (T * S) h, ← hT1]
      simp only [mul_smul, hSTρ]
    · refine Or.inr (Or.inl ⟨re_ρ', ?_⟩)
      rw [hneg g (T⁻¹ * S * T⁻¹) h, ← hT1]
      simp only [mul_smul, inv_smul_smul, hSρ]
    · exfalso; apply hne
      rw [hneg g (S * T⁻¹) h, ← hT1]
      simp only [mul_smul, inv_smul_smul, hSρ]
    · exfalso; apply hne
      rw [hneg g (S * T) h]
      simp only [mul_smul, hSTρ]
    · refine Or.inl ⟨re_ρ, ?_⟩
      rw [hneg g (T * S * T) h]
      simp only [mul_smul, hSTρ]
    · exfalso; apply hne
      rw [hneg g (T⁻¹ * S) h]
      exact hTS.symm
  · rintro (⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩)
    · exact ⟨T, h.symm⟩
    · exact ⟨T⁻¹, h.symm⟩
    · exact ⟨S, h.symm⟩

/-- The six elements $\pm 1$, $\pm x$, $\pm x^2$ lie in the cyclic group generated by an element $x$ with
$x^3 = -I$. -/
lemma six_mem_zpowers {x : SL(2, ℤ)} (hx : x ^ 3 = -1) :
    (1 : SL(2, ℤ)) ∈ Subgroup.zpowers x ∧ (-1 : SL(2, ℤ)) ∈ Subgroup.zpowers x ∧
    x ∈ Subgroup.zpowers x ∧ -x ∈ Subgroup.zpowers x ∧
    x ^ 2 ∈ Subgroup.zpowers x ∧ -x ^ 2 ∈ Subgroup.zpowers x := by
  have h1 : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
  have h3 : (-1 : SL(2, ℤ)) ∈ Subgroup.zpowers x := hx ▸ Subgroup.pow_mem _ h1 3
  have hneg : ∀ y : SL(2, ℤ), y ∈ Subgroup.zpowers x → -y ∈ Subgroup.zpowers x := by
    intro y hy
    have := Subgroup.mul_mem _ h3 hy
    simpa using this
  exact ⟨Subgroup.one_mem _, h3, h1, hneg _ h1, Subgroup.pow_mem _ h1 2, hneg _ (Subgroup.pow_mem _ h1 2)⟩

/-- The matrix $S$ has order $4$. -/
lemma orderOf_S : orderOf S = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 ↦ ?_⟩
  interval_cases m <;> decide

/-- The matrix $ST$ has order $6$. -/
lemma orderOf_ST : orderOf (S * T) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 ↦ ?_⟩
  interval_cases m <;> decide

/-- The matrix $TS$ has order $6$. -/
lemma orderOf_TS : orderOf (T * S) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 ↦ ?_⟩
  interval_cases m <;> decide

/-- The matrix $-I$ has order $2$. -/
lemma orderOf_neg_one : orderOf (-1 : SL(2, ℤ)) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 ↦ ?_⟩
  interval_cases m; decide

/-- The stabilizer of $i$ in $\mathrm{SL}_2(\mathbb Z)$ is generated by $S$. -/
lemma stabilizer_I_eq : MulAction.stabilizer SL(2, ℤ) UpperHalfPlane.I = Subgroup.zpowers S := by
  have hS2 : S ^ 2 = -1 := S_sq_ST_cube.1
  apply le_antisymm
  · intro g hg
    rw [MulAction.mem_stabilizer_iff, stabilizer_I] at hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    have h1 : S ∈ Subgroup.zpowers S := Subgroup.mem_zpowers S
    have h2 : (-1 : SL(2, ℤ)) ∈ Subgroup.zpowers S := hS2 ▸ Subgroup.pow_mem _ h1 2
    rcases hg with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact h2
    · exact h1
    · have := Subgroup.mul_mem _ h2 h1
      simpa using this
  · rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
    exact stabilizer_I.mpr (by simp)

/-- The stabilizer of Mathlib's $\rho$ in $\mathrm{SL}_2(\mathbb Z)$ is generated by $ST$. -/
lemma stabilizer_ρ_eq : MulAction.stabilizer SL(2, ℤ) ρ = Subgroup.zpowers (S * T) := by
  have hx3 : (S * T) ^ 3 = -1 := S_sq_ST_cube.2
  have hx2 : (S * T) ^ 2 = T⁻¹ * S := by decide
  apply le_antisymm
  · intro g hg
    rw [MulAction.mem_stabilizer_iff, stabilizer_ρ] at hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    obtain ⟨h0, hm1, h1, hn1, h2, hn2⟩ := six_mem_zpowers hx3
    rw [hx2] at h2 hn2
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
    exact stabilizer_ρ.mpr (by simp)

/-- The stabilizer of $1 + \rho$ in $\mathrm{SL}_2(\mathbb Z)$ is generated by $TS$. -/
lemma stabilizer_one_add_ρ_eq :
    MulAction.stabilizer SL(2, ℤ) ((1 : ℝ) +ᵥ ρ) = Subgroup.zpowers (T * S) := by
  rw [← modular_T_smul, MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_ρ_eq,
    MonoidHom.map_zpowers]
  congr 1
  simp [MulAut.conj_apply, mul_assoc]

/-- **Proposition 1.3** (b) (pdf p. 183): for $z \in \bar D$ the stabilizer of $z$ is $\{\pm I\}$ unless
$z = i$ (stabilizer $\langle S\rangle$), $z = \rho = e^{2\pi i/6}$ (stabilizer $\langle TS\rangle$) or
$z = \rho^2 = e^{2\pi i/3}$ (stabilizer $\langle ST\rangle$). Milne's $\rho$ is `(1 : ℝ) +ᵥ ρ`, Mathlib's `ρ` is
Milne's $\rho^2$. -/
@[kb "milne2006ec" "Ch. V, Proposition 1.3 (b), pdf p. 183"]
theorem prop_1_3_b :
    MulAction.stabilizer SL(2, ℤ) UpperHalfPlane.I = Subgroup.zpowers S ∧
    MulAction.stabilizer SL(2, ℤ) ((1 : ℝ) +ᵥ ρ) = Subgroup.zpowers (T * S) ∧
    MulAction.stabilizer SL(2, ℤ) ρ = Subgroup.zpowers (S * T) ∧
    ∀ z ∈ 𝒟, z ≠ UpperHalfPlane.I → z ≠ (1 : ℝ) +ᵥ ρ → z ≠ ρ →
      (MulAction.stabilizer SL(2, ℤ) z : Set SL(2, ℤ)) = {1, -1} := by
  refine ⟨stabilizer_I_eq, stabilizer_one_add_ρ_eq, stabilizer_ρ_eq, fun z hz h1 h2 h3 ↦ ?_⟩
  ext g
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hg
    exact stabilizer_of_ne hz hg h1 h3 h2
  · rintro (rfl | rfl)
    · exact one_smul _ _
    · rw [SL_neg_smul, one_smul]

/-- **Proposition 1.3** (c) (pdf p. 183): $\mathrm{SL}_2(\mathbb Z)/\{\pm I\}$ is generated by $S$ and $T$; in fact
$S$ and $T$ generate $\mathrm{SL}_2(\mathbb Z)$ (as $S^2 = -I$). -/
@[kb "milne2006ec" "Ch. V, Proposition 1.3 (c), pdf p. 183"]
theorem prop_1_3_c : Subgroup.closure {S, T} = ⊤ := by
  exact SpecialLinearGroup.SL2Z_generators

/-- Every point of the closed fundamental domain has a stabilizer generated by one element of order
$2$, $4$ or $6$. -/
lemma stabilizer_fd_zpowers {z : ℍ} (hz : z ∈ 𝒟) :
    ∃ x : SL(2, ℤ), MulAction.stabilizer SL(2, ℤ) z = Subgroup.zpowers x ∧ orderOf x ∈ ({2, 4, 6} : Set ℕ) := by
  obtain ⟨hI, hρ', hρ, hrest⟩ := prop_1_3_b
  by_cases h1 : z = UpperHalfPlane.I
  · subst h1; exact ⟨S, hI, by simp [orderOf_S]⟩
  by_cases h2 : z = (1 : ℝ) +ᵥ ρ
  · subst h2; exact ⟨T * S, hρ', by simp [orderOf_TS]⟩
  by_cases h3 : z = ρ
  · subst h3; exact ⟨S * T, hρ, by simp [orderOf_ST]⟩
  refine ⟨-1, ?_, by simp [orderOf_neg_one]⟩
  have := hrest z hz h1 h2 h3
  apply SetLike.coe_injective
  rw [this]
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, SetLike.mem_coe, Subgroup.mem_zpowers_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with h | h
    · exact Or.inl (h.neg_one_zpow)
    · exact Or.inr (h.neg_one_zpow)

/-- Running text (pdf p. 186), from Proposition 1.3 (b): the stabilizer in $\mathrm{SL}_2(\mathbb Z)$ of a point of
$\mathbb H$ is cyclic of order $2$, $4$ or $6$. -/
@[kb "milne2006ec" "Ch. V, §1, stabilizers are cyclic of order 2, 4 or 6 (running text), pdf p. 186"]
theorem stabilizer_cyclic (z : ℍ) :
    IsCyclic (MulAction.stabilizer SL(2, ℤ) z) ∧ Nat.card (MulAction.stabilizer SL(2, ℤ) z) ∈ ({2, 4, 6} : Set ℕ) := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  obtain ⟨x, hx, hxo⟩ := stabilizer_fd_zpowers hg
  have hz : z = g⁻¹ • (g • z) := by simp
  have hst : MulAction.stabilizer SL(2, ℤ) z = Subgroup.zpowers ((MulAut.conj g⁻¹) x) := by
    rw [hz, MulAction.stabilizer_smul_eq_stabilizer_map_conj, hx, MonoidHom.map_zpowers]
    rfl
  have ho : orderOf ((MulAut.conj g⁻¹) x) = orderOf x := MulEquiv.orderOf_eq _ _
  rw [hst]
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_zpowers, ho]
  exact hxo

/-- The group $\mathrm{SL}_2(\mathbb Z)$ acts properly discontinuously on the upper half plane. -/
instance properlyDiscontinuousSL2Z : ProperlyDiscontinuousSMul SL(2, ℤ) ℍ := by
  rw [properlyDiscontinuousSMul_iff]
  intro K L hK hL
  have h := (properlyDiscontinuousSL2ZRange.finite_disjoint_inter_image hK hL)
  have hinj : Function.Injective (fun g : SL(2, ℤ) ↦ (⟨mapGL ℝ g, g, rfl⟩ : 𝒮ℒ)) := by
    intro a b hab
    have := congrArg Subtype.val hab
    exact mapGL_injective this
  refine (h.preimage (hinj.injOn)).subset ?_
  intro g hg
  obtain ⟨_, ⟨x, hx, rfl⟩, hxL⟩ := hg
  exact ⟨_, ⟨x, hx, rfl⟩, hxL⟩

/-- The group $\mathrm{SL}_2(\mathbb Z)$ acts continuously on the upper half plane. -/
instance : ContinuousConstSMul SL(2, ℤ) ℍ :=
  ⟨fun g ↦ by
    have : Continuous fun x : ℍ => (mapGL ℝ g) • x := continuous_const_smul (mapGL ℝ g)
    exact this⟩

/-- A subgroup of $\mathrm{SL}_2(\mathbb Z)$ acts continuously on the upper half plane. -/
instance (Γ : Subgroup SL(2, ℤ)) : ContinuousConstSMul Γ ℍ :=
  ⟨fun g ↦ continuous_const_smul (g : SL(2, ℤ))⟩

/-- A subgroup of $\mathrm{SL}_2(\mathbb Z)$ acts properly discontinuously on the upper half plane. -/
instance (Γ : Subgroup SL(2, ℤ)) : ProperlyDiscontinuousSMul Γ ℍ := by
  rw [properlyDiscontinuousSMul_iff]
  intro K L hK hL
  refine ((properlyDiscontinuousSL2Z.finite_disjoint_inter_image hK hL).preimage
    (Subtype.val_injective.injOn)).subset ?_
  intro g hg
  exact hg

/-- **Remark 1.4** (pdf p. 183), first part: if $\mathrm{SL}_2(\mathbb Z) = \bigsqcup_i \Gamma\gamma_i$ then
$D' = \bigcup_i \gamma_iD$ is open, no two of its points are in the same $\Gamma$-orbit, and its closure meets every
$\Gamma$-orbit. The hypothesis $-I \in \Gamma$ is needed (erratum): otherwise $\gamma$ and $-\gamma$ lie in different
cosets with $\gamma D = -\gamma D$; it holds for $\Gamma_0(N)$. -/
@[kb "milne2006ec" "Ch. V, Remark 1.4, pdf p. 183"]
theorem remark_1_4 (Γ : Subgroup SL(2, ℤ)) (hΓ : -1 ∈ Γ) (R : Set SL(2, ℤ))
    (hR : ∀ g : SL(2, ℤ), ∃! r, r ∈ R ∧ g * r⁻¹ ∈ Γ) :
    IsOpen (⋃ r ∈ R, r • 𝒟ᵒ) ∧
    (∀ x ∈ ⋃ r ∈ R, r • 𝒟ᵒ, ∀ y ∈ ⋃ r ∈ R, r • 𝒟ᵒ, (∃ γ ∈ Γ, γ • x = y) → x = y) ∧
    ∀ x : ℍ, ∃ γ ∈ Γ, γ • x ∈ closure (⋃ r ∈ R, r • 𝒟ᵒ) := by
  refine ⟨?_, ?_, ?_⟩
  · refine isOpen_biUnion fun r _ ↦ ?_
    exact (isOpenMap_smul r) _ isOpen_fdo
  · intro x hx y hy ⟨γ, hγ, hγxy⟩
    simp only [Set.mem_iUnion] at hx hy
    obtain ⟨r, hr, a, ha, rfl⟩ := hx
    obtain ⟨r', hr', b, hb, rfl⟩ := hy
    -- (r'⁻¹ γ r) a = b
    have hγxy' : γ • r • a = r' • b := hγxy
    have h1 : (r'⁻¹ * γ * r) • a = b := by
      calc (r'⁻¹ * γ * r) • a = r'⁻¹ • (γ • r • a) := by simp [mul_smul]
        _ = b := by rw [hγxy', inv_smul_smul]
    have hk := eq_one_or_neg_one_of_mem_fdo_mem_fdo ha (h1 ▸ hb)
    have hγ' : r' * r⁻¹ ∈ Γ := by
      have e : γ = r' * (r'⁻¹ * γ * r) * r⁻¹ := by group
      rcases hk with h | h
      · rw [h] at e; simp at e; rw [← e]; exact hγ
      · rw [h] at e
        have : r' * r⁻¹ = -γ := by
          have e2 : r' * (-1 : SL(2, ℤ)) * r⁻¹ = -(r' * r⁻¹) := by simp
          rw [e2] at e
          rw [e]; simp
        rw [this]; have := Γ.mul_mem hΓ hγ; simpa using this
    obtain ⟨r0, h0, huniq⟩ := hR r'
    have e1 := huniq r ⟨hr, hγ'⟩
    have e2 := huniq r' ⟨hr', by simp [Γ.one_mem]⟩
    have hrr : r = r' := e1.trans e2.symm
    subst hrr
    rcases hk with h | h
    · rw [h] at h1; simp at h1; rw [h1]
    · rw [h, SL_neg_smul, one_smul] at h1; rw [h1]
  · intro x
    obtain ⟨h, hh⟩ := exists_smul_mem_fd x
    obtain ⟨r, ⟨hr, hrΓ⟩, -⟩ := hR h⁻¹
    refine ⟨r * h, ?_, ?_⟩
    · have := Γ.inv_mem hrΓ
      simpa using this
    · rw [mul_smul]
      have : r • (h • x) ∈ r • 𝒟 := Set.smul_mem_smul_set hh
      rw [fd_eq_closure_fdo, ← Set.image_smul] at this
      obtain ⟨y, hy, hyeq⟩ := this
      have h3 : (fun w : ℍ => r • w) '' closure 𝒟ᵒ ⊆ closure ((fun w : ℍ => r • w) '' 𝒟ᵒ) :=
        image_closure_subset_closure_image (continuous_const_smul r)
      have h4 := h3 ⟨y, hy, rfl⟩
      have h5 : closure ((fun w : ℍ => r • w) '' 𝒟ᵒ) ⊆ closure (⋃ r ∈ R, r • 𝒟ᵒ) := by
        apply closure_mono
        rw [Set.image_smul]
        exact Set.subset_biUnion_of_mem (u := fun r => r • 𝒟ᵒ) hr
      rw [← hyeq]
      exact h5 h4

/-- **Remark 1.4** (pdf p. 183), second part, a named statement: for $\Gamma$ of finite index in
$\mathrm{SL}_2(\mathbb Z)$ the coset representatives can be chosen so that the closure of $D'$ is connected, and
then the interior of the closure is a fundamental domain for $\Gamma$. -/
@[kb "milne2006ec" "Ch. V, Remark 1.4 (connected choice), pdf p. 183"]
structure Remark1_4Connected : Prop where
  exists_reps : ∀ (Γ : Subgroup SL(2, ℤ)), Γ.FiniteIndex → ∃ R : Set SL(2, ℤ),
    (∀ g : SL(2, ℤ), ∃! r, r ∈ R ∧ g * r⁻¹ ∈ Γ) ∧ IsConnected (closure (⋃ r ∈ R, r • 𝒟ᵒ)) ∧
    IsFundamentalDomainFor (fun x y : ℍ ↦ ∃ γ ∈ Γ, γ • x = y) (interior (closure (⋃ r ∈ R, r • 𝒟ᵒ)))

/-- **Proposition 1.5** (pdf p. 185), for a subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb Z)$ (finite index is not
needed): (a) for compact $A$, $B \subset \mathbb H$, only finitely many $\gamma \in \Gamma$ have
$\gamma A \cap B \ne \emptyset$; (b) every $z$ has a neighbourhood $U$ with $\gamma U \cap U = \emptyset$ unless
$\gamma z = z$; (c) points $x$, $y$ in different orbits have neighbourhoods $U$, $V$ with
$\gamma U \cap V = \emptyset$ for all $\gamma \in \Gamma$. -/
@[kb "milne2006ec" "Ch. V, Proposition 1.5, pdf p. 185"]
theorem prop_1_5 (Γ : Subgroup SL(2, ℤ)) :
    (∀ A B : Set ℍ, IsCompact A → IsCompact B → {γ : Γ | ((γ : SL(2, ℤ)) • A ∩ B).Nonempty}.Finite) ∧
    (∀ z : ℍ, ∃ U ∈ 𝓝 z, ∀ γ ∈ Γ, γ • z ≠ z → Disjoint (γ • U) U) ∧
    (∀ x y : ℍ, (∀ γ ∈ Γ, γ • x ≠ y) → ∃ U ∈ 𝓝 x, ∃ V ∈ 𝓝 y, ∀ γ ∈ Γ, Disjoint (γ • U) V) := by
  refine ⟨fun A B hA hB ↦ ?_, fun z ↦ ?_, fun x y hxy ↦ ?_⟩
  · have := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ) (T := ℍ) hA hB
    simp only [Set.image_smul] at this
    exact this
  · obtain ⟨U, hU, h⟩ := ProperlyDiscontinuousSMul.exists_nhds_disjoint_image Γ z
    refine ⟨U, hU, fun γ hγ hne ↦ ?_⟩
    have := h ⟨γ, hγ⟩ hne
    simp only [Set.image_smul] at this
    exact this
  · have hT2 : T2Space (Quotient (MulAction.orbitRel Γ ℍ)) := inferInstance
    have hne : (Quotient.mk (MulAction.orbitRel Γ ℍ) x) ≠ Quotient.mk (MulAction.orbitRel Γ ℍ) y := by
      intro h
      obtain ⟨g, hg⟩ := Quotient.exact h
      exact hxy g⁻¹ (Γ.inv_mem g.2) (inv_smul_eq_iff.mpr hg.symm)
    obtain ⟨U', V', hU', hV', hxU, hyV, hUV⟩ := t2_separation hne
    have hq : Continuous (Quotient.mk (MulAction.orbitRel Γ ℍ)) := continuous_quot_mk
    refine ⟨_, (hU'.preimage hq).mem_nhds hxU, _, (hV'.preimage hq).mem_nhds hyV, fun γ hγ ↦ ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ hv
    refine Set.disjoint_left.mp hUV hu ?_
    have : Quotient.mk (MulAction.orbitRel Γ ℍ) (γ • u) = Quotient.mk (MulAction.orbitRel Γ ℍ) u :=
      Quotient.sound ⟨⟨γ, hγ⟩, rfl⟩
    rw [← this]; exact hv

/-- **Corollary 1.6** (pdf p. 185): $\Gamma\backslash\mathbb H$ is Hausdorff (Mathlib:
`t2Space_of_properlyDiscontinuousSMul_of_t2Space` with the proper discontinuity of arithmetic groups). -/
@[kb "milne2006ec" "Ch. V, Corollary 1.6, pdf p. 185"]
theorem cor_1_6 (Γ : Subgroup SL(2, ℤ)) : T2Space (Quotient (MulAction.orbitRel Γ ℍ)) := by
  infer_instance

/-- Running text (pdf p. 186): if $z$ and $\gamma z$ both lie in $\{\Im z > 2\}$ for
$\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(\mathbb Z)$ then $c = 0$, so
$\gamma = \pm\begin{pmatrix}1&m\\0&1\end{pmatrix}$. -/
@[kb "milne2006ec" "Ch. V, §1, the chart at ∞ (running text), pdf p. 186"]
theorem c_eq_zero_of_im_gt_two {γ : SL(2, ℤ)} {z : ℍ} (hz : 2 < z.im) (hγz : 2 < (γ • z).im) :
    γ 1 0 = 0 ∧ ∃ m : ℤ, γ = T ^ m ∨ γ = -T ^ m := by
  have hc : γ 1 0 = 0 := by
    by_contra hc
    have h1 : (1:ℝ) ≤ |(γ 1 0 : ℝ)| := by
      have : (1:ℤ) ≤ |γ 1 0| := Int.one_le_abs hc
      exact_mod_cast this
    rw [ModularGroup.im_smul_eq_div_normSq] at hγz
    have hN := normSq_denom_pos γ z.im_ne_zero
    have h2 : ((γ 1 0 : ℝ) * z.im) ^ 2 ≤ Complex.normSq (denom (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (z : ℂ)) := by
      simpa using z.c_mul_im_sq_le_normSq_denom γ
    rw [lt_div_iff₀ hN] at hγz
    have h3 : (1:ℝ) ≤ (γ 1 0 : ℝ)^2 := by nlinarith [sq_abs (γ 1 0 : ℝ)]
    have hz0 : 0 < z.im := z.im_pos
    nlinarith [mul_pow (γ 1 0 : ℝ) z.im 2]
  refine ⟨hc, ?_⟩
  have had := γ.det_coe
  replace had : γ 0 0 * γ 1 1 = 1 := by rw [Matrix.det_fin_two, hc] at had; lia
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with (⟨ha, hd⟩ | ⟨ha, hd⟩)
  · refine ⟨γ 0 1, Or.inl ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, coe_T_zpow, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]
  · refine ⟨-(γ 0 1), Or.inr ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ha, hc, hd, coe_T_zpow, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]

/-- A matrix of $\mathrm{SL}_2(\mathbb Z)$ whose first column is a given coprime pair. -/
lemma exists_sl_first_col (a d : ℤ) (h : IsCoprime a d) :
    ∃ γ : SL(2, ℤ), γ 0 0 = a ∧ γ 1 0 = d := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨⟨!![a, -y; d, x], by simp [Matrix.det_fin_two]; linarith⟩, ?_, ?_⟩ <;> simp

/-- Running text (pdf p. 184): $\mathrm{SL}_2(\mathbb Z)$ acts transitively on the cusps
$\mathbb P^1(\mathbb Q) = \mathbb Q \cup \{\infty\}$ (passing from $\mathbb H$ to $\mathbb H^*$ adds one orbit). -/
@[kb "milne2006ec" "Ch. V, §1, the cusps form one SL₂(ℤ)-orbit (running text), pdf p. 184"]
theorem cusps_one_orbit (c : OnePoint ℚ) : ∃ γ : SL(2, ℤ), mapGL ℚ γ • (OnePoint.infty : OnePoint ℚ) = c := by
  induction c using OnePoint.rec with
  | infty => exact ⟨1, by simp⟩
  | coe r =>
    obtain ⟨γ, h1, h2⟩ := exists_sl_first_col r.num r.den (by
      rw [Int.isCoprime_iff_gcd_eq_one]; exact r.reduced)
    refine ⟨γ, ?_⟩
    have hd : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
    rw [OnePoint.smul_infty_eq_ite]
    simp [h1, h2, hd, Rat.num_div_den]

/-- **Exercise 1.10** (a) (pdf p. 188): for a prime $p$, $\Gamma_0(p)$ has exactly two orbits on
$\mathbb P^1(\mathbb Q)$, represented by $0$ and $\infty$ (so $X_0(p) \smallsetminus Y_0(p)$ has two points). -/
@[kb "milne2006ec" "Ch. V, Exercise 1.10 (a), pdf p. 188"]
theorem exercise_1_10_a {p : ℕ} (hp : p.Prime) :
    (∀ c : OnePoint ℚ, ∃ γ ∈ CongruenceSubgroup.Gamma0 p,
      mapGL ℚ γ • (OnePoint.infty : OnePoint ℚ) = c ∨ mapGL ℚ γ • ((0 : ℚ) : OnePoint ℚ) = c) ∧
    ∀ γ ∈ CongruenceSubgroup.Gamma0 p, mapGL ℚ γ • (OnePoint.infty : OnePoint ℚ) ≠ ((0 : ℚ) : OnePoint ℚ) := by
  constructor
  · intro c
    induction c using OnePoint.rec with
    | infty => exact ⟨1, Subgroup.one_mem _, Or.inl (by simp)⟩
    | coe r =>
      have hd : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
      have hcop : IsCoprime r.num (r.den : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]; exact r.reduced
      by_cases hpd : (p : ℤ) ∣ r.den
      · obtain ⟨γ, h1, h2⟩ := exists_sl_first_col r.num r.den hcop
        refine ⟨γ, ?_, Or.inl ?_⟩
        · rw [CongruenceSubgroup.Gamma0_mem, h2]
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpd
        · rw [OnePoint.smul_infty_eq_ite]
          simp [h1, h2, hd, Rat.num_div_den]
      · have hc1 : IsCoprime (r.den : ℤ) r.num := hcop.symm
        have hc2 : IsCoprime (r.den : ℤ) (p : ℤ) := by
          have h1 : Nat.Coprime p r.den :=
            (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h ↦ hpd (by exact_mod_cast h))
          exact Nat.isCoprime_iff_coprime.mpr h1.symm
        obtain ⟨u, v, huv⟩ := hc1.mul_right hc2
        have hdet : (!![u, r.num; (p : ℤ) * -v, (r.den : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
          simp [Matrix.det_fin_two]; linarith
        obtain ⟨γ0, h00, h01, h10, h11⟩ : ∃ γ : SL(2, ℤ), γ 0 0 = u ∧ γ 0 1 = r.num ∧
            γ 1 0 = (p : ℤ) * -v ∧ γ 1 1 = (r.den : ℤ) :=
          ⟨⟨!![u, r.num; (p : ℤ) * -v, (r.den : ℤ)], hdet⟩, rfl, rfl, rfl, rfl⟩
        refine ⟨γ0, ?_, Or.inr ?_⟩
        · rw [CongruenceSubgroup.Gamma0_mem, h10]
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (dvd_mul_right _ _)
        · rw [OnePoint.smul_some_eq_ite]
          simp [h01, h11, hd, Rat.num_div_den]
  · intro γ hγ
    rw [CongruenceSubgroup.Gamma0_mem] at hγ
    rw [OnePoint.smul_infty_eq_ite]
    by_cases h : ((mapGL ℚ γ : GL (Fin 2) ℚ) 1 0) = 0
    · simp [h]
    · simp only [h, ite_false]
      intro h0
      simp at h0
      have h' : γ 1 0 ≠ 0 := by intro e; apply h; simp [e]
      rcases h0 with h0 | h0
      · have h0 : γ 0 0 = 0 := by exact_mod_cast h0
        have hdet := γ.det_coe
        rw [Matrix.det_fin_two, h0] at hdet
        have hdvd : (p : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hγ
        have : (p : ℤ) ∣ 1 := by
          have h2 : (p : ℤ) ∣ γ 0 1 * γ 1 0 := Dvd.dvd.mul_left hdvd _
          have h3 : γ 0 1 * γ 1 0 = -1 := by linarith
          rw [h3] at h2
          simpa using h2
        have := Int.eq_one_of_dvd_one (by positivity) this
        exact hp.one_lt.ne' (by exact_mod_cast this)
      · exact h' (by exact_mod_cast h0)

end NumberFieldKB.MilneEC.V
