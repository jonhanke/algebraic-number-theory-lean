import NumberFieldKB.MilneEC.Ch3Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Milne, Elliptic Curves, Chapter III, Example 3.2: the Riemann sphere

Example 3.2 of Milne, *Elliptic Curves* (`milne2006ec`, pdf p. 98): stereographic projections
from the north and south poles give the unit sphere `S² ⊂ ℝ³` a complex structure (the Riemann
sphere), and `S²` is identified with `ℙ¹(ℂ)`.

Two corrections to the text:
* the projection from the south pole must be taken as `(x, y, z) ↦ (x − iy)/(1 + z)` (the complex
  conjugate of the naive formula `(x + iy)/(1 + z)`): with the conjugate, the change of
  coordinates is `w ↦ 1/w`, holomorphic on `ℂ ∖ {0}`; without it, the change is `w ↦ 1/w̄`, which
  is not holomorphic, and the two charts are not compatible;
* the identification with `ℙ¹(ℂ)` is `P ↦ (σ(P) : 1)` for `P ≠ N` and `N ↦ (1 : 0)`, where `σ` is
  the projection from the north pole; the text's `(x, y, z) ↦ (x : y : z)` is a map to `ℙ²(ℝ)`.
-/

open Complex

namespace NumberFieldKB.MilneEC.III

/-- The unit sphere `S² : X² + Y² + Z² = 1` in `ℝ³`. -/
def unitSphere : Set (ℝ × ℝ × ℝ) := {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 1}

/-- The north pole `(0, 0, 1)`. -/
def northPole : ℝ × ℝ × ℝ := (0, 0, 1)

/-- The south pole `(0, 0, -1)`. -/
def southPole : ℝ × ℝ × ℝ := (0, 0, -1)

/-- Stereographic projection from the north pole, `(x, y, z) ↦ (x + iy)/(1 − z)` (Milne,
pdf p. 98). -/
@[kb "milne2006ec" "Ch. III, Example 3.2, stereographic projection, pdf p. 98"]
noncomputable def stereoNorth (p : ℝ × ℝ × ℝ) : ℂ := (p.1 + p.2.1 * I) / (1 - p.2.2)

/-- Stereographic projection from the south pole, conjugated: `(x, y, z) ↦ (x − iy)/(1 + z)`. -/
@[kb "milne2006ec" "Ch. III, Example 3.2, stereographic projection from the south pole, pdf p. 98"]
noncomputable def stereoSouth (p : ℝ × ℝ × ℝ) : ℂ := (p.1 - p.2.1 * I) / (1 + p.2.2)

/-- Inverse of the projection from the north pole. -/
noncomputable def invN (w : ℂ) : ℝ × ℝ × ℝ :=
  (2 * w.re / (Complex.normSq w + 1), 2 * w.im / (Complex.normSq w + 1),
    (Complex.normSq w - 1) / (Complex.normSq w + 1))

/-- The reflection `(x, y, z) ↦ (x, -y, -z)` swapping the poles. -/
def refl (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (p.1, -p.2.1, -p.2.2)

lemma refl_refl (p : ℝ × ℝ × ℝ) : refl (refl p) = p := by
  simp [refl]

lemma stereoSouth_eq (p : ℝ × ℝ × ℝ) : stereoSouth p = stereoNorth (refl p) := by
  unfold stereoSouth stereoNorth refl
  push_cast
  ring

lemma refl_mem {p : ℝ × ℝ × ℝ} (hp : p ∈ unitSphere) : refl p ∈ unitSphere := by
  simp only [unitSphere, Set.mem_ofPred_eq, refl] at hp ⊢
  linarith

lemma sN_re (p : ℝ × ℝ × ℝ) : (stereoNorth p).re = p.1 / (1 - p.2.2) := by
  have : stereoNorth p =
      (((p.1 / (1 - p.2.2) : ℝ) : ℂ)) + ((p.2.1 / (1 - p.2.2) : ℝ) : ℂ) * I := by
    unfold stereoNorth; push_cast; ring
  rw [this]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

lemma sN_im (p : ℝ × ℝ × ℝ) : (stereoNorth p).im = p.2.1 / (1 - p.2.2) := by
  have : stereoNorth p =
      (((p.1 / (1 - p.2.2) : ℝ) : ℂ)) + ((p.2.1 / (1 - p.2.2) : ℝ) : ℂ) * I := by
    unfold stereoNorth; push_cast; ring
  rw [this]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re]
  ring

lemma z_ne_one {p : ℝ × ℝ × ℝ} (hp : p ∈ unitSphere) (h : p ≠ northPole) : p.2.2 ≠ 1 := by
  intro hz
  apply h
  simp only [unitSphere, Set.mem_ofPred_eq] at hp
  have hx : p.1 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2.1]
  have hy : p.2.1 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2.1]
  exact Prod.ext hx (Prod.ext hy hz)

lemma z_ne_neg_one {p : ℝ × ℝ × ℝ} (hp : p ∈ unitSphere) (h : p ≠ southPole) :
    p.2.2 ≠ -1 := by
  intro hz
  have h1 := z_ne_one (refl_mem hp) (fun h' => h (by
    have := congrArg refl h'
    rw [refl_refl] at this
    rw [this]; simp [refl, northPole, southPole]))
  apply h1
  simp [refl, hz]

lemma normSq_sN {p : ℝ × ℝ × ℝ} (hp : p ∈ unitSphere) (hz : p.2.2 ≠ 1) :
    Complex.normSq (stereoNorth p) = (1 + p.2.2) / (1 - p.2.2) := by
  have h1 : (1 - p.2.2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  simp only [unitSphere, Set.mem_ofPred_eq] at hp
  rw [Complex.normSq_apply, sN_re, sN_im]
  field_simp
  nlinarith [hp]

lemma sN_invN (w : ℂ) : stereoNorth (invN w) = w := by
  have hn : 0 ≤ Complex.normSq w := Complex.normSq_nonneg w
  have h1 : Complex.normSq w + 1 ≠ 0 := by positivity
  have h2 : 1 - (Complex.normSq w - 1) / (Complex.normSq w + 1) ≠ 0 := by
    rw [sub_ne_zero]; intro h
    field_simp at h; linarith
  apply Complex.ext
  · rw [sN_re]; simp only [invN]; field_simp; ring
  · rw [sN_im]; simp only [invN]; field_simp; ring

lemma invN_mem (w : ℂ) : invN w ∈ unitSphere := by
  have hn : 0 ≤ Complex.normSq w := Complex.normSq_nonneg w
  have h1 : Complex.normSq w + 1 ≠ 0 := by positivity
  simp only [unitSphere, Set.mem_ofPred_eq, invN]
  rw [Complex.normSq_apply] at *
  field_simp
  ring

lemma invN_z_ne_one (w : ℂ) : (invN w).2.2 ≠ 1 := by
  have hn : 0 ≤ Complex.normSq w := Complex.normSq_nonneg w
  have h1 : Complex.normSq w + 1 ≠ 0 := by positivity
  simp only [invN]
  intro h
  field_simp at h
  linarith

lemma invN_sN {p : ℝ × ℝ × ℝ} (hp : p ∈ unitSphere) (hz : p.2.2 ≠ 1) :
    invN (stereoNorth p) = p := by
  have h1 : (1 - p.2.2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h2 : (1 + p.2.2) / (1 - p.2.2) + 1 ≠ 0 := by
    have : (1 + p.2.2) / (1 - p.2.2) + 1 = 2 / (1 - p.2.2) := by field_simp; ring
    rw [this]; exact div_ne_zero two_ne_zero h1
  have h3 : (1 + p.2.2) + (1 - p.2.2) ≠ 0 := by ring_nf; norm_num
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [invN]; rw [normSq_sN hp hz, sN_re]; field_simp; ring
  · simp only [invN]; rw [normSq_sN hp hz, sN_im]; field_simp; ring
  · simp only [invN]; rw [normSq_sN hp hz]; field_simp; ring

/-- Example 3.2 (Milne, pdf p. 98), the charts: each projection is a bijection from the sphere
minus its pole onto `ℂ`. -/
@[kb "milne2006ec" "Ch. III, Example 3.2, pdf p. 98"]
theorem example_3_2_bijOn :
    Set.BijOn stereoNorth (unitSphere \ {northPole}) Set.univ ∧
      Set.BijOn stereoSouth (unitSphere \ {southPole}) Set.univ := by
  have hN : Set.BijOn stereoNorth (unitSphere \ {northPole}) Set.univ := by
    refine ⟨fun _ _ => trivial, ?_, ?_⟩
    · intro a ha b hb hab
      have := congrArg invN hab
      rwa [invN_sN ha.1 (z_ne_one ha.1 ha.2), invN_sN hb.1 (z_ne_one hb.1 hb.2)] at this
    · intro w _
      refine ⟨invN w, ⟨invN_mem w, ?_⟩, sN_invN w⟩
      intro h
      apply invN_z_ne_one w
      rw [Set.mem_singleton_iff] at h
      rw [h]; rfl
  refine ⟨hN, ?_, ?_, ?_⟩
  · exact fun _ _ => trivial
  · intro a ha b hb hab
    rw [stereoSouth_eq, stereoSouth_eq] at hab
    have hne : ∀ q, q ∈ unitSphere \ {southPole} → refl q ∈ unitSphere \ {northPole} := by
      intro q hq
      refine ⟨refl_mem hq.1, ?_⟩
      intro h
      apply hq.2
      have := congrArg refl h
      rw [refl_refl] at this
      rw [this]; simp [refl, northPole, southPole]
    have := hN.injOn (hne a ha) (hne b hb) hab
    have := congrArg refl this
    rwa [refl_refl, refl_refl] at this
  · intro w _
    obtain ⟨q, hq, hqw⟩ := hN.surjOn (Set.mem_univ w)
    refine ⟨refl q, ⟨refl_mem hq.1, ?_⟩, ?_⟩
    · intro h
      apply hq.2
      have := congrArg refl h
      rw [refl_refl] at this
      rw [this]; simp [refl, northPole, southPole]
    · rw [stereoSouth_eq, refl_refl]; exact hqw

lemma sN_ne_zero {p : ℝ × ℝ × ℝ} (hp : p ∈ unitSphere) (h1 : p.2.2 ≠ 1) (h2 : p.2.2 ≠ -1) :
    stereoNorth p ≠ 0 := by
  intro h
  have h3 := normSq_sN hp h1
  have hz : 1 - p.2.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [h, map_zero] at h3
  rcases div_eq_zero_iff.mp h3.symm with h4 | h4
  · exact h2 (by linarith)
  · exact hz h4

lemma sS_eq_inv {p : ℝ × ℝ × ℝ} (hp : p ∈ unitSphere) (h1 : p.2.2 ≠ 1) (h2 : p.2.2 ≠ -1) :
    stereoSouth p = (stereoNorth p)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have hc : (p.1 : ℂ) ^ 2 + (p.2.1 : ℂ) ^ 2 + (p.2.2 : ℂ) ^ 2 = 1 := by
    simp only [unitSphere, Set.mem_ofPred_eq] at hp
    exact_mod_cast hp
  have e1 : (1 - (p.2.2 : ℂ)) ≠ 0 := by
    intro h; apply h1; exact_mod_cast (sub_eq_zero.mp h).symm
  have e2 : (1 + (p.2.2 : ℂ)) ≠ 0 := by
    intro h; apply h2; exact_mod_cast eq_neg_of_add_eq_zero_right h
  unfold stereoNorth stereoSouth
  field_simp
  linear_combination hc + (-(p.2.1 : ℂ) ^ 2) * Complex.I_sq

/-- Example 3.2 (Milne, pdf p. 98), compatibility: on the sphere minus both poles,
`σ_S = 1/σ_N`, so the change of coordinates `σ_S ∘ σ_N⁻¹ : w ↦ 1/w` and its inverse are
holomorphic on `σ_N(S² ∖ {N, S}) = ℂ ∖ {0}`; the two charts define a complex structure. -/
@[kb "milne2006ec" "Ch. III, Example 3.2, pdf p. 98"]
theorem example_3_2_transition :
    (∀ p ∈ unitSphere, p ≠ northPole → p ≠ southPole →
      stereoNorth p ≠ 0 ∧ stereoSouth p = (stereoNorth p)⁻¹) ∧
      stereoNorth '' (unitSphere \ {northPole, southPole}) = {0}ᶜ ∧
      DifferentiableOn ℂ (fun w : ℂ => w⁻¹) {0}ᶜ := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp hN hS
    exact ⟨sN_ne_zero hp (z_ne_one hp hN) (z_ne_neg_one hp hS),
      sS_eq_inv hp (z_ne_one hp hN) (z_ne_neg_one hp hS)⟩
  · ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hp
      exact sN_ne_zero hp.1 (z_ne_one hp.1 hp.2.1) (z_ne_neg_one hp.1 hp.2.2)
    · intro hw
      have hw' : w ≠ 0 := hw
      have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw'
      have h1 : Complex.normSq w + 1 ≠ 0 := by positivity
      refine ⟨invN w, ⟨invN_mem w, ?_⟩, sN_invN w⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro h
        apply invN_z_ne_one w
        rw [h]; rfl
      · intro h
        have h' := congrArg (fun q : ℝ × ℝ × ℝ => q.2.2) h
        simp only [invN, southPole] at h'
        field_simp at h'
        linarith
  · intro w hw
    exact (differentiableAt_inv (show w ≠ 0 from hw)).differentiableWithinAt

/-- The identification `S² → ℙ¹(ℂ)` of Example 3.2: `P ↦ (σ_N(P) : 1)`, `N ↦ (1 : 0)`. -/
noncomputable def sphereToProj (p : ℝ × ℝ × ℝ) : Projectivization ℂ (Fin 2 → ℂ) := by
  classical
  exact if p = northPole then Projectivization.mk ℂ (![1, 0] : Fin 2 → ℂ) (by simp)
    else Projectivization.mk ℂ (![stereoNorth p, 1] : Fin 2 → ℂ) (by simp)

lemma sphereToProj_north :
    sphereToProj northPole = Projectivization.mk ℂ (![1, 0] : Fin 2 → ℂ) (by simp) := by
  unfold sphereToProj; simp

lemma sphereToProj_of_ne {p : ℝ × ℝ × ℝ} (h : p ≠ northPole) :
    sphereToProj p = Projectivization.mk ℂ (![stereoNorth p, 1] : Fin 2 → ℂ) (by simp) := by
  unfold sphereToProj; simp [h]

/-- Example 3.2 (Milne, pdf p. 98): `S² ≅ ℙ¹(ℂ)`; the map `P ↦ (σ_N(P) : 1)`, `N ↦ (1 : 0)` is a
bijection, and in the standard charts `(u : v) ↦ u/v`, `(u : v) ↦ v/u` of `ℙ¹(ℂ)` it is the chart
`σ_N`, resp. (away from `N`, `S`) the chart `σ_S`. -/
@[kb "milne2006ec" "Ch. III, Example 3.2, S² ≅ P¹(C), pdf p. 98"]
theorem example_3_2_proj :
    Set.BijOn sphereToProj unitSphere Set.univ ∧
      ∀ p ∈ unitSphere, p ≠ northPole → p ≠ southPole →
        sphereToProj p = Projectivization.mk ℂ (![1, stereoSouth p] : Fin 2 → ℂ) (by simp) := by
  refine ⟨⟨fun _ _ => trivial, ?_, ?_⟩, ?_⟩
  · intro a ha b hb h
    by_cases hna : a = northPole <;> by_cases hnb : b = northPole
    · rw [hna, hnb]
    · rw [hna, sphereToProj_north, sphereToProj_of_ne hnb,
        Projectivization.mk_eq_mk_iff'] at h
      obtain ⟨c, hc⟩ := h
      have h1 := congrFun hc 1
      have h0 := congrFun hc 0
      simp at h1 h0
      rw [h1] at h0
      simp at h0
    · rw [hnb, sphereToProj_north, sphereToProj_of_ne hna,
        Projectivization.mk_eq_mk_iff'] at h
      obtain ⟨c, hc⟩ := h
      have h1 := congrFun hc 1
      simp at h1
    · rw [sphereToProj_of_ne hna, sphereToProj_of_ne hnb, Projectivization.mk_eq_mk_iff'] at h
      obtain ⟨c, hc⟩ := h
      have h1 := congrFun hc 1
      have h0 := congrFun hc 0
      simp at h1 h0
      rw [h1] at h0
      simp at h0
      have := congrArg invN h0
      rw [invN_sN ha (z_ne_one ha hna), invN_sN hb (z_ne_one hb hnb)] at this
      exact this.symm
  · intro q _
    induction q using Projectivization.ind with
    | h v hv =>
      by_cases h1 : v 1 = 0
      · have h0 : v 0 ≠ 0 := by
          intro h0
          apply hv
          funext i
          fin_cases i <;> simp [h0, h1]
        refine ⟨northPole, ?_, ?_⟩
        · simp [unitSphere, northPole]
        · rw [sphereToProj_north, Projectivization.mk_eq_mk_iff']
          refine ⟨(v 0)⁻¹, ?_⟩
          funext i
          fin_cases i <;> simp [h0, h1]
      · have hne : invN (v 0 / v 1) ≠ northPole := by
          intro h
          apply invN_z_ne_one (v 0 / v 1)
          rw [h]; rfl
        refine ⟨invN (v 0 / v 1), invN_mem _, ?_⟩
        rw [sphereToProj_of_ne hne, Projectivization.mk_eq_mk_iff', sN_invN]
        refine ⟨(v 1)⁻¹, ?_⟩
        funext i
        fin_cases i <;> simp [h1, div_eq_mul_inv, mul_comm]
  · intro p hp hN hS
    have e1 := z_ne_one hp hN
    have e2 := z_ne_neg_one hp hS
    rw [sphereToProj_of_ne hN, Projectivization.mk_eq_mk_iff']
    refine ⟨stereoNorth p, ?_⟩
    have hne := sN_ne_zero hp e1 e2
    funext i
    fin_cases i
    · simp
    · simp [sS_eq_inv hp e1 e2, hne]

end NumberFieldKB.MilneEC.III
