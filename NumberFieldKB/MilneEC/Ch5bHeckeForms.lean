import NumberFieldKB.MilneEC.Ch5bHeckeLattice
import NumberFieldKB.MilneEC.Ch5bHermite
import NumberFieldKB.MilneEC.Ch5bHeckeOp
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.NumberTheory.ModularForms.LFunction

/-!
# Milne, *Elliptic Curves*, Chapter V, Section 4: Hecke operators on modular forms of level one through lattices

Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, subsection "Definition of the Hecke operators" (pdf
pp. 208–211).

* **The correspondence** (p. 208): $f(z) = F(\Lambda(z, 1))$ is a bijection between the functions
  $F : \mathcal L \to \mathbb C$ homogeneous of weight $-2k$ and the functions $f : \mathbb H \to \mathbb C$ with
  $f(\gamma z) = (cz + d)^{2k} f(z)$, $\gamma \in \mathrm{SL}_2(\mathbb Z)$ (`latFnOfModular`, `lattice_correspondence`).
* **$T(n)$ on modular forms** (Definition in prose, p. 210): $T(n)f$ is the function on $\mathbb H$ associated with
  $n^{2k-1}\,T(n)\cdot F$ (`heckeOpLat`).
* **Sublattices of $\Lambda(z, 1)$** (p. 211): the sublattices of index $n$ are the $\Lambda(az + b, d)$ for the
  triples of Lemma 4.15 (`mem_sublatticesOfIndex_latticeZ1`, `latticeSpan_injective`), hence the explicit formula
  (`heckeOpLat_eq_heckeOp`): Milne's $T(n)$ is `heckeOp 1 k n`.
* **Theorem 4.7 for $N = 1$** (p. 210, "follows easily from the Proposition"): `thm_4_7_levelOne_a`, `_b`, `_d`; and
  $T(n)$ maps $M_{2k}(\mathrm{SL}_2(\mathbb Z))$ and $S_{2k}(\mathrm{SL}_2(\mathbb Z))$ to themselves
  (`heckeOp_modularForm`, `heckeOp_cuspForm`).
-/

open UpperHalfPlane ModularForm
open scoped MatrixGroups Pointwise

noncomputable section

namespace NumberFieldKB.MilneEC.Vb

/-- The subgroup $\mathbb Z\omega_1 + \mathbb Z\omega_2$ of $\mathbb C$. -/
def latticeSpan (ω₁ ω₂ : ℂ) : Submodule ℤ ℂ :=
  Submodule.span ℤ {ω₁, ω₂}

/-- A real relation `p ω₁ + q ω₂ = 0` forces `p = q = 0` when `Im (ω₁ / ω₂) > 0`. -/
lemma real_indep_of_im {ω₁ ω₂ : ℂ} (h : 0 < (ω₁ / ω₂).im) {p q : ℝ} (hpq : (p : ℂ) * ω₁ + q * ω₂ = 0) :
    p = 0 ∧ q = 0 := by
  have hω₂ : ω₂ ≠ 0 := by rintro rfl; simp at h
  have h1 : (p : ℂ) * (ω₁ / ω₂) + q = 0 := by
    field_simp
    linear_combination hpq
  have h2 := congrArg Complex.im h1
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.zero_im] at h2
  have hp : p = 0 := by
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd h3 h.ne'
  subst hp
  refine ⟨rfl, ?_⟩
  simpa using h1

/-- Integer version of `real_indep_of_im`. -/
lemma int_indep_of_im {ω₁ ω₂ : ℂ} (h : 0 < (ω₁ / ω₂).im) {p q : ℤ} (hpq : (p : ℂ) * ω₁ + q * ω₂ = 0) :
    p = 0 ∧ q = 0 := by
  have := real_indep_of_im h (p := p) (q := q) (by exact_mod_cast hpq)
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

/-- $\Lambda(\omega_1, \omega_2)$ is a lattice when $\mathrm{Im}(\omega_1/\omega_2) > 0$. -/
theorem isLatticeC_latticeSpan {ω₁ ω₂ : ℂ} (h : 0 < (ω₁ / ω₂).im) : IsLatticeC (latticeSpan ω₁ ω₂) := by
  refine ⟨⟨ω₁, ω₂, ?_⟩, rfl⟩
  rw [LinearIndependent.pair_iff]
  intro s t hst
  exact real_indep_of_im h (p := s) (q := t) (by simpa [Complex.real_smul] using hst)

/-- The lattice $\Lambda(\omega_1, \omega_2)$ of an oriented pair ($\mathrm{Im}(\omega_1/\omega_2) > 0$). -/
def latticeOfPair (ω₁ ω₂ : ℂ) (h : 0 < (ω₁ / ω₂).im) : LatticeC :=
  ⟨latticeSpan ω₁ ω₂, isLatticeC_latticeSpan h⟩

/-- $\Lambda(z, 1)$ for $z \in \mathbb H$. -/
def latticeZ1 (z : ℍ) : LatticeC :=
  latticeOfPair z 1 (by simpa using z.im_pos)

/-- Every lattice is $\Lambda(\omega_1, \omega_2)$ for an oriented pair. -/
theorem exists_latticeOfPair (Λ : LatticeC) :
    ∃ (ω₁ ω₂ : ℂ) (h : 0 < (ω₁ / ω₂).im), latticeOfPair ω₁ ω₂ h = Λ := by
  obtain ⟨Λ, L, hL⟩ := Λ
  have hω₂ : L.ω₂ ≠ 0 := by
    have := L.indep.ne_zero 1
    simpa using this
  have hne : (L.ω₁ / L.ω₂).im ≠ 0 := by
    intro h0
    have hre : L.ω₁ / L.ω₂ = ((L.ω₁ / L.ω₂).re : ℂ) := Complex.ext (by simp) (by simpa using h0)
    have h1 : L.ω₁ = ((L.ω₁ / L.ω₂).re : ℂ) * L.ω₂ := by
      rw [← hre]; field_simp
    have := (LinearIndependent.pair_iff.1 L.indep) 1 (-(L.ω₁ / L.ω₂).re)
      (by simp [Complex.real_smul]; rw [← h1]; ring)
    simp at this
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine ⟨L.ω₂, L.ω₁, ?_, Subtype.ext ?_⟩
    · rw [← inv_div, Complex.inv_im]
      have : 0 < Complex.normSq (L.ω₁ / L.ω₂) := Complex.normSq_pos.2 (by
        intro h0; rw [h0] at hneg; simp at hneg)
      simp only [neg_div, Left.neg_pos_iff]
      exact div_neg_of_neg_of_pos hneg this
    · simp only [latticeOfPair, latticeSpan, ← hL, PeriodPair.lattice]
      rw [Set.pair_comm]
  · exact ⟨L.ω₁, L.ω₂, hpos, Subtype.ext hL⟩

/-- The function on lattices of a function $f$ on $\mathbb H$ (Milne, *EC*, V.4, p. 208):
$F(\Lambda(\omega_1, \omega_2)) = \omega_2^{-2k} f(\omega_1/\omega_2)$ for a chosen oriented basis. -/
def latFnOfModular (k : ℤ) (f : ℍ → ℂ) (Λ : LatticeC) : ℂ :=
  let ω₁ := (exists_latticeOfPair Λ).choose
  let ω₂ := (exists_latticeOfPair Λ).choose_spec.choose
  ω₂ ^ (-2 * k) * f ⟨ω₁ / ω₂, (exists_latticeOfPair Λ).choose_spec.choose_spec.choose⟩

/-- Membership in $\Lambda(\omega_1, \omega_2)$ with integer coefficients. -/
lemma mem_latticeSpan {ω₁ ω₂ x : ℂ} :
    x ∈ latticeSpan ω₁ ω₂ ↔ ∃ a b : ℤ, (a : ℂ) * ω₁ + b * ω₂ = x := by
  simp [latticeSpan, Submodule.mem_span_pair, zsmul_eq_mul]

/-- A change of basis by $\mathrm{SL}_2(\mathbb Z)$ does not change $\Lambda(\omega_1, \omega_2)$. -/
lemma latticeSpan_eq_of_det {ω₁ ω₂ : ℂ} {a b c d : ℤ} (h : a * d - b * c = 1) :
    latticeSpan (a * ω₁ + b * ω₂) (c * ω₁ + d * ω₂) = latticeSpan ω₁ ω₂ := by
  have h' : (a : ℂ) * d - b * c = 1 := by exact_mod_cast h
  apply le_antisymm
  · rw [latticeSpan, Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl <;> exact mem_latticeSpan.2 ⟨_, _, rfl⟩
  · rw [latticeSpan, Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact mem_latticeSpan.2 ⟨d, -b, by push_cast; linear_combination x * h'⟩
    · exact mem_latticeSpan.2 ⟨-c, a, by push_cast; linear_combination x * h'⟩

/-- The imaginary part of a Möbius transform. -/
lemma im_mobius (τ : ℂ) (a b c d : ℤ) (hne : (c : ℂ) * τ + d ≠ 0) :
    ((a * τ + b) / (c * τ + d)).im * Complex.normSq (c * τ + d) = (a * d - b * c) * τ.im := by
  have hn : Complex.normSq ((c : ℂ) * τ + d) ≠ 0 := (Complex.normSq_pos.2 hne).ne'
  rw [Complex.div_im, ← sub_div, div_mul_cancel₀ _ hn]
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.intCast_re,
    Complex.intCast_im]
  ring

/-- The ratio of a new basis $a\omega_1 + b\omega_2$, $c\omega_1 + d\omega_2$ is the Möbius transform. -/
lemma div_affine {ω₁ ω₂ : ℂ} (hω₂ : ω₂ ≠ 0) (a b c d : ℤ) (hne : (c : ℂ) * ω₁ + d * ω₂ ≠ 0) :
    ((a : ℂ) * ω₁ + b * ω₂) / (c * ω₁ + d * ω₂) =
      (a * (ω₁ / ω₂) + b) / (c * (ω₁ / ω₂) + d) := by
  have : (c : ℂ) * (ω₁ / ω₂) + d ≠ 0 := by
    intro h0
    apply hne
    have : (c : ℂ) * ω₁ + d * ω₂ = ω₂ * (c * (ω₁ / ω₂) + d) := by field_simp
    rw [this, h0, mul_zero]
  field_simp

/-- A change of basis between two oriented pairs has positive determinant. -/
lemma det_pos_of_oriented {ω₁ ω₂ ω₁' ω₂' : ℂ} (h : 0 < (ω₁ / ω₂).im) (h' : 0 < (ω₁' / ω₂').im)
    {a b c d : ℤ} (e1 : ω₁' = a * ω₁ + b * ω₂) (e2 : ω₂' = c * ω₁ + d * ω₂) : 0 < a * d - b * c := by
  have hω₂ : ω₂ ≠ 0 := by rintro rfl; simp at h
  have hω₂' : ω₂' ≠ 0 := by rintro rfl; simp at h'
  have hne : (c : ℂ) * ω₁ + d * ω₂ ≠ 0 := by rw [← e2]; exact hω₂'
  have hw : (c : ℂ) * (ω₁ / ω₂) + d ≠ 0 := by
    intro h0
    apply hne
    have : (c : ℂ) * ω₁ + d * ω₂ = ω₂ * (c * (ω₁ / ω₂) + d) := by field_simp
    rw [this, h0, mul_zero]
  have him := im_mobius (ω₁ / ω₂) a b c d hw
  rw [← div_affine hω₂ a b c d hne, ← e1, ← e2] at him
  have hpos : 0 < ((a : ℝ) * d - b * c) * (ω₁ / ω₂).im := by
    rw [← him]
    exact mul_pos h' (Complex.normSq_pos.2 hw)
  have hD : 0 < (a : ℝ) * d - b * c := by
    by_contra hh
    push Not at hh
    nlinarith
  exact_mod_cast hD

/-- Two oriented bases of the same lattice differ by an element of $\mathrm{SL}_2(\mathbb Z)$. -/
lemma sl2_of_span_eq {ω₁ ω₂ ω₁' ω₂' : ℂ} (h : 0 < (ω₁ / ω₂).im) (h' : 0 < (ω₁' / ω₂').im)
    (hs : latticeSpan ω₁ ω₂ = latticeSpan ω₁' ω₂') :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧ ω₁' = a * ω₁ + b * ω₂ ∧ ω₂' = c * ω₁ + d * ω₂ := by
  have hω₂ : ω₂ ≠ 0 := by rintro rfl; simp at h
  have hω₂' : ω₂' ≠ 0 := by rintro rfl; simp at h'
  have m1 : ω₁' ∈ latticeSpan ω₁ ω₂ := hs ▸ mem_latticeSpan.2 ⟨1, 0, by simp⟩
  have m2 : ω₂' ∈ latticeSpan ω₁ ω₂ := hs ▸ mem_latticeSpan.2 ⟨0, 1, by simp⟩
  have m3 : ω₁ ∈ latticeSpan ω₁' ω₂' := hs ▸ mem_latticeSpan.2 ⟨1, 0, by simp⟩
  have m4 : ω₂ ∈ latticeSpan ω₁' ω₂' := hs ▸ mem_latticeSpan.2 ⟨0, 1, by simp⟩
  obtain ⟨a, b, e1⟩ := mem_latticeSpan.1 m1
  obtain ⟨c, d, e2⟩ := mem_latticeSpan.1 m2
  obtain ⟨a', b', e3⟩ := mem_latticeSpan.1 m3
  obtain ⟨c', d', e4⟩ := mem_latticeSpan.1 m4
  have r1 := int_indep_of_im h (p := a' * a + b' * c - 1) (q := a' * b + b' * d) (by
    push_cast
    rw [← e1, ← e2] at e3
    linear_combination e3)
  have r2 := int_indep_of_im h (p := c' * a + d' * c) (q := c' * b + d' * d - 1) (by
    push_cast
    rw [← e1, ← e2] at e4
    linear_combination e4)
  have hprod : (a * d - b * c) * (a' * d' - b' * c') = 1 := by
    have : (a * d - b * c) * (a' * d' - b' * c') =
        (a' * a + b' * c) * (c' * b + d' * d) - (a' * b + b' * d) * (c' * a + d' * c) := by ring
    rw [this]
    have h1 : a' * a + b' * c = 1 := by linarith [r1.1]
    have h2 : c' * b + d' * d = 1 := by linarith [r2.2]
    rw [h1, h2, r1.2, r2.1]; ring
  have hD' : 0 < a * d - b * c := det_pos_of_oriented h h' e1.symm e2.symm
  have : a * d - b * c = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hprod with h1 | h1 <;> omega
  exact ⟨a, b, c, d, this, e1.symm, e2.symm⟩

/-- Slash invariance as a transformation law. -/
lemma slash_eq_apply {k : ℤ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[2 * k] γ = f) (γ : SL(2, ℤ)) (z : ℍ) :
    f (γ • z) = ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ (2 * k) * f z :=
  (ModularForm.slash_action_eq'_iff (2 * k) f γ z).1 (congrFun (hf γ) z)

/-- The value $\omega_2^{-2k} f(\omega_1/\omega_2)$ depends only on the lattice. -/
lemma modular_val_eq {k : ℤ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[2 * k] γ = f) {ω₁ ω₂ ω₁' ω₂' : ℂ}
    (h : 0 < (ω₁ / ω₂).im) (h' : 0 < (ω₁' / ω₂').im) (hs : latticeSpan ω₁ ω₂ = latticeSpan ω₁' ω₂') :
    ω₂' ^ (-2 * k) * f ⟨ω₁' / ω₂', h'⟩ = ω₂ ^ (-2 * k) * f ⟨ω₁ / ω₂, h⟩ := by
  obtain ⟨a, b, c, d, hdet, e1, e2⟩ := sl2_of_span_eq h h' hs
  have hω₂ : ω₂ ≠ 0 := by rintro rfl; simp at h
  have hω₂' : ω₂' ≠ 0 := by rintro rfl; simp at h'
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by simp [Matrix.det_fin_two]; linarith⟩
  have hne : (c : ℂ) * ω₁ + d * ω₂ ≠ 0 := by rw [← e2]; exact hω₂'
  have hw : (c : ℂ) * (ω₁ / ω₂) + d ≠ 0 := by
    intro h0
    apply hne
    have : (c : ℂ) * ω₁ + d * ω₂ = ω₂ * (c * (ω₁ / ω₂) + d) := by field_simp
    rw [this, h0, mul_zero]
  have hz : (⟨ω₁' / ω₂', h'⟩ : ℍ) = γ • (⟨ω₁ / ω₂, h⟩ : ℍ) := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [γ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, eq_intCast, algebraMap_int_eq]
    rw [e1, e2, div_affine hω₂ a b c d hne]
    rfl
  rw [hz, slash_eq_apply hf γ]
  have hc : ((γ 1 0 : ℤ) : ℂ) = c := rfl
  have hd : ((γ 1 1 : ℤ) : ℂ) = d := rfl
  rw [hc, hd]
  have e2' : ω₂' = ω₂ * (c * (ω₁ / ω₂) + d) := by
    rw [e2]; field_simp
  rw [e2', mul_zpow]
  have : (((c : ℂ) * (ω₁ / ω₂) + d) ^ (-2 * k)) * (((c : ℂ) * ((⟨ω₁ / ω₂, h⟩ : ℍ) : ℂ) + d) ^ (2 * k)) = 1 := by
    rw [show (-2 * k) = -(2 * k) by ring, zpow_neg]
    exact inv_mul_cancel₀ (zpow_ne_zero _ hw)
  calc _ = ω₂ ^ (-2 * k) * ((((c : ℂ) * (ω₁ / ω₂) + d) ^ (-2 * k)) *
        (((c : ℂ) * ((⟨ω₁ / ω₂, h⟩ : ℍ) : ℂ) + d) ^ (2 * k))) * f ⟨ω₁ / ω₂, h⟩ := by ring
    _ = _ := by rw [this]; ring

/-- For $f$ of weight $2k$ for $\mathrm{SL}_2(\mathbb Z)$, $F(\Lambda(\omega_1, \omega_2)) = \omega_2^{-2k}
f(\omega_1/\omega_2)$ for every oriented basis (two oriented bases differ by $\mathrm{SL}_2(\mathbb Z)$). -/
theorem latFnOfModular_latticeOfPair {k : ℤ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[2 * k] γ = f) (ω₁ ω₂ : ℂ)
    (h : 0 < (ω₁ / ω₂).im) : latFnOfModular k f (latticeOfPair ω₁ ω₂ h) = ω₂ ^ (-2 * k) * f ⟨ω₁ / ω₂, h⟩ := by
  have hspec := (exists_latticeOfPair (latticeOfPair ω₁ ω₂ h)).choose_spec.choose_spec.choose_spec
  have hs : latticeSpan ω₁ ω₂ =
      latticeSpan (exists_latticeOfPair (latticeOfPair ω₁ ω₂ h)).choose
        (exists_latticeOfPair (latticeOfPair ω₁ ω₂ h)).choose_spec.choose :=
    (congrArg Subtype.val hspec).symm
  unfold latFnOfModular
  exact (modular_val_eq hf _ h hs.symm).symm

/-- Scaling $\Lambda(\omega_1, \omega_2)$ by $c$. -/
lemma smul_latticeSpan (c ω₁ ω₂ : ℂ) : c • latticeSpan ω₁ ω₂ = latticeSpan (c * ω₁) (c * ω₂) := by
  simp only [latticeSpan, Submodule.smul_span, Set.smul_set_insert, Set.smul_set_singleton, smul_eq_mul]

/-- Scaling an oriented pair keeps it oriented. -/
lemma im_smul_pair {c : ℂ} (hc : c ≠ 0) {ω₁ ω₂ : ℂ} (h : 0 < (ω₁ / ω₂).im) :
    0 < ((c * ω₁) / (c * ω₂)).im := by
  rwa [mul_div_mul_left _ _ hc]

/-- Scaling a lattice of an oriented pair. -/
lemma smul_latticeOfPair (c : ℂˣ) {ω₁ ω₂ : ℂ} (h : 0 < (ω₁ / ω₂).im) :
    c • latticeOfPair ω₁ ω₂ h = latticeOfPair (c * ω₁) (c * ω₂) (im_smul_pair c.ne_zero h) :=
  Subtype.ext (smul_latticeSpan _ _ _)

/-- The function on lattices of a function of weight $2k$ is homogeneous. -/
lemma latFnOfModular_homogeneous {k : ℤ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[2 * k] γ = f) :
    IsHomogeneousLat k (latFnOfModular k f) := by
  intro c Λ
  obtain ⟨ω₁, ω₂, h, rfl⟩ := exists_latticeOfPair Λ
  rw [smul_latticeOfPair, latFnOfModular_latticeOfPair hf, latFnOfModular_latticeOfPair hf]
  have : (⟨(c : ℂ) * ω₁ / ((c : ℂ) * ω₂), im_smul_pair c.ne_zero h⟩ : ℍ) = ⟨ω₁ / ω₂, h⟩ :=
    UpperHalfPlane.ext (mul_div_mul_left _ _ c.ne_zero)
  rw [this, mul_zpow]
  ring

/-- The denominator of an element of $\mathrm{SL}_2(\mathbb Z)$ at $z$ is nonzero. -/
lemma sl2_denom_ne_zero (γ : SL(2, ℤ)) (z : ℍ) : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hz : 0 < ((z : ℂ) / 1).im := by simpa using z.im_pos
  intro h0
  have := int_indep_of_im hz (p := γ 1 0) (q := γ 1 1) (by simpa using h0)
  rw [this.1, this.2] at hdet
  simp at hdet

/-- The lattice $\Lambda(\gamma z, 1)$ is $(cz + d)^{-1}\Lambda(z, 1)$. -/
lemma latticeZ1_smul_sl2 (γ : SL(2, ℤ)) (z : ℍ) :
    (latticeZ1 (γ • z)).1 = (((γ 1 0 : ℂ) * z + γ 1 1)⁻¹) • (latticeZ1 z).1 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hw := sl2_denom_ne_zero γ z
  show latticeSpan ((γ • z : ℍ) : ℂ) 1 = _ • latticeSpan (z : ℂ) 1
  rw [← latticeSpan_eq_of_det (ω₁ := (z : ℂ)) (ω₂ := 1) hdet, smul_latticeSpan,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [eq_intCast, algebraMap_int_eq, Complex.ofReal_intCast]
  congr 1
  · field_simp
  · field_simp

/-- A function on lattices homogeneous of weight $-2k$ gives a function on $\mathbb H$ of weight $2k$. -/
lemma slash_invariant_of_homogeneous {k : ℤ} {F : LatticeC → ℂ} (hF : IsHomogeneousLat k F) :
    ∀ γ : SL(2, ℤ), (fun z : ℍ => F (latticeZ1 z)) ∣[2 * k] γ = fun z : ℍ => F (latticeZ1 z) := by
  intro γ
  funext z
  rw [ModularForm.slash_action_eq'_iff]
  have hw := sl2_denom_ne_zero γ z
  have hL : latticeZ1 (γ • z) = Units.mk0 _ (inv_ne_zero hw) • latticeZ1 z :=
    Subtype.ext (latticeZ1_smul_sl2 γ z)
  show F (latticeZ1 (γ • z)) = _ * F (latticeZ1 z)
  rw [hL, hF]
  simp only [Units.val_mk0]
  rw [inv_zpow', show -(-2 * k) = 2 * k by ring]

/-- **The lattice–function correspondence** (Milne, *EC*, V.4, p. 208, running text): $f(z) = F(\Lambda(z, 1))$
defines a one-to-one correspondence between the functions $F : \mathcal L \to \mathbb C$ with
$F(\lambda\Lambda) = \lambda^{-2k}F(\Lambda)$ and the functions $f : \mathbb H \to \mathbb C$ with
$f(\gamma z) = (cz + d)^{2k} f(z)$ for $\gamma \in \mathrm{SL}_2(\mathbb Z)$; the inverse is `latFnOfModular`. -/
@[kb "milne2006ec" "Ch. V, Section 4 (pdf p. 208): F ↔ f, f(z) = F(Λ(z,1))"]
theorem lattice_correspondence (k : ℤ) :
    ∃ e : {F : LatticeC → ℂ // IsHomogeneousLat k F} ≃ {f : ℍ → ℂ // ∀ γ : SL(2, ℤ), f ∣[2 * k] γ = f},
      (∀ F z, (e F).1 z = F.1 (latticeZ1 z)) ∧ ∀ f, (e.symm f).1 = latFnOfModular k f.1 := by
  refine ⟨{ toFun := fun F => ⟨fun z => F.1 (latticeZ1 z), slash_invariant_of_homogeneous F.2⟩
            invFun := fun f => ⟨latFnOfModular k f.1, latFnOfModular_homogeneous f.2⟩
            left_inv := ?_
            right_inv := ?_ }, fun F z => rfl, fun f => rfl⟩
  · rintro ⟨F, hF⟩
    refine Subtype.ext (funext fun Λ => ?_)
    obtain ⟨ω₁, ω₂, h, rfl⟩ := exists_latticeOfPair Λ
    have hω₂ : ω₂ ≠ 0 := by rintro rfl; simp at h
    show latFnOfModular k (fun z : ℍ => F (latticeZ1 z)) (latticeOfPair ω₁ ω₂ h) = _
    rw [latFnOfModular_latticeOfPair (slash_invariant_of_homogeneous hF)]
    have hL : latticeZ1 ⟨ω₁ / ω₂, h⟩ = Units.mk0 ω₂⁻¹ (inv_ne_zero hω₂) • latticeOfPair ω₁ ω₂ h := by
      refine Subtype.ext ?_
      show latticeSpan (ω₁ / ω₂) 1 = ω₂⁻¹ • latticeSpan ω₁ ω₂
      rw [smul_latticeSpan]
      congr 1
      · field_simp
      · field_simp
    show ω₂ ^ (-2 * k) * F (latticeZ1 ⟨ω₁ / ω₂, h⟩) = _
    rw [hL, hF, Units.val_mk0, inv_zpow', ← mul_assoc, ← zpow_add₀ hω₂]
    simp
  · rintro ⟨f, hf⟩
    refine Subtype.ext (funext fun z => ?_)
    show latFnOfModular k f (latticeOfPair z 1 _) = f z
    rw [latFnOfModular_latticeOfPair hf]
    simp

/-- **The Hecke operator $T(n)$ on modular forms of weight $2k$ for $\Gamma_0(1)$** (Milne, *EC*, V.4, p. 210,
definition in prose): $T(n)f$ is the function on $\mathbb H$ associated with $n^{2k-1}\,T(n)\cdot F$, $F$ the function
on lattices of $f$: $(T(n)f)(z) = n^{2k-1}(T(n)\cdot F)(\Lambda(z, 1))$. -/
@[kb "milne2006ec" "Ch. V, Section 4 (pdf p. 210): T(n) on modular forms (definition in prose)"]
def heckeOpLat (k : ℤ) (n : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun z => (n : ℂ) ^ (2 * k - 1) * heckeActFn (heckeT n) (latFnOfModular k f) (latticeZ1 z)

/-- The triples of `hermiteTriples n` are those of Lemma 4.15. -/
theorem mem_hermiteTriples {n : ℕ} {t : ℤ × ℤ × ℤ} : t ∈ hermiteTriples n ↔ HermiteTriple n t := by
  obtain ⟨a, b, d⟩ := t
  simp only [hermiteTriples, HermiteTriple, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_Ico]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, ⟨h3, _⟩, _⟩, h6, h7⟩
    exact ⟨h6, h1, h3, h7⟩
  · rintro ⟨h6, h1, h3, h7⟩
    have hd : 1 ≤ d := by omega
    refine ⟨⟨⟨h1, ?_⟩, ⟨h3, ?_⟩, ⟨hd, ?_⟩⟩, h6, h7⟩
    · nlinarith
    · nlinarith
    · nlinarith

/-- The period pair of an oriented pair. -/
def orientedPair {ω₁ ω₂ : ℂ} (h : 0 < (ω₁ / ω₂).im) : PeriodPair :=
  ⟨ω₁, ω₂, by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    exact real_indep_of_im h (p := s) (q := t) (by simpa [Complex.real_smul] using hst)⟩

/-- The index of a sublattice given by a change of basis is the absolute value of the determinant. -/
lemma latIndex_periodPair (L L' : PeriodPair) {a b c d : ℤ}
    (e1 : L'.ω₁ = a * L.ω₁ + b * L.ω₂) (e2 : L'.ω₂ = c * L.ω₁ + d * L.ω₂) :
    latIndex L'.lattice L.lattice = (a * d - b * c).natAbs := by
  have hle : L'.lattice ≤ L.lattice := by
    rw [PeriodPair.lattice, Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact (mem_latticeSpan (ω₁ := L.ω₁) (ω₂ := L.ω₂)).2 ⟨a, b, e1.symm⟩
    · exact (mem_latticeSpan (ω₁ := L.ω₁) (ω₂ := L.ω₂)).2 ⟨c, d, e2.symm⟩
  unfold latIndex
  rw [AddSubgroup.relIndex_eq_natAbs_det L'.lattice.toAddSubgroup L.lattice.toAddSubgroup hle
    L'.latticeBasis L.latticeBasis]
  congr 1
  erw [Module.Basis.det_apply]
  rw [Matrix.det_fin_two]
  have r0 : L.latticeBasis.repr ⟨(L'.latticeBasis 0 : ℂ), hle (SetLike.coe_mem _)⟩ =
      Finsupp.single 0 a + Finsupp.single 1 b := by
    have : (⟨(L'.latticeBasis 0 : ℂ), hle (SetLike.coe_mem _)⟩ : L.lattice) =
        a • L.latticeBasis 0 + b • L.latticeBasis 1 := by
      apply Subtype.ext
      simp [e1]
    rw [this]
    simp
  have r1 : L.latticeBasis.repr ⟨(L'.latticeBasis 1 : ℂ), hle (SetLike.coe_mem _)⟩ =
      Finsupp.single 0 c + Finsupp.single 1 d := by
    have : (⟨(L'.latticeBasis 1 : ℂ), hle (SetLike.coe_mem _)⟩ : L.lattice) =
        c • L.latticeBasis 0 + d • L.latticeBasis 1 := by
      apply Subtype.ext
      simp [e2]
    rw [this]
    simp
  erw [Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply,
    Module.Basis.toMatrix_apply]
  erw [r0, r1]
  simp
  ring

/-- The index of $\Lambda(\omega_1', \omega_2')$ in $\Lambda(\omega_1, \omega_2)$ for oriented pairs related by
an integer matrix. -/
lemma latIndex_span {ω₁ ω₂ ω₁' ω₂' : ℂ} (h : 0 < (ω₁ / ω₂).im) (h' : 0 < (ω₁' / ω₂').im) {a b c d : ℤ}
    (e1 : ω₁' = a * ω₁ + b * ω₂) (e2 : ω₂' = c * ω₁ + d * ω₂) :
    latIndex (latticeSpan ω₁' ω₂') (latticeSpan ω₁ ω₂) = (a * d - b * c).natAbs :=
  latIndex_periodPair (orientedPair h) (orientedPair h') e1 e2

/-- The point $(az + b)/d$ lies in $\mathbb H$ for $a, d > 0$. -/
lemma im_hermite_pos {a b d : ℤ} (ha : 0 < a) (hd : 0 < d) (z : ℍ) :
    0 < (((a : ℂ) * z + b) / d).im := by
  rw [Complex.div_intCast_im]
  simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re, zero_mul, add_zero]
  have h1 : (0 : ℝ) < a := by exact_mod_cast ha
  have h2 : (0 : ℝ) < d := by exact_mod_cast hd
  exact div_pos (mul_pos h1 z.im_pos) h2

/-- Milne, *EC*, V.4, p. 211 (running text): the sublattices of index $n$ of $\Lambda(z, 1)$ are exactly the lattices
$\Lambda(az + b, d)$, $(a, b, d)$ running through the triples of Lemma 4.15. -/
@[kb "milne2006ec" "Ch. V, Section 4 (pdf p. 211): sublattices of index n of Λ(z,1)"]
theorem mem_sublatticesOfIndex_latticeZ1 {n : ℕ} (hn : 0 < n) (z : ℍ) (Λ' : LatticeC) :
    Λ' ∈ sublatticesOfIndex n (latticeZ1 z) ↔
      ∃ t : ℤ × ℤ × ℤ, HermiteTriple n t ∧ Λ'.1 = latticeSpan (t.1 * z + t.2.1) t.2.2 := by
  have hz : 0 < ((z : ℂ) / 1).im := by simpa using z.im_pos
  have hΛ : (latticeZ1 z).1 = latticeSpan z 1 := rfl
  constructor
  · intro hmem
    obtain ⟨hle, hidx⟩ := hmem
    obtain ⟨ω₁', ω₂', h', hΛ'⟩ := exists_latticeOfPair Λ'
    have hspan : Λ'.1 = latticeSpan ω₁' ω₂' := (congrArg Subtype.val hΛ').symm
    have m1 : ω₁' ∈ latticeSpan (z : ℂ) 1 :=
      hΛ ▸ hle (hspan ▸ mem_latticeSpan.2 ⟨1, 0, by simp⟩)
    have m2 : ω₂' ∈ latticeSpan (z : ℂ) 1 :=
      hΛ ▸ hle (hspan ▸ mem_latticeSpan.2 ⟨0, 1, by simp⟩)
    obtain ⟨p, q, e1⟩ := mem_latticeSpan.1 m1
    obtain ⟨r, s, e2⟩ := mem_latticeSpan.1 m2
    have hpos := det_pos_of_oriented hz h' e1.symm e2.symm
    have hidx' := latIndex_span hz h' e1.symm e2.symm
    rw [hspan, hΛ] at hidx
    rw [hidx'] at hidx
    have hdet : p * s - q * r = n := by
      have := Int.natAbs_of_nonneg hpos.le
      rw [hidx] at this
      exact this.symm
    obtain ⟨U, t, ht, hUA⟩ := lemma_4_15_exists (Nat.succ_le_of_lt hn) !![p, q; r, s] (by
      rw [Matrix.det_fin_two_of]; exact hdet)
    have hU : U 0 0 * U 1 1 - U 0 1 * U 1 0 = 1 := by
      have := U.2
      rw [Matrix.det_fin_two] at this
      exact this
    have e00 := congrFun (congrFun hUA 0) 0
    have e01 := congrFun (congrFun hUA 0) 1
    have e10 := congrFun (congrFun hUA 1) 0
    have e11 := congrFun (congrFun hUA 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, hermiteMatrix] at e00 e01 e10 e11
    refine ⟨t, ht, ?_⟩
    rw [hspan, ← latticeSpan_eq_of_det (ω₁ := ω₁') (ω₂ := ω₂') (a := U 0 0) (b := U 0 1) (c := U 1 0)
      (d := U 1 1) hU]
    have c00 : ((U 0 0 : ℤ) : ℂ) * p + (U 0 1 : ℤ) * r = t.1 := by exact_mod_cast e00
    have c01 : ((U 0 0 : ℤ) : ℂ) * q + (U 0 1 : ℤ) * s = t.2.1 := by exact_mod_cast e01
    have c10 : ((U 1 0 : ℤ) : ℂ) * p + (U 1 1 : ℤ) * r = 0 := by exact_mod_cast e10
    have c11 : ((U 1 0 : ℤ) : ℂ) * q + (U 1 1 : ℤ) * s = t.2.2 := by exact_mod_cast e11
    congr 1
    · rw [← e1, ← e2]
      linear_combination (z : ℂ) * c00 + c01
    · rw [← e1, ← e2]
      linear_combination (z : ℂ) * c10 + c11
  · rintro ⟨t, ht, hΛ'⟩
    obtain ⟨h1, h2, h3, h4⟩ := ht
    have hd : 0 < t.2.2 := by omega
    have h' : 0 < (((t.1 : ℂ) * z + t.2.1) / (t.2.2 : ℂ)).im := im_hermite_pos (by omega) hd z
    have e1 : (t.1 : ℂ) * z + t.2.1 = (t.1 : ℂ) * (z : ℂ) + (t.2.1 : ℂ) * 1 := by ring
    have e2 : ((t.2.2 : ℤ) : ℂ) = ((0 : ℤ) : ℂ) * (z : ℂ) + (t.2.2 : ℂ) * 1 := by simp
    have hind := latIndex_span (ω₁ := (z : ℂ)) (ω₂ := 1) hz h' e1 e2
    refine ⟨?_, ?_⟩
    · rw [hΛ', hΛ, latticeSpan, Submodule.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact mem_latticeSpan.2 ⟨t.1, t.2.1, by simp⟩
      · exact mem_latticeSpan.2 ⟨0, t.2.2, by simp⟩
    · show latIndex Λ'.1 (latticeSpan (z : ℂ) 1) = n
      rw [hΛ', hind, mul_zero, sub_zero, h1]
      simp

/-- Distinct triples of Lemma 4.15 give distinct sublattices $\Lambda(az + b, d)$. -/
theorem latticeSpan_injective {n : ℕ} (z : ℍ) {t t' : ℤ × ℤ × ℤ} (ht : HermiteTriple n t)
    (ht' : HermiteTriple n t')
    (h : latticeSpan (t.1 * z + t.2.1) t.2.2 = latticeSpan (t'.1 * z + t'.2.1) t'.2.2) : t = t' := by
  have hz : 0 < ((z : ℂ) / 1).im := by simpa using z.im_pos
  obtain ⟨a, b, d⟩ := t
  obtain ⟨a', b', d'⟩ := t'
  have ht1 := ht
  have ht1' := ht'
  obtain ⟨h1, h2, h3, h4⟩ := ht
  obtain ⟨h1', h2', h3', h4'⟩ := ht'
  simp only at h1 h2 h3 h4 h1' h2' h3' h4' h
  have hA : 0 < (((a : ℂ) * z + b) / (d : ℂ)).im := im_hermite_pos (by omega) (by omega) z
  have hB : 0 < (((a' : ℂ) * z + b') / (d' : ℂ)).im := im_hermite_pos (by omega) (by omega) z
  obtain ⟨α, β, γ, δ, hdet, e1, e2⟩ := sl2_of_span_eq hA hB h
  have r1 := int_indep_of_im hz (p := a' - α * a) (q := b' - α * b - β * d) (by
    push_cast
    linear_combination e1)
  have r2 := int_indep_of_im hz (p := -(γ * a)) (q := d' - γ * b - δ * d) (by
    push_cast
    linear_combination e2)
  have hγ : γ = 0 := by
    have : γ * a = 0 := by linarith [r2.1]
    rcases mul_eq_zero.1 this with h0 | h0
    · exact h0
    · omega
  subst hγ
  let U' : SL(2, ℤ) := ⟨!![α, β; 0, δ], by
    rw [Matrix.det_fin_two_of]; linarith⟩
  have hU' : (U' : Matrix (Fin 2) (Fin 2) ℤ) * hermiteMatrix (a, b, d) = hermiteMatrix (a', b', d') := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U', hermiteMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> linarith [r1.1, r1.2, r2.1, r2.2]
  refine lemma_4_15_unique (hermiteMatrix (a, b, d)) ?_ 1 U' ht1 ht1' (by simp) hU'
  rw [hermiteMatrix, Matrix.det_fin_two_of]
  simp only [mul_zero, sub_zero]
  exact h1

/-- Milne, *EC*, V.4, p. 211 (running text): for $f$ of weight $2k$ for $\mathrm{SL}_2(\mathbb Z)$,
$(T(n)f)(z) = n^{2k-1}\sum_{a,b,d} d^{-2k} f\big(\frac{az+b}{d}\big)$: Milne's $T(n)$ is `heckeOp 1 k n`. -/
@[kb "milne2006ec" "Ch. V, Section 4 (pdf p. 211): explicit formula for T(n)f"]
theorem heckeOpLat_eq_heckeOp {k : ℤ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[2 * k] γ = f) {n : ℕ} (hn : 0 < n) :
    heckeOpLat k n f = heckeOp 1 k n f := by
  funext z
  unfold heckeOpLat heckeOp
  rw [heckeActFn_heckeT]
  congr 1
  have hfilt : (hermiteTriples n).filter (fun t => Int.gcd t.1 ((1 : ℕ) : ℤ) = 1) = hermiteTriples n :=
    Finset.filter_true_of_mem (fun t _ => by simp)
  rw [hfilt]
  have hpos : ∀ t ∈ hermiteTriples n, 0 < (((t.1 : ℂ) * z + t.2.1) / (t.2.2 : ℂ)).im := by
    intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := mem_hermiteTriples.1 ht
    exact im_hermite_pos (by omega) (by omega) z
  symm
  refine Finset.sum_bij (fun t ht => latticeOfPair _ _ (hpos t ht)) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Set.Finite.mem_toFinset]
    exact (mem_sublatticesOfIndex_latticeZ1 hn z _).2 ⟨t, mem_hermiteTriples.1 ht, rfl⟩
  · intro t ht t' ht' h
    exact latticeSpan_injective z (mem_hermiteTriples.1 ht) (mem_hermiteTriples.1 ht')
      (congrArg Subtype.val h)
  · intro Λ' hΛ'
    rw [Set.Finite.mem_toFinset] at hΛ'
    obtain ⟨t, ht, hspan⟩ := (mem_sublatticesOfIndex_latticeZ1 hn z Λ').1 hΛ'
    exact ⟨t, mem_hermiteTriples.2 ht, Subtype.ext hspan.symm⟩
  · intro t ht
    rw [latFnOfModular_latticeOfPair hf]
    have : hermitePoint t z = ⟨_, hpos t ht⟩ :=
      UpperHalfPlane.ext (by simp [hermitePoint, ofComplex_apply_of_im_pos (hpos t ht)])
    rw [this]

/-- $T(n)$ preserves the functions of weight $2k$ for $\mathrm{SL}_2(\mathbb Z)$ (from Proposition 4.14 through the
correspondence). -/
theorem heckeOp_slash_invariant {k : ℤ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[2 * k] γ = f) {n : ℕ} (hn : 0 < n) :
    ∀ γ : SL(2, ℤ), heckeOp 1 k n f ∣[2 * k] γ = heckeOp 1 k n f := by
  have hg := slash_invariant_of_homogeneous
    (prop_4_14 (latFnOfModular_homogeneous hf) n)
  have e : heckeOp 1 k n f = (n : ℂ) ^ (2 * k - 1) •
      (fun z : ℍ => heckeActFn (heckeT n) (latFnOfModular k f) (latticeZ1 z)) := by
    rw [← heckeOpLat_eq_heckeOp hf hn]
    rfl
  intro γ
  rw [e, ModularForm.SL_smul_slash, hg γ]

/-- A slash invariant form for `𝒮ℒ` is invariant under `SL(2, ℤ)`. -/
lemma slash_invariant_levelOne {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] [SlashInvariantFormClass F 𝒮ℒ (2 * k)]
    (f : F) : ∀ γ : SL(2, ℤ), (f : ℍ → ℂ) ∣[2 * k] γ = f :=
  fun γ => SlashInvariantFormClass.slash_action_eq f _ ⟨γ, rfl⟩

/-- The `q`-series of `T(n) f` for a modular form `f` of level one. -/
lemma heckeOp_hasSum_levelOne {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F 𝒮ℒ (2 * k)]
    (f : F) (n : ℕ) (τ : ℍ) :
    HasSum (fun m : ℕ => heckeCoeff 1 k n (fun m => (qExpansion 1 f).coeff m) m *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (heckeOp 1 k n f τ) := by
  have hΓ : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  exact hasSum_heckeOp 1 k n _ f (fun τ => ModularForm.hasSum_qExpansion f one_pos hΓ τ) τ

/-- `T(n) f` is bounded at the cusps for a modular form `f` of level one. -/
lemma heckeOp_isBoundedAt {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F 𝒮ℒ (2 * k)]
    (f : F) {n : ℕ} (hn : 0 < n) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsBoundedAt (heckeOp 1 k n f) (2 * k) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
  intro γ _
  rw [heckeOp_slash_invariant (slash_invariant_levelOne f) hn γ]
  exact isBoundedAtImInfty_of_hasSum_qExpansion one_pos
    (fun τ => by simpa using heckeOp_hasSum_levelOne f n τ)

/-- `T(n) f` vanishes at the cusps for a cusp form `f` of level one. -/
lemma heckeOp_isZeroAt {k : ℤ} (f : CuspForm 𝒮ℒ (2 * k)) {n : ℕ} (hn : 0 < n) {c : OnePoint ℝ}
    (hc : IsCusp c 𝒮ℒ) : c.IsZeroAt (heckeOp 1 k n f) (2 * k) := by
  have hΓ : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  rw [heckeOp_slash_invariant (slash_invariant_levelOne f) hn γ]
  have hc0 : (qExpansion 1 f).coeff 0 = 0 := CuspFormClass.qExpansion_coeff_zero f one_pos hΓ
  have := tendsto_atImInfty_of_hasSum_qExpansion one_pos
    (f := heckeOp 1 k n f) (fun τ => by simpa using heckeOp_hasSum_levelOne f n τ)
  rw [heckeCoeff_zero 1 k n _ hc0] at this
  exact this

/-- Milne, *EC*, V.4, p. 207 ("Hecke defined linear maps $T(n) : S_{2k}(\Gamma_0(N)) \to S_{2k}(\Gamma_0(N))$"), case
$N = 1$, for modular forms: $T(n)$ maps $M_{2k}(\mathrm{SL}_2(\mathbb Z))$ to itself. -/
@[kb "milne2006ec" "Ch. V, Section 4 (pdf p. 210): T(n) preserves modular forms of level one"]
theorem heckeOp_modularForm {k : ℤ} (f : ModularForm 𝒮ℒ (2 * k)) {n : ℕ} (hn : 0 < n) :
    ∃ g : ModularForm 𝒮ℒ (2 * k), ⇑g = heckeOp 1 k n f :=
  ⟨{ toFun := heckeOp 1 k n f
     slash_action_eq' := by
       rintro _ ⟨γ, rfl⟩
       exact heckeOp_slash_invariant (slash_invariant_levelOne f) hn γ
     holo' := mdifferentiable_heckeOp 1 k n (ModularFormClass.holo f)
     bdd_at_cusps' := fun {_} hc => heckeOp_isBoundedAt f hn hc }, rfl⟩

/-- Milne, *EC*, V.4, p. 207, case $N = 1$: $T(n)$ maps $S_{2k}(\mathrm{SL}_2(\mathbb Z))$ to itself. -/
@[kb "milne2006ec" "Ch. V, Section 4 (pdf p. 210): T(n) preserves cusp forms of level one"]
theorem heckeOp_cuspForm {k : ℤ} (f : CuspForm 𝒮ℒ (2 * k)) {n : ℕ} (hn : 0 < n) :
    ∃ g : CuspForm 𝒮ℒ (2 * k), ⇑g = heckeOp 1 k n f :=
  ⟨{ toFun := heckeOp 1 k n f
     slash_action_eq' := by
       rintro _ ⟨γ, rfl⟩
       exact heckeOp_slash_invariant (slash_invariant_levelOne f) hn γ
     holo' := mdifferentiable_heckeOp 1 k n (ModularFormClass.holo f)
     zero_at_cusps' := fun {_} hc => heckeOp_isZeroAt f hn hc }, rfl⟩

/-- Scalars pass through the action of `T` on functions on lattices. -/
lemma heckeActFn_const_mul (T : LatDiv →ₗ[ℤ] LatDiv) (c : ℂ) (F : LatticeC → ℂ) :
    heckeActFn T (fun Λ => c * F Λ) = fun Λ => c * heckeActFn T F Λ := by
  have key : ∀ x : LatDiv, latFnExt (fun Λ => c * F Λ) x = c * latFnExt F x := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]
    | single a b => simp [latFnExt_single, zsmul_eq_mul]; ring
  funext Λ
  exact key _

/-- $T(n)f$ in terms of the action of $T(n)$ on the function on lattices of $f$. -/
lemma heckeOp_apply_lat {k : ℤ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[2 * k] γ = f) {n : ℕ} (hn : 0 < n)
    (z : ℍ) : heckeOp 1 k n f z =
      (n : ℂ) ^ (2 * k - 1) * heckeActFn (heckeT n) (latFnOfModular k f) (latticeZ1 z) := by
  rw [← heckeOpLat_eq_heckeOp hf hn]
  rfl

/-- The function on lattices of $T(n)f$ is $n^{2k-1}\,T(n)\cdot F$. -/
lemma latFnOfModular_heckeOp {k : ℤ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[2 * k] γ = f) {n : ℕ}
    (hn : 0 < n) : latFnOfModular k (heckeOp 1 k n f) =
      fun Λ => (n : ℂ) ^ (2 * k - 1) * heckeActFn (heckeT n) (latFnOfModular k f) Λ := by
  obtain ⟨e, he1, he2⟩ := lattice_correspondence k
  have hhom : IsHomogeneousLat k
      (fun Λ => (n : ℂ) ^ (2 * k - 1) * heckeActFn (heckeT n) (latFnOfModular k f) Λ) := by
    intro c Λ
    have := prop_4_14 (latFnOfModular_homogeneous hf) n c Λ
    simp only
    rw [this]
    ring
  let H : {F : LatticeC → ℂ // IsHomogeneousLat k F} := ⟨_, hhom⟩
  let g : {f : ℍ → ℂ // ∀ γ : SL(2, ℤ), f ∣[2 * k] γ = f} :=
    ⟨heckeOp 1 k n f, heckeOp_slash_invariant hf hn⟩
  have h1 : e H = g := by
    refine Subtype.ext (funext fun z => ?_)
    rw [he1]
    exact (heckeOp_apply_lat hf hn z).symm
  have h2 : H = e.symm g := by rw [← h1]; simp
  have := congrArg Subtype.val h2
  rw [he2] at this
  exact this.symm

/-- $T(m)T(n)f$ in terms of the iterated action on the function on lattices. -/
lemma heckeOp_heckeOp_apply {k : ℤ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[2 * k] γ = f) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (z : ℍ) : heckeOp 1 k m (heckeOp 1 k n f) z =
      (m : ℂ) ^ (2 * k - 1) * ((n : ℂ) ^ (2 * k - 1) *
        heckeActFn (heckeT m) (heckeActFn (heckeT n) (latFnOfModular k f)) (latticeZ1 z)) := by
  rw [heckeOp_apply_lat (heckeOp_slash_invariant hf hn) hm, latFnOfModular_heckeOp hf hn,
    heckeActFn_const_mul]

/-- **Theorem 4.7(a) for $N = 1$** (Milne, *EC*, V.4, p. 210: "Theorem 4.7 in the case $N = 1$ follows easily from
the Proposition"): $T(mn) = T(m)T(n)$ for $\gcd(m, n) = 1$, on functions of weight $2k$ for
$\mathrm{SL}_2(\mathbb Z)$. -/
@[kb "milne2006ec" "Ch. V, Theorem 4.7(a) for N = 1 (pdf p. 210)"]
theorem thm_4_7_levelOne_a {k : ℤ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[2 * k] γ = f) {m n : ℕ} (hm : 0 < m)
    (hn : 0 < n) (h : m.Coprime n) : heckeOp 1 k (m * n) f = heckeOp 1 k m (heckeOp 1 k n f) := by
  funext z
  rw [heckeOp_apply_lat hf (Nat.mul_pos hm hn), heckeOp_heckeOp_apply hf hm hn,
    prop_4_14_a (latFnOfModular_homogeneous hf) hm hn h, Nat.cast_mul, mul_zpow, mul_assoc]

/-- **Theorem 4.7(b) for $N = 1$** (Milne, *EC*, V.4, p. 210): $T(p)T(p^r) = T(p^{r+1}) + p^{2k-1}T(p^{r-1})$,
$r \ge 1$. -/
@[kb "milne2006ec" "Ch. V, Theorem 4.7(b) for N = 1 (pdf p. 210)"]
theorem thm_4_7_levelOne_b {k : ℤ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[2 * k] γ = f) {p : ℕ} (hp : p.Prime)
    {r : ℕ} (hr : 1 ≤ r) :
    heckeOp 1 k p (heckeOp 1 k (p ^ r) f) =
      heckeOp 1 k (p ^ (r + 1)) f + (p : ℂ) ^ (2 * k - 1) • heckeOp 1 k (p ^ (r - 1)) f := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  funext z
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hq : (p : ℂ) ^ (2 * k - 1) ≠ 0 := zpow_ne_zero _ hp0
  have hpow : ∀ (r : ℕ) (e : ℤ), ((p ^ r : ℕ) : ℂ) ^ e = ((p : ℂ) ^ e) ^ r := by
    intro r e
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hinv : (p : ℂ) ^ (1 - 2 * k) = ((p : ℂ) ^ (2 * k - 1))⁻¹ := by
    rw [← zpow_neg]; congr 1; ring
  rw [heckeOp_heckeOp_apply hf hp.pos (pow_pos hp.pos _) z,
    congrFun (prop_4_14_b (latFnOfModular_homogeneous hf) hp hr) (latticeZ1 z)]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.add_sub_cancel]
  rw [heckeOp_apply_lat hf (pow_pos hp.pos _) z, heckeOp_apply_lat hf (pow_pos hp.pos _) z,
    hpow, hpow, hpow, hinv]
  field_simp
  ring

/-- **Theorem 4.7(d) for $N = 1$** (Milne, *EC*, V.4, p. 210): all $T(n)$ commute. -/
@[kb "milne2006ec" "Ch. V, Theorem 4.7(d) for N = 1 (pdf p. 210)"]
theorem thm_4_7_levelOne_d {k : ℤ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[2 * k] γ = f) {m n : ℕ} (hm : 0 < m)
    (hn : 0 < n) : heckeOp 1 k m (heckeOp 1 k n f) = heckeOp 1 k n (heckeOp 1 k m f) := by
  funext z
  rw [heckeOp_heckeOp_apply hf hm hn z, heckeOp_heckeOp_apply hf hn hm z]
  have hc := LinearMap.congr_fun (cor_4_13.1 (heckeT m) (cor_4_13.2 m hm) (heckeT n) (cor_4_13.2 n hn))
    (Finsupp.single (latticeZ1 z) 1)
  have : heckeActFn (heckeT m) (heckeActFn (heckeT n) (latFnOfModular k f)) (latticeZ1 z) =
      heckeActFn (heckeT n) (heckeActFn (heckeT m) (latFnOfModular k f)) (latticeZ1 z) := by
    show latFnExt (heckeActFn (heckeT n) (latFnOfModular k f)) (heckeT m (Finsupp.single (latticeZ1 z) 1)) =
      latFnExt (heckeActFn (heckeT m) (latFnOfModular k f)) (heckeT n (Finsupp.single (latticeZ1 z) 1))
    rw [latFnExt_heckeActFn, latFnExt_heckeActFn]
    exact congrArg (latFnExt (latFnOfModular k f)) hc.symm
  rw [this]
  ring

end NumberFieldKB.MilneEC.Vb
