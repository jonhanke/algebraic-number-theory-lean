import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Chapter 7: Krasner's lemma and applications

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Setting (Milne p. 131): $K$ is complete with respect to a discrete absolute value, extended (uniquely) to an algebraic
closure $K^{\mathrm{al}}$; from Proposition 7.61 on, $K$ has characteristic zero. Here $K$ is a complete nontrivially
normed field with ultrametric norm, and $K^{\mathrm{al}}$ is `AlgebraicClosure K` with the spectral norm
(`spectralNorm K (AlgebraicClosure K)`, Mathlib's unique extension of the norm). Krasner's lemma itself
(Proposition 7.60) is Mathlib's `IsKrasner.krasner` (see `Ch7Cite.lean`). The hypothesis that the absolute value is
discrete is not used in the statements below and is omitted.

* **Norm of a polynomial** (prose definition, p. 132; `polyNorm`): $\lVert \sum c_i X^i \rVert = \max |c_i|$.
* **A root $\beta$ belongs to a root $\alpha_i$** (prose definition, p. 132; `BelongsTo`).
* **Proposition 7.61** (`prop_7_61`), **Corollary 7.62** (`cor_7_62`), **Proposition 7.63** (`prop_7_63`).
-/

open Polynomial IntermediateField

namespace NumberFieldKB.MilneANT

variable {K : Type*} [NontriviallyNormedField K]

/-- **Norm of a polynomial** (prose definition, Milne p. 122 and p. 132): $\lVert h \rVert = \max_i |c_i|$ for
$h = \sum c_i X^i$. -/
@[kb "milne2020ant" "v3.08, Ch. 7, definition of the norm of a polynomial, p. 132"]
noncomputable def polyNorm (h : K[X]) : ℝ := ⨆ i : ℕ, ‖h.coeff i‖

/-- **A root belongs to a root** (prose definition, Milne p. 132): for $f \in K[X]$ with roots $\alpha_j$ in
$K^{\mathrm{al}}$, an element $\beta \in K^{\mathrm{al}}$ *belongs to* the root $\alpha_i$ if
$|\beta - \alpha_i| < |\alpha_i - \alpha_j|$ for all roots $\alpha_j \ne \alpha_i$. -/
@[kb "milne2020ant" "v3.08, Ch. 7, definition of a root belonging to a root, p. 132"]
def BelongsTo (f : K[X]) (β α : AlgebraicClosure K) : Prop :=
  α ∈ (f.map (algebraMap K (AlgebraicClosure K))).roots ∧
    ∀ α' ∈ (f.map (algebraMap K (AlgebraicClosure K))).roots, α' ≠ α →
      spectralNorm K (AlgebraicClosure K) (β - α) < spectralNorm K (AlgebraicClosure K) (α - α')

variable [IsUltrametricDist K] [CompleteSpace K]

section Helpers

set_option linter.unusedSectionVars false

lemma norm_coeff_le_polyNorm (h : K[X]) (i : ℕ) : ‖h.coeff i‖ ≤ polyNorm h := by
  unfold polyNorm
  refine le_ciSup (f := fun i => ‖h.coeff i‖) ⟨∑ j ∈ Finset.range (h.natDegree + 1), ‖h.coeff j‖, ?_⟩ i
  rintro _ ⟨j, rfl⟩
  by_cases hj : j ≤ h.natDegree
  · exact Finset.single_le_sum (f := fun j => ‖h.coeff j‖) (fun _ _ => norm_nonneg _)
      (by simp; omega)
  · simp only [coeff_eq_zero_of_natDegree_lt (not_le.1 hj), norm_zero]
    positivity

lemma natDegree_eq_of_polyNorm_lt_one (f g : K[X]) (hf : f.Monic) (hg : g.Monic)
    (h : polyNorm (f - g) < 1) : g.natDegree = f.natDegree := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := norm_coeff_le_polyNorm (f - g) f.natDegree
    rw [coeff_sub, hf.coeff_natDegree, coeff_eq_zero_of_natDegree_lt hlt] at this
    simp at this
    linarith
  · have := norm_coeff_le_polyNorm (f - g) g.natDegree
    rw [coeff_sub, hg.coeff_natDegree, coeff_eq_zero_of_natDegree_lt hlt] at this
    simp at this
    linarith

lemma exists_sep {C : Type*} [NormedField C] (S : Finset C) :
    ∃ d > 0, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → d ≤ ‖a - b‖ := by
  by_cases hS : S.offDiag.Nonempty
  · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image S.offDiag (fun p => ‖p.1 - p.2‖) hS
    have hp' := Finset.mem_offDiag.1 hp
    refine ⟨‖p.1 - p.2‖, norm_pos_iff.2 (sub_ne_zero.2 hp'.2.2), fun a ha b hb hab => ?_⟩
    exact hmin (a, b) (Finset.mem_offDiag.2 ⟨ha, hb, hab⟩)
  · refine ⟨1, one_pos, fun a ha b hb hab => ?_⟩
    exact absurd ⟨(a, b), Finset.mem_offDiag.2 ⟨ha, hb, hab⟩⟩ hS

lemma exists_eps_roots_close {C : Type*} [NormedField C] [NormedAlgebra K C] [IsAlgClosed C]
    (f : K[X]) (hf : f.Monic) {r : ℝ} (hr : 0 < r) :
    ∃ ε > 0, ∀ g : K[X], g.Monic → g.natDegree = f.natDegree →
      (∀ i, ‖g.coeff i - f.coeff i‖ < ε) →
      ∀ a ∈ (f.map (algebraMap K C)).roots,
        ∃ b ∈ (g.map (algebraMap K C)).roots, ‖a - b‖ < r := by
  classical
  set n := f.natDegree with hn
  set R : ℝ := 1 + ∑ a ∈ (f.map (algebraMap K C)).roots.toFinset, ‖a‖ with hR
  have hR1 : 1 ≤ R := by
    have : 0 ≤ ∑ a ∈ (f.map (algebraMap K C)).roots.toFinset, ‖a‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have hRpos : 0 < R := by linarith
  refine ⟨(r / R) ^ n / (n + 1), by positivity, fun g hg hdeg hcoeff a ha => ?_⟩
  have hmem := (mem_roots'.1 ha)
  have ha0 : f.aeval a = 0 := by
    have := hmem.2
    simpa [IsRoot.def, eval_map_algebraMap] using this
  have hn0 : n ≠ 0 := by
    intro h0
    have := hf.natDegree_eq_zero.1 h0
    rw [this] at ha0
    simp at ha0
  obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (K := K) (L := C)
    (f := f) (g := g) (ε := (r / R) ^ n / (n + 1)) (by positivity) ha0 hf hg hdeg hcoeff
    (IsAlgClosed.splits _)
  refine ⟨b, hb, lt_of_lt_of_le hab ?_⟩
  have h1 : ((↑n + 1) * ((r / R) ^ n / (↑n + 1))) = (r / R) ^ n := by
    field_simp
  rw [h1, Real.pow_rpow_inv_natCast (by positivity) hn0]
  have h2 : max ‖a‖ 1 ≤ R := by
    refine max_le ?_ hR1
    have : ‖a‖ ≤ ∑ a ∈ (f.map (algebraMap K C)).roots.toFinset, ‖a‖ :=
      Finset.single_le_sum (f := fun a : C => ‖a‖) (fun _ _ => norm_nonneg _)
        (Multiset.mem_toFinset.2 ha)
    linarith
  calc r / R * max ‖a‖ 1 ≤ r / R * R := by gcongr
    _ = r := by field_simp

lemma exists_delta_roots {C : Type*} [NormedField C] [NormedAlgebra K C] [IsAlgClosed C]
    (f : K[X]) (hf : f.Monic) (hsep : f.Separable) :
    ∃ d > 0, (∀ a ∈ (f.map (algebraMap K C)).roots, ∀ a' ∈ (f.map (algebraMap K C)).roots,
        a ≠ a' → d ≤ ‖a - a'‖) ∧
      ∃ δ > 0, ∀ g : K[X], g.Monic → polyNorm (f - g) < δ →
        g.natDegree = f.natDegree ∧
        (∀ a ∈ (f.map (algebraMap K C)).roots, ∃ b ∈ (g.map (algebraMap K C)).roots, ‖b - a‖ < d) ∧
        (∀ b ∈ (g.map (algebraMap K C)).roots, ∃ a ∈ (f.map (algebraMap K C)).roots, ‖b - a‖ < d) := by
  classical
  obtain ⟨d, hd, hsepd⟩ := exists_sep (C := C) (f.map (algebraMap K C)).roots.toFinset
  refine ⟨d, hd, fun a ha a' ha' => hsepd a (Multiset.mem_toFinset.2 ha) a'
    (Multiset.mem_toFinset.2 ha'), ?_⟩
  obtain ⟨ε, hε, hεg⟩ := exists_eps_roots_close (C := C) f hf (half_pos hd)
  refine ⟨min ε 1, lt_min hε one_pos, fun g hg hfg => ?_⟩
  have hfg1 : polyNorm (f - g) < 1 := lt_of_lt_of_le hfg (min_le_right _ _)
  have hdeg := natDegree_eq_of_polyNorm_lt_one f g hf hg hfg1
  have hcoeff : ∀ i, ‖g.coeff i - f.coeff i‖ < ε := fun i => by
    rw [norm_sub_rev, ← coeff_sub]
    exact lt_of_le_of_lt (norm_coeff_le_polyNorm _ _) (lt_of_lt_of_le hfg (min_le_left _ _))
  have hclose := hεg g hg hdeg hcoeff
  refine ⟨hdeg, fun a ha => ?_, ?_⟩
  · obtain ⟨b, hb, hab⟩ := hclose a ha
    exact ⟨b, hb, by rw [norm_sub_rev]; linarith⟩
  · -- counting argument
    set S := (f.map (algebraMap K C)).roots.toFinset with hS
    set T := (g.map (algebraMap K C)).roots.toFinset with hT
    have hA : ∀ a ∈ S, ∃ b ∈ T, ‖a - b‖ < d / 2 := fun a ha => by
      obtain ⟨b, hb, hab⟩ := hclose a (Multiset.mem_toFinset.1 ha)
      exact ⟨b, Multiset.mem_toFinset.2 hb, hab⟩
    choose! φ hφT hφ using hA
    have hinj : Set.InjOn φ S := by
      intro a ha a' ha' h
      by_contra hne
      have h1 := hsepd a ha a' ha' hne
      have h2 : ‖a - a'‖ ≤ ‖a - φ a‖ + ‖a' - φ a'‖ := by
        calc ‖a - a'‖ = ‖(a - φ a) - (a' - φ a')‖ := by rw [h]; congr 1; ring
          _ ≤ _ := norm_sub_le _ _
      have := hφ a ha
      have := hφ a' ha'
      have h3 : ‖a - a'‖ < d := lt_of_le_of_lt h2 (by linarith)
      linarith
    have hScard : S.card = f.natDegree := by
      have hnd : ((f.map (algebraMap K C)).roots).Nodup := Polynomial.nodup_roots (Separable.map hsep)
      rw [hS, Multiset.toFinset_card_of_nodup hnd, IsAlgClosed.card_roots_eq_natDegree,
        natDegree_map]
    have hTcard : T.card ≤ f.natDegree := by
      calc T.card ≤ (g.map (algebraMap K C)).roots.card := Multiset.toFinset_card_le _
        _ = g.natDegree := by rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map]
        _ = f.natDegree := hdeg
    have himg : S.image φ ⊆ T := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
      exact hφT a ha
    have heq : S.image φ = T := Finset.eq_of_subset_of_card_le himg (by
      rw [Finset.card_image_of_injOn hinj]; omega)
    intro b hb
    have : b ∈ S.image φ := heq ▸ Multiset.mem_toFinset.2 hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 this
    refine ⟨a, Multiset.mem_toFinset.1 ha, ?_⟩
    have := hφ a ha
    rw [norm_sub_rev]; linarith

lemma krasner_step {C : Type*} [NormedField C] [NormedAlgebra K C] [IsAlgClosed C]
    [Algebra.IsAlgebraic K C] [CharZero K]
    (f g : K[X]) (hf : f.Monic) (hirr : Irreducible f) (hg : g.Monic) (α β : C)
    (hα : α ∈ (f.map (algebraMap K C)).roots) (hβ : β ∈ (g.map (algebraMap K C)).roots)
    (hclose : ∀ α' ∈ (f.map (algebraMap K C)).roots, α' ≠ α → ‖β - α‖ < ‖α - α'‖)
    (hdeg : g.natDegree = f.natDegree) :
    K⟮α⟯ = K⟮β⟯ ∧ Irreducible g := by
  have hα0 : aeval α f = 0 := by
    have := (mem_roots'.1 hα).2
    simpa [IsRoot.def, eval_map_algebraMap] using this
  have hβ0 : aeval β g = 0 := by
    have := (mem_roots'.1 hβ).2
    simpa [IsRoot.def, eval_map_algebraMap] using this
  have hmin : minpoly K α = f := (minpoly.eq_of_irreducible_of_monic hirr hα0 hf).symm
  have hαint : IsIntegral K α := ⟨f, hf, by rwa [← aeval_def]⟩
  have hβint : IsIntegral K β := ⟨g, hg, by rwa [← aeval_def]⟩
  have hmem : α ∈ K⟮β⟯ := by
    refine IsKrasner.krasner (by rw [hmin]; exact hirr.separable)
      (by rw [hmin]; exact IsAlgClosed.splits _) hβint ?_
    intro x' hx' hne
    have hx'0 : aeval x' f = 0 := by
      have := hx'.aeval_eq_zero
      rwa [hmin] at this
    have hx'r : x' ∈ (f.map (algebraMap K C)).roots := by
      rw [mem_roots', IsRoot.def, eval_map_algebraMap]
      exact ⟨Polynomial.map_ne_zero hf.ne_zero, hx'0⟩
    have := hclose x' hx'r (Ne.symm hne)
    rwa [norm_sub_rev β α] at this
  have hle : K⟮α⟯ ≤ K⟮β⟯ := by
    rw [IntermediateField.adjoin_simple_le_iff]; exact hmem
  have hdvd : minpoly K β ∣ g := minpoly.dvd K β hβ0
  have hfr1 : Module.finrank K K⟮α⟯ = f.natDegree := by
    rw [IntermediateField.adjoin.finrank hαint, hmin]
  have hfr2 : Module.finrank K K⟮β⟯ = (minpoly K β).natDegree :=
    IntermediateField.adjoin.finrank hβint
  have hle2 : (minpoly K β).natDegree ≤ g.natDegree :=
    natDegree_le_of_dvd hdvd hg.ne_zero
  have : FiniteDimensional K K⟮β⟯ := IntermediateField.adjoin.finiteDimensional hβint
  have heq : K⟮α⟯ = K⟮β⟯ :=
    IntermediateField.eq_of_le_of_finrank_le hle (by rw [hfr1, hfr2]; omega)
  refine ⟨heq, ?_⟩
  have hdeg2 : (minpoly K β).natDegree = g.natDegree := by
    have : Module.finrank K K⟮β⟯ = f.natDegree := heq ▸ hfr1
    omega
  have : g = minpoly K β :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβint) hg hdvd (by omega)
  rw [this]
  exact minpoly.irreducible hβint

lemma krasnerCore [CharZero K] (f : K[X]) (hf : f.Monic) (hirr : Irreducible f) :
    ∃ δ > 0, ∀ g : K[X], g.Monic → polyNorm (f - g) < δ →
      g.natDegree = f.natDegree ∧
      (∀ α ∈ (f.map (algebraMap K (AlgebraicClosure K))).roots,
        ∃ β ∈ (g.map (algebraMap K (AlgebraicClosure K))).roots, BelongsTo f β α) ∧
      (∀ β ∈ (g.map (algebraMap K (AlgebraicClosure K))).roots, ∃ α, BelongsTo f β α) ∧
      (∀ α β, BelongsTo f β α → β ∈ (g.map (algebraMap K (AlgebraicClosure K))).roots →
        K⟮α⟯ = K⟮β⟯ ∧ Irreducible g) := by
  have : IsAlgClosed (AlgebraicClosure K) := inferInstance
  have : Algebra.IsAlgebraic K (AlgebraicClosure K) := inferInstance
  let : NormedField (AlgebraicClosure K) := spectralNorm.normedField K (AlgebraicClosure K)
  let : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K (AlgebraicClosure K)
  obtain ⟨d, hd, hsepd, δ, hδ, H⟩ := exists_delta_roots (C := AlgebraicClosure K) f hf hirr.separable
  have hB : ∀ (a b : AlgebraicClosure K), a ∈ (f.map (algebraMap K (AlgebraicClosure K))).roots →
      ‖b - a‖ < d → BelongsTo f b a := fun a b ha hb =>
    ⟨ha, fun α' hα' hne => lt_of_lt_of_le hb (hsepd a ha α' hα' (Ne.symm hne))⟩
  refine ⟨δ, hδ, fun g hg hfg => ?_⟩
  obtain ⟨hdeg, h1, h2⟩ := H g hg hfg
  refine ⟨hdeg, fun α hα => ?_, fun β hβ => ?_, fun α β hbel hβ => ?_⟩
  · obtain ⟨b, hb, hab⟩ := h1 α hα
    exact ⟨b, hb, hB α b hα hab⟩
  · obtain ⟨a, ha, hab⟩ := h2 β hβ
    exact ⟨a, hB a β ha hab⟩
  · exact krasner_step f g hf hirr hg α β hbel.1 hβ hbel.2 hdeg

end Helpers

/-- **Proposition 7.61.** Let $K$ have characteristic zero and let $f \in K[X]$ be monic irreducible. Every monic
$g \in K[X]$ sufficiently close to $f$ is irreducible, and each root $\beta$ of $g$ belongs to some root $\alpha$ of $f$;
for such a root, $K[\alpha] = K[\beta]$. -/
@[kb "milne2020ant" "v3.08, Prop. 7.61, p. 132"]
theorem prop_7_61 [CharZero K] (f : K[X]) (hf : f.Monic) (hirr : Irreducible f) :
    ∃ δ > 0, ∀ g : K[X], g.Monic → polyNorm (f - g) < δ →
      Irreducible g ∧ ∀ β ∈ (g.map (algebraMap K (AlgebraicClosure K))).roots,
        ∃ α, BelongsTo f β α ∧ K⟮α⟯ = K⟮β⟯ := by
  obtain ⟨δ, hδ, H⟩ := krasnerCore f hf hirr
  refine ⟨δ, hδ, fun g hg hfg => ?_⟩
  obtain ⟨hdeg, h1, h2, h3⟩ := H g hg hfg
  have hne : (f.map (algebraMap K (AlgebraicClosure K))).roots ≠ 0 := by
    intro h0
    have := IsAlgClosed.card_roots_eq_natDegree (k := AlgebraicClosure K)
      (p := f.map (algebraMap K (AlgebraicClosure K)))
    rw [h0, natDegree_map] at this
    have := hirr.natDegree_pos
    simp_all
  obtain ⟨α₀, hα₀⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨β₀, hβ₀, hb₀⟩ := h1 α₀ hα₀
  refine ⟨(h3 α₀ β₀ hb₀ hβ₀).2, fun β hβ => ?_⟩
  obtain ⟨α, hα⟩ := h2 β hβ
  exact ⟨α, hα, (h3 α β hα hβ).1⟩

/-- **Proposition 7.63.** Let $K$ have characteristic zero. If two monic irreducible polynomials $f$ and $g$ are
sufficiently close, then each root of $g$ belongs to exactly one root of $f$, and
$\{K[\alpha] : f(\alpha) = 0\} = \{K[\beta] : g(\beta) = 0\}$. Stated for a fixed $f$: there is $\delta > 0$ that works
for every $g$ with $\lVert f - g \rVert < \delta$. -/
@[kb "milne2020ant" "v3.08, Prop. 7.63, p. 133"]
theorem prop_7_63 [CharZero K] (f : K[X]) (hf : f.Monic) (hirr : Irreducible f) :
    ∃ δ > 0, ∀ g : K[X], g.Monic → Irreducible g → polyNorm (f - g) < δ →
      (∀ β ∈ (g.map (algebraMap K (AlgebraicClosure K))).roots, ∃! α, BelongsTo f β α) ∧
      {E | ∃ α ∈ (f.map (algebraMap K (AlgebraicClosure K))).roots, E = K⟮α⟯} =
        {E | ∃ β ∈ (g.map (algebraMap K (AlgebraicClosure K))).roots, E = K⟮β⟯} := by
  obtain ⟨δ, hδ, H⟩ := krasnerCore f hf hirr
  refine ⟨δ, hδ, fun g hg _ hfg => ?_⟩
  obtain ⟨hdeg, h1, h2, h3⟩ := H g hg hfg
  refine ⟨fun β hβ => ?_, ?_⟩
  · obtain ⟨α, hα⟩ := h2 β hβ
    refine ⟨α, hα, fun α₂ hα₂ => ?_⟩
    by_contra hne
    let : NormedField (AlgebraicClosure K) := spectralNorm.normedField K (AlgebraicClosure K)
    let : NormedAlgebra K (AlgebraicClosure K) := spectralNorm.normedAlgebra K (AlgebraicClosure K)
    have : IsUltrametricDist (AlgebraicClosure K) := IsUltrametricDist.of_normedAlgebra K
    have e1 := hα.2 α₂ hα₂.1 hne
    have e2 := hα₂.2 α hα.1 (Ne.symm hne)
    have e1' : ‖β - α‖ < ‖α - α₂‖ := e1
    have e2' : ‖β - α₂‖ < ‖α₂ - α‖ := e2
    have : ‖α - α₂‖ ≤ max ‖α - β‖ ‖β - α₂‖ := by
      calc ‖α - α₂‖ = ‖(α - β) + (β - α₂)‖ := by congr 1; ring
        _ ≤ _ := IsUltrametricDist.norm_add_le_max _ _
    rw [norm_sub_rev α β] at this
    rw [norm_sub_rev α₂ α] at e2'
    rcases max_cases ‖β - α‖ ‖β - α₂‖ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at this <;> linarith
  · ext E
    constructor
    · rintro ⟨α, hα, rfl⟩
      obtain ⟨β, hβ, hbel⟩ := h1 α hα
      exact ⟨β, hβ, (h3 α β hbel hβ).1⟩
    · rintro ⟨β, hβ, rfl⟩
      obtain ⟨α, hα⟩ := h2 β hβ
      exact ⟨α, hα.1, (h3 α β hα hβ).1.symm⟩

/-- **Corollary 7.62.** Let $K$ be a finite extension of $\mathbb Q_p$. Then there is a finite extension $L$ of
$\mathbb Q$ contained in $K$ with $[L : \mathbb Q] = [K : \mathbb Q_p]$ and $L \cdot \mathbb Q_p = K$. -/
@[kb "milne2020ant" "v3.08, Cor. 7.62, p. 132"]
theorem cor_7_62 (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [CharZero E] [Algebra ℚ_[p] E]
    [FiniteDimensional ℚ_[p] E] :
    ∃ L : IntermediateField ℚ E, Module.finrank ℚ L = Module.finrank ℚ_[p] E ∧
      IntermediateField.adjoin ℚ_[p] (L : Set E) = ⊤ := by
  classical
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ_[p] E
  have hαint : IsIntegral ℚ_[p] α := Algebra.IsIntegral.isIntegral α
  set f := minpoly ℚ_[p] α with hfdef
  have hfm : f.Monic := minpoly.monic hαint
  have hfi : Irreducible f := minpoly.irreducible hαint
  have hfrank : Module.finrank ℚ_[p] E = f.natDegree := by
    rw [← IntermediateField.finrank_top', ← hα, IntermediateField.adjoin.finrank hαint]
  obtain ⟨δ, hδ, H⟩ := prop_7_61 f hfm hfi
  have hdense : DenseRange (algebraMap ℚ ℚ_[p]) := by
    have := Padic.denseRange_ratCast (p := p)
    convert this using 1
    funext x
    exact eq_ratCast (algebraMap ℚ ℚ_[p]) x
  obtain ⟨g, hgm, hgdeg, hgc⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hdense hfm
      (half_pos hδ)
  set G := g.map (algebraMap ℚ ℚ_[p]) with hG
  have hGm : G.Monic := hgm.map _
  have hGdeg : G.natDegree = f.natDegree := by rw [hG, natDegree_map, hgdeg]
  have hnorm : polyNorm (f - G) < δ := by
    refine lt_of_le_of_lt (ciSup_le fun i => ?_) (half_lt_self hδ)
    rw [coeff_sub, norm_sub_rev]
    exact (hgc i).le
  obtain ⟨hGirr, hroots⟩ := H G hGm hnorm
  set C := AlgebraicClosure ℚ_[p] with hC
  have hne : (G.map (algebraMap ℚ_[p] C)).roots ≠ 0 := by
    intro h0
    have := IsAlgClosed.card_roots_eq_natDegree (k := C) (p := G.map (algebraMap ℚ_[p] C))
    rw [h0, natDegree_map] at this
    have := hGirr.natDegree_pos
    simp_all
  obtain ⟨β, hβ⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨α', hbel, heq⟩ := hroots β hβ
  have hβ0 : aeval β G = 0 := by
    have := (mem_roots'.1 hβ).2
    simpa [IsRoot.def, eval_map_algebraMap] using this
  have hα'0 : aeval α' f = 0 := by
    have := (mem_roots'.1 hbel.1).2
    simpa [IsRoot.def, eval_map_algebraMap] using this
  let ι : E →ₐ[ℚ_[p]] C := IsAlgClosed.lift
  have hconj : IsConjRoot ℚ_[p] α' (ι α) := by
    have h1 : minpoly ℚ_[p] α' = f := (minpoly.eq_of_irreducible_of_monic hfi hα'0 hfm).symm
    have h2 : minpoly ℚ_[p] (ι α) = f := minpoly.algHom_eq ι ι.injective α
    rw [isConjRoot_def, h1, h2]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  let τ : E →ₐ[ℚ_[p]] C := (σ : C →ₐ[ℚ_[p]] C).comp ι
  have hτα : τ α = α' := hσ
  have hβmem : β ∈ τ.fieldRange := by
    have hle : ℚ_[p]⟮α'⟯ ≤ τ.fieldRange := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact ⟨α, hτα⟩
    exact hle (heq ▸ IntermediateField.mem_adjoin_simple_self ℚ_[p] β)
  obtain ⟨b, hb⟩ := hβmem
  have hb' : τ b = β := hb
  have hb0 : aeval b G = 0 := by
    have h : τ (aeval b G) = τ 0 := by
      rw [← Polynomial.aeval_algHom_apply, hb', hβ0, map_zero]
    exact τ.injective h
  have hgb : aeval b g = 0 := by
    rw [← hb0, hG, aeval_map_algebraMap]
  have hgirr : Irreducible g :=
    hgm.irreducible_of_irreducible_map (algebraMap ℚ ℚ_[p]) g hGirr
  have hgmin : minpoly ℚ b = g := (minpoly.eq_of_irreducible_of_monic hgirr hgb hgm).symm
  have hbint : IsIntegral ℚ b := ⟨g, hgm, by rwa [← aeval_def]⟩
  refine ⟨ℚ⟮b⟯, ?_, ?_⟩
  · rw [IntermediateField.adjoin.finrank hbint, hgmin, ← hgdeg, hfrank]
  · have hbint' : IsIntegral ℚ_[p] b := Algebra.IsIntegral.isIntegral b
    have hGmin : minpoly ℚ_[p] b = G :=
      (minpoly.eq_of_irreducible_of_monic hGirr hb0 hGm).symm
    have hle : ℚ_[p]⟮b⟯ ≤ IntermediateField.adjoin ℚ_[p] ((ℚ⟮b⟯ : IntermediateField ℚ E) : Set E) := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin _ _ (IntermediateField.mem_adjoin_simple_self ℚ b)
    have htop : ℚ_[p]⟮b⟯ = ⊤ := by
      apply IntermediateField.eq_of_le_of_finrank_eq le_top
      rw [IntermediateField.adjoin.finrank hbint', hGmin, hGdeg, IntermediateField.finrank_top',
        hfrank]
    rw [htop] at hle
    exact top_le_iff.1 hle

end NumberFieldKB.MilneANT
