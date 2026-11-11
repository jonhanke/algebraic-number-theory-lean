import NumberFieldKB.MilneANT.Ch7Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# Milne, *Algebraic Number Theory*, Chapter 7: local fields

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

* **Definition 7.48** (`IsLocalFieldMilne`): a field with a nontrivial absolute value for which it is locally compact;
  such a field is complete (`IsLocalFieldMilne.completeSpace`). Milne's notion covers archimedean and
  nonarchimedean local fields; Mathlib's `IsNonarchimedeanLocalField` is the nonarchimedean case, phrased with a
  valuative relation.
* **Remark 7.49** (named statements `Remark7_49a`, `Remark7_49b`, `Remark7_49c`): the classification of local
  fields; consequence `remark_7_49a_locallyCompact` (for archimedean absolute values completeness implies local
  compactness).

The topology of an absolute value $v$ on $K$ is that of Mathlib's type synonym `WithAbs v`.
-/

namespace NumberFieldKB.MilneANT

/-- **Definition 7.48.** A *local field* is a field $K$ with a nontrivial absolute value $|\cdot|$ such that $K$ is
locally compact for the topology of $|\cdot|$. -/
@[kb "milne2020ant" "v3.08, Def. 7.48, p. 126"]
structure IsLocalFieldMilne {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : Prop where
  isNontrivial : v.IsNontrivial
  locallyCompact : LocallyCompactSpace (WithAbs v)

/-- **Definition 7.48**, "(and hence complete)": a local field is complete. -/
@[kb "milne2020ant" "v3.08, Def. 7.48, p. 126"]
theorem IsLocalFieldMilne.completeSpace {K : Type*} [Field K] {v : AbsoluteValue K ℝ} (h : IsLocalFieldMilne v) :
    CompleteSpace (WithAbs v) := by
  have := h.locallyCompact
  exact IsLeftUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace (WithAbs v)

/-- **Remark 7.49(a)** (named statement; Ostrowski, see Artin 1959): a field complete for an archimedean absolute
value is isomorphic to $\mathbb R$ or $\mathbb C$, and the absolute value is equivalent to the usual one. -/
@[kb "milne2020ant" "v3.08, Remark 7.49, p. 127"]
structure Remark7_49a : Prop where
  real_or_complex : ∀ (K : Type) [Field K] (v : AbsoluteValue K ℝ), ¬ IsNonarchimedean v →
    CompleteSpace (WithAbs v) →
    (∃ e : K ≃+* ℝ, v.IsEquiv ((NormedField.toAbsoluteValue ℝ).comp (f := e.toRingHom) e.injective)) ∨
      ∃ e : K ≃+* ℂ, v.IsEquiv ((NormedField.toAbsoluteValue ℂ).comp (f := e.toRingHom) e.injective)

/-- **Remark 7.49(a)**, consequence: for archimedean absolute values, completeness implies local compactness (so a
complete archimedean field is a local field). Conditional on `Remark7_49a`. -/
@[kb "milne2020ant" "v3.08, Remark 7.49, p. 127"]
theorem remark_7_49a_locallyCompact (h : Remark7_49a) (K : Type) [Field K] (v : AbsoluteValue K ℝ)
    (hv : ¬ IsNonarchimedean v) (hc : CompleteSpace (WithAbs v)) : IsLocalFieldMilne v := by
  have hnt : v.IsNontrivial := by
    by_contra hnt
    apply hv
    intro x y
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    rw [AbsoluteValue.not_isNontrivial_apply hnt hx, AbsoluteValue.not_isNontrivial_apply hnt hy]
    rcases eq_or_ne (x + y) 0 with h0 | h0
    · simp [h0]
    · rw [AbsoluteValue.not_isNontrivial_apply hnt h0]; simp
  refine ⟨hnt, ?_⟩
  have key : ∀ (F : Type) [NormedField F] [LocallyCompactSpace F] (e : K ≃+* F),
      v.IsEquiv ((NormedField.toAbsoluteValue F).comp (f := e.toRingHom) e.injective) →
      LocallyCompactSpace (WithAbs v) := by
    intro F _ _ e he
    set w := (NormedField.toAbsoluteValue F).comp (f := e.toRingHom) e.injective with hw
    have h1 : IsHomeomorph (WithAbs.congr v w (RingEquiv.refl K)) :=
      (AbsoluteValue.isEquiv_iff_isHomeomorph v w).1 he
    let ι : WithAbs w ≃ₜ F :=
      (IsometryEquiv.mk (⟨fun x => e x.ofAbs, fun y => WithAbs.toAbs w (e.symm y), fun x => by simp,
        fun y => by simp⟩ : WithAbs w ≃ F) (Isometry.of_dist_eq (fun x y => by
          show dist (e x.ofAbs) (e y.ofAbs) = dist x y
          simp [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, hw, ← map_sub]))).toHomeomorph
    let H : WithAbs v ≃ₜ F := h1.homeomorph.trans ι
    exact H.isOpenEmbedding.locallyCompactSpace
  rcases h.real_or_complex K v hv hc with ⟨e, he⟩ | ⟨e, he⟩
  · exact key ℝ e he
  · exact key ℂ e he

/-- **Remark 7.49(b)** (named statement): a nonarchimedean local field $K$ of characteristic zero is a finite
extension of $\mathbb Q_p$ for some prime $p$, and its absolute value is equivalent to the (unique) extension of the
$p$-adic absolute value. -/
@[kb "milne2020ant" "v3.08, Remark 7.49, p. 127"]
structure Remark7_49b : Prop where
  finite_ext_padic : ∀ (K : Type) [Field K] [CharZero K] (v : AbsoluteValue K ℝ), IsNonarchimedean v →
    IsLocalFieldMilne v →
    ∃ (p : ℕ) (_ : Fact p.Prime) (φ : ℚ_[p] →+* K),
      @FiniteDimensional ℚ_[p] K _ _ φ.toModule ∧
        (v.comp φ.injective).IsEquiv (NormedField.toAbsoluteValue ℚ_[p])

/-- **Remark 7.49(c)** (named statement): a nonarchimedean local field of characteristic $p \ne 0$ is isomorphic to a
field of formal Laurent series $k((T))$ over a finite field $k$. -/
@[kb "milne2020ant" "v3.08, Remark 7.49, p. 127"]
structure Remark7_49c : Prop where
  laurentSeries : ∀ (K : Type) [Field K] (v : AbsoluteValue K ℝ), ringChar K ≠ 0 → IsLocalFieldMilne v →
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nonempty (K ≃+* LaurentSeries k)

end NumberFieldKB.MilneANT
