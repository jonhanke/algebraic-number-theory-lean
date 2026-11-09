import NumberFieldKB.MilneCFT.LubinTate.Complements
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.AlgebraicExtension.Basic
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Lemma 3.12 of Milne, *Class Field Theory*, Chapter I: subfields of $K^{\mathrm{sep}}$ are closed

Every intermediate field $E$ of $\Omega/K$ ($\Omega$ a separable closure of the nonarchimedean local field $K$, with a
valuation extending that of $K$ and the valuation topology) is closed. Milne's proof: $\mathrm{Gal}(\Omega/E)$ fixes
$E$, hence by continuity its closure, so the closure is $E$ by Galois theory.

Here the continuity step is done by hand: the automorphisms of $\Omega/K$ preserve the valuation (Tau Ceti's
`AlgEquiv.valuation_eq`, ported under `NumberFieldKB/TauCetiPort/`, Apache 2.0: the extended valuation is unique), so
if $x$ is in the closure of $E$ and $\sigma$ fixes $E$, then for $e\in E$ close to $x$,
$v(\sigma x - x) = v((e - x) - \sigma(e - x)) \le v(e - x)$, which is as small as we like; hence $\sigma x = x$. The
Galois correspondence for the (infinite) Galois extension $\Omega/K$ is Mathlib's
`InfiniteGalois.fixedField_fixingSubgroup`.
-/

open scoped ValuativeRel

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

variable (K Ω) in
/-- **Lemma 3.12, proved** (Milne, *CFT*, I, Lemma 3.12): every intermediate field of $\Omega/K$ is closed for the
topology of a valuation extending that of $K$. -/
@[kb "milne2020cft" "Ch. I, Lemma 3.12"]
theorem subfieldsClosed : SubfieldsClosed K Ω := by
  refine ⟨fun E => ?_⟩
  have : Algebra.IsAlgebraic K Ω := Algebra.IsSeparable.isAlgebraic K Ω
  rw [← closure_subset_iff_isClosed]
  intro x hx
  have hfix : ∀ σ ∈ E.fixingSubgroup, σ x = x := by
    intro σ hσ
    by_contra hne
    have hd : ValuativeRel.valuation Ω (σ x - x) ≠ 0 := by
      rw [Ne, map_eq_zero, sub_eq_zero]; exact hne
    obtain ⟨e, he, heE⟩ := mem_closure_iff_nhds.1 hx
      {z | ValuativeRel.valuation Ω (z - x) < (Units.mk0 _ hd : (ValuativeRel.ValueGroupWithZero Ω)ˣ)}
      (IsValuativeTopology.mem_nhds_iff'.2 ⟨Units.mk0 _ hd, subset_rfl⟩)
    have hσe : σ e = e := (IntermediateField.mem_fixingSubgroup_iff E σ).1 hσ e heE
    have h1 : σ x - x = (e - x) - σ (e - x) := by rw [map_sub, hσe]; ring
    have h2 : ValuativeRel.valuation Ω (σ (e - x)) = ValuativeRel.valuation Ω (e - x) :=
      AlgEquiv.valuation_eq (K := K) σ (e - x)
    have h3 := Valuation.map_sub (ValuativeRel.valuation Ω) (e - x) (σ (e - x))
    rw [← h1, h2, max_self] at h3
    have he' : ValuativeRel.valuation Ω (e - x) < ValuativeRel.valuation Ω (σ x - x) := he
    exact absurd (lt_of_le_of_lt h3 he') (lt_irrefl _)
  rw [← InfiniteGalois.fixedField_fixingSubgroup E]
  exact (IntermediateField.mem_fixedField_iff _ _).2 hfix

end NumberFieldKB.MilneCFT.LocalCFT
