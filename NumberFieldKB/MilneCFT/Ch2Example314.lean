import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Tate

/-!
# Milne, *Class Field Theory*, Chapter II §3: Example 3.14

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

Example 3.14 announces the main input of local class field theory (proved in Chapter III, Theorem 3.1 there) and
its consequence by Tate's theorem. We record the announced fact as a named statement and prove the consequence
from it and the named Tate's theorem (`Thm3_11`).
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology Limits

/-- **Example 3.14** (p. 85), the announced fact, as a named statement. Let $K$ be a nonarchimedean local field
(Mathlib's `IsNonarchimedeanLocalField`) and $L/K$ a finite Galois extension with group $G$. Then
$H^2(G, L^\times)$ is cyclic of order $[L : K]$ (`cyclic_top`). Also recorded (`cyclic`): for every subgroup $H$
of $G$, $H^2(H, L^\times)$ is cyclic of order $(H : 1)$; this is the same statement for the Galois extension
$L/L^H$ (with $L^H$ again a local field), written directly for $H \subseteq G$ to avoid transporting between
$\operatorname{Gal}(L/L^H)$ and $H$. The canonical generator (the fundamental class, defined by the invariant
map) is not part of this statement. Proved in Chapter III (Theorem III.3.1).

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.ClassFieldTheory.ClassFormation.isAddCyclic_H2`
(`TauCeti/NumberTheory/ClassFieldTheory/Formation/ClassFormation.lean:170`),
`TauCeti.ClassFieldTheory.ClassFormation.natCard_H2` (same file, line 125) and
`TauCeti.ClassFieldTheory.localClassFormation` (`TauCeti/NumberTheory/ClassFieldTheory/Local/ClassFormation.lean:119`)
at Tau Ceti commit `7ed979dc`. Needed to apply it here: identify the second cohomology group of a finite layer in
Tau Ceti (via `TauCeti.ClassFieldTheory.layerCohomologyEquiv`) with the second group cohomology of the Galois group
acting on the units of `L`; the clause for subgroups is the same statement for `L` over the fixed field of the
subgroup, which is again a local field.

**Proved here** as `example3_14` (`Ch2Example314TauCeti.lean`), from the ported Tau Ceti
`localClassFormation`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 3.14, p. 85"]
structure Example3_14 : Prop where
  cyclic_top : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    IsAddCyclic (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) = Module.finrank K L
  cyclic : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)),
    IsAddCyclic (groupCohomology (res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) ∧
      Nat.card (groupCohomology (res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) = Nat.card H

/-- **Example 3.14** (p. 85), the consequence: for a finite Galois extension $L/K$ of nonarchimedean local fields
with group $G$, Tate's theorem gives isomorphisms $H^r_T(G, \mathbb Z) \simeq H^{r+2}_T(G, L^\times)$ for all $r$;
for $r = -2$ this is $G^{\mathrm{ab}} \simeq H_1(G, \mathbb Z) = H^{-2}_T(G, \mathbb Z) \simeq H^0_T(G, L^\times) =
K^\times / \operatorname{Nm}(L^\times)$, the inverse of the local Artin map. Proved from the named
statements `Thm3_11` and `Example3_14` with Hilbert's Theorem 90 (`isZero_h1_fixingSubgroup`). -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 3.14, p. 85"]
theorem example_3_14 (h311 : Thm3_11) (h314 : Example3_14) (K : Type) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (L : Type) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (r : ℤ) :
    Nonempty (tateCohomology (trivial ℤ (L ≃ₐ[K] L) ℤ) r ≅
      tateCohomology (Rep.ofAlgebraAutOnUnits K L) (r + 2)) := by
  have hyp : ∀ H : Subgroup (L ≃ₐ[K] L),
      IsZero (groupCohomology (res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 1) ∧
      IsAddCyclic (groupCohomology (res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) ∧
      Nat.card (groupCohomology (res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) = Nat.card H := by
    intro H
    refine ⟨?_, h314.cyclic K L H⟩
    rw [← IntermediateField.fixingSubgroup_fixedField H]
    exact isZero_h1_fixingSubgroup K L _
  obtain ⟨γ, hγ⟩ := (h314.cyclic_top K L).1.exists_generator
  exact h311.iso (L ≃ₐ[K] L) (Rep.ofAlgebraAutOnUnits K L) hyp γ hγ r

end NumberFieldKB.MilneCFT
