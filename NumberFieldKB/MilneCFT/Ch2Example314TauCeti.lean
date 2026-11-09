import NumberFieldKB.MilneCFT.Ch2Example314
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Local.ClassFormation
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.UnitsLayer
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.FiniteExtension.IntermediateField

/-!
# Milne, *Class Field Theory*, Chapter II, Example 3.14, from Tau Ceti's local class formation

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

Tau Ceti proves that the units of the separable closure of a nonarchimedean local field form a class formation
(`TauCeti.ClassFieldTheory.localClassFormation`, ported under `NumberFieldKB/TauCetiPort/` from Tau Ceti main
`85f3eb55`, Apache 2.0), and that $H^2$ of a finite layer of a class formation is cyclic of order the degree
(`ClassFormation.isAddCyclic_H2`, `ClassFormation.natCard_H2`). The layer of a finite Galois $L/K$ has cohomology
$H^n(\mathrm{Gal}(L/K), L^\times)$ (`layerCohomologyEquiv`). This proves the first clause of the named statement
`Example3_14` (`cyclic_top_of_localClassFormation`); the second clause is the first one for $L$ over the fixed field
of a subgroup $H$ (`cyclic_of_localClassFormation`), transported along $\mathrm{Gal}(L/L^H)\cong H$.
-/

open CategoryTheory Rep groupCohomology

noncomputable section

namespace NumberFieldKB.MilneCFT

open TauCeti TauCeti.ClassFieldTheory

/-- **Example 3.14, first clause** (Milne, *CFT*, II, Example 3.14, p. 85): for a finite Galois extension $L/K$ of
nonarchimedean local fields, $H^2(\mathrm{Gal}(L/K), L^\times)$ is cyclic of order $[L:K]$. From Tau Ceti's local
class formation. -/
theorem cyclic_top_of_localClassFormation (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    IsAddCyclic (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) = Module.finrank K L := by
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let X := NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)
  let e := layerCohomologyEquiv ι 2
  have hc := (localClassFormation K).isAddCyclic_H2 X
  have hn := (localClassFormation K).natCard_H2 X
  refine ⟨isAddCyclic_of_surjective e.toAddMonoidHom e.surjective, ?_⟩
  change Nat.card (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2) = _
  rw [← Nat.card_congr e.toEquiv, hn, X.degree_eq_natCard_gal, Nat.card_congr (layerGalEquiv ι).toEquiv,
    IsGalois.card_aut_eq_finrank]

/-- **Example 3.14, second clause** (Milne, *CFT*, II, Example 3.14, p. 85): for a subgroup $H$ of $G=\mathrm{Gal}(L/K)$,
$H^2(H, L^\times)$ is cyclic of order $(H:1)$. This is the first clause for $L$ over the fixed field $F = L^H$ (a
nonarchimedean local field with Tau Ceti's structure `TauCeti.finiteIntermediateFieldValuativeRel`), transported
along $H\cong\mathrm{Gal}(L/F)$ (`IntermediateField.fixingSubgroup_fixedField`, `fixingSubgroupEquiv`), which acts
on $L^\times$ in the same way. -/
theorem cyclic_of_localClassFormation (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup (L ≃ₐ[K] L)) :
    IsAddCyclic (groupCohomology (res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) ∧
      Nat.card (groupCohomology (res H.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) = Nat.card H := by
  let F := IntermediateField.fixedField H
  let _ : ValuativeRel F := TauCeti.finiteIntermediateFieldValuativeRel K L F
  let _ : TopologicalSpace F := TauCeti.finiteIntermediateFieldTopology K L F
  have : IsNonarchimedeanLocalField F := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K L F
  obtain ⟨-, hn⟩ := cyclic_top_of_localClassFormation F L
  let e : H ≃* (L ≃ₐ[F] L) :=
    (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField H).symm).trans
      (IntermediateField.fixingSubgroupEquiv F)
  let φ := groupCohomology.mapIso (A := Rep.ofAlgebraAutOnUnits F L)
    (B := res H.subtype (Rep.ofAlgebraAutOnUnits K L)) e (LinearEquiv.refl ℤ _)
    (fun _ => LinearMap.ext fun _ => rfl) 2
  let ψ := φ.toLinearEquiv.toAddEquiv
  obtain ⟨hc, -⟩ := cyclic_top_of_localClassFormation F L
  refine ⟨isAddCyclic_of_surjective ψ.symm.toAddMonoidHom ψ.symm.surjective, ?_⟩
  rw [Nat.card_congr ψ.toEquiv, hn, ← IsGalois.card_aut_eq_finrank, Nat.card_congr e.toEquiv.symm]

/-- **Example 3.14, proved** (Milne, *CFT*, II, Example 3.14, p. 85): the named statement `Example3_14` holds, from
Tau Ceti's local class formation (ported). -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 3.14, p. 85"]
theorem example3_14 : Example3_14 :=
  ⟨fun K _ _ _ _ L _ _ _ _ => cyclic_top_of_localClassFormation K L,
   fun K _ _ _ _ L _ _ _ _ H => cyclic_of_localClassFormation K L H⟩

end NumberFieldKB.MilneCFT
