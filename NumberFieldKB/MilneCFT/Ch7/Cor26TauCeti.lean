import NumberFieldKB.MilneCFT.Ch7.Cohomology
import NumberFieldKB.MilneCFT.Ch8.H2TauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Local.ClassFormation
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.UnitsLayer
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.PlacewiseCohomology
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Brauer.Archimedean.ClassFormation
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.InfinitePlace.Completion.DecompositionGroup
import NumberFieldKB.TauCetiPort.RingTheory.DedekindDomain.AdicValuation.LocalDegree
import NumberFieldKB.TauCetiPort.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Milne, *Class Field Theory*, Chapter VII, Corollary 2.6, proved from Tau Ceti

The named statement `NumberFieldKB.MilneCFT.Ch7.Cor2_6` ($H^1(G,\mathbb I_L)=0$ and
$H^2(G,\mathbb I_L)\cong\bigoplus_v\mathbb Z/n_v\mathbb Z$) is proved here (`Ch7.cor2_6`) for every finite Galois
extension $L/K$ of number fields, from the ported Tau Ceti development:

* `TauCeti.ClassFieldTheory.subsingleton_groupCohomology_one_idelesRep` (Hilbert 90 for the ideles, from
  `isZero_tateCohomology_one_idelesRep`) gives $H^1(G,\mathbb I_L)=0$;
* `TauCeti.ClassFieldTheory.idelesCohomologyLocalizationEquiv` identifies $H^2(G,\mathbb I_L)$ with
  $\bigoplus_{v\nmid\infty}H^2(G,(K_v\otimes L)^\times)\times\prod_{v\mid\infty}H^2(G,(K_v\otimes L)^\times)$;
* Shapiro's lemma (`IsDedekindDomain.HeightOneSpectrum.semilocalUnitsTateCohomologyIsoPos`,
  `NumberField.InfinitePlace.infiniteSemilocalUnitsTateCohomologyIsoPos`) identifies each factor with
  $H^2(\mathrm{Gal}(L_w/K_v),L_w^\times)$;
* the local class formations `TauCeti.ClassFieldTheory.localClassFormation` (finite $v$) and
  `TauCeti.ClassFieldTheory.infiniteClassFormation` (infinite $v$) make that group cyclic of order $[L_w:K_v]$
  (`ClassFormation.isAddCyclic_H2`, `ClassFormation.natCard_H2`), which is `localDegree` by
  `IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletion` and
  `NumberField.InfinitePlace.finrank_completion_eq_ite`.

Our Galois action on the idèles is Tau Ceti's (`instMulDistribMulActionIdeleGroup_eq_tauCeti`), so `ideleRep K L` is
Tau Ceti's `idelesRep K L` (`ideleRep_eq_tauCeti`).
-/

open CategoryTheory CategoryTheory.Limits IsDedekindDomain NumberField TauCeti TauCeti.ClassFieldTheory
open scoped AdicCompletionExtension NumberField.LiesOver

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K L) in
/-- **The $G$-module $\mathbb I_L$ is Tau Ceti's.** -/
theorem ideleRep_eq_tauCeti : ideleRep K L = TauCeti.ClassFieldTheory.idelesRep K L := by
  unfold ideleRep TauCeti.ClassFieldTheory.idelesRep
  rw [instMulDistribMulActionIdeleGroup_eq_tauCeti]

/-- $H^2$ of the units of a Galois extension, for a class formation on the base: cyclic of order $[E:F]$. -/
theorem cyclic_of_classFormation {F : Type} [Field F] (cf : ClassFormation (unitsFormation F))
    (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] :
    IsAddCyclic (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2) = Module.finrank F E := by
  let ι : E →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let X := NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup F E)
  let e := layerCohomologyEquiv ι 2
  have hc := cf.isAddCyclic_H2 X
  have hn := cf.natCard_H2 X
  refine ⟨isAddCyclic_of_surjective e.toAddMonoidHom e.surjective, ?_⟩
  change Nat.card (groupCohomology (Rep.ofMulDistribMulAction (E ≃ₐ[F] E) Eˣ) 2) = _
  rw [← Nat.card_congr e.toEquiv, hn, X.degree_eq_natCard_gal, Nat.card_congr (layerGalEquiv ι).toEquiv,
    IsGalois.card_aut_eq_finrank]

/-- A cyclic group of order `n` is `ZMod n`. -/
def zmodEquivOfCyclic {G : Type*} [AddCommGroup G] (h : IsAddCyclic G) {n : ℕ} (hn : Nat.card G = n) :
    G ≃+ ZMod n := by
  subst hn
  exact (zmodAddCyclicAddEquiv h).symm

variable [IsGalois K L]

/-- Hilbert 90 for the ideles, in the form of `Cor2_6.h1`. -/
theorem cor2_6_h1 : IsZero (groupCohomology (ideleRep K L) 1) := by
  rw [ideleRep_eq_tauCeti]
  exact ModuleCat.isZero_of_subsingleton _

/-- The local degree at a finite place is the degree of any completion above it. -/
theorem localDegree_inr_eq (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    localDegree K L (Sum.inr v) =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  haveI : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  rw [HeightOneSpectrum.finrank_adicCompletion (R := 𝓞 K) (B := 𝓞 L) v w]
  set Q := Classical.arbitrary (v.asIdeal.primesOver (𝓞 L))
  have := v.isPrime
  have := Q.2.1
  have := Q.2.2
  have := w.isPrime
  have h1 := Ideal.ramificationIdx_eq_of_isGaloisGroup v.asIdeal Q.1 w.asIdeal (L ≃ₐ[K] L)
  have h2 := Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal Q.1 w.asIdeal (L ≃ₐ[K] L)
  simp only [localDegree]
  rw [h1, h2]

/-- Each finite place contributes `ZMod (localDegree)`. -/
theorem finite_component (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (tateCohomology (semilocalUnitsRep L v) 2 ≃+ ZMod (localDegree K L (Sum.inr v))) := by
  obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) v
  let A := Rep.ofAlgebraAutOnUnits ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion L)
  let e : tateCohomology (semilocalUnitsRep L (w.under (𝓞 K))) 2 ≃+ groupCohomology A 2 :=
    (HeightOneSpectrum.semilocalUnitsTateCohomologyIsoPos (w.under (𝓞 K)) w 2 ≪≫
      (_root_.TateCohomology.isoGroupCohomology 2).app A).toLinearEquiv.toAddEquiv
  haveI : Finite (𝓞 K ⧸ (w.under (𝓞 K)).asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient (w.under (𝓞 K)).ne_bot
  obtain ⟨hc, hn⟩ := cyclic_of_classFormation
    (localClassFormation ((w.under (𝓞 K)).adicCompletion K)) (w.adicCompletion L)
  exact ⟨e.trans (zmodEquivOfCyclic hc
    (hn.trans (localDegree_inr_eq (w.under (𝓞 K)) w).symm))⟩

/-- Each infinite place contributes `ZMod (localDegree)`. -/
theorem infinite_component (v : InfinitePlace K) :
    Nonempty (tateCohomology (GlobalNumberFields.infiniteSemilocalUnitsRep L v) 2 ≃+
      ZMod (localDegree K L (Sum.inl v))) := by
  classical
  obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := L) v
  have := InfinitePlace.isGalois_completion (w.comap (algebraMap K L)) w
  let A := Rep.ofAlgebraAutOnUnits (w.comap (algebraMap K L)).Completion w.Completion
  let e : tateCohomology (GlobalNumberFields.infiniteSemilocalUnitsRep L (w.comap (algebraMap K L))) 2 ≃+
      groupCohomology A 2 :=
    (InfinitePlace.infiniteSemilocalUnitsTateCohomologyIsoPos (w.comap (algebraMap K L)) w 2 ≪≫
      (_root_.TateCohomology.isoGroupCohomology 2).app A).toLinearEquiv.toAddEquiv
  obtain ⟨hc, hn⟩ := cyclic_of_classFormation
    (infiniteClassFormation (w.comap (algebraMap K L))) w.Completion
  refine ⟨e.trans (zmodEquivOfCyclic hc (hn.trans ?_))⟩
  rw [InfinitePlace.finrank_completion_eq_ite (w.comap (algebraMap K L)) w]
  simp only [localDegree]
  have key : (w.comap (algebraMap K L)).IsUnramifiedIn L ↔
      ¬ InfinitePlace.RamifiesIn L (w.comap (algebraMap K L)) := by
    unfold InfinitePlace.RamifiesIn InfinitePlace.IsUnramifiedIn
    constructor
    · rintro h ⟨hv, w', hw', hc'⟩
      have := h w' hw'
      rw [InfinitePlace.isUnramified_iff, hw'] at this
      rcases this with h1 | h1
      · exact (InfinitePlace.not_isReal_iff_isComplex.mpr hc') h1
      · exact (InfinitePlace.not_isReal_iff_isComplex.mpr h1) hv
    · intro h w' hw'
      rw [InfinitePlace.isUnramified_iff, hw']
      by_cases hr : w'.IsReal
      · exact Or.inl hr
      · refine Or.inr ?_
        by_contra hcon
        exact h ⟨not_not.mp (mt InfinitePlace.not_isReal_iff_isComplex.mp hcon) , w', hw',
          InfinitePlace.not_isReal_iff_isComplex.mp hr⟩
  by_cases h : InfinitePlace.RamifiesIn L (w.comap (algebraMap K L))
  · rw [if_pos h, if_neg (fun h' => (key.mp h') h)]
  · rw [if_neg h, if_pos (key.mpr h)]


/-- A direct sum over a sum type is the product of the direct sums. -/
def directSumSumEquiv {α β : Type} (f : α ⊕ β → Type) [∀ i, AddCommMonoid (f i)] :
    DirectSum (α ⊕ β) f ≃+ DirectSum α (fun a => f (Sum.inl a)) × DirectSum β (fun b => f (Sum.inr b)) := by
  classical
  let Ψ : DirectSum (α ⊕ β) f →+ DirectSum α (fun a => f (Sum.inl a)) × DirectSum β (fun b => f (Sum.inr b)) :=
    { toFun := fun x => (DFinsupp.comapDomain Sum.inl Sum.inl_injective (x : Π₀ i, f i),
        DFinsupp.comapDomain Sum.inr Sum.inr_injective (x : Π₀ i, f i))
      map_zero' := Prod.ext (DFinsupp.ext fun _ => rfl) (DFinsupp.ext fun _ => rfl)
      map_add' := fun x y => Prod.ext (DFinsupp.ext fun _ => rfl) (DFinsupp.ext fun _ => rfl) }
  refine AddEquiv.ofBijective Ψ ⟨?_, ?_⟩
  · intro x y hxy
    refine DFinsupp.ext fun i => ?_
    rcases i with i | i
    · exact congrArg (fun z => (z.1 : Π₀ i, _) i) hxy
    · exact congrArg (fun z => (z.2 : Π₀ i, _) i) hxy
  · have hl : ∀ a : DirectSum α (fun a => f (Sum.inl a)), ∃ x, Ψ x = (a, 0) := by
      intro a
      induction a using DirectSum.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | of i x =>
        refine ⟨DirectSum.of _ (Sum.inl i) x, Prod.ext (DFinsupp.ext fun j => ?_)
          (DFinsupp.ext fun j => ?_)⟩
        · by_cases h : i = j
          · subst h; simp [Ψ, DirectSum.of_apply]
          · simp [Ψ, DirectSum.of_apply, h]
        · simp [Ψ, DirectSum.of_apply]
      | add a b ha hb =>
        obtain ⟨x, hx⟩ := ha
        obtain ⟨y, hy⟩ := hb
        exact ⟨x + y, by rw [map_add, hx, hy]; simp⟩
    have hr : ∀ b : DirectSum β (fun b => f (Sum.inr b)), ∃ x, Ψ x = (0, b) := by
      intro b
      induction b using DirectSum.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | of i x =>
        refine ⟨DirectSum.of _ (Sum.inr i) x, Prod.ext (DFinsupp.ext fun j => ?_)
          (DFinsupp.ext fun j => ?_)⟩
        · simp [Ψ, DirectSum.of_apply]
        · by_cases h : i = j
          · subst h; simp [Ψ, DirectSum.of_apply]
          · simp [Ψ, DirectSum.of_apply, h]
      | add a b ha hb =>
        obtain ⟨x, hx⟩ := ha
        obtain ⟨y, hy⟩ := hb
        exact ⟨x + y, by rw [map_add, hx, hy]; simp⟩
    rintro ⟨a, b⟩
    obtain ⟨x, hx⟩ := hl a
    obtain ⟨y, hy⟩ := hr b
    exact ⟨x + y, by rw [map_add, hx, hy]; simp⟩

/-- **Corollary 2.6, proved** (Milne, *CFT*, VII, Cor. 2.6, p. 206): for every finite Galois extension $L/K$ of
number fields, $H^1(G,\mathbb I_L)=0$ and $H^2(G,\mathbb I_L)\cong\bigoplus_v\mathbb Z/n_v\mathbb Z$. From Tau Ceti's
`idelesCohomologyLocalizationEquiv`, Shapiro's lemma and the local class formations (ported). -/
@[kb "milne2020cft" "Ch. VII, Cor. 2.6"]
theorem cor2_6 (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    Cor2_6 K L := by
  classical
  refine ⟨cor2_6_h1, ?_⟩
  let f := fun v => (finite_component (K := K) (L := L) v).some
  let g := fun v => (infinite_component (K := K) (L := L) v).some
  let e0 : groupCohomology (ideleRep K L) 2 ≃+ tateCohomology (idelesRep K L) 2 := by
    rw [ideleRep_eq_tauCeti]
    exact ((_root_.TateCohomology.isoGroupCohomology 2).app (idelesRep K L)).symm.toLinearEquiv.toAddEquiv
  let e1 := idelesCohomologyLocalizationEquiv K L 2
  let e2 : (Π₀ v : HeightOneSpectrum (𝓞 K), tateCohomology (semilocalUnitsRep L v) 2) ×
      ((w : InfinitePlace K) → tateCohomology (GlobalNumberFields.infiniteSemilocalUnitsRep L w) 2) ≃+
      DirectSum (HeightOneSpectrum (𝓞 K)) (fun v => ZMod (localDegree K L (Sum.inr v))) ×
        DirectSum (InfinitePlace K) (fun w => ZMod (localDegree K L (Sum.inl w))) :=
    (DFinsupp.mapRange.addEquiv f).prodCongr
      ((AddEquiv.piCongrRight g).trans (DirectSum.addEquivProd _).symm)
  exact ⟨e0.trans (e1.trans (e2.trans
    ((AddEquiv.prodComm).trans (directSumSumEquiv (fun v => ZMod (localDegree K L v))).symm)))⟩

end NumberFieldKB.MilneCFT.Ch7
