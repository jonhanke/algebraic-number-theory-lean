import NumberFieldKB.MilneCFT.Ch7.Theorem51
import NumberFieldKB.MilneCFT.Ch7.Cohomology
import NumberFieldKB.MilneCFT.Ch8.H2TauCeti
import NumberFieldKB.Ideles.RelativeNormTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.IdeleClass.SecondInequality
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.IdeleClass.HerbrandQuotient
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.Reciprocity
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Milne, *Class Field Theory*, Chapter VII, Theorems 4.3 and 5.1 from the Tau Ceti port

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, Chapter VII,
§§4–6 (pp. 211–218).

The named statements `Theorem4_3` ($h(C_L) = [L:K]$ for cyclic $L/K$) and `Theorem5_1` (the second inequality,
$H^1(G, C_L) = 0$, $|H^2(G,C_L)|$ divides $[L:K]$) are proved here from Tau Ceti's global class field theory (ported
under `NumberFieldKB/TauCetiPort/`, Apache 2.0, the Tau Ceti contributors):

* `TauCeti.ClassFieldTheory.herbrandQuotient_ideleClassRep_eq_finrank` (the same `G`-module `ideleClassRep`; Tau Ceti's
  Herbrand quotient divides by $|H^{-1}_T|$, Milne's by $|H^1|$, equal for cyclic $G$ by periodicity, Chapter II);
* `TauCeti.ClassFieldTheory.subsingleton_groupCohomology_one_ideleClassRep`;
* `TauCeti.ClassFieldTheory.natCard_H2_globalFormation_dvd_degree`, read on $H^2(\mathrm{Gal}(L/K), C_L)$ through
  `globalLayerCohomologyEquiv`;
* the index $(\mathbb I_K : K^\times\mathrm{Nm}(\mathbb I_L)) = |\mathrm{Gal}(L/K)^{\mathrm{ab}}|$ from
  `globalArtinEquiv`, with the comparison of idèle norms `NumberFieldKB.Ideles.ideleRelNorm_eq_ideleNormMap`.

Milne's reductions (Lemmas 5.3, 5.4, 6.1) conclude Theorem 5.1 (or its part (a)) for all extensions of the relevant
kind; with Theorem 5.1 proved outright their conclusions hold, which proves them.
-/

open IsDedekindDomain NumberField CategoryTheory CategoryTheory.Limits

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

/-- $K^\times\mathrm{Nm}(\mathbb I_L)$ is the preimage in $\mathbb I_K$ of Tau Ceti's norm group
$\mathrm{Nm}_{L/K}(C_L)\subseteq C_K$. -/
theorem principalNormIdeles_eq_comap :
    principalNormIdeles K L =
      (TauCeti.GlobalNumberFields.ideleClassNormMap K L :
          IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range.comap
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) := by
  ext x
  rw [Subgroup.mem_comap]
  constructor
  · intro hx
    obtain ⟨p, hp, q, ⟨y, rfl⟩, rfl⟩ := Subgroup.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := hp
    refine ⟨(y : IdeleClassGroup (𝓞 L) L), ?_⟩
    change TauCeti.GlobalNumberFields.ideleClassNormMap K L (y : IdeleClassGroup (𝓞 L) L) = _
    rw [TauCeti.GlobalNumberFields.ideleClassNormMap_mk]
    have hy : ideleNorm K L y = TauCeti.GlobalNumberFields.ideleNormMap K L y :=
      Ideles.ideleRelNorm_eq_ideleNormMap (Module.finBasis K L) y
    rw [← hy, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff (N := IdeleGroup.principalSubgroup (𝓞 K) K) _).2 ⟨a, rfl⟩]
    exact (one_mul (_ : IdeleClassGroup (𝓞 K) K)).symm
  · rintro ⟨c, hc⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    change TauCeti.GlobalNumberFields.ideleClassNormMap K L (y : IdeleClassGroup (𝓞 L) L) = _ at hc
    rw [TauCeti.GlobalNumberFields.ideleClassNormMap_mk] at hc
    obtain ⟨a, ha⟩ := QuotientGroup.eq.mp hc
    have hx : x = TauCeti.GlobalNumberFields.ideleNormMap K L y *
        IdeleGroup.unitEmbedding (𝓞 K) K a := by
      rw [ha]; simp
    rw [hx]
    refine mul_mem (Subgroup.mem_sup_right ⟨y, ?_⟩) (Subgroup.mem_sup_left ⟨a, rfl⟩)
    exact Ideles.ideleRelNorm_eq_ideleNormMap (Module.finBasis K L) y

variable [IsGalois K L]

/-- $(\mathbb I_K : K^\times\mathrm{Nm}(\mathbb I_L)) = |\mathrm{Gal}(L/K)^{\mathrm{ab}}|$ (global reciprocity,
Tau Ceti's `globalArtinEquiv`). -/
theorem index_principalNormIdeles :
    (principalNormIdeles K L).index = Nat.card (Abelianization Gal(L/K)) := by
  rw [principalNormIdeles_eq_comap, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),
    Subgroup.index]
  exact (Nat.card_congr (Additive.ofMul.trans
    (TauCeti.ClassFieldTheory.globalArtinEquiv K L IsSepClosed.lift).toEquiv)).trans
    (Nat.card_congr Additive.ofMul.symm)

/-- **Theorem 5.1 (a)**: $(\mathbb I_K : K^\times\mathrm{Nm}(\mathbb I_L))$ is finite and divides $[L:K]$. -/
theorem principalNormIdeles_index_dvd :
    (principalNormIdeles K L).FiniteIndex ∧ (principalNormIdeles K L).index ∣ Module.finrank K L := by
  have hdvd : (principalNormIdeles K L).index ∣ Module.finrank K L := by
    rw [index_principalNormIdeles, ← IsGalois.card_aut_eq_finrank]
    exact Subgroup.index_dvd_card (commutator Gal(L/K))
  exact ⟨⟨fun h => by rw [h] at hdvd; exact Module.finrank_pos.ne' (Nat.eq_zero_of_zero_dvd hdvd)⟩, hdvd⟩

/-- **Theorem 5.1 (b)**: $H^1(G, C_L) = 0$. -/
theorem isZero_h1_ideleClassRep : IsZero (groupCohomology (ideleClassRep K L) 1) := by
  rw [ideleClassRep_eq_tauCeti]
  have : Subsingleton (groupCohomology (TauCeti.ClassFieldTheory.ideleClassRep K L) 1) :=
    TauCeti.ClassFieldTheory.subsingleton_groupCohomology_one_ideleClassRep K L
  exact ModuleCat.isZero_of_subsingleton _

/-- **Theorem 5.1 (c)**: $H^2(G, C_L)$ is finite of order dividing $[L:K]$. -/
theorem h2_ideleClassRep_card_dvd :
    Finite (groupCohomology (ideleClassRep K L) 2) ∧
      Nat.card (groupCohomology (ideleClassRep K L) 2) ∣ Module.finrank K L := by
  rw [ideleClassRep_eq_tauCeti]
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let Lay := TauCeti.ClassFieldTheory.NormalLayer.ofOpenNormal (TauCeti.fixingOpenNormalSubgroup K L)
  have hdeg : Lay.degree = Module.finrank K L := by
    rw [TauCeti.ClassFieldTheory.NormalLayer.degree_eq_natCard_gal,
      Nat.card_congr (TauCeti.ClassFieldTheory.layerGalEquiv ι).toEquiv,
      IsGalois.card_aut_eq_finrank]
  have hdvd : Nat.card (groupCohomology (TauCeti.ClassFieldTheory.ideleClassRep K L) 2) ∣ Module.finrank K L := by
    rw [← Nat.card_congr (TauCeti.ClassFieldTheory.globalLayerCohomologyEquiv ι 2).toEquiv, ← hdeg]
    exact TauCeti.ClassFieldTheory.natCard_H2_globalFormation_dvd_degree Lay
  refine ⟨Nat.finite_of_card_ne_zero fun h => ?_, hdvd⟩
  rw [h] at hdvd
  exact Module.finrank_pos.ne' (Nat.eq_zero_of_zero_dvd hdvd)

/-- Theorem 5.1 for one Galois extension (`Thm51For`). -/
theorem thm51For : Thm51For K L :=
  ⟨principalNormIdeles_index_dvd K L, isZero_h1_ideleClassRep K L, h2_ideleClassRep_card_dvd K L⟩

/-- **Theorem 5.1, unconditional** (Milne, *CFT*, Chapter VII, p. 212): for every Galois extension $L/K$ of number
fields, (a) $(\mathbb I_K : K^\times\mathrm{Nm}(\mathbb I_L))$ is finite and divides $[L:K]$, (b) $H^1(G, C_L) = 0$,
(c) $H^2(G, C_L)$ is finite of order dividing $[L:K]$. From the Tau Ceti port. -/
@[kb "milne2020cft" "Ch. VII, Thm. 5.1"]
theorem theorem5_1 : Theorem5_1 K where
  index_dvd L _ _ _ _ := principalNormIdeles_index_dvd K L
  h1 L _ _ _ _ := isZero_h1_ideleClassRep K L
  h2 L _ _ _ _ := h2_ideleClassRep_card_dvd K L

/-- **Lemma 5.3, unconditional** (Milne, *CFT*, Chapter VII, p. 212): its conclusion, Theorem 5.1 for every Galois
extension, holds (`thm51For`). -/
@[kb "milne2020cft" "Ch. VII, Lemma 5.3"]
theorem lemma5_3 : Lemma5_3 where
  reduce _ F L _ _ _ _ _ _ := thm51For F L

/-- **Lemma 5.4, unconditional** (Milne, *CFT*, Chapter VII, p. 213): its conclusion holds (`thm51For`). -/
@[kb "milne2020cft" "Ch. VII, Lemma 5.4"]
theorem lemma5_4 : Lemma5_4 where
  reduce _ _ _ F L _ _ _ _ _ _ _ := thm51For F L

/-- **Lemma 6.1, unconditional** (Milne, *CFT*, Chapter VII, p. 214): its conclusion, the second inequality for
cyclic extensions of prime degree, holds. -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.1"]
theorem lemma6_1 : Lemma6_1 where
  reduce p _ _ F L _ _ _ _ _ _ hcard := by
    have h := principalNormIdeles_index_dvd F L
    rwa [← IsGalois.card_aut_eq_finrank, hcard] at h

/-! ## Theorem 4.3 -/

/-- **Theorem 4.3, unconditional** (Milne, *CFT*, Chapter VII, p. 211): for a cyclic extension $L/K$ of number fields,
$h(C_L)$ is defined and equals $[L:K]$. From Tau Ceti's `herbrandQuotient_ideleClassRep_eq_finrank`, whose
denominator $|H^{-1}_T|$ equals Milne's $|H^1_T|$ by periodicity (`periodicity`). -/
@[kb "milne2020cft" "Ch. VII, Thm. 4.3"]
theorem theorem4_3 : Theorem4_3 K where
  herbrand L _ _ _ _ hc := by
    haveI : IsCyclic Gal(L/K) := hc
    rw [ideleClassRep_eq_tauCeti]
    have hq := TauCeti.ClassFieldTheory.herbrandQuotient_ideleClassRep_eq_finrank (K := K) L
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
    have c1 : Nat.card (tateCohomology (TauCeti.ClassFieldTheory.ideleClassRep K L) (-1)) =
        Nat.card (tateCohomology (TauCeti.ClassFieldTheory.ideleClassRep K L) 1) :=
      Nat.card_congr (periodicity g hg (TauCeti.ClassFieldTheory.ideleClassRep K L) (-1)).toLinearEquiv.toEquiv
    rw [TauCeti.TateCohomology.herbrandQuotient_def, c1] at hq
    have hn : (Module.finrank K L : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    have h0 : Nat.card (tateCohomology (TauCeti.ClassFieldTheory.ideleClassRep K L) 0) ≠ 0 := by
      intro h; rw [h] at hq; simp at hq; exact hn hq.symm
    have h1 : Nat.card (tateCohomology (TauCeti.ClassFieldTheory.ideleClassRep K L) 1) ≠ 0 := by
      intro h; rw [h] at hq; simp at hq; exact hn hq.symm
    exact ⟨⟨Nat.finite_of_card_ne_zero h0, Nat.finite_of_card_ne_zero h1⟩, hq⟩

end NumberFieldKB.MilneCFT.Ch7
