import NumberFieldKB.MilneCFT.Ch2Tate
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.TrivialityCriterion
import Mathlib.Computability.Reduce
import Mathlib.GroupTheory.PGroup
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Milne, *Class Field Theory*, Chapter II, Theorem 3.10, proved from Tau Ceti

The named statement `NumberFieldKB.MilneCFT.Thm3_10` (Tate's criterion for cohomological triviality, Milne II,
Theorem 3.10, p. 83) is proved here from Tau Ceti's `TauCeti.TateCohomology.isZero_of_forall_isPGroup` (ported,
`NumberFieldKB/TauCetiPort/RepresentationTheory/Homological/TateCohomology/TrivialityCriterion.lean`; Tau Ceti main
`67aa1716`, Apache 2.0). Tau Ceti asks for vanishing in two consecutive Tate degrees on subgroups of prime-power order
only; Milne's hypothesis (degrees one and two, every subgroup) is stronger, and Tate cohomology agrees with group
cohomology in positive degrees (Mathlib's `TateCohomology.isoGroupCohomology`).

Tau Ceti concludes vanishing for the restriction of $M$ to every subgroup; for the subgroup $G$ itself this is the
restriction along `(⊤ : Subgroup G).subtype`. `isZero_tateCohomology_of_isZero_res_top` transfers it to $M$: in
positive degrees through group cohomology and the isomorphism $\top \cong G$ (Mathlib's `groupCohomology.mapIso`), in
other degrees by Tau Ceti's dimension shifting, which commutes with restriction.
-/

open CategoryTheory Rep Limits

namespace NumberFieldKB.MilneCFT

universe u

/-- The subgroup $G$ of a finite group $G$ is finite (chosen through `Fintype.ofFinite`; Tate cohomology of a
representation of `⊤` needs a `Fintype` instance on `⊤`). -/
noncomputable def fintypeTopSubgroup {G : Type*} [Group G] [Finite G] : Fintype (⊤ : Subgroup G) :=
  Fintype.ofFinite _

attribute [local instance] fintypeTopSubgroup

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

omit [Fintype G] in
/-- Group cohomology of $M$ vanishes if that of its restriction to the subgroup $G$ itself does. -/
theorem isZero_groupCohomology_of_isZero_res_top (A : Rep k G) (n : ℕ)
    (h : IsZero (groupCohomology (res (⊤ : Subgroup G).subtype A) n)) :
    IsZero (groupCohomology A n) :=
  (groupCohomology.mapIso (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G) (LinearEquiv.refl k A.V)
    (fun _ => rfl) n).isZero_iff.1 h

/-- Tate cohomology of $M$ vanishes in degree $n$ if that of its restriction to the subgroup $G$ itself does (by
induction on the number $d$ of dimension shifts needed to reach a positive degree). -/
theorem isZero_tateCohomology_of_isZero_res_top_aux : ∀ (d : ℕ) (A : Rep k G) (n : ℤ), 1 ≤ n + d →
    IsZero (tateCohomology (res (⊤ : Subgroup G).subtype A) n) → IsZero (tateCohomology A n)
  | 0, A, n, hn, h => by
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = ((m + 1 : ℕ) : ℤ) := ⟨(n - 1).toNat, by omega⟩
    have e1 := (TateCohomology.isoGroupCohomology (R := k) (G := G) (m + 1)).app A
    have e2 := (TateCohomology.isoGroupCohomology (R := k) (G := (⊤ : Subgroup G)) (m + 1)).app
      (res (⊤ : Subgroup G).subtype A)
    exact e1.isZero_iff.2 (isZero_groupCohomology_of_isZero_res_top A (m + 1) (e2.isZero_iff.1 h))
  | d + 1, A, n, hn, h => by
    rw [← TauCeti.TateCohomology.isZero_dimensionShiftDown_iff]
    exact isZero_tateCohomology_of_isZero_res_top_aux d _ (n + 1) (by omega)
      ((TauCeti.TateCohomology.isZero_res_dimensionShiftDown_iff A ⊤ n).2 h)

/-- Tate cohomology of $M$ vanishes in degree $n$ if that of its restriction to the subgroup $G$ itself does. -/
theorem isZero_tateCohomology_of_isZero_res_top (A : Rep k G) (n : ℤ)
    (h : IsZero (tateCohomology (res (⊤ : Subgroup G).subtype A) n)) : IsZero (tateCohomology A n) :=
  isZero_tateCohomology_of_isZero_res_top_aux (1 - n).toNat A n (by omega) h

/-- **Theorem 3.10, proved** (Milne, *CFT*, II, Theorem 3.10, p. 83): the named statement `Thm3_10` holds. Let $G$ be
a finite group and $M$ a $G$-module with $H^1(H, M) = 0 = H^2(H, M)$ for all subgroups $H$; then
$H^r_T(G, M) = 0$ for all $r$. From Tau Ceti's `TauCeti.TateCohomology.isZero_of_forall_isPGroup` (ported). -/
@[kb "milne2020cft" "v4.03, Ch. II, Thm. 3.10, p. 83"]
theorem thm3_10 : Thm3_10 := by
  refine ⟨fun G _ _ M h r => ?_⟩
  have h1 : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      IsZero (tateCohomology (res S.subtype M) ((1 : ℕ) : ℤ)) := fun _ _ S _ _ =>
    ((TateCohomology.isoGroupCohomology 1).app (res S.subtype M)).isZero_iff.2 (h S).1
  have h2 : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      IsZero (tateCohomology (res S.subtype M) (((1 : ℕ) : ℤ) + 1)) := fun _ _ S _ _ =>
    ((TateCohomology.isoGroupCohomology 2).app (res S.subtype M)).isZero_iff.2 (h S).2
  exact isZero_tateCohomology_of_isZero_res_top M r
    (TauCeti.TateCohomology.isZero_of_forall_isPGroup M h1 h2 ⊤ r)

end NumberFieldKB.MilneCFT
