import NumberFieldKB.MilneCFT.Ch2TateTriviality
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.Cup.TateTheorem

/-!
# Milne, *Class Field Theory*, Chapter II, Theorem 3.11 (Tate's theorem), proved from Tau Ceti

The named statement `NumberFieldKB.MilneCFT.Thm3_11` (Milne II, Theorem 3.11, p. 84) is proved here (`thm3_11`) from
Tau Ceti's `TauCeti.TateCohomology.cup_bijective_of_forall_isPGroup` (ported,
`NumberFieldKB/TauCetiPort/RepresentationTheory/Homological/TateCohomology/Cup/TateTheorem.lean`; Apache 2.0, the Tau
Ceti contributors): for a generator $u$ of $H^2_T(G, C)$, cup product with $u$ is a bijection
$H^r_T(G,\mathbb Z) \to H^{r+2}_T(G, \mathbb Z \otimes C)$. Both sides use Mathlib's `tateCohomology`.

The comparison steps: Tate cohomology equals group cohomology in degrees one and two (Mathlib's
`TateCohomology.isoGroupCohomology`); the hypothesis for the subgroup $G$ itself is transported along $\top \cong G$
(Mathlib's `groupCohomology.mapIso`); $\mathbb Z \otimes C \cong C$ is the left unitor of `Rep ℤ G`. The isomorphism
obtained is cup product with the generator followed by the unitor (Remark 3.13's description); the named statement
asks only for its existence.
-/

open CategoryTheory Rep Limits MonoidalCategory

namespace NumberFieldKB.MilneCFT

attribute [local instance] fintypeTopSubgroup

/-- Group cohomology of the restriction of `C` to the subgroup `G` itself is that of `C`. -/
noncomputable def groupCohomologyResTopIso {G : Type} [Group G] (C : Rep ℤ G) (n : ℕ) :
    groupCohomology (res (⊤ : Subgroup G).subtype C) n ≅ groupCohomology C n :=
  groupCohomology.mapIso (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G) (LinearEquiv.refl ℤ C.V)
    (fun _ => rfl) n

/-- Cup product on the right with a fixed class, as a linear map (stated over a general commutative ring so that the
instances of Tau Ceti's `cup` apply). -/
noncomputable def cupRight {k G : Type} [CommRing k] [Group G] [Fintype G] (M N : Rep k G) (p q r : ℤ)
    (h : p + q = r) (u : tateCohomology N q) : tateCohomology M p →ₗ[k] tateCohomology (M ⊗ N) r :=
  (TauCeti.TateCohomology.cup M N p q r h).flip u

/-- **Theorem 3.11 (Tate's theorem), proved** (Milne, *CFT*, II, Theorem 3.11, p. 84): if for every subgroup $H$ of
the finite group $G$, $H^1(H, C) = 0$ and $H^2(H, C)$ is cyclic of order $(H:1)$, then for every generator $\gamma$
of $H^2(G, C)$ and every $r \in \mathbb Z$ there is an isomorphism $H^r_T(G,\mathbb Z) \cong H^{r+2}_T(G, C)$ (cup
product with $\gamma$). From Tau Ceti's `TauCeti.TateCohomology.cup_bijective_of_forall_isPGroup` (ported). -/
@[kb "milne2020cft" "v4.03, Ch. II, Thm. 3.11, p. 84"]
theorem thm3_11 : Thm3_11 := by
  refine ⟨fun G _ _ C hC γ hγ r => ?_⟩
  -- Tate cohomology in degree `2` is group cohomology.
  let e2 : tateCohomology C ((2 : ℕ) : ℤ) ≅ groupCohomology C 2 :=
    (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 2).app C
  let u : tateCohomology C 2 := e2.inv.hom γ
  have hgen : ∀ y : tateCohomology C 2, ∃ m : ℤ, m • u = y := by
    intro y
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 (hγ (e2.hom.hom y))
    refine ⟨m, ?_⟩
    have : e2.inv.hom (e2.hom.hom y) = y := by
      rw [← ModuleCat.comp_apply, Iso.hom_inv_id]; rfl
    rw [← this, ← hm, map_zsmul]
  have hcardG : Nat.card (tateCohomology C 2) = Nat.card G := by
    refine (Nat.card_congr e2.toLinearEquiv.toEquiv).trans ?_
    rw [← Nat.card_congr (groupCohomologyResTopIso C 2).toLinearEquiv.toEquiv, (hC ⊤).2.2]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have h1 : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      IsZero (tateCohomology (res S.subtype C) 1) := fun _ _ S _ _ =>
    ((TateCohomology.isoGroupCohomology (R := ℤ) 1).app (res S.subtype C)).isZero_iff.2 (hC S).1
  have hcard : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      Nat.card (tateCohomology (res S.subtype C) 2) = Nat.card S := fun _ _ S _ _ => by
    exact (Nat.card_congr ((TateCohomology.isoGroupCohomology (R := ℤ) 2).app
      (res S.subtype C)).toLinearEquiv.toEquiv).trans (hC S).2.2
  have hb := TauCeti.TateCohomology.cup_bijective_of_forall_isPGroup C u hgen hcardG h1 hcard r (r + 2) rfl
  let f := cupRight (trivial ℤ G ℤ) C r 2 (r + 2) rfl u
  have hf : Function.Bijective f := hb
  exact ⟨(LinearEquiv.ofBijective f hf).toModuleIso ≪≫
    (tateCohomologyFunctor (r + 2)).mapIso (λ_ C)⟩

end NumberFieldKB.MilneCFT
