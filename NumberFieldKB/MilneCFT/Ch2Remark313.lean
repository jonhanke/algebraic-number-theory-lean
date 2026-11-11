import NumberFieldKB.MilneCFT.Ch2CupExists
import NumberFieldKB.MilneCFT.Ch2CupUnique
import NumberFieldKB.MilneCFT.Ch2Remarks
import NumberFieldKB.MilneCFT.Ch2TateTheorem
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.Connecting.GroupCohomology
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.Cup.Delta
import Mathlib.GroupTheory.PGroup
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Milne, *Class Field Theory*, Chapter II, Remark 3.13, proved from Tau Ceti

We compare Tau Ceti's Tate cup product `TauCeti.TateCohomology.cup` with the cup products of
`CupProductFamily` in bidegree `(r, 2)` through the canonical map `Rep.fromGroupCohomology` (ordinary to Tate
cohomology, an isomorphism in positive degrees): by dimension shifting in the first variable along the
sequence (15) (split over `ℤ`), using `TauCeti.TateCohomology.δ_cup_of_leftInverse` and
`TauCeti.TateCohomology.cup_zero_left`. Tate's theorem for Tate's cup product then gives `Remark3_13`.
-/

open CategoryTheory Rep Limits MonoidalCategory

namespace NumberFieldKB.MilneCFT

attribute [local instance] fintypeTopSubgroup

/-- Naturality of the comparison `fromGroupCohomology` in degree `2`. -/
theorem fromGroupCohomology_two_natural {G : Type} [Group G] [Fintype G] {A B : Rep ℤ G} (f : A ⟶ B)
    (z : groupCohomology A 2) :
    (Rep.fromGroupCohomology B 2).hom ((groupCohomology.functor ℤ G 2).map f z) =
      (tateCohomologyFunctor 2).map f ((Rep.fromGroupCohomology A 2).hom z) := by
  show (Rep.fromGroupCohomology B (1 + 1)).hom _ =
    (tateCohomologyFunctor (((1 + 1 : ℕ)) : ℤ)).map f ((Rep.fromGroupCohomology A (1 + 1)).hom z)
  rw [Rep.fromGroupCohomology_succ, Rep.fromGroupCohomology_succ]
  have := (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) (1 + 1)).inv.naturality f
  exact (ConcreteCategory.congr_hom this z)

/-- Comparison of `CupProductFamily` cups with Tau Ceti's Tate cup in bidegree `(r, 2)`. -/
theorem fromGroupCohomology_cup {G : Type} [Group G] [Fintype G] (c : CupProductFamily G)
    (C : Rep ℤ G) (y : groupCohomology C 2) :
    ∀ (r : ℕ) (M : Rep ℤ G) (x : groupCohomology M r),
      (Rep.fromGroupCohomology (M ⊗ C) (r + 2)).hom (c.cup M C r 2 (r + 2) rfl x y) =
        TauCeti.TateCohomology.cup M C (r : ℤ) ((2 : ℕ) : ℤ) ((r + 2 : ℕ) : ℤ) (by push_cast; ring)
          ((Rep.fromGroupCohomology M r).hom x) ((Rep.fromGroupCohomology C 2).hom y) := by
  intro r
  induction r with
  | zero =>
    intro M x
    obtain ⟨m, rfl⟩ : ∃ m, x = (groupCohomology.H0Iso M).inv m :=
      ⟨(groupCohomology.H0Iso M).hom x, by simp⟩
    have h1 := cup_zero_left c M m 2 C y
    have h2 : (Rep.fromGroupCohomology M 0).hom ((groupCohomology.H0Iso M).inv m) =
        TauCeti.TateCohomology.H0π M m := by
      rw [Rep.fromGroupCohomology_zero]
      simp
    have h3 := DFunLike.congr_fun (DFunLike.congr_fun
      (TauCeti.TateCohomology.cup_zero_left M C 2 (by norm_num))
      (TauCeti.TateCohomology.H0π M m)) ((Rep.fromGroupCohomology C 2).hom y)
    have h4 : tensorLeftOf m C = Rep.tensorInvariant C m ≫ (β_ C M).hom := by
      refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun n => ?_))
      rfl
    show (Rep.fromGroupCohomology (M ⊗ C) 2).hom
      (c.cup M C 0 2 2 (zero_add 2) ((groupCohomology.H0Iso M).inv m) y) = _
    rw [h1, fromGroupCohomology_two_natural, h2, h4]
    exact (h3.trans (TauCeti.TateCohomology.cup0H_H0π 2 m _)).symm
  | succ r ih =>
    intro M x
    obtain ⟨x', rfl⟩ := delta_surjective M r x
    have hd := c.delta_left (seq15 M) (seq15_shortExact M) C (seq15_tensorRight C M) r 2 (r + 2)
      rfl x' y
    have hc := ConcreteCategory.congr_hom
      (TauCeti.TateCohomology.δ_comp_fromGroupCohomology (seq15_tensorRight C M) (r + 2))
      (c.cup (seq15 M).X₃ C r 2 (r + 2) rfl x' y)
    have hc' := ConcreteCategory.congr_hom
      (TauCeti.TateCohomology.δ_comp_fromGroupCohomology (seq15_shortExact M) r) x'
    have hT := TauCeti.TateCohomology.δ_cup_of_leftInverse (seq15_shortExact M)
      (r := indRetraction M) (indRetraction_toIndG M) C
      (p := (r : ℤ)) (q := ((2 : ℕ) : ℤ)) (n := ((r + 2 : ℕ) : ℤ)) (by push_cast; ring)
      ((Rep.fromGroupCohomology (seq15 M).X₃ r).hom x') ((Rep.fromGroupCohomology C 2).hom y)
    have ih' := ih (seq15 M).X₃ x'
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hc hc'
    refine ((congrArg _ hd).trans hc).trans ?_
    refine (congrArg _ ih').trans (hT.trans ?_)
    exact congrArg (fun z => (TauCeti.TateCohomology.cup M C ((r : ℤ) + 1) ((2 : ℕ) : ℤ)
      ((r + 1 + 2 : ℕ) : ℤ) (by push_cast; ring) z) ((Rep.fromGroupCohomology C 2).hom y)) hc'.symm

/-- Naturality of the comparison `fromGroupCohomology` in every positive degree. -/
theorem fromGroupCohomology_succ_natural {G : Type} [Group G] [Fintype G] {A B : Rep ℤ G}
    (f : A ⟶ B) (n : ℕ) (z : groupCohomology A (n + 1)) :
    (Rep.fromGroupCohomology B (n + 1)).hom ((groupCohomology.functor ℤ G (n + 1)).map f z) =
      (tateCohomologyFunctor ((n + 1 : ℕ) : ℤ)).map f ((Rep.fromGroupCohomology A (n + 1)).hom z) := by
  rw [Rep.fromGroupCohomology_succ, Rep.fromGroupCohomology_succ]
  have := (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) (n + 1)).inv.naturality f
  exact (ConcreteCategory.congr_hom this z)

/-- **Remark 3.13, proved** (Milne, *CFT*, II, Remark 3.13, p. 85): under Tate's hypotheses, with $\gamma$ a
generator of $H^2(G, C)$, cup product with $\gamma$ (followed by $\mathbb Z \otimes C \cong C$) is a bijection
$H^r(G, \mathbb Z) \to H^{r+2}(G, C)$ for $r \ge 1$ and every cup-product family. From Tau Ceti's Tate theorem via
`fromGroupCohomology_cup`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 3.13, p. 85"]
theorem remark3_13 : Remark3_13 := by
  refine ⟨fun G _ _ C hC γ hγ c r hr => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  let e2 : tateCohomology C ((2 : ℕ) : ℤ) ≅ groupCohomology C 2 :=
    (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 2).app C
  let u : tateCohomology C 2 := (Rep.fromGroupCohomology C 2).hom γ
  have hu : u = e2.inv.hom γ := by
    change (Rep.fromGroupCohomology C (1 + 1)).hom γ = _
    rw [Rep.fromGroupCohomology_succ]
  have hgen : ∀ y : tateCohomology C 2, ∃ m : ℤ, m • u = y := by
    intro y
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 (hγ (e2.hom.hom y))
    refine ⟨m, ?_⟩
    have : e2.inv.hom (e2.hom.hom y) = y := by
      rw [← ModuleCat.comp_apply, Iso.hom_inv_id]; rfl
    rw [hu, ← this, ← hm, map_zsmul]
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
  have hb := TauCeti.TateCohomology.cup_bijective_of_forall_isPGroup C u hgen hcardG h1 hcard
    ((n + 1 : ℕ) : ℤ) ((n + 1 + 2 : ℕ) : ℤ) (by push_cast; ring)
  let F : groupCohomology (trivial ℤ G ℤ) (n + 1) → groupCohomology C (n + 1 + 2) := fun x =>
    (groupCohomology.functor ℤ G (n + 1 + 2)).map (λ_ C).hom
      (c.cup (trivial ℤ G ℤ) C (n + 1) 2 (n + 1 + 2) rfl x γ)
  have hcomp : (fun x => (Rep.fromGroupCohomology C (n + 1 + 2)).hom (F x)) =
      ((tateCohomologyFunctor ((n + 1 + 2 : ℕ) : ℤ)).map (λ_ C).hom) ∘
        (fun t => TauCeti.TateCohomology.cup (trivial ℤ G ℤ) C ((n + 1 : ℕ) : ℤ) 2
          ((n + 1 + 2 : ℕ) : ℤ) (by push_cast; ring) t u) ∘
        (Rep.fromGroupCohomology (trivial ℤ G ℤ) (n + 1)).hom := by
    funext x
    change (Rep.fromGroupCohomology C (n + 2 + 1)).hom
      ((groupCohomology.functor ℤ G (n + 2 + 1)).map (λ_ C).hom _) = _
    rw [fromGroupCohomology_succ_natural]
    exact congrArg ((tateCohomologyFunctor ((n + 1 + 2 : ℕ) : ℤ)).map (λ_ C).hom)
      (fromGroupCohomology_cup c C γ (n + 1) (trivial ℤ G ℤ) x)
  have hg : Function.Bijective (Rep.fromGroupCohomology C (n + 1 + 2)).hom := by
    change Function.Bijective (Rep.fromGroupCohomology C (n + 2 + 1)).hom
    rw [Rep.fromGroupCohomology_succ]
    exact ((TateCohomology.isoGroupCohomology (R := ℤ) (G := G) (n + 2 + 1)).app
      C).symm.toLinearEquiv.bijective
  have hD : Function.Bijective (Rep.fromGroupCohomology (trivial ℤ G ℤ) (n + 1)).hom := by
    rw [Rep.fromGroupCohomology_succ]
    exact ((TateCohomology.isoGroupCohomology (R := ℤ) (G := G) (n + 1)).app
      (trivial ℤ G ℤ)).symm.toLinearEquiv.bijective
  have hlam : Function.Bijective ((tateCohomologyFunctor ((n + 1 + 2 : ℕ) : ℤ)).map (λ_ C).hom) :=
    ConcreteCategory.bijective_of_isIso _
  refine (Function.Bijective.of_comp_iff' hg F).1 ?_
  change Function.Bijective (fun x => (Rep.fromGroupCohomology C (n + 1 + 2)).hom (F x))
  rw [hcomp]
  exact hlam.comp (hb.comp hD)

end NumberFieldKB.MilneCFT
