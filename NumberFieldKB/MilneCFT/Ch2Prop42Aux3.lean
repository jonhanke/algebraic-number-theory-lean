import Mathlib
import NumberFieldKB.MilneCFT.Ch2Prop42Aux2
import NumberFieldKB.MilneCFT.Ch2Profinite

/-!
# Proposition 4.2, auxiliary file 3: from cochains of a finite quotient to homogeneous cochains

For an open normal subgroup `U` of a topological group `G` and a topological representation `A`,
every inhomogeneous cochain of `G/U` with values in `A^U` gives a homogeneous continuous cochain of
`G` with values in `A`.  This is an injective additive map commuting with the differentials and
compatible with the inflation maps.
-/

open CategoryTheory _root_.TopRep groupCohomology

namespace NumberFieldKB.MilneCFT.Prop42

section Generic

variable {k Γ : Type} [CommRing k] [Group Γ]

/-- The inclusion of the invariants `M^S` into `M`, as a morphism of representations of `Γ`
(restricted along the quotient map `Γ → Γ/S`). -/
noncomputable def inclQ (M : Rep k Γ) (S : Subgroup Γ) [S.Normal] :
    Rep.res (QuotientGroup.mk' S) (Rep.quotientToInvariants M S) ⟶ M :=
  Rep.ofHom <| M.ρ.quotientToInvariants_lift S

end Generic

section Theta

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : TopRep ℤ G)
  (U : OpenNormalSubgroup G)

/-- Pull back an inhomogeneous cochain of `G/U` with values in `A^U` to `G` with values in `A`. -/
noncomputable def pull (n : ℕ) :
    (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A) (U : Subgroup G))).X n ⟶
      (inhomogeneousCochains (TopRep.toRep A)).X n :=
  (cochainsMap (QuotientGroup.mk' (U : Subgroup G))
    (inclQ (TopRep.toRep A) (U : Subgroup G))).f n

theorem pull_apply (n : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) (g : Fin n → G) :
    (pull A U n).hom f g = ((f (fun i => (g i : G ⧸ (U : Subgroup G)))).1 : A.V) := rfl

/-- The homogeneous cochain, as a function of tuples, attached to an inhomogeneous cochain of the
quotient. -/
noncomputable def hom0 (n : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) : (Fin (n + 1) → G) → A.V :=
  homG (TopRep.toRep A) ((pull A U n).hom f)

theorem hom0_apply (n : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) (x : Fin (n + 1) → G) :
    hom0 A U n f x = (TopRep.toRep A).ρ (x 0)
      ((f (fun i => (QuotientGroup.mk (diffs x i) : G ⧸ (U : Subgroup G)))).1 : A.V) := rfl

theorem per_hom0 (n : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) : Per (U : Subgroup G) (hom0 A U n f) := by
  intro x u hu
  have h1 : (fun i : Fin n => ((diffs (fun i => x i * u i) i : G) : G ⧸ (U : Subgroup G))) =
      fun i => ((diffs x i : G) : G ⧸ (U : Subgroup G)) := by
    funext i
    have h0 : ((u (Fin.castSucc i) : G) : G ⧸ (U : Subgroup G)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hu _)
    have h2 : ((u i.succ : G) : G ⧸ (U : Subgroup G)) = 1 := (QuotientGroup.eq_one_iff _).2 (hu _)
    simp [diffs, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h0, h2]
  rw [hom0_apply, hom0_apply, h1]
  have h3 : (TopRep.toRep A).ρ (u 0) ((f (fun i => (QuotientGroup.mk (diffs x i) : G ⧸ (U : Subgroup G)))).1 : A.V) =
      ((f (fun i => (QuotientGroup.mk (diffs x i) : G ⧸ (U : Subgroup G)))).1 : A.V) :=
    (f (fun i => (QuotientGroup.mk (diffs x i) : G ⧸ (U : Subgroup G)))).2 ⟨u 0, hu 0⟩
  show (TopRep.toRep A).ρ (x 0 * u 0) _ = _
  rw [Rep.ρ_mul, LinearMap.comp_apply, h3]

theorem hom0_smul (n : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) (g : G) (x : Fin (n + 1) → G) :
    hom0 A U n f (fun i => g * x i) = (TopRep.toRep A).ρ g (hom0 A U n f x) := by
  have : diffs (fun i => g * x i) = diffs x := by
    funext i; simp [diffs, mul_assoc]
  rw [hom0_apply, hom0_apply, this]
  show (TopRep.toRep A).ρ (g * x 0) _ = _
  rw [Rep.ρ_mul, LinearMap.comp_apply]

variable {A U} in
/-- The element of the coinduced resolution that reads as `hom0 f`. -/
noncomputable def liftRes (n : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) : (resolutionX A (n + 1)).V :=
  Classical.choose (exists_ev_eq A U.toOpenSubgroup (n + 1) (hom0 A U n f) (per_hom0 A U n f))

theorem ev_liftRes (n : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) : ev A (n + 1) (liftRes n f) = hom0 A U n f :=
  Classical.choose_spec
    (exists_ev_eq A U.toOpenSubgroup (n + 1) (hom0 A U n f) (per_hom0 A U n f))

theorem liftRes_invariant (n : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) (g : G) :
    (resolutionX A (n + 1)).ρ g (liftRes n f) = liftRes n f := by
  apply ev_injective A (n + 1)
  funext x
  rw [ev_ρ, ev_liftRes]
  have := hom0_smul A U n f g⁻¹ x
  show (TopRep.toRep A).ρ g (hom0 A U n f (fun i => g⁻¹ * x i)) = _
  rw [this, ← LinearMap.comp_apply, ← Rep.ρ_mul]
  simp

theorem hom0_add (n : ℕ)
    (f f' : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) : hom0 A U n (f + f') = hom0 A U n f + hom0 A U n f' := by
  funext x
  rw [Pi.add_apply, hom0_apply, hom0_apply, hom0_apply]
  rw [← map_add]
  rfl

theorem liftRes_add (n : ℕ)
    (f f' : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) : liftRes n (f + f') = liftRes n f + liftRes n f' := by
  apply ev_injective A (n + 1)
  rw [ev_add, ev_liftRes, ev_liftRes, ev_liftRes, hom0_add]

theorem liftRes_zero (n : ℕ) :
    liftRes (A := A) (U := U) n 0 = 0 := by
  apply ev_injective A (n + 1)
  rw [ev_zero, ev_liftRes]
  funext x
  rw [hom0_apply]
  exact map_zero _

/-- The additive map from inhomogeneous cochains of `G/U` with values in `A^U` to homogeneous
continuous cochains of `G` with values in `A`. -/
noncomputable def theta (n : ℕ) :
    (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n →+ (homogeneousCochains A).X n where
  toFun f := ⟨liftRes n f, liftRes_invariant A U n f⟩
  map_zero' := Subtype.ext (liftRes_zero A U n)
  map_add' f f' := Subtype.ext (liftRes_add A U n f f')

theorem theta_val (n : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) : (theta A U n f).val = liftRes n f := rfl

theorem pull_d (n : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) :
    (pull A U (n + 1)).hom ((inhomogeneousCochains.d _ n).hom f) =
      (inhomogeneousCochains.d (TopRep.toRep A) n).hom ((pull A U n).hom f) := by
  have := (cochainsMap (QuotientGroup.mk' (U : Subgroup G))
    (inclQ (TopRep.toRep A) (U : Subgroup G))).comm n (n + 1)
  rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def] at this
  have h2 := congrArg (fun φ => φ.hom f) this
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2.symm

/-- The map `theta` commutes with the differentials. -/
theorem theta_d (n : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) :
    theta A U (n + 1) (((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).d n (n + 1)).hom f) =
      ((homogeneousCochains A).d n (n + 1)).hom (theta A U n f) := by
  apply Subtype.ext
  rw [homogeneousCochains.d_apply]
  apply ev_injective A (n + 2)
  funext x
  show ev A (n + 2) (liftRes (n + 1) _) x = ev A (n + 2) ((d A (n + 1)).hom (liftRes n f)) x
  rw [ev_d, ev_liftRes, inhomogeneousCochains.d_def]
  simp only [ev_liftRes]
  unfold hom0
  rw [pull_d, homG_d]

theorem hom0_partialProd (n : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) (g : Fin n → G) :
    hom0 A U n f (Fin.partialProd g) =
      ((f (fun i => (QuotientGroup.mk (g i) : G ⧸ (U : Subgroup G)))).1 : A.V) := by
  rw [hom0_apply]
  have h1 : (fun i : Fin n => (QuotientGroup.mk (diffs (Fin.partialProd g) i) :
      G ⧸ (U : Subgroup G))) = fun i => QuotientGroup.mk (g i) := by
    funext i
    simp only [diffs, Fin.partialProd_right_inv]
  rw [h1]
  show (TopRep.toRep A).ρ (Fin.partialProd g 0) _ = _
  rw [Fin.partialProd_zero, map_one]
  rfl

theorem theta_injective (n : ℕ) : Function.Injective (theta A U n) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h1 : liftRes n f = 0 := congrArg Subtype.val hf
  have h2 : hom0 A U n f = 0 := by
    rw [← ev_liftRes, h1, ev_zero]
  funext q
  have h3 := congrFun h2 (Fin.partialProd (fun i => Quotient.out (q i)))
  rw [hom0_partialProd] at h3
  apply Subtype.ext
  have h4 : (fun i => (QuotientGroup.mk (Quotient.out (q i)) : G ⧸ (U : Subgroup G))) = q := by
    funext i
    exact QuotientGroup.out_eq' (q i)
  rw [h4] at h3
  exact h3

theorem theta_infl {V : OpenNormalSubgroup G} (h : V ≤ U) (n : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n) :
    theta A V n (((cochainsMap (QuotientGroup.map (V : Subgroup G) (U : Subgroup G)
      (MonoidHom.id G) h) (inclMorGen (TopRep.toRep A) h)).f n).hom f) = theta A U n f := by
  apply Subtype.ext
  apply ev_injective A (n + 1)
  rw [theta_val, theta_val, ev_liftRes, ev_liftRes]
  funext x
  rw [hom0_apply, hom0_apply]
  rfl

end Theta

section Surjective

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : TopRep ℤ G)

theorem ev_smul_of_invariant (k : ℕ) (F : (resolutionX A k).V)
    (hF : ∀ g : G, (resolutionX A k).ρ g F = F) (g : G) (x : Fin k → G) :
    ev A k F (fun i => g * x i) = A.ρ g (ev A k F x) := by
  have := ev_ρ A k g F (fun i => g * x i)
  rw [hF g] at this
  rw [this]
  simp

theorem partialProd_inv_mul_mem (S : Subgroup G) [S.Normal] {n : ℕ} (g g' : Fin n → G)
    (h : ∀ i, (g' i)⁻¹ * g i ∈ S) :
    ∀ i : Fin (n + 1), (Fin.partialProd g' i)⁻¹ * Fin.partialProd g i ∈ S := by
  intro i
  refine Fin.induction ?_ (fun i ih => ?_) i
  · simp [S.one_mem]
  · rw [Fin.partialProd_succ, Fin.partialProd_succ]
    have h1 : (Fin.partialProd g' (Fin.castSucc i) * g' i)⁻¹ *
        (Fin.partialProd g (Fin.castSucc i) * g i) =
        ((g' i)⁻¹ * ((Fin.partialProd g' (Fin.castSucc i))⁻¹ * Fin.partialProd g (Fin.castSucc i)) *
          g' i) * ((g' i)⁻¹ * g i) := by
      group
    rw [h1]
    refine S.mul_mem ?_ (h i)
    have := Subgroup.Normal.conj_mem ‹S.Normal› _ ih ((g' i)⁻¹)
    simpa using this

variable [CompactSpace G] [TotallyDisconnectedSpace G] [DiscreteTopology A.V]

theorem theta_surjective (n : ℕ) (F : (homogeneousCochains A).X n) :
    ∃ (U : OpenNormalSubgroup G) (f : (inhomogeneousCochains (Rep.quotientToInvariants
      (TopRep.toRep A) (U : Subgroup G))).X n), theta A U n f = F := by
  have hFinv : ∀ g : G, (resolutionX A (n + 1)).ρ g F.val = F.val := F.2
  obtain ⟨U, hU⟩ := exists_per A (n + 1) F.val
  have hinv : ∀ (x : Fin (n + 1) → G) (s : G), s ∈ (U : Subgroup G) →
      A.ρ s (ev A (n + 1) F.val x) = ev A (n + 1) F.val x := by
    intro x s hs
    rw [← ev_smul_of_invariant A (n + 1) F.val hFinv s x]
    have := hU x (fun i => (x i)⁻¹ * s * x i) (fun i => by
      simpa using Subgroup.Normal.conj_mem inferInstance s hs ((x i)⁻¹))
    rw [← this]
    congr 1
    funext i
    simp [mul_assoc]
  let f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X n :=
    fun q => ⟨ev A (n + 1) F.val (Fin.partialProd (fun i => Quotient.out (q i))),
      fun s => hinv _ s s.2⟩
  refine ⟨U, f, ?_⟩
  apply Subtype.ext
  apply ev_injective A (n + 1)
  rw [theta_val, ev_liftRes]
  funext x
  rw [hom0_apply]
  have hcoset := partialProd_inv_mul_mem (U : Subgroup G)
    (fun i => Quotient.out (QuotientGroup.mk (diffs x i) : G ⧸ (U : Subgroup G)))
    (diffs x) (fun i => by
      have := QuotientGroup.out_eq' (QuotientGroup.mk (diffs x i) : G ⧸ (U : Subgroup G))
      exact (QuotientGroup.eq.1 this.symm))
  have hper := hU (Fin.partialProd (diffs x))
    (fun i => (Fin.partialProd (diffs x) i)⁻¹ * Fin.partialProd (fun i =>
      Quotient.out (QuotientGroup.mk (diffs x i) : G ⧸ (U : Subgroup G))) i) hcoset
  simp only [mul_inv_cancel_left] at hper
  show (TopRep.toRep A).ρ (x 0) (ev A (n + 1) F.val _) = _
  rw [hper]
  have h2 := ev_smul_of_invariant A (n + 1) F.val hFinv (x 0) (fun i => (x 0)⁻¹ * x i)
  simp only [mul_inv_cancel_left] at h2
  have h3 : Fin.partialProd (diffs x) = fun i => (x 0)⁻¹ * x i := funext (partialProd_diffs x)
  rw [h3]
  exact h2.symm

end Surjective

end NumberFieldKB.MilneCFT.Prop42
