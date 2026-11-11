import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Topology.Category.Profinite.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Corestriction

/-!
# Milne, *Class Field Theory*, Chapter II §4: the cohomology of profinite groups

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

A profinite group is a compact, totally disconnected topological group (Mathlib's `ProfiniteGrp`; here
the classes `CompactSpace`, `TotallyDisconnectedSpace`, `IsTopologicalGroup`). Milne's continuous cohomology of a
discrete $G$-module is computed by continuous cochains; Mathlib's `continuousCohomology` (homogeneous continuous
cochains of a topological representation `TopRep ℤ G`) is used for it, applied to a module with the discrete
topology. Mathlib's continuous cohomology has no inflation maps yet, so Proposition 4.2 is stated as an isomorphism
with the direct limit of the $H^r(G/H, M^H)$ along inflation (a named statement); Corollary 4.3 is proved from it.
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology

section Discrete

variable {G : Type} [Group G] [TopologicalSpace G]

/-- A **discrete $G$-module** (p. 87): a $G$-module $M$ such that the stabilizer in $G$ of every element is open.
Equivalent conditions are in `isDiscreteModule_tfae`. -/
@[kb "milne2020cft" "v4.03, Ch. II, §4, definition of a discrete G-module, p. 87"]
def IsDiscreteModule (M : Rep ℤ G) : Prop :=
  ∀ m : M, IsOpen {g : G | M.ρ g m = m}

/-- The stabilizer of an element of a $G$-module, as a subgroup. -/
def stabSubgroup (M : Rep ℤ G) (m : M) : Subgroup G where
  carrier := {g | M.ρ g m = m}
  mul_mem' := fun {a b} ha hb => by
    show M.ρ (a * b) m = m
    rw [map_mul]; exact (congrArg (M.ρ a) hb).trans ha
  one_mem' := by show M.ρ 1 m = m; simp
  inv_mem' := fun {a} ha => by
    show M.ρ a⁻¹ m = m
    have : M.ρ a⁻¹ (M.ρ a m) = M.ρ a⁻¹ m := congrArg _ ha
    rw [← this, ← Module.End.mul_apply, ← map_mul]; simp

/-- Milne (p. 87): for a $G$-module $M$ the following are equivalent: (i) the action map $G \times M \to M$ is
continuous for the discrete topology on $M$; (ii) $M = \bigcup_H M^H$, $H$ running through the open subgroups of
$G$; (iii) the stabilizer of every element of $M$ is open. -/
@[kb "milne2020cft" "v4.03, Ch. II, §4, equivalent conditions for a discrete G-module, p. 87"]
theorem isDiscreteModule_tfae [IsTopologicalGroup G] (M : Rep ℤ G) :
    List.TFAE
      [@Continuous (G × M) M (@instTopologicalSpaceProd G M _ ⊥) ⊥ (fun p => M.ρ p.1 p.2),
        ∀ m : M, ∃ H : OpenSubgroup G, ∀ h ∈ H, M.ρ h m = m,
        IsDiscreteModule M] := by
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have key : ∀ m : M, Continuous (fun g : G => M.ρ g m) → IsOpen {g : G | M.ρ g m = m} := by
    intro m hc
    exact isOpen_discrete ({m} : Set M) |>.preimage hc
  tfae_have 1 → 3 := by
    intro h m
    apply key
    exact h.comp (continuous_id.prodMk continuous_const)
  tfae_have 2 → 3 := by
    intro h m
    obtain ⟨H, hH⟩ := h m
    have hHS : (H : Subgroup G) ≤ stabSubgroup M m := fun g hg => hH g hg
    exact Subgroup.isOpen_mono hHS H.isOpen
  tfae_have 3 → 2 := by
    intro h m
    exact ⟨⟨stabSubgroup M m, h m⟩, fun g hg => hg⟩
  tfae_have 3 → 1 := by
    intro h
    rw [continuous_def]
    intro T _
    rw [isOpen_iff_mem_nhds]
    rintro ⟨g, m⟩ hgm
    have hU : IsOpen ((fun g' : G => g⁻¹ * g') ⁻¹' {s : G | M.ρ s m = m}) :=
      (h m).preimage (continuous_const.mul continuous_id)
    refine Filter.mem_of_superset ((hU.prod (isOpen_discrete ({m} : Set M))).mem_nhds
      ⟨show M.ρ (g⁻¹ * g) m = m by simp, rfl⟩) ?_
    rintro ⟨g', m'⟩ ⟨h1, h2⟩
    have h2' : m' = m := h2
    subst h2'
    have h1' : M.ρ (g⁻¹ * g') m' = m' := h1
    show M.ρ g' m' ∈ T
    have : M.ρ g' m' = M.ρ g m' := by
      calc M.ρ g' m' = M.ρ (g * (g⁻¹ * g')) m' := by rw [mul_inv_cancel_left]
        _ = M.ρ g m' := by rw [map_mul, Module.End.mul_apply, h1']
    rw [this]; exact hgm
  tfae_finish

end Discrete

section Incl

variable {k Γ : Type} [CommRing k] [Group Γ]

/-- The inclusion $M^U \hookrightarrow M^V$ for normal subgroups $V \le U$, as a morphism of
$\Gamma/V$-representations from the restriction (along $\Gamma/V \to \Gamma/U$) of $M^U$ to $M^V$. -/
noncomputable def inclMorGen (M : Rep k Γ) {U V : Subgroup Γ} [U.Normal] [V.Normal] (h : V ≤ U) :
    res (QuotientGroup.map V U (MonoidHom.id Γ) h) (quotientToInvariants M U) ⟶
      quotientToInvariants M V :=
  Rep.ofHom (k := k)
    (ρ := (M.ρ.quotientToInvariants U).comp (QuotientGroup.map V U (MonoidHom.id Γ) h))
    (σ := M.ρ.quotientToInvariants V)
    ⟨Submodule.inclusion (fun x hx g => hx ⟨g.1, h g.2⟩), fun g => by
      refine QuotientGroup.induction_on g fun g => ?_
      apply LinearMap.ext
      intro x
      rfl⟩

lemma inflGen_self (M : Rep k Γ) (U : Subgroup Γ) [U.Normal] (r : ℕ) :
    groupCohomology.map (QuotientGroup.map U U (MonoidHom.id Γ) le_rfl)
      (inclMorGen M (le_refl U)) r = 𝟙 _ := by
  have hf : QuotientGroup.map U U (MonoidHom.id Γ) le_rfl = MonoidHom.id (Γ ⧸ U) :=
    MonoidHom.ext fun g => QuotientGroup.induction_on g fun _ => rfl
  rw [← groupCohomology.map_id (B := quotientToInvariants M U) r]
  exact groupCohomology.map_congr hf (LinearMap.ext fun _ => rfl) r

lemma inflGen_comp (M : Rep k Γ) {U V W : Subgroup Γ} [U.Normal] [V.Normal] [W.Normal]
    (hVU : V ≤ U) (hWV : W ≤ V) (r : ℕ) :
    groupCohomology.map (QuotientGroup.map W U (MonoidHom.id Γ) (hWV.trans hVU))
      (inclMorGen M (hWV.trans hVU)) r =
    groupCohomology.map (QuotientGroup.map V U (MonoidHom.id Γ) hVU) (inclMorGen M hVU) r ≫
      groupCohomology.map (QuotientGroup.map W V (MonoidHom.id Γ) hWV) (inclMorGen M hWV) r := by
  rw [← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ r
  · exact MonoidHom.ext fun g => QuotientGroup.induction_on g fun _ => rfl
  · exact LinearMap.ext fun _ => rfl

end Incl

section Profinite

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The inflation map $H^r(G/U, M^U) \to H^r(G/V, M^V)$ for open normal subgroups $V \subseteq U$ (p. 87–88),
defined by the compatible pair ($G/V \to G/U$, $M^U \hookrightarrow M^V$). -/
@[kb "milne2020cft" "v4.03, Ch. II, §4, inflation between finite quotients, p. 87"]
noncomputable def inflStep (M : Rep ℤ G) {U V : OpenNormalSubgroup G} (h : V ≤ U) (r : ℕ) :
    groupCohomology (quotientToInvariants M (U : Subgroup G)) r ⟶
      groupCohomology (quotientToInvariants M (V : Subgroup G)) r :=
  groupCohomology.map (QuotientGroup.map (V : Subgroup G) (U : Subgroup G) (MonoidHom.id G) h)
    (inclMorGen M h) r

/-- The direct system $(H^r(G/H, M^H))_H$, $H$ running through the open normal subgroups of $G$ ordered by reverse
inclusion, with the inflation maps. -/
theorem inflStep_directedSystem (M : Rep ℤ G) (r : ℕ) :
    DirectedSystem (fun U : (OpenNormalSubgroup G)ᵒᵈ =>
        groupCohomology (quotientToInvariants M ((OrderDual.ofDual U : OpenNormalSubgroup G) : Subgroup G)) r)
      (fun _ _ h => ⇑(inflStep M h r).hom) := by
  constructor
  · intro i x
    have : inflStep M (le_refl (OrderDual.ofDual i)) r = 𝟙 _ :=
      inflGen_self M _ r
    show (inflStep M (le_refl (OrderDual.ofDual i)) r).hom x = x
    rw [this]; rfl
  · intro i j k hij hjk x
    have := inflGen_comp M (U := ((OrderDual.ofDual k : OpenNormalSubgroup G) : Subgroup G))
      (V := ((OrderDual.ofDual j : OpenNormalSubgroup G) : Subgroup G))
      (W := ((OrderDual.ofDual i : OpenNormalSubgroup G) : Subgroup G)) hij hjk r
    exact (congrArg (fun φ => φ.hom x) this).symm

open Classical in
/-- The direct limit $\varinjlim_H H^r(G/H, M^H)$ over the open normal subgroups $H$ (p. 88). -/
noncomputable def inflLimit (M : Rep ℤ G) (r : ℕ) : Type :=
  AddCommGroup.DirectLimit (fun U : (OpenNormalSubgroup G)ᵒᵈ =>
      groupCohomology (quotientToInvariants M ((OrderDual.ofDual U : OpenNormalSubgroup G) : Subgroup G)) r)
    (fun _ _ h => (inflStep M h r).hom.toAddMonoidHom)

open Classical in
noncomputable instance (M : Rep ℤ G) (r : ℕ) : AddCommGroup (inflLimit M r) :=
  AddCommGroup.DirectLimit.addCommGroup _ _

/-- The $G$-module underlying a topological representation. -/
noncomputable abbrev TopRep.toRep (A : TopRep ℤ G) : Rep ℤ G :=
  @Rep.of ℤ G _ _ A.V _ A.hV2 (@ContRepresentation.toRepresentation ℤ G A.V _ _ _ _ _ A.hV2 A.ρ)

/-- **Proposition 4.2** (p. 88), as a named statement. Let $G$ be a profinite group and $M$ a discrete $G$-module
(a topological representation with the discrete topology whose stabilizers are open). Then
$\varinjlim_H H^r(G/H, M^H) \simeq H^r_{cts}(G, M)$, the limit over the open normal subgroups $H$ along inflation.
Milne's statement says that the inflation maps realize the isomorphism; Mathlib's `continuousCohomology` has no
inflation maps, so the statement asserts an isomorphism of abelian groups. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 4.2, p. 88"]
structure Prop4_2 : Prop where
  iso : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (A : TopRep ℤ G) [DiscreteTopology A],
    IsDiscreteModule (TopRep.toRep A) →
    ∀ r : ℕ, Nonempty (continuousCohomology r A ≃+ inflLimit (TopRep.toRep A) r)

lemma nsmul_zero_of_hom {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B) (n : ℕ)
    (y : A) (h : n • y = 0) : n • φ y = 0 := by
  rw [← map_nsmul, h, map_zero]

/-- **Corollary 4.3** (p. 88). For a profinite group $G$ and a discrete $G$-module $M$, $H^r(G, M)$ is torsion
for all $r > 0$. Proved from Proposition 4.2 (named statement) and Corollary 1.31 for the finite quotients
$G/H$. The module lives in `Type` (universe 0), as in `Prop4_2` and throughout the library. -/
@[kb "milne2020cft" "v4.03, Ch. II, Cor. 4.3, p. 88"]
theorem cor_4_3 (h42 : Prop4_2) [CompactSpace G] [TotallyDisconnectedSpace G]
    (A : TopRep.{0, 0, 0} ℤ G)
    [DiscreteTopology A] (hA : IsDiscreteModule (TopRep.toRep A)) (r : ℕ) (hr : 0 < r)
    (x : continuousCohomology r A) : ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  classical
  obtain ⟨e⟩ := h42.iso G A hA r
  haveI : Nonempty (OpenNormalSubgroup G)ᵒᵈ :=
    ⟨OrderDual.toDual ⟨⟨⊤, isOpen_univ⟩, Subgroup.normal_top⟩⟩
  have key : ∀ z : inflLimit (TopRep.toRep A) r, ∃ n : ℕ, 0 < n ∧ n • z = 0 := by
    intro z
    refine AddCommGroup.DirectLimit.induction_on z (fun i y => ?_)
    have hfin : Finite (G ⧸ ((OrderDual.ofDual i : OpenNormalSubgroup G) : Subgroup G)) :=
      inferInstanceAs (Finite (G ⧸ (OrderDual.ofDual i : OpenNormalSubgroup G).toOpenSubgroup.toSubgroup))
    refine ⟨Nat.card (G ⧸ ((OrderDual.ofDual i : OpenNormalSubgroup G) : Subgroup G)),
      Nat.card_pos, ?_⟩
    have h0 := cor_1_31 _ r hr y
    rw [natCast_zsmul] at h0
    exact nsmul_zero_of_hom _ _ _ h0
  obtain ⟨n, hn, h⟩ := key (e x)
  refine ⟨n, hn, e.injective ?_⟩
  rw [map_nsmul, h, map_zero]

end Profinite

end NumberFieldKB.MilneCFT
