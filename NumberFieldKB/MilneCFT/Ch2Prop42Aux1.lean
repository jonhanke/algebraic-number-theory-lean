import Mathlib
import NumberFieldKB.MilneCFT.Ch2Profinite
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.ContCohomology.CompactDiscrete
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.ContCohomology.Resolution.Basic

/-!
# Proposition 4.2, auxiliary file 1: cochains of the coinduced resolution as functions of tuples

For a topological representation `A` of a topological group `G`, the `k`-th term of the coinduced
resolution is the iterated space of continuous maps `C(G, C(G, ..., A))`.  Reading such an element at
a tuple of points gives a function from tuples of length `k` to `A`.  This file records the formulas
for the differential and the group action in terms of these functions, and, for a compact totally
disconnected group and a discrete module, shows that every element is a function that is unchanged
when each coordinate is multiplied on the right by an element of some open normal subgroup.
-/

open CategoryTheory _root_.TopRep

namespace NumberFieldKB.MilneCFT.Prop42

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Reading an element of the `k`-th term of the coinduced resolution at a tuple of `k` points. -/
def ev (A : TopRep ℤ G) : (k : ℕ) → (resolutionX A k).V → ((Fin k → G) → A.V)
  | 0, m => fun _ => m
  | k + 1, F => fun x => ev A k ((F : C(G, (resolutionX A k).V)) (x 0)) (Fin.tail x)

theorem ev_zero_apply (A : TopRep ℤ G) (m : (resolutionX A 0).V) (x : Fin 0 → G) :
    ev A 0 m x = m := rfl

theorem ev_succ_apply (A : TopRep ℤ G) (k : ℕ) (F : (resolutionX A (k + 1)).V) (x₀ : G)
    (t : Fin k → G) :
    ev A (k + 1) F (Fin.cons x₀ t) = ev A k ((F : C(G, (resolutionX A k).V)) x₀) t := by
  simp [ev]

theorem ev_add (A : TopRep ℤ G) : ∀ (k : ℕ) (F F' : (resolutionX A k).V),
    ev A k (F + F') = ev A k F + ev A k F'
  | 0, F, F' => rfl
  | k + 1, F, F' => by
    funext x
    show ev A k ((F + F' : C(G, (resolutionX A k).V)) (x 0)) _ = _
    rw [ContinuousMap.add_apply, ev_add A k]
    rfl

theorem ev_sub (A : TopRep ℤ G) : ∀ (k : ℕ) (F F' : (resolutionX A k).V),
    ev A k (F - F') = ev A k F - ev A k F'
  | 0, F, F' => rfl
  | k + 1, F, F' => by
    funext x
    show ev A k ((F - F' : C(G, (resolutionX A k).V)) (x 0)) _ = _
    rw [ContinuousMap.sub_apply, ev_sub A k]
    rfl

theorem ev_zero (A : TopRep ℤ G) : ∀ (k : ℕ), ev A k 0 = 0
  | 0 => rfl
  | k + 1 => by
    funext x
    show ev A k ((0 : C(G, (resolutionX A k).V)) (x 0)) _ = _
    rw [ContinuousMap.zero_apply, ev_zero A k]
    rfl

theorem ev_injective (A : TopRep ℤ G) : ∀ (k : ℕ), Function.Injective (ev A k)
  | 0, F, F' , h => congrFun h default
  | k + 1, F, F', h => by
    apply ContinuousMap.ext
    intro x₀
    apply ev_injective A k
    funext t
    have := congrFun h (Fin.cons x₀ t)
    rwa [ev_succ_apply, ev_succ_apply] at this

/-- The group action on the coinduced resolution, in terms of tuples. -/
theorem ev_ρ (A : TopRep ℤ G) : ∀ (k : ℕ) (g : G) (F : (resolutionX A k).V) (x : Fin k → G),
    ev A k ((resolutionX A k).ρ g F) x = A.ρ g (ev A k F (fun i => g⁻¹ * x i))
  | 0, g, F, x => rfl
  | k + 1, g, F, x => by
    show ev A k (((resolutionX A (k + 1)).ρ g F : C(G, (resolutionX A k).V)) (x 0))
      (Fin.tail x) = _
    rw [resolutionX_succ_ρ_apply_apply, ev_ρ A k]
    rfl

theorem cons_succAbove_succ {n : ℕ} (x₀ : G) (t : Fin (n + 1) → G) (j : Fin (n + 1)) :
    (fun i : Fin (n + 1) => (Fin.cons x₀ t : Fin (n + 2) → G) ((Fin.succ j).succAbove i)) =
      Fin.cons x₀ (fun i : Fin n => t (j.succAbove i)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp [Fin.succ_succAbove_succ]

/-- **The differential of the coinduced resolution, in terms of tuples**: the usual alternating sum
over omitted coordinates. -/
theorem ev_d (A : TopRep ℤ G) : ∀ (k : ℕ) (F : (resolutionX A k).V) (x : Fin (k + 1) → G),
    ev A (k + 1) ((d A k).hom F) x =
      ∑ j : Fin (k + 1), (-1 : ℤ) ^ (j : ℕ) • ev A k F (fun i => x (j.succAbove i))
  | 0, F, x => by
    simp [d_zero, ev]
  | k + 1, F, x => by
    rw [← Fin.cons_self_tail x]
    generalize x 0 = x₀
    generalize Fin.tail x = t
    rw [ev_succ_apply, hom_d_succ_apply_apply, ev_sub, Pi.sub_apply, ev_d A k]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
      Fin.succAbove_zero, Fin.cons_succ]
    simp only [cons_succAbove_succ, ev_succ_apply, pow_succ, mul_neg, mul_one, neg_smul,
      Finset.sum_neg_distrib, sub_eq_add_neg]

/-- A function of tuples is **periodic** for a subgroup `U` when multiplying each coordinate on the right
by an element of `U` does not change its value. -/
def Per {B : Type*} (U : Subgroup G) {k : ℕ} (f : (Fin k → G) → B) : Prop :=
  ∀ (x u : Fin k → G), (∀ i, u i ∈ U) → f (fun i => x i * u i) = f x

theorem Per.mono {B : Type*} {U V : Subgroup G} (h : U ≤ V) {k : ℕ} {f : (Fin k → G) → B}
    (hf : Per V f) : Per U f :=
  fun x u hu => hf x u (fun i => h (hu i))

theorem Per.cons_right {B : Type*} {U : Subgroup G} {k : ℕ} {f : (Fin (k + 1) → G) → B}
    (hf : Per U f) (x₀ : G) : Per U (fun t : Fin k → G => f (Fin.cons x₀ t)) := by
  intro t u hu
  have := hf (Fin.cons x₀ t) (Fin.cons 1 u) (fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using U.one_mem
    · simpa using hu j)
  convert this using 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem Per.cons_left {B : Type*} {U : Subgroup G} {k : ℕ} {f : (Fin (k + 1) → G) → B}
    (hf : Per U f) (t : Fin k → G) {x₀ u₀ : G} (hu : u₀ ∈ U) :
    f (Fin.cons (x₀ * u₀) t) = f (Fin.cons x₀ t) := by
  have := hf (Fin.cons x₀ t) (Fin.cons u₀ 1) (fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hu
    · simpa using U.one_mem)
  convert this using 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Every periodic function of tuples (for an open subgroup) is the reading of an element of the
coinduced resolution. -/
theorem exists_ev_eq (A : TopRep ℤ G) (U : OpenSubgroup G) :
    ∀ (k : ℕ) (f : (Fin k → G) → A.V), Per (U : Subgroup G) f → ∃ F, ev A k F = f
  | 0, f, _ => ⟨f default, funext fun x => by rw [Subsingleton.elim x default]; rfl⟩
  | k + 1, f, hf => by
    have ih := fun x₀ : G => exists_ev_eq A U k (fun t => f (Fin.cons x₀ t)) (hf.cons_right x₀)
    choose Φ hΦ using ih
    have hΦu : ∀ (x₀ u₀ : G), u₀ ∈ (U : Subgroup G) → Φ (x₀ * u₀) = Φ x₀ := by
      intro x₀ u₀ hu
      apply ev_injective A k
      rw [hΦ, hΦ]
      funext t
      exact hf.cons_left t hu
    have hcont : Continuous Φ := by
      apply IsLocallyConstant.continuous
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x₀
      have hopen : IsOpen ((fun y : G => x₀⁻¹ * y) ⁻¹' (U : Set G)) :=
        U.isOpen.preimage (continuous_const.mul continuous_id)
      filter_upwards [hopen.mem_nhds (by simpa using U.one_mem)] with y hy
      have hy' : x₀⁻¹ * y ∈ (U : Subgroup G) := hy
      have := hΦu x₀ (x₀⁻¹ * y) hy'
      rwa [mul_inv_cancel_left] at this
    refine ⟨(⟨Φ, hcont⟩ : C(G, (resolutionX A k).V)), ?_⟩
    funext x
    rw [← Fin.cons_self_tail x, ev_succ_apply]
    exact congrFun (hΦ (x 0)) (Fin.tail x)

section Compact

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A continuous map from a compact group to a discrete space is unchanged by right translation by
the elements of some open normal subgroup. -/
theorem exists_openNormalSubgroup_right_invariant {B : Type*} [TopologicalSpace B]
    [DiscreteTopology B] (F : G → B) (hF : Continuous F) :
    ∃ U : OpenNormalSubgroup G, ∀ (x u : G), u ∈ (U : Subgroup G) → F (x * u) = F x := by
  have hA : IsOpen {p : G × G | F (p.1 * p.2) = F p.1} :=
    ((hF.comp (continuous_fst.mul continuous_snd)).prodMk (hF.comp continuous_fst)).isOpen_preimage
      {q : B × B | q.1 = q.2} (isOpen_discrete _)
  obtain ⟨u, v, hu, hv, hsu, hsv, huv⟩ := generalized_tube_lemma
    (isCompact_univ (X := G)) (isCompact_singleton (x := (1 : G))) hA fun p hp => by
      have hp2 : p.2 = 1 := hp.2
      simp [hp2]
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hv
    (hsv rfl)
  refine ⟨U, fun x u hu => ?_⟩
  exact huv (Set.mk_mem_prod (hsu (Set.mem_univ x)) (hU hu))

/-- Every element of the coinduced resolution of a discrete module over a profinite group is
periodic for some open normal subgroup. -/
theorem exists_per (A : TopRep ℤ G) [DiscreteTopology A.V] :
    ∀ (k : ℕ) (F : (resolutionX A k).V), ∃ U : OpenNormalSubgroup G,
      Per (U : Subgroup G) (ev A k F)
  | 0, F => ⟨⟨⟨⊤, isOpen_univ⟩, Subgroup.normal_top⟩, fun x u _ => rfl⟩
  | k + 1, F => by
    haveI : DiscreteTopology (resolutionX A k).V := TauCeti.discreteTopology_resolutionX A k
    haveI : Nonempty (OpenNormalSubgroup G) :=
      ⟨⟨⟨⊤, isOpen_univ⟩, Subgroup.normal_top⟩⟩
    have ih := fun v : (resolutionX A k).V => exists_per A k v
    choose Uv hUv using ih
    obtain ⟨U0, hU0⟩ := exists_openNormalSubgroup_right_invariant
      (fun x => (F : C(G, (resolutionX A k).V)) x) F.continuous
    have hfin : (Set.range (F : C(G, (resolutionX A k).V))).Finite :=
      (isCompact_range F.continuous).finite_of_discrete
    haveI : Finite (Set.range (F : C(G, (resolutionX A k).V))) := hfin.to_subtype
    obtain ⟨U1, hU1⟩ := Finite.exists_ge
      (fun v : Set.range (F : C(G, (resolutionX A k).V)) => Uv v.1)
    refine ⟨U0 ⊓ U1, fun x u hu => ?_⟩
    have h0 : u 0 ∈ (U0 : Subgroup G) := (hu 0).1
    have key : Per ((U0 ⊓ U1 : OpenNormalSubgroup G) : Subgroup G)
        (ev A k ((F : C(G, (resolutionX A k).V)) (x 0))) := by
      refine (hUv _).mono ?_
      exact (inf_le_right : U0 ⊓ U1 ≤ U1).trans (hU1 ⟨_, ⟨x 0, rfl⟩⟩)
    show ev A k ((F : C(G, (resolutionX A k).V)) (x 0 * u 0))
        (fun i => x i.succ * u i.succ) = ev A k ((F : C(G, (resolutionX A k).V)) (x 0))
        (Fin.tail x)
    rw [hU0 (x 0) (u 0) h0]
    exact key (Fin.tail x) (Fin.tail u) (fun i => hu i.succ)

end Compact

end NumberFieldKB.MilneCFT.Prop42
