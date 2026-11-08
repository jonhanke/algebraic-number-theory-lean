import NumberFieldKB.MilneCFT.Ch8.QuadraticForms

/-!
# Milne, *CFT*, VIII, Lemma 6.8 (O'Meara 58:1): chains of orthogonal bases

Proof of `Lemma6_8`, unconditionally. Work with a bilinear form `b` and *good* families `f : Fin n → V` (pairwise
orthogonal, anisotropic) spanning a fixed subspace `W`; nondegeneracy is only used at the end to see that an orthogonal
basis is good. A `Step` replaces a good family by another one spanning `W` that differs in two adjacent positions.

1. Permutations: swapping adjacent entries is a step, so (adjacent transpositions generate `Perm (Fin n)`,
   `perm_rtg`) `f ~ f ∘ σ` for every permutation `σ`.
2. Plane step (`pair_step`): if `α, β ≠ 0` and `α² Q(f z) + β² Q(f o) ≠ 0`, replace `(f z, f o)` by the orthogonal
   basis `(α f z + β f o, β Q(f o) f z - α Q(f z) f o)` of the plane they span; `scale_step` rescales one vector.
3. Move (`move`): given `y = ∑ aᵢ fᵢ ∈ W` with `b y y ≠ 0`, induct on the number of nonzero `aᵢ`. If two are nonzero,
   some pair has `α² Q + β² Q' ≠ 0` (`good_pair`: otherwise all `aᵢ² Q(fᵢ)` of the support are pairwise negatives,
   impossible for three of them as `2 ≠ 0`, and for two it makes `b y y = 0`); permute that pair to positions `0, 1`,
   do the plane step, and the support shrinks. With one nonzero coefficient, permute it to position `0` and scale.
   So `f ~ f'` with `f' 0 = y`.
4. Induction on `n` (`main`): move `g 0` into position `0` of `f`; the tails of the two families are good families
   spanning `W ∩ (g 0)^⊥` (`tail_span`), so the induction hypothesis chains them, and steps lift through
   `Fin.cons (g 0)` (`step_cons`), shifting the adjacent pair by one.
5. A reflexive-transitive chain gives the indexed chain of `Basis` (`rtg_chain`, `lemma6_8`).
-/

namespace NumberFieldKB.MilneCFT.Ch8
namespace Lemma68

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (b : V →ₗ[k] V →ₗ[k] k)

/-- A family is *good* if it is pairwise `b`-orthogonal and anisotropic. -/
def Good {n : ℕ} (f : Fin n → V) : Prop :=
  (∀ i j, i ≠ j → b (f i) (f j) = 0) ∧ ∀ i, b (f i) (f i) ≠ 0

/-- A good family spanning `W`. -/
def G (W : Submodule k V) {n : ℕ} (f : Fin n → V) : Prop :=
  Good b f ∧ Submodule.span k (Set.range f) = W

/-- The two families agree outside two adjacent positions `i, i+1`. -/
def Near {n : ℕ} (f g : Fin n → V) : Prop :=
  ∃ i : ℕ, ∀ j : Fin n, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → f j = g j

/-- One step of the chain. -/
def Step (W : Submodule k V) {n : ℕ} (f g : Fin n → V) : Prop :=
  G b W f ∧ G b W g ∧ Near f g

variable {b}

theorem G_comp {W : Submodule k V} {n : ℕ} {f : Fin n → V} (hf : G b W f) (σ : Equiv.Perm (Fin n)) :
    G b W (f ∘ σ) := by
  refine ⟨⟨fun i j hij => hf.1.1 _ _ (σ.injective.ne hij), fun i => hf.1.2 _⟩, ?_⟩
  rw [σ.surjective.range_comp]
  exact hf.2

theorem perm_rtg {W : Submodule k V} (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) :
    ∀ f : Fin (m + 1) → V, G b W f → Relation.ReflTransGen (Step b W) f (f ∘ σ) := by
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  induction hσ using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    intro f hf
    refine Relation.ReflTransGen.single ⟨hf, G_comp hf _, i, fun j hj1 hj2 => ?_⟩
    have h1 : j ≠ i.castSucc := fun h => hj1 (by rw [h]; simp)
    have h2 : j ≠ i.succ := fun h => hj2 (by rw [h]; simp)
    simp [Equiv.swap_apply_of_ne_of_ne h1 h2]
  | one => intro f _; exact Relation.ReflTransGen.refl
  | mul x y _ _ hx hy =>
    intro f hf
    exact (hx f hf).trans (hy (f ∘ x) (G_comp hf x))

theorem Good.linearIndependent {n : ℕ} {f : Fin n → V} (hf : Good b f) :
    LinearIndependent k f := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have := congrArg (fun v => b (f j) v) hc
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
  rw [Finset.sum_eq_single j] at this
  · exact (mul_eq_zero.mp this).resolve_right (hf.2 j)
  · intro i _ hij
    rw [hf.1 j i (Ne.symm hij), mul_zero]
  · simp

theorem rtg_chain {α : Type*} {R : α → α → Prop} {a c : α} (h : Relation.ReflTransGen R a c) :
    ∃ (m : ℕ) (C : ℕ → α), C 0 = a ∧ C m = c ∧ ∀ l < m, R (C l) (C (l + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun l hl => absurd hl (Nat.not_lt_zero _)⟩
  | @tail b' c' _ hbc ih =>
    obtain ⟨m, C, h0, hm, hC⟩ := ih
    refine ⟨m + 1, fun l => if l ≤ m then C l else c', by simp [h0], by simp, fun l hl => ?_⟩
    by_cases hlm : l < m
    · simp only [Nat.le_of_lt hlm, ite_true, Nat.succ_le_of_lt hlm]
      exact hC l hlm
    · have : l = m := by omega
      subst this
      simp [hm, hbc]

theorem span_eq_of {n : ℕ} {F H : Fin n → V}
    (h1 : ∀ i, H i ∈ Submodule.span k (Set.range F)) (h2 : ∀ i, F i ∈ Submodule.span k (Set.range H)) :
    Submodule.span k (Set.range H) = Submodule.span k (Set.range F) :=
  le_antisymm (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h1 i))
    (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h2 i))

theorem range_eq_insert {n : ℕ} (f : Fin (n + 1) → V) :
    Set.range f = insert (f 0) (Set.range fun i : Fin n => f i.succ) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · left; rfl
    · right; exact ⟨j, rfl⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨j.succ, rfl⟩

theorem span_cons (y : V) {n : ℕ} (t : Fin n → V) :
    Submodule.span k (Set.range (Fin.cons y t : Fin (n + 1) → V)) =
      Submodule.span k {y} ⊔ Submodule.span k (Set.range t) := by
  rw [Fin.range_cons, Submodule.span_insert]

theorem tail_span {W : Submodule k V} {n : ℕ} {f : Fin (n + 1) → V}
    (hf : G b W f) :
    Submodule.span k (Set.range fun i : Fin n => f i.succ) = W ⊓ LinearMap.ker (b (f 0)) := by
  have hT : Submodule.span k (Set.range fun i : Fin n => f i.succ) ≤ LinearMap.ker (b (f 0)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact hf.1.1 0 i.succ (Fin.succ_ne_zero i).symm
  have hsup : Submodule.span k (Set.range f) =
      Submodule.span k {f 0} ⊔ Submodule.span k (Set.range fun i : Fin n => f i.succ) := by
    rw [range_eq_insert, Submodule.span_insert]
  apply le_antisymm
  · refine le_inf ?_ hT
    rw [← hf.2]
    exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.succ, rfl⟩)
  · rintro w ⟨hwW, hwk⟩
    rw [← hf.2, hsup] at hwW
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hwW
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hp
    have hq0 : b (f 0) q = 0 := hT hq
    have hk : b (f 0) (c • f 0 + q) = 0 := hwk
    rw [map_add, map_smul, hq0, add_zero, smul_eq_mul] at hk
    have hc : c = 0 := (mul_eq_zero.mp hk).resolve_right (hf.1.2 0)
    simpa [hc] using hq

theorem G_cons (hs : ∀ x y, b x y = b y x) {W' : Submodule k V} {n : ℕ} {t : Fin n → V}
    (ht : G b W' t) {y : V} (hy : b y y ≠ 0) (hyt : ∀ i, b y (t i) = 0) :
    G b (Submodule.span k {y} ⊔ W') (Fin.cons y t : Fin (n + 1) → V) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j => simpa using hyt j
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa [hs] using hyt i
      | succ j => simpa using ht.1.1 i j (fun h => hij (by rw [h]))
  · intro i
    induction i using Fin.cases with
    | zero => simpa using hy
    | succ i => simpa using ht.1.2 i
  · rw [span_cons, ht.2]

theorem step_cons (hs : ∀ x y, b x y = b y x) {W' : Submodule k V} {n : ℕ} {y : V} (hy : b y y ≠ 0)
    (hyW : ∀ w ∈ W', b y w = 0) {t t' : Fin n → V} (h : Step b W' t t') :
    Step b (Submodule.span k {y} ⊔ W') (Fin.cons y t : Fin (n + 1) → V) (Fin.cons y t') := by
  obtain ⟨h1, h2, i, hi⟩ := h
  refine ⟨G_cons hs h1 hy fun j => hyW _ (h1.2 ▸ Submodule.subset_span ⟨j, rfl⟩),
    G_cons hs h2 hy fun j => hyW _ (h2.2 ▸ Submodule.subset_span ⟨j, rfl⟩), i + 1, ?_⟩
  intro j hj1 hj2
  induction j using Fin.cases with
  | zero => simp
  | succ j =>
    simp only [Fin.cons_succ]
    exact hi j (fun h => hj1 (by simp [h])) (fun h => hj2 (by simp [h]))

theorem scale_step (hs : ∀ x y, b x y = b y x) {W : Submodule k V} {n : ℕ} {F : Fin n → V}
    (hF : G b W F) (z : Fin n) {c : k} (hc : c ≠ 0) :
    ∃ H : Fin n → V, G b W H ∧ H z = c • F z ∧ ∀ i, i ≠ z → H i = F i := by
  refine ⟨Function.update F z (c • F z), ⟨⟨?_, ?_⟩, ?_⟩, by simp, fun i hi => by simp [hi]⟩
  · intro i j hij
    by_cases hi : i = z <;> by_cases hj : j = z
    · exact absurd (hi.trans hj.symm) hij
    · simp [Function.update_apply, hi, hj, hF.1.1 z j (Ne.symm hj)]
    · simp [Function.update_apply, hi, hj, hF.1.1 i z hi]
    · simp [Function.update_apply, hi, hj, hF.1.1 i j hij]
  · intro i
    by_cases hi : i = z
    · subst hi
      simpa [hc] using hF.1.2 i
    · simpa [Function.update_apply, hi] using hF.1.2 i
  · rw [← hF.2]
    apply span_eq_of
    · intro i
      by_cases hi : i = z
      · subst hi
        simpa using Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_range_self i))
      · simpa [Function.update_apply, hi] using Submodule.subset_span (Set.mem_range_self i)
    · intro i
      by_cases hi : i = z
      · subst hi
        have : c • F i ∈ Submodule.span k (Set.range (Function.update F i (c • F i))) := by
          simpa using Submodule.subset_span (Set.mem_range_self (f := Function.update F i (c • F i)) i)
        exact (Submodule.smul_mem_iff _ hc).1 this
      · exact Submodule.subset_span ⟨i, by simp [Function.update_apply, hi]⟩

theorem pair_step (hs : ∀ x y, b x y = b y x) {W : Submodule k V} {n : ℕ} {F : Fin n → V}
    (hF : G b W F) {z o : Fin n} (hzo : z ≠ o) {α β : k}
    (hD : α ^ 2 * b (F z) (F z) + β ^ 2 * b (F o) (F o) ≠ 0) :
    ∃ H : Fin n → V, G b W H ∧ H z = α • F z + β • F o ∧ ∀ i, i ≠ z → i ≠ o → H i = F i := by
  have hQz0 : b (F z) (F z) ≠ 0 := hF.1.2 z
  have hQo0 : b (F o) (F o) ≠ 0 := hF.1.2 o
  have hzo' : b (F z) (F o) = 0 := hF.1.1 z o hzo
  have hozo : b (F o) (F z) = 0 := hF.1.1 o z hzo.symm
  have hperp : ∀ i, i ≠ z → i ≠ o → b (F z) (F i) = 0 ∧ b (F o) (F i) = 0 ∧ b (F i) (F z) = 0 ∧
      b (F i) (F o) = 0 :=
    fun i h1 h2 => ⟨hF.1.1 _ _ (Ne.symm h1), hF.1.1 _ _ (Ne.symm h2), hF.1.1 _ _ h1, hF.1.1 _ _ h2⟩
  obtain ⟨Qz, hQz⟩ : ∃ Q, b (F z) (F z) = Q := ⟨_, rfl⟩
  obtain ⟨Qo, hQo⟩ : ∃ Q, b (F o) (F o) = Q := ⟨_, rfl⟩
  rw [hQz] at hQz0 hD
  rw [hQo] at hQo0 hD
  obtain ⟨u, hu⟩ : ∃ u, u = α • F z + β • F o := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = (β * Qo) • F z - (α * Qz) • F o := ⟨_, rfl⟩
  have huu : b u u = α ^ 2 * Qz + β ^ 2 * Qo := by
    simp only [hu, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hzo', hozo,
      hQz, hQo]
    ring
  have buv : b u v = 0 := by
    simp only [hu, hv, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hzo', hozo, hQz, hQo]
    ring
  have bvv : b v v = Qz * Qo * (α ^ 2 * Qz + β ^ 2 * Qo) := by
    simp only [hv, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hzo', hozo, hQz, hQo]
    ring
  have bvu : b v u = 0 := by rw [hs]; exact buv
  have buF : ∀ i, i ≠ z → i ≠ o → b u (F i) = 0 ∧ b (F i) u = 0 := fun i h1 h2 => by
    obtain ⟨p1, p2, p3, p4⟩ := hperp i h1 h2
    simp only [hu, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, p1, p2, p3, p4]
    simp
  have bvF : ∀ i, i ≠ z → i ≠ o → b v (F i) = 0 ∧ b (F i) v = 0 := fun i h1 h2 => by
    obtain ⟨p1, p2, p3, p4⟩ := hperp i h1 h2
    simp only [hv, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, p1, p2, p3, p4]
    simp
  classical
  obtain ⟨H, hH⟩ : ∃ H : Fin n → V, H = fun i => if i = z then u else if i = o then v else F i :=
    ⟨_, rfl⟩
  have hH_z : H z = u := by simp [hH]
  have hH_o : H o = v := by simp [hH, hzo.symm]
  have hH_i : ∀ i, i ≠ z → i ≠ o → H i = F i := by intro i h1 h2; simp [hH, h1, h2]
  have cls : ∀ i, i = z ∨ i = o ∨ (i ≠ z ∧ i ≠ o) := by intro i; tauto
  have hD' : α ^ 2 * Qz + β ^ 2 * Qo ≠ 0 := hD
  have horth : ∀ i j, i ≠ j → b (H i) (H j) = 0 := by
    intro i j hij
    rcases cls i with hi | hi | ⟨hi1, hi2⟩ <;> rcases cls j with hj | hj | ⟨hj1, hj2⟩
    · exact absurd (hi.trans hj.symm) hij
    · rw [hi, hj, hH_z, hH_o]; exact buv
    · rw [hi, hH_z, hH_i j hj1 hj2]; exact (buF j hj1 hj2).1
    · rw [hi, hj, hH_z, hH_o]; exact bvu
    · exact absurd (hi.trans hj.symm) hij
    · rw [hi, hH_o, hH_i j hj1 hj2]; exact (bvF j hj1 hj2).1
    · rw [hj, hH_z, hH_i i hi1 hi2]; exact (buF i hi1 hi2).2
    · rw [hj, hH_o, hH_i i hi1 hi2]; exact (bvF i hi1 hi2).2
    · rw [hH_i i hi1 hi2, hH_i j hj1 hj2]; exact hF.1.1 i j hij
  have hnd : ∀ i, b (H i) (H i) ≠ 0 := by
    intro i
    rcases cls i with hi | hi | ⟨hi1, hi2⟩
    · rw [hi, hH_z, huu]; exact hD'
    · rw [hi, hH_o, bvv]; exact mul_ne_zero (mul_ne_zero hQz0 hQo0) hD'
    · rw [hH_i i hi1 hi2]; exact hF.1.2 i
  have hzF : F z ∈ Submodule.span k (Set.range F) := Submodule.subset_span (Set.mem_range_self z)
  have hoF : F o ∈ Submodule.span k (Set.range F) := Submodule.subset_span (Set.mem_range_self o)
  have huH : u ∈ Submodule.span k (Set.range H) := hH_z ▸ Submodule.subset_span (Set.mem_range_self z)
  have hvH : v ∈ Submodule.span k (Set.range H) := hH_o ▸ Submodule.subset_span (Set.mem_range_self o)
  refine ⟨H, ⟨⟨horth, hnd⟩, ?_⟩, by rw [hH_z, hu], hH_i⟩
  rw [← hF.2]
  apply span_eq_of
  · intro i
    rcases cls i with hi | hi | ⟨hi1, hi2⟩
    · rw [hi, hH_z, hu]
      exact add_mem (Submodule.smul_mem _ _ hzF) (Submodule.smul_mem _ _ hoF)
    · rw [hi, hH_o, hv]
      exact sub_mem (Submodule.smul_mem _ _ hzF) (Submodule.smul_mem _ _ hoF)
    · rw [hH_i i hi1 hi2]; exact Submodule.subset_span (Set.mem_range_self i)
  · intro i
    rcases cls i with hi | hi | ⟨hi1, hi2⟩
    · rw [hi]
      have : (α ^ 2 * Qz + β ^ 2 * Qo) • F z = (α * Qz) • u + β • v := by
        rw [hu, hv]; module
      refine (Submodule.smul_mem_iff _ hD').1 ?_
      rw [this]
      exact add_mem (Submodule.smul_mem _ _ huH) (Submodule.smul_mem _ _ hvH)
    · rw [hi]
      have : (α ^ 2 * Qz + β ^ 2 * Qo) • F o = (β * Qo) • u - α • v := by
        rw [hu, hv]; module
      refine (Submodule.smul_mem_iff _ hD').1 ?_
      rw [this]
      exact sub_mem (Submodule.smul_mem _ _ huH) (Submodule.smul_mem _ _ hvH)
    · rw [← hH_i i hi1 hi2]; exact Submodule.subset_span (Set.mem_range_self i)

theorem exists_perm{N : ℕ} (z o p q : Fin N) (hzo : z ≠ o) (hpq : p ≠ q) :
    ∃ σ : Equiv.Perm (Fin N), σ z = p ∧ σ o = q := by
  have hz : z ≠ Equiv.swap z p q := fun h => hpq (by
    have := congrArg (Equiv.swap z p) h
    simpa using this)
  refine ⟨Equiv.swap z p * Equiv.swap o (Equiv.swap z p q), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hzo hz, Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]

theorem bsum {n : ℕ} {f : Fin n → V} (hf : Good b f) (a : Fin n → k) :
    b (∑ i, a i • f i) (∑ i, a i • f i) = ∑ i, a i ^ 2 * b (f i) (f i) := by
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    rw [hf.1 j i hji]; ring
  · simp

theorem good_pair (h2 : (2 : k) ≠ 0) {n : ℕ} {f : Fin n → V} (hf : Good b f) (a : Fin n → k)
    (hyy : b (∑ i, a i • f i) (∑ i, a i • f i) ≠ 0) (hpair : ∃ p q, p ≠ q ∧ a p ≠ 0 ∧ a q ≠ 0) :
    ∃ p q, p ≠ q ∧ a p ≠ 0 ∧ a q ≠ 0 ∧
      a p ^ 2 * b (f p) (f p) + a q ^ 2 * b (f q) (f q) ≠ 0 := by
  by_contra hall
  push_neg at hall
  obtain ⟨p, q, hpq, hp, hq⟩ := hpair
  have hcp : a p ^ 2 * b (f p) (f p) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hp) (hf.2 p)
  have hs3 : ∀ s, a s ≠ 0 → s = p ∨ s = q := by
    intro s hsne
    by_contra hcon
    push_neg at hcon
    have e1 := hall p q hpq hp hq
    have e2 := hall p s (Ne.symm hcon.1) hp hsne
    have e3 := hall q s (Ne.symm hcon.2) hq hsne
    apply hcp
    have : (2 : k) * (a p ^ 2 * b (f p) (f p)) = 0 := by linear_combination e1 + e2 - e3
    exact (mul_eq_zero.mp this).resolve_left h2
  apply hyy
  rw [bsum hf, Finset.sum_eq_add p q hpq]
  · exact hall p q hpq hp hq
  · intro c _ hc
    have : a c = 0 := by
      by_contra hne
      rcases hs3 c hne with h | h
      · exact hc.1 h
      · exact hc.2 h
    simp [this]
  · simp
  · simp

theorem move (hs : ∀ x y, b x y = b y x) (h2 : (2 : k) ≠ 0) {W : Submodule k V} {n : ℕ}
    (f : Fin (n + 1) → V) (hf : G b W f) {y : V} (hy : y ∈ W) (hyy : b y y ≠ 0) :
    ∃ f', G b W f' ∧ Relation.ReflTransGen (Step b W) f f' ∧ f' 0 = y := by
  classical
  have key : ∀ r : ℕ, ∀ f : Fin (n + 1) → V, G b W f → ∀ a : Fin (n + 1) → k, ∑ i, a i • f i = y →
      (Finset.univ.filter (fun i => a i ≠ 0)).card ≤ r →
      ∃ f', G b W f' ∧ Relation.ReflTransGen (Step b W) f f' ∧ f' 0 = y := by
    intro r
    induction r with
    | zero =>
      intro f hf a ha hc
      exfalso
      have hall : ∀ i, a i = 0 := by
        intro i
        by_contra hne
        have hmem : i ∈ Finset.univ.filter (fun i => a i ≠ 0) := by simp [hne]
        have := Finset.card_pos.2 ⟨i, hmem⟩
        omega
      simp [hall] at ha
      apply hyy
      rw [← ha]; simp
    | succ r ih =>
      intro f hf a ha hc
      by_cases hpair : ∃ p q, p ≠ q ∧ a p ≠ 0 ∧ a q ≠ 0
      · obtain ⟨p, q, hpq, hp, hq, hD⟩ := good_pair h2 hf.1 a (by rw [ha]; exact hyy) hpair
        have hN : 2 ≤ n + 1 := by
          have := Fin.val_ne_of_ne hpq
          have := p.isLt
          have := q.isLt
          omega
        let z : Fin (n + 1) := 0
        let o : Fin (n + 1) := ⟨1, hN⟩
        have hzo : z ≠ o := by simp [z, o, Fin.ext_iff]
        obtain ⟨σ, hσz, hσo⟩ := exists_perm z o p q hzo hpq
        have hF : G b W (f ∘ σ) := G_comp hf σ
        have hrF := perm_rtg n σ f hf
        have hsum : ∑ i, (a ∘ σ) i • (f ∘ σ) i = y := by
          rw [← ha]
          exact Equiv.sum_comp σ (fun i => a i • f i)
        have hFz : (f ∘ σ) z = f p := by simp [hσz]
        have hFo : (f ∘ σ) o = f q := by simp [hσo]
        have hAz : (a ∘ σ) z = a p := by simp [hσz]
        have hAo : (a ∘ σ) o = a q := by simp [hσo]
        obtain ⟨H, hH, hHz, hHi⟩ := pair_step hs hF hzo (α := (a ∘ σ) z) (β := (a ∘ σ) o)
          (by rw [hFz, hFo, hAz, hAo]; exact hD)
        have hstep : Step b W (f ∘ σ) H := by
          refine ⟨hF, hH, 0, fun j hj1 hj2 => ?_⟩
          have h1 : j ≠ z := fun h => hj1 (by subst h; rfl)
          have h2' : j ≠ o := fun h => hj2 (by subst h; rfl)
          exact (hHi j h1 h2').symm
        obtain ⟨A', hA'⟩ : ∃ A' : Fin (n + 1) → k,
            A' = Function.update (Function.update (a ∘ σ) z 1) o 0 := ⟨_, rfl⟩
        have hA'z : A' z = 1 := by simp [hA', Function.update_apply, hzo]
        have hA'o : A' o = 0 := by simp [hA']
        have hA'i : ∀ i, i ≠ z → i ≠ o → A' i = (a ∘ σ) i := by
          intro i h1 h2'; simp [hA', Function.update_apply, h1, h2']
        have hsum' : ∑ i, A' i • H i = y := by
          rw [← hsum]
          have : ∑ i, (A' i • H i - (a ∘ σ) i • (f ∘ σ) i) = 0 := by
            rw [Finset.sum_eq_add z o hzo]
            · rw [hA'z, hA'o, hHz, hAz, hAo]
              module
            · intro c _ hc
              rw [hHi c hc.1 hc.2, hA'i c hc.1 hc.2, sub_self]
            · simp
            · simp
          rw [Finset.sum_sub_distrib] at this
          exact sub_eq_zero.mp this
        have hcard : (Finset.univ.filter (fun i => A' i ≠ 0)).card ≤ r := by
          have hsub : Finset.univ.filter (fun i => A' i ≠ 0) ⊆
              (Finset.univ.filter (fun i => (a ∘ σ) i ≠ 0)).erase o := by
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
            have hio : i ≠ o := fun h => hi (by rw [h, hA'o])
            refine ⟨hio, ?_⟩
            by_cases hiz : i = z
            · rw [hiz, hAz]; exact hp
            · rw [← hA'i i hiz hio]; exact hi
          have hmem : o ∈ Finset.univ.filter (fun i => (a ∘ σ) i ≠ 0) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            show (a ∘ σ) o ≠ 0
            rw [hAo]; exact hq
          have heq : (Finset.univ.filter (fun i => (a ∘ σ) i ≠ 0)).card =
              (Finset.univ.filter (fun i => a i ≠ 0)).card :=
            Finset.card_equiv σ (by intro i; simp)
          calc _ ≤ ((Finset.univ.filter (fun i => (a ∘ σ) i ≠ 0)).erase o).card :=
                Finset.card_le_card hsub
            _ = (Finset.univ.filter (fun i => (a ∘ σ) i ≠ 0)).card - 1 :=
                Finset.card_erase_of_mem hmem
            _ ≤ r := by omega
        obtain ⟨f', hf', hr', h0⟩ := ih H hH A' hsum' hcard
        exact ⟨f', hf', hrF.trans ((Relation.ReflTransGen.single hstep).trans hr'), h0⟩
      · push_neg at hpair
        have hex : ∃ p, a p ≠ 0 := by
          by_contra hne
          push_neg at hne
          apply hyy
          rw [← ha]; simp [hne]
        obtain ⟨p, hp⟩ := hex
        have hone : ∀ j, j ≠ p → a j = 0 := by
          intro j hj
          by_contra hne
          exact hp (hpair j p hj hne)
        have hyp : y = a p • f p := by
          rw [← ha, Finset.sum_eq_single p]
          · intro j _ hj; rw [hone j hj]; simp
          · simp
        let z : Fin (n + 1) := 0
        obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (n + 1)), σ z = p := ⟨Equiv.swap z p, by simp⟩
        have hF : G b W (f ∘ σ) := G_comp hf σ
        have hrF := perm_rtg n σ f hf
        obtain ⟨H, hH, hHz, hHi⟩ := scale_step hs hF z hp
        have hstep : Step b W (f ∘ σ) H := by
          refine ⟨hF, hH, 0, fun j hj1 hj2 => ?_⟩
          have h1 : j ≠ z := fun h => hj1 (by subst h; rfl)
          exact (hHi j h1).symm
        refine ⟨H, hH, hrF.trans (Relation.ReflTransGen.single hstep), ?_⟩
        rw [hyp]
        have : H z = a p • f p := by simp [hHz, hσ]
        exact this
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 (hf.2 ▸ hy)
  exact key _ f hf a ha le_rfl

theorem main (hs : ∀ x y, b x y = b y x) (h2 : (2 : k) ≠ 0) :
    ∀ (n : ℕ) (W : Submodule k V) (f g : Fin n → V), G b W f → G b W g →
      Relation.ReflTransGen (Step b W) f g := by
  intro n
  induction n with
  | zero =>
    intro W f g _ _
    have : f = g := Subsingleton.elim _ _
    rw [this]
  | succ n ih =>
    intro W f g hf hg
    obtain ⟨f', hf', hr, h0⟩ := move hs h2 f hf (y := g 0)
      (by rw [← hg.2]; exact Submodule.subset_span (Set.mem_range_self 0)) (hg.1.2 0)
    have hyy : b (g 0) (g 0) ≠ 0 := hg.1.2 0
    have ht_f := tail_span hf'
    have ht_g := tail_span hg
    rw [h0] at ht_f
    obtain ⟨W', hW'⟩ : ∃ W', W' = Submodule.span k (Set.range fun i : Fin n => g i.succ) := ⟨_, rfl⟩
    have hGf : G b W' (fun i : Fin n => f' i.succ) :=
      ⟨⟨fun i j hij => hf'.1.1 _ _ (fun h => hij (Fin.succ_injective _ h)), fun i => hf'.1.2 _⟩,
        by rw [hW', ht_f, ht_g]⟩
    have hGg : G b W' (fun i : Fin n => g i.succ) :=
      ⟨⟨fun i j hij => hg.1.1 _ _ (fun h => hij (Fin.succ_injective _ h)), fun i => hg.1.2 _⟩, hW'.symm⟩
    have hyW : ∀ w ∈ W', b (g 0) w = 0 := by
      intro w hw
      rw [hW', ht_g] at hw
      exact hw.2
    have hWeq : Submodule.span k {g 0} ⊔ W' = W := by
      rw [← hg.2, hW', range_eq_insert, Submodule.span_insert]
    have hlift := Relation.ReflTransGen.lift
      (fun t : Fin n → V => (Fin.cons (g 0) t : Fin (n + 1) → V))
      (fun t t' h => step_cons hs hyy hyW h) _ _ (ih W' _ _ hGf hGg)
    rw [hWeq] at hlift
    have hcf : (Fin.cons (g 0) (fun i : Fin n => f' i.succ) : Fin (n + 1) → V) = f' := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [h0]
      · simp
    have hcg : (Fin.cons (g 0) (fun i : Fin n => g i.succ) : Fin (n + 1) → V) = g := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp
    change Relation.ReflTransGen (Step b W) (Fin.cons (g 0) (fun i : Fin n => f' i.succ) : Fin (n + 1) → V)
      (Fin.cons (g 0) (fun i : Fin n => g i.succ) : Fin (n + 1) → V) at hlift
    rw [hcf, hcg] at hlift
    exact hr.trans hlift

end Lemma68

open Lemma68 in
/-- **Lemma 6.8** (Milne, *CFT*, VIII, Lemma 6.8, p. 254; O'Meara 58:1), proved: any two orthogonal bases of a
nondegenerate quadratic space over a field with $2$ invertible are joined by a chain of orthogonal bases, consecutive
ones differing in at most two adjacent positions. See the module docstring for the proof. -/
@[kb "milne2020cft" "Ch. VIII, Lemma 6.8, p. 254 (O'Meara 58:1)"]
theorem lemma6_8 : Lemma6_8 := by
  refine ⟨fun k V _ _ _ _ h2 n Q hQ B B' hB hB' => ?_⟩
  have hs : ∀ x y : V, QuadraticMap.associated Q x y = QuadraticMap.associated Q y x :=
    fun x y => QuadraticMap.associated_isSymm k Q x y
  have good : ∀ B : Module.Basis (Fin n) k V,
      (∀ i j, i ≠ j → QuadraticMap.associated Q (B i) (B j) = 0) →
      G (QuadraticMap.associated Q) ⊤ B := by
    intro B hB
    refine ⟨⟨hB, fun i hi => ?_⟩, B.span_eq⟩
    have h0 : (QuadraticMap.associated Q) (B i) = 0 := by
      apply B.ext
      intro j
      by_cases hij : i = j
      · subst hij; simpa using hi
      · simpa using hB i j hij
    have := hQ.1 (B i) (fun y => by rw [h0]; rfl)
    exact B.ne_zero i this
  have rtg := main hs h2 n ⊤ B B' (good B hB) (good B' hB')
  obtain ⟨m, C, h0, hm, hC⟩ := rtg_chain rtg
  have hG : ∀ l, l ≤ m → G (QuadraticMap.associated Q) ⊤ (C l) := by
    intro l hl
    rcases Nat.eq_zero_or_pos l with rfl | hpos
    · rw [h0]; exact good B hB
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      exact (hC l' (by omega)).2.1
  obtain ⟨Cb, hCb⟩ : ∃ Cb : Fin (m + 1) → Module.Basis (Fin n) k V, ∀ l i, Cb l i = C l i :=
    ⟨fun l => Module.Basis.mk (v := C l)
        (Good.linearIndependent (hG l (by omega)).1)
        (le_of_eq (hG l (by omega)).2.symm),
      fun l i => by simp⟩
  refine ⟨m, Cb, ?_, ?_, ?_, ?_⟩
  · apply Module.Basis.eq_of_apply_eq
    intro i
    rw [hCb]
    show C 0 i = B i
    rw [h0]
  · apply Module.Basis.eq_of_apply_eq
    intro i
    rw [hCb]
    show C m i = B' i
    rw [hm]
  · intro l i j hij
    rw [hCb, hCb]
    exact (hG l (by omega)).1.1 i j hij
  · intro l
    obtain ⟨_, _, i, hi⟩ := hC l l.2
    refine ⟨i, fun j h1 h2 => ?_⟩
    rw [hCb, hCb]
    simpa using hi j h1 h2

end NumberFieldKB.MilneCFT.Ch8
