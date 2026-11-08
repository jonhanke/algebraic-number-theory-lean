import NumberFieldKB.WeilBNT.IdeleCharacterComplex

/-!
# Weil, *Basic Number Theory*, VII.§3, Lemma 4: representations of totally disconnected groups

Weil (VII.§3, p. 114) calls a topological group *totally disconnected* if the open subgroups form a basis of
neighbourhoods of the neutral element; this is Mathlib's `NonarchimedeanGroup`. A *representation* into
$\mathbb C^\times$ is a continuous morphism.

* **`weil_VII_3_lemma4`** (first assertion): every representation of a totally disconnected group into
  $\mathbb C^\times$ is trivial on an open subgroup, hence locally constant (`weil_VII_3_lemma4_locallyConstant`).
  (Weil also assumes $G$ locally compact; it is not needed.)
* **`weil_VII_3_lemma4_compact`** (second assertion): if $G$ is moreover compact, every such representation has
  finite order and takes values of absolute value $1$ (it is a character of finite order).

Weil's proof: by Lemmas 2–3 ($\mathbb C^\times$ has no small subgroups, `noSmallSubgroups_complexUnits`) the image of a
small open subgroup is trivial; an open subgroup of a compact group has finite index.

The third assertion (a compact commutative group whose characters all have finite order is totally disconnected)
uses Pontryagin duality ($G$ is the dual of the discrete group $G^*$), which Mathlib does not have; it is not
formalized here.
-/

open Topology

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {G : Type*} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]

/-- **Weil, VII.§3, Lemma 4, first assertion.** A continuous morphism of a totally disconnected group into
$\mathbb C^\times$ is trivial on some open subgroup. -/
@[kb "weil1973bnt" "Ch. VII, §3, Lemma 4, first assertion"]
theorem weil_VII_3_lemma4 (ω : G →* ℂˣ) (hω : Continuous ω) :
    ∃ H : OpenSubgroup G, (H : Subgroup G) ≤ ω.ker := by
  obtain ⟨U, hU, hsmall⟩ := noSmallSubgroups_complexUnits
  have hpre : ω ⁻¹' U ∈ 𝓝 (1 : G) := hω.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨H, hH⟩ := NonarchimedeanGroup.is_nonarchimedean _ hpre
  refine ⟨H, ?_⟩
  have hmap : (H : Subgroup G).map ω = ⊥ := hsmall _ (by
    rintro _ ⟨x, hx, rfl⟩
    exact hH hx)
  intro x hx
  have : ω x ∈ (H : Subgroup G).map ω := ⟨x, hx, rfl⟩
  rw [hmap, Subgroup.mem_bot] at this
  exact this

/-- **Weil, VII.§3, Lemma 4, first assertion (locally constant).** A continuous morphism of a totally disconnected
group into $\mathbb C^\times$ is locally constant. -/
@[kb "weil1973bnt" "Ch. VII, §3, Lemma 4, first assertion"]
theorem weil_VII_3_lemma4_locallyConstant (ω : G →* ℂˣ) (hω : Continuous ω) : IsLocallyConstant ω := by
  obtain ⟨H, hH⟩ := weil_VII_3_lemma4 ω hω
  have hker : IsOpen (ω.ker : Set G) := Subgroup.isOpen_mono hH H.isOpen
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro c
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hn : (fun y => x * y) '' (ω.ker : Set G) ∈ 𝓝 x := by
    have := (isOpenMap_mul_left x).image_mem_nhds (hker.mem_nhds (Subgroup.one_mem _))
    simpa using this
  refine Filter.mem_of_superset hn ?_
  rintro _ ⟨y, hy, rfl⟩
  have hy' : ω y = 1 := hy
  simp only [Set.mem_preimage, Set.mem_singleton_iff, map_mul, hy', mul_one] at hx ⊢
  exact hx

/-- **Weil, VII.§3, Lemma 4, second assertion.** If $G$ is a compact totally disconnected group, every continuous
morphism $\omega$ of $G$ into $\mathbb C^\times$ has finite order ($\omega^n=1$ for some $n\ge1$), and
$\lvert\omega(g)\rvert=1$ for all $g$. -/
@[kb "weil1973bnt" "Ch. VII, §3, Lemma 4, second assertion"]
theorem weil_VII_3_lemma4_compact [CompactSpace G] (ω : G →* ℂˣ) (hω : Continuous ω) :
    (∃ n : ℕ, 0 < n ∧ ω ^ n = 1) ∧ ∀ g, ‖((ω g : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨H, hH⟩ := weil_VII_3_lemma4 ω hω
  have : Finite (G ⧸ (H : Subgroup G)) := inferInstance
  have hfin : (H : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hker : ω.ker.FiniteIndex := Subgroup.finiteIndex_of_le hH
  have hn0 : ω.ker.index ≠ 0 := hker.index_ne_zero
  have hpow : ∀ g, ω g ^ ω.ker.index = 1 := by
    intro g
    rw [← map_pow]
    exact Subgroup.pow_index_mem ω.ker g
  refine ⟨⟨ω.ker.index, Nat.pos_of_ne_zero hn0, ?_⟩, fun g => ?_⟩
  · ext g
    simp [hpow g]
  · have h := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (hpow g)
    simp only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn0).1 h

end NumberFieldKB.WeilBNT
