import NumberFieldKB.Ideles.Compact
import NumberFieldKB.WeilBNT.AdeleBoxes

/-!
# Weil, *Basic Number Theory*, Chapter IV, §4: the groups $\Omega(P)$ and Theorem 7

$k$ is a number field and $P=P_\infty\cup S$ with $S$ a finite set of finite places. Weil (IV.§4, (5), p. 76) puts
$$\Omega(P)=\prod_{v\in P}k_v^\times\times\prod_{v\notin P}r_v^\times ,$$
an open subgroup of the idele group $k_{\mathbb A}^\times$ (IV.§3, Cor. of Prop. 2), and proves

* **Theorem 7** (p. 76): $k_{\mathbb A}^\times/k^\times\Omega(P)$ is finite (`weil_IV_4_thm7`);
* **Corollary** (p. 77): $P$ can be chosen with $k_{\mathbb A}^\times=k^\times\Omega(P)$ (`weil_IV_4_thm7_cor`).

For $P=P_\infty$ this is, through the map from ideles to ideals, the finiteness of the class number (Weil's remark after
the corollary); here it is proved adelically, by Weil's argument, without the class group:

1. $\Omega^1(P)=\Omega(P)\cap k^1$ is open in $k^1$, so its image is an open subgroup of the compact group $k^1/k^\times$
   (IV.§4 Thm. 6; NumberFieldKB `IdeleClassGroup.isCompact_normOne`), hence of finite index;
2. $\Omega(P)$ contains the ideles $Z(\lambda)$ that are $1$ at the finite places (Cor. 2 of Thm. 5), whose norms fill
   $\mathbb R_{>0}$, so $k_{\mathbb A}^\times=k^1\,\Omega(P)$ and $k_{\mathbb A}^\times/k^\times\Omega(P)$ is a quotient of
   $k^1/k^\times\Omega^1(P)$.

Main declarations:
* **`omega K S`**: $\Omega(P_\infty\cup S)$ as a subgroup of Mathlib's `IdeleGroup (𝓞 K) K`, the ideles whose components
  at $v\notin S$ (finite) and their inverses are integral; `mem_omega_iff` says this is "the finite components outside
  $S$ are units of $r_v$";
* **`isOpen_omega`**, **`exists_mem_omega`**, **`omega_mono`**: text (5) and IV.§3, Cor. of Prop. 2 ($\Omega(P)$ is open,
  increasing in $P$, and the idele group is their union).
-/

open IsDedekindDomain NumberField Filter Topology
open NumberFieldKB.Ideles

noncomputable section

namespace NumberFieldKB.WeilBNT

variable (K : Type) [Field K] [NumberField K]

/-- **Weil's $\Omega(P)$** for $P=P_\infty\cup S$: the ideles $x$ with $x_v\in r_v^\times$ for every finite place
$v\notin S$, i.e. $x$ and $x^{-1}$ lie in the box $k_{\mathbb A}(P)$. -/
def omega (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup (𝓞 K) K) where
  carrier := {x | (x : AdeleRing (𝓞 K) K) ∈ AdeleRing.box K S ∧
    ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K) ∈ AdeleRing.box K S}
  mul_mem' {x y} hx hy := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact mul_mem hx.1 hy.1
    · rw [mul_inv_rev, Units.val_mul]; exact mul_mem hy.2 hx.2
  one_mem' := by simp only [inv_one, Units.val_one, Set.mem_ofPred_eq, and_self]; exact one_mem _
  inv_mem' {x} hx := by simpa only [Set.mem_ofPred_eq, inv_inv] using hx.symm

variable {K}

theorem mem_omega {S : Set (HeightOneSpectrum (𝓞 K))} {x : IdeleGroup (𝓞 K) K} :
    x ∈ omega K S ↔ (x : AdeleRing (𝓞 K) K) ∈ AdeleRing.box K S ∧
      ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K) ∈ AdeleRing.box K S := Iff.rfl

/-- $x\in\Omega(P)$ if and only if every finite component outside $S$ is a unit of $r_v$ (an element of norm one). -/
theorem mem_omega_iff {S : Set (HeightOneSpectrum (𝓞 K))} {x : IdeleGroup (𝓞 K) K} :
    x ∈ omega K S ↔ ∀ v, v ∉ S → Valued.v ((x : AdeleRing (𝓞 K) K).2 v) = 1 := by
  have hinv : ∀ v, ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 v *
      (x : AdeleRing (𝓞 K) K).2 v = 1 := by
    intro v
    exact congrArg (fun y : AdeleRing (𝓞 K) K => y.2 v) (Units.inv_mul x)
  simp only [mem_omega, AdeleRing.mem_box, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · rintro ⟨h1, h2⟩ v hv
    have h := congrArg Valued.v (hinv v)
    rw [map_mul, map_one] at h
    exact le_antisymm (h1 v hv) (by
      by_contra hlt
      push Not at hlt
      have := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (h2 v hv) hlt zero_le zero_lt_one
      simp [h] at this)
  · intro h
    refine ⟨fun v hv => (h v hv).le, fun v hv => ?_⟩
    have h' := congrArg Valued.v (hinv v)
    rw [map_mul, map_one, h v hv, mul_one] at h'
    exact h'.le

theorem omega_mono {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) : omega K S ≤ omega K T :=
  fun _ hx => ⟨(weil_IV_1_prop1 (K := K)).2.1 S T h hx.1, (weil_IV_1_prop1 (K := K)).2.1 S T h hx.2⟩

/-- **Weil, IV.§4 (5)** (and IV.§3, Cor. of Prop. 2 for $k$): $\Omega(P)$ is an open subgroup of the idele group. -/
@[kb "weil1973bnt" "Ch. IV, §4, (5) (p. 76); Ch. IV, §3, Cor. of Prop. 2 (p. 72)"]
theorem isOpen_omega (S : Set (HeightOneSpectrum (𝓞 K))) : IsOpen (omega K S : Set (IdeleGroup (𝓞 K) K)) := by
  have hbox := (weil_IV_1_prop1 (K := K)).1 S
  exact (hbox.preimage Units.continuous_val).inter (hbox.preimage Units.continuous_coe_inv)

/-- **Weil, IV.§3, Cor. of Prop. 2** (for $k$): the idele group is the union of the $\Omega(P)$. -/
@[kb "weil1973bnt" "Ch. IV, §3, Cor. of Prop. 2 (p. 72)"]
theorem exists_mem_omega (x : IdeleGroup (𝓞 K) K) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), x ∈ omega K (S : Set (HeightOneSpectrum (𝓞 K))) := by
  classical
  obtain ⟨S, hS⟩ := (weil_IV_1_prop1 (K := K)).2.2 (x : AdeleRing (𝓞 K) K)
  obtain ⟨T, hT⟩ := (weil_IV_1_prop1 (K := K)).2.2 ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)
  refine ⟨S ∪ T, ?_, ?_⟩
  · exact (weil_IV_1_prop1 (K := K)).2.1 _ _ (by simp) hS
  · exact (weil_IV_1_prop1 (K := K)).2.1 _ _ (by simp) hT

/-! ### Ideles of arbitrary norm in $\Omega(P_\infty)$ (Weil, IV.§4, Cor. 2 of Thm. 5) -/

omit [NumberField K] in
/-- Every positive real number is the `mult`-th power of the norm of a nonzero element of the completion at an infinite
place. (The same argument as `NumberFieldKB.MilneCFT.exists_norm_completion`, repeated here to keep this file's imports
small.) -/
theorem exists_norm_completion' (w : InfinitePlace K) (t : ℝ) (ht : 0 < t) :
    ∃ y : w.Completion, y ≠ 0 ∧ ‖y‖ ^ w.mult = t := by
  by_cases hw : w.IsReal
  · obtain ⟨y, hy⟩ := (InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw) t
    have hn : ‖y‖ = ‖t‖ := by
      rw [← hy]
      exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) y).symm
    refine ⟨y, ?_, ?_⟩
    · rintro rfl; simp at hy; linarith
    · rw [InfinitePlace.mult, ite_eq_left hw, hn, pow_one, Real.norm_of_nonneg ht.le]
  · have hc := InfinitePlace.not_isReal_iff_isComplex.1 hw
    obtain ⟨y, hy⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hc
      ((Real.sqrt t : ℝ) : ℂ)
    have hn : ‖y‖ = ‖((Real.sqrt t : ℝ) : ℂ)‖ := by
      rw [← hy]
      exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) y).symm
    refine ⟨y, ?_, ?_⟩
    · rintro rfl
      have h1 := Real.sqrt_pos.2 ht
      have h2 : ((Real.sqrt t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
      exact h2 (by simpa using hy.symm)
    · rw [InfinitePlace.mult, ite_eq_right hw, hn, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt ht.le]

/-- $\Omega(P_\infty)$ contains ideles of every positive norm (Weil, IV.§4, Cor. 2 of Thm. 5: the ideles $Z(\lambda)$;
here the idele is supported at one infinite place). -/
theorem exists_mem_omega_ideleGroupNorm (S : Set (HeightOneSpectrum (𝓞 K))) (t : NNReal) (ht : 0 < t) :
    ∃ x ∈ omega K S, ideleGroupNorm K x = t := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain ⟨y, hy0, hy⟩ := exists_norm_completion' w (t : ℝ) ht
  refine ⟨IdeleGroup.ofCompletion (𝓞 K) K w (Units.mk0 y hy0), ⟨fun v _ => ?_, fun v _ => ?_⟩, ?_⟩
  · show ((IdeleGroup.ofCompletion (𝓞 K) K w (Units.mk0 y hy0) : AdeleRing (𝓞 K) K)).2 v ∈ _
    simp only [IdeleGroup.val_ofCompletion_apply]
    exact one_mem _
  · show (((IdeleGroup.ofCompletion (𝓞 K) K w (Units.mk0 y hy0))⁻¹ : IdeleGroup (𝓞 K) K) :
      AdeleRing (𝓞 K) K).2 v ∈ _
    rw [← map_inv]
    simp only [IdeleGroup.val_ofCompletion_apply]
    exact one_mem _
  apply NNReal.coe_injective
  rw [coe_ideleGroupNorm, AdeleRing.norm_def]
  have h2 : ‖((IdeleGroup.ofCompletion (𝓞 K) K w (Units.mk0 y hy0) : IdeleGroup (𝓞 K) K) :
      AdeleRing (𝓞 K) K).2‖ = 1 := by
    have h : ∀ v : HeightOneSpectrum (𝓞 K), ‖(1 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := fun v => norm_one
    simp [FiniteAdeleRing.norm_def, h]
  have h1 : ‖((IdeleGroup.ofCompletion (𝓞 K) K w (Units.mk0 y hy0) : IdeleGroup (𝓞 K) K) :
      AdeleRing (𝓞 K) K).1‖ = ‖y‖ ^ w.mult := by
    rw [InfiniteAdeleRing.norm_def]
    classical
    rw [Finset.prod_eq_single w]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [h1, h2, mul_one, hy]

/-- The norm of an idele is positive. -/
theorem ideleGroupNorm_pos (x : IdeleGroup (𝓞 K) K) : 0 < ideleGroupNorm K x := by
  refine pos_iff_ne_zero.mpr fun h => ?_
  have := map_mul (ideleGroupNorm K) x x⁻¹
  rw [mul_inv_cancel, map_one, h, zero_mul] at this
  exact one_ne_zero this

/-- $k_{\mathbb A}^\times=k^1\,\Omega(P)$: every idele is a norm-one idele times an element of $\Omega(P)$. -/
theorem exists_mul_mem_ideleGroupOne (S : Set (HeightOneSpectrum (𝓞 K))) (x : IdeleGroup (𝓞 K) K) :
    ∃ m ∈ omega K S, x * m⁻¹ ∈ ideleGroupOne K := by
  obtain ⟨m, hm, hnorm⟩ := exists_mem_omega_ideleGroupNorm S (ideleGroupNorm K x) (ideleGroupNorm_pos x)
  refine ⟨m, hm, ?_⟩
  show ideleGroupNorm K (x * m⁻¹) = 1
  rw [map_mul, map_inv, hnorm, mul_inv_cancel₀ (ideleGroupNorm_pos x).ne']

/-! ### Theorem 7 -/

/-- **Weil, IV.§4, Theorem 7** (number field $k$, $P=P_\infty\cup S$): the group $k_{\mathbb A}^\times/k^\times\Omega(P)$
is finite. Weil's proof: the image of the open subgroup $\Omega^1(P)$ in the compact group $k^1/k^\times$ has finite index,
and $k_{\mathbb A}^\times = k^1\,\Omega(P)$. -/
@[kb "weil1973bnt" "Ch. IV, §4, Thm. 7 (p. 76), number field case"]
theorem weil_IV_4_thm7 (S : Set (HeightOneSpectrum (𝓞 K))) :
    Finite (IdeleGroup (𝓞 K) K ⧸ (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ omega K S)) := by
  set Pr := IdeleGroup.principalSubgroup (𝓞 K) K
  set N := Pr ⊔ omega K S
  set C1 := IdeleClassGroup.normOne K
  have : CompactSpace C1 := isCompact_iff_compactSpace.mp (IdeleClassGroup.isCompact_normOne (F := K))
  -- the map $C^1\to k_{\mathbb A}^\times/k^\times\Omega(P)$
  let φ : C1 →* IdeleGroup (𝓞 K) K ⧸ N :=
    (QuotientGroup.lift Pr (QuotientGroup.mk' N) (by
      rw [QuotientGroup.ker_mk']; exact le_sup_left)).comp C1.subtype
  -- the open subgroup: the image of $\Omega(P)$ in $C^1$
  let H : Subgroup (IdeleClassGroup (𝓞 K) K) := (omega K S).map (QuotientGroup.mk' Pr)
  have hHopen : IsOpen (H : Set (IdeleClassGroup (𝓞 K) K)) := by
    have : (H : Set (IdeleClassGroup (𝓞 K) K)) = (QuotientGroup.mk : IdeleGroup (𝓞 K) K → _) '' (omega K S) := by
      simp only [H, Subgroup.coe_map, QuotientGroup.coe_mk']
      rfl
    rw [this]
    exact QuotientGroup.isOpenMap_coe _ (isOpen_omega S)
  let U : Subgroup C1 := H.subgroupOf C1
  have hUopen : IsOpen (U : Set C1) := hHopen.preimage continuous_subtype_val
  have hU : U ≤ φ.ker := by
    rintro ⟨c, hc⟩ hcU
    obtain ⟨m, hm, hmc⟩ := (Subgroup.mem_subgroupOf.mp hcU : c ∈ H)
    have hmc' : ((m : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K) = c := hmc
    subst hmc'
    rw [MonoidHom.mem_ker]
    simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.lift_mk, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff m).mpr (le_sup_right (a := Pr) hm)
  have : Finite (C1 ⧸ U) := Subgroup.quotient_finite_of_isOpen U hUopen
  refine Finite.of_surjective (QuotientGroup.lift U φ hU) ?_
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨m, hm, hxm⟩ := exists_mul_mem_ideleGroupOne S x
  refine ⟨((⟨((x * m⁻¹ : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K),
    (IdeleClassGroup.mem_normOne_mk _).mpr hxm⟩ : C1) : C1 ⧸ U), ?_⟩
  rw [QuotientGroup.lift_mk]
  simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.lift_mk, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq]
  have : (x * m⁻¹)⁻¹ * x = m := by group
  rw [this]
  exact le_sup_right (a := Pr) hm

/-- **Weil, IV.§4, Corollary of Theorem 7**: one can choose $P$ so that $k_{\mathbb A}^\times=k^\times\Omega(P)$. Weil's
proof: take representatives of the finitely many classes modulo $k^\times\Omega(P_\infty)$ and enlarge $P$ until they
all lie in $\Omega(P)$. -/
@[kb "weil1973bnt" "Ch. IV, §4, Cor. of Thm. 7 (p. 77), number field case"]
theorem weil_IV_4_thm7_cor :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      IdeleGroup.principalSubgroup (𝓞 K) K ⊔ omega K (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ := by
  classical
  set Pr := IdeleGroup.principalSubgroup (𝓞 K) K
  set N₀ := Pr ⊔ omega K (∅ : Set (HeightOneSpectrum (𝓞 K)))
  have : Finite (IdeleGroup (𝓞 K) K ⧸ N₀) := weil_IV_4_thm7 ∅
  have : Fintype (IdeleGroup (𝓞 K) K ⧸ N₀) := Fintype.ofFinite _
  choose T hT using fun q : IdeleGroup (𝓞 K) K ⧸ N₀ => exists_mem_omega (Quotient.out q)
  refine ⟨Finset.univ.biUnion T, eq_top_iff.mpr fun x _ => ?_⟩
  set q : IdeleGroup (𝓞 K) K ⧸ N₀ := (x : IdeleGroup (𝓞 K) K ⧸ N₀)
  have hz : Quotient.out q ∈ omega K ((Finset.univ.biUnion T : Finset _) : Set (HeightOneSpectrum (𝓞 K))) :=
    omega_mono (by
      intro v hv
      simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      exact ⟨q, hv⟩) (hT q)
  have hN : N₀ ≤ Pr ⊔ omega K ((Finset.univ.biUnion T : Finset _) : Set (HeightOneSpectrum (𝓞 K))) :=
    sup_le_sup_left (omega_mono (Set.empty_subset _)) _
  have hxq : (Quotient.out q)⁻¹ * x ∈ N₀ := by
    rw [← QuotientGroup.eq]
    exact QuotientGroup.out_eq' q
  have : x = Quotient.out q * ((Quotient.out q)⁻¹ * x) := by group
  rw [this]
  exact mul_mem (le_sup_right (a := Pr) hz) (hN hxq)

end NumberFieldKB.WeilBNT

end
