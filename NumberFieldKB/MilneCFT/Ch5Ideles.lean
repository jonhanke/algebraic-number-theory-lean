import NumberFieldKB.MilneCFT.Ch5MainIdeal
import NumberFieldKB.Ideles.Compact
import NumberFieldKB.Ideles.RelativeNorm
import NumberFieldKB.HeckeCharacter.Basic
import NumberFieldKB.MilneCFT.LocalCFT.Uniqueness
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleIdeal
import Mathlib.Computability.Reduce
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Topology.Algebra.Group.Units

/-!
# Idèles (Milne, *Class Field Theory*, Chapter V, §4, pp. 168–177)

The idèle group $I_K$ is Mathlib's `IdeleGroup (𝓞 K) K` (the units of the adèle ring, with the unit-group topology),
the idèle class group $C_K = I_K/K^\times$ is `IdeleClassGroup (𝓞 K) K`.

* **4.1** (`item_4_1`): $\mathrm{id} : I_K \to I$, $(a_v) \mapsto \prod\mathfrak p_v^{\mathrm{ord}_v(a_v)}$
  (`ideleToIdeal`, QuadFormsKB's `ideleIdeal` on the finite part) is onto with kernel the idèles that are units at every
  finite prime;
* **4.2** (`item_4_2`): $K^\times \to I_K$ is injective with discrete image; **4.3** (`item_4_3`): $K_v^\times \to I_K$ is
  a topological embedding; **4.4** (`item_4_4`): the content (`NumberFieldKB.Ideles.ideleGroupNorm`) is onto
  $\mathbb R_{>0}$, $K^\times \subseteq I^1$, $C_K$ is not compact, $I^1/K^\times$ is compact; **Aside 4.5**;
* $W_\mathfrak m(\mathfrak p)$, $I_\mathfrak m$, $W_\mathfrak m$ (`idelesMod`, `idelesW`), $K_{\mathfrak m,1} = K^\times \cap
  I_\mathfrak m$ (`mem_congruenceSubgroup_iff_mem_idelesMod`); **Proposition 4.6** (`prop_4_6a`, `prop_4_6b`);
* Proposition 4.7 to Corollary 4.13: `Ch5IdelesChar.lean`.
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev Filter Topology
open scoped nonZeroDivisors ValuativeRel
open NumberField.InfinitePlace

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-! ## 4.1–4.5 -/

variable (K) in
/-- **The ideal of an idèle** $\mathrm{id} : I_K \to I$, $(a_v) \mapsto \prod_{v \text{ finite}}\mathfrak p_v^{\mathrm{ord}_v(a_v)}$
(Milne, *CFT*, V, 4.1, p. 170): QuadFormsKB's `ideleIdeal` applied to the finite part. -/
@[kb "milne2020cft" "Ch. V, 4.1 (the map id : I_K → I)"]
def ideleToIdeal : IdeleGroup (𝓞 K) K →* (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  (QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal K).comp
    (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K →+*
      FiniteAdeleRing (𝓞 K) K).toMonoidHom)

/-- The component at a finite prime $v$ of an idèle. -/
def ideleFinAt (x : IdeleGroup (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K :=
  (x : AdeleRing (𝓞 K) K).2 v

/-- The component at an infinite place $w$ of an idèle. -/
def ideleInfAt (x : IdeleGroup (𝓞 K) K) (w : InfinitePlace K) : w.Completion :=
  (x : AdeleRing (𝓞 K) K).1 w

theorem ideleFinAt_mul (x y : IdeleGroup (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ideleFinAt (x * y) v = ideleFinAt x v * ideleFinAt y v := rfl

theorem ideleFinAt_one (v : HeightOneSpectrum (𝓞 K)) : ideleFinAt (1 : IdeleGroup (𝓞 K) K) v = 1 := rfl

theorem ideleFinAt_inv (x : IdeleGroup (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ideleFinAt x⁻¹ v = (ideleFinAt x v)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← ideleFinAt_mul, mul_inv_cancel, ideleFinAt_one]

theorem ideleInfAt_mul (x y : IdeleGroup (𝓞 K) K) (w : InfinitePlace K) :
    ideleInfAt (x * y) w = ideleInfAt x w * ideleInfAt y w := rfl

theorem ideleInfAt_one (w : InfinitePlace K) : ideleInfAt (1 : IdeleGroup (𝓞 K) K) w = 1 := rfl

theorem ideleInfAt_inv (x : IdeleGroup (𝓞 K) K) (w : InfinitePlace K) :
    ideleInfAt x⁻¹ w = (ideleInfAt x w)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← ideleInfAt_mul, mul_inv_cancel, ideleInfAt_one]

/-- **4.1** (Milne, *CFT*, V, p. 170): $\mathrm{id} : I_K \to I$ is onto, with kernel $I_{S_\infty}$, the idèles that are
units at every finite prime. -/
@[kb "milne2020cft" "Ch. V, 4.1"]
theorem item_4_1 : Function.Surjective (ideleToIdeal K) ∧
    ∀ x : IdeleGroup (𝓞 K) K, ideleToIdeal K x = 1 ↔ ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (ideleFinAt x v) = 1 := by
  refine ⟨fun I => ?_, fun x => ?_⟩
  · obtain ⟨z, hz⟩ := QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal_surjective (F := K) I
    exact ⟨Units.map (MonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) z, hz⟩
  · show QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal K _ = 1 ↔ _
    rw [QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal_eq_one_iff,
      QuadFormsKB.Tamagawa.Measure.Weil.mem_OHatUnits_iff_ordAt]
    exact forall_congr' fun v => QuadFormsKB.Tamagawa.Measure.Weil.ordAt_eq_zero_iff _ v

/-- $\mathrm{id}$ of a principal idèle is the principal ideal. -/
theorem ideleToIdeal_unitEmbedding (a : Kˣ) :
    ideleToIdeal K (IdeleGroup.unitEmbedding (𝓞 K) K a) = toPrincipalIdeal (𝓞 K) K a :=
  QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal_finDiag a

/-- An open neighbourhood of zero in the adèle ring (small at the infinite places, integral at the finite ones)
meeting `K` only in zero. -/
def discreteNbhd (K : Type) [Field K] [NumberField K] : Set (AdeleRing (𝓞 K) K) :=
  {x | (∀ w, ‖x.1 w‖ < 1) ∧ ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (x.2 v) ≤ 1}

/-- `discreteNbhd` is open. -/
theorem isOpen_discreteNbhd : IsOpen (discreteNbhd K) := by
  have hA : IsOpen {y : InfiniteAdeleRing K | ∀ w, ‖y w‖ < 1} := by
    have : {y : InfiniteAdeleRing K | ∀ w, ‖y w‖ < 1} =
        Set.pi Set.univ (fun w : InfinitePlace K => {z : w.Completion | ‖z‖ < 1}) := by
      ext y
      exact ⟨fun h w _ => h w, fun h w => h w (Set.mem_univ _)⟩
    rw [this]
    exact isOpen_set_pi Set.finite_univ fun w _ => isOpen_lt continuous_norm continuous_const
  have hB : IsOpen {f : FiniteAdeleRing (𝓞 K) K | ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (f v) ≤ 1} := by
    have := RestrictedProduct.isOpen_forall_mem
      (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      (fun v => Valued.isOpen_valuationSubring _)
    exact this
  have : discreteNbhd K = (Prod.fst ⁻¹' {y : InfiniteAdeleRing K | ∀ w, ‖y w‖ < 1}) ∩
      (Prod.snd ⁻¹' {f : FiniteAdeleRing (𝓞 K) K | ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (f v) ≤ 1}) := rfl
  rw [this]
  exact (hA.preimage continuous_fst).inter (hB.preimage continuous_snd)

/-- An element of `K` in `discreteNbhd` is zero (its norm is a rational integer of absolute value less than one). -/
theorem eq_zero_of_algebraMap_mem_discreteNbhd {ξ : K}
    (h : algebraMap K (AdeleRing (𝓞 K) K) ξ ∈ discreteNbhd K) : ξ = 0 := by
  obtain ⟨h1, h2⟩ := h
  have hval : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ξ ≤ 1 := by
    intro v
    have := h2 v
    rw [AdeleRing.algebraMap_snd_apply] at this
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  obtain ⟨n, hn⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ξ hval
  by_contra hξ
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hξ (by rw [← hn, map_zero])
  have hN : Algebra.norm ℤ n ≠ 0 := by
    rwa [Ne, Algebra.norm_eq_zero_iff]
  have hnorm : ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) < 1 := by
    rw [← InfiniteAdeleRing.coe_norm_eq_abs_norm, InfiniteAdeleRing.norm_def]
    classical
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
    have hf : ∀ w : InfinitePlace K, ‖algebraMap K (InfiniteAdeleRing K) ξ w‖ ^ w.mult < 1 := fun w =>
      pow_lt_one₀ (norm_nonneg _) (h1 w) w.mult_ne_zero
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₀)]
    calc _ ≤ ‖algebraMap K (InfiniteAdeleRing K) ξ w₀‖ ^ w₀.mult * 1 := by
          refine mul_le_mul_of_nonneg_left (Finset.prod_le_one₀ (fun w _ => by positivity) fun w _ => (hf w).le) (by positivity)
      _ < 1 := by rw [mul_one]; exact hf w₀
  have hint : ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) = |((Algebra.norm ℤ n : ℤ) : ℝ)| := by
    rw [← hn, ← Algebra.coe_norm_int]
    push_cast
    rfl
  rw [hint] at hnorm
  have : (1 : ℝ) ≤ |((Algebra.norm ℤ n : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hN
  linarith

/-- Zero lies in `discreteNbhd`. -/
theorem zero_mem_discreteNbhd : (0 : AdeleRing (𝓞 K) K) ∈ discreteNbhd K := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · show ‖(0 : w.Completion)‖ < 1
    rw [norm_zero]; exact one_pos
  · show Valued.v (0 : v.adicCompletion K) ≤ 1
    rw [map_zero]; exact zero_le

/-- The principal idèles are discrete. -/
theorem discrete_principalSubgroup : DiscreteTopology (IdeleGroup.principalSubgroup (𝓞 K) K) := by
  let U : Set (IdeleGroup (𝓞 K) K) := (fun x => (x : AdeleRing (𝓞 K) K)) ⁻¹'
    ((fun y => y - 1) ⁻¹' discreteNbhd K)
  have hU : IsOpen U :=
    (isOpen_discreteNbhd.preimage (continuous_id.sub continuous_const)).preimage Units.continuous_val
  apply discreteTopology_of_isOpen_singleton_one
  have : ({1} : Set (IdeleGroup.principalSubgroup (𝓞 K) K)) = Subtype.val ⁻¹' U := by
    ext ⟨g, ξ, rfl⟩
    constructor
    · intro h
      have : (⟨_, ξ, rfl⟩ : IdeleGroup.principalSubgroup (𝓞 K) K) = 1 := h
      have h1 : IdeleGroup.unitEmbedding (𝓞 K) K ξ = 1 := congrArg Subtype.val this
      show ((IdeleGroup.unitEmbedding (𝓞 K) K ξ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K) - 1 ∈ discreteNbhd K
      rw [h1, Units.val_one, sub_self]
      exact zero_mem_discreteNbhd
    · intro h
      have h' : algebraMap K (AdeleRing (𝓞 K) K) ((ξ : K) - 1) ∈ discreteNbhd K := by
        rw [map_sub, map_one]
        exact h
      have := eq_zero_of_algebraMap_mem_discreteNbhd h'
      have hξ : ξ = 1 := Units.ext (sub_eq_zero.1 this)
      subst hξ
      rfl
  rw [this]
  exact hU.preimage continuous_subtype_val

/-- **4.2** (Milne, *CFT*, V, p. 170): the diagonal map $K^\times \to I_K$ is injective and its image is discrete. -/
@[kb "milne2020cft" "Ch. V, 4.2"]
theorem item_4_2 : Function.Injective (IdeleGroup.unitEmbedding (𝓞 K) K) ∧
    DiscreteTopology (IdeleGroup.principalSubgroup (𝓞 K) K) :=
  ⟨Units.map_injective (AdeleRing.algebraMap_injective (𝓞 K) K), discrete_principalSubgroup⟩

/-- The embedding of `K_v` into the finite adèles is continuous. -/
theorem continuous_ofAdicCompletion_finite (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (FiniteAdeleRing.ofAdicCompletion K v) := by
  classical
  have hS : cofinite ≤ 𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) := by
    rw [le_principal_iff]
    simp
  let g : v.adicCompletion K → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w : HeightOneSpectrum (𝓞 K) => (w.adicCompletionIntegers K : Set (w.adicCompletion K)))
      (𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K)))) :=
    fun x => ⟨Pi.mulSingle v x, fun w hw => by
      show Pi.mulSingle v x w ∈ (w.adicCompletionIntegers K : Set (w.adicCompletion K))
      rw [Pi.mulSingle_eq_of_ne (by simpa using hw)]; exact one_mem _⟩
  have hg : Continuous g := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_mulSingle v
  have : (FiniteAdeleRing.ofAdicCompletion K v : v.adicCompletion K → FiniteAdeleRing (𝓞 K) K) =
      RestrictedProduct.inclusion _ _ hS ∘ g := rfl
  rw [this]
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

/-- The embedding of `K_v` into the adèle ring is a topological embedding. -/
theorem isEmbedding_ofAdicCompletion_adele (v : HeightOneSpectrum (𝓞 K)) :
    IsEmbedding (AdeleRing.ofAdicCompletion (𝓞 K) K v) := by
  refine Function.LeftInverse.isEmbedding (f := fun x : AdeleRing (𝓞 K) K => x.2 v) ?_ ?_ ?_
  · intro x
    classical
    show (Pi.mulSingle v x : Π w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) v = x
    exact Pi.mulSingle_eq_same v x
  · exact (RestrictedProduct.continuous_eval v).comp continuous_snd
  · exact continuous_const.prodMk (continuous_ofAdicCompletion_finite v)

/-- The embedding of `K_w` (at an infinite place) into the adèle ring is a topological embedding. -/
theorem isEmbedding_ofCompletion_adele (w : InfinitePlace K) :
    IsEmbedding (AdeleRing.ofCompletion (𝓞 K) K w) := by
  let _ := Classical.decEq (InfinitePlace K)
  refine Function.LeftInverse.isEmbedding (f := fun x : AdeleRing (𝓞 K) K => x.1 w) ?_ ?_ ?_
  · intro x
    show (Pi.mulSingle w x : InfiniteAdeleRing K) w = x
    exact Pi.mulSingle_eq_same w x
  · exact (continuous_apply w).comp continuous_fst
  · exact (continuous_mulSingle w).prodMk continuous_const

/-- **4.3** (Milne, *CFT*, V, p. 171): for every prime $v$, $K_v^\times \to I_K$ ($a$ in the $v$-th place, $1$ elsewhere)
is injective and induces on $K_v^\times$ its natural topology (a topological embedding). -/
@[kb "milne2020cft" "Ch. V, 4.3"]
theorem item_4_3 : (∀ v : HeightOneSpectrum (𝓞 K),
      Topology.IsEmbedding (IdeleGroup.ofAdicCompletion (𝓞 K) K v)) ∧
    ∀ w : InfinitePlace K, Topology.IsEmbedding (IdeleGroup.ofCompletion (𝓞 K) K w) :=
  ⟨fun v => (isEmbedding_ofAdicCompletion_adele v).units_map,
    fun w => (isEmbedding_ofCompletion_adele w).units_map⟩

/-- Every positive real number is a power (the multiplicity) of the norm of a nonzero element of the completion at
an infinite place. -/
theorem exists_norm_completion (w : InfinitePlace K) (t : ℝ) (ht : 0 < t) :
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
  · have hc := not_isReal_iff_isComplex.1 hw
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

/-- The content $c : I_K \to \mathbb R_{>0}$ is onto. -/
theorem exists_ideleGroupNorm (t : NNReal) (ht : 0 < t) :
    ∃ x : IdeleGroup (𝓞 K) K, Ideles.ideleGroupNorm K x = t := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain ⟨y, hy0, hy⟩ := exists_norm_completion w (t : ℝ) ht
  refine ⟨IdeleGroup.ofCompletion (𝓞 K) K w (Units.mk0 y hy0), ?_⟩
  apply NNReal.coe_injective
  rw [Ideles.coe_ideleGroupNorm, AdeleRing.norm_def]
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

/-- The idèle class group is not compact, since the content maps it continuously onto $(0, \infty)$. -/
theorem not_compactSpace_ideleClassGroup : ¬ CompactSpace (IdeleClassGroup (𝓞 K) K) := by
  intro hc
  let f : IdeleClassGroup (𝓞 K) K →* NNReal :=
    QuotientGroup.lift (IdeleGroup.principalSubgroup (𝓞 K) K) (Ideles.ideleGroupNorm K)
      (fun x hx => Ideles.ideleGroupNorm_eq_one_of_mem_principalSubgroup hx)
  have hf : Continuous f := by
    refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    exact Ideles.continuous_ideleGroupNorm
  have hcl : IsClosed (Set.range f) := (isCompact_range hf).isClosed
  have hr : Set.range f = Set.Ioi 0 := by
    ext t
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      show 0 < Ideles.ideleGroupNorm K x
      rw [pos_iff_ne_zero]
      intro h0
      have h1 : Ideles.ideleGroupNorm K x * Ideles.ideleGroupNorm K x⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      rw [h0, zero_mul] at h1
      exact zero_ne_one h1
    · intro ht
      obtain ⟨x, hx⟩ := exists_ideleGroupNorm (K := K) t ht
      exact ⟨(x : IdeleClassGroup (𝓞 K) K), hx⟩
  rw [hr] at hcl
  have := hcl.closure_eq
  rw [closure_Ioi] at this
  have h0 : (0 : NNReal) ∈ Set.Ici (0 : NNReal) := Set.mem_Ici.2 le_rfl
  rw [this] at h0
  exact lt_irrefl _ (Set.mem_Ioi.1 h0)

/-- **4.4** (Milne, *CFT*, V, p. 171): the content $c(a) = \prod_v|a_v|_v$ (`Ideles.ideleGroupNorm`) maps $I_K$ onto
$\mathbb R_{>0}$; by the product formula $K^\times \subseteq I^1 = \ker c$; $C_K = I_K/K^\times$ is not compact; and
$I^1/K^\times$ is compact (`Ideles.IdeleClassGroup.isCompact_normOne`). -/
@[kb "milne2020cft" "Ch. V, 4.4"]
theorem item_4_4 :
    (∀ t : NNReal, 0 < t → ∃ x : IdeleGroup (𝓞 K) K, Ideles.ideleGroupNorm K x = t) ∧
      IdeleGroup.principalSubgroup (𝓞 K) K ≤ Ideles.ideleGroupOne K ∧
      ¬ CompactSpace (IdeleClassGroup (𝓞 K) K) ∧
      IsCompact (Ideles.IdeleClassGroup.normOne K : Set (IdeleClassGroup (𝓞 K) K)) :=
  ⟨exists_ideleGroupNorm, Ideles.principalSubgroup_le_ideleGroupOne (F := K),
    not_compactSpace_ideleClassGroup, Ideles.IdeleClassGroup.isCompact_normOne⟩

/-- The units $\prod_v\mathcal O_v^\times$ of the finite idèles. -/
def finiteIdeleUnits (K : Type) [Field K] [NumberField K] : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((x : FiniteAdeleRing (𝓞 K) K) v) = 1}
  mul_mem' := by
    intro x y hx hy v
    simp only [Units.val_mul]
    show Valued.v ((x : FiniteAdeleRing (𝓞 K) K) v * (y : FiniteAdeleRing (𝓞 K) K) v) = 1
    rw [map_mul, hx v, hy v, one_mul]
  one_mem' := by
    intro v
    show Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v) = 1
    exact map_one _
  inv_mem' := by
    intro x hx v
    have h := QuadFormsKB.Tamagawa.Measure.Weil.valued_mul_inv x v
    rw [hx v, one_mul] at h
    exact h

/-- **Aside 4.5** (Milne, *CFT*, V, p. 171): in the group $I_f$ of finite idèles, $\prod_v\mathcal O_v^\times$ is open and
compact, and $I_f/\prod_v\mathcal O_v^\times \cong I$ (via $\mathrm{id}$). -/
@[kb "milne2020cft" "Ch. V, Aside 4.5 (finite idèles)"]
theorem aside_4_5 : IsOpen (finiteIdeleUnits K : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ∧
    IsCompact (finiteIdeleUnits K : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ∧
    Function.Surjective (QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal K) ∧
    (QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal K).ker = finiteIdeleUnits K := by
  have heq : finiteIdeleUnits K = QuadFormsKB.Tamagawa.Measure.Weil.OHatUnits K := by
    ext x
    rw [QuadFormsKB.Tamagawa.Measure.Weil.mem_OHatUnits_iff_ordAt]
    exact forall_congr' fun v => (QuadFormsKB.Tamagawa.Measure.Weil.ordAt_eq_zero_iff x v).symm
  rw [heq]
  exact ⟨QuadFormsKB.Tamagawa.Measure.Weil.isOpen_OHatUnits, QuadFormsKB.Tamagawa.Measure.Weil.isCompact_OHatUnits,
    QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal_surjective, QuadFormsKB.Tamagawa.Measure.Weil.ker_ideleIdeal⟩

/-- The diagonal $K^\times \to I_f$ into the finite idèles. -/
def finiteDiag (K : Type) [Field K] [NumberField K] : Kˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).toMonoidHom

/-- A neighbourhood of `1` in the finite adèles contains a box: conditions at finitely many primes, integrality
elsewhere. -/
theorem exists_box {A : Set (FiniteAdeleRing (𝓞 K) K)} (hA : A ∈ 𝓝 (1 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (ε : HeightOneSpectrum (𝓞 K) → WithZero (Multiplicative ℤ)),
      (∀ v, ε v ≠ 0) ∧ ∀ f : FiniteAdeleRing (𝓞 K) K, (∀ v, Valued.v (f v) ≤ 1) →
        (∀ v ∈ S, Valued.v (f v - 1) < ε v) → f ∈ A := by
  classical
  let x : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => ⟨1, one_mem _⟩
  have hcont : Continuous (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have h1 : RestrictedProduct.structureMap _ _ Filter.cofinite x = (1 : FiniteAdeleRing (𝓞 K) K) := rfl
  have hpre := hcont.continuousAt (x := x) |>.preimage_mem_nhds (by rw [h1]; exact hA)
  rw [nhds_pi, Filter.mem_pi] at hpre
  obtain ⟨I, hI, t, ht, hsub⟩ := hpre
  have hε : ∀ v : HeightOneSpectrum (𝓞 K), ∃ ε : WithZero (Multiplicative ℤ), ε ≠ 0 ∧
      ∀ (y : v.adicCompletion K) (hy : y ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))),
        Valued.v (y - 1) < ε → (⟨y, hy⟩ : (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := mem_nhds_subtype _ _ _ |>.1 (ht v)
    have hu' : u ∈ 𝓝 (1 : v.adicCompletion K) := hu
    rw [Valued.mem_nhds] at hu'
    obtain ⟨γ, hγ⟩ := hu'
    refine ⟨MonoidWithZeroHom.ValueGroup₀.embedding γ.1,
      (MonoidWithZeroHom.ValueGroup₀.embedding_unit_pos γ).ne', fun y hy hlt => hut (hγ ?_)⟩
    · show Valued.v.restrict (y - 1) < _
      rw [Valuation.restrict_lt_iff_lt_embedding]
      exact hlt
  choose ε hε0 hεt using hε
  refine ⟨hI.toFinset, ε, hε0, fun f hf hclose => ?_⟩
  have hmem : ∀ v : HeightOneSpectrum (𝓞 K),
      f v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := fun v => by
    show f v ∈ v.adicCompletionIntegers K
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).2 (hf v)
  let x' : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => ⟨f v, hmem v⟩
  have hx' : x' ∈ I.pi t := fun v hv => hεt v (f v) (hmem v) (hclose v (hI.mem_toFinset.2 hv))
  exact hsub hx'

/-- A neighbourhood of `1` in the finite idèles contains a box (conditions on a finite set of primes, for the idèle
and its inverse). -/
theorem exists_box_units {W : Set (FiniteAdeleRing (𝓞 K) K)ˣ} (hW : W ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 K) K)ˣ)) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (ε : HeightOneSpectrum (𝓞 K) → WithZero (Multiplicative ℤ)),
      (∀ v, ε v ≠ 0) ∧ ∀ g : (FiniteAdeleRing (𝓞 K) K)ˣ,
        (∀ v, Valued.v ((g : FiniteAdeleRing (𝓞 K) K) v) ≤ 1) →
        (∀ v, Valued.v (((g⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) ≤ 1) →
        (∀ v ∈ S, Valued.v ((g : FiniteAdeleRing (𝓞 K) K) v - 1) < ε v) →
        (∀ v ∈ S, Valued.v (((g⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v - 1) < ε v) →
        g ∈ W := by
  classical
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨T, hT, hTW⟩ := hW
  rw [map_one, nhds_prod_eq, Filter.mem_prod_iff] at hT
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := hT
  have ht₂' : (MulOpposite.op ⁻¹' t₂ : Set (FiniteAdeleRing (𝓞 K) K)) ∈ 𝓝 (1 : FiniteAdeleRing (𝓞 K) K) := by
    have := MulOpposite.continuous_op.continuousAt (x := (1 : FiniteAdeleRing (𝓞 K) K))
    exact this.preimage_mem_nhds (by rw [MulOpposite.op_one]; exact ht₂)
  obtain ⟨S₁, ε₁, h₁0, h₁⟩ := exists_box ht₁
  obtain ⟨S₂, ε₂, h₂0, h₂⟩ := exists_box ht₂'
  refine ⟨S₁ ∪ S₂, fun v => min (ε₁ v) (ε₂ v), fun v => ?_, fun g hg hg' hc hc' => hTW ?_⟩
  · exact (lt_min (zero_lt_iff.2 (h₁0 v)) (zero_lt_iff.2 (h₂0 v))).ne'
  · refine hsub ⟨?_, ?_⟩
    · exact h₁ _ hg fun v hv => lt_of_lt_of_le (hc v (Finset.mem_union_left _ hv)) (min_le_left _ _)
    · exact h₂ _ hg' fun v hv => lt_of_lt_of_le (hc' v (Finset.mem_union_right _ hv)) (min_le_right _ _)

/-- A finite-index congruence subgroup of the global units. -/
theorem exists_congruence_units (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    ∃ H : Subgroup Kˣ, H ≤ unitsK K ∧ (H.subgroupOf (unitsK K)).FiniteIndex ∧
      ∀ a ∈ H, ∀ v ∈ S, v.valuation K ((a : K) - 1) ≤ WithZero.exp (-(n v : ℤ)) := by
  classical
  let I : Ideal (𝓞 K) := ∏ v ∈ S, v.asIdeal ^ n v
  have hI : I ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ ?_
    exact v.ne_bot
  have : Finite (𝓞 K ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI
  let φ : (𝓞 K)ˣ →* (𝓞 K ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I : 𝓞 K →* 𝓞 K ⧸ I)
  let ψ : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)
  have hψ : Function.Injective ψ := Units.map_injective (IsFractionRing.injective (𝓞 K) K)
  refine ⟨φ.ker.map ψ, ?_, ?_, ?_⟩
  · rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  · rw [← Subgroup.isFiniteRelIndex_iff_finiteIndex, Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
    have : unitsK K = (⊤ : Subgroup (𝓞 K)ˣ).map ψ := by
      rw [Subgroup.map_top]; rfl
    rw [this, Subgroup.relIndex_map_map_of_injective _ _ hψ, Subgroup.relIndex_top_right, Subgroup.index_ker]
    exact Nat.card_pos.ne'
  · rintro _ ⟨u, hu, rfl⟩ v hv
    have h1 : (u : 𝓞 K) - 1 ∈ I := by
      rw [← Ideal.Quotient.eq]
      have := congrArg (fun x : (𝓞 K ⧸ I)ˣ => (x : 𝓞 K ⧸ I)) (MonoidHom.mem_ker.1 hu)
      simpa [φ] using this
    have h2 : (u : 𝓞 K) - 1 ∈ v.asIdeal ^ n v :=
      Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv) h1
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem] at h2
    have : ((ψ u : Kˣ) : K) - 1 = algebraMap (𝓞 K) K ((u : 𝓞 K) - 1) := by
      simp [ψ]
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
    exact h2

/-- The global units are finite iff the group of units of `𝓞 K` is. -/
theorem finite_unitsK_iff_finite_units : Finite (unitsK K) ↔ Finite (𝓞 K)ˣ := by
  have hinj : Function.Injective (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)) :=
    Units.map_injective (IsFractionRing.injective (𝓞 K) K)
  exact (((MonoidHom.ofInjective hinj).toEquiv).finite_iff).symm

/-- Dirichlet: the group of units is finite iff the unit rank is zero. -/
theorem finite_units_iff_rank_eq_zero : Finite (𝓞 K)ˣ ↔ Units.rank K = 0 := by
  constructor
  · intro h
    rw [← Units.finrank_eq]
    rw [Module.finrank_eq_zero_iff]
    intro x
    refine ⟨(orderOf (Additive.toMul x) : ℤ), ?_, ?_⟩
    · exact_mod_cast (orderOf_pos _).ne'
    · rw [natCast_zsmul]
      apply Additive.toMul.injective
      rw [toMul_nsmul, pow_orderOf_eq_one]
      rfl
  · intro h
    have : (Set.univ : Set (𝓞 K)ˣ) ⊆ (Units.torsion K : Set (𝓞 K)ˣ) := by
      intro x _
      obtain ⟨⟨ζ, e⟩, hx, -⟩ := Units.exist_unique_eq_mul_prod K x
      have hemp : IsEmpty (Fin (Units.rank K)) := by rw [h]; infer_instance
      rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at hx
      rw [hx]
      exact ζ.2
    have hfin : (Set.univ : Set (𝓞 K)ˣ).Finite :=
      (Set.finite_coe_iff.1 (inferInstanceAs (Finite (Units.torsion K)))).subset this
    exact Set.finite_univ_iff.1 hfin

/-- The unit group is finite iff `K` is `ℚ` or an imaginary quadratic field. -/
theorem finite_unitsK_iff : Finite (unitsK K) ↔
    Module.finrank ℚ K = 1 ∨ (Module.finrank ℚ K = 2 ∧ nrRealPlaces K = 0) := by
  rw [finite_unitsK_iff_finite_units, finite_units_iff_rank_eq_zero]
  have h1 := card_add_two_mul_card_eq_rank K
  have h2 := card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
  have h3 : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
  unfold Units.rank
  omega

/-- Exponents with `exp (-n) < ε`. -/
theorem exists_exp_neg_lt {ε : WithZero (Multiplicative ℤ)} (hε : ε ≠ 0) :
    ∃ n : ℕ, WithZero.exp (-(n : ℤ)) < ε := by
  refine ⟨(1 - WithZero.log ε).toNat, ?_⟩
  conv_rhs => rw [← WithZero.exp_log hε]
  rw [WithZero.exp_lt_exp]
  have := Int.self_le_toNat (1 - WithZero.log ε)
  omega

/-- A global unit has valuation `1` at every prime, and conversely. -/
theorem mem_unitsK_iff (a : Kˣ) : a ∈ unitsK K ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (a : K) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩ v
    have h1 : v.valuation K (algebraMap (𝓞 K) K (u : 𝓞 K)) ≤ 1 := HeightOneSpectrum.valuation_le_one v _
    have h2 : v.valuation K (algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) ≤ 1 :=
      HeightOneSpectrum.valuation_le_one v _
    have h3 : v.valuation K (algebraMap (𝓞 K) K (u : 𝓞 K)) *
        v.valuation K (algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) = 1 := by
      rw [← map_mul, ← map_mul]; simp
    show v.valuation K (algebraMap (𝓞 K) K (u : 𝓞 K)) = 1
    refine le_antisymm h1 ?_
    by_contra hlt
    rw [not_le] at hlt
    have := mul_lt_one_of_lt_of_le hlt h2
    rw [h3] at this
    exact lt_irrefl _ this
  · intro h
    have ha : (a : K) ∈ (algebraMap (𝓞 K) K).range :=
      HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun v => (h v).le
    have ha' : ((a⁻¹ : Kˣ) : K) ∈ (algebraMap (𝓞 K) K).range :=
      HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun v => by
        rw [Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one]
    obtain ⟨n, hn⟩ := ha
    obtain ⟨m, hm⟩ := ha'
    have hnm : n * m = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_mul, hn, hm, map_one]; simp
    refine ⟨⟨n, m, hnm, by rw [mul_comm]; exact hnm⟩, ?_⟩
    exact Units.ext hn

/-- The valuation of a principal finite idèle at `v` is the valuation of the field element. -/
theorem valued_finiteDiag (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((finiteDiag K a : FiniteAdeleRing (𝓞 K) K) v) = v.valuation K (a : K) :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ _

/-- `U_K` is the preimage of `∏ O_v^×` under the diagonal embedding. -/
theorem mem_unitsK_iff_finiteDiag (a : Kˣ) :
    a ∈ unitsK K ↔ finiteDiag K a ∈ QuadFormsKB.Tamagawa.Measure.Weil.OHatUnits K := by
  rw [QuadFormsKB.Tamagawa.Measure.Weil.mem_OHatUnits_iff_ordAt, mem_unitsK_iff]
  refine forall_congr' fun v => ?_
  rw [QuadFormsKB.Tamagawa.Measure.Weil.ordAt_eq_zero_iff, valued_finiteDiag]

/-- The diagonal embedding of `Kˣ` into the finite idèles is injective. -/
theorem finiteDiag_injective : Function.Injective (finiteDiag K) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  let v : HeightOneSpectrum (𝓞 K) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩
  intro a b h
  have := congrArg (fun g : (FiniteAdeleRing (𝓞 K) K)ˣ => ((g : FiniteAdeleRing (𝓞 K) K) v)) h
  exact Units.ext ((algebraMap K (v.adicCompletion K)).injective this)

/-- **Aside 4.5**, the topology induced on $K^\times$ by the finite idèles (Milne, *CFT*, V, p. 171): $U_K$ is open,
every neighbourhood of $1$ contains a subgroup of $U_K$ of finite index, and $K^\times$ is discrete in $I_f$ iff $U_K$ is
finite iff $K$ is $\mathbb Q$ or an imaginary quadratic field. (That conversely every subgroup of $U_K$ of finite index
is open, Milne's "nontrivial theorem", is not included.) -/
@[kb "milne2020cft" "Ch. V, Aside 4.5 (the topology induced on K^× by I_f)"]
theorem aside_4_5_topology :
    letI : TopologicalSpace Kˣ := TopologicalSpace.induced (finiteDiag K) inferInstance
    IsOpen (unitsK K : Set Kˣ) ∧
      (∀ U ∈ 𝓝 (1 : Kˣ), ∃ H : Subgroup Kˣ, H ≤ unitsK K ∧ (H.subgroupOf (unitsK K)).FiniteIndex ∧
        (H : Set Kˣ) ⊆ U) ∧
      ((DiscreteTopology Kˣ ↔ Finite (unitsK K)) ∧
        (Finite (unitsK K) ↔ Module.finrank ℚ K = 1 ∨ (Module.finrank ℚ K = 2 ∧ nrRealPlaces K = 0))) := by
  let _ : TopologicalSpace Kˣ := TopologicalSpace.induced (finiteDiag K) inferInstance
  have hopen : IsOpen (unitsK K : Set Kˣ) := by
    refine isOpen_induced_iff.2 ⟨(QuadFormsKB.Tamagawa.Measure.Weil.OHatUnits K :
      Set (FiniteAdeleRing (𝓞 K) K)ˣ), QuadFormsKB.Tamagawa.Measure.Weil.isOpen_OHatUnits, ?_⟩
    ext a
    exact (mem_unitsK_iff_finiteDiag a).symm
  have hnbhd : ∀ U ∈ 𝓝 (1 : Kˣ), ∃ H : Subgroup Kˣ, H ≤ unitsK K ∧ (H.subgroupOf (unitsK K)).FiniteIndex ∧
      (H : Set Kˣ) ⊆ U := by
    intro U hU
    rw [nhds_induced, Filter.mem_comap] at hU
    obtain ⟨W, hW, hWU⟩ := hU
    rw [map_one] at hW
    obtain ⟨S, ε, hε0, hbox⟩ := exists_box_units hW
    choose n hn using fun v => exists_exp_neg_lt (hε0 v)
    obtain ⟨H, hHle, hHfin, hHv⟩ := exists_congruence_units S n
    have key : ∀ b ∈ H, (∀ v, Valued.v ((finiteDiag K b : FiniteAdeleRing (𝓞 K) K) v) ≤ 1) ∧
        ∀ v ∈ S, Valued.v ((finiteDiag K b : FiniteAdeleRing (𝓞 K) K) v - 1) < ε v := by
      intro b hb
      refine ⟨fun v => ?_, fun v hv => ?_⟩
      · rw [valued_finiteDiag, (mem_unitsK_iff b).1 (hHle hb) v]
      · have : (finiteDiag K b : FiniteAdeleRing (𝓞 K) K) v - 1 =
            algebraMap K (v.adicCompletion K) ((b : K) - 1) := by
          rw [map_sub, map_one]; rfl
        have e : Valued.v (algebraMap K (v.adicCompletion K) ((b : K) - 1)) = v.valuation K ((b : K) - 1) :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ _
        rw [this, e]
        exact lt_of_le_of_lt (hHv b hb v hv) (hn v)
    refine ⟨H, hHle, hHfin, fun a ha => hWU ?_⟩
    have hinv : (finiteDiag K a)⁻¹ = finiteDiag K a⁻¹ := (map_inv _ a).symm
    refine hbox _ (key a ha).1 ?_ (key a ha).2 ?_
    · rw [hinv]; exact (key a⁻¹ (inv_mem ha)).1
    · rw [hinv]; exact (key a⁻¹ (inv_mem ha)).2
  refine ⟨hopen, hnbhd, ⟨fun hdisc => ?_, fun hfin => ?_⟩, finite_unitsK_iff⟩
  · -- discrete implies finite
    obtain ⟨H, hHle, hHfin, hHsub⟩ := hnbhd {1} (isOpen_discrete _ |>.mem_nhds rfl)
    have hH : H = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      exact hHsub ha
    subst hH
    rw [Subgroup.bot_subgroupOf] at hHfin
    have := hHfin.index_ne_zero
    rw [Subgroup.index_bot] at this
    exact Nat.finite_of_card_ne_zero this
  · -- finite implies discrete
    have hemb : Topology.IsEmbedding (finiteDiag K) := ⟨⟨rfl⟩, finiteDiag_injective⟩
    have : T1Space Kˣ := hemb.t1Space
    have hcont : ∀ x : Kˣ, Continuous (fun y : Kˣ => x⁻¹ * y) := fun x => by
      refine continuous_induced_rng.2 ?_
      have : (finiteDiag K) ∘ (fun y : Kˣ => x⁻¹ * y) = fun y => finiteDiag K x⁻¹ * finiteDiag K y := by
        funext y; simp
      rw [this]
      exact continuous_const.mul continuous_induced_dom
    rw [discreteTopology_iff_isOpen_singleton]
    intro x
    have hP : IsOpen ((fun y : Kˣ => x⁻¹ * y) ⁻¹' (unitsK K : Set Kˣ)) := hopen.preimage (hcont x)
    have hPfin : ((fun y : Kˣ => x⁻¹ * y) ⁻¹' (unitsK K : Set Kˣ)).Finite := by
      have : Finite (unitsK K) := hfin
      refine ((Set.toFinite (unitsK K : Set Kˣ)).image (fun y => x * y)).subset ?_
      intro y hy
      exact ⟨x⁻¹ * y, hy, by simp⟩
    have hx : ({x} : Set Kˣ) = (fun y : Kˣ => x⁻¹ * y) ⁻¹' (unitsK K : Set Kˣ) ∩
        (((fun y : Kˣ => x⁻¹ * y) ⁻¹' (unitsK K : Set Kˣ)) \ {x})ᶜ := by
      ext y
      constructor
      · rintro rfl
        exact ⟨by simp, fun h => h.2 rfl⟩
      · rintro ⟨h1, h2⟩
        by_contra hy
        exact h2 ⟨h1, hy⟩
    rw [hx]
    exact hP.inter (hPfin.sdiff.isClosed.isOpen_compl)

/-- The finite family of absolute values (adic ones at the primes of `S`, archimedean ones at the places of `T`)
used for weak approximation. -/
noncomputable def approxAbv (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K)) :
    S ⊕ T → AbsoluteValue K ℝ :=
  Sum.elim (fun v => HeightOneSpectrum.adicAbv K v.1) (fun w => w.1.1)

/-- The absolute values of `approxAbv` are nontrivial. -/
theorem approx_nontrivial (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (i : S ⊕ T) : (approxAbv S T i).IsNontrivial := by
  rcases i with v | w
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.1.ne_bot
    refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
    · exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hx0
    · have := (FinitePlace.norm_lt_one_iff_mem (K := K) (v := v.1) x).2 hx
      rw [FinitePlace.norm_embedding] at this
      exact this.ne
  · exact w.1.isNontrivial

/-- An adic absolute value is not equivalent to an archimedean one. -/
theorem approx_not_equiv_inl_inr (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    ¬ (HeightOneSpectrum.adicAbv K v).IsEquiv w.1 := by
  intro h
  have h1 := (h.le_one_iff (x := ((2 : ℕ) : K))).1 (HeightOneSpectrum.adicAbv_natCast_le_one K v 2)
  have h2 : w.1 ((2 : ℕ) : K) = 2 := by
    show w ((2 : ℕ) : K) = 2
    rw [← norm_embedding_eq, map_natCast, Complex.norm_natCast]
    norm_num
  rw [h2] at h1
  norm_num at h1

/-- The absolute values of `approxAbv` are pairwise inequivalent. -/
theorem approx_pairwise (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K)) :
    Pairwise fun i j => ¬ (approxAbv S T i).IsEquiv (approxAbv S T j) := by
  rintro (v | w) (v' | w') hne h
  · refine hne (congrArg Sum.inl (Subtype.ext ?_))
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    have h1 := h.lt_one_iff (x := algebraMap (𝓞 K) K x)
    simp only [approxAbv, Sum.elim_inl] at h1
    rw [← FinitePlace.norm_embedding, ← FinitePlace.norm_embedding, FinitePlace.norm_lt_one_iff_mem,
      FinitePlace.norm_lt_one_iff_mem] at h1
    exact h1
  · exact approx_not_equiv_inl_inr v.1 w'.1 h
  · exact approx_not_equiv_inl_inr v'.1 w.1 h.symm
  · refine hne (congrArg Sum.inr (Subtype.ext ?_))
    exact (eq_iff_isEquiv).2 h

/-- **Weak approximation** for finitely many finite and infinite places of a number field: an element of `K`
which is simultaneously `v`-adically close to `c v` for `v ∈ S` (strictly within `δ v`) and within distance `1` of
`q w` at the infinite places `w ∈ T`. -/
theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (c : HeightOneSpectrum (𝓞 K) → K) (δ : HeightOneSpectrum (𝓞 K) → WithZero (Multiplicative ℤ))
    (hδ : ∀ v ∈ S, δ v ≠ 0) (q : InfinitePlace K → K) :
    ∃ b : K, (∀ v ∈ S, v.valuation K (b - c v) < δ v) ∧ ∀ w ∈ T, w (b - q w) < 1 := by
  have hd := AbsoluteValue.denseRange_algebraMap_pi (approx_nontrivial S T) (approx_pairwise S T)
  let z : (i : S ⊕ T) → WithAbs (approxAbv S T i) := fun i =>
    Sum.rec (fun v => WithAbs.toAbs _ (c v.1)) (fun w => WithAbs.toAbs _ (q w.1)) i
  let ε : S ⊕ T → ℝ := Sum.elim (fun v => (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v.1) (δ v.1) : ℝ))
    (fun _ => 1)
  have hU : IsOpen (Set.pi Set.univ fun i => Metric.ball (z i) (ε i)) :=
    isOpen_set_pi Set.finite_univ fun i _ => Metric.isOpen_ball
  have hne : (Set.pi Set.univ fun i => Metric.ball (z i) (ε i)).Nonempty := by
    refine ⟨z, fun i _ => ?_⟩
    rw [Metric.mem_ball, dist_self]
    rcases i with v | w
    · exact_mod_cast WithZeroMulInt.toNNReal_pos _ (hδ v.1 v.2)
    · exact one_pos
  obtain ⟨y, hmem⟩ := hd.exists_mem_open hU hne
  refine ⟨y, fun v hv => ?_, fun w hw => ?_⟩
  · have := hmem (Sum.inl ⟨v, hv⟩) (Set.mem_univ _)
    rw [Metric.mem_ball] at this
    rw [dist_eq_norm] at this
    change HeightOneSpectrum.adicAbv K v (y - c v) <
      ((WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (δ v) : NNReal) : ℝ) at this
    rw [HeightOneSpectrum.adicAbv_def] at this
    exact (WithZeroMulInt.toNNReal_strictMono (HeightOneSpectrum.one_lt_absNorm_nnreal v)).lt_iff_lt.1
      (NNReal.coe_lt_coe.1 this)
  · have := hmem (Sum.inr ⟨w, hw⟩) (Set.mem_univ _)
    rw [Metric.mem_ball, dist_eq_norm] at this
    change w.1 (y - q w) < 1 at this
    exact this

/-! ## Ray class groups as quotients of $I_K$ (pp. 172–173) -/

/-- An element of the completion at a real place is positive (through $K_v \cong \mathbb R$). -/
def IsPosAt (w : InfinitePlace K) (hw : w.IsReal) (x : w.Completion) : Prop :=
  0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x

/-- If `v (a - 1) ≤ γ < 1` then `v a = 1`. -/
theorem val_eq_one_of_sub_one_le {L : Type*} [Field L] (v : Valuation L (WithZero (Multiplicative ℤ))) {a : L} {γ : WithZero (Multiplicative ℤ)} (hγ : γ < 1)
    (ha : v (a - 1) ≤ γ) : v a = 1 := by
  have := Valuation.map_eq_of_sub_lt v (x := 1) (y := a) (by simpa using ha.trans_lt hγ)
  simpa using this

theorem val_mul_sub_one_le {L : Type*} [Field L] (v : Valuation L (WithZero (Multiplicative ℤ))) {a b : L} {γ : WithZero (Multiplicative ℤ)} (hγ : γ < 1)
    (ha : v (a - 1) ≤ γ) (hb : v (b - 1) ≤ γ) : v (a * b - 1) ≤ γ := by
  have hva := val_eq_one_of_sub_one_le v hγ ha
  have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  rw [this]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ha)
  rw [map_mul, hva, one_mul]; exact hb

theorem val_inv_sub_one_le {L : Type*} [Field L] (v : Valuation L (WithZero (Multiplicative ℤ))) {a : L} {γ : WithZero (Multiplicative ℤ)} (hγ : γ < 1)
    (ha : v (a - 1) ≤ γ) : v (a⁻¹ - 1) ≤ γ := by
  have hva := val_eq_one_of_sub_one_le v hγ ha
  have ha0 : a ≠ 0 := by rintro rfl; simp at hva
  have : a⁻¹ - 1 = -((a - 1) * a⁻¹) := by field_simp; ring
  rw [this, Valuation.map_neg, map_mul, map_inv₀, hva]
  simpa using ha

theorem exp_neg_ord_lt_one (m : Modulus K) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ m.finiteSupport) :
    WithZero.exp (-(m.ord v : ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  have := one_le_ord m v hv
  omega

/-- $I_\mathfrak m$ (Milne, *CFT*, V, §4, p. 172): the idèles $(a_\mathfrak p)$ with $a_\mathfrak p \in W_\mathfrak m(\mathfrak p)$
for every $\mathfrak p \mid \mathfrak m$, where $W_\mathfrak m(\mathfrak p) = \mathbb R_{>0}$ for $\mathfrak p$ real and
$1 + \hat{\mathfrak p}^{\mathfrak m(\mathfrak p)}$ for $\mathfrak p$ finite. -/
@[kb "milne2020cft" "Ch. V, §4, p. 172 (the groups W_m(p) and I_m)"]
def idelesMod (m : Modulus K) : Subgroup (IdeleGroup (𝓞 K) K) where
  carrier := {x | (∀ (w : InfinitePlace K) (hw : w ∈ m.infinite), IsPosAt w (m.isReal_of_mem w hw) (ideleInfAt x w)) ∧
    ∀ v ∈ m.finiteSupport, Valued.v (ideleFinAt x v - 1) ≤ WithZero.exp (-(m.ord v : ℤ))}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · have h1 := hx1 w hw
      have h2 := hy1 w hw
      unfold IsPosAt at *
      rw [ideleInfAt_mul, map_mul]
      positivity
    · rw [ideleFinAt_mul]
      exact val_mul_sub_one_le _ (exp_neg_ord_lt_one m v hv) (hx2 v hv) (hy2 v hv)
  one_mem' := by
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · unfold IsPosAt; rw [ideleInfAt_one]; simp
    · rw [ideleFinAt_one]; simp
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · have h1 := hx1 w hw
      unfold IsPosAt at *
      rw [ideleInfAt_inv, map_inv₀]
      positivity
    · rw [ideleFinAt_inv]
      exact val_inv_sub_one_le _ (exp_neg_ord_lt_one m v hv) (hx2 v hv)

/-- $W_\mathfrak m$ (Milne, *CFT*, V, §4, p. 172): the idèles in $I_\mathfrak m$ that are units at every finite prime not
dividing $\mathfrak m$. -/
@[kb "milne2020cft" "Ch. V, §4, p. 172 (the group W_m)"]
def idelesW (m : Modulus K) : Subgroup (IdeleGroup (𝓞 K) K) where
  carrier := {x | x ∈ idelesMod m ∧ ∀ v ∉ m.finiteSupport, Valued.v (ideleFinAt x v) = 1}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨mul_mem hx1 hy1, fun v hv => ?_⟩
    rw [ideleFinAt_mul, map_mul, hx2 v hv, hy2 v hv, one_mul]
  one_mem' := ⟨one_mem _, fun v _ => by rw [ideleFinAt_one]; exact map_one _⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨inv_mem hx1, fun v hv => ?_⟩
    rw [ideleFinAt_inv, map_inv₀, hx2 v hv, inv_one]

theorem ideleInfAt_unitEmbedding (a : Kˣ) (w : InfinitePlace K) :
    ideleInfAt (IdeleGroup.unitEmbedding (𝓞 K) K a) w = ((a : K) : w.Completion) := rfl

theorem ideleFinAt_unitEmbedding_sub_one (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (ideleFinAt (IdeleGroup.unitEmbedding (𝓞 K) K a) v - 1) = v.valuation K ((a : K) - 1) := by
  have : ideleFinAt (IdeleGroup.unitEmbedding (𝓞 K) K a) v - 1 = algebraMap K (v.adicCompletion K) ((a : K) - 1) := by
    rw [map_sub, map_one]; rfl
  rw [this]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ _

/-- $K_{\mathfrak m,1} = K^\times \cap I_\mathfrak m$ (Milne, *CFT*, V, §4, p. 173). -/
@[kb "milne2020cft" "Ch. V, §4, p. 173 (K_{m,1} = K^× ∩ I_m)"]
theorem mem_congruenceSubgroup_iff_mem_idelesMod (m : Modulus K) (a : Kˣ) :
    a ∈ congruenceSubgroup m ↔ IdeleGroup.unitEmbedding (𝓞 K) K a ∈ idelesMod m := by
  refine and_congr (forall_congr' fun w => forall_congr' fun hw => ?_) (forall_congr' fun v => forall_congr' fun hv => ?_)
  · unfold IsPosAt IsPositiveAt
    rw [ideleInfAt_unitEmbedding]
    simp
  · rw [ideleFinAt_unitEmbedding_sub_one]

theorem ideleToIdeal_mem_coprimeIdeals (m : Modulus K) (x : IdeleGroup (𝓞 K) K) (hx : x ∈ idelesMod m) :
    ideleToIdeal K x ∈ coprimeIdeals m := by
  intro v hv
  have h1 := val_eq_one_of_sub_one_le Valued.v (exp_neg_ord_lt_one m v hv) (hx.2 v hv)
  have h2 := QuadFormsKB.Tamagawa.Measure.Weil.count_ideleIdeal
    (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K →+*
      FiniteAdeleRing (𝓞 K) K).toMonoidHom x) v
  have h3 := (QuadFormsKB.Tamagawa.Measure.Weil.ordAt_eq_zero_iff
    (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K →+*
      FiniteAdeleRing (𝓞 K) K).toMonoidHom x) v).2 h1
  exact h2.trans (by rw [h3])

/-- `K` is dense in `K_v`, in terms of the valuation: every element of `K_v` is within `γ` of an element of `K`. -/
theorem exists_close (v : HeightOneSpectrum (𝓞 K)) (a : v.adicCompletion K) (γ : WithZero (Multiplicative ℤ))
    (hγ : γ ≠ 0) : ∃ c : K, Valued.v (algebraMap K (v.adicCompletion K) c - a) < γ := by
  have hd := HeightOneSpectrum.denseRange_algebraMap K v
  have hU : {y : v.adicCompletion K | Valued.v (y - a) < γ} ∈ nhds a := by
    rw [Valued.mem_nhds]
    obtain ⟨x₀, hx₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v γ
    have hx0 : x₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx₀
      exact hγ hx₀.symm
    refine ⟨Units.mk0 (Valued.v.restrict x₀) ?_, fun y hy => ?_⟩
    · rwa [Ne, map_eq_zero]
    · have hy' : Valued.v.restrict (y - a) < Valued.v.restrict x₀ := hy
      rw [Valuation.restrict_lt_iff_lt_embedding, Valuation.embedding_restrict, hx₀] at hy'
      exact hy'
  obtain ⟨_, h1, ⟨c, rfl⟩⟩ := mem_closure_iff_nhds.mp (hd a) _ hU
  exact ⟨c, h1⟩

theorem ideleFinAt_ne_zero (x : IdeleGroup (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) : ideleFinAt x v ≠ 0 := by
  refine left_ne_zero_of_mul_eq_one (b := ideleFinAt x⁻¹ v) ?_
  rw [← ideleFinAt_mul, mul_inv_cancel, ideleFinAt_one]

theorem ideleInfAt_ne_zero (x : IdeleGroup (𝓞 K) K) (w : InfinitePlace K) : ideleInfAt x w ≠ 0 := by
  refine left_ne_zero_of_mul_eq_one (b := ideleInfAt x⁻¹ w) ?_
  rw [← ideleInfAt_mul, mul_inv_cancel, ideleInfAt_one]

theorem ideleFinAt_unitEmbedding (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ideleFinAt (IdeleGroup.unitEmbedding (𝓞 K) K a) v = algebraMap K (v.adicCompletion K) (a : K) := rfl

theorem extEmbedding_coe {w : InfinitePlace K} (hw : w.IsReal) (x : K) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((x : K) : w.Completion) =
      InfinitePlace.embedding_of_isReal hw x := by
  simp

/-- **Weak approximation for idèles**: every idèle can be multiplied by a principal idèle to land in $I_\mathfrak m$. -/
theorem exists_unitEmbedding_mul_mem_idelesMod (m : Modulus K) (a : IdeleGroup (𝓞 K) K) :
    ∃ b : Kˣ, IdeleGroup.unitEmbedding (𝓞 K) K b * a ∈ idelesMod m := by
  classical
  have hS : m.finiteSupport.Finite := Ideal.finite_factors m.finite_ne_bot
  let S := hS.toFinset
  let T := (Set.toFinite m.infinite).toFinset
  let δ : HeightOneSpectrum (𝓞 K) → WithZero (Multiplicative ℤ) := fun v =>
    Valued.v (ideleFinAt a v) * WithZero.exp (-(m.ord v : ℤ))
  have hδ : ∀ v, δ v ≠ 0 := fun v =>
    mul_ne_zero (by rw [Ne, map_eq_zero]; exact ideleFinAt_ne_zero a v) (WithZero.exp_ne_zero)
  choose c hc using fun v => exists_close v (ideleFinAt a v) (δ v) (hδ v)
  let q : InfinitePlace K → K := fun w =>
    if hw : w.IsReal then
      (if 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (ideleInfAt a w) then 1 else -1) else 0
  obtain ⟨b₀, hb1, hb2⟩ := exists_approx S T c δ (fun v _ => hδ v) q
  -- the local statements
  have hA : ∀ v ∈ m.finiteSupport, Valued.v (algebraMap K (v.adicCompletion K) b₀ - ideleFinAt a v) < δ v := by
    intro v hv
    have h1 : Valued.v (algebraMap K (v.adicCompletion K) (b₀ - c v)) < δ v := by
      have e : Valued.v (algebraMap K (v.adicCompletion K) (b₀ - c v)) = v.valuation K (b₀ - c v) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ _
      rw [e]
      exact hb1 v (hS.mem_toFinset.2 hv)
    have : algebraMap K (v.adicCompletion K) b₀ - ideleFinAt a v =
        algebraMap K (v.adicCompletion K) (b₀ - c v) + (algebraMap K (v.adicCompletion K) (c v) - ideleFinAt a v) := by
      rw [map_sub]; ring
    rw [this]
    exact Valuation.map_add_lt _ h1 (hc v)
  have hB : ∀ w (hw : w ∈ m.infinite),
      0 < InfinitePlace.embedding_of_isReal (m.isReal_of_mem w hw) b₀ *
        InfinitePlace.Completion.extensionEmbeddingOfIsReal (m.isReal_of_mem w hw) (ideleInfAt a w) := by
    intro w hw
    have hwr := m.isReal_of_mem w hw
    have h1 := hb2 w ((Set.toFinite m.infinite).mem_toFinset.2 hw)
    have h2 : w (b₀ - q w) = |InfinitePlace.embedding_of_isReal hwr b₀ - InfinitePlace.embedding_of_isReal hwr (q w)| := by
      rw [← InfinitePlace.norm_embedding_of_isReal hwr, map_sub, Real.norm_eq_abs]
    rw [h2, abs_lt] at h1
    have hne := ideleInfAt_ne_zero a w
    have hne' : InfinitePlace.Completion.extensionEmbeddingOfIsReal hwr (ideleInfAt a w) ≠ 0 :=
      (map_ne_zero _).2 hne
    simp only [q, dite_eq_left hwr] at h1
    by_cases hpos : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hwr (ideleInfAt a w)
    · rw [ite_eq_left hpos, map_one] at h1
      exact mul_pos (by linarith [h1.1]) hpos
    · rw [ite_eq_right hpos, map_neg, map_one] at h1
      exact mul_pos_of_neg_of_neg (by linarith [h1.2]) (lt_of_le_of_ne (not_lt.1 hpos) hne')
  have key : ∃ b₁ : K, b₁ ≠ 0 ∧
      (∀ v ∈ m.finiteSupport, Valued.v (algebraMap K (v.adicCompletion K) b₁ - ideleFinAt a v) < δ v) ∧
      ∀ w (hw : w ∈ m.infinite), 0 < InfinitePlace.embedding_of_isReal (m.isReal_of_mem w hw) b₁ *
        InfinitePlace.Completion.extensionEmbeddingOfIsReal (m.isReal_of_mem w hw) (ideleInfAt a w) := by
    by_cases hb : b₀ = 0
    · subst hb
      refine ⟨1, one_ne_zero, fun v hv => absurd (hA v hv) ?_, fun w hw => absurd (hB w hw) ?_⟩
      · rw [map_zero, zero_sub, Valuation.map_neg, not_lt]
        have h0 : Valued.v (ideleFinAt a v) ≠ 0 := by rw [Ne, map_eq_zero]; exact ideleFinAt_ne_zero a v
        have := exp_neg_ord_lt_one m v hv
        calc δ v = Valued.v (ideleFinAt a v) * WithZero.exp (-(m.ord v : ℤ)) := rfl
          _ ≤ Valued.v (ideleFinAt a v) * 1 := mul_le_mul_right this.le _
          _ = _ := mul_one _
      · simp
    · exact ⟨b₀, hb, hA, hB⟩
  obtain ⟨b₁, hb1ne, hA', hB'⟩ := key
  refine ⟨Units.mk0 b₁⁻¹ (inv_ne_zero hb1ne), fun w hw => ?_, fun v hv => ?_⟩
  · have hwr := m.isReal_of_mem w hw
    unfold IsPosAt
    rw [ideleInfAt_mul, ideleInfAt_unitEmbedding, map_mul, extEmbedding_coe]
    have h := hB' w hw
    simp only [Units.val_mk0, map_inv₀]
    have hx : InfinitePlace.embedding_of_isReal hwr b₁ ≠ 0 := by
      rintro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h
    rw [show (InfinitePlace.embedding_of_isReal hwr b₁)⁻¹ *
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hwr (ideleInfAt a w) =
        (InfinitePlace.embedding_of_isReal hwr b₁ *
          InfinitePlace.Completion.extensionEmbeddingOfIsReal hwr (ideleInfAt a w)) *
          ((InfinitePlace.embedding_of_isReal hwr b₁)⁻¹ * (InfinitePlace.embedding_of_isReal hwr b₁)⁻¹) by
      field_simp]
    exact mul_pos h (mul_self_pos.2 (inv_ne_zero hx))
  · have h := hA' v hv
    set α := ideleFinAt a v with hα
    set β := algebraMap K (v.adicCompletion K) b₁ with hβ
    have hα0 : Valued.v α ≠ 0 := by rw [Ne, map_eq_zero]; exact ideleFinAt_ne_zero a v
    have hβ0 : β ≠ 0 := (map_ne_zero _).2 hb1ne
    have he := exp_neg_ord_lt_one m v hv
    have hle : δ v ≤ Valued.v α := by
      calc δ v = Valued.v α * WithZero.exp (-(m.ord v : ℤ)) := rfl
        _ ≤ Valued.v α * 1 := mul_le_mul_right he.le _
        _ = _ := mul_one _
    have hvβ : Valued.v β = Valued.v α := Valuation.map_eq_of_sub_lt _ (h.trans_le hle)
    rw [ideleFinAt_mul, ideleFinAt_unitEmbedding]
    have e1 : algebraMap K (v.adicCompletion K) ((Units.mk0 b₁⁻¹ (inv_ne_zero hb1ne) : Kˣ) : K) * α - 1 =
        β⁻¹ * (α - β) := by
      simp only [Units.val_mk0, map_inv₀]
      rw [← hβ]
      field_simp
    rw [e1, map_mul, map_inv₀, hvβ, Valuation.map_sub_swap]
    calc (Valued.v α)⁻¹ * Valued.v (β - α) ≤ (Valued.v α)⁻¹ * (Valued.v α * WithZero.exp (-(m.ord v : ℤ))) :=
          mul_le_mul_right h.le _
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hα0, one_mul]

/-- The $v$-component of a finite idèle as a homomorphism to the unit group of $K_v$. -/
def unitAtHom (v : HeightOneSpectrum (𝓞 K)) : (FiniteAdeleRing (𝓞 K) K)ˣ →* (v.adicCompletion K)ˣ where
  toFun g := QuadFormsKB.Tamagawa.Measure.Weil.unitAt g v
  map_one' := QuadFormsKB.Tamagawa.Measure.Weil.unitAt_one v
  map_mul' g h := QuadFormsKB.Tamagawa.Measure.Weil.unitAt_mul g h v

/-- **Every ideal prime to $\mathfrak m$ is the ideal of an idèle in $I_\mathfrak m$** (even one that is trivial at the
infinite places and at the primes dividing $\mathfrak m$). -/
theorem exists_mem_idelesMod_ideleToIdeal (m : Modulus K) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hJ : J ∈ coprimeIdeals m) : ∃ x ∈ idelesMod m, ideleToIdeal K x = J := by
  classical
  obtain ⟨z₀, hz₀⟩ := QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal_surjective (F := K) J
  have hS : m.finiteSupport.Finite := Ideal.finite_factors m.finite_ne_bot
  let S := hS.toFinset
  let z : (FiniteAdeleRing (𝓞 K) K)ˣ := z₀ * ∏ v ∈ S, QuadFormsKB.Tamagawa.Measure.Weil.mulSingleAt v
    ((QuadFormsKB.Tamagawa.Measure.Weil.unitAt z₀ v)⁻¹)
  have hz : ∀ v', unitAtHom v' z = unitAtHom v' z₀ * ∏ v ∈ S, unitAtHom v'
      (QuadFormsKB.Tamagawa.Measure.Weil.mulSingleAt v ((QuadFormsKB.Tamagawa.Measure.Weil.unitAt z₀ v)⁻¹)) := by
    intro v'
    simp only [z, map_mul, map_prod]
  have hin : ∀ v' ∈ S, unitAtHom v' z = 1 := by
    intro v' hv'
    rw [hz, Finset.prod_eq_single_of_mem v' hv']
    · show _ * QuadFormsKB.Tamagawa.Measure.Weil.unitAt
        (QuadFormsKB.Tamagawa.Measure.Weil.mulSingleAt v' _) v' = 1
      rw [QuadFormsKB.Tamagawa.Measure.Weil.unitAt_mulSingleAt]
      exact mul_inv_cancel _
    · intro b _ hb
      exact QuadFormsKB.Tamagawa.Measure.Weil.unitAt_mulSingleAt_of_ne (Ne.symm hb) _
  have hout : ∀ v' ∉ S, unitAtHom v' z = unitAtHom v' z₀ := by
    intro v' hv'
    rw [hz, Finset.prod_eq_one, mul_one]
    intro v hv
    exact QuadFormsKB.Tamagawa.Measure.Weil.unitAt_mulSingleAt_of_ne (fun h => hv' (by rw [h]; exact hv)) _
  have hid : QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal K z = J := by
    refine QuadFormsKB.Tamagawa.Measure.Weil.fracIdeal_ext_count fun v' => ?_
    rw [QuadFormsKB.Tamagawa.Measure.Weil.count_ideleIdeal, ← hz₀,
      QuadFormsKB.Tamagawa.Measure.Weil.count_ideleIdeal]
    by_cases hv' : v' ∈ S
    · have h0 : QuadFormsKB.Tamagawa.Measure.Weil.ordAt z₀ v' = 0 := by
        rw [← QuadFormsKB.Tamagawa.Measure.Weil.count_ideleIdeal, hz₀]
        exact hJ v' (hS.mem_toFinset.1 hv')
      rw [h0, QuadFormsKB.Tamagawa.Measure.Weil.ordAt_eq_zero_iff]
      have := congrArg (fun u : (v'.adicCompletion K)ˣ => (u : v'.adicCompletion K)) (hin v' hv')
      simp only [unitAtHom, MonoidHom.coe_mk, OneHom.coe_mk, QuadFormsKB.Tamagawa.Measure.Weil.unitAt_val,
        Units.val_one] at this
      rw [this, map_one]
    · have := congrArg (fun u : (v'.adicCompletion K)ˣ => (u : v'.adicCompletion K)) (hout v' hv')
      simp only [unitAtHom, MonoidHom.coe_mk, OneHom.coe_mk, QuadFormsKB.Tamagawa.Measure.Weil.unitAt_val] at this
      simp only [QuadFormsKB.Tamagawa.Measure.Weil.ordAt, this]
  refine ⟨Units.map (MonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) z, ⟨fun w hw => ?_, fun v hv => ?_⟩, ?_⟩
  · show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (m.isReal_of_mem w hw) 1
    rw [map_one]; exact one_pos
  · have := congrArg (fun u : (v.adicCompletion K)ˣ => (u : v.adicCompletion K)) (hin v (hS.mem_toFinset.2 hv))
    simp only [unitAtHom, MonoidHom.coe_mk, OneHom.coe_mk, QuadFormsKB.Tamagawa.Measure.Weil.unitAt_val,
      Units.val_one] at this
    show Valued.v ((z : FiniteAdeleRing (𝓞 K) K) v - 1) ≤ _
    rw [this, sub_self, map_zero]
    exact zero_le
  · rw [← hid]
    rfl

/-- The map $I_\mathfrak m \to C_\mathfrak m$, $x \mapsto [\mathrm{id}(x)]$. -/
def idelesModToRay (m : Modulus K) : idelesMod m →* RayClassGroup m where
  toFun x := QuotientGroup.mk ⟨ideleToIdeal K x, ideleToIdeal_mem_coprimeIdeals m x x.2⟩
  map_one' := by
    rw [← QuotientGroup.mk_one]
    congr 1
    exact Subtype.ext (map_one _)
  map_mul' := by
    intro x y
    rw [← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (map_mul _ _ _)

/-- **Proposition 4.6(a)** (Milne, *CFT*, V, p. 173): $\mathrm{id} : I_\mathfrak m \to I^{S(\mathfrak m)}$ induces
$I_\mathfrak m/K_{\mathfrak m,1}\cdot W_\mathfrak m \cong C_\mathfrak m$: the map $I_\mathfrak m \to C_\mathfrak m$ is onto with
kernel $K_{\mathfrak m,1}\cdot W_\mathfrak m$. -/
@[kb "milne2020cft" "Ch. V, Proposition 4.6(a)"]
theorem prop_4_6a (m : Modulus K) : Function.Surjective (idelesModToRay m) ∧
    ∀ x : idelesMod m, idelesModToRay m x = 1 ↔
      (x : IdeleGroup (𝓞 K) K) ∈ (congruenceSubgroup m).map (IdeleGroup.unitEmbedding (𝓞 K) K) ⊔ idelesW m := by
  have hW : ∀ z ∈ idelesW m, ideleToIdeal K z = 1 := by
    intro z hz
    refine (item_4_1.2 z).2 fun v => ?_
    by_cases hv : v ∈ m.finiteSupport
    · exact val_eq_one_of_sub_one_le Valued.v (exp_neg_ord_lt_one m v hv) (hz.1.2 v hv)
    · exact hz.2 v hv
  refine ⟨fun g => ?_, fun x => ?_⟩
  · obtain ⟨J, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨x, hx, hxJ⟩ := exists_mem_idelesMod_ideleToIdeal m J.1 J.2
    refine ⟨⟨x, hx⟩, ?_⟩
    show QuotientGroup.mk (⟨ideleToIdeal K x, _⟩ : coprimeIdeals m) = QuotientGroup.mk J
    congr 1
    exact Subtype.ext hxJ
  · have h1 : idelesModToRay m x = 1 ↔ ideleToIdeal K (x : IdeleGroup (𝓞 K) K) ∈ rayPrincipal m := by
      show (QuotientGroup.mk (⟨ideleToIdeal K x, _⟩ : coprimeIdeals m) : RayClassGroup m) = 1 ↔ _
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rw [h1]
    constructor
    · rintro ⟨b, hb, hbx⟩
      have hbm : IdeleGroup.unitEmbedding (𝓞 K) K b ∈ idelesMod m :=
        (mem_congruenceSubgroup_iff_mem_idelesMod m b).1 hb
      have hwm : IdeleGroup.unitEmbedding (𝓞 K) K b⁻¹ * (x : IdeleGroup (𝓞 K) K) ∈ idelesMod m := by
        rw [map_inv]
        exact mul_mem (inv_mem hbm) x.2
      have hw1 : ideleToIdeal K (IdeleGroup.unitEmbedding (𝓞 K) K b⁻¹ * (x : IdeleGroup (𝓞 K) K)) = 1 := by
        rw [map_mul, map_inv, map_inv, ideleToIdeal_unitEmbedding, ← hbx, inv_mul_cancel]
      have hwW : IdeleGroup.unitEmbedding (𝓞 K) K b⁻¹ * (x : IdeleGroup (𝓞 K) K) ∈ idelesW m := by
        refine ⟨hwm, fun v hv => ?_⟩
        exact (item_4_1.2 _).1 hw1 v
      have := Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem (IdeleGroup.unitEmbedding (𝓞 K) K) hb) hwW
      rwa [map_inv, mul_inv_cancel_left] at this
    · intro hx
      obtain ⟨y, ⟨b, hb, rfl⟩, z, hz, hyz⟩ := Subgroup.mem_sup.1 hx
      refine ⟨b, hb, ?_⟩
      rw [← hyz, map_mul, hW z hz, mul_one, ideleToIdeal_unitEmbedding]

/-- **Proposition 4.6(b)** (Milne, *CFT*, V, p. 173): the inclusion $I_\mathfrak m \hookrightarrow I_K$ induces
$I_\mathfrak m/K_{\mathfrak m,1} \cong I_K/K^\times$: the map $I_\mathfrak m \to C_K$ is onto with kernel $K_{\mathfrak m,1}$. -/
@[kb "milne2020cft" "Ch. V, Proposition 4.6(b)"]
theorem prop_4_6b (m : Modulus K) :
    Function.Surjective (fun x : idelesMod m => (x : IdeleClassGroup (𝓞 K) K)) ∧
      ∀ x : idelesMod m, (x : IdeleClassGroup (𝓞 K) K) = 1 ↔
        (x : IdeleGroup (𝓞 K) K) ∈ (congruenceSubgroup m).map (IdeleGroup.unitEmbedding (𝓞 K) K) := by
  refine ⟨fun g => ?_, fun x => ?_⟩
  · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨b, hb⟩ := exists_unitEmbedding_mul_mem_idelesMod m a
    refine ⟨⟨_, hb⟩, ?_⟩
    show (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 K) K b * a) : IdeleClassGroup (𝓞 K) K) = QuotientGroup.mk a
    rw [QuotientGroup.eq]
    exact ⟨b⁻¹, by simp⟩
  · show (QuotientGroup.mk (x : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_, hb⟩
      show b ∈ congruenceSubgroup m
      rw [mem_congruenceSubgroup_iff_mem_idelesMod, hb]
      exact x.2
    · rintro ⟨b, -, hb⟩
      exact ⟨b, hb⟩

end NumberFieldKB.MilneCFT
