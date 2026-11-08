import NumberFieldKB.WeilBNT.FunctionField.Divisor
import NumberFieldKB.WeilBNT.FieldClassification
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Completions and adeles of a global function field (Weil I.§3, III.§1, IV.§1, VI.§1)

For a place $v$ of the global function field $k/\mathbb F_q$:
* **`Place.Completion v`** $=k_v$, Mathlib's `Valuation.Completion` of $k$ at the valuation of $v$ (the uniform
  completion of `WithVal v.valuation`), with its extended valuation; **`Place.completionIntegers v`** $=\mathfrak r_v$
  in $k_v$ (the closed unit ball).
* **`Place.compactSpace_completionIntegers`**: $\mathfrak r_v$ is compact (complete, a discrete valuation ring, finite
  residue field: Mathlib's `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`);
  hence $k_v$ is locally compact (**`Place.locallyCompactSpace`**).
* **`weil_ff_completion_isPField`** (Weil III.§1, characteristic $p$; I.§3 Def. 2): $k_v$ is a $p$-field in Weil's
  sense (`IsPField`, `FieldClassification.lean`), $p$ the characteristic of $\mathbb F_q$.
* **`FFAdeleRing Fq k`** $=k_{\mathbb A}$ (Weil IV.§1 Def. 1): the restricted product of the $k_v$ over **all**
  places with respect to the $\mathfrak r_v$ (Mathlib's `RestrictedProduct`), and the diagonal embedding
  **`FFAdeleRing.diag`** $k\to k_{\mathbb A}$ (well defined by `weil_III_1_thm3_ff`).
-/

open scoped WithZero RestrictedProduct Pointwise
open Valuation IsDedekindDomain

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace Place

variable (v : Place Fq k)

/-- **The completion $k_v$** of $k$ at the place $v$. -/
abbrev Completion : Type _ := v.valuation.Completion

/-- The embedding $k\to k_v$. -/
def toCompletion : k →+* v.Completion :=
  (UniformSpace.Completion.coeRingHom).comp (WithVal.equiv v.valuation).symm.toRingHom

/-- $\mathfrak r_v\subset k_v$, the closed unit ball of the extended valuation. -/
def completionIntegers : ValuationSubring v.Completion := (Valued.v : Valuation v.Completion ℤᵐ⁰).valuationSubring

theorem valued_toCompletion (x : k) : Valued.v (v.toCompletion x) = v.valuation x := by
  exact Valued.valuedCompletion_apply (K := WithVal v.valuation) (WithVal.equiv v.valuation |>.symm x)

theorem valued_surjective : Function.Surjective (Valued.v : Valuation v.Completion ℤᵐ⁰) := fun g => by
  obtain ⟨x, hx⟩ := v.valuation_surjective g
  exact ⟨v.toCompletion x, by rw [valued_toCompletion, hx]⟩

instance : IsCyclic (Valued.v : Valuation v.Completion ℤᵐ⁰).valueGroup := Subgroup.isCyclic _

instance : Nontrivial (Valued.v : Valuation v.Completion ℤᵐ⁰).valueGroup := by
  obtain ⟨x, hx⟩ := v.valued_surjective (WithZero.exp 1)
  have h1 : (WithZero.exp (1 : ℤ)) ≠ 0 := WithZero.exp_ne_zero
  refine ⟨⟨⟨Units.mk0 _ h1, MonoidWithZeroHom.mem_valueGroup _ ⟨x, hx⟩⟩, 1, fun h => ?_⟩⟩
  have := congrArg (fun u : (Valued.v : Valuation v.Completion ℤᵐ⁰).valueGroup => ((u : ℤᵐ⁰ˣ) : ℤᵐ⁰)) h
  simp [← WithZero.exp_zero] at this

instance : (Valued.v : Valuation v.Completion ℤᵐ⁰).IsRankOneDiscrete :=
  Valuation.IsRankOneDiscrete.mk' _

instance : (Valued.v : Valuation v.Completion ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne (Valued.v : Valuation v.Completion ℤᵐ⁰)
    (e := 2) (by norm_num)

theorem mem_completionIntegers_iff {x : v.Completion} :
    x ∈ v.completionIntegers ↔ Valued.v x ≤ 1 := Iff.rfl

instance : IsDiscreteValuationRing (Valued.v : Valuation v.Completion ℤᵐ⁰).integer :=
  Valuation.valuationSubring_isDiscreteValuationRing _

/-- The map $\mathfrak r_v\to\mathcal O[k_v]$. -/
def integersToCompletion : v.integers →+* (Valued.v : Valuation v.Completion ℤᵐ⁰).integer :=
  (v.toCompletion.comp v.integers.subtype).codRestrict _ (fun x => by
    rw [Valuation.mem_integer_iff]
    simp only [RingHom.coe_comp, Function.comp_apply, ValuationSubring.coe_subtype]
    rw [valued_toCompletion]
    exact x.2)

theorem residue_eq_zero_iff_completion (y : (Valued.v : Valuation v.Completion ℤᵐ⁰).integer) :
    IsLocalRing.residue (Valued.v : Valuation v.Completion ℤᵐ⁰).integer y = 0 ↔
      Valued.v (y : v.Completion) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]

theorem residue_eq_iff_completion (y z : (Valued.v : Valuation v.Completion ℤᵐ⁰).integer) :
    IsLocalRing.residue (Valued.v : Valuation v.Completion ℤᵐ⁰).integer y =
      IsLocalRing.residue (Valued.v : Valuation v.Completion ℤᵐ⁰).integer z ↔
      Valued.v ((y : v.Completion) - z) < 1 := by
  rw [← sub_eq_zero, ← _root_.map_sub, residue_eq_zero_iff_completion]
  rfl

/-- The residue field map $\kappa(v)\to$ residue field of $\mathcal O[k_v]$. -/
def resMap : IsLocalRing.ResidueField v.integers →+*
    IsLocalRing.ResidueField (Valued.v : Valuation v.Completion ℤᵐ⁰).integer :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal v.integers)
    ((IsLocalRing.residue (Valued.v : Valuation v.Completion ℤᵐ⁰).integer).comp
      v.integersToCompletion) (by
    intro x hx
    rw [RingHom.comp_apply, residue_eq_zero_iff_completion]
    have hx' := (Valuation.mem_maximalIdeal_iff (v := v.valuation)).1 hx
    show Valued.v (v.toCompletion (x : k)) < 1
    rw [valued_toCompletion]
    exact hx')

theorem resMap_surjective : Function.Surjective v.resMap := by
  have hf : Function.Surjective v.resMap := by
    intro r
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
    have hnhds : {z : v.Completion | Valued.v (z - (y : v.Completion)) < 1} ∈ nhds (y : v.Completion) :=
      Valued.mem_nhds.2 ⟨1, fun z hz => by simpa [Valuation.restrict_lt_iff] using hz⟩
    obtain ⟨a, ha⟩ := (UniformSpace.Completion.denseRange_coe (α := WithVal v.valuation)).mem_nhds hnhds
    set x : k := WithVal.equiv v.valuation a with hx
    have hxa : v.toCompletion x = (a : v.Completion) := rfl
    have hlt : Valued.v (v.toCompletion x - (y : v.Completion)) < 1 := by
      rw [hxa]; exact ha
    have hy : Valued.v (y : v.Completion) ≤ 1 := y.2
    have hxi : x ∈ v.integers := by
      rw [mem_integers_iff, ← valued_toCompletion]
      have : v.toCompletion x = (v.toCompletion x - y) + y := by ring
      rw [this]
      exact (Valuation.map_add_le_max' _ _ _).trans (max_le hlt.le hy)
    refine ⟨Ideal.Quotient.mk _ ⟨x, hxi⟩, ?_⟩
    show IsLocalRing.residue _ (v.integersToCompletion ⟨x, hxi⟩) = IsLocalRing.residue _ y
    rw [residue_eq_iff_completion]
    exact hlt
  exact hf

theorem resMap_injective : Function.Injective v.resMap := (v.resMap).injective

theorem finite_residueField_completion :
    Finite (IsLocalRing.ResidueField (Valued.v : Valuation v.Completion ℤᵐ⁰).integer) :=
  have : Finite (IsLocalRing.ResidueField v.integers) := inferInstanceAs (Finite v.residueField)
  Finite.of_surjective _ v.resMap_surjective

theorem card_residueField_completion :
    Nat.card (IsLocalRing.ResidueField (Valued.v : Valuation v.Completion ℤᵐ⁰).integer) =
      Nat.card Fq ^ v.degree := by
  rw [← Place.card_residueField v]
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨v.resMap_injective, v.resMap_surjective⟩)).symm

/-- **$\mathfrak r_v$ is compact.** -/
instance compactSpace_completionIntegers : CompactSpace v.completionIntegers := by
  have : CompleteSpace (Valued.v : Valuation v.Completion ℤᵐ⁰).integer :=
    (Valued.isClosed_integer v.Completion).completeSpace_coe
  have h := (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := v.Completion) (Γ₀ := ℤᵐ⁰)).2 ⟨inferInstance, inferInstance, finite_residueField_completion v⟩
  have hc : IsCompact ((Valued.v : Valuation v.Completion ℤᵐ⁰).integer : Set v.Completion) :=
    isCompact_iff_compactSpace.2 h
  exact isCompact_iff_compactSpace.1 hc

theorem isCompact_completionIntegers : IsCompact (v.completionIntegers : Set v.Completion) :=
  isCompact_iff_compactSpace.2 (compactSpace_completionIntegers v)

/-- **$k_v$ is locally compact.** -/
instance locallyCompactSpace : LocallyCompactSpace v.Completion :=
  v.isCompact_completionIntegers.locallyCompactSpace_of_mem_nhds_of_addGroup
    ((Valued.isOpen_valuationSubring v.Completion).mem_nhds v.completionIntegers.zero_mem)

theorem lt_one_iff_le_exp_neg_one (g : ℤᵐ⁰) : g < 1 ↔ g ≤ WithZero.exp (-1) := by
  rcases eq_or_ne g 0 with rfl | h
  · simp
  · obtain ⟨n, rfl⟩ : ∃ n : ℤ, g = WithZero.exp n := ⟨WithZero.log g, (WithZero.exp_log h).symm⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem modK_toCompletion_eq {π : k} (hπ : v.valuation π = WithZero.exp (-1)) :
    FieldModule.modK v.Completion (v.toCompletion π) =
      ((Nat.card (IsLocalRing.ResidueField (Valued.v : Valuation v.Completion ℤᵐ⁰).integer) : ℕ) :
        NNReal)⁻¹ := by
  letI : MeasurableSpace v.Completion := borel _
  haveI : BorelSpace v.Completion := ⟨rfl⟩
  set O : Set v.Completion := (v.completionIntegers : Set v.Completion) with hO
  have hOopen : IsOpen O := Valued.isOpen_valuationSubring v.Completion
  let K₀ : TopologicalSpace.PositiveCompacts v.Completion :=
    ⟨⟨O, v.isCompact_completionIntegers⟩, ⟨0, by
      show (0 : v.Completion) ∈ interior O
      rw [hOopen.interior_eq]; exact v.completionIntegers.zero_mem⟩⟩
  let μ := MeasureTheory.Measure.addHaarMeasure K₀
  have hμ1 : μ O = 1 := MeasureTheory.Measure.addHaarMeasure_self
  set p := v.toCompletion π with hp
  have hpv : Valued.v p = WithZero.exp (-1) := by rw [hp, valued_toCompletion, hπ]
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, map_zero] at hpv
    exact WithZero.exp_ne_zero hpv.symm
  set B : Set v.Completion := {z | Valued.v z < 1} with hB
  have hBopen : IsOpen B := by
    have := Valued.isOpen_ball v.Completion (1 : (Valued.v : Valuation v.Completion ℤᵐ⁰).ValueGroup₀)
    simpa [Valuation.restrict_lt_iff] using this
  have hpO : p • O = B := by
    ext z
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show Valued.v (p * y) < 1
      rw [map_mul, hpv]
      have hy' : Valued.v y ≤ 1 := hy
      calc WithZero.exp (-1 : ℤ) * Valued.v y ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
        _ < 1 := by rw [mul_one, lt_one_iff_le_exp_neg_one]
    · intro hz
      refine ⟨z / p, ?_, by rw [smul_eq_mul]; field_simp⟩
      show Valued.v (z / p) ≤ 1
      rw [map_div₀, hpv]
      exact div_le_one_of_le₀ ((lt_one_iff_le_exp_neg_one _).1 hz) zero_le
  -- coset decomposition of `O`
  have : Fintype (IsLocalRing.ResidueField (Valued.v : Valuation v.Completion ℤᵐ⁰).integer) :=
    @Fintype.ofFinite _ (finite_residueField_completion v)
  let res := IsLocalRing.residue (Valued.v : Valuation v.Completion ℤᵐ⁰).integer
  let r := Function.surjInv (IsLocalRing.residue_surjective (R := (Valued.v : Valuation v.Completion ℤᵐ⁰).integer))
  have hr : ∀ q, res (r q) = q := Function.surjInv_eq _
  let A : IsLocalRing.ResidueField (Valued.v : Valuation v.Completion ℤᵐ⁰).integer →
      Set v.Completion := fun q => (fun z => z + (-(r q : v.Completion))) ⁻¹' B
  have hAmeas : ∀ q, MeasurableSet (A q) := fun q =>
    (hBopen.preimage (continuous_id.add continuous_const)).measurableSet
  have hAB : ∀ q, μ (A q) = μ B := fun q =>
    MeasureTheory.measure_preimage_add_right μ _ B
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    apply hqq'
    have h1 : Valued.v (z + -(r q : v.Completion)) < 1 := hz
    have h2 : Valued.v (z + -(r q' : v.Completion)) < 1 := hz'
    have h3 : Valued.v ((r q : v.Completion) - (r q' : v.Completion)) < 1 := by
      have : (r q : v.Completion) - (r q' : v.Completion) =
          (z + -(r q' : v.Completion)) - (z + -(r q : v.Completion)) := by ring
      rw [this]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h2 h1)
    have := (residue_eq_iff_completion v (r q) (r q')).2 h3
    rw [← hr q, ← hr q']
    exact this
  have hunion : O = ⋃ q, A q := by
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · intro hz
      refine ⟨res ⟨z, hz⟩, ?_⟩
      show Valued.v (z + -(r (res ⟨z, hz⟩) : v.Completion)) < 1
      have := (residue_eq_iff_completion v ⟨z, hz⟩ (r (res ⟨z, hz⟩))).1 (by rw [hr])
      simpa [sub_eq_add_neg] using this
    · rintro ⟨q, hq⟩
      have h1 : Valued.v (z + -(r q : v.Completion)) < 1 := hq
      have h2 : Valued.v (r q : v.Completion) ≤ 1 := (r q).2
      show Valued.v z ≤ 1
      have : z = (z + -(r q : v.Completion)) + r q := by ring
      rw [this]
      exact (Valuation.map_add_le_max' _ _ _).trans (max_le h1.le h2)
  have hmeasO : μ O = (Nat.card (IsLocalRing.ResidueField
      (Valued.v : Valuation v.Completion ℤᵐ⁰).integer) : ENNReal) * μ B := by
    rw [hunion, MeasureTheory.measure_iUnion hdisj hAmeas, tsum_fintype]
    simp only [hAB, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hmod := FieldModule.modK_mul_measure μ hp0 O
  rw [hpO, hμ1, mul_one] at hmod
  rw [hμ1, ← hmod] at hmeasO
  -- hmeasO : 1 = card * modK p
  have h2 : ((Nat.card (IsLocalRing.ResidueField
      (Valued.v : Valuation v.Completion ℤᵐ⁰).integer) : NNReal) * FieldModule.modK v.Completion p : NNReal)
      = 1 := by
    have : (((Nat.card (IsLocalRing.ResidueField
      (Valued.v : Valuation v.Completion ℤᵐ⁰).integer) : NNReal) *
        FieldModule.modK v.Completion p : NNReal) : ENNReal) = 1 := by
      push_cast
      exact hmeasO.symm
    exact_mod_cast this
  exact eq_inv_of_mul_eq_one_right h2

end Place

/-- **Weil III.§1** (characteristic $p$): the completion of a global function field at a place is a $p$-field
(Weil I.§3 Def. 2: a nondiscrete locally compact field with $|p|<1$ for the module), $p=\operatorname{char}\mathbb F_q$. -/
@[kb "weil1973bnt" "Ch. III, §1, text p. 43-44 (completions of an A-field of characteristic p are p-fields)"]
theorem weil_ff_completion_isPField (v : Place Fq k) :
    FieldModule.IsPField v.Completion (ringChar Fq) ∧ (nhdsWithin (0 : v.Completion) {0}ᶜ).NeBot := by
  refine ⟨⟨CharP.char_is_prime Fq (ringChar Fq), ?_⟩, ?_⟩
  · have h0 : ((ringChar Fq : ℕ) : k) = 0 := by
      rw [← map_natCast (algebraMap Fq k), ringChar.Nat.cast_ringChar, map_zero]
    rw [← map_natCast v.toCompletion, h0, map_zero, FieldModule.modK_zero]
    exact one_pos
  · obtain ⟨π, hπ⟩ := v.valuation_surjective (WithZero.exp (-1))
    have hπ0 : v.toCompletion π ≠ 0 := by
      intro h
      have := Place.valued_toCompletion v π
      rw [h, map_zero, hπ] at this
      exact WithZero.exp_ne_zero this.symm.symm.symm
    have ht : Filter.Tendsto (fun n : ℕ => v.toCompletion π ^ n) Filter.atTop
        (nhdsWithin (0 : v.Completion) {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
      · exact Valued.tendsto_zero_pow_of_le_exp_neg_one (by rw [Place.valued_toCompletion, hπ])
      · exact pow_ne_zero n hπ0
    exact ht.neBot

/-- **Weil VI.§1, text p. 96**: the module of $k_v$ is $q_v=q^{\deg v}$: a prime element $\pi$ (with $v(\pi)=e^{-1}$)
has $\operatorname{mod}_{k_v}(\pi)=q^{-\deg v}$. -/
@[kb "weil1973bnt" "Ch. VI, §1, text p. 96 (the module of k_v is q^deg v)"]
theorem weil_VI_1_text96_modK (v : Place Fq k) {π : k} (hπ : v.valuation π = WithZero.exp (-1)) :
    FieldModule.modK v.Completion (v.toCompletion π) = ((Nat.card Fq : NNReal) ^ v.degree)⁻¹ := by
  rw [Place.modK_toCompletion_eq v hπ, Place.card_residueField_completion v]
  push_cast
  rfl

variable (Fq k) in
/-- **The adele ring $k_{\mathbb A}$** of the global function field $k$ (Weil IV.§1 Def. 1): the restricted product
of the completions $k_v$ over all places with respect to the compact open subrings $\mathfrak r_v$. -/
abbrev FFAdeleRing : Type _ :=
  Πʳ v : Place Fq k, [v.Completion, (v.completionIntegers : Set v.Completion)]

namespace FFAdeleRing

/-- The diagonal embedding $k\to k_{\mathbb A}$: $\xi\in\mathfrak r_v$ for almost all $v$. -/
def diag (x : k) : FFAdeleRing Fq k :=
  ⟨fun v => v.toCompletion x, by
    rcases eq_or_ne x 0 with rfl | hx
    · exact Filter.Eventually.of_forall fun v => by simp
    · have h := Filter.eventually_cofinite.2 (Place.weil_III_1_thm3_ff (Fq := Fq) hx)
      filter_upwards [h] with v hv
      show Valued.v (v.toCompletion x) ≤ 1
      rw [Place.valued_toCompletion]
      have h1 : v.valuation x = 1 := by simpa using hv
      exact h1.le⟩

end FFAdeleRing

end NumberFieldKB.WeilBNT.FF
