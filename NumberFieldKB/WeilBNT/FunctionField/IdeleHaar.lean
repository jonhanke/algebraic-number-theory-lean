import NumberFieldKB.WeilBNT.FunctionField.FourierFF
import NumberFieldKB.WeilBNT.FunctionField.ZetaFinal
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# The Haar measure on the ideles of a function field (Weil VII.§4–§5, characteristic $p$)

$k$ is a global function field with a finite field $\mathbb F_q$ of constants (`Fq`, of order $q$), and
$k_{\mathbb A}^\times$ = `FFIdeleGroup Fq k` its idele group, with the topology of units.

* `FFIdeleGroup.instMeasurableSpace`: the Borel structure of the units topology. (Mathlib's
  `Units.instMeasurableSpace` is the structure pulled back along $z\mapsto z$ from $k_{\mathbb A}$; it is not used
  here, and the instance below takes priority.)
* **`FFIdeleGroup.isCompact_integralUnits`**: $\prod_v\mathfrak r_v^\times$ is a compact open subgroup.
* **`FFIdeleGroup.haarU`**: the Haar measure with $\mu(\prod_v\mathfrak r_v^\times)=1$.
* `Place.countable`: a function field has countably many places (finitely many of each degree), so $D(k)$ is
  countable.
* **`FFIdeleGroup.piD`**: for a divisor $D$, the idele $\pi^D$ with component $\pi_v^{D(v)}$ at $v$, for a fixed prime
  element $\pi_v\in k$ of each $k_v$; `div_piD`: $\operatorname{div}\pi^D=D$, and
  **`FFIdeleGroup.mem_fiber_iff`**: $\operatorname{div}z=D$ iff $(\pi^D)^{-1}z\in\prod_v\mathfrak r_v^\times$. So
  $k_{\mathbb A}^\times$ is the disjoint union of the countably many open cosets $\pi^D\prod_v\mathfrak r_v^\times$.
-/

open MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal

namespace NumberFieldKB.WeilBNT.FF

noncomputable section

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

set_option linter.unusedSectionVars false

namespace FFIdeleGroup

/-- The Borel structure of the units topology on $k_{\mathbb A}^\times$. -/
instance (priority := high) instMeasurableSpace : MeasurableSpace (FFIdeleGroup Fq k) := borel _

instance instBorelSpace : BorelSpace (FFIdeleGroup Fq k) := ⟨rfl⟩

theorem mem_integralUnits_iff (z : FFIdeleGroup Fq k) :
    z ∈ integralUnits ↔ ∀ v : Place Fq k, Valued.v (comp z v) = 1 := by
  constructor
  · intro hz v
    have h := div_eq_zero_of_mem_integralUnits hz
    have hv : v.ordC (comp z v) = 0 := by
      have := congrArg (fun D : Divisor Fq k => D v) h
      simpa using this
    rw [v.valued_eq_exp_neg_ordC (comp_ne_zero z v), hv, neg_zero, WithZero.exp_zero]
  · intro h
    refine ⟨fun v => ?_, fun v => ?_⟩
    · show Valued.v (comp z v) ≤ 1
      rw [h v]
    · show Valued.v (comp z⁻¹ v) ≤ 1
      have hm : Valued.v (comp z v) * Valued.v (comp z⁻¹ v) = 1 := by
        rw [← map_mul, comp_mul_inv, map_one]
      rw [h v, one_mul] at hm
      rw [hm]

theorem mem_integralUnits_iff_div (z : FFIdeleGroup Fq k) : z ∈ integralUnits ↔ div z = 0 := by
  refine ⟨div_eq_zero_of_mem_integralUnits, fun h => (mem_integralUnits_iff z).2 fun v => ?_⟩
  have hv : v.ordC (comp z v) = 0 := by
    have := congrArg (fun D : Divisor Fq k => D v) h
    simpa using this
  rw [v.valued_eq_exp_neg_ordC (comp_ne_zero z v), hv, neg_zero, WithZero.exp_zero]

/-- **$\prod_v\mathfrak r_v^\times$ is compact** in the units topology. -/
theorem isCompact_integralUnits : IsCompact (integralUnits (Fq := Fq) (k := k)) := by
  have hK : IsCompact ((FFAdeleRing.U (0 : Divisor Fq k) : Set (FFAdeleRing Fq k)) ×ˢ
      (MulOpposite.op '' (FFAdeleRing.U (0 : Divisor Fq k) : Set (FFAdeleRing Fq k)))) :=
    FFAdeleRing.isCompact_U_zero.prod (FFAdeleRing.isCompact_U_zero.image MulOpposite.continuous_op)
  have := (Units.isClosedEmbedding_embedProduct (α := FFAdeleRing Fq k)).isCompact_preimage hK
  convert this using 1
  ext z
  simp only [Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, Set.mem_image,
    MulOpposite.op_inj, exists_eq_right, FFAdeleRing.U_zero_eq, Set.mem_ofPred_eq]
  rfl

/-- $\prod_v\mathfrak r_v^\times$ as a positive compact set. -/
def integralUnitsPC : TopologicalSpace.PositiveCompacts (FFIdeleGroup Fq k) :=
  ⟨⟨integralUnits, isCompact_integralUnits⟩, ⟨1, by
    show (1 : FFIdeleGroup Fq k) ∈ interior integralUnits
    rw [isOpen_integralUnits.interior_eq]; exact one_mem_integralUnits⟩⟩

variable (Fq k) in
/-- **The Haar measure on $k_{\mathbb A}^\times$ with $\mu(\prod_v\mathfrak r_v^\times)=1$.** -/
noncomputable def haarU : Measure (FFIdeleGroup Fq k) := Measure.haarMeasure integralUnitsPC

instance : (haarU Fq k).IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _

theorem haarU_integralUnits : haarU Fq k integralUnits = 1 := Measure.haarMeasure_self

/-- A Haar measure gives $\prod_v\mathfrak r_v^\times$ finite positive measure. -/
theorem measure_integralUnits_lt_top (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure] :
    μ integralUnits < ⊤ := isCompact_integralUnits.measure_lt_top

theorem measure_integralUnits_pos (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure] :
    0 < μ integralUnits := isOpen_integralUnits.measure_pos μ ⟨1, one_mem_integralUnits⟩

/-! ### Prime elements and the ideles `π^D` -/

/-- A prime element $\pi_v\in k$ of $k_v$, as a unit of $k_v$. -/
noncomputable def unif (v : Place Fq k) : v.Completionˣ :=
  Units.mk0 (v.toCompletion (v.valuation_surjective (WithZero.exp (-1))).choose) (by
    intro h
    have := Place.valued_toCompletion v (v.valuation_surjective (WithZero.exp (-1))).choose
    rw [h, map_zero, (v.valuation_surjective (WithZero.exp (-1))).choose_spec] at this
    exact WithZero.exp_ne_zero this.symm)

theorem valued_unif (v : Place Fq k) : Valued.v (unif v : v.Completion) = WithZero.exp (-1) := by
  rw [unif, Units.val_mk0, Place.valued_toCompletion,
    (v.valuation_surjective (WithZero.exp (-1))).choose_spec]

theorem valued_unif_zpow (v : Place Fq k) (n : ℤ) :
    Valued.v ((unif v ^ n : v.Completionˣ) : v.Completion) = WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_unif, ← WithZero.exp_zsmul]
  congr 1
  simp

/-- The component map $z\mapsto z_v$ as a monoid morphism. -/
def compHom (v : Place Fq k) : FFIdeleGroup Fq k →* v.Completion where
  toFun z := comp z v
  map_one' := comp_one v
  map_mul' z w := comp_mul z w v

/-- **The idele $\pi^D$** with components $\pi_v^{D(v)}$. -/
noncomputable def piD (D : Divisor Fq k) : FFIdeleGroup Fq k :=
  D.prod fun v n => single v (unif v ^ n)

open Classical in
theorem comp_piD (D : Divisor Fq k) (w : Place Fq k) :
    comp (piD D) w = ((unif w ^ D w : w.Completionˣ) : w.Completion) := by
  have h : comp (piD D) w = ∏ v ∈ D.support, comp (single v (unif v ^ D v)) w := by
    show compHom w (piD D) = _
    rw [piD, Finsupp.prod, map_prod]
    rfl
  rw [h]
  by_cases hw : w ∈ D.support
  · rw [Finset.prod_eq_single w]
    · rw [comp_single_self]
    · intro v _ hvw
      exact comp_single_ne (Ne.symm hvw) _
    · intro h'; exact absurd hw h'
  · rw [Finset.prod_eq_one]
    · rw [Finsupp.notMem_support_iff.1 hw, zpow_zero, Units.val_one]
    · intro v hv
      exact comp_single_ne (by rintro rfl; exact hw hv) _

theorem valued_comp_piD (D : Divisor Fq k) (w : Place Fq k) :
    Valued.v (comp (piD D) w) = WithZero.exp (-D w) := by
  rw [comp_piD, valued_unif_zpow]

theorem div_piD (D : Divisor Fq k) : div (piD D) = D := by
  ext w
  rw [div_apply, Place.ordC, valued_comp_piD, WithZero.log_exp, neg_neg]

/-- **The fibre of the divisor map over $D$ is the coset $\pi^D\prod_v\mathfrak r_v^\times$.** -/
theorem mem_fiber_iff (D : Divisor Fq k) (z : FFIdeleGroup Fq k) :
    div z = D ↔ (piD D)⁻¹ * z ∈ integralUnits := by
  rw [mem_integralUnits_iff_div, div_mul]
  have h1 : div (piD D)⁻¹ = -D := by
    have := div_mul (piD D) (piD D)⁻¹
    rw [mul_inv_cancel, div_one, div_piD] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  rw [h1]
  constructor
  · intro h; rw [h, neg_add_cancel]
  · intro h; exact (neg_add_eq_zero.1 h).symm

theorem isOpen_fiber (D : Divisor Fq k) : IsOpen {z : FFIdeleGroup Fq k | div z = D} := by
  have : {z : FFIdeleGroup Fq k | div z = D} = (fun z => (piD D)⁻¹ * z) ⁻¹' integralUnits := by
    ext z; exact mem_fiber_iff D z
  rw [this]
  exact isOpen_integralUnits.preimage (continuous_const.mul continuous_id)

theorem measurableSet_fiber (D : Divisor Fq k) : MeasurableSet {z : FFIdeleGroup Fq k | div z = D} :=
  (isOpen_fiber D).measurableSet

/-- $z\mapsto\operatorname{div}z$ is locally constant. -/
theorem div_eventually_eq (z : FFIdeleGroup Fq k) : ∀ᶠ w in 𝓝 z, div w = div z :=
  (isOpen_fiber (div z)).mem_nhds rfl

/-- **The idele norm is continuous** (it is locally constant). -/
theorem continuous_norm : Continuous (norm : FFIdeleGroup Fq k → ℝ≥0) := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  refine (continuousAt_const : ContinuousAt (fun _ => norm z) z).congr ?_
  filter_upwards [div_eventually_eq z] with w hw
  rw [norm_eq, norm_eq, hw]

theorem norm_piD (D : Divisor Fq k) : norm (piD D) = (Nat.card Fq : ℝ≥0) ^ (-Divisor.deg D) := by
  rw [norm_eq, div_piD]

end FFIdeleGroup

/-! ### Countably many places -/

section Countable

/-- **A function field has countably many places**: $v\mapsto v$ (the prime divisor) maps the places of degree $n$
into the finite set of effective divisors of degree $n$. -/
theorem Place.countable : Countable (Place Fq k) := by
  have hinj : Function.Injective (fun v : Place Fq k => (Finsupp.single v (1 : ℤ) : Divisor Fq k)) :=
    fun v w h => by
      have := congrArg (fun D : Divisor Fq k => D v) h
      by_contra hvw
      simp [Ne.symm hvw] at this
  have hsub : Set.range (fun v : Place Fq k => (Finsupp.single v (1 : ℤ) : Divisor Fq k)) ⊆
      ⋃ n : ℤ, {a : Divisor Fq k | 0 ≤ a ∧ Divisor.deg a = n} := by
    rintro _ ⟨v, rfl⟩
    exact Set.mem_iUnion.2 ⟨_, Finsupp.single_nonneg.2 zero_le_one, rfl⟩
  have hc : (Set.range (fun v : Place Fq k => (Finsupp.single v (1 : ℤ) : Divisor Fq k))).Countable :=
    (Set.countable_iUnion fun n => (Divisor.finite_setOf_effective_deg_eq n).countable).mono hsub
  have := hc.to_subtype
  exact Function.Injective.countable
    (f := fun v => (⟨_, v, rfl⟩ : Set.range (fun v : Place Fq k => (Finsupp.single v (1 : ℤ) : Divisor Fq k))))
    (fun v w h => hinj (congrArg Subtype.val h))

attribute [instance] Place.countable

instance Divisor.countable : Countable (Divisor Fq k) := inferInstanceAs (Countable (Place Fq k →₀ ℤ))

end Countable

end

end NumberFieldKB.WeilBNT.FF
