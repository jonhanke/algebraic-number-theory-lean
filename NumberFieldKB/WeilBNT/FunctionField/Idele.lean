import NumberFieldKB.WeilBNT.FunctionField.Completion
import NumberFieldKB.WeilBNT.FunctionField.ProductFormula
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Mathlib.Topology.Algebra.Group.Units

/-!
# Ideles of a global function field (Weil IV.§3–§4, VI.§1)

For a global function field $k$ over a finite field $\mathbb F_q$ (`Fq`, any finite subfield; $q=\lvert\mathbb F_q\rvert$):

* `Place.modK_completion`: the module of $k_v$ (Weil I.§2) is $\operatorname{mod}_{k_v}(x)=q^{-\deg(v)\,n}$ when
  $\operatorname{ord}_v(x)=n$ (Weil VI.§1, text p. 96; `weil_VI_1_text96_modK` is the case $n=1$);
* `FFIdeleGroup`: the idele group $k_{\mathbb A}^\times$, the units of the adele ring `FFAdeleRing` (Weil IV.§3);
* `FFIdeleGroup.div`: the divisor $\operatorname{div}(z)=\sum_v\operatorname{ord}_v(z_v)\,v$ of an idele (Weil VI.§1,
  text p. 97), a surjective morphism onto the divisor group;
* `FFIdeleGroup.norm`: $\lvert z\rvert_{\mathbb A}=\prod_v\operatorname{mod}_{k_v}(z_v)$ (Weil IV.§3, Def. after
  Prop. 3), and **`FFIdeleGroup.norm_eq`**: $\lvert z\rvert_{\mathbb A}=q^{-\deg\operatorname{div}(z)}$;
* `FFIdeleGroup.div_diag`, `FFIdeleGroup.norm_diag`: principal ideles have the principal divisor and norm $1$
  (Artin's product formula, Weil IV.§4 Thm. 5, function-field case, from `Divisor.deg_div_eq_zero`).
-/

open scoped WithZero RestrictedProduct Pointwise NNReal
open Valuation IsDedekindDomain Topology MeasureTheory

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace Place

/-- $k$ is dense in its completion $k_v$. -/
theorem denseRange_toCompletion {Fq k : Type*} [Field Fq] [Field k] [Algebra Fq k] (v : Place Fq k) :
    DenseRange v.toCompletion := by
  exact (UniformSpace.Completion.denseRange_coe).comp
    (WithVal.equiv v.valuation).symm.surjective.denseRange (UniformSpace.Completion.continuous_coe _)

variable (v : Place Fq k)

instance neBot_completion : (𝓝[≠] (0 : v.Completion)).NeBot := (weil_ff_completion_isPField v).2

/-- The order $\operatorname{ord}_v(x)=-\log v(x)$ of an element of the completion $k_v$. -/
def ordC (x : v.Completion) : ℤ := -WithZero.log (Valued.v x)

theorem ordC_toCompletion (x : k) : v.ordC (v.toCompletion x) = v.ord x := by
  rw [ordC, Place.ord, valued_toCompletion]

theorem valued_eq_exp_neg_ordC {x : v.Completion} (hx : x ≠ 0) :
    Valued.v x = WithZero.exp (-v.ordC x) := by
  rw [ordC, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)]

theorem ordC_mul {x y : v.Completion} (hx : x ≠ 0) (hy : y ≠ 0) :
    v.ordC (x * y) = v.ordC x + v.ordC y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  simp only [ordC, map_mul, WithZero.log_mul hx' hy']
  ring

/-- A unit of the valuation ring has module $1$. -/
theorem modK_eq_one_of_valued_eq_one {u : v.Completion} (hu : Valued.v u = 1) :
    FieldModule.modK v.Completion u = 1 := by
  let _ : MeasurableSpace v.Completion := borel _
  have : BorelSpace v.Completion := ⟨rfl⟩
  set O : Set v.Completion := (v.completionIntegers : Set v.Completion) with hO
  have hOopen : IsOpen O := Valued.isOpen_valuationSubring v.Completion
  let K₀ : TopologicalSpace.PositiveCompacts v.Completion :=
    ⟨⟨O, v.isCompact_completionIntegers⟩, ⟨0, by
      show (0 : v.Completion) ∈ interior O
      rw [hOopen.interior_eq]; exact v.completionIntegers.zero_mem⟩⟩
  let μ := MeasureTheory.Measure.addHaarMeasure K₀
  have hμ1 : μ O = 1 := MeasureTheory.Measure.addHaarMeasure_self
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hu; exact zero_ne_one hu
  have huO : u • O = O := by
    ext z
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show Valued.v (u * y) ≤ 1
      rw [map_mul, hu, one_mul]; exact hy
    · intro hz
      refine ⟨z / u, ?_, by rw [smul_eq_mul]; field_simp⟩
      show Valued.v (z / u) ≤ 1
      rw [map_div₀, hu, div_one]; exact hz
  have h := FieldModule.modK_mul_measure μ hu0 O
  rw [huO, hμ1, mul_one] at h
  exact_mod_cast h

/-- **Weil VI.§1, text p. 96**: if $\operatorname{ord}_v(x)=n$ then $\operatorname{mod}_{k_v}(x)=(q^{\deg v})^{-n}$. -/
theorem modK_completion {x : v.Completion} {n : ℤ} (hx : Valued.v x = WithZero.exp (-n)) :
    FieldModule.modK v.Completion x = ((Nat.card Fq : ℝ≥0) ^ v.degree) ^ (-n) := by
  obtain ⟨π, hπ⟩ := v.valuation_surjective (WithZero.exp (-1))
  set p := v.toCompletion π with hp
  have hpv : Valued.v p = WithZero.exp (-1) := by rw [hp, valued_toCompletion, hπ]
  have hp0 : p ≠ 0 := by
    intro h; rw [h, map_zero] at hpv; exact WithZero.exp_ne_zero hpv.symm
  have hmodp := weil_VI_1_text96_modK v hπ
  rw [← hp] at hmodp
  have hx0 : x ≠ 0 := by
    intro h; rw [h, map_zero] at hx; exact WithZero.exp_ne_zero hx.symm
  set u := x * (p ^ n)⁻¹ with hu
  have huv : Valued.v u = 1 := by
    rw [hu, map_mul, map_inv₀, map_zpow₀, hpv, hx, ← WithZero.exp_zsmul, ← WithZero.exp_neg,
      ← WithZero.exp_add]
    simp
  have hxu : x = u * p ^ n := by
    rw [hu, mul_assoc, inv_mul_cancel₀ (zpow_ne_zero n hp0), mul_one]
  have hmodpow : ∀ m : ℤ, FieldModule.modK v.Completion (p ^ m) =
      (FieldModule.modK v.Completion p) ^ m := by
    intro m
    rcases Int.eq_nat_or_neg m with ⟨j, rfl | rfl⟩
    · simp [zpow_natCast, FieldModule.modK_pow]
    · rw [zpow_neg, zpow_natCast, FieldModule.modK_inv (pow_ne_zero j hp0), FieldModule.modK_pow,
        zpow_neg, zpow_natCast]
  rw [hxu, FieldModule.modK_mul, modK_eq_one_of_valued_eq_one v huv, one_mul, hmodpow, hmodp,
    inv_zpow', zpow_neg]

end Place

/-- The rings $\mathfrak r_v$ are open in $k_v$ (needed for the topological ring structure of $k_{\mathbb A}$). -/
instance FFAdeleRing.fact_isOpen :
    Fact (∀ v : Place Fq k, IsOpen (v.completionIntegers : Set v.Completion)) :=
  ⟨fun v => Valued.isOpen_valuationSubring v.Completion⟩

example : IsTopologicalRing (FFAdeleRing Fq k) := inferInstance

example : IsTopologicalGroup (FFAdeleRing Fq k)ˣ := inferInstance

variable (Fq k) in
/-- **The idele group $k_{\mathbb A}^\times$** of the global function field $k$ (Weil IV.§3): the invertible elements
of the adele ring $k_{\mathbb A}$, with the topology of units (the topology of $z\mapsto(z,z^{-1})$). -/
abbrev FFIdeleGroup : Type _ := (FFAdeleRing Fq k)ˣ

namespace FFIdeleGroup

/-- The component $z_v\in k_v$ of an idele. -/
def comp (z : FFIdeleGroup Fq k) (v : Place Fq k) : v.Completion := (z : FFAdeleRing Fq k) v

theorem comp_mul (z w : FFIdeleGroup Fq k) (v : Place Fq k) : comp (z * w) v = comp z v * comp w v := rfl

theorem comp_one (v : Place Fq k) : comp (1 : FFIdeleGroup Fq k) v = 1 := rfl

theorem comp_mul_inv (z : FFIdeleGroup Fq k) (v : Place Fq k) : comp z v * comp z⁻¹ v = 1 := by
  rw [← comp_mul, mul_inv_cancel, comp_one]

theorem comp_ne_zero (z : FFIdeleGroup Fq k) (v : Place Fq k) : comp z v ≠ 0 := by
  intro h
  have := comp_mul_inv z v
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- For almost all $v$, $z_v$ is a unit of $\mathfrak r_v$, i.e. $v(z_v)=1$. -/
theorem eventually_valued_eq_one (z : FFIdeleGroup Fq k) :
    ∀ᶠ v in Filter.cofinite, Valued.v (comp z v) = 1 := by
  filter_upwards [(z : FFAdeleRing Fq k).2, (z⁻¹ : FFIdeleGroup Fq k).val.2] with v h1 h2
  have h1' : Valued.v (comp z v) ≤ 1 := h1
  have h2' : Valued.v (comp z⁻¹ v) ≤ 1 := h2
  have hm : Valued.v (comp z v) * Valued.v (comp z⁻¹ v) = 1 := by
    rw [← map_mul, comp_mul_inv, map_one]
  by_contra hne
  have hlt : Valued.v (comp z v) < 1 := lt_of_le_of_ne h1' hne
  have : Valued.v (comp z v) * Valued.v (comp z⁻¹ v) < 1 :=
    lt_of_lt_of_le (mul_lt_one_of_lt_of_le hlt h2') le_rfl
  rw [hm] at this
  exact lt_irrefl _ this

theorem finite_support (z : FFIdeleGroup Fq k) : {v : Place Fq k | v.ordC (comp z v) ≠ 0}.Finite := by
  refine (Filter.eventually_cofinite.1 (eventually_valued_eq_one z)).subset ?_
  intro v hv h1
  apply hv
  simp [Place.ordC, h1]

/-- **The divisor of an idele** (Weil VI.§1, text p. 97): $\operatorname{div}(z)=\sum_v\operatorname{ord}_v(z_v)\,v$. -/
def div (z : FFIdeleGroup Fq k) : Divisor Fq k :=
  Finsupp.ofSupportFinite (fun v => v.ordC (comp z v)) (finite_support z)

@[simp] theorem div_apply (z : FFIdeleGroup Fq k) (v : Place Fq k) : div z v = v.ordC (comp z v) := rfl

theorem div_mul (z w : FFIdeleGroup Fq k) : div (z * w) = div z + div w := by
  ext v
  simp only [div_apply, Finsupp.add_apply, comp_mul]
  exact v.ordC_mul (comp_ne_zero z v) (comp_ne_zero w v)

theorem div_one : div (1 : FFIdeleGroup Fq k) = 0 := by
  ext v
  simp [comp_one, Place.ordC]

/-- The divisor map as a morphism $k_{\mathbb A}^\times\to D(k)$ (written multiplicatively on the target). -/
def divHom : FFIdeleGroup Fq k →* Multiplicative (Divisor Fq k) where
  toFun z := Multiplicative.ofAdd (div z)
  map_one' := by simp [div_one]
  map_mul' z w := by simp [div_mul]

open Classical in
/-- The idele with component $x\in k_v^\times$ at $v$ and $1$ elsewhere. -/
def single (v : Place Fq k) (x : v.Completionˣ) : FFIdeleGroup Fq k :=
  RestrictedProduct.mkUnit (fun w => if h : w = v then h ▸ x else 1) (by
    filter_upwards [Set.Finite.compl_mem_cofinite (Set.finite_singleton v)] with w hw
    have hw' : w ≠ v := hw
    simp only [hw', dite_false]
    exact (Submonoid.ofClass _).units.one_mem)

open Classical in
theorem comp_single_self (v : Place Fq k) (x : v.Completionˣ) : comp (single v x) v = x := by
  simp [comp, single, RestrictedProduct.mkUnit]

open Classical in
theorem comp_single_ne {v w : Place Fq k} (h : w ≠ v) (x : v.Completionˣ) : comp (single v x) w = 1 := by
  simp [comp, single, RestrictedProduct.mkUnit, h]

theorem div_single (v : Place Fq k) (x : v.Completionˣ) :
    div (single v x) = Finsupp.single v (v.ordC (x : v.Completion)) := by
  ext w
  by_cases h : w = v
  · subst h; simp [comp_single_self]
  · simp [comp_single_ne h, Place.ordC, Finsupp.single_apply, Ne.symm h]

/-- The divisor map is surjective: a prime element at $v$ gives $\operatorname{div}=v$. -/
theorem div_surjective : Function.Surjective (div : FFIdeleGroup Fq k → Divisor Fq k) := by
  have hv : ∀ v : Place Fq k, ∃ z : FFIdeleGroup Fq k, div z = Finsupp.single v 1 := by
    intro v
    obtain ⟨π, hπ⟩ := v.valuation_surjective (WithZero.exp (-1))
    have hπ0 : v.toCompletion π ≠ 0 := by
      intro h
      have := Place.valued_toCompletion v π
      rw [h, map_zero, hπ] at this
      exact WithZero.exp_ne_zero this.symm
    refine ⟨single v (Units.mk0 _ hπ0), ?_⟩
    rw [div_single]
    congr 1
    simp [Place.ordC, Place.valued_toCompletion, hπ]
  intro a
  induction a using Finsupp.induction_linear with
  | zero => exact ⟨1, div_one⟩
  | add a b ha hb =>
    obtain ⟨z, rfl⟩ := ha
    obtain ⟨w, rfl⟩ := hb
    exact ⟨z * w, div_mul z w⟩
  | single v n =>
    obtain ⟨z, hz⟩ := hv v
    refine ⟨z ^ n, ?_⟩
    have : div (z ^ n) = n • div z := by
      have := map_zpow (divHom (Fq := Fq) (k := k)) z n
      simpa [divHom] using congrArg Multiplicative.toAdd this
    rw [this, hz, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The degree of the divisor of an idele, $z\mapsto\deg\operatorname{div}(z)$, a morphism to $\mathbb Z$. -/
def degHom : FFIdeleGroup Fq k →* Multiplicative ℤ where
  toFun z := Multiplicative.ofAdd (Divisor.deg (div z))
  map_one' := by simp [div_one]
  map_mul' z w := by simp [div_mul]

theorem deg_div_zpow (z : FFIdeleGroup Fq k) (n : ℤ) :
    Divisor.deg (div (z ^ n)) = n * Divisor.deg (div z) := by
  have := map_zpow (degHom (Fq := Fq) (k := k)) z n
  simpa [degHom] using congrArg Multiplicative.toAdd this

theorem deg_div_inv (z : FFIdeleGroup Fq k) : Divisor.deg (div z⁻¹) = -Divisor.deg (div z) := by
  have h := div_mul z z⁻¹
  rw [mul_inv_cancel, div_one] at h
  have := congrArg Divisor.deg h
  rw [map_zero, map_add] at this
  omega

/-- **The norm of an idele** (Weil IV.§3, after Prop. 3; IV.§4): $\lvert z\rvert_{\mathbb A}=\prod_v
\operatorname{mod}_{k_v}(z_v)$, a finite product. -/
def norm (z : FFIdeleGroup Fq k) : ℝ≥0 := ∏ᶠ v : Place Fq k, FieldModule.modK v.Completion (comp z v)

theorem modK_comp (z : FFIdeleGroup Fq k) (v : Place Fq k) :
    FieldModule.modK v.Completion (comp z v) = (Nat.card Fq : ℝ≥0) ^ (-(div z v * v.degree)) := by
  rw [v.modK_completion (v.valued_eq_exp_neg_ordC (comp_ne_zero z v)), div_apply, ← zpow_natCast,
    ← zpow_mul]
  ring_nf

theorem prod_zpow_aux {ι : Type*} (s : Finset ι) (q : ℝ≥0) (hq : q ≠ 0) (f : ι → ℤ) :
    ∏ i ∈ s, q ^ f i = q ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

theorem deg_eq_sum (a : Divisor Fq k) : Divisor.deg a = ∑ v ∈ a.support, a v * v.degree := by
  simp [Divisor.deg, Finsupp.liftAddHom_apply, Finsupp.sum]

/-- **The norm of an idele and its divisor** (Weil VI.§1, text p. 97):
$\lvert z\rvert_{\mathbb A}=q^{-\deg\operatorname{div}(z)}$ with $q=\lvert\mathbb F_q\rvert$. -/
@[kb "weil1973bnt" "Ch. VI, §1, text p. 97 (|z|_A = q^(-deg div z) for an idele z), function fields"]
theorem norm_eq (z : FFIdeleGroup Fq k) :
    norm z = (Nat.card Fq : ℝ≥0) ^ (-Divisor.deg (div z)) := by
  have hq : (Nat.card Fq : ℝ≥0) ≠ 0 := by
    have : 0 < Nat.card Fq := Nat.card_pos
    exact_mod_cast this.ne'
  rw [norm, finprod_eq_prod_of_mulSupport_subset (s := (div z).support)]
  · simp_rw [modK_comp]
    rw [prod_zpow_aux _ _ hq, deg_eq_sum, ← Finset.sum_neg_distrib]
  · intro v hv
    simp only [Function.mem_mulSupport] at hv
    simp only [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    apply hv
    rw [modK_comp, h0, zero_mul, neg_zero, zpow_zero]

theorem one_lt_card : (1 : ℝ≥0) < Nat.card Fq := by
  have : 1 < Nat.card Fq := Finite.one_lt_card
  exact_mod_cast this

theorem norm_mul (z w : FFIdeleGroup Fq k) : norm (z * w) = norm z * norm w := by
  have hq : (Nat.card Fq : ℝ≥0) ≠ 0 := (zero_lt_one.trans one_lt_card).ne'
  rw [norm_eq, norm_eq, norm_eq, div_mul, map_add, neg_add, zpow_add₀ hq]

theorem norm_eq_one_iff (z : FFIdeleGroup Fq k) : norm z = 1 ↔ Divisor.deg (div z) = 0 := by
  rw [norm_eq]
  constructor
  · intro h
    have := (zpow_right_injective₀ (zero_lt_one.trans one_lt_card) one_lt_card.ne')
      (h.trans (zpow_zero _).symm)
    omega
  · intro h; rw [h, neg_zero, zpow_zero]

/-- The diagonal embedding $k\to k_{\mathbb A}$ as a ring morphism. -/
def diagHom : k →+* FFAdeleRing Fq k where
  toFun := FFAdeleRing.diag
  map_one' := by ext v; exact map_one v.toCompletion
  map_mul' x y := by ext v; exact map_mul v.toCompletion x y
  map_zero' := by ext v; exact map_zero v.toCompletion
  map_add' x y := by ext v; exact map_add v.toCompletion x y

/-- The principal idele $\xi\in k^\times\subset k_{\mathbb A}^\times$. -/
def principal : kˣ →* FFIdeleGroup Fq k := Units.map (diagHom (Fq := Fq) (k := k)).toMonoidHom

theorem comp_principal (ξ : kˣ) (v : Place Fq k) : comp (principal ξ) v = v.toCompletion (ξ : k) := rfl

/-- The divisor of a principal idele is the divisor of the element of $k^\times$. -/
theorem div_principal (ξ : kˣ) : div (principal (Fq := Fq) ξ) = Divisor.div ξ := by
  ext v
  rw [div_apply, comp_principal, Place.ordC_toCompletion, Divisor.div_apply]

/-- **Artin's product formula** for a function field (Weil IV.§4 Thm. 5): $\lvert\xi\rvert_{\mathbb A}=1$ for
$\xi\in k^\times$. -/
@[kb "weil1973bnt" "Ch. IV, §4, Thm. 5 (Artin's product formula), function fields"]
theorem norm_principal (ξ : kˣ) : norm (principal (Fq := Fq) ξ) = 1 := by
  rw [norm_eq_one_iff, div_principal, Divisor.deg_div_eq_zero]

variable (Fq k) in
/-- The group $k^1$ of ideles of norm $1$ (Weil IV.§4, after Thm. 5). -/
def normOne : Subgroup (FFIdeleGroup Fq k) where
  carrier := {z | norm z = 1}
  one_mem' := by
    show norm 1 = 1
    rw [norm_eq_one_iff, div_one, map_zero]
  mul_mem' {z w} hz hw := by
    show norm (z * w) = 1
    rw [norm_mul, show norm z = 1 from hz, show norm w = 1 from hw, one_mul]
  inv_mem' {z} hz := by
    have hz' : Divisor.deg (div z) = 0 := (norm_eq_one_iff z).1 hz
    show norm z⁻¹ = 1
    rw [norm_eq_one_iff, deg_div_inv, hz', neg_zero]

theorem mem_normOne_iff (z : FFIdeleGroup Fq k) : z ∈ normOne Fq k ↔ Divisor.deg (div z) = 0 :=
  norm_eq_one_iff z

theorem principal_mem_normOne (ξ : kˣ) : principal ξ ∈ normOne Fq k := norm_principal ξ

/-- The open subgroup $\prod_v\mathfrak r_v^\times$ of $k_{\mathbb A}^\times$: ideles with all components units. -/
def integralUnits : Set (FFIdeleGroup Fq k) :=
  {z | (∀ v : Place Fq k, (z : FFAdeleRing Fq k) v ∈ (v.completionIntegers : Set v.Completion)) ∧
    ∀ v : Place Fq k, ((z⁻¹ : FFIdeleGroup Fq k) : FFAdeleRing Fq k) v ∈
      (v.completionIntegers : Set v.Completion)}

theorem isOpen_integralUnits : IsOpen (integralUnits (Fq := Fq) (k := k)) := by
  have hO : IsOpen {f : FFAdeleRing Fq k | ∀ v, f.1 v ∈ (v.completionIntegers : Set v.Completion)} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring v.Completion)
  exact (hO.preimage Units.continuous_val).inter (hO.preimage Units.continuous_coe_inv)

theorem one_mem_integralUnits : (1 : FFIdeleGroup Fq k) ∈ integralUnits :=
  ⟨fun v => v.completionIntegers.one_mem, fun v => v.completionIntegers.one_mem⟩

theorem div_eq_zero_of_mem_integralUnits {z : FFIdeleGroup Fq k} (hz : z ∈ integralUnits) : div z = 0 := by
  ext v
  have h1 : Valued.v (comp z v) ≤ 1 := hz.1 v
  have h2 : Valued.v (comp z⁻¹ v) ≤ 1 := hz.2 v
  have hm : Valued.v (comp z v) * Valued.v (comp z⁻¹ v) = 1 := by
    rw [← map_mul, comp_mul_inv, map_one]
  have h : Valued.v (comp z v) = 1 := by
    by_contra hne
    have hlt : Valued.v (comp z v) < 1 := lt_of_le_of_ne h1 hne
    have : Valued.v (comp z v) * Valued.v (comp z⁻¹ v) < 1 :=
      lt_of_lt_of_le (mul_lt_one_of_lt_of_le hlt h2) le_rfl
    rw [hm] at this
    exact lt_irrefl _ this
  simp [Place.ordC, h]

/-- $k^1$ is an open (hence also closed) subgroup of $k_{\mathbb A}^\times$. -/
theorem isOpen_normOne : IsOpen (normOne Fq k : Set (FFIdeleGroup Fq k)) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  refine Filter.mem_of_superset (isOpen_integralUnits.mem_nhds one_mem_integralUnits) ?_
  intro z hz
  rw [SetLike.mem_coe, mem_normOne_iff, div_eq_zero_of_mem_integralUnits hz, map_zero]

theorem exists_deg_pos : ∃ z : FFIdeleGroup Fq k, 0 < Divisor.deg (div z) := by
  obtain ⟨v⟩ := Place.nonempty (Fq := Fq) (k := k)
  obtain ⟨z, hz⟩ := div_surjective (Finsupp.single v (1 : ℤ) : Divisor Fq k)
  refine ⟨z, ?_⟩
  rw [hz, Divisor.deg_single, one_mul]
  exact_mod_cast v.degree_pos

/-- **Weil IV.§4, Cor. 1 of Thm. 5** (characteristic $p$): $k_{\mathbb A}^\times$ is the direct product of $k^1$ and
of a discrete subgroup isomorphic to $\mathbb Z$, generated by an idele $z_1$ with $\lvert z_1\rvert_{\mathbb A}>1$.
Moreover $k^1$ is open. -/
@[kb "weil1973bnt" "Ch. IV, §4, Cor. 1 of Thm. 5 (p. 75), function fields"]
theorem weil_IV_4_thm5_cor1 :
    ∃ z₁ : FFIdeleGroup Fq k, 1 < norm z₁ ∧ IsCompl (normOne Fq k) (Subgroup.zpowers z₁) ∧
      DiscreteTopology (Subgroup.zpowers z₁) ∧ Function.Injective (fun n : ℤ => z₁ ^ n) ∧
      IsOpen (normOne Fq k : Set (FFIdeleGroup Fq k)) := by
  classical
  have hex : ∃ d : ℕ, 0 < d ∧ ∃ z : FFIdeleGroup Fq k, Divisor.deg (div z) = -(d : ℤ) := by
    obtain ⟨z, hz⟩ := exists_deg_pos (Fq := Fq) (k := k)
    refine ⟨(Divisor.deg (div z)).toNat, by omega, z⁻¹, ?_⟩
    rw [deg_div_inv]
    omega
  obtain ⟨hd0, z₁, hz₁⟩ := Nat.find_spec hex
  set d := Nat.find hex with hd
  have hdpos : (0 : ℤ) < d := by exact_mod_cast hd0
  -- every degree is a multiple of `-d`
  have hmult : ∀ z : FFIdeleGroup Fq k, ∃ n : ℤ, Divisor.deg (div z) = -(d : ℤ) * n := by
    intro z
    obtain ⟨m, hm⟩ : ∃ m, Divisor.deg (div z) = m := ⟨_, rfl⟩
    refine ⟨m / -(d : ℤ), ?_⟩
    have hr0 : 0 ≤ m % -(d : ℤ) := Int.emod_nonneg _ (by omega)
    have hr1 : m % -(d : ℤ) < d := by
      have := Int.emod_lt m (show -(d : ℤ) ≠ 0 by omega)
      simpa using this
    have hdecomp : -(d : ℤ) * (m / -(d : ℤ)) + m % -(d : ℤ) = m := Int.mul_ediv_add_emod m _
    obtain ⟨n, hn⟩ : ∃ n, m / -(d : ℤ) = n := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, m % -(d : ℤ) = r := ⟨_, rfl⟩
    rw [hn, hr] at hdecomp
    rw [hr] at hr0 hr1
    rw [hn]
    by_contra hne
    have hrpos : 0 < r := by
      rcases hr0.lt_or_eq with h | h
      · exact h
      · exfalso; apply hne; omega
    have hlt : r.toNat < d := by omega
    apply Nat.find_min hex hlt
    refine ⟨by omega, z₁ ^ n * z⁻¹, ?_⟩
    rw [div_mul, map_add, deg_div_zpow, hz₁, deg_div_inv, hm]
    have : n * -(d : ℤ) = -(d : ℤ) * n := mul_comm _ _
    omega
  have hq1 := one_lt_card (Fq := Fq)
  have hdeg_zpow : ∀ n : ℤ, Divisor.deg (div (z₁ ^ n)) = -(d : ℤ) * n := by
    intro n; rw [deg_div_zpow, hz₁]; ring
  have hzero : ∀ n : ℤ, Divisor.deg (div (z₁ ^ n)) = 0 → n = 0 := by
    intro n h
    rw [hdeg_zpow] at h
    rcases mul_eq_zero.1 h with h | h
    · omega
    · exact h
  have hinj : Function.Injective (fun n : ℤ => z₁ ^ n) := by
    intro n m h
    have h' : z₁ ^ (n - m) = 1 := by
      simp only at h
      rw [zpow_sub, h, mul_inv_cancel]
    have := hzero (n - m) (by rw [h', div_one, map_zero])
    omega
  refine ⟨z₁, ?_, ?_, ?_, hinj, isOpen_normOne⟩
  · rw [norm_eq, hz₁, neg_neg]
    exact one_lt_zpow₀ hq1 hdpos
  · constructor
    · rw [disjoint_iff, eq_bot_iff]
      rintro z ⟨hz1, ⟨n, rfl⟩⟩
      have h1 : Divisor.deg (div (z₁ ^ n)) = 0 := (mem_normOne_iff _).1 hz1
      simp [hzero n h1]
    · rw [codisjoint_iff, eq_top_iff]
      intro z _
      obtain ⟨n, hz⟩ := hmult z
      have hy : z * (z₁ ^ n)⁻¹ ∈ normOne Fq k := by
        rw [mem_normOne_iff, div_mul, map_add, deg_div_inv, hdeg_zpow]
        omega
      have : z = (z * (z₁ ^ n)⁻¹) * z₁ ^ n := by group
      rw [this]
      exact Subgroup.mul_mem_sup hy (Subgroup.zpow_mem_zpowers z₁ n)
  · apply discreteTopology_of_isOpen_singleton_one
    have hW := isOpen_integralUnits.preimage
      (continuous_subtype_val (p := fun z => z ∈ Subgroup.zpowers z₁))
    convert hW using 1
    ext ⟨z, hz⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h
      have : z = 1 := congrArg Subtype.val h
      subst this
      exact one_mem_integralUnits
    · intro h
      obtain ⟨n, rfl⟩ := hz
      have h0 : Divisor.deg (div (z₁ ^ n)) = 0 := by
        rw [div_eq_zero_of_mem_integralUnits h, map_zero]
      have := hzero n h0
      subst this
      rfl

end FFIdeleGroup

end NumberFieldKB.WeilBNT.FF
