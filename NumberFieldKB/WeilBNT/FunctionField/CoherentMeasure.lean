import NumberFieldKB.WeilBNT.FunctionField.CoherentFF
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-!
# The Haar measure of $E_{\mathbb A}=k_{\mathbb A}^n$ (Weil VI.§1, Cor. 2 of Prop. 2; VI, Cor. 1 of Thm. 1)

`FFAdeleVec Fq k n` is $E_{\mathbb A}=k_{\mathbb A}^n$ with its Borel $\sigma$-algebra (a type synonym of
`Fin n → FFAdeleRing Fq k`, whose product $\sigma$-algebra need not be the Borel one).

* `haarVec`: the Haar measure $\mu$ of $E_{\mathbb A}$ with $\mu(\prod_v\mathfrak r_v^n)=1$.
* `haarVec_pi_U`: $\mu(\prod_iU(\mathfrak a_i))=q^{\sum_i\deg\mathfrak a_i}$; in particular $\mu$ agrees with the product
  of the measures $\mu_1$ of `AdeleVolume.lean` on these boxes.
* **`weil_VI_1_prop2_cor2`** (Weil VI.§1, Cor. 2 of Prop. 2): $\mu(U(L))=q^{-\delta(L)}$ for every coherent system $L$;
  `haarVec_U_basis`: $\mu(\prod_v\mathfrak e'_v)=1$ for the system of any other basis $\mathfrak e'$ of $E$.
* **`weil_VI_1_thm1_cor1_vec`** (Weil VI, Cor. 1 of Thm. 1): if $\mathbb F_q$ is the field of constants,
  $\mu(E_{\mathbb A}/E)=q^{n(g-1)}$.
-/

open scoped WithZero NNReal ENNReal Topology Pointwise
open MeasureTheory Filter Matrix

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

variable (Fq k) in
/-- $E_{\mathbb A}=k_{\mathbb A}^n$, with the Borel $\sigma$-algebra. -/
def FFAdeleVec (n : ℕ) : Type _ := Fin n → FFAdeleRing Fq k

namespace FFAdeleVec

variable {n : ℕ}

instance : AddCommGroup (FFAdeleVec Fq k n) := inferInstanceAs (AddCommGroup (Fin n → FFAdeleRing Fq k))
instance : TopologicalSpace (FFAdeleVec Fq k n) :=
  inferInstanceAs (TopologicalSpace (Fin n → FFAdeleRing Fq k))
instance : IsTopologicalAddGroup (FFAdeleVec Fq k n) :=
  inferInstanceAs (IsTopologicalAddGroup (Fin n → FFAdeleRing Fq k))
instance : T2Space (FFAdeleVec Fq k n) := inferInstanceAs (T2Space (Fin n → FFAdeleRing Fq k))
instance : LocallyCompactSpace (FFAdeleVec Fq k n) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → FFAdeleRing Fq k))
instance : MeasurableSpace (FFAdeleVec Fq k n) := borel _
instance : BorelSpace (FFAdeleVec Fq k n) := ⟨rfl⟩

/-- The identification with `Fin n → FFAdeleRing Fq k`. -/
def equiv : FFAdeleVec Fq k n ≃+ (Fin n → FFAdeleRing Fq k) := AddEquiv.refl _

/-- $U(L)$ as a subset of `FFAdeleVec`. -/
def USet (L : CoherentSystem Fq k n) : Set (FFAdeleVec Fq k n) := equiv ⁻¹' (L.U : Set (Fin n → FFAdeleRing Fq k))

/-- $U(\mathrm{std})$ is the box $\prod_iU(0)$. -/
theorem USet_std_eq : USet (CoherentSystem.std Fq k n) =
    equiv ⁻¹' Set.pi Set.univ (fun _ => (FFAdeleRing.U (0 : Divisor Fq k) : Set (FFAdeleRing Fq k))) := by
  ext x
  simp only [USet, Set.mem_preimage, SetLike.mem_coe, CoherentSystem.mem_U, Set.mem_pi, Set.mem_univ,
    true_implies, FFAdeleRing.mem_U_iff]
  show (∀ v, ∀ i, Valued.v (x i v) ≤ 1) ↔ _
  simp only [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
  exact forall_comm

theorem isCompact_USet_std : IsCompact (USet (CoherentSystem.std Fq k n)) := by
  rw [USet_std_eq]
  exact isCompact_univ_pi fun _ => FFAdeleRing.isCompact_U_zero

theorem isOpen_USet (L : CoherentSystem Fq k n) : IsOpen (USet L) := by
  classical
  have hS : {v : Place Fq k | ¬ L.L v = Place.stdLattice v n}.Finite :=
    Filter.eventually_cofinite.1 L.eventually_eq
  have h1 : IsOpen {x : Fin n → FFAdeleRing Fq k | ∀ i, ∀ v, v ∉ hS.toFinset →
      (x i).1 v ∈ (v.completionIntegers : Set v.Completion)} := by
    have : {x : Fin n → FFAdeleRing Fq k | ∀ i, ∀ v, v ∉ hS.toFinset →
        (x i).1 v ∈ (v.completionIntegers : Set v.Completion)} =
        ⋂ i, (fun x : Fin n → FFAdeleRing Fq k => x i) ⁻¹'
          {y : FFAdeleRing Fq k | ∀ v, v ∉ hS.toFinset → y.1 v ∈ (v.completionIntegers : Set v.Completion)} := by
      ext x; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      (RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring v.Completion)).preimage
        (continuous_apply i)
  have h2 : IsOpen {x : Fin n → FFAdeleRing Fq k | ∀ v ∈ hS.toFinset, (fun i => x i v) ∈ L.L v} := by
    have : {x : Fin n → FFAdeleRing Fq k | ∀ v ∈ hS.toFinset, (fun i => x i v) ∈ L.L v} =
        ⋂ v ∈ hS.toFinset, (fun x : Fin n → FFAdeleRing Fq k => fun i => x i v) ⁻¹' (L.L v : Set (Fin n → v.Completion)) := by
      ext x; simp
    rw [this]
    refine isOpen_biInter_finset fun v _ => ?_
    exact (L.isLattice v).2.2.preimage (continuous_pi fun i =>
      (RestrictedProduct.continuous_eval v).comp (continuous_apply i))
  suffices H : USet L = {x : Fin n → FFAdeleRing Fq k | ∀ i, ∀ v, v ∉ hS.toFinset →
      (x i).1 v ∈ (v.completionIntegers : Set v.Completion)} ∩
      {x : Fin n → FFAdeleRing Fq k | ∀ v ∈ hS.toFinset, (fun i => x i v) ∈ L.L v} by
    rw [H]; exact h1.inter h2
  ext x
  simp only [USet, Set.mem_preimage, SetLike.mem_coe, CoherentSystem.mem_U, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨fun i v hv => ?_, fun v _ => h v⟩
    have hv' : L.L v = Place.stdLattice v n := by simpa using hv
    have := h v
    rw [hv'] at this
    exact this i
  · rintro ⟨h1, h2⟩ v
    by_cases hv : v ∈ hS.toFinset
    · exact h2 v hv
    · have hv' : L.L v = Place.stdLattice v n := by simpa using hv
      rw [hv']
      exact fun i => h1 i v hv

/-- $\prod_v\mathfrak r_v^n$ as a compact set with nonempty interior. -/
def stdCompacts : TopologicalSpace.PositiveCompacts (FFAdeleVec Fq k n) :=
  ⟨⟨USet (CoherentSystem.std Fq k n), isCompact_USet_std⟩, ⟨0, by
    rw [(isOpen_USet _).interior_eq]; exact (CoherentSystem.std Fq k n).U.zero_mem⟩⟩

end FFAdeleVec

variable (Fq k) in
/-- **The Haar measure $\mu$ of $E_{\mathbb A}=k_{\mathbb A}^n$** with $\mu(\prod_v\mathfrak r_v^n)=1$ (Weil VI.§1, Cor. 2
of Prop. 2). -/
def haarVec (n : ℕ) : Measure (FFAdeleVec Fq k n) := Measure.addHaarMeasure FFAdeleVec.stdCompacts

instance (n : ℕ) : (haarVec Fq k n).IsAddHaarMeasure := by unfold haarVec; infer_instance

theorem haarVec_std (n : ℕ) : haarVec Fq k n (FFAdeleVec.USet (CoherentSystem.std Fq k n)) = 1 :=
  Measure.addHaarMeasure_self

/-- The box $\prod_iU(\mathfrak a_i)$ as an additive subgroup of $E_{\mathbb A}$. -/
def boxSub {n : ℕ} (a : Fin n → Divisor Fq k) : AddSubgroup (FFAdeleVec Fq k n) :=
  AddSubgroup.pi Set.univ fun i => FFAdeleRing.U (a i)

theorem mem_boxSub {n : ℕ} {a : Fin n → Divisor Fq k} {x : FFAdeleVec Fq k n} :
    x ∈ boxSub a ↔ ∀ i, (x : Fin n → FFAdeleRing Fq k) i ∈ FFAdeleRing.U (a i) := by
  exact ⟨fun h i => h i (Set.mem_univ i), fun h i _ => h i⟩

theorem isOpen_boxSub {n : ℕ} (a : Fin n → Divisor Fq k) : IsOpen (boxSub a : Set (FFAdeleVec Fq k n)) := by
  have : (boxSub a : Set (FFAdeleVec Fq k n)) =
      Set.pi Set.univ fun i => (FFAdeleRing.U (a i) : Set (FFAdeleRing Fq k)) := by
    ext x; exact ⟨fun h i _ => mem_boxSub.1 h i, fun h => mem_boxSub.2 fun i => h i (Set.mem_univ i)⟩
  rw [this]
  exact isOpen_set_pi Set.finite_univ fun i _ => FFAdeleRing.isOpen_U _

/-- The coordinatewise quotient map $\prod_iU(\mathfrak a_i)\to\prod_iU(\mathfrak a_i)/U(\mathfrak b_i)$. -/
def boxQuotHom {n : ℕ} (a b : Fin n → Divisor Fq k) :
    boxSub a →+ ∀ i, (FFAdeleRing.U (a i) ⧸ (FFAdeleRing.U (b i)).addSubgroupOf (FFAdeleRing.U (a i))) :=
  AddMonoidHom.pi fun i => (QuotientAddGroup.mk' _).comp
    { toFun := fun x => ⟨(x.1 : Fin n → FFAdeleRing Fq k) i, mem_boxSub.1 x.2 i⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem boxQuotHom_ker {n : ℕ} {a b : Fin n → Divisor Fq k} (h : ∀ i, b i ≤ a i) :
    (boxQuotHom a b).ker = (boxSub b).addSubgroupOf (boxSub a) := by
  ext x
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, mem_boxSub]
  constructor
  · intro hx i
    have := congrFun hx i
    simp only [boxQuotHom, AddMonoidHom.pi_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      QuotientAddGroup.mk'_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at this
    exact this
  · intro hx
    funext i
    simp only [boxQuotHom, AddMonoidHom.pi_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      QuotientAddGroup.mk'_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact hx i

theorem boxQuotHom_surjective {n : ℕ} (a b : Fin n → Divisor Fq k) :
    Function.Surjective (boxQuotHom a b) := by
  intro f
  refine ⟨⟨(fun i => (Quotient.out (f i)).1 : Fin n → FFAdeleRing Fq k), mem_boxSub.2 fun i => (Quotient.out (f i)).2⟩, ?_⟩
  funext i
  simp only [boxQuotHom, AddMonoidHom.pi_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    QuotientAddGroup.mk'_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact QuotientAddGroup.out_eq' (f i)

theorem natCard_box_quot {n : ℕ} {a b : Fin n → Divisor Fq k} (h : ∀ i, b i ≤ a i) :
    Nat.card (boxSub a ⧸ (boxSub b).addSubgroupOf (boxSub a)) =
      ∏ i, Nat.card Fq ^ (Divisor.deg (a i) - Divisor.deg (b i)).toNat := by
  rw [← boxQuotHom_ker h]
  have e := QuotientAddGroup.quotientKerEquivOfSurjective (G := boxSub a) (H := ∀ i, (FFAdeleRing.U (a i) ⧸ (FFAdeleRing.U (b i)).addSubgroupOf (FFAdeleRing.U (a i)))) (boxQuotHom a b) (boxQuotHom_surjective a b)
  have e2 := Nat.card_congr e.toEquiv
  rw [e2, Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact FFAdeleRing.relIndex_U (b i) (a i) (h i)

theorem haarVec_box_le {n : ℕ} {a b : Fin n → Divisor Fq k} (h : ∀ i, b i ≤ a i) :
    haarVec Fq k n (boxSub a) = (∏ i, (Nat.card Fq : ℝ≥0∞) ^ (Divisor.deg (a i) - Divisor.deg (b i)).toNat) *
      haarVec Fq k n (boxSub b) := by
  have hle : boxSub b ≤ boxSub a := fun x hx => mem_boxSub.2 fun i =>
    FFAdeleRing.U_mono (h i) (mem_boxSub.1 hx i)
  have hne : Nat.card (boxSub a ⧸ (boxSub b).addSubgroupOf (boxSub a)) ≠ 0 := by
    rw [natCard_box_quot h]
    exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (Nat.card_pos (α := Fq)).ne'
  haveI : Finite (boxSub a ⧸ (boxSub b).addSubgroupOf (boxSub a)) := Nat.finite_of_card_ne_zero hne
  rw [FFAdeleRing.measure_eq_card_mul (haarVec Fq k n) hle (isOpen_boxSub b).measurableSet, natCard_box_quot h]
  push_cast
  rfl

theorem exists_lower_bound {n : ℕ} (a : Fin n → Divisor Fq k) :
    ∃ bb : Divisor Fq k, bb ≤ 0 ∧ ∀ i, bb ≤ a i := by
  classical
  obtain ⟨M, hM⟩ := Finset.exists_le (insert (0 : Divisor Fq k) (Finset.univ.image fun i => -a i))
  refine ⟨-M, ?_, fun i => ?_⟩
  · have := hM 0 (Finset.mem_insert_self _ _)
    simpa using this
  · have := hM (-a i) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    exact neg_le.2 this

theorem prod_pow_toNat {n : ℕ} (x : Fin n → ℤ) (hx : ∀ i, 0 ≤ x i) :
    (∏ i, (Nat.card Fq : ℝ≥0∞) ^ (x i).toNat) = (Nat.card Fq : ℝ≥0∞) ^ (∑ i, x i) := by
  rw [Finset.prod_pow_eq_pow_sum, ← zpow_natCast]
  congr 1
  push_cast
  exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hx i)

/-- **Boxes**: $\mu(\prod_iU(\mathfrak a_i))=q^{\sum_i\deg\mathfrak a_i}$. -/
theorem haarVec_pi_U {n : ℕ} (a : Fin n → Divisor Fq k) :
    haarVec Fq k n (FFAdeleVec.equiv ⁻¹' Set.pi Set.univ fun i => (FFAdeleRing.U (a i) : Set (FFAdeleRing Fq k))) =
      (Nat.card Fq : ℝ≥0∞) ^ (∑ i, Divisor.deg (a i)) := by
  obtain ⟨bb, hb0, hba⟩ := exists_lower_bound a
  have hbox : ∀ c : Fin n → Divisor Fq k, (FFAdeleVec.equiv ⁻¹' Set.pi Set.univ fun i =>
      (FFAdeleRing.U (c i) : Set (FFAdeleRing Fq k)) : Set (FFAdeleVec Fq k n)) = boxSub c := by
    intro c; ext x; exact ⟨fun h i _ => mem_boxSub.1 h i, fun h => mem_boxSub.2 fun i => h i (Set.mem_univ i)⟩
  rw [hbox]
  set z : Fin n → Divisor Fq k := fun _ => (0 : Divisor Fq k) with hz
  set bv : Fin n → Divisor Fq k := fun _ => bb with hbv
  have h1 := haarVec_box_le (a := a) (b := bv) hba
  have h2 := haarVec_box_le (a := z) (b := bv) (fun _ => hb0)
  have h0 : haarVec Fq k n (boxSub z) = 1 := by
    have e : (boxSub z : Set (FFAdeleVec Fq k n)) = FFAdeleVec.USet (CoherentSystem.std Fq k n) := by
      ext x
      rw [FFAdeleVec.USet_std_eq]
      exact ⟨fun h i _ => mem_boxSub.1 h i, fun h => mem_boxSub.2 fun i => h i (Set.mem_univ i)⟩
    rw [e]; exact haarVec_std n
  rw [h0] at h2
  have hnn : ∀ i, 0 ≤ Divisor.deg (a i) - Divisor.deg bb := fun i => by
    rw [← _root_.map_sub]; exact Divisor.deg_nonneg (sub_nonneg.mpr (hba i))
  have hnn0 : 0 ≤ -Divisor.deg bb := by
    have := Divisor.deg_nonneg (sub_nonneg.mpr hb0)
    rw [_root_.map_sub, _root_.map_zero] at this; omega
  rw [prod_pow_toNat _ hnn] at h1
  rw [prod_pow_toNat (fun _ : Fin n => Divisor.deg (0 : Divisor Fq k) - Divisor.deg bb)
    (fun _ => by simpa using hnn0)] at h2
  set Q : ℝ≥0∞ := (Nat.card Fq : ℝ≥0∞)
  have hQ0 : Q ≠ 0 := by
    simp only [Q, ne_eq, Nat.cast_eq_zero]; exact (Nat.card_pos (α := Fq)).ne'
  have hQt : Q ≠ ⊤ := by simp [Q]
  set m := haarVec Fq k n (boxSub bv)
  have hsplit : Q ^ (∑ i, (Divisor.deg (a i) - Divisor.deg bb)) =
      Q ^ (∑ i, Divisor.deg (a i)) * Q ^ (∑ _i : Fin n, (Divisor.deg (0 : Divisor Fq k) - Divisor.deg bb)) := by
    rw [← ENNReal.zpow_add hQ0 hQt]
    congr 1
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      _root_.map_zero]
    ring
  rw [h1, hsplit, mul_assoc, ← h2]
  simp

section GLAction

variable {n : ℕ}

/-- The action $x\mapsto a\,x$ of $a\in\mathrm{GL}_n(k_{\mathbb A})$ on $E_{\mathbb A}=k_{\mathbb A}^n$ as a
continuous additive automorphism. -/
def glAct (a : GL (Fin n) (FFAdeleRing Fq k)) : FFAdeleVec Fq k n ≃ₜ+ FFAdeleVec Fq k n where
  toFun x := a.1 *ᵥ (x : Fin n → FFAdeleRing Fq k)
  invFun x := a.inv *ᵥ (x : Fin n → FFAdeleRing Fq k)
  left_inv x := by
    have h : ∀ y : Fin n → FFAdeleRing Fq k, a.inv *ᵥ (a.1 *ᵥ y) = y := fun y => by
      rw [Matrix.mulVec_mulVec, a.inv_val, Matrix.one_mulVec]
    exact h x
  right_inv x := by
    have h : ∀ y : Fin n → FFAdeleRing Fq k, a.1 *ᵥ (a.inv *ᵥ y) = y := fun y => by
      rw [Matrix.mulVec_mulVec, a.val_inv, Matrix.one_mulVec]
    exact h x
  map_add' x y := Matrix.mulVec_add _ _ _
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem glAct_apply (a : GL (Fin n) (FFAdeleRing Fq k)) (x : FFAdeleVec Fq k n) :
    (glAct a x : Fin n → FFAdeleRing Fq k) = a.1 *ᵥ (x : Fin n → FFAdeleRing Fq k) := rfl

/-- The $v$-component of $a\,x$ is $a_v\,x_v$. -/
theorem glAct_local (a : GL (Fin n) (FFAdeleRing Fq k)) (x : FFAdeleVec Fq k n) (v : Place Fq k) :
    (fun i => (glAct a x : Fin n → FFAdeleRing Fq k) i v) =
      (glAt v a).1 *ᵥ (fun i => (x : Fin n → FFAdeleRing Fq k) i v) := by
  funext i
  have := RingHom.map_mulVec (RestrictedProduct.evalRingHom (fun w : Place Fq k => w.Completion) v)
    a.1 (x : Fin n → FFAdeleRing Fq k) i
  exact this

theorem mem_latticeMap_iff_inv {v : Place Fq k} (g : GL (Fin n) v.Completion)
    (L : AddSubgroup (Fin n → v.Completion)) (x : Fin n → v.Completion) :
    x ∈ Place.latticeMap g.1 L ↔ g⁻¹.1 *ᵥ x ∈ L := by
  rw [Place.mem_latticeMap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  · intro h
    refine ⟨_, h, ?_⟩
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

/-- Local-global: $x\in\prod_v g_vL_v$ iff $g^{-1}x\in\prod_vL_v$. -/
theorem mem_glAct_inv_iff (κ : GL (Fin n) (FFAdeleRing Fq k))
    (L : ∀ v : Place Fq k, AddSubgroup (Fin n → v.Completion)) (x : FFAdeleVec Fq k n) :
    (∀ v, (fun i => (x : Fin n → FFAdeleRing Fq k) i v) ∈ Place.latticeMap (glAt v κ).1 (L v)) ↔
      ∀ v, (fun i => (glAct κ⁻¹ x : Fin n → FFAdeleRing Fq k) i v) ∈ L v := by
  refine forall_congr' fun v => ?_
  rw [mem_latticeMap_iff_inv, glAct_local]
  have : glAt v κ⁻¹ = (glAt v κ)⁻¹ := map_inv (Matrix.GeneralLinearGroup.map _) κ
  rw [this]

end GLAction

namespace Place

/-- $\operatorname{mod}_{k_v}(x)<1$ iff $v(x)<1$. -/
theorem modK_lt_one_iff (v : Place Fq k) (x : v.Completion) :
    FieldModule.modK v.Completion x < 1 ↔ Valued.v x < 1 := by
  by_cases hx : x = 0
  · subst hx; simp
  · have h := valued_eq_exp_neg_ordC v hx
    rw [modK_completion v h, h]
    have hB : (1 : ℝ≥0) < (Nat.card Fq : ℝ≥0) ^ v.degree :=
      one_lt_pow₀ FFIdeleGroup.one_lt_card v.degree_pos.ne'
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    exact zpow_lt_one_iff_right₀ hB

/-- $v(x)<1$ iff $v(x)\le e^{-1}$. -/
theorem valued_lt_one_iff (v : Place Fq k) (x : v.Completion) :
    Valued.v x < 1 ↔ Valued.v x ≤ WithZero.exp (-1) := by
  by_cases hx : x = 0
  · subst hx; simp
  · have h := valued_eq_exp_neg_ordC v hx
    rw [h, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

/-- The prime ideal of $k_v$ is generated by `uniC v`. -/
theorem pP_eq_uniC (v : Place Fq k) :
    FieldModule.pP (weil_ff_completion_isPField v).1 =
      (fun r => FFAdeleRing.uniC v * r) '' (FieldModule.pR (weil_ff_completion_isPField v).1 : Set v.Completion) := by
  ext x
  rw [FieldModule.mem_pP, modK_lt_one_iff, valued_lt_one_iff]
  have hu0 : FFAdeleRing.uniC v ≠ 0 := FFAdeleRing.uniC_ne_zero v
  constructor
  · intro hx
    refine ⟨x / FFAdeleRing.uniC v, ?_, mul_div_cancel₀ _ hu0⟩
    rw [SetLike.mem_coe, mem_pR_iff, map_div₀, FFAdeleRing.valued_uniC]
    exact div_le_one_of_le₀ hx (zero_le')
  · rintro ⟨r, hr, rfl⟩
    have := (mem_pR_iff v r).1 hr
    rw [map_mul, FFAdeleRing.valued_uniC]
    calc WithZero.exp (-1) * Valued.v r ≤ WithZero.exp (-1) * 1 := by gcongr
      _ = _ := mul_one _

/-- The lattice $\{y: v(y_i)\le e^{-\nu_i}\}=\pi^{\nu}\mathfrak r_v^n$. -/
def boxLat (v : Place Fq k) {n : ℕ} (ν : Fin n → ℤ) : AddSubgroup (Fin n → v.Completion) where
  carrier := {y | ∀ i, Valued.v (y i) ≤ WithZero.exp (-ν i)}
  zero_mem' := fun i => by simp
  add_mem' {x y} hx hy := fun i => by
    show Valued.v (x i + y i) ≤ _
    exact (Valuation.map_add _ _ _).trans (max_le (hx i) (hy i))
  neg_mem' {x} hx := fun i => by
    show Valued.v (-(x i)) ≤ _
    rw [Valuation.map_neg]; exact hx i

theorem mem_boxLat {v : Place Fq k} {n : ℕ} {ν : Fin n → ℤ} {y : Fin n → v.Completion} :
    y ∈ boxLat v ν ↔ ∀ i, Valued.v (y i) ≤ WithZero.exp (-ν i) := Iff.rfl

theorem boxLat_zero (v : Place Fq k) (n : ℕ) : boxLat v (0 : Fin n → ℤ) = stdLattice v n := by
  ext x; simp [mem_boxLat, mem_stdLattice]

theorem cm_latticeMap_one {v : Place Fq k} {n : ℕ} (L : AddSubgroup (Fin n → v.Completion)) :
    latticeMap (1 : Matrix (Fin n) (Fin n) v.Completion) L = L := by
  ext x; simp [mem_latticeMap]

theorem cm_latticeMap_mul {v : Place Fq k} {n : ℕ} (g h : GL (Fin n) v.Completion)
    (L : AddSubgroup (Fin n → v.Completion)) :
    latticeMap (g * h).1 L = latticeMap g.1 (latticeMap h.1 L) := by
  ext x
  simp only [mem_latticeMap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨h.1 *ᵥ y, ⟨y, hy, rfl⟩, by rw [Units.val_mul, Matrix.mulVec_mulVec]⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by rw [Units.val_mul, Matrix.mulVec_mulVec]⟩

/-- Products of exponentials. -/
theorem exp_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, WithZero.exp (f i) = WithZero.exp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, WithZero.exp_add]

/-- The diagonal matrix $\operatorname{diag}(\pi^{\nu_i})$. -/
def diagGL (v : Place Fq k) {n : ℕ} (ν : Fin n → ℤ) : GL (Fin n) v.Completion :=
  Matrix.GeneralLinearGroup.mk'' (Matrix.diagonal fun i => FFAdeleRing.uniC v ^ ν i) (by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (FFAdeleRing.uniC_ne_zero v))

theorem valued_det_diagGL (v : Place Fq k) {n : ℕ} (ν : Fin n → ℤ) :
    Valued.v (diagGL v ν).1.det = WithZero.exp (-(∑ i, ν i)) := by
  simp only [diagGL, Matrix.GeneralLinearGroup.val_mk'', Matrix.det_diagonal, map_prod]
  simp_rw [FFAdeleRing.valued_zpow (FFAdeleRing.valued_uniC v)]
  rw [exp_sum, Finset.sum_neg_distrib]

theorem latticeMap_diagGL (v : Place Fq k) {n : ℕ} (ν : Fin n → ℤ) :
    latticeMap (diagGL v ν).1 (stdLattice v n) = boxLat v ν := by
  ext x
  rw [mem_latticeMap]
  simp only [diagGL, Matrix.GeneralLinearGroup.val_mk'']
  have hpos : ∀ i, (0 : ℤᵐ⁰) < WithZero.exp (-ν i) := fun i => zero_lt_iff.2 WithZero.exp_ne_zero
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    rw [Matrix.mulVec_diagonal, map_mul, FFAdeleRing.valued_zpow (FFAdeleRing.valued_uniC v)]
    calc WithZero.exp (-ν i) * Valued.v (y i) ≤ WithZero.exp (-ν i) * 1 := by
          gcongr; exact mem_stdLattice.1 hy i
      _ = _ := mul_one _
  · intro hx
    refine ⟨fun i => (FFAdeleRing.uniC v ^ ν i)⁻¹ * x i, fun i => ?_, ?_⟩
    · show Valued.v ((FFAdeleRing.uniC v ^ ν i)⁻¹ * x i) ≤ 1
      rw [map_mul, map_inv₀, FFAdeleRing.valued_zpow (FFAdeleRing.valued_uniC v),
        inv_mul_le_iff₀ (hpos i), mul_one]
      exact hx i
    · funext i
      rw [Matrix.mulVec_diagonal]
      exact mul_inv_cancel_left₀ (zpow_ne_zero _ (FFAdeleRing.uniC_ne_zero v)) _

/-- **Elementary divisors at $v$, in the form needed globally**: $L=\kappa\,\pi^{\nu}\mathfrak r_v^n$ with
$\kappa\,\mathfrak r_v^n=\mathfrak r_v^n$. -/
theorem decomp_aux (v : Place Fq k) {n : ℕ} {L : AddSubgroup (Fin n → v.Completion)} (hL : v.IsLattice L) :
    ∃ (κ : GL (Fin n) v.Completion) (ν : Fin n → ℤ),
      latticeMap κ.1 (stdLattice v n) = stdLattice v n ∧ L = latticeMap κ.1 (boxLat v ν) := by
  have hK := (weil_ff_completion_isPField v).1
  obtain ⟨b, ν, h1, h2⟩ := FieldModule.weil_II_2_thm2 hK (isLattice_stdLattice v n) hL
    (FFAdeleRing.uniC_ne_zero v) (pP_eq_uniC v)
  have hn : Module.finrank v.Completion (Fin n → v.Completion) = n := Module.finrank_fin_fun _
  let e : Fin (Module.finrank v.Completion (Fin n → v.Completion)) ≃ Fin n := finCongr hn
  let b' := b.reindex e
  let M : Matrix (Fin n) (Fin n) v.Completion := Matrix.of fun i j => b' j i
  have hM : M = (Pi.basisFun v.Completion (Fin n)).toMatrix b' := by
    ext i j; simp [M, Module.Basis.toMatrix_apply]
  have hdet : IsUnit M.det := by
    rw [hM]
    haveI := (Pi.basisFun v.Completion (Fin n)).invertibleToMatrix b'
    exact Matrix.isUnit_det_of_invertible _
  have key : ∀ c : Fin n → v.Completion, M *ᵥ c = ∑ i, c (e i) • b i := by
    intro c
    have h1 : M *ᵥ c = ∑ j, c j • b' j := by
      funext r
      simp [Matrix.mulVec, dotProduct, M, mul_comm, Finset.sum_apply]
    rw [h1, ← Equiv.sum_comp e]
    simp [b']
  have hstd : ∀ x, x ∈ stdLattice v n ↔ ∃ c : Fin (Module.finrank v.Completion (Fin n → v.Completion)) → v.Completion,
      (∀ i, c i ∈ FieldModule.pR hK) ∧ x = ∑ i, c i • b i := fun x => Set.ext_iff.1 h1 x
  have hL2 : ∀ x, x ∈ L ↔ ∃ c : Fin (Module.finrank v.Completion (Fin n → v.Completion)) → v.Completion,
      (∀ i, c i ∈ FieldModule.pR hK) ∧ x = ∑ i, (c i * FFAdeleRing.uniC v ^ ν i) • b i :=
    fun x => Set.ext_iff.1 h2 x
  refine ⟨Matrix.GeneralLinearGroup.mk'' M hdet, fun j => ν (e.symm j), ?_, ?_⟩
  · ext x
    rw [mem_latticeMap]
    simp only [Matrix.GeneralLinearGroup.val_mk'']
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hstd]
      exact ⟨fun i => y (e i), fun i => (mem_pR_iff v _).2 (mem_stdLattice.1 hy (e i)), key y⟩
    · intro hx
      obtain ⟨c, hc, rfl⟩ := (hstd x).1 hx
      refine ⟨fun j => c (e.symm j), mem_stdLattice.2 fun j => (mem_pR_iff v _).1 (hc _), ?_⟩
      rw [key]
      simp
  · ext x
    rw [mem_latticeMap]
    simp only [Matrix.GeneralLinearGroup.val_mk'']
    constructor
    · intro hx
      obtain ⟨c, hc, rfl⟩ := (hL2 x).1 hx
      refine ⟨fun j => c (e.symm j) * FFAdeleRing.uniC v ^ ν (e.symm j), fun j => ?_, ?_⟩
      · show Valued.v (c (e.symm j) * FFAdeleRing.uniC v ^ ν (e.symm j)) ≤ WithZero.exp (-ν (e.symm j))
        rw [map_mul, FFAdeleRing.valued_zpow (FFAdeleRing.valued_uniC v)]
        calc Valued.v (c (e.symm j)) * WithZero.exp (-ν (e.symm j)) ≤ 1 * WithZero.exp (-ν (e.symm j)) := by
              gcongr; exact (mem_pR_iff v _).1 (hc _)
          _ = _ := one_mul _
      · rw [key]
        simp
    · rintro ⟨y, hy, rfl⟩
      rw [hL2]
      refine ⟨fun i => y (e i) * (FFAdeleRing.uniC v ^ ν i)⁻¹, fun i => ?_, ?_⟩
      · rw [mem_pR_iff, map_mul, map_inv₀, FFAdeleRing.valued_zpow (FFAdeleRing.valued_uniC v)]
        have := hy (e i)
        simp only [Equiv.symm_apply_apply] at this
        have hpos : (0 : ℤᵐ⁰) < WithZero.exp (-ν i) := zero_lt_iff.2 WithZero.exp_ne_zero
        rw [← div_eq_mul_inv, div_le_one₀ hpos]
        exact this
      · rw [key]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [inv_mul_cancel_right₀ (zpow_ne_zero _ (FFAdeleRing.uniC_ne_zero v))]

/-- Elementary divisors at $v$, with the determinant. -/
theorem local_decomp (v : Place Fq k) {n : ℕ} {L : AddSubgroup (Fin n → v.Completion)} (hL : v.IsLattice L) :
    ∃ (κ : GL (Fin n) v.Completion) (ν : Fin n → ℤ),
      latticeMap κ.1 (stdLattice v n) = stdLattice v n ∧
      L = latticeMap κ.1 (boxLat v ν) ∧
      (∀ g : GL (Fin n) v.Completion, L = latticeMap g.1 (stdLattice v n) →
        Valued.v g.1.det = WithZero.exp (-(∑ i, ν i))) ∧
      (L = stdLattice v n → ν = 0) := by
  have main : ∀ (κ : GL (Fin n) v.Completion) (ν : Fin n → ℤ),
      latticeMap κ.1 (stdLattice v n) = stdLattice v n → L = latticeMap κ.1 (boxLat v ν) →
      ∀ g : GL (Fin n) v.Completion, L = latticeMap g.1 (stdLattice v n) →
        Valued.v g.1.det = WithZero.exp (-(∑ i, ν i)) := by
    intro κ ν hκ hLκ g hg
    have h1 : latticeMap g.1 (stdLattice v n) = latticeMap (κ * diagGL v ν).1 (stdLattice v n) := by
      rw [← hg, cm_latticeMap_mul, latticeMap_diagGL, ← hLκ]
    rw [valued_det_eq_of_map_eq v g _ h1, Units.val_mul, Matrix.det_mul, map_mul,
      valued_det_diagGL]
    have : Valued.v κ.1.det = 1 := by
      have := valued_det_eq_of_map_eq v κ 1 (by rw [hκ, Units.val_one, latticeMap_one])
      rw [this]; simp
    rw [this, one_mul]
  by_cases hs : L = stdLattice v n
  · refine ⟨1, 0, ?_, ?_, ?_, fun _ => rfl⟩
    · rw [Units.val_one, latticeMap_one]
    · rw [Units.val_one, latticeMap_one, boxLat_zero, hs]
    · apply main 1 0
      · rw [Units.val_one, latticeMap_one]
      · rw [Units.val_one, latticeMap_one, boxLat_zero, hs]
  · obtain ⟨κ, ν, h1, h2⟩ := decomp_aux v hL
    exact ⟨κ, ν, h1, h2, main κ ν h1 h2, fun h => absurd h hs⟩

end Place

namespace Place

/-- If $g\,\mathfrak r_v^n=\mathfrak r_v^n$ then the entries of $g$ are integral. -/
theorem entry_le_one_of_latticeMap_eq {v : Place Fq k} {n : ℕ} {g : GL (Fin n) v.Completion}
    (h : latticeMap g.1 (stdLattice v n) = stdLattice v n) (i j : Fin n) :
    Valued.v (g.1 i j) ≤ 1 := by
  classical
  have hy : (Pi.single j 1 : Fin n → v.Completion) ∈ stdLattice v n := by
    intro i'
    by_cases h : i' = j <;> simp [Pi.single_apply, h]
  have h1 : g.1 *ᵥ (Pi.single j 1 : Fin n → v.Completion) ∈ stdLattice v n := by
    rw [← h]; exact mem_latticeMap.2 ⟨_, hy, rfl⟩
  have h2 := h1 i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

/-- If $g\,\mathfrak r_v^n=\mathfrak r_v^n$ then $g^{-1}\mathfrak r_v^n=\mathfrak r_v^n$. -/
theorem latticeMap_inv_eq {v : Place Fq k} {n : ℕ} {g : GL (Fin n) v.Completion}
    (h : latticeMap g.1 (stdLattice v n) = stdLattice v n) :
    latticeMap g⁻¹.1 (stdLattice v n) = stdLattice v n := by
  have := cm_latticeMap_mul g⁻¹ g (stdLattice v n)
  rw [inv_mul_cancel, Units.val_one, latticeMap_one, h] at this
  exact this.symm

end Place

/-- Local elements of $\mathrm{GL}_n(\mathfrak r_v)$ assemble to an element of $\mathrm{GL}_n(k_{\mathbb A})$. -/
theorem exists_glAdele {n : ℕ} (κ : ∀ v : Place Fq k, GL (Fin n) v.Completion)
    (hκ : ∀ v, Place.latticeMap (κ v).1 (Place.stdLattice v n) = Place.stdLattice v n) :
    ∃ K : GL (Fin n) (FFAdeleRing Fq k), ∀ v, glAt v K = κ v := by
  let K : Matrix (Fin n) (Fin n) (FFAdeleRing Fq k) := Matrix.of fun i j =>
    ⟨fun v => (κ v).1 i j, Filter.Eventually.of_forall fun v =>
      Place.entry_le_one_of_latticeMap_eq (hκ v) i j⟩
  let K' : Matrix (Fin n) (Fin n) (FFAdeleRing Fq k) := Matrix.of fun i j =>
    ⟨fun v => (κ v)⁻¹.1 i j, Filter.Eventually.of_forall fun v =>
      Place.entry_le_one_of_latticeMap_eq (Place.latticeMap_inv_eq (hκ v)) i j⟩
  have hK : ∀ v, (RestrictedProduct.evalRingHom (fun w : Place Fq k => w.Completion) v).mapMatrix K =
      (κ v).1 := fun v => by ext i j; rfl
  have hK' : ∀ v, (RestrictedProduct.evalRingHom (fun w : Place Fq k => w.Completion) v).mapMatrix K' =
      (κ v)⁻¹.1 := fun v => by ext i j; rfl
  have h1 : K * K' = 1 := by
    ext i j v
    have : (RestrictedProduct.evalRingHom (fun w : Place Fq k => w.Completion) v).mapMatrix (K * K') =
        (RestrictedProduct.evalRingHom (fun w : Place Fq k => w.Completion) v).mapMatrix
          (1 : Matrix (Fin n) (Fin n) (FFAdeleRing Fq k)) := by
      rw [map_mul, hK, hK', Units.mul_inv, map_one]
    have := congrFun (congrFun this i) j
    simpa [RingHom.mapMatrix_apply, RestrictedProduct.evalRingHom_apply] using this
  have h2 : K' * K = 1 := by
    ext i j v
    have : (RestrictedProduct.evalRingHom (fun w : Place Fq k => w.Completion) v).mapMatrix (K' * K) =
        (RestrictedProduct.evalRingHom (fun w : Place Fq k => w.Completion) v).mapMatrix
          (1 : Matrix (Fin n) (Fin n) (FFAdeleRing Fq k)) := by
      rw [map_mul, hK, hK', Units.inv_mul, map_one]
    have := congrFun (congrFun this i) j
    simpa [RingHom.mapMatrix_apply, RestrictedProduct.evalRingHom_apply] using this
  exact ⟨⟨K, K', h1, h2⟩, fun v => Units.ext (hK v)⟩

theorem coe_boxSub {n : ℕ} (d : Fin n → Divisor Fq k) :
    (boxSub d : Set (FFAdeleVec Fq k n)) =
      FFAdeleVec.equiv ⁻¹' Set.pi Set.univ fun i => (FFAdeleRing.U (d i) : Set (FFAdeleRing Fq k)) := by
  ext x; exact ⟨fun h i _ => mem_boxSub.1 h i, fun h => mem_boxSub.2 fun i => h i (Set.mem_univ i)⟩

instance (n : ℕ) : (haarVec Fq k n).Regular := by unfold haarVec; infer_instance

/-- **Weil VI.§1, Cor. 2 of Prop. 2** ($E=k^n$): the Haar measure $\mu$ with $\mu(\prod_v\mathfrak r_v^n)=1$ gives
$\mu(U(L))=q^{-\delta(L)}$ for every coherent system $L$. -/
@[kb "weil1973bnt" "Ch. VI, §1, Cor. 2 of Prop. 2 (p. 98), E = k^n: mu(U(L)) = q^(-delta(L))"]
theorem weil_VI_1_prop2_cor2 {n : ℕ} (L : CoherentSystem Fq k n) :
    haarVec Fq k n (FFAdeleVec.USet L) = (Nat.card Fq : ℝ≥0∞) ^ (-L.delta) := by
  classical
  choose κ ν hκ hL hdet hν using fun v : Place Fq k => Place.local_decomp v (L.isLattice v)
  obtain ⟨K, hK⟩ := exists_glAdele κ hκ
  have hfin : ∀ i, (Function.support fun v : Place Fq k => -(ν v i)).Finite := by
    intro i
    refine (Filter.eventually_cofinite.1 L.eventually_eq).subset ?_
    intro v hv h
    apply hv
    simp [hν v h]
  let d : Fin n → Divisor Fq k := fun i => Finsupp.ofSupportFinite _ (hfin i)
  have hd : ∀ i v, d i v = -(ν v i) := fun i v => rfl
  have hmem : ∀ x : FFAdeleVec Fq k n, x ∈ FFAdeleVec.USet L ↔ glAct K⁻¹ x ∈ boxSub d := by
    intro x
    have e1 : x ∈ FFAdeleVec.USet L ↔ ∀ v, (fun i => (x : Fin n → FFAdeleRing Fq k) i v) ∈
        Place.latticeMap (glAt v K).1 (Place.boxLat v (ν v)) := by
      refine forall_congr' fun v => ?_
      rw [hK v, ← hL v]
      exact Iff.rfl
    rw [e1, mem_glAct_inv_iff, mem_boxSub]
    constructor
    · intro h i
      rw [FFAdeleRing.mem_U_iff]
      intro v
      rw [hd]
      exact h v i
    · intro h v i
      have := (FFAdeleRing.mem_U_iff _ _).1 (h i) v
      rw [hd] at this
      exact this
  have hstd : (glAct K⁻¹) ⁻¹' (FFAdeleVec.USet (CoherentSystem.std Fq k n)) =
      FFAdeleVec.USet (CoherentSystem.std Fq k n) := by
    ext x
    have e1 : x ∈ FFAdeleVec.USet (CoherentSystem.std Fq k n) ↔ ∀ v, (fun i => (x : Fin n → FFAdeleRing Fq k) i v) ∈
        Place.latticeMap (glAt v K).1 (Place.stdLattice v n) := by
      refine forall_congr' fun v => ?_
      rw [hK v, hκ v]
      exact Iff.rfl
    rw [e1, mem_glAct_inv_iff]
    exact Iff.rfl
  have hchar : addEquivAddHaarChar (glAct K⁻¹) = 1 := by
    have := addEquivAddHaarChar_smul_preimage (haarVec Fq k n)
      (X := FFAdeleVec.USet (CoherentSystem.std Fq k n)) (glAct K⁻¹)
    rw [hstd, haarVec_std] at this
    simpa using this
  have hpre : haarVec Fq k n (FFAdeleVec.USet L) = haarVec Fq k n (boxSub d) := by
    have := addEquivAddHaarChar_smul_preimage (haarVec Fq k n) (X := (boxSub d : Set (FFAdeleVec Fq k n)))
      (glAct K⁻¹)
    rw [hchar, one_smul] at this
    rw [← this]
    congr 1
    ext x
    exact hmem x
  rw [hpre, coe_boxSub, haarVec_pi_U]
  congr 1
  obtain ⟨a, ha⟩ := (weil_VI_1_prop2 L).1
  have hdiv : FFIdeleGroup.div (detIdele a) = ∑ i, -d i := by
    ext v
    have h := hdet v (glAt v a) (ha v)
    rw [FFIdeleGroup.div_apply, comp_detIdele, Place.ordC, h, WithZero.log_exp, Finsupp.finset_sum_apply]
    simp [hd]
  rw [CoherentSystem.delta, L.div_eq a ha, hdiv]
  simp

/-- The matrix $P\in\mathrm{GL}_n(k)$ of a basis, as an element of $\mathrm{GL}_n(k_{\mathbb A})$. -/
def glDiag {n : ℕ} (P : GL (Fin n) k) : GL (Fin n) (FFAdeleRing Fq k) :=
  Matrix.GeneralLinearGroup.map (FFIdeleGroup.diagHom (Fq := Fq) (k := k)) P

/-- **Weil VI.§1, Cor. 2 of Prop. 2**, first part: $\mu(\prod_v\mathfrak e'_v)=1$ for the coherent system
$(P\,\mathfrak r_v^n)$ of any basis $\mathfrak e'$ of $E$ (matrix $P\in\mathrm{GL}_n(k)$). -/
theorem haarVec_U_basis {n : ℕ} (P : GL (Fin n) k) :
    haarVec Fq k n (FFAdeleVec.USet (CoherentSystem.ofGL (glDiag (Fq := Fq) P))) = 1 := by
  rw [weil_VI_1_prop2_cor2]
  have h1 : detIdele (glDiag (Fq := Fq) P) = FFIdeleGroup.principal (Matrix.GeneralLinearGroup.det P) :=
    Matrix.GeneralLinearGroup.map_det _ P
  have h2 : (CoherentSystem.ofGL (glDiag (Fq := Fq) P)).delta = 0 := by
    rw [CoherentSystem.delta, CoherentSystem.div_eq _ (glDiag (Fq := Fq) P) (fun v => rfl), h1,
      FFIdeleGroup.div_principal, Divisor.deg_div_eq_zero]
  rw [h2]; simp

variable (Fq k) in
/-- $E=k^n$ embedded diagonally in $E_{\mathbb A}$. -/
def diagVecSubgroup (n : ℕ) : AddSubgroup (FFAdeleVec Fq k n) :=
  AddSubgroup.pi Set.univ fun _ => FFAdeleRing.diagSubgroup Fq k

/-- Every adele is translated into the fundamental domain `fundDom a b` by a principal adele. -/
theorem exists_diag_mem_fundDom (hc : IsConstantField Fq k) {a b : Divisor Fq k}
    (ha : 2 * Rep.genusInt Fq k - 2 < Divisor.deg a) (hba : b ≤ a) (x : FFAdeleRing Fq k) :
    ∃ ζ : k, (FFAdeleRing.diag ζ : FFAdeleRing Fq k) + x ∈ FFAdeleRing.fundDom a b := by
  obtain ⟨ξ, hξ⟩ := FFAdeleRing.weil_VI_2_cor3_adelic hc ha x
  set c : FFAdeleRing.U a ⧸ (FFAdeleRing.Hp a b).addSubgroupOf (FFAdeleRing.U a) := QuotientAddGroup.mk (⟨x - FFAdeleRing.diag ξ, hξ⟩ : FFAdeleRing.U a) with hcdef
  have h2 := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' c)
  rw [AddSubgroup.mem_addSubgroupOf] at h2
  have h3 : -(Quotient.out c).1 + (x - FFAdeleRing.diag ξ) ∈ FFAdeleRing.Hp a b := by simpa using h2
  obtain ⟨h, hh, η, hη, heq⟩ := (FFAdeleRing.mem_Hp a b).1 h3
  refine ⟨-(ξ + η), FFAdeleRing.mem_fundDom.2 ⟨c, ?_⟩⟩
  have : -(Quotient.out c).1 + (FFAdeleRing.diag (-(ξ + η)) + x) = h := by
    have e1 : h = -(Quotient.out c).1 + (x - FFAdeleRing.diag ξ) - FFAdeleRing.diag η := by rw [eq_sub_iff_add_eq, heq]
    rw [e1, FFAdeleRing.diag_neg, FFAdeleRing.diag_add]; abel
  rw [this]; exact hh

/-- $F^n$ for $F=$ `fundDom a b`. -/
def fundDomVec (a b : Divisor Fq k) (n : ℕ) : Set (FFAdeleVec Fq k n) :=
  FFAdeleVec.equiv ⁻¹' Set.pi Set.univ fun _ => FFAdeleRing.fundDom a b

instance (n : ℕ) : MeasurableConstVAdd (diagVecSubgroup Fq k n) (FFAdeleVec Fq k n) :=
  AddSubgroup.instMeasurableConstVAdd _

instance (n : ℕ) : VAddInvariantMeasure (diagVecSubgroup Fq k n) (FFAdeleVec Fq k n) (haarVec Fq k n) :=
  inferInstanceAs (VAddInvariantMeasure (diagVecSubgroup Fq k n).toAddSubmonoid (FFAdeleVec Fq k n)
    (haarVec Fq k n))

instance (n : ℕ) : Countable (diagVecSubgroup Fq k n) := by
  refine Function.Injective.countable (f := fun x : diagVecSubgroup Fq k n =>
    (fun i => (⟨(x.1 : Fin n → FFAdeleRing Fq k) i, x.2 i (Set.mem_univ i)⟩ : FFAdeleRing.diagSubgroup Fq k))) ?_
  intro x y h
  apply Subtype.ext
  funext i
  exact congrArg (fun z : Fin n → FFAdeleRing.diagSubgroup Fq k => (z i : FFAdeleRing Fq k)) h

theorem isAddFundamentalDomain_fundDomVec (hc : IsConstantField Fq k) {a b : Divisor Fq k}
    (ha : 2 * Rep.genusInt Fq k - 2 < Divisor.deg a) (hba : b ≤ a) (hb : Divisor.deg b < 0) (n : ℕ) :
    IsAddFundamentalDomain (diagVecSubgroup Fq k n) (fundDomVec a b n) (haarVec Fq k n) := by
  classical
  refine IsAddFundamentalDomain.mk' ?_ ?_
  · have : IsOpen (fundDomVec (Fq := Fq) (k := k) a b n) :=
      isOpen_set_pi Set.finite_univ fun i _ => FFAdeleRing.isOpen_fundDom a b
    exact this.measurableSet.nullMeasurableSet
  · intro x
    choose ζ hζ using fun i => exists_diag_mem_fundDom hc ha hba ((x : Fin n → FFAdeleRing Fq k) i)
    have hmemg : (fun i => (FFAdeleRing.diag (ζ i) : FFAdeleRing Fq k) : Fin n → FFAdeleRing Fq k) ∈
        diagVecSubgroup Fq k n := fun i _ => FFAdeleRing.mem_diagSubgroup.2 ⟨ζ i, rfl⟩
    refine ⟨⟨_, hmemg⟩, fun i _ => hζ i, ?_⟩
    rintro ⟨y, hy⟩ hy'
    apply Subtype.ext
    funext i
    obtain ⟨ξ, hξ⟩ := FFAdeleRing.mem_diagSubgroup.1 (hy i (Set.mem_univ i))
    have h1 : (FFAdeleRing.diag ξ : FFAdeleRing Fq k) + (x : Fin n → FFAdeleRing Fq k) i ∈
        FFAdeleRing.fundDom a b := by
      rw [hξ]; exact hy' i (Set.mem_univ i)
    have := FFAdeleRing.fundDom_unique hba hb _ h1 (hζ i)
    show y i = FFAdeleRing.diag (ζ i)
    rw [← hξ, this]

/-- $Q^{nz}=(Q^z)^n$ in $[0,\infty]$. -/
theorem ennreal_zpow_nat_mul {Q : ℝ≥0∞} (h0 : Q ≠ 0) (ht : Q ≠ ⊤) (n : ℕ) (z : ℤ) :
    Q ^ ((n : ℤ) * z) = (Q ^ z) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    push_cast
    rw [add_mul, one_mul, ENNReal.zpow_add h0 ht, ih, pow_succ]

/-- **Weil VI, Cor. 1 of Thm. 1** ($E=k^n$): if $\mathbb F_q$ is the field of constants, $\mu(E_{\mathbb A}/E)=
q^{n(g-1)}$ for the Haar measure $\mu$ with $\mu(\prod_v\mathfrak r_v^n)=1$. -/
@[kb "weil1973bnt" "Ch. VI, Cor. 1 (Thm. 1) (p. 100), E = k^n: mu(E_A/E) = q^(n(g-1))"]
theorem weil_VI_1_thm1_cor1_vec (hc : IsConstantField Fq k) (n : ℕ) :
    addCovolume (diagVecSubgroup Fq k n) (FFAdeleVec Fq k n) (haarVec Fq k n) =
      (Nat.card Fq : ℝ≥0∞) ^ ((n : ℤ) * (Rep.genusInt Fq k - 1)) := by
  classical
  obtain ⟨a, b, ha, hba, hb⟩ := FFAdeleRing.exists_ab hc
  haveI hfin := FFAdeleRing.finite_quotient_Hp hba
  haveI : Fintype (FFAdeleRing.U a ⧸ (FFAdeleRing.Hp a b).addSubgroupOf (FFAdeleRing.U a)) :=
    Fintype.ofFinite _
  set C := FFAdeleRing.U a ⧸ (FFAdeleRing.Hp a b).addSubgroupOf (FFAdeleRing.U a) with hC
  rw [(isAddFundamentalDomain_fundDomVec hc ha hba hb n).covolume_eq_volume (haarVec Fq k n)]
  -- the 1-dimensional computation
  have h1 : FFAdeleRing.haar Fq k (FFAdeleRing.fundDom a b) = (Nat.card Fq : ℝ≥0∞) ^ (Rep.genusInt Fq k - 1) := by
    rw [← FFAdeleRing.weil_VI_1_thm1_cor1 hc,
      (FFAdeleRing.isAddFundamentalDomain_fundDom hc ha hba hb).covolume_eq_volume (FFAdeleRing.haar Fq k)]
  rw [FFAdeleRing.haar_fundDom hba, FFAdeleRing.haar_U] at h1
  -- the n-dimensional decomposition
  set g : (Fin n → C) → FFAdeleVec Fq k n := fun c => (fun i => (Quotient.out (c i)).1 : Fin n → FFAdeleRing Fq k)
    with hg
  have hset : fundDomVec (Fq := Fq) (k := k) a b n =
      ⋃ c : Fin n → C, (fun x => -g c + x) ⁻¹' (boxSub (fun _ : Fin n => b) : Set (FFAdeleVec Fq k n)) := by
    ext x
    simp only [fundDomVec, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_iUnion,
      SetLike.mem_coe, mem_boxSub, FFAdeleRing.mem_fundDom]
    constructor
    · intro h
      choose c hc' using h
      exact ⟨c, fun i => hc' i⟩
    · rintro ⟨c, hc'⟩ i
      exact ⟨c i, hc' i⟩
  have key := FFAdeleRing.measure_iUnion_translates (haarVec Fq k n) g (boxSub (fun _ : Fin n => b))
    (isOpen_boxSub _).measurableSet (by
      intro c c' hcc'
      funext i
      exact FFAdeleRing.out_diff_mem (c i) (c' i)
        (FFAdeleRing.U_le_Hp a b ((mem_boxSub.1 hcc') i)))
  rw [← hset] at key
  rw [key, coe_boxSub, haarVec_pi_U, Fintype.card_fun, Fintype.card_fin,
    ← Nat.card_eq_fintype_card (α := C), Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hQ0 : (Nat.card Fq : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact (Nat.card_pos (α := Fq)).ne'
  have hQt : (Nat.card Fq : ℝ≥0∞) ≠ ⊤ := by simp
  push_cast
  rw [ennreal_zpow_nat_mul hQ0 hQt, ← mul_pow, h1, ennreal_zpow_nat_mul hQ0 hQt]

end NumberFieldKB.WeilBNT.FF
