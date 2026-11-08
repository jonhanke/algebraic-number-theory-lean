import NumberFieldKB.WeilBNT.FunctionField.AdeleMeasure
import Mathlib.Data.Finsupp.Encodable

/-!
# The Haar measure of $k_{\mathbb A}$ and the volume of $k_{\mathbb A}/k$ (Weil VI, $E=k$; IV.§2 Thm. 2)

For a global function field $k$ over $\mathbb F_q$ ($q=\lvert\mathbb F_q\rvert$):

* `FFAdeleRing.discreteTopology_diagSubgroup`, `FFAdeleRing.compactSpace_quotient`: Weil IV.§2, Thm. 2 for
  $E=k$ a function field: $k$ is discrete in $k_{\mathbb A}$ and $k_{\mathbb A}/k$ is compact.
* `FFAdeleRing.haar`: the Haar measure $\mu_1$ on $k_{\mathbb A}$ with $\mu_1(\prod_v\mathfrak r_v)=1$;
  **`FFAdeleRing.haar_U`**: $\mu_1(U(\mathfrak a))=q^{\deg\mathfrak a}$ (Weil VI.§1, Cor. 2 of Prop. 2 for $E=k$,
  $L=L(\mathfrak a)$, $\delta(L(\mathfrak a))=-\deg\mathfrak a$). Proof: $[U(\mathfrak a+v):U(\mathfrak a)]=q^{\deg v}$
  (the quotient is the residue field at $v$), and a subgroup of finite index $n$ has measure $1/n$ of the group.
* **`FFAdeleRing.weil_VI_1_thm1_cor1`**: Weil VI, Cor. 1 of Thm. 1 for $E=k$: $\mu_1(k_{\mathbb A}/k)=q^{g-1}$ (the
  covolume of $k$; $\mathbb F_q$ the field of constants). A fundamental domain: for $\deg\mathfrak a>2g-2$ and
  $\mathfrak b\le\mathfrak a$ with $\deg\mathfrak b<0$, the union of the translates $r+U(\mathfrak b)$, $r$ running
  over representatives of $U(\mathfrak a)/(U(\mathfrak b)+A(\mathfrak a))$.
-/

open scoped WithZero RestrictedProduct Pointwise NNReal ENNReal
open Valuation IsDedekindDomain Topology MeasureTheory

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace FFAdeleRing

variable (Fq k) in
/-- $k$ as a subgroup of $k_{\mathbb A}$ (the principal adeles). -/
def diagSubgroup : AddSubgroup (FFAdeleRing Fq k) :=
  (FFIdeleGroup.diagHom (Fq := Fq) (k := k)).toAddMonoidHom.range

theorem mem_diagSubgroup {x : FFAdeleRing Fq k} : x ∈ diagSubgroup Fq k ↔ ∃ ξ : k, diag ξ = x := Iff.rfl

theorem diag_injective : Function.Injective (diag : k → FFAdeleRing Fq k) := by
  obtain ⟨v⟩ := Place.nonempty (Fq := Fq) (k := k)
  intro x y h
  have := congrArg (fun z : FFAdeleRing Fq k => z v) h
  exact v.toCompletion.injective this

theorem diag_zero : (diag 0 : FFAdeleRing Fq k) = 0 :=
  (FFIdeleGroup.diagHom (Fq := Fq) (k := k)).map_zero

theorem diag_sub (x y : k) : (diag (x - y) : FFAdeleRing Fq k) = diag x - diag y :=
  (FFIdeleGroup.diagHom (Fq := Fq) (k := k)).map_sub x y

theorem diag_add (x y : k) : (diag (x + y) : FFAdeleRing Fq k) = diag x + diag y :=
  (FFIdeleGroup.diagHom (Fq := Fq) (k := k)).map_add x y

theorem diagSubgroup_inter_U_neg {b : Divisor Fq k} (hb : Divisor.deg b < 0) {ξ : k}
    (h : diag ξ ∈ U b) : ξ = 0 := by
  rw [diag_mem_U_iff, Divisor.riemannRochSpace_eq_bot_of_deg_neg hb] at h
  simpa using h

theorem exists_deg_neg : ∃ b : Divisor Fq k, Divisor.deg b < 0 := by
  obtain ⟨v⟩ := Place.nonempty (Fq := Fq) (k := k)
  refine ⟨-(Finsupp.single v 1), ?_⟩
  rw [_root_.map_neg, Divisor.deg_single]
  have := v.degree_pos
  push_cast; omega

/-- **Weil IV.§2, Thm. 2** ($E=k$ a function field), first half: $k$ is discrete in $k_{\mathbb A}$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Thm. 2 (p. 64), k discrete in k_A, function fields"]
theorem discreteTopology_diagSubgroup : DiscreteTopology (diagSubgroup Fq k) := by
  obtain ⟨b, hb⟩ := exists_deg_neg (Fq := Fq) (k := k)
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have : ({0} : Set (diagSubgroup Fq k)) = Subtype.val ⁻¹' (U b : Set (FFAdeleRing Fq k)) := by
    ext ⟨x, hx⟩
    obtain ⟨ξ, rfl⟩ := mem_diagSubgroup.1 hx
    simp only [Set.mem_singleton_iff, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro h
      have : diag ξ = 0 := congrArg Subtype.val h
      rw [this]; exact (U b).zero_mem
    · intro h
      have := diagSubgroup_inter_U_neg hb h
      subst this
      exact Subtype.ext diag_zero
  rw [this]
  exact (isOpen_U b).preimage continuous_subtype_val

theorem divisor_induction_le {P : Divisor Fq k → Prop} {a0 : Divisor Fq k}
    (h0 : P a0) (step : ∀ a, a0 ≤ a → ∀ v, P a → P (a + Finsupp.single v 1)) :
    ∀ b, a0 ≤ b → P b := by
  suffices H : ∀ (n : ℕ) (b : Divisor Fq k), a0 ≤ b → (Divisor.deg (b - a0)).toNat = n → P b from
    fun b hb => H _ b hb rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hab hn
    by_cases heq : a0 = b
    · subst heq; exact h0
    · obtain ⟨v, hv⟩ : ∃ v, a0 v ≠ b v := by
        by_contra hcon
        push Not at hcon
        exact heq (Finsupp.ext hcon)
      have hlt : a0 v < b v := lt_of_le_of_ne (hab v) hv
      have hab' : a0 ≤ b - Finsupp.single v 1 := by
        intro w
        by_cases hw : w = v
        · subst hw; simp; omega
        · simpa [Finsupp.single_apply, Ne.symm hw] using hab w
      have hd : Divisor.deg ((b - Finsupp.single v 1) - a0) = Divisor.deg (b - a0) - v.degree := by
        rw [sub_right_comm, _root_.map_sub, Divisor.deg_single]; simp
      have hdp := v.degree_pos
      have hnn : 0 ≤ Divisor.deg (b - a0) := Divisor.deg_nonneg (sub_nonneg.mpr hab)
      have hlt' : (Divisor.deg ((b - Finsupp.single v 1) - a0)).toNat < n := by
        have hnn2 := Divisor.deg_nonneg (sub_nonneg.mpr hab')
        rw [hd] at hnn2
        rw [← hn, hd]
        omega
      have := step _ hab' v (ih _ hlt' _ hab' rfl)
      simpa using this

theorem key_lt_exp (y : ℤᵐ⁰) (n : ℤ) : WithZero.exp (-n) * y < 1 ↔ y ≤ WithZero.exp (n - 1) := by
  rcases eq_or_ne y 0 with rfl | h
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m : ℤ, y = WithZero.exp m := ⟨WithZero.log y, (WithZero.exp_log h).symm⟩
    rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem valued_zpow {v : Place Fq k} {p : v.Completion} (hp : Valued.v p = WithZero.exp (-1)) (n : ℤ) :
    Valued.v (p ^ n) = WithZero.exp (-n) := by
  rw [map_zpow₀, hp, ← WithZero.exp_zsmul]; simp

def adeleSingle (v : Place Fq k) (y : v.Completion) : FFAdeleRing Fq k := by
  classical
  exact ⟨Function.update (0 : ∀ w : Place Fq k, w.Completion) v y, by
    filter_upwards [show {v}ᶜ ∈ Filter.cofinite by simp] with w hw
    rw [Function.update_of_ne (by simpa using hw)]
    exact (w.completionIntegers).zero_mem⟩

theorem adeleSingle_same (v : Place Fq k) (y : v.Completion) : adeleSingle v y v = y := by
  classical
  exact Function.update_self v y _

theorem adeleSingle_ne (v : Place Fq k) (y : v.Completion) {w : Place Fq k} (h : w ≠ v) :
    adeleSingle v y w = 0 := by
  classical
  exact Function.update_of_ne h y _

/-- A uniformizer of the completion. -/
def uniC (v : Place Fq k) : v.Completion := (v.valued_surjective (WithZero.exp (-1))).choose

theorem valued_uniC (v : Place Fq k) : Valued.v (uniC v) = WithZero.exp (-1) :=
  (v.valued_surjective (WithZero.exp (-1))).choose_spec

theorem uniC_ne_zero (v : Place Fq k) : uniC v ≠ 0 := by
  intro h
  have := valued_uniC v
  rw [h, map_zero] at this
  exact WithZero.exp_ne_zero this.symm

theorem add_single_apply_self (a : Divisor Fq k) (v : Place Fq k) :
    ((a + Finsupp.single v 1 : Divisor Fq k) v) = a v + 1 := by simp

theorem add_single_apply_ne (a : Divisor Fq k) {v w : Place Fq k} (h : w ≠ v) :
    ((a + Finsupp.single v 1 : Divisor Fq k) w) = a w := by simp [Finsupp.single_apply, Ne.symm h]

theorem resElt_mem (a : Divisor Fq k) (v : Place Fq k) (x : U (a + Finsupp.single v 1)) :
    Valued.v (uniC v ^ (a v + 1) * (x.1 v)) ≤ 1 := by
  have hx := (mem_U_iff _ _).1 x.2 v
  rw [add_single_apply_self] at hx
  rw [map_mul, valued_zpow (valued_uniC v)]
  calc WithZero.exp (-(a v + 1)) * Valued.v (x.1 v)
      ≤ WithZero.exp (-(a v + 1)) * WithZero.exp (a v + 1) := by gcongr
    _ = 1 := by rw [← WithZero.exp_add]; simp

/-- The residue map $U(\mathfrak a+v)\to\kappa(v)$. -/
def resU (a : Divisor Fq k) (v : Place Fq k) :
    U (a + Finsupp.single v 1) →+ IsLocalRing.ResidueField (Valued.v : Valuation v.Completion ℤᵐ⁰).integer where
  toFun x := IsLocalRing.residue (Valued.v : Valuation v.Completion ℤᵐ⁰).integer
    ⟨uniC v ^ (a v + 1) * (x.1 v), (Valuation.mem_integer_iff _ _).2 (resElt_mem a v x)⟩
  map_zero' := by
    rw [← map_zero (IsLocalRing.residue (Valued.v : Valuation v.Completion ℤᵐ⁰).integer)]
    congr 1
    apply Subtype.ext
    simp
  map_add' x y := by
    rw [← map_add]
    congr 1
    apply Subtype.ext
    simp [mul_add]

theorem resU_eq_zero_iff (a : Divisor Fq k) (v : Place Fq k) (x : U (a + Finsupp.single v 1)) :
    resU a v x = 0 ↔ (x : FFAdeleRing Fq k) ∈ U a := by
  show IsLocalRing.residue _ _ = 0 ↔ _
  rw [Place.residue_eq_zero_iff_completion]
  show Valued.v (uniC v ^ (a v + 1) * x.1 v) < 1 ↔ _
  rw [map_mul, valued_zpow (valued_uniC v), key_lt_exp, add_sub_cancel_right]
  constructor
  · intro h w
    by_cases hw : w = v
    · subst hw; exact h
    · have := (mem_U_iff _ _).1 x.2 w
      rwa [add_single_apply_ne a hw] at this
  · intro h; exact h v

theorem resU_surjective (a : Divisor Fq k) (v : Place Fq k) : Function.Surjective (resU a v) := by
  intro r
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
  have hy : Valued.v (y : v.Completion) ≤ 1 := y.2
  have hx : adeleSingle v (uniC v ^ (-(a v + 1)) * (y : v.Completion)) ∈ U (a + Finsupp.single v 1) := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [adeleSingle_same, map_mul, valued_zpow (valued_uniC w), add_single_apply_self, neg_neg]
      calc WithZero.exp (a w + 1) * Valued.v (y : w.Completion) ≤ WithZero.exp (a w + 1) * 1 := by gcongr
        _ = _ := mul_one _
    · rw [adeleSingle_ne _ _ hw, map_zero]; exact zero_le'
  refine ⟨⟨_, hx⟩, ?_⟩
  show IsLocalRing.residue _ _ = _
  congr 1
  apply Subtype.ext
  show uniC v ^ (a v + 1) * (adeleSingle v (uniC v ^ (-(a v + 1)) * (y : v.Completion))) v = y
  rw [adeleSingle_same, ← mul_assoc, ← zpow_add₀ (uniC_ne_zero v)]
  simp

/-- $U(\mathfrak a+v)/U(\mathfrak a)\cong\kappa(v)$ (residue field of the completion). -/
def quotEquivResidue (a : Divisor Fq k) (v : Place Fq k) :
    (U (a + Finsupp.single v 1) ⧸ (U a).addSubgroupOf (U (a + Finsupp.single v 1))) ≃+
      IsLocalRing.ResidueField (Valued.v : Valuation v.Completion ℤᵐ⁰).integer :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, resU_eq_zero_iff]
    : (U a).addSubgroupOf (U (a + Finsupp.single v 1)) = (resU a v).ker)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (resU a v) (resU_surjective a v))

theorem finite_quotient_U_single_aux (a : Divisor Fq k) (v : Place Fq k) :
    Finite (U (a + Finsupp.single v 1) ⧸ (U a).addSubgroupOf (U (a + Finsupp.single v 1))) :=
  have := v.finite_residueField_completion
  Finite.of_equiv _ (quotEquivResidue a v).symm.toEquiv

theorem card_quotient_U_single_aux (a : Divisor Fq k) (v : Place Fq k) :
    Nat.card (U (a + Finsupp.single v 1) ⧸ (U a).addSubgroupOf (U (a + Finsupp.single v 1))) =
      Nat.card Fq ^ v.degree := by
  rw [Nat.card_congr (quotEquivResidue a v).toEquiv, Place.card_residueField_completion]

theorem isCompact_U_add_single (a : Divisor Fq k) (v : Place Fq k)
    (h : IsCompact (U a : Set (FFAdeleRing Fq k))) :
    IsCompact (U (a + Finsupp.single v 1) : Set (FFAdeleRing Fq k)) := by
  haveI := finite_quotient_U_single_aux a v
  haveI := Fintype.ofFinite
    (U (a + Finsupp.single v 1) ⧸ (U a).addSubgroupOf (U (a + Finsupp.single v 1)))
  refine IsCompact.of_isClosed_subset
    (isCompact_iUnion fun c : (U (a + Finsupp.single v 1) ⧸ (U a).addSubgroupOf (U (a + Finsupp.single v 1))) =>
      h.image (continuous_const.add continuous_id : Continuous fun x : FFAdeleRing Fq k => (Quotient.out c).1 + x))
    (AddSubgroup.isClosed_of_isOpen _ (isOpen_U _)) ?_
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨QuotientAddGroup.mk ⟨x, hx⟩, -(Quotient.out (QuotientAddGroup.mk (⟨x, hx⟩ : U (a + Finsupp.single v 1)) :
    U (a + Finsupp.single v 1) ⧸ (U a).addSubgroupOf (U (a + Finsupp.single v 1)))).1 + x, ?_, by abel⟩
  have h2 := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (⟨x, hx⟩ : U (a + Finsupp.single v 1)) :
    U (a + Finsupp.single v 1) ⧸ (U a).addSubgroupOf (U (a + Finsupp.single v 1))))
  exact h2

theorem isCompact_U (a : Divisor Fq k) : IsCompact (U a : Set (FFAdeleRing Fq k)) := by
  have h0 : ∀ b : Divisor Fq k, 0 ≤ b → IsCompact (U b : Set (FFAdeleRing Fq k)) :=
    divisor_induction_le (Fq := Fq) (k := k) (P := fun b => IsCompact (U b : Set (FFAdeleRing Fq k))) (a0 := 0) isCompact_U_zero
      (fun b _ v hb => isCompact_U_add_single b v hb)
  exact (h0 (a ⊔ 0) le_sup_right).of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (isOpen_U a))
    (U_mono le_sup_left)

/-- **Weil IV.§2, Thm. 2** ($E=k$ a function field), second half: $k_{\mathbb A}/k$ is compact. -/
@[kb "weil1973bnt" "Ch. IV, §2, Thm. 2 (p. 64), k_A/k compact, function fields"]
theorem compactSpace_quotient : CompactSpace (FFAdeleRing Fq k ⧸ diagSubgroup Fq k) := by
  refine ⟨?_⟩
  set b : Divisor Fq k := Rep.maxDefect Fq k ⊔ 0
  have hb : Rep.maxDefect Fq k ≤ b := le_sup_left
  have : (QuotientAddGroup.mk '' (U b : Set (FFAdeleRing Fq k)) : Set (FFAdeleRing Fq k ⧸ diagSubgroup Fq k))
      = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨ξ, hξ⟩ := exists_sub_diag_mem_U_of_S_eq_top (Rep.S_eq_top hb) x
    refine ⟨x - diag ξ, hξ, ?_⟩
    rw [QuotientAddGroup.eq]
    simpa using (mem_diagSubgroup.2 ⟨ξ, rfl⟩ : diag ξ ∈ diagSubgroup Fq k)
  rw [← this]
  exact (isCompact_U b).image continuous_quot_mk

instance : MeasurableSpace (FFAdeleRing Fq k) := borel _

instance : BorelSpace (FFAdeleRing Fq k) := ⟨rfl⟩

/-- $\prod_v\mathfrak r_v=U(0)$ as a compact set with nonempty interior. -/
def U0Compacts : TopologicalSpace.PositiveCompacts (FFAdeleRing Fq k) :=
  ⟨⟨(U (0 : Divisor Fq k) : Set (FFAdeleRing Fq k)), isCompact_U_zero⟩, ⟨0, by
    show (0 : FFAdeleRing Fq k) ∈ interior (U (0 : Divisor Fq k) : Set (FFAdeleRing Fq k))
    rw [(isOpen_U 0).interior_eq]; exact (U 0).zero_mem⟩⟩

variable (Fq k) in
/-- **The Haar measure $\mu_1$ of $k_{\mathbb A}$** with $\mu_1(\prod_v\mathfrak r_v)=1$ (Weil VI.§1, Cor. 2 of
Prop. 2, and VI, Cor. 1 of Thm. 1). -/
def haar : Measure (FFAdeleRing Fq k) := Measure.addHaarMeasure U0Compacts

instance : (haar Fq k).IsAddHaarMeasure := by unfold haar; infer_instance

theorem haar_U_zero : haar Fq k (U (0 : Divisor Fq k) : Set (FFAdeleRing Fq k)) = 1 :=
  Measure.addHaarMeasure_self

theorem measure_iUnion_translates {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : Measure G) [μ.IsAddLeftInvariant] {ι : Type*} [Fintype ι] (g : ι → G) (H : AddSubgroup G)
    (hH : MeasurableSet (H : Set G)) (hdisj : ∀ i j, -g i + g j ∈ H → i = j) :
    μ (⋃ i, (fun x => -g i + x) ⁻¹' (H : Set G)) = Fintype.card ι * μ (H : Set G) := by
  have hmeas : ∀ i, MeasurableSet ((fun x => -g i + x) ⁻¹' (H : Set G)) :=
    fun i => (measurable_const_add _) hH
  rw [measure_iUnion ?_ hmeas, tsum_fintype]
  · simp [measure_preimage_add]
  · intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hi hj
    apply hij
    apply hdisj
    have h1 := H.sub_mem hi hj
    have e : -g i + g j = (-g i + x) - (-g j + x) := by simp [sub_eq_add_neg, add_assoc]
    rw [e]; exact h1

/-- A subgroup $H$ of finite index $n$ in $K$ has $\mu(K)=n\,\mu(H)$ (any left invariant measure). -/
theorem measure_eq_card_mul {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : Measure G) [μ.IsAddLeftInvariant] {H K : AddSubgroup G} (hHK : H ≤ K)
    (hH : MeasurableSet (H : Set G)) [Finite (K ⧸ H.addSubgroupOf K)] :
    μ (K : Set G) = Nat.card (K ⧸ H.addSubgroupOf K) * μ (H : Set G) := by
  haveI := Fintype.ofFinite (K ⧸ H.addSubgroupOf K)
  have key := measure_iUnion_translates μ (fun c : K ⧸ H.addSubgroupOf K => (Quotient.out c).1) H hH
    (by
      intro i j hij
      have : (-(Quotient.out i) + Quotient.out j : K) ∈ H.addSubgroupOf K := by
        rw [AddSubgroup.mem_addSubgroupOf]; simpa using hij
      have h2 := QuotientAddGroup.eq.2 this
      rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h2)
  have hset : (⋃ c : K ⧸ H.addSubgroupOf K, (fun x => -(Quotient.out c).1 + x) ⁻¹' (H : Set G)) = K := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨c, hc⟩
      have := K.add_mem (Quotient.out c).2 (hHK hc)
      simpa using this
    · intro hx
      refine ⟨QuotientAddGroup.mk ⟨x, hx⟩, ?_⟩
      have h2 := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (⟨x, hx⟩ : K) : K ⧸ H.addSubgroupOf K))
      rw [AddSubgroup.mem_addSubgroupOf] at h2
      simpa using h2
  rw [hset] at key
  rw [key, Nat.card_eq_fintype_card]

instance finite_quotient_U_single (a : Divisor Fq k) (v : Place Fq k) :
    Finite (U (a + Finsupp.single v 1) ⧸ (U a).addSubgroupOf (U (a + Finsupp.single v 1))) :=
  finite_quotient_U_single_aux a v

/-- $[U(\mathfrak a+v):U(\mathfrak a)]=q^{\deg v}$. -/
theorem card_quotient_U_single (a : Divisor Fq k) (v : Place Fq k) :
    Nat.card (U (a + Finsupp.single v 1) ⧸ (U a).addSubgroupOf (U (a + Finsupp.single v 1))) =
      Nat.card Fq ^ v.degree :=
  card_quotient_U_single_aux a v

theorem relIndex_U (a0 : Divisor Fq k) (b : Divisor Fq k) (h : a0 ≤ b) :
    (U a0).relIndex (U b) = Nat.card Fq ^ (Divisor.deg b - Divisor.deg a0).toNat := by
  refine divisor_induction_le (Fq := Fq) (k := k)
    (P := fun b => (U a0).relIndex (U b) = Nat.card Fq ^ (Divisor.deg b - Divisor.deg a0).toNat)
    (a0 := a0) (by simp) ?_ b h
  intro a ha v hP
  rw [← AddSubgroup.relIndex_mul_relIndex (U a0) (U a) (U (a + Finsupp.single v 1)) (U_mono ha)
    (U_mono (by simp)), hP]
  have h2 : (U a).relIndex (U (a + Finsupp.single v 1)) = Nat.card Fq ^ v.degree :=
    card_quotient_U_single_aux a v
  rw [h2, ← pow_add]
  congr 1
  have hnn : 0 ≤ Divisor.deg a - Divisor.deg a0 := by
    rw [← _root_.map_sub]; exact Divisor.deg_nonneg (sub_nonneg.mpr ha)
  rw [_root_.map_add, Divisor.deg_single]
  simp only [one_mul]
  omega

theorem haar_U_of_le {a b : Divisor Fq k} (h : a ≤ b) :
    haar Fq k (U b : Set (FFAdeleRing Fq k)) =
      (Nat.card Fq : ℝ≥0∞) ^ (Divisor.deg b - Divisor.deg a).toNat * haar Fq k (U a : Set (FFAdeleRing Fq k)) := by
  have hne : (U a).relIndex (U b) ≠ 0 := by
    rw [relIndex_U a b h]
    exact pow_ne_zero _ (Nat.card_pos (α := Fq)).ne'
  haveI : Finite (U b ⧸ (U a).addSubgroupOf (U b)) :=
    Nat.finite_of_card_ne_zero hne
  rw [measure_eq_card_mul (haar Fq k) (U_mono h) (isOpen_U a).measurableSet]
  congr 1
  have : Nat.card (U b ⧸ (U a).addSubgroupOf (U b)) = Nat.card Fq ^ (Divisor.deg b - Divisor.deg a).toNat :=
    relIndex_U a b h
  rw [this]; push_cast; rfl

/-- **Weil VI.§1, Cor. 2 of Prop. 2** ($E=k$): $\mu_1(U(\mathfrak a))=q^{\deg\mathfrak a}$. -/
@[kb "weil1973bnt" "Ch. VI, §1, Cor. 2 of Prop. 2 (p. 98), E = k: mu(U(a)) = q^deg a"]
theorem haar_U (a : Divisor Fq k) : haar Fq k (U a : Set (FFAdeleRing Fq k)) = (Nat.card Fq : ℝ≥0∞) ^ Divisor.deg a := by
  set c : Divisor Fq k := a ⊔ 0
  have h1 := haar_U_of_le (le_sup_left : a ≤ c)
  have h2 := haar_U_of_le (le_sup_right : (0 : Divisor Fq k) ≤ c)
  rw [haar_U_zero, _root_.map_zero, sub_zero, mul_one] at h2
  have hca : Divisor.deg a ≤ Divisor.deg c := by
    have := Divisor.deg_nonneg (sub_nonneg.mpr (le_sup_left : a ≤ c)); rwa [_root_.map_sub, sub_nonneg] at this
  have hc0 : 0 ≤ Divisor.deg c := Divisor.deg_nonneg (le_sup_right : (0 : Divisor Fq k) ≤ c)
  set Q : ℝ≥0∞ := (Nat.card Fq : ℝ≥0∞)
  have hQ0 : Q ≠ 0 := by
    simp only [Q, ne_eq, Nat.cast_eq_zero]; exact (Nat.card_pos (α := Fq)).ne'
  have hQt : Q ≠ ⊤ := by simp [Q]
  set m := (Divisor.deg c - Divisor.deg a).toNat
  have hm : (m : ℤ) = Divisor.deg c - Divisor.deg a := by omega
  have hn : ((Divisor.deg c).toNat : ℤ) = Divisor.deg c := by omega
  have h3 : Q ^ (Divisor.deg c).toNat = Q ^ (Divisor.deg a) * Q ^ m := by
    rw [← zpow_natCast, ← zpow_natCast Q m, ← ENNReal.zpow_add hQ0 hQt, hn]
    congr 1; omega
  rw [h2] at h1
  rw [h3, mul_comm] at h1
  exact ((ENNReal.mul_right_inj (pow_ne_zero _ hQ0) (ENNReal.pow_ne_top hQt)).1 h1).symm

instance : Countable (diagSubgroup Fq k) := by
  haveI : Countable (RatFunc Fq) := by
    haveI : Countable (Polynomial Fq) := by
      refine Function.Injective.countable (f := fun p : Polynomial Fq =>
        Finsupp.onFinset p.support p.coeff (fun n h => Polynomial.mem_support_iff.2 h)) ?_
      intro p q h
      ext n
      have := congrArg (fun f : ℕ →₀ Fq => f n) h
      simpa using this
    have : Function.Surjective (fun p : Polynomial Fq × Polynomial Fq =>
        algebraMap (Polynomial Fq) (RatFunc Fq) p.1 / algebraMap (Polynomial Fq) (RatFunc Fq) p.2) := by
      intro x
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial Fq) x
      exact ⟨(a, b), rfl⟩
    exact this.countable
  haveI : Countable k :=
    Countable.of_equiv _ (Module.finBasis (RatFunc Fq) k).equivFun.toEquiv.symm
  have : Function.Surjective fun ξ : k => (⟨diag ξ, mem_diagSubgroup.2 ⟨ξ, rfl⟩⟩ : diagSubgroup Fq k) := by
    rintro ⟨x, hx⟩
    obtain ⟨ξ, rfl⟩ := mem_diagSubgroup.1 hx
    exact ⟨ξ, rfl⟩
  exact this.countable

theorem diag_neg (x : k) : (diag (-x) : FFAdeleRing Fq k) = -diag x :=
  (FFIdeleGroup.diagHom (Fq := Fq) (k := k)).map_neg x

theorem finite_quotient_U_of_le {a b : Divisor Fq k} (h : b ≤ a) :
    Finite (U a ⧸ (U b).addSubgroupOf (U a)) :=
  Nat.finite_of_card_ne_zero (by
    have : Nat.card (U a ⧸ (U b).addSubgroupOf (U a)) =
        Nat.card Fq ^ (Divisor.deg a - Divisor.deg b).toNat := relIndex_U b a h
    rw [this]; exact pow_ne_zero _ (Nat.card_pos (α := Fq)).ne')

/-- $U(\mathfrak b)+A(\mathfrak a)$. -/
def Hp (a b : Divisor Fq k) : AddSubgroup (FFAdeleRing Fq k) :=
  U b ⊔ (a.riemannRochSpace.toAddSubgroup).map (FFIdeleGroup.diagHom (Fq := Fq) (k := k)).toAddMonoidHom

theorem mem_Hp (a b : Divisor Fq k) {x : FFAdeleRing Fq k} :
    x ∈ Hp a b ↔ ∃ h ∈ U b, ∃ ξ ∈ a.riemannRochSpace, h + diag ξ = x := by
  unfold Hp
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨h, hh, z, hz, rfl⟩
    obtain ⟨ξ, hξ, rfl⟩ := AddSubgroup.mem_map.1 hz
    exact ⟨h, hh, ξ, hξ, rfl⟩
  · rintro ⟨h, hh, ξ, hξ, rfl⟩
    exact ⟨h, hh, diag ξ, AddSubgroup.mem_map.2 ⟨ξ, hξ, rfl⟩, rfl⟩

theorem U_le_Hp (a b : Divisor Fq k) : U b ≤ Hp a b := le_sup_left

theorem Hp_le {a b : Divisor Fq k} (hba : b ≤ a) : Hp a b ≤ U a := by
  intro x hx
  obtain ⟨h, hh, ξ, hξ, rfl⟩ := (mem_Hp a b).1 hx
  exact (U a).add_mem (U_mono hba hh) ((diag_mem_U_iff a ξ).2 hξ)

theorem isOpen_Hp (a b : Divisor Fq k) : IsOpen (Hp a b : Set (FFAdeleRing Fq k)) :=
  AddSubgroup.isOpen_mono (U_le_Hp a b) (isOpen_U b)

theorem finite_riemannRochSpace {a b : Divisor Fq k} (hba : b ≤ a) (hb : Divisor.deg b < 0) :
    Finite a.riemannRochSpace := by
  haveI := finite_quotient_U_of_le hba
  refine Finite.of_injective (fun η : a.riemannRochSpace =>
    (QuotientAddGroup.mk (⟨diag (η : k), (diag_mem_U_iff a _).2 η.2⟩ : U a) :
      U a ⧸ (U b).addSubgroupOf (U a))) ?_
  intro η1 η2 h
  have h1 := QuotientAddGroup.eq.1 h
  rw [AddSubgroup.mem_addSubgroupOf] at h1
  have h2 : -diag (η1 : k) + diag (η2 : k) ∈ U b := by simpa using h1
  rw [show -diag (η1 : k) + diag (η2 : k) = (diag ((η2 : k) - η1) : FFAdeleRing Fq k) by
    rw [diag_sub]; abel] at h2
  have := diagSubgroup_inter_U_neg hb h2
  exact Subtype.ext (sub_eq_zero.1 this).symm

theorem natCard_riemannRochSpace {a b : Divisor Fq k} (hba : b ≤ a) (hb : Divisor.deg b < 0) :
    Nat.card a.riemannRochSpace = Nat.card Fq ^ a.ell := by
  haveI := finite_riemannRochSpace hba hb
  haveI : Module.Finite Fq a.riemannRochSpace := Module.Finite.of_finite
  exact Module.natCard_eq_pow_finrank (K := Fq) (V := a.riemannRochSpace)

theorem haar_Hp {a b : Divisor Fq k} (hba : b ≤ a) (hb : Divisor.deg b < 0) :
    haar Fq k (Hp a b : Set (FFAdeleRing Fq k)) =
      (Nat.card Fq : ℝ≥0∞) ^ a.ell * haar Fq k (U b : Set (FFAdeleRing Fq k)) := by
  haveI := finite_riemannRochSpace hba hb
  haveI := Fintype.ofFinite a.riemannRochSpace
  have key := measure_iUnion_translates (haar Fq k) (fun η : a.riemannRochSpace => diag (η : k))
    (U b) (isOpen_U b).measurableSet (by
      intro i j hij
      have h2 : (diag ((j : k) - i) : FFAdeleRing Fq k) ∈ U b := by
        rw [diag_sub, sub_eq_neg_add]; exact hij
      have := diagSubgroup_inter_U_neg hb h2
      exact Subtype.ext (sub_eq_zero.1 this).symm)
  have hset : (⋃ η : a.riemannRochSpace, (fun x => -(diag (η : k) : FFAdeleRing Fq k) + x) ⁻¹'
      (U b : Set (FFAdeleRing Fq k))) = Hp a b := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨η, hη⟩
      exact (mem_Hp a b).2 ⟨-diag (η : k) + x, hη, η, η.2, by abel⟩
    · intro hx
      obtain ⟨h, hh, ξ, hξ, rfl⟩ := (mem_Hp a b).1 hx
      exact ⟨⟨ξ, hξ⟩, by rw [show -(diag ξ : FFAdeleRing Fq k) + (h + diag ξ) = h by abel]; exact hh⟩
  rw [hset] at key
  rw [key, ← Nat.card_eq_fintype_card, natCard_riemannRochSpace hba hb]
  push_cast; rfl

theorem finite_quotient_Hp {a b : Divisor Fq k} (hba : b ≤ a) :
    Finite (U a ⧸ (Hp a b).addSubgroupOf (U a)) := by
  have h1 := AddSubgroup.relIndex_mul_relIndex (U b) (Hp a b) (U a) (U_le_Hp a b) (Hp_le hba)
  have hne : (U b).relIndex (U a) ≠ 0 := by
    rw [relIndex_U b a hba]; exact pow_ne_zero _ (Nat.card_pos (α := Fq)).ne'
  refine Nat.finite_of_card_ne_zero (fun h0 => hne ?_)
  rw [← h1]
  have : (Hp a b).relIndex (U a) = 0 := h0
  rw [this, mul_zero]

/-- The fundamental domain $\bigcup_r (r+U(\mathfrak b))$. -/
def fundDom (a b : Divisor Fq k) : Set (FFAdeleRing Fq k) :=
  ⋃ c : U a ⧸ (Hp a b).addSubgroupOf (U a),
    (fun x => -(Quotient.out c).1 + x) ⁻¹' (U b : Set (FFAdeleRing Fq k))

theorem isOpen_fundDom (a b : Divisor Fq k) : IsOpen (fundDom a b) :=
  isOpen_iUnion fun c => (isOpen_U b).preimage (continuous_const.add continuous_id)

theorem mem_fundDom {a b : Divisor Fq k} {x : FFAdeleRing Fq k} :
    x ∈ fundDom a b ↔ ∃ c : U a ⧸ (Hp a b).addSubgroupOf (U a), -(Quotient.out c).1 + x ∈ U b := by
  simp [fundDom]

theorem out_diff_mem {a b : Divisor Fq k} (i j : U a ⧸ (Hp a b).addSubgroupOf (U a))
    (h : -(Quotient.out i).1 + (Quotient.out j).1 ∈ Hp a b) : i = j := by
  have : (-(Quotient.out i) + Quotient.out j : U a) ∈ (Hp a b).addSubgroupOf (U a) := by
    rw [AddSubgroup.mem_addSubgroupOf]; simpa using h
  have h2 := QuotientAddGroup.eq.2 this
  rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h2

theorem haar_fundDom {a b : Divisor Fq k} (hba : b ≤ a) :
    haar Fq k (fundDom a b) = Nat.card (U a ⧸ (Hp a b).addSubgroupOf (U a)) *
      haar Fq k (U b : Set (FFAdeleRing Fq k)) := by
  haveI := finite_quotient_Hp hba
  haveI := Fintype.ofFinite (U a ⧸ (Hp a b).addSubgroupOf (U a))
  have key := measure_iUnion_translates (haar Fq k)
    (fun c : U a ⧸ (Hp a b).addSubgroupOf (U a) => (Quotient.out c).1) (U b)
    (isOpen_U b).measurableSet (fun i j hij => out_diff_mem i j (U_le_Hp a b hij))
  rw [fundDom, key, Nat.card_eq_fintype_card]

theorem haar_U_eq {a b : Divisor Fq k} (hba : b ≤ a) (hb : Divisor.deg b < 0) :
    haar Fq k (U a : Set (FFAdeleRing Fq k)) =
      (Nat.card Fq : ℝ≥0∞) ^ a.ell * haar Fq k (fundDom a b) := by
  haveI := finite_quotient_Hp hba
  rw [measure_eq_card_mul (haar Fq k) (Hp_le hba) (isOpen_Hp a b).measurableSet, haar_Hp hba hb,
    haar_fundDom hba]
  ring

theorem fundDom_unique {a b : Divisor Fq k} (hba : b ≤ a) (hb : Divisor.deg b < 0) (x : FFAdeleRing Fq k)
    {ζ₁ ζ₂ : k} (h₁ : diag ζ₁ + x ∈ fundDom a b) (h₂ : diag ζ₂ + x ∈ fundDom a b) : ζ₁ = ζ₂ := by
  obtain ⟨c₁, hc₁⟩ := mem_fundDom.1 h₁
  obtain ⟨c₂, hc₂⟩ := mem_fundDom.1 h₂
  set o₁ := (Quotient.out c₁).1 with ho₁
  set o₂ := (Quotient.out c₂).1 with ho₂
  have hoa₁ : o₁ ∈ U a := (Quotient.out c₁).2
  have hoa₂ : o₂ ∈ U a := (Quotient.out c₂).2
  set y₁ := -o₁ + (diag ζ₁ + x) with hy₁
  set y₂ := -o₂ + (diag ζ₂ + x) with hy₂
  have e : (diag (ζ₁ - ζ₂) : FFAdeleRing Fq k) = (o₁ + y₁) - (o₂ + y₂) := by
    rw [diag_sub, hy₁, hy₂]; abel
  have hy₁b : y₁ ∈ U b := hc₁
  have hy₂b : y₂ ∈ U b := hc₂
  have hdU : diag (ζ₁ - ζ₂) ∈ U a := by
    rw [e]
    exact (U a).sub_mem ((U a).add_mem hoa₁ (U_mono hba hy₁b)) ((U a).add_mem hoa₂ (U_mono hba hy₂b))
  have hA : ζ₁ - ζ₂ ∈ a.riemannRochSpace := (diag_mem_U_iff a _).1 hdU
  have hH : -o₁ + o₂ ∈ Hp a b := by
    refine (mem_Hp a b).2 ⟨y₁ - y₂, (U b).sub_mem hy₁b hy₂b, ζ₂ - ζ₁, ?_, ?_⟩
    · rw [← neg_sub]; exact a.riemannRochSpace.neg_mem hA
    · rw [diag_sub, hy₁, hy₂]; abel
  have hc : c₁ = c₂ := out_diff_mem c₁ c₂ hH
  have ho : o₁ = o₂ := by rw [ho₁, ho₂, hc]
  have hz : (diag (ζ₁ - ζ₂) : FFAdeleRing Fq k) ∈ U b := by
    have : (diag (ζ₁ - ζ₂) : FFAdeleRing Fq k) = y₁ - y₂ := by rw [e, ← ho]; abel
    rw [this]; exact (U b).sub_mem hy₁b hy₂b
  exact sub_eq_zero.1 (diagSubgroup_inter_U_neg hb hz)

instance : MeasurableConstVAdd (diagSubgroup Fq k) (FFAdeleRing Fq k) :=
  AddSubgroup.instMeasurableConstVAdd _

instance : VAddInvariantMeasure (diagSubgroup Fq k) (FFAdeleRing Fq k) (haar Fq k) :=
  inferInstanceAs (VAddInvariantMeasure (diagSubgroup Fq k).toAddSubmonoid (FFAdeleRing Fq k) (haar Fq k))

theorem isAddFundamentalDomain_fundDom (hc : IsConstantField Fq k) {a b : Divisor Fq k}
    (ha : 2 * Rep.genusInt Fq k - 2 < Divisor.deg a) (hba : b ≤ a) (hb : Divisor.deg b < 0) :
    IsAddFundamentalDomain (diagSubgroup Fq k) (fundDom a b) (haar Fq k) := by
  refine IsAddFundamentalDomain.mk' (isOpen_fundDom a b).measurableSet.nullMeasurableSet ?_
  intro x
  obtain ⟨ξ, hξ⟩ := weil_VI_2_cor3_adelic hc ha x
  set c : U a ⧸ (Hp a b).addSubgroupOf (U a) := QuotientAddGroup.mk (⟨x - diag ξ, hξ⟩ : U a) with hcdef
  have h2 := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' c)
  rw [AddSubgroup.mem_addSubgroupOf] at h2
  have h3 : -(Quotient.out c).1 + (x - diag ξ) ∈ Hp a b := by simpa using h2
  obtain ⟨h, hh, η, hη, heq⟩ := (mem_Hp a b).1 h3
  have hmem : diag (-(ξ + η)) + x ∈ fundDom a b := by
    refine mem_fundDom.2 ⟨c, ?_⟩
    have : -(Quotient.out c).1 + (diag (-(ξ + η)) + x) = h := by
      have e1 : h = -(Quotient.out c).1 + (x - diag ξ) - diag η := by rw [eq_sub_iff_add_eq, heq]
      rw [e1, diag_neg, diag_add]; abel
    rw [this]; exact hh
  refine ⟨⟨diag (-(ξ + η)), mem_diagSubgroup.2 ⟨_, rfl⟩⟩, hmem, ?_⟩
  rintro ⟨y, hy⟩ hy'
  obtain ⟨ζ, rfl⟩ := mem_diagSubgroup.1 hy
  have : ζ = -(ξ + η) := fundDom_unique hba hb x hy' hmem
  subst this
  rfl

theorem exists_ab (hc : IsConstantField Fq k) : ∃ a b : Divisor Fq k,
    2 * Rep.genusInt Fq k - 2 < Divisor.deg a ∧ b ≤ a ∧ Divisor.deg b < 0 := by
  obtain ⟨B, -, hB⟩ := Rep.exists_divisor_deg_ge (Fq := Fq) (k := k) (2 * Rep.genusInt Fq k - 1).toNat
  have ha : 2 * Rep.genusInt Fq k - 2 < Divisor.deg B := by omega
  obtain ⟨v⟩ := Place.nonempty (Fq := Fq) (k := k)
  set n : ℤ := ((Divisor.deg B).toNat : ℤ) + 1 with hn
  refine ⟨B, B - Finsupp.single v n, ha, ?_, ?_⟩
  · refine sub_le_self _ ?_
    rw [Finsupp.single_nonneg]; omega
  · rw [_root_.map_sub, Divisor.deg_single]
    have := v.degree_pos
    have h1 : n ≤ n * (v.degree : ℤ) := by nlinarith
    omega

/-- **Weil VI, Cor. 1 of Thm. 1** ($E=k$): if $\mathbb F_q$ is the field of constants, the Haar measure $\mu_1$ with
$\mu_1(\prod_v\mathfrak r_v)=1$ gives $k_{\mathbb A}/k$ the volume $q^{g-1}$. -/
@[kb "weil1973bnt" "Ch. VI, Cor. 1 (Thm. 1) (p. 100), E = k: mu_1(k_A/k) = q^(g-1)"]
theorem weil_VI_1_thm1_cor1 (hc : IsConstantField Fq k) :
    addCovolume (diagSubgroup Fq k) (FFAdeleRing Fq k) (haar Fq k) =
      (Nat.card Fq : ℝ≥0∞) ^ (Rep.genusInt Fq k - 1) := by
  obtain ⟨a, b, ha, hba, hb⟩ := exists_ab hc
  rw [(isAddFundamentalDomain_fundDom hc ha hba hb).covolume_eq_volume (haar Fq k)]
  have h1 := haar_U_eq hba hb
  rw [haar_U] at h1
  have hell := weil_VI_2_cor2 hc ha
  set Q : ℝ≥0∞ := (Nat.card Fq : ℝ≥0∞)
  have hQ0 : Q ≠ 0 := by
    simp only [Q, ne_eq, Nat.cast_eq_zero]; exact (Nat.card_pos (α := Fq)).ne'
  have hQt : Q ≠ ⊤ := by simp [Q]
  have h2 : Q ^ (Divisor.deg a) = Q ^ a.ell * Q ^ (Rep.genusInt Fq k - 1) := by
    rw [← zpow_natCast, ← ENNReal.zpow_add hQ0 hQt]
    congr 1; omega
  rw [h2] at h1
  exact ((ENNReal.mul_right_inj (pow_ne_zero _ hQ0) (ENNReal.pow_ne_top hQt)).1 h1).symm

end FFAdeleRing

end NumberFieldKB.WeilBNT.FF
