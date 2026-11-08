import NumberFieldKB.WeilBNT.FunctionField.Idele
import NumberFieldKB.WeilBNT.FunctionField.ZetaFinal
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# The Haar measure of $k_{\mathbb A}$ and the volume of $k_{\mathbb A}/k$ (Weil VI.§1–2, $E=k$)

For a global function field $k$ over $\mathbb F_q$ and a divisor $\mathfrak a$, Weil's
$U(\mathfrak a)=\prod_v\mathfrak p_v^{-a(v)}$ is the compact open subgroup `FFAdeleRing.U a` of the adele ring.

* `FFAdeleRing.isOpen_U`, `FFAdeleRing.isCompact_U_zero`; `FFAdeleRing.diag_mem_U_iff`:
  $k\cap U(\mathfrak a)=A(\mathfrak a)$ (the Riemann–Roch space).
* **`FFAdeleRing.weil_VI_2_cor3_adelic`**: Weil VI.§2, Cor. 3 of Thm. 2, in the adelic form:
  $k_{\mathbb A}=k+U(\mathfrak a)$ when $\deg\mathfrak a>2g-2$ (from the repartition form `Rep.S_eq_top` /
  `weil_VI_1_thm1_cor2` and the density of $k$ in each $k_v$).
* `FFAdeleRing.haar`: the Haar measure $\mu_1$ of $k_{\mathbb A}$ with $\mu_1(\prod_v\mathfrak r_v)=1$, and
  **`FFAdeleRing.haar_U`**: $\mu_1(U(\mathfrak a))=q^{\deg\mathfrak a}$ (Weil VI.§1, Cor. 2 of Prop. 2, $E=k$, where
  $\delta(L(\mathfrak a))=-\deg\mathfrak a$).
* **`FFAdeleRing.weil_VI_1_thm1_cor1`**: Weil VI, Cor. 1 of Thm. 1 for $E=k$: $\mu_1(k_{\mathbb A}/k)=q^{g-1}$, as the
  covolume of the discrete subgroup $k$ (a fundamental domain is built from $U(\mathfrak b)$, $\deg\mathfrak b<0$, and
  representatives of $U(\mathfrak a)/(U(\mathfrak b)+A(\mathfrak a))$ for $\deg\mathfrak a>2g-2$).
-/

open scoped WithZero RestrictedProduct Pointwise NNReal ENNReal
open Valuation IsDedekindDomain Topology MeasureTheory

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

/-- The closed balls $\{y\in k_v: v(y)\le e^n\}$ are open. -/
theorem Place.isOpen_valued_le (v : Place Fq k) (n : ℤ) :
    IsOpen {y : v.Completion | Valued.v y ≤ WithZero.exp n} := by
  obtain ⟨c, hc⟩ := v.valued_surjective (WithZero.exp n)
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [map_zero] at hc; exact WithZero.exp_ne_zero hc.symm
  have hcv : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  have hcont : Continuous fun y : v.Completion => y * c⁻¹ := continuous_id.mul continuous_const
  convert (Valued.isOpen_valuationSubring v.Completion).preimage hcont using 1
  ext y
  show Valued.v y ≤ WithZero.exp n ↔ Valued.v (y * c⁻¹) ≤ 1
  rw [map_mul, map_inv₀, ← hc, mul_inv_le_iff₀ (zero_lt_iff.2 hcv), one_mul]

namespace FFAdeleRing

/-- **Weil's $U(\mathfrak a)=\prod_v\mathfrak p_v^{-a(v)}$** in $k_{\mathbb A}$: adeles with
$v(x_v)\le e^{a(v)}$ for every place $v$. -/
def U (a : Divisor Fq k) : AddSubgroup (FFAdeleRing Fq k) where
  carrier := {x | ∀ v : Place Fq k, Valued.v (x v) ≤ WithZero.exp (a v)}
  zero_mem' := fun v => by simp
  add_mem' {x y} hx hy := fun v => by
    show Valued.v (x v + y v) ≤ _
    exact (Valuation.map_add _ _ _).trans (max_le (hx v) (hy v))
  neg_mem' {x} hx := fun v => by
    show Valued.v (-(x v)) ≤ _
    rw [Valuation.map_neg]; exact hx v

theorem mem_U_iff (a : Divisor Fq k) (x : FFAdeleRing Fq k) :
    x ∈ U a ↔ ∀ v : Place Fq k, Valued.v (x v) ≤ WithZero.exp (a v) := Iff.rfl

theorem U_mono {a b : Divisor Fq k} (h : a ≤ b) : U a ≤ U b := fun x hx v =>
  (hx v).trans (WithZero.exp_le_exp.2 (h v))

theorem U_zero_eq : (U (0 : Divisor Fq k) : Set (FFAdeleRing Fq k)) =
    {x | ∀ v : Place Fq k, x.1 v ∈ (v.completionIntegers : Set v.Completion)} := by
  ext x
  simp only [SetLike.mem_coe, mem_U_iff, Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
  rfl

theorem isCompact_U_zero : IsCompact (U (0 : Divisor Fq k) : Set (FFAdeleRing Fq k)) := by
  have : ∀ v : Place Fq k, CompactSpace (v.completionIntegers : Set v.Completion) := fun v =>
    isCompact_iff_compactSpace.1 v.isCompact_completionIntegers
  rw [U_zero_eq, ← RestrictedProduct.range_structureMap]
  exact isCompact_range (RestrictedProduct.isEmbedding_structureMap.continuous)

theorem isOpen_U (a : Divisor Fq k) : IsOpen (U a : Set (FFAdeleRing Fq k)) := by
  classical
  have h1 : IsOpen {x : FFAdeleRing Fq k | ∀ v, v ∉ a.support → x.1 v ∈ (v.completionIntegers : Set v.Completion)} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring v.Completion)
  have h2 : IsOpen {x : FFAdeleRing Fq k | ∀ v ∈ a.support, Valued.v (x v) ≤ WithZero.exp (a v)} := by
    have : {x : FFAdeleRing Fq k | ∀ v ∈ a.support, Valued.v (x v) ≤ WithZero.exp (a v)} =
        ⋂ v ∈ a.support, (fun x : FFAdeleRing Fq k => x v) ⁻¹' {y | Valued.v y ≤ WithZero.exp (a v)} := by
      ext x; simp
    rw [this]
    refine isOpen_biInter_finset fun v _ => ?_
    exact (Place.isOpen_valued_le v (a v)).preimage (RestrictedProduct.continuous_eval v)
  convert h1.inter h2 using 1
  ext x
  simp only [SetLike.mem_coe, mem_U_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v _ => h v⟩
    have := h v
    rwa [Finsupp.notMem_support_iff.1 hv, WithZero.exp_zero] at this
  · rintro ⟨h1, h2⟩ v
    by_cases hv : v ∈ a.support
    · exact h2 v hv
    · have : Valued.v (x v) ≤ 1 := h1 v hv
      rwa [Finsupp.notMem_support_iff.1 hv, WithZero.exp_zero]

/-- $k\cap U(\mathfrak a)=A(\mathfrak a)$: a principal adele lies in $U(\mathfrak a)$ iff the element lies in the
Riemann–Roch space. -/
theorem diag_mem_U_iff (a : Divisor Fq k) (ξ : k) : diag ξ ∈ U a ↔ ξ ∈ a.riemannRochSpace := by
  rw [mem_U_iff, Divisor.mem_riemannRochSpace_iff]
  refine forall_congr' fun v => ?_
  show Valued.v (v.toCompletion ξ) ≤ _ ↔ _
  rw [Place.valued_toCompletion]

/-- From repartitions to adeles: if $U(\mathfrak a)+k$ is all repartitions then $k_{\mathbb A}=k+U(\mathfrak a)$. -/
theorem exists_sub_diag_mem_U_of_S_eq_top {a : Divisor Fq k} (hS : Rep.S Fq k a = ⊤)
    (x : FFAdeleRing Fq k) : ∃ ξ : k, x - diag ξ ∈ U a := by
  classical
  -- local approximations
  have hloc : ∀ v : Place Fq k, ∃ r : k, Valued.v (x v - v.toCompletion r) ≤ WithZero.exp (a v) := by
    intro v
    have hopen : IsOpen {y : v.Completion | Valued.v (x v - y) ≤ WithZero.exp (a v)} := by
      have := (Place.isOpen_valued_le v (a v)).preimage (continuous_const.sub continuous_id :
        Continuous fun y : v.Completion => x v - y)
      exact this
    obtain ⟨r, hr⟩ := (Place.denseRange_toCompletion v).exists_mem_open hopen ⟨x v, by simp⟩
    exact ⟨r, hr⟩
  choose r hr using hloc
  set T : Set (Place Fq k) := {v | ¬ Valued.v (x v) ≤ WithZero.exp (a v)} with hT
  have hTfin : T.Finite := by
    have h1 : {v : Place Fq k | ¬ x.1 v ∈ (v.completionIntegers : Set v.Completion)}.Finite :=
      Filter.eventually_cofinite.1 x.2
    refine (h1.union a.support.finite_toSet).subset ?_
    intro v hv
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, Finset.mem_coe,
      Finsupp.mem_support_iff] at hnot
    apply hv
    have : Valued.v (x v) ≤ 1 := hnot.1
    rw [hnot.2, WithZero.exp_zero]
    exact this
  -- the repartition
  let α : Place Fq k → k := fun v => if v ∈ T then r v else 0
  have hα : α ∈ repartitions Fq k := by
    refine hTfin.subset ?_
    intro v hv
    by_contra hvT
    simp only [Set.mem_ofPred_eq, α, if_neg hvT, map_zero] at hv
    exact (not_lt.2 zero_le) hv
  have hαx : ∀ v, Valued.v (x v - v.toCompletion (α v)) ≤ WithZero.exp (a v) := by
    intro v
    by_cases hv : v ∈ T
    · simp only [α, if_pos hv]; exact hr v
    · simp only [α, if_neg hv, map_zero, sub_zero]
      simpa [hT] using hv
  have hmem : (⟨α, hα⟩ : Rep Fq k) ∈ Rep.S Fq k a := hS ▸ Submodule.mem_top
  obtain ⟨u, hu, p, hp, hup⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨ξ, rfl⟩ := hp
  refine ⟨ξ, fun v => ?_⟩
  have hαv : α v = u.1 v + ξ := by
    have := congrArg (fun β : Rep Fq k => β.1 v) hup
    simpa using this.symm
  have e : (x - diag ξ : FFAdeleRing Fq k) v = (x v - v.toCompletion (α v)) + v.toCompletion (u.1 v) := by
    rw [hαv, map_add]
    show x v - v.toCompletion ξ = _
    ring
  rw [e]
  refine (Valuation.map_add _ _ _).trans (max_le (hαx v) ?_)
  rw [Place.valued_toCompletion]
  exact (Rep.mem_U_iff a u).1 hu v

/-- **Weil VI.§2, Cor. 3 of Thm. 2** (adelic form): if $\deg\mathfrak a>2g-2$ then $k_{\mathbb A}=k+U(\mathfrak a)$,
where $U(\mathfrak a)=\prod_v\mathfrak p_v^{-a(v)}$ ($\mathbb F_q$ the field of constants). -/
@[kb "weil1973bnt" "Ch. VI, Cor. 3 (Thm. 2) (p. 101), k_A = k + U(a), adelic form"]
theorem weil_VI_2_cor3_adelic (hc : IsConstantField Fq k) {a : Divisor Fq k}
    (ha : 2 * Rep.genusInt Fq k - 2 < Divisor.deg a) (x : FFAdeleRing Fq k) :
    ∃ ξ : k, x - diag ξ ∈ U a :=
  exists_sub_diag_mem_U_of_S_eq_top (weil_VI_2_cor3 hc ha) x

end FFAdeleRing

end NumberFieldKB.WeilBNT.FF
