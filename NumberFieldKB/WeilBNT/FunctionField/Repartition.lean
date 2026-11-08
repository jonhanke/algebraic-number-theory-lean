import NumberFieldKB.WeilBNT.FunctionField.ProductFormula

/-!
# Repartitions and the parallelotopes $U(\mathfrak a)$ (Weil VI.§1–2, divisor form)

Weil VI works with the adele ring $k_{\mathbb A}$ and the compact open subgroups
$U(\mathfrak a)=\prod_v\pi_v^{-a(v)}\mathfrak r_v$. For the dimension counts of Riemann–Roch only the quotients
$k_{\mathbb A}/(U(\mathfrak a)+k)$ matter, and these do not change if each completion $k_v$ is replaced by $k$
(Chevalley's *repartitions*; the quotient $k_v/\pi_v^{-a(v)}\mathfrak r_v$ is the same for $k$ and $k_v$). We use
repartitions so that everything stays inside $k$.

* **`repartitions Fq k`**: the $k$-module of families $(\alpha_v)$ of elements of $k$ with $\alpha_v\in\mathfrak r_v$ for
  almost all $v$; **`Rep Fq k`** its carrier type.
* **`Rep.diag`**: the diagonal embedding $k\to$ `Rep`, with image **`Rep.principal`**.
* **`Rep.U a`** $=\{\alpha:\ v(\alpha_v)\le q^{a(v)}\ \forall v\}$, an $\mathbb F_q$-subspace (Weil's
  $U(\mathfrak a)$ restricted to $k$); **`Rep.diag_mem_U_iff`**: $\operatorname{diag}\xi\in U(\mathfrak a)$ iff
  $\xi\in A(\mathfrak a)$.
-/

open scoped Polynomial

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

variable (Fq k) in
/-- **Repartitions**: families $(\alpha_v)_v$ in $k$ with $v(\alpha_v)\le1$ for almost all places $v$. -/
def repartitions : Submodule k (Place Fq k → k) where
  carrier := {α | {v : Place Fq k | 1 < v.valuation (α v)}.Finite}
  add_mem' := by
    intro α β hα hβ
    refine (hα.union hβ).subset ?_
    intro v hv
    simp only [Set.mem_ofPred_eq, Pi.add_apply] at hv
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at h
    exact absurd (lt_of_lt_of_le hv ((v.valuation.map_add _ _).trans (max_le h.1 h.2))) (lt_irrefl _)
  zero_mem' := by simp
  smul_mem' := by
    intro c α hα
    by_cases hc : c = 0
    · subst hc; simp
    refine ((Place.weil_III_1_thm3_ff (Fq := Fq) hc).union hα).subset ?_
    intro v hv
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul] at hv
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, not_not] at h
    rw [h.1, one_mul] at hv
    exact absurd hv (not_lt.mpr h.2)

variable (Fq k) in
/-- The type of repartitions. -/
abbrev Rep : Type _ := ↥(repartitions Fq k)

namespace Rep

theorem finite_poles (α : Rep Fq k) : {v : Place Fq k | 1 < v.valuation (α.1 v)}.Finite := α.2

/-- The diagonal embedding $k\to$ `Rep`. -/
def diag : k →ₗ[Fq] Rep Fq k where
  toFun f := ⟨fun _ => f, by
    by_cases hf : f = 0
    · subst hf
      exact (repartitions Fq k).zero_mem
    refine (Place.weil_III_1_thm3_ff (Fq := Fq) hf).subset ?_
    intro v hv h1
    simp only [Set.mem_ofPred_eq] at hv
    rw [h1] at hv
    exact lt_irrefl _ hv⟩
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp] theorem diag_apply (f : k) (v : Place Fq k) : (diag (Fq := Fq) f).1 v = f := rfl

theorem diag_injective : Function.Injective (diag (Fq := Fq) (k := k)) := by
  intro f g h
  obtain ⟨v⟩ := Place.nonempty (Fq := Fq) (k := k)
  have := congrArg (fun α : Rep Fq k => α.1 v) h
  simpa using this

variable (Fq k) in
/-- The principal repartitions $k\subset$ `Rep`. -/
def principal : Submodule Fq (Rep Fq k) := LinearMap.range (diag (Fq := Fq) (k := k))

/-- **The parallelotope** $U(\mathfrak a)=\{\alpha:\ v(\alpha_v)\le q^{a(v)}\}$ (Weil's $U(\mathfrak a)$). -/
def U (a : Divisor Fq k) : Submodule Fq (Rep Fq k) where
  carrier := {α | ∀ v : Place Fq k, v.valuation (α.1 v) ≤ WithZero.exp (a v)}
  add_mem' := by
    intro α β hα hβ v
    exact (v.valuation.map_add _ _).trans (max_le (hα v) (hβ v))
  zero_mem' := by intro v; simp
  smul_mem' := by
    intro c α hα v
    show v.valuation (c • α.1 v) ≤ _
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' ((Place.mem_integers_iff v).1 (v.algebraMap_mem_integers c))).trans
      (hα v)

theorem mem_U_iff (a : Divisor Fq k) (α : Rep Fq k) :
    α ∈ U a ↔ ∀ v : Place Fq k, v.valuation (α.1 v) ≤ WithZero.exp (a v) := Iff.rfl

theorem U_mono {a b : Divisor Fq k} (h : a ≤ b) : U a ≤ U b := by
  intro α hα v
  exact (hα v).trans (WithZero.exp_le_exp.mpr (h v))

theorem diag_mem_U_iff (a : Divisor Fq k) (f : k) :
    diag (Fq := Fq) f ∈ U a ↔ f ∈ a.riemannRochSpace := by
  rw [mem_U_iff, Divisor.mem_riemannRochSpace_iff]
  rfl

theorem U_inf_principal (a : Divisor Fq k) :
    U a ⊓ principal Fq k = a.riemannRochSpace.map (diag (Fq := Fq) (k := k)) := by
  ext α
  simp only [Submodule.mem_inf, principal, LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨hα, f, rfl⟩
    exact ⟨f, (diag_mem_U_iff a f).1 hα, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨(diag_mem_U_iff a f).2 hf, f, rfl⟩

/-- Every repartition lies in some $U(\mathfrak b)$ with $\mathfrak b\ge\mathfrak a$. -/
theorem exists_mem_U (a : Divisor Fq k) (α : Rep Fq k) : ∃ b : Divisor Fq k, a ≤ b ∧ α ∈ U b := by
  classical
  let S := (finite_poles α).toFinset
  let c : Divisor Fq k := ∑ v ∈ S, Finsupp.single v (WithZero.log (v.valuation (α.1 v)))
  have hc : ∀ v ∈ S, c v = WithZero.log (v.valuation (α.1 v)) := by
    intro v hv
    simp only [c, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
    rw [Finset.sum_eq_single v]
    · simp
    · intro w _ hw; simp [hw]
    · intro h; exact absurd hv h
  let b : Divisor Fq k := a.pos + c.pos
  refine ⟨b, fun v => ?_, fun v => ?_⟩
  · simp only [b, Finsupp.coe_add, Pi.add_apply, Divisor.pos_apply]
    omega
  · by_cases hv : v ∈ S
    · have h1 : 1 < v.valuation (α.1 v) := (Set.Finite.mem_toFinset (finite_poles α)).1 hv
      have h0 : v.valuation (α.1 v) ≠ 0 := (lt_trans zero_lt_one h1).ne'
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      simp only [b, Finsupp.coe_add, Pi.add_apply, Divisor.pos_apply, hc v hv]
      omega
    · have h1 : v.valuation (α.1 v) ≤ 1 := by
        have : ¬ (1 < v.valuation (α.1 v)) := fun h => hv ((Set.Finite.mem_toFinset (finite_poles α)).2 h)
        exact not_lt.mp this
      refine h1.trans ?_
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      simp only [b, Finsupp.coe_add, Pi.add_apply, Divisor.pos_apply]
      omega

/-- Multiplication by $\xi\in k^\times$ maps $U(\mathfrak a)$ onto $U(\mathfrak a-\operatorname{div}\xi)$. -/
theorem smul_mem_U_iff (a : Divisor Fq k) (f : kˣ) (α : Rep Fq k) :
    (f : k) • α ∈ U (a - Divisor.div f) ↔ α ∈ U a := by
  rw [mem_U_iff, mem_U_iff]
  refine forall_congr' fun v => ?_
  show v.valuation ((f : k) * α.1 v) ≤ _ ↔ _
  have hf : v.valuation (f : k) ≠ 0 := by simp
  rw [map_mul, Finsupp.coe_sub, Pi.sub_apply, Divisor.div_apply]
  have hvf : v.valuation (f : k) = WithZero.exp (-(v.ord (f : k))) := by
    rw [Place.ord, neg_neg, WithZero.exp_log hf]
  have he : WithZero.exp (a v - v.ord (f : k)) = WithZero.exp (-(v.ord (f : k))) * WithZero.exp (a v) := by
    rw [← WithZero.exp_add]; ring_nf
  rw [hvf, he]
  exact mul_le_mul_iff_of_pos_left (WithZero.exp_pos)

/-- The local piece: $U(\mathfrak a+v)/U(\mathfrak a)\cong\kappa(v)$, via $\alpha\mapsto$ the residue of
$\alpha_v\pi^{a(v)+1}$. -/
theorem exists_residue_surj (a : Divisor Fq k) (v : Place Fq k) :
    ∃ ψ : U (a + Finsupp.single v 1) →ₗ[Fq] v.residueField,
      Function.Surjective ψ ∧ ∀ α : U (a + Finsupp.single v 1), ψ α = 0 ↔ α.1 ∈ U a := by
  classical
  obtain ⟨π, hπ⟩ := v.valuation_surjective (WithZero.exp (-1))
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hmul : ∀ (f : k) (m : ℤ), v.valuation (f * π ^ m) = v.valuation f * WithZero.exp (-m) := by
    intro f m
    rw [map_mul, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul]
    congr 2
    ring
  set m : ℤ := a v + 1 with hm
  have hav : (a + Finsupp.single v 1 : Divisor Fq k) v = m := by simp [hm]
  have hmem : ∀ α : U (a + Finsupp.single v 1), v.valuation (α.1.1 v * π ^ m) ≤ 1 := by
    intro α
    rw [hmul]
    have h := α.2 v
    rw [hav] at h
    calc v.valuation (α.1.1 v) * WithZero.exp (-m) ≤ WithZero.exp m * WithZero.exp (-m) :=
          mul_le_mul_left h _
      _ = 1 := by rw [← WithZero.exp_add]; simp
  let ψ : U (a + Finsupp.single v 1) →ₗ[Fq] v.residueField :=
    { toFun := fun α => IsLocalRing.residue v.integers ⟨α.1.1 v * π ^ m, hmem α⟩
      map_add' := by
        intro α β
        rw [← map_add]
        congr 1
        ext
        show (α.1.1 v + β.1.1 v) * π ^ m = _
        simp [add_mul]
      map_smul' := by
        intro c α
        rw [Algebra.smul_def]
        show _ = (IsLocalRing.residue v.integers (algebraMap Fq v.integers c)) * _
        rw [← map_mul]
        congr 1
        ext
        show (c • α.1.1 v) * π ^ m = _
        simp [Algebra.smul_def, mul_assoc]
        exact Or.inl rfl }
  refine ⟨ψ, ?_, ?_⟩
  · intro r
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
    let z : k := (y : k) * π ^ (-m)
    let α : Rep Fq k := ⟨fun w => if w = v then z else 0, by
      refine (Set.finite_singleton v).subset ?_
      intro w hw
      by_contra hwv
      have hwv' : w ≠ v := hwv
      have hw' : w.valuation (if w = v then z else 0) = 0 := by
        rw [if_neg hwv', map_zero]
      have hw2 : 1 < w.valuation (if w = v then z else 0) := hw
      rw [hw'] at hw2
      exact absurd hw2 (not_lt.mpr zero_le')⟩
    have hαU : α ∈ U (a + Finsupp.single v 1) := by
      intro w
      by_cases hw : w = v
      · subst hw
        simp only [α, if_pos rfl, if_true, z, hav]
        rw [hmul, neg_neg]
        calc w.valuation (y : k) * WithZero.exp m ≤ 1 * WithZero.exp m := mul_le_mul_left y.2 _
          _ = _ := one_mul _
      · simp only [α, if_neg hw, map_zero]
        exact zero_le'
    refine ⟨⟨α, hαU⟩, ?_⟩
    show IsLocalRing.residue v.integers _ = _
    congr 1
    ext
    show (if v = v then z else 0) * π ^ m = (y : k)
    rw [if_pos rfl]
    simp only [z, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
  · intro α
    constructor
    · intro h0 w
      by_cases hw : w = v
      · subst hw
        have h1 := Place.valuation_lt_one_of_mem_maximalIdeal' w _
          ((IsLocalRing.residue_eq_zero_iff _).mp h0)
        have h2 : w.valuation (α.1.1 w * π ^ m) < 1 := h1
        rw [hmul] at h2
        by_cases hz : w.valuation (α.1.1 w) = 0
        · rw [hz]; exact zero_le'
        · rw [← WithZero.exp_log hz] at h2 ⊢
          rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
          rw [WithZero.exp_le_exp]
          omega
      · have := α.2 w
        simpa [Finsupp.single_apply, Ne.symm hw] using this
    · intro h
      apply (IsLocalRing.residue_eq_zero_iff _).mpr
      apply Place.mem_maximalIdeal_of_valuation_lt_one
      show v.valuation (α.1.1 v * π ^ m) < 1
      rw [hmul]
      have h1 := h v
      calc v.valuation (α.1.1 v) * WithZero.exp (-m) ≤ WithZero.exp (a v) * WithZero.exp (-m) :=
            mul_le_mul_left h1 _
        _ < 1 := by
          rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp]
          omega

end Rep

end NumberFieldKB.WeilBNT.FF
