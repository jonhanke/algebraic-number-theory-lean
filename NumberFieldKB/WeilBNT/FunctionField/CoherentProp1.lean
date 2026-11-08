import NumberFieldKB.WeilBNT.FunctionField.CoherentMeasure
import NumberFieldKB.WeilBNT.FunctionField.AdeleTopology

/-!
# Weil VI.§1, Prop. 1 for $E=k^n$: products of lattices in $E_{\mathbb A}$

$k$ is a global function field over $\mathbb F_q$, $E=k^n$ with its standard basis $\mathfrak e$, $E_{\mathbb A}=
k_{\mathbb A}^n$ (product topology). For a family $L=(L_v)$ of $k_v$-lattices $L_v\subset k_v^n$, `Ufam L` is
$E_{\mathbb A}\cap\prod_vL_v$.

* **`weil_VI_1_prop1_vec`** (Weil VI.§1, Prop. 1): $\prod_vL_v$ is open and compact in $E_{\mathbb A}$ iff
  $L_v=\mathfrak e_v=\mathfrak r_v^n$ for almost all $v$.

*Proof.* Every lattice lies between $\pi_v^N\mathfrak r_v^n$ and $\pi_v^{-N}\mathfrak r_v^n$. If the product is open
it contains a box $U(\mathfrak b)^n$, so $L_v\supseteq\mathfrak r_v^n$ outside the support of $\mathfrak b$; if it is
compact it lies in some box $U(\mathfrak a)^n$ (a compact set is covered by finitely many translates of the open
subgroup $U(0)^n$), and testing with single adeles gives $L_v\subseteq\mathfrak r_v^n$ outside the support of
$\mathfrak a$. Conversely, if $L_v=\mathfrak r_v^n$ almost everywhere the product is open (`FFAdeleVec.isOpen_USet`),
closed, and contained in a box $U(\mathfrak a)^n$, which is compact.
-/

open scoped WithZero Topology
open Filter

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

variable {n : ℕ}

/-- $E_{\mathbb A}\cap\prod_vL_v$ for an arbitrary family of subgroups $L_v\subset k_v^n$. -/
def UfamVec (L : ∀ v : Place Fq k, AddSubgroup (Fin n → v.Completion)) :
    AddSubgroup (Fin n → FFAdeleRing Fq k) where
  carrier := {x | ∀ v, (fun i => x i v) ∈ L v}
  zero_mem' := fun v => (L v).zero_mem
  add_mem' {x y} hx hy := fun v => (L v).add_mem (hx v) (hy v)
  neg_mem' {x} hx := fun v => (L v).neg_mem (hx v)

theorem mem_UfamVec {L : ∀ v : Place Fq k, AddSubgroup (Fin n → v.Completion)} {x : Fin n → FFAdeleRing Fq k} :
    x ∈ UfamVec L ↔ ∀ v, (fun i => x i v) ∈ L v := Iff.rfl

/-- Helper: every element of $\mathbb Z_{m0}$ is bounded by `exp` of a natural number. -/
theorem le_exp_toNat_log (z : ℤᵐ⁰) : z ≤ WithZero.exp ((WithZero.log z).toNat : ℤ) := by
  by_cases hz : z = 0
  · rw [hz]; exact zero_le
  · calc z = WithZero.exp (WithZero.log z) := (WithZero.exp_log hz).symm
      _ ≤ _ := WithZero.exp_le_exp.2 (Int.self_le_toNat _)

/-- Helper: a valuation `≤ 1` has `toNat (log) = 0`. -/
theorem toNat_log_eq_zero_of_le_one {z : ℤᵐ⁰} (h : z ≤ 1) : (WithZero.log z).toNat = 0 := by
  by_cases hz : z = 0
  · simp [hz]
  · have : WithZero.log z ≤ 0 := by
      rw [← WithZero.exp_le_exp, WithZero.exp_log hz, WithZero.exp_zero]; exact h
    omega

/-- Helper: every adele lies in some $U(\mathfrak a)$. -/
theorem exists_U_mem (x : FFAdeleRing Fq k) : ∃ a : Divisor Fq k, x ∈ FFAdeleRing.U a := by
  have hfin := Filter.eventually_cofinite.1 x.2
  refine ⟨Finsupp.ofSupportFinite (fun v => ((WithZero.log (Valued.v (x v))).toNat : ℤ)) ?_, fun v => ?_⟩
  · refine hfin.subset fun v hv => ?_
    intro hx
    apply hv
    have : (WithZero.log (Valued.v (x v))).toNat = 0 :=
      toNat_log_eq_zero_of_le_one ((Place.mem_completionIntegers_iff v).1 hx)
    simp [this]
  · exact le_exp_toNat_log _

/-- Helper: a compact subset of $k_{\mathbb A}$ lies in some $U(\mathfrak a)$. -/
theorem exists_U_superset_of_isCompact {K : Set (FFAdeleRing Fq k)} (hK : IsCompact K) :
    ∃ a : Divisor Fq k, K ⊆ FFAdeleRing.U a := by
  obtain ⟨a, ha⟩ := hK.elim_directed_cover (fun a : Divisor Fq k => (FFAdeleRing.U a : Set (FFAdeleRing Fq k)))
    (fun a => FFAdeleRing.isOpen_U a)
    (fun x _ => Set.mem_iUnion.2 (exists_U_mem x))
    (fun a b => ⟨a ⊔ b, FFAdeleRing.U_mono le_sup_left, FFAdeleRing.U_mono le_sup_right⟩)
  exact ⟨a, ha⟩

/-- Helper: a $k_v$-lattice lies in $\pi^{-N}\mathfrak r_v^n$ for some $N$. -/
theorem exists_le_boxLat (v : Place Fq k) {L : AddSubgroup (Fin n → v.Completion)} (hL : v.IsLattice L) :
    ∃ N : ℕ, L ≤ Place.boxLat v (fun _ => -(N : ℤ)) := by
  have hc : IsCompact (L : Set (Fin n → v.Completion)) := hL.2.1
  obtain ⟨m, hm⟩ := hc.elim_directed_cover
    (fun m : ℕ => Set.pi Set.univ fun _ : Fin n => {z : v.Completion | Valued.v z ≤ WithZero.exp (m : ℤ)})
    (fun m => isOpen_set_pi Set.finite_univ fun i _ => Place.isOpen_valued_le v _)
    (fun y _ => by
      have := fun i => le_exp_toNat_log (Valued.v (y i))
      refine Set.mem_iUnion.2 ⟨Finset.univ.sup fun i => (WithZero.log (Valued.v (y i))).toNat,
        fun i _ => (this i).trans (WithZero.exp_le_exp.2 ?_)⟩
      exact_mod_cast Finset.le_sup (f := fun i => (WithZero.log (Valued.v (y i))).toNat) (Finset.mem_univ i))
    (fun a b => ⟨max a b, fun y hy i hi => (hy i hi).trans (WithZero.exp_le_exp.2 (by exact_mod_cast le_max_left a b)),
      fun y hy i hi => (hy i hi).trans (WithZero.exp_le_exp.2 (by exact_mod_cast le_max_right a b))⟩)
  refine ⟨m, fun y hy i => ?_⟩
  simpa using hm hy i (Set.mem_univ i)

/-- **Weil, VI.§1, Prop. 1** ($E=k^n$): for a family of $k_v$-lattices $L_v\subset k_v^n$, the product
$\prod_vL_v$ is open and compact in $E_{\mathbb A}$ iff $L_v=\mathfrak r_v^n$ for almost all $v$. -/
@[kb "weil1973bnt" "Ch. VI, §1, Prop. 1 (p. 97), E = k^n"]
theorem weil_VI_1_prop1_vec (L : ∀ v : Place Fq k, AddSubgroup (Fin n → v.Completion))
    (hL : ∀ v : Place Fq k, v.IsLattice (L v)) :
    (IsOpen (UfamVec L : Set (Fin n → FFAdeleRing Fq k)) ∧ IsCompact (UfamVec L : Set (Fin n → FFAdeleRing Fq k))) ↔
      ∀ᶠ v in cofinite, L v = Place.stdLattice v n := by
  classical
  constructor
  · rintro ⟨hO, hC⟩
    have h0 : (UfamVec L : Set (Fin n → FFAdeleRing Fq k)) ∈ 𝓝 (0 : Fin n → FFAdeleRing Fq k) :=
      hO.mem_nhds (UfamVec L).zero_mem
    rw [show (0 : Fin n → FFAdeleRing Fq k) = fun _ => 0 from rfl, nhds_pi, Filter.mem_pi'] at h0
    obtain ⟨I, t, ht, hIt⟩ := h0
    have hb : ∀ i, ∃ b : Divisor Fq k, (FFAdeleRing.U b : Set (FFAdeleRing Fq k)) ⊆ t i :=
      fun i => FFAdeleRing.exists_U_subset_of_mem_nhds_zero (ht i)
    choose b hb using hb
    have ha : ∀ i, ∃ a : Divisor Fq k, (fun x : Fin n → FFAdeleRing Fq k => x i) '' (UfamVec L : Set _) ⊆
        FFAdeleRing.U a := fun i =>
      exists_U_superset_of_isCompact (hC.image (continuous_apply i))
    choose a ha using ha
    have e1 : ∀ᶠ v in cofinite, ∀ i, b i v = 0 :=
      Filter.eventually_all.2 fun i => Filter.eventually_cofinite.2 ((b i).support.finite_toSet.subset fun v hv => Finsupp.mem_support_iff.2 hv)
    have e2 : ∀ᶠ v in cofinite, ∀ i, a i v = 0 :=
      Filter.eventually_all.2 fun i => Filter.eventually_cofinite.2 ((a i).support.finite_toSet.subset fun v hv => Finsupp.mem_support_iff.2 hv)
    filter_upwards [e1, e2] with v h1 h2
    ext y
    constructor
    · intro hy
      have hx : (fun i => FFAdeleRing.single v (y i)) ∈ UfamVec L := fun w => by
        by_cases hw : w = v
        · subst hw; simpa using hy
        · have : (fun i => FFAdeleRing.single v (y i) w) = 0 := by
            ext i; simp [FFAdeleRing.single_apply_of_ne hw]
          rw [this]; exact (L w).zero_mem
      intro i
      have h3 := (FFAdeleRing.single_mem_U_iff (a i) v (y i)).1 (ha i ⟨_, hx, rfl⟩)
      simpa [h2 i] using h3
    · intro hy
      have hx : (fun i => FFAdeleRing.single v (y i)) ∈ Set.pi (↑I) t := fun i _ =>
        hb i (by
          rw [SetLike.mem_coe, FFAdeleRing.single_mem_U_iff, h1 i]
          simpa using hy i)
      have := hIt hx
      simpa using this v
  · intro h
    let S : CoherentSystem Fq k n := ⟨L, hL, h⟩
    have hopen : IsOpen (UfamVec L : Set (Fin n → FFAdeleRing Fq k)) := FFAdeleVec.isOpen_USet S
    refine ⟨hopen, ?_⟩
    choose N hN using fun v => exists_le_boxLat v (hL v)
    have hfin : {v | ¬ L v = Place.stdLattice v n}.Finite := Filter.eventually_cofinite.1 h
    let a : Divisor Fq k := Finsupp.ofSupportFinite
      (fun v => if L v = Place.stdLattice v n then 0 else (N v : ℤ)) (hfin.subset fun v hv => by
        by_contra hc
        have hc' : L v = Place.stdLattice v n := by simpa using hc
        apply hv
        simp [hc'])
    have hsub : (UfamVec L : Set (Fin n → FFAdeleRing Fq k)) ⊆
        Set.pi Set.univ fun _ => (FFAdeleRing.U a : Set (FFAdeleRing Fq k)) := fun x hx i _ v => by
      have hxv := hx v
      by_cases hv : L v = Place.stdLattice v n
      · rw [hv] at hxv
        have := hxv i
        show Valued.v (x i v) ≤ WithZero.exp (a v)
        simpa [a, hv] using this
      · have := hN v hxv i
        show Valued.v (x i v) ≤ WithZero.exp (a v)
        simpa [a, hv] using this
    have hcl : IsClosed (UfamVec L : Set (Fin n → FFAdeleRing Fq k)) := by
      have : (UfamVec L : Set (Fin n → FFAdeleRing Fq k)) =
          ⋂ v, (fun x : Fin n → FFAdeleRing Fq k => fun i => x i v) ⁻¹' (L v : Set (Fin n → v.Completion)) := by
        ext x; simp [mem_UfamVec]
      rw [this]
      exact isClosed_iInter fun v => ((hL v).2.1.isClosed).preimage
        (continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i))
    exact (isCompact_univ_pi fun _ => FFAdeleRing.isCompact_U a).of_isClosed_subset hcl hsub

end NumberFieldKB.WeilBNT.FF
