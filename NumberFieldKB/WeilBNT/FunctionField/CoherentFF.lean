import NumberFieldKB.WeilBNT.FunctionField.Idele
import NumberFieldKB.WeilBNT.FunctionField.AdeleVolume
import NumberFieldKB.WeilBNT.PFieldLattices

/-!
# Coherent systems of lattices (Weil VI.§1, general $E$)

Let $k$ be a function field over $\mathbb F_q$ and $E=k^n$ with its standard basis $\mathfrak e$ (every $n$-dimensional
$E$ is of this form after the choice of a basis; another basis is handled by `weil_VI_1_prop2_cor1`). For a place $v$,
$E_v=k_v^n$.

* `Place.IsLattice v L`: $L$ is a $k_v$-lattice in $k_v^n$ (Weil II.§2, Def. 2: a compact open $\mathfrak r_v$-module,
  `FieldModule.IsKLattice` for the $p$-field $k_v$); `Place.stdLattice v n` $=\mathfrak r_v^n$ (Weil's
  $\mathfrak e_v$).
* `Place.exists_gl_eq` (Weil II.§2, Thm. 1, for $k_v$): every lattice is $g\,\mathfrak r_v^n$ with
  $g\in\mathrm{GL}_n(k_v)$; `Place.valued_det_eq_of_map_eq`: $v(\det g)$ depends only on the lattice.
* `CoherentSystem`: Weil's coherent system $L=(L_v)$ ($L_v$ a lattice, $L_v=\mathfrak r_v^n$ for almost all $v$);
  `CoherentSystem.U` $=\prod_vL_v\subset E_{\mathbb A}=k_{\mathbb A}^n$; `CoherentSystem.A` $=E\cap U(L)$ as an
  $\mathbb F_q$-space; `CoherentSystem.lam` $=\lambda(L)=\dim_{\mathbb F_q}A(L)$.
* **`weil_VI_1_prop2`** (Weil VI.§1, Prop. 2): for every $a\in\mathrm{GL}_n(k_{\mathbb A})$, $(a_v\mathfrak r_v^n)$ is a
  coherent system (`CoherentSystem.ofGL`); every coherent system is of this form; and $\operatorname{div}(\det a)$
  depends only on the system. Two coherent systems differ by an element of $\mathrm{GL}_n(k_{\mathbb A})$
  (`weil_VI_1_prop2_two`).
* `CoherentSystem.div`, `CoherentSystem.delta`: Weil's $\operatorname{div}(\det a)$ and
  $\delta(L)=\deg\operatorname{div}(\det a)$ for $L=a\,L_0$.
* **`weil_VI_1_prop2_cor1`** (Weil VI.§1, Cor. 1 of Prop. 2): if $L=aL_0'$ for the system $L_0'$ of another basis
  ($P\in\mathrm{GL}_n(k)$), the divisor $\operatorname{div}(\det a)$ changes by a principal divisor, so its class and
  its degree depend only on $L$.
-/

open scoped WithZero NNReal Topology
open Valuation Filter Matrix

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace Place

/-- **The standard lattice** $\mathfrak r_v^n\subset k_v^n$ (Weil's $\mathfrak e_v$ for the standard basis). -/
def stdLattice (v : Place Fq k) (n : ℕ) : AddSubgroup (Fin n → v.Completion) where
  carrier := {x | ∀ i, Valued.v (x i) ≤ 1}
  zero_mem' := fun i => by simp
  add_mem' {x y} hx hy := fun i => by
    show Valued.v (x i + y i) ≤ 1
    exact (Valuation.map_add _ _ _).trans (max_le (hx i) (hy i))
  neg_mem' {x} hx := fun i => by
    show Valued.v (-(x i)) ≤ 1
    rw [Valuation.map_neg]; exact hx i

theorem mem_stdLattice {v : Place Fq k} {n : ℕ} {x : Fin n → v.Completion} :
    x ∈ stdLattice v n ↔ ∀ i, Valued.v (x i) ≤ 1 := Iff.rfl

/-- **A $k_v$-lattice** in $k_v^n$ (Weil II.§2, Def. 2): a compact open $\mathfrak r_v$-module of $k_v^n$. -/
def IsLattice (v : Place Fq k) {n : ℕ} (L : AddSubgroup (Fin n → v.Completion)) : Prop :=
  FieldModule.IsKLattice (weil_ff_completion_isPField v).1 L

/-- The maximal compact subring $R$ of the $p$-field $k_v$ is $\mathfrak r_v=\{x:v(x)\le1\}$. -/
theorem mem_pR_iff (v : Place Fq k) (x : v.Completion) :
    x ∈ FieldModule.pR (weil_ff_completion_isPField v).1 ↔ Valued.v x ≤ 1 := by
  rw [FieldModule.mem_pR]
  by_cases hx : x = 0
  · subst hx; simp [FieldModule.modK_zero]
  · have h := v.valued_eq_exp_neg_ordC hx
    rw [v.modK_completion h, h]
    have hq : (1 : ℝ≥0) < (Nat.card Fq : ℝ≥0) := by
      have : 2 ≤ Nat.card Fq := Finite.one_lt_card
      exact_mod_cast this
    have hQ : (1 : ℝ≥0) < (Nat.card Fq : ℝ≥0) ^ v.degree :=
      one_lt_pow₀ hq v.degree_pos.ne'
    rw [zpow_le_one_iff_right₀ hQ, ← WithZero.exp_zero, WithZero.exp_le_exp]

theorem isLattice_stdLattice (v : Place Fq k) (n : ℕ) : v.IsLattice (stdLattice v n) := by
  have hset : ((stdLattice v n : AddSubgroup (Fin n → v.Completion)) : Set (Fin n → v.Completion)) =
      Set.pi Set.univ (fun _ => (v.completionIntegers : Set v.Completion)) := by
    ext x
    simp [mem_stdLattice, Set.mem_pi, ValuationSubring.mem_toSubring]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro r hr m hm i
    have hr' := (mem_pR_iff v r).1 hr
    show Valued.v (r * m i) ≤ 1
    rw [map_mul]
    exact mul_le_one' hr' (hm i)
  · rw [hset]
    exact isCompact_univ_pi fun _ => v.isCompact_completionIntegers
  · rw [hset]
    exact isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring v.Completion

/-- If all entries of `M` are integral then so is its determinant. -/
theorem valued_det_le_one {v : Place Fq k} {n : ℕ} {M : Matrix (Fin n) (Fin n) v.Completion}
    (h : ∀ i j, Valued.v (M i j) ≤ 1) : Valued.v M.det ≤ 1 := by
  let M' : Matrix (Fin n) (Fin n) v.completionIntegers := Matrix.of fun i j => ⟨M i j, h i j⟩
  have h1 := RingHom.map_det v.completionIntegers.subtype M'
  have h2 : (v.completionIntegers.subtype.mapMatrix M') = M := by
    ext i j; rfl
  rw [h2] at h1
  rw [← h1]
  exact (M'.det).2

/-- Integral matrices send integral vectors to integral vectors. -/
theorem valued_mulVec_le_one {v : Place Fq k} {n : ℕ} {M : Matrix (Fin n) (Fin n) v.Completion}
    (h : ∀ i j, Valued.v (M i j) ≤ 1) {y : Fin n → v.Completion} (hy : ∀ j, Valued.v (y j) ≤ 1) (i : Fin n) :
    Valued.v ((M *ᵥ y) i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_one' (h i j) (hy j)

/-- The image $gL$ of a subgroup of $k_v^n$ under a matrix $g$. -/
def latticeMap {v : Place Fq k} {n : ℕ} (g : Matrix (Fin n) (Fin n) v.Completion)
    (L : AddSubgroup (Fin n → v.Completion)) : AddSubgroup (Fin n → v.Completion) :=
  L.map (Matrix.mulVecLin g).toAddMonoidHom

theorem mem_latticeMap {v : Place Fq k} {n : ℕ} {g : Matrix (Fin n) (Fin n) v.Completion}
    {L : AddSubgroup (Fin n → v.Completion)} {x : Fin n → v.Completion} :
    x ∈ latticeMap g L ↔ ∃ y ∈ L, g *ᵥ y = x := by
  simp [latticeMap]

/-- The identity matrix acts trivially on subgroups. -/
theorem latticeMap_one {v : Place Fq k} {n : ℕ} (L : AddSubgroup (Fin n → v.Completion)) :
    latticeMap (1 : Matrix (Fin n) (Fin n) v.Completion) L = L := by
  ext x
  rw [mem_latticeMap]
  simp

/-- The image under a product of matrices is the iterated image. -/
theorem latticeMap_mul {v : Place Fq k} {n : ℕ} (g h : Matrix (Fin n) (Fin n) v.Completion)
    (L : AddSubgroup (Fin n → v.Completion)) :
    latticeMap (g * h) L = latticeMap g (latticeMap h L) := by
  ext x
  rw [mem_latticeMap, mem_latticeMap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨h *ᵥ y, (mem_latticeMap).2 ⟨y, hy, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (mem_latticeMap).1 hz
    exact ⟨y, hy, by rw [Matrix.mulVec_mulVec]⟩

/-- The image under `g` is the preimage under `g⁻¹`. -/
theorem latticeMap_eq_comap {v : Place Fq k} {n : ℕ} (g : GL (Fin n) v.Completion)
    (L : AddSubgroup (Fin n → v.Completion)) :
    latticeMap g.1 L = L.comap (Matrix.mulVecLin (g⁻¹ : GL (Fin n) v.Completion).1).toAddMonoidHom := by
  ext x
  rw [mem_latticeMap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (g⁻¹ : GL (Fin n) v.Completion).1 *ᵥ (g.1 *ᵥ y) ∈ L
    rw [Matrix.mulVec_mulVec]
    simpa using hy
  · intro hx
    refine ⟨(g⁻¹ : GL (Fin n) v.Completion).1 *ᵥ x, hx, ?_⟩
    rw [Matrix.mulVec_mulVec]
    simp

/-- The image of a lattice under $g\in\mathrm{GL}_n(k_v)$ is a lattice. -/
theorem isLattice_latticeMap {v : Place Fq k} {n : ℕ} (g : GL (Fin n) v.Completion)
    {L : AddSubgroup (Fin n → v.Completion)} (hL : v.IsLattice L) :
    v.IsLattice (latticeMap g.1 L) := by
  rw [latticeMap_eq_comap]
  refine FieldModule.isKLattice_comap (weil_ff_completion_isPField v).1 hL ?_
  intro x y hxy
  have h : (g⁻¹ : GL (Fin n) v.Completion).1 *ᵥ x = (g⁻¹ : GL (Fin n) v.Completion).1 *ᵥ y := hxy
  have := congrArg (fun z => g.1 *ᵥ z) h
  simpa [Matrix.mulVec_mulVec] using this

/-- **Elementary divisors over $k_v$** (Weil II.§2, Thm. 1 for the $p$-field $k_v$): every lattice of $k_v^n$ is
$g\,\mathfrak r_v^n$ for some $g\in\mathrm{GL}_n(k_v)$. -/
theorem exists_gl_eq (v : Place Fq k) {n : ℕ} {L : AddSubgroup (Fin n → v.Completion)} (hL : v.IsLattice L) :
    ∃ g : GL (Fin n) v.Completion, L = latticeMap g.1 (stdLattice v n) := by
  have hfr : Module.finrank v.Completion (Fin n → v.Completion) = n := Module.finrank_fin_fun _
  obtain ⟨b, hb⟩ := FieldModule.weil_II_2_thm1 (weil_ff_completion_isPField v).1 hL
  have key : ∀ m : ℕ, m = n → ∀ b : Module.Basis (Fin m) v.Completion (Fin n → v.Completion),
      (L : Set (Fin n → v.Completion)) = {w | ∃ c : Fin m → v.Completion,
        (∀ i, c i ∈ FieldModule.pR (weil_ff_completion_isPField v).1) ∧ w = ∑ i, c i • b i} →
      ∃ g : GL (Fin n) v.Completion, L = latticeMap g.1 (stdLattice v n) := by
    rintro m rfl b hb
    have hdet : IsUnit (Matrix.of fun i j => b j i).det := by
      have h1 := (Pi.basisFun v.Completion (Fin m)).isUnit_det b
      rw [Module.Basis.det_apply] at h1
      have h2 : (Matrix.of fun i j => b j i) = (Pi.basisFun v.Completion (Fin m)).toMatrix b := by
        ext i j; simp [Module.Basis.toMatrix_apply]
      rw [h2]; exact h1
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
    refine ⟨u, ?_⟩
    ext w
    have hw : w ∈ L ↔ ∃ c : Fin m → v.Completion,
        (∀ i, c i ∈ FieldModule.pR (weil_ff_completion_isPField v).1) ∧ w = ∑ i, c i • b i := by
      have := Set.ext_iff.1 hb w
      exact this
    rw [hw, mem_latticeMap]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c, fun i => (mem_pR_iff v _).1 (hc i), ?_⟩
      rw [hu]
      ext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, fun i => (mem_pR_iff v _).2 (hy i), ?_⟩
      rw [hu]
      ext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
  exact key n rfl (b.reindex (finCongr hfr)) (by
    rw [hb]
    ext w
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun i => c ((finCongr hfr).symm i), fun i => hc _, ?_⟩
      simp only [Module.Basis.reindex_apply]
      exact (Equiv.sum_comp (finCongr hfr).symm (fun j => c j • b j)).symm
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun i => c (finCongr hfr i), fun i => hc _, ?_⟩
      simp only [Module.Basis.reindex_apply]
      have := Equiv.sum_comp (finCongr hfr) (fun i => c i • b ((finCongr hfr).symm i))
      simpa using this.symm)

/-- If `g` and its inverse have integral entries then `g` preserves `𝔯_v^n`. -/
theorem latticeMap_stdLattice_le {v : Place Fq k} {n : ℕ} {g : Matrix (Fin n) (Fin n) v.Completion}
    (h : ∀ i j, Valued.v (g i j) ≤ 1) : latticeMap g (stdLattice v n) ≤ stdLattice v n := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_latticeMap.1 hx
  exact fun i => valued_mulVec_le_one h hy i

/-- If `g` and `g⁻¹` have integral entries then `g 𝔯_v^n = 𝔯_v^n`. -/
theorem latticeMap_stdLattice_eq {v : Place Fq k} {n : ℕ} (g : GL (Fin n) v.Completion)
    (h1 : ∀ i j, Valued.v (g.1 i j) ≤ 1) (h2 : ∀ i j, Valued.v ((g⁻¹ : GL (Fin n) v.Completion).1 i j) ≤ 1) :
    latticeMap g.1 (stdLattice v n) = stdLattice v n := by
  refine le_antisymm (latticeMap_stdLattice_le h1) ?_
  intro x hx
  refine mem_latticeMap.2 ⟨(g⁻¹ : GL (Fin n) v.Completion).1 *ᵥ x, latticeMap_stdLattice_le h2 ?_, ?_⟩
  · exact mem_latticeMap.2 ⟨x, hx, rfl⟩
  · rw [Matrix.mulVec_mulVec]; simp

/-- If `g 𝔯^n ⊆ h 𝔯^n` then `v(det (h⁻¹ g)) ≤ 1`. -/
theorem valued_det_le_of_le {v : Place Fq k} {n : ℕ} (g h : GL (Fin n) v.Completion)
    (hle : latticeMap g.1 (stdLattice v n) ≤ latticeMap h.1 (stdLattice v n)) :
    Valued.v (h⁻¹ * g).1.det ≤ 1 := by
  apply valued_det_le_one
  intro i j
  have hmem : g.1 *ᵥ (Pi.single j 1) ∈ latticeMap h.1 (stdLattice v n) :=
    hle (mem_latticeMap.2 ⟨Pi.single j 1, fun l => by
      by_cases hl : l = j <;> simp [Pi.single_apply, hl], rfl⟩)
  obtain ⟨z, hz, hzeq⟩ := mem_latticeMap.1 hmem
  have : (h⁻¹ * g).1 *ᵥ (Pi.single j 1) = z := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hzeq, Matrix.mulVec_mulVec]
    simp
  have hij : (h⁻¹ * g).1 i j = ((h⁻¹ * g).1 *ᵥ (Pi.single j 1)) i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hij, this]
  exact hz i

/-- If $g\,\mathfrak r_v^n=h\,\mathfrak r_v^n$ then $h^{-1}g\in\mathrm{GL}_n(\mathfrak r_v)$, so
$v(\det g)=v(\det h)$. -/
theorem valued_det_eq_of_map_eq (v : Place Fq k) {n : ℕ} (g h : GL (Fin n) v.Completion)
    (hgh : latticeMap g.1 (stdLattice v n) =
      latticeMap h.1 (stdLattice v n)) :
    Valued.v g.1.det =
      Valued.v h.1.det := by
  have key : ∀ g h : GL (Fin n) v.Completion,
      latticeMap g.1 (stdLattice v n) ≤ latticeMap h.1 (stdLattice v n) →
      Valued.v g.1.det ≤ Valued.v h.1.det := by
    intro g h hle
    have h1 := valued_det_le_of_le g h hle
    have h2 : g.1.det = h.1.det * (h⁻¹ * g).1.det := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel_left]
    rw [h2, map_mul]
    exact mul_le_of_le_one_right' h1
  exact le_antisymm (key g h hgh.le) (key h g hgh.ge)

end Place

/-- The $v$-component $a_v\in\mathrm{GL}_n(k_v)$ of $a\in\mathrm{GL}_n(k_{\mathbb A})$. -/
def glAt (v : Place Fq k) {n : ℕ} (a : GL (Fin n) (FFAdeleRing Fq k)) : GL (Fin n) v.Completion :=
  Matrix.GeneralLinearGroup.map
    (RestrictedProduct.evalRingHom (fun w : Place Fq k => w.Completion) v) a

/-- The idele $\det a$ of $a\in\mathrm{GL}_n(k_{\mathbb A})$. -/
def detIdele {n : ℕ} (a : GL (Fin n) (FFAdeleRing Fq k)) : FFIdeleGroup Fq k :=
  Matrix.GeneralLinearGroup.det a

theorem comp_detIdele (v : Place Fq k) {n : ℕ} (a : GL (Fin n) (FFAdeleRing Fq k)) :
    FFIdeleGroup.comp (detIdele a) v = (glAt v a).1.det := by
  have h := RingHom.map_det (RestrictedProduct.evalRingHom (fun w : Place Fq k => w.Completion) v) a.1
  simp only [FFIdeleGroup.comp, detIdele, Matrix.GeneralLinearGroup.val_det_apply, glAt]
  exact h

/-- The entries of an adele matrix are integral at almost all places. -/
theorem eventually_valued_entry_le_one {n : ℕ} (M : Matrix (Fin n) (Fin n) (FFAdeleRing Fq k)) :
    ∀ᶠ v in cofinite, ∀ i j, Valued.v (M i j v) ≤ 1 :=
  Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (M i j).2

/-- For almost all `v`, `a_v 𝔯_v^n = 𝔯_v^n`. -/
theorem eventually_latticeMap_eq {n : ℕ} (a : GL (Fin n) (FFAdeleRing Fq k)) :
    ∀ᶠ v in cofinite, Place.latticeMap (glAt v a).1 (Place.stdLattice v n) = Place.stdLattice v n := by
  have e1 := eventually_valued_entry_le_one (Fq := Fq) (k := k) a.1
  have e2 := eventually_valued_entry_le_one (Fq := Fq) (k := k) (a⁻¹ : GL (Fin n) (FFAdeleRing Fq k)).1
  filter_upwards [e1, e2] with v hv1 hv2
  have hinv : (glAt v a)⁻¹ = glAt v a⁻¹ := by
    unfold glAt
    exact (_root_.map_inv (Matrix.GeneralLinearGroup.map
      (RestrictedProduct.evalRingHom (fun w : Place Fq k => w.Completion) v)) a).symm
  have h1 : ∀ i j, Valued.v ((glAt v a).1 i j) ≤ 1 := fun i j => hv1 i j
  have h2 : ∀ i j, Valued.v ((glAt v a)⁻¹.1 i j) ≤ 1 := by
    rw [hinv]
    exact fun i j => hv2 i j
  exact Place.latticeMap_stdLattice_eq (glAt v a) h1 h2

variable (Fq k) in
/-- **A coherent system** of $k_v$-lattices in $E_v=k_v^n$ (Weil VI.§1, Def. p. 97): a lattice $L_v$ at every place,
equal to $\mathfrak r_v^n$ for almost all $v$. -/
@[kb "weil1973bnt" "Ch. VI, §1, Def. p. 97 (coherent systems of lattices), E = k^n"]
structure CoherentSystem (n : ℕ) where
  /-- the lattice at $v$ -/
  L : ∀ v : Place Fq k, AddSubgroup (Fin n → v.Completion)
  isLattice : ∀ v : Place Fq k, v.IsLattice (L v)
  eventually_eq : ∀ᶠ v in cofinite, L v = Place.stdLattice v n

namespace CoherentSystem

variable {n : ℕ}

/-- The standard coherent system $L_0=(\mathfrak r_v^n)$ of the basis $\mathfrak e$. -/
def std (Fq k) [Field Fq] [Finite Fq] [Field k] [Algebra Fq k] [Algebra (RatFunc Fq) k]
    [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k] (n : ℕ) : CoherentSystem Fq k n where
  L v := Place.stdLattice v n
  isLattice v := Place.isLattice_stdLattice v n
  eventually_eq := Eventually.of_forall fun _ => rfl

/-- $U(L)=\prod_vL_v\subset E_{\mathbb A}=k_{\mathbb A}^n$. -/
def U (L : CoherentSystem Fq k n) : AddSubgroup (Fin n → FFAdeleRing Fq k) where
  carrier := {x | ∀ v, (fun i => x i v) ∈ L.L v}
  zero_mem' := fun v => (L.L v).zero_mem
  add_mem' {x y} hx hy := fun v => (L.L v).add_mem (hx v) (hy v)
  neg_mem' {x} hx := fun v => (L.L v).neg_mem (hx v)

theorem mem_U {L : CoherentSystem Fq k n} {x : Fin n → FFAdeleRing Fq k} :
    x ∈ L.U ↔ ∀ v, (fun i => x i v) ∈ L.L v := Iff.rfl

/-- $A(L)=E\cap U(L)$, the $\xi\in k^n$ with $\xi\in L_v$ at every place, an $\mathbb F_q$-space. -/
def A (L : CoherentSystem Fq k n) : Submodule Fq (Fin n → k) where
  carrier := {ξ | ∀ v, (fun i => v.toCompletion (ξ i)) ∈ L.L v}
  zero_mem' := fun v => by simpa [Pi.zero_def] using (L.L v).zero_mem
  add_mem' {x y} hx hy := fun v => by simpa [Pi.add_def] using (L.L v).add_mem (hx v) (hy v)
  smul_mem' c x hx := fun v => by
    have hr : v.toCompletion (algebraMap Fq k c) ∈ FieldModule.pR (weil_ff_completion_isPField v).1 := by
      rw [Place.mem_pR_iff, Place.valued_toCompletion]
      by_cases hc : c = 0
      · subst hc; simp
      · rw [v.valuation_algebraMap hc]
    have := (L.isLattice v).1 _ hr _ (hx v)
    convert this using 1
    ext i
    simp [Algebra.smul_def]

/-- $\lambda(L)=\dim_{\mathbb F_q}A(L)$. -/
def lam (L : CoherentSystem Fq k n) : ℕ := Module.finrank Fq L.A

/-- **The coherent system $(a_v\mathfrak r_v^n)$** of $a\in\mathrm{GL}_n(k_{\mathbb A})$ (Weil VI.§1, Prop. 2, first
part). -/
def ofGL (a : GL (Fin n) (FFAdeleRing Fq k)) : CoherentSystem Fq k n where
  L v := Place.latticeMap (glAt v a).1 (Place.stdLattice v n)
  isLattice v := Place.isLattice_latticeMap _ (Place.isLattice_stdLattice v n)
  eventually_eq := eventually_latticeMap_eq a

end CoherentSystem

/-- **Weil VI.§1, Prop. 2**: every coherent system is $L=a\,L_0$ for some $a\in\mathrm{GL}_n(k_{\mathbb A})$ (elementary
divisors at every place, and $a_v=1$ where $L_v=\mathfrak r_v^n$), and $\operatorname{div}(\det a)$ is determined by
$L$. -/
@[kb "weil1973bnt" "Ch. VI, §1, Prop. 2 (p. 98), E = k^n: L = a L_0 with a in GL_n(k_A), div(det a) determined by L"]
theorem weil_VI_1_prop2 {n : ℕ} (L : CoherentSystem Fq k n) :
    (∃ a : GL (Fin n) (FFAdeleRing Fq k), ∀ v, L.L v = (CoherentSystem.ofGL a).L v) ∧
    ∀ a b : GL (Fin n) (FFAdeleRing Fq k), (∀ v, L.L v = (CoherentSystem.ofGL a).L v) →
      (∀ v, L.L v = (CoherentSystem.ofGL b).L v) →
      FFIdeleGroup.div (detIdele a) = FFIdeleGroup.div (detIdele b) := by
  refine ⟨?_, ?_⟩
  · have hg : ∀ v : Place Fq k, ∃ g : GL (Fin n) v.Completion,
        L.L v = Place.latticeMap g.1 (Place.stdLattice v n) ∧
          (L.L v = Place.stdLattice v n → g = 1) := by
      intro v
      by_cases h : L.L v = Place.stdLattice v n
      · exact ⟨1, by rw [h]; simp [Place.latticeMap_one], fun _ => rfl⟩
      · obtain ⟨g, hg⟩ := Place.exists_gl_eq v (L.isLattice v)
        exact ⟨g, hg, fun h' => absurd h' h⟩
    choose g hgL hg1 using hg
    have hev : ∀ᶠ v in cofinite, g v = 1 := by
      filter_upwards [L.eventually_eq] with v hv using hg1 v hv
    let A : Matrix (Fin n) (Fin n) (FFAdeleRing Fq k) := Matrix.of fun i j =>
      ⟨fun v => (g v).1 i j, by
        filter_upwards [hev] with v hv
        show Valued.v ((g v).1 i j) ≤ 1
        rw [hv]
        by_cases h : i = j <;> simp [h]⟩
    let B : Matrix (Fin n) (Fin n) (FFAdeleRing Fq k) := Matrix.of fun i j =>
      ⟨fun v => ((g v)⁻¹ : GL (Fin n) v.Completion).1 i j, by
        filter_upwards [hev] with v hv
        show Valued.v (((g v)⁻¹ : GL (Fin n) v.Completion).1 i j) ≤ 1
        rw [hv]
        by_cases h : i = j <;> simp [h]⟩
    let ev : ∀ v : Place Fq k, Matrix (Fin n) (Fin n) (FFAdeleRing Fq k) →+*
        Matrix (Fin n) (Fin n) v.Completion := fun v =>
      (RestrictedProduct.evalRingHom (fun w : Place Fq k => w.Completion) v).mapMatrix
    have hA : ∀ v, ev v A = (g v).1 := fun v => by ext i j; rfl
    have hB : ∀ v, ev v B = ((g v)⁻¹ : GL (Fin n) v.Completion).1 := fun v => by ext i j; rfl
    have hAB : A * B = 1 := by
      have key : ∀ v, ev v (A * B) = ev v 1 := fun v => by
        rw [map_mul, map_one, hA v, hB v]; simp
      ext i j v
      exact congrFun (congrFun (key v) i) j
    have hBA : B * A = 1 := by
      have key : ∀ v, ev v (B * A) = ev v 1 := fun v => by
        rw [map_mul, map_one, hA v, hB v]; simp
      ext i j v
      exact congrFun (congrFun (key v) i) j
    refine ⟨⟨A, B, hAB, hBA⟩, fun v => ?_⟩
    have : glAt v (⟨A, B, hAB, hBA⟩ : GL (Fin n) (FFAdeleRing Fq k)) = g v := Units.ext (hA v)
    show L.L v = Place.latticeMap (glAt v (⟨A, B, hAB, hBA⟩ : GL (Fin n) (FFAdeleRing Fq k))).1
      (Place.stdLattice v n)
    rw [this]
    exact hgL v
  · intro a b ha hb
    ext v
    have h := Place.valued_det_eq_of_map_eq v (glAt v a) (glAt v b) ((ha v).symm.trans (hb v))
    rw [FFIdeleGroup.div_apply, FFIdeleGroup.div_apply, comp_detIdele, comp_detIdele]
    simp only [Place.ordC, h]

/-- **Weil VI.§1, Prop. 2** (two systems): two coherent systems $L$, $M$ differ by an element of
$\mathrm{GL}_n(k_{\mathbb A})$: $M_v=a_vL_v$ for all $v$. -/
theorem weil_VI_1_prop2_two {n : ℕ} (L M : CoherentSystem Fq k n) :
    ∃ a : GL (Fin n) (FFAdeleRing Fq k), ∀ v,
      M.L v = Place.latticeMap (glAt v a).1 (L.L v) := by
  obtain ⟨aL, haL⟩ := (weil_VI_1_prop2 L).1
  obtain ⟨aM, haM⟩ := (weil_VI_1_prop2 M).1
  refine ⟨aM * aL⁻¹, fun v => ?_⟩
  have hL : L.L v = Place.latticeMap (glAt v aL).1 (Place.stdLattice v n) := haL v
  have hM : M.L v = Place.latticeMap (glAt v aM).1 (Place.stdLattice v n) := haM v
  have hmap : glAt v (aM * aL⁻¹) = glAt v aM * (glAt v aL)⁻¹ := by
    unfold glAt; rw [map_mul, _root_.map_inv]
  rw [hL, hM, hmap, Units.val_mul, ← Place.latticeMap_mul]
  congr 1
  rw [mul_assoc]
  simp

namespace CoherentSystem

variable {n : ℕ}

/-- **The divisor of a coherent system**: $\operatorname{div}(\det a)$ for any $a$ with $L=aL_0$
(well defined by `weil_VI_1_prop2`). -/
def div (L : CoherentSystem Fq k n) : Divisor Fq k :=
  FFIdeleGroup.div (detIdele (weil_VI_1_prop2 L).1.choose)

theorem div_eq (L : CoherentSystem Fq k n) (a : GL (Fin n) (FFAdeleRing Fq k))
    (ha : ∀ v, L.L v = (ofGL a).L v) : L.div = FFIdeleGroup.div (detIdele a) :=
  (weil_VI_1_prop2 L).2 _ _ (weil_VI_1_prop2 L).1.choose_spec ha

/-- **Weil's $\delta(L)$**: the degree of $\operatorname{div}(\det a)$ for $L=aL_0$. -/
def delta (L : CoherentSystem Fq k n) : ℤ := Divisor.deg L.div

end CoherentSystem

/-- The matrix $P\in\mathrm{GL}_n(k)$ of a basis change, at the place $v$. -/
def glK (v : Place Fq k) {n : ℕ} (P : GL (Fin n) k) : GL (Fin n) v.Completion :=
  Matrix.GeneralLinearGroup.map v.toCompletion P

/-- **Weil VI.§1, Cor. 1 of Prop. 2**: let $P\in\mathrm{GL}_n(k)$ be the matrix of another basis $\mathfrak e'$ of
$E=k^n$, with coherent system $L_0'=(P\,\mathfrak r_v^n)$. If $L=a\,L_0'$ and $L=b\,L_0$, then
$\operatorname{div}(\det a)-\operatorname{div}(\det b)$ is principal; so the class of the divisor of $L$ and its degree
do not depend on the basis. -/
@[kb "weil1973bnt" "Ch. VI, §1, Cor. 1 of Prop. 2 (p. 98), E = k^n: the class and degree of div(det a) do not depend on the basis"]
theorem weil_VI_1_prop2_cor1 {n : ℕ} (L : CoherentSystem Fq k n) (P : GL (Fin n) k)
    (a b : GL (Fin n) (FFAdeleRing Fq k))
    (ha : ∀ v, L.L v = Place.latticeMap (glAt v a).1
      (Place.latticeMap (glK v P).1 (Place.stdLattice v n)))
    (hb : ∀ v, L.L v = (CoherentSystem.ofGL b).L v) :
    FFIdeleGroup.div (detIdele a) - FFIdeleGroup.div (detIdele b) ∈ principalDivisors Fq k ∧
      Divisor.deg (FFIdeleGroup.div (detIdele a)) = Divisor.deg (FFIdeleGroup.div (detIdele b)) := by
  set u : kˣ := Matrix.GeneralLinearGroup.det P with hu
  have hdiff : FFIdeleGroup.div (detIdele a) - FFIdeleGroup.div (detIdele b) = -Divisor.div u := by
    ext v
    have h := Place.valued_det_eq_of_map_eq v (glAt v a * glK v P) (glAt v b) (by
      rw [Units.val_mul, Place.latticeMap_mul]
      exact (ha v).symm.trans (hb v))
    rw [Units.val_mul, Matrix.det_mul] at h
    have hK : (glK v P).1.det = v.toCompletion (u : k) := by
      have := RingHom.map_det v.toCompletion P.1
      rw [hu, Matrix.GeneralLinearGroup.val_det_apply]
      exact this.symm
    have hne1 : (glAt v a).1.det ≠ 0 := by
      rw [← comp_detIdele]; exact FFIdeleGroup.comp_ne_zero _ v
    have hne2 : (glK v P).1.det ≠ 0 := by
      rw [hK]; exact (map_ne_zero v.toCompletion).2 u.ne_zero
    have h2 : v.ordC (glAt v a).1.det + v.ordC (glK v P).1.det = v.ordC (glAt v b).1.det := by
      rw [← v.ordC_mul hne1 hne2]
      simp only [Place.ordC, h]
    rw [Finsupp.sub_apply, Finsupp.neg_apply, FFIdeleGroup.div_apply, FFIdeleGroup.div_apply,
      comp_detIdele, comp_detIdele, Divisor.div_apply, ← Place.ordC_toCompletion, ← hK]
    omega
  refine ⟨?_, ?_⟩
  · rw [hdiff]
    exact neg_mem ((mem_principalDivisors_iff _).2 ⟨u, rfl⟩)
  · have h0 : Divisor.deg (FFIdeleGroup.div (detIdele a) - FFIdeleGroup.div (detIdele b)) = 0 := by
      rw [hdiff, _root_.map_neg, Divisor.deg_div_eq_zero, neg_zero]
    rw [_root_.map_sub] at h0
    omega

end NumberFieldKB.WeilBNT.FF
