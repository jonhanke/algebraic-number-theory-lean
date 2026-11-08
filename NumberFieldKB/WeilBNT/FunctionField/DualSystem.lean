import NumberFieldKB.WeilBNT.FunctionField.SelfDuality
import NumberFieldKB.WeilBNT.FunctionField.CoherentMeasure

/-!
# Dual coherent systems and Riemann–Roch for $E=k^n$ (Weil VI, text p. 99, Thm. 1)

$k$ is a global function field over $\mathbb F_q$, $E=k^n$, $E_{\mathbb A}=k_{\mathbb A}^n$, and $\chi=\psi_0\circ\hat\omega$
the basic character of $k_{\mathbb A}$ (`FFAdeleRing.chiA ψ₀`, `SelfDuality.lean`) with local components
$\chi_v$ (`chiV ψ₀ v`). $E'=k^n$ is identified with the dual of $E$ by $[x,y]=\sum_ix_iy_i$.

* `dualLattice ψ₀ v L` $=L^*=\{y\in k_v^n:\chi_v([x,y])=1\ \forall x\in L\}$ (Weil II.§5 for $k_v$).
* `dualLattice_stdLattice`: $(\mathfrak r_v^n)^*=(\mathfrak p_v^{-\mathfrak c(v)})^n$; `dualLattice_latticeMap`:
  $(gL)^*={}^tg^{-1}L^*$; `isLattice_dualLattice`: the dual of a lattice is a lattice.
* **`CoherentSystem.dual`** (Weil VI, text p. 99): the dual system $L'=(L_v^*)$ of a coherent system is a coherent
  system in $E'$.
* `chiA_eq_prod`: $\chi(z)=\prod_{v\in S}\chi_v(z_v)$ when $z_v\in\mathfrak p_v^{-\mathfrak c(v)}$ outside $S$.
* `exists_unique_addChar_vec`: every character of $k_{\mathbb A}^n$ is $x\mapsto\chi([a,x])$ for a unique $a\in
  k_{\mathbb A}^n$ (IV.§2, Thm. 3, first assertion, for $E=k^n$).
* `natCard_quotient_eq_natCard_A_dual`: $[E_{\mathbb A}:E+U(L)]=\lvert A(L')\rvert$ (the characters of the finite group
  $E_{\mathbb A}/(E+U(L))$ are the $\chi([a,\cdot])$, $a\in E\cap U(L')$).
* `natCard_quotient_eq`: $[E_{\mathbb A}:E+U(L)]=q^{\lambda(L)+\delta(L)+n(g-1)}$ (compare with a box
  $U(\mathfrak a)^n\supset U(L)$, $\deg\mathfrak a>2g-2$, where $E+U(\mathfrak a)^n=E_{\mathbb A}$; Riemann–Roch for
  $\mathfrak a$, $\mu(U(L))=q^{-\delta(L)}$).
* **`weil_VI_1_thm1_vec`** (Weil VI, Thm. 1, $E=k^n$): $\lambda(L)=\lambda(L')-\delta(L)-n(g-1)$, $\mathbb F_q$ the
  field of constants, $g$ the genus.

The proof is not Weil's (Poisson summation applied to the characteristic function of $U(L)$): for these compact open
subgroups Poisson summation is the finite counting of the two bullets above.
-/

open scoped WithZero NNReal ENNReal Topology
open Filter Matrix

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

variable (ψ₀ : AddChar Fq Circle) {n : ℕ}

/-- The local component $\chi_v$ of the basic character. -/
def chiV (v : Place Fq k) : AddChar v.Completion Circle where
  toFun t := FFAdeleRing.chiA ψ₀ (FFAdeleRing.single v t)
  map_zero_eq_one' := by
    have : FFAdeleRing.single v (0 : v.Completion) = 0 := by
      ext w
      by_cases h : w = v
      · subst h; rw [FFAdeleRing.single_apply_same]; rfl
      · rw [FFAdeleRing.single_apply_of_ne h]; rfl
    show FFAdeleRing.chiA ψ₀ (FFAdeleRing.single v 0) = 1
    rw [this, AddChar.map_zero_eq_one]
  map_add_eq_mul' s t := by
    rw [FFAdeleRing.single_add, AddChar.map_add_eq_mul]

theorem chiV_apply (v : Place Fq k) (t : v.Completion) :
    chiV ψ₀ v t = FFAdeleRing.chiA ψ₀ (FFAdeleRing.single v t) := rfl

/-- **The dual lattice** $L^*=\{y:\chi_v([x,y])=1\ \forall x\in L\}$ in $k_v^n$. -/
def dualLattice (v : Place Fq k) (L : AddSubgroup (Fin n → v.Completion)) : AddSubgroup (Fin n → v.Completion) where
  carrier := {y | ∀ x ∈ L, chiV ψ₀ v (x ⬝ᵥ y) = 1}
  zero_mem' := fun x _ => by simp
  add_mem' {y z} hy hz := fun x hx => by
    rw [dotProduct_add, AddChar.map_add_eq_mul, hy x hx, hz x hx, one_mul]
  neg_mem' {y} hy := fun x hx => by
    rw [dotProduct_neg, AddChar.map_neg_eq_inv, hy x hx, inv_one]

theorem mem_dualLattice {v : Place Fq k} {L : AddSubgroup (Fin n → v.Completion)} {y : Fin n → v.Completion} :
    y ∈ dualLattice ψ₀ v L ↔ ∀ x ∈ L, chiV ψ₀ v (x ⬝ᵥ y) = 1 := Iff.rfl

namespace FFAdeleRing

/-- If $\chi_v(ta)=1$ for all integral $t$ then $v(a)\le e^{\mathfrak c(v)}$. -/
theorem valued_le_exp_of_chiA (hψ₀ : ψ₀ ≠ 1) (v : Place Fq k)
    (a : v.Completion) (h : ∀ t : v.Completion, Valued.v t ≤ 1 → chiA ψ₀ (single v (t * a)) = 1) :
    Valued.v a ≤ WithZero.exp (canonical Fq k v) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨-, t', ht', hne⟩ := weil_IV_2_thm3_cor1_ff_order ψ₀ hψ₀ v
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hlt
    exact absurd hlt (not_lt.mpr zero_le)
  have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
  have hexp : WithZero.exp (canonical Fq k v + 1 : ℤ) ≤ Valued.v a := by
    rw [← WithZero.exp_log hva] at hlt ⊢
    rw [WithZero.exp_lt_exp] at hlt
    rw [WithZero.exp_le_exp]
    omega
  have hle : Valued.v (t' * a⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀, ← div_eq_mul_inv, div_le_one₀ (zero_lt_iff.2 hva)]
    exact ht'.trans hexp
  apply hne
  have := h _ hle
  rwa [inv_mul_cancel_right₀ ha0] at this

end FFAdeleRing

/-- $(\mathfrak r_v^n)^*=(\mathfrak p_v^{-\mathfrak c(v)})^n$. -/
theorem dualLattice_stdLattice (hψ₀ : ψ₀ ≠ 1) (v : Place Fq k) :
    dualLattice ψ₀ v (Place.stdLattice v n) = Place.boxLat v (fun _ => -canonical Fq k v) := by
  ext y
  rw [mem_dualLattice, Place.mem_boxLat]
  simp only [neg_neg]
  constructor
  · intro h i
    have := FFAdeleRing.valued_le_exp_of_chiA ψ₀ hψ₀ v (y i) (fun t ht => by
      have h1 := h (Pi.single i t) (fun j => by
        by_cases hj : j = i
        · subst hj; simpa using ht
        · simp [hj])
      rwa [single_dotProduct, chiV_apply] at h1)
    exact this
  · intro h x hx
    rw [chiV_apply]
    refine (FFAdeleRing.weil_IV_2_thm3_cor1_ff_order ψ₀ hψ₀ v).1 _ ?_
    simp only [dotProduct]
    refine Valuation.map_sum_le _ fun i _ => ?_
    rw [map_mul]
    calc Valued.v (x i) * Valued.v (y i) ≤ 1 * WithZero.exp (canonical Fq k v) :=
          mul_le_mul' (Place.mem_stdLattice.1 hx i) (h i)
      _ = _ := one_mul _

/-- $[gx,y]=[x,{}^tg\,y]$. -/
theorem transpose_dotProduct {v : Place Fq k} (g : Matrix (Fin n) (Fin n) v.Completion)
    (x y : Fin n → v.Completion) : (g *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (gᵀ *ᵥ y) := by
  rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

/-- $(gL)^*={}^tg^{-1}L^*$. -/
theorem dualLattice_latticeMap (v : Place Fq k) (g : GL (Fin n) v.Completion) (L : AddSubgroup (Fin n → v.Completion)) :
    dualLattice ψ₀ v (Place.latticeMap g.1 L) = Place.latticeMap (g⁻¹).1ᵀ (dualLattice ψ₀ v L) := by
  ext y
  rw [mem_dualLattice, Place.mem_latticeMap]
  constructor
  · intro h
    refine ⟨g.1ᵀ *ᵥ y, fun x hx => ?_, ?_⟩
    · rw [← transpose_dotProduct]
      exact h _ (Place.mem_latticeMap.2 ⟨x, hx, rfl⟩)
    · rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul]
      simp
  · rintro ⟨z, hz, rfl⟩ x hx
    obtain ⟨w, hw, rfl⟩ := Place.mem_latticeMap.1 hx
    rw [transpose_dotProduct, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul]
    simpa using hz w hw

/-- The dual of a lattice is a lattice. -/
theorem isLattice_dualLattice (hψ₀ : ψ₀ ≠ 1) (v : Place Fq k) {L : AddSubgroup (Fin n → v.Completion)}
    (hL : v.IsLattice L) : v.IsLattice (dualLattice ψ₀ v L) := by
  obtain ⟨g, rfl⟩ := Place.exists_gl_eq v hL
  rw [dualLattice_latticeMap, dualLattice_stdLattice ψ₀ hψ₀, ← Place.latticeMap_diagGL]
  let h : GL (Fin n) v.Completion := ⟨(g⁻¹).1ᵀ, g.1ᵀ, by
    rw [← Matrix.transpose_mul, ← Units.val_mul]; simp, by
    rw [← Matrix.transpose_mul, ← Units.val_mul]; simp⟩
  have := Place.isLattice_latticeMap (h * Place.diagGL v (fun _ => -canonical Fq k v))
    (Place.isLattice_stdLattice v n)
  rwa [Units.val_mul, Place.latticeMap_mul] at this

namespace CoherentSystem

/-- **Weil, VI, text p. 99**: the dual system $L'=(L_v^*)$ of a coherent system $L$ is a coherent system in $E'$
($L_v^*=\mathfrak r_v^n$ whenever $L_v=\mathfrak r_v^n$ and $\mathfrak c(v)=0$). -/
@[kb "weil1973bnt" "Ch. VI, text p. 99 (the dual system L' of a coherent system is coherent), E = k^n"]
def dual (hψ₀ : ψ₀ ≠ 1) (L : CoherentSystem Fq k n) : CoherentSystem Fq k n where
  L v := dualLattice ψ₀ v (L.L v)
  isLattice v := isLattice_dualLattice ψ₀ hψ₀ v (L.isLattice v)
  eventually_eq := by
    have hc : ∀ᶠ v in cofinite, canonical Fq k v = 0 :=
      Filter.eventually_cofinite.2 ((canonical Fq k).support.finite_toSet.subset
        (fun v hv => by simpa using hv))
    filter_upwards [L.eventually_eq, hc] with v hv hcv
    show dualLattice ψ₀ v (L.L v) = _
    rw [hv, dualLattice_stdLattice ψ₀ hψ₀, ← Place.boxLat_zero]
    congr 1
    funext i
    simp [hcv]

theorem dual_L (hψ₀ : ψ₀ ≠ 1) (L : CoherentSystem Fq k n) (v : Place Fq k) :
    (L.dual ψ₀ hψ₀).L v = dualLattice ψ₀ v (L.L v) := rfl

end CoherentSystem

namespace FFAdeleRing

/-- An additive character sends finite sums to finite products. -/
theorem addChar_map_sum {A M : Type*} [AddCommGroup A] [CommMonoid M] (χ : AddChar A M) {ι : Type*}
    (f : ι → A) (T : Finset ι) : χ (∑ v ∈ T, f v) = ∏ v ∈ T, χ (f v) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- $\chi(z)=\prod_{v\in S}\chi_v(z_v)$ when $\mathfrak v(z_v)\le q^{\mathfrak c(v)}$ for $v\notin S$. -/
theorem chiA_eq_prod (z : FFAdeleRing Fq k) (S : Finset (Place Fq k))
    (hS : ∀ v ∉ S, Valued.v (z v) ≤ WithZero.exp (canonical Fq k v)) :
    chiA ψ₀ z = ∏ v ∈ S, chiV ψ₀ v (z v) := by
  classical
  have hsum : ∀ u, (∑ v ∈ S, single v (z v)) u = if u ∈ S then z u else 0 := by
    intro u
    have h := map_sum (RestrictedProduct.evalRingHom (fun w : Place Fq k => w.Completion) u)
      (fun v => single v (z v)) S
    change (∑ v ∈ S, single v (z v)) u = ∑ v ∈ S, single v (z v) u at h
    rw [h]
    by_cases hu : u ∈ S
    · rw [if_pos hu, Finset.sum_eq_single_of_mem u hu]
      · exact single_apply_same _ _
      · intro v _ hvu
        exact single_apply_of_ne (Ne.symm hvu) _
    · rw [if_neg hu]
      exact Finset.sum_eq_zero fun v hv => single_apply_of_ne (v := v) (w := u) (fun h => hu (h ▸ hv)) _
  have hw : z - ∑ v ∈ S, single v (z v) ∈ U (canonical Fq k) := by
    intro u
    show Valued.v ((z - ∑ v ∈ S, single v (z v)) u) ≤ _
    have : (z - ∑ v ∈ S, single v (z v)) u = z u - (∑ v ∈ S, single v (z v)) u := rfl
    rw [this, hsum]
    by_cases hu : u ∈ S
    · simp [hu]
    · simpa [hu] using hS u hu
  have hz : z = ∑ v ∈ S, single v (z v) + (z - ∑ v ∈ S, single v (z v)) := by abel
  have h2 := AddChar.map_add_eq_mul (chiA ψ₀) (∑ v ∈ S, single v (z v)) (z - ∑ v ∈ S, single v (z v))
  rw [← hz, addChar_map_sum] at h2
  have h1 : chiA ψ₀ (z - ∑ v ∈ S, single v (z v)) = 1 := by
    rw [chiA_apply, omegaA_eq_zero_of_mem_U hw, AddChar.map_zero_eq_one]
  rw [h1, mul_one] at h2
  rw [h2]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [chiV_apply]

end FFAdeleRing

/-- **Weil, IV.§2, Thm. 3, first assertion, $E=k^n$, function fields**: every character of $k_{\mathbb A}^n$ is
$x\mapsto\chi([a,x])$ for one and only one $a\in k_{\mathbb A}^n$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Thm. 3 (p. 66), first assertion, E = k^n, function fields"]
theorem exists_unique_addChar_vec (hψ₀ : ψ₀ ≠ 1) (ψ : AddChar (Fin n → FFAdeleRing Fq k) Circle)
    (hψ : Continuous ψ) : ∃! a : Fin n → FFAdeleRing Fq k, ∀ x, ψ x = FFAdeleRing.chiA ψ₀ (a ⬝ᵥ x) := by
  classical
  let ψi : Fin n → AddChar (FFAdeleRing Fq k) Circle := fun i =>
    ψ.compAddMonoidHom (AddMonoidHom.single (fun _ : Fin n => FFAdeleRing Fq k) i)
  have hψi : ∀ i, Continuous (ψi i) := fun i =>
    hψ.comp (continuous_pi fun j => by
      by_cases h : j = i
      · subst h; exact continuous_id.congr fun x => by simp
      · exact (continuous_const (y := (0 : FFAdeleRing Fq k))).congr fun x => by simp [h])
  have hψi_apply : ∀ i x, ψi i x = ψ (Pi.single i x) := fun i x => rfl
  choose a ha using fun i => (FFAdeleRing.weil_IV_2_thm3_ff_char ψ₀ hψ₀ (ψi i) (hψi i)).exists
  refine ⟨a, fun x => ?_, fun b hb => ?_⟩
  · have hx : x = ∑ i, Pi.single i (x i) := (Finset.univ_sum_single x).symm
    conv_lhs => rw [hx]
    rw [FFAdeleRing.addChar_map_sum]
    simp_rw [← hψi_apply, ha]
    rw [← FFAdeleRing.addChar_map_sum]
    simp [dotProduct]
  · funext i
    refine (FFAdeleRing.weil_IV_2_thm3_ff_char ψ₀ hψ₀ (ψi i) (hψi i)).unique ?_ (ha i)
    intro x
    rw [hψi_apply, hb, dotProduct_single]

/-- $E+U(L)$ in $E_{\mathbb A}$. -/
def principalAddU (L : CoherentSystem Fq k n) : AddSubgroup (Fin n → FFAdeleRing Fq k) :=
  AddSubgroup.pi Set.univ (fun _ => FFAdeleRing.diagSubgroup Fq k) ⊔ L.U

/-- Counting identity for subgroups `U ≤ M` of `G` with `G = Γ + M` and `M/U` finite. -/
theorem card_quot_identity {G : Type*} [AddCommGroup G] (Γ M U : AddSubgroup G) (hUM : U ≤ M)
    (hG : ∀ g : G, ∃ γ ∈ Γ, ∃ m ∈ M, g = γ + m) [Finite (M ⧸ U.addSubgroupOf M)] :
    Finite (G ⧸ (Γ ⊔ U)) ∧ Nat.card (M ⧸ U.addSubgroupOf M) * Nat.card (Γ ⊓ U : AddSubgroup G) =
      Nat.card (Γ ⊓ M : AddSubgroup G) * Nat.card (G ⧸ (Γ ⊔ U)) := by
  classical
  let f : M →+ G ⧸ (Γ ⊔ U) := (QuotientAddGroup.mk' (Γ ⊔ U)).comp M.subtype
  have hf : U.addSubgroupOf M ≤ f.ker := by
    intro m hm
    rw [AddSubgroup.mem_addSubgroupOf] at hm
    rw [AddMonoidHom.mem_ker]
    show ((m : G) : G ⧸ (Γ ⊔ U)) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact AddSubgroup.mem_sup_right hm
  let β : M ⧸ U.addSubgroupOf M →+ G ⧸ (Γ ⊔ U) := QuotientAddGroup.lift _ f hf
  let α : (Γ ⊓ M : AddSubgroup G) →+ M ⧸ U.addSubgroupOf M :=
    (QuotientAddGroup.mk' _).comp
      { toFun := fun p => ⟨p.1, p.2.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hβ : ∀ m : M, β (QuotientAddGroup.mk m) = ((m : G) : G ⧸ (Γ ⊔ U)) := fun m => rfl
  have hα : ∀ p : (Γ ⊓ M : AddSubgroup G), α p = QuotientAddGroup.mk (⟨p.1, p.2.2⟩ : M) := fun p => rfl
  have hβsurj : Function.Surjective β := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨γ, hγ, m, hm, rfl⟩ := hG g
    refine ⟨QuotientAddGroup.mk ⟨m, hm⟩, ?_⟩
    rw [hβ]
    rw [QuotientAddGroup.eq]
    have : -m + (γ + m) = γ := by abel
    show -m + (γ + m) ∈ Γ ⊔ U
    rw [this]; exact AddSubgroup.mem_sup_left hγ
  have hker : β.ker = α.range := by
    ext x
    obtain ⟨m, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range, hβ]
    constructor
    · intro h
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_sup] at h
      obtain ⟨γ, hγ, u, hu, hmu⟩ := h
      have hγM : γ ∈ M := by
        have : γ = (m : G) - u := by rw [← hmu]; abel
        rw [this]; exact M.sub_mem m.2 (hUM hu)
      refine ⟨⟨γ, hγ, hγM⟩, ?_⟩
      rw [hα, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      show -γ + (m : G) ∈ U
      have : -γ + (m : G) = u := by rw [← hmu]; abel
      rw [this]; exact hu
    · rintro ⟨p, hp⟩
      rw [hα, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hp
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_sup]
      refine ⟨p.1, p.2.1, -p.1 + (m : G), hp, ?_⟩
      abel
  have hker0 : ∀ p : (Γ ⊓ M : AddSubgroup G), α p = 0 ↔ (p : G) ∈ U := by
    intro p
    rw [hα, ← QuotientAddGroup.mk_zero, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -(p : G) + 0 ∈ U ↔ _
    rw [add_zero, neg_mem_iff]
  have e : α.ker ≃ (Γ ⊓ U : AddSubgroup G) :=
    { toFun := fun p => ⟨(p.1 : G), p.1.2.1, (hker0 p.1).1 p.2⟩
      invFun := fun u => ⟨⟨u, u.2.1, hUM u.2.2⟩, (hker0 _).2 u.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun u => rfl }
  have h1 := AddSubgroup.card_ker_mul_card_range β
  have h2 := AddSubgroup.card_ker_mul_card_range α
  rw [AddMonoidHom.range_eq_top_of_surjective _ hβsurj, AddSubgroup.card_top, hker] at h1
  refine ⟨Finite.of_surjective β hβsurj, ?_⟩
  rw [← h1, ← Nat.card_congr e, ← h2]
  ring

/-- A compact subgroup has finite quotient by an open subgroup. -/
theorem finite_quot_of_compact_open {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (M U : AddSubgroup G) (hM : IsCompact (M : Set G)) (hU : IsOpen (U : Set G)) :
    Finite (M ⧸ U.addSubgroupOf M) := by
  have : CompactSpace M := isCompact_iff_compactSpace.mp hM
  exact AddSubgroup.quotient_finite_of_isOpen _ (AddSubgroup.addSubgroupOf_isOpen M U hU)

/-- A character trivial on an open subgroup is continuous. -/
theorem continuous_of_trivial_on_open {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (ψ : AddChar G Circle) (U : AddSubgroup G) (hU : IsOpen (U : Set G)) (h : ∀ x ∈ U, ψ x = 1) :
    Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro x
  have hn : {y : G | y - x ∈ (U : Set G)} ∈ nhds x :=
    (hU.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  refine (continuousAt_const (y := ψ x)).congr (Filter.eventually_of_mem hn fun y hy => ?_)
  show ψ x = ψ y
  have h1 := h (y - x) hy
  rw [AddChar.map_sub_eq_div, div_eq_one] at h1
  exact h1.symm

/-- The subgroup $\prod_iU(\mathfrak a)$ of $k_{\mathbb A}^n$. -/
def boxU (n : ℕ) (a : Divisor Fq k) : AddSubgroup (Fin n → FFAdeleRing Fq k) :=
  AddSubgroup.pi Set.univ (fun _ => FFAdeleRing.U a)

/-- Membership in the box $U(\mathfrak a)^n$. -/
theorem mem_boxU {n : ℕ} {a : Divisor Fq k} {x : Fin n → FFAdeleRing Fq k} :
    x ∈ boxU n a ↔ ∀ i, x i ∈ FFAdeleRing.U a :=
  ⟨fun h i => h i (Set.mem_univ i), fun h i _ => h i⟩

/-- $E=k^n$ inside $k_{\mathbb A}^n$. -/
def diagVec (Fq k) [Field Fq] [Finite Fq] [Field k] [Algebra Fq k] [Algebra (RatFunc Fq) k]
    [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k] (n : ℕ) : AddSubgroup (Fin n → FFAdeleRing Fq k) :=
  AddSubgroup.pi Set.univ (fun _ => FFAdeleRing.diagSubgroup Fq k)

/-- Membership in $k^n\subset k_{\mathbb A}^n$. -/
theorem mem_diagVec {n : ℕ} {x : Fin n → FFAdeleRing Fq k} :
    x ∈ diagVec Fq k n ↔ ∀ i, ∃ ξ : k, FFAdeleRing.diag ξ = x i :=
  ⟨fun h i => FFAdeleRing.mem_diagSubgroup.1 (h i (Set.mem_univ i)),
    fun h i _ => FFAdeleRing.mem_diagSubgroup.2 (h i)⟩

/-- Unfolding `principalAddU`. -/
theorem principalAddU_eq (L : CoherentSystem Fq k n) : principalAddU L = diagVec Fq k n ⊔ L.U := rfl

/-- $U(L)$ is open in $k_{\mathbb A}^n$. -/
theorem isOpen_U_vec (L : CoherentSystem Fq k n) : IsOpen (L.U : Set (Fin n → FFAdeleRing Fq k)) :=
  FFAdeleVec.isOpen_USet L

/-- $A(L)\simeq E\cap U(L)$. -/
theorem nonempty_equiv_A (L : CoherentSystem Fq k n) :
    Nonempty (L.A ≃ (diagVec Fq k n ⊓ L.U : AddSubgroup _)) := by
  refine ⟨Equiv.ofBijective
    (fun ξ : L.A => (⟨fun i => FFAdeleRing.diag (ξ.1 i), ⟨mem_diagVec.2 fun i => ⟨ξ.1 i, rfl⟩,
      fun v => ξ.2 v⟩⟩ : (diagVec Fq k n ⊓ L.U : AddSubgroup _))) ⟨?_, ?_⟩⟩
  · intro ξ η h
    apply Subtype.ext
    funext i
    exact FFAdeleRing.diag_injective (congrFun (congrArg Subtype.val h) i)
  · rintro ⟨x, hxΓ, hxU⟩
    choose ξ hξ using mem_diagVec.1 hxΓ
    refine ⟨⟨ξ, fun v => ?_⟩, ?_⟩
    · have e : (fun i => v.toCompletion (ξ i)) = (fun i => (x i) v) :=
        funext fun i => by rw [← hξ i]; rfl
      rw [e]; exact hxU v
    · apply Subtype.ext
      funext i
      exact hξ i

/-- $\lvert E\cap U(L)\rvert=\lvert A(L)\rvert$. -/
theorem natCard_inf_U (L : CoherentSystem Fq k n) :
    Nat.card (diagVec Fq k n ⊓ L.U : AddSubgroup _) = Nat.card L.A :=
  (Nat.card_congr (nonempty_equiv_A L).some).symm

/-- $U(\mathfrak a)^n/U(L)$ is finite. -/
theorem finite_box_quot (L : CoherentSystem Fq k n) (a : Divisor Fq k) :
    Finite (boxU n a ⧸ L.U.addSubgroupOf (boxU n a)) := by
  have hcpt : IsCompact (boxU n a : Set (Fin n → FFAdeleRing Fq k)) := by
    have : (boxU n a : Set (Fin n → FFAdeleRing Fq k)) =
        Set.pi Set.univ (fun _ => (FFAdeleRing.U a : Set (FFAdeleRing Fq k))) := by
      ext x; exact ⟨fun h i _ => mem_boxU.1 h i, fun h => mem_boxU.2 fun i => h i (Set.mem_univ i)⟩
    rw [this]
    exact isCompact_univ_pi fun _ => FFAdeleRing.isCompact_U a
  exact finite_quot_of_compact_open (boxU n a) L.U hcpt (isOpen_U_vec L)

/-- **The counting step**: for a divisor $\mathfrak a$ with $U(L)\subset U(\mathfrak a)^n$ and
$k_{\mathbb A}=k+U(\mathfrak a)$. -/
theorem count_aux (L : CoherentSystem Fq k n) {a : Divisor Fq k} (hUa : L.U ≤ boxU n a)
    (hsurj : ∀ y : FFAdeleRing Fq k, ∃ ξ : k, y - FFAdeleRing.diag ξ ∈ FFAdeleRing.U a) :
    Finite ((Fin n → FFAdeleRing Fq k) ⧸ principalAddU L) ∧
      Nat.card (boxU n a ⧸ L.U.addSubgroupOf (boxU n a)) * Nat.card L.A =
        Nat.card (diagVec Fq k n ⊓ boxU n a : AddSubgroup _) *
          Nat.card ((Fin n → FFAdeleRing Fq k) ⧸ principalAddU L) := by
  have hfin := finite_box_quot L a
  have hG : ∀ g : Fin n → FFAdeleRing Fq k, ∃ γ ∈ diagVec Fq k n, ∃ m ∈ boxU n a, g = γ + m := by
    intro g
    choose ξ hξ using fun i => hsurj (g i)
    refine ⟨fun i => FFAdeleRing.diag (ξ i), mem_diagVec.2 fun i => ⟨ξ i, rfl⟩, g - fun i => FFAdeleRing.diag (ξ i),
      mem_boxU.2 fun i => by rw [Pi.sub_apply]; exact hξ i, (add_sub_cancel _ _).symm⟩
  have key := @card_quot_identity (Fin n → FFAdeleRing Fq k) _ (diagVec Fq k n) (boxU n a) L.U hUa hG hfin
  rw [← principalAddU_eq, natCard_inf_U] at key
  exact key

/-- Every $U(L)$ lies in a box $U(\mathfrak a)^n$ with $\mathfrak a\succ\mathfrak a_0$ arbitrarily large. -/
theorem exists_box_ge (L : CoherentSystem Fq k n) (a0 : Divisor Fq k) :
    ∃ a : Divisor Fq k, a0 ≤ a ∧ L.U ≤ boxU n a := by
  classical
  choose κ ν hκ hL hdet hν using fun v : Place Fq k => Place.local_decomp v (L.isLattice v)
  have hfin : (Function.support fun v : Place Fq k => ∑ i, |ν v i|).Finite := by
    refine (Filter.eventually_cofinite.1 L.eventually_eq).subset ?_
    intro v hv h
    apply hv
    simp [hν v h]
  let b : Divisor Fq k := Finsupp.ofSupportFinite _ hfin
  have hb : ∀ v, b v = ∑ i, |ν v i| := fun v => rfl
  have key : ∀ v, ∀ y ∈ L.L v, ∀ i, Valued.v (y i) ≤ WithZero.exp (b v) := by
    intro v y hy i
    rw [hL v] at hy
    obtain ⟨z, hz, rfl⟩ := Place.mem_latticeMap.1 hy
    simp only [Matrix.mulVec, dotProduct]
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    have h1 := Place.entry_le_one_of_latticeMap_eq (hκ v) i j
    have h2 : Valued.v (z j) ≤ WithZero.exp (b v) := by
      refine (Place.mem_boxLat.1 hz j).trans (WithZero.exp_le_exp.2 ?_)
      rw [hb]
      have h3 : |ν v j| ≤ ∑ i, |ν v i| :=
        Finset.single_le_sum (f := fun i => |ν v i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
      linarith [neg_le_abs (ν v j)]
    calc Valued.v ((κ v).1 i j) * Valued.v (z j) ≤ 1 * WithZero.exp (b v) := mul_le_mul' h1 h2
      _ = _ := one_mul _
  refine ⟨b ⊔ a0, le_sup_right, fun x hx => mem_boxU.2 fun i => (FFAdeleRing.mem_U_iff _ _).2 fun v => ?_⟩
  exact (key v _ (hx v) i).trans (WithZero.exp_le_exp.2 ((le_sup_left : b ≤ b ⊔ a0) v))

/-- The Riemann–Roch space $A(\mathfrak a)$ is finite. -/
theorem finite_RR (a : Divisor Fq k) : Finite a.riemannRochSpace := by
  obtain ⟨b0, hb0⟩ := FFAdeleRing.exists_deg_neg (Fq := Fq) (k := k)
  have h := Divisor.deg_nonneg (sub_nonneg.2 (inf_le_left : b0 ⊓ a ≤ b0))
  rw [_root_.map_sub] at h
  exact FFAdeleRing.finite_riemannRochSpace (inf_le_right : b0 ⊓ a ≤ a) (by omega)

/-- $\lvert A(\mathfrak a)\rvert=q^{\lambda(\mathfrak a)}$. -/
theorem natCard_RR (a : Divisor Fq k) : Nat.card a.riemannRochSpace = Nat.card Fq ^ a.ell := by
  obtain ⟨b0, hb0⟩ := FFAdeleRing.exists_deg_neg (Fq := Fq) (k := k)
  have h := Divisor.deg_nonneg (sub_nonneg.2 (inf_le_left : b0 ⊓ a ≤ b0))
  rw [_root_.map_sub] at h
  exact FFAdeleRing.natCard_riemannRochSpace (inf_le_right : b0 ⊓ a ≤ a) (by omega)

/-- $\lvert E\cap U(\mathfrak a)^n\rvert=q^{n\lambda(\mathfrak a)}$. -/
theorem natCard_inf_box (a : Divisor Fq k) :
    Nat.card (diagVec Fq k n ⊓ boxU n a : AddSubgroup _) = (Nat.card Fq ^ a.ell) ^ n := by
  haveI := finite_RR a
  have e : (Fin n → a.riemannRochSpace) ≃ (diagVec Fq k n ⊓ boxU n a : AddSubgroup _) := by
    refine Equiv.ofBijective
      (fun η => (⟨fun i => FFAdeleRing.diag ((η i : a.riemannRochSpace) : k),
        ⟨mem_diagVec.2 fun i => ⟨_, rfl⟩,
          mem_boxU.2 fun i => (FFAdeleRing.diag_mem_U_iff a _).2 (η i).2⟩⟩ :
          (diagVec Fq k n ⊓ boxU n a : AddSubgroup _))) ⟨?_, ?_⟩
    · intro η η' h
      funext i
      apply Subtype.ext
      exact FFAdeleRing.diag_injective (congrFun (congrArg Subtype.val h) i)
    · rintro ⟨x, hxΓ, hxM⟩
      choose ξ hξ using mem_diagVec.1 hxΓ
      refine ⟨fun i => ⟨ξ i, (FFAdeleRing.diag_mem_U_iff a _).1 (by rw [hξ i]; exact mem_boxU.1 hxM i)⟩, ?_⟩
      apply Subtype.ext
      funext i
      exact hξ i
  rw [← Nat.card_congr e, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, natCard_RR]

/-- $A(L)$ is finite. -/
theorem finite_A (L : CoherentSystem Fq k n) {a : Divisor Fq k} (hUa : L.U ≤ boxU n a) : Finite L.A := by
  haveI := finite_RR a
  have hP : Finite (diagVec Fq k n ⊓ boxU n a : AddSubgroup _) := by
    apply Nat.finite_of_card_ne_zero
    rw [natCard_inf_box]
    exact pow_ne_zero _ (pow_ne_zero _ (Nat.card_pos (α := Fq)).ne')
  haveI : Finite (diagVec Fq k n ⊓ L.U : AddSubgroup _) :=
    Finite.of_injective (AddSubgroup.inclusion (inf_le_inf_left (diagVec Fq k n) hUa))
      (AddSubgroup.inclusion_injective _)
  exact Finite.of_equiv _ (nonempty_equiv_A L).some.symm

/-- $\lvert A(L)\rvert=q^{\lambda(L)}$ if $A(L)$ is finite. -/
theorem natCard_A (L : CoherentSystem Fq k n) [Finite L.A] : Nat.card L.A = Nat.card Fq ^ L.lam := by
  haveI : Module.Finite Fq L.A := Module.Finite.of_finite
  exact Module.natCard_eq_pow_finrank (K := Fq) (V := L.A)

/-- Cast from $[0,\infty]$ to $\mathbb Q$ of an integer-power identity. -/
theorem cast_zpow_eq (m q : ℕ) (hq : q ≠ 0) (z : ℤ) (h : (m : ℝ≥0∞) = (q : ℝ≥0∞) ^ z) :
    (m : ℚ) = (q : ℚ) ^ z := by
  have hq' : (q : ℝ≥0) ≠ 0 := by exact_mod_cast hq
  have h1 : ((m : ℝ≥0) : ℝ≥0∞) = (((q : ℝ≥0) ^ z : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_zpow hq']; simpa using h
  have h2 : (m : ℝ≥0) = (q : ℝ≥0) ^ z := ENNReal.coe_injective h1
  have h3 : (m : ℝ) = (q : ℝ) ^ z := by
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h2
    simpa using this
  apply Rat.cast_injective (α := ℝ)
  push_cast
  exact h3

/-- Solving `Q^a = m * Q^(-b)` for `m` in $[0,\infty]$. -/
theorem ennreal_eq_of_mul {Q : ℝ≥0∞} (hQ0 : Q ≠ 0) (hQt : Q ≠ ⊤) (m : ℕ) (a b : ℤ)
    (h : Q ^ a = (m : ℝ≥0∞) * Q ^ (-b)) : (m : ℝ≥0∞) = Q ^ (a + b) := by
  rw [ENNReal.zpow_add hQ0 hQt, h, mul_assoc, ← ENNReal.zpow_add hQ0 hQt, neg_add_cancel, zpow_zero, mul_one]

/-- $[U(\mathfrak a)^n:U(L)]=q^{n\deg\mathfrak a+\delta(L)}$ (via Haar measure). -/
theorem natCard_box_quot_vec (L : CoherentSystem Fq k n) {a : Divisor Fq k} (hUa : L.U ≤ boxU n a) :
    (Nat.card (boxU n a ⧸ L.U.addSubgroupOf (boxU n a)) : ℚ) =
      (Nat.card Fq : ℚ) ^ ((n : ℤ) * Divisor.deg a + L.delta) := by
  haveI := finite_box_quot L a
  let K : AddSubgroup (FFAdeleVec Fq k n) := boxU n a
  let H : AddSubgroup (FFAdeleVec Fq k n) := L.U
  have hHK : H ≤ K := hUa
  haveI : Finite (K ⧸ H.addSubgroupOf K) := finite_box_quot L a
  have hmeas := FFAdeleRing.measure_eq_card_mul (G := FFAdeleVec Fq k n) (haarVec Fq k n) hHK
    (FFAdeleVec.isOpen_USet L).measurableSet
  have h1 : haarVec Fq k n (K : Set (FFAdeleVec Fq k n)) =
      (Nat.card Fq : ℝ≥0∞) ^ ((n : ℤ) * Divisor.deg a) := by
    have := haarVec_pi_U (Fq := Fq) (k := k) (fun _ : Fin n => a)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have h2 : haarVec Fq k n (H : Set (FFAdeleVec Fq k n)) =
      (Nat.card Fq : ℝ≥0∞) ^ (-L.delta) := weil_VI_1_prop2_cor2 L
  rw [h1, h2] at hmeas
  have hQ0 : (Nat.card Fq : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact (Nat.card_pos (α := Fq)).ne'
  have hQt : (Nat.card Fq : ℝ≥0∞) ≠ ⊤ := by simp
  exact cast_zpow_eq _ _ (Nat.card_pos (α := Fq)).ne' _ (ennreal_eq_of_mul hQ0 hQt _ _ _ hmeas)

/-- The character $x\mapsto\chi([a,x])$ of $k_{\mathbb A}^n$. -/
def charVec (ψ₀ : AddChar Fq Circle) (a : Fin n → FFAdeleRing Fq k) : AddChar (Fin n → FFAdeleRing Fq k) Circle :=
  (FFAdeleRing.chiA ψ₀).compAddMonoidHom (AddMonoidHom.mk' (fun x => a ⬝ᵥ x) (dotProduct_add a))

/-- Evaluation of `charVec`. -/
theorem charVec_apply (a x : Fin n → FFAdeleRing Fq k) :
    charVec ψ₀ a x = FFAdeleRing.chiA ψ₀ (a ⬝ᵥ x) := rfl

/-- `charVec` is continuous. -/
theorem continuous_charVec (a : Fin n → FFAdeleRing Fq k) : Continuous (charVec ψ₀ a) := by
  show Continuous fun x : Fin n → FFAdeleRing Fq k => FFAdeleRing.chiA ψ₀ (∑ i, a i * x i)
  exact (FFAdeleRing.continuous_chiA ψ₀).comp
    (continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i))

/-- The additive map $t\mapsto\text{single}_v\,t$. -/
def FFAdeleRing.singleAdd (v : Place Fq k) : v.Completion →+ FFAdeleRing Fq k :=
  AddMonoidHom.mk' (FFAdeleRing.single v) (FFAdeleRing.single_add v)

/-- The $v$-component of $[a,x]$ is $[a_v,x_v]$. -/
theorem dotProduct_apply_adele (a x : Fin n → FFAdeleRing Fq k) (v : Place Fq k) :
    (a ⬝ᵥ x) v = (fun i => a i v) ⬝ᵥ (fun i => x i v) := by
  have h := map_sum (RestrictedProduct.evalRingHom (fun w : Place Fq k => w.Completion) v)
    (fun i => a i * x i) Finset.univ
  exact h

/-- $\chi([a,\cdot])$ is trivial on $k^n$ iff $a\in k^n$. -/
theorem charVec_trivial_diag_iff (hψ₀ : ψ₀ ≠ 1) (a : Fin n → FFAdeleRing Fq k) :
    (∀ γ ∈ diagVec Fq k n, charVec ψ₀ a γ = 1) ↔ ∀ i, ∃ η : k, a i = FFAdeleRing.diag η := by
  classical
  constructor
  · intro h i
    refine (FFAdeleRing.weil_IV_2_thm3_ff_annihilator ψ₀ hψ₀ (a i)).1 fun ξ => ?_
    have := h (Pi.single i (FFAdeleRing.diag ξ)) (mem_diagVec.2 fun j => by
      by_cases hj : j = i
      · subst hj; exact ⟨ξ, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, hj, FFAdeleRing.diag_zero]⟩)
    rwa [charVec_apply, dotProduct_single] at this
  · intro h γ hγ
    choose η hη using h
    choose ζ hζ using mem_diagVec.1 hγ
    rw [charVec_apply]
    show FFAdeleRing.chiA ψ₀ (∑ i, a i * γ i) = 1
    rw [FFAdeleRing.addChar_map_sum]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [hη i, ← hζ i, FFAdeleRing.diag_mul_diag, FFAdeleRing.chiA_diag]

/-- $\chi([a,\cdot])$ is trivial on $U(L)$ iff $a_v\in L_v^*$ for all $v$. -/
theorem charVec_trivial_U_iff (hψ₀ : ψ₀ ≠ 1) (L : CoherentSystem Fq k n) (a : Fin n → FFAdeleRing Fq k) :
    (∀ x ∈ L.U, charVec ψ₀ a x = 1) ↔ ∀ v, (fun i => a i v) ∈ dualLattice ψ₀ v (L.L v) := by
  classical
  constructor
  · intro h v y hy
    let x : Fin n → FFAdeleRing Fq k := fun i => FFAdeleRing.single v (y i)
    have hx : x ∈ L.U := by
      intro w
      by_cases hw : w = v
      · subst hw
        have : (fun i => x i w) = y := funext fun i => FFAdeleRing.single_apply_same _ _
        rw [this]; exact hy
      · have : (fun i => x i w) = 0 := funext fun i => FFAdeleRing.single_apply_of_ne hw _
        rw [this]; exact (L.L w).zero_mem
    have h1 := h x hx
    have h2 : a ⬝ᵥ x = FFAdeleRing.single v ((fun i => a i v) ⬝ᵥ y) := by
      have : ∀ i, a i * x i = FFAdeleRing.singleAdd v (a i v * y i) := fun i => by
        show a i * FFAdeleRing.single v (y i) = FFAdeleRing.single v (a i v * y i)
        exact FFAdeleRing.mul_single _ _ _
      simp only [dotProduct, this, ← map_sum]
      rfl
    rw [charVec_apply, h2] at h1
    rw [chiV_apply, dotProduct_comm]
    exact h1
  · intro h x hx
    rw [charVec_apply]
    have hev := Filter.eventually_cofinite.1 L.eventually_eq
    rw [FFAdeleRing.chiA_eq_prod ψ₀ (a ⬝ᵥ x) hev.toFinset ?_]
    · refine Finset.prod_eq_one fun v _ => ?_
      rw [dotProduct_apply_adele, dotProduct_comm]
      exact h v _ (hx v)
    · intro v hv
      have hLv : L.L v = Place.stdLattice v n := by
        by_contra hne
        exact hv ((Set.Finite.mem_toFinset hev).2 hne)
      have h1 := h v
      have h2 := hx v
      rw [hLv] at h2
      rw [hLv, dualLattice_stdLattice ψ₀ hψ₀ v] at h1
      rw [dotProduct_apply_adele]
      simp only [dotProduct]
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [map_mul]
      calc Valued.v (a i v) * Valued.v (x i v) ≤ WithZero.exp (canonical Fq k v) * 1 := by
            refine mul_le_mul' ?_ (Place.mem_stdLattice.1 h2 i)
            simpa using Place.mem_boxLat.1 h1 i
        _ = _ := mul_one _

/-- A character trivial on a subgroup descends to the quotient. -/
theorem exists_addChar_quot {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (ψ : AddChar G Circle)
    (h : ∀ x ∈ H, ψ x = 1) : ∃ ψ' : AddChar (G ⧸ H) Circle, ∀ x : G, ψ' (x : G ⧸ H) = ψ x := by
  have hf : H ≤ (AddChar.toAddMonoidHomEquiv ψ).ker := fun x hx => by
    rw [AddMonoidHom.mem_ker]
    exact congrArg Additive.ofMul (h x hx)
  refine ⟨AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift H _ hf), fun x => rfl⟩

/-- $[E_{\mathbb A}:E+U(L)]=\lvert A(L')\rvert$, and both are finite. -/
theorem natCard_quotient_eq_natCard_A_dual (hψ₀ : ψ₀ ≠ 1) (L : CoherentSystem Fq k n) :
    Finite ((Fin n → FFAdeleRing Fq k) ⧸ principalAddU L) ∧
      Nat.card ((Fin n → FFAdeleRing Fq k) ⧸ principalAddU L) = Nat.card (L.dual ψ₀ hψ₀).A := by
  classical
  obtain ⟨a, ha0, hUa⟩ := exists_box_ge L (Rep.maxDefect Fq k)
  obtain ⟨hfin, -⟩ := count_aux L hUa
    (fun y => FFAdeleRing.exists_sub_diag_mem_U_of_S_eq_top (Rep.S_eq_top ha0) y)
  refine ⟨hfin, ?_⟩
  haveI := hfin
  have hUH : L.U ≤ principalAddU L := le_sup_right
  have hΓH : diagVec Fq k n ≤ principalAddU L := le_sup_left
  have crit : ∀ b : Fin n → FFAdeleRing Fq k, (∀ x ∈ principalAddU L, charVec ψ₀ b x = 1) ↔
      ((∀ i, ∃ η : k, b i = FFAdeleRing.diag η) ∧ ∀ v, (fun i => b i v) ∈ dualLattice ψ₀ v (L.L v)) := by
    intro b
    constructor
    · intro h
      exact ⟨(charVec_trivial_diag_iff ψ₀ hψ₀ b).1 fun x hx => h x (hΓH hx),
        (charVec_trivial_U_iff ψ₀ hψ₀ L b).1 fun x hx => h x (hUH hx)⟩
    · rintro ⟨h1, h2⟩ x hx
      have hx' : x ∈ diagVec Fq k n ⊔ L.U := hx
      obtain ⟨γ, hγ, u, hu, rfl⟩ := AddSubgroup.mem_sup.1 hx'
      rw [AddChar.map_add_eq_mul, (charVec_trivial_diag_iff ψ₀ hψ₀ b).2 h1 γ hγ,
        (charVec_trivial_U_iff ψ₀ hψ₀ L b).2 h2 u hu, one_mul]
  have hAmem : ∀ ξ : Fin n → k, ξ ∈ (L.dual ψ₀ hψ₀).A ↔
      ∀ v, (fun i => (FFAdeleRing.diag (ξ i)) v) ∈ dualLattice ψ₀ v (L.L v) := fun ξ => Iff.rfl
  have htriv : ∀ ξ : (L.dual ψ₀ hψ₀).A, ∀ x ∈ principalAddU L,
      charVec ψ₀ (fun i => FFAdeleRing.diag (ξ.1 i)) x = 1 := fun ξ =>
    (crit _).2 ⟨fun i => ⟨ξ.1 i, rfl⟩, (hAmem ξ.1).1 ξ.2⟩
  choose Φ hΦ using fun ξ : (L.dual ψ₀ hψ₀).A => exists_addChar_quot (principalAddU L) _ (htriv ξ)
  have hinj : Function.Injective Φ := by
    intro ξ ξ' h
    have hx : ∀ x, charVec ψ₀ (fun i => FFAdeleRing.diag (ξ.1 i)) x =
        charVec ψ₀ (fun i => FFAdeleRing.diag (ξ'.1 i)) x := fun x => by
      rw [← hΦ ξ x, ← hΦ ξ' x, h]
    obtain ⟨b, -, huniq⟩ := exists_unique_addChar_vec ψ₀ hψ₀ (charVec ψ₀ (fun i => FFAdeleRing.diag (ξ.1 i)))
      (continuous_charVec ψ₀ _)
    have e1 := huniq (fun i => FFAdeleRing.diag (ξ.1 i)) (fun x => rfl)
    have e2 := huniq (fun i => FFAdeleRing.diag (ξ'.1 i)) (fun x => hx x)
    exact Subtype.ext (funext fun i => FFAdeleRing.diag_injective (congrFun (e1.trans e2.symm) i))
  have hsurj : Function.Surjective Φ := by
    intro ψ'
    let ψ : AddChar (Fin n → FFAdeleRing Fq k) Circle := ψ'.compAddMonoidHom (QuotientAddGroup.mk' (principalAddU L))
    have htr : ∀ x ∈ principalAddU L, ψ x = 1 := fun x hx => by
      show ψ' (x : (Fin n → FFAdeleRing Fq k) ⧸ principalAddU L) = 1
      rw [(QuotientAddGroup.eq_zero_iff x).2 hx, AddChar.map_zero_eq_one]
    have hcont : Continuous ψ :=
      continuous_of_trivial_on_open ψ L.U (isOpen_U_vec L) fun x hx => htr x (hUH hx)
    obtain ⟨b, hb, -⟩ := exists_unique_addChar_vec ψ₀ hψ₀ ψ hcont
    obtain ⟨h1, h2⟩ := (crit b).1 fun x hx => by rw [charVec_apply, ← hb x]; exact htr x hx
    choose η hη using h1
    have hηA : η ∈ (L.dual ψ₀ hψ₀).A := by
      rw [hAmem]
      intro v
      have := h2 v
      have e : (fun i => b i v) = (fun i => (FFAdeleRing.diag (η i)) v) := funext fun i => by rw [hη i]
      rwa [e] at this
    refine ⟨⟨η, hηA⟩, DFunLike.ext _ _ fun q => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [hΦ]
    show FFAdeleRing.chiA ψ₀ ((fun i => FFAdeleRing.diag (η i)) ⬝ᵥ x) = ψ x
    rw [hb x]
    have e : (fun i => FFAdeleRing.diag (η i)) = b := funext fun i => (hη i).symm
    rw [e]
  have hcard : Nat.card (AddChar ((Fin n → FFAdeleRing Fq k) ⧸ principalAddU L) Circle) =
      Nat.card ((Fin n → FFAdeleRing Fq k) ⧸ principalAddU L) := by
    letI : Fintype ((Fin n → FFAdeleRing Fq k) ⧸ principalAddU L) := Fintype.ofFinite _
    have e := Nat.card_congr
      (AddChar.circleEquivComplex (α := (Fin n → FFAdeleRing Fq k) ⧸ principalAddU L)).toEquiv
    rw [e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  rw [← hcard]
  exact (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm

/-- $[E_{\mathbb A}:E+U(L)]=q^{\lambda(L)+\delta(L)+n(g-1)}$. -/
theorem natCard_quotient_eq (hc : IsConstantField Fq k) (L : CoherentSystem Fq k n) :
    Finite ((Fin n → FFAdeleRing Fq k) ⧸ principalAddU L) ∧
      (Nat.card ((Fin n → FFAdeleRing Fq k) ⧸ principalAddU L) : ℚ) =
        (Nat.card Fq : ℚ) ^ ((L.lam : ℤ) + L.delta + n * (Rep.genusInt Fq k - 1)) := by
  obtain ⟨v0⟩ := Place.nonempty (Fq := Fq) (k := k)
  obtain ⟨a, ha0, hUa⟩ := exists_box_ge L
    (Finsupp.single v0 (((2 * Rep.genusInt Fq k - 2).natAbs : ℤ) + 1))
  have hdeg : 2 * Rep.genusInt Fq k - 2 < Divisor.deg a := by
    have h1 := Divisor.deg_nonneg (sub_nonneg.2 ha0)
    rw [_root_.map_sub, Divisor.deg_single] at h1
    have h2 : (1 : ℤ) ≤ v0.degree := by exact_mod_cast v0.degree_pos
    have h3 : 2 * Rep.genusInt Fq k - 2 ≤ ((2 * Rep.genusInt Fq k - 2).natAbs : ℤ) := Int.le_natAbs
    nlinarith
  obtain ⟨hfin, hcount⟩ := count_aux L hUa (FFAdeleRing.weil_VI_2_cor3_adelic hc hdeg)
  refine ⟨hfin, ?_⟩
  haveI := finite_A L hUa
  have hE := natCard_box_quot_vec L hUa
  have hP := natCard_inf_box (n := n) a
  have hA := natCard_A L
  have hell := weil_VI_2_cor2 hc hdeg
  rw [hP, hA] at hcount
  have hcountQ := congrArg (fun m : ℕ => (m : ℚ)) hcount
  simp only [Nat.cast_mul, Nat.cast_pow] at hcountQ
  rw [hE] at hcountQ
  have hq : (Nat.card Fq : ℚ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := Fq)).ne'
  have hne : (Nat.card Fq : ℚ) ^ ((n : ℤ) * (a.ell : ℤ)) ≠ 0 := zpow_ne_zero _ hq
  have hP' : ((Nat.card Fq : ℚ) ^ a.ell) ^ n = (Nat.card Fq : ℚ) ^ ((n : ℤ) * (a.ell : ℤ)) := by
    rw [← pow_mul, ← zpow_natCast]; congr 1; push_cast; ring
  rw [hP'] at hcountQ
  apply mul_left_cancel₀ hne
  rw [← hcountQ, ← zpow_natCast, ← zpow_add₀ hq, ← zpow_add₀ hq]
  congr 1
  rw [hell]
  ring

/-- **Weil, VI, Thm. 1 (Riemann–Roch), $E=k^n$**: if $\mathbb F_q$ is the field of constants and $g$ the genus, then
$\lambda(L)=\lambda(L')-\delta(L)-n(g-1)$ for every coherent system $L$ in $E$. -/
@[kb "weil1973bnt" "Ch. VI, Thm. 1 (p. 99), E = k^n: lambda(L) = lambda(L') - delta(L) - n(g-1)"]
theorem weil_VI_1_thm1_vec (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) (L : CoherentSystem Fq k n) :
    (L.lam : ℤ) = (L.dual ψ₀ hψ₀).lam - L.delta - n * (Rep.genusInt Fq k - 1) := by
  obtain ⟨hf, hq⟩ := natCard_quotient_eq hc L
  obtain ⟨-, h8⟩ := natCard_quotient_eq_natCard_A_dual ψ₀ hψ₀ L
  haveI := hf
  have hpos : 0 < Nat.card ((Fin n → FFAdeleRing Fq k) ⧸ principalAddU L) := Nat.card_pos
  haveI : Finite (L.dual ψ₀ hψ₀).A := Nat.finite_of_card_ne_zero (h8 ▸ hpos.ne')
  have hA := natCard_A (L.dual ψ₀ hψ₀)
  have hcard : (Nat.card Fq : ℚ) ^ ((L.dual ψ₀ hψ₀).lam : ℤ) =
      (Nat.card Fq : ℚ) ^ ((L.lam : ℤ) + L.delta + n * (Rep.genusInt Fq k - 1)) := by
    rw [zpow_natCast, ← hq, h8, hA]
    push_cast
    rfl
  have h2 : (2 : ℚ) ≤ (Nat.card Fq : ℚ) := by exact_mod_cast Finite.one_lt_card (α := Fq)
  have := zpow_right_injective₀ (by linarith : (0 : ℚ) < Nat.card Fq) (by linarith : (Nat.card Fq : ℚ) ≠ 1) hcard
  omega

end NumberFieldKB.WeilBNT.FF
