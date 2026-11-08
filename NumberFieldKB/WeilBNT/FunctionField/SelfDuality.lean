import NumberFieldKB.WeilBNT.FunctionField.AdeleTopology
import NumberFieldKB.WeilBNT.FunctionField.WeilDifferential
import NumberFieldKB.WeilBNT.PFieldDuality

/-!
# Weil, *Basic Number Theory*, IV.§2, Thm. 3 for function fields: the adeles are self-dual

$k$ is a global function field over $\mathbb F_q$, $k_{\mathbb A}$ = `FFAdeleRing Fq k`. A *character* of an additive
topological group is a continuous `AddChar _ Circle`.

**The basic character.** The Weil differential $\omega_0$ (`weilDifferential₀`, an $\mathbb F_q$-linear form on the
repartitions vanishing on $k+U(\mathfrak c)$, $\mathfrak c$ = `canonical Fq k`) is transported to $k_{\mathbb A}$:
every adele is a repartition modulo $U(\mathfrak c)$ (`exists_ofRep_sub_mem_U`), so
$\hat\omega(x)=\omega_0(\alpha)$ for $x-\alpha\in U(\mathfrak c)$ is well defined (`omegaA`). For a non-trivial
character $\psi_0$ of $\mathbb F_q$, $\chi=\psi_0\circ\hat\omega$ (`chiA ψ₀`) is a non-trivial character of
$k_{\mathbb A}$, trivial on $k$ (Weil IV.§2: "a non-trivial character of $k_{\mathbb A}$ trivial on $k$").

* `FFAdeleRing.ofRep`: the repartitions as adeles; `ofRep_mem_U_iff`, `exists_ofRep_sub_mem_U`.
* **`weil_IV_2_thm3_cor1_ff`**: the local components $\chi_v(t)=\chi(t\text{ at }v)$ are non-trivial at every place
  (Weil IV.§2, Cor. 1 of Thm. 3), and **`weil_IV_2_thm3_cor1_ff_order`**: $\chi_v$ is trivial on
  $\mathfrak p_v^{-\mathfrak c(v)}$ and not on $\mathfrak p_v^{-\mathfrak c(v)-1}$ (its order is $\mathfrak c(v)$;
  order $0$ for almost all $v$).
* **`weil_IV_2_thm3_ff_annihilator`**: IV.§2, Thm. 3, last assertion for $E=k$: the annihilator of $k$ under
  $(x,y)\mapsto\chi(xy)$ is $k$.
* **`weil_IV_2_thm3_ff_char`**: IV.§2, Thm. 3, first assertion for $E=k$: every character of $k_{\mathbb A}$ is
  $x\mapsto\chi(ax)$ for one and only one $a\in k_{\mathbb A}$.

*Proof.* $\hat\omega$ kills $U(\mathfrak c)$ and $k$. If $\hat\omega$ vanished on $\mathfrak p_v^{-\mathfrak c(v)-1}$ at
$v$, $\omega_0$ would kill $U(\mathfrak c+v)$, against $\mathfrak c=(\omega_0)$ (`mem_Omega_canonical_iff`). For the
annihilator: if $\chi(x\xi)=1$ for all $\xi\in k$, then $\hat\omega(x\xi)=0$ (scale $\xi$ by $\mathbb F_q$), so
$\alpha\mapsto\hat\omega(x\,\alpha)$ is a Weil differential, equal to $\xi_0\omega_0$ for some $\xi_0\in k$
(`exists_eq_xω`); then $(x-\xi_0)\hat\omega=0$ on $k_{\mathbb A}$, and since every local component of $\hat\omega$ is
non-zero, $x=\xi_0$. For the characters: locally by $p$-field duality (`weil_II_5_cor_thm3_right`), globally as in the
number-field case (`NumberFieldKB.WeilBNT.weil_IV_2_thm3_char`): a character is trivial on some $U(\mathfrak b)$, so its
local coefficients $a_v$ are integral for almost all $v$, and two characters agreeing on the adeles with finitely many
non-zero components (a dense set) are equal.
-/

open scoped WithZero RestrictedProduct
open Topology

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace FFAdeleRing

/-! ### Repartitions as adeles -/

/-- A repartition $(\alpha_v)$, $\alpha_v\in k$ integral for almost all $v$, as an adele. -/
def ofRep : Rep Fq k →+ FFAdeleRing Fq k where
  toFun α := ⟨fun v => v.toCompletion (α.1 v), by
    refine Filter.eventually_cofinite.2 ((Rep.finite_poles α).subset ?_)
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    by_contra h
    exact hv (by
      show Valued.v (v.toCompletion (α.1 v)) ≤ 1
      rw [Place.valued_toCompletion]
      exact not_lt.mp h)⟩
  map_zero' := by
    ext v
    simp
  map_add' α β := by
    ext v
    exact map_add v.toCompletion _ _

theorem ofRep_apply (α : Rep Fq k) (v : Place Fq k) : ofRep α v = v.toCompletion (α.1 v) := rfl

theorem ofRep_mem_U_iff (a : Divisor Fq k) (α : Rep Fq k) : ofRep α ∈ U a ↔ α ∈ Rep.U a := by
  rw [mem_U_iff, Rep.mem_U_iff]
  refine forall_congr' fun v => ?_
  rw [ofRep_apply, Place.valued_toCompletion]

theorem ofRep_diag (ξ : k) : ofRep (Rep.diag (Fq := Fq) ξ) = diag ξ := by
  ext v
  rfl

/-- $k$ is dense in $k_v$: every $y\in k_v$ is within $e^n$ of an element of $k$. -/
theorem exists_approx (v : Place Fq k) (y : v.Completion) (n : ℤ) :
    ∃ b : k, Valued.v (y - v.toCompletion b) ≤ WithZero.exp n := by
  have hnhds : {z : v.Completion | Valued.v (z - y) ≤ WithZero.exp n} ∈ nhds y :=
    (((Place.isOpen_valued_le v n).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simp))
  obtain ⟨a, ha⟩ := (UniformSpace.Completion.denseRange_coe (α := WithVal v.valuation)).mem_nhds hnhds
  refine ⟨WithVal.equiv v.valuation a, ?_⟩
  rw [Valuation.map_sub_swap]
  exact ha

/-- Every adele is a repartition modulo $U(\mathfrak a)$ ($k$ is dense in each $k_v$). -/
theorem exists_ofRep_sub_mem_U (a : Divisor Fq k) (x : FFAdeleRing Fq k) :
    ∃ α : Rep Fq k, x - ofRep α ∈ U a := by
  classical
  choose β hβ using fun v : Place Fq k => exists_approx v (x v) (a v)
  have hfin : {v : Place Fq k | ¬ x v ∈ (v.completionIntegers : Set v.Completion)}.Finite :=
    Filter.eventually_cofinite.1 x.2
  set T : Set (Place Fq k) := {v | ¬ x v ∈ (v.completionIntegers : Set v.Completion)} ∪ (a.support : Set (Place Fq k))
    with hT
  have hTfin : T.Finite := hfin.union (Finset.finite_toSet _)
  let α : Rep Fq k := ⟨fun v => if v ∈ T then β v else 0, by
    refine hTfin.subset ?_
    intro v hv
    by_contra hvT
    have : v.valuation (if v ∈ T then β v else 0) = 0 := by rw [if_neg hvT, map_zero]
    have hv' : 1 < v.valuation (if v ∈ T then β v else 0) := hv
    rw [this] at hv'
    exact absurd hv' (not_lt.mpr zero_le')⟩
  refine ⟨α, fun v => ?_⟩
  show Valued.v (x v - v.toCompletion (if v ∈ T then β v else 0)) ≤ _
  by_cases hv : v ∈ T
  · rw [if_pos hv]; exact hβ v
  · rw [if_neg hv, map_zero, sub_zero]
    have h1 : x v ∈ (v.completionIntegers : Set v.Completion) := by
      by_contra h; exact hv (Or.inl h)
    have h2 : a v = 0 := by
      by_contra h; exact hv (Or.inr (by simpa using h))
    rw [h2, WithZero.exp_zero]
    exact h1

/-! ### The Weil differential on the adeles -/

/-- Two repartitions approximating the same adele modulo $U(\mathfrak c)$ have the same $\omega_0$-value. -/
theorem weil₀_eq_of_sub_mem_U {x : FFAdeleRing Fq k} {α β : Rep Fq k}
    (hα : x - ofRep α ∈ U (canonical Fq k)) (hβ : x - ofRep β ∈ U (canonical Fq k)) :
    weilDifferential₀ Fq k α = weilDifferential₀ Fq k β := by
  have h : ofRep (α - β) ∈ U (canonical Fq k) := by
    have := (U (canonical Fq k)).sub_mem hβ hα
    rwa [show x - ofRep β - (x - ofRep α) = ofRep (α - β) by rw [map_sub]; abel] at this
  have h2 : α - β ∈ Rep.S Fq k (canonical Fq k) := Submodule.mem_sup_left ((ofRep_mem_U_iff _ _).1 h)
  have h3 := (Rep.mem_Omega_iff _ _).1 ((mem_Omega_canonical_iff _).2 le_rfl) _ h2
  rwa [map_sub, sub_eq_zero] at h3

/-- $\omega_0$ kills $U(\mathfrak c)$ and the principal repartitions. -/
theorem weil₀_eq_zero_of_mem_S {α : Rep Fq k} (h : α ∈ Rep.S Fq k (canonical Fq k)) :
    weilDifferential₀ Fq k α = 0 :=
  (Rep.mem_Omega_iff _ _).1 ((mem_Omega_canonical_iff _).2 le_rfl) _ h

/-- $\hat\omega(x)=\omega_0(\alpha)$ for any repartition $\alpha$ with $x-\alpha\in U(\mathfrak c)$. -/
def omegaA : FFAdeleRing Fq k →+ Fq where
  toFun x := weilDifferential₀ Fq k (exists_ofRep_sub_mem_U (canonical Fq k) x).choose
  map_zero' := by
    have h := weil₀_eq_of_sub_mem_U (x := (0 : FFAdeleRing Fq k)) (β := 0)
      (exists_ofRep_sub_mem_U (canonical Fq k) 0).choose_spec (by simp)
    rw [h, map_zero]
  map_add' x y := by
    have hx := (exists_ofRep_sub_mem_U (canonical Fq k) x).choose_spec
    have hy := (exists_ofRep_sub_mem_U (canonical Fq k) y).choose_spec
    have hxy := (exists_ofRep_sub_mem_U (canonical Fq k) (x + y)).choose_spec
    generalize (exists_ofRep_sub_mem_U (canonical Fq k) x).choose = α at hx ⊢
    generalize (exists_ofRep_sub_mem_U (canonical Fq k) y).choose = β at hy ⊢
    generalize (exists_ofRep_sub_mem_U (canonical Fq k) (x + y)).choose = γ at hxy ⊢
    have h := weil₀_eq_of_sub_mem_U (x := x + y) (α := γ) (β := α + β) hxy (by
      have := (U (canonical Fq k)).add_mem hx hy
      rwa [show x - ofRep α + (y - ofRep β) = x + y - ofRep (α + β) by rw [map_add]; abel] at this)
    show weilDifferential₀ Fq k γ = weilDifferential₀ Fq k α + weilDifferential₀ Fq k β
    rw [h, map_add]

theorem omegaA_eq (x : FFAdeleRing Fq k) (α : Rep Fq k) (h : x - ofRep α ∈ U (canonical Fq k)) :
    omegaA x = weilDifferential₀ Fq k α :=
  weil₀_eq_of_sub_mem_U (exists_ofRep_sub_mem_U (canonical Fq k) x).choose_spec h

theorem omegaA_ofRep (α : Rep Fq k) : omegaA (ofRep α) = weilDifferential₀ Fq k α :=
  omegaA_eq _ α (by simp)

theorem omegaA_eq_zero_of_mem_U {x : FFAdeleRing Fq k} (hx : x ∈ U (canonical Fq k)) : omegaA x = 0 := by
  rw [omegaA_eq x 0 (by simpa using hx), map_zero]

theorem omegaA_diag (ξ : k) : omegaA (diag (Fq := Fq) ξ) = 0 := by
  rw [← ofRep_diag, omegaA_ofRep]
  exact weil₀_eq_zero_of_mem_S (Submodule.mem_sup_right ⟨ξ, rfl⟩)

/-- Multiplying by an integral principal adele preserves $U(\mathfrak a)$. -/
theorem diag_mul_mem_U {ξ : k} (hξ : ∀ v : Place Fq k, v.valuation ξ ≤ 1) {a : Divisor Fq k}
    {y : FFAdeleRing Fq k} (hy : y ∈ U a) : diag ξ * y ∈ U a := fun v => by
  show Valued.v (v.toCompletion ξ * y v) ≤ _
  rw [map_mul, Place.valued_toCompletion]
  exact (mul_le_of_le_one_left' (hξ v)).trans (hy v)

/-- `ofRep` is compatible with the $\mathbb F_q$-action. -/
theorem ofRep_smul (c : Fq) (α : Rep Fq k) :
    ofRep (c • α) = diag (algebraMap Fq k c) * ofRep α := by
  ext v
  show v.toCompletion (c • α.1 v) = v.toCompletion (algebraMap Fq k c) * v.toCompletion (α.1 v)
  rw [Algebra.smul_def, map_mul]

/-- The diagonal embedding is multiplicative. -/
theorem diag_mul_diag (a b : k) : diag (Fq := Fq) a * diag b = diag (a * b) := by
  ext v
  exact (map_mul v.toCompletion a b).symm

/-- Multiplication by an adele is continuous at $0$: $zU(\mathfrak b)\subset U(\mathfrak c)$ for some $\mathfrak b$. -/
theorem exists_U_mul_subset (z : FFAdeleRing Fq k) (c : Divisor Fq k) :
    ∃ b : Divisor Fq k, ∀ y ∈ U b, z * y ∈ U c := by
  have hW : {y : FFAdeleRing Fq k | z * y ∈ (U c : Set (FFAdeleRing Fq k))} ∈ 𝓝 (0 : FFAdeleRing Fq k) :=
    ((isOpen_U c).preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  obtain ⟨b, hb⟩ := exists_U_subset_of_mem_nhds_zero hW
  exact ⟨b, fun y hy => hb hy⟩

/-- $\hat\omega$ is $\mathbb F_q$-linear: $\hat\omega(cx)=c\,\hat\omega(x)$ for constants $c$. -/
theorem omegaA_const_mul (c : Fq) (x : FFAdeleRing Fq k) :
    omegaA (diag (algebraMap Fq k c) * x) = c * omegaA x := by
  obtain ⟨α, hα⟩ := exists_ofRep_sub_mem_U (canonical Fq k) x
  rw [omegaA_eq x α hα]
  have h : ofRep (c • α) = diag (algebraMap Fq k c) * ofRep α := by
    ext v
    show v.toCompletion (c • α.1 v) = v.toCompletion (algebraMap Fq k c) * v.toCompletion (α.1 v)
    rw [Algebra.smul_def, map_mul]
  rw [omegaA_eq _ (c • α) (by
    rw [h, ← mul_sub]
    exact diag_mul_mem_U (fun v => (Place.mem_integers_iff v).1 (v.algebraMap_mem_integers c)) hα),
    map_smul, smul_eq_mul]

/-- **The order of the local components of $\hat\omega$**: $\hat\omega$ vanishes on
$\mathfrak p_v^{-\mathfrak c(v)}$ at $v$ and not on $\mathfrak p_v^{-\mathfrak c(v)-1}$. -/
theorem omegaA_single_order (v : Place Fq k) :
    (∀ t : v.Completion, Valued.v t ≤ WithZero.exp (canonical Fq k v) → omegaA (single v t) = 0) ∧
      ∃ t : v.Completion, Valued.v t ≤ WithZero.exp (canonical Fq k v + 1) ∧ omegaA (single v t) ≠ 0 := by
  refine ⟨fun t ht => omegaA_eq_zero_of_mem_U ((single_mem_U_iff _ v t).2 ht), ?_⟩
  by_contra hcon
  push Not at hcon
  have hmem : weilDifferential₀ Fq k ∈ Rep.Omega Fq k (canonical Fq k + Finsupp.single v 1) := by
    rw [Rep.mem_Omega_iff]
    intro α hα
    obtain ⟨u, hu, β, hβ, rfl⟩ := Submodule.mem_sup.mp hα
    rw [map_add, weil₀_eq_zero_of_mem_S (Submodule.mem_sup_right hβ), add_zero]
    rw [← omegaA_ofRep]
    have hdec : ofRep u = single v (v.toCompletion (u.1 v)) + (ofRep u - single v (v.toCompletion (u.1 v))) := by
      abel
    have hU : ofRep u - single v (v.toCompletion (u.1 v)) ∈ U (canonical Fq k) := by
      intro w
      rcases eq_or_ne w v with rfl | hw
      · show Valued.v (ofRep u w - single w (w.toCompletion (u.1 w)) w) ≤ _
        rw [ofRep_apply, single_apply_same, sub_self, map_zero]
        exact zero_le
      · show Valued.v (ofRep u w - single v (v.toCompletion (u.1 v)) w) ≤ _
        rw [single_apply_of_ne hw, sub_zero, ofRep_apply, Place.valued_toCompletion]
        have h2 : (canonical Fq k + Finsupp.single v (1 : ℤ) : Divisor Fq k) w = canonical Fq k w := by
          simp [Finsupp.single_apply, Ne.symm hw]
        have := hu w
        rwa [h2] at this
    rw [hdec, map_add, omegaA_eq_zero_of_mem_U hU, add_zero]
    apply hcon
    rw [Place.valued_toCompletion]
    have := hu v
    simpa using this
  have := (mem_Omega_canonical_iff _).1 hmem v
  simp at this

/-- If $y\hat\omega=0$ on $k_{\mathbb A}$ then $y=0$. -/
theorem eq_zero_of_omegaA_mul {y : FFAdeleRing Fq k} (h : ∀ x, omegaA (y * x) = 0) : y = 0 := by
  by_contra hy
  have : ∃ v, y v ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hy (by ext v; exact hall v)
  obtain ⟨v, hv⟩ := this
  obtain ⟨t0, -, ht0⟩ := (omegaA_single_order v).2
  apply ht0
  have := h (single v ((y v)⁻¹ * t0))
  rwa [mul_single, ← mul_assoc, mul_inv_cancel₀ hv, one_mul] at this

/-- Every value $s\in\mathbb F_q$ is $\hat\omega(\text{single}_v\,t)$ for some $t$ with $v(t)\le e^{\mathfrak c(v)+1}$. -/
theorem exists_single_omegaA_eq (v : Place Fq k) (s : Fq) :
    ∃ t : v.Completion, Valued.v t ≤ WithZero.exp (canonical Fq k v + 1) ∧ omegaA (single v t) = s := by
  obtain ⟨t0, ht0, hne⟩ := (omegaA_single_order v).2
  set c : Fq := s * (omegaA (single v t0))⁻¹ with hc
  refine ⟨v.toCompletion (algebraMap Fq k c) * t0, ?_, ?_⟩
  · rw [map_mul, Place.valued_toCompletion]
    exact (mul_le_of_le_one_left' ((Place.mem_integers_iff v).1 (v.algebraMap_mem_integers c))).trans ht0
  · have : single v (v.toCompletion (algebraMap Fq k c) * t0) = diag (algebraMap Fq k c) * single v t0 := by
      rw [mul_single]; rfl
    rw [this, omegaA_const_mul, hc, mul_assoc, inv_mul_cancel₀ hne, mul_one]

/-! ### The basic character -/

variable (ψ₀ : AddChar Fq Circle)

/-- **The basic character** $\chi=\psi_0\circ\hat\omega$ of $k_{\mathbb A}$, trivial on $k$. -/
def chiA : AddChar (FFAdeleRing Fq k) Circle := ψ₀.compAddMonoidHom omegaA

theorem chiA_apply (x : FFAdeleRing Fq k) : chiA ψ₀ x = ψ₀ (omegaA x) := rfl

theorem continuous_chiA : Continuous (chiA (Fq := Fq) (k := k) ψ₀) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hn : {y : FFAdeleRing Fq k | y - x ∈ (U (canonical Fq k) : Set (FFAdeleRing Fq k))} ∈ 𝓝 x :=
    ((isOpen_U (canonical Fq k)).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  refine (continuousAt_const (y := chiA ψ₀ x)).congr (Filter.eventually_of_mem hn fun y hy => ?_)
  show chiA ψ₀ x = chiA ψ₀ y
  have : omegaA y = omegaA x := by
    have h := omegaA_eq_zero_of_mem_U (SetLike.mem_coe.1 hy)
    rw [map_sub, sub_eq_zero] at h
    exact h
  rw [chiA_apply, chiA_apply, this]

/-- $\chi$ is trivial on $k$. -/
theorem chiA_diag (ξ : k) : chiA ψ₀ (diag (Fq := Fq) ξ) = 1 := by
  rw [chiA_apply, omegaA_diag, AddChar.map_zero_eq_one]

/-- If $\psi_0\neq1$ and $\chi(cx)=1$ for all constants $c$, then $\hat\omega(x)=0$. -/
theorem omegaA_eq_zero_of_chiA (hψ₀ : ψ₀ ≠ 1) {x : FFAdeleRing Fq k}
    (h : ∀ c : Fq, chiA ψ₀ (diag (algebraMap Fq k c) * x) = 1) : omegaA x = 0 := by
  by_contra ht
  apply hψ₀
  refine DFunLike.ext _ _ fun s => ?_
  have := h (s * (omegaA x)⁻¹)
  rw [chiA_apply, omegaA_const_mul, mul_assoc, inv_mul_cancel₀ ht, mul_one] at this
  simpa using this

/-- **Weil, IV.§2, Cor. 1 of Thm. 3, function fields**: the local components $\chi_v$ of $\chi$ are non-trivial
characters of $k_v$, at every place $v$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Cor. 1 of Thm. 3 (p. 67), the local components χ_v are non-trivial, function fields"]
theorem weil_IV_2_thm3_cor1_ff (hψ₀ : ψ₀ ≠ 1) (v : Place Fq k) :
    Continuous (fun t : v.Completion => chiA ψ₀ (single v t)) ∧ ∃ t : v.Completion, chiA ψ₀ (single v t) ≠ 1 := by
  refine ⟨(continuous_chiA ψ₀).comp (continuous_single v), ?_⟩
  obtain ⟨s, hs⟩ := AddChar.ne_one_iff.1 hψ₀
  obtain ⟨t, -, ht⟩ := exists_single_omegaA_eq v s
  exact ⟨t, by rw [chiA_apply, ht]; exact hs⟩

/-- **Weil, IV.§2, Cor. 1 of Thm. 3, function fields**: $\chi_v$ is trivial on $\mathfrak p_v^{-\mathfrak c(v)}$ and
not on $\mathfrak p_v^{-\mathfrak c(v)-1}$; in particular it has order $0$ for all $v$ outside the support of
$\mathfrak c$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Cor. 1 of Thm. 3 (p. 67), the order of χ_v is c(v), function fields"]
theorem weil_IV_2_thm3_cor1_ff_order (hψ₀ : ψ₀ ≠ 1) (v : Place Fq k) :
    (∀ t : v.Completion, Valued.v t ≤ WithZero.exp (canonical Fq k v) → chiA ψ₀ (single v t) = 1) ∧
      ∃ t : v.Completion, Valued.v t ≤ WithZero.exp (canonical Fq k v + 1) ∧ chiA ψ₀ (single v t) ≠ 1 := by
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [chiA_apply, (omegaA_single_order v).1 t ht, AddChar.map_zero_eq_one]
  · obtain ⟨s, hs⟩ := AddChar.ne_one_iff.1 hψ₀
    obtain ⟨t, ht, hts⟩ := exists_single_omegaA_eq v s
    exact ⟨t, ht, by rw [chiA_apply, hts]; exact hs⟩

/-- **Weil, IV.§2, Thm. 3, last assertion, $E=k$ a function field**: the annihilator of $k$ in $k_{\mathbb A}$ under
the pairing $(x,y)\mapsto\chi(xy)$ is $k$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Thm. 3 (p. 66), last assertion, E = k, function fields: k is its own annihilator"]
theorem weil_IV_2_thm3_ff_annihilator (hψ₀ : ψ₀ ≠ 1) (x : FFAdeleRing Fq k) :
    (∀ ξ : k, chiA ψ₀ (x * diag ξ) = 1) ↔ ∃ ξ : k, x = diag ξ := by
  constructor
  · intro h
    have h0 : ∀ ξ : k, omegaA (x * diag ξ) = 0 := fun ξ => by
      refine omegaA_eq_zero_of_chiA ψ₀ hψ₀ fun c => ?_
      rw [mul_left_comm, diag_mul_diag]
      exact h _
    obtain ⟨b, hb⟩ := exists_U_mul_subset x (canonical Fq k)
    let η : Module.Dual Fq (Rep Fq k) :=
      { toFun := fun α => omegaA (x * ofRep α)
        map_add' := fun α β => by rw [map_add, mul_add, map_add]
        map_smul' := fun c α => by
          rw [ofRep_smul, mul_left_comm, omegaA_const_mul]
          rfl }
    have hη : η ∈ Rep.Omega Fq k b := by
      rw [Rep.mem_Omega_iff]
      intro α hα
      obtain ⟨u, hu, β, ⟨ξ, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hα
      show omegaA (x * ofRep (u + Rep.diag ξ)) = 0
      rw [map_add, mul_add, map_add, omegaA_eq_zero_of_mem_U (hb _ ((ofRep_mem_U_iff _ _).2 hu)),
        ofRep_diag, h0, add_zero]
    obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀ : k, η = Rep.xω ξ₀ (weilDifferential₀ Fq k) := by
      by_cases hz : η = 0
      · exact ⟨0, by rw [hz, Rep.xω_zero_left]⟩
      · exact Rep.exists_eq_xω hz weilDifferential₀_ne_zero ⟨b, hη⟩ weilDifferential₀_mem
    refine ⟨ξ₀, ?_⟩
    rw [← sub_eq_zero]
    refine eq_zero_of_omegaA_mul fun w => ?_
    obtain ⟨b', hb'⟩ := exists_U_mul_subset (x - diag ξ₀) (canonical Fq k)
    obtain ⟨α, hα⟩ := exists_ofRep_sub_mem_U b' w
    have h1 : omegaA ((x - diag ξ₀) * ofRep α) = 0 := by
      rw [sub_mul, map_sub, sub_eq_zero]
      have e1 : omegaA (x * ofRep α) = η α := rfl
      have e2 : diag ξ₀ * ofRep α = ofRep (Rep.mulRep ξ₀ α) := by
        ext v
        show v.toCompletion ξ₀ * v.toCompletion (α.1 v) = v.toCompletion (ξ₀ * α.1 v)
        rw [map_mul]
      rw [e1, e2, omegaA_ofRep, hξ₀]
      rfl
    have h2 := omegaA_eq_zero_of_mem_U (hb' _ hα)
    have : (x - diag ξ₀) * w = (x - diag ξ₀) * ofRep α + (x - diag ξ₀) * (w - ofRep α) := by ring
    rw [this, map_add, h1, h2, add_zero]
  · rintro ⟨ξ, rfl⟩ η
    rw [diag_mul_diag, chiA_diag]

/-- The additive map $k_v\to k_{\mathbb A}$, $t\mapsto\text{single}_v\,t$. -/
def singleHom (v : Place Fq k) : v.Completion →+ FFAdeleRing Fq k :=
  AddMonoidHom.mk' (single v) (single_add v)

/-- If $\chi_v(ta)=1$ for all integral $t$ and $\mathfrak c(v)=0$, then $a$ is integral. -/
theorem valued_le_one_of_chiA (hψ₀ : ψ₀ ≠ 1) (v : Place Fq k) (hc : canonical Fq k v = 0)
    (a : v.Completion) (h : ∀ t : v.Completion, Valued.v t ≤ 1 → chiA ψ₀ (single v (t * a)) = 1) :
    Valued.v a ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨-, t', ht', hne⟩ := weil_IV_2_thm3_cor1_ff_order ψ₀ hψ₀ v
  rw [hc] at ht'
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hlt
    exact absurd hlt (not_lt.mpr zero_le)
  have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
  have hexp : WithZero.exp (0 + 1 : ℤ) ≤ Valued.v a := by
    rw [← WithZero.exp_log hva] at hlt ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    rw [WithZero.exp_le_exp]
    omega
  have hle : Valued.v (t' * a⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀, ← div_eq_mul_inv, div_le_one₀ (zero_lt_iff.2 hva)]
    exact ht'.trans hexp
  apply hne
  have := h _ hle
  rwa [inv_mul_cancel_right₀ ha0] at this

/-- **Weil, IV.§2, Thm. 3, first assertion, $E=k$ a function field**: every character of $k_{\mathbb A}$ is
$x\mapsto\chi(ax)$ for one and only one $a\in k_{\mathbb A}$. -/
@[kb "weil1973bnt" "Ch. IV, §2, Thm. 3 (p. 66), first assertion, E = k, function fields: every character is χ(a·)"]
theorem weil_IV_2_thm3_ff_char (hψ₀ : ψ₀ ≠ 1) (ψ : AddChar (FFAdeleRing Fq k) Circle) (hψ : Continuous ψ) :
    ∃! a : FFAdeleRing Fq k, ∀ x, ψ x = chiA ψ₀ (a * x) := by
  classical
  -- local coefficients
  have hloc : ∀ v : Place Fq k, ∃ a : v.Completion, ∀ t : v.Completion,
      ψ (single v t) = chiA ψ₀ (single v (t * a)) := fun v => by
    have hχ := weil_IV_2_thm3_cor1_ff ψ₀ hψ₀ v
    obtain ⟨a, ha, -⟩ := FieldModule.weil_II_5_cor_thm3_right (weil_ff_completion_isPField v).1
      (χ := (chiA ψ₀).compAddMonoidHom (singleHom v)) hχ.1
      (fun h => hχ.2.elim fun t ht => ht (DFunLike.congr_fun h t))
      (ψ := ψ.compAddMonoidHom (singleHom v)) (hψ.comp (continuous_single v))
    exact ⟨a, ha⟩
  choose a₀ ha₀ using hloc
  obtain ⟨b, hb⟩ := exists_U_trivial ψ hψ
  have hint : ∀ᶠ v in Filter.cofinite, a₀ v ∈ (v.completionIntegers : Set v.Completion) := by
    refine Filter.eventually_cofinite.2
      (((Finset.finite_toSet b.support).union (Finset.finite_toSet (canonical Fq k).support)).subset ?_)
    intro v hv
    by_contra hnot
    simp only [Set.mem_union, Finset.mem_coe, not_or, Finsupp.mem_support_iff, not_not] at hnot
    apply hv
    refine valued_le_one_of_chiA ψ₀ hψ₀ v hnot.2 (a₀ v) fun t ht => ?_
    rw [← ha₀]
    refine hb _ ((single_mem_U_iff b v t).2 ?_)
    rw [hnot.1, WithZero.exp_zero]
    exact ht
  let α : FFAdeleRing Fq k := ⟨a₀, hint⟩
  have main : ∀ x, ψ x = chiA ψ₀ (α * x) := by
    let E : Set (FFAdeleRing Fq k) := {x | ψ x = chiA ψ₀ (α * x)}
    have hEc : IsClosed E :=
      isClosed_eq hψ ((continuous_chiA ψ₀).comp (continuous_const.mul continuous_id))
    have hEadd : ∀ x y, x ∈ E → y ∈ E → x + y ∈ E := by
      intro x y hx hy
      show ψ (x + y) = chiA ψ₀ (α * (x + y))
      rw [AddChar.map_add_eq_mul, mul_add, AddChar.map_add_eq_mul]
      exact congr (congrArg _ hx) hy
    have hE0 : (0 : FFAdeleRing Fq k) ∈ E := by
      show ψ 0 = chiA ψ₀ (α * 0)
      rw [mul_zero, AddChar.map_zero_eq_one, AddChar.map_zero_eq_one]
    have hEs : ∀ (v : Place Fq k) (t : v.Completion), single v t ∈ E := by
      intro v t
      show ψ (single v t) = chiA ψ₀ (α * single v t)
      rw [ha₀, mul_single]
      exact congrArg _ (congrArg _ (mul_comm _ _))
    have hEsupp : ∀ (T : Finset (Place Fq k)) (x : FFAdeleRing Fq k), (∀ u ∉ T, x u = 0) → x ∈ E := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        intro x hx
        have : x = 0 := by ext v; exact hx v (Finset.notMem_empty v)
        subst this
        exact hE0
      | insert u T hu ih =>
        intro x hx
        have h1 := ih (x - single u (x u)) (fun w hw => by
          show x w - single u (x u) w = 0
          by_cases hwu : w = u
          · subst hwu
            rw [single_apply_same, sub_self]
          · rw [single_apply_of_ne hwu, sub_zero]
            exact hx w (by simp [hwu, hw]))
        have e : x = (x - single u (x u)) + single u (x u) := by abel
        rw [e]
        exact hEadd _ _ h1 (hEs u _)
    have hD : {x : FFAdeleRing Fq k | Set.Finite {v : Place Fq k | x v ≠ 0}} ⊆ E := by
      intro x hx
      refine hEsupp hx.toFinset x fun u hu => ?_
      by_contra h
      exact hu ((Set.Finite.mem_toFinset hx).2 h)
    have hdense : Dense E := dense_finiteSupport.mono hD
    intro x
    have : E = Set.univ := by rw [← hEc.closure_eq, hdense.closure_eq]
    have hx : x ∈ E := by rw [this]; exact Set.mem_univ x
    exact hx
  refine ⟨α, main, fun α' hα' => ?_⟩
  have hz : α' - α = 0 := by
    refine eq_zero_of_omegaA_mul fun x => ?_
    refine omegaA_eq_zero_of_chiA ψ₀ hψ₀ fun c => ?_
    have h1 := main (diag (algebraMap Fq k c) * x)
    have h2 := hα' (diag (algebraMap Fq k c) * x)
    rw [h1] at h2
    rw [mul_left_comm, sub_mul, AddChar.map_sub_eq_div, ← h2, div_self']
  exact sub_eq_zero.mp hz

/-- A non-trivial character of $\mathbb F_q$ exists, so the basic character exists. -/
theorem exists_addChar_ne_one : ∃ ψ₀ : AddChar Fq Circle, ψ₀ ≠ 1 := by
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := Fq) (a := 1)).2 one_ne_zero
  refine ⟨AddChar.circleEquivComplex.symm ψ, fun h => hψ ?_⟩
  have h2 := congrArg (fun χ : AddChar Fq Circle => ((χ 1 : Circle) : ℂ)) h
  have h3 : ((AddChar.circleEquivComplex.symm ψ) 1 : ℂ) = ψ 1 := rfl
  simp only [h3] at h2
  simpa using h2

end FFAdeleRing

end NumberFieldKB.WeilBNT.FF
