import NumberFieldKB.WeilBNT.FunctionField.RiemannRoch

/-!
# Weil differentials, the canonical divisor and Riemann–Roch (Weil VI.§2, Thm. 2)

A **Weil differential** is an $\mathbb F_q$-linear form on the repartitions vanishing on $U(\mathfrak a)+k$ for some
divisor $\mathfrak a$ (Weil: a character of $k_{\mathbb A}$ trivial on $k$; the "differential idele" of a nontrivial
character of $k_{\mathbb A}/k$, VII.§2; here in the linear form of Chevalley). $\Omega(\mathfrak a)$
(`Rep.Omega a`) is the annihilator of $S(\mathfrak a)=U(\mathfrak a)+k$, so $\dim\Omega(\mathfrak a)=i(\mathfrak a)$.

* **`Rep.mem_Omega_xω`**: $\xi\omega\in\Omega(\mathfrak a)\iff\omega\in\Omega(\mathfrak a-\operatorname{div}\xi)$.
* **`Rep.exists_divisor`**: a nonzero Weil differential $\omega$ has a divisor $(\omega)$:
  $\omega\in\Omega(\mathfrak a)\iff\mathfrak a\le(\omega)$.
* **`Rep.exists_eq_xω`**: Weil differentials form a $k$-vector space of dimension $1$.
* **`canonical`**: the divisor $\mathfrak c$ of a fixed nonzero Weil differential (a canonical divisor), and
  **`index_eq_ell_canonical_sub`**: $i(\mathfrak a)=\lambda(\mathfrak c-\mathfrak a)$.
* **`weil_VI_2_thm2`** (Riemann–Roch): $\lambda(\mathfrak a)=\deg\mathfrak a+1-g+\lambda(\mathfrak c-\mathfrak a)$.
-/

open scoped Polynomial
open Module

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace Rep

open Divisor

variable (Fq k) in
/-- **$\Omega(\mathfrak a)$**: the linear forms on repartitions vanishing on $U(\mathfrak a)+k$. -/
def Omega (a : Divisor Fq k) : Submodule Fq (Module.Dual Fq (Rep Fq k)) :=
  (S Fq k a).dualAnnihilator

theorem finrank_Omega (a : Divisor Fq k) : finrank Fq (Omega Fq k a) = index Fq k a :=
  finrank_dualAnnihilator _

theorem mem_Omega_iff (a : Divisor Fq k) (ω : Module.Dual Fq (Rep Fq k)) :
    ω ∈ Omega Fq k a ↔ ∀ α ∈ S Fq k a, ω α = 0 :=
  Submodule.mem_dualAnnihilator ω

instance (a : Divisor Fq k) : FiniteDimensional Fq (Omega Fq k a) :=
  Module.Finite.equiv (Submodule.dualQuotEquivDualAnnihilator (S Fq k a))

theorem Omega_antitone {a b : Divisor Fq k} (h : a ≤ b) : Omega Fq k b ≤ Omega Fq k a :=
  Submodule.dualAnnihilator_anti (S_mono h)

/-- Multiplication by $\xi\in k$ on repartitions, as an $\mathbb F_q$-linear map. -/
def mulRep (x : k) : Rep Fq k →ₗ[Fq] Rep Fq k where
  toFun α := x • α
  map_add' := smul_add x
  map_smul' c α := by
    ext v
    show x * (c • α.1 v) = c • (x * α.1 v)
    rw [Algebra.smul_def, Algebra.smul_def]
    ring

@[simp] theorem mulRep_apply (x : k) (α : Rep Fq k) (v : Place Fq k) :
    (mulRep x α).1 v = x * α.1 v := rfl

/-- **The $k$-action on linear forms**: $(\xi\omega)(\alpha)=\omega(\xi\alpha)$. -/
def xω (x : k) (ω : Module.Dual Fq (Rep Fq k)) : Module.Dual Fq (Rep Fq k) := ω ∘ₗ mulRep x

@[simp] theorem xω_apply (x : k) (ω : Module.Dual Fq (Rep Fq k)) (α : Rep Fq k) :
    xω x ω α = ω (mulRep x α) := rfl

theorem xω_mul (x y : k) (ω : Module.Dual Fq (Rep Fq k)) : xω (x * y) ω = xω x (xω y ω) := by
  ext α
  simp only [xω_apply]
  congr 1
  ext v
  simp only [mulRep_apply]
  ring

theorem xω_one (ω : Module.Dual Fq (Rep Fq k)) : xω 1 ω = ω := by
  ext α
  simp only [xω_apply]
  congr 1
  ext v
  simp

theorem xω_zero_left (ω : Module.Dual Fq (Rep Fq k)) : xω 0 ω = 0 := by
  ext α
  simp only [xω_apply, LinearMap.zero_apply]
  have : mulRep (0 : k) α = 0 := by ext v; simp
  rw [this, map_zero]

theorem xω_zero_right (x : k) : xω x (0 : Module.Dual Fq (Rep Fq k)) = 0 := by
  ext α; simp

theorem xω_add_left (x y : k) (ω : Module.Dual Fq (Rep Fq k)) :
    xω (x + y) ω = xω x ω + xω y ω := by
  ext α
  simp only [xω_apply, LinearMap.add_apply]
  rw [← map_add]
  congr 1
  ext v
  simp only [mulRep_apply, Submodule.coe_add, Pi.add_apply]
  ring

theorem xω_smul_left (c : Fq) (x : k) (ω : Module.Dual Fq (Rep Fq k)) :
    xω (c • x) ω = c • xω x ω := by
  ext α
  simp only [xω_apply, LinearMap.smul_apply]
  rw [← map_smul]
  congr 1
  ext v
  simp only [mulRep_apply, Submodule.coe_smul_of_tower, Pi.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def]
  ring

theorem xω_add_right (x : k) (ω₁ ω₂ : Module.Dual Fq (Rep Fq k)) :
    xω x (ω₁ + ω₂) = xω x ω₁ + xω x ω₂ := by
  ext α; simp

theorem xω_neg_right (x : k) (ω : Module.Dual Fq (Rep Fq k)) : xω x (-ω) = -xω x ω := by
  ext α; simp

theorem eq_zero_of_xω_eq_zero {x : k} (hx : x ≠ 0) {ω : Module.Dual Fq (Rep Fq k)}
    (h : xω x ω = 0) : ω = 0 := by
  have : xω (x⁻¹ * x) ω = 0 := by rw [xω_mul, h, xω_zero_right]
  rwa [inv_mul_cancel₀ hx, xω_one] at this

theorem mulRep_diag (x y : k) : mulRep x (diag (Fq := Fq) y) = diag (x * y) := by
  ext v; simp

theorem mulRep_mem_S {a : Divisor Fq k} (f : kˣ) {α : Rep Fq k} (h : α ∈ S Fq k a) :
    mulRep (f : k) α ∈ S Fq k (a - Divisor.div f) := by
  obtain ⟨u, hu, β, hβ, rfl⟩ := Submodule.mem_sup.mp h
  obtain ⟨y, rfl⟩ := hβ
  rw [map_add]
  refine Submodule.add_mem_sup ((smul_mem_U_iff a f u).2 hu) ?_
  rw [mulRep_diag]
  exact ⟨_, rfl⟩

theorem mulRep_mul (x y : k) (α : Rep Fq k) : mulRep x (mulRep y α) = mulRep (x * y) α := by
  ext v; simp only [mulRep_apply]; ring

/-- **$\xi\omega\in\Omega(\mathfrak a)\iff\omega\in\Omega(\mathfrak a-\operatorname{div}\xi)$.** -/
theorem mem_Omega_xω (a : Divisor Fq k) (f : kˣ) (ω : Module.Dual Fq (Rep Fq k)) :
    xω (f : k) ω ∈ Omega Fq k a ↔ ω ∈ Omega Fq k (a - Divisor.div f) := by
  rw [mem_Omega_iff, mem_Omega_iff]
  constructor
  · intro h β hβ
    have h1 := mulRep_mem_S f⁻¹ hβ
    rw [Divisor.div_inv, sub_neg_eq_add, sub_add_cancel] at h1
    have := h _ h1
    rw [xω_apply, mulRep_mul, Units.mul_inv, show mulRep (1 : k) β = β by ext v; simp] at this
    exact this
  · intro h α hα
    exact h _ (mulRep_mem_S f hα)

/-- $U(\sup(\mathfrak a,\mathfrak b))\subset U(\mathfrak a)+U(\mathfrak b)$. -/
theorem U_sup'_le (a b : Divisor Fq k) : U (sup' a b) ≤ U a ⊔ U b := by
  classical
  intro α hα
  let α₁ : Rep Fq k := ⟨fun v => if b v ≤ a v then α.1 v else 0, by
    refine (finite_poles α).subset ?_
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    split_ifs at hv with h
    · exact hv
    · simp at hv⟩
  have h₁ : α₁ ∈ U a := by
    intro v
    show v.valuation (if b v ≤ a v then α.1 v else 0) ≤ _
    split_ifs with h
    · have := hα v
      rwa [sup'_apply, max_eq_left h] at this
    · simp
  have h₂ : α - α₁ ∈ U b := by
    intro v
    show v.valuation (α.1 v - (if b v ≤ a v then α.1 v else 0)) ≤ _
    split_ifs with h
    · simp
    · have := hα v
      rw [sup'_apply, max_eq_right (le_of_lt (not_le.mp h))] at this
      simpa using this
  have : α = α₁ + (α - α₁) := by abel
  rw [this]
  exact Submodule.add_mem_sup h₁ h₂

theorem mem_Omega_sup' {a b : Divisor Fq k} {ω : Module.Dual Fq (Rep Fq k)} (ha : ω ∈ Omega Fq k a)
    (hb : ω ∈ Omega Fq k b) : ω ∈ Omega Fq k (sup' a b) := by
  rw [mem_Omega_iff] at *
  intro α hα
  obtain ⟨u, hu, β, hβ, rfl⟩ := Submodule.mem_sup.mp hα
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp (U_sup'_le a b hu)
  rw [map_add, map_add, ha _ (Submodule.mem_sup_left hu₁), hb _ (Submodule.mem_sup_left hu₂),
    ha _ (Submodule.mem_sup_right hβ)]
  simp

/-- For $\xi\in A(\mathfrak b-\mathfrak a)$ and $\omega\in\Omega(\mathfrak b)$: $\xi\omega\in\Omega(\mathfrak a)$. -/
theorem xω_mem_Omega {a b : Divisor Fq k} {x : k} (hx : x ∈ (b - a).riemannRochSpace)
    {ω : Module.Dual Fq (Rep Fq k)} (hω : ω ∈ Omega Fq k b) : xω x ω ∈ Omega Fq k a := by
  by_cases h0 : x = 0
  · subst h0; rw [xω_zero_left]; exact zero_mem _
  · have h1 := (nonneg_add_div_iff (b - a) (Units.mk0 x h0)).mpr hx
    rw [show x = ((Units.mk0 x h0 : kˣ) : k) from rfl, mem_Omega_xω]
    refine Omega_antitone (fun v => ?_) hω
    have := h1 v
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply,
      Pi.sub_apply] at this
    simp only [Finsupp.coe_sub, Pi.sub_apply]
    omega

/-- The linear map $A(\mathfrak b-\mathfrak a)\to\Omega(\mathfrak a)$, $\xi\mapsto\xi\omega$, for $\omega\in\Omega(\mathfrak b)$. -/
def xωMap {a b : Divisor Fq k} {ω : Module.Dual Fq (Rep Fq k)} (hω : ω ∈ Omega Fq k b) :
    (b - a).riemannRochSpace →ₗ[Fq] Omega Fq k a where
  toFun x := ⟨xω x.1 ω, xω_mem_Omega x.2 hω⟩
  map_add' x y := by ext1; exact xω_add_left _ _ _
  map_smul' c x := by ext1; exact xω_smul_left _ _ _

theorem xωMap_injective {a b : Divisor Fq k} {ω : Module.Dual Fq (Rep Fq k)} (hω : ω ∈ Omega Fq k b)
    (hω0 : ω ≠ 0) : Function.Injective (xωMap (a := a) hω) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  by_contra hx0
  have hx0' : (x : k) ≠ 0 := fun h => hx0 (Subtype.ext h)
  exact hω0 (eq_zero_of_xω_eq_zero hx0' (congrArg Subtype.val hx))

/-- The degrees of the $\mathfrak a$ with $\omega\in\Omega(\mathfrak a)$ are bounded, for $\omega\ne0$. -/
theorem deg_le_of_mem_Omega {a : Divisor Fq k} {ω : Module.Dual Fq (Rep Fq k)} (hω : ω ∈ Omega Fq k a)
    (hω0 : ω ≠ 0) : deg a ≤ index Fq k 0 + genusInt Fq k - 1 := by
  have h1 := LinearMap.finrank_le_finrank_of_injective (xωMap_injective (a := 0) hω hω0)
  rw [finrank_Omega, sub_zero] at h1
  have h2 := ell_sub_index a
  unfold ell at h2
  have h3 : (Module.finrank Fq a.riemannRochSpace : ℤ) ≤ index Fq k 0 := by exact_mod_cast h1
  omega

/-- **The divisor of a nonzero Weil differential**: $\omega\in\Omega(\mathfrak a)\iff\mathfrak a\le(\omega)$. -/
theorem exists_divisor {ω : Module.Dual Fq (Rep Fq k)} (hω0 : ω ≠ 0) (hω : ∃ a, ω ∈ Omega Fq k a) :
    ∃ W : Divisor Fq k, ∀ a, ω ∈ Omega Fq k a ↔ a ≤ W := by
  obtain ⟨a₀, ha₀⟩ := hω
  obtain ⟨m, ⟨W, hW, rfl⟩, hm⟩ := Int.exists_greatest_of_bdd
    (P := fun m => ∃ a : Divisor Fq k, ω ∈ Omega Fq k a ∧ deg a = m)
    ⟨index Fq k 0 + genusInt Fq k - 1, by rintro _ ⟨a, ha, rfl⟩; exact deg_le_of_mem_Omega ha hω0⟩
    ⟨_, a₀, ha₀, rfl⟩
  refine ⟨W, fun a => ⟨fun ha => ?_, fun h => Omega_antitone h hW⟩⟩
  have hc := mem_Omega_sup' ha hW
  have h1 := hm _ ⟨_, hc, rfl⟩
  have h2 := deg_mono (le_sup'_right a W)
  have h3 : sup' a W = W := (eq_of_le_of_deg_eq (le_sup'_right a W) (by omega)).symm
  rw [← h3]
  exact le_sup'_left a W

/-- $\lambda(\mathfrak a)\ge\deg\mathfrak a+1-g$ (Riemann's inequality, from `ell_sub_index`). -/
theorem ell_ge (a : Divisor Fq k) : deg a + 1 - genusInt Fq k ≤ a.ell := by
  have := ell_sub_index a
  omega

/-- $i(\mathfrak a)=\deg(-\mathfrak a)-1+g$ when $\deg\mathfrak a<0$. -/
theorem index_of_deg_neg {a : Divisor Fq k} (ha : deg a < 0) :
    (index Fq k a : ℤ) = -deg a - 1 + genusInt Fq k := by
  have := ell_sub_index a
  rw [ell_eq_zero_of_deg_neg' ha] at this
  omega

/-- A divisor $N\cdot P$ of degree $\ge N$. -/
theorem exists_divisor_deg_ge (N : ℕ) : ∃ B : Divisor Fq k, 0 ≤ B ∧ (N : ℤ) ≤ deg B := by
  obtain ⟨P⟩ := Place.nonempty (Fq := Fq) (k := k)
  refine ⟨Finsupp.single P (N : ℤ), fun v => ?_, ?_⟩
  · by_cases h : v = P
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h]
  · rw [deg_single]
    have := P.degree_pos
    nlinarith

/-- **Weil differentials form a one-dimensional $k$-space**: two nonzero ones differ by a factor in $k$. -/
theorem exists_eq_xω {ω₁ ω₂ : Module.Dual Fq (Rep Fq k)} (h₁ : ω₁ ≠ 0) (h₂ : ω₂ ≠ 0)
    (hω₁ : ∃ a, ω₁ ∈ Omega Fq k a) (hω₂ : ∃ a, ω₂ ∈ Omega Fq k a) : ∃ x : k, ω₁ = xω x ω₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨W₁, hW₁⟩ := exists_divisor h₁ hω₁
  obtain ⟨W₂, hW₂⟩ := exists_divisor h₂ hω₂
  obtain ⟨B, hB0, hBdeg⟩ := exists_divisor_deg_ge (Fq := Fq) (k := k)
    ((3 * genusInt Fq k - deg W₁ - deg W₂ + 3).toNat + 1)
  -- the two maps into Ω(-B)
  have hmem₁ : ω₁ ∈ Omega Fq k W₁ := (hW₁ W₁).2 le_rfl
  have hmem₂ : ω₂ ∈ Omega Fq k W₂ := (hW₂ W₂).2 le_rfl
  have e₁ : W₁ - (-B) = W₁ + B := by abel
  have e₂ : W₂ - (-B) = W₂ + B := by abel
  let φ₁ := xωMap (a := -B) hmem₁
  let φ₂ := xωMap (a := -B) hmem₂
  let Φ := φ₁.coprod φ₂
  have hΦ : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero _).mpr fun ⟨x₁, x₂⟩ hx => ?_
    have hx' : xω (x₁ : k) ω₁ + xω (x₂ : k) ω₂ = 0 := congrArg Subtype.val hx
    by_cases hx1 : (x₁ : k) = 0
    · have hx2 : xω (x₂ : k) ω₂ = 0 := by rw [hx1, xω_zero_left, zero_add] at hx'; exact hx'
      have : (x₂ : k) = 0 := by
        by_contra h
        exact h₂ (eq_zero_of_xω_eq_zero h hx2)
      exact Prod.ext (Subtype.ext hx1) (Subtype.ext this)
    · exfalso
      apply hcon (-((x₁ : k)⁻¹ * x₂))
      have h1 : xω (x₁ : k) ω₁ = -xω (x₂ : k) ω₂ := eq_neg_of_add_eq_zero_left hx'
      have h2 : xω (x₁ : k)⁻¹ (xω (x₁ : k) ω₁) = ω₁ := by
        rw [← xω_mul, inv_mul_cancel₀ hx1, xω_one]
      rw [← h2, h1, xω_neg_right, ← xω_mul]
      have : -((x₁ : k)⁻¹ * x₂) = (-1 : Fq) • ((x₁ : k)⁻¹ * x₂) := (neg_one_smul Fq _).symm
      rw [this, xω_smul_left]
      exact (neg_one_smul Fq _).symm
  have hfin := LinearMap.finrank_le_finrank_of_injective hΦ
  rw [Module.finrank_prod, finrank_Omega] at hfin
  have hl₁ := ell_ge (W₁ + B)
  have hl₂ := ell_ge (W₂ + B)
  have hBpos : 0 < deg B := by omega
  have hi := index_of_deg_neg (a := -B) (by rw [map_neg]; omega)
  rw [map_neg, neg_neg] at hi
  have hf : ((W₁ - -B).ell : ℤ) + (W₂ - -B).ell ≤ index Fq k (-B) := by exact_mod_cast hfin
  rw [e₁, e₂] at hf
  rw [map_add] at hl₁ hl₂
  push_cast at hBdeg
  omega

end Rep

open Rep Divisor in
/-- There is a nonzero Weil differential. -/
theorem exists_weilDifferential : ∃ ω : Module.Dual Fq (Rep Fq k), ω ≠ 0 ∧ ∃ a, ω ∈ Omega Fq k a := by
  obtain ⟨B, hB0, hBdeg⟩ := exists_divisor_deg_ge (Fq := Fq) (k := k) ((-genusInt Fq k).toNat + 2)
  have hi := index_of_deg_neg (a := -B) (by rw [map_neg]; push_cast at hBdeg; omega)
  rw [map_neg, neg_neg] at hi
  have hpos : 0 < finrank Fq (Omega Fq k (-B)) := by
    rw [finrank_Omega]
    push_cast at hBdeg
    omega
  obtain ⟨ω, hω, hω0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Submodule.one_le_finrank_iff.mp hpos)
  exact ⟨ω, hω0, -B, hω⟩

variable (Fq k) in
/-- A fixed nonzero Weil differential. -/
def weilDifferential₀ : Module.Dual Fq (Rep Fq k) := (exists_weilDifferential (Fq := Fq) (k := k)).choose

theorem weilDifferential₀_ne_zero : weilDifferential₀ Fq k ≠ 0 :=
  (exists_weilDifferential (Fq := Fq) (k := k)).choose_spec.1

theorem weilDifferential₀_mem : ∃ a, weilDifferential₀ Fq k ∈ Rep.Omega Fq k a :=
  (exists_weilDifferential (Fq := Fq) (k := k)).choose_spec.2

variable (Fq k) in
/-- **A canonical divisor** $\mathfrak c$: the divisor of the fixed nonzero Weil differential (Weil VI.§2, VII.§2
"divisor of a differential idele"). -/
def canonical : Divisor Fq k :=
  (Rep.exists_divisor weilDifferential₀_ne_zero weilDifferential₀_mem).choose

theorem mem_Omega_canonical_iff (a : Divisor Fq k) :
    weilDifferential₀ Fq k ∈ Rep.Omega Fq k a ↔ a ≤ canonical Fq k :=
  (Rep.exists_divisor weilDifferential₀_ne_zero weilDifferential₀_mem).choose_spec a

open Rep Divisor in
/-- **$i(\mathfrak a)=\lambda(\mathfrak c-\mathfrak a)$** (duality: $\Omega(\mathfrak a)=A(\mathfrak c-\mathfrak a)\,\omega_0$). -/
theorem index_eq_ell_canonical_sub (a : Divisor Fq k) : index Fq k a = (canonical Fq k - a).ell := by
  have hmem : weilDifferential₀ Fq k ∈ Omega Fq k (canonical Fq k) := (mem_Omega_canonical_iff _).2 le_rfl
  let φ := xωMap (a := a) hmem
  have hinj := xωMap_injective (a := a) hmem weilDifferential₀_ne_zero
  have hsurj : Function.Surjective φ := by
    rintro ⟨ω, hω⟩
    by_cases hω0 : ω = 0
    · exact ⟨0, by ext1; simp [φ, xωMap, hω0, xω_zero_left]⟩
    obtain ⟨x, hx⟩ := exists_eq_xω hω0 weilDifferential₀_ne_zero ⟨a, hω⟩ weilDifferential₀_mem
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hω0 (by rw [hx, xω_zero_left])
    have hxL : x ∈ (canonical Fq k - a).riemannRochSpace := by
      refine (nonneg_add_div_iff (canonical Fq k - a) (Units.mk0 x hx0)).mp ?_
      have h1 : weilDifferential₀ Fq k ∈ Omega Fq k (a - Divisor.div (Units.mk0 x hx0)) := by
        rw [← mem_Omega_xω]
        show xω x (weilDifferential₀ Fq k) ∈ _
        rw [← hx]
        exact hω
      have h2 := (mem_Omega_canonical_iff _).1 h1
      intro v
      have := h2 v
      simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add,
        Pi.add_apply] at this ⊢
      omega
    exact ⟨⟨x, hxL⟩, by ext1; exact hx.symm⟩
  rw [← finrank_Omega]
  exact (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq.symm

/-- **Riemann–Roch** (Weil VI.§2, Thm. 2): $\lambda(\mathfrak a)=\deg\mathfrak a+1-g+\lambda(\mathfrak c-\mathfrak a)$,
with $\mathfrak c$ a canonical divisor and $g$ the genus. -/
@[kb "weil1973bnt" "Ch. VI, Thm. 2 (p. 101), Riemann-Roch for divisors, function fields"]
theorem weil_VI_2_thm2 (a : Divisor Fq k) :
    (a.ell : ℤ) = Divisor.deg a + 1 - Rep.genusInt Fq k + (canonical Fq k - a).ell := by
  have h := Rep.ell_sub_index a
  rw [index_eq_ell_canonical_sub] at h
  omega

end NumberFieldKB.WeilBNT.FF
