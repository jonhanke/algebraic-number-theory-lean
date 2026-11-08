import NumberFieldKB.WeilBNT.FunctionField.SelfDuality

/-!
# Fourier transform and Poisson summation on the adeles of a function field (Weil VII.§2, characteristic $p$)

$k$ is a global function field over $\mathbb F_q$, $k_{\mathbb A}$ = `FFAdeleRing Fq k` with the Haar measure $\mu_1$
(`FFAdeleRing.haar`, $\mu_1(\prod_v\mathfrak r_v)=1$), $\chi$ the basic character (`chiA ψ₀`, `SelfDuality.lean`) and
$\mathfrak c$ the canonical divisor, the divisor of the Weil differential underlying $\chi$.

* `IsSchwartzBruhat Φ`: $\Phi$ is a Schwartz–Bruhat function on $k_{\mathbb A}$ (Weil VII.§1 "standard" functions in
  characteristic $p$; Bruhat): supported in some $U(\mathfrak a)$ and invariant under some $U(\mathfrak b)$.
* `fourierFF ψ₀ Φ`: $\hat\Phi(y)=\int_{k_{\mathbb A}}\Phi(x)\chi(xy)\,d\mu_1(x)$.
* `fourierFF_indicator_U`: $\widehat{1_{U(\mathfrak a)}}=q^{\deg\mathfrak a}\,1_{U(\mathfrak c-\mathfrak a)}$.
* `isSchwartzBruhat_fourierFF`: the Fourier transform of a Schwartz–Bruhat function is Schwartz–Bruhat.
* **`fourierFF_fourierFF`** (Fourier inversion): $\hat{\hat\Phi}(x)=q^{2g-2}\Phi(-x)$, so the self-dual measure is
  $q^{1-g}\mu_1$ (Weil VII.§2 for $k_{\mathbb A}$), $\mathbb F_q$ the field of constants.
* **`weil_VII_2_poisson_ff`** (Poisson summation for $k\subset k_{\mathbb A}$): $\sum_{\xi\in k}\Phi(\xi)=
  q^{1-g}\sum_{\eta\in k}\hat\Phi(\eta)$ (both sums finite).

*Proof.* A Schwartz–Bruhat function is a finite combination of indicators of cosets $x+U(\mathfrak b)$, and
$\int_{x+U(\mathfrak b)}\chi(ty)\,d\mu_1(t)=q^{\deg\mathfrak b}\chi(xy)1_{U(\mathfrak c-\mathfrak b)}(y)$, because the
annihilator of $U(\mathfrak b)$ under $\chi$ is $U(\mathfrak c-\mathfrak b)$ (`weil_IV_2_thm3_cor1_ff_order`). Poisson
summation is Fourier inversion on the finite group $k_{\mathbb A}/(k+U(\mathfrak b))$, whose characters are the
$\chi(\eta\,\cdot)$, $\eta\in k\cap U(\mathfrak c-\mathfrak b)$ (`weil_IV_2_thm3_ff_annihilator`), with
$[k_{\mathbb A}:k+U(\mathfrak b)]\cdot\lvert k\cap U(\mathfrak b)\rvert^{-1}\cdot q^{\deg\mathfrak b}=q^{g-1}$.
-/

open scoped WithZero ENNReal
open MeasureTheory

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace FFAdeleRing

set_option linter.unusedSectionVars false

/-- **Schwartz–Bruhat functions** on $k_{\mathbb A}$: supported in some $U(\mathfrak a)$ and invariant under
translation by some $U(\mathfrak b)$. -/
def IsSchwartzBruhat (Φ : FFAdeleRing Fq k → ℂ) : Prop :=
  ∃ a b : Divisor Fq k, (∀ x, x ∉ U a → Φ x = 0) ∧ ∀ x, ∀ u ∈ U b, Φ (x + u) = Φ x

variable (ψ₀ : AddChar Fq Circle)

/-- **The Fourier transform** $\hat\Phi(y)=\int\Phi(x)\chi(xy)\,d\mu_1(x)$ on $k_{\mathbb A}$. -/
def fourierFF (Φ : FFAdeleRing Fq k → ℂ) (y : FFAdeleRing Fq k) : ℂ :=
  ∫ x, Φ x * (chiA ψ₀ (x * y) : ℂ) ∂(haar Fq k)


/-- Products of adeles in `U a` and `U b` lie in `U (a + b)`. -/
theorem U_mul_mem {a b : Divisor Fq k} {x y : FFAdeleRing Fq k} (hx : x ∈ U a) (hy : y ∈ U b) :
    x * y ∈ U (a + b) := fun v => by
  show Valued.v (x v * y v) ≤ _
  rw [map_mul, Finsupp.add_apply, WithZero.exp_add]
  exact mul_le_mul' (hx v) (hy v)

/-- `χ` is trivial on products of `U b` with `U (c - b)`. -/
theorem chiA_mul_eq_one {b : Divisor Fq k} {x y : FFAdeleRing Fq k} (hx : x ∈ U b)
    (hy : y ∈ U (canonical Fq k - b)) : chiA ψ₀ (x * y) = 1 := by
  have := U_mul_mem hx hy
  rw [show b + (canonical Fq k - b) = canonical Fq k by abel] at this
  rw [chiA_apply, omegaA_eq_zero_of_mem_U this, AddChar.map_zero_eq_one]

/-- If `y ∉ U (c - b)` then `u ↦ χ(u y)` is non-trivial on `U b`. -/
theorem exists_chiA_ne_one (hψ₀ : ψ₀ ≠ 1) {b : Divisor Fq k} {y : FFAdeleRing Fq k}
    (hy : y ∉ U (canonical Fq k - b)) : ∃ u ∈ U b, chiA ψ₀ (u * y) ≠ 1 := by
  rw [mem_U_iff] at hy
  push Not at hy
  obtain ⟨v, hv⟩ := hy
  have hy0 : y v ≠ 0 := by
    rintro h
    rw [h, map_zero] at hv
    exact absurd hv (not_lt.mpr zero_le)
  obtain ⟨-, t, ht, hne⟩ := weil_IV_2_thm3_cor1_ff_order ψ₀ hψ₀ v
  have hvy : Valued.v (y v) ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (y v) = WithZero.exp m := ⟨_, (WithZero.exp_log hvy).symm⟩
  rw [hm, Finsupp.coe_sub, Pi.sub_apply, WithZero.exp_lt_exp] at hv
  refine ⟨single v (t * (y v)⁻¹), ?_, ?_⟩
  · rw [single_mem_U_iff, map_mul, map_inv₀, hm]
    calc Valued.v t * (WithZero.exp m)⁻¹ ≤ WithZero.exp (canonical Fq k v + 1) * (WithZero.exp m)⁻¹ :=
          mul_le_mul' ht le_rfl
      _ = WithZero.exp (canonical Fq k v + 1 - m) := by
          rw [← WithZero.exp_neg, ← WithZero.exp_add]; ring_nf
      _ ≤ WithZero.exp (b v) := WithZero.exp_le_exp.2 (by omega)
  · rw [mul_comm, mul_single, mul_left_comm, mul_inv_cancel₀ hy0, mul_one]
    exact hne

/-- The coset `r + U b` as a set. -/
def cosSet (b : Divisor Fq k) (r : FFAdeleRing Fq k) : Set (FFAdeleRing Fq k) :=
  (fun x => x - r) ⁻¹' (U b : Set (FFAdeleRing Fq k))

/-- The coset `r + U b` is open. -/
theorem isOpen_cosSet (b : Divisor Fq k) (r : FFAdeleRing Fq k) : IsOpen (cosSet b r) :=
  (isOpen_U b).preimage (continuous_id.sub continuous_const)

/-- The coset `r + U b` is compact. -/
theorem isCompact_cosSet (b : Divisor Fq k) (r : FFAdeleRing Fq k) : IsCompact (cosSet b r) := by
  have : cosSet b r = (fun t => t + r) '' (U b : Set (FFAdeleRing Fq k)) := by
    ext x
    constructor
    · intro hx
      exact ⟨x - r, hx, by simp⟩
    · rintro ⟨t, ht, rfl⟩
      show t + r - r ∈ (U b : Set (FFAdeleRing Fq k))
      simpa using ht
  rw [this]
  exact (isCompact_U b).image (continuous_id.add continuous_const)

/-- The indicator function (valued in `ℂ`) of the coset `r + U b`. -/
def cosInd (b : Divisor Fq k) (r : FFAdeleRing Fq k) : FFAdeleRing Fq k → ℂ :=
  (cosSet b r).indicator 1

open Classical in
/-- Pointwise formula for `cosInd`. -/
theorem cosInd_apply (b : Divisor Fq k) (r x : FFAdeleRing Fq k) :
    cosInd b r x = if x - r ∈ U b then 1 else 0 := by
  unfold cosInd Set.indicator
  rfl

/-- An indicator of a compact open set times a continuous function is integrable. -/
theorem integrable_indicator_cont {s : Set (FFAdeleRing Fq k)} (hs : IsOpen s) (hc : IsCompact s)
    {f : FFAdeleRing Fq k → ℂ} (hf : Continuous f) : Integrable (s.indicator f) (haar Fq k) :=
  (integrable_indicator_iff hs.measurableSet).2 (hf.continuousOn.integrableOn_compact hc)

/-- `x ↦ χ(x y)` as a `ℂ`-valued continuous function. -/
theorem continuous_chiA_mul (y : FFAdeleRing Fq k) :
    Continuous fun x : FFAdeleRing Fq k => (chiA ψ₀ (x * y) : ℂ) :=
  continuous_subtype_val.comp ((continuous_chiA ψ₀).comp (continuous_id.mul continuous_const))

/-- `q^{deg b}` as the (complex) volume of `U b`. -/
theorem haar_U_real (b : Divisor Fq k) :
    (haar Fq k).real (U b : Set (FFAdeleRing Fq k)) = (Nat.card Fq : ℝ) ^ Divisor.deg b := by
  have hq : (Nat.card Fq : NNReal) ≠ 0 := by
    have := Nat.card_pos (α := Fq)
    positivity
  rw [Measure.real, haar_U, ← ENNReal.coe_natCast, ← ENNReal.coe_zpow hq, ENNReal.coe_toReal]
  simp

open Classical in
/-- The integral of `χ(· y)` over `U b`. -/
theorem integral_indicator_chi (hψ₀ : ψ₀ ≠ 1) (b : Divisor Fq k) (y : FFAdeleRing Fq k) :
    ∫ x, (U b : Set (FFAdeleRing Fq k)).indicator (fun t => (chiA ψ₀ (t * y) : ℂ)) x ∂(haar Fq k) =
      if y ∈ U (canonical Fq k - b) then (Nat.card Fq : ℂ) ^ Divisor.deg b else 0 := by
  split_ifs with hy
  · have : (U b : Set (FFAdeleRing Fq k)).indicator (fun t => (chiA ψ₀ (t * y) : ℂ)) =
        (U b : Set (FFAdeleRing Fq k)).indicator (fun _ => (1 : ℂ)) := by
      ext x
      by_cases hx : x ∈ (U b : Set (FFAdeleRing Fq k))
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, chiA_mul_eq_one ψ₀ hx hy]
        rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    rw [this, integral_indicator_const _ (isOpen_U b).measurableSet, haar_U_real]
    simp
  · obtain ⟨u, hu, hne⟩ := exists_chiA_ne_one ψ₀ hψ₀ hy
    set F : FFAdeleRing Fq k → ℂ :=
      (U b : Set (FFAdeleRing Fq k)).indicator (fun t => (chiA ψ₀ (t * y) : ℂ)) with hF
    have h2 : ∀ x, F (x + u) = F x * (chiA ψ₀ (u * y) : ℂ) := by
      intro x
      by_cases hx : x ∈ (U b : Set (FFAdeleRing Fq k))
      · have hxu : x + u ∈ (U b : Set (FFAdeleRing Fq k)) := (U b).add_mem hx hu
        rw [hF, Set.indicator_of_mem hx, Set.indicator_of_mem hxu, add_mul, AddChar.map_add_eq_mul]
        push_cast
        rfl
      · have hxu : x + u ∉ (U b : Set (FFAdeleRing Fq k)) := fun h => hx (by
          have := (U b).sub_mem h hu
          simpa using this)
        rw [hF, Set.indicator_of_notMem hx, Set.indicator_of_notMem hxu, zero_mul]
    have h3 : ∫ x, F x ∂(haar Fq k) = (∫ x, F x ∂(haar Fq k)) * (chiA ψ₀ (u * y) : ℂ) := by
      rw [← integral_mul_const, ← integral_add_right_eq_self F u]
      exact integral_congr_ae (Filter.Eventually.of_forall h2)
    have hz : (chiA ψ₀ (u * y) : ℂ) ≠ 1 := fun h => hne (Subtype.ext h)
    by_contra hI
    apply hz
    have := mul_left_cancel₀ hI (h3.symm.trans (mul_one _).symm)
    exact this


open Classical in
/-- The Fourier transform of a coset indicator. -/
theorem fourierFF_cosInd (hψ₀ : ψ₀ ≠ 1) (b : Divisor Fq k) (r y : FFAdeleRing Fq k) :
    fourierFF ψ₀ (cosInd b r) y =
      if y ∈ U (canonical Fq k - b) then (chiA ψ₀ (r * y) : ℂ) * (Nat.card Fq : ℂ) ^ Divisor.deg b else 0 := by
  unfold fourierFF
  rw [← integral_add_right_eq_self (fun x => cosInd b r x * (chiA ψ₀ (x * y) : ℂ)) r]
  have h : ∀ x : FFAdeleRing Fq k, cosInd b r (x + r) * (chiA ψ₀ ((x + r) * y) : ℂ) =
      (chiA ψ₀ (r * y) : ℂ) *
        (U b : Set (FFAdeleRing Fq k)).indicator (fun t => (chiA ψ₀ (t * y) : ℂ)) x := by
    intro x
    rw [cosInd_apply, add_sub_cancel_right, add_mul, AddChar.map_add_eq_mul]
    by_cases hx : x ∈ U b
    · rw [if_pos hx, Set.indicator_of_mem (show x ∈ (U b : Set (FFAdeleRing Fq k)) from hx)]
      push_cast
      ring
    · rw [if_neg hx, Set.indicator_of_notMem (show x ∉ (U b : Set (FFAdeleRing Fq k)) from hx)]
      simp
  simp_rw [h]
  rw [integral_const_mul, integral_indicator_chi ψ₀ hψ₀]
  split_ifs <;> simp

/-- A Schwartz–Bruhat function is a finite combination of indicators of cosets of one `U b`, with
representatives in `U a`, `b ≤ a`. -/
theorem exists_decomp {Φ : FFAdeleRing Fq k → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    ∃ (a b : Divisor Fq k) (n : ℕ) (ρ : Fin n → FFAdeleRing Fq k), b ≤ a ∧ (∀ i, ρ i ∈ U a) ∧
      ∀ x, Φ x = ∑ i, Φ (ρ i) * cosInd b (ρ i) x := by
  classical
  obtain ⟨a, b, hs, hinv⟩ := hΦ
  set b' : Divisor Fq k := b ⊓ a with hb'
  have hb'a : b' ≤ a := inf_le_right
  have hb'b : b' ≤ b := inf_le_left
  haveI := finite_quotient_U_of_le hb'a
  let e := Finite.equivFin (U a ⧸ (U b').addSubgroupOf (U a))
  let ρ : Fin (Nat.card (U a ⧸ (U b').addSubgroupOf (U a))) → FFAdeleRing Fq k :=
    fun i => ((e.symm i).out : U a)
  have hρ : ∀ i, ρ i ∈ U a := fun i => ((e.symm i).out : U a).2
  refine ⟨a, b', _, ρ, hb'a, hρ, fun x => ?_⟩
  by_cases hx : x ∈ U a
  · set q : U a ⧸ (U b').addSubgroupOf (U a) := QuotientAddGroup.mk ⟨x, hx⟩ with hq
    have key : ∀ i, x - ρ i ∈ U b' ↔ i = e q := by
      intro i
      have h1 : (e.symm i = q) ↔ x - ρ i ∈ U b' := by
        rw [← QuotientAddGroup.out_eq' (e.symm i), hq, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, QuotientAddGroup.out_eq']
        rw [neg_add_eq_sub]
      rw [← h1, Equiv.symm_apply_eq]
    have hsum : ∑ i, Φ (ρ i) * cosInd b' (ρ i) x = Φ (ρ (e q)) := by
      rw [Finset.sum_eq_single (e q)]
      · rw [cosInd_apply, if_pos ((key _).2 rfl), mul_one]
      · intro i _ hi
        rw [cosInd_apply, if_neg (fun h => hi ((key i).1 h)), mul_zero]
      · simp
    rw [hsum]
    have h1 : x - ρ (e q) ∈ U b' := (key _).2 rfl
    have := hinv (ρ (e q)) (x - ρ (e q)) (U_mono hb'b h1)
    rw [add_sub_cancel] at this
    exact this
  · rw [hs x hx]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [cosInd_apply, if_neg, mul_zero]
    intro h
    apply hx
    have := (U a).add_mem (U_mono hb'a h) (hρ i)
    simpa using this

open Classical in
/-- The Fourier transform of a combination of coset indicators. -/
theorem fourierFF_of_decomp (hψ₀ : ψ₀ ≠ 1) {Φ : FFAdeleRing Fq k → ℂ} {b : Divisor Fq k} {n : ℕ}
    {ρ : Fin n → FFAdeleRing Fq k} {φ : Fin n → ℂ}
    (h : ∀ x, Φ x = ∑ i, φ i * cosInd b (ρ i) x) (y : FFAdeleRing Fq k) :
    fourierFF ψ₀ Φ y = ∑ i, φ i *
      (if y ∈ U (canonical Fq k - b) then (chiA ψ₀ (ρ i * y) : ℂ) * (Nat.card Fq : ℂ) ^ Divisor.deg b else 0) := by
  have hint : ∀ i, Integrable (fun x => φ i * cosInd b (ρ i) x * (chiA ψ₀ (x * y) : ℂ)) (haar Fq k) := by
    intro i
    have : (fun x => φ i * cosInd b (ρ i) x * (chiA ψ₀ (x * y) : ℂ)) =
        fun x => φ i * (cosSet b (ρ i)).indicator (fun x => (chiA ψ₀ (x * y) : ℂ)) x := by
      ext x
      by_cases hx : x ∈ cosSet b (ρ i)
      · simp [cosInd, Set.indicator_of_mem hx]
      · simp [cosInd, Set.indicator_of_notMem hx]
    rw [this]
    exact (integrable_indicator_cont (isOpen_cosSet _ _) (isCompact_cosSet _ _)
      (continuous_chiA_mul ψ₀ y)).const_mul _
  unfold fourierFF
  simp_rw [h, Finset.sum_mul]
  rw [integral_finset_sum _ (fun i _ => hint i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  congr 1
  exact fourierFF_cosInd ψ₀ hψ₀ b (ρ i) y


open Rep Divisor in
/-- Every non-zero `λ ∈ Ω(b)` is `xω₀` with `x ∈ L(c - b)` (duality in Riemann–Roch). -/
theorem exists_eq_xω_mem {b : Divisor Fq k} {lam : Module.Dual Fq (Rep Fq k)}
    (hlam : lam ∈ Omega Fq k b) (hlam0 : lam ≠ 0) :
    ∃ x ∈ (canonical Fq k - b).riemannRochSpace, lam = xω x (weilDifferential₀ Fq k) := by
  obtain ⟨x, hx⟩ := exists_eq_xω hlam0 weilDifferential₀_ne_zero ⟨b, hlam⟩ weilDifferential₀_mem
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hlam0 (by rw [hx, xω_zero_left])
  refine ⟨x, ?_, hx⟩
  refine (nonneg_add_div_iff (canonical Fq k - b) (Units.mk0 x hx0)).mp ?_
  have h1 : weilDifferential₀ Fq k ∈ Omega Fq k (b - Divisor.div (Units.mk0 x hx0)) := by
    rw [← mem_Omega_xω]
    show xω x (weilDifferential₀ Fq k) ∈ _
    rw [← hx]
    exact hlam
  have h2 := (mem_Omega_canonical_iff _).1 h1
  intro v
  have := h2 v
  simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add,
    Pi.add_apply] at this ⊢
  omega

/-- Duality: if `ω̂(r η) = 0` for all `η ∈ L(c - b)` then `r ∈ k + U b`. -/
theorem exists_sub_diag_mem_U_of_annihilates {b : Divisor Fq k} {r : FFAdeleRing Fq k}
    (h : ∀ η ∈ (canonical Fq k - b).riemannRochSpace, omegaA (r * diag η) = 0) :
    ∃ ξ : k, r - diag ξ ∈ U b := by
  by_contra hne
  push Not at hne
  obtain ⟨α, hα⟩ := exists_ofRep_sub_mem_U b r
  have hαS : α ∉ Rep.S Fq k b := by
    intro hS
    obtain ⟨u, hu, β, ⟨ξ, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hS
    apply hne ξ
    have h1 : r - diag ξ = (r - ofRep (u + Rep.diag ξ)) + ofRep u := by
      rw [map_add, ofRep_diag]; abel
    rw [h1]
    exact (U b).add_mem hα ((ofRep_mem_U_iff _ _).2 hu)
  obtain ⟨lam, hlam, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hαS inferInstance
  have hlamO : lam ∈ Rep.Omega Fq k b := by
    rw [Rep.mem_Omega_iff]
    intro α' hα'
    have : lam α' ∈ (Rep.S Fq k b).map lam := Submodule.mem_map_of_mem hα'
    rw [hmap] at this
    exact (Submodule.mem_bot _).1 this
  have hlam0 : lam ≠ 0 := fun h0 => hlam (by rw [h0]; rfl)
  obtain ⟨x, hxL, hx⟩ := exists_eq_xω_mem hlamO hlam0
  apply hlam
  rw [hx, Rep.xω_apply]
  have e2 : ofRep (Rep.mulRep x α) = diag x * ofRep α := by
    ext v
    show v.toCompletion (x * α.1 v) = v.toCompletion x * v.toCompletion (α.1 v)
    rw [map_mul]
  rw [← omegaA_ofRep, e2]
  have h3 : diag x * ofRep α = r * diag x - diag x * (r - ofRep α) := by ring
  have h4 := U_mul_mem ((diag_mem_U_iff _ _).2 hxL) hα
  rw [sub_add_cancel] at h4
  rw [h3, map_sub, h x hxL, omegaA_eq_zero_of_mem_U h4, sub_zero]

/-- The number of points of a (finite) submodule, as a `finsum` of indicators. -/
theorem finsum_indicator_one (S : Divisor Fq k) :
    ∑ᶠ ζ : k, (S.riemannRochSpace : Set k).indicator (fun _ => (1 : ℂ)) ζ = (Nat.card S.riemannRochSpace : ℂ) := by
  haveI : Finite S.riemannRochSpace := Module.finite_of_finite Fq
  have hfin : (S.riemannRochSpace : Set k).Finite := Set.toFinite _
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
  · rw [Finset.sum_congr rfl (fun ζ hζ => Set.indicator_of_mem (hfin.mem_toFinset.1 hζ) _)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, ← Nat.card_eq_card_finite_toFinset hfin]
    rfl
  · intro ζ hζ
    by_contra h
    exact hζ (Set.indicator_of_notMem (by simpa using h) _)

/-- `#L(a) = q^{ℓ(a)}`. -/
theorem natCard_L (a : Divisor Fq k) : Nat.card a.riemannRochSpace = Nat.card Fq ^ a.ell := by
  haveI : Finite a.riemannRochSpace := Module.finite_of_finite Fq
  haveI : Module.Finite Fq a.riemannRochSpace := Module.Finite.of_finite
  exact Module.natCard_eq_pow_finrank (K := Fq) (V := a.riemannRochSpace)

open Classical in
/-- Poisson summation for the indicator of a coset `r + U b`. -/
theorem poisson_coset (hψ₀ : ψ₀ ≠ 1) (b : Divisor Fq k) (r : FFAdeleRing Fq k) :
    ∑ᶠ ξ : k, cosInd b r (diag ξ) = (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k + Divisor.deg b) *
      ∑ᶠ η : k, (((canonical Fq k - b).riemannRochSpace : Set k)).indicator
        (fun η => (chiA ψ₀ (r * diag η) : ℂ)) η := by
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := Fq)
    exact_mod_cast this.ne'
  by_cases hex : ∃ ξ0 : k, r - diag ξ0 ∈ U b
  · obtain ⟨ξ0, hξ0⟩ := hex
    have hN : ∀ ξ : k, cosInd b r (diag ξ) = (b.riemannRochSpace : Set k).indicator (fun _ => (1 : ℂ)) (ξ - ξ0) := by
      intro ξ
      rw [cosInd_apply]
      have hiff : diag ξ - r ∈ U b ↔ (ξ - ξ0) ∈ b.riemannRochSpace := by
        rw [← diag_mem_U_iff]
        have : diag (ξ - ξ0) = (diag ξ - r) + (r - diag ξ0) := by rw [diag_sub]; abel
        rw [this]
        exact (AddSubgroup.add_mem_cancel_right _ hξ0).symm
      by_cases hm : (ξ - ξ0) ∈ b.riemannRochSpace
      · rw [if_pos (hiff.2 hm), Set.indicator_of_mem (show ξ - ξ0 ∈ (b.riemannRochSpace : Set k) from hm)]
      · rw [if_neg (mt hiff.1 hm), Set.indicator_of_notMem (show ξ - ξ0 ∉ (b.riemannRochSpace : Set k) from hm)]
    have hM : ∀ η : k, (((canonical Fq k - b).riemannRochSpace : Set k)).indicator
        (fun η => (chiA ψ₀ (r * diag η) : ℂ)) η =
        (((canonical Fq k - b).riemannRochSpace : Set k)).indicator (fun _ => (1 : ℂ)) η := by
      intro η
      by_cases hη : η ∈ (canonical Fq k - b).riemannRochSpace
      · rw [Set.indicator_of_mem (show η ∈ (((canonical Fq k - b).riemannRochSpace : Set k)) from hη),
          Set.indicator_of_mem (show η ∈ (((canonical Fq k - b).riemannRochSpace : Set k)) from hη)]
        have : r * diag η = diag (ξ0 * η) + (r - diag ξ0) * diag η := by
          rw [← diag_mul_diag]; ring
        rw [this, AddChar.map_add_eq_mul, chiA_diag, one_mul,
          chiA_mul_eq_one ψ₀ hξ0 ((diag_mem_U_iff _ _).2 hη)]
        rfl
      · rw [Set.indicator_of_notMem (show η ∉ (((canonical Fq k - b).riemannRochSpace : Set k)) from hη),
          Set.indicator_of_notMem (show η ∉ (((canonical Fq k - b).riemannRochSpace : Set k)) from hη)]
    simp_rw [hN, hM]
    rw [show (∑ᶠ ξ : k, (b.riemannRochSpace : Set k).indicator (fun _ => (1 : ℂ)) (ξ - ξ0)) =
        ∑ᶠ ζ : k, (b.riemannRochSpace : Set k).indicator (fun _ => (1 : ℂ)) ζ from
        finsum_comp_equiv (Equiv.subRight ξ0),
      finsum_indicator_one, finsum_indicator_one, natCard_L, natCard_L]
    push_cast
    rw [← zpow_natCast, ← zpow_natCast (Nat.card Fq : ℂ) (canonical Fq k - b).ell, ← zpow_add₀ hq0,
      weil_VI_2_thm2 b]
    congr 1
    ring
  · push Not at hex
    have hN : ∀ ξ : k, cosInd b r (diag ξ) = 0 := by
      intro ξ
      rw [cosInd_apply, if_neg]
      intro h
      apply hex ξ
      have := (U b).neg_mem h
      simpa using this
    simp_rw [hN]
    rw [finsum_zero]
    symm
    rw [mul_eq_zero]
    right
    -- the character sum vanishes
    have hnz : ∃ η0 ∈ (canonical Fq k - b).riemannRochSpace, omegaA (r * diag η0) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨ξ, hξ⟩ := exists_sub_diag_mem_U_of_annihilates hcon
      exact hex ξ hξ
    obtain ⟨η0, hη0, hne0⟩ := hnz
    obtain ⟨t, ht⟩ := AddChar.ne_one_iff.1 hψ₀
    set c : Fq := t * (omegaA (r * diag η0))⁻¹ with hc
    set η1 : k := algebraMap Fq k c * η0 with hη1
    have hη1L : η1 ∈ (canonical Fq k - b).riemannRochSpace := by
      have := Submodule.smul_mem _ c hη0
      rwa [Algebra.smul_def] at this
    have hω1 : omegaA (r * diag η1) = t := by
      have : r * diag η1 = diag (algebraMap Fq k c) * (r * diag η0) := by
        rw [hη1, ← diag_mul_diag]; ring
      rw [this, omegaA_const_mul, hc, mul_assoc, inv_mul_cancel₀ hne0, mul_one]
    set z : ℂ := (chiA ψ₀ (r * diag η1) : ℂ) with hz
    have hz1 : z ≠ 1 := by
      intro h
      apply ht
      have h' : chiA ψ₀ (r * diag η1) = 1 := Subtype.ext h
      rwa [chiA_apply, hω1] at h'
    set Mf := ∑ᶠ η : k, (((canonical Fq k - b).riemannRochSpace : Set k)).indicator
        (fun η => (chiA ψ₀ (r * diag η) : ℂ)) η with hMf
    have hF : ∀ η : k, (((canonical Fq k - b).riemannRochSpace : Set k)).indicator
        (fun η => (chiA ψ₀ (r * diag η) : ℂ)) (η + η1) =
        (((canonical Fq k - b).riemannRochSpace : Set k)).indicator
          (fun η => (chiA ψ₀ (r * diag η) : ℂ)) η * z := by
      intro η
      by_cases hη : η ∈ (canonical Fq k - b).riemannRochSpace
      · have hη' : η + η1 ∈ (canonical Fq k - b).riemannRochSpace := Submodule.add_mem _ hη hη1L
        rw [Set.indicator_of_mem (show η ∈ (((canonical Fq k - b).riemannRochSpace : Set k)) from hη),
          Set.indicator_of_mem (show η + η1 ∈ (((canonical Fq k - b).riemannRochSpace : Set k)) from hη'),
          diag_add, mul_add, AddChar.map_add_eq_mul]
        push_cast
        rfl
      · have hη' : η + η1 ∉ (canonical Fq k - b).riemannRochSpace := fun h => hη (by
          have := Submodule.sub_mem _ h hη1L
          simpa using this)
        rw [Set.indicator_of_notMem (show η ∉ (((canonical Fq k - b).riemannRochSpace : Set k)) from hη),
          Set.indicator_of_notMem (show η + η1 ∉ (((canonical Fq k - b).riemannRochSpace : Set k)) from hη')]
        simp
    have hshift : Mf = Mf * z := by
      rw [hMf, finsum_mul]
      rw [← finsum_comp_equiv (Equiv.addRight η1)]
      exact finsum_congr fun η => hF η
    have : Mf * (1 - z) = 0 := by rw [mul_sub, mul_one, ← hshift, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h).symm hz1


/-- `∑ᶠ c * f = c * ∑ᶠ f` in `ℂ`. -/
theorem finsum_const_mul' (c : ℂ) (f : k → ℂ) : ∑ᶠ ξ : k, c * f ξ = c * ∑ᶠ ξ : k, f ξ := by
  simp_rw [mul_comm c]
  rw [← finsum_mul, mul_comm]

/-- The coset indicator along `k` is supported in `L(a)` when `r ∈ U a` and `b ≤ a`. -/
theorem support_cosInd_diag {a b : Divisor Fq k} (hba : b ≤ a) {r : FFAdeleRing Fq k} (hr : r ∈ U a)
    (c : ℂ) :
    (Function.support fun ξ : k => c * cosInd b r (diag ξ)) ⊆ (a.riemannRochSpace : Set k) := by
  classical
  intro ξ hξ
  by_contra h
  apply hξ
  show c * cosInd b r (diag ξ) = 0
  rw [cosInd_apply, if_neg, mul_zero]
  intro hm
  apply h
  have := (U a).add_mem (U_mono hba hm) hr
  rw [sub_add_cancel] at this
  exact (diag_mem_U_iff a ξ).1 this

open Classical in
/-- $\widehat{1_{U(\mathfrak a)}}=q^{\deg\mathfrak a}1_{U(\mathfrak c-\mathfrak a)}$. -/
theorem fourierFF_indicator_U (hψ₀ : ψ₀ ≠ 1) (a : Divisor Fq k) (y : FFAdeleRing Fq k) :
    fourierFF ψ₀ ((U a : Set (FFAdeleRing Fq k)).indicator 1) y =
      if y ∈ U (canonical Fq k - a) then (Nat.card Fq : ℂ) ^ Divisor.deg a else 0 := by
  unfold fourierFF
  rw [← integral_indicator_chi ψ₀ hψ₀ a y]
  congr 1
  ext x
  by_cases hx : x ∈ (U a : Set (FFAdeleRing Fq k))
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- The Fourier transform of a Schwartz–Bruhat function is a Schwartz–Bruhat function. -/
theorem isSchwartzBruhat_fourierFF (hψ₀ : ψ₀ ≠ 1) {Φ : FFAdeleRing Fq k → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    IsSchwartzBruhat (fourierFF ψ₀ Φ) := by
  classical
  obtain ⟨a, b, n, ρ, hba, hρ, hdec⟩ := exists_decomp hΦ
  have hF := fun y => fourierFF_of_decomp ψ₀ hψ₀ hdec y
  refine ⟨canonical Fq k - b, canonical Fq k - a, fun y hy => ?_, fun y u hu => ?_⟩
  · rw [hF y]
    exact Finset.sum_eq_zero fun i _ => by rw [if_neg hy, mul_zero]
  · have hle : U (canonical Fq k - a) ≤ U (canonical Fq k - b) := U_mono (sub_le_sub_left hba _)
    have hiff : y + u ∈ U (canonical Fq k - b) ↔ y ∈ U (canonical Fq k - b) :=
      AddSubgroup.add_mem_cancel_right _ (hle hu)
    rw [hF, hF]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hy : y ∈ U (canonical Fq k - b)
    · rw [if_pos hy, if_pos (hiff.2 hy), mul_add, AddChar.map_add_eq_mul, chiA_mul_eq_one ψ₀ (hρ i) hu]
      push_cast
      simp
    · rw [if_neg hy, if_neg (mt hiff.1 hy)]

/-- **Fourier inversion on $k_{\mathbb A}$**: $\hat{\hat\Phi}(x)=q^{2g-2}\Phi(-x)$ for Schwartz–Bruhat $\Phi$
($\mathbb F_q$ the field of constants); the self-dual Haar measure is $q^{1-g}\mu_1$. -/
@[kb "weil1973bnt" "Ch. VII, §2, text p. 105 (Fourier inversion and the self-dual measure), k_A, function fields"]
theorem fourierFF_fourierFF (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) {Φ : FFAdeleRing Fq k → ℂ}
    (hΦ : IsSchwartzBruhat Φ) (x : FFAdeleRing Fq k) :
    fourierFF ψ₀ (fourierFF ψ₀ Φ) x = (Nat.card Fq : ℂ) ^ (2 * Rep.genusInt Fq k - 2) * Φ (-x) := by
  classical
  obtain ⟨a, b, n, ρ, hba, hρ, hdec⟩ := exists_decomp hΦ
  have hF := fun y => fourierFF_of_decomp ψ₀ hψ₀ hdec y
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := Fq)
    exact_mod_cast this.ne'
  have hterm : ∀ i, ∀ y : FFAdeleRing Fq k,
      Φ (ρ i) * (if y ∈ U (canonical Fq k - b) then (chiA ψ₀ (ρ i * y) : ℂ) * (Nat.card Fq : ℂ) ^ Divisor.deg b
        else 0) * (chiA ψ₀ (y * x) : ℂ) =
      (Φ (ρ i) * (Nat.card Fq : ℂ) ^ Divisor.deg b) *
        (U (canonical Fq k - b) : Set (FFAdeleRing Fq k)).indicator
          (fun t => (chiA ψ₀ (t * (ρ i + x)) : ℂ)) y := by
    intro i y
    by_cases hy : y ∈ U (canonical Fq k - b)
    · rw [if_pos hy, Set.indicator_of_mem (show y ∈ (U (canonical Fq k - b) : Set (FFAdeleRing Fq k)) from hy),
        mul_add, AddChar.map_add_eq_mul, mul_comm y (ρ i)]
      push_cast
      ring
    · rw [if_neg hy, Set.indicator_of_notMem (show y ∉ (U (canonical Fq k - b) : Set (FFAdeleRing Fq k)) from hy)]
      simp
  have hint : ∀ i, Integrable (fun y => Φ (ρ i) * (if y ∈ U (canonical Fq k - b)
      then (chiA ψ₀ (ρ i * y) : ℂ) * (Nat.card Fq : ℂ) ^ Divisor.deg b else 0) * (chiA ψ₀ (y * x) : ℂ))
      (haar Fq k) := by
    intro i
    simp_rw [hterm i]
    exact (integrable_indicator_cont (isOpen_U _) (isCompact_U _) (continuous_chiA_mul ψ₀ _)).const_mul _
  have hqq : (Nat.card Fq : ℂ) ^ Divisor.deg b * (Nat.card Fq : ℂ) ^ Divisor.deg (canonical Fq k - b) =
      (Nat.card Fq : ℂ) ^ (2 * Rep.genusInt Fq k - 2) := by
    rw [← zpow_add₀ hq0, ← map_add, add_sub_cancel, (weil_VI_2_cor1 hc).1]
  have h0 : fourierFF ψ₀ (fourierFF ψ₀ Φ) x =
      ∫ y, fourierFF ψ₀ Φ y * (chiA ψ₀ (y * x) : ℂ) ∂(haar Fq k) := rfl
  rw [h0]
  simp_rw [hF, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hint i)]
  simp_rw [hterm]
  simp_rw [integral_const_mul, integral_indicator_chi ψ₀ hψ₀, sub_sub_cancel]
  rw [hdec (-x), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cosInd_apply]
  have hiff : -x - ρ i ∈ U b ↔ ρ i + x ∈ U b := by
    rw [show -x - ρ i = -(ρ i + x) by abel]
    exact neg_mem_iff
  by_cases hm : ρ i + x ∈ U b
  · rw [if_pos hm, if_pos (hiff.2 hm)]
    rw [← hqq]; ring
  · rw [if_neg hm, if_neg (mt hiff.1 hm)]; simp

/-- For a Schwartz–Bruhat function only finitely many $\Phi(\xi)$, $\xi\in k$, are non-zero. -/
theorem finite_support_diag {Φ : FFAdeleRing Fq k → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    (Function.support fun ξ : k => Φ (diag ξ)).Finite := by
  obtain ⟨a, b, hs, -⟩ := hΦ
  haveI : Finite a.riemannRochSpace := Module.finite_of_finite Fq
  refine (Set.toFinite (a.riemannRochSpace : Set k)).subset fun ξ hξ => ?_
  by_contra h
  exact hξ (hs _ (fun h' => h ((diag_mem_U_iff a ξ).1 h')))

/-- **Weil, VII.§2, Poisson summation formula (1) for $(k_{\mathbb A},k)$, function fields**:
$\sum_{\xi\in k}\Phi(\xi)=q^{1-g}\sum_{\eta\in k}\hat\Phi(\eta)$ for every Schwartz–Bruhat function $\Phi$ ($\mathbb F_q$
the field of constants; $q^{1-g}\mu_1$ is the self-dual measure, giving $k_{\mathbb A}/k$ measure $1$). -/
@[kb "weil1973bnt" "Ch. VII, §2, text p. 106 (Poisson summation formula (1)), (k_A, k), function fields"]
theorem weil_VII_2_poisson_ff (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) {Φ : FFAdeleRing Fq k → ℂ}
    (hΦ : IsSchwartzBruhat Φ) :
    ∑ᶠ ξ : k, Φ (diag ξ) = (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * ∑ᶠ η : k, fourierFF ψ₀ Φ (diag η) := by
  classical
  obtain ⟨a, b, n, ρ, hba, hρ, hdec⟩ := exists_decomp hΦ
  have hF := fun y => fourierFF_of_decomp ψ₀ hψ₀ hdec y
  haveI : Finite a.riemannRochSpace := Module.finite_of_finite Fq
  haveI : Finite (canonical Fq k - b).riemannRochSpace := Module.finite_of_finite Fq
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := Fq)
    exact_mod_cast this.ne'
  have hL : ∑ᶠ ξ : k, Φ (diag ξ) =
      ∑ i, Φ (ρ i) * ∑ᶠ ξ : k, cosInd b (ρ i) (diag ξ) := by
    rw [finsum_congr (fun ξ => hdec (diag ξ))]
    rw [finsum_sum_comm]
    · exact Finset.sum_congr rfl fun i _ => finsum_const_mul' _ _
    · intro i _
      exact (Set.toFinite (a.riemannRochSpace : Set k)).subset (support_cosInd_diag hba (hρ i) _)
  have hterm : ∀ (i : Fin n) (η : k), Φ (ρ i) *
      (if diag η ∈ U (canonical Fq k - b) then (chiA ψ₀ (ρ i * diag η) : ℂ) * (Nat.card Fq : ℂ) ^ Divisor.deg b
        else 0) =
      (Φ (ρ i) * (Nat.card Fq : ℂ) ^ Divisor.deg b) *
        (((canonical Fq k - b).riemannRochSpace : Set k)).indicator
          (fun η => (chiA ψ₀ (ρ i * diag η) : ℂ)) η := by
    intro i η
    by_cases hη : η ∈ (canonical Fq k - b).riemannRochSpace
    · rw [if_pos ((diag_mem_U_iff _ _).2 hη),
        Set.indicator_of_mem (show η ∈ (((canonical Fq k - b).riemannRochSpace : Set k)) from hη)]
      ring
    · rw [if_neg (fun h => hη ((diag_mem_U_iff _ _).1 h)),
        Set.indicator_of_notMem (show η ∉ (((canonical Fq k - b).riemannRochSpace : Set k)) from hη)]
      simp
  have hR : ∑ᶠ η : k, fourierFF ψ₀ Φ (diag η) =
      ∑ i, (Φ (ρ i) * (Nat.card Fq : ℂ) ^ Divisor.deg b) *
        ∑ᶠ η : k, (((canonical Fq k - b).riemannRochSpace : Set k)).indicator
          (fun η => (chiA ψ₀ (ρ i * diag η) : ℂ)) η := by
    have hR1 : ∀ η : k, fourierFF ψ₀ Φ (diag η) = ∑ i, (Φ (ρ i) * (Nat.card Fq : ℂ) ^ Divisor.deg b) *
        (((canonical Fq k - b).riemannRochSpace : Set k)).indicator
          (fun η => (chiA ψ₀ (ρ i * diag η) : ℂ)) η := fun η => by
      rw [hF]; exact Finset.sum_congr rfl fun i _ => hterm i η
    rw [finsum_congr hR1]
    rw [finsum_sum_comm]
    · exact Finset.sum_congr rfl fun i _ => finsum_const_mul' _ _
    · intro i _
      refine (Set.toFinite (((canonical Fq k - b).riemannRochSpace : Set k))).subset ?_
      intro η hη
      by_contra h
      apply hη
      show (Φ (ρ i) * (Nat.card Fq : ℂ) ^ Divisor.deg b) * _ = 0
      rw [Set.indicator_of_notMem (show η ∉ (((canonical Fq k - b).riemannRochSpace : Set k)) from h),
        mul_zero]
  rw [hL, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [poisson_coset ψ₀ hψ₀ b (ρ i), zpow_add₀ hq0]
  ring

end FFAdeleRing

end NumberFieldKB.WeilBNT.FF
