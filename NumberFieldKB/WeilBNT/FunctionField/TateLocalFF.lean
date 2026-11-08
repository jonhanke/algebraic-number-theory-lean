import NumberFieldKB.WeilBNT.FunctionField.TateFF

/-!
# Gauss sums modulo $\mathfrak p_v^{f}$ and the Fourier transform of $\Phi_\omega$ (Weil VII.§7, characteristic $p$)

$k$ is a global function field with field of constants $\mathbb F_q$, $\chi$ the basic character of $k_{\mathbb A}$
(`chiA ψ₀`), $\mathfrak c$ the canonical divisor, and $\omega$ a quasicharacter of $G_k$ with conductor
$\mathfrak f=\sum_vf(v)v$.

* `reps v n`: a finite set of representatives of $\mathfrak r_v/\mathfrak p_v^n$ in $\mathfrak r_v$.
* `prodFn T E φ`: $P(T,E)(x)=[x\in U(E)]\prod_{v\in T}\varphi_v(x_v)$ for local functions $\varphi_v$ on $k_v$ that are
  $\mathfrak p_v^{n_v}$-periodic on $\mathfrak r_v$.
* **`fourierFF_prodFn`**: $\hat P(T,E)(y)=\prod_{v\in T}G_v(y_v)\,q^{\deg E-\deg n_T}\,[y\in U(\mathfrak c-E+n_T)]$ with the
  **Gauss sums modulo $\mathfrak p_v^{n_v}$** $G_v(s)=\sum_{t\in\mathfrak r_v/\mathfrak p_v^{n_v}}\varphi_v(t)\chi_v(ts)$.
-/

open MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal

namespace NumberFieldKB.WeilBNT.FF

noncomputable section

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

set_option linter.unusedSectionVars false

open FFIdeleGroup FFAdeleRing

namespace Place

/-- $\mathfrak p_v^n=\{t\in k_v: v(t)\le e^{-n}\}$ as an additive subgroup ($\mathfrak p_v^0=\mathfrak r_v$). -/
def pPow (v : Place Fq k) (n : ℤ) : AddSubgroup v.Completion where
  carrier := {t | Valued.v t ≤ WithZero.exp (-n)}
  zero_mem' := by simp
  add_mem' {s t} hs ht := by
    show Valued.v (s + t) ≤ _
    exact (Valuation.map_add _ _ _).trans (max_le hs ht)
  neg_mem' {t} ht := by
    show Valued.v (-t) ≤ _
    rw [Valuation.map_neg]; exact ht

theorem mem_pPow {v : Place Fq k} {n : ℤ} {t : v.Completion} :
    t ∈ v.pPow n ↔ Valued.v t ≤ WithZero.exp (-n) := by rfl

theorem pPow_anti {v : Place Fq k} {m n : ℤ} (h : m ≤ n) : v.pPow n ≤ v.pPow m := fun _ ht =>
  mem_pPow.2 ((mem_pPow.1 ht).trans (WithZero.exp_le_exp.2 (by omega)))

end Place

namespace FFAdeleRing

theorem single_zero' (v : Place Fq k) : single v (0 : v.Completion) = 0 := by
  have := single_add v (0 : v.Completion) 0
  rw [add_zero] at this
  exact left_eq_add.1 this |>.symm ▸ rfl

theorem single_sub' (v : Place Fq k) (s t : v.Completion) : single v (s - t) = single v s - single v t := by
  rw [eq_sub_iff_add_eq, ← single_add, sub_add_cancel]

theorem single_sub_single_mem_U (v : Place Fq k) (n : ℕ) (s t : v.Completion) :
    single v s - single v t ∈ U (-((n : ℤ) • Finsupp.single v 1)) ↔ s - t ∈ v.pPow n := by
  classical
  rw [← single_sub', single_mem_U_iff, Place.mem_pPow]
  simp

end FFAdeleRing

namespace Place

theorem finite_quotient_pPow (v : Place Fq k) (n : ℕ) :
    Finite (v.pPow 0 ⧸ (v.pPow n).addSubgroupOf (v.pPow 0)) := by
  classical
  set a : Divisor Fq k := 0
  set b : Divisor Fq k := -((n : ℤ) • Finsupp.single v 1)
  have hba : b ≤ a := fun w => by
    simp only [b, a, Finsupp.coe_neg, Pi.neg_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero,
      Pi.zero_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have := finite_quotient_U_of_le hba
  let g : v.pPow 0 →+ U a :=
    { toFun := fun t => ⟨FFAdeleRing.single v t, (single_mem_U_iff a v t).2 (by
        have := mem_pPow.1 t.2; simpa [a] using this)⟩
      map_zero' := Subtype.ext (FFAdeleRing.single_zero' v)
      map_add' := fun s t => Subtype.ext (FFAdeleRing.single_add v s t) }
  have hg : (v.pPow n).addSubgroupOf (v.pPow 0) ≤ ((U b).addSubgroupOf (U a)).comap g := by
    intro t ht
    rw [AddSubgroup.mem_addSubgroupOf] at ht
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    have := (FFAdeleRing.single_sub_single_mem_U v n (t : v.Completion) 0).2 (by rw [sub_zero]; exact ht)
    rwa [FFAdeleRing.single_zero', sub_zero] at this
  let f := QuotientAddGroup.map _ _ g hg
  refine Finite.of_injective f fun x y hxy => ?_
  induction x using QuotientAddGroup.induction_on with | H s => ?_
  induction y using QuotientAddGroup.induction_on with | H t => ?_
  rw [QuotientAddGroup.eq]
  have := (QuotientAddGroup.eq (s := (U b).addSubgroupOf (U a))).1 hxy
  rw [AddSubgroup.mem_addSubgroupOf] at this ⊢
  have h2 := (FFAdeleRing.single_sub_single_mem_U v n (t : v.Completion) s).1 (by
    simpa [g, neg_add_eq_sub, b] using this)
  simpa [neg_add_eq_sub] using h2

end Place

/-! ### Representatives of `𝔯_v / 𝔭_v^n` -/

namespace Place

open Classical in
/-- A finite set of representatives of $\mathfrak r_v/\mathfrak p_v^n$ in $\mathfrak r_v$. -/
def reps (v : Place Fq k) (n : ℕ) : Finset v.Completion :=
  letI : Fintype (v.pPow 0 ⧸ (v.pPow n).addSubgroupOf (v.pPow 0)) :=
    @Fintype.ofFinite _ (v.finite_quotient_pPow n)
  (Finset.univ : Finset (v.pPow 0 ⧸ (v.pPow n).addSubgroupOf (v.pPow 0))).image
    fun q => ((Quotient.out q : v.pPow 0) : v.Completion)

theorem mem_pPow_zero_of_mem_reps {v : Place Fq k} {n : ℕ} {t : v.Completion} (ht : t ∈ v.reps n) :
    t ∈ v.pPow 0 := by
  classical
  unfold reps at ht
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
  exact (Quotient.out q : v.pPow 0).2

theorem existsUnique_reps (v : Place Fq k) (n : ℕ) {x : v.Completion} (hx : x ∈ v.pPow 0) :
    ∃! t, t ∈ v.reps n ∧ x - t ∈ v.pPow n := by
  classical
  have hfin := v.finite_quotient_pPow n
  letI := Fintype.ofFinite (v.pPow 0 ⧸ (v.pPow n).addSubgroupOf (v.pPow 0))
  set q : v.pPow 0 ⧸ (v.pPow n).addSubgroupOf (v.pPow 0) := QuotientAddGroup.mk ⟨x, hx⟩
  have hmem : ∀ q' : v.pPow 0 ⧸ (v.pPow n).addSubgroupOf (v.pPow 0),
      ((Quotient.out q' : v.pPow 0) : v.Completion) ∈ v.reps n := fun q' => by
    unfold reps
    exact Finset.mem_image.2 ⟨q', Finset.mem_univ _, rfl⟩
  have hkey : ∀ q' : v.pPow 0 ⧸ (v.pPow n).addSubgroupOf (v.pPow 0),
      x - ((Quotient.out q' : v.pPow 0) : v.Completion) ∈ v.pPow n ↔ q' = q := fun q' => by
    conv_rhs => rw [← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [neg_add_eq_sub]
  refine ⟨((Quotient.out q : v.pPow 0) : v.Completion), ⟨hmem q, (hkey q).2 rfl⟩, ?_⟩
  rintro t ⟨ht, hxt⟩
  unfold reps at ht
  obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 ht
  rw [(hkey q').1 hxt]

end Place

/-! ### Products of local functions -/

namespace FFAdeleRing

open Classical in
/-- $P(T,E)(x)=[x\in U(E)]\prod_{v\in T}\varphi_v(x_v)$. -/
def prodFn (T : Finset (Place Fq k)) (E : Divisor Fq k) (φ : ∀ v : Place Fq k, v.Completion → ℂ)
    (x : FFAdeleRing Fq k) : ℂ :=
  (if x ∈ U E then 1 else 0) * ∏ v ∈ T, φ v (x v)

/-- $\varphi_v$ is $\mathfrak p_v^{n_v}$-periodic on $\mathfrak r_v$ for $v\in T$. -/
def IsPeriodicOn (T : Finset (Place Fq k)) (φ : ∀ v : Place Fq k, v.Completion → ℂ) (n : Place Fq k → ℕ) : Prop :=
  ∀ v ∈ T, ∀ t ∈ v.pPow 0, ∀ p ∈ v.pPow (n v), φ v (t + p) = φ v t

/-- The divisor $n_T=\sum_{v\in T}n_v\,v$. -/
def nDiv (T : Finset (Place Fq k)) (n : Place Fq k → ℕ) : Divisor Fq k :=
  ∑ v ∈ T, ((n v : ℤ) • Finsupp.single v 1)

theorem nDiv_apply_of_mem {T : Finset (Place Fq k)} (n : Place Fq k → ℕ) {v : Place Fq k} (hv : v ∈ T) :
    nDiv T n v = n v := by
  classical
  rw [nDiv, Finsupp.finset_sum_apply, Finset.sum_eq_single v]
  · simp
  · intro w _ hw; simp [Finsupp.single_apply, hw]
  · intro h; exact absurd hv h

theorem nDiv_apply_of_not_mem {T : Finset (Place Fq k)} (n : Place Fq k → ℕ) {v : Place Fq k} (hv : v ∉ T) :
    nDiv T n v = 0 := by
  classical
  rw [nDiv, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun w hw => ?_
  have : w ≠ v := fun h => hv (h ▸ hw)
  simp [Finsupp.single_apply, this]

open Classical in
theorem nDiv_insert {T : Finset (Place Fq k)} (n : Place Fq k → ℕ) {v : Place Fq k} (hv : v ∉ T) :
    nDiv (insert v T) n = (n v : ℤ) • Finsupp.single v 1 + nDiv T n := by
  rw [nDiv, Finset.sum_insert hv, nDiv]

theorem nDiv_nonneg (T : Finset (Place Fq k)) (n : Place Fq k → ℕ) : 0 ≤ nDiv T n := fun w => by
  classical
  by_cases h : w ∈ T
  · rw [nDiv_apply_of_mem n h]; simp
  · rw [nDiv_apply_of_not_mem n h]; simp

open Classical in
/-- **Decomposition at a place**: $P(\{v\}\cup T,E)=\sum_{t\in R_v}\varphi_v(t)\,P(T,E-n_vv)(\cdot-\mathrm{single}_vt)$. -/
theorem prodFn_insert {T : Finset (Place Fq k)} {v : Place Fq k} (hv : v ∉ T) {E : Divisor Fq k} (hEv : E v = 0)
    {φ : ∀ v : Place Fq k, v.Completion → ℂ} {n : Place Fq k → ℕ} (hper : IsPeriodicOn (insert v T) φ n)
    (x : FFAdeleRing Fq k) :
    prodFn (insert v T) E φ x = ∑ t ∈ v.reps (n v), φ v t *
      prodFn T (E - (n v : ℤ) • Finsupp.single v 1) φ (x - single v t) := by
  have hcomp : ∀ (t : v.Completion) (w : Place Fq k), w ≠ v → (x - single v t) w = x w := fun t w hw => by
    show x w - single v t w = x w
    rw [single_apply_of_ne hw, sub_zero]
  have hprod : ∀ t : v.Completion, ∏ w ∈ T, φ w ((x - single v t) w) = ∏ w ∈ T, φ w (x w) := fun t =>
    Finset.prod_congr rfl fun w hw => by rw [hcomp t w (fun h => hv (h ▸ hw))]
  have hE' : ∀ w, w ≠ v → (E - (n v : ℤ) • Finsupp.single v (1 : ℤ) : Divisor Fq k) w = E w := fun w hw => by
    simp [Finsupp.single_apply, Ne.symm hw]
  have hEv' : (E - (n v : ℤ) • Finsupp.single v (1 : ℤ) : Divisor Fq k) v = -(n v : ℤ) := by simp [hEv]
  -- membership in `U (E - n_v v)` after translating
  have hmemU : ∀ t : v.Completion, x - single v t ∈ U (E - (n v : ℤ) • Finsupp.single v 1) ↔
      (∀ w, w ≠ v → Valued.v (x w) ≤ WithZero.exp (E w)) ∧ x v - t ∈ v.pPow (n v) := by
    intro t
    rw [mem_U_iff]
    constructor
    · intro h
      refine ⟨fun w hw => ?_, ?_⟩
      · have := h w; rwa [hcomp t w hw, hE' w hw] at this
      · have := h v
        rw [hEv'] at this
        show Valued.v (x v - t) ≤ _
        simpa [single_apply_same] using this
    · rintro ⟨h1, h2⟩ w
      by_cases hw : w = v
      · subst hw
        rw [hEv']
        show Valued.v (x w - single w t w) ≤ _
        rw [single_apply_same]; exact h2
      · rw [hcomp t w hw, hE' w hw]; exact h1 w hw
  unfold prodFn
  by_cases hx : x ∈ U E
  · have hxv : x v ∈ v.pPow 0 := by
      have := hx v; rw [hEv] at this; exact Place.mem_pPow.2 (by simpa using this)
    obtain ⟨t₀, ⟨ht₀, hxt₀⟩, huniq⟩ := v.existsUnique_reps (n v) hxv
    rw [Finset.sum_eq_single t₀]
    · rw [if_pos hx, if_pos ((hmemU t₀).2 ⟨fun w _ => hx w, hxt₀⟩), hprod, Finset.prod_insert hv]
      have := hper v (Finset.mem_insert_self v T) t₀ (v.mem_pPow_zero_of_mem_reps ht₀) _ hxt₀
      rw [add_sub_cancel] at this
      rw [this]; ring
    · intro t ht hne
      rw [if_neg (fun h => hne (huniq t ⟨ht, ((hmemU t).1 h).2⟩)), zero_mul, mul_zero]
    · intro h; exact absurd ht₀ h
  · rw [if_neg hx, zero_mul]
    symm
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [if_neg, zero_mul, mul_zero]
    intro h
    obtain ⟨h1, h2⟩ := (hmemU t).1 h
    apply hx
    intro w
    by_cases hw : w = v
    · subst hw
      rw [hEv]
      have := (w.pPow 0).add_mem (Place.pPow_anti (Nat.cast_nonneg _) h2) (w.mem_pPow_zero_of_mem_reps ht)
      rw [sub_add_cancel] at this
      simpa using Place.mem_pPow.1 this
    · exact h1 w hw

end FFAdeleRing

/-! ### Fourier transforms of the product functions -/

namespace FFAdeleRing

variable (ψ₀ : AddChar Fq Circle)

/-- An integrable function times a character: Schwartz–Bruhat functions are integrable against `χ(x y)`. -/
theorem IsSchwartzBruhat.integrable_mul_chi {Φ : FFAdeleRing Fq k → ℂ} (hΦ : IsSchwartzBruhat Φ)
    (y : FFAdeleRing Fq k) : Integrable (fun x => Φ x * (chiA ψ₀ (x * y) : ℂ)) (haar Fq k) := by
  obtain ⟨a, b, n, ρ, -, -, hdec⟩ := exists_decomp hΦ
  have : (fun x => Φ x * (chiA ψ₀ (x * y) : ℂ)) = fun x => ∑ i, Φ (ρ i) *
      (cosSet b (ρ i)).indicator (fun x => (chiA ψ₀ (x * y) : ℂ)) x := by
    ext x
    rw [hdec, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx : x ∈ cosSet b (ρ i)
    · simp [cosInd, Set.indicator_of_mem hx]
    · simp [cosInd, Set.indicator_of_notMem hx]
  rw [this]
  exact integrable_finset_sum _ fun i _ => (integrable_indicator_cont (isOpen_cosSet _ _) (isCompact_cosSet _ _)
    (continuous_chiA_mul ψ₀ y)).const_mul _

theorem IsSchwartzBruhat.sub_const {Φ : FFAdeleRing Fq k → ℂ} (hΦ : IsSchwartzBruhat Φ) {r : FFAdeleRing Fq k}
    {d : Divisor Fq k} (hr : r ∈ U d) : IsSchwartzBruhat fun x => Φ (x - r) := by
  obtain ⟨a, b, hs, hinv⟩ := hΦ
  refine ⟨a ⊔ d, b, fun x hx => hs _ fun h => hx ?_, fun x u hu => ?_⟩
  · have := (U (a ⊔ d)).add_mem (U_mono le_sup_left h) (U_mono le_sup_right hr)
    rwa [sub_add_cancel] at this
  · show Φ (x + u - r) = Φ (x - r)
    rw [add_sub_right_comm]; exact hinv _ _ hu

/-- **Fourier transform of a translate**: $\widehat{\Phi(\cdot-r)}(y)=\chi(ry)\hat\Phi(y)$. -/
theorem fourierFF_sub_const (Φ : FFAdeleRing Fq k → ℂ) (r y : FFAdeleRing Fq k) :
    fourierFF ψ₀ (fun x => Φ (x - r)) y = (chiA ψ₀ (r * y) : ℂ) * fourierFF ψ₀ Φ y := by
  unfold fourierFF
  rw [← integral_add_right_eq_self (fun x => Φ (x - r) * (chiA ψ₀ (x * y) : ℂ)) r, ← integral_const_mul]
  congr 1
  ext x
  rw [add_sub_cancel_right, add_mul, AddChar.map_add_eq_mul]
  push_cast
  ring

theorem fourierFF_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → FFAdeleRing Fq k → ℂ)
    (hF : ∀ i ∈ s, IsSchwartzBruhat (F i)) (y : FFAdeleRing Fq k) :
    fourierFF ψ₀ (fun x => ∑ i ∈ s, c i * F i x) y = ∑ i ∈ s, c i * fourierFF ψ₀ (F i) y := by
  unfold fourierFF
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum _ fun i hi => ((hF i hi).integrable_mul_chi ψ₀ y).const_mul (c i) |>.congr
    (Eventually.of_forall fun x => by simp only; ring)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_const_mul]
  congr 1; ext x; ring

end FFAdeleRing

namespace FFAdeleRing

variable (ψ₀ : AddChar Fq Circle)

theorem prodFn_isSchwartzBruhat {T : Finset (Place Fq k)} {E : Divisor Fq k} {φ : ∀ v : Place Fq k, v.Completion → ℂ}
    {n : Place Fq k → ℕ} (hper : IsPeriodicOn T φ n) (hE : ∀ v ∈ T, E v = 0) :
    IsSchwartzBruhat (prodFn T E φ) := by
  classical
  refine ⟨E, E - nDiv T n, fun x hx => by simp [prodFn, hx], fun x u hu => ?_⟩
  have huE : u ∈ U E := U_mono (sub_le_self _ (nDiv_nonneg T n)) hu
  unfold prodFn
  by_cases hx : x ∈ U E
  · have hxu : x + u ∈ U E := (U E).add_mem hx huE
    rw [if_pos hx, if_pos hxu]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    show φ v (x v + u v) = φ v (x v)
    refine hper v hv (x v) (Place.mem_pPow.2 ?_) (u v) (Place.mem_pPow.2 ?_)
    · have := hx v; rw [hE v hv] at this; simpa using this
    · have := hu v
      rw [Finsupp.sub_apply, hE v hv, nDiv_apply_of_mem n hv, zero_sub] at this
      exact this
  · have hxu : x + u ∉ U E := fun h => hx (by
      have := (U E).sub_mem h huE; rwa [add_sub_cancel_right] at this)
    rw [if_neg hx, if_neg hxu, zero_mul, zero_mul]

/-- **The Gauss sum modulo $\mathfrak p_v^m$**: $G(s)=\sum_{t\in\mathfrak r_v/\mathfrak p_v^m}\varphi(t)\chi_v(st)$. -/
def gaussL (v : Place Fq k) (φv : v.Completion → ℂ) (m : ℕ) (s : v.Completion) : ℂ :=
  ∑ t ∈ v.reps m, φv t * (chiA ψ₀ (single v (s * t)) : ℂ)

open Classical in
/-- **Fourier transform of a product function**:
$\hat P(T,E)(y)=\prod_{v\in T}G_v(y_v)\cdot q^{\deg E-\deg n_T}\cdot[y\in U(\mathfrak c-E+n_T)]$. -/
theorem fourierFF_prodFn (hψ₀ : ψ₀ ≠ 1) (φ : ∀ v : Place Fq k, v.Completion → ℂ) (n : Place Fq k → ℕ)
    (T : Finset (Place Fq k)) (hper : IsPeriodicOn T φ n) (E : Divisor Fq k) (hE : ∀ v ∈ T, E v = 0)
    (y : FFAdeleRing Fq k) :
    fourierFF ψ₀ (prodFn T E φ) y = (∏ v ∈ T, gaussL ψ₀ v (φ v) (n v) (y v)) *
      (Nat.card Fq : ℂ) ^ (Divisor.deg E - Divisor.deg (nDiv T n)) *
      (if y ∈ U (canonical Fq k - E + nDiv T n) then 1 else 0) := by
  induction T using Finset.induction_on generalizing E with
  | empty =>
    have h : prodFn ∅ E φ = (U E : Set (FFAdeleRing Fq k)).indicator 1 := by
      ext x
      by_cases hx : x ∈ U E
      · simp [prodFn, hx, Set.indicator_of_mem (show x ∈ (U E : Set (FFAdeleRing Fq k)) from hx)]
      · simp [prodFn, hx, Set.indicator_of_notMem (show x ∉ (U E : Set (FFAdeleRing Fq k)) from hx)]
    rw [h, fourierFF_indicator_U ψ₀ hψ₀]
    simp only [Finset.prod_empty, one_mul, nDiv, Finset.sum_empty, map_zero, sub_zero, add_zero]
    split_ifs <;> simp
  | insert v T hv ih =>
    have hEv : E v = 0 := hE v (Finset.mem_insert_self v T)
    set E' : Divisor Fq k := E - (n v : ℤ) • Finsupp.single v 1 with hE'
    have hE'T : ∀ w ∈ T, E' w = 0 := fun w hw => by
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      simp [hE', Finsupp.single_apply, Ne.symm hwv, hE w (Finset.mem_insert_of_mem hw)]
    have hperT : IsPeriodicOn T φ n := fun w hw => hper w (Finset.mem_insert_of_mem hw)
    have hfun : prodFn (insert v T) E φ = fun x => ∑ t ∈ v.reps (n v), φ v t *
        (fun t x => prodFn T E' φ (x - single v t)) t x := by
      ext x; exact prodFn_insert hv hEv hper x
    rw [hfun, fourierFF_finset_sum ψ₀ _ _ _ (fun t ht => (prodFn_isSchwartzBruhat hperT hE'T).sub_const
      (d := 0) ((single_mem_U_iff 0 v t).2 (by
        have := Place.mem_pPow.1 (v.mem_pPow_zero_of_mem_reps ht); simpa using this)))]
    simp_rw [fourierFF_sub_const, ih hperT E' hE'T]
    have hchi : ∀ t : v.Completion, chiA ψ₀ (single v t * y) = chiA ψ₀ (single v (y v * t)) := fun t => by
      rw [mul_comm, mul_single]
    simp_rw [hchi]
    rw [Finset.prod_insert hv, nDiv_insert n hv, gaussL]
    have hdeg : Divisor.deg E' - Divisor.deg (nDiv T n) =
        Divisor.deg E - Divisor.deg ((n v : ℤ) • Finsupp.single v 1 + nDiv T n) := by
      rw [hE', map_sub, map_add]; ring
    have hdiv : canonical Fq k - E' + nDiv T n = canonical Fq k - E + ((n v : ℤ) • Finsupp.single v 1 + nDiv T n) := by
      rw [hE']; abel
    rw [hdeg, hdiv, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring

end FFAdeleRing

/-! ### Weil's local functions $\varphi_v=\omega_v^{-1}$ on $\mathfrak r_v^\times$ -/

namespace FFHeckeCharacter

theorem ne_zero_of_valued_eq_one {v : Place Fq k} {t : v.Completion} (h : Valued.v t = 1) : t ≠ 0 := by
  rintro rfl; simp at h

/-- $\varphi_v(t)=\omega_v(t)^{-1}$ for $t\in\mathfrak r_v^\times$ and $0$ otherwise (Weil VII.§7, p. 131). -/
def phiLoc (ω : FFHeckeCharacter Fq k) (v : Place Fq k) (t : v.Completion) : ℂ :=
  if h : Valued.v t = 1 then (((ω.component v (Units.mk0 t (ne_zero_of_valued_eq_one h)))⁻¹ : ℂˣ) : ℂ) else 0

variable (ω : FFHeckeCharacter Fq k)

theorem phiLoc_unit (v : Place Fq k) (u : v.Completionˣ) (hu : Valued.v (u : v.Completion) = 1) :
    ω.phiLoc v u = (((ω.component v u)⁻¹ : ℂˣ) : ℂ) := by
  rw [phiLoc, dif_pos hu]
  congr 3
  exact Units.ext rfl

theorem phiLoc_of_ne (v : Place Fq k) {t : v.Completion} (h : Valued.v t ≠ 1) : ω.phiLoc v t = 0 := by
  rw [phiLoc, dif_neg h]

theorem phiLoc_mul_unit (v : Place Fq k) (t : v.Completion) (ε : v.Completionˣ)
    (hε : Valued.v (ε : v.Completion) = 1) :
    ω.phiLoc v (t * ε) = (((ω.component v ε)⁻¹ : ℂˣ) : ℂ) * ω.phiLoc v t := by
  by_cases ht : Valued.v t = 1
  · have ht' : Valued.v (t * ε) = 1 := by rw [map_mul, ht, hε, one_mul]
    have e : Units.mk0 (t * ε) (ne_zero_of_valued_eq_one ht') =
        Units.mk0 t (ne_zero_of_valued_eq_one ht) * ε := Units.ext rfl
    rw [phiLoc, dif_pos ht', phiLoc, dif_pos ht, e, map_mul, mul_inv, Units.val_mul, mul_comm]
  · have ht' : Valued.v (t * ε) ≠ 1 := by rwa [map_mul, hε, mul_one]
    rw [phiLoc_of_ne ω v ht, phiLoc_of_ne ω v ht', mul_zero]

theorem phiLoc_one (v : Place Fq k) : ω.phiLoc v 1 = 1 := by
  have := ω.phiLoc_unit v 1 (by simp)
  rw [map_one, inv_one, Units.val_one] at this
  exact this

/-- $\varphi_v$ is $\mathfrak p_v^{f(v)}$-periodic on $\mathfrak r_v$ when $f(v)\ge1$. -/
theorem phiLoc_periodic {v : Place Fq k} (hf : 0 < ω.conductorExponent v) {t : v.Completion}
    (ht : t ∈ v.pPow 0) {p : v.Completion} (hp : p ∈ v.pPow (ω.conductorExponent v)) :
    ω.phiLoc v (t + p) = ω.phiLoc v t := by
  have hp1 : Valued.v p < 1 := lt_of_le_of_lt (Place.mem_pPow.1 hp)
    (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  by_cases hunit : Valued.v t = 1
  · have ht0 := ne_zero_of_valued_eq_one hunit
    set ε : v.Completion := 1 + p * t⁻¹ with hεdef
    have hε1 : Valued.v (ε - 1) = Valued.v p := by
      rw [hεdef, add_sub_cancel_left, map_mul, map_inv₀, hunit, inv_one, mul_one]
    have hεv : Valued.v ε = 1 := by
      rw [hεdef, Valuation.map_add_eq_of_lt_left]
      · simp
      · rw [map_mul, map_inv₀, hunit, inv_one, mul_one, map_one]; exact hp1
    have hε0 : ε ≠ 0 := ne_zero_of_valued_eq_one hεv
    have hmem : Units.mk0 ε hε0 ∈ unitFiltration v (ω.conductorExponent v) :=
      ⟨hεv, by rw [Units.val_mk0, hε1]; exact Place.mem_pPow.1 hp⟩
    have htp : t + p = t * (Units.mk0 ε hε0 : v.Completion) := by
      rw [Units.val_mk0, hεdef, mul_add, mul_one, mul_comm p, ← mul_assoc, mul_inv_cancel₀ ht0, one_mul]
    rw [htp, ω.phiLoc_mul_unit v t _ (by rw [Units.val_mk0]; exact hεv), ω.component_eq_one_of_mem hmem,
      inv_one, Units.val_one, one_mul]
  · have ht1 : Valued.v t < 1 := lt_of_le_of_ne (by simpa using Place.mem_pPow.1 ht) hunit
    have htp : Valued.v (t + p) ≠ 1 := ne_of_lt (lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ht1 hp1))
    rw [ω.phiLoc_of_ne v hunit, ω.phiLoc_of_ne v htp]

/-- The places where $\omega$ is ramified. -/
def ramSet : Finset (Place Fq k) := ω.conductor.support

theorem mem_ramSet {v : Place Fq k} : v ∈ ω.ramSet ↔ 0 < ω.conductorExponent v := by
  rw [ramSet, Finsupp.mem_support_iff, conductor_apply]; omega

theorem isPeriodicOn_phiLoc {T : Finset (Place Fq k)} (hT : T ⊆ ω.ramSet) :
    FFAdeleRing.IsPeriodicOn T ω.phiLoc ω.conductorExponent := fun v hv t ht p hp =>
  ω.phiLoc_periodic ((ω.mem_ramSet).1 (hT hv)) ht hp

theorem nDiv_ramSet : FFAdeleRing.nDiv ω.ramSet ω.conductorExponent = ω.conductor := by
  ext v
  by_cases hv : v ∈ ω.ramSet
  · rw [FFAdeleRing.nDiv_apply_of_mem _ hv, conductor_apply]
  · rw [FFAdeleRing.nDiv_apply_of_not_mem _ hv, conductor_apply]
    have := (not_congr (ω.mem_ramSet)).1 hv
    omega

/-- **Weil's standard function** $\Phi_\omega=\bigotimes_v\Phi_v$ (VII.§7, p. 131): $\mathbf 1_{\mathfrak r_v}$ at the
unramified places, $\omega_v^{-1}$ on $\mathfrak r_v^\times$ (and $0$ elsewhere) at the ramified ones. -/
def stdPhi : FFAdeleRing Fq k → ℂ := FFAdeleRing.prodFn ω.ramSet 0 ω.phiLoc

end FFHeckeCharacter

/-! ### Equivariance and the vanishing of the Gauss sums -/

namespace FFHeckeCharacter

variable (ψ₀ : AddChar Fq Circle) (ω : FFHeckeCharacter Fq k)

theorem div_single_unit {v : Place Fq k} {ε : v.Completionˣ} (hε : Valued.v (ε : v.Completion) = 1) :
    FFIdeleGroup.div (FFIdeleGroup.single v ε) = 0 := by
  rw [FFIdeleGroup.div_single]
  simp [Place.ordC, hε]

open Classical in
theorem prodFn_mul_single_unit {T : Finset (Place Fq k)} {v : Place Fq k} (hv : v ∈ T) (ε : v.Completionˣ)
    (hε : Valued.v (ε : v.Completion) = 1) (x : FFAdeleRing Fq k) :
    FFAdeleRing.prodFn T 0 ω.phiLoc (x * ((FFIdeleGroup.single v ε⁻¹ : FFIdeleGroup Fq k) : FFAdeleRing Fq k)) =
      ((ω.component v ε : ℂˣ) : ℂ) * FFAdeleRing.prodFn T 0 ω.phiLoc x := by
  have hεi : Valued.v ((ε⁻¹ : v.Completionˣ) : v.Completion) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hε, inv_one]
  set z := FFIdeleGroup.single v ε⁻¹
  have hU : x * (z : FFAdeleRing Fq k) ∈ U 0 ↔ x ∈ U 0 := by
    rw [FFAdeleRing.mul_mem_U_iff, div_single_unit hεi, add_zero]
  have hcomp : ∀ w, w ≠ v → (x * (z : FFAdeleRing Fq k)) w = x w := fun w hw => by
    show x w * FFIdeleGroup.comp z w = x w
    rw [FFIdeleGroup.comp_single_ne hw, mul_one]
  have hcompv : (x * (z : FFAdeleRing Fq k)) v = x v * ((ε⁻¹ : v.Completionˣ) : v.Completion) := by
    show x v * FFIdeleGroup.comp z v = _
    rw [FFIdeleGroup.comp_single_self]
  unfold FFAdeleRing.prodFn
  rw [← Finset.mul_prod_erase T _ hv, ← Finset.mul_prod_erase T _ hv, hcompv,
    ω.phiLoc_mul_unit v _ _ hεi, map_inv, inv_inv]
  rw [Finset.prod_congr rfl fun w hw => by rw [hcomp w (Finset.ne_of_mem_erase hw)]]
  by_cases hx : x ∈ U 0
  · rw [if_pos (hU.2 hx), if_pos hx]; ring
  · rw [if_neg (fun h => hx (hU.1 h)), if_neg hx]; ring

/-- **Equivariance of the Fourier transform** under the units at a ramified place:
$\hat P(y\varepsilon)=\omega_v(\varepsilon)\hat P(y)$ for $\varepsilon\in\mathfrak r_v^\times$. -/
theorem fourierFF_prodFn_mul_single_unit (hψ₀ : ψ₀ ≠ 1) {T : Finset (Place Fq k)} (hT : T ⊆ ω.ramSet)
    {v : Place Fq k} (hv : v ∈ T) (ε : v.Completionˣ) (hε : Valued.v (ε : v.Completion) = 1)
    (y : FFAdeleRing Fq k) :
    fourierFF ψ₀ (FFAdeleRing.prodFn T 0 ω.phiLoc)
        (y * ((FFIdeleGroup.single v ε : FFIdeleGroup Fq k) : FFAdeleRing Fq k)) =
      ((ω.component v ε : ℂˣ) : ℂ) * fourierFF ψ₀ (FFAdeleRing.prodFn T 0 ω.phiLoc) y := by
  have hSB := FFAdeleRing.prodFn_isSchwartzBruhat (ω.isPeriodicOn_phiLoc hT) (E := 0) (fun _ _ => rfl)
  have hεi : Valued.v ((ε⁻¹ : v.Completionˣ) : v.Completion) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hε, inv_one]
  have h := FFAdeleRing.fourierFF_mulRight ψ₀ hψ₀ hSB (FFIdeleGroup.single v ε⁻¹) y
  have hinvz : (FFIdeleGroup.single v ε⁻¹)⁻¹ = FFIdeleGroup.single (Fq := Fq) (k := k) v ε := by
    rw [inv_eq_iff_mul_eq_one, ← FFIdeleGroup.single_mul, inv_mul_cancel, FFIdeleGroup.single_one]
  rw [div_single_unit hεi, map_zero, zpow_zero, one_mul, hinvz] at h
  rw [← h]
  have hfun : (fun x => FFAdeleRing.prodFn T 0 ω.phiLoc
      (x * ((FFIdeleGroup.single v ε⁻¹ : FFIdeleGroup Fq k) : FFAdeleRing Fq k))) =
      fun x => ((ω.component v ε : ℂˣ) : ℂ) * FFAdeleRing.prodFn T 0 ω.phiLoc x :=
    funext (ω.prodFn_mul_single_unit hv ε hε)
  rw [hfun, FFAdeleRing.fourierFF_const_mul]

end FFHeckeCharacter

namespace FFHeckeCharacter

variable (ψ₀ : AddChar Fq Circle) (ω : FFHeckeCharacter Fq k)

/-- The local Gauss sum $G_v(s)=\sum_{t\in\mathfrak r_v/\mathfrak p_v^{f(v)}}\omega_v(t)^{-1}\chi_v(st)$ (sum over units). -/
def gaussV (v : Place Fq k) (s : v.Completion) : ℂ :=
  FFAdeleRing.gaussL ψ₀ v (ω.phiLoc v) (ω.conductorExponent v) s

open Classical in
theorem fourierFF_single_place (hψ₀ : ψ₀ ≠ 1) {v : Place Fq k} (hv : v ∈ ω.ramSet) (y : FFAdeleRing Fq k) :
    fourierFF ψ₀ (FFAdeleRing.prodFn {v} 0 ω.phiLoc) y = ω.gaussV ψ₀ v (y v) *
      (Nat.card Fq : ℂ) ^ (-((ω.conductorExponent v : ℤ) * v.degree)) *
      (if y ∈ U (canonical Fq k + (ω.conductorExponent v : ℤ) • Finsupp.single v 1) then 1 else 0) := by
  rw [FFAdeleRing.fourierFF_prodFn ψ₀ hψ₀ ω.phiLoc ω.conductorExponent {v}
    (ω.isPeriodicOn_phiLoc (Finset.singleton_subset_iff.2 hv)) 0 (fun _ _ => rfl) y]
  simp only [Finset.prod_singleton, FFAdeleRing.nDiv, Finset.sum_singleton, map_zero, zero_sub, sub_zero,
    map_zsmul, Divisor.deg_single, smul_eq_mul, one_mul, gaussV]

theorem single_mul_single_unit (v : Place Fq k) (s : v.Completion) (ε : v.Completionˣ) :
    FFAdeleRing.single v s * ((FFIdeleGroup.single v ε : FFIdeleGroup Fq k) : FFAdeleRing Fq k) =
      FFAdeleRing.single v (s * ε) := by
  rw [mul_comm, FFAdeleRing.mul_single]
  congr 1
  rw [mul_comm]
  congr 1
  exact FFIdeleGroup.comp_single_self v ε

theorem single_mem_U_cf {v : Place Fq k} {s : v.Completion} {m : ℤ} (hs : Valued.v s ≤ WithZero.exp (canonical Fq k v + m)) :
    FFAdeleRing.single v s ∈ U (canonical Fq k + m • Finsupp.single v 1) := by
  rw [single_mem_U_iff]; simpa using hs

/-- **Equivariance of the local Gauss sum**: $G_v(s\varepsilon)=\omega_v(\varepsilon)G_v(s)$ for $\varepsilon\in\mathfrak r_v^\times$
and $s\in\mathfrak p_v^{-\mathfrak c(v)-f(v)}$. -/
theorem gaussV_mul_unit (hψ₀ : ψ₀ ≠ 1) {v : Place Fq k} (hv : v ∈ ω.ramSet) {s : v.Completion}
    (hs : Valued.v s ≤ WithZero.exp (canonical Fq k v + ω.conductorExponent v)) (ε : v.Completionˣ)
    (hε : Valued.v (ε : v.Completion) = 1) :
    ω.gaussV ψ₀ v (s * ε) = ((ω.component v ε : ℂˣ) : ℂ) * ω.gaussV ψ₀ v s := by
  have h := ω.fourierFF_prodFn_mul_single_unit ψ₀ hψ₀ (Finset.singleton_subset_iff.2 hv)
    (Finset.mem_singleton_self v) ε hε (FFAdeleRing.single v s)
  rw [single_mul_single_unit, fourierFF_single_place ψ₀ ω hψ₀ hv, fourierFF_single_place ψ₀ ω hψ₀ hv,
    if_pos (single_mem_U_cf hs), if_pos (single_mem_U_cf (by rwa [map_mul, hε, mul_one])),
    FFAdeleRing.single_apply_same, FFAdeleRing.single_apply_same] at h
  have hq : (Nat.card Fq : ℂ) ^ (-((ω.conductorExponent v : ℤ) * v.degree)) ≠ 0 :=
    zpow_ne_zero _ (by have := Nat.card_pos (α := Fq); exact_mod_cast this.ne')
  rw [mul_one, mul_one, ← mul_assoc] at h
  exact mul_right_cancel₀ hq h

/-- **The Gauss sum vanishes off the exact order**: $G_v(s)=0$ for $s\in\mathfrak p_v^{1-\mathfrak c(v)-f(v)}$ (the
character $\omega_v$ is nontrivial on $1+\mathfrak p_v^{f(v)-1}$, by minimality of the conductor). -/
theorem gaussV_eq_zero (hψ₀ : ψ₀ ≠ 1) {v : Place Fq k} (hv : v ∈ ω.ramSet) {s : v.Completion}
    (hs : Valued.v s ≤ WithZero.exp (canonical Fq k v + ω.conductorExponent v - 1)) : ω.gaussV ψ₀ v s = 0 := by
  have hf := (ω.mem_ramSet).1 hv
  obtain ⟨ε, hεmem, hεne⟩ : ∃ ε ∈ unitFiltration v (ω.conductorExponent v - 1), ω.component v ε ≠ 1 := by
    by_contra h
    push Not at h
    have := (ω.conductorExponent_le_iff v _).2 h
    omega
  have hε1 : Valued.v (ε : v.Completion) = 1 := hεmem.1
  have hs' : Valued.v s ≤ WithZero.exp (canonical Fq k v + ω.conductorExponent v) :=
    hs.trans (WithZero.exp_le_exp.2 (by omega))
  have heq : ω.gaussV ψ₀ v (s * ε) = ω.gaussV ψ₀ v s := by
    unfold gaussV FFAdeleRing.gaussL
    refine Finset.sum_congr rfl fun t ht => ?_
    congr 1
    have htv : Valued.v t ≤ 1 := by simpa using Place.mem_pPow.1 (v.mem_pPow_zero_of_mem_reps ht)
    have hsplit : s * ε * t = s * t + s * ((ε : v.Completion) - 1) * t := by ring
    rw [hsplit, FFAdeleRing.single_add, AddChar.map_add_eq_mul,
      (weil_IV_2_thm3_cor1_ff_order ψ₀ hψ₀ v).1 (s * ((ε : v.Completion) - 1) * t) ?_, mul_one]
    rw [map_mul, map_mul]
    have h2 := hεmem.2
    calc Valued.v s * Valued.v ((ε : v.Completion) - 1) * Valued.v t
        ≤ WithZero.exp (canonical Fq k v + ω.conductorExponent v - 1) *
            WithZero.exp (-((ω.conductorExponent v - 1 : ℕ) : ℤ)) * 1 :=
          mul_le_mul' (mul_le_mul' hs h2) htv
      _ = WithZero.exp (canonical Fq k v) := by
          have hc : ((ω.conductorExponent v - 1 : ℕ) : ℤ) = ω.conductorExponent v - 1 := by omega
          rw [mul_one, ← WithZero.exp_add, hc]; congr 1; ring
  rw [gaussV_mul_unit ψ₀ ω hψ₀ hv hs' ε hε1] at heq
  have h2 : (((ω.component v ε : ℂˣ) : ℂ) - 1) * ω.gaussV ψ₀ v s = 0 := by rw [sub_mul, heq, one_mul, sub_self]
  refine (mul_eq_zero.1 h2).resolve_left fun h => hεne (Units.ext ?_)
  simpa [sub_eq_zero] using h

end FFHeckeCharacter

/-! ### Weil VII.§7 Prop. 14: the Fourier transform of $\Phi_\omega$ -/

namespace FFHeckeCharacter

variable (ψ₀ : AddChar Fq Circle) (ω : FFHeckeCharacter Fq k)

theorem component_inv (v : Place Fq k) (u : v.Completionˣ) : (ω⁻¹).component v u = (ω.component v u)⁻¹ := rfl

theorem conductorExponent_inv (v : Place Fq k) : (ω⁻¹).conductorExponent v = ω.conductorExponent v := by
  unfold conductorExponent
  congr 1
  ext n
  simp only [Set.mem_setOf_eq, component_inv, inv_eq_one]

theorem ramSet_inv : (ω⁻¹).ramSet = ω.ramSet := by
  ext v; rw [mem_ramSet, mem_ramSet, conductorExponent_inv]

theorem conductor_inv : (ω⁻¹).conductor = ω.conductor := by
  ext v; rw [conductor_apply, conductor_apply, conductorExponent_inv]

theorem phiLoc_inv_unit (v : Place Fq k) (u : v.Completionˣ) (hu : Valued.v (u : v.Completion) = 1) :
    (ω⁻¹).phiLoc v u = ((ω.component v u : ℂˣ) : ℂ) := by
  rw [phiLoc_unit _ v u hu, component_inv, inv_inv]

/-- $b_v=\pi_v^{\mathfrak c(v)+f(v)}$, the $v$-component of the idele $b=\pi^{\mathfrak c+\mathfrak f}$. -/
def bLoc (v : Place Fq k) : v.Completionˣ := FFIdeleGroup.unif v ^ (canonical Fq k v + ω.conductorExponent v)

theorem valued_bLoc (v : Place Fq k) :
    Valued.v (ω.bLoc v : v.Completion) = WithZero.exp (-(canonical Fq k v + ω.conductorExponent v)) :=
  FFIdeleGroup.valued_unif_zpow v _

theorem valued_bLoc_inv (v : Place Fq k) :
    Valued.v (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion) =
      WithZero.exp (canonical Fq k v + ω.conductorExponent v) := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, valued_bLoc, ← WithZero.exp_neg, neg_neg]

/-- **The Gauss sum on the exact order**: for $s\in\mathfrak p_v^{-\mathfrak c(v)-f(v)}$,
$G_v(s)=G_v(b_v^{-1})\,\Phi_{\omega^{-1},v}(b_vs)$, i.e. $G_v(s)=G_v(b_v^{-1})\omega_v(b_vs)$ if $b_vs$ is a unit and $0$
otherwise. -/
theorem gaussV_eq (hψ₀ : ψ₀ ≠ 1) {v : Place Fq k} (hv : v ∈ ω.ramSet) {s : v.Completion}
    (hs : Valued.v s ≤ WithZero.exp (canonical Fq k v + ω.conductorExponent v)) :
    ω.gaussV ψ₀ v s = ω.gaussV ψ₀ v (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion) *
      (ω⁻¹).phiLoc v ((ω.bLoc v : v.Completion) * s) := by
  by_cases hu : Valued.v ((ω.bLoc v : v.Completion) * s) = 1
  · set ε : v.Completionˣ := Units.mk0 _ (ne_zero_of_valued_eq_one hu)
    have hsε : s = (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion) * ε := by
      rw [Units.val_mk0, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [show (ω.bLoc v : v.Completion) * s = (ε : v.Completion) from (Units.val_mk0 _).symm,
      phiLoc_inv_unit _ v ε (by rw [Units.val_mk0]; exact hu)]
    conv_lhs => rw [hsε]
    rw [gaussV_mul_unit ψ₀ ω hψ₀ hv (le_of_eq (valued_bLoc_inv ω v)) ε (by rw [Units.val_mk0]; exact hu)]
    ring
  · rw [phiLoc_of_ne _ v hu, mul_zero]
    refine gaussV_eq_zero ψ₀ ω hψ₀ hv ?_
    have hle : Valued.v ((ω.bLoc v : v.Completion) * s) ≤ 1 := by
      rw [map_mul, valued_bLoc]
      calc WithZero.exp (-(canonical Fq k v + ω.conductorExponent v)) * Valued.v s
          ≤ WithZero.exp (-(canonical Fq k v + ω.conductorExponent v)) *
              WithZero.exp (canonical Fq k v + ω.conductorExponent v) := mul_le_mul' le_rfl hs
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    have hlt : Valued.v ((ω.bLoc v : v.Completion) * s) < 1 := lt_of_le_of_ne hle hu
    have hlt' : Valued.v ((ω.bLoc v : v.Completion) * s) ≤ WithZero.exp (-1) :=
      (Place.lt_one_iff_le_exp_neg_one _).1 hlt
    rw [map_mul, valued_bLoc] at hlt'
    have hs0 : Valued.v s = WithZero.exp (canonical Fq k v + ω.conductorExponent v) *
        (WithZero.exp (-(canonical Fq k v + ω.conductorExponent v)) * Valued.v s) := by
      rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]
    rw [hs0]
    calc WithZero.exp (canonical Fq k v + ω.conductorExponent v) *
          (WithZero.exp (-(canonical Fq k v + ω.conductorExponent v)) * Valued.v s)
        ≤ WithZero.exp (canonical Fq k v + ω.conductorExponent v) * WithZero.exp (-1) := mul_le_mul' le_rfl hlt'
      _ = WithZero.exp (canonical Fq k v + ω.conductorExponent v - 1) := by
          rw [← WithZero.exp_add]; rfl

/-- The idele $b=\pi^{\mathfrak c+\mathfrak f}$. -/
def bIdele : FFIdeleGroup Fq k := FFIdeleGroup.piD (canonical Fq k + ω.conductor)

theorem comp_bIdele (v : Place Fq k) : FFIdeleGroup.comp ω.bIdele v = (ω.bLoc v : v.Completion) := by
  rw [bIdele, FFIdeleGroup.comp_piD, bLoc, Finsupp.add_apply, conductor_apply]

/-- The idele $b_T=\pi^{\mathfrak c+f_T}$ for a set $T$ of ramified places. -/
def bT (T : Finset (Place Fq k)) : FFIdeleGroup Fq k :=
  FFIdeleGroup.piD (canonical Fq k + FFAdeleRing.nDiv T ω.conductorExponent)

theorem comp_bT {T : Finset (Place Fq k)} {v : Place Fq k} (hv : v ∈ T) :
    FFIdeleGroup.comp (ω.bT T) v = (ω.bLoc v : v.Completion) := by
  rw [bT, FFIdeleGroup.comp_piD, bLoc, Finsupp.add_apply, FFAdeleRing.nDiv_apply_of_mem _ hv]

open Classical in
/-- **The Fourier transform of $P(T,0)$ for ramified places** (Weil VII.§7 Prop. 13–14):
$\hat P_\omega(y)=\Big(\prod_{v\in T}G_v(b_v^{-1})\Big)q^{-\deg f_T}P_{\omega^{-1}}(yb_T)$. -/
theorem fourierFF_prodFn_ram (hψ₀ : ψ₀ ≠ 1) {T : Finset (Place Fq k)} (hT : T ⊆ ω.ramSet) (y : FFAdeleRing Fq k) :
    fourierFF ψ₀ (FFAdeleRing.prodFn T 0 ω.phiLoc) y =
      (∏ v ∈ T, ω.gaussV ψ₀ v (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion)) *
      (Nat.card Fq : ℂ) ^ (-Divisor.deg (FFAdeleRing.nDiv T ω.conductorExponent)) *
      FFAdeleRing.prodFn T 0 (ω⁻¹).phiLoc (y * (ω.bT T : FFAdeleRing Fq k)) := by
  rw [FFAdeleRing.fourierFF_prodFn ψ₀ hψ₀ ω.phiLoc ω.conductorExponent T
    (ω.isPeriodicOn_phiLoc hT) 0 (fun _ _ => rfl) y]
  unfold FFAdeleRing.prodFn
  rw [map_zero, zero_sub, sub_zero, FFAdeleRing.mul_mem_U_iff, bT, FFIdeleGroup.div_piD, zero_add]
  by_cases hy : y ∈ U (canonical Fq k + FFAdeleRing.nDiv T ω.conductorExponent)
  · rw [if_pos hy, one_mul, mul_one, ← bT]
    have : ∀ v ∈ T, ω.gaussV ψ₀ v (y v) =
        ω.gaussV ψ₀ v (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion) *
          (ω⁻¹).phiLoc v ((y * (ω.bT T : FFAdeleRing Fq k)) v) := fun v hv => by
      rw [show (y * (ω.bT T : FFAdeleRing Fq k)) v = y v * FFIdeleGroup.comp (ω.bT T) v from rfl,
        comp_bT ω hv, mul_comm (y v)]
      refine gaussV_eq ψ₀ ω hψ₀ (hT hv) ?_
      have := hy v
      rwa [Finsupp.add_apply, FFAdeleRing.nDiv_apply_of_mem _ hv] at this
    simp only [gaussV] at this ⊢
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib]
    ring
  · rw [if_neg hy, mul_zero, zero_mul, mul_zero]

theorem bT_ramSet : ω.bT ω.ramSet = ω.bIdele := by rw [bT, nDiv_ramSet, bIdele]

/-- **Weil VII.§7 Prop. 14, function fields (Fourier transform for $\mu_1$)**:
$\hat\Phi_\omega(y)=\Big(\prod_{v\in S}G_v(b_v^{-1})\Big)\,q^{-\deg\mathfrak f}\,\Phi_{\omega^{-1}}(by)$, $S$ the ramified
places and $b=\pi^{\mathfrak c+\mathfrak f}$. -/
theorem fourierFF_stdPhi (hψ₀ : ψ₀ ≠ 1) (y : FFAdeleRing Fq k) :
    fourierFF ψ₀ ω.stdPhi y = (∏ v ∈ ω.ramSet, ω.gaussV ψ₀ v (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion)) *
      (Nat.card Fq : ℂ) ^ (-Divisor.deg ω.conductor) * (ω⁻¹).stdPhi (y * (ω.bIdele : FFAdeleRing Fq k)) := by
  rw [stdPhi, fourierFF_prodFn_ram ψ₀ ω hψ₀ subset_rfl, nDiv_ramSet, bT_ramSet, stdPhi, ramSet_inv]

end FFHeckeCharacter

/-! ### The local constants have absolute value one -/

namespace FFHeckeCharacter

variable (ψ₀ : AddChar Fq Circle) (ω : FFHeckeCharacter Fq k)

theorem bLoc_inv (v : Place Fq k) : (ω⁻¹).bLoc v = ω.bLoc v := by
  rw [bLoc, bLoc, conductorExponent_inv]

theorem bT_inv (T : Finset (Place Fq k)) : (ω⁻¹).bT T = ω.bT T := by
  rw [bT, bT]
  congr 3
  ext v; simp [conductorExponent_inv]

theorem single_mem_integralUnits {v : Place Fq k} {u : v.Completionˣ} (hu : Valued.v (u : v.Completion) = 1) :
    FFIdeleGroup.single v u ∈ FFIdeleGroup.integralUnits := by
  rw [FFIdeleGroup.mem_integralUnits_iff_div]; exact div_single_unit hu

theorem norm_component {v : Place Fq k} {u : v.Completionˣ} (hu : Valued.v (u : v.Completion) = 1) :
    ‖((ω.component v u : ℂˣ) : ℂ)‖ = 1 :=
  ω.norm_ev_of_mem (single_mem_integralUnits hu)

theorem conj_phiLoc (v : Place Fq k) (t : v.Completion) :
    (starRingEnd ℂ) (ω.phiLoc v t) = (ω⁻¹).phiLoc v t := by
  by_cases ht : Valued.v t = 1
  · set u : v.Completionˣ := Units.mk0 t (ne_zero_of_valued_eq_one ht)
    have hu : Valued.v (u : v.Completion) = 1 := ht
    rw [show t = (u : v.Completion) from rfl, phiLoc_unit _ v u hu, phiLoc_inv_unit _ v u hu,
      Units.val_inv_eq_inv_val, map_inv₀]
    have hn := ω.norm_component hu
    set z : ℂ := ((ω.component v u : ℂˣ) : ℂ)
    have hz : z ≠ 0 := by rintro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
    have hc : (starRingEnd ℂ) z = z⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn, one_pow, inv_one, Complex.ofReal_one, mul_one]
    rw [hc, inv_inv]
  · rw [phiLoc_of_ne _ v ht, phiLoc_of_ne _ v ht, map_zero]

/-- $\overline{G_v^{\omega}(s)}=G_v^{\omega^{-1}}(-s)$. -/
theorem conj_gaussV (v : Place Fq k) (s : v.Completion) :
    (starRingEnd ℂ) (ω.gaussV ψ₀ v s) = (ω⁻¹).gaussV ψ₀ v (-s) := by
  unfold gaussV FFAdeleRing.gaussL
  rw [map_sum, conductorExponent_inv]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, conj_phiLoc, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_mul]
  congr 3
  rw [neg_eq_zero_sub, ← FFAdeleRing.single_zero' v, ← FFAdeleRing.single_sub', zero_sub]

end FFHeckeCharacter

namespace FFHeckeCharacter

variable (ψ₀ : AddChar Fq Circle) (ω : FFHeckeCharacter Fq k)

theorem nDiv_inv (T : Finset (Place Fq k)) :
    FFAdeleRing.nDiv T (ω⁻¹).conductorExponent = FFAdeleRing.nDiv T ω.conductorExponent := by
  unfold FFAdeleRing.nDiv; simp_rw [conductorExponent_inv]

open Classical in
theorem prodFn_single_place_apply (φ : ∀ v : Place Fq k, v.Completion → ℂ) (v : Place Fq k)
    (x : FFAdeleRing Fq k) (hx : x ∈ U 0) : FFAdeleRing.prodFn {v} 0 φ x = φ v (x v) := by
  rw [FFAdeleRing.prodFn, if_pos hx, one_mul, Finset.prod_singleton]

theorem one_mem_U_zero : (1 : FFAdeleRing Fq k) ∈ U 0 := fun v => by simp

theorem neg_one_mem_U_zero : (-1 : FFAdeleRing Fq k) ∈ U 0 := (U 0).neg_mem one_mem_U_zero

/-- **Fourier inversion for the single-place function**: $G_v^{\omega}(b_v^{-1})\,G_v^{\omega^{-1}}(b_v^{-1})=
q_v^{f(v)}\,\omega_v(-1)^{-1}$. -/
theorem gaussV_mul_gaussV_inv (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) {v : Place Fq k} (hv : v ∈ ω.ramSet) :
    ω.gaussV ψ₀ v (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion) *
      (ω⁻¹).gaussV ψ₀ v (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion) =
      (Nat.card Fq : ℂ) ^ ((ω.conductorExponent v : ℤ) * v.degree) *
        (((ω.component v (-1))⁻¹ : ℂˣ) : ℂ) := by
  classical
  have hT : ({v} : Finset (Place Fq k)) ⊆ ω.ramSet := Finset.singleton_subset_iff.2 hv
  have hT' : ({v} : Finset (Place Fq k)) ⊆ (ω⁻¹).ramSet := by rw [ramSet_inv]; exact hT
  have hΦ := FFAdeleRing.prodFn_isSchwartzBruhat (ω.isPeriodicOn_phiLoc hT) (E := 0) (fun _ _ => rfl)
  have hΨ := FFAdeleRing.prodFn_isSchwartzBruhat ((ω⁻¹).isPeriodicOn_phiLoc hT') (E := 0) (fun _ _ => rfl)
  have hdegb : Divisor.deg (FFIdeleGroup.div (ω.bT {v})) = (2 * Rep.genusInt Fq k - 2) +
      (ω.conductorExponent v : ℤ) * v.degree := by
    rw [bT, FFIdeleGroup.div_piD, map_add, (weil_VI_2_cor1 hc).1, FFAdeleRing.nDiv, Finset.sum_singleton,
      map_zsmul, Divisor.deg_single, smul_eq_mul, one_mul]
  have hQ : (Nat.card Fq : ℂ) ^ (-Divisor.deg (FFAdeleRing.nDiv {v} ω.conductorExponent)) =
      ((Nat.card Fq : ℂ) ^ ((ω.conductorExponent v : ℤ) * v.degree))⁻¹ := by
    rw [FFAdeleRing.nDiv, Finset.sum_singleton, map_zsmul, Divisor.deg_single, smul_eq_mul, one_mul, zpow_neg]
  have hii : (ω⁻¹)⁻¹ = ω := inv_inv ω
  set G := ω.gaussV ψ₀ v (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion)
  set G' := (ω⁻¹).gaussV ψ₀ v (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion)
  set Q := (Nat.card Fq : ℂ) ^ (-Divisor.deg (FFAdeleRing.nDiv {v} ω.conductorExponent))
  set b := ω.bT {v}
  have h1 : ∀ y, fourierFF ψ₀ (FFAdeleRing.prodFn {v} 0 ω.phiLoc) y =
      G * Q * FFAdeleRing.prodFn {v} 0 (ω⁻¹).phiLoc (y * (b : FFAdeleRing Fq k)) := fun y => by
    rw [fourierFF_prodFn_ram ψ₀ ω hψ₀ hT, Finset.prod_singleton]
  have h2 : ∀ y, fourierFF ψ₀ (FFAdeleRing.prodFn {v} 0 (ω⁻¹).phiLoc) y =
      G' * Q * FFAdeleRing.prodFn {v} 0 ω.phiLoc (y * (b : FFAdeleRing Fq k)) := fun y => by
    rw [fourierFF_prodFn_ram ψ₀ ω⁻¹ hψ₀ hT', Finset.prod_singleton, hii, bLoc_inv, nDiv_inv, bT_inv]
  have hinv := FFAdeleRing.fourierFF_fourierFF ψ₀ hc hψ₀ hΦ 1
  have hfun : fourierFF ψ₀ (FFAdeleRing.prodFn {v} 0 ω.phiLoc) =
      fun y => (G * Q) * FFAdeleRing.prodFn {v} 0 (ω⁻¹).phiLoc (y * (b : FFAdeleRing Fq k)) := funext h1
  rw [hfun, FFAdeleRing.fourierFF_const_mul, FFAdeleRing.fourierFF_mulRight ψ₀ hψ₀ hΨ, h2] at hinv
  have hbb : (1 : FFAdeleRing Fq k) * ((b⁻¹ : FFIdeleGroup Fq k) : FFAdeleRing Fq k) * (b : FFAdeleRing Fq k) = 1 := by
    rw [one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [hbb, prodFn_single_place_apply _ v _ one_mem_U_zero, prodFn_single_place_apply _ v _ neg_one_mem_U_zero,
    show ((1 : FFAdeleRing Fq k) v) = 1 from rfl, show ((-1 : FFAdeleRing Fq k) v) = -1 from rfl,
    phiLoc_one] at hinv
  have hm1 : ω.phiLoc v (-1) = (((ω.component v (-1))⁻¹ : ℂˣ) : ℂ) := by
    have := ω.phiLoc_unit v (-1) (by simp)
    simpa using this
  rw [hm1] at hinv
  rw [hdegb, hQ] at hinv
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := Fq); exact_mod_cast this.ne'
  rw [zpow_add₀ hq0] at hinv
  have hX : (Nat.card Fq : ℂ) ^ ((ω.conductorExponent v : ℤ) * v.degree) ≠ 0 := zpow_ne_zero _ hq0
  have hA : (Nat.card Fq : ℂ) ^ (2 * Rep.genusInt Fq k - 2) ≠ 0 := zpow_ne_zero _ hq0
  generalize (Nat.card Fq : ℂ) ^ ((ω.conductorExponent v : ℤ) * v.degree) = X at hinv hX ⊢
  generalize (Nat.card Fq : ℂ) ^ (2 * Rep.genusInt Fq k - 2) = A at hinv hA ⊢
  field_simp at hinv
  exact hinv

end FFHeckeCharacter

namespace FFHeckeCharacter

variable (ψ₀ : AddChar Fq Circle) (ω : FFHeckeCharacter Fq k)

theorem component_neg_one_sq (v : Place Fq k) : (ω.component v (-1)) ^ 2 = 1 := by
  rw [← map_pow, neg_one_sq, map_one]

/-- **$|G_v(b_v^{-1})|^2=q_v^{f(v)}$** for the Gauss sum modulo $\mathfrak p_v^{f(v)}$ ($q_v=q^{\deg v}$). -/
theorem norm_gaussV_sq (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) {v : Place Fq k} (hv : v ∈ ω.ramSet) :
    ‖ω.gaussV ψ₀ v (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion)‖ ^ 2 =
      (Nat.card Fq : ℝ) ^ ((ω.conductorExponent v : ℤ) * v.degree) := by
  have hprod := ω.gaussV_mul_gaussV_inv ψ₀ hc hψ₀ hv
  rw [Units.val_inv_eq_inv_val (ω.component v (-1))] at hprod
  set β := (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion)
  set G := ω.gaussV ψ₀ v β
  set G' := (ω⁻¹).gaussV ψ₀ v β
  set e : ℂ := ((ω.component v (-1) : ℂˣ) : ℂ)
  have he : e ^ 2 = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) (ω.component_neg_one_sq v)
    simpa [e] using this
  have he0 : e ≠ 0 := Units.ne_zero _
  have hconj : (starRingEnd ℂ) G = e⁻¹ * G' := by
    rw [conj_gaussV, show -β = β * ((-1 : v.Completionˣ) : v.Completion) by simp,
      gaussV_mul_unit ψ₀ ω⁻¹ hψ₀ (by rw [ramSet_inv]; exact hv)
        (by rw [conductorExponent_inv]; exact le_of_eq (valued_bLoc_inv ω v)) _ (by simp), component_inv,
      Units.val_inv_eq_inv_val (ω.component v (-1))]
  have hG' : G' = e * (starRingEnd ℂ) G := by rw [hconj]; field_simp
  rw [hG'] at hprod
  have hnorm : G * (starRingEnd ℂ) G = ((Nat.card Fq : ℂ) ^ ((ω.conductorExponent v : ℤ) * v.degree)) := by
    have h1 : e * (G * (starRingEnd ℂ) G) =
        ((Nat.card Fq : ℂ) ^ ((ω.conductorExponent v : ℤ) * v.degree)) * e⁻¹ := by
      linear_combination hprod
    calc G * (starRingEnd ℂ) G = e⁻¹ * (e * (G * (starRingEnd ℂ) G)) := by field_simp
      _ = e⁻¹ * (((Nat.card Fq : ℂ) ^ ((ω.conductorExponent v : ℤ) * v.degree)) * e⁻¹) := by rw [h1]
      _ = ((Nat.card Fq : ℂ) ^ ((ω.conductorExponent v : ℤ) * v.degree)) * (e ^ 2)⁻¹ := by ring
      _ = _ := by rw [he, inv_one, mul_one]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hnorm
  exact_mod_cast hnorm

/-- **Weil's local constant** $\kappa_v=q_v^{-f(v)/2}\,G_v(b_v^{-1})$ (VII.§7 Prop. 13–14). -/
def kappaV (v : Place Fq k) : ℂ :=
  ((((Nat.card Fq : ℝ) ^ (-(((ω.conductorExponent v : ℤ) * v.degree : ℤ) : ℝ) / 2)) : ℝ) : ℂ) *
    ω.gaussV ψ₀ v (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion)

/-- **$\kappa_v\bar\kappa_v=1$** (Weil VII.§7 Prop. 13). -/
theorem norm_kappaV (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) {v : Place Fq k} (hv : v ∈ ω.ramSet) :
    ‖ω.kappaV ψ₀ v‖ = 1 := by
  have hq0 : (0 : ℝ) < Nat.card Fq := by exact_mod_cast (Nat.card_pos (α := Fq))
  have hG := ω.norm_gaussV_sq ψ₀ hc hψ₀ hv
  set m : ℤ := (ω.conductorExponent v : ℤ) * v.degree
  rw [kappaV, _root_.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hq0 _)]
  have hGn : ‖ω.gaussV ψ₀ v (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion)‖ = (Nat.card Fq : ℝ) ^ ((m : ℝ) / 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), hG, ← Real.rpow_intCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hq0.le]
    ring_nf
  rw [hGn, ← Real.rpow_add hq0]
  convert Real.rpow_zero (Nat.card Fq : ℝ) using 2
  simp only [m]; push_cast; ring

end FFHeckeCharacter

namespace FFHeckeCharacter

variable (ψ₀ : AddChar Fq Circle) (ω : FFHeckeCharacter Fq k)

theorem cast_rpow_intCast (n : ℤ) :
    ((((Nat.card Fq : ℝ) ^ (n : ℝ) : ℝ)) : ℂ) = (Nat.card Fq : ℂ) ^ n := by
  rw [Real.rpow_intCast, Complex.ofReal_zpow, Complex.ofReal_natCast]

theorem sum_ramSet_deg : ∑ v ∈ ω.ramSet, ((ω.conductorExponent v : ℤ) * v.degree) = Divisor.deg ω.conductor := by
  rw [deg_eq_sum, ramSet]
  rfl

/-- $\prod_{v}q_v^{-f(v)/2}\cdot\lvert b\rvert^{1/2}=q^{1-g-\deg\mathfrak f}$. -/
theorem prod_rpow_mul_norm_sqrt (hc : IsConstantField Fq k) :
    (∏ v ∈ ω.ramSet, (Nat.card Fq : ℝ) ^ (-(((ω.conductorExponent v : ℤ) * v.degree : ℤ) : ℝ) / 2)) *
      ((FFIdeleGroup.norm ω.bIdele : ℝ) ^ (1 / 2 : ℝ)) =
      (Nat.card Fq : ℝ) ^ (((1 - Rep.genusInt Fq k - Divisor.deg ω.conductor : ℤ) : ℝ)) := by
  have hq0 : (0 : ℝ) < Nat.card Fq := by exact_mod_cast (Nat.card_pos (α := Fq))
  rw [← Real.rpow_sum_of_pos hq0, bIdele, FFIdeleGroup.norm_piD, NNReal.coe_zpow, NNReal.coe_natCast,
    ← Real.rpow_intCast, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0]
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  have h1 : ∑ x ∈ ω.ramSet, (((ω.conductorExponent x : ℤ) * x.degree : ℤ) : ℝ) = (Divisor.deg ω.conductor : ℝ) := by
    rw [← sum_ramSet_deg]; push_cast; rfl
  rw [h1, map_add, (weil_VI_2_cor1 hc).1]
  push_cast
  ring

/-- **Weil, VII.§7 Prop. 14, function fields.** With the Fourier transform $\Phi'=q^{1-g}\hat\Phi$ for the self-dual
measure, $b=\pi^{\mathfrak c+\mathfrak f}$ (an idele with $\operatorname{div}b=\mathfrak c+\mathfrak f$) and the local
constants $\kappa_v=q_v^{-f(v)/2}G_v(b_v^{-1})$ at the ramified places (Gauss sums modulo $\mathfrak p_v^{f(v)}$),
$\kappa_v\bar\kappa_v=1$ and $\Phi'_\omega(y)=\kappa\,\lvert b\rvert^{1/2}\,\Phi_{\omega^{-1}}(by)$ with
$\kappa=\prod_v\kappa_v$ ($\kappa_v=1$ at the unramified places). -/
@[kb "weil1973bnt" "Ch. VII, §7, Prop. 14 (p. 132), function fields: Fourier transform of Φ_ω, local constants κ_v with κ_v κ̄_v = 1 (Gauss sums modulo p_v^f(v))"]
theorem weil_VII_7_prop14_ff (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) :
    (∀ v ∈ ω.ramSet, ‖ω.kappaV ψ₀ v‖ = 1) ∧
      ∀ y : FFAdeleRing Fq k, (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ ω.stdPhi y =
        (∏ v ∈ ω.ramSet, ω.kappaV ψ₀ v) * ((((FFIdeleGroup.norm ω.bIdele : ℝ) ^ (1 / 2 : ℝ)) : ℝ) : ℂ) *
          (ω⁻¹).stdPhi (y * (ω.bIdele : FFAdeleRing Fq k)) := by
  refine ⟨fun v hv => ω.norm_kappaV ψ₀ hc hψ₀ hv, fun y => ?_⟩
  rw [fourierFF_stdPhi ψ₀ ω hψ₀]
  simp only [kappaV]
  rw [Finset.prod_mul_distrib]
  have h := congrArg (fun r : ℝ => (r : ℂ)) (ω.prod_rpow_mul_norm_sqrt hc)
  simp only [Complex.ofReal_mul, Complex.ofReal_prod] at h
  rw [cast_rpow_intCast] at h
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := Fq); exact_mod_cast this.ne'
  have h2 : (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k - Divisor.deg ω.conductor) =
      (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * (Nat.card Fq : ℂ) ^ (-Divisor.deg ω.conductor) := by
    rw [← zpow_add₀ hq0]; ring_nf
  calc (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) *
        ((∏ v ∈ ω.ramSet, ω.gaussV ψ₀ v (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion)) *
          (Nat.card Fq : ℂ) ^ (-Divisor.deg ω.conductor) * (ω⁻¹).stdPhi (y * (ω.bIdele : FFAdeleRing Fq k)))
      = ((Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * (Nat.card Fq : ℂ) ^ (-Divisor.deg ω.conductor)) *
          (∏ v ∈ ω.ramSet, ω.gaussV ψ₀ v (((ω.bLoc v)⁻¹ : v.Completionˣ) : v.Completion)) *
          (ω⁻¹).stdPhi (y * (ω.bIdele : FFAdeleRing Fq k)) := by ring
    _ = _ := by rw [← h2, ← h]; ring

end FFHeckeCharacter

end

end NumberFieldKB.WeilBNT.FF
