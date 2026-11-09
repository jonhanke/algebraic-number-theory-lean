import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4Centralizer

/-!
# Milne, Class Field Theory, Chapter IV, §3: crossed products and $H^2$

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`),
Chapter IV, §3, "Central simple algebras and 2-cocycles": the crossed-product algebra
$A(\varphi)$ of a normalized 2-cocycle (definition in prose, Lemma 3.13), the cocycle of an
algebra in $\mathcal A(L/k)$ (Lemma 3.12, Theorem 3.11), the isomorphism
$H^2(L/k) \cong \mathrm{Br}(L/k)$ (Theorem 3.14, Lemma 3.15) and Corollaries 3.16, 3.17.

Setting: $L/K$ a finite Galois extension, $G = \mathrm{Gal}(L/K)$ (`L ≃ₐ[K] L`).  A 2-cocycle is a
map $\varphi : G \times G \to L^\times$ with Mathlib's `groupCohomology.IsMulCocycle₂`:
$\varphi(\sigma\tau, \rho)\varphi(\sigma, \tau) = \sigma(\varphi(\tau, \rho))\varphi(\sigma, \tau\rho)$,
which is Milne's associativity condition.  It is *normalized* if $\varphi(1, 1) = 1$ (then
$\varphi(1, \tau) = \varphi(\sigma, 1) = 1$).  $H^2(L/K)$ is Mathlib's
`groupCohomology.H2 (Rep.ofAlgebraAutOnUnits K L)`.

The crossed product $A(\varphi)$ is the left $L$-vector space with basis $(e_\sigma)_{\sigma \in G}$
(functions $G \to L$) with $e_\sigma a = \sigma(a) e_\sigma$ and
$e_\sigma e_\tau = \varphi(\sigma, \tau) e_{\sigma\tau}$, i.e.
$(\sum_\sigma x_\sigma e_\sigma)(\sum_\tau y_\tau e_\tau)
  = \sum_\rho \bigl(\sum_\sigma x_\sigma\,\sigma(y_{\sigma^{-1}\rho})\,\varphi(\sigma, \sigma^{-1}\rho)\bigr) e_\rho$.

Milne's infinite Galois cohomology $H^2(k^{\mathrm{al}}/k)$ (Cor. 3.16) is the direct limit of the
$H^2(L/k)$ along inflation; as in the Chapter III files, the statement is formalized at finite level
(compatibility of the isomorphisms of Theorem 3.14 with inflation, together with Cor. 3.10).

Locators give the printed page of the book (printed page = pdf page − 9).
-/

open scoped TensorProduct

namespace NumberFieldKB.MilneCFT.Ch4

universe u

section Generic

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]

/-- A normalized 2-cocycle $\varphi : \mathrm{Gal}(L/K)^2 \to L^\times$ (Milne, §3, p. 135). -/
@[kb "milne2020cft" "v4.03, Ch. IV, §3, normalized 2-cocycle (factor set), p. 135"]
structure NormalizedCocycle where
  /-- The function $\varphi$. -/
  toFun : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ
  isMulCocycle₂ : groupCohomology.IsMulCocycle₂ toFun
  map_one_one : toFun (1, 1) = 1

variable {K L}

instance : CoeFun (NormalizedCocycle K L) fun _ => (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ :=
  ⟨NormalizedCocycle.toFun⟩

namespace NormalizedCocycle

variable (φ : NormalizedCocycle K L)

theorem cocycle (σ τ ρ : L ≃ₐ[K] L) :
    φ (σ * τ, ρ) * φ (σ, τ) = σ • φ (τ, ρ) * φ (σ, τ * ρ) :=
  φ.isMulCocycle₂ σ τ ρ

theorem one_left (τ : L ≃ₐ[K] L) : φ (1, τ) = 1 := by
  have h := φ.cocycle 1 1 τ
  simp only [mul_one, one_mul, one_smul, φ.map_one_one] at h
  simpa using h

theorem one_right (σ : L ≃ₐ[K] L) : φ (σ, 1) = 1 := by
  have h := φ.cocycle σ 1 1
  simp only [mul_one, one_mul, φ.map_one_one, smul_one] at h
  simpa using h

/-- The product of two normalized cocycles (the group law of $H^2$, written additively by
Milne: $\varphi + \varphi'$). -/
def mul (φ' : NormalizedCocycle K L) : NormalizedCocycle K L :=
  ⟨fun p => φ p * φ' p, by
    intro σ τ ρ
    have h1 := φ.cocycle σ τ ρ
    have h2 := φ'.cocycle σ τ ρ
    show φ (σ * τ, ρ) * φ' (σ * τ, ρ) * (φ (σ, τ) * φ' (σ, τ)) =
      σ • (φ (τ, ρ) * φ' (τ, ρ)) * (φ (σ, τ * ρ) * φ' (σ, τ * ρ))
    rw [smul_mul', mul_mul_mul_comm, h1, h2]
    exact mul_mul_mul_comm _ _ _ _, by
    show φ (1, 1) * φ' (1, 1) = 1
    rw [φ.map_one_one, φ'.map_one_one, one_mul]⟩

/-- Two cocycles are cohomologous if their quotient is a coboundary. -/
def Cohomologous (φ' : NormalizedCocycle K L) : Prop :=
  groupCohomology.IsMulCoboundary₂ fun p => φ p / φ' p

end NormalizedCocycle

theorem finrank_fun_aut [FiniteDimensional K L] [IsGalois K L] :
    Module.finrank K ((L ≃ₐ[K] L) → L) = Module.finrank K L ^ 2 := by
  rw [Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, sq]
  congr 1
  rw [← Nat.card_eq_fintype_card]
  exact IsGalois.card_aut_eq_finrank K L

/-! ### The crossed-product algebra -/

/-- The crossed-product algebra $A(\varphi)$ of a normalized 2-cocycle (Milne, §3, p. 136): the
$L$-vector space of functions $G \to L$ ($x = \sum_\sigma x_\sigma e_\sigma$) with the
multiplication described in the module docstring. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §3, def. of crossed-product algebra A(φ), p. 136"]
def CrossedProduct (_φ : NormalizedCocycle K L) : Type u := (L ≃ₐ[K] L) → L

namespace CrossedProduct

variable [FiniteDimensional K L] (φ : NormalizedCocycle K L)

instance : AddCommGroup (CrossedProduct φ) := inferInstanceAs (AddCommGroup ((L ≃ₐ[K] L) → L))

instance : Module L (CrossedProduct φ) := inferInstanceAs (Module L ((L ≃ₐ[K] L) → L))

instance : Module K (CrossedProduct φ) := inferInstanceAs (Module K ((L ≃ₐ[K] L) → L))

open Classical in
/-- The basis element $e_\sigma$ multiplied by $a$: the element $a e_\sigma$. -/
noncomputable def single (σ : L ≃ₐ[K] L) (a : L) : CrossedProduct φ := Pi.single σ a

noncomputable instance : Mul (CrossedProduct φ) :=
  ⟨fun x y => fun ρ => ∑ σ : L ≃ₐ[K] L, x σ * σ (y (σ⁻¹ * ρ)) * (φ (σ, σ⁻¹ * ρ) : L)⟩

noncomputable instance : One (CrossedProduct φ) := ⟨single φ 1 1⟩

@[simp] theorem add_apply (x y : CrossedProduct φ) (ρ : L ≃ₐ[K] L) : (x + y) ρ = x ρ + y ρ := rfl

@[simp] theorem zero_apply (ρ : L ≃ₐ[K] L) : (0 : CrossedProduct φ) ρ = 0 := rfl

@[simp] theorem sub_apply (x y : CrossedProduct φ) (ρ : L ≃ₐ[K] L) : (x - y) ρ = x ρ - y ρ := rfl

theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → CrossedProduct φ) (ρ : L ≃ₐ[K] L) :
    (∑ i ∈ s, f i) ρ = ∑ i ∈ s, f i ρ := Finset.sum_apply ρ s f

open Classical in
theorem single_apply (σ ρ : L ≃ₐ[K] L) (a : L) :
    single φ σ a ρ = if ρ = σ then a else 0 := by
  unfold single
  rw [Pi.single_apply]

theorem mul_apply (x y : CrossedProduct φ) (ρ : L ≃ₐ[K] L) :
    (x * y) ρ = ∑ σ : L ≃ₐ[K] L, x σ * σ (y (σ⁻¹ * ρ)) * (φ (σ, σ⁻¹ * ρ) : L) := rfl

/-- The multiplication rule $(a e_\sigma)(b e_\tau) = a\,\sigma(b)\,\varphi(\sigma, \tau)\,e_{\sigma\tau}$. -/
theorem single_mul_single (σ τ : L ≃ₐ[K] L) (a b : L) :
    single φ σ a * single φ τ b = single φ (σ * τ) (a * σ b * φ (σ, τ)) := by
  funext ρ
  rw [mul_apply, Finset.sum_eq_single σ]
  · simp only [single_apply]
    by_cases h : ρ = σ * τ
    · have h' : σ⁻¹ * ρ = τ := by rw [h]; group
      simp [h, h']
    · have h' : ¬ σ⁻¹ * ρ = τ := by
        intro h'; apply h; rw [← h']; group
      simp [h, h']
  · intro σ' _ hne
    simp [single_apply, hne]
  · simp

theorem left_distrib' (x y z : CrossedProduct φ) : x * (y + z) = x * y + x * z := by
  funext ρ
  simp only [mul_apply, add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem right_distrib' (x y z : CrossedProduct φ) : (x + y) * z = x * z + y * z := by
  funext ρ
  simp only [mul_apply, add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem zero_mul' (x : CrossedProduct φ) : 0 * x = 0 := by
  funext ρ
  simp [mul_apply]

theorem mul_zero' (x : CrossedProduct φ) : x * 0 = 0 := by
  funext ρ
  simp [mul_apply]

theorem decomp (x : CrossedProduct φ) : x = ∑ σ, single φ σ (x σ) := by
  funext ρ
  rw [sum_apply]
  simp only [single_apply]
  exact (Finset.sum_eq_single_of_mem ρ (Finset.mem_univ _)
    (fun b _ hb => if_neg (Ne.symm hb))).trans (if_pos rfl) |>.symm

theorem induction_on (P : CrossedProduct φ → Prop) (x : CrossedProduct φ) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hs : ∀ σ a, P (single φ σ a)) : P x := by
  rw [decomp φ x]
  exact Finset.sum_induction _ P hadd h0 (fun σ _ => hs σ _)

theorem mul_assoc' (x y z : CrossedProduct φ) : x * y * z = x * (y * z) := by
  refine induction_on φ (fun x => x * y * z = x * (y * z)) x ?_ ?_ ?_
  · simp only [zero_mul']
  · intro a b ha hb
    simp only [right_distrib', ha, hb]
  refine fun σ a => induction_on φ (fun y => single φ σ a * y * z = single φ σ a * (y * z)) y ?_ ?_ ?_
  · simp only [zero_mul', mul_zero']
  · intro u v hu hv
    simp only [right_distrib', left_distrib', hu, hv]
  refine fun τ b => induction_on φ (fun z => single φ σ a * single φ τ b * z =
    single φ σ a * (single φ τ b * z)) z ?_ ?_ ?_
  · simp only [mul_zero']
  · intro u v hu hv
    simp only [left_distrib', hu, hv]
  intro ρ c
  rw [single_mul_single, single_mul_single, single_mul_single, single_mul_single, mul_assoc]
  congr 1
  have h := congrArg Units.val (φ.cocycle σ τ ρ)
  simp only [Units.val_mul, Units.smul_def] at h
  simp only [map_mul, AlgEquiv.mul_apply]
  have h' : ((φ (σ * τ, ρ) : Lˣ) : L) * φ (σ, τ) = σ (φ (τ, ρ) : Lˣ) * φ (σ, τ * ρ) := by
    simpa using h
  linear_combination (a * σ b * σ (τ c)) * h'

theorem one_mul' (x : CrossedProduct φ) : 1 * x = x := by
  refine induction_on φ (fun x => 1 * x = x) x ?_ ?_ ?_
  · exact mul_zero' φ _
  · intro a b ha hb
    simp only [left_distrib', ha, hb]
  intro σ a
  show single φ 1 1 * single φ σ a = single φ σ a
  rw [single_mul_single]
  simp [NormalizedCocycle.one_left]

theorem mul_one' (x : CrossedProduct φ) : x * 1 = x := by
  refine induction_on φ (fun x => x * 1 = x) x ?_ ?_ ?_
  · exact zero_mul' φ _
  · intro a b ha hb
    simp only [right_distrib', ha, hb]
  intro σ a
  show single φ σ a * single φ 1 1 = single φ σ a
  rw [single_mul_single]
  simp [NormalizedCocycle.one_right]

noncomputable instance : Ring (CrossedProduct φ) where
  __ := (inferInstance : AddCommGroup (CrossedProduct φ))
  mul_assoc := mul_assoc' φ
  one_mul := one_mul' φ
  mul_one := mul_one' φ
  left_distrib := left_distrib' φ
  right_distrib := right_distrib' φ
  zero_mul := zero_mul' φ
  mul_zero := mul_zero' φ

theorem smul_mul_assoc' (r : K) (x y : CrossedProduct φ) : r • x * y = r • (x * y) := by
  funext ρ
  show _ = r • (x * y) ρ
  simp only [mul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  show (r • x σ) * _ * _ = _
  rw [smul_mul_assoc, smul_mul_assoc]

theorem mul_smul_comm' (r : K) (x y : CrossedProduct φ) : x * r • y = r • (x * y) := by
  funext ρ
  show _ = r • (x * y) ρ
  simp only [mul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  show x σ * σ (r • y (σ⁻¹ * ρ)) * _ = _
  rw [map_smul, mul_smul_comm, smul_mul_assoc]

noncomputable instance : Algebra K (CrossedProduct φ) :=
  Algebra.ofModule (smul_mul_assoc' φ) (mul_smul_comm' φ)

/-- The embedding $L \to A(\varphi)$, $a \mapsto a e_1$ (Milne identifies $L$ with $L e_1$). -/
noncomputable def incl : L →ₐ[K] CrossedProduct φ where
  toFun a := single φ 1 a
  map_one' := rfl
  map_mul' a b := by
    show single φ 1 (a * b) = single φ 1 a * single φ 1 b
    rw [single_mul_single]
    simp [φ.map_one_one]
  map_zero' := by
    funext ρ
    simp [single_apply]
  map_add' a b := by
    funext ρ
    simp only [single_apply, add_apply]
    split_ifs <;> simp
  commutes' r := by
    show single φ 1 (algebraMap K L r) = algebraMap K _ r
    rw [Algebra.algebraMap_eq_smul_one]
    funext ρ
    show _ = r • (single φ 1 1 ρ)
    simp only [single_apply]
    split_ifs
    · simp [Algebra.algebraMap_eq_smul_one]
    · simp

instance : FiniteDimensional K (CrossedProduct φ) :=
  inferInstanceAs (Module.Finite K ((L ≃ₐ[K] L) → L))

theorem single_one_mul_apply (b : L) (y : CrossedProduct φ) (ρ : L ≃ₐ[K] L) :
    (single φ 1 b * y) ρ = b * y ρ := by
  rw [mul_apply, Finset.sum_eq_single 1]
  · simp [single_apply, NormalizedCocycle.one_left]
  · intro σ _ hne
    simp [single_apply, hne]
  · simp

theorem mul_single_one_apply (x : CrossedProduct φ) (b : L) (ρ : L ≃ₐ[K] L) :
    (x * single φ 1 b) ρ = x ρ * ρ b := by
  rw [mul_apply, Finset.sum_eq_single ρ]
  · simp [single_apply, NormalizedCocycle.one_right]
  · intro σ _ hne
    have : σ⁻¹ * ρ ≠ 1 := fun h => hne (by rw [inv_mul_eq_one] at h; exact h)
    simp [single_apply, this]
  · simp

theorem exists_apply_ne {σ τ : L ≃ₐ[K] L} (h : σ ≠ τ) : ∃ b, σ b ≠ τ b := by
  by_contra hc
  push_neg at hc
  exact h (AlgEquiv.ext hc)

theorem eq_single_one_of_comm (x : CrossedProduct φ)
    (h : ∀ b, x * single φ 1 b = single φ 1 b * x) : x = single φ 1 (x 1) := by
  funext ρ
  by_cases hρ : ρ = 1
  · subst hρ
    simp [single_apply]
  · obtain ⟨b, hb⟩ := exists_apply_ne hρ
    have h1 := congrArg (fun z : CrossedProduct φ => z ρ) (h b)
    simp only [mul_single_one_apply, single_one_mul_apply] at h1
    have h2 : x ρ * (ρ b - b) = 0 := by linear_combination h1
    have hne : ρ b - b ≠ 0 := sub_ne_zero.2 (by simpa using hb)
    simp only [single_apply, if_neg hρ]
    exact (mul_eq_zero.1 h2).resolve_right hne

open Classical in
theorem one_mem_of_ne (I : TwoSidedIdeal (CrossedProduct φ)) :
    ∀ (n : ℕ) (α : CrossedProduct φ), α ∈ I → α ≠ 0 →
      (Finset.univ.filter (fun σ => α σ ≠ 0)).card = n → (1 : CrossedProduct φ) ∈ I := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α hα h0 hn
  classical
  obtain ⟨σ0, hσ0⟩ : ∃ σ0, α σ0 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (funext hc)
  by_cases hs : ∃ σ1, σ1 ≠ σ0 ∧ α σ1 ≠ 0
  · obtain ⟨σ1, hne, hσ1⟩ := hs
    obtain ⟨b, hb⟩ := exists_apply_ne hne.symm
    have hβI : α * single φ 1 b - single φ 1 (σ1 b) * α ∈ I :=
      I.sub_mem (I.mul_mem_right _ _ hα) (I.mul_mem_left _ _ hα)
    have hβ : ∀ ρ, (α * single φ 1 b - single φ 1 (σ1 b) * α) ρ = α ρ * (ρ b - σ1 b) := by
      intro ρ
      rw [sub_apply, mul_single_one_apply, single_one_mul_apply]
      ring
    have hβ0 : α * single φ 1 b - single φ 1 (σ1 b) * α ≠ 0 := by
      intro h
      have := hβ σ0
      rw [h] at this
      have h3 : α σ0 * (σ0 b - σ1 b) = 0 := this.symm
      exact (mul_ne_zero hσ0 (sub_ne_zero.2 hb)) h3
    refine ih _ ?_ _ hβI hβ0 rfl
    rw [← hn]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨σ1, ?_, ?_⟩
      · simp [hσ1]
      · simp [hβ]
    · intro ρ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hβ]
      intro h h'
      exact h (by rw [h', zero_mul])
  · push_neg at hs
    obtain ⟨a0, ha0⟩ : ∃ a0, a0 = α σ0 := ⟨_, rfl⟩
    have hαs : α = single φ σ0 a0 := by
      funext ρ
      rw [single_apply]
      by_cases h : ρ = σ0
      · subst h; simp [ha0]
      · rw [if_neg h]; exact hs ρ h
    have ha0' : a0 ≠ 0 := by rw [ha0]; exact hσ0
    subst hαs
    have e1 : single φ 1 a0⁻¹ * single φ σ0 a0 ∈ I := I.mul_mem_left _ _ hα
    rw [single_mul_single] at e1
    have e2 : single φ (1 * σ0) (a0⁻¹ * (1 : L ≃ₐ[K] L) a0 * φ (1, σ0)) = single φ σ0 1 := by
      simp [NormalizedCocycle.one_left, ha0']
    rw [e2] at e1
    have e3 : single φ σ0 1 * single φ σ0⁻¹ 1 ∈ I := I.mul_mem_right _ _ e1
    rw [single_mul_single] at e3
    have e4 := I.mul_mem_left (single φ 1 ((φ (σ0, σ0⁻¹) : Lˣ) : L)⁻¹) _ e3
    rw [single_mul_single] at e4
    have e5 : single φ (1 * (σ0 * σ0⁻¹))
        ((((φ (σ0, σ0⁻¹) : Lˣ) : L))⁻¹ * (1 : L ≃ₐ[K] L) (1 * σ0 1 * φ (σ0, σ0⁻¹)) * φ (1, σ0 * σ0⁻¹))
        = 1 := by
      show _ = single φ 1 1
      simp [NormalizedCocycle.one_left]
    rwa [e5] at e4

variable [IsGalois K L]

/-- Lemma 3.13 of Milne (central part): $A(\varphi)$ is central over $K$.  (The book's
"central simple over $K$" has a misprint, "over $K$" for the base field $k$.) -/
@[kb "milne2020cft" "v4.03, Ch. IV, Lem. 3.13, p. 136"]
instance isCentral : Algebra.IsCentral K (CrossedProduct φ) := by
  refine ⟨fun x hx => ?_⟩
  rw [Subalgebra.mem_center_iff] at hx
  obtain ⟨a, rfl⟩ : ∃ a, x = single φ 1 a :=
    ⟨_, eq_single_one_of_comm φ x (fun b => (hx (single φ 1 b)).symm)⟩
  have hσ : ∀ σ : L ≃ₐ[K] L, σ a = a := by
    intro σ
    have h1 := congrArg (fun z : CrossedProduct φ => z σ) (hx (single φ σ 1))
    simp only [single_mul_single, single_apply] at h1
    simpa [NormalizedCocycle.one_left, NormalizedCocycle.one_right] using h1
  have hmem : a ∈ (⊥ : IntermediateField K L) := (IsGalois.mem_bot_iff_fixed a).2 hσ
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 hmem
  rw [Algebra.mem_bot]
  exact ⟨k, by rw [← (incl φ).commutes k, hk]; rfl⟩

/-- Lemma 3.13 of Milne (simple part): $A(\varphi)$ is simple. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Lem. 3.13, p. 136"]
instance isSimpleRing : IsSimpleRing (CrossedProduct φ) := by
  refine ⟨{ toNontrivial := ⟨⟨⊥, ⊤, fun h => ?_⟩⟩, eq_bot_or_eq_top := fun I => ?_ }⟩
  · have h1 : (1 : CrossedProduct φ) ∈ (⊥ : TwoSidedIdeal (CrossedProduct φ)) := by
      rw [h]; trivial
    rw [TwoSidedIdeal.mem_bot] at h1
    have := congrArg (fun z : CrossedProduct φ => z 1) h1
    change (single φ 1 1) 1 = 0 at this
    rw [single_apply, if_pos rfl] at this
    exact one_ne_zero this
  · by_cases hI : I = ⊥
    · exact Or.inl hI
    · right
      obtain ⟨α, hα, h0⟩ : ∃ α ∈ I, α ≠ 0 := by
        by_contra hc
        push_neg at hc
        apply hI
        ext x
        rw [TwoSidedIdeal.mem_bot]
        exact ⟨fun hx => hc x hx, fun hx => hx ▸ I.zero_mem⟩
      exact (TwoSidedIdeal.one_mem_iff I).1 (one_mem_of_ne φ I _ α hα h0 rfl)

/-- Lemma 3.13 of Milne, first step of the proof: the centralizer of $L = L e_1$ in $A(\varphi)$
is $L$. -/
theorem centralizer_incl_range :
    Subalgebra.centralizer K ((incl φ).range : Set (CrossedProduct φ)) = (incl φ).range := by
  apply le_antisymm
  · intro x hx
    rw [Subalgebra.mem_centralizer_iff] at hx
    have := eq_single_one_of_comm φ x (fun b => (hx (incl φ b) ⟨b, rfl⟩).symm)
    exact ⟨x 1, this.symm⟩
  · rintro _ ⟨a, rfl⟩
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]

theorem finrank_eq : Module.finrank K (CrossedProduct φ) = Module.finrank K L ^ 2 := by
  have h : Module.finrank K (CrossedProduct φ) = Module.finrank K ((L ≃ₐ[K] L) → L) := rfl
  rw [h]
  exact finrank_fun_aut

/-- $A(\varphi)$ as an element of `CSA K`. -/
noncomputable def toCSA : CSA.{u, u} K where
  toAlgCat := AlgCat.of K (CrossedProduct φ)

end CrossedProduct

/-! ### The cocycle of an algebra in $\mathcal A(L/K)$ -/

section Cocycle

variable [FiniteDimensional K L]

/-- Milne's class $\mathcal A(L/K)$ (p. 135): central simple $K$-algebras $A$ containing $L$ (an
embedding $\iota : L \to A$) with $[A : K] = [L : K]^2$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §3, the class A(L/k), p. 135"]
structure IsInClassA (A : Type u) [Ring A] [Algebra K A] (ι : L →ₐ[K] A) : Prop where
  isCentral : Algebra.IsCentral K A
  isSimpleRing : IsSimpleRing A
  finiteDimensional : FiniteDimensional K A
  finrank_eq : Module.finrank K A = Module.finrank K L ^ 2

/-- $\varphi$ is a cocycle attached to $(A, \iota)$ (Milne, (38)–(40)): there are invertible
$e_\sigma \in A$ with $e_\sigma\,\iota(a) = \iota(\sigma a)\,e_\sigma$ and
$e_\sigma e_\tau = \iota(\varphi(\sigma, \tau))\,e_{\sigma\tau}$. -/
def IsCocycleOf (A : Type u) [Ring A] [Algebra K A] (ι : L →ₐ[K] A)
    (φ : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) : Prop :=
  ∃ e : (L ≃ₐ[K] L) → Aˣ, (∀ σ a, (e σ : A) * ι a = ι (σ a) * e σ) ∧
    ∀ σ τ, (e σ : A) * e τ = ι (φ (σ, τ)) * e (σ * τ)

/-- Lemma 3.12 of Milne: for $A \in \mathcal A(L/K)$ and elements $e_\sigma$ satisfying (38), the
family $(e_\sigma)_{\sigma \in G}$ is a basis of $A$ as a left $L$-vector space: every $x \in A$ is
uniquely $\sum_\sigma \iota(c_\sigma) e_\sigma$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Lem. 3.12, p. 135"]
theorem lemma_3_12 [IsGalois K L] (A : Type u) [Ring A] [Algebra K A] (ι : L →ₐ[K] A)
    (hA : IsInClassA A ι) (e : (L ≃ₐ[K] L) → Aˣ)
    (he : ∀ σ a, (e σ : A) * ι a = ι (σ a) * e σ) (x : A) :
    ∃! c : (L ≃ₐ[K] L) → L, x = ∑ σ, ι (c σ) * e σ := by
  classical
  haveI := hA.isCentral
  haveI := hA.isSimpleRing
  haveI := hA.finiteDimensional
  have hι : Function.Injective ι := RingHom.injective ι.toRingHom
  let T : ((L ≃ₐ[K] L) → L) →ₗ[K] A :=
    { toFun := fun c => ∑ σ, ι (c σ) * e σ
      map_add' := by
        intro c d
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c
        simp [Finset.smul_sum, smul_mul_assoc] }
  have key : ∀ n : ℕ, ∀ c : (L ≃ₐ[K] L) → L,
      (Finset.univ.filter (fun σ => c σ ≠ 0)).card = n → ∑ σ, ι (c σ) * e σ = 0 → c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro c hn hsum
    by_contra hc
    obtain ⟨σ0, hσ0⟩ : ∃ σ0, c σ0 ≠ 0 := by
      by_contra hc'
      push_neg at hc'
      exact hc (funext hc')
    by_cases hs : ∃ σ1, σ1 ≠ σ0 ∧ c σ1 ≠ 0
    · obtain ⟨σ1, hne, hσ1⟩ := hs
      obtain ⟨b, hb⟩ := CrossedProduct.exists_apply_ne hne.symm
      have hsum' : ∑ ρ, ι (c ρ * (ρ b - σ1 b)) * e ρ = 0 := by
        have h3 : ∑ ρ, ι (c ρ * (ρ b - σ1 b)) * e ρ =
            (∑ ρ, ι (c ρ) * e ρ) * ι b - ι (σ1 b) * (∑ ρ, ι (c ρ) * e ρ) := by
          rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun ρ _ => ?_
          have h1 : ι (c ρ) * e ρ * ι b = ι (c ρ) * ι (ρ b) * e ρ := by
            rw [mul_assoc, he, ← mul_assoc]
          have h2 : ι (σ1 b) * (ι (c ρ) * e ρ) = ι (c ρ) * ι (σ1 b) * e ρ := by
            rw [← mul_assoc, ← map_mul, ← map_mul, mul_comm]
          rw [h1, h2, map_mul, map_sub, mul_sub, sub_mul]
        rw [h3, hsum]
        simp
      have hlt : (Finset.univ.filter (fun ρ => c ρ * (ρ b - σ1 b) ≠ 0)).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨σ1, ?_, ?_⟩
          · simp [hσ1]
          · simp
        · intro ρ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro h h'
          exact h (by rw [h', zero_mul])
      have := ih _ hlt _ rfl hsum'
      have h4 := congrFun this σ0
      simp only [Pi.zero_apply] at h4
      exact mul_ne_zero hσ0 (sub_ne_zero.2 hb) h4
    · push_neg at hs
      have hsingle : ∑ σ, ι (c σ) * e σ = ι (c σ0) * e σ0 := by
        refine Finset.sum_eq_single_of_mem σ0 (Finset.mem_univ _) fun ρ _ hρ => ?_
        rw [hs ρ hρ]
        simp
      rw [hsingle] at hsum
      have h5 : ι (c σ0) = 0 := by
        have := congrArg (fun z : A => z * (↑(e σ0)⁻¹ : A)) hsum
        simpa using this
      exact hσ0 (hι (by rw [h5, map_zero]))
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    exact key _ c rfl hc
  have hfr : Module.finrank K ((L ≃ₐ[K] L) → L) = Module.finrank K A := by
    rw [finrank_fun_aut, hA.finrank_eq]
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj
  obtain ⟨c, hc⟩ := hsurj x
  refine ⟨c, hc.symm, fun d hd => hinj ?_⟩
  show T d = T c
  rw [hc]
  exact hd.symm

/-- Theorem 3.11 of Milne, existence and normalization of the cocycle: every
$A \in \mathcal A(L/K)$ has a normalized 2-cocycle attached to it (choose $e_1 = 1$). -/
@[kb "milne2020cft" "v4.03, Ch. IV, Thm. 3.11 (the map A ↦ φ(A)), p. 135"]
theorem exists_isCocycleOf [IsGalois K L] (A : Type u) [Ring A] [Algebra K A]
    (ι : L →ₐ[K] A) (hA : IsInClassA A ι) :
    ∃ φ : NormalizedCocycle K L, IsCocycleOf A ι φ := by
  classical
  haveI := hA.isCentral
  haveI := hA.isSimpleRing
  haveI := hA.finiteDimensional
  have hι : Function.Injective ι := RingHom.injective ι.toRingHom
  let B : Subalgebra K A := ι.range
  let eB : L ≃ₐ[K] B := AlgEquiv.ofInjectiveField ι
  haveI : IsSimpleRing B := IsSimpleRing.of_ringEquiv eB.toRingEquiv inferInstance
  have hBfield : IsField B := eB.symm.toRingEquiv.toMulEquiv.isField (Field.toIsField L)
  have hconj : ∀ σ : L ≃ₐ[K] L, ∃ u : Aˣ, ∀ a, (u : A) * ι a = ι (σ a) * u := by
    intro σ
    obtain ⟨u, hu⟩ := cor_2_11 (K := K) A B B ((eB.symm.trans σ).trans eB)
    refine ⟨u, fun a => ?_⟩
    have h1 := hu (eB a)
    have h2 : (((eB.symm.trans σ).trans eB) (eB a) : A) = ι (σ a) := by
      have h4 : ((eB.symm.trans σ).trans eB) (eB a) = eB (σ a) := by simp
      rw [h4]
      rfl
    rw [h2] at h1
    have h3 : ((eB a : B) : A) = ι a := rfl
    rw [h3] at h1
    rw [h1, mul_assoc, mul_assoc, Units.inv_mul, mul_one]
  choose e0 he0 using hconj
  let e : (L ≃ₐ[K] L) → Aˣ := fun σ => if σ = 1 then 1 else e0 σ
  have he : ∀ σ a, (e σ : A) * ι a = ι (σ a) * e σ := by
    intro σ a
    by_cases h : σ = 1
    · subst h
      simp [e]
    · simp only [e, if_neg h]
      exact he0 σ a
  have he1 : e 1 = 1 := by simp [e]
  have hcancel : ∀ (u : Aˣ) (x y : A), x * u = y * u → x = y := by
    intro u x y h
    simpa using congrArg (fun z : A => z * (↑u⁻¹ : A)) h
  have hcent : Subalgebra.centralizer K (B : Set A) = B := by
    have hfr : Module.finrank K A = Module.finrank K B ^ 2 := by
      rw [hA.finrank_eq, LinearEquiv.finrank_eq eB.toLinearEquiv]
    exact ((cor_3_4 (K := K) A B hBfield).out 2 1).1 hfr
  have hw : ∀ σ τ : L ≃ₐ[K] L, ∃ u : Lˣ, (e σ : A) * e τ = ι u * e (σ * τ) := by
    intro σ τ
    set n : Aˣ := e (σ * τ) with hn
    have hcomm : ((e σ : A) * e τ * ↑n⁻¹) ∈ Subalgebra.centralizer K (B : Set A) := by
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ ⟨a, rfl⟩
      change ι a * _ = _ * ι a
      set c' : L := (σ * τ)⁻¹ a with hc'
      have hgc : (σ * τ) c' = a := by
        rw [hc', ← AlgEquiv.mul_apply, mul_inv_cancel]; rfl
      have hm : (e σ : A) * e τ * ι c' = ι a * ((e σ : A) * e τ) := by
        rw [mul_assoc, he τ c', ← mul_assoc, he σ, ← mul_assoc, ← hgc]
        rfl
      have hn' : (n : A) * ι c' = ι a * n := by
        rw [hn, he, hgc]
      have hn'' : ι c' * (↑n⁻¹ : A) = ↑n⁻¹ * ι a := by
        have := congrArg (fun z : A => ↑n⁻¹ * z * (↑n⁻¹ : A)) hn'
        simpa [mul_assoc] using this
      calc ι a * ((e σ : A) * e τ * ↑n⁻¹) = (ι a * ((e σ : A) * e τ)) * ↑n⁻¹ := by
            exact (mul_assoc _ _ _).symm
        _ = (e σ : A) * e τ * ι c' * ↑n⁻¹ := by rw [hm]
        _ = (e σ : A) * e τ * (ι c' * ↑n⁻¹) := by rw [mul_assoc _ (ι c')]
        _ = (e σ : A) * e τ * (↑n⁻¹ * ι a) := by rw [hn'']
        _ = (e σ : A) * e τ * ↑n⁻¹ * ι a := by rw [mul_assoc _ (↑n⁻¹ : A)]
    rw [hcent] at hcomm
    obtain ⟨u, hu⟩ := hcomm
    have hu' : ι u = (e σ : A) * e τ * ↑n⁻¹ := hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      have h0 : ((e σ * e τ * n⁻¹ : Aˣ) : A) = 0 := by
        rw [Units.val_mul, Units.val_mul, ← hu', map_zero]
      exact Units.ne_zero _ h0
    refine ⟨Units.mk0 u hu0, ?_⟩
    show _ = ι u * _
    rw [hu']
    simp
  choose φ0 hφ0 using hw
  have hnorm : φ0 1 1 = 1 := by
    have h := hφ0 1 1
    rw [mul_one (1 : L ≃ₐ[K] L), he1] at h
    simp at h
    apply Units.ext
    apply hι
    rw [Units.val_one, map_one]
    exact h.symm
  have hcoc : groupCohomology.IsMulCocycle₂
      (fun p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) => φ0 p.1 p.2) := by
    intro σ τ ρ
    show φ0 (σ * τ) ρ * φ0 σ τ = σ • φ0 τ ρ * φ0 σ (τ * ρ)
    have h1 : ((e σ : A) * e τ) * e ρ = (e σ : A) * (e τ * e ρ) := mul_assoc _ _ _
    rw [hφ0 σ τ, hφ0 τ ρ] at h1
    have h2 : (e σ : A) * (ι (φ0 τ ρ) * e (τ * ρ)) =
        ι (σ (φ0 τ ρ)) * (ι (φ0 σ (τ * ρ)) * e (σ * (τ * ρ))) := by
      rw [← mul_assoc, he, mul_assoc, hφ0 σ (τ * ρ)]
    have h3 : ((ι (φ0 σ τ) * e (σ * τ)) * e ρ : A) =
        ι (φ0 σ τ) * (ι (φ0 (σ * τ) ρ) * e (σ * τ * ρ)) := by
      rw [mul_assoc, hφ0 (σ * τ) ρ]
    rw [h3, h2, mul_assoc σ τ ρ] at h1
    simp only [← mul_assoc] at h1
    have h5 := hcancel _ _ _ h1
    rw [← map_mul, ← map_mul] at h5
    have h6 := hι h5
    apply Units.ext
    simp only [Units.val_mul, Units.smul_def] 
    rw [mul_comm]
    exact h6
  exact ⟨⟨fun p => φ0 p.1 p.2, hcoc, hnorm⟩, e, he, fun σ τ => hφ0 σ τ⟩

theorem cocycle_e_one {A : Type u} [Ring A] [Algebra K A] (ι : L →ₐ[K] A)
    (φ : NormalizedCocycle K L) (e : (L ≃ₐ[K] L) → Aˣ)
    (he2 : ∀ σ τ, (e σ : A) * e τ = ι (φ (σ, τ)) * e (σ * τ)) : e 1 = 1 := by
  have h := he2 1 1
  simp only [mul_one, φ.map_one_one, Units.val_one, map_one, one_mul] at h
  apply Units.ext
  have := congrArg (fun z : A => z * (↑(e 1)⁻¹ : A)) h
  simpa using this

theorem eq_incl_of_comm [IsGalois K L] {A : Type u} [Ring A] [Algebra K A] (ι : L →ₐ[K] A)
    (hA : IsInClassA A ι) (x : A) (hx : ∀ b, x * ι b = ι b * x) : ∃ u : L, x = ι u := by
  classical
  haveI := hA.isCentral
  haveI := hA.isSimpleRing
  haveI := hA.finiteDimensional
  let B : Subalgebra K A := ι.range
  let eB : L ≃ₐ[K] B := AlgEquiv.ofInjectiveField ι
  have hBfield : IsField B := eB.symm.toRingEquiv.toMulEquiv.isField (Field.toIsField L)
  have hcent : Subalgebra.centralizer K (B : Set A) = B := by
    have hfr : Module.finrank K A = Module.finrank K B ^ 2 := by
      rw [hA.finrank_eq, LinearEquiv.finrank_eq eB.toLinearEquiv]
    exact ((cor_3_4 (K := K) A B hBfield).out 2 1).1 hfr
  have hmem : x ∈ Subalgebra.centralizer K (B : Set A) := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    exact (hx b).symm
  rw [hcent] at hmem
  obtain ⟨u, hu⟩ := hmem
  exact ⟨u, by exact hu.symm⟩

theorem cohomologous_of_two_families [IsGalois K L] {A' : Type u} [Ring A'] [Algebra K A']
    (ι' : L →ₐ[K] A') (hA' : IsInClassA A' ι') (φ φ' : NormalizedCocycle K L)
    (e' f : (L ≃ₐ[K] L) → A'ˣ)
    (he' : ∀ σ a, (e' σ : A') * ι' a = ι' (σ a) * e' σ)
    (he2' : ∀ σ τ, (e' σ : A') * e' τ = ι' (φ' (σ, τ)) * e' (σ * τ))
    (hf : ∀ σ a, (f σ : A') * ι' a = ι' (σ a) * f σ)
    (hf2 : ∀ σ τ, (f σ : A') * f τ = ι' (φ (σ, τ)) * f (σ * τ)) :
    NormalizedCocycle.Cohomologous φ φ' := by
  classical
  haveI := hA'.isSimpleRing
  have hι : Function.Injective ι' := RingHom.injective ι'.toRingHom
  have hσσ : ∀ (σ : L ≃ₐ[K] L) (x : L), σ (σ⁻¹ x) = x := by
    intro σ x
    rw [← AlgEquiv.mul_apply, mul_inv_cancel]
    rfl
  have hx : ∀ σ, ∃ u : Lˣ, (f σ : A') = ι' u * e' σ := by
    intro σ
    have hcomm : ∀ b, ((f σ : A') * ↑(e' σ)⁻¹) * ι' b = ι' b * ((f σ : A') * ↑(e' σ)⁻¹) := by
      intro b
      have h1 : (↑(e' σ)⁻¹ : A') * ι' b = ι' (σ⁻¹ b) * ↑(e' σ)⁻¹ := by
        have := he' σ (σ⁻¹ b)
        rw [hσσ] at this
        calc (↑(e' σ)⁻¹ : A') * ι' b = ↑(e' σ)⁻¹ * ι' b * (e' σ * ↑(e' σ)⁻¹) := by simp
          _ = ↑(e' σ)⁻¹ * (ι' b * e' σ) * ↑(e' σ)⁻¹ := by simp only [mul_assoc]
          _ = ↑(e' σ)⁻¹ * (e' σ * ι' (σ⁻¹ b)) * ↑(e' σ)⁻¹ := by rw [this]
          _ = ι' (σ⁻¹ b) * ↑(e' σ)⁻¹ := by simp [mul_assoc]
      calc ((f σ : A') * ↑(e' σ)⁻¹) * ι' b = f σ * (↑(e' σ)⁻¹ * ι' b) := by rw [mul_assoc]
        _ = (f σ * ι' (σ⁻¹ b)) * ↑(e' σ)⁻¹ := by rw [h1, mul_assoc]
        _ = ι' b * ((f σ : A') * ↑(e' σ)⁻¹) := by rw [hf, hσσ, mul_assoc]
    obtain ⟨u, hu⟩ := eq_incl_of_comm ι' hA' _ hcomm
    have hfu : (f σ : A') = ι' u * e' σ := by
      rw [← hu]; simp
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hfu
      exact Units.ne_zero _ hfu
    exact ⟨Units.mk0 u hu0, by simpa using hfu⟩
  choose x hx using hx
  refine ⟨x, fun σ τ => ?_⟩
  have h := hf2 σ τ
  rw [hx σ, hx τ, hx (σ * τ)] at h
  have lhs : (ι' (x σ : L) * e' σ) * (ι' (x τ : L) * e' τ) =
      ι' ((x σ : L) * σ (x τ : L) * (φ' (σ, τ) : L)) * e' (σ * τ) := by
    calc (ι' (x σ : L) * e' σ) * (ι' (x τ : L) * e' τ)
        = ι' (x σ : L) * ((e' σ * ι' (x τ : L)) * e' τ) := by simp only [mul_assoc]
      _ = ι' (x σ : L) * ((ι' (σ (x τ : L)) * e' σ) * e' τ) := by rw [he']
      _ = ι' (x σ : L) * (ι' (σ (x τ : L)) * (e' σ * e' τ)) := by simp only [mul_assoc]
      _ = ι' (x σ : L) * (ι' (σ (x τ : L)) * (ι' (φ' (σ, τ)) * e' (σ * τ))) := by rw [he2']
      _ = _ := by simp only [map_mul, mul_assoc]
  have rhs : ι' (φ (σ, τ) : L) * (ι' (x (σ * τ) : L) * e' (σ * τ)) =
      ι' ((φ (σ, τ) : L) * (x (σ * τ) : L)) * e' (σ * τ) := by
    simp only [map_mul, mul_assoc]
  rw [lhs, rhs] at h
  have h3 : ι' ((x σ : L) * σ (x τ : L) * (φ' (σ, τ) : L)) =
      ι' ((φ (σ, τ) : L) * (x (σ * τ) : L)) := by
    simpa using congrArg (fun z : A' => z * (↑(e' (σ * τ))⁻¹ : A')) h
  have h2 := hι h3
  have hs : ((σ • x τ : Lˣ) : L) = σ (x τ : L) := rfl
  apply Units.ext
  simp only [Units.val_mul, Units.val_div_eq_div_val, hs]
  have hn1 := (x (σ * τ)).ne_zero
  have hn2 := (φ' (σ, τ)).ne_zero
  field_simp
  linear_combination h2

/-- The $K$-linear map $c \mapsto \sum_\sigma \iota(c_\sigma) e_\sigma$. -/
noncomputable def coeffMap {A : Type u} [Ring A] [Algebra K A] (ι : L →ₐ[K] A)
    (e : (L ≃ₐ[K] L) → Aˣ) : ((L ≃ₐ[K] L) → L) →ₗ[K] A where
  toFun c := ∑ σ, ι (c σ) * e σ
  map_add' c d := by
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    simp [Finset.smul_sum, smul_mul_assoc]

open Classical in
theorem coeffMap_single {A : Type u} [Ring A] [Algebra K A] (ι : L →ₐ[K] A)
    (e : (L ≃ₐ[K] L) → Aˣ) (σ : L ≃ₐ[K] L) (a : L) :
    coeffMap ι e (Pi.single σ a) = ι a * e σ := by
  classical
  show ∑ τ, ι ((Pi.single σ a : (L ≃ₐ[K] L) → L) τ) * (e τ : A) = _
  rw [Finset.sum_eq_single σ]
  · simp
  · intro τ _ hτ
    simp [Pi.single_apply, hτ]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem coeffMap_bijective [IsGalois K L] {A : Type u} [Ring A] [Algebra K A] (ι : L →ₐ[K] A)
    (hA : IsInClassA A ι) (e : (L ≃ₐ[K] L) → Aˣ)
    (he : ∀ σ a, (e σ : A) * ι a = ι (σ a) * e σ) : Function.Bijective (coeffMap ι e) := by
  refine ⟨fun c d h => ?_, fun x => ?_⟩
  · exact (lemma_3_12 A ι hA e he (coeffMap ι e d)).unique (y₁ := c) (y₂ := d) h.symm rfl
  · obtain ⟨c, hc, -⟩ := lemma_3_12 A ι hA e he x
    exact ⟨c, hc.symm⟩

theorem nonempty_algEquiv_of_two_families [IsGalois K L] {A A' : Type u} [Ring A] [Algebra K A]
    [Ring A'] [Algebra K A'] (ι : L →ₐ[K] A) (ι' : L →ₐ[K] A') (hA : IsInClassA A ι)
    (hA' : IsInClassA A' ι') (φ : NormalizedCocycle K L)
    (e : (L ≃ₐ[K] L) → Aˣ) (f : (L ≃ₐ[K] L) → A'ˣ)
    (he : ∀ σ a, (e σ : A) * ι a = ι (σ a) * e σ)
    (he2 : ∀ σ τ, (e σ : A) * e τ = ι (φ (σ, τ)) * e (σ * τ))
    (hf : ∀ σ a, (f σ : A') * ι' a = ι' (σ a) * f σ)
    (hf2 : ∀ σ τ, (f σ : A') * f τ = ι' (φ (σ, τ)) * f (σ * τ)) :
    Nonempty (A ≃ₐ[K] A') := by
  classical
  have he1 := cocycle_e_one ι φ e he2
  have hf1 := cocycle_e_one ι' φ f hf2
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : A ≃ₗ[K] A', ∀ σ a, Ψ (ι a * e σ) = ι' a * f σ := by
    refine ⟨(LinearEquiv.ofBijective _ (coeffMap_bijective ι hA e he)).symm.trans
      (LinearEquiv.ofBijective _ (coeffMap_bijective ι' hA' f hf)), fun σ a => ?_⟩
    have h1 : ι a * (e σ : A) =
        LinearEquiv.ofBijective _ (coeffMap_bijective ι hA e he) (Pi.single σ a) :=
      (coeffMap_single ι e σ a).symm
    rw [LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_apply]
    exact coeffMap_single ι' f σ a
  have hpure : ∀ σ a τ b, Ψ ((ι a * e σ) * (ι b * e τ)) = Ψ (ι a * e σ) * Ψ (ι b * e τ) := by
    intro σ a τ b
    have h1 : (ι a * (e σ : A)) * (ι b * e τ) = ι (a * σ b * φ (σ, τ)) * e (σ * τ) := by
      calc (ι a * (e σ : A)) * (ι b * e τ) = ι a * ((e σ * ι b) * e τ) := by simp only [mul_assoc]
        _ = ι a * ((ι (σ b) * e σ) * e τ) := by rw [he]
        _ = ι a * (ι (σ b) * (e σ * e τ)) := by simp only [mul_assoc]
        _ = ι a * (ι (σ b) * (ι (φ (σ, τ)) * e (σ * τ))) := by rw [he2]
        _ = _ := by simp only [map_mul, mul_assoc]
    have h2 : (ι' a * (f σ : A')) * (ι' b * f τ) = ι' (a * σ b * φ (σ, τ)) * f (σ * τ) := by
      calc (ι' a * (f σ : A')) * (ι' b * f τ) = ι' a * ((f σ * ι' b) * f τ) := by
            simp only [mul_assoc]
        _ = ι' a * ((ι' (σ b) * f σ) * f τ) := by rw [hf]
        _ = ι' a * (ι' (σ b) * (f σ * f τ)) := by simp only [mul_assoc]
        _ = ι' a * (ι' (σ b) * (ι' (φ (σ, τ)) * f (σ * τ))) := by rw [hf2]
        _ = _ := by simp only [map_mul, mul_assoc]
    rw [h1, hΨ, hΨ, hΨ, h2]
  have hmul : ∀ x y : A, Ψ (x * y) = Ψ x * Ψ y := by
    intro x y
    obtain ⟨c, hc, -⟩ := lemma_3_12 A ι hA e he x
    obtain ⟨d, hd, -⟩ := lemma_3_12 A ι hA e he y
    subst hc hd
    simp only [Finset.sum_mul_sum, map_sum, hpure]
  have hone : Ψ 1 = 1 := by
    have := hΨ 1 1
    simpa [he1, hf1] using this
  exact ⟨AlgEquiv.ofLinearEquiv Ψ hone hmul⟩

/-- Theorem 3.11 of Milne, the map $A \mapsto \varphi(A)$ is well defined on isomorphism classes
and its fibres are the isomorphism classes: if $\varphi$ is attached to $A$ and $\varphi'$ to $A'$
(both in $\mathcal A(L/K)$), then $A \cong A'$ as $K$-algebras if and only if $\varphi$ and
$\varphi'$ are cohomologous. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Thm. 3.11 (fibres), p. 135"]
theorem thm_3_11_fibres [IsGalois K L] (A A' : Type u) [Ring A] [Algebra K A] [Ring A']
    [Algebra K A'] (ι : L →ₐ[K] A) (ι' : L →ₐ[K] A') (hA : IsInClassA A ι)
    (hA' : IsInClassA A' ι') (φ φ' : NormalizedCocycle K L) (hφ : IsCocycleOf A ι φ)
    (hφ' : IsCocycleOf A' ι' φ') :
    Nonempty (A ≃ₐ[K] A') ↔ NormalizedCocycle.Cohomologous φ φ' := by
  classical
  obtain ⟨e, he, he2⟩ := hφ
  obtain ⟨e', he', he2'⟩ := hφ'
  haveI := hA.isCentral
  haveI := hA.isSimpleRing
  haveI := hA.finiteDimensional
  haveI := hA'.isCentral
  haveI := hA'.isSimpleRing
  haveI := hA'.finiteDimensional
  constructor
  · rintro ⟨h⟩
    obtain ⟨b, hb⟩ := thm_2_10 (K := K) L A' ι' (h.toAlgHom.comp ι)
    have hb' : ∀ a, ι' a = b * h (ι a) * ↑b⁻¹ := fun a => by simpa using hb a
    obtain ⟨f, hfval⟩ : ∃ f : (L ≃ₐ[K] L) → A'ˣ,
        ∀ σ, (f σ : A') = b * h (e σ) * ↑b⁻¹ :=
      ⟨fun σ => b * Units.map (h : A →* A') (e σ) * b⁻¹, fun σ => by simp⟩
    have hcc : ∀ x y : A', (b * x * ↑b⁻¹) * (b * y * ↑b⁻¹) = b * (x * y) * (↑b⁻¹ : A') := by
      intro x y
      simp [mul_assoc]
    refine cohomologous_of_two_families ι' hA' φ φ' e' f he' he2' (fun σ a => ?_)
      (fun σ τ => ?_)
    · have hh := congrArg h (he σ a)
      simp only [map_mul] at hh
      rw [hfval, hb' a, hb' (σ a), hcc, hcc, hh]
    · have hh := congrArg h (he2 σ τ)
      simp only [map_mul] at hh
      rw [hfval, hfval, hfval, hb' (φ (σ, τ)), hcc, hcc, hh]
  · intro hc
    obtain ⟨x, hx⟩ := hc
    obtain ⟨f, hfval⟩ : ∃ f : (L ≃ₐ[K] L) → A'ˣ, ∀ σ, (f σ : A') = ι' (x σ : L) * e' σ :=
      ⟨fun σ => Units.map (ι' : L →* A') (x σ) * e' σ, fun σ => by simp⟩
    have hxx : ∀ σ τ, (x σ : L) * σ (x τ : L) * (φ' (σ, τ) : L) = (φ (σ, τ) : L) * x (σ * τ) := by
      intro σ τ
      have h := congrArg Units.val (hx σ τ)
      have hs : ((σ • x τ : Lˣ) : L) = σ (x τ : L) := rfl
      simp only [Units.val_mul, Units.val_div_eq_div_val, hs] at h
      have hn1 := (x (σ * τ)).ne_zero
      have hn2 := (φ' (σ, τ)).ne_zero
      field_simp at h
      linear_combination h
    refine nonempty_algEquiv_of_two_families ι ι' hA hA' φ e f he he2 (fun σ a => ?_)
      (fun σ τ => ?_)
    · rw [hfval, mul_assoc, he', ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm]
    · rw [hfval, hfval, hfval]
      calc (ι' (x σ : L) * e' σ) * (ι' (x τ : L) * e' τ)
          = ι' (x σ : L) * ((e' σ * ι' (x τ : L)) * e' τ) := by simp only [mul_assoc]
        _ = ι' (x σ : L) * ((ι' (σ (x τ : L)) * e' σ) * e' τ) := by rw [he']
        _ = ι' (x σ : L) * (ι' (σ (x τ : L)) * (e' σ * e' τ)) := by simp only [mul_assoc]
        _ = ι' (x σ : L) * (ι' (σ (x τ : L)) * (ι' (φ' (σ, τ)) * e' (σ * τ))) := by rw [he2']
        _ = ι' ((x σ : L) * σ (x τ : L) * (φ' (σ, τ) : L)) * e' (σ * τ) := by
            simp only [map_mul, mul_assoc]
        _ = ι' ((φ (σ, τ) : L) * x (σ * τ)) * e' (σ * τ) := by rw [hxx]
        _ = _ := by simp only [map_mul, mul_assoc]

/-- Theorem 3.11 of Milne, surjectivity: every normalized 2-cocycle is attached to the crossed
product $A(\varphi) \in \mathcal A(L/K)$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Thm. 3.11 (surjectivity), p. 135"]
theorem thm_3_11_surj [IsGalois K L] (φ : NormalizedCocycle K L) :
    IsInClassA (CrossedProduct φ) (CrossedProduct.incl φ) ∧
      IsCocycleOf (CrossedProduct φ) (CrossedProduct.incl φ) φ := by
  refine ⟨⟨CrossedProduct.isCentral φ, CrossedProduct.isSimpleRing φ, inferInstance,
    CrossedProduct.finrank_eq φ⟩, ?_⟩
  have hσσ : ∀ (σ : L ≃ₐ[K] L) (x : L), σ (σ⁻¹ x) = x := by
    intro σ x
    rw [← AlgEquiv.mul_apply, mul_inv_cancel]
    rfl
  have hσσ' : ∀ (σ : L ≃ₐ[K] L) (x : L), σ⁻¹ (σ x) = x := by
    intro σ x
    rw [← AlgEquiv.mul_apply, inv_mul_cancel]
    rfl
  have key1 : ∀ σ : L ≃ₐ[K] L, ((φ (σ⁻¹, σ) : Lˣ) : L) = σ⁻¹ ((φ (σ, σ⁻¹) : Lˣ) : L) := by
    intro σ
    have h := φ.cocycle σ⁻¹ σ σ⁻¹
    rw [inv_mul_cancel, mul_inv_cancel, NormalizedCocycle.one_left,
      NormalizedCocycle.one_right, one_mul, mul_one] at h
    have := congrArg Units.val h
    simpa using this
  let u : (L ≃ₐ[K] L) → (CrossedProduct φ)ˣ := fun σ =>
    ⟨CrossedProduct.single φ σ 1,
      CrossedProduct.single φ σ⁻¹ (σ⁻¹ (((φ (σ, σ⁻¹) : Lˣ) : L)⁻¹)), by
        rw [CrossedProduct.single_mul_single, mul_inv_cancel]
        show _ = CrossedProduct.single φ 1 1
        congr 1
        rw [hσσ, one_mul]
        exact inv_mul_cancel₀ (Units.ne_zero _), by
        rw [CrossedProduct.single_mul_single, inv_mul_cancel]
        show _ = CrossedProduct.single φ 1 1
        congr 1
        rw [key1, map_one, mul_one, map_inv₀]
        exact inv_mul_cancel₀ (by simp)⟩
  refine ⟨u, fun σ a => ?_, fun σ τ => ?_⟩
  · show CrossedProduct.single φ σ 1 * CrossedProduct.single φ 1 a =
      CrossedProduct.single φ 1 (σ a) * CrossedProduct.single φ σ 1
    rw [CrossedProduct.single_mul_single, CrossedProduct.single_mul_single]
    simp [NormalizedCocycle.one_left, NormalizedCocycle.one_right]
  · show CrossedProduct.single φ σ 1 * CrossedProduct.single φ τ 1 =
      CrossedProduct.single φ 1 (φ (σ, τ) : Lˣ) * CrossedProduct.single φ (σ * τ) 1
    rw [CrossedProduct.single_mul_single, CrossedProduct.single_mul_single]
    simp [NormalizedCocycle.one_left]

end Cocycle

end Generic

end NumberFieldKB.MilneCFT.Ch4
