import NumberFieldKB.WeilBNT.PField
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Weil, *Basic Number Theory*, II.§5, Cor. of Thm. 3 and Def. 4 for $p$-fields: self-duality

$K$ is a $p$-field (`hK : IsPField K p`, commutative or not; `PField`). A *character* of $K$ is a continuous morphism of
the additive group of $K$ into the unit circle: `ψ : AddChar K Circle` with `Continuous ψ`.

* `weil_II_5_cor_thm3_right`, `weil_II_5_cor_thm3_left`: Cor. of Thm. 3. If $\chi$ is a non-trivial character of $K$,
  every character of $K$ can be written in one and only one way as $t\mapsto\chi(tx)$ with $x\in K$, and also as
  $t\mapsto\chi(yt)$ with $y\in K$.
* `weil_II_5_def4`: Def. 4. A non-trivial character $\chi$ has an order: there is a largest $\nu\in\mathbb Z$ with
  $\chi=1$ on $P^{-\nu}$ (`pPow hK (-ν)`).

*Proof* (not Weil's: Weil uses Pontryagin duality, which Mathlib lacks). A character is trivial on some $P^N$ (the circle
has no small subgroups and the $P^N$ are a basis of neighbourhoods of $0$), and not trivial on all $P^{-m}$. The map
$x\mapsto\chi(\cdot\,x)$ identifies $P^{a}/P^{b}$ with the characters of the finite group $P^{-b+c}/P^{-a+c}$ (counting:
both have $q^{b-a}$ elements and the map is injective), so the restrictions of a given character to the $P^{-m}$ are
of the form $\chi(\cdot\,x_m)$ with $x_m$ converging; the limit $x$ works on $K=\bigcup_mP^{-m}$.
-/

open Topology Filter
open scoped NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ}

/-- $P^n=\{x:\operatorname{mod}_K(x)\le q^{-n}\}$ for $n\in\mathbb Z$ (Def. 3). -/
def pPow (hK : IsPField K p) (n : ℤ) : Set K := {x | (modK K x : ℝ≥0) ≤ ((pq hK : ℝ≥0) ^ n)⁻¹}

/-! ### The filtration by the powers of the prime ideal -/

/-- The module of a $p$-field is greater than one on the residue field size. -/
theorem one_lt_pq (hK : IsPField K p) : (1 : ℝ≥0) < (pq hK : ℝ≥0) := by
  obtain ⟨f, hf, h⟩ := weil_I_4_thm6_residue hK
  have : 1 < pq hK := by rw [h]; exact Nat.one_lt_pow (by omega) hK.1.one_lt
  exact_mod_cast this

theorem pq_ne_zero (hK : IsPField K p) : (pq hK : ℝ≥0) ≠ 0 :=
  (lt_trans zero_lt_one (one_lt_pq hK)).ne'

theorem mem_pPow {hK : IsPField K p} {n : ℤ} {x : K} :
    x ∈ pPow hK n ↔ (modK K x : ℝ≥0) ≤ ((pq hK : ℝ≥0) ^ n)⁻¹ := Iff.rfl

/-- $P^b\subseteq P^a$ for $a\le b$. -/
theorem pPow_anti (hK : IsPField K p) {a b : ℤ} (h : a ≤ b) : pPow hK b ⊆ pPow hK a := by
  intro x hx
  have hq := one_lt_pq hK
  have hpos : 0 < (pq hK : ℝ≥0) ^ a := zpow_pos (lt_trans zero_lt_one hq) a
  exact le_trans (mem_pPow.1 hx) (inv_anti₀ hpos (zpow_le_zpow_right₀ hq.le h))

/-- $P^n$ as an additive subgroup of $K$. -/
def pPowAdd (hK : IsPField K p) (n : ℤ) : AddSubgroup K where
  carrier := pPow hK n
  add_mem' {a b} ha hb := le_trans (isUltrametricMod_of_isPField hK a b) (max_le ha hb)
  zero_mem' := by show modK K 0 ≤ _; rw [modK_zero]; exact bot_le
  neg_mem' {a} ha := by show modK K (-a) ≤ _; rw [modK_neg]; exact ha

theorem mem_pPowAdd {hK : IsPField K p} {n : ℤ} {x : K} : x ∈ pPowAdd hK n ↔ x ∈ pPow hK n :=
  Iff.rfl

/-- Every element lies in some $P^{-m}$. -/
theorem exists_nat_mem_pPow (hK : IsPField K p) (x : K) : ∃ m : ℕ, x ∈ pPow hK (-(m : ℤ)) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (modK K x) (one_lt_pq hK)
  refine ⟨n, ?_⟩
  rw [mem_pPow, zpow_neg, inv_inv, zpow_natCast]
  exact hn.le

/-- The $P^N$ form a basis of neighbourhoods of $0$. -/
theorem exists_nat_pPow_subset (hK : IsPField K p) {U : Set K} (hU : U ∈ 𝓝 (0 : K)) :
    ∃ N : ℕ, pPow hK (N : ℤ) ⊆ U := by
  obtain ⟨m, hm, hsub⟩ := hasBasis_nhds_zero_modK.mem_iff.1 hU
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hm (inv_lt_one_of_one_lt₀ (one_lt_pq hK))
  refine ⟨N, fun x hx => hsub ?_⟩
  have : ((pq hK : ℝ≥0) ^ (N : ℤ))⁻¹ = ((pq hK : ℝ≥0)⁻¹) ^ N := by rw [zpow_natCast, inv_pow]
  exact le_trans (mem_pPow.1 hx) (this ▸ hN.le)

/-- The circle has no small subgroups: if all powers of `z` have positive real part, `z = 1`. -/
theorem circle_eq_one_of_pow_re_pos {z : Circle} (h : ∀ n : ℕ, 0 < ((z ^ n : Circle) : ℂ).re) :
    z = 1 := by
  have hsq : ∀ w : Circle, (w : ℂ).re ^ 2 + (w : ℂ).im ^ 2 = 1 := by
    intro w
    have := Circle.normSq_coe w
    rw [Complex.normSq_apply] at this
    nlinarith
  have hre2 : ∀ w : Circle, ((w ^ 2 : Circle) : ℂ).re = 2 * (w : ℂ).re ^ 2 - 1 := by
    intro w
    have := hsq w
    have e : ((w ^ 2 : Circle) : ℂ) = (w : ℂ) ^ 2 := rfl
    rw [e, pow_two, Complex.mul_re]
    nlinarith
  by_contra hz
  set c := (z : ℂ).re with hc
  have hc1 : c < 1 := by
    have h1 := hsq z
    have h2 : c ≤ 1 := by nlinarith [sq_nonneg (z : ℂ).im]
    refine lt_of_le_of_ne h2 fun he => hz ?_
    have him : (z : ℂ).im = 0 := by
      have : (z : ℂ).im ^ 2 = 0 := by rw [← hc, he] at h1; nlinarith
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    apply Subtype.ext
    apply Complex.ext
    · simpa using he
    · simpa using him
  have key : ∀ k : ℕ, 2 ^ k * (1 - c) ≤ 1 - ((z ^ (2 ^ k) : Circle) : ℂ).re := by
    intro k
    induction k with
    | zero => simp [hc]
    | succ k ih =>
      have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by rw [← pow_mul, pow_succ]
      rw [e, hre2, pow_succ]
      have hpos := h (2 ^ k)
      have hs := hsq (z ^ (2 ^ k))
      have hle : ((z ^ (2 ^ k) : Circle) : ℂ).re ≤ 1 := by
        nlinarith [sq_nonneg ((z ^ (2 ^ k) : Circle) : ℂ).im]
      nlinarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (1 - c)) (one_lt_two (α := ℝ))
  have h1 : 0 < 1 - c := by linarith
  have h2 : 1 < 2 ^ k * (1 - c) := by
    rw [div_lt_iff₀ h1] at hk
    exact hk
  have := key k
  have := h (2 ^ k)
  linarith

/-- A continuous character is trivial on some $P^N$. -/
theorem exists_trivial_pPow (hK : IsPField K p) {ψ : AddChar K Circle} (hψ : Continuous ψ) :
    ∃ N : ℕ, ∀ t ∈ pPow hK (N : ℤ), ψ t = 1 := by
  have hU : ψ ⁻¹' {z : Circle | 0 < (z : ℂ).re} ∈ 𝓝 (0 : K) := by
    refine hψ.continuousAt.preimage_mem_nhds ?_
    rw [AddChar.map_zero_eq_one]
    exact IsOpen.mem_nhds (isOpen_lt continuous_const
      (Complex.continuous_re.comp continuous_subtype_val)) (by simp)
  obtain ⟨N, hN⟩ := exists_nat_pPow_subset hK hU
  refine ⟨N, fun t ht => ?_⟩
  apply circle_eq_one_of_pow_re_pos
  intro n
  have hmem : n • t ∈ pPowAdd hK (N : ℤ) := (pPowAdd hK (N : ℤ)).nsmul_mem ht n
  have := hN hmem
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at this
  rw [AddChar.map_nsmul_eq_pow] at this
  exact this

/-- A non-trivial character has an order (Def. 4). -/
theorem exists_order (hK : IsPField K p) {χ : AddChar K Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) :
    ∃ ν : ℤ, (∀ t ∈ pPow hK (-ν), χ t = 1) ∧ ∀ μ : ℤ, (∀ t ∈ pPow hK (-μ), χ t = 1) → μ ≤ ν := by
  obtain ⟨N, hN⟩ := exists_trivial_pPow hK hχ
  obtain ⟨s, hs⟩ : ∃ s, χ s ≠ 1 := by
    by_contra h
    push Not at h
    exact hχ1 (DFunLike.ext _ _ fun x => by rw [h x]; rfl)
  obtain ⟨m, hm⟩ := exists_nat_mem_pPow hK s
  obtain ⟨ν, h1, h2⟩ := Int.exists_greatest_of_bdd (P := fun ν : ℤ => ∀ t ∈ pPow hK (-ν), χ t = 1)
    ⟨m, fun z hz => by
      by_contra hlt
      push Not at hlt
      exact hs (hz s (pPow_anti hK (by omega) hm))⟩
    ⟨-(N : ℤ), fun t ht => hN t (by simpa using ht)⟩
  exact ⟨ν, h1, h2⟩

/-- Weil's pairings $(t,x)\mapsto tx$ and $(t,x)\mapsto xt$, abstractly: biadditive, multiplicative in the
module, continuous in the second variable and surjective in the first variable. -/
structure PFieldPairing (μ : K → K → K) : Prop where
  add_left : ∀ t u x, μ (t + u) x = μ t x + μ u x
  add_right : ∀ t x y, μ t (x + y) = μ t x + μ t y
  modK_eq : ∀ t x, modK K (μ t x) = modK K t * modK K x
  continuous_right : ∀ t, Continuous (μ t)
  surj : ∀ x, x ≠ 0 → ∀ s, ∃ t, μ t x = s

theorem pairing_right : PFieldPairing (K := K) (fun t x => t * x) where
  add_left t u x := add_mul t u x
  add_right t x y := mul_add t x y
  modK_eq t x := modK_mul t x
  continuous_right _ := continuous_const.mul continuous_id
  surj x hx s := ⟨s * x⁻¹, inv_mul_cancel_right₀ hx s⟩

theorem pairing_left : PFieldPairing (K := K) (fun t x => x * t) where
  add_left t u x := mul_add x t u
  add_right t x y := add_mul x y t
  modK_eq t x := by rw [modK_mul, mul_comm]
  continuous_right t := continuous_id.mul continuous_const
  surj x hx s := ⟨x⁻¹ * s, mul_inv_cancel_left₀ hx s⟩

namespace PFieldPairing

variable {μ : K → K → K} (h : PFieldPairing μ)

include h in
theorem map_zero_right (t : K) : μ t 0 = 0 := by
  have := h.add_right t 0 0
  simpa using this

include h in
theorem map_zero_left (x : K) : μ 0 x = 0 := by
  have := h.add_left 0 0 x
  simpa using this

include h in
theorem map_neg_right (t x : K) : μ t (-x) = -μ t x := by
  have := h.add_right t x (-x)
  rw [add_neg_cancel, h.map_zero_right] at this
  exact eq_neg_of_add_eq_zero_right this.symm

include h in
theorem map_sub_right (t x y : K) : μ t (x - y) = μ t x - μ t y := by
  rw [sub_eq_add_neg, h.add_right, h.map_neg_right, ← sub_eq_add_neg]

include h in
theorem eq_zero_of_char {χ : AddChar K Circle} (hχ1 : χ ≠ 1) {z : K} (hz : ∀ t, χ (μ t z) = 1) :
    z = 0 := by
  by_contra hz0
  apply hχ1
  refine DFunLike.ext _ _ fun s => ?_
  obtain ⟨t, ht⟩ := h.surj z hz0 s
  rw [← ht, hz t]
  rfl

end PFieldPairing

theorem mem_pPow_mul (hK : IsPField K p) {μ : K → K → K} (h : PFieldPairing μ) {a b : ℤ} {t x : K}
    (ht : t ∈ pPow hK a) (hx : x ∈ pPow hK b) : μ t x ∈ pPow hK (a + b) := by
  rw [mem_pPow, h.modK_eq, zpow_add₀ (pq_ne_zero hK), mul_inv]
  exact mul_le_mul' (mem_pPow.1 ht) (mem_pPow.1 hx)

/-! ### Indices -/

theorem modK_lt_one_iff_le (hK : IsPField K p) (x : K) :
    modK K x < 1 ↔ modK K x ≤ ((pq hK : ℝ≥0))⁻¹ := by
  have hq := one_lt_pq hK
  constructor
  · intro h
    by_cases hx : x = 0
    · subst hx; rw [modK_zero]; exact bot_le
    · obtain ⟨n, hn⟩ := weil_I_4_thm6_range hK hx
      rw [hn] at h ⊢
      have hn0 : n < 0 := by
        by_contra hn0
        push Not at hn0
        exact absurd h (not_lt.2 (one_le_zpow₀ hq.le hn0))
      rw [← zpow_neg_one]
      exact zpow_le_zpow_right₀ hq.le (by omega)
  · intro h; exact lt_of_le_of_lt h (inv_lt_one_of_one_lt₀ hq)

theorem pPow_shift_iff (hK : IsPField K p) {π : K} (hπ0 : π ≠ 0) (hπ : modK K π = (pq hK : ℝ≥0)⁻¹)
    (a k : ℤ) (x : K) : π ^ k * x ∈ pPow hK (a + k) ↔ x ∈ pPow hK a := by
  rw [mem_pPow, mem_pPow, modK_mul, modK_zpow hπ0, hπ, inv_zpow, zpow_add₀ (pq_ne_zero hK), mul_inv]
  have hpos : 0 < ((pq hK : ℝ≥0) ^ k)⁻¹ :=
    inv_pos.2 (zpow_pos (lt_trans zero_lt_one (one_lt_pq hK)) k)
  rw [mul_comm ((pq hK : ℝ≥0) ^ k)⁻¹ (modK K x)]
  constructor
  · intro h; exact le_of_mul_le_mul_right h hpos
  · intro h; gcongr

theorem relIndex_shift (hK : IsPField K p) (a b k : ℤ) :
    (pPowAdd hK (b + k)).relIndex (pPowAdd hK (a + k)) =
      (pPowAdd hK b).relIndex (pPowAdd hK a) := by
  obtain ⟨π, hπ0, hP, -⟩ := weil_I_4_thm6_prime hK
  have hπ := weil_I_4_thm6_modK_prime hK hπ0 hP
  have hne : π ^ k ≠ 0 := zpow_ne_zero k hπ0
  let f : K →+ K := AddMonoidHom.mulLeft (π ^ k)
  have hmap : ∀ c : ℤ, (pPowAdd hK c).map f = pPowAdd hK (c + k) := by
    intro c
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (pPow_shift_iff hK hπ0 hπ c k x).2 hx
    · intro hy
      refine ⟨(π ^ k)⁻¹ * y, ?_, mul_inv_cancel_left₀ hne y⟩
      show (π ^ k)⁻¹ * y ∈ pPow hK c
      rw [← pPow_shift_iff hK hπ0 hπ c k, mul_inv_cancel_left₀ hne]
      exact hy
  rw [← hmap a, ← hmap b]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (mul_right_injective₀ hne)

theorem relIndex_one_zero (hK : IsPField K p) :
    (pPowAdd hK 1).relIndex (pPowAdd hK 0) = pq hK := by
  have h0 : pPowAdd hK 0 = (pR hK).toAddSubgroup := by
    ext x
    show modK K x ≤ _ ↔ modK K x ≤ 1
    simp
  have h1 : (pPowAdd hK 1).addSubgroupOf (pR hK).toAddSubgroup = pPAdd hK := by
    ext x
    show modK K (x : K) ≤ ((pq hK : ℝ≥0) ^ (1 : ℤ))⁻¹ ↔ modK K (x : K) < 1
    rw [zpow_one]
    exact (modK_lt_one_iff_le hK x).symm
  rw [h0, AddSubgroup.relIndex, h1]
  rfl

theorem relIndex_succ (hK : IsPField K p) (a : ℤ) :
    (pPowAdd hK (a + 1)).relIndex (pPowAdd hK a) = pq hK := by
  have := relIndex_shift hK 0 1 a
  rw [zero_add, add_comm 1 a, relIndex_one_zero] at this
  exact this

theorem relIndex_pPow (hK : IsPField K p) (a : ℤ) (k : ℕ) :
    (pPowAdd hK (a + k)).relIndex (pPowAdd hK a) = pq hK ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; ring
    have h := AddSubgroup.relIndex_mul_relIndex (pPowAdd hK (a + ((k + 1 : ℕ) : ℤ)))
      (pPowAdd hK (a + k)) (pPowAdd hK a)
      (fun x hx => pPow_anti hK (by omega) hx) (fun x hx => pPow_anti hK (by omega) hx)
    rw [e, relIndex_succ, ih] at h
    rw [e, ← h, pow_succ, mul_comm]

/-! ### Finite duality -/

/-- A character of a quotient from a function on the group that is a character and trivial on the subgroup. -/
def quotChar {G : Type*} [AddCommGroup G] (H : AddSubgroup G) {M : Type*} [CommMonoid M] (g : G → M)
    (h0 : g 0 = 1) (hadd : ∀ a b, g (a + b) = g a * g b) (htriv : ∀ h ∈ H, g h = 1) :
    AddChar (G ⧸ H) M where
  toFun := Quotient.lift g (by
    intro a b hab
    have hmem : -a + b ∈ H := QuotientAddGroup.leftRel_apply.1 hab
    have := hadd a (-a + b)
    rw [add_neg_cancel_left, htriv _ hmem, mul_one] at this
    exact this.symm)
  map_zero_eq_one' := h0
  map_add_eq_mul' := by
    intro a b
    induction a using QuotientAddGroup.induction_on with
    | H a =>
      induction b using QuotientAddGroup.induction_on with
      | H b => exact hadd a b

/-- Finite duality: if `x ↦ χ(· x)` maps `A` onto characters of `B / H` with kernel contained in `A'`,
and `[A : A'] = [B : H]` is finite, then every character of `B` trivial on `H` is of this form. -/
theorem exists_dual_rep {μ : K → K → K} (hμ : PFieldPairing μ) {A A' B H : AddSubgroup K}
    (χ : AddChar K Circle)
    (hpair : ∀ t ∈ H, ∀ x ∈ A, χ (μ t x) = 1)
    (hker : ∀ x ∈ A, (∀ t ∈ B, χ (μ t x) = 1) → x ∈ A')
    (hcard : A'.relIndex A = H.relIndex B) (hfin : H.relIndex B ≠ 0)
    {ψ : AddChar K Circle} (hψ : ∀ t ∈ H, ψ t = 1) :
    ∃ x ∈ A, ∀ t ∈ B, ψ t = χ (μ t x) := by
  classical
  set HB : AddSubgroup B := H.addSubgroupOf B with hHB
  have : Finite (B ⧸ HB) := Nat.finite_of_card_ne_zero hfin
  let Θ : A →+ AddChar (B ⧸ HB) Circle :=
    { toFun := fun x => quotChar HB (fun b : B => χ (μ b.1 x.1))
        (by simp [hμ.map_zero_left])
        (fun a b => by simp [hμ.add_left, AddChar.map_add_eq_mul])
        (fun h hh => hpair h.1 hh x.1 x.2)
      map_zero' := by
        refine DFunLike.ext _ _ fun q => ?_
        induction q using QuotientAddGroup.induction_on with
        | H b =>
          show χ (μ b.1 (0 : A).1) = 1
          simp [hμ.map_zero_right]
      map_add' := by
        intro x y
        refine DFunLike.ext _ _ fun q => ?_
        induction q using QuotientAddGroup.induction_on with
        | H b =>
          show χ (μ b.1 (x + y : A).1) = χ (μ b.1 x.1) * χ (μ b.1 y.1)
          rw [← AddChar.map_add_eq_mul, ← hμ.add_right]
          rfl }
  let ψb : AddChar (B ⧸ HB) Circle := quotChar HB (fun b : B => ψ b.1) (by simp)
    (fun a b => by simp [AddChar.map_add_eq_mul]) (fun h hh => hψ h.1 hh)
  have hcardY : Nat.card (AddChar (B ⧸ HB) Circle) = H.relIndex B := by
    have := Fintype.ofFinite (B ⧸ HB)
    rw [Nat.card_congr (AddChar.circleEquivComplex (α := B ⧸ HB)).toEquiv, Nat.card_eq_fintype_card,
      AddChar.card_eq, ← Nat.card_eq_fintype_card]
    rfl
  have : Finite (AddChar (B ⧸ HB) Circle) := Nat.finite_of_card_ne_zero (hcardY ▸ hfin)
  have hker' : Θ.ker ≤ A'.addSubgroupOf A := by
    intro x hx
    have hx0 : Θ x = 0 := hx
    rw [AddSubgroup.mem_addSubgroupOf]
    apply hker x.1 x.2
    intro t ht
    have := DFunLike.congr_fun hx0 (QuotientAddGroup.mk ⟨t, ht⟩)
    exact this
  have hdvd : (A'.addSubgroupOf A).index ∣ Θ.ker.index := AddSubgroup.index_dvd_of_le hker'
  rw [AddSubgroup.index_ker] at hdvd
  have h1 : (A'.addSubgroupOf A).index = H.relIndex B := hcard
  have hle : Nat.card Θ.range ≤ Nat.card (AddChar (B ⧸ HB) Circle) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have hpos : 0 < Nat.card Θ.range := Nat.card_pos
  have heq : Nat.card Θ.range = Nat.card (AddChar (B ⧸ HB) Circle) := by
    refine le_antisymm hle ?_
    rw [hcardY, ← h1]
    exact Nat.le_of_dvd hpos (h1 ▸ hdvd)
  have htop := AddSubgroup.eq_top_of_card_eq Θ.range heq
  have hmem : ψb ∈ Θ.range := by rw [htop]; trivial
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x.1, x.2, fun t ht => ?_⟩
  have := DFunLike.congr_fun hx (QuotientAddGroup.mk ⟨t, ht⟩)
  exact this.symm

/-- The representation theorem on the level of the finite quotients. -/
theorem exists_rep_level (hK : IsPField K p) {μ : K → K → K} (hμ : PFieldPairing μ)
    {χ : AddChar K Circle} {ν : ℤ} (hν1 : ∀ t ∈ pPow hK (-ν), χ t = 1)
    (hν2 : ∀ m : ℤ, (∀ t ∈ pPow hK (-m), χ t = 1) → m ≤ ν)
    {ψ : AddChar K Circle} {N : ℕ} (hψ : ∀ t ∈ pPow hK (N : ℤ), ψ t = 1) (m : ℕ) :
    ∃ x ∈ pPow hK (-(N : ℤ) - ν), ∀ t ∈ pPow hK (-(m : ℤ)), ψ t = χ (μ t x) := by
  have hq := one_lt_pq hK
  have hcardA : (pPowAdd hK ((m : ℤ) - ν)).relIndex (pPowAdd hK (-(N : ℤ) - ν)) = pq hK ^ (m + N) := by
    have := relIndex_pPow hK (-(N : ℤ) - ν) (m + N)
    rwa [show -(N : ℤ) - ν + ((m + N : ℕ) : ℤ) = (m : ℤ) - ν by push_cast; ring] at this
  have hcardB : (pPowAdd hK (N : ℤ)).relIndex (pPowAdd hK (-(m : ℤ))) = pq hK ^ (m + N) := by
    have := relIndex_pPow hK (-(m : ℤ)) (m + N)
    rwa [show -(m : ℤ) + ((m + N : ℕ) : ℤ) = (N : ℤ) by push_cast; ring] at this
  have hq1 : 1 < pq hK := by exact_mod_cast hq
  refine exists_dual_rep (A := pPowAdd hK (-(N : ℤ) - ν)) (A' := pPowAdd hK ((m : ℤ) - ν))
    (B := pPowAdd hK (-(m : ℤ))) (H := pPowAdd hK (N : ℤ)) hμ χ ?_ ?_
    (hcardA.trans hcardB.symm) ?_ hψ
  · intro t ht x hx
    have := mem_pPow_mul hK hμ ht hx
    rw [show (N : ℤ) + (-(N : ℤ) - ν) = -ν by ring] at this
    exact hν1 _ this
  · intro x hx hall
    by_contra hxA'
    have hx0 : x ≠ 0 := fun h => hxA' (h ▸ (pPowAdd hK ((m : ℤ) - ν)).zero_mem)
    obtain ⟨n, hn⟩ := weil_I_4_thm6_range hK hx0
    have hnot : ¬ modK K x ≤ ((pq hK : ℝ≥0) ^ ((m : ℤ) - ν))⁻¹ := hxA'
    have hn1 : ν - m + 1 ≤ n := by
      by_contra hlt
      push Not at hlt
      apply hnot
      rw [hn, ← zpow_neg]
      exact zpow_le_zpow_right₀ hq.le (by omega)
    have hs : ¬ ∀ t ∈ pPow hK (-(ν + 1)), χ t = 1 := fun h =>
      absurd (hν2 _ h) (by omega)
    push Not at hs
    obtain ⟨s, hs1, hs2⟩ := hs
    obtain ⟨t, ht⟩ := hμ.surj x hx0 s
    have hmods : modK K s ≤ (pq hK : ℝ≥0) ^ (ν + 1) := by
      have := mem_pPow.1 hs1
      rwa [zpow_neg, inv_inv] at this
    have hm : modK K t * modK K x = modK K s := by rw [← hμ.modK_eq, ht]
    rw [hn] at hm
    have htmem : t ∈ pPow hK (-(m : ℤ)) := by
      rw [mem_pPow, zpow_neg, inv_inv]
      have hposn : 0 < (pq hK : ℝ≥0) ^ (ν - m + 1) := zpow_pos (lt_trans zero_lt_one hq) _
      have h2 : (pq hK : ℝ≥0) ^ (ν - m + 1) ≤ (pq hK : ℝ≥0) ^ n := zpow_le_zpow_right₀ hq.le hn1
      have h3 : modK K t * (pq hK : ℝ≥0) ^ (ν - m + 1) ≤
          (pq hK : ℝ≥0) ^ (m : ℤ) * (pq hK : ℝ≥0) ^ (ν - m + 1) := by
        calc modK K t * (pq hK : ℝ≥0) ^ (ν - m + 1) ≤ modK K t * (pq hK : ℝ≥0) ^ n := by gcongr
          _ = modK K s := hm
          _ ≤ (pq hK : ℝ≥0) ^ (ν + 1) := hmods
          _ = (pq hK : ℝ≥0) ^ (m : ℤ) * (pq hK : ℝ≥0) ^ (ν - m + 1) := by
            rw [← zpow_add₀ (pq_ne_zero hK)]; congr 1; ring
      exact le_of_mul_le_mul_right h3 hposn
    exact hs2 (by rw [← ht]; exact hall t htmem)
  · rw [hcardB]; exact pow_ne_zero _ (by omega)

/-- Representation and uniqueness for an abstract pairing. -/
theorem exists_unique_rep (hK : IsPField K p) {μ : K → K → K} (hμ : PFieldPairing μ)
    {χ : AddChar K Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) {ψ : AddChar K Circle}
    (hψ : Continuous ψ) : ∃! x : K, ∀ t, ψ t = χ (μ t x) := by
  obtain ⟨ν, hν1, hν2⟩ := exists_order hK hχ hχ1
  obtain ⟨N, hN⟩ := exists_trivial_pPow hK hψ
  choose xs hxsC hxs using exists_rep_level hK hμ hν1 hν2 hN
  have hC : IsCompact (pPow hK (-(N : ℤ) - ν)) := isCompact_modK_le _
  obtain ⟨x, -, hx⟩ := hC.exists_mapClusterPt (f := (atTop : Filter ℕ)) (u := xs)
    (Filter.tendsto_principal.2 (Filter.Eventually.of_forall hxsC))
  have hex : ∀ t, ψ t = χ (μ t x) := by
    intro t
    obtain ⟨m0, hm0⟩ := exists_nat_mem_pPow hK t
    have hclosed : IsClosed {y : K | χ (μ t y) = ψ t} :=
      isClosed_eq (hχ.comp (hμ.continuous_right t)) continuous_const
    have := hclosed.mem_of_mapClusterPt hx (by
      filter_upwards [eventually_ge_atTop m0] with m hm
      exact (hxs m t (pPow_anti hK (by omega) hm0)).symm)
    exact this.symm
  refine ⟨x, hex, fun y hy => ?_⟩
  have hz : y - x = 0 := by
    refine hμ.eq_zero_of_char hχ1 fun t => ?_
    rw [hμ.map_sub_right, AddChar.map_sub_eq_div, ← hy, ← hex]
    exact div_self' _
  exact sub_eq_zero.1 hz

@[kb "weil1973bnt" "Ch. II, §5, Cor. of Thm. 3 (p-fields, right multiplication)"]
theorem weil_II_5_cor_thm3_right (hK : IsPField K p) {χ : AddChar K Circle} (hχ : Continuous χ)
    (hχ1 : χ ≠ 1) {ψ : AddChar K Circle} (hψ : Continuous ψ) : ∃! x : K, ∀ t, ψ t = χ (t * x) :=
  exists_unique_rep hK pairing_right hχ hχ1 hψ

@[kb "weil1973bnt" "Ch. II, §5, Cor. of Thm. 3 (p-fields, left multiplication)"]
theorem weil_II_5_cor_thm3_left (hK : IsPField K p) {χ : AddChar K Circle} (hχ : Continuous χ)
    (hχ1 : χ ≠ 1) {ψ : AddChar K Circle} (hψ : Continuous ψ) : ∃! y : K, ∀ t, ψ t = χ (y * t) :=
  exists_unique_rep hK pairing_left hχ hχ1 hψ

/-- Def. 4: the order of a non-trivial character, the largest $\nu$ with $\chi=1$ on $P^{-\nu}$. -/
@[kb "weil1973bnt" "Ch. II, §5, Def. 4 (the order of a character exists)"]
theorem weil_II_5_def4 (hK : IsPField K p) {χ : AddChar K Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) :
    ∃ ν : ℤ, (∀ t ∈ pPow hK (-ν), χ t = 1) ∧ ∀ μ : ℤ, (∀ t ∈ pPow hK (-μ), χ t = 1) → μ ≤ ν :=
  exists_order hK hχ hχ1

end NumberFieldKB.WeilBNT.FieldModule
