import NumberFieldKB.MilneEC.Ch5bModularity
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Topology.Filter

/-!
# Milne, *Elliptic Curves*, Chapter V, Sections 8–9: $\mathrm{GL}_2(\mathbb F_3)$ and Fermat's Last Theorem

Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, Section 8 (pdf p. 233) and Section 9 "Fermat, at last"
(pp. 234–235).

* p. 233 (running text): $\mathrm{GL}_2(\mathbb F_3)$ has order $8 \cdot 6 = 48$ (`card_GL_two_ZMod_three`).
* p. 235 (running text): "$X_0(2)$ has genus $0$, and so there is no such cusp form": $S_2(\Gamma_0(2)) = 0$
  (`cuspForm_Gamma0_two_eq_zero`), proved from Mathlib's norm of modular forms and the level-one dimension formula
  ($S_6(\mathrm{SL}_2(\mathbb Z)) = 0$), not from the genus.
* p. 218 and p. 235: the Frey curve of a solution of $X^\ell + Y^\ell = Z^\ell$ is a semistable elliptic curve
  (`freyCurve_isElliptic`, `freyCurve_isSemistable`, from Exercise 4.21).
* p. 235: Ribet's theorem as used for the Frey curve (named statement `RibetFrey`).
* p. 235, "Wiles's theorem proves that $E$ doesn't exist": Fermat's Last Theorem from the theorem of Wiles and
  Taylor and `RibetFrey` (`fermatLastTheorem_of_wilesTaylor_ribet`), with the exponents $3$, $4$ from Mathlib.
-/

open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

namespace NumberFieldKB.MilneEC.Vb

/-- Milne, *EC*, V.8, p. 233 (running text): $\mathrm{GL}_2(\mathbb F_3)$ has order $8 \cdot 6 = 48$. -/
@[kb "milne2006ec" "Ch. V, Section 8 (pdf p. 233): |GL₂(F₃)| = 48"]
theorem card_GL_two_ZMod_three : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]

/-- Helper: a statement over the field with two elements, checked on all cases. -/
theorem zmod_two_aux (a b c d a' b' c' d' : ZMod 2) (hA : a * d - b * c = 1)
    (hB : a' * d' - b' * c' = 1) : c * a' + a * c' = 0 ↔ (a = a' ∧ c = c') := by
  revert a b c d a' b' c' d'
  decide

/-- Helper: $A^{-1}B \in \Gamma_0(2)$ iff the first columns of $A$ and $B$ agree modulo $2$. -/
theorem gamma0_two_mem_aux (A B : SL(2, ℤ)) :
    A⁻¹ * B ∈ Gamma0 2 ↔
      ((A 0 0 : ZMod 2) = (B 0 0 : ZMod 2) ∧ (A 1 0 : ZMod 2) = (B 1 0 : ZMod 2)) := by
  have hA := congrArg (Int.cast : ℤ → ZMod 2) A.det_coe
  have hB := congrArg (Int.cast : ℤ → ZMod 2) B.det_coe
  rw [Matrix.det_fin_two] at hA hB
  push_cast at hA hB
  rw [Gamma0_mem]
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  rw [← zmod_two_aux _ _ _ _ _ _ _ _ hA hB]

/-- Helper: the index of $\Gamma_0(2)$ in $\mathrm{SL}_2(\mathbb Z)$ is at most $4$ (it is $3$): the coset of $A$
is determined by the first column of $A$ modulo $2$. -/
theorem index_gamma0_two_le : (Gamma0 2).index ≤ 4 := by
  rw [Subgroup.index]
  let f : SL(2, ℤ) ⧸ Gamma0 2 → ZMod 2 × ZMod 2 :=
    Quotient.lift (fun A : SL(2, ℤ) => ((A 0 0 : ZMod 2), (A 1 0 : ZMod 2))) (by
      intro A B hAB
      have hAB := QuotientGroup.leftRel_apply.mp hAB
      obtain ⟨h1, h2⟩ := (gamma0_two_mem_aux A B).mp hAB
      simp [h1, h2])
  have : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn with | _ A =>
    induction y using Quotient.inductionOn with | _ B =>
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    apply (gamma0_two_mem_aux A B).mpr
    simpa [f, Prod.ext_iff] using hxy
  calc Nat.card (SL(2, ℤ) ⧸ Gamma0 2) ≤ Nat.card (ZMod 2 × ZMod 2) :=
        Nat.card_le_card_of_injective f this
    _ = 4 := by simp

/-- Helper: the relative index of $\Gamma_0(2)$ in the image of $\mathrm{SL}_2(\mathbb Z)$ in
$\mathrm{GL}_2(\mathbb R)$ is at most $4$. -/
theorem card_quotient_gamma0_two_le :
    Nat.card (𝒮ℒ ⧸ ((Gamma0 2 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ≤ 4 := by
  have h : (((Gamma0 2 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).relIndex 𝒮ℒ =
      (Gamma0 2).index := by
    rw [MonoidHom.range_eq_map]
    show (Subgroup.map (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ) (Gamma0 2)).relIndex
      (Subgroup.map (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ) ⊤) = _
    rw [Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective,
      Subgroup.relIndex_top_right]
  have h2 := index_gamma0_two_le
  rw [← h] at h2
  exact h2

open ModularForm SlashInvariantForm in
/-- Helper: every translate of a cusp form for $\Gamma_0(2)$ by an element of $\mathrm{SL}_2(\mathbb Z)$ vanishes at
$i\infty$. -/
theorem quotientFunc_isZeroAtImInfty (f : CuspForm (Gamma0 2) 2)
    (q : 𝒮ℒ ⧸ ((Gamma0 2 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :
    IsZeroAtImInfty (quotientFunc f q) := by
  induction q using Quotient.inductionOn with | _ h =>
  obtain ⟨h, γ, rfl⟩ := h
  rw [quotientFunc_mk]
  have := CuspFormClass.zero_at_infty_slash f γ⁻¹
  convert this using 1
  simp [SL_slash]
  rfl

/-- Milne, *EC*, V.9, p. 235 (running text: "$X_0(2)$ has genus 0, and so there is no such cusp form"): there is no
nonzero cusp form of weight $2$ for $\Gamma_0(2)$. -/
@[kb "milne2006ec" "Ch. V, Section 9 (pdf p. 235): S₂(Γ₀(2)) = 0"]
theorem cuspForm_Gamma0_two_eq_zero (f : CuspForm (Gamma0 2) 2) : f = 0 := by
  have hlt : (2 : ℤ) * Nat.card (𝒮ℒ ⧸ ((Gamma0 2 : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) < 12 := by
    have := card_quotient_gamma0_two_le
    omega
  let n := ModularForm.norm 𝒮ℒ f
  have hz : IsZeroAtImInfty (n : ℍ → ℂ) := by
    have : Nonempty (𝒮ℒ ⧸ ((Gamma0 2 : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := ⟨⟦1⟧⟩
    let := Fintype.ofFinite (𝒮ℒ ⧸ ((Gamma0 2 : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
    have key : Filter.Tendsto (fun τ => ∏ q, SlashInvariantForm.quotientFunc f q τ) atImInfty
        (nhds (∏ _q : (𝒮ℒ ⧸ ((Gamma0 2 : Subgroup SL(2, ℤ)) :
          Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ), (0 : ℂ))) :=
      tendsto_finsetProd _ (fun q _ => quotientFunc_isZeroAtImInfty f q)
    have e : (∏ _q : (𝒮ℒ ⧸ ((Gamma0 2 : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ), (0 : ℂ)) = 0 :=
      Finset.prod_eq_zero (i := (⟦1⟧ : (𝒮ℒ ⧸ ((Gamma0 2 : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))) (f := fun _ => (0 : ℂ)) (Finset.mem_univ _) rfl
    rw [e] at key
    have e2 : (n : ℍ → ℂ) = fun τ => ∏ q : (𝒮ℒ ⧸ ((Gamma0 2 : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ), SlashInvariantForm.quotientFunc f q τ := by
      ext τ
      simp [n, Finset.prod_apply]
    rw [e2]
    exact key
  have hc : (qExpansion 1 n).coeff 0 = 0 :=
    (qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero n one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex n one_mem_strictPeriods_SL)).trans
      hz.valueAtInfty_eq_zero
  have h0 : ModularForm.toCuspForm n hc = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve hlt) _
  have h1 : ModularForm.norm 𝒮ℒ f = 0 := by
    ext τ
    exact congr($h0 τ)
  have := (ModularForm.norm_eq_zero_iff 𝒮ℒ f).mp h1
  ext τ
  simpa using congr($this τ)

/-- The Frey curve of a solution with $\alpha\beta\gamma \ne 0$ is an elliptic curve ($\Delta \ne 0$ by
Exercise 4.21(a)). -/
theorem freyCurve_isElliptic {α β γ : ℤ} {ℓ : ℕ} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (h : α ^ ℓ + β ^ ℓ = γ ^ ℓ) : (freyCurve α γ ℓ).IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [exercise_4_21_a h]
  have hα' : (α : ℚ) ≠ 0 := by exact_mod_cast hα
  have hβ' : (β : ℚ) ≠ 0 := by exact_mod_cast hβ
  have hγ' : (γ : ℚ) ≠ 0 := by exact_mod_cast hγ
  positivity

/-- Milne, *EC*, V.9, p. 235 and V.5, p. 218: the Frey curve of Exercise 4.21 is semistable (it has at worst nodal
reduction everywhere, by Exercise 4.21(b)–(d)). -/
@[kb "milne2006ec" "Ch. V, Section 9 (pdf p. 235): the Frey curve is semistable"]
theorem freyCurve_isSemistable {α β γ : ℤ} {ℓ : ℕ} (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hγ0 : γ ≠ 0) (hℓ : 4 ≤ ℓ)
    (h : α ^ ℓ + β ^ ℓ = γ ^ ℓ) (hαβ : IsCoprime α β) (hαγ : IsCoprime α γ) (hβγ : IsCoprime β γ)
    (hγ : Even γ) (hα : α ^ ℓ ≡ -1 [ZMOD 4]) : IsSemistable (freyCurve α γ ℓ) := by
  intro p hp hadd
  by_cases hdiv : (p : ℤ) ∣ α * β * γ
  · by_cases hp2 : p = 2
    · subst hp2
      rcases exercise_4_21_d hα0 hβ0 hγ0 hℓ h hαβ hαγ hβγ hγ hα with h' | h'
      · exact WeierstrassCurve.HasGoodReduction.not_hasAdditiveReduction _ h' hadd
      · exact WeierstrassCurve.HasMultiplicativeReduction.not_hasAdditiveReduction _ h' hadd
    · rcases exercise_4_21_c hα0 hβ0 hγ0 (by omega) h hαβ hαγ hβγ p hp2 hdiv with h' | h'
      · exact WeierstrassCurve.HasGoodReduction.not_hasAdditiveReduction _ h' hadd
      · exact WeierstrassCurve.HasMultiplicativeReduction.not_hasAdditiveReduction _ h' hadd
  · exact WeierstrassCurve.HasGoodReduction.not_hasAdditiveReduction _ (exercise_4_21_b h p hdiv) hadd

/-- **Ribet's theorem for the Frey curve** (named statement; Milne, *EC*, V.9, p. 235, with Theorem 9.4 (Ribet and
others) and the "nontrivial facts about elliptic curves" quoted there: the representation $\bar\rho_0$ of $G$ on
$E(\bar{\mathbb Q})_\ell$ is irreducible, unramified for $p \ne 2, \ell$ and flat at $\ell$): for a solution of
$\alpha^\ell + \beta^\ell = \gamma^\ell$, $\ell \ge 5$ prime, in nonzero relatively prime integers normalized as in
Exercise 4.21(d), if the Frey curve is modular then $\bar\rho_0$ is modular for a cusp form of weight $2$ and
level $2$: there is a nonzero cusp form of weight $2$ for $\Gamma_0(2)$. -/
@[kb "milne2006ec" "Ch. V, Section 9 (pdf p. 235): Ribet's level lowering for the Frey curve (input)"]
structure RibetFrey : Prop where
  level_two : ∀ (α β γ : ℤ) (ℓ : ℕ), ℓ.Prime → 5 ≤ ℓ → α ≠ 0 → β ≠ 0 → γ ≠ 0 → α ^ ℓ + β ^ ℓ = γ ^ ℓ →
    IsCoprime α β → IsCoprime α γ → IsCoprime β γ → Even γ → α ^ ℓ ≡ -1 [ZMOD 4] →
    IsModularCurve (freyCurve α γ ℓ) → ∃ f : CuspForm (Gamma0 2) 2, f ≠ 0

/-- Helper: dividing by the greatest common divisor, a solution in nonzero integers gives one in pairwise relatively
prime nonzero integers (odd exponent). -/
theorem exists_pairwise_coprime_solution {ℓ : ℕ} (hℓ : Odd ℓ) {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (h : a ^ ℓ + b ^ ℓ = c ^ ℓ) :
    ∃ A B C : ℤ, A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧ A ^ ℓ + B ^ ℓ = C ^ ℓ ∧ IsCoprime A B ∧ IsCoprime A C ∧
      IsCoprime B C := by
  have hn : ℓ ≠ 0 := hℓ.pos.ne'
  obtain ⟨c', rfl⟩ : ∃ c', c = -c' := ⟨-c, by simp⟩
  rw [hℓ.neg_pow] at h
  have hc0 : c' ≠ 0 := neg_ne_zero.mp hc
  let s : Finset ℤ := {a, b, c'}
  let d := s.gcd id
  obtain ⟨A, hA⟩ : d ∣ a := Finset.gcd_dvd (by simp [s])
  obtain ⟨B, hB⟩ : d ∣ b := Finset.gcd_dvd (by simp [s])
  obtain ⟨C, hC⟩ : d ∣ c' := Finset.gcd_dvd (by simp [s])
  simp only [hA, hB, hC, mul_ne_zero_iff, mul_pow] at ha hb hc0 h
  have h : A ^ ℓ + B ^ ℓ + C ^ ℓ = 0 := by
    have : d ^ ℓ * (A ^ ℓ + B ^ ℓ + C ^ ℓ) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero ℓ ha.1)
  have hg : ({A, B, C} : Finset ℤ).gcd id = 1 := by
    rw [← Finset.normalize_gcd, normalize_eq_one]
    refine isUnit_of_associated_mul ?_ ha.1
    grw [← Finset.gcd_mul_left', Finset.gcd_eq_gcd_image]
    refine .of_eq ?_
    congr
    simp [s, hA, hB, hC]
  have hAB : IsCoprime A B := isCoprime_of_gcd_eq_one_of_FLT hg h
  have hApow : IsCoprime (A ^ ℓ) (B ^ ℓ) := hAB.pow
  have h : A ^ ℓ + B ^ ℓ = (-C) ^ ℓ := by
    rw [hℓ.neg_pow]
    linarith
  replace hAB : IsCoprime A B := hAB
  refine ⟨A, B, -C, ha.2, hb.2, neg_ne_zero.mpr hc0.2, h, hAB, ?_, ?_⟩
  · have : IsCoprime (A ^ ℓ) ((-C) ^ ℓ) := by
      rw [← h]
      simpa [add_comm] using hApow.add_mul_left_right 1
    exact (IsCoprime.pow_iff hℓ.pos hℓ.pos).mp this
  · have : IsCoprime (B ^ ℓ) ((-C) ^ ℓ) := by
      rw [← h]
      simpa [add_comm] using hApow.symm.add_mul_left_right 1
    exact (IsCoprime.pow_iff hℓ.pos hℓ.pos).mp this

/-- Helper: an integer relatively prime to an even integer is odd. -/
theorem odd_of_isCoprime_even {a b : ℤ} (hab : IsCoprime a b) (hb : Even b) : Odd a := by
  rw [← Int.not_even_iff_odd]
  intro ha
  have := Int.isUnit_iff.mp (hab.isUnit_of_dvd' (even_iff_two_dvd.mp ha) (even_iff_two_dvd.mp hb))
  omega

/-- Helper: an odd power (odd exponent) of an odd integer is $\equiv \pm 1 \pmod 4$. -/
theorem odd_pow_modEq_four {ℓ : ℕ} (hℓ : Odd ℓ) {x : ℤ} (hx : Odd x) :
    x ^ ℓ ≡ 1 [ZMOD 4] ∨ x ^ ℓ ≡ -1 [ZMOD 4] := by
  have h4 : x % 4 = 1 ∨ x % 4 = 3 := by
    obtain ⟨k, hk⟩ := hx
    omega
  rcases h4 with h4 | h4
  · left
    have : x ≡ 1 [ZMOD 4] := by simpa [Int.ModEq] using h4
    simpa using this.pow ℓ
  · right
    have : x ≡ -1 [ZMOD 4] := by
      unfold Int.ModEq
      omega
    simpa [hℓ.neg_one_pow] using this.pow ℓ

/-- Helper: the last step of the normalization, for $\gamma$ even. -/
theorem exists_normalized_of_even {ℓ : ℕ} (hℓ : Odd ℓ) (hℓ2 : 2 ≤ ℓ) {α β γ : ℤ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hγ : γ ≠ 0) (h : α ^ ℓ + β ^ ℓ = γ ^ ℓ) (hαβ : IsCoprime α β) (hαγ : IsCoprime α γ)
    (hβγ : IsCoprime β γ) (he : Even γ) :
    ∃ α β γ : ℤ, α ≠ 0 ∧ β ≠ 0 ∧ γ ≠ 0 ∧ α ^ ℓ + β ^ ℓ = γ ^ ℓ ∧ IsCoprime α β ∧ IsCoprime α γ ∧
      IsCoprime β γ ∧ Even γ ∧ α ^ ℓ ≡ -1 [ZMOD 4] := by
  have hα_odd := odd_of_isCoprime_even hαγ he
  have hβ_odd := odd_of_isCoprime_even hβγ he
  have h4 : (4 : ℤ) ∣ γ ^ ℓ := by
    obtain ⟨k, hk⟩ := he
    have : γ = 2 * k := by omega
    rw [this, mul_pow]
    exact Dvd.dvd.mul_right ((by norm_num : (4 : ℤ) ∣ 2 ^ 2).trans (pow_dvd_pow 2 hℓ2)) _
  rw [← h] at h4
  rcases odd_pow_modEq_four hℓ hα_odd with h1 | h1
  · rcases odd_pow_modEq_four hℓ hβ_odd with h2 | h2
    · exfalso
      have := h1.add h2
      unfold Int.ModEq at this
      omega
    · exact ⟨β, α, γ, hβ, hα, hγ, by rw [← h]; ring, hαβ.symm, hβγ, hαγ, he, h2⟩
  · exact ⟨α, β, γ, hα, hβ, hγ, h, hαβ, hαγ, hβγ, he, h1⟩

/-- Normalization of a solution (Milne, *EC*, V, Exercise 4.21(d), hint): a solution of $a^\ell + b^\ell = c^\ell$ in
nonzero integers, $\ell$ an odd prime, gives one in nonzero pairwise relatively prime integers with $\gamma$ even and
$\alpha^\ell \equiv -1 \pmod 4$. -/
theorem exists_normalized_solution {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (h : a ^ ℓ + b ^ ℓ = c ^ ℓ) :
    ∃ α β γ : ℤ, α ≠ 0 ∧ β ≠ 0 ∧ γ ≠ 0 ∧ α ^ ℓ + β ^ ℓ = γ ^ ℓ ∧ IsCoprime α β ∧ IsCoprime α γ ∧
      IsCoprime β γ ∧ Even γ ∧ α ^ ℓ ≡ -1 [ZMOD 4] := by
  have hodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have h2 : 2 ≤ ℓ := hℓ.two_le
  obtain ⟨A, B, C, hA, hB, hC, h, hAB, hAC, hBC⟩ :=
    exists_pairwise_coprime_solution hodd ha hb hc h
  by_cases hAe : Even A
  · -- `A` even: `B^ℓ + (-C)^ℓ = (-A)^ℓ`
    refine exists_normalized_of_even hodd h2 hB (neg_ne_zero.mpr hC) (neg_ne_zero.mpr hA) ?_
      hBC.neg_right hAB.symm.neg_right hAC.symm.neg_left.neg_right (by simpa using hAe)
    rw [hodd.neg_pow, hodd.neg_pow]
    linarith
  · by_cases hBe : Even B
    · refine exists_normalized_of_even hodd h2 hA (neg_ne_zero.mpr hC) (neg_ne_zero.mpr hB) ?_
        hAC.neg_right hAB.neg_right hBC.symm.neg_left.neg_right (by simpa using hBe)
      rw [hodd.neg_pow, hodd.neg_pow]
      linarith
    · refine exists_normalized_of_even hodd h2 hA hB hC h hAB hAC hBC ?_
      rw [Int.not_even_iff_odd] at hAe hBe
      have : Even (C ^ ℓ) := by
        rw [← h]
        exact hAe.pow.add_odd hBe.pow
      exact (Int.even_pow.mp this).1

/-- **Fermat's Last Theorem** (Milne, *EC*, V.9, p. 235: "Wiles's theorem proves that $E$ doesn't exist"), from the
theorem of Wiles and Taylor (semistable curves are modular) and Ribet's theorem for the Frey curve; the exponents
$3$ and $4$ are Mathlib's `fermatLastTheoremThree` and `fermatLastTheoremFour`. -/
@[kb "milne2006ec" "Ch. V, Section 9 (pdf p. 235): Fermat's Last Theorem from Wiles-Taylor and Ribet"]
theorem fermatLastTheorem_of_wilesTaylor_ribet (hW : WilesTaylor) (hR : RibetFrey) : FermatLastTheorem := by
  refine FermatLastTheorem.of_odd_primes fun p hp hodd => ?_
  by_cases h3 : p = 3
  · subst h3
    exact fermatLastTheoremThree
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hodd (by decide)
  have h5 : 5 ≤ p := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := hodd
    omega
  intro a b c ha hb hc habc
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℤ) ≠ 0 := by exact_mod_cast hb
  have hc' : (c : ℤ) ≠ 0 := by exact_mod_cast hc
  have habcZ : (a : ℤ) ^ p + (b : ℤ) ^ p = (c : ℤ) ^ p := by exact_mod_cast habc
  obtain ⟨α, β, γ, hα, hβ, hγ, h, h1, h2, h3', he, hmod⟩ :=
    exists_normalized_solution hp hp2 ha' hb' hc' habcZ
  have hel := freyCurve_isElliptic hα hβ hγ h
  have hss := freyCurve_isSemistable hα hβ hγ (by omega) h h1 h2 h3' he hmod
  obtain ⟨f, hf⟩ := hR.level_two α β γ p hp h5 hα hβ hγ h h1 h2 h3' he hmod
    (hW.modular _ hel hss)
  exact hf (cuspForm_Gamma0_two_eq_zero f)

end NumberFieldKB.MilneEC.Vb
