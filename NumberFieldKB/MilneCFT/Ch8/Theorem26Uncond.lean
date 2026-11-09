import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangCor25
import NumberFieldKB.MilneCFT.Ch8.Theorem26Split
import NumberFieldKB.MilneCFT.Ch8.Theorem26Index
import NumberFieldKB.MilneCFT.Ch8.Theorem26Gen
import NumberFieldKB.MilneCFT.Ch4SkolemNoether

/-!
# Milne, *CFT*, VIII, Theorem 2.6 (period = index; cyclic algebras), unconditionally

**Proved here:** `T26.theorem2_6 : Theorem2_6 K`.

Let `D` be a central division algebra over a number field `K`, `[D : K] = d^2`, and `m` the order of `[D]` in `Br(K)`.
* `m ∣ d` (`T26.brClass_pow_eq_one`: period divides index, via Tau Ceti's corestriction).
* Corollary 2.5 (`GW.corollary2_5`, the Grunwald–Wang theorem) gives a cyclic `L/K` of degree `m` splitting `D`
  (`T26.exists_cyclic_splitsOver_of_corollary2_5`), so `d ∣ m` (`T26.dvd_finrank_of_splitsOver`). Hence `m^2 = [D : K]`.
* `L` has degree `d` and splits `D`, so it embeds in `D` (`Ch4.cor_3_7`) as a maximal subfield `L'`, its own
  centralizer (`Ch4.cor_3_4`). For a generator `σ` of `Gal(L'/K)`, Skolem–Noether (`Ch4.cor_2_11`) gives `β ∈ D^×` with
  `β α β⁻¹ = σ(α)`. Then `β^d` commutes with `L'` (as `σ^d = 1`), so lies in `L'`, and is fixed by `σ`, so lies in
  `K`. An element of `L'` commuting with `β` is fixed by `σ`, so lies in `K`; hence `L'` and `β` generate `D`
  (`T26.adjoin_eq_top`).
-/

open IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.T26

variable {K : Type} [Field K] [NumberField K]

/-- The dimension of a central division algebra is the square of the degree of a maximal subfield. -/
theorem exists_finrank_eq_sq (D : Type) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] : ∃ d : ℕ, Module.finrank K D = d ^ 2 := by
  obtain ⟨F, hF, hmax, -⟩ := Ch4.prop_3_8 (K := K) D
  exact ⟨_, (Ch4.cor_3_5 D F hF).1 hmax⟩

/-- **Period equals index.** -/
theorem orderOf_eq (D : Type) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] {d : ℕ} (hd : Module.finrank K D = d ^ 2) :
    orderOf (Ch4.BrauerGroup.mk (⟨.of K D⟩ : CSA.{0, 0} K)) = d := by
  obtain ⟨L, _, _, _, _, -, hdeg, hsplit⟩ :=
    exists_cyclic_splitsOver_of_corollary2_5 (GW.corollary2_5 (K := K)) D
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (brClass_pow_eq_one D hd)) ?_
  have := dvd_finrank_of_splitsOver D hd L hsplit
  rwa [hdeg] at this

/-- **Milne, CFT, VIII, Theorem 2.6**, unconditionally. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 2.6, p. 233"]
theorem theorem2_6 : Theorem2_6 K where
  order_eq D _ _ _ _ := by
    obtain ⟨d, hd⟩ := exists_finrank_eq_sq (K := K) D
    have h := orderOf_eq D hd
    rw [hd]
    exact congrArg (· ^ 2) h
  cyclic D _ _ _ _ := by
    obtain ⟨d, hd⟩ := exists_finrank_eq_sq (K := K) D
    have hm := orderOf_eq D hd
    obtain ⟨L, _, _, _, _, hcyc, hdeg, hsplit⟩ :=
      exists_cyclic_splitsOver_of_corollary2_5 (GW.corollary2_5 (K := K)) D
    rw [Ch7.brClass, hm] at hdeg
    -- `L` embeds in `D`
    have hsplit' : Ch4.IsSplitBy (K := K) L D := by
      have h := (Ch7.splitsOver_iff_baseChange_eq_one D L).1 hsplit
      exact (Ch4.mk_mem_relBrauer_iff L (⟨.of K D⟩ : CSA.{0, 0} K)).1 h
    obtain ⟨f⟩ := (Ch4.cor_3_7 D L hd hdeg).1 hsplit'
    set L' : Subalgebra K D := f.range with hL'def
    let e : L ≃ₐ[K] L' := AlgEquiv.ofInjective f f.toRingHom.injective
    have hL' : IsField L' := MulEquiv.isField (Field.toIsField L) e.symm.toMulEquiv
    letI : Field L' := hL'.toField
    have hfinL' : Module.finrank K L' = d := by rw [← e.toLinearEquiv.finrank_eq, hdeg]
    have hdim' : Module.finrank K D = Module.finrank K L' ^ 2 := by rw [hfinL', hd]
    haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by
      rw [hdeg]; exact Nat.pos_of_ne_zero (by
        rintro rfl
        have := Module.finrank_pos (R := K) (M := D)
        rw [hd] at this
        simp at this))
    haveI : IsGalois K L' := IsGalois.of_algEquiv e
    haveI : FiniteDimensional K L' := e.toLinearEquiv.finiteDimensional
    have hcyc' : IsCyclic (L' ≃ₐ[K] L') :=
      isCyclic_of_surjective (AlgEquiv.autCongr e).toMonoidHom (AlgEquiv.autCongr e).surjective
    have hcard : Nat.card (L' ≃ₐ[K] L') = Module.finrank K L' := by
      rw [← IsGalois.card_aut_eq_finrank]
    have hcent : Subalgebra.centralizer K (L' : Set D) = L' :=
      ((Ch4.cor_3_4 D L' hL').out 1 2).2 hdim'
    obtain ⟨σ, hσ⟩ := hcyc'.exists_generator
    have hσtop : Subgroup.zpowers σ = ⊤ := by
      rw [eq_top_iff]; intro g _; exact hσ g
    have hσord : orderOf σ = d := by
      rw [← hfinL', ← hcard]
      exact orderOf_eq_card_of_forall_mem_zpowers hσ
    obtain ⟨a, ha⟩ := Ch4.cor_2_11 D L' L' σ
    have hβ : ∀ α : L', (a : D) * (α : D) = (σ α : D) * a := by
      intro α
      rw [ha α, mul_assoc, mul_assoc, Units.inv_mul, mul_one]
    -- iterating: `a^k α = σ^k(α) a^k`
    have hβk : ∀ (k : ℕ) (α : L'), (a : D) ^ k * (α : D) = ((σ ^ k) α : D) * (a : D) ^ k := by
      intro k
      induction k with
      | zero => intro α; simp
      | succ k ih =>
        intro α
        rw [pow_succ', mul_assoc, ih α, ← mul_assoc, hβ, mul_assoc, pow_succ' σ k, AlgEquiv.mul_apply]
    -- elements fixed by `σ` lie in `K`
    have hfixK : ∀ ζ : L', σ ζ = ζ → ∃ γ : K, algebraMap K L' γ = ζ := by
      intro ζ hζ
      have hall : ∀ g : L' ≃ₐ[K] L', g ζ = ζ := by
        intro g
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hσ g)
        have h1 : ∀ n : ℕ, (σ ^ n) ζ = ζ := by
          intro n
          induction n with
          | zero => simp
          | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hζ]
        rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
        · rw [zpow_natCast]; exact h1 n
        · rw [zpow_neg, zpow_natCast]
          conv_lhs => rw [← h1 n]
          exact AlgEquiv.symm_apply_apply _ _ |>.trans rfl
      obtain ⟨γ, hγ⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L') ζ).2 hall
      exact ⟨γ, hγ⟩
    -- `a^d` lies in `L'` and is fixed by `σ`
    have hzC : (a : D) ^ d ∈ Subalgebra.centralizer K (L' : Set D) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro x hx
      have := hβk d ⟨x, hx⟩
      rw [← hσord, pow_orderOf_eq_one, AlgEquiv.one_apply, hσord] at this
      exact this.symm
    rw [hcent] at hzC
    set ζ : L' := ⟨_, hzC⟩ with hζdef
    have hσζ : σ ζ = ζ := by
      apply Subtype.ext
      rw [ha ζ]
      simp only [hζdef]
      rw [← pow_succ', pow_succ, mul_assoc, Units.mul_inv, mul_one]
    obtain ⟨γ, hγ⟩ := hfixK ζ hσζ
    have hγD : (a : D) ^ d = algebraMap K D γ := by
      have := congrArg Subtype.val hγ
      calc (a : D) ^ d = (ζ : D) := rfl
        _ = _ := this.symm
        _ = algebraMap K D γ := rfl
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hγD
      exact (Units.ne_zero (a ^ d)) (by simp at hγD)
    refine ⟨L', hL', hcyc', hcard, hdim'.symm, σ, a, γ, hσtop, hγ0, ?_, hβ, ?_⟩
    · rw [hfinL']; exact hγD
    · refine adjoin_eq_top L' hcent a fun x hx hcomm => ?_
      have hσx : σ ⟨x, hx⟩ = ⟨x, hx⟩ := by
        apply Subtype.ext
        have h := hβ ⟨x, hx⟩
        rw [hcomm] at h
        exact (mul_right_cancel₀ (Units.ne_zero a) h).symm
      obtain ⟨γ', hγ'⟩ := hfixK _ hσx
      rw [Algebra.mem_bot]
      exact ⟨γ', congrArg Subtype.val hγ'⟩

end NumberFieldKB.MilneCFT.Ch8.T26
