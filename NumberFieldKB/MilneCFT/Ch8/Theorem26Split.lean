import NumberFieldKB.MilneCFT.Ch8.GrunwaldWang
import NumberFieldKB.MilneCFT.Ch8.LocalRelBrTauCeti
import NumberFieldKB.MilneCFT.Ch7.BrauerTauCeti
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Milne, *CFT*, VIII, Theorem 2.6: a cyclic splitting field of degree the period

**Proved here:** `T26.exists_cyclic_splitsOver_of_corollary2_5`: given Corollary 2.5 (proved unconditionally in
`GrunwaldWangCor25.lean`), every central simple algebra `A` over a number field `K` is split by a cyclic extension of
degree exactly the order `m` of `[A]` in `Br(K)`.

Proof (Milne, p. 233). Let `x = [A]`, `x_v` its localizations, `m_v = ord x_v`. Only finitely many `x_v` are nontrivial
(Tau Ceti `brauerSupport`); at a real place `x_w` has order `1` or `2`. By the Hasse principle (`brLocalization_injective`)
`m = lcm m_v`. Corollary 2.5 gives a cyclic `L/K` of degree `m` with local degree `m_v` at the finite places of the
support, ramified at the real places where `x_w ≠ 1`. Then `x_v` dies in every `L_w` (restriction multiplies the local
invariant by `e f = m_v`, `baseChange_adicCompletion_eq_one_iff`), and at the ramified real places all `L_w` are complex;
the relative Hasse principle (`Ch8.relativeHasse`) gives `x ∈ Br(L/K)`.
-/

open IsDedekindDomain NumberField TauCeti.ClassFieldTheory
open scoped TensorProduct

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.T26

variable {K : Type} [Field K] [NumberField K]

/-- The Tau Ceti image of a base-changed class. -/
theorem equivBr_baseChange (x : BrauerGroup.{0, 0} K) (F : Type) [Field F] [Algebra K F] :
    brauerGroupEquivBr F (Additive.ofMul (Ch4.baseChange F x)) =
      brBaseChange K F (brauerGroupEquivBr K (Additive.ofMul x)) := by
  rw [Ch4.baseChange_eq_tauCeti, BrauerBaseChange.brauerGroupEquivBr_baseChange]

theorem baseChange_eq_one_iff (x : BrauerGroup.{0, 0} K) (F : Type) [Field F] [Algebra K F] :
    Ch4.baseChange F x = 1 ↔ brBaseChange K F (brauerGroupEquivBr K (Additive.ofMul x)) = 0 := by
  rw [← equivBr_baseChange, Ch4.brauerGroupEquivBr_eq_zero_iff]

/-- **A cyclic splitting field of degree the period**, from Corollary 2.5. -/
theorem exists_cyclic_splitsOver_of_corollary2_5 (hcor : Corollary2_5 K) (A : Type) [Ring A] [Algebra K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsGalois K L),
      IsCyclic Gal(L/K) ∧ Module.finrank K L = orderOf (Ch7.brClass (K := K) A) ∧ Ch7.SplitsOver K A L := by
  classical
  set x : BrauerGroup.{0, 0} K := Ch7.brClass (K := K) A with hxdef
  set y : Br K := brauerGroupEquivBr K (Additive.ofMul x) with hy
  set m := orderOf x with hm
  have hxfin : IsOfFinOrder x := Ch4.cor_3_17_torsion x
  have hmpos : 0 < m := hxfin.orderOf_pos
  let xv : ∀ v : HeightOneSpectrum (𝓞 K), BrauerGroup.{0, 0} (v.adicCompletion K) :=
    fun v => Ch4.baseChange (v.adicCompletion K) x
  let xw : ∀ w : InfinitePlace K, BrauerGroup.{0, 0} w.Completion := fun w => Ch4.baseChange w.Completion x
  have hxv_pow : ∀ v k, xv v ^ k = Ch4.baseChange (v.adicCompletion K) (x ^ k) := fun v k =>
    (map_pow (Ch4.baseChange (v.adicCompletion K)) x k).symm
  have hxw_pow : ∀ w k, xw w ^ k = Ch4.baseChange w.Completion (x ^ k) := fun w k =>
    (map_pow (Ch4.baseChange w.Completion) x k).symm
  let S : Finset (HeightOneSpectrum (𝓞 K)) := brauerSupport K y
  have hS : ∀ v, v ∉ S → xv v = 1 := by
    intro v hv
    rw [baseChange_eq_one_iff]
    exact (finiteInvAt_eq_zero_iff K v y).mp (finiteInvAt_eq_zero_of_notMem_brauerSupport K hv)
  let T : Finset (InfinitePlace K) := Finset.univ.filter fun w => w.IsReal ∧ xw w ≠ 1
  have hT2 : ∀ w ∈ T, orderOf (xw w) = 2 := by
    intro w hw
    obtain ⟨hreal, hne⟩ := (Finset.mem_filter.1 hw).2
    have hcard := natCard_brauerGroup_of_isReal w hreal
    haveI : Finite (BrauerGroup.{0, 0} w.Completion) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have h2 : xw w ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
    exact orderOf_eq_prime h2 hne
  have hTc : ∀ w, w ∉ T → xw w = 1 := by
    intro w hw
    by_contra hne
    rcases w.isReal_or_isComplex with hr | hc
    · exact hw (Finset.mem_filter.2 ⟨Finset.mem_univ _, hr, hne⟩)
    · exact hne (brauerGroup_eq_one_of_isComplex w hc _)
  let nv : HeightOneSpectrum (𝓞 K) → ℕ := fun v => orderOf (xv v)
  let nw : InfinitePlace K → ℕ := fun w => if w ∈ T then 2 else 1
  have hnv_dvd : ∀ v, nv v ∣ m := fun v => orderOf_dvd_of_pow_eq_one (by
    rw [hxv_pow, hm, pow_orderOf_eq_one, map_one]; rfl)
  have hnvpos : ∀ v ∈ S, 0 < nv v := fun v _ => Nat.pos_of_dvd_of_pos (hnv_dvd v) hmpos
  have hT : ∀ w ∈ T, nw w = 1 ∨ (w.IsReal ∧ nw w = 2) := fun w hw =>
    Or.inr ⟨(Finset.mem_filter.1 hw).2.1, if_pos hw⟩
  have h1 : ∀ v ∈ S, nv v ∣ m := fun v _ => hnv_dvd v
  have h2 : ∀ w ∈ T, nw w ∣ m := by
    intro w hw
    simp only [nw, if_pos hw]
    rw [← hT2 w hw]
    exact orderOf_dvd_of_pow_eq_one (by rw [hxw_pow, hm, pow_orderOf_eq_one, map_one]; rfl)
  have hmin : ∀ k : ℕ, (∀ v ∈ S, nv v ∣ k) → (∀ w ∈ T, nw w ∣ k) → m ∣ k := by
    intro k hkS hkT
    refine orderOf_dvd_of_pow_eq_one ?_
    have hky : k • y = 0 := by
      apply brLocalization_injective K
      rw [map_zero]
      refine Prod.ext (DFinsupp.ext fun v => ?_) (funext fun w => ?_)
      · rw [brLocalization_fst_apply, map_nsmul]
        have : xv v ^ k = 1 := by
          by_cases hv : v ∈ S
          · exact orderOf_dvd_iff_pow_eq_one.1 (hkS v hv)
          · rw [hS v hv]; exact one_pow k
        rw [hxv_pow, baseChange_eq_one_iff, ofMul_pow, map_nsmul, map_nsmul] at this
        simpa [hy] using this
      · rw [brLocalization_snd_apply, map_nsmul]
        have : xw w ^ k = 1 := by
          by_cases hw : w ∈ T
          · have := hkT w hw
            simp only [nw, if_pos hw] at this
            exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hT2 w hw]; exact this)
          · rw [hTc w hw]; exact one_pow k
        rw [hxw_pow, baseChange_eq_one_iff, ofMul_pow, map_nsmul, map_nsmul] at this
        simpa [hy] using this
    have : brauerGroupEquivBr K (Additive.ofMul (x ^ k)) = 0 := by
      rw [ofMul_pow, map_nsmul, ← hy, hky]
    exact Additive.ofMul.injective ((brauerGroupEquivBr K).injective (this.trans (map_zero _).symm))
  obtain ⟨L, _, _, _, _, hcyc, hdeg, hloc, hinf⟩ := hcor.exists_cyclic S T nv nw hnvpos hT m h1 h2 hmin
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hcyc, hdeg, ?_⟩
  have hrel : x ∈ Ch4.relBrauer K L := by
    refine (relativeHasse K L).mem_relBrauer x (fun v => ?_) (fun w => ?_)
    · show xv v ∈ localRelBr K L (v.adicCompletion K)
      rw [mem_localRelBr_adicCompletion_iff]
      rintro ⟨w, hw⟩
      by_cases hv : v ∈ S
      · rw [baseChange_adicCompletion_eq_one_iff]
        have hef := hloc v hv ⟨w.asIdeal, w.isPrime, hw⟩
        rw [hef]
        rw [← map_nsmul, ← map_nsmul, ← ofMul_pow, pow_orderOf_eq_one]
        simp
      · rw [hS v hv, map_one]
    · show xw w ∈ localRelBr K L w.Completion
      rw [mem_localRelBr_completion_iff]
      rintro ⟨w', hw'⟩
      by_cases hwT : w ∈ T
      · have hram : InfinitePlace.RamifiesIn L w := (hinf w hwT).2 (if_pos hwT)
        obtain ⟨hv, w0, hw0, hc⟩ := hram
        obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq (k := K)
          (hw0.trans ((InfinitePlace.liesOver_iff_comap_eq).1 hw').symm)
        have hc' : w'.IsComplex := by
          rw [← hσ]
          exact InfinitePlace.isComplex_smul_iff.2 hc
        exact brauerGroup_eq_one_of_isComplex _ hc' _
      · rw [hTc w hwT, map_one]
  obtain ⟨n, -, ⟨e⟩⟩ := (Ch4.mk_mem_relBrauer_iff L (⟨.of K A⟩ : CSA.{0, 0} K)).1 hrel
  exact ⟨n, ⟨e⟩⟩

end NumberFieldKB.MilneCFT.Ch8.T26
