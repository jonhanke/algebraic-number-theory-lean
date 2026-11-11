import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangChar
import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangCyclic
import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangSelmer
import NumberFieldKB.MilneCFT.Ch8.ChevalleyUncond
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Milne, *CFT*, VIII, Theorem 2.4 (Grunwald–Wang), unconditionally

**Proved here:** `GW.theorem2_4 : Theorem2_4 K`.

Both halves use `GW.exists_char_of_subgroup` (`GrunwaldWangChar.lean`) with `N_v = ker χ_v`, `N'_w = ker χ'_w`:

* *Existence of `ψ`* (`GW.exists_char`, all cases): `W = Wsub S T N N' P` with `P` from Chevalley's congruence
  theorem for `H = {S-units in every N_v, N'_w}` (as in `existsU_of_chevalley`). If an idele `x` concentrated on
  `S ∪ T` is `w · a` with `w ∈ W`, `a ∈ K^×`, then `a` is an `S`-unit `≡ 1` at `P` (`ExistsUAux.key`), so `a ∈ H` and
  `x` has every coordinate in the kernels.
* *Order `n`* (`GW.exists_char_pow_eq_one`, when `K(ζ_{2^t})/K` is cyclic for all `2^t ∣ n`): `W = Wsub S T N N' P ⊔
  I_K^n` with `P` from `GW.exists_places_detect_pow` (Selmer group finiteness and `P(n, S') = K^{×n}`,
  `GW.powSet_subset_of_isCyclic`). If `x = w · y^n · a`, then `v(a) ≡ 0 mod n` outside `S`, and `a` is a local
  `n`-th power at `P` (Hensel, `P` prime to `n`), so `a ∈ K^{×n}` and again every coordinate of `x` is in the kernels
  (`χ_v^n = 1`). Since `I_K^n ⊆ W`, `ψ^n = 1`; since `χ_v = ψ|_{K_v^×}`, `ord χ_v ∣ ord ψ`, so `ord ψ = n`.
-/

open IsDedekindDomain NumberField TauCeti.GlobalNumberFields
open scoped Classical
open ValuativeRel

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.GW

open ExistsUAux

variable {K : Type} [Field K] [NumberField K]

local notation "ι" => IdeleGroup.unitEmbedding (𝓞 K) K

/-- **Existence of a global character with prescribed local components** (Chevalley route). -/
theorem exists_char (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (χ' : ∀ w : InfinitePlace K, w.Completionˣ →* ℂˣ)
    (hS : ∀ v ∈ S, Continuous (χ v) ∧ IsOfFinOrder (χ v))
    (hT : ∀ w ∈ T, Continuous (χ' w) ∧ IsOfFinOrder (χ' w)) :
    ∃ ψ : IdeleClassGroup (𝓞 K) K →* ℂˣ, Continuous ψ ∧
      (∀ v ∈ S, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v)) = χ v) ∧
      (∀ w ∈ T, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofCompletion (𝓞 K) K w)) = χ' w) := by
  let N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ := fun v => (χ v).ker
  let N' : ∀ w : InfinitePlace K, Subgroup w.Completionˣ := fun w => (χ' w).ker
  have hN : ∀ v ∈ S, IsOpen (N v : Set (v.adicCompletion K)ˣ) ∧ (N v).FiniteIndex := fun v hv =>
    isOpen_ker_and_finiteIndex (χ v) (hS v hv).1 (hS v hv).2
  have hN' : ∀ w ∈ T, IsOpen (N' w : Set w.Completionˣ) ∧ (N' w).FiniteIndex := fun w hw =>
    isOpen_ker_and_finiteIndex (χ' w) (hT w hw).1 (hT w hw).2
  let L : Subgroup Kˣ := (⨅ v ∈ S, (N v).comap (v.ideleFiniteCoord.comp ι)) ⊓
    ⨅ w ∈ T, (N' w).comap (w.ideleInfiniteCoord.comp ι)
  have hLmem : ∀ a : Kˣ, ι a ∈ prescribed S T N N' ↔ a ∈ L := by
    intro a
    simp [L, mem_prescribed_iff, Subgroup.mem_iInf]
  have hLfi : L.FiniteIndex := by
    have : (⨅ v ∈ S, (N v).comap (v.ideleFiniteCoord.comp ι)).FiniteIndex :=
      Subgroup.finiteIndex_iInf' _ (fun v hv => by have := (hN v hv).2; infer_instance)
    have : (⨅ w ∈ T, (N' w).comap (w.ideleInfiniteCoord.comp ι)).FiniteIndex :=
      Subgroup.finiteIndex_iInf' _ (fun w hw => by have := (hN' w hw).2; infer_instance)
    infer_instance
  let H : Subgroup Kˣ := L ⊓ (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  have hHle : H ≤ (S : Set (HeightOneSpectrum (𝓞 K))).unit K := inf_le_right
  have hHrel : H.relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) ≠ 0 := by
    rw [Subgroup.inf_relIndex_right]
    exact ne_zero_of_dvd_ne_zero hLfi.index_ne_zero (Subgroup.relIndex_dvd_index_of_normal _ _)
  obtain ⟨P, hPd, hP⟩ := (Chevalley.chevalleyCongruence (K := K)).congr S H hHle hHrel ∅
  have hPS : ∀ 𝔭 ∈ P, 𝔭 ∉ S := fun 𝔭 h𝔭 hS =>
    Finset.disjoint_left.mp hPd h𝔭 (by simp [hS])
  obtain ⟨𝔫, h𝔫⟩ := exists_cong_le_Wsub (fun v hv => (hN v hv).1) (fun w hw => (hN' w hw).1) P
  obtain ⟨ψ, hψc, -, hψS, hψT⟩ := exists_char_of_subgroup S T χ χ' (Wsub S T N N' P) 𝔫 h𝔫 (by
    intro x hxJ hxU
    obtain ⟨w, hw, hwx⟩ := hxU
    obtain ⟨a, ha⟩ := QuotientGroup.eq.1 hwx
    have hx : x = w * ι a := by
      have : ι a = w⁻¹ * x := ha
      rw [this]; simp
    obtain ⟨haS, haP⟩ := key hPS hw hx (mem_concentrated_iff.1 hxJ).1
    have haH : a ∈ H := hP a haS haP
    have hxp := mem_prescribed_iff.1 (hx ▸ mul_mem hw.1.1 ((hLmem a).2 haH.1))
    exact ⟨fun v hv => hxp.1 v hv, fun w hw => hxp.2 w hw⟩)
  exact ⟨ψ, hψc, hψS, hψT⟩

/-- **Grunwald–Wang, the order-`n` half**: in the non-special case the character can be chosen with `ψ^n = 1`. -/
theorem exists_char_pow_eq_one (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (χ' : ∀ w : InfinitePlace K, w.Completionˣ →* ℂˣ)
    (hS : ∀ v ∈ S, Continuous (χ v) ∧ IsOfFinOrder (χ v))
    (hT : ∀ w ∈ T, Continuous (χ' w) ∧ IsOfFinOrder (χ' w)) {n : ℕ} (hn : 0 < n)
    (hnS : ∀ v ∈ S, orderOf (χ v) ∣ n) (hnT : ∀ w ∈ T, orderOf (χ' w) ∣ n)
    (hcyc : ∀ t : ℕ, 2 ^ t ∣ n →
      IsCyclic (CyclotomicField (2 ^ t) K ≃ₐ[K] CyclotomicField (2 ^ t) K)) :
    ∃ ψ : IdeleClassGroup (𝓞 K) K →* ℂˣ, Continuous ψ ∧
      (∀ v ∈ S, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v)) = χ v) ∧
      (∀ w ∈ T, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofCompletion (𝓞 K) K w)) = χ' w) ∧
      ψ ^ n = 1 := by
  let N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ := fun v => (χ v).ker
  let N' : ∀ w : InfinitePlace K, Subgroup w.Completionˣ := fun w => (χ' w).ker
  have hN : ∀ v ∈ S, IsOpen (N v : Set (v.adicCompletion K)ˣ) ∧ (N v).FiniteIndex := fun v hv =>
    isOpen_ker_and_finiteIndex (χ v) (hS v hv).1 (hS v hv).2
  have hN' : ∀ w ∈ T, IsOpen (N' w : Set w.Completionˣ) ∧ (N' w).FiniteIndex := fun w hw =>
    isOpen_ker_and_finiteIndex (χ' w) (hT w hw).1 (hT w hw).2
  have hχn : ∀ v ∈ S, χ v ^ n = 1 := fun v hv => orderOf_dvd_iff_pow_eq_one.1 (hnS v hv)
  have hχn' : ∀ w ∈ T, χ' w ^ n = 1 := fun w hw => orderOf_dvd_iff_pow_eq_one.1 (hnT w hw)
  obtain ⟨P, hPd, hPn, hPdet⟩ := exists_places_detect_pow hn S
    (fun S' hS' => powSet_subset_of_isCyclic hn hS' hcyc)
  have hPS : ∀ 𝔭 ∈ P, 𝔭 ∉ S := fun 𝔭 h𝔭 hS => Finset.disjoint_left.mp hPd h𝔭 hS
  let Wn : Subgroup (IdeleGroup (𝓞 K) K) := (powMonoidHom n : IdeleGroup (𝓞 K) K →* _).range
  let W := Wsub S T N N' P ⊔ Wn
  obtain ⟨𝔫, h𝔫⟩ := exists_cong_le_Wsub (fun v hv => (hN v hv).1) (fun w hw => (hN' w hw).1) P
  obtain ⟨ψ, hψc, hψU, hψS, hψT⟩ := exists_char_of_subgroup S T χ χ' W 𝔫 (h𝔫.trans le_sup_left) (by
    intro x hxJ hxU
    obtain ⟨z, hz, hzx⟩ := hxU
    obtain ⟨a, ha⟩ := QuotientGroup.eq.1 hzx
    obtain ⟨w, hw, y', ⟨y, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hz
    have hx : x = w * y ^ n * ι a := by
      have : ι a = (w * y ^ n)⁻¹ * x := ha
      rw [this]; group
    obtain ⟨⟨hwp, hwU⟩, hwP⟩ := hw
    have hxS := (mem_concentrated_iff.1 hxJ).1
    -- coordinates of `ι a` outside `S`
    have hcoord : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ S →
        u.ideleFiniteCoord (ι a) = (u.ideleFiniteCoord w)⁻¹ * ((u.ideleFiniteCoord y)⁻¹) ^ n := by
      intro u hu
      have h := hxS u hu
      rw [hx, map_mul, map_mul, map_pow] at h
      rw [inv_pow, ← mul_inv]
      exact eq_inv_of_mul_eq_one_right h
    have hval : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ S →
        ∃ k : ℤ, u.valuation K (a : K) = WithZero.exp ((n : ℤ) * k) := by
      intro u hu
      have hw1 := (mem_unitsAway_iff.1 hwU) u hu
      set c : (u.adicCompletion K)ˣ := u.ideleFiniteCoord y
      have hc0 : Valued.v (c : u.adicCompletion K) ≠ 0 := by simp
      refine ⟨-WithZero.log (Valued.v (c : u.adicCompletion K)), ?_⟩
      rw [← valued_coord_unitEmbedding, hcoord u hu]
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀,
        map_pow, hw1, inv_one, one_mul]
      rw [mul_neg, WithZero.exp_neg, ← nsmul_eq_mul, WithZero.exp_nsmul, WithZero.exp_log hc0, inv_pow]
    have hloc : ∀ u ∈ P, IsLocalPow n (a : K) u := by
      intro u hu
      have : Finite (𝓞 K ⧸ u.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient u.ne_bot
      have hun : IsUnit (n : 𝒪[u.adicCompletion K]) := by
        rw [IsLocalRing.isUnit_natCast_iff_not_dvd]
        rw [HeightOneSpectrum.ringChar_residueField_adicCompletion_dvd_iff]
        exact hPn u hu
      have hmem : (u.ideleFiniteCoord w)⁻¹ ∈ TauCeti.unitFiltration (u.adicCompletion K) 1 :=
        Subgroup.inv_mem _ ((mem_principalAt_iff.1 hwP) u hu)
      obtain ⟨b, hb⟩ := TauCeti.unitFiltration_one_le_range_powMonoidHom_of_isUnit hun hmem
      refine ⟨((b * (u.ideleFiniteCoord y)⁻¹ : (u.adicCompletion K)ˣ) : u.adicCompletion K), ?_⟩
      have h1 : algebraMap K (u.adicCompletion K) (a : K) =
          ((u.ideleFiniteCoord (ι a) : (u.adicCompletion K)ˣ) : u.adicCompletion K) := by
        rw [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding, Units.coe_map]
        rfl
      rw [h1, hcoord u (hPS u hu), ← hb, ← Units.val_pow_eq_pow_val, mul_pow]
      rfl
    obtain ⟨b, rfl⟩ := hPdet a hval hloc
    have hx' : x = w * (y * ι b) ^ n := by rw [hx, mul_pow, map_pow, mul_assoc]
    have hwp' := mem_prescribed_iff.1 hwp
    refine ⟨fun v hv => ?_, fun w' hw' => ?_⟩
    · rw [hx', map_mul, map_mul, map_pow, map_pow]
      have h1 : χ v (v.ideleFiniteCoord w) = 1 := hwp'.1 v hv
      have h2 : χ v (v.ideleFiniteCoord (y * ι b)) ^ n = 1 := by
        rw [← MonoidHom.pow_apply, hχn v hv, MonoidHom.one_apply]
      rw [h1, h2, one_mul]
    · rw [hx', map_mul, map_mul, map_pow, map_pow]
      have h1 : χ' w' (w'.ideleInfiniteCoord w) = 1 := hwp'.2 w' hw'
      have h2 : χ' w' (w'.ideleInfiniteCoord (y * ι b)) ^ n = 1 := by
        rw [← MonoidHom.pow_apply, hχn' w' hw', MonoidHom.one_apply]
      rw [h1, h2, one_mul])
  refine ⟨ψ, hψc, hψS, hψT, ?_⟩
  refine MonoidHom.ext fun c => ?_
  induction c using QuotientGroup.induction_on with
  | H x =>
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, ← QuotientGroup.mk_pow]
    exact hψU _ ⟨x ^ n, le_sup_right (a := Wsub S T N N' P) ⟨x, rfl⟩, rfl⟩

/-- **Milne, CFT, VIII, Theorem 2.4 (Grunwald–Wang)**, unconditionally. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 2.4, p. 232 (Grunwald-Wang)"]
theorem theorem2_4 : Theorem2_4 K := by
  refine ⟨fun S T χ χ' hS hT n hnS hnT hmin => ?_⟩
  by_cases hc : ∀ t : ℕ, 2 ^ t ∣ n →
      IsCyclic (CyclotomicField (2 ^ t) K ≃ₐ[K] CyclotomicField (2 ^ t) K)
  · have hn : 0 < n := by
      set m := (∏ v ∈ S, orderOf (χ v)) * ∏ w ∈ T, orderOf (χ' w)
      have hm0 : m ≠ 0 := mul_ne_zero
        (Finset.prod_ne_zero_iff.2 fun v hv => (hS v hv).2.orderOf_pos.ne')
        (Finset.prod_ne_zero_iff.2 fun w hw => (hT w hw).2.orderOf_pos.ne')
      have := hmin m (fun v hv => dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hv) _)
        (fun w hw => dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hw) _)
      exact Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hm0 this)
    obtain ⟨ψ, hψc, hψS, hψT, hψn⟩ := exists_char_pow_eq_one S T χ χ' hS hT hn hnS hnT hc
    refine ⟨ψ, hψc, hψS, hψT, fun _ => Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hψn) ?_⟩
    refine hmin _ (fun v hv => ?_) (fun w hw => ?_)
    · rw [← hψS v hv]
      refine orderOf_dvd_of_pow_eq_one ?_
      refine MonoidHom.ext fun y => ?_
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, pow_orderOf_eq_one,
        MonoidHom.one_apply, MonoidHom.one_apply]
    · rw [← hψT w hw]
      refine orderOf_dvd_of_pow_eq_one ?_
      refine MonoidHom.ext fun y => ?_
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, pow_orderOf_eq_one,
        MonoidHom.one_apply, MonoidHom.one_apply]
  · obtain ⟨ψ, hψc, hψS, hψT⟩ := exists_char S T χ χ' hS hT
    exact ⟨ψ, hψc, hψS, hψT, fun h => absurd h hc⟩

end NumberFieldKB.MilneCFT.Ch8.GW
