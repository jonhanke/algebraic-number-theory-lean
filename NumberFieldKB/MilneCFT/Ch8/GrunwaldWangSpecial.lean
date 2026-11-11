import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangUncond
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Grunwald–Wang in the special case: characters of exponent `n` when the local components kill `a₀`

**Proved here:** `GW.exists_char_pow_eq_one_of_mem`. Let `a₀ ∈ K^×` be such that every element of
`P(n, S ∪ {v ∣ n})` lies in `K^{×n} ∪ a₀ K^{×n}` (Remark VIII.1.5 (a), `R15a.remark1_5a`, always provides one, with
`a₀ = 1` in the non-special case). If the local characters `χ_v` (`v ∈ S`), `χ'_w` (`w ∈ T`) satisfy `χ^n = 1` and
kill `a₀`, there is a continuous character `ψ` of `C_K` with these local components and `ψ^n = 1`.

Proof: as `GW.exists_char_pow_eq_one`, with `GW.exists_places_detect_powSet` in place of
`GW.exists_places_detect_pow`: if an idele `x` concentrated on `S ∪ T` is `w · y^n · a` (`w ∈ Wsub`, `a ∈ K^×`), then
`a ∈ P(n, S ∪ {v ∣ n})`, so `a = b^n` or `a = a₀ b^n`, and every coordinate of `x` is killed by the local character.
-/

open IsDedekindDomain NumberField TauCeti.GlobalNumberFields
open scoped Classical
open ValuativeRel

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.GW

open ExistsUAux

variable {K : Type} [Field K] [NumberField K]

local notation "ι" => IdeleGroup.unitEmbedding (𝓞 K) K

/-- **Characters of exponent `n` with prescribed local components killing `a₀`.** -/
theorem exists_char_pow_eq_one_of_mem (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (χ' : ∀ w : InfinitePlace K, w.Completionˣ →* ℂˣ)
    (hS : ∀ v ∈ S, Continuous (χ v) ∧ IsOfFinOrder (χ v))
    (hT : ∀ w ∈ T, Continuous (χ' w) ∧ IsOfFinOrder (χ' w)) {n : ℕ} (hn : 0 < n)
    (hχn : ∀ v ∈ S, χ v ^ n = 1) (hχn' : ∀ w ∈ T, χ' w ^ n = 1) (a₀ : Kˣ)
    (ha₀ : ∀ a ∈ powSet n ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ {v | (n : 𝓞 K) ∈ v.asIdeal}),
      ∃ b : Kˣ, a = b ^ n ∨ a = a₀ * b ^ n)
    (hS₀ : ∀ v ∈ S, χ v (v.ideleFiniteCoord (ι a₀)) = 1)
    (hT₀ : ∀ w ∈ T, χ' w (w.ideleInfiniteCoord (ι a₀)) = 1) :
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
  obtain ⟨P, hPd, hPn, hPdet⟩ := exists_places_detect_powSet hn S
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
    obtain ⟨b, hab⟩ := ha₀ a (hPdet a hval hloc)
    -- in both cases `x = w * (y * ι b) ^ n * ι c` with `c ∈ {1, a₀}`
    obtain ⟨c, hc, hxc⟩ : ∃ c : Kˣ, (c = 1 ∨ c = a₀) ∧ x = w * (y * ι b) ^ n * ι c := by
      rcases hab with rfl | rfl
      · exact ⟨1, Or.inl rfl, by rw [hx, mul_pow, map_pow, map_one, mul_one, mul_assoc]⟩
      · refine ⟨a₀, Or.inr rfl, ?_⟩
        rw [hx, mul_pow, map_mul, map_pow]
        simp only [mul_assoc, mul_comm, mul_left_comm]
    have hwp' := mem_prescribed_iff.1 hwp
    refine ⟨fun v hv => ?_, fun w' hw' => ?_⟩
    · rw [hxc, map_mul, map_mul, map_mul, map_pow, map_mul, map_pow]
      have h1 : χ v (v.ideleFiniteCoord w) = 1 := hwp'.1 v hv
      have h2 : χ v (v.ideleFiniteCoord (y * ι b)) ^ n = 1 := by
        rw [← MonoidHom.pow_apply, hχn v hv, MonoidHom.one_apply]
      have h3 : χ v (v.ideleFiniteCoord (ι c)) = 1 := by
        rcases hc with rfl | rfl
        · simp
        · exact hS₀ v hv
      rw [h1, h2, h3, one_mul, one_mul]
    · rw [hxc, map_mul, map_mul, map_mul, map_pow, map_mul, map_pow]
      have h1 : χ' w' (w'.ideleInfiniteCoord w) = 1 := hwp'.2 w' hw'
      have h2 : χ' w' (w'.ideleInfiniteCoord (y * ι b)) ^ n = 1 := by
        rw [← MonoidHom.pow_apply, hχn' w' hw', MonoidHom.one_apply]
      have h3 : χ' w' (w'.ideleInfiniteCoord (ι c)) = 1 := by
        rcases hc with rfl | rfl
        · simp
        · exact hT₀ w' hw'
      rw [h1, h2, h3, one_mul, one_mul])
  refine ⟨ψ, hψc, hψS, hψT, ?_⟩
  refine MonoidHom.ext fun c => ?_
  induction c using QuotientGroup.induction_on with
  | H x =>
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow, ← QuotientGroup.mk_pow]
    exact hψU _ ⟨x ^ n, le_sup_right (a := Wsub S T N N' P) ⟨x, rfl⟩, rfl⟩

end NumberFieldKB.MilneCFT.Ch8.GW
