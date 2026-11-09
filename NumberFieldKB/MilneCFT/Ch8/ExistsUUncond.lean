import NumberFieldKB.MilneCFT.Ch8.Theorem23Uncond
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient

/-!
# Milne, *CFT*, VIII, Theorem 2.3: `ExistsU` from Chevalley's congruence theorem

**Proved here** (all against the named statement `ChevalleyCongruence` of `Theorem23Uncond.lean`):
* `existsU_of_chevalley`: `ChevalleyCongruence K → ExistsU K`.
* `theorem2_3_of_chevalley`: `ChevalleyCongruence K → Theorem2_3 K` (with `theorem2_3_of_existsU`).

**Not proved** (so there is no unconditional `existsU` / `theorem2_3` headline yet): `ChevalleyCongruence K`
itself, i.e. for a finite set `S` of finite places and a finite-index subgroup `H` of the `S`-units there is a
finite set `P` of primes outside `S ∪ B` such that every `S`-unit congruent to `1` at all `𝔭 ∈ P` lies in `H`.
Classically this is Kummer theory over `K(ζ_m, E_S^{1/m})` plus Chebotarev; Tau Ceti has the prime-exponent
ingredients only over a field containing `ζ_p`.

## Proof of the implication (Artin–Tate X §1)
Put `H := {a ∈ E_S : a ∈ N_v (v ∈ S), a ∈ N'_w (w ∈ T)}`; it has finite relative index in `E_S`.
Chevalley gives `P`.  Let `W` be the subgroup of ideles with coordinates in `N_v` (`v ∈ S`), `N'_w` (`w ∈ T`),
principal units at `P`, and units at every other finite place; `U` is its image in `C_K`.  `W` contains an
idele congruence subgroup (it is open: `exists_ideleCongruenceSubgroup_le_of_isOpen` for the coordinate
conditions, intersected with the modulus `∏_{𝔭∈P} 𝔭`), so `U` contains a ray subgroup, hence is open of finite
index.  If an idele `x` concentrated at a place of `S ∪ T` equals `j · a` with `j ∈ W`, `a ∈ K^×`, then `a` is
an `S`-unit congruent to `1` at `P` (`ExistsUAux.key`), so `a ∈ H` and `x ∈ N`-conditions follow, since `j` and
`a` both satisfy them.  (The membership of `a` in `N_v` at `v` itself comes from `a ∈ H`, not from `x`.)
-/

open IsDedekindDomain NumberField TauCeti.GlobalNumberFields
open scoped Classical

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8
namespace ExistsUAux

variable {K : Type} [Field K] [NumberField K]

theorem continuous_ideleFiniteCoord' (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (v.ideleFiniteCoord : IdeleGroup (𝓞 K) K → (v.adicCompletion K)ˣ) := by
  have h : (v.ideleFiniteCoord : IdeleGroup (𝓞 K) K → (v.adicCompletion K)ˣ) =
      fun x => (IdeleGroup.localUnitsEquiv (𝓞 K) K x).2 v := by
    funext x; rw [IdeleGroup.localUnitsEquiv_apply_snd]
  rw [h]
  exact (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (IdeleGroup.localUnitsEquiv (𝓞 K) K).continuous)

theorem continuous_ideleInfiniteCoord' (w : InfinitePlace K) :
    Continuous (w.ideleInfiniteCoord : IdeleGroup (𝓞 K) K → w.Completionˣ) := by
  have h : (w.ideleInfiniteCoord : IdeleGroup (𝓞 K) K → w.Completionˣ) =
      fun x => (IdeleGroup.localUnitsEquiv (𝓞 K) K x).1 w := by
    funext x; rw [IdeleGroup.localUnitsEquiv_apply_fst]
  rw [h]
  exact (continuous_apply w).comp
    (continuous_fst.comp (IdeleGroup.localUnitsEquiv (𝓞 K) K).continuous)

/-- The ideles whose coordinates lie in the prescribed subgroups. -/
def prescribed (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
    (N' : ∀ w : InfinitePlace K, Subgroup w.Completionˣ) : Subgroup (IdeleGroup (𝓞 K) K) :=
  (⨅ v ∈ S, (N v).comap v.ideleFiniteCoord) ⊓ ⨅ w ∈ T, (N' w).comap w.ideleInfiniteCoord

theorem mem_prescribed_iff {S : Finset (HeightOneSpectrum (𝓞 K))} {T : Finset (InfinitePlace K)}
    {N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ}
    {N' : ∀ w : InfinitePlace K, Subgroup w.Completionˣ} {x : IdeleGroup (𝓞 K) K} :
    x ∈ prescribed S T N N' ↔
      (∀ v ∈ S, v.ideleFiniteCoord x ∈ N v) ∧ ∀ w ∈ T, w.ideleInfiniteCoord x ∈ N' w := by
  simp [prescribed, Subgroup.mem_iInf]

theorem isOpen_prescribed {S : Finset (HeightOneSpectrum (𝓞 K))} {T : Finset (InfinitePlace K)}
    {N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ}
    {N' : ∀ w : InfinitePlace K, Subgroup w.Completionˣ}
    (hN : ∀ v ∈ S, IsOpen (N v : Set (v.adicCompletion K)ˣ))
    (hN' : ∀ w ∈ T, IsOpen (N' w : Set w.Completionˣ)) :
    IsOpen (prescribed S T N N' : Set (IdeleGroup (𝓞 K) K)) := by
  have : (prescribed S T N N' : Set (IdeleGroup (𝓞 K) K)) =
      (⋂ v ∈ S, v.ideleFiniteCoord ⁻¹' (N v : Set (v.adicCompletion K)ˣ)) ∩
        ⋂ w ∈ T, w.ideleInfiniteCoord ⁻¹' (N' w : Set w.Completionˣ) := by
    ext x
    simp only [SetLike.mem_coe, mem_prescribed_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage]
  rw [this]
  exact (isOpen_biInter_finset fun v hv => (hN v hv).preimage (continuous_ideleFiniteCoord' v)).inter
    (isOpen_biInter_finset fun w hw => (hN' w hw).preimage (continuous_ideleInfiniteCoord' w))

/-- Ideles that are units at all finite places outside `S`. -/
def unitsAway (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup (𝓞 K) K) :=
  ⨅ u : {u : HeightOneSpectrum (𝓞 K) // u ∉ S},
    ((Valued.v : Valuation (u.1.adicCompletion K) _).valuationSubring.unitGroup).comap
      u.1.ideleFiniteCoord

theorem mem_unitsAway_iff {S : Finset (HeightOneSpectrum (𝓞 K))} {x : IdeleGroup (𝓞 K) K} :
    x ∈ unitsAway S ↔ ∀ u : HeightOneSpectrum (𝓞 K), u ∉ S →
      Valued.v (u.ideleFiniteCoord x : u.adicCompletion K) = 1 := by
  simp only [unitsAway, Subgroup.mem_iInf, Subgroup.mem_comap, Valuation.mem_unitGroup_iff,
    Subtype.forall]

/-- Ideles that are principal units at the places of `P`. -/
def principalAt (P : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup (𝓞 K) K) :=
  ⨅ u : P, (TauCeti.unitFiltration (u.1.adicCompletion K) 1).comap u.1.ideleFiniteCoord

theorem mem_principalAt_iff {P : Finset (HeightOneSpectrum (𝓞 K))} {x : IdeleGroup (𝓞 K) K} :
    x ∈ principalAt P ↔ ∀ u ∈ P,
      u.ideleFiniteCoord x ∈ TauCeti.unitFiltration (u.adicCompletion K) 1 := by
  simp [principalAt, Subgroup.mem_iInf]

theorem valued_coord_unitEmbedding (u : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    Valued.v (u.ideleFiniteCoord (IdeleGroup.unitEmbedding (𝓞 K) K a) : u.adicCompletion K) =
      u.valuation K (a : K) := by
  rw [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding, Units.coe_map]
  simp only [MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe,
    HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self_apply, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-- The class-group-level subgroup. -/
def Wsub (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
    (N' : ∀ w : InfinitePlace K, Subgroup w.Completionˣ) (P : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (IdeleGroup (𝓞 K) K) :=
  prescribed S T N N' ⊓ unitsAway S ⊓ principalAt P

/-- The local-global step: if `x = w * a` with `w ∈ W` and `x` trivial at the finite places
outside `S`, then `a` is an `S`-unit congruent to one at `P`. -/
theorem key {S : Finset (HeightOneSpectrum (𝓞 K))} {T : Finset (InfinitePlace K)}
    {N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ}
    {N' : ∀ w : InfinitePlace K, Subgroup w.Completionˣ} {P : Finset (HeightOneSpectrum (𝓞 K))}
    (hPS : ∀ 𝔭 ∈ P, 𝔭 ∉ S) {x w : IdeleGroup (𝓞 K) K} {a : Kˣ}
    (hw : w ∈ Wsub S T N N' P)
    (hx : x = w * IdeleGroup.unitEmbedding (𝓞 K) K a)
    (hxS : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ S → u.ideleFiniteCoord x = 1) :
    a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K ∧
      ∀ 𝔭 ∈ P, Valued.v (algebraMap K (𝔭.adicCompletion K) (a : K) - 1) < 1 := by
  obtain ⟨⟨-, hwU⟩, hwP⟩ := hw
  replace hwU := mem_unitsAway_iff.1 hwU
  replace hwP := mem_principalAt_iff.1 hwP
  have hcoord : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ S →
      u.ideleFiniteCoord (IdeleGroup.unitEmbedding (𝓞 K) K a) = (u.ideleFiniteCoord w)⁻¹ := by
    intro u hu
    have h := hxS u hu
    rw [hx, map_mul, mul_eq_one_iff_eq_inv] at h
    rw [h]; simp
  refine ⟨?_, fun 𝔭 h𝔭 => ?_⟩
  · rw [Set.unit_eq]
    simp only [Subgroup.mem_iInf, Valuation.mem_unitGroup_iff, Finset.mem_coe]
    intro u hu
    rw [← valued_coord_unitEmbedding, hcoord u hu]
    rw [Units.val_inv_eq_inv_val, map_inv₀, hwU u hu, inv_one]
  · have h1 := hwP 𝔭 h𝔭
    have h2 : 𝔭.ideleFiniteCoord (IdeleGroup.unitEmbedding (𝓞 K) K a) ∈
        TauCeti.unitFiltration (𝔭.adicCompletion K) 1 := by
      rw [hcoord 𝔭 (hPS 𝔭 h𝔭)]
      exact Subgroup.inv_mem _ h1
    rw [HeightOneSpectrum.mem_unitFiltration_adicCompletion_iff] at h2
    have h3 := h2.2
    rw [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding, Units.coe_map] at h3
    refine lt_of_le_of_lt h3 ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)

end ExistsUAux

variable (K : Type) [Field K] [NumberField K]

open ExistsUAux in
/-- **`ExistsU` from Chevalley's congruence theorem.** -/
theorem existsU_of_chevalley (h : ChevalleyCongruence K) : ExistsU K := by
  refine ⟨fun S T N N' hN hN' => ?_⟩
  let ι : Kˣ →* IdeleGroup (𝓞 K) K := IdeleGroup.unitEmbedding (𝓞 K) K
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
  obtain ⟨P, hPd, hP⟩ := h.congr S H hHle hHrel ∅
  have hPS : ∀ 𝔭 ∈ P, 𝔭 ∉ S := fun 𝔭 h𝔭 hS =>
    Finset.disjoint_left.mp hPd h𝔭 (by simp [hS])
  obtain ⟨𝔪A, h𝔪A⟩ := exists_ideleCongruenceSubgroup_le_of_isOpen (prescribed S T N N')
    (isOpen_prescribed (fun v hv => (hN v hv).1) (fun w hw => (hN' w hw).1))
  let 𝔫 : TauCeti.GlobalNumberFields.Modulus K :=
    ⟨𝔪A.finitePart * ∏ 𝔭 ∈ P, 𝔭.asIdeal, by
      rw [← Ideal.zero_eq_bot]
      exact mul_ne_zero 𝔪A.finitePart_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => by
        rw [Ideal.zero_eq_bot]; exact v.ne_bot), 𝔪A.infinitePart⟩
  have hdvd : 𝔪A ∣ 𝔫 := TauCeti.GlobalNumberFields.Modulus.dvd_iff.mpr ⟨dvd_mul_right _ _, Finset.Subset.refl _⟩
  have hcongW : ideleCongruenceSubgroup 𝔫 ≤ Wsub S T N N' P := by
    intro x hx
    refine ⟨⟨h𝔪A (ideleCongruenceSubgroup_antitone hdvd hx),
      mem_unitsAway_iff.2 fun u _ =>
        ideleCongruenceSubgroup.valued_ideleFiniteCoord_eq_one hx u⟩,
      mem_principalAt_iff.2 fun 𝔭 h𝔭 => ?_⟩
    have h1 := ideleCongruenceSubgroup.ideleFiniteCoord_mem_unitFiltration hx 𝔭
    have hdv : 𝔭.asIdeal ∣ 𝔫.finitePart :=
      dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
        h𝔭) _
    have hpos : 1 ≤ 𝔫.exponent 𝔭 :=
      TauCeti.GlobalNumberFields.Modulus.exponent_pos_of_mem_support ((TauCeti.GlobalNumberFields.Modulus.mem_support_iff 𝔫 𝔭).2 hdv)
    exact TauCeti.unitFiltration_antitone hpos h1
  let U : Subgroup (IdeleClassGroup (𝓞 K) K) :=
    (Wsub S T N N' P).map (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))
  have hle : raySubgroup 𝔫 ≤ U := Subgroup.map_mono hcongW
  have hfwd : ∀ x : IdeleGroup (𝓞 K) K, (∀ u : HeightOneSpectrum (𝓞 K), u ∉ S →
      u.ideleFiniteCoord x = 1) → (x : IdeleClassGroup (𝓞 K) K) ∈ U →
      x ∈ prescribed S T N N' := by
    intro x hxS hxU
    obtain ⟨w, hw, hwx⟩ := hxU
    obtain ⟨a, ha⟩ := QuotientGroup.eq.1 hwx
    have hx : x = w * ι a := by
      have : ι a = w⁻¹ * x := ha
      rw [this]; simp
    obtain ⟨haS, haP⟩ := key hPS hw hx hxS
    have haH : a ∈ H := hP a haS haP
    exact hx ▸ mul_mem hw.1.1 ((hLmem a).2 haH.1)
  have hbwd : ∀ x : IdeleGroup (𝓞 K) K, x ∈ Wsub S T N N' P →
      (x : IdeleClassGroup (𝓞 K) K) ∈ U := fun x hx => ⟨x, hx, rfl⟩
  refine ⟨U, Subgroup.isOpen_mono hle (isOpen_raySubgroup 𝔫), ?_, ?_, ?_⟩
  · have := finiteIndex_raySubgroup 𝔫
    exact Subgroup.finiteIndex_of_le hle
  · intro v hv y
    constructor
    · intro hyU
      have hxS : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ S →
          u.ideleFiniteCoord (IdeleGroup.ofAdicCompletion (𝓞 K) K v y) = 1 := fun u hu =>
        HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne u (fun h => hu (h ▸ hv)) y
      have := (mem_prescribed_iff.1 (hfwd _ hxS hyU)).1 v hv
      simpa using this
    · intro hy
      refine hbwd _ ⟨⟨mem_prescribed_iff.2 ⟨fun u hu => ?_, fun w _ => by simp⟩,
        mem_unitsAway_iff.2 fun u hu => ?_⟩, mem_principalAt_iff.2 fun u hu => ?_⟩
      · by_cases huv : u = v
        · subst huv; simpa using hy
        · simp [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne u huv]
      · have huv : u ≠ v := fun h => hu (h ▸ hv)
        simp [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne u huv]
      · have huv : u ≠ v := fun h => hPS u hu (h ▸ hv)
        simp [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne u huv]
  · intro w hw y
    constructor
    · intro hyU
      have hxS : ∀ u : HeightOneSpectrum (𝓞 K), u ∉ S →
          u.ideleFiniteCoord (IdeleGroup.ofCompletion (𝓞 K) K w y) = 1 := fun u _ =>
        HeightOneSpectrum.ideleFiniteCoord_ofCompletion u w y
      have := (mem_prescribed_iff.1 (hfwd _ hxS hyU)).2 w hw
      simpa using this
    · intro hy
      refine hbwd _ ⟨⟨mem_prescribed_iff.2 ⟨fun u _ => by simp, fun w' hw' => ?_⟩,
        mem_unitsAway_iff.2 fun u _ => by simp⟩, mem_principalAt_iff.2 fun u _ => by simp⟩
      by_cases hww : w' = w
      · subst hww; simpa using hy
      · simp [InfinitePlace.ideleInfiniteCoord_ofCompletion_of_ne w' hww]

/-- **Theorem 2.3 from Chevalley's congruence theorem** (via `existsU_of_chevalley` and
`theorem2_3_of_existsU`). -/
theorem theorem2_3_of_chevalley (h : ChevalleyCongruence K) : Theorem2_3 K :=
  theorem2_3_of_existsU K (existsU_of_chevalley K h)

end NumberFieldKB.MilneCFT.Ch8
