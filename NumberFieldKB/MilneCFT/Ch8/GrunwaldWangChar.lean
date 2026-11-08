import NumberFieldKB.MilneCFT.Ch8.ExistsUUncond
import NumberFieldKB.MilneCFT.Ch8.GrunwaldWang

/-!
# Grunwald–Wang: characters of `C_K` from an open subgroup with controlled local traces

**Proved here** (`GW` namespace):
* `GW.exists_char_of_subgroup`: let `W` be a subgroup of the ideles containing an idele congruence subgroup, and
  `χ_v` (`v ∈ S`), `χ'_w` (`w ∈ T`) characters of the local multiplicative groups. If every idele concentrated on
  `S ∪ T` whose class lies in the image `U` of `W` in `C_K` is killed by `∏ χ_v`, factor by factor, then there is a
  continuous character `ψ` of `C_K`, trivial on `U`, restricting to `χ_v` on `K_v^×` for `v ∈ S ∪ T`.
* `GW.exists_cong_le_Wsub`: the subgroup `Wsub S T N N' P` of `ExistsUUncond.lean` (coordinates in `N_v`, `N'_w`,
  units outside `S`, principal units at `P`) contains an idele congruence subgroup when the `N_v`, `N'_w` are open.
* `GW.isOpen_ker_and_finiteIndex`: the kernel of a continuous character of finite order is open of finite index.

Proof of the first item. `U` contains a ray subgroup, so it is open of finite index. The ideles `J` concentrated on
`S ∪ T` map to the finite group `C_K/U`; by hypothesis the product character `Φ = ∏ χ_v` on `J` vanishes on the
kernel, so it descends to the image of `J`, and extends to `C_K/U` (characters of finite abelian groups extend,
Mathlib `MonoidHom.domRestrict_surjective`). The extension is continuous because it is trivial on the open
subgroup `U`.
-/

open IsDedekindDomain NumberField TauCeti.GlobalNumberFields
open scoped Classical

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.GW

open ExistsUAux

variable {K : Type} [Field K] [NumberField K]

/-- The kernel of a continuous character of finite order is open and of finite index. -/
theorem isOpen_ker_and_finiteIndex {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (χ : G →* ℂˣ) (hc : Continuous χ) (hf : IsOfFinOrder χ) :
    IsOpen (χ.ker : Set G) ∧ χ.ker.FiniteIndex := by
  obtain ⟨k, hk, hχk⟩ := hf.exists_pow_eq_one
  haveI : NeZero k := ⟨hk.ne'⟩
  have hrange : (χ.range : Set ℂˣ) ⊆ (rootsOfUnity k ℂ : Set ℂˣ) := by
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, mem_rootsOfUnity]
    have := congrArg (fun f : G →* ℂˣ => f g) hχk
    simpa using this
  have hfin : Finite χ.range := by
    have : Finite (rootsOfUnity k ℂ) := inferInstance
    exact Finite.of_injective (fun x : χ.range => (⟨x.1, hrange x.2⟩ : rootsOfUnity k ℂ))
      (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
  have hfi : χ.ker.FiniteIndex := by
    have := Subgroup.finiteIndex_ker χ
    exact this
  refine ⟨?_, hfi⟩
  have hclosed : IsClosed (χ.ker : Set G) := by
    have : (χ.ker : Set G) = χ ⁻¹' {1} := by ext; simp
    rw [this]
    exact isClosed_singleton.preimage hc
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ hclosed

/-- `Wsub S T N N' P` contains an idele congruence subgroup (copied from the proof of `existsU_of_chevalley`). -/
theorem exists_cong_le_Wsub {S : Finset (HeightOneSpectrum (𝓞 K))} {T : Finset (InfinitePlace K)}
    {N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ}
    {N' : ∀ w : InfinitePlace K, Subgroup w.Completionˣ}
    (hN : ∀ v ∈ S, IsOpen (N v : Set (v.adicCompletion K)ˣ))
    (hN' : ∀ w ∈ T, IsOpen (N' w : Set w.Completionˣ)) (P : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ 𝔫 : TauCeti.GlobalNumberFields.Modulus K, ideleCongruenceSubgroup 𝔫 ≤ Wsub S T N N' P := by
  obtain ⟨𝔪A, h𝔪A⟩ := exists_ideleCongruenceSubgroup_le_of_isOpen (prescribed S T N N')
    (isOpen_prescribed hN hN')
  let 𝔫 : TauCeti.GlobalNumberFields.Modulus K :=
    ⟨𝔪A.finitePart * ∏ 𝔭 ∈ P, 𝔭.asIdeal, by
      rw [← Ideal.zero_eq_bot]
      exact mul_ne_zero 𝔪A.finitePart_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => by
        rw [Ideal.zero_eq_bot]; exact v.ne_bot), 𝔪A.infinitePart⟩
  have hdvd : 𝔪A ∣ 𝔫 := TauCeti.GlobalNumberFields.Modulus.dvd_iff.mpr ⟨dvd_mul_right _ _, Finset.Subset.refl _⟩
  refine ⟨𝔫, fun x hx => ?_⟩
  refine ⟨⟨h𝔪A (ideleCongruenceSubgroup_antitone hdvd hx),
    mem_unitsAway_iff.2 fun u _ =>
      ideleCongruenceSubgroup.valued_ideleFiniteCoord_eq_one hx u⟩,
    mem_principalAt_iff.2 fun 𝔭 h𝔭 => ?_⟩
  have h1 := ideleCongruenceSubgroup.ideleFiniteCoord_mem_unitFiltration hx 𝔭
  have hdv : 𝔭.asIdeal ∣ 𝔫.finitePart :=
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) h𝔭) _
  have hpos : 1 ≤ 𝔫.exponent 𝔭 :=
    TauCeti.GlobalNumberFields.Modulus.exponent_pos_of_mem_support ((TauCeti.GlobalNumberFields.Modulus.mem_support_iff 𝔫 𝔭).2 hdv)
  exact TauCeti.unitFiltration_antitone hpos h1

/-- The ideles concentrated on `S ∪ T` (trivial at every finite place outside `S` and every infinite place outside
`T`). -/
def concentrated (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K)) :
    Subgroup (IdeleGroup (𝓞 K) K) :=
  (⨅ u : {u : HeightOneSpectrum (𝓞 K) // u ∉ S}, u.1.ideleFiniteCoord.ker) ⊓
    ⨅ w : {w : InfinitePlace K // w ∉ T}, w.1.ideleInfiniteCoord.ker

theorem mem_concentrated_iff {S : Finset (HeightOneSpectrum (𝓞 K))} {T : Finset (InfinitePlace K)}
    {x : IdeleGroup (𝓞 K) K} :
    x ∈ concentrated S T ↔ (∀ u : HeightOneSpectrum (𝓞 K), u ∉ S → u.ideleFiniteCoord x = 1) ∧
      ∀ w : InfinitePlace K, w ∉ T → w.ideleInfiniteCoord x = 1 := by
  simp [concentrated, Subgroup.mem_iInf, MonoidHom.mem_ker]

/-- The product of the local characters, as a character of the ideles. -/
def prodChar (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (χ' : ∀ w : InfinitePlace K, w.Completionˣ →* ℂˣ) : IdeleGroup (𝓞 K) K →* ℂˣ :=
  (∏ v ∈ S, (χ v).comp v.ideleFiniteCoord) * ∏ w ∈ T, (χ' w).comp w.ideleInfiniteCoord

theorem prodChar_apply (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (χ' : ∀ w : InfinitePlace K, w.Completionˣ →* ℂˣ) (x : IdeleGroup (𝓞 K) K) :
    prodChar S T χ χ' x =
      (∏ v ∈ S, χ v (v.ideleFiniteCoord x)) * ∏ w ∈ T, χ' w (w.ideleInfiniteCoord x) := by
  simp [prodChar, MonoidHom.finsetProd_apply]

theorem prodChar_ofAdicCompletion {S : Finset (HeightOneSpectrum (𝓞 K))} (T : Finset (InfinitePlace K))
    (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (χ' : ∀ w : InfinitePlace K, w.Completionˣ →* ℂˣ) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S)
    (y : (v.adicCompletion K)ˣ) :
    prodChar S T χ χ' (IdeleGroup.ofAdicCompletion (𝓞 K) K v y) = χ v y := by
  rw [prodChar_apply]
  have h2 : ∏ w ∈ T, χ' w (w.ideleInfiniteCoord (IdeleGroup.ofAdicCompletion (𝓞 K) K v y)) = 1 :=
    Finset.prod_eq_one fun w _ => by simp [InfinitePlace.ideleInfiniteCoord_ofAdicCompletion]
  rw [h2, mul_one, Finset.prod_eq_single v]
  · simp [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self]
  · intro u _ huv
    simp [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne u huv]
  · intro h; exact absurd hv h

theorem prodChar_ofCompletion (S : Finset (HeightOneSpectrum (𝓞 K))) {T : Finset (InfinitePlace K)}
    (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (χ' : ∀ w : InfinitePlace K, w.Completionˣ →* ℂˣ) {w : InfinitePlace K} (hw : w ∈ T)
    (y : w.Completionˣ) :
    prodChar S T χ χ' (IdeleGroup.ofCompletion (𝓞 K) K w y) = χ' w y := by
  rw [prodChar_apply]
  have h1 : ∏ v ∈ S, χ v (v.ideleFiniteCoord (IdeleGroup.ofCompletion (𝓞 K) K w y)) = 1 :=
    Finset.prod_eq_one fun v _ => by simp [HeightOneSpectrum.ideleFiniteCoord_ofCompletion]
  rw [h1, one_mul, Finset.prod_eq_single w]
  · simp [InfinitePlace.ideleInfiniteCoord_ofCompletion_self]
  · intro u _ huw
    simp [InfinitePlace.ideleInfiniteCoord_ofCompletion_of_ne u huw]
  · intro h; exact absurd hw h

/-- **Characters of `C_K` with prescribed local components, from a subgroup `W` of the ideles.** -/
theorem exists_char_of_subgroup (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (χ' : ∀ w : InfinitePlace K, w.Completionˣ →* ℂˣ)
    (W : Subgroup (IdeleGroup (𝓞 K) K)) (𝔫 : TauCeti.GlobalNumberFields.Modulus K) (h𝔫 : ideleCongruenceSubgroup 𝔫 ≤ W)
    (hW : ∀ x : IdeleGroup (𝓞 K) K, x ∈ concentrated S T →
      (x : IdeleClassGroup (𝓞 K) K) ∈ W.map (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) →
      (∀ v ∈ S, χ v (v.ideleFiniteCoord x) = 1) ∧ ∀ w ∈ T, χ' w (w.ideleInfiniteCoord x) = 1) :
    ∃ ψ : IdeleClassGroup (𝓞 K) K →* ℂˣ, Continuous ψ ∧
      (∀ y ∈ W.map (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)), ψ y = 1) ∧
      (∀ v ∈ S, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v)) = χ v) ∧
      (∀ w ∈ T, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofCompletion (𝓞 K) K w)) = χ' w) := by
  set U : Subgroup (IdeleClassGroup (𝓞 K) K) :=
    W.map (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) with hU
  have hle : raySubgroup 𝔫 ≤ U := Subgroup.map_mono h𝔫
  have hUo : IsOpen (U : Set (IdeleClassGroup (𝓞 K) K)) := Subgroup.isOpen_mono hle (isOpen_raySubgroup 𝔫)
  have hUf : U.FiniteIndex := Subgroup.finiteIndex_of_le hle
  haveI : Finite (IdeleClassGroup (𝓞 K) K ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
  let J := concentrated S T
  let π : IdeleGroup (𝓞 K) K →* IdeleClassGroup (𝓞 K) K ⧸ U :=
    (QuotientGroup.mk' U).comp (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))
  let f : J →* IdeleClassGroup (𝓞 K) K ⧸ U := π.comp J.subtype
  let g : J →* ℂˣ := (prodChar S T χ χ').comp J.subtype
  have hker : f.ker ≤ g.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxU : ((x : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K) ∈ U :=
      (QuotientGroup.eq_one_iff _).1 hx
    obtain ⟨h1, h2⟩ := hW x x.2 hxU
    show prodChar S T χ χ' x = 1
    rw [prodChar_apply, Finset.prod_eq_one h1, Finset.prod_eq_one h2, mul_one]
  let h : f.range →* ℂˣ :=
    (QuotientGroup.lift f.ker g hker).comp (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom
  have hh : ∀ x : J, h (f.rangeRestrict x) = g x := by
    intro x
    have : (QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict x) = (x : J ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [h, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, QuotientGroup.lift_mk]
  letI : CommGroup (IdeleClassGroup (𝓞 K) K ⧸ U) :=
    { (inferInstance : Group (IdeleClassGroup (𝓞 K) K ⧸ U)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on
        induction b using QuotientGroup.induction_on
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm'] }
  haveI : NeZero ((Monoid.exponent (IdeleClassGroup (𝓞 K) K ⧸ U) : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨ψ₀, hψ₀⟩ := MonoidHom.domRestrict_surjective (G := IdeleClassGroup (𝓞 K) K ⧸ U) (M := ℂ) f.range h
  have hψ₀' : ∀ x : J, ψ₀ (f x) = g x := by
    intro x
    rw [← hh x]
    have := congrArg (fun φ : f.range →* ℂˣ => φ (f.rangeRestrict x)) hψ₀
    simpa using this
  let ψ : IdeleClassGroup (𝓞 K) K →* ℂˣ := ψ₀.comp (QuotientGroup.mk' U)
  have hψU : ∀ y ∈ U, ψ y = 1 := by
    intro y hy
    simp [ψ, (QuotientGroup.eq_one_iff y).2 hy]
  refine ⟨ψ, ?_, hψU, ?_, ?_⟩
  · refine continuous_of_continuousAt_one ψ ?_
    have hev : (ψ : IdeleClassGroup (𝓞 K) K → ℂˣ) =ᶠ[nhds 1] fun _ => 1 :=
      Filter.eventually_of_mem (hUo.mem_nhds U.one_mem) fun y hy => hψU y hy
    exact (continuousAt_const (y := (1 : ℂˣ))).congr hev.symm
  · intro v hv
    ext1 y
    have hJ : IdeleGroup.ofAdicCompletion (𝓞 K) K v y ∈ J := by
      rw [mem_concentrated_iff]
      refine ⟨fun u hu => ?_, fun w _ => ?_⟩
      · exact HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne u (fun h => hu (h ▸ hv)) y
      · simp [InfinitePlace.ideleInfiniteCoord_ofAdicCompletion]
    have := hψ₀' ⟨_, hJ⟩
    simp only [g, MonoidHom.comp_apply, Subgroup.coe_subtype, prodChar_ofAdicCompletion T χ χ' hv] at this
    simpa [ψ, f, π] using this
  · intro w hw
    ext1 y
    have hJ : IdeleGroup.ofCompletion (𝓞 K) K w y ∈ J := by
      rw [mem_concentrated_iff]
      refine ⟨fun u _ => ?_, fun w' hw' => ?_⟩
      · simp [HeightOneSpectrum.ideleFiniteCoord_ofCompletion]
      · exact InfinitePlace.ideleInfiniteCoord_ofCompletion_of_ne w' (fun h => hw' (h ▸ hw)) y
    have := hψ₀' ⟨_, hJ⟩
    simp only [g, MonoidHom.comp_apply, Subgroup.coe_subtype, prodChar_ofCompletion S χ χ' hw] at this
    simpa [ψ, f, π] using this

end NumberFieldKB.MilneCFT.Ch8.GW
