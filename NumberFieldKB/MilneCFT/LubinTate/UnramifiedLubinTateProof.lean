import NumberFieldKB.MilneCFT.LubinTate.LocalKroneckerWeberCFT
import NumberFieldKB.MilneCFT.LubinTate.RamificationQuotientTauCeti
import NumberFieldKB.MilneCFT.LocalCFT.UnramifiedTauCeti
import NumberFieldKB.MilneCFT.LocalCFT.TotallyRamifiedTauCeti

/-!
# Lemma 4.10 (Milne, *CFT*, I, §4), proved by a degree count

`lubinTateUnramified`: the named statement `LubinTateUnramified K Ω` (for `K Ω : Type`, the universe of
`lubinTateExtensionTheorem`): a finite `L' ⊇ K_{π,n}` with `e(L'/K) = e(K_{π,n}/K)` lies in `K_π K^un`.

Proof. Let `M = K_{π,n}`, `f = f(L'/K)` and `T = TauCeti.unramifiedExtension K Ω f`. Since `|l'| = q^f`, `L'`
contains a primitive `(q^f-1)`-st root of unity (Teichmüller), so `T ≤ L'`. Put `N = M ⊔ T ≤ L'`. By
multiplicativity of `e` and `f` in towers (`tower_ef`), `e(M) ∣ e(N)` and `f ∣ f(N)`, so
`[N:K] = e(N) f(N) ≥ e(M) f = e(L') f = [L':K]` (using `e(M) = [M:K] = e(L')`, `M` totally ramified,
Theorem 3.6). Hence `L' = M ⊔ T ≤ K_π ⊔ K^un`. Our `ramIdx` is Tau Ceti's `ramificationIndex`
(`ramIdx_eq_ramificationIndex`).
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Compatible

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [ValuativeRel L] [TopologicalSpace L]
  [ValuativeExtension K L] [IsNonarchimedeanLocalField L]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Our `ramIdx` is Tau Ceti's ramification index. -/
theorem ramIdx_eq_ramificationIndex : ramIdx L = TauCeti.ramificationIndex K L := by
  have : Algebra.IsSeparable K L := by
    have : Algebra.IsSeparable K Ω := IsSepClosure.separable
    exact Algebra.isSeparable_tower_bot_of_isSeparable K L Ω
  have hD : IsDedekindDomain (integers L) := integralClosure.isDedekindDomain 𝒪[K] K L
  set e := TauCeti.integerRingEquivIntegralClosure K L
  have hm : maxIdealL L = (𝓂[L]).map (e : 𝒪[L] →+* integers L) := by
    rw [← comap_maxIdealL L]
    exact (Ideal.map_comap_of_surjective (e : 𝒪[L] →+* integers L) e.surjective _).symm
  have hmax : (maxIdealL L).IsMaximal := by
    have h : maxIdealL L = (𝓂[L]).comap (e.toRingEquiv.symm : integers L →+* 𝒪[L]) := by
      rw [hm]; exact Ideal.map_comap_of_equiv e.toRingEquiv
    rw [h]
    exact Ideal.comap_isMaximal_of_surjective _ e.toRingEquiv.symm.surjective
  have hinj1 : Function.Injective (algebraMap 𝒪[K] (integers L)) := by
    intro a b h
    have h' : algebraMap K L (a : K) = algebraMap K L (b : K) := congrArg (fun x : integers L => (x : L)) h
    exact Subtype.ext ((algebraMap K L).injective h')
  have hinj2 : Function.Injective (algebraMap 𝒪[K] 𝒪[L]) := by
    intro a b h
    have h' : algebraMap K L (a : K) = algebraMap K L (b : K) := congrArg (fun x : 𝒪[L] => (x : L)) h
    exact Subtype.ext ((algebraMap K L).injective h')
  have hne : (𝓂[K]) ≠ ⊥ := IsDiscreteValuationRing.not_a_field 𝒪[K]
  have hne1 : (𝓂[K]).map (algebraMap 𝒪[K] (integers L)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hinj1).not.mpr hne
  have hne2 : (𝓂[K]).map (algebraMap 𝒪[K] 𝒪[L]) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hinj2).not.mpr hne
  have hlies : (maxIdealL L).LiesOver 𝓂[K] := by
    refine ⟨?_⟩
    have : ((maxIdealL L).under 𝒪[K]).IsMaximal := by
      exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maxIdealL L)
    exact (IsLocalRing.eq_maximalIdeal this).symm
  have hliesL : 𝓂[L].LiesOver 𝓂[K] := by
    refine ⟨?_⟩
    have h1 := hlies.over
    rw [h1, Ideal.under, Ideal.under, ← comap_maxIdealL L, Ideal.comap_comap]
    congr 1
  rw [ramIdx, ← Ideal.ramificationIdx'_eq_ramificationIdx' 𝓂[K] (maxIdealL L) hne1, show maxIdealL L = Ideal.map e 𝓂[L] from hm,
    Ideal.ramificationIdx'_map_eq,
    Ideal.ramificationIdx'_eq_ramificationIdx' 𝓂[K] 𝓂[L] hne2,
    TauCeti.ramificationIndex_eq_ramificationIdx]

end Compatible

/-- Install Tau Ceti's local-field structure on a finite intermediate field. -/
theorem withLocal (L : IntermediateField K Ω) [FiniteDimensional K L] {P : Prop}
    (h : ∀ (_ : ValuativeRel L) (_ : TopologicalSpace L) (_ : ValuativeExtension K L)
      (_ : IsNonarchimedeanLocalField L), P) : P := by
  let _ : ValuativeRel L := TauCeti.finiteIntermediateFieldValuativeRel K Ω L
  let _ : TopologicalSpace L := TauCeti.finiteIntermediateFieldTopology K Ω L
  exact h _ _ (TauCeti.finiteIntermediateField_valuativeExtension K Ω L)
    (TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω L)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- `e f = [L:K]`, with `|l| = q^f`, structure-free. -/
theorem exists_ef (L : IntermediateField K Ω) [FiniteDimensional K L] :
    ∃ f, 0 < f ∧ Nat.card (residueFieldL L) = resCard K ^ f ∧ 0 < ramIdx L ∧
      Module.finrank K L = ramIdx L * f := by
  refine withLocal L fun _ _ _ _ => ?_
  refine ⟨TauCeti.inertiaDegree K L, TauCeti.inertiaDegree_pos, ?_, ?_, ?_⟩
  · rw [natCard_residueFieldL, TauCeti.natCard_residueField K L]
  · rw [ramIdx_eq_ramificationIndex]; exact TauCeti.ramificationIndex_pos
  · rw [ramIdx_eq_ramificationIndex, TauCeti.ramificationIndex_mul_inertiaDegree]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- A totally ramified extension has `ramIdx = [L:K]`. -/
theorem ramIdx_eq_finrank_of_totallyRamified (L : IntermediateField K Ω) [FiniteDimensional K L]
    (h : IsTotallyRamifiedExt L) : ramIdx L = Module.finrank K L := by
  refine withLocal L fun _ _ _ _ => ?_
  rw [ramIdx_eq_ramificationIndex]
  exact (isTotallyRamifiedExt_iff L).1 h

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Containing the unramified extension of degree `f` when the residue field has `q^f` elements. -/
theorem unramifiedExtension_le_of_card (L : IntermediateField K Ω) [FiniteDimensional K L] {f : ℕ}
    (hf : 0 < f) (hc : Nat.card (residueFieldL L) = resCard K ^ f) :
    TauCeti.unramifiedExtension K Ω f ≤ L := by
  refine withLocal L fun _ _ _ _ => ?_
  have hcard : Nat.card 𝓀[L] = Nat.card 𝓀[K] ^ f := by
    rw [← natCard_residueFieldL]; exact hc
  obtain ⟨η, hη⟩ := TauCeti.exists_isPrimitiveRoot_natCard_residueField_sub_one L
  rw [hcard] at hη
  have hηΩ := hη.map_of_injective (f := L.val) L.val.injective
  rw [TauCeti.unramifiedExtension_eq_adjoin_simple hf.ne' hηΩ, IntermediateField.adjoin_simple_le_iff]
  exact η.2

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- `T_f` is unramified with residue field of `q^f` elements. -/
theorem unramifiedExtension_facts [IsSepClosed Ω] {f : ℕ} (hf : 0 < f) :
    IsUnramifiedExt (TauCeti.unramifiedExtension K Ω f) ∧
      Nat.card (residueFieldL (TauCeti.unramifiedExtension K Ω f)) = resCard K ^ f := by
  set T := TauCeti.unramifiedExtension K Ω f
  refine withLocal T fun _ _ _ _ => ?_
  have hu : TauCeti.IsUnramified K T := TauCeti.isUnramified_unramifiedExtension hf.ne'
  refine ⟨(isUnramified_iff_isUnramifiedExt T).1 hu, ?_⟩
  rw [natCard_residueFieldL, TauCeti.natCard_residueField K T,
    TauCeti.IsUnramified.inertiaDegree_eq_finrank, TauCeti.finrank_unramifiedExtension hf.ne']

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- `e` and `f` increase (divisibility) in towers, structure-free. -/
theorem tower_ef (A B : IntermediateField K Ω) (h : A ≤ B) [FiniteDimensional K B] :
    ramIdx A ∣ ramIdx B ∧ ∀ a b, Nat.card (residueFieldL A) = resCard K ^ a →
      Nat.card (residueFieldL B) = resCard K ^ b → a ∣ b := by
  have : FiniteDimensional K A :=
    Module.Finite.of_injective (IntermediateField.inclusion h).toLinearMap
      (IntermediateField.inclusion_injective h)
  refine withLocal A fun _ _ _ _ => withLocal B fun _ _ _ _ => ?_
  let _ : Algebra A B := (IntermediateField.inclusion h).toAlgebra
  have : ValuativeExtension A B := (IntermediateField.inclusion h).valuativeExtension
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite A B := Module.Finite.of_restrictScalars_finite K A B
  have hq : 1 < resCard K := Finite.one_lt_card
  refine ⟨?_, fun a b ha hb => ?_⟩
  · rw [ramIdx_eq_ramificationIndex, ramIdx_eq_ramificationIndex,
      TauCeti.ramificationIndex_tower (K := K) (L := A) B]
    exact Dvd.intro _ rfl
  · rw [natCard_residueFieldL, TauCeti.natCard_residueField K A] at ha
    rw [natCard_residueFieldL, TauCeti.natCard_residueField K B] at hb
    have ha' := Nat.pow_right_injective hq ha
    have hb' := Nat.pow_right_injective hq hb
    rw [← ha', ← hb', TauCeti.inertiaDegree_tower (K := K) (L := A) B]
    exact Dvd.intro _ rfl

end NumberFieldKB.MilneCFT.LocalCFT

namespace NumberFieldKB.MilneCFT.LocalCFT

section Main

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Lemma 4.10, proved** (Milne, *CFT*, I, Lemma 4.10), for `K Ω : Type`. -/
@[kb "milne2020cft" "Ch. I, Lemma 4.10"]
theorem lubinTateUnramified : LubinTateUnramified K Ω := by
  refine ⟨fun {π} hπ n L' hfd hM hram => ?_⟩
  set M := ltField Ω π n with hMdef
  have : FiniteDimensional K M :=
    Module.Finite.of_injective (IntermediateField.inclusion hM).toLinearMap
      (IntermediateField.inclusion_injective hM)
  have hMe : ramIdx M = Module.finrank K M := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨f, hf, -, -, h⟩ := exists_ef M
      have h1 : Module.finrank K M = 1 := by
        rw [hMdef, IntermediateField.finrank_eq_one_iff, ltField, ltTorsion_zero]
        exact IntermediateField.adjoin_zero
      rw [h1] at h ⊢
      exact Nat.eq_one_of_mul_eq_one_right h.symm
    · exact ramIdx_eq_finrank_of_totallyRamified M
        ((lubinTateExtensionTheorem K Ω).totallyRamified hπ n hn)
  obtain ⟨f, hf, hcL, hL0, hLfin⟩ := exists_ef L'
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨hTun, hTcard⟩ := unramifiedExtension_facts (K := K) (Ω := Ω) hf
  set T := TauCeti.unramifiedExtension K Ω f with hTdef
  have hTL : T ≤ L' := unramifiedExtension_le_of_card L' hf hcL
  have hNL : M ⊔ T ≤ L' := sup_le hM hTL
  have : FiniteDimensional K (M ⊔ T : IntermediateField K Ω) :=
    Module.Finite.of_injective (IntermediateField.inclusion hNL).toLinearMap
      (IntermediateField.inclusion_injective hNL)
  obtain ⟨hdvdE, -⟩ := tower_ef M (M ⊔ T) le_sup_left
  obtain ⟨-, hdvdF⟩ := tower_ef T (M ⊔ T) le_sup_right
  obtain ⟨fN, hfN, hcN, hN0, hNfin⟩ := exists_ef (M ⊔ T)
  have h2 : ramIdx M ≤ ramIdx (M ⊔ T) := Nat.le_of_dvd hN0 hdvdE
  have h3 : f ≤ fN := Nat.le_of_dvd hfN (hdvdF f fN hTcard hcN)
  have hle : Module.finrank K L' ≤ Module.finrank K (M ⊔ T : IntermediateField K Ω) := by
    rw [hLfin, hram, hNfin]
    exact Nat.mul_le_mul h2 h3
  have hEq : M ⊔ T = L' := IntermediateField.eq_of_le_of_finrank_le hNL hle
  rw [← hEq]
  exact sup_le_sup (le_iSup (fun m => ltField Ω π m) n)
    (le_iSup₂_of_le T ⟨inferInstance, hTun⟩ le_rfl)

end Main

end NumberFieldKB.MilneCFT.LocalCFT
