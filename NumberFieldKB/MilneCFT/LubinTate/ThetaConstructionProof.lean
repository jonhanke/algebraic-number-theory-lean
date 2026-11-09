import NumberFieldKB.MilneCFT.LubinTate.IsoOverCompletionProof
import NumberFieldKB.MilneCFT.LubinTate.ThetaConstructionAux

/-!
# Proposition 3.10 (Milne, *Class Field Theory*, Ch. I): the construction of θ

Proof of the named statement `LubinTateThetaConstruction`, following Milne: first a series `θ₀` with
`θ₀^σ = θ₀ ∘ [u]_f` is built degree by degree (`exists_theta0`); then `h = θ₀^σ ∘ f ∘ θ₀⁻¹` is fixed by `σ`, hence
comes from a series `h'` over `A` lying in `ℱ_{uπ}`; finally `θ = [1]_{g,h'} ∘ θ₀`. Properties (c) and (d) follow
from `θ ∘ [uπ]_f = g ∘ θ` by a uniqueness argument over `B` (`eq_of_defect_zero`).
-/

open scoped ValuativeRel
open IsLocalRing

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

local notation:90 P:91 " ⊚ " Q:90 => PowerSeries.subst Q P

section Residue

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {B : Type} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B] {σ : B ≃+* B}

theorem algebraMap_injective' (h : IsCompletedUnramifiedInt K B σ) :
    Function.Injective (algebraMap 𝒪[K] B) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
  rw [map_mul, map_pow] at ha
  rcases mul_eq_zero.1 ha with h1 | h1
  · exact (v.isUnit.map _).ne_zero h1
  · exact (h.irreducible π hπ).ne_zero (pow_eq_zero_iff'.1 h1).1

theorem mem_span_of_algebraMap_mem (h : IsCompletedUnramifiedInt K B σ) {π : 𝒪[K]}
    (hπ : Irreducible π) {c : 𝒪[K]} (hc : algebraMap 𝒪[K] B c ∈ maximalIdeal B) :
    c ∈ Ideal.span {π} := by
  have := isLocalHom_algebraMap h π hπ
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, mem_maximalIdeal,
    mem_nonunits_iff]
  intro hu
  exact (mem_maximalIdeal _).1 hc |> fun h2 => (mem_nonunits_iff.1 h2) (hu.map _)

theorem span_algebraMap_le (h : IsCompletedUnramifiedInt K B σ) {π : 𝒪[K]} (hπ : Irreducible π)
    {c : 𝒪[K]} (hc : c ∈ Ideal.span {π}) : algebraMap 𝒪[K] B c ∈ maximalIdeal B := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 (h.irreducible π hπ)]
  obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem exists_charP (h : IsCompletedUnramifiedInt K B σ) :
    ∃ p n : ℕ, p.Prime ∧ CharP (ResidueField B) p ∧ resCard K = p ^ n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have := isLocalHom_algebraMap h π hπ
  obtain ⟨p, hp⟩ := CharP.exists 𝓀[K]
  let _ : Fintype 𝓀[K] := Fintype.ofFinite _
  obtain ⟨n, hpp, hn⟩ := FiniteField.card 𝓀[K] p
  refine ⟨p, n, hpp, ?_, ?_⟩
  · exact charP_of_injective_ringHom (ResidueField.map (algebraMap 𝒪[K] B)).injective p
  · rw [← hn]; exact Nat.card_eq_fintype_card

end Residue

section Hprime

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {B : Type} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B] {σ : B ≃+* B}

/-- The series `h = θ₀^σ ∘ f ∘ θ₀⁻¹` of Proposition 3.10 comes from a series `h'` over `A` lying in `ℱ_{uπ}`. -/
theorem exists_h' (hB : IsCompletedUnramifiedInt K B σ) {π : 𝒪[K]} (hπ : Irreducible π) (u : 𝒪[K]ˣ)
    {f U : PowerSeries 𝒪[K]} (hf : f ∈ lubinTateSeries π (resCard K))
    (hU0 : PowerSeries.constantCoeff U = 0) (_hU1 : PowerSeries.coeff 1 U = u) (hUf : U ⊚ f = f ⊚ U)
    {ε : Bˣ} (hε : σ ε = ε * algebraMap 𝒪[K] B u)
    {θ₀ : PowerSeries B} (h0 : PowerSeries.constantCoeff θ₀ = 0) (h1 : PowerSeries.coeff 1 θ₀ = ε)
    (hσ : PowerSeries.map σ.toRingHom θ₀ = θ₀ ⊚ PowerSeries.map (algebraMap 𝒪[K] B) U) :
    ∃ h' : PowerSeries 𝒪[K], h' ∈ lubinTateSeries ((u : 𝒪[K]) * π) (resCard K) ∧
      (PowerSeries.map (algebraMap 𝒪[K] B) h') ⊚ θ₀ =
        (PowerSeries.map σ.toRingHom θ₀) ⊚ (PowerSeries.map (algebraMap 𝒪[K] B) f) := by
  classical
  set φ := algebraMap 𝒪[K] B with hφ
  set σr : B →+* B := σ.toRingHom with hσr
  have hinj : Function.Injective φ := algebraMap_injective' hB
  have hfix : σr.comp φ = φ := RingHom.ext fun a => hB.frob_fix a
  let T0 : CS B := ⟨θ₀, h0⟩
  let UA : CS 𝒪[K] := ⟨U, hU0⟩
  let FA : CS 𝒪[K] := ⟨f, hf.1⟩
  have hUFA : UA * FA = FA * UA := Subtype.ext hUf
  have hσT0 : CS.map σr T0 = T0 * CS.map φ UA := Subtype.ext hσ
  have hσU : CS.map σr (CS.map φ UA) = CS.map φ UA := by rw [CS.map_map, hfix]
  have hσF : CS.map σr (CS.map φ FA) = CS.map φ FA := by rw [CS.map_map, hfix]
  have hUF : CS.map φ UA * CS.map φ FA = CS.map φ FA * CS.map φ UA := by
    rw [← map_mul, ← map_mul, hUFA]
  have hT0u : IsUnit (CS.c1 T0) := by
    show IsUnit (PowerSeries.coeff 1 θ₀)
    rw [h1]; exact ε.isUnit
  obtain ⟨H, hHT, hHσ⟩ := exists_fixed_conj σr T0 _ _ hT0u hσT0 hσU hσF hUF
  obtain ⟨h', hh'⟩ := exists_map_of_fixed φ σr (fun b hb => by
    have := ((frobeniusMinusOneSurjective (K := K)).add_ker B σ hB b).1 (by
      show σ b - b = 0
      rw [show σ b = b from hb, sub_self])
    exact this) H.1 (congrArg Subtype.val hHσ)
  have hcoeff : ∀ n, φ (PowerSeries.coeff n h') = PowerSeries.coeff n H.1 := fun n => by
    rw [← hh', PowerSeries.coeff_map]
  have hc0 : PowerSeries.constantCoeff h' = 0 := hinj (by
    rw [map_zero, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeff 0,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, H.2])
  have hc1 : PowerSeries.coeff 1 h' = (u : 𝒪[K]) * π := by
    have e := congrArg CS.c1 hHT
    rw [CS.c1_mul, CS.c1_mul, CS.c1_map, CS.c1_map] at e
    have e1 : CS.c1 H = φ (PowerSeries.coeff 1 h') := (hcoeff 1).symm
    have e2 : CS.c1 T0 = ε := h1
    have e3 : CS.c1 FA = π := hf.2.1
    have hε' : σr (ε : B) = ε * φ u := hε
    rw [e1, e2, e3, hε'] at e
    apply hinj
    apply mul_right_cancel₀ ε.ne_zero
    rw [map_mul]
    linear_combination e
  -- the reduction modulo the maximal ideal
  obtain ⟨p, m, hp, hcp, hq⟩ := exists_charP hB
  have : Fact p.Prime := ⟨hp⟩
  let R := ResidueField B
  let r : B →+* R := residue B
  have hrσ : ∀ b, r (σ b) = iterateFrobenius R p m (r b) := fun b => by
    rw [iterateFrobenius_def, ← hq]; exact residue_sigma hB b
  have key := congrArg (fun P : CS B => (CS.map r P).1) hHT
  simp only [map_mul, CS.val_mul] at key
  have key' : (PowerSeries.map r H.1) ⊚ (PowerSeries.map r θ₀) =
      (PowerSeries.map r (PowerSeries.map σr θ₀)) ⊚ (PowerSeries.map r (PowerSeries.map φ f)) := key
  have hA : PowerSeries.map r (PowerSeries.map σr θ₀) =
      PowerSeries.map (iterateFrobenius R p m) (PowerSeries.map r θ₀) := by
    ext n; simp only [PowerSeries.coeff_map]; exact hrσ _
  have h2 : ∀ n, r (φ (PowerSeries.coeff n (PowerSeries.X ^ resCard K : PowerSeries 𝒪[K]))) =
      PowerSeries.coeff n (PowerSeries.X ^ resCard K : PowerSeries R) := by
    intro n
    simp only [PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  have hrf : PowerSeries.map r (PowerSeries.map φ f) = PowerSeries.X ^ resCard K := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map, ← h2 n]
    have := span_algebraMap_le hB hπ (hf.2.2 n)
    rw [← residue_eq_zero_iff, map_sub] at this
    exact sub_eq_zero.1 this
  have hθ0 : PowerSeries.constantCoeff (PowerSeries.map r θ₀) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  have hθ1 : IsUnit (PowerSeries.coeff 1 (PowerSeries.map r θ₀)) := by
    rw [PowerSeries.coeff_map, h1]; exact ε.isUnit.map r
  have hHbar : PowerSeries.map r H.1 = PowerSeries.X ^ resCard K := by
    refine subst_right_cancel hθ0 hθ1 ?_
    rw [key', hA, hrf, hq, map_frobenius_subst_X_pow m, PowerSeries.subst_pow (hs0 hθ0),
      PowerSeries.subst_X (hs0 hθ0)]
  have hirr : Irreducible ((u : 𝒪[K]) * π) := (irreducible_units_mul u).2 hπ
  refine ⟨h', ⟨hc0, hc1, fun n => ?_⟩, ?_⟩
  · apply mem_span_of_algebraMap_mem hB hirr
    rw [map_sub, ← residue_eq_zero_iff]
    show r (_ - _) = 0
    rw [map_sub, h2 n, ← hHbar, PowerSeries.coeff_map, ← hcoeff n]
    exact sub_self _
  · show (PowerSeries.map φ h') ⊚ θ₀ = _
    rw [hh']
    exact congrArg Subtype.val hHT

end Hprime

section FormalGroupLaw

open MvPowerSeries in
/-- Uniqueness argument for property (c): if `g ∘ θ = θ ∘ V`, `V` is an endomorphism of the law `Ft` and `g` an
endomorphism of the law `Gt`, then `θ` is a homomorphism `Ft → Gt`. Both `θ(Ft(X,Y))` and `Gt(θX, θY)` satisfy
the functional equation `g ∘ Φ = Φ(V, V)` with the same linear terms, and such solutions are unique
(`eq_of_defect_zero`). -/
theorem eq_formal_group_hom {B : Type*} [CommRing B] [IsDomain B] {ϖ : B} (hϖ0 : ϖ ≠ 0)
    (hϖ1 : ¬ IsUnit ϖ)
    {g V θ : PowerSeries B} (hg0 : PowerSeries.constantCoeff g = 0) (hg1 : PowerSeries.coeff 1 g = ϖ)
    (hV0 : PowerSeries.constantCoeff V = 0) (hV1 : PowerSeries.coeff 1 V = ϖ)
    (hθ0 : PowerSeries.constantCoeff θ = 0)
    {Ft Gt : MvPowerSeries (Fin 2) B} (hF0 : constantCoeff Ft = 0) (hG0 : constantCoeff Gt = 0)
    (hF1 : ∀ i, coeff (Finsupp.single i 1) Ft = 1) (hG1 : ∀ i, coeff (Finsupp.single i 1) Gt = 1)
    (hgθ : g ⊚ θ = θ ⊚ V)
    (hV : V.subst Ft = Ft.subst ![V.subst (X 0 : MvPowerSeries (Fin 2) B),
      V.subst (X 1 : MvPowerSeries (Fin 2) B)])
    (hg : g.subst Gt = Gt.subst ![g.subst (X 0 : MvPowerSeries (Fin 2) B),
      g.subst (X 1 : MvPowerSeries (Fin 2) B)]) :
    θ.subst Ft = Gt.subst ![θ.subst (X 0 : MvPowerSeries (Fin 2) B),
      θ.subst (X 1 : MvPowerSeries (Fin 2) B)] := by
  classical
  have hθs : PowerSeries.HasSubst θ := hs0 hθ0
  have hFs : PowerSeries.HasSubst Ft := PowerSeries.HasSubst.of_constantCoeff_zero hF0
  have hVs : MvPowerSeries.HasSubst (fun i : Fin 2 => V.subst (X i : MvPowerSeries (Fin 2) B)) :=
    NumberFieldKB.MilneCFT.hasSubst_twist hV0
  have hgs : MvPowerSeries.HasSubst (fun i : Fin 2 => g.subst (X i : MvPowerSeries (Fin 2) B)) :=
    NumberFieldKB.MilneCFT.hasSubst_twist hg0
  have hvec : ∀ ρ : PowerSeries B, (![ρ.subst (X 0 : MvPowerSeries (Fin 2) B),
      ρ.subst (X 1 : MvPowerSeries (Fin 2) B)] : Fin 2 → MvPowerSeries (Fin 2) B) =
      fun i => ρ.subst (X i : MvPowerSeries (Fin 2) B) := by
    intro ρ; funext i; fin_cases i <;> rfl
  rw [hvec θ]
  rw [hvec V] at hV
  rw [hvec g] at hg
  set W : Fin 2 → MvPowerSeries (Fin 2) B := fun k => θ.subst (X k) with hWdef
  have hW0 : ∀ k, constantCoeff (W k) = 0 := fun k =>
    NumberFieldKB.MilneCFT.constantCoeff_twist hθ0 k
  have hWs : MvPowerSeries.HasSubst W := hasSubst_of_constantCoeff_zero hW0
  have hgW : ∀ k, g.subst (W k) = θ.subst (V.subst (X k : MvPowerSeries (Fin 2) B)) := by
    intro k
    have hXk : PowerSeries.HasSubst (X k : MvPowerSeries (Fin 2) B) := PowerSeries.HasSubst.X k
    have h1 := PowerSeries.subst_comp_subst_apply hθs hXk g
    have h2 := PowerSeries.subst_comp_subst_apply (hs0 hV0) hXk θ
    rw [hWdef]
    simp only
    rw [← h2, ← hgθ, h1]
  have hc : ∀ i j : Fin 2, coeff (Finsupp.single i 1) (W j) =
      if i = j then PowerSeries.coeff 1 θ else 0 := by
    intro i j
    have := NumberFieldKB.MilneCFT.coeff_single_subst (τ := Unit) (P := θ) hθ0
      (v := fun _ => (X j : MvPowerSeries (Fin 2) B)) (fun _ => MvPowerSeries.constantCoeff_X j) i
    change coeff (Finsupp.single i 1)
      (MvPowerSeries.subst (fun _ : Unit => (X j : MvPowerSeries (Fin 2) B)) θ) = _
    rw [this]
    simp [coeff_X, Finsupp.single_left_inj]
  refine eq_of_defect_zero hϖ0 hϖ1 hg0 hg1 hV0 hV1 ?_ ?_ ?_ ?_ ?_
  · exact PowerSeries.constantCoeff_subst_eq_zero hF0 θ hθ0
  · exact constantCoeff_subst_eq_zero hWs hW0 hG0
  · intro i
    have h1 := NumberFieldKB.MilneCFT.coeff_single_subst (τ := Unit) (P := θ) hθ0
      (v := fun _ => Ft) (fun _ => hF0) i
    have h2 := NumberFieldKB.MilneCFT.coeff_single_subst hG0 hW0 i
    change coeff (Finsupp.single i 1) (MvPowerSeries.subst (fun _ : Unit => Ft) θ) = _
    rw [h1, h2]
    simp [hF1, hG1, hc]
  · -- the left series
    have hgS : (NumberFieldKB.MilneCFT.gSub V : Fin 2 → MvPowerSeries (Fin 2) B) =
        fun i => V.subst (X i : MvPowerSeries (Fin 2) B) := rfl
    unfold NumberFieldKB.MilneCFT.defect
    rw [hgS, sub_eq_zero]
    have e1 : g.subst (θ.subst Ft) = θ.subst (V.subst Ft) :=
      (PowerSeries.subst_comp_subst_apply hθs hFs g).symm.trans (by
        rw [hgθ]; exact PowerSeries.subst_comp_subst_apply (hs0 hV0) hFs θ)
    have e2 := NumberFieldKB.MilneCFT.mvSubst_powerSeriesSubst (φ := Ft) hF0 θ
      (v := fun i : Fin 2 => V.subst (X i : MvPowerSeries (Fin 2) B)) hVs
    rw [e1, e2, hV]
  · unfold NumberFieldKB.MilneCFT.defect
    rw [sub_eq_zero]
    have e3 := NumberFieldKB.MilneCFT.mvSubst_powerSeriesSubst (φ := Gt) hG0 g hWs
    have e5 : ∀ i, MvPowerSeries.subst W (g.subst (X i : MvPowerSeries (Fin 2) B)) =
        g.subst (W i) := by
      intro i
      rw [NumberFieldKB.MilneCFT.mvSubst_powerSeriesSubst (by simp) g hWs, subst_X hWs]
    have e6 : ∀ k, MvPowerSeries.subst (fun i : Fin 2 => V.subst (X i : MvPowerSeries (Fin 2) B)) (W k) =
        θ.subst (V.subst (X k : MvPowerSeries (Fin 2) B)) := by
      intro k
      simp only [hWdef]
      rw [NumberFieldKB.MilneCFT.mvSubst_powerSeriesSubst (by simp) θ hVs, subst_X hVs]
    change _ = MvPowerSeries.subst (fun i : Fin 2 => V.subst (X i : MvPowerSeries (Fin 2) B))
      (MvPowerSeries.subst W Gt)
    rw [← e3, hg, subst_comp_subst_apply hgs hWs, subst_comp_subst_apply hWs hVs]
    congr 1
    funext k
    rw [e5, e6, hgW]

end FormalGroupLaw

section Assembly

theorem vec2_eq {C : Type*} [CommRing C] (ρ : PowerSeries C) :
    (![ρ.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) C),
      ρ.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) C)] : Fin 2 → MvPowerSeries (Fin 2) C) =
      fun i => ρ.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) C) := by
  funext i; fin_cases i <;> rfl

open MvPowerSeries in
/-- A homomorphism-like property of a series `E` of `A` (`E(F(X,Y)) = G(E X, E Y)`) is preserved by mapping the
coefficients along a ring homomorphism. -/
theorem map_end_add {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B) {F G : MvPowerSeries (Fin 2) A}
    {E : PowerSeries A} (hF0 : constantCoeff F = 0) (hE0 : PowerSeries.constantCoeff E = 0)
    (h : E.subst F = G.subst ![E.subst (X 0 : MvPowerSeries (Fin 2) A),
      E.subst (X 1 : MvPowerSeries (Fin 2) A)]) :
    (PowerSeries.map ψ E).subst (MvPowerSeries.map ψ F) =
      (MvPowerSeries.map ψ G).subst ![(PowerSeries.map ψ E).subst (X 0 : MvPowerSeries (Fin 2) B),
        (PowerSeries.map ψ E).subst (X 1 : MvPowerSeries (Fin 2) B)] := by
  rw [vec2_eq] at h ⊢
  have hw : MvPowerSeries.HasSubst (fun i : Fin 2 => E.subst (X i : MvPowerSeries (Fin 2) A)) :=
    NumberFieldKB.MilneCFT.hasSubst_twist hE0
  have h1 := congrArg (MvPowerSeries.map ψ) h
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF0) E,
    MvPowerSeries.map_subst hw G] at h1
  refine h1.trans ?_
  congr 1
  funext i
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.X i) E, MvPowerSeries.map_X]

/-- Uniqueness for one variable: two series with the same linear term satisfying `g ∘ P = P ∘ V` are equal. -/
theorem eq_of_comm_unit {B : Type*} [CommRing B] [IsDomain B] {ϖ : B} (hϖ0 : ϖ ≠ 0) (hϖ1 : ¬ IsUnit ϖ)
    {g V P Q : PowerSeries B} (hg0 : PowerSeries.constantCoeff g = 0) (hg1 : PowerSeries.coeff 1 g = ϖ)
    (hV0 : PowerSeries.constantCoeff V = 0) (hV1 : PowerSeries.coeff 1 V = ϖ)
    (hP0 : PowerSeries.constantCoeff P = 0) (hQ0 : PowerSeries.constantCoeff Q = 0)
    (hlin : PowerSeries.coeff 1 P = PowerSeries.coeff 1 Q) (hP : g ⊚ P = P ⊚ V) (hQ : g ⊚ Q = Q ⊚ V) :
    P = Q := by
  have hdef : ∀ R : PowerSeries B, g ⊚ R = R ⊚ V →
      NumberFieldKB.MilneCFT.defect g V (R : MvPowerSeries Unit B) = 0 := by
    intro R hR
    unfold NumberFieldKB.MilneCFT.defect
    rw [sub_eq_zero]
    show _ = MvPowerSeries.subst (fun i : Unit => V.subst (MvPowerSeries.X i : MvPowerSeries Unit B)) R
    rw [NumberFieldKB.MilneCFT.twist_unit]
    exact hR
  exact eq_of_defect_zero (ι := Unit) hϖ0 hϖ1 hg0 hg1 hV0 hV1 (φ := P) (ψ := Q) hP0 hQ0
    (fun _ => hlin) (hdef P hP) (hdef Q hQ)

end Assembly

section Main

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {B : Type} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B] {σ : B ≃+* B}

/-- **Proposition 3.10** (Milne, *CFT*, I): the construction of `θ`, in the form of the named statement. -/
theorem theta_construct (hB : IsCompletedUnramifiedInt K B σ) {π : 𝒪[K]} (hπ : Irreducible π)
    (u : 𝒪[K]ˣ) {f g : PowerSeries 𝒪[K]} (hf : f ∈ lubinTateSeries π (resCard K))
    (hg : g ∈ lubinTateSeries ((u : 𝒪[K]) * π) (resCard K)) (ε : Bˣ)
    (hε : σ ε = ε * algebraMap 𝒪[K] B u) :
    ∃ θ : PowerSeries B,
      PowerSeries.constantCoeff θ = 0 ∧ PowerSeries.coeff 1 θ = ε ∧
      PowerSeries.map σ.toRingHom θ = θ.subst (PowerSeries.map (algebraMap 𝒪[K] B)
        (lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) hf u).toPowerSeries) ∧
      θ.subst (MvPowerSeries.map (algebraMap 𝒪[K] B)
          (lubinTateFormalGroup (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) hf).toPowerSeries) =
        (MvPowerSeries.map (algebraMap 𝒪[K] B) (lubinTateFormalGroup
          (lubinTateHyp_of_isNonarchimedeanLocalField K ((irreducible_units_mul u).2 hπ)) hg).toPowerSeries).subst
          ![θ.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) B),
            θ.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) B)] ∧
      ∀ a : 𝒪[K], θ.subst (PowerSeries.map (algebraMap 𝒪[K] B)
          (lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) hf a).toPowerSeries) =
        (PowerSeries.map (algebraMap 𝒪[K] B) (lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K
          ((irreducible_units_mul u).2 hπ)) hg
            a).toPowerSeries).subst θ := by
  classical
  set φ := algebraMap 𝒪[K] B with hφ
  set σr : B →+* B := σ.toRingHom with hσr
  have hinj : Function.Injective φ := algebraMap_injective' hB
  have hfix : σr.comp φ = φ := RingHom.ext fun a => hB.frob_fix a
  have hirr : Irreducible ((u : 𝒪[K]) * π) := (irreducible_units_mul u).2 hπ
  set H := lubinTateHyp_of_isNonarchimedeanLocalField K hπ with hH
  set H' := lubinTateHyp_of_isNonarchimedeanLocalField K hirr with hH'
  -- the data over `A`
  obtain ⟨hU0, hU1, hUspec⟩ := lubinTateSeriesHom_spec H hf hf (u : 𝒪[K])
  set U : PowerSeries 𝒪[K] := lubinTateSeriesHom H hf hf (u : 𝒪[K]) with hU
  have hUf : U ⊚ f = f ⊚ U := hUspec.symm
  have hUt0 : PowerSeries.constantCoeff (PowerSeries.map φ U) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hU0, map_zero]
  have hUt1 : PowerSeries.coeff 1 (PowerSeries.map φ U) = φ u := by
    rw [PowerSeries.coeff_map, hU1]
  have hsolve : ∀ c : B, ∃ b, σr b - b = c :=
    (frobeniusMinusOneSurjective (K := K)).add_surjective B σ hB
  obtain ⟨θ₀, h0, h1, hσ⟩ := exists_theta0 σr hsolve hUt0 (u.isUnit.map φ) hUt1 ε.isUnit hε
  obtain ⟨h', hh'mem, hh'eq⟩ := exists_h' hB hπ u hf hU0 hU1 hUf hε h0 h1 hσ
  -- the isomorphism `[1]_{g,h'}`
  obtain ⟨hG0, hG1, hGspec⟩ := lubinTateSeriesHom_spec H' hh'mem hg (1 : 𝒪[K])
  set G : PowerSeries 𝒪[K] := lubinTateSeriesHom H' hh'mem hg (1 : 𝒪[K]) with hG
  -- the series `V = [uπ]_f = U ∘ f`
  have hpi : lubinTateSeriesHom H hf hf π = f := lubinTateEnd_pi H hf
  obtain ⟨hV0, hV1, hVspec⟩ := lubinTateSeriesHom_spec H hf hf ((u : 𝒪[K]) * π)
  set V : PowerSeries 𝒪[K] := lubinTateSeriesHom H hf hf ((u : 𝒪[K]) * π) with hV
  have hVUf : V = U ⊚ f := by
    rw [hV, lubinTateSeriesHom_mul H hf hf hf (u : 𝒪[K]) π, hpi]
  -- elements of the monoid of series
  let gA : CS 𝒪[K] := ⟨g, hg.1⟩
  let GA : CS 𝒪[K] := ⟨G, hG0⟩
  let h'A : CS 𝒪[K] := ⟨h', hh'mem.1⟩
  let UA : CS 𝒪[K] := ⟨U, hU0⟩
  let FA : CS 𝒪[K] := ⟨f, hf.1⟩
  let VA : CS 𝒪[K] := ⟨V, hV0⟩
  let T0 : CS B := ⟨θ₀, h0⟩
  have hA1 : gA * GA = GA * h'A := Subtype.ext hGspec
  have hA2 : h'A.map φ * T0 = CS.map σr T0 * FA.map φ := Subtype.ext hh'eq
  have hA3 : CS.map σr T0 = T0 * UA.map φ := Subtype.ext hσ
  have hA4 : VA = UA * FA := Subtype.ext hVUf
  have hGfix : CS.map σr (GA.map φ) = GA.map φ := by rw [CS.map_map, hfix]
  let thC : CS B := GA.map φ * T0
  have hth0 : PowerSeries.constantCoeff thC.1 = 0 := thC.2
  have hth1 : PowerSeries.coeff 1 thC.1 = ε := by
    have := CS.c1_mul (GA.map φ) T0
    rw [CS.c1_map] at this
    show CS.c1 thC = ε
    rw [this]
    show φ (PowerSeries.coeff 1 G) * PowerSeries.coeff 1 θ₀ = ε
    rw [hG1, h1, map_one, one_mul]
  have hb : CS.map σr thC = thC * UA.map φ := by
    show CS.map σr (GA.map φ * T0) = _
    rw [map_mul, hGfix, hA3, mul_assoc]
  have key : gA.map φ * thC = thC * VA.map φ := by
    show gA.map φ * (GA.map φ * T0) = (GA.map φ * T0) * VA.map φ
    rw [← mul_assoc, ← map_mul, hA1, map_mul, mul_assoc, hA2, hA3, hA4, map_mul]
    simp only [mul_assoc]
  refine ⟨thC.1, hth0, hth1, congrArg Subtype.val hb, ?_, ?_⟩
  · -- property (c)
    have hϖ : Irreducible (φ ((u : 𝒪[K]) * π)) := hB.irreducible _ hirr
    have hFf0 := (lubinTateFormalGroup H hf).zero_constantCoeff
    have hFg0 := (lubinTateFormalGroup H' hg).zero_constantCoeff
    have mapc0 : ∀ F : MvPowerSeries (Fin 2) 𝒪[K], MvPowerSeries.constantCoeff F = 0 →
        MvPowerSeries.constantCoeff (MvPowerSeries.map φ F) = 0 := by
      intro F hF
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF, map_zero]
    have mapc1 : ∀ F : FormalGroup 𝒪[K], ∀ i : Fin 2,
        MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.map φ F.toPowerSeries) = 1 := by
      intro F i
      rw [MvPowerSeries.coeff_map]
      fin_cases i
      · simp [F.lin_coeff_X]
      · simp [F.lin_coeff_Y]
    refine eq_formal_group_hom (g := PowerSeries.map φ g) (V := PowerSeries.map φ V)
      (ϖ := φ ((u : 𝒪[K]) * π)) hϖ.ne_zero hϖ.not_isUnit (gA.map φ).2 ?_ (VA.map φ).2 ?_ hth0
      (mapc0 _ hFf0) (mapc0 _ hFg0) (mapc1 _) (mapc1 _) (congrArg Subtype.val key) ?_ ?_
    · rw [PowerSeries.coeff_map, hg.2.1]
    · rw [PowerSeries.coeff_map, hV1]
    · exact map_end_add φ hFf0 hV0 (lubinTateEnd H hf ((u : 𝒪[K]) * π)).map_add
    · exact map_end_add φ hFg0 hg.1 (lubinTateEndo H' hg).map_add
  · -- property (d)
    intro a
    obtain ⟨hA0, hA1', hAspec⟩ := lubinTateSeriesHom_spec H hf hf a
    obtain ⟨hB0, hB1', hBspec⟩ := lubinTateSeriesHom_spec H' hg hg a
    have hϖ : Irreducible (φ ((u : 𝒪[K]) * π)) := hB.irreducible _ hirr
    let AaA : CS 𝒪[K] := ⟨lubinTateSeriesHom H hf hf a, hA0⟩
    let AbA : CS 𝒪[K] := ⟨lubinTateSeriesHom H' hg hg a, hB0⟩
    have hcomm : VA * AaA = AaA * VA := by
      refine Subtype.ext ?_
      have e1 := lubinTateSeriesHom_mul H hf hf hf ((u : 𝒪[K]) * π) a
      have e2 := lubinTateSeriesHom_mul H hf hf hf a ((u : 𝒪[K]) * π)
      rw [mul_comm a] at e2
      exact e1.symm.trans e2
    have hgA : gA * AbA = AbA * gA := Subtype.ext hBspec
    have hcomm' : VA.map φ * AaA.map φ = AaA.map φ * VA.map φ := by
      rw [← map_mul, ← map_mul, hcomm]
    have hgA' : gA.map φ * AbA.map φ = AbA.map φ * gA.map φ := by
      rw [← map_mul, ← map_mul, hgA]
    clear_value thC
    have hP : gA.map φ * (thC * AaA.map φ) = (thC * AaA.map φ) * VA.map φ := by
      calc gA.map φ * (thC * AaA.map φ) = (gA.map φ * thC) * AaA.map φ := (mul_assoc _ _ _).symm
        _ = (thC * VA.map φ) * AaA.map φ := by rw [key]
        _ = thC * (VA.map φ * AaA.map φ) := mul_assoc _ _ _
        _ = thC * (AaA.map φ * VA.map φ) := by rw [hcomm']
        _ = (thC * AaA.map φ) * VA.map φ := (mul_assoc _ _ _).symm
    have hQ : gA.map φ * (AbA.map φ * thC) = (AbA.map φ * thC) * VA.map φ := by
      calc gA.map φ * (AbA.map φ * thC) = (gA.map φ * AbA.map φ) * thC := (mul_assoc _ _ _).symm
        _ = (AbA.map φ * gA.map φ) * thC := by rw [hgA']
        _ = AbA.map φ * (gA.map φ * thC) := mul_assoc _ _ _
        _ = AbA.map φ * (thC * VA.map φ) := by rw [key]
        _ = (AbA.map φ * thC) * VA.map φ := (mul_assoc _ _ _).symm
    have hlin : CS.c1 (thC * AaA.map φ) = CS.c1 (AbA.map φ * thC) := by
      rw [CS.c1_mul, CS.c1_mul, CS.c1_map, CS.c1_map]
      show PowerSeries.coeff 1 thC.1 * φ (PowerSeries.coeff 1 (lubinTateSeriesHom H hf hf a)) =
        φ (PowerSeries.coeff 1 (lubinTateSeriesHom H' hg hg a)) * PowerSeries.coeff 1 thC.1
      rw [hA1', hB1', mul_comm]
    exact eq_of_comm_unit hϖ.ne_zero hϖ.not_isUnit (gA.map φ).2
      (by show PowerSeries.coeff 1 (PowerSeries.map φ g) = _; rw [PowerSeries.coeff_map, hg.2.1])
      (VA.map φ).2 (by show PowerSeries.coeff 1 (PowerSeries.map φ V) = _; rw [PowerSeries.coeff_map, hV1])
      (thC * AaA.map φ).2 (AbA.map φ * thC).2 hlin
      (congrArg Subtype.val hP) (congrArg Subtype.val hQ)

end Main

section Headline

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **Proposition 3.10, construction of θ** (Milne, *CFT*, I): proof of the named statement
`LubinTateThetaConstruction`. -/
@[kb "milne2020cft" "Ch. I, Prop. 3.10, construction of θ (proved)"]
theorem lubinTateThetaConstruction : LubinTateThetaConstruction K where
  construct _ _ _ _ _ _ hB _ hπ u _ _ hf hg ε hε := theta_construct hB hπ u hf hg ε hε

/-- **Proposition 3.10** (Milne, *CFT*, I): over the completion of the maximal unramified extension, the Lubin–Tate
formal group laws for `π` and `uπ` are isomorphic, with the isomorphism `θ` satisfying properties (a) to (d). -/
@[kb "milne2020cft" "Ch. I, Proposition 3.10"]
theorem lubinTateIsoOverCompletion (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : LubinTateIsoOverCompletion K :=
  lubinTateIsoOverCompletion_of_theta K lubinTateThetaConstruction

end Headline

end NumberFieldKB.MilneCFT.LocalCFT
