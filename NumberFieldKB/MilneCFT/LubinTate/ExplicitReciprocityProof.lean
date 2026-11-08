import NumberFieldKB.MilneCFT.LubinTate.ExplicitReciprocityCore
import NumberFieldKB.MilneCFT.LubinTate.CompletedUnramified.Concrete
import NumberFieldKB.MilneCFT.LubinTate.SameLevelContainment
import NumberFieldKB.MilneCFT.LubinTate.ArtinIndependenceProof
import NumberFieldKB.MilneCFT.LocalCFT.UnramifiedTauCeti

/-!
# The explicit reciprocity law for Lubin–Tate extensions, and Theorem 3.9 (Milne, *Class Field Theory*, Chapter I)

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, Chapter I,
§3 (Theorem 3.9 and its proof, with Proposition 3.10 and Lemma 3.11).

**`lubinTateExplicitReciprocity`**: the local Artin map of Theorem 1.1 sends a unit `u` to the automorphism acting on
the torsion points `Λ_n` of the Lubin–Tate formal group of `f = πT + T^q` as `[u⁻¹]_f`. Proof (Milne's argument,
carried out at a finite level): let `ϖ = uπ` and `N = n`; by local class field theory
`K_{ϖ,N} ⊆ M = K_{π,N} K_m` for an unramified `K_m` (`exists_ltField_le_ltField_sup_unramified`). Let
`σ̃ = φ_M(ϖ)`: it fixes `K_{ϖ,N}` (`ϖ` is a norm from it), is the Frobenius on `K_m`, and acts on `Λ_{f,N}` as some
`[w]_f`. Over the completion `B` of the integers of `K^un` (`CompletedUnramified.Concrete`), the isomorphism `θ` of
Proposition 3.10 gives `explicit_core`: `σ̃` acts on `Λ_{g,N}` as `[uw]_g`. Since it fixes `Λ_{g,N}`,
`uw ≡ 1 (mod π^N)`; and `φ_M(u) = φ_M(ϖ) φ_M(π)^{-1}` with `φ_M(π)` trivial on `K_{π,N}`, so `φ_M(u)` acts as
`[w]_f = [u^{-1}]_f`.

**`lubinTateArtinIndependence`** (Theorem 3.9) then follows from `lubinTateArtinIndependence_of`.
-/

open scoped ValuativeRel
open Polynomial

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- On an unramified extension, `φ(ϖ)` is the Frobenius of `K^un` (Tau Ceti), for every prime element `ϖ`. -/
theorem tauCetiArtin_unrExt_apply [IsSepClosed Ω] {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {m : ℕ} (hm : m ≠ 0)
    (x : TauCeti.unramifiedExtension K Ω m) :
    ((tauCetiArtin (unrExt m hm) (primeUnit hϖ) x : TauCeti.unramifiedExtension K Ω m) : Ω) =
      ((TauCeti.maximalUnramifiedFrobenius K Ω
        ⟨x, TauCeti.unramifiedExtension_le_maximalUnramifiedExtension K Ω m x.2⟩ :
          TauCeti.maximalUnramifiedExtension K Ω) : Ω) := by
  let E := TauCeti.unramifiedExtension K Ω m
  let _ : ValuativeRel E := TauCeti.finiteIntermediateFieldValuativeRel K Ω E
  let _ : TopologicalSpace E := TauCeti.finiteIntermediateFieldTopology K Ω E
  have : ValuativeExtension K E := TauCeti.finiteIntermediateField_valuativeExtension K Ω E
  have : IsNonarchimedeanLocalField E := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω E
  have hU : TauCeti.IsUnramified K E := TauCeti.isUnramified_unramifiedExtension hm
  have hfrob := eq_frobeniusAlgEquiv_of_isFrobenius E (tauCetiArtin (unrExt m hm) (primeUnit hϖ))
    (isFrobenius_tauCetiArtin hϖ (unrExt m hm) (isUnramifiedExt_unrExt m hm))
  rw [TauCeti.coe_maximalUnramifiedFrobenius_apply_of_mem x.2]
  exact congrArg (fun σ : Gal(E/K) => ((σ x : E) : Ω)) hfrob

/-- Points of `Λ_n` are mapped into `Λ_n` by `K`-automorphisms. -/
theorem algEquiv_mem_ltTorsion {M : IntermediateField K Ω} (σ : M ≃ₐ[K] M) {π : 𝒪[K]} {n : ℕ} (x : M)
    (hx : (x : Ω) ∈ ltTorsion Ω π n) : ((σ x : M) : Ω) ∈ ltTorsion Ω π n := by
  rw [ltTorsion, mem_rootSet] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have h0 : aeval x ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) = 0 := aeval_intermediate_eq_zero x hx.2
  have h1 : aeval (σ x) ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) = 0 := by
    rw [show aeval (σ x) ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) =
      σ (aeval x ((ltPolyIter π n).map (algebraMap 𝒪[K] K))) from aeval_algHom_apply σ.toAlgHom x _, h0,
      map_zero]
  exact (aeval_algHom_apply M.val (σ x) _).trans (by rw [h1, map_zero])

/-- **The explicit reciprocity law at level `n + 1`** for the Tau Ceti local Artin map, on
`M = K_{π,n+1} K_m`. -/
theorem tauCetiArtin_unit_ltTorsion {π : 𝒪[K]} (hπ : Irreducible π) (u : 𝒪[K]ˣ) (n : ℕ) :
    ∃ Mx : FiniteAbelianExt K Ω, ∃ hM : ltField Ω π (n + 1) ≤ Mx.toField,
      ∀ (α : Ω) (hα : α ∈ ltTorsion Ω π (n + 1)),
        ((tauCetiArtin Mx (unitToK u) ⟨α, hM (mem_ltField hα)⟩ : Mx.toField) : Ω) =
          ltAct hπ (n + 1) ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) α := by
  classical
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hϖ : Irreducible ((u : 𝒪[K]) * π) := (irreducible_units_mul u).2 hπ
  set ϖ : 𝒪[K] := (u : 𝒪[K]) * π with hϖdef
  obtain ⟨m, hm, hle⟩ := exists_ltField_le_ltField_sup_unramified (Ω := Ω) hπ hϖ (n + 1) (by omega)
  set LT := ltFieldExt (lubinTateExtensionTheorem K Ω) hπ (n := n + 1) (by omega) with hLT
  set Mx := LT.sup (unrExt m hm) with hMx
  have hfM : ltField Ω π (n + 1) ≤ Mx.toField := le_sup_left
  have hKmM : TauCeti.unramifiedExtension K Ω m ≤ Mx.toField := le_sup_right
  refine ⟨Mx, hfM, ?_⟩
  set σM := tauCetiArtin Mx (primeUnit hϖ) with hσM
  /- `σ̃ = φ_M(ϖ)` acts on `Λ_{f,n+1}` as some `[w]_f`. -/
  set lam : Ω := x0 Ω hπ n with hlam
  have hlamT : lam ∈ ltTorsion Ω π (n + 1) := x0_mem Ω hπ n
  obtain ⟨w, hw0⟩ := exists_ltAct_x0 Ω hπ n _
    (algEquiv_mem_ltTorsion σM ⟨lam, hfM (mem_ltField hlamT)⟩ hlamT)
  have hw : ∀ (α : Ω) (hα : α ∈ ltTorsion Ω π (n + 1)),
      ((σM ⟨α, hfM (mem_ltField hα)⟩ : Mx.toField) : Ω) = ltAct hπ (n + 1) w α := by
    intro α hα
    obtain ⟨a, rfl⟩ := exists_ltAct_x0 Ω hπ n α hα
    have h2 : ltAct hπ (n + 1) a ((σM ⟨lam, hfM (mem_ltField hlamT)⟩ : Mx.toField) : Ω) ∈ Mx.toField := by
      rw [hw0, ltAct_ltAct_x0 Ω hπ n]
      exact hfM (mem_ltField (ltAct_x0_mem Ω hπ n _))
    rw [algEquiv_ltAct σM hπ (n + 1) a ⟨lam, hfM (mem_ltField hlamT)⟩ _ h2]
    show ltAct hπ (n + 1) a ((σM ⟨lam, hfM (mem_ltField hlamT)⟩ : Mx.toField) : Ω) = _
    rw [hw0, ltAct_ltAct_x0 Ω hπ n, ltAct_ltAct_x0 Ω hπ n, mul_comm]
  /- The core, with `B` the completed integers of `K^un`. -/
  set Km := TauCeti.unramifiedExtension K Ω m with hKm
  have hKmun : Km ≤ TauCeti.maximalUnramifiedExtension K Ω :=
    TauCeti.unramifiedExtension_le_maximalUnramifiedExtension K Ω m
  let j : Km →ₐ[K] CompletedUnramified.Fun K Ω :=
    (CompletedUnramified.jun K Ω).comp (IntermediateField.inclusion hKmun)
  let σKm : Km →ₐ[K] Km := (tauCetiArtin (unrExt m hm) (primeUnit hϖ)).toAlgHom
  haveI : Normal K (unrExt (K := K) (Ω := Ω) m hm).toField :=
    (unrExt (K := K) (Ω := Ω) m hm).isAbelianGalois.toIsGalois.to_normal
  have h1 : ∀ x : Km, ((σM ⟨x, hKmM x.2⟩ : Mx.toField) : Ω) = σKm x := by
    intro x
    have := galRestrict_apply (L := (unrExt m hm).toField) hKmM σM x
    rw [hσM, galRestrict_tauCetiArtin (unrExt m hm) Mx hKmM] at this
    exact this.symm
  have h2 : ∀ x : Km, j (σKm x) = CompletedUnramified.frobFun K Ω (j x) := by
    intro x
    show CompletedUnramified.jun K Ω (IntermediateField.inclusion hKmun (σKm x)) =
      CompletedUnramified.frobFun K Ω (CompletedUnramified.jun K Ω (IntermediateField.inclusion hKmun x))
    rw [← CompletedUnramified.jun_frob]
    congr 1
    exact Subtype.ext (tauCetiArtin_unrExt_apply hϖ hm x)
  haveI : Normal K Km := (unrExt (K := K) (Ω := Ω) m hm).isAbelianGalois.toIsGalois.to_normal
  haveI : Normal K Mx.toField := Mx.isAbelianGalois.toIsGalois.to_normal
  have hcore := explicit_core (CompletedUnramified.isCompletedUnramifiedInt K Ω)
    (CompletedUnramified.algebraKFun_apply K Ω) (CompletedUnramified.frobFun K Ω)
    (CompletedUnramified.frobFun_algebraMap K Ω) (CompletedUnramified.frobFun_algebraMap_K K Ω)
    hπ u n Km j Mx.toField hfM hKmM le_rfl σM σKm h1 h2 w hw hle
  /- `σ̃` fixes `Λ_{g,n+1}`, so `uw ≡ 1`. -/
  have hfix := tauCetiArtin_primeUnit_apply hϖ (n + 1) Mx hle
    ⟨x0 Ω hϖ n, hle (mem_ltField (x0_mem Ω hϖ n))⟩ (mem_ltField (x0_mem Ω hϖ n))
  have hc := hcore (x0 Ω hϖ n) (x0_mem Ω hϖ n)
  rw [hfix] at hc
  have huw : (u : 𝒪[K]) * w - 1 ∈ Ideal.span {π ^ (n + 1)} := by
    have h := (ltAct_x0_eq_iff Ω hϖ n ((u : 𝒪[K]) * w) 1).1 (by rw [ltAct_one_x0 Ω hϖ n]; exact hc.symm)
    rw [Ideal.mem_span_singleton] at h ⊢
    rw [hϖdef, mul_pow] at h
    exact (Units.isUnit (u ^ (n + 1))).dvd_mul_left.1 (by simpa using h)
  /- `φ(u) = φ(ϖ) φ(π)⁻¹` acts as `[w]_f = [u⁻¹]_f`. -/
  intro α hα
  have hpu : unitToK u = primeUnit hϖ * (primeUnit hπ)⁻¹ := by
    apply Units.ext
    simp [unitToK, primeUnit, hϖdef]
    rfl
  have hπfix := tauCetiArtin_primeUnit_apply hπ (n + 1) Mx hfM ⟨α, hfM (mem_ltField hα)⟩ (mem_ltField hα)
  have hπinv : (tauCetiArtin Mx (primeUnit hπ))⁻¹ ⟨α, hfM (mem_ltField hα)⟩ = ⟨α, hfM (mem_ltField hα)⟩ := by
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    exact hπfix.symm
  rw [hpu, map_mul, map_inv, AlgEquiv.mul_apply, hπinv, hw α hα]
  obtain ⟨a, rfl⟩ := exists_ltAct_x0 Ω hπ n α hα
  rw [ltAct_ltAct_x0 Ω hπ n, ltAct_ltAct_x0 Ω hπ n]
  refine (ltAct_x0_eq_iff Ω hπ n _ _).2 ?_
  have : w * a - ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * a =
      ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * a * ((u : 𝒪[K]) * w - 1) := by
    have hu1 : ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * (u : 𝒪[K]) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    linear_combination (-(w * a)) * hu1
  rw [this]
  exact Ideal.mul_mem_left _ _ huw

variable (K Ω) in
/-- **The explicit reciprocity law, proved** (Milne, *CFT*, I, §3, Theorem 3.9 with Theorem 1.1): every local Artin
map sends a unit `u` to an automorphism acting on `Λ_n` as `[u⁻¹]_f`. -/
@[kb "milne2020cft" "Ch. I, §3, Theorem 3.9 (explicit reciprocity law)"]
theorem lubinTateExplicitReciprocity : LubinTateExplicitReciprocity K Ω where
  torsion φ hφ π hπ n L hL u α hα := by
    have hφeq : φ = fun L => tauCetiArtin L :=
      isLocalArtinMap_unique_unconditional Ω hφ isLocalArtinMap_tauCeti_family
    subst hφeq
    rcases n with _ | n
    · have hα0 : α = 0 := by
        rw [ltTorsion, mem_rootSet] at hα
        simpa [ltPolyIter] using hα.2
      subst hα0
      rw [ltAct_zero_level]
      have : (⟨0, hL (mem_ltField hα)⟩ : L.toField) = 0 := rfl
      rw [this, map_zero]
      rfl
    · obtain ⟨Mx, hM, hMx⟩ := tauCetiArtin_unit_ltTorsion (Ω := Ω) hπ u n
      set L' := L.sup Mx
      have hLL' : L.toField ≤ L'.toField := le_sup_left
      have hML' : Mx.toField ≤ L'.toField := le_sup_right
      have e1 := galRestrict_apply hLL' (tauCetiArtin L' (unitToK u)) ⟨α, hL (mem_ltField hα)⟩
      have e2 := galRestrict_apply hML' (tauCetiArtin L' (unitToK u)) ⟨α, hM (mem_ltField hα)⟩
      rw [galRestrict_tauCetiArtin] at e1 e2
      show ((tauCetiArtin L (unitToK u) ⟨α, _⟩ : L.toField) : Ω) = _
      rw [e1, ← hMx α hα, e2]
      rfl

variable (K Ω) in
/-- **Theorem 3.9, proved** (Milne, *CFT*, I, Theorem 3.9): `K_π K^un` and `φ_π` do not depend on the prime
element `π`. -/
@[kb "milne2020cft" "Ch. I, Theorem 3.9"]
theorem lubinTateArtinIndependence : LubinTateArtinIndependence K Ω :=
  lubinTateArtinIndependence_of K Ω (lubinTateExplicitReciprocity K Ω)

end NumberFieldKB.MilneCFT.LocalCFT
