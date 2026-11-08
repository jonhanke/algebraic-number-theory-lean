import NumberFieldKB.MilneCFT.LubinTate.ExplicitReciprocityEval

/-!
# The core of the explicit reciprocity law (Milne, *Class Field Theory*, Chapter I, proof of Theorem 3.9)

Let `f = πT + T^q` and `g = ϖT + T^q` with `ϖ = uπ`, `N = n + 1`. Let `B` be a ring with
`IsCompletedUnramifiedInt K B σ` (for instance the completion of the integers of `K^un`), `F` its field of
fractions, with an automorphism `σF` extending `σ`, and `K_m ⊆ Ω` a finite normal extension with a `K`-embedding
`j : K_m → F`. Let `M ⊆ Ω` be a finite normal extension with `K_{π,N}, K_m ⊆ M ⊆ K_{π,N} K_m` and `K_{ϖ,N} ⊆ M`,
and let `σ̃ ∈ Gal(M/K)` act on `K_m` compatibly with `σF` (through `j`) and on `Λ_{f,N}` as `[w]_f`.

**Theorem** (`explicit_core`): `σ̃` acts on `Λ_{g,N}` as `[uw]_g`.

Proof (Milne's argument, at finite level). Let `E = F[X]/(Q_n)` (`Q_n` is Eisenstein, so irreducible over `F`;
`LevelPolynomial.lean`). Embed `M` into `E` by a `K`-embedding `ι` which is `j` on `K_m` and sends the primitive
torsion point `λ` to the root of `Q_n`; extend `σF` to `τ : E → E` by `τ(root) = ι(σ̃ λ)`, so `τ ∘ ι = ι ∘ σ̃`.
With `θ` from Proposition 3.10 (`lubinTateIsoOverCompletion`), evaluated algebraically at torsion points
(`PowerSeriesEvalAlg.lean`): `θ(ι λ)` is a primitive root `ι μ₀` of `g^{(N)}`, and
`τ(θ(ιλ)) = θ^σ(τ ιλ) = θ([u]_f [w]_f ιλ) = θ([uw]_f ιλ) = [uw]_g θ(ιλ)`, so `σ̃ μ₀ = [uw]_g μ₀`; `μ₀` generates
`Λ_{g,N}`.
-/

open scoped ValuativeRel
open Polynomial NumberFieldKB.MilneCFT.PowerSeriesEval

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- The power series `[a]_f` for `f = πT + T^q`. -/
abbrev ltSer {π : 𝒪[K]} (hπ : Irreducible π) (a : 𝒪[K]) : PowerSeries 𝒪[K] :=
  (lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) (ltPoly_mem hπ) a).toPowerSeries

theorem constantCoeff_map_ltSer {B : Type} [CommRing B] [Algebra 𝒪[K] B] {π : 𝒪[K]} (hπ : Irreducible π)
    (a : 𝒪[K]) : PowerSeries.constantCoeff (PowerSeries.map (algebraMap 𝒪[K] B) (ltSer hπ a)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, FormalGroupHom.constantCoeff_eq_zero, map_zero]

theorem aeval_intermediate_eq_zero {M : IntermediateField K Ω} (z : M) {p : K[X]}
    (h : aeval (z : Ω) p = 0) : aeval z p = 0 :=
  Subtype.ext ((aeval_algHom_apply M.val z p).symm.trans h)

/-- A `K`-automorphism of an intermediate field commutes with `[a]_f`. -/
theorem algEquiv_ltAct {M : IntermediateField K Ω} (σM : M ≃ₐ[K] M) {π : 𝒪[K]} (hπ : Irreducible π) (N : ℕ)
    (a : 𝒪[K]) (x : M) (h1 : ltAct hπ N a (x : Ω) ∈ M) (h2 : ltAct hπ N a ((σM x : M) : Ω) ∈ M) :
    σM ⟨ltAct hπ N a (x : Ω), h1⟩ = ⟨ltAct hπ N a ((σM x : M) : Ω), h2⟩ := by
  set r := ((lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) (ltPoly_mem hπ) a).toPowerSeries %ʷ
    ((ltPolyIter π N : 𝒪[K][X]) : PowerSeries 𝒪[K])).map (algebraMap 𝒪[K] K)
  have e : ∀ (y : M) (hy : ltAct hπ N a (y : Ω) ∈ M), (⟨ltAct hπ N a (y : Ω), hy⟩ : M) = aeval y r := by
    intro y hy
    apply Subtype.ext
    show aeval (y : Ω) r = _
    exact aeval_algHom_apply M.val y r
  rw [e x h1, e _ h2]
  exact (aeval_algHom_apply σM.toAlgHom x r).symm

section Core

variable {B : Type} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
variable {F : Type} [Field F] [Algebra B F] [IsFractionRing B F] [Algebra K F]

/-- **Core of the explicit reciprocity law** (see the module docstring). -/
theorem explicit_core {σ : B ≃+* B} (hB : IsCompletedUnramifiedInt K B σ)
    (hKF : ∀ a : 𝒪[K], algebraMap K F a = algebraMap B F (algebraMap 𝒪[K] B a))
    (σF : F ≃+* F) (hσF : ∀ b : B, σF (algebraMap B F b) = algebraMap B F (σ b))
    (hσFK : ∀ c : K, σF (algebraMap K F c) = algebraMap K F c)
    {π : 𝒪[K]} (hπ : Irreducible π) (u : 𝒪[K]ˣ) (n : ℕ)
    (Km : IntermediateField K Ω) [Normal K Km] (j : Km →ₐ[K] F)
    (M : IntermediateField K Ω) [Normal K M] (hfM : ltField Ω π (n + 1) ≤ M) (hKmM : Km ≤ M)
    (hMle : M ≤ ltField Ω π (n + 1) ⊔ Km)
    (σM : M ≃ₐ[K] M) (σKm : Km →ₐ[K] Km)
    (h1 : ∀ x : Km, ((σM ⟨x, hKmM x.2⟩ : M) : Ω) = σKm x)
    (h2 : ∀ x : Km, j (σKm x) = σF (j x))
    (w : 𝒪[K])
    (hw : ∀ (α : Ω) (hα : α ∈ ltTorsion Ω π (n + 1)),
      ((σM ⟨α, hfM (mem_ltField hα)⟩ : M) : Ω) = ltAct hπ (n + 1) w α)
    (hgM : ltField Ω ((u : 𝒪[K]) * π) (n + 1) ≤ M) (μ : Ω)
    (hμ : μ ∈ ltTorsion Ω ((u : 𝒪[K]) * π) (n + 1)) :
    ((σM ⟨μ, hgM (mem_ltField hμ)⟩ : M) : Ω) =
      ltAct ((irreducible_units_mul u).2 hπ) (n + 1) ((u : 𝒪[K]) * w) μ := by
  classical
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal B) B := hB.complete
  have hϖ : Irreducible ((u : 𝒪[K]) * π) := (irreducible_units_mul u).2 hπ
  set ϖ : 𝒪[K] := (u : 𝒪[K]) * π with hϖdef
  have halg : Algebra.IsAlgebraic K Ω := by
    have : Algebra.IsSeparable K Ω := IsSepClosure.separable
    exact Algebra.IsSeparable.isAlgebraic K Ω
  /- The field `E = F[X]/(Q_n)`. -/
  set Qf : F[X] := (ltPrim π n).map ((algebraMap B F).comp (algebraMap 𝒪[K] B)) with hQf
  haveI hQirr : Fact (Irreducible Qf) := ⟨ltPrim_map_irreducible hπ (hB.irreducible π hπ) n⟩
  let E := AdjoinRoot Qf
  have hKE : ∀ a : 𝒪[K], algebraMap K E a = algebraMap B E (algebraMap 𝒪[K] B a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply K F E, hKF, ← IsScalarTower.algebraMap_apply B F E]
  set Q : K[X] := (ltPrim π n).map (algebraMap 𝒪[K] K) with hQ
  have hQE : ∀ y : E, aeval y Q = aeval y Qf := by
    intro y
    rw [aeval_def, aeval_def]
    show eval₂ (algebraMap K E) y ((ltPrim π n).map (algebraMap 𝒪[K] K)) =
      eval₂ (algebraMap F E) y ((ltPrim π n).map ((algebraMap B F).comp (algebraMap 𝒪[K] B)))
    rw [eval₂_map, eval₂_map]
    congr 1
    refine RingHom.ext fun a => ?_
    show algebraMap K E (a : K) = algebraMap F E (algebraMap B F (algebraMap 𝒪[K] B a))
    rw [hKE, IsScalarTower.algebraMap_apply B F E]
  set r : E := AdjoinRoot.root Qf with hrdef
  have hr : aeval r Qf = 0 := by rw [hrdef, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  /- The primitive torsion point `λ`. -/
  set lam : Ω := x0 Ω hπ n with hlam
  have hlamT : lam ∈ ltTorsion Ω π (n + 1) := x0_mem Ω hπ n
  have hlamQ : aeval lam Q = 0 := aeval_x0_ltPrim Ω hπ n
  have hminpoly : minpoly K lam = Q := minpoly_x0_eq_ltPrim Ω hπ n
  have hlamM : lam ∈ M := hfM (mem_ltField hlamT)
  set lamM : M := ⟨lam, hlamM⟩ with hlamMdef
  /- `Q` splits in `E`. -/
  have hLf : ltField Ω π (n + 1) = IntermediateField.adjoin K {lam} := ltField_eq_adjoin Ω hπ n
  have hint : IsIntegral K lam := Algebra.IsIntegral.isIntegral lam
  have hrQ : r ∈ (minpoly K lam).aroots E := by
    rw [mem_aroots, hminpoly]
    refine ⟨?_, by rw [hQE]; exact hr⟩
    exact (ltPrim_map_irreducible_K hπ n).ne_zero
  let ι₀ : IntermediateField.adjoin K {lam} →ₐ[K] E :=
    (IntermediateField.algHomAdjoinIntegralEquiv K hint).symm ⟨r, hrQ⟩
  haveI : IsGalois K (ltField Ω π (n + 1)) := isGalois_ltField Ω hπ n
  have hQsplit : (Q.map (algebraMap K E)).Splits := by
    have hl : lam ∈ ltField Ω π (n + 1) := mem_ltField hlamT
    have hs := Normal.splits (F := K) (K := ltField Ω π (n + 1)) IsGalois.to_normal ⟨lam, hl⟩
    rw [IntermediateField.minpoly_eq, hminpoly] at hs
    have hs' := hs.map ((ι₀.comp (IntermediateField.equivOfEq hLf).toAlgHom) : _ →+* E)
    rwa [Polynomial.map_map, AlgHom.comp_algebraMap] at hs'
  /- The embedding `ι₁ : M → E` extending `j`. -/
  set S : Set Ω := (Km : Set Ω) ∪ {lam} with hS
  have hMadj : M = IntermediateField.adjoin K S := by
    apply le_antisymm
    · refine hMle.trans (sup_le ?_ ?_)
      · rw [hLf]
        exact IntermediateField.adjoin.mono K _ _ (Set.subset_union_right)
      · intro x hx
        exact IntermediateField.subset_adjoin K S (Or.inl hx)
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (hx | hx)
      · exact hKmM hx
      · rw [Set.mem_singleton_iff.1 hx]; exact hlamM
  have hKmS : Km ≤ IntermediateField.adjoin K S := fun x hx =>
    IntermediateField.subset_adjoin K S (Or.inl hx)
  have hsplitS : ∀ s ∈ S, IsIntegral K s ∧ ((minpoly K s).map (algebraMap K E)).Splits := by
    rintro s (hs | hs)
    · refine ⟨Algebra.IsIntegral.isIntegral s, ?_⟩
      have h := Normal.splits (F := K) (K := Km) inferInstance ⟨s, hs⟩
      rw [IntermediateField.minpoly_eq] at h
      have h' := h.map (((IsScalarTower.toAlgHom K F E).comp j : Km →ₐ[K] E) : Km →+* E)
      rwa [Polynomial.map_map, AlgHom.comp_algebraMap] at h'
    · rw [Set.mem_singleton_iff.1 hs]
      exact ⟨hint, by rw [hminpoly]; exact hQsplit⟩
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_adjoin_of_splits hsplitS
    ((IsScalarTower.toAlgHom K F E).comp j) hKmS
  let ι₁ : M →ₐ[K] E := φ.comp (IntermediateField.equivOfEq hMadj).toAlgHom
  have hι₁Km : ∀ x : Km, ι₁ ⟨x, hKmM x.2⟩ = algebraMap F E (j x) := by
    intro x
    have := AlgHom.congr_fun hφ x
    exact this
  /- Move `ι₁ λ` to the root by an automorphism `ρ` of `E` over `F`. -/
  set y1 : E := ι₁ lamM with hy1def
  have hy1 : aeval y1 Qf = 0 := by
    rw [← hQE, hy1def, aeval_algHom_apply]
    have : aeval lamM Q = 0 := by
      apply Subtype.ext
      refine (aeval_algHom_apply M.val lamM Q).symm.trans ?_
      exact hlamQ
    rw [this, map_zero]
  haveI : Module.Finite F E := (AdjoinRoot.powerBasis hQirr.out.ne_zero).finite
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  let ρ : E ≃ₐ[F] E := AlgEquiv.ofBijective (AdjoinRoot.liftAlgHom Qf (Algebra.ofId F E) y1 hy1)
    (Algebra.IsAlgebraic.algHom_bijective _)
  have hρr : ρ r = y1 := AdjoinRoot.liftAlgHom_root Qf (Algebra.ofId F E) y1 hy1
  let ι : M →ₐ[K] E := ((ρ.symm.restrictScalars K : E ≃ₐ[K] E) : E →ₐ[K] E).comp ι₁
  have hιlam : ι lamM = r := by
    show ρ.symm (ι₁ lamM) = r
    rw [← hy1def, ← hρr, AlgEquiv.symm_apply_apply]
  have hιKm : ∀ x : Km, ι ⟨x, hKmM x.2⟩ = algebraMap F E (j x) := by
    intro x
    show ρ.symm (ι₁ ⟨x, hKmM x.2⟩) = _
    rw [hι₁Km, AlgEquiv.commutes]
  have hι_inj : Function.Injective ι := ι.toRingHom.injective
  have hlamMQ : aeval lamM Q = 0 := aeval_intermediate_eq_zero lamM hlamQ
  /- `τ : E → E` extending `σF`, with `τ ∘ ι = ι ∘ σ̃`. -/
  have hσfix : ∀ a : 𝒪[K],
      σF (algebraMap B F (algebraMap 𝒪[K] B a)) = algebraMap B F (algebraMap 𝒪[K] B a) := by
    intro a; rw [hσF, hB.frob_fix]
  have hτ0 : Qf.eval₂ ((algebraMap F E).comp σF.toRingHom) (ι (σM lamM)) = 0 := by
    have e1 : Qf.eval₂ ((algebraMap F E).comp σF.toRingHom) (ι (σM lamM)) = aeval (ι (σM lamM)) Qf := by
      rw [aeval_def]
      show eval₂ _ _ ((ltPrim π n).map ((algebraMap B F).comp (algebraMap 𝒪[K] B))) =
        eval₂ (algebraMap F E) _ ((ltPrim π n).map ((algebraMap B F).comp (algebraMap 𝒪[K] B)))
      rw [eval₂_map, eval₂_map]
      congr 1
      refine RingHom.ext fun a => ?_
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [hσfix]
    rw [e1, ← hQE, aeval_algHom_apply, show aeval (σM lamM) Q = σM (aeval lamM Q) from
      aeval_algHom_apply σM.toAlgHom lamM Q, hlamMQ, map_zero, map_zero]
  let τ : E →+* E := AdjoinRoot.lift ((algebraMap F E).comp σF.toRingHom) (ι (σM lamM)) hτ0
  have hτF : ∀ c : F, τ (algebraMap F E c) = algebraMap F E (σF c) := by
    intro c
    show AdjoinRoot.lift _ _ hτ0 (AdjoinRoot.of Qf c) = _
    exact AdjoinRoot.lift_of hτ0
  have hτB : ∀ b : B, τ (algebraMap B E b) = algebraMap B E (σ b) := by
    intro b
    rw [IsScalarTower.algebraMap_apply B F E, hτF, hσF, ← IsScalarTower.algebraMap_apply B F E]
  have hτr : τ r = ι (σM lamM) := AdjoinRoot.lift_root hτ0
  let τK : E →ₐ[K] E :=
    { τ with
      commutes' := fun c => by
        show τ (algebraMap K E c) = algebraMap K E c
        rw [IsScalarTower.algebraMap_apply K F E, hτF, hσFK] }
  have hτι : ∀ x : M, τ (ι x) = ι (σM x) := by
    have hcomp : τK.comp ι = ι.comp σM.toAlgHom := by
      refine IntermediateField.algHom_ext_of_eq_adjoin K hMadj ?_
      rintro x (hx | hx)
      · show τ (ι ⟨x, _⟩) = ι (σM ⟨x, _⟩)
        have e2 : (σM ⟨x, hMadj.ge (IntermediateField.subset_adjoin K S (Or.inl hx))⟩ : M) =
            ⟨σKm ⟨x, hx⟩, hKmM (σKm ⟨x, hx⟩).2⟩ := Subtype.ext (h1 ⟨x, hx⟩)
        rw [e2, hιKm, show (⟨x, hMadj.ge (IntermediateField.subset_adjoin K S (Or.inl hx))⟩ : M) =
          ⟨((⟨x, hx⟩ : Km) : Ω), hKmM hx⟩ from rfl, hιKm, hτF, h2]
      · have hx' : x = lam := Set.mem_singleton_iff.1 hx
        subst hx'
        show τ (ι lamM) = ι (σM lamM)
        rw [hιlam, hτr]
    intro x
    exact AlgHom.congr_fun hcomp x
  /- `θ` from Proposition 3.10. -/
  obtain ⟨ε, θ, -, hθ0, hθ1, hθb, -, hθd⟩ :=
    (lubinTateIsoOverCompletion K).exists_iso B σ hB hπ u (ltPoly_mem hπ) (ltPoly_mem hϖ)
  have hθd' : ∀ a : 𝒪[K], θ.subst (PowerSeries.map (algebraMap 𝒪[K] B) (ltSer hπ a)) =
      (PowerSeries.map (algebraMap 𝒪[K] B) (ltSer hϖ a)).subst θ := fun a => hθd a
  have hθb' : PowerSeries.map (σ : B →+* B) θ =
      θ.subst (PowerSeries.map (algebraMap 𝒪[K] B) (ltSer hπ (u : 𝒪[K]))) := hθb
  have hθs : PowerSeries.HasSubst θ := PowerSeries.HasSubst.of_constantCoeff_zero' hθ0
  /- Torsion points of `M` give distinguished roots in `E`. -/
  have hdistf : ∀ z : M, (z : Ω) ∈ ltTorsion Ω π (n + 1) → IsDistRoot (B := B) (ι z) := fun z hz =>
    isDistRoot_of_aeval hB hKE hπ (N := n + 1)
      (by rw [aeval_algHom_apply, aeval_intermediate_eq_zero z (mem_rootSet.1 hz).2, map_zero])
  have hdistg : ∀ z : M, (z : Ω) ∈ ltTorsion Ω ϖ (n + 1) → IsDistRoot (B := B) (ι z) := fun z hz =>
    isDistRoot_of_aeval hB hKE hϖ (N := n + 1)
      (by rw [aeval_algHom_apply, aeval_intermediate_eq_zero z (mem_rootSet.1 hz).2, map_zero])
  have hTM : ∀ {α : Ω}, α ∈ ltTorsion Ω π (n + 1) → α ∈ M := fun h => hfM (mem_ltField h)
  have hsubst_f : ∀ (z : M) (hz : (z : Ω) ∈ ltTorsion Ω π (n + 1)) (a : 𝒪[K])
      (hza : ltAct hπ (n + 1) a (z : Ω) ∈ ltTorsion Ω π (n + 1)),
      evalHom (hdistf z hz) (θ.subst (PowerSeries.map (algebraMap 𝒪[K] B) (ltSer hπ a))) =
        evalHom (hdistf ⟨_, hTM hza⟩ hza) θ := by
    intro z hz a hza
    have e : evalHom (hdistf z hz) (PowerSeries.map (algebraMap 𝒪[K] B) (ltSer hπ a)) = ι ⟨_, hTM hza⟩ :=
      (algHom_ltAct hKE hπ ι z hz (hdistf z hz) a (hTM hza)).symm
    have h' : IsDistRoot (B := B)
        (evalHom (hdistf z hz) (PowerSeries.map (algebraMap 𝒪[K] B) (ltSer hπ a))) := by
      rw [e]; exact hdistf _ hza
    rw [evalHom_subst (hdistf z hz) (constantCoeff_map_ltSer hπ a) h' θ]
    exact evalHom_congr _ _ e θ
  /- Values of `θ`. -/
  have hθzero : ∀ (t : E) (ht : IsDistRoot (B := B) t), t = 0 → evalHom ht θ = 0 := by
    intro t ht h0
    rw [evalHom_congr ht isDistRoot_zero h0, evalHom_zero_apply, hθ0, map_zero]
  have hθne : ∀ (t : E) (ht : IsDistRoot (B := B) t), t ≠ 0 → evalHom ht θ ≠ 0 := by
    intro t ht h0
    obtain ⟨θ₁, hθ₁c, he⟩ := evalHom_eq_mul ht hθ0
    rw [he]
    refine mul_ne_zero h0 (isUnit_evalHom ht ?_).ne_zero
    rw [hθ₁c, hθ1]; exact ε.isUnit
  set y0 : E := ι lamM with hy0def
  have hy0 : IsDistRoot (B := B) y0 := hdistf lamM hlamT
  have hgk : ∀ k : ℕ, aeval (evalHom hy0 θ) ((ltPolyIter ϖ k).map (algebraMap 𝒪[K] B)) =
      evalHom (hdistf ⟨_, hTM (ltAct_x0_mem Ω hπ n (ϖ ^ k))⟩ (ltAct_x0_mem Ω hπ n (ϖ ^ k))) θ := by
    intro k
    rw [aeval_algHom_apply, ← PowerSeries.subst_coe hθs, Polynomial.polynomial_map_coe,
      ← lubinTateEnd_pow_toPowerSeries hϖ k]
    show evalHom hy0 ((PowerSeries.map (algebraMap 𝒪[K] B) (ltSer hϖ (ϖ ^ k))).subst θ) = _
    rw [← hθd']
    exact hsubst_f lamM hlamT (ϖ ^ k) (ltAct_x0_mem Ω hπ n _)
  have hϖpow : ∀ k : ℕ, ϖ ^ k = (u : 𝒪[K]) ^ k * π ^ k := fun k => by rw [hϖdef, mul_pow]
  have hN0 : ltAct hπ (n + 1) (ϖ ^ (n + 1)) lam = 0 := by
    rw [← ltAct_zero_x0 Ω hπ n]
    refine (ltAct_x0_eq_iff Ω hπ n _ _).2 ?_
    rw [sub_zero, hϖpow, Ideal.mem_span_singleton]
    exact dvd_mul_left _ _
  have hn0 : ltAct hπ (n + 1) (ϖ ^ n) lam ≠ 0 := by
    intro h
    rw [← ltAct_zero_x0 Ω hπ n] at h
    have h' := (ltAct_x0_eq_iff Ω hπ n _ _).1 h
    rw [sub_zero, hϖpow, Ideal.mem_span_singleton, pow_succ, mul_comm ((u : 𝒪[K]) ^ n)] at h'
    have h'' : π ∣ (u : 𝒪[K]) ^ n := (mul_dvd_mul_iff_left (pow_ne_zero n hπ.ne_zero)).1 h'
    exact hπ.not_isUnit (isUnit_of_dvd_unit h'' ((Units.isUnit u).pow n))
  have hθN : aeval (evalHom hy0 θ) ((ltPolyIter ϖ (n + 1)).map (algebraMap 𝒪[K] B)) = 0 := by
    rw [hgk]
    refine hθzero _ _ ?_
    rw [show (⟨_, hTM (ltAct_x0_mem Ω hπ n (ϖ ^ (n + 1)))⟩ : M) = 0 from Subtype.ext hN0, map_zero]
  have hθn : aeval (evalHom hy0 θ) ((ltPolyIter ϖ n).map (algebraMap 𝒪[K] B)) ≠ 0 := by
    rw [hgk]
    refine hθne _ _ ?_
    intro h
    exact hn0 (congrArg Subtype.val (hι_inj (h.trans (map_zero ι).symm)))
  have hθy0 : IsDistRoot (B := B) (evalHom hy0 θ) :=
    ⟨_, isDistinguishedAt_map hB (ltPolyIter_isDistinguishedAt hϖ (n + 1)), hθN⟩
  /- `θ(ι λ) = ι μ₀` with `μ₀` a primitive torsion point for `ϖ`. -/
  set Qg : K[X] := (ltPrim ϖ n).map (algebraMap 𝒪[K] K) with hQg
  have hQgθ : aeval (evalHom hy0 θ) Qg = 0 := by
    have h := hθN
    rw [ltPolyIter_succ_eq_mul_ltPrim hϖ n, Polynomial.map_mul, map_mul] at h
    rw [hQg, aeval_map_K_eq_B hKE]
    exact (mul_eq_zero.1 h).resolve_left hθn
  have hx0g : x0 Ω hϖ n ∈ M := hgM (mem_ltField (x0_mem Ω hϖ n))
  have hQgsplit : (Qg.map (algebraMap K M)).Splits := by
    have hs := Normal.splits (F := K) (K := M) inferInstance ⟨x0 Ω hϖ n, hx0g⟩
    rwa [IntermediateField.minpoly_eq, minpoly_x0_eq_ltPrim Ω hϖ n] at hs
  have hQg0 : Qg.map (algebraMap K M) ≠ 0 :=
    Polynomial.map_ne_zero (ltPrim_map_irreducible_K hϖ n).ne_zero
  obtain ⟨μ0M, hιμ0⟩ := hQgsplit.mem_range_of_isRoot hQg0 (i := (ι : M →+* E)) (x := evalHom hy0 θ) (by
    rw [Polynomial.map_map, show ((ι : M →+* E)).comp (algebraMap K M) = algebraMap K E from
      ι.comp_algebraMap, IsRoot, Polynomial.eval_map_algebraMap]
    exact hQgθ)
  change ι μ0M = evalHom hy0 θ at hιμ0
  set μ0 : Ω := (μ0M : Ω) with hμ0def
  have hμ0Q : aeval μ0 Qg = 0 := by
    have h : aeval μ0M Qg = 0 := by
      apply hι_inj
      rw [map_zero, ← aeval_algHom_apply, hιμ0, hQgθ]
    rw [hμ0def]
    exact (aeval_algHom_apply M.val μ0M Qg).trans (by rw [h, map_zero])
  have hμ0T : μ0 ∈ ltTorsion Ω ϖ (n + 1) := mem_ltTorsion_of_root Ω hϖ n hμ0Q
  have hμ0n : aeval μ0 ((ltPolyIter ϖ n).map (algebraMap 𝒪[K] K)) ≠ 0 := by
    intro h
    have h2 : aeval (ι μ0M) ((ltPolyIter ϖ n).map (algebraMap 𝒪[K] K)) = 0 := by
      rw [aeval_algHom_apply, aeval_intermediate_eq_zero μ0M h, map_zero]
    rw [hιμ0, aeval_map_K_eq_B hKE] at h2
    exact hθn h2
  /- The key computation: `σ̃ μ₀ = [uw]_g μ₀`. -/
  set zw : Ω := ltAct hπ (n + 1) w lam with hzwdef
  have hzwT : zw ∈ ltTorsion Ω π (n + 1) := ltAct_x0_mem Ω hπ n w
  have hσlam : σM lamM = ⟨zw, hTM hzwT⟩ := Subtype.ext (hw lam hlamT)
  have hτy0 : τ y0 = ι ⟨zw, hTM hzwT⟩ := by rw [hy0def, hτι, hσlam]
  have huw : ltAct hπ (n + 1) (u : 𝒪[K]) zw = ltAct hπ (n + 1) ((u : 𝒪[K]) * w) lam :=
    ltAct_ltAct_x0 Ω hπ n w u
  have huwT : ltAct hπ (n + 1) ((u : 𝒪[K]) * w) lam ∈ ltTorsion Ω π (n + 1) := ltAct_x0_mem Ω hπ n _
  have huwT' : ltAct hπ (n + 1) (u : 𝒪[K]) zw ∈ ltTorsion Ω π (n + 1) := huw ▸ huwT
  have hgμ0 : ltAct hϖ (n + 1) ((u : 𝒪[K]) * w) μ0 ∈ M := by
    obtain ⟨d, hd⟩ := exists_ltAct_x0 Ω hϖ n μ0 hμ0T
    rw [hd, ltAct_ltAct_x0 Ω hϖ n]
    exact hgM (mem_ltField (ltAct_x0_mem Ω hϖ n _))
  have hτy0' : IsDistRoot (B := B) (τ y0) := by rw [hτy0]; exact hdistf _ hzwT
  have hkey : σM μ0M = ⟨ltAct hϖ (n + 1) ((u : 𝒪[K]) * w) μ0, hgμ0⟩ := by
    apply hι_inj
    calc ι (σM μ0M) = τ (ι μ0M) := (hτι μ0M).symm
      _ = τ (evalHom hy0 θ) := by rw [hιμ0]
      _ = evalHom hτy0' (PowerSeries.map (σ : B →+* B) θ) := evalHom_twist hy0 σ τ hτB hτy0' θ
      _ = evalHom (hdistf _ hzwT)
          (θ.subst (PowerSeries.map (algebraMap 𝒪[K] B) (ltSer hπ (u : 𝒪[K])))) := by
        rw [hθb']; exact evalHom_congr _ _ hτy0 _
      _ = evalHom (hdistf ⟨_, hTM huwT'⟩ huwT') θ :=
        hsubst_f ⟨zw, hTM hzwT⟩ hzwT (u : 𝒪[K]) huwT'
      _ = evalHom (hdistf ⟨_, hTM huwT⟩ huwT) θ :=
        evalHom_congr _ _ (congrArg ι (Subtype.ext huw)) θ
      _ = evalHom hy0 (θ.subst (PowerSeries.map (algebraMap 𝒪[K] B) (ltSer hπ ((u : 𝒪[K]) * w)))) :=
        (hsubst_f lamM hlamT _ huwT).symm
      _ = evalHom hy0 ((PowerSeries.map (algebraMap 𝒪[K] B) (ltSer hϖ ((u : 𝒪[K]) * w))).subst θ) := by
        rw [hθd']
      _ = evalHom hθy0 (PowerSeries.map (algebraMap 𝒪[K] B) (ltSer hϖ ((u : 𝒪[K]) * w))) :=
        evalHom_subst hy0 hθ0 hθy0 _
      _ = evalHom (hdistg μ0M hμ0T) (PowerSeries.map (algebraMap 𝒪[K] B) (ltSer hϖ ((u : 𝒪[K]) * w))) :=
        evalHom_congr _ _ hιμ0.symm _
      _ = ι ⟨ltAct hϖ (n + 1) ((u : 𝒪[K]) * w) μ0, hgμ0⟩ :=
        (algHom_ltAct hKE hϖ ι μ0M hμ0T (hdistg μ0M hμ0T) _ hgμ0).symm
  /- `μ₀` generates `Λ_{g,N}`. -/
  obtain ⟨c0, hc0⟩ := exists_ltAct_x0 Ω hϖ n μ0 hμ0T
  have hc0u : IsUnit c0 := by
    by_contra hnu
    have hc0m : c0 ∈ IsLocalRing.maximalIdeal 𝒪[K] := hnu
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hc0m
    obtain ⟨c', hc'⟩ := hc0m
    apply hμ0n
    rw [hc0, aeval_iter_ltAct_x0 Ω hϖ n n, ← ltAct_zero_x0 Ω hϖ n]
    refine (ltAct_x0_eq_iff Ω hϖ n _ _).2 ?_
    rw [sub_zero, Ideal.mem_span_singleton, hc']
    exact ⟨c', by ring⟩
  obtain ⟨d, hd⟩ := exists_ltAct_x0 Ω hϖ n μ hμ
  obtain ⟨cu, hcu⟩ := hc0u
  set e : 𝒪[K] := d * ↑cu⁻¹ with hedef
  have hde : e * c0 = d := by
    rw [hedef, ← hcu, mul_assoc, Units.inv_mul, mul_one]
  have hμe : μ = ltAct hϖ (n + 1) e μ0 := by
    rw [hc0, ltAct_ltAct_x0 Ω hϖ n, hde, hd]
  have h1M : ltAct hϖ (n + 1) e μ0 ∈ M := hμe ▸ hgM (mem_ltField hμ)
  have hσμ0 : ((σM μ0M : M) : Ω) = ltAct hϖ (n + 1) ((u : 𝒪[K]) * w) μ0 := congrArg Subtype.val hkey
  have h2M : ltAct hϖ (n + 1) e ((σM μ0M : M) : Ω) ∈ M := by
    rw [hσμ0, hc0, ltAct_ltAct_x0 Ω hϖ n, ltAct_ltAct_x0 Ω hϖ n]
    exact hgM (mem_ltField (ltAct_x0_mem Ω hϖ n _))
  have hcomm := algEquiv_ltAct σM hϖ (n + 1) e μ0M h1M h2M
  have hμM : (⟨μ, hgM (mem_ltField hμ)⟩ : M) = ⟨ltAct hϖ (n + 1) e μ0, h1M⟩ := Subtype.ext hμe
  rw [hμM, hcomm]
  show ltAct hϖ (n + 1) e ((σM μ0M : M) : Ω) = _
  rw [hσμ0, hμe, hc0, ltAct_ltAct_x0 Ω hϖ n, ltAct_ltAct_x0 Ω hϖ n, ltAct_ltAct_x0 Ω hϖ n,
    ltAct_ltAct_x0 Ω hϖ n]
  congr 1
  ring

end Core

end NumberFieldKB.MilneCFT.LocalCFT
