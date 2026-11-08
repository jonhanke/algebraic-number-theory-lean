import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.LubinTate.ArtinMap
import NumberFieldKB.MilneCFT.LubinTate.LocalKroneckerWeberCFT
import NumberFieldKB.MilneCFT.LubinTate.ExtensionYamaguchi
import NumberFieldKB.MilneCFT.LocalCFT.ReciprocityTauCeti
import NumberFieldKB.MilneCFT.LocalCFT.UnramifiedTauCeti
import NumberFieldKB.MilneCFT.Ch3Unramified

/-!
# Auxiliary facts for Milne, *Class Field Theory*, Chapter I, Theorem 3.9

Helper lemmas for `ArtinIndependenceProof.lean`: finite unramified extensions are finite abelian extensions, the
tower $K_{\pi,n}$ is increasing, $K^{\mathrm{un}}$ is the union of the unramified extensions of degree $m!$, and
the union of all finite abelian extensions is $K_\pi K^{\mathrm{un}}$ for every prime element $\pi$.
-/

open scoped ValuativeRel
open Polynomial

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- The unramified extension of degree `f ≥ 1` as a finite abelian extension of `K` inside `Ω`
(its Galois group is cyclic). -/
def unrExt (f : ℕ) (hf : f ≠ 0) : FiniteAbelianExt K Ω where
  toField := TauCeti.unramifiedExtension K Ω f
  isAbelianGalois := by
    have : IsSepClosed Ω := IsSepClosure.sep_closed K
    let E := TauCeti.unramifiedExtension K Ω f
    let _ : ValuativeRel E := TauCeti.finiteIntermediateFieldValuativeRel K Ω E
    let _ : TopologicalSpace E := TauCeti.finiteIntermediateFieldTopology K Ω E
    have : ValuativeExtension K E := TauCeti.finiteIntermediateField_valuativeExtension K Ω E
    have : IsNonarchimedeanLocalField E := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω E
    have hU : TauCeti.IsUnramified K E := TauCeti.isUnramified_unramifiedExtension hf
    have : IsCyclic Gal(E/K) := TauCeti.isCyclic_algEquiv
    have : IsMulCommutative Gal(E/K) := ⟨⟨IsCyclic.commGroup.mul_comm⟩⟩
    exact ⟨⟩

/-- The unramified extension of degree `f ≥ 1` is unramified in the sense of `IsUnramifiedExt`. -/
theorem isUnramifiedExt_unrExt (f : ℕ) (hf : f ≠ 0) :
    IsUnramifiedExt (unrExt (K := K) (Ω := Ω) f hf).toField := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  let E := TauCeti.unramifiedExtension K Ω f
  let _ : ValuativeRel E := TauCeti.finiteIntermediateFieldValuativeRel K Ω E
  let _ : TopologicalSpace E := TauCeti.finiteIntermediateFieldTopology K Ω E
  have : ValuativeExtension K E := TauCeti.finiteIntermediateField_valuativeExtension K Ω E
  have : IsNonarchimedeanLocalField E := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω E
  exact (isUnramified_iff_isUnramifiedExt E).1 (TauCeti.isUnramified_unramifiedExtension hf)

/-- A finite unramified extension of `K` inside `Ω` is the unramified extension of degree `[E : K]`. -/
theorem eq_unramifiedExtension_of_isUnramifiedExt (E : IntermediateField K Ω) [FiniteDimensional K E]
    (hE : IsUnramifiedExt E) : E = TauCeti.unramifiedExtension K Ω (Module.finrank K E) := by
  let _ : ValuativeRel E := TauCeti.finiteIntermediateFieldValuativeRel K Ω E
  let _ : TopologicalSpace E := TauCeti.finiteIntermediateFieldTopology K Ω E
  have : ValuativeExtension K E := TauCeti.finiteIntermediateField_valuativeExtension K Ω E
  have : IsNonarchimedeanLocalField E := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω E
  have : TauCeti.IsUnramified K E := (isUnramified_iff_isUnramifiedExt E).2 hE
  exact E.eq_unramifiedExtension_finrank

/-- A finite unramified extension is contained in the unramified extension of degree `f!` for some `f`. -/
theorem le_unramifiedExtension_factorial (E : IntermediateField K Ω) [FiniteDimensional K E]
    (hE : IsUnramifiedExt E) : ∃ f : ℕ, E ≤ TauCeti.unramifiedExtension K Ω f.factorial := by
  refine ⟨Module.finrank K E, ?_⟩
  have hpos : 0 < Module.finrank K E := Module.finrank_pos
  conv_lhs => rw [eq_unramifiedExtension_of_isUnramifiedExt E hE]
  exact TauCeti.unramifiedExtension_le_of_dvd (Nat.factorial_ne_zero _) (Nat.dvd_factorial hpos le_rfl)

/-- $K^{\mathrm{un}}$ is the union of the unramified extensions of degree $m!$. -/
theorem unramifiedClosure_eq_iSup :
    unramifiedClosure K Ω = ⨆ m : ℕ, TauCeti.unramifiedExtension K Ω m.factorial := by
  apply le_antisymm
  · refine iSup_le fun L => iSup_le fun ⟨hfd, hu⟩ => ?_
    obtain ⟨f, hf⟩ := le_unramifiedExtension_factorial L hu
    exact hf.trans (le_iSup (fun m : ℕ => TauCeti.unramifiedExtension K Ω m.factorial) f)
  · refine iSup_le fun m => ?_
    exact le_iSup₂_of_le (TauCeti.unramifiedExtension K Ω m.factorial)
      ⟨inferInstance, isUnramifiedExt_unrExt m.factorial (Nat.factorial_ne_zero _)⟩ le_rfl

/-- $\Lambda_n \subseteq \Lambda_{n+1}$ (the roots of $f^{(n)}$ are roots of $f^{(n+1)} = f \circ f^{(n)}$,
since $f(0) = 0$). -/
theorem ltTorsion_subset_succ {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    ltTorsion Ω π n ⊆ ltTorsion Ω π (n + 1) := by
  intro α hα
  unfold ltTorsion at hα ⊢
  rw [Polynomial.mem_rootSet] at hα ⊢
  refine ⟨((ltPolyIter_isDistinguishedAt hπ (n + 1)).monic.map _).ne_zero, ?_⟩
  rw [ltPolyIter_succ, Polynomial.map_comp, Polynomial.aeval_comp, hα.2]
  have hq : resCard K ≠ 0 := by have := resCard_pos hπ; omega
  simp [ltPoly, hq]

theorem ltField_le_succ {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    ltField Ω π n ≤ ltField Ω π (n + 1) :=
  IntermediateField.adjoin.mono _ _ _ (ltTorsion_subset_succ hπ n)

theorem ltField_mono {π : 𝒪[K]} (hπ : Irreducible π) : Monotone (ltField Ω π) :=
  monotone_nat_of_le_succ (ltField_le_succ hπ)

/-- Every $K_{\pi,n}$ is contained in a finite abelian extension. -/
theorem ltField_le_abelian {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    ltField Ω π n ≤ (ltFieldExt (lubinTateExtensionTheorem K Ω) hπ (n := n + 1) (by omega)).toField :=
  ltField_le_succ hπ n

/-- The compositum of all finite abelian extensions of `K` in `Ω`. -/
def abelianSup (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] : IntermediateField K Ω :=
  ⨆ L : FiniteAbelianExt K Ω, L.toField

/-- **Local Kronecker–Weber, field form**: for every prime element $\pi$, $K_\pi K^{\mathrm{un}}$ is the compositum of
all finite abelian extensions of $K$. -/
theorem ltTower_sup_unramifiedClosure_eq_abelianSup {π : 𝒪[K]} (hπ : Irreducible π) :
    ltTower Ω π ⊔ unramifiedClosure K Ω = abelianSup K Ω := by
  apply le_antisymm
  · refine sup_le (iSup_le fun n => ?_) ?_
    · exact (ltField_le_abelian hπ n).trans
        (le_iSup (fun L : FiniteAbelianExt K Ω => L.toField)
          (ltFieldExt (lubinTateExtensionTheorem K Ω) hπ (n := n + 1) (by omega)))
    · refine iSup_le fun L => iSup_le fun ⟨hfd, hu⟩ => ?_
      obtain ⟨f, hf⟩ := le_unramifiedExtension_factorial L hu
      exact hf.trans (le_iSup (fun L : FiniteAbelianExt K Ω => L.toField)
        (unrExt f.factorial (Nat.factorial_ne_zero _)))
  · exact iSup_le fun L => (localKroneckerWeber K Ω).le hπ L

/-- **Theorem 3.9, field equality**: $K_\pi K^{\mathrm{un}}$ does not depend on the prime element $\pi$
(Milne, *CFT*, I, Theorem 3.9; unconditional, from local Kronecker–Weber). -/
theorem ltTower_sup_unramifiedClosure_eq {π ϖ : 𝒪[K]} (hπ : Irreducible π) (hϖ : Irreducible ϖ) :
    ltTower Ω π ⊔ unramifiedClosure K Ω = ltTower Ω ϖ ⊔ unramifiedClosure K Ω :=
  (ltTower_sup_unramifiedClosure_eq_abelianSup hπ).trans
    (ltTower_sup_unramifiedClosure_eq_abelianSup hϖ).symm

/-! ## The Tau Ceti local Artin map satisfies the properties of $\phi_\pi$ that need no explicit reciprocity -/

/-- The family `tauCetiArtin` satisfies the conditions of Theorem 1.1 (restated for convenience). -/
theorem isLocalArtinMap_tauCeti_family :
    IsLocalArtinMap (fun L : FiniteAbelianExt K Ω => tauCetiArtin L) :=
  ⟨galRestrict_tauCetiArtin, fun hπ L hL => isFrobenius_tauCetiArtin hπ L hL, ker_tauCetiArtin,
    surjective_tauCetiArtin⟩

/-- On a finite unramified extension the local Artin map kills units (units are norms from unramified
extensions, Milne, *CFT*, III, Proposition 1.2). -/
theorem tauCetiArtin_unit_of_unramified (L : FiniteAbelianExt K Ω) (hL : IsUnramifiedExt L.toField)
    (u : 𝒪[K]ˣ) : tauCetiArtin L (unitToK u) = 1 := by
  have hu : unitToK u ∈ unitGroup K := mem_unitGroup.2 ⟨u, rfl⟩
  obtain ⟨v, -, hv⟩ := (Ch3.prop1_2 (K := K) (Ω := Ω)).surj L.toField hL _ hu
  rw [← MonoidHom.mem_ker, ker_tauCetiArtin]
  exact ⟨v, hv⟩

/-- On a finite unramified extension, $\phi_L(u\pi^m) = \mathrm{Frob}^m$ for the local Artin map of Theorem 1.1
(for any Frobenius element $\sigma$). -/
theorem tauCetiArtin_frobenius {π : 𝒪[K]} (hπ : Irreducible π) (L : FiniteAbelianExt K Ω)
    (hL : IsUnramifiedExt L.toField) (σ : Gal(L.toField/K)) (hσ : IsFrobenius L.toField σ) (u : 𝒪[K]ˣ)
    (m : ℤ) : tauCetiArtin L (unitToK u * primeUnit hπ ^ m) = σ ^ m := by
  rw [map_mul, map_zpow, tauCetiArtin_unit_of_unramified L hL u, one_mul,
    (unramifiedInput K Ω).frobenius_unique L hL _ σ (isFrobenius_tauCetiArtin hπ L hL) hσ]

/-- An automorphism fixing `x` fixes `x` under all integer powers. -/
theorem zpow_apply_eq_of_apply_eq {M : IntermediateField K Ω} (σ : Gal(M/K)) (x : M) (hx : σ x = x)
    (m : ℤ) : (σ ^ m) x = x := by
  have : σ ∈ MulAction.stabilizer Gal(M/K) x := by rw [MulAction.mem_stabilizer_iff]; exact hx
  exact MulAction.mem_stabilizer_iff.1 (zpow_mem this m)

/-- $\phi_L(\pi)$ fixes $K_{\pi,n}$ pointwise, since $\pi$ is a norm from $K_{\pi,n}$ (Milne, *CFT*, I,
Theorem 3.6 (c)) and the kernel of the local Artin map is the norm group. -/
theorem tauCetiArtin_primeUnit_apply {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) (L : FiniteAbelianExt K Ω)
    (hL : ltField Ω π n ≤ L.toField) (x : L.toField) (hx : (x : Ω) ∈ ltField Ω π n) :
    tauCetiArtin L (primeUnit hπ) x = x := by
  rcases n with _ | k
  · have h0 : ltField Ω π 0 = ⊥ := by
      rw [ltField, ltTorsion_zero]; exact IntermediateField.adjoin_zero
    rw [h0] at hx
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hx
    have : x = algebraMap K L.toField c := Subtype.ext hc.symm
    rw [this]
    exact AlgEquiv.commutes _ c
  · set M := ltFieldExt (lubinTateExtensionTheorem K Ω) hπ (n := k + 1) (by omega) with hM
    have h1 : M.toField ≤ L.toField := hL
    have hker : tauCetiArtin M (primeUnit hπ) = 1 := by
      rw [← MonoidHom.mem_ker, ker_tauCetiArtin]
      exact isNorm_succ Ω hπ k
    have h3 := galRestrict_tauCetiArtin M L h1 (primeUnit hπ)
    rw [hker] at h3
    have h2 := galRestrict_apply h1 (tauCetiArtin L (primeUnit hπ)) ⟨x, hx⟩
    rw [h3] at h2
    exact Subtype.ext h2.symm

/-! ## Generation lemmas -/

/-- An automorphism of $N$ fixing two subfields $M_1, M_2$ with $N \le M_1 M_2$ is trivial. -/
theorem eq_one_of_fixes_sup {M₁ M₂ N : IntermediateField K Ω} (h₁ : M₁ ≤ N) (h₂ : M₂ ≤ N)
    (hN : N ≤ M₁ ⊔ M₂) (g : Gal(N/K)) (g₁ : ∀ x : N, (x : Ω) ∈ M₁ → g x = x)
    (g₂ : ∀ x : N, (x : Ω) ∈ M₂ → g x = x) : g = 1 := by
  have hsup : IntermediateField.restrict h₁ ⊔ IntermediateField.restrict h₂ = (⊤ : IntermediateField K N) := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict, IntermediateField.lift_restrict,
      IntermediateField.lift_top]
    exact le_antisymm (sup_le h₁ h₂) hN
  have hg : g ∈ IntermediateField.fixingSubgroup (⊤ : IntermediateField K N) := by
    rw [← hsup, IntermediateField.fixingSubgroup_sup]
    refine ⟨?_, ?_⟩
    · change g ∈ (IntermediateField.restrict h₁).fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      exact g₁ y ((IntermediateField.mem_restrict h₁ y).1 hy)
    · change g ∈ (IntermediateField.restrict h₂).fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      exact g₂ y ((IntermediateField.mem_restrict h₂ y).1 hy)
  rw [IntermediateField.fixingSubgroup_top] at hg
  exact Subgroup.mem_bot.1 hg

/-- An automorphism of $N$ fixing the elements of a set $S \subseteq N$ of algebraic elements fixes the
field generated by $S$ (inside $N$). -/
theorem fix_of_adjoin {N : IntermediateField K Ω} (S : Set Ω) (hS : S ⊆ N)
    (hSalg : ∀ x ∈ S, IsAlgebraic K x) (g : Gal(N/K))
    (hg : ∀ (x : Ω) (hx : x ∈ N), x ∈ S → g ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∀ x : N, (x : Ω) ∈ IntermediateField.adjoin K S → g x = x := by
  intro x hx
  have hx' : (x : Ω) ∈ Algebra.adjoin K S := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic hSalg]
    exact hx
  let E : Subalgebra K Ω :=
    (AlgHom.equalizer (g : N →ₐ[K] N) (AlgHom.id K N)).map (IntermediateField.val N)
  have hS' : S ⊆ E := fun s hs => ⟨⟨s, hS hs⟩, hg s (hS hs) hs, rfl⟩
  obtain ⟨y, hy, hyx⟩ := Algebra.adjoin_le hS' hx'
  have : y = x := Subtype.ext hyx
  subst this
  exact hy

/-- A finite subextension of $K_\pi K^{\mathrm{un}}$ lies in $K_{\pi,n}\cdot K_{m!}$ for some $n$ and $m$,
where $K_{f}$ is the unramified extension of degree $f$. -/
theorem exists_le_ltField_sup {π : 𝒪[K]} (hπ : Irreducible π) (L : IntermediateField K Ω)
    [FiniteDimensional K L] (hL : L ≤ ltTower Ω π ⊔ unramifiedClosure K Ω) :
    ∃ n m : ℕ, L ≤ ltField Ω π n ⊔ TauCeti.unramifiedExtension K Ω m.factorial := by
  set c : ℕ → IntermediateField K Ω :=
    fun k => ltField Ω π k ⊔ TauCeti.unramifiedExtension K Ω k.factorial with hc
  have hmono : Monotone c := fun a b hab => sup_le_sup (ltField_mono hπ hab)
    (TauCeti.unramifiedExtension_le_of_dvd (Nat.factorial_ne_zero _) (Nat.factorial_dvd_factorial hab))
  have hle : L ≤ ⨆ k, c k := by
    refine hL.trans (sup_le (iSup_le fun n => ?_) ?_)
    · exact le_sup_left.trans (le_iSup c n)
    · rw [unramifiedClosure_eq_iSup]
      exact iSup_le fun n => le_sup_right.trans (le_iSup c n)
  have hfg : L.FG := IntermediateField.essFiniteType_iff.1 inferInstance
  obtain ⟨t, ht, htL⟩ := IntermediateField.fg_def.1 hfg
  have hcomp : IsCompactElement L := htL ▸ IntermediateField.adjoin_finite_isCompactElement ht
  rw [isCompactElement_iff_le_of_directed_sSup_le] at hcomp
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hcomp (Set.range c) (Set.range_nonempty c)
    hmono.directed_le.directedOn_range (by rwa [sSup_range])
  exact ⟨k, k, hk⟩

end NumberFieldKB.MilneCFT.LocalCFT
