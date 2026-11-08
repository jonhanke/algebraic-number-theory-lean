import NumberFieldKB.MilneCFT.Ch2Remark312
import NumberFieldKB.MilneCFT.Ch2TensorCohomTrivial
import NumberFieldKB.MilneCFT.Ch2TorInjective

/-!
# Milne, *Class Field Theory*, Chapter II, Remark 3.12: proof of the tensor lemma

We prove `TensorCohomTrivialLemma` and hence `Remark3_12` unconditionally.

* `isZero_tateCohomology_tensor_of_isZero_tor`: for a finite `p`-group `G`, a representation `W` with no Tate
  cohomology and a representation `M` with `Tor₁(M, W) = 0`, the tensor product `M ⊗ W` has no Tate cohomology.
  Proof: write `W` as a quotient of the induced representation `F` from the trivial subgroup on the free module
  on the underlying set of `W`; the kernel `R` has no `ℤ`-torsion and no Tate cohomology, so `M ⊗ R` has no Tate
  cohomology by `isZero_tateCohomology_tensor_of_torsionFree`; since `Tor₁(M, W) = 0` the sequence
  `0 → M ⊗ R → M ⊗ F → M ⊗ W → 0` is short exact and `M ⊗ F` has no Tate cohomology.
* `tensorCohomTrivialLemma`: the general finite group case, from the triviality criterion on `p`-subgroups.
-/

open CategoryTheory Rep Limits MonoidalCategory
open TauCeti TauCeti.TateCohomology

namespace NumberFieldKB.MilneCFT

section PGroup

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]

/-- The structure map from the induced representation on the free module over the underlying set of `W` onto `W`. -/
noncomputable def freeCover (W : Rep ℤ G) : indBot ℤ G (W.V →₀ ℤ) ⟶ W :=
  ((indBotFunctor ℤ G).map (ModuleCat.ofHom (Finsupp.linearCombination ℤ (id : W.V → W.V))) :
    (indBotFunctor ℤ G).obj (ModuleCat.of ℤ (W.V →₀ ℤ)) ⟶ (indBotFunctor ℤ G).obj (ModuleCat.of ℤ W.V)) ≫
    indBotCounit W

omit [Fintype G] in
/-- The structure map from the induced representation onto `W` is surjective. -/
theorem freeCover_surjective (W : Rep ℤ G) : Function.Surjective (freeCover W).hom := by
  intro w
  let φ := ModuleCat.ofHom (Finsupp.linearCombination ℤ (id : W.V → W.V))
  have hφ : φ.hom (Finsupp.single w 1) = w := by
    simp [φ]
    exact @one_smul ℤ W.V _ (DistribMulAction.toMulAction) w
  let x := Representation.IndV.mk (⊥ : Subgroup G).subtype
    (Representation.trivial ℤ (⊥ : Subgroup G) (W.V →₀ ℤ)) 1 (Finsupp.single w 1)
  refine ⟨x, ?_⟩
  have h1 := indBotFunctor_map_hom_mk (k := ℤ) (G := G) φ 1 (Finsupp.single w 1)
  rw [hφ] at h1
  have h2 : (freeCover W).hom x = (indBotCounit W).hom (((indBotFunctor ℤ G).map φ).hom x) := rfl
  rw [h2]
  rw [h1]
  exact rightInverse_indBotCounit W w

/-- **Tensor lemma for a finite `p`-group.** If `W` has no Tate cohomology and `Tor₁(M, W) = 0` then `M ⊗ W` has no
Tate cohomology. -/
theorem isZero_tateCohomology_tensor_of_isZero_tor (hG : IsPGroup p G) (W M : Rep ℤ G)
    (hWc : ∀ n, IsZero (tateCohomology W n))
    (hTor : IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ M)).obj (ModuleCat.of ℤ W))) (n : ℤ) :
    IsZero (tateCohomology (M ⊗ W) n) := by
  classical
  let F : Rep ℤ G := indBot ℤ G (W.V →₀ ℤ)
  let ε : F ⟶ W := freeCover W
  have : Epi ε := (Rep.epi_iff_surjective ε).2 (freeCover_surjective W)
  have hS : (ShortComplex.kernelSequence ε).ShortExact := TauCeti.kernelSequence_shortExact ε
  let ι := (ShortComplex.kernelSequence ε).f
  have hFfree : Module.Free ℤ F.V :=
    Module.Free.of_equiv (indBotEquivFinsupp ℤ G (W.V →₀ ℤ)).symm
  have hFproj : Module.Projective ℤ F.V := Module.Projective.of_free
  have hFtf : ∀ (m : ℤ) (w : F.V), m • w = 0 → m = 0 ∨ w = 0 := fun m w h =>
    smul_eq_zero.1 h
  have hι : Function.Injective ι.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hRtf : ∀ (m : ℤ) (w : (ShortComplex.kernelSequence ε).X₁.V), m • w = 0 → m = 0 ∨ w = 0 := by
    intro m w h
    have : m • ι.hom w = 0 := by rw [← map_zsmul, h, map_zero]
    rcases hFtf m _ this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (hι (h1.trans (map_zero _).symm))
  have hFc : ∀ k, IsZero (tateCohomology F k) := fun k => isZero_indBot _ k
  have hRc : ∀ k, IsZero (tateCohomology (ShortComplex.kernelSequence ε).X₁ k) := fun k =>
    isZero_X₁_of_isZero_X₃_of_isZero_X₂ hS (k - 1) k (sub_add_cancel k 1) (hWc _) (hFc _)
  have hMR := isZero_tateCohomology_tensor_of_torsionFree hG _ hRtf hRc M
  have hinj : Function.Injective (LinearMap.lTensor M.V ι.hom.toLinearMap) := by
    have : CategoryTheory.Projective (ModuleCat.of ℤ F.V) := by
      have : Module.Projective ℤ F.V := hFproj
      exact (ModuleCat.of ℤ F.V).projective_of_categoryTheory_projective
    exact @lTensor_injective_of_isZero_tor (ModuleCat.of ℤ M.V) (ModuleCat.of ℤ W.V)
      (ModuleCat.of ℤ (ShortComplex.kernelSequence ε).X₁.V) (ModuleCat.of ℤ F.V) this
      (ModuleCat.ofHom ι.hom.toLinearMap) (ModuleCat.ofHom ε.hom.toLinearMap) hι
      ((Rep.epi_iff_surjective ε).1 inferInstance)
      (fun f => ((exact_iff_function_exact _).1 hS.exact) f) hTor
  have hT := shortExact_map_tensorLeft_of_injective hS.exact M hinj
  exact isZero_X₃_of_isZero_X₂_of_isZero_X₁ hT n (n + 1) rfl
    (isZero_tensor_indBot _ M n) (hMR (n + 1))

end PGroup

section General

variable {G : Type} [Group G] [Fintype G]

/-- Restriction of a tensor product is the tensor product of the restrictions, on Tate cohomology. -/
noncomputable def tateCohomologyResTensorIso (S : Subgroup G) [Fintype S] (M W : Rep ℤ G) (n : ℤ) :
    tateCohomology (res S.subtype M ⊗ res S.subtype W) n ≅ tateCohomology (res S.subtype (M ⊗ W)) n :=
  TauCeti.TateCohomology.mapIso (e := MulEquiv.refl S) (e' := LinearEquiv.refl ℤ _) ⟨fun _ _ => rfl⟩ n

/-- **The tensor lemma** (Milne, *Class Field Theory*, II, Remark 3.12, p. 85): if `W` has no Tate cohomology on any
subgroup and `Tor₁(M, W) = 0`, then `M ⊗ W` has no Tate cohomology. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 3.12, p. 85 (tensor lemma)"]
theorem tensorCohomTrivialLemma : TensorCohomTrivialLemma where
  isZero G _ _ W M hW hTor := by
    classical
    have hp : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S → ∀ n : ℤ,
        IsZero (tateCohomology (res S.subtype (M ⊗ W)) n) := by
      intro p _ S _ hS n
      exact (isZero_tateCohomology_tensor_of_isZero_tor hS (res S.subtype W) (res S.subtype M)
        (hW S) hTor n).of_iso (tateCohomologyResTensorIso S M W n)
    have hall : ∀ (S : Subgroup G) [Fintype S] (n : ℤ),
        IsZero (tateCohomology (res S.subtype (M ⊗ W)) n) := fun S _ n =>
      TauCeti.TateCohomology.isZero_of_forall_isPGroup (M ⊗ W) (q := 0)
        (fun p _ S _ hS => hp p S hS 0) (fun p _ S _ hS => hp p S hS (0 + 1)) S n
    exact fun n => isZero_of_forall_isZero_res (M ⊗ W) hall n

/-- **Remark 3.12** (Milne, *Class Field Theory*, II, Remark 3.12, p. 85), proved unconditionally. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 3.12, p. 85"]
theorem remark3_12 : Remark3_12 := remark3_12_of_lemma tensorCohomTrivialLemma

end General

end NumberFieldKB.MilneCFT
