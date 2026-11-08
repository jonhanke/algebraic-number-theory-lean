import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Cochains

/-!
# Milne, *Class Field Theory*, Chapter II: acyclic resolutions compute cohomology (Remark 1.14)

Dimension shifting along the short exact sequences `0 → Zᵏ → Jᵏ → Zᵏ⁺¹ → 0` (with `Zᵏ = ker (Jᵏ → Jᵏ⁺¹)`) gives
`Hʳ(G, M) ≅ H¹(G, Zʳ⁻¹) ≅ coker ((Jʳ⁻¹)ᴳ → (Zʳ)ᴳ) ≅ Hʳ((J•)ᴳ)`, using left exactness of invariants.
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology Limits

variable {G : Type} [Group G]

section Helpers

/-- `H¹(X₁) ≅ coker (X₂ᴳ → X₃ᴳ)` when `H¹(X₂) = 0`. -/
lemma h1_iso_cokernel (X : ShortComplex (Rep ℤ G)) (hX : X.ShortExact)
    (h1 : IsZero (groupCohomology X.X₂ 1)) :
    Nonempty (groupCohomology X.X₁ 1 ≅ cokernel ((Rep.invariantsFunctor ℤ G).map X.g)) := by
  have hS := mapShortComplex₃_exact hX (i := 0) (j := 1) rfl
  have : Epi (mapShortComplex₃ hX (i := 0) (j := 1) rfl).g := epi_δ_of_isZero hX 0 h1
  have hc := hS.gIsCokernel
  refine ⟨hc.coconePointUniqueUpToIso (cokernelIsCokernel _) ≪≫ ?_⟩
  refine cokernel.mapIso _ _ (groupCohomology.H0Iso X.X₂)
    (groupCohomology.H0Iso X.X₃) ?_
  exact groupCohomology.map_id_comp_H0Iso_hom X.g

lemma homology_map_iso {A B C : Rep ℤ G} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
    (w' : (Rep.invariantsFunctor ℤ G).map f ≫ (Rep.invariantsFunctor ℤ G).map g = 0) :
    Nonempty ((ShortComplex.mk ((Rep.invariantsFunctor ℤ G).map f)
      ((Rep.invariantsFunctor ℤ G).map g) w').homology ≅
      cokernel ((Rep.invariantsFunctor ℤ G).map (kernel.lift g f w))) := by
  refine ⟨ShortComplex.homologyIsoCokernelLift _ ≪≫
    cokernel.mapIso _ _ (Iso.refl _) (PreservesKernel.iso (Rep.invariantsFunctor ℤ G) g).symm ?_⟩
  rw [← cancel_mono (PreservesKernel.iso (Rep.invariantsFunctor ℤ G) g).hom,
    ← cancel_mono (kernel.ι _)]
  simp

/-- If `f = 0`, the invariants complex has homology the kernel. -/
lemma homology_map_iso_zero {A B C : Rep ℤ G} (f : A ⟶ B) (g : B ⟶ C) (hf : f = 0)
    (w' : (Rep.invariantsFunctor ℤ G).map f ≫ (Rep.invariantsFunctor ℤ G).map g = 0) :
    Nonempty ((ShortComplex.mk ((Rep.invariantsFunctor ℤ G).map f)
      ((Rep.invariantsFunctor ℤ G).map g) w').homology ≅
      kernel ((Rep.invariantsFunctor ℤ G).map g)) := by
  have h : kernel.lift ((Rep.invariantsFunctor ℤ G).map g) ((Rep.invariantsFunctor ℤ G).map f) w' =
      0 := by
    rw [← cancel_mono (kernel.ι _)]
    simp [hf]
  exact ⟨ShortComplex.homologyIsoCokernelLift _ ≪≫ cokernelIsoOfEq h ≪≫ cokernelZeroIsoTarget⟩

end Helpers

section Resolution

variable (J : CochainComplex (Rep ℤ G) ℕ)

/-- The cycles `Zᵏ = ker (Jᵏ → Jᵏ⁺¹)`. -/
noncomputable abbrev cycZ (k : ℕ) : Rep ℤ G := kernel (J.d k (k + 1))

/-- The map `Jᵏ → Zᵏ⁺¹`. -/
noncomputable def liftZ (k : ℕ) : J.X k ⟶ cycZ J (k + 1) :=
  kernel.lift (J.d (k + 1) (k + 2)) (J.d k (k + 1)) (J.d_comp_d _ _ _)

/-- The short exact sequence `0 → Zᵏ → Jᵏ → Zᵏ⁺¹ → 0`. -/
noncomputable def sesZ (k : ℕ) : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (kernel.ι (J.d k (k + 1))) (liftZ J k) (by
    rw [← cancel_mono (kernel.ι (J.d (k + 1) (k + 2)))]
    simp [liftZ])

lemma sesZ_shortExact (hJ : ∀ n : ℕ, (J.sc (n + 1)).Exact) (k : ℕ) : (sesZ J k).ShortExact := by
  have hex : (J.sc' k (k + 1) (k + 2)).Exact :=
    (HomologicalComplex.exactAt_iff' J k (k + 1) (k + 2) (by simp) (by simp)).1 (hJ k)
  have hepi : Epi (liftZ J k) := by
    have := ShortComplex.exact_iff_epi_kernel_lift _ |>.1 hex
    exact this
  refine ShortComplex.ShortExact.mk' ?_ (inferInstance : Mono (kernel.ι (J.d k (k + 1)))) hepi
  refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
    (fun {W} (x : W ⟶ J.X k) hx => kernel.lift (J.d k (k + 1)) x ?_) ?_ ?_)
  · have hx' : x ≫ liftZ J k = 0 := hx
    have : x ≫ liftZ J k ≫ kernel.ι (J.d (k + 1) (k + 2)) = 0 := by
      rw [← Category.assoc, hx', zero_comp]
    simpa [liftZ] using this
  · intros; exact kernel.lift_ι _ _ _
  · intro W x hx m hm
    exact (cancel_mono (kernel.ι (J.d k (k + 1)))).1 (hm.trans (kernel.lift_ι _ _ _).symm)

lemma shift_iso (hJ : ∀ n : ℕ, (J.sc (n + 1)).Exact)
    (hacyc : ∀ r s : ℕ, 0 < s → IsZero (groupCohomology (J.X r) s)) :
    ∀ s k m : ℕ, k + s = m →
      Nonempty (groupCohomology (cycZ J k) (s + 1) ≅ groupCohomology (cycZ J m) 1) := by
  intro s
  induction s with
  | zero => intro k m h; simp at h; subst h; exact ⟨Iso.refl _⟩
  | succ s ih =>
    intro k m h
    obtain ⟨e⟩ := ih (k + 1) m (by omega)
    have hX := sesZ_shortExact J hJ k
    have := isIso_δ_of_isZero hX (s + 1) (hacyc k (s + 1) (by omega)) (hacyc k (s + 1 + 1) (by omega))
    exact ⟨(asIso (groupCohomology.δ hX (s + 1) (s + 1 + 1) rfl)).symm ≪≫ e⟩

end Resolution

/-- **Remark 1.14** (p. 63): cohomology is computed by acyclic resolutions. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.14, p. 63"]
theorem remark1_14 : Remark1_14 := by
  refine ⟨fun G _ M J ε hε hmono hex hJ hacyc r => ?_⟩
  have := hmono
  have e1 : M ≅ kernel (J.d 0 1) :=
    IsLimit.conePointUniqueUpToIso (hex.fIsKernel) (limit.isLimit _)
  have e : M ≅ cycZ J 0 := e1
  cases r with
  | zero =>
    have hd : J.d 0 0 = 0 := J.shape 0 0 (by simp)
    have w' : (Rep.invariantsFunctor ℤ G).map (J.d 0 0) ≫ (Rep.invariantsFunctor ℤ G).map (J.d 0 1)
        = 0 := by simp
    refine ⟨groupCohomology.H0Iso M ≪≫ (Rep.invariantsFunctor ℤ G).mapIso e ≪≫
      PreservesKernel.iso (Rep.invariantsFunctor ℤ G) (J.d 0 1) ≪≫
      (homology_map_iso_zero (J.d 0 0) (J.d 0 1) hd w').some.symm ≪≫ ?_⟩
    exact (HomologicalComplex.homologyIsoSc' (((Rep.invariantsFunctor ℤ G).mapHomologicalComplex _).obj J)
      0 0 1 (by simp) (by simp)).symm
  | succ s =>
    have hX := sesZ_shortExact J hJ s
    have w' : (Rep.invariantsFunctor ℤ G).map (J.d s (s + 1)) ≫
        (Rep.invariantsFunctor ℤ G).map (J.d (s + 1) (s + 2)) = 0 := by
      rw [← Functor.map_comp, J.d_comp_d, Functor.map_zero]
    refine ⟨(groupCohomology.functor ℤ G (s + 1)).mapIso e ≪≫
      (shift_iso J hJ hacyc s 0 s (by simp)).some ≪≫
      (h1_iso_cokernel (sesZ J s) hX (hacyc s 1 (by omega))).some ≪≫
      (homology_map_iso (J.d s (s + 1)) (J.d (s + 1) (s + 2)) (J.d_comp_d _ _ _) w').some.symm ≪≫ ?_⟩
    exact (HomologicalComplex.homologyIsoSc' (((Rep.invariantsFunctor ℤ G).mapHomologicalComplex _).obj J)
      s (s + 1) (s + 2) (by simp) (by simp)).symm

end NumberFieldKB.MilneCFT
