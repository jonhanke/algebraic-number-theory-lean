import Mathlib
import QuadFormsKB.Citation

/-!
# `Tor₁(M, W) = 0` makes `M ⊗ -` injective on a projective presentation of `W`

Used for Milne, *Class Field Theory*, Chapter II, Remark 3.12 (the tensor lemma `TensorCohomTrivialLemma`).
Mathlib's `Tor` (`CategoryTheory.Tor`) is the left derived functor of `M ⊗ -`, computed from a projective
resolution of the second argument, and Mathlib has no long exact sequence for it. We prove directly:

`lTensor_injective_of_isZero_tor`: if `0 → R → F → W → 0` is exact with `F` projective and `Tor₁(M, W) = 0`,
then `M ⊗ R → M ⊗ F` is injective.

Proof: compare with a projective resolution `P₂ → P₁ → P₀ → W` (lifts `c : F → P₀`, `a : P₀ → F` over `W`); an
element `z` of the kernel gives a 1-cycle of `M ⊗ P`, hence a boundary, and the splitting `1 = a c + (1 - a c)` of
`F` over `W` writes `z` as the image of that boundary, which is `0`.
-/

open CategoryTheory Limits MonoidalCategory

namespace NumberFieldKB.MilneCFT

variable {M W R F : ModuleCat.{0} ℤ}

/-- Exactness of `M ⊗ P` in degree `1` when `Tor₁(M, W) = 0`. -/
theorem tensor_resolution_exact_one (P : ProjectiveResolution W)
    (hTor : IsZero (((Tor (ModuleCat.{0} ℤ) 1).obj M).obj W)) (y : (M ⊗ P.complex.X 1 : ModuleCat.{0} ℤ))
    (hy : (M ◁ P.complex.d 1 0) y = 0) :
    ∃ x : (M ⊗ P.complex.X 2 : ModuleCat.{0} ℤ), (M ◁ P.complex.d 2 1) x = y := by
  set T := ((tensoringLeft (ModuleCat.{0} ℤ)).obj M).mapHomologicalComplex _ |>.obj P.complex
  have hZ : IsZero (T.homology 1) :=
    IsZero.of_iso hTor (P.isoLeftDerivedObj ((tensoringLeft (ModuleCat.{0} ℤ)).obj M) 1).symm
  have hex : T.ExactAt 1 := (HomologicalComplex.exactAt_iff_isZero_homology T 1).2 hZ
  rw [HomologicalComplex.exactAt_iff' T 2 1 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hex
  exact hex y hy

/-- **`Tor₁(M, W) = 0` gives injectivity of `M ⊗ R → M ⊗ F`** for `0 → R → F → W → 0` exact, `F` projective. -/
theorem lTensor_injective_of_isZero_tor [Projective F] (ι : R ⟶ F) (ε : F ⟶ W)
    (hι : Function.Injective ι) (hε : Function.Surjective ε) (hex : ∀ f : F, ε f = 0 ↔ ∃ r, ι r = f)
    (hTor : IsZero (((Tor (ModuleCat.{0} ℤ) 1).obj M).obj W)) :
    Function.Injective (M ◁ ι) := by
  classical
  obtain ⟨P⟩ : Nonempty (ProjectiveResolution W) := ⟨projectiveResolution W⟩
  -- lifts over `W` (instance arguments passed explicitly: instance search does not find `Epi` hypotheses here)
  have hπ : Epi (P.π.f 0) := epi_of_isColimit_cofork P.isColimitCokernelCofork
  have hεepi : Epi ε := (ModuleCat.epi_iff_surjective _).2 hε
  let c : F ⟶ P.complex.X 0 := @Projective.factorThru _ _ _ _ _ _ ε (P.π.f 0) hπ
  have hc : c ≫ (P.π.f 0) = ε := @Projective.factorThru_comp _ _ _ _ _ _ ε (P.π.f 0) hπ
  let a : P.complex.X 0 ⟶ F := @Projective.factorThru _ _ _ _ _ _ (P.π.f 0) ε hεepi
  have ha : a ≫ ε = (P.π.f 0) := @Projective.factorThru_comp _ _ _ _ _ _ (P.π.f 0) ε hεepi
  -- exactness of the resolution at `P₀`
  have hex0 : ∀ q : P.complex.X 0, (P.π.f 0) q = 0 → ∃ y, P.complex.d 1 0 y = q := by
    intro q hq
    exact (ShortComplex.moduleCat_exact_iff _).1 P.exact₀ q hq
  -- the retraction of `ι`
  have hpre : ∀ f : F, ε f = 0 → ∃! r, ι r = f := fun f hf => by
    obtain ⟨r, hr⟩ := (hex f).1 hf
    exact ⟨r, hr, fun r' hr' => hι (hr'.trans hr.symm)⟩
  -- `g : P₁ → R`, `g = ι⁻¹ ∘ a ∘ d₁`
  have hg0 : ∀ y : P.complex.X 1, ε (a (P.complex.d 1 0 y)) = 0 := by
    intro y
    have h1 : ε (a (P.complex.d 1 0 y)) = (P.π.f 0) (P.complex.d 1 0 y) := by
      rw [← ha]; rfl
    rw [h1]
    have := P.complex_d_comp_π_f_zero
    exact congrArg (fun φ => φ.hom y) this |>.trans rfl
  let gfun : P.complex.X 1 → R := fun y => (hpre _ (hg0 y)).exists.choose
  have hgfun : ∀ y, ι (gfun y) = a (P.complex.d 1 0 y) := fun y => (hpre _ (hg0 y)).exists.choose_spec
  let g : P.complex.X 1 ⟶ R := ModuleCat.ofHom
    { toFun := gfun
      map_add' := fun y y' => hι (by rw [map_add, hgfun, hgfun, hgfun, map_add, map_add])
      map_smul' := fun n y => hι (by
        rw [RingHom.id_apply]
        erw [LinearMap.map_smul, hgfun, hgfun, LinearMap.map_smul, LinearMap.map_smul]) }
  have hg : ∀ y, ι (g y) = a (P.complex.d 1 0 y) := hgfun
  -- `h : F → R`, `h = ι⁻¹ ∘ (1 - a c)`
  have hh0 : ∀ f : F, ε (f - a (c f)) = 0 := by
    intro f
    have h1 : ε (a (c f)) = ε f := by
      have e1 : ε (a (c f)) = (P.π.f 0) (c f) := by rw [← ha]; rfl
      rw [e1, ← hc]; rfl
    rw [map_sub, h1, sub_self]
  let hfun : F → R := fun f => (hpre _ (hh0 f)).exists.choose
  have hhfun : ∀ f, ι (hfun f) = f - a (c f) := fun f => (hpre _ (hh0 f)).exists.choose_spec
  let h : F ⟶ R := ModuleCat.ofHom
    { toFun := hfun
      map_add' := fun f f' => hι (by rw [map_add, hhfun, hhfun, hhfun, map_add, map_add]; abel)
      map_smul' := fun n f => hι (by
        rw [RingHom.id_apply]
        erw [LinearMap.map_smul, hhfun, hhfun, LinearMap.map_smul, LinearMap.map_smul, smul_sub]) }
  have hh : ∀ f, ι (h f) = f - a (c f) := hhfun
  -- `g ∘ d₂ = 0`
  have hgd : P.complex.d 2 1 ≫ g = 0 := by
    ext x
    apply hι
    change ι (g (P.complex.d 2 1 x)) = ι 0
    rw [hg, map_zero]
    have := P.complex.d_comp_d 2 1 0
    have h2 : P.complex.d 1 0 (P.complex.d 2 1 x) = 0 := congrArg (fun φ => φ.hom x) this
    rw [h2, map_zero]
  -- main argument
  rw [← LinearMap.ker_eq_bot (f := (M ◁ ι).hom), eq_bot_iff]
  intro z hz
  rw [LinearMap.mem_ker] at hz
  rw [Submodule.mem_bot]
  -- for each `r`, `c (ι r) = d₁ y_r`
  have hcr : ∀ r : R, ∃ y, P.complex.d 1 0 y = c (ι r) := by
    intro r
    apply hex0
    have : (P.π.f 0) (c (ι r)) = ε (ι r) := by rw [← hc]; rfl
    rw [this]
    exact (hex _).2 ⟨r, rfl⟩
  choose yr hyr using hcr
  -- `z = (M ⊗ g)(Y) + (M ⊗ h)((M ⊗ ι) z)` with `(M ⊗ d₁) Y = (M ⊗ c)((M ⊗ ι) z)`
  -- Define `Y` by induction on `z`.
  have key : ∀ z : (M ⊗ R : ModuleCat.{0} ℤ), ∃ Y : (M ⊗ P.complex.X 1 : ModuleCat.{0} ℤ),
      (M ◁ P.complex.d 1 0) Y = (M ◁ c) ((M ◁ ι) z) ∧ z = (M ◁ g) Y + (M ◁ h) ((M ◁ ι) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul m r =>
      refine ⟨m ⊗ₜ yr r, ?_, ?_⟩
      · simp only [ModuleCat.MonoidalCategory.whiskerLeft_apply, hyr]
      · simp only [ModuleCat.MonoidalCategory.whiskerLeft_apply]
        rw [← TensorProduct.tmul_add]
        congr 1
        apply hι
        rw [map_add, hg, hh, hyr]
        abel
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨Y₁, e₁, f₁⟩ := h₁
      obtain ⟨Y₂, e₂, f₂⟩ := h₂
      refine ⟨Y₁ + Y₂, by rw [map_add, map_add, map_add, e₁, e₂], ?_⟩
      rw [map_add, map_add, map_add]
      conv_lhs => rw [f₁, f₂]
      abel
  obtain ⟨Y, hY1, hY2⟩ := key z
  have hz' : (M ◁ ι) z = 0 := hz
  rw [hz', map_zero] at hY1
  obtain ⟨X, hX⟩ := tensor_resolution_exact_one P hTor Y hY1
  rw [hY2, hz', map_zero, add_zero, ← hX]
  have : (M ◁ P.complex.d 2 1) ≫ (M ◁ g) = 0 := by rw [← whiskerLeft_comp, hgd]; simp
  exact congrArg (fun φ => φ.hom X) this

end NumberFieldKB.MilneCFT
