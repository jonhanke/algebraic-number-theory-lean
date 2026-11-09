import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Delta

/-!
# Milne, *Class Field Theory*, Chapter II: uniqueness of (co)homological $\delta$-functors

Unconditional proofs of `RemarkA_12`, `Remark1_10` and `Remark2_5` (Grothendieck's universal $\delta$-functor
argument). For a cohomological $\delta$-functor $T$ which is effaceable and an object $X$, embed
$X \hookrightarrow I(X)$ with cokernel $Q(X)$; then $T^{n+1}(X)$ is the cokernel of $T^n(I(X)) \to T^n(Q(X))$.
This lets one build $\varphi_{n+1}$ from $\varphi_n$, and prove it natural, compatible with all connecting maps, and
unique. The homological case is the dual argument (projective cover with kernel).
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

section Generic

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- Two exact short complexes with epimorphic `g` and compatible isomorphisms on the first two terms have
isomorphic third terms, compatibly. -/
lemma exists_iso_cokernel (S₁ S₂ : ShortComplex D) [Epi S₁.g] [Epi S₂.g] (h₁ : S₁.Exact) (h₂ : S₂.Exact)
    (a : S₁.X₁ ≅ S₂.X₁) (b : S₁.X₂ ≅ S₂.X₂) (hab : a.hom ≫ S₂.f = S₁.f ≫ b.hom) :
    ∃ c : S₁.X₃ ≅ S₂.X₃, S₁.g ≫ c.hom = b.hom ≫ S₂.g := by
  have hab' : S₂.f ≫ b.inv = a.inv ≫ S₁.f := by
    calc S₂.f ≫ b.inv = a.inv ≫ a.hom ≫ S₂.f ≫ b.inv := by simp
      _ = a.inv ≫ S₁.f := by rw [← Category.assoc a.hom, hab]; simp
  have k₁ : S₁.f ≫ b.hom ≫ S₂.g = 0 := by rw [← Category.assoc, ← hab]; simp
  have k₂ : S₂.f ≫ b.inv ≫ S₁.g = 0 := by rw [← Category.assoc, hab']; simp
  refine ⟨⟨h₁.desc (b.hom ≫ S₂.g) k₁, h₂.desc (b.inv ≫ S₁.g) k₂, ?_, ?_⟩, ?_⟩
  · rw [← cancel_epi S₁.g]; simp
  · rw [← cancel_epi S₂.g]; simp
  · simp

/-- Dual of `exists_iso_cokernel`: exact short complexes with monomorphic `f`. -/
lemma exists_iso_kernel (S₁ S₂ : ShortComplex D) [Mono S₁.f] [Mono S₂.f] (h₁ : S₁.Exact) (h₂ : S₂.Exact)
    (b : S₁.X₂ ≅ S₂.X₂) (c : S₁.X₃ ≅ S₂.X₃) (hbc : S₁.g ≫ c.hom = b.hom ≫ S₂.g) :
    ∃ a : S₁.X₁ ≅ S₂.X₁, a.hom ≫ S₂.f = S₁.f ≫ b.hom := by
  have hbc' : b.inv ≫ S₁.g = S₂.g ≫ c.inv := by
    calc b.inv ≫ S₁.g = b.inv ≫ S₁.g ≫ c.hom ≫ c.inv := by simp
      _ = S₂.g ≫ c.inv := by rw [← Category.assoc S₁.g, hbc]; simp
  have k₁ : (S₁.f ≫ b.hom) ≫ S₂.g = 0 := by rw [Category.assoc, ← hbc]; simp
  have k₂ : (S₂.f ≫ b.inv) ≫ S₁.g = 0 := by rw [Category.assoc, hbc']; simp
  refine ⟨⟨h₂.lift (S₁.f ≫ b.hom) k₁, h₁.lift (S₂.f ≫ b.inv) k₂, ?_, ?_⟩, ?_⟩
  · rw [← cancel_mono S₁.f]; simp
  · rw [← cancel_mono S₂.f]; simp
  · simp

end Generic

section Cohom

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- The short exact sequence $0 \to X \to I(X) \to Q(X) \to 0$ with $I(X)$ injective. -/
@[reducible] noncomputable def injSeq (X : C) : ShortComplex C :=
  ShortComplex.mk (Injective.ι X) (cokernel.π (Injective.ι X)) (cokernel.condition _)

lemma injSeq_shortExact (X : C) : (injSeq X).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (Injective.ι X))
    (inferInstanceAs (Mono (Injective.ι X))) (inferInstanceAs (Epi (cokernel.π (Injective.ι X))))

/-- Any short exact sequence maps to `injSeq Y` extending a given map out of the first term. -/
noncomputable def toInjSeq (S : ShortComplex C) (hS : S.ShortExact) (Y : C) (f : S.X₁ ⟶ Y) :
    S ⟶ injSeq Y :=
  haveI := hS.mono_f
  haveI := hS.epi_g
  { τ₁ := f
    τ₂ := Injective.factorThru (f ≫ Injective.ι Y) S.f
    τ₃ := hS.exact.desc (Injective.factorThru (f ≫ Injective.ι Y) S.f ≫ cokernel.π (Injective.ι Y)) (by
      rw [← Category.assoc, Injective.comp_factorThru]; simp)
    comm₁₂ := by simp [injSeq]
    comm₂₃ := by simp [injSeq] }

@[simp] lemma toInjSeq_τ₁ (S : ShortComplex C) (hS : S.ShortExact) (Y : C) (f : S.X₁ ⟶ Y) :
    (toInjSeq S hS Y f).τ₁ = f := rfl

variable (T₁ T₂ : CohomDeltaFunctor C D)

lemma CohomDeltaFunctor.epi_δ_injSeq (T : CohomDeltaFunctor C D) (hT : T.Effaceable) (X : C) (n : ℕ) :
    Epi (T.δ (injSeq X) (injSeq_shortExact X) n) := by
  have h := T.exact₁ _ (injSeq_shortExact X) n
  have hz : IsZero ((T.T (n + 1)).obj (injSeq X).X₂) :=
    hT (Injective.under X) inferInstance (n + 1) n.succ_pos
  exact (ShortComplex.exact_iff_epi _ (hz.eq_of_tgt _ _)).1 h

lemma CohomDeltaFunctor.exists_succ_iso (h₁ : T₁.Effaceable) (h₂ : T₂.Effaceable) {n : ℕ}
    (α : T₁.T n ≅ T₂.T n) (X : C) :
    ∃ c : (T₁.T (n + 1)).obj X ≅ (T₂.T (n + 1)).obj X,
      T₁.δ (injSeq X) (injSeq_shortExact X) n ≫ c.hom =
        α.hom.app (injSeq X).X₃ ≫ T₂.δ (injSeq X) (injSeq_shortExact X) n := by
  haveI := T₁.epi_δ_injSeq h₁ X n
  haveI := T₂.epi_δ_injSeq h₂ X n
  exact exists_iso_cokernel (ShortComplex.mk _ _ (T₁.comp_δ _ (injSeq_shortExact X) n))
    (ShortComplex.mk _ _ (T₂.comp_δ _ (injSeq_shortExact X) n))
    (T₁.exact₃ _ (injSeq_shortExact X) n) (T₂.exact₃ _ (injSeq_shortExact X) n)
    (α.app _) (α.app _) (α.hom.naturality _).symm

/-- The isomorphism in degree `n + 1` induced from one in degree `n`. -/
noncomputable def CohomDeltaFunctor.succIso (h₁ : T₁.Effaceable) (h₂ : T₂.Effaceable) {n : ℕ}
    (α : T₁.T n ≅ T₂.T n) : T₁.T (n + 1) ≅ T₂.T (n + 1) :=
  NatIso.ofComponents (fun X => (T₁.exists_succ_iso T₂ h₁ h₂ α X).choose) (by
    intro X Y f
    haveI := T₁.epi_δ_injSeq h₁ X n
    rw [← cancel_epi (T₁.δ (injSeq X) (injSeq_shortExact X) n)]
    let F := toInjSeq (injSeq X) (injSeq_shortExact X) Y f
    have e1 : T₁.δ (injSeq X) (injSeq_shortExact X) n ≫ (T₁.T (n + 1)).map f =
        (T₁.T n).map F.τ₃ ≫ T₁.δ (injSeq Y) (injSeq_shortExact Y) n :=
      T₁.naturality _ _ (injSeq_shortExact X) (injSeq_shortExact Y) F n
    have e2 : T₂.δ (injSeq X) (injSeq_shortExact X) n ≫ (T₂.T (n + 1)).map f =
        (T₂.T n).map F.τ₃ ≫ T₂.δ (injSeq Y) (injSeq_shortExact Y) n :=
      T₂.naturality _ _ (injSeq_shortExact X) (injSeq_shortExact Y) F n
    have sX := (T₁.exists_succ_iso T₂ h₁ h₂ α X).choose_spec
    have sY := (T₁.exists_succ_iso T₂ h₁ h₂ α Y).choose_spec
    calc T₁.δ (injSeq X) (injSeq_shortExact X) n ≫ (T₁.T (n + 1)).map f ≫
          (T₁.exists_succ_iso T₂ h₁ h₂ α Y).choose.hom
        = (T₁.T n).map F.τ₃ ≫ T₁.δ (injSeq Y) (injSeq_shortExact Y) n ≫
          (T₁.exists_succ_iso T₂ h₁ h₂ α Y).choose.hom := by rw [← Category.assoc, e1, Category.assoc]
      _ = (T₁.T n).map F.τ₃ ≫ α.hom.app (injSeq Y).X₃ ≫ T₂.δ (injSeq Y) (injSeq_shortExact Y) n := by
          rw [sY]
      _ = α.hom.app (injSeq X).X₃ ≫ (T₂.T n).map F.τ₃ ≫ T₂.δ (injSeq Y) (injSeq_shortExact Y) n := by
          rw [← Category.assoc, α.hom.naturality, Category.assoc]
      _ = α.hom.app (injSeq X).X₃ ≫ T₂.δ (injSeq X) (injSeq_shortExact X) n ≫ (T₂.T (n + 1)).map f := by
          rw [e2]
      _ = T₁.δ (injSeq X) (injSeq_shortExact X) n ≫ (T₁.exists_succ_iso T₂ h₁ h₂ α X).choose.hom ≫
          (T₂.T (n + 1)).map f := by rw [← Category.assoc (T₁.δ _ _ _), sX, Category.assoc])

lemma CohomDeltaFunctor.succIso_spec (h₁ : T₁.Effaceable) (h₂ : T₂.Effaceable) {n : ℕ}
    (α : T₁.T n ≅ T₂.T n) (X : C) :
    T₁.δ (injSeq X) (injSeq_shortExact X) n ≫ (T₁.succIso T₂ h₁ h₂ α).hom.app X =
      α.hom.app (injSeq X).X₃ ≫ T₂.δ (injSeq X) (injSeq_shortExact X) n :=
  (T₁.exists_succ_iso T₂ h₁ h₂ α X).choose_spec

/-- The sequence of isomorphisms, built by recursion from the one in degree `0`. -/
noncomputable def CohomDeltaFunctor.isoSeq (h₁ : T₁.Effaceable) (h₂ : T₂.Effaceable)
    (φ₀ : T₁.T 0 ≅ T₂.T 0) : ∀ n, T₁.T n ≅ T₂.T n
  | 0 => φ₀
  | n + 1 => T₁.succIso T₂ h₁ h₂ (CohomDeltaFunctor.isoSeq h₁ h₂ φ₀ n)

lemma CohomDeltaFunctor.isoSeq_isDeltaIso (h₁ : T₁.Effaceable) (h₂ : T₂.Effaceable)
    (φ₀ : T₁.T 0 ≅ T₂.T 0) : T₁.IsDeltaIso T₂ (T₁.isoSeq T₂ h₁ h₂ φ₀) := by
  intro S hS n
  haveI := hS.epi_g
  let F := toInjSeq S hS S.X₁ (𝟙 _)
  have e1 : T₁.δ S hS n = (T₁.T n).map F.τ₃ ≫ T₁.δ (injSeq S.X₁) (injSeq_shortExact S.X₁) n := by
    simpa [F] using T₁.naturality S _ hS (injSeq_shortExact S.X₁) F n
  have e2 : T₂.δ S hS n = (T₂.T n).map F.τ₃ ≫ T₂.δ (injSeq S.X₁) (injSeq_shortExact S.X₁) n := by
    simpa [F] using T₂.naturality S _ hS (injSeq_shortExact S.X₁) F n
  have sp := T₁.succIso_spec T₂ h₁ h₂ (T₁.isoSeq T₂ h₁ h₂ φ₀ n) S.X₁
  calc T₁.δ S hS n ≫ (T₁.isoSeq T₂ h₁ h₂ φ₀ (n + 1)).hom.app S.X₁
      = (T₁.T n).map F.τ₃ ≫ T₁.δ (injSeq S.X₁) (injSeq_shortExact S.X₁) n ≫
          (T₁.isoSeq T₂ h₁ h₂ φ₀ (n + 1)).hom.app S.X₁ := by rw [e1, Category.assoc]
    _ = (T₁.T n).map F.τ₃ ≫ (T₁.isoSeq T₂ h₁ h₂ φ₀ n).hom.app (injSeq S.X₁).X₃ ≫
          T₂.δ (injSeq S.X₁) (injSeq_shortExact S.X₁) n := by rw [← sp]; rfl
    _ = (T₁.isoSeq T₂ h₁ h₂ φ₀ n).hom.app S.X₃ ≫ (T₂.T n).map F.τ₃ ≫
          T₂.δ (injSeq S.X₁) (injSeq_shortExact S.X₁) n := by
        rw [← Category.assoc, (T₁.isoSeq T₂ h₁ h₂ φ₀ n).hom.naturality, Category.assoc]
    _ = _ := by rw [← e2]

lemma CohomDeltaFunctor.isoSeq_unique (h₁ : T₁.Effaceable) (h₂ : T₂.Effaceable)
    (φ₀ : T₁.T 0 ≅ T₂.T 0) (ψ : ∀ n, T₁.T n ≅ T₂.T n) (h0 : ψ 0 = φ₀) (hψ : T₁.IsDeltaIso T₂ ψ) :
    ψ = T₁.isoSeq T₂ h₁ h₂ φ₀ := by
  funext n
  induction n with
  | zero => exact h0
  | succ n ih =>
    refine Iso.ext (NatTrans.ext (funext fun X => ?_))
    haveI := T₁.epi_δ_injSeq h₁ X n
    rw [← cancel_epi (T₁.δ (injSeq X) (injSeq_shortExact X) n), hψ _ _ n, ih]
    exact (T₁.succIso_spec T₂ h₁ h₂ (T₁.isoSeq T₂ h₁ h₂ φ₀ n) X).symm

end Cohom

/-- **Remark A.12** (p. 95), proved: universal property of right derived functors / effaceable
cohomological $\delta$-functors. Grothendieck's argument: $T^{n+1}(X)$ is the cokernel of
$T^n(I(X)) \to T^n(Q(X))$ for an embedding $X \hookrightarrow I(X)$ into an injective. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark A.12, p. 95"]
theorem remarkA_12 : RemarkA_12 :=
  ⟨fun _ _ _ _ _ _ _ _ T₁ T₂ e₁ e₂ h₁ h₂ =>
    ⟨T₁.isoSeq T₂ h₁ h₂ (e₁ ≪≫ e₂.symm), ⟨rfl, T₁.isoSeq_isDeltaIso T₂ h₁ h₂ _⟩,
      fun ψ hψ => T₁.isoSeq_unique T₂ h₁ h₂ _ ψ hψ.1 hψ.2⟩⟩

/-- **Remark 1.10** (p. 61), proved: `Remark1_10` is the case `Rep ℤ G` of `RemarkA_12`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.10, p. 61"]
theorem remark1_10 : Remark1_10 := remark_1_10_of_remarkA_12 remarkA_12

section Hom

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughProjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- The short exact sequence $0 \to K(X) \to P(X) \to X \to 0$ with $P(X)$ projective. -/
@[reducible] noncomputable def projSeq (X : C) : ShortComplex C :=
  ShortComplex.mk (kernel.ι (Projective.π X)) (Projective.π X) (kernel.condition _)

lemma projSeq_shortExact (X : C) : (projSeq X).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel (Projective.π X))
    (inferInstanceAs (Mono (kernel.ι (Projective.π X)))) (inferInstanceAs (Epi (Projective.π X)))

/-- `projSeq Y` maps to any short exact sequence, extending a given map into the last term. -/
noncomputable def fromProjSeq (S : ShortComplex C) (hS : S.ShortExact) (Y : C) (f : Y ⟶ S.X₃) :
    projSeq Y ⟶ S :=
  haveI := hS.mono_f
  haveI := hS.epi_g
  { τ₁ := hS.exact.lift (kernel.ι (Projective.π Y) ≫ Projective.factorThru (Projective.π Y ≫ f) S.g) (by
      rw [Category.assoc, Projective.factorThru_comp]; simp)
    τ₂ := Projective.factorThru (Projective.π Y ≫ f) S.g
    τ₃ := f
    comm₁₂ := by simp [projSeq]
    comm₂₃ := by simp [projSeq] }

@[simp] lemma fromProjSeq_τ₃ (S : ShortComplex C) (hS : S.ShortExact) (Y : C) (f : Y ⟶ S.X₃) :
    (fromProjSeq S hS Y f).τ₃ = f := rfl

variable (T₁ T₂ : HomDeltaFunctor C D)

lemma HomDeltaFunctor.mono_δ_projSeq (T : HomDeltaFunctor C D) (hT : T.Coeffaceable) (X : C) (n : ℕ) :
    Mono (T.δ (projSeq X) (projSeq_shortExact X) n) := by
  have h := T.exact₃ _ (projSeq_shortExact X) n
  have hz : IsZero ((T.T (n + 1)).obj (projSeq X).X₂) :=
    hT (Projective.over X) inferInstance (n + 1) n.succ_pos
  exact (ShortComplex.exact_iff_mono _ (hz.eq_of_src _ _)).1 h

lemma HomDeltaFunctor.exists_succ_iso (h₁ : T₁.Coeffaceable) (h₂ : T₂.Coeffaceable) {n : ℕ}
    (α : T₁.T n ≅ T₂.T n) (X : C) :
    ∃ c : (T₁.T (n + 1)).obj X ≅ (T₂.T (n + 1)).obj X,
      c.hom ≫ T₂.δ (projSeq X) (projSeq_shortExact X) n =
        T₁.δ (projSeq X) (projSeq_shortExact X) n ≫ α.hom.app (projSeq X).X₁ := by
  haveI := T₁.mono_δ_projSeq h₁ X n
  haveI := T₂.mono_δ_projSeq h₂ X n
  exact exists_iso_kernel (ShortComplex.mk _ _ (T₁.δ_comp _ (projSeq_shortExact X) n))
    (ShortComplex.mk _ _ (T₂.δ_comp _ (projSeq_shortExact X) n))
    (T₁.exact₁ _ (projSeq_shortExact X) n) (T₂.exact₁ _ (projSeq_shortExact X) n)
    (α.app _) (α.app _) (α.hom.naturality _)

/-- The isomorphism in degree `n + 1` induced from one in degree `n`. -/
noncomputable def HomDeltaFunctor.succIso (h₁ : T₁.Coeffaceable) (h₂ : T₂.Coeffaceable) {n : ℕ}
    (α : T₁.T n ≅ T₂.T n) : T₁.T (n + 1) ≅ T₂.T (n + 1) :=
  NatIso.ofComponents (fun X => (T₁.exists_succ_iso T₂ h₁ h₂ α X).choose) (by
    intro X Y f
    haveI := T₂.mono_δ_projSeq h₂ Y n
    rw [← cancel_mono (T₂.δ (projSeq Y) (projSeq_shortExact Y) n)]
    let F := fromProjSeq (projSeq Y) (projSeq_shortExact Y) X f
    have e1 : T₁.δ (projSeq X) (projSeq_shortExact X) n ≫ (T₁.T n).map F.τ₁ =
        (T₁.T (n + 1)).map f ≫ T₁.δ (projSeq Y) (projSeq_shortExact Y) n :=
      T₁.naturality _ _ (projSeq_shortExact X) (projSeq_shortExact Y) F n
    have e2 : T₂.δ (projSeq X) (projSeq_shortExact X) n ≫ (T₂.T n).map F.τ₁ =
        (T₂.T (n + 1)).map f ≫ T₂.δ (projSeq Y) (projSeq_shortExact Y) n :=
      T₂.naturality _ _ (projSeq_shortExact X) (projSeq_shortExact Y) F n
    have sX := (T₁.exists_succ_iso T₂ h₁ h₂ α X).choose_spec
    have sY := (T₁.exists_succ_iso T₂ h₁ h₂ α Y).choose_spec
    calc ((T₁.T (n + 1)).map f ≫ (T₁.exists_succ_iso T₂ h₁ h₂ α Y).choose.hom) ≫
          T₂.δ (projSeq Y) (projSeq_shortExact Y) n
        = (T₁.T (n + 1)).map f ≫ T₁.δ (projSeq Y) (projSeq_shortExact Y) n ≫
          α.hom.app (projSeq Y).X₁ := by rw [Category.assoc, sY]
      _ = T₁.δ (projSeq X) (projSeq_shortExact X) n ≫ (T₁.T n).map F.τ₁ ≫ α.hom.app (projSeq Y).X₁ := by
          rw [← Category.assoc, ← e1, Category.assoc]
      _ = T₁.δ (projSeq X) (projSeq_shortExact X) n ≫ α.hom.app (projSeq X).X₁ ≫ (T₂.T n).map F.τ₁ := by
          rw [α.hom.naturality]
      _ = (T₁.exists_succ_iso T₂ h₁ h₂ α X).choose.hom ≫ T₂.δ (projSeq X) (projSeq_shortExact X) n ≫
          (T₂.T n).map F.τ₁ := by rw [← Category.assoc (T₁.exists_succ_iso T₂ h₁ h₂ α X).choose.hom, sX, Category.assoc]
      _ = ((T₁.exists_succ_iso T₂ h₁ h₂ α X).choose.hom ≫ (T₂.T (n + 1)).map f) ≫
          T₂.δ (projSeq Y) (projSeq_shortExact Y) n := by rw [e2, Category.assoc])

lemma HomDeltaFunctor.succIso_spec (h₁ : T₁.Coeffaceable) (h₂ : T₂.Coeffaceable) {n : ℕ}
    (α : T₁.T n ≅ T₂.T n) (X : C) :
    (T₁.succIso T₂ h₁ h₂ α).hom.app X ≫ T₂.δ (projSeq X) (projSeq_shortExact X) n =
      T₁.δ (projSeq X) (projSeq_shortExact X) n ≫ α.hom.app (projSeq X).X₁ :=
  (T₁.exists_succ_iso T₂ h₁ h₂ α X).choose_spec

/-- The sequence of isomorphisms, built by recursion from the one in degree `0`. -/
noncomputable def HomDeltaFunctor.isoSeq (h₁ : T₁.Coeffaceable) (h₂ : T₂.Coeffaceable)
    (φ₀ : T₁.T 0 ≅ T₂.T 0) : ∀ n, T₁.T n ≅ T₂.T n
  | 0 => φ₀
  | n + 1 => T₁.succIso T₂ h₁ h₂ (HomDeltaFunctor.isoSeq h₁ h₂ φ₀ n)

lemma HomDeltaFunctor.isoSeq_isDeltaIso (h₁ : T₁.Coeffaceable) (h₂ : T₂.Coeffaceable)
    (φ₀ : T₁.T 0 ≅ T₂.T 0) : T₁.IsDeltaIso T₂ (T₁.isoSeq T₂ h₁ h₂ φ₀) := by
  intro S hS n
  haveI := hS.mono_f
  let F := fromProjSeq S hS S.X₃ (𝟙 _)
  have e1 : T₁.δ S hS n = T₁.δ (projSeq S.X₃) (projSeq_shortExact S.X₃) n ≫ (T₁.T n).map F.τ₁ := by
    simpa [F] using (T₁.naturality _ S (projSeq_shortExact S.X₃) hS F n).symm
  have e2 : T₂.δ S hS n = T₂.δ (projSeq S.X₃) (projSeq_shortExact S.X₃) n ≫ (T₂.T n).map F.τ₁ := by
    simpa [F] using (T₂.naturality _ S (projSeq_shortExact S.X₃) hS F n).symm
  have sp := T₁.succIso_spec T₂ h₁ h₂ (T₁.isoSeq T₂ h₁ h₂ φ₀ n) S.X₃
  calc T₁.δ S hS n ≫ (T₁.isoSeq T₂ h₁ h₂ φ₀ n).hom.app S.X₁
      = T₁.δ (projSeq S.X₃) (projSeq_shortExact S.X₃) n ≫ (T₁.T n).map F.τ₁ ≫
          (T₁.isoSeq T₂ h₁ h₂ φ₀ n).hom.app S.X₁ := by rw [e1, Category.assoc]
    _ = T₁.δ (projSeq S.X₃) (projSeq_shortExact S.X₃) n ≫
          (T₁.isoSeq T₂ h₁ h₂ φ₀ n).hom.app (projSeq S.X₃).X₁ ≫ (T₂.T n).map F.τ₁ := by
        rw [(T₁.isoSeq T₂ h₁ h₂ φ₀ n).hom.naturality]
    _ = (T₁.isoSeq T₂ h₁ h₂ φ₀ (n + 1)).hom.app S.X₃ ≫
          T₂.δ (projSeq S.X₃) (projSeq_shortExact S.X₃) n ≫ (T₂.T n).map F.τ₁ := by
        rw [← Category.assoc, ← sp, Category.assoc]; rfl
    _ = _ := by rw [← e2]

lemma HomDeltaFunctor.isoSeq_unique (h₁ : T₁.Coeffaceable) (h₂ : T₂.Coeffaceable)
    (φ₀ : T₁.T 0 ≅ T₂.T 0) (ψ : ∀ n, T₁.T n ≅ T₂.T n) (h0 : ψ 0 = φ₀) (hψ : T₁.IsDeltaIso T₂ ψ) :
    ψ = T₁.isoSeq T₂ h₁ h₂ φ₀ := by
  funext n
  induction n with
  | zero => exact h0
  | succ n ih =>
    refine Iso.ext (NatTrans.ext (funext fun X => ?_))
    haveI := T₂.mono_δ_projSeq h₂ X n
    rw [← cancel_mono (T₂.δ (projSeq X) (projSeq_shortExact X) n), ← hψ (projSeq X) (projSeq_shortExact X) n, ih]
    exact (T₁.succIso_spec T₂ h₁ h₂ (T₁.isoSeq T₂ h₁ h₂ φ₀ n) X).symm

end Hom

/-- **Remark 2.5** (p. 67), proved: the dual argument for homological $\delta$-functors vanishing on
projectives in positive degrees, using `Rep ℤ G` having enough projectives. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 2.5, p. 67"]
theorem remark2_5 : Remark2_5 :=
  ⟨fun _ _ T₁ T₂ e₁ e₂ h₁ h₂ =>
    ⟨T₁.isoSeq T₂ h₁ h₂ (e₁ ≪≫ e₂.symm), ⟨rfl, T₁.isoSeq_isDeltaIso T₂ h₁ h₂ _⟩,
      fun ψ hψ => T₁.isoSeq_unique T₂ h₁ h₂ _ ψ hψ.1 hψ.2⟩⟩

end NumberFieldKB.MilneCFT
