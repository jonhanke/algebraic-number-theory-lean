import Mathlib.Algebra.Exact.Basic
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import QuadFormsKB.Citation

/-!
# Milne, *Class Field Theory*, Chapter II, Appendix A: some homological algebra

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

The appendix items that are in Mathlib are cited in `Ch2Cite.lean`. This file has the ones that are not:
* Lemma A.2 (the kernel-cokernel lemma for a pair of homomorphisms of abelian groups);
* Lemmas A.9 and A.10 in Milne's generality: the source $M \to I^\bullet$ is only a resolution (an exact
  complex), not an injective one. Mathlib's `InjectiveResolution.desc` and `InjectiveResolution.descHomotopy`
  need both resolutions to be injective.
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Limits

/-! ## Lemma A.2: the kernel-cokernel lemma -/

section KernelCokernel

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C)

/-- $\operatorname{Ker} f \to \operatorname{Ker}(g \circ f)$, the inclusion. -/
def kc₁ : LinearMap.ker f →ₗ[ℤ] LinearMap.ker (g ∘ₗ f) :=
  Submodule.inclusion (LinearMap.ker_le_ker_comp f g)

/-- $\operatorname{Ker}(g \circ f) \to \operatorname{Ker} g$, induced by $f$. -/
def kc₂ : LinearMap.ker (g ∘ₗ f) →ₗ[ℤ] LinearMap.ker g :=
  f.restrict (fun _ hx => hx)

/-- $\operatorname{Ker} g \to \operatorname{Coker} f$, the inclusion followed by the quotient map. -/
def kc₃ : LinearMap.ker g →ₗ[ℤ] B ⧸ LinearMap.range f :=
  (LinearMap.range f).mkQ ∘ₗ (LinearMap.ker g).subtype

/-- $\operatorname{Coker} f \to \operatorname{Coker}(g \circ f)$, induced by $g$. -/
def kc₄ : B ⧸ LinearMap.range f →ₗ[ℤ] C ⧸ LinearMap.range (g ∘ₗ f) :=
  (LinearMap.range f).mapQ (LinearMap.range (g ∘ₗ f)) g (by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl⟩)

/-- $\operatorname{Coker}(g \circ f) \to \operatorname{Coker} g$, induced by the identity of $C$. -/
def kc₅ : C ⧸ LinearMap.range (g ∘ₗ f) →ₗ[ℤ] C ⧸ LinearMap.range g :=
  Submodule.factor (LinearMap.range_comp_le_range f g)

theorem kc₁_injective : Function.Injective (kc₁ f g) :=
  Submodule.inclusion_injective _

theorem kc_exact₁₂ : Function.Exact (kc₁ f g) (kc₂ f g) := by
  intro x
  constructor
  · intro h
    have h2 : f x.1 = 0 := congrArg Subtype.val h
    exact ⟨⟨x.1, h2⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact y.2

theorem kc_exact₂₃ : Function.Exact (kc₂ f g) (kc₃ f g) := by
  intro y
  constructor
  · intro h
    have h' : (y : B) ∈ LinearMap.range f := by
      simpa [kc₃, Submodule.Quotient.mk_eq_zero] using h
    obtain ⟨a, ha⟩ := h'
    refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
    have := y.2
    rw [LinearMap.mem_ker] at this ⊢
    rw [← ha] at this
    exact this
  · rintro ⟨x, rfl⟩
    simp only [kc₃, kc₂, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x.1, rfl⟩

theorem kc_exact₃₄ : Function.Exact (kc₃ f g) (kc₄ f g) := by
  intro b
  induction b using Submodule.Quotient.induction_on with
  | H b =>
  constructor
  · intro h
    have h' : g b ∈ LinearMap.range (g ∘ₗ f) := by
      simpa [kc₄, Submodule.Quotient.mk_eq_zero] using h
    obtain ⟨a, ha⟩ := h'
    refine ⟨⟨b - f a, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, map_sub]
      simp only [LinearMap.comp_apply] at ha
      rw [ha, sub_self]
    · simp only [kc₃, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simp
  · rintro ⟨y, hy⟩
    simp only [kc₃, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply] at hy
    rw [Submodule.Quotient.eq] at hy
    obtain ⟨a, ha⟩ := hy
    have hgy := y.2
    rw [LinearMap.mem_ker] at hgy
    simp only [kc₄, Submodule.mapQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨-a, ?_⟩
    have : b = y - f a := by rw [ha]; abel
    simp only [LinearMap.comp_apply]
    rw [this]
    simp [hgy]

theorem kc_exact₄₅ : Function.Exact (kc₄ f g) (kc₅ f g) := by
  intro c
  induction c using Submodule.Quotient.induction_on with
  | H c =>
  constructor
  · intro h
    have h' : c ∈ LinearMap.range g := by
      simpa [kc₅, Submodule.Quotient.mk_eq_zero] using h
    obtain ⟨b, rfl⟩ := h'
    exact ⟨Submodule.Quotient.mk b, by simp [kc₄]⟩
  · rintro ⟨b, hb⟩
    induction b using Submodule.Quotient.induction_on with
    | H b =>
    simp only [kc₄, Submodule.mapQ_apply] at hb
    rw [← hb]
    show Submodule.Quotient.mk (p := LinearMap.range g) (g b) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨b, rfl⟩

theorem kc₅_surjective : Function.Surjective (kc₅ f g) := by
  intro c
  induction c using Submodule.Quotient.induction_on with
  | H c => exact ⟨Submodule.Quotient.mk c, by simp [kc₅]⟩

/-- **Lemma A.2 (kernel-cokernel lemma)** (p. 89). A pair of homomorphisms $A \xrightarrow{f} B \xrightarrow{g} C$
of abelian groups gives rise to an exact sequence
$0 \to \operatorname{Ker} f \to \operatorname{Ker}(g \circ f) \to \operatorname{Ker} g \to \operatorname{Coker} f
\to \operatorname{Coker}(g \circ f) \to \operatorname{Coker} g \to 0$. -/
@[kb "milne2020cft" "v4.03, Ch. II, App. A, Lemma A.2, p. 89"]
theorem lemma_A_2 :
    Function.Injective (kc₁ f g) ∧ Function.Exact (kc₁ f g) (kc₂ f g) ∧
      Function.Exact (kc₂ f g) (kc₃ f g) ∧ Function.Exact (kc₃ f g) (kc₄ f g) ∧
      Function.Exact (kc₄ f g) (kc₅ f g) ∧ Function.Surjective (kc₅ f g) :=
  ⟨kc₁_injective f g, kc_exact₁₂ f g, kc_exact₂₃ f g, kc_exact₃₄ f g, kc_exact₄₅ f g,
    kc₅_surjective f g⟩

end KernelCokernel

/-! ## Lemmas A.9 and A.10 -/

section Resolutions

variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞]

/-- Exactness of `I.X n → I.X (n+1) → I.X (n+2)` from `I.ExactAt (n+1)`. -/
lemma resolution_exact_succ (I : CochainComplex 𝒞 ℕ) (hI : ∀ n : ℕ, I.ExactAt (n + 1)) (n : ℕ) :
    (ShortComplex.mk (I.d n (n + 1)) (I.d (n + 1) (n + 2))
      (I.d_comp_d n (n + 1) (n + 2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (hI n)

/-- **Lemma A.9** (p. 94). Let $M \to I^\bullet$ be a resolution of $M$ (the complex $I^\bullet$ is exact in
positive degrees and $M \to I^0 \to I^1$ is exact with $M \to I^0$ injective) and $N \to J^\bullet$ an injective
resolution of $N$. Every morphism $\alpha : M \to N$ extends to a morphism of complexes $I^\bullet \to J^\bullet$.
The resolution $M \to I^\bullet$ is encoded as a cochain complex `I` with a morphism `ι : M ⟶ I.X 0`. -/
@[kb "milne2020cft" "v4.03, Ch. II, App. A, Lemma A.9, p. 94"]
theorem lemma_A_9 {M N : 𝒞} (I : CochainComplex 𝒞 ℕ) (ι : M ⟶ I.X 0) [Mono ι]
    (hι : ι ≫ I.d 0 1 = 0) (h₀ : (ShortComplex.mk ι (I.d 0 1) hι).Exact)
    (hI : ∀ n : ℕ, I.ExactAt (n + 1)) (J : InjectiveResolution N) (α : M ⟶ N) :
    ∃ φ : I ⟶ J.cocomplex, ι ≫ φ.f 0 = α ≫ J.ι.f 0 := by
  have := J.injective
  let f0 : I.X 0 ⟶ J.cocomplex.X 0 := Injective.factorThru (α ≫ J.ι.f 0) ι
  have hf0 : ι ≫ f0 = α ≫ J.ι.f 0 := Injective.comp_factorThru _ _
  let f1 : I.X 1 ⟶ J.cocomplex.X 1 :=
    h₀.descToInjective (f0 ≫ J.cocomplex.d 0 1) (by
      dsimp
      rw [reassoc_of% hf0]
      exact (Category.assoc α (J.ι.f 0) (J.cocomplex.d 0 1)).trans
        ((congrArg (α ≫ ·) J.ι_f_zero_comp_complex_d).trans comp_zero))
  have hf1 : I.d 0 1 ≫ f1 = f0 ≫ J.cocomplex.d 0 1 :=
    h₀.comp_descToInjective (f0 ≫ J.cocomplex.d 0 1) _
  refine ⟨CochainComplex.mkHom _ _ f0 f1 hf1.symm ?_, hf0⟩
  intro n ⟨g, g', w⟩
  have ex := resolution_exact_succ I hI n
  refine ⟨ex.descToInjective (g' ≫ J.cocomplex.d (n + 1) (n + 2)) ?_, ?_⟩
  · dsimp
    rw [← reassoc_of% w, HomologicalComplex.d_comp_d, comp_zero]
  · exact (ex.comp_descToInjective _ _).symm

/-- **Lemma A.10** (p. 94). Let $M \to I^\bullet$ be a resolution of $M$ and $N \to J^\bullet$ an injective
resolution of $N$. Any two extensions $I^\bullet \to J^\bullet$ of the same morphism $M \to N$ are homotopic. -/
@[kb "milne2020cft" "v4.03, Ch. II, App. A, Lemma A.10, p. 94"]
theorem lemma_A_10 {M N : 𝒞} (I : CochainComplex 𝒞 ℕ) (ι : M ⟶ I.X 0) [Mono ι]
    (hι : ι ≫ I.d 0 1 = 0) (h₀ : (ShortComplex.mk ι (I.d 0 1) hι).Exact)
    (hI : ∀ n : ℕ, I.ExactAt (n + 1)) (J : InjectiveResolution N) (α : M ⟶ N)
    (φ ψ : I ⟶ J.cocomplex) (hφ : ι ≫ φ.f 0 = α ≫ J.ι.f 0) (hψ : ι ≫ ψ.f 0 = α ≫ J.ι.f 0) :
    Nonempty (Homotopy φ ψ) := by
  have := J.injective
  set e : I ⟶ J.cocomplex := φ - ψ with he
  have he0 : ι ≫ e.f 0 = 0 := by
    have : ι ≫ e.f 0 = ι ≫ φ.f 0 - ι ≫ ψ.f 0 := by
      rw [he, HomologicalComplex.sub_f_apply, Preadditive.comp_sub]
    rw [this, hφ, hψ, sub_self]
  let z0 : I.X 1 ⟶ J.cocomplex.X 0 := h₀.descToInjective (e.f 0) he0
  have hz0 : I.d 0 1 ≫ z0 = e.f 0 := h₀.comp_descToInjective _ _
  have ex0 := resolution_exact_succ I hI 0
  let z1 : I.X 2 ⟶ J.cocomplex.X 1 :=
    ex0.descToInjective (e.f 1 - z0 ≫ J.cocomplex.d 0 1) (by
      dsimp
      rw [Preadditive.comp_sub, reassoc_of% hz0, HomologicalComplex.Hom.comm, sub_self])
  have hz1 : I.d 1 2 ≫ z1 = e.f 1 - z0 ≫ J.cocomplex.d 0 1 := ex0.comp_descToInjective _ _
  have H : Homotopy e 0 :=
    Homotopy.mkCoinductive e z0 hz0.symm z1 (by rw [hz1]; abel) (by
      intro n ⟨g, g', w⟩
      have ex := resolution_exact_succ I hI (n + 1)
      refine ⟨ex.descToInjective (e.f (n + 2) - g' ≫ J.cocomplex.d (n + 1) (n + 2)) ?_, ?_⟩
      · dsimp
        rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
          Category.assoc, Category.assoc, HomologicalComplex.d_comp_d, comp_zero]
        rw [zero_add]
        exact sub_self _
      · rw [ex.comp_descToInjective]
        abel)
  exact ⟨Homotopy.equivSubZero.invFun H⟩

end Resolutions

end NumberFieldKB.MilneCFT
