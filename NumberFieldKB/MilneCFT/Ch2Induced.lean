import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import QuadFormsKB.Citation
import Mathlib.RepresentationTheory.Induced

/-!
# Milne, *Class Field Theory*, Chapter II §1: induced modules

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

Milne's $G$-modules are Mathlib's `Rep ℤ G`. For a subgroup $H$ and an $H$-module $N$, Milne's
$\operatorname{Ind}_H^G(N)$ (maps $\varphi : G \to N$ with $\varphi(hg) = h\varphi(g)$, and $(g\varphi)(x) = \varphi(xg)$)
is exactly Mathlib's coinduced module `Rep.coind H.subtype N` (not Mathlib's `Rep.ind`). For $H = 1$ an
$H$-module is an abelian group $M_0$ and $\operatorname{Ind}^G(M_0)$ is `indG M₀` below.
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology MonoidalCategory

variable {G : Type} [Group G]

/-- Milne's $\operatorname{Ind}^G(M_0)$ for an abelian group $M_0$: the $G$-module of all maps $G \to M_0$, with
$(g\varphi)(x) = \varphi(xg)$ (p. 59). It is Mathlib's coinduction `Rep.coind` from the trivial subgroup of the
trivial module $M_0$. -/
@[kb "milne2020cft" "v4.03, Ch. II, §1, definition of Ind^G(M_0), p. 59"]
noncomputable abbrev indG (G : Type) [Group G] (M₀ : Type) [AddCommGroup M₀] [Module ℤ M₀] : Rep ℤ G :=
  coind (⊥ : Subgroup G).subtype (Rep.trivial ℤ (⊥ : Subgroup G) M₀)

/-- **Induced $G$-module** (prose definition, p. 59): a $G$-module isomorphic to $\operatorname{Ind}^G(M_0)$ for
some abelian group $M_0$. -/
@[kb "milne2020cft" "v4.03, Ch. II, §1, definition of an induced G-module, p. 59"]
def IsInduced (M : Rep ℤ G) : Prop :=
  ∃ (M₀ : Type) (_ : AddCommGroup M₀) (_ : Module ℤ M₀), Nonempty (M ≅ indG G M₀)

/-- The element $a \otimes b$ of the tensor product $A \otimes B$ of $G$-modules (diagonal action). -/
noncomputable abbrev rtmul {A B : Rep ℤ G} (a : A) (b : B) : (A ⊗ B : Rep ℤ G) :=
  TensorProduct.tmul ℤ (M := A) (N := B) a b

/-! ## Corollary 1.12 -/

/-- **Corollary 1.12.** If $M$ is an induced $G$-module, then $H^r(G, M) = 0$ for $r > 0$. (From Shapiro's lemma,
Mathlib's `groupCohomology.coindIso`, and the vanishing for the trivial group.) -/
@[kb "milne2020cft" "v4.03, Ch. II, Cor. 1.12, p. 62"]
theorem cor_1_12 {M : Rep ℤ G} (hM : IsInduced M) (r : ℕ) (hr : 0 < r) :
    Limits.IsZero (groupCohomology M r) := by
  obtain ⟨M₀, _, _, ⟨e⟩⟩ := hM
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have h1 : Limits.IsZero (groupCohomology (Rep.trivial ℤ (⊥ : Subgroup G) M₀) (n + 1)) :=
    isZero_groupCohomology_succ_of_subsingleton _ n
  have h2 := h1.of_iso (groupCohomology.coindIso (Rep.trivial ℤ (⊥ : Subgroup G) M₀) (n + 1))
  exact h2.of_iso ((groupCohomology.functor ℤ G (n + 1)).mapIso e)

/-! ## The module $M_* = \operatorname{Ind}^G(M_0)$ and the sequence (15) -/

set_option backward.isDefEq.respectTransparency false in
/-- The $G$-homomorphism $M \to M_* = \operatorname{Ind}^G(M_0)$, $m \mapsto (g \mapsto gm)$, where $M_0$ is $M$
regarded as an abelian group (proof of Proposition 1.5 and Remark 1.13, p. 60, p. 62). -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.13, the map M → M_*, p. 62"]
noncomputable def toIndG (M : Rep ℤ G) : M ⟶ indG G M :=
  resCoindToHom (⊥ : Subgroup G).subtype M (Rep.trivial ℤ (⊥ : Subgroup G) M)
    (Rep.ofHom ⟨LinearMap.id, fun g => by
      have : g = 1 := Subtype.ext (Subgroup.mem_bot.1 g.2)
      subst this
      ext
      simp⟩)

set_option backward.isDefEq.respectTransparency false in
theorem toIndG_apply (M : Rep ℤ G) (m : M) (g : G) : ((toIndG M).hom m).1 g = M.ρ g m := rfl

set_option backward.isDefEq.respectTransparency false in
instance (M : Rep ℤ G) : Mono (toIndG M) := by
  rw [Rep.mono_iff_injective]
  intro m n h
  have := congrArg (fun f : indG G M => f.1 1) h
  rw [toIndG_apply, toIndG_apply] at this
  simpa using this

/-- Milne's $M^* = M_*/M$ (Remark 1.13, p. 62). -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.13, the module M^* = M_*/M, p. 62"]
noncomputable abbrev mStar (M : Rep ℤ G) : Rep ℤ G := Limits.cokernel (toIndG M)

/-- The exact sequence (15), $0 \to M \to M_* \to M^* \to 0$ (p. 62). -/
@[kb "milne2020cft" "v4.03, Ch. II, sequence (15), p. 62"]
noncomputable def seq15 (M : Rep ℤ G) : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (toIndG M) (Limits.cokernel.π _) (Limits.cokernel.condition _)

theorem seq15_shortExact (M : Rep ℤ G) : (seq15 M).ShortExact := by
  have : Mono (seq15 M).f := inferInstanceAs (Mono (toIndG M))
  have : Epi (seq15 M).g := inferInstanceAs (Epi (Limits.cokernel.π (toIndG M)))
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (toIndG M)) inferInstance inferInstance

/-! ## Remark 1.13: dimension shifting -/

/-- **Remark 1.13**, first part. Let $0 \to M \to J \to N \to 0$ be exact with $H^r(G, J) = 0$ for all $r > 0$.
Then $N^G \to H^1(G, M)$ is onto (so $0 \to M^G \to J^G \to N^G \to H^1(G,M) \to 0$ is exact; the left part is
Mathlib's long exact sequence), and the connecting maps $H^r(G, N) \to H^{r+1}(G, M)$, $r \ge 1$, are isomorphisms.
-/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.13, p. 62"]
theorem remark_1_13 {S : ShortComplex (Rep ℤ G)} (hS : S.ShortExact)
    (hJ : ∀ r : ℕ, 0 < r → Limits.IsZero (groupCohomology S.X₂ r)) :
    Epi (δ hS 0 1 rfl) ∧ ∀ r : ℕ, 1 ≤ r → IsIso (δ hS r (r + 1) rfl) :=
  ⟨epi_δ_of_isZero hS 0 (hJ 1 one_pos),
    fun r hr => isIso_δ_of_isZero hS r (hJ r hr) (hJ (r + 1) (by omega))⟩

/-- **Remark 1.13**, example: $H^r(G, M^*) \simeq H^{r+1}(G, M)$ for all $r \ge 1$, by the connecting map of (15). -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.13, p. 62–63"]
theorem remark_1_13_mStar (M : Rep ℤ G) (r : ℕ) (hr : 1 ≤ r) :
    IsIso (δ (seq15_shortExact M) r (r + 1) rfl) :=
  (remark_1_13 (seq15_shortExact M) fun r hr => cor_1_12 (M := indG G M) ⟨M, inferInstance, inferInstance,
    ⟨Iso.refl _⟩⟩ r hr).2 r hr

/-- One step of the dimension shifting: if `A₀ → A₁ → A₂` is exact at `A₁` and `A₂` is acyclic, then
`H^r(coker d) ≅ H^{r+1}(coker f)` for `r ≥ 1`. -/
theorem cokernel_step {A₀ A₁ A₂ : Rep ℤ G} (f : A₀ ⟶ A₁) (d : A₁ ⟶ A₂) (w : f ≫ d = 0)
    (h : (ShortComplex.mk f d w).Exact)
    (hJ : ∀ r : ℕ, 0 < r → Limits.IsZero (groupCohomology A₂ r)) (r : ℕ) (hr : 1 ≤ r) :
    Nonempty (groupCohomology (Limits.cokernel d) r ≅ groupCohomology (Limits.cokernel f) (r + 1)) := by
  let g' : Limits.cokernel f ⟶ A₂ := Limits.cokernel.desc f d w
  have hg' : Limits.cokernel.π f ≫ g' = d := Limits.cokernel.π_desc _ _ _
  have w' : g' ≫ Limits.cokernel.π d = 0 := by
    rw [← cancel_epi (Limits.cokernel.π f), ← Category.assoc, hg']
    simp
  let Sh : ShortComplex (Rep ℤ G) := ShortComplex.mk g' (Limits.cokernel.π d) w'
  have hmono : Mono g' := h.mono_cokernelDesc
  let φ : ShortComplex.mk d (Limits.cokernel.π d) (Limits.cokernel.condition d) ⟶ Sh :=
    { τ₁ := Limits.cokernel.π f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [Sh, hg']
      comm₂₃ := by simp [Sh] }
  have hex : Sh.Exact := by
    haveI : Epi φ.τ₁ := inferInstanceAs (Epi (Limits.cokernel.π f))
    haveI : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    haveI : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 _))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 (ShortComplex.exact_cokernel d)
  have hSh : Sh.ShortExact := ShortComplex.ShortExact.mk' hex hmono inferInstance
  haveI := (remark_1_13 hSh hJ).2 r hr
  exact ⟨asIso (δ hSh r (r + 1) rfl)⟩

/-- Auxiliary form of the iterated dimension shifting, peeling off the first map. -/
theorem remark_1_13_aux (s : ℕ) : ∀ (S : ComposableArrows (Rep ℤ G) (s + 2)) (_ : S.Exact)
    (_ : Epi (S.map' (s + 1) (s + 2)))
    (_ : ∀ i : ℕ, ∀ hi : 1 ≤ i ∧ i ≤ s + 1, ∀ r : ℕ, 0 < r →
      Limits.IsZero (groupCohomology (S.obj ⟨i, by omega⟩) r))
    (r : ℕ), 1 ≤ r →
    Nonempty (groupCohomology (S.obj ⟨s + 2, by omega⟩) r ≅
      groupCohomology (Limits.cokernel (S.map' 0 1)) (r + s)) := by
  induction s with
  | zero =>
    intro S hS hepi _ r hr
    have h0 := hS.exact 0
    have hmono := h0.mono_cokernelDesc
    set g' := Limits.cokernel.desc (S.sc hS.toIsComplex 0).f (S.sc hS.toIsComplex 0).g
      (S.sc hS.toIsComplex 0).zero with hg'
    have hfac : Limits.cokernel.π (S.sc hS.toIsComplex 0).f ≫ g' = S.map' 1 2 :=
      Limits.cokernel.π_desc _ _ _
    haveI : Epi g' := epi_of_epi_fac hfac
    haveI : IsIso g' := isIso_of_mono_of_epi g'
    exact ⟨(groupCohomology.functor ℤ G r).mapIso (asIso g').symm⟩
  | succ s ih =>
    intro S hS hepi hJ r hr
    have hδ : S.δ₀.Exact := hS.δ₀
    obtain ⟨e₁⟩ := ih S.δ₀ hδ hepi
      (fun i hi r' hr' => hJ (i + 1) ⟨by omega, by omega⟩ r' hr') r hr
    obtain ⟨e₂⟩ := cokernel_step (S.map' 0 1) (S.map' 1 2) (S.sc hS.toIsComplex 0).zero
      (hS.exact 0) (hJ 2 ⟨by omega, by omega⟩) (r + s) (by omega)
    exact ⟨e₁ ≪≫ e₂⟩

/-- **Remark 1.13**, iterated form. An exact sequence $0 \to M \to J_1 \to \cdots \to J_s \to N \to 0$ with
$H^r(G, J_i) = 0$ for all $r, i > 0$ defines isomorphisms $H^r(G, N) \simeq H^{r+s}(G, M)$ for all $r \ge 1$. The
sequence is `S : ComposableArrows (Rep ℤ G) (s + 1)` with `S.obj 0 = M`, `S.obj i = J_i`, `S.obj (s+1) = N`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.13 (iterated), p. 63"]
theorem remark_1_13_iterated (s : ℕ) (S : ComposableArrows (Rep ℤ G) (s + 1)) (hS : S.Exact)
    (h₀ : Mono (S.map' 0 1)) (h₁ : Epi (S.map' s (s + 1)))
    (hJ : ∀ i : ℕ, ∀ hi : 1 ≤ i ∧ i ≤ s, ∀ r : ℕ, 0 < r →
      Limits.IsZero (groupCohomology (S.obj ⟨i, by omega⟩) r))
    (r : ℕ) (hr : 1 ≤ r) :
    Nonempty (groupCohomology (S.obj ⟨s + 1, by omega⟩) r ≅ groupCohomology (S.obj 0) (r + s)) := by
  cases s with
  | zero =>
    have hI : IsIso (S.map' 0 1) := by
      haveI := h₀
      haveI := h₁
      exact isIso_of_mono_of_epi _
    exact ⟨(groupCohomology.functor ℤ G r).mapIso (@asIso _ _ _ _ _ hI).symm⟩
  | succ k =>
    obtain ⟨e₁⟩ := remark_1_13_aux k S hS h₁ (fun i hi r' hr' => hJ i hi r' hr') r hr
    let Sh : ShortComplex (Rep ℤ G) :=
      ShortComplex.mk (S.map' 0 1) (Limits.cokernel.π (S.map' 0 1)) (Limits.cokernel.condition _)
    have hSh : Sh.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) h₀ inferInstance
    have hiso := (remark_1_13 hSh (hJ 1 ⟨le_rfl, by omega⟩)).2 (r + k) (by omega)
    exact ⟨e₁ ≪≫ @asIso _ _ _ _ (δ hSh (r + k) (r + k + 1) rfl) hiso⟩

section ExtLemma

open scoped TensorProduct

variable {k : Type} [CommRing k]

/-- Two linear maps out of `k[G] ⊗ V` agreeing on `single x r ⊗ v` are equal. -/
theorem monoidAlgebra_tensor_ext {V N : Type} [AddCommGroup V] [Module k V] [AddCommGroup N]
    [Module k N] {f h : MonoidAlgebra k G ⊗[k] V →ₗ[k] N}
    (H : ∀ x r v, f (MonoidAlgebra.single x r ⊗ₜ v) = h (MonoidAlgebra.single x r ⊗ₜ v)) :
    f = h := by
  refine TensorProduct.ext' fun a m => ?_
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | single x r => exact H x r m

end ExtLemma

/-! ## Remark 1.3 (finite groups) -/

section Finite

variable [Fintype G]

section IndTensor

open scoped TensorProduct

variable {k : Type} [CommRing k] (M₀ : Type) [AddCommGroup M₀] [Module k M₀]

/-- The submodule of `G → M₀` underlying `Ind^G(M₀)`. -/
abbrev IndV : Type := Representation.coindV (⊥ : Subgroup G).subtype
  (Rep.trivial k (⊥ : Subgroup G) M₀).ρ

theorem mem_indV (f : G → M₀) : f ∈ Representation.coindV (⊥ : Subgroup G).subtype
    (Rep.trivial k (⊥ : Subgroup G) M₀).ρ := by
  intro g h
  have : g = 1 := Subtype.ext (Subgroup.mem_bot.1 g.2)
  subst this
  simp

/-- `φ ↦ ∑ g, single g 1 ⊗ φ(g⁻¹)`. -/
noncomputable def indToTensorL : IndV (k := k) (G := G) M₀ →ₗ[k] MonoidAlgebra k G ⊗[k] M₀ :=
  ∑ g : G, (TensorProduct.mk k (MonoidAlgebra k G) M₀ (MonoidAlgebra.single g 1)).comp
    ((LinearMap.proj g⁻¹).comp (Submodule.subtype _))

theorem indToTensorL_apply (φ : IndV (k := k) (G := G) M₀) :
    indToTensorL M₀ φ = ∑ g : G, (MonoidAlgebra.single g (1 : k)) ⊗ₜ[k] (φ.1 g⁻¹) := by
  simp [indToTensorL]

/-- `single g n ⊗ m ↦ (x ↦ if x = g⁻¹ then n • m else 0)`. -/
noncomputable def tensorToIndL : MonoidAlgebra k G ⊗[k] M₀ →ₗ[k] IndV (k := k) (G := G) M₀ :=
  (TensorProduct.lift (LinearMap.mk₂ k (fun (a : MonoidAlgebra k G) (m : M₀) => fun x : G =>
      a.coeff x⁻¹ • m)
    (fun a b m => by funext x; simp [add_smul])
    (fun c a m => by funext x; simp [mul_smul])
    (fun a m n => by funext x; simp [smul_add])
    (fun c a m => by funext x; simp [smul_comm c]))).codRestrict _ (fun _ => mem_indV M₀ _)

theorem tensorToIndL_apply (a : MonoidAlgebra k G) (m : M₀) (x : G) :
    (tensorToIndL M₀ (a ⊗ₜ[k] m)).1 x = a.coeff x⁻¹ • m := by
  simp [tensorToIndL]

/-- The linear equivalence `Ind^G(M₀) ≃ k[G] ⊗ M₀`. -/
noncomputable def indTensorEquiv : IndV (k := k) (G := G) M₀ ≃ₗ[k] MonoidAlgebra k G ⊗[k] M₀ :=
  LinearEquiv.ofLinear (indToTensorL M₀) (tensorToIndL M₀)
    (by
      refine monoidAlgebra_tensor_ext fun x r v => ?_
      classical
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [indToTensorL_apply, Finset.sum_eq_single x]
      · have h : (tensorToIndL M₀ (MonoidAlgebra.single x r ⊗ₜ[k] v)).1 x⁻¹ = r • v := by
          simp [tensorToIndL_apply]
        rw [h, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        simp
      · intro b _ hb
        simp [tensorToIndL_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, hb.symm]
      · simp)
    (by
      refine LinearMap.ext fun φ => ?_
      refine Subtype.ext (funext fun x => ?_)
      classical
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [indToTensorL_apply, map_sum, Submodule.coe_sum, Finset.sum_apply,
        Finset.sum_eq_single x⁻¹]
      · simp [tensorToIndL_apply]
      · intro b _ hb
        simp [tensorToIndL_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, hb]
      · simp)

set_option backward.isDefEq.respectTransparency false in
/-- Generic-coefficient version of `indGIsoTensor`. -/
noncomputable def indIsoTensorAux :
    coind (⊥ : Subgroup G).subtype (Rep.trivial k (⊥ : Subgroup G) M₀) ≅
      leftRegular k G ⊗ trivial k G M₀ :=
  Rep.mkIso (Representation.Equiv.mk (indTensorEquiv M₀) (fun g => by
    refine LinearMap.ext fun φ => ?_
    simp only [LinearMap.comp_apply]
    show indToTensorL M₀ _ = TensorProduct.map _ _ (indToTensorL M₀ φ)
    rw [indToTensorL_apply, indToTensorL_apply, map_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft g)
      (fun x => TensorProduct.map ((Representation.ofMulAction k G G) g)
        ((Representation.trivial k G M₀) g) (MonoidAlgebra.single x 1 ⊗ₜ[k] φ.1 x⁻¹))
      (fun y => MonoidAlgebra.single y (1 : k) ⊗ₜ[k] (φ.1 (y⁻¹ * g))) (fun x => ?_)).symm
    simp [Representation.ofMulAction_single, mul_assoc]))

end IndTensor

/-- **Remark 1.3 (a)**, the isomorphism $\operatorname{Ind}^G(M_0) \to \mathbb Z[G] \otimes_{\mathbb Z} M_0$,
$\varphi \mapsto \sum_g g \otimes \varphi(g^{-1})$, where $G$ acts on the first factor only. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.3 (a), the isomorphism Ind^G(M_0) ≅ Z[G] ⊗ M_0, p. 59"]
noncomputable def indGIsoTensor (M₀ : Type) [AddCommGroup M₀] [Module ℤ M₀] :
    indG G M₀ ≅ leftRegular ℤ G ⊗ trivial ℤ G M₀ :=
  indIsoTensorAux M₀

theorem indGIsoTensor_hom_apply (M₀ : Type) [AddCommGroup M₀] [Module ℤ M₀] (φ : indG G M₀) :
    (indGIsoTensor M₀).hom.hom φ = ∑ g : G,
      rtmul (A := leftRegular ℤ G) (B := trivial ℤ G M₀) (MonoidAlgebra.single g (1 : ℤ)) (φ.1 g⁻¹) :=
  indToTensorL_apply M₀ φ

omit [Fintype G] in
theorem rho_injective' (M : Rep ℤ G) (g : G) : Function.Injective (M.ρ g) := by
  intro a b h
  have := congrArg (M.ρ g⁻¹) h
  simpa [← Module.End.mul_apply, ← map_mul] using this

/-- `(f g)_g ↦ ∑ g, ρ g (f g)` for an additive subgroup `M₀ ⊆ M`. -/
def sumMap (M : Rep ℤ G) (M₀ : AddSubgroup M) : (G → M₀) →+ M :=
  AddMonoidHom.mk' (fun f => ∑ g, M.ρ g (f g : M)) (fun f f' => by
    simp [Finset.sum_add_distrib])

theorem isInternal_iff_sumMap [DecidableEq G] (M : Rep ℤ G) (M₀ : AddSubgroup M) :
    DirectSum.IsInternal (fun g : G => M₀.map (M.ρ g).toAddMonoidHom) ↔
      Function.Bijective (sumMap M M₀) := by
  classical
  set A : G → AddSubgroup M := fun g => M₀.map (M.ρ g).toAddMonoidHom with hA
  let P : (G → M₀) →+ ∀ g, A g :=
    AddMonoidHom.mk' (fun f g => ⟨M.ρ g (f g : M), ⟨f g, (f g).2, rfl⟩⟩) (fun f f' => by
      funext g; apply Subtype.ext; simp)
  have hP : Function.Bijective P := by
    constructor
    · intro f f' h
      funext g
      have := congrFun h g
      exact Subtype.ext (rho_injective' M g (congrArg Subtype.val this))
    · intro h
      choose a ha using fun g => (h g).2
      refine ⟨fun g => ⟨a g, (ha g).1⟩, ?_⟩
      funext g
      exact Subtype.ext (ha g).2
  let T : (∀ g, A g) →+ M := AddMonoidHom.mk' (fun f => ∑ g, (f g : M)) (fun f f' => by
    simp [Finset.sum_add_distrib])
  have hT : (DirectSum.coeAddMonoidHom A : (DirectSum G (fun g => A g)) → M) =
      T ∘ (DFinsupp.equivFunOnFintype) := by
    funext d
    rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum,
      DFinsupp.sum_eq_sum_fintype]
    · rfl
    · intro i; simp
  have hS : (sumMap M M₀ : (G → M₀) → M) = T ∘ P := by
    funext f; rfl
  unfold DirectSum.IsInternal
  rw [hT, hS]
  have he : Function.Bijective
      (DFinsupp.equivFunOnFintype : (DirectSum G (fun g => A g)) → ∀ g, A g) :=
    DFinsupp.equivFunOnFintype.bijective
  rw [show (⇑T ∘ ⇑(DFinsupp.equivFunOnFintype : (DirectSum G (fun g => A g)) ≃ _)) =
      T ∘ (Equiv.ofBijective _ he) from rfl,
    show (⇑T ∘ ⇑P) = T ∘ (Equiv.ofBijective _ hP) from rfl,
    Equiv.bijective_comp, Equiv.bijective_comp]

/-- `φ ↦ ∑ g, g φ(g⁻¹)` for `φ ∈ Ind^G(M₀)`, `M₀ ⊆ M`. -/
noncomputable def indQ (M : Rep ℤ G) (M₀ : AddSubgroup M) :
    IndV (k := ℤ) (G := G) M₀ →ₗ[ℤ] M :=
  { toFun := fun φ => sumMap M M₀ (fun g => φ.1 g⁻¹)
    map_add' := fun φ ψ => by
      rw [← map_add]; rfl
    map_smul' := fun n φ => by
      have h1 := map_zsmul (sumMap M M₀) n (fun g => φ.1 g⁻¹)
      have h2 : (fun g => (n • φ).1 g⁻¹) = n • (fun g => φ.1 g⁻¹) := by
        funext g
        show ((n • φ).1 g⁻¹) = n • (φ.1 g⁻¹)
        simp
      refine (congrArg (sumMap M M₀) h2).trans (h1.trans ?_)
      exact (Int.cast_smul_eq_zsmul ℤ n _).symm }

theorem indQ_apply (M : Rep ℤ G) (M₀ : AddSubgroup M) (φ : IndV (k := ℤ) (G := G) M₀) :
    indQ M M₀ φ = sumMap M M₀ (fun g => φ.1 g⁻¹) := rfl

theorem indQ_bijective (M : Rep ℤ G) (M₀ : AddSubgroup M) (h : Function.Bijective (sumMap M M₀)) :
    Function.Bijective (indQ M M₀) := by
  have : (indQ M M₀ : IndV (k := ℤ) (G := G) M₀ → M) = sumMap M M₀ ∘
      (fun φ => fun g => φ.1 g⁻¹) := by
    funext φ; exact indQ_apply M M₀ φ
  rw [this]
  refine h.comp ⟨fun a b hab => ?_, fun f => ⟨⟨fun x => f x⁻¹, mem_indV (k := ℤ) (G := G) M₀ _⟩, ?_⟩⟩
  · refine Subtype.ext (funext fun x => ?_)
    simpa using congrFun hab x⁻¹
  · funext g; simp

set_option backward.isDefEq.respectTransparency false in
theorem indQ_comm (M : Rep ℤ G) (M₀ : AddSubgroup M) (g : G) (φ : indG G M₀) :
    indQ M M₀ (((indG G M₀).ρ g) φ) = M.ρ g (indQ M M₀ φ) := by
  rw [indQ_apply, indQ_apply]
  show ∑ d, M.ρ d (φ.1 (d⁻¹ * g) : M) = M.ρ g (∑ e, M.ρ e (φ.1 e⁻¹ : M))
  rw [map_sum]
  refine (Fintype.sum_equiv (Equiv.mulLeft g) (fun e => M.ρ g (M.ρ e (φ.1 e⁻¹ : M)))
    (fun d => M.ρ d (φ.1 (d⁻¹ * g) : M)) (fun e => ?_)).symm
  simp [mul_assoc, map_mul]

set_option backward.isDefEq.respectTransparency false in
/-- If `M = ⊕ g M₀` then `M` is induced. -/
theorem isInduced_of_sumMap_bijective (M : Rep ℤ G) (M₀ : AddSubgroup M)
    (h : Function.Bijective (sumMap M M₀)) : IsInduced M :=
  ⟨M₀, inferInstance, inferInstance, ⟨(Rep.mkIso (Representation.Equiv.mk
    (LinearEquiv.ofBijective (indQ M M₀) (indQ_bijective M M₀ h))
    (fun g => LinearMap.ext fun φ => indQ_comm M M₀ g φ))).symm⟩⟩

/-- The functions in `Ind^G(N₀)` supported at `1`. -/
def suppOne (N₀ : Type) [AddCommGroup N₀] [Module ℤ N₀] : AddSubgroup (indG G N₀) where
  carrier := {φ | ∀ x, x ≠ 1 → φ.1 x = 0}
  zero_mem' := fun x _ => rfl
  add_mem' := fun {a b} ha hb x hx => by
    show a.1 x + b.1 x = 0
    rw [ha x hx, hb x hx, add_zero]
  neg_mem' := fun {a} ha x hx => by
    show -a.1 x = 0
    rw [ha x hx, neg_zero]

set_option backward.isDefEq.respectTransparency false in
theorem sumMap_ind_apply (N₀ : Type) [AddCommGroup N₀] [Module ℤ N₀]
    (f : G → suppOne (G := G) N₀) (x : G) :
    (sumMap (indG G N₀) (suppOne N₀) f).1 x = ((f x⁻¹ : indG G N₀).1 1) := by
  classical
  show (∑ g, (indG G N₀).ρ g (f g : indG G N₀)).1 x = _
  rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_eq_single x⁻¹]
  · show (f x⁻¹ : indG G N₀).1 (x * x⁻¹) = _
    simp
  · intro b _ hb
    show (f b : indG G N₀).1 (x * b) = 0
    apply (f b).2
    intro h
    exact hb (eq_inv_of_mul_eq_one_right h)
  · simp

set_option backward.isDefEq.respectTransparency false in
theorem sumMap_ind_bijective (N₀ : Type) [AddCommGroup N₀] [Module ℤ N₀] :
    Function.Bijective (sumMap (indG G N₀) (suppOne N₀)) := by
  classical
  constructor
  · intro f f' h
    funext g
    apply Subtype.ext
    apply Subtype.ext
    funext y
    by_cases hy : y = 1
    · subst hy
      have := congrFun (congrArg Subtype.val h) g⁻¹
      rw [sumMap_ind_apply, sumMap_ind_apply] at this
      simpa using this
    · rw [(f g).2 y hy, (f' g).2 y hy]
  · intro ψ
    refine ⟨fun g => ⟨⟨fun y => if y = 1 then ψ.1 g⁻¹ else 0,
      mem_indV (k := ℤ) (G := G) N₀ _⟩, ?_⟩, ?_⟩
    · intro x hx; simp [hx]
    · apply Subtype.ext; funext x; rw [sumMap_ind_apply]; simp

/-- The preimage of an additive subgroup under an isomorphism of `G`-modules. -/
def pullbackSub {M N : Rep ℤ G} (e : M ≅ N) (A : AddSubgroup N) : AddSubgroup M where
  carrier := {m | e.hom.hom m ∈ A}
  zero_mem' := by
    show e.hom.hom 0 ∈ A
    rw [map_zero]; exact A.zero_mem
  add_mem' := fun {a b} ha hb => by
    show e.hom.hom (a + b) ∈ A
    rw [map_add]; exact A.add_mem ha hb
  neg_mem' := fun {a} ha => by
    show e.hom.hom (-a) ∈ A
    rw [map_neg]; exact A.neg_mem ha

theorem iso_hom_bijective {M N : Rep ℤ G} (e : M ≅ N) : Function.Bijective e.hom.hom := by
  have h1 : ∀ m, e.inv.hom (e.hom.hom m) = m := fun m => by
    have := congrArg (fun f => f.hom m) e.hom_inv_id
    simpa using this
  have h2 : ∀ n, e.hom.hom (e.inv.hom n) = n := fun n => by
    have := congrArg (fun f => f.hom n) e.inv_hom_id
    simpa using this
  exact ⟨fun a b hab => by rw [← h1 a, ← h1 b, hab], fun n => ⟨e.inv.hom n, h2 n⟩⟩

theorem sumMap_bijective_of_iso {M N : Rep ℤ G} (e : M ≅ N) (A : AddSubgroup N)
    (h : Function.Bijective (sumMap N A)) : Function.Bijective (sumMap M (pullbackSub e A)) := by
  let Ψ : (G → pullbackSub e A) → (G → A) := fun f g => ⟨e.hom.hom (f g), (f g).2⟩
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro f f' hf
      funext g
      exact Subtype.ext ((iso_hom_bijective e).1 (congrArg Subtype.val (congrFun hf g)))
    · intro k
      choose a ha using fun g => (iso_hom_bijective e).2 (k g : N)
      refine ⟨fun g => ⟨a g, by show e.hom.hom (a g) ∈ A; rw [ha g]; exact (k g).2⟩, ?_⟩
      funext g
      exact Subtype.ext (ha g)
  have key : (e.hom.hom ∘ sumMap M (pullbackSub e A)) = sumMap N A ∘ Ψ := by
    funext f
    show e.hom.hom (∑ g, M.ρ g (f g : M)) = ∑ g, N.ρ g (e.hom.hom (f g : M))
    rw [map_sum]
    exact Finset.sum_congr rfl fun g _ => Rep.hom_comm_apply e.hom g _
  have : Function.Bijective (e.hom.hom ∘ sumMap M (pullbackSub e A)) := by
    rw [key]; exact h.comp hΨ
  exact (Function.Bijective.of_comp_iff' (iso_hom_bijective e) _).1 this

/-- **Remark 1.3 (a).** For finite $G$, a $G$-module $M$ is induced if and only if there is a subgroup
$M_0 \subseteq M$ with $M = \bigoplus_{g \in G} gM_0$ (internal direct sum of abelian groups). -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.3 (a), p. 59"]
theorem remark_1_3a [DecidableEq G] (M : Rep ℤ G) :
    IsInduced M ↔ ∃ M₀ : AddSubgroup M,
      DirectSum.IsInternal (fun g : G => M₀.map (M.ρ g).toAddMonoidHom) := by
  constructor
  · rintro ⟨N₀, _, _, ⟨e⟩⟩
    exact ⟨pullbackSub e (suppOne N₀), (isInternal_iff_sumMap M _).2
      (sumMap_bijective_of_iso e _ (sumMap_ind_bijective N₀))⟩
  · rintro ⟨M₀, h⟩
    exact isInduced_of_sumMap_bijective M M₀ ((isInternal_iff_sumMap M M₀).1 h)

/-- `G ≃ (G ⧸ H) × H`, `x ↦ (xH, (out xH)⁻¹ x)`, inverse `(q, h) ↦ out q * h`. -/
noncomputable def splitEquiv (H : Subgroup G) : (G ⧸ H) × H ≃ G where
  toFun p := p.1.out * p.2
  invFun x := ((x : G ⧸ H), ⟨((x : G ⧸ H).out)⁻¹ * x, by
    have := QuotientGroup.out_eq' (s := H) (x : G ⧸ H)
    exact QuotientGroup.eq.1 this⟩)
  left_inv p := by
    obtain ⟨q, h⟩ := p
    have hq : ((q.out * (h : G) : G) : G ⧸ H) = q := by
      rw [QuotientGroup.mk_mul_of_mem _ h.2]; exact QuotientGroup.out_eq' q
    refine Prod.ext hq (Subtype.ext ?_)
    show (((q.out * (h : G) : G) : G ⧸ H).out)⁻¹ * (q.out * (h : G)) = h
    rw [hq]; simp
  right_inv x := by
    show ((x : G ⧸ H).out) * (((x : G ⧸ H).out)⁻¹ * x) = x
    simp

/-- Restriction of `Ind^G(N₀)` to `H` is `Ind^H(Map(G/H, N₀))`: the underlying linear equivalence,
`φ ↦ (h ↦ (q ↦ φ(out q * h)))`. -/
noncomputable def resIndFun {k : Type} [CommRing k] (H : Subgroup G) [Fintype H] (N₀ : Type)
    [AddCommGroup N₀] [Module k N₀] (φ : IndV (k := k) (G := G) N₀) :
    IndV (k := k) (G := H) (G ⧸ H → N₀) :=
  ⟨fun h q => φ.1 (splitEquiv H (q, h)), mem_indV (k := k) (G := H) _ _⟩

theorem resIndFun_bijective {k : Type} [CommRing k] (H : Subgroup G) [Fintype H] (N₀ : Type)
    [AddCommGroup N₀] [Module k N₀] : Function.Bijective (resIndFun (k := k) H N₀) :=
  ⟨fun a b hab => by
      refine Subtype.ext (funext fun x => ?_)
      have := congrFun (congrFun (congrArg Subtype.val hab) ((splitEquiv H).symm x).2)
        ((splitEquiv H).symm x).1
      simpa [resIndFun] using this,
   fun ψ => ⟨⟨fun x => ψ.1 ((splitEquiv H).symm x).2 ((splitEquiv H).symm x).1,
        mem_indV (k := k) (G := G) N₀ _⟩, by
      refine Subtype.ext (funext fun h => funext fun q => ?_)
      simp [resIndFun]⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The `H`-homomorphism `Res^G_H Ind^G(N₀) → Ind^H(Map(G/H, N₀))` (bijective). -/
noncomputable def resIndHom {k : Type} [CommRing k] (H : Subgroup G) [Fintype H] (N₀ : Type)
    [AddCommGroup N₀] [Module k N₀] :
    res H.subtype (coind (⊥ : Subgroup G).subtype (Rep.trivial k (⊥ : Subgroup G) N₀)) ⟶
      coind (⊥ : Subgroup H).subtype (Rep.trivial k (⊥ : Subgroup H) (G ⧸ H → N₀)) :=
  Rep.ofHom ⟨{ toFun := resIndFun H N₀, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun h => by
      refine LinearMap.ext fun φ => ?_
      refine Subtype.ext (funext fun x => funext fun q => ?_)
      show φ.1 (splitEquiv H (q, x) * (h : G)) = φ.1 (splitEquiv H (q, x * h))
      simp [splitEquiv, mul_assoc]⟩

set_option backward.isDefEq.respectTransparency false in
theorem isInduced_res_of_isInduced (H : Subgroup G) {M : Rep ℤ G} (hM : IsInduced M) :
    IsInduced (res H.subtype M) := by
  classical
  haveI : Fintype H := Fintype.ofFinite _
  obtain ⟨N₀, _, _, ⟨e⟩⟩ := hM
  have hb := resIndFun_bijective (k := ℤ) H N₀
  haveI : Mono (resIndHom (k := ℤ) H N₀) := (Rep.mono_iff_injective _).2 (fun a b h => hb.1 h)
  haveI : Epi (resIndHom (k := ℤ) H N₀) := (Rep.epi_iff_surjective _).2 (fun y => hb.2 y)
  haveI : IsIso (resIndHom (k := ℤ) H N₀) := isIso_of_mono_of_epi _
  exact ⟨G ⧸ H → N₀, inferInstance, Pi.module _ _ _,
    ⟨(resFunctor H.subtype).mapIso e ≪≫ asIso (resIndHom (k := ℤ) H N₀)⟩⟩

/-- **Remark 1.3 (b).** For finite $G$ and a subgroup $H$, an induced $G$-module is induced as an $H$-module. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.3 (b), p. 59"]
theorem remark_1_3b {M : Rep ℤ G} (hM : IsInduced M) (H : Subgroup G) :
    IsInduced (res H.subtype M) :=
  isInduced_res_of_isInduced H hM

/-- Generic-coefficient version of `indGπ` (avoids the `ℤ`-module diamond). -/
noncomputable def indGπAux {k : Type} [CommRing k] (M : Rep k G) :
    coind (⊥ : Subgroup G).subtype (Rep.trivial k (⊥ : Subgroup G) M) ⟶ M :=
  Rep.ofHom ⟨∑ g : G, (M.ρ g).comp ((LinearMap.proj g⁻¹).comp
      (Representation.coindV (⊥ : Subgroup G).subtype (Rep.trivial k (⊥ : Subgroup G) M).ρ).subtype),
    fun g => by
    refine LinearMap.ext fun φ => ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply,
      Submodule.subtype_apply, LinearMap.coe_proj, Function.eval]
    show ∑ d, M.ρ d (φ.1 (d⁻¹ * g)) = _
    rw [map_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft g) (fun e => M.ρ g (M.ρ e (φ.1 e⁻¹)))
      (fun d => M.ρ d (φ.1 (d⁻¹ * g))) (fun e => ?_)).symm
    simp [mul_assoc, map_mul]⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Remark 1.3 (c)**, the map $\pi : \operatorname{Ind}^G(M_0) \to M$, $\varphi \mapsto \sum_g g\varphi(g^{-1})$,
where $M_0$ is $M$ regarded as an abelian group. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.3 (c), the map Ind^G(M_0) → M, p. 59"]
noncomputable def indGπ (M : Rep ℤ G) : indG G M ⟶ M :=
  indGπAux M

set_option backward.isDefEq.respectTransparency false in
theorem indGπ_apply (M : Rep ℤ G) (φ : indG G M) :
    (indGπ M).hom φ = ∑ g : G, M.ρ g (φ.1 g⁻¹) := by
  simp [indGπ, indGπAux]

set_option backward.isDefEq.respectTransparency false in
/-- Generic-coefficient version of `tensorToSelf`. -/
noncomputable def tensorToSelfAux {k : Type} [CommRing k] (M : Rep k G) :
    leftRegular k G ⊗ trivial k G M ⟶ M :=
  Rep.ofHom ⟨TensorProduct.lift
      (Finsupp.lift (M →ₗ[k] M) k G (fun g => M.ρ g) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap), fun g => by
    refine TensorProduct.ext' fun a m => ?_
    simp only [LinearMap.comp_apply]
    change (TensorProduct.lift _) (TensorProduct.map _ _ (a ⊗ₜ m)) = _
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
    | single x r =>
      simp [Representation.ofMulAction_single, MonoidAlgebra.coeff_single, Finsupp.sum_single_index]⟩

/-- The map $\mathbb Z[G] \otimes M_0 \to M$, $\sum n_g\, g \otimes m \mapsto \sum n_g\, gm$ (Remark 1.3 (c)). -/
noncomputable def tensorToSelf (M : Rep ℤ G) : leftRegular ℤ G ⊗ trivial ℤ G M ⟶ M :=
  tensorToSelfAux M

set_option backward.isDefEq.respectTransparency false in
theorem tensorToSelf_apply (M : Rep ℤ G) (g : G) (m : M) :
    (tensorToSelf M).hom
      (rtmul (A := leftRegular ℤ G) (B := trivial ℤ G M) (MonoidAlgebra.single g (1 : ℤ)) m) = M.ρ g m := by
  simp [tensorToSelf, tensorToSelfAux, rtmul, MonoidAlgebra.coeff_single]
  rw [Finsupp.sum_single_index]
  · simp
  · exact @zero_smul ℤ M _ _ (@MulActionWithZero.toSMulWithZero ℤ M _ _
      (@Module.toMulActionWithZero ℤ M _ _ M.hV2)) _

section Remark13cAux

open scoped TensorProduct

variable {k : Type} [CommRing k]

theorem tensorToSelfAux_single (M : Rep.{0, 0, 0} k G) (x : G) (r : k) (v : M) :
    (tensorToSelfAux M).hom (MonoidAlgebra.single x r ⊗ₜ[k] v) = r • M.ρ x v := by
  simp [tensorToSelfAux, MonoidAlgebra.coeff_single]

set_option backward.isDefEq.respectTransparency false in
theorem indGπAux_apply (M : Rep.{0, 0, 0} k G) (φ : IndV (k := k) (G := G) M) :
    (indGπAux M).hom φ = ∑ g : G, M.ρ g (φ.1 g⁻¹) := by
  simp [indGπAux]

theorem indGπAux_surjective (M : Rep.{0, 0, 0} k G) : Function.Surjective (indGπAux M).hom := by
  classical
  intro m
  refine ⟨⟨fun g => if g = 1 then m else 0, mem_indV (k := k) (G := G) M _⟩, ?_⟩
  rw [indGπAux_apply]
  show ∑ x : G, M.ρ x (if x⁻¹ = 1 then m else 0) = m
  rw [Finset.sum_eq_single 1]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

set_option backward.isDefEq.respectTransparency false in
theorem indIsoTensorAux_inv_comp (M : Rep.{0, 0, 0} k G) :
    (indIsoTensorAux (k := k) (G := G) M).inv ≫ indGπAux M = tensorToSelfAux M := by
  classical
  refine Rep.hom_ext (Representation.IntertwiningMap.ext ?_)
  refine monoidAlgebra_tensor_ext fun x r v => ?_
  show (indGπAux M).hom (tensorToIndL (k := k) (G := G) M (MonoidAlgebra.single x r ⊗ₜ[k] v)) = _
  refine Eq.trans ?_ (tensorToSelfAux_single M x r v).symm
  rw [indGπAux_apply, Finset.sum_eq_single x]
  · simp [tensorToIndL_apply, MonoidAlgebra.coeff_single]
  · intro b _ hb
    simp [tensorToIndL_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, hb]
  · simp

end Remark13cAux

/-- **Remark 1.3 (c).** The map $\pi : \operatorname{Ind}^G(M_0) \to M$ is a surjective homomorphism of
$G$-modules, and it corresponds to $\mathbb Z[G] \otimes M_0 \to M$, $g \otimes m \mapsto gm$, under the
isomorphism of (a). -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.3 (c), p. 59"]
theorem remark_1_3c (M : Rep ℤ G) :
    Function.Surjective (indGπ M).hom ∧ (indGIsoTensor (G := G) M).inv ≫ indGπ M = tensorToSelf M :=
  ⟨indGπAux_surjective M, indIsoTensorAux_inv_comp M⟩

end Finite

/-! ## Remark 1.4 -/

section Twist

open scoped TensorProduct

variable {k : Type} [CommRing k]

/-- The linear map `single x r ⊗ v ↦ single x r ⊗ c x v` on `k[G] ⊗ V`. -/
noncomputable def twistL {V : Type} [AddCommGroup V] [Module k V] (c : G → V →ₗ[k] V) :
    MonoidAlgebra k G ⊗[k] V →ₗ[k] MonoidAlgebra k G ⊗[k] V :=
  TensorProduct.lift ((Finsupp.lift (V →ₗ[k] MonoidAlgebra k G ⊗[k] V) k G
    (fun x => (TensorProduct.mk k (MonoidAlgebra k G) V (MonoidAlgebra.single x 1)).comp (c x))) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)

theorem twistL_single {V : Type} [AddCommGroup V] [Module k V] (c : G → V →ₗ[k] V) (x : G) (r : k)
    (v : V) : twistL c (MonoidAlgebra.single x r ⊗ₜ v) = MonoidAlgebra.single x r ⊗ₜ c x v := by
  simp only [twistL, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearEquiv.coe_coe,
    MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.coeff_single]
  rw [Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, TensorProduct.mk_apply]
  rw [TensorProduct.smul_tmul']
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Generic-coefficient version of `remark_1_4`. -/
noncomputable def remark14Aux (M : Rep k G) :
    leftRegular k G ⊗ trivial k G M ≅ leftRegular k G ⊗ M where
  hom := Rep.ofHom ⟨twistL (fun x => M.ρ x), fun g => by
    refine monoidAlgebra_tensor_ext fun x r v => ?_
    simp [Representation.ofMulAction_single, twistL_single, Representation.tprod_apply,
      map_mul]⟩
  inv := Rep.ofHom ⟨twistL (fun x => M.ρ x⁻¹), fun g => by
    refine monoidAlgebra_tensor_ext fun x r v => ?_
    simp [Representation.ofMulAction_single, twistL_single, Representation.tprod_apply,
      map_mul, mul_inv_rev]⟩
  hom_inv_id := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext ?_)
    refine monoidAlgebra_tensor_ext fun x r v => ?_
    simp [twistL_single]
  inv_hom_id := by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext ?_)
    refine monoidAlgebra_tensor_ext fun x r v => ?_
    simp [twistL_single]

end Twist

/-- **Remark 1.4.** For a $G$-module $M$ with underlying abelian group $M_0$, the map
$\mathbb Z[G] \otimes M_0 \to \mathbb Z[G] \otimes M$, $g \otimes m \mapsto g \otimes gm$, is an isomorphism of
$G$-modules (on the left $G$ acts on $\mathbb Z[G]$ only, on the right diagonally). -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.4, p. 60"]
noncomputable def remark_1_4 (M : Rep ℤ G) : leftRegular ℤ G ⊗ trivial ℤ G M ≅ leftRegular ℤ G ⊗ M :=
  remark14Aux M

set_option backward.isDefEq.respectTransparency false in
theorem remark_1_4_hom_apply (M : Rep ℤ G) (g : G) (m : M) :
    (remark_1_4 M).hom.hom
      (rtmul (A := leftRegular ℤ G) (B := trivial ℤ G M) (MonoidAlgebra.single g (1 : ℤ)) m) =
      rtmul (A := leftRegular ℤ G) (B := M) (MonoidAlgebra.single g (1 : ℤ)) (M.ρ g m) :=
  twistL_single (fun x => M.ρ x) g 1 m

/-! ## Lemma 1.37 -/

/-- **Lemma 1.37.** The exact sequence (15), $0 \to M \to M_* \to M^* \to 0$, is split as a sequence of abelian
groups: $s(\varphi) = \varphi(1_G)$ is a retraction of $M \to M_*$, and $M_* \simeq M \oplus M^*$ as abelian
groups. -/
@[kb "milne2020cft" "v4.03, Ch. II, Lemma 1.37, p. 72"]
theorem lemma_1_37 (M : Rep ℤ G) :
    (∃ s : indG G M →+ M, (∀ φ : indG G M, s φ = φ.1 1) ∧ ∀ m : M, s ((toIndG M).hom m) = m) ∧
      Nonempty (indG G M ≃+ M × mStar M) := by
  let π : indG G M →+ mStar M :=
    AddMonoidHom.mk' (fun x => (Limits.cokernel.π (toIndG M)).hom x) (fun x y => map_add _ x y)
  let s : indG G M →+ M :=
    { toFun := fun φ => φ.1 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hs : ∀ m : M, s ((toIndG M).hom m) = m := fun m => by
    show ((toIndG M).hom m).1 1 = m
    rw [toIndG_apply]; simp
  have hex : ∀ x : indG G M, π x = 0 → ∃ m : M, (toIndG M).hom m = x := by
    have := (ShortComplex.moduleCat_exact_iff _).1
      ((seq15_shortExact M).exact.map (forget₂ (Rep ℤ G) (ModuleCat ℤ)))
    exact fun x hx => this x hx
  have hsurj : Function.Surjective π := by
    have : Epi (Limits.cokernel.π (toIndG M)) := inferInstance
    exact (Rep.epi_iff_surjective _).1 this
  have hπf : ∀ m : M, π ((toIndG M).hom m) = 0 := fun m => by
    have := congrArg (fun f => f.hom m) (Limits.cokernel.condition (toIndG M))
    exact this
  refine ⟨⟨s, fun _ => rfl, hs⟩, ⟨AddEquiv.ofBijective (s.prod π) ⟨?_, ?_⟩⟩⟩
  · rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    have h1 : s x = 0 := congrArg Prod.fst hx
    have h2 : π x = 0 := congrArg Prod.snd hx
    obtain ⟨m, rfl⟩ := hex x h2
    rw [hs] at h1
    subst h1
    exact map_zero _
  · rintro ⟨m, y⟩
    obtain ⟨φ, rfl⟩ := hsurj y
    refine ⟨φ - (toIndG M).hom (s φ) + (toIndG M).hom m, ?_⟩
    ext
    · show s (φ - (toIndG M).hom (s φ) + (toIndG M).hom m) = m
      rw [map_add, map_sub, hs, hs]; abel
    · show π (φ - (toIndG M).hom (s φ) + (toIndG M).hom m) = π φ
      rw [map_add, map_sub, hπf, hπf]; abel

section NormalBasis

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem normalBasis_repr_aut (σ : L ≃ₐ[K] L) (x : L) (g : L ≃ₐ[K] L) :
    (IsGalois.normalBasis K L).repr (σ x) g = (IsGalois.normalBasis K L).repr x (σ⁻¹ * g) := by
  have key : ∀ y g, (IsGalois.normalBasis K L).repr y g =
      (IsGalois.normalBasis K L).repr (σ⁻¹ y) (σ⁻¹ * g) := by
    intro y g
    refine (IsGalois.normalBasis K L).repr_apply_eq
      (fun y g => (IsGalois.normalBasis K L).repr (σ⁻¹ y) (σ⁻¹ * g)) ?_ ?_ ?_ y g
    · intro a b
      funext g
      simp
    · intro c a
      funext g
      simp
    · intro i
      funext g
      have h1 : σ⁻¹ ((IsGalois.normalBasis K L) i) =
          (IsGalois.normalBasis K L) (σ⁻¹ * i) := by
        rw [IsGalois.normalBasis_apply i, IsGalois.normalBasis_apply (σ⁻¹ * i)]
        rfl
      rw [h1, Module.Basis.repr_self]
      classical
      rw [Finsupp.single_apply, Finsupp.single_apply]
      simp
  have := key (σ x) g
  simpa using this

/-- The normal basis gives an additive isomorphism `L ≃ Ind^G(K)` compatible with the `G`-actions. -/
noncomputable def normalBasisIndEquiv : L ≃ₗ[ℤ] IndV (k := ℤ) (G := L ≃ₐ[K] L) K := by
  classical
  haveI : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  let b := IsGalois.normalBasis K L
  let f : L →ₗ[ℤ] IndV (k := ℤ) (G := L ≃ₐ[K] L) K :=
    { toFun := fun x => ⟨fun g => b.repr x g⁻¹, mem_indV (G := L ≃ₐ[K] L) (k := ℤ) K _⟩
      map_add' := fun x y => Subtype.ext (funext fun g => by simp)
      map_smul' := fun n x => Subtype.ext (funext fun g => by
        show b.repr (n • x) g⁻¹ = n • (b.repr x g⁻¹)
        rw [map_zsmul]; rfl) }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    refine b.repr.injective (Finsupp.ext fun g => ?_)
    have := congrFun (congrArg Subtype.val hxy) g⁻¹
    simpa [f] using this
  · intro φ
    refine ⟨b.repr.symm (Finsupp.equivFunOnFinite.symm (fun g => φ.1 g⁻¹)), ?_⟩
    refine Subtype.ext (funext fun g => ?_)
    simp [f]

theorem normalBasisIndEquiv_apply (x : L) (g : L ≃ₐ[K] L) :
    (normalBasisIndEquiv K L x).1 g = (IsGalois.normalBasis K L).repr x g⁻¹ := rfl

set_option backward.isDefEq.respectTransparency false in
theorem isInduced_ofAlgebraAut : IsInduced (Rep.ofAlgebraAut K L) := by
  classical
  haveI : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  refine ⟨K, inferInstance, inferInstance, ⟨Rep.mkIso (Representation.Equiv.mk
    (normalBasisIndEquiv K L) (fun σ => ?_))⟩⟩
  refine LinearMap.ext fun x => ?_
  refine Subtype.ext (funext fun h => ?_)
  simp only [LinearMap.comp_apply]
  show (normalBasisIndEquiv K L (σ x)).1 h = (normalBasisIndEquiv K L x).1 (h * σ)
  rw [normalBasisIndEquiv_apply, normalBasisIndEquiv_apply, normalBasis_repr_aut]
  simp [mul_inv_rev]

end NormalBasis

/-! ## Proposition 1.24: additive Hilbert 90 -/

/-- **Proposition 1.24.** For a finite Galois extension $L/K$ with group $G$, $H^r(G, L) = 0$ for all $r > 0$
($L$ under addition; Mathlib's `Rep.ofAlgebraAut K L`). The proof is the normal basis theorem
(`IsGalois.normalBasis`) and Shapiro's lemma. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.24, p. 67"]
theorem prop_1_24 (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (r : ℕ) (hr : 0 < r) : Limits.IsZero (groupCohomology (Rep.ofAlgebraAut K L) r) :=
  cor_1_12 (isInduced_ofAlgebraAut K L) r hr

end NumberFieldKB.MilneCFT
