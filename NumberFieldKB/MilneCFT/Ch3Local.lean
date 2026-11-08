import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Residue
import NumberFieldKB.MilneCFT.LocalCFT.Uniqueness
import NumberFieldKB.MilneCFT.LubinTate.Complements

/-!
# Milne, *Class Field Theory*, Chapter III: the Galois modules $L^\times$ and $U_L$

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

**Setting** (Milne, Chapter III, introduction, p. 97). $K$ is a nonarchimedean local field (Mathlib's
`IsNonarchimedeanLocalField`), $K^{\mathrm{al}}$ a separable closure `Ω`, and extensions of $K$ are intermediate
fields $K \subseteq L \subseteq \Omega$, as in Chapter I (`NumberFieldKB.MilneCFT.LocalCFT`). For a finite Galois
extension $L/K$ with group $G = \operatorname{Gal}(L/K)$:
* $L^\times$ is the $G$-module `Rep.ofAlgebraAutOnUnits K L` (Mathlib), as in Chapter II;
* $\mathcal O_L$ is `integers L`, the integral closure of $\mathcal O_K$ in $L$ (Chapter I), and the unit group
  $U_L = \mathcal O_L^\times$ is `unitsL L`, a $G$-stable subgroup of $L^\times$; `unitsRep L` is the $G$-module
  $U_L$ and `unitsIncl L` the inclusion $U_L \to L^\times$.
* Milne's $H^2(L/K) = H^2(G, L^\times)$ is `H2 L`.

General facts proved here: $U_L^G = U_K$ (`mem_unitGroup_of_fixed`); $H^0_T(G, M) = 0$ when every invariant is a
norm (`tate_zero_isZero_of_norm`); a $G$-submodule with a $G$-retraction has $H^r$ injecting into the $H^r$ of the
big module (`isZero_groupCohomology_of_retraction`).
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT

/-! ## Generalities on Tate groups -/

section General

variable {G : Type} [Group G] [Fintype G]

/-- $H^0_T(G, M) = M^G/\mathrm{Nm}_G M$ vanishes when every $G$-invariant element of $M$ is a norm
$\sum_{g} g m$. -/
theorem tate_zero_isZero_of_norm (M : Rep ℤ G)
    (h : ∀ m : M, (∀ g : G, M.ρ g m = m) → ∃ y : M, ∑ g : G, M.ρ g y = m) :
    IsZero (tateCohomology M 0) := by
  show IsZero ((tateComplex M).homology 0)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change (inhomogeneousCochains M).d 0 1 x = 0 at hx
  obtain ⟨m, rfl⟩ : ∃ m, x = (cochainsIso₀ M).inv m :=
    ⟨(cochainsIso₀ M).hom x, ((cochainsIso₀ M).hom_inv_id_apply x).symm⟩
  have h1 := eq_d₀₁_comp_inv_apply M m
  have h2 : d₀₁ M m = 0 := by
    have : (cochainsIso₁ M).inv (d₀₁ M m) = 0 := by rw [← h1]; exact hx
    simpa using congrArg (cochainsIso₁ M).hom this
  have hinv : ∀ g : G, M.ρ g m = m := fun g => by
    have := congrFun h2 g
    exact sub_eq_zero.1 this
  obtain ⟨y, hy⟩ := h m hinv
  refine ⟨Finsupp.single default y, ?_⟩
  change M.tateNorm _ = _
  rw [Rep.tateNorm_eq]
  funext z
  simp [cochainsIso₀, Representation.norm, hy]

omit [Fintype G] in
/-- If $i : M \to N$ has a $G$-equivariant retraction $r$ ($r \circ i = 1$) and $H^n(G, N) = 0$, then
$H^n(G, M) = 0$ ($H^n(G, M)$ is a direct summand of $H^n(G, N)$; Milne, Chapter II, Proposition 1.25). -/
theorem isZero_groupCohomology_of_retraction {M N : Rep ℤ G} (i : M ⟶ N) (r : N ⟶ M) (hri : i ≫ r = 𝟙 M)
    (n : ℕ) (hN : IsZero (groupCohomology N n)) : IsZero (groupCohomology M n) := by
  rw [IsZero.iff_id_eq_zero]
  have : (functor ℤ G n).map i ≫ (functor ℤ G n).map r = 𝟙 _ := by
    rw [← Functor.map_comp, hri, CategoryTheory.Functor.map_id]
  change 𝟙 ((functor ℤ G n).obj M) = 0
  have hN' : IsZero ((functor ℤ G n).obj N) := hN
  rw [← this, hN'.eq_of_tgt ((functor ℤ G n).map i) 0, zero_comp]

end General

/-! ## The units of a finite extension of a local field -/

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- Milne's $H^2(L/K) = H^2(\operatorname{Gal}(L/K), L^\times)$ (Chapter III, introduction, p. 97), for a finite
Galois extension $L/K$ (finite level; Milne also allows infinite Galois extensions, with continuous cochains). -/
@[kb "milne2020cft" "v4.03, Ch. III, introduction, the group H^2(L/K), p. 97"]
noncomputable abbrev H2 (L : IntermediateField K Ω) : ModuleCat ℤ :=
  groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2

/-- The unit group $U_L = \mathcal O_L^\times$ of a finite extension $L$ of $K$, as a subgroup of $L^\times$: the
$x$ with $x, x^{-1} \in \mathcal O_L$. -/
@[kb "milne2020cft" "v4.03, Ch. III, §1, the unit group U_L, p. 97"]
def unitsL (L : IntermediateField K Ω) : Subgroup Lˣ where
  carrier := {x | (x : L) ∈ integers L ∧ ((x⁻¹ : Lˣ) : L) ∈ integers L}
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simpa using Subalgebra.mul_mem _ hx hy, ?_⟩
    simpa [mul_comm] using Subalgebra.mul_mem _ hx' hy'
  one_mem' := ⟨by simp, by simp⟩
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨hx', by simpa using hx⟩

theorem mem_unitsL {L : IntermediateField K Ω} {x : Lˣ} :
    x ∈ unitsL L ↔ (x : L) ∈ integers L ∧ ((x⁻¹ : Lˣ) : L) ∈ integers L := Iff.rfl

theorem gal_smul_mem_unitsL {L : IntermediateField K Ω} (σ : Gal(L/K)) {x : Lˣ} (hx : x ∈ unitsL L) :
    σ • x ∈ unitsL L := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · exact galMap_mem_integers L σ h1
  · have : ((σ • x)⁻¹ : Lˣ) = σ • x⁻¹ := (smul_inv' σ x).symm
    rw [this]
    exact galMap_mem_integers L σ h2

/-- The action of $\operatorname{Gal}(L/K)$ on $U_L$. -/
noncomputable instance (L : IntermediateField K Ω) : MulDistribMulAction Gal(L/K) (unitsL L) where
  smul σ u := ⟨σ • (u : Lˣ), gal_smul_mem_unitsL σ u.2⟩
  one_smul u := Subtype.ext (one_smul _ (u : Lˣ))
  mul_smul σ τ u := Subtype.ext (mul_smul σ τ (u : Lˣ))
  smul_mul σ u v := Subtype.ext (smul_mul' σ (u : Lˣ) v)
  smul_one σ := Subtype.ext (smul_one σ)

@[simp] theorem coe_gal_smul_unitsL (L : IntermediateField K Ω) (σ : Gal(L/K)) (u : unitsL L) :
    ((σ • u : unitsL L) : Lˣ) = σ • (u : Lˣ) := rfl

/-- The $G$-module $U_L$ (Milne, Chapter III, §1, p. 97), $G = \operatorname{Gal}(L/K)$. -/
@[kb "milne2020cft" "v4.03, Ch. III, §1, the G-module U_L, p. 97"]
noncomputable abbrev unitsRep (L : IntermediateField K Ω) : Rep ℤ Gal(L/K) :=
  Rep.ofMulDistribMulAction Gal(L/K) (unitsL L)

/-- The inclusion $U_L \to L^\times$ of $G$-modules. -/
noncomputable def unitsIncl (L : IntermediateField K Ω) : unitsRep L ⟶ Rep.ofAlgebraAutOnUnits K L :=
  Rep.ofHom ⟨(AddMonoidHom.toIntLinearMap
      (MonoidHom.toAdditive (unitsL L).subtype)), fun σ => by
    ext u; rfl⟩

theorem unitsIncl_apply (L : IntermediateField K Ω) (u : unitsRep L) :
    (unitsIncl L).hom u = Additive.ofMul ((Additive.toMul u : unitsL L) : Lˣ) := rfl

/-- **$U_L^G = U_K$**: a unit of $\mathcal O_L$ fixed by $\operatorname{Gal}(L/K)$ lies in $U_K$ (it lies in $K$,
and $\mathcal O_K$ is integrally closed). -/
theorem mem_unitGroup_of_fixed (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] (u : Lˣ)
    (hu : u ∈ unitsL L) (hfix : ∀ σ : Gal(L/K), σ • u = u) :
    ∃ a ∈ unitGroup K, Units.map (algebraMap K L).toMonoidHom a = u := by
  have hfix' : ∀ x : Lˣ, (∀ σ : Gal(L/K), σ • x = x) → ∃ c : K, algebraMap K L c = x := by
    intro x hx
    have : (x : L) ∈ (⊥ : IntermediateField K L) := by
      rw [← IsGalois.fixedField_top (F := K) (E := L)]
      intro σ
      exact congrArg Units.val (hx σ)
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 this
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hfix' u hfix
  obtain ⟨d, hd⟩ := hfix' u⁻¹ (fun σ => by rw [smul_inv', hfix σ])
  have hint : ∀ (e : K) (x : L), algebraMap K L e = x → x ∈ integers L → e ∈ 𝒪[K] := by
    intro e x he hx
    have hx' : IsIntegral 𝒪[K] x := hx
    rw [← he] at hx'
    have : IsIntegral 𝒪[K] e := by
      exact isIntegral_algebraMap_iff.1 hx'
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    rw [← hy]; exact y.2
  have hc0 : c ≠ 0 := by
    rintro rfl; simp at hc; exact u.ne_zero hc.symm
  refine ⟨Units.mk0 c hc0, ?_, ?_⟩
  · refine mem_unitGroup.2 ⟨⟨⟨c, hint c _ hc hu.1⟩, ⟨d, hint d _ hd hu.2⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      have : algebraMap K L (c * d) = 1 := by rw [map_mul, hc, hd]; simp
      simpa using (algebraMap K L).injective (this.trans (map_one _).symm)
    · apply Subtype.ext
      have : algebraMap K L (d * c) = 1 := by rw [map_mul, hc, hd]; simp
      simpa using (algebraMap K L).injective (this.trans (map_one _).symm)
  · apply Units.ext; simpa using hc

end NumberFieldKB.MilneCFT.Ch3
