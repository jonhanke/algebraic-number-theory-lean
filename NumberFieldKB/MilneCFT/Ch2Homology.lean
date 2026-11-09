import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, *Class Field Theory*, Chapter II §2: homology, the augmentation ideal

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

The group ring $\mathbb Z[G]$ is Mathlib's `MonoidAlgebra ℤ G`, with basis elements `MonoidAlgebra.of ℤ G g`
($= $ `MonoidAlgebra.single g 1`). Milne's homology groups are Mathlib's `groupHomology`; Proposition 2.7
($H_1(G, \mathbb Z) \simeq G^{ab}$) is Mathlib's `groupHomology.H1AddEquivOfIsTrivial` (cited in `Ch2Cite.lean`).
-/

namespace NumberFieldKB.MilneCFT

open MonoidAlgebra

variable (G : Type) [Group G]

/-- The **augmentation map** $\mathbb Z[G] \to \mathbb Z$, $\sum n_g g \mapsto \sum n_g$ (p. 76), as a ring
homomorphism (it is the algebra map sending every $g$ to $1$). -/
@[kb "milne2020cft" "v4.03, Ch. II, §2, the augmentation map, p. 76"]
noncomputable def augmentation : MonoidAlgebra ℤ G →ₐ[ℤ] ℤ :=
  MonoidAlgebra.lift ℤ ℤ G 1

theorem augmentation_single (g : G) (n : ℤ) : augmentation G (single g n) = n := by
  simp [augmentation]

theorem augmentation_apply (x : MonoidAlgebra ℤ G) : augmentation G x = x.coeff.sum fun _ n => n := by
  simp [augmentation, MonoidAlgebra.lift_apply]

/-- The **augmentation ideal** $I_G = \operatorname{Ker}(\mathbb Z[G] \to \mathbb Z)$ (p. 74, p. 76), as a
$\mathbb Z$-submodule of $\mathbb Z[G]$ (it is a two-sided ideal; see `augmentationIdeal_eq_ker`). -/
@[kb "milne2020cft" "v4.03, Ch. II, §2, the augmentation ideal I_G, p. 76"]
noncomputable def augmentationIdeal : Submodule ℤ (MonoidAlgebra ℤ G) :=
  LinearMap.ker (augmentation G).toLinearMap

theorem mem_augmentationIdeal (x : MonoidAlgebra ℤ G) :
    x ∈ augmentationIdeal G ↔ augmentation G x = 0 := Iff.rfl

theorem augmentationIdeal_eq_ker :
    (augmentationIdeal G : Set (MonoidAlgebra ℤ G)) = RingHom.ker (augmentation G).toRingHom := by
  ext x; simp [mem_augmentationIdeal, RingHom.mem_ker]

theorem single_sub_one_mem (g : G) : single g (1 : ℤ) - 1 ∈ augmentationIdeal G := by
  simp [mem_augmentationIdeal, augmentation_single, MonoidAlgebra.one_def]

/-- Generators `g - 1`, `g ≠ 1`. -/
private theorem aug_decomp (x : MonoidAlgebra ℤ G) :
    x = x.coeff.sum (fun g n => n • (single g (1 : ℤ) - 1 : MonoidAlgebra ℤ G)) +
      augmentation G x • (1 : MonoidAlgebra ℤ G) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [coeff_add, Finsupp.sum_add_index' (by simp) (by intros; simp [add_smul]), map_add, add_smul]
    nth_rewrite 1 [hx, hy]
    abel
  | single g n =>
    rw [coeff_single, Finsupp.sum_single_index (by simp), augmentation_single, smul_sub]
    simp

private noncomputable def hom1 : MonoidAlgebra ℤ G →ₗ[ℤ] Additive (Abelianization G) where
  toFun x := x.coeff.sum (fun g n => n • (Additive.ofMul (Abelianization.of g)))
  map_add' x y := by
    rw [coeff_add, Finsupp.sum_add_index' (by simp) (by intros; simp [add_smul])]
  map_smul' c x := by
    simp only [coeff_smul, RingHom.id_apply]
    rw [Finsupp.sum_smul_index' (by simp), Finsupp.smul_sum]
    exact Finsupp.sum_congr fun i _ => mul_smul c _ _

private theorem hom1_single (g : G) (n : ℤ) :
    hom1 G (single g n) = n • Additive.ofMul (Abelianization.of g) := by
  simp [hom1, coeff_single, Finsupp.sum_single_index]

private theorem hom1_gen (g : G) :
    hom1 G (single g (1 : ℤ) - 1) = Additive.ofMul (Abelianization.of g) := by
  have : (1 : MonoidAlgebra ℤ G) = single 1 (1 : ℤ) := MonoidAlgebra.one_def
  rw [map_sub, this, hom1_single, hom1_single]
  simp

private theorem hom1_prod (g h : G) :
    hom1 G ((single g (1 : ℤ) - 1) * (single h (1 : ℤ) - 1)) = 0 := by
  have : (single g (1 : ℤ) - 1) * (single h (1 : ℤ) - 1) =
      (single (g * h) (1 : ℤ) - 1) - (single g (1 : ℤ) - 1) - (single h (1 : ℤ) - 1) := by
    simp only [sub_mul, mul_sub, mul_one, one_mul, MonoidAlgebra.single_mul_single]; abel
  rw [this, map_sub, map_sub, hom1_gen, hom1_gen, hom1_gen]
  simp

/-- Milne (p. 76): $I_G$ is a free $\mathbb Z$-module with basis $\{g - 1 \mid g \in G,\ g \neq 1\}$. Stated as:
these elements are linearly independent and span $I_G$. -/
@[kb "milne2020cft" "v4.03, Ch. II, §2, basis of the augmentation ideal, p. 76"]
theorem augmentationIdeal_basis :
    LinearIndependent ℤ (fun g : {g : G // g ≠ 1} => (single (g : G) (1 : ℤ) - 1 : MonoidAlgebra ℤ G)) ∧
      Submodule.span ℤ (Set.range fun g : {g : G // g ≠ 1} =>
        (single (g : G) (1 : ℤ) - 1 : MonoidAlgebra ℤ G)) = augmentationIdeal G := by
  have hspan : Submodule.span ℤ (Set.range fun g : {g : G // g ≠ 1} =>
        (single (g : G) (1 : ℤ) - 1 : MonoidAlgebra ℤ G)) = augmentationIdeal G := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact single_sub_one_mem G g
    · intro x hx
      have hx0 : augmentation G x = 0 := hx
      rw [aug_decomp G x, hx0, zero_smul, add_zero]
      refine Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ ?_
      by_cases hg : g = 1
      · subst hg; simp [MonoidAlgebra.one_def]
      · exact Submodule.subset_span ⟨⟨g, hg⟩, rfl⟩
  refine ⟨?_, hspan⟩
  let ρ : MonoidAlgebra ℤ G →ₗ[ℤ] ({g : G // g ≠ 1} →₀ ℤ) :=
    { toFun := fun x => Finsupp.comapDomain Subtype.val x.coeff Subtype.val_injective.injOn
      map_add' := fun x y => by
        ext j; simp [Finsupp.comapDomain_apply]
      map_smul' := fun c x => by
        ext j; simp [-zsmul_eq_mul, coeff_smul, Finsupp.comapDomain_apply] }
  have hρ : (ρ ∘ fun g : {g : G // g ≠ 1} => (single (g : G) (1 : ℤ) - 1 : MonoidAlgebra ℤ G)) =
      fun g => Finsupp.single g 1 := by
    funext i; ext j
    have hj : (j : G) ≠ 1 := j.2
    simp [ρ, Finsupp.comapDomain_apply, coeff_sub, coeff_single, MonoidAlgebra.one_def, hj]
    by_cases h : i = j
    · subst h; simp
    · have h' : (i : G) ≠ j := fun e => h (Subtype.ext e)
      rw [Finsupp.single_eq_of_ne h'.symm, Finsupp.single_eq_of_ne (Ne.symm h)]
  refine LinearIndependent.of_comp ρ ?_
  rw [hρ]
  exact (Finsupp.basisSingleOne (R := ℤ) (ι := {g : G // g ≠ 1})).linearIndependent

/-- $I_G^2 = I_G \cdot I_G$, the $\mathbb Z$-submodule of $\mathbb Z[G]$ spanned by products of two elements of
$I_G$ (p. 76). -/
noncomputable abbrev augmentationIdealSq : Submodule ℤ (MonoidAlgebra ℤ G) :=
  augmentationIdeal G * augmentationIdeal G

/-- $I_G / I_G^2$, as a quotient of the abelian group $I_G$. -/
noncomputable abbrev augQuot : Type :=
  augmentationIdeal G ⧸ (augmentationIdealSq G).comap (augmentationIdeal G).subtype

/-- **Lemma 2.6** (p. 76). The map $g \mapsto (g - 1) + I_G^2$ induces an isomorphism
$G / G^c = G^{ab} \to I_G / I_G^2$ (of abelian groups; $G^{ab}$ written additively). -/
@[kb "milne2020cft" "v4.03, Ch. II, Lemma 2.6, p. 76"]
theorem lemma_2_6 : ∃ e : Additive (Abelianization G) ≃+ augQuot G, ∀ g : G,
    e (Additive.ofMul (Abelianization.of g)) =
      Submodule.Quotient.mk ⟨single g (1 : ℤ) - 1, single_sub_one_mem G g⟩ := by
  obtain ⟨-, hspan⟩ := augmentationIdeal_basis G
  -- forward map
  let gen : G → augQuot G := fun g =>
    Submodule.Quotient.mk ⟨single g (1 : ℤ) - 1, single_sub_one_mem G g⟩
  have hgen : ∀ g h : G, gen (g * h) = gen g + gen h := by
    intro g h
    have hmem : (single g (1 : ℤ) - 1) * (single h (1 : ℤ) - 1) ∈ augmentationIdealSq G :=
      Submodule.mul_mem_mul (single_sub_one_mem G g) (single_sub_one_mem G h)
    have : (⟨single (g * h) (1 : ℤ) - 1, single_sub_one_mem G (g * h)⟩ : augmentationIdeal G) -
        (⟨single g (1 : ℤ) - 1, single_sub_one_mem G g⟩ + ⟨single h (1 : ℤ) - 1, single_sub_one_mem G h⟩)
        ∈ (augmentationIdealSq G).comap (augmentationIdeal G).subtype := by
      rw [Submodule.mem_comap]
      change (single (g * h) (1 : ℤ) - 1) - ((single g (1 : ℤ) - 1) + (single h (1 : ℤ) - 1)) ∈ augmentationIdealSq G
      have e : (single (g * h) (1 : ℤ) - 1) - ((single g (1 : ℤ) - 1) + (single h (1 : ℤ) - 1)) =
          (single g (1 : ℤ) - 1) * (single h (1 : ℤ) - 1) := by
        simp only [sub_mul, mul_sub, mul_one, one_mul, MonoidAlgebra.single_mul_single]; abel
      rw [e]; exact hmem
    simp only [gen]
    rw [← Submodule.Quotient.mk_add]
    exact (Submodule.Quotient.eq _).2 this
  let F : Abelianization G →* Multiplicative (augQuot G) :=
    Abelianization.lift
      { toFun := fun g => Multiplicative.ofAdd (gen g)
        map_one' := by
          have : gen 1 = 0 := by
            have := hgen 1 1
            simpa using this
          simpa using this
        map_mul' := fun g h => hgen g h }
  let fwd : Additive (Abelianization G) →+ augQuot G :=
    { toFun := fun a => Multiplicative.toAdd (F a.toMul)
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hfwd : ∀ g : G, fwd (Additive.ofMul (Abelianization.of g)) = gen g := by
    intro g; simp [fwd, F]; rfl
  -- backward map
  have hker : augmentationIdealSq G ≤ LinearMap.ker (hom1 G) := by
    show augmentationIdeal G * augmentationIdeal G ≤ _
    rw [← hspan, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    exact hom1_prod G a b
  let ψ : augQuot G →ₗ[ℤ] Additive (Abelianization G) :=
    Submodule.liftQ _ ((hom1 G).comp (augmentationIdeal G).subtype) (by
      intro x hx
      exact hker hx)
  have hψ : ∀ g : G, ψ (gen g) = Additive.ofMul (Abelianization.of g) := by
    intro g
    exact hom1_gen G g
  refine ⟨AddMonoidHom.toAddEquiv fwd ψ.toAddMonoidHom ?_ ?_, hfwd⟩
  · ext g
    show ψ (fwd (Additive.ofMul (Abelianization.of g))) = _
    rw [hfwd, hψ]
    rfl
  · ext q
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have key : ∀ x (hxs : x ∈ Submodule.span ℤ (Set.range fun g : {g : G // g ≠ 1} =>
        (single (g : G) (1 : ℤ) - 1 : MonoidAlgebra ℤ G))), ∀ hx : x ∈ augmentationIdeal G,
        fwd (hom1 G x) = (Submodule.Quotient.mk ⟨x, hx⟩ : augQuot G) := by
      intro x hxs
      induction hxs using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        intro hx'
        rw [hom1_gen, hfwd]
      | zero => intro hx'; simp; rfl
      | add x y _ _ ihx ihy =>
        intro hx'
        have hx1 : x ∈ augmentationIdeal G := hspan ▸ ‹x ∈ _›
        have hy1 : y ∈ augmentationIdeal G := hspan ▸ ‹y ∈ _›
        rw [map_add, map_add, ihx hx1, ihy hy1]
        rfl
      | smul n x _ ihx =>
        intro hx'
        have hx1 : x ∈ augmentationIdeal G := hspan ▸ ‹x ∈ _›
        rw [map_smul, map_zsmul, ihx hx1]
        rfl
    exact key x (hspan ▸ hx) hx


end NumberFieldKB.MilneCFT
