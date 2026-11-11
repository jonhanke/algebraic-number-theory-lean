import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch4Thm429Surj
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.TotallyPositive

/-!
# Milne, *Algebraic Number Theory*, Theorem 4.29, p. 82: assembly

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Theorem 4.29, p. 82; bib key `milne2020ant`.

The map `𝔞 ↦ [Q_{b₀,b₁}]` (for an oriented `ℤ`-basis `b` of `𝔞`) is well defined on the narrow class group
(`cls_mul_tpp`), injective (`mk_eq_of_sLEquiv`, `Ch4Thm429Inj.lean`) and surjective (`exists_of_form`,
`Ch4Thm429Surj.lean`). This proves the named statement `QuadraticFormsIdealClasses` (`quadraticFormsIdealClasses`).

The norm of a nonzero totally positive element is positive by the ported Tau Ceti
`NumberField.norm_pos_of_isTotallyPositive`.
-/

open NumberField Module
open scoped nonZeroDivisors

namespace NumberFieldKB.MilneANT.Thm429

section Assembly

variable {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (σ : K ≃ₐ[ℚ] K)
  (hσ : σ ≠ 1) (δ : K) (hδ : δ ^ 2 = (NumberField.discr K : K))

/-- A nonzero element positive at every real embedding has positive norm. -/
theorem norm_pos_of_forall (α : K) (hα : α ≠ 0) (h : ∀ ρ : K →+* ℝ, 0 < ρ α) :
    0 < Algebra.norm ℚ α :=
  NumberField.norm_pos_of_isTotallyPositive hα (fun _ _ => h _)

include hδ in
/-- If `d_K < 0` there is no real embedding (`ρ(δ)² = d_K`). -/
theorem no_real_of_discr_neg (hd : NumberField.discr K < 0) (ρ : K →+* ℝ) : False := by
  have h := congrArg ρ hδ
  rw [map_pow, map_intCast] at h
  have h0 : (0 : ℝ) ≤ (NumberField.discr K : ℝ) := h ▸ sq_nonneg _
  have : (0 : ℤ) ≤ NumberField.discr K := by exact_mod_cast h0
  omega

include hδ in
/-- For `d_K < 0` the form of a basis is positive definite (its `a` coefficient is `N(b₀)/N𝔞 > 0`). -/
theorem formOf_a_pos (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
    (hd : NumberField.discr K < 0) : 0 < (formOf hK 𝔞 b).a := by
  have h := formOf_eval hK 𝔞 b 1 0
  rw [QuadFormsKB.BinQF.eval_eq] at h
  unfold idealNormForm at h
  have hb0 : (b 0 : K) ≠ 0 := by
    intro h0
    exact b.ne_zero 0 (Subtype.ext h0)
  have hN : 0 < Algebra.norm ℚ (b 0 : K) :=
    norm_pos_of_forall _ hb0 (fun ρ => (no_real_of_discr_neg δ hδ hd ρ).elim)
  have hA : 0 < FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
    refine lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm ?_)
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact 𝔞.ne_zero
  have hq : (0 : ℚ) < ((formOf hK 𝔞 b).a : ℚ) := by
    norm_num at h
    rw [h]
    exact mul_pos (inv_pos.2 hA) hN
  exact_mod_cast hq

include hδ in
/-- The form of a basis, as an element of `FormsOfDisc d_K`. -/
noncomputable def formsOf (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    FormsOfDisc (NumberField.discr K) :=
  ⟨formOf hK 𝔞 b, formOf_disc hK 𝔞 b, formOf_a_pos hK δ hδ 𝔞 b⟩

/-- The relation on `FormsOfDisc d_K` used in the statement. -/
abbrev Rel : FormsOfDisc (NumberField.discr K) → FormsOfDisc (NumberField.discr K) → Prop :=
  fun f g => QuadFormsKB.Binary.SLEquiv f.1 g.1

/-- The class of `𝔞`: the class of the form of a chosen oriented basis. -/
noncomputable def cls (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Quot (Rel (K := K)) :=
  Quot.mk _ (formsOf hK δ hδ 𝔞 (Classical.choose (exists_oriented_basis hK σ hσ δ hδ 𝔞)))

/-- `cls 𝔞` is the class of the form of any oriented basis. -/
theorem cls_eq (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
    (hb : orient σ (b 0) (b 1) = δ * N 𝔞) :
    cls hK σ hσ δ hδ 𝔞 = Quot.mk _ (formsOf hK δ hδ 𝔞 b) :=
  Quot.sound (sLEquiv_formOf_of_oriented hK 𝔞 σ δ hδ _ b
    (Classical.choose_spec (exists_oriented_basis hK σ hσ δ hδ 𝔞)) hb)

/-- `cls (𝔞 (α)) = cls 𝔞` for `N α > 0`. -/
theorem cls_mul_spanUnit (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α : K) (hα0 : α ≠ 0)
    (hpos : 0 < Algebra.norm ℚ α) :
    cls hK σ hσ δ hδ (𝔞 * spanUnit α hα0) = cls hK σ hσ δ hδ 𝔞 := by
  obtain ⟨b, hb⟩ := exists_oriented_basis hK σ hσ δ hδ 𝔞
  obtain ⟨h1, h2⟩ := formOf_smul hK 𝔞 σ hσ δ α hα0 hpos b hb
  rw [cls_eq hK σ hσ δ hδ _ _ h1, cls_eq hK σ hσ δ hδ 𝔞 b hb]
  congr 1
  exact Subtype.ext h2

/-- The ideals `u` with `cls (𝔞 u) = cls 𝔞` for every `𝔞` form a subgroup. -/
def stab : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier := {u | ∀ 𝔞, cls hK σ hσ δ hδ (𝔞 * u) = cls hK σ hσ δ hδ 𝔞}
  one_mem' := fun 𝔞 => by rw [mul_one]
  mul_mem' := fun {u v} hu hv 𝔞 => by rw [← mul_assoc, hv, hu]
  inv_mem' := fun {u} hu 𝔞 => by
    have := hu (𝔞 * u⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

/-- Totally positive principal ideals do not change `cls`. -/
theorem tpp_le_stab : totallyPositivePrincipal K ≤ stab hK σ hσ δ hδ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨α, hα0, hpos, hu⟩ 𝔞
  have hu' : u = spanUnit α hα0 := Units.ext hu
  subst hu'
  exact cls_mul_spanUnit hK σ hσ δ hδ 𝔞 α hα0 (norm_pos_of_forall α hα0 hpos)

/-- The map `Cl⁺(K) → {forms of discriminant d_K}/SL₂(ℤ)`. -/
noncomputable def phi : NarrowClassGroup K → Quot (Rel (K := K)) := fun x =>
  Quotient.liftOn' x (cls hK σ hσ δ hδ) (fun 𝔞 𝔟 h => by
    have h' : 𝔞⁻¹ * 𝔟 ∈ totallyPositivePrincipal K := QuotientGroup.leftRel_apply.mp h
    have := tpp_le_stab hK σ hσ δ hδ h' 𝔞
    rw [mul_inv_cancel_left] at this
    exact this.symm)

theorem phi_mk (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    phi hK σ hσ δ hδ (QuotientGroup.mk 𝔞) = cls hK σ hσ δ hδ 𝔞 := rfl

theorem sLEquiv_of_eqvGen {f g : FormsOfDisc (NumberField.discr K)} (h : Relation.EqvGen Rel f g) :
    QuadFormsKB.Binary.SLEquiv f.1 g.1 := by
  induction h with
  | rel _ _ h => exact h
  | refl f => exact QuadFormsKB.Binary.SLEquiv.refl f.1
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem phi_injective : Function.Injective (phi hK σ hσ δ hδ) := by
  intro x y hxy
  obtain ⟨𝔞, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨𝔟, rfl⟩ := QuotientGroup.mk_surjective y
  have hxy : cls hK σ hσ δ hδ 𝔞 = cls hK σ hσ δ hδ 𝔟 := hxy
  obtain ⟨b, hb⟩ := exists_oriented_basis hK σ hσ δ hδ 𝔞
  obtain ⟨c, hc⟩ := exists_oriented_basis hK σ hσ δ hδ 𝔟
  rw [cls_eq hK σ hσ δ hδ 𝔞 b hb, cls_eq hK σ hσ δ hδ 𝔟 c hc] at hxy
  have h1 := Quot.eqvGen_exact hxy
  have h2 := sLEquiv_of_eqvGen h1
  exact mk_eq_of_sLEquiv hK σ hσ δ hδ 𝔞 𝔟 b c hb hc h2

theorem phi_surjective : Function.Surjective (phi hK σ hσ δ hδ) := by
  intro q
  induction q using Quot.ind with | mk f => ?_
  obtain ⟨𝔞, b, hb, hf⟩ := exists_of_form hK σ hσ δ hδ f
  refine ⟨QuotientGroup.mk 𝔞, ?_⟩
  rw [phi_mk, cls_eq hK σ hσ δ hδ 𝔞 b hb]
  congr 1
  exact Subtype.ext hf

end Assembly

end Thm429

open Thm429 in
/-- **Theorem 4.29** (Milne, p. 82), proved: for a quadratic field `K`, oriented bases give a bijection between the
narrow class group and `SL₂(ℤ)`-classes of integral binary quadratic forms of discriminant `d_K` (positive definite
when `d_K < 0`). The sign normalization of `δ` through `φ` is not needed for the proof. -/
@[kb "milne2020ant" "v3.08, Thm. 4.29, p. 82"]
theorem quadraticFormsIdealClasses : QuadraticFormsIdealClasses where
  bijection := by
    intro K _ _ hK σ hσ _φ δ hδ _ _
    refine ⟨Equiv.ofBijective _ ⟨phi_injective hK σ hσ δ hδ, phi_surjective hK σ hσ δ hδ⟩, ?_⟩
    intro 𝔞 b hb f hf
    have hfe : f.1 = formOf hK 𝔞 b := by
      apply QuadFormsKB.BinQF.ext_of_eval
      intro x y
      apply Int.cast_injective (α := ℚ)
      rw [hf x y, formOf_eval]
    show phi hK σ hσ δ hδ (QuotientGroup.mk 𝔞) = _
    rw [phi_mk, cls_eq hK σ hσ δ hδ 𝔞 b hb]
    congr 1
    exact (Subtype.ext hfe).symm

end NumberFieldKB.MilneANT
