import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch4

/-!
# Milne, *Algebraic Number Theory*, Theorem 4.29, p. 82: basic lemmas

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Theorem 4.29, p. 82; bib key `milne2020ant`.

First lemmas towards `NumberFieldKB.MilneANT.QuadraticFormsIdealClasses`, for a quadratic number field `K` with
nontrivial automorphism `σ` and `δ² = d_K`: trace and norm in terms of `σ`; the orientation
`orient σ u v = u σ(v) - v σ(u)` of a `ℤ`-basis of a fractional ideal `𝔞` satisfies
`orient² = (N𝔞)² d_K`; oriented bases exist; the integral form `formOf 𝔞 b` attached to a basis; its `SL₂(ℤ)`-class
depends only on `𝔞` among oriented bases; and it is unchanged under `𝔞 ↦ α𝔞`, `b ↦ αb` for `N(α) > 0`.
-/

open NumberField Polynomial Module
open scoped nonZeroDivisors

namespace NumberFieldKB.MilneANT.Thm429

section Galois

variable {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (σ : K ≃ₐ[ℚ] K)
  (hσ : σ ≠ 1)

include hK hσ in
theorem aut_univ_eq [Fintype (K ≃ₐ[ℚ] K)] [DecidableEq (K ≃ₐ[ℚ] K)] :
    (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, σ} := by
  have hle : Nat.card (K ≃ₐ[ℚ] K) ≤ 2 := by
    have h1 : Nat.card (K ≃ₐ[ℚ] K) ≤ Nat.card (K →ₐ[ℚ] K) :=
      Nat.card_le_card_of_injective (fun f => (f : K →ₐ[ℚ] K)) (fun f g h => AlgEquiv.ext (fun x => by
        simpa using congrArg (fun φ : K →ₐ[ℚ] K => φ x) h))
    have h2 := card_algHom_le_finrank ℚ K K
    omega
  have hsub : ({1, σ} : Finset (K ≃ₐ[ℚ] K)) ⊆ Finset.univ := Finset.subset_univ _
  have hc : ({1, σ} : Finset (K ≃ₐ[ℚ] K)).card = 2 := Finset.card_pair (Ne.symm hσ)
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hc, Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact hle

include hK hσ in
theorem isGalois_of_quadratic : IsGalois ℚ K := by
  classical
  have : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  have hu := aut_univ_eq hK σ hσ
  apply IsGalois.of_card_aut_eq_finrank
  have : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by
    rw [← Finset.card_univ, hu, Finset.card_pair (Ne.symm hσ)]
  rw [Nat.card_eq_fintype_card, this, hK]

include hK hσ in
theorem trace_eq_add_sigma (x : K) : (Algebra.trace ℚ K x : K) = x + σ x := by
  classical
  have := isGalois_of_quadratic hK σ hσ
  have hu := aut_univ_eq hK σ hσ
  have h := trace_eq_sum_automorphisms (K := ℚ) (L := K) x
  rw [hu, Finset.sum_pair (Ne.symm hσ)] at h
  simpa using h

include hK hσ in
theorem norm_eq_mul_sigma (x : K) : (Algebra.norm ℚ x : K) = x * σ x := by
  classical
  have := isGalois_of_quadratic hK σ hσ
  have hu := aut_univ_eq hK σ hσ
  have h := Algebra.norm_eq_prod_automorphisms (K := ℚ) (L := K) x
  rw [hu, Finset.prod_pair (Ne.symm hσ)] at h
  simpa using h

end Galois

section Orient

variable {K : Type*} [Field K] [NumberField K]

/-- The orientation `u σ(v) - v σ(u)` of a pair `(u, v)`. -/
def orient (σ : K ≃ₐ[ℚ] K) (u v : K) : K := u * σ v - v * σ u

/-- The (rational) absolute norm `N𝔞` of a fractional ideal, as an element of `K`. -/
noncomputable abbrev N (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : K :=
  (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) : K)

theorem N_ne_zero (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : N 𝔞 ≠ 0 := by
  have : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact 𝔞.ne_zero
  exact Rat.cast_ne_zero.2 this

variable (hK : Module.finrank ℚ K = 2) (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (δ : K)
  (hδ : δ ^ 2 = (NumberField.discr K : K)) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

include hK hσ in
/-- `orient(b₀, b₁)² = (N𝔞)² d_K` for a `ℤ`-basis of `𝔞` (Milne, Thm. 4.29, p. 82). -/
@[kb "milne2020ant" "v3.08, Thm. 4.29, p. 82"]
theorem orient_sq
    (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    orient σ (b 0) (b 1) ^ 2 = (N 𝔞) ^ 2 * (NumberField.discr K : K) := by
  have hd := NormForm.discr_frac hK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) b
  have hD : Algebra.discr ℚ (fun i => (b i : K)) =
      Algebra.trace ℚ K ((b 0 : K) * b 0) * Algebra.trace ℚ K ((b 1 : K) * b 1)
        - Algebra.trace ℚ K ((b 0 : K) * b 1) ^ 2 := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, mul_comm (b 1 : K) (b 0 : K)]
    ring
  have h2 := congrArg (fun q : ℚ => (q : K)) (hD.symm.trans hd)
  push_cast at h2
  simp only [trace_eq_add_sigma hK σ hσ, map_mul] at h2
  unfold orient
  linear_combination h2

include hK hσ hδ in
theorem orient_eq_or
    (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    orient σ (b 0) (b 1) = δ * N 𝔞 ∨ orient σ (b 0) (b 1) = -(δ * N 𝔞) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [orient_sq hK σ hσ 𝔞 b, mul_pow, hδ, mul_comm]

theorem orient_swap (u v : K) : orient σ v u = -orient σ u v := by
  unfold orient; ring

include hK hσ hδ in
/-- Every fractional ideal has an oriented `ℤ`-basis: `orient(b₀, b₁) = δ N𝔞`. -/
@[kb "milne2020ant" "v3.08, Thm. 4.29, p. 82"]
theorem exists_oriented_basis :
    ∃ b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      orient σ (b 0) (b 1) = δ * N 𝔞 := by
  have hr : Module.finrank ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = 2 := by
    rw [fractionalIdeal_rank K 𝔞, RingOfIntegers.rank, hK]
  let b := Module.finBasisOfFinrankEq ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) hr
  rcases orient_eq_or hK σ hσ δ hδ 𝔞 b with h | h
  · exact ⟨b, h⟩
  · refine ⟨b.reindex (Equiv.swap 0 1), ?_⟩
    simp only [Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [orient_swap, h, neg_neg]

theorem orient_comb (p q r s : ℤ) (u v : K) :
    orient σ ((p : K) * u + (q : K) * v) ((r : K) * u + (s : K) * v) =
      ((p * s - q * r : ℤ) : K) * orient σ u v := by
  unfold orient
  simp only [map_add, map_mul, map_intCast]
  push_cast
  ring

end Orient

section Forms

variable {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
  (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- A `BinQF` is determined by its values on integer points. -/
theorem _root_.QuadFormsKB.BinQF.ext_of_eval {f g : QuadFormsKB.BinQF}
    (h : ∀ x y : ℤ, f.eval x y = g.eval x y) : f = g := by
  have h1 := h 1 0
  have h2 := h 0 1
  have h3 := h 1 1
  simp only [QuadFormsKB.BinQF.eval_eq] at h1 h2 h3
  refine QuadFormsKB.BinQF.ext_abc ?_ ?_ ?_ <;> nlinarith

/-- The integral binary quadratic form `Q_{b₀,b₁}` of a `ℤ`-basis `b` of `𝔞` (chosen from
`idealNormForm_integral`). -/
noncomputable def formOf
    (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    QuadFormsKB.BinQF :=
  Classical.choose (idealNormForm_integral hK 𝔞 b)

theorem formOf_disc
    (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    (formOf hK 𝔞 b).disc = NumberField.discr K :=
  (Classical.choose_spec (idealNormForm_integral hK 𝔞 b)).1

theorem formOf_eval
    (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) (x y : ℤ) :
    (QuadFormsKB.BinQF.eval (formOf hK 𝔞 b) x y : ℚ) =
      idealNormForm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (b 0) (b 1) x y :=
  (Classical.choose_spec (idealNormForm_integral hK 𝔞 b)).2 x y

omit [NumberField K] in
/-- Expansion of a basis vector in another basis. -/
theorem coe_basis_expand
    (b b' : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) (j : Fin 2) :
    ((b' j : ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) : K) =
      ((b.toMatrix b' 0 j : ℤ) : K) * (b 0 : K) + ((b.toMatrix b' 1 j : ℤ) : K) * (b 1 : K) := by
  have h := congrArg (fun z : ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) => (z : K))
    (b.sum_repr (b' j))
  simp only [Fin.sum_univ_two, Submodule.coe_add] at h
  rw [← h]
  simp [Basis.toMatrix_apply, zsmul_eq_mul]

variable (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (δ : K) (hδ : δ ^ 2 = (NumberField.discr K : K))

include hδ in
theorem delta_ne_zero : δ ≠ 0 := by
  intro h
  rw [h] at hδ
  have : (NumberField.discr K : K) = 0 := by rw [← hδ]; ring
  exact NumberField.discr_ne_zero K (by exact_mod_cast this)

include hK hδ in
/-- Two oriented bases of the same fractional ideal give `SL₂(ℤ)`-equivalent forms. -/
@[kb "milne2020ant" "v3.08, Thm. 4.29, p. 82"]
theorem sLEquiv_formOf_of_oriented
    (b b' : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
    (hb : orient σ (b 0) (b 1) = δ * N 𝔞) (hb' : orient σ (b' 0) (b' 1) = δ * N 𝔞) :
    QuadFormsKB.Binary.SLEquiv (formOf hK 𝔞 b) (formOf hK 𝔞 b') := by
  set M := b.toMatrix b' with hM
  have hne : δ * N 𝔞 ≠ 0 := mul_ne_zero (delta_ne_zero δ hδ) (N_ne_zero 𝔞)
  have hdet : M 0 0 * M 1 1 - M 1 0 * M 0 1 = 1 := by
    have h := orient_comb σ (M 0 0) (M 1 0) (M 0 1) (M 1 1) (b 0 : K) (b 1 : K)
    rw [← coe_basis_expand 𝔞 b b' 0, ← coe_basis_expand 𝔞 b b' 1, hb', hb] at h
    have h2 : (((M 0 0 * M 1 1 - M 1 0 * M 0 1 : ℤ) : K) - 1) * (δ * N 𝔞) = 0 := by
      linear_combination -h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact_mod_cast sub_eq_zero.1 h3
    · exact absurd h3 hne
  rw [QuadFormsKB.Binary.sLEquiv_iff]
  refine ⟨M 0 0, M 0 1, M 1 0, M 1 1, by linear_combination hdet, ?_⟩
  apply QuadFormsKB.BinQF.ext_of_eval
  intro x y
  apply Int.cast_injective (α := ℚ)
  rw [QuadFormsKB.BinQF.eval_subst, formOf_eval, formOf_eval]
  unfold idealNormForm
  congr 1
  congr 1
  rw [coe_basis_expand 𝔞 b b' 0, coe_basis_expand 𝔞 b b' 1]
  push_cast
  rw [hM]
  ring

/-- The unit of fractional ideals `(α)` for `α ≠ 0`. -/
noncomputable def spanUnit (α : K) (hα0 : α ≠ 0) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ α)
    (FractionalIdeal.spanSingleton_ne_zero_iff.2 hα0)

theorem mem_mul_spanUnit (α : K) (hα0 : α ≠ 0) (y : K) :
    y ∈ ((𝔞 * spanUnit α hα0 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∃ z ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K), α * z = y := by
  have : ((𝔞 * spanUnit α hα0 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ α * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [Units.val_mul, mul_comm]
    rfl
  rw [this]
  rw [FractionalIdeal.mem_singleton_mul (S := (𝓞 K)⁰) (P := K)
    (I := (𝔞 : FractionalIdeal (𝓞 K)⁰ K))]
  exact exists_congr fun z => and_congr_right fun _ => eq_comm

/-- Multiplication by `α`, a `ℤ`-linear map `𝔞 → 𝔞 * (α)`. -/
noncomputable def smulMap (α : K) (hα0 : α ≠ 0) :
    ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) →ₗ[ℤ]
      (((𝔞 * spanUnit α hα0 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) where
  toFun x := ⟨α * (x : K), (mem_mul_spanUnit 𝔞 α hα0 _).2 ⟨x, x.2, rfl⟩⟩
  map_add' x y := by ext; simp [mul_add]
  map_smul' n x := by
    ext
    simp only [Submodule.coe_smul_of_tower, RingHom.id_apply]
    rw [zsmul_eq_mul, zsmul_eq_mul]
    ring

theorem smulMap_bijective (α : K) (hα0 : α ≠ 0) : Function.Bijective (smulMap 𝔞 α hα0) := by
  constructor
  · intro x y h
    have := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel₀ hα0 this)
  · intro y
    obtain ⟨z, hz, hzy⟩ := (mem_mul_spanUnit 𝔞 α hα0 _).1 y.2
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩

/-- The basis `α • b` of `α𝔞 = 𝔞 * (α)`. -/
noncomputable def smulBasis (α : K) (hα0 : α ≠ 0)
    (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    Basis (Fin 2) ℤ (((𝔞 * spanUnit α hα0 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
  b.map (LinearEquiv.ofBijective (smulMap 𝔞 α hα0) (smulMap_bijective 𝔞 α hα0))

theorem smulBasis_apply (α : K) (hα0 : α ≠ 0)
    (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) (i : Fin 2) :
    ((smulBasis 𝔞 α hα0 b i : _) : K) = α * (b i : K) := by
  simp [smulBasis, smulMap]

theorem absNorm_mul_spanUnit (α : K) (hα0 : α ≠ 0) (hpos : 0 < Algebra.norm ℚ α) :
    FractionalIdeal.absNorm ((𝔞 * spanUnit α hα0 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) * Algebra.norm ℚ α := by
  rw [Units.val_mul, map_mul]
  congr 1
  show FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ α) = _
  rw [FractionalIdeal.absNorm_span_singleton, abs_of_pos hpos]

include hK hσ in
/-- Replacing `𝔞` by `α𝔞` with `N(α) > 0` and `b` by `α b` preserves orientation and the form. -/
@[kb "milne2020ant" "v3.08, Thm. 4.29, p. 82"]
theorem formOf_smul (α : K) (hα0 : α ≠ 0) (hpos : 0 < Algebra.norm ℚ α)
    (b : Basis (Fin 2) ℤ ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
    (hb : orient σ (b 0) (b 1) = δ * N 𝔞) :
    orient σ (smulBasis 𝔞 α hα0 b 0) (smulBasis 𝔞 α hα0 b 1) =
        δ * N (𝔞 * spanUnit α hα0) ∧
      formOf hK (𝔞 * spanUnit α hα0) (smulBasis 𝔞 α hα0 b) = formOf hK 𝔞 b := by
  have hN : N (𝔞 * spanUnit α hα0) = N 𝔞 * (Algebra.norm ℚ α : K) := by
    unfold N
    rw [absNorm_mul_spanUnit 𝔞 α hα0 hpos]
    push_cast
    rfl
  constructor
  · rw [smulBasis_apply, smulBasis_apply, hN]
    have h1 := norm_eq_mul_sigma hK σ hσ α
    have h2 : orient σ (α * (b 0 : K)) (α * (b 1 : K)) = (Algebra.norm ℚ α : K) * orient σ (b 0) (b 1) := by
      rw [h1]; unfold orient; simp only [map_mul]; ring
    rw [h2, hb]; ring
  · apply QuadFormsKB.BinQF.ext_of_eval
    intro x y
    apply Int.cast_injective (α := ℚ)
    rw [formOf_eval, formOf_eval]
    unfold idealNormForm
    rw [absNorm_mul_spanUnit 𝔞 α hα0 hpos, smulBasis_apply, smulBasis_apply]
    have hnz : Algebra.norm ℚ α ≠ 0 := hpos.ne'
    have hn0 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]
      exact 𝔞.ne_zero
    have : α * (b 0 : K) * (x : ℚ) + α * (b 1 : K) * (y : ℚ) =
        α * ((b 0 : K) * (x : ℚ) + (b 1 : K) * (y : ℚ)) := by ring
    rw [this, map_mul]
    field_simp

end Forms

end NumberFieldKB.MilneANT.Thm429
