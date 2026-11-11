import NumberFieldKB.MilneCFT.Ch8.ArtinInductionUncond
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Brauer's induction theorem: proved pieces (Milne, *CFT*, VIII, §10, p. 262)

`BrauerInduction` itself is **not** proved here. This file proves the formal skeleton of the standard argument
(Serre, *Linear Representations*, §10–11) on class functions:

* `indFun_mul_class`: Frobenius reciprocity `χ · Ind_H f = Ind_H (χ|_H · f)` for a class function `χ`;
* `indFun_zsmul`, `indFun_mem_zspan`: `Ind_H` is `ℤ`-linear and maps the `ℤ`-span of the characters of `H`
  into the `ℤ`-span in the statement of `BrauerInduction`;
* `brauer_reduction`: if the constant function `1` is an integral combination `∑ nᵢ Ind_{Hᵢ} φᵢ` and each
  `χ|_{Hᵢ} · φᵢ` is an integral combination of characters of `Hᵢ`, then `χ` is in the `ℤ`-span of
  `BrauerInduction`.

Missing (precisely): the Brauer/Solomon input, `BrauerData` below, for the trace `χ` of every representation:
that `1 = ∑ nᵢ Ind_{Hᵢ} φᵢ` with `Hᵢ` elementary and `χ|_{Hᵢ} φᵢ` in the `ℤ`-span of linear characters of `Hᵢ`
(the latter needs: characters of elementary, hence nilpotent, groups are monomial). Neither is in Mathlib.
-/

open scoped Classical

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

lemma indFun_mul_class {G : Type} [Group G] [Fintype G] (H : Subgroup G) (χ : G → ℂ)
    (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g) (f : H → ℂ) (g : G) :
    indFun H (fun h : H => χ (h : G) * f h) g = χ g * indFun H f g := by
  unfold indFun
  rw [mul_left_comm (χ g)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : x * g * x⁻¹ ∈ H
  · rw [dif_pos h, dif_pos h]
    show χ (x * g * x⁻¹) * f ⟨_, h⟩ = _
    rw [hχ]
  · simp [h]

lemma indFun_zsmul {G : Type} [Group G] [Fintype G] (H : Subgroup G) (a : ℤ) (f : H → ℂ) :
    indFun H (a • f) = a • indFun H f := by
  funext g
  simp only [indFun, Pi.smul_apply, zsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp
  ring

/-- The target of `BrauerInduction`. -/
abbrev brauerSpan (G : Type) [Group G] [Fintype G] : Submodule ℤ (G → ℂ) :=
  Submodule.span ℤ {f : G → ℂ | ∃ (H : Subgroup G) (ψ : H →* ℂˣ),
    f = fun g => (Fintype.card H : ℂ)⁻¹ *
      ∑ x : G, if h : x * g * x⁻¹ ∈ H then (ψ ⟨_, h⟩ : ℂ) else 0}

lemma indFun_mem_zspan {G : Type} [Group G] [Fintype G] (H : Subgroup G) {f : H → ℂ}
    (hf : f ∈ Submodule.span ℤ (charSet H)) : indFun H f ∈ brauerSpan G := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, rfl⟩ := hx
    refine Submodule.subset_span ⟨H, ψ, ?_⟩
    funext g
    simp [indFun, Nat.card_eq_fintype_card]
  | zero => rw [indFun_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : indFun H (x + y) = indFun H x + indFun H y := indFun_add H x y
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [indFun_zsmul]; exact Submodule.smul_mem _ _ hx

/-- The reduction step of Brauer's argument. -/
theorem brauer_reduction {G : Type} [Group G] [Fintype G] (χ : G → ℂ)
    (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g) {ι : Type} (s : Finset ι) (H : ι → Subgroup G)
    (n : ι → ℤ) (φ : ∀ i, H i → ℂ)
    (h1 : ∀ g, ∑ i ∈ s, (n i : ℂ) * indFun (H i) (φ i) g = 1)
    (hmem : ∀ i ∈ s, (fun h : H i => χ (h : G) * φ i h) ∈ Submodule.span ℤ (charSet (H i))) :
    χ ∈ brauerSpan G := by
  have : χ = ∑ i ∈ s, n i • indFun (H i) (fun h : H i => χ (h : G) * φ i h) := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply]
    simp_rw [indFun_mul_class (H _) χ hχ, zsmul_eq_mul]
    calc χ g = χ g * ∑ i ∈ s, (n i : ℂ) * indFun (H i) (φ i) g := by rw [h1 g, mul_one]
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (indFun_mem_zspan (H i) (hmem i hi))

/-- **Brauer's elementary-subgroup data** (named statement; the core of Brauer's induction theorem, Serre, *Linear
Representations of Finite Groups*, §§10–11; Milne, *CFT*, VIII, §10, p. 262): for the trace $\chi$ of every complex
representation of a finite group $G$ there are subgroups $H_i$, integers $m_i$ and functions $\varphi_i$ on $H_i$ with
$1 = \sum_i m_i\,\mathrm{Ind}_{H_i}\varphi_i$ and $\chi|_{H_i}\varphi_i$ in the $\mathbb Z$-span of the linear characters
of $H_i$ (Brauer–Solomon: $1$ is an integral combination of characters induced from elementary subgroups; characters of
elementary, hence nilpotent, groups are monomial). Missing from Mathlib: irreducible characters and their orthogonality,
the Brauer–Solomon argument, monomiality of nilpotent groups. -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 262 (Brauer's theorem, elementary-subgroup data; input)"]
structure BrauerData : Prop where
  data : ∀ (G : Type) [Group G] [Fintype G] (n : ℕ) (ρ : G →* GL (Fin n) ℂ),
    ∃ (ι : Type) (s : Finset ι) (H : ι → Subgroup G) (m : ι → ℤ) (φ : ∀ i, H i → ℂ),
      (∀ g, ∑ i ∈ s, (m i : ℂ) * indFun (H i) (φ i) g = 1) ∧
      ∀ i ∈ s, (fun h : H i => Matrix.trace ((ρ (h : G) : GL (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ) * φ i h) ∈ Submodule.span ℤ (charSet (H i))

variable {G' : Type} in
/-- **Brauer's induction theorem from the elementary-subgroup data** (Milne, *CFT*, VIII, §10, p. 262): Frobenius
reciprocity (`indFun_mul_class`) and `brauer_reduction`. -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 262 (Brauer's induction theorem, from BrauerData)"]
theorem brauerInduction_of_brauerData (h : BrauerData) : BrauerInduction where
  span G _ _ _ n ρ := by
    obtain ⟨ι, s, H, m, φ, h1, hmem⟩ := h.data G n ρ
    refine brauer_reduction _ (fun x g => ?_) s H m φ h1 hmem
    simp only [map_mul, map_inv, Units.val_mul]
    rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

end NumberFieldKB.MilneCFT.Ch8
