import NumberFieldKB.MilneCFT.Ch8.ReciprocityLaw
import NumberFieldKB.MilneCFT.Ch5ConductorUncond
import NumberFieldKB.MilneCFT.Ch5RatIdeles
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star

/-!
# Milne, *Class Field Theory*, Chapter VIII, 5.7: the form `Item5_7NoRoot` without $\zeta_n \in K$ is false

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`: Chapter VIII,
5.7 (p. 246).

Milne's 5.7, $(b,a)_v = (a,b)_v^{-1}$, is stated for a number field $K$ containing a primitive $n$-th root of unity
(Milne's standing hypothesis in §5; not an erratum). The statement `Ch8.Item5_7 K n` now carries it (and is proved in
`Item57Uncond.lean`); the earlier form `Ch8.Item5_7NoRoot K n` omitted it and fails (`not_item5_7_rat`): take
$K = \mathbb Q$, $n = 4$, $L_a = L_b = \mathbb Q(i)$, $a = 1$, $\alpha = i$, $b = -4$, $\beta = 1 + i$ (so $\alpha^4 = a$,
$\beta^4 = b$), and Tau Ceti's idèlic Artin map for both. At the real place $w$, $b < 0$ and $w$ ramifies in
$\mathbb Q(i)$, so the Artin symbol of $b_w$ is complex conjugation and the symbol `hilbertArtinInf` of $(\alpha, b)$ is
$\bar\imath/i = -1$, while that of $(\beta, a)$ is $1$ ($a = 1$). The product is $-1 \neq 1$.
-/

open NumberField IsDedekindDomain

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

local notation "Lq" => CyclotomicField 4 ℚ

instance : IsCyclotomicExtension {4} ℚ Lq := CyclotomicField.isCyclotomicExtension 4 ℚ

instance : IsAbelianGalois ℚ Lq := IsCyclotomicExtension.isAbelianGalois {4} ℚ Lq

/-- The primitive fourth root of unity `i` of `ℚ(i)`. -/
abbrev iq : Lq := IsCyclotomicExtension.zeta 4 ℚ Lq

theorem iq_spec : IsPrimitiveRoot iq 4 := IsCyclotomicExtension.zeta_spec 4 ℚ Lq

theorem iq_sq : iq ^ 2 = -1 := by
  have := iq_spec.pow_eq_one
  have h2 : iq ^ 2 ≠ 1 := iq_spec.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h : (iq ^ 2 - 1) * (iq ^ 2 + 1) = 0 := by ring_nf; rw [show iq ^ 4 = 1 from this]; ring
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · exact eq_neg_of_add_eq_zero_left h

theorem finrank_Lq : Module.finrank ℚ Lq = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 4) Lq (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide

theorem adjoin_iq : IntermediateField.adjoin ℚ {iq} = ⊤ := by
  apply IntermediateField.toSubalgebra_injective
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic iq),
    IntermediateField.top_toSubalgebra]
  exact IsCyclotomicExtension.adjoin_primitive_root_eq_top iq_spec

/-- A nontrivial automorphism of `ℚ(i)` sends `i` to `-i`. -/
theorem apply_iq_of_ne_one (σ : Gal(Lq/ℚ)) (hσ : σ ≠ 1) : σ iq = -iq := by
  have h1 : (σ iq) ^ 2 = -1 := by rw [← map_pow, iq_sq, map_neg, map_one]
  have h2 : (σ iq - iq) * (σ iq + iq) = 0 := by ring_nf; rw [h1, iq_sq]; ring
  rcases mul_eq_zero.1 h2 with h | h
  · refine absurd ?_ hσ
    apply AlgEquiv.coe_toAlgHom_injective
    refine AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top iq_spec) ?_
    intro x hx
    rw [Set.mem_singleton_iff.1 hx]
    simpa using sub_eq_zero.1 h
  · exact eq_neg_of_add_eq_zero_left h

/-- The Galois group of `ℚ(i)` has order 2, so every square in it is trivial. -/
theorem sq_eq_one_Lq (σ : Gal(Lq/ℚ)) : σ ^ 2 = 1 := by
  have hcard : Nat.card Gal(Lq/ℚ) = 2 := by
    rw [← finrank_Lq, ← IsGalois.card_aut_eq_finrank]
  rw [← hcard]
  exact pow_card_eq_one'

theorem ramifiesIn_Lq (w : InfinitePlace ℚ) : InfinitePlace.RamifiesIn Lq w := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact ramifiesIn_infinite 4 Lq (by norm_num)

theorem choose_eq_of_eq {y : Lq} (hy : y ≠ 0) {x : Lq} {c : ℚ} (hx : x = algebraMap ℚ Lq c * y)
    (h : ∃ μ : ℚ, x = algebraMap ℚ Lq μ * y) : h.choose = c := by
  have h1 : algebraMap ℚ Lq c * y = algebraMap ℚ Lq h.choose * y := hx.symm.trans h.choose_spec
  exact (algebraMap ℚ Lq).injective (mul_right_cancel₀ hy h1).symm

/-- **`Item5_7NoRoot` is false** (Milne, *CFT*, VIII, 5.7, p. 246; see the module docstring): without the
hypothesis $\zeta_n \in K$, the skew symmetry fails for $K = \mathbb Q$, $n = 4$ at the real place. -/
@[kb "milne2020cft" "Ch. VIII, 5.7 (counterexample to the named statement without ζ_n ∈ K)"]
theorem not_item5_7_rat : ¬ Item5_7NoRoot ℚ 4 := by
  intro h
  let φ := idelicArtinTauCeti (K := ℚ) Lq
  let β : Lq := 1 + iq
  have hα : iq ^ 4 = algebraMap ℚ Lq ((1 : ℚˣ) : ℚ) := by simpa using iq_spec.pow_eq_one
  let b : ℚˣ := Units.mk0 (-4 : ℚ) (by norm_num)
  have hβ : β ^ 4 = algebraMap ℚ Lq (b : ℚ) := by
    have : β ^ 4 = (1 + iq) ^ 4 := rfl
    rw [this, Units.val_mk0, map_neg, map_ofNat]
    linear_combination (iq ^ 2 + 4 * iq + 5) * iq_sq
  have hadjα : IntermediateField.adjoin ℚ {iq} = ⊤ := adjoin_iq
  have hadjβ : IntermediateField.adjoin ℚ {β} = ⊤ := by
    rw [← hadjα]
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact add_mem (one_mem _) (IntermediateField.subset_adjoin _ _ rfl)
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have : iq = β - 1 := by ring
      rw [this]
      exact sub_mem (IntermediateField.subset_adjoin _ _ rfl) (one_mem _)
  obtain ⟨-, hinf⟩ := h.skew Lq Lq 1 b iq β hα hβ hadjα hadjβ φ φ
    (isIdelicArtinMap_tauCeti Lq) (isIdelicArtinMap_tauCeti Lq)
    (idelicArtinTauCeti_principal Lq) (idelicArtinTauCeti_principal Lq)
  have hw := hinf Rat.infinitePlace
  have hβ0 : β ≠ 0 := by
    intro h0
    have : iq = -1 := by linear_combination h0
    have h2 := iq_sq
    rw [this] at h2
    norm_num at h2
  have hi0 : iq ≠ 0 := iq_spec.ne_zero (by norm_num)
  -- the symbol of `(β, 1)` is `1`
  have hA : hilbertArtinInf Lq φ β Rat.infinitePlace 1 = 1 := by
    have hex : ∃ μ : ℚ, φ (IdeleGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace
        (Units.map (algebraMap ℚ _).toMonoidHom 1)) β = algebraMap ℚ Lq μ * β :=
      ⟨1, by simp⟩
    unfold hilbertArtinInf
    rw [dif_pos hex]
    exact choose_eq_of_eq hβ0 (by simp) hex
  -- the symbol of `(i, -4)` is `-1`
  have hσ : φ (IdeleGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace
      (Units.map (algebraMap ℚ _).toMonoidHom b)) ≠ 1 := by
    have hb : b = -1 * (Units.mk0 (2 : ℚ) (by norm_num)) ^ 2 := by
      ext; simp [b]; norm_num
    rw [hb, map_mul, map_pow, map_mul, map_pow, map_mul, map_pow, sq_eq_one_Lq, mul_one]
    have hm : Units.map (algebraMap ℚ Rat.infinitePlace.Completion).toMonoidHom (-1) = -1 := by
      ext; simp
    rw [hm]
    exact idelicArtinTauCeti_ofCompletion_neg_one_ne_one Lq Rat.infinitePlace (ramifiesIn_Lq _)
  have hB : hilbertArtinInf Lq φ iq Rat.infinitePlace b = -1 := by
    have happ := apply_iq_of_ne_one _ hσ
    have hex : ∃ μ : ℚ, φ (IdeleGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace
        (Units.map (algebraMap ℚ _).toMonoidHom b)) iq = algebraMap ℚ Lq μ * iq :=
      ⟨-1, by rw [happ]; simp⟩
    unfold hilbertArtinInf
    rw [dif_pos hex]
    exact choose_eq_of_eq hi0 (by rw [happ]; simp) hex
  rw [hA, hB] at hw
  norm_num at hw

end NumberFieldKB.MilneCFT.Ch8
