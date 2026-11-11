import NumberFieldKB.MilneCFT.Ch8.Powers
import NumberFieldKB.MilneCFT.Ch8.Reciprocity
import NumberFieldKB.MilneCFT.Ch5IdelicReciprocityTauCeti
import NumberFieldKB.MilneCFT.Ch5Density
import NumberFieldKB.WeilBNT.IdeleCharacterExtension
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Algebra.Group.Units

/-!
# The Kummer character $\chi_D$ of Milne, *CFT*, VIII, Example 10.1

For $L = K(D^{1/3})$ and $\kappa(g) = \sigma(g(\delta)/\delta)$, the idèle character $\kappa \circ \psi_{L/K}$
(`idelicArtinTauCeti`): at a prime $v \notin S(3, D)$ it is trivial on the units and takes the value
$\sigma(D/\mathfrak p_v)_3$ on a uniformizer (`powerResidue`).
-/

open NumberField IsDedekindDomain NumberFieldKB.WeilBNT NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.Ch8 NumberFieldKB.Chebotarev
open scoped nonZeroDivisors IsMulCommutative

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace NumberFieldKB.MilneCFT.Ch8.Ex101

variable {K : Type} [Field K] [NumberField K]

/-- The Artin map is trivial on the units at an unramified prime. -/
theorem artin_unit {L : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ unramifiedPrimes K L) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    idelicArtinTauCeti L (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) = 1 := by
  obtain ⟨n, hn⟩ := idelicArtinTauCeti_local_ramified (K := K) L
  refine hn _ (fun v' hv' => ?_) (fun v' hv' => ?_) (fun w hw hr => ?_)
  · by_cases h : v' = v
    · subst h; rw [ofAdicCompletion_finAt_self]; exact hu
    · rw [ofAdicCompletion_finAt_ne h]; simp
  · have h : v' ≠ v := fun h => hv' (h ▸ hv)
    rw [ofAdicCompletion_finAt_ne h]; simp
  · rw [ofAdicCompletion_infAt]
    unfold IsPosAt
    simp


variable [IsCyclotomicExtension {3} ℚ K]

/-- **The Kummer character $\omega_D$**: continuous, trivial on $K^\times$, unitary, trivial on the units at
$v \notin S(3, D)$, and with value $\sigma(D/\mathfrak p_v)_3$ at a uniformizer. -/
theorem exists_omegaD (D : ℤ) (hD : D ≠ 0) (σ : K →+* ℂ) :
    ∃ ω : IdeleGroup (𝓞 K) K →* ℂˣ, Continuous ω ∧
      (∀ ξ : Kˣ, ω (IdeleGroup.unitEmbedding (𝓞 K) K ξ) = 1) ∧ (∀ x, ‖(ω x : ℂ)‖ = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sset 3 {(D : K)} → ∀ u : (v.adicCompletion K)ˣ,
        Valued.v (u : v.adicCompletion K) = 1 → ω (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sset 3 {(D : K)} → ∀ u : (v.adicCompletion K)ˣ,
        Valued.v (u : v.adicCompletion K) = WithZero.exp (-1) →
          (ω (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) : ℂ) = σ (powerResidue 3 (D : K) v)) := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hD' : (D : K) ≠ 0 := by exact_mod_cast hD
  obtain ⟨L, _, _, _, _, α, hα, hgen⟩ :=
    exists_kummer_field 3 (by norm_num) (IsCyclotomicExtension.zeta 3 ℚ K) hζ (D : K) hD'
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hα
    exact hD' ((algebraMap K L).injective (by simpa using hα.symm))
  have hex : ∀ g : Gal(L/K), ∃ c : K, g α = algebraMap K L c * α := fun g => by
    obtain ⟨j, -, h⟩ := kummer_zeta (by norm_num) hζ (D : K) hD' L α hα g
    exact ⟨_, h⟩
  choose c hc using hex
  have huniq : ∀ (g : Gal(L/K)) (d : K), g α = algebraMap K L d * α → d = c g := by
    intro g d h
    apply (algebraMap K L).injective
    exact mul_right_cancel₀ hα0 (h.symm.trans (hc g))
  have hc0 : ∀ g, c g ≠ 0 := by
    intro g h0
    have := hc g
    rw [h0, map_zero, zero_mul] at this
    exact hα0 ((map_eq_zero g).1 this)
  have hone : c 1 = 1 := (huniq 1 1 (by simp)).symm
  have hmul : ∀ g h, c (g * h) = c g * c h := by
    intro g h
    refine (huniq _ _ ?_).symm
    rw [AlgEquiv.mul_apply, hc h, map_mul, AlgEquiv.commutes, hc g, map_mul]
    ring
  have hc3 : ∀ g, c g ^ 3 = 1 := by
    intro g
    have h1 : (g α) ^ 3 = α ^ 3 := by
      rw [← map_pow, hα, AlgEquiv.commutes]
    rw [hc g, mul_pow, ← map_pow] at h1
    have h2 : algebraMap K L (c g ^ 3) = 1 := by
      have : α ^ 3 ≠ 0 := pow_ne_zero _ hα0
      exact mul_right_cancel₀ this (by rw [one_mul]; exact h1)
    exact (algebraMap K L).injective (by simpa using h2)
  let κ : Gal(L/K) →* ℂˣ :=
    { toFun := fun g => Units.mk0 (σ (c g)) (by simpa using hc0 g)
      map_one' := by ext; simp [hone]
      map_mul' := fun g h => by ext; simp [hmul] }
  have hκ : ∀ g, ((κ g : ℂˣ) : ℂ) = σ (c g) := fun g => rfl
  have hker : (idelicArtinTauCeti (K := K) L).ker ≤ (κ.comp (idelicArtinTauCeti (K := K) L)).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    simp [hx]
  refine ⟨κ.comp (idelicArtinTauCeti L), ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_of_isOpen_ker' _ (Subgroup.isOpen_mono hker (isOpen_ker_idelicArtinTauCeti L))
  · intro ξ
    simp [idelicArtinTauCeti_principal]
  · intro x
    rw [MonoidHom.comp_apply, hκ]
    refine Complex.norm_eq_one_of_pow_eq_one (n := 3) ?_ (by norm_num)
    rw [← map_pow, hc3, map_one]
  · intro v hv u hu
    have hunr := (item_5_3 3 (by norm_num) _ hζ (D : K) hD' L α hα hgen v hv).1
    simp [artin_unit hunr u hu]
  · intro v hv u hu
    obtain ⟨hunr, hfr⟩ := item_5_3 3 (by norm_num) _ hζ (D : K) hD' L α hα hgen v hv
    rw [MonoidHom.comp_apply, idelicArtinTauCeti_frobenius L v hunr u hu, hκ]
    rw [← huniq _ _ hfr]

end NumberFieldKB.MilneCFT.Ch8.Ex101
