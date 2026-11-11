import NumberFieldKB.MilneCFT.Ch8.Remark32Norm
import NumberFieldKB.MilneCFT.Ch8.Remark32Field
import NumberFieldKB.MilneCFT.Ch8.Remark32Rational
import NumberFieldKB.MilneCFT.Ch8.HasseNormTauCeti
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Milne, *Class Field Theory*, Remark VIII.3.2: $25$ is a local norm everywhere from $\mathbb Q(\sqrt{13},\sqrt{17})$

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, Remark 3.2,
p. 234.

At every place $v$ of $\mathbb Q$ one of $13$, $17$, $221$ is a square $r^2$ in $\mathbb Q_v$ (`R32.isSquare_padic`;
at the infinite place $13 > 0$). Let $\delta \in \{s, t, st\}$ be the corresponding square root in $L$ and $A =
\mathbb Q_v \otimes_{\mathbb Q} L$. An automorphism of $L$ with $\sigma(\delta) = -\delta$ (`R32.exists_aut_neg`)
induces $\tau$ on $A$, and `R32.norm_smul_idem_add` gives $\mathrm N_{A/\mathbb Q_v}(5e + (1-e)) = 5^2$, with
$[A : \mathbb Q_v] = [L : \mathbb Q] = 4$ (`R32.finrank_eq_four`). By the bridge `Ch8.mem_localNormGroup_iff`
(norms from $A$ = Chapter VII's local norms), $25$ is a local norm at $v$ (`R32.isLocalNorm_25`,
`R32.isLocalNormInf_25`).
-/

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.R32

variable {L : Type} [Field L] [NumberField L] {s t : L}

/-- If $\delta^2 = d$ with $d$ a rational non-square and $d = r^2$ in a field $F \supseteq \mathbb Q$, then every
element of $F^\times$ equal to $25$ is a norm from $F \otimes_{\mathbb Q} L$ (given $[L:\mathbb Q] = 4$). -/
theorem mem_range_normUnits_of_sq (F : Type) [Field F] [Algebra ℚ F] [IsGalois ℚ L]
    (hL : Module.finrank ℚ L = 4) {δ : L} {d : ℚ} (hδ : δ ^ 2 = algebraMap ℚ L d) (hd : ∀ q : ℚ, q ^ 2 ≠ d)
    {r : F} (hr : r ^ 2 = algebraMap ℚ F d) (x : Fˣ) (hx : (x : F) = 25) :
    x ∈ (TauCeti.Algebra.normUnits F (S := F ⊗[ℚ] L)).range := by
  obtain ⟨σ, hσ⟩ := exists_aut_neg hδ hd
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hd 0 (by ring)
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hd0
    have : algebraMap ℚ F d = 0 := by rw [← hr]; ring
    exact (map_eq_zero_iff _ (algebraMap ℚ F).injective).mp this
  set A := F ⊗[ℚ] L
  set δA : A := Algebra.TensorProduct.includeRight δ
  have hδA : δA ^ 2 = algebraMap F A (r ^ 2) := by
    simp only [δA, ← map_pow, hδ, hr]
    rw [← IsScalarTower.algebraMap_apply ℚ F A, AlgHom.commutes]
  set τ : A ≃ₐ[F] A := Algebra.TensorProduct.congr AlgEquiv.refl σ
  have hτ : τ δA = -δA := by
    change Algebra.TensorProduct.congr AlgEquiv.refl σ ((1 : F) ⊗ₜ[ℚ] δ) = -((1 : F) ⊗ₜ[ℚ] δ)
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    simp [hσ, TensorProduct.tmul_neg]
  have hk : Module.finrank F A = 2 * 2 := by
    rw [Module.finrank_baseChange, hL]
  set e := idem r δA
  have he := idem_mul_self hr0 h2 hδA
  have hn := norm_smul_idem_add hr0 h2 hδA τ hτ hk 5
  have hunit : (algebraMap F A 5 * e + (1 - e)) * (algebraMap F A 5⁻¹ * e + (1 - e)) = 1 := by
    have h5 : algebraMap F A 5 * algebraMap F A 5⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (by norm_num : (5 : F) ≠ 0), map_one]
    calc (algebraMap F A 5 * e + (1 - e)) * (algebraMap F A 5⁻¹ * e + (1 - e))
        = algebraMap F A 5 * algebraMap F A 5⁻¹ * (e * e) + algebraMap F A 5 * (e - e * e) +
            algebraMap F A 5⁻¹ * (e - e * e) + (1 - 2 * e + e * e) := by ring
      _ = 1 := by rw [h5, he]; ring
  refine ⟨⟨_, _, hunit, by rw [mul_comm]; exact hunit⟩, ?_⟩
  ext
  rw [TauCeti.Algebra.coe_normUnits, Units.val_mk, hn, hx]
  norm_num

/-- At every completion of $\mathbb Q$ at a finite prime one of $13$, $17$, $221$ is a square. -/
theorem isSquare_adicCompletion (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsSquare (13 : v.adicCompletion ℚ) ∨ IsSquare (17 : v.adicCompletion ℚ) ∨
      IsSquare (221 : v.adicCompletion ℚ) := by
  set p := Rat.HeightOneSpectrum.primesEquiv v
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  letI : Algebra ℚ (v.adicCompletion ℚ) := HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  have e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v
  have hmap : ∀ n : ℕ, IsSquare (n : ℚ_[p]) → IsSquare (n : v.adicCompletion ℚ) := by
    intro n ⟨y, hy⟩
    obtain ⟨x, hx⟩ := e.surjective y
    subst hx
    refine ⟨x, e.injective ?_⟩
    rw [map_natCast, map_mul]
    exact hy
  rcases isSquare_padic (p : ℕ) with h | h | h
  · exact Or.inl (by exact_mod_cast hmap 13 (by exact_mod_cast h))
  · exact Or.inr (Or.inl (by exact_mod_cast hmap 17 (by exact_mod_cast h)))
  · exact Or.inr (Or.inr (by exact_mod_cast hmap 221 (by exact_mod_cast h)))

/-- $13$ is a square at every infinite place of $\mathbb Q$. -/
theorem isSquare_completion_13 (w : InfinitePlace ℚ) : IsSquare (13 : w.Completion) := by
  rcases w.isReal_or_isComplex with hw | hw
  · let f := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
    refine ⟨f (Real.sqrt 13), ?_⟩
    rw [← map_mul, Real.mul_self_sqrt (by norm_num), map_ofNat]
  · haveI : IsAlgClosed w.Completion :=
      IsAlgClosed.of_ringEquiv ℂ _ (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm
    exact IsAlgClosed.isSquare _

variable (hs : s ^ 2 = 13) (ht : t ^ 2 = 17)
  (hgen : IntermediateField.adjoin ℚ ({s, t} : Set L) = ⊤)
include hs ht hgen

/-- Over a field $F \supseteq \mathbb Q$ in which $13$, $17$ or $221$ is a square, $25$ is a norm from
$F \otimes_{\mathbb Q} L$. -/
theorem mem_range_normUnits (F : Type) [Field F] [Algebra ℚ F]
    (hF : IsSquare (13 : F) ∨ IsSquare (17 : F) ∨ IsSquare (221 : F)) (x : Fˣ) (hx : (x : F) = 25) :
    x ∈ (TauCeti.Algebra.normUnits F (S := F ⊗[ℚ] L)).range := by
  haveI := isGalois hs ht hgen
  have hL := finrank_eq_four hs ht hgen
  rcases hF with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩
  · exact mem_range_normUnits_of_sq F hL (d := 13) (by rw [hs, map_ofNat]) (fun q => (rat_sq_ne q).1)
      (r := r) (by rw [map_ofNat, hr]; ring) x hx
  · exact mem_range_normUnits_of_sq F hL (d := 17) (by rw [ht, map_ofNat]) (fun q => (rat_sq_ne q).2.1)
      (r := r) (by rw [map_ofNat, hr]; ring) x hx
  · exact mem_range_normUnits_of_sq F hL (δ := s * t) (d := 221) (by rw [mul_pow, hs, ht, map_ofNat]; norm_num)
      (fun q => (rat_sq_ne q).2.2) (r := r) (by rw [map_ofNat, hr]; ring) x hx

/-- $25$ is a local norm from $L$ at every finite prime of $\mathbb Q$. -/
theorem isLocalNorm_25 (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsLocalNorm ℚ L (Units.mk0 (25 : ℚ) (by norm_num)) v := by
  letI : Algebra ℚ (v.adicCompletion ℚ) := HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  exact (mem_localNormGroup_iff ℚ L v _).mpr
    (mem_range_normUnits hs ht hgen _ (isSquare_adicCompletion v) _
      (by rw [Units.coe_map, Units.val_mk0]; exact map_ofNat (algebraMap ℚ (v.adicCompletion ℚ)) 25))

/-- $25$ is a local norm from $L$ at the infinite place of $\mathbb Q$. -/
theorem isLocalNormInf_25 (w : InfinitePlace ℚ) :
    IsLocalNormInf ℚ L (Units.mk0 (25 : ℚ) (by norm_num)) w :=
  (mem_localNormGroupInf_iff ℚ L w _).mpr
    (mem_range_normUnits hs ht hgen _ (Or.inl (isSquare_completion_13 w)) _
      (by rw [Units.coe_map, Units.val_mk0]; exact map_ofNat (algebraMap ℚ w.Completion) 25))

end NumberFieldKB.MilneCFT.Ch8.R32
