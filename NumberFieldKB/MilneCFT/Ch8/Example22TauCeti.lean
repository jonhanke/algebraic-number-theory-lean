import NumberFieldKB.MilneCFT.Ch8.GrunwaldWang
import NumberFieldKB.MilneCFT.Ch8.Eighth
import NumberFieldKB.MilneCFT.Ch8.Brauer
import NumberFieldKB.MilneCFT.Ch5IdelicReciprocityTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.ExponentNorms
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Class Field Theory*, Chapter VIII, Example 2.2, proved from Tau Ceti

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §2, Example 2.2,
p. 231.

The named statement `Example2_2` (no cyclic extension of $\mathbb Q$ of degree $8$ in which $(2)$ stays prime) is
proved here (`example2_2`) by Milne's argument: the product formula for the idèlic Artin map applied to $16 = 2^4$.

If $(2)$ were prime in $L$, then $2$ is unramified with residue degree $8$, so the Frobenius element `artinFrob L v₂`
has order $8$. The principal idèle $16$ has trivial Artin symbol (`idelicArtinTauCeti_principal`). Dividing it by the
idèle $y^4$ ($y$ = a uniformizer $2$ at $v_2$ and $1$ elsewhere) leaves an idèle all of whose coordinates are eighth
powers (`exists_pow_eight_adic`, `exists_pow_eight_inf`, from `sixteen_eighth_power_padic` of `Eighth.lean`
transported along Mathlib's `Rat.HeightOneSpectrum.adicCompletion.padicEquiv`; at $v_2$ the coordinate is $1$), hence
an idèle norm by Tau Ceti's `TauCeti.ClassFieldTheory.mem_range_ideleNormMap_of_exponent_dvd` (the exponent of
$\mathrm{Gal}(L/\mathbb Q)$ divides $8$) and so in the kernel `ker_idelicArtinTauCeti`. Hence
`idelicArtinTauCeti L y = artinFrob L v₂` (`idelicArtinTauCeti_frobenius`) has fourth power $1$, contradicting that
its order is $8$ (`orderOf_frobAt_eq_inertiaDeg`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev
open scoped TensorProduct

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

open Rat.HeightOneSpectrum

/-- The finite prime `(2)` of `ℚ`. -/
def v2 : HeightOneSpectrum (𝓞 ℚ) := primesEquiv.symm ⟨2, Nat.prime_two⟩

theorem v2_asIdeal : v2.asIdeal = Ideal.span {(2 : 𝓞 ℚ)} := by
  show Ideal.map _ _ = _
  rw [Ideal.map_span, Set.image_singleton]
  simp

theorem ne_v2 (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ≠ v2) : (primesEquiv v : ℕ) ≠ 2 := by
  intro h
  apply hv
  have : primesEquiv v = ⟨2, Nat.prime_two⟩ := Subtype.ext h
  exact (primesEquiv.eq_symm_apply).2 this

/-- The principal idèle `16`. -/
def sixteenIdele : IdeleGroup (𝓞 ℚ) ℚ := IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ sixteenUnit

/-- `16` is an eighth power at every finite place other than `v2`. -/
theorem exists_pow_eight_adic (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ≠ v2) :
    ∃ y : (v.adicCompletion ℚ)ˣ, y ^ 8 = v.ideleFiniteCoord sixteenIdele := by
  have : Fact (Nat.Prime (primesEquiv v : ℕ)) := ⟨(primesEquiv v).2⟩
  obtain ⟨x, hx⟩ := sixteen_eighth_power_padic (primesEquiv v : ℕ) (ne_v2 v hv)
  obtain ⟨y, rfl⟩ := EquivLike.surjective (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v) x
  have h8' : y ^ 8 = 16 := by
    apply EquivLike.injective (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)
    rw [map_pow, hx]
    exact (map_ofNat (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v) 16).symm
  have hne : y ≠ 0 := by
    intro h0
    rw [h0] at h8'
    norm_num at h8'
  rw [sixteenIdele, HeightOneSpectrum.ideleFiniteCoord_unitEmbedding]
  refine ⟨Units.mk0 _ hne, ?_⟩
  ext
  simp [h8', sixteenUnit]

/-- `16` is an eighth power at the (unique) infinite place. -/
theorem exists_pow_eight_inf (w : InfinitePlace ℚ) :
    ∃ y : w.Completionˣ, y ^ 8 = w.ideleInfiniteCoord sixteenIdele := by
  have hw : w.IsReal := by
    have : w = Rat.infinitePlace := Subsingleton.elim _ _
    rw [this]; exact Rat.isReal_infinitePlace
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have h8 : (e.symm (Real.sqrt 2)) ^ 8 = 16 := by
    rw [← map_pow]
    have : Real.sqrt 2 ^ 8 = 16 := by
      have : Real.sqrt 2 ^ 8 = (Real.sqrt 2 ^ 2) ^ 4 := by ring
      rw [this, Real.sq_sqrt (by norm_num)]; norm_num
    rw [this, map_ofNat e.symm 16]
  have hne : e.symm (Real.sqrt 2) ≠ 0 := by
    intro h0
    rw [h0] at h8
    have h16 : (0 : w.Completion) = 16 := by simpa using h8
    have := congrArg e h16
    rw [map_zero, map_ofNat e 16] at this
    norm_num at this
  rw [sixteenIdele, InfinitePlace.ideleInfiniteCoord_unitEmbedding]
  refine ⟨Units.mk0 _ hne, ?_⟩
  ext
  simp [h8, sixteenUnit]

/-- The uniformizer `2` at `v2`, as the coordinate of the principal idèle `2`. -/
def twoUnit : (v2.adicCompletion ℚ)ˣ :=
  v2.ideleFiniteCoord (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ (Units.mk0 (2 : ℚ) two_ne_zero))

theorem valued_twoUnit : Valued.v (twoUnit : v2.adicCompletion ℚ) = WithZero.exp (-1) := by
  have h : Valued.v (twoUnit : v2.adicCompletion ℚ) = v2.valuation ℚ 2 :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := ℚ) (v := v2) (2 : ℚ)
  have e3 : (2 : ℚ) = algebraMap (𝓞 ℚ) ℚ 2 := (map_ofNat (algebraMap (𝓞 ℚ) ℚ) 2).symm
  rw [e3, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_singleton v2 two_ne_zero v2_asIdeal] at h
  exact h

theorem ideleFiniteCoord_sixteen : v2.ideleFiniteCoord sixteenIdele = twoUnit ^ 4 := by
  have : sixteenUnit = (Units.mk0 (2 : ℚ) two_ne_zero) ^ 4 := by
    ext
    simp [sixteenUnit]
    norm_num
  rw [sixteenIdele, this, map_pow, map_pow]
  rfl

section Main

variable (L : Type) [Field L] [NumberField L]

theorem map_v2_eq : v2.asIdeal.map (algebraMap (𝓞 ℚ) (𝓞 L)) = Ideal.span {(2 : 𝓞 L)} := by
  rw [v2_asIdeal, Ideal.map_span, Set.image_singleton, map_ofNat]

variable {L}

theorem eq_of_liesOver (hPm : (Ideal.span {(2 : 𝓞 L)}).IsMaximal) (Q : Ideal (𝓞 L)) (hQ : Q.IsPrime)
    (hQo : Q.LiesOver v2.asIdeal) : Q = Ideal.span {(2 : 𝓞 L)} := by
  have : Ideal.span {(2 : 𝓞 L)} ≤ Q := by
    rw [← map_v2_eq L]
    exact Ideal.map_le_iff_le_comap.2 (le_of_eq (Ideal.over_def Q v2.asIdeal))
  exact (hPm.eq_of_le hQ.ne_top this).symm

/-- The core of Example 2.2. -/
theorem not_inert_aux [IsAbelianGalois ℚ L] (hrank : Module.finrank ℚ L = 8)
    (hP : (Ideal.span {(2 : 𝓞 L)}).IsPrime) : False := by
  classical
  set P : Ideal (𝓞 L) := Ideal.span {(2 : 𝓞 L)} with hPdef
  have hP0 : P ≠ ⊥ := by
    rw [hPdef, Ne, Ideal.span_singleton_eq_bot]; exact two_ne_zero
  have hPm : P.IsMaximal := hP.isMaximal hP0
  have hmap : v2.asIdeal.map (algebraMap (𝓞 ℚ) (𝓞 L)) = P := map_v2_eq L
  have hover : P.LiesOver v2.asIdeal := by
    refine ⟨?_⟩
    have hle : v2.asIdeal ≤ P.under (𝓞 ℚ) := Ideal.map_le_iff_le_comap.1 hmap.le
    exact v2.isMaximal.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) hle
  have hmem : P ∈ v2.asIdeal.primesOver (𝓞 L) := ⟨hP, hover⟩
  have hprimes : v2.asIdeal.primesOver (𝓞 L) = {P} := by
    ext Q
    constructor
    · rintro ⟨hQ, hQo⟩
      exact eq_of_liesOver hPm Q hQ hQo
    · intro hQ
      rw [Set.mem_singleton_iff] at hQ
      rw [hQ]
      exact hmem
  have hncard : (v2.asIdeal.primesOver (𝓞 L)).ncard = 1 := by
    rw [hprimes, Set.ncard_singleton]
  have he : P.ramificationIdx (𝓞 ℚ) = 1 := by
    have h1 : v2.asIdeal.ramificationIdx' P = 1 := by
      rw [← hmap]
      exact Ideal.ramificationIdx'_map_self_eq_one (by rw [hmap]; exact hP.ne_top)
        (by rw [hmap]; exact hP0)
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx v2.asIdeal P v2.ne_bot]
    exact h1
  have hunrP : Algebra.IsUnramifiedAt (𝓞 ℚ) P := by
    have := finite_quotient_of_ne_bot P hP0
    exact Ideal.ramificationIdx_eq_one_iff.mp he
  have hv : v2 ∈ unramifiedPrimes ℚ L := by
    intro Q hQp hQo
    have : Q = P := eq_of_liesOver hPm Q hQp hQo
    subst this
    exact hunrP
  have hG : Nat.card Gal(L/ℚ) = 8 := by
    rw [IsGalois.card_aut_eq_finrank]; exact hrank
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v2.asIdeal (𝓞 L) Gal(L/ℚ)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v2.asIdeal P Gal(L/ℚ),
    Ideal.inertiaDegIn_eq_inertiaDeg v2.asIdeal P Gal(L/ℚ), hncard, he, hG] at hfund
  have hf : P.inertiaDeg (𝓞 ℚ) = 8 := by omega
  let Q : v2.asIdeal.primesOver (𝓞 L) := ⟨P, hmem⟩
  have hord : orderOf (artinFrob L v2) = 8 := by
    rw [artinFrob_eq L v2 hv Q, orderOf_frobAt_eq_inertiaDeg ℚ L hv Q]
    exact hf
  have hexp : Monoid.exponent Gal(L/ℚ) ∣ 8 := by
    have := Group.exponent_dvd_nat_card (G := Gal(L/ℚ))
    rwa [hG] at this
  let y : IdeleGroup (𝓞 ℚ) ℚ := IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v2 twoUnit
  have hy : MilneCFT.idelicArtinTauCeti L y = artinFrob L v2 :=
    MilneCFT.idelicArtinTauCeti_frobenius L v2 hv twoUnit valued_twoUnit
  have hz : sixteenIdele * (y ^ 4)⁻¹ ∈
      (TauCeti.GlobalNumberFields.ideleNormMap ℚ L).toMonoidHom.range := by
    refine TauCeti.ClassFieldTheory.mem_range_ideleNormMap_of_exponent_dvd ℚ L hexp
      (S := {v | v ≠ v2}) (T := ∅) ?_ ?_ ?_ ?_ ?_
    · intro v hv'
      exact absurd hv' (Set.notMem_empty v)
    · intro v hvS _
      have hv2 : v = v2 := not_not.1 hvS
      subst hv2
      exact ⟨⟨⟨P, hP, hP0⟩, hover⟩, hunrP⟩
    · intro v hv'
      rw [TauCeti.mem_powerSubgroup_iff]
      obtain ⟨u, hu⟩ := exists_pow_eight_adic v hv'
      refine ⟨u, ?_⟩
      rw [hu, map_mul, map_inv, map_pow,
        HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne v hv' twoUnit]
      simp
    · intro v hvS _
      have hv2 : v = v2 := not_not.1 hvS
      subst hv2
      rw [map_mul, map_inv, map_pow, HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self,
        ideleFiniteCoord_sixteen, mul_inv_cancel]
      simp
    · intro w
      rw [TauCeti.mem_powerSubgroup_iff]
      obtain ⟨u, hu⟩ := exists_pow_eight_inf w
      refine ⟨u, ?_⟩
      rw [hu, map_mul, map_inv, map_pow, InfinitePlace.ideleInfiniteCoord_ofAdicCompletion]
      simp
  have hker : sixteenIdele * (y ^ 4)⁻¹ ∈ (MilneCFT.idelicArtinTauCeti (K := ℚ) L).ker := by
    rw [MilneCFT.ker_idelicArtinTauCeti]
    obtain ⟨y', hy'⟩ := hz
    exact Subgroup.mem_sup_right
      ⟨y', (Ideles.ideleRelNorm_eq_ideleNormMap (Module.finBasis ℚ L) y').trans hy'⟩
  have h1 : MilneCFT.idelicArtinTauCeti (K := ℚ) L (sixteenIdele * (y ^ 4)⁻¹) = 1 := hker
  rw [map_mul, map_inv, map_pow, hy, sixteenIdele, MilneCFT.idelicArtinTauCeti_principal, one_mul,
    inv_eq_one] at h1
  have h4 := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at h4
  omega

end Main

/-- **Example 2.2, proved** (Milne, *CFT*, VIII, Example 2.2, p. 231): no cyclic extension of $\mathbb Q$ of degree
$8$ has $(2)$ prime. Via the product formula for the idèlic Artin map of Tau Ceti (`idelicArtinTauCeti`) applied to
$16 = 2^4$; $16$ is an eighth power in every $\mathbb Q_p$, $p \ne 2$, and at the real place. -/
@[kb "milne2020cft" "Ch. VIII, Example 2.2, p. 231"]
theorem example2_2 : Example2_2 where
  not_inert L _ _ _ hcyc hrank hP := by
    have := hcyc
    have : IsMulCommutative Gal(L/ℚ) := ⟨⟨IsCyclic.commGroup.mul_comm⟩⟩
    have : IsAbelianGalois ℚ L := ⟨⟩
    exact not_inert_aux hrank hP

end NumberFieldKB.MilneCFT.Ch8
