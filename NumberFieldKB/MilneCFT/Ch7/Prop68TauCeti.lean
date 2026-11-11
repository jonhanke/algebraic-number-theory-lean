import NumberFieldKB.MilneCFT.Ch7.Kummer
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.PowerSubgroup.Basic
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.PowerSubgroup.Units
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.NatCastValuation
import NumberFieldKB.TauCetiPort.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Milne, *Class Field Theory*, VII §6: Proposition 6.8 (nonarchimedean case), from Tau Ceti

Proves the named statement `Ch7.Prop6_8` unconditionally from the Tau Ceti port: the counts
`TauCeti.card_powerClasses` and `TauCeti.card_integerUnitPowerClasses` for a nonarchimedean local field,
applied to the completion $K_v$ (a nonarchimedean local field by
`HeightOneSpectrum.isNonarchimedeanLocalField_adicCompletion`).

* `natCastValuation_adicCompletion`: Tau Ceti's `natCastValuation (K_v) n` equals `ordNat K v n`.
* `prop6_8` : `Prop6_8 K`.
-/

open IsDedekindDomain NumberField ValuativeRel

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable {K : Type} [Field K] [NumberField K]

theorem natCast_adicCompletion_ne_zero (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : 0 < n) :
    ((n : ℕ) : v.adicCompletion K) ≠ 0 := by
  rw [← map_natCast (algebraMap K (v.adicCompletion K))]
  exact (map_ne_zero _).mpr (by exact_mod_cast hn.ne')

theorem natCastValuation_adicCompletion (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : 0 < n) :
    haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    TauCeti.natCastValuation (v.adicCompletion K) n (natCast_adicCompletion_ne_zero v hn) =
      ordNat K v n := by
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have h1 := TauCeti.normalizedValuationWithZero_natCast (v.adicCompletion K) n
    (natCast_adicCompletion_ne_zero v hn)
  rw [HeightOneSpectrum.normalizedValuationWithZero_adicCompletion] at h1
  have h2 : (Valued.v ((n : ℕ) : v.adicCompletion K) : WithZero (Multiplicative ℤ)) =
      v.intValuation ((n : ℕ) : 𝓞 K) := by
    rw [← map_natCast (algebraMap K (v.adicCompletion K)) n, HeightOneSpectrum.algebraMap_adicCompletion,
      Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      Algebra.algebraMap_self_apply, ← map_natCast (algebraMap (𝓞 K) K),
      HeightOneSpectrum.valuation_of_algebraMap]
  have hne : ((n : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hn.ne'
  rw [h2, v.intValuation_if_neg hne] at h1
  unfold ordNat
  rw [← WithZero.exp_neg] at h1
  simp only [neg_neg] at h1
  have := WithZero.exp_injective h1.symm
  exact_mod_cast this

/-- **Proposition 6.8** (Milne, *CFT*, Chapter VII, p. 217), nonarchimedean case, proved from the Tau Ceti
port. -/
@[kb "milne2020cft" "Ch. VII, Prop. 6.8 (nonarchimedean case)"]
theorem prop6_8 (K : Type) [Field K] [NumberField K] : Prop6_8 K where
  index_pow v n hn := by
    haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    have hn' := natCast_adicCompletion_ne_zero (K := K) v hn
    rw [Subgroup.index_eq_card, TauCeti.card_powerClasses hn',
      natCastValuation_adicCompletion v hn,
      HeightOneSpectrum.natCard_residueField_adicCompletion_eq_absNorm]
    rfl
  index_pow_units v n hn := by
    haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    have hn' := natCast_adicCompletion_ne_zero (K := K) v hn
    let e : localUnits K v ≃* 𝒪[v.adicCompletion K]ˣ :=
      (Submonoid.unitsEquivUnitsType _).trans
        (Units.mapEquiv (v.integerEquivAdicCompletionIntegers (K := K)).symm.toMulEquiv)
    rw [← Subgroup.index_map_equiv _ e, e.map_range_powMonoidHom n, Subgroup.index_eq_card,
      TauCeti.card_integerUnitPowerClasses hn', natCastValuation_adicCompletion v hn,
      HeightOneSpectrum.natCard_residueField_adicCompletion_eq_absNorm]
    rfl

end NumberFieldKB.MilneCFT.Ch7
