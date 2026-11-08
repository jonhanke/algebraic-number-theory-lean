import NumberFieldKB.MilneCFT.LubinTate.Complements
import NumberFieldKB.MilneCFT.LocalCFT.ReciprocityTauCeti
import NumberFieldKB.MilneCFT.LocalCFT.ArtinMapTransport
import NumberFieldKB.MilneCFT.LocalCFT.UnconditionalYamaguchi
import NumberFieldKB.MilneCFT.LocalCFT.Uniqueness
import NumberFieldKB.MilneCFT.LocalCFT.UnramifiedTauCeti
import NumberFieldKB.MilneCFT.LubinTate.ExtensionYamaguchi
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap
import NumberFieldKB.TauCetiPort.NumberTheory.Cyclotomic.Irreducible

/-!
# Example 3.13: the local Artin map of $\mathbb Q_p$ on cyclotomic extensions (proved)

Milne, *Class Field Theory*, Chapter I, Example 3.13. Tau Ceti computes its local Artin map of $\mathbb Q_p$ on
roots of unity (`localArtinMap_cyclotomic_padic_primePow`, `localArtinMap_cyclotomic_uniformizer`); every family
satisfying the conditions of Theorem 1.1 is the pullback of Tau Ceti's (`eq_pullback_tauCetiArtin`), so the formulas
hold for every local Artin map and every separable closure $\Omega$ (any universe).
-/

open scoped ValuativeRel
open Polynomial

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

open TauCeti TauCeti.ClassFieldTheory

section TypeZero

variable (p : ℕ) [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra ℚ_[p] Ω] [IsSepClosure ℚ_[p] Ω]

/-- Every local Artin map of `ℚ_p` is Tau Ceti's: the abelianized value is `localArtinMap`. -/
theorem localArtinMap_eq_of_isLocalArtinMap
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (L : FiniteAbelianExt ℚ_[p] Ω) (a : ℚ_[p]ˣ) :
    localArtinMap ℚ_[p] L.toField (sepEmb L) (Additive.ofMul a) =
      Additive.ofMul (Abelianization.of (φ L a)) := by
  have hT : IsLocalArtinMap (tauCetiArtin (K := ℚ_[p]) (Ω := Ω)) :=
    ⟨galRestrict_tauCetiArtin, fun hπ L hL => isFrobenius_tauCetiArtin hπ L hL,
      ker_tauCetiArtin, surjective_tauCetiArtin⟩
  have h : φ = tauCetiArtin := isLocalArtinMap_unique_unconditional Ω hφ hT
  subst h
  have := abelianizationOf_tauCetiArtin L (sepEmb L) a
  rw [this]
  rfl

/-- The unit `u ∈ 𝒪[ℚ_p]ˣ` as a unit of `ℤ_p`. -/
def unitToZp (u : 𝒪[ℚ_[p]]ˣ) : ℤ_[p]ˣ := Units.map (_root_.Padic.integerRingEquiv p).toMonoidHom u

theorem coe_unitToK_mul_zpow (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ) :
    ((unitToK u * padicPrimeUnit p ^ t : ℚ_[p]ˣ) : ℚ_[p]) =
      (p : ℚ_[p]) ^ t * ((unitToZp p u : ℤ_[p]) : ℚ_[p]) := by
  simp only [unitToK, padicPrimeUnit, unitToZp, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  rw [mul_comm]
  rfl

/-- **Prime-power roots of unity.** The Artin symbol of `u p^t` raises `ζ` with `ζ^(p^n) = 1` to the power
`u⁻¹ mod p^n`. -/
theorem artin_apply_primePow₀
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (L : FiniteAbelianExt ℚ_[p] Ω) (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ) {n : ℕ} (ζ : L.toField) (hζ : ζ ^ p ^ n = 1) :
    φ L (unitToK u * padicPrimeUnit p ^ t) ζ =
      ζ ^ (PadicInt.toZModPow n (((unitToZp p u)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])).val :=
  localArtinMap_cyclotomic_padic_primePow p L.toField (sepEmb L) (coe_unitToK_mul_zpow p u t)
    (localArtinMap_eq_of_isLocalArtinMap p hφ L _) hζ

/-- **Prime-to-`p` roots of unity.** The Artin symbol of any prime element raises `ζ` with `ζ^m = 1`,
`p ∤ m`, to the `p`-th power. -/
theorem artin_apply_uniformizer₀
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (L : FiniteAbelianExt ℚ_[p] Ω) {π : 𝒪[ℚ_[p]]} (hπ : Irreducible π) {m : ℕ} (hm : p.Coprime m)
    (ζ : L.toField) (hζ : ζ ^ m = 1) : φ L (primeUnit hπ) ζ = ζ ^ p := by
  have hU : IsUniformizer ℚ_[p] (primeUnit hπ) :=
    (isUniformizer_iff_exists_irreducible ℚ_[p] _).2 ⟨π, hπ, rfl⟩
  have h := localArtinMap_cyclotomic_uniformizer ℚ_[p] L.toField (sepEmb L) hU
    (localArtinMap_eq_of_isLocalArtinMap p hφ L _)
    (m := m) (by rwa [Padic.natCard_residueField]) hζ
  rwa [Padic.natCard_residueField] at h

end TypeZero

section Core

variable (p : ℕ) [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra ℚ_[p] Ω] [IsSepClosure ℚ_[p] Ω]

/-- Transport of an identity `φ L a x = x ^ k` (for `x` with `x ^ N = 1`) from Tau Ceti's Artin map on
`SeparableClosure ℚ_p` to any local Artin map on `Ω`. -/
theorem artin_apply_pow_of_sepClosure
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (L : FiniteAbelianExt ℚ_[p] Ω) (a : ℚ_[p]ˣ) (N k : ℕ)
    (h : ∀ (L' : FiniteAbelianExt ℚ_[p] (SeparableClosure ℚ_[p])) (y : L'.toField), y ^ N = 1 →
      tauCetiArtin L' a y = y ^ k)
    (x : L.toField) (hx : x ^ N = 1) : φ L a x = x ^ k := by
  rw [eq_pullback_tauCetiArtin Ω hφ]
  apply Subtype.ext
  rw [coe_pullbackArtin_apply, h _ _ ?_]
  · rw [SubmonoidClass.coe_pow, map_pow, AlgEquiv.symm_apply_apply, SubmonoidClass.coe_pow]
  · apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    change ((IsSepClosure.equiv ℚ_[p] Ω (SeparableClosure ℚ_[p])) (x : Ω)) ^ N = 1
    rw [← map_pow, ← SubmonoidClass.coe_pow, hx, OneMemClass.coe_one, map_one]

theorem isLocalArtinMap_tauCetiArtin :
    IsLocalArtinMap (tauCetiArtin (K := ℚ_[p]) (Ω := SeparableClosure ℚ_[p])) :=
  ⟨galRestrict_tauCetiArtin, fun hπ L hL => isFrobenius_tauCetiArtin hπ L hL,
    ker_tauCetiArtin, surjective_tauCetiArtin⟩

/-- **Prime-power roots of unity.** The Artin symbol of `u p^t` raises `ζ` with `ζ^(p^n) = 1` to the power
`u⁻¹ mod p^n`. -/
theorem artin_apply_primePow
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (L : FiniteAbelianExt ℚ_[p] Ω) (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ) {n : ℕ} (ζ : L.toField) (hζ : ζ ^ p ^ n = 1) :
    φ L (unitToK u * padicPrimeUnit p ^ t) ζ =
      ζ ^ (PadicInt.toZModPow n (((unitToZp p u)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])).val :=
  artin_apply_pow_of_sepClosure p hφ L _ _ _
    (fun L' y hy => artin_apply_primePow₀ p (isLocalArtinMap_tauCetiArtin p) L' u t y hy) ζ hζ

/-- **Prime-to-`p` roots of unity.** The Artin symbol of any prime element raises `ζ` with `ζ^m = 1`,
`p ∤ m`, to the `p`-th power. -/
theorem artin_apply_uniformizer
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (L : FiniteAbelianExt ℚ_[p] Ω) {π : 𝒪[ℚ_[p]]} (hπ : Irreducible π) {m : ℕ} (hm : p.Coprime m)
    (ζ : L.toField) (hζ : ζ ^ m = 1) : φ L (primeUnit hπ) ζ = ζ ^ p :=
  artin_apply_pow_of_sepClosure p hφ L _ _ _
    (fun L' y hy => artin_apply_uniformizer₀ p (isLocalArtinMap_tauCetiArtin p) L' hπ hm y hy) ζ hζ

/-- `ψ_r : 𝒪[ℚ_p] → ℤ/p^r`. -/
def psi (r : ℕ) : 𝒪[ℚ_[p]] →+* ZMod (p ^ r) :=
  (PadicInt.toZModPow r).comp (_root_.Padic.integerRingEquiv p : 𝒪[ℚ_[p]] →+* ℤ_[p])

theorem psi_natCast (r : ℕ) (k : ℕ) : psi p r (k : 𝒪[ℚ_[p]]) = (k : ZMod (p ^ r)) := by
  simp [psi]

theorem psi_unit (r : ℕ) (u : 𝒪[ℚ_[p]]ˣ) :
    psi p r (u : 𝒪[ℚ_[p]]) = PadicInt.toZModPow r ((unitToZp p u : ℤ_[p]ˣ) : ℤ_[p]) := rfl

theorem mem_maxIdeal_pow_iff (r : ℕ) (x : 𝒪[ℚ_[p]]) : x ∈ 𝓂[ℚ_[p]] ^ r ↔ psi p r x = 0 := by
  have hπ := TauCeti.Padic.irreducible_natCast_self p
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have : psi p r x = 0 ↔ (p : ℤ_[p]) ^ r ∣ (_root_.Padic.integerRingEquiv p x) := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    rfl
  rw [this]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨_root_.Padic.integerRingEquiv p c, ?_⟩
    simp
  · rintro ⟨c, hc⟩
    refine ⟨(_root_.Padic.integerRingEquiv p).symm c, ?_⟩
    apply (_root_.Padic.integerRingEquiv p).injective
    simpa using hc

/-- If `k u ≡ 1 mod 𝓂^r` then `k ≡ u⁻¹ mod p^r`. -/
theorem natCast_eq_toZModPow_inv {r : ℕ} (u : 𝒪[ℚ_[p]]ˣ) (k : ℕ)
    (hk : (k : 𝒪[ℚ_[p]]) * u - 1 ∈ 𝓂[ℚ_[p]] ^ r) :
    (k : ZMod (p ^ r)) = PadicInt.toZModPow r (((unitToZp p u)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
  rw [mem_maxIdeal_pow_iff, map_sub, map_mul, psi_natCast, psi_unit, map_one, sub_eq_zero] at hk
  have h2 : PadicInt.toZModPow r (((unitToZp p u)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
      PadicInt.toZModPow r ((unitToZp p u : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  linear_combination (-(k : ZMod (p ^ r))) * h2 +
    PadicInt.toZModPow r (((unitToZp p u)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * hk

theorem pow_eq_pow_of_cast_eq {M : Type*} [Monoid M] {ζ : M} {N : ℕ} (hζ : ζ ^ N = 1) {k m : ℕ}
    (h : (k : ZMod N) = (m : ZMod N)) : ζ ^ k = ζ ^ m := by
  have key : ∀ j : ℕ, ζ ^ j = ζ ^ (j % N) := fun j => by
    conv_lhs => rw [← Nat.mod_add_div j N, pow_add, pow_mul, hζ, one_pow, mul_one]
  rw [key k, key m]
  exact congrArg (ζ ^ ·) ((ZMod.natCast_eq_natCast_iff k m N).1 h)

/-- **Example 3.13 (b), action.** For `ζ ∈ L` with `ζ^(p^r) = 1`, `φ_L(u p^t) ζ = ζ^k` whenever `k u ≡ 1 mod p^r`. -/
theorem artin_apply_pow_of_mul_unit
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (L : FiniteAbelianExt ℚ_[p] Ω) (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ) {r : ℕ} (ζ : L.toField) (hζ : ζ ^ p ^ r = 1)
    (k : ℕ) (hk : (k : 𝒪[ℚ_[p]]) * u - 1 ∈ 𝓂[ℚ_[p]] ^ r) :
    φ L (unitToK u * padicPrimeUnit p ^ t) ζ = ζ ^ k := by
  rw [artin_apply_primePow p hφ L u t ζ hζ]
  refine (pow_eq_pow_of_cast_eq hζ ?_).symm
  rw [natCast_eq_toZModPow_inv p u k hk, ZMod.natCast_zmod_val]

theorem algEquiv_ext_of_eq_adjoin {F E : Type*} [Field F] [Field E] [Algebra F E] {S : IntermediateField F E}
    {s : Set E} (hS : S = IntermediateField.adjoin F s) {f g : S ≃ₐ[F] S}
    (h : ∀ x (hx : x ∈ s), f ⟨x, hS.ge (IntermediateField.subset_adjoin _ _ hx)⟩ =
      g ⟨x, hS.ge (IntermediateField.subset_adjoin _ _ hx)⟩) : f = g :=
  AlgEquiv.coe_toAlgHom_injective (IntermediateField.algHom_ext_of_eq_adjoin F hS h)

/-- A finite subextension generated by an `n`-th root of unity with `p ∤ n` is unramified. -/
theorem isUnramifiedExt_of_eq_adjoin (L : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] L] {ζ : Ω}
    {n : ℕ} (hn : p.Coprime n) (hζ : IsPrimitiveRoot ζ n) (hL : L = IntermediateField.adjoin ℚ_[p] {ζ}) :
    IsUnramifiedExt L := by
  let _ : ValuativeRel L := TauCeti.finiteIntermediateFieldValuativeRel ℚ_[p] Ω L
  let _ : TopologicalSpace L := TauCeti.finiteIntermediateFieldTopology ℚ_[p] Ω L
  have : ValuativeExtension ℚ_[p] L := TauCeti.finiteIntermediateField_valuativeExtension ℚ_[p] Ω L
  have : IsNonarchimedeanLocalField L := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField ℚ_[p] Ω L
  refine (isUnramified_iff_isUnramifiedExt L).1 ?_
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact (Fact.out : p.Prime).ne_one (Nat.coprime_zero_right _ |>.1 hn)
  have hnp : ¬ (p : ℤ) ∣ (n : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).1 hn
  let ζL : L := ⟨ζ, hL ▸ IntermediateField.mem_adjoin_simple_self _ ζ⟩
  have hζL : ζL ^ n = 1 := Subtype.ext (by simpa [ζL] using hζ.pow_eq_one)
  let b : 𝒪[L] := ⟨ζL, (Valuation.mem_integer_iff _ _).2
    ((pow_le_one_iff_of_nonneg zero_le hn0).1 (by rw [← map_pow, hζL, map_one]))⟩
  have hb : b ^ n = 1 := Subtype.ext (by simpa [b] using hζL)
  refine TauCeti.isUnramified_of_adjoin_eq_top_of_isUnit_aeval_derivative (b := b)
    (p := X ^ n - 1) ?_ ?_ ?_
  · exact IntermediateField.map_injective _ ((IntermediateField.lift_adjoin_simple ℚ_[p] _ ζL).trans
      (hL.symm.trans (IntermediateField.lift_top ℚ_[p] _).symm))
  · rw [map_sub, map_pow, aeval_X, map_one, hb, sub_self]
  · rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero, map_mul, aeval_C,
      map_natCast, map_pow, aeval_X]
    refine .mul ?_ ((IsUnit.of_pow_eq_one hb hn0).pow _)
    simpa using (_root_.Padic.isUnit_intCast_integerRing hnp).map
      (algebraMap 𝒪[ℚ_[p]] 𝒪[L])

theorem autToPow_eq_cast {S R : Type*} [CommRing S] [IsDomain S] [CommRing R] [Algebra R S] {μ : S} {n : ℕ}
    [NeZero n] (hμ : IsPrimitiveRoot μ n) (f : S ≃ₐ[R] S) (s : ℕ) (hs : f μ = μ ^ s) :
    ((hμ.autToPow R f : (ZMod n)ˣ) : ZMod n) = (s : ZMod n) := by
  have h := hμ.autToPow_spec R f
  rw [hs] at h
  have hs' : μ ^ s = μ ^ (s % n) := by
    conv_lhs => rw [← Nat.mod_add_div s n, pow_add, pow_mul, hμ.pow_eq_one, one_pow, mul_one]
  have hv := hμ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))) (h.trans hs')
  rw [← ZMod.natCast_zmod_val ((hμ.autToPow R f : (ZMod n)ˣ) : ZMod n), hv, ZMod.natCast_mod]

theorem primeUnit_mul_eq (u : 𝒪[ℚ_[p]]ˣ) :
    primeUnit ((irreducible_units_mul u).2 (TauCeti.Padic.irreducible_natCast_self p)) =
      unitToK u * padicPrimeUnit p := by
  apply Units.ext
  simp [primeUnit, unitToK, padicPrimeUnit]
  left
  rfl

theorem padicPrimeUnit_eq : padicPrimeUnit p = primeUnit (TauCeti.Padic.irreducible_natCast_self p) :=
  Units.ext rfl

theorem artin_prime_autToPow
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (L : FiniteAbelianExt ℚ_[p] Ω) {m : ℕ} [NeZero m] (hm : p.Coprime m)
    (ζ : L.toField) (hζ : IsPrimitiveRoot ζ m) :
    hζ.autToPow ℚ_[p] (φ L (padicPrimeUnit p)) = ZMod.unitOfCoprime p hm := by
  apply Units.ext
  rw [padicPrimeUnit_eq, autToPow_eq_cast hζ _ p
    (artin_apply_uniformizer p hφ L (TauCeti.Padic.irreducible_natCast_self p) hm ζ hζ.pow_eq_one)]
  simp

/-- **Prime-to-`p` roots of unity, general element.** -/
theorem artin_autToPow
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (L : FiniteAbelianExt ℚ_[p] Ω) (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ) {m : ℕ} [NeZero m] (hm : p.Coprime m)
    (ζ : L.toField) (hζ : IsPrimitiveRoot ζ m) :
    hζ.autToPow ℚ_[p] (φ L (unitToK u * padicPrimeUnit p ^ t)) = (ZMod.unitOfCoprime p hm) ^ t := by
  have hp := TauCeti.Padic.irreducible_natCast_self p
  have hup := (irreducible_units_mul u).2 hp
  have e : unitToK u * padicPrimeUnit p ^ t =
      primeUnit hup * primeUnit hp ^ (t - 1) := by
    rw [primeUnit_mul_eq, padicPrimeUnit_eq, zpow_sub_one]
    group
  have h1 : hζ.autToPow ℚ_[p] (φ L (primeUnit hup)) = ZMod.unitOfCoprime p hm := by
    apply Units.ext
    rw [autToPow_eq_cast hζ _ p (artin_apply_uniformizer p hφ L hup hm ζ hζ.pow_eq_one)]
    simp
  have h0 : hζ.autToPow ℚ_[p] (φ L (primeUnit hp)) = ZMod.unitOfCoprime p hm := by
    apply Units.ext
    rw [autToPow_eq_cast hζ _ p (artin_apply_uniformizer p hφ L hp hm ζ hζ.pow_eq_one)]
    simp
  rw [e, map_mul, map_mul, map_zpow, map_zpow, h1, h0]
  group

/-! ### Part (c) -/

theorem cyclotomicArtinQp_general
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (m r : ℕ) (hm : Nat.Coprime p m) (L : FiniteAbelianExt ℚ_[p] Ω) (ζm ζpr : Ω) (h1 : ζm ∈ L.toField)
    (h2 : ζpr ∈ L.toField) (hζm : IsPrimitiveRoot ζm m) (hζpr : IsPrimitiveRoot ζpr (p ^ r))
    (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ) :
    (∀ j : ℕ, ((j : ZMod m) = ((ZMod.unitOfCoprime p hm ^ t : (ZMod m)ˣ) : ZMod m)) →
        ((φ L (unitToK u * padicPrimeUnit p ^ t) ⟨ζm, h1⟩ : L.toField) : Ω) = ζm ^ j) ∧
      (∀ k : ℕ, (k : 𝒪[ℚ_[p]]) * u - 1 ∈ 𝓂[ℚ_[p]] ^ r →
        ((φ L (unitToK u * padicPrimeUnit p ^ t) ⟨ζpr, h2⟩ : L.toField) : Ω) = ζpr ^ k) := by
  have hm0 : NeZero m := ⟨by rintro rfl; exact (Fact.out : p.Prime).ne_one (Nat.coprime_zero_right _ |>.1 hm)⟩
  constructor
  · intro j hj
    have hζ' : IsPrimitiveRoot (⟨ζm, h1⟩ : L.toField) m :=
      hζm.of_map_of_injective (f := L.toField.val) L.toField.val.injective
    have hspec := hζ'.autToPow_spec ℚ_[p] (φ L (unitToK u * padicPrimeUnit p ^ t))
    rw [artin_autToPow p hφ L u t hm _ hζ'] at hspec
    have : (⟨ζm, h1⟩ : L.toField) ^ j = (⟨ζm, h1⟩ : L.toField) ^
        ((ZMod.unitOfCoprime p hm ^ t : (ZMod m)ˣ) : ZMod m).val := by
      refine pow_eq_pow_of_cast_eq hζ'.pow_eq_one ?_
      rw [ZMod.natCast_zmod_val]
      exact hj
    have e := this.trans hspec
    rw [← e]
    rfl
  · intro k hk
    have := artin_apply_pow_of_mul_unit p hφ L u t (⟨ζpr, h2⟩ : L.toField)
      (Subtype.ext (by simpa using hζpr.pow_eq_one)) k hk
    rw [this]
    rfl

/-! ### Part (b) -/

theorem cast_eq_of_pow_eq {S : Type*} [CommRing S] [IsDomain S] {ζ : S} {N : ℕ} [NeZero N]
    (hζ : IsPrimitiveRoot ζ N) {i j : ℕ}
    (h : ζ ^ i = ζ ^ j) : (i : ZMod N) = (j : ZMod N) := by
  have key : ∀ k : ℕ, ζ ^ k = ζ ^ (k % N) := fun k => by
    conv_lhs => rw [← Nat.mod_add_div k N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have := hζ.pow_inj (Nat.mod_lt i hN) (Nat.mod_lt j hN) ((key i).symm.trans (h.trans (key j)))
  rw [← ZMod.natCast_mod i N, this, ZMod.natCast_mod]

/-- Kernel criterion for a field generated by a primitive `p^r`-th root of unity. -/
theorem artin_eq_one_iff
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (r : ℕ) (hr : 1 ≤ r) (L : FiniteAbelianExt ℚ_[p] Ω) (ζ : Ω) (hζ : ζ ∈ L.toField)
    (hζr : IsPrimitiveRoot ζ (p ^ r)) (hL : L.toField = IntermediateField.adjoin ℚ_[p] {ζ})
    (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ) :
    φ L (unitToK u * padicPrimeUnit p ^ t) = 1 ↔ (u : 𝒪[ℚ_[p]]) - 1 ∈ 𝓂[ℚ_[p]] ^ r := by
  have hζ' : IsPrimitiveRoot (⟨ζ, hζ⟩ : L.toField) (p ^ r) :=
    hζr.of_map_of_injective (f := L.toField.val) L.toField.val.injective
  have hpow : (⟨ζ, hζ⟩ : L.toField) ^ p ^ r = 1 := hζ'.pow_eq_one
  have hN : NeZero (p ^ r) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  set g := φ L (unitToK u * padicPrimeUnit p ^ t) with hg
  set c := PadicInt.toZModPow r (((unitToZp p u)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) with hc
  have h2 : c * psi p r (u : 𝒪[ℚ_[p]]) = 1 := by
    rw [psi_unit, hc, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  have hgc : g ⟨ζ, hζ⟩ = (⟨ζ, hζ⟩ : L.toField) ^ c.val :=
    (artin_apply_primePow p hφ L u t _ hpow)
  have hcg : g = 1 ↔ c = 1 := by
    constructor
    · intro h1
      rw [h1, AlgEquiv.one_apply] at hgc
      have h3 : (⟨ζ, hζ⟩ : L.toField) ^ 1 = (⟨ζ, hζ⟩ : L.toField) ^ c.val := by
        rw [pow_one]; exact hgc
      have h4 := cast_eq_of_pow_eq hζ' h3
      rw [ZMod.natCast_zmod_val] at h4
      simpa using h4.symm
    · intro h1
      apply algEquiv_ext_of_eq_adjoin hL
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [AlgEquiv.one_apply]
      refine hgc.trans ((pow_eq_pow_of_cast_eq hpow (k := c.val) (m := 1) ?_).trans (pow_one _))
      rw [ZMod.natCast_zmod_val, h1, Nat.cast_one]
  have hpsi : c = 1 ↔ psi p r (u : 𝒪[ℚ_[p]]) = 1 := by
    constructor
    · intro h1
      rw [h1, one_mul] at h2
      exact h2
    · intro h1
      rw [h1, mul_one] at h2
      exact h2
  rw [hcg, hpsi, mem_maxIdeal_pow_iff, map_sub, map_one, sub_eq_zero]

theorem unitToK_one_mul : unitToK (1 : 𝒪[ℚ_[p]]ˣ) * padicPrimeUnit p ^ (1 : ℤ) = padicPrimeUnit p := by
  apply Units.ext
  simp [unitToK]

theorem finrank_adjoin_primePow (r : ℕ) (hr : 1 ≤ r) (ζ : Ω) (hζr : IsPrimitiveRoot ζ (p ^ r)) :
    Module.finrank ℚ_[p] (IntermediateField.adjoin ℚ_[p] {ζ}) = (p - 1) * p ^ (r - 1) := by
  have hint : IsIntegral ℚ_[p] ζ := (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
  have hN : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos _
  have hmin : minpoly ℚ_[p] ζ = cyclotomic (p ^ r) ℚ_[p] :=
    (minpoly.eq_of_irreducible_of_monic (TauCeti.irreducible_cyclotomic_prime_pow_ratPadic p r)
      (by rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]; exact hζr.isRoot_cyclotomic hN)
      (cyclotomic.monic _ _)).symm
  rw [IntermediateField.adjoin.finrank hint, hmin, natDegree_cyclotomic,
    Nat.totient_prime_pow (Fact.out : p.Prime) (by omega), mul_comm]

theorem cyclotomicArtinQp_totallyRamified
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (r : ℕ) (hr : 1 ≤ r) (L : FiniteAbelianExt ℚ_[p] Ω) (ζ : Ω) (hζ : ζ ∈ L.toField)
    (hζr : IsPrimitiveRoot ζ (p ^ r)) (hL : L.toField = IntermediateField.adjoin ℚ_[p] {ζ}) :
    IsTotallyRamifiedExt L.toField ∧ Module.finrank ℚ_[p] L.toField = (p - 1) * p ^ (r - 1) ∧
    (∀ (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ) (k : ℕ), (k : 𝒪[ℚ_[p]]) * u - 1 ∈ 𝓂[ℚ_[p]] ^ r →
      ((φ L (unitToK u * padicPrimeUnit p ^ t) ⟨ζ, hζ⟩ : L.toField) : Ω) = ζ ^ k) ∧
    ((φ L).ker : Set ℚ_[p]ˣ) = {a | ∃ (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ),
      (u : 𝒪[ℚ_[p]]) - 1 ∈ 𝓂[ℚ_[p]] ^ r ∧ a = unitToK u * padicPrimeUnit p ^ t} := by
  have hp := TauCeti.Padic.irreducible_natCast_self p
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ((totallyRamifiedNormInput ℚ_[p] Ω).iff L.toField).2 ⟨_, hp, ?_⟩
    rw [← padicPrimeUnit_eq, ← hφ.ker_eq, MonoidHom.mem_ker, ← unitToK_one_mul,
      artin_eq_one_iff p hφ r hr L ζ hζ hζr hL]
    simp
  · rw [hL]
    exact finrank_adjoin_primePow p r hr ζ hζr
  · intro u t k hk
    have hpow : (⟨ζ, hζ⟩ : L.toField) ^ p ^ r = 1 := Subtype.ext (by simpa using hζr.pow_eq_one)
    rw [artin_apply_pow_of_mul_unit p hφ L u t _ hpow k hk]
    rfl
  · ext a
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_ofPred_eq]
    constructor
    · intro ha
      obtain ⟨v, hv, k, rfl⟩ := exists_unit_zpow _ hp a
      obtain ⟨u, hu⟩ := mem_unitGroup.1 hv
      have hvu : v = unitToK u := Units.ext hu.symm
      rw [hvu, ← padicPrimeUnit_eq] at ha ⊢
      exact ⟨u, k, (artin_eq_one_iff p hφ r hr L ζ hζ hζr hL u k).1 ha, rfl⟩
    · rintro ⟨u, t, hu, rfl⟩
      exact (artin_eq_one_iff p hφ r hr L ζ hζ hζr hL u t).2 hu

theorem artin_unit_mul_zpow_unramified
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (L : FiniteAbelianExt ℚ_[p] Ω) (hL : IsUnramifiedExt L.toField) (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ) :
    φ L (unitToK u * padicPrimeUnit p ^ t) = (φ L (padicPrimeUnit p)) ^ t := by
  rw [map_mul, map_zpow, artin_unit_eq_one (unramifiedInput ℚ_[p] Ω) hφ
    (mem_unitGroup.2 ⟨u, rfl⟩) L hL, one_mul]

theorem artin_prime_eq_of_isFrobenius
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (L : FiniteAbelianExt ℚ_[p] Ω) (hL : IsUnramifiedExt L.toField) (σ : Gal(L.toField/ℚ_[p]))
    (hσ : IsFrobenius L.toField σ) : φ L (padicPrimeUnit p) = σ := by
  refine (unramifiedInput ℚ_[p] Ω).frobenius_unique L hL _ _ ?_ hσ
  rw [padicPrimeUnit_eq]
  exact hφ.frobenius (TauCeti.Padic.irreducible_natCast_self p) L hL

theorem cyclotomicArtinQp_unramified
    {φ : ∀ L : FiniteAbelianExt ℚ_[p] Ω, ℚ_[p]ˣ →* Gal(L.toField/ℚ_[p])} (hφ : IsLocalArtinMap φ)
    (n : ℕ) (hn : Nat.Coprime p n) (L : FiniteAbelianExt ℚ_[p] Ω) (ζ : Ω) (hζ : IsPrimitiveRoot ζ n)
    (hL : L.toField = IntermediateField.adjoin ℚ_[p] {ζ}) :
    IsUnramifiedExt L.toField ∧ Module.finrank ℚ_[p] L.toField = orderOf (ZMod.unitOfCoprime p hn) ∧
    (∀ (σ : Gal(L.toField/ℚ_[p])), IsFrobenius L.toField σ →
      ∀ (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ), φ L (unitToK u * padicPrimeUnit p ^ t) = σ ^ t) ∧
    ((φ L).ker : Set ℚ_[p]ˣ) = {a | ∃ (u : 𝒪[ℚ_[p]]ˣ) (t : ℤ),
      (orderOf (ZMod.unitOfCoprime p hn) : ℤ) ∣ t ∧ a = unitToK u * padicPrimeUnit p ^ t} := by
  have hn0 : NeZero n := ⟨by rintro rfl; exact (Fact.out : p.Prime).ne_one (Nat.coprime_zero_right _ |>.1 hn)⟩
  have hU := isUnramifiedExt_of_eq_adjoin p L.toField hn hζ hL
  have hmem : ζ ∈ L.toField := hL ▸ IntermediateField.mem_adjoin_simple_self _ ζ
  have hζ' : IsPrimitiveRoot (⟨ζ, hmem⟩ : L.toField) n :=
    hζ.of_map_of_injective (f := L.toField.val) L.toField.val.injective
  have hinj : Function.Injective (hζ'.autToPow ℚ_[p]) := by
    intro f g hfg
    have key : f ⟨ζ, hmem⟩ = g ⟨ζ, hmem⟩ := by
      rw [← hζ'.autToPow_spec ℚ_[p] f, ← hζ'.autToPow_spec ℚ_[p] g, hfg]
    apply algEquiv_ext_of_eq_adjoin hL
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact key
  have hp := TauCeti.Padic.irreducible_natCast_self p
  have hord : orderOf (φ L (padicPrimeUnit p)) = Module.finrank ℚ_[p] L.toField := by
    rw [padicPrimeUnit_eq]
    exact orderOf_artin_prime (unramifiedInput ℚ_[p] Ω) hφ hp L hU
  have hord2 : orderOf (φ L (padicPrimeUnit p)) = orderOf (ZMod.unitOfCoprime p hn) := by
    rw [← artin_prime_autToPow p hφ L hn _ hζ']
    exact (orderOf_injective _ hinj _).symm
  refine ⟨hU, hord.symm.trans hord2, ?_, ?_⟩
  · intro σ hσ u t
    rw [artin_unit_mul_zpow_unramified p hφ L hU, artin_prime_eq_of_isFrobenius p hφ L hU σ hσ]
  · ext a
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_ofPred_eq]
    constructor
    · intro ha
      obtain ⟨v, hv, k, rfl⟩ := exists_unit_zpow _ hp a
      obtain ⟨u, hu⟩ := mem_unitGroup.1 hv
      have hvu : v = unitToK u := Units.ext hu.symm
      refine ⟨u, k, ?_, by rw [hvu, padicPrimeUnit_eq]⟩
      rw [hvu, ← padicPrimeUnit_eq, artin_unit_mul_zpow_unramified p hφ L hU] at ha
      rw [← hord2]
      exact orderOf_dvd_iff_zpow_eq_one.2 ha
    · rintro ⟨u, t, ht, rfl⟩
      rw [artin_unit_mul_zpow_unramified p hφ L hU]
      rw [← hord2] at ht
      exact orderOf_dvd_iff_zpow_eq_one.1 ht

/-- **Example 3.13** (Milne, *CFT*, I, Example 3.13), for a separable closure `Ω` in any universe: the local Artin map of
`ℚ_p` on cyclotomic extensions, from Tau Ceti's explicit cyclotomic reciprocity law
(`localArtinMap_cyclotomic_padic_primePow`, `localArtinMap_cyclotomic_uniformizer`) and the uniqueness of the local
Artin map, transported from `SeparableClosure ℚ_p` (`eq_pullback_tauCetiArtin`). -/
@[kb "milne2020cft" "Ch. I, Example 3.13"]
theorem cyclotomicArtinQp : CyclotomicArtinQp p Ω where
  unramified _ hφ n hn L ζ hζ hL := cyclotomicArtinQp_unramified p hφ n hn L ζ hζ hL
  totallyRamified _ hφ r hr L ζ hζ hζr hL := cyclotomicArtinQp_totallyRamified p hφ r hr L ζ hζ hζr hL
  general _ hφ m r hm L ζm ζpr h1 h2 hζm hζpr _ u t :=
    cyclotomicArtinQp_general p hφ m r hm L ζm ζpr h1 h2 hζm hζpr u t

end Core

end NumberFieldKB.MilneCFT.LocalCFT
