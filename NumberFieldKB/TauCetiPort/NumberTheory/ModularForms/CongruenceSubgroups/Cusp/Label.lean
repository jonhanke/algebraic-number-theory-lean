/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.Modular
public import Mathlib.Data.ZMod.Units
public import Mathlib.Data.Nat.Totient
public import NumberFieldKB.TauCetiPort.Data.Int.GCD

/-!
# The labels of the cusps of `Γ₀(N)`

Extract of Tau Ceti `TauCeti/NumberTheory/ModularForms/CongruenceSubgroups/Cusp/Count.lean` (the labels of cusps,
without the orbit spaces of `PSL(2, ℝ)`) and of `TauCeti/Data/ZMod/Units.lean`
(`TauCeti.ZMod.unitOfIsCoprime_div_eq_iff`), main `e8758b7`. Declarations unchanged.

For `γ ∈ SL(2, ℤ)` with bottom row `(c, d)`, the label of `γ` is the divisor `g = gcd(c, N)` of `N` together with
the unit `(c / g) / d` modulo `gcd(g, N / g)` (`TauCeti.gamma0CuspLabel`). Two matrices have the same label exactly
when `N ∣ c d' - c' d + j c c'` for some integer `j` (`TauCeti.gamma0CuspLabel_eq_iff_exists_dvd`), and every pair
`(g, x)` is a label (`TauCeti.gamma0CuspLabel_surjective`).

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §3.8.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularGroup
open scoped MatrixGroups

namespace TauCeti

namespace ZMod

/-- **Equality of quotients of integer units.** For integers `a`, `b`, `a'` and `b'` prime to
`n`, the units `a / b` and `a' / b'` of `ZMod n` agree exactly when `n ∣ a b' - a' b`. -/
theorem unitOfIsCoprime_div_eq_iff {n : ℕ} {a b a' b' : ℤ} (ha : IsCoprime a n)
    (hb : IsCoprime b n) (ha' : IsCoprime a' n) (hb' : IsCoprime b' n) :
    ZMod.unitOfIsCoprime a ha / ZMod.unitOfIsCoprime b hb =
        ZMod.unitOfIsCoprime a' ha' / ZMod.unitOfIsCoprime b' hb' ↔
      (n : ℤ) ∣ a * b' - a' * b := by
  rw [div_eq_div_iff_mul_eq_mul, Units.ext_iff]
  simp only [Units.val_mul, ZMod.coe_unitOfIsCoprime, ← Int.cast_mul]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ← dvd_neg, neg_sub]

end ZMod

variable {N : ℕ} [NeZero N]

/-! ### Labels of cusps -/

variable (N) in
/-- **The label of the cusp `γ • ∞` of `Γ₀(N)`.** For `γ ∈ SL(2, ℤ)` with bottom row `(c, d)`,
it is the divisor `g = gcd(c, N)` of `N` together with the unit `(c / g) / d` modulo
`gcd(g, N / g)`. Matrices representing the same cusp have the same label
(`gamma0CuspLabel_eq_iff`), and `gamma0CuspOrbitEquiv` is the resulting bijection. -/
noncomputable def gamma0CuspLabel (γ : SL(2, ℤ)) :
    Σ g : N.divisors, (ZMod (Nat.gcd g (N / g)))ˣ :=
  ⟨⟨Int.gcd (γ 1 0) N,
      Nat.mem_divisors.mpr ⟨Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ..), NeZero.ne N⟩⟩,
    ZMod.unitOfIsCoprime (γ 1 0 / Int.gcd (γ 1 0) N) (by
        refine (Int.isCoprime_div_gcd_div_gcd (NeZero.ne N) (γ 1 0)).of_isCoprime_of_dvd_right ?_
        exact Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right ..)) /
      ZMod.unitOfIsCoprime (γ 1 1) ((bottom_row_coprime γ).symm.of_isCoprime_of_dvd_right
        ((Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left ..)).trans (Int.gcd_dvd_left ..)))⟩

/-- The divisor in the label of `γ` is `gcd(c, N)`, for `c` the lower-left entry of `γ`. -/
@[simp]
theorem coe_gamma0CuspLabel_fst (γ : SL(2, ℤ)) :
    ((gamma0CuspLabel N γ).1 : ℕ) = Int.gcd (γ 1 0) N :=
  (rfl)

/-- The residue in the label of `γ` is `(c / g) / d`, for `(c, d)` the bottom row of `γ` and
`g = gcd(c, N)`: its product with `d` is `c / g`. -/
theorem coe_gamma0CuspLabel_snd_mul (γ : SL(2, ℤ)) :
    ((gamma0CuspLabel N γ).2 : ZMod (Nat.gcd (gamma0CuspLabel N γ).1
      (N / (gamma0CuspLabel N γ).1))) * (γ 1 1 : ℤ) = (γ 1 0 / Int.gcd (γ 1 0) N : ℤ) := by
  rw [gamma0CuspLabel]
  dsimp only
  generalize_proofs _ _ hd
  rw [← ZMod.coe_unitOfIsCoprime (γ 1 1) hd, ← Units.val_mul, div_mul_cancel,
    ZMod.coe_unitOfIsCoprime]

/-- Two matrices have the same label exactly when their bottom rows `(c, d)` and `(c', d')`
satisfy `N ∣ c d' - c' d + j c c'` for some integer `j`. -/
theorem gamma0CuspLabel_eq_iff_exists_dvd (γ γ' : SL(2, ℤ)) :
    gamma0CuspLabel N γ = gamma0CuspLabel N γ' ↔
      ∃ j : ℤ, (N : ℤ) ∣ γ 1 0 * γ' 1 1 - γ' 1 0 * γ 1 1 + j * γ 1 0 * γ' 1 0 := by
  have hc (c : ℤ) : c = Int.gcd c N * (c / Int.gcd c N) :=
    (Int.mul_ediv_cancel' (Int.gcd_dvd_left ..)).symm
  have hN : (N : ℤ) = Int.gcd (γ 1 0) N * (N / Int.gcd (γ 1 0) N : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' (Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ..))).symm
  -- The residues live in `ZMod` of moduli that agree only propositionally, so they are compared
  -- as `HEq`; once the divisors are identified this is `ZMod.unitOfIsCoprime_div_eq_iff`.
  have hx {g g' : ℕ} (hg : g = g') {a b a' b' : ℤ} (ha : IsCoprime a (Nat.gcd g (N / g) : ℤ))
      (hb : IsCoprime b (Nat.gcd g (N / g) : ℤ)) (ha' : IsCoprime a' (Nat.gcd g' (N / g') : ℤ))
      (hb' : IsCoprime b' (Nat.gcd g' (N / g') : ℤ)) :
      HEq (ZMod.unitOfIsCoprime a ha / ZMod.unitOfIsCoprime b hb)
          (ZMod.unitOfIsCoprime a' ha' / ZMod.unitOfIsCoprime b' hb') ↔
        (Nat.gcd g (N / g) : ℤ) ∣ a * b' - a' * b := by
    subst hg
    exact heq_iff_eq.trans (ZMod.unitOfIsCoprime_div_eq_iff ..)
  rw [gamma0CuspLabel, gamma0CuspLabel, Sigma.mk.inj_iff, Subtype.mk.injEq]
  constructor
  · rintro ⟨hg, hx'⟩
    rw [hx hg, ← hg] at hx'
    exact Int.exists_dvd_mul_sub_mul_add_mul_of_gcd_dvd hN (hc _) (hg ▸ hc _)
      (Int.isCoprime_div_gcd_div_gcd (NeZero.ne N) _)
      (hg ▸ Int.isCoprime_div_gcd_div_gcd (NeZero.ne N) _) hx'
  · rintro ⟨j, h⟩
    have hg := Int.gcd_eq_gcd_of_dvd_mul_sub_mul_add_mul (bottom_row_coprime γ)
      (bottom_row_coprime γ') h
    refine ⟨hg, (hx hg ..).mpr ?_⟩
    rw [← hg]
    exact Int.gcd_dvd_mul_sub_mul_of_dvd_mul_sub_mul_add_mul
      (Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast NeZero.ne N)).ne' hN (hc _) (hg ▸ hc _) h

/-- Every divisor `g` of `N` and every unit modulo `gcd(g, N / g)` is a label: that of a matrix
with bottom row `(g, d)`. -/
theorem gamma0CuspLabel_surjective : Function.Surjective (gamma0CuspLabel N) := by
  rintro ⟨⟨g, hg⟩, x⟩
  have hgN : g ∣ N := Nat.dvd_of_mem_divisors hg
  have : NeZero g := ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors hg)⟩
  obtain ⟨y, hy⟩ := ZMod.unitsMap_surjective (Nat.gcd_dvd_left g (N / g)) x⁻¹
  have hgd : IsCoprime (g : ℤ) ((y : ZMod g).val : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime y).symm
  have hmem : ![(g : ℤ), ((y : ZMod g).val : ℤ)] ∈
      {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} := hgd
  obtain ⟨γ, -, hγ⟩ := bottom_row_surj hmem
  have hc : γ 1 0 = g := congrFun hγ 0
  have hd : γ 1 1 = ((y : ZMod g).val : ℤ) := congrFun hγ 1
  have hgcd : Int.gcd (γ 1 0) N = g := by
    rw [hc, Int.gcd_natCast_natCast, Nat.gcd_eq_left hgN]
  have h1 : γ 1 0 / Int.gcd (γ 1 0) N = 1 := by
    rw [hgcd, hc]
    exact Int.ediv_self (by exact_mod_cast NeZero.ne g)
  refine ⟨γ, ?_⟩
  subst hgcd
  rw [gamma0CuspLabel]
  refine Sigma.ext rfl (heq_of_eq ?_)
  dsimp only
  rw [div_eq_iff_eq_mul, Units.ext_iff]
  simp only [Units.val_mul, ZMod.coe_unitOfIsCoprime, h1, Int.cast_one]
  rw [hd, Int.cast_natCast, ZMod.natCast_val, ← ZMod.unitsMap_val (Nat.gcd_dvd_left _ _), hy,
    Units.mul_inv]

end TauCeti
