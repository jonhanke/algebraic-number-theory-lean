/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Transporting the value group along an equivalence of valuations

Mathlib's `Valuation.IsEquiv.orderMonoidIso` transports value groups along an equivalence
of valuations. This file records its functoriality, using the corresponding results for
`Valuation.IsEquiv.orderMonoidIso₀` on value groups with zero adjoined.

## Main results

* `Valuation.IsEquiv.orderMonoidIso_symm_eq`,
  `Valuation.IsEquiv.orderMonoidIso_self` and
  `Valuation.IsEquiv.orderMonoidIso_trans_eq` : the transport respects inverses, identities
  and composition.

-/

public section

namespace Valuation

open MonoidWithZeroHom

variable {A : Type*} [Ring A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀']

/-- Backport: the transport of the value group (without zero) along an equivalence of valuations.
In Tau Ceti's Mathlib this is `Valuation.IsEquiv.orderMonoidIso`; in this Mathlib that name
denotes the transport of the value group with zero adjoined (Tau Ceti's `orderMonoidIso₀`), so
the group-level transport is named `valueGroupIso` here. -/
noncomputable def IsEquiv.valueGroupIso {v : Valuation A Γ₀} {w : Valuation A Γ₀'}
    (h : v.IsEquiv w) : v.valueGroup ≃*o w.valueGroup :=
  { h.orderMonoidIso.toMulEquiv.unzero with
    map_le_map_iff' := fun {a b} ↦ by
      rw [← WithZero.coe_le_coe (a := a) (b := b),
        ← h.orderMonoidIso.map_le_map_iff' (a := (a : v.ValueGroup₀)) (b := b),
        ← WithZero.coe_le_coe]
      simp [MulEquiv.unzero] }

/-- The value-group transport agrees with the transport of the value group with zero. -/
theorem IsEquiv.orderMonoidIso_coe {v : Valuation A Γ₀} {w : Valuation A Γ₀'}
    (h : v.IsEquiv w) (γ : v.valueGroup) :
    ((h.valueGroupIso γ : w.valueGroup) : w.ValueGroup₀) =
      h.orderMonoidIso (γ : v.ValueGroup₀) := by
  simp [IsEquiv.valueGroupIso, MulEquiv.unzero]

/-- Transport along the inverse equivalence is the inverse transport. -/
theorem IsEquiv.orderMonoidIso_symm_eq {v : Valuation A Γ₀}
    {w : Valuation A Γ₀'} (h : v.IsEquiv w) (h' : w.IsEquiv v) :
    h.valueGroupIso.symm = h'.valueGroupIso := by
  refine DFunLike.ext _ _ fun g ↦ ?_
  apply WithZero.coe_injective
  have h1 := h.orderMonoidIso_coe (h.valueGroupIso.symm g)
  rw [OrderMonoidIso.apply_symm_apply] at h1
  have h2 := h'.orderMonoidIso_coe g
  have h3 : h.orderMonoidIso.symm (g : w.ValueGroup₀) = h'.orderMonoidIso g := by
    rw [Valuation.IsEquiv.orderMonoidIso_symm h h']
  rw [h2, ← h3, h1]
  simp

/-- Transport along a valuation's equivalence with itself is the identity. -/
@[simp]
theorem IsEquiv.orderMonoidIso_self {v : Valuation A Γ₀}
    (h : v.IsEquiv v) : h.valueGroupIso = .refl _ := by
  refine DFunLike.ext _ _ fun g ↦ ?_
  apply WithZero.coe_injective
  rw [h.orderMonoidIso_coe g, Valuation.IsEquiv.orderMonoidIso_eq_refl h]
  rfl

/-- Transport along a composite equivalence is the composite transport. -/
@[simp]
theorem IsEquiv.orderMonoidIso_trans_eq {Γ₀'' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀''] {v : Valuation A Γ₀} {w : Valuation A Γ₀'}
    {u : Valuation A Γ₀''} (h : v.IsEquiv w) (h' : w.IsEquiv u) :
    h.valueGroupIso.trans h'.valueGroupIso = (h.trans h').valueGroupIso := by
  refine DFunLike.ext _ _ fun g ↦ ?_
  apply WithZero.coe_injective
  rw [OrderMonoidIso.trans_apply, h'.orderMonoidIso_coe, h.orderMonoidIso_coe,
    (h.trans h').orderMonoidIso_coe, ← Valuation.IsEquiv.orderMonoidIso_trans h h']
  rfl

end Valuation
