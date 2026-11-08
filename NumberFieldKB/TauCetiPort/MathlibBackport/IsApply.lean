/-
Copyright (c) 2026 The Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Mathlib contributors
-/
module

public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Backport from Mathlib master: `IsOneApplyEqSelf` and `IsMulApplyEqComp` for endomorphisms

Mathlib master (`a1f75768`, `Mathlib/Algebra/Module/LinearMap/End.lean` and
`Mathlib/Algebra/Module/Equiv/Basic.lean`) registers these instances, so that the generic lemmas
`one_apply_eq_self` and `mul_apply_eq_comp` apply to `Module.End R M` and `M ≃ₗ[R] M`. Mathlib v4.35.0 has
the classes (with the carrier as an explicit `outParam`) but not these instances. Tau Ceti's representation
theory files use the generic lemmas, so the ported copies import this file. Proofs are `rfl`, as upstream.
-/

@[expose] public section

namespace Module.End

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

instance instIsOneApplyEqSelfBackport : IsOneApplyEqSelf (Module.End R M) M where

instance instIsMulApplyEqCompBackport : IsMulApplyEqComp (Module.End R M) M where

end Module.End

namespace LinearEquiv

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

instance instIsOneApplyEqSelfBackport : IsOneApplyEqSelf (M ≃ₗ[R] M) M where

instance instIsMulApplyEqCompBackport : IsMulApplyEqComp (M ≃ₗ[R] M) M where

end LinearEquiv
