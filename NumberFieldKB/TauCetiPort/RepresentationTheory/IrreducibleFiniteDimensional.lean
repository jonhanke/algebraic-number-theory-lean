/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Port of a fact available in newer Mathlib: an irreducible representation of a
finite group over a field is finite-dimensional.  Not in Tau Ceti; written for this Mathlib.
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic

/-!
# Irreducible representations of finite groups are finite-dimensional

Newer Mathlib provides this as an instance; the pinned Mathlib does not, and the ported character
theory (`CharacterTable.Pairing`, `.Independence`) expects it.
-/

public section

namespace Representation

variable {G k V : Type*} [Group G] [Finite G] [Field k] [AddCommGroup V] [Module k V]

theorem IsIrreducible.finiteDimensional' (ρ : Representation k G V) [ρ.IsIrreducible] :
    FiniteDimensional k V := by
  have h : IsSimpleModule (MonoidAlgebra k G) ρ.asModule := inferInstance
  have h1 : Module.Finite (MonoidAlgebra k G) ρ.asModule := inferInstance
  have h2 : Module.Finite k (MonoidAlgebra k G) := inferInstance
  have h3 : Module.Finite k ρ.asModule := Module.Finite.trans (MonoidAlgebra k G) _
  exact Module.Finite.equiv ρ.asModuleEquiv

end Representation
