/-
Copyright (c) the PrimeNumberTheoremAnd contributors (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd).
Released under Apache 2.0 license as described in the file LICENSE of that repository.
Authors: the PrimeNumberTheoremAnd contributors
-/
import Mathlib.Algebra.Notation.Support

namespace NumberFieldKB.PNTPort

section
open Function

variable {α : Type*} [Zero α]

theorem _root_.Function.support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem _root_.Function.support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end

end NumberFieldKB.PNTPort
