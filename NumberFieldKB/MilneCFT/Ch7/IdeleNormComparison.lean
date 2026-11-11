import NumberFieldKB.MilneCFT.Ch7.FirstInequality
import NumberFieldKB.Ideles.RelativeNormTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Global.Ideles.Norm.Open
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Openness of idele norm groups from Tau Ceti, through a comparison of idele norms

Tau Ceti proves that $\mathrm{Nm}_{L/K}\mathbb I_L$ is open in $\mathbb I_K$ for every finite extension of number
fields (`TauCeti.GlobalNumberFields.isOpen_range_ideleNormMap`, ported under `NumberFieldKB/TauCetiPort/`, Tau Ceti
main `67aa1716`, Apache 2.0). Its idele norm `TauCeti.GlobalNumberFields.ideleNormMap` is the product of the local norms
$\prod_{w\mid v}\mathrm{Nm}_{L_w/K_v}$ at every place; ours (`Ch7.ideleNorm`, the library's `Ideles.ideleRelNorm`) is
the determinant of multiplication on $L\otimes_K\mathbb A_K$ through QuadFormsKB's base change of adeles. Both are
Milne's $\mathrm{Nm}_{L/K}$ (Chapter V, §4, p. 177), but they are different constructions.

Their equality was first isolated as the statement `IdeleNormComparison`, from which Milne's
Proposition VII.2.8 (`Ch7.Prop2_8`) was proved (`prop2_8_of_ideleNormComparison`). The file now
**proves the comparison** (`ideleNormComparison`, from `NumberFieldKB.Ideles.ideleRelNorm_eq_ideleNormMap`, which
identifies QuadFormsKB's adelic base change with Tau Ceti's placewise $K_v\otimes_K L\cong\prod_{w\mid v}L_w$), so
Proposition 2.8 is **unconditional** (`prop2_8`).
-/

open IsDedekindDomain NumberField

namespace NumberFieldKB.MilneCFT.Ch7

variable (K : Type) [Field K] [NumberField K]

/-- **The two idele norms agree** (comparison of definitions, not a result of Milne's; proved below as
`ideleNormComparison`): for every
finite extension $L/K$ of number fields, our `ideleNorm K L` (determinant of multiplication on $L\otimes_K\mathbb A_K$,
QuadFormsKB's base change) equals Tau Ceti's `TauCeti.GlobalNumberFields.ideleNormMap K L` (the product of the local
norms $\mathrm{Nm}_{L_w/K_v}$ over $w\mid v$). Both are Milne's $\mathrm{Nm}_{L/K}$ (*CFT*, V, §4, p. 177). -/
@[kb "milne2020cft" "Ch. V, §4, p. 177 (the norm of idèles: comparison of two constructions)"]
structure IdeleNormComparison : Prop where
  eq : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] (x : IdeleGroup (𝓞 L) L),
    ideleNorm K L x = TauCeti.GlobalNumberFields.ideleNormMap K L x

variable {K}

/-- **Proposition 2.8 from the comparison of idele norms** (Milne, *CFT*, VII, Proposition 2.8, p. 207):
$\mathrm{Nm}_{L/K}\mathbb I_L$ is open in $\mathbb I_K$, for every finite extension (no Galois hypothesis is needed),
from Tau Ceti's `TauCeti.GlobalNumberFields.isOpen_range_ideleNormMap` (ported). -/
@[kb "milne2020cft" "Ch. VII, Prop. 2.8"]
theorem prop2_8_of_ideleNormComparison (h : IdeleNormComparison K) : Prop2_8 K := by
  refine ⟨fun L _ _ _ _ => ?_⟩
  have hr : (normIdeles K L : Set (IdeleGroup (𝓞 K) K)) =
      ((TauCeti.GlobalNumberFields.ideleNormMap K L).toMonoidHom.range : Set (IdeleGroup (𝓞 K) K)) := by
    ext y
    simp only [SetLike.mem_coe, normIdeles, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, (h.eq L x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, h.eq L x⟩
  rw [hr]
  exact TauCeti.GlobalNumberFields.isOpen_range_ideleNormMap K L

variable (K)

/-- **The two idele norms agree** (proof of `IdeleNormComparison`): `ideleNorm K L` is
`NumberFieldKB.Ideles.ideleRelNorm` for the basis `Module.finBasis K L`, which equals Tau Ceti's `ideleNormMap K L`
by `NumberFieldKB.Ideles.ideleRelNorm_eq_ideleNormMap`. -/
@[kb "milne2020cft" "Ch. V, §4, p. 177 (the norm of idèles: the two constructions agree)"]
theorem ideleNormComparison : IdeleNormComparison K :=
  ⟨fun L _ _ _ x => NumberFieldKB.Ideles.ideleRelNorm_eq_ideleNormMap (Module.finBasis K L) x⟩

/-- **Proposition 2.8, unconditional** (Milne, *CFT*, VII, Proposition 2.8, p. 207): $\mathrm{Nm}_{L/K}\mathbb I_L$ is
open in $\mathbb I_K$ for every finite Galois extension $L/K$ of number fields. -/
@[kb "milne2020cft" "Ch. VII, Prop. 2.8"]
theorem prop2_8 : Prop2_8 K := prop2_8_of_ideleNormComparison (ideleNormComparison K)

end NumberFieldKB.MilneCFT.Ch7
