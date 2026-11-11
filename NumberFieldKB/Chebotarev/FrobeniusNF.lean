import NumberFieldKB.Chebotarev.Frobenius
import Mathlib.RingTheory.Frobenius
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Frobenius elements in Galois extensions of number fields
Number-field instances of the abstract results of `NumberFieldKB.Chebotarev.Frobenius`: `K ⊆ L` number
fields, `L/K` Galois, `𝔓` a prime of `𝓞 L` with finite residue field (e.g. `𝔓 ≠ ⊥`, see
`finite_quotient_of_ne_bot`), unramified over `K` (`Algebra.IsUnramifiedAt (𝓞 K) 𝔓`).
-/

set_option linter.unusedSectionVars false

open NumberField Ideal

namespace NumberFieldKB.Chebotarev

section

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois K L] (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]

/-- A nonzero ideal of `𝓞 L` has finite quotient. -/
theorem finite_quotient_of_ne_bot (h : 𝔓 ≠ ⊥) : Finite (𝓞 L ⧸ 𝔓) :=
  Ideal.finiteQuotientOfFreeOfNeBot 𝔓 h

/-- The residue field of `𝔓 ∩ F` is finite when that of `𝔓` is. -/
instance finite_quotient_under_nf (F : Type*) [Field F] [NumberField F] [Algebra F L]
    [Finite (𝓞 L ⧸ 𝔓)] : Finite (𝓞 F ⧸ 𝔓.under (𝓞 F)) := finite_quotient_under 𝔓

/-- Residue field extensions above a prime of `K` with finite residue field are separable. -/
instance hasSeparableResidueFieldsAt_under [Finite (𝓞 L ⧸ 𝔓)] :
    Algebra.HasSeparableResidueFieldsAt (𝓞 K) (𝓞 L) (𝔓.under (𝓞 K)) := by
  have : Finite (𝓞 K ⧸ 𝔓.under (𝓞 K)) := finite_quotient_under 𝔓
  have : (𝔓.under (𝓞 K)).IsMaximal := isMaximal_under_of_finite 𝔓
  infer_instance

/-- `𝔓` unramified over `K` means `e(𝔓|p) = 1`, in the form `ramificationIdxIn`. -/
theorem ramificationIdxIn_eq_one_of_isUnramifiedAt [Finite (𝓞 L ⧸ 𝔓)]
    [Algebra.IsUnramifiedAt (𝓞 K) 𝔓] :
    (𝔓.under (𝓞 K)).ramificationIdxIn (𝓞 L) = 1 := by
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (𝔓.under (𝓞 K)) 𝔓 Gal(L/K)]
  exact (Ideal.ramificationIdx_eq_one_iff).mpr ‹_›

/-- **Order of Frobenius** (number field form): `ord Frob_𝔓 = f(𝔓 | p)`. -/
theorem orderOf_arithFrobAt_nf [Finite (𝓞 L ⧸ 𝔓)] [Algebra.IsUnramifiedAt (𝓞 K) 𝔓] :
    orderOf (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) = 𝔓.inertiaDeg (𝓞 K) := by
  have : (𝔓.under (𝓞 K)).IsMaximal := isMaximal_under_of_finite 𝔓
  have : 𝔓.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
  exact orderOf_arithFrobAt (G := Gal(L/K)) (𝔓.under (𝓞 K)) 𝔓
    (ramificationIdxIn_eq_one_of_isUnramifiedAt 𝔓)

/-- **Frobenius in a tower** (Milne ANT Prop. 8.13(b)): for `K ⊆ E ⊆ L` with `L/K` Galois and `𝔓` an
unramified prime of `L`, `Frob_𝔓(L/E) = Frob_𝔓(L/K) ^ f` (as elements of `Gal(L/K)`, via restriction of
scalars), where `f = f(𝔓 ∩ E | p)` is the residue degree of `𝔓 ∩ E` over `K`. -/
theorem restrictScalars_arithFrobAt_eq_pow (E : IntermediateField K L) [Finite (𝓞 L ⧸ 𝔓)]
    [Algebra.IsUnramifiedAt (𝓞 K) 𝔓] :
    (arithFrobAt (𝓞 E) Gal(L/E) 𝔓).restrictScalars K =
      arithFrobAt (𝓞 K) Gal(L/K) 𝔓 ^ (𝔓.under (𝓞 E)).inertiaDeg (𝓞 K) :=
  arithFrobAt_subgroup_eq_pow (A := 𝓞 K) (B := 𝓞 E) (C := 𝓞 L) (G := Gal(L/K)) (H := Gal(L/E))
    (AlgEquiv.restrictScalarsHom K) (fun _ _ => rfl) 𝔓
    (ramificationIdxIn_eq_one_of_isUnramifiedAt 𝔓)

/-- If `𝔓 ∩ E` has residue degree `1` over `K`, the Frobenius elements of `L/E` and `L/K` at `𝔓`
agree. -/
theorem restrictScalars_arithFrobAt_eq_of_inertiaDeg_eq_one (E : IntermediateField K L)
    [Finite (𝓞 L ⧸ 𝔓)] [Algebra.IsUnramifiedAt (𝓞 K) 𝔓]
    (h : (𝔓.under (𝓞 E)).inertiaDeg (𝓞 K) = 1) :
    (arithFrobAt (𝓞 E) Gal(L/E) 𝔓).restrictScalars K = arithFrobAt (𝓞 K) Gal(L/K) 𝔓 := by
  rw [restrictScalars_arithFrobAt_eq_pow, h, pow_one]

/-- `Frob_𝔓 = 1` iff the residue degree of `𝔓` over `K` is `1`. -/
theorem arithFrobAt_eq_one_iff_nf [Finite (𝓞 L ⧸ 𝔓)] [Algebra.IsUnramifiedAt (𝓞 K) 𝔓] :
    arithFrobAt (𝓞 K) Gal(L/K) 𝔓 = 1 ↔ 𝔓.inertiaDeg (𝓞 K) = 1 := by
  rw [← orderOf_arithFrobAt_nf 𝔓, orderOf_eq_one_iff]

/-- **Splitting via Frobenius** (number field form): an unramified `𝔭 = 𝔓 ∩ K` splits completely in
`L` (there are `[L:K]` primes of `𝓞 L` above it) iff `Frob_𝔓 = 1`. -/
theorem arithFrobAt_eq_one_iff_ncard_primesOver_nf [Finite (𝓞 L ⧸ 𝔓)]
    [Algebra.IsUnramifiedAt (𝓞 K) 𝔓] :
    arithFrobAt (𝓞 K) Gal(L/K) 𝔓 = 1 ↔
      ((𝔓.under (𝓞 K)).primesOver (𝓞 L)).ncard = Module.finrank K L := by
  have : (𝔓.under (𝓞 K)).IsMaximal := isMaximal_under_of_finite 𝔓
  have : 𝔓.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
  rw [← IsGaloisGroup.card_eq_finrank Gal(L/K) K L]
  exact _root_.NumberFieldKB.Chebotarev.arithFrobAt_eq_one_iff_ncard_primesOver (G := Gal(L/K)) (𝔓.under (𝓞 K)) 𝔓
    (ramificationIdxIn_eq_one_of_isUnramifiedAt 𝔓)

/-- If `𝔓` is unramified over `K` then so is `𝔓 ∩ E`, for any intermediate Galois field `E`. -/
theorem ramificationIdxIn_under_eq_one (E : IntermediateField K L) [IsGalois K E]
    [Finite (𝓞 L ⧸ 𝔓)] [Algebra.IsUnramifiedAt (𝓞 K) 𝔓] :
    ((𝔓.under (𝓞 E)).under (𝓞 K)).ramificationIdxIn (𝓞 E) = 1 := by
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx ((𝔓.under (𝓞 E)).under (𝓞 K)) (𝔓.under (𝓞 E))
    Gal(E/K)]
  have h1 : 𝔓.ramificationIdx (𝓞 K) = 1 := Ideal.ramificationIdx_eq_one 𝔓 (𝓞 K)
  have := Ideal.ramificationIdx_below_dvd (R := 𝓞 K) (S := 𝓞 E) (T := 𝓞 L) (𝔓.under (𝓞 E)) 𝔓
  rw [h1] at this
  exact Nat.dvd_one.mp this

/-- **Frobenius and restriction** (Milne ANT Prop. 8.13(a)): for `K ⊆ E ⊆ L` with `L/K` and `E/K`
Galois and `𝔓` an unramified prime of `L`, the restriction to `E` of `Frob_𝔓(L/K)` is
`Frob_{𝔓 ∩ E}(E/K)`. -/
theorem restrictNormalHom_arithFrobAt (E : IntermediateField K L) [IsGalois K E]
    [Finite (𝓞 L ⧸ 𝔓)] [Algebra.IsUnramifiedAt (𝓞 K) 𝔓] :
    AlgEquiv.restrictNormalHom E (arithFrobAt (𝓞 K) Gal(L/K) 𝔓) =
      arithFrobAt (𝓞 K) Gal(E/K) (𝔓.under (𝓞 E)) := by
  have : Algebra.HasSeparableResidueFieldsAt (𝓞 K) (𝓞 E) ((𝔓.under (𝓞 E)).under (𝓞 K)) := by
    have : Finite (𝓞 K ⧸ (𝔓.under (𝓞 E)).under (𝓞 K)) := finite_quotient_under _
    have : ((𝔓.under (𝓞 E)).under (𝓞 K)).IsMaximal := isMaximal_under_of_finite _
    infer_instance
  refine map_arithFrobAt_eq (A := 𝓞 K) (B := 𝓞 E) (C := 𝓞 L) (G := Gal(L/K)) (G' := Gal(E/K))
    (AlgEquiv.restrictNormalHom E) ?_ 𝔓 (ramificationIdxIn_under_eq_one 𝔓 E)
  intro g b
  apply Subtype.ext
  change algebraMap E L ((AlgEquiv.restrictNormalHom E g) (b : E)) = g ((b : E) : L)
  exact AlgEquiv.restrictNormal_commutes g E (b : E)

end

end NumberFieldKB.Chebotarev
