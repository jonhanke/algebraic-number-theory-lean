import NumberFieldKB.HilbertClassField.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Class number one: $K$ is its own Hilbert class field

If $\mathrm{Cl}_K$ is trivial then $H = K$ is a Hilbert class field of $K$ in the sense of
`NumberFieldKB.HilbertClassField.IsHilbertClassField`: the identity extension $K/K$ is Galois, unramified at every
finite prime and every infinite place, and both $\mathrm{Cl}_K$ and $\mathrm{Gal}(K/K)$ are trivial, so the Artin map
is the unique isomorphism between them (`isHilbertClassField_self_of_classNumber_eq_one`,
`hilbertClassFieldExists_of_classNumber_eq_one`).
-/

open NumberField IsDedekindDomain Ideal
open NumberFieldKB.Chebotarev

namespace NumberFieldKB.HilbertClassField

noncomputable section

set_option linter.style.haveILetI false

/-- **Class number one: $K$ is its own Hilbert class field.** If `classNumber K = 1`, then `IsHilbertClassField K K`.
*Proof:* $K/K$ is unramified at every prime and every infinite place (the identity is étale), and
$\mathrm{Cl}_K$ and $\mathrm{Gal}(K/K)$ are both trivial, so the Artin condition holds for the trivial isomorphism. -/
@[kb "neukirch1999" "Ch. VI, §6: for class number one the Hilbert class field is K itself [unverified locator]"]
theorem isHilbertClassField_self_of_classNumber_eq_one {K : Type} [Field K] [NumberField K]
    (h : classNumber K = 1) : IsHilbertClassField K K := by
  haveI : Subsingleton (ClassGroup (𝓞 K)) := Fintype.card_le_one_iff_subsingleton.mp h.le
  haveI : Unique (ClassGroup (𝓞 K)) := uniqueOfSubsingleton 1
  haveI : Unique Gal(K/K) := uniqueOfSubsingleton 1
  refine ⟨fun 𝔭 Q _ _ => ?_, inferInstance, ⟨MulEquiv.ofUnique, fun _ _ => Subsingleton.elim _ _⟩⟩
  -- the algebra `𝓞 K → 𝓞 K` induced by `Algebra.id K` is `Algebra.id (𝓞 K)`, for which `IsUnramifiedAt` is an instance
  have e : inst_ringOfIntegersAlgebra K K = Algebra.id (𝓞 K) := Algebra.algebra_ext _ _ fun _ => rfl
  convert (inferInstance : @Algebra.IsUnramifiedAt (𝓞 K) (𝓞 K) _ _ (Algebra.id _) Q _)

/-- **Class number one: the Hilbert class field exists** (it is $K$ itself). -/
theorem hilbertClassFieldExists_of_classNumber_eq_one {K : Type} [Field K] [NumberField K]
    (h : classNumber K = 1) : HilbertClassFieldExists K :=
  ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
    isHilbertClassField_self_of_classNumber_eq_one h⟩

end

end NumberFieldKB.HilbertClassField
