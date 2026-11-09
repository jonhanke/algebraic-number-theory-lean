import NumberFieldKB.MilneCFT.LocalCFT.Unconditional
import NumberFieldKB.MilneCFT.LocalCFT.ExistenceYamaguchi
import NumberFieldKB.MilneCFT.Ch3Existence

/-!
# Local class field theory in every characteristic

With the named statement `LocalExistenceInput` (Milne, *CFT*, I, Theorem 1.4, hard half) proved in every
characteristic from Yamaguchi's library (`localExistenceInput_yamaguchi`), the consumers stated in characteristic zero
in `LocalCFT/Unconditional.lean` hold for every nonarchimedean local field, in particular for the local fields
$\mathbb F_q((t))$ of positive characteristic. Theorem 1.1 still uses Tau Ceti's local Artin map
(`localReciprocityExistence`), which fixes $K$ and $\Omega$ in `Type`; Chapter III, Theorem 5.1 is stated
there for `Type`. Hasse's Theorem 0.9 (`hasse_theorem_charZero`) stays in characteristic zero: in positive
characteristic not every subgroup of finite index of $K^\times$ is open.
-/

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch3

open NumberFieldKB.MilneCFT.LocalCFT

/-- **Theorem 5.1, existence theorem, unconditional** (Milne, *CFT*, III, Theorem 5.1, p. 115): every open subgroup of
finite index of $K^\times$ is a norm group, for every nonarchimedean local field $K$ (every characteristic). -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 5.1, p. 115"]
theorem theorem_5_1' {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ))
    (hfi : H.FiniteIndex) : IsNormGroup K Ω H :=
  theorem_5_1 (localExistenceInput_yamaguchi K Ω) H hopen hfi

end NumberFieldKB.MilneCFT.Ch3

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **Theorem 1.4, local existence theorem, unconditional** (Milne, *CFT*, I, Theorem 1.4), every characteristic: the
norm groups in $K^\times$ are exactly the open subgroups of finite index. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.4"]
theorem isNormGroup_iff_unconditional (H : Subgroup Kˣ) :
    IsNormGroup K Ω H ↔ IsOpen (H : Set Kˣ) ∧ H.FiniteIndex :=
  isNormGroup_iff (localReciprocityExistence K Ω) (localExistenceInput_yamaguchi K Ω) H

/-- **Theorem 1.1, local reciprocity law, unconditional** (Milne, *CFT*, I, Theorem 1.1), every characteristic: there
is a unique family $\phi_L : K^\times\to\mathrm{Gal}(L/K)$ satisfying (a) and (b). -/
@[kb "milne2020cft" "Ch. I, Theorem 1.1"]
theorem localReciprocityLaw_unconditional :
    ∃! φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K), IsLocalArtinMap φ :=
  localReciprocityLaw (localReciprocityExistence K Ω) (localExistenceInput_yamaguchi K Ω) (unramifiedInput K Ω)

/-- **Theorem 1.13, unconditional** (Milne, *CFT*, I, p. 30), every characteristic: there is at most one family
satisfying the conditions of Theorem 1.1. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.13"]
theorem isLocalArtinMap_unique_unconditional {φ ψ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)}
    (hφ : IsLocalArtinMap φ) (hψ : IsLocalArtinMap ψ) : φ = ψ :=
  isLocalArtinMap_unique_of_existence (isNormGroup_iff_unconditional Ω) hφ hψ

/-- **Corollary 1.5 (a), unconditional** (Milne, *CFT*, I), every characteristic: $L\mapsto\mathrm{Nm}(L^\times)$ is a
bijection onto the open subgroups of finite index. -/
@[kb "milne2020cft" "Ch. I, Corollary 1.5 (a)"]
theorem existsUnique_normGroup_eq_unconditional (H : Subgroup Kˣ) (hH : IsOpen (H : Set Kˣ))
    (hfi : H.FiniteIndex) :
    ∃ L : FiniteAbelianExt K Ω, normGroup L.toField = H ∧
      ∀ L' : FiniteAbelianExt K Ω, normGroup L'.toField = H → L'.toField = L.toField :=
  existsUnique_normGroup_eq (localReciprocityExistence K Ω) (localExistenceInput_yamaguchi K Ω) H hH hfi

end NumberFieldKB.MilneCFT.LocalCFT
