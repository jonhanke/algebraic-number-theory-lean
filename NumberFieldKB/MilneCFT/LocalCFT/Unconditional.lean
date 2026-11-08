import NumberFieldKB.MilneCFT.LocalCFT.Uniqueness
import NumberFieldKB.MilneCFT.LocalCFT.UnramifiedTauCeti
import NumberFieldKB.MilneCFT.Ch3ArtinMaps
import NumberFieldKB.MilneCFT.Ch2Example314TauCeti
import NumberFieldKB.MilneCFT.LocalCFT.ReciprocityTauCeti
import NumberFieldKB.MilneCFT.LocalCFT.ExistenceTauCeti
import NumberFieldKB.MilneCFT.LocalCFT.Complements
import NumberFieldKB.MilneCFT.Ch3Artin
import NumberFieldKB.MilneCFT.Ch5IdelesChar

/-!
# Consequences of the named statements proved from Tau Ceti

The named statements `UnramifiedInput` (Milne, *CFT*, I, §1; `unramifiedInput`), `Example3_14` (II, Example 3.14;
`example3_14`), `LocalReciprocityExistence` (I, Theorem 1.1, for $K$ and $\Omega$ in `Type`;
`localReciprocityExistence`) and `LocalExistenceInput` (I, Theorem 1.4, for $K$ of characteristic zero in `Type`;
`localExistenceInput`) are proved from the Tau Ceti port. This file states their consumers without them as hypotheses (the
conditional forms stay where they are, unchanged).
-/

open scoped ValuativeRel

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **Theorem 1.13** (Milne, *CFT*, I, p. 30), with `UnramifiedInput` proved: assuming the local existence theorem 1.4,
there is at most one family satisfying the conditions of Theorem 1.1. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.13"]
theorem isLocalArtinMap_unique_of_existence
    (h4 : ∀ H : Subgroup Kˣ, IsNormGroup K Ω H ↔ IsOpen (H : Set Kˣ) ∧ H.FiniteIndex)
    {φ ψ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)}
    (hφ : IsLocalArtinMap φ) (hψ : IsLocalArtinMap ψ) : φ = ψ :=
  isLocalArtinMap_unique h4 (unramifiedInput K Ω) hφ hψ

end NumberFieldKB.MilneCFT.LocalCFT

namespace NumberFieldKB.MilneCFT.Ch3

open NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **Lemma 3.7** (Milne, *CFT*, III, p. 109), with `UnramifiedInput` proved: for $L/K$ unramified,
$\phi_{L/K}(u\pi^m) = \mathrm{Frob}^m$. -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 3.7, p. 109"]
theorem lemma_3_7' {φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)}
    (hφ : IsLocalArtinMap φ) (L : FiniteAbelianExt K Ω) (hL : IsUnramifiedExt L.toField)
    {σ : Gal(L.toField/K)} (hσ : IsFrobenius L.toField σ) {π : 𝒪[K]} (hπ : Irreducible π) {u : Kˣ}
    (hu : u ∈ unitGroup K) (m : ℤ) : φ L (u * primeUnit hπ ^ m) = σ ^ m :=
  lemma_3_7 (unramifiedInput K Ω) hφ L hL hσ hπ hu m

end NumberFieldKB.MilneCFT.Ch3

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology

/-- **Example 3.14** (Milne, *CFT*, II, p. 85), the consequence, with the named statement `Example3_14` proved: Tate's
theorem gives $H^r_T(G,\mathbb Z)\simeq H^{r+2}_T(G,L^\times)$. Conditional only on Tate's theorem `Thm3_11`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 3.14, p. 85"]
theorem example_3_14_of_thm3_11 (h311 : Thm3_11) (K : Type) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (L : Type) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (r : ℤ) :
    Nonempty (tateCohomology (trivial ℤ (L ≃ₐ[K] L) ℤ) r ≅
      tateCohomology (Rep.ofAlgebraAutOnUnits K L) (r + 2)) :=
  example_3_14 h311 example3_14 K L r

end NumberFieldKB.MilneCFT

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **Theorem 1.1, local reciprocity law, in characteristic zero, unconditional** (Milne, *CFT*, I, Theorem 1.1): for
a nonarchimedean local field $K$ of characteristic zero (a finite extension of $\mathbb Q_p$), there is a unique family
$\phi_L : K^\times\to\mathrm{Gal}(L/K)$ satisfying (a) and (b). -/
@[kb "milne2020cft" "Ch. I, Theorem 1.1"]
theorem localReciprocityLaw_charZero [CharZero K] :
    ∃! φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K), IsLocalArtinMap φ :=
  localReciprocityLaw (localReciprocityExistence K Ω) (localExistenceInput K Ω) (unramifiedInput K Ω)

/-- **Theorem 1.4, local existence theorem, in characteristic zero, unconditional** (Milne, *CFT*, I, Theorem 1.4):
the norm groups in $K^\times$ are exactly the open subgroups of finite index. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.4"]
theorem isNormGroup_iff_charZero [CharZero K] (H : Subgroup Kˣ) :
    IsNormGroup K Ω H ↔ IsOpen (H : Set Kˣ) ∧ H.FiniteIndex :=
  isNormGroup_iff (localReciprocityExistence K Ω) (localExistenceInput K Ω) H

/-- **Corollary 1.5 (a), in characteristic zero, unconditional** (Milne, *CFT*, I): $L\mapsto\mathrm{Nm}(L^\times)$ is a
bijection onto the open subgroups of finite index. -/
@[kb "milne2020cft" "Ch. I, Corollary 1.5 (a)"]
theorem existsUnique_normGroup_eq_charZero [CharZero K] (H : Subgroup Kˣ) (hH : IsOpen (H : Set Kˣ))
    (hfi : H.FiniteIndex) :
    ∃ L : FiniteAbelianExt K Ω, normGroup L.toField = H ∧
      ∀ L' : FiniteAbelianExt K Ω, normGroup L'.toField = H → L'.toField = L.toField :=
  existsUnique_normGroup_eq (localReciprocityExistence K Ω) (localExistenceInput K Ω) H hH hfi

/-- **Theorem 0.9 (Hasse 1930), unconditional** (Milne, *CFT*, Introduction): for a local field $K$ of characteristic
zero, the norm groups of the finite abelian extensions have finite index, and $L\mapsto\mathrm{Nm}(L^\times)$ is an
order-reversing bijection onto the subgroups of finite index. -/
@[kb "milne2020cft" "Introduction, Theorem 0.9"]
theorem hasse_theorem_charZero [CharZero K] :
    (∀ L : FiniteAbelianExt K Ω, (normGroup L.toField).FiniteIndex) ∧
    (∀ L L' : FiniteAbelianExt K Ω, L.toField ≤ L'.toField ↔ normGroup L'.toField ≤ normGroup L.toField) ∧
    (∀ H : Subgroup Kˣ, H.FiniteIndex → ∃ L : FiniteAbelianExt K Ω, normGroup L.toField = H ∧
      ∀ L' : FiniteAbelianExt K Ω, normGroup L'.toField = H → L'.toField = L.toField) :=
  hasse_theorem (localReciprocityExistence K Ω) (localExistenceInput K Ω)

end NumberFieldKB.MilneCFT.LocalCFT

namespace NumberFieldKB.MilneCFT.Ch3

open NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **Theorem 3.4, unconditional** (Milne, *CFT*, III, Theorem 3.4, p. 108): the local Artin map exists, for $K$
and $\Omega$ in `Type`. -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 3.4, p. 108"]
theorem theorem_3_4' :
    ∃ φ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K),
      (∀ (L L' : FiniteAbelianExt K Ω) (h : L.toField ≤ L'.toField) (a : Kˣ), galRestrict h (φ L' a) = φ L a) ∧
      (∀ {π : 𝒪[K]} (hπ : Irreducible π) (L : FiniteAbelianExt K Ω), IsUnramifiedExt L.toField →
        IsFrobenius L.toField (φ L (primeUnit hπ))) ∧
      ∀ L : FiniteAbelianExt K Ω, normGroup L.toField ≤ (φ L).ker ∧
        ∃ e : Kˣ ⧸ normGroup L.toField ≃* Gal(L.toField/K), ∀ a : Kˣ, e a = φ L a :=
  theorem_3_4 (localReciprocityExistence K Ω)

end NumberFieldKB.MilneCFT.Ch3

namespace NumberFieldKB.MilneCFT

open NumberFieldKB.MilneCFT.LocalCFT

/-- **Proposition 4.12(c), unconditional** (Milne, *CFT*, V, Proposition 4.12(c)): for a finite unramified abelian
extension $L$ of a nonarchimedean local field $F$ (in `Type`), $\mathrm{Nm}(L^\times)\supseteq\mathcal O_F^\times$. -/
@[kb "milne2020cft" "Ch. V, Proposition 4.12(c)"]
theorem prop_4_12c' (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (Ω : Type) [Field Ω] [Algebra F Ω] [IsSepClosure F Ω] (L : FiniteAbelianExt F Ω)
    (hL : IsUnramifiedExt L.toField) :
    (Units.map (algebraMap 𝒪[F] F).toMonoidHom).range ≤ normGroup L.toField :=
  prop_4_12c F Ω (localReciprocityExistence F Ω) (unramifiedInput F Ω) L hL

end NumberFieldKB.MilneCFT
