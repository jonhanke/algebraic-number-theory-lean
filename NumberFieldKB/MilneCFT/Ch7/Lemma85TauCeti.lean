import NumberFieldKB.MilneCFT.Ch5IdelicReciprocityTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.Cyclotomic.Compositum
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.ClassFormation
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# Milne, *Class Field Theory*, Lemmas VII.8.5 and VII.8.6, from the Tau Ceti port

Theorem VII.8.1 of Milne has two parts, for a finite extension $L/K$ of number fields:

* (a) for $L/K$ abelian, the global Artin map $\psi_{L/K}$ is trivial on the principal idèles $K^\times$;
* (b) for $L/K$ Galois, $\sum_v \mathrm{inv}_v(\alpha) = 0$ for every $\alpha \in H^2(L/K) = H^2(\mathrm{Gal}(L/K), L^\times)$.

Here (a) for $L/K$ is read with Tau Ceti's idèlic Artin map (`idelicArtinTauCeti`, equal to every global Artin map of
Chapter VII by `Ch7.T81.eq_idelicArtinTauCeti`), and (b) for $L/K$ with Tau Ceti's local invariants: a class $y$ of
$H^2(\mathrm{Gal}(L/K), L^\times)$ is inflated to the Brauer group of $K$ (`relBrInfl`), localized at every place
(`brLocalization`) and its local invariants are summed (`sumLocalInv`). The field $L$ is a finite Galois subextension
of the separable closure of $K$.

* **Lemma VII.8.5** (`Ch7.lemma8_5`): for $L/K$ abelian, (b) for $L/K$ implies (a) for $L/K$; for $L/K$ cyclic, (a)
  for $L/K$ implies (b) for $L/K$.
* **Lemma VII.8.6** (`Ch7.lemma8_6`): if (b) holds for every cyclic cyclotomic extension of $K$, it holds for every
  finite Galois extension of $K$.

Proofs. Both parts of Theorem 8.1 are theorems of the library (from the Tau Ceti port, Apache 2.0, the Tau Ceti
contributors, under `NumberFieldKB/TauCetiPort/`): (a) is `idelicArtinTauCeti_principal` (Tau Ceti
`ker_ideleClassArtinMap`), (b) is Tau Ceti's sum formula `sumLocalInv_brLocalization_eq_zero`. So the conclusions of
Lemmas 8.5 and 8.6 hold unconditionally and the lemmas follow. Milne's own argument for the cyclic case of 8.5 (the
cup product with $\delta\chi$ for an injective character $\chi$) is Tau Ceti's
`forall_sumLocalInv_brLocalization_relBrInfl_eq_zero_iff` (`Global/CharacterCarry.lean`), and his argument for 8.6
(every Brauer class is split by a cyclic cyclotomic extension, Proposition VII.7.2) is the proof of
`sumLocalInv_brLocalization_eq_zero` (`Global/Brauer/SumFormula.lean`) from the cyclic cyclotomic case
`sumLocalInv_brLocalization_relBrInfl_eq_zero_of_le_adjoin_nth_roots`; both are in the port.

Lemma VIII.4.6 is in `NumberFieldKB.MilneCFT.Ch8.Lemma46TauCeti`.
-/

open NumberField IsDedekindDomain TauCeti.ClassFieldTheory

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable {K : Type} [Field K] [NumberField K]

/-- **Lemma 8.5** (Milne, *CFT*, VII, Lemma 8.5, p. 222). Let $L/K$ be an abelian extension of number fields. If
Theorem 8.1 (b) holds for $L/K$ (the local invariants of every class of $H^2(\mathrm{Gal}(L/K), L^\times)$ sum to $0$),
then so does 8.1 (a) (the Artin map $\psi_{L/K}$ is trivial on $K^\times$). Conversely, if $L/K$ is cyclic and 8.1 (a)
holds for $L/K$, then so does 8.1 (b). Proved from the two parts of Theorem 8.1, which the library proves (module
docstring). -/
@[kb "milne2020cft" "Ch. VII, Lemma 8.5, p. 222"]
theorem lemma8_5 (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L] [NumberField L]
    [IsAbelianGalois K L] :
    ((∀ y : groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2,
        sumLocalInv K (brLocalization K (relBrInfl K L L.val y)) = 0) →
      IdeleGroup.principalSubgroup (𝓞 K) K ≤ (idelicArtinTauCeti L (K := K)).ker) ∧
    (IsCyclic Gal(L/K) →
      IdeleGroup.principalSubgroup (𝓞 K) K ≤ (idelicArtinTauCeti L (K := K)).ker →
      ∀ y : groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2,
        sumLocalInv K (brLocalization K (relBrInfl K L L.val y)) = 0) := by
  refine ⟨fun _ => ?_, fun _ _ y => sumLocalInv_brLocalization_eq_zero K _⟩
  rintro _ ⟨a, rfl⟩
  exact idelicArtinTauCeti_principal L a

/-- **Lemma 8.6** (Milne, *CFT*, VII, Lemma 8.6, p. 223): if Theorem 8.1 (b) holds for the cyclic cyclotomic
extensions of $K$ (cyclic Galois subextensions $L$ of $K(\mu_m)/K$, $m \ne 0$), then it holds for every finite Galois
extension of $K$. Proved from Tau Ceti's sum formula (module docstring). -/
@[kb "milne2020cft" "Ch. VII, Lemma 8.6, p. 223"]
theorem lemma8_6
    (_h : ∀ (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L] [IsGalois K L]
      [IsCyclic Gal(L/K)] (m : ℕ), m ≠ 0 →
      L ≤ IntermediateField.adjoin K {ζ : SeparableClosure K | ζ ^ m = 1} →
      ∀ y : groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2,
        sumLocalInv K (brLocalization K (relBrInfl K L L.val y)) = 0)
    (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L] [IsGalois K L]
    (y : groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 2) :
    sumLocalInv K (brLocalization K (relBrInfl K L L.val y)) = 0 :=
  sumLocalInv_brLocalization_eq_zero K _

end NumberFieldKB.MilneCFT.Ch7
