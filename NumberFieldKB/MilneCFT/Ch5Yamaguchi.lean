import NumberFieldKB.MilneCFT.Ch5Complements
import NumberFieldKB.YamaguchiPort.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldExists
import NumberFieldKB.YamaguchiPort.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldDegree
import NumberFieldKB.YamaguchiPort.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldPrincipalization
import NumberFieldKB.YamaguchiPort.GaloisCohomology.GroupTheory.Transfer.Witt

/-!
# Theorem 3.19 and Remark 3.20 from Yamaguchi's library (Milne, *CFT*, V, pp. 163)

Yamaguchi's class field theory library proves, for every number field $K$ (in `Type`), that there is a "small Hilbert
class field" $E$ (a finite abelian extension of $K$ inside `SeparableClosure K`, unramified at every place and
containing every other such extension; `ClassFieldTheory.exists_smallHilbertClassField`), that $[E:K] = h_K$
(`ClassFieldTheory.smallHilbertClassField_degree_eq_classNumber`) and that every ideal of $\mathcal O_K$ becomes
principal in $\mathcal O_E$ (`ClassFieldTheory.ideals_becomePrincipalInSmallHilbertClassField`, the principal ideal
theorem). All three are ported under `NumberFieldKB/YamaguchiPort/` from Yamaguchi main `fbd320cd` (Apache 2.0). The
field $E$ is a number field with an algebra over $K$ by Yamaguchi's instances on `FiniteAbelianExtension K`, so it is
directly a witness of the named statement `Remark3_20` (with degree equal to, hence dividing, $h_K$).

Theorem 3.19 (Furtwängler 1930, Witt 1954; the group-theoretic half of the principal ideal theorem) is Yamaguchi's
`GroupTheory.Transfer.Witt.commutatorTransfer_eq_one_of_finite_abelianization` (ported, a 3-file closure): for a finitely
generated group $G$ whose commutator subgroup has finite index, the transfer $G^{ab}\to (G')^{ab}$ is trivial. A finite
group satisfies both hypotheses.
-/

namespace NumberFieldKB.MilneCFT

variable (K : Type) [Field K] [NumberField K]

/-- **Remark 3.20, proved** (Milne, *CFT*, V, Remark 3.20, p. 163): there is a finite extension $L$ of $K$ of degree
dividing the class number in which every ideal of $K$ becomes principal; $L$ is Yamaguchi's small Hilbert class field
(ported), of degree exactly $h_K$. -/
@[kb "milne2020cft" "Ch. V, Remark 3.20"]
theorem remark3_20 : Remark3_20 K := by
  obtain ⟨E, hE⟩ := ClassFieldTheory.exists_smallHilbertClassField K
  refine ⟨⟨E, inferInstance, inferInstance, inferInstance, ?_,
    ClassFieldTheory.ideals_becomePrincipalInSmallHilbertClassField K E hE⟩⟩
  exact dvd_of_eq (ClassFieldTheory.smallHilbertClassField_degree_eq_classNumber K E hE)

/-- **Theorem 3.19, proved** (Milne, *CFT*, V, Theorem 3.19, p. 163; Furtwängler 1930, Witt 1954): for a finite group
$G$ with commutator subgroup $H$, the transfer $V : G \to H^{ab}$ is trivial. From Yamaguchi's
`GroupTheory.Transfer.Witt.commutatorTransfer_eq_one_of_finite_abelianization` (ported), which assumes only that $G$ is
finitely generated and $H$ has finite index. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.19"]
theorem theorem3_19 : Theorem3_19 := by
  refine ⟨fun G _ _ g => ?_⟩
  have h := congrArg (fun f => f (Abelianization.of g))
    (GroupTheory.Transfer.Witt.commutatorTransfer_eq_one_of_finite_abelianization (G := G))
  simpa using h

end NumberFieldKB.MilneCFT
