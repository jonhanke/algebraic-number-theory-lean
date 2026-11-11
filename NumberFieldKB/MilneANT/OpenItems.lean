import NumberFieldKB.MilneANT.Ch7Artin
import NumberFieldKB.MilneANT.Ch7OstrowskiFinite
import NumberFieldKB.MilneANT.Ch7OstrowskiComplete
import NumberFieldKB.MilneANT.Ch7OstrowskiInfinite
import NumberFieldKB.MilneANT.Ch7Ostrowski
import NumberFieldKB.MilneANT.Ch7NormFormula
import NumberFieldKB.MilneANT.Ch7LocalFieldsPadic
import NumberFieldKB.MilneANT.Ch7Thm758b
import NumberFieldKB.MilneANT.Ch7Thm758aFixed
import NumberFieldKB.MilneANT.Ch8CompleteUnique
import NumberFieldKB.MilneANT.Ch8CompleteExists
import NumberFieldKB.MilneANT.Ch8TensorFactor
import NumberFieldKB.MilneANT.Ch8Prop81
import NumberFieldKB.MilneANT.Ch8Prop810
import NumberFieldKB.MilneANT.Ch8LocalDegreeLower
import NumberFieldKB.MilneANT.Ch8Remark83
import NumberFieldKB.MilneANT.Ch8LocalDegree
import NumberFieldKB.MilneANT.Ch7Remark753
import NumberFieldKB.MilneANT.Ch7Example754
import NumberFieldKB.MilneANT.Ch7HenselExt
import NumberFieldKB.MilneANT.Ch7ResidueSub
import NumberFieldKB.MilneANT.Ch7Prop750
import NumberFieldKB.MilneANT.Ch7Cor751
import NumberFieldKB.MilneANT.Ch7NormOfDVR
import NumberFieldKB.MilneANT.Ch7Prop764
import Mathlib.Tactic.MinImports

/-!
# Milne, *Algebraic Number Theory*: the open items now proved

Aggregator for the files that prove results previously recorded as named
statements: Theorem 7.14 and Lemma 7.16 (Ostrowski), Remark 7.49(a) and (b), Theorem 7.58 (the fixed field of $G_0$, and (b)) and Corollary 7.59, Theorem 7.38 for every complete field,
Propositions 8.1 and 8.2, Corollary 8.4, Proposition 8.10, Remark 8.3 with the local degree formula $[L_w:K_{\mathfrak p}]=ef$, Remark 7.53 (finite unramified extensions of $K$ versus finite separable extensions of $k$), Example 7.54 (unramified extensions of a local field: existence, uniqueness, Frobenius), Proposition 7.50 (finite unramified subextensions of an algebraic extension versus finite residue
extensions) with Hensel's lemma in the valuation ring of an algebraic extension, Corollaries 7.51 and 7.52 (maximal unramified extension; roots of unity of order prime to $p$;
the residue field of $K^{\mathrm{al}}$ is algebraically closed), Proposition 7.64 for every degree $n\ge1$ (`prop_7_64_pos`).
Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), bib key `milne2020ant`.
-/
