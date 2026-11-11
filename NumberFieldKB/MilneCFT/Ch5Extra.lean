import NumberFieldKB.MilneCFT.Ch5RayClassOrder
import NumberFieldKB.MilneCFT.Ch5Ideles
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Remaining claims of Milne, *Class Field Theory*, Chapter V (named statements)

* **Example 1.8(b), the table** (named `Example1_8b_table`): class numbers, fundamental units and narrow class
  numbers of $\mathbb Q(\sqrt d)$, $d = 2, 3, 5, 6$;
* **Aside 4.5, the nontrivial theorem** (named `Aside4_5_finiteIndexOpen`): for the topology induced on $K^\times$ by the
  finite idèles, every subgroup of finite index of $U_K$ is open (Chevalley).
-/

open NumberField IsDedekindDomain

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

/-- **Example 1.8(b), the table** (named statement; Milne, *CFT*, V, Example 1.8(b), p. 151): for $d = 2, 3, 5, 6$ the
real quadratic field $\mathbb Q(\sqrt d)$ has class number $1$, fundamental unit $\varepsilon = 1 + \sqrt 2$, $2 + \sqrt 3$,
$(1 + \sqrt 5)/2$, $5 + 2\sqrt 6$ (every unit is $\pm\varepsilon^k$) of norm $-1, 1, -1, 1$; hence $\mathbb Q(\sqrt 3)$
and $\mathbb Q(\sqrt 6)$ have narrow class number $2$ and $\mathbb Q(\sqrt 2)$, $\mathbb Q(\sqrt 5)$ narrow class number
$1$. Stated for a quadratic field $K$ with $s \in K$, $s^2 = d$; $\varepsilon = a + b s$ with $(a, b)$ as listed. -/
@[kb "milne2020cft" "Ch. V, Example 1.8(b) (the table for d = 2, 3, 5, 6; input)"]
structure Example1_8b_table : Prop where
  table : ∀ (K : Type) [Field K] [NumberField K] (d : ℤ) (s : K), Module.finrank ℚ K = 2 → s ^ 2 = d →
    ∀ (a b : ℚ) (n hn : ℤ),
      (d, a, b, n, hn) ∈ ({(2, 1, 1, -1, 1), (3, 2, 1, 1, 2), (5, 1/2, 1/2, -1, 1), (6, 5, 2, 1, 2)} :
        Set (ℤ × ℚ × ℚ × ℤ × ℤ)) →
      classNumber K = 1 ∧
      (∃ ε : (𝓞 K)ˣ, ((ε : 𝓞 K) : K) = a + b * s ∧ Algebra.norm ℚ ((ε : 𝓞 K) : K) = n ∧
        ∀ u : (𝓞 K)ˣ, ∃ k : ℤ, u = ε ^ k ∨ u = -ε ^ k) ∧
      (Nat.card (RayClassGroup (narrowModulus K)) : ℤ) = hn

variable (K : Type) [Field K] [NumberField K] in
/-- **Aside 4.5, the nontrivial theorem** (named statement; Milne, *CFT*, V, Aside 4.5, p. 171, "nontrivial theorem";
Chevalley): for the topology induced on $K^\times$ by the diagonal embedding into the finite idèles, every subgroup of
$U_K$ of finite index is open (so the subgroups of finite index of $U_K$ form a fundamental system of neighbourhoods of
$1$, with `aside_4_5_topology`). -/
@[kb "milne2020cft" "Ch. V, Aside 4.5 (finite index subgroups of U_K are open; input)"]
structure Aside4_5_finiteIndexOpen : Prop where
  isOpen : letI : TopologicalSpace Kˣ := TopologicalSpace.induced (finiteDiag K) inferInstance
    ∀ H : Subgroup Kˣ, H ≤ unitsK K → (H.subgroupOf (unitsK K)).FiniteIndex → IsOpen (H : Set Kˣ)

end NumberFieldKB.MilneCFT
