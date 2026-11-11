import NumberFieldKB.MilneANT.Ch7Prop764
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Milne, Proposition 7.64: reduction of the named statement to its degree-zero case

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Proposition 7.64, p. 133; bib key `milne2020ant`.

`prop_7_64_pos` proves Milne's Proposition 7.64 for every degree $n \ge 1$. The named statement `Prop7_64` quantifies
over every `n : ℕ` in its first version (`Prop764Original`), and `Module.finrank K E = 0` holds exactly for the subfields $E$ of
$K^{\mathrm{al}}$ of infinite degree, which Milne does not mean. **`prop764Original_iff_zero`**: the first version holds
iff the degree-zero set is finite (`Prop764ZeroCase`), which is false (`Ch7Prop764Erratum.lean`) (for $E \supseteq K(\pi^{1/\ell^\infty})$ the maximal ideal $\mathfrak P$ of the integral closure
satisfies $\mathfrak P = \mathfrak P^2$, so the length defining `ramIdxMilne` is infinite and `ramIdxMilne` is $0$).
-/

open IsLocalRing

universe u v

namespace NumberFieldKB.MilneANT

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]

/-- The degree-zero case of the named statement `Prop7_64`: finitely many subfields of $K^{\mathrm{al}}$ of infinite
degree over $K$ (`finrank = 0`) are "totally ramified" in the sense `ramIdxMilne = finrank`. Not Milne's statement
(he speaks of extensions of degree $n$); recorded to isolate what `Prop7_64` asks beyond `prop_7_64_pos`. -/
def Prop764ZeroCase : Prop :=
  {E : IntermediateField K (AlgebraicClosure K) | Module.finrank K E = 0 ∧ IsTotallyRamifiedMilne A K E}.Finite

/-- The first version of the named statement `Prop7_64` (before the erratum of 2026-11-05): finiteness for every
`n : ℕ`, including `n = 0`. False (`not_prop764Original`, `Ch7Prop764Erratum.lean`). -/
def Prop764Original [CharZero K] [Finite (ResidueField A)] : Prop :=
  ∀ n : ℕ,
    {E : IntermediateField K (AlgebraicClosure K) | Module.finrank K E = n ∧ IsTotallyRamifiedMilne A K E}.Finite

/-- The first version of Proposition 7.64 is equivalent to its degree-zero case: every degree $n \ge 1$ is proved
(`prop_7_64_pos`). -/
theorem prop764Original_iff_zero [CharZero K] [Finite (ResidueField A)] :
    Prop764Original A K ↔ Prop764ZeroCase A K := by
  constructor
  · intro h
    exact h 0
  · intro h0 n
    rcases n with _ | d
    · exact h0
    · exact prop_7_64_pos A K d

/-- **Proposition 7.64** (proved, unconditionally): for $K$ of characteristic zero with finite residue field and
every $n \ge 1$, finitely many subfields of $K^{\mathrm{al}}$ of degree $n$ are totally ramified over $K$. -/
@[kb "milne2020ant" "v3.08, Prop. 7.64, p. 133"]
theorem prop_7_64 [CharZero K] [Finite (ResidueField A)] : Prop7_64 A K where
  finite n hn := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact prop_7_64_pos A K d

end NumberFieldKB.MilneANT
