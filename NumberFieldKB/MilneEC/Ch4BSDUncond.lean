import NumberFieldKB.MilneEC.Ch4BSDComparisons
import NumberFieldKB.MilneEC.Ch4Thm31

/-!
# Conjecture IV.10.5 against `StrongBSD` over $\mathbb Q$: Mordell's theorem no longer an instance argument

Milne, *Elliptic Curves* (`milne2006ec`), Chapter IV, Conjecture 10.5, pdf p. 173.
`Ch4BSDComparisons.lean` proves the equivalence of Conjecture 10.5 with Formal Conjectures' `StrongBSD` for a minimal
equation over $\mathbb Q$, with only `ShaComparison` assumed, but with finite generation of $E(\mathbb Q)$ as an
instance argument `[Module.Finite ℤ E.toAffine.Point]`. Here that argument is discharged by `mordell_weil_rat`
(`Ch4Thm31.lean`). Only `ShaComparison` remains assumed.
-/

open WeierstrassCurve

namespace NumberFieldKB.MilneEC

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **Conjecture 10.5 (corrected normalization) is Formal Conjectures' `StrongBSD` over $\mathbb Q$** for a minimal
equation, with finite generation of $E(\mathbb Q)$ proved (`mordell_weil_rat`); only `ShaComparison` is assumed. -/
theorem conjecture10_5Corrected_iff_strongBSD_rat (hSha : ShaComparison) (hmin : IsMinimalOverRat E) :
    haveI := mordell_weil_rat E
    Conjecture10_5Corrected E ↔ FormalConjectures.StrongBSD E.toAffine :=
  haveI := mordell_weil_rat E
  conjecture10_5Corrected_iff_strongBSD_of_sha E hSha hmin

/-- In rank $0$, Conjecture 10.5 as printed is `StrongBSD`, with Mordell's theorem proved. -/
theorem conjecture10_5_iff_strongBSD_of_rank_eq_zero_rat (hSha : ShaComparison) (hmin : IsMinimalOverRat E) :
    haveI := mordell_weil_rat E
    rank E = 0 → (Conjecture10_5 E ↔ FormalConjectures.StrongBSD E.toAffine) :=
  haveI := mordell_weil_rat E
  fun h0 => conjecture10_5_iff_strongBSD_of_rank_eq_zero_of_sha E hSha hmin h0

/-- In positive rank, `StrongBSD` refutes Conjecture 10.5 as printed, with Mordell's theorem proved. -/
theorem not_conjecture10_5_of_strongBSD_rat (hSha : ShaComparison) (hmin : IsMinimalOverRat E) :
    haveI := mordell_weil_rat E
    0 < rank E → FormalConjectures.StrongBSD E.toAffine → ¬ Conjecture10_5 E :=
  haveI := mordell_weil_rat E
  fun hr h => not_conjecture10_5_of_strongBSD_of_sha E hSha hmin hr h

end NumberFieldKB.MilneEC
