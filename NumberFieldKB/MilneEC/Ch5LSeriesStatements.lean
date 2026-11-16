import NumberFieldKB.MilneEC.Ch5LSeries
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Milne, *Elliptic Curves*, Chapter V §4: the named statements

The named statements (cited results, not proved in this library) of Milne, *Elliptic Curves*, Chapter V, §4, on the
definitions of `NumberFieldKB.MilneEC.Ch5LSeries`: Theorem 4.1 (`Thm4_1`), Corollary 4.2 (`Cor4_2`, with
`Cor4_2.isogenous_symm` proved from it) and Ramanujan's conjecture (a), proved by Deligne (`RamanujanDeligne`).
They are kept apart from the definitions and theorems of §4, which are used without them.
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Matrix.SpecialLinearGroup
open scoped MatrixGroups Real Manifold Pointwise

namespace NumberFieldKB.MilneEC.V

/-- **Theorem 4.1** (pdf p. 203), a named statement: isogenous elliptic curves over $\mathbb Q$ have the same
number of points modulo every prime of good reduction; conversely (Tate's conjecture, proved by Faltings 1983),
if $N_p(E) = N_p(E')$ for all good primes outside a finite set, then $E$ and $E'$ are isogenous. ("Sufficiently
many good $p$" is read as "all but finitely many"; Faltings' effective bound is the paragraph after the proof.) -/
@[kb "milne2006ec" "Ch. V, Theorem 4.1, pdf p. 203"]
structure Thm4_1 : Prop where
  numPoints_eq : ∀ (E E' : WeierstrassCurve ℚ) [E.IsElliptic] [E'.IsElliptic], Isogenous E E' →
    ∀ (p : ℕ) [Fact p.Prime], HasGoodReductionAt E p → HasGoodReductionAt E' p → numPoints E p = numPoints E' p
  isogenous_of_numPoints_eq : ∀ (E E' : WeierstrassCurve ℚ) [E.IsElliptic] [E'.IsElliptic],
    (∃ S : Finset ℕ, ∀ (p : ℕ) [Fact p.Prime], p ∉ S → HasGoodReductionAt E p → HasGoodReductionAt E' p →
      numPoints E p = numPoints E' p) → Isogenous E E'

/-- **Corollary 4.2** (pdf p. 204), a named statement: two elliptic curves over $\mathbb Q$ are isogenous if and
only if they have the same $L$-series (from Theorem 4.1 and the fact, from Néron models, that isogenous curves have
the same reduction type at every prime). -/
@[kb "milne2006ec" "Ch. V, Corollary 4.2, pdf p. 204"]
structure Cor4_2 : Prop where
  iff : ∀ (E E' : WeierstrassCurve ℚ) [E.IsElliptic] [E'.IsElliptic],
    Isogenous E E' ↔ E.LFunction = E'.LFunction

/-- Under Corollary 4.2, isogeny is an equivalence relation on elliptic curves over $\mathbb Q$ (pdf p. 203:
"isogeny is an equivalence relation"; symmetry needs the dual isogeny, which Corollary 4.2 replaces). -/
theorem Cor4_2.isogenous_symm (h : Cor4_2) {E E' : WeierstrassCurve ℚ} [E.IsElliptic] [E'.IsElliptic]
    (hE : Isogenous E E') : Isogenous E' E :=
  (h.iff E' E).2 ((h.iff E E').1 hE).symm

/-- Ramanujan's conjecture (a) (pdf p. 206), proved by Deligne: $|\tau(p)| \le 2p^{11/2}$ for primes $p$. A named
statement. -/
@[kb "milne2006ec" "Ch. V, §4, Ramanujan's conjecture (a), proved by Deligne (running text), pdf p. 206"]
structure RamanujanDeligne : Prop where
  bound : ∀ p : ℕ, p.Prime → ‖tau p‖ ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2)

end NumberFieldKB.MilneEC.V
