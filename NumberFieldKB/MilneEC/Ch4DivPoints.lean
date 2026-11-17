import NumberFieldKB.MilneEC.Ch4ValuedShort
import NumberFieldKB.MilneEC.Ch4LocalBridge
import NumberFieldKB.MilneEC.Ch4Lemma21
import NumberFieldKB.MilneEC.Ch4DivPointsAux2
import NumberFieldKB.TauCetiPort.NumberTheory.RamificationInertia.Unramified

/-!
# Division points of a point of $E(\mathbb Q_p)$ generate an unramified extension

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter IV, Lemma 3.5 and Proposition 3.6 (pdf p. 120),
and the proof of Theorem 3.1 (pdf pp. 121–125), where the field $\mathbb Q(E_n)$ is used to be unramified outside
$2n\Delta$.

**Statement.** Let $E : Y^2 = X^3 + aX + b$ with $a, b \in \mathbb Z_p$ have good reduction (`Valued.Good`:
$2$ and $4a^3 + 27b^2$ units) and let $n$ be prime to $p$.  For $P \in E(\mathbb Q_p)$ there is a finite
unramified extension $K \subseteq \bar{\mathbb Q}_p$ of $\mathbb Q_p$ containing the coordinates of *every*
$Q \in E(\bar{\mathbb Q}_p)$ with $nQ = P$ (`exists_unramified_divPoints_short`).  For $P = O$ this is the
easy direction of the Néron–Ogg–Shafarevich criterion; for general $P$ it is the strong form of Lemma 3.5 used in
Proposition 3.6.

**Proof (different from Milne's).**  Milne lifts from the residue field by Hensel's lemma over an unramified
extension (Lemma 3.3).  Here: let $D$ be the (finite, nonempty: Lemma 2.1) set of such $Q$ and
$K = \mathbb Q_p(D)$, a finite Galois extension.  An element $\sigma$ of the inertia group of $K/\mathbb Q_p$
acts trivially on the residue field, so $\overline{\sigma Q} = \bar Q$; hence $\sigma Q - Q$ lies in the kernel
$E^1(K)$ of reduction and is killed by $n$, so it is $O$ (`Valued.eq_zero_of_zsmul_eq_zero`, injectivity in
Corollary 4.2).  So the inertia group fixes the generators $D$ of $K$ and is trivial, and $K$ is unramified
(`Ideal.isUnramifiedAt_iff_inertia_eq_bot_of_isMaximal`, Tau Ceti port).
-/

namespace NumberFieldKB.MilneEC

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

/-- All $n$-division points over $\bar{\mathbb Q}_p$ of a point of $E(\mathbb Q_p)$ are defined over one finite
unramified extension of $\mathbb Q_p$ (short model with good reduction, $p \nmid n$). -/
theorem exists_unramified_divPoints_short (a b : ℤ_[p]) (h : II.Valued.Good a b) {n : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) (P : ((II.shortZp a b).toAffine⁄ℚ_[p]).Point) :
    ∃ K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]), FiniteDimensional ℚ_[p] K ∧
      IsUnramifiedOverQp p K ∧
      ∀ Q : ((II.shortZp a b).toAffine⁄(AlgebraicClosure ℚ_[p])).Point,
        n • Q = Point.map (W' := (II.shortZp a b).toAffine) (Algebra.ofId ℚ_[p] (AlgebraicClosure ℚ_[p])) P →
          ∃ Q₀ : ((II.shortZp a b).toAffine⁄K).Point,
            Point.map (W' := (II.shortZp a b).toAffine) K.val Q₀ = Q := by
  exact short_main a b h hn P

end NumberFieldKB.MilneEC
