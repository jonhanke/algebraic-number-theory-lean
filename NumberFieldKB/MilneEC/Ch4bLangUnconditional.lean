import NumberFieldKB.MilneEC.Ch4bLangDivisible
import NumberFieldKB.MilneEC.Ch4Lemma21

/-!
# Milne, Elliptic Curves, Chapter IV §9: Lang's theorem, unconditional

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Proposition 9.2 and
Corollary 9.3, pdf p. 157.

`Ch4bLangDivisible.lean` derives Lang's theorem for $E$ (`LangFrobenius`) from Lemma IV.2.1 (`Lemma2_1`), and
`Ch4Lemma21.lean` proves Lemma IV.2.1 in every characteristic (`lemma2_1`). This file combines the two.

## Proved
* `langFrobenius`: $P \mapsto \varphi(P) - P$ is surjective on $E(\mathbb F)$ for an elliptic curve over a finite
  field.
* `prop_9_2_unconditional`: Proposition 9.2, $H^1(k, E) = 0$ (continuous cohomology of the absolute Galois group).
* `cor_9_3_unconditional`: Corollary 9.3, every principal homogeneous space has a rational point.
-/

open WeierstrassCurve

namespace NumberFieldKB.MilneEC

variable (k : Type) [Field k] [Fintype k] (W : WeierstrassCurve k)

/-- **Lang's theorem for an elliptic curve over a finite field** (Milne's input to Proposition 9.2, pdf p. 157):
$P \mapsto \varphi(P) - P$ is surjective on $E(\mathbb F)$. Unconditional: `langFrobenius_of_lemma2_1` with
`lemma2_1`. -/
@[kb "milne2006ec" "Ch. IV, proof of Proposition 9.2, pdf p. 157 (Lang's theorem)"]
theorem langFrobenius [W.IsElliptic] : LangFrobenius k W :=
  langFrobenius_of_lemma2_1 k W lemma2_1

/-- **Proposition 9.2** (Lang; Milne, *Elliptic Curves*, pdf p. 157), unconditional: for an elliptic curve $E$ over a
finite field $k$, $H^1(k, E) = 0$. -/
@[kb "milne2006ec" "Ch. IV, Proposition 9.2, pdf p. 157"]
theorem prop_9_2_unconditional [W.IsElliptic]
    (c : ContH1 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (W.toAffine.baseChange (AlgebraicClosure k)).Point) :
    c = 0 :=
  prop_9_2_of_lemma2_1 k W lemma2_1 c

/-- **Corollary 9.3** (pdf p. 157), Galois-set form, unconditional: every principal homogeneous space of $E$ over a
finite field has a rational point. -/
@[kb "milne2006ec" "Ch. IV, Corollary 9.3, pdf p. 157"]
theorem cor_9_3_unconditional [W.IsElliptic]
    (T : GaloisTorsor (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (W.toAffine.baseChange (AlgebraicClosure k)).Point) :
    T.rationalPoints.Nonempty :=
  cor_9_3_of_lemma2_1 k W lemma2_1 T

end NumberFieldKB.MilneEC
