import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import QuadFormsKB.Citation

/-!
# Milne, Elliptic Curves, Chapter IV §3: local preliminaries

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Section 3, "Preliminaries"
(pdf pp. 119–120): reduction of points modulo $p$, unramified extensions of $\mathbb{Q}_p$, Lemmas 3.2, 3.3, 3.5 and
Remark 3.4.  Locators give the pdf page of the text `ectext6` (printed page = pdf page − 8).

Conventions.
* An elliptic curve over $\mathbb{Q}_p$ with good reduction is given by a Weierstrass equation `W₀` with coefficients in
  $\mathbb{Z}_p$ whose discriminant is a unit (Milne, Chapter II §4: a minimal equation whose reduction is
  nonsingular).  Its points over $\mathbb{Q}_p$ are those of `W₀.baseChange ℚ_[p]`, and its reduction is
  `W₀.map PadicInt.toZMod` over $\mathbb{F}_p$.
* The reduction $P \mapsto \bar P$ is recorded as the relation `ReducesTo P P'` ("$\bar P = P'$"): $O \mapsto O$;
  $(x, y) \mapsto (\bar x, \bar y)$ if $x \in \mathbb{Z}_p$ (then $y \in \mathbb{Z}_p$); $(x, y) \mapsto O$ otherwise.
* A finite extension $K$ of $\mathbb{Q}_p$ is given with compatible algebra structures over $\mathbb{Z}_p$ and
  $\mathbb{Q}_p$; $\mathcal{O}_K$ is the integral closure of $\mathbb{Z}_p$ in $K$.
-/

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped Classical

namespace NumberFieldKB.MilneEC

variable (p : ℕ) [Fact p.Prime]

/-- Milne (pdf p. 119): a finite extension $K$ of $\mathbb{Q}_p$ is **unramified** if the ramification index is 1,
i.e. the maximal ideal of $\mathcal{O}_K$ is $(p)$. -/
@[kb "milne2006ec" "Ch. IV, §3, definition of an unramified extension of Q_p, pdf p. 119"]
def IsUnramifiedOverQp (K : Type) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] ℚ_[p] K] : Prop :=
  ∀ P : Ideal (integralClosure ℤ_[p] K), P.IsMaximal → P = Ideal.span {(p : integralClosure ℤ_[p] K)}

/-- **Lemma 3.3** (pdf p. 119), a named statement (Milne cites ANT 7.41).  For every finite extension $k$ of
$\mathbb{F}_p$ there is an unramified extension $K$ of $\mathbb{Q}_p$ of degree $[k : \mathbb{F}_p]$ with
$\mathcal{O}_K/p\mathcal{O}_K \cong k$. -/
@[kb "milne2006ec" "Ch. IV, Lemma 3.3, pdf p. 119"]
structure Lemma3_3 : Prop where
  exists_unramified : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [Algebra (ZMod p) k],
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[p] K) (_ : Algebra ℤ_[p] K) (_ : IsScalarTower ℤ_[p] ℚ_[p] K),
      FiniteDimensional ℚ_[p] K ∧ IsUnramifiedOverQp p K ∧
        Module.finrank ℚ_[p] K = Module.finrank (ZMod p) k ∧
        Nonempty ((integralClosure ℤ_[p] K) ⧸ Ideal.span {(p : integralClosure ℤ_[p] K)} ≃+* k)

/-- **Remark 3.4** (pdf p. 119), a named statement.  If $K$ is a finite unramified extension of $\mathbb{Q}_p$ whose
residue field $\mathcal{O}_K/p\mathcal{O}_K$ has $q$ elements, then Hensel's lemma holds for $\mathcal{O}_K$, and $K$ is
the splitting field of $X^q - X$ over $\mathbb{Q}_p$. -/
@[kb "milne2006ec" "Ch. IV, Remark 3.4, pdf p. 119"]
structure Remark3_4 : Prop where
  isSplittingField : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K] (q : ℕ),
    IsUnramifiedOverQp p K →
      Nat.card ((integralClosure ℤ_[p] K) ⧸ Ideal.span {(p : integralClosure ℤ_[p] K)}) = q →
        IsSplittingField ℚ_[p] K (X ^ q - X : ℚ_[p][X])

section Reduction

variable {p} (W₀ : WeierstrassCurve ℤ_[p])

/-- The reduction relation $\bar P = P'$ for a point $P \in E(\mathbb{Q}_p)$ and $P' \in \bar E(\mathbb{F}_p)$
(Milne, Chapter II §4; used in Lemma 3.2, pdf p. 119). -/
@[kb "milne2006ec" "Ch. IV, Lemma 3.2, the reduction map E(Q_p) → E(F_p), pdf p. 119"]
def ReducesTo (P : (W₀.baseChange ℚ_[p]).toAffine.Point)
    (P' : (W₀.map PadicInt.toZMod).toAffine.Point) : Prop :=
  (P = 0 ∧ P' = 0) ∨
    (∃ (x y : ℚ_[p]) (h : (W₀.baseChange ℚ_[p]).toAffine.Nonsingular x y), P = .some x y h ∧ 1 < ‖x‖ ∧ P' = 0) ∨
    ∃ (x y : ℤ_[p]) (h : (W₀.baseChange ℚ_[p]).toAffine.Nonsingular (x : ℚ_[p]) (y : ℚ_[p]))
      (h' : (W₀.map PadicInt.toZMod).toAffine.Nonsingular (PadicInt.toZMod x) (PadicInt.toZMod y)),
      P = .some (x : ℚ_[p]) (y : ℚ_[p]) h ∧ P' = .some _ _ h'

end Reduction

/-- **Lemma 3.2** (pdf p. 119), a named statement (Milne's proof uses Chapter II, 4.2: multiplication by $n$ is an
isomorphism on $E^1(\mathbb{Q}_p)$ for $p \nmid n$).  Let $E$ be an elliptic curve over $\mathbb{Q}_p$ with good
reduction and $n$ an integer not divisible by $p$.  A point $P \in E(\mathbb{Q}_p)$ is of the form $nQ$ with
$Q \in E(\mathbb{Q}_p)$ if and only if its reduction $\bar P$ is of the form $n\bar Q$ with $\bar Q \in E(\mathbb{F}_p)$. -/
@[kb "milne2006ec" "Ch. IV, Lemma 3.2, pdf p. 119"]
structure Lemma3_2 : Prop where
  mem_multiples_iff : ∀ (p : ℕ) [Fact p.Prime] (W₀ : WeierstrassCurve ℤ_[p]), IsUnit W₀.Δ →
    ∀ (n : ℤ), ¬ (p : ℤ) ∣ n → ∀ (P : (W₀.baseChange ℚ_[p]).toAffine.Point)
      (P' : (W₀.map PadicInt.toZMod).toAffine.Point), ReducesTo W₀ P P' →
        ((∃ Q, n • Q = P) ↔ ∃ Q', n • Q' = P')

/-- **Lemma 3.5** (pdf p. 120), a named statement (Milne derives it from Lemma 3.2 over unramified extensions and
Lemma 3.3).  Let $E$ be an elliptic curve over $\mathbb{Q}_p$ with good reduction and $n$ an integer not divisible
by $p$.  For every $P \in E(\mathbb{Q}_p)$ there is a finite unramified extension $K$ of $\mathbb{Q}_p$ with
$P \in nE(K)$. -/
@[kb "milne2006ec" "Ch. IV, Lemma 3.5, pdf p. 120"]
structure Lemma3_5 : Prop where
  exists_unramified : ∀ (p : ℕ) [Fact p.Prime] (W₀ : WeierstrassCurve ℤ_[p]), IsUnit W₀.Δ →
    ∀ (n : ℤ), ¬ (p : ℤ) ∣ n → ∀ P : (W₀.baseChange ℚ_[p]).toAffine.Point,
      ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[p] K) (_ : Algebra ℤ_[p] K) (_ : IsScalarTower ℤ_[p] ℚ_[p] K),
        FiniteDimensional ℚ_[p] K ∧ IsUnramifiedOverQp p K ∧
          ∃ Q : ((W₀.baseChange ℚ_[p]).toAffine⁄K).Point,
            n • Q = Point.map (W' := (W₀.baseChange ℚ_[p]).toAffine) (Algebra.ofId ℚ_[p] K) P

end NumberFieldKB.MilneEC
