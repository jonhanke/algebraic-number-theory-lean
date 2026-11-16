import NumberFieldKB.MilneEC.Ch4Selmer
import NumberFieldKB.MilneEC.Ch4Local
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Milne, Elliptic Curves, Chapter IV, Proposition 3.6

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Proposition 3.6 (pdf p. 120):
a Selmer class becomes zero over a finite unramified extension of $\mathbb{Q}_p$ for almost all $p$.

Conventions.  The curve is given by a Weierstrass equation `W₀` with integer coefficients; $E = $ `W₀.map ℚ`.  For a
finite extension $K$ of $\mathbb{Q}_p$ inside $\bar{\mathbb{Q}}_p$ (an `IntermediateField`), $H^1(K, E_n)$ is the
cohomology of `K.fixingSubgroup` $\subseteq \operatorname{Gal}(\bar{\mathbb{Q}}_p/\mathbb{Q}_p)$ with coefficients in
$E_n(\bar{\mathbb{Q}}_p)$, and the map from $H^1(\mathbb{Q}, E_n)$ is induced by the localization of 1.9
(`decompHom`, `closureEmb`) followed by restriction.
-/

open CategoryTheory groupCohomology WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace NumberFieldKB.MilneEC

variable (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℚ) (n : ℤ)

/-- The map $E_n(\bar{\mathbb{Q}}) \to E_n(\bar{\mathbb{Q}}_p)$ induced by `closureEmb`, compatible with `decompHom`. -/
noncomputable def localizeTorsionTorsion :
    Rep.res (decompHom ℚ_[p]) (torsionRep W (AlgebraicClosure ℚ) n) ⟶
      Rep.res (AlgEquiv.restrictScalarsHom ℚ) (torsionRep W (AlgebraicClosure ℚ_[p]) n) :=
  Rep.ofHom ⟨(((Point.map (W' := W.toAffine) (closureEmb ℚ_[p])).comp
      (torsionPoints W (AlgebraicClosure ℚ) n).subtype).codRestrict
      (torsionPoints W (AlgebraicClosure ℚ_[p]) n) (fun P => by
        show n • Point.map (W' := W.toAffine) (closureEmb ℚ_[p]) (P : (W.toAffine⁄(AlgebraicClosure ℚ)).Point) = 0
        rw [← map_zsmul, show n • (P : (W.toAffine⁄(AlgebraicClosure ℚ)).Point) = 0 from P.2, map_zero])).toIntLinearMap,
    fun σ => by
    ext P
    exact localize_map ℚ_[p] W σ P.1⟩

/-- The map $H^1(\mathbb{Q}, E_n) \to H^1(K, E_n)$ for a finite extension $K$ of $\mathbb{Q}_p$ in
$\bar{\mathbb{Q}}_p$ (pdf p. 120). -/
noncomputable def resToLocalField (K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) :
    H1 (torsionRep W (AlgebraicClosure ℚ) n) →+
      H1 (Rep.res K.fixingSubgroup.subtype
        (Rep.res (AlgEquiv.restrictScalarsHom ℚ) (torsionRep W (AlgebraicClosure ℚ_[p]) n))) :=
  ((map K.fixingSubgroup.subtype (𝟙 _) 1).hom.toAddMonoidHom).comp
    (map (decompHom ℚ_[p]) (localizeTorsionTorsion p W n) 1).hom.toAddMonoidHom

/-- **Proposition 3.6** (pdf p. 120), a named statement (Milne derives it from the definition of the Selmer group,
Lemma 3.5 and the local Kummer sequence).  Let $E$ be an elliptic curve over $\mathbb{Q}$ given by an equation with
integer coefficients and discriminant $\Delta$, and let $T$ be the set of primes dividing $2n\Delta$.  For every
$\gamma \in S^{(n)}(E/\mathbb{Q})$ and every prime $p \notin T$ there is a finite unramified extension $K$ of
$\mathbb{Q}_p$ such that $\gamma$ maps to zero in $H^1(K, E_n)$. -/
@[kb "milne2006ec" "Ch. IV, Prop. 3.6, pdf p. 120"]
structure Prop3_6 : Prop where
  exists_unramified : ∀ (W₀ : WeierstrassCurve ℤ) [(W₀.map (Int.castRingHom ℚ)).IsElliptic] (n : ℤ),
    n ≠ 0 → ∀ γ ∈ selmerGroup ℚ (W₀.map (Int.castRingHom ℚ)) n, ∀ (p : ℕ) [Fact p.Prime],
      ¬ (p : ℤ) ∣ 2 * n * W₀.Δ →
        ∃ K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]), FiniteDimensional ℚ_[p] K ∧
          IsUnramifiedOverQp p K ∧ resToLocalField p (W₀.map (Int.castRingHom ℚ)) n K γ = 0

end NumberFieldKB.MilneEC
