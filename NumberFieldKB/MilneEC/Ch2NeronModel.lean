import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import QuadFormsKB.Citation
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Milne, Elliptic Curves, Chapter II §6: the complete Néron model

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter II, Section 6 ("Néron models"),
pdf pp. 77, 82.

## The Weierstrass minimal model (pdf p. 77)
Milne's Weierstrass minimal model of $E/\mathbb Q_p$ is the curve over $\mathbb Z_p$ defined by a minimal Weierstrass
equation.  Minimal equations are Mathlib's `WeierstrassCurve.IsMinimal`; the curve over $\mathbb Z_p$ as a scheme is
Tau Ceti's `WeierstrassCurve.projModel` (`TauCeti/AlgebraicGeometry/EllipticCurve/Scheme/ProjModel.lean`, the `Proj` of
the graded coordinate ring $R[X, Y, Z]/(W)$).  Neither is redefined here (Tau Ceti cannot be imported on this
toolchain).

## The complete Néron model (pdf p. 82)
Milne: given $E/\mathbb Q_p$, the complete Néron (minimal) model is a scheme $\mathcal E$ over $\mathbb Z_p$ with
(a) $\mathcal E$ regular (all local rings regular local rings), (b) generic fibre $E$, (c) $\mathcal E$ proper over
$\mathbb Z_p$, (d) minimal: every regular map $\mathcal E \to \mathcal E'$ over $\mathbb Z_p$ to a scheme with
(a)–(c) that is an isomorphism on generic fibres is an isomorphism.

`IsCompleteNeronModel` states (a)–(d) with Mathlib's schemes, `IsRegularLocalRing` and `IsProper`.  For (b), $E$ is
the regular proper curve over $\mathbb Q_p$ containing the affine Weierstrass curve
$\operatorname{Spec} \mathbb Q_p[x, y]/(W)$ (Mathlib's `WeierstrassCurve.Affine.CoordinateRing`) as a dense open
subscheme over $\mathbb Q_p$ (`IsGenericFibreOf`): a regular proper curve over a field is determined by any dense open
subscheme (it is the unique regular proper model of its function field), so this says that the generic fibre is the
projective curve $E$.  Milne's existence theorem (Néron) and the comparison with the Weierstrass model are not
formalized.
-/

open CategoryTheory AlgebraicGeometry Limits

namespace NumberFieldKB.MilneEC.NeronModel

variable (p : ℕ) [Fact p.Prime]

/-- The morphism $\operatorname{Spec}\mathbb Q_p \to \operatorname{Spec}\mathbb Z_p$ (the generic point). -/
noncomputable def toGeneric : Spec (CommRingCat.of ℚ_[p]) ⟶ Spec (CommRingCat.of ℤ_[p]) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ_[p] ℚ_[p]))

/-- The generic fibre $X \times_{\mathbb Z_p} \mathbb Q_p$ of a scheme over $\mathbb Z_p$. -/
noncomputable abbrev genericFibre {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ_[p])) : Scheme :=
  pullback f (toGeneric p)

/-- The structure morphism of the generic fibre to $\operatorname{Spec}\mathbb Q_p$. -/
noncomputable abbrev genericFibreHom {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ_[p])) :
    genericFibre p f ⟶ Spec (CommRingCat.of ℚ_[p]) :=
  pullback.snd f (toGeneric p)

/-- The affine Weierstrass curve $\operatorname{Spec}\mathbb Q_p[x, y]/(W)$ over $\mathbb Q_p$. -/
noncomputable def affineModelHom (E : WeierstrassCurve ℚ_[p]) :
    Spec (CommRingCat.of E.toAffine.CoordinateRing) ⟶ Spec (CommRingCat.of ℚ_[p]) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ_[p] E.toAffine.CoordinateRing))

/-- A scheme is **regular** if all its local rings are regular local rings (Milne's (a), pdf p. 82). -/
def IsRegularScheme (X : Scheme) : Prop := ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- **The generic fibre of $f$ is the elliptic curve $E$** (Milne's (b), pdf p. 82): it is a regular proper scheme
over $\mathbb Q_p$ containing the affine Weierstrass curve of $E$ as a dense open subscheme over $\mathbb Q_p$. -/
def IsGenericFibreOf (E : WeierstrassCurve ℚ_[p]) {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ_[p])) : Prop :=
  IsRegularScheme (genericFibre p f) ∧ IsProper (genericFibreHom p f) ∧
    ∃ ι : Spec (CommRingCat.of E.toAffine.CoordinateRing) ⟶ genericFibre p f,
      IsOpenImmersion ι ∧ ι ≫ genericFibreHom p f = affineModelHom p E ∧ DenseRange ι.base

/-- **The complete Néron (minimal) model** of an elliptic curve $E$ over $\mathbb Q_p$ (Milne pdf p. 82): a scheme
$X \to \operatorname{Spec}\mathbb Z_p$ that is (a) regular, (b) has generic fibre $E$, (c) is proper, and (d) is
minimal: a morphism over $\mathbb Z_p$ to another such scheme that is an isomorphism on generic fibres is an
isomorphism. -/
@[kb "milne2006ec" "Ch. II, §6, the complete Néron (minimal) model (definition in prose), pdf p. 82"]
structure IsCompleteNeronModel (E : WeierstrassCurve ℚ_[p]) [E.IsElliptic] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of ℤ_[p])) : Prop where
  regular : IsRegularScheme X
  generic : IsGenericFibreOf p E f
  proper : IsProper f
  minimal : ∀ (X' : Scheme) (f' : X' ⟶ Spec (CommRingCat.of ℤ_[p])), IsRegularScheme X' →
    IsGenericFibreOf p E f' → IsProper f' → ∀ (g : X ⟶ X') (hg : g ≫ f' = f),
      IsIso (pullback.map f (toGeneric p) f' (toGeneric p) g (𝟙 _) (𝟙 _) (by simp [hg]) (by simp)) →
        IsIso g

end NumberFieldKB.MilneEC.NeronModel
