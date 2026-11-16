import NumberFieldKB.MilneEC.Ch4Cohomology
import NumberFieldKB.MilneEC.Ch4Heights
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-!
# Milne, Elliptic Curves, Chapter IV §§2–3: the Selmer and Tate–Shafarevich groups

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Section 2 ("The Selmer and
Tate-Shafarevich groups") and Section 3 ("The finiteness of the Selmer group"), with the localization maps of
1.9.  Locators give the pdf page of the text `ectext6` (printed page = pdf page − 8).

Conventions and deviations.
* For a field $K$, $\bar K$ is Mathlib's `AlgebraicClosure K` and $G_K = \operatorname{Aut}(\bar K/K)$ with its Krull
  topology.  $H^1(K, M)$ is the group `H1cont M` of classes of continuous crossed homomorphisms
  (`Ch4Cohomology`), a subgroup of the abstract group cohomology `H1 M`.
* The elliptic curve is a Weierstrass curve `W : WeierstrassCurve K` with `W.IsElliptic` (general Weierstrass
  equation; Milne uses $Y^2Z = X^3 + aXZ^2 + bZ^3$).  $E(\bar K)$ is `pointsRep W (AlgebraicClosure K)` and
  $E_n(\bar K)$ is `torsionRep W (AlgebraicClosure K) n`.
* **Localization (1.9, pdf p. 115).**  For a field $K_v$ containing $K$, Milne chooses an embedding
  $\bar K \to \bar K_v$ over $K$ (here `closureEmb`, the one given by `IsAlgClosed.lift`); restriction gives
  $\operatorname{Gal}(\bar K_v/K_v) \to \operatorname{Gal}(\bar K/K)$ (`decompHom`), and a crossed homomorphism
  $G_K \to E(\bar K)$ composed with these is a crossed homomorphism $G_{K_v} \to E(\bar K_v)$.  The local module
  $E(\bar K_v)$ is `localPointsRep W Kv`: the points of $W$ (with coefficients in $K \subseteq K_v$) over
  $\bar K_v$, with $G_{K_v}$ acting on the coordinates.  Milne remarks that the map does not depend on the
  embedding; this is not needed here (the definitions use the fixed choice).
* The Selmer group and the Tate–Shafarevich group of a number field are defined with all places: the finite
  places `IsDedekindDomain.HeightOneSpectrum (𝓞 K)` (completion `adicCompletion`) and the infinite places
  `NumberField.InfinitePlace K` (completion `InfinitePlace.Completion`).  For `K = ℚ` these are Milne's
  $p = 2, 3, 5, \dots, \infty$.
* Milne's "any integer $n$" in Lemma 2.1 and Theorem 3.1 must exclude $n = 0$.
-/

open CategoryTheory groupCohomology WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace NumberFieldKB.MilneEC

/-! ## Generic facts on group cohomology in low degrees -/

section Generic

variable {G : Type} [Group G]

/-- In a short complex of modules, exactness at the middle term, as a statement about elements. -/
theorem exact_elem {S : ShortComplex (ModuleCat ℤ)} (h : S.Exact) (x : S.X₂) :
    S.g x = 0 ↔ ∃ y, S.f y = x := by
  refine ⟨(ShortComplex.moduleCat_exact_iff S).1 h x, ?_⟩
  rintro ⟨y, rfl⟩
  simp

variable {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact)

/-- Exactness of $H^0(X_2) \to H^0(X_3) \to H^1(X_1)$, elementwise. -/
theorem exactH0 (z : H0 X.X₃) :
    δ hX 0 1 rfl z = 0 ↔ ∃ y : H0 X.X₂, map (MonoidHom.id G) X.g 0 y = z :=
  exact_elem (S := mapShortComplex₃ hX (zero_add 1)) (mapShortComplex₃_exact hX _) z

/-- Exactness of $H^0(X_3) \to H^1(X_1) \to H^1(X_2)$, elementwise. -/
theorem exactH1a (x : H1 X.X₁) :
    map (MonoidHom.id G) X.f 1 x = 0 ↔ ∃ z : H0 X.X₃, δ hX 0 1 rfl z = x :=
  exact_elem (S := mapShortComplex₁ hX (zero_add 1)) (mapShortComplex₁_exact hX _) x

include hX in
/-- Exactness of $H^1(X_1) \to H^1(X_2) \to H^1(X_3)$, elementwise. -/
theorem exactH1b (x : H1 X.X₂) :
    map (MonoidHom.id G) X.g 1 x = 0 ↔ ∃ y : H1 X.X₁, map (MonoidHom.id G) X.f 1 y = x :=
  exact_elem (S := mapShortComplex₂ X 1) (mapShortComplex₂_exact (k := ℤ) hX 1) x

/-- The effect of a map of modules on the class of a crossed homomorphism. -/
theorem map_H1π {A B : Rep ℤ G} (φ : A ⟶ B) (x : cocycles₁ A) (y : cocycles₁ B)
    (hy : (y : G → B) = φ.hom ∘ (x : G → A)) :
    map (MonoidHom.id G) φ 1 (H1π A x) = H1π B y := by
  rw [H1π_comp_map_apply]
  congr 1
  exact Subtype.ext hy.symm

/-- Naturality of `H0Iso` on elements. -/
theorem map_H0Iso_inv {A B : Rep ℤ G} (φ : A ⟶ B) (v : A.ρ.invariants) :
    map (MonoidHom.id G) φ 0 ((H0Iso A).inv v) = (H0Iso B).inv ((Rep.invariantsFunctor ℤ G).map φ v) := by
  have h := congrArg (fun F => F.hom ((H0Iso A).inv v)) (map_id_comp_H0Iso_hom (k := ℤ) φ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  have h2 : (H0Iso A).hom ((H0Iso A).inv v) = v := Iso.inv_hom_id_apply _ _
  rw [h2] at h
  calc map (MonoidHom.id G) φ 0 ((H0Iso A).inv v)
      = (H0Iso B).inv ((H0Iso B).hom (map (MonoidHom.id G) φ 0 ((H0Iso A).inv v))) :=
        (Iso.hom_inv_id_apply _ _).symm
    _ = _ := by rw [h]; rfl

/-- Continuity into a discrete (bottom) topology is unchanged by composing with an injective map. -/
theorem continuous_bot_comp_iff {G X Y : Type*} [TopologicalSpace G] (f : G → X) (φ : X → Y)
    (hφ : Function.Injective φ) :
    @Continuous G Y _ ⊥ (φ ∘ f) ↔ @Continuous G X _ ⊥ f := by
  constructor
  · intro h
    rw [continuous_def] at h ⊢
    intro s _
    have := h (φ '' s) trivial
    rwa [Set.preimage_comp, Set.preimage_image_eq _ hφ] at this
  · intro h
    rw [continuous_def] at h ⊢
    intro t _
    exact h (φ ⁻¹' t) trivial

/-- A class lies in `H1cont` exactly when it is the class of a continuous crossed homomorphism. -/
theorem mem_H1cont_iff [TopologicalSpace G] (A : Rep ℤ G) (x : H1 A) :
    x ∈ H1cont A ↔ ∃ c : cocycles₁ A, c ∈ contCocycles₁ A ∧ H1π A c = x := by
  simp [H1cont, AddSubgroup.mem_map]

end Generic

/-! ## Localization maps (1.9) -/

section Local

variable {K : Type} [Field K] (Kv : Type) [Field Kv] [Algebra K Kv]

/-- The embedding $\bar K \to \bar K_v$ over $K$ chosen in 1.9 (pdf p. 115). -/
noncomputable def closureEmb : AlgebraicClosure K →ₐ[K] AlgebraicClosure Kv := IsAlgClosed.lift

/-- The homomorphism $\operatorname{Gal}(\bar K_v/K_v) \to \operatorname{Gal}(\bar K/K)$ of 1.9 (pdf p. 115):
$\sigma$ maps to the unique $\tau$ with $\iota \circ \tau = \sigma \circ \iota$, where $\iota$ is `closureEmb`. -/
@[kb "milne2006ec" "Ch. IV, 1.9, the map Gal(Q_p^al/Q_p) → Gal(Q^al/Q), pdf p. 115"]
noncomputable def decompHom :
    (AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv) →* (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure Kv) := (closureEmb Kv).toRingHom.toAlgebra
  haveI : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure Kv) :=
    IsScalarTower.of_algebraMap_eq fun x => ((closureEmb Kv).commutes x).symm
  (AlgEquiv.restrictNormalHom (AlgebraicClosure K)).comp (AlgEquiv.restrictScalarsHom K)

/-- The defining property of `decompHom`: $\iota(\tau x) = \sigma(\iota x)$. -/
theorem closureEmb_decompHom (σ : AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv) (x : AlgebraicClosure K) :
    closureEmb Kv (decompHom Kv σ x) = σ (closureEmb Kv x) := by
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure Kv) := (closureEmb Kv).toRingHom.toAlgebra
  have : IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure Kv) :=
    IsScalarTower.of_algebraMap_eq fun x => ((closureEmb Kv).commutes x).symm
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) (AlgebraicClosure K) x

variable (W : WeierstrassCurve K)

/-- The local Galois module $E(\bar K_v)$ (pdf p. 115): points of $W$ over $\bar K_v$, with
$\operatorname{Gal}(\bar K_v/K_v)$ acting on coordinates. -/
noncomputable abbrev localPointsRep : Rep ℤ (AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv) :=
  Rep.res (AlgEquiv.restrictScalarsHom K) (pointsRep W (AlgebraicClosure Kv))

/-- Equivariance of the coordinatewise map `closureEmb` with respect to `decompHom`. -/
theorem localize_map (σ : AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv)
    (P : (W.toAffine⁄(AlgebraicClosure K)).Point) :
    Point.map (W' := W.toAffine) (closureEmb Kv)
        (Point.map (W' := W.toAffine) ((decompHom Kv σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
          AlgebraicClosure K →ₐ[K] AlgebraicClosure K) P) =
      Point.map (W' := W.toAffine)
        ((AlgEquiv.restrictScalarsHom K σ : AlgebraicClosure Kv ≃ₐ[K] AlgebraicClosure Kv) :
          AlgebraicClosure Kv →ₐ[K] AlgebraicClosure Kv)
        (Point.map (W' := W.toAffine) (closureEmb Kv) P) := by
  rw [Point.map_map, Point.map_map]
  have e : (closureEmb Kv).comp ((decompHom Kv σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
        AlgebraicClosure K →ₐ[K] AlgebraicClosure K) =
      ((AlgEquiv.restrictScalarsHom K σ : AlgebraicClosure Kv ≃ₐ[K] AlgebraicClosure Kv) :
        AlgebraicClosure Kv →ₐ[K] AlgebraicClosure Kv).comp (closureEmb Kv) :=
    AlgHom.ext fun x => closureEmb_decompHom Kv σ x
  rw [e]

/-- The map $E(\bar K) \to E(\bar K_v)$ induced by `closureEmb`, compatible with `decompHom`. -/
noncomputable def localizePoints :
    Rep.res (decompHom Kv) (pointsRep W (AlgebraicClosure K)) ⟶ localPointsRep Kv W :=
  Rep.ofHom ⟨(Point.map (W' := W.toAffine) (closureEmb Kv)).toIntLinearMap, fun σ => by
    ext P
    exact localize_map Kv W σ P⟩

/-- The map $E_n(\bar K) \to E(\bar K_v)$: inclusion followed by `localizePoints`. -/
noncomputable def localizeTorsion (n : ℤ) :
    Rep.res (decompHom Kv) (torsionRep W (AlgebraicClosure K) n) ⟶ localPointsRep Kv W :=
  Rep.ofHom ⟨((Point.map (W' := W.toAffine) (closureEmb Kv)).comp
      (torsionPoints W (AlgebraicClosure K) n).subtype).toIntLinearMap, fun σ => by
    ext P
    exact localize_map Kv W σ P.1⟩

/-- The localization map $H^1(K, E) \to H^1(K_v, E)$ of 1.9 (pdf p. 115). -/
@[kb "milne2006ec" "Ch. IV, 1.9, the localization map H^1(Q, E) → H^1(Q_p, E), pdf p. 115"]
noncomputable def locPoints : H1 (pointsRep W (AlgebraicClosure K)) →+ H1 (localPointsRep Kv W) :=
  (map (decompHom Kv) (localizePoints Kv W) 1).hom.toAddMonoidHom

/-- The map $H^1(K, E_n) \to H^1(K_v, E)$ (pdf p. 117): $E_n \to E$ followed by localization. -/
@[kb "milne2006ec" "Ch. IV, 1.9, the localization map H^1(Q, E_n) → H^1(Q_p, E), pdf p. 117"]
noncomputable def locTorsion (n : ℤ) : H1 (torsionRep W (AlgebraicClosure K) n) →+ H1 (localPointsRep Kv W) :=
  (map (decompHom Kv) (localizeTorsion Kv W n) 1).hom.toAddMonoidHom

end Local

/-! ## The Kummer sequence (22) -/

section Kummer

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

/-- The inclusion $E_n(\bar K) \to E(\bar K)$ of $G_K$-modules. -/
noncomputable def torsionIncl (L : Type) [Field L] [Algebra K L] (n : ℤ) :
    torsionRep W L n ⟶ pointsRep W L :=
  Rep.ofHom ⟨(torsionPoints W L n).subtype.toIntLinearMap, fun σ => by
    ext P
    rfl⟩

/-- Multiplication by $n$ on $E(\bar K)$, a map of $G_K$-modules. -/
noncomputable def pointsMul (L : Type) [Field L] [Algebra K L] (n : ℤ) : pointsRep W L ⟶ pointsRep W L :=
  Rep.ofHom ⟨(zsmulAddGroupHom (α := (W.toAffine⁄L).Point) n).toIntLinearMap, fun σ => by
    ext P
    exact (map_zsmul _ _ _).symm⟩

/-- The map $H^1(K, E_n) \to H^1(K, E)$ induced by the inclusion. -/
noncomputable def torsionToPointsH1 (L : Type) [Field L] [Algebra K L] (n : ℤ) :
    H1 (torsionRep W L n) →+ H1 (pointsRep W L) :=
  (map (MonoidHom.id _) (torsionIncl W L n) 1).hom.toAddMonoidHom

/-- The sequence $0 \to E_n(\bar K) \to E(\bar K) \xrightarrow{n} E(\bar K)$ of $G_K$-modules (pdf p. 117). -/
noncomputable def kummerComplex (L : Type) [Field L] [Algebra K L] (n : ℤ) : ShortComplex (Rep ℤ (L ≃ₐ[K] L)) :=
  ShortComplex.mk (torsionIncl W L n) (pointsMul W L n) (by
    ext P
    exact P.2)

/-- **Lemma 2.1** (pdf p. 116), a named statement: for an elliptic curve $E$ over an algebraically closed field
$k$ and an integer $n \ne 0$, $P \mapsto nP$ is surjective on $E(k)$.  (Milne says "integer $n$"; $n = 0$ must be
excluded.)  Milne's proofs use the Nullstellensatz with the complex uniformization, or that the image of the
regular map $n$ on the complete connected curve $E$ is closed and connected. -/
@[kb "milne2006ec" "Ch. IV, Lemma 2.1, pdf p. 116"]
structure Lemma2_1 : Prop where
  surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℤ),
    n ≠ 0 → Function.Surjective fun P : W.toAffine.Point => n • P

/-- Lemma 2.1 applied to the points of $W$ over an algebraically closed extension $L$ of $K$. -/
theorem Lemma2_1.surjective_baseChange (h : Lemma2_1) [W.IsElliptic] (L : Type) [Field L] [Algebra K L]
    [IsAlgClosed L] (n : ℤ) (hn : n ≠ 0) : Function.Surjective fun P : (W.toAffine⁄L).Point => n • P :=
  haveI : (W.baseChange L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic
  h.surjective L (W.baseChange L) n hn

/-- The sequence $0 \to E_n(\bar K) \to E(\bar K) \xrightarrow{n} E(\bar K) \to 0$ is exact (pdf p. 117; uses
Lemma 2.1). -/
@[kb "milne2006ec" "Ch. IV, §2, the exact sequence 0 → E_n → E → E → 0, pdf p. 117"]
theorem kummerComplex_shortExact (h : Lemma2_1) [W.IsElliptic] (L : Type) [Field L] [Algebra K L]
    [IsAlgClosed L] (n : ℤ) (hn : n ≠ 0) : (kummerComplex W L n).ShortExact where
  exact := (forget₂ (Rep ℤ (L ≃ₐ[K] L)) (ModuleCat ℤ)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun x hx => ⟨⟨x, hx⟩, rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
  epi_g := (Rep.epi_iff_surjective _).2 (Lemma2_1.surjective_baseChange W h L n hn)

/-- The point of $E(\bar K)^{G}$ defined by a point of $E(K)$, as an element of $H^0$. -/
noncomputable def pointsToH0 (L : Type) [Field L] [Algebra K L] :
    (W.toAffine.Point) →+ H0 (pointsRep W L) :=
  ((H0Iso (pointsRep W L)).inv.hom.toAddMonoidHom).comp
    { toFun := fun P => ⟨Point.map (W' := W.toAffine) (Algebra.ofId K L) (by exact P), fun σ => by
        change Point.map (W' := W.toAffine) (σ : L →ₐ[K] L)
          (Point.map (W' := W.toAffine) (Algebra.ofId K L) P) = _
        rw [Point.map_map]
        have : (σ : L →ₐ[K] L).comp (Algebra.ofId K L) = Algebra.ofId K L :=
          AlgHom.ext fun a => σ.commutes a
        rw [this]⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }

/-- `pointsToH0` is injective. -/
theorem pointsToH0_injective (L : Type) [Field L] [Algebra K L] : Function.Injective (pointsToH0 W L) := by
  intro P Q h
  have hinj : Function.Injective (H0Iso (pointsRep W L)).inv := fun a b hab => by
    simpa using congrArg (H0Iso (pointsRep W L)).hom hab
  have h2 : Point.map (W' := W.toAffine) (Algebra.ofId K L) P =
      Point.map (W' := W.toAffine) (Algebra.ofId K L) Q := Subtype.ext_iff.1 (hinj h)
  exact Point.map_injective (W' := W.toAffine) (Algebra.ofId K L) h2

/-- When `L / K` is Galois, `pointsToH0` is surjective (this is `points_fixed_iff`). -/
theorem pointsToH0_surjective (L : Type) [Field L] [Algebra K L] [IsGalois K L] :
    Function.Surjective (pointsToH0 W L) := by
  intro z
  obtain ⟨v, rfl⟩ : ∃ v, (H0Iso (pointsRep W L)).inv v = z :=
    ⟨(H0Iso (pointsRep W L)).hom z, Iso.hom_inv_id_apply _ _⟩
  obtain ⟨R, hR⟩ := (points_fixed_iff W L v.1).1 (fun σ => v.2 σ)
  refine ⟨R, ?_⟩
  change (H0Iso (pointsRep W L)).inv _ = _
  congr 1
  exact Subtype.ext hR

/-- Multiplication by `n` on `H^0` corresponds to multiplication by `n` on `E(K)`. -/
theorem map_pointsMul_pointsToH0 (L : Type) [Field L] [Algebra K L] (n : ℤ) (R : W.toAffine.Point) :
    map (MonoidHom.id _) (pointsMul W L n) 0 (pointsToH0 W L R) = pointsToH0 W L (n • R) := by
  change map (MonoidHom.id _) (pointsMul W L n) 0 ((H0Iso (pointsRep W L)).inv _) = (H0Iso (pointsRep W L)).inv _
  rw [map_H0Iso_inv]
  congr 1
  refine Subtype.ext ?_
  exact (map_zsmul (Point.map (W' := W.toAffine) (Algebra.ofId K L)) n R).symm

/-- The **Kummer map** $E(K) \to H^1(K, E_n)$ (pdf p. 117): the connecting map of the cohomology sequence of
$0 \to E_n \to E \xrightarrow{n} E \to 0$ restricted to $E(K) = H^0(K, E)$.  Explicitly
(`kummerMap_apply`), $P$ maps to the class of $\sigma \mapsto \sigma Q - Q$ where $nQ = P$. -/
@[kb "milne2006ec" "Ch. IV, §2, the map E(Q)/nE(Q) → H^1(Q, E_n) of (22), pdf p. 117"]
noncomputable def kummerMap (h : Lemma2_1) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0) :
    W.toAffine.Point →+ H1 (torsionRep W (AlgebraicClosure K) n) :=
  (δ (kummerComplex_shortExact W h (AlgebraicClosure K) n hn) 0 1 rfl).hom.toAddMonoidHom.comp
    (pointsToH0 W (AlgebraicClosure K))

/-- The explicit form of the Kummer map: if $nQ = P$ in $E(\bar K)$, then the image of $P$ is the class of the
crossed homomorphism $\sigma \mapsto \sigma Q - Q$ (with values in $E_n$). -/
theorem kummerMap_apply (h : Lemma2_1) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0) (P : W.toAffine.Point)
    (Q : (W.toAffine⁄(AlgebraicClosure K)).Point)
    (hQ : n • Q = Point.map (W' := W.toAffine) (Algebra.ofId K (AlgebraicClosure K)) (by exact P))
    (f : cocycles₁ (torsionRep W (AlgebraicClosure K) n))
    (hf : ∀ σ, ((f σ : torsionPoints W (AlgebraicClosure K) n) : (W.toAffine⁄(AlgebraicClosure K)).Point) =
      Point.map (W' := W.toAffine) (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) Q - Q) :
    kummerMap W h n hn P = H1π _ f := by
  have hx : (kummerComplex W (AlgebraicClosure K) n).f.hom ∘ (fun σ => (f : _ → _) σ) =
      d₀₁ (kummerComplex W (AlgebraicClosure K) n).X₂ Q := by
    funext σ
    rw [d₀₁_hom_apply]
    exact (hf σ)
  have key := δ₀_apply (kummerComplex_shortExact W h (AlgebraicClosure K) n hn)
    ⟨Point.map (W' := W.toAffine) (Algebra.ofId K (AlgebraicClosure K)) P, fun σ => by
      change Point.map (W' := W.toAffine) (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K)
          (Point.map (W' := W.toAffine) (Algebra.ofId K (AlgebraicClosure K)) P) = _
      rw [Point.map_map]
      have : (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K).comp (Algebra.ofId K (AlgebraicClosure K)) =
          Algebra.ofId K (AlgebraicClosure K) := AlgHom.ext fun a => σ.commutes a
      rw [this]⟩ Q hQ _ hx
  exact key

/-- Multiplication by `n` on `E` induces multiplication by `n` on `H^1`. -/
theorem map_pointsMul_H1 (L : Type) [Field L] [Algebra K L] (n : ℤ) (x : H1 (pointsRep W L)) :
    map (MonoidHom.id _) (pointsMul W L n) 1 x = n • x := by
  refine H1_induction_on x (fun c => ?_)
  rw [map_H1π _ c (n • c) ?_, map_zsmul]
  funext g
  rfl

/-- A crossed homomorphism of `E` with values in `E_n` is a crossed homomorphism of `E_n`. -/
theorem exists_torsionCocycle (L : Type) [Field L] [Algebra K L] (n : ℤ) (c : cocycles₁ (pointsRep W L))
    (hc : ∀ σ, n • (c σ : (W.toAffine⁄L).Point) = 0) :
    ∃ b : cocycles₁ (torsionRep W L n), ∀ σ, ((b σ : torsionPoints W L n) : (W.toAffine⁄L).Point) = c σ :=
  ⟨⟨fun σ => ⟨c σ, hc σ⟩, (mem_cocycles₁_iff _).2 fun g h =>
    Subtype.ext ((mem_cocycles₁_iff _).1 c.2 g h)⟩, fun σ => rfl⟩

/-- The image of a crossed homomorphism with values in `E_n` in the crossed homomorphisms of `E`. -/
theorem torsionIncl_cocycle_coe (L : Type) [Field L] [Algebra K L] (n : ℤ)
    (b : cocycles₁ (torsionRep W L n)) :
    (mapCocycles₁ (MonoidHom.id _) (torsionIncl W L n) b : _ → _) =
      (torsionIncl W L n).hom ∘ (b : _ → _) := rfl

theorem torsionIncl_hom_injective (L : Type) [Field L] [Algebra K L] (n : ℤ) :
    Function.Injective (torsionIncl W L n).hom := fun _ _ h => Subtype.ext h

/-- A crossed homomorphism with values in `E_n` is continuous exactly when its image in `E` is. -/
theorem torsionIncl_mem_contCocycles_iff (L : Type) [Field L] [Algebra K L] (n : ℤ)
    (b : cocycles₁ (torsionRep W L n)) :
    mapCocycles₁ (MonoidHom.id _) (torsionIncl W L n) b ∈ contCocycles₁ (pointsRep W L) ↔
      b ∈ contCocycles₁ (torsionRep W L n) :=
  continuous_bot_comp_iff (b : _ → _) (torsionIncl W L n).hom (torsionIncl_hom_injective W L n)

/-- The effect of `torsionToPointsH1` on the class of a crossed homomorphism. -/
theorem torsionToPointsH1_H1π (L : Type) [Field L] [Algebra K L] (n : ℤ)
    (b : cocycles₁ (torsionRep W L n)) :
    torsionToPointsH1 W L n (H1π (torsionRep W L n) b) =
      H1π (pointsRep W L) (mapCocycles₁ (MonoidHom.id (L ≃ₐ[K] L)) (torsionIncl W L n) b) := by
  exact map_H1π (torsionIncl W L n) b _ (torsionIncl_cocycle_coe W L n b)

/-- The localization of a class from `E_n` factors through `E`. -/
theorem locTorsion_eq (Kv : Type) [Field Kv] [Algebra K Kv] (n : ℤ)
    (x : H1 (torsionRep W (AlgebraicClosure K) n)) :
    locTorsion Kv W n x = locPoints Kv W (torsionToPointsH1 W (AlgebraicClosure K) n x) := by
  refine H1_induction_on x (fun b => ?_)
  rw [torsionToPointsH1_H1π]
  change map (decompHom Kv) (localizeTorsion Kv W n) 1 (H1π _ b) =
    map (decompHom Kv) (localizePoints Kv W) 1 (H1π _ _)
  rw [H1π_comp_map_apply, H1π_comp_map_apply]
  congr 1

/-- A point coming from `K` is fixed by every automorphism. -/
theorem map_ofId_fixed (L : Type) [Field L] [Algebra K L] (P : W.toAffine.Point) (σ : L ≃ₐ[K] L) :
    Point.map (W' := W.toAffine) (σ : L →ₐ[K] L) (Point.map (W' := W.toAffine) (Algebra.ofId K L) P) =
      Point.map (W' := W.toAffine) (Algebra.ofId K L) P := by
  rw [Point.map_map]
  have : (σ : L →ₐ[K] L).comp (Algebra.ofId K L) = Algebra.ofId K L :=
    AlgHom.ext fun a => σ.commutes a
  rw [this]

/-- The Kummer class of a point is the class of a continuous crossed homomorphism with values in `E_n`. -/
theorem kummerMap_eq_continuous (h : Lemma2_1) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0) (P : W.toAffine.Point) :
    ∃ b : cocycles₁ (torsionRep W (AlgebraicClosure K) n), b ∈ contCocycles₁ _ ∧
      kummerMap W h n hn P = H1π _ b := by
  obtain ⟨Q, hQ⟩ := Lemma2_1.surjective_baseChange W h (AlgebraicClosure K) n hn
    (Point.map (W' := W.toAffine) (Algebra.ofId K (AlgebraicClosure K)) P)
  have hQ' : n • Q = Point.map (W' := W.toAffine) (Algebra.ofId K (AlgebraicClosure K)) P := hQ
  let c : cocycles₁ (pointsRep W (AlgebraicClosure K)) :=
    ⟨d₀₁ (pointsRep W (AlgebraicClosure K)) Q, coboundaries₁_le_cocycles₁ _ ⟨Q, rfl⟩⟩
  have hcoe : ∀ σ, (c σ : (W.toAffine⁄(AlgebraicClosure K)).Point) =
      Point.map (W' := W.toAffine) (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) Q - Q := fun σ => by
    change (d₀₁ (pointsRep W (AlgebraicClosure K)) Q) σ = _
    rw [d₀₁_hom_apply]
    rfl
  have hc : ∀ σ, n • (c σ : (W.toAffine⁄(AlgebraicClosure K)).Point) = 0 := fun σ => by
    rw [hcoe, smul_sub, ← map_zsmul, hQ', map_ofId_fixed, sub_self]
  obtain ⟨b, hb⟩ := exists_torsionCocycle W (AlgebraicClosure K) n c hc
  refine ⟨b, ?_, kummerMap_apply W h n hn P Q hQ' b (fun σ => (hb σ).trans (hcoe σ))⟩
  have hfun : (torsionIncl W (AlgebraicClosure K) n).hom ∘ (b : _ → _) = (c : _ → _) :=
    funext fun σ => hb σ
  have hcont : @Continuous _ _ _ ⊥ (c : _ → _) :=
    continuous_of_mem_coboundaries₁ _ (pointsRep_isDiscreteModule W (AlgebraicClosure K)) c ⟨Q, rfl⟩
  exact (continuous_bot_comp_iff _ _ (torsionIncl_hom_injective W (AlgebraicClosure K) n)).1
    (hfun ▸ hcont)

variable [PerfectField K]

/-- **The exact sequence (22)** (pdf p. 117), for a perfect field $K$ (Milne: $K = \mathbb{Q}$; §7 uses a perfect
field):
$$0 \to E(K)/nE(K) \to H^1(K, E_n) \to H^1(K, E)_n \to 0.$$
Stated as: (a) the kernel of the Kummer map is $nE(K)$; (b) its image is the kernel of $H^1(K, E_n) \to H^1(K, E)$
and consists of continuous classes; (c) the image of $H^1(K, E_n)$ in $H^1(K, E)$ is the set of continuous classes
killed by $n$. -/
@[kb "milne2006ec" "Ch. IV, §2, the exact sequence (22), pdf p. 117"]
theorem exact_22 (h : Lemma2_1) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0) :
    (kummerMap W h n hn).ker = multiples W.toAffine.Point n ∧
      (kummerMap W h n hn).range = (torsionToPointsH1 W (AlgebraicClosure K) n).ker ∧
      (kummerMap W h n hn).range ≤ H1cont (torsionRep W (AlgebraicClosure K) n) ∧
      (H1cont (torsionRep W (AlgebraicClosure K) n)).map (torsionToPointsH1 W (AlgebraicClosure K) n) =
        H1cont (pointsRep W (AlgebraicClosure K)) ⊓
          (zsmulAddGroupHom (α := H1 (pointsRep W (AlgebraicClosure K))) n).ker := by
  have hX := kummerComplex_shortExact W h (AlgebraicClosure K) n hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext P
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    change δ hX 0 1 rfl (pointsToH0 W _ P) = 0 ↔ _
    rw [exactH0 hX]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨R, rfl⟩ := pointsToH0_surjective W (AlgebraicClosure K) y
      refine ⟨R, ?_⟩
      apply pointsToH0_injective W (AlgebraicClosure K)
      rw [← hy]
      exact (map_pointsMul_pointsToH0 W (AlgebraicClosure K) n R).symm
    · rintro ⟨R, rfl⟩
      exact ⟨pointsToH0 W _ R, map_pointsMul_pointsToH0 W (AlgebraicClosure K) n R⟩
  · ext x
    rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
    change _ ↔ map (MonoidHom.id _) (torsionIncl W (AlgebraicClosure K) n) 1 x = 0
    refine Iff.trans ?_ (exactH1a hX x).symm
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨R, rfl⟩ := pointsToH0_surjective W (AlgebraicClosure K) z
      exact ⟨R, rfl⟩
  · rintro _ ⟨P, rfl⟩
    obtain ⟨b, hb, hP⟩ := kummerMap_eq_continuous W h n hn P
    rw [mem_H1cont_iff]
    exact ⟨b, hb, hP.symm⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' : y ∈ H1cont (torsionRep W (AlgebraicClosure K) n) := hy
      rw [mem_H1cont_iff] at hy'
      obtain ⟨b, hb, rfl⟩ := hy'
      refine ⟨?_, ?_⟩
      · change _ ∈ H1cont (pointsRep W (AlgebraicClosure K))
        rw [mem_H1cont_iff]
        refine ⟨mapCocycles₁ (MonoidHom.id _) (torsionIncl W (AlgebraicClosure K) n) b, ?_, ?_⟩
        · exact (torsionIncl_mem_contCocycles_iff W (AlgebraicClosure K) n b).2 hb
        · exact (torsionToPointsH1_H1π W (AlgebraicClosure K) n b).symm
      · change _ ∈ (zsmulAddGroupHom (α := H1 (pointsRep W (AlgebraicClosure K))) n).ker
        rw [AddMonoidHom.mem_ker]
        change n • (map (MonoidHom.id _) (torsionIncl W (AlgebraicClosure K) n) 1 (H1π _ b)) = 0
        rw [← map_pointsMul_H1]
        exact (exactH1b hX _).2 ⟨_, rfl⟩
    · rintro ⟨hx1, hx2⟩
      have hx1' : x ∈ H1cont (pointsRep W (AlgebraicClosure K)) := hx1
      rw [mem_H1cont_iff] at hx1'
      obtain ⟨c, hc, rfl⟩ := hx1'
      have hx2' := hx2
      have h0 : map (MonoidHom.id _) (pointsMul W (AlgebraicClosure K) n) 1 (H1π _ c) = 0 := by
        rw [map_pointsMul_H1]
        exact AddMonoidHom.mem_ker.1 hx2'
      obtain ⟨y, hy0⟩ := (exactH1b hX _).1 h0
      obtain ⟨b, rfl⟩ := (h1_eq_crossed_mod_principal _).1 y
      have hy2 : H1π (pointsRep W (AlgebraicClosure K))
          (mapCocycles₁ (MonoidHom.id _) (torsionIncl W (AlgebraicClosure K) n) b) = H1π _ c :=
        (torsionToPointsH1_H1π W (AlgebraicClosure K) n b).symm.trans hy0
      have hy1 := (H1π_eq_iff (A := pointsRep W (AlgebraicClosure K)) _ _).1 hy2
      have hd : (mapCocycles₁ (MonoidHom.id _) (torsionIncl W (AlgebraicClosure K) n) b - c) ∈
          contCocycles₁ (pointsRep W (AlgebraicClosure K)) :=
        continuous_of_mem_coboundaries₁ _ (pointsRep_isDiscreteModule W (AlgebraicClosure K)) _ hy1
      have hbc : mapCocycles₁ (MonoidHom.id _) (torsionIncl W (AlgebraicClosure K) n) b ∈
          contCocycles₁ (pointsRep W (AlgebraicClosure K)) := by
        have := add_mem hd hc
        simpa using this
      refine AddSubgroup.mem_map.2 ⟨H1π _ b, ?_, hy0⟩
      rw [mem_H1cont_iff]
      refine ⟨b, ?_, rfl⟩
      exact (torsionIncl_mem_contCocycles_iff W (AlgebraicClosure K) n b).1 hbc

/-- The quotient $E(K)/nE(K)$ embeds in $H^1(K, E_n)$ (the injectivity in (22)). -/
@[kb "milne2006ec" "Ch. IV, §2, the exact sequence (22), pdf p. 117"]
noncomputable def kummerQuotientHom (h : Lemma2_1) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0) :
    W.toAffine.Point ⧸ multiples W.toAffine.Point n →+ H1 (torsionRep W (AlgebraicClosure K) n) :=
  QuotientAddGroup.lift _ (kummerMap W h n hn) (fun P hP => by
    rw [← (exact_22 W h n hn).1] at hP
    exact hP)

theorem kummerQuotientHom_injective (h : Lemma2_1) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0) :
    Function.Injective (kummerQuotientHom W h n hn) := by
  intro a b
  induction a using QuotientAddGroup.induction_on with
  | H P =>
    induction b using QuotientAddGroup.induction_on with
    | H Q =>
      intro hab
      have hab' : kummerMap W h n hn P = kummerMap W h n hn Q := hab
      rw [QuotientAddGroup.eq, ← (exact_22 W h n hn).1, AddMonoidHom.mem_ker, map_add, map_neg, hab']
      simp

end Kummer

/-! ## Selmer and Tate–Shafarevich groups (§2) -/

section Groups

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

/-- The Selmer group relative to a family $(K_v)_{v \in V}$ of extensions of $K$ (pdf p. 117): the continuous
classes in $H^1(K, E_n)$ whose image in every $H^1(K_v, E)$ is zero. -/
noncomputable def selmerGroupOf {V : Type} (Kv : V → Type) [∀ v, Field (Kv v)] [∀ v, Algebra K (Kv v)] (n : ℤ) :
    AddSubgroup (H1 (torsionRep W (AlgebraicClosure K) n)) :=
  H1cont (torsionRep W (AlgebraicClosure K) n) ⊓ ⨅ v, (locTorsion (Kv v) W n).ker

/-- The Tate–Shafarevich group relative to a family $(K_v)_{v \in V}$ of extensions of $K$ (pdf p. 117): the
continuous classes in $H^1(K, E)$ whose image in every $H^1(K_v, E)$ is zero. -/
noncomputable def tateShafarevichOf {V : Type} (Kv : V → Type) [∀ v, Field (Kv v)] [∀ v, Algebra K (Kv v)] :
    AddSubgroup (H1 (pointsRep W (AlgebraicClosure K))) :=
  H1cont (pointsRep W (AlgebraicClosure K)) ⊓ ⨅ v, (locPoints (Kv v) W).ker

variable (K) [NumberField K]

/-- The **Selmer group** $S^{(n)}(E/K)$ of an elliptic curve over a number field (pdf pp. 117, 122):
$\operatorname{Ker}\bigl(H^1(K, E_n) \to \prod_v H^1(K_v, E)\bigr)$, $v$ running over all places of $K$ (finite
and infinite). -/
@[kb "milne2006ec" "Ch. IV, §2 and §3, definition of the Selmer group, pdf pp. 117, 122"]
noncomputable def selmerGroup (n : ℤ) : AddSubgroup (H1 (torsionRep W (AlgebraicClosure K) n)) :=
  selmerGroupOf W (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      v.adicCompletion K) n ⊓
    selmerGroupOf W (fun w : NumberField.InfinitePlace K => w.Completion) n

/-- The **Tate–Shafarevich group** $Ш(E/K)$ of an elliptic curve over a number field (pdf p. 117):
$\operatorname{Ker}\bigl(H^1(K, E) \to \prod_v H^1(K_v, E)\bigr)$ over all places $v$ of $K$. -/
@[kb "milne2006ec" "Ch. IV, §2, definition of the Tate-Shafarevich group, pdf p. 117"]
noncomputable def tateShafarevich : AddSubgroup (H1 (pointsRep W (AlgebraicClosure K))) :=
  tateShafarevichOf W (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      v.adicCompletion K) ⊓
    tateShafarevichOf W (fun w : NumberField.InfinitePlace K => w.Completion)

/-- Membership in the Selmer group, unfolded. -/
theorem mem_selmerGroup_iff (n : ℤ) (x : H1 (torsionRep W (AlgebraicClosure K) n)) :
    x ∈ selmerGroup K W n ↔ x ∈ H1cont (torsionRep W (AlgebraicClosure K) n) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        locTorsion (v.adicCompletion K) W n x = 0) ∧
      ∀ w : NumberField.InfinitePlace K, locTorsion w.Completion W n x = 0 := by
  simp only [selmerGroup, selmerGroupOf, AddSubgroup.mem_inf, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker]
  tauto

/-- Membership in the Tate–Shafarevich group, unfolded. -/
theorem mem_tateShafarevich_iff (x : H1 (pointsRep W (AlgebraicClosure K))) :
    x ∈ tateShafarevich K W ↔ x ∈ H1cont (pointsRep W (AlgebraicClosure K)) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        locPoints (v.adicCompletion K) W x = 0) ∧
      ∀ w : NumberField.InfinitePlace K, locPoints w.Completion W x = 0 := by
  simp only [tateShafarevich, tateShafarevichOf, AddSubgroup.mem_inf, AddSubgroup.mem_iInf,
    AddMonoidHom.mem_ker]
  tauto

/-- Milne (pdf p. 118): the Tate–Shafarevich group is a torsion group. -/
@[kb "milne2006ec" "Ch. IV, §2, the Tate-Shafarevich group is torsion, pdf p. 118"]
theorem tateShafarevich_torsion (x : H1 (pointsRep W (AlgebraicClosure K))) (hx : x ∈ tateShafarevich K W) :
    ∃ m : ℕ, 0 < m ∧ (m : ℤ) • x = 0 := by
  have hx' : x ∈ H1cont (pointsRep W (AlgebraicClosure K)) := hx.1.1
  exact H1cont_torsion _ (pointsRep_isDiscreteModule W (AlgebraicClosure K)) x hx'

/-- **The fundamental exact sequence (23)** (pdf p. 118):
$$0 \to E(K)/nE(K) \to S^{(n)}(E/K) \to Ш(E/K)_n \to 0.$$
Stated as: (a) the image of the Kummer map lies in the Selmer group; (b) the map $H^1(K, E_n) \to H^1(K, E)$ sends
the Selmer group onto the elements of $Ш(E/K)$ killed by $n$; (c) an element of the Selmer group maps to zero if and
only if it is in the image of the Kummer map.  (Injectivity on $E(K)/nE(K)$ is `kummerQuotientHom_injective`.) -/
@[kb "milne2006ec" "Ch. IV, §2, the fundamental exact sequence (23), pdf p. 118"]
theorem exact_23 (h : Lemma2_1) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0) :
    (kummerMap W h n hn).range ≤ selmerGroup K W n ∧
      (selmerGroup K W n).map (torsionToPointsH1 W (AlgebraicClosure K) n) =
        tateShafarevich K W ⊓ (zsmulAddGroupHom (α := H1 (pointsRep W (AlgebraicClosure K))) n).ker ∧
      ∀ x ∈ selmerGroup K W n, torsionToPointsH1 W (AlgebraicClosure K) n x = 0 ↔
        x ∈ (kummerMap W h n hn).range := by
  obtain ⟨ha, hb, hc, hd⟩ := exact_22 W h n hn
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨P, rfl⟩
    have h1 : kummerMap W h n hn P ∈ H1cont (torsionRep W (AlgebraicClosure K) n) := hc ⟨P, rfl⟩
    have h2 : torsionToPointsH1 W (AlgebraicClosure K) n (kummerMap W h n hn P) = 0 := by
      have : kummerMap W h n hn P ∈ (torsionToPointsH1 W (AlgebraicClosure K) n).ker := hb ▸ ⟨P, rfl⟩
      exact this
    rw [mem_selmerGroup_iff]
    refine ⟨h1, fun v => ?_, fun w => ?_⟩
    · rw [locTorsion_eq, h2, map_zero]
    · rw [locTorsion_eq, h2, map_zero]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ selmerGroup K W n := hx
      rw [mem_selmerGroup_iff] at hx'
      obtain ⟨hx1, hx2, hx3⟩ := hx'
      have hy : torsionToPointsH1 W (AlgebraicClosure K) n x ∈
          H1cont (pointsRep W (AlgebraicClosure K)) ⊓
            (zsmulAddGroupHom (α := H1 (pointsRep W (AlgebraicClosure K))) n).ker := by
        rw [← hd]
        exact ⟨x, hx1, rfl⟩
      refine AddSubgroup.mem_inf.2 ⟨?_, hy.2⟩
      rw [mem_tateShafarevich_iff]
      refine ⟨hy.1, fun v => ?_, fun w => ?_⟩
      · rw [← locTorsion_eq]; exact hx2 v
      · rw [← locTorsion_eq]; exact hx3 w
    · rintro ⟨hy1, hy2⟩
      have hy1' : y ∈ tateShafarevich K W := hy1
      rw [mem_tateShafarevich_iff] at hy1'
      obtain ⟨hy1, hy3, hy4⟩ := hy1'
      have : y ∈ (H1cont (torsionRep W (AlgebraicClosure K) n)).map
          (torsionToPointsH1 W (AlgebraicClosure K) n) := by
        rw [hd]
        exact ⟨hy1, hy2⟩
      obtain ⟨x, hx, rfl⟩ := this
      refine ⟨x, ?_, rfl⟩
      show x ∈ selmerGroup K W n
      rw [mem_selmerGroup_iff]
      refine ⟨hx, fun v => ?_, fun w => ?_⟩
      · rw [locTorsion_eq]; exact hy3 v
      · rw [locTorsion_eq]; exact hy4 w
  · intro x _
    rw [← AddMonoidHom.mem_ker, ← hb]

/-- **Theorem 3.1** (pdf p. 118), a named statement: for an elliptic curve $E$ over a number field $K$ and an
integer $n \ne 0$, the Selmer group $S^{(n)}(E/K)$ is finite.  (Milne says "any integer $n$"; for $n = 0$ the
Selmer group is $Ш(E/K)$, whose finiteness is Conjecture 5.3.)  Milne proves it in §3 from Lemmas 3.2–3.8 and
the finiteness of the class group and finite generation of the $T$-units (Corollary 3.12). -/
@[kb "milne2006ec" "Ch. IV, Thm. 3.1, pdf p. 118"]
structure Thm3_1_Selmer : Prop where
  finite : ∀ (K : Type) [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic] (n : ℤ), n ≠ 0 →
    Finite (selmerGroup K W n)

/-- **Weak finite basis theorem** (Chapter IV, introduction, pdf p. 109): for an elliptic curve $E$ over a number
field $K$ and an integer $n \ne 0$, $E(K)/nE(K)$ is finite.  (Milne says "any integer $n$"; $n = 0$ must be
excluded.)  Proved from Lemma 2.1 and Theorem 3.1 (named statements) by the injection of (23). -/
@[kb "milne2006ec" "Ch. IV, introduction, Weak finite basis theorem, pdf p. 109"]
theorem weak_finite_basis (h21 : Lemma2_1) (h31 : Thm3_1_Selmer) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0) :
    Finite (W.toAffine.Point ⧸ multiples W.toAffine.Point n) := by
  have hmem : ∀ a : W.toAffine.Point ⧸ multiples W.toAffine.Point n,
      kummerQuotientHom W h21 n hn a ∈ selmerGroup K W n := by
    intro a
    induction a using QuotientAddGroup.induction_on with
    | H P => exact (exact_23 K W h21 n hn).1 ⟨P, rfl⟩
  have := h31.finite K W n hn
  exact Finite.of_injective (fun a => (⟨kummerQuotientHom W h21 n hn a, hmem a⟩ : selmerGroup K W n))
    (fun a b hab => kummerQuotientHom_injective W h21 n hn (congrArg Subtype.val hab))

/-- **Finite basis (Mordell–Weil) theorem** (Chapter IV, introduction, pdf p. 109; proof completed in §4,
pdf p. 133): for an elliptic curve $E$ over a number field $K$, $E(K)$ is finitely generated.  Proved from
Lemma 2.1 and Theorem 3.1 (named statements): the weak finite basis theorem and descent with heights. -/
@[kb "milne2006ec" "Ch. IV, introduction, Finite basis theorem, pdf p. 109"]
theorem finite_basis (h21 : Lemma2_1) (h31 : Thm3_1_Selmer) [W.IsElliptic] :
    AddGroup.FG W.toAffine.Point :=
  fg_of_finite_quotient_two W.toAffine (weak_finite_basis K W h21 h31 2 two_ne_zero)

end Groups

/-! ## Lemma 2.2: the kernel-cokernel sequence -/

section KerCoker

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (α : A →+ B) (β : B →+ C)

/-- The connecting map $\operatorname{Ker}(\beta) \to \operatorname{Coker}(\alpha)$ of Lemma 2.2. -/
def kerCokerConnecting : β.ker →+ B ⧸ α.range :=
  (QuotientAddGroup.mk' α.range).comp β.ker.subtype

/-- The map $\operatorname{Coker}(\alpha) \to \operatorname{Coker}(\beta \circ \alpha)$ induced by $\beta$. -/
def cokerMap : B ⧸ α.range →+ C ⧸ (β.comp α).range :=
  QuotientAddGroup.map _ _ β (by
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl⟩)

/-- The map $\operatorname{Coker}(\beta \circ \alpha) \to \operatorname{Coker}(\beta)$. -/
def cokerCompMap : C ⧸ (β.comp α).range →+ C ⧸ β.range :=
  QuotientAddGroup.map _ _ (AddMonoidHom.id C) (by
    rintro _ ⟨a, rfl⟩
    exact ⟨α a, rfl⟩)

/-- **Lemma 2.2** (pdf p. 118).  For maps $A \xrightarrow{\alpha} B \xrightarrow{\beta} C$ of abelian groups the
sequence
$$0 \to \operatorname{Ker}\alpha \to \operatorname{Ker}\beta\alpha \xrightarrow{\alpha} \operatorname{Ker}\beta
\to \operatorname{Coker}\alpha \xrightarrow{\beta} \operatorname{Coker}\beta\alpha \to \operatorname{Coker}\beta
\to 0$$
is exact.  The six exactness conditions are stated with the maps written out: $\operatorname{Ker}\alpha \subseteq
\operatorname{Ker}\beta\alpha$ is an inclusion, $\operatorname{Ker}\beta\alpha \to \operatorname{Ker}\beta$ is
$\alpha$, $\operatorname{Ker}\beta \to \operatorname{Coker}\alpha$ is the quotient map. -/
@[kb "milne2006ec" "Ch. IV, Lemma 2.2, pdf p. 118"]
theorem lemma_2_2 :
    -- exact at Ker(βα): the kernel of α on Ker(βα) is Ker(α)
    (∀ a : A, β (α a) = 0 → (α a = 0 ↔ a ∈ α.ker)) ∧
    -- exact at Ker(β): the image of Ker(βα) under α is the kernel of Ker(β) → Coker(α)
    (∀ b : β.ker, kerCokerConnecting α β b = 0 ↔ ∃ a : A, β (α a) = 0 ∧ α a = b) ∧
    -- exact at Coker(α)
    (∀ x : B ⧸ α.range, cokerMap α β x = 0 ↔ ∃ b : β.ker, kerCokerConnecting α β b = x) ∧
    -- exact at Coker(βα)
    (∀ y : C ⧸ (β.comp α).range, cokerCompMap α β y = 0 ↔ ∃ x : B ⧸ α.range, cokerMap α β x = y) ∧
    -- surjective onto Coker(β)
    Function.Surjective (cokerCompMap α β) := by
  refine ⟨fun a _ => Iff.rfl, fun b => ?_, fun x => ?_, fun y => ?_, ?_⟩
  · change (QuotientAddGroup.mk (b : B) : B ⧸ α.range) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [ha]; exact b.2, ha⟩
    · rintro ⟨a, -, ha⟩
      exact ⟨a, ha⟩
  · induction x using QuotientAddGroup.induction_on with
    | H b =>
      change (QuotientAddGroup.mk (β b) : C ⧸ (β.comp α).range) = 0 ↔ _
      rw [QuotientAddGroup.eq_zero_iff]
      constructor
      · rintro ⟨a, ha⟩
        refine ⟨⟨b - α a, ?_⟩, ?_⟩
        · change β (b - α a) = 0
          rw [map_sub]
          exact sub_eq_zero.2 ha.symm
        · change (QuotientAddGroup.mk (b - α a) : B ⧸ α.range) = QuotientAddGroup.mk b
          rw [QuotientAddGroup.eq]
          simp
      · rintro ⟨b', hb'⟩
        change (QuotientAddGroup.mk (b' : B) : B ⧸ α.range) = QuotientAddGroup.mk b at hb'
        rw [QuotientAddGroup.eq] at hb'
        obtain ⟨a, ha⟩ := hb'
        refine ⟨a, ?_⟩
        have h0 : β b' = 0 := b'.2
        have : α a = -(b' : B) + b := ha
        change β (α a) = β b
        rw [this, map_add, map_neg, h0]
        simp
  · induction y using QuotientAddGroup.induction_on with
    | H c =>
      change (QuotientAddGroup.mk c : C ⧸ β.range) = 0 ↔ _
      rw [QuotientAddGroup.eq_zero_iff]
      constructor
      · rintro ⟨b, hb⟩
        exact ⟨QuotientAddGroup.mk b, by
          change (QuotientAddGroup.mk (β b) : C ⧸ (β.comp α).range) = _
          rw [hb]⟩
      · rintro ⟨x, hx⟩
        induction x using QuotientAddGroup.induction_on with
        | H b =>
          change (QuotientAddGroup.mk (β b) : C ⧸ (β.comp α).range) = QuotientAddGroup.mk c at hx
          rw [QuotientAddGroup.eq] at hx
          obtain ⟨a, ha⟩ := hx
          refine ⟨b + α a, ?_⟩
          have : β (α a) = -(β b) + c := ha
          rw [map_add, this]
          abel
  · intro y
    induction y using QuotientAddGroup.induction_on with
    | H c => exact ⟨QuotientAddGroup.mk c, rfl⟩

end KerCoker

end NumberFieldKB.MilneEC
