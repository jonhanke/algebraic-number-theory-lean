import NumberFieldKB.MilneEC.Ch5bGalois
import NumberFieldKB.MilneEC.Ch2Iso
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Milne, *Elliptic Curves*, Chapter V, §2: the set $\mathcal E_0(N)(k)$ of pairs $(E, S)$

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §2, before Theorem 2.7 (pdf p. 196).

Milne: for a field $k$, $\mathcal E_0(N)(k)$ is the set of isomorphism classes of pairs $(E, S)$ with $E$ an
elliptic curve over $k$ and $S$ a cyclic subgroup of $E(k^{\mathrm{al}})$ of order $N$ stable under
$\mathrm{Gal}(k^{\mathrm{al}}/k)$; $(E, S) \cong (E', S')$ when an isomorphism $E \to E'$ over $k$ carries $S$ onto
$S'$.

**Formalization.** An elliptic curve over $k$ is a Weierstrass curve with nonzero discriminant (Mathlib's
`WeierstrassCurve.IsElliptic`); the isomorphisms over $k$ between Weierstrass curves are the changes of variables
$C$ with $C \cdot E = E'$ (Milne, Chapter II, Theorem 2.4), acting on points over $k^{\mathrm{al}}$ by the group
isomorphism `NumberFieldKB.MilneEC.II.variableChangePointEquiv` (base changed to $k^{\mathrm{al}}$). $k^{\mathrm{al}}$
is `AlgebraicClosure k` and $\mathrm{Gal}(k^{\mathrm{al}}/k)$ its group of $k$-automorphisms, acting on points by
`NumberFieldKB.MilneEC.Vb.galAct`. `CyclicPair.Iso` is proved to be an equivalence relation
(`CyclicPair.iso_equivalence`) and `E0 k N` is the quotient.

Theorem 2.7 itself (a map $\mathcal E_0(N)(k) \to Y_0(N)(k)$, bijective for $k$ algebraically closed) is not
formalized: it needs $X_0(N)$ as a curve over $\mathbb Q$ and its points over every field of characteristic zero.
The complex statement $\Gamma_0(N)\backslash\mathbb H \cong \{(\Lambda, S)\}$ (pdf p. 195) is
`NumberFieldKB.MilneEC.V.gamma0_orbits_eq_lattice_subgroup_pairs`.
-/

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace NumberFieldKB.MilneEC.Vb

variable (k : Type*) [Field k] (N : ℕ)

noncomputable instance instDecidableEqAlgebraicClosure : DecidableEq (AlgebraicClosure k) := Classical.decEq _

/-- A pair $(E, S)$ (Milne, *EC*, V.2, pdf p. 196): an elliptic curve $E$ over $k$ and a cyclic subgroup
$S \subseteq E(k^{\mathrm{al}})$ of order $N$ stable under $\mathrm{Gal}(k^{\mathrm{al}}/k)$. -/
structure CyclicPair where
  /-- The elliptic curve. -/
  E : WeierstrassCurve k
  isElliptic : E.IsElliptic
  /-- The subgroup of $E(k^{\mathrm{al}})$. -/
  S : AddSubgroup (pts E (AlgebraicClosure k))
  isAddCyclic : IsAddCyclic S
  card_eq : Nat.card S = N
  galois_stable : ∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, ∀ P ∈ S, σ • P ∈ S

/-- Transport of points along an equality of Weierstrass curves (coordinates unchanged). -/
def pointCongr {K : Type*} [Field K] [DecidableEq K] {W W' : WeierstrassCurve K} (h : W = W') :
    W.toAffine.Point ≃+ W'.toAffine.Point := by
  subst h; exact AddEquiv.refl _

theorem pointCongr_some {K : Type*} [Field K] [DecidableEq K] {W W' : WeierstrassCurve K} (h : W = W')
    {x y : K} (hP : W.toAffine.Nonsingular x y) (hQ : W'.toAffine.Nonsingular x y) :
    pointCongr h (Affine.Point.some x y hP) = Affine.Point.some x y hQ := by
  subst h; rfl

variable {k}

/-- Base change of the equation $C \cdot E = E'$. -/
theorem transportPts_curve {E E' : WeierstrassCurve k} (C : VariableChange k) (h : C • E = E') :
    (C.baseChange (AlgebraicClosure k)) • (E.baseChange (AlgebraicClosure k)) =
      E'.baseChange (AlgebraicClosure k) := by
  unfold WeierstrassCurve.baseChange VariableChange.baseChange
  rw [map_variableChange, h]

/-- The isomorphism $E(k^{\mathrm{al}}) \to E'(k^{\mathrm{al}})$ of the change of variables $C$ over $k$ with
$C \cdot E = E'$ (the inverse of `variableChangePointEquiv`, which goes from $C \cdot E$ to $E$, base changed to
$k^{\mathrm{al}}$). On points: $(x, y) \mapsto (u^{-2}(x - r), u^{-3}(y - s(x - r) - t))$. -/
def transportPts {E E' : WeierstrassCurve k} (C : VariableChange k) (h : C • E = E') :
    pts E (AlgebraicClosure k) ≃+ pts E' (AlgebraicClosure k) :=
  (II.variableChangePointEquiv (E.baseChange (AlgebraicClosure k))
    (C.baseChange (AlgebraicClosure k))).symm.trans (pointCongr (transportPts_curve C h))

theorem transportPts_some {E E' : WeierstrassCurve k} (C : VariableChange k) (h : C • E = E')
    {x y : AlgebraicClosure k} (hP : (E.toAffine.baseChange (AlgebraicClosure k)).Nonsingular x y)
    (hQ : (E'.toAffine.baseChange (AlgebraicClosure k)).Nonsingular
      ((algebraMap k (AlgebraicClosure k) (C.u : k))⁻¹ ^ 2 * (x - algebraMap k _ C.r))
      ((algebraMap k (AlgebraicClosure k) (C.u : k))⁻¹ ^ 3 *
        (y - algebraMap k _ C.s * (x - algebraMap k _ C.r) - algebraMap k _ C.t))) :
    transportPts C h (Affine.Point.some x y hP) = Affine.Point.some _ _ hQ := by
  exact pointCongr_some _ _ hQ

theorem transportPts_zero {E E' : WeierstrassCurve k} (C : VariableChange k) (h : C • E = E') :
    transportPts C h 0 = 0 := map_zero _

theorem transportPts_some_ex {E E' : WeierstrassCurve k} (C : VariableChange k) (h : C • E = E')
    {x y : AlgebraicClosure k} (hP : (E.toAffine.baseChange (AlgebraicClosure k)).Nonsingular x y) :
    ∃ hQ : (E'.toAffine.baseChange (AlgebraicClosure k)).Nonsingular
      ((algebraMap k (AlgebraicClosure k) (C.u : k))⁻¹ ^ 2 * (x - algebraMap k _ C.r))
      ((algebraMap k (AlgebraicClosure k) (C.u : k))⁻¹ ^ 3 *
        (y - algebraMap k _ C.s * (x - algebraMap k _ C.r) - algebraMap k _ C.t)),
      transportPts C h (Affine.Point.some x y hP) = Affine.Point.some _ _ hQ := by
  have hn := II.variableChange_nonsingular_inv (E.baseChange (AlgebraicClosure k))
    (C.baseChange (AlgebraicClosure k)) hP
  have hn' := (transportPts_curve C h) ▸ hn
  exact ⟨hn', transportPts_some C h hP hn'⟩

theorem transportPts_congr {E E' : WeierstrassCurve k} {C D : VariableChange k} (hCD : C = D)
    (h : C • E = E') (h' : D • E = E') (P : pts E (AlgebraicClosure k)) :
    transportPts C h P = transportPts D h' P := by
  subst hCD; rfl

theorem transportPts_one {E : WeierstrassCurve k} (h : (1 : VariableChange k) • E = E)
    (P : pts E (AlgebraicClosure k)) : transportPts 1 h P = P := by
  rcases P with _ | ⟨x, y, hP⟩
  · exact transportPts_zero _ _
  · obtain ⟨hQ, e⟩ := transportPts_some_ex (1 : VariableChange k) h hP
    rw [e]
    apply II.point_some_congr <;> simp [VariableChange.one_def]

theorem transportPts_comp {E E' E'' : WeierstrassCurve k} (C C' : VariableChange k)
    (h : C • E = E') (h' : C' • E' = E'') (h'' : (C' * C) • E = E'')
    (P : pts E (AlgebraicClosure k)) :
    transportPts (C' * C) h'' P = transportPts C' h' (transportPts C h P) := by
  have hu : (algebraMap k (AlgebraicClosure k) (C.u : k)) ≠ 0 := by
    simp
  have hu' : (algebraMap k (AlgebraicClosure k) (C'.u : k)) ≠ 0 := by
    simp
  rcases P with _ | ⟨x, y, hP⟩
  · change transportPts _ _ 0 = transportPts _ _ (transportPts _ _ 0)
    simp only [transportPts_zero]
  · obtain ⟨h1, e1⟩ := transportPts_some_ex C h hP
    obtain ⟨h2, e2⟩ := transportPts_some_ex C' h' h1
    obtain ⟨h3, e3⟩ := transportPts_some_ex (C' * C) h'' hP
    rw [e1, e2, e3]
    apply II.point_some_congr
    · simp only [VariableChange.mul_def, Units.val_mul, map_mul, map_add, map_pow]
      field_simp
      ring
    · simp only [VariableChange.mul_def, Units.val_mul, map_mul, map_add, map_pow]
      field_simp
      ring

variable (k)

/-- Milne's isomorphism of pairs: $(E, S) \cong (E', S')$ if a change of variables $C$ over $k$ with
$C \cdot E = E'$ carries $S$ onto $S'$. -/
def CyclicPair.Iso (P Q : CyclicPair k N) : Prop :=
  ∃ (C : VariableChange k) (h : C • P.E = Q.E), Q.S = P.S.map (transportPts C h).toAddMonoidHom

/-- Isomorphism of pairs is an equivalence relation. -/
theorem CyclicPair.iso_equivalence : Equivalence (CyclicPair.Iso k N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro P
    refine ⟨1, one_smul _ _, ?_⟩
    have : (transportPts (1 : VariableChange k) (one_smul _ P.E)).toAddMonoidHom =
        AddMonoidHom.id _ := by
      ext Q; exact transportPts_one _ Q
    rw [this, AddSubgroup.map_id]
  · rintro P Q ⟨C, h, hS⟩
    have h' : C⁻¹ • Q.E = P.E := by rw [← h, inv_smul_smul]
    refine ⟨C⁻¹, h', ?_⟩
    rw [hS, AddSubgroup.map_map]
    have : (transportPts C⁻¹ h').toAddMonoidHom.comp (transportPts C h).toAddMonoidHom =
        AddMonoidHom.id _ := by
      ext Q
      have h1 : (C⁻¹ * C) • P.E = P.E := by rw [inv_mul_cancel, one_smul]
      exact (transportPts_comp C C⁻¹ h h' h1 Q).symm.trans
        ((transportPts_congr (inv_mul_cancel C) h1 (one_smul _ _) Q).trans (transportPts_one _ Q))
    rw [this, AddSubgroup.map_id]
  · rintro P Q R ⟨C, h, hS⟩ ⟨C', h', hS'⟩
    have h'' : (C' * C) • P.E = R.E := by rw [mul_smul, h, h']
    refine ⟨C' * C, h'', ?_⟩
    rw [hS', hS, AddSubgroup.map_map]
    congr 1
    ext Q
    exact (transportPts_comp C C' h h' h'' Q).symm

/-- The setoid of pairs up to isomorphism. -/
def cyclicPairSetoid : Setoid (CyclicPair k N) := ⟨CyclicPair.Iso k N, CyclicPair.iso_equivalence k N⟩

/-- **$\mathcal E_0(N)(k)$** (Milne, *EC*, V.2, pdf p. 196, definition in prose): the set of isomorphism classes of
pairs $(E, S)$, $E$ an elliptic curve over $k$, $S \subseteq E(k^{\mathrm{al}})$ cyclic of order $N$ and stable under
$\mathrm{Gal}(k^{\mathrm{al}}/k)$. -/
@[kb "milne2006ec" "Ch. V, §2, the set E_0(N)(k) of pairs (E, S), pdf p. 196"]
def E0 : Type _ := Quotient (cyclicPairSetoid k N)

/-- The transport of points along a change of variables over $k$ commutes with the Galois action (so the image of
a Galois-stable subgroup is Galois stable). -/
theorem transportPts_galois {E E' : WeierstrassCurve k} (C : VariableChange k) (h : C • E = E')
    (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (P : pts E (AlgebraicClosure k)) :
    transportPts C h (σ • P) = σ • transportPts C h P := by
  rcases P with _ | ⟨x, y, hP⟩
  · change transportPts C h 0 = σ • transportPts C h 0
    rw [transportPts_zero]; rfl
  · have hs : σ • (Affine.Point.some x y hP : pts E (AlgebraicClosure k)) =
        Affine.Point.some (σ x) (σ y) ((E.toAffine.baseChange_nonsingular
          (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k).injective ..).mpr hP) := rfl
    obtain ⟨h1, e1⟩ := transportPts_some_ex C h hP
    obtain ⟨h2, e2⟩ := transportPts_some_ex C h
      ((E.toAffine.baseChange_nonsingular
          (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k).injective ..).mpr hP)
    rw [hs, e1]
    refine e2.trans ?_
    show _ = Affine.Point.some (σ _) (σ _) _
    apply II.point_some_congr
    · simp [AlgEquiv.commutes]
    · simp [AlgEquiv.commutes]

end NumberFieldKB.MilneEC.Vb
