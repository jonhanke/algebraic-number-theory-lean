import NumberFieldKB.MilneEC.Ch5bFrey
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Instances.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Milne, *Elliptic Curves*, Chapter V, Sections 7–9: Frobenius, Tate modules and Galois representations

Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, Section 7 ("The Frobenius map", "The zeta function of an elliptic
curve revisited", pdf pp. 225–228), Section 8 (pp. 230–233) and Section 9 (pp. 234–235).

**Setting.** $G = \mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q)$ with $\bar{\mathbb Q}$ = `AlgebraicClosure ℚ`; it acts on
$E(\bar{\mathbb Q})$ (`galAct`) and on the ring of algebraic integers. A representation of $G_S =
\mathrm{Gal}(K_S/\mathbb Q)$ is treated as a representation of $G$ unramified outside $S$ (the two notions correspond
by restriction along $G \to G_S$, since $K_S$ is the union of the finite extensions unramified outside $S$). Traces
on the Tate module $T_\ell E$ are stated at every finite level $E[\ell^n] = T_\ell E / \ell^n T_\ell E$, as elements
of $\mathbb Z/\ell^n$; a trace on $T_\ell E$ is the unique $\ell$-adic integer with these reductions, so the
statements are equivalent to Milne's.

* Definitions in prose: the Tate module (`tateModuleVb`, p. 227 and p. 231), the Frobenius map $C \to C^{(p)}$ of a
  Weierstrass curve over $\bar{\mathbb F}_p$ (`frobeniusTwist`, `frobeniusPointMap`, p. 225), degree, separable and
  purely inseparable morphisms through function fields (`curveMapDegree`, `IsSeparableCurveMap`,
  `IsPurelyInseparableCurveMap`, p. 226), unramified representations (`IsUnramifiedRepAt`, p. 234), Frobenius
  elements of $G$ (`IsFrobeniusAt`, p. 230), the field $K_S$ (`fieldKS`, p. 231).
* Example 8.2 (`example_8_2`), Definition 8.4 (`IsModularRep`, `IsModularRepModL`, corrected
  `IsModularRepModLChar`), Conjecture 8.5 (`SerreConjecture`, a definition, not assumed).
* Proposition 7.5, Corollary 7.6, Proposition 8.1, Proposition 8.3, Theorem 8.6 and Theorem 9.1 (cited results,
  not proved in this library) are not part of this release.
-/

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Pointwise

noncomputable section

namespace NumberFieldKB.MilneEC.Vb

/-- $\bar{\mathbb Q}$. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

noncomputable instance : DecidableEq Qbar := Classical.decEq _

/-- $G = \mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q)$. -/
abbrev GQ : Type := Qbar ≃ₐ[ℚ] Qbar

/-! ### Points, torsion and the Galois action -/

section Points

variable {K : Type*} [Field K] (W : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L] [DecidableEq L]

/-- $E(L)$ for a Weierstrass curve $E$ over $K$ and an extension $L$ of $K$. -/
abbrev pts : Type _ := (W.toAffine.baseChange L).Point

/-- The torsion subgroup $E(L)_n = \{P \mid nP = 0\}$. -/
def torsionPts (n : ℕ) : AddSubgroup (pts W L) :=
  (nsmulAddMonoidHom n : pts W L →+ pts W L).ker

/-- The action of $\mathrm{Aut}(L/K)$ on $E(L)$, $\sigma(x, y) = (\sigma x, \sigma y)$. -/
instance galAct : MulAction (L ≃ₐ[K] L) (pts W L) where
  smul σ P := Point.map (W' := W.toAffine) (σ : L →ₐ[K] L) P
  one_smul P := by
    exact Point.map_id (W' := W.toAffine) P
  mul_smul σ τ P := by
    exact (Point.map_map (W' := W.toAffine) (τ : L →ₐ[K] L) (σ : L →ₐ[K] L) P).symm

theorem galAct_smul_add (σ : L ≃ₐ[K] L) (P Q : pts W L) : σ • (P + Q) = σ • P + σ • Q :=
  map_add (Point.map (W' := W.toAffine) (σ : L →ₐ[K] L)) P Q

/-- The torsion subgroup is stable under $\mathrm{Aut}(L/K)$. -/
theorem smul_mem_torsionPts (σ : L ≃ₐ[K] L) {n : ℕ} {P : pts W L} (hP : P ∈ torsionPts W L n) :
    σ • P ∈ torsionPts W L n := by
  have h : n • P = 0 := hP
  show n • σ • P = 0
  have := map_nsmul (Point.map (W' := W.toAffine) (σ : L →ₐ[K] L)) n P
  change σ • (n • P) = n • σ • P at this
  rw [← this, h]
  exact map_zero (Point.map (W' := W.toAffine) (σ : L →ₐ[K] L))

/-- The representation of $\mathrm{Aut}(L/K)$ on $E(L)_n$ (by additive endomorphisms). -/
def torsionRep (n : ℕ) : (L ≃ₐ[K] L) →* AddMonoid.End (torsionPts W L n) where
  toFun σ :=
    { toFun := fun P => ⟨σ • (P : pts W L), smul_mem_torsionPts W L σ P.2⟩
      map_zero' := by
        ext
        exact map_zero (Point.map (W' := W.toAffine) (σ : L →ₐ[K] L))
      map_add' := fun P Q => by ext; simp [galAct_smul_add] }
  map_one' := by
    ext P
    exact one_smul _ (P : pts W L)
  map_mul' σ τ := by
    ext P
    exact mul_smul σ τ (P : pts W L)

/-- $E(L)_m$ is a $\mathbb Z/m$-module. -/
instance torsionModule (m : ℕ) [NeZero m] : Module (ZMod m) (torsionPts W L m) :=
  AddCommGroup.zmodModule fun P => by
    ext
    exact P.2

/-- The trace of an additive endomorphism of $E(L)_m$, as a $\mathbb Z/m$-linear map. -/
def torsionTrace (m : ℕ) [NeZero m] (f : torsionPts W L m →+ torsionPts W L m) : ZMod m :=
  LinearMap.trace (ZMod m) _ (f.toZModLinearMap m)

/-- The determinant of an additive endomorphism of $E(L)_m$, as a $\mathbb Z/m$-linear map. -/
def torsionDet (m : ℕ) [NeZero m] (f : torsionPts W L m →+ torsionPts W L m) : ZMod m :=
  LinearMap.det (f.toZModLinearMap m)

end Points

/-- **The Tate module** (Milne, *EC*, V.7, p. 227 and V.8, p. 231, definition in prose; III.3):
$T_\ell A = \varprojlim A_{\ell^n}$ for an abelian group $A$ (for Milne $A = E(k^{\mathrm{al}})$), as the group of
sequences $(x_n)$ with $x_0 = 0$ and $\ell x_{n+1} = x_n$. (The same definition as the Tate module of Chapter III,
`NumberFieldKB.MilneEC.III.tateModule`.) -/
@[kb "milne2006ec" "Ch. V, Section 8 (pdf p. 231): the Tate module (definition in prose)"]
def tateModuleVb (ℓ : ℕ) (A : Type*) [AddCommGroup A] : AddSubgroup (ℕ → A) where
  carrier := {x | x 0 = 0 ∧ ∀ n, ℓ • x (n + 1) = x n}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    exact ⟨by simp [hx0, hy0], fun n => by simp [smul_add, hx n, hy n]⟩
  zero_mem' := ⟨rfl, fun n => by simp⟩
  neg_mem' := by
    rintro x ⟨hx0, hx⟩
    exact ⟨by simp [hx0], fun n => by simp [smul_neg, hx n]⟩

/-! ### The Frobenius map (Section 7) -/

section Frobenius

variable (p : ℕ) [Fact p.Prime]

/-- The algebraic closure $\mathbb F$ of $\mathbb F_p$. -/
abbrev Fpbar (p : ℕ) [Fact p.Prime] : Type := AlgebraicClosure (ZMod p)

noncomputable instance : DecidableEq (Fpbar p) := Classical.decEq _

/-- **The curve $C^{(p)}$** (Milne, *EC*, V.7, p. 225, definition in prose) for a Weierstrass curve $C$ over $\mathbb F$:
the curve whose equation has the coefficients raised to the $p$-th power. -/
def frobeniusTwist (C : WeierstrassCurve (Fpbar p)) : WeierstrassCurve (Fpbar p) :=
  C.map (frobenius (Fpbar p) p)

/-- **The Frobenius map $\varphi_p : C \to C^{(p)}$** (Milne, *EC*, V.7, p. 225, definition in prose) on points:
$(b_0 : b_1 : b_2) \mapsto (b_0^p : b_1^p : b_2^p)$, i.e. $(x, y) \mapsto (x^p, y^p)$ and $O \mapsto O$. -/
def frobeniusPointMap (C : WeierstrassCurve (Fpbar p)) :
    C.toAffine.Point → (frobeniusTwist p C).toAffine.Point
  | .zero => .zero
  | .some (x := x) (y := y) h => .some (x := x ^ p) (y := y ^ p) (by
      exact (WeierstrassCurve.Affine.map_nonsingular (W := C.toAffine) (f := frobenius (Fpbar p) p)
        (frobenius (Fpbar p) p).injective x y).mpr h)

/-- Milne, *EC*, V.7, p. 226 (running text): if $C$ is defined over $\mathbb F_p$ then $C^{(p)} = C$. -/
@[kb "milne2006ec" "Ch. V, Section 7 (pdf p. 226): C^(p) = C for C over F_p"]
theorem frobeniusTwist_baseChange (E : WeierstrassCurve (ZMod p)) :
    frobeniusTwist p (E.baseChange (Fpbar p)) = E.baseChange (Fpbar p) := by
  have key : ∀ a : ZMod p, (algebraMap (ZMod p) (Fpbar p) a) ^ p = algebraMap (ZMod p) (Fpbar p) a := by
    intro a
    rw [← map_pow, ZMod.pow_card]
  unfold frobeniusTwist
  ext <;> simp [WeierstrassCurve.baseChange, WeierstrassCurve.map, frobenius_def, key]

/-- The Frobenius endomorphism $\varphi_p$ of $E(\mathbb F)$ for $E$ over $\mathbb F_p$ (the action of the
Frobenius $x \mapsto x^p$ of $\mathrm{Gal}(\mathbb F/\mathbb F_p)$). -/
def frobPts (E : WeierstrassCurve (ZMod p)) : pts E (Fpbar p) →+ pts E (Fpbar p) :=
  Point.map (W' := E.toAffine) ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (Fpbar p) : _ ≃ₐ[ZMod p] _) :
    Fpbar p →ₐ[ZMod p] Fpbar p)

/-- The restriction of an additive endomorphism of $E(\mathbb F)$ to $E(\mathbb F)_m$. -/
def restrictTorsion {K : Type*} [Field K] (W : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L]
    [DecidableEq L] (m : ℕ) (f : pts W L →+ pts W L) : torsionPts W L m →+ torsionPts W L m :=
  (f.comp (torsionPts W L m).subtype).codRestrict _ fun P => by
    have h : m • (P : pts W L) = 0 := P.2
    show m • f (P : pts W L) = 0
    rw [← map_nsmul, h, map_zero]

/-- The number $N_p$ of points of $E$ over $\mathbb F_p$ (including the point at infinity). -/
def numPoints (E : WeierstrassCurve (ZMod p)) : ℕ :=
  Nat.card E.toAffine.Point

/-- A point map along an algebra endomorphism fixing every element is the identity. -/
theorem map_eq_self_of_forall {K : Type*} [Field K] (W : WeierstrassCurve K) {L : Type*} [Field L] [Algebra K L]
    [DecidableEq L] {f : L →ₐ[K] L} (hf : ∀ x, f x = x) (P : pts W L) :
    Point.map (W' := W.toAffine) f P = P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Point.map_some]
    simp only [hf]

/-- The Frobenius $\varphi_p$ is bijective on $E(\mathbb F)$ (the Frobenius of $\mathbb F$ is an automorphism). -/
theorem frobPts_bijective (E : WeierstrassCurve (ZMod p)) : Function.Bijective (frobPts p E) := by
  set e := (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (Fpbar p) : _ ≃ₐ[ZMod p] _) with he
  have h1 : ∀ P, Point.map (W' := E.toAffine) (e.symm : Fpbar p →ₐ[ZMod p] Fpbar p)
      (frobPts p E P) = P := by
    intro P
    unfold frobPts
    rw [Point.map_map]
    exact map_eq_self_of_forall E (fun x => e.symm_apply_apply x) _
  have h2 : ∀ P, frobPts p E (Point.map (W' := E.toAffine) (e.symm : Fpbar p →ₐ[ZMod p] Fpbar p) P) = P := by
    intro P
    unfold frobPts
    rw [Point.map_map]
    exact map_eq_self_of_forall E (fun x => e.apply_symm_apply x) _
  exact ⟨fun P Q h => by rw [← h1 P, ← h1 Q, h], fun P => ⟨_, h2 P⟩⟩

/-- Cayley-Hamilton for an endomorphism of a free module of rank $2$ over a nontrivial commutative ring. -/
theorem cayley_two {R M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M]
    (h : Module.finrank R M = 2) (F : M →ₗ[R] M) :
    F * F - LinearMap.trace R M F • F + LinearMap.det F • (1 : M →ₗ[R] M) = 0 := by
  have : Module.Finite R M := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq R M h
  have hc := LinearMap.aeval_self_charpoly F
  rw [← LinearMap.charpoly_toMatrix F b, Matrix.charpoly_fin_two] at hc
  rw [← LinearMap.trace_eq_matrix_trace R b F, LinearMap.det_toMatrix b F] at hc
  simp at hc
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] at hc
  simpa [sq] using hc

/-- If $F G = G F = d$ with $d$ invertible and $\det F = d$ on a free module of rank $2$, then
$\operatorname{tr} G = \operatorname{tr} F$ (since $G = \operatorname{tr}(F) - F$ by Cayley-Hamilton). -/
theorem trace_inverse_two {R M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M]
    [Module.Free R M] (h : Module.finrank R M = 2) (u d : R) (hu : u * d = 1) (F G : M →ₗ[R] M)
    (hdet : LinearMap.det F = d) (hFG : F * G = d • 1) (hGF : G * F = d • 1) :
    LinearMap.trace R M G = LinearMap.trace R M F := by
  have : Module.Finite R M := Module.finite_of_finrank_pos (by omega)
  have hCH := cayley_two h F
  rw [hdet] at hCH
  set t := LinearMap.trace R M F with ht
  have h1 : F * (t • (1 : M →ₗ[R] M) - F - G) = 0 := by
    rw [mul_sub, mul_sub, mul_smul_comm, mul_one, hFG]
    have : t • F - F * F - d • (1 : M →ₗ[R] M) = -(F * F - t • F + d • 1) := by abel
    rw [this, hCH, neg_zero]
  have h2 : (u • G) * F = 1 := by
    rw [smul_mul_assoc, hGF, smul_smul, hu, one_smul]
  have h3 : t • (1 : M →ₗ[R] M) - F - G = 0 := by
    calc t • (1 : M →ₗ[R] M) - F - G = ((u • G) * F) * (t • (1 : M →ₗ[R] M) - F - G) := by rw [h2, one_mul]
      _ = (u • G) * (F * (t • (1 : M →ₗ[R] M) - F - G)) := by rw [mul_assoc]
      _ = 0 := by rw [h1, mul_zero]
  have h4 : G = t • (1 : M →ₗ[R] M) - F := (sub_eq_zero.mp h3).symm
  rw [h4, map_sub, map_smul, LinearMap.trace_one, h]
  simp
  ring

end Frobenius

/-- **Degree of a morphism of curves** (Milne, *EC*, V.7, p. 226, definition in prose): for a nonconstant morphism
$\alpha : C \to C'$, given by its $k$-algebra map $\alpha^* : k(C') \to k(C)$ of function fields, $\deg\alpha =
[k(C) : \alpha^* k(C')]$ (Mathlib's `Module.finrank` over the image `AlgHom.fieldRange`). -/
@[kb "milne2006ec" "Ch. V, Section 7 (pdf p. 226): degree of a morphism (definition in prose)"]
def curveMapDegree {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (α : F' →ₐ[k] F) : ℕ :=
  Module.finrank α.fieldRange F

/-- **Separable morphism of curves** (Milne, *EC*, V.7, p. 226, definition in prose): $k(C)$ is separable over
$\alpha^* k(C')$ (Mathlib's `Algebra.IsSeparable`). -/
@[kb "milne2006ec" "Ch. V, Section 7 (pdf p. 226): separable morphism (definition in prose)"]
def IsSeparableCurveMap {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (α : F' →ₐ[k] F) : Prop :=
  Algebra.IsSeparable α.fieldRange F

/-- **Purely inseparable morphism of curves** (Milne, *EC*, V.7, p. 226, definition in prose): $k(C)$ is purely
inseparable over $\alpha^* k(C')$ (Mathlib's `IsPurelyInseparable`). -/
@[kb "milne2006ec" "Ch. V, Section 7 (pdf p. 226): purely inseparable morphism (definition in prose)"]
def IsPurelyInseparableCurveMap {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (α : F' →ₐ[k] F) : Prop :=
  IsPurelyInseparable α.fieldRange F

/-! ### Galois representations (Sections 8 and 9) -/

/-- The prime ideal $p\mathbb Z$. -/
abbrev primeIdeal (p : ℕ) : Ideal ℤ := Ideal.span {(p : ℤ)}

/-- $p$ is **unramified** in an algebraic extension $K \subset \bar{\mathbb Q}$: every prime of the integral closure
of $\mathbb Z$ in $K$ over $p$ is unramified (Mathlib's `Algebra.IsUnramifiedIn`; for a number field this is
"no $e_{\mathfrak p} > 1$", Milne, p. 230 and `Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one`). -/
def IsUnramifiedInField (K : IntermediateField ℚ Qbar) (p : ℕ) : Prop :=
  Algebra.IsUnramifiedIn (integralClosure ℤ K) (primeIdeal p)

/-- **Unramified representation** (Milne, *EC*, V.9, p. 234, definition in prose): $\rho : G \to \mathrm{Aut}(M)$ is
unramified at $p$ if $p$ is unramified in the fixed field $\bar{\mathbb Q}^H$ of its kernel $H$. Stated for any
homomorphism to a monoid (for Milne the target is $\mathrm{Aut}(M)$, $M$ finite, or $\mathrm{GL}_2$). -/
@[kb "milne2006ec" "Ch. V, Section 9 (pdf p. 234): unramified representation (definition in prose)"]
def IsUnramifiedRepAt {M : Type*} [Monoid M] (ρ : GQ →* M) (p : ℕ) : Prop :=
  IsUnramifiedInField (IntermediateField.fixedField ρ.ker) p

/-- **Frobenius element at $p$** in $G$ (Milne, *EC*, V.8, pp. 230–231, definition in prose): $\sigma \in G$ is a
Frobenius element at $p$ if for some prime $\mathfrak P$ of the ring of algebraic integers over $p$,
$\sigma\mathfrak P = \mathfrak P$ and $\sigma x \equiv x^p \pmod{\mathfrak P}$ for all algebraic integers $x$ (Mathlib's
`IsArithFrobAt`; it implies $\sigma\mathfrak P = \mathfrak P$). Well defined up to conjugation and inertia. -/
@[kb "milne2006ec" "Ch. V, Section 8 (pdf p. 231): Frobenius element (definition in prose)"]
def IsFrobeniusAt (σ : GQ) (p : ℕ) : Prop :=
  ∃ Q : Ideal (integralClosure ℤ Qbar), Q.IsPrime ∧ Q.LiesOver (primeIdeal p) ∧ IsArithFrobAt ℤ σ Q

/-- **The field $K_S$** (Milne, *EC*, V.8, p. 231): the union (compositum) of all subfields of $\bar{\mathbb Q}$ of
finite degree over $\mathbb Q$ that are unramified outside the finite set $S$ of primes. -/
@[kb "milne2006ec" "Ch. V, Section 8 (pdf p. 231): the field K_S (definition in prose)"]
def fieldKS (S : Finset ℕ) : IntermediateField ℚ Qbar :=
  ⨆ K : {K : IntermediateField ℚ Qbar // FiniteDimensional ℚ K ∧ ∀ p : ℕ, p.Prime → p ∉ S → IsUnramifiedInField K p},
    K.1

/-- The set $S = \{p \mid E \text{ has bad reduction at } p\} \cup \{\ell\}$ of Proposition 8.1, as a predicate. -/
def InBadSet (E : WeierstrassCurve ℚ) (ℓ p : ℕ) : Prop :=
  p = ℓ ∨ ∃ _ : Fact p.Prime, ¬ HasGoodReductionAt E p

/-- The field generated over $\mathbb Q$ by the coordinates of a set of points of $E(\bar{\mathbb Q})$. -/
def coordField (E : WeierstrassCurve ℚ) (T : Set (pts E Qbar)) : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ {c | ∃ (x y : Qbar) (h : (E.toAffine.baseChange Qbar).Nonsingular x y),
    (Point.some (x := x) (y := y) h : pts E Qbar) ∈ T ∧ (c = x ∨ c = y)}

/-- The curve $Y^2 = X^3 + aX + b$. -/
def shortCurve (a b : ℚ) : WeierstrassCurve ℚ := ⟨0, 0, 0, a, b⟩

/-- A point $(x, y) \ne O$ of $Y^2 = X^3 + aX + b$ over $\bar{\mathbb Q}$ has order dividing $2$ if and only if
$y = 0$. -/
theorem some_mem_torsionPts_two_iff (a b : ℚ) (x y : Qbar)
    (h : ((shortCurve a b).toAffine.baseChange Qbar).Nonsingular x y) :
    (Point.some (x := x) (y := y) h : pts (shortCurve a b) Qbar) ∈ torsionPts (shortCurve a b) Qbar 2 ↔
      y = 0 := by
  show 2 • (Point.some (x := x) (y := y) h : pts (shortCurve a b) Qbar) = 0 ↔ y = 0
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq]
  simp [WeierstrassCurve.Affine.negY, shortCurve, WeierstrassCurve.baseChange]
  constructor
  · intro hy
    have h2 : (2 : Qbar) * y = 0 := by linear_combination hy
    exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  · intro hy
    rw [hy, neg_zero]

/-- **Example 8.2, first assertion** (Milne, *EC*, V, Example 8.2, p. 231): the smallest field containing the
coordinates of the points of order $2$ of $E : Y^2Z = X^3 + aXZ^2 + bZ^3$ is the splitting field of $X^3 + aX + b$
(the subfield of $\bar{\mathbb Q}$ generated by its roots). -/
@[kb "milne2006ec" "Ch. V, Example 8.2 (pdf p. 231): 2-torsion field = splitting field"]
theorem example_8_2 (a b : ℚ) :
    coordField (shortCurve a b) (torsionPts (shortCurve a b) Qbar 2) =
      IntermediateField.adjoin ℚ ((Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b).rootSet Qbar) := by
  have hroot : ∀ r : Qbar, r ∈ (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b).rootSet Qbar ↔
      r ^ 3 + (a : Qbar) * r + (b : Qbar) = 0 := by
    intro r
    rw [Polynomial.mem_rootSet]
    constructor
    · rintro ⟨-, h⟩
      simpa using h
    · intro h
      refine ⟨?_, by simpa using h⟩
      intro h0
      have := congrArg (Polynomial.coeff · 3) h0
      simp at this
  have hEq : ∀ x y : Qbar, ((shortCurve a b).toAffine.baseChange Qbar).Equation x y ↔
      y ^ 2 = x ^ 3 + (a : Qbar) * x + (b : Qbar) := by
    intro x y
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [shortCurve, WeierstrassCurve.baseChange]
  unfold coordField
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.2
    rintro c ⟨x, y, h, hT, rfl | rfl⟩
    · have hy := (some_mem_torsionPts_two_iff a b c y h).1 hT
      have heq := (hEq c y).1 h.1
      rw [hy] at heq
      apply IntermediateField.subset_adjoin
      rw [hroot]
      linear_combination -heq
    · have hy := (some_mem_torsionPts_two_iff a b x c h).1 hT
      rw [hy]
      exact zero_mem _
  · apply IntermediateField.adjoin_le_iff.2
    intro r hr
    rw [SetLike.mem_coe]
    have heq := (hroot r).1 hr
    by_cases hns : ((shortCurve a b).toAffine.baseChange Qbar).Nonsingular r 0
    · apply IntermediateField.subset_adjoin
      exact ⟨r, 0, hns, (some_mem_torsionPts_two_iff a b r 0 hns).2 rfl, Or.inl rfl⟩
    · have h3 : 3 * r ^ 2 + (a : Qbar) = 0 := by
        by_contra hne
        apply hns
        rw [WeierstrassCurve.Affine.nonsingular_iff, hEq]
        refine ⟨by linear_combination -heq, Or.inl ?_⟩
        simpa [shortCurve, WeierstrassCurve.baseChange, eq_comm] using hne
      by_cases ha : a = 0
      · subst ha
        have : r = 0 := by
          have : r ^ 2 = 0 := by
            have h3' : 3 * r ^ 2 = 0 := by simpa using h3
            simpa using h3'
          exact pow_eq_zero_iff (two_ne_zero) |>.1 this
        rw [this]
        exact zero_mem _
      · have h4 : (2 * a : Qbar) * r + 3 * b = 0 := by linear_combination 3 * heq - r * h3
        have ha' : (a : Qbar) ≠ 0 := by exact_mod_cast ha
        have : r = algebraMap ℚ Qbar (-3 * b / (2 * a)) := by
          simp only [map_div₀, map_mul, map_neg, map_ofNat, eq_ratCast]
          have h2a : (2 : Qbar) * a ≠ 0 := mul_ne_zero two_ne_zero ha'
          field_simp
          linear_combination h4
        rw [this]
        exact IntermediateField.algebraMap_mem _ _

/-- $a_p = p + 1 - N_p(E)$ for an elliptic curve $E$ over $\mathbb Q$, with $N_p$ the number of points of the reduction
of the minimal model at $p$ over the residue field $\mathbb F_p$ of $\mathbb Z_p$ (as in Mathlib's
`WeierstrassCurve.localPolynomial`). -/
def apAt (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : ℤ :=
  p + 1 - Nat.card (((E.baseChange ℚ_[p]).minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point

/-- A representation of $G$ that factors through $G_S$: continuous and unramified at every prime $p \notin S$. -/
def IsGSRep {M : Type*} [Monoid M] [TopologicalSpace M] (S : Finset ℕ) (ρ : GQ →* M) : Prop :=
  Continuous ρ ∧ ∀ p : ℕ, p.Prime → p ∉ S → IsUnramifiedRepAt ρ p

/-- **Modular $\ell$-adic representation** (Milne, *EC*, V, Definition 8.4, p. 232): $\rho : G_S \to
\mathrm{GL}_2(\mathbb Z_\ell)$ is modular if $\mathrm{Tr}(\rho(F_p)) \in \mathbb Z$ for all $p \notin S$ and there is a
cusp form $f = \sum c(n) q^n \in S_{2k}(\Gamma_0(N))$, for some $k$ and $N$, with $\mathrm{Tr}(\rho(F_p)) = c(p)$ for all
$p \notin S$. -/
@[kb "milne2006ec" "Ch. V, Definition 8.4 (pdf p. 232)"]
def IsModularRep (ℓ : ℕ) [Fact ℓ.Prime] (S : Finset ℕ) (ρ : GQ →* GL (Fin 2) ℤ_[ℓ]) : Prop :=
  ∃ a : ℕ → ℤ, (∀ p : ℕ, p.Prime → p ∉ S → ∀ σ : GQ, IsFrobeniusAt σ p →
      Matrix.trace (ρ σ : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) = a p) ∧
    ∃ (k : ℤ) (N : ℕ) (_ : NeZero N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) (2 * k)),
      ∀ p : ℕ, p.Prime → p ∉ S → (UpperHalfPlane.qExpansion 1 f).coeff p = a p

/-- **Modular mod $\ell$ representation, as defined by Milne** (Milne, *EC*, V.8, p. 232, after Definition 8.4):
$\bar\rho : G_S \to \mathrm{GL}_2(\mathbb F_\ell)$ is modular if there is a cusp form $f = \sum c(n)q^n \in
S_{2k}(\Gamma_0(N))$ with $\mathrm{Tr}(\bar\rho(F_p)) \equiv c(p) \bmod \ell$ for all $p \notin S$ (the congruence
read for integer $c(p)$). **Correction**: with forms on $\Gamma_0(N)$ only, the
determinant of $\bar\rho$ is forced to be a power of the cyclotomic character mod $\ell$, so Conjecture 8.5 and
Theorem 8.6 are false for this notion; they are stated with `IsModularRepModLChar`. -/
@[kb "milne2006ec" "Ch. V, Section 8 (pdf p. 232): modular mod ℓ representation (definition in prose)"]
def IsModularRepModL (ℓ : ℕ) [Fact ℓ.Prime] (S : Finset ℕ) (ρ : GQ →* GL (Fin 2) (ZMod ℓ)) : Prop :=
  ∃ (k : ℤ) (N : ℕ) (_ : NeZero N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) (2 * k)) (a : ℕ → ℤ),
    ∀ p : ℕ, p.Prime → p ∉ S → (UpperHalfPlane.qExpansion 1 f).coeff p = a p ∧
      ∀ σ : GQ, IsFrobeniusAt σ p → Matrix.trace (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = (a p : ZMod ℓ)

/-- **Modular mod $\ell$ representation, standard notion** (Serre 1987; the notion of Conjecture 8.5 and
Theorem 8.6, correcting Milne's, see `IsModularRepModL`): there are a weight $k$, a level $N$, a cusp form
$f = \sum c(n) q^n$ of weight $k$ for $\Gamma_1(N)$ whose coefficients $c(p)$, $p \notin S$, are algebraic
integers, and a reduction $\pi$ of the algebraic integers modulo a prime above $\ell$ (a ring homomorphism to
$\bar{\mathbb F}_\ell$) with $\pi(c(p)) = \mathrm{Tr}(\bar\rho(F_p))$ for all $p \notin S$. -/
def IsModularRepModLChar (ℓ : ℕ) [Fact ℓ.Prime] (S : Finset ℕ) (ρ : GQ →* GL (Fin 2) (ZMod ℓ)) : Prop :=
  ∃ (k : ℤ) (N : ℕ) (_ : NeZero N) (f : CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (π : integralClosure ℤ ℂ →+* AlgebraicClosure (ZMod ℓ)), ∀ p : ℕ, p.Prime → p ∉ S →
      ∃ h : (UpperHalfPlane.qExpansion 1 f).coeff p ∈ integralClosure ℤ ℂ, ∀ σ : GQ, IsFrobeniusAt σ p →
        π ⟨_, h⟩ = algebraMap (ZMod ℓ) (AlgebraicClosure (ZMod ℓ)) (Matrix.trace (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)))

/-- A complex conjugation in $G$: the restriction of complex conjugation along an embedding
$\bar{\mathbb Q} \hookrightarrow \mathbb C$. -/
def IsComplexConjugation (c : GQ) : Prop :=
  ∃ ι : Qbar →ₐ[ℚ] ℂ, ∀ x, ι (c x) = starRingEnd ℂ (ι x)

/-- **Odd** (Milne, *EC*, V.8, p. 232): $\det\bar\rho(c) = -1$ for complex conjugation $c$. -/
def IsOddRep {ℓ : ℕ} (ρ : GQ →* GL (Fin 2) (ZMod ℓ)) : Prop :=
  ∀ c : GQ, IsComplexConjugation c → Matrix.det (ρ c : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = -1

/-- **Irreducible** (Milne, *EC*, V.8, p. 232): no one-dimensional subspace of $\mathbb F_\ell^2$ is stable under
the action of $G$. -/
def IsIrreducibleRep {ℓ : ℕ} (ρ : GQ →* GL (Fin 2) (ZMod ℓ)) : Prop :=
  ∀ v : Fin 2 → ZMod ℓ, v ≠ 0 → ∃ σ : GQ,
    (ρ σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).mulVec v ∉ Submodule.span (ZMod ℓ) {v}

/-- **Conjecture 8.5 (Serre)** (Milne, *EC*, V, Conjecture 8.5, p. 232; proved by Khare and Wintenberger, not used):
every odd irreducible representation $\bar\rho : G_S \to \mathrm{GL}_2(\mathbb F_\ell)$ is modular (for the standard
notion `IsModularRepModLChar`; for Milne's literal notion the statement is false, see `IsModularRepModL`). A
definition (the proposition), not an assumption. -/
@[kb "milne2006ec" "Ch. V, Conjecture 8.5 (Serre; the statement)"]
def SerreConjecture : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (S : Finset ℕ) (ρ : GQ →* GL (Fin 2) (ZMod ℓ)), IsGSRep S ρ → IsOddRep ρ →
    IsIrreducibleRep ρ → IsModularRepModLChar ℓ S ρ

end NumberFieldKB.MilneEC.Vb
