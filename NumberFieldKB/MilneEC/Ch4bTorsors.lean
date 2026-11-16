import Mathlib.Algebra.Torsor.Defs
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Topology.Algebra.Group.Defs
import QuadFormsKB.Citation

/-!
# Milne, Elliptic Curves, Chapter IV §7: principal homogeneous spaces and their classification

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Section 7 ("Geometric
interpretation of the cohomology groups"), pdf pp. 142–146.  Locators give the pdf page of the text `ectext6`
(printed page = pdf page − 8).

## Principal homogeneous spaces of sets (pdf p. 142)
Milne's principal homogeneous space for a commutative group $A$ (a nonempty right $A$-set on which $A$ acts simply
transitively) is Mathlib's `AddTorsor A W`.  Example 7.1 and statements 7.2, 7.3 are proved below.

## Principal homogeneous spaces of curves, at the level of points (pdf pp. 143–146)
Milne's principal homogeneous space for an elliptic curve $E$ over $k$ is a curve $W$ over $k$ with a regular simply
transitive action of $E$.  Mathlib has no curves over $k$ as varieties, so we formalize what Milne's proofs of
Theorems 7.8 and 7.10 actually use: the **Galois set** $W(k^{\mathrm{al}})$, an $E(k^{\mathrm{al}})$-torsor with a
compatible continuous action of $\Gamma = \operatorname{Gal}(k^{\mathrm{al}}/k)$ (Milne's $\sigma(w + P) =
\sigma w + \sigma P$, pdf p. 143).  **Deviation recorded:** by Galois descent (Milne, Chapter I, 5.3–5.5, used in the
last step of his proof of 7.8) a curve over $k$ is the same as a curve over $k^{\mathrm{al}}$ with a continuous descent
system; that geometric step is *not* formalized here, so Theorem 7.8 is proved for Galois sets: isomorphism classes of
Galois-set principal homogeneous spaces correspond bijectively to $H^1(\Gamma, A)$.  Everything is stated for an
arbitrary topological group $\Gamma$ acting on a discrete abelian group $A$ (stabilizers open), which covers
$A = E(k^{\mathrm{al}})$ with the Krull topology on $\Gamma$.

$H^1(\Gamma, A)$ is Milne's continuous crossed homomorphisms modulo principal crossed homomorphisms (pdf pp. 111,
114): `ContH1 Γ A`.  Crossed homomorphisms are Mathlib's `groupCohomology.IsCocycle₁`
($f(\sigma\tau) = \sigma f(\tau) + f(\sigma)$); continuity, for the discrete group $A$, is `IsLocallyConstant`.

## Proved
* `example_7_1`, `statement_7_2_a`, `statement_7_2_b`, `statement_7_3_a`, `statement_7_3_b`.
* `GaloisTorsor.cls` (the class $[f]$ of $W$, pdf p. 143) and `theorem_7_8`: well defined, injective and surjective on
  isomorphism classes, the trivial space going to $0$.
* `statement_7_6` (trivial if and only if $W(k) \neq \emptyset$), `statement_7_7` (automorphisms are translations by
  $E(k)$).
* `theorem_7_10`: $n$-coverings modulo isomorphism correspond to $H^1(\Gamma, A_n)$.
-/

open groupCohomology

universe u

namespace NumberFieldKB.MilneEC

/-! ## Principal homogeneous spaces of sets (pdf p. 142) -/

section Sets

variable {A : Type*} [AddCommGroup A]

/-- **Example 7.1(a)** (pdf p. 142): addition $A \times A \to A$ makes $A$ a principal homogeneous space for $A$, the
trivial one (Mathlib's `AddGroup.instAddTorsor`). -/
@[kb "milne2006ec" "Ch. IV, Example 7.1, pdf p. 142"]
theorem example_7_1 (w₁ w₂ : A) : ∃! a : A, a +ᵥ w₁ = w₂ :=
  ⟨w₂ - w₁, by simp [vadd_eq_add], fun a ha => by simp [vadd_eq_add, ← ha]⟩

variable {W W' : Type*} [AddTorsor A W] [AddTorsor A W']

/-- A morphism of principal homogeneous spaces for $A$ (pdf p. 142) is a map of $A$-sets. -/
def IsTorsorHom (φ : W → W') : Prop := ∀ (a : A) (w : W), φ (a +ᵥ w) = a +ᵥ φ w

/-- **7.2(a)** (pdf p. 142): for $w_0 \in W$, $w_0' \in W'$ there is a unique morphism $W \to W'$ sending $w_0$ to
$w_0'$. -/
@[kb "milne2006ec" "Ch. IV, 7.2(a), pdf p. 142"]
theorem statement_7_2_a (w₀ : W) (w₀' : W') :
    ∃! φ : W → W', IsTorsorHom (A := A) φ ∧ φ w₀ = w₀' := by
  refine ⟨fun w => (w -ᵥ w₀) +ᵥ w₀', ⟨fun a w => ?_, by simp⟩, fun ψ ⟨hψ, h0⟩ => funext fun w => ?_⟩
  · simp [vadd_vsub_assoc, add_vadd]
  · rw [← vsub_vadd w w₀, hψ, h0, vadd_vsub]

/-- **7.2(b)** (pdf p. 142): every morphism of principal homogeneous spaces is an isomorphism (bijective, with inverse
a morphism). -/
@[kb "milne2006ec" "Ch. IV, 7.2(b), pdf p. 142"]
theorem statement_7_2_b {φ : W → W'} (hφ : IsTorsorHom (A := A) φ) :
    ∃ ψ : W' → W, IsTorsorHom (A := A) ψ ∧ Function.LeftInverse ψ φ ∧ Function.RightInverse ψ φ := by
  obtain ⟨w₀⟩ := (inferInstance : Nonempty W)
  refine ⟨fun w' => (w' -ᵥ φ w₀) +ᵥ w₀, fun a w' => ?_, fun w => ?_, fun w' => ?_⟩
  · simp [vadd_vsub_assoc, add_vadd]
  · have h : φ w = (w -ᵥ w₀) +ᵥ φ w₀ := by
      conv_lhs => rw [← vsub_vadd w w₀]
      exact hφ _ _
    show (φ w -ᵥ φ w₀) +ᵥ w₀ = w
    rw [h, vadd_vsub, vsub_vadd]
  · show φ ((w' -ᵥ φ w₀) +ᵥ w₀) = w'
    rw [hφ, vsub_vadd]

/-- **7.3(a)** (pdf p. 142): for $w_0 \in W$ there is a unique morphism $A \to W$ sending $0$ to $w_0$, namely
$a \mapsto w_0 + a$. -/
@[kb "milne2006ec" "Ch. IV, 7.3(a), pdf p. 142"]
theorem statement_7_3_a (w₀ : W) :
    ∃! φ : A → W, IsTorsorHom (A := A) φ ∧ φ 0 = w₀ :=
  statement_7_2_a (A := A) (0 : A) w₀

/-- **7.3(b)** (pdf p. 142): $a \in A$ defines the automorphism $w \mapsto w + a$, and every automorphism is of this form
for a unique $a$; hence $\operatorname{Aut}(W) = A$. -/
@[kb "milne2006ec" "Ch. IV, 7.3(b), pdf p. 142"]
theorem statement_7_3_b (φ : W → W) (hφ : IsTorsorHom (A := A) φ) :
    ∃! a : A, ∀ w, φ w = a +ᵥ w := by
  obtain ⟨w₀⟩ := (inferInstance : Nonempty W)
  refine ⟨φ w₀ -ᵥ w₀, fun w => ?_, fun b hb => ?_⟩
  · conv_lhs => rw [← vsub_vadd w w₀, hφ]
    rw [← vsub_vadd (φ w₀) w₀, vadd_vadd, add_comm, ← vadd_vadd, vsub_vadd]
    simp
  · have := hb w₀
    rw [← vsub_vadd (φ w₀) w₀] at this
    exact (vadd_right_cancel _ this).symm

end Sets

/-! ## Continuous crossed homomorphisms and $H^1$ (pdf pp. 111, 114) -/

section H1

variable (Γ : Type*) [Group Γ] [TopologicalSpace Γ] (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]

/-- The continuous crossed homomorphisms $\Gamma \to A$ (pdf pp. 111, 114): $f(\sigma\tau) = \sigma f(\tau) +
f(\sigma)$, and $f$ continuous for the discrete topology on $A$, i.e. locally constant. -/
def contCocycles : AddSubgroup (Γ → A) where
  carrier := {f | IsCocycle₁ f ∧ IsLocallyConstant f}
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨fun σ τ => ?_, hf'.add hg'⟩
    simp only [Pi.add_apply, hf σ τ, hg σ τ, smul_add]
    abel
  zero_mem' := ⟨fun σ τ => by simp, IsLocallyConstant.const 0⟩
  neg_mem' := by
    rintro f ⟨hf, hf'⟩
    refine ⟨fun σ τ => ?_, hf'.neg⟩
    simp only [Pi.neg_apply, hf σ τ, smul_neg]
    abel

/-- The principal crossed homomorphisms $\sigma \mapsto \sigma P - P$, as a subgroup of the continuous ones (they are
continuous when $A$ is a discrete $\Gamma$-module). -/
def contCoboundaries :
    AddSubgroup (contCocycles Γ A) where
  carrier := {f | IsCoboundary₁ (f : Γ → A)}
  add_mem' := by
    rintro f g ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x + y, fun σ => by simp [← hx σ, ← hy σ, smul_add]; abel⟩
  zero_mem' := ⟨0, fun σ => by simp⟩
  neg_mem' := by
    rintro f ⟨x, hx⟩
    exact ⟨-x, fun σ => by simp [← hx σ, smul_neg]; abel⟩

/-- **$H^1(\Gamma, A)$** (pdf pp. 111, 114): continuous crossed homomorphisms modulo principal crossed homomorphisms,
for a discrete $\Gamma$-module $A$ (every stabilizer open). -/
@[kb "milne2006ec" "Ch. IV, §1, definition of H^1 for a profinite group, pdf p. 114"]
def ContH1 : Type _ :=
  (contCocycles Γ A) ⧸ (contCoboundaries Γ A)

instance : AddCommGroup (ContH1 Γ A) :=
  QuotientAddGroup.Quotient.addCommGroup _

/-- The class of a continuous crossed homomorphism. -/
def ContH1.mk (f : contCocycles Γ A) : ContH1 Γ A :=
  QuotientAddGroup.mk f

variable {Γ A}

theorem ContH1.mk_eq_mk_iff (f g : contCocycles Γ A) :
    (ContH1.mk Γ A f : ContH1 Γ A) = ContH1.mk Γ A g ↔
      ∃ P : A, ∀ σ : Γ, (g : Γ → A) σ = (f : Γ → A) σ + (σ • P - P) := by
  refine (QuotientAddGroup.eq (s := contCoboundaries Γ A)).trans ?_
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨P, fun σ => ?_⟩
    have h2 : σ • P - P = (-(f : Γ → A) + (g : Γ → A)) σ := hP σ
    simp only [Pi.add_apply, Pi.neg_apply] at h2
    rw [h2]; abel
  · rintro ⟨P, hP⟩
    refine ⟨P, fun σ => ?_⟩
    show σ • P - P = (-(f : Γ → A) + (g : Γ → A)) σ
    simp only [Pi.add_apply, Pi.neg_apply, hP σ]
    abel

theorem ContH1.mk_eq_zero_iff (f : contCocycles Γ A) :
    (ContH1.mk Γ A f : ContH1 Γ A) = 0 ↔ IsCoboundary₁ (f : Γ → A) := by
  exact QuotientAddGroup.eq_zero_iff (N := contCoboundaries Γ A) f

theorem ContH1.mk_surjective :
    Function.Surjective (ContH1.mk Γ A : contCocycles Γ A → ContH1 Γ A) :=
  QuotientAddGroup.mk_surjective

end H1

/-! ## Galois-set principal homogeneous spaces (pdf pp. 142–144) -/

section Torsors

variable (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]

/-- **A principal homogeneous space for $E$ over $k$, at the level of $k^{\mathrm{al}}$-points** (pdf p. 143): an
$A$-torsor $W$ ($A = E(k^{\mathrm{al}})$) with an action of $\Gamma$ such that $\sigma(w + P) = \sigma w + \sigma P$,
continuous for the discrete topology on $W$ (each point has coordinates in a finite extension, so its stabilizer is
open).  See the module docstring for the deviation from Milne's curves. -/
@[kb "milne2006ec" "Ch. IV, §7, principal homogeneous space for E (Galois-set form), pdf p. 143"]
structure GaloisTorsor where
  /-- The set $W(k^{\mathrm{al}})$. -/
  carrier : Type u
  [torsor : AddTorsor A carrier]
  [action : MulAction Γ carrier]
  smul_vadd' : ∀ (σ : Γ) (P : A) (w : carrier), σ • (P +ᵥ w) = (σ • P) +ᵥ (σ • w)
  isOpen_stabilizer' : ∀ w : carrier, IsOpen (MulAction.stabilizer Γ w : Set Γ)

attribute [instance] GaloisTorsor.torsor GaloisTorsor.action

variable {Γ A}

namespace GaloisTorsor

instance : CoeSort (GaloisTorsor Γ A) (Type _) := ⟨GaloisTorsor.carrier⟩

/-- An isomorphism of principal homogeneous spaces over $k$ (pdf p. 143): a bijection of $A$-sets commuting with
$\Gamma$ (i.e. defined over $k$). -/
structure Iso (W W' : GaloisTorsor Γ A) where
  /-- The underlying bijection. -/
  toEquiv : W ≃ W'
  map_vadd' : ∀ (P : A) (w : W), toEquiv (P +ᵥ w) = P +ᵥ toEquiv w
  map_smul' : ∀ (σ : Γ) (w : W), toEquiv (σ • w) = σ • toEquiv w

/-- The $k$-points $W(k) = W(k^{\mathrm{al}})^\Gamma$. -/
def rationalPoints (W : GaloisTorsor Γ A) : Set W := {w | ∀ σ : Γ, σ • w = w}

/-- **7.4** (pdf p. 143): addition makes $E$ a principal homogeneous space for $E$ (here $A$ with its own $\Gamma$-action),
the trivial principal homogeneous space. -/
@[kb "milne2006ec" "Ch. IV, 7.4, pdf p. 143"]
def trivial (hA : ∀ a : A, IsOpen (MulAction.stabilizer Γ a : Set Γ)) : GaloisTorsor Γ A where
  carrier := A
  smul_vadd' σ P w := by simp [vadd_eq_add, smul_add]
  isOpen_stabilizer' := hA

/-- $W$ is **trivial** (pdf p. 143) if it is isomorphic to the trivial principal homogeneous space. -/
def IsTrivial (W : GaloisTorsor Γ A) : Prop :=
  ∃ hA : ∀ a : A, IsOpen (MulAction.stabilizer Γ a : Set Γ), Nonempty (Iso W (trivial hA))

/-- Orbit maps $\sigma \mapsto \sigma x$ of an action with open stabilizers are locally constant. -/
theorem isLocallyConstant_orbit {X : Type*} [MulAction Γ X]
    (h : ∀ x : X, IsOpen (MulAction.stabilizer Γ x : Set Γ)) (x : X) :
    IsLocallyConstant (fun σ : Γ => σ • x) := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  by_cases hy : ∃ σ₀ : Γ, σ₀ • x = y
  · obtain ⟨σ₀, rfl⟩ := hy
    have : {σ : Γ | σ • x = σ₀ • x} = (fun σ => σ₀⁻¹ * σ) ⁻¹' (MulAction.stabilizer Γ x : Set Γ) := by
      ext σ
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul]
      rw [inv_smul_eq_iff]
    show IsOpen {σ : Γ | σ • x = σ₀ • x}
    rw [this]
    exact (h x).preimage (continuous_const.mul continuous_id)
  · convert isOpen_empty
    ext σ
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun e => hy ⟨σ, e⟩

/-- The crossed homomorphism identity for $\sigma \mapsto \sigma w_0 - w_0$. -/
theorem cocycle_mul (W : GaloisTorsor Γ A) (w₀ : W) (g h : Γ) :
    ((g * h) • w₀) -ᵥ w₀ = g • ((h • w₀) -ᵥ w₀) + ((g • w₀) -ᵥ w₀) := by
  have e := W.smul_vadd' g ((h • w₀) -ᵥ w₀) w₀
  rw [vsub_vadd] at e
  rw [mul_smul, e, vadd_vsub_assoc]

/-- Change of the point by a translation changes $\sigma w_0 - w_0$ by a principal crossed homomorphism. -/
theorem cocycle_vadd (W : GaloisTorsor Γ A) (c : A) (w₀ : W) (σ : Γ) :
    (σ • (c +ᵥ w₀)) -ᵥ (c +ᵥ w₀) = ((σ • w₀) -ᵥ w₀) + (σ • c - c) := by
  rw [W.smul_vadd' σ c w₀, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub]
  abel

/-- The crossed homomorphism at a second point $w_1$ differs from that at $w_0$ by the principal crossed
homomorphism of $w_1 - w_0$. -/
theorem cocycle_change (W : GaloisTorsor Γ A) (w₀ w₁ : W) (σ : Γ) :
    ((σ • w₁) -ᵥ w₁) = ((σ • w₀) -ᵥ w₀) + (σ • (w₁ -ᵥ w₀) - (w₁ -ᵥ w₀)) := by
  have h := cocycle_vadd W (w₁ -ᵥ w₀) w₀ σ
  rwa [vsub_vadd] at h

/-- The crossed homomorphism at corresponding points of isomorphic spaces agrees. -/
theorem cocycle_iso {W W' : GaloisTorsor Γ A} (e : Iso W W') (w₀ : W) (σ : Γ) :
    ((σ • e.toEquiv w₀) -ᵥ e.toEquiv w₀) = ((σ • w₀) -ᵥ w₀) := by
  have h := e.map_vadd' ((σ • w₀) -ᵥ w₀) w₀
  rw [vsub_vadd] at h
  rw [← e.map_smul', h, vadd_vsub]

/-- The crossed homomorphism $\sigma \mapsto \sigma w_0 - w_0$ attached to a point $w_0 \in W(k^{\mathrm{al}})$
(pdf p. 143: $\sigma w_0 = w_0 + f(\sigma)$). -/
def cocycleAt (W : GaloisTorsor Γ A) (w₀ : W) : contCocycles Γ A :=
  ⟨fun σ => (σ • w₀) -ᵥ w₀, cocycle_mul W w₀,
    (isLocallyConstant_orbit W.isOpen_stabilizer' w₀).comp (fun x => x -ᵥ w₀)⟩

/-- **The class $[f] \in H^1(\Gamma, A)$ of $W$** (pdf pp. 143–144), computed at a chosen point of $W$; by
`cls_eq_mk_cocycleAt` it does not depend on the point. -/
@[kb "milne2006ec" "Ch. IV, §7, the class of a principal homogeneous space, pdf p. 143"]
noncomputable def cls (W : GaloisTorsor Γ A) :
    ContH1 Γ A :=
  ContH1.mk Γ A (W.cocycleAt (Classical.arbitrary W))

/-- The class does not depend on the chosen point (pdf p. 144: a second point changes $f$ by a principal crossed
homomorphism). -/
theorem cls_eq_mk_cocycleAt (W : GaloisTorsor Γ A) (w₀ : W) : W.cls = ContH1.mk Γ A (W.cocycleAt w₀) := by
  unfold cls
  rw [ContH1.mk_eq_mk_iff]
  refine ⟨w₀ -ᵥ Classical.arbitrary W, fun σ => ?_⟩
  generalize Classical.arbitrary W = b
  obtain ⟨P, rfl⟩ : ∃ P : A, w₀ = P +ᵥ b := ⟨w₀ -ᵥ b, (vsub_vadd _ _).symm⟩
  show (σ • (P +ᵥ b)) -ᵥ (P +ᵥ b) = ((σ • b) -ᵥ b) + (σ • ((P +ᵥ b) -ᵥ b) - ((P +ᵥ b) -ᵥ b))
  rw [W.smul_vadd' σ P b, vadd_vsub, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub]
  abel

/-- An isomorphism with the trivial space is an equivalence with $A$ commuting with $\Gamma$. -/
theorem equiv_of_iso_trivial {W : GaloisTorsor Γ A} {hA : ∀ a : A, IsOpen (MulAction.stabilizer Γ a : Set Γ)}
    (e : Iso W (trivial hA)) : ∃ e' : W ≃ A, ∀ (σ : Γ) (w : W), e' (σ • w) = σ • e' w :=
  ⟨e.toEquiv, fun σ w => e.map_smul' σ w⟩

/-- An equivalence with $A$ compatible with both actions gives an isomorphism with the trivial space. -/
theorem isTrivial_of_equiv {W : GaloisTorsor Γ A} (hA : ∀ a : A, IsOpen (MulAction.stabilizer Γ a : Set Γ))
    (e : W ≃ A) (hv : ∀ (P : A) (w : W), e (P +ᵥ w) = P +ᵥ e w) (hs : ∀ (σ : Γ) (w : W), e (σ • w) = σ • e w) :
    W.IsTrivial :=
  ⟨hA, ⟨{ toEquiv := e, map_vadd' := hv, map_smul' := hs }⟩⟩

/-- **7.6** (pdf p. 143): $W$ is trivial if and only if $W(k) \neq \emptyset$. -/
@[kb "milne2006ec" "Ch. IV, 7.6, pdf p. 143"]
theorem statement_7_6 (W : GaloisTorsor Γ A) :
    W.IsTrivial ↔ W.rationalPoints.Nonempty := by
  constructor
  · rintro ⟨hA, ⟨e⟩⟩
    obtain ⟨e', he'⟩ := equiv_of_iso_trivial e
    refine ⟨e'.symm 0, fun σ => ?_⟩
    apply e'.injective
    rw [he', Equiv.apply_symm_apply]
    exact smul_zero σ
  · rintro ⟨w, hw⟩
    have hsm : ∀ (σ : Γ) (w' : W), σ • (w' -ᵥ w) = σ • w' -ᵥ σ • w := by
      intro σ w'
      have h := W.smul_vadd' σ (w' -ᵥ w) w
      rw [vsub_vadd] at h
      rw [h, vadd_vsub]
    have hA : ∀ a : A, IsOpen (MulAction.stabilizer Γ a : Set Γ) := by
      intro a
      have : (MulAction.stabilizer Γ a : Set Γ) = MulAction.stabilizer Γ (a +ᵥ w) := by
        ext σ
        simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
        rw [W.smul_vadd' σ a w, hw σ]
        exact ⟨fun h => by rw [h], fun h => vadd_right_cancel _ h⟩
      rw [this]
      exact W.isOpen_stabilizer' _
    refine isTrivial_of_equiv hA ⟨fun w' => w' -ᵥ w, fun a => a +ᵥ w, fun w' => vsub_vadd w' w,fun a => vadd_vsub a w⟩
      (fun P w' => vadd_vsub_assoc P w' w) (fun σ w' => ?_)
    show σ • w' -ᵥ w = σ • (w' -ᵥ w)
    rw [hsm, hw σ]

/-- **7.7** (pdf p. 143): a point $P \in E(k)$ defines the automorphism $w \mapsto w + P$ of $W$, and every
automorphism of $W$ over $k$ is of this form for a unique $P \in E(k)$. -/
@[kb "milne2006ec" "Ch. IV, 7.7, pdf p. 143"]
theorem statement_7_7 (W : GaloisTorsor Γ A) (φ : Iso W W) :
    ∃! P : A, (∀ σ : Γ, σ • P = P) ∧ ∀ w, φ.toEquiv w = P +ᵥ w := by
  obtain ⟨P, hP, huniq⟩ := statement_7_3_b (A := A) (W := W) φ.toEquiv φ.map_vadd'
  refine ⟨P, ⟨fun σ => ?_, hP⟩, fun Q hQ => huniq Q hQ.2⟩
  obtain ⟨w⟩ := (inferInstance : Nonempty W)
  have h1 := φ.map_smul' σ w
  rw [hP, hP, W.smul_vadd'] at h1
  exact vadd_right_cancel _ h1.symm

/-- Two points with the same crossed homomorphism give an isomorphism $w \mapsto (w - w_0) + w_0'$. -/
def isoOfPoints (W W' : GaloisTorsor Γ A) (w₀ : W) (w₀' : W')
    (h : ∀ σ : Γ, (σ • w₀) -ᵥ w₀ = (σ • w₀') -ᵥ w₀') : Iso W W' where
  toEquiv := ⟨fun w => (w -ᵥ w₀) +ᵥ w₀', fun w' => (w' -ᵥ w₀') +ᵥ w₀,
    fun w => by simp, fun w' => by simp⟩
  map_vadd' P w := by
    show ((P +ᵥ w) -ᵥ w₀) +ᵥ w₀' = P +ᵥ ((w -ᵥ w₀) +ᵥ w₀')
    rw [vadd_vsub_assoc, add_vadd]
  map_smul' σ w := by
    show ((σ • w) -ᵥ w₀) +ᵥ w₀' = σ • ((w -ᵥ w₀) +ᵥ w₀')
    obtain ⟨a, rfl⟩ : ∃ a : A, w = a +ᵥ w₀ := ⟨w -ᵥ w₀, (vsub_vadd _ _).symm⟩
    rw [vadd_vsub, W.smul_vadd' σ a w₀, W'.smul_vadd' σ a w₀', vadd_vsub_assoc, add_vadd, h σ, vsub_vadd]

theorem isoOfPoints_apply (W W' : GaloisTorsor Γ A) (w₀ : W) (w₀' : W')
    (h : ∀ σ : Γ, (σ • w₀) -ᵥ w₀ = (σ • w₀') -ᵥ w₀') (w : W) :
    (isoOfPoints W W' w₀ w₀' h).toEquiv w = (w -ᵥ w₀) +ᵥ w₀' := rfl

/-- The action $\sigma \star P = \sigma P + f(\sigma)$ of $\Gamma$ on $A$ twisted by a crossed homomorphism $f$. -/
def twistAction (f : contCocycles Γ A) : MulAction Γ A where
  smul σ P := σ • P + (f : Γ → A) σ
  one_smul P := by
    have h1 : (f : Γ → A) 1 = 0 := by
      have := (f.2 : IsCocycle₁ (f : Γ → A) ∧ IsLocallyConstant (f : Γ → A)).1 1 1
      simpa using this
    show (1 : Γ) • P + (f : Γ → A) 1 = P
    rw [h1, one_smul, add_zero]
  mul_smul g h P := by
    show (g * h) • P + (f : Γ → A) (g * h) = g • (h • P + (f : Γ → A) h) + (f : Γ → A) g
    rw [(f.2 : IsCocycle₁ (f : Γ → A) ∧ IsLocallyConstant (f : Γ → A)).1 g h, mul_smul, smul_add]
    abel

/-- **The twist** of the trivial principal homogeneous space by a continuous crossed homomorphism $f$ (pdf p. 144):
$A$ acting on itself by translation, with $\Gamma$ acting by $\sigma \star P = \sigma P + f(\sigma)$. -/
def twist (hA : ∀ a : A, IsOpen (MulAction.stabilizer Γ a : Set Γ)) (f : contCocycles Γ A) :
    GaloisTorsor Γ A where
  carrier := A
  action := twistAction f
  smul_vadd' σ P w := by
    show σ • (P + w) + (f : Γ → A) σ = σ • P + (σ • w + (f : Γ → A) σ)
    rw [smul_add]
    abel
  isOpen_stabilizer' P := by
    have hlc : IsLocallyConstant (fun σ : Γ => σ • P + (f : Γ → A) σ) :=
      (isLocallyConstant_orbit hA P).add (f.2 : IsCocycle₁ (f : Γ → A) ∧ IsLocallyConstant (f : Γ → A)).2
    exact hlc.isOpen_fiber P

/-- The class of the twist by $f$ is $[f]$. -/
theorem cls_twist (hA : ∀ a : A, IsOpen (MulAction.stabilizer Γ a : Set Γ)) (f : contCocycles Γ A) :
    (twist hA f).cls = ContH1.mk Γ A f := by
  rw [cls_eq_mk_cocycleAt (twist hA f) (0 : A)]
  congr 1
  apply Subtype.ext
  funext σ
  show (σ • (0 : A) + (f : Γ → A) σ) - 0 = (f : Γ → A) σ
  simp

/-- The class of $W$ is zero if and only if $W$ is trivial. -/
theorem cls_eq_zero_iff (W : GaloisTorsor Γ A) : W.cls = 0 ↔ W.IsTrivial := by
  rw [statement_7_6, cls_eq_mk_cocycleAt W (Classical.arbitrary W), ContH1.mk_eq_zero_iff]
  generalize Classical.arbitrary W = w₀
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(-x) +ᵥ w₀, fun σ => ?_⟩
    have h := cocycle_vadd W (-x) w₀ σ
    have h2 : (σ • w₀) -ᵥ w₀ = σ • x - x := (hx σ).symm
    rw [h2, smul_neg] at h
    have : (σ • ((-x) +ᵥ w₀)) -ᵥ ((-x) +ᵥ w₀) = 0 := by rw [h]; abel
    exact vsub_eq_zero_iff_eq.1 this
  · rintro ⟨w, hw⟩
    refine ⟨-(w -ᵥ w₀), fun σ => ?_⟩
    have h := cocycle_vadd W (w -ᵥ w₀) w₀ σ
    rw [vsub_vadd, (hw σ : σ • w = w), vsub_self] at h
    show σ • -(w -ᵥ w₀) - -(w -ᵥ w₀) = (σ • w₀) -ᵥ w₀
    rw [smul_neg, eq_neg_of_add_eq_zero_left h.symm]
    abel

/-- **Theorem 7.8** (pdf p. 144): the map $W \mapsto [f]$ is a bijection
$\{\text{principal homogeneous spaces for } E\}/\!\approx\ \to H^1(k, E)$ sending the trivial principal homogeneous
space to the zero element.  (Galois-set form; see the module docstring.)  Stated as: isomorphic spaces have the same
class, spaces with the same class are isomorphic, every class occurs, and the class is $0$ exactly for trivial
spaces. -/
@[kb "milne2006ec" "Ch. IV, Theorem 7.8, pdf p. 144"]
theorem theorem_7_8 (hA : ∀ a : A, IsOpen (MulAction.stabilizer Γ a : Set Γ)) :
    (∀ W W' : GaloisTorsor Γ A, W.cls = W'.cls ↔ Nonempty (Iso W W')) ∧
    (∀ c : ContH1 Γ A, ∃ W : GaloisTorsor Γ A, W.cls = c) ∧
    (∀ W : GaloisTorsor Γ A, W.cls = 0 ↔ W.IsTrivial) := by
  refine ⟨fun W W' => ⟨fun h => ?_, fun ⟨e⟩ => ?_⟩, fun c => ?_, cls_eq_zero_iff⟩
  · rw [cls_eq_mk_cocycleAt W (Classical.arbitrary W), cls_eq_mk_cocycleAt W' (Classical.arbitrary W'),
      ContH1.mk_eq_mk_iff] at h
    obtain ⟨P, hP⟩ := h
    refine ⟨isoOfPoints W W' (Classical.arbitrary W) ((-P) +ᵥ Classical.arbitrary W') fun σ => ?_⟩
    rw [cocycle_vadd W' (-P) _ σ]
    have h1 : (σ • Classical.arbitrary W') -ᵥ Classical.arbitrary W' =
        ((σ • Classical.arbitrary W) -ᵥ Classical.arbitrary W) + (σ • P - P) := hP σ
    rw [h1, smul_neg]
    abel
  · rw [cls_eq_mk_cocycleAt W (Classical.arbitrary W), cls_eq_mk_cocycleAt W' (e.toEquiv (Classical.arbitrary W))]
    congr 1
    exact Subtype.ext (funext fun σ => (cocycle_iso e _ σ).symm)
  · obtain ⟨f, rfl⟩ := ContH1.mk_surjective c
    exact ⟨twist hA f, cls_twist hA f⟩

end GaloisTorsor

/-! ## $n$-coverings and $H^1(\Gamma, A_n)$ (pdf pp. 145–146) -/

variable (A) in
/-- The $n$-torsion $A_n = \{P \in A \mid nP = 0\}$ (for $A = E(k^{\mathrm{al}})$, Milne's $E_n$). -/
def nTorsion (n : ℤ) : AddSubgroup A := (zsmulAddGroupHom (α := A) n).ker

theorem mem_nTorsion {n : ℤ} {P : A} : P ∈ nTorsion A n ↔ n • P = 0 := Iff.rfl

instance (n : ℤ) : DistribMulAction Γ (nTorsion A n) where
  smul σ P := ⟨σ • (P : A), by rw [mem_nTorsion, smul_comm, mem_nTorsion.1 P.2, smul_zero]⟩
  one_smul P := Subtype.ext (one_smul Γ (P : A))
  mul_smul σ τ P := Subtype.ext (mul_smul σ τ (P : A))
  smul_zero σ := Subtype.ext (smul_zero σ)
  smul_add σ P Q := Subtype.ext (smul_add σ (P : A) Q)

@[simp] theorem coe_smul_nTorsion {n : ℤ} (σ : Γ) (P : nTorsion A n) : ((σ • P : nTorsion A n) : A) = σ • (P : A) :=
  rfl

variable (Γ A) in
/-- **An $n$-covering** (pdf p. 145, Galois-set form): a principal homogeneous space $W$ for $E$ with a map
$\alpha : W \to E$ defined over $k$ (commuting with $\Gamma$) such that $\alpha(w_1 + P) = nP$ for all $P$, for some
$w_1 \in W(k^{\mathrm{al}})$. -/
@[kb "milne2006ec" "Ch. IV, §7, n-covering (Galois-set form), pdf p. 145"]
structure NCovering (n : ℤ) where
  /-- The principal homogeneous space. -/
  W : GaloisTorsor Γ A
  /-- The map $\alpha : W \to E$. -/
  α : W → A
  map_smul' : ∀ (σ : Γ) (w : W), α (σ • w) = σ • α w
  exists_base' : ∃ w₁ : W, ∀ P : A, α (P +ᵥ w₁) = n • P

namespace NCovering

variable {n : ℤ}

/-- A morphism (here: isomorphism) of $n$-coverings (pdf p. 145): an isomorphism $\varphi$ of principal homogeneous
spaces with $\alpha = \alpha' \circ \varphi$. -/
structure Iso (C C' : NCovering Γ A n) where
  /-- The isomorphism of principal homogeneous spaces. -/
  toIso : GaloisTorsor.Iso C.W C'.W
  comm' : ∀ w, C'.α (toIso.toEquiv w) = C.α w

/-- A base point of an $n$-covering is sent to $0$. -/
theorem α_base (C : NCovering Γ A n) (w₁ : C.W) (hw₁ : ∀ P : A, C.α (P +ᵥ w₁) = n • P) : C.α w₁ = 0 := by
  have h := hw₁ 0
  rwa [zero_vadd, smul_zero] at h

/-- The element $\sigma w_1 - w_1$ is $n$-torsion. -/
theorem cocycle_mem (C : NCovering Γ A n) (w₁ : C.W) (hw₁ : ∀ P : A, C.α (P +ᵥ w₁) = n • P) (σ : Γ) :
    (σ • w₁) -ᵥ w₁ ∈ nTorsion A n := by
  rw [mem_nTorsion]
  have h1 := hw₁ ((σ • w₁) -ᵥ w₁)
  rw [vsub_vadd, C.map_smul', α_base C w₁ hw₁, smul_zero] at h1
  exact h1.symm

/-- A function into an $n$-torsion subgroup is locally constant if it is so as a function into $A$. -/
theorem isLocallyConstant_subtype_val {X : Type*} [TopologicalSpace X] (F : X → A)
    (hF : IsLocallyConstant F) (hmem : ∀ x, F x ∈ nTorsion A n) :
    IsLocallyConstant (fun x => (⟨F x, hmem x⟩ : nTorsion A n)) := by
  intro s
  have := hF (Subtype.val '' s)
  convert this using 1
  ext x
  exact Subtype.val_injective.mem_set_image.symm

/-- The crossed homomorphism $\sigma \mapsto \sigma w_1 - w_1 \in E_n$ of (27) (pdf p. 145), for a base point
$w_1$ with $\alpha(w_1 + P) = nP$. -/
def cocycleAt (C : NCovering Γ A n) (w₁ : C.W) (hw₁ : ∀ P : A, C.α (P +ᵥ w₁) = n • P) :
    contCocycles Γ (nTorsion A n) :=
  ⟨fun σ => ⟨(σ • w₁) -ᵥ w₁, cocycle_mem C w₁ hw₁ σ⟩,
    fun g h => Subtype.ext (GaloisTorsor.cocycle_mul C.W w₁ g h),
    isLocallyConstant_subtype_val (fun σ : Γ => ((σ • w₁) -ᵥ w₁))
      ((GaloisTorsor.isLocallyConstant_orbit C.W.isOpen_stabilizer' w₁).comp (fun x => x -ᵥ w₁)) _⟩

/-- The class of $n$-coverings does not depend on the base point. -/
theorem mk_cocycleAt_eq (C : NCovering Γ A n) (b w₁ : C.W) (hb : ∀ P : A, C.α (P +ᵥ b) = n • P)
    (hw₁ : ∀ P : A, C.α (P +ᵥ w₁) = n • P) :
    ContH1.mk Γ _ (C.cocycleAt b hb) = ContH1.mk Γ _ (C.cocycleAt w₁ hw₁) := by
  rw [ContH1.mk_eq_mk_iff]
  have hP : n • (w₁ -ᵥ b) = 0 := by
    have h1 := hb (w₁ -ᵥ b)
    rw [vsub_vadd, α_base C w₁ hw₁] at h1
    exact h1.symm
  refine ⟨⟨w₁ -ᵥ b, mem_nTorsion.2 hP⟩, fun σ => ?_⟩
  apply Subtype.ext
  exact GaloisTorsor.cocycle_change C.W b w₁ σ

/-- **The class of an $n$-covering in $H^1(k, E_n)$** (pdf p. 145), computed at a chosen base point. -/
@[kb "milne2006ec" "Ch. IV, §7, the class of an n-covering, pdf p. 145"]
noncomputable def cls (C : NCovering Γ A n) : ContH1 Γ (nTorsion A n) :=
  ContH1.mk Γ _ (C.cocycleAt C.exists_base'.choose C.exists_base'.choose_spec)

/-- The class of an $n$-covering is computed at any base point. -/
theorem cls_eq_mk_cocycleAt (C : NCovering Γ A n) (w₁ : C.W) (hw₁ : ∀ P : A, C.α (P +ᵥ w₁) = n • P) :
    C.cls = ContH1.mk Γ _ (C.cocycleAt w₁ hw₁) :=
  mk_cocycleAt_eq C _ _ _ _

/-- **Theorem 7.10** (pdf p. 145): $(W, \alpha) \mapsto [f]$ defines a bijection
$\{n\text{-coverings}\}/\!\approx\ \to H^1(k, E_n)$ (Galois-set form): isomorphic $n$-coverings have the same class,
$n$-coverings with the same class are isomorphic, and every class occurs. -/
@[kb "milne2006ec" "Ch. IV, Theorem 7.10, pdf p. 145"]
theorem theorem_7_10 (hA : ∀ a : A, IsOpen (MulAction.stabilizer Γ a : Set Γ)) :
    (∀ C C' : NCovering Γ A n, C.cls = C'.cls ↔ Nonempty (Iso C C')) ∧
    (∀ c : ContH1 Γ (nTorsion A n), ∃ C : NCovering Γ A n, C.cls = c) := by
  refine ⟨fun C C' => ⟨fun h => ?_, fun ⟨e⟩ => ?_⟩, fun c => ?_⟩
  · obtain ⟨w₁, hw₁⟩ := C.exists_base'
    obtain ⟨w₁', hw₁'⟩ := C'.exists_base'
    rw [cls_eq_mk_cocycleAt C w₁ hw₁, cls_eq_mk_cocycleAt C' w₁' hw₁', ContH1.mk_eq_mk_iff] at h
    obtain ⟨P, hP⟩ := h
    have hpt : ∀ σ : Γ, (σ • w₁) -ᵥ w₁ = (σ • ((-(P : A)) +ᵥ w₁')) -ᵥ ((-(P : A)) +ᵥ w₁') := by
      intro σ
      rw [GaloisTorsor.cocycle_vadd C'.W (-(P : A)) w₁' σ]
      have h1 : (σ • w₁') -ᵥ w₁' = ((σ • w₁) -ᵥ w₁) + (σ • (P : A) - P) :=
        congrArg Subtype.val (hP σ)
      rw [h1, smul_neg]
      abel
    refine ⟨⟨GaloisTorsor.isoOfPoints C.W C'.W w₁ ((-(P : A)) +ᵥ w₁') hpt, fun w => ?_⟩⟩
    obtain ⟨a, rfl⟩ : ∃ a : A, w = a +ᵥ w₁ := ⟨w -ᵥ w₁, (vsub_vadd _ _).symm⟩
    rw [GaloisTorsor.isoOfPoints_apply, vadd_vsub, vadd_vadd, hw₁', hw₁, smul_add, smul_neg,
      mem_nTorsion.1 P.2, neg_zero, add_zero]
  · obtain ⟨w₁, hw₁⟩ := C.exists_base'
    have hw₁' : ∀ P : A, C'.α (P +ᵥ e.toIso.toEquiv w₁) = n • P := fun P => by
      rw [← e.toIso.map_vadd', e.comm', hw₁]
    rw [cls_eq_mk_cocycleAt C w₁ hw₁, cls_eq_mk_cocycleAt C' _ hw₁']
    congr 1
    exact Subtype.ext (funext fun σ => Subtype.ext (GaloisTorsor.cocycle_iso e.toIso w₁ σ).symm)
  · obtain ⟨f, rfl⟩ := ContH1.mk_surjective c
    let F : contCocycles Γ A :=
      ⟨fun σ => ((f : Γ → nTorsion A n) σ : A),
        fun g h => congrArg Subtype.val
          ((f.2 : IsCocycle₁ (f : Γ → nTorsion A n) ∧ IsLocallyConstant (f : Γ → nTorsion A n)).1 g h),
        (f.2 : IsCocycle₁ (f : Γ → nTorsion A n) ∧ IsLocallyConstant (f : Γ → nTorsion A n)).2.comp Subtype.val⟩
    have hbase : ∀ P : A, (fun Q : A => n • Q) (P +ᵥ (0 : A)) = n • P := by
      intro P
      show n • (P + 0) = n • P
      rw [add_zero]
    let C : NCovering Γ A n :=
      { W := GaloisTorsor.twist hA F
        α := fun Q : A => n • Q
        map_smul' := fun σ (w : A) => by
          show n • (σ • w + F.1 σ) = σ • (n • w)
          rw [smul_add, smul_comm n σ w, mem_nTorsion.1 ((f : Γ → nTorsion A n) σ).2, add_zero]
        exists_base' := ⟨(0 : A), hbase⟩ }
    refine ⟨C, ?_⟩
    rw [cls_eq_mk_cocycleAt C (0 : A) hbase]
    congr 1
    apply Subtype.ext
    funext σ
    apply Subtype.ext
    show (σ • (0 : A) + F.1 σ) - 0 = F.1 σ
    simp

end NCovering

end Torsors

end NumberFieldKB.MilneEC
