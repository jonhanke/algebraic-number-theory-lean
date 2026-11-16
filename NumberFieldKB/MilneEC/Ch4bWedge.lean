import Mathlib.Algebra.Torsor.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch4bTorsors

/-!
# Milne, Elliptic Curves, Chapter IV, Aside 7.9: the group structure on principal homogeneous spaces

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Aside 7.9, pdf p. 145.  Galois-set
form of principal homogeneous spaces, as in `NumberFieldKB.MilneEC.Ch4bTorsors`.

Aside 7.9: the bijection of Theorem 7.8 makes the set $WC(E/k)$ of isomorphism classes a commutative group; for $W$,
$W'$ define $W \wedge W'$ as the quotient of $W \times W'$ by an action of $E$, with $W \wedge W'$ a principal
homogeneous space representing the sum.

**Correction.** Milne writes the quotient by the *diagonal* action $(w, w') \sim (w + P, w' + P)$.  With that relation
(and $E$ acting on one factor) the class of the quotient is the *difference* $[W] - [W']$ (`cls_wedgeDiag`).  The sum
is represented by the quotient by the antidiagonal action $(w, w') \sim (w + P, w' - P)$ (`aside_7_9`).

## Proved
* `wedge`, `aside_7_9`: $[W \wedge W'] = [W] + [W']$ for the antidiagonal quotient.
* `wedgeDiag`, `cls_wedgeDiag`: $[W \wedge_{\mathrm{diag}} W'] = [W] - [W']$ for Milne's diagonal quotient.
-/

namespace NumberFieldKB.MilneEC

universe u

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {A : Type u} [AddCommGroup A]
  [DistribMulAction Γ A]

namespace GaloisTorsor

/-- The antidiagonal relation $(w, w') \sim (w + P, w' - P)$ on $W \times W'$. -/
def wedgeSetoid (W W' : GaloisTorsor Γ A) : Setoid (W × W') where
  r x y := ∃ P : A, y = (P +ᵥ x.1, (-P) +ᵥ x.2)
  iseqv := by
    refine ⟨fun x => ⟨0, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨P, rfl⟩
      exact ⟨-P, by simp⟩
    · rintro x y z ⟨P, rfl⟩ ⟨R, rfl⟩
      exact ⟨R + P, Prod.ext (by simp [add_vadd]) (by simp only [neg_add_rev, add_vadd]; exact vadd_comm _ _ _)⟩

/-- Helper: the stabilizer of a point is open once it contains the intersection of two open stabilizers. -/
theorem isOpen_stabilizer_of_inf {X : Type*} [MulAction Γ X] (x : X) {Y Z : Type*} [MulAction Γ Y] [MulAction Γ Z]
    (y : Y) (z : Z) (hy : IsOpen (MulAction.stabilizer Γ y : Set Γ))
    (hz : IsOpen (MulAction.stabilizer Γ z : Set Γ))
    (h : MulAction.stabilizer Γ y ⊓ MulAction.stabilizer Γ z ≤ MulAction.stabilizer Γ x) :
    IsOpen (MulAction.stabilizer Γ x : Set Γ) :=
  Subgroup.isOpen_mono h (by rw [Subgroup.coe_inf]; exact hy.inter hz)

/-- The action of $A$ on the first factor, on the quotient $W \wedge W'$. -/
def wedgeVAdd (W W' : GaloisTorsor Γ A) (Q : A) : Quotient (wedgeSetoid W W') → Quotient (wedgeSetoid W W') :=
  Quotient.map (fun x => (Q +ᵥ x.1, x.2)) (by
    rintro x y ⟨P, rfl⟩
    exact ⟨P, Prod.ext (vadd_comm Q P _) rfl⟩)

theorem wedgeVAdd_mk (W W' : GaloisTorsor Γ A) (Q : A) (x : W × W') :
    wedgeVAdd W W' Q (Quotient.mk _ x) = Quotient.mk _ (Q +ᵥ x.1, x.2) := rfl

/-- The difference of two points of $W \wedge W'$. -/
def wedgeVSub (W W' : GaloisTorsor Γ A) : Quotient (wedgeSetoid W W') → Quotient (wedgeSetoid W W') → A :=
  Quotient.lift₂ (fun x y => (x.1 -ᵥ y.1) + (x.2 -ᵥ y.2)) (by
    rintro x y x' y' ⟨P, rfl⟩ ⟨R, rfl⟩
    simp only [vadd_vsub_vadd_comm]
    simp
    abel)

theorem wedgeVSub_mk (W W' : GaloisTorsor Γ A) (x y : W × W') :
    wedgeVSub W W' (Quotient.mk _ x) (Quotient.mk _ y) = (x.1 -ᵥ y.1) + (x.2 -ᵥ y.2) := rfl

/-- The torsor structure on the quotient $W \wedge W'$. -/
@[instance_reducible]
noncomputable def wedgeTorsor (W W' : GaloisTorsor Γ A) : AddTorsor A (Quotient (wedgeSetoid W W')) where
  vadd := wedgeVAdd W W'
  zero_vadd q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (by simp)
  add_vadd Q R q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (by simp [add_vadd])
  vsub := wedgeVSub W W'
  nonempty := ⟨Quotient.mk _ (Classical.arbitrary W, Classical.arbitrary W')⟩
  vsub_vadd' q r := by
    induction q using Quotient.inductionOn with
    | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
    obtain ⟨w, w'⟩ := x
    obtain ⟨v, v'⟩ := y
    apply Quotient.sound
    refine ⟨v' -ᵥ w', Prod.ext ?_ ?_⟩
    · show w = (v' -ᵥ w') +ᵥ (((w -ᵥ v) + (w' -ᵥ v')) +ᵥ v)
      rw [vadd_vadd, ← add_assoc, add_comm (v' -ᵥ w'), add_assoc, add_comm (v' -ᵥ w'), vsub_add_vsub_cancel]
      simp
    · show w' = (-(v' -ᵥ w')) +ᵥ v'
      rw [neg_vsub_eq_vsub_rev, vsub_vadd]
  vadd_vsub' Q q := by
    induction q using Quotient.inductionOn with
    | _ x =>
    show wedgeVSub W W' (wedgeVAdd W W' Q ⟦x⟧) ⟦x⟧ = Q
    rw [wedgeVAdd_mk, wedgeVSub_mk]
    simp

/-- The diagonal action of $\Gamma$ on the quotient $W \wedge W'$. -/
def wedgeSMul (W W' : GaloisTorsor Γ A) (σ : Γ) : Quotient (wedgeSetoid W W') → Quotient (wedgeSetoid W W') :=
  Quotient.map (fun x => (σ • x.1, σ • x.2)) (by
    rintro x y ⟨P, rfl⟩
    refine ⟨σ • P, Prod.ext (W.smul_vadd' σ P x.1) ?_⟩
    show σ • ((-P) +ᵥ x.2) = (-(σ • P)) +ᵥ σ • x.2
    rw [W'.smul_vadd', smul_neg])

theorem wedgeSMul_mk (W W' : GaloisTorsor Γ A) (σ : Γ) (x : W × W') :
    wedgeSMul W W' σ (Quotient.mk _ x) = Quotient.mk _ (σ • x.1, σ • x.2) := rfl

/-- The action of $\Gamma$ on the quotient $W \wedge W'$. -/
@[instance_reducible]
def wedgeAction (W W' : GaloisTorsor Γ A) : MulAction Γ (Quotient (wedgeSetoid W W')) where
  smul := wedgeSMul W W'
  one_smul q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (Prod.ext (one_smul Γ x.1) (one_smul Γ x.2))
  mul_smul g h q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (Prod.ext (mul_smul g h x.1) (mul_smul g h x.2))

/-- **$W \wedge W'$** (Aside 7.9, pdf p. 145, with the antidiagonal relation): the quotient of $W \times W'$ by
$(w, w') \sim (w + P, w' - P)$, with $E$ acting by $[w, w'] + Q = [w + Q, w']$ and $\Gamma$ acting diagonally. -/
@[kb "milne2006ec" "Ch. IV, Aside 7.9, pdf p. 145"]
noncomputable def wedge (W W' : GaloisTorsor Γ A) : GaloisTorsor Γ A where
  carrier := Quotient (wedgeSetoid W W')
  torsor := wedgeTorsor W W'
  action := wedgeAction W W'
  smul_vadd' σ P q := by
    induction q using Quotient.inductionOn with
    | _ x =>
    change wedgeSMul W W' σ (wedgeVAdd W W' P (Quotient.mk _ x)) =
      wedgeVAdd W W' (σ • P) (wedgeSMul W W' σ (Quotient.mk _ x))
    rw [wedgeVAdd_mk, wedgeSMul_mk, wedgeSMul_mk, wedgeVAdd_mk]
    exact congrArg (Quotient.mk _) (Prod.ext (W.smul_vadd' σ P x.1) rfl)
  isOpen_stabilizer' q := by
    induction q using Quotient.inductionOn with
    | _ x =>
    letI := wedgeAction W W'
    refine isOpen_stabilizer_of_inf _ x.1 x.2 (W.isOpen_stabilizer' x.1) (W'.isOpen_stabilizer' x.2) ?_
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff]
    change wedgeSMul W W' σ (Quotient.mk _ x) = Quotient.mk _ x
    rw [wedgeSMul_mk]
    exact congrArg (Quotient.mk _) (Prod.ext hσ.1 hσ.2)

/-- The class of $[w, w']$ in $W \wedge W'$. -/
def wedgeMk (W W' : GaloisTorsor Γ A) (w : W) (w' : W') : wedge W W' := Quotient.mk _ (w, w')

theorem wedgeMk_vadd (W W' : GaloisTorsor Γ A) (Q : A) (w : W) (w' : W') :
    Q +ᵥ wedgeMk W W' w w' = wedgeMk W W' (Q +ᵥ w) w' := rfl

theorem smul_wedgeMk (W W' : GaloisTorsor Γ A) (σ : Γ) (w : W) (w' : W') :
    σ • wedgeMk W W' w w' = wedgeMk W W' (σ • w) (σ • w') := rfl

theorem wedgeMk_vsub (W W' : GaloisTorsor Γ A) (w₁ w₂ : W) (w₁' w₂' : W') :
    wedgeMk W W' w₁ w₁' -ᵥ wedgeMk W W' w₂ w₂' = (w₁ -ᵥ w₂) + (w₁' -ᵥ w₂') := rfl

theorem ContH1.mk_add (f g : contCocycles Γ A) :
    ContH1.mk Γ A (f + g) = ContH1.mk Γ A f + ContH1.mk Γ A g := rfl

theorem ContH1.mk_sub (f g : contCocycles Γ A) :
    ContH1.mk Γ A (f - g) = ContH1.mk Γ A f - ContH1.mk Γ A g := rfl

/-- **Aside 7.9** (pdf p. 145): $W \wedge W'$ represents the sum of $W$ and $W'$ in $WC(E/k) \cong H^1(k, E)$. -/
@[kb "milne2006ec" "Ch. IV, Aside 7.9, pdf p. 145"]
theorem aside_7_9 (W W' : GaloisTorsor Γ A) : (wedge W W').cls = W.cls + W'.cls := by
  have h1 := cls_eq_mk_cocycleAt W (Classical.arbitrary W)
  have h2 := cls_eq_mk_cocycleAt W' (Classical.arbitrary W')
  rw [cls_eq_mk_cocycleAt (wedge W W') (wedgeMk W W' (Classical.arbitrary W) (Classical.arbitrary W')), h1, h2,
    ← ContH1.mk_add]
  congr 1

/-- Milne's diagonal relation $(w, w') \sim (w + P, w' + P)$ on $W \times W'$. -/
def wedgeDiagSetoid (W W' : GaloisTorsor Γ A) : Setoid (W × W') where
  r x y := ∃ P : A, y = (P +ᵥ x.1, P +ᵥ x.2)
  iseqv := by
    refine ⟨fun x => ⟨0, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨P, rfl⟩
      exact ⟨-P, by simp⟩
    · rintro x y z ⟨P, rfl⟩ ⟨R, rfl⟩
      exact ⟨R + P, by simp [add_vadd]⟩

/-- The action of $A$ on the first factor, on the diagonal quotient. -/
def wedgeDiagVAdd (W W' : GaloisTorsor Γ A) (Q : A) :
    Quotient (wedgeDiagSetoid W W') → Quotient (wedgeDiagSetoid W W') :=
  Quotient.map (fun x => (Q +ᵥ x.1, x.2)) (by
    rintro x y ⟨P, rfl⟩
    exact ⟨P, Prod.ext (vadd_comm Q P _) rfl⟩)

theorem wedgeDiagVAdd_mk (W W' : GaloisTorsor Γ A) (Q : A) (x : W × W') :
    wedgeDiagVAdd W W' Q (Quotient.mk _ x) = Quotient.mk _ (Q +ᵥ x.1, x.2) := rfl

/-- The difference of two points of the diagonal quotient. -/
def wedgeDiagVSub (W W' : GaloisTorsor Γ A) :
    Quotient (wedgeDiagSetoid W W') → Quotient (wedgeDiagSetoid W W') → A :=
  Quotient.lift₂ (fun x y => (x.1 -ᵥ y.1) - (x.2 -ᵥ y.2)) (by
    rintro x y x' y' ⟨P, rfl⟩ ⟨R, rfl⟩
    simp only [vadd_vsub_vadd_comm]
    simp)

theorem wedgeDiagVSub_mk (W W' : GaloisTorsor Γ A) (x y : W × W') :
    wedgeDiagVSub W W' (Quotient.mk _ x) (Quotient.mk _ y) = (x.1 -ᵥ y.1) - (x.2 -ᵥ y.2) := rfl

/-- The torsor structure on the diagonal quotient. -/
@[instance_reducible]
noncomputable def wedgeDiagTorsor (W W' : GaloisTorsor Γ A) :
    AddTorsor A (Quotient (wedgeDiagSetoid W W')) where
  vadd := wedgeDiagVAdd W W'
  zero_vadd q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (by simp)
  add_vadd Q R q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (by simp [add_vadd])
  vsub := wedgeDiagVSub W W'
  nonempty := ⟨Quotient.mk _ (Classical.arbitrary W, Classical.arbitrary W')⟩
  vsub_vadd' q r := by
    induction q using Quotient.inductionOn with
    | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
    obtain ⟨w, w'⟩ := x
    obtain ⟨v, v'⟩ := y
    apply Quotient.sound
    refine ⟨w' -ᵥ v', Prod.ext ?_ ?_⟩
    · show w = (w' -ᵥ v') +ᵥ ((((w -ᵥ v) - (w' -ᵥ v')) +ᵥ v))
      rw [vadd_vadd]
      simp
    · show w' = (w' -ᵥ v') +ᵥ v'
      rw [vsub_vadd]
  vadd_vsub' Q q := by
    induction q using Quotient.inductionOn with
    | _ x =>
    show wedgeDiagVSub W W' (wedgeDiagVAdd W W' Q ⟦x⟧) ⟦x⟧ = Q
    rw [wedgeDiagVAdd_mk, wedgeDiagVSub_mk]
    simp

/-- The diagonal action of $\Gamma$ on the diagonal quotient. -/
def wedgeDiagSMul (W W' : GaloisTorsor Γ A) (σ : Γ) :
    Quotient (wedgeDiagSetoid W W') → Quotient (wedgeDiagSetoid W W') :=
  Quotient.map (fun x => (σ • x.1, σ • x.2)) (by
    rintro x y ⟨P, rfl⟩
    exact ⟨σ • P, Prod.ext (W.smul_vadd' σ P x.1) (W'.smul_vadd' σ P x.2)⟩)

theorem wedgeDiagSMul_mk (W W' : GaloisTorsor Γ A) (σ : Γ) (x : W × W') :
    wedgeDiagSMul W W' σ (Quotient.mk _ x) = Quotient.mk _ (σ • x.1, σ • x.2) := rfl

/-- The action of $\Gamma$ on the diagonal quotient. -/
@[instance_reducible]
def wedgeDiagAction (W W' : GaloisTorsor Γ A) : MulAction Γ (Quotient (wedgeDiagSetoid W W')) where
  smul := wedgeDiagSMul W W'
  one_smul q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (Prod.ext (one_smul Γ x.1) (one_smul Γ x.2))
  mul_smul g h q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (Prod.ext (mul_smul g h x.1) (mul_smul g h x.2))

/-- The quotient of $W \times W'$ by Milne's diagonal action (pdf p. 145), with $E$ acting on the first factor. -/
noncomputable def wedgeDiag (W W' : GaloisTorsor Γ A) : GaloisTorsor Γ A where
  carrier := Quotient (wedgeDiagSetoid W W')
  torsor := wedgeDiagTorsor W W'
  action := wedgeDiagAction W W'
  smul_vadd' σ P q := by
    induction q using Quotient.inductionOn with
    | _ x =>
    change wedgeDiagSMul W W' σ (wedgeDiagVAdd W W' P (Quotient.mk _ x)) =
      wedgeDiagVAdd W W' (σ • P) (wedgeDiagSMul W W' σ (Quotient.mk _ x))
    rw [wedgeDiagVAdd_mk, wedgeDiagSMul_mk, wedgeDiagSMul_mk, wedgeDiagVAdd_mk]
    exact congrArg (Quotient.mk _) (Prod.ext (W.smul_vadd' σ P x.1) rfl)
  isOpen_stabilizer' q := by
    induction q using Quotient.inductionOn with
    | _ x =>
    letI := wedgeDiagAction W W'
    refine isOpen_stabilizer_of_inf _ x.1 x.2 (W.isOpen_stabilizer' x.1) (W'.isOpen_stabilizer' x.2) ?_
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff]
    change wedgeDiagSMul W W' σ (Quotient.mk _ x) = Quotient.mk _ x
    rw [wedgeDiagSMul_mk]
    exact congrArg (Quotient.mk _) (Prod.ext hσ.1 hσ.2)

/-- With Milne's diagonal relation the quotient represents the difference $[W] - [W']$, not the sum (the correction
recorded in the module docstring). -/
@[kb "milne2006ec" "Ch. IV, Aside 7.9, pdf p. 145 (correction)"]
theorem cls_wedgeDiag (W W' : GaloisTorsor Γ A) : (wedgeDiag W W').cls = W.cls - W'.cls := by
  have h1 := cls_eq_mk_cocycleAt W (Classical.arbitrary W)
  have h2 := cls_eq_mk_cocycleAt W' (Classical.arbitrary W')
  rw [cls_eq_mk_cocycleAt (wedgeDiag W W')
    (Quotient.mk (wedgeDiagSetoid W W') (Classical.arbitrary W, Classical.arbitrary W')), h1, h2, ← ContH1.mk_sub]
  congr 1

end GaloisTorsor

end NumberFieldKB.MilneEC
