import Mathlib.Algebra.Torsor.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Topology.Algebra.Group.Defs
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch4bTorsors

/-!
# Milne, Elliptic Curves, Chapter IV §7: curves of genus 1 and their jacobians

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Section 7, Theorem 7.19, the
definition of the jacobian (pdf p. 150) and the summaries 7.23, 7.24 (pdf p. 151).

## Milne's argument (pdf pp. 149–150)
Let $W$ be a nonsingular projective curve of genus 1 over $k$.  Over $k^{\mathrm{al}}$ there is an isomorphism
$\varphi\colon E_0 \to W$ from an elliptic curve $E_0$ over $k$ (Riemann–Roch, and $j \in k$).  For
$\sigma \in \Gamma$, ${}^\sigma\varphi = \varphi \circ \alpha(\sigma)$ with $\alpha(\sigma) \in
\operatorname{Aut}_{k^{\mathrm{al}}}(E_0) = E_0(k^{\mathrm{al}}) \rtimes \operatorname{Aut}(E_0, O)$ (Remark 7.18),
so $\alpha(\sigma)(P) = u_\sigma(P) + Q_\sigma$ with $u_\sigma \in \operatorname{Aut}(E_0, O)$.  Twisting $E_0$ by the
image $[u]$ of $[\alpha]$ in $H^1(k, \operatorname{Aut}(E_0, O))$ gives $E_1$, and $W$ is a principal homogeneous
space for $E_1$.

## Formalization (Galois sets, as in `Ch4bTorsors`)
As for Theorems 7.8 and 7.10 in `Ch4bTorsors`, curves over $k$ are replaced by their Galois sets of
$k^{\mathrm{al}}$-points.  A `CurveForm Γ A W` is a $\Gamma$-set $W$ (the points of $W$) with a bijection
$\varphi\colon A \to W$ ($A = E_0(k^{\mathrm{al}})$) whose conjugates ${}^\sigma\varphi = \sigma\circ\varphi\circ
\sigma^{-1}$ satisfy $\varphi^{-1}\circ{}^\sigma\varphi = (P \mapsto u_\sigma(P) + Q_\sigma)$ with $u_\sigma$ an
automorphism of the group $A$: this is the conclusion of Milne's first step together with Remark 7.18.

## Proved
* `CurveForm.twistAction`: $\sigma \star P = u_\sigma(\sigma P)$ is an action of $\Gamma$ on $A$ by group
  automorphisms (the Galois action on $E_1(k^{\mathrm{al}})$); `CurveForm.u_mul` is the cocycle identity of $u$
  (Milne's class $[u] \in H^1(k, \operatorname{Aut}(E_0, O))$).
* `theorem_7_19_galois`: **Theorem 7.19, Milne's proof at the level of points**: $W$ is a principal homogeneous space
  for $A$ with the twisted action, with translation $P + w = \varphi(P + \varphi^{-1}(w))$.
* `IsJacobianOf`: **the jacobian** (pdf p. 150): an isomorphism $\varphi\colon E_0 \to W$ over $k^{\mathrm{al}}$ such
  that ${}^\sigma\varphi(P) = \varphi(P + Q_\sigma)$; `isJacobianOf_iff`: this holds exactly when $W$ is a
  principal homogeneous space for $E_0$ (7.23: the curves with jacobian $E$ are the principal homogeneous spaces for
  $E$, classified by $H^1$ by `theorem_7_8`).
* `CurveForm.isJacobianOf_of_u_eq_one`: if all $u_\sigma = 1$ ($[u] = 0$), $E_0$ itself is the jacobian.

## Not formalized (recorded)
The geometric inputs: that a curve of genus 1 over $k$ is a $k$-form of an elliptic curve (the existence of
$\varphi$ uses Riemann–Roch on $W_{k^{\mathrm{al}}}$, Ch. I 4.10, a named statement there), that the twisted Galois set
is the set of points of an elliptic curve $E_1$ over $k$ (Theorem 7.15, `theorem_7_15`, plus the transport of points
along a change of variables, which Mathlib lacks), and the uniqueness of $E_0$ up to isomorphism.
-/

universe u

namespace NumberFieldKB.MilneEC

variable (Γ : Type*) [Group Γ] (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] (W : Type u)
  [MulAction Γ W]

/-- **A $k$-form of the curve $E_0$, at the level of points** (Milne pdf p. 149): a bijection $\varphi\colon A \to W$
($A = E_0(k^{\mathrm{al}})$, $W$ the Galois set of the curve) such that $\varphi^{-1} \circ {}^\sigma\varphi$ is the
automorphism $P \mapsto u_\sigma(P) + Q_\sigma$ of the curve $E_0$, with $u_\sigma$ a group automorphism. -/
@[kb "milne2006ec" "Ch. IV, proof of Theorem 7.19, the isomorphism φ : E₀ → W over k^al, pdf p. 149"]
structure CurveForm where
  /-- The isomorphism $\varphi\colon E_0 \to W$ over $k^{\mathrm{al}}$, on points. -/
  φ : A ≃ W
  /-- The part $u_\sigma \in \operatorname{Aut}(E_0, O)$ of $\alpha(\sigma)$. -/
  u : Γ → A ≃+ A
  /-- The translation part $Q_\sigma \in E_0(k^{\mathrm{al}})$ of $\alpha(\sigma)$. -/
  Q : Γ → A
  form : ∀ (σ : Γ) (P : A), φ.symm (σ • φ (σ⁻¹ • P)) = u σ P + Q σ

namespace CurveForm

variable {Γ A W} (F : CurveForm Γ A W)

/-- $\varphi^{-1}(\sigma \varphi(X)) = \alpha(\sigma)(\sigma X)$. -/
lemma symm_smul_φ (σ : Γ) (X : A) : F.φ.symm (σ • F.φ X) = F.u σ (σ • X) + F.Q σ := by
  have := F.form σ (σ • X)
  rwa [inv_smul_smul] at this

lemma Q_one : F.Q 1 = 0 := by
  have := F.form 1 0
  simp only [inv_one, one_smul, Equiv.symm_apply_apply, map_zero, zero_add] at this
  exact this.symm

lemma u_one (P : A) : F.u 1 P = P := by
  have := F.form 1 P
  simp only [inv_one, one_smul, Equiv.symm_apply_apply, F.Q_one, add_zero] at this
  exact this.symm

/-- The cocycle identity of $\alpha$: $\alpha(\sigma\tau) = \alpha(\sigma) \circ {}^\sigma\alpha(\tau)$. -/
lemma alpha_mul (σ τ : Γ) (P : A) :
    F.u (σ * τ) P + F.Q (σ * τ) = F.u σ (σ • (F.u τ (σ⁻¹ • P) + F.Q τ)) + F.Q σ := by
  rw [← F.form (σ * τ) P, ← F.symm_smul_φ σ, ← F.form τ (σ⁻¹ • P), Equiv.apply_symm_apply,
    mul_inv_rev, mul_smul, mul_smul]

lemma Q_mul (σ τ : Γ) : F.Q (σ * τ) = F.u σ (σ • F.Q τ) + F.Q σ := by
  have := F.alpha_mul σ τ 0
  simpa using this

/-- **The cocycle identity of $u$** (Milne pdf pp. 149–150): $u_{\sigma\tau}\circ\sigma\tau =
u_\sigma\circ\sigma\circ u_\tau\circ\tau$ on $A$, i.e. $u$ is a crossed homomorphism into
$\operatorname{Aut}(E_0, O)$, the class used to twist $E_0$. -/
@[kb "milne2006ec" "Ch. IV, proof of Theorem 7.19, the class in H¹(k, Aut(E₀, O)), pdf p. 150"]
lemma u_mul (σ τ : Γ) (P : A) : F.u (σ * τ) ((σ * τ) • P) = F.u σ (σ • F.u τ (τ • P)) := by
  have h := F.alpha_mul σ τ ((σ * τ) • P)
  rw [mul_smul σ τ P, inv_smul_smul, smul_add, map_add, F.Q_mul, ← add_assoc, ← mul_smul] at h
  exact add_right_cancel (add_right_cancel h)

/-- The points $E_1(k^{\mathrm{al}})$ of the twist: the group $A$ with the twisted Galois action. -/
def Twist (_F : CurveForm Γ A W) : Type u := A

instance : AddCommGroup F.Twist := inferInstanceAs (AddCommGroup A)

/-- The identity map from $E_1(k^{\mathrm{al}})$ to $A$. -/
def ofTw : F.Twist → A := id

/-- The identity map from $A$ to $E_1(k^{\mathrm{al}})$. -/
def toTw : A → F.Twist := id

@[simp] lemma ofTw_toTw (P : A) : F.ofTw (F.toTw P) = P := rfl
@[simp] lemma toTw_ofTw (P : F.Twist) : F.toTw (F.ofTw P) = P := rfl
@[simp] lemma ofTw_add (P P' : F.Twist) : F.ofTw (P + P') = F.ofTw P + F.ofTw P' := rfl
@[simp] lemma ofTw_zero : F.ofTw 0 = 0 := rfl

/-- The twisted action $\sigma \star P = u_\sigma(\sigma P)$ (Milne: twist $E_0$ by $[u]$). -/
@[kb "milne2006ec" "Ch. IV, proof of Theorem 7.19, the twist E₁ of E₀, pdf p. 150"]
instance twistAction : DistribMulAction Γ F.Twist where
  smul σ P := F.toTw (F.u σ (σ • F.ofTw P))
  one_smul P := by
    show F.toTw (F.u 1 ((1 : Γ) • F.ofTw P)) = P
    rw [one_smul, F.u_one]; rfl
  mul_smul σ τ P := by
    show F.toTw (F.u (σ * τ) ((σ * τ) • F.ofTw P)) = F.toTw (F.u σ (σ • F.u τ (τ • F.ofTw P)))
    rw [F.u_mul σ τ]
  smul_zero σ := by
    show F.toTw (F.u σ (σ • (0 : A))) = 0
    simp; rfl
  smul_add σ P P' := by
    show F.toTw (F.u σ (σ • (F.ofTw P + F.ofTw P'))) =
      F.toTw (F.u σ (σ • F.ofTw P) + F.u σ (σ • F.ofTw P'))
    rw [smul_add, map_add]

lemma twist_smul_def (σ : Γ) (P : F.Twist) : F.ofTw (σ • P) = F.u σ (σ • F.ofTw P) := rfl

/-- The translation $P + w = \varphi(P + \varphi^{-1}(w))$ of $W$ by $E_1(k^{\mathrm{al}})$. -/
@[instance_reducible]
def torsorStruct : AddTorsor F.Twist W where
  vadd P w := F.φ (F.ofTw P + F.φ.symm w)
  vsub w w' := F.toTw (F.φ.symm w - F.φ.symm w')
  zero_vadd w := by
    show F.φ (F.ofTw 0 + F.φ.symm w) = w
    simp
  add_vadd P P' w := by
    show F.φ (F.ofTw (P + P') + F.φ.symm w) = F.φ (F.ofTw P + F.φ.symm (F.φ (F.ofTw P' + F.φ.symm w)))
    rw [Equiv.symm_apply_apply, ofTw_add, add_assoc]
  vsub_vadd' w w' := by
    show F.φ (F.ofTw (F.toTw (F.φ.symm w - F.φ.symm w')) + F.φ.symm w') = w
    simp
  vadd_vsub' P w := by
    show F.toTw (F.φ.symm (F.φ (F.ofTw P + F.φ.symm w)) - F.φ.symm w) = P
    simp
  nonempty := ⟨F.φ 0⟩

/-- The computation behind Theorem 7.19: $\sigma\varphi(P + \varphi^{-1}w) =
\varphi(\sigma{\star}P + \varphi^{-1}(\sigma w))$. -/
theorem smul_φ_add (σ : Γ) (P : F.Twist) (w : W) :
    σ • F.φ (F.ofTw P + F.φ.symm w) = F.φ (F.ofTw (σ • P) + F.φ.symm (σ • w)) := by
  rw [twist_smul_def]
  apply F.φ.symm.injective
  rw [Equiv.symm_apply_apply, F.symm_smul_φ]
  conv_rhs => rw [show σ • w = σ • F.φ (F.φ.symm w) by simp, F.symm_smul_φ]
  rw [smul_add, map_add, add_assoc]

/-- **Theorem 7.19, at the level of points** (Milne's proof, pdf pp. 149–150): $W$, with its own Galois action, is a
principal homogeneous space for the twist $E_1$ of $E_0$ by $[u]$: $\sigma(P + w) = \sigma{\star}P + \sigma w$. -/
@[kb "milne2006ec" "Ch. IV, Theorem 7.19 (Galois-set form), pdf p. 149"]
theorem theorem_7_19_galois (σ : Γ) (P : F.Twist) (w : W) :
    letI := F.torsorStruct
    σ • (P +ᵥ w) = (σ • P) +ᵥ (σ • w) :=
  F.smul_φ_add σ P w

/-- **Theorem 7.19 (Galois-set form) as a principal homogeneous space** (pdf p. 149): when the stabilizers of points
of $W$ are open, `theorem_7_19_galois` makes $W$ a `GaloisTorsor` for the twist. -/
@[kb "milne2006ec" "Ch. IV, Theorem 7.19 (Galois-set form), pdf p. 149"]
def toGaloisTorsor [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hW : ∀ w : W, IsOpen (MulAction.stabilizer Γ w : Set Γ)) : GaloisTorsor Γ F.Twist where
  carrier := W
  torsor := F.torsorStruct
  smul_vadd' := F.theorem_7_19_galois
  isOpen_stabilizer' := hW

end CurveForm

/-- **The jacobian of a curve of genus 1** (Milne pdf p. 150), at the level of points: $E_0$ (with points $A$) is the
jacobian of $W$ if there is an isomorphism $\varphi\colon E_0 \to W$ over $k^{\mathrm{al}}$ such that for every
$\sigma$ there is $Q_\sigma \in E_0(k^{\mathrm{al}})$ with $({}^\sigma\varphi)(P) = \varphi(P + Q_\sigma)$ for all
$P$. -/
@[kb "milne2006ec" "Ch. IV, §7, definition of the jacobian of a curve of genus 1, pdf p. 150"]
def IsJacobianOf : Prop :=
  ∃ φ : A ≃ W, ∀ σ : Γ, ∃ Q : A, ∀ P : A, σ • φ (σ⁻¹ • P) = φ (P + Q)

/-- **The jacobian characterizes principal homogeneous spaces** (Milne pdf pp. 150–151, 7.23): $E_0$ is the jacobian
of $W$ exactly when $W$ is a principal homogeneous space for $E_0$, i.e. carries a simply transitive action of $A$ with
$\sigma(P + w) = \sigma P + \sigma w$.  Together with `theorem_7_8` this is 7.23: the curves with jacobian $E$ are the
principal homogeneous spaces for $E$, classified by $H^1(\mathbb Q, E)$. -/
@[kb "milne2006ec" "Ch. IV, §7, characterization of the jacobian; 7.23, pdf pp. 150-151"]
theorem isJacobianOf_iff :
    IsJacobianOf Γ A W ↔ ∃ T : AddTorsor A W,
      letI := T
      ∀ (σ : Γ) (P : A) (w : W), σ • (P +ᵥ w) = (σ • P) +ᵥ (σ • w) := by
  constructor
  · rintro ⟨φ, hφ⟩
    choose Q hQ using hφ
    let F : CurveForm Γ A W :=
      { φ := φ
        u := fun _ => AddEquiv.refl A
        Q := Q
        form := fun σ P => by rw [hQ σ P]; simp }
    refine ⟨F.torsorStruct, fun σ P w => ?_⟩
    exact F.theorem_7_19_galois σ P w
  · rintro ⟨T, hT⟩
    let _ := T
    obtain ⟨w₀⟩ := (inferInstance : Nonempty W)
    let φ : A ≃ W :=
      { toFun := fun P => P +ᵥ w₀
        invFun := fun w => w -ᵥ w₀
        left_inv := fun P => vadd_vsub P w₀
        right_inv := fun w => vsub_vadd w w₀ }
    refine ⟨φ, fun σ => ⟨σ • w₀ -ᵥ w₀, fun P => ?_⟩⟩
    show σ • (σ⁻¹ • P +ᵥ w₀) = (P + (σ • w₀ -ᵥ w₀)) +ᵥ w₀
    rw [hT, smul_inv_smul, add_vadd, vsub_vadd]

/-- If every $u_\sigma$ is the identity (the class $[u]$ is trivial), $E_0$ itself is the jacobian of $W$. -/
theorem CurveForm.isJacobianOf_of_u_eq_one (F : CurveForm Γ A W) (hu : ∀ σ P, F.u σ P = P) :
    IsJacobianOf Γ A W := by
  refine ⟨F.φ, fun σ => ⟨F.Q σ, fun P => ?_⟩⟩
  apply F.φ.symm.injective
  rw [F.form, hu, Equiv.symm_apply_apply]

end NumberFieldKB.MilneEC
