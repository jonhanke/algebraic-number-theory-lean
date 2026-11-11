import NumberFieldKB.MilneEC.Ch1Maps
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Elliptic Curves*, Chapter I, Proposition 4.18: the named statement is false as stated

The named statement `Prop4_18` asks that the extension of a regular map of affine pieces be unique as a map on the
points over **every** field `K ⊇ k`. A `ProjRegularMap` is a family of maps $C(K) \to C'(K)$, one for each `K`, with
no compatibility between different fields, and each map is constrained only by the points of $C(K)$ itself. When
$C(K)$ has no point in the affine piece, nothing ties the value at a point at infinity to the affine map.

**Counterexample** (`not_prop4_18`). Over $k = \mathbb F_3$ (a perfect field of characteristic not 2), take the
nonsingular Weierstrass cubics $C : Y^2Z = X^3 - XZ^2 - Z^3$ and $C' : Y^2Z = X^3 - XZ^2$ ($4a^3 + 27b^2 = -4 \ne 0$
in $\mathbb F_3$ for both), and the constant map $f$ of the affine pieces onto $(0, 0) \in C'$. Since
$y^2 = x^3 - x - 1 = -1$ has no solution in $\mathbb F_3$, the only point of $C(\mathbb F_3)$ is $(0 : 1 : 0)$
(`rep_two_eq_zero_of_mem`). The constant map onto $(0 : 0 : 1)$ extends $f$; so does the map that is $(0 : 0 : 1)$
over every field `K` for which $C(K)$ has an affine point and $(0 : 1 : 0)$ over the other fields (both pieces are
given by constant polynomials, `ProjRegularMap.const`, `ProjRegularMap.ite`). The two differ at the point
$(0 : 1 : 0)$ of $C(\mathbb F_3)$.

The same pair refutes the conclusion of `example_4_20` for these curves (`not_example_4_20_conclusion`); so
`Prop4_18`, and the results proved from it (`example_4_20`, `remark_7_1`), are vacuous as stated.

**Corrected statement** (`Prop4_18Corrected`): Milne's regular maps are determined by their points over an
algebraically closed field (compare Proposition 4.16 (c) for affine curves); uniqueness is asked over algebraically
closed fields `K` only. `example_4_20_corrected` is proved from it. The corrected statement is not proved here: its
existence half needs the local rings of a nonsingular curve to be discrete valuation rings and a representation of the
map near each point at infinity by polynomials over `k`. The counterexample is an error of this
repository's formal statement, not an erratum of Milne.
-/

open MvPolynomial
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace NumberFieldKB.MilneEC

universe u

section General

variable {k : Type u} [Field k] {F F' : MvPolynomial (Fin 3) k}

theorem algebraMap_comp_ne_zero {K : Type*} [Field K] [Algebra k K] {v : Fin 3 → k} (hv : v ≠ 0) :
    (fun i => algebraMap k K (v i)) ≠ 0 := by
  intro h
  apply hv
  funext i
  have := congrFun h i
  simpa using this

theorem aeval_algebraMap_comp {K : Type*} [Field K] [Algebra k K] (v : Fin 3 → k)
    (G : MvPolynomial (Fin 3) k) :
    aeval (fun i => algebraMap k K (v i)) G = algebraMap k K (aeval v G) := by
  induction G using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The **constant regular map** $C \to C'$ onto a point $(v_0 : v_1 : v_2)$ of $C'(k)$, given everywhere by the
constant polynomials $v_0, v_1, v_2$. -/
def ProjRegularMap.const {d : ℕ} (hF' : F'.IsHomogeneous d) (v : Fin 3 → k) (hv : v ≠ 0)
    (hvF : aeval v F' = 0) : ProjRegularMap F F' where
  toFun K _ _ _ := ⟨Projectivization.mk K (fun i => algebraMap k K (v i)) (algebraMap_comp_ne_zero hv),
    (mem_projectivePoints_mk hF' _ _).mpr (by rw [aeval_algebraMap_comp, hvF, map_zero])⟩
  locally_polynomial K _ _ _ := ⟨0, fun i => C (v i), fun i => isHomogeneous_C _ _,
    by simpa only [aeval_C] using algebraMap_comp_ne_zero hv, fun Q hQ => by
      show Projectivization.mk K _ _ = _
      congr 1
      funext i
      exact (aeval_C _ _).symm⟩

theorem ProjRegularMap.const_apply {d : ℕ} (hF' : F'.IsHomogeneous d) (v : Fin 3 → k) (hv : v ≠ 0)
    (hvF : aeval v F' = 0) (K : Type u) [Field K] [Algebra k K] (P : projectivePoints F K) :
    ((ProjRegularMap.const (F := F) hF' v hv hvF).toFun K P).1 =
      Projectivization.mk K (fun i => algebraMap k K (v i)) (algebraMap_comp_ne_zero hv) := rfl

open Classical in
/-- Gluing two regular maps along a property of the field: `φ₁` over the fields `K` with `p K`, `φ₂` over the
others. A `ProjRegularMap` imposes no compatibility between different fields, so this is again one. -/
def ProjRegularMap.ite (p : ∀ (K : Type u) [Field K] [Algebra k K], Prop) (φ₁ φ₂ : ProjRegularMap F F') :
    ProjRegularMap F F' where
  toFun K _ _ := if p K then φ₁.toFun K else φ₂.toFun K
  locally_polynomial K _ _ P := by
    by_cases h : p K
    · simp only [h, ite_true]
      exact φ₁.locally_polynomial K P
    · simp only [h, ite_false]
      exact φ₂.locally_polynomial K P

open Classical in
theorem ProjRegularMap.ite_toFun (p : ∀ (K : Type u) [Field K] [Algebra k K], Prop)
    (φ₁ φ₂ : ProjRegularMap F F') (K : Type u) [Field K] [Algebra k K] :
    (ProjRegularMap.ite p φ₁ φ₂).toFun K = if p K then φ₁.toFun K else φ₂.toFun K := rfl

/-- The vector $(0, 0, 1)$. -/
def vecZ : Fin 3 → k := ![0, 0, 1]

theorem vecZ_ne_zero : (vecZ : Fin 3 → k) ≠ 0 := by
  intro h
  have := congrFun h 2
  simp [vecZ] at this

/-- The vector $(0, 1, 0)$. -/
def vecY : Fin 3 → k := ![0, 1, 0]

theorem vecY_ne_zero : (vecY : Fin 3 → k) ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [vecY] at this

/-- The constant map onto $(0 : 0 : 1)$ extends the constant affine map onto $(0, 0)$. -/
theorem ProjRegularMap.const_vecZ_extends {d : ℕ} (hF' : F'.IsHomogeneous d) (hvF : aeval vecZ F' = 0) :
    (ProjRegularMap.const (F := F) hF' vecZ vecZ_ne_zero hvF).Extends (fun _ => 0) := by
  intro K _ _ P hP hP'
  rw [ProjRegularMap.const_apply]
  obtain ⟨c, hc, hvc⟩ := exists_smul_rep (fun i => algebraMap k K (vecZ i)) (algebraMap_comp_ne_zero vecZ_ne_zero)
  set w := (Projectivization.mk K (fun i => algebraMap k K (vecZ i))
    (algebraMap_comp_ne_zero vecZ_ne_zero)).rep
  have h0 := congrFun hvc 0
  have h1 := congrFun hvc 1
  have h2 := congrFun hvc 2
  simp only [vecZ, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_zero, map_one] at h0 h1 h2
  have hw0 : w 0 = 0 := (mul_eq_zero.mp h0.symm).resolve_left hc
  have hw1 : w 1 = 0 := (mul_eq_zero.mp h1.symm).resolve_left hc
  have hw2 : w 2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at h2
    exact one_ne_zero h2
  refine ⟨hw2, ?_⟩
  have e0 : evalCoord hP' (0 : coordinateRing (dehomogenize 2 F)) = 0 := map_zero _
  rw [e0]
  show (w 0 / w 2, w 1 / w 2) = (0, 0)
  rw [hw0, hw1, zero_div]

end General

/-! ### The counterexample over $\mathbb F_3$ -/

section Counterexample

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The curve $C : Y^2Z = X^3 - XZ^2 - Z^3$ over $\mathbb F_3$. -/
abbrev cexC : MvPolynomial (Fin 3) (ZMod 3) := weierstrassCubic (-1) (-1)

/-- The curve $C' : Y^2Z = X^3 - XZ^2$ over $\mathbb F_3$. -/
abbrev cexC' : MvPolynomial (Fin 3) (ZMod 3) := weierstrassCubic (-1) 0

theorem ringChar_zmod_three_ne_two : ringChar (ZMod 3) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  decide

theorem cex_disc : (4 * (-1) ^ 3 + 27 * (-1) ^ 2 : ZMod 3) ≠ 0 := by decide

theorem cex_disc' : (4 * (-1) ^ 3 + 27 * 0 ^ 2 : ZMod 3) ≠ 0 := by decide

/-- $C(\mathbb F_3)$ has no point in the affine piece $Z \ne 0$: $y^2 = x^3 - x - 1 = -1$ has no solution. -/
theorem rep_two_eq_zero_of_mem (P : ℙ (ZMod 3) (Fin 3 → ZMod 3)) (hP : P ∈ projectivePoints cexC (ZMod 3)) :
    P.rep 2 = 0 := by
  by_contra h
  have hP' : aeval P.rep cexC = 0 := hP
  rw [aeval_weierstrassCubic] at hP'
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hP'
  have key : ∀ x y z : ZMod 3, z ≠ 0 → y ^ 2 * z - (x ^ 3 + -1 * x * z ^ 2 + -1 * z ^ 3) ≠ 0 := by decide
  exact key _ _ _ h hP'

theorem aeval_vecZ_cexC' : aeval (vecZ : Fin 3 → ZMod 3) cexC' = 0 := by
  rw [aeval_weierstrassCubic]
  simp [vecZ]

theorem aeval_vecY_cexC' : aeval (vecY : Fin 3 → ZMod 3) cexC' = 0 := by
  rw [aeval_weierstrassCubic]
  simp [vecY]

/-- The constant affine map onto $(0, 0)$ is a regular map of the affine pieces. -/
theorem cex_isAffineRegularMap :
    IsAffineRegularMap (dehomogenize 2 cexC) (dehomogenize 2 cexC') (fun _ => 0) := by
  intro K _ _ P hP
  have e0 : evalCoord hP (0 : coordinateRing (dehomogenize 2 cexC)) = 0 := map_zero _
  simp only [e0]
  show evalAt (dehomogenize 2 cexC') (0, 0) = 0
  rw [(example_1_16.{0, 0} (-1 : ZMod 3) 0).1]
  simp [evalAt]

/-- The fields `K` over which $C(K)$ has a point in the affine piece $Z \ne 0$. -/
def HasAffinePoint (K : Type) [Field K] [Algebra (ZMod 3) K] : Prop :=
  ∃ Q ∈ projectivePoints cexC K, Q.rep 2 ≠ 0

/-- The constant map onto $(0 : 0 : 1)$. -/
def cexφ : ProjRegularMap cexC cexC' :=
  ProjRegularMap.const (weierstrassCubic_isHomogeneous _ _) vecZ vecZ_ne_zero aeval_vecZ_cexC'

/-- $(0 : 0 : 1)$ over the fields where $C$ has an affine point, $(0 : 1 : 0)$ over the others. -/
def cexψ : ProjRegularMap cexC cexC' :=
  ProjRegularMap.ite (fun K _ _ => HasAffinePoint K) cexφ
    (ProjRegularMap.const (weierstrassCubic_isHomogeneous _ _) vecY vecY_ne_zero aeval_vecY_cexC')

theorem cexφ_extends : cexφ.Extends (fun _ => 0) :=
  ProjRegularMap.const_vecZ_extends _ _

open Classical in
theorem cexψ_extends : cexψ.Extends (fun _ => 0) := by
  intro K _ _ P hP hP'
  have hK : HasAffinePoint K := ⟨P.1, P.2, hP⟩
  have e : cexψ.toFun K = cexφ.toFun K := by
    rw [cexψ, ProjRegularMap.ite_toFun, ite_eq_left hK]
  rw [e]
  exact cexφ_extends K P hP hP'

/-- The point $(0 : 1 : 0)$ of $C(\mathbb F_3)$. -/
def cexO : projectivePoints cexC (ZMod 3) :=
  ⟨pointAtInfinity (ZMod 3), ((example_1_15 (-1 : ZMod 3) (-1) (ZMod 3) _).mpr rfl).1⟩

/-- The two extensions differ at $(0 : 1 : 0)$ over $\mathbb F_3$. -/
theorem cexψ_ne_cexφ : cexψ.toFun (ZMod 3) cexO ≠ cexφ.toFun (ZMod 3) cexO := by
  classical
  have hK : ¬ HasAffinePoint (ZMod 3) := by
    rintro ⟨Q, hQ, h2⟩
    exact h2 (rep_two_eq_zero_of_mem Q hQ)
  intro h
  have h' := congrArg Subtype.val h
  rw [cexψ, ProjRegularMap.ite_toFun, ite_eq_right hK, ProjRegularMap.const_apply, cexφ,
    ProjRegularMap.const_apply, Projectivization.mk_eq_mk_iff] at h'
  obtain ⟨a, ha⟩ := h'
  have := congrFun ha 1
  simp [vecY, vecZ] at this

/-- **The conclusion of Example 4.20 fails** for $C \to C'$ over $\mathbb F_3$ and the constant affine map onto
$(0, 0)$: no extension is unique on the points over every field. -/
theorem not_example_4_20_conclusion :
    ¬ ∃ φ : ProjRegularMap cexC cexC', φ.Extends (fun _ => 0) ∧
      ∀ ψ : ProjRegularMap cexC cexC', ψ.Extends (fun _ => 0) →
        ∀ (K : Type) [Field K] [Algebra (ZMod 3) K], ψ.toFun K = φ.toFun K := by
  rintro ⟨φ₀, -, h⟩
  apply cexψ_ne_cexφ
  rw [h cexψ cexψ_extends (ZMod 3), h cexφ cexφ_extends (ZMod 3)]

/-- **The named statement `Prop4_18` is false** (counterexample over $\mathbb F_3$; see the module docstring). -/
theorem not_prop4_18 : ¬ Prop4_18 := fun h =>
  not_example_4_20_conclusion
    (example_4_20 h ringChar_zmod_three_ne_two cex_disc cex_disc' _ cex_isAffineRegularMap)

end Counterexample

/-! ### The corrected statement -/

/-- **Proposition 4.18, corrected** (p. 48), as a named statement: a regular map $C \cap U_2 \to C' \cap U_2$ of the
affine pieces of nonsingular projective plane curves extends to a regular map $C \to C'$, and the extension is unique
on the points over every algebraically closed field `K ⊇ k`. (Uniqueness over every field `K` is false:
`not_prop4_18`.) -/
@[kb "milne2006ec" "Ch. I, Prop. 4.18, pdf p. 48 (corrected: uniqueness over algebraically closed fields)"]
structure Prop4_18Corrected : Prop where
  extends_unique : ∀ (k : Type) [Field k] [PerfectField k] (F F' : MvPolynomial (Fin 3) k),
    IsProjectivePlaneCurve F → IsNonsingularProjCurve F → IsProjectivePlaneCurve F' →
    IsNonsingularProjCurve F' → ¬ F ∣ X 2 → ¬ F' ∣ X 2 →
    ∀ f, IsAffineRegularMap (dehomogenize 2 F) (dehomogenize 2 F') f →
      ∃ φ : ProjRegularMap F F', φ.Extends f ∧
        ∀ ψ : ProjRegularMap F F', ψ.Extends f →
          ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra k K], ψ.toFun K = φ.toFun K

/-- **Example 4.20, corrected** (p. 49), first part, from `Prop4_18Corrected`: every regular map of affine
Weierstrass curves $E(a, b)^{\mathrm{aff}} \to E(a', b')^{\mathrm{aff}}$ extends to $E(a, b) \to E(a', b')$, uniquely on
the points over algebraically closed fields. -/
@[kb "milne2006ec" "Ch. I, Ex. 4.20, pdf p. 49 (corrected uniqueness)"]
theorem example_4_20_corrected (h : Prop4_18Corrected) {k : Type} [Field k] [PerfectField k]
    (hk : ringChar k ≠ 2) {a b a' b' : k} (hab : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (hab' : 4 * a' ^ 3 + 27 * b' ^ 2 ≠ 0)
    (f : Fin 2 → coordinateRing (dehomogenize 2 (weierstrassCubic a b)))
    (hf : IsAffineRegularMap (dehomogenize 2 (weierstrassCubic a b))
      (dehomogenize 2 (weierstrassCubic a' b')) f) :
    ∃ φ : ProjRegularMap (weierstrassCubic a b) (weierstrassCubic a' b'), φ.Extends f ∧
      ∀ ψ : ProjRegularMap (weierstrassCubic a b) (weierstrassCubic a' b'), ψ.Extends f →
        ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra k K], ψ.toFun K = φ.toFun K :=
  h.extends_unique k _ _ (isProjectivePlaneCurve_weierstrass hk a b)
    (isNonsingularProjCurve_weierstrass hk hab) (isProjectivePlaneCurve_weierstrass hk a' b')
    (isNonsingularProjCurve_weierstrass hk hab') (weierstrassCubic_not_dvd_X a b)
    (weierstrassCubic_not_dvd_X a' b') f hf

end NumberFieldKB.MilneEC
