import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.QuaternionSO3

/-!
# Quaternion algebras with isometric pure norm forms are isomorphic

For a field $K$ with $2 \ne 0$ and $a, b \in K^\times$, let $H(a,b) = (a,b)_K$ = `ℍ[K,a,b]` (Mathlib's
`QuaternionAlgebra K a 0 b`: $i^2 = a$, $j^2 = b$, $ij = -ji = k$) and let
$\langle -a, -b, ab\rangle$ = QuadFormsKB `Quat.pureForm a b` be the reduced norm restricted to the pure quaternions
$Ki + Kj + Kk$ (QuadFormsKB `Quat.nrd_pure`).

* `nonempty_algEquiv_of_pureForm_isometric`: if $\langle -a,-b,ab\rangle \cong \langle -c,-d,cd\rangle$ over $K$, then
  $H(c,d) \cong H(a,b)$ as $K$-algebras.
* `pureForm_isometric_of_algEquiv`: conversely, a $K$-algebra isomorphism $H(c,d) \cong H(a,b)$ gives an isometry
  $\langle -a,-b,ab\rangle \cong \langle -c,-d,cd\rangle$.

*Proof idea.* An isometry sends the orthogonal basis $e_0, e_1$ of $\langle -c,-d,cd\rangle$ to pure quaternions
$u, v \in H(a,b)$ with $\operatorname{nrd} u = -c$, $\operatorname{nrd} v = -d$ and $\operatorname{nrd}(u+v) = -c-d$;
for a pure quaternion $x^2 = -\operatorname{nrd} x$, so $u^2 = c$, $v^2 = d$, $uv = -vu$. Mathlib's
`QuaternionAlgebra.Basis.liftHom` gives an algebra map $H(c,d) \to H(a,b)$; it is injective (its kernel is a two-sided
ideal, and a nonzero element of $H(c,d)$ times a suitable basis vector has nonzero scalar part, so the kernel would
contain a nonzero scalar), hence bijective by dimension ($4 = 4$). Conversely an algebra isomorphism preserves the set
of pure quaternions ($x \ne 0$ is pure iff $x^2 \in K$ and $x \notin K$) and $x^2 = -\operatorname{nrd} x$ on it.

Sources: Voight, *Quaternion Algebras* (2021), §5.2, Prop. 5.2.? (quaternion algebras are classified by the
similarity class of the ternary norm form) [unverified locator]; Lam, *Introduction to Quadratic Forms over Fields*
(2005), Ch. III, Thm. 2.5 [unverified locator]. Used for Milne, *Class Field Theory*, VIII, Example 4.4(b)
(`NumberFieldKB.MilneCFT.Ch8.example_4_4b_algEquiv_of_ramified_eq`).
-/

open Quaternion QuadFormsKB
open scoped Matrix

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {K : Type*} [Field K]

/-- A pure quaternion squares to the scalar $-Q_3$. -/
theorem pure_mul_self_aux {a b : K} (z : Fin 3 → K) :
    (Quat.pure z : ℍ[K,a,b]) * Quat.pure z = ((-(Quat.Q3 a b z) : K) : ℍ[K,a,b]) := by
  ext <;> simp only [QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe,
    QuaternionAlgebra.imK_coe] <;> simp [Quat.pure, Quat.Q3] <;> ring

/-- If a $K$-algebra map out of $(c,d)_K$ kills `y`, then `y` has zero real part. -/
theorem re_eq_zero_of_map_eq_zero_aux (h2 : (2 : K) ≠ 0) {a b c d : K} (hc : c ≠ 0) (hd : d ≠ 0)
    (φ : ℍ[K,c,d] →ₐ[K] ℍ[K,a,b]) {y : ℍ[K,c,d]} (hy : φ y = 0) : y.re = 0 := by
  have key : (4 * y.re) • (1 : ℍ[K,c,d]) = y + c⁻¹ • ((⟨0,1,0,0⟩ : ℍ[K,c,d]) * y * ⟨0,1,0,0⟩)
      + d⁻¹ • ((⟨0,0,1,0⟩ : ℍ[K,c,d]) * y * ⟨0,0,1,0⟩)
      - (c * d)⁻¹ • ((⟨0,0,0,1⟩ : ℍ[K,c,d]) * y * ⟨0,0,0,1⟩) := by
    ext <;> simp <;> field_simp <;> ring
  have h := congrArg φ key
  simp only [map_smul, map_one, map_sub, map_add, map_mul, hy, mul_zero, zero_mul, smul_zero,
    add_zero, sub_zero] at h
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  rcases smul_eq_zero.mp h with h | h
  · exact (mul_eq_zero.mp h).resolve_left h4
  · exact absurd h one_ne_zero

/-- A $K$-algebra map $(c,d)_K \to (a,b)_K$ is injective. -/
theorem injective_of_algHom_aux (h2 : (2 : K) ≠ 0) {a b c d : K} (hc : c ≠ 0) (hd : d ≠ 0)
    (φ : ℍ[K,c,d] →ₐ[K] ℍ[K,a,b]) : Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h0 := re_eq_zero_of_map_eq_zero_aux h2 hc hd φ hx
  have h1 := re_eq_zero_of_map_eq_zero_aux h2 hc hd φ
    (y := x * ⟨0,1,0,0⟩) (by rw [map_mul, hx, zero_mul])
  have h2' := re_eq_zero_of_map_eq_zero_aux h2 hc hd φ
    (y := x * ⟨0,0,1,0⟩) (by rw [map_mul, hx, zero_mul])
  have h3 := re_eq_zero_of_map_eq_zero_aux h2 hc hd φ
    (y := x * ⟨0,0,0,1⟩) (by rw [map_mul, hx, zero_mul])
  simp at h1 h2' h3
  ext <;> simp [h0] <;> tauto

/-- An algebra equivalence of quaternion algebras maps pure quaternions to elements of real part $0$. -/
theorem re_map_pure_aux (h2 : (2 : K) ≠ 0) {a b c d : K}
    (e : ℍ[K,c,d] ≃ₐ[K] ℍ[K,a,b]) (z : Fin 3 → K) : (e (Quat.pure z)).re = 0 := by
  have hsq : e (Quat.pure z) * e (Quat.pure z) = ((-(Quat.Q3 c d z) : K) : ℍ[K,a,b]) := by
    rw [← map_mul, pure_mul_self_aux]
    exact e.commutes (-(Quat.Q3 c d z))
  set y := e (Quat.pure z) with hyd
  have hco : 2 * y.re * y.imI = 0 ∧ 2 * y.re * y.imJ = 0 ∧ 2 * y.re * y.imK = 0 := by
    refine ⟨?_, ?_, ?_⟩
    · have := congrArg QuaternionAlgebra.imI hsq; simp at this; linear_combination this
    · have := congrArg QuaternionAlgebra.imJ hsq; simp at this; linear_combination this
    · have := congrArg QuaternionAlgebra.imK hsq; simp at this; linear_combination this
  by_contra hre
  have h2r : 2 * y.re ≠ 0 := mul_ne_zero h2 hre
  have hI := (mul_eq_zero.mp hco.1).resolve_left h2r
  have hJ := (mul_eq_zero.mp hco.2.1).resolve_left h2r
  have hK := (mul_eq_zero.mp hco.2.2).resolve_left h2r
  have hy : y = ((y.re : K) : ℍ[K,a,b]) := by ext <;> simp [hI, hJ, hK]
  have : Quat.pure z = ((y.re : K) : ℍ[K,c,d]) := by
    apply e.injective
    rw [← hyd, hy]
    exact (e.commutes y.re).symm
  have h0 := congrArg QuaternionAlgebra.re this
  simp [Quat.pure] at h0
  exact hre h0.symm

/-- **Isometric pure norm forms give isomorphic quaternion algebras:** for $a, b, c, d \in K^\times$, $2 \ne 0$ in
$K$, if $\langle -a,-b,ab\rangle \cong \langle -c,-d,cd\rangle$ over $K$ then $(c,d)_K \cong (a,b)_K$. -/
@[kb "voight2021" "§5.2 [unverified]"]
theorem nonempty_algEquiv_of_pureForm_isometric (h2 : (2 : K) ≠ 0) {a b c d : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (h : (Quat.pureForm a b).IsometricIn K (Quat.pureForm c d)) :
    Nonempty (ℍ[K,c,d] ≃ₐ[K] ℍ[K,a,b]) := by
  obtain ⟨P, -, hP⟩ := h
  have hQ : ∀ x, Quat.Q3 a b (P *ᵥ x) = Quat.Q3 c d x := fun x => by
    rw [← Quat.eval_pureForm, ← Quat.eval_pureForm]; exact hP x
  set y0 : Fin 3 → K := P *ᵥ Pi.single 0 1 with hy0
  set y1 : Fin 3 → K := P *ᵥ Pi.single 1 1 with hy1
  have e0 : Quat.Q3 a b y0 = -c := by rw [hy0, hQ]; simp [Quat.Q3]
  have e1 : Quat.Q3 a b y1 = -d := by rw [hy1, hQ]; simp [Quat.Q3]
  have ew : Quat.Q3 a b (y0 + y1) = -c - d := by
    have : y0 + y1 = P *ᵥ (Pi.single 0 1 + Pi.single 1 1) := by
      rw [Matrix.mulVec_add]
    rw [this, hQ]
    simp [Quat.Q3, Pi.add_apply]
  set u : ℍ[K,a,b] := Quat.pure y0 with hu
  set v : ℍ[K,a,b] := Quat.pure y1 with hv
  have huu : u * u = ((c : K) : ℍ[K,a,b]) := by
    rw [hu, pure_mul_self_aux, e0, neg_neg]
  have hvv : v * v = ((d : K) : ℍ[K,a,b]) := by
    rw [hv, pure_mul_self_aux, e1, neg_neg]
  have hanti : v * u + u * v = 0 := by
    have h1 : (u + v) * (u + v) = ((c + d : K) : ℍ[K,a,b]) := by
      have : u + v = Quat.pure (y0 + y1) := by rw [Quat.pure_add]
      rw [this, pure_mul_self_aux, ew]; congr 1; ring
    have h2 : v * u + u * v = (u + v) * (u + v) - u * u - v * v := by noncomm_ring
    rw [h2, h1, huu, hvv]
    ext <;> simp
  let B : QuaternionAlgebra.Basis ℍ[K,a,b] c 0 d :=
    { i := u
      j := v
      k := u * v
      i_mul_i := by
        rw [huu, zero_smul, add_zero]; ext <;> simp
      j_mul_j := by
        rw [hvv]; ext <;> simp
      i_mul_j := rfl
      j_mul_i := by
        rw [zero_smul, zero_sub]; exact eq_neg_of_add_eq_zero_left hanti }
  have hinj : Function.Injective B.liftHom := injective_of_algHom_aux h2 hc hd _
  have hsurj : Function.Surjective B.liftHom := by
    have : Function.Injective B.liftHom.toLinearMap := hinj
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [QuaternionAlgebra.finrank_eq_four, QuaternionAlgebra.finrank_eq_four])).1 this
  exact ⟨AlgEquiv.ofBijective B.liftHom ⟨hinj, hsurj⟩⟩

/-- **Isomorphic quaternion algebras have isometric pure norm forms:** a $K$-algebra isomorphism
$(c,d)_K \cong (a,b)_K$ gives $\langle -a,-b,ab\rangle \cong \langle -c,-d,cd\rangle$ over $K$. -/
@[kb "voight2021" "§5.2 [unverified]"]
theorem pureForm_isometric_of_algEquiv (h2 : (2 : K) ≠ 0) {a b c d : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (e : ℍ[K,c,d] ≃ₐ[K] ℍ[K,a,b]) :
    (Quat.pureForm a b).IsometricIn K (Quat.pureForm c d) := by
  let L : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    { toFun := fun y => Quat.imv (e (Quat.pure y))
      map_add' := fun y z => by rw [Quat.pure_add, map_add, Quat.imv_add]
      map_smul' := fun r y => by
        rw [Quat.pure_smul, map_smul, Quat.imv_smul]; rfl }
  have hL : ∀ y, (Quat.pure (L y) : ℍ[K,a,b]) = e (Quat.pure y) := fun y =>
    Quat.pure_imv (re_map_pure_aux h2 e y)
  refine ⟨LinearMap.toMatrix' L, ?_, fun y => ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have hx : ∀ z, (LinearMap.toMatrix' L) *ᵥ z = L z := fun z => by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    have h1 : L x = L y := by rw [← hx, ← hx]; exact hxy
    have h2' : e (Quat.pure x) = e (Quat.pure y) := by rw [← hL, ← hL, h1]
    have h3 := e.injective h2'
    have := congrArg Quat.imv h3
    simpa using this
  · have hx : (LinearMap.toMatrix' L) *ᵥ y = L y := by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rw [hx]
    show (Quat.pureForm a b).eval (L y) = (Quat.pureForm c d).eval y
    rw [Quat.eval_pureForm, Quat.eval_pureForm]
    have h1 : e (Quat.pure y) * e (Quat.pure y) = ((-(Quat.Q3 c d y) : K) : ℍ[K,a,b]) := by
      rw [← map_mul, pure_mul_self_aux]
      exact e.commutes (-(Quat.Q3 c d y))
    rw [← hL, pure_mul_self_aux] at h1
    have := QuaternionAlgebra.coe_injective h1
    exact neg_inj.mp this

end NumberFieldKB.MilneCFT.Ch8
