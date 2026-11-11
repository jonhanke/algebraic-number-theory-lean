import NumberFieldKB.MilneCFT.Ch8.Speiser
import QuadFormsKB.Lattices.Genus
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Galois descent for quadratic forms (for Milne, *Class Field Theory*, VIII, Remark 6.4)

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §6,
Remark 6.4 (pdf p. 261, printed p. 252). Milne reads Hasse–Minkowski as the injectivity of
$H^1(K, O) \to \prod_v H^1(K_v, O)$; that reading rests on the classical dictionary between $H^1(\operatorname{Gal}(L/K),
O_Q(L))$ and the quadratic forms over $K$ that become isometric to $Q$ over $L$ (Serre, *Galois Cohomology*, III, §1;
Serre, *Local Fields*, X, §2). This file proves that dictionary for a finite Galois extension $L/K$ of a number field
$K$ and a form $Q$ = `Q : QuadForm K n` (QuadFormsKB's forms; $O_Q(L)$ = QuadFormsKB `Lattices.orthGroup Q L`, the
$g \in \mathrm{GL}_n(L)$ with $g^{\mathsf T} H g = H$ for the Hessian $H$ of $Q$).

## What is formalized

* `IsOrthCocycle Q a`: $a : \operatorname{Gal}(L/K) \to \mathrm{GL}_n(L)$ is a crossed homomorphism with values in
  $O_Q(L)$; `OrthCohomologous Q a a'`: $a'(\sigma) = c^{-1} a(\sigma)\, \sigma(c)$ for some $c \in O_Q(L)$.
* `twistCocycle P`: the cocycle $\sigma \mapsto P\,\sigma(P)^{-1}$ of a form $Q'$ over $K$ with $Q(P\vec x) = Q'(\vec x)$
  over $L$ (`twistCocycle_isOrthCocycle`).
* **Galois descent** (`galois_descent_exists`, `galois_descent_cohomologous_iff`): every $O_Q(L)$-valued cocycle is
  `twistCocycle P` for such a pair $(Q', P)$ (uses Speiser's Hilbert 90, `speiser_hilbert90`); and two twists are
  cohomologous in $O_Q(L)$ iff the forms are isometric over $K$. Hence $Q' \mapsto [\sigma \mapsto P\sigma(P)^{-1}]$ is a
  bijection from the $K$-isometry classes of forms over $K$ that become isometric to $Q$ over $L$ onto
  $H^1(\operatorname{Gal}(L/K), O_Q(L))$.

*Convention.* Everything is phrased through Hessians ($Q(\vec x) = \tfrac12 \vec x^{\mathsf T} H \vec x$), which is
legitimate in characteristic $0$ (`isometricIn_iff_hessian`). Indices are 0-based (`Fin n`).
-/

open Matrix QuadFormsKB QuadFormsKB.Lattices

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {n : ℕ}

/-! ### Hessians and isometry in characteristic 0 -/

section Hessian

variable {K : Type*} [Field K]

/-- The Hessian of a form is symmetric. -/
theorem hessian_transpose (Q : QuadForm K n) : Q.hessianᵀ = Q.hessian := by
  simp [QuadForm.hessian, add_comm]

/-- $2Q(\vec x) = \vec x^{\mathsf T} H \vec x$ over any $K$-algebra. -/
theorem two_mul_evalIn' {F : Type*} [CommRing F] [Algebra K F] (Q : QuadForm K n) (x : Fin n → F) :
    2 * Q.evalIn F x = x ⬝ᵥ (Q.hessian.map (algebraMap K F) *ᵥ x) := by
  have h := QuadForm.polar_eq_hessian F Q x x
  have h2 : x + x = (2 : F) • x := (two_smul F x).symm
  have hs : Q.evalIn F ((2 : F) • x) = 2 ^ 2 * Q.evalIn F x := by
    rw [QuadForm.evalIn_eq_dotProduct, QuadForm.evalIn_eq_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  rw [h2, hs] at h
  linear_combination h

/-- **Isometry over a field of characteristic $0$ is congruence of Hessians:** $Q(P\vec x) = Q'(\vec x)$ for all
$\vec x \in F^n$ iff $P^{\mathsf T} H P = H'$. -/
theorem evalIn_iff_hessian {F : Type*} [Field F] [CharZero F] [Algebra K F] (Q Q' : QuadForm K n)
    (P : Matrix (Fin n) (Fin n) F) :
    (∀ x, Q.evalIn F (P *ᵥ x) = Q'.evalIn F x) ↔
      Pᵀ * Q.hessian.map (algebraMap K F) * P = Q'.hessian.map (algebraMap K F) := by
  constructor
  · intro h
    have key : ∀ x y : Fin n → F, x ⬝ᵥ (Q'.hessian.map (algebraMap K F) *ᵥ y) =
        x ⬝ᵥ ((Pᵀ * Q.hessian.map (algebraMap K F) * P) *ᵥ y) := by
      intro x y
      have h1 := QuadForm.polar_eq_hessian F Q' x y
      have h2 := QuadForm.polar_eq_hessian F Q (P *ᵥ x) (P *ᵥ y)
      rw [← h1, ← h x, ← h y, ← h (x + y), Matrix.mulVec_add, h2, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Pᵀ, Matrix.vecMul_transpose]
    ext i j
    have := key (Pi.single i 1) (Pi.single j 1)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this.symm
  · intro h x
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    apply mul_left_cancel₀ h2
    have e : x ⬝ᵥ ((Pᵀ * Q.hessian.map (algebraMap K F) * P) *ᵥ x) =
        (P *ᵥ x) ⬝ᵥ (Q.hessian.map (algebraMap K F) *ᵥ (P *ᵥ x)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [two_mul_evalIn', two_mul_evalIn', ← h, e]

/-- `IsometricIn` over a field of characteristic $0$ through Hessians. -/
theorem isometricIn_iff_hessian (F : Type*) [Field F] [CharZero F] [Algebra K F] (Q Q' : QuadForm K n) :
    Q.IsometricIn F Q' ↔ ∃ P : GL (Fin n) F,
      (P : Matrix (Fin n) (Fin n) F)ᵀ * Q.hessian.map (algebraMap K F) * P = Q'.hessian.map (algebraMap K F) := by
  constructor
  · rintro ⟨P, hP, h⟩
    refine ⟨((Matrix.isUnit_iff_isUnit_det P).mpr hP).unit, ?_⟩
    rw [IsUnit.unit_spec]
    exact (evalIn_iff_hessian Q Q' P).mp h
  · rintro ⟨P, h⟩
    refine ⟨(P : Matrix (Fin n) (Fin n) F),
      (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit P), ?_⟩
    exact (evalIn_iff_hessian Q Q' (P : Matrix (Fin n) (Fin n) F)).mpr h

/-- A symmetric matrix is the Hessian of a form (characteristic $\ne 2$): $c_{ii} = M_{ii}/2$, $c_{ij} = M_{ij}$
for $i < j$. -/
theorem exists_hessian_eq [CharZero K] (M : Matrix (Fin n) (Fin n) K) (hM : Mᵀ = M) :
    ∃ Q : QuadForm K n, Q.hessian = M := by
  refine ⟨QuadForm.ofUpper fun i j => if i = j then M i i / 2 else M i j, ?_⟩
  ext i j
  simp only [QuadForm.hessian, QuadForm.ofUpper, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [if_pos h.le, if_neg h.ne, if_neg (not_le.mpr h), add_zero]
  · simp only [le_refl, if_true]
    ring
  · rw [if_neg (not_le.mpr h), if_pos h.le, if_neg h.ne, zero_add]
    exact (Matrix.transpose_apply M i j).symm.trans (congrFun (congrFun hM i) j)

end Hessian

/-! ### The congruence action $S \mapsto g^{\mathsf T} S g$ -/

section Cong

variable {E : Type*} [Field E]

/-- The congruence action of $g \in \mathrm{GL}_n(E)$ on matrices: $S \mapsto g^{\mathsf T} S g$. -/
def cong (g : GL (Fin n) E) (S : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  (g : Matrix (Fin n) (Fin n) E)ᵀ * S * g

theorem cong_mul (g h : GL (Fin n) E) (S : Matrix (Fin n) (Fin n) E) :
    cong (g * h) S = cong h (cong g S) := by
  simp only [cong, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem cong_one (S : Matrix (Fin n) (Fin n) E) : cong 1 S = S := by
  simp [cong]

theorem cong_inv_mul (g : GL (Fin n) E) (S : Matrix (Fin n) (Fin n) E) : cong g⁻¹ (cong g S) = S := by
  rw [← cong_mul, mul_inv_cancel, cong_one]

theorem cong_mul_inv (g : GL (Fin n) E) (S : Matrix (Fin n) (Fin n) E) : cong g (cong g⁻¹ S) = S := by
  rw [← cong_mul, inv_mul_cancel, cong_one]

theorem cong_map {E' : Type*} [Field E'] (f : E →+* E') (g : GL (Fin n) E) (S : Matrix (Fin n) (Fin n) E) :
    (cong g S).map f = cong (Matrix.GeneralLinearGroup.map f g) (S.map f) := by
  simp only [cong, Matrix.map_mul, Matrix.transpose_map]
  rfl

end Cong

/-! ### Cocycles with values in the orthogonal group -/

variable {K L : Type*} [Field K] [NumberField K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Galois conjugation of a matrix commutes with `map (algebraMap K L)`. -/
theorem map_algebraMap_galois (σ : L ≃ₐ[K] L) (M : Matrix (Fin n) (Fin n) K) :
    (M.map (algebraMap K L)).map σ = M.map (algebraMap K L) := by
  ext i j
  simp

/-- $\sigma$ preserves $O_Q(L)$. -/
theorem galGL_mem_orthGroup (Q : QuadForm K n) (σ : L ≃ₐ[K] L) {g : GL (Fin n) L}
    (hg : g ∈ orthGroup Q L) : galGL σ g ∈ orthGroup Q L := by
  rw [mem_orthGroup] at hg ⊢
  have := congrArg (fun M => M.map σ) hg
  simp only [Matrix.map_mul, Matrix.transpose_map, map_algebraMap_galois] at this
  exact this

/-- A crossed homomorphism $\operatorname{Gal}(L/K) \to O_Q(L)$ (Milne, *CFT*, VIII, Remark 6.4, the elements of
$H^1(\operatorname{Gal}(L/K), O)$). -/
def IsOrthCocycle (Q : QuadForm K n) (a : (L ≃ₐ[K] L) → GL (Fin n) L) : Prop :=
  IsGLCocycle a ∧ ∀ σ, a σ ∈ orthGroup Q L

/-- Two crossed homomorphisms with values in $O_Q(L)$ are **cohomologous**: $a'(\sigma) = c^{-1} a(\sigma)\,\sigma(c)$
for some $c \in O_Q(L)$. -/
def OrthCohomologous (Q : QuadForm K n) (a a' : (L ≃ₐ[K] L) → GL (Fin n) L) : Prop :=
  ∃ c ∈ orthGroup Q L, ∀ σ, a' σ = c⁻¹ * a σ * galGL σ c

/-- The cocycle $\sigma \mapsto P\,\sigma(P)^{-1}$ attached to $P \in \mathrm{GL}_n(L)$. -/
def twistCocycle (P : GL (Fin n) L) : (L ≃ₐ[K] L) → GL (Fin n) L := fun σ => P * (galGL σ P)⁻¹

theorem galGL_mul (σ τ : L ≃ₐ[K] L) (g : GL (Fin n) L) : galGL (σ * τ) g = galGL σ (galGL τ g) := by
  ext i j
  rfl

theorem twistCocycle_isGLCocycle (P : GL (Fin n) L) : IsGLCocycle (twistCocycle (K := K) P) := by
  intro σ τ
  simp only [twistCocycle, map_mul, map_inv, galGL_mul]
  group

/-- A pair $(Q', P)$ with $Q'$ over $K$ and $P^{\mathsf T} H_Q P = H_{Q'}$ over $L$, i.e. $Q(P\vec x) = Q'(\vec x)$
(a **twist** of $Q$ split by $L$). -/
def IsTwist (Q Q' : QuadForm K n) (P : GL (Fin n) L) : Prop :=
  (P : Matrix (Fin n) (Fin n) L)ᵀ * Q.hessian.map (algebraMap K L) * P = Q'.hessian.map (algebraMap K L)

theorem isTwist_galGL {Q Q' : QuadForm K n} {P : GL (Fin n) L} (h : IsTwist Q Q' P) (σ : L ≃ₐ[K] L) :
    IsTwist Q Q' (galGL σ P) := by
  have := congrArg (fun M => M.map σ) h
  simp only [Matrix.map_mul, Matrix.transpose_map, map_algebraMap_galois] at this
  exact this

/-- **The cocycle of a twist** has values in $O_Q(L)$. -/
theorem twistCocycle_isOrthCocycle {Q Q' : QuadForm K n} {P : GL (Fin n) L} (h : IsTwist Q Q' P) :
    IsOrthCocycle Q (twistCocycle (K := K) P) := by
  refine ⟨twistCocycle_isGLCocycle P, fun σ => ?_⟩
  rw [mem_orthGroup]
  have h' : cong (galGL σ P) (Q.hessian.map (algebraMap K L)) = Q'.hessian.map (algebraMap K L) :=
    isTwist_galGL h σ
  have h0 : cong P (Q.hessian.map (algebraMap K L)) = Q'.hessian.map (algebraMap K L) := h
  change cong (P * (galGL σ P)⁻¹) (Q.hessian.map (algebraMap K L)) = _
  rw [cong_mul, h0, ← h', cong_inv_mul]

/-- A matrix over $L$ fixed by $\operatorname{Gal}(L/K)$ has entries in $K$ ($L/K$ Galois). -/
theorem exists_map_eq_of_fixed [IsGalois K L] (M : Matrix (Fin n) (Fin n) L) (hM : ∀ σ : L ≃ₐ[K] L, M.map σ = M) :
    ∃ N : Matrix (Fin n) (Fin n) K, N.map (algebraMap K L) = M := by
  have : ∀ i j, ∃ c : K, algebraMap K L c = M i j := fun i j =>
    (IsGalois.mem_range_algebraMap_iff_fixed (M i j)).mpr fun σ => congrFun (congrFun (hM σ) i) j
  choose N hN using this
  exact ⟨Matrix.of N, by ext i j; exact hN i j⟩

/-- **Galois descent, existence** (Serre, *Galois Cohomology*, III, §1.1–1.3; for Milne, *CFT*, VIII, Remark 6.4,
p. 252): every crossed homomorphism $\operatorname{Gal}(L/K) \to O_Q(L)$ is $\sigma \mapsto P\,\sigma(P)^{-1}$ for a
twist $(Q', P)$ of $Q$: a form $Q'$ over $K$ and $P \in \mathrm{GL}_n(L)$ with $Q(P\vec x) = Q'(\vec x)$. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Remark 6.4, p. 252 (Galois descent for quadratic forms, input)"]
theorem galois_descent_exists [IsGalois K L] (Q : QuadForm K n) {a : (L ≃ₐ[K] L) → GL (Fin n) L}
    (ha : IsOrthCocycle Q a) : ∃ (Q' : QuadForm K n) (P : GL (Fin n) L), IsTwist Q Q' P ∧ a = twistCocycle P := by
  obtain ⟨B, hB⟩ := speiser_hilbert90 a ha.1
  set S := Q.hessian.map (algebraMap K L)
  -- `Bᵀ S B` is Galois-fixed
  have hfix : ∀ σ : L ≃ₐ[K] L, (cong B S).map σ = cong B S := by
    intro σ
    have hσB : galGL σ B = (a σ)⁻¹ * B := by
      rw [hB σ]; group
    have hO : cong (a σ)⁻¹ S = S := (mem_orthGroup Q).mp ((orthGroup Q L).inv_mem (ha.2 σ))
    change (cong B S).map (σ : L →+* L) = _
    have hSσ : S.map (σ : L →+* L) = S := map_algebraMap_galois σ _
    rw [cong_map, show Matrix.GeneralLinearGroup.map (σ : L →+* L) B = galGL σ B from rfl, hσB,
      hSσ, cong_mul, hO]
  obtain ⟨M, hM⟩ := exists_map_eq_of_fixed _ hfix
  have hMsymm : Mᵀ = M := by
    apply Matrix.map_injective (algebraMap K L).injective
    have hS : Sᵀ = S := by simp only [S]; rw [← Matrix.transpose_map, hessian_transpose]
    show Mᵀ.map (algebraMap K L) = M.map (algebraMap K L)
    rw [Matrix.transpose_map, hM]
    simp only [cong, Matrix.transpose_mul, Matrix.transpose_transpose, hS, Matrix.mul_assoc]
  obtain ⟨Q', hQ'⟩ := exists_hessian_eq M hMsymm
  refine ⟨Q', B, ?_, ?_⟩
  · change cong B S = _
    rw [hQ', hM]
  · funext σ
    exact hB σ

/-- **Galois descent, classes** (Serre, *Galois Cohomology*, III, §1.3): two twists of $Q$ give cohomologous cocycles
in $O_Q(L)$ iff the forms are isometric over $K$. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Remark 6.4, p. 252 (Galois descent for quadratic forms, classes)"]
theorem galois_descent_cohomologous_iff [IsGalois K L] {Q Q₁ Q₂ : QuadForm K n} {P₁ P₂ : GL (Fin n) L}
    (h₁ : IsTwist Q Q₁ P₁) (h₂ : IsTwist Q Q₂ P₂) :
    OrthCohomologous Q (twistCocycle (K := K) P₁) (twistCocycle P₂) ↔ Q₁.IsometricIn K Q₂ := by
  set S := Q.hessian.map (algebraMap K L)
  have h₁' : cong P₁ S = Q₁.hessian.map (algebraMap K L) := h₁
  have h₂' : cong P₂ S = Q₂.hessian.map (algebraMap K L) := h₂
  rw [isometricIn_iff_hessian]
  constructor
  · rintro ⟨c, hc, hcoh⟩
    have hcS : cong c S = S := (mem_orthGroup Q).mp hc
    set g : GL (Fin n) L := P₁⁻¹ * c * P₂
    have hgfix : ∀ σ : L ≃ₐ[K] L, (g : Matrix (Fin n) (Fin n) L).map σ = (g : Matrix (Fin n) (Fin n) L) := by
      intro σ
      have e := hcoh σ
      simp only [twistCocycle] at e
      have hy : galGL σ c = galGL σ P₁ * P₁⁻¹ * c * (P₂ * (galGL σ P₂)⁻¹) := by
        rw [e]; group
      have : galGL σ g = g := by
        simp only [g, map_mul, map_inv]
        rw [hy]; group
      exact congrArg Units.val this
    obtain ⟨N, hN⟩ := exists_map_eq_of_fixed _ hgfix
    have hdet : IsUnit N.det := by
      have : algebraMap K L N.det = (g : Matrix (Fin n) (Fin n) L).det := by
        rw [← hN, RingHom.map_det]; rfl
      refine isUnit_iff_ne_zero.mpr fun h0 => ?_
      rw [h0, map_zero] at this
      exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit |>.ne_zero this.symm
    refine ⟨((Matrix.isUnit_iff_isUnit_det N).mpr hdet).unit, ?_⟩
    rw [IsUnit.unit_spec]
    have hinj : Function.Injective (fun M : Matrix (Fin n) (Fin n) K => M.map (algebraMap K L)) :=
      Matrix.map_injective (algebraMap K L).injective
    apply hinj
    simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id]
    change (Nᵀ * Q₁.hessian * N).map (algebraMap K L) = _
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hN, ← h₂', ← h₁']
    change cong g (cong P₁ S) = _
    rw [← cong_mul, show P₁ * g = c * P₂ by simp only [g]; group, cong_mul, hcS]
  · rintro ⟨g, hg⟩
    simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at hg
    set gL : GL (Fin n) L := Matrix.GeneralLinearGroup.map (algebraMap K L) g
    have hgL : cong gL (Q₁.hessian.map (algebraMap K L)) = Q₂.hessian.map (algebraMap K L) := by
      rw [← hg]
      change (gL : Matrix (Fin n) (Fin n) L)ᵀ * _ * (gL : Matrix (Fin n) (Fin n) L) = ((g : Matrix (Fin n) (Fin n) K)ᵀ * Q₁.hessian * (g : Matrix (Fin n) (Fin n) K)).map (algebraMap K L)
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
      rfl
    have hgfix : ∀ σ : L ≃ₐ[K] L, galGL σ gL = gL := by
      intro σ
      ext i j
      simp [gL, galGL]
    refine ⟨P₁ * gL * P₂⁻¹, ?_, fun σ => ?_⟩
    · rw [mem_orthGroup]
      change cong (P₁ * gL * P₂⁻¹) S = S
      rw [cong_mul, cong_mul, h₁', hgL, ← h₂', cong_inv_mul]
    · simp only [twistCocycle, map_mul, map_inv, hgfix]
      group

end NumberFieldKB.MilneCFT.Ch8
