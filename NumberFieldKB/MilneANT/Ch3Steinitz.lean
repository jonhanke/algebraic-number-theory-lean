import NumberFieldKB.MilneANT.Ch3InvariantFactors
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Algebraic Number Theory*, Theorem 3.31: structure of torsion-free modules over a Dedekind domain

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Theorem 3.31, pp. 57-58; bib key `milne2020ant`.

**`thm_3_31`** proves the named statement `TorsionFreeModuleStructure A K` (Ch3Modules.lean) unconditionally.

* (a) `decomposition_aux`: for a finitely generated torsion-free $M$, the localisation $M \to K \otimes_A M$ is
  injective with image spanning the finite-dimensional $K$-space $K \otimes_A M$; the existence part of the
  invariant factor theorem (Theorem 3.32, `InvariantFactors.thm_3_32_exists`) with $N = M$ writes the image as
  $\bigoplus \mathfrak a_i e_i$.
* (b), sufficiency (Steinitz): `exists_coprime_reps` and `pair_equiv` show
  $\mathfrak a \oplus \mathfrak b \cong A \oplus \mathfrak a\mathfrak b$ (move both to coprime integral ideals in their
  classes, then `splitEquiv`: $\mathfrak p \times \mathfrak q \cong A \times \mathfrak p\mathfrak q$); `normal_form`
  gives $\bigoplus \mathfrak a_i \cong A^{m-1} \oplus \prod\mathfrak a_i$ by induction, and
  `thm_3_31_rank_one` identifies ideals in the same class (`iso_of_class_eq`).
* (b), necessity (`iso_imp`): an isomorphism extends (`exists_extend`) to a $K$-linear isomorphism, so $m = n$;
  its matrix $T$ and the matrix $T'$ of the inverse satisfy $T_{ji} \in \mathfrak b_j\mathfrak a_i^{-1}$,
  $T'_{ij} \in \mathfrak a_i\mathfrak b_j^{-1}$, hence $\det T \in \prod\mathfrak b\,(\prod\mathfrak a)^{-1}$ and
  $\det T^{-1} \in \prod\mathfrak a\,(\prod\mathfrak b)^{-1}$, i.e. the two products differ by the principal ideal
  $(\det T)$ (`class_eq_of_mem`).
-/

open scoped nonZeroDivisors

namespace NumberFieldKB.MilneANT

universe u

section Decomp

variable (A : Type u) [CommRing A] [IsDedekindDomain A] (K : Type u) [Field K]
    [Algebra A K] [IsFractionRing A K]

theorem decomposition_aux (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [NoZeroSMulDivisors A M] :
    ∃ (m : ℕ) (a : Fin m → (FractionalIdeal A⁰ K)ˣ),
      Nonempty (M ≃ₗ[A] ∀ i, ((a i : FractionalIdeal A⁰ K) : Submodule A K)) := by
  classical
  let f : M →ₗ[A] TensorProduct A K M := TensorProduct.mk A K M 1
  have hf : IsLocalizedModule A⁰ f :=
    (isLocalizedModule_iff_isBaseChange A⁰ K f).2 (TensorProduct.isBaseChange A M K)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff A⁰ (f := f)).1 hx
    exact (smul_eq_zero.1 hs).resolve_left (nonZeroDivisors.coe_ne_zero s)
  set V := TensorProduct A K M
  have hspan : Submodule.span K ((LinearMap.range f : Submodule A V) : Set V) = ⊤ := by
    rw [eq_top_iff]
    intro x hx0
    clear hx0
    induction x using TensorProduct.inductionOn with
    | tmul k m =>
      have : k ⊗ₜ[A] m = k • f m := by
        rw [show f m = (1 : K) ⊗ₜ[A] m from rfl, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    | add x y hx hy => exact add_mem hx hy
  have hFG : (LinearMap.range f).FG := by
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map f Module.Finite.fg_top
  have : FiniteDimensional K V := InvariantFactors.finiteDimensional_of_fg hFG hspan
  obtain ⟨e, a, b, -, -, hM, -⟩ := InvariantFactors.thm_3_32_exists (A := A) (K := K) V
    (Module.finrank K V) rfl (LinearMap.range f) (LinearMap.range f) hFG hFG le_rfl hspan
  refine ⟨Module.finrank K V, a, ⟨?_⟩⟩
  let g : (∀ i, ((a i : FractionalIdeal A⁰ K) : Submodule A K)) →ₗ[A] V :=
    ∑ i, ((LinearMap.toSpanSingleton K V (e i)).restrictScalars A).comp
      (((a i : FractionalIdeal A⁰ K) : Submodule A K).subtype.comp (LinearMap.proj i))
  have hg : ∀ c, g c = ∑ i, (c i : K) • e i := by
    intro c
    simp [g]
  have hcoord : ∀ c j, e.coord j (g c) = c j := by
    intro c j
    classical
    simp [hg, Module.Basis.coord_apply, Finsupp.single_apply]
  have hginj : Function.Injective g := by
    intro c d h
    ext j
    have := hcoord c j
    rw [h, hcoord d j] at this
    exact this.symm
  have hrange : LinearMap.range f = LinearMap.range g := by
    rw [hM]
    ext v
    refine (InvariantFactors.mem_iSup_line_iff e
      (fun i => ((a i : FractionalIdeal A⁰ K) : Submodule A K)) v).trans ?_
    constructor
    · intro h
      refine ⟨fun i => ⟨e.coord i v, h i⟩, ?_⟩
      rw [hg]
      simp
    · rintro ⟨c, rfl⟩ i
      rw [hcoord]
      exact (c i).2
  exact (LinearEquiv.ofInjective f hinj).trans
    ((LinearEquiv.ofEq _ _ hrange).trans (LinearEquiv.ofInjective g hginj).symm)

end Decomp

section Split

open scoped Pointwise

variable {A : Type u} [CommRing A] {K : Type u} [Field K] [Algebra A K]

theorem mul_mem_of_mem_one {p : Submodule A K} {t x : K} (ht : t ∈ (1 : Submodule A K))
    (hx : x ∈ p) : t * x ∈ p := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 ht
  rw [← Algebra.smul_def]
  exact p.smul_mem r hx

theorem mul_le_left {p q : Submodule A K} (hq : q ≤ 1) : p * q ≤ p := by
  rw [Submodule.mul_le]
  intro x hx y hy
  rw [mul_comm]
  exact mul_mem_of_mem_one (hq hy) hx

theorem mul_le_right {p q : Submodule A K} (hp : p ≤ 1) : p * q ≤ q := by
  rw [Submodule.mul_le]
  intro x hx y hy
  exact mul_mem_of_mem_one (hp hx) hy

/-- If `p, q ⊆ A` are coprime (`u0 + v0 = 1` with `u0 ∈ p`, `v0 ∈ q`), then
`p × q ≃ A × (p q)` (with `A` realized as the submodule `1` of `K`). -/
def splitEquiv (p q : Submodule A K) (hp : p ≤ 1) (hq : q ≤ 1) (u0 v0 : K) (hu : u0 ∈ p)
    (hv : v0 ∈ q) (h : u0 + v0 = 1) :
    (p × q) ≃ₗ[A] (↥(1 : Submodule A K) × ↥(p * q)) where
  toFun x := (⟨(x.1 : K) + x.2, add_mem (hp x.1.2) (hq x.2.2)⟩,
    ⟨(x.1 : K) * v0 - x.2 * u0, sub_mem (Submodule.mul_mem_mul x.1.2 hv)
      (by rw [mul_comm (x.2 : K) u0]; exact Submodule.mul_mem_mul hu x.2.2)⟩)
  invFun y := (⟨(y.1 : K) * u0 + y.2, add_mem (mul_mem_of_mem_one y.1.2 hu)
      (mul_le_left hq y.2.2)⟩,
    ⟨(y.1 : K) * v0 - y.2, sub_mem (mul_mem_of_mem_one y.1.2 hv) (mul_le_right hp y.2.2)⟩)
  map_add' x y := by
    ext <;> simp <;> ring
  map_smul' r x := by
    ext <;> simp [mul_sub, mul_add, Algebra.smul_def] <;> ring
  left_inv x := by
    ext
    · simp only
      linear_combination (x.1 : K) * h
    · simp only
      linear_combination (x.2 : K) * h
  right_inv y := by
    ext
    · simp only
      linear_combination (y.1 : K) * h
    · simp only
      linear_combination (y.2 : K) * h

end Split

section Coprime

variable {A : Type u} [CommRing A] [IsDedekindDomain A] {K : Type u} [Field K] [Algebra A K]
  [IsFractionRing A K]

theorem mk_eq_mk_iff' (a b : (FractionalIdeal A⁰ K)ˣ) :
    ClassGroup.mk K a = ClassGroup.mk K b ↔ ∃ x : Kˣ, a * toPrincipalIdeal A K x = b := by
  rw [← (ClassGroup.equiv (R := A) K).injective.eq_iff]
  simp only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self, RingEquiv.coe_mulEquiv_refl,
    QuotientGroup.mk'_eq_mk', MonoidHom.mem_range]
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, h⟩
    exact ⟨x, h⟩
  · rintro ⟨x, h⟩
    exact ⟨_, ⟨x, rfl⟩, h⟩

/-- Every invertible fractional ideal is, up to a principal one, an integral ideal. -/
theorem exists_integral (b : (FractionalIdeal A⁰ K)ˣ) :
    ∃ (q : (FractionalIdeal A⁰ K)ˣ) (x : Kˣ) (B : Ideal A),
      b * toPrincipalIdeal A K x = q ∧ ((q : FractionalIdeal A⁰ K)) = (B : FractionalIdeal A⁰ K) := by
  obtain ⟨d, B, hd, hB⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (b : FractionalIdeal A⁰ K)
  have hd' : algebraMap A K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hd
  refine ⟨Units.mk0 (B : FractionalIdeal A⁰ K) ?_, Units.mk0 (algebraMap A K d) hd', B, ?_, rfl⟩
  · intro h0
    have : (b : FractionalIdeal A⁰ K) = 0 := by rw [hB, h0, mul_zero]
    exact b.ne_zero this
  · apply Units.ext
    simp only [Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0]
    rw [hB, mul_assoc, mul_comm, mul_assoc, ← map_mul, mul_inv_cancel₀ hd', map_one, mul_one]

theorem exists_alpha (C B : Ideal A) (hC : C ≠ ⊥) (hB : B ≠ ⊥) :
    ∃ α : A, α ≠ 0 ∧ C * B ⊔ Ideal.span {α} = C := by
  obtain ⟨α, hα⟩ := IsDedekindDomain.exists_sup_span_eq (I := C * B) (J := C)
    Ideal.mul_le_left (mul_ne_zero hC hB)
  by_cases h0 : α = 0
  · subst h0
    simp only [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq] at hα
    obtain ⟨α', hα', hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC
    refine ⟨α', hne, ?_⟩
    rw [hα]
    exact sup_eq_left.2 ((Ideal.span_singleton_le_iff_mem _).2 hα')
  · exact ⟨α, h0, hα⟩

theorem exists_coprime_reps (a b : (FractionalIdeal A⁰ K)ˣ) :
    ∃ (P Q : Ideal A) (uP uQ : (FractionalIdeal A⁰ K)ˣ),
      (uP : FractionalIdeal A⁰ K) = (P : FractionalIdeal A⁰ K) ∧
      (uQ : FractionalIdeal A⁰ K) = (Q : FractionalIdeal A⁰ K) ∧ P ⊔ Q = ⊤ ∧
      ClassGroup.mk K uP = ClassGroup.mk K a ∧ ClassGroup.mk K uQ = ClassGroup.mk K b := by
  classical
  obtain ⟨qa, xa, Ba, hxa, hqa⟩ := exists_integral a
  obtain ⟨qb, xb, Cb, hxb, hqb⟩ := exists_integral b⁻¹
  have hB : Ba ≠ ⊥ := by
    rintro rfl
    apply qa.ne_zero
    rw [hqa]; simp
  have hC : Cb ≠ ⊥ := by
    rintro rfl
    apply qb.ne_zero
    rw [hqb]; simp
  obtain ⟨α, hα0, hα⟩ := exists_alpha Cb Ba hC hB
  have hle : Ideal.span {α} ≤ Cb := le_sup_right.trans hα.le
  obtain ⟨D, hD⟩ := Ideal.dvd_iff_le.2 hle
  have hD0 : D ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hD
    exact hα0 (by simpa using hD)
  have hcop : Ba ⊔ D = ⊤ := by
    have h1 : Cb * (Ba ⊔ D) = Cb * ⊤ := by
      rw [Ideal.mul_sup, Ideal.mul_top, ← hD]
      exact hα
    exact mul_left_cancel₀ (by simpa using hC) h1
  have hD1 : ((D : Ideal A) : FractionalIdeal A⁰ K) ≠ 0 := by
    intro h; apply hD0; exact (FractionalIdeal.coeIdeal_eq_zero).1 h
  have hα' : algebraMap A K α ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hα0
  set α' : Kˣ := Units.mk0 (algebraMap A K α) hα' with hα'def
  have h1 : qb * Units.mk0 ((D : Ideal A) : FractionalIdeal A⁰ K) hD1 =
      toPrincipalIdeal A K α' := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0, coe_toPrincipalIdeal, α']
    rw [hqb, ← FractionalIdeal.coeIdeal_mul, ← hD, FractionalIdeal.coeIdeal_span_singleton]
  refine ⟨Ba, D, qa, Units.mk0 _ hD1, hqa, rfl, hcop, ?_, ?_⟩
  · exact ((mk_eq_mk_iff' a qa).2 ⟨xa, hxa⟩).symm
  · refine ((mk_eq_mk_iff' b _).2 ⟨xb⁻¹ * α', ?_⟩).symm
    have hq : qb = b⁻¹ * toPrincipalIdeal A K xb := hxb.symm
    rw [hq] at h1
    rw [map_mul, map_inv, ← h1]
    generalize (toPrincipalIdeal A K xb) = t
    generalize Units.mk0 ((D : Ideal A) : FractionalIdeal A⁰ K) hD1 = u
    calc b * (t⁻¹ * (b⁻¹ * t * u)) = (b * b⁻¹) * (t⁻¹ * t) * u := by
          simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = u := by simp

open scoped Pointwise in
theorem pair_equiv (a b : (FractionalIdeal A⁰ K)ˣ) :
    Nonempty ((↥((a : FractionalIdeal A⁰ K) : Submodule A K) × ↥((b : FractionalIdeal A⁰ K) : Submodule A K)) ≃ₗ[A]
      (↥(((1 : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) : Submodule A K) ×
        ↥(((a * b : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) : Submodule A K))) := by
  obtain ⟨P, Q, uP, uQ, hP, hQ, hPQ, hcP, hcQ⟩ := exists_coprime_reps a b
  obtain ⟨u0, hu0, v0, hv0, huv⟩ := Submodule.mem_sup.1
    (show (1 : A) ∈ P ⊔ Q by rw [hPQ]; exact Submodule.mem_top)
  have hmem : ∀ (I : Ideal A) (u : (FractionalIdeal A⁰ K)ˣ), (u : FractionalIdeal A⁰ K) = I →
      ∀ x ∈ I, algebraMap A K x ∈ ((u : FractionalIdeal A⁰ K) : Submodule A K) := by
    intro I u hu x hx
    rw [FractionalIdeal.mem_coe, hu]
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨x, hx, rfl⟩
  have hle : ∀ (I : Ideal A) (u : (FractionalIdeal A⁰ K)ˣ), (u : FractionalIdeal A⁰ K) = I →
      ((u : FractionalIdeal A⁰ K) : Submodule A K) ≤ 1 := by
    intro I u hu
    rw [← FractionalIdeal.coe_one, FractionalIdeal.coe_le_coe, hu]
    exact FractionalIdeal.coeIdeal_le_one
  have huv' : algebraMap A K u0 + algebraMap A K v0 = 1 := by
    rw [← map_add, huv, map_one]
  let e := splitEquiv ((uP : FractionalIdeal A⁰ K) : Submodule A K)
    ((uQ : FractionalIdeal A⁰ K) : Submodule A K) (hle P uP hP) (hle Q uQ hQ) (algebraMap A K u0)
    (algebraMap A K v0) (hmem P uP hP u0 hu0) (hmem Q uQ hQ v0 hv0) huv'
  have e1 := (thm_3_31_rank_one a uP).2 hcP.symm
  have e2 := (thm_3_31_rank_one b uQ).2 hcQ.symm
  have e3 : ClassGroup.mk K (uP * uQ) = ClassGroup.mk K (a * b) := by
    rw [map_mul, map_mul, hcP, hcQ]
  have e4 := (thm_3_31_rank_one (uP * uQ) (a * b)).2 e3
  obtain ⟨f1⟩ := e1
  obtain ⟨f2⟩ := e2
  obtain ⟨f4⟩ := e4
  have hmul : ((uP : FractionalIdeal A⁰ K) : Submodule A K) * ((uQ : FractionalIdeal A⁰ K) : Submodule A K) =
      (((uP * uQ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) : Submodule A K) := by
    rw [Units.val_mul, FractionalIdeal.coe_mul]
  have hone : (1 : Submodule A K) = ((((1 : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K)) : Submodule A K) := by
    rw [Units.val_one, FractionalIdeal.coe_one]
  exact ⟨(LinearEquiv.prodCongr f1 f2).trans (e.trans (LinearEquiv.prodCongr (LinearEquiv.ofEq _ _ hone)
    ((LinearEquiv.ofEq _ _ hmul).trans f4)))⟩

/-- Normal form: `a₀ ⊕ ⋯ ⊕ a_m ≅ A^m ⊕ (a₀ ⋯ a_m)` (Steinitz). -/
theorem normal_form (m : ℕ) : ∀ a : Fin (m + 1) → (FractionalIdeal A⁰ K)ˣ,
    Nonempty ((∀ i, ↥((a i : FractionalIdeal A⁰ K) : Submodule A K)) ≃ₗ[A]
      ((Fin m → ↥(((1 : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) : Submodule A K)) ×
        ↥(((∏ i, a i : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) : Submodule A K))) := by
  induction m with
  | zero =>
    intro a
    haveI : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
    have hp : (∏ i, a i) = a 0 := by
      simp only [Finset.univ_unique, Finset.prod_singleton]
      exact congrArg a (Subsingleton.elim _ _)
    have hd : a default = a 0 := congrArg a (Subsingleton.elim _ _)
    have e2 : ↥((a 0 : FractionalIdeal A⁰ K) : Submodule A K) ≃ₗ[A]
        ((Fin 0 → ↥(((1 : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) : Submodule A K)) ×
          ↥(((∏ i, a i : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) : Submodule A K)) :=
      (LinearEquiv.ofEq _ _ (by rw [hp])).trans (LinearEquiv.uniqueProd (R := A)).symm
    exact ⟨((LinearEquiv.piUnique A (fun i => ↥((a i : FractionalIdeal A⁰ K) : Submodule A K))).trans
      (LinearEquiv.ofEq _ _ (by rw [congrArg a (Subsingleton.elim _ _)]))).trans e2⟩
  | succ m ih =>
    intro a
    obtain ⟨eih⟩ := ih (fun i : Fin (m + 1) => a i.succ)
    obtain ⟨epair⟩ := pair_equiv (a 0) (∏ i : Fin (m + 1), a i.succ)
    let M : Fin (m + 2) → Type u := fun i => ↥((a i : FractionalIdeal A⁰ K) : Submodule A K)
    let X := Fin m → ↥(((1 : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) : Submodule A K)
    let O := ↥(((1 : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) : Submodule A K)
    let P := ↥(((∏ i : Fin (m + 1), a i.succ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) :
      Submodule A K)
    let C := ↥(((a 0 * ∏ i : Fin (m + 1), a i.succ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) :
      Submodule A K)
    let N := ↥(((∏ i, a i : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) : Submodule A K)
    have s1 : (∀ i, M i) ≃ₗ[A] (M 0 × ∀ i : Fin (m + 1), M i.succ) := (Fin.consLinearEquiv A M).symm
    have s2 : (M 0 × ∀ i : Fin (m + 1), M i.succ) ≃ₗ[A] (M 0 × (X × P)) :=
      LinearEquiv.prodCongr (LinearEquiv.refl A (M 0)) eih
    have s3 : (M 0 × (X × P)) ≃ₗ[A] (X × (P × M 0)) :=
      (LinearEquiv.prodComm A _ _).trans (LinearEquiv.prodAssoc A _ _ _)
    have s4 : (X × (P × M 0)) ≃ₗ[A] (X × (O × C)) :=
      LinearEquiv.prodCongr (LinearEquiv.refl A X) ((LinearEquiv.prodComm A _ _).trans epair)
    have s5 : (X × (O × C)) ≃ₗ[A] ((X × O) × C) := (LinearEquiv.prodAssoc A _ _ _).symm
    have s6 : ((X × O) × C) ≃ₗ[A] ((Fin (m + 1) → O) × N) :=
      LinearEquiv.prodCongr ((LinearEquiv.prodComm A _ _).trans
        (Fin.consLinearEquiv A (fun _ : Fin (m + 1) => O)))
        (LinearEquiv.ofEq _ _ (by rw [Fin.prod_univ_succ a]))
    exact ⟨s1.trans (s2.trans (s3.trans (s4.trans (s5.trans s6))))⟩

/-- **Steinitz**: direct sums of fractional ideals with the same number of summands and the same product class are
isomorphic. -/
theorem iso_of_class_eq (m : ℕ) (a b : Fin m → (FractionalIdeal A⁰ K)ˣ)
    (h : ClassGroup.mk K (∏ i, a i) = ClassGroup.mk K (∏ i, b i)) :
    Nonempty ((∀ i, ↥((a i : FractionalIdeal A⁰ K) : Submodule A K)) ≃ₗ[A]
      ∀ j, ↥((b j : FractionalIdeal A⁰ K) : Submodule A K)) := by
  cases m with
  | zero => exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  | succ m =>
    obtain ⟨ea⟩ := normal_form m a
    obtain ⟨eb⟩ := normal_form m b
    obtain ⟨r⟩ := (thm_3_31_rank_one (∏ i, a i) (∏ i, b i)).2 h
    exact ⟨ea.trans ((LinearEquiv.prodCongr (LinearEquiv.refl A _) r).trans eb.symm)⟩

end Coprime

section Necessity

open scoped Pointwise

variable {A : Type u} [CommRing A] [IsDedekindDomain A] {K : Type u} [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- An $A$-linear map from a submodule of $K$ to a $K$-vector space is $K$-homogeneous on ratios. -/
theorem lin_scale {n : ℕ} {I : Submodule A K} (ψ : ↥I →ₗ[A] (Fin n → K)) (x y : ↥I) :
    (x : K) • ψ y = (y : K) • ψ x := by
  by_cases hx : (x : K) = 0
  · have : x = 0 := Subtype.ext hx
    subst this
    simp
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := A) (z := (y : K) / x)
  have hs0 : algebraMap A K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have h1 : algebraMap A K s * (y : K) = algebraMap A K r * x := by
    field_simp at hrs
    linear_combination -hrs
  have h2 : s • y = r • x := Subtype.ext (by simpa [Algebra.smul_def] using h1)
  have h3 := congrArg ψ h2
  rw [map_smul, map_smul, ← algebraMap_smul K s (ψ y), ← algebraMap_smul K r (ψ x)] at h3
  apply smul_right_injective (Fin n → K) hs0
  simp only
  calc algebraMap A K s • (x : K) • ψ y = (x : K) • (algebraMap A K s • ψ y) := smul_comm _ _ _
    _ = (x : K) • algebraMap A K r • ψ x := by rw [h3]
    _ = (algebraMap A K r * x) • ψ x := by rw [smul_smul, mul_comm]
    _ = (algebraMap A K s * y) • ψ x := by rw [h1]
    _ = _ := by rw [mul_smul]

theorem exists_ne_zero_elt (a : (FractionalIdeal A⁰ K)ˣ) :
    ∃ x : ↥((a : FractionalIdeal A⁰ K) : Submodule A K), (x : K) ≠ 0 := by
  have ha : ((a : FractionalIdeal A⁰ K) : Submodule A K) ≠ ⊥ := by
    have := a.ne_zero
    rwa [Ne, ← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_zero] at this
  obtain ⟨y0, hy0, hy0ne⟩ := (Submodule.ne_bot_iff _).mp ha
  exact ⟨⟨y0, hy0⟩, hy0ne⟩

theorem det_mem_prod_prod {n : ℕ} (T : Matrix (Fin n) (Fin n) K) (c d : Fin n → Submodule A K)
    (h : ∀ j i, T j i ∈ c j * d i) : T.det ∈ (∏ j, c j) * ∏ i, d i := by
  rw [Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hp := InvariantFactors.prod_mem_prod_fin (fun i => T (σ i) i) (fun i => c (σ i) * d i)
    fun i => h _ i
  have hq : ∏ i, (c (σ i) * d i) = (∏ j, c j) * ∏ i, d i := by
    rw [Finset.prod_mul_distrib, Equiv.prod_comp σ c]
  rw [hq] at hp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> rw [h1]
  · rwa [one_smul]
  · rw [Units.neg_smul, one_smul]; exact neg_mem hp

theorem coe_prod_units {ι : Type*} (s : Finset ι) (u : ι → (FractionalIdeal A⁰ K)ˣ) :
    ∏ i ∈ s, ((u i : FractionalIdeal A⁰ K) : Submodule A K) =
      (((∏ i ∈ s, u i : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) : Submodule A K) := by
  rw [Units.coe_prod]
  exact (map_prod (FractionalIdeal.coeSubmoduleHom A⁰ K) (fun i => (u i : FractionalIdeal A⁰ K)) s).symm

theorem det_mem_units {n : ℕ} (T : Matrix (Fin n) (Fin n) K) (c d : Fin n → (FractionalIdeal A⁰ K)ˣ)
    (h : ∀ j i, T j i ∈ ((c j * d i : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K)) :
    T.det ∈ (((∏ j, c j) * ∏ i, d i : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) := by
  have h' : ∀ j i, T j i ∈ ((c j : FractionalIdeal A⁰ K) : Submodule A K) *
      ((d i : FractionalIdeal A⁰ K) : Submodule A K) := by
    intro j i
    have := h j i
    rwa [← FractionalIdeal.mem_coe, Units.val_mul, FractionalIdeal.coe_mul] at this
  have := det_mem_prod_prod T (fun j => ((c j : FractionalIdeal A⁰ K) : Submodule A K))
    (fun i => ((d i : FractionalIdeal A⁰ K) : Submodule A K)) h'
  rw [coe_prod_units, coe_prod_units, ← FractionalIdeal.coe_mul, ← Units.val_mul] at this
  exact FractionalIdeal.mem_coe.1 this

theorem mem_div_of_mul_mem (t : K) (I J : (FractionalIdeal A⁰ K)ˣ)
    (h : ∀ x ∈ (I : FractionalIdeal A⁰ K), t * x ∈ (J : FractionalIdeal A⁰ K)) :
    t ∈ ((J * I⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) := by
  have h1 : FractionalIdeal.spanSingleton A⁰ t * (I : FractionalIdeal A⁰ K) ≤ (J : FractionalIdeal A⁰ K) := by
    rw [FractionalIdeal.mul_le]
    intro z hz w hw
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hz
    rw [smul_mul_assoc]
    exact FractionalIdeal.mem_coe.1
      (((J : FractionalIdeal A⁰ K) : Submodule A K).smul_mem r (FractionalIdeal.mem_coe.2 (h w hw)))
  have h2 : FractionalIdeal.spanSingleton A⁰ t ≤ ((J * I⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) := by
    calc FractionalIdeal.spanSingleton A⁰ t
        = FractionalIdeal.spanSingleton A⁰ t * ((I * I⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) := by
          rw [mul_inv_cancel, Units.val_one, mul_one]
      _ = (FractionalIdeal.spanSingleton A⁰ t * (I : FractionalIdeal A⁰ K)) *
            ((I⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) := by
          rw [Units.val_mul, mul_assoc]
      _ ≤ (J : FractionalIdeal A⁰ K) * ((I⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) :=
          mul_le_mul' h1 le_rfl
      _ = _ := by rw [Units.val_mul]
  exact h2 (FractionalIdeal.mem_spanSingleton_self _ _)

theorem exists_extend {m n : ℕ} (a : Fin m → (FractionalIdeal A⁰ K)ˣ) (b : Fin n → (FractionalIdeal A⁰ K)ˣ)
    (φ : (∀ i, ↥((a i : FractionalIdeal A⁰ K) : Submodule A K)) →ₗ[A]
      ∀ j, ↥((b j : FractionalIdeal A⁰ K) : Submodule A K)) :
    ∃ Φ : (Fin m → K) →ₗ[K] (Fin n → K), ∀ c : ∀ i, ↥((a i : FractionalIdeal A⁰ K) : Submodule A K),
      Φ (fun i => (c i : K)) = fun j => ((φ c j : ↥((b j : FractionalIdeal A⁰ K) : Submodule A K)) : K) := by
  classical
  let out : (∀ j, ↥((b j : FractionalIdeal A⁰ K) : Submodule A K)) →ₗ[A] (Fin n → K) :=
    LinearMap.pi fun j => ((b j : FractionalIdeal A⁰ K) : Submodule A K).subtype ∘ₗ LinearMap.proj j
  let ψ : ∀ i, ↥((a i : FractionalIdeal A⁰ K) : Submodule A K) →ₗ[A] (Fin n → K) := fun i =>
    out ∘ₗ φ ∘ₗ LinearMap.single A (fun i => ↥((a i : FractionalIdeal A⁰ K) : Submodule A K)) i
  choose x hx using fun i => exists_ne_zero_elt (a i)
  refine ⟨(Pi.basisFun K (Fin m)).constr K (fun i => ((x i : K))⁻¹ • ψ i (x i)), fun c => ?_⟩
  have key : ∀ i, (c i : K) • ((x i : K))⁻¹ • ψ i (x i) = ψ i (c i) := by
    intro i
    rw [smul_comm, ← lin_scale (ψ i) (x i) (c i), inv_smul_smul₀ (hx i)]
  rw [Module.Basis.constr_apply_fintype]
  simp only [Module.Basis.equivFun_apply, Pi.basisFun_repr, key]
  have h2 : ∑ i, ψ i (c i) = out (φ c) := by
    simp only [ψ, LinearMap.comp_apply, LinearMap.single_apply]
    rw [← map_sum, ← map_sum, Finset.univ_sum_single]
  rw [h2]
  rfl

theorem comp_id {m n : ℕ} (a : Fin m → (FractionalIdeal A⁰ K)ˣ) (b : Fin n → (FractionalIdeal A⁰ K)ˣ)
    (φ : (∀ i, ↥((a i : FractionalIdeal A⁰ K) : Submodule A K)) ≃ₗ[A]
      ∀ j, ↥((b j : FractionalIdeal A⁰ K) : Submodule A K))
    (Φ : (Fin m → K) →ₗ[K] (Fin n → K)) (Ψ : (Fin n → K) →ₗ[K] (Fin m → K))
    (hΦ : ∀ c : ∀ i, ↥((a i : FractionalIdeal A⁰ K) : Submodule A K),
      Φ (fun i => (c i : K)) = fun j => ((φ c j : ↥((b j : FractionalIdeal A⁰ K) : Submodule A K)) : K))
    (hΨ : ∀ c : ∀ j, ↥((b j : FractionalIdeal A⁰ K) : Submodule A K),
      Ψ (fun j => (c j : K)) = fun i => ((φ.symm c i : ↥((a i : FractionalIdeal A⁰ K) : Submodule A K)) : K)) :
    Ψ ∘ₗ Φ = LinearMap.id := by
  classical
  refine (Pi.basisFun K (Fin m)).ext fun i => ?_
  obtain ⟨x, hx⟩ := exists_ne_zero_elt (a i)
  set c : ∀ k, ↥((a k : FractionalIdeal A⁰ K) : Submodule A K) :=
    Pi.single (M := fun k => ↥((a k : FractionalIdeal A⁰ K) : Submodule A K)) i x with hc
  have hv : (fun k => (c k : K)) = (x : K) • (Pi.basisFun K (Fin m) i) := by
    ext k
    by_cases h : k = i
    · subst h; simp [hc]
    · simp [hc, Pi.single_eq_of_ne h, Pi.single_apply, h]
  have h1 := hΦ c
  have h2 := hΨ (φ c)
  rw [LinearEquiv.symm_apply_apply] at h2
  rw [hv, map_smul] at h1
  have h3 : Ψ (Φ ((x : K) • (Pi.basisFun K (Fin m) i))) = (x : K) • Pi.basisFun K (Fin m) i := by
    rw [← hv, hΦ, h2]
  rw [map_smul, map_smul] at h3
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  exact smul_right_injective _ hx h3

theorem class_eq_of_mem (Pa Pb : (FractionalIdeal A⁰ K)ˣ) (D D' : K) (hDD : D * D' = 1)
    (h1 : D ∈ ((Pb * Pa⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K))
    (h2 : D' ∈ ((Pa * Pb⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K)) :
    ClassGroup.mk K Pa = ClassGroup.mk K Pb := by
  have hD0 : D ≠ 0 := left_ne_zero_of_mul_eq_one hDD
  set u : (FractionalIdeal A⁰ K)ˣ := Pb * Pa⁻¹ with hu
  have hle1 : FractionalIdeal.spanSingleton A⁰ D ≤ (u : FractionalIdeal A⁰ K) :=
    (FractionalIdeal.spanSingleton_le_iff_mem).2 h1
  have hle2 : FractionalIdeal.spanSingleton A⁰ D' ≤ ((u⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) := by
    refine (FractionalIdeal.spanSingleton_le_iff_mem).2 ?_
    have : u⁻¹ = Pa * Pb⁻¹ := by
      rw [hu]; simp only [mul_inv_rev, inv_inv]
    rw [this]; exact h2
  have hle3 : (u : FractionalIdeal A⁰ K) * FractionalIdeal.spanSingleton A⁰ D' ≤ 1 := by
    calc (u : FractionalIdeal A⁰ K) * FractionalIdeal.spanSingleton A⁰ D'
        ≤ (u : FractionalIdeal A⁰ K) * ((u⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) :=
          mul_le_mul' le_rfl hle2
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hge : (u : FractionalIdeal A⁰ K) ≤ FractionalIdeal.spanSingleton A⁰ D := by
    calc (u : FractionalIdeal A⁰ K)
        = ((u : FractionalIdeal A⁰ K) * FractionalIdeal.spanSingleton A⁰ D') *
            FractionalIdeal.spanSingleton A⁰ D := by
          rw [mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_comm D', hDD,
            FractionalIdeal.spanSingleton_one, mul_one]
      _ ≤ 1 * FractionalIdeal.spanSingleton A⁰ D := mul_le_mul' hle3 le_rfl
      _ = _ := one_mul _
  have hEq : u = toPrincipalIdeal A K (Units.mk0 D hD0) := by
    apply Units.ext
    rw [coe_toPrincipalIdeal, Units.val_mk0]
    exact le_antisymm hge hle1
  refine (mk_eq_mk_iff' Pa Pb).2 ⟨Units.mk0 D hD0, ?_⟩
  rw [← hEq, hu, mul_left_comm, mul_inv_cancel, mul_one]

theorem vec_single {m : ℕ} (a : Fin m → (FractionalIdeal A⁰ K)ˣ) (i : Fin m)
    (x : ↥((a i : FractionalIdeal A⁰ K) : Submodule A K)) :
    (fun k => (((Pi.single (M := fun k => ↥((a k : FractionalIdeal A⁰ K) : Submodule A K)) i x :
      ∀ k, ↥((a k : FractionalIdeal A⁰ K) : Submodule A K)) k : _) : K)) =
      (x : K) • (Pi.single i (1 : K) : Fin m → K) := by
  classical
  ext k
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem toMatrix_entry {m : ℕ} (Φ : (Fin m → K) →ₗ[K] (Fin m → K)) (j i : Fin m) :
    LinearMap.toMatrix' Φ j i = Φ (Pi.single i 1) j := by
  classical
  rw [LinearMap.toMatrix'_apply]

theorem entry_mem {m : ℕ} (a b : Fin m → (FractionalIdeal A⁰ K)ˣ)
    (φ : (∀ i, ↥((a i : FractionalIdeal A⁰ K) : Submodule A K)) ≃ₗ[A]
      ∀ j, ↥((b j : FractionalIdeal A⁰ K) : Submodule A K))
    (Φ : (Fin m → K) →ₗ[K] (Fin m → K))
    (hΦ : ∀ c : ∀ i, ↥((a i : FractionalIdeal A⁰ K) : Submodule A K),
      Φ (fun i => (c i : K)) = fun j => ((φ c j : ↥((b j : FractionalIdeal A⁰ K) : Submodule A K)) : K))
    (j i : Fin m) :
    LinearMap.toMatrix' Φ j i ∈ ((b j * (a i)⁻¹ : (FractionalIdeal A⁰ K)ˣ) : FractionalIdeal A⁰ K) := by
  classical
  refine mem_div_of_mul_mem _ (a i) (b j) fun x hx => ?_
  set c : ∀ k, ↥((a k : FractionalIdeal A⁰ K) : Submodule A K) :=
    Pi.single (M := fun k => ↥((a k : FractionalIdeal A⁰ K) : Submodule A K)) i
      ⟨x, FractionalIdeal.mem_coe.2 hx⟩ with hc
  have h1 := congrFun (hΦ c) j
  rw [hc, vec_single, map_smul, Pi.smul_apply, smul_eq_mul, ← toMatrix_entry] at h1
  rw [mul_comm, h1]
  exact FractionalIdeal.mem_coe.1 (φ c j).2

/-- **Necessity** in Theorem 3.31(b): an isomorphism forces equal rank and equal class of the product. -/
theorem iso_imp {m n : ℕ} (a : Fin m → (FractionalIdeal A⁰ K)ˣ) (b : Fin n → (FractionalIdeal A⁰ K)ˣ)
    (φ : (∀ i, ↥((a i : FractionalIdeal A⁰ K) : Submodule A K)) ≃ₗ[A]
      ∀ j, ↥((b j : FractionalIdeal A⁰ K) : Submodule A K)) :
    m = n ∧ ClassGroup.mk K (∏ i, a i) = ClassGroup.mk K (∏ j, b j) := by
  obtain ⟨Φ, hΦ⟩ := exists_extend a b φ.toLinearMap
  obtain ⟨Ψ, hΨ⟩ := exists_extend b a φ.symm.toLinearMap
  have hΦ' : ∀ c : ∀ i, ↥((a i : FractionalIdeal A⁰ K) : Submodule A K),
      Φ (fun i => (c i : K)) = fun j => ((φ c j : ↥((b j : FractionalIdeal A⁰ K) : Submodule A K)) : K) :=
    hΦ
  have hΨ' : ∀ c : ∀ j, ↥((b j : FractionalIdeal A⁰ K) : Submodule A K),
      Ψ (fun j => (c j : K)) = fun i => ((φ.symm c i : ↥((a i : FractionalIdeal A⁰ K) : Submodule A K)) : K) :=
    hΨ
  have h2 : Ψ ∘ₗ Φ = LinearMap.id := comp_id a b φ Φ Ψ hΦ' hΨ'
  have h1 : Φ ∘ₗ Ψ = LinearMap.id := comp_id b a φ.symm Ψ Φ hΨ' (by intro c; simpa using hΦ' c)
  let E : (Fin m → K) ≃ₗ[K] (Fin n → K) := LinearEquiv.ofLinear Φ Ψ h1 h2
  have hmn : m = n := by simpa using E.finrank_eq
  subst hmn
  refine ⟨rfl, ?_⟩
  have hDD : (LinearMap.toMatrix' Φ).det * (LinearMap.toMatrix' Ψ).det = 1 := by
    rw [← Matrix.det_mul, ← LinearMap.toMatrix'_comp, h1, LinearMap.toMatrix'_id, Matrix.det_one]
  have hD := det_mem_units (LinearMap.toMatrix' Φ) b (fun i => (a i)⁻¹) (entry_mem a b φ Φ hΦ')
  have hD' := det_mem_units (LinearMap.toMatrix' Ψ) a (fun i => (b i)⁻¹)
    (entry_mem b a φ.symm Ψ hΨ')
  rw [Finset.prod_inv_distrib] at hD hD'
  exact class_eq_of_mem _ _ _ _ hDD hD hD'

end Necessity

/-- **Theorem 3.31** (Milne, v3.08, pp. 57-58), proved: the named statement `TorsionFreeModuleStructure A K` holds
for every Dedekind domain $A$ with field of fractions $K$.

(a) is `decomposition_aux` (localise to the $K$-vector space $K \otimes_A M$ and apply the invariant factor
theorem to $M \subseteq K \otimes M$). (b), $\Leftarrow$: `iso_of_class_eq` (Steinitz: `pair_equiv` gives
$\mathfrak a \oplus \mathfrak b \cong A \oplus \mathfrak a\mathfrak b$ by making the ideals integral and coprime,
then `normal_form` by induction). (b), $\Rightarrow$: `iso_imp` (an isomorphism extends to a $K$-linear
isomorphism, so $m = n$, and its determinant lies in $\prod\mathfrak b_j \cdot (\prod \mathfrak a_i)^{-1}$ with
inverse in the reciprocal ideal, so the two products differ by a principal ideal). -/
@[kb "milne2020ant" "v3.08, Thm. 3.31, pp. 57–58"]
theorem thm_3_31 (A : Type u) [CommRing A] [IsDedekindDomain A] (K : Type u) [Field K] [Algebra A K]
    [IsFractionRing A K] : TorsionFreeModuleStructure A K where
  decomposition M _ _ _ _ := decomposition_aux A K M
  iso_iff m n a b :=
    ⟨fun ⟨φ⟩ => iso_imp a b φ, fun ⟨hmn, h⟩ => by
      subst hmn
      exact iso_of_class_eq m a b h⟩

end NumberFieldKB.MilneANT
