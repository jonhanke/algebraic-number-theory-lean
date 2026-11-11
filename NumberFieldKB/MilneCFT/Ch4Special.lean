import Mathlib.Algebra.QuaternionBasis
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4H2
import Mathlib.Data.Int.Range

/-!
# Milne, Class Field Theory, Chapter IV, §4: Brauer groups of special fields

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`),
Chapter IV, §4 (and Example 2.14 (b), (d)): the real numbers (Frobenius' theorem,
$\mathrm{Br}(\mathbb R) = \{[\mathbb R], [\mathbb H]\}$, the crossed product of the nontrivial cocycle
of $\mathrm{Gal}(\mathbb C/\mathbb R)$ is $\mathbb H$) and nonarchimedean local fields (the extension of
the valuation to a central division algebra, the local invariant, Example 4.2, Proposition 4.3,
Remark 4.4).

Local fields.  A nonarchimedean local field is Mathlib's `IsNonarchimedeanLocalField K`.  Its
normalized valuation $\mathrm{ord}_K : K^\times \to \mathbb Z$ is read off the order isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` of the value group with $\mathbb Z^{m0}$
(an order isomorphism to $\mathbb Z^{m0}$ is unique, so this is canonical).  For a central
division algebra $D$ of dimension $n^2$ over $K$, Milne extends $\mathrm{ord}_K$ to $D$ through the
unique extension of the absolute value to the subfields $K[\alpha]$; we use the equivalent
closed formula $\mathrm{ord}(\alpha) = \mathrm{ord}_K(\mathrm{Nm}_{D/K}\alpha)/[D : K]$
($\mathrm{Nm}_{D/K}$ = determinant of left multiplication, `Algebra.norm K`), since
$\mathrm{Nm}_{D/K}(\alpha) = \mathrm{Nm}_{K[\alpha]/K}(\alpha)^{[D : K[\alpha]]}$.

The deep facts of the section (the extended valuation is ultrametric; $e = f = n$; existence of an
unramified maximal subfield; independence of the invariant from the choices; bijectivity of the
invariant; that it is a homomorphism) are named statements (Prop structures with a source), and
their consequences are proved from them.

Locators give the printed page of the book (printed page = pdf page − 9).
-/

open scoped TensorProduct ValuativeRel Quaternion

namespace NumberFieldKB.MilneCFT.Ch4

/-! ### The real numbers -/

section Real

instance isAlgClosure_real_complex : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩

instance isGalois_real_complex : IsGalois ℝ ℂ := inferInstance

theorem quaternion_isCentral : Algebra.IsCentral ℝ ℍ[ℝ] := by
  refine ⟨fun z hz => ?_⟩
  rw [Subalgebra.mem_center_iff] at hz
  have h1 := hz ⟨0, 1, 0, 0⟩
  have h2 := hz ⟨0, 0, 1, 0⟩
  have e1 := congrArg QuaternionAlgebra.imJ h1
  have e2 := congrArg QuaternionAlgebra.imK h1
  have e3 := congrArg QuaternionAlgebra.imI h2
  have e4 := congrArg QuaternionAlgebra.imK h2
  simp at e1 e2 e3 e4
  rw [Algebra.mem_bot]
  refine ⟨z.re, ?_⟩
  ext <;> simp <;> linarith

/-- A 4-dimensional real algebra with elements `i, j` satisfying the quaternion relations is
isomorphic to `ℍ`. -/
theorem quaternionEquiv (D : Type*) [Ring D] [Algebra ℝ D] [FiniteDimensional ℝ D]
    (hD : Module.finrank ℝ D = 4) (i j : D) (hi : i * i = -1) (hj : j * j = -1)
    (hji : j * i = -(i * j)) : Nonempty (ℍ[ℝ] ≃ₐ[ℝ] D) := by
  have : Nontrivial D := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  let q : QuaternionAlgebra.Basis D (-1 : ℝ) 0 (-1) :=
    { i := i, j := j, k := i * j
      i_mul_i := by simp [hi]
      j_mul_j := by simp [hj]
      i_mul_j := rfl
      j_mul_i := by simp [hji] }
  let f : ℍ[ℝ] →ₐ[ℝ] D := q.liftHom
  have hinj : Function.Injective f := f.toRingHom.injective
  have hbij : Function.Bijective f :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap)
      (by rw [Quaternion.finrank_eq_four, hD])).1 hinj⟩
  exact ⟨AlgEquiv.ofBijective f hbij⟩

/-- Frobenius for division algebras: a finite-dimensional central division algebra over `ℝ` is
`ℝ` or `ℍ`. -/
theorem real_division_classify (D : Type*) [DivisionRing D] [Algebra ℝ D]
    [Algebra.IsCentral ℝ D] [FiniteDimensional ℝ D] :
    Nonempty (D ≃ₐ[ℝ] ℝ) ∨ Nonempty (D ≃ₐ[ℝ] ℍ[ℝ]) := by
  obtain ⟨L, hL, hmax, -⟩ := prop_3_8 (K := ℝ) D
  have hdim := (cor_3_5 (K := ℝ) D L hL).1 hmax
  have hcent := ((cor_3_4 (K := ℝ) D L hL).out 2 1).1 hdim
  let _ : Field L := hL.toField
  have : Algebra.IsAlgebraic ℝ L := Algebra.IsAlgebraic.of_finite ℝ L
  let ι : L →ₐ[ℝ] ℂ := IsAlgClosed.lift
  have hι : Function.Injective ι := ι.toRingHom.injective
  have hle : Module.finrank ℝ L ≤ 2 := by
    have := LinearMap.finrank_le_finrank_of_injective (f := ι.toLinearMap) hι
    simpa [Complex.finrank_real_complex] using this
  have hpos : 0 < Module.finrank ℝ L := Module.finrank_pos
  have hcases : Module.finrank ℝ L = 1 ∨ Module.finrank ℝ L = 2 := by omega
  rcases hcases with h1 | h2
  · left
    have hD1 : Module.finrank ℝ D = 1 := by rw [hdim, h1]; norm_num
    have hinj : Function.Injective (Algebra.ofId ℝ D) := (Algebra.ofId ℝ D).toRingHom.injective
    have hbij : Function.Bijective (Algebra.ofId ℝ D) :=
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := (Algebra.ofId ℝ D).toLinearMap) (by rw [hD1]; simp)).1 hinj⟩
    exact ⟨(AlgEquiv.ofBijective _ hbij).symm⟩
  · right
    have hD4 : Module.finrank ℝ D = 4 := by rw [hdim, h2]; norm_num
    have hbij : Function.Bijective ι :=
      ⟨hι, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := ι.toLinearMap)
        (by rw [h2, Complex.finrank_real_complex])).1 hι⟩
    let ε : L ≃ₐ[ℝ] ℂ := AlgEquiv.ofBijective ι hbij
    let τ : L ≃ₐ[ℝ] L := ε.trans (Complex.conjAe.trans ε.symm)
    have : IsSimpleRing L := inferInstance
    obtain ⟨a, ha⟩ := cor_2_11 (K := ℝ) D L L τ
    have hτε : ∀ b : L, ε (τ b) = (starRingEnd ℂ) (ε b) := by
      intro b; simp [τ]
    let i : D := (ε.symm Complex.I : L)
    have hi : i * i = -1 := by
      have : ε.symm Complex.I * ε.symm Complex.I = -1 := by
        rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
      have := congrArg Subtype.val this
      simpa [i] using this
    have hai : a * i = -(i * a) := by
      have h1 := ha (ε.symm Complex.I)
      have h2' : τ (ε.symm Complex.I) = -(ε.symm Complex.I) := by
        apply ε.injective
        rw [hτε]; simp
      rw [h2'] at h1
      have h3 : -i = a * i * ↑a⁻¹ := by simpa [i] using h1
      calc a * i = (a * i * ↑a⁻¹) * a := by rw [mul_assoc, Units.inv_mul, mul_one]
        _ = -(i * a) := by rw [← h3]; simp
    -- `a * a` commutes with `L`, hence lies in `L`
    have hcomm : ∀ b : L, (b : D) * ((a : D) * (a : D)) = ((a : D) * (a : D)) * b := by
      intro b
      have h1 : (τ (τ b) : D) = a * (τ b : D) * ↑a⁻¹ := ha (τ b)
      have h2' : τ (τ b) = b := by
        apply ε.injective
        rw [hτε, hτε]; simp
      rw [h2', ha b] at h1
      calc (b : D) * (a * a) = (a * (a * (b : D) * ↑a⁻¹) * ↑a⁻¹) * (a * a) := by rw [← h1]
        _ = (a * a) * b := by simp [mul_assoc]
    have hmem : ((a : D) * (a : D)) ∈ Subalgebra.centralizer ℝ (L : Set D) :=
      (Subalgebra.mem_centralizer_iff ℝ).2 fun g hg => hcomm ⟨g, hg⟩
    rw [hcent] at hmem
    let ℓ : L := ⟨(a : D) * (a : D), hmem⟩
    have hτℓ : τ ℓ = ℓ := Subtype.ext (by
      rw [ha ℓ]
      show (a : D) * ((a : D) * (a : D)) * ↑a⁻¹ = (a : D) * (a : D)
      simp [mul_assoc])
    obtain ⟨r, hr⟩ : ∃ r : ℝ, ε ℓ = (r : ℂ) := by
      apply Complex.conj_eq_iff_real.1
      rw [← hτε, hτℓ]
    have haa : (a : D) * (a : D) = algebraMap ℝ D r := by
      have : ℓ = algebraMap ℝ L r := by
        apply ε.injective
        rw [hr, ε.commutes]; rfl
      exact congrArg Subtype.val this
    have hrneg : r < 0 := by
      by_contra hnr
      push Not at hnr
      set c : D := algebraMap ℝ D (Real.sqrt r) with hc
      have hcc : c * c = (a : D) * (a : D) := by
        rw [hc, ← map_mul, Real.mul_self_sqrt hnr, haa]
      have hca : c * (a : D) = a * c := Algebra.commutes _ _
      have hprod : ((a : D) - c) * (a + c) = 0 := by
        rw [sub_mul, mul_add, mul_add, hca]
        rw [hcc]; abel
      have hci : c * i = i * c := Algebra.commutes _ _
      have hai' : (a : D) * i = i * a := by
        rcases mul_eq_zero.1 hprod with h | h
        · have : (a : D) = c := sub_eq_zero.1 h
          rw [this, hci]
        · have : (a : D) = -c := eq_neg_of_add_eq_zero_left h
          rw [this, neg_mul, mul_neg, hci]
      have e : i * a = -(i * a) := hai'.symm.trans hai
      have h0 : i * a = 0 := by
        have h2 : (2 : ℝ) • (i * a) = 0 := by
          rw [two_smul]
          calc i * a + i * a = -(i * a) + i * a := by rw [← e]
            _ = 0 := neg_add_cancel _
        exact (smul_eq_zero.1 h2).resolve_left (by norm_num)
      have hi0 : i = 0 := by
        calc i = (i * a) * ↑a⁻¹ := by simp
          _ = 0 := by rw [h0, zero_mul]
      rw [hi0, mul_zero] at hi
      exact one_ne_zero (neg_eq_zero.1 hi.symm)
    set t : ℝ := Real.sqrt (-r) with ht
    have htpos : 0 < t := Real.sqrt_pos.2 (by linarith)
    have htt : t * t = -r := Real.mul_self_sqrt (by linarith)
    let j : D := t⁻¹ • (a : D)
    have hj : j * j = -1 := by
      show (t⁻¹ • (a : D)) * (t⁻¹ • (a : D)) = -1
      rw [smul_mul_smul_comm, haa, Algebra.algebraMap_eq_smul_one, smul_smul]
      have : t⁻¹ * t⁻¹ * r = -1 := by
        field_simp
        linarith
      rw [this, neg_smul, one_smul]
    have hji : j * i = -(i * j) := by
      show (t⁻¹ • (a : D)) * i = -(i * (t⁻¹ • (a : D)))
      rw [smul_mul_assoc, mul_smul_comm, hai, smul_neg]
    obtain ⟨e⟩ := quaternionEquiv D hD4 i j hi hj hji
    exact ⟨e.symm⟩

/-- Frobenius' theorem as used by Milne (Example 2.14 (b), §4 "The real numbers"): every central
simple $\mathbb R$-algebra is isomorphic to a matrix algebra over $\mathbb R$ or over Hamilton's
quaternions $\mathbb H$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §4, central simple algebras over R, p. 139"]
theorem centralSimple_real (A : Type*) [Ring A] [Algebra ℝ A] [Algebra.IsCentral ℝ A]
    [IsSimpleRing A] [FiniteDimensional ℝ A] :
    ∃ n : ℕ, n ≠ 0 ∧ (Nonempty (A ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ) ∨
      Nonempty (A ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℍ[ℝ])) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite ℝ A
  obtain ⟨r, hr, D, _, _, _, ⟨f⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite ℝ A
  have hcen : Algebra.IsCentral ℝ D := by
    refine ⟨fun z hz => ?_⟩
    have hw : f.symm (Matrix.diagonal fun _ => z) ∈ Subalgebra.center ℝ A := by
      rw [Subalgebra.mem_center_iff]
      intro b
      apply f.injective
      simp only [map_mul, AlgEquiv.apply_symm_apply]
      ext i j
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
      exact Subalgebra.mem_center_iff.mp hz _
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out (K := ℝ) hw)
    have h2 := congrArg f hc
    rw [AlgEquiv.commutes, AlgEquiv.apply_symm_apply] at h2
    have h3 := congrFun (congrFun h2 ⟨0, Nat.pos_of_ne_zero hr.out⟩) ⟨0, Nat.pos_of_ne_zero hr.out⟩
    refine Algebra.mem_bot.mpr ⟨c, ?_⟩
    simp [Matrix.algebraMap_matrix_apply] at h3
    exact h3
  refine ⟨r, hr.out, ?_⟩
  rcases real_division_classify D with h | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨f.trans e.mapMatrix⟩
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨f.trans e.mapMatrix⟩

/-- Hamilton's quaternions $\mathbb H$ as an element of `CSA ℝ`. -/
noncomputable def quaternionRealCSA : CSA.{0, 0} ℝ :=
  haveI : Algebra.IsCentral ℝ ℍ[ℝ] := quaternion_isCentral
  { toAlgCat := AlgCat.of ℝ ℍ[ℝ] }

/-- Example 2.14 (b) of Milne (Frobenius): $\mathrm{Br}(\mathbb R)$ is cyclic of order $2$, equal to
$\{[\mathbb R], [\mathbb H]\}$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 2.14(b), p. 130"]
theorem example_2_14b :
    Nat.card (BrauerGroup.{0, 0} ℝ) = 2 ∧
      ∀ x : BrauerGroup.{0, 0} ℝ, x = 1 ∨ x = BrauerGroup.mk quaternionRealCSA := by
  have hne : BrauerGroup.mk quaternionRealCSA ≠ 1 := by
    intro h
    rw [BrauerGroup.mk_eq_one_iff] at h
    obtain ⟨n, hn, ⟨e⟩⟩ := h
    have hdim : Module.finrank ℝ ℍ[ℝ] = Module.finrank ℝ (Matrix (Fin n) (Fin n) ℝ) :=
      e.toLinearEquiv.finrank_eq
    rw [Quaternion.finrank_eq_four, Module.finrank_matrix] at hdim
    simp at hdim
    have hn2 : n = 2 := by
      have : n ≤ 2 := by nlinarith
      interval_cases n <;> omega
    subst hn2
    let E0 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.single 0 0 1
    let E1 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.single 1 1 1
    have hE : E0 * E1 = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [E0, E1, Matrix.mul_apply, Matrix.single_apply]
    have hE0 : E0 ≠ 0 := by
      intro h
      have := congrFun (congrFun h 0) 0
      simp [E0] at this
    have hE1 : E1 ≠ 0 := by
      intro h
      have := congrFun (congrFun h 1) 1
      simp [E1] at this
    have hprod : e.symm E0 * e.symm E1 = 0 := by rw [← map_mul, hE, map_zero]
    rcases (mul_eq_zero (M₀ := ℍ[ℝ])).1 hprod with h | h
    · exact hE0 (e.symm.injective (h.trans (map_zero e.symm).symm))
    · exact hE1 (e.symm.injective (h.trans (map_zero e.symm).symm))
  have hall : ∀ x : BrauerGroup.{0, 0} ℝ, x = 1 ∨ x = BrauerGroup.mk quaternionRealCSA := by
    intro x
    induction x using Quotient.inductionOn with | _ A => ?_
    show BrauerGroup.mk A = 1 ∨ BrauerGroup.mk A = BrauerGroup.mk quaternionRealCSA
    obtain ⟨n, hn, h | h⟩ := centralSimple_real A
    · left
      rw [BrauerGroup.mk_eq_one_iff]
      exact ⟨n, hn, h⟩
    · right
      rw [BrauerGroup.mk_eq_mk_iff]
      obtain ⟨e⟩ := h
      exact ⟨1, n, one_ne_zero, hn, ⟨(BrauerGroup.matOne A).trans e⟩⟩
  refine ⟨?_, hall⟩
  rw [Nat.card_eq_two_iff]
  refine ⟨1, BrauerGroup.mk quaternionRealCSA, hne.symm, ?_⟩
  ext x
  simp only [Set.mem_univ, iff_true, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact hall x

/-- §4 of Milne, the real numbers: $\mathrm{Br}(\mathbb C/\mathbb R)$ is cyclic of order $2$, and
$H^2(\mathbb C/\mathbb R)$ has order $2$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §4, Br(C/R) cyclic of order 2, p. 139"]
theorem relBrauer_complex_real :
    Nat.card (relBrauer ℝ ℂ) = 2 ∧
      Nat.card (groupCohomology.H2 (Rep.ofAlgebraAutOnUnits ℝ ℂ)) = 2 := by
  have hall : ∀ x : BrauerGroup.{0, 0} ℝ, x ∈ relBrauer ℝ ℂ := by
    intro x
    rw [relBrauer, MonoidHom.mem_ker]
    exact example_2_14a _
  have htop : relBrauer ℝ ℂ = ⊤ := eq_top_iff.2 fun x _ => hall x
  have h2 : Nat.card (BrauerGroup.{0, 0} ℝ) = 2 := example_2_14b.1
  have hcard : Nat.card (relBrauer ℝ ℂ) = 2 := by
    rw [htop, Subgroup.card_top]; exact h2
  refine ⟨hcard, ?_⟩
  obtain ⟨f, hinj, -, hrange⟩ := thm_3_14 (K := ℝ) (L := ℂ)
  have hsurj : f.range = ⊤ :=
    eq_top_iff.2 fun y _ => (hrange y.toMul).1 (hall _)
  calc Nat.card (groupCohomology.H2 (Rep.ofAlgebraAutOnUnits ℝ ℂ)) = Nat.card f.range :=
        Nat.card_congr (AddMonoidHom.ofInjective hinj).toEquiv
    _ = Nat.card (Additive (BrauerGroup.{0, 0} ℝ)) := by
        rw [hsurj, AddSubgroup.card_top]
    _ = 2 := by
        rw [Nat.card_congr (Additive.toMul : Additive (BrauerGroup.{0, 0} ℝ) ≃ _), h2]

theorem complex_aut_cases (σ : ℂ ≃ₐ[ℝ] ℂ) : σ = 1 ∨ σ = Complex.conjAe := by
  have h : σ Complex.I * σ Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have h2 : (σ Complex.I - Complex.I) * (σ Complex.I + Complex.I) = 0 := by
    linear_combination h - Complex.I_mul_I
  rcases mul_eq_zero.1 h2 with h3 | h3
  · left
    refine AlgEquiv.coe_toAlgHom_injective (Complex.algHom_ext ?_)
    simpa [sub_eq_zero] using h3
  · right
    refine AlgEquiv.coe_toAlgHom_injective (Complex.algHom_ext ?_)
    have : σ Complex.I = -Complex.I := eq_neg_of_add_eq_zero_left h3
    simp [this]

theorem conjAe_ne_one : (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ) ≠ 1 := by
  intro h
  have := congrArg (fun f : ℂ ≃ₐ[ℝ] ℂ => f Complex.I) h
  simp at this
  have h2 := congrArg Complex.im this
  simp at h2
  norm_num at h2

theorem conjAe_mul_self : (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ) * Complex.conjAe = 1 := by
  ext z
  simp

/-- The 2-cocycle $\varphi$ of $\mathrm{Gal}(\mathbb C/\mathbb R) = \{1, \sigma\}$ with
$\varphi(\sigma, \sigma) = -1$ and $\varphi = 1$ otherwise (Milne, §4). -/
noncomputable def realCocycle : NormalizedCocycle ℝ ℂ :=
  open Classical in
  ⟨fun p => if p.1 ≠ 1 ∧ p.2 ≠ 1 then -1 else 1, by
    intro σ τ ρ
    have hc := conjAe_ne_one
    have hm := conjAe_mul_self
    rcases complex_aut_cases σ with rfl | rfl <;> rcases complex_aut_cases τ with rfl | rfl <;>
      rcases complex_aut_cases ρ with rfl | rfl <;>
      simp [hc, hm], by simp⟩

/-- §4 of Milne, the real numbers: the crossed product $A(\varphi)$ of the nontrivial cocycle is
isomorphic to $\mathbb H$ (the $\mathbb C$-linear map sending $e_\sigma$ to $j$). -/
@[kb "milne2020cft" "v4.03, Ch. IV, §4, A(φ) ≅ H for Gal(C/R), p. 139"]
theorem crossedProduct_realCocycle :
    Nonempty (CrossedProduct realCocycle ≃ₐ[ℝ] ℍ[ℝ]) := by
  have hc := conjAe_ne_one
  have hm := conjAe_mul_self
  have hφcc : ((realCocycle (Complex.conjAe, Complex.conjAe) : ℂˣ) : ℂ) = -1 := by
    simp [realCocycle, hc]
  have hdim : Module.finrank ℝ (CrossedProduct realCocycle) = 4 := by
    rw [CrossedProduct.finrank_eq, Complex.finrank_real_complex]; norm_num
  have hneg : ∀ (σ : ℂ ≃ₐ[ℝ] ℂ) (a : ℂ), CrossedProduct.single realCocycle σ (-a) =
      -CrossedProduct.single realCocycle σ a := by
    intro σ a
    funext ρ
    show CrossedProduct.single realCocycle σ (-a) ρ = -(CrossedProduct.single realCocycle σ a ρ)
    simp only [CrossedProduct.single_apply]
    split_ifs <;> simp
  have hi : CrossedProduct.incl realCocycle Complex.I * CrossedProduct.incl realCocycle Complex.I
      = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have hj : CrossedProduct.single realCocycle Complex.conjAe 1 *
      CrossedProduct.single realCocycle Complex.conjAe 1 = -1 := by
    rw [CrossedProduct.single_mul_single, hm, hφcc]
    simp only [map_one, mul_one, one_mul]
    rw [hneg]
    rfl
  have hji : CrossedProduct.single realCocycle Complex.conjAe 1 *
      CrossedProduct.incl realCocycle Complex.I = -(CrossedProduct.incl realCocycle Complex.I *
      CrossedProduct.single realCocycle Complex.conjAe 1) := by
    show CrossedProduct.single realCocycle Complex.conjAe 1 *
      CrossedProduct.single realCocycle 1 Complex.I = -(CrossedProduct.single realCocycle 1
      Complex.I * CrossedProduct.single realCocycle Complex.conjAe 1)
    rw [CrossedProduct.single_mul_single, CrossedProduct.single_mul_single]
    simp [NormalizedCocycle.one_left, NormalizedCocycle.one_right, ← hneg]
  obtain ⟨e⟩ := quaternionEquiv (CrossedProduct realCocycle) hdim
    (CrossedProduct.incl realCocycle Complex.I)
    (CrossedProduct.single realCocycle Complex.conjAe 1) hi hj hji
  exact ⟨e.symm⟩

end Real

/-! ### Nonarchimedean local fields -/

section Local

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable (K) in
/-- The normalized valuation $\mathrm{ord}_K : K \to \mathbb Z$ ($\mathrm{ord}_K(0) = 0$ by
convention), with $\mathrm{ord}_K(K^\times) = \mathbb Z$. -/
noncomputable def ordK (x : K) : ℤ :=
  -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (ValuativeRel.valuation K x))

variable (K) in
/-- Milne's extension of $\mathrm{ord}_K$ to a central division algebra $D$ (§4, p. 139):
$\mathrm{ord}(\alpha) = \mathrm{ord}_K(\mathrm{Nm}_{D/K}\alpha)/[D : K]$, a rational number. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §4, the valuation ord on D, p. 139"]
noncomputable def ordD (D : Type u) [Ring D] [Algebra K D] (α : D) : ℚ :=
  (ordK K (Algebra.norm K α) : ℚ) / Module.finrank K D

/-- A subfield $L$ of $D$ is *unramified* over $K$ if $\mathrm{ord}(L^\times) \subseteq \mathbb Z$
(ramification index $1$). -/
def IsUnramifiedSubfield (D : Type u) [Ring D] [Algebra K D] (L : Subalgebra K D) : Prop :=
  ∀ x : L, x ≠ 0 → ∃ m : ℤ, ordD K D (x : D) = m

/-- $\sigma \in \mathrm{Gal}(L/K)$ is the Frobenius automorphism of the subfield $L \subseteq D$:
$\sigma(x) \equiv x^q$ modulo the maximal ideal for every integral $x \in L$, where $q$ is the
order of the residue field of $K$. -/
def IsFrobeniusOn (D : Type u) [Ring D] [Algebra K D] (L : Subalgebra K D) (σ : L ≃ₐ[K] L) :
    Prop :=
  ∀ x : L, 0 ≤ ordD K D (x : D) →
    (σ x : D) = (x : D) ^ Nat.card 𝓀[K] ∨ 0 < ordD K D ((σ x : D) - (x : D) ^ Nat.card 𝓀[K])

variable (K) in
/-- Milne's local invariant (§4, p. 140, definition in prose), as a relation: $r$ is an invariant of
the central division algebra $D$ if there are a maximal subfield $L$ unramified over $K$, its
Frobenius $\sigma$, and $\alpha \in D^\times$ with $\sigma x = \alpha x \alpha^{-1}$ for $x \in L$ and
$r = \mathrm{ord}(\alpha)$; then $\mathrm{inv}_K(D) = r \bmod \mathbb Z$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §4, def. of the local invariant inv_K, p. 140"]
def IsLocalInvariant (D : Type u) [Ring D] [Algebra K D] (r : ℚ) : Prop :=
  ∃ (L : Subalgebra K D) (_ : IsField L) (σ : L ≃ₐ[K] L) (α : Dˣ),
    Module.finrank K D = Module.finrank K L ^ 2 ∧ IsUnramifiedSubfield D L ∧
      IsFrobeniusOn D L σ ∧ (∀ x : L, (σ x : D) = α * x * ↑α⁻¹) ∧ r = ordD K D (α : D)

/-- $\mathbb Q/\mathbb Z$. -/
abbrev QZ : Type := ℚ ⧸ (Int.castAddHom ℚ).range

/-- A central division algebra over $K$, as a ring with every nonzero element a unit (the form
in which `CSA K` representatives are division algebras, Remark 2.13 (a)). -/
def IsDivisionAlgebra (D : Type u) [Ring D] : Prop := ∀ d : D, d ≠ 0 → IsUnit d

/-- The facts about a central division algebra $D$ over a nonarchimedean local field that Milne
verifies or sketches on pp. 139–140 (named statement): the extended valuation is ultrametric
("it is possible to verify"), $D$ has a maximal subfield unramified over $K$ (from $e = f = n$),
so $D$ has a local invariant, and the invariant is well defined modulo $\mathbb Z$ ("it depends
only on the isomorphism class of $D$"). `exists_invariant` assumes `Nontrivial D` (Milne's division algebras are
nonzero; the zero ring satisfies the other hypotheses vacuously and has no subfield, so without it the field was
false; corrected 2026-11-05). -/
@[kb "milne2020cft" "v4.03, Ch. IV, §4, valuation and unramified maximal subfield of D, pp. 139-140"]
structure LocalDivisionAlgebraFacts (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop where
  ordD_add : ∀ (D : Type u) [Ring D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D], IsDivisionAlgebra D → ∀ α β : D, α ≠ 0 → β ≠ 0 → α + β ≠ 0 →
      min (ordD K D α) (ordD K D β) ≤ ordD K D (α + β)
  exists_invariant : ∀ (D : Type u) [Ring D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] [Nontrivial D], IsDivisionAlgebra D → ∃ r : ℚ, IsLocalInvariant K D r
  invariant_wellDefined : ∀ (D D' : Type u) [Ring D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] [Ring D'] [Algebra K D'] [Algebra.IsCentral K D']
    [FiniteDimensional K D'], IsDivisionAlgebra D → IsDivisionAlgebra D' → (D ≃ₐ[K] D') →
      ∀ r r' : ℚ, IsLocalInvariant K D r → IsLocalInvariant K D' r' → ∃ m : ℤ, r - r' = m

/-- The local invariant $\mathrm{inv}_K : \mathrm{Br}(K) \to \mathbb Q/\mathbb Z$ (Milne, p. 140),
defined from the named statement `LocalDivisionAlgebraFacts`: the invariant of a central division
algebra representing the class (Remark 2.13 (a)). -/
noncomputable def invK (h : LocalDivisionAlgebraFacts K) (x : BrauerGroup.{u, u} K) : QZ :=
  let D : CSA.{u, u} K := Classical.choose (remark_2_13a_exists x)
  QuotientAddGroup.mk (Classical.choose (h.exists_invariant D
    (Classical.choose_spec (remark_2_13a_exists x)).1))

/-- $\mathrm{inv}_K$ computed on any central division algebra representing the class. -/
theorem invK_eq (h : LocalDivisionAlgebraFacts K) (D : CSA.{u, u} K) (hD : IsDivisionAlgebra D)
    (r : ℚ) (hr : IsLocalInvariant K D r) : invK h (BrauerGroup.mk D) = QuotientAddGroup.mk r := by
  obtain ⟨hD₀, hmk⟩ := Classical.choose_spec (remark_2_13a_exists (BrauerGroup.mk D))
  obtain ⟨e⟩ := (remark_2_13a_unique _ D hD₀ hD).1 hmk
  obtain ⟨m, hm⟩ := h.invariant_wellDefined _ D hD₀ hD e _ r
    (Classical.choose_spec (h.exists_invariant _ hD₀)) hr
  simp only [invK]
  rw [QuotientAddGroup.eq]
  refine ⟨-m, ?_⟩
  simp
  linarith

/-- Proposition 4.3 of Milne (named statement; Hasse): the invariant
$\mathrm{inv}_K : \mathrm{Br}(K) \to \mathbb Q/\mathbb Z$ is a bijection. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Prop. 4.3, p. 141"]
structure Prop4_3 (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop where
  facts : LocalDivisionAlgebraFacts K
  bijective : Function.Bijective (invK facts)

/-- Remark 4.4 (a) of Milne (named statement): the invariant map is a homomorphism (it agrees with
the cohomological invariant of Chapter III). -/
@[kb "milne2020cft" "v4.03, Ch. IV, Rem. 4.4(a), p. 141"]
structure Remark4_4a (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop where
  facts : LocalDivisionAlgebraFacts K
  map_mul : ∀ x y : BrauerGroup.{u, u} K, invK facts (x * y) = invK facts x + invK facts y

/-- Example 2.14 (d) of Milne (Hasse), from Proposition 4.3 and Remark 4.4 (a): the Brauer group
of a nonarchimedean local field is isomorphic to $\mathbb Q/\mathbb Z$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 2.14(d), p. 130"]
theorem example_2_14d (h : Prop4_3 K) (h' : Remark4_4a K) :
    Nonempty (Additive (BrauerGroup.{u, u} K) ≃+ QZ) := by
  have hf : h'.facts = h.facts := rfl
  have hmul : ∀ x y : BrauerGroup.{u, u} K,
      invK h.facts (x * y) = invK h.facts x + invK h.facts y := by
    intro x y
    have := h'.map_mul x y
    rwa [hf] at this
  let f : Additive (BrauerGroup.{u, u} K) →+ QZ :=
    AddMonoidHom.mk' (fun x => invK h.facts x.toMul) fun x y => hmul x.toMul y.toMul
  exact ⟨AddEquiv.ofBijective f h.bijective⟩

theorem ordK_zero : ordK K (0 : K) = 0 := by
  simp [ordK]

theorem ordK_pow (x : K) (k : ℕ) : ordK K (x ^ k) = k * ordK K x := by
  unfold ordK
  rw [map_pow, map_pow, WithZero.log_pow]
  simp

theorem ordD_algebraMap (D : Type u) [Ring D] [Algebra K D] [FiniteDimensional K D] (π : K)
    (hπ : ordK K π = 1) (hD : 0 < Module.finrank K D) :
    ordD K D (algebraMap K D π) = 1 := by
  unfold ordD
  rw [Algebra.norm_algebraMap, ordK_pow, hπ]
  have : (Module.finrank K D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  push_cast
  field_simp

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem crossed_pow_single {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (φ : NormalizedCocycle K L) (n : ℕ)
    (h : ∀ k, k + 1 < n → (φ (σ ^ k, σ) : L) = 1) :
    ∀ k, k < n → CrossedProduct.single φ σ 1 ^ k = CrossedProduct.single φ (σ ^ k) 1 := by
  intro k
  induction k with
  | zero => intro _; rw [pow_zero, pow_zero]; rfl
  | succ k ih =>
    intro hk
    rw [pow_succ, ih (by omega), CrossedProduct.single_mul_single, h k hk, pow_succ]
    simp

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem example_4_2_conj {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (φ : NormalizedCocycle K L) (a : L) :
    CrossedProduct.single φ σ 1 * CrossedProduct.incl φ a =
        CrossedProduct.incl φ (σ a) * CrossedProduct.single φ σ 1 := by
  show CrossedProduct.single φ σ 1 * CrossedProduct.single φ 1 a =
    CrossedProduct.single φ 1 (σ a) * CrossedProduct.single φ σ 1
  rw [CrossedProduct.single_mul_single, CrossedProduct.single_mul_single]
  simp [NormalizedCocycle.one_left, NormalizedCocycle.one_right]

/-- Example 4.2 (ii), (iii) for `n ≥ 2` (for `n = 1` the displayed cocycle is trivial and the
statement `e_σ ^ 1 = π` fails). -/
theorem example_4_2_aux (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (π : K)
    (hπ : ordK K π = 1) (φ : NormalizedCocycle K L)
    (hφ : ∀ i j : ℕ, i < Module.finrank K L → j < Module.finrank K L →
      (φ (σ ^ i, σ ^ j) : L) = if i + j ≤ Module.finrank K L - 1 then 1 else algebraMap K L π)
    (hn : 2 ≤ Module.finrank K L) :
    CrossedProduct.single φ σ 1 ^ Module.finrank K L = algebraMap K (CrossedProduct φ) π ∧
      ordD K (CrossedProduct φ) (CrossedProduct.single φ σ 1) = 1 / Module.finrank K L := by
  set n := Module.finrank K L with hn'
  have hσn : σ ^ n = 1 := by
    rw [hn', ← IsGalois.card_aut_eq_finrank K L]
    exact pow_card_eq_one'
  have hpow := crossed_pow_single σ φ n (fun k hk => by
    have := hφ k 1 (by omega) (by omega)
    simp only [pow_one, show k + 1 ≤ n - 1 ↔ True by simp; omega, ↓reduceIte] at this
    exact this) (n - 1) (by omega)
  have hlast := hφ (n - 1) 1 (by omega) (by omega)
  simp only [pow_one, show n - 1 + 1 ≤ n - 1 ↔ False by simp, ↓reduceIte] at hlast
  have e1 : CrossedProduct.single φ σ 1 ^ n = algebraMap K (CrossedProduct φ) π := by
    have h1 : CrossedProduct.single φ σ 1 ^ n =
        CrossedProduct.single φ σ 1 ^ (n - 1) * CrossedProduct.single φ σ 1 := by
      rw [← pow_succ]; congr 1; omega
    rw [h1, hpow, CrossedProduct.single_mul_single, hlast, ← pow_succ,
      show n - 1 + 1 = n by omega, hσn]
    simp only [map_one, one_mul]
    exact (CrossedProduct.incl φ).commutes π
  refine ⟨e1, ?_⟩
  have hnorm : (Algebra.norm K (CrossedProduct.single φ σ 1)) ^ n = π ^ (n ^ 2) := by
    rw [← map_pow, e1, Algebra.norm_algebraMap, CrossedProduct.finrank_eq]
  have h1 : (n : ℤ) * ordK K (Algebra.norm K (CrossedProduct.single φ σ 1)) = n ^ 2 * 1 := by
    have := congrArg (ordK K) hnorm
    rw [ordK_pow, ordK_pow, hπ] at this
    push_cast at this
    exact this
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have h2 : ordK K (Algebra.norm K (CrossedProduct.single φ σ 1)) = n := by
    apply mul_left_cancel₀ hn0
    rw [h1]; ring
  unfold ordD
  rw [h2, CrossedProduct.finrank_eq, ← hn']
  have : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  push_cast
  field_simp

/-- Example 4.2 of Milne: let $L \subseteq A$ be the unramified extension of degree $n$ with
Frobenius $\sigma$, and $\pi$ a prime element of $K$.  For the cocycle
$\varphi(\sigma^i, \sigma^j) = 1$ if $i + j \le n - 1$ and $\pi$ otherwise, the element $e_\sigma$
of $A(\varphi)$ satisfies $e_\sigma a e_\sigma^{-1} = \sigma a$ and $e_\sigma^n = \pi$, so
$\mathrm{ord}(e_\sigma) = 1/n$, i.e. $\mathrm{inv}_K(A(\varphi)) = 1/n$.

Stated for a finite Galois extension $L/K$ of degree $n$ with $\mathrm{Gal}(L/K)$ cyclic generated
by $\sigma$; `φ` is any normalized cocycle with the displayed values (indices $0 \le i, j < n$).
The computation $e_\sigma^n = \pi$ needs $n \ge 2$ (for $n = 1$, $e_\sigma = e_1 = 1$); Milne leaves this
implicit, so the hypothesis `2 ≤ finrank K L` is added. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 4.2, p. 140"]
theorem example_4_2 (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, ∃ i : ℕ, τ = σ ^ i) (π : K) (hπ : ordK K π = 1)
    (φ : NormalizedCocycle K L)
    (hφ : ∀ i j : ℕ, i < Module.finrank K L → j < Module.finrank K L →
      (φ (σ ^ i, σ ^ j) : L) = if i + j ≤ Module.finrank K L - 1 then 1 else algebraMap K L π)
    (hn : 2 ≤ Module.finrank K L) :
    (∀ a : L, CrossedProduct.single φ σ 1 * CrossedProduct.incl φ a =
        CrossedProduct.incl φ (σ a) * CrossedProduct.single φ σ 1) ∧
      CrossedProduct.single φ σ 1 ^ Module.finrank K L = algebraMap K (CrossedProduct φ) π ∧
      ordD K (CrossedProduct φ) (CrossedProduct.single φ σ 1) = 1 / Module.finrank K L := by
  exact ⟨fun a => example_4_2_conj σ φ a, example_4_2_aux L σ π hπ φ hφ hn⟩

/-- Example 4.2 of Milne, conclusion $\mathrm{inv}_K(A(\varphi)) = 1/n$: if moreover $L = L e_1$ is
unramified in $A(\varphi)$ and $\sigma$ is its Frobenius, then $1/n$ is a local invariant of
$A(\varphi)$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 4.2, p. 140"]
theorem example_4_2_inv (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, ∃ i : ℕ, τ = σ ^ i) (π : K)
    (hπ : ordK K π = 1) (φ : NormalizedCocycle K L)
    (hφ : ∀ i j : ℕ, i < Module.finrank K L → j < Module.finrank K L →
      (φ (σ ^ i, σ ^ j) : L) = if i + j ≤ Module.finrank K L - 1 then 1 else algebraMap K L π)
    (hunr : IsUnramifiedSubfield (CrossedProduct φ) (CrossedProduct.incl φ).range)
    (hfrob : IsFrobeniusOn (CrossedProduct φ) (CrossedProduct.incl φ).range
      (((AlgEquiv.ofInjective (CrossedProduct.incl φ) (CrossedProduct.incl φ).toRingHom.injective).symm.trans
        σ).trans (AlgEquiv.ofInjective (CrossedProduct.incl φ)
          (CrossedProduct.incl φ).toRingHom.injective))) :
    IsLocalInvariant K (CrossedProduct φ) (1 / Module.finrank K L) := by
  set n := Module.finrank K L with hn'
  have hnpos : 0 < n := Module.finrank_pos
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [ordK_zero] at hπ
    exact zero_ne_one hπ
  let f := CrossedProduct.incl φ
  have hinj : Function.Injective f := (CrossedProduct.incl φ).toRingHom.injective
  let eqv := AlgEquiv.ofInjective f hinj
  have hσ'x : ∀ a : L, ((((eqv.symm.trans σ).trans eqv) ⟨f a, a, rfl⟩ : f.range) :
      CrossedProduct φ) = f (σ a) := by
    intro a
    have : eqv.symm ⟨f a, a, rfl⟩ = a := by
      rw [AlgEquiv.symm_apply_eq]
      apply Subtype.ext
      simp [eqv]
    simp [this, eqv]
  have hfield : IsField f.range := MulEquiv.isField (Field.toIsField L) eqv.symm.toMulEquiv
  have hdim : Module.finrank K (CrossedProduct φ) = Module.finrank K f.range ^ 2 := by
    rw [CrossedProduct.finrank_eq, eqv.toLinearEquiv.finrank_eq]
  obtain ⟨α, hα, hαord⟩ : ∃ α : (CrossedProduct φ)ˣ, (∀ a : L, (α : CrossedProduct φ) * f a =
      f (σ a) * α) ∧ ordD K (CrossedProduct φ) (α : CrossedProduct φ) = 1 / n := by
    by_cases h2 : 2 ≤ n
    · obtain ⟨he, hord⟩ := example_4_2_aux L σ π hπ φ hφ h2
      let c : CrossedProduct φ := algebraMap K (CrossedProduct φ) π⁻¹
      have hc : c * algebraMap K (CrossedProduct φ) π = 1 := by
        simp only [c, ← map_mul, inv_mul_cancel₀ hπ0, map_one]
      have h1 : CrossedProduct.single φ σ 1 * (c * CrossedProduct.single φ σ 1 ^ (n - 1)) = 1 := by
        rw [← mul_assoc, ← Algebra.commutes, mul_assoc, ← pow_succ',
          show n - 1 + 1 = n by omega, he, hc]
      have h2' : (c * CrossedProduct.single φ σ 1 ^ (n - 1)) * CrossedProduct.single φ σ 1 = 1 := by
        rw [mul_assoc, ← pow_succ, show n - 1 + 1 = n by omega, he, hc]
      exact ⟨⟨_, _, h1, h2'⟩, fun a => example_4_2_conj σ φ a, hord⟩
    · have hn1 : n = 1 := by omega
      have hcard : Nat.card (L ≃ₐ[K] L) = 1 := by
        rw [IsGalois.card_aut_eq_finrank K L]; exact hn1
      obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.1 hcard
      have hσ1 : σ = 1 := Subsingleton.elim _ _
      have hu : IsUnit (algebraMap K (CrossedProduct φ) π) := (isUnit_iff_ne_zero.2 hπ0).map _
      refine ⟨hu.unit, fun a => ?_, ?_⟩
      · rw [hσ1]
        exact Algebra.commutes π (f a)
      · show ordD K (CrossedProduct φ) (algebraMap K (CrossedProduct φ) π) = _
        rw [ordD_algebraMap _ π hπ (by rw [CrossedProduct.finrank_eq]; positivity), hn1]
        simp
  refine ⟨f.range, hfield, (eqv.symm.trans σ).trans eqv, α, hdim, hunr, hfrob, ?_, hαord.symm⟩
  intro x
  obtain ⟨a, ha⟩ := x.2
  have hx : x = ⟨f a, a, rfl⟩ := Subtype.ext (by simpa using ha.symm)
  rw [hx, hσ'x]
  show f (σ a) = α * f a * ↑α⁻¹
  rw [hα, mul_assoc, Units.mul_inv, mul_one]

/-- Remark 4.4 (b) of Milne (named statement): for a central division algebra $D$ over $K$, the
order of $[D]$ in $\mathrm{Br}(K)$ is $\sqrt{[D : K]}$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Rem. 4.4(b), p. 141"]
structure Remark4_4b (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop where
  orderOf_eq : ∀ D : CSA.{u, u} K, IsDivisionAlgebra D →
    orderOf (BrauerGroup.mk D) ^ 2 = Module.finrank K D

/-- Remark 4.4 (c) of Milne, first assertion (named statement; from Chapter III, Theorem 2.1:
$\mathrm{Br}(K) \to \mathrm{Br}(L)$ multiplies the invariant by $[L : K]$): a central division
algebra of degree $n^2$ over $K$ is split by every extension $L$ of $K$ of degree $n$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Rem. 4.4(c), p. 141"]
structure Remark4_4c (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop where
  isSplitBy : ∀ (D : Type u) [Ring D] [Algebra K D] [Algebra.IsCentral K D] [IsSimpleRing D]
    [FiniteDimensional K D], IsDivisionAlgebra D → ∀ (L : Type u) [Field L] [Algebra K L] (n : ℕ),
      Module.finrank K D = n ^ 2 → Module.finrank K L = n → IsSplitBy (K := K) L D

/-- Remark 4.4 (c) of Milne, second assertion, proved from the first and Corollary 3.7: every
irreducible polynomial of degree $n$ over $K$ has a root in a central division algebra $D$ of
degree $n^2$ over $K$. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Rem. 4.4(c), p. 141"]
theorem remark_4_4c_root (h : Remark4_4c K) (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D] (n : ℕ)
    (hD : Module.finrank K D = n ^ 2) (p : Polynomial K) (hp : Irreducible p)
    (hdeg : p.natDegree = n) : ∃ x : D, Polynomial.aeval x p = 0 := by
  have : Fact (Irreducible p) := ⟨hp⟩
  have hL : Module.finrank K (AdjoinRoot p) = n := by
    rw [(AdjoinRoot.powerBasis hp.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hdiv : IsDivisionAlgebra D := fun d hd => isUnit_iff_ne_zero.2 hd
  have hs := h.isSplitBy D hdiv (AdjoinRoot p) n hD hL
  obtain ⟨ι⟩ := (cor_3_7 (K := K) D (AdjoinRoot p) hD hL).1 hs
  refine ⟨ι (AdjoinRoot.root p), ?_⟩
  rw [Polynomial.aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

end Local

end NumberFieldKB.MilneCFT.Ch4
