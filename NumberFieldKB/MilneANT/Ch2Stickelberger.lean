import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import QuadFormsKB.Citation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc

/-!
# Milne, *Algebraic Number Theory*, Proposition 2.40: sign of the discriminant and Stickelberger's theorem

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Prop. 2.40, p. 39; bib key `milne2020ant`.

* (a) `prop_2_40_a`: the sign of $\mathrm{disc}(\mathcal O_K/\mathbb Z)$ is $(-1)^s$, $s$ the number of complex
  places (Mathlib's `NumberField.sign_discr`).
* (b) `prop_2_40_b` (Stickelberger): $\mathrm{disc}(\mathcal O_K/\mathbb Z) \equiv 0$ or $1 \pmod 4$.
-/

open NumberField

namespace NumberFieldKB.MilneANT

/-- **Proposition 2.40 (a).** The sign of the discriminant of a number field $K$ is $(-1)^s$, where $2s$ is the
number of embeddings $K \hookrightarrow \mathbb C$ with image not contained in $\mathbb R$ ($s$ = number of complex
places). Restates Mathlib's `NumberField.sign_discr`. -/
@[kb "milne2020ant" "v3.08, Prop. 2.40 (a), p. 39"]
theorem prop_2_40_a (K : Type*) [Field K] [NumberField K] :
    (discr K).sign = (-1) ^ InfinitePlace.nrComplexPlaces K :=
  NumberField.sign_discr K

/-- Splitting the determinant as `P - N` and the permanent as `P + N`: `4 P N = perm² - det²`
with `P N` integral when the entries are. -/
private lemma exists_Q {E : Type*} [CommRing E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι E) (h : ∀ i j, IsIntegral ℤ (M i j)) :
    ∃ Q : E, IsIntegral ℤ Q ∧ 4 * Q = M.permanent ^ 2 - M.det ^ 2 := by
  let P : E := ∑ σ : Equiv.Perm ι, if Equiv.Perm.sign σ = 1 then ∏ i, M (σ i) i else 0
  let N : E := ∑ σ : Equiv.Perm ι, if Equiv.Perm.sign σ = 1 then 0 else ∏ i, M (σ i) i
  have hdet : M.det = P - N := by
    rw [Matrix.det_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
  have hperm : M.permanent = P + N := by
    rw [Matrix.permanent, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    split_ifs <;> simp
  have hprod : ∀ σ : Equiv.Perm ι, IsIntegral ℤ (∏ i, M (σ i) i) := fun σ =>
    IsIntegral.prod _ fun i _ => h _ _
  refine ⟨P * N, IsIntegral.mul ?_ ?_, ?_⟩
  · exact IsIntegral.sum _ fun σ _ => by
      split_ifs
      exacts [hprod σ, isIntegral_zero]
  · exact IsIntegral.sum _ fun σ _ => by
      split_ifs
      exacts [isIntegral_zero, hprod σ]
  · rw [hdet, hperm]; ring

private lemma mod_four_of_eq {s D Q : ℤ} (h : 4 * Q = s ^ 2 - D) : D % 4 = 0 ∨ D % 4 = 1 := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' s
  · subst hk; left; have : D = (2 * k) ^ 2 - 4 * Q := by linarith
    subst this; ring_nf; omega
  · subst hk; right; have : D = (2 * k + 1) ^ 2 - 4 * Q := by linarith
    subst this; ring_nf; omega

/-- **Proposition 2.40 (b)** (Stickelberger's theorem). The discriminant of a number field is congruent to $0$ or
$1$ modulo $4$. -/
@[kb "milne2020ant" "v3.08, Prop. 2.40 (b), p. 39"]
theorem prop_2_40_b (K : Type*) [Field K] [NumberField K] : discr K % 4 = 0 ∨ discr K % 4 = 1 := by
  classical
  let E := AlgebraicClosure ℚ
  let b := integralBasis K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) =
      Fintype.card (K →ₐ[ℚ] E) := by
    rw [AlgHom.card ℚ K E]
    exact (Module.finrank_eq_card_basis b).symm
  let e := Fintype.equivOfCardEq hcard
  let M := Algebra.embeddingsMatrixReindex ℚ E b e
  have hM : ∀ i j, M i j = e j (b i) := by
    intro i j
    simp [M, Algebra.embeddingsMatrixReindex, Matrix.reindex_apply]
  have hint : ∀ i j, IsIntegral ℤ (M i j) := by
    intro i j
    rw [hM, integralBasis_apply]
    have : IsIntegral ℤ (algebraMap (𝓞 K) K (RingOfIntegers.basis K i)) :=
      RingOfIntegers.isIntegral_coe _
    exact this.map ((e j).restrictScalars ℤ)
  have hdisc : M.det ^ 2 = ((discr K : ℤ) : E) := by
    have := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ E b e
    rw [← this, ← NumberField.coe_discr]
    simp
  -- the permanent is Galois invariant
  have hfix : ∀ τ : E ≃ₐ[ℚ] E, τ M.permanent = M.permanent := by
    intro τ
    let f : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → Module.Free.ChooseBasisIndex ℤ (𝓞 K) :=
      fun i => e.symm (τ.toAlgHom.comp (e i))
    have hf : Function.Injective f := by
      intro i j hij
      apply e.injective
      have h1 := e.symm.injective hij
      ext x
      exact τ.injective (congrArg (fun g : K →ₐ[ℚ] E => g x) h1)
    let π := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
    have hπ : ∀ i j, τ (M i j) = M i (π j) := by
      intro i j
      rw [hM, hM]
      have : e (π j) = τ.toAlgHom.comp (e j) := by simp [π, f]
      rw [this]; rfl
    have : τ M.permanent = (M.submatrix id π).permanent := by
      simp only [Matrix.permanent, map_sum, map_prod, hπ, Matrix.submatrix_apply, id]
    rw [this, Matrix.permanent_permute_rows]
  obtain ⟨q, hq⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) (K := E)
    M.permanent).2 hfix
  obtain ⟨Q, hQ, h4⟩ := exists_Q M hint
  have hperm_int : IsIntegral ℤ M.permanent := by
    unfold Matrix.permanent
    exact IsIntegral.sum _ fun σ _ => IsIntegral.prod _ fun i _ => hint _ _
  have hqint : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (A := ℚ) (B := E), hq]
    exact hperm_int
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.1 hqint
  have hsE : M.permanent = (s : E) := by
    rw [← hq, ← hs]; simp
  rw [hsE, hdisc] at h4
  set z : ℤ := s ^ 2 - discr K with hz
  have h4' : 4 * Q = (z : E) := by rw [h4]; simp [hz]
  have hQrat : Q = algebraMap ℚ E ((z : ℚ) / 4) := by
    have h4ne : (4 : E) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h4ne
    rw [h4']
    simp [mul_div_cancel₀]
  have hQint : IsIntegral ℤ ((z : ℚ) / 4) := by
    rw [← isIntegral_algebraMap_iff (A := ℚ) (B := E), ← hQrat]
    exact hQ
  obtain ⟨Qz, hQz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hQint
  have : 4 * Qz = z := by
    have h5 : (4 : ℚ) * Qz = z := by
      simp only [eq_intCast] at hQz
      rw [hQz]; ring
    exact_mod_cast h5
  exact mod_four_of_eq (s := s) (D := discr K) (Q := Qz) (by rw [this, hz])

end NumberFieldKB.MilneANT
