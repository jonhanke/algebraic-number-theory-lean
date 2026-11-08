import NumberFieldKB.WeilBNT.QLattices

/-!
# Weil, *Basic Number Theory*, V.§1 Prop. 3: elements of an order are integral

$\mathcal A$ is a finite-dimensional algebra over $\mathbb Q$ (not necessarily commutative), $R$ an order of
$\mathcal A$ (`IsQOrder R`, Weil V.§1 Def. 2). Weil's trace and norm $\mathrm{Tr}_{\mathcal A/\mathbb Q}(a)$,
$N_{\mathcal A/\mathbb Q}(a)$ are the trace and determinant of left multiplication $x\mapsto ax$ on $\mathcal A$
(the regular representation).

* **`weil_V_1_prop3`**: every $a\in R$ is integral over $\mathbb Z$, and $\mathrm{Tr}_{\mathcal A/\mathbb Q}(a)$,
  $N_{\mathcal A/\mathbb Q}(a)$ are integers.

Weil's proof: write $a\,a_i=\sum_jc_{ij}a_j$ with $c_{ij}\in\mathbb Z$ for generators $a_i$ of $R$; the
characteristic polynomial $D(T)=\det(\delta_{ij}T-c_{ij})$ is monic in $\mathbb Z[T]$ and kills $a$; taking for the
$a_i$ a $\mathbb Q$-basis of $\mathcal A$ (Cor. 1 of Prop. 1), the trace and norm are the trace and determinant of the
integer matrix $(c_{ij})$.
-/

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT

variable {A : Type*} [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A]

/-- **Weil, V.§1 Prop. 3.** Let $a$ be an element of an order $R$ of a finite-dimensional $\mathbb Q$-algebra
$\mathcal A$. Then $a$ is integral over $\mathbb Z$, and $\mathrm{Tr}_{\mathcal A/\mathbb Q}(a)$ and
$N_{\mathcal A/\mathbb Q}(a)$ (trace and determinant of $x\mapsto ax$) are in $\mathbb Z$. -/
@[kb "weil1973bnt" "Ch. V, §1, Prop. 3 (p. 81)"]
theorem weil_V_1_prop3 {R : Subring A} (hR : IsQOrder R) {a : A} (ha : a ∈ R) :
    IsIntegral ℤ a ∧
      (∃ z : ℤ, LinearMap.trace ℚ A (LinearMap.mulLeft ℚ a) = z) ∧
      ∃ z : ℤ, LinearMap.det (LinearMap.mulLeft ℚ a) = z := by
  obtain ⟨n, b, hbR, hcl⟩ := weil_V_1_prop1_cor1 hR
  have hmem : ∀ j, ∃ c : Fin n → ℤ, ∑ i, c i • b i = a * b j := by
    intro j
    have h1 : a * b j ∈ R := R.mul_mem ha (hbR j)
    have h2 : a * b j ∈ (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
      rw [Submodule.span_int_eq_addSubgroupClosure, hcl]; exact h1
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp h2
  choose c hc using hmem
  let Mz : Matrix (Fin n) (Fin n) ℤ := fun i j => c j i
  have hM : LinearMap.toMatrix b b (LinearMap.mulLeft ℚ a) = Mz.map (Int.castRingHom ℚ) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have : a * b j = ∑ i, ((c j i : ℤ) : ℚ) • b i := by
      rw [← hc j]
      exact Finset.sum_congr rfl fun i _ => (Int.cast_smul_eq_zsmul ℚ _ _).symm
    simp only [LinearMap.mulLeft_apply]
    rw [this, b.repr_sum_self]
    rfl
  refine ⟨?_, ⟨Mz.trace, ?_⟩, ⟨Mz.det, ?_⟩⟩
  · -- integrality via the characteristic polynomial
    let f := LinearMap.mulLeft ℚ a
    have h0 := LinearMap.aeval_self_charpoly f
    have hcp : f.charpoly = Mz.charpoly.map (Int.castRingHom ℚ) := by
      rw [← LinearMap.charpoly_toMatrix f b, hM, Matrix.charpoly_map]
    have hlmul : ∀ q : Polynomial ℚ, Polynomial.aeval f q = Algebra.lmul ℚ A (Polynomial.aeval a q) := by
      intro q
      rw [← Polynomial.aeval_algHom_apply]
      rfl
    have h1 : Polynomial.aeval a (Mz.charpoly.map (Int.castRingHom ℚ)) = 0 := by
      rw [hcp, hlmul] at h0
      have := congrArg (fun g => g 1) h0
      simpa using this
    refine ⟨Mz.charpoly, Matrix.charpoly_monic Mz, ?_⟩
    have h2 := Polynomial.aeval_map_algebraMap ℚ a Mz.charpoly
    rw [show algebraMap ℤ ℚ = Int.castRingHom ℚ from rfl] at h2
    rw [h1] at h2
    exact h2.symm
  · rw [LinearMap.trace_eq_matrix_trace ℚ b, hM]
    simp [Matrix.trace]
  · rw [← LinearMap.det_toMatrix b, hM]
    exact (RingHom.map_det (Int.castRingHom ℚ) Mz).symm

end NumberFieldKB.WeilBNT
