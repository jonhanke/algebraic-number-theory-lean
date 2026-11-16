import NumberFieldKB.MilneEC.Ch1CubicLocal
import NumberFieldKB.MilneEC.Ch1NinePointLine
import NumberFieldKB.MilneEC.Ch1Bezout

/-!
# The nine-point lemma with multiplicities, affine form

Part of the proof of associativity of the chord and tangent law (Milne, *Elliptic Curves*, Theorem I.3.1;
Fulton 1969, §5.6, Proposition 1 and its use on p. 124). Let `f`, `g`, `h` be affine cubics whose leading
forms are nonzero, with those of `f`, `g` and of `f`, `h` relatively prime, and let `f` be nonsingular at
the common zeros of `f` and `g`. If $I_p(f, g) \le I_p(f, h)$ for every $p \ne u$ and
$I_u(f, g) \le I_u(f, h) + 1$, then $I_u(f, g) \le I_u(f, h)$.

The proof is the line argument of `Ch1NinePointLine`: for the line `l` through `u` chosen there,
$I_p(f, g) \le I_p(f, lh)$ at every common zero, so $lh \in (f, g)$ (local criterion `mem_span_of_numAt_le`
and the product decomposition), hence $h = cf + dg$ with constants, $d \ne 0$, and
$I_u(f, h) = I_u(f, g)$.
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

theorem isUnit_algebraMap_of_evalAt_ne_zero {q : MvPolynomial (Fin 2) K} {p : K × K}
    (hq : evalAt q p ≠ 0) : IsUnit (algebraMap _ (LocalRingAt p) q) :=
  IsLocalization.map_units (LocalRingAt p) (⟨q, fun h => hq (by
    simpa [pointIdeal, evalAt] using h)⟩ : (pointIdeal p).primeCompl)

theorem span_eq_top_of_not_mem {f g : MvPolynomial (Fin 2) K} {p : K × K}
    (hp : p ∉ commonZeros f g) :
    Ideal.span {algebraMap _ (LocalRingAt p) f, algebraMap _ (LocalRingAt p) g} = ⊤ := by
  simp only [commonZeros, Set.mem_ofPred_eq, not_and_or] at hp
  rcases hp with hf | hg
  · exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp))
      (isUnit_algebraMap_of_evalAt_ne_zero hf)
  · exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp))
      (isUnit_algebraMap_of_evalAt_ne_zero hg)

theorem finite_localQuotient_of_not_mem {f g : MvPolynomial (Fin 2) K} {p : K × K}
    (hp : p ∉ commonZeros f g) : Module.Finite K (LocalQuotientAt f g p) := by
  have : Subsingleton (LocalQuotientAt f g p) := by
    rw [LocalQuotientAt, span_eq_top_of_not_mem hp]
    exact Ideal.Quotient.subsingleton_iff.mpr rfl
  infer_instance

theorem numAt_eq_zero_of_not_mem {f g : MvPolynomial (Fin 2) K} {p : K × K}
    (hp : p ∉ commonZeros f g) : numAt f g p = 0 := by
  have : Subsingleton (LocalQuotientAt f g p) := by
    rw [LocalQuotientAt, span_eq_top_of_not_mem hp]
    exact Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

theorem finite_localQuotient' [IsAlgClosed K] {f g : MvPolynomial (Fin 2) K}
    (hfin : Module.Finite K (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g})) (p : K × K) :
    Module.Finite K (LocalQuotientAt f g p) := by
  by_cases hp : p ∈ commonZeros f g
  · exact finite_localQuotient hfin hp
  · exact finite_localQuotient_of_not_mem hp

/-- Replacing `h` by `c f + d g` with `d ≠ 0` does not change the local intersection number with `f`. -/
theorem numAt_add_mul {f g : MvPolynomial (Fin 2) K} (c : K) {d : K} (hd : d ≠ 0) (p : K × K) :
    numAt f (C c * f + C d * g) p = numAt f g p := by
  unfold numAt LocalQuotientAt
  apply finrank_quotient_congr
  set a := algebraMap (MvPolynomial (Fin 2) K) (LocalRingAt p) f
  set b := algebraMap (MvPolynomial (Fin 2) K) (LocalRingAt p) g
  have hC : ∀ e : K, algebraMap (MvPolynomial (Fin 2) K) (LocalRingAt p) (C e) =
      algebraMap K (LocalRingAt p) e := fun e => by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  have e : algebraMap (MvPolynomial (Fin 2) K) (LocalRingAt p) (C c * f + C d * g) =
      algebraMap K _ c * a + algebraMap K _ d * b := by
    rw [map_add, map_mul, map_mul, hC, hC]
  rw [e]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact Ideal.subset_span (by simp)
    · exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  · rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact Ideal.subset_span (by simp)
    · have hinv : algebraMap K (LocalRingAt p) d⁻¹ * algebraMap K (LocalRingAt p) d = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hd, map_one]
      rw [SetLike.mem_coe, Ideal.mem_span_pair]
      refine ⟨-(algebraMap K _ d⁻¹ * algebraMap K _ c), algebraMap K _ d⁻¹, ?_⟩
      linear_combination b * hinv

theorem numAt_le_of_le_succ [IsAlgClosed K] {f g h : MvPolynomial (Fin 2) K}
    (hf : f.totalDegree ≤ 3) (hg : g.totalDegree ≤ 3) (hh : h.totalDegree ≤ 3)
    (hf3 : homogeneousComponent 3 f ≠ 0) (hg3 : homogeneousComponent 3 g ≠ 0)
    (hh3 : homogeneousComponent 3 h ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent 3 f) (homogeneousComponent 3 g))
    (hcop' : IsRelPrime (homogeneousComponent 3 f) (homogeneousComponent 3 h))
    (hns : ∀ p ∈ commonZeros f g, NonsingAt f p) (u : K × K)
    (hle : ∀ p, p ≠ u → numAt f g p ≤ numAt f h p) (hu : numAt f g u ≤ numAt f h u + 1) :
    numAt f g u ≤ numAt f h u := by
  classical
  by_cases hu0 : u ∈ commonZeros f g
  swap
  · rw [numAt_eq_zero_of_not_mem hu0]; exact Nat.zero_le _
  obtain ⟨hQfin, -⟩ := finrank_quotient_of_isRelPrime_top hf hg hf3 hg3 hcop
  obtain ⟨hQfin', -⟩ := finrank_quotient_of_isRelPrime_top hf hh hf3 hh3 hcop'
  obtain ⟨S1, hS1, -⟩ := finrank_quotient_eq_sum_numAt f g hQfin
  have hfin : (commonZeros f g).Finite := by rw [← hS1]; exact S1.finite_toSet
  have hnsu := hns u hu0
  obtain ⟨s, hs1, hs2, hs3⟩ := exists_good_s hf3 hfin u hnsu.2
  set l := lineForm u.1 u.2 s
  -- the line meets `f` with multiplicity 1 at `u`
  have hlu : Module.Finite K (LocalQuotientAt f l u) ∧ numAt f l u = 1 := by
    refine numAt_line hnsu (lineForm_totalDegree _ _ _) (by rw [evalAt_lineForm]; ring) ?_
    have e0 : evalAt (pderiv 0 l) u = s := by simp [l, lineForm, evalAt]
    have e1 : evalAt (pderiv 1 l) u = -1 := by simp [l, lineForm, evalAt]
    rw [e0, e1]
    intro h0; apply hs2; linear_combination -h0
  -- `l * h` lies in `(f, g)` locally at every common zero
  have hloc : ∀ p ∈ commonZeros f g, Ideal.Quotient.mk _ (algebraMap _ (LocalRingAt p) (l * h)) =
      (0 : LocalQuotientAt f g p) := by
    intro p hp
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hfl : Module.Finite K (LocalQuotientAt f l p) := by
      by_cases hpu : p = u
      · subst hpu; exact hlu.1
      · refine finite_localQuotient_of_not_mem fun h' => ?_
        have := hs3 p hp hpu
        apply this
        have h2 := h'.2
        rw [evalAt_lineForm] at h2
        linear_combination h2
    obtain ⟨-, hmul⟩ := numAt_mul (hns p hp) hfl (finite_localQuotient' hQfin' p)
    refine mem_span_of_numAt_le (hns p hp) (finite_localQuotient hQfin hp) ?_
    rw [hmul]
    by_cases hpu : p = u
    · subst hpu; rw [hlu.2]; omega
    · have := hle p hpu; omega
  have hmem : l * h ∈ Ideal.span {f, g} := mem_span_of_forall_localQuotient f g _ hQfin hloc
  obtain ⟨c, d, hcd⟩ := exists_eq_of_lineForm_mul_mem hf hg hh hf3 hg3 hcop hu0 hs1 hs2 hs3 hmem
  have hd : d ≠ 0 := by
    rintro rfl
    rw [C_0, zero_mul, add_zero] at hcd
    have h3 : homogeneousComponent 3 h = C c * homogeneousComponent 3 f := by
      rw [hcd, homogeneousComponent_C_mul]
    have hu3 : IsUnit (homogeneousComponent 3 f) := hcop' dvd_rfl (h3 ▸ dvd_mul_left _ _)
    exact not_isUnit_of_isHomogeneous (homogeneousComponent_isHomogeneous 3 f) (by norm_num) hf3 hu3
  rw [hcd, numAt_add_mul c hd]

end NumberFieldKB.MilneEC.Bezout
