import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch2MazurRealizationA
import NumberFieldKB.MilneEC.Ch2MazurRealizationB

/-!
# Milne, *Elliptic Curves*, Chapter II, Remark 5.11: realization of the Mazur groups, part C

Source: J. S. Milne, *Elliptic Curves*, second edition (2006), bib key `milne2006ec`, Remark 5.11 (pdf p. 76).

Part C combines the lower-bound model (part A) and the reduction bound (part B) into two drivers
(`torsion_cyclic`, `torsion_prod`) whose hypotheses are decidable closed computations on integers, rationals
and $\mathbb F_p$.
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve

namespace MazurReal

lemma isElliptic_curveQ {a b : ℤ} (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) : (curveQ a b).IsElliptic := by
  rw [curveQ, isElliptic_shortCurve_iff]
  exact_mod_cast hΔ

variable {a b : ℤ}

lemma toPt_ne_zero [(shortCurve (a : ℚ) b).IsElliptic] {Q : Option (ℚ × ℚ)} (hQ : OnC (a : ℚ) b Q)
    (h : Q ≠ none) : toPt (a : ℚ) b Q ≠ 0 := by
  rcases Q with _ | ⟨x, y⟩
  · exact absurd rfl h
  · rw [toPt_some (a : ℚ) b hQ (hns := nsOf _ _ hQ)]
    exact Affine.Point.some_ne_zero _

lemma toPt_injective [(shortCurve (a : ℚ) b).IsElliptic] {Q R : Option (ℚ × ℚ)} (hQ : OnC (a : ℚ) b Q)
    (hR : OnC (a : ℚ) b R) (h : toPt (a : ℚ) b Q = toPt (a : ℚ) b R) : Q = R := by
  rcases Q with _ | ⟨x, y⟩ <;> rcases R with _ | ⟨x', y'⟩
  · rfl
  · rw [toPt_some (a : ℚ) b hR (hns := nsOf _ _ hR)] at h
    exact absurd h.symm (Affine.Point.some_ne_zero _)
  · rw [toPt_some (a : ℚ) b hQ (hns := nsOf _ _ hQ)] at h
    exact absurd h (Affine.Point.some_ne_zero _)
  · rw [toPt_some (a : ℚ) b hQ (hns := nsOf _ _ hQ), toPt_some (a : ℚ) b hR (hns := nsOf _ _ hR)] at h
    simp only [Affine.Point.some.injEq] at h
    rw [h.1, h.2]

lemma toPt_isOfFinAddOrder [(shortCurve (a : ℚ) b).IsElliptic] {Q : Option (ℚ × ℚ)}
    (hQ : OnC (a : ℚ) b Q) (n : ℕ) (hn : 0 < n) (h : nsmulC (a : ℚ) n Q = none) :
    IsOfFinAddOrder (toPt (a : ℚ) b Q) := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  refine ⟨n, hn, ?_⟩
  rw [← (toPt_nsmulC (a : ℚ) b hQ n).2, h]
  rfl

lemma addOrderOf_toPt [(shortCurve (a : ℚ) b).IsElliptic] {Q : Option (ℚ × ℚ)} (hQ : OnC (a : ℚ) b Q)
    (N : ℕ) (hN : 0 < N) (h0 : nsmulC (a : ℚ) N Q = none)
    (h1 : ∀ k < N, 0 < k → nsmulC (a : ℚ) k Q ≠ none) : addOrderOf (toPt (a : ℚ) b Q) = N := by
  rw [addOrderOf_eq_iff hN]
  refine ⟨?_, fun k hk hk0 hz => ?_⟩
  · rw [← (toPt_nsmulC (a : ℚ) b hQ N).2, h0]; rfl
  · rw [← (toPt_nsmulC (a : ℚ) b hQ k).2] at hz
    exact toPt_ne_zero (toPt_nsmulC (a : ℚ) b hQ k).1 (h1 k hk hk0) hz

/-- Driver for cyclic groups: a point of exact order `N` (decided on coordinates) and a good prime `p` with
$1 + \#\{(x, y) \in \mathbb F_p^2 : y^2 = x^3 + ax + b\} = N$ give $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/N$. -/
theorem torsion_cyclic (N : ℕ) [NeZero N] (P : Option (ℚ × ℚ)) (hP : OnC (a : ℚ) b P)
    (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hgood : ¬(p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2)
    (hcount : 1 + (Finset.univ.filter
      (fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 + (a : ZMod p) * xy.1 + (b : ZMod p))).card = N)
    (h0 : nsmulC (a : ℚ) N P = none) (h1 : ∀ k < N, 0 < k → nsmulC (a : ℚ) k P ≠ none) :
    Nonempty (AddCommGroup.torsion (curveQ a b).toAffine.Point ≃+ ZMod N) := by
  have := isElliptic_curveQ hΔ
  have hord := addOrderOf_toPt hP N (NeZero.pos N) h0 h1
  have hmem : toPt (a : ℚ) b P ∈ AddCommGroup.torsion (curveQ a b).toAffine.Point :=
    (AddCommGroup.mem_torsion _).2 (toPt_isOfFinAddOrder hP N (NeZero.pos N) h0)
  have hdvd := card_torsion_dvd p hΔ hp2 hgood
  rw [card_FpPts, hcount] at hdvd
  exact cyclic_of_order (⟨_, hmem⟩ : AddCommGroup.torsion (curveQ a b).toAffine.Point)
    (by rw [AddSubgroup.addOrderOf_mk]; exact hord) hdvd

/-- Driver for $\mathbb Z/2 \times \mathbb Z/2m$: `P` of exact order `2m`, `Q` of order `2` not in
$\langle P\rangle$ (decided on coordinates), and a good prime with $1 + \#\{\ldots\} = 4m$. -/
theorem torsion_prod (m : ℕ) [NeZero m] (P Q : Option (ℚ × ℚ)) (hP : OnC (a : ℚ) b P)
    (hQ : OnC (a : ℚ) b Q)
    (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hgood : ¬(p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2)
    (hcount : 1 + (Finset.univ.filter
      (fun xy : ZMod p × ZMod p => xy.2 ^ 2 = xy.1 ^ 3 + (a : ZMod p) * xy.1 + (b : ZMod p))).card = 4 * m)
    (h0 : nsmulC (a : ℚ) (2 * m) P = none) (h1 : ∀ k < 2 * m, 0 < k → nsmulC (a : ℚ) k P ≠ none)
    (hQ2 : nsmulC (a : ℚ) 2 Q = none) (hQ0 : Q ≠ none) (hQP : Q ≠ nsmulC (a : ℚ) m P) :
    Nonempty (AddCommGroup.torsion (curveQ a b).toAffine.Point ≃+ ZMod 2 × ZMod (2 * m)) := by
  have := isElliptic_curveQ hΔ
  have hm : 0 < m := NeZero.pos m
  have hord := addOrderOf_toPt hP (2 * m) (by omega) h0 h1
  have hmemP : toPt (a : ℚ) b P ∈ AddCommGroup.torsion (curveQ a b).toAffine.Point :=
    (AddCommGroup.mem_torsion _).2 (toPt_isOfFinAddOrder hP (2 * m) (by omega) h0)
  have hmemQ : toPt (a : ℚ) b Q ∈ AddCommGroup.torsion (curveQ a b).toAffine.Point :=
    (AddCommGroup.mem_torsion _).2 (toPt_isOfFinAddOrder hQ 2 (by omega) hQ2)
  have hdvd := card_torsion_dvd p hΔ hp2 hgood
  rw [card_FpPts, hcount] at hdvd
  refine prod_of_orders (⟨_, hmemP⟩ : AddCommGroup.torsion (curveQ a b).toAffine.Point) ⟨_, hmemQ⟩
    (by rw [AddSubgroup.addOrderOf_mk]; exact hord) ?_ ?_ ?_ hdvd
  · apply Subtype.ext
    show 2 • toPt (a : ℚ) b Q = 0
    rw [← (toPt_nsmulC (a : ℚ) b hQ 2).2, hQ2]; rfl
  · intro h
    exact toPt_ne_zero hQ hQ0 (congrArg Subtype.val h)
  · intro h
    apply hQP
    refine toPt_injective hQ (toPt_nsmulC (a : ℚ) b hP m).1 ?_
    rw [(toPt_nsmulC (a : ℚ) b hP m).2]
    exact congrArg Subtype.val h

end MazurReal

end NumberFieldKB.MilneEC.II
