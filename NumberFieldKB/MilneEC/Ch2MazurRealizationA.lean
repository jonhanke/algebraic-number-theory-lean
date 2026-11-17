import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Torsion
import Mathlib.Data.ZMod.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch2Short

/-!
# Milne, *Elliptic Curves*, Chapter II, Remark 5.11: realization of the Mazur groups, part A

Source: J. S. Milne, *Elliptic Curves*, second edition (2006), bib key `milne2006ec`, Remark 5.11 (pdf p. 76).

Part A is the lower-bound machinery: a computable model `addC` of the chord-and-tangent law on the short
Weierstrass curve $Y^2 = X^3 + aX + b$ over $\mathbb Q$ (points are `Option (ℚ × ℚ)`, `none` being the point at
infinity), a proof that it agrees with Mathlib's group law on `(shortCurve a b).toAffine.Point`
(`toPt_addC`), and group-theoretic lemmas turning "a point of exact order $N$ and $|T| \mid N$" into
$T \simeq \mathbb Z/N$, and "points $P$, $Q$ of orders $2m$, $2$ with $Q \notin \langle P\rangle$ and
$|T| \mid 4m$" into $T \simeq \mathbb Z/2 \times \mathbb Z/2m$.
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve

namespace MazurReal

section Model

variable (a b : ℚ)

/-- Coordinates $(x, y)$ (or `none` for $O$) lying on $Y^2 = X^3 + aX + b$. -/
def OnC : Option (ℚ × ℚ) → Prop
  | none => True
  | some (x, y) => y ^ 2 = x ^ 3 + a * x + b

/-- The computable chord-and-tangent law on coordinates. -/
def addC : Option (ℚ × ℚ) → Option (ℚ × ℚ) → Option (ℚ × ℚ)
  | none, Q => Q
  | some P, none => some P
  | some (x1, y1), some (x2, y2) =>
    if x1 = x2 then
      if y1 + y2 = 0 then none
      else some (((3 * x1 ^ 2 + a) / (2 * y1)) ^ 2 - x1 - x2,
        -(((3 * x1 ^ 2 + a) / (2 * y1)) * ((((3 * x1 ^ 2 + a) / (2 * y1)) ^ 2 - x1 - x2) - x1) + y1))
    else some ((((y2 - y1) / (x2 - x1)) ^ 2 - x1 - x2),
        -(((y2 - y1) / (x2 - x1)) * ((((y2 - y1) / (x2 - x1)) ^ 2 - x1 - x2) - x1) + y1))

/-- Iterated addition $n \cdot P$ on coordinates. -/
def nsmulC : ℕ → Option (ℚ × ℚ) → Option (ℚ × ℚ)
  | 0, _ => none
  | n + 1, P => addC a (nsmulC n P) P

variable [(shortCurve a b).IsElliptic]

/-- The point of Mathlib's group attached to coordinates (`0` if they are not on the curve). -/
noncomputable def toPt : Option (ℚ × ℚ) → (shortCurve a b).toAffine.Point
  | none => 0
  | some (x, y) =>
    if h : y ^ 2 = x ^ 3 + a * x + b then
      Affine.Point.some x y
        ((Affine.equation_iff_nonsingular (W := (shortCurve a b).toAffine)).1
          (by rw [Affine.equation_iff]; simp [shortCurve]; linear_combination h))
    else 0

lemma nsOf {x y : ℚ} (h : y ^ 2 = x ^ 3 + a * x + b) : (shortCurve a b).toAffine.Nonsingular x y :=
  (Affine.equation_iff_nonsingular (W := (shortCurve a b).toAffine)).1
    (by rw [Affine.equation_iff]; simp [shortCurve]; linear_combination h)

lemma toPt_some {x y : ℚ} (h : y ^ 2 = x ^ 3 + a * x + b) {hns} :
    toPt a b (some (x, y)) = Affine.Point.some x y hns := by
  simp [toPt, h]

omit [(shortCurve a b).IsElliptic] in
lemma onC_of_equation {x y : ℚ} (h : (shortCurve a b).toAffine.Equation x y) : y ^ 2 = x ^ 3 + a * x + b := by
  rw [Affine.equation_iff] at h
  simp [shortCurve] at h
  linear_combination h

lemma some_congr {W : WeierstrassCurve ℚ} {x y x' y' : ℚ} {h : W.toAffine.Nonsingular x y}
    {h' : W.toAffine.Nonsingular x' y'} (hx : x = x') (hy : y = y') :
    Affine.Point.some x y h = Affine.Point.some x' y' h' := by
  subst hx; subst hy; rfl

theorem toPt_addC {P Q : Option (ℚ × ℚ)} (hP : OnC a b P) (hQ : OnC a b Q) :
    OnC a b (addC a P Q) ∧ toPt a b (addC a P Q) = toPt a b P + toPt a b Q := by
  rcases P with _ | ⟨x1, y1⟩
  · simp [addC, toPt]; exact hQ
  rcases Q with _ | ⟨x2, y2⟩
  · simp [addC, toPt]; exact hP
  have hP' : y1 ^ 2 = x1 ^ 3 + a * x1 + b := hP
  have hQ' : y2 ^ 2 = x2 ^ 3 + a * x2 + b := hQ
  have hn1 := (Affine.equation_iff_nonsingular (W := (shortCurve a b).toAffine)).1
    (show (shortCurve a b).toAffine.Equation x1 y1 by rw [Affine.equation_iff]; simp [shortCurve]; linear_combination hP')
  have hn2 := (Affine.equation_iff_nonsingular (W := (shortCurve a b).toAffine)).1
    (show (shortCurve a b).toAffine.Equation x2 y2 by rw [Affine.equation_iff]; simp [shortCurve]; linear_combination hQ')
  rw [toPt_some a b hP' (hns := hn1), toPt_some a b hQ' (hns := hn2)]
  by_cases hx : x1 = x2
  · subst hx
    by_cases hy : y1 + y2 = 0
    · have hy' : y1 = (shortCurve a b).toAffine.negY x1 y2 := by
        simp [Affine.negY, shortCurve]; linear_combination hy
      simp only [addC, hy, ite_true]
      rw [Affine.Point.add_of_Y_eq rfl hy']
      exact ⟨trivial, rfl⟩
    · have hy' : y1 ≠ (shortCurve a b).toAffine.negY x1 y2 := by
        simp [Affine.negY, shortCurve]; intro h; apply hy; linear_combination h
      have h2 : (2 : ℚ) * y1 ≠ 0 := by
        have : y1 ≠ 0 := by
          intro h0; apply hy
          have : y2 ^ 2 = 0 := by rw [hQ', ← hP', h0]; ring
          have : y2 = 0 := by simpa using this
          rw [h0, this]; ring
        exact mul_ne_zero two_ne_zero this
      have hsl : (shortCurve a b).toAffine.slope x1 x1 y1 y2 = (3 * x1 ^ 2 + a) / (2 * y1) := by
        rw [Affine.slope_of_Y_ne (by exact rfl) hy']
        simp [shortCurve]
        congr 1; ring
      have hadd := Affine.Point.add_of_Y_ne (h₁ := hn1) (h₂ := hn2) hy'
      have hE := (Affine.nonsingular_add hn1 hn2 (fun hxy => hy' hxy.right)).1
      rw [hadd]
      simp only [addC, ite_true, hy, ite_false]
      have hx3 : (shortCurve a b).toAffine.addX x1 x1 ((shortCurve a b).toAffine.slope x1 x1 y1 y2) =
          ((3 * x1 ^ 2 + a) / (2 * y1)) ^ 2 - x1 - x1 := by
        rw [hsl]; simp [Affine.addX, shortCurve]
      have hy3 : (shortCurve a b).toAffine.addY x1 x1 y1 ((shortCurve a b).toAffine.slope x1 x1 y1 y2) =
          -((3 * x1 ^ 2 + a) / (2 * y1) * (((3 * x1 ^ 2 + a) / (2 * y1)) ^ 2 - x1 - x1 - x1) + y1) := by
        rw [hsl]; simp [Affine.addY, Affine.negAddY, Affine.addX, shortCurve]
      have hO : OnC a b (some (((3 * x1 ^ 2 + a) / (2 * y1)) ^ 2 - x1 - x1,
          -((3 * x1 ^ 2 + a) / (2 * y1) * (((3 * x1 ^ 2 + a) / (2 * y1)) ^ 2 - x1 - x1 - x1) + y1))) := by
        rw [hx3, hy3] at hE
        exact onC_of_equation a b hE
      refine ⟨hO, ?_⟩
      rw [toPt_some a b hO (hns := nsOf a b hO)]
      exact some_congr hx3.symm hy3.symm
  · have hsl : (shortCurve a b).toAffine.slope x1 x2 y1 y2 = (y2 - y1) / (x2 - x1) := by
      rw [Affine.slope_of_X_ne hx]
      have : x1 - x2 ≠ 0 := sub_ne_zero.2 hx
      have : x2 - x1 ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
      field_simp
      ring
    have hadd := Affine.Point.add_of_X_ne (h₁ := hn1) (h₂ := hn2) hx
    have hE := (Affine.nonsingular_add hn1 hn2 (fun hxy => hx hxy.left)).1
    simp only [addC, hx, ite_false]
    have hx3 : (shortCurve a b).toAffine.addX x1 x2 ((shortCurve a b).toAffine.slope x1 x2 y1 y2) =
        ((y2 - y1) / (x2 - x1)) ^ 2 - x1 - x2 := by
      rw [hsl]; simp [Affine.addX, shortCurve]
    have hy3 : (shortCurve a b).toAffine.addY x1 x2 y1 ((shortCurve a b).toAffine.slope x1 x2 y1 y2) =
        -((y2 - y1) / (x2 - x1) * (((y2 - y1) / (x2 - x1)) ^ 2 - x1 - x2 - x1) + y1) := by
      rw [hsl]; simp [Affine.addY, Affine.negAddY, Affine.addX, shortCurve]
    have hO : OnC a b (some (((y2 - y1) / (x2 - x1)) ^ 2 - x1 - x2,
        -((y2 - y1) / (x2 - x1) * (((y2 - y1) / (x2 - x1)) ^ 2 - x1 - x2 - x1) + y1))) := by
      rw [hx3, hy3] at hE
      exact onC_of_equation a b hE
    refine ⟨hO, ?_⟩
    rw [toPt_some a b hO (hns := nsOf a b hO), hadd]
    exact some_congr hx3.symm hy3.symm

theorem toPt_nsmulC {P : Option (ℚ × ℚ)} (hP : OnC a b P) (n : ℕ) :
    OnC a b (nsmulC a n P) ∧ toPt a b (nsmulC a n P) = n • toPt a b P := by
  induction n with
  | zero => simp [nsmulC, OnC, toPt]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := toPt_addC a b ih.1 hP
    refine ⟨h1, ?_⟩
    rw [nsmulC, h2, ih.2, succ_nsmul]

end Model

section Groups

/-- A finite abelian group of order dividing `N` containing an element of order `N` is `ZMod N`. -/
theorem cyclic_of_order {G : Type*} [AddCommGroup G] {N : ℕ} [NeZero N] (P : G)
    (hP : addOrderOf P = N) (hc : Nat.card G ∣ N) : Nonempty (G ≃+ ZMod N) := by
  have hfin : Finite G := Nat.finite_of_card_ne_zero (fun h => NeZero.ne N (by rw [h] at hc; exact zero_dvd_iff.1 hc))
  have hN : Nat.card G = N := Nat.dvd_antisymm hc (hP ▸ addOrderOf_dvd_natCard P)
  have : Fintype G := Fintype.ofFinite G
  have hcyc : IsAddCyclic G := isAddCyclic_of_addOrderOf_eq_card P (by rw [hN]; exact hP)
  have e := zmodAddCyclicAddEquiv hcyc
  rw [hN] at e
  exact ⟨e.symm⟩

/-- A finite abelian group of order dividing `4 m` with `P` of order `2 m`, `Q` of order `2`, `Q ∉ ⟨P⟩`,
is `ℤ/2 × ℤ/2m`. -/
theorem prod_of_orders {G : Type*} [AddCommGroup G] {m : ℕ} [NeZero m] (P Q : G)
    (hP : addOrderOf P = 2 * m) (hQ2 : 2 • Q = 0) (hQ0 : Q ≠ 0) (hQP : Q ≠ m • P)
    (hc : Nat.card G ∣ 4 * m) : Nonempty (G ≃+ ZMod 2 × ZMod (2 * m)) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hfin : Finite G := Nat.finite_of_card_ne_zero (fun h => by
    rw [h] at hc; have := zero_dvd_iff.1 hc; omega)
  have : NeZero (2 * m) := ⟨by omega⟩
  have h2P : (2 * m) • P = 0 := by rw [← hP]; exact addOrderOf_nsmul_eq_zero P
  let f : ZMod 2 →+ G := ZMod.lift 2 ⟨zmultiplesHom G Q, by rw [zmultiplesHom_apply, natCast_zsmul]; exact hQ2⟩
  let g : ZMod (2 * m) →+ G := ZMod.lift (2 * m) ⟨zmultiplesHom G P, by rw [zmultiplesHom_apply, natCast_zsmul]; exact h2P⟩
  have hf : ∀ x : ZMod 2, f x = x.val • Q := fun x => by
    conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Int.cast_natCast]
    simp only [f, ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul]
  have hg : ∀ x : ZMod (2 * m), g x = x.val • P := fun x => by
    conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Int.cast_natCast]
    simp only [g, ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul]
  let φ : ZMod 2 × ZMod (2 * m) →+ G := f.coprod g
  have hφ : ∀ x y, φ (x, y) = x.val • Q + y.val • P := fun x y => by
    simp [φ, hf, hg]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ h
    rw [hφ] at h
    have hy : y.val < 2 * m := ZMod.val_lt y
    have hx : x.val < 2 := ZMod.val_lt x
    have hord : ∀ k : ℕ, k • P = 0 → 2 * m ∣ k := fun k hk => hP ▸ addOrderOf_dvd_of_nsmul_eq_zero hk
    have hy0 : y.val • P = 0 → y = 0 := fun h0 => by
      have := hord _ h0
      have : y.val = 0 := Nat.eq_zero_of_dvd_of_lt this hy
      exact (ZMod.val_eq_zero y).1 this
    have : x.val = 0 ∨ x.val = 1 := by omega
    rcases this with h0 | h1
    · rw [h0, zero_smul, zero_add] at h
      refine Prod.ext ?_ (hy0 h)
      exact (ZMod.val_eq_zero x).1 h0
    · exfalso
      rw [h1, one_smul] at h
      have hQe : Q = -(y.val • P) := eq_neg_of_add_eq_zero_left h
      have h2 : (2 * y.val) • P = 0 := by
        have : 2 • Q = 0 := hQ2
        rw [hQe, smul_neg, ← mul_smul] at this
        simpa using this
      have hd := hord _ h2
      obtain ⟨c, hc'⟩ := hd
      have : c = 0 ∨ c = 1 := by
        rcases c with _ | _ | c
        · left; rfl
        · right; rfl
        · exfalso; nlinarith
      rcases this with rfl | rfl
      · have : y.val = 0 := by omega
        rw [this, zero_smul, neg_zero] at hQe
        exact hQ0 hQe
      · have : y.val = m := by omega
        rw [this] at hQe
        apply hQP
        rw [hQe]
        have : m • P + m • P = 0 := by rw [← add_nsmul, ← two_mul]; exact h2P
        exact (neg_eq_of_add_eq_zero_left this)
  have hcard : Nat.card (ZMod 2 × ZMod (2 * m)) = 4 * m := by
    rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod]; ring
  have hle : 4 * m ≤ Nat.card G := by
    rw [← hcard]; exact Nat.card_le_card_of_injective _ hinj
  have hGe : Nat.card G = 4 * m := Nat.dvd_antisymm hc (by
    exact (Nat.le_of_dvd (by omega) hc).antisymm' hle ▸ dvd_rfl)
  have hbij : Function.Bijective φ :=
    hinj.bijective_of_nat_card_le (by rw [hcard, hGe])
  exact ⟨(AddEquiv.ofBijective φ hbij).symm⟩

end Groups


end MazurReal

end NumberFieldKB.MilneEC.II
