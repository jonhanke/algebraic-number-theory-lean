import QuadFormsKB.Citation
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases
import NumberFieldKB.MilneEC.Ch2MazurRealizationC

/-!
# Milne, *Elliptic Curves*, Chapter II, Remark 5.11: the fifteen Mazur groups occur

Source: J. S. Milne, *Elliptic Curves*, second edition (2006), bib key `milne2006ec`, Remark 5.11 (pdf p. 76),
the realization half of Mazur's theorem.

For each of the fifteen groups of `MazurTorsion` (`Ch2Torsion.lean`) there is an explicit curve
$Y^2 = X^3 + aX + b$ ($a, b \in \mathbb Z$) over $\mathbb Q$ and a theorem computing its torsion subgroup.
The lower bound is a point of exact order $N$ (resp. of order $2m$ together with a second $2$-torsion point),
checked on rational coordinates by `decide +kernel` through the model `nsmulC` of the group law (part A);
the upper bound is $|E(\mathbb Q)_{\mathrm{tors}}| \mid \#\bar E(\mathbb F_p)$ for a prime $p$ of good reduction
(`card_torsion_dvd`, part B, from Corollary 5.7), where $\#\bar E(\mathbb F_p)$ is also computed by `decide +kernel`.
The model curves were found by a Tate-normal-form search (Kubert's families) and scaled to integral short
Weierstrass form; they are isomorphic over $\mathbb Q$ to the Cremona curves of the same torsion type, but only
the torsion statements below are proved.

Main result: `mazur_groups_realized`.
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve MazurReal

-- local, so as not to add global instances that other libraries (Tau Ceti) also declare
local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The curve $E : Y^2 = X^3 + (-1)X + (-1)$ over $\mathbb Q$ with $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/1$:
the point at infinity is the only rational point of finite order; the upper bound is by reduction at $p = 3$ (good reduction), where $\#\bar E(\mathbb F_{3}) = 1$. -/
noncomputable abbrev curveZ1 : WeierstrassCurve ℚ := curveQ (-1) (-1)

lemma isElliptic_curveZ1 : curveZ1.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/1$ for `curveZ1` (reduction at $p = 3$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ1 : Nonempty (AddCommGroup.torsion curveZ1.toAffine.Point ≃+ ZMod 1) := by
  exact torsion_cyclic (a := (-1)) (b := (-1)) 1 none (trivial) (by norm_num) 3 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The curve $E : Y^2 = X^3 + (2)X + (0)$ over $\mathbb Q$ with $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/2$:
the point $P = (0, 0)$ has exact order $2$; the upper bound is by reduction at $p = 5$ (good reduction), where $\#\bar E(\mathbb F_{5}) = 2$. -/
noncomputable abbrev curveZ2 : WeierstrassCurve ℚ := curveQ 2 0

lemma isElliptic_curveZ2 : curveZ2.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/2$ for `curveZ2` (reduction at $p = 5$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ2 : Nonempty (AddCommGroup.torsion curveZ2.toAffine.Point ≃+ ZMod 2) := by
  exact torsion_cyclic (a := 2) (b := 0) 2 (some (0, 0)) (by norm_num [OnC]) (by norm_num) 5 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The curve $E : Y^2 = X^3 + (0)X + (4)$ over $\mathbb Q$ with $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/3$:
the point $P = (0, 2)$ has exact order $3$; the upper bound is by reduction at $p = 7$ (good reduction), where $\#\bar E(\mathbb F_{7}) = 3$. -/
noncomputable abbrev curveZ3 : WeierstrassCurve ℚ := curveQ 0 4

lemma isElliptic_curveZ3 : curveZ3.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/3$ for `curveZ3` (reduction at $p = 7$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ3 : Nonempty (AddCommGroup.torsion curveZ3.toAffine.Point ≃+ ZMod 3) := by
  exact torsion_cyclic (a := 0) (b := 4) 3 (some (0, 2)) (by norm_num [OnC]) (by norm_num) 7 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The curve $E : Y^2 = X^3 + (-2)X + (1)$ over $\mathbb Q$ with $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/4$:
the point $P = (0, -1)$ has exact order $4$; the upper bound is by reduction at $p = 3$ (good reduction), where $\#\bar E(\mathbb F_{3}) = 4$. -/
noncomputable abbrev curveZ4 : WeierstrassCurve ℚ := curveQ (-2) 1

lemma isElliptic_curveZ4 : curveZ4.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/4$ for `curveZ4` (reduction at $p = 3$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ4 : Nonempty (AddCommGroup.torsion curveZ4.toAffine.Point ≃+ ZMod 4) := by
  exact torsion_cyclic (a := (-2)) (b := 1) 4 (some (0, -1)) (by norm_num [OnC]) (by norm_num) 3 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The curve $E : Y^2 = X^3 + (-432)X + (8208)$ over $\mathbb Q$ with $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/5$:
the point $P = (24, 108)$ has exact order $5$; the upper bound is by reduction at $p = 5$ (good reduction), where $\#\bar E(\mathbb F_{5}) = 5$. -/
noncomputable abbrev curveZ5 : WeierstrassCurve ℚ := curveQ (-432) 8208

lemma isElliptic_curveZ5 : curveZ5.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/5$ for `curveZ5` (reduction at $p = 5$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ5 : Nonempty (AddCommGroup.torsion curveZ5.toAffine.Point ≃+ ZMod 5) := by
  exact torsion_cyclic (a := (-432)) (b := 8208) 5 (some (24, 108)) (by norm_num [OnC]) (by norm_num) 5 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The curve $E : Y^2 = X^3 + (0)X + (1)$ over $\mathbb Q$ with $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/6$:
the point $P = (2, 3)$ has exact order $6$; the upper bound is by reduction at $p = 5$ (good reduction), where $\#\bar E(\mathbb F_{5}) = 6$. -/
noncomputable abbrev curveZ6 : WeierstrassCurve ℚ := curveQ 0 1

lemma isElliptic_curveZ6 : curveZ6.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/6$ for `curveZ6` (reduction at $p = 5$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ6 : Nonempty (AddCommGroup.torsion curveZ6.toAffine.Point ≃+ ZMod 6) := by
  exact torsion_cyclic (a := 0) (b := 1) 6 (some (2, 3)) (by norm_num [OnC]) (by norm_num) 5 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The curve $E : Y^2 = X^3 + (-43)X + (166)$ over $\mathbb Q$ with $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/7$:
the point $P = (3, 8)$ has exact order $7$; the upper bound is by reduction at $p = 3$ (good reduction), where $\#\bar E(\mathbb F_{3}) = 7$. -/
noncomputable abbrev curveZ7 : WeierstrassCurve ℚ := curveQ (-43) 166

lemma isElliptic_curveZ7 : curveZ7.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/7$ for `curveZ7` (reduction at $p = 3$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ7 : Nonempty (AddCommGroup.torsion curveZ7.toAffine.Point ≃+ ZMod 7) := by
  exact torsion_cyclic (a := (-43)) (b := 166) 7 (some (3, 8)) (by norm_num [OnC]) (by norm_num) 3 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The curve $E : Y^2 = X^3 + (1269)X + (127386)$ over $\mathbb Q$ with $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/8$:
the point $P = (-15, -324)$ has exact order $8$; the upper bound is by reduction at $p = 5$ (good reduction), where $\#\bar E(\mathbb F_{5}) = 8$. -/
noncomputable abbrev curveZ8 : WeierstrassCurve ℚ := curveQ 1269 127386

lemma isElliptic_curveZ8 : curveZ8.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/8$ for `curveZ8` (reduction at $p = 5$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ8 : Nonempty (AddCommGroup.torsion curveZ8.toAffine.Point ≃+ ZMod 8) := by
  exact torsion_cyclic (a := 1269) (b := 127386) 8 (some (-15, -324)) (by norm_num [OnC]) (by norm_num) 5 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The curve $E : Y^2 = X^3 + (-219)X + (1654)$ over $\mathbb Q$ with $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/9$:
the point $P = (11, 24)$ has exact order $9$; the upper bound is by reduction at $p = 5$ (good reduction), where $\#\bar E(\mathbb F_{5}) = 9$. -/
noncomputable abbrev curveZ9 : WeierstrassCurve ℚ := curveQ (-219) 1654

lemma isElliptic_curveZ9 : curveZ9.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/9$ for `curveZ9` (reduction at $p = 5$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ9 : Nonempty (AddCommGroup.torsion curveZ9.toAffine.Point ≃+ ZMod 9) := by
  exact torsion_cyclic (a := (-219)) (b := 1654) 9 (some (11, 24)) (by norm_num [OnC]) (by norm_num) 5 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The curve $E : Y^2 = X^3 + (-58347)X + (3954150)$ over $\mathbb Q$ with $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/10$:
the point $P = (3, -1944)$ has exact order $10$; the upper bound is by reduction at $p = 5$ (good reduction), where $\#\bar E(\mathbb F_{5}) = 10$. -/
noncomputable abbrev curveZ10 : WeierstrassCurve ℚ := curveQ (-58347) 3954150

lemma isElliptic_curveZ10 : curveZ10.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/10$ for `curveZ10` (reduction at $p = 5$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ10 : Nonempty (AddCommGroup.torsion curveZ10.toAffine.Point ≃+ ZMod 10) := by
  exact torsion_cyclic (a := (-58347)) (b := 3954150) 10 (some (3, -1944)) (by norm_num [OnC]) (by norm_num) 5 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The curve $E : Y^2 = X^3 + (-1947)X + (108214)$ over $\mathbb Q$ with $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/12$:
the point $P = (-37, 360)$ has exact order $12$; the upper bound is by reduction at $p = 7$ (good reduction), where $\#\bar E(\mathbb F_{7}) = 12$. -/
noncomputable abbrev curveZ12 : WeierstrassCurve ℚ := curveQ (-1947) 108214

lemma isElliptic_curveZ12 : curveZ12.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/12$ for `curveZ12` (reduction at $p = 7$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ12 : Nonempty (AddCommGroup.torsion curveZ12.toAffine.Point ≃+ ZMod 12) := by
  exact torsion_cyclic (a := (-1947)) (b := 108214) 12 (some (-37, 360)) (by norm_num [OnC]) (by norm_num) 7 (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The curve $E : Y^2 = X^3 + (-1)X + (0)$ over $\mathbb Q$ with
$E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/2 \times \mathbb Z/2$: the point $P = (1, 0)$ has exact
order $2$, the cubic has the three rational roots $0, 1, -1$ (so full $2$-torsion), and
$Q = (0, 0) \notin \langle P\rangle$; the upper bound is by reduction at $p = 3$ (good reduction), where
$\#\bar E(\mathbb F_{3}) = 4$. -/
noncomputable abbrev curveZ2Z2 : WeierstrassCurve ℚ := curveQ (-1) 0

lemma isElliptic_curveZ2Z2 : curveZ2Z2.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/2 \times \mathbb Z/2$ for `curveZ2Z2` (reduction at $p = 3$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ2Z2 :
    Nonempty (AddCommGroup.torsion curveZ2Z2.toAffine.Point ≃+ ZMod 2 × ZMod (2 * 1)) := by
  have : NeZero 1 := ⟨by norm_num⟩
  exact torsion_prod (a := (-1)) (b := 0) 1 (some (1, 0)) (some (0, 0))
    (by norm_num [OnC]) (by norm_num [OnC]) (by norm_num) 3 (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The curve $E : Y^2 = X^3 + (-351)X + (1890)$ over $\mathbb Q$ with
$E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/2 \times \mathbb Z/4$: the point $P = (33, 162)$ has exact
order $4$, the cubic has the three rational roots $6, 15, -21$ (so full $2$-torsion), and
$Q = (6, 0) \notin \langle P\rangle$; the upper bound is by reduction at $p = 5$ (good reduction), where
$\#\bar E(\mathbb F_{5}) = 8$. -/
noncomputable abbrev curveZ2Z4 : WeierstrassCurve ℚ := curveQ (-351) 1890

lemma isElliptic_curveZ2Z4 : curveZ2Z4.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/2 \times \mathbb Z/4$ for `curveZ2Z4` (reduction at $p = 5$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ2Z4 :
    Nonempty (AddCommGroup.torsion curveZ2Z4.toAffine.Point ≃+ ZMod 2 × ZMod (2 * 2)) := by
  have : NeZero 2 := ⟨by norm_num⟩
  exact torsion_prod (a := (-351)) (b := 1890) 2 (some (33, 162)) (some (6, 0))
    (by norm_num [OnC]) (by norm_num [OnC]) (by norm_num) 5 (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The curve $E : Y^2 = X^3 + (-24003)X + (1296702)$ over $\mathbb Q$ with
$E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/2 \times \mathbb Z/6$: the point $P = (39, -648)$ has exact
order $6$, the cubic has the three rational roots $66, 111, -177$ (so full $2$-torsion), and
$Q = (66, 0) \notin \langle P\rangle$; the upper bound is by reduction at $p = 7$ (good reduction), where
$\#\bar E(\mathbb F_{7}) = 12$. -/
noncomputable abbrev curveZ2Z6 : WeierstrassCurve ℚ := curveQ (-24003) 1296702

lemma isElliptic_curveZ2Z6 : curveZ2Z6.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/2 \times \mathbb Z/6$ for `curveZ2Z6` (reduction at $p = 7$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ2Z6 :
    Nonempty (AddCommGroup.torsion curveZ2Z6.toAffine.Point ≃+ ZMod 2 × ZMod (2 * 3)) := by
  have : NeZero 3 := ⟨by norm_num⟩
  exact torsion_prod (a := (-24003)) (b := 1296702) 3 (some (39, -648)) (some (66, 0))
    (by norm_num [OnC]) (by norm_num [OnC]) (by norm_num) 7 (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The curve $E : Y^2 = X^3 + (-1386747)X + (368636886)$ over $\mathbb Q$ with
$E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/2 \times \mathbb Z/8$: the point $P = (147, -12960)$ has exact
order $8$, the cubic has the three rational roots $282, 1011, -1293$ (so full $2$-torsion), and
$Q = (282, 0) \notin \langle P\rangle$; the upper bound is by reduction at $p = 11$ (good reduction), where
$\#\bar E(\mathbb F_{11}) = 16$. -/
noncomputable abbrev curveZ2Z8 : WeierstrassCurve ℚ := curveQ (-1386747) 368636886

lemma isElliptic_curveZ2Z8 : curveZ2Z8.IsElliptic := isElliptic_curveQ (by norm_num)

/-- $E(\mathbb Q)_{\mathrm{tors}} \simeq \mathbb Z/2 \times \mathbb Z/8$ for `curveZ2Z8` (reduction at $p = 11$). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem torsion_curveZ2Z8 :
    Nonempty (AddCommGroup.torsion curveZ2Z8.toAffine.Point ≃+ ZMod 2 × ZMod (2 * 4)) := by
  have : NeZero 4 := ⟨by norm_num⟩
  exact torsion_prod (a := (-1386747)) (b := 368636886) 4 (some (147, -12960)) (some (282, 0))
    (by norm_num [OnC]) (by norm_num [OnC]) (by norm_num) 11 (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- **Remark 5.11, the realization half** (pdf p. 76): every group in Mazur's list, $\mathbb Z/m$
($1 \le m \le 10$ or $m = 12$) and $\mathbb Z/2 \times \mathbb Z/2m$ ($1 \le m \le 4$), is
$E(\mathbb Q)_{\mathrm{tors}}$ for an elliptic curve $E$ over $\mathbb Q$ (the curves `curveZ1`, ..., `curveZ12`,
`curveZ2Z2`, ..., `curveZ2Z8`). -/
@[kb "milne2006ec" "Ch. II, Remark 5.11 (the fifteen groups occur), pdf p. 76"]
theorem mazur_groups_realized :
    (∀ m : ℕ, (1 ≤ m ∧ m ≤ 10 ∨ m = 12) → ∃ W : WeierstrassCurve ℚ, W.IsElliptic ∧
        Nonempty (AddCommGroup.torsion W.toAffine.Point ≃+ ZMod m)) ∧
      ∀ m : ℕ, 1 ≤ m ∧ m ≤ 4 → ∃ W : WeierstrassCurve ℚ, W.IsElliptic ∧
        Nonempty (AddCommGroup.torsion W.toAffine.Point ≃+ ZMod 2 × ZMod (2 * m)) := by
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · rcases hm with ⟨h1, h2⟩ | rfl
    · interval_cases m
      · exact ⟨_, isElliptic_curveZ1, torsion_curveZ1⟩
      · exact ⟨_, isElliptic_curveZ2, torsion_curveZ2⟩
      · exact ⟨_, isElliptic_curveZ3, torsion_curveZ3⟩
      · exact ⟨_, isElliptic_curveZ4, torsion_curveZ4⟩
      · exact ⟨_, isElliptic_curveZ5, torsion_curveZ5⟩
      · exact ⟨_, isElliptic_curveZ6, torsion_curveZ6⟩
      · exact ⟨_, isElliptic_curveZ7, torsion_curveZ7⟩
      · exact ⟨_, isElliptic_curveZ8, torsion_curveZ8⟩
      · exact ⟨_, isElliptic_curveZ9, torsion_curveZ9⟩
      · exact ⟨_, isElliptic_curveZ10, torsion_curveZ10⟩
    · exact ⟨_, isElliptic_curveZ12, torsion_curveZ12⟩
  · obtain ⟨h1, h2⟩ := hm
    interval_cases m
    · exact ⟨_, isElliptic_curveZ2Z2, torsion_curveZ2Z2⟩
    · exact ⟨_, isElliptic_curveZ2Z4, torsion_curveZ2Z4⟩
    · exact ⟨_, isElliptic_curveZ2Z6, torsion_curveZ2Z6⟩
    · exact ⟨_, isElliptic_curveZ2Z8, torsion_curveZ2Z8⟩

end NumberFieldKB.MilneEC.II
