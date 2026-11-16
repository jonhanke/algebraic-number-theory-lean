import NumberFieldKB.MilneEC.Ch1Affine
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiNFMain
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Connected.Separation
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Milne, Elliptic Curves: the Introduction and Chapter I, Section 2 (rational points on plane curves)

Milne, *Elliptic Curves* (`milne2006ec`): congruent numbers (Introduction, pdf p. 10); Chapter I, §2
(pdf pp. 25–33): Remark 2.2, the height of a rational point (Remark 2.3), the $p$-adic numbers
(Theorem 2.5, Remark 2.6), Legendre's theorem (Theorem 2.8) and the Hasse–Minkowski theorem
(Remark 2.9), Hensel's lemma (Lemma 2.10, Remark 2.11, Theorem 2.12, Examples 2.13–2.15),
Exercise 2.17.  Mordell's theorem (Theorem 2.1) needs the chord and tangent construction and is in
`Ch1GroupLaw`.

Conventions.  Polynomials in `n` variables over `ℤ` are `MvPolynomial (Fin n) ℤ` (0-based indices: Milne's
$X_1, \dots, X_n$ are `X 0`, …, `X (n-1)`).  Congruences modulo $p^k$ between integers are divisibility
`(p : ℤ) ^ k ∣ a - b`; between $p$-adic integers they are written `∃ c, b - a = p ^ k * c` in
`ℤ_[p]`.
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC

/-! ### Congruent numbers (Introduction) -/

/-- A natural number `n` is **congruent** (p. 10) if it is the area of a right triangle whose sides have
rational length: $x^2 + y^2 = z^2$ and $n = \tfrac12 xy$ with $x, y, z > 0$ rational. -/
@[kb "milne2006ec" "Introduction, Def. of congruent number, pdf p. 10"]
def IsCongruentNumber (n : ℕ) : Prop :=
  ∃ x y z : ℚ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧ (n : ℚ) = x * y / 2

/-- For `n > 0`, `n` is congruent if and only if the equations $x^2 + y^2 = z^2$, $n = \tfrac12 xy$
have a simultaneous solution in $\mathbb Q$ (p. 10). -/
@[kb "milne2006ec" "Introduction, congruent numbers, pdf p. 10"]
theorem isCongruentNumber_iff {n : ℕ} (hn : 0 < n) :
    IsCongruentNumber n ↔ ∃ x y z : ℚ, x ^ 2 + y ^ 2 = z ^ 2 ∧ (n : ℚ) = x * y / 2 := by
  refine ⟨fun ⟨x, y, z, _, _, _, h1, h2⟩ => ⟨x, y, z, h1, h2⟩, fun ⟨x, y, z, h1, h2⟩ => ?_⟩
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hxy : 0 < x * y := by linarith
  have hx : x ≠ 0 := fun h => by simp [h] at hxy
  have hy : y ≠ 0 := fun h => by simp [h] at hxy
  have hz : z ≠ 0 := fun h => by
    simp [h] at h1
    exact hx (by nlinarith [sq_nonneg x, sq_nonneg y])
  refine ⟨|x|, |y|, |z|, abs_pos.2 hx, abs_pos.2 hy, abs_pos.2 hz, ?_, ?_⟩
  · simpa [sq_abs] using h1
  · rw [← abs_mul, abs_of_pos hxy]; exact h2

/-- Fibonacci: 5 is congruent (the triangle with sides $3/2, 20/3, 41/6$) (p. 10). -/
@[kb "milne2006ec" "Introduction, 5 is congruent, pdf p. 10"]
theorem isCongruentNumber_five : IsCongruentNumber 5 :=
  ⟨3/2, 20/3, 41/6, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Fibonacci: 6 is congruent (the triangle with sides $3, 4, 5$) (p. 10). -/
@[kb "milne2006ec" "Introduction, 6 is congruent, pdf p. 10"]
theorem isCongruentNumber_six : IsCongruentNumber 6 :=
  ⟨3, 4, 5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Euler: 7 is congruent (the triangle with sides $24/5, 35/12, 337/60$) (p. 10). -/
@[kb "milne2006ec" "Introduction, 7 is congruent, pdf p. 10"]
theorem isCongruentNumber_seven : IsCongruentNumber 7 :=
  ⟨24/5, 35/12, 337/60, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ### Remark 2.2 and heights -/

/-- **Remark 2.2** (p. 28), the group-theoretic part (with footnote 4): neither $(\mathbb Q, +)$ nor
$(\mathbb Q^\times, \cdot)$ is finitely generated.  (That the nonsingular points of a singular cubic form
such a group is Chapter II, §3.) -/
@[kb "milne2006ec" "Ch. I, Rem. 2.2 and footnote 4, pdf p. 28"]
theorem remark_2_2 : ¬ AddGroup.FG ℚ ∧ ¬ Group.FG ℚˣ := by
  constructor
  · intro h
    obtain ⟨S, hS, hfin⟩ := (AddGroup.fg_iff).1 h
    obtain ⟨T, rfl⟩ := hfin.exists_finset_coe
    set D : ℕ := ∏ s ∈ T, s.den with hD
    have hDpos : 0 < D := Finset.prod_pos fun s _ => s.den_pos
    have hle : AddSubgroup.closure (T : Set ℚ) ≤ AddSubgroup.zmultiples (1 / (D : ℚ)) := by
      rw [AddSubgroup.closure_le]
      intro s hs
      have hdvd : s.den ∣ D := Finset.dvd_prod_of_mem _ hs
      obtain ⟨k, hk⟩ := hdvd
      refine ⟨s.num * k, ?_⟩
      have hden : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_nz
      have hk' : (D : ℚ) = s.den * k := by exact_mod_cast hk
      have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
      have hkq : (k : ℚ) ≠ 0 := by
        rintro h0; apply hDq; rw [hk', h0]; simp
      simp only [zsmul_eq_mul]
      push_cast
      have e : (s.num : ℚ) = s * s.den := (Rat.mul_den_eq_num s).symm
      rw [hk', e]
      field_simp
    rw [hS] at hle
    have hmem : (1 / ((D : ℚ) + 1)) ∈ AddSubgroup.zmultiples (1 / (D : ℚ)) := hle trivial
    obtain ⟨z, hz⟩ := hmem
    simp only [zsmul_eq_mul] at hz
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    have hz2 : (z : ℚ) * (D + 1) = D := by
      field_simp at hz
      linarith
    have hz3 : z * ((D : ℤ) + 1) = D := by exact_mod_cast hz2
    have hD1 : (1 : ℤ) ≤ D := by exact_mod_cast hDpos
    rcases lt_trichotomy z 0 with h0 | h0 | h0
    · nlinarith
    · subst h0; simp at hz3; omega
    · nlinarith
  · intro h
    obtain ⟨S, hS, hfin⟩ := (Group.fg_iff).1 h
    obtain ⟨T, rfl⟩ := hfin.exists_finset_coe
    set N : ℕ := ∑ s ∈ T, ((s : ℚ).num.natAbs + (s : ℚ).den) with hN
    obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 1)
    have : Fact p.Prime := ⟨hp⟩
    let f : ℚˣ →* Multiplicative ℤ :=
      { toFun := fun u => Multiplicative.ofAdd (padicValRat p (u : ℚ))
        map_one' := by simp
        map_mul' := by
          intro a b
          simp [padicValRat.mul a.ne_zero b.ne_zero] }
    have hle : Subgroup.closure (T : Set ℚˣ) ≤ f.ker := by
      rw [Subgroup.closure_le]
      intro s hs
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      have h1 : (s : ℚ).num.natAbs + (s : ℚ).den ≤ N :=
        Finset.single_le_sum (f := fun s : ℚˣ => (s : ℚ).num.natAbs + (s : ℚ).den)
          (fun _ _ => Nat.zero_le _) hs
      have h2 : ¬ p ∣ (s : ℚ).den := fun hd =>
        absurd (Nat.le_of_dvd (s : ℚ).den_pos hd) (by omega)
      have h3 : ¬ (p : ℤ) ∣ (s : ℚ).num := by
        intro hd
        have hne : (s : ℚ).num ≠ 0 := Rat.num_ne_zero.2 s.ne_zero
        have := Nat.le_of_dvd (Int.natAbs_pos.2 hne) (Int.natCast_dvd.1 hd)
        omega
      show Multiplicative.ofAdd (padicValRat p (s : ℚ)) = 1
      rw [padicValRat, padicValInt.eq_zero_of_not_dvd h3, padicValNat.eq_zero_of_not_dvd h2]
      rfl
    rw [hS] at hle
    have := hle (Set.mem_univ (Units.mk0 (p : ℚ) (by exact_mod_cast hp.ne_zero)))
    rw [MonoidHom.mem_ker] at this
    have h1 : padicValRat p (p : ℚ) = 1 := padicValRat.self hp.one_lt
    have h2 : Multiplicative.ofAdd (padicValRat p (p : ℚ)) = 1 := this
    rw [h1] at h2
    exact absurd (congrArg Multiplicative.toAdd h2) (by simp)

-- Height of a rational point (Remark 2.3, p. 28): Milne's $H(P)$ is Mathlib's multiplicative height
-- `Projectivization.mulHeight`; `height_eq_max_abs` gives Milne's formula.
attribute [kb "milne2006ec" "Ch. I, Rem. 2.3, Def. of the height H(P), pdf p. 28"]
  Projectivization.mulHeight

/-- **Height** (Remark 2.3, p. 28): for $P = (a : b : c) \in \mathbb P^2(\mathbb Q)$ with $a, b, c$
integers having no common factor, $H(P) = \max(|a|, |b|, |c|)$; and every point has such a
representative. -/
@[kb "milne2006ec" "Ch. I, Rem. 2.3, Def. of the height H(P), pdf p. 28"]
theorem height_eq_max_abs (P : Projectivization ℚ (Fin 3 → ℚ)) :
    ∃ (a : Fin 3 → ℤ) (ha : (fun i => (a i : ℚ)) ≠ 0), Finset.univ.gcd a = 1 ∧
      P = Projectivization.mk ℚ (fun i => (a i : ℚ)) ha ∧
      Projectivization.mulHeight P = max (max |a 0| |a 1|) |a 2| := by
  obtain ⟨v, hv, rfl⟩ : ∃ v, ∃ hv : v ≠ 0, P = Projectivization.mk ℚ v hv :=
    ⟨P.rep, P.rep_nonzero, P.mk_rep.symm⟩
  set D : ℕ := ∏ i, (v i).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun s _ => (v s).den_pos
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hint : ∀ i, ∃ z : ℤ, (z : ℚ) = v i * D := by
    intro i
    obtain ⟨k, hk⟩ : (v i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    refine ⟨(v i).num * k, ?_⟩
    have e : ((v i).num : ℚ) = v i * (v i).den := (Rat.mul_den_eq_num (v i)).symm
    rw [hk]; push_cast; rw [e]; ring
  choose w hw using hint
  have hw0 : w ≠ 0 := by
    intro h0
    apply hv
    funext i
    have := hw i
    rw [h0] at this
    have h2 : v i * D = 0 := by simpa using this.symm
    exact (mul_eq_zero.1 h2).resolve_right hDq
  have hg : Finset.univ.gcd w ≠ 0 := by
    intro h
    exact hw0 (funext fun i => Finset.gcd_eq_zero_iff.1 h i (Finset.mem_univ i))
  obtain ⟨a, hwa, hga⟩ := Finset.extract_gcd w (Finset.univ_nonempty (α := Fin 3))
  have hgq : ((Finset.univ.gcd w : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hg
  have hav : ∀ i, (a i : ℚ) = v i * D / (Finset.univ.gcd w : ℤ) := by
    intro i
    rw [← hw i, hwa i (Finset.mem_univ i)]
    push_cast
    field_simp
  have ha0 : (fun i => (a i : ℚ)) ≠ 0 := by
    intro h
    apply hv
    funext i
    have := congrFun h i
    rw [hav i] at this
    simpa [hDq, hgq] using this
  have peq : Projectivization.mk ℚ v hv = Projectivization.mk ℚ (fun i => (a i : ℚ)) ha0 := by
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨(Finset.univ.gcd w : ℤ) / D, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hav i]
    field_simp
  refine ⟨a, ha0, hga, peq, ?_⟩
  rw [peq, Projectivization.mulHeight_mk]
  have hga' := Rat.mulHeight_eq_max_abs_of_gcd_eq_one hga
  have e : (fun i => (a i : ℚ)) = ((↑) : ℤ → ℚ) ∘ a := rfl
  rw [e, hga']
  congr 1
  refine le_antisymm (ciSup_le fun i => ?_) (max_le (max_le ?_ ?_) ?_)
  · fin_cases i <;> simp
  · exact Finite.le_ciSup_of_le 0 le_rfl
  · exact Finite.le_ciSup_of_le 1 le_rfl
  · exact Finite.le_ciSup_of_le 2 le_rfl

/-! ### The p-adic numbers -/

-- Theorem 2.5 (p. 29): (a) `Padic.field`/`Padic.normedField` and `Padic.complete`; (b) the cast
-- `ℚ → ℚ_[p]` is an injective ring homomorphism (`Padic.coe_inj`) with dense range
-- (`Padic.denseRange_ratCast`).  The p-adic absolute value on ℚ (p. 29) is `padicNorm`.
attribute [kb "milne2006ec" "Ch. I, Thm. 2.5 (a), pdf p. 29"] Padic.complete
attribute [kb "milne2006ec" "Ch. I, Thm. 2.5 (b), pdf p. 30"] Padic.denseRange_ratCast
attribute [kb "milne2006ec" "Ch. I, §2, Def. of the p-adic absolute value, pdf p. 29"] padicNorm

/-- **Remark 2.6** (p. 30), descriptions of $\mathbb Z_p$: (a) it is the closure of $\mathbb Z$ in
$\mathbb Q_p$, (b) it is the set of $\alpha$ with $|\alpha|_p \leq 1$ (Mathlib's definition of `ℤ_[p]`). -/
@[kb "milne2006ec" "Ch. I, Rem. 2.6 (a)(b), pdf p. 30"]
theorem remark_2_6_closure (p : ℕ) [Fact p.Prime] :
    closure (Set.range (fun n : ℤ => (n : ℚ_[p]))) = {x : ℚ_[p] | ‖x‖ ≤ 1} ∧
      Set.range (fun x : ℤ_[p] => (x : ℚ_[p])) = {x : ℚ_[p] | ‖x‖ ≤ 1} := by
  have h2 : Set.range (fun x : ℤ_[p] => (x : ℚ_[p])) = {x : ℚ_[p] | ‖x‖ ≤ 1} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩; exact z.2
    · intro h; exact ⟨⟨x, h⟩, rfl⟩
  refine ⟨?_, h2⟩
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro _ ⟨n, rfl⟩; exact Padic.norm_int_le_one n
    · simpa [Metric.closedBall, dist_zero_right] using
        (Metric.isClosed_closedBall (x := (0 : ℚ_[p])) (ε := 1))
  · intro x hx
    rw [← h2] at hx
    obtain ⟨z, rfl⟩ := hx
    have hz : z ∈ closure (Set.range (Int.cast : ℤ → ℤ_[p])) := by
      rw [(PadicInt.denseRange_intCast (p := p)).closure_range]; trivial
    have hmaps : Set.MapsTo (fun x : ℤ_[p] => (x : ℚ_[p])) (Set.range (Int.cast : ℤ → ℤ_[p]))
        (Set.range (fun n : ℤ => (n : ℚ_[p]))) := by
      rintro y ⟨n, rfl⟩
      exact ⟨n, by simp⟩
    exact map_mem_closure (f := fun x : ℤ_[p] => (x : ℚ_[p])) continuous_subtype_val hz hmaps

/-- The partial sum $\sum_{i < n} a_i p^i$ of a digit sequence, as a natural number. -/
def digitSum (p : ℕ) (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, a i * p ^ i

/-- A partial sum of digits $< p$ is $< p^n$. -/
lemma digitSum_lt (p : ℕ) [Fact p.Prime] (a : ℕ → ℕ) (ha : ∀ i, a i < p) (n : ℕ) :
    digitSum p a n < p ^ n := by
  induction n with
  | zero => simp [digitSum]
  | succ n ih =>
    have h1 := ha n
    have h2 : digitSum p a (n + 1) = digitSum p a n + a n * p ^ n := by
      simp [digitSum, Finset.sum_range_succ]
    rw [h2, pow_succ]
    have : a n * p ^ n ≤ (p - 1) * p ^ n := Nat.mul_le_mul_right _ (by omega)
    have h3 : (p - 1) * p ^ n + p ^ n = p * p ^ n := by
      have : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
      zify [this]; ring
    nlinarith

/-- The ideal $p^n\mathbb Z_p$ is closed. -/
lemma isClosed_span_pow (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsClosed ((Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
  have : ((Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) : Set ℤ_[p]) =
      {x | ‖x‖ ≤ (p : ℝ) ^ (-n : ℤ)} := by
    ext x; exact (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm
  rw [this]
  exact isClosed_le continuous_norm continuous_const

/-- If a digit series sums to `x`, then `x` minus the first `n` terms lies in $p^n\mathbb Z_p$. -/
lemma digit_tail (p : ℕ) [Fact p.Prime] (a : ℕ → ℕ) (x : ℤ_[p])
    (hx : HasSum (fun i => (a i : ℤ_[p]) * (p : ℤ_[p]) ^ i) x) (n : ℕ) :
    x - (digitSum p a n : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
  have h1 := (hasSum_nat_add_iff' n).2 hx
  have h2 := h1.tendsto_sum_nat
  have e : (digitSum p a n : ℤ_[p]) = ∑ i ∈ Finset.range n, (a i : ℤ_[p]) * (p : ℤ_[p]) ^ i := by
    simp [digitSum]
  rw [e]
  refine (isClosed_span_pow p n).mem_of_tendsto h2 (Filter.Eventually.of_forall fun m => ?_)
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Ideal.mem_span_singleton]
  exact ⟨a (i + n) * p ^ i, by ring⟩

/-- The partial sums of a digit series for `x` are the approximations `x.appr n`. -/
lemma digitSum_eq_appr (p : ℕ) [Fact p.Prime] (a : ℕ → ℕ) (ha : ∀ i, a i < p) (x : ℤ_[p])
    (hx : HasSum (fun i => (a i : ℤ_[p]) * (p : ℤ_[p]) ^ i) x) (n : ℕ) :
    digitSum p a n = x.appr n := by
  have h := PadicInt.zmod_congr_of_sub_mem_span n x _ _ (digit_tail p a x hx n)
    (PadicInt.appr_spec n x)
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt (digitSum_lt p a ha n), Nat.mod_eq_of_lt (PadicInt.appr_lt x n)] at h

/-- **Remark 2.6** (p. 30), (c): every element of $\mathbb Z_p$ is uniquely a series
$a_0 + a_1p + a_2p^2 + \cdots$ with $0 \leq a_i \leq p - 1$. -/
@[kb "milne2006ec" "Ch. I, Rem. 2.6 (c), pdf p. 30"]
theorem remark_2_6_digits (p : ℕ) [Fact p.Prime] (x : ℤ_[p]) :
    ∃! a : ℕ → ℕ, (∀ i, a i < p) ∧ HasSum (fun i => (a i : ℤ_[p]) * (p : ℤ_[p]) ^ i) x := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hdiv : ∀ n, p ^ n ∣ x.appr (n + 1) - x.appr n := fun n =>
    PadicInt.dvd_appr_sub_appr x n (n + 1) (Nat.le_succ n)
  have hmono : ∀ n, x.appr n ≤ x.appr (n + 1) := fun n => PadicInt.appr_mono x (Nat.le_succ n)
  have hmul : ∀ n, (x.appr (n + 1) - x.appr n) / p ^ n * p ^ n = x.appr (n + 1) - x.appr n :=
    fun n => Nat.div_mul_cancel (hdiv n)
  have hlt : ∀ n, (x.appr (n + 1) - x.appr n) / p ^ n < p := by
    intro n
    by_contra hc
    rw [not_lt] at hc
    have h1 := Nat.mul_le_mul_right (p ^ n) hc
    have h2 := PadicInt.appr_lt x (n + 1)
    rw [hmul n, ← pow_succ'] at h1
    omega
  have hsum : ∀ n, digitSum p (fun n => (x.appr (n + 1) - x.appr n) / p ^ n) n = x.appr n := by
    intro n
    induction n with
    | zero => have := PadicInt.appr_lt x 0; simp [digitSum] at this ⊢; omega
    | succ n ih =>
      have h3 : digitSum p (fun n => (x.appr (n + 1) - x.appr n) / p ^ n) (n + 1) =
          digitSum p (fun n => (x.appr (n + 1) - x.appr n) / p ^ n) n +
            (x.appr (n + 1) - x.appr n) / p ^ n * p ^ n := by
        simp [digitSum, Finset.sum_range_succ]
      rw [h3, ih, hmul n]
      have := hmono n
      omega
  refine ⟨fun n => (x.appr (n + 1) - x.appr n) / p ^ n, ⟨hlt, ?_⟩, ?_⟩
  · set d : ℕ → ℕ := fun n => (x.appr (n + 1) - x.appr n) / p ^ n with hd
    have hsumm : Summable (fun i => (d i : ℤ_[p]) * (p : ℤ_[p]) ^ i) := by
      apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      rw [Nat.cofinite_eq_atTop]
      refine squeeze_zero_norm (a := fun i => ‖(p : ℤ_[p])‖ ^ i) (fun i => ?_) ?_
      · rw [norm_mul, ← norm_pow]
        exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)
      · exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (by
          rw [PadicInt.norm_p]
          exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))
    refine (hsumm.hasSum_iff_tendsto_nat).2 ?_
    have e : ∀ n, ∑ i ∈ Finset.range n, (d i : ℤ_[p]) * (p : ℤ_[p]) ^ i = (x.appr n : ℤ_[p]) := by
      intro n
      rw [← hsum n]; simp [digitSum]
    simp_rw [e]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (a := fun n => ‖(p : ℤ_[p])‖ ^ n) (fun n => ?_) ?_
    · have := (PadicInt.norm_le_pow_iff_mem_span_pow (x - (x.appr n : ℤ_[p])) n).2
        (PadicInt.appr_spec n x)
      rw [norm_norm, norm_sub_rev, ← norm_pow, PadicInt.norm_p_pow]
      exact this
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (by
          rw [PadicInt.norm_p]
          exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))
  · rintro b ⟨hb, hbx⟩
    funext n
    have h1 := digitSum_eq_appr p b hb x hbx n
    have h2 := digitSum_eq_appr p b hb x hbx (n + 1)
    have h3 : digitSum p b (n + 1) = digitSum p b n + b n * p ^ n := by
      simp [digitSum, Finset.sum_range_succ]
    rw [h3, h1] at h2
    have : x.appr (n + 1) - x.appr n = b n * p ^ n := by omega
    rw [this, Nat.mul_div_cancel _ (by positivity)]

/-- **Remark 2.6** (p. 30), the series for $\mathbb Q_p$: every $p$-adic number is a series
$a_{-n}p^{-n} + \cdots + a_0 + a_1p + \cdots$ with $0 \leq a_i \leq p - 1$. -/
@[kb "milne2006ec" "Ch. I, Rem. 2.6 (b), pdf p. 30"]
theorem remark_2_6_digits_padic (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    ∃ (n : ℕ) (a : ℕ → ℕ), (∀ i, a i < p) ∧
      HasSum (fun i => (a i : ℚ_[p]) * (p : ℚ_[p]) ^ ((i : ℤ) - n)) x := by
  have hpq : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(p : ℚ_[p]) ^ n * x‖ ≤ 1 := by
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    · have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hxn) (Padic.norm_p_lt_one (p := p))
      refine ⟨n, ?_⟩
      rw [norm_mul, norm_pow]
      calc ‖(p : ℚ_[p])‖ ^ n * ‖x‖ ≤ ‖x‖⁻¹ * ‖x‖ :=
            mul_le_mul_of_nonneg_right hn.le hxn.le
        _ = 1 := inv_mul_cancel₀ hxn.ne'
  obtain ⟨a, ⟨ha, hs⟩, -⟩ := remark_2_6_digits p (⟨(p : ℚ_[p]) ^ n * x, hn⟩ : ℤ_[p])
  refine ⟨n, a, ha, ?_⟩
  have h1 := (hs.map (PadicInt.Coe.ringHom (p := p)) continuous_subtype_val)
  have h2 := h1.mul_left ((p : ℚ_[p]) ^ n)⁻¹
  have hc : ∀ y : ℤ_[p], PadicInt.Coe.ringHom y = (y : ℚ_[p]) := fun _ => rfl
  convert h2 using 1
  · funext i
    simp only [Function.comp_apply, hc]
    rw [zpow_sub₀ hpq, zpow_natCast, zpow_natCast]
    push_cast
    ring
  · show x = ((p : ℚ_[p]) ^ n)⁻¹ * ((p : ℚ_[p]) ^ n * x)
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hpq), one_mul]

/-- **Remark 2.6** (p. 30), (d): $\mathbb Z_p = \varprojlim \mathbb Z/p^m\mathbb Z$: the map
$x \mapsto (x \bmod p^m)_m$ is a bijection from `ℤ_[p]` onto the compatible sequences. -/
@[kb "milne2006ec" "Ch. I, Rem. 2.6 (d), pdf p. 30"]
theorem remark_2_6_inverse_limit (p : ℕ) [Fact p.Prime] :
    Function.Injective (fun x : ℤ_[p] => fun m : ℕ => PadicInt.toZModPow m x) ∧
    ∀ a : (m : ℕ) → ZMod (p ^ m),
      (∀ m, ZMod.castHom (pow_dvd_pow p (Nat.le_succ m)) (ZMod (p ^ m)) (a (m + 1)) = a m) →
      ∃ x : ℤ_[p], ∀ m, PadicInt.toZModPow m x = a m := by
  refine ⟨fun x y h => PadicInt.ext_of_toZModPow.1 fun n => congrFun h n, fun a ha => ?_⟩
  have hi : ∀ i, (p : ℤ) ^ i ∣ ((a (i + 1)).val : ℤ) - (a i).val := by
    intro i
    have h1 := ha i
    have e1 : ((a (i + 1)).val : ZMod (p ^ i)) = ((a i).val : ZMod (p ^ i)) := by
      have : ((a (i + 1)).val : ZMod (p ^ i)) =
          ZMod.castHom (pow_dvd_pow p (Nat.le_succ i)) (ZMod (p ^ i))
            (((a (i + 1)).val : ZMod (p ^ (i+1)))) := by simp
      rw [this, ZMod.natCast_zmod_val, h1, ZMod.natCast_zmod_val]
    have e2 : (((a (i + 1)).val : ℤ) : ZMod (p ^ i)) = (((a i).val : ℤ) : ZMod (p ^ i)) := by
      simpa using e1
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 e2.symm
    simpa using this
  refine ⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
    (fun n => ((a n).val : ℤ)) p hi), fun m => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => ((a n).val : ℤ)) p hi m]
  simp

/-! ### Legendre and Hasse–Minkowski -/

open scoped Matrix in
/-- A quadratic form whose Hessian has determinant zero over a field `K` of characteristic zero has
a nontrivial zero in `K`: a nonzero vector `v` of the kernel of the Hessian satisfies
$2 Q(v) = v^{\mathsf T} H v = 0$. -/
lemma isotropicIn_of_hessian_det_eq_zero {R : Type*} [CommRing R] {n : ℕ} (K : Type*) [Field K]
    [CharZero K] [Algebra R K] (Q : QuadFormsKB.QuadForm R n)
    (h : (Q.hessian.map (algebraMap R K)).det = 0) : Q.IsotropicIn K := by
  obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  refine ⟨v, hv, ?_⟩
  have h1 := QuadFormsKB.QuadForm.polar_eq_hessian K Q v v
  rw [hmv, dotProduct_zero] at h1
  have h2 : v + v = (2 : K) • v := (two_smul K v).symm
  rw [h2] at h1
  simp only [QuadFormsKB.QuadForm.evalIn_eq_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul] at h1 ⊢
  have h3 : (2 : K) * (v ⬝ᵥ (Q.coeff.map (algebraMap R K) *ᵥ v)) = 0 := by linear_combination h1
  exact (mul_eq_zero.1 h3).resolve_left two_ne_zero

/-- A degenerate quadratic form over a field `F` is isotropic over every extension field of
characteristic zero. -/
lemma isotropicIn_of_not_nondegenerate {F : Type*} [Field F] {n : ℕ}
    (Q : QuadFormsKB.QuadForm F n) (hQ : ¬ Q.Nondegenerate) (K : Type*) [Field K] [CharZero K]
    [Algebra F K] : Q.IsotropicIn K := by
  apply isotropicIn_of_hessian_det_eq_zero
  have hdet : Q.hessian.det = 0 := not_not.1 hQ
  have := (RingHom.map_det (algebraMap F K) Q.hessian).symm
  rw [hdet, map_zero] at this
  exact this

/-- **Theorem 2.8 (Legendre)** (p. 30): a quadratic form in three variables with rational coefficients
has a nontrivial zero in $\mathbb Q$ if and only if it has one in $\mathbb R$ and in every $\mathbb Q_p$.
Milne's statement has no nondegeneracy hypothesis; QuadFormsKB's `QuadFormsKB.hasseMinkowski_three`
assumes it, and a degenerate form has a nontrivial rational zero (a vector of the radical). -/
@[kb "milne2006ec" "Ch. I, Thm. 2.8, pdf p. 30"]
theorem theorem_2_8 (Q : QuadFormsKB.RatQF 3) :
    Q.IsotropicIn ℚ ↔ QuadFormsKB.RatPlace.Everywhere fun K _ _ => Q.IsotropicIn K := by
  by_cases hQ : Q.Nondegenerate
  · exact QuadFormsKB.hasseMinkowski_three Q hQ
  · have iso : ∀ (K : Type) [Field K] [CharZero K], Q.IsotropicIn K := fun K _ _ =>
      isotropicIn_of_not_nondegenerate Q hQ K
    refine ⟨fun _ v => ?_, fun _ => iso ℚ⟩
    cases v with
    | infinite => exact iso ℝ
    | finite p =>
      have : Fact p.1.Prime := ⟨p.2⟩
      exact iso ℚ_[p.1]

/-- **Remark 2.9** (p. 31): Theorem 2.8 holds for quadratic forms in any number of variables over any
number field `F` (Hasse–Minkowski).  From QuadFormsKB's `QuadFormsKB.hasseMinkowski_nf`, without its
nondegeneracy hypothesis (a degenerate form in at least one variable has a nontrivial zero over `F`). -/
@[kb "milne2006ec" "Ch. I, Rem. 2.9, pdf p. 31"]
theorem remark_2_9 {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadFormsKB.QuadForm F n) :
    Q.IsotropicIn F ↔ QuadFormsKB.NFPlace.Everywhere (F := F) fun K _ _ => Q.IsotropicIn K := by
  by_cases hQ : Q.Nondegenerate
  · exact QuadFormsKB.hasseMinkowski_nf Q hQ
  · have iso : ∀ (K : Type) [Field K] [Algebra F K], Q.IsotropicIn K := fun K _ _ =>
      have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
      isotropicIn_of_not_nondegenerate Q hQ K
    refine ⟨fun _ v => ?_, fun _ => iso F⟩
    cases v with
    | infinite w => exact iso _
    | finite v => exact iso _

/-! ### Hensel's lemma -/

/-- Taylor expansion to first order: if `d` divides each `h i`, then $d^2$ divides
$f(a + h) - f(a) - \sum_i h_i (\partial f/\partial X_i)(a)$. -/
lemma taylor_dvd {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R] (f : MvPolynomial σ R)
    (a h : σ → R) (d : R) (hd : ∀ i, d ∣ h i) :
    d ^ 2 ∣ eval (a + h) f - eval a f - ∑ i, h i * eval a (pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    have := dvd_add hp hq
    convert this using 1
    simp only [map_add, Finset.sum_add_distrib, mul_add]
    ring
  | mul_X p k hp =>
    set S := ∑ i, h i * eval a (pderiv i p) with hS
    set P := eval a p with hP
    have e1 : ∑ i, h i * eval a (pderiv i (p * X k)) = S * a k + P * h k := by
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X,
        Pi.single_apply, hS, hP, Finset.sum_mul]
      have : ∀ x, h x * (eval a p * eval a (if k = x then 1 else 0) +
          a k * eval a (pderiv x p)) =
          (if k = x then h x * eval a p else 0) + (h x * eval a (pderiv x p)) * a k := by
        intro x
        split_ifs <;> simp <;> ring
      simp_rw [this]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
      simp
      ring
    have e2 : eval (a + h) (p * X k) - eval a (p * X k) - ∑ i, h i * eval a (pderiv i (p * X k)) =
        S * h k + (eval (a + h) p - P - S) * (a k + h k) := by
      rw [e1]
      simp only [map_mul, eval_X, Pi.add_apply]
      ring
    rw [e2]
    refine dvd_add ?_ (dvd_mul_of_dvd_left hp _)
    rw [hS, Finset.sum_mul]
    refine Finset.dvd_sum fun i _ => ?_
    rw [pow_two, mul_assoc, mul_comm (eval a (pderiv i p)), ← mul_assoc]
    exact dvd_mul_of_dvd_left (mul_dvd_mul (hd i) (hd k)) _

/-- The Newton step of Hensel's lemma (the content of Remark 2.11; Lemma 2.10 is the case `r = 1`). -/
lemma hensel_step {n : ℕ} (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin n) ℤ) (a : Fin n → ℤ)
    (m r : ℕ) (hr : 1 ≤ r) (hf : (p : ℤ) ^ (2 * m + r) ∣ eval a f)
    (hd : ∃ i, ¬ (p : ℤ) ^ (m + 1) ∣ eval a (pderiv i f)) :
    ∃ b : Fin n → ℤ, (∀ j, (p : ℤ) ^ (m + r) ∣ b j - a j) ∧
      (p : ℤ) ^ (2 * m + r + 1) ∣ eval b f := by
  obtain ⟨i0, hi0⟩ := hd
  obtain ⟨u, hu⟩ := hf
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hp : p.Prime := Fact.out
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  generalize hD : eval a (pderiv i0 f) = D at hi0
  have hD0 : D ≠ 0 := fun h => hi0 (by rw [h]; exact dvd_zero _)
  -- write D = p^s * D' with p ∤ D'
  obtain ⟨s, m', hm', hs⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hD0) p hp.ne_one
  obtain ⟨D', hD'⟩ : (p : ℤ) ^ s ∣ D := by
    rw [← Int.natCast_pow, Int.natCast_dvd, hs]
    exact dvd_mul_right _ _
  have hm'D : m' = D'.natAbs := by
    have : D.natAbs = p ^ s * D'.natAbs := by
      rw [hD', Int.natAbs_mul, Int.natAbs_pow]; simp
    have hps : 0 < p ^ s := pow_pos hp.pos s
    rw [hs] at this
    exact Nat.eq_of_mul_eq_mul_left hps this
  have hD'p : ¬ (p : ℤ) ∣ D' := by
    rw [Int.natCast_dvd, ← hm'D]; exact hm'
  have hsm : s ≤ m := by
    by_contra hlt
    rw [not_le] at hlt
    exact hi0 (hD' ▸ (pow_dvd_pow (p : ℤ) hlt).trans (dvd_mul_right _ _))
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hsm
  have hcop : IsCoprime ((p : ℤ) ^ (s + e + 1)) D' :=
    ((Irreducible.coprime_iff_not_dvd hpz.irreducible).2 hD'p).pow_left
  obtain ⟨y, x, hxy⟩ := hcop
  set t : ℤ := -x * (p : ℤ) ^ e * u with ht
  have hT := taylor_dvd f a (Pi.single i0 ((p : ℤ) ^ (s + e + (r' + 1)) * t))
    ((p : ℤ) ^ (s + e + (r' + 1)))
    (fun i => by
      by_cases h : i = i0
      · subst h; simp
      · simp [h])
  have hsum : ∑ i, (Pi.single i0 ((p : ℤ) ^ (s + e + (r' + 1)) * t) : Fin n → ℤ) i *
      eval a (pderiv i f) = (p : ℤ) ^ (s + e + (r' + 1)) * t * D := by
    rw [← hD]; simp [Pi.single_apply]
  rw [hsum] at hT
  obtain ⟨w, hw⟩ := hT
  refine ⟨a + Pi.single i0 ((p : ℤ) ^ (s + e + (r' + 1)) * t), fun j => ?_, ?_⟩
  · by_cases h : j = i0
    · subst h; simp
    · simp [h]
  · refine ⟨u * y * (p : ℤ) ^ (s + e) + w * (p : ℤ) ^ r', ?_⟩
    linear_combination hw + hu + ((p : ℤ) ^ (s + e + (r' + 1)) * t) * hD' -
      (p : ℤ) ^ (2 * (s + e) + (r' + 1)) * u * hxy

/-- Congruent arguments give congruent values of an integer polynomial. -/
lemma congr_eval {n : ℕ} (g : MvPolynomial (Fin n) ℤ) (N : ℤ) (a b : Fin n → ℤ)
    (h : ∀ j, N ∣ b j - a j) : N ∣ eval b g - eval a g := by
  have h1 := taylor_dvd g a (b - a) N (fun i => h i)
  have h2 : N ∣ ∑ i, (b - a) i * eval a (pderiv i g) :=
    Finset.dvd_sum fun i _ => dvd_mul_of_dvd_left (h i) _
  have h3 : N ∣ N ^ 2 := dvd_pow_self N two_ne_zero
  have h4 := dvd_add (h3.trans h1) h2
  simp only [add_sub_cancel] at h4
  convert h4 using 1
  ring

/-- A ring homomorphism commutes with evaluation of an integer polynomial. -/
lemma map_aeval_int {σ S T : Type*} [CommRing S] [CommRing T] (k : S →+* T) (z : σ → S)
    (f : MvPolynomial σ ℤ) : k (aeval z f) = aeval (k ∘ z) f := by
  rw [aeval_def, aeval_def, eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

/-- **Lemma 2.10** (p. 31): let $f \in \mathbb Z[X_1, \dots, X_n]$ and $a \in \mathbb Z^n$ with
$f(a) \equiv 0 \bmod p^{2m+1}$ and $(\partial f/\partial X_i)(a) \not\equiv 0 \bmod p^{m+1}$ for some `i`.
Then there is $b \in \mathbb Z^n$ with $b \equiv a \bmod p^{m+1}$ and $f(b) \equiv 0 \bmod p^{2m+2}$. -/
@[kb "milne2006ec" "Ch. I, Lem. 2.10, pdf p. 31"]
theorem lemma_2_10 {n : ℕ} (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin n) ℤ) (a : Fin n → ℤ)
    (m : ℕ) (hf : (p : ℤ) ^ (2 * m + 1) ∣ eval a f)
    (hd : ∃ i, ¬ (p : ℤ) ^ (m + 1) ∣ eval a (pderiv i f)) :
    ∃ b : Fin n → ℤ, (∀ j, (p : ℤ) ^ (m + 1) ∣ b j - a j) ∧ (p : ℤ) ^ (2 * m + 2) ∣ eval b f :=
  hensel_step p f a m 1 le_rfl hf hd

/-- **Remark 2.11** (p. 32): if in Lemma 2.10 $f(a) \equiv 0 \bmod p^{2m+r}$ for some $r \geq 1$, there is
$b \equiv a \bmod p^{m+r}$ with $f(b) \equiv 0 \bmod p^{2m+r+1}$. -/
@[kb "milne2006ec" "Ch. I, Rem. 2.11, pdf p. 32"]
theorem remark_2_11 {n : ℕ} (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin n) ℤ) (a : Fin n → ℤ)
    (m r : ℕ) (hr : 1 ≤ r) (hf : (p : ℤ) ^ (2 * m + r) ∣ eval a f)
    (hd : ∃ i, ¬ (p : ℤ) ^ (m + 1) ∣ eval a (pderiv i f)) :
    ∃ b : Fin n → ℤ, (∀ j, (p : ℤ) ^ (m + r) ∣ b j - a j) ∧
      (p : ℤ) ^ (2 * m + r + 1) ∣ eval b f :=
  hensel_step p f a m r hr hf hd

/-- **Theorem 2.12 (Hensel's lemma)** (p. 32): under the hypotheses of Lemma 2.10 there is
$b \in \mathbb Z_p^n$ with $f(b) = 0$ and $b \equiv a \bmod p^{m+1}$. -/
@[kb "milne2006ec" "Ch. I, Thm. 2.12, pdf p. 32"]
theorem theorem_2_12 {n : ℕ} (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin n) ℤ) (a : Fin n → ℤ)
    (m : ℕ) (hf : (p : ℤ) ^ (2 * m + 1) ∣ eval a f)
    (hd : ∃ i, ¬ (p : ℤ) ^ (m + 1) ∣ eval a (pderiv i f)) :
    ∃ b : Fin n → ℤ_[p], aeval b f = 0 ∧ ∀ j, ∃ c : ℤ_[p], b j - a j = (p : ℤ_[p]) ^ (m + 1) * c := by
  let P : ℕ → (Fin n → ℤ) → Prop := fun k c =>
    (∀ j, (p : ℤ) ^ (m + 1) ∣ c j - a j) ∧ (p : ℤ) ^ (2 * m + k + 1) ∣ eval c f
  have base : P 0 a := ⟨fun j => by simp, hf⟩
  obtain ⟨i0, hi0⟩ := hd
  have step : ∀ k (c : {c // P k c}), ∃ b : {c // P (k + 1) c},
      ∀ j, (p : ℤ) ^ (m + k + 1) ∣ b.1 j - c.1 j := by
    intro k ⟨c, hc1, hc2⟩
    have hdc : ¬ (p : ℤ) ^ (m + 1) ∣ eval c (pderiv i0 f) := by
      intro h
      apply hi0
      have h5 := congr_eval (pderiv i0 f) ((p : ℤ) ^ (m + 1)) a c hc1
      have := dvd_sub h h5
      simpa using this
    obtain ⟨b, hb1, hb2⟩ := remark_2_11 p f c m (k + 1) (by omega) hc2 ⟨i0, hdc⟩
    refine ⟨⟨b, fun j => ?_, hb2⟩, fun j => hb1 j⟩
    have h6 : (p : ℤ) ^ (m + 1) ∣ b j - c j := (pow_dvd_pow _ (by omega)).trans (hb1 j)
    have := dvd_add h6 (hc1 j)
    simpa using this
  choose g hg using step
  let s : (k : ℕ) → {c // P k c} := fun k => Nat.rec ⟨a, base⟩ (fun k c => g k c) k
  have hs : ∀ k j, (p : ℤ) ^ k ∣ (s (k + 1)).1 j - (s k).1 j := fun k j =>
    (pow_dvd_pow _ (by omega)).trans (hg k (s k) j)
  have hcau := fun j =>
    PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun k => (s k).1 j) p (hs · j)
  let z : Fin n → ℤ_[p] := fun j => PadicInt.ofIntSeq _ (hcau j)
  have hz : ∀ k j, PadicInt.toZModPow k (z j) = (((s k).1 j : ℤ) : ZMod (p ^ k)) := fun k j =>
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun k => (s k).1 j) p (hs · j) k
  refine ⟨z, ?_, fun j => ?_⟩
  · apply PadicInt.ext_of_toZModPow.1
    intro k
    rw [map_aeval_int, map_zero]
    have h1 : (PadicInt.toZModPow k : ℤ_[p] →+* ZMod (p ^ k)) ∘ z =
        fun j => (((s k).1 j : ℤ) : ZMod (p ^ k)) :=
      funext fun j => hz k j
    rw [h1]
    have h2 : aeval (fun j => (((s k).1 j : ℤ) : ZMod (p ^ k))) f =
        (((eval (s k).1 f : ℤ)) : ZMod (p ^ k)) := by
      have := map_aeval_int (Int.castRingHom (ZMod (p ^ k))) (s k).1 f
      have e : aeval (s k).1 f = eval (s k).1 f := by
        rw [aeval_def, eval, coe_eval₂Hom]
        congr 1
      rw [e] at this
      exact this.symm
    rw [h2, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := (s k).2.2
    push_cast
    exact (pow_dvd_pow _ (by omega)).trans this
  · have h1 : PadicInt.toZModPow (m + 1) (z j - (a j : ℤ_[p])) = 0 := by
      rw [map_sub, hz]
      have h7 : ∀ k, (p : ℤ) ^ (m + 1) ∣ (s k).1 j - a j := fun k => (s k).2.1 j
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (by exact h7 (m + 1))
      push_cast at this ⊢
      rw [sub_eq_zero]
      simpa [sub_eq_zero] using this
    have : z j - (a j : ℤ_[p]) ∈
        RingHom.ker (PadicInt.toZModPow (m + 1) : ℤ_[p] →+* ZMod (p ^ (m + 1))) := h1
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc⟩

/-- **Example 2.13** (p. 32): if $\bar a$ is a simple root of the reduction $\bar f \in \mathbb F_p[X]$ of
$f \in \mathbb Z[X]$, then $\bar a$ lifts to a root of `f` in $\mathbb Z_p$. -/
@[kb "milne2006ec" "Ch. I, Ex. 2.13, pdf p. 32"]
theorem example_2_13 (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ) (a : ℤ)
    (hroot : (f.map (Int.castRingHom (ZMod p))).eval (a : ZMod p) = 0)
    (hsimple : (Polynomial.derivative (f.map (Int.castRingHom (ZMod p)))).eval (a : ZMod p) ≠ 0) :
    ∃ z : ℤ_[p], Polynomial.aeval z f = 0 ∧ PadicInt.toZMod z = (a : ZMod p) := by
  have h1 : (p : ℤ) ∣ f.eval a := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← hroot]
    simp
  have h2 : ¬ (p : ℤ) ∣ (Polynomial.derivative f).eval a := by
    intro h
    apply hsimple
    rw [Polynomial.derivative_map]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
    rw [← this]
    simp
  set F : Polynomial ℤ_[p] := f.map (algebraMap ℤ ℤ_[p]) with hF
  have hFa : F.aeval (a : ℤ_[p]) = ((f.eval a : ℤ) : ℤ_[p]) := by
    rw [hF, Polynomial.aeval_map_algebraMap]
    simpa using Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℤ_[p]) a f
  have hFa' : F.derivative.aeval (a : ℤ_[p]) =
      (((Polynomial.derivative f).eval a : ℤ) : ℤ_[p]) := by
    rw [hF, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap]
    simpa using
      Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℤ_[p]) a (Polynomial.derivative f)
  have hn1 : ‖F.aeval (a : ℤ_[p])‖ < 1 := by
    rw [hFa]; exact (PadicInt.norm_int_lt_one_iff_dvd _).2 h1
  have hn2 : ‖F.derivative.aeval (a : ℤ_[p])‖ = 1 := by
    rw [hFa']
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => h2 ?_)
    exact (PadicInt.norm_int_lt_one_iff_dvd _).1 h
  have hnorm : ‖F.aeval (a : ℤ_[p])‖ < ‖F.derivative.aeval (a : ℤ_[p])‖ ^ 2 := by
    rw [hn2]; simpa using hn1
  obtain ⟨z, hz0, hza, -, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_, ?_⟩
  · have : Polynomial.aeval z f = F.aeval z := by
      rw [hF, Polynomial.aeval_map_algebraMap]
    rw [this]; exact hz0
  · rw [hn2] at hza
    have : z - (a : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
        ← PadicInt.norm_lt_one_iff_dvd]
      exact hza
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    rw [this]; simp

/-- Reduction modulo `p` commutes with evaluating an integer polynomial at an integer point. -/
lemma cast_eval_eq {σ : Type*} (p : ℕ) [Fact p.Prime] (g : MvPolynomial σ ℤ) (a : σ → ℤ) :
    ((eval a g : ℤ) : ZMod p) =
      eval (fun i => (a i : ZMod p)) (map (Int.castRingHom (ZMod p)) g) := by
  have h1 := map_aeval_int (Int.castRingHom (ZMod p)) a g
  have e : aeval a g = eval a g := by
    rw [aeval_def, eval, coe_eval₂Hom]
    congr 1
  rw [e] at h1
  have e2 : eval (fun i => (a i : ZMod p)) (map (Int.castRingHom (ZMod p)) g) =
      aeval (fun i => (a i : ZMod p)) g := by
    rw [eval_map, aeval_def]
    rfl
  rw [e2]
  exact h1

/-- **Example 2.14** (p. 33): let $f \in \mathbb Z[X, Y, Z]$ be homogeneous and $(a, b, c) \in \mathbb Z^3$ such
that $(\bar a, \bar b, \bar c)$ is a nonsingular point of $\bar f = 0$ over $\mathbb F_p$ (a nonzero vector
where $\bar f$ vanishes and some partial derivative does not).  Then it lifts to a point of $f = 0$ with
coordinates in $\mathbb Z_p$. -/
@[kb "milne2006ec" "Ch. I, Ex. 2.14, pdf p. 33"]
theorem example_2_14 (p : ℕ) [Fact p.Prime] {d : ℕ} (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (a : Fin 3 → ℤ) (ha : (fun i => (a i : ZMod p)) ≠ 0)
    (hzero : eval (fun i => (a i : ZMod p)) (map (Int.castRingHom (ZMod p)) f) = 0)
    (hns : ∃ i, eval (fun i => (a i : ZMod p)) (map (Int.castRingHom (ZMod p)) (pderiv i f)) ≠ 0) :
    ∃ w : Fin 3 → ℤ_[p], w ≠ 0 ∧ aeval w f = 0 ∧
      ∀ j, PadicInt.toZMod (w j) = (a j : ZMod p) := by
  have h1 : (p : ℤ) ^ (2 * 0 + 1) ∣ eval a f := by
    rw [mul_zero, zero_add, pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd, cast_eval_eq]
    exact hzero
  obtain ⟨i, hi⟩ := hns
  have h2 : ∃ i, ¬ (p : ℤ) ^ (0 + 1) ∣ eval a (pderiv i f) := by
    refine ⟨i, fun h => hi ?_⟩
    rw [zero_add, pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd, cast_eval_eq] at h
    exact h
  obtain ⟨b, hb0, hb⟩ := theorem_2_12 p f a 0 h1 h2
  have hbj : ∀ j, PadicInt.toZMod (b j) = (a j : ZMod p) := by
    intro j
    obtain ⟨c, hc⟩ := hb j
    have : b j = (a j : ℤ_[p]) + (p : ℤ_[p]) ^ (0 + 1) * c := by rw [← hc]; ring
    rw [this, map_add, map_mul]
    simp
  refine ⟨b, ?_, hb0, hbj⟩
  intro h0
  apply ha
  funext j
  have := hbj j
  rw [h0] at this
  simpa using this.symm

/-- The discriminant of a ternary quadratic form with integer coefficients, taken here as the
determinant of the matrix of second partial derivatives $(\partial^2 f/\partial X_i \partial X_j)$ (Milne
does not fix the normalization; this one makes $p \nmid D$ imply that $\bar f$ is nondegenerate over
$\mathbb F_p$ also for $p = 2$, where it never holds). -/
noncomputable def hessianDiscr (f : MvPolynomial (Fin 3) ℤ) : ℤ :=
  (Matrix.of fun i j => eval 0 (pderiv i (pderiv j f))).det

/-- Evaluating the reduction of an integer polynomial is `aeval`. -/
lemma eval_map_eq_aeval {σ R : Type*} [CommRing R] (x : σ → R) (g : MvPolynomial σ ℤ) :
    eval x (map (Int.castRingHom R) g) = aeval x g := by
  rw [eval_map, aeval_def]
  rfl

/-- The gradient of a quadratic form is the Hessian matrix times the vector: as polynomials,
$\partial f/\partial X_i = \sum_j (\partial^2 f/\partial X_j \partial X_i)(0)\, X_j$. -/
lemma pderiv_eq_sum (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous 2) (i : Fin 3) :
    pderiv i f = ∑ j, C (eval 0 (pderiv j (pderiv i f))) * X j := by
  have hg : (pderiv i f).IsHomogeneous 1 := by simpa using hf.pderiv (i := i)
  have h1 := hg.sum_X_mul_pderiv
  rw [one_smul] at h1
  conv_lhs => rw [← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : (pderiv j (pderiv i f)).IsHomogeneous 0 := by simpa using hg.pderiv (i := j)
  have h2 := (totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous _).2 h0))
  have h3 : eval 0 (pderiv j (pderiv i f)) = (pderiv j (pderiv i f)).coeff 0 := by
    conv_lhs => rw [h2]
    simp
  rw [h3, mul_comm]
  conv_lhs => rw [h2]

/-- The value of the gradient of a quadratic form at a point of any commutative ring. -/
lemma aeval_pderiv {S : Type*} [CommRing S] (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous 2)
    (x : Fin 3 → S) (i : Fin 3) :
    aeval x (pderiv i f) = ∑ j, ((eval 0 (pderiv j (pderiv i f)) : ℤ) : S) * x j := by
  conv_lhs => rw [pderiv_eq_sum f hf i]
  simp [map_sum]

/-- If the Hessian determinant is nonzero in an integral domain `S`, the gradient of a quadratic form
does not vanish at a nonzero point of `S`. -/
lemma exists_aeval_pderiv_ne_zero {S : Type*} [CommRing S] [IsDomain S]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous 2) (hD : (hessianDiscr f : S) ≠ 0)
    (x : Fin 3 → S) (hx : x ≠ 0) : ∃ i, aeval x (pderiv i f) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set H : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun i j => eval 0 (pderiv j (pderiv i f)) with hH
  have hmul : (H.map (Int.castRingHom S)).mulVec x = 0 := by
    funext i
    have := hcon i
    rw [aeval_pderiv f hf x i] at this
    simpa [Matrix.mulVec, dotProduct, hH] using this
  have hdet : (H.map (Int.castRingHom S)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx, hmul⟩
  have h2 : (H.map (Int.castRingHom S)).det = ((H.det : ℤ) : S) :=
    (RingHom.map_det (Int.castRingHom S) H).symm
  have h3 : H.det = hessianDiscr f := by
    rw [hessianDiscr, ← Matrix.det_transpose]
    rfl
  rw [h2, h3] at hdet
  exact hD hdet

/-- A quadratic form is homogeneous of degree two: $f(cx) = c^2 f(x)$. -/
lemma aeval_smul_homog {S : Type*} [CommRing S] (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous 2) (c : S) (x : Fin 3 → S) :
    aeval (c • x) f = c ^ 2 * aeval x f := by
  rw [← eval_map_eq_aeval, ← eval_map_eq_aeval]
  have h := hf.map (Int.castRingHom S)
  conv_lhs => rw [(map (Int.castRingHom S) f).as_sum]
  conv_rhs => rw [(map (Int.castRingHom S) f).as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg := h (mem_support_iff.1 hd)
  simp only [eval_monomial, Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have : ∑ i ∈ d.support, d i = 2 := by
    simpa [Finsupp.weight_apply, Finsupp.sum] using hdeg
  rw [this]
  ring

/-- A nontrivial zero in `ℤ_[p]^3` of an integer polynomial gives one in `ℚ_[p]^3`. -/
lemma exists_padic_zero_of_padicInt_zero (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 3) ℤ)
    (w : Fin 3 → ℤ_[p]) (hw0 : w ≠ 0) (hw : aeval w f = 0) :
    ∃ x : Fin 3 → ℚ_[p], x ≠ 0 ∧ aeval x f = 0 := by
  refine ⟨fun j => (w j : ℚ_[p]),
    fun h0 => hw0 (funext fun j => Subtype.ext (by simpa using congrFun h0 j)), ?_⟩
  have := map_aeval_int (PadicInt.Coe.ringHom (p := p)) w f
  rw [hw, map_zero] at this
  exact this.symm

/-- Evaluating an integer polynomial at the image of an integer point. -/
lemma aeval_intCast_point {σ : Type*} {S : Type*} [CommRing S] (g : MvPolynomial σ ℤ)
    (a : σ → ℤ) : aeval (fun j => (a j : S)) g = ((eval a g : ℤ) : S) := by
  have h1 := map_aeval_int (Int.castRingHom S) a g
  have e : aeval a g = eval a g := by
    rw [aeval_def, eval, coe_eval₂Hom]
    congr 1
  rw [e] at h1
  exact h1.symm

/-- If `w` and the integer point `a` agree modulo $p^N$, then so do the values of an integer
polynomial at them. -/
lemma congr_aeval_int {n : ℕ} (p : ℕ) [Fact p.Prime] (N : ℕ) (g : MvPolynomial (Fin n) ℤ)
    (w : Fin n → ℤ_[p]) (a : Fin n → ℤ)
    (h : ∀ j, w j - (a j : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ N}) :
    aeval w g - ((eval a g : ℤ) : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ N} := by
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_aeval_int, sub_eq_zero]
  have hk : ∀ j, PadicInt.toZModPow N (w j) = PadicInt.toZModPow N (a j : ℤ_[p]) := fun j => by
    have := h j
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  have e1 : (PadicInt.toZModPow N : ℤ_[p] →+* ZMod (p ^ N)) ∘ w =
      (PadicInt.toZModPow N : ℤ_[p] →+* ZMod (p ^ N)) ∘ (fun j => (a j : ℤ_[p])) := funext hk
  rw [e1, ← map_aeval_int, aeval_intCast_point]

/-- Chevalley–Warning: a quadratic form in three variables over `𝔽_p` has a nontrivial zero. -/
lemma exists_nontrivial_zero_zmod (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous 2) : ∃ x : Fin 3 → ZMod p, x ≠ 0 ∧ aeval x f = 0 := by
  classical
  have hdeg : (map (Int.castRingHom (ZMod p)) f).totalDegree < Fintype.card (Fin 3) := by
    have := (hf.map (Int.castRingHom (ZMod p))).totalDegree_le
    simp only [Fintype.card_fin]
    omega
  have hcard := char_dvd_card_solutions p hdeg
  by_contra hno
  push Not at hno
  have h1 : Fintype.card {x : Fin 3 → ZMod p // eval x (map (Int.castRingHom (ZMod p)) f) = 0} =
      1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, ?_⟩, fun ⟨x, hx⟩ => ?_⟩
    · rw [eval_map_eq_aeval]
      have := aeval_smul_homog f hf (0 : ZMod p) 0
      simpa using this
    · apply Subtype.ext
      by_contra hne
      exact hno x hne (by rw [← eval_map_eq_aeval]; exact hx)
  rw [h1] at hcard
  exact (Fact.out : p.Prime).not_dvd_one hcard

/-- **Example 2.15** (p. 33), first part: let `f` be a quadratic form in three variables with integer
coefficients and discriminant $D \neq 0$.  If $p \nmid D$, then $\bar f$ has a nontrivial zero in
$\mathbb F_p$ and `f` has a nontrivial zero in $\mathbb Q_p$. -/
@[kb "milne2006ec" "Ch. I, Ex. 2.15, pdf p. 33"]
theorem example_2_15 (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous 2)
    (hD : ¬ (p : ℤ) ∣ hessianDiscr f) :
    (∃ x : Fin 3 → ZMod p, x ≠ 0 ∧ eval x (map (Int.castRingHom (ZMod p)) f) = 0) ∧
    ∃ x : Fin 3 → ℚ_[p], x ≠ 0 ∧ aeval x f = 0 := by
  have hDz : (hessianDiscr f : ZMod p) ≠ 0 := fun h =>
    hD ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h)
  obtain ⟨x, hx0, hx⟩ := exists_nontrivial_zero_zmod p f hf
  refine ⟨⟨x, hx0, by rw [eval_map_eq_aeval]; exact hx⟩, ?_⟩
  obtain ⟨i, hi⟩ := exists_aeval_pderiv_ne_zero (S := ZMod p) f hf hDz x hx0
  set a : Fin 3 → ℤ := fun j => ((x j).val : ℤ) with ha
  have hax : (fun j => (a j : ZMod p)) = x := by funext j; simp [a]
  obtain ⟨w, hw0, hw, -⟩ := example_2_14 p f hf a (by rw [hax]; exact hx0)
    (by rw [hax, eval_map_eq_aeval]; exact hx)
    ⟨i, by rw [hax, eval_map_eq_aeval]; exact hi⟩
  exact exists_padic_zero_of_padicInt_zero p f w hw0 hw

/-- **Example 2.15** (p. 33), second part: a quadratic form `f` in three variables with integer
coefficients and $D \neq 0$ has a nontrivial zero in $\mathbb Q_p$ if and only if it has an "approximate
zero", which we take to be the hypothesis of Lemma 2.10: a vector $a \in \mathbb Z^3$, not all entries
divisible by `p`, with $f(a) \equiv 0 \bmod p^{2m+1}$ and some $(\partial f/\partial X_i)(a)
\not\equiv 0 \bmod p^{m+1}$. (This holds for every prime `p`.) -/
@[kb "milne2006ec" "Ch. I, Ex. 2.15, approximate zeros, pdf p. 33"]
theorem example_2_15_approx (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous 2) (hD : hessianDiscr f ≠ 0) :
    (∃ x : Fin 3 → ℚ_[p], x ≠ 0 ∧ aeval x f = 0) ↔
      ∃ (m : ℕ) (a : Fin 3 → ℤ), (∃ j, ¬ (p : ℤ) ∣ a j) ∧ (p : ℤ) ^ (2 * m + 1) ∣ eval a f ∧
        ∃ i, ¬ (p : ℤ) ^ (m + 1) ∣ eval a (pderiv i f) := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    obtain ⟨j0, hmax⟩ := Finite.exists_max (fun j => ‖x j‖)
    have hxj0 : x j0 ≠ 0 := fun h => hx0 (funext fun j =>
      norm_le_zero_iff.1 ((hmax j).trans (by rw [h, norm_zero])))
    set c : ℚ_[p] := (x j0)⁻¹ with hc
    have hcn : ∀ j, ‖c * x j‖ ≤ 1 := fun j => by
      rw [norm_mul, hc, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 hxj0), mul_one]
      exact hmax j
    let w : Fin 3 → ℤ_[p] := fun j => ⟨c * x j, hcn j⟩
    have hwj0 : w j0 = 1 := Subtype.ext (by simp [w, hc, inv_mul_cancel₀ hxj0])
    have hw0 : w ≠ 0 := fun h => by
      have := congrFun h j0
      rw [hwj0] at this
      exact one_ne_zero this
    have hww : aeval w f = 0 := by
      have h1 := map_aeval_int (PadicInt.Coe.ringHom (p := p)) w f
      have h2 : (PadicInt.Coe.ringHom (p := p)) ∘ w = c • x := rfl
      rw [h2, aeval_smul_homog f hf c x, hx, mul_zero] at h1
      exact Subtype.ext h1
    have hDp : ((hessianDiscr f : ℤ) : ℤ_[p]) ≠ 0 := Int.cast_ne_zero.2 hD
    obtain ⟨i, hi⟩ := exists_aeval_pderiv_ne_zero (S := ℤ_[p]) f hf hDp w hw0
    set G : ℤ_[p] := aeval w (pderiv i f) with hG
    have hpn : ‖(p : ℤ_[p])‖ < 1 := by
      rw [PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hi) hpn
    have hnd : ¬ (p : ℤ_[p]) ^ (k + 1) ∣ G := by
      intro hd
      have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow G (k + 1)).2 (Ideal.mem_span_singleton.2 hd)
      rw [← PadicInt.norm_p_pow, norm_pow] at h1
      have h2 : ‖(p : ℤ_[p])‖ ^ (k + 1) ≤ ‖(p : ℤ_[p])‖ ^ k :=
        pow_le_pow_of_le_one (norm_nonneg _) hpn.le (Nat.le_succ k)
      linarith
    set N : ℕ := 3 * k + 2 with hN
    let a : Fin 3 → ℤ := fun j => ((w j).appr N : ℤ)
    have hap : ∀ j, w j - (a j : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ N} := by
      intro j
      simpa [a] using PadicInt.appr_spec N (w j)
    refine ⟨k, a, ⟨j0, ?_⟩, ?_, i, ?_⟩
    · intro hd
      have h1 : (p : ℤ_[p]) ∣ w j0 - (a j0 : ℤ_[p]) := by
        have := Ideal.mem_span_singleton.1 (hap j0)
        exact (dvd_pow_self (p : ℤ_[p]) (by omega)).trans this
      have h2 : (p : ℤ_[p]) ∣ (a j0 : ℤ_[p]) := by
        obtain ⟨d, hd⟩ := hd
        exact ⟨d, by rw [hd]; push_cast; ring⟩
      rw [hwj0] at h1
      have h3 := dvd_add h1 h2
      simp only [sub_add_cancel] at h3
      exact PadicInt.p_nonunit (isUnit_of_dvd_one h3)
    · have h := congr_aeval_int p N f w a hap
      rw [hww, zero_sub, Ideal.neg_mem_iff, Ideal.mem_span_singleton,
        PadicInt.pow_p_dvd_int_iff] at h
      exact (pow_dvd_pow (p : ℤ) (show 2 * k + 1 ≤ N by omega)).trans (by exact_mod_cast h)
    · intro hd
      have h := congr_aeval_int p N (pderiv i f) w a hap
      rw [← hG, Ideal.mem_span_singleton] at h
      have h1 : (p : ℤ_[p]) ^ (k + 1) ∣ ((eval a (pderiv i f) : ℤ) : ℤ_[p]) :=
        (PadicInt.pow_p_dvd_int_iff _ _).2 (by exact_mod_cast hd)
      have h2 : (p : ℤ_[p]) ^ (k + 1) ∣ G - ((eval a (pderiv i f) : ℤ) : ℤ_[p]) :=
        (pow_dvd_pow _ (by omega)).trans h
      exact hnd (by simpa using dvd_add h2 h1)
  · rintro ⟨m, a, ⟨j, hj⟩, hfa, i, hi⟩
    obtain ⟨b, hb0, hb⟩ := theorem_2_12 p f a m hfa ⟨i, hi⟩
    refine exists_padic_zero_of_padicInt_zero p f b ?_ hb0
    intro h0
    obtain ⟨c, hc⟩ := hb j
    have h1 : (p : ℤ_[p]) ^ 1 ∣ (a j : ℤ_[p]) := by
      refine ⟨-((p : ℤ_[p]) ^ m * c), ?_⟩
      have : (a j : ℤ_[p]) = -((p : ℤ_[p]) ^ (m + 1) * c) := by
        rw [← hc, h0]; simp
      rw [this]; ring
    rw [PadicInt.pow_p_dvd_int_iff] at h1
    exact hj (by simpa using h1)

/-- **Exercise 2.17** (p. 33): the point $(0, 0)$ of the reduction $Y^2 = X^3$ of
$C : Y^2 = X^3 + p$ does not lift to a point of $C$ with coordinates in $\mathbb Z_p$; this does not
contradict Hensel's lemma because $(0, 0)$ is a singular point of the reduced curve. -/
@[kb "milne2006ec" "Ch. I, Ex. 2.17, pdf p. 33"]
theorem exercise_2_17 (p : ℕ) [Fact p.Prime] :
    (¬ ∃ x y : ℤ_[p], y ^ 2 = x ^ 3 + p ∧ PadicInt.toZMod x = 0 ∧ PadicInt.toZMod y = 0) ∧
    IsSingularPoint (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) (ZMod p)) ((0, 0) : ZMod p × ZMod p) := by
  constructor
  · rintro ⟨x, y, h, hx, hy⟩
    have mem : ∀ z : ℤ_[p], PadicInt.toZMod z = 0 → ∃ c, z = p * c := by
      intro z hz
      have : z ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := hz
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
      exact this
    obtain ⟨c, rfl⟩ := mem x hx
    obtain ⟨d, rfl⟩ := mem y hy
    have hp : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have h2 : (p : ℤ_[p]) * (p * d ^ 2 - (p ^ 2 * c ^ 3 + 1)) = 0 := by linear_combination h
    have h3 := (mul_eq_zero.1 h2).resolve_left hp
    have h4 : (p : ℤ_[p]) * (d ^ 2 - p * c ^ 3) = 1 := by linear_combination h3
    exact PadicInt.p_nonunit (IsUnit.of_mul_eq_one _ h4)
  · refine ⟨?_, ?_, ?_⟩ <;> simp [affinePoints, evalAt, dX, dY]

end NumberFieldKB.MilneEC
