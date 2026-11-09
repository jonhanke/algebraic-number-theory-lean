import QuadFormsKB.Literature.LocalGlobal.HilbertReciprocity
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Literature.LocalGlobal.HasseConventions
import QuadFormsKB.Equiv.Hilbert

/-! # Milne, *Class Field Theory*, Remark VIII.3.2: the rational core

Source: J. S. Milne, *Class Field Theory*, v4.03 (2020), Chapter VIII, Remark 3.2, p. 234, which
cites Cassels–Fröhlich, Exercise 5.3.

The remark exhibits the biquadratic extension $\mathbb{Q}(\sqrt{13}, \sqrt{17})$, for which the
Hasse norm principle fails ($25$ is a local norm everywhere but not a global norm). The rational
arithmetic behind the global half is the following statements.

* `isSquare_padic`: at every prime $p$, at least one of $13$, $17$, $221 = 13 \cdot 17$ is a
  square in $\mathbb{Q}_p$.
* `not_isSquare_thirteen_five`, `not_isSquare_seventeen_five`: neither $13$ nor $17$ is a square in
  $\mathbb{Q}_5$.
* `rational_core`: for rationals with $m^2 - 13k^2 \ne 0$, the equation
  $5(m^2 - 13k^2) = (x^2 - 17y^2)(z^2 - 221w^2)$ has no solution.  The proof applies Hilbert's
  product formula to the symbol $(5(m^2-13k^2), 17)_v$, which equals $1$ at every place $v$
  except $v = 5$, where it equals $-1$.
-/

open QuadFormsKB

namespace NumberFieldKB.MilneCFT.Ch8.R32

/-- Residue criterion for natural numbers: for an odd prime $p \nmid n$, $n$ is a square in
$\mathbb{Q}_p$ iff it is a square modulo $p$. -/
theorem isSquare_nat_iff (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (n : ℕ) (hn : ¬ p ∣ n) :
    IsSquare (n : ℚ_[p]) ↔ IsSquare (n : ZMod p) := by
  have hu : IsUnit (n : ℤ_[p]) := PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
    ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hn))
  have := QuadFormsKB.HilbertLocal.isSquare_unit_iff hp2 hu.unit
  simpa using this

local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance fact_prime_thirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩
local instance fact_prime_seventeen : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- $17$ is a square in $\mathbb{Q}_2$, since $17 \equiv 1 \pmod 8$. -/
theorem isSquare_17_two : IsSquare (17 : ℚ_[2]) := by
  have hu : IsUnit (17 : ℤ_[2]) := PadicInt.isUnit_iff.mpr (by
    have := PadicInt.norm_natCast_eq_one_iff (p := 2) (n := 17)
    simpa using this.mpr (by norm_num))
  have := (QuadFormsKB.HilbertLocal.isSquare_two_adic_unit_iff hu.unit).mpr (by
    simp only [IsUnit.unit_spec]
    have : (17 : ℤ_[2]) = ((17 : ℕ) : ℤ_[2]) := by norm_num
    rw [this, map_natCast]; decide)
  have e : (((17 : ℤ_[2]) : ℚ_[2])) = 17 := by norm_cast
  simpa [e] using this

/-- $17 \equiv 4 = 2^2 \pmod{13}$, so $17$ is a square in $\mathbb{Q}_{13}$. -/
theorem isSquare_17_thirteen : IsSquare (17 : ℚ_[13]) := by
  have := isSquare_nat_iff 13 (by norm_num) 17 (by norm_num)
  simp only [Nat.cast_ofNat] at this
  rw [this]
  exact ⟨2, by decide⟩

/-- $13 \equiv 64 = 8^2 \pmod{17}$, so $13$ is a square in $\mathbb{Q}_{17}$. -/
theorem isSquare_13_seventeen : IsSquare (13 : ℚ_[17]) := by
  have := isSquare_nat_iff 17 (by norm_num) 13 (by norm_num)
  simp only [Nat.cast_ofNat] at this
  rw [this]
  exact ⟨8, by decide⟩

/-- At every prime $p$ other than $2, 13, 17$, one of $13$, $17$, $221$ is a square in
$\mathbb{Q}_p$: if $13$ and $17$ are non-squares modulo $p$, then $221 = 13 \cdot 17$ is a
square, by multiplicativity of the quadratic character. -/
theorem isSquare_padic_aux (p : ℕ) [Fact p.Prime] (h2 : p ≠ 2) (h13 : p ≠ 13) (h17 : p ≠ 17) :
    IsSquare (13 : ℚ_[p]) ∨ IsSquare (17 : ℚ_[p]) ∨ IsSquare (221 : ℚ_[p]) := by
  have hp := (Fact.out : p.Prime)
  have n13 : ¬ p ∣ 13 := fun h => h13 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
  have n17 : ¬ p ∣ 17 := fun h => h17 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
  have n221 : ¬ p ∣ 221 := by
    intro h
    have : p ∣ 13 * 17 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h <;> contradiction
  have e13 := isSquare_nat_iff p h2 13 n13
  have e17 := isSquare_nat_iff p h2 17 n17
  have e221 := isSquare_nat_iff p h2 221 n221
  simp only [Nat.cast_ofNat] at e13 e17 e221
  haveI : Fact (ringChar (ZMod p) ≠ 2) := ⟨by rw [ZMod.ringChar_zmod_n]; exact h2⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨c13, c17, c221⟩ := hcon
  rw [e13] at c13
  rw [e17] at c17
  rw [e221] at c221
  have q13 := (quadraticChar_neg_one_iff_not_isSquare).mpr c13
  have q17 := (quadraticChar_neg_one_iff_not_isSquare).mpr c17
  have q221 := (quadraticChar_neg_one_iff_not_isSquare).mpr c221
  have : (221 : ZMod p) = 13 * 17 := by norm_num
  rw [this, map_mul, q13, q17] at q221
  norm_num at q221

/-- At every prime $p$, one of $13$, $17$, $221$ is a square in $\mathbb{Q}_p$. -/
theorem isSquare_padic (p : ℕ) [Fact p.Prime] :
    IsSquare (13 : ℚ_[p]) ∨ IsSquare (17 : ℚ_[p]) ∨ IsSquare (221 : ℚ_[p]) := by
  by_cases h2 : p = 2
  · subst h2
    exact Or.inr (Or.inl isSquare_17_two)
  by_cases h13 : p = 13
  · subst h13
    exact Or.inr (Or.inl isSquare_17_thirteen)
  by_cases h17 : p = 17
  · subst h17
    exact Or.inl isSquare_13_seventeen
  exact isSquare_padic_aux p h2 h13 h17

/-- $13$ is not a square in $\mathbb{Q}_5$ (it is $\equiv 3 \pmod 5$). -/
theorem not_isSquare_thirteen_five : ¬ IsSquare (13 : ℚ_[5]) := by
  have := isSquare_nat_iff 5 (by norm_num) 13 (by norm_num)
  simp only [Nat.cast_ofNat] at this
  rw [this]
  decide

/-- $17$ is not a square in $\mathbb{Q}_5$ (it is $\equiv 2 \pmod 5$). -/
theorem not_isSquare_seventeen_five : ¬ IsSquare (17 : ℚ_[5]) := by
  have := isSquare_nat_iff 5 (by norm_num) 17 (by norm_num)
  simp only [Nat.cast_ofNat] at this
  rw [this]
  decide

/-! ### Hilbert symbol computations -/

/-- Over a field $K$, $(b, d)_K = 1$ whenever $b$ is a square: take $(x,y,z) = (0, 1, \sqrt b)$
in $z^2 = a x^2 + b y^2$. -/
theorem hs_one_of_isSquare (K : Type*) [Field K] (a b : K) (h : IsSquare b) :
    hilbertSymbol K a b = 1 := by
  obtain ⟨c, hc⟩ := h
  unfold hilbertSymbol
  rw [if_pos]
  exact ⟨0, 1, c, by simp, by rw [hc]; ring⟩

/-- Over a field $K$, $(x^2 - d y^2, d)_K = 1$: take $(1, y, x)$. -/
theorem hs_norm (K : Type*) [Field K] (d x y : K) :
    hilbertSymbol K (x ^ 2 - d * y ^ 2) d = 1 := by
  unfold hilbertSymbol
  rw [if_pos]
  exact ⟨1, y, x, by simp, by ring⟩

/-- "$b$ is a square in $\mathbb{Q}_v$", for a rational $b$. -/
def IsSqAt (v : RatPlace) (b : ℚ) : Prop :=
  RatPlace.atPlace (fun K _ _ => IsSquare (b : K)) v

/-- If $b$ is a square in $\mathbb{Q}_v$ then $(a, b)_v = 1$. -/
theorem hilbert_one_of_isSqAt (v : RatPlace) (a b : ℚ) (h : IsSqAt v b) : v.hilbert a b = 1 := by
  cases v with
  | infinite => exact hs_one_of_isSquare ℝ _ _ h
  | finite p =>
    haveI : Fact p.1.Prime := ⟨p.2⟩
    exact hs_one_of_isSquare ℚ_[p.1] _ _ h

/-- $(x^2 - d y^2, d)_v = 1$ at every place $v$. -/
theorem hilbert_norm (v : RatPlace) (d x y : ℚ) : v.hilbert (x ^ 2 - d * y ^ 2) d = 1 := by
  cases v with
  | infinite =>
    have := hs_norm ℝ (d : ℝ) x y
    simpa [RatPlace.hilbert] using this
  | finite p =>
    haveI : Fact p.1.Prime := ⟨p.2⟩
    have := hs_norm ℚ_[p.1] (d : ℚ_[p.1]) x y
    simpa [RatPlace.hilbert] using this

/-- The local computation at a place $v$: with $5 n = A B$, if $13$ or $17$ is a square in
$\mathbb{Q}_v$ then $(5n, 17)_v = 1$; if $221$ is a square then $(5n, 17)_v = (5, 17)_v$. -/
theorem local_step (v : RatPlace) (A B n : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hn : n ≠ 0)
    (hq : 5 * n = A * B) (hAn : v.hilbert A 17 = 1) (hB221 : v.hilbert B 221 = 1)
    (hn13 : v.hilbert n 13 = 1) :
    (IsSqAt v 13 → v.hilbert (5 * n) 17 = 1) ∧ (IsSqAt v 17 → v.hilbert (5 * n) 17 = 1) ∧
      (IsSqAt v 221 → v.hilbert (5 * n) 17 = v.hilbert 5 17) := by
  have h221 : (221 : ℚ) = 13 * 17 := by norm_num
  refine ⟨fun h13 => ?_, fun h17 => hilbert_one_of_isSqAt v _ _ h17, fun h221' => ?_⟩
  · rw [hq, QuadFormsKB.HilbertLocal.RatPlace.hilbert_mul_left v A B 17 hA hB (by norm_num), hAn,
      one_mul]
    have hB13 := hilbert_one_of_isSqAt v B 13 h13
    rw [h221, QuadFormsKB.RatPlace.hilbert_mul_right v B 13 17 hB (by norm_num) (by norm_num),
      hB13, one_mul] at hB221
    exact hB221
  · have hn221 := hilbert_one_of_isSqAt v n 221 h221'
    rw [h221, QuadFormsKB.RatPlace.hilbert_mul_right v n 13 17 hn (by norm_num) (by norm_num),
      hn13, one_mul] at hn221
    rw [QuadFormsKB.HilbertLocal.RatPlace.hilbert_mul_left v 5 n 17 (by norm_num) hn
      (by norm_num), hn221, mul_one]

/-- $(5, 17)_5 = -1$: $17 \equiv 2 \pmod 5$ is not a square. -/
theorem hilbert_five_seventeen_five :
    RatPlace.hilbert (.finite ⟨5, by norm_num⟩) 5 17 = -1 := by
  have hu : IsUnit (17 : ℤ_[5]) := PadicInt.isUnit_iff.mpr (by
    have := PadicInt.norm_natCast_eq_one_iff (p := 5) (n := 17)
    simpa using this.mpr (by norm_num))
  have key := QuadFormsKB.HilbertLocal.hilbertSymbol_odd_formula (p := 5) (by norm_num) 1 0 1 hu.unit
  simp only [pow_one, pow_zero, one_mul, mul_zero, zero_mul, Units.val_one, PadicInt.coe_one,
    Padic.coe_one, mul_one, one_zpow] at key
  have e : (((17 : ℤ_[5]) : ℚ_[5])) = 17 := by norm_cast
  simp only [RatPlace.hilbert]
  simp only [IsUnit.unit_spec, e, Nat.cast_ofNat] at key
  push_cast
  rw [key]
  unfold QuadFormsKB.HilbertLocal.unitChar
  simp only [IsUnit.unit_spec]
  have e2 : (17 : ℤ_[5]) = ((17 : ℕ) : ℤ_[5]) := by norm_num
  rw [e2, map_natCast]
  haveI : Fact (ringChar (ZMod 5) ≠ 2) := ⟨by rw [ZMod.ringChar_zmod_n]; norm_num⟩
  exact quadraticChar_neg_one_iff_not_isSquare.mpr (by decide)

/-- Unfolding `IsSqAt` at a finite place. -/
theorem isSqAt_finite (p : ℕ) [hp : Fact p.Prime] (b : ℚ) :
    IsSqAt (.finite ⟨p, hp.out⟩) b ↔ IsSquare (b : ℚ_[p]) := Iff.rfl

/-- The symbol $(5 n, 17)_v$ is $1$ at every place $v \ne 5$, given the local identities. -/
theorem hilbert_ne_five (v : RatPlace) (hv : v ≠ .finite ⟨5, by norm_num⟩) (A B n : ℚ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hn : n ≠ 0) (hq : 5 * n = A * B) (hAn : v.hilbert A 17 = 1)
    (hB221 : v.hilbert B 221 = 1) (hn13 : v.hilbert n 13 = 1) : v.hilbert (5 * n) 17 = 1 := by
  obtain ⟨s13, s17, s221⟩ := local_step v A B n hA hB hn hq hAn hB221 hn13
  cases v with
  | infinite =>
    apply s17
    refine ⟨Real.sqrt 17, ?_⟩
    have : ((17 : ℚ) : ℝ) = 17 := by norm_num
    show ((17 : ℚ) : ℝ) = _
    rw [this, Real.mul_self_sqrt (by norm_num)]
  | finite q =>
    obtain ⟨p, hp⟩ := q
    haveI : Fact p.Prime := ⟨hp⟩
    have hp5 : p ≠ 5 := fun h => hv (by subst h; rfl)
    by_cases h2 : p = 2
    · subst h2
      apply s17
      rw [isSqAt_finite]
      simpa using isSquare_17_two
    by_cases h17 : p = 17
    · subst h17
      apply s13
      rw [isSqAt_finite]
      simpa using isSquare_13_seventeen
    rcases isSquare_padic p with h | h | h
    · exact s13 (by rw [isSqAt_finite]; simpa using h)
    · exact s17 (by rw [isSqAt_finite]; simpa using h)
    · rw [s221 (by rw [isSqAt_finite]; simpa using h)]
      have n5 : ¬ p ∣ 5 := fun h => hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
      have n17 : ¬ p ∣ 17 := fun h => h17 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
      exact QuadFormsKB.HilbertLocal.hilbert_eq_one_of_padicValRat h2 5 17 (by norm_num)
        (by norm_num)
        (by
          have := padicValRat.of_nat (p := p) (n := 5)
          simp only [Nat.cast_ofNat] at this
          rw [this, padicValNat.eq_zero_of_not_dvd n5]; rfl)
        (by
          have := padicValRat.of_nat (p := p) (n := 17)
          simp only [Nat.cast_ofNat] at this
          rw [this, padicValNat.eq_zero_of_not_dvd n17]; rfl)

/-- The symbol $(5 n, 17)_5 = -1$ when $5 n = A B$. -/
theorem hilbert_at_five (A B n : ℚ) (hA : A ≠ 0) (hB : B ≠ 0) (hn : n ≠ 0)
    (hq : 5 * n = A * B) (hAn : (RatPlace.finite ⟨5, by norm_num⟩).hilbert A 17 = 1)
    (hB221 : (RatPlace.finite ⟨5, by norm_num⟩).hilbert B 221 = 1)
    (hn13 : (RatPlace.finite ⟨5, by norm_num⟩).hilbert n 13 = 1) :
    (RatPlace.finite ⟨5, by norm_num⟩).hilbert (5 * n) 17 = -1 := by
  obtain ⟨-, -, s221⟩ := local_step (.finite ⟨5, by norm_num⟩) A B n hA hB hn hq hAn hB221 hn13
  rw [s221, hilbert_five_seventeen_five]
  rcases isSquare_padic 5 with h | h | h
  · exact absurd h not_isSquare_thirteen_five
  · exact absurd h not_isSquare_seventeen_five
  · rw [isSqAt_finite]; simpa using h

/-- The rational core of Remark VIII.3.2. -/
theorem rational_core (m k x y z w : ℚ) (hn : m ^ 2 - 13 * k ^ 2 ≠ 0) :
    5 * (m ^ 2 - 13 * k ^ 2) ≠ (x ^ 2 - 17 * y ^ 2) * (z ^ 2 - 221 * w ^ 2) := by
  intro hq
  set n := m ^ 2 - 13 * k ^ 2 with hn_def
  set A := x ^ 2 - 17 * y ^ 2 with hA_def
  set B := z ^ 2 - 221 * w ^ 2 with hB_def
  have h5n : 5 * n ≠ 0 := mul_ne_zero (by norm_num) hn
  have hAB : A * B ≠ 0 := hq ▸ h5n
  have hA : A ≠ 0 := left_ne_zero_of_mul hAB
  have hB : B ≠ 0 := right_ne_zero_of_mul hAB
  have hset : {v : RatPlace | v.hilbert (5 * n) 17 = -1} = {.finite ⟨5, by norm_num⟩} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    have hAn := hilbert_norm v 17 x y
    have hB221 := hilbert_norm v 221 z w
    have hn13 := hilbert_norm v 13 m k
    constructor
    · intro h
      by_contra hne
      have := hilbert_ne_five v hne A B n hA hB hn hq hAn hB221 hn13
      rw [this] at h
      norm_num at h
    · rintro rfl
      exact hilbert_at_five A B n hA hB hn hq hAn hB221 hn13
  obtain ⟨-, hev⟩ := hilbert_product_formula (5 * n) 17 h5n (by norm_num)
  rw [hset, Set.ncard_singleton] at hev
  exact absurd hev (by decide)

end NumberFieldKB.MilneCFT.Ch8.R32
