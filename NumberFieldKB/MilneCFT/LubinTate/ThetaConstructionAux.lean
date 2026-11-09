import NumberFieldKB.MilneCFT.LubinTate.FrobeniusMinusOne
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Auxiliary lemmas for the construction of θ in Proposition 3.10 (Milne, *Class Field Theory*, Ch. I)

Generic facts about composition of power series over a commutative ring (cancellation of an invertible series on
the right, the coefficients of a composite), a successive approximation principle for sequences, and the
construction of the first approximation $\theta_0$ of Proposition 3.10, which satisfies
$\theta_0^\sigma = \theta_0 \circ [u]_f$.
-/

open scoped ValuativeRel

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

/-- Composition of power series: `P ⊚ Q` is `P(Q(T))`. -/
local notation:90 P:91 " ⊚ " Q:90 => PowerSeries.subst Q P

section Generic

variable {R : Type*} [CommRing R]

theorem hs0 {Q : PowerSeries R} (h : PowerSeries.constantCoeff Q = 0) : PowerSeries.HasSubst Q :=
  PowerSeries.HasSubst.of_constantCoeff_zero' h

theorem cz_subst {P Q : PowerSeries R} (hP : PowerSeries.constantCoeff P = 0)
    (hQ : PowerSeries.constantCoeff Q = 0) : PowerSeries.constantCoeff (P.subst Q) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hQ P hP

/-- Associativity of composition, in the form used throughout. -/
theorem sa (P : PowerSeries R) {Q S : PowerSeries R} (hQ : PowerSeries.constantCoeff Q = 0)
    (hS : PowerSeries.constantCoeff S = 0) : P ⊚ (Q ⊚ S) = (P ⊚ Q) ⊚ S :=
  subst_subst_assoc P hQ hS

/-- A series with zero constant term and unit linear coefficient can be cancelled on the right. -/
theorem subst_right_cancel {Q P P' : PowerSeries R} (hQ0 : PowerSeries.constantCoeff Q = 0)
    (hQ1 : IsUnit (PowerSeries.coeff 1 Q)) (h : P.subst Q = P'.subst Q) : P = P' := by
  have hi0 := PowerSeries.constantCoeff_substInvOfIsUnit Q hQ1
  have hr := PowerSeries.subst_substInvOfIsUnit_right Q hQ0 hQ1
  calc P = P.subst (PowerSeries.X) := (PowerSeries.X_subst P).symm
    _ = P ⊚ (Q ⊚ (Q.substInvOfIsUnit hQ1)) := by rw [hr]
    _ = (P ⊚ Q) ⊚ (Q.substInvOfIsUnit hQ1) := sa P hQ0 hi0
    _ = (P' ⊚ Q) ⊚ (Q.substInvOfIsUnit hQ1) := by rw [h]
    _ = P' ⊚ (Q ⊚ (Q.substInvOfIsUnit hQ1)) := (sa P' hQ0 hi0).symm
    _ = P' := by rw [hr, PowerSeries.X_subst]

theorem coeff_pow_eq_zero_of_lt {U : PowerSeries R} (hU : PowerSeries.constantCoeff U = 0) {n d : ℕ}
    (h : n < d) : PowerSeries.coeff n (U ^ d) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  have := PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hU
  have h2 : ((n : ℕ) : ℕ∞) < d := by exact_mod_cast h
  exact lt_of_lt_of_le h2 this

/-- The coefficients of a composite as a finite sum. -/
theorem coeff_subst_sum {U : PowerSeries R} (hU : PowerSeries.constantCoeff U = 0) (P : PowerSeries R)
    (n : ℕ) :
    PowerSeries.coeff n (P.subst U) =
      ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d P * PowerSeries.coeff n (U ^ d) := by
  rw [PowerSeries.coeff_subst' (hs0 hU), finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp
  · intro d hd
    rw [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    rw [coeff_pow_eq_zero_of_lt hU (by omega), smul_zero]

theorem coeff_pow_self {U : PowerSeries R} (hU : PowerSeries.constantCoeff U = 0) (n : ℕ) :
    PowerSeries.coeff n (U ^ n) = (PowerSeries.coeff 1 U) ^ n := by
  obtain ⟨V, rfl⟩ := PowerSeries.X_dvd_iff.mpr hU
  have h1 : PowerSeries.coeff 1 (PowerSeries.X * V) = PowerSeries.constantCoeff V := by
    simp
  rw [h1, mul_pow, PowerSeries.coeff_X_pow_mul']
  simp

/-- Successive approximation for sequences. -/
theorem exists_seq_of_step {α : Type*} (P : ℕ → (ℕ → α) → Prop)
    (hloc : ∀ n, 1 ≤ n → ∀ a b, (∀ k ≤ n, a k = b k) → P n a → P n b)
    (h0 : ∃ a, P 0 a)
    (hstep : ∀ n a, P n a → ∃ b, P (n + 1) b ∧ ∀ k ≤ n, b k = a k) :
    ∃ a, ∀ n, 1 ≤ n → P n a := by
  have hs : ∀ n (x : {a // P n a}), ∃ y : {a // P (n + 1) a}, ∀ k ≤ n, y.1 k = x.1 k := by
    intro n x
    obtain ⟨y, hy, h⟩ := hstep n x.1 x.2
    exact ⟨⟨y, hy⟩, h⟩
  choose g hg using hs
  obtain ⟨a0, ha0⟩ := h0
  let s : ∀ n, {a // P n a} := fun n =>
    Nat.rec (motive := fun n => {a // P n a}) ⟨a0, ha0⟩ (fun n x => g n x) n
  have hagree : ∀ n r, r ≤ n → (s n).1 r = (s r).1 r := by
    intro n
    induction n with
    | zero => intro r hr; obtain rfl : r = 0 := by omega
              rfl
    | succ n ih =>
      intro r hr
      rcases Nat.lt_or_ge n r with h | h
      · obtain rfl : r = n + 1 := by omega
        rfl
      · have : (s (n + 1)).1 r = (s n).1 r := hg n (s n) r h
        rw [this]; exact ih r h
  refine ⟨fun r => (s r).1 r, fun n hn => hloc n hn (s n).1 _ (fun k hk => ?_) (s n).2⟩
  exact hagree n k hk

end Generic

section Theta0

variable {B : Type*} [CommRing B]

/-- The first approximation $\theta_0$ of Proposition 3.10: given a series `U` with zero constant term and unit
linear coefficient `w`, and a unit `ε` with `σ ε = ε w`, there is `θ₀ = ε T + (deg ≥ 2)` with
`θ₀^σ = θ₀ ∘ U`. Built degree by degree; each step solves `σ z - z = c` (Lemma 3.11). -/
theorem exists_theta0 (σ : B →+* B) (hsolve : ∀ c : B, ∃ b, σ b - b = c)
    {U : PowerSeries B} (hU0 : PowerSeries.constantCoeff U = 0) {w : B} (hw : IsUnit w)
    (hU1 : PowerSeries.coeff 1 U = w) {ε : B} (hε : IsUnit ε) (hεw : σ ε = ε * w) :
    ∃ θ : PowerSeries B, PowerSeries.constantCoeff θ = 0 ∧ PowerSeries.coeff 1 θ = ε ∧
      PowerSeries.map σ θ = θ.subst U := by
  classical
  set c : ℕ → ℕ → B := fun r k => PowerSeries.coeff r (U ^ k) with hc
  let E : ℕ → (ℕ → B) → Prop := fun r a =>
    σ (a r) = ∑ k ∈ Finset.range (r + 1), a k * c r k
  let P : ℕ → (ℕ → B) → Prop := fun n a =>
    a 0 = 0 ∧ a 1 = ε ∧ ∀ r, 1 ≤ r → r ≤ n → E r a
  have hE : ∀ r a b, (∀ k ≤ r, a k = b k) → E r a → E r b := by
    intro r a b hab ha
    simp only [E] at ha ⊢
    rw [← hab r le_rfl, ha]
    exact Finset.sum_congr rfl fun k hk => by rw [hab k (by simpa [Nat.lt_succ_iff] using hk)]
  have hloc : ∀ n, 1 ≤ n → ∀ a b, (∀ k ≤ n, a k = b k) → P n a → P n b := by
    intro n hn a b hab ⟨h0, h1, hr⟩
    refine ⟨by rw [← hab 0 (Nat.zero_le _)]; exact h0, by rw [← hab 1 hn]; exact h1, ?_⟩
    intro r hr1 hrn
    exact hE r a b (fun k hk => hab k (le_trans hk hrn)) (hr r hr1 hrn)
  have hP0 : ∃ a, P 0 a := by
    refine ⟨fun k => if k = 1 then ε else 0, by simp, by simp, ?_⟩
    intro r hr1 hr0
    omega
  have hstep : ∀ n a, P n a → ∃ b, P (n + 1) b ∧ ∀ k ≤ n, b k = a k := by
    intro n a ⟨h0, h1, hr⟩
    rcases n with _ | n
    · refine ⟨a, ⟨h0, h1, ?_⟩, fun _ _ => rfl⟩
      intro r hr1 hr0
      obtain rfl : r = 1 := by omega
      simp only [E, Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, hc, pow_one, hU1,
        zero_mul, zero_add]
      exact hεw
    · set r := n + 2 with hr2
      set S : B := ∑ k ∈ Finset.range r, a k * c r k with hS
      have hu : IsUnit (ε ^ r * w ^ r) := (hε.pow r).mul (hw.pow r)
      obtain ⟨e', he'⟩ := hu.exists_right_inv
      obtain ⟨z, hz⟩ := hsolve (e' * S)
      refine ⟨Function.update a r (ε ^ r * z), ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [Function.update_of_ne (by omega)]; exact h0
      · rw [Function.update_of_ne (by omega)]; exact h1
      · intro r' hr1 hr'
        by_cases hlt : r' ≤ n + 1
        · exact hE r' a _ (fun k hk => (Function.update_of_ne (by omega) _ _).symm) (hr r' hr1 hlt)
        · obtain rfl : r' = r := by omega
          simp only [E]
          rw [Finset.sum_range_succ, Function.update_self]
          have h1 : ∑ k ∈ Finset.range r, Function.update a r (ε ^ r * z) k * c r k = S := by
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [Function.update_of_ne (by simpa using (Finset.mem_range.1 hk).ne)]
          have h2 : c r r = w ^ r := by simp only [hc]; rw [coeff_pow_self hU0, hU1]
          rw [h1, h2, map_mul, map_pow, hεw]
          have h3 : (ε ^ r * w ^ r) * (σ z - z) = S := by
            rw [hz]; linear_combination S * he'
          linear_combination h3
      · intro k hk
        exact Function.update_of_ne (by omega) _ _
  obtain ⟨a, ha⟩ := exists_seq_of_step P hloc hP0 hstep
  refine ⟨PowerSeries.mk a, by simp [(ha 1 le_rfl).1], by simpa using (ha 1 le_rfl).2.1, ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, coeff_subst_sum hU0]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [(ha 1 le_rfl).1]
  · have := (ha n hn).2.2 n hn le_rfl
    simpa only [E, PowerSeries.coeff_mk] using this

end Theta0

section Descent

/-- Descent: a series over `B` fixed by `σ` comes from a series over `A`, when every `σ`-fixed element of `B`
comes from `A`. -/
theorem exists_map_of_fixed {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (σ : B →+* B)
    (hker : ∀ b, σ b = b → ∃ a, φ a = b) (P : PowerSeries B) (hP : PowerSeries.map σ P = P) :
    ∃ P' : PowerSeries A, PowerSeries.map φ P' = P := by
  choose g hg using fun n => hker (PowerSeries.coeff n P) (by
    have := congrArg (PowerSeries.coeff n) hP
    simpa using this)
  refine ⟨PowerSeries.mk g, ?_⟩
  ext n
  simp [hg]

end Descent

section Frobenius

/-- In characteristic `p`, $(P^{(q)})(T^q) = P(T)^q$ for $q = p^n$, where $P^{(q)}$ raises coefficients to the
power `q`. -/
theorem map_frobenius_subst_X_pow {k : Type*} [CommRing k] {p : ℕ} [Fact p.Prime] [CharP k p] (n : ℕ)
    (P : PowerSeries k) :
    (PowerSeries.map (iterateFrobenius k p n) P) ⊚ (PowerSeries.X ^ (p ^ n)) = P ^ (p ^ n) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have h := MvPowerSeries.map_iterateFrobenius_expand (R := k) (σ := Unit) p hp P n
  rw [← PowerSeries.expand_apply (p ^ n) (pow_ne_zero n hp), ← PowerSeries.map_expand]
  exact h

end Frobenius

section Unique

open MvPowerSeries NumberFieldKB.MilneCFT

variable {B : Type*} [CommRing B] [IsDomain B] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eq_zero_of_sub_pow_mul_eq_zero_dom {ϖ : B} (hϖ0 : ϖ ≠ 0) (hϖ1 : ¬ IsUnit ϖ) {N : ℕ}
    (hN : 2 ≤ N) {c : B} (h : (ϖ - ϖ ^ N) * c = 0) : c = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have h2 : ϖ * ((ϖ ^ (m + 1) - 1) * c) = 0 := by linear_combination (-1 : B) * h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 hϖ0
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exfalso
      apply hϖ1
      have : ϖ * ϖ ^ m = 1 := by
        have : ϖ ^ (m + 1) = 1 := by linear_combination h4
        rw [← pow_succ']; exact this
      exact IsUnit.of_mul_eq_one _ this
    · exact h4

theorem vanishes_sub_of_defect_dom {ϖ : B} (hϖ0 : ϖ ≠ 0) (hϖ1 : ¬ IsUnit ϖ) {f g u h : PowerSeries B}
    (hfu : f = PowerSeries.C ϖ * PowerSeries.X + PowerSeries.X ^ 2 * u)
    (hgh : g = PowerSeries.X * h) (hh : PowerSeries.constantCoeff h = ϖ)
    {φ ψ : MvPowerSeries ι B} (hφ : constantCoeff φ = 0) (hψ : constantCoeff ψ = 0)
    (hlin : ∀ i : ι, coeff (Finsupp.single i 1) φ = coeff (Finsupp.single i 1) ψ)
    {N : ℕ} (hN : 2 ≤ N) (hdφ : Vanishes N (defect f g φ)) (hdψ : Vanishes N (defect f g ψ)) :
    Vanishes N (φ - ψ) := by
  induction N, hN using Nat.le_induction with
  | base =>
    intro α hα
    rw [map_sub, sub_eq_zero]
    by_cases h0 : α.degree = 0
    · rw [Finsupp.degree_eq_zero_iff] at h0
      subst h0
      simp only [coeff_zero_eq_constantCoeff_apply, hφ, hψ]
    · have h1 : α.degree = 1 := by omega
      have : α ∈ Set.range (fun a : ι => Finsupp.single a 1) := by
        rw [Finsupp.range_single_one]; exact h1
      obtain ⟨i, rfl⟩ := this
      exact hlin i
  | succ N hN ih =>
    have ih' := ih (hdφ.mono (by omega)) (hdψ.mono (by omega))
    intro α hα
    by_cases hlt : α.degree < N
    · exact ih' α hlt
    · have hdeg : α.degree = N := by omega
      have hQ : Vanishes N (ψ - φ) := fun β hβ => by
        have := ih' β hβ
        rw [map_sub, sub_eq_zero] at this ⊢
        exact this.symm
      have key := coeff_defect_add (f := f) (g := g) hfu hgh hh (by omega) hφ hQ (le_of_eq hdeg)
      rw [add_sub_cancel, hdψ α (by omega)] at key
      rw [hdφ α (by omega)] at key
      simp only [hdeg, ↓reduceIte] at key
      have := eq_zero_of_sub_pow_mul_eq_zero_dom hϖ0 hϖ1 hN (c := coeff α (ψ - φ))
        (by linear_combination (-1 : B) * key)
      rw [map_sub] at this ⊢
      linear_combination -this

/-- Uniqueness for the functional equation `f ∘ φ = φ ∘ g` over a domain, for `f` and `g` with the same
nonzero nonunit linear coefficient `ϖ`. -/
theorem eq_of_defect_zero {ϖ : B} (hϖ0 : ϖ ≠ 0) (hϖ1 : ¬ IsUnit ϖ) {f g : PowerSeries B}
    (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f = ϖ)
    (hg0 : PowerSeries.constantCoeff g = 0) (hg1 : PowerSeries.coeff 1 g = ϖ)
    {φ ψ : MvPowerSeries ι B} (hφ : constantCoeff φ = 0) (hψ : constantCoeff ψ = 0)
    (hlin : ∀ i : ι, coeff (Finsupp.single i 1) φ = coeff (Finsupp.single i 1) ψ)
    (hdφ : defect f g φ = 0) (hdψ : defect f g ψ = 0) : φ = ψ := by
  obtain ⟨u, hfu⟩ := exists_eq_C_mul_X_add hf0 hf1
  obtain ⟨h, hgh, hh⟩ := exists_eq_X_mul hg0 hg1
  ext α
  have := vanishes_sub_of_defect_dom hϖ0 hϖ1 hfu hgh hh hφ hψ hlin (N := α.degree + 2) (by omega)
    (by rw [hdφ]; exact Vanishes.zero _) (by rw [hdψ]; exact Vanishes.zero _) α (by omega)
  rwa [map_sub, sub_eq_zero] at this

end Unique

section Monoid

/-- Power series with zero constant term; the multiplication is composition, `P * Q = P(Q(T))`. -/
abbrev CS (R : Type*) [CommRing R] : Type _ := {P : PowerSeries R // PowerSeries.constantCoeff P = 0}

namespace CS

variable {R S : Type*} [CommRing R] [CommRing S]

instance : Monoid (CS R) where
  mul P Q := ⟨P.1 ⊚ Q.1, cz_subst P.2 Q.2⟩
  one := ⟨PowerSeries.X, by simp⟩
  mul_assoc P Q S := Subtype.ext (sa P.1 Q.2 S.2).symm
  one_mul P := Subtype.ext (PowerSeries.subst_X (hs0 P.2))
  mul_one P := Subtype.ext (PowerSeries.X_subst P.1)

theorem val_mul (P Q : CS R) : (P * Q).1 = P.1 ⊚ Q.1 := rfl

theorem val_one : (1 : CS R).1 = PowerSeries.X := rfl

/-- The linear coefficient. -/
def c1 (P : CS R) : R := PowerSeries.coeff 1 P.1

theorem c1_mul (P Q : CS R) : c1 (P * Q) = c1 P * c1 Q := coeff_one_subst_aux Q.2 P.1

theorem mul_right_cancel {Q P P' : CS R} (hQ : IsUnit (c1 Q)) (h : P * Q = P' * Q) : P = P' :=
  Subtype.ext (subst_right_cancel Q.2 hQ (congrArg Subtype.val h))

theorem exists_inv (P : CS R) (hP : IsUnit (c1 P)) : ∃ Q : CS R, P * Q = 1 ∧ Q * P = 1 :=
  ⟨⟨P.1.substInvOfIsUnit hP, PowerSeries.constantCoeff_substInvOfIsUnit P.1 hP⟩,
    Subtype.ext (PowerSeries.subst_substInvOfIsUnit_right P.1 P.2 hP),
    Subtype.ext (PowerSeries.subst_substInvOfIsUnit_left P.1 P.2 hP)⟩

theorem map_comp (ψ : R →+* S) (P Q : PowerSeries R) (hQ : PowerSeries.constantCoeff Q = 0) :
    PowerSeries.map ψ (P ⊚ Q) = (PowerSeries.map ψ P) ⊚ (PowerSeries.map ψ Q) :=
  PowerSeries.map_subst (hs0 hQ) P

/-- Applying a ring homomorphism to the coefficients. -/
def map (ψ : R →+* S) : CS R →* CS S where
  toFun P := ⟨PowerSeries.map ψ P.1, by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, P.2, map_zero]⟩
  map_one' := Subtype.ext (by simp [val_one])
  map_mul' P Q := Subtype.ext (map_comp ψ P.1 Q.1 Q.2)

theorem map_map {T : Type*} [CommRing T] (ψ : S →+* T) (φ : R →+* S) (P : CS R) :
    map ψ (map φ P) = map (ψ.comp φ) P :=
  Subtype.ext (by
    show PowerSeries.map ψ (PowerSeries.map φ P.1) = PowerSeries.map (ψ.comp φ) P.1
    ext n; simp)

theorem val_map (ψ : R →+* S) (P : CS R) : (map ψ P).1 = PowerSeries.map ψ P.1 := rfl

theorem c1_map (ψ : R →+* S) (P : CS R) : c1 (map ψ P) = ψ (c1 P) := by
  show PowerSeries.coeff 1 (PowerSeries.map ψ P.1) = ψ (PowerSeries.coeff 1 P.1)
  simp

end CS

end Monoid

section Conj

/-- The key step of Proposition 3.10: the series $h = \theta_0^\sigma \circ f \circ \theta_0^{-1}$ is fixed by
$\sigma$, when $\theta_0^\sigma = \theta_0 \circ U$ and $U$ commutes with $f$ and both are fixed by $\sigma$.
Stated without inverses: $h \circ \theta_0 = \theta_0^\sigma \circ f$. -/
theorem exists_fixed_conj {B : Type*} [CommRing B] (σ : B →+* B) (T0 U F : CS B)
    (hT0 : IsUnit (CS.c1 T0)) (hσT0 : CS.map σ T0 = T0 * U) (hσU : CS.map σ U = U)
    (hσF : CS.map σ F = F) (hUF : U * F = F * U) :
    ∃ H : CS B, H * T0 = CS.map σ T0 * F ∧ CS.map σ H = H := by
  obtain ⟨Ti, hTi, hiT⟩ := CS.exists_inv T0 hT0
  have hHT : ((CS.map σ T0 * F) * Ti) * T0 = CS.map σ T0 * F := by rw [mul_assoc, hiT, mul_one]
  refine ⟨(CS.map σ T0 * F) * Ti, hHT, ?_⟩
  have hu : IsUnit (CS.c1 (CS.map σ T0)) := by rw [CS.c1_map]; exact hT0.map σ
  refine CS.mul_right_cancel hu ?_
  calc CS.map σ ((CS.map σ T0 * F) * Ti) * CS.map σ T0
      = CS.map σ (((CS.map σ T0 * F) * Ti) * T0) := (map_mul _ _ _).symm
    _ = CS.map σ (CS.map σ T0 * F) := by rw [hHT]
    _ = CS.map σ (T0 * U) * F := by rw [map_mul, hσT0, hσF]
    _ = (CS.map σ T0 * U) * F := by rw [map_mul, hσU]
    _ = (CS.map σ T0 * F) * U := by rw [mul_assoc, hUF, ← mul_assoc]
    _ = (((CS.map σ T0 * F) * Ti) * T0) * U := by rw [hHT]
    _ = ((CS.map σ T0 * F) * Ti) * CS.map σ T0 := by rw [hσT0, ← mul_assoc]

end Conj

end NumberFieldKB.MilneCFT.LocalCFT
