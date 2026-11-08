import NumberFieldKB.MilneCFT.Ch8.ExplicitPairingSteinberg

/-!
# Prop. VIII.5.12 on the generators, with "pairs trivially" in place of "is a $p$-th power"

Variant of `IsSteinbergPairing.cond_c_eta` and `IsSteinbergPairing.isExplicitPairing` (ExplicitPairingSteinberg.lean)
for a Steinberg pairing on a field $K$ for which the $\eta_k$, $k \ge p + 1$, pair trivially with everything, without
being $p$-th powers in $K$. This is the situation of a global symbol $(\cdot,\cdot)_\lambda$ on $\mathbb Q(\zeta_p)^\times$:
the $\eta_k$ with $k \ge p+1$ are $p$-th powers only in the completion $K_\lambda$ (Milne, *CFT*, VIII, p. 248).
-/

namespace NumberFieldKB.MilneCFT.Ch8

namespace IsSteinbergPairing

variable {K M : Type*} [Field K] [CommGroup M] {P : Kˣ →* Kˣ →* M} {p : ℕ}

/-- (c) on the generators, assuming the $\eta_k$ ($k \ge p+1$) pair trivially on both sides. -/
theorem cond_c_eta_of_triv (hP : IsSteinbergPairing P p) {lam : Kˣ} {eta : ℕ → Kˣ}
    (heta : ∀ i, 1 ≤ i → (eta i : K) = 1 - (lam : K) ^ i) (hp : Odd p)
    (htriv : ∀ k, p + 1 ≤ k → ∀ x, P (eta k) x = 1 ∧ P x (eta k) = 1) (i j : ℕ) (hi : 1 ≤ i)
    (hj : 1 ≤ j) (hij : p + 1 ≤ i + j) : P (eta i) (eta j) = 1 := by
  rw [hP.cond_a heta hp i j hi hj, (htriv _ hij _).2, (htriv _ hij _).1, (htriv _ hij _).1]
  simp

/-- Every Steinberg pairing for which the $\eta_k$ ($k \ge p+1$) pair trivially satisfies `IsExplicitPairing` with
$z = (\eta_p, \lambda)$ ($p$ an odd prime). -/
theorem isExplicitPairing_of_triv (hP : IsSteinbergPairing P p) {lam : Kˣ} {eta : ℕ → Kˣ}
    (heta : ∀ i, 1 ≤ i → (eta i : K) = 1 - (lam : K) ^ i) (hp : p.Prime) (hp2 : p ≠ 2)
    (htriv : ∀ k, p + 1 ≤ k → ∀ x, P (eta k) x = 1 ∧ P x (eta k) = 1) :
    IsExplicitPairing P p lam eta (P (eta p) lam) (fun i _ => i) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  exact
    { skew := hP.skew
      lam_lam := hP.self_eq_one hodd lam
      a := fun i j hi hj => hP.cond_a heta hodd i j hi hj
      b_lt := fun i hi hip => hP.cond_b_lt heta hp i hi hip
      b_eq := rfl
      c_eta := fun i j hi hj hij => hP.cond_c_eta_of_triv heta hodd htriv i j hi hj hij
      c_lam := fun i hi => (htriv i hi lam).1 }

/-- **$(\eta_p, \lambda) = (\zeta, \eta_{p-1})$** with $\zeta = \eta_1 = 1 - \lambda$ ($p$ odd, $\eta_k$ trivial for
$k \ge p + 1$): condition (a) with $i = 1$, $j = p - 1$ and (c). This reduces Milne's normalization
$(\eta_p, \lambda) = \zeta$ to the value of $(\zeta, 1 - \lambda^{p-1})$. -/
theorem eta_p_lam_eq (hP : IsSteinbergPairing P p) {lam : Kˣ} {eta : ℕ → Kˣ}
    (heta : ∀ i, 1 ≤ i → (eta i : K) = 1 - (lam : K) ^ i) (hp : Odd p) (hp1 : 2 ≤ p)
    (htriv : ∀ k, p + 1 ≤ k → ∀ x, P (eta k) x = 1 ∧ P x (eta k) = 1) :
    P (eta p) lam = P (eta 1) (eta (p - 1)) := by
  have h := hP.cond_a heta hp 1 (p - 1) le_rfl (by omega)
  rw [show 1 + (p - 1) = p by omega, pow_one] at h
  rw [h, hP.cond_c_eta_of_triv heta hp htriv 1 p le_rfl (by omega) (by omega),
    hP.cond_c_eta_of_triv heta hp htriv p (p - 1) (by omega) (by omega) (by omega)]
  simp

end IsSteinbergPairing

end NumberFieldKB.MilneCFT.Ch8
