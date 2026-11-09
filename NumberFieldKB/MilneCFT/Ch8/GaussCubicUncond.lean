import NumberFieldKB.MilneCFT.Ch8.LSeries
import NumberFieldKB.MilneCFT.Ch8.CubicTauCeti

/-!
# Milne, *Class Field Theory*, VIII §10: Gauss's cubic point count, unconditionally

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §10, printed
p. 263 (a theorem of Gauss, after Silverman--Tate IV.2). This file proves the named statement `GaussCubicCount` of
`LSeries.lean` (`gaussCubicCount`), with no input hypothesis. Let $p$ be a prime and
$N = \#\{(x,y,z) \in \mathbb F_p^3 : x^3+y^3+z^3 = 0\}$ (`nsol`), so `cubicAffineCount p = N - 1`
(`cubicAffineCount_add_one`).

* **Case $p \not\equiv 1 \pmod 3$** (`count_not_one`). Then $x \mapsto x^3$ is a bijection of $\mathbb F_p$
  (`exists_cube_inverse`, `cnt_eq_one`: $x^{3m} = x$ for $m = (2p-1)/3$, or $m = 1$ for $p = 3$), so the solutions biject
  with those of $u+v+w = 0$: $N = p^2$.
* **Case $p \equiv 1 \pmod 3$** (`count_one`). Let $\chi$ be a character of $\mathbb F_p^\times$ of order $3$ with
  values in $\mathcal O_K = \mathbb Z[\omega]$, $K = \mathbb Q(\zeta_3)$. The number of cube roots of $a$ is
  $1 + \chi(a) + \chi^2(a)$ (`cnt_eq`; for $a$ a nonzero non-cube it uses that $\chi(a) \ne 1$, via a generator of
  $\mathbb F_p^\times$). Writing $\sum_{u+v+w=0} \varphi_1(u)\varphi_2(v)\varphi_3(w)$ as `S`, expanding the
  product and using orthogonality gives (`nsol_eq`)
  $$N = p^2 + (p-1)\bigl(J(\chi,\chi) + J(\chi^2,\chi^2)\bigr),$$
  because the mixed terms vanish by scaling (`S_eq_zero`) and the diagonal ones are $(p-1)J$ (`S_diag`). Write
  $J(\chi,\chi) = a + b\omega$. Tau Ceti's `isPrimaryEisenstein_jacobiSum` gives $a \equiv 2$, $b \equiv 0 \pmod 3$
  (so $b = 3B$); $J(\chi^2,\chi^2) = \bar J$ (`CubicTC.conj`), and $J \bar J = p$ (Mathlib's
  `jacobiSum_mul_jacobiSum_inv`) gives $a^2 - ab + b^2 = p$. Hence with $A = 2a - b = J + \bar J$ one has
  $A \equiv 1 \pmod 3$, $4p = A^2 + 27B^2$ and $N - 1 = (p-1)(p+1+A)$.
* **Uniqueness of $A$** (`uniq`, elementary). If $4p = A^2+27B^2 = A'^2+27B'^2$ with $A \equiv A' \equiv 1 \pmod 3$,
  then $p$ divides $(AB'-A'B)(AB'+A'B) = 4p(B'^2-B^2)$; as $16p^2 = (AA' \pm 27BB')^2 + 27(AB' \mp A'B)^2$, the factor
  divisible by $p$ is $0$, whence $A' = \pm A$, and the congruence mod $3$ forces $A' = A$.
-/

open NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

namespace GaussCubic

section Sums

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

/-- The sum `Σ_{u+v+w=0} f(u) g(v) h(w)`, with `w = -u-v` eliminated. -/
def S (f g h : ZMod p → R) : R := ∑ u, ∑ v, f u * g v * h (-u - v)

theorem S_add_left (f₁ f₂ g h : ZMod p → R) :
    S (fun u => f₁ u + f₂ u) g h = S f₁ g h + S f₂ g h := by
  simp only [S, add_mul, Finset.sum_add_distrib]

theorem S_add_mid (f g₁ g₂ h : ZMod p → R) :
    S f (fun u => g₁ u + g₂ u) h = S f g₁ h + S f g₂ h := by
  simp only [S, add_mul, mul_add, Finset.sum_add_distrib]

theorem S_add_right (f g h₁ h₂ : ZMod p → R) :
    S f g (fun u => h₁ u + h₂ u) = S f g h₁ + S f g h₂ := by
  simp only [S, mul_add, Finset.sum_add_distrib]

theorem S_one_right (f g : ZMod p → R) : S f g (fun _ => 1) = (∑ u, f u) * ∑ v, g v := by
  simp only [S, mul_one, Finset.sum_mul_sum]

theorem S_one_mid (f h : ZMod p → R) : S f (fun _ => 1) h = (∑ u, f u) * ∑ v, h v := by
  simp only [S, mul_one, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact (Equiv.subLeft (-u)).sum_comp h

theorem S_one_left (g h : ZMod p → R) : S (fun _ => 1) g h = (∑ u, g u) * ∑ v, h v := by
  simp only [S, one_mul]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact ((Equiv.neg _).trans (Equiv.subRight v)).sum_comp h

theorem S_scale (f g h : ZMod p → R) {l : ZMod p} (hl : l ≠ 0) :
    S (fun u => f (l * u)) (fun u => g (l * u)) (fun u => h (l * u)) = S f g h := by
  unfold S
  refine Fintype.sum_equiv (Equiv.mulLeft₀ l hl) _ _ fun u => ?_
  refine Fintype.sum_equiv (Equiv.mulLeft₀ l hl) _ _ fun v => ?_
  show f (l * u) * g (l * v) * h (l * (-u - v)) = f (l * u) * g (l * v) * h (-(l * u) - l * v)
  rw [show l * (-u - v) = -(l * u) - l * v by ring]

/-- A sum `S χ₁ χ₂ χ₃` vanishes when the product `χ₁ χ₂ χ₃` is a nontrivial character. -/
theorem S_eq_zero [IsDomain R] (χ₁ χ₂ χ₃ : MulChar (ZMod p) R) (h : χ₁ * χ₂ * χ₃ ≠ 1) :
    S (fun u => χ₁ u) (fun u => χ₂ u) (fun u => χ₃ u) = 0 := by
  obtain ⟨l, hl⟩ := MulChar.ne_one_iff.mp h
  have hl0 : (l : ZMod p) ≠ 0 := l.ne_zero
  have key := S_scale (fun u => χ₁ u) (fun u => χ₂ u) (fun u => χ₃ u) hl0
  have e : S (fun u => χ₁ ((l : ZMod p) * u)) (fun u => χ₂ ((l : ZMod p) * u))
      (fun u => χ₃ ((l : ZMod p) * u)) =
      (χ₁ * χ₂ * χ₃) l * S (fun u => χ₁ u) (fun u => χ₂ u) (fun u => χ₃ u) := by
    unfold S
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [map_mul, MulChar.coeToFun_mul, Pi.mul_apply]
    ring
  rw [e] at key
  have : (1 - (χ₁ * χ₂ * χ₃) l) * S (fun u => χ₁ u) (fun u => χ₂ u) (fun u => χ₃ u) = 0 := by
    linear_combination -key
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hl
  · exact h0

/-- For a cubic character `χ`, the "diagonal" sum is `(p-1) J(χ,χ)`. -/
theorem S_diag [IsDomain R] (χ : MulChar (ZMod p) R) (hχ : χ ^ 3 = 1) :
    S (fun u => χ u) (fun u => χ u) (fun u => χ u) = ((p : R) - 1) * jacobiSum χ χ := by
  have hneg : χ (-1) = 1 := χ.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) hχ
  have hcube : ∀ t : ZMod p, t ≠ 0 → χ t ^ 3 = 1 := by
    intro t ht
    have := congrArg (fun ψ : MulChar (ZMod p) R => ψ t) hχ
    rw [MulChar.pow_apply' χ (by norm_num : (3 : ℕ) ≠ 0), MulChar.one_apply ht.isUnit] at this
    exact this
  unfold S
  have h1 : ∀ u : ZMod p, ∑ v, χ u * χ v * χ (-u - v) = ∑ t, χ u * χ (t - u) * χ (-t) :=
    fun u => (Fintype.sum_equiv (Equiv.subRight u) _ _ fun t => by
      show χ u * χ (t - u) * χ (-t) = χ u * χ (t - u) * χ (-u - (t - u))
      rw [show -u - (t - u) = -t by ring]).symm
  rw [Finset.sum_congr rfl fun u _ => h1 u, Finset.sum_comm]
  have h2 : ∀ t : ZMod p, ∑ u, χ u * χ (t - u) * χ (-t) =
      (if t = 0 then 0 else jacobiSum χ χ) := by
    intro t
    by_cases ht : t = 0
    · subst ht; simp only [neg_zero, MulChar.map_zero, mul_zero, Finset.sum_const_zero, ↓reduceIte]
    · simp only [ht, ↓reduceIte]
      calc ∑ u, χ u * χ (t - u) * χ (-t)
          = (∑ s, χ (t * s) * χ (t - t * s)) * χ (-t) := by
            rw [← Finset.sum_mul]
            congr 1
            exact (Equiv.sum_comp (Equiv.mulLeft₀ t ht) (fun u => χ u * χ (t - u))).symm
        _ = (∑ s, χ t ^ 2 * (χ s * χ (1 - s))) * χ (-t) := by
            congr 1
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [show t - t * s = t * (1 - s) by ring, map_mul, map_mul]
            ring
        _ = χ t ^ 3 * χ (-1) * jacobiSum χ χ := by
            rw [← Finset.mul_sum, show -t = -1 * t by ring, map_mul]
            unfold jacobiSum
            ring
        _ = jacobiSum χ χ := by rw [hcube t ht, hneg]; ring
  rw [Finset.sum_congr rfl fun t _ => h2 t]
  have h3 : ∀ t : ZMod p, (if t = 0 then (0 : R) else jacobiSum χ χ) =
      jacobiSum χ χ - if t = 0 then jacobiSum χ χ else 0 := by
    intro t; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun t _ => h3 t, Finset.sum_sub_distrib]
  simp [ZMod.card, sub_mul]

end Sums

section Counting

variable {p : ℕ} [Fact p.Prime]

/-- The number of cube roots of `a` in `𝔽_p`. -/
def cnt (p : ℕ) [Fact p.Prime] (a : ZMod p) : ℕ :=
  (Finset.univ.filter fun x : ZMod p => x ^ 3 = a).card

theorem cnt_zero : cnt p 0 = 1 := by
  unfold cnt
  rw [Finset.card_eq_one]
  exact ⟨0, by ext x; simp [pow_eq_zero_iff]⟩

theorem cnt_of_not_cube {a : ZMod p} (h : ¬ ∃ α : ZMod p, α ^ 3 = a) : cnt p a = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun x _ hx => h ⟨x, hx⟩

theorem cnt_of_cube (h3 : 3 ∣ p - 1) {a : ZMod p} (ha0 : a ≠ 0) (ha : ∃ α : ZMod p, α ^ 3 = a) :
    cnt p a = 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rwa [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 hcard
  have hζ : IsPrimitiveRoot (g : ZMod p) 3 := by
    exact IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hg)
  have hnodup := hζ.nthRoots_nodup ha0
  have hc := hζ.card_nthRoots a
  simp only [ha, ↓reduceIte] at hc
  have : (Finset.univ.filter fun x : ZMod p => x ^ 3 = a) = (Polynomial.nthRoots 3 a).toFinset := by
    ext x
    simp [Polynomial.mem_nthRoots (by norm_num : 0 < 3)]
  unfold cnt
  rw [this, Multiset.toFinset_card_of_nodup hnodup, hc]

/-- The number of cube roots of `a` is `1 + χ(a) + χ²(a)` for a cubic character `χ`. -/
theorem cnt_eq {R : Type*} [CommRing R] [IsDomain R] (χ : MulChar (ZMod p) R)
    (hχ : orderOf χ = 3) (a : ZMod p) : (cnt p a : R) = 1 + χ a + (χ ^ 2) a := by
  classical
  have h3 : 3 ∣ p - 1 := by
    have := χ.orderOf_dvd_card_sub_one
    rwa [hχ, ZMod.card] at this
  have hχ3 : χ ^ 3 = 1 := hχ ▸ pow_orderOf_eq_one χ
  have hcube : ∀ t : ZMod p, t ≠ 0 → χ t ^ 3 = 1 := by
    intro t ht
    have := congrArg (fun ψ : MulChar (ZMod p) R => ψ t) hχ3
    rw [MulChar.pow_apply' χ (by norm_num : (3 : ℕ) ≠ 0), MulChar.one_apply ht.isUnit] at this
    exact this
  rw [MulChar.pow_apply' χ (by norm_num : (2 : ℕ) ≠ 0)]
  by_cases ha : a = 0
  · subst ha
    simp [cnt_zero, MulChar.map_zero]
  by_cases hcb : ∃ α : ZMod p, α ^ 3 = a
  · obtain ⟨α, rfl⟩ := hcb
    have hα : α ≠ 0 := fun h => ha (by simp [h])
    have h1 : χ (α ^ 3) = 1 := by rw [map_pow]; exact hcube α hα
    rw [cnt_of_cube h3 ha ⟨α, rfl⟩, h1]
    norm_num
  · rw [cnt_of_not_cube hcb]
    -- `χ a ≠ 1`, because `a` is not a cube
    have hne : χ a ≠ 1 := by
      intro h1
      apply hcb
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 a ha))
      have hω : χ.toUnitHom g ≠ 1 := by
        intro hω
        have : χ = 1 := by
          refine MulChar.ext fun u => ?_
          obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
          have h6 : χ.toUnitHom u = 1 := by rw [← hj, map_zpow, hω, one_zpow]
          rw [← MulChar.coe_toUnitHom, h6, MulChar.one_apply_coe]
          rfl
        rw [this] at hχ
        simp at hχ
      have hord : orderOf (χ.toUnitHom g) = 3 := by
        refine orderOf_eq_prime ?_ hω
        ext
        rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom]
        exact hcube g g.ne_zero
      have hk1 : (χ.toUnitHom g) ^ k = 1 := by
        rw [← map_zpow, hk]
        ext
        rw [MulChar.coe_toUnitHom]
        simpa using h1
      have hdvd : ((3 : ℕ) : ℤ) ∣ k := by
        have := orderOf_dvd_iff_zpow_eq_one.mpr hk1
        rwa [hord] at this
      obtain ⟨m, hm⟩ := hdvd
      refine ⟨((g ^ m : (ZMod p)ˣ) : ZMod p), ?_⟩
      have h4 : (g ^ m) ^ 3 = Units.mk0 a ha := by
        rw [← zpow_natCast, ← zpow_mul, show m * ((3 : ℕ) : ℤ) = k by rw [hm]; ring, hk]
      have h5 := congrArg Units.val h4
      simpa using h5
    have h3 := hcube a ha
    have : (χ a - 1) * (1 + χ a + χ a ^ 2) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · simp only [Nat.cast_zero]; linear_combination -h

end Counting

section Total

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

/-- The number of solutions `(x, y, z) ∈ 𝔽_p³` of `x³ + y³ + z³ = 0`, zero included. -/
def nsol (p : ℕ) [Fact p.Prime] : ℕ :=
  (Finset.univ.filter fun v : Fin 3 → ZMod p => v 0 ^ 3 + v 1 ^ 3 + v 2 ^ 3 = 0).card

theorem cubicAffineCount_add_one : cubicAffineCount p + 1 = nsol p := by
  classical
  unfold cubicAffineCount nsol
  have : (Finset.univ.filter fun v : Fin 3 → ZMod p => v ≠ 0 ∧ v 0 ^ 3 + v 1 ^ 3 + v 2 ^ 3 = 0) =
      (Finset.univ.filter fun v : Fin 3 → ZMod p => v 0 ^ 3 + v 1 ^ 3 + v 2 ^ 3 = 0).erase 0 := by
    ext v
    simp [and_comm]
  rw [this]
  exact Finset.card_erase_add_one (by simp)

theorem sum_cube (g : ZMod p → R) : ∑ x : ZMod p, g (x ^ 3) = ∑ u, (cnt p u : R) * g u := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun x : ZMod p => x ^ 3) (fun x => g (x ^ 3))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2] : ∀ x ∈ Finset.univ.filter
    (fun x : ZMod p => x ^ 3 = u), g (x ^ 3) = g u)]
  simp [cnt]

theorem nsol_cast : (nsol p : R) = S (fun u => (cnt p u : R)) (fun u => (cnt p u : R))
    (fun u => (cnt p u : R)) := by
  classical
  let e : ZMod p × ZMod p × ZMod p ≃ (Fin 3 → ZMod p) :=
    { toFun := fun t => ![t.1, t.2.1, t.2.2]
      invFun := fun v => (v 0, v 1, v 2)
      left_inv := fun t => rfl
      right_inv := fun v => by funext i; fin_cases i <;> rfl }
  have h1 : (nsol p : R) = ∑ x : ZMod p, ∑ y : ZMod p, ∑ z : ZMod p,
      if x ^ 3 + y ^ 3 + z ^ 3 = 0 then (1 : R) else 0 := by
    unfold nsol
    rw [Finset.card_filter, Nat.cast_sum]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type]
    rfl
  have step1 : ∀ a b : ZMod p, ∑ z : ZMod p, (if a + b + z ^ 3 = 0 then (1 : R) else 0) =
      cnt p (-a - b) := by
    intro a b
    rw [sum_cube (fun w => if a + b + w = 0 then (1 : R) else 0)]
    rw [Finset.sum_eq_single (-a - b)]
    · simp
    · intro w _ hw
      have : ¬ (a + b + w = 0) := fun h => hw (by linear_combination h)
      simp [this]
    · simp
  rw [h1]
  simp only [step1]
  unfold S
  have h2 : ∀ x : ZMod p, ∑ y : ZMod p, (cnt p (-x ^ 3 - y ^ 3) : R) =
      ∑ v, (cnt p v : R) * (cnt p (-x ^ 3 - v) : R) :=
    fun x => sum_cube (fun v => (cnt p (-x ^ 3 - v) : R))
  rw [Finset.sum_congr rfl fun x _ => h2 x,
    sum_cube (fun u => ∑ v : ZMod p, (cnt p v : R) * (cnt p (-u - v) : R))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

/-- **The point count through Jacobi sums**: for a character `χ` of order `3` with values in a domain,
`#{(x,y,z) : x³+y³+z³ = 0} = p² + (p-1)(J(χ,χ) + J(χ²,χ²))`. -/
theorem nsol_eq [IsDomain R] (χ : MulChar (ZMod p) R) (hχ : orderOf χ = 3) :
    (nsol p : R) = (p : R) ^ 2 +
      ((p : R) - 1) * (jacobiSum χ χ + jacobiSum (χ ^ 2) (χ ^ 2)) := by
  have hχ3 : χ ^ 3 = 1 := hχ ▸ pow_orderOf_eq_one χ
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    simp at hχ
  have hχ2 : χ ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hχ] at this
    omega
  have hsum1 : ∑ u, χ u = 0 := MulChar.sum_eq_zero_of_ne_one hχ1
  have hsum2 : ∑ u, (χ ^ 2) u = 0 := MulChar.sum_eq_zero_of_ne_one hχ2
  have hψ : ∑ u : ZMod p, (χ u + (χ ^ 2) u) = 0 := by
    rw [Finset.sum_add_distrib, hsum1, hsum2, add_zero]
  have hc : (fun u => (cnt p u : R)) = fun u => (1 : R) + (χ u + (χ ^ 2) u) := by
    funext u; rw [cnt_eq χ hχ u]; ring
  have hsc : ∑ u : ZMod p, ((1 : R) + (χ u + (χ ^ 2) u)) = p := by
    rw [Finset.sum_add_distrib, hψ]; simp
  rw [nsol_cast, hc]
  rw [S_add_left (fun _ => (1 : R)), S_one_left]
  rw [S_add_mid (fun u => χ u + (χ ^ 2) u) (fun _ => (1 : R)), S_one_mid]
  rw [S_add_right (fun u => χ u + (χ ^ 2) u) (fun u => χ u + (χ ^ 2) u) (fun _ => (1 : R)),
    S_one_right]
  simp only [hsc, hψ, mul_zero, zero_mul]
  simp only [S_add_left, S_add_mid, S_add_right]
  have e1 : χ * χ * χ ^ 2 ≠ 1 := by
    rwa [show χ * χ * χ ^ 2 = χ ^ 3 * χ by group, hχ3, one_mul]
  have e2 : χ * χ ^ 2 * χ ≠ 1 := by
    rwa [show χ * χ ^ 2 * χ = χ ^ 3 * χ by group, hχ3, one_mul]
  have e3 : χ ^ 2 * χ * χ ≠ 1 := by
    rwa [show χ ^ 2 * χ * χ = χ ^ 3 * χ by group, hχ3, one_mul]
  have e4 : χ * χ ^ 2 * χ ^ 2 ≠ 1 := by
    rwa [show χ * χ ^ 2 * χ ^ 2 = χ ^ 3 * χ ^ 2 by group, hχ3, one_mul]
  have e5 : χ ^ 2 * χ * χ ^ 2 ≠ 1 := by
    rwa [show χ ^ 2 * χ * χ ^ 2 = χ ^ 3 * χ ^ 2 by group, hχ3, one_mul]
  have e6 : χ ^ 2 * χ ^ 2 * χ ≠ 1 := by
    rwa [show χ ^ 2 * χ ^ 2 * χ = χ ^ 3 * χ ^ 2 by group, hχ3, one_mul]
  have hχ23 : (χ ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hχ3, one_pow]
  rw [S_eq_zero _ _ _ e1, S_eq_zero _ _ _ e2, S_eq_zero _ _ _ e3, S_eq_zero _ _ _ e4,
    S_eq_zero _ _ _ e5, S_eq_zero _ _ _ e6, S_diag χ hχ3, S_diag (χ ^ 2) hχ23]
  ring

end Total

section NotOne

variable {p : ℕ} [Fact p.Prime]

/-- For `p = 3` or `p ≡ 2 (mod 3)`, `x ↦ x³` is a bijection of `𝔽_p`; here is an explicit inverse
exponent: `x ^ (3 m) = x`. -/
theorem exists_cube_inverse (h : p % 3 ≠ 1) : ∃ m : ℕ, 0 < m ∧ ∀ x : ZMod p, x ^ (3 * m) = x := by
  have hp := (Fact.out : p.Prime)
  by_cases hp3 : p = 3
  · subst hp3
    exact ⟨1, one_pos, fun x => by simp⟩
  · have hp2 : p % 3 = 2 := by
      have : p % 3 ≠ 0 := fun h0 => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm
      omega
    refine ⟨(2 * p - 1) / 3, ?_, fun x => ?_⟩
    · have := hp.two_le
      omega
    · have h3 : 3 * ((2 * p - 1) / 3) = 2 * p - 1 := by
        have := hp.two_le
        omega
      rw [h3]
      by_cases hx : x = 0
      · subst hx
        have := hp.two_le
        exact zero_pow (by omega)
      · have : 2 * p - 1 = p + (p - 1) := by
          have := hp.two_le
          omega
        rw [this, pow_add, ZMod.pow_card, ZMod.pow_card_sub_one_eq_one hx, mul_one]

theorem cnt_eq_one (h : p % 3 ≠ 1) (u : ZMod p) : cnt p u = 1 := by
  obtain ⟨m, hm, hx⟩ := exists_cube_inverse (p := p) h
  unfold cnt
  rw [Finset.card_eq_one]
  refine ⟨u ^ m, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro rfl
    rw [← pow_mul, hx]
  · rintro rfl
    rw [← pow_mul, mul_comm, hx]

/-- **Gauss's theorem, case (a)**: `p = 3` or `p ≡ 2 (mod 3)`. -/
theorem count_not_one (h : p % 3 ≠ 1) : cubicAffineCount p = (p - 1) * (p + 1) := by
  have h1 : (nsol p : ℤ) = (p : ℤ) ^ 2 := by
    rw [nsol_cast]
    unfold S
    simp [cnt_eq_one h, sq]
  have h2 := cubicAffineCount_add_one (p := p)
  have hp1 := (Fact.out : p.Prime).one_lt
  have h3 : (cubicAffineCount p : ℤ) + 1 = (p : ℤ) ^ 2 := by
    rw [← h1, ← h2]; push_cast; ring
  zify [hp1.le]
  linear_combination h3

end NotOne

section Uniqueness

/-- If `D = 0` and `E² = 16 p²`, `4 p A' = A E`, then `A' = ± A`; combined with the congruences
mod 3 this gives `A' = A`. -/
theorem uniq_aux {p A A' E : ℤ} (hp : 0 < p) (hA : A % 3 = 1) (hA' : A' % 3 = 1)
    (hE : E ^ 2 = 16 * p ^ 2) (h : 4 * p * A' = A * E) : A' = A := by
  have h4 : (E - 4 * p) * (E + 4 * p) = 0 := by linear_combination hE
  rcases mul_eq_zero.mp h4 with h5 | h5
  · have : E = 4 * p := by linarith
    subst this
    have : 4 * p * (A' - A) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h6 | h6
    · omega
    · linarith
  · have : E = -(4 * p) := by linarith
    subst this
    have : 4 * p * (A' + A) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h6 | h6
    · omega
    · omega

/-- **Uniqueness of `A`** in `4 p = A² + 27 B²` with `A ≡ 1 (mod 3)`. -/
theorem uniq {p : ℕ} (hp : p.Prime) {A B A' B' : ℤ} (hA : A % 3 = 1) (hA' : A' % 3 = 1)
    (h : 4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2) (h' : 4 * (p : ℤ) = A' ^ 2 + 27 * B' ^ 2) :
    A' = A := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hprod : (A * B' - A' * B) * (A * B' + A' * B) = p * (4 * (B' ^ 2 - B ^ 2)) := by
    have e1 : A ^ 2 = 4 * p - 27 * B ^ 2 := by linarith
    have e2 : A' ^ 2 = 4 * p - 27 * B' ^ 2 := by linarith
    calc (A * B' - A' * B) * (A * B' + A' * B) = A ^ 2 * B' ^ 2 - A' ^ 2 * B ^ 2 := by ring
      _ = _ := by rw [e1, e2]; ring
  have hdvd : (p : ℤ) ∣ (A * B' - A' * B) * (A * B' + A' * B) := ⟨_, hprod⟩
  have h16 : (A * A' + 27 * B * B') ^ 2 + 27 * (A * B' - A' * B) ^ 2 = 16 * (p : ℤ) ^ 2 := by
    have : (A * A' + 27 * B * B') ^ 2 + 27 * (A * B' - A' * B) ^ 2 =
        (A ^ 2 + 27 * B ^ 2) * (A' ^ 2 + 27 * B' ^ 2) := by ring
    rw [this, ← h, ← h']; ring
  have h16' : (A * A' - 27 * B * B') ^ 2 + 27 * (A * B' + A' * B) ^ 2 = 16 * (p : ℤ) ^ 2 := by
    have : (A * A' - 27 * B * B') ^ 2 + 27 * (A * B' + A' * B) ^ 2 =
        (A ^ 2 + 27 * B ^ 2) * (A' ^ 2 + 27 * B' ^ 2) := by ring
    rw [this, ← h, ← h']; ring
  have small : ∀ D E : ℤ, (p : ℤ) ∣ D → E ^ 2 + 27 * D ^ 2 = 16 * (p : ℤ) ^ 2 → D = 0 := by
    intro D E hD hE
    obtain ⟨k, rfl⟩ := hD
    by_contra hk
    have hk0 : k ≠ 0 := fun h0 => hk (by simp [h0])
    have : 0 < k ^ 2 := by positivity
    have : 1 ≤ k ^ 2 := this
    nlinarith [sq_nonneg E, sq_nonneg (p : ℤ), mul_pos hp0 hp0]
  rcases hpz.dvd_or_dvd hdvd with hD | hD
  · have hD0 := small _ _ hD h16
    have hE : (A * A' + 27 * B * B') ^ 2 = 16 * (p : ℤ) ^ 2 := by
      rw [hD0] at h16; linarith
    refine uniq_aux hp0 hA hA' hE ?_
    have : A * B' = A' * B := by linarith
    linear_combination A' * h - 27 * B * this
  · have hD0 := small _ _ hD h16'
    have hE : (A * A' - 27 * B * B') ^ 2 = 16 * (p : ℤ) ^ 2 := by
      rw [hD0] at h16'; linarith
    refine uniq_aux hp0 hA hA' hE ?_
    have : A * B' = -(A' * B) := by linarith
    linear_combination A' * h + 27 * B * this

end Uniqueness

section One

open TauCeti Ideal CubicTC

variable {p : ℕ} [Fact p.Prime]

/-- **Gauss's theorem, case (b)**: `p ≡ 1 (mod 3)`. -/
theorem count_one (hp : p % 3 = 1) : ∃ A B : ℤ, A % 3 = 1 ∧ 4 * (p : ℤ) = A ^ 2 + 27 * B ^ 2 ∧
    (cubicAffineCount p : ℤ) = ((p : ℤ) - 1) * ((p : ℤ) + 1 + A) ∧
    ∀ A' B' : ℤ, A' % 3 = 1 → 4 * (p : ℤ) = A' ^ 2 + 27 * B' ^ 2 → A' = A := by
  have hpp := (Fact.out : p.Prime)
  let K := CyclotomicField 3 ℚ
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hω : IsPrimitiveRoot hζ.toInteger 3 := hζ.toInteger_isPrimitiveRoot
  have h3 : 3 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf (ZMod p) h3 hω
  have hχ3 : χ ^ 3 = 1 := by
    have := pow_orderOf_eq_one χ
    rwa [hχ] at this
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    simp at hχ
  have hχ2 : χ * χ ≠ 1 := by
    intro h
    have := Nat.le_of_dvd two_pos (hχ ▸ orderOf_dvd_of_pow_eq_one (by rwa [sq]))
    omega
  have hN := nsol_eq (R := 𝓞 K) χ hχ
  -- the cubic Jacobi sum is primary
  have hprim := isPrimaryEisenstein_jacobiSum hχ
  obtain ⟨a, b, hJ, hJc⟩ := conj_eq (jacobiSum χ χ)
  have hab : a ≡ 2 [ZMOD 3] ∧ b ≡ 0 [ZMOD 3] := by
    rw [hJ, hζ.isPrimaryEisenstein_add_mul_iff] at hprim
    exact hprim
  -- `χ² = χ⁻¹` is `χ` composed with the conjugation
  have hinv : χ⁻¹ = χ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hχ3)
  have hcube : ∀ u : (ZMod p)ˣ, χ u ^ 3 = 1 := by
    intro u
    have := congrArg (fun ψ : MulChar (ZMod p) (𝓞 K) => ψ u) hχ3
    rwa [MulChar.pow_apply_coe, MulChar.one_apply_coe] at this
  have hχc : χ⁻¹ = χ.ringHomComp (conj (K := K)).toRingHom := by
    refine MulChar.ext fun u => ?_
    rw [MulChar.ringHomComp_apply]
    show χ⁻¹ u = conj (χ u)
    rw [conj_pow_two (hcube u), hinv, MulChar.pow_apply_coe]
  have hconj : jacobiSum (χ ^ 2) (χ ^ 2) = conj (jacobiSum χ χ) := by
    rw [← hinv, hχc, jacobiSum_ringHomComp]
    rfl
  -- the product of the two conjugate Jacobi sums is `p`
  have hprod : jacobiSum χ χ * conj (jacobiSum χ χ) = (p : 𝓞 K) := by
    classical
    have hchar : ringChar K ≠ ringChar (ZMod p) := by
      rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]
      exact hpp.ne_zero.symm
    have hinj := RingOfIntegers.coe_injective (K := K)
    have h1K : χ.ringHomComp (algebraMap (𝓞 K) K) ≠ 1 :=
      (MulChar.ringHomComp_ne_one_iff hinj).mpr hχ1
    have h2K : χ.ringHomComp (algebraMap (𝓞 K) K) * χ.ringHomComp (algebraMap (𝓞 K) K) ≠ 1 := by
      rwa [← MulChar.ringHomComp_mul, MulChar.ringHomComp_ne_one_iff hinj]
    have key := jacobiSum_mul_jacobiSum_inv hchar h1K h1K h2K
    rw [← hconj, ← hinv]
    apply hinj
    simpa [MulChar.ringHomComp_inv, jacobiSum_ringHomComp, ZMod.card] using key
  obtain ⟨n, hn1, hn2⟩ := mul_conj (jacobiSum χ χ)
  have hn : a ^ 2 - a * b + b ^ 2 = (p : ℤ) := by
    have e1 : n = a ^ 2 - a * b + b ^ 2 := by
      rw [← hn2, hJ]
      exact hζ.norm_intCast_add_intCast_mul_toInteger_of_three a b
    have e2 : ((n : ℤ) : 𝓞 K) = (((p : ℤ)) : 𝓞 K) := by
      rw [← hn1, hprod]; simp
    rw [← e1]
    exact Int.cast_injective e2
  have h2 : hζ.toInteger ^ 2 = -hζ.toInteger - 1 := IsCyclotomicExtension.Rat.Three.eta_sq hζ
  have hsum : jacobiSum χ χ + jacobiSum (χ ^ 2) (χ ^ 2) = ((2 * a - b : ℤ) : 𝓞 K) := by
    rw [hconj, hJc]
    nth_rewrite 1 [hJ]
    rw [h2]
    push_cast
    ring
  rw [hsum] at hN
  push_cast at hN
  have hNz : (nsol p : ℤ) = (p : ℤ) ^ 2 + ((p : ℤ) - 1) * (2 * a - b) := by
    apply Int.cast_injective (α := 𝓞 K)
    push_cast
    exact hN
  obtain ⟨B, rfl⟩ : (3 : ℤ) ∣ b := Int.modEq_zero_iff_dvd.mp hab.2
  have ha : a % 3 = 2 := hab.1
  have hcount : (cubicAffineCount p : ℤ) + 1 = nsol p := by exact_mod_cast cubicAffineCount_add_one (p := p)
  refine ⟨2 * a - 3 * B, B, by omega, by linear_combination (-4 : ℤ) * hn, ?_,
    fun A' B' hA' hAB' => uniq hpp (B := B) (by omega) hA' (by linear_combination (-4 : ℤ) * hn) hAB'⟩
  linear_combination hcount + hNz

end One

end GaussCubic

/-- **A theorem of Gauss** (Milne, *CFT*, VIII, §10, p. 263): the point count of $X^3+Y^3+Z^3 = 0$ over $\mathbb F_p$,
proved without hypotheses (see the module docstring). -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 263 (a theorem of Gauss)"]
theorem gaussCubicCount : GaussCubicCount where
  not_one := fun _ _ h => GaussCubic.count_not_one h
  one := fun _ _ h => GaussCubic.count_one h

end NumberFieldKB.MilneCFT.Ch8
