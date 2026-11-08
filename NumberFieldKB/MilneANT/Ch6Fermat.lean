import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Chapter 6: the first case of Fermat's last theorem for regular primes

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers.

* **Regular prime** (prose definition, p. 101; `IsRegularPrime`): an odd prime $p$ that does not divide the class
  number of $\mathbb Q[\zeta_p]$.
* **Lemma 6.9** (`lemma_6_9`): under the hypotheses of the proof of Theorem 6.8, the elements $x + \zeta^i y$
  ($0 \le i \le p-1$) of $\mathbb Z[\zeta]$ are relatively prime in pairs.
* **Lemma 6.10** (`lemma_6_10`): for every $\alpha \in \mathbb Z[\zeta]$, $\alpha^p \in \mathbb Z + p\mathbb Z[\zeta]$.
* **Lemma 6.11** (`lemma_6_11`): if $\alpha = \sum_{i=0}^{p-1} a_i\zeta^i$ with $a_i \in \mathbb Z$ and at least one
  $a_i = 0$ is divisible by an integer $n$ in $\mathbb Z[\zeta]$, then $n \mid a_i$ for all $i$.
* **Theorem 6.8**: see `Ch6FermatThm.lean`.

Throughout, $\zeta$ is a primitive $p$th root of $1$ in a field $K$ with `IsCyclotomicExtension {p} ℚ K`, and Milne's
ring $\mathbb Z[\zeta]$ is the ring of integers $\mathcal O_K$ (Proposition 6.2(b), Mathlib's
`IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime`); `hζ.toInteger` is $\zeta$ as an element of
$\mathcal O_K$. Theorem 6.8 is stated for Mathlib's `CyclotomicField p ℚ`.
-/

open NumberField Polynomial

namespace NumberFieldKB.MilneANT

/-- **Regular prime** (Milne's prose definition, p. 101). A prime $p$ is *regular* if $p$ does not divide the class
number of $\mathbb Q[\zeta]$, $\zeta$ a primitive $p$th root of $1$ (Milne: "primes $p$ such that $p$ does not
divide the class number of $\mathbb Q[\zeta]$ are of particular interest. They are called regular"). Milne
introduces the notion for odd primes; the definition makes sense for every prime (and $2$ is regular, since
$\mathbb Q[\zeta_2] = \mathbb Q$). -/
@[kb "milne2020ant" "v3.08, Class numbers of cyclotomic fields (regular prime), p. 101"]
def IsRegularPrime (p : ℕ) [Fact p.Prime] : Prop :=
  ¬ p ∣ classNumber (CyclotomicField p ℚ)

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K}

/-- **Lemma 6.10.** For every $\alpha \in \mathbb Z[\zeta]$, $\alpha^p \in \mathbb Z + p\,\mathbb Z[\zeta]$: there is an
integer $a$ with $\alpha^p \equiv a \pmod{p}$. -/
@[kb "milne2020ant" "v3.08, Lemma 6.10, p. 103"]
theorem lemma_6_10 (hζ : IsPrimitiveRoot ζ p) (α : 𝓞 K) :
    ∃ a : ℤ, α ^ p - (a : 𝓞 K) ∈ Ideal.span {(p : 𝓞 K)} := by
  set pB := hζ.integralPowerBasis with hpB
  have hgen : pB.gen = hζ.toInteger := by rw [hpB, IsPrimitiveRoot.integralPowerBasis_gen]
  have hzp : IsPrimitiveRoot hζ.toInteger p := hζ.toInteger_isPrimitiveRoot
  have hα := pB.basis.sum_repr α
  have hnu : (p : 𝓞 K) ∈ nonunits (𝓞 K) := by
    intro hu
    exact hζ.zeta_sub_one_prime'.not_isUnit (isUnit_of_dvd_unit hζ.toInteger_sub_one_dvd_prime' hu)
  have : CharP (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) p := CharP.quotient (𝓞 K) p hnu
  refine ⟨∑ i, (pB.basis.repr α i) ^ p, ?_⟩
  apply Ideal.Quotient.eq.1
  rw [map_pow]
  conv_lhs => rw [← hα]
  rw [map_sum, sum_pow_char p]
  simp only [Int.cast_sum, Int.cast_pow, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zsmul_eq_mul, PowerBasis.coe_basis]
  show (Ideal.Quotient.mk _ (_ * (pB.gen ^ (i : ℕ)))) ^ p = _
  have h1 : (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)}) (hζ.toInteger ^ (i : ℕ))) ^ p = 1 := by
    rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hzp.pow_eq_one, one_pow, map_one]
  rw [hgen, map_mul, mul_pow, h1, mul_one, map_pow, map_intCast]

/-- **Lemma 6.11.** Let $\alpha = a_0 + a_1\zeta + \dots + a_{p-1}\zeta^{p-1}$ with $a_i \in \mathbb Z$ and at least
one $a_i = 0$. If $\alpha$ is divisible by an integer $n$ in $\mathbb Z[\zeta]$, then each $a_i$ is divisible by
$n$. -/
@[kb "milne2020ant" "v3.08, Lemma 6.11, p. 103"]
theorem lemma_6_11 (hζ : IsPrimitiveRoot ζ p) (a : Fin p → ℤ) (h0 : ∃ i, a i = 0) (n : ℤ)
    (hn : (n : 𝓞 K) ∣ ∑ i : Fin p, (a i : 𝓞 K) * hζ.toInteger ^ (i : ℕ)) :
    ∀ i, n ∣ a i := by
  set pB := hζ.integralPowerBasis with hpB
  have hdim : pB.dim + 1 = p := by
    have := hp.1.two_le
    rw [hpB, IsPrimitiveRoot.integralPowerBasis_dim, Nat.totient_prime hp.1]; omega
  set d := pB.dim with hd
  set z : 𝓞 K := hζ.toInteger with hz
  have hzp : IsPrimitiveRoot z p := hζ.toInteger_isPrimitiveRoot
  let a' : ℕ → ℤ := fun i => if h : i < p then a ⟨i, h⟩ else 0
  have ha' : ∀ i : Fin p, a' i = a i := fun i => by simp [a', i.2]
  have hS : ∑ i : Fin p, (a i : 𝓞 K) * z ^ (i : ℕ)
      = ∑ i ∈ Finset.range d, ((a' i - a' d : ℤ) : 𝓞 K) * z ^ i := by
    have h1 : ∑ i : Fin p, (a i : 𝓞 K) * z ^ (i : ℕ) = ∑ i ∈ Finset.range p, (a' i : 𝓞 K) * z ^ i := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => (a' i : 𝓞 K) * z ^ i) p]
      simp [ha']
    have hg := hzp.geom_sum_eq_zero (by have := hp.1.two_le; omega)
    rw [← hdim, Finset.sum_range_succ] at hg
    rw [h1, ← hdim, Finset.sum_range_succ]
    have : z ^ d = -∑ i ∈ Finset.range d, z ^ i := by linear_combination hg
    rw [this]
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, mul_neg, Finset.mul_sum]
    ring
  obtain ⟨β, hβ⟩ := hn
  rw [hS] at hβ
  have hgen : pB.gen = z := by rw [hpB, IsPrimitiveRoot.integralPowerBasis_gen]
  have hb := pB.basis.sum_repr β
  have key : ∀ j : Fin d, (n : ℤ) * pB.basis.repr β j = a' j - a' d := by
    intro j
    have e1 : ∑ i ∈ Finset.range d, ((a' i - a' d : ℤ) : 𝓞 K) * z ^ i
        = ∑ i : Fin d, (a' i - a' d) • pB.basis i := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => ((a' i - a' d : ℤ) : 𝓞 K) * z ^ i) d]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [zsmul_eq_mul, PowerBasis.coe_basis]
      show _ = _ * (pB.gen ^ (i : ℕ))
      rw [hgen]
    have e2 : ∑ i ∈ Finset.range d, ((a' i - a' d : ℤ) : 𝓞 K) * z ^ i
        = ∑ i : Fin d, (n * pB.basis.repr β i) • pB.basis i := by
      rw [hβ]
      conv_lhs => rw [← hb]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul]; exact (zsmul_eq_mul _ _).symm
    have := congrArg (fun v => pB.basis.repr v j) (e1.symm.trans e2)
    have h3 := pB.basis.repr_sum_self (fun i : Fin d => (a' i - a' d))
    have h4 := pB.basis.repr_sum_self (fun i : Fin d => (n * pB.basis.repr β i))
    exact ((congrFun h4 j).symm.trans this.symm).trans (congrFun h3 j)
  have hdiv : ∀ j : Fin d, n ∣ a' j - a' d := fun j => ⟨_, (key j).symm⟩
  have hd0 : n ∣ a' d := by
    obtain ⟨k, hk⟩ := h0
    have hk' : a' k = 0 := by rw [ha', hk]
    by_cases hkd : (k : ℕ) = d
    · rw [← hkd, hk']; exact dvd_zero _
    · have := hdiv ⟨k, by omega⟩
      simp only [hk', zero_sub, dvd_neg] at this
      exact this
  intro i
  rw [← ha']
  by_cases hid : (i : ℕ) = d
  · rw [hid]; exact hd0
  · have := hdiv ⟨i, by omega⟩
    simpa using dvd_add this hd0

/-- **Lemma 6.9.** In the setting of the proof of Theorem 6.8 ($p$ an odd prime, $x, y, z$ integers with
$x^p + y^p = z^p$, $x$ and $y$ relatively prime, and $p \nmid z$), the elements $x + \zeta^i y$ of $\mathbb Z[\zeta]$,
$0 \le i \le p - 1$, are relatively prime in pairs. Milne's "relatively prime" (no prime ideal divides both) is
expressed as `IsCoprime` in $\mathcal O_K$, which is equivalent in a Dedekind domain. -/
@[kb "milne2020ant" "v3.08, Lemma 6.9, p. 103"]
theorem lemma_6_9 (hodd : p ≠ 2) (hζ : IsPrimitiveRoot ζ p) {x y z : ℤ} (hxyz : x ^ p + y ^ p = z ^ p)
    (hxy : IsCoprime x y) (hz : ¬ (p : ℤ) ∣ z) {i j : ℕ} (hi : i < p) (hj : j < p) (hij : i ≠ j) :
    IsCoprime ((x : 𝓞 K) + hζ.toInteger ^ i * y) ((x : 𝓞 K) + hζ.toInteger ^ j * y) := by
  set w : 𝓞 K := hζ.toInteger with hw
  have hwp : IsPrimitiveRoot w p := hζ.toInteger_isPrimitiveRoot
  by_contra hnc
  have hne : Ideal.span {(x : 𝓞 K) + w ^ i * y} ⊔ Ideal.span {(x : 𝓞 K) + w ^ j * y} ≠ ⊤ := fun h =>
    hnc ((Ideal.isCoprime_span_singleton_iff _ _).1 (Ideal.isCoprime_iff_sup_eq.2 h))
  obtain ⟨q, hqmax, hq⟩ := Ideal.exists_le_maximal _ hne
  have hu : (x : 𝓞 K) + w ^ i * y ∈ q :=
    hq (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hv : (x : 𝓞 K) + w ^ j * y ∈ q :=
    hq (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hq1 : (1 : 𝓞 K) ∉ q := (Ideal.ne_top_iff_one q).1 hqmax.ne_top
  -- the key: q contains w^i - w^j
  have hwx : (w ^ i - w ^ j) * x ∈ q := by
    have : (w ^ i - w ^ j) * x = w ^ i * ((x : 𝓞 K) + w ^ j * y) - w ^ j * ((x : 𝓞 K) + w ^ i * y) := by
      ring
    rw [this]
    exact q.sub_mem (q.mul_mem_left _ hv) (q.mul_mem_left _ hu)
  have hwy : (w ^ i - w ^ j) * y ∈ q := by
    have : (w ^ i - w ^ j) * y = ((x : 𝓞 K) + w ^ i * y) - ((x : 𝓞 K) + w ^ j * y) := by ring
    rw [this]
    exact q.sub_mem hu hv
  have hdiff : w ^ i - w ^ j ∈ q := by
    obtain ⟨a, b, hab⟩ := hxy
    have : w ^ i - w ^ j = (a : 𝓞 K) * ((w ^ i - w ^ j) * x) + (b : 𝓞 K) * ((w ^ i - w ^ j) * y) := by
      have h' : (a : 𝓞 K) * x + (b : 𝓞 K) * y = 1 := by exact_mod_cast hab
      linear_combination (-(w ^ i - w ^ j)) * h'
    rw [this]
    exact q.add_mem (q.mul_mem_left _ hwx) (q.mul_mem_left _ hwy)
  have key : ∀ {m k : ℕ}, k < m → m < p → w ^ m - w ^ k ∈ q → w - 1 ∈ q := by
    intro m k hkm hmp h
    have hcop : (m - k).Coprime p := by
      refine (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.1).2 ?_))
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    have hass := hwp.associated_sub_one_pow_sub_one_of_coprime hcop
    obtain ⟨c, hc⟩ := hass.symm.dvd
    have h2 : w ^ (m - k) - 1 ∈ q := by
      obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hkm.le
      obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (show k ≤ p by omega)
      have : w ^ (k + e - k) - 1 = (w ^ (k + e) - w ^ k) * w ^ r := by
        have hp1 : w ^ k * w ^ r = 1 := by rw [← pow_add, ← hr, hwp.pow_eq_one]
        have : w ^ (k + e) - w ^ k = w ^ k * (w ^ e - 1) := by rw [pow_add]; ring
        rw [this, Nat.add_sub_cancel_left]
        linear_combination (-(w ^ e - 1)) * hp1
      rw [this]
      exact q.mul_mem_right _ h
    rw [hc]
    exact q.mul_mem_right _ h2
  have hw1 : w - 1 ∈ q := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact key h hj (by have := q.neg_mem hdiff; simpa using this)
    · exact key h hi hdiff
  have hwi : ∀ m : ℕ, w ^ m - 1 ∈ q := fun m => by
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow w 1 m
    rw [one_pow] at hc
    rw [hc]
    exact q.mul_mem_right _ hw1
  have hpq : (p : 𝓞 K) ∈ q := by
    obtain ⟨c, hc⟩ := hζ.toInteger_sub_one_dvd_prime'
    rw [hc]
    exact q.mul_mem_right _ hw1
  have hxyq : ((x + y : ℤ) : 𝓞 K) ∈ q := by
    have : ((x + y : ℤ) : 𝓞 K) = ((x : 𝓞 K) + w ^ i * y) - (w ^ i - 1) * y := by push_cast; ring
    rw [this]
    exact q.sub_mem hu (q.mul_mem_right _ (hwi i))
  have hdvd : (p : ℤ) ∣ x + y := by
    by_contra hnd
    have hcop : IsCoprime (p : ℤ) (x + y) :=
      (Nat.prime_iff_prime_int.1 hp.1).irreducible.coprime_iff_not_dvd.2 hnd
    obtain ⟨a, b, hab⟩ := hcop
    apply hq1
    have : (1 : 𝓞 K) = (a : 𝓞 K) * p + (b : 𝓞 K) * ((x + y : ℤ) : 𝓞 K) := by exact_mod_cast hab.symm
    rw [this]
    exact q.add_mem (q.mul_mem_left _ hpq) (q.mul_mem_left _ hxyq)
  apply hz
  have h1 : ((x + y : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
  have h2 := congrArg (fun t : ℤ => (t : ZMod p)) hxyz
  simp only [Int.cast_add, Int.cast_pow, ZMod.pow_card] at h2
  push_cast at h1
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← h2]
  exact h1

end NumberFieldKB.MilneANT
