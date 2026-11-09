import NumberFieldKB.MilneCFT.Ch8.Basic
import NumberFieldKB.MilneCFT.Ch5Artin
import NumberFieldKB.Chebotarev.FrobeniusNF

/-!
# Milne, *Class Field Theory*, Chapter VIII §5: higher reciprocity laws

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §5,
printed pp. 243–250 (printed page = pdf page − 9).

## The power residue symbol
$K$ is a number field containing a primitive $n$th root of $1$. For a finite set of elements $a, b, \dots$ of $K$,
$S(a,b,\dots)$ (`Sset`) is the set of primes $\mathfrak p$ with $\mathrm{ord}_\mathfrak p(n) \ne 0$ or
$\mathrm{ord}_\mathfrak p(a) \ne 0$ or …; for $\mathfrak p \notin S(a)$ the **power residue symbol**
$(a/\mathfrak p)$ (`powerResidue`) is the unique $n$th root of $1$ in $K$ with $(a/\mathfrak p) \equiv
a^{(N\mathfrak p-1)/n} \pmod{\mathfrak p}$, the congruence meaning $v_\mathfrak p((a/\mathfrak p) -
a^{(N\mathfrak p - 1)/n}) < 1$ (multiplicative valuation). It is extended multiplicatively to ideals
(`powerResidueIdeal`) and to elements (`powerResidueElt`, $(a/b) = \prod_{v\notin S(a)}(a/\mathfrak p_v)^{\mathrm{ord}_v
b}$). This is a different definition from Chapter V's `powerResidueSymbol` (through the Artin symbol); 5.3
(`item_5_3`) is the comparison.

## The Hilbert symbol
Milne defines $(a,b)_v = \zeta^{n\,\mathrm{inv}_v[A(a,b;\zeta)]}$ through the cyclic algebra $A(a,b;\zeta)$ and the local
invariant; neither the cyclic algebras of degree $n$ nor the local invariants at completions of number fields are
formalized. Here the symbol is defined by the formula of **Remark 5.9**, $(a,b)_v = \phi_v(b)(a^{1/n})/a^{1/n}$, with
the local Artin map $\phi_v$ the restriction to $K_v^\times$ of an idèlic Artin map $\phi$ of $L = K[a^{1/n}]$
(Chapter V, Summary 5.10, `IsIdelicArtinMap`; Milne, V, 5.2 and the diagram of VIII, Example 2.2): `hilbertArtin`.
The equality with the algebra definition is Remark 5.9, not formalized. Results about it are conditional on the
existence of $\phi$ (Chapter V's named `IdelicReciprocity`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev
open scoped nonZeroDivisors IsMulCommutative

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {K : Type} [Field K] [NumberField K]

/-! ## The power residue symbol -/

/-- The set $S(a, b, \dots)$ of Milne, *CFT*, VIII, p. 244: the primes $\mathfrak p$ with $\mathrm{ord}_\mathfrak
p(n) \ne 0$ or $\mathrm{ord}_\mathfrak p(a) \ne 0$ for some $a \in A$. ($S(\emptyset) = S$ is the set of divisors of
$n$.) -/
@[kb "milne2020cft" "Ch. VIII, §5, p. 244 (the set S(a, b, ...))"]
def Sset (n : ℕ) (A : Set K) : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | (n : 𝓞 K) ∈ v.asIdeal ∨ ∃ a ∈ A, v.valuation K a ≠ 1}

/-- $\mu$ is the value of the power residue symbol $(a/\mathfrak p)$: an $n$th root of $1$ with $\mu \equiv
a^{(N\mathfrak p-1)/n} \pmod{\mathfrak p}$. -/
def IsPowerResidueValue (n : ℕ) (a : K) (v : HeightOneSpectrum (𝓞 K)) (μ : K) : Prop :=
  μ ^ n = 1 ∧ v.valuation K (μ - a ^ ((Ideal.absNorm v.asIdeal - 1) / n)) < 1

/-! ### Reduction modulo $\mathfrak p$ -/

section Core
variable (v : HeightOneSpectrum (𝓞 K))

theorem val_add_lt_one {x y : K} (hx : v.valuation K x < 1) (hy : v.valuation K y < 1) :
    v.valuation K (x + y) < 1 := Valuation.map_add_lt _ hx hy

theorem val_sub_lt_one {x y : K} (hx : v.valuation K x < 1) (hy : v.valuation K y < 1) :
    v.valuation K (x - y) < 1 := by
  rw [sub_eq_add_neg]; exact val_add_lt_one v hx (by rwa [Valuation.map_neg])

theorem val_pow_sub_lt_gen {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation R Γ₀) {x y : R} (hx : w x ≤ 1) (hy : w y ≤ 1)
    (h : w (x - y) < 1) (k : ℕ) : w (x ^ k - y ^ k) < 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : x ^ (k + 1) - y ^ (k + 1) = x * (x ^ k - y ^ k) + (x - y) * y ^ k := by ring
    rw [this]
    apply Valuation.map_add_lt
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) ih
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hy k)) h

theorem val_pow_sub_lt {x y : K} (hx : v.valuation K x ≤ 1) (hy : v.valuation K y ≤ 1)
    (h : v.valuation K (x - y) < 1) (k : ℕ) : v.valuation K (x ^ k - y ^ k) < 1 :=
  val_pow_sub_lt_gen (v.valuation K) hx hy h k

theorem exists_approx (a : K) (ha : v.valuation K a ≤ 1) :
    ∃ x : 𝓞 K, v.valuation K ((x : K) - a) < 1 := by
  obtain ⟨x, hx⟩ := v.exists_valuation_sub_lt_of_integer ha 1
  exact ⟨x, by simpa using hx⟩

theorem congr_iff (a : K) (ha : v.valuation K a ≤ 1) (x : 𝓞 K) (hx : v.valuation K ((x : K) - a) < 1)
    (μ : 𝓞 K) (k : ℕ) :
    v.valuation K ((μ : K) - a ^ k) < 1 ↔
      Ideal.Quotient.mk v.asIdeal μ = (Ideal.Quotient.mk v.asIdeal x) ^ k := by
  have hxle : v.valuation K (x : K) ≤ 1 := v.valuation_le_one x
  have h1 : v.valuation K ((x : K) ^ k - a ^ k) < 1 := val_pow_sub_lt v hxle ha hx k
  have h2 : v.valuation K ((μ : K) - a ^ k) < 1 ↔ v.valuation K ((μ : K) - (x : K) ^ k) < 1 := by
    constructor
    · intro h
      have := val_sub_lt_one v h h1
      convert this using 2; ring
    · intro h
      have := val_add_lt_one v h h1
      convert this using 2; ring
  rw [h2, show (Ideal.Quotient.mk v.asIdeal x) ^ k = Ideal.Quotient.mk v.asIdeal (x ^ k) from
    (map_pow _ _ _).symm, Ideal.Quotient.eq]
  have : ((μ : K) - (x : K) ^ k) = ((μ - x ^ k : 𝓞 K) : K) := by push_cast; ring
  rw [this, v.valuation_lt_one_iff_mem]

theorem notMem_Sset_iff (n : ℕ) (a : K) :
    v ∉ Sset n {a} ↔ (n : 𝓞 K) ∉ v.asIdeal ∧ v.valuation K a = 1 := by
  simp [Sset]

theorem val_natCast_eq_one (n : ℕ) (h : (n : 𝓞 K) ∉ v.asIdeal) : v.valuation K (n : K) = 1 := by
  have := (v.valuation_eq_one_iff_notMem (K := K) (r := (n : 𝓞 K))).2 h
  simpa using this

theorem val_zeta_eq_one {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    v.valuation K ζ = 1 := by
  have h : v.valuation K ζ ^ n = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  exact ((pow_eq_one_iff).1 h).resolve_right hn.ne'

theorem val_one_sub_le (x : K) (hx : v.valuation K x ≤ 1) : v.valuation K (1 - x) ≤ 1 := by
  refine (Valuation.map_sub _ _ _).trans ?_
  simp [hx]

theorem zeta_pow_sub_one_not_lt {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hnv : (n : 𝓞 K) ∉ v.asIdeal) {d : ℕ} (h0 : 0 < d) (hd : d < n) :
    ¬ v.valuation K (ζ ^ d - 1) < 1 := by
  intro hlt
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hprod := hζ.prod_one_sub_pow_eq_order
  have hvn := val_natCast_eq_one v (m + 1) hnv
  have hvp : v.valuation K (∏ k ∈ Finset.range m, (1 - ζ ^ (k + 1))) = 1 := by
    rw [hprod]; push_cast at hvn; exact hvn
  have hmem : d - 1 ∈ Finset.range m := by simp; omega
  rw [← Finset.mul_prod_erase _ _ hmem, map_mul] at hvp
  have h1 : v.valuation K (1 - ζ ^ (d - 1 + 1)) < 1 := by
    rw [Nat.sub_add_cancel h0, ← Valuation.map_neg, neg_sub]; exact hlt
  have h2 : v.valuation K (∏ k ∈ (Finset.range m).erase (d - 1), (1 - ζ ^ (k + 1))) ≤ 1 := by
    rw [map_prod]
    refine Finset.prod_le_one fun k _ => val_one_sub_le v _ ?_
    rw [map_pow, val_zeta_eq_one v (by omega) hζ, one_pow]
  have : v.valuation K (1 - ζ ^ (d - 1 + 1)) * v.valuation K (∏ k ∈ (Finset.range m).erase (d - 1), (1 - ζ ^ (k + 1))) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' h2) h1
  exact absurd hvp this.ne

theorem zeta_pow_inj {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hnv : (n : 𝓞 K) ∉ v.asIdeal) {i j : ℕ} (hi : i < n) (hj : j < n)
    (h : v.valuation K (ζ ^ i - ζ ^ j) < 1) : i = j := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi (by rwa [Valuation.map_sub_swap]) (by omega)).symm
  by_contra hne
  have h0 : 0 < j - i := by omega
  apply zeta_pow_sub_one_not_lt v hn hζ hnv h0 (by omega)
  have : ζ ^ j - ζ ^ i = ζ ^ i * (ζ ^ (j - i) - 1) := by
    rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hij]; ring
  rw [Valuation.map_sub_swap, this, map_mul, map_pow, val_zeta_eq_one v hn hζ, one_pow, one_mul] at h
  exact h


theorem exists_zeta_val {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n) (a : K)
    (hv : v ∉ Sset n {a}) : ∃ i < n, IsPowerResidueValue n a v (ζ ^ i) := by
  obtain ⟨hnv, hav⟩ := (notMem_Sset_iff v n a).1 hv
  have := v.isMaximal
  obtain ⟨x, hx⟩ := exists_approx v a hav.le
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let _ : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  let _ : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hq : Ideal.absNorm v.asIdeal = Fintype.card (𝓞 K ⧸ v.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hint : IsIntegral ℤ ζ := hζ.isIntegral hn
  let ζ' : 𝓞 K := ⟨ζ, hint⟩
  have hζ' : ((ζ' : 𝓞 K) : K) = ζ := rfl
  have hpow : ∀ l : ℕ, ((ζ' ^ l : 𝓞 K) : K) = ζ ^ l := fun l => by push_cast; rfl
  have hξ : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal ζ') n := by
    refine IsPrimitiveRoot.mk_of_lt _ hn ?_ ?_
    · rw [← map_pow]
      have : ζ' ^ n = 1 := by
        apply Subtype.ext
        show ((ζ' ^ n : 𝓞 K) : K) = ((1 : 𝓞 K) : K)
        rw [hpow]; simpa using hζ.pow_eq_one
      rw [this, map_one]
    · intro l hl0 hln heq
      apply zeta_pow_sub_one_not_lt v hn hζ hnv hl0 hln
      rw [← map_pow, ← map_one (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq] at heq
      have := (v.valuation_lt_one_iff_mem (K := K) _).2 heq
      simpa [hpow] using this
  have hxne : Ideal.Quotient.mk v.asIdeal x ≠ 0 := by
    intro h0
    rw [Ideal.Quotient.eq_zero_iff_mem, ← v.valuation_lt_one_iff_mem (K := K)] at h0
    have : v.valuation K a < 1 := by
      have := val_sub_lt_one v h0 hx
      simpa using this
    exact absurd hav this.ne
  have hξne := hξ.ne_zero hn.ne'
  have hdvd : n ∣ Fintype.card (𝓞 K ⧸ v.asIdeal) - 1 :=
    hξ.dvd_of_pow_eq_one _ (FiniteField.pow_card_sub_one_eq_one _ hξne)
  obtain ⟨c, hc⟩ := hdvd
  have hm : (Ideal.absNorm v.asIdeal - 1) / n = c := by
    rw [hq, hc, Nat.mul_div_cancel_left _ hn]
  have hy : (Ideal.Quotient.mk v.asIdeal x ^ c) ^ n = 1 := by
    rw [← pow_mul, mul_comm, ← hc]
    exact FiniteField.pow_card_sub_one_eq_one _ hxne
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨i, hi, hiy⟩ := hξ.eq_pow_of_pow_eq_one hy
  refine ⟨i, hi, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · rw [hm, ← hpow, congr_iff v a hav.le x hx, map_pow, hiy]


end Core

/-! ### Newton's method in a complete valued field -/

section Hensel

open Filter Topology Polynomial
open scoped WithZero

variable {F : Type*} [Field F] [Valued F ℤᵐ⁰]

theorem exists_pow_lt_of_lt_one' (c γ : ℤᵐ⁰) (hc : c < 1) (hγ : γ ≠ 0) : ∃ N : ℕ, c ^ N < γ := by
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨1, by simpa using zero_lt_iff.2 hγ⟩
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt hγ
  refine ⟨k, lt_of_le_of_lt ?_ hk⟩
  have h1 : c = WithZero.exp (WithZero.log c) := (WithZero.exp_log hc0).symm
  have h2 : WithZero.log c ≤ -1 := by
    have : WithZero.log c < 0 := by
      rw [← WithZero.exp_lt_exp, ← h1]; simpa using hc
    omega
  rw [h1, ← WithZero.exp_nsmul]
  apply WithZero.exp_le_exp.2
  simp only [nsmul_eq_mul]
  nlinarith


theorem eventually_pow_lt {c : ℤᵐ⁰} (hc : c < 1) {ε : ℤᵐ⁰} (hε : ε ≠ 0) :
    ∃ N : ℕ, ∀ k, N ≤ k → c ^ (2 ^ k) < ε := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one' c ε hc hε
  refine ⟨N, fun k hk => lt_of_le_of_lt ?_ hN⟩
  exact pow_le_pow_right_of_le_one' hc.le (hk.trans (Nat.lt_two_pow_self).le)

theorem embedding_ne_zero (γ : (Valued.v : Valuation F ℤᵐ⁰).ValueGroup₀ˣ) :
    (MonoidWithZeroHom.ValueGroup₀.embedding γ.1 : ℤᵐ⁰) ≠ 0 :=
  (map_ne_zero_iff _ MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective).2 γ.ne_zero

theorem tendsto_zero_of_le_pow {z : ℕ → F} {c : ℤᵐ⁰} (hc : c < 1)
    (hz : ∀ k, Valued.v (z k) ≤ c ^ (2 ^ k)) : Tendsto z atTop (𝓝 0) := by
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  obtain ⟨N, hN⟩ := eventually_pow_lt hc (embedding_ne_zero γ)
  rw [mem_map, mem_atTop_sets]
  refine ⟨N, fun k hk => hγ ?_⟩
  show Valued.v.restrict (z k) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt (hz k) (hN k hk)

theorem cauchySeq_of_le_pow {x : ℕ → F} {c : ℤᵐ⁰} (hc : c < 1)
    (hz : ∀ k, Valued.v (x (k + 1) - x k) ≤ c ^ (2 ^ k)) : CauchySeq x := by
  rw [(Valued.hasBasis_uniformity F ℤᵐ⁰).cauchySeq_iff]
  intro γ _
  obtain ⟨N, hN⟩ := eventually_pow_lt hc (embedding_ne_zero γ)
  have key : ∀ m, N ≤ m → ∀ d, Valued.v (x (m + d) - x m) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    intro m hm d
    induction d with
    | zero => simp [zero_lt_iff, embedding_ne_zero γ]
    | succ d ih =>
      have : x (m + (d + 1)) - x m = (x (m + d + 1) - x (m + d)) + (x (m + d) - x m) := by
        rw [← add_assoc]; ring
      rw [this]
      exact Valuation.map_add_lt _ (lt_of_le_of_lt (hz _) (hN _ (hm.trans (Nat.le_add_right _ _)))) ih
  refine ⟨N, fun m hm n hn => ?_⟩
  show Valued.v.restrict (x n - x m) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  rcases le_total m n with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact key m hm d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Valuation.map_sub_swap]
    exact key n hn d


theorem newton_step (n : ℕ) (A y : F) (hn1 : Valued.v (n : F) = 1) (hy : Valued.v y = 1)
    (hA : Valued.v A ≤ 1) :
    Valued.v (-(y ^ n - A) / (n * y ^ (n - 1))) = Valued.v (y ^ n - A) ∧
    Valued.v ((y + -(y ^ n - A) / (n * y ^ (n - 1))) ^ n - A) ≤ Valued.v (y ^ n - A) ^ 2 := by
  have hd : Valued.v ((n : F) * y ^ (n - 1)) = 1 := by
    rw [map_mul, hn1, map_pow, hy, one_pow, one_mul]
  have hd0 : (n : F) * y ^ (n - 1) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hd; exact zero_ne_one hd
  have hfle : Valued.v (y ^ n - A) ≤ 1 := by
    refine (Valuation.map_sub _ _ _).trans ?_
    simp [hy, hA]
  have hh : Valued.v (-(y ^ n - A) / ((n : F) * y ^ (n - 1))) = Valued.v (y ^ n - A) := by
    rw [map_div₀, Valuation.map_neg, hd, div_one]
  refine ⟨hh, ?_⟩
  set h := -(y ^ n - A) / ((n : F) * y ^ (n - 1)) with hhdef
  let O := (Valued.v : Valuation F ℤᵐ⁰).valuationSubring
  let Y : O := ⟨y, (Valuation.mem_valuationSubring_iff _ _).2 hy.le⟩
  let Aa : O := ⟨A, hA⟩
  let H : O := ⟨h, by rw [Valuation.mem_valuationSubring_iff, hh]; exact hfle⟩
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (X ^ n - C Aa : O[X]) Y H
  have hk' := congrArg (fun z : O => (z : F)) hk
  simp only [eval_sub, eval_pow, eval_X, eval_C, derivative_sub, derivative_X_pow, derivative_C,
    sub_zero, eval_mul] at hk'
  push_cast at hk'
  have hdh : (n : F) * y ^ (n - 1) * h = -(y ^ n - A) := by
    rw [hhdef, mul_div_assoc']; rw [mul_div_cancel_left₀ _ hd0]
  have e : (y + h) ^ n - A = (k : F) * h ^ 2 := by
    have : (y + h) ^ n - A = (y ^ n - A) + (n : F) * y ^ (n - 1) * h + (k : F) * h ^ 2 := by
      simpa [Y, Aa, H] using hk'
    rw [this, hdh]; ring
  rw [e, map_mul, map_pow, hh]
  exact mul_le_of_le_one_left' ((Valuation.mem_valuationSubring_iff _ _).1 k.2)


theorem exists_pow_eq_of_approx [CompleteSpace F] (n : ℕ) (A x0 : F)
    (hn1 : Valued.v (n : F) = 1) (hA : Valued.v A ≤ 1) (hx0 : Valued.v x0 = 1)
    (h : Valued.v (x0 ^ n - A) < 1) : ∃ x : F, x ^ n = A := by
  set c := Valued.v (x0 ^ n - A) with hc
  let g : F → F := fun y => y + -(y ^ n - A) / (n * y ^ (n - 1))
  let x : ℕ → F := fun k => g^[k] x0
  have hxs : ∀ k, x (k + 1) = g (x k) := fun k => Function.iterate_succ_apply' g k x0
  have hx : ∀ k, Valued.v (x k) = 1 ∧ Valued.v ((x k) ^ n - A) ≤ c ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => simp [x, hx0, ← hc]
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨s1, s2⟩ := newton_step n A (x k) hn1 h1 hA
      have hlt : Valued.v (-(x k ^ n - A) / (n * x k ^ (n - 1))) < 1 := by
        rw [s1]; exact lt_of_le_of_lt h2 (pow_lt_one' h (by positivity))
      rw [hxs]
      refine ⟨?_, ?_⟩
      · show Valued.v (x k + _) = 1
        rw [Valuation.map_add_eq_of_lt_left _ (by rwa [h1])]; exact h1
      · show Valued.v ((x k + _) ^ n - A) ≤ _
        calc _ ≤ _ := s2
          _ ≤ (c ^ (2 ^ k)) ^ 2 := pow_le_pow_left' h2 2
          _ = c ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]
  have hz : ∀ k, Valued.v (x (k + 1) - x k) ≤ c ^ (2 ^ k) := by
    intro k
    obtain ⟨s1, -⟩ := newton_step n A (x k) hn1 (hx k).1 hA
    rw [hxs]
    have : g (x k) - x k = -(x k ^ n - A) / (n * x k ^ (n - 1)) := by simp only [g]; ring
    rw [this, s1]; exact (hx k).2
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_pow h hz)
  refine ⟨L, ?_⟩
  have t1 : Tendsto (fun k => x k ^ n - A) atTop (𝓝 (L ^ n - A)) := (hL.pow n).sub_const A
  have t2 : Tendsto (fun k => x k ^ n - A) atTop (𝓝 0) :=
    tendsto_zero_of_le_pow h (fun k => (hx k).2)
  exact sub_eq_zero.1 (tendsto_nhds_unique t1 t2)

end Hensel

open Classical in
/-- **The power residue symbol** $(a/\mathfrak p)$ (definition in prose; Milne, *CFT*, VIII, §5, p. 244): for $K$
containing a primitive $n$th root of $1$ and $\mathfrak p \notin S(a)$, the unique $n$th root of $1$ congruent to
$a^{(N\mathfrak p-1)/n}$ modulo $\mathfrak p$ (`powerResidue_spec`, `powerResidue_unique`); $1$ by convention
otherwise. -/
@[kb "milne2020cft" "Ch. VIII, §5, p. 244 (the power residue symbol (a/p))"]
def powerResidue (n : ℕ) (a : K) (v : HeightOneSpectrum (𝓞 K)) : K :=
  if h : ∃ μ, IsPowerResidueValue n a v μ then h.choose else 1

/-- The defining property of the power residue symbol holds for $\mathfrak p \notin S(a)$. -/
theorem powerResidue_spec (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ Sset n {a}) : IsPowerResidueValue n a v (powerResidue n a v) := by
  obtain ⟨i, -, hi⟩ := exists_zeta_val v hn hζ a hv
  have h : ∃ μ, IsPowerResidueValue n a v μ := ⟨_, hi⟩
  unfold powerResidue
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

/-- Uniqueness of the power residue symbol (the reduction $\mu_n(K) \to \mu_n(\mathcal O_K/\mathfrak p)$ is bijective
for $\mathfrak p \nmid n$). -/
theorem isPowerResidueValue_unique (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ Sset n {a}) (μ μ' : K) (hμ : IsPowerResidueValue n a v μ)
    (hμ' : IsPowerResidueValue n a v μ') : μ = μ' := by
  obtain ⟨hnv, -⟩ := (notMem_Sset_iff v n a).1 hv
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.1
  obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ'.1
  have : v.valuation K (ζ ^ i - ζ ^ j) < 1 := by
    have := val_sub_lt_one v hμ.2 hμ'.2
    convert this using 2; ring
  rw [zeta_pow_inj v hn hζ hnv hi hj this]

theorem powerResidue_unique (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ Sset n {a}) (μ : K) (hμ : IsPowerResidueValue n a v μ) :
    μ = powerResidue n a v :=
  isPowerResidueValue_unique n hn ζ hζ a v hv μ _ hμ (powerResidue_spec n hn ζ hζ a v hv)

/-- In a finite field with `q - 1 = n m`, an element `x` with `x ^ m = 1` is an `n`th power. -/
theorem exists_pow_eq_of_pow_eq_one {κ : Type*} [Field κ] [Fintype κ] {n m : ℕ}
    (hnm : Fintype.card κ - 1 = n * m) (x : κ) (hx : x ≠ 0) (h : x ^ m = 1) :
    ∃ y : κ, y ^ n = x := by
  classical
  have hc : 1 < Fintype.card κ := Fintype.one_lt_card
  have hm : m ≠ 0 := by
    rintro rfl
    simp at hnm; omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := κˣ)
  have hord : orderOf g = n * m := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units, hnm]
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1 (hg (Units.mk0 x hx))
  have h1 : (Units.mk0 x hx) ^ m = 1 := Units.ext (by simpa using h)
  rw [← ht, ← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hord] at h1
  have h2 : (n : ℤ) * m ∣ t * m := by exact_mod_cast h1
  obtain ⟨s, hs⟩ := Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast hm) h2
  refine ⟨((g ^ s : κˣ) : κ), ?_⟩
  have : (g ^ s) ^ n = Units.mk0 x hx := by
    rw [← ht, ← zpow_natCast, ← zpow_mul, hs]; congr 1; ring
  simpa using congrArg (fun u : κˣ => (u : κ)) this

theorem dvd_absNorm_sub_one (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hnv : (n : 𝓞 K) ∉ v.asIdeal) : n ∣ Ideal.absNorm v.asIdeal - 1 := by
  have := v.isMaximal
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let _ : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  let _ : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hq : Ideal.absNorm v.asIdeal = Fintype.card (𝓞 K ⧸ v.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hint : IsIntegral ℤ ζ := hζ.isIntegral hn
  let ζ' : 𝓞 K := ⟨ζ, hint⟩
  have hpow : ∀ l : ℕ, ((ζ' ^ l : 𝓞 K) : K) = ζ ^ l := fun l => by push_cast; rfl
  have hξ : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal ζ') n := by
    refine IsPrimitiveRoot.mk_of_lt _ hn ?_ ?_
    · rw [← map_pow]
      have : ζ' ^ n = 1 := by
        apply Subtype.ext
        show ((ζ' ^ n : 𝓞 K) : K) = ((1 : 𝓞 K) : K)
        rw [hpow]; simpa using hζ.pow_eq_one
      rw [this, map_one]
    · intro l hl0 hln heq
      apply zeta_pow_sub_one_not_lt v hn hζ hnv hl0 hln
      rw [← map_pow, ← map_one (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq] at heq
      have := (v.valuation_lt_one_iff_mem (K := K) _).2 heq
      simpa [hpow] using this
  rw [hq]
  exact hξ.dvd_of_pow_eq_one _ (FiniteField.pow_card_sub_one_eq_one _ (hξ.ne_zero hn.ne'))

theorem powerResidue_eq_one_iff (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ Sset n {a}) :
    powerResidue n a v = 1 ↔ ∃ x : 𝓞 K, v.valuation K ((x : K) ^ n - a) < 1 := by
  obtain ⟨hnv, hav⟩ := (notMem_Sset_iff v n a).1 hv
  have := v.isMaximal
  obtain ⟨x, hx⟩ := exists_approx v a hav.le
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let _ : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  let _ : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hq : Ideal.absNorm v.asIdeal = Fintype.card (𝓞 K ⧸ v.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hxne : Ideal.Quotient.mk v.asIdeal x ≠ 0 := by
    intro h0
    rw [Ideal.Quotient.eq_zero_iff_mem, ← v.valuation_lt_one_iff_mem (K := K)] at h0
    have : v.valuation K a < 1 := by
      have := val_sub_lt_one v h0 hx
      simpa using this
    exact absurd hav this.ne
  obtain ⟨c, hc⟩ := dvd_absNorm_sub_one v hn hζ hnv
  rw [hq] at hc
  have hm : (Ideal.absNorm v.asIdeal - 1) / n = c := by
    rw [hq, hc, Nat.mul_div_cancel_left _ hn]
  have hsp := powerResidue_spec n hn ζ hζ a v hv
  constructor
  · intro h1
    rw [h1] at hsp
    have h2 := (congr_iff v a hav.le x hx 1 c).1 (by have := hsp.2; rw [hm] at this; simpa using this)
    rw [map_one] at h2
    obtain ⟨y, hy⟩ := exists_pow_eq_of_pow_eq_one hc _ hxne h2.symm
    obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨y0, ?_⟩
    have := (congr_iff v a hav.le x hx (y0 ^ n) 1).2 (by rw [pow_one, map_pow, hy])
    simpa using this
  · rintro ⟨x0, hx0⟩
    have h2 := (congr_iff v a hav.le x hx (x0 ^ n) 1).1 (by simpa using hx0)
    rw [pow_one, map_pow] at h2
    have h3 : (Ideal.Quotient.mk v.asIdeal x) ^ c = 1 := by
      rw [← h2, ← pow_mul, ← hc]
      refine FiniteField.pow_card_sub_one_eq_one _ ?_
      intro h0
      apply hxne
      rw [← h2, h0, zero_pow hn.ne']
    refine (powerResidue_unique n hn ζ hζ a v hv 1 ⟨one_pow _, ?_⟩).symm
    rw [hm]
    refine (congr_iff v a hav.le x hx 1 c).2 ?_
    rw [map_one, h3]

theorem exists_approx_iff_isLocalPow (n : ℕ) (hn : 0 < n) (a : K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ Sset n {a}) :
    (∃ x : 𝓞 K, v.valuation K ((x : K) ^ n - a) < 1) ↔ IsLocalPow n a v := by
  obtain ⟨hnv, hav⟩ := (notMem_Sset_iff v n a).1 hv
  have hι : ∀ k : K, Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
    fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  constructor
  · rintro ⟨x, hx⟩
    have hxn : v.valuation K ((x : K) ^ n) = 1 := by
      have := Valuation.map_eq_of_sub_lt (v.valuation K) (y := (x : K) ^ n) (x := a) (by rwa [hav])
      rw [this, hav]
    have hx1 : v.valuation K (x : K) = 1 := by
      rw [map_pow] at hxn
      exact ((pow_eq_one_iff).1 hxn).resolve_right hn.ne'
    refine exists_pow_eq_of_approx n (algebraMap K (v.adicCompletion K) a)
      (algebraMap K (v.adicCompletion K) (x : K)) ?_ ?_ ?_ ?_
    · rw [← map_natCast (algebraMap K (v.adicCompletion K)), hι, val_natCast_eq_one v n hnv]
    · rw [hι, hav]
    · rw [hι, hx1]
    · rw [← map_pow, ← map_sub, hι]; exact hx
  · rintro ⟨y, hy⟩
    have hy1 : Valued.v y = 1 := by
      have : Valued.v y ^ n = 1 := by rw [← map_pow, hy, hι, hav]
      exact ((pow_eq_one_iff).1 this).resolve_right hn.ne'
    have hs : {z : v.adicCompletion K | Valued.v (z - y) < 1} ∈ nhds y := by
      refine Valued.mem_nhds.2 ⟨1, fun z hz => ?_⟩
      have hz' : Valued.v.restrict (z - y) < 1 := hz
      rw [Valuation.restrict_lt_iff_lt_embedding] at hz'
      simpa using hz'
    obtain ⟨_, hk, k, rfl⟩ := mem_closure_iff_nhds.1
      (HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v) y) _ hs
    have hk1 : v.valuation K k = 1 := by
      rw [← hι]
      have := Valuation.map_eq_of_sub_lt Valued.v (y := algebraMap K (v.adicCompletion K) k) (x := y)
        (by rw [hy1]; exact hk)
      rw [this, hy1]
    obtain ⟨x, hx⟩ := exists_approx v k hk1.le
    refine ⟨x, ?_⟩
    have h1 : v.valuation K ((x : K) ^ n - k ^ n) < 1 :=
      val_pow_sub_lt v (v.valuation_le_one x) hk1.le hx n
    have h2 : v.valuation K (k ^ n - a) < 1 := by
      rw [← hι, map_sub, map_pow, ← hy]
      exact val_pow_sub_lt_gen Valued.v (by rw [hι, hk1]) hy1.le hk n
    have := val_add_lt_one v h1 h2
    convert this using 2; ring

theorem powerResidue_congr (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a a' : 𝓞 K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ Sset n {(a : K)}) (h : a - a' ∈ v.asIdeal) :
    v ∉ Sset n {(a' : K)} ∧ powerResidue n (a : K) v = powerResidue n (a' : K) v := by
  obtain ⟨hnv, hav⟩ := (notMem_Sset_iff v n (a : K)).1 hv
  have hlt : v.valuation K ((a : K) - a') < 1 := by
    have := (v.valuation_lt_one_iff_mem (K := K) (a - a')).2 h
    simpa using this
  have ha'1 : v.valuation K (a' : K) = 1 := by
    have := Valuation.map_eq_of_sub_lt (v.valuation K) (y := (a' : K)) (x := (a : K))
      (by rw [Valuation.map_sub_swap, hav]; exact hlt)
    rw [this, hav]
  have hv' : v ∉ Sset n {(a' : K)} := (notMem_Sset_iff v n _).2 ⟨hnv, ha'1⟩
  refine ⟨hv', ?_⟩
  have sp := powerResidue_spec n hn ζ hζ (a : K) v hv
  refine (powerResidue_unique n hn ζ hζ (a' : K) v hv' (powerResidue n (a : K) v) ⟨sp.1, ?_⟩)
  have h1 : v.valuation K ((a : K) ^ ((Ideal.absNorm v.asIdeal - 1) / n) - (a' : K) ^ ((Ideal.absNorm v.asIdeal - 1) / n)) < 1 :=
    val_pow_sub_lt v hav.le ha'1.le hlt _
  have := val_add_lt_one v sp.2 h1
  convert this using 2; ring

theorem count_mk0_eq_zero (v : HeightOneSpectrum (𝓞 K)) (b : Ideal (𝓞 K)) (hb0 : b ≠ ⊥)
    (hnd : ¬ v.asIdeal ∣ b) :
    FractionalIdeal.count K v
      ((FractionalIdeal.mk0 K ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  rw [FractionalIdeal.coe_mk0]
  have := FractionalIdeal.count_coe K v (J := b) hb0
  rw [this]
  by_contra hne
  exact hnd ((Associates.count_ne_zero_iff_dvd hb0 v.irreducible).1 (by exact_mod_cast hne))

/-- **5.1** (Milne, *CFT*, VIII, 5.1, p. 244): $(ab/\mathfrak p) = (a/\mathfrak p)(b/\mathfrak p)$ for
$\mathfrak p \notin S(a,b)$. -/
@[kb "milne2020cft" "Ch. VIII, 5.1, p. 244"]
theorem item_5_1 (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a b : K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ Sset n {a, b}) :
    powerResidue n (a * b) v = powerResidue n a v * powerResidue n b v := by
  have hv' : (n : 𝓞 K) ∉ v.asIdeal ∧ v.valuation K a = 1 ∧ v.valuation K b = 1 := by
    simpa [Sset, not_or] using hv
  obtain ⟨hnv, ha, hb⟩ := hv'
  have hva : v ∉ Sset n {a} := (notMem_Sset_iff v n a).2 ⟨hnv, ha⟩
  have hvb : v ∉ Sset n {b} := (notMem_Sset_iff v n b).2 ⟨hnv, hb⟩
  have hvab : v ∉ Sset n {a * b} := (notMem_Sset_iff v n _).2 ⟨hnv, by rw [map_mul, ha, hb, one_mul]⟩
  have sa := powerResidue_spec n hn ζ hζ a v hva
  have sb := powerResidue_spec n hn ζ hζ b v hvb
  symm
  apply powerResidue_unique n hn ζ hζ (a * b) v hvab
  refine ⟨by rw [mul_pow, sa.1, sb.1, one_mul], ?_⟩
  set m := (Ideal.absNorm v.asIdeal - 1) / n
  set μa := powerResidue n a v
  set μb := powerResidue n b v
  have hμa : v.valuation K μa = 1 := by
    have h : v.valuation K μa ^ n = 1 := by rw [← map_pow, sa.1, map_one]
    exact ((pow_eq_one_iff).1 h).resolve_right hn.ne'
  have hbm : v.valuation K (b ^ m) = 1 := by rw [map_pow, hb, one_pow]
  have : μa * μb - (a * b) ^ m = μa * (μb - b ^ m) + b ^ m * (μa - a ^ m) := by
    rw [mul_pow]; ring
  rw [this]
  apply val_add_lt_one
  · rw [map_mul, hμa, one_mul]; exact sb.2
  · rw [map_mul, hbm, one_mul]; exact sa.2

/-- **5.2** (Milne, *CFT*, VIII, 5.2, p. 244): for $\mathfrak p \notin S(a)$ the following are equivalent:
(a) $(a/\mathfrak p) = 1$; (b) $a$ becomes an $n$th power in $\mathcal O_K/\mathfrak p$ (some $x \in \mathcal O_K$
with $x^n \equiv a \pmod{\mathfrak p}$); (c) $a$ becomes an $n$th power in $K_\mathfrak p$. -/
@[kb "milne2020cft" "Ch. VIII, 5.2, p. 244"]
theorem item_5_2 (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ Sset n {a}) :
    List.TFAE [powerResidue n a v = 1,
      ∃ x : 𝓞 K, v.valuation K ((x : K) ^ n - a) < 1,
      IsLocalPow n a v] := by
  tfae_have 1 ↔ 2 := powerResidue_eq_one_iff n hn ζ hζ a v hv
  tfae_have 2 ↔ 3 := exists_approx_iff_isLocalPow n hn a v hv
  tfae_finish

/-- The power residue symbol $(a/\mathfrak b)$ of a fractional ideal $\mathfrak b = \prod\mathfrak p_i^{r_i}$
(Milne, *CFT*, VIII, p. 244, "by linearity"): $\prod_i (a/\mathfrak p_i)^{r_i}$; meaningful for $\mathfrak b \in
I^{S(a)}$. -/
@[kb "milne2020cft" "Ch. VIII, §5, p. 244 ((a/b) for b ∈ I^{S(a)})"]
def powerResidueIdeal (n : ℕ) (a : K) (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : K :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), powerResidue n a v ^ FractionalIdeal.count K v (b : FractionalIdeal (𝓞 K)⁰ K)

open Classical in
/-- The symbol $(a/b) = \prod_{v \notin S(a)} (a/\mathfrak p_v)^{\mathrm{ord}_v(b)} = (a/(b)_{S(a)})$ for $a, b \in
K^\times$ (Milne, *CFT*, VIII, p. 247). -/
@[kb "milne2020cft" "Ch. VIII, §5, p. 247 ((a/b) for elements a, b)"]
def powerResidueElt (n : ℕ) (a b : K) : K :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), if v ∈ Sset n {a} then 1 else
    powerResidue n a v ^ FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ b)

/-! ### Kummer extensions: Frobenius and ramification -/

theorem pow_absNorm_sub_one_sub_one_lt (v : HeightOneSpectrum (𝓞 K)) (d : 𝓞 K) (hd : d ∉ v.asIdeal) :
    v.valuation K ((d : K) ^ (Ideal.absNorm v.asIdeal - 1) - 1) < 1 := by
  have := v.isMaximal
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let _ : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  let _ : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hq : Ideal.absNorm v.asIdeal = Fintype.card (𝓞 K ⧸ v.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hne : Ideal.Quotient.mk v.asIdeal d ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h1 := FiniteField.pow_card_sub_one_eq_one _ hne
  rw [← hq, ← map_pow, ← map_one (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq] at h1
  have := (v.valuation_lt_one_iff_mem (K := K) _).2 h1
  simpa using this

theorem exists_scale (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : 0 < n) (a : K)
    (hav : v.valuation K a = 1) :
    ∃ d c : 𝓞 K, d ∉ v.asIdeal ∧ c ∉ v.asIdeal ∧ (c : K) = (d : K) ^ n * a := by
  obtain ⟨m, d, hmd⟩ := v.exists_primeCompl_mul_eq_of_integer a hav.le
  have hd : (d : 𝓞 K) ∉ v.asIdeal := d.2
  have hdv : v.valuation K ((d : 𝓞 K) : K) = 1 := (v.valuation_eq_one_iff_notMem).2 hd
  have hcK : algebraMap (𝓞 K) K ((d : 𝓞 K) ^ (n - 1) * m) =
      (algebraMap (𝓞 K) K (d : 𝓞 K)) ^ n * a := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [map_mul, map_pow, ← hmd, Nat.add_sub_cancel]; ring
  refine ⟨d, (d : 𝓞 K) ^ (n - 1) * m, hd, ?_, hcK⟩
  rw [← v.valuation_eq_one_iff_notMem (K := K), hcK, map_mul, map_pow]
  have hdv' : v.valuation K (algebraMap (𝓞 K) K (d : 𝓞 K)) = 1 := hdv
  rw [hdv', hav]
  simp

theorem kummer_zeta {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n) (a : K) (ha : a ≠ 0)
    (L : Type) [Field L] [NumberField L] [Algebra K L] (α : L) (hα : α ^ n = algebraMap K L a)
    (σ : Gal(L/K)) : ∃ j < n, σ α = algebraMap K L (ζ ^ j) * α := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hα
    exact ha ((algebraMap K L).injective (by simpa using hα.symm))
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) n := hζ.map_of_injective (algebraMap K L).injective
  have h : (σ α / α) ^ n = 1 := by
    rw [div_pow, ← map_pow, hα, AlgEquiv.commutes, div_self]
    exact (map_ne_zero _).2 ha
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨j, hj, hjeq⟩ := hζL.eq_pow_of_pow_eq_one h
  refine ⟨j, hj, ?_⟩
  rw [map_pow, hjeq]
  field_simp

theorem exists_beta {n : ℕ} (hn : 0 < n) (a : K)
    (L : Type) [Field L] [NumberField L] [Algebra K L] (α : L) (hα : α ^ n = algebraMap K L a)
    (d c : 𝓞 K) (hcd : (c : K) = (d : K) ^ n * a) :
    ∃ β : 𝓞 L, (β : L) = algebraMap K L d * α := by
  have h1 : (algebraMap K L d * α) ^ n = ((algebraMap (𝓞 K) (𝓞 L) c : 𝓞 L) : L) := by
    rw [mul_pow, hα, ← map_pow, ← map_mul, ← hcd]; rfl
  have : IsIntegral ℤ (algebraMap K L d * α) :=
    IsIntegral.of_pow hn (h1 ▸ RingOfIntegers.isIntegral_coe _)
  exact ⟨⟨_, this⟩, rfl⟩

theorem kummer_cong {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n) (a : K)
    (L : Type) [Field L] [NumberField L] [Algebra K L] (α : L) (hα : α ^ n = algebraMap K L a)
    (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (d c : 𝓞 K) (hc : c ∉ v.asIdeal) (hcd : (c : K) = (d : K) ^ n * a)
    (σ : Gal(L/K)) (j t : ℕ) (hj : σ α = algebraMap K L (ζ ^ j) * α)
    (β : 𝓞 L) (hβ : (β : L) = algebraMap K L d * α)
    (h : σ • β - β ^ (n * t + 1) ∈ Q) :
    v.valuation K (ζ ^ j - (c : K) ^ t) < 1 := by
  have hint : IsIntegral ℤ ζ := hζ.isIntegral hn
  let ζ' : 𝓞 K := ⟨ζ, hint⟩
  have e1 : (β : L) ^ n = algebraMap K L c := by
    rw [hβ, mul_pow, hα, ← map_pow, ← map_mul, hcd]
  have hβn : β ^ n = algebraMap (𝓞 K) (𝓞 L) c := RingOfIntegers.ext e1
  have e3 : (((ζ' ^ j - c ^ t : 𝓞 K)) : K) = ζ ^ j - (c : K) ^ t := by push_cast; rfl
  have e : σ • β - β ^ (n * t + 1) = algebraMap (𝓞 K) (𝓞 L) (ζ' ^ j - c ^ t) * β := by
    apply RingOfIntegers.ext
    have e2 : σ (β : L) = algebraMap K L (ζ ^ j) * β := by
      rw [hβ, map_mul, AlgEquiv.commutes, hj]; ring
    change σ (β : L) - (β : L) ^ (n * t + 1) = algebraMap K L (((ζ' ^ j - c ^ t : 𝓞 K)) : K) * β
    rw [e3, pow_succ, pow_mul, e1, e2]
    simp only [map_sub, map_pow]
    ring
  have hβQ : β ∉ Q := by
    intro hβQ
    have h2 : β ^ n ∈ Q := Q.pow_mem_of_mem hβQ n hn
    rw [hβn] at h2
    have h3 : c ∈ Q.under (𝓞 K) := h2
    rw [← Ideal.over_def Q v.asIdeal] at h3
    exact hc h3
  rw [e] at h
  have h4 : algebraMap (𝓞 K) (𝓞 L) (ζ' ^ j - c ^ t) ∈ Q :=
    (Ideal.IsPrime.mem_or_mem inferInstance h).resolve_right hβQ
  have h5 : (ζ' ^ j - c ^ t) ∈ v.asIdeal := by
    have : (ζ' ^ j - c ^ t) ∈ Q.under (𝓞 K) := h4
    rwa [← Ideal.over_def Q v.asIdeal] at this
  rw [← e3]
  exact (v.valuation_lt_one_iff_mem (K := K) _).2 h5

/-- **5.3** (Milne, *CFT*, VIII, 5.3, p. 245): let $L = K[a^{1/n}]$ ($\alpha^n = a$, $L = K(\alpha)$; abelian over $K$
since $K$ contains the $n$th roots of $1$). For $\mathfrak p \notin S(a)$ (so $\mathfrak p$ is unramified in $L$), the
Frobenius element (Chapter V's `artinFrob`) satisfies $(\mathfrak p, L/K)(\alpha) = (a/\mathfrak p)\,\alpha$. -/
@[kb "milne2020cft" "Ch. VIII, 5.3, p. 245 (at a prime)"]
theorem item_5_3 (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : K) (ha : a ≠ 0)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (α : L)
    (hα : α ^ n = algebraMap K L a) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ Sset n {a}) :
    v ∈ unramifiedPrimes K L ∧ artinFrob L v α = algebraMap K L (powerResidue n a v) * α := by
  obtain ⟨hnv, hav⟩ := (notMem_Sset_iff v n a).1 hv
  obtain ⟨d, c, hd, hc, hcd⟩ := exists_scale v hn a hav
  obtain ⟨β, hβ⟩ := exists_beta hn a L α hα d c hcd
  have hgen' : Algebra.adjoin K {α} = ⊤ := by
    have := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (F := K)
      (IsAlgebraic.of_finite K α)
    rw [hgen] at this
    simpa using this.symm
  have ext_gen : ∀ σ τ : Gal(L/K), σ α = τ α → σ = τ := fun σ τ h =>
    AlgEquiv.coe_toAlgHom_injective (AlgHom.ext_of_adjoin_eq_top hgen' (by simpa using h))
  have hunr : v ∈ unramifiedPrimes K L := by
    intro Q hQp hQo
    have hQm : Q.IsMaximal := hQp.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
    have := finite_quotient_of_ne_bot Q (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
    refine Ideal.ramificationIdx_eq_one_iff.mp ?_
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q Gal(L/K),
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K)) v.asIdeal Q, Subgroup.card_eq_one,
      Subgroup.eq_bot_iff_forall]
    intro σ hσ
    obtain ⟨j, hj, hσα⟩ := kummer_zeta hn hζ a ha L α hα σ
    have h1 := Ideal.mem_inertia.1 hσ β
    have h2 := kummer_cong hn hζ a L α hα v Q d c hc hcd σ j 0 hσα β hβ (by simpa using h1)
    have h3 : v.valuation K (ζ ^ j - ζ ^ 0) < 1 := by simpa using h2
    have hj0 : j = 0 := zeta_pow_inj v hn hζ hnv hj hn h3
    exact ext_gen σ 1 (by rw [hσα, hj0]; simp)
  refine ⟨hunr, ?_⟩
  let Q0 : v.asIdeal.primesOver (𝓞 L) := Classical.arbitrary _
  have hQp : Q0.1.IsPrime := Q0.2.1
  have hQo : Q0.1.LiesOver v.asIdeal := Q0.2.2
  have hσ := isArithFrobAt_frobAt K L v Q0
  change frobAt K L v Q0 α = _
  set σ := frobAt K L v Q0
  obtain ⟨j, hj, hσα⟩ := kummer_zeta hn hζ a ha L α hα σ
  have hcard : Nat.card (𝓞 K ⧸ Q0.1.under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
    rw [← Ideal.over_def Q0.1 v.asIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  obtain ⟨m, hm⟩ := dvd_absNorm_sub_one v hn hζ hnv
  have hq : Ideal.absNorm v.asIdeal = n * m + 1 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    omega
  have h : σ • β - β ^ (n * m + 1) ∈ Q0.1 := by
    have := hσ β
    rwa [hcard, hq] at this
  have hcong := kummer_cong hn hζ a L α hα v Q0.1 d c hc hcd σ j m hσα β hβ h
  have hm' : (Ideal.absNorm v.asIdeal - 1) / n = m := by
    rw [hm, Nat.mul_div_cancel_left _ hn]
  have h2 : v.valuation K ((c : K) ^ m - a ^ m) < 1 := by
    have : (c : K) ^ m - a ^ m = a ^ m * ((d : K) ^ (n * m) - 1) := by
      rw [hcd, mul_pow, ← pow_mul]; ring
    rw [this, map_mul, map_pow, hav, one_pow, one_mul, ← hm]
    exact pow_absNorm_sub_one_sub_one_lt v d hd
  have h3 : IsPowerResidueValue n a v (ζ ^ j) := by
    refine ⟨by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow], ?_⟩
    rw [hm']
    have := val_add_lt_one v hcong h2
    convert this using 2; ring
  have h4 := powerResidue_unique n hn ζ hζ a v hv (ζ ^ j) h3
  rw [hσα, ← h4]

/-- **5.3** (Milne, *CFT*, VIII, 5.3, p. 245): for $\mathfrak b \in I^{S(a)}$, the global Artin map of
$L = K[a^{1/n}]$ (Chapter V's `artinMap`) satisfies $\psi_{L/K}(\mathfrak b)(\alpha) = (a/\mathfrak b)\,\alpha$. -/
@[kb "milne2020cft" "Ch. VIII, 5.3, p. 245"]
theorem item_5_3_ideal (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a : K) (ha : a ≠ 0)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (α : L)
    (hα : α ^ n = algebraMap K L a) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (b : sIdeals (Sset n {a})) :
    artinMap L (Sset n {a}) b α = algebraMap K L (powerResidueIdeal n a b) * α := by
  classical
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hα
    exact ha ((algebraMap K L).injective (by simpa using hα.symm))
  let ε : Gal(L/K) →* Lˣ :=
    { toFun := fun σ => Units.mk0 (σ α / α) (div_ne_zero ((map_ne_zero σ).2 hα0) hα0)
      map_one' := by ext; simp [hα0]
      map_mul' := fun σ τ => by
        obtain ⟨j, -, hj⟩ := kummer_zeta hn hζ a ha L α hα τ
        ext
        simp only [Units.val_mk0, Units.val_mul, AlgEquiv.mul_apply]
        rw [hj, map_mul, AlgEquiv.commutes]
        field_simp }
  have hεσ : ∀ (σ : Gal(L/K)) (μ : K), σ α = algebraMap K L μ * α →
      ((ε σ : Lˣ) : L) = algebraMap K L μ := by
    intro σ μ h
    change σ α / α = _
    rw [h]; field_simp
  have hx : ∀ x : Gal(L/K), x α = ((ε x : Lˣ) : L) * α := by
    intro x
    change x α = (x α / α) * α
    field_simp
  let T := (finite_count_ne_zero ((b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)).toFinset
  have hvT : ∀ v ∈ T, v ∉ Sset n {a} := by
    intro v hvT hvS
    have h0 := b.2 v hvS
    simp only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hvT
    exact hvT h0
  have e1 : artinMap L (Sset n {a}) b = ∏ v ∈ T, artinFrob L v ^
      FractionalIdeal.count K v ((b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
    change ∏ᶠ v : HeightOneSpectrum (𝓞 K), _ = _
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvT'
    apply hv
    have : FractionalIdeal.count K v ((b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
      by_contra h0
      exact hvT' (by simpa [T] using h0)
    simp [this]
  have e2 : powerResidueIdeal n a b = ∏ v ∈ T, powerResidue n a v ^
      FractionalIdeal.count K v ((b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
    unfold powerResidueIdeal
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvT'
    apply hv
    have : FractionalIdeal.count K v ((b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
      by_contra h0
      exact hvT' (by simpa [T] using h0)
    simp [this]
  have key : ((ε (∏ v ∈ T, artinFrob L v ^ FractionalIdeal.count K v
      ((b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) : Lˣ) : L) =
      algebraMap K L (∏ v ∈ T, powerResidue n a v ^ FractionalIdeal.count K v
        ((b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) := by
    rw [map_prod, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun v hvt => ?_
    rw [map_zpow, Units.val_zpow_eq_zpow_val, map_zpow₀]
    congr 1
    obtain ⟨-, h53⟩ := item_5_3 n hn ζ hζ a ha L α hα hgen v (hvT v hvt)
    exact hεσ _ _ h53
  rw [e1, e2, hx, key]

/-- **5.4** (Milne, *CFT*, VIII, 5.4, p. 245): let $a \in \mathcal O_K$ and $\mathfrak b$ an integral ideal in
$I^{S(a)}$. If $a' \in \mathcal O_K$, $a' \equiv a \pmod{\mathfrak b}$, then $\mathfrak b \in I^{S(a')}$ and
$(a/\mathfrak b) = (a'/\mathfrak b)$. -/
@[kb "milne2020cft" "Ch. VIII, 5.4, p. 245"]
theorem item_5_4 (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) (a a' : 𝓞 K) (b : Ideal (𝓞 K))
    (hb0 : b ≠ ⊥) (hb : ∀ v ∈ Sset n {(a : K)}, ¬ v.asIdeal ∣ b) (haa' : a - a' ∈ b) :
    (∀ v ∈ Sset n {(a' : K)}, ¬ v.asIdeal ∣ b) ∧
      powerResidueIdeal n (a : K) (FractionalIdeal.mk0 K ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩) =
        powerResidueIdeal n (a' : K) (FractionalIdeal.mk0 K ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩) := by
  have key : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ b → v ∉ Sset n {(a : K)} := fun v hvb hv =>
    hb v hv hvb
  have hb' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ b → a - a' ∈ v.asIdeal := fun v hvb =>
    Ideal.le_of_dvd hvb haa'
  refine ⟨fun v hv hvb => ?_, ?_⟩
  · exact (powerResidue_congr n hn ζ hζ a a' v (key v hvb) (hb' v hvb)).1 hv
  · unfold powerResidueIdeal
    refine finprod_congr fun v => ?_
    by_cases hvb : v.asIdeal ∣ b
    · rw [(powerResidue_congr n hn ζ hζ a a' v (key v hvb) (hb' v hvb)).2]
    · rw [count_mk0_eq_zero v b hb0 hvb, zpow_zero, zpow_zero]

end NumberFieldKB.MilneCFT.Ch8
