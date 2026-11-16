import Mathlib.Computability.Reduce
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import QuadFormsKB.Citation

/-!
# Milne, *Elliptic Curves*, Chapter V, Section 4: the Hecke operators $T(n)$ on functions on $\mathbb H$

Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, subsection "Definition of the Hecke operators" (pdf
pp. 210–212).

Milne defines $T(n)$ on modular forms of weight $2k$ for $\Gamma_0(1)$ through lattices (Definition in prose, p. 210;
see `Ch5bHeckeForms.lean` for the comparison) and derives the explicit formula (p. 211)
$$(T(n)f)(z) = n^{2k-1}\sum_{a,b,d} d^{-2k} f\Big(\frac{az+b}{d}\Big),$$
the sum over the triples of Lemma 4.15 ($ad = n$, $a \ge 1$, $0 \le b < d$). For $N \ne 1$ he only says that "the
theory of the Hecke operators is much the same, only a little more complicated" (pairs $(\Lambda, S)$, p. 211). Here
`heckeOp N k n` is the operator given by the explicit formula with the triples restricted by $\gcd(a, N) = 1$, which
is the standard Hecke operator on $S_{2k}(\Gamma_0(N))$ (Shimura, *Introduction to the arithmetic theory of
automorphic functions*, 3.5; Diamond and Shurman, *A first course in modular forms*, Proposition 5.3.1, trivial
character) and agrees with Milne's for $N = 1$. It is defined on all functions $\mathbb H \to \mathbb C$.

* `hermiteTriples n`, `heckeOp N k n`.
* `heckeOp_pow_of_dvd` (p. 212, running text): for $p \mid N$, $T(p^r) = T(p)^r$.
* `heckeOp_qExpansion_coeff_one` (p. 211, running text): for a cusp form $f = \sum c(m) q^m$ of weight $2k$ for
  $\Gamma_0(N)$, $T(n) f = c(n) q + \cdots$ for every $n \ge 1$ (Milne states it for $N = 1$).
* `thm_4_8_levelOne` (p. 211, "This proves Theorem 4.8 in the case $N = 1$").
-/

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

namespace NumberFieldKB.MilneEC.Vb

/-- The triples $(a, b, d) \in \mathbb Z^3$ with $ad = n$, $a \ge 1$, $0 \le b < d$ (Milne, *EC*, V, Lemma 4.15). -/
def hermiteTriples (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (1 : ℤ) n ×ˢ Finset.Ico (0 : ℤ) n ×ˢ Finset.Icc (1 : ℤ) n).filter
    fun t => t.1 * t.2.2 = n ∧ t.2.1 < t.2.2

/-- The point $(az + b)/d$ of $\mathbb H$ ($a, d \ge 1$). -/
def hermitePoint (t : ℤ × ℤ × ℤ) (z : ℍ) : ℍ :=
  ofComplex ((t.1 * (z : ℂ) + t.2.1) / t.2.2)

/-- **The Hecke operator $T(n)$ of level $N$ and weight $2k$** on functions $f : \mathbb H \to \mathbb C$
(Milne, *EC*, V.4, pp. 210–211; level $N$ as in the module docstring):
$(T(n)f)(z) = n^{2k-1} \sum d^{-2k} f((az + b)/d)$, the sum over the triples $(a, b, d)$ of Lemma 4.15 with
$\gcd(a, N) = 1$. -/
def heckeOp (N : ℕ) (k : ℤ) (n : ℕ) (f : ℍ → ℂ) : ℍ → ℂ := fun z =>
  (n : ℂ) ^ (2 * k - 1) *
    ∑ t ∈ (hermiteTriples n).filter (fun t => Int.gcd t.1 N = 1), (t.2.2 : ℂ) ^ (-2 * k) * f (hermitePoint t z)

/-- `heckeOp N k n` is linear. -/
def heckeOpLinear (N : ℕ) (k : ℤ) (n : ℕ) : (ℍ → ℂ) →ₗ[ℂ] (ℍ → ℂ) where
  toFun := heckeOp N k n
  map_add' f g := by
    ext z; simp only [heckeOp, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext z; simp only [heckeOp, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => by ring

/-- The point $(z + b)/m$ of $\mathbb H$ ($m \ge 1$). -/
def divPoint (m : ℕ) (b : ℕ) (z : ℍ) : ℍ := ofComplex (((z : ℂ) + b) / m)

/-- The imaginary part of $(z + b)/m$ is positive. -/
lemma im_div_pos (z : ℍ) (b : ℕ) (m : ℕ) (hm : 0 < m) : 0 < (((z : ℂ) + b) / m).im := by
  rw [Complex.div_natCast_im]
  simp only [Complex.add_im, Complex.natCast_im, add_zero]
  exact div_pos z.im_pos (by exact_mod_cast hm)

/-- The coercion of `divPoint m b z` to the complex numbers. -/
lemma coe_divPoint (m : ℕ) (hm : 0 < m) (b : ℕ) (z : ℍ) :
    ((divPoint m b z : ℍ) : ℂ) = ((z : ℂ) + b) / m := by
  simp only [divPoint, ofComplex_apply_of_im_pos (im_div_pos z b m hm)]

/-- The triples of Lemma 4.15 for $n = p^r$ with $\gcd(a, N) = 1$ and $p \mid N$ are $(1, b, p^r)$. -/
lemma filter_triples_prime_pow {N : ℕ} {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (r : ℕ) :
    (hermiteTriples (p ^ r)).filter (fun t => Int.gcd t.1 N = 1) =
      (Finset.range (p ^ r)).image (fun b : ℕ => ((1 : ℤ), (b : ℤ), ((p ^ r : ℕ) : ℤ))) := by
  have hpos : 0 < p ^ r := pow_pos hp.pos r
  ext ⟨a, b, d⟩
  simp only [hermiteTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Ico,
    Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨⟨ha1, han⟩, ⟨hb0, hbn⟩, ⟨hd1, hdn⟩⟩, had, hbd⟩, hg⟩
    have hdvd : a.natAbs ∣ p ^ r := by
      have h1 : a ∣ ((p ^ r : ℕ) : ℤ) := Dvd.intro _ had
      simpa using Int.natAbs_dvd_natAbs.mpr h1
    obtain ⟨j, hj, hja⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hj0 : j = 0 := by
      by_contra hj0
      have hpa : p ∣ a.natAbs := by
        rw [hja]; exact dvd_pow_self p hj0
      have : p ∣ Int.gcd a N := Nat.dvd_gcd hpa hpN
      rw [hg] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    subst hj0
    rw [pow_zero] at hja
    have ha : a = 1 := by omega
    subst ha
    refine ⟨b.toNat, ?_, by omega, by omega, by omega⟩
    omega
  · rintro ⟨b', hb', rfl, rfl, rfl⟩
    refine ⟨⟨⟨⟨le_refl _, ?_⟩, ⟨by positivity, ?_⟩, ⟨?_, le_refl _⟩⟩, by simp, ?_⟩, by simp⟩
    · exact_mod_cast hpos
    · exact_mod_cast hb'
    · exact_mod_cast hpos
    · exact_mod_cast hb'

/-- A sum over `range (p * q)` split by the residue and quotient modulo `p`. -/
lemma sum_range_mul_split (p q : ℕ) (F : ℕ → ℂ) :
    ∑ m ∈ Finset.range (p * q), F m = ∑ c ∈ Finset.range p, ∑ b ∈ Finset.range q, F (c + p * b) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun x => x.1 + p * x.2) (fun m => (m % p, m / p)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨c, b⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h ⊢
    nlinarith [h.1, h.2]
  · intro m hm
    simp only [Finset.mem_product, Finset.mem_range] at hm ⊢
    refine ⟨Nat.mod_lt _ hp, ?_⟩
    exact Nat.div_lt_of_lt_mul (by linarith)
  · rintro ⟨c, b⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h
    have h1 : (c + p * b) % p = c := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.1]
    have h2 : (c + p * b) / p = b := by
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt h.1, zero_add]
    simp [h1, h2]
  · intro m _
    simp only
    rw [add_comm, Nat.div_add_mod]
  · intro _ _
    rfl

/-- For $p \mid N$ prime, $T(p^r) f (z) = p^{-r} \sum_{b < p^r} f((z + b)/p^r)$. -/
lemma heckeOp_prime_pow_apply {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (r : ℕ)
    (f : ℍ → ℂ) (z : ℍ) :
    heckeOp N k (p ^ r) f z =
      ((p : ℂ) ^ r)⁻¹ * ∑ b ∈ Finset.range (p ^ r), f (divPoint (p ^ r) b z) := by
  have hpos : 0 < p ^ r := pow_pos hp.pos r
  unfold heckeOp
  rw [filter_triples_prime_pow hp hpN r, Finset.sum_image (by intro x _ y _ h; simpa using h)]
  have hA : ((p ^ r : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have key : ((p ^ r : ℕ) : ℂ) ^ (2 * k - 1) * ((p ^ r : ℕ) : ℂ) ^ (-2 * k) = ((p : ℂ) ^ r)⁻¹ := by
    rw [← zpow_add₀ hA]
    have : 2 * k - 1 + -2 * k = -1 := by ring
    rw [this, zpow_neg_one]; push_cast; rfl
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hpt : hermitePoint ((1 : ℤ), (b : ℤ), ((p ^ r : ℕ) : ℤ)) z = divPoint (p ^ r) b z := by
    simp [hermitePoint, divPoint]
  simp only [hpt]
  push_cast at key ⊢
  rw [← mul_assoc, key]

/-- For $p \mid N$ prime, $T(p^{r+1}) f = T(p)(T(p^r) f)$. -/
lemma heckeOp_succ_pow {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (r : ℕ)
    (f : ℍ → ℂ) :
    heckeOp N k (p ^ (r + 1)) f = heckeOp N k p (heckeOp N k (p ^ r) f) := by
  funext z
  have hp0 : 0 < p := hp.pos
  have hpr : 0 < p ^ r := pow_pos hp0 r
  have h1 := heckeOp_prime_pow_apply k hp hpN 1 (heckeOp N k (p ^ r) f) z
  rw [pow_one] at h1
  rw [heckeOp_prime_pow_apply k hp hpN (r + 1), h1]
  simp only [heckeOp_prime_pow_apply k hp hpN r, pow_one]
  rw [show p ^ (r + 1) = p * p ^ r from pow_succ' p r, sum_range_mul_split p (p ^ r)
    (fun m => f (divPoint (p * p ^ r) m z))]
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hpp : ((p ^ r : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hpr.ne'
  have hpq : ((p * p ^ r : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hp0 hpr).ne'
  rw [pow_succ', mul_inv, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  apply UpperHalfPlane.ext
  rw [coe_divPoint _ hpr, coe_divPoint _ hp0, coe_divPoint _ (Nat.mul_pos hp0 hpr)]
  push_cast
  field_simp
  ring

/-- Milne, *EC*, V.4, p. 212 (running text): for a prime $p$ dividing $N$, $T(p^r) = T(p)^r$, $r \ge 1$ (on all
functions on $\mathbb H$; Milne states it for the functions $F$ on pairs $(\Lambda, S)$). -/
@[kb "milne2006ec" "Ch. V, Section 4 (pdf p. 212): T(p^r) = T(p)^r for p | N"]
theorem heckeOp_pow_of_dvd {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (r : ℕ) :
    heckeOpLinear N k (p ^ r) = heckeOpLinear N k p ^ r := by
  induction r with
  | zero =>
    ext f z
    change heckeOp N k (p ^ 0) f z = f z
    rw [heckeOp_prime_pow_apply k hp hpN 0]
    simp only [pow_zero, inv_one, one_mul, Finset.range_one, Finset.sum_singleton]
    congr 1
    apply UpperHalfPlane.ext
    rw [coe_divPoint 1 one_pos]
    simp
  | succ r ih =>
    rw [pow_succ' (heckeOpLinear N k p) r, ← ih]
    ext f z
    exact congrFun (heckeOp_succ_pow k hp hpN r f) z

/-- The sum of `(ζ^m)^b` over `b < d` for `ζ` a primitive `d`-th root of unity. -/
lemma sum_rootOfUnity_pow (d m : ℕ) (hd : 0 < d) :
    ∑ b ∈ Finset.range d, (Complex.exp (2 * Real.pi * Complex.I / d) ^ m) ^ b =
      if d ∣ m then (d : ℂ) else 0 := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / d)) d :=
    Complex.isPrimitiveRoot_exp d hd.ne'
  by_cases hdm : d ∣ m
  · have : Complex.exp (2 * Real.pi * Complex.I / d) ^ m = 1 := (hζ.pow_eq_one_iff_dvd m).2 hdm
    simp [this, hdm]
  · have h1 : Complex.exp (2 * Real.pi * Complex.I / d) ^ m ≠ 1 :=
      fun h => hdm ((hζ.pow_eq_one_iff_dvd m).1 h)
    rw [geom_sum_eq h1]
    have : (Complex.exp (2 * Real.pi * Complex.I / d) ^ m) ^ d = 1 := by
      rw [← pow_mul, mul_comm m d, pow_mul, hζ.pow_eq_one, one_pow]
    simp only [hdm, ↓reduceIte]
    simp [this]

/-- Expanding the `q`-parameter of `(a z + b) / d`. -/
lemma exp_affine_pow (a d m b : ℕ) (z : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I * ((a * z + b) / d)) ^ m =
      Complex.exp (2 * Real.pi * Complex.I * (a * z / d)) ^ m *
        (Complex.exp (2 * Real.pi * Complex.I / d) ^ m) ^ b := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  ring

/-- The point $(az + b)/d$ has positive imaginary part ($a, d \ge 1$). -/
lemma im_affine_pos (a d b : ℕ) (ha : 0 < a) (hd : 0 < d) (z : ℍ) :
    0 < (((a : ℂ) * z + b) / d).im := by
  rw [Complex.div_natCast_im]
  simp only [Complex.add_im, Complex.natCast_im, Complex.mul_im, Complex.natCast_re, zero_mul,
    add_zero]
  have : (0 : ℝ) < a := by exact_mod_cast ha
  have : (0 : ℝ) < d := by exact_mod_cast hd
  exact div_pos (mul_pos (by assumption) z.im_pos) (by assumption)

/-- The `q`-parameter of period `1`. -/
lemma qParam_one_eq (w : ℂ) :
    Function.Periodic.qParam 1 w = Complex.exp (2 * Real.pi * Complex.I * w) := by
  simp [Function.Periodic.qParam]

/-- The `q`-series of the sum over `b` of `f ((a z + b)/d)`, regrouped by powers of `q`. -/
lemma hasSum_pair (c : ℕ → ℂ) (f : ℍ → ℂ)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ))
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (z : ℍ) :
    HasSum (fun j : ℕ => (if a ∣ j then (d : ℂ) * c (d * (j / a)) else 0) *
        Function.Periodic.qParam 1 (z : ℂ) ^ j)
      (∑ b ∈ Finset.range d, f (ofComplex (((a : ℂ) * z + b) / d))) := by
  have hpt : ∀ b : ℕ, ((ofComplex (((a : ℂ) * z + b) / d) : ℍ) : ℂ) = ((a : ℂ) * z + b) / d :=
    fun b => by rw [ofComplex_apply_of_im_pos (im_affine_pos a d b ha hd z)]
  have h1 := hasSum_sum (s := Finset.range d)
    (fun b _ => hc (ofComplex (((a : ℂ) * z + b) / d)))
  set X : ℂ := Complex.exp (2 * Real.pi * Complex.I * (a * (z : ℂ) / d)) with hX
  have h2 : (fun m : ℕ => ∑ b ∈ Finset.range d,
      c m * Function.Periodic.qParam 1 ((ofComplex (((a : ℂ) * z + b) / d) : ℍ) : ℂ) ^ m) =
      fun m => c m * X ^ m * (if d ∣ m then (d : ℂ) else 0) := by
    funext m
    simp only [hpt, qParam_one_eq, exp_affine_pow, hX]
    rw [← sum_rootOfUnity_pow d m hd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h2] at h1
  have hinj : Function.Injective (fun m' : ℕ => d * m') := fun x y h => by
    simpa [hd.ne'] using h
  rw [← hinj.hasSum_iff] at h1
  swap
  · intro m hm
    have : ¬ d ∣ m := fun ⟨k, hk⟩ => hm ⟨k, hk.symm⟩
    simp [this]
  have hinj2 : Function.Injective (fun m' : ℕ => a * m') := fun x y h => by
    simpa [ha.ne'] using h
  rw [← hinj2.hasSum_iff]
  swap
  · intro j hj
    have : ¬ a ∣ j := fun ⟨k, hk⟩ => hj ⟨k, hk.symm⟩
    simp [this]
  convert h1 using 1
  funext m'
  simp only [Function.comp_apply, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ ha, hX]
  rw [qParam_one_eq]
  have : Complex.exp (2 * Real.pi * Complex.I * (a * (z : ℂ) / d)) ^ (d * m') =
      Complex.exp (2 * Real.pi * Complex.I * z) ^ (a * m') := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
  rw [this]
  ring

/-- The pairs $(a, d)$ of natural numbers with $ad = n$ and $\gcd(a, N) = 1$. -/
def hermitePairs (N n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p => p.1 * p.2 = n ∧ Nat.gcd p.1 N = 1

/-- Grouping the triples by `(a, d)`. -/
lemma sum_triples (N n : ℕ) (φ : ℤ × ℤ × ℤ → ℂ) :
    ∑ t ∈ (hermiteTriples n).filter (fun t => Int.gcd t.1 N = 1), φ t =
      ∑ p ∈ hermitePairs N n, ∑ b ∈ Finset.range p.2, φ ((p.1 : ℤ), (b : ℤ), (p.2 : ℤ)) := by
  rw [Finset.sum_sigma' (hermitePairs N n) (fun p => Finset.range p.2)
    (fun p b => φ ((p.1 : ℤ), (b : ℤ), (p.2 : ℤ)))]
  refine Finset.sum_bij' (fun t _ => (⟨(t.1.toNat, t.2.2.toNat), t.2.1.toNat⟩ : Σ _ : ℕ × ℕ, ℕ))
    (fun x _ => ((x.1.1 : ℤ), (x.2 : ℤ), (x.1.2 : ℤ))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b, d⟩ h
    simp only [hermiteTriples, hermitePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_Ico, Finset.mem_sigma, Finset.mem_range] at h ⊢
    obtain ⟨⟨⟨⟨ha1, han⟩, ⟨hb0, hbn⟩, ⟨hd1, hdn⟩⟩, had, hbd⟩, hg⟩ := h
    refine ⟨⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, ?_, ?_⟩, by omega⟩
    · have : (a.toNat : ℤ) * d.toNat = n := by
        rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]; exact had
      exact_mod_cast this
    · have : Int.gcd a N = Nat.gcd a.toNat N := by
        conv_lhs => rw [← Int.toNat_of_nonneg (show 0 ≤ a by omega)]
        exact Int.gcd_natCast_natCast _ _
      rw [← this]; exact hg
  · rintro ⟨⟨a, d⟩, b⟩ h
    simp only [hermiteTriples, hermitePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_Ico, Finset.mem_sigma, Finset.mem_range] at h ⊢
    obtain ⟨⟨⟨⟨ha1, han⟩, ⟨hd1, hdn⟩⟩, had, hg⟩, hb⟩ := h
    refine ⟨⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega⟩, ?_, by omega⟩, ?_⟩
    · exact_mod_cast had
    · rw [Int.gcd_natCast_natCast]; exact hg
  · rintro ⟨a, b, d⟩ h
    simp only [hermiteTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_Ico] at h
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨⟨a, d⟩, b⟩ h
    simp
  · rintro ⟨a, b, d⟩ h
    simp only [hermiteTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_Ico] at h
    have e1 : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg (by omega)
    have e2 : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg (by omega)
    have e3 : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg (by omega)
    simp only [e1, e2, e3]

/-- The coefficients of the `q`-series of `T(n) f` in terms of those of `f`. -/
def heckeCoeff (N : ℕ) (k : ℤ) (n : ℕ) (c : ℕ → ℂ) (j : ℕ) : ℂ :=
  (n : ℂ) ^ (2 * k - 1) * ∑ p ∈ hermitePairs N n,
    (p.2 : ℂ) ^ (-2 * k) * (if p.1 ∣ j then (p.2 : ℂ) * c (p.2 * (j / p.1)) else 0)

/-- If `f` has `q`-series with coefficients `c`, then `T(n) f` has `q`-series with coefficients
`heckeCoeff N k n c`. -/
lemma hasSum_heckeOp (N : ℕ) (k : ℤ) (n : ℕ) (c : ℕ → ℂ) (f : ℍ → ℂ)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ)) (z : ℍ) :
    HasSum (fun j : ℕ => heckeCoeff N k n c j * Function.Periodic.qParam 1 (z : ℂ) ^ j)
      (heckeOp N k n f z) := by
  unfold heckeOp
  rw [sum_triples]
  have hP : ∀ p ∈ hermitePairs N n, HasSum
      (fun j : ℕ => (p.2 : ℂ) ^ (-2 * k) * ((if p.1 ∣ j then (p.2 : ℂ) * c (p.2 * (j / p.1)) else 0) *
        Function.Periodic.qParam 1 (z : ℂ) ^ j))
      ((p.2 : ℂ) ^ (-2 * k) * ∑ b ∈ Finset.range p.2, f (ofComplex (((p.1 : ℂ) * z + b) / p.2))) := by
    intro p hp
    simp only [hermitePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    exact (hasSum_pair c f hc p.1 p.2 (by omega) (by omega) z).mul_left _
  have h := (hasSum_sum hP).mul_left ((n : ℂ) ^ (2 * k - 1))
  convert h using 1
  · funext j
    simp only [heckeCoeff, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  · congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [hermitePoint]

/-- The constant coefficient of `T(n) f` vanishes if that of `f` does. -/
lemma heckeCoeff_zero (N : ℕ) (k : ℤ) (n : ℕ) (c : ℕ → ℂ) (h0 : c 0 = 0) :
    heckeCoeff N k n c 0 = 0 := by
  simp [heckeCoeff, h0]

/-- The coefficient of `q` in `T(n) f` is the coefficient of `q^n` in `f`. -/
lemma heckeCoeff_one (N : ℕ) (k : ℤ) {n : ℕ} (hn : 0 < n) (c : ℕ → ℂ) :
    heckeCoeff N k n c 1 = c n := by
  unfold heckeCoeff
  have hmem : ((1 : ℕ), n) ∈ hermitePairs N n := by
    simp [hermitePairs]; omega
  rw [Finset.sum_eq_single ((1 : ℕ), n)]
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [dvd_refl, ↓reduceIte, Nat.div_one, mul_one]
    have key : (n : ℂ) ^ (2 * k - 1) * (n : ℂ) ^ (-2 * k) * n = 1 := by
      rw [← zpow_add₀ hn0, show 2 * k - 1 + -2 * k = -1 by ring, zpow_neg_one, inv_mul_cancel₀ hn0]
    calc (n : ℂ) ^ (2 * k - 1) * ((n : ℂ) ^ (-2 * k) * (↑n * c n))
        = ((n : ℂ) ^ (2 * k - 1) * (n : ℂ) ^ (-2 * k) * n) * c n := by ring
      _ = c n := by rw [key, one_mul]
  · rintro ⟨a, d⟩ hp hne
    simp only [hermitePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    by_cases ha : a ∣ 1
    · exfalso
      have : a = 1 := Nat.dvd_one.mp ha
      subst this
      apply hne
      simp only [one_mul] at hp
      simp [hp.2.1]
    · simp [ha]
  · intro h; exact absurd hmem h

open scoped Manifold in
/-- `T(n)` preserves holomorphy. -/
lemma mdifferentiable_heckeOp (N : ℕ) (k : ℤ) (n : ℕ) {f : ℍ → ℂ} (hf : MDiff f) :
    MDiff (heckeOp N k n f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  set S : Set ℂ := {z | 0 < z.im} with hS
  set T := (hermiteTriples n).filter (fun t => Int.gcd t.1 N = 1) with hT
  let G : ℂ → ℂ := fun w => (n : ℂ) ^ (2 * k - 1) * ∑ t ∈ T, (t.2.2 : ℂ) ^ (-2 * k) *
    ((f ∘ ofComplex) (((t.1 : ℂ) * w + t.2.1) / t.2.2))
  have hG : DifferentiableOn ℂ G S := by
    refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun t ht => ?_) _
    refine DifferentiableOn.const_mul ?_ _
    simp only [hT, hermiteTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_Ico] at ht
    have hd : (t.2.2 : ℂ) ≠ 0 := by
      have : (1 : ℤ) ≤ t.2.2 := ht.1.1.2.2.1
      exact_mod_cast (by omega : t.2.2 ≠ 0)
    have haff : DifferentiableOn ℂ (fun w : ℂ => ((t.1 : ℂ) * w + t.2.1) / t.2.2) S := by
      apply Differentiable.differentiableOn
      fun_prop
    refine hf.comp haff ?_
    intro w hw
    simp only [hS, Set.mem_ofPred_eq] at hw ⊢
    have h1 : (1 : ℤ) ≤ t.1 := ht.1.1.1.1
    have h2 : (1 : ℤ) ≤ t.2.2 := ht.1.1.2.2.1
    have h1' : (0 : ℝ) < t.1 := by exact_mod_cast (by omega : 0 < t.1)
    have h2' : (0 : ℝ) < t.2.2 := by exact_mod_cast (by omega : 0 < t.2.2)
    rw [Complex.div_intCast_im]
    simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re, zero_mul,
      add_zero]
    exact div_pos (mul_pos h1' hw) h2'
  refine hG.congr fun w hw => ?_
  simp only [Function.comp_apply, G, heckeOp, hermitePoint, ofComplex_apply_of_im_pos hw]
  rfl

/-- If `g` is given by a `q`-series with period `1`, then `g (1 +ᵥ τ) = g τ`. -/
lemma periodic_of_hasSum {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : ∀ τ : ℍ, HasSum (fun m => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (g τ)) :
    Function.Periodic (g ∘ ofComplex) 1 := by
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro τ
  have h1 := hg ((1 : ℝ) +ᵥ τ)
  have hq : Function.Periodic.qParam 1 (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) := by
    rw [qParam_one_eq, qParam_one_eq, UpperHalfPlane.coe_vadd]
    simp [mul_add, Complex.exp_add]
  rw [hq] at h1
  exact h1.unique (hg τ)

/-- A bundled function on the upper half plane (only to apply the `FunLike` lemmas of the `q`-expansion
library to plain functions). -/
structure FunWrap where
  /-- The underlying function. -/
  toFun : ℍ → ℂ

instance : FunLike FunWrap ℍ ℂ where
  coe := FunWrap.toFun
  coe_injective a b h := by cases a; cases b; congr

/-- Uniqueness of `q`-expansion coefficients (period `1`) for a plain function. -/
lemma qExpansion_coeff_unique' (g : ℍ → ℂ) {c : ℕ → ℂ}
    (han : AnalyticAt ℂ (cuspFunction 1 g) 0)
    (hgs : ∀ τ : ℍ, HasSum (fun m => c m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion 1 g).coeff m :=
  UpperHalfPlane.qExpansion_coeff_unique (F := FunWrap) ⟨g⟩ one_pos han hgs m

/-- The `q`-expansion of `T(n) f` for a cusp form `f` for any group with strict period `1`. -/
theorem heckeOp_qExpansion_aux {Γ : Subgroup (GL (Fin 2) ℝ)} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    {k : ℤ} (f : CuspForm Γ (2 * k)) (N : ℕ) {n : ℕ} (hn : 0 < n) :
    (qExpansion 1 (heckeOp N k n f)).coeff 0 = 0 ∧
      (qExpansion 1 (heckeOp N k n f)).coeff 1 = (qExpansion 1 f).coeff n := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → ℂ, ∀ m, c m = (qExpansion 1 f).coeff m :=
    ⟨fun m => (qExpansion 1 f).coeff m, fun _ => rfl⟩
  have hc : ∀ τ : ℍ, HasSum (fun m => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ) := by
    intro τ
    simp only [hcdef]
    exact ModularForm.hasSum_qExpansion f one_pos hΓ τ
  have hg := hasSum_heckeOp N k n c f hc
  have hgs : ∀ τ : ℍ, HasSum (fun m => heckeCoeff N k n c m • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (heckeOp N k n f τ) := fun τ => by simpa using hg τ
  have hper := periodic_of_hasSum hg
  have hmd := mdifferentiable_heckeOp N k n (ModularFormClass.holo f)
  have hbd := isBoundedAtImInfty_of_hasSum_qExpansion one_pos hgs
  have han : AnalyticAt ℂ (cuspFunction 1 (heckeOp N k n f)) 0 :=
    analyticAt_cuspFunction_zero one_pos hper hmd hbd
  clear hg hper hmd hbd
  generalize heckeOp N k n f = g at han hgs ⊢
  have hu0 : heckeCoeff N k n c 0 = (qExpansion 1 g).coeff 0 :=
    qExpansion_coeff_unique' g han hgs 0
  have hu1 : heckeCoeff N k n c 1 = (qExpansion 1 g).coeff 1 :=
    qExpansion_coeff_unique' g han hgs 1
  have hc0 : c 0 = 0 := by
    rw [hcdef]; exact CuspFormClass.qExpansion_coeff_zero f one_pos hΓ
  refine ⟨hu0.symm.trans (heckeCoeff_zero N k n c hc0), ?_⟩
  rw [← hcdef n]
  exact hu1.symm.trans (heckeCoeff_one N k hn c)

/-- Milne, *EC*, V.4, p. 211 (running text, "one finds (after a little work) that $T(n) \cdot f = c(n) q + \cdots$"):
for a cusp form $f = \sum_{m \ge 1} c(m) q^m$ of weight $2k$ for $\Gamma_0(N)$ and $n \ge 1$, the $q$-expansion of
$T(n)f$ has constant term $0$ and $q$-coefficient $c(n)$ (Milne states it for $N = 1$). -/
@[kb "milne2006ec" "Ch. V, Section 4 (pdf p. 211): T(n)f = c(n)q + ..."]
theorem heckeOp_qExpansion_coeff_one {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma0 N) (2 * k)) {n : ℕ}
    (hn : 0 < n) :
    (qExpansion 1 (heckeOp N k n f)).coeff 0 = 0 ∧
      (qExpansion 1 (heckeOp N k n f)).coeff 1 = (qExpansion 1 f).coeff n :=
  heckeOp_qExpansion_aux (Γ := (Gamma0 N : Subgroup (GL (Fin 2) ℝ))) (by simp) f N hn

/-- **Theorem 4.8 for $N = 1$** (Milne, *EC*, V, p. 211: "This proves Theorem 4.8 in the case $N = 1$"): if a cusp
form $f = \sum c(n) q^n$ of weight $2k$ for $\mathrm{SL}_2(\mathbb Z)$ satisfies $T(n) f = \lambda(n) f$ for all
$n \ge 1$, then $c(n) = \lambda(n) c(1)$. -/
@[kb "milne2006ec" "Ch. V, Theorem 4.8 for N = 1 (pdf p. 211)"]
theorem thm_4_8_levelOne {k : ℤ} (f : CuspForm 𝒮ℒ (2 * k)) (eig : ℕ → ℂ)
    (hf : ∀ n, 0 < n → heckeOp 1 k n f = eig n • ⇑f) (n : ℕ) (hn : 0 < n) :
    (qExpansion 1 f).coeff n = eig n * (qExpansion 1 f).coeff 1 := by
  have hΓ : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have h := (heckeOp_qExpansion_aux hΓ f 1 hn).2
  rw [hf n hn, qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ)] at h
  simpa using h.symm

end NumberFieldKB.MilneEC.Vb
