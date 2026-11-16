import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch1Functions

/-!
# Milne, Elliptic Curves, Chapter IV §11: constant elliptic curves over function fields

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Section 11 ("Elliptic curves and
sphere packings"), Proposition 11.1, Theorem 11.2 and Proposition 11.4, pdf pp. 176–179.

Let $k$ be a finite field with $Q$ elements and $K = k(C)$ the function field of a nonsingular projective curve $C$
over $k$ of genus $g$.  Milne writes $Z(C, T) = \prod_{i=1}^{2g}(1 - \omega_i T)/((1 - T)(1 - QT))$ with
$|\omega_i| = Q^{1/2}$, and, for an elliptic curve $E$ over $k$ (a *constant* elliptic curve over $K$),
$Z(E, T) = (1 - \alpha_1 T)(1 - \alpha_2 T)/((1 - T)(1 - QT))$.

## Formalization
* The curve $C$ is its function field `K` (an `Algebra k K`); its points over $\mathbb F_{Q^m}$ are counted through the
  places of `K` (the `PrimeDivisor`s of `Ch1Functions`): `pointCount k K m` $= \sum_{d \mid m} d \cdot a_d$, $a_d$ the
  number of places of degree $d$.  This is the standard count of $\#C(\mathbb F_{Q^m})$ for a curve with function
  field $K$.
* `IsWeilMultiset k K ω`: $\omega$ is a multiset of $2g$ complex numbers of absolute value $Q^{1/2}$ with
  $\#C(\mathbb F_{Q^m}) = 1 + Q^m - \sum_i \omega_i^m$ for all $m \ge 1$, i.e. the reciprocal roots of the numerator
  of $Z(C, T)$ (Weil's theorem; `WeilCurve` names its existence).
* `frobRoots E`: the roots $\alpha_1, \alpha_2$ of $X^2 - aX + Q$, $a = Q + 1 - \#E(k)$, so that
  $(1 - \alpha_1 T)(1 - \alpha_2 T) = 1 - aT + QT^2$ is the numerator of $Z(E, T)$ (Milne IV 9).
* `mordellWeilRank`: the rank of $E(K)$, $\dim_{\mathbb Q} E(K) \otimes \mathbb Q$.
* `Theorem11_2a`: **Theorem 11.2, part (a) of 11.1** (Tate 1966), as a named statement: the rank of $E(K)$ is the
  number of pairs $(i, j)$ with $\alpha_i = \omega_j$.

## Proved
* `prop_11_4_a`: **Proposition 11.4(a)** from `Theorem11_2a`: for $Q = q^2$, a curve of genus $q(q-1)/2$ with
  $q^3 + 1$ points over $\mathbb F_{q^2}$ (Lemma 11.3) and $E$ with $(q+1)^2$ points, the rank of $E(K)$ is
  $2q(q-1)$.  Milne's argument "all $\alpha_i$ and $\omega_j$ equal $-q$" is proved: the $\omega_j$ by the equality
  case of the triangle inequality (`eq_neg_of_sum_eq`, Milne's proof of 11.3(c)), the $\alpha_i$ from the
  polynomial $(X + q)^2$.
* `prop_11_4_d`: **Proposition 11.4(d)** from (b) and (c): $\gamma(L) = m(L)/\operatorname{disc}(L)^{1/r} \ge
  2(q-1)/\sqrt q$.

## Not formalized (recorded)
* Part (b) of 11.1 and 11.2 (Milne 1968), Proposition 11.4(b), (c), and the equivalence of 11.1 with the conjecture
  of Birch and Swinnerton-Dyer: they need the Tate–Shafarevich group of $E$ over $K$, the Néron–Tate pairing over a
  function field and the $L$-function $L(E/K, s)$, none of which exists in Mathlib or here.  In `prop_11_4_d` the
  quantities $m(L)$, $\operatorname{disc}(L)$ and $[\text{Ш}]$ are therefore real numbers satisfying (b) and (c).
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace NumberFieldKB.MilneEC.FunctionFieldBSD

variable (k : Type) [Field k] [Fintype k] (K : Type) [Field K] [Algebra k K]

/-- The number $a_d$ of places of degree $d$ of the function field `K` over `k`. -/
noncomputable def placesOfDeg (d : ℕ) : ℕ := Nat.card {P : PrimeDivisor k K // P.deg = d}

/-- $\#C(\mathbb F_{Q^m}) = \sum_{d \mid m} d\, a_d$: the number of points over the extension of degree `m` of the
curve with function field `K`. -/
noncomputable def pointCount (m : ℕ) : ℕ := ∑ d ∈ m.divisors, d * placesOfDeg k K d

/-- $\omega$ is the multiset of reciprocal roots of the numerator of $Z(C, T)$ (pdf p. 176): $2g$ complex numbers of
absolute value $Q^{1/2}$ with $\#C(\mathbb F_{Q^m}) = 1 + Q^m - \sum_i \omega_i^m$ for all $m \geq 1$. -/
@[kb "milne2006ec" "Ch. IV, §11, the numbers ω_i of Z(C,T), pdf p. 176"]
def IsWeilMultiset (ω : Multiset ℂ) : Prop :=
  (Multiset.card ω : ℤ) = 2 * genus k K ∧
  (∀ z ∈ ω, ‖z‖ = Real.sqrt (Fintype.card k)) ∧
  ∀ m : ℕ, 1 ≤ m → (pointCount k K m : ℂ) = 1 + (Fintype.card k : ℂ) ^ m - (ω.map (· ^ m)).sum

/-- **Weil's theorem for curves over finite fields** (rationality and Riemann hypothesis, used on pdf p. 176), as a
named statement (Weil 1948): the function field of a nonsingular projective curve over a finite field has its numbers
$\omega_i$. -/
@[kb "milne2006ec" "Ch. IV, §11, Z(C,T) and |ω_i| = q^(1/2), pdf p. 176 (input)"]
structure WeilCurve : Prop where
  exists_weil : ∃ ω : Multiset ℂ, IsWeilMultiset k K ω

/-- The numbers $\alpha_1, \alpha_2$ of $Z(E, T)$ (pdf p. 176): the roots of $X^2 - aX + Q$, where
$a = Q + 1 - \#E(k)$. -/
@[kb "milne2006ec" "Ch. IV, §11, the numbers α_i of Z(E,T), pdf p. 176"]
noncomputable def frobRoots (E : WeierstrassCurve k) : Multiset ℂ :=
  (X ^ 2 - C ((Fintype.card k : ℂ) + 1 - Nat.card E.toAffine.Point) * X + C (Fintype.card k : ℂ)).roots

/-- The number of pairs $(i, j)$ with $\alpha_i = \omega_j$, counted with multiplicity. -/
noncomputable def pairCount (α ω : Multiset ℂ) : ℕ :=
  Multiset.card ((α ×ˢ ω).filter fun x => x.1 = x.2)

open Classical in
/-- The rank of the Mordell–Weil group $E(K)$ of the constant curve $E$ over $K$: $\dim_{\mathbb Q} E(K)\otimes
\mathbb Q$. -/
noncomputable def mordellWeilRank (E : WeierstrassCurve k) : ℕ :=
  Module.finrank ℚ (TensorProduct ℤ ℚ (E.toAffine⁄K).Point)

/-- `K` is a function field of one variable over `k` with field of constants `k`: a finite extension of a rational
function field $k(t)$ in which `k` is algebraically closed. -/
def IsCurveFunctionField : Prop :=
  (∃ t : K, Transcendental k t ∧ FiniteDimensional (IntermediateField.adjoin k {t}) K) ∧
  ∀ x : K, IsAlgebraic k x → x ∈ Set.range (algebraMap k K)

/-- **Theorem 11.2, statement (a) of Proposition 11.1** (pdf p. 177), as a named statement (Tate 1966): for a constant
elliptic curve $E$ over the function field $K$ of a curve over a finite field, the rank of $E(K)$ is the number of
pairs $(i, j)$ with $\alpha_i = \omega_j$. -/
@[kb "milne2006ec" "Ch. IV, Theorem 11.2 (statement (a) of Proposition 11.1), pdf p. 177 (input)"]
structure Theorem11_2a : Prop where
  rank_eq : ∀ (k : Type) [Field k] [Fintype k] (K : Type) [Field K] [Algebra k K],
    IsCurveFunctionField k K → ∀ (E : WeierstrassCurve k) [E.IsElliptic] (ω : Multiset ℂ),
      IsWeilMultiset k K ω → mordellWeilRank k K E = pairCount (frobRoots k E) ω

/-- Equality case of the triangle inequality: complex numbers of absolute value `r` summing to $-nr$ are all
$-r$. -/
theorem eq_neg_of_sum_eq (s : Multiset ℂ) (r : ℝ) (hs : ∀ z ∈ s, ‖z‖ = r)
    (hsum : s.sum = -(Multiset.card s * r : ℝ)) : ∀ z ∈ s, z = -(r : ℂ) := by
  -- each `re z + r` is `≥ 0`, and they sum to `0`
  have hre : ∀ z ∈ s, 0 ≤ z.re + r := by
    intro z hz
    have := Complex.abs_re_le_norm z
    rw [hs z hz] at this
    linarith [neg_abs_le z.re]
  have hsumre : (s.map fun z => z.re + r).sum = 0 := by
    have h1 : (s.map fun z => z.re + r).sum = (s.map Complex.re).sum + Multiset.card s * r := by
      rw [Multiset.sum_map_add]
      simp
    have h2 : (s.map Complex.re).sum = s.sum.re :=
      (map_multiset_sum Complex.reAddGroupHom s).symm
    rw [h1, h2, hsum]
    simp
  intro z hz
  have hz0 : z.re + r = 0 := by
    have := Multiset.single_le_sum (s := s.map fun z => z.re + r) (by simpa using hre) _
      (Multiset.mem_map_of_mem _ hz)
    linarith [hre z hz]
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hs z hz] at hnorm
  have hre' : z.re = -r := by linarith
  rw [hre'] at hnorm
  have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
  apply Complex.ext <;> simp [hre', him]

/-- The numbers $\alpha_i$ for a curve with $(q+1)^2$ points over a field with $q^2$ elements (pdf p. 179): both
equal $-q$. -/
theorem frobRoots_eq_of_card (E : WeierstrassCurve k) (q : ℕ) (hk : Fintype.card k = q ^ 2)
    (hE : Nat.card E.toAffine.Point = (q + 1) ^ 2) :
    frobRoots k E = Multiset.replicate 2 (-(q : ℂ)) := by
  have hpoly : (X ^ 2 - C ((Fintype.card k : ℂ) + 1 - Nat.card E.toAffine.Point) * X +
      C (Fintype.card k : ℂ) : ℂ[X]) = (X - C (-(q : ℂ))) ^ 2 := by
    rw [hk, hE]
    simp only [map_neg, sub_neg_eq_add, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    have : ((q : ℂ) ^ 2 + 1 - ((q : ℂ) + 1) ^ 2) = -2 * q := by ring
    rw [this]
    simp only [map_mul, map_neg, map_pow, map_ofNat]
    ring
  rw [frobRoots, hpoly, Polynomial.roots_pow, Polynomial.roots_X_sub_C]
  simp [Multiset.nsmul_singleton]

theorem pairCount_replicate (a : ℂ) (m n : ℕ) :
    pairCount (Multiset.replicate m a) (Multiset.replicate n a) = m * n := by
  unfold pairCount
  rw [Multiset.filter_eq_self.2, Multiset.card_product, Multiset.card_replicate, Multiset.card_replicate]
  intro x hx
  rw [Multiset.mem_product, Multiset.mem_replicate, Multiset.mem_replicate] at hx
  rw [hx.1.2, hx.2.2]

/-- The numbers $\omega_i$ of the curve of Lemma 11.3 (pdf p. 179, proof of 11.3(c)): if $Q = q^2$, the genus is
$q(q-1)/2$ and $\#C(\mathbb F_{q^2}) = q^3 + 1$, then every $\omega_i$ equals $-q$. -/
@[kb "milne2006ec" "Ch. IV, proof of Lemma 11.3(c): all ω_i = −q, pdf p. 179"]
theorem weil_eq_replicate (q : ℕ) (hk : Fintype.card k = q ^ 2)
    (hg : 2 * genus k K = q * ((q : ℤ) - 1)) (hN : pointCount k K 1 = q ^ 3 + 1) (ω : Multiset ℂ)
    (hω : IsWeilMultiset k K ω) : ω = Multiset.replicate (q * (q - 1)) (-(q : ℂ)) := by
  obtain ⟨hcard, hnorm, htr⟩ := hω
  have hsq : Real.sqrt (Fintype.card k) = q := by
    rw [hk, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)]
  have hcard' : Multiset.card ω = q * (q - 1) := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq; simp at hg; omega
    · have : ((q * (q - 1) : ℕ) : ℤ) = q * ((q : ℤ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega)]; simp
      omega
  rw [hsq] at hnorm
  have h1 := htr 1 le_rfl
  rw [hN, hk] at h1
  simp only [pow_one, Multiset.map_id'] at h1
  have hsum : ω.sum = -((Multiset.card ω : ℝ) * (q : ℝ) : ℝ) := by
    rw [hcard']
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      push_cast at h1 ⊢
      linear_combination h1
    · rw [Nat.cast_mul, Nat.cast_sub (by omega)]
      push_cast at h1 ⊢
      linear_combination h1
  have hall := eq_neg_of_sum_eq ω q hnorm hsum
  rw [← hcard']
  exact Multiset.eq_replicate_card.2 hall

/-- **Proposition 11.4(a)** (pdf p. 179), from Tate's theorem (`Theorem11_2a`): let $k$ have $q^2$ elements, `K` the
function field of a curve of genus $q(q-1)/2$ with $q^3 + 1$ points over $k$ (Lemma 11.3 for the curve
$X^{q+1} + Y^{q+1} + Z^{q+1} = 0$), and $E$ an elliptic curve over $k$ with $(q + 1)^2$ points.  Then the rank of
$E(K)$ is $2q(q-1)$. -/
@[kb "milne2006ec" "Ch. IV, Proposition 11.4(a), pdf p. 179"]
theorem prop_11_4_a (hT : Theorem11_2a) (hW : WeilCurve k K) (hK : IsCurveFunctionField k K) (q : ℕ)
    (hk : Fintype.card k = q ^ 2) (hg : 2 * genus k K = q * ((q : ℤ) - 1))
    (hN : pointCount k K 1 = q ^ 3 + 1) (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Nat.card E.toAffine.Point = (q + 1) ^ 2) :
    mordellWeilRank k K E = 2 * q * (q - 1) := by
  obtain ⟨ω, hω⟩ := hW.exists_weil
  rw [hT.rank_eq k K hK E ω hω, frobRoots_eq_of_card k E q hk hE,
    weil_eq_replicate k K q hk hg hN ω hω, pairCount_replicate]
  ring

/-- **Proposition 11.4(d)** (pdf p. 179) from (b) and (c): if $L$ has rank $r = 2q(q-1)$, minimal norm
$m(L) \geq 2(q-1)$ and $[\text{Ш}]\cdot\operatorname{disc}(L) = q^{q(q-1)}$ with $[\text{Ш}] \geq 1$, then
$\gamma(L) = m(L)/\operatorname{disc}(L)^{1/r} \geq 2(q-1)/\sqrt q$. -/
@[kb "milne2006ec" "Ch. IV, Proposition 11.4(d) (from (b) and (c)), pdf p. 179"]
theorem prop_11_4_d (q : ℕ) (hq : 2 ≤ q) (m disc sha : ℝ) (hdisc : 0 < disc) (hsha : 1 ≤ sha)
    (hb : 2 * ((q : ℝ) - 1) ≤ m) (hc : sha * disc = (q : ℝ) ^ (q * (q - 1))) :
    2 * ((q : ℝ) - 1) / Real.sqrt q ≤ m / disc ^ ((1 : ℝ) / (2 * q * (q - 1) : ℕ)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hn : 0 < q * (q - 1) := Nat.mul_pos (by omega) (by omega)
  have hn' : (0 : ℝ) < (q * (q - 1) : ℕ) := by exact_mod_cast hn
  -- `disc ≤ q^(q(q-1))`
  have hdle : disc ≤ (q : ℝ) ^ (q * (q - 1)) := by
    rw [← hc]; nlinarith
  -- `disc^(1/r) ≤ √q`
  have hroot : disc ^ ((1 : ℝ) / (2 * q * (q - 1) : ℕ)) ≤ Real.sqrt q := by
    have hr : ((2 * q * (q - 1) : ℕ) : ℝ) = 2 * ((q * (q - 1) : ℕ) : ℝ) := by push_cast; ring
    calc disc ^ ((1 : ℝ) / (2 * q * (q - 1) : ℕ))
        ≤ ((q : ℝ) ^ (q * (q - 1))) ^ ((1 : ℝ) / (2 * q * (q - 1) : ℕ)) :=
          Real.rpow_le_rpow hdisc.le hdle (by positivity)
      _ = Real.sqrt q := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, hr, Real.sqrt_eq_rpow]
          congr 1
          field_simp
  have hpos : 0 < disc ^ ((1 : ℝ) / (2 * q * (q - 1) : ℕ)) := Real.rpow_pos_of_pos hdisc _
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hq1 : (0 : ℝ) ≤ 2 * ((q : ℝ) - 1) := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  calc 2 * ((q : ℝ) - 1) / Real.sqrt q ≤ 2 * ((q : ℝ) - 1) / disc ^ ((1 : ℝ) / (2 * q * (q - 1) : ℕ)) :=
        div_le_div_of_nonneg_left hq1 hpos hroot
    _ ≤ m / disc ^ ((1 : ℝ) / (2 * q * (q - 1) : ℕ)) := div_le_div_of_nonneg_right hb hpos.le

end NumberFieldKB.MilneEC.FunctionFieldBSD
