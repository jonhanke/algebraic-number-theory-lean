import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.NumberTheory.SumPrimeReciprocals
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch4VarietyZetaWeierstrass

/-!
# Milne, Elliptic Curves, Chapter IV §10: convergence of $\zeta(V, s)$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Section 10, pdf p. 170:
the product $\zeta(V, s) = \prod_{p \text{ good}} \zeta(V_p, s)$ converges for
$\Re s > \dim V + 1$.

The definitions (`numPoints`, `localZeta`, `varietyZeta`) are those of `Ch4VarietyZeta.lean`, unchanged. Here
`varietyZetaFactor F s p` is the factor at $p$ of the product defining `varietyZeta` (`varietyZeta_eq_tprod`, by
definition), and "converges" means: the family of factors is multipliable in $\mathbb C$ and the product is nonzero.

## Proved
* `numPoints_le_ambient`: the trivial bound $\#V_p(\mathbb F_q) \le \#\mathbb P^n(\mathbb F_q) \le 2q^n$.
* `varietyZeta_converges`: the product converges for $\Re s > n + 1$, every variety in $\mathbb P^n$ (the bound by
  the ambient dimension).
* `numPoints_le_hypersurface`: if some equation reduces to a nonzero polynomial of degree at most $D$, then
  $\#V_p(\mathbb F_q) \le 2Dq^{n-1}$ (Schwartz–Zippel on the affine cone).
* `varietyZeta_converges_of_pos`: with at least one equation ($r \ge 1$), the product converges for $\Re s > n$.
  For a hypersurface ($r = 1$, $\dim V = n - 1$) this is Milne's $\Re s > \dim V + 1$.
* `weierstrassZeta_converges`: for an integral Weierstrass equation (a plane cubic, $\dim V = 1$) the product
  converges for $\Re s > 2$.

For a complete intersection of codimension $r \ge 2$ Milne's abscissa $\dim V + 1 = n - r + 1$ needs the bound
$\#V(\mathbb F_q) = O(q^{\dim V})$ (Lang–Weil, upper half), which is not formalized.
-/

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace NumberFieldKB.MilneEC.VarietyZeta

open Classical in
/-- The factor at $p$ of $\zeta(V, s)$: $\zeta(V_p, s)$ for a good prime $p$ (the reduction computed from the
chosen primitive integral scaling, as in `varietyZeta`), and $1$ for a bad prime. -/
noncomputable def varietyZetaFactor {n r : ℕ} (F : Fin r → MvPolynomial (Fin (n + 1)) ℚ) (s : ℂ)
    (p : Nat.Primes) : ℂ :=
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  if h : HasGoodReductionAt F p then
    localZeta p (fun i => (h.choose i).map (Int.castRingHom (ZMod p))) s
  else 1

/-- `varietyZeta` is the product of the factors `varietyZetaFactor` (by definition). -/
theorem varietyZeta_eq_tprod {n r : ℕ} (F : Fin r → MvPolynomial (Fin (n + 1)) ℚ) (s : ℂ) :
    varietyZeta F s = ∏' p : Nat.Primes, varietyZetaFactor F s p := rfl

/-- **The trivial bound** $\#V_p(\mathbb F_{p^m}) \le \#\mathbb P^n(\mathbb F_{p^m}) \le 2p^{mn}$, $m \ge 1$. -/
theorem numPoints_le_ambient {n r : ℕ} (p : ℕ) [Fact p.Prime]
    (F : Fin r → MvPolynomial (Fin (n + 1)) (ZMod p)) {m : ℕ} (hm : 1 ≤ m) :
    (numPoints p F m : ℝ) ≤ 2 * (p : ℝ) ^ (m * n) := by
  have hq : 1 < Nat.card (GaloisField p m) := Finite.one_lt_card
  have hcard : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m (by omega)
  have h1 : numPoints p F m ≤ Nat.card (ℙ (GaloisField p m) (Fin (n + 1) → GaloisField p m)) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have h2 := Projectivization.card' (GaloisField p m) (Fin (n + 1) → GaloisField p m)
  have h3 : Nat.card (Fin (n + 1) → GaloisField p m) = (p ^ m) ^ (n + 1) := by
    simp [Nat.card_fun, hcard]
  rw [h3, hcard] at h2
  set q := p ^ m with hqdef
  have hq2 : 2 ≤ q := by rw [hcard] at hq; omega
  set P := Nat.card (ℙ (GaloisField p m) (Fin (n + 1) → GaloisField p m))
  have h4 : P ≤ 2 * q ^ n := by
    have hqn : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
    have hqq : q ^ (n + 1) = q * q ^ n := by ring
    by_contra hc
    have hc' : 2 * q ^ n + 1 ≤ P := by omega
    have : (2 * q ^ n + 1) * (q - 1) ≤ P * (q - 1) := Nat.mul_le_mul_right _ hc'
    zify [(by omega : 1 ≤ q)] at this h2 hqq
    have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have hq2' : (2 : ℤ) ≤ q := by exact_mod_cast hq2
    nlinarith
  calc (numPoints p F m : ℝ) ≤ (P : ℝ) := by exact_mod_cast h1
    _ ≤ ((2 * q ^ n : ℕ) : ℝ) := by exact_mod_cast h4
    _ = 2 * (p : ℝ) ^ (m * n) := by
      rw [hqdef]; push_cast; ring

/-- Local bound: if $\#V_p(\mathbb F_{p^m}) \le K p^{me}$ for $m \ge 1$ and $\Re s > e + 1$, the exponent of
$\zeta(V_p, s)$ has norm at most $2K p^{-(\Re s - e)}$. -/
lemma localExponent_norm_le (p : ℕ) [Fact p.Prime] {n r : ℕ}
    (F : Fin r → MvPolynomial (Fin (n + 1)) (ZMod p)) (s : ℂ) (e : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hs : (e : ℝ) + 1 < s.re) (hN : ∀ m : ℕ, 1 ≤ m → (numPoints p F m : ℝ) ≤ K * (p : ℝ) ^ (m * e)) :
    ‖∑' m : ℕ, (numPoints p F m : ℂ) * ((p : ℂ) ^ (-s)) ^ m / m‖ ≤ 2 * K * (p : ℝ) ^ (-(s.re - e)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hp1 : (1 : ℝ) < p := by linarith
  set y : ℝ := (p : ℝ) ^ (-(s.re - e)) with hydef
  have hy0 : 0 ≤ y := by positivity
  have hy_eq : y = (p : ℝ) ^ e * (p : ℝ) ^ (-s.re) := by
    rw [hydef, show -(s.re - e) = (e : ℝ) + -s.re by ring, Real.rpow_add (by linarith), Real.rpow_natCast]
  have hyle : y ≤ 1 / 2 := by
    have h1 : y ≤ (p : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    rw [Real.rpow_neg_one] at h1
    have : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) hp2
    linarith
  have hnz : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (Fact.out : p.Prime).pos]; simp
  have hterm : ∀ m : ℕ, ‖(numPoints p F m : ℂ) * ((p : ℂ) ^ (-s)) ^ m / m‖ ≤
      if m = 0 then 0 else K * y ^ m := by
    intro m
    by_cases hm : m = 0
    · simp [hm]
    · rw [if_neg hm]
      have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      rw [norm_div, norm_mul, norm_pow, hnz]
      simp only [Complex.norm_natCast]
      have hz0 : 0 ≤ ((p : ℝ) ^ (-s.re)) ^ m := by positivity
      calc (numPoints p F m : ℝ) * ((p : ℝ) ^ (-s.re)) ^ m / m
          ≤ (numPoints p F m : ℝ) * ((p : ℝ) ^ (-s.re)) ^ m := by
            apply div_le_self (by positivity) hmR
        _ ≤ K * (p : ℝ) ^ (m * e) * ((p : ℝ) ^ (-s.re)) ^ m :=
            mul_le_mul_of_nonneg_right (hN m hm1) hz0
        _ = K * y ^ m := by
            rw [hy_eq, mul_pow, ← pow_mul, mul_comm e m]; ring
  have hsum : HasSum (fun m : ℕ => if m = 0 then (0 : ℝ) else K * y ^ m) (K * y * (1 - y)⁻¹) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, if_pos, sub_zero, Nat.add_one_ne_zero, if_false]
    have := (hasSum_geometric_of_lt_one hy0 (by linarith)).mul_left (K * y)
    convert this using 2 with k
    ring
  refine (tsum_of_norm_bounded hsum hterm).trans ?_
  have h1y : (1 - y)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have : 0 ≤ K * y := by positivity
  nlinarith

open Classical in
/-- The exponent of the factor at `p` of `varietyZeta`: the logarithm of `varietyZetaFactor`. -/
noncomputable def zetaExponent {n r : ℕ} (F : Fin r → MvPolynomial (Fin (n + 1)) ℚ) (s : ℂ)
    (p : Nat.Primes) : ℂ :=
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  if h : HasGoodReductionAt F p then
    ∑' m : ℕ, (numPoints p (fun i => (h.choose i).map (Int.castRingHom (ZMod p))) m : ℂ) *
      ((p : ℂ) ^ (-s)) ^ m / m
  else 0

lemma varietyZetaFactor_eq_cexp {n r : ℕ} (F : Fin r → MvPolynomial (Fin (n + 1)) ℚ) (s : ℂ)
    (p : Nat.Primes) : varietyZetaFactor F s p = Complex.exp (zetaExponent F s p) := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  unfold varietyZetaFactor zetaExponent
  by_cases h : HasGoodReductionAt F p
  · simp only [dif_pos h, localZeta]
  · simp only [dif_neg h, Complex.exp_zero]

/-- General convergence criterion: a uniform bound $\#V_p(\mathbb F_{p^m}) \le K p^{me}$ at good primes gives
convergence for $\Re s > e + 1$. -/
lemma converges_of_bound {n r : ℕ} (F : Fin r → MvPolynomial (Fin (n + 1)) ℚ) {s : ℂ} (e : ℕ) (K : ℝ)
    (hK : 0 ≤ K) (hs : (e : ℝ) + 1 < s.re)
    (hN : ∀ (p : ℕ) [Fact p.Prime] (h : HasGoodReductionAt F p) (m : ℕ), 1 ≤ m →
      (numPoints p (fun i => (h.choose i).map (Int.castRingHom (ZMod p))) m : ℝ) ≤
        K * (p : ℝ) ^ (m * e)) :
    Multipliable (varietyZetaFactor F s) ∧ varietyZeta F s ≠ 0 := by
  have hbound : ∀ p : Nat.Primes, ‖zetaExponent F s p‖ ≤ 2 * K * ((p : ℕ) : ℝ) ^ (-(s.re - e)) := by
    intro p
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    unfold zetaExponent
    by_cases h : HasGoodReductionAt F p
    · simp only [dif_pos h]
      exact localExponent_norm_le p _ s e K hK hs (hN p h)
    · simp only [dif_neg h, norm_zero]
      have : 0 ≤ ((p : ℕ) : ℝ) ^ (-(s.re - e)) := by positivity
      positivity
  have hsumm : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(s.re - e))) := by
    have h1 : Summable (fun k : ℕ => (k : ℝ) ^ (-(s.re - e))) :=
      Real.summable_nat_rpow.2 (by linarith)
    exact h1.comp_injective Nat.Primes.coe_nat_injective
  have hA : Summable (zetaExponent F s) :=
    Summable.of_norm_bounded (hsumm.mul_left (2 * K)) (fun p => by
      simpa [mul_assoc] using hbound p)
  have hprod := hA.hasSum.cexp
  have hfun : (Complex.exp ∘ zetaExponent F s) = varietyZetaFactor F s := by
    funext p; exact (varietyZetaFactor_eq_cexp F s p).symm
  rw [hfun] at hprod
  refine ⟨hprod.multipliable, ?_⟩
  rw [varietyZeta_eq_tprod, hprod.tprod_eq]
  exact Complex.exp_ne_zero _

/-- **D115, the bound by the ambient dimension** (Milne pdf p. 170): $\zeta(V, s)$ converges for $\Re s > n + 1$, for
every variety in $\mathbb P^n$: the factors are multipliable and the product is nonzero. -/
@[kb "milne2006ec" "Ch. IV, §10, convergence of ζ(V, s) (ambient bound), pdf p. 170"]
theorem varietyZeta_converges {n r : ℕ} (F : Fin r → MvPolynomial (Fin (n + 1)) ℚ) {s : ℂ}
    (hs : (n : ℝ) + 1 < s.re) :
    Multipliable (varietyZetaFactor F s) ∧ varietyZeta F s ≠ 0 :=
  converges_of_bound F n 2 (by norm_num) hs (fun p _ _ m hm => by
    have := numPoints_le_ambient p (fun i => ((‹HasGoodReductionAt F p›).choose i).map
      (Int.castRingHom (ZMod p))) hm
    simpa [mul_comm] using this)

lemma eval_smul_of_isHomogeneous {K : Type*} [CommRing K] {σ : Type*} [Fintype σ] {φ : MvPolynomial σ K}
    {d : ℕ} (hφ : φ.IsHomogeneous d) (u : K) (x : σ → K) : eval (u • x) φ = u ^ d * eval x φ := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hw := hφ (mem_support_iff.1 hs)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have : ∑ i ∈ s.support, s i = d := by simpa [Finsupp.weight_apply, Finsupp.sum] using hw
  rw [this]; ring

/-- **The hypersurface bound for a homogeneous equation**: if `F i` is a nonzero homogeneous polynomial of degree
`d`, then $\#V_p(\mathbb F_{p^m}) \le 2dp^{m(n-1)}$ for $m \ge 1$, $n \ge 1$. -/
lemma numPoints_le_hypersurface_of_homogeneous {n r : ℕ} (hn : 1 ≤ n) (p : ℕ) [Fact p.Prime]
    (F : Fin r → MvPolynomial (Fin (n + 1)) (ZMod p)) (i : Fin r) (hFi : F i ≠ 0) {d : ℕ}
    (hd : (F i).IsHomogeneous d) {m : ℕ} (hm : 1 ≤ m) :
    (numPoints p F m : ℝ) ≤ 2 * d * (p : ℝ) ^ (m * (n - 1)) := by
  classical
  set K := GaloisField p m
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ m := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p m (by omega)
  set q := p ^ m with hqdef
  have hq2 : 2 ≤ q := by
    have := (Fact.out : p.Prime).two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ m := Nat.pow_le_pow_right (by omega) hm
  set Fk : MvPolynomial (Fin (n + 1)) K := (F i).map (algebraMap (ZMod p) K) with hFk
  have hFk0 : Fk ≠ 0 := by
    intro h
    apply hFi
    exact MvPolynomial.map_injective _ (algebraMap (ZMod p) K).injective (by rw [← hFk, h, map_zero])
  have hFkh : Fk.IsHomogeneous d := hd.map _
  have hev : ∀ x : Fin (n + 1) → K, eval x Fk = aeval x (F i) := fun x => by
    rw [hFk, eval_map, aeval_def]
  set Z : Finset (Fin (n + 1) → K) :=
    (Fintype.piFinset fun _ => (Finset.univ : Finset K)).filter (fun x => eval x Fk = 0) with hZ
  have hZcard : Z.card ≤ d * q ^ n := by
    have h := schwartz_zippel_totalDegree hFk0 (Finset.univ : Finset K)
    rw [← hZ] at h
    simp only [Finset.card_univ, hcard] at h
    have hq0 : (0 : NNRat) < (q : NNRat) := by exact_mod_cast (by omega : 0 < q)
    rw [div_le_div_iff₀ (by positivity) hq0] at h
    have h' : Z.card * q ≤ Fk.totalDegree * q ^ (n + 1) := by exact_mod_cast h
    have h'' : Z.card * q ≤ (d * q ^ n) * q := by
      calc Z.card * q ≤ Fk.totalDegree * q ^ (n + 1) := h'
        _ ≤ d * q ^ (n + 1) := Nat.mul_le_mul_right _ hFkh.totalDegree_le
        _ = (d * q ^ n) * q := by ring
    exact Nat.le_of_mul_le_mul_right h'' (by omega)
  -- the injection from (points × units) into `Z`
  have hinj : Nat.card ({P : ℙ K (Fin (n + 1) → K) // ∀ j, aeval P.rep (F j) = 0} × Kˣ) ≤ Z.card := by
    have : Nat.card ({P : ℙ K (Fin (n + 1) → K) // ∀ j, aeval P.rep (F j) = 0} × Kˣ) ≤
        Nat.card (Z : Set (Fin (n + 1) → K)) := by
      refine Nat.card_le_card_of_injective
        (fun a => ⟨(a.2 : K) • a.1.1.rep, ?_⟩) ?_
      · simp only [hZ, Finset.coe_filter, Fintype.mem_piFinset, Finset.mem_univ, implies_true,
          true_and, Set.mem_setOf_eq]
        rw [eval_smul_of_isHomogeneous hFkh, hev, a.1.2 i, mul_zero]
      · rintro ⟨⟨P, hP⟩, u⟩ ⟨⟨P', hP'⟩, u'⟩ h
        simp only [Subtype.mk.injEq] at h
        have hPP : P = P' := by
          rw [← Projectivization.mk_rep P, ← Projectivization.mk_rep P', Projectivization.mk_eq_mk_iff']
          refine ⟨(u⁻¹ * u' : Kˣ), ?_⟩
          have h2 : (u' : K) • P'.rep = (u : K) • P.rep := h.symm
          have h3 : ((u⁻¹ * u' : Kˣ) : K) • P'.rep = P.rep := by
            rw [Units.val_mul, mul_smul, h2, ← mul_smul]; simp
          exact h3
        subst hPP
        have : u = u' := by
          apply Units.ext
          exact smul_left_injective K P.rep_nonzero h
        rw [this]
    simpa using this
  have hN : numPoints p F m * (q - 1) ≤ Z.card := by
    have e1 : Nat.card ({P : ℙ K (Fin (n + 1) → K) // ∀ j, aeval P.rep (F j) = 0} × Kˣ) =
        numPoints p F m * (q - 1) := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Kˣ), Fintype.card_units, hcard]
      rfl
    rw [← e1]; exact hinj
  have hqn : q ^ n = q * q ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h5 : numPoints p F m * (q - 1) ≤ (2 * d * q ^ (n - 1)) * (q - 1) := by
    calc numPoints p F m * (q - 1) ≤ d * q ^ n := hN.trans hZcard
      _ = d * q ^ (n - 1) * q := by rw [hqn]; ring
      _ ≤ d * q ^ (n - 1) * (2 * (q - 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = (2 * d * q ^ (n - 1)) * (q - 1) := by ring
  have h6 : numPoints p F m ≤ 2 * d * q ^ (n - 1) := Nat.le_of_mul_le_mul_right h5 (by omega)
  calc (numPoints p F m : ℝ) ≤ ((2 * d * q ^ (n - 1) : ℕ) : ℝ) := by exact_mod_cast h6
    _ = 2 * d * (p : ℝ) ^ (m * (n - 1)) := by
      rw [hqdef]; push_cast; rw [pow_mul]

/-- **The hypersurface bound**: if the equation `F i` is a nonzero homogeneous polynomial of degree `D`
(as the equations of a projective variety are), then $\#V_p(\mathbb F_{p^m}) \le 2Dp^{m(n-1)}$ for $m \ge 1$ and $n \ge 1$ (Schwartz–Zippel on the affine cone
$\mathbb F_q^{n+1}$, then divide by $q - 1$). -/
theorem numPoints_le_hypersurface {n r : ℕ} (hn : 1 ≤ n) (p : ℕ) [Fact p.Prime]
    (F : Fin r → MvPolynomial (Fin (n + 1)) (ZMod p)) (i : Fin r) (hFi : F i ≠ 0) {D : ℕ}
    (hhom : (F i).IsHomogeneous D) {m : ℕ} (hm : 1 ≤ m) :
    (numPoints p F m : ℝ) ≤ 2 * D * (p : ℝ) ^ (m * (n - 1)) :=
  numPoints_le_hypersurface_of_homogeneous hn p F i hFi hhom hm

/-- **D115 with at least one equation** (Milne pdf p. 170): if $r \ge 1$ and $n \ge 1$, $\zeta(V, s)$ converges for
$\Re s > n$. For a hypersurface ($r = 1$, $\dim V = n - 1$) this is Milne's $\Re s > \dim V + 1$. (At a good prime
the reduced equations form a nonsingular complete intersection, so none of them reduces to $0$.) The equations
`F i` are assumed homogeneous (`hhom`), as the equations of a projective variety are; the bound on the
number of points uses this. -/
@[kb "milne2006ec" "Ch. IV, §10, convergence of ζ(V, s) for Re s > dim V + 1 (hypersurfaces), pdf p. 170"]
theorem varietyZeta_converges_of_pos {n r : ℕ} (hn : 1 ≤ n) (hr : 0 < r)
    (F : Fin r → MvPolynomial (Fin (n + 1)) ℚ) (hhom : ∀ i, ∃ d, (F i).IsHomogeneous d) {s : ℂ}
    (hs : (n : ℝ) < s.re) :
    Multipliable (varietyZetaFactor F s) ∧ varietyZeta F s ≠ 0 := by
  obtain ⟨d, hd⟩ := hhom ⟨0, hr⟩
  refine converges_of_bound F (n - 1) (2 * d) (by positivity) (by
    have : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      rw [Nat.cast_sub hn]; push_cast; ring
    linarith) (fun p _ h m hm => ?_)
  obtain ⟨⟨c, hc, hGc⟩, hprim⟩ := h.choose_spec.1 ⟨0, hr⟩
  set G := h.choose ⟨0, hr⟩ with hG
  have hGh : G.IsHomogeneous d := by
    intro t ht
    have h1 : (G.map (Int.castRingHom ℚ)).coeff t ≠ 0 := by
      rw [coeff_map]; simpa using ht
    rw [hGc, coeff_C_mul] at h1
    exact hd (right_ne_zero_of_mul h1)
  have hne : G.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    obtain ⟨k, hk⟩ := hprim p (Fact.out : p.Prime)
    intro h0
    apply hk
    have := congrArg (fun P : MvPolynomial (Fin (n + 1)) (ZMod p) => P.coeff k) h0
    simp only [coeff_map, MvPolynomial.coeff_zero] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  have := numPoints_le_hypersurface hn p (fun i => (h.choose i).map (Int.castRingHom (ZMod p)))
    ⟨0, hr⟩ hne (hGh.map _) hm
  simpa [mul_assoc] using this

/-- The Weierstrass polynomial $Y^2Z + a_1XYZ + a_3YZ^2 - (X^3 + a_2X^2Z + a_4XZ^2 + a_6Z^3)$ is homogeneous of
degree $3$. -/
lemma weierstrass_isHomogeneous {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.toProjective.polynomial.IsHomogeneous 3 := by
  unfold WeierstrassCurve.Projective.polynomial
  have hX : (X 0 : MvPolynomial (Fin 3) R).IsHomogeneous 1 := isHomogeneous_X R _
  have hY : (X 1 : MvPolynomial (Fin 3) R).IsHomogeneous 1 := isHomogeneous_X R _
  have hZ : (X 2 : MvPolynomial (Fin 3) R).IsHomogeneous 1 := isHomogeneous_X R _
  have t1 := (hY.pow 2).mul hZ
  have t2 := (((isHomogeneous_C_mul_X W.a₁ 0).mul hY).mul hZ)
  have t3 := ((isHomogeneous_C_mul_X W.a₃ 1).mul (hZ.pow 2))
  have t4 := hX.pow 3
  have t5 := ((isHomogeneous_C_mul_X_pow W.a₂ 0 2).mul hZ)
  have t6 := ((isHomogeneous_C_mul_X W.a₄ 0).mul (hZ.pow 2))
  have t7 : (C W.a₆ * X 2 ^ 3 : MvPolynomial (Fin 3) R).IsHomogeneous 3 :=
    isHomogeneous_C_mul_X_pow W.a₆ 2 3
  exact (((t1.add t2).add t3).sub (((t4.add t5).add t6).add t7))

lemma weierstrass_numPoints_le (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (h : HasGoodReductionAt (n := 2)
      (fun _ : Fin 1 => (W.map (Int.castRingHom ℚ)).toProjective.polynomial) p) (m : ℕ) (hm : 1 ≤ m) :
    (numPoints p (fun i => (h.choose i).map (Int.castRingHom (ZMod p))) m : ℝ) ≤
      6 * (p : ℝ) ^ (m * 1) := by
  have hQ : (W.map (Int.castRingHom ℚ)).toProjective.polynomial =
      W.toProjective.polynomial.map (Int.castRingHom ℚ) :=
    WeierstrassCurve.Projective.map_polynomial W.toProjective _
  have hsc := scaling_pm W (h.choose 0) (by simpa [hQ] using h.choose_spec.1 0)
  have hne : W.toProjective.polynomial.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    obtain ⟨k, hk⟩ := not_dvd_coeff_weierstrass W p (Fact.out : p.Prime)
    intro h0
    apply hk
    have := congrArg (fun P : MvPolynomial (Fin 3) (ZMod p) => P.coeff k) h0
    simp only [coeff_map, MvPolynomial.coeff_zero] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  have hhom : (W.toProjective.polynomial.map (Int.castRingHom (ZMod p))).IsHomogeneous 3 :=
    (weierstrass_isHomogeneous W).map _
  have key : ∀ i : Fin 1, (numPoints p (fun i => (h.choose i).map (Int.castRingHom (ZMod p))) m : ℝ) ≤
      2 * (3 : ℕ) * (p : ℝ) ^ (m * (2 - 1)) := fun i => by
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    refine numPoints_le_hypersurface_of_homogeneous (by norm_num) p _ 0 ?_ (d := 3) ?_ hm
    · rcases hsc with e | e <;> simp only [e, map_neg] <;> simpa using hne
    · rcases hsc with e | e <;> simp only [e, map_neg]
      · exact hhom
      · exact hhom.neg
  have := key 0
  norm_num at this ⊢
  exact this

/-- **D115 for an elliptic curve** (Milne pdf p. 170): for an integral Weierstrass equation, the zeta function of the
projective cubic ($\dim V = 1$) converges for $\Re s > 2 = \dim V + 1$. -/
@[kb "milne2006ec" "Ch. IV, §10, convergence of ζ(E, s) for Re s > 2, pdf p. 170"]
theorem weierstrassZeta_converges (W : WeierstrassCurve ℤ) {s : ℂ} (hs : 2 < s.re) :
    Multipliable (varietyZetaFactor (n := 2)
        (fun _ : Fin 1 => (W.map (Int.castRingHom ℚ)).toProjective.polynomial) s) ∧
      varietyZeta (n := 2) (fun _ : Fin 1 => (W.map (Int.castRingHom ℚ)).toProjective.polynomial) s ≠ 0 :=
  converges_of_bound _ 1 6 (by norm_num) (by norm_num; linarith) (fun p _ h m hm =>
    weierstrass_numPoints_le W p h m hm)

end NumberFieldKB.MilneEC.VarietyZeta
