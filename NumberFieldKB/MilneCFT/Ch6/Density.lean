import NumberFieldKB.MilneANT.Ch8Density
import NumberFieldKB.Chebotarev.PrimeDensity
import NumberFieldKB.MilneCFT.Ch6.Basic

/-!
# Milne, *Class Field Theory*, Chapter VI §§3–4: polar, Dirichlet and natural density

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

$K$ is a number field and $T$ a set of nonzero prime ideals of $\mathcal O_K$ (`HeightOneSpectrum (𝓞 K)`).

* `primeZetaProduct T s` $= \zeta_{K,T}(s) = \prod_{\mathfrak p\in T}(1 - N\mathfrak p^{-s})^{-1}$ and
  **`HasPolarDensity T δ`** (definition in prose, p. 191): some power $\zeta_{K,T}^n$ extends to a meromorphic function
  near $1$ with a pole of order $m$, and $\delta = m/n$.
* **`MilneHasDirichletDensity T δ`** (definition in prose, p. 194): $\sum_{\mathfrak p\in T}N\mathfrak p^{-s} - \delta
  \log\frac1{s-1}$ is bounded as $s\downarrow1$. Mathlib's `NumberField.Set.HasDirichletDensity` is the ratio form
  ($\sum_T/\sum_{\text{all}}\to\delta$); Milne's form implies it (`MilneHasDirichletDensity.hasDirichletDensity`).
* Natural density (definition in prose, p. 194) is `NumberFieldKB.MilneANT.HasNaturalDensity` (Milne, *ANT*, 8.30);
  it implies Dirichlet density (`natural_hasDirichletDensity`, Milne's Proposition 4.1 (b)).
* **Remark 4.2** (a): named statement `Remark4_2a` (primes with leading digit $1$); (b): `remark_4_2b` (proved).
* **Lemma 4.3** (`lemma_4_3`): $\log f(s)\sim\sum_j u_j^{-s}$ for an Euler product over reals $u_j\ge2$.
* **Proposition 4.5** (`prop_4_5`) and **Corollary 4.6** (`cor_4_6`): the primes of degree one have Dirichlet density
  $1$ and intersecting with them does not change Dirichlet densities.
-/

open Filter Topology Asymptotics IsDedekindDomain NumberField Set
open NumberFieldKB.Chebotarev

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch6

variable {K : Type} [Field K] [NumberField K]

/-! ## Polar density (p. 191) -/

/-- $\zeta_{K,T}(s) = \prod_{\mathfrak p\in T}(1 - N\mathfrak p^{-s})^{-1}$ (Milne, *CFT*, Chapter VI, p. 191), the
unconditional product `tprod` (it converges for $\mathrm{Re}\,s > 1$). -/
@[kb "milne2020cft" "Ch. VI, §3, p. 191 (the product ζ_{K,T})"]
def primeZetaProduct (T : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∏' 𝔭 : T, (1 - (Ideal.absNorm 𝔭.1.asIdeal : ℂ) ^ (-s))⁻¹

/-- **Polar density** (Milne, *CFT*, Chapter VI, p. 191, following Marcus): $T$ has polar density $\delta = m/n$ if
for some integer $n \ge 1$ the power $\zeta_{K,T}(s)^n$ extends to a meromorphic function on a neighbourhood of $1$
having a pole of order $m$ at $1$. Here: there are $g$ analytic at $1$ with $g(1)\ne0$ and an integer $m$ with
$\zeta_{K,T}(s)^n = g(s)/(s-1)^m$ for $s$ near $1$ with $\mathrm{Re}\,s > 1$ (a meromorphic germ at $1$ is exactly
$g(s)(s-1)^{-m}$ with such $g$; $m$ is an integer, a priori of either sign). -/
@[kb "milne2020cft" "Ch. VI, §3, p. 191 (polar density)"]
def HasPolarDensity (T : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  ∃ (n : ℕ) (m : ℤ), 0 < n ∧ δ = m / n ∧ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
    ∀ᶠ s in 𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ), primeZetaProduct T s ^ n = g s / (s - 1) ^ m

/-! ## Dirichlet density in Milne's form (p. 194) -/

/-- **Dirichlet density, Milne's form** (Milne, *CFT*, Chapter VI, p. 194): $T$ has Dirichlet density $\delta$ if
$\sum_{\mathfrak p\in T}N\mathfrak p^{-s} \sim \delta\log\frac1{s-1}$ as $s\downarrow1$, where $f\sim g$ means that
$f - g$ is bounded on $(1, 1+\varepsilon)$ for some $\varepsilon > 0$. The sum is Mathlib's `primeIdealZetaSum`. -/
@[kb "milne2020cft" "Ch. VI, §4, p. 194 (Dirichlet density)"]
def MilneHasDirichletDensity (T : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  (fun s : ℝ => T.primeIdealZetaSum s - δ * Real.log (1 / (s - 1))) =O[𝓝[>] 1] (fun _ => (1 : ℝ))

/-- **Milne's Dirichlet density implies Mathlib's** (ratio form): from $\sum_{\text{all}}N\mathfrak p^{-s} =
\log\frac1{s-1} + O(1)$ (`NumberFieldKB.Chebotarev.isBigO_primeIdealZetaSum_sub_log`) and
$\log\frac1{s-1}\to\infty$. (The converse fails in general: a ratio limit does not bound the difference.) -/
@[kb "milne2020cft" "Ch. VI, §4, p. 194 (Dirichlet density; comparison with Mathlib's ratio form)"]
theorem MilneHasDirichletDensity.hasDirichletDensity {T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : MilneHasDirichletDensity T δ) : T.HasDirichletDensity δ := by
  refine hasDirichletDensity_of_isBigO ?_
  have h2 := h.sub ((isBigO_primeIdealZetaSum_sub_log (F := K)).const_mul_left δ)
  refine h2.congr_left fun s => ?_
  ring

/-- **Natural density implies Dirichlet density** (Milne, *CFT*, Chapter VI, Proposition 4.1 (b); natural density as
in the definition in prose on p. 194 is `NumberFieldKB.MilneANT.HasNaturalDensity`). Proved in this library
(`NumberFieldKB.MilneANT.HasNaturalDensity.hasDirichletDensity`, by Abel summation), for Mathlib's ratio form of
Dirichlet density. -/
@[kb "milne2020cft" "Ch. VI, §4, Prop. 4.1 (b) and p. 194 (natural density)"]
theorem natural_hasDirichletDensity {T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : NumberFieldKB.MilneANT.HasNaturalDensity T δ) : T.HasDirichletDensity δ :=
  h.hasDirichletDensity

/-! ## Remark 4.2 -/

/-- The rational primes whose leading decimal digit is $1$, as primes of $\mathcal O_{\mathbb Q}$. -/
def leadingDigitOnePrimes : Set (HeightOneSpectrum (𝓞 ℚ)) :=
  {v | (Nat.digits 10 (Ideal.absNorm v.asIdeal)).getLast? = some 1}

/-- **Remark 4.2 (a)** (named statement; Milne, *CFT*, Chapter VI, p. 194, citing Serre, *A Course in Arithmetic*,
VI.4.5): the set of prime numbers whose leading decimal digit is $1$ has Dirichlet density $\log_{10}2$ but no
natural density. (A prime of $\mathcal O_{\mathbb Q}$ has norm the prime number it contains.) -/
@[kb "milne2020cft" "Ch. VI, Remark 4.2 (a)"]
structure Remark4_2a : Prop where
  dirichlet : MilneHasDirichletDensity leadingDigitOnePrimes (Real.log 2 / Real.log 10)
  not_natural : ∀ δ : ℝ, ¬ NumberFieldKB.MilneANT.HasNaturalDensity leadingDigitOnePrimes δ

/-- **Remark 4.2 (b)** (Milne, *CFT*, Chapter VI, p. 194): polar densities are rational numbers (by definition). -/
@[kb "milne2020cft" "Ch. VI, Remark 4.2 (b)"]
theorem remark_4_2b {T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} (h : HasPolarDensity T δ) :
    ∃ q : ℚ, δ = q := by
  obtain ⟨n, m, -, rfl, -⟩ := h
  exact ⟨m / n, by push_cast; ring⟩

/-! ## Lemma 4.3 -/

/-- Helper: for $u\ge2$ and $s\ge1$, $u^{-s}\le u^{-1}\le 1/2$. -/
theorem rpow_neg_le_inv_aux {u s : ℝ} (hu : 2 ≤ u) (hs : 1 ≤ s) : u ^ (-s) ≤ u⁻¹ := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- Helper: for $0\le x\le 1/2$, $x \le \log (1-x)^{-1} \le x + 2x^2$. -/
theorem log_inv_one_sub_bounds {x : ℝ} (_h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    x ≤ Real.log (1 - x)⁻¹ ∧ Real.log (1 - x)⁻¹ ≤ x + 2 * x ^ 2 := by
  have hpos : 0 < 1 - x := by linarith
  constructor
  · rw [Real.log_inv]
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  · have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    have h2 : (1 - x)⁻¹ ≤ 1 + x + 2 * x ^ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ 1 - 2 * x)]
    linarith

/-- Helper: the hypothesis of Lemma 4.3 forces $\sum_j u_j^{-s}<\infty$ for every real $s>1$ (the real point
$s$ lies in $D(1,s-1,1)$, so the real partial products converge, and they dominate $\exp\sum_{j<N}u_j^{-s}$). -/
theorem summable_rpow_of_conv (u : ℕ → ℝ) (hu : ∀ j, 2 ≤ u j)
    (hconv : ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ f : ℂ → ℂ,
      TendstoUniformlyOn (fun (N : ℕ) (s : ℂ) => ∏ j ∈ Finset.range N, (1 - (u j : ℂ) ^ (-s))⁻¹) f atTop
        (sectorD 1 δ ε)) {s : ℝ} (hs : 1 < s) : Summable fun j => u j ^ (-s) := by
  obtain ⟨f, hf⟩ := hconv (s - 1) 1 (by linarith) one_pos
  have hmem : (s : ℂ) ∈ sectorD 1 (s - 1) 1 := by
    refine ⟨by simp, ?_⟩
    have : (s : ℂ) - ((1 : ℝ) : ℂ) = ((s - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.arg_ofReal_of_nonneg (by linarith), abs_zero]
    linarith [Real.pi_gt_three]
  have ht := hf.tendsto_at hmem
  have ht2 : Filter.Tendsto (fun N => ∏ j ∈ Finset.range N, (1 - u j ^ (-s))⁻¹) atTop
      (𝓝 (f s).re) := by
    have := (Complex.continuous_re.tendsto _).comp ht
    refine this.congr (fun N => ?_)
    have e : (∏ j ∈ Finset.range N, (1 - (u j : ℂ) ^ (-(s : ℂ)))⁻¹) =
        ((∏ j ∈ Finset.range N, (1 - u j ^ (-s))⁻¹ : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.ofReal_cpow (by linarith [hu j]), Complex.ofReal_neg]
    simp only [Function.comp_apply]
    rw [e, Complex.ofReal_re]
  obtain ⟨C, hC⟩ := ht2.bddAbove_range
  have hx0 : ∀ j, 0 ≤ u j ^ (-s) := fun j => Real.rpow_nonneg (by linarith [hu j]) _
  have hxh : ∀ j, u j ^ (-s) ≤ 1 / 2 := fun j => by
    have := rpow_neg_le_inv_aux (hu j) hs.le
    have : (u j)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (hu j)
    linarith
  refine summable_of_sum_range_le (c := C) hx0 fun N => ?_
  have hPN : (∏ j ∈ Finset.range N, (1 - u j ^ (-s))⁻¹) ≤ C := hC ⟨N, rfl⟩
  have hexp : ∀ j, Real.exp (u j ^ (-s)) ≤ (1 - u j ^ (-s))⁻¹ := fun j => by
    have hp : 0 < 1 - u j ^ (-s) := by linarith [hxh j]
    have h1 := Real.add_one_le_exp (-(u j ^ (-s)))
    have h2 : Real.exp (u j ^ (-s)) * Real.exp (-(u j ^ (-s))) = 1 := by
      rw [← Real.exp_add]; simp
    rw [← one_div, le_div_iff₀ hp]
    nlinarith [Real.exp_pos (u j ^ (-s))]
  have hprod : Real.exp (∑ j ∈ Finset.range N, u j ^ (-s)) ≤ ∏ j ∈ Finset.range N, (1 - u j ^ (-s))⁻¹ := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun j _ => (Real.exp_pos _).le) fun j _ => hexp j
  have := Real.add_one_le_exp (∑ j ∈ Finset.range N, u j ^ (-s))
  have hge : (1 : ℝ) ≤ Real.exp (∑ j ∈ Finset.range N, u j ^ (-s)) := by
    rw [Real.one_le_exp_iff]; exact Finset.sum_nonneg fun j _ => hx0 j
  linarith

/-- **Lemma 4.3** (Milne, *CFT*, Chapter VI, p. 195): let $u_1, u_2,\dots$ be real numbers $\ge 2$ such that
$f(s) = \prod_j(1-u_j^{-s})^{-1}$ converges uniformly on each region $D(1,\delta,\varepsilon)$, $\delta,\varepsilon>0$.
Then $\log f(s)\sim\sum_j u_j^{-s}$ as $s\downarrow1$: the difference is bounded on $(1, 1+\varepsilon_0)$. The
uniform convergence is that of the partial products $\prod_{j<N}$; on the real half-line $s > 1$ the product and the
sum are Mathlib's `tprod` and `tsum`. -/
@[kb "milne2020cft" "Ch. VI, Lemma 4.3"]
theorem lemma_4_3 (u : ℕ → ℝ) (hu : ∀ j, 2 ≤ u j)
    (hconv : ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ f : ℂ → ℂ,
      TendstoUniformlyOn (fun (N : ℕ) (s : ℂ) => ∏ j ∈ Finset.range N, (1 - (u j : ℂ) ^ (-s))⁻¹) f atTop
        (sectorD 1 δ ε)) :
    (fun s : ℝ => Real.log (∏' j, (1 - u j ^ (-s))⁻¹) - ∑' j, u j ^ (-s)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hu0 : ∀ j, 0 < u j := fun j => by linarith [hu j]
  have hy : Summable fun j => ((u j)⁻¹) ^ 2 := by
    have h2 := summable_rpow_of_conv u hu hconv (s := 2) (by norm_num)
    refine h2.congr fun j => ?_
    rw [Real.rpow_neg (hu0 j).le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  refine IsBigO.of_bound (2 * ∑' j, ((u j)⁻¹) ^ 2) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with s hs
  rw [norm_one, mul_one, Real.norm_eq_abs]
  have hsum := summable_rpow_of_conv u hu hconv hs.1
  have hx0 : ∀ j, 0 ≤ u j ^ (-s) := fun j => Real.rpow_nonneg (hu0 j).le _
  have hxy : ∀ j, u j ^ (-s) ≤ (u j)⁻¹ := fun j => rpow_neg_le_inv_aux (hu j) hs.1.le
  have hxh : ∀ j, u j ^ (-s) ≤ 1 / 2 := fun j => by
    have : (u j)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) (hu j)
    linarith [hxy j]
  set g : ℕ → ℝ := fun j => Real.log (1 - u j ^ (-s))⁻¹ with hg
  have hb := fun j => log_inv_one_sub_bounds (hx0 j) (hxh j)
  have hg0 : ∀ j, 0 ≤ g j := fun j => (hx0 j).trans (hb j).1
  have hg2 : ∀ j, g j ≤ 2 * u j ^ (-s) := fun j => by
    have := (hb j).2
    nlinarith [hx0 j, hxh j]
  have hgs : Summable g := Summable.of_nonneg_of_le hg0 hg2 (hsum.mul_left 2)
  have hpos : ∀ j, 0 < (1 - u j ^ (-s))⁻¹ := fun j => inv_pos.mpr (by linarith [hxh j])
  have hprod : ∏' j, (1 - u j ^ (-s))⁻¹ = Real.exp (∑' j, g j) :=
    (Real.rexp_tsum_eq_tprod hpos hgs).symm
  rw [hprod, Real.log_exp, ← Summable.tsum_sub hgs hsum]
  have hd0 : ∀ j, 0 ≤ g j - u j ^ (-s) := fun j => sub_nonneg.mpr (hb j).1
  have hd2 : ∀ j, g j - u j ^ (-s) ≤ 2 * ((u j)⁻¹) ^ 2 := fun j => by
    have := (hb j).2
    have := pow_le_pow_left₀ (hx0 j) (hxy j) 2
    linarith
  rw [abs_of_nonneg (tsum_nonneg hd0)]
  calc ∑' j, (g j - u j ^ (-s)) ≤ ∑' j, 2 * ((u j)⁻¹) ^ 2 :=
        (hgs.sub hsum).tsum_le_tsum hd2 (hy.mul_left 2)
    _ = 2 * ∑' j, ((u j)⁻¹) ^ 2 := tsum_mul_left

/-! ## Proposition 4.5 and Corollary 4.6 -/

variable (K) in
/-- The primes of $K$ **of degree one** over $\mathbb Q$ (Milne, *CFT*, Chapter VI, Proposition 4.5): residue class
degree $f(\mathfrak p/p) = 1$. -/
def degreeOnePrimes : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | v.asIdeal.inertiaDeg ℤ = 1}

/-- The primes of degree one are those of prime norm (the library's `NumberFieldKB.Chebotarev.degOnePrimes`):
$N\mathfrak p = p^{f(\mathfrak p/p)}$. -/
theorem degreeOnePrimes_eq : degreeOnePrimes K = degOnePrimes K := by
  ext v
  simp only [degreeOnePrimes, degOnePrimes, mem_ofPred_eq]
  rw [QuadFormsKB.NFEuler.normP_eq_pow v]
  have hp := (QuadFormsKB.NFEuler.primeBelow v).2
  have hf : v.asIdeal.inertiaDeg ℤ ≠ 0 := by
    intro h0
    have := QuadFormsKB.NFEuler.two_le_normP v
    rw [QuadFormsKB.NFEuler.normP_eq_pow v, h0, pow_zero] at this
    omega
  constructor
  · intro h; rw [h, pow_one]; exact hp
  · intro h; exact (Nat.Prime.eq_one_of_pow h)

/-- **Proposition 4.5** (Milne, *CFT*, Chapter VI, p. 196): the set of prime ideals of $K$ of degree one over
$\mathbb Q$ has Dirichlet density $1$ (Milne's form, hence also Mathlib's). -/
@[kb "milne2020cft" "Ch. VI, Prop. 4.5"]
theorem prop_4_5 : MilneHasDirichletDensity (degreeOnePrimes K) 1 := by
  rw [degreeOnePrimes_eq]
  have h1 := (isBigO_primeIdealZetaSum_diff_degOnePrimes (F := K) (Set.univ)).neg_left
  have h2 := (isBigO_primeIdealZetaSum_sub_log (F := K))
  refine (h1.add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s hs
  have h := primeIdealZetaSum_union (S := degOnePrimes K) (T := Set.univ \ degOnePrimes K)
    disjoint_sdiff_self_right hs
  rw [union_sdiff_cancel (subset_univ _)] at h
  simp only [one_mul]
  rw [h]
  ring

/-- **Corollary 4.6** (Milne, *CFT*, Chapter VI, p. 196): for every set $S$ of primes of $K$ having a Dirichlet
density, $\delta(T\cap S) = \delta(S)$, $T$ the primes of degree one. -/
@[kb "milne2020cft" "Ch. VI, Cor. 4.6"]
theorem cor_4_6 {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} (hS : MilneHasDirichletDensity S δ) :
    MilneHasDirichletDensity (degreeOnePrimes K ∩ S) δ := by
  rw [degreeOnePrimes_eq]
  have h1 := (isBigO_primeIdealZetaSum_diff_degOnePrimes (F := K) S).neg_left
  refine (hS.add h1).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s hs
  have h := primeIdealZetaSum_union (S := degOnePrimes K ∩ S) (T := S \ degOnePrimes K)
    (by rw [inter_comm]; exact disjoint_sdiff_inter.symm) hs
  rw [inter_comm, inter_union_sdiff] at h
  rw [inter_comm, h]
  ring

/-- **Corollary 4.6, Mathlib's form of Dirichlet density** (proved in this library as
`NumberFieldKB.Chebotarev.hasDirichletDensity_inter_degOnePrimes_iff`). -/
@[kb "milne2020cft" "Ch. VI, Cor. 4.6 (ratio form of Dirichlet density)"]
theorem cor_4_6_ratio {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} (hS : S.HasDirichletDensity δ) :
    (degreeOnePrimes K ∩ S).HasDirichletDensity δ := by
  rw [degreeOnePrimes_eq, inter_comm]
  exact hasDirichletDensity_inter_degOnePrimes_iff.mpr hS

end NumberFieldKB.MilneCFT.Ch6
