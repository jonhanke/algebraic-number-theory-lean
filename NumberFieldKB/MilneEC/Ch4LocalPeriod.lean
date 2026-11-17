import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.NumberTheory.Padics.RingHoms
import QuadFormsKB.Analysis.LocalFourier
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import QuadFormsKB.Citation
import NumberFieldKB.TauCetiPort.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Discriminant
import NumberFieldKB.FormalConjectures.EllipticCurve

/-!
# Milne, *Elliptic Curves*, Remark IV.10.6 (a), (c): the local measure $\int_{E(\mathbb Q_p)}|\omega|$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Remark 10.6, pdf p. 173:
for a minimal equation of $E$ over $\mathbb Q_p$ with invariant differential
$\omega = dx/(2y + a_1x + a_3)$,
$$\int_{E(\mathbb Q_p)} |\omega|_p = c_p\,\frac{N_p}{p}, \qquad N_p = \#\tilde E_{ns}(\mathbb F_p),$$
and $N_p/p = L_p(E, 1)^{-1}$, so that $L_p(E, 1)\int_{E(\mathbb Q_p)}|\omega|_p = c_p$.

## The measure
On the open subset of $E(\mathbb Q_p)$ where $\psi = 2y + a_1x + a_3 \neq 0$ the coordinate $x$ is a local analytic
coordinate, and there $|\omega|_p = |dx|_p / |\psi|_p$ (Weil's measure attached to a gauge form). On the curve
$\psi^2 = \Psi_2^2(x) = 4x^3 + b_2x^2 + 2b_4x + b_6$ (Mathlib's `WeierstrassCurve.Ψ₂Sq`), so over a given $x$ there
are two points when $\Psi_2^2(x)$ is a nonzero square in $\mathbb Q_p$, with $|\psi|_p = |\Psi_2^2(x)|_p^{1/2}$, and
none when it is not a square. The remaining points (those with $\psi = 0$, at most three, and the point at
infinity) form a null set. Hence
$$\int_{E(\mathbb Q_p)}|\omega|_p = \int_{\mathbb Q_p} \frac{2\cdot\mathbf 1[\Psi_2^2(x) \in \mathbb Q_p^{\times2}]}
{|\Psi_2^2(x)|_p^{1/2}}\,dx,$$
`omegaVolume`, with $dx$ the Haar measure of QuadFormsKB, `QuadFormsKB.Analysis.haarP`, normalized by
$\operatorname{vol}(\mathbb Z_p) = 1$ (the self-dual measure of Tate's thesis, the one used by QuadFormsKB's local
densities and Tamagawa measures). This is the $p$-adic counterpart of Formal Conjectures' `realPeriod`
($2\int_{\mathbb R} dx/\sqrt{\Psi_2^2(x)}$, vendored in `NumberFieldKB.FormalConjectures.EllipticCurve`), with the
same convention for the factor $2$. The integral is a Lebesgue integral in $[0, \infty]$, so a divergent integral
cannot silently read as $0$.

## Proved (good reduction, $p$ odd)
* `lintegral_sqrtDensity_outside`: the points with $|x|_p > 1$ (the kernel of reduction $E^1(\mathbb Q_p)$) have
  measure $1/p$.
* `lintegral_sqrtDensity_ball`: the residue disc $x_0 + p\mathbb Z_p$ has measure $\#\{v : v^2 = \bar F(\bar x_0)\}/p$
  when $F(x_0)$ is a unit or $x_0$ is a simple root modulo $p$.
* `lintegral_sqrtDensity`: summing, $\int = (1 + \sum_{\bar x}\#\{v : v^2 = \bar F(\bar x)\})/p$.
* `card_point_eq_of_isElliptic`: $N_p = 1 + \sum_{\bar x}\#\{v : v^2 = \bar\Psi_2^2(\bar x)\}$ ($p$ odd).
* `remark_10_6_a_good`: **Remark 10.6 (a)** at good reduction, $p$ odd: $\int_{E(\mathbb Q_p)}|\omega| = N_p/p$
  ($c_p = 1$ there: `Tamagawa.tamagawaNumber_eq_one_of_hasGoodReduction`, used in `remark_10_6_a_good_cp`).
* `remark_10_6_c_good`: **Remark 10.6 (c)** at good reduction, $p$ odd: $\int_{E(\mathbb Q_p)}|\omega| =
  L_p(E, p^{-1})$-polynomial value, i.e. $L_p(E, 1)^{-1}$, with Mathlib's `WeierstrassCurve.localPolynomial`.

## Stated
* `Remark10_6`: (a) and (c) for every minimal model, every reduction type and every $p$. It is derived in
  Ch4LocalPeriodRemark.lean (`remark10_6_of`) from Milne's translation step `ZeroComponentIndex` and two statements
  at $p = 2$; there also (a) with the factor $c_p$ at good reduction and (c) from (a) at every odd prime; the measure
  of $E_0(\mathbb Q_p)$ at every reduction type, $p$ odd, is Ch4LocalPeriodBad.lean's `omegaVolume_zeroComponent`.
-/

open MeasureTheory QuadFormsKB.Analysis Polynomial
open scoped ENNReal

namespace NumberFieldKB.MilneEC.LocalPeriod

variable {p : ℕ} [hp : Fact p.Prime]

open scoped Classical in
/-- The density $2\cdot\mathbf 1[F(x) \in \mathbb Q_p^{\times 2}]\,|F(x)|_p^{-1/2}$ on the $x$-line, in
$[0, \infty]$: the number of square roots $\psi$ of $F(x)$ in $\mathbb Q_p$ divided by $|\psi|_p$. -/
noncomputable def sqrtDensity (F : ℚ_[p][X]) (x : ℚ_[p]) : ℝ≥0∞ :=
  if IsSquare (F.eval x) ∧ F.eval x ≠ 0 then 2 / ENNReal.ofReal √‖F.eval x‖ else 0

/-- The density of $|\omega|_p$ pushed to the $x$-line: `sqrtDensity` of $\Psi_2^2 = 4x^3 + b_2x^2 + 2b_4x + b_6$. -/
noncomputable def omegaDensity (W : WeierstrassCurve ℚ_[p]) (x : ℚ_[p]) : ℝ≥0∞ :=
  sqrtDensity W.Ψ₂Sq x

/-- **The local measure** $\int_{E(\mathbb Q_p)}|\omega|_p$ of the Weierstrass equation `W`, $\omega = dx/(2y + a_1x +
a_3)$: $\int_{\mathbb Q_p} 2\cdot\mathbf 1[\Psi_2^2(x) \in \mathbb Q_p^{\times 2}]\,|\Psi_2^2(x)|_p^{-1/2}\,dx$, with
$\operatorname{vol}(\mathbb Z_p) = 1$ (see the module docstring). -/
@[kb "milne2006ec" "Ch. IV, Remark 10.6 (a), the measure of E(Q_p) for |ω|, pdf p. 173"]
noncomputable def omegaVolume (W : WeierstrassCurve ℚ_[p]) : ℝ≥0∞ :=
  ∫⁻ x, omegaDensity W x ∂haarP p

/-! ## Helper lemmas -/

lemma norm_lt_one_iff_toZMod (x : ℤ_[p]) : ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

lemma isUnit_iff_toZMod_ne (x : ℤ_[p]) : IsUnit x ↔ PadicInt.toZMod x ≠ 0 := by
  rw [← not_iff_not, PadicInt.not_isUnit_iff, not_not, norm_lt_one_iff_toZMod]

lemma norm_two_eq_one (hp2 : p ≠ 2) : ‖(2 : ℤ_[p])‖ = 1 := by
  have := (PadicInt.norm_natCast_eq_one_iff (p := p) (n := 2)).mpr (by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp h).symm)
  simpa using this

lemma isSquare_of_norm_sub_one_lt (hp2 : p ≠ 2) {w : ℚ_[p]} (hw : ‖w - 1‖ < 1) : IsSquare w := by
  have h1 : ‖w‖ = 1 := by
    have h2 : ‖(1 : ℚ_[p]) + (w - 1)‖ = max ‖(1 : ℚ_[p])‖ ‖w - 1‖ :=
      Padic.add_eq_max_of_ne (by rw [norm_one]; exact hw.ne')
    rw [add_sub_cancel, norm_one] at h2
    rw [h2]; exact (max_eq_left hw.le)
  set W : ℤ_[p] := ⟨w, h1.le⟩ with hW
  have hnorm : ‖(X ^ 2 - C W : ℤ_[p][X]).aeval (1 : ℤ_[p])‖ <
      ‖(X ^ 2 - C W : ℤ_[p][X]).derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    have e1 : (X ^ 2 - C W : ℤ_[p][X]).aeval (1 : ℤ_[p]) = 1 - W := by simp
    have e2 : (X ^ 2 - C W : ℤ_[p][X]).derivative.aeval (1 : ℤ_[p]) = 2 := by
      simp [one_add_one_eq_two]
    rw [e1, e2, norm_two_eq_one hp2]
    simp only [one_pow]
    rw [PadicInt.norm_def]
    push_cast
    rw [norm_sub_rev]; exact hw
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  have hz' : z ^ 2 = W := by
    have : z ^ 2 - W = 0 := by simpa using hz
    exact sub_eq_zero.mp this
  refine ⟨(z : ℚ_[p]), ?_⟩
  have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hz'
  simp only [PadicInt.coe_pow, hW] at this
  rw [← this]; ring


lemma isSquare_coe_iff (hp2 : p ≠ 2) {w : ℤ_[p]} (hw : IsUnit w) :
    IsSquare (w : ℚ_[p]) ↔ IsSquare (PadicInt.toZMod w) := by
  constructor
  · rintro ⟨y, hy⟩
    have hy1 : ‖y‖ = 1 := by
      have h : ‖(w : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp hw
      rw [hy, norm_mul] at h
      nlinarith [norm_nonneg y]
    let Y : ℤ_[p] := ⟨y, hy1.le⟩
    have hY : w = Y * Y := Subtype.ext hy
    exact ⟨PadicInt.toZMod Y, by rw [hY, map_mul]⟩
  · rintro ⟨s, hs⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact (isUnit_iff_toZMod_ne w).mp hw (by rw [hs]; simp)
    set S : ℤ_[p] := (s.val : ℤ_[p]) with hSdef
    have hS : PadicInt.toZMod S = s := by simp [S]
    have hSu : IsUnit S := (isUnit_iff_toZMod_ne S).mpr (by rw [hS]; exact hs0)
    have hS1 : ‖(S : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp hSu
    have hS0 : (S : ℚ_[p]) ≠ 0 := by intro h; rw [h] at hS1; simp at hS1
    have hlt : ‖(w : ℚ_[p]) / (S : ℚ_[p]) ^ 2 - 1‖ < 1 := by
      have : (w : ℚ_[p]) / (S : ℚ_[p]) ^ 2 - 1 = ((w - S ^ 2 : ℤ_[p]) : ℚ_[p]) / (S : ℚ_[p]) ^ 2 := by
        push_cast; field_simp
      rw [this, norm_div, norm_pow, hS1, one_pow, div_one, ← PadicInt.norm_def,
        norm_lt_one_iff_toZMod]
      simp [hS, hs]; ring
    obtain ⟨t, ht⟩ := isSquare_of_norm_sub_one_lt hp2 hlt
    refine ⟨(S : ℚ_[p]) * t, ?_⟩
    have : (w : ℚ_[p]) = (S : ℚ_[p]) ^ 2 * (t * t) := by
      rw [← ht]; field_simp
    rw [this]; ring

lemma isSquare_mul_iff_of_one_add (hp2 : p ≠ 2) {c w : ℚ_[p]} (hw : ‖w - 1‖ < 1) :
    IsSquare (c * w) ↔ IsSquare c := by
  obtain ⟨u, hu⟩ := isSquare_of_norm_sub_one_lt hp2 hw
  have hu0 : u ≠ 0 := by
    rintro rfl
    have : w = 0 := by simpa using hu
    rw [this] at hw; simp at hw
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a / u, ?_⟩
    have : c = c * w / w := by
      have : w ≠ 0 := by rw [hu]; exact mul_ne_zero hu0 hu0
      field_simp
    rw [this, ha, hu]; field_simp
  · rintro ⟨a, ha⟩
    exact ⟨a * u, by rw [ha, hu]; ring⟩

lemma isSquare_mul_zpow_iff {a : ℚ_[p]} (ha : ‖a‖ = 1) (m : ℤ) :
    IsSquare (a * (p : ℚ_[p]) ^ m) ↔ Even m ∧ IsSquare a := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  constructor
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz
      rcases hz with h | h
      · exact ha0 h
      · exact zpow_ne_zero m hp0 h
    have hn : ‖z‖ = (p : ℝ) ^ (-z.valuation) := Padic.norm_eq_zpow_neg_valuation hz0
    have h1 : ‖a * (p : ℚ_[p]) ^ m‖ = (p : ℝ) ^ (-m) := by
      rw [norm_mul, ha, one_mul, Padic.norm_p_zpow]
    rw [hz, norm_mul, hn, ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)] at h1
    have h2 : -z.valuation + -z.valuation = -m :=
      zpow_right_injective₀ (by exact_mod_cast hp.out.pos) (by exact_mod_cast hp.out.one_lt.ne') h1
    have hm : Even m := ⟨z.valuation, by omega⟩
    refine ⟨hm, ⟨z / (p : ℚ_[p]) ^ z.valuation, ?_⟩⟩
    have hm' : m = z.valuation + z.valuation := by omega
    rw [hm'] at hz
    have : a = z * z / (p : ℚ_[p]) ^ (z.valuation + z.valuation) := by
      rw [← hz]; field_simp
    rw [this, zpow_add₀ hp0]; field_simp
  · rintro ⟨⟨k, hk⟩, y, hy⟩
    refine ⟨y * (p : ℚ_[p]) ^ k, ?_⟩
    rw [hy, hk, zpow_add₀ hp0]; ring


lemma norm_sub_nat_le_iff (U : ℤ_[p]) (n : ℕ) :
    ‖(U : ℚ_[p]) - (n : ℚ_[p])‖ ≤ (p : ℝ) ^ (-1 : ℤ) ↔ PadicInt.toZMod U = (n : ZMod p) := by
  rw [norm_le_zpow_iff_lt]
  have : ‖(U : ℚ_[p]) - (n : ℚ_[p])‖ = ‖U - (n : ℤ_[p])‖ := by
    rw [PadicInt.norm_def]; push_cast; rfl
  rw [this, show (-1 : ℤ) + 1 = 0 by norm_num, zpow_zero, norm_lt_one_iff_toZMod, map_sub,
    map_natCast, sub_eq_zero]

lemma exists_fin_close (U : ℤ_[p]) :
    ∃ j : Fin p, PadicInt.toZMod U = ((j : ℕ) : ZMod p) := by
  obtain ⟨n, hnp, hn⟩ := PadicInt.exists_mem_range (x := U)
  refine ⟨⟨n, hnp⟩, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hn
  have := (norm_lt_one_iff_toZMod (U - (n : ℤ_[p]))).mp hn
  simpa [sub_eq_zero] using this

lemma card_square_class (hp2 : p ≠ 2) {c : ZMod p} (hc : c ≠ 0) :
    2 * (Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ IsSquare (c * a))).card = p - 1 := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  set χ := quadraticChar (ZMod p)
  have hsum : ∑ a : ZMod p, χ (c * a) = 0 := by
    rw [Fintype.sum_equiv (Equiv.mulLeft₀ c hc) (fun a => χ (c * a)) χ (fun a => rfl)]
    exact quadraticChar_sum_zero hchar
  have hsum2 : ∑ a ∈ Finset.univ.filter (fun a : ZMod p => a ≠ 0), χ (c * a) = 0 := by
    rw [← hsum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a = 0 <;> simp [ha, MulChar.map_zero]
  have hval : ∀ a ∈ Finset.univ.filter (fun a : ZMod p => a ≠ 0),
      χ (c * a) = if IsSquare (c * a) then 1 else -1 := by
    intro a ha
    have ha0 : a ≠ 0 := by simpa using ha
    have hca : c * a ≠ 0 := mul_ne_zero hc ha0
    split_ifs with h
    · exact (quadraticChar_one_iff_isSquare hca).mpr h
    · exact quadraticChar_neg_one_iff_not_isSquare.mpr h
  rw [Finset.sum_congr rfl hval, Finset.sum_ite] at hsum2
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg] at hsum2
  have hA : (Finset.univ.filter (fun a : ZMod p => a ≠ 0)).filter (fun a => IsSquare (c * a)) =
      Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ IsSquare (c * a)) := by
    ext a; simp
  have htot := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun a : ZMod p => a ≠ 0))
    (fun a => IsSquare (c * a))
  have hcard : (Finset.univ.filter (fun a : ZMod p => a ≠ 0)).card = p - 1 := by
    rw [Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card]
  rw [hA, hcard] at htot
  rw [hA] at hsum2
  have h1 : ((Finset.univ.filter (fun a : ZMod p => a ≠ 0 ∧ IsSquare (c * a))).card : ℤ) =
      (((Finset.univ.filter (fun a : ZMod p => a ≠ 0)).filter (fun a => ¬ IsSquare (c * a))).card : ℤ) := by
    linarith
  omega


/-- The shell `{y : ‖y‖ = p^(-m), c * y a square}`. -/
def shell (c : ℤ_[p]) (m : ℤ) : Set ℚ_[p] :=
  {y | ‖y‖ = (p : ℝ) ^ (-m) ∧ IsSquare ((c : ℚ_[p]) * y)}

lemma norm_coe_unit {c : ℤ_[p]} (hc : IsUnit c) : ‖(c : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp hc

lemma mem_shell_iff (hp2 : p ≠ 2) {c : ℤ_[p]} (hc : IsUnit c) (m : ℤ) (y : ℚ_[p]) :
    y ∈ shell c m ↔ Even m ∧ ∃ U : ℤ_[p], (U : ℚ_[p]) = y / (p : ℚ_[p]) ^ m ∧ IsUnit U ∧
      IsSquare (PadicInt.toZMod c * PadicInt.toZMod U) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpm : (p : ℚ_[p]) ^ m ≠ 0 := zpow_ne_zero m hp0
  have hnp : ‖(p : ℚ_[p]) ^ m‖ = (p : ℝ) ^ (-m) := Padic.norm_p_zpow m
  have hnp0 : (p : ℝ) ^ (-m) ≠ 0 := (zpow_p_pos _).ne'
  constructor
  · rintro ⟨hn, hsq⟩
    have hu : ‖y / (p : ℚ_[p]) ^ m‖ = 1 := by rw [norm_div, hnp, hn, div_self hnp0]
    set U : ℤ_[p] := ⟨y / (p : ℚ_[p]) ^ m, hu.le⟩ with hU
    have hUu : IsUnit U := PadicInt.isUnit_iff.mpr hu
    have hca : ‖(c : ℚ_[p]) * (U : ℚ_[p])‖ = 1 := by
      rw [norm_mul, norm_coe_unit hc, norm_coe_unit hUu, one_mul]
    have e : (c : ℚ_[p]) * y = ((c : ℚ_[p]) * (U : ℚ_[p])) * (p : ℚ_[p]) ^ m := by
      simp only [hU]; field_simp
    rw [e] at hsq
    obtain ⟨hm, hsq'⟩ := (isSquare_mul_zpow_iff hca m).mp hsq
    refine ⟨hm, U, rfl, hUu, ?_⟩
    rw [← map_mul]
    exact (isSquare_coe_iff hp2 (hc.mul hUu)).mp (by simpa using hsq')
  · rintro ⟨hm, U, hU, hUu, hsq⟩
    have hy : y = (U : ℚ_[p]) * (p : ℚ_[p]) ^ m := by rw [hU]; field_simp
    have hca : ‖(c : ℚ_[p]) * (U : ℚ_[p])‖ = 1 := by
      rw [norm_mul, norm_coe_unit hc, norm_coe_unit hUu, one_mul]
    refine ⟨?_, ?_⟩
    · rw [hy, norm_mul, norm_coe_unit hUu, one_mul, hnp]
    · have e : (c : ℚ_[p]) * y = ((c : ℚ_[p]) * (U : ℚ_[p])) * (p : ℚ_[p]) ^ m := by rw [hy]; ring
      rw [e]
      refine (isSquare_mul_zpow_iff hca m).mpr ⟨hm, ?_⟩
      rw [← map_mul] at hsq
      have := (isSquare_coe_iff hp2 (hc.mul hUu)).mpr hsq
      simpa using this

lemma shell_eq_odd (hp2 : p ≠ 2) {c : ℤ_[p]} (hc : IsUnit c) {m : ℤ} (hm : ¬ Even m) :
    shell c m = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_shell_iff hp2 hc]
  exact fun h => hm h.1

lemma shell_eq_even (hp2 : p ≠ 2) {c : ℤ_[p]} (hc : IsUnit c) {m : ℤ} (hm : Even m) :
    shell c m = ⋃ j ∈ Finset.univ.filter (fun j : Fin p => ((j : ℕ) : ZMod p) ≠ 0 ∧
        IsSquare (PadicInt.toZMod c * ((j : ℕ) : ZMod p))),
      Metric.closedBall ((j : ℚ_[p]) * (p : ℚ_[p]) ^ m) ((p : ℝ) ^ (-(m + 1))) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpm : (p : ℚ_[p]) ^ m ≠ 0 := zpow_ne_zero m hp0
  have hnp : ‖(p : ℚ_[p]) ^ m‖ = (p : ℝ) ^ (-m) := Padic.norm_p_zpow m
  have hnp0 : (0 : ℝ) < (p : ℝ) ^ (-m) := zpow_p_pos _
  have hnorm : ∀ (y : ℚ_[p]) (j : Fin p),
      ‖y - (j : ℚ_[p]) * (p : ℚ_[p]) ^ m‖ ≤ (p : ℝ) ^ (-(m + 1)) ↔
      ‖y / (p : ℚ_[p]) ^ m - (j : ℚ_[p])‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
    intro y j
    have e : y - (j : ℚ_[p]) * (p : ℚ_[p]) ^ m = (y / (p : ℚ_[p]) ^ m - (j : ℚ_[p])) * (p : ℚ_[p]) ^ m := by
      field_simp
    have e2 : (p : ℝ) ^ (-(m + 1)) = (p : ℝ) ^ (-1 : ℤ) * (p : ℝ) ^ (-m) := by
      rw [← zpow_add₀ p_pos.ne']; ring_nf
    rw [e, norm_mul, hnp, e2]
    exact mul_le_mul_iff_of_pos_right hnp0
  ext y
  simp only [Set.mem_iUnion, Metric.mem_closedBall, dist_eq_norm, Finset.mem_filter,
    Finset.mem_univ, true_and, exists_prop]
  rw [mem_shell_iff hp2 hc]
  constructor
  · rintro ⟨-, U, hU, hUu, hsq⟩
    obtain ⟨j, hj⟩ := exists_fin_close U
    refine ⟨j, ⟨?_, ?_⟩, ?_⟩
    · rw [← hj]; exact (isUnit_iff_toZMod_ne U).mp hUu
    · rw [← hj]; exact hsq
    · rw [hnorm y j, ← hU]; exact (norm_sub_nat_le_iff U j).mpr hj
  · rintro ⟨j, ⟨hj0, hjsq⟩, hn⟩
    rw [hnorm y j] at hn
    have hj1 : ‖((j : ℕ) : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one ((j : ℕ) : ℤ)
    have hu1 : ‖y / (p : ℚ_[p]) ^ m‖ ≤ 1 := by
      have : y / (p : ℚ_[p]) ^ m = (y / (p : ℚ_[p]) ^ m - (j : ℚ_[p])) + (j : ℚ_[p]) := by ring
      rw [this]
      refine (Padic.nonarchimedean _ _).trans (max_le ?_ hj1)
      exact hn.trans (zpow_le_one_of_nonpos₀ one_lt_p.le (by norm_num))
    set U : ℤ_[p] := ⟨_, hu1⟩ with hUdef
    have hUj : PadicInt.toZMod U = ((j : ℕ) : ZMod p) := (norm_sub_nat_le_iff U j).mp hn
    refine ⟨hm, U, rfl, ?_, ?_⟩
    · exact (isUnit_iff_toZMod_ne U).mpr (by rw [hUj]; exact hj0)
    · rw [hUj]; exact hjsq


lemma haarP_closedBall_any (a : ℚ_[p]) (k : ℤ) :
    haarP p (Metric.closedBall a ((p : ℝ) ^ (-k))) = ENNReal.ofReal ((p : ℝ) ^ (-k)) := by
  rw [Measure.addHaar_closedBall_center, haarP_closedBall]

lemma card_fin_filter (P : ZMod p → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun j : Fin p => P ((j : ℕ) : ZMod p))).card =
      (Finset.univ.filter P).card := by
  refine Finset.card_bij (fun j _ => ((j : ℕ) : ZMod p)) ?_ ?_ ?_
  · intro j hj; simpa using hj
  · intro i _ j _ h
    have := (ZMod.natCast_eq_natCast_iff' i j p).mp h
    rw [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at this
    exact Fin.ext this
  · intro a ha
    exact ⟨⟨a.val, ZMod.val_lt a⟩, by simpa using ha, by simp⟩

lemma haarP_shell_even (hp2 : p ≠ 2) {c : ℤ_[p]} (hc : IsUnit c) {m : ℤ} (hm : Even m) :
    haarP p (shell c m) = ENNReal.ofReal (((p : ℝ) - 1) / 2 * (p : ℝ) ^ (-(m + 1))) := by
  classical
  rw [shell_eq_even hp2 hc hm, measure_biUnion_finset]
  · simp only [haarP_closedBall_any (p := p) _ (m + 1)]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc0 : PadicInt.toZMod c ≠ 0 := (isUnit_iff_toZMod_ne c).mp hc
    have h2 := card_square_class hp2 hc0
    have h1 := card_fin_filter (p := p) (fun a : ZMod p => a ≠ 0 ∧ IsSquare (PadicInt.toZMod c * a))
    have hcard : (Finset.univ.filter (fun j : Fin p => ((j : ℕ) : ZMod p) ≠ 0 ∧
        IsSquare (PadicInt.toZMod c * ((j : ℕ) : ZMod p)))).card * 2 = p - 1 := by
      rw [h1]; omega
    have hr : ((Finset.univ.filter (fun j : Fin p => ((j : ℕ) : ZMod p) ≠ 0 ∧
        IsSquare (PadicInt.toZMod c * ((j : ℕ) : ZMod p)))).card : ℝ) = ((p : ℝ) - 1) / 2 := by
      have : (((Finset.univ.filter (fun j : Fin p => ((j : ℕ) : ZMod p) ≠ 0 ∧
        IsSquare (PadicInt.toZMod c * ((j : ℕ) : ZMod p)))).card * 2 : ℕ) : ℝ) = ((p - 1 : ℕ) : ℝ) := by
        rw [hcard]
      rw [Nat.cast_sub hp.out.one_le] at this
      push_cast at this
      linarith
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hr]
  · intro i _ j _ hij
    exact closedBall_disjoint m hij
  · intro j _
    exact Metric.isClosed_closedBall.measurableSet

lemma haarP_shell_odd (hp2 : p ≠ 2) {c : ℤ_[p]} (hc : IsUnit c) {m : ℤ} (hm : ¬ Even m) :
    haarP p (shell c m) = 0 := by
  rw [shell_eq_odd hp2 hc hm]; simp


lemma measurableSet_shell (hp2 : p ≠ 2) {c : ℤ_[p]} (hc : IsUnit c) (m : ℤ) :
    MeasurableSet (shell c m) := by
  by_cases hm : Even m
  · rw [shell_eq_even hp2 hc hm]
    exact Finset.measurableSet_biUnion _ (fun j _ => Metric.isClosed_closedBall.measurableSet)
  · rw [shell_eq_odd hp2 hc hm]; exact MeasurableSet.empty

lemma haarP_cshell (a : ℚ_[p]) (S : Set ℚ_[p]) : haarP p {x | x - a ∈ S} = haarP p S := by
  have : {x : ℚ_[p] | x - a ∈ S} = (fun h => -a + h) ⁻¹' S := by
    ext x; simp [sub_eq_neg_add]
  rw [this, measure_preimage_add]

open scoped Classical in
lemma setLIntegral_cshell (hp2 : p ≠ 2) {c : ℤ_[p]} (hc : IsUnit c) (a : ℚ_[p]) (m : ℤ)
    (f : ℚ_[p] → ℝ≥0∞) (d : ℝ≥0∞)
    (hf : ∀ x, ‖x - a‖ = (p : ℝ) ^ (-m) → f x = if IsSquare ((c : ℚ_[p]) * (x - a)) then d else 0) :
    ∫⁻ x in {x : ℚ_[p] | ‖x - a‖ = (p : ℝ) ^ (-m)}, f x ∂haarP p = d * haarP p (shell c m) := by
  have hA : MeasurableSet {x : ℚ_[p] | ‖x - a‖ = (p : ℝ) ^ (-m)} :=
    (measurableSet_singleton _).preimage
      ((continuous_norm.comp (continuous_sub_right a)).measurable)
  have hS : MeasurableSet {x : ℚ_[p] | x - a ∈ shell c m} :=
    (measurableSet_shell hp2 hc m).preimage (continuous_sub_right a).measurable
  rw [setLIntegral_congr_fun hA (g := {x : ℚ_[p] | x - a ∈ shell c m}.indicator (fun _ => d)) ?_]
  · rw [setLIntegral_eq_of_support_subset, lintegral_indicator_const hS, haarP_cshell, mul_comm]
    intro x hx
    have : x ∈ {x : ℚ_[p] | x - a ∈ shell c m} := Set.support_indicator_subset hx
    exact this.1
  · intro x hx
    rw [hf x hx, Set.indicator_apply]
    simp only [Set.mem_setOf_eq, shell]
    exact if_congr ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩ rfl rfl

lemma tsum_shell_series (g : ℕ → ℝ≥0∞) (h0 : ∀ k, g (2 * k) = 0)
    (h1 : ∀ k, g (2 * k + 1) = ENNReal.ofReal (((p : ℝ) - 1) / (p : ℝ) ^ (k + 2))) :
    ∑' n, g n = 1 / (p : ℝ≥0∞) := by
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
  simp only [h0, h1, tsum_zero, zero_add]
  have hp1 : (1 : ℝ) < p := one_lt_p
  have hp0 : (0 : ℝ) < p := p_pos
  have hsum : HasSum (fun k : ℕ => ((p : ℝ) - 1) / (p : ℝ) ^ (k + 2)) (1 / (p : ℝ)) := by
    have hg := (hasSum_geometric_of_lt_one (r := 1 / (p : ℝ)) (by positivity)
      (by rw [div_lt_one hp0]; exact hp1)).mul_left (((p : ℝ) - 1) / (p : ℝ) ^ 2)
    convert hg using 1
    · ext k; simp only [pow_add, one_div, inv_pow]; field_simp
    · have : (1 - 1 / (p : ℝ)) = ((p : ℝ) - 1) / p := by field_simp
      rw [this]; field_simp
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by
      have : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
      positivity) hsum.summable, hsum.tsum_eq,
    ENNReal.ofReal_div_of_pos hp0]
  simp


lemma norm_eq_one_of_sub_one_lt {w : ℚ_[p]} (hw : ‖w - 1‖ < 1) : ‖w‖ = 1 := by
  have h2 : ‖(1 : ℚ_[p]) + (w - 1)‖ = max ‖(1 : ℚ_[p])‖ ‖w - 1‖ :=
    Padic.add_eq_max_of_ne (by rw [norm_one]; exact hw.ne')
  rw [add_sub_cancel, norm_one] at h2
  rw [h2]; exact (max_eq_left hw.le)

lemma isSquare_mul_sq_iff {a b : ℚ_[p]} (hb : b ≠ 0) : IsSquare (a * b ^ 2) ↔ IsSquare a := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z / b, by field_simp; linear_combination hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z * b, by rw [hz]; ring⟩

lemma eval_cubic (F : ℤ_[p][X]) (hdeg : F.natDegree = 3) (x : ℚ_[p]) :
    (F.map (algebraMap ℤ_[p] ℚ_[p])).eval x =
      (F.coeff 3 : ℚ_[p]) * x ^ 3 + (F.coeff 2 : ℚ_[p]) * x ^ 2 + (F.coeff 1 : ℚ_[p]) * x +
        (F.coeff 0 : ℚ_[p]) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range, hdeg]
  simp [Finset.sum_range_succ]
  ring

open scoped Classical in
lemma sqrtDensity_outside (hp2 : p ≠ 2) (F : ℤ_[p][X]) (hdeg : F.natDegree = 3)
    (hlead : IsUnit F.leadingCoeff) (x : ℚ_[p]) (hx : 1 < ‖x‖) :
    sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x =
      if IsSquare ((F.coeff 3 : ℚ_[p]) * x) then 2 / ENNReal.ofReal √(‖x‖ ^ 3) else 0 := by
  have hc3 : IsUnit (F.coeff 3) := by
    have : F.leadingCoeff = F.coeff 3 := by rw [Polynomial.leadingCoeff, hdeg]
    rwa [this] at hlead
  have ha3 : ‖(F.coeff 3 : ℚ_[p])‖ = 1 := norm_coe_unit hc3
  have hx0 : x ≠ 0 := by rintro rfl; rw [norm_zero] at hx; linarith
  have hxpos : 0 < ‖x‖ := by linarith
  have hai : ∀ i, ‖(F.coeff i : ℚ_[p])‖ ≤ 1 := fun i => (F.coeff i).2
  set tail : ℚ_[p] := (F.coeff 2 : ℚ_[p]) * x ^ 2 + (F.coeff 1 : ℚ_[p]) * x + (F.coeff 0 : ℚ_[p])
    with htail
  have hP : (F.map (algebraMap ℤ_[p] ℚ_[p])).eval x = (F.coeff 3 : ℚ_[p]) * x ^ 3 + tail := by
    rw [eval_cubic F hdeg x, htail]; ring
  have htl : ‖tail‖ < ‖x‖ ^ 3 := by
    have h2 : ‖(F.coeff 2 : ℚ_[p]) * x ^ 2‖ ≤ ‖x‖ ^ 2 := by
      rw [norm_mul, norm_pow]; exact mul_le_of_le_one_left (by positivity) (hai 2)
    have h1 : ‖(F.coeff 1 : ℚ_[p]) * x‖ ≤ ‖x‖ ^ 2 := by
      rw [norm_mul]
      calc _ ≤ 1 * ‖x‖ := by gcongr; exact hai 1
        _ ≤ ‖x‖ ^ 2 := by nlinarith
    have h0 : ‖(F.coeff 0 : ℚ_[p])‖ ≤ ‖x‖ ^ 2 := (hai 0).trans (by nlinarith)
    have : ‖tail‖ ≤ ‖x‖ ^ 2 := by
      refine (Padic.nonarchimedean _ _).trans (max_le ?_ h0)
      exact (Padic.nonarchimedean _ _).trans (max_le h2 h1)
    refine this.trans_lt ?_
    nlinarith [pow_pos hxpos 2]
  set a3 : ℚ_[p] := (F.coeff 3 : ℚ_[p]) with ha3def
  have ha30 : a3 ≠ 0 := by intro h; rw [h] at ha3; simp at ha3
  have hx3 : ‖a3 * x ^ 3‖ = ‖x‖ ^ 3 := by rw [norm_mul, ha3, norm_pow, one_mul]
  have hx30 : a3 * x ^ 3 ≠ 0 := mul_ne_zero ha30 (pow_ne_zero _ hx0)
  set w : ℚ_[p] := 1 + tail / (a3 * x ^ 3) with hw
  have hw1 : ‖w - 1‖ < 1 := by
    rw [hw, add_sub_cancel_left, norm_div, hx3, div_lt_one (by positivity)]; exact htl
  have hwn : ‖w‖ = 1 := norm_eq_one_of_sub_one_lt hw1
  have hPw : (F.map (algebraMap ℤ_[p] ℚ_[p])).eval x = (a3 * x ^ 3) * w := by
    rw [hP, hw]; field_simp
  have hnP : ‖(F.map (algebraMap ℤ_[p] ℚ_[p])).eval x‖ = ‖x‖ ^ 3 := by
    rw [hPw, norm_mul, hx3, hwn, mul_one]
  have hne : (F.map (algebraMap ℤ_[p] ℚ_[p])).eval x ≠ 0 := by
    rw [hPw]; exact mul_ne_zero hx30 (by intro h; rw [h] at hwn; simp at hwn)
  have hsq : IsSquare ((F.map (algebraMap ℤ_[p] ℚ_[p])).eval x) ↔ IsSquare (a3 * x) := by
    rw [hPw, isSquare_mul_iff_of_one_add hp2 hw1]
    have : a3 * x ^ 3 = (a3 * x) * x ^ 2 := by ring
    rw [this, isSquare_mul_sq_iff hx0]
  unfold sqrtDensity
  rw [hnP]
  simp only [hne, ne_eq, not_false_eq_true, and_true, hsq]


lemma outside_eq_iUnion :
    {x : ℚ_[p] | 1 < ‖x‖} =
      ⋃ n : ℕ, {x : ℚ_[p] | ‖x - 0‖ = (p : ℝ) ^ (-(-((n : ℤ) + 1)))} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, sub_zero]
  constructor
  · intro hx
    have hx0 : x ≠ 0 := by rintro rfl; rw [norm_zero] at hx; linarith
    have hn : ‖x‖ = (p : ℝ) ^ (-x.valuation) := Padic.norm_eq_zpow_neg_valuation hx0
    have hpos : 0 < -x.valuation := by
      by_contra hneg
      push Not at hneg
      have : (p : ℝ) ^ (-x.valuation) ≤ 1 := zpow_le_one_of_nonpos₀ one_lt_p.le hneg
      linarith
    refine ⟨(-x.valuation - 1).toNat, ?_⟩
    rw [hn]; congr 1; omega
  · rintro ⟨n, hn⟩
    rw [hn]
    exact one_lt_zpow₀ one_lt_p (by omega)

lemma outside_disjoint :
    Pairwise (Function.onFun Disjoint fun n : ℕ =>
      {x : ℚ_[p] | ‖x - 0‖ = (p : ℝ) ^ (-(-((n : ℤ) + 1)))}) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro x hxi hxj
  simp only [Set.mem_setOf_eq] at hxi hxj
  have := zpow_right_injective₀ (p_pos (p := p)) (one_lt_p (p := p)).ne' (hxi.symm.trans hxj)
  omega

lemma outside_term (k : ℕ) :
    2 / ENNReal.ofReal √(((p : ℝ) ^ (((2 * k + 1 : ℕ) : ℤ) + 1)) ^ 3) *
      ENNReal.ofReal (((p : ℝ) - 1) / 2 * (p : ℝ) ^ (-(-(((2 * k + 1 : ℕ) : ℤ) + 1) + 1))) =
    ENNReal.ofReal (((p : ℝ) - 1) / (p : ℝ) ^ (k + 2)) := by
  have hP : (0 : ℝ) < p := p_pos
  have e1 : (p : ℝ) ^ (((2 * k + 1 : ℕ) : ℤ) + 1) = (p : ℝ) ^ (2 * k + 2) := by
    rw [show ((2 * k + 1 : ℕ) : ℤ) + 1 = ((2 * k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have e2 : (p : ℝ) ^ (-(-(((2 * k + 1 : ℕ) : ℤ) + 1) + 1)) = (p : ℝ) ^ (2 * k + 1) := by
    rw [show -(-(((2 * k + 1 : ℕ) : ℤ) + 1) + 1) = ((2 * k + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]
  have e3 : √(((p : ℝ) ^ (2 * k + 2)) ^ 3) = (p : ℝ) ^ (3 * k + 3) := by
    rw [show ((p : ℝ) ^ (2 * k + 2)) ^ 3 = ((p : ℝ) ^ (3 * k + 3)) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [e1, e2, e3]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith [one_lt_p (p := p)]
  rw [h2, ← ENNReal.ofReal_div_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

open scoped Classical in
theorem lintegral_sqrtDensity_outside_aux (hp2 : p ≠ 2) (F : ℤ_[p][X]) (hdeg : F.natDegree = 3)
    (hlead : IsUnit F.leadingCoeff) :
    ∫⁻ x in {x : ℚ_[p] | 1 < ‖x‖}, sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x ∂haarP p =
      1 / p := by
  have hc3 : IsUnit (F.coeff 3) := by
    have : F.leadingCoeff = F.coeff 3 := by rw [Polynomial.leadingCoeff, hdeg]
    rwa [this] at hlead
  have hmeas : ∀ n : ℕ, MeasurableSet {x : ℚ_[p] | ‖x - 0‖ = (p : ℝ) ^ (-(-((n : ℤ) + 1)))} :=
    fun n => (measurableSet_singleton _).preimage
      ((continuous_norm.comp (continuous_sub_right 0)).measurable)
  rw [outside_eq_iUnion, lintegral_iUnion hmeas outside_disjoint]
  have hterm : ∀ n : ℕ,
      ∫⁻ x in {x : ℚ_[p] | ‖x - 0‖ = (p : ℝ) ^ (-(-((n : ℤ) + 1)))},
        sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x ∂haarP p =
      2 / ENNReal.ofReal √(((p : ℝ) ^ ((n : ℤ) + 1)) ^ 3) *
        haarP p (shell (F.coeff 3) (-((n : ℤ) + 1))) := by
    intro n
    refine setLIntegral_cshell hp2 hc3 0 (-((n : ℤ) + 1)) _ _ ?_
    intro x hx
    rw [neg_neg, sub_zero] at hx
    have hx1 : 1 < ‖x‖ := by
      rw [hx]; exact one_lt_zpow₀ one_lt_p (by omega)
    rw [sqrtDensity_outside hp2 F hdeg hlead x hx1, hx, sub_zero]
  rw [tsum_congr hterm]
  refine tsum_shell_series _ ?_ ?_
  · intro k
    rw [haarP_shell_odd hp2 hc3 (by
      rintro ⟨r, hr⟩; push_cast at hr; omega), mul_zero]
  · intro k
    rw [haarP_shell_even hp2 hc3 (m := -(((2 * k + 1 : ℕ) : ℤ) + 1)) ⟨-(k : ℤ) - 1, by push_cast; ring⟩]
    exact outside_term k


lemma toZMod_eval (F : ℤ_[p][X]) (x : ℤ_[p]) :
    PadicInt.toZMod (F.eval x) = (F.map (PadicInt.toZMod (p := p))).eval (PadicInt.toZMod x) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

lemma eval_map_coe (F : ℤ_[p][X]) (x : ℤ_[p]) :
    (F.map (algebraMap ℤ_[p] ℚ_[p])).eval (x : ℚ_[p]) = ((F.eval x : ℤ_[p]) : ℚ_[p]) := by
  have : (x : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] x := rfl
  rw [this, Polynomial.eval_map, Polynomial.eval₂_at_apply]; rfl

lemma natCard_sqrt (hp2 : p ≠ 2) (a : ZMod p) :
    (Nat.card {v : ZMod p // v ^ 2 = a} : ℤ) = quadraticChar (ZMod p) a + 1 := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have := quadraticChar_card_sqrts hchar a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← this]
  simp

lemma natCard_sqrt_of_ne (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    Nat.card {v : ZMod p // v ^ 2 = a} = if IsSquare a then 2 else 0 := by
  have h := natCard_sqrt hp2 a
  split_ifs with hs
  · rw [(quadraticChar_one_iff_isSquare ha).mpr hs] at h; omega
  · rw [quadraticChar_neg_one_iff_not_isSquare.mpr hs] at h; omega

lemma natCard_sqrt_zero (hp2 : p ≠ 2) : Nat.card {v : ZMod p // v ^ 2 = 0} = 1 := by
  have h := natCard_sqrt hp2 0
  rw [quadraticChar_zero] at h; omega


lemma ball_subset_int (x₀ : ℤ_[p]) {x : ℚ_[p]} (hx : x ∈ Metric.closedBall (x₀ : ℚ_[p]) (p : ℝ)⁻¹) :
    ‖x‖ ≤ 1 ∧ ‖x - (x₀ : ℚ_[p])‖ < 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_p
  refine ⟨?_, hx.trans_lt hlt⟩
  have : x = (x - (x₀ : ℚ_[p])) + (x₀ : ℚ_[p]) := by ring
  rw [this]
  exact (Padic.nonarchimedean _ _).trans (max_le (hx.trans hlt.le) x₀.2)

lemma toZMod_eq_of_close {X x₀ : ℤ_[p]} (h : ‖(X : ℚ_[p]) - (x₀ : ℚ_[p])‖ < 1) :
    PadicInt.toZMod X = PadicInt.toZMod x₀ := by
  have : ‖X - x₀‖ < 1 := by rw [PadicInt.norm_def]; push_cast; exact h
  rw [norm_lt_one_iff_toZMod, map_sub, sub_eq_zero] at this
  exact this

open scoped Classical in
lemma sqrtDensity_unit (hp2 : p ≠ 2) (G : ℚ_[p][X]) (x : ℚ_[p]) (E : ℤ_[p]) (hE : IsUnit E)
    (h : G.eval x = (E : ℚ_[p])) :
    sqrtDensity G x = if IsSquare (PadicInt.toZMod E) then 2 else 0 := by
  unfold sqrtDensity
  rw [h]
  have hn : ‖(E : ℚ_[p])‖ = 1 := norm_coe_unit hE
  have hne : (E : ℚ_[p]) ≠ 0 := by intro h0; rw [h0] at hn; simp at hn
  simp only [hne, ne_eq, not_false_eq_true, and_true, hn, Real.sqrt_one, ENNReal.ofReal_one, div_one]
  exact if_congr (isSquare_coe_iff hp2 hE) rfl rfl

open scoped Classical in
lemma lintegral_ball_unit (hp2 : p ≠ 2) (F : ℤ_[p][X]) (x₀ : ℤ_[p]) (hu : IsUnit (F.eval x₀)) :
    ∫⁻ x in Metric.closedBall (x₀ : ℚ_[p]) (p : ℝ)⁻¹,
        sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x ∂haarP p =
      (Nat.card {v : ZMod p // v ^ 2 = PadicInt.toZMod (F.eval x₀)} : ℝ≥0∞) / p := by
  have hconst : ∀ x ∈ Metric.closedBall (x₀ : ℚ_[p]) (p : ℝ)⁻¹,
      sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x =
        if IsSquare (PadicInt.toZMod (F.eval x₀)) then 2 else 0 := by
    intro x hx
    obtain ⟨h1, h2⟩ := ball_subset_int x₀ hx
    let X : ℤ_[p] := ⟨x, h1⟩
    have hX : (X : ℚ_[p]) = x := rfl
    have hXx : PadicInt.toZMod X = PadicInt.toZMod x₀ := toZMod_eq_of_close (by rw [hX]; exact h2)
    have hE : PadicInt.toZMod (F.eval X) = PadicInt.toZMod (F.eval x₀) := by
      rw [toZMod_eval, toZMod_eval, hXx]
    have hEu : IsUnit (F.eval X) := (isUnit_iff_toZMod_ne _).mpr (by
      rw [hE]; exact (isUnit_iff_toZMod_ne _).mp hu)
    rw [sqrtDensity_unit hp2 _ x (F.eval X) hEu (by rw [← hX]; exact eval_map_coe F X), hE]
  rw [setLIntegral_congr_fun Metric.isClosed_closedBall.measurableSet hconst, setLIntegral_const]
  have hvol : haarP p (Metric.closedBall (x₀ : ℚ_[p]) (p : ℝ)⁻¹) = ENNReal.ofReal (p : ℝ)⁻¹ := by
    have := haarP_closedBall_any (p := p) (x₀ : ℚ_[p]) 1
    simpa [zpow_neg_one] using this
  rw [hvol]
  have ha : PadicInt.toZMod (F.eval x₀) ≠ 0 := (isUnit_iff_toZMod_ne _).mp hu
  rw [natCard_sqrt_of_ne hp2 ha]
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hinv : ENNReal.ofReal (p : ℝ)⁻¹ = 1 / (p : ℝ≥0∞) := by
    rw [ENNReal.ofReal_inv_of_pos p_pos]; simp
  rw [hinv]
  split_ifs
  · simp [div_eq_mul_inv]
  · simp



/-! ## Points of the reduction -/

lemma eval_Ψ₂Sq_eq (W : WeierstrassCurve (ZMod p)) (x : ZMod p) :
    W.Ψ₂Sq.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [WeierstrassCurve.Ψ₂Sq]

lemma two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

lemma equation_iff_sq (hp2 : p ≠ 2) (W : WeierstrassCurve (ZMod p)) (x y : ZMod p) :
    W.toAffine.Equation x y ↔ (2 * y + W.a₁ * x + W.a₃) ^ 2 = W.Ψ₂Sq.eval x := by
  have h2 := two_ne_zero_zmod hp2
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  rw [WeierstrassCurve.Affine.equation_iff, eval_Ψ₂Sq_eq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  constructor
  · intro h; linear_combination 4 * h
  · intro h
    apply mul_left_cancel₀ h4
    linear_combination h

/-- Points of an elliptic curve in affine coordinates, with the point at infinity. -/
def pointEquivOption (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] :
    W.toAffine.Point ≃ Option {xy : ZMod p × ZMod p // W.toAffine.Equation xy.1 xy.2} where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x, y), (WeierstrassCurve.Affine.equation_iff_nonsingular).mpr h⟩
  invFun
    | none => .zero
    | some ⟨_, h⟩ => WeierstrassCurve.Affine.Point.mk h
  left_inv := by
    intro P; cases P <;> rfl
  right_inv := by
    intro P; rcases P with _ | ⟨⟨x, y⟩, h⟩ <;> rfl

theorem card_point_eq_aux (hp2 : p ≠ 2) (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] :
    Nat.card W.toAffine.Point = 1 + ∑ x : ZMod p, Nat.card {v : ZMod p // v ^ 2 = W.Ψ₂Sq.eval x} := by
  have h2 := two_ne_zero_zmod hp2
  rw [Nat.card_congr (pointEquivOption W), Finite.card_option,
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun x y : ZMod p => W.toAffine.Equation x y)), Nat.card_sigma, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Nat.card_congr (Equiv.subtypeEquiv
    ((Equiv.mulLeft₀ 2 h2).trans (Equiv.addRight (W.a₁ * x + W.a₃))) ?_)
  intro y
  rw [equation_iff_sq hp2]
  simp [add_assoc]


/-! ### The case of a simple root modulo `p` -/

open scoped Classical in
lemma sqrtDensity_root (hp2 : p ≠ 2) (F : ℤ_[p][X]) (r : ℤ_[p]) (hr : F.eval r = 0)
    (hr' : IsUnit (F.derivative.eval r)) (x : ℚ_[p]) (hxr : x ≠ (r : ℚ_[p])) (hx : ‖x - r‖ < 1) :
    sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x =
      if IsSquare (((F.derivative.eval r : ℤ_[p]) : ℚ_[p]) * (x - r))
        then 2 / ENNReal.ofReal √‖x - r‖ else 0 := by
  set t : ℚ_[p] := x - r with htdef
  have ht0 : t ≠ 0 := sub_ne_zero.mpr hxr
  set T : ℤ_[p] := ⟨t, hx.le⟩ with hT
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion F r T
  set c : ℚ_[p] := ((F.derivative.eval r : ℤ_[p]) : ℚ_[p]) with hcdef
  have hc1 : ‖c‖ = 1 := norm_coe_unit hr'
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc1; simp at hc1
  have hxeq : x = ((r + T : ℤ_[p]) : ℚ_[p]) := by
    push_cast; simp only [hT, htdef]; ring
  have hG : (F.map (algebraMap ℤ_[p] ℚ_[p])).eval x = c * t + (k : ℚ_[p]) * t ^ 2 := by
    rw [hxeq, eval_map_coe, hk, hr]
    push_cast
    simp only [hT, hcdef]
    ring
  have hk1 : ‖(k : ℚ_[p])‖ ≤ 1 := k.2
  set w : ℚ_[p] := 1 + (k : ℚ_[p]) * t / c with hw
  have hw1 : ‖w - 1‖ < 1 := by
    rw [hw, add_sub_cancel_left, norm_div, norm_mul, hc1, div_one]
    calc ‖(k : ℚ_[p])‖ * ‖t‖ ≤ 1 * ‖t‖ := by gcongr
      _ < 1 := by rw [one_mul]; exact hx
  have hwn : ‖w‖ = 1 := norm_eq_one_of_sub_one_lt hw1
  have hGw : (F.map (algebraMap ℤ_[p] ℚ_[p])).eval x = (c * t) * w := by
    rw [hG, hw]; field_simp
  have hct : c * t ≠ 0 := mul_ne_zero hc0 ht0
  have hn : ‖(F.map (algebraMap ℤ_[p] ℚ_[p])).eval x‖ = ‖t‖ := by
    rw [hGw, norm_mul, norm_mul, hc1, hwn, one_mul, mul_one]
  have hne : (F.map (algebraMap ℤ_[p] ℚ_[p])).eval x ≠ 0 := by
    rw [hGw]; exact mul_ne_zero hct (by intro h; rw [h] at hwn; simp at hwn)
  have hsq : IsSquare ((F.map (algebraMap ℤ_[p] ℚ_[p])).eval x) ↔ IsSquare (c * t) := by
    rw [hGw, isSquare_mul_iff_of_one_add hp2 hw1]
  unfold sqrtDensity
  rw [hn]
  simp only [hne, ne_eq, not_false_eq_true, and_true, hsq]

lemma exists_root_near (F : ℤ_[p][X]) (x₀ : ℤ_[p]) (hn : ¬ IsUnit (F.eval x₀))
    (hu : IsUnit (F.derivative.eval x₀)) :
    ∃ r : ℤ_[p], F.eval r = 0 ∧ ‖r - x₀‖ < 1 ∧ IsUnit (F.derivative.eval r) := by
  have h1 : ‖F.eval x₀‖ < 1 := PadicInt.not_isUnit_iff.mp hn
  have h2 : ‖F.derivative.eval x₀‖ = 1 := PadicInt.isUnit_iff.mp hu
  have hnorm : ‖F.aeval x₀‖ < ‖F.derivative.aeval x₀‖ ^ 2 := by
    simp only [Polynomial.coe_aeval_eq_eval]
    rw [h2]; simpa using h1
  obtain ⟨z, hz, hzd, hzn, -⟩ := hensels_lemma hnorm
  simp only [Polynomial.coe_aeval_eq_eval] at hz hzd hzn
  refine ⟨z, hz, by rwa [h2] at hzd, PadicInt.isUnit_iff.mpr (by rw [hzn, h2])⟩

lemma closedBall_eq_of_close {a b : ℚ_[p]} (h : ‖a - b‖ < 1) :
    Metric.closedBall a (p : ℝ)⁻¹ = Metric.closedBall b (p : ℝ)⁻¹ := by
  have h' : ‖a - b‖ ≤ (p : ℝ)⁻¹ := by
    have := (norm_le_zpow_iff_lt (a - b) (-1)).mpr (by simpa using h)
    simpa [zpow_neg_one] using this
  ext x
  simp only [Metric.mem_closedBall, dist_eq_norm]
  constructor
  · intro hx
    have : x - b = (x - a) + (a - b) := by ring
    rw [this]; exact (Padic.nonarchimedean _ _).trans (max_le hx h')
  · intro hx
    have : x - a = (x - b) + (b - a) := by ring
    rw [this]; exact (Padic.nonarchimedean _ _).trans (max_le hx (by rwa [norm_sub_rev]))

lemma ball_eq_union_root (r : ℚ_[p]) :
    Metric.closedBall r (p : ℝ)⁻¹ =
      (⋃ n : ℕ, {x : ℚ_[p] | ‖x - r‖ = (p : ℝ) ^ (-((n : ℤ) + 1))}) ∪ {r} := by
  ext x
  simp only [Metric.mem_closedBall, dist_eq_norm, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq,
    Set.mem_singleton_iff]
  constructor
  · intro hx
    by_cases hxr : x = r
    · exact Or.inr hxr
    · left
      have ht0 : x - r ≠ 0 := sub_ne_zero.mpr hxr
      have hn : ‖x - r‖ = (p : ℝ) ^ (-(x - r).valuation) := Padic.norm_eq_zpow_neg_valuation ht0
      have hle : (p : ℝ) ^ (-(x - r).valuation) ≤ (p : ℝ) ^ (-1 : ℤ) := by
        rw [← hn, zpow_neg_one]; exact hx
      have := (zpow_le_zpow_iff_right₀ one_lt_p).mp hle
      refine ⟨((x - r).valuation - 1).toNat, ?_⟩
      rw [hn]; congr 1; omega
  · rintro (⟨n, hn⟩ | hx)
    · rw [hn, ← zpow_neg_one]
      exact zpow_le_zpow_right₀ one_lt_p.le (by omega)
    · rw [hx]; simp

lemma root_disjoint (r : ℚ_[p]) :
    Pairwise (Function.onFun Disjoint fun n : ℕ =>
      {x : ℚ_[p] | ‖x - r‖ = (p : ℝ) ^ (-((n : ℤ) + 1))}) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro x hxi hxj
  simp only [Set.mem_setOf_eq] at hxi hxj
  have := zpow_right_injective₀ (p_pos (p := p)) (one_lt_p (p := p)).ne' (hxi.symm.trans hxj)
  omega

lemma root_term (k : ℕ) :
    2 / ENNReal.ofReal √((p : ℝ) ^ (-(((2 * k + 1 : ℕ) : ℤ) + 1))) *
      ENNReal.ofReal (((p : ℝ) - 1) / 2 * (p : ℝ) ^ (-(((2 * k + 1 : ℕ) : ℤ) + 1 + 1))) =
    ENNReal.ofReal (((p : ℝ) - 1) / (p : ℝ) ^ (k + 2)) := by
  have hP : (0 : ℝ) < p := p_pos
  have e1 : (p : ℝ) ^ (-(((2 * k + 1 : ℕ) : ℤ) + 1)) = ((p : ℝ) ^ (k + 1)) ⁻¹ ^ 2 := by
    rw [show -(((2 * k + 1 : ℕ) : ℤ) + 1) = -((2 * k + 2 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, inv_pow, ← pow_mul]
    congr 2; ring
  have e2 : (p : ℝ) ^ (-(((2 * k + 1 : ℕ) : ℤ) + 1 + 1)) = ((p : ℝ) ^ (2 * k + 3))⁻¹ := by
    rw [show -(((2 * k + 1 : ℕ) : ℤ) + 1 + 1) = -((2 * k + 3 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast]
  rw [e1, e2, Real.sqrt_sq (by positivity)]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith [one_lt_p (p := p)]
  rw [h2, ← ENNReal.ofReal_div_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

open scoped Classical in
lemma lintegral_ball_root (hp2 : p ≠ 2) (F : ℤ_[p][X]) (x₀ : ℤ_[p]) (hn : ¬ IsUnit (F.eval x₀))
    (hu : IsUnit (F.derivative.eval x₀)) :
    ∫⁻ x in Metric.closedBall (x₀ : ℚ_[p]) (p : ℝ)⁻¹,
        sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x ∂haarP p = 1 / p := by
  obtain ⟨r, hr, hrx, hr'⟩ := exists_root_near F x₀ hn hu
  have hclose : ‖(x₀ : ℚ_[p]) - (r : ℚ_[p])‖ < 1 := by
    rw [norm_sub_rev]
    have : ‖r - x₀‖ < 1 := hrx
    rw [PadicInt.norm_def] at this; push_cast at this; exact this
  rw [closedBall_eq_of_close hclose, ball_eq_union_root]
  have hmeas : ∀ n : ℕ, MeasurableSet {x : ℚ_[p] | ‖x - (r : ℚ_[p])‖ = (p : ℝ) ^ (-((n : ℤ) + 1))} :=
    fun n => (measurableSet_singleton _).preimage
      ((continuous_norm.comp (continuous_sub_right _)).measurable)
  have hdisj : Disjoint (⋃ n : ℕ, {x : ℚ_[p] | ‖x - (r : ℚ_[p])‖ = (p : ℝ) ^ (-((n : ℤ) + 1))})
      {(r : ℚ_[p])} := by
    rw [Set.disjoint_singleton_right]
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, sub_self, norm_zero, not_exists]
    intro n h
    exact (zpow_p_pos _).ne h
  rw [lintegral_union (measurableSet_singleton _) hdisj, lintegral_iUnion hmeas (root_disjoint _)]
  have hsing : ∫⁻ x in {(r : ℚ_[p])}, sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x ∂haarP p = 0 := by
    rw [setLIntegral_congr_fun (measurableSet_singleton _) (g := fun _ => 0)]
    · simp
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have : (F.map (algebraMap ℤ_[p] ℚ_[p])).eval (r : ℚ_[p]) = 0 := by
        rw [eval_map_coe, hr]; simp
      simp [sqrtDensity, this]
  rw [hsing, add_zero]
  have hterm : ∀ n : ℕ,
      ∫⁻ x in {x : ℚ_[p] | ‖x - (r : ℚ_[p])‖ = (p : ℝ) ^ (-((n : ℤ) + 1))},
        sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x ∂haarP p =
      2 / ENNReal.ofReal √((p : ℝ) ^ (-((n : ℤ) + 1))) *
        haarP p (shell (F.derivative.eval r) ((n : ℤ) + 1)) := by
    intro n
    refine setLIntegral_cshell hp2 hr' (r : ℚ_[p]) ((n : ℤ) + 1) _ _ ?_
    intro x hx
    have hlt : ‖x - (r : ℚ_[p])‖ < 1 := by
      rw [hx]; exact zpow_lt_one_of_neg₀ one_lt_p (by omega)
    have hxr : x ≠ (r : ℚ_[p]) := by
      intro h; rw [h, sub_self, norm_zero] at hx; exact (zpow_p_pos _).ne hx
    rw [sqrtDensity_root hp2 F r hr hr' x hxr hlt, hx]
  rw [tsum_congr hterm]
  refine tsum_shell_series _ ?_ ?_
  · intro k
    rw [haarP_shell_odd hp2 hr' (by
      rintro ⟨s, hs⟩; push_cast at hs; omega), mul_zero]
  · intro k
    rw [haarP_shell_even hp2 hr' (m := ((2 * k + 1 : ℕ) : ℤ) + 1) ⟨(k : ℤ) + 1, by push_cast; ring⟩]
    exact root_term k

lemma lintegral_ball_aux (hp2 : p ≠ 2) (F : ℤ_[p][X]) (x₀ : ℤ_[p])
    (h : IsUnit (F.eval x₀) ∨ IsUnit (F.derivative.eval x₀)) :
    ∫⁻ x in Metric.closedBall (x₀ : ℚ_[p]) (p : ℝ)⁻¹,
        sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x ∂haarP p =
      (Nat.card {v : ZMod p // v ^ 2 = PadicInt.toZMod (F.eval x₀)} : ℝ≥0∞) / p := by
  by_cases hu : IsUnit (F.eval x₀)
  · exact lintegral_ball_unit hp2 F x₀ hu
  · have hd : IsUnit (F.derivative.eval x₀) := h.resolve_left hu
    rw [lintegral_ball_root hp2 F x₀ hu hd]
    have h0 : PadicInt.toZMod (F.eval x₀) = 0 := by
      rw [← not_ne_iff, ← isUnit_iff_toZMod_ne]; exact hu
    rw [h0, natCard_sqrt_zero hp2]
    simp


lemma sum_fin_zmod {M : Type*} [AddCommMonoid M] (g : ZMod p → M) :
    ∑ j : Fin p, g ((j : ℕ) : ZMod p) = ∑ a : ZMod p, g a := by
  refine Fintype.sum_bijective (fun j : Fin p => ((j : ℕ) : ZMod p)) ?_ _ _ (fun _ => rfl)
  constructor
  · intro i j h
    have := (ZMod.natCast_eq_natCast_iff' i j p).mp h
    rw [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at this
    exact Fin.ext this
  · intro a
    exact ⟨⟨a.val, ZMod.val_lt a⟩, by simp⟩

lemma univ_eq_union_balls :
    (Set.univ : Set ℚ_[p]) = {x : ℚ_[p] | 1 < ‖x‖} ∪
      ⋃ j : Fin p, Metric.closedBall (((j : ℕ) : ℤ_[p]) : ℚ_[p]) (p : ℝ)⁻¹ := by
  ext x
  simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, true_iff]
  by_cases hx : 1 < ‖x‖
  · exact Or.inl hx
  · right
    push Not at hx
    obtain ⟨j, hj⟩ := exists_fin_close (⟨x, hx⟩ : ℤ_[p])
    refine ⟨j, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have := (norm_sub_nat_le_iff (⟨x, hx⟩ : ℤ_[p]) j).mpr hj
    simpa [zpow_neg_one] using this

lemma balls_disjoint :
    Pairwise (Function.onFun Disjoint fun j : Fin p =>
      Metric.closedBall (((j : ℕ) : ℤ_[p]) : ℚ_[p]) (p : ℝ)⁻¹) := by
  intro i j hij
  have := closedBall_disjoint (p := p) 0 hij
  simpa [zpow_neg_one, Function.onFun] using this

lemma balls_disjoint_outside :
    Disjoint {x : ℚ_[p] | 1 < ‖x‖}
      (⋃ j : Fin p, Metric.closedBall (((j : ℕ) : ℤ_[p]) : ℚ_[p]) (p : ℝ)⁻¹) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [Set.mem_iUnion, Metric.mem_closedBall, dist_eq_norm] at hx'
  obtain ⟨j, hj⟩ := hx'
  have h1 := (ball_subset_int ((j : ℕ) : ℤ_[p]) (x := x) (by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hj)).1
  simp only [Set.mem_setOf_eq] at hx
  linarith

theorem lintegral_sqrtDensity_aux (hp2 : p ≠ 2) (F : ℤ_[p][X]) (hdeg : F.natDegree = 3)
    (hlead : IsUnit F.leadingCoeff)
    (hsep : ∀ x₀ : ℤ_[p], IsUnit (F.eval x₀) ∨ IsUnit (F.derivative.eval x₀)) :
    ∫⁻ x, sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x ∂haarP p =
      ((1 + ∑ x : ZMod p, Nat.card {v : ZMod p // v ^ 2 = (F.map (PadicInt.toZMod (p := p))).eval x} : ℕ) :
        ℝ≥0∞) / p := by
  have hmeasB : ∀ j : Fin p, MeasurableSet
      (Metric.closedBall (((j : ℕ) : ℤ_[p]) : ℚ_[p]) (p : ℝ)⁻¹) :=
    fun j => Metric.isClosed_closedBall.measurableSet
  rw [← setLIntegral_univ, univ_eq_union_balls,
    lintegral_union (MeasurableSet.iUnion hmeasB) balls_disjoint_outside,
    lintegral_sqrtDensity_outside_aux hp2 F hdeg hlead,
    lintegral_iUnion hmeasB balls_disjoint, tsum_fintype]
  have hterm : ∀ j : Fin p,
      ∫⁻ x in Metric.closedBall (((j : ℕ) : ℤ_[p]) : ℚ_[p]) (p : ℝ)⁻¹,
        sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x ∂haarP p =
      (Nat.card {v : ZMod p // v ^ 2 = (F.map (PadicInt.toZMod (p := p))).eval ((j : ℕ) : ZMod p)} :
        ℝ≥0∞) / p := by
    intro j
    rw [lintegral_ball_aux hp2 F _ (hsep _), toZMod_eval, map_natCast]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [sum_fin_zmod (fun a : ZMod p => (Nat.card {v : ZMod p // v ^ 2 =
    (F.map (PadicInt.toZMod (p := p))).eval a} : ℝ≥0∞) / p)]
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_sum, ENNReal.add_div]
  congr 1
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-! ## The integral of `sqrtDensity` for an integral cubic, $p$ odd -/

/-- **The kernel of reduction.** For an integral cubic $F$ with unit leading coefficient and $p$ odd, the region
$|x|_p > 1$ contributes $1/p$: on $|x|_p = p^{2k}$, $F(x)$ is a square iff $x p^{2k}$ is a square unit, and
$\sum_{k \ge 1} 2p^{-3k}\cdot\tfrac12(1 - p^{-1})p^{2k} = 1/p$; odd valuations of $x$ give no squares. -/
theorem lintegral_sqrtDensity_outside (hp2 : p ≠ 2) (F : ℤ_[p][X]) (hdeg : F.natDegree = 3)
    (hlead : IsUnit F.leadingCoeff) :
    ∫⁻ x in {x : ℚ_[p] | 1 < ‖x‖}, sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x ∂haarP p = 1 / p :=
  lintegral_sqrtDensity_outside_aux hp2 F hdeg hlead

/-- **A residue disc.** For an integral polynomial $F$, $p$ odd and $x_0 \in \mathbb Z_p$ such that either $F(x_0)$
is a unit or $x_0$ is a simple root of $F$ modulo $p$, the disc $x_0 + p\mathbb Z_p$ contributes
$\#\{v \in \mathbb F_p : v^2 = \bar F(\bar x_0)\}/p$ (that is $2/p$, $0$, or $1/p$ in the case of a simple root). -/
theorem lintegral_sqrtDensity_ball (hp2 : p ≠ 2) (F : ℤ_[p][X]) (x₀ : ℤ_[p])
    (h : IsUnit (F.eval x₀) ∨ IsUnit (F.derivative.eval x₀)) :
    ∫⁻ x in Metric.closedBall (x₀ : ℚ_[p]) (p : ℝ)⁻¹,
        sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x ∂haarP p =
      (Nat.card {v : ZMod p // v ^ 2 = PadicInt.toZMod (F.eval x₀)} : ℝ≥0∞) / p :=
  lintegral_ball_aux hp2 F x₀ h

/-- **The whole line.** For an integral cubic $F$ with unit leading coefficient whose reduction has only simple
roots, $p$ odd: $\int_{\mathbb Q_p}$ `sqrtDensity` $= \bigl(1 + \sum_{\bar x \in \mathbb F_p}\#\{v : v^2 =
\bar F(\bar x)\}\bigr)/p$. -/
theorem lintegral_sqrtDensity (hp2 : p ≠ 2) (F : ℤ_[p][X]) (hdeg : F.natDegree = 3)
    (hlead : IsUnit F.leadingCoeff)
    (hsep : ∀ x₀ : ℤ_[p], IsUnit (F.eval x₀) ∨ IsUnit (F.derivative.eval x₀)) :
    ∫⁻ x, sqrtDensity (F.map (algebraMap ℤ_[p] ℚ_[p])) x ∂haarP p =
      ((1 + ∑ x : ZMod p, Nat.card {v : ZMod p // v ^ 2 = (F.map (PadicInt.toZMod (p := p))).eval x} : ℕ) :
        ℝ≥0∞) / p := by
  exact lintegral_sqrtDensity_aux hp2 F hdeg hlead hsep

/-! ## Points of the reduction -/

/-- **Point count by completing the square** ($p$ odd): for an elliptic curve over $\mathbb F_p$,
$\#E(\mathbb F_p) = 1 + \sum_x \#\{v : v^2 = \Psi_2^2(x)\}$ ($v = 2y + a_1x + a_3$). -/
theorem card_point_eq_of_isElliptic (hp2 : p ≠ 2) (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] :
    Nat.card W.toAffine.Point = 1 + ∑ x : ZMod p, Nat.card {v : ZMod p // v ^ 2 = W.Ψ₂Sq.eval x} :=
  card_point_eq_aux hp2 W

/-! ## Remark 10.6 (a), (c) at good reduction -/


/-! ### Good reduction -/

/-- Point counts are invariant under a field isomorphism. -/
lemma card_point_map_equiv {K L : Type*} [Field K] [Field L] (φ : K ≃+* L)
    (W : WeierstrassCurve K) :
    Nat.card (W.map (φ : K →+* L)).toAffine.Point = Nat.card W.toAffine.Point := by
  let f : W.toAffine.Point → (W.map (φ : K →+* L)).toAffine.Point
    | .zero => .zero
    | .some x y h => .some (φ x) (φ y)
        ((WeierstrassCurve.Affine.map_nonsingular W (f := (φ : K →+* L)) φ.injective x y).mpr h)
  have hf : Function.Bijective f := by
    constructor
    · rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hPQ
      · rfl
      · simp [f] at hPQ
      · simp [f] at hPQ
      · have hPQ' : WeierstrassCurve.Affine.Point.some (φ x) (φ y) _ =
            WeierstrassCurve.Affine.Point.some (φ x') (φ y') _ := hPQ
        injection hPQ' with h1 h2
        obtain rfl := φ.injective h1
        obtain rfl := φ.injective h2
        rfl
    · intro P
      cases P with
      | zero => exact ⟨.zero, rfl⟩
      | some x y h =>
        have hh : W.toAffine.Nonsingular (φ.symm x) (φ.symm y) := by
          refine (WeierstrassCurve.Affine.map_nonsingular W (f := (φ : K →+* L)) φ.injective _ _).mp ?_
          simpa using h
        refine ⟨.some _ _ hh, ?_⟩
        simp [f]
  exact (Nat.card_eq_of_bijective f hf).symm

lemma natDegree_Ψ₂Sq_int (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ_[p]) :
    W.Ψ₂Sq.natDegree = 3 ∧ IsUnit W.Ψ₂Sq.leadingCoeff := by
  have h4 : IsUnit (4 : ℤ_[p]) := by
    have : (4 : ℤ_[p]) = 2 * 2 := by norm_num
    rw [PadicInt.isUnit_iff, this, norm_mul, norm_two_eq_one hp2, one_mul]
  have h40 : (4 : ℤ_[p]) ≠ 0 := h4.ne_zero
  unfold WeierstrassCurve.Ψ₂Sq
  exact ⟨Polynomial.natDegree_cubic h40, by rw [Polynomial.leadingCoeff_cubic h40]; exact h4⟩

theorem remark_10_6_a_aux (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p])
    [W.HasGoodReduction ℤ_[p]] :
    omegaVolume W = (Nat.card (W.reduction ℤ_[p]).toAffine.Point : ℝ≥0∞) / p := by
  classical
  set Wi : WeierstrassCurve ℤ_[p] := WeierstrassCurve.integralModel ℤ_[p] W with hWi
  have hW : W = Wi.map (algebraMap ℤ_[p] ℚ_[p]) :=
    (WeierstrassCurve.baseChange_integralModel_eq ℤ_[p] W).symm
  have hΨ : W.Ψ₂Sq = Wi.Ψ₂Sq.map (algebraMap ℤ_[p] ℚ_[p]) := by
    have := congrArg WeierstrassCurve.Ψ₂Sq hW
    rwa [WeierstrassCurve.map_Ψ₂Sq] at this
  have hell : (W.reduction ℤ_[p]).IsElliptic :=
    (WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction ℤ_[p]).mp inferInstance
  set W₀ : WeierstrassCurve (ZMod p) := Wi.map (PadicInt.toZMod (p := p)) with hW₀
  have hW₀' : W₀ = (W.reduction ℤ_[p]).map (PadicInt.residueField (p := p) : _ →+* ZMod p) := by
    rw [WeierstrassCurve.reduction, WeierstrassCurve.map_map, hW₀]
    rfl
  have hell₀ : W₀.IsElliptic := by
    rw [hW₀', WeierstrassCurve.isElliptic_iff, WeierstrassCurve.map_Δ]
    exact ((WeierstrassCurve.isElliptic_iff _).mp hell).map _
  have hcard : Nat.card (W.reduction ℤ_[p]).toAffine.Point = Nat.card W₀.toAffine.Point := by
    rw [hW₀']
    exact (card_point_map_equiv (PadicInt.residueField (p := p)) _).symm
  have hF : Wi.Ψ₂Sq.map (PadicInt.toZMod (p := p)) = W₀.Ψ₂Sq := by
    rw [hW₀, WeierstrassCurve.map_Ψ₂Sq]
  obtain ⟨hdeg, hlead⟩ := natDegree_Ψ₂Sq_int hp2 Wi
  have hsep : ∀ x₀ : ℤ_[p], IsUnit (Wi.Ψ₂Sq.eval x₀) ∨ IsUnit (Wi.Ψ₂Sq.derivative.eval x₀) := by
    intro x₀
    by_cases h0 : PadicInt.toZMod (Wi.Ψ₂Sq.eval x₀) = 0
    · right
      rw [isUnit_iff_toZMod_ne, toZMod_eval, ← Polynomial.derivative_map, hF]
      refine WeierstrassCurve.eval_derivative_Ψ₂Sq_ne_zero W₀ (two_ne_zero_zmod hp2) ?_
      rw [toZMod_eval, hF] at h0
      exact h0
    · left
      exact (isUnit_iff_toZMod_ne _).mpr h0
  unfold omegaVolume omegaDensity
  rw [hΨ, lintegral_sqrtDensity_aux hp2 Wi.Ψ₂Sq hdeg hlead hsep, hcard,
    card_point_eq_aux hp2 W₀]
  simp only [hF]

lemma natCard_residueField : Nat.card (IsLocalRing.ResidueField ℤ_[p]) = p := by
  rw [Nat.card_congr (PadicInt.residueField (p := p)).toEquiv, Nat.card_zmod]

/-- **Milne, Remark IV.10.6 (a), good reduction, $p$ odd** (pdf p. 173): for a minimal equation with good reduction,
$\int_{E(\mathbb Q_p)}|\omega|_p = N_p/p$, $N_p = \#\tilde E(\mathbb F_p)$ the points of the reduction (here
$c_p = 1$). -/
@[kb "milne2006ec" "Ch. IV, Remark 10.6 (a), ∫|ω| = c_p N_p / p (good reduction, p odd), pdf p. 173"]
theorem remark_10_6_a_good (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p]) [W.HasGoodReduction ℤ_[p]] :
    omegaVolume W = (Nat.card (W.reduction ℤ_[p]).toAffine.Point : ℝ≥0∞) / p :=
  remark_10_6_a_aux hp2 W

/-- The value $f_p(p^{-1})$ of Mathlib's local polynomial $f_p(T)$ of `W` at $T = p^{-1}$, i.e.
$L_p(E, 1)^{-1}$ ($L_p(E, s) = f_p(p^{-s})^{-1}$). -/
noncomputable def localFactorInvAtOne (W : WeierstrassCurve ℚ_[p]) : ℝ :=
  ((W.localPolynomial ℤ_[p]).map (Int.castRingHom ℝ)).eval (p : ℝ)⁻¹

/-- **Milne, Remark IV.10.6 (c), good reduction, $p$ odd** (pdf p. 173): for a curve with good reduction,
$\int_{E(\mathbb Q_p)}|\omega|_p = L_p(E, 1)^{-1}$ on its minimal model, i.e.
$L_p(E, 1)\int_{E(\mathbb Q_p)}|\omega|_p = 1 = c_p$. -/
@[kb "milne2006ec" "Ch. IV, Remark 10.6 (c), L_p(E,1) ∫|ω| = c_p (good reduction, p odd), pdf p. 173"]
theorem remark_10_6_c_good (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p])
    [(W.minimal ℤ_[p]).HasGoodReduction ℤ_[p]] :
    omegaVolume (W.minimal ℤ_[p]) = ENNReal.ofReal (localFactorInvAtOne W) := by
  classical
  rw [remark_10_6_a_good hp2 (W.minimal ℤ_[p])]
  unfold localFactorInvAtOne WeierstrassCurve.localPolynomial
  have hgood : (W.minimal ℤ_[p]).HasGoodReduction ℤ_[p] := inferInstance
  simp only [hgood, ite_true, natCard_residueField]
  have hP : (0 : ℝ) < p := p_pos
  generalize Nat.card (WeierstrassCurve.reduction ℤ_[p] (W.minimal ℤ_[p])).toAffine.Point = N
  have hev : Polynomial.eval (p : ℝ)⁻¹ (Polynomial.map (Int.castRingHom ℝ)
      (1 - Polynomial.C ((p : ℤ) + 1 - (N : ℤ)) * Polynomial.X + Polynomial.C (p : ℤ) * Polynomial.X ^ 2 : Polynomial ℤ))
      = (N : ℝ) / p := by
    simp
    field_simp
    ring
  rw [hev, ENNReal.ofReal_div_of_pos hP, ENNReal.ofReal_natCast]
  simp

/-! ## The general statement -/

/-- **Milne, Remark IV.10.6 (a), (c)** (pdf p. 173), for every prime and every reduction type, as a named statement
(proved here at good reduction for $p$ odd: `remark_10_6_a_good`, `remark_10_6_c_good`; derived from named inputs
in `remark10_6_of`, Ch4LocalPeriodRemark.lean):
(a) on a minimal equation, $\int_{E(\mathbb Q_p)}|\omega|_p = c_p N_p/p$, with $c_p$ Formal Conjectures' local
`tamagawaNumber` of the integral model and $N_p = \#\tilde E_{ns}(\mathbb F_p)$ (Mathlib's `Point` type of the
reduction consists of its nonsingular points); (c) $\int_{E(\mathbb Q_p)}|\omega|_p = c_p L_p(E, 1)^{-1}$. -/
@[kb "milne2006ec" "Ch. IV, Remark 10.6 (a), (c), pdf p. 173"]
structure Remark10_6 : Prop where
  a : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℚ_[p]) [W.IsElliptic] [W.IsMinimal ℤ_[p]],
    omegaVolume W = (FormalConjectures.tamagawaNumber ℚ_[p] (W.integralModel ℤ_[p]).toProjective : ℝ≥0∞) *
      Nat.card (W.reduction ℤ_[p]).toAffine.Point / p
  c : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℚ_[p]) [W.IsElliptic],
    omegaVolume (W.minimal ℤ_[p]) =
      (FormalConjectures.tamagawaNumber ℚ_[p] ((W.minimal ℤ_[p]).integralModel ℤ_[p]).toProjective : ℝ≥0∞) *
        ENNReal.ofReal (localFactorInvAtOne W)

end NumberFieldKB.MilneEC.LocalPeriod
