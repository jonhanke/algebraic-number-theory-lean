import NumberFieldKB.WeilBNT.FunctionField.IdeleZeta
import NumberFieldKB.WeilBNT.FunctionField.HeckeFF

/-!
# Weil's normalization of the Haar measure on the ideles of a function field (VII.§5, p. 120)

Weil fixes the Haar measure $\mu$ on $k_{\mathbb A}^\times$ through its image on $G_k=k_{\mathbb A}^\times/k^\times$
(Chap. II-4, formula (6): $\int f\,d\mu=\int_{G_k}\sum_{\xi\in k^\times}f(z\xi)\,d\nu(\dot z)$), and takes $\nu$ to be
$\mu_1\times\nu_N$ on $G_k=G_k^1\times N$ with $\mu_1(G_k^1)=1$ and $\nu_N(\{1\})=1$. So Weil's normalization says
exactly: $\nu(G_k^1)=1$ for the image $\nu$ of $\mu$.

* `FFIdeleGroup.IsQuotientMeasure μ ν`: $\nu$ is the image of $\mu$ on $G_k$ (Weil II-4 (6), for non-negative
  measurable $f$).
* **`FFIdeleGroup.measure_normOne_quotient`**: for every Haar measure $\mu$ and every such $\nu$,
  $\nu(G_k^1)=h\,\mu(\prod_v\mathfrak r_v^\times)/(q-1)$; equivalently (`zetaConst_eq_quotient`) the constant
  $c_\mu$ of `weil_VII_5_thm2_ff` is $\nu(G_k^1)$.
* **`FFIdeleGroup.weil_VII_5_cor7_quotient`**: Weil VII.§5 Cor. 7 for every Haar measure normalized as Weil does
  ($\nu(G_k^1)=1$).

Proof: $G_k^1$ is the disjoint union over the $h$ classes $C\in D_0/P$ of the images of the cosets
$\{\operatorname{div}z=D_C\}$; for such a coset $S$, $\sum_\xi\mathbf 1_S(z\xi)$ is $q-1$ or $0$ (the elements of $k^\times$
without zeros and poles are the constants $\mathbb F_q^\times$), so $\mu(S)=(q-1)\,\nu(\dot S)$ and
$\mu(S)=\mu(\prod_v\mathfrak r_v^\times)$.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

namespace NumberFieldKB.WeilBNT.FF

noncomputable section

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

set_option linter.unusedSectionVars false

open Classical

namespace FFIdeleGroup

/-- **$\nu$ is the image of $\mu$ on $G_k=k_{\mathbb A}^\times/k^\times$** (Weil II-4, formula (6)):
$\int f\,d\mu=\int_{G_k}\big(\sum_{\xi\in k^\times}f(\xi z)\big)\,d\nu$ for every non-negative measurable $f$. -/
def IsQuotientMeasure (μ : Measure (FFIdeleGroup Fq k)) (ν : Measure (FFIdeleClassGroup Fq k)) : Prop :=
  ∀ f : FFIdeleGroup Fq k → ℝ≥0∞, Measurable f → ∀ F : FFIdeleClassGroup Fq k → ℝ≥0∞,
    (∀ z, F (QuotientGroup.mk z) = ∑' ξ : kˣ, f (principal ξ * z)) → ∫⁻ z, f z ∂μ = ∫⁻ x, F x ∂ν

variable (Fq k) in
/-- $G_k^1$, the image of the ideles of norm $1$ in $G_k$. -/
def classNormOne : Set (FFIdeleClassGroup Fq k) := QuotientGroup.mk '' (normOne Fq k : Set (FFIdeleGroup Fq k))

theorem _root_.NumberFieldKB.WeilBNT.FF.Divisor.div_inv' (ξ : kˣ) :
    Divisor.div ξ⁻¹ = -(Divisor.div ξ : Divisor Fq k) := by
  have := Divisor.div_mul (Fq := Fq) ξ ξ⁻¹
  rw [mul_inv_cancel, Divisor.div_one] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

/-- The elements of $k^\times$ with divisor $E$. -/
def divSet (E : Divisor Fq k) : Set kˣ := {ξ | Divisor.div ξ = E}

/-- The elements without zeros and poles are the constants. -/
theorem divSet_zero (hc : IsConstantField Fq k) :
    divSet (Fq := Fq) (k := k) 0 = Set.range (Units.map (algebraMap Fq k).toMonoidHom) := by
  ext ξ
  simp only [divSet, Set.mem_setOf_eq, Set.mem_range]
  rw [Divisor.div_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨c, hc'⟩ := hc _ h
    have hc0 : c ≠ 0 := by
      rintro rfl; rw [map_zero] at hc'; exact ξ.ne_zero hc'.symm
    exact ⟨Units.mk0 c hc0, Units.ext (by simpa using hc')⟩
  · rintro ⟨c, rfl⟩
    exact isAlgebraic_algebraMap (c : Fq)

theorem encard_divSet_zero (hc : IsConstantField Fq k) :
    (divSet (Fq := Fq) (k := k) 0).encard = (Nat.card Fq - 1 : ℕ) := by
  have hinj : Function.Injective (Units.map (algebraMap Fq k).toMonoidHom) := by
    intro a b h
    apply Units.ext
    have := congrArg Units.val h
    exact (algebraMap Fq k).injective this
  rw [divSet_zero hc, ← Set.image_univ, hinj.encard_image, Set.encard_univ, ENat.card_eq_coe_natCard,
    Nat.card_units]

theorem encard_divSet (hc : IsConstantField Fq k) {E : Divisor Fq k} {ξ₀ : kˣ} (h₀ : Divisor.div ξ₀ = E) :
    (divSet (Fq := Fq) (k := k) E).encard = (Nat.card Fq - 1 : ℕ) := by
  have : divSet (Fq := Fq) (k := k) E = (fun c => ξ₀ * c) '' divSet (Fq := Fq) (k := k) 0 := by
    ext ξ
    simp only [divSet, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h
      refine ⟨ξ₀⁻¹ * ξ, ?_, by group⟩
      rw [Divisor.div_mul, h, Divisor.div_inv', h₀, neg_add_cancel]
    · rintro ⟨c, hc0, rfl⟩
      rw [Divisor.div_mul, hc0, add_zero, h₀]
  rw [this, (mul_right_injective ξ₀).encard_image, encard_divSet_zero hc]

theorem div_inv' (z : FFIdeleGroup Fq k) : div z⁻¹ = -div z := by
  have := div_mul z z⁻¹
  rw [mul_inv_cancel, div_one] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

/-- The fibre $\{z : \operatorname{div}z=D\}$. -/
def fib (D : Divisor Fq k) : Set (FFIdeleGroup Fq k) := {z | div z = D}

theorem mk_mem_image_fib_iff (D : Divisor Fq k) (z : FFIdeleGroup Fq k) :
    (QuotientGroup.mk z : FFIdeleClassGroup Fq k) ∈ QuotientGroup.mk '' fib D ↔
      (divSet (Fq := Fq) (k := k) (D - div z)).Nonempty := by
  constructor
  · rintro ⟨w, hw, hwz⟩
    rw [QuotientGroup.eq] at hwz
    obtain ⟨ξ, hξ⟩ := hwz
    refine ⟨ξ⁻¹, ?_⟩
    have h1 : div (principal ξ) = div z - D := by
      rw [hξ, div_mul, div_inv', (show div w = D from hw)]; abel
    show Divisor.div ξ⁻¹ = D - div z
    rw [div_principal] at h1
    rw [Divisor.div_inv', h1]; abel
  · rintro ⟨ξ, hξ⟩
    refine ⟨principal ξ * z, ?_, ?_⟩
    · show div (principal ξ * z) = D
      rw [div_mul, div_principal, (show Divisor.div ξ = D - div z from hξ), sub_add_cancel]
    · rw [QuotientGroup.eq]
      exact ⟨ξ⁻¹, by rw [map_inv, mul_inv_rev, mul_comm z⁻¹, inv_mul_cancel_right]⟩

theorem tsum_indicator_fib (hc : IsConstantField Fq k) (D : Divisor Fq k) (z : FFIdeleGroup Fq k) :
    ∑' ξ : kˣ, (fib D).indicator (1 : FFIdeleGroup Fq k → ℝ≥0∞) (principal ξ * z) =
      ((Nat.card Fq - 1 : ℕ) : ℝ≥0∞) *
        (QuotientGroup.mk '' fib D).indicator (1 : FFIdeleClassGroup Fq k → ℝ≥0∞) (QuotientGroup.mk z) := by
  have hpt : ∀ ξ : kˣ, (fib D).indicator (1 : FFIdeleGroup Fq k → ℝ≥0∞) (principal ξ * z) =
      (divSet (D - div z)).indicator 1 ξ := by
    intro ξ
    simp only [Set.indicator_apply, fib, divSet, Set.mem_setOf_eq, div_mul, div_principal]
    congr 1
    exact propext ⟨fun h => by rw [← h]; abel, fun h => by rw [h]; abel⟩
  simp_rw [hpt]
  rw [← tsum_subtype]
  simp only [Pi.one_apply]
  rw [ENNReal.tsum_set_one]
  by_cases h : (divSet (Fq := Fq) (k := k) (D - div z)).Nonempty
  · obtain ⟨ξ₀, h₀⟩ := h
    rw [encard_divSet hc h₀, Set.indicator_of_mem ((mk_mem_image_fib_iff D z).2 ⟨ξ₀, h₀⟩), Pi.one_apply,
      mul_one]
    rfl
  · rw [Set.not_nonempty_iff_eq_empty.1 h, Set.encard_empty,
      Set.indicator_of_notMem (fun h' => h ((mk_mem_image_fib_iff D z).1 h')), mul_zero]
    simp

theorem measurableSet_image_fib (D : Divisor Fq k) :
    MeasurableSet (QuotientGroup.mk '' fib D : Set (FFIdeleClassGroup Fq k)) := by
  show MeasurableSet ((QuotientGroup.mk : FFIdeleGroup Fq k → FFIdeleClassGroup Fq k) ⁻¹'
    (QuotientGroup.mk '' fib D))
  have : (QuotientGroup.mk : FFIdeleGroup Fq k → FFIdeleClassGroup Fq k) ⁻¹' (QuotientGroup.mk '' fib D) =
      ⋃ E ∈ {E : Divisor Fq k | (divSet (Fq := Fq) (k := k) (D - E)).Nonempty}, {z | div z = E} := by
    ext z
    simp only [Set.mem_preimage, mk_mem_image_fib_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨fun h => ⟨div z, h, rfl⟩, fun ⟨E, hE, hz⟩ => hz ▸ hE⟩
  rw [this]
  exact (isOpen_biUnion fun E _ => isOpen_fiber E).measurableSet

/-- **The image of a fibre of the divisor map has measure $\mu(\prod_v\mathfrak r_v^\times)/(q-1)$.** -/
theorem quotient_measure_image_fib (hc : IsConstantField Fq k) (μ : Measure (FFIdeleGroup Fq k))
    [μ.IsHaarMeasure] (ν : Measure (FFIdeleClassGroup Fq k)) (hν : IsQuotientMeasure μ ν) (D : Divisor Fq k) :
    ((Nat.card Fq - 1 : ℕ) : ℝ≥0∞) * ν (QuotientGroup.mk '' fib D) = μ integralUnits := by
  have h := hν ((fib D).indicator 1) (measurable_one.indicator (measurableSet_fiber D))
    (fun x => ((Nat.card Fq - 1 : ℕ) : ℝ≥0∞) * (QuotientGroup.mk '' fib D).indicator 1 x)
    (fun z => (tsum_indicator_fib hc D z).symm)
  rw [lintegral_indicator_one (show MeasurableSet (fib D) from measurableSet_fiber D), lintegral_const_mul _
    (measurable_one.indicator (measurableSet_image_fib D)), lintegral_indicator_one (measurableSet_image_fib D)]
    at h
  rw [← h]
  exact measure_fiber μ D

/-- A representative of degree $0$ of a class in $D_0/P$. -/
def classRep (C : ClassGroup0 Fq k) : Divisor Fq k := ((Quotient.out C : (Divisor.deg (Fq := Fq) (k := k)).ker) : _)

theorem deg_classRep (C : ClassGroup0 Fq k) : Divisor.deg (classRep C) = 0 :=
  AddMonoidHom.mem_ker.1 (Quotient.out C).2

theorem classRep_spec {C : ClassGroup0 Fq k} {a : Divisor Fq k} (ha : Divisor.deg a = 0) :
    (QuotientAddGroup.mk ⟨a, ha⟩ : ClassGroup0 Fq k) = C ↔ a - classRep C ∈ principalDivisors Fq k := by
  conv_lhs => rw [← QuotientAddGroup.out_eq' C]
  rw [eq_comm, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, classRep]
  rw [neg_add_eq_sub]

/-- $G_k^1$ is the union of the images of the fibres over the representatives of $D_0/P$. -/
theorem classNormOne_eq_iUnion :
    classNormOne Fq k = ⋃ C : ClassGroup0 Fq k, QuotientGroup.mk '' fib (classRep C) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz0 : Divisor.deg (div z) = 0 := (mem_normOne_iff z).1 hz
    set C : ClassGroup0 Fq k := QuotientAddGroup.mk ⟨div z, hz0⟩
    have h := (classRep_spec (C := C) hz0).1 rfl
    obtain ⟨ξ, hξ⟩ := (mem_principalDivisors_iff _).1 h
    refine Set.mem_iUnion.2 ⟨C, (mk_mem_image_fib_iff _ z).2 ⟨ξ⁻¹, ?_⟩⟩
    show Divisor.div ξ⁻¹ = classRep C - div z
    rw [Divisor.div_inv', hξ]; abel
  · intro hx
    obtain ⟨C, w, hw, rfl⟩ := Set.mem_iUnion.1 hx
    refine ⟨w, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_normOne_iff, show div w = classRep C from hw, deg_classRep]

theorem pairwise_disjoint_image_fib :
    Pairwise (Function.onFun Disjoint fun C : ClassGroup0 Fq k =>
      (QuotientGroup.mk '' fib (classRep C) : Set (FFIdeleClassGroup Fq k))) := by
  intro C C' hCC'
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', hww'⟩
  apply hCC'
  rw [QuotientGroup.eq] at hww'
  obtain ⟨ξ, hξ⟩ := hww'
  have hd : classRep C - classRep C' = Divisor.div ξ := by
    rw [← div_principal (Fq := Fq), hξ, div_mul, div_inv', (show div w = classRep C from hw),
      (show div w' = classRep C' from hw')]; abel
  have h1 : classRep C - classRep C' ∈ principalDivisors Fq k := (mem_principalDivisors_iff _).2 ⟨ξ, hd.symm⟩
  have e1 := (classRep_spec (C := C) (deg_classRep C)).2 (by rw [sub_self]; exact zero_mem _)
  have e2 := (classRep_spec (C := C') (deg_classRep C)).2 h1
  exact e1.symm.trans e2

/-- **Weil's normalization in terms of $\mu$**: for every Haar measure $\mu$ on $k_{\mathbb A}^\times$ and its image
$\nu$ on $G_k$, $(q-1)\,\nu(G_k^1)=h\,\mu(\prod_v\mathfrak r_v^\times)$. -/
@[kb "weil1973bnt" "Ch. VII, §5, p. 120 (the Haar measure on the ideles with μ_1(G_k^1) = 1), function fields: ν(G_k^1) = h μ(∏ r_v^×)/(q - 1)"]
theorem measure_normOne_quotient (hc : IsConstantField Fq k) (μ : Measure (FFIdeleGroup Fq k))
    [μ.IsHaarMeasure] (ν : Measure (FFIdeleClassGroup Fq k)) (hν : IsQuotientMeasure μ ν) :
    ((Nat.card Fq - 1 : ℕ) : ℝ≥0∞) * ν (classNormOne Fq k) =
      (Nat.card (ClassGroup0 Fq k) : ℝ≥0∞) * μ integralUnits := by
  have := finite_classGroup0 (Fq := Fq) (k := k)
  have : Fintype (ClassGroup0 Fq k) := Fintype.ofFinite _
  rw [classNormOne_eq_iUnion, measure_iUnion pairwise_disjoint_image_fib
    (fun C => measurableSet_image_fib _), tsum_fintype, Finset.mul_sum]
  simp_rw [quotient_measure_image_fib hc μ ν hν]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card]

/-- **The constant $c_\mu$ of VII.§5 Thm. 2 is $\nu(G_k^1)$.** -/
theorem zetaConst_eq_quotient (hc : IsConstantField Fq k) (μ : Measure (FFIdeleGroup Fq k))
    [μ.IsHaarMeasure] (ν : Measure (FFIdeleClassGroup Fq k)) (hν : IsQuotientMeasure μ ν) :
    zetaConst μ = ((ν (classNormOne Fq k)).toReal : ℂ) := by
  have h := measure_normOne_quotient hc μ ν hν
  have hq2 : 2 ≤ Nat.card Fq := Finite.one_lt_card
  have hq1 : ((Nat.card Fq - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    rw [Nat.cast_ne_zero]; omega
  have hν' : ν (classNormOne Fq k) =
      (Nat.card (ClassGroup0 Fq k) : ℝ≥0∞) * μ integralUnits / ((Nat.card Fq - 1 : ℕ) : ℝ≥0∞) := by
    rw [← h, mul_comm, ENNReal.mul_div_cancel_right hq1 ENNReal.coe_ne_top]
  rw [hν', ENNReal.toReal_div, ENNReal.toReal_mul, zetaConst]
  simp only [ENNReal.toReal_natCast, Measure.real]
  push_cast [Nat.cast_sub (show 1 ≤ Nat.card Fq by omega)]
  ring

/-- **Weil VII.§5 Cor. 7, with Weil's normalization stated through the quotient.** For a Haar measure $\mu$ on
$k_{\mathbb A}^\times$ whose image $\nu$ on $G_k$ gives $G_k^1$ the measure $1$ (Weil VII.§5, p. 120), and a
Schwartz–Bruhat $\Phi$, the continuation of $Z(\omega_s,\Phi)$ satisfies: $Z(\omega_s,\Phi)+\Phi(0)(1-q^{-s})^{-1}$ is
holomorphic at $s=0$. -/
@[kb "weil1973bnt" "Ch. VII, §5, Cor. 7 (p. 127), with Weil's normalization μ_1(G_k^1) = 1 of p. 120"]
theorem weil_VII_5_cor7_quotient (hc : IsConstantField Fq k) (μ : Measure (FFIdeleGroup Fq k))
    [μ.IsHaarMeasure] (ν : Measure (FFIdeleClassGroup Fq k)) (hν : IsQuotientMeasure μ ν)
    (h1 : ν (classNormOne Fq k) = 1) {Φ : FFAdeleRing Fq k → ℂ} (hΦ : FFAdeleRing.IsSchwartzBruhat Φ) :
    ∃ Zc : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re → zetaIntegral μ Φ s = Zc s) ∧
      MeromorphicOn Zc Set.univ ∧
      AnalyticAt ℂ (fun s => Zc s + Φ 0 * (1 - (Nat.card Fq : ℂ) ^ (-s))⁻¹) 0 := by
  obtain ⟨Zc, h1', h2, -, h4⟩ := weil_VII_5_thm2_ff hc μ hΦ
  refine ⟨Zc, fun s hs => (h1' s hs).2, h2, ?_⟩
  rw [zetaConst_eq_quotient hc μ ν hν, h1, ENNReal.toReal_one, Complex.ofReal_one, one_mul] at h4
  exact h4

end FFIdeleGroup

end

end NumberFieldKB.WeilBNT.FF
