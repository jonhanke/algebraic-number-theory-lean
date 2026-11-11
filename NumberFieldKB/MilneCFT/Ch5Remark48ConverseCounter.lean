import NumberFieldKB.MilneCFT.Ch5Remark48Corrected
import NumberFieldKB.HeckeCharacter.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Complex.Circle
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Milne, *Class Field Theory*, Chapter V, Remark 4.8: the second sentence fails for characters of infinite type

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter V, Remark 4.8, p. 174.

The second sentence of Remark 4.8 (`Remark4_8Converse`, the `converse` field of the named statement `Remark4_8`) says
that for $G$ complete with no small subgroups, every continuous $\varphi : \mathbb I_K \to G$ trivial on $K^\times$
arises from an admissible $\psi : I^S \to G$, where admissible is defined by moduli: for every neighbourhood $N$ of $1$
there is $\mathfrak m$ with $\psi(i(K_{\mathfrak m,1})) \subseteq N$.

Counterexample (`not_remark4_8_converse_rat`): $K = \mathbb Q$, $G$ the circle group (complete, no small subgroups:
`circle_noSmallSubgroups`), $\varphi = \|\cdot\|^{i}$ (the idèle norm to the power $i$; continuous, trivial on
$\mathbb Q^\times$ by the product formula). If $\psi : I^S \to G$ matched $\varphi$ on the idèles equal to $1$ at $S$
and at $\infty$, then $\psi((a)) = a^{-i} = e^{-i\log a}$ for every positive integer $a$ prime to $S$. Every
$K_{\mathfrak m,1}$ with $\mathfrak m$ supported on $S$ contains all positive integers $a \equiv 1 \bmod M$ for some
$M$ divisible by the primes of $S$, and $\log a$ for such $a$ meets every interval $[\pi/2 + 2\pi n, 3\pi/2 + 2\pi n]$
for $n$ large, where $\mathrm{Re}\,e^{-i\log a} \le 0$. So $\psi$ is not admissible (take $N = \{\mathrm{Re}\,z > 0\}$).
The corrected statement (`Remark4_8Corrected`) adds the hypothesis that $\varphi$ is trivial on the identity component
of $K_\infty^\times$, which $\|\cdot\|^{i}$ is not.
-/

open NumberField IsDedekindDomain Topology
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

open NumberFieldKB.Ideles

theorem ideleGroupNorm_ne_zero' (x : IdeleGroup (𝓞 ℚ) ℚ) : (ideleGroupNorm ℚ x : ℝ) ≠ 0 :=
  NNReal.coe_ne_zero.mpr ((Group.isUnit x).map (ideleGroupNorm ℚ)).ne_zero

/-- `φ x = ‖x‖^i`. -/
def phiCircle : IdeleGroup (𝓞 ℚ) ℚ →* Circle where
  toFun x := Circle.exp (Real.log (ideleGroupNorm ℚ x))
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, NNReal.coe_mul, Real.log_mul (ideleGroupNorm_ne_zero' x) (ideleGroupNorm_ne_zero' y),
      Circle.exp_add]

theorem phiCircle_apply (x : IdeleGroup (𝓞 ℚ) ℚ) :
    phiCircle x = Circle.exp (Real.log (ideleGroupNorm ℚ x)) := rfl

theorem continuous_phiCircle : Continuous phiCircle :=
  Circle.exp.continuous.comp ((NNReal.continuous_coe.comp continuous_ideleGroupNorm).log
    ideleGroupNorm_ne_zero')

theorem phiCircle_unit (a : ℚˣ) : phiCircle (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) = 1 := by
  rw [phiCircle_apply, ideleGroupNorm_unitEmbedding]; simp

theorem norm_one_finiteAdele : ‖(1 : FiniteAdeleRing (𝓞 ℚ) ℚ)‖ = 1 := by
  rw [FiniteAdeleRing.norm_eq_finprod_of_isUnit isUnit_one]
  have h : ∀ v : HeightOneSpectrum (𝓞 ℚ), ‖(1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v‖ = 1 := fun v => by
    change ‖(1 : v.adicCompletion ℚ)‖ = 1
    exact norm_one
  simp only [h, finprod_one]

theorem norm_infPart_unit (a : ℚˣ) :
    (ideleGroupNorm ℚ (infPart (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a)) : ℝ) = |((a : ℚ) : ℝ)| := by
  rw [coe_ideleGroupNorm, AdeleRing.norm_def]
  have h1 : ((infPart (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 :=
    rfl
  have h2 : ((infPart (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).1 =
      algebraMap ℚ (InfiniteAdeleRing ℚ) (a : ℚ) := rfl
  rw [h1, h2, norm_one_finiteAdele, mul_one, InfiniteAdeleRing.coe_norm_eq_abs_norm]
  simp

theorem norm_localPart_unit (a : ℚˣ) (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hT : ∀ v ∈ T, Valued.v (ideleFinAt (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) v) = 1) :
    (ideleGroupNorm ℚ (localPart (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) T) : ℝ) = 1 := by
  classical
  rw [coe_ideleGroupNorm, AdeleRing.norm_def]
  have h1 : ((localPart (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) T : IdeleGroup (𝓞 ℚ) ℚ) :
      AdeleRing (𝓞 ℚ) ℚ).1 = 1 := rfl
  have hu : IsUnit (((localPart (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) T : IdeleGroup (𝓞 ℚ) ℚ) :
      AdeleRing (𝓞 ℚ) ℚ).2) := (Prod.isUnit_iff.1 (Units.isUnit _)).2
  rw [h1, FiniteAdeleRing.norm_eq_finprod_of_isUnit hu, InfiniteAdeleRing.norm_def]
  have h3 : ∀ v, ‖(((localPart (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) T : IdeleGroup (𝓞 ℚ) ℚ) :
      AdeleRing (𝓞 ℚ) ℚ).2) v‖ = 1 := by
    intro v
    change ‖(finRestrict (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (a : ℚ)) T) v‖ = 1
    rw [finRestrict_apply]
    split_ifs with hv
    · exact Valued.toNormedField.norm_eq_one_iff.2 (hT v hv)
    · exact norm_one
  have h4 : ∀ w : InfinitePlace ℚ, ‖(1 : InfiniteAdeleRing ℚ) w‖ = 1 := fun w => by
    change ‖(1 : w.Completion)‖ = 1
    exact norm_one
  simp [h3, h4]

theorem norm_xa (a : ℚˣ) (ha : 0 < (a : ℚ)) (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hT : ∀ v ∈ T, Valued.v (ideleFinAt (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) v) = 1) :
    (ideleGroupNorm ℚ (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a *
      (infPart (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) * localPart (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) T)⁻¹) : ℝ)
      = ((a : ℚ) : ℝ)⁻¹ := by
  rw [map_mul, map_inv, map_mul, ideleGroupNorm_unitEmbedding, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_mul,
    NNReal.coe_one, norm_infPart_unit, norm_localPart_unit a T hT, abs_of_pos (by exact_mod_cast ha)]
  simp

/-- Among the integers `≡ 1 mod M` there is one with `cos (log a) ≤ 0`. -/
theorem exists_cos_log_nonpos (M : ℕ) (hM : 0 < M) :
    ∃ j : ℕ, Real.cos (Real.log (((1 + M * j : ℕ) : ℕ) : ℝ)) ≤ 0 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  set L : ℝ := Real.exp (Real.pi / 2 + 2 * Real.pi * M) with hL
  have hMle : (M : ℝ) + 1 ≤ L := by
    have h1 := Real.add_one_le_exp (Real.pi / 2 + 2 * Real.pi * M)
    have h2 : (M : ℝ) ≤ Real.pi / 2 + 2 * Real.pi * M := by nlinarith [Real.pi_gt_three]
    linarith
  have hL1 : 1 ≤ L := by linarith
  set j : ℕ := ⌈(L - 1) / M⌉₊ with hj
  have hj1 : (L - 1) / M ≤ j := Nat.le_ceil _
  have hj2 : (j : ℝ) < (L - 1) / M + 1 := Nat.ceil_lt_add_one (div_nonneg (by linarith) hMr.le)
  have ha1 : L ≤ ((1 + M * j : ℕ) : ℝ) := by
    push_cast
    have := (div_le_iff₀ hMr).1 hj1
    linarith
  have ha2 : ((1 + M * j : ℕ) : ℝ) ≤ L + M := by
    push_cast
    have := (lt_div_iff₀ hMr).1 (show (j : ℝ) - 1 < (L - 1) / M by
      have := hj2; linarith)
    nlinarith
  have hR : L + M ≤ Real.exp (3 * Real.pi / 2 + 2 * Real.pi * M) := by
    have : Real.exp (3 * Real.pi / 2 + 2 * Real.pi * M) = L * Real.exp Real.pi := by
      rw [hL, ← Real.exp_add]; congr 1; ring
    rw [this]
    have h3 := Real.add_one_le_exp Real.pi
    nlinarith [Real.pi_gt_three, Real.exp_pos (Real.pi / 2 + 2 * Real.pi * M)]
  refine ⟨j, ?_⟩
  have hLpos : 0 < L := by linarith
  have hlog1 : Real.pi / 2 + 2 * Real.pi * M ≤ Real.log (((1 + M * j : ℕ) : ℕ) : ℝ) := by
    rw [← Real.log_exp (Real.pi / 2 + 2 * Real.pi * M)]
    exact Real.log_le_log hLpos ha1
  have hlog2 : Real.log (((1 + M * j : ℕ) : ℕ) : ℝ) ≤ 3 * Real.pi / 2 + 2 * Real.pi * M := by
    rw [← Real.log_exp (3 * Real.pi / 2 + 2 * Real.pi * M)]
    exact Real.log_le_log (by linarith) (ha2.trans hR)
  have : Real.cos (Real.log (((1 + M * j : ℕ) : ℕ) : ℝ)) =
      Real.cos (Real.log (((1 + M * j : ℕ) : ℕ) : ℝ) - M * (2 * Real.pi)) :=
    (Real.cos_sub_nat_mul_two_pi _ _).symm
  rw [this]
  apply Real.cos_nonpos_of_pi_div_two_le_of_le <;> nlinarith

theorem val_nat_le (v : HeightOneSpectrum (𝓞 ℚ)) (e k : ℕ) (hk : Ideal.absNorm (v.asIdeal ^ e) ∣ k) :
    v.valuation ℚ (k : ℚ) ≤ WithZero.exp (-(e : ℤ)) := by
  obtain ⟨t, rfl⟩ := hk
  have hmem : ((Ideal.absNorm (v.asIdeal ^ e) * t : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ^ e := by
    push_cast
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have h1 := (v.intValuation_le_pow_iff_mem _ e).2 hmem
  have h2 := v.valuation_of_algebraMap (K := ℚ) (((Ideal.absNorm (v.asIdeal ^ e) * t : ℕ) : 𝓞 ℚ))
  have h4 : v.valuation ℚ (((Ideal.absNorm (v.asIdeal ^ e) * t : ℕ)) : ℚ) =
      v.intValuation (((Ideal.absNorm (v.asIdeal ^ e) * t : ℕ)) : 𝓞 ℚ) := by
    rw [← h2]; congr 1
  rw [h4]
  exact h1

/-- `Remark4_8Converse K` is the `converse` field of the named statement `Remark4_8 K` (the second sentence of the
remark as printed). -/
theorem remark4_8Converse_of_remark4_8 {K : Type} [Field K] [NumberField K] (h : Remark4_8 K) :
    Remark4_8Converse K :=
  fun G _ _ _ _ => h.converse G

/-- **Remark 4.8, second sentence, as printed, is false** (Milne, *CFT*, V, Remark 4.8, p. 174): for $K = \mathbb Q$,
$G$ the circle and $\varphi = \|\cdot\|^{i}$ there is no admissible $\psi$ (admissibility by moduli). -/
@[kb "milne2020cft" "Ch. V, Remark 4.8 (counterexample to the second sentence as printed)"]
theorem not_remark4_8_converse_rat : ¬ Remark4_8Converse ℚ := by
  classical
  intro H
  obtain ⟨S, hS, ψ, hadm, hψ⟩ := H Circle circle_noSmallSubgroups phiCircle continuous_phiCircle phiCircle_unit
  have hN : {z : Circle | 0 < (z : ℂ).re} ∈ 𝓝 (1 : Circle) := by
    refine IsOpen.mem_nhds ?_ (by simp)
    exact isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
  obtain ⟨m, hmS, hm⟩ := hadm _ hN
  set T : Finset (HeightOneSpectrum (𝓞 ℚ)) := hS.toFinset with hT
  have hTS : (↑T : Set (HeightOneSpectrum (𝓞 ℚ))) = S := hS.coe_toFinset
  set M : ℕ := ∏ v ∈ T, Ideal.absNorm (v.asIdeal ^ (m.ord v + 1)) with hM
  have hMpos : 0 < M := by
    refine Finset.prod_pos fun v _ => Nat.pos_of_ne_zero fun h => ?_
    rw [Ideal.absNorm_eq_zero_iff] at h
    exact pow_ne_zero _ v.ne_bot h
  obtain ⟨j, hj⟩ := exists_cos_log_nonpos M hMpos
  set n : ℕ := 1 + M * j with hn
  have hn0 : (n : ℚ) ≠ 0 := by
    have : 0 < n := by omega
    exact_mod_cast this.ne'
  set a : ℚˣ := Units.mk0 (n : ℚ) hn0 with ha
  have haq : (a : ℚ) = (n : ℚ) := rfl
  have hapos : 0 < (a : ℚ) := by
    rw [haq]; have : 0 < n := by omega
    exact_mod_cast this
  -- congruence at primes of `T`
  have hcong : ∀ v ∈ T, v.valuation ℚ ((a : ℚ) - 1) ≤ WithZero.exp (-((m.ord v + 1 : ℕ) : ℤ)) := by
    intro v hv
    have : (a : ℚ) - 1 = ((M * j : ℕ) : ℚ) := by rw [haq, hn]; push_cast; ring
    rw [this]
    refine val_nat_le v (m.ord v + 1) _ ?_
    exact (Finset.dvd_prod_of_mem (fun v => Ideal.absNorm (v.asIdeal ^ (m.ord v + 1))) hv).trans
      (dvd_mul_right _ _)
  have hlt : ∀ v : HeightOneSpectrum (𝓞 ℚ), WithZero.exp (-((m.ord v + 1 : ℕ) : ℤ)) <
      (1 : WithZero (Multiplicative ℤ)) := by
    intro v
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hunit : ∀ v ∈ T, Valued.v (ideleFinAt (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) v) = 1 := by
    intro v hv
    refine val_eq_one_of_sub_one_le Valued.v (hlt v) ?_
    rw [ideleFinAt_unitEmbedding_sub_one]
    exact hcong v hv
  have hmemC : a ∈ congruenceSubgroup m := by
    refine ⟨fun w hw => ?_, fun v hv => ?_⟩
    · unfold IsPositiveAt
      have : (a : ℚ) = ((n : ℕ) : ℚ) := rfl
      rw [this, map_natCast]
      have : 0 < n := by omega
      exact_mod_cast this
    · have hvT : v ∈ T := by
        rw [← hTS] at hmS
        exact hmS (show v ∈ m.finiteSupport from hv)
      refine (hcong v hvT).trans ?_
      rw [WithZero.exp_le_exp]; omega
  have hS' : toPrincipalIdeal (𝓞 ℚ) ℚ a ∈ sIdeals S := by
    rw [← ideleToIdeal_unitEmbedding, ideleToIdeal_mem_sIdeals_iff]
    intro v hv
    exact hunit v (by rw [← hTS] at hv; exact hv)
  have hxmem := splitTriv_mem (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) T S hTS.ge
  have hid : ideleToIdeal ℚ ((IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) *
      (infPart (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) * localPart (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) T)⁻¹) =
      toPrincipalIdeal (𝓞 ℚ) ℚ a := by
    rw [ideleToIdeal_splitTriv _ T hunit, ideleToIdeal_unitEmbedding]
  have h1 := hψ _ hxmem ⟨_, hS'⟩ hid.symm
  have h2 := hm a hmemC hS'
  have h3 : (ψ ⟨_, hS'⟩ : Circle) = phiCircle _ := h1.symm
  rw [h3, phiCircle_apply, norm_xa a hapos T hunit] at h2
  have h4 : ((Circle.exp (Real.log (((a : ℚ) : ℝ)⁻¹)) : Circle) : ℂ).re = Real.cos (Real.log (n : ℝ)) := by
    rw [Real.log_inv, Circle.coe_exp]
    have : ((a : ℚ) : ℝ) = (n : ℝ) := by rw [haq]; push_cast; rfl
    rw [this, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have h5 : (0 : ℝ) < Real.cos (Real.log (n : ℝ)) := by
    rw [← h4]; exact h2
  exact absurd hj (not_le.2 h5)

end NumberFieldKB.MilneCFT
