import NumberFieldKB.MilneCFT.Ch6.Splitting
import NumberFieldKB.MilneCFT.Ch6.Density
import NumberFieldKB.HeckeL.DedekindCont
import NumberFieldKB.MilneCFT.Ch6.PolarAux
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real

/-!
# Milne, *Class Field Theory*, Chapter VI §§3–4: polar densities

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9). These items are numbered in the book but missing from the
audit's item list (rows added).

* **Proposition 3.1 (a)** (`prop_3_1a`): the set of all primes of $K$ has polar density $1$ ($\zeta_K$ has a simple
  pole at $1$).
* **Theorem 3.4, Galois case** (`thm_3_4_galois`): the primes of $K$ splitting completely in a finite Galois extension
  $L$ have polar density $1/[L:K]$.
* **Proposition 4.1 (a)** (`prop_4_1a`): a polar density is a Dirichlet density (Milne's form).
* **Example 3.7, polar form** (`example_3_7_polar`).
-/

open Filter Topology NumberField IsDedekindDomain Polynomial
open NumberFieldKB.Chebotarev

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch6

variable {K : Type} [Field K] [NumberField K]

/-- **Proposition 3.1 (a)** (Milne, *CFT*, Chapter VI, p. 192): the set of all prime ideals of $K$ has polar
density $1$. -/
@[kb "milne2020cft" "Ch. VI, Prop. 3.1 (a)"]
theorem prop_3_1a : HasPolarDensity (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 1 := by
  obtain ⟨g, hg, hg1, hev⟩ := zeta_polar_data (E := K)
  refine ⟨1, 1, one_pos, by simp, g, hg, hg1, ?_⟩
  filter_upwards [hev] with s hs
  rw [pow_one, hs, zpow_one]

/-- **Theorem 3.4, Galois case** (Milne, *CFT*, Chapter VI, p. 192): for a finite Galois extension $L$ of $K$, the
set of prime ideals of $K$ that split completely in $L$ has polar density $1/[L:K]$. -/
@[kb "milne2020cft" "Ch. VI, Thm. 3.4 (L Galois over K)"]
theorem thm_3_4_galois (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    HasPolarDensity (splitPrimes K L) (1 / Module.finrank K L) := by
  obtain ⟨gL, hgL, hgL1, hev⟩ := zeta_polar_data (E := L)
  have hU : IsOpen {s : ℂ | 3 / 4 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hH1 : (1 : ℂ) ∈ {s : ℂ | 3 / 4 < s.re} := by simp; norm_num
  have hHan : AnalyticAt ℂ (primeZetaProduct (splitAbove K L)ᶜ) 1 :=
    (differentiableOn_primeZetaProduct_compl (K := K) (L := L)).analyticAt (hU.mem_nhds hH1)
  have hH0 : primeZetaProduct (splitAbove K L)ᶜ 1 ≠ 0 :=
    primeZetaProduct_compl_ne_zero (K := K) (L := L) (by simp; norm_num)
  refine ⟨Module.finrank K L, 1, Module.finrank_pos, by simp,
    fun s => gL s / primeZetaProduct (splitAbove K L)ᶜ s, hgL.div hHan hH0, div_ne_zero hgL1 hH0, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hs'
  have hs1 : 1 < s.re := hs'
  have hsU : 3 / 4 < s.re := by linarith
  have hH := primeZetaProduct_compl_ne_zero (K := K) (L := L) hsU
  have h1 := primeZetaProduct_univ_eq_mul_compl hs1 (splitAbove K L)
  rw [hs, primeZetaProduct_splitAbove hs1] at h1
  have hsub : s - 1 ≠ 0 := by
    intro h; have : s = 1 := by linear_combination h
    rw [this] at hs1; simp at hs1
  rw [zpow_one]
  calc primeZetaProduct (splitPrimes K L) s ^ Module.finrank K L
      = (primeZetaProduct (splitPrimes K L) s ^ Module.finrank K L *
          primeZetaProduct (splitAbove K L)ᶜ s) / primeZetaProduct (splitAbove K L)ᶜ s := by
        field_simp
    _ = _ := by rw [← h1]; ring

section Real41

open Asymptotics QuadFormsKB.NFEuler

/-- Helper: the real Euler product $\prod_{\mathfrak p\in T}(1-N\mathfrak p^{-s})^{-1}$. -/
def realZeta (T : Set (HeightOneSpectrum (𝓞 K))) (s : ℝ) : ℝ :=
  ∏' p : T, (1 - ((normP p.1 : ℕ) : ℝ) ^ (-s))⁻¹

/-- Helper: $\sum_{\mathfrak p} N\mathfrak p^{-2}$ over $T$ (as inverse squares) converges. -/
theorem summable_inv_sq (T : Set (HeightOneSpectrum (𝓞 K))) :
    Summable fun p : T => (((normP p.1 : ℕ) : ℝ)⁻¹) ^ 2 := by
  have h2 := (summable_normP_rpow (F := K) (σ := 2) (by norm_num)).comp_injective
    (Subtype.val_injective (p := fun x => x ∈ T))
  refine h2.congr fun p => ?_
  have hp : (0 : ℝ) ≤ ((normP p.1 : ℕ) : ℝ) := Nat.cast_nonneg _
  simp only [Function.comp_apply]
  rw [Real.rpow_neg hp, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]

/-- Helper: constant bounding $\log\zeta_{K,T}(s)-\sum_T N\mathfrak p^{-s}$. -/
def boundC (T : Set (HeightOneSpectrum (𝓞 K))) : ℝ :=
  ∑' p : T, 2 * (((normP p.1 : ℕ) : ℝ)⁻¹) ^ 2

theorem hasProd_real (T : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : T => (1 - ((normP p.1 : ℕ) : ℝ) ^ (-s))⁻¹)
      (Real.exp (∑' p : T, Real.log (1 - ((normP p.1 : ℕ) : ℝ) ^ (-s))⁻¹)) := by
  have hx0 : ∀ p : T, 0 ≤ ((normP p.1 : ℕ) : ℝ) ^ (-s) := fun p =>
    Real.rpow_nonneg (by linarith [normP_real_ge p.1]) _
  have hxh : ∀ p : T, ((normP p.1 : ℕ) : ℝ) ^ (-s) ≤ 1 / 2 := fun p => rpow_neg_normP_le_half p.1 hs.le
  have hsx : Summable fun p : T => ((normP p.1 : ℕ) : ℝ) ^ (-s) :=
    (summable_normP_rpow (F := K) hs).comp_injective (Subtype.val_injective (p := fun x => x ∈ T))
  have hb := fun p : T => log_inv_one_sub_bounds (hx0 p) (hxh p)
  have hg0 : ∀ p : T, 0 ≤ Real.log (1 - ((normP p.1 : ℕ) : ℝ) ^ (-s))⁻¹ := fun p => (hx0 p).trans (hb p).1
  have hg2 : ∀ p : T, Real.log (1 - ((normP p.1 : ℕ) : ℝ) ^ (-s))⁻¹ ≤ 2 * ((normP p.1 : ℕ) : ℝ) ^ (-s) :=
    fun p => by
      have := (hb p).2
      nlinarith [hx0 p, hxh p]
  have hgs := Summable.of_nonneg_of_le hg0 hg2 (hsx.mul_left 2)
  have e : (fun p : T => (1 - ((normP p.1 : ℕ) : ℝ) ^ (-s))⁻¹) =
      Real.exp ∘ fun p : T => Real.log (1 - ((normP p.1 : ℕ) : ℝ) ^ (-s))⁻¹ := by
    funext p
    simp only [Function.comp_apply]
    refine (Real.exp_log (inv_pos.mpr ?_)).symm
    linarith [hxh p]
  rw [e]
  exact hgs.hasSum.rexp

theorem primeZetaProduct_ofReal (T : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    primeZetaProduct T (s : ℂ) = ((realZeta T s : ℝ) : ℂ) := by
  have h := (hasProd_real T hs).map Complex.ofRealHom Complex.continuous_ofReal
  rw [primeZetaProduct, realZeta, (hasProd_real T hs).tprod_eq]
  refine HasProd.tprod_eq ?_
  have e : (fun p : T => (1 - (Ideal.absNorm p.1.asIdeal : ℂ) ^ (-(s : ℂ)))⁻¹) =
      Complex.ofRealHom ∘ fun p : T => (1 - ((normP p.1 : ℕ) : ℝ) ^ (-s))⁻¹ := by
    funext p
    simp only [Function.comp_apply, Complex.ofRealHom_eq_coe]
    rw [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.ofReal_natCast]
  rw [e]
  exact h

theorem realZeta_pos (T : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) : 0 < realZeta T s := by
  rw [realZeta, (hasProd_real T hs).tprod_eq]
  exact Real.exp_pos _

theorem logZeta_sub_sum_bounds (T : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    0 ≤ Real.log (realZeta T s) - T.primeIdealZetaSum s ∧
      Real.log (realZeta T s) - T.primeIdealZetaSum s ≤ boundC T := by
  have hx0 : ∀ p : T, 0 ≤ ((normP p.1 : ℕ) : ℝ) ^ (-s) := fun p =>
    Real.rpow_nonneg (by linarith [normP_real_ge p.1]) _
  have hxh : ∀ p : T, ((normP p.1 : ℕ) : ℝ) ^ (-s) ≤ 1 / 2 := fun p => rpow_neg_normP_le_half p.1 hs.le
  have hxy : ∀ p : T, ((normP p.1 : ℕ) : ℝ) ^ (-s) ≤ ((normP p.1 : ℕ) : ℝ)⁻¹ := fun p =>
    rpow_neg_le_inv_aux (normP_real_ge p.1) hs.le
  have hsx : Summable fun p : T => ((normP p.1 : ℕ) : ℝ) ^ (-s) :=
    (summable_normP_rpow (F := K) hs).comp_injective (Subtype.val_injective (p := fun x => x ∈ T))
  have hb := fun p : T => log_inv_one_sub_bounds (hx0 p) (hxh p)
  have hg0 : ∀ p : T, 0 ≤ Real.log (1 - ((normP p.1 : ℕ) : ℝ) ^ (-s))⁻¹ := fun p => (hx0 p).trans (hb p).1
  have hg2 : ∀ p : T, Real.log (1 - ((normP p.1 : ℕ) : ℝ) ^ (-s))⁻¹ ≤ 2 * ((normP p.1 : ℕ) : ℝ) ^ (-s) :=
    fun p => by
      have := (hb p).2
      nlinarith [hx0 p, hxh p]
  have hgs := Summable.of_nonneg_of_le hg0 hg2 (hsx.mul_left 2)
  have hlog : Real.log (realZeta T s) = ∑' p : T, Real.log (1 - ((normP p.1 : ℕ) : ℝ) ^ (-s))⁻¹ := by
    rw [realZeta, (hasProd_real T hs).tprod_eq, Real.log_exp]
  have hsum : T.primeIdealZetaSum s = ∑' p : T, ((normP p.1 : ℕ) : ℝ) ^ (-s) := rfl
  rw [hlog, hsum, ← Summable.tsum_sub hgs hsx]
  have hd0 : ∀ p : T, 0 ≤ Real.log (1 - ((normP p.1 : ℕ) : ℝ) ^ (-s))⁻¹ - ((normP p.1 : ℕ) : ℝ) ^ (-s) :=
    fun p => sub_nonneg.mpr (hb p).1
  have hd2 : ∀ p : T, Real.log (1 - ((normP p.1 : ℕ) : ℝ) ^ (-s))⁻¹ - ((normP p.1 : ℕ) : ℝ) ^ (-s) ≤
      2 * (((normP p.1 : ℕ) : ℝ)⁻¹) ^ 2 := fun p => by
    have := (hb p).2
    have := pow_le_pow_left₀ (hx0 p) (hxy p) 2
    linarith
  exact ⟨tsum_nonneg hd0, (hgs.sub hsx).tsum_le_tsum hd2 ((summable_inv_sq T).mul_left 2)⟩

/-- **Proposition 4.1 (a)** (Milne, *CFT*, Chapter VI, p. 194): if a set of primes has a polar density, then it has
the same Dirichlet density. -/
@[kb "milne2020cft" "Ch. VI, Prop. 4.1 (a)"]
theorem prop_4_1a {T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} (h : HasPolarDensity T δ) :
    MilneHasDirichletDensity T δ := by
  obtain ⟨n, m, hn, rfl, g, hga, hg1, hev⟩ := h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmap : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
    · have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using this
    · simpa using hx
  have hev' := hmap.eventually hev
  have h2 : ContinuousAt (fun s : ℝ => g (s : ℂ)) 1 := by
    have h1 : ContinuousAt g ((1 : ℝ) : ℂ) := by simpa using hga.continuousAt
    exact h1.comp Complex.continuous_ofReal.continuousAt
  have hg1' : ‖g ((1 : ℝ) : ℂ)‖ ≠ 0 := by simpa using hg1
  have hcont : ContinuousAt (fun s : ℝ => Real.log ‖g (s : ℂ)‖) 1 :=
    ContinuousAt.comp_of_eq (Real.continuousAt_log hg1') h2.norm rfl
  have hl : (fun s : ℝ => Real.log ‖g (s : ℂ)‖) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) :=
    (hcont.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  have hne : ∀ᶠ s : ℝ in 𝓝[>] 1, g (s : ℂ) ≠ 0 := by
    have : ∀ᶠ s : ℝ in 𝓝 1, ‖g (s : ℂ)‖ ≠ 0 := h2.norm.eventually_ne hg1'
    exact (this.filter_mono nhdsWithin_le_nhds).mono fun s hs => by simpa using hs
  have hD : (fun s : ℝ => Real.log (realZeta T s) - T.primeIdealZetaSum s) =O[𝓝[>] 1]
      (fun _ => (1 : ℝ)) := by
    refine IsBigO.of_bound (boundC T) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have := logZeta_sub_sum_bounds T (show 1 < s from hs)
    rw [norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg this.1]
    exact this.2
  have hmain := (hD.neg_left).add (hl.const_mul_left (1 / (n : ℝ)))
  refine hmain.congr' ?_ EventuallyEq.rfl
  filter_upwards [hev', hne, self_mem_nhdsWithin] with s hs hgs hs1
  have hs1' : 1 < s := hs1
  have hpos := realZeta_pos T hs1'
  rw [primeZetaProduct_ofReal T hs1'] at hs
  have hsub : (0 : ℝ) < s - 1 := by linarith
  have hnorm : (realZeta T s) ^ n = ‖g (s : ℂ)‖ / (s - 1) ^ m := by
    have := congrArg norm hs
    rw [norm_pow, norm_div, norm_zpow, Complex.norm_real, Real.norm_of_nonneg hpos.le] at this
    rw [this]
    congr 2
    rw [show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg hsub.le]
  have hgn : 0 < ‖g (s : ℂ)‖ := norm_pos_iff.mpr hgs
  have hlogn : (n : ℝ) * Real.log (realZeta T s) = Real.log ‖g (s : ℂ)‖ - m * Real.log (s - 1) := by
    have := congrArg Real.log hnorm
    rw [Real.log_pow, Real.log_div hgn.ne' (zpow_pos hsub m).ne', Real.log_zpow] at this
    exact this
  have hL : Real.log (realZeta T s) = (Real.log ‖g (s : ℂ)‖ - m * Real.log (s - 1)) / n := by
    field_simp
    linarith
  simp only [one_div, Real.log_inv]
  rw [hL]
  field_simp
  ring

end Real41

/-- **Example 3.7, polar density** (Milne, *CFT*, Chapter VI, p. 193): for a monic irreducible cubic $f$ over
$\mathbb Z$, the primes modulo which $f$ splits have polar density $1/3$ or $1/6$ according as the Galois group has
order $3$ or $6$. -/
@[kb "milne2020cft" "Ch. VI, Example 3.7"]
theorem example_3_7_polar (f : (𝓞 ℚ)[X]) (hf : f.Monic) (h3 : f.natDegree = 3)
    (hirr : Irreducible (f.map (algebraMap (𝓞 ℚ) ℚ))) :
    (Nat.card (f.map (algebraMap (𝓞 ℚ) ℚ)).Gal = 3 → HasPolarDensity (splitModPrimes f) (1 / 3)) ∧
    (Nat.card (f.map (algebraMap (𝓞 ℚ) ℚ)).Gal = 6 → HasPolarDensity (splitModPrimes f) (1 / 6)) := by
  classical
  have hdeg : (f.map (algebraMap (𝓞 ℚ) ℚ)).natDegree = 3 := by
    rw [natDegree_map_eq_of_injective (IsFractionRing.injective (𝓞 ℚ) ℚ)]
    exact h3
  set g := f.map (algebraMap (𝓞 ℚ) ℚ) with hg
  have hs : g.Separable := hirr.separable
  have hcard : Fintype.card (g.rootSet g.SplittingField) = 3 :=
    (NumberFieldKB.MilneANT.card_rootSet_splittingField g hs).trans hdeg
  have hφ := NumberFieldKB.MilneANT.galPerm_injective g
  have hone : ∀ σ : g.Gal, NumberFieldKB.MilneANT.cyc f σ = {1, 1, 1} ↔ σ = 1 := fun σ =>
    NumberFieldKB.MilneANT.parts_eq_triv_iff (MulAction.toPermHom g.Gal (g.rootSet g.SplittingField))
      hφ hcard σ
  have hU : (⋃ C : NumberFieldKB.MilneANT.typeClasses f {1, 1, 1},
      frobSet ℚ (NumberFieldKB.MilneANT.SF f) C.1) = splitPrimes ℚ g.SplittingField := by
    have hcl : ∀ C : NumberFieldKB.MilneANT.typeClasses f {1, 1, 1}, C.1 = ConjClasses.mk 1 := by
      rintro ⟨C, σ, hσ, hc⟩
      have h1 : σ = 1 := (hone σ).1 hc
      rw [ConjClasses.mem_carrier_iff_mk_eq] at hσ
      show C = _
      rw [← hσ, h1]
    ext 𝔭
    simp only [Set.mem_iUnion]
    rw [splitPrimes_eq_frobSet_one]
    constructor
    · rintro ⟨C, hC⟩
      rw [hcl C] at hC
      exact hC
    · intro h
      exact ⟨⟨ConjClasses.mk 1, NumberFieldKB.MilneANT.mem_typeClasses_mk.2 ((hone 1).2 rfl)⟩, h⟩
  have hsym : (symmDiff (splitModPrimes f) (splitPrimes ℚ g.SplittingField)).Finite := by
    have h1 := splitModPrimes_symmDiff_finite f hf h3 hs
    have h2 := NumberFieldKB.MilneANT.factorizationTypeSet_symmDiff_finite
      NumberFieldKB.MilneANT.dedekindFrobenius f hf hs {1, 1, 1}
    rw [hU] at h2
    exact (h1.union h2).subset (symmDiff_triangle _ (NumberFieldKB.MilneANT.factorizationTypeSet f {1, 1, 1}) _)
  have hfr : Module.finrank ℚ g.SplittingField = Nat.card g.Gal := by
    exact (IsGalois.card_aut_eq_finrank ℚ g.SplittingField).symm
  have hpol := thm_3_4_galois (K := ℚ) g.SplittingField
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hh : (1 : ℝ) / (Module.finrank ℚ g.SplittingField : ℝ) = 1 / 3 := by
      rw [hfr, h]; norm_num
    rw [hh] at hpol
    exact hpol.congr_finite (by rw [symmDiff_comm]; exact hsym)
  · have hh : (1 : ℝ) / (Module.finrank ℚ g.SplittingField : ℝ) = 1 / 6 := by
      rw [hfr, h]; norm_num
    rw [hh] at hpol
    exact hpol.congr_finite (by rw [symmDiff_comm]; exact hsym)

end NumberFieldKB.MilneCFT.Ch6
