import NumberFieldKB.MilneCFT.Ch6.Density
import NumberFieldKB.Chebotarev.DensityTools
import NumberFieldKB.Chebotarev.FrobeniusPrimes
import NumberFieldKB.HeckeL.DedekindCont

/-!
# Auxiliary lemmas for the polar-density results of Milne, *CFT*, Chapter VI §§3–4

Euler factors `eulerF`, multipliability, the regrouping of the Euler product of $L$ along the primes of $K$ below
(for the Galois case of Theorem 3.4), and analyticity of the Euler product over the primes of $L$ not above a
completely split prime of $K$.
-/

open Filter Topology NumberField IsDedekindDomain
open NumberFieldKB.Chebotarev QuadFormsKB.NFEuler

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NumberFieldKB.MilneCFT.Ch6

section Euler

variable {E : Type} [Field E] [NumberField E]

/-- The Euler factor $(1 - N\mathfrak p^{-s})^{-1}$ of a prime $\mathfrak p$ of $E$. -/
def eulerF (s : ℂ) (P : HeightOneSpectrum (𝓞 E)) : ℂ :=
  (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹

theorem normP_real_ge (p : HeightOneSpectrum (𝓞 E)) : (2 : ℝ) ≤ ((normP p : ℕ) : ℝ) := by
  exact_mod_cast two_le_normP p

/-- Helper: $|N\mathfrak p^{-s}| = N\mathfrak p^{-\mathrm{Re}\,s}$. -/
theorem norm_cpow_normP (s : ℂ) (P : HeightOneSpectrum (𝓞 E)) :
    ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ = ((normP P : ℕ) : ℝ) ^ (-s.re) := by
  have h : 0 < normP P := by have := two_le_normP P; omega
  rw [Complex.norm_natCast_cpow_of_pos h]
  simp

/-- Helper: $\|(1-z)^{-1} - 1\| \le 2\|z\|$ for $\|z\| \le 1/2$. -/
theorem norm_inv_one_sub_sub_one_le {z : ℂ} (h : ‖z‖ ≤ 1 / 2) : ‖(1 - z)⁻¹ - 1‖ ≤ 2 * ‖z‖ := by
  have h1 : 1 / 2 ≤ ‖1 - z‖ := by
    have := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one] at this; linarith
  have hne : 1 - z ≠ 0 := by intro h0; rw [h0, norm_zero] at h1; linarith
  rw [show (1 - z)⁻¹ - 1 = z / (1 - z) by field_simp; ring, norm_div, div_le_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left h1 (norm_nonneg z)]

theorem norm_eulerF_sub_one_le {s : ℂ} (hs : 1 ≤ s.re) (P : HeightOneSpectrum (𝓞 E)) :
    ‖eulerF s P - 1‖ ≤ 2 * ((normP P : ℕ) : ℝ) ^ (-s.re) := by
  have h := norm_cpow_normP s P
  have hh : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    rw [h]; exact rpow_neg_normP_le_half P hs
  have := norm_inv_one_sub_sub_one_le hh
  rw [h] at this
  exact this

theorem summable_norm_eulerF_sub_one {s : ℂ} (hs : 1 < s.re) :
    Summable fun P : HeightOneSpectrum (𝓞 E) => ‖eulerF s P - 1‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun P => norm_eulerF_sub_one_le hs.le P)
    ((summable_normP_rpow (F := E) hs).mul_left 2)

theorem multipliable_of_summable_norm_sub_one {ι : Type*} {f : ι → ℂ}
    (hf : Summable fun i => ‖f i - 1‖) : Multipliable f := by
  have := multipliable_one_add_of_summable (f := fun i => f i - 1) hf
  simpa using this

theorem multipliable_mulIndicator_eulerF {s : ℂ} (hs : 1 < s.re) (A : Set (HeightOneSpectrum (𝓞 E))) :
    Multipliable (A.mulIndicator (eulerF s)) := by
  classical
  refine multipliable_of_summable_norm_sub_one (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => ?_) (summable_norm_eulerF_sub_one (E := E) hs))
  by_cases hP : P ∈ A
  · rw [Set.mulIndicator_of_mem hP]
  · rw [Set.mulIndicator_of_notMem hP]; simp

/-- Helper: the Euler product over all primes is the product over a set and over its complement. -/
theorem primeZetaProduct_univ_eq_mul_compl {s : ℂ} (hs : 1 < s.re) (A : Set (HeightOneSpectrum (𝓞 E))) :
    primeZetaProduct (Set.univ : Set (HeightOneSpectrum (𝓞 E))) s =
      primeZetaProduct A s * primeZetaProduct Aᶜ s := by
  have hA : Multipliable (fun P : A => eulerF s P.1) :=
    multipliable_of_summable_norm_sub_one ((summable_norm_eulerF_sub_one (E := E) hs).subtype A)
  have hAc : Multipliable (fun P : (Aᶜ : Set _) => eulerF s P.1) :=
    multipliable_of_summable_norm_sub_one ((summable_norm_eulerF_sub_one (E := E) hs).subtype Aᶜ)
  have := Multipliable.tprod_mul_tprod_compl (f := eulerF s) (s := A) hA hAc
  calc primeZetaProduct (Set.univ : Set (HeightOneSpectrum (𝓞 E))) s
      = ∏' P : (Set.univ : Set (HeightOneSpectrum (𝓞 E))), eulerF s P.1 := rfl
    _ = ∏' P, eulerF s P := tprod_univ _
    _ = _ := this.symm

/-- Helper: the Euler product over all primes is the Dedekind zeta function for $\mathrm{Re}\,s>1$. -/
theorem primeZetaProduct_univ_eq {s : ℂ} (hs : 1 < s.re) :
    primeZetaProduct (Set.univ : Set (HeightOneSpectrum (𝓞 E))) s = dedekindZeta E s := by
  rw [← NumberFieldKB.HeckeL.heckeL_one_eq_dedekindZeta hs, NumberFieldKB.HeckeL.heckeL, primeZetaProduct]
  refine (tprod_univ (fun v : HeightOneSpectrum (𝓞 E) =>
    (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)).trans (tprod_congr fun v => ?_)
  rw [NumberFieldKB.HeckeL.localL_one]
  simp

/-- Helper: $\zeta_E(s) = g(s)/(s-1)$ near $1$ with $g$ analytic and $g(1)\ne0$ (the content of
Proposition 3.1 (a)). -/
theorem zeta_polar_data : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
    ∀ᶠ s in 𝓝[{s : ℂ | 1 < s.re}] (1 : ℂ),
      primeZetaProduct (Set.univ : Set (HeightOneSpectrum (𝓞 E))) s = g s / (s - 1) := by
  set G : ℂ → ℂ := fun s => (s - 1) * NumberFieldKB.HeckeL.dedekindZetaCont E s with hG
  refine ⟨Function.update G 1 (dedekindZeta_residue E : ℂ), ?_, ?_, ?_⟩
  · refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hz1 : z ≠ 1 := hz
      have hd : DifferentiableAt ℂ G z :=
        (differentiableAt_id.sub_const 1).mul
          (NumberFieldKB.HeckeL.differentiableAt_dedekindZetaCont hz1)
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
      exact Function.update_of_ne hw _ _
    · exact continuousAt_update_same.mpr NumberFieldKB.HeckeL.tendsto_sub_one_mul_dedekindZetaCont
  · rw [Function.update_self]
    exact_mod_cast (dedekindZeta_residue_pos E).ne'
  · refine eventually_nhdsWithin_of_forall fun s hs => ?_
    have hs' : 1 < s.re := hs
    have hs1 : s ≠ 1 := fun h => by simp [h] at hs'
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [Function.update_of_ne hs1, primeZetaProduct_univ_eq hs', hG]
    show _ = (s - 1) * NumberFieldKB.HeckeL.dedekindZetaCont E s / (s - 1)
    rw [NumberFieldKB.HeckeL.dedekindZetaCont_eq hs']
    field_simp

end Euler

section Fibre

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- Helper: the fibre of the map $P\mapsto P\cap\mathcal O_K$ over $\mathfrak p$ is the set of primes over
$\mathfrak p$. -/
theorem fibre_set_eq (𝔭 : HeightOneSpectrum (𝓞 K)) :
    {P : HeightOneSpectrum (𝓞 L) | P.under (𝓞 K) = 𝔭} = {P | P.asIdeal.LiesOver 𝔭.asIdeal} := by
  ext P
  simp only [Set.mem_ofPred_eq, Ideal.liesOver_iff]
  constructor
  · intro h; rw [← h]; rfl
  · intro h; exact HeightOneSpectrum.ext (by simpa using h.symm)

/-- Helper: the fundamental identity for the number of primes over $\mathfrak p$. -/
theorem fibre_ncard_mul (𝔭 : HeightOneSpectrum (𝓞 K)) :
    {P : HeightOneSpectrum (𝓞 L) | P.asIdeal.LiesOver 𝔭.asIdeal}.ncard *
      (𝔭.asIdeal.ramificationIdxIn (𝓞 L) * 𝔭.asIdeal.inertiaDegIn (𝓞 L)) = Module.finrank K L := by
  rw [ncard_fibre_eq]
  have hid := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔭.asIdeal (𝓞 L) Gal(L/K)
  rw [IsGaloisGroup.card_eq_finrank Gal(L/K) K L] at hid
  exact hid

/-- Helper: a completely split prime has exactly $[L:K]$ primes above it. -/
theorem fibre_ncard_split {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ splitPrimes K L) :
    {P : HeightOneSpectrum (𝓞 L) | P.asIdeal.LiesOver 𝔭.asIdeal}.ncard = Module.finrank K L := by
  have hid := fibre_ncard_mul (L := L) 𝔭
  obtain ⟨Q⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 L)))
  have h1 := h𝔭 Q
  haveI := Q.2.1
  haveI := Q.2.2
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal Q.1 Gal(L/K),
    Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal Q.1 Gal(L/K), h1.1, h1.2] at hid
  simpa using hid

/-- Helper: every prime of $K$ has at most $[L:K]$ primes above it, and at least one. -/
theorem fibre_ncard_le_pos (𝔭 : HeightOneSpectrum (𝓞 K)) :
    {P : HeightOneSpectrum (𝓞 L) | P.asIdeal.LiesOver 𝔭.asIdeal}.ncard ≤ Module.finrank K L ∧
      {P : HeightOneSpectrum (𝓞 L) | P.asIdeal.LiesOver 𝔭.asIdeal}.ncard ≠ 0 := by
  have hid := fibre_ncard_mul (L := L) 𝔭
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  generalize 𝔭.asIdeal.ramificationIdxIn (𝓞 L) * 𝔭.asIdeal.inertiaDegIn (𝓞 L) = c at hid
  generalize {P : HeightOneSpectrum (𝓞 L) | P.asIdeal.LiesOver 𝔭.asIdeal}.ncard = m at hid ⊢
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, mul_zero] at hid; omega
    · calc m ≤ m * c := Nat.le_mul_of_pos_right _ h
        _ = _ := hid
  · rintro rfl; rw [zero_mul] at hid; omega

theorem finite_fibre (𝔭 : HeightOneSpectrum (𝓞 K)) :
    {P : HeightOneSpectrum (𝓞 L) | P.under (𝓞 K) = 𝔭}.Finite := by
  rw [fibre_set_eq]
  exact Set.finite_of_ncard_ne_zero (fibre_ncard_le_pos 𝔭).2

theorem nat_card_fibre_le (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Nat.card {P : HeightOneSpectrum (𝓞 L) // P.under (𝓞 K) = 𝔭} ≤ Module.finrank K L := by
  have h : Nat.card {P : HeightOneSpectrum (𝓞 L) // P.under (𝓞 K) = 𝔭} =
      {P : HeightOneSpectrum (𝓞 L) | P.under (𝓞 K) = 𝔭}.ncard := Nat.card_coe_set_eq _
  rw [h, fibre_set_eq]
  exact (fibre_ncard_le_pos 𝔭).1

/-- Helper: $\sum_P N(P\cap\mathcal O_K)^{-\sigma} < \infty$ for $\sigma>1$ (at most $[L:K]$ primes above each
$\mathfrak p$). -/
theorem summable_under_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun P : HeightOneSpectrum (𝓞 L) => ((normP (P.under (𝓞 K)) : ℕ) : ℝ) ^ (-σ) := by
  set h : HeightOneSpectrum (𝓞 K) → ℝ := fun 𝔭 => ((normP 𝔭 : ℕ) : ℝ) ^ (-σ) with hh_def
  have hh : Summable h := summable_normP_rpow hσ
  have h0 : ∀ 𝔭, 0 ≤ h 𝔭 := fun 𝔭 => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let e := Equiv.sigmaFiberEquiv (fun P : HeightOneSpectrum (𝓞 L) => P.under (𝓞 K))
  refine e.summable_iff.1 ?_
  have hGe : ((fun P : HeightOneSpectrum (𝓞 L) => ((normP (P.under (𝓞 K)) : ℕ) : ℝ) ^ (-σ)) ∘ e) =
      fun x => h x.1 := by
    funext x
    obtain ⟨𝔭, c, hc⟩ := x
    change h (c.under (𝓞 K)) = h 𝔭
    rw [hc]
  rw [hGe]
  have hfin : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), Finite {P : HeightOneSpectrum (𝓞 L) // P.under (𝓞 K) = 𝔭} :=
    fun 𝔭 => (finite_fibre 𝔭).to_subtype
  refine (summable_sigma_of_nonneg (fun x => h0 _)).2 ⟨fun 𝔭 => ?_, ?_⟩
  · haveI := hfin 𝔭
    exact Summable.of_finite
  · refine Summable.of_nonneg_of_le (fun 𝔭 => tsum_nonneg fun _ => h0 _) (fun 𝔭 => ?_)
      (hh.mul_left (Module.finrank K L : ℝ))
    haveI := hfin 𝔭
    show ∑' _ : {P : HeightOneSpectrum (𝓞 L) // P.under (𝓞 K) = 𝔭}, h 𝔭 ≤ _
    rw [tsum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast nat_card_fibre_le 𝔭) (h0 𝔭)

/-- The primes of $L$ lying over a completely split prime of $K$. -/
def splitAbove (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    Set (HeightOneSpectrum (𝓞 L)) :=
  {P | P.under (𝓞 K) ∈ splitPrimes K L}

/-- Helper: for $\mathfrak P$ over a completely split $\mathfrak p$, $N\mathfrak P = N\mathfrak p$. -/
theorem normP_eq_of_split {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ splitPrimes K L)
    (P : HeightOneSpectrum (𝓞 L)) (hP : P.under (𝓞 K) = 𝔭) : normP P = normP 𝔭 := by
  haveI : P.asIdeal.LiesOver 𝔭.asIdeal := ⟨by rw [← hP]; rfl⟩
  have h1 := (h𝔭 ⟨P.asIdeal, P.isPrime, this⟩).2
  have h := absNorm_pow_inertiaDeg_eq (F := K) L P 𝔭
  rw [h1, pow_one] at h
  exact h.symm

/-- **Regrouping along the prime below**: $\zeta_{L,T}(s) = \zeta_{K,S}(s)^{[L:K]}$, where $S$ is the set of
completely split primes of $K$ and $T$ the set of primes of $L$ above them. -/
theorem primeZetaProduct_splitAbove {s : ℂ} (hs : 1 < s.re) :
    primeZetaProduct (splitAbove K L) s = primeZetaProduct (splitPrimes K L) s ^ Module.finrank K L := by
  classical
  set T := splitAbove K L with hT
  set S := splitPrimes K L with hS
  set n := Module.finrank K L with hn
  have hmulL : Multipliable (T.mulIndicator (eulerF s) : HeightOneSpectrum (𝓞 L) → ℂ) :=
    multipliable_mulIndicator_eulerF hs T
  have hmulK : Multipliable (S.mulIndicator (eulerF s) : HeightOneSpectrum (𝓞 K) → ℂ) :=
    multipliable_mulIndicator_eulerF hs S
  let e := Equiv.sigmaFiberEquiv (fun P : HeightOneSpectrum (𝓞 L) => P.under (𝓞 K))
  have hm : Multipliable (fun x => T.mulIndicator (eulerF s) (e x)) := (e.multipliable_iff).2 hmulL
  have hfin : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), Finite {P : HeightOneSpectrum (𝓞 L) // P.under (𝓞 K) = 𝔭} :=
    fun 𝔭 => (finite_fibre 𝔭).to_subtype
  have hfib : ∀ 𝔭 : HeightOneSpectrum (𝓞 K),
      ∏' c : {P : HeightOneSpectrum (𝓞 L) // P.under (𝓞 K) = 𝔭}, T.mulIndicator (eulerF s) c.1 =
        (S.mulIndicator (eulerF s) 𝔭) ^ n := by
    intro 𝔭
    haveI := hfin 𝔭
    haveI := Fintype.ofFinite {P : HeightOneSpectrum (𝓞 L) // P.under (𝓞 K) = 𝔭}
    rw [tprod_fintype]
    by_cases h𝔭 : 𝔭 ∈ S
    · rw [Set.mulIndicator_of_mem h𝔭]
      have : ∀ c : {P : HeightOneSpectrum (𝓞 L) // P.under (𝓞 K) = 𝔭},
          T.mulIndicator (eulerF s) c.1 = eulerF s 𝔭 := by
        intro c
        have hc : c.1 ∈ T := by
          show c.1.under (𝓞 K) ∈ S
          rw [c.2]; exact h𝔭
        rw [Set.mulIndicator_of_mem hc]
        have hN := normP_eq_of_split h𝔭 c.1 c.2
        simp only [eulerF]
        have : (Ideal.absNorm c.1.asIdeal : ℂ) = (Ideal.absNorm 𝔭.asIdeal : ℂ) := by
          exact_mod_cast hN
        rw [this]
      rw [Finset.prod_congr rfl (fun c _ => this c), Finset.prod_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card]
      congr 1
      have h2 : Nat.card {P : HeightOneSpectrum (𝓞 L) // P.under (𝓞 K) = 𝔭} =
          {P : HeightOneSpectrum (𝓞 L) | P.under (𝓞 K) = 𝔭}.ncard := Nat.card_coe_set_eq _
      rw [h2, fibre_set_eq]
      exact fibre_ncard_split h𝔭
    · rw [Set.mulIndicator_of_notMem h𝔭, one_pow]
      refine Finset.prod_eq_one fun c _ => ?_
      have hc : c.1 ∉ T := by
        show ¬ c.1.under (𝓞 K) ∈ S
        rw [c.2]; exact h𝔭
      rw [Set.mulIndicator_of_notMem hc]
  calc primeZetaProduct T s = ∏' P : T, eulerF s P.1 := rfl
    _ = ∏' P, T.mulIndicator (eulerF s) P := tprod_subtype T _
    _ = ∏' x, T.mulIndicator (eulerF s) (e x) := (e.tprod_eq _).symm
    _ = ∏' 𝔭, ∏' c : {P : HeightOneSpectrum (𝓞 L) // P.under (𝓞 K) = 𝔭},
          T.mulIndicator (eulerF s) c.1 :=
        hm.tprod_sigma' (fun 𝔭 => by haveI := hfin 𝔭; exact Multipliable.of_finite)
    _ = ∏' 𝔭, (S.mulIndicator (eulerF s) 𝔭) ^ n := tprod_congr hfib
    _ = (∏' 𝔭, S.mulIndicator (eulerF s) 𝔭) ^ n := hmulK.tprod_pow n
    _ = primeZetaProduct S s ^ n := by
        rw [← tprod_subtype S (eulerF s)]; rfl

end Fibre

section Analytic

theorem one_sub_cpow_ne_zero {E : Type} [Field E] [NumberField E] {s : ℂ} (hs : 0 < s.re)
    (P : HeightOneSpectrum (𝓞 E)) : 1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have h2 := norm_cpow_normP s P
  rw [h1, norm_one] at h2
  have h3 : (1 : ℝ) < ((normP P : ℕ) : ℝ) := by
    have := normP_real_ge P; linarith
  have := Real.rpow_lt_one_of_one_lt_of_neg h3 (show -s.re < 0 by linarith)
  linarith

theorem differentiableAt_eulerF {E : Type} [Field E] [NumberField E] {s : ℂ} (hs : 0 < s.re)
    (P : HeightOneSpectrum (𝓞 E)) : DifferentiableAt ℂ (fun s => eulerF s P) s := by
  have hN : (Ideal.absNorm P.asIdeal : ℂ) ≠ 0 := by
    have : 2 ≤ Ideal.absNorm P.asIdeal := two_le_normP P
    exact_mod_cast (by omega : Ideal.absNorm P.asIdeal ≠ 0)
  have hz : DifferentiableAt ℂ (fun s : ℂ => (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hN)
  exact ((differentiableAt_const _).sub hz).inv (one_sub_cpow_ne_zero hs P)

theorem eulerF_ne_zero {E : Type} [Field E] [NumberField E] {s : ℂ} (hs : 0 < s.re)
    (P : HeightOneSpectrum (𝓞 E)) : eulerF s P ≠ 0 :=
  inv_ne_zero (one_sub_cpow_ne_zero hs P)

theorem rpow_neg_le_of_sq_le {a b r : ℝ} (ha : 1 ≤ a) (hab : a ^ 2 ≤ b) (hr : 3 / 4 ≤ r) :
    b ^ (-r) ≤ a ^ (-(3 / 2 : ℝ)) := by
  have ha0 : 0 < a := by linarith
  calc b ^ (-r) ≤ (a ^ 2) ^ (-r) := Real.rpow_le_rpow_of_nonpos (pow_pos ha0 2) hab (by linarith)
    _ = a ^ (-(2 * r)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
        congr 1; push_cast; ring
    _ ≤ a ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le ha (by linarith)

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- The primes of $L$ above a prime of $K$ ramified in $L$ (a finite set). -/
def badSet (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    Set (HeightOneSpectrum (𝓞 L)) :=
  {P | P.under (𝓞 K) ∈ (unramifiedPrimes K L)ᶜ}

theorem finite_badSet : (badSet K L).Finite :=
  (finite_compl_unramifiedPrimes K L).preimage' fun 𝔭 _ => (finite_fibre 𝔭).subset fun P hP => hP

/-- Helper: a prime of $L$ over an unramified prime of $K$ that is not over a completely split prime has
$N\mathfrak P\ge N(\mathfrak P\cap\mathcal O_K)^2$ (its residue degree is $\ge2$, by Galois-ness). -/
theorem normP_sq_le_of_notMem {P : HeightOneSpectrum (𝓞 L)} (hP : P ∉ splitAbove K L)
    (hunr : P.under (𝓞 K) ∈ unramifiedPrimes K L) :
    (normP (P.under (𝓞 K))) ^ 2 ≤ normP P := by
  set 𝔭 := P.under (𝓞 K) with h𝔭
  haveI : P.asIdeal.LiesOver 𝔭.asIdeal := liesOver_under (F := K) L P
  have hP' : 𝔭 ∉ splitPrimes K L := hP
  simp only [splitPrimes, Set.mem_ofPred_eq, not_forall] at hP'
  obtain ⟨Q, hQ⟩ := hP'
  haveI := Q.2.1
  haveI := Q.2.2
  have hunr' : Algebra.IsUnramifiedIn (𝓞 L) 𝔭.asIdeal := hunr
  have he : Q.1.ramificationIdx (𝓞 K) = 1 := Algebra.IsUnramifiedIn.ramificationIdx_eq_one hunr' Q.2.2
  have hf : Q.1.inertiaDeg (𝓞 K) ≠ 1 := fun h => hQ ⟨he, h⟩
  have hfP : P.asIdeal.inertiaDeg (𝓞 K) = Q.1.inertiaDeg (𝓞 K) :=
    Ideal.inertiaDeg_eq_of_isGaloisGroup 𝔭.asIdeal P.asIdeal Q.1 Gal(L/K)
  have hpos : 0 < P.asIdeal.inertiaDeg (𝓞 K) := Ideal.inertiaDeg_pos _ _
  have h2 : 2 ≤ P.asIdeal.inertiaDeg (𝓞 K) := by omega
  have hN := absNorm_pow_inertiaDeg_eq (F := K) L P 𝔭
  rw [← hN]
  exact Nat.pow_le_pow_right (by have := two_le_normP 𝔭; omega) h2

theorem norm_eulerF_sub_one_tail_le {s : ℂ} (hs : 3 / 4 ≤ s.re) {P : HeightOneSpectrum (𝓞 L)}
    (hP : P ∉ splitAbove K L) (hb : P ∉ badSet K L) :
    ‖eulerF s P - 1‖ ≤ 2 * ((normP (P.under (𝓞 K)) : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hunr : P.under (𝓞 K) ∈ unramifiedPrimes K L := by
    by_contra h; exact hb h
  have hsq := normP_sq_le_of_notMem hP hunr
  have hsq' : ((normP (P.under (𝓞 K)) : ℕ) : ℝ) ^ 2 ≤ ((normP P : ℕ) : ℝ) := by exact_mod_cast hsq
  have hNu : (1 : ℝ) ≤ ((normP (P.under (𝓞 K)) : ℕ) : ℝ) := by
    have := normP_real_ge (P.under (𝓞 K)); linarith
  have hx := rpow_neg_le_of_sq_le hNu hsq' hs
  have hc : ((normP (P.under (𝓞 K)) : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 1 / 2 := by
    have h1 : ((normP (P.under (𝓞 K)) : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤
        ((normP (P.under (𝓞 K)) : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hNu (by norm_num)
    rw [Real.rpow_neg_one] at h1
    have h2 := normP_real_ge (P.under (𝓞 K))
    have h3 : ((normP (P.under (𝓞 K)) : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h2
    linarith
  have hz := norm_cpow_normP s P
  have hz' : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ ≤ 1 / 2 := by rw [hz]; linarith
  have := norm_inv_one_sub_sub_one_le hz'
  rw [hz] at this
  show ‖(1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹ - 1‖ ≤ _
  linarith

theorem eventually_tail_bound :
    ∀ᶠ P : ↥((splitAbove K L)ᶜ) in cofinite, ∀ s : ℂ, 3 / 4 ≤ s.re →
      ‖eulerF s P.1 - 1‖ ≤ 2 * ((normP (P.1.under (𝓞 K)) : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  rw [Filter.eventually_cofinite]
  refine ((finite_badSet (K := K) (L := L)).preimage Subtype.val_injective.injOn).subset ?_
  intro P hP
  by_contra hb
  exact hP fun s hs => norm_eulerF_sub_one_tail_le hs P.2 hb

theorem summable_tail_bound :
    Summable fun P : ↥((splitAbove K L)ᶜ) => 2 * ((normP (P.1.under (𝓞 K)) : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
  ((summable_under_rpow (K := K) (L := L) (σ := 3 / 2) (by norm_num)).subtype _).mul_left 2

/-- **Analyticity of the Euler product over the primes not above a completely split prime**: it is
holomorphic on $\mathrm{Re}\,s > 3/4$. -/
theorem differentiableOn_primeZetaProduct_compl :
    DifferentiableOn ℂ (primeZetaProduct (splitAbove K L)ᶜ) {s : ℂ | 3 / 4 < s.re} := by
  have hU : IsOpen {s : ℂ | 3 / 4 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  set f : ↥((splitAbove K L)ᶜ) → ℂ → ℂ := fun P s => eulerF s P.1 - 1 with hf
  have hd : ∀ (P : ↥((splitAbove K L)ᶜ)), ∀ x ∈ {s : ℂ | 3 / 4 < s.re},
      DifferentiableAt ℂ (f P) x := by
    intro P x hx
    have hx' : 0 < x.re := by have : 3 / 4 < x.re := hx; linarith
    exact (differentiableAt_eulerF hx' P.1).sub_const 1
  have h := Summable.hasProdLocallyUniformlyOn_one_add (K := {s : ℂ | 3 / 4 < s.re}) (f := f) hU
    summable_tail_bound (by
      filter_upwards [eventually_tail_bound (K := K) (L := L)] with P hP x hx
      exact hP x (le_of_lt hx))
    (fun P x hx => (hd P x hx).continuousAt.continuousWithinAt)
  have hF : ∀ᶠ t : Finset ↥((splitAbove K L)ᶜ) in atTop,
      DifferentiableOn ℂ (fun x => ∏ i ∈ t, (1 + f i x)) {s : ℂ | 3 / 4 < s.re} :=
    Filter.Eventually.of_forall fun t =>
      DifferentiableOn.fun_finsetProd fun i _ x hx =>
        ((differentiableAt_const (1 : ℂ)).add (hd i x hx)).differentiableWithinAt
  have h2 := TendstoLocallyUniformlyOn.differentiableOn h hF hU
  refine h2.congr fun x _ => ?_
  simp only [f, add_sub_cancel]
  rfl

/-- The Euler product over the primes not above a completely split prime is nonzero for $\mathrm{Re}\,s>3/4$. -/
theorem primeZetaProduct_compl_ne_zero {s : ℂ} (hs : 3 / 4 < s.re) :
    primeZetaProduct (splitAbove K L)ᶜ s ≠ 0 := by
  have hs0 : 0 < s.re := by linarith
  set f : ↥((splitAbove K L)ᶜ) → ℂ := fun P => eulerF s P.1 - 1 with hf
  have hu : Summable fun P => ‖f P‖ := by
    refine Summable.of_norm_bounded_eventually summable_tail_bound ?_
    filter_upwards [eventually_tail_bound (K := K) (L := L)] with P hP
    rw [norm_norm]; exact hP s hs.le
  have h := tprod_one_add_ne_zero_of_summable (f := f)
    (fun P => by simpa [f] using eulerF_ne_zero hs0 P.1) hu
  have e : primeZetaProduct (splitAbove K L)ᶜ s = ∏' P, (1 + f P) := by
    simp only [hf, add_sub_cancel]; rfl
  rw [e]; exact h

end Analytic

section Finite

variable {E : Type} [Field E] [NumberField E]

/-- Helper: the Euler product over a disjoint union is the product of the Euler products. -/
theorem primeZetaProduct_union_disjoint {s : ℂ} (hs : 1 < s.re) {A B : Set (HeightOneSpectrum (𝓞 E))}
    (hd : Disjoint A B) :
    primeZetaProduct (A ∪ B) s = primeZetaProduct A s * primeZetaProduct B s := by
  have hA : Multipliable (eulerF s ∘ ((↑) : A → HeightOneSpectrum (𝓞 E))) :=
    multipliable_of_summable_norm_sub_one ((summable_norm_eulerF_sub_one (E := E) hs).subtype A)
  have hB : Multipliable (eulerF s ∘ ((↑) : B → HeightOneSpectrum (𝓞 E))) :=
    multipliable_of_summable_norm_sub_one ((summable_norm_eulerF_sub_one (E := E) hs).subtype B)
  exact Multipliable.tprod_union_disjoint hd hA hB

/-- Helper: the Euler product over a finite set of primes is a finite product of analytic nonvanishing
factors. -/
theorem finite_primeZetaProduct {A : Set (HeightOneSpectrum (𝓞 E))} (hA : A.Finite) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 1 ∧ (∀ s : ℂ, 0 < s.re → F s ≠ 0) ∧
      ∀ s : ℂ, 0 < s.re → primeZetaProduct A s = F s := by
  classical
  refine ⟨fun s => ∏ p ∈ hA.toFinset, eulerF s p, ?_, ?_, ?_⟩
  · have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hd : DifferentiableOn ℂ (fun s => ∏ p ∈ hA.toFinset, eulerF s p) {s : ℂ | 0 < s.re} :=
      DifferentiableOn.fun_finsetProd fun p _ s hs => (differentiableAt_eulerF hs p).differentiableWithinAt
    exact hd.analyticAt (hU.mem_nhds (by simp))
  · intro s hs
    exact Finset.prod_ne_zero_iff.2 fun p _ => eulerF_ne_zero hs p
  · intro s _
    haveI := hA.fintype
    rw [primeZetaProduct, tprod_fintype]
    exact (Finset.prod_subtype hA.toFinset (fun x => by simp) (eulerF s)).symm

/-- **Polar density is unchanged by a finite modification of the set of primes.** -/
theorem HasPolarDensity.congr_finite {S T : Set (HeightOneSpectrum (𝓞 E))} {δ : ℝ}
    (h : HasPolarDensity S δ) (hST : (symmDiff S T).Finite) : HasPolarDensity T δ := by
  obtain ⟨n, m, hn, hδ, g, hg, hg1, hev⟩ := h
  have h1 : (T \ S).Finite := hST.subset fun x hx => Or.inr hx
  have h2 : (S \ T).Finite := hST.subset fun x hx => Or.inl hx
  obtain ⟨F1, hF1, hF1n, hF1e⟩ := finite_primeZetaProduct h1
  obtain ⟨F2, hF2, hF2n, hF2e⟩ := finite_primeZetaProduct h2
  have hF2_1 : F2 1 ≠ 0 := hF2n 1 (by simp)
  refine ⟨n, m, hn, hδ, fun s => g s * (F1 s / F2 s) ^ n, hg.mul ((hF1.div hF2 hF2_1).pow n),
    mul_ne_zero hg1 (pow_ne_zero _ (div_ne_zero (hF1n 1 (by simp)) hF2_1)), ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hs'
  have hs1 : 1 < s.re := hs'
  have hs0 : 0 < s.re := by linarith
  have eT' : T = (T ∩ S) ∪ (T \ S) := (Set.inter_union_sdiff T S).symm
  have eS' : S = (T ∩ S) ∪ (S \ T) := by rw [Set.inter_comm]; exact (Set.inter_union_sdiff S T).symm
  have eT : primeZetaProduct T s = primeZetaProduct (T ∩ S) s * primeZetaProduct (T \ S) s := by
    calc primeZetaProduct T s = primeZetaProduct ((T ∩ S) ∪ (T \ S)) s :=
          congrArg (fun A => primeZetaProduct A s) eT'
      _ = _ := primeZetaProduct_union_disjoint hs1
          (Set.disjoint_left.2 fun x hx hy => hy.2 hx.2)
  have eS : primeZetaProduct S s = primeZetaProduct (T ∩ S) s * primeZetaProduct (S \ T) s := by
    calc primeZetaProduct S s = primeZetaProduct ((T ∩ S) ∪ (S \ T)) s :=
          congrArg (fun A => primeZetaProduct A s) eS'
      _ = _ := primeZetaProduct_union_disjoint hs1
          (Set.disjoint_left.2 fun x hx hy => hy.2 hx.1)
  rw [hF1e s hs0] at eT
  rw [hF2e s hs0] at eS
  have hF2s := hF2n s hs0
  have hTS : primeZetaProduct T s = primeZetaProduct S s * (F1 s / F2 s) := by
    rw [eT, eS]; field_simp
  show primeZetaProduct T s ^ n = g s * (F1 s / F2 s) ^ n / (s - 1) ^ m
  rw [hTS, mul_pow, hs, div_mul_eq_mul_div]

end Finite

end NumberFieldKB.MilneCFT.Ch6
