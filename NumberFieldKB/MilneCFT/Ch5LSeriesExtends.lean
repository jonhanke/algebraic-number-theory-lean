import NumberFieldKB.MilneCFT.Ch5LSeries
import NumberFieldKB.MilneCFT.Ch8.WeberLTauCeti

/-!
# Milne, *Class Field Theory*, Chapter V, Theorem 2.4(b), corrected and proved

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter V, Theorem 2.4(b),
p. 156.

As printed, Theorem 2.4(b) says that for a nontrivial character $\chi$ of a ray class group $C_\mathfrak m$ "the series
for $L(s,\chi)$ converges for $\Re(s) > 0$ and $L(1,\chi) \ne 0$". The convergence claim is an erratum (confirmed by
Jon Hanke, 2026-11-08): for $[K:\mathbb Q] \ge 2$ the Dirichlet series need not
converge on the whole half-plane (Landau); what holds, and what Milne uses, is that $L(s,\chi)$ **extends** to an
analytic function on $\Re(s) > 0$. The literal statement stays the named statement `Theorem2_4b` (labelled an
erratum, not refuted here).

**Proved here** (`theorem_2_4b_extends : Theorem2_4bExtends K`): for every modulus $\mathfrak m$ and every nontrivial
$\chi : C_\mathfrak m \to \mathbb C^\times$ there is a function $L$ holomorphic on $\Re(s) > 0$, equal to the Weber
$L$-series `weberLSeries` for $\Re(s) > 1$, with $L(1) \ne 0$.

*Proof.* Let $\Psi$ be the finite-order Hecke character attached to $\chi$ (`exists_heckeChar`), as in the proof of
Chapter VIII, Theorem 7.1 (`Ch8.theorem7_1`). Its completed $L$-function gives the entire function `heckeLCont Ψ`,
nonzero at $s = 1$. For $\Re(s) > 1$ the Weber series times the Euler factors $L_\mathfrak p(s,\Psi)$ at the primes
$\mathfrak p \mid \mathfrak m_0$ equals $L(s,\Psi)$ (`weberLSeries_mul_prod_eq_heckeL_complex`, the complex form of
`Ch8.weberLSeries_mul_prod_eq_heckeL`). So
$L(s) = L(s,\Psi)\prod_{\mathfrak p\mid\mathfrak m_0,\ \Psi\ \text{unramified at}\ \mathfrak p}(1 - \Psi_\mathfrak p(\varpi)N\mathfrak p^{-s})$
is entire, equal to the Weber series for $\Re(s) > 1$ and nonzero at $1$.
-/

open NumberField IsDedekindDomain Filter Topology QuadFormsKB QuadFormsKB.NFEuler
open NumberFieldKB.HeckeCharacter NumberFieldKB.HeckeL NumberFieldKB.NonVanishing NumberFieldKB.GlobalZeta

noncomputable section

namespace NumberFieldKB.MilneCFT

variable (K : Type) [Field K] [NumberField K]

/-- **Theorem 2.4(b), corrected** (Milne, *CFT*, V, Theorem 2.4(b), p. 156, with "converges for" read as "extends to",
an erratum confirmed by Jon Hanke, 2026-11-08): for a nontrivial character $\chi$ of a ray class group $C_\mathfrak m$,
the Weber $L$-series $L(s,\chi) = \sum_{(\mathfrak a,\mathfrak m_0) = 1}\chi(\mathfrak a)N\mathfrak a^{-s}$ (`weberLSeries`,
absolutely convergent for $\Re(s) > 1$) extends to a holomorphic function on the half-plane $\Re(s) > 0$, and its value
at $s = 1$ is nonzero. -/
@[kb "milne2020cft" "Ch. V, Theorem 2.4(b) (corrected: extends to Re(s) > 0)"]
structure Theorem2_4bExtends : Prop where
  extends_ : ∀ (m : Modulus K) (χ : RayClassGroup m →* ℂˣ), χ ≠ 1 →
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s : ℂ | 0 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → L s = weberLSeries m χ s) ∧ L 1 ≠ 0

variable {K}

open Ch8 Classical in
theorem norm_webTerm_le_complex (m : Modulus K) (χ : RayClassGroup m →* ℂˣ) (hfin : Finite (RayClassGroup m))
    (s : ℂ) (𝔞 : Ideal (𝓞 K)) :
    ‖webTerm m χ s 𝔞‖ ≤ (Ideal.absNorm 𝔞 : ℝ) ^ (-s.re) := by
  unfold webTerm
  split_ifs with h
  · have hpos : 0 < Ideal.absNorm 𝔞 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h.1)
    rw [norm_mul, norm_eq_one_of_finite m χ hfin, one_mul, Complex.norm_natCast_cpow_of_pos hpos]
    simp
  · rw [norm_zero]; positivity

open Ch8 Classical in
/-- Complex form of `Ch8.weberLSeries_mul_prod_eq_heckeL`: for $\Re s > 1$,
$L(s,\chi)\prod_{\mathfrak p\mid\mathfrak m_0}L_\mathfrak p(s,\Psi) = L(s,\Psi)$. -/
theorem weberLSeries_mul_prod_eq_heckeL_complex (m : Modulus K) (χ : RayClassGroup m →* ℂˣ)
    (hfin : Finite (RayClassGroup m)) (Ψ : HeckeCharacter K)
    (hunit : Ψ.IsUnitary)
    (hloc : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite), Ψ.IsUnramifiedAt v ∧
      (Ψ.finiteComponent v (Analysis.ϖU v) : ℂ) = χ (rayClass m v hv))
    {s : ℂ} (hs : 1 < s.re) :
    weberLSeries m χ s * ∏ v ∈ badPrimes m, localL Ψ s v = heckeL Ψ s := by
  set g := webTerm m χ s with hg
  have hbd : ∀ v : HeightOneSpectrum (𝓞 K), ‖g v.asIdeal‖ ≤ 1 / 2 := fun v =>
    (norm_webTerm_le_complex m χ hfin s _).trans (QuadFormsKB.NFEuler.rpow_neg_normP_le_half v hs.le)
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), 1 - g v.asIdeal ≠ 0 := by
    intro v h
    have h1 : g v.asIdeal = 1 := by linear_combination -h
    have := hbd v
    rw [h1, norm_one] at this
    norm_num at this
  have hloc_eq : ∀ v ∉ badPrimes m, localL Ψ s v = (1 - g v.asIdeal)⁻¹ := by
    intro v hv
    have hv' : ¬ v.asIdeal ∣ m.finite := fun h => hv ((mem_badPrimes m).2 h)
    have hr : rV Ψ s v = g v.asIdeal := by
      rw [hg, webTerm_prime m χ _ v hv']
      unfold rV
      rw [(hloc v hv').2, Complex.ofReal_natCast]
    rw [localL, if_pos (hloc v hv').1, hr]
  have hshift : Ψ.shift = 0 := (shift_eq_zero_iff Ψ).mpr hunit
  have hP : HasProd (localL Ψ s) (heckeL Ψ s) := hasProd_heckeL Ψ (by simp [hshift, hs])
  set h : HeightOneSpectrum (𝓞 K) → ℂ := fun v => localL Ψ s v * (1 - g v.asIdeal) with hh_def
  have hh : HasProd h (∏ v ∈ badPrimes m, h v) :=
    hasProd_prod_of_ne_finset_one fun v hv => by
      rw [hh_def]; simp only; rw [hloc_eq v hv]; exact inv_mul_cancel₀ (hne v)
  have hW := hasProd_euler g hs (webTerm_mul m χ s) (webTerm_top m χ s) (webTerm_bot m χ s)
    (norm_webTerm_le_complex m χ hfin s)
  have hprod := hh.mul hW
  have hfun : (fun v => h v * (1 - g v.asIdeal)⁻¹) = localL Ψ s := by
    funext v
    simp only [hh_def]
    rw [mul_assoc, mul_inv_cancel₀ (hne v), mul_one]
  rw [hfun] at hprod
  have heq := hP.unique hprod
  have hbad : ∏ v ∈ badPrimes m, h v = ∏ v ∈ badPrimes m, localL Ψ s v :=
    Finset.prod_congr rfl fun v hv => by
      simp only [hh_def, hg]
      rw [webTerm_prime_dvd m χ _ v ((mem_badPrimes m).1 hv), sub_zero, mul_one]
  rw [heq, hbad, weberLSeries_eq_tsum]
  ring

open Ch8 Classical in
/-- **Theorem 2.4(b), corrected**, proved (Milne, *CFT*, V, Theorem 2.4(b), p. 156; "converges" read as "extends"). -/
@[kb "milne2020cft" "Ch. V, Theorem 2.4(b) (corrected form, proved)"]
theorem theorem_2_4b_extends (K : Type) [Field K] [NumberField K] : Theorem2_4bExtends K := by
  refine ⟨fun m χ hχ => ?_⟩
  haveI hfin : Finite (RayClassGroup m) := (theorem_1_7_card m).1
  let ψ : MulChar (RayClassGroup m) ℂ := MulChar.ofUnitHom (χ.comp (toUnits (G := RayClassGroup m)).symm.toMonoidHom)
  have hψ : ∀ g, ψ g = (χ g : ℂ) := by
    intro g
    have : ψ ((toUnits g : (RayClassGroup m)ˣ) : RayClassGroup m) =
        ((χ.comp (toUnits (G := RayClassGroup m)).symm.toMonoidHom) (toUnits g) : ℂˣ) :=
      MulChar.ofUnitHom_coe _ _
    simpa using this
  obtain ⟨Ψ, hpow, hne, hloc⟩ := exists_heckeChar m ψ
  have hn : Nat.card (RayClassGroup m) ≠ 0 := Nat.card_pos.ne'
  have hψne : ψ ≠ 1 := by
    intro h1
    apply hχ
    refine MonoidHom.ext fun g => Units.ext ?_
    rw [← hψ g, h1, MulChar.one_apply (Group.isUnit g)]
    rfl
  have hunit : Ψ.IsUnitary := isUnitary_of_pow_eq_one hn hpow
  have hnp : ∀ c : ℂ, Ψ ≠ HeckeCharacter.normPow K c := ne_normPow_of_pow_eq_one hn hpow (hne hψne)
  have hloc' : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite), Ψ.IsUnramifiedAt v ∧
      (Ψ.finiteComponent v (Analysis.ϖU v) : ℂ) = χ (rayClass m v hv) :=
    fun v hv => ⟨(hloc v hv).1, by rw [(hloc v hv).2, hψ]⟩
  have hshift : Ψ.shift = 0 := (shift_eq_zero_iff Ψ).mpr hunit
  set P : ℂ → ℂ := fun s => ∏ v ∈ badPrimes m, localL Ψ s v with hP
  let F : ℂ → ℂ := fun s => ∏ v ∈ badPrimes m, (if Ψ.IsUnramifiedAt v then (1 - rV Ψ s v) else 1)
  have hFd : Differentiable ℂ F := by
    refine Differentiable.fun_finsetProd (𝕜 := ℂ)
      (f := fun v s => if Ψ.IsUnramifiedAt v then (1 - rV Ψ s v) else 1) fun v _ => ?_
    by_cases hu : Ψ.IsUnramifiedAt v
    · simp only [hu, ite_true]
      refine (differentiable_const _).sub ?_
      unfold rV
      exact (differentiable_const _).mul
        (Differentiable.const_cpow (differentiable_id.neg)
          (Or.inl (Complex.ofReal_ne_zero.2 (normV_pos v).ne')))
    · simp only [hu, ite_false]
      exact differentiable_const _
  refine ⟨fun s => heckeLCont Ψ s * F s, ?_, ?_, ?_⟩
  · exact ((differentiable_heckeLCont hnp).mul hFd).differentiableOn
  · intro s hs
    have hs' : 1 < s.re + Ψ.shift := by simp [hshift, hs]
    have key := weberLSeries_mul_prod_eq_heckeL_complex m χ hfin Ψ hunit hloc' hs
    have hFP : F s * P s = 1 := by
      simp only [F, hP, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v _ => ?_
      unfold localL
      by_cases hu : Ψ.IsUnramifiedAt v
      · simp only [hu, ite_true]
        exact mul_inv_cancel₀ (one_sub_rV_ne_zero Ψ (by simp [hshift, hs.le]) v)
      · simp [hu]
    have hP0 : P s ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => localL_ne_zero Ψ (by simp [hshift, hs.le]) v
    show heckeLCont Ψ s * F s = weberLSeries m χ s
    rw [heckeLCont_eq Ψ hs', ← key]
    have : weberLSeries m χ s * P s * F s = weberLSeries m χ s * (F s * P s) := by ring
    simp only [hP] at this hFP
    rw [this, hFP, mul_one]
  · have hA0 : heckeLCont Ψ 1 ≠ 0 := heckeLCont_ne_zero_of_re_eq_one hunit hnp (by simp)
    have hF0 : F 1 ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => by
      by_cases hu : Ψ.IsUnramifiedAt v
      · simp only [hu, ite_true]
        exact one_sub_rV_ne_zero Ψ (by simp [hshift]) v
      · simp [hu]
    exact mul_ne_zero hA0 hF0

end NumberFieldKB.MilneCFT
