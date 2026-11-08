import NumberFieldKB.GlobalZeta.Decay
import NumberFieldKB.HeckeCharacter.ArchimedeanCharacters
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Tate's main theorem: continuation and functional equation of the global zeta integral

$F$ is a number field, $\Phi$ a factorizable Schwartz–Bruhat function on $\mathbb A_F$, $\hat\Phi$ its Fourier
transform, $\chi$ a Hecke character with shift $\sigma$ ($|\chi| = \|\cdot\|^\sigma$), $\rho_F$ the residue of the
Dedekind zeta function at $s = 1$ (= the volume of $F^\times\backslash\mathbb A_F^1$ for Tate's measure).

**The Mellin argument** (`fePair`). For a normalized character (`IsNormalized`: $\chi = 1$, or $\chi$ unitary and
not trivial on $\mathbb A_F^1$) the theta integrals $f = f_{\Phi,\chi}$, $g = f_{\hat\Phi,\chi^{-1}}$ form a weak
FE-pair in the sense of Mathlib's `WeakFEPair` (`NumberTheory/LSeries/AbstractFuncEq.lean`), with weight $k = 1$,
root number $\varepsilon = 1$ and constant terms $\Phi(0)\rho_F$, $\hat\Phi(0)\rho_F$ (for $\chi = 1$) or $0$:
Riemann–Roch gives $f(1/t) = t\,g(t)$ (`thetaInt_one_div`), and `Decay.lean` gives local integrability and rapid
decay. Mathlib's theorems on FE-pairs then give the continuation.

**Main theorem** for every Hecke character (`globalZetaCont Φ χ`, the continuation):
* `globalZetaCont_eq` : it equals $Z(\Phi,\chi,s)$ for $\operatorname{Re}s+\sigma>1$;
* `globalZetaCont_one_sub` (**the functional equation**): $Z(\Phi,\chi,1-s)$ continued equals
  $Z(\hat\Phi,\chi^{-1},s)$ for $\operatorname{Re}s-\sigma>1$, so the two zeta integrals are the same meromorphic
  function, $Z(\Phi,\chi,s) = Z(\hat\Phi,\chi^{-1},1-s)$;
* `meromorphic_globalZetaCont`: it is meromorphic on $\mathbb C$;
* `differentiable_globalZetaCont`: it is entire unless $\chi = \|\cdot\|^{c}$ for some $c\in\mathbb C$
  (for unitary $\chi$: $c = i\tau$);
* `differentiableAt_globalZetaCont_normPow`, `tendsto_globalZetaCont_normPow_residue_one`,
  `tendsto_globalZetaCont_normPow_residue_zero`: for $\chi = \|\cdot\|^c$ it is holomorphic away from $s = -c$ and
  $s = 1-c$, with simple poles there and residues $-\Phi(0)\rho_F$ and $\hat\Phi(0)\rho_F$.

Tate's thesis, Cassels–Fröhlich Ch. XV, Main Theorem 4.4.1 [unverified locator].
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Filter Topology Set Asymptotics
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical ENNReal NNReal nonZeroDivisors

namespace NumberFieldKB.GlobalZeta

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

/-! ### The FE-pair of a normalized character -/

/-- **The FE-pair** $(f_{\Phi,\chi}, f_{\hat\Phi,\chi^{-1}})$ of theta integrals, for a normalized character: weight $1$,
root number $1$. -/
def fePair (Φ : SchwartzBruhat F) (χ : HeckeCharacter F) (hχ : IsNormalized χ) : WeakFEPair ℂ where
  f := thetaInt (Φ : Adeles F → ℂ) χ
  g := thetaInt Φ.fourier χ⁻¹
  k := 1
  ε := 1
  f₀ := constTerm (Φ : Adeles F → ℂ) χ
  g₀ := constTerm Φ.fourier χ⁻¹
  hf_int := locallyIntegrableOn_thetaInt Φ.isAdmissible hχ
  hg_int := locallyIntegrableOn_thetaInt Φ.isAdmissible_fourier hχ.inv
  hk := one_pos
  hε := one_ne_zero
  h_feq := fun x hx => by
    rw [thetaInt_one_div Φ χ hx, Real.rpow_one, one_mul, smul_eq_mul]
  hf_top := isBigO_thetaInt_sub Φ.isAdmissible hχ
  hg_top := isBigO_thetaInt_sub Φ.isAdmissible_fourier hχ.inv

variable (Φ : SchwartzBruhat F)

/-- For $\operatorname{Re}s>1$, the completed function of the FE-pair is the zeta integral. -/
theorem fePair_Λ_eq {χ : HeckeCharacter F} (hχ : IsNormalized χ) {s : ℂ} (hs : 1 < s.re) :
    (fePair Φ χ hχ).Λ s = globalZeta (Φ : Adeles F → ℂ) χ s := by
  rw [globalZeta_eq_mellin Φ.isAdmissible hχ hs]
  exact ((fePair Φ χ hχ).hasMellin (by simpa [fePair] using hs)).2.symm

/-- For $\operatorname{Re}s>1$, the completed function of the dual pair is the zeta integral of $\hat\Phi$, $\chi^{-1}$. -/
theorem fePair_symm_Λ_eq {χ : HeckeCharacter F} (hχ : IsNormalized χ) {s : ℂ} (hs : 1 < s.re) :
    (fePair Φ χ hχ).symm.Λ s = globalZeta Φ.fourier χ⁻¹ s := by
  rw [globalZeta_eq_mellin Φ.isAdmissible_fourier hχ.inv hs]
  exact ((fePair Φ χ hχ).symm.hasMellin (by simpa [fePair] using hs)).2.symm

theorem fePair_functional_equation {χ : HeckeCharacter F} (hχ : IsNormalized χ) (s : ℂ) :
    (fePair Φ χ hχ).Λ (1 - s) = (fePair Φ χ hχ).symm.Λ s := by
  have h := (fePair Φ χ hχ).functional_equation s
  simpa [fePair] using h

theorem constTerm_inv_of_ne_one {Ψ : Adeles F → ℂ} {χ : HeckeCharacter F} (h : χ ≠ 1) : constTerm Ψ χ⁻¹ = 0 := by
  rw [constTerm, if_neg (fun h' => h (inv_eq_one.mp h'))]

theorem constTerm_of_ne_one {Ψ : Adeles F → ℂ} {χ : HeckeCharacter F} (h : χ ≠ 1) : constTerm Ψ χ = 0 := by
  rw [constTerm, if_neg h]

/-! ### Characters trivial on the norm-one ideles -/

/-- $\|\cdot\|^c$ is trivial on $\mathbb A_F^1$. -/
theorem normPow_onIdeles_ideleOne (c : ℂ) (b : ideleOne F) : (HeckeCharacter.normPow F c).onIdeles b = 1 := by
  apply Units.ext
  rw [HeckeCharacter.normPow_onIdeles, mem_ideleOne.mp b.2, Complex.ofReal_one, Complex.one_cpow, Units.val_one]

theorem onIdeles_injective {χ ψ : HeckeCharacter F} (h : ∀ g, χ.onIdeles g = ψ.onIdeles g) : χ = ψ := by
  ext c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  have := h (Ideles.ideleGroupEquiv F x)
  rw [HeckeCharacter.onIdeles_apply, HeckeCharacter.onIdeles_apply, ContinuousMulEquiv.symm_apply_apply] at this
  rw [this]

/-- Every idele is $a\,s(e^u)$ with $a\in\mathbb A_F^1$, $u = \log\|g\|$. -/
theorem mul_sec_inv_mem_ideleOne (g : (Adeles F)ˣ) :
    g * (sec F (Real.log (ideleNorm F g)))⁻¹ ∈ ideleOne F := by
  rw [mem_ideleOne, ideleNorm_mul, ideleNorm_inv, ideleNorm_sec, Real.exp_log (ideleNorm_pos g),
    mul_inv_cancel₀ (ideleNorm_pos g).ne']

/-- **A Hecke character trivial on $\mathbb A_F^1$ is a power of the norm**: $\chi = \|\cdot\|^c$. -/
theorem exists_eq_normPow_of_ideleOne {χ : HeckeCharacter F} (h : ∀ b : ideleOne F, χ.onIdeles b = 1) :
    ∃ c : ℂ, χ = HeckeCharacter.normPow F c := by
  obtain ⟨c, hc⟩ := HeckeCharacters.exists_eq_exp_mul_of_continuous (fun u => χ.onIdeles (sec F u))
    (χ.continuous_onIdeles.comp continuous_sec) (by rw [sec_zero, map_one])
    (fun a b => by rw [sec_add, map_mul])
  refine ⟨c, onIdeles_injective fun g => Units.ext ?_⟩
  have hg : g = (g * (sec F (Real.log (ideleNorm F g)))⁻¹) * sec F (Real.log (ideleNorm F g)) := by group
  have hχg : χ.onIdeles g = χ.onIdeles (sec F (Real.log (ideleNorm F g))) := by
    conv_lhs => rw [hg]
    rw [map_mul, h ⟨_, mul_sec_inv_mem_ideleOne g⟩, one_mul]
  rw [hχg, hc, HeckeCharacter.normPow_onIdeles,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ideleNorm_pos g).ne'),
    ← Complex.ofReal_log (ideleNorm_pos g).le, mul_comm]

/-- The exponent of a power of the norm is unique. -/
theorem normPow_injective {c c' : ℂ} (h : HeckeCharacter.normPow F c = HeckeCharacter.normPow F c') : c = c' := by
  refine HeckeCharacters.eq_of_forall_exp_mul_eq fun u => ?_
  have := congrArg (fun χ : HeckeCharacter F => (χ.onIdeles (sec F u) : ℂ)) h
  simp only [HeckeCharacter.normPow_onIdeles, ideleNorm_sec] at this
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp] at this
  rw [mul_comm c, mul_comm c']
  exact this

theorem unitaryPart_onIdeles_ideleOne (χ : HeckeCharacter F) (b : ideleOne F) :
    χ.unitaryPart.onIdeles b = χ.onIdeles b := by
  apply Units.ext
  rw [HeckeCharacter.unitaryPart, HeckeCharacter.mul_onIdeles, HeckeCharacter.normPow_onIdeles,
    mem_ideleOne.mp b.2, Complex.ofReal_one, Complex.one_cpow, mul_one]

/-- **The dichotomy**: a Hecke character is either $\|\cdot\|^c$, or its unitary part is not trivial on $\mathbb A_F^1$. -/
theorem isNormalized_unitaryPart {χ : HeckeCharacter F} (h : ∀ c : ℂ, χ ≠ HeckeCharacter.normPow F c) :
    IsNormalized χ.unitaryPart := by
  refine ⟨χ.isUnitary_unitaryPart, Or.inr ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := exists_eq_normPow_of_ideleOne (χ := χ) fun b => by
    rw [← unitaryPart_onIdeles_ideleOne, hcon b]
  exact h c hc

theorem isNormalized_one : IsNormalized (1 : HeckeCharacter F) :=
  ⟨fun (c : IdeleClassGroup (𝓞 F) F) => by
    show ‖((1 : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_one, norm_one], Or.inl rfl⟩

/-! ### Zeta integrals of twisted characters -/

theorem globalZeta_mul_normPow (Ψ : Adeles F → ℂ) (χ : HeckeCharacter F) (c s : ℂ) :
    globalZeta Ψ (χ * HeckeCharacter.normPow F c) s = globalZeta Ψ χ (s + c) := by
  unfold globalZeta
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [globalZetaIntegrand, HeckeCharacter.mul_onIdeles, HeckeCharacter.normPow_onIdeles]
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ideleNorm_pos g).ne')]
  ring

theorem globalZeta_normPow (Ψ : Adeles F → ℂ) (c s : ℂ) :
    globalZeta Ψ (HeckeCharacter.normPow F c) s = globalZeta Ψ 1 (s + c) := by
  unfold globalZeta
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [globalZetaIntegrand, HeckeCharacter.one_onIdeles, HeckeCharacter.normPow_onIdeles, Units.val_one]
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ideleNorm_pos g).ne')]
  ring

theorem globalZeta_inv_mul_normPow (Ψ : Adeles F → ℂ) (χ : HeckeCharacter F) (c s : ℂ) :
    globalZeta Ψ (χ * HeckeCharacter.normPow F c)⁻¹ s = globalZeta Ψ χ⁻¹ (s - c) := by
  unfold globalZeta
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [globalZetaIntegrand, HeckeCharacter.inv_onIdeles, HeckeCharacter.mul_onIdeles,
    HeckeCharacter.normPow_onIdeles]
  have hx : ((ideleNorm F g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ideleNorm_pos g).ne'
  rw [Complex.cpow_sub _ _ hx, mul_inv]
  field_simp

theorem globalZeta_inv_normPow (Ψ : Adeles F → ℂ) (c s : ℂ) :
    globalZeta Ψ (HeckeCharacter.normPow F c)⁻¹ s = globalZeta Ψ 1 (s - c) := by
  unfold globalZeta
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [globalZetaIntegrand, HeckeCharacter.inv_onIdeles, HeckeCharacter.one_onIdeles,
    HeckeCharacter.normPow_onIdeles, Units.val_one]
  have hx : ((ideleNorm F g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ideleNorm_pos g).ne'
  rw [Complex.cpow_sub _ _ hx]
  field_simp

theorem globalZeta_inv_one (Ψ : Adeles F → ℂ) (s : ℂ) :
    globalZeta Ψ (1 : HeckeCharacter F)⁻¹ s = globalZeta Ψ 1 s := by
  unfold globalZeta
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [globalZetaIntegrand, HeckeCharacter.inv_onIdeles, HeckeCharacter.one_onIdeles, Units.val_one, inv_one]

/-! ### The continuation for every Hecke character -/

open Classical in
/-- **The continuation of the global zeta integral** $Z(\Phi,\chi,s)$ to $s\in\mathbb C$. If $\chi = \|\cdot\|^c$ it is
$\Lambda_1(s + c)$, with $\Lambda_1$ the completed function of the FE-pair of the trivial character; otherwise it is
$\Lambda_{\chi_0}(s+\sigma)$, with $\chi = \chi_0\|\cdot\|^\sigma$ and $\chi_0$ unitary, not trivial on $\mathbb A_F^1$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Main Theorem 4.4.1 [unverified locator] (analytic continuation of ζ(f, c))"]
def globalZetaCont (χ : HeckeCharacter F) (s : ℂ) : ℂ :=
  if h : ∃ c : ℂ, χ = HeckeCharacter.normPow F c then (fePair Φ 1 isNormalized_one).Λ (s + h.choose)
  else (fePair Φ χ.unitaryPart (isNormalized_unitaryPart (not_exists.mp h))).Λ (s + χ.shift)

theorem globalZetaCont_normPow (c s : ℂ) :
    globalZetaCont Φ (HeckeCharacter.normPow F c) s = (fePair Φ 1 isNormalized_one).Λ (s + c) := by
  have h : ∃ c' : ℂ, HeckeCharacter.normPow F c = HeckeCharacter.normPow F c' := ⟨c, rfl⟩
  rw [globalZetaCont, dif_pos h, ← normPow_injective h.choose_spec]

theorem globalZetaCont_of_ne {χ : HeckeCharacter F} (h : ∀ c : ℂ, χ ≠ HeckeCharacter.normPow F c) (s : ℂ) :
    globalZetaCont Φ χ s = (fePair Φ χ.unitaryPart (isNormalized_unitaryPart h)).Λ (s + χ.shift) := by
  rw [globalZetaCont, dif_neg (not_exists.mpr h)]

/-- **The continuation agrees with the zeta integral** where the integral converges: $\operatorname{Re}s+\sigma>1$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Main Theorem 4.4.1 [unverified locator]"]
theorem globalZetaCont_eq (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re + χ.shift) :
    globalZetaCont Φ χ s = globalZeta (Φ : Adeles F → ℂ) χ s := by
  by_cases h : ∃ c : ℂ, χ = HeckeCharacter.normPow F c
  · obtain ⟨c, rfl⟩ := h
    rw [globalZetaCont_normPow, fePair_Λ_eq Φ isNormalized_one, globalZeta_normPow]
    simpa using hs
  · push Not at h
    rw [globalZetaCont_of_ne Φ h, fePair_Λ_eq Φ _ (by simpa using hs)]
    conv_rhs => rw [← χ.unitaryPart_mul_normPow_shift]
    rw [globalZeta_mul_normPow]

/-- **The functional equation** $Z(\Phi,\chi,s) = Z(\hat\Phi,\chi^{-1},1-s)$: the continuation of $Z(\Phi,\chi,\cdot)$ at
$1-s$ equals the zeta integral $Z(\hat\Phi,\chi^{-1},s)$ wherever the latter converges, $\operatorname{Re}s-\sigma>1$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Main Theorem 4.4.1 [unverified locator] (ζ(f, c) = ζ(f̂, ĉ))"]
theorem globalZetaCont_one_sub (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re - χ.shift) :
    globalZetaCont Φ χ (1 - s) = globalZeta Φ.fourier χ⁻¹ s := by
  by_cases h : ∃ c : ℂ, χ = HeckeCharacter.normPow F c
  · obtain ⟨c, rfl⟩ := h
    rw [globalZetaCont_normPow, show 1 - s + c = 1 - (s - c) by ring, fePair_functional_equation,
      fePair_symm_Λ_eq Φ isNormalized_one (by simpa [sub_eq_add_neg] using hs), globalZeta_inv_normPow,
      globalZeta_inv_one]
  · push Not at h
    rw [globalZetaCont_of_ne Φ h, show 1 - s + (χ.shift : ℂ) = 1 - (s - χ.shift) by ring,
      fePair_functional_equation, fePair_symm_Λ_eq Φ _ (by simpa using hs)]
    conv_rhs => rw [← χ.unitaryPart_mul_normPow_shift]
    rw [globalZeta_inv_mul_normPow]

/-- **Entire**: unless $\chi$ is a power of the norm, the continuation is an entire function. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Main Theorem 4.4.1 [unverified locator] (no poles unless c = |·|^s)"]
theorem differentiable_globalZetaCont {χ : HeckeCharacter F} (h : ∀ c : ℂ, χ ≠ HeckeCharacter.normPow F c) :
    Differentiable ℂ (globalZetaCont Φ χ) := by
  have hne : χ.unitaryPart ≠ 1 := fun h1 => by
    obtain ⟨c, hc⟩ := exists_eq_normPow_of_ideleOne (χ := χ) fun b => by
      rw [← unitaryPart_onIdeles_ideleOne, h1]; rfl
    exact h c hc
  have hfun : globalZetaCont Φ χ = fun s =>
      (fePair Φ χ.unitaryPart (isNormalized_unitaryPart h)).Λ (s + χ.shift) :=
    funext (globalZetaCont_of_ne Φ h)
  rw [hfun]
  refine fun s => ((fePair Φ χ.unitaryPart _).differentiableAt_Λ (Or.inr ?_) (Or.inr ?_)).comp s
    ((differentiableAt_id).add_const _)
  · exact constTerm_of_ne_one hne
  · exact constTerm_inv_of_ne_one hne

/-- **Holomorphy away from the poles** for $\chi = \|\cdot\|^c$: away from $s = -c$ and $s = 1 - c$. -/
theorem differentiableAt_globalZetaCont_normPow (c : ℂ) {s : ℂ} (h0 : s ≠ -c) (h1 : s ≠ 1 - c) :
    DifferentiableAt ℂ (globalZetaCont Φ (HeckeCharacter.normPow F c)) s := by
  have hfun : globalZetaCont Φ (HeckeCharacter.normPow F c) = fun s => (fePair Φ 1 isNormalized_one).Λ (s + c) :=
    funext (globalZetaCont_normPow Φ c)
  rw [hfun]
  refine ((fePair Φ 1 isNormalized_one).differentiableAt_Λ (Or.inl ?_) (Or.inl ?_)).comp s
    ((differentiableAt_id).add_const _)
  · intro h; apply h0; linear_combination h
  · intro h; apply h1; simp only [fePair, Complex.ofReal_one] at h; linear_combination h

theorem tendsto_add_const_nhdsNE (a c : ℂ) : Tendsto (fun s => s + c) (𝓝[≠] a) (𝓝[≠] (a + c)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun s hs => ?_⟩
  · exact ((continuous_id.add continuous_const).tendsto a).mono_left nhdsWithin_le_nhds
  · simpa using hs

/-- **The residue at $s = 1 - c$** for $\chi = \|\cdot\|^c$: $\hat\Phi(0)\,\rho_F$, with $\rho_F = \operatorname{vol}(F^\times\backslash\mathbb A_F^1)$
the residue of $\zeta_F$ at $1$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Main Theorem 4.4.1 [unverified locator] (residue κ f̂(0) at s = 1 - c)"]
theorem tendsto_globalZetaCont_normPow_residue_one (c : ℂ) :
    Tendsto (fun s => (s - (1 - c)) * globalZetaCont Φ (HeckeCharacter.normPow F c) s) (𝓝[≠] (1 - c))
      (𝓝 (Φ.fourier 0 * dedekindZeta_residue F)) := by
  have h := (fePair Φ 1 isNormalized_one).Λ_residue_k
  have hk : (((fePair Φ 1 isNormalized_one).k : ℝ) : ℂ) = 1 := by simp [fePair]
  have hg₀ : (fePair Φ 1 isNormalized_one).g₀ = Φ.fourier 0 * dedekindZeta_residue F := by
    simp only [fePair, constTerm]
    split_ifs with hh
    · rfl
    · exact (hh (by simp)).elim
  rw [hk, hg₀, show (fePair Φ 1 isNormalized_one).ε = 1 from rfl, one_smul] at h
  have ht := tendsto_add_const_nhdsNE (1 - c) c
  rw [sub_add_cancel] at ht
  have hc := h.comp ht
  refine hc.congr fun s => ?_
  simp only [Function.comp_apply, smul_eq_mul, globalZetaCont_normPow]
  ring_nf

/-- **The residue at $s = -c$** for $\chi = \|\cdot\|^c$: $-\Phi(0)\,\rho_F$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Main Theorem 4.4.1 [unverified locator] (residue −κ f(0) at s = −c)"]
theorem tendsto_globalZetaCont_normPow_residue_zero (c : ℂ) :
    Tendsto (fun s => (s + c) * globalZetaCont Φ (HeckeCharacter.normPow F c) s) (𝓝[≠] (-c))
      (𝓝 (-((Φ : Adeles F → ℂ) 0 * dedekindZeta_residue F))) := by
  have h := (fePair Φ 1 isNormalized_one).Λ_residue_zero
  have hf₀ : (fePair Φ 1 isNormalized_one).f₀ = (Φ : Adeles F → ℂ) 0 * dedekindZeta_residue F := by
    simp only [fePair, constTerm]
    split_ifs with hh
    · rfl
    · exact absurd trivial hh
  rw [hf₀] at h
  have ht := tendsto_add_const_nhdsNE (-c) c
  rw [neg_add_cancel] at ht
  have hc := h.comp ht
  refine hc.congr fun s => ?_
  simp only [Function.comp_apply, smul_eq_mul, globalZetaCont_normPow]

/-- **Meromorphy**: the continuation is a meromorphic function on $\mathbb C$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Main Theorem 4.4.1 [unverified locator]"]
theorem meromorphic_globalZetaCont (χ : HeckeCharacter F) : Meromorphic (globalZetaCont Φ χ) := by
  have hP : ∀ (P : WeakFEPair ℂ) (c : ℂ), Meromorphic fun s => P.Λ (s + c) := by
    intro P c x
    have hΛ : Meromorphic P.Λ := by
      intro y
      have h0 : MeromorphicAt P.Λ₀ y := (P.differentiable_Λ₀.analyticAt y).meromorphicAt
      have h1 : MeromorphicAt (fun s : ℂ => (1 / s) • P.f₀) y :=
        ((MeromorphicAt.const 1 y).div (MeromorphicAt.id y)).smul (MeromorphicAt.const _ y)
      have h2 : MeromorphicAt (fun s : ℂ => (P.ε / (P.k - s)) • P.g₀) y :=
        ((MeromorphicAt.const _ y).div ((MeromorphicAt.const _ y).sub (MeromorphicAt.id y))).smul
          (MeromorphicAt.const _ y)
      exact (h0.sub h1).sub h2
    exact (hΛ (x + c)).comp_analyticAt (g := fun s => s + c) (by fun_prop)
  by_cases h : ∃ c : ℂ, χ = HeckeCharacter.normPow F c
  · obtain ⟨c, rfl⟩ := h
    have hfun : globalZetaCont Φ (HeckeCharacter.normPow F c) = fun s => (fePair Φ 1 isNormalized_one).Λ (s + c) :=
      funext (globalZetaCont_normPow Φ c)
    rw [hfun]; exact hP _ _
  · push Not at h
    exact fun x => ((differentiable_globalZetaCont Φ h).analyticAt x).meromorphicAt

end

end NumberFieldKB.GlobalZeta
