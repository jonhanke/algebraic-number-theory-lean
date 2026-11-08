import NumberFieldKB.GlobalZeta.Majorant

/-!
# Theta functions on the ideles and Tate's Riemann–Roch identity

$F$ is a number field. For a function $\Psi$ on $\mathbb A_F$ and an idele $g$,
$$\theta_\Psi(g) = \sum_{\gamma\in F}\Psi(g\gamma)$$
(`theta`). For a factorizable Schwartz–Bruhat function $\Phi$, QuadFormsKB's twisted adelic Poisson summation
(`adelicPoisson_smul`) is Tate's *Riemann–Roch theorem* (Cassels–Fröhlich Ch. XV, Thm. 4.2.1 [unverified locator]):
$$\theta_\Phi(g) = \|g\|^{-1}\,\theta_{\hat\Phi}(g^{-1})\qquad(\texttt{theta\_eq\_poisson}).$$

With $D$ the fundamental domain of $F^\times$ in $\mathbb A_F^1$ and $s(t)$ the section of the norm, the **theta
integral** of a Hecke character $\chi$ is
$$f_{\Psi,\chi}(t) = \int_D\chi(a\,s(t))\,\theta_\Psi(a\,s(t))\,d\mu^1(a)\qquad(\texttt{thetaInt}),$$
and Riemann–Roch gives its functional equation $f_{\Phi,\chi}(1/t) = t\,f_{\hat\Phi,\chi^{-1}}(t)$
(**`thetaInt_one_div`**), using that $\mu^1$ is inversion invariant and $D^{-1}$ is again a fundamental domain.

The constant term: $\int_D\chi(a\,g)\,d\mu^1(a) = 0$ if $\chi$ is not trivial on $\mathbb A_F^1$
(`setIntegral_onIdeles_eq_zero`), by translation invariance.
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Filter Topology Set
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical ENNReal NNReal nonZeroDivisors

namespace NumberFieldKB.GlobalZeta

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "V" => mixedSpace F

/-! ### Theta functions -/

/-- **The theta function** $\theta_\Psi(g) = \sum_{\gamma\in F}\Psi(g\gamma)$ of a function on the adeles. -/
def theta (Ψ : Adeles F → ℂ) (g : (Adeles F)ˣ) : ℂ := ∑' γ : F, Ψ ((g : Adeles F) * diagRing F γ)

/-- **Admissible functions**: majorized, with absolutely convergent theta series at every idele. -/
structure IsAdmissible (Ψ : Adeles F → ℂ) : Prop extends IsMajorized Ψ where
  summable : ∀ g : (Adeles F)ˣ, Summable fun γ : F => Ψ ((g : Adeles F) * diagRing F γ)

theorem coe_diagUnits (ξ : Fˣ) : ((diagUnits F ξ : (Adeles F)ˣ) : Adeles F) = diagRing F ξ := rfl

theorem theta_diagUnits_mul (Ψ : Adeles F → ℂ) (ξ : Fˣ) (g : (Adeles F)ˣ) :
    theta Ψ (diagUnits F ξ * g) = theta Ψ g := by
  unfold theta
  have h : ∀ γ : F, ((diagUnits F ξ * g : (Adeles F)ˣ) : Adeles F) * diagRing F γ =
      (g : Adeles F) * diagRing F ((ξ : F) * γ) := fun γ => by
    rw [Units.val_mul, coe_diagUnits, map_mul]; ring
  simp_rw [h]
  exact (Equiv.mulLeft₀ (ξ : F) ξ.ne_zero).tsum_eq fun γ => Ψ ((g : Adeles F) * diagRing F γ)

/-- $\theta_\Psi(g) = \Psi(0) + \sum_{\xi\in F^\times}\Psi(\xi g)$. -/
theorem theta_eq_add {Ψ : Adeles F → ℂ} {g : (Adeles F)ˣ}
    (hs : Summable fun γ : F => Ψ ((g : Adeles F) * diagRing F γ)) :
    theta Ψ g = Ψ 0 + ∑' ξ : Fˣ, Ψ ((diagUnits F ξ * g : (Adeles F)ˣ) : Adeles F) := by
  unfold theta
  rw [hs.tsum_eq_add_tsum_ite 0, map_zero, mul_zero]
  congr 1
  have hinj : Function.Injective (Units.val : Fˣ → F) := Units.val_injective
  rw [← hinj.tsum_eq (f := fun γ : F => if γ = 0 then 0 else Ψ ((g : Adeles F) * diagRing F γ)) fun γ hγ => by
    have : γ ≠ 0 := fun h => hγ (by simp [h])
    exact ⟨Units.mk0 γ this, rfl⟩]
  refine tsum_congr fun ξ => ?_
  rw [if_neg ξ.ne_zero, Units.val_mul, coe_diagUnits, mul_comm]

/-! ### Riemann–Roch: twisted Poisson summation -/

end

end GlobalZeta

open GlobalZeta

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "V" => mixedSpace F

namespace SchwartzBruhat

variable (Φ : SchwartzBruhat F)

theorem apply_mul_diagRing (g : (Adeles F)ˣ) (γ : F) :
    Φ ((g : Adeles F) * diagRing F γ) = Φ.fInf ((infPart g : V) * mixedEmbedding F γ) *
      ∏ᶠ v, Φ.fv v ((unitAt (finPart g) v : v.adicCompletion F) * algebraMap F _ γ) := rfl

theorem fourier_inv_mul_diagRing (g : (Adeles F)ˣ) (γ : F) :
    Φ.fourier (((g⁻¹ : (Adeles F)ˣ) : Adeles F) * diagRing F γ) =
      Analysis.fourierInf (Φ.fInf : V → ℂ) (((infPart g)⁻¹ : Vˣ) * mixedEmbedding F γ) *
        ∏ᶠ v, Analysis.fourierV v (Φ.fv v)
          (((unitAt (finPart g) v)⁻¹ : (v.adicCompletion F)ˣ) * algebraMap F _ γ) := rfl

theorem summable_theta (g : (Adeles F)ˣ) :
    Summable fun γ : F => Φ ((g : Adeles F) * diagRing F γ) :=
  summable_adelicPoisson_smul_lhs Φ.fv Φ.S Φ.isSchwartzBruhat Φ.eq_charO Φ.fInf g

theorem summable_theta_fourier (g : (Adeles F)ˣ) :
    Summable fun γ : F => Φ.fourier ((g : Adeles F) * diagRing F γ) := by
  have h := summable_adelicPoisson_smul_rhs Φ.fv Φ.S Φ.isSchwartzBruhat Φ.eq_charO Φ.fInf g⁻¹
  have e : ∀ γ : F, Φ.fourier ((g : Adeles F) * diagRing F γ) =
      Φ.fourier ((((g⁻¹)⁻¹ : (Adeles F)ˣ) : Adeles F) * diagRing F γ) := fun γ => by rw [inv_inv]
  simp_rw [e, fourier_inv_mul_diagRing]
  exact h

theorem isAdmissible : IsAdmissible (Φ : Adeles F → ℂ) := ⟨Φ.isMajorized, Φ.summable_theta⟩

theorem isAdmissible_fourier : IsAdmissible Φ.fourier := ⟨Φ.isMajorized_fourier, Φ.summable_theta_fourier⟩

/-- **Tate's Riemann–Roch theorem** (twisted adelic Poisson summation, QuadFormsKB `adelicPoisson_smul`):
$\sum_{\gamma\in F}\Phi(g\gamma) = \|g\|^{-1}\sum_{\gamma\in F}\hat\Phi(g^{-1}\gamma)$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.2, Thm. 4.2.1 [unverified locator] (the Riemann–Roch theorem)"]
theorem theta_eq_poisson (g : (Adeles F)ˣ) :
    theta (Φ : Adeles F → ℂ) g = ((ideleNorm F g)⁻¹ : ℂ) * theta Φ.fourier g⁻¹ := by
  unfold theta
  simp_rw [apply_mul_diagRing, fourier_inv_mul_diagRing]
  rw [adelicPoisson_smul Φ.fv Φ.S Φ.isSchwartzBruhat Φ.eq_charO Φ.fInf g, Complex.real_smul]
  push_cast
  rfl

end SchwartzBruhat

end

namespace GlobalZeta

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-! ### The theta integral -/

/-- The point $a\,s(t)$, $a\in\mathbb A_F^1$, $s(t)$ the section of the norm at $t$ (for $t>0$, $\|a\,s(t)\| = t$). -/
abbrev pt (a : ideleOne F) (t : ℝ) : (Adeles F)ˣ := (a : (Adeles F)ˣ) * sec F (Real.log t)

theorem ideleNorm_pt (a : ideleOne F) {t : ℝ} (ht : 0 < t) : ideleNorm F (pt a t) = t := by
  rw [pt, ideleNorm_mul, mem_ideleOne.mp a.2, one_mul, ideleNorm_sec, Real.exp_log ht]

/-- **The theta integral** $f_{\Psi,\chi}(t) = \int_D\chi(a\,s(t))\,\theta_\Psi(a\,s(t))\,d\mu^1(a)$. -/
def thetaInt (Ψ : Adeles F → ℂ) (χ : HeckeCharacter F) (t : ℝ) : ℂ :=
  ∫ a in ideleClassFD F, (χ.onIdeles (pt a t) : ℂ) * theta Ψ (pt a t) ∂muIdeleOne F

theorem coe_smul_ideleOne (γ : diagUnitsOne F) (a : ideleOne F) :
    ((γ • a : ideleOne F) : (Adeles F)ˣ) = ((γ : ideleOne F) : (Adeles F)ˣ) * a := rfl

/-- Elements of `diagUnitsOne F` are principal ideles. -/
theorem exists_diagUnits (γ : diagUnitsOne F) : ∃ ξ : Fˣ, ((γ : ideleOne F) : (Adeles F)ˣ) = diagUnits F ξ := by
  obtain ⟨ξ, hξ⟩ := Subgroup.mem_subgroupOf.mp γ.2
  exact ⟨ξ, hξ.symm⟩

/-- The integrand of the theta integral is $F^\times$-invariant. -/
theorem thetaIntegrand_smul (Ψ : Adeles F → ℂ) (χ : HeckeCharacter F) (g : (Adeles F)ˣ) (γ : diagUnitsOne F)
    (a : ideleOne F) :
    (χ.onIdeles ((γ • a : ideleOne F) * g) : ℂ) * theta Ψ ((γ • a : ideleOne F) * g) =
      (χ.onIdeles ((a : (Adeles F)ˣ) * g) : ℂ) * theta Ψ ((a : (Adeles F)ˣ) * g) := by
  obtain ⟨ξ, hξ⟩ := exists_diagUnits γ
  rw [coe_smul_ideleOne, hξ, mul_assoc, HeckeCharacter.onIdeles_diagUnits_mul, theta_diagUnits_mul]

/-- **The functional equation of the theta integral** (from Riemann–Roch):
$f_{\Phi,\chi}(1/t) = t\,f_{\hat\Phi,\chi^{-1}}(t)$ for $t>0$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.4 [unverified locator] (the theta integral and Riemann–Roch)"]
theorem thetaInt_one_div (Φ : SchwartzBruhat F) (χ : HeckeCharacter F) {t : ℝ} (ht : 0 < t) :
    thetaInt (Φ : Adeles F → ℂ) χ (1 / t) = t * thetaInt Φ.fourier χ⁻¹ t := by
  unfold thetaInt
  set u := Real.log t
  have hlog : Real.log (1 / t) = -u := by rw [one_div, Real.log_inv]
  set k : ideleOne F → ℂ := fun b =>
    (χ⁻¹.onIdeles ((b : (Adeles F)ˣ) * sec F u) : ℂ) * theta Φ.fourier ((b : (Adeles F)ˣ) * sec F u)
  have hk : ∀ (γ : diagUnitsOne F) b, k (γ • b) = k b := fun γ b =>
    thetaIntegrand_smul Φ.fourier χ⁻¹ (sec F u) γ b
  have hpt : ∀ a : ideleOne F, (χ.onIdeles (pt a (1 / t)) : ℂ) * theta (Φ : Adeles F → ℂ) (pt a (1 / t)) =
      t * k a⁻¹ := by
    intro a
    have hg : pt a (1 / t) = (a : (Adeles F)ˣ) * (sec F u)⁻¹ := by rw [pt, hlog, sec_neg]
    have hinv : (pt a (1 / t))⁻¹ = ((a⁻¹ : ideleOne F) : (Adeles F)ˣ) * sec F u := by
      rw [hg, mul_inv, inv_inv, Subgroup.coe_inv, mul_comm]
    have hnorm : ideleNorm F (pt a (1 / t)) = 1 / t := ideleNorm_pt a (by positivity)
    rw [SchwartzBruhat.theta_eq_poisson, hnorm]
    simp only [k]
    rw [HeckeCharacter.inv_onIdeles, ← hinv, map_inv, Units.val_inv_eq_inv_val, inv_inv]
    simp only [one_div, Complex.ofReal_inv, inv_inv]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  exact setIntegral_fd_inv hk

/-! ### The constant term -/

/-- **Orthogonality**: if $\chi$ is not trivial on $\mathbb A_F^1$, then $\int_D\chi(a\,g)\,d\mu^1(a) = 0$. -/
theorem setIntegral_onIdeles_eq_zero (χ : HeckeCharacter F) (hχ : ∃ b : ideleOne F, χ.onIdeles b ≠ 1)
    (g : (Adeles F)ˣ) : ∫ a in ideleClassFD F, (χ.onIdeles ((a : (Adeles F)ˣ) * g) : ℂ) ∂muIdeleOne F = 0 := by
  obtain ⟨b, hb⟩ := hχ
  set J := ∫ a in ideleClassFD F, (χ.onIdeles ((a : (Adeles F)ˣ) * g) : ℂ) ∂muIdeleOne F
  have hk : ∀ (γ : diagUnitsOne F) (a : ideleOne F),
      (χ.onIdeles ((γ • a : ideleOne F) * g) : ℂ) = (χ.onIdeles ((a : (Adeles F)ˣ) * g) : ℂ) := by
    intro γ a
    obtain ⟨ξ, hξ⟩ := exists_diagUnits γ
    rw [coe_smul_ideleOne, hξ, mul_assoc, HeckeCharacter.onIdeles_diagUnits_mul]
  have htr := setIntegral_fd_mul_left (k := fun a : ideleOne F => (χ.onIdeles ((a : (Adeles F)ˣ) * g) : ℂ)) hk b
  have h2 : ∫ a in ideleClassFD F, (χ.onIdeles (((b * a : ideleOne F) : (Adeles F)ˣ) * g) : ℂ) ∂muIdeleOne F =
      (χ.onIdeles b : ℂ) * J := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [Subgroup.coe_mul, mul_assoc, map_mul, Units.val_mul]
  rw [h2] at htr
  have h3 : ((χ.onIdeles b : ℂ) - 1) * J = 0 := by rw [sub_mul, htr, one_mul, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (Units.ext (sub_eq_zero.mp h)) hb
  · exact h

/-- The volume $\mu^1(D)$ of the norm-one idele class group is finite: it is $\rho_F$ (QuadFormsKB
`muIdeleClass_univ_eq_residue`). -/
theorem muIdeleOne_fd_eq_residue : muIdeleOne F (ideleClassFD F) = ENNReal.ofReal (dedekindZeta_residue F) := by
  rw [← muIdeleClass_univ isFundamentalDomain_ideleClassFD, QFPort.muIdeleClass_univ_eq_residue]

theorem muIdeleOne_fd_lt_top : muIdeleOne F (ideleClassFD F) < ⊤ := by
  rw [muIdeleOne_fd_eq_residue]; exact ENNReal.ofReal_lt_top

/-- **$\operatorname{vol}(F^\times\backslash\mathbb A_F^1) = \rho_F$**, the residue of $\zeta_F$ at $s = 1$. -/
theorem measureReal_fd : (muIdeleOne F).real (ideleClassFD F) = dedekindZeta_residue F := by
  rw [Measure.real, muIdeleOne_fd_eq_residue, ENNReal.toReal_ofReal (dedekindZeta_residue_pos F).le]

end

end NumberFieldKB.GlobalZeta
