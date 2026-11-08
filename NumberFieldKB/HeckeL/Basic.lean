import NumberFieldKB.HeckeL.Arch
import QuadFormsKB.Analysis.NFEulerProduct

/-!
# Hecke L-functions: the Euler product and the global zeta integral

$F$ is a number field and $\chi$ a Hecke character with shift $\sigma$ ($|\chi| = \|\cdot\|^\sigma$). At a finite
place $v$ where $\chi$ is unramified, $\chi_v(\varpi_v)$ does not depend on the uniformizer $\varpi_v$.

* **`localL χ s v`** $= (1-\chi_v(\varpi_v)N(v)^{-s})^{-1}$ if $\chi$ is unramified at $v$, and $1$ otherwise.
* **`heckeL χ s`** $= L(s,\chi) = \prod_{v\text{ finite, unramified}}(1-\chi_v(\varpi_v)N(v)^{-s})^{-1}$, the Hecke
  $L$-function (without archimedean factors). For $\operatorname{Re}s+\sigma>1$ the product converges absolutely
  (`hasProd_heckeL`, `HasProd`: unconditional convergence) and is nonzero (`heckeL_ne_zero`).
* **`stdPhi χ f`**: the standard test function $\Phi_\chi = f\otimes\bigotimes_vf_v$ with $f_v = \mathbf 1_{\mathcal O_v}$ at the
  unramified places and $f_v = \mathbf 1_{1+\mathfrak p_v^{a_v}}$ at the ramified ones ($a_v$ the conductor exponent).
* **`globalZeta_stdPhi`**: for $\operatorname{Re}s+\sigma>1$,
  $$Z(\Phi_\chi,\chi,s) = Z_\infty(f,\chi,s)\cdot C_\chi\cdot L(s,\chi),\qquad
  C_\chi = \prod_{v\text{ unramified}}N(\mathfrak d_v)^{-1/2}\prod_{v\text{ ramified}}\operatorname{vol}^\times(U_v^{(a_v)})>0$$
  (`stdConst`, a finite product, `stdConst_pos`): the $L$-function is the global zeta integral up to explicit local
  factors (Tate's thesis, Cassels–Fröhlich Ch. XV, §4.4 [unverified locator]).
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Filter Set
open QuadFormsKB QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical ENNReal NNReal

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

open GlobalZeta LocalZeta

/-! ### The Euler factors -/

/-- $N(v)$ as a real number. -/
abbrev normV (v : HeightOneSpectrum (𝓞 F)) : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

theorem two_le_normV (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ normV v := by
  exact_mod_cast QuadFormsKB.NFEuler.two_le_normP v

theorem normV_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < normV v := by
  have := two_le_normV v; linarith

/-- **The local Euler factor** of $L(s,\chi)$ at a finite place: $(1-\chi_v(\varpi_v)N(v)^{-s})^{-1}$ if $\chi$ is
unramified at $v$, $1$ otherwise. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.4 [unverified locator] (the L-function Π_p (1 − c(p))^{-1})"]
def localL (χ : HeckeCharacter F) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if χ.IsUnramifiedAt v then (1 - rV χ s v)⁻¹ else 1

/-- **The Hecke $L$-function** $L(s,\chi) = \prod_{v\text{ unramified}}(1-\chi_v(\varpi_v)N(v)^{-s})^{-1}$ (finite places
only). It converges for $\operatorname{Re}s+\sigma>1$ (`hasProd_heckeL`); elsewhere it is the junk value of `tprod`
and the continuation is `heckeLCont` (`Completed.lean`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.4 [unverified locator] (Hecke's L-function L(s, χ))"]
def heckeL (χ : HeckeCharacter F) (s : ℂ) : ℂ := ∏' v, localL χ s v

/-- $|\chi_v(\varpi_v)N(v)^{-s}| = N(v)^{-(\operatorname{Re}s+\sigma)}$. -/
theorem norm_rV (χ : HeckeCharacter F) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    ‖rV χ s v‖ = normV v ^ (-(s.re + χ.shift)) := by
  rw [rV, ← modV_cpow, norm_mul, HeckeCharacter.norm_finiteComponent_eq_rpow,
    Complex.norm_cpow_eq_rpow_re_of_pos (modV_pos' v), show (distribHaarChar (v.adicCompletion F)
      (Analysis.ϖU v) : ℝ) = Analysis.modV v from rfl, ← Real.rpow_add (modV_pos' v), Analysis.modV_eq,
    Real.inv_rpow (Nat.cast_nonneg _), ← Real.rpow_neg (Nat.cast_nonneg _)]
  congr 1
  ring

theorem norm_rV_le_half (χ : HeckeCharacter F) {s : ℂ} (hs : 1 ≤ s.re + χ.shift) (v : HeightOneSpectrum (𝓞 F)) :
    ‖rV χ s v‖ ≤ 1 / 2 := by
  rw [norm_rV]
  exact QuadFormsKB.NFEuler.rpow_neg_normP_le_half v hs

theorem one_sub_rV_ne_zero (χ : HeckeCharacter F) {s : ℂ} (hs : 1 ≤ s.re + χ.shift) (v : HeightOneSpectrum (𝓞 F)) :
    1 - rV χ s v ≠ 0 := by
  intro h
  have h1 : rV χ s v = 1 := (sub_eq_zero.mp h).symm
  have := norm_rV_le_half χ hs v
  rw [h1, norm_one] at this
  norm_num at this

theorem localL_ne_zero (χ : HeckeCharacter F) {s : ℂ} (hs : 1 ≤ s.re + χ.shift) (v : HeightOneSpectrum (𝓞 F)) :
    localL χ s v ≠ 0 := by
  unfold localL
  split_ifs
  · exact inv_ne_zero (one_sub_rV_ne_zero χ hs v)
  · exact one_ne_zero

/-- $\|L_v - 1\|\le 2N(v)^{-(\operatorname{Re}s+\sigma)}$ for $\operatorname{Re}s+\sigma\ge1$. -/
theorem norm_localL_sub_one_le (χ : HeckeCharacter F) {s : ℂ} (hs : 1 ≤ s.re + χ.shift)
    (v : HeightOneSpectrum (𝓞 F)) : ‖localL χ s v - 1‖ ≤ 2 * normV v ^ (-(s.re + χ.shift)) := by
  have hpos : 0 ≤ normV v ^ (-(s.re + χ.shift)) := Real.rpow_nonneg (normV_pos v).le _
  unfold localL
  split_ifs
  · have hne := one_sub_rV_ne_zero χ hs v
    have h12 := norm_rV_le_half χ hs v
    have hlow : 1 / 2 ≤ ‖1 - rV χ s v‖ := by
      have := norm_sub_norm_le (1 : ℂ) (rV χ s v)
      rw [norm_one] at this
      linarith
    rw [show (1 - rV χ s v)⁻¹ - 1 = rV χ s v / (1 - rV χ s v) by field_simp; ring, norm_div, ← norm_rV χ s v]
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (rV χ s v)]
  · simp only [sub_self, norm_zero]; positivity

/-- **The Euler product converges** (unconditionally) for $\operatorname{Re}s+\sigma>1$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.4 [unverified locator]"]
theorem hasProd_heckeL (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re + χ.shift) :
    HasProd (localL χ s) (heckeL χ s) := by
  have hsum : Summable fun v => ‖localL χ s v - 1‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => norm_localL_sub_one_le χ hs.le v)
      ((QuadFormsKB.NFEuler.summable_normP_rpow hs).mul_left 2)
  have h := multipliable_one_add_of_summable hsum
  simp only [add_sub_cancel] at h
  exact h.hasProd

/-- **$L(s,\chi)\ne0$** for $\operatorname{Re}s+\sigma>1$. -/
theorem heckeL_ne_zero (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re + χ.shift) : heckeL χ s ≠ 0 := by
  have hsum : Summable fun v => ‖localL χ s v - 1‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => norm_localL_sub_one_le χ hs.le v)
      ((QuadFormsKB.NFEuler.summable_normP_rpow hs).mul_left 2)
  have h := tprod_one_add_ne_zero_of_summable (f := fun v => localL χ s v - 1)
    (fun v => by simpa using localL_ne_zero χ hs.le v) hsum
  simpa [heckeL] using h

/-! ### The standard test function -/

/-- The finite places where $\chi$ is ramified. -/
def ramSet (χ : HeckeCharacter F) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Filter.eventually_cofinite.mp χ.eventually_isUnramifiedAt).toFinset

theorem mem_ramSet {χ : HeckeCharacter F} {v : HeightOneSpectrum (𝓞 F)} :
    v ∈ ramSet χ ↔ ¬ χ.IsUnramifiedAt v := by
  simp [ramSet]

/-- The standard local test function: $\mathbf 1_{\mathcal O_v}$ where $\chi$ is unramified,
$\mathbf 1_{1+\mathfrak p_v^{a_v}}$ where it is ramified ($a_v$ = `conductorExponent`). -/
def stdFv (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F → ℂ :=
  if χ.IsUnramifiedAt v then Analysis.ballIndV v 0 0 else Analysis.ballIndV v 1 (χ.conductorExponent v)

theorem isSchwartzBruhatV_ballIndV (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletion F) (k : ℤ) :
    Analysis.IsSchwartzBruhatV v (Analysis.ballIndV v c k) :=
  ⟨1, fun _ => 1, fun _ => c, fun _ => k, by funext x; simp⟩

/-- **The standard test function** $\Phi_\chi = f\otimes\bigotimes_vf_v$ (`stdFv`) for a Schwartz function $f$ on
$F_\infty$. -/
def stdPhi (χ : HeckeCharacter F) (f : SchwartzMap (mixedSpace F) ℂ) : SchwartzBruhat F where
  fInf := f
  fv := stdFv χ
  S := ramSet χ
  isSchwartzBruhat := fun v _ => by
    unfold stdFv
    split_ifs
    · exact isSchwartzBruhatV_ballIndV v 0 0
    · exact isSchwartzBruhatV_ballIndV v 1 _
  eq_charO := fun v hv => by
    rw [stdFv, if_pos (by simpa [mem_ramSet] using hv)]

theorem conductorExponent_pos {χ : HeckeCharacter F} {v : HeightOneSpectrum (𝓞 F)} (hv : ¬ χ.IsUnramifiedAt v) :
    1 ≤ χ.conductorExponent v := by
  by_contra h
  exact hv ((χ.conductorExponent_eq_zero_iff v).mp (by omega))

/-- The local constant: $\operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$ (unramified) or
$\operatorname{vol}^\times(U_v^{(a_v)})$ (ramified). -/
def stdConstFactor (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  if χ.IsUnramifiedAt v then (volO v).toReal else (tateHaarV v (unitFiltration v (χ.conductorExponent v))).toReal

theorem stdConstFactor_pos (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) : 0 < stdConstFactor χ v := by
  unfold stdConstFactor
  split_ifs with h
  · exact volO_toReal_pos v
  · exact ENNReal.toReal_pos (tateHaarV_unitFiltration_pos v (conductorExponent_pos h)).ne'
      (tateHaarV_unitFiltration_lt_top v _).ne

/-- The places where the local constant may differ from $1$. -/
def constSet (χ : HeckeCharacter F) : Finset (HeightOneSpectrum (𝓞 F)) :=
  ramSet χ ∪ (Analysis.finite_support_diffExp (F := F)).toFinset

theorem stdConstFactor_eq_one {χ : HeckeCharacter F} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ constSet χ) :
    stdConstFactor χ v = 1 := by
  simp only [constSet, Finset.mem_union, mem_ramSet, Set.Finite.mem_toFinset, Function.mem_support, ne_eq,
    not_or, not_not] at hv
  rw [stdConstFactor, if_pos hv.1, volO_toReal]
  have hd : Analysis.diffExp v = 0 := by exact_mod_cast hv.2
  rw [hd, pow_zero, Real.one_rpow]

/-- **The constant $C_\chi$** $= \prod_v$ `stdConstFactor` (a finite product). -/
def stdConst (χ : HeckeCharacter F) : ℝ := ∏ v ∈ constSet χ, stdConstFactor χ v

theorem stdConst_pos (χ : HeckeCharacter F) : 0 < stdConst χ :=
  Finset.prod_pos fun v _ => stdConstFactor_pos χ v

theorem hasProd_stdConstFactor (χ : HeckeCharacter F) :
    HasProd (fun v => (stdConstFactor χ v : ℂ)) (stdConst χ) := by
  rw [stdConst, Complex.ofReal_prod]
  exact hasProd_prod_of_ne_finset_one fun v hv => by rw [stdConstFactor_eq_one hv, Complex.ofReal_one]

/-- **The local zeta integrals of the standard test function**: $Z(f_v,\chi_v,s) = c_v\,L_v(s,\chi)$ for
$\operatorname{Re}s+\sigma>0$, $c_v$ = `stdConstFactor`. -/
theorem zetaIntegral_stdFv (χ : HeckeCharacter F) {s : ℂ} (hs : 0 < χ.shift + s.re) (v : HeightOneSpectrum (𝓞 F)) :
    zetaIntegral (tateHaarV v) (stdFv χ v) (χ.finiteComponent v).toMonoidHom s =
      stdConstFactor χ v * localL χ s v := by
  unfold stdFv stdConstFactor localL
  split_ifs with h
  · rw [← charO_eq_ballIndV, HeckeCharacter.zetaIntegral_finiteComponent_charO χ v h hs, volO_toReal,
      div_eq_mul_inv]
  · rw [zetaIntegral_ballIndV_one v (conductorExponent_pos h)
      (fun u hu => χ.finiteComponent_eq_one_of_mem hu) (tateHaarV v) s, mul_one]

/-- **The finite zeta integral of the standard test function**: $Z_f = C_\chi\,L(s,\chi)$ for
$\operatorname{Re}s+\sigma>1$. -/
theorem finZeta_stdFv (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re + χ.shift) :
    finZeta (stdFv χ) χ s = stdConst χ * heckeL χ s := by
  have h1 := hasProd_finZeta (stdPhi χ 0) χ hs
  have h2 := (hasProd_stdConstFactor χ).mul (hasProd_heckeL χ hs)
  refine h1.unique ?_
  convert h2 using 1
  funext v
  exact zetaIntegral_stdFv χ (by linarith) v

/-- **The Hecke $L$-function is the global zeta integral up to explicit local factors**: for
$\operatorname{Re}s+\sigma>1$,
$$Z(\Phi_\chi,\chi,s) = Z_\infty(f,\chi,s)\cdot C_\chi\cdot L(s,\chi).$$ -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.4 [unverified locator] (ζ(f, c) = ζ_∞ · Π_p ζ_p, unramified factors L_p)"]
theorem globalZeta_stdPhi (χ : HeckeCharacter F) (f : SchwartzMap (mixedSpace F) ℂ) {s : ℂ}
    (hs : 1 < s.re + χ.shift) :
    globalZeta (stdPhi χ f : Adeles F → ℂ) χ s = archZeta f χ s * stdConst χ * heckeL χ s := by
  rw [globalZeta_eq_archZeta_mul_finZeta, show (stdPhi χ f).fv = stdFv χ from rfl, finZeta_stdFv χ hs,
    show (stdPhi χ f).fInf = f from rfl, mul_assoc]

end

end NumberFieldKB.HeckeL
