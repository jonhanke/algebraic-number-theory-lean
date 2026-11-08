import NumberFieldKB.HeckeL.ArchGamma
import NumberFieldKB.HeckeL.DedekindCont
import NumberFieldKB.HeckeCharacter.Examples

/-!
# The completed Hecke L-function and its continuation

$F$ is a number field, $\chi$ a Hecke character with shift $\sigma$, conductor $\mathfrak f_\chi$ and
archimedean factor $L_\infty(s,\chi)$ (`gammaInf`, `ArchGamma.lean`). Put $A(\chi) = |d_F|\,N(\mathfrak f_\chi)$
(`condDisc`).

* **`completedHeckeL χ s`** $=\Lambda(s,\chi)$: defined from the continued global zeta integral of the standard test
  function $\Phi_\chi = f_\infty^\chi\otimes\bigotimes_vf_v$; for $\operatorname{Re}s+\sigma>1$,
  $$\Lambda(s,\chi) = A(\chi)^{s/2}\,L_\infty(s,\chi)\,L(s,\chi)\qquad(\texttt{completedHeckeL\_eq}).$$
  It is meromorphic on $\mathbb C$ (`meromorphic_completedHeckeL`), **entire unless $\chi = \|\cdot\|^c$** for some
  $c\in\mathbb C$ (`differentiable_completedHeckeL`; for unitary $\chi$, $c = i\tau$), and for $\chi = \|\cdot\|^c$
  holomorphic away from $-c$ and $1-c$.
* **`heckeLCont χ`**: the continuation of $L(s,\chi)$, $A^{-s/2}\Lambda(s,\chi)/L_\infty(s,\chi)$; it equals
  $L(s,\chi)$ for $\operatorname{Re}s+\sigma>1$ (`heckeLCont_eq`) and is **entire unless $\chi = \|\cdot\|^c$**
  (`differentiable_heckeLCont`). For $\chi = \|\cdot\|^c$, $L(s,\chi) = \zeta_F(s+c)$ (`heckeL_normPow`), whose
  continuation is `dedekindZetaCont`.

Tate's thesis, Cassels–Fröhlich Ch. XV, §4.4 and §4.5 [unverified locators]; Neukirch, *Algebraic Number Theory*,
Ch. VII, §8 [unverified locator].
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Filter Set
open Topology
open QuadFormsKB QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

open GlobalZeta LocalZeta

/-! ### The conductor-discriminant factor -/

theorem conductor_ne_bot (χ : HeckeCharacter F) : χ.conductor ≠ ⊥ := by
  rw [HeckeCharacter.conductor, finprod_eq_prod_of_mulSupport_subset (s := ramSet χ) _ (fun v hv => by
    rw [Finset.mem_coe, mem_ramSet]
    intro h
    apply hv
    simp [(χ.conductorExponent_eq_zero_iff v).mpr h])]
  rw [Ne, ← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff, not_exists]
  intro v ⟨_, hv⟩
  exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot) hv

/-- $N(\mathfrak f_\chi)$, the absolute norm of the conductor. -/
def condNorm (χ : HeckeCharacter F) : ℝ := (Ideal.absNorm χ.conductor : ℝ)

theorem condNorm_pos (χ : HeckeCharacter F) : 0 < condNorm χ := by
  rw [condNorm, Nat.cast_pos, Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact conductor_ne_bot χ

/-- **$A(\chi) = |d_F|\,N(\mathfrak f_\chi)$**, the conductor-discriminant factor of the completed $L$-function. -/
def condDisc (χ : HeckeCharacter F) : ℝ := |(discr F : ℝ)| * condNorm χ

theorem condDisc_pos (χ : HeckeCharacter F) : 0 < condDisc χ :=
  mul_pos abs_discr_pos (condNorm_pos χ)

theorem condDisc_ne_zero (χ : HeckeCharacter F) : ((condDisc χ : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (condDisc_pos χ).ne'

/-! ### The completed $L$-function -/

theorem gammaInf_ne_zero (χ : HeckeCharacter F) {s : ℂ} (hs : 0 < s.re + χ.shift) : gammaInf χ s ≠ 0 := by
  unfold gammaInf
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun w _ => Complex.Gammaℝ_ne_zero_of_re_pos ?_)
    (Finset.prod_ne_zero_iff.mpr fun w _ => Gammaℂ_ne_zero_of_re_pos ?_)
  · have := χ.re_realExponent w.2
    simp only [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (eW χ w : ℝ) := Nat.cast_nonneg _
    linarith
  · have := χ.re_complexExponent w.2
    simp only [Complex.add_re, Complex.div_re, Complex.natCast_re, Complex.natCast_im]
    norm_num
    have : (0 : ℝ) ≤ |((kW χ w : ℤ) : ℝ)| := abs_nonneg _
    linarith

/-- The constant $\pi^{r_2}C_\chi$ relating $Z(\Phi_\chi,\chi,s)$ to $L_\infty(s,\chi)L(s,\chi)$. -/
def zetaConst (χ : HeckeCharacter F) : ℂ := (Real.pi : ℂ) ^ nrComplexPlaces F * stdConst χ

theorem zetaConst_ne_zero (χ : HeckeCharacter F) : zetaConst χ ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)) (by exact_mod_cast (stdConst_pos χ).ne')

/-- The standard test function $\Phi_\chi = f_\infty^\chi\otimes\bigotimes_vf_v$ of $\chi$. -/
def heckePhi (χ : HeckeCharacter F) : SchwartzBruhat F := stdPhi χ (archTest χ)

/-- **$Z(\Phi_\chi,\chi,s) = \pi^{r_2}C_\chi\,L_\infty(s,\chi)\,L(s,\chi)$** for $\operatorname{Re}s+\sigma>1$. -/
theorem globalZeta_heckePhi (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re + χ.shift) :
    globalZeta (heckePhi χ : Adeles F → ℂ) χ s = zetaConst χ * gammaInf χ s * heckeL χ s := by
  rw [heckePhi, globalZeta_stdPhi χ _ hs, archZeta_archTest χ (by linarith), zetaConst]
  ring

/-- **The completed Hecke $L$-function** $\Lambda(s,\chi) = A(\chi)^{s/2}(\pi^{r_2}C_\chi)^{-1}Z(\Phi_\chi,\chi,s)$, with the
continued global zeta integral; it is $A(\chi)^{s/2}L_\infty(s,\chi)L(s,\chi)$ for
$\operatorname{Re}s+\sigma>1$ (`completedHeckeL_eq`). -/
@[kb "neukirch1999" "Ch. VII, §8, Def. 8.4 and Cor. 8.6 [unverified locator] (Λ(X, s) = (|d_K| 𝔑(𝔣))^{s/2} L_∞ L)"]
def completedHeckeL (χ : HeckeCharacter F) (s : ℂ) : ℂ :=
  ((condDisc χ : ℝ) : ℂ) ^ (s / 2) * (zetaConst χ)⁻¹ * globalZetaCont (heckePhi χ) χ s

/-- **$\Lambda(s,\chi) = A(\chi)^{s/2}L_\infty(s,\chi)L(s,\chi)$** for $\operatorname{Re}s+\sigma>1$. -/
theorem completedHeckeL_eq (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re + χ.shift) :
    completedHeckeL χ s = ((condDisc χ : ℝ) : ℂ) ^ (s / 2) * gammaInf χ s * heckeL χ s := by
  rw [completedHeckeL, globalZetaCont_eq _ _ hs, globalZeta_heckePhi χ hs]
  have := zetaConst_ne_zero χ
  field_simp

/-- **$\Lambda(s,\chi)$ is entire unless $\chi = \|\cdot\|^c$** (for unitary $\chi$: $c = i\tau$, $\tau\in\mathbb R$). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.5 [unverified locator] (L(s, χ) entire for χ ≠ |·|^{iτ})"]
theorem differentiable_completedHeckeL {χ : HeckeCharacter F} (h : ∀ c : ℂ, χ ≠ HeckeCharacter.normPow F c) :
    Differentiable ℂ (completedHeckeL χ) := fun s =>
  ((((differentiableAt_id.div_const 2).const_cpow (Or.inl (condDisc_ne_zero χ))).mul
    (differentiableAt_const _)).mul (differentiable_globalZetaCont (heckePhi χ) h s))

/-- **$\Lambda(s,\|\cdot\|^c)$ is holomorphic away from $s = -c$ and $s = 1-c$.** -/
theorem differentiableAt_completedHeckeL_normPow (c : ℂ) {s : ℂ} (h0 : s ≠ -c) (h1 : s ≠ 1 - c) :
    DifferentiableAt ℂ (completedHeckeL (HeckeCharacter.normPow F c)) s :=
  ((((differentiableAt_id.div_const 2).const_cpow (Or.inl (condDisc_ne_zero _))).mul
    (differentiableAt_const _)).mul (differentiableAt_globalZetaCont_normPow _ c h0 h1))

/-- **$\Lambda(s,\chi)$ is meromorphic on $\mathbb C$.** -/
theorem meromorphic_completedHeckeL (χ : HeckeCharacter F) : Meromorphic (completedHeckeL χ) := by
  intro x
  have hd : Differentiable ℂ fun s : ℂ => ((condDisc χ : ℝ) : ℂ) ^ (s / 2) * (zetaConst χ)⁻¹ := fun s =>
    ((differentiableAt_id.div_const 2).const_cpow (Or.inl (condDisc_ne_zero χ))).mul (differentiableAt_const _)
  exact ((hd.analyticAt x).meromorphicAt).mul (meromorphic_globalZetaCont (heckePhi χ) χ x)

/-! ### The continuation of $L(s,\chi)$ -/

/-- $1/L_\infty(s,\chi)$, an entire function. -/
def gammaInfInv (χ : HeckeCharacter F) (s : ℂ) : ℂ :=
  (∏ w : {w : InfinitePlace F // w.IsReal}, (Complex.Gammaℝ (s + χ.realExponent w.2 + eW χ w))⁻¹) *
    ∏ w : {w : InfinitePlace F // w.IsComplex},
      (Complex.Gammaℂ (s + χ.complexExponent w.2 / 2 + (kW χ w).natAbs / 2))⁻¹

theorem gammaInfInv_eq (χ : HeckeCharacter F) (s : ℂ) : gammaInfInv χ s = (gammaInf χ s)⁻¹ := by
  rw [gammaInfInv, gammaInf, mul_inv, Finset.prod_inv_distrib, Finset.prod_inv_distrib]

theorem differentiable_gammaInfInv (χ : HeckeCharacter F) : Differentiable ℂ (gammaInfInv χ) := by
  unfold gammaInfInv
  refine Differentiable.mul ?_ ?_
  · refine Differentiable.fun_finsetProd fun w _ => ?_
    exact Complex.differentiable_Gammaℝ_inv.comp ((differentiable_id.add_const _).add_const _)
  · refine Differentiable.fun_finsetProd fun w _ => ?_
    exact Complex.differentiable_Gammaℂ_inv.comp ((differentiable_id.add_const _).add_const _)

/-- **The continuation of the Hecke $L$-function**: $L(s,\chi) = A(\chi)^{-s/2}\Lambda(s,\chi)/L_\infty(s,\chi)$. -/
@[kb "neukirch1999" "Ch. VII, §8, Cor. 8.6 [unverified locator]"]
def heckeLCont (χ : HeckeCharacter F) (s : ℂ) : ℂ :=
  ((condDisc χ : ℝ) : ℂ) ^ (-s / 2) * completedHeckeL χ s * gammaInfInv χ s

/-- **The continuation agrees with the Euler product** for $\operatorname{Re}s+\sigma>1$. -/
theorem heckeLCont_eq (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re + χ.shift) : heckeLCont χ s = heckeL χ s := by
  rw [heckeLCont, completedHeckeL_eq χ hs, gammaInfInv_eq]
  have hg := gammaInf_ne_zero χ (s := s) (by linarith)
  have hd : ((condDisc χ : ℝ) : ℂ) ^ (s / 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => condDisc_ne_zero χ h.1
  rw [neg_div, Complex.cpow_neg]
  field_simp

/-- **$L(s,\chi)$ continues to an entire function unless $\chi = \|\cdot\|^c$.** -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.5 [unverified locator]"]
theorem differentiable_heckeLCont {χ : HeckeCharacter F} (h : ∀ c : ℂ, χ ≠ HeckeCharacter.normPow F c) :
    Differentiable ℂ (heckeLCont χ) := fun s =>
  ((((differentiableAt_id.neg.div_const 2).const_cpow (Or.inl (condDisc_ne_zero χ))).mul
    (differentiable_completedHeckeL h s)).mul (differentiable_gammaInfInv χ s))

/-- **$L(s,\|\cdot\|^c) = \zeta_F(s+c)$** (Euler products, $\operatorname{Re}s+c>1$ for convergence). -/
theorem heckeL_normPow (c s : ℂ) : heckeL (HeckeCharacter.normPow F c) s = heckeL (1 : HeckeCharacter F) (s + c) := by
  unfold heckeL
  congr 1
  funext v
  rw [localL, if_pos (HeckeCharacter.isUnramifiedAt_normPow c v), localL_one]
  congr 2
  rw [rV, HeckeCharacter.finiteComponent_normPow, ← Ideles.distribHaarChar_adicCompletion,
    show (distribHaarChar (v.adicCompletion F) (Analysis.ϖU v) : ℝ) = Analysis.modV v from rfl, modV_cpow,
    ← Complex.cpow_add _ _ (by exact_mod_cast (normV_pos v).ne')]
  congr 1
  ring

end

end NumberFieldKB.HeckeL
