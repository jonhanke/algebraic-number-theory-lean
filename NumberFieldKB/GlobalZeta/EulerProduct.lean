import NumberFieldKB.GlobalZeta.FunctionalEquation
import NumberFieldKB.GlobalZeta.EulerAux
import NumberFieldKB.LocalZeta.Hecke
import QuadFormsKB.Tamagawa.Measure.Weil.ChartMeasures

/-!
# The Euler product of the global zeta integral

$F$ is a number field, $\Phi = f_\infty\otimes\bigotimes_vf_v$ a factorizable Schwartz–Bruhat function, $\chi$ a Hecke
character with shift $\sigma$.

* **`globalZeta_eq_archZeta_mul_finZeta`**: $Z(\Phi,\chi,s) = Z_\infty(f_\infty,\chi,s)\cdot Z_f(\Phi_f,\chi,s)$, the
  archimedean integral over $F_\infty^\times$ (Tate's measure $\omega_\infty$) times the integral over $\mathbb A_f^\times$.
* **`hasProd_finZeta`** (the Euler product): for $\operatorname{Re}s+\sigma>1$,
  $Z_f(\Phi_f,\chi,s) = \prod_vZ(f_v,\chi_v,s)$, the product of the local zeta integrals (Tate's measure
  $d^\times x_v$ = `tateHaarV v`), converging unconditionally (`HasProd`).
* **`globalZeta_eq_archZeta_mul_tprod`**: $Z(\Phi,\chi,s) = Z_\infty(f_\infty,\chi,s)\prod_vZ(f_v,\chi_v,s)$.

*Proof of the Euler product.* Let $S$ be a finite set of places containing those where $f_v\ne\mathbf 1_{\mathcal O_v}$
or $\chi$ is ramified, and $B_S = \{g\in\mathbb A_f^\times : g_v\in\mathcal O_v^\times\ (v\notin S)\}$. QuadFormsKB's chart
lemma as an equality of measures (`map_restrict_idele_eq_pi`) says that $(g_v)_{v\in S}$ pushes $\mu_f|_{B_S}$ to
$\mu_f(\hat{\mathcal O}^\times)\bigotimes_{v\in S}\omega_v(\mathcal O_v^\times)^{-1}\omega_v$. The group $\mathbb A_f^\times$ is the
disjoint union of the cosets $z_xB_S$, $x$ running over the exponent vectors supported outside $S$
($z_x = \prod_v\varpi_v^{x_v}$). On $z_xB_S$ the integrand is $\prod_{v\in S}\zeta_v(g_v)\cdot\prod_{v\notin S}\zeta_v(\varpi_v^{x_v})$
($\chi$ is trivial on $\prod_{v\notin S}\mathcal O_v^\times$: `onIdeles_finEmb_eq_one`), so the integral is a product of
the local integrals at $v\in S$ times a sum over $x$, which is an Euler product (`hasProd_tsum_finsupp`) of the
geometric series $\sum_{j\ge0}\chi_v(\varpi_v)^jN(v)^{-js}$, $v\notin S$.
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Filter Topology Set
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical ENNReal NNReal nonZeroDivisors RestrictedProduct

namespace NumberFieldKB.GlobalZeta

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "V" => mixedSpace F

open LocalZeta Ideles

/-! ### Archimedean and finite ideles -/

variable (F) in
/-- $\mathbb A_f^\times\to\mathbb A_F^\times$, $z\mapsto(1,z)$. -/
def finEmb : AFˣ →* (Adeles F)ˣ := (idelesEquiv F).symm.toMulEquiv.toMonoidHom.comp (MonoidHom.inr _ _)

variable (F) in
/-- $F_\infty^\times\to\mathbb A_F^\times$, $u\mapsto(u,1)$. -/
def infEmb : (mixedSpace F)ˣ →* (Adeles F)ˣ := (idelesEquiv F).symm.toMulEquiv.toMonoidHom.comp (MonoidHom.inl _ _)

theorem idelesEquiv_symm_eq_mul (u : (mixedSpace F)ˣ) (z : AFˣ) :
    (idelesEquiv F).symm (u, z) = infEmb F u * finEmb F z := by
  apply (idelesEquiv F).injective
  rw [map_mul]
  change (u, z) = (idelesEquiv F) ((idelesEquiv F).symm (u, 1)) * (idelesEquiv F) ((idelesEquiv F).symm (1, z))
  rw [ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply, Prod.mk_mul_mk, mul_one, one_mul]

theorem continuous_finEmb : Continuous (finEmb F) :=
  (idelesEquiv F).symm.continuous.comp (continuous_const.prodMk continuous_id)

theorem continuous_infEmb : Continuous (infEmb F) :=
  (idelesEquiv F).symm.continuous.comp (continuous_id.prodMk continuous_const)

theorem infPart_finEmb (z : AFˣ) : infPart (finEmb F z) = 1 := Units.ext rfl

theorem finPart_finEmb (z : AFˣ) : finPart (finEmb F z) = z := Units.ext rfl

/-- $\|(1,z)\| = \prod_v|z_v|_v$. -/
theorem ideleNorm_finEmb (z : AFˣ) : ideleNorm F (finEmb F z) = ∏ᶠ v, (modAt z v : ℝ) := by
  rw [ideleNorm, infPart_finEmb, finPart_finEmb, Units.val_one, LinearMap.mulLeft_one, LinearMap.det_id,
    abs_one, one_mul]

/-- **The archimedean zeta integral** $Z_\infty(f,\chi,s) = \int_{F_\infty^\times}f(u)\chi(u)\|u\|^s\,d\omega_\infty$, with
Tate's (Weil's) measure $\omega_\infty = \prod_{w\text{ real}}dx/|x|\prod_{w\text{ complex}}2\,dx\,dy/|z|^2$. -/
def archZeta (f : SchwartzMap V ℂ) (χ : HeckeCharacter F) (s : ℂ) : ℂ :=
  ∫ u, f (u : V) * (χ.onIdeles (infEmb F u) : ℂ) * (ideleNorm F (infEmb F u) : ℂ) ^ s ∂omegaInf F

/-- The integrand of the finite zeta integral. -/
def finIntegrand (fv : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ) (χ : HeckeCharacter F) (s : ℂ)
    (z : AFˣ) : ℂ :=
  (∏ᶠ v, fv v ((z : AF) v)) * (χ.onIdeles (finEmb F z) : ℂ) * (ideleNorm F (finEmb F z) : ℂ) ^ s

/-- **The finite zeta integral** $Z_f = \int_{\mathbb A_f^\times}\prod_vf_v(z_v)\,\chi(z)\,\|z\|^s\,d\mu_f$. -/
def finZeta (fv : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ) (χ : HeckeCharacter F) (s : ℂ) : ℂ :=
  ∫ z, finIntegrand fv χ s z ∂muFinUnits F

/-- **The archimedean and finite parts**: $Z(\Phi,\chi,s) = Z_\infty(f_\infty,\chi,s)\,Z_f(\Phi_f,\chi,s)$. -/
theorem globalZeta_eq_archZeta_mul_finZeta (Φ : SchwartzBruhat F) (χ : HeckeCharacter F) (s : ℂ) :
    globalZeta (Φ : Adeles F → ℂ) χ s = archZeta Φ.fInf χ s * finZeta Φ.fv χ s := by
  unfold globalZeta archZeta finZeta
  have he : ((idelesEquiv F).symm : _ → (Adeles F)ˣ) = (idelesEquiv F).symm.toHomeomorph.toMeasurableEquiv := rfl
  rw [tamIdeles, he, integral_map_equiv, ← integral_prod_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  obtain ⟨u, z⟩ := p
  change globalZetaIntegrand (Φ : Adeles F → ℂ) χ s ((idelesEquiv F).symm (u, z)) = _
  simp only [globalZetaIntegrand, finIntegrand]
  have hΦ : (Φ : Adeles F → ℂ) ((idelesEquiv F).symm (u, z) : Adeles F) =
      Φ.fInf (u : V) * ∏ᶠ v, Φ.fv v ((z : AF) v) := rfl
  rw [hΦ, idelesEquiv_symm_eq_mul, map_mul, Units.val_mul, ideleNorm_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (ideleNorm_pos _).le (ideleNorm_pos _).le]
  ring

/-! ### Single-place ideles and the factorization of $\chi$ -/

/-- **$\chi(1,(y)_v) = \chi_v(y)$** for the single-place idele (`mulSingleAt`). -/
theorem onIdeles_finEmb_mulSingleAt (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (y : (v.adicCompletion F)ˣ) :
    χ.onIdeles (finEmb F (mulSingleAt v y)) = χ.finiteComponent v y := by
  have h : finEmb F (mulSingleAt v y) = ideleGroupEquiv F (IdeleGroup.ofAdicCompletion (𝓞 F) F v y) := by
    refine Units.ext (Prod.ext ?_ ?_)
    · change (1 : V) = InfiniteAdeleRing.ringEquiv_mixedSpace F 1
      rw [map_one]
    · refine FiniteAdeleRing.ext _ fun w => ?_
      change Pi.mulSingle v (y : v.adicCompletion F) w = FiniteAdeleRing.ofAdicCompletion F v (y : _) w
      change _ = RestrictedProduct.mulSingle _ v (y : v.adicCompletion F) w
      rw [RestrictedProduct.coe_mulSingle_apply]
  rw [h, HeckeCharacter.onIdeles_apply, ContinuousMulEquiv.symm_apply_apply,
    HeckeCharacter.finiteComponent_apply]

theorem unitAt_one' (v : HeightOneSpectrum (𝓞 F)) : unitAt (1 : AFˣ) v = 1 := Units.ext rfl

theorem modAt_mulSingleAt_self (v : HeightOneSpectrum (𝓞 F)) (y : (v.adicCompletion F)ˣ) :
    modAt (mulSingleAt v y) v = distribHaarChar (v.adicCompletion F) y := by
  rw [modAt, unitAt_mulSingleAt]

theorem modAt_mulSingleAt_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : (v.adicCompletion F)ˣ) :
    modAt (mulSingleAt v y) w = 1 := by
  rw [modAt, unitAt_mulSingleAt_of_ne h, map_one]

/-- $\|(1,(y)_v)\| = |y|_v$. -/
theorem ideleNorm_finEmb_mulSingleAt (v : HeightOneSpectrum (𝓞 F)) (y : (v.adicCompletion F)ˣ) :
    ideleNorm F (finEmb F (mulSingleAt v y)) = distribHaarChar (v.adicCompletion F) y := by
  rw [ideleNorm_finEmb, finprod_eq_single _ v fun w hw => by rw [modAt_mulSingleAt_of_ne hw, NNReal.coe_one],
    modAt_mulSingleAt_self]

/-- $\|(1,u)\| = 1$ for $u\in\hat{\mathcal O}^\times$. -/
theorem ideleNorm_finEmb_of_units {u : AFˣ} (hu : ∀ v, unitAt u v ∈ unitsVSub v) :
    ideleNorm F (finEmb F u) = 1 := by
  rw [ideleNorm_finEmb, finprod_eq_one_of_forall_eq_one fun v => by
    rw [modAt, distribHaarChar_eq_one_of_mem_unitsVSub (hu v), NNReal.coe_one]]

/-! ### $\chi$ is trivial on $\prod_{v\notin S}\mathcal O_v^\times$ -/

/-- The finite adele with components $x_v\in\mathcal O_v^\times$. -/
def piUnitsFinVal (x : ∀ v : HeightOneSpectrum (𝓞 F), unitFiltration v 0) : AF :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
    fun v => ⟨((x v : (v.adicCompletion F)ˣ) : v.adicCompletion F),
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr
        (mem_unitFiltration_zero_iff.mp (x v).2).le⟩

theorem piUnitsFinVal_apply (x : ∀ v : HeightOneSpectrum (𝓞 F), unitFiltration v 0)
    (v : HeightOneSpectrum (𝓞 F)) : piUnitsFinVal x v = ((x v : (v.adicCompletion F)ˣ) : v.adicCompletion F) := rfl

theorem continuous_piUnitsFinVal : Continuous (piUnitsFinVal (F := F)) := by
  refine (RestrictedProduct.isOpenEmbedding_structureMap fun v =>
    Valued.isOpen_valuationSubring _).continuous.comp ?_
  exact continuous_pi fun v => (Units.continuous_val.comp
    (continuous_subtype_val.comp (continuous_apply v))).subtype_mk _

theorem piUnitsFinVal_mul (x y : ∀ v : HeightOneSpectrum (𝓞 F), unitFiltration v 0) :
    piUnitsFinVal (x * y) = piUnitsFinVal x * piUnitsFinVal y :=
  FiniteAdeleRing.ext _ fun _ => rfl

theorem piUnitsFinVal_one : piUnitsFinVal (1 : ∀ v : HeightOneSpectrum (𝓞 F), unitFiltration v 0) = 1 :=
  FiniteAdeleRing.ext _ fun _ => rfl

/-- The continuous homomorphism $\prod_v\mathcal O_v^\times\to\mathbb A_f^\times$. -/
def piUnitsFin : (∀ v : HeightOneSpectrum (𝓞 F), unitFiltration v 0) →* AFˣ where
  toFun x :=
    { val := piUnitsFinVal x
      inv := piUnitsFinVal x⁻¹
      val_inv := by rw [← piUnitsFinVal_mul, mul_inv_cancel, piUnitsFinVal_one]
      inv_val := by rw [← piUnitsFinVal_mul, inv_mul_cancel, piUnitsFinVal_one] }
  map_one' := Units.ext piUnitsFinVal_one
  map_mul' x y := Units.ext (piUnitsFinVal_mul x y)

theorem continuous_piUnitsFin : Continuous (piUnitsFin (F := F)) :=
  Units.continuous_iff.mpr ⟨continuous_piUnitsFinVal, continuous_piUnitsFinVal.comp continuous_inv⟩

theorem piUnitsFin_mulSingle (v : HeightOneSpectrum (𝓞 F)) (y : unitFiltration v 0) :
    piUnitsFin (Pi.mulSingle v y) = mulSingleAt v (y : (v.adicCompletion F)ˣ) := by
  refine Units.ext (FiniteAdeleRing.ext _ fun w => ?_)
  change ((Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => unitFiltration w 0) v y w :
      unitFiltration w 0) : (w.adicCompletion F)ˣ).val =
    Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v
      ((y : (v.adicCompletion F)ˣ) : v.adicCompletion F) w
  by_cases hw : w = v
  · subst hw; simp
  · simp [Pi.mulSingle_eq_of_ne hw]

/-- **A Hecke character unramified outside $S$ is trivial on $\prod_{v\notin S}\mathcal O_v^\times$**: on finite ideles
$u$ with $u_v\in\mathcal O_v^\times$ for all $v$ and $u_v = 1$ for $v\in S$. -/
theorem onIdeles_finEmb_eq_one (χ : HeckeCharacter F) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, χ.IsUnramifiedAt v) {u : AFˣ} (hu : ∀ v, unitAt u v ∈ unitsVSub v)
    (hu1 : ∀ v ∈ S, unitAt u v = 1) : χ.onIdeles (finEmb F u) = 1 := by
  set x : ∀ v : HeightOneSpectrum (𝓞 F), unitFiltration v 0 := fun v =>
    ⟨unitAt u v, mem_unitFiltration_zero_iff.mpr (hu v)⟩
  have hux : piUnitsFin x = u := Units.ext (FiniteAdeleRing.ext _ fun _ => rfl)
  set Ψ := (χ.onIdeles.comp (finEmb F)).comp piUnitsFin
  have hΨ : Continuous Ψ := χ.continuous_onIdeles.comp (continuous_finEmb.comp continuous_piUnitsFin)
  have h := MonoidHom.eq_one_of_continuous_pi Ψ hΨ (S : Set (HeightOneSpectrum (𝓞 F))) (fun v hv y => by
    simp only [Ψ, MonoidHom.comp_apply, piUnitsFin_mulSingle, onIdeles_finEmb_mulSingleAt]
    exact hS v hv _ (mem_unitFiltration_zero_iff.mp y.2)) x (fun v hv =>
      Subtype.ext (hu1 v hv))
  rw [← hux]
  exact h

/-! ### The sets $B_S$ and the coset representatives $z_x$ -/

section Cosets

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- $B_S = \{g\in\mathbb A_f^\times : g_v\in\mathcal O_v^\times\text{ for }v\notin S\}$. -/
def boxS : Set AFˣ := {g | ∀ v, v ∉ S → unitAt g v ∈ unitsVSub v}

theorem boxS_eq_ideleBox : boxS S = ideleBox S fun _ => univ := by
  ext g
  simp only [boxS, ideleBox, mem_ofPred_eq]
  refine forall_congr' fun v => ?_
  by_cases hv : v ∈ S <;> simp [hv]

theorem measurableSet_boxS : MeasurableSet (boxS S) := by
  rw [boxS_eq_ideleBox]
  exact measurableSet_ideleBox S _ fun _ _ => MeasurableSet.univ

/-- The components at the places of $S$. -/
def projS (g : AFˣ) : (v : S) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ := fun v => unitAt g v

theorem continuous_projS : Continuous (projS (F := F) S) :=
  continuous_pi fun v => continuous_unitAt (v : HeightOneSpectrum (𝓞 F))

/-- The finite idele with components $y_v$ at $v\in S$ and $1$ elsewhere. -/
def liftS (y : (v : S) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ) : AFˣ :=
  ∏ v : S, mulSingleAt (v : HeightOneSpectrum (𝓞 F)) (y v)

theorem unitAt_liftS_of_mem (y : (v : S) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ) (v : S) :
    unitAt (liftS S y) v = y v := by
  have hmap : unitAt (liftS S y) v = ∏ w : S, unitAt (mulSingleAt (w : HeightOneSpectrum (𝓞 F)) (y w)) v :=
    map_prod (unitAtHom (v : HeightOneSpectrum (𝓞 F))) _ _
  rw [hmap, Finset.prod_eq_single v (fun w _ hwv => unitAt_mulSingleAt_of_ne
    (fun h => hwv (Subtype.ext h.symm)) _) (fun h => absurd (Finset.mem_univ v) h), unitAt_mulSingleAt]

theorem unitAt_liftS_of_notMem (y : (v : S) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ S) : unitAt (liftS S y) w = 1 := by
  have hmap : unitAt (liftS S y) w = ∏ v : S, unitAt (mulSingleAt (v : HeightOneSpectrum (𝓞 F)) (y v)) w :=
    map_prod (unitAtHom w) _ _
  rw [hmap]
  exact Finset.prod_eq_one fun v _ => unitAt_mulSingleAt_of_ne (fun h => hw (by rw [h]; exact v.2)) _

theorem onIdeles_finEmb_liftS (χ : HeckeCharacter F)
    (y : (v : S) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ) :
    (χ.onIdeles (finEmb F (liftS S y)) : ℂ) = ∏ v : S, (χ.finiteComponent v (y v) : ℂ) := by
  rw [liftS, map_prod, map_prod, Units.coe_prod]
  exact Finset.prod_congr rfl fun v _ => by rw [onIdeles_finEmb_mulSingleAt]

theorem ideleNorm_finEmb_prod {ι : Type*} (T : Finset ι) (z : ι → AFˣ) :
    ideleNorm F (finEmb F (∏ i ∈ T, z i)) = ∏ i ∈ T, ideleNorm F (finEmb F (z i)) := by
  rw [← coe_ideleNormHom, map_prod, map_prod, NNReal.coe_prod]
  exact Finset.prod_congr rfl fun i _ => coe_ideleNormHom _

theorem ideleNorm_finEmb_liftS (y : (v : S) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ) :
    ideleNorm F (finEmb F (liftS S y)) =
      ∏ v : S, (distribHaarChar ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) (y v) : ℝ) := by
  rw [liftS, ideleNorm_finEmb_prod]
  exact Finset.prod_congr rfl fun v _ => ideleNorm_finEmb_mulSingleAt _ _

/-- The representative $z_x = \prod_v\varpi_v^{x_v}$ of the exponent vector $x$. -/
def zx (x : HeightOneSpectrum (𝓞 F) →₀ ℤ) : AFˣ := ∏ v ∈ x.support, mulSingleAt v (Analysis.ϖU v ^ x v)

theorem unitAt_zx (x : HeightOneSpectrum (𝓞 F) →₀ ℤ) (w : HeightOneSpectrum (𝓞 F)) :
    unitAt (zx x) w = Analysis.ϖU w ^ x w := by
  have hmap : unitAt (zx x) w = ∏ v ∈ x.support, unitAt (mulSingleAt v (Analysis.ϖU v ^ x v)) w :=
    map_prod (unitAtHom w) _ _
  rw [hmap]
  by_cases hw : w ∈ x.support
  · rw [Finset.prod_eq_single w (fun v _ hvw => unitAt_mulSingleAt_of_ne (Ne.symm hvw) _)
      (fun h => absurd hw h), unitAt_mulSingleAt]
  · rw [Finset.prod_eq_one fun v hv => unitAt_mulSingleAt_of_ne (fun h => hw (by rw [h]; exact hv)) _,
      Finsupp.notMem_support_iff.mp hw, zpow_zero]

theorem ordAt_zx (x : HeightOneSpectrum (𝓞 F) →₀ ℤ) (w : HeightOneSpectrum (𝓞 F)) : ordAt (zx x) w = x w := by
  rw [ordAt, ← unitAt_val, unitAt_zx, LocalZeta.valued_ϖU_zpow, WithZero.log_exp, neg_neg]

theorem onIdeles_finEmb_zx (χ : HeckeCharacter F) (x : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    (χ.onIdeles (finEmb F (zx x)) : ℂ) =
      ∏ v ∈ x.support, (χ.finiteComponent v (Analysis.ϖU v ^ x v) : ℂ) := by
  rw [zx, map_prod, map_prod, Units.coe_prod]
  exact Finset.prod_congr rfl fun v _ => by rw [onIdeles_finEmb_mulSingleAt]

theorem ideleNorm_finEmb_zx (x : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    ideleNorm F (finEmb F (zx x)) =
      ∏ v ∈ x.support, (distribHaarChar (v.adicCompletion F) (Analysis.ϖU v ^ x v) : ℝ) := by
  rw [zx, ideleNorm_finEmb_prod]
  exact Finset.prod_congr rfl fun v _ => ideleNorm_finEmb_mulSingleAt _ _

/-- The decomposition $g = (\prod_{v\in S}(g_v)_v)\cdot u$ with $u_v = 1$ for $v\in S$. -/
def unitPartS (g : AFˣ) : AFˣ := (liftS S (projS S g))⁻¹ * g

theorem unitAt_inv_mul (a g : AFˣ) (w : HeightOneSpectrum (𝓞 F)) :
    unitAt (a⁻¹ * g) w = (unitAt a w)⁻¹ * unitAt g w := by
  rw [unitAt_mul]
  congr 1

theorem liftS_mul_unitPartS (g : AFˣ) : liftS S (projS S g) * unitPartS S g = g := by
  rw [unitPartS, mul_inv_cancel_left]

theorem unitAt_unitPartS_of_mem (g : AFˣ) (v : S) : unitAt (unitPartS S g) v = 1 := by
  rw [unitPartS, unitAt_inv_mul, unitAt_liftS_of_mem, projS, inv_mul_cancel]

theorem unitAt_unitPartS_of_notMem (g : AFˣ) {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ S) :
    unitAt (unitPartS S g) w = unitAt g w := by
  rw [unitPartS, unitAt_inv_mul, unitAt_liftS_of_notMem S _ hw, inv_one, one_mul]

theorem unitAt_unitPartS_mem {g : AFˣ} (hg : g ∈ boxS S) (w : HeightOneSpectrum (𝓞 F)) :
    unitAt (unitPartS S g) w ∈ unitsVSub w := by
  by_cases hw : w ∈ S
  · rw [unitAt_unitPartS_of_mem S g ⟨w, hw⟩]; exact one_mem_unitsVSub w
  · rw [unitAt_unitPartS_of_notMem S g hw]; exact hg w hw

end Cosets

/-! ### The integrand on a coset $z_xB_S$ -/

section Integrand

variable (Φ : SchwartzBruhat F) (χ : HeckeCharacter F) (s : ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- The local integrand $\zeta_v(y) = f_v(y)\chi_v(y)|y|_v^s$ (the local `zetaIntegrand`). -/
abbrev locInt (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ → ℂ :=
  zetaIntegrand (Φ.fv v) (χ.finiteComponent v).toMonoidHom s

theorem ballIndV_mul_unit {v : HeightOneSpectrum (𝓞 F)} (y : v.adicCompletion F) {u : (v.adicCompletion F)ˣ}
    (hu : u ∈ unitsVSub v) : Analysis.ballIndV v 0 0 (y * u) = Analysis.ballIndV v 0 0 y := by
  have hu1 : Valued.v (u : v.adicCompletion F) = 1 := hu
  rw [ballIndV_zero_zero_apply, ballIndV_zero_zero_apply]
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hu1, mul_one]

theorem ballIndV_unit {v : HeightOneSpectrum (𝓞 F)} {u : (v.adicCompletion F)ˣ} (hu : u ∈ unitsVSub v) :
    Analysis.ballIndV v 0 0 u = 1 := by
  have hu1 : Valued.v (u : v.adicCompletion F) = 1 := hu
  rw [ballIndV_zero_zero_apply, if_pos ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu1.le)]

variable {S}

/-- The finite part of $\Phi$ on $z_xB_S$. -/
theorem finprod_fv_zx_mul (hSΦ : Φ.S ⊆ S) {x : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hx : ∀ v ∈ S, x v = 0)
    {g : AFˣ} (hg : g ∈ boxS S) :
    ∏ᶠ w, Φ.fv w (((zx x * g : AFˣ) : AF) w) =
      (∏ v ∈ x.support, Φ.fv v ((Analysis.ϖU v ^ x v : (v.adicCompletion F)ˣ) : v.adicCompletion F)) *
        ∏ v : S, Φ.fv v (unitAt g v) := by
  have hval : ∀ w, ((zx x * g : AFˣ) : AF) w =
      ((Analysis.ϖU w ^ x w : (w.adicCompletion F)ˣ) : w.adicCompletion F) * unitAt g w := fun w => by
    rw [← unitAt_val, unitAt_mul, unitAt_zx, Units.val_mul]
  have hdisj : Disjoint S x.support := Finset.disjoint_left.mpr fun v hvS hvx =>
    (Finsupp.mem_support_iff.mp hvx) (hx v hvS)
  have hout : ∀ w, w ∉ S → Φ.fv w = Analysis.ballIndV w 0 0 := fun w hw => Φ.eq_charO w fun h => hw (hSΦ h)
  rw [finprod_eq_prod_of_mulSupport_subset (s := S ∪ x.support) _ fun w hw => by
    by_contra h
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at h
    apply hw
    show Φ.fv w (((zx x * g : AFˣ) : AF) w) = 1
    rw [hval, Finsupp.notMem_support_iff.mp h.2, zpow_zero, Units.val_one, one_mul, hout w h.1]
    exact ballIndV_unit (hg w h.1)]
  rw [Finset.prod_union hdisj, mul_comm, ← Finset.prod_coe_sort S]
  congr 1
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hvS : v ∉ S := fun h => (Finsupp.mem_support_iff.mp hv) (hx v h)
    rw [hval, hout v hvS, ballIndV_mul_unit _ (hg v hvS)]
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [hval, hx v v.2, zpow_zero, Units.val_one, one_mul]

/-- **The finite integrand on the coset $z_xB_S$**: for $g\in B_S$,
$F(z_xg) = \prod_{v}\zeta_v(\varpi_v^{x_v})\cdot\prod_{v\in S}\zeta_v(g_v)$. -/
theorem finIntegrand_zx_mul (hSΦ : Φ.S ⊆ S) (hSχ : ∀ v ∉ S, χ.IsUnramifiedAt v)
    {x : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hx : ∀ v ∈ S, x v = 0) {g : AFˣ} (hg : g ∈ boxS S) :
    finIntegrand Φ.fv χ s (zx x * g) =
      (∏ v ∈ x.support, locInt Φ χ s v (Analysis.ϖU v ^ x v)) * ∏ v : S, locInt Φ χ s v (unitAt g v) := by
  have hdec : zx x * g = zx x * liftS S (projS S g) * unitPartS S g := by
    rw [mul_assoc, liftS_mul_unitPartS]
  have hu := unitAt_unitPartS_mem S hg
  have hχ : (χ.onIdeles (finEmb F (zx x * g)) : ℂ) =
      (∏ v ∈ x.support, (χ.finiteComponent v (Analysis.ϖU v ^ x v) : ℂ)) *
        ∏ v : S, (χ.finiteComponent v (unitAt g v) : ℂ) := by
    rw [hdec, map_mul, map_mul, map_mul, map_mul, onIdeles_finEmb_eq_one χ S hSχ hu
      (fun v hv => unitAt_unitPartS_of_mem S g ⟨v, hv⟩), mul_one, Units.val_mul, onIdeles_finEmb_zx,
      onIdeles_finEmb_liftS]
    rfl
  have hN : ideleNorm F (finEmb F (zx x * g)) =
      (∏ v ∈ x.support, (distribHaarChar (v.adicCompletion F) (Analysis.ϖU v ^ x v) : ℝ)) *
        ∏ v : S, (distribHaarChar ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) (unitAt g v) : ℝ) := by
    rw [hdec, map_mul, map_mul, ideleNorm_mul, ideleNorm_mul, ideleNorm_finEmb_of_units hu, mul_one,
      ideleNorm_finEmb_zx, ideleNorm_finEmb_liftS]
    rfl
  rw [finIntegrand, finprod_fv_zx_mul Φ hSΦ hx hg, hχ, hN, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _)
      (Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _),
    ofReal_prod_cpow _ _ (fun _ => NNReal.coe_nonneg _), ofReal_prod_cpow _ _ (fun _ => NNReal.coe_nonneg _)]
  simp only [locInt, zetaIntegrand, Finset.prod_mul_distrib]
  simp only [MonoidHom.coe_coe, ContinuousMonoidHom.coe_toMonoidHom]
  ring

end Integrand

/-! ### Integrals over $B_S$ and its cosets -/

section Integrals

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- The normalized local measures $\omega_v(\mathcal O_v^\times)^{-1}\omega_v$, $v\in S$. -/
abbrev locMeas (v : S) : Measure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ :=
  ((omegaV (v : HeightOneSpectrum (𝓞 F)) (unitsVSub (v : HeightOneSpectrum (𝓞 F)))).toNNReal)⁻¹ •
    omegaV (v : HeightOneSpectrum (𝓞 F))

/-- **Integration over $B_S$ of a function of the $S$-components**: QuadFormsKB's chart lemma
`map_restrict_idele_eq_pi`. -/
theorem setIntegral_boxS_projS (G : ((v : S) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ) → ℂ)
    (hG : Measurable G) :
    ∫ g in boxS S, G (projS S g) ∂muFinUnits F =
      (muFinUnits F (OHatUnits F)).toReal • ∫ y, G y ∂Measure.pi (locMeas S) := by
  rw [← integral_map (continuous_projS S).aemeasurable hG.aestronglyMeasurable]
  have h : Measure.map (projS S) ((muFinUnits F).restrict (boxS S)) =
      muFinUnits F (OHatUnits F) • Measure.pi (locMeas S) := map_restrict_idele_eq_pi (F := F) S
  rw [h, integral_smul_measure]

theorem integral_pi_locMeas (φ : ∀ v : S, ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ → ℂ) :
    ∫ y, ∏ v : S, φ v (y v) ∂Measure.pi (locMeas S) =
      ∏ v : S, (((omegaV (v : HeightOneSpectrum (𝓞 F)) (unitsVSub (v : HeightOneSpectrum (𝓞 F)))).toReal)⁻¹ : ℂ) *
        ∫ u, φ v u ∂omegaV (v : HeightOneSpectrum (𝓞 F)) := by
  rw [integral_fintype_prod_eq_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_inv, ENNReal.coe_toNNReal_eq_toReal,
    Complex.real_smul, Complex.ofReal_inv]

/-- Integration over a coset $aB_S$ by translation. -/
theorem setIntegral_coset (F' : AFˣ → ℂ) (a : AFˣ) :
    ∫ z in (fun z => a⁻¹ * z) ⁻¹' boxS S, F' z ∂muFinUnits F = ∫ g in boxS S, F' (a * g) ∂muFinUnits F := by
  have hmp := measurePreserving_mul_left (muFinUnits F) a
  have h := hmp.setIntegral_preimage_emb (MeasurableEquiv.mulLeft a).measurableEmbedding F'
    ((fun z => a⁻¹ * z) ⁻¹' boxS S)
  have hset : (fun g => a * g) ⁻¹' ((fun z => a⁻¹ * z) ⁻¹' boxS S) = boxS S := by
    ext g; simp
  rw [hset] at h
  exact h.symm

theorem ordAt_inv_mul (a z : AFˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ordAt (a⁻¹ * z) v = ordAt z v - ordAt a v := by
  have := ordAt_mul a (a⁻¹ * z) v
  rw [mul_inv_cancel_left] at this
  linarith

theorem mem_unitsVSub_iff_ordAt (z : AFˣ) (v : HeightOneSpectrum (𝓞 F)) :
    unitAt z v ∈ unitsVSub v ↔ ordAt z v = 0 := by
  rw [ordAt_eq_zero_iff]; rfl

/-- The coset $z_xB_S$ (empty unless $x$ vanishes on $S$). -/
def cosetC (x : HeightOneSpectrum (𝓞 F) →₀ ℤ) : Set AFˣ :=
  {z | (∀ v ∈ S, x v = 0) ∧ (zx x)⁻¹ * z ∈ boxS S}

theorem mem_cosetC_iff (x : HeightOneSpectrum (𝓞 F) →₀ ℤ) (z : AFˣ) :
    z ∈ cosetC S x ↔ (∀ v ∈ S, x v = 0) ∧ ∀ v, v ∉ S → ordAt z v = x v := by
  simp only [cosetC, boxS, mem_ofPred_eq, mem_unitsVSub_iff_ordAt, ordAt_inv_mul, ordAt_zx, sub_eq_zero]

theorem measurableSet_cosetC (x : HeightOneSpectrum (𝓞 F) →₀ ℤ) : MeasurableSet (cosetC S x) := by
  have : cosetC S x = {_z | ∀ v ∈ S, x v = 0} ∩ (fun z => (zx x)⁻¹ * z) ⁻¹' boxS S := rfl
  rw [this]
  exact (MeasurableSet.const _).inter ((measurableSet_boxS S).preimage (measurable_const_mul _))

theorem pairwise_disjoint_cosetC : Pairwise (Function.onFun Disjoint (cosetC (F := F) S)) := by
  intro x y hxy
  rw [Function.onFun, Set.disjoint_left]
  intro z hzx hzy
  apply hxy
  rw [mem_cosetC_iff] at hzx hzy
  ext v
  by_cases hv : v ∈ S
  · rw [hzx.1 v hv, hzy.1 v hv]
  · rw [← hzx.2 v hv, ← hzy.2 v hv]

theorem iUnion_cosetC : ⋃ x, cosetC (F := F) S x = univ := by
  refine eq_univ_of_forall fun z => mem_iUnion.mpr ?_
  refine ⟨Finsupp.onFinset (finite_ordAt z).toFinset (fun v => if v ∈ S then 0 else ordAt z v) fun v hv => by
    simp only [Set.Finite.mem_toFinset, mem_ofPred_eq]
    split_ifs at hv with h
    · exact absurd rfl hv
    · exact hv, ?_⟩
  rw [mem_cosetC_iff]
  refine ⟨fun v hv => by simp [hv], fun v hv => by simp [hv]⟩

theorem setIntegral_cosetC (F' : AFˣ → ℂ) (x : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    ∫ z in cosetC S x, F' z ∂muFinUnits F =
      if ∀ v ∈ S, x v = 0 then ∫ g in boxS S, F' (zx x * g) ∂muFinUnits F else 0 := by
  split_ifs with hx
  · have : cosetC S x = (fun z => (zx x)⁻¹ * z) ⁻¹' boxS S := by
      ext z
      simp only [cosetC, mem_ofPred_eq, mem_preimage]
      exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
    rw [this, setIntegral_coset]
  · have : cosetC S x = ∅ := by
      ext z; simp only [cosetC, mem_ofPred_eq, hx, false_and, mem_empty_iff_false]
    rw [this, Measure.restrict_empty, integral_zero_measure]

/-- **Unfolding over the cosets**: $\int_{\mathbb A_f^\times}F = \sum_x\int_{z_xB_S}F$. -/
theorem integral_eq_tsum_cosetC (F' : AFˣ → ℂ) (hF : Integrable F' (muFinUnits F)) :
    ∫ z, F' z ∂muFinUnits F = ∑' x, ∫ z in cosetC S x, F' z ∂muFinUnits F := by
  rw [← integral_iUnion (measurableSet_cosetC S) (pairwise_disjoint_cosetC S)
    (by rw [iUnion_cosetC]; exact hF.integrableOn), iUnion_cosetC, Measure.restrict_univ]

end Integrals

/-! ### Integrability of the finite integrand -/

/-- $\int_{\mathbb A_f^\times}H(\mathfrak a(z))\,d\mu_f = |d_F|^{-1/2}\sum_{\mathfrak b}H(\mathfrak b)$. -/
theorem lintegral_comp_ideleIdeal (H : IdeleClass.FracIdeal F → ℝ≥0∞) :
    ∫⁻ z, H (ideleIdeal F z) ∂muFinUnits F = ∑' 𝔟, H 𝔟 * ENNReal.ofReal (ohatVol F) := by
  have h : (fun z => H (ideleIdeal F z)) = fun z =>
      ∑' 𝔟, {z : AFˣ | ideleIdeal F z = 𝔟}.indicator (fun _ => H 𝔟) z :=
    funext (QFPort.comp_ideleIdeal_eq_tsum H)
  rw [h, lintegral_tsum fun 𝔟 => (measurable_const.indicator
    (QFPort.measurableSet_ideleIdeal_fiber 𝔟)).aemeasurable]
  refine tsum_congr fun 𝔟 => ?_
  rw [lintegral_indicator_const (QFPort.measurableSet_ideleIdeal_fiber 𝔟), QFPort.muFinUnits_ideleIdeal_fiber]

theorem measurable_finIntegrand (Φ : SchwartzBruhat F) (χ : HeckeCharacter F) (s : ℂ) :
    Measurable (finIntegrand Φ.fv χ s) := by
  refine (((measurable_finprod Φ.isSchwartzBruhatLC Φ.eq_charO).comp Units.continuous_val.measurable).mul
    (χ.continuous_coe_onIdeles.comp continuous_finEmb).measurable).mul ?_
  exact (Complex.continuous_ofReal.comp (continuous_ideleNorm.comp continuous_finEmb)).measurable.pow_const s

theorem ideleNorm_finEmb_eq (z : AFˣ) :
    ideleNorm F (finEmb F z) = (IdeleClass.idealNorm F (ideleIdeal F z))⁻¹ := by
  rw [ideleNorm_finEmb, finprod_modAt_eq]

/-- **The finite zeta integral converges absolutely** for $\operatorname{Re}s+\sigma>1$. -/
theorem integrable_finIntegrand (Φ : SchwartzBruhat F) (χ : HeckeCharacter F) {s : ℂ}
    (hs : 1 < s.re + χ.shift) : Integrable (finIntegrand Φ.fv χ s) (muFinUnits F) := by
  refine ⟨(measurable_finIntegrand Φ χ s).aestronglyMeasurable, ?_⟩
  obtain ⟨M, hM, e, hb⟩ := exists_finprod_bound Φ.isSchwartzBruhatLC Φ.eq_charO
  set σ := s.re + χ.shift
  set H : IdeleClass.FracIdeal F → ℝ≥0∞ := fun 𝔟 =>
    ENNReal.ofReal M * ENNReal.ofReal (if InBox e 𝔟 then IdeleClass.idealNorm F 𝔟 ^ (-σ) else 0)
  have hpt : ∀ z : AFˣ, ‖finIntegrand Φ.fv χ s z‖ₑ ≤ H (ideleIdeal F z) := by
    intro z
    have hN := IdeleClass.idealNorm_pos F (ideleIdeal F z)
    rw [← ofReal_norm, finIntegrand, norm_mul, norm_mul, HeckeCharacter.norm_onIdeles,
      Complex.norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos _), mul_assoc,
      ← Real.rpow_add (ideleNorm_pos _), add_comm χ.shift, ideleNorm_finEmb_eq, Real.inv_rpow hN.le,
      ← Real.rpow_neg hN.le]
    simp only [H]
    rw [← ENNReal.ofReal_mul hM]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hb z
    split_ifs at h1 ⊢ with hbox
    · rw [mul_one] at h1
      exact mul_le_mul h1 le_rfl (Real.rpow_nonneg hN.le _) hM
    · rw [mul_zero] at h1
      rw [norm_le_zero_iff.mp h1, norm_zero, zero_mul, mul_zero]
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_comp_ideleIdeal]
  simp only [H]
  simp_rw [mul_assoc, mul_comm _ (ENNReal.ofReal (ohatVol F)), ← mul_assoc]
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    (tsum_inBox_lt_top e hs)

/-! ### The Euler product -/

section Euler

variable (Φ : SchwartzBruhat F) (χ : HeckeCharacter F) (s : ℂ)

theorem sb_isSchwartzBruhatLC_all (v : HeightOneSpectrum (𝓞 F)) : IsSchwartzBruhatLC v (Φ.fv v) := by
  by_cases hv : v ∈ Φ.S
  · exact Φ.isSchwartzBruhatLC v hv
  · rw [Φ.eq_charO v hv]
    exact IsSchwartzBruhatLC.of_isSchwartzBruhatV (isSchwartzBruhatV_ballIndV v 0 0)

theorem measurable_locInt (v : HeightOneSpectrum (𝓞 F)) : Measurable (locInt Φ χ s v) := by
  unfold locInt zetaIntegrand
  refine ((((sb_isSchwartzBruhatLC_all Φ v).measurable.comp Units.continuous_val.measurable)).mul
    ((Units.continuous_val.comp (χ.finiteComponent v).continuous).measurable)).mul ?_
  exact (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
    (LocalZeta.continuous_distribHaarChar_v v))).measurable.pow_const s

/-- The places where $f_v\ne\mathbf 1_{\mathcal O_v}$ or $\chi$ is ramified. -/
def badS : Finset (HeightOneSpectrum (𝓞 F)) :=
  Φ.S ∪ (Filter.eventually_cofinite.mp χ.eventually_isUnramifiedAt).toFinset

theorem subset_badS : Φ.S ⊆ badS Φ χ := Finset.subset_union_left

theorem isUnramifiedAt_of_notMem_badS {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badS Φ χ) :
    χ.IsUnramifiedAt v := by
  by_contra h
  exact hv (Finset.mem_union_right _ (by simpa using h))

/-- The local factors of the series over exponent vectors: $[j = 0]$ at $v\in S$, $\zeta_v(\varpi_v^j)$ at $v\notin S$. -/
def eFun (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) (j : ℤ) : ℂ :=
  if v ∈ S then (if j = 0 then 1 else 0) else locInt Φ χ s v (Analysis.ϖU v ^ j)

variable {Φ χ s}

theorem locInt_one {v : HeightOneSpectrum (𝓞 F)} (hv : Φ.fv v = Analysis.ballIndV v 0 0) :
    locInt Φ χ s v 1 = 1 := by
  simp only [locInt, zetaIntegrand]
  rw [hv, ballIndV_unit (one_mem_unitsVSub v), map_one, map_one, Units.val_one, NNReal.coe_one, Complex.ofReal_one,
    Complex.one_cpow, mul_one, mul_one]

theorem finprod_eFun {S : Finset (HeightOneSpectrum (𝓞 F))} (hSΦ : Φ.S ⊆ S) (x : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    ∏ᶠ v, eFun Φ χ s S v (x v) =
      if ∀ v ∈ S, x v = 0 then ∏ v ∈ x.support, locInt Φ χ s v (Analysis.ϖU v ^ x v) else 0 := by
  have hout : ∀ w, w ∉ S → Φ.fv w = Analysis.ballIndV w 0 0 := fun w hw => Φ.eq_charO w fun h => hw (hSΦ h)
  rw [finprod_eq_prod_of_mulSupport_subset (s := S ∪ x.support) _ fun v hv => by
    by_contra h
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at h
    apply hv
    show eFun Φ χ s S v (x v) = 1
    rw [eFun, if_neg h.1, Finsupp.notMem_support_iff.mp h.2, zpow_zero, locInt_one (hout v h.1)]]
  split_ifs with hx
  · have hdisj : Disjoint S x.support := Finset.disjoint_left.mpr fun v hvS hvx =>
      (Finsupp.mem_support_iff.mp hvx) (hx v hvS)
    rw [Finset.prod_union hdisj, Finset.prod_eq_one fun v hv => by rw [eFun, if_pos hv, if_pos (hx v hv)], one_mul]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hvS : v ∉ S := fun h => (Finsupp.mem_support_iff.mp hv) (hx v h)
    rw [eFun, if_neg hvS]
  · push Not at hx
    obtain ⟨v, hv, hxv⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_union_left _ hv) (by rw [eFun, if_pos hv, if_neg hxv])

/-- The integral over $B_S$ of $\prod_{v\in S}\zeta_v(g_v)$. -/
def kInt (Φ : SchwartzBruhat F) (χ : HeckeCharacter F) (s : ℂ) (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ :=
  ∫ g in boxS S, ∏ v : S, locInt Φ χ s v (unitAt g v) ∂muFinUnits F

/-- $Z_f = \sum_x\Bigl(\prod_ve_v(x_v)\Bigr)\int_{B_S}\prod_{v\in S}\zeta_v$. -/
theorem finZeta_eq_tsum {S : Finset (HeightOneSpectrum (𝓞 F))} (hSΦ : Φ.S ⊆ S)
    (hSχ : ∀ v ∉ S, χ.IsUnramifiedAt v) (hs : 1 < s.re + χ.shift) :
    finZeta Φ.fv χ s = ∑' x : HeightOneSpectrum (𝓞 F) →₀ ℤ, (∏ᶠ v, eFun Φ χ s S v (x v)) * kInt Φ χ s S := by
  rw [finZeta, integral_eq_tsum_cosetC S _ (integrable_finIntegrand Φ χ hs)]
  refine tsum_congr fun x => ?_
  rw [setIntegral_cosetC, finprod_eFun hSΦ]
  split_ifs with hx
  · rw [setIntegral_congr_fun (measurableSet_boxS S) fun g hg => finIntegrand_zx_mul Φ χ s hSΦ hSχ hx hg,
      integral_const_mul, kInt]
  · rw [zero_mul]

theorem kInt_eq (S : Finset (HeightOneSpectrum (𝓞 F))) :
    kInt Φ χ s S = (muFinUnits F (OHatUnits F)).toReal *
      ∏ v : S, (((omegaV (v : HeightOneSpectrum (𝓞 F)) (unitsVSub (v : HeightOneSpectrum (𝓞 F)))).toReal)⁻¹ : ℂ) *
        ∫ u, locInt Φ χ s v u ∂omegaV (v : HeightOneSpectrum (𝓞 F)) := by
  have hmeas : Measurable fun y : (v : S) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ =>
      ∏ v : S, locInt Φ χ s v (y v) :=
    Finset.measurable_prod _ fun v _ => (measurable_locInt Φ χ s v).comp (measurable_pi_apply v)
  have h := setIntegral_boxS_projS S (fun y => ∏ v : S, locInt Φ χ s v (y v)) hmeas
  rw [integral_pi_locMeas, Complex.real_smul] at h
  rw [kInt]
  exact h

/-- $\operatorname{vol}(\mathcal O_v) = \lambda_v^{-1}\omega_v(\mathcal O_v^\times)$. -/
theorem volO_toReal_eq (v : HeightOneSpectrum (𝓞 F)) :
    (volO v).toReal = (lamV v)⁻¹ * (omegaV v (unitsVSub v)).toReal := by
  rw [← lamV_inv_mul_omegaV_unitsVSub, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 (lamV_pos v).le)]

theorem volO_toReal_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < (volO v).toReal :=
  ENNReal.toReal_pos (volO_pos v).ne' (volO_ne_top v)

theorem omegaV_toReal_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < (omegaV v (unitsVSub v)).toReal :=
  ENNReal.toReal_pos (omegaV_unitsVSub_ne_zero v) (QuadFormsKB.Tamagawa.Measure.Weil.omegaV_unitsVSub_ne_top v)

/-- The local zeta integral is $\lambda_v^{-1}\int\zeta_v\,d\omega_v$. -/
theorem zetaIntegral_tateHaarV_eq (v : HeightOneSpectrum (𝓞 F)) :
    zetaIntegral (tateHaarV v) (Φ.fv v) (χ.finiteComponent v).toMonoidHom s =
      ((lamV v)⁻¹ : ℂ) * ∫ u, locInt Φ χ s v u ∂omegaV v := by
  rw [tateHaarV, zetaIntegral_smul_measure, Real.coe_toNNReal _ (inv_nonneg.2 (lamV_pos v).le),
    Complex.ofReal_inv]
  rfl

/-- At a place of $S$: $\omega_v(\mathcal O_v^\times)^{-1}\int\zeta_v\,d\omega_v = Z_v/\operatorname{vol}(\mathcal O_v)$. -/
theorem omegaV_inv_mul_integral (v : HeightOneSpectrum (𝓞 F)) :
    (((omegaV v (unitsVSub v)).toReal)⁻¹ : ℂ) * ∫ u, locInt Φ χ s v u ∂omegaV v =
      zetaIntegral (tateHaarV v) (Φ.fv v) (χ.finiteComponent v).toMonoidHom s / ((volO v).toReal : ℂ) := by
  rw [zetaIntegral_tateHaarV_eq, volO_toReal_eq, Complex.ofReal_mul, Complex.ofReal_inv]
  have h1 : ((lamV v)⁻¹ : ℂ) ≠ 0 := by
    rw [ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]; exact (lamV_pos v).ne'
  have h2 : ((omegaV v (unitsVSub v)).toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (omegaV_toReal_pos v).ne'
  have h3 : ((lamV v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lamV_pos v).ne'
  field_simp

theorem charO_eq_ballIndV (v : HeightOneSpectrum (𝓞 F)) : charO v = Analysis.ballIndV v 0 0 := by
  funext y
  rw [charO_apply, ballIndV_zero_zero_apply]
  by_cases h : Valued.v y ≤ 1
  · rw [if_pos h, if_pos ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h)]
  · rw [if_neg h, if_neg fun h' => h ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h')]

/-- The unramified local factor $r_v = \chi_v(\varpi_v)N(v)^{-s}$. -/
abbrev rV (χ : HeckeCharacter F) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  (χ.finiteComponent v (Analysis.ϖU v) : ℂ) * ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (-s)

theorem distribHaarChar_ϖU_pow (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    (distribHaarChar (v.adicCompletion F) (Analysis.ϖU v ^ k) : ℝ) = (Analysis.modV v : ℝ) ^ k := by
  rw [map_pow, NNReal.coe_pow]; rfl

theorem norm_rV_lt_one (χ : HeckeCharacter F) {s : ℂ} (hs : 0 < χ.shift + s.re) (v : HeightOneSpectrum (𝓞 F)) :
    ‖rV χ s v‖ < 1 := by
  rw [rV, ← modV_cpow, norm_mul, HeckeCharacter.norm_finiteComponent_eq_rpow,
    Complex.norm_cpow_eq_rpow_re_of_pos (modV_pos' v), show (distribHaarChar (v.adicCompletion F)
      (Analysis.ϖU v) : ℝ) = Analysis.modV v from rfl, ← Real.rpow_add (modV_pos' v)]
  exact Real.rpow_lt_one (modV_pos' v).le (modV_lt_one v) hs

theorem locInt_ϖU_pow {v : HeightOneSpectrum (𝓞 F)} (hv : Φ.fv v = Analysis.ballIndV v 0 0) (k : ℕ) :
    locInt Φ χ s v (Analysis.ϖU v ^ (k : ℤ)) = rV χ s v ^ k := by
  have hO : Analysis.ballIndV v 0 0 ((Analysis.ϖU v ^ (k : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [ballIndV_zero_zero_apply, if_pos]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, LocalZeta.valued_ϖU_zpow, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    omega
  have hd : ((distribHaarChar (v.adicCompletion F) (Analysis.ϖU v ^ (k : ℤ)) : ℝ) : ℂ) ^ s =
      (((Analysis.modV v : ℝ) : ℂ) ^ s) ^ k := by
    rw [zpow_natCast, distribHaarChar_ϖU_pow, ofReal_pow_cpow (modV_pos' v).le]
  have hχ : (((χ.finiteComponent v).toMonoidHom (Analysis.ϖU v ^ (k : ℤ)) : ℂˣ) : ℂ) =
      (χ.finiteComponent v (Analysis.ϖU v) : ℂ) ^ k := by
    rw [zpow_natCast, map_pow, Units.val_pow_eq_pow_val]; rfl
  unfold locInt zetaIntegrand
  rw [hv, hO, hχ, hd, modV_cpow, one_mul, rV, mul_pow]

theorem locInt_ϖU_zpow_neg {v : HeightOneSpectrum (𝓞 F)} (hv : Φ.fv v = Analysis.ballIndV v 0 0) {j : ℤ}
    (hj : j < 0) : locInt Φ χ s v (Analysis.ϖU v ^ j) = 0 := by
  have hO : Analysis.ballIndV v 0 0 ((Analysis.ϖU v ^ j : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 0 := by
    rw [ballIndV_zero_zero_apply, if_neg]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, LocalZeta.valued_ϖU_zpow, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    omega
  simp only [locInt, zetaIntegrand, hv, hO, zero_mul]

/-- At an unramified place outside $S$: $\sum_je_v(j) = (1-\chi_v(\varpi_v)N(v)^{-s})^{-1}$. -/
theorem hasSum_eFun_of_notMem {S : Finset (HeightOneSpectrum (𝓞 F))} (hSΦ : Φ.S ⊆ S) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ S) (hs : 0 < χ.shift + s.re) : HasSum (eFun Φ χ s S v) (1 - rV χ s v)⁻¹ := by
  have hout : Φ.fv v = Analysis.ballIndV v 0 0 := Φ.eq_charO v fun h => hv (hSΦ h)
  have hg := hasSum_geometric_of_norm_lt_one (norm_rV_lt_one χ hs v)
  have hsupp : ∀ j ∉ Set.range (Nat.cast : ℕ → ℤ), eFun Φ χ s S v j = 0 := by
    intro j hj
    rw [eFun, if_neg hv]
    refine locInt_ϖU_zpow_neg hout ?_
    by_contra h
    exact hj ⟨j.toNat, by omega⟩
  refine (Nat.cast_injective.hasSum_iff hsupp).mp ?_
  refine hg.congr_fun fun k => ?_
  simp only [Function.comp_apply, eFun, if_neg hv]
  exact locInt_ϖU_pow hout k

theorem hasSum_eFun_of_mem {S : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    HasSum (eFun Φ χ s S v) 1 := by
  have : eFun Φ χ s S v = fun j => if j = 0 then 1 else 0 := funext fun j => by rw [eFun, if_pos hv]
  rw [this]
  convert hasSum_ite_eq (0 : ℤ) (1 : ℂ) using 1

/-- The unramified local zeta integral: $Z_v = \operatorname{vol}(\mathcal O_v)\sum_je_v(j)$ at $v\notin S$. -/
theorem zetaIntegral_eq_vol_mul_tsum {S : Finset (HeightOneSpectrum (𝓞 F))} (hSΦ : Φ.S ⊆ S)
    (hSχ : ∀ v ∉ S, χ.IsUnramifiedAt v) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) (hs : 0 < χ.shift + s.re) :
    zetaIntegral (tateHaarV v) (Φ.fv v) (χ.finiteComponent v).toMonoidHom s =
      ((volO v).toReal : ℂ) * ∑' j, eFun Φ χ s S v j := by
  have hout : Φ.fv v = Analysis.ballIndV v 0 0 := Φ.eq_charO v fun h => hv (hSΦ h)
  rw [(hasSum_eFun_of_notMem hSΦ hv hs).tsum_eq, hout, ← charO_eq_ballIndV,
    HeckeCharacter.zetaIntegral_finiteComponent_charO χ v (hSχ v hv) hs, volO_toReal, div_eq_mul_inv]

/-- $\prod_v\operatorname{vol}(\mathcal O_v) = \mu_f(\hat{\mathcal O}^\times) = |d_F|^{-1/2}$, a finite product. -/
theorem hasProd_volO :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => ((volO v).toReal : ℂ)) (muFinUnits F (OHatUnits F)).toReal := by
  set T := Analysis.finite_support_diffExp (F := F)
  have h1 : ∀ v ∉ T.toFinset, ((volO v).toReal : ℂ) = 1 := fun v hv => by
    simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, not_not] at hv
    have hv' : Analysis.diffExp v = 0 := by exact_mod_cast hv
    rw [volO_toReal, hv', pow_zero, Real.one_rpow, Complex.ofReal_one]
  have h2 := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) h1
  convert h2 using 1
  rw [muFinUnits_OHatUnits, ENNReal.toReal_ofReal ohatVol_pos.le, ohatVol_eq_finprod, ← Complex.ofReal_prod]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset (s := T.toFinset) _ fun v hv => by
    by_contra h
    apply hv
    have := h1 v h
    rw [volO_eq_ofReal, ENNReal.toReal_ofReal (measureReal_nonneg)] at this
    exact_mod_cast this]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [volO_eq_ofReal, ENNReal.toReal_ofReal measureReal_nonneg]

/-- **The Euler product of the finite zeta integral** (Tate, Cassels–Fröhlich Ch. XV, §3.3 and §4.4 [unverified
locators]): for $\operatorname{Re}s+\sigma>1$, $Z_f(\Phi_f,\chi,s) = \prod_vZ(f_v,\chi_v,s)$, an unconditionally convergent
product of the local zeta integrals (Tate's measure $d^\times x_v$). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.4 [unverified locator] (ζ(f, c) = ∏_p ζ_p(f_p, c_p) for Re > 1)"]
theorem hasProd_finZeta (Φ : SchwartzBruhat F) (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re + χ.shift) :
    HasProd (fun v => zetaIntegral (tateHaarV v) (Φ.fv v) (χ.finiteComponent v).toMonoidHom s)
      (finZeta Φ.fv χ s) := by
  set S := badS Φ χ
  have hSΦ : Φ.S ⊆ S := subset_badS Φ χ
  have hSχ : ∀ v ∉ S, χ.IsUnramifiedAt v := fun v hv => isUnramifiedAt_of_notMem_badS Φ χ hv
  have hs0 : 0 < χ.shift + s.re := by linarith
  set σ := s.re + χ.shift
  -- the Euler product of the series over exponent vectors
  have hE := hasProd_tsum_finsupp (eFun Φ χ s S) S (fun v hv => by
      rw [eFun, if_neg hv, zpow_zero, locInt_one (Φ.eq_charO v fun h => hv (hSΦ h))])
    (boxFactor 0 σ) (fun v j => ?_) (fun v _ => by simp [boxFactor])
    (fun v => (hasSum_boxFactor 0 (zero_lt_one.trans hs) v).summable) (hasProd_boxFactor 0 hs)
  · obtain ⟨_, hP⟩ := hE
    set P := ∑' x : HeightOneSpectrum (𝓞 F) →₀ ℤ, ∏ᶠ v, eFun Φ χ s S v (x v)
    set Z := fun v => zetaIntegral (tateHaarV v) (Φ.fv v) (χ.finiteComponent v).toMonoidHom s
    -- the local factors at the places of `S`
    set rr : HeightOneSpectrum (𝓞 F) → ℂ := fun v => if v ∈ S then Z v / ((volO v).toReal : ℂ) else 1
    have hrr : HasProd rr (∏ v ∈ S, Z v / ((volO v).toReal : ℂ)) := by
      have := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (s := S) (f := rr)
        fun v hv => by simp only [rr, if_neg hv]
      convert this using 1
      exact Finset.prod_congr rfl fun v hv => by simp only [rr, if_pos hv]
    have hall := (hasProd_volO.mul hP).mul hrr
    have hZ : (fun v => ((volO v).toReal : ℂ) * (∑' j, eFun Φ χ s S v j) * rr v) = Z := by
      funext v
      by_cases hv : v ∈ S
      · rw [(hasSum_eFun_of_mem hv).tsum_eq, mul_one]
        simp only [rr, if_pos hv]
        have : ((volO v).toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (volO_toReal_pos v).ne'
        field_simp
      · simp only [rr, if_neg hv, mul_one]
        exact (zetaIntegral_eq_vol_mul_tsum hSΦ hSχ hv hs0).symm
    rw [hZ] at hall
    convert hall using 1
    rw [finZeta_eq_tsum hSΦ hSχ hs, tsum_mul_right, kInt_eq, ← Finset.prod_coe_sort S]
    simp_rw [omegaV_inv_mul_integral]
    ring
  · -- the bound by the box factors
    by_cases hv : v ∈ S
    · simp only [eFun, if_pos hv]
      split_ifs with hj
      · subst hj; simp [boxFactor]
      · rw [norm_zero]; exact boxFactor_nonneg 0 σ v j
    · simp only [eFun, if_neg hv]
      have hout : Φ.fv v = Analysis.ballIndV v 0 0 := Φ.eq_charO v fun h => hv (hSΦ h)
      rcases lt_or_ge j 0 with hj | hj
      · rw [locInt_ϖU_zpow_neg hout hj, norm_zero]; exact boxFactor_nonneg 0 σ v j
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj
        rw [locInt_ϖU_pow hout k, norm_pow, boxFactor, if_pos (by simp)]
        rw [rV, ← modV_cpow, norm_mul, HeckeCharacter.norm_finiteComponent_eq_rpow,
          Complex.norm_cpow_eq_rpow_re_of_pos (modV_pos' v), show (distribHaarChar (v.adicCompletion F)
            (Analysis.ϖU v) : ℝ) = Analysis.modV v from rfl, ← Real.rpow_add (modV_pos' v), Analysis.modV_eq,
          Real.inv_rpow (Nat.cast_nonneg _), ← Real.rpow_neg (Nat.cast_nonneg _), ← Real.rpow_natCast,
          ← Real.rpow_mul (Nat.cast_nonneg _)]
        apply le_of_eq
        congr 1
        push_cast
        ring

/-- **The Euler product of the global zeta integral**: for $\operatorname{Re}s+\sigma>1$,
$$Z(\Phi,\chi,s) = Z_\infty(f_\infty,\chi,s)\prod_vZ(f_v,\chi_v,s).$$ -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.4 [unverified locator] (ζ(f, c) = ∏_p ζ_p(f_p, c_p))"]
theorem globalZeta_eq_archZeta_mul_tprod (Φ : SchwartzBruhat F) (χ : HeckeCharacter F) {s : ℂ}
    (hs : 1 < s.re + χ.shift) :
    globalZeta (Φ : Adeles F → ℂ) χ s =
      archZeta Φ.fInf χ s * ∏' v, zetaIntegral (tateHaarV v) (Φ.fv v) (χ.finiteComponent v).toMonoidHom s := by
  rw [globalZeta_eq_archZeta_mul_finZeta, (hasProd_finZeta Φ χ hs).tprod_eq]

end Euler

end

end NumberFieldKB.GlobalZeta
