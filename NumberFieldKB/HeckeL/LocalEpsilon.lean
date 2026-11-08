import NumberFieldKB.HeckeL.FourierSB

/-!
# Local zeta integrals of the dual test function at the finite places

$F$ is a number field, $\chi$ a Hecke character with shift $\sigma$, $v$ a finite place, $d_v$ the exponent of the
different, $\psi_v$ QuadFormsKB's standard character (trivial exactly on $\mathfrak p_v^{-d_v}$), and $f_v$ the standard
local test function of `Basic.lean`. Tate's thesis (Cassels–Fröhlich Ch. XV, §2.5 [unverified locator]) computes
$Z(\hat f_v,\chi_v^{-1},s)$ for $\operatorname{Re}s>\sigma$:

* **unramified** (`zetaIntegral_fourierV_charO_inv`): $\hat f_v = N(\mathfrak d_v)^{-1/2}\mathbf 1_{\mathfrak p_v^{-d_v}}$
  and $Z = N(\mathfrak d_v)^{-1/2}(\chi_v(\varpi_v)N(v)^s)^{d_v}\,Z(\mathbf 1_{\mathcal O_v},\chi_v^{-1},s)$;
* **ramified** (`zetaIntegral_fourierV_ram`), $f_v = \mathbf 1_{1+\mathfrak p_v^{a_v}}$, $a_v\ge1$ the conductor exponent:
  $$Z(\hat f_v,\chi_v^{-1},s) = N(v)^{(a_v+d_v)s}\,\varepsilon_v(\chi),\qquad
  \varepsilon_v(\chi) = \int_{\varpi_v^{-(a_v+d_v)}\mathcal O_v^\times}\hat f_v(y)\chi_v(y)^{-1}\,d^\times y$$
  (`epsLocal`, independent of $s$). The proof is Tate's: the integral over the shell
  $\varpi_v^k\mathcal O_v^\times$ vanishes for $k<-(a_v+d_v)$ (support of $\hat f_v$) and for $k>-(a_v+d_v)$, since there
  $y\mapsto uy$ with $u\in U_v^{(a_v-1)}$ fixes $\hat f_v(y)$ while $\chi_v$ is not trivial on $U_v^{(a_v-1)}$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Set WithZero
open QuadFormsKB QuadFormsKB.Analysis QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

open GlobalZeta LocalZeta

/-! ### The inverse character -/

theorem inv_finiteComponent (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    (((χ⁻¹).finiteComponent v u : ℂˣ) : ℂ) = ((χ.finiteComponent v u : ℂˣ) : ℂ)⁻¹ := by
  show (((χ.finiteComponent v u)⁻¹ : ℂˣ) : ℂ) = _
  rw [Units.val_inv_eq_inv_val]

theorem isUnramifiedAt_inv_iff (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    (χ⁻¹).IsUnramifiedAt v ↔ χ.IsUnramifiedAt v := by
  constructor
  · intro h u hu
    apply Units.ext
    have := congrArg (fun z : ℂˣ => (z : ℂ)) (h u hu)
    simp only [inv_finiteComponent, Units.val_one, inv_eq_one] at this
    exact this
  · intro h u hu
    apply Units.ext
    rw [inv_finiteComponent, h u hu, Units.val_one, inv_one]

theorem conductorExponent_inv (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    (χ⁻¹).conductorExponent v = χ.conductorExponent v := by
  have key : ∀ n, (∀ u ∈ unitFiltration v n, (χ⁻¹).finiteComponent v u = 1) ↔
      ∀ u ∈ unitFiltration v n, χ.finiteComponent v u = 1 := fun n => by
    refine ⟨fun h u hu => Units.ext ?_, fun h u hu => Units.ext ?_⟩
    · have := congrArg (fun z : ℂˣ => (z : ℂ)) (h u hu)
      simp only [inv_finiteComponent, Units.val_one, inv_eq_one] at this
      rw [this, Units.val_one]
    · rw [inv_finiteComponent, h u hu, Units.val_one, inv_one]
  refine le_antisymm ?_ ?_
  · rw [HeckeCharacter.conductorExponent_le_iff, key, ← HeckeCharacter.conductorExponent_le_iff]
  · rw [HeckeCharacter.conductorExponent_le_iff, ← key, ← HeckeCharacter.conductorExponent_le_iff]

theorem shift_inv (χ : HeckeCharacter F) : (χ⁻¹).shift = -χ.shift := by
  refine HeckeCharacter.shift_eq_of_norm_apply_eq_rpow fun c => ?_
  have h := HeckeCharacter.norm_apply_eq_rpow_shift χ c
  have hpos := Ideles.coe_ideleClassNorm_pos c
  show ‖(((χ c)⁻¹ : ℂˣ) : ℂ)‖ = _
  rw [Units.val_inv_eq_inv_val, norm_inv, h, Real.rpow_neg hpos.le]

/-! ### Unramified places -/

/-- **The dual local integral at an unramified place**:
$Z(\hat{\mathbf 1}_{\mathcal O_v},\chi_v^{-1},s) = N(\mathfrak d_v)^{-1/2}(\chi_v(\varpi_v)N(v)^s)^{d_v}\,c_v(\chi^{-1})L_v(s,\chi^{-1})$
for $\operatorname{Re}s>\sigma$. -/
theorem zetaIntegral_fourierV_charO_inv (χ : HeckeCharacter F) {v : HeightOneSpectrum (𝓞 F)}
    (hχ : χ.IsUnramifiedAt v) {s : ℂ} (hs : 0 < -χ.shift + s.re) :
    zetaIntegral (tateHaarV v) (fourierV v (ballIndV v 0 0)) ((χ⁻¹).finiteComponent v).toMonoidHom s =
      ((volO v).toReal : ℂ) * ((χ.finiteComponent v (ϖU v) : ℂ) * (normV v : ℂ) ^ s) ^ diffExp v *
        (stdConstFactor χ⁻¹ v * localL χ⁻¹ s v) := by
  set d := diffExp v
  have h1 : zetaIntegral (tateHaarV v) (fourierV v (ballIndV v 0 0)) ((χ⁻¹).finiteComponent v).toMonoidHom s =
      ((volO v).toReal : ℂ) * zetaIntegral (tateHaarV v)
        (fun x => ballIndV v 0 0 (((ϖU v ^ (d : ℤ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x))
        ((χ⁻¹).finiteComponent v).toMonoidHom s := by
    rw [fourierV_charO, zetaIntegral, zetaIntegral, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [zetaIntegrand, ballIndV_neg_eq]
    ring
  have hur : (χ⁻¹).IsUnramifiedAt v := (isUnramifiedAt_inv_iff χ v).mpr hχ
  have h2 : zetaIntegral (tateHaarV v) (ballIndV v 0 0) ((χ⁻¹).finiteComponent v).toMonoidHom s =
      stdConstFactor χ⁻¹ v * localL χ⁻¹ s v := by
    rw [← zetaIntegral_stdFv χ⁻¹ (by rw [shift_inv]; exact hs) v, stdFv, if_pos hur]
  rw [h1, zetaIntegral_comp_mul, h2]
  have hχ' : ((((χ⁻¹).finiteComponent v).toMonoidHom (ϖU v ^ (d : ℤ)) : ℂˣ) : ℂ)⁻¹ =
      (χ.finiteComponent v (ϖU v) : ℂ) ^ d := by
    change ((((χ⁻¹).finiteComponent v (ϖU v ^ (d : ℤ))) : ℂˣ) : ℂ)⁻¹ = _
    rw [inv_finiteComponent, inv_inv, zpow_natCast, map_pow, Units.val_pow_eq_pow_val]
  have hmod : ((distribHaarChar (v.adicCompletion F) (ϖU v ^ (d : ℤ)) : ℝ) : ℂ) ^ (-s) =
      ((normV v : ℂ) ^ s) ^ d := by
    rw [zpow_natCast, distribHaarChar_ϖU_pow, ofReal_pow_cpow (modV_pos' v).le, modV_cpow, neg_neg]
  rw [hχ', hmod, mul_pow]
  ring

/-! ### Ramified places -/

/-- $\psi_v$ is trivial on $\mathfrak p_v^{-d_v}$. -/
theorem psiV_eq_one {v : HeightOneSpectrum (𝓞 F)} {y : v.adicCompletion F}
    (hy : Valued.v y ≤ exp (diffExp v : ℤ)) : psiV v y = 1 := by
  have hmem : y ∈ annihV v (latticeV v 0) := by
    rw [annihV_latticeV, SetLike.mem_coe, mem_latticeV]
    simpa using hy
  have h1 : (1 : v.adicCompletion F) ∈ latticeV v 0 := by
    rw [mem_latticeV]; simp
  simpa using hmem 1 h1

/-- **The local root-number integral** at a ramified place: $\varepsilon_v(\chi) = \int_{\varpi_v^{-(a_v+d_v)}\mathcal O_v^\times}
\hat f_v(y)\chi_v(y)^{-1}\,d^\times y$, $f_v = \mathbf 1_{1+\mathfrak p_v^{a_v}}$. -/
def epsLocal (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  ∫ u in shell v (-((χ.conductorExponent v : ℤ) + diffExp v)),
    fourierV v (ballIndV v 1 (χ.conductorExponent v)) u * ((χ.finiteComponent v u : ℂˣ) : ℂ)⁻¹ ∂tateHaarV v

theorem exists_unitFiltration_ne_one (χ : HeckeCharacter F) {v : HeightOneSpectrum (𝓞 F)}
    (hχ : ¬ χ.IsUnramifiedAt v) :
    ∃ u ∈ unitFiltration v (χ.conductorExponent v - 1), χ.finiteComponent v u ≠ 1 := by
  by_contra h
  push Not at h
  have hle := (χ.conductorExponent_le_iff v (χ.conductorExponent v - 1)).mpr h
  have := conductorExponent_pos hχ
  omega

/-- **Tate's ramified computation**: for $\operatorname{Re}s>\sigma$,
$Z(\hat f_v,\chi_v^{-1},s) = (N(v)^{a_v+d_v})^s\,\varepsilon_v(\chi)$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 [unverified locator] (the ramified local ζ-function, a Gauss sum)"]
theorem zetaIntegral_fourierV_ram (χ : HeckeCharacter F) {v : HeightOneSpectrum (𝓞 F)}
    (hχ : ¬ χ.IsUnramifiedAt v) {s : ℂ} (hs : 0 < -χ.shift + s.re) :
    zetaIntegral (tateHaarV v) (fourierV v (ballIndV v 1 (χ.conductorExponent v)))
        ((χ⁻¹).finiteComponent v).toMonoidHom s =
      (((normV v ^ (χ.conductorExponent v + diffExp v) : ℝ)) : ℂ) ^ s * epsLocal χ v := by
  set n := χ.conductorExponent v
  set d := diffExp v
  set fh := fourierV v (ballIndV v 1 n)
  set χ' := ((χ⁻¹).finiteComponent v).toMonoidHom
  set g := zetaIntegrand fh χ' s
  have hfh : IsSchwartzBruhatLC v fh :=
    (IsSchwartzBruhatLC.of_isSchwartzBruhatV (isSchwartzBruhatV_ballIndV v 1 n)).fourierV
  have hint : Integrable g (tateHaarV v) :=
    hfh.integrable_zetaIntegrand ((χ⁻¹).finiteComponent v).continuous
      (fun u => by rw [← shift_inv]; exact HeckeCharacter.norm_finiteComponent_eq_rpow χ⁻¹ v u) hs (tateHaarV v)
      (tateHaarV_unitsVSub_ne_top v)
  have hfh_apply : ∀ y, fh y = ballIndV v 0 (-(n : ℤ) - d) y *
      (((selfDualV v).real (latticeV v n) : ℂ) * (psiV v y : ℂ)) := fun y => by
    simp only [fh, fourierV_ballIndV_eq, one_mul]
    rfl
  have hunion : (⋃ k : ℤ, shell v k) = univ :=
    eq_univ_of_forall fun u => mem_iUnion.mpr ⟨_, mem_shell_log v u⟩
  have hsum : zetaIntegral (tateHaarV v) fh χ' s = ∑' k : ℤ, ∫ u in shell v k, g u ∂tateHaarV v := by
    rw [zetaIntegral, ← integral_iUnion (fun k => measurableSet_shell v k) (pairwise_disjoint_shell v)
      hint.integrableOn, hunion, Measure.restrict_univ]
  -- shells below the support
  have hlow : ∀ k : ℤ, k < -((n : ℤ) + d) → ∫ u in shell v k, g u ∂tateHaarV v = 0 := by
    intro k hk
    refine (setIntegral_congr_fun (measurableSet_shell v k) (g := fun _ => (0 : ℂ)) fun u hu => ?_).trans
      (by simp)
    have hv : Valued.v (u : v.adicCompletion F) = exp (-k) := hu
    have h0 : ballIndV v 0 (-(n : ℤ) - d) u = 0 := by
      rw [ballIndV, Set.indicator_of_notMem]
      rw [Set.mem_ofPred_eq, sub_zero, hv, exp_le_exp]
      omega
    simp [g, zetaIntegrand, hfh_apply, h0]
  -- shells above: Tate's vanishing argument
  obtain ⟨u₀, hu₀, hχu₀⟩ := exists_unitFiltration_ne_one χ hχ
  have hu₀v : Valued.v (u₀ : v.adicCompletion F) = 1 := (mem_unitFiltration.mp hu₀).1
  have hhigh : ∀ k : ℤ, -((n : ℤ) + d) < k → ∫ u in shell v k, g u ∂tateHaarV v = 0 := by
    intro k hk
    have hshell : ∀ u, u₀ * u ∈ shell v k ↔ u ∈ shell v k := fun u => by
      simp only [shell, Set.mem_ofPred_eq, Units.val_mul, map_mul, hu₀v, one_mul]
    have hg : ∀ u ∈ shell v k, g (u₀ * u) = (χ' u₀ : ℂ) * g u := by
      intro u hu
      have hv : Valued.v (u : v.adicCompletion F) = exp (-k) := hu
      have hpsi : psiV v ((u₀ : v.adicCompletion F) * u) = psiV v u := by
        have : (u₀ : v.adicCompletion F) * u = u + ((u₀ : v.adicCompletion F) - 1) * u := by ring
        rw [this, AddChar.map_add_eq_mul, psiV_eq_one (y := ((u₀ : v.adicCompletion F) - 1) * (u : v.adicCompletion F)) ?_, mul_one]
        rw [Valuation.map_mul, hv]
        calc Valued.v ((u₀ : v.adicCompletion F) - 1) * exp (-k) ≤ exp (-((n - 1 : ℕ) : ℤ)) * exp (-k) :=
              mul_le_mul_left (mem_unitFiltration.mp hu₀).2 _
          _ ≤ exp (d : ℤ) := by
              rw [← exp_add, exp_le_exp]
              have := conductorExponent_pos hχ
              omega
      have hind : ballIndV v 0 (-(n : ℤ) - d) ((u₀ : v.adicCompletion F) * u) =
          ballIndV v 0 (-(n : ℤ) - d) u := by
        simp only [ballIndV, Set.indicator_apply, Set.mem_ofPred_eq, sub_zero, map_mul, hu₀v, one_mul]
      have hmod : distribHaarChar (v.adicCompletion F) (u₀ * u) = distribHaarChar (v.adicCompletion F) u := by
        rw [map_mul, distribHaarChar_eq_one_of_mem_unitsVSub hu₀v, one_mul]
      simp only [g, zetaIntegrand, Units.val_mul, hfh_apply, hpsi, hind, map_mul, hmod]
      ring
    have hI : ∫ u in shell v k, g u ∂tateHaarV v = (χ' u₀ : ℂ) * ∫ u in shell v k, g u ∂tateHaarV v := by
      calc ∫ u in shell v k, g u ∂tateHaarV v = ∫ u, (shell v k).indicator g u ∂tateHaarV v :=
            (integral_indicator (measurableSet_shell v k)).symm
        _ = ∫ u, (shell v k).indicator g (u₀ * u) ∂tateHaarV v := (integral_mul_left_eq_self _ u₀).symm
        _ = ∫ u, (χ' u₀ : ℂ) * (shell v k).indicator g u ∂tateHaarV v := by
            refine integral_congr_ae (Eventually.of_forall fun u => ?_)
            dsimp only
            by_cases hu : u ∈ shell v k
            · rw [Set.indicator_of_mem ((hshell u).mpr hu), Set.indicator_of_mem hu, hg u hu]
            · rw [Set.indicator_of_notMem (fun h => hu ((hshell u).mp h)), Set.indicator_of_notMem hu,
                mul_zero]
        _ = (χ' u₀ : ℂ) * ∫ u in shell v k, g u ∂tateHaarV v := by
            rw [integral_const_mul, integral_indicator (measurableSet_shell v k)]
    have hne : (χ' u₀ : ℂ) ≠ 1 := by
      change ((((χ⁻¹).finiteComponent v u₀) : ℂˣ) : ℂ) ≠ 1
      rw [inv_finiteComponent, Ne, inv_eq_one]
      intro h
      exact hχu₀ (Units.ext h)
    have : (1 - (χ' u₀ : ℂ)) * ∫ u in shell v k, g u ∂tateHaarV v = 0 := by
      rw [sub_mul, one_mul, ← hI, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  rw [hsum, tsum_eq_single (-((n : ℤ) + d)) fun k hk => by
    rcases lt_or_gt_of_ne hk with h | h
    · exact hlow k h
    · exact hhigh k h]
  -- the remaining shell
  rw [epsLocal, ← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_shell v _) fun u hu => ?_
  have hmod : ((distribHaarChar (v.adicCompletion F) u : ℝ) : ℂ) ^ s =
      (((normV v ^ (n + d) : ℝ)) : ℂ) ^ s := by
    rw [distribHaarChar_of_mem_shell v hu, Analysis.modV_eq, inv_zpow', neg_neg]
    norm_cast
  simp only [g, zetaIntegrand, hmod]
  change fh u * ((((χ⁻¹).finiteComponent v u) : ℂˣ) : ℂ) * _ = _
  rw [inv_finiteComponent]
  ring

end

end NumberFieldKB.HeckeL
