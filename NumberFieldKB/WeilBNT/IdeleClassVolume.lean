import QuadFormsKB.Tamagawa.Measure.Weil.IdeleClassVolume

/-!
# Weil, *Basic Number Theory*, Chapter V, §4, Proposition 9: the volume of $C(m)$ in the idele class group

$k$ is a number field (here `F`) with $r_1$ real and $r_2$ imaginary places, class number $h$, regulator $R$, and $e$
roots of unity. Weil (V.§4, Prop. 9, p. 95) takes the Haar measure $\gamma=\prod_v\gamma_v$ on $k_{\mathbb A}^\times$ with
$\gamma_v(r_v^\times)=1$ at every finite place, $d\gamma_w=\lvert x\rvert^{-1}dx$ at a real place and
$d\gamma_w=(x\bar x)^{-1}\lvert dx\wedge d\bar x\rvert$ at an imaginary place, and proves that the image $C(m)$ in
$k_{\mathbb A}^\times/k^\times$ of $\{z:1\le\lvert z\rvert_{\mathbb A}\le m\}$ has measure $c_k\log m$,
$$c_k=\frac{2^{r_1}(2\pi)^{r_2}hR}{e}.$$
The measure of a subset of $k_{\mathbb A}^\times/k^\times$ is, by V.§4 text p. 89 (here `weil_V_4_text89`), the measure
of its trace on a fundamental set; so the statement is made for an arbitrary measurable fundamental domain $X$ of
$k^\times$ in $k_{\mathbb A}^\times$ (`weil_V_4_prop9`), and such an $X$ exists (`exists_isFundamentalDomain_ideles`).

Types and measures are QuadFormsKB's: `(Adeles F)ˣ`, the principal ideles `diagUnitsSub F`, the idele norm
`ideleNorm F`, and its Haar measure `tamIdeles F` $=\omega_\infty\times\prod_v\lambda_v^{-1}\omega_v$, which gives
$\hat{\mathcal O}^\times$ the mass $\lvert D\rvert^{-1/2}$ (`muFinUnits_OHatUnits`) and is $\lvert x\rvert^{-1}dx$ at the
real places and $2\,dx\,dy/\lvert z\rvert^2=(z\bar z)^{-1}\lvert dz\wedge d\bar z\rvert$ at the complex places
(`omegaInf_eq`). Hence

* **`weilIdeleMeasure F`** $=\sqrt{\lvert D\rvert}\cdot$`tamIdeles F` is Weil's $\gamma$; the normalization at the finite
  places is `weilIdeleMeasure_prod_OHatUnits` ($\gamma(A\times\hat{\mathcal O}^\times)=\omega_\infty(A)$).
* **`weilCk F`** is $c_k$ (Mathlib's `classNumber`, `Units.regulator`, `Units.torsionOrder`), and
  `weilCk_eq` : $c_k=\sqrt{\lvert D\rvert}\,\rho_k$ with $\rho_k$ = Mathlib's `dedekindZeta_residue`.

*Proof* (not Weil's: his goes through the explicit fundamental set of Prop. 8 and the regulator). Through
$k_{\mathbb A}^\times\cong k^1\times\mathbb R_{>0}$ (QuadFormsKB `ideleSplit`, `map_ideleSplit_tamIdeles`:
`tamIdeles` $=\mu^1\times dt/t$), $X_0=\{g:g\,s(\lvert g\rvert)^{-1}\in D\}$, $D$ a fundamental domain of $k^\times$ in
$k^1$, is a fundamental domain of $k^\times$ in $k_{\mathbb A}^\times$ and
$\mu(X_0\cap\{1\le\lvert z\rvert\le m\})=\mu^1(D)\log m=\rho_k\log m$ (`muIdeleClass_univ_eq_residue`, the analytic class
number computation in QuadFormsKB); any other fundamental domain gives the same value on the $k^\times$-invariant set
$\{1\le\lvert z\rvert\le m\}$ (product formula, `IsFundamentalDomain.measure_set_eq`).
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.Units NumberField.mixedEmbedding MeasureTheory Set
open QuadFormsKB.Tamagawa.Measure.Weil
open scoped ENNReal Real

open scoped Pointwise

noncomputable section

namespace NumberFieldKB.WeilBNT

variable (F : Type) [Field F] [NumberField F]

/-- **Weil's Haar measure $\gamma$ on $k_{\mathbb A}^\times$** (V.§4, p. 94–95): $\sqrt{\lvert D\rvert}$ times QuadFormsKB's
`tamIdeles F`, so that $\gamma_v(r_v^\times)=1$ at the finite places (`weilIdeleMeasure_prod_OHatUnits`). -/
def weilIdeleMeasure : Measure (Adeles F)ˣ := ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) • tamIdeles F

/-- **Weil's constant** $c_k=2^{r_1}(2\pi)^{r_2}hR/e$ (V.§4, Prop. 9). -/
def weilCk : ℝ :=
  2 ^ nrRealPlaces F * (2 * π) ^ nrComplexPlaces F * classNumber F * regulator F / torsionOrder F

/-- The set $\{z\in k_{\mathbb A}^\times : 1\le\lvert z\rvert_{\mathbb A}\le m\}$. -/
def normShell (m : ℝ) : Set (Adeles F)ˣ := {g | 1 ≤ ideleNorm F g ∧ ideleNorm F g ≤ m}

variable {F}

/-- **Normalization of $\gamma$**: $\gamma(\{g : g_\infty\in A,\ g_f\in\hat{\mathcal O}^\times\})=\omega_\infty(A)$, i.e.
$\gamma_v(r_v^\times)=1$ for every finite place $v$, and $\gamma_\infty=\omega_\infty$ is Weil's measure at the infinite
places (`omegaInf_eq`). -/
theorem weilIdeleMeasure_prod_OHatUnits (A : Set (mixedSpace F)ˣ) :
    weilIdeleMeasure F (idelesEquiv F ⁻¹' (A ×ˢ (OHatUnits F : Set (FiniteAdeleRing (𝓞 F) F)ˣ))) = omegaInf F A := by
  have ha : 0 < Real.sqrt |(discr F : ℝ)| := sqrt_abs_discr_pos
  rw [weilIdeleMeasure, Measure.smul_apply, tamIdeles_prod, muFinUnits_OHatUnits, ohatVol, smul_eq_mul,
    ENNReal.ofReal_inv_of_pos ha, ← mul_assoc, mul_comm _ (omegaInf F A), mul_assoc,
    ENNReal.mul_inv_cancel (by simpa using ha) ENNReal.ofReal_ne_top, mul_one]

/-- $c_k=\sqrt{\lvert D\rvert}\,\rho_k$, $\rho_k$ = Mathlib's `dedekindZeta_residue F`. -/
theorem weilCk_eq : weilCk F = Real.sqrt |(discr F : ℝ)| * dedekindZeta_residue F := by
  have ha : 0 < Real.sqrt |(discr F : ℝ)| := sqrt_abs_discr_pos
  have hT : (0 : ℝ) < torsionOrder F := Nat.cast_pos.mpr (torsionOrder_pos F)
  rw [weilCk, dedekindZeta_residue_def]
  field_simp

/-- The principal idele `γ` as an element of `diagUnitsOne F`. -/
def toOne (γ : diagUnitsSub F) : diagUnitsOne F :=
  ⟨⟨(γ : (Adeles F)ˣ), diagUnitsSub_le_ideleOne γ.2⟩, Subgroup.mem_subgroupOf.2 γ.2⟩

theorem toOne_injective : Function.Injective (toOne (F := F)) := fun _ _ h =>
  Subtype.ext (congrArg (fun z : diagUnitsOne F => ((z : ideleOne F) : (Adeles F)ˣ)) h)

/-- Splitting is equivariant for principal ideles: first coordinate. -/
theorem ideleSplit_mul_fst (γ : diagUnitsSub F) (g : (Adeles F)ˣ) :
    (ideleSplit F ((γ : (Adeles F)ˣ) * g)).1 = ((toOne γ : diagUnitsOne F) : ideleOne F) * (ideleSplit F g).1 := by
  apply Subtype.ext
  have hγ : ideleLogNorm F γ = 1 := (mem_ideleOne_iff_logNorm _).1 (diagUnitsSub_le_ideleOne γ.2)
  change ((γ : (Adeles F)ˣ) * g) * (normSectionHom F (ideleLogNorm F ((γ : (Adeles F)ˣ) * g)))⁻¹ =
    (γ : (Adeles F)ˣ) * (g * (normSectionHom F (ideleLogNorm F g))⁻¹)
  rw [map_mul, hγ, one_mul, mul_assoc]

/-- Splitting is equivariant for principal ideles: second coordinate. -/
theorem ideleSplit_mul_snd (γ : diagUnitsSub F) (g : (Adeles F)ˣ) :
    (ideleSplit F ((γ : (Adeles F)ˣ) * g)).2 = (ideleSplit F g).2 := by
  have hγ : ideleLogNorm F γ = 1 := (mem_ideleOne_iff_logNorm _).1 (diagUnitsSub_le_ideleOne γ.2)
  change ideleLogNorm F ((γ : (Adeles F)ˣ) * g) = ideleLogNorm F g
  rw [map_mul, hγ, one_mul]

/-- The Haar measure of a preimage under the splitting. -/
theorem tamIdeles_ideleSplit_preimage (T : Set (ideleOne F × Multiplicative ℝ)) :
    tamIdeles F (ideleSplit F ⁻¹' T) = (muIdeleOne F).prod dtt T := by
  rw [← map_ideleSplit_tamIdeles]
  exact ((ideleSplit F).toHomeomorph.toMeasurableEquiv.map_apply T).symm

theorem tamIdeles_ideleSplit_fst_null {E : Set (ideleOne F)} (h : muIdeleOne F E = 0) :
    tamIdeles F (ideleSplit F ⁻¹' (Prod.fst ⁻¹' E)) = 0 := by
  rw [tamIdeles_ideleSplit_preimage, ← Set.prod_univ, Measure.prod_prod, h, zero_mul]

theorem mem_X0_smul (D : Set (ideleOne F)) (γ : diagUnitsSub F) (g : (Adeles F)ˣ) :
    γ • g ∈ ideleSplit F ⁻¹' (Prod.fst ⁻¹' D) ↔ toOne γ • (ideleSplit F g).1 ∈ D := by
  change (ideleSplit F ((γ : (Adeles F)ˣ) * g)).1 ∈ D ↔ _
  rw [ideleSplit_mul_fst]
  rfl

/-- The lift of a fundamental domain of `diagUnitsOne F` in `𝔸¹` to `𝔸ˣ` is a fundamental domain of `diagUnitsSub F`. -/
theorem isFundamentalDomain_X0 :
    IsFundamentalDomain (diagUnitsSub F) (ideleSplit F ⁻¹' (Prod.fst ⁻¹' ideleClassFD F)) (tamIdeles F) := by
  have hD := isFundamentalDomain_ideleClassFD (F := F)
  refine ⟨?_, ?_, ?_⟩
  · have hqmp : QuasiMeasurePreserving (fun g => (ideleSplit F g).1) (tamIdeles F) (muIdeleOne F) :=
      (Measure.quasiMeasurePreserving_fst (μ := muIdeleOne F) (ν := dtt)).comp
        ⟨(ideleSplit F).continuous.measurable, by rw [map_ideleSplit_tamIdeles]⟩
    exact hD.nullMeasurableSet.preimage hqmp
  · rw [ae_iff]
    have hN := ae_iff.1 hD.ae_covers
    refine measure_mono_null ?_ (tamIdeles_ideleSplit_fst_null hN)
    intro g hg
    simp only [mem_ofPred_eq, not_exists] at hg
    simp only [mem_preimage, mem_ofPred_eq, not_exists]
    intro δ
    have := hg ⟨δ.1.1, Subgroup.mem_subgroupOf.1 δ.2⟩
    rw [mem_X0_smul] at this
    exact this
  · intro γ γ' hne
    have hne' : (toOne γ⁻¹)⁻¹ ≠ (toOne γ'⁻¹)⁻¹ := fun h =>
      hne (inv_injective (toOne_injective (inv_injective h)))
    have hd := hD.aedisjoint hne'
    change tamIdeles F ((γ • _) ∩ (γ' • _)) = 0
    refine measure_mono_null ?_ (tamIdeles_ideleSplit_fst_null hd)
    intro g ⟨h1, h2⟩
    rw [mem_smul_set_iff_inv_smul_mem, mem_X0_smul] at h1 h2
    exact ⟨mem_smul_set_iff_inv_smul_mem.2 (by rwa [inv_inv]), mem_smul_set_iff_inv_smul_mem.2 (by rwa [inv_inv])⟩

/-- A measurable fundamental domain of the principal ideles $k^\times$ in $k_{\mathbb A}^\times$ exists. -/
theorem exists_isFundamentalDomain_ideles :
    ∃ X : Set (Adeles F)ˣ, IsFundamentalDomain (diagUnitsSub F) X (tamIdeles F) :=
  ⟨_, isFundamentalDomain_X0⟩

/-- **Weil, V.§4, Proposition 9**: for every measurable fundamental domain $X$ of $k^\times$ in $k_{\mathbb A}^\times$ and
every $m\ge1$, $\gamma(X\cap\{1\le\lvert z\rvert_{\mathbb A}\le m\})=c_k\log m$; that is, the image $C(m)$ of
$\{1\le\lvert z\rvert_{\mathbb A}\le m\}$ in $k_{\mathbb A}^\times/k^\times$ has measure $c_k\log m$. -/
@[kb "weil1973bnt" "Ch. V, §4, Prop. 9 (p. 95)"]
theorem weil_V_4_prop9 {X : Set (Adeles F)ˣ} (hX : IsFundamentalDomain (diagUnitsSub F) X (tamIdeles F))
    {m : ℝ} (hm : 1 ≤ m) :
    weilIdeleMeasure F (X ∩ normShell F m) = ENNReal.ofReal (weilCk F * Real.log m) := by
  have hX0 := isFundamentalDomain_X0 (F := F)
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm
  have hnorm : ∀ γ : diagUnitsSub F, ∀ g : (Adeles F)ˣ, ideleNorm F (γ • g) = ideleNorm F g := fun γ g => by
    change ideleNorm F ((γ : (Adeles F)ˣ) * g) = _
    rw [ideleNorm_mul, mem_ideleOne.1 (diagUnitsSub_le_ideleOne γ.2), one_mul]
  have hAm : MeasurableSet (normShell F m) :=
    (measurableSet_le measurable_const continuous_ideleNorm.measurable).inter
      (measurableSet_le continuous_ideleNorm.measurable measurable_const)
  have hAinv : ∀ γ : diagUnitsSub F, (fun x => γ • x) ⁻¹' normShell F m = normShell F m := fun γ => by
    ext x
    simp only [mem_preimage, normShell, mem_ofPred_eq, hnorm]
  have h1 := hX.measure_set_eq hX0 hAm hAinv
  have hset : normShell F m ∩ ideleSplit F ⁻¹' (Prod.fst ⁻¹' ideleClassFD F) =
      ideleSplit F ⁻¹' (ideleClassFD F ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) (Real.log m))) := by
    ext g
    have hp := ideleNorm_pos g
    simp only [normShell, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_prod, ideleSplit_apply_snd, toAdd_ofAdd,
      mem_Icc]
    rw [Real.log_nonneg_iff hp, Real.log_le_log_iff hp hm0]
    tauto
  have hD : muIdeleOne F (ideleClassFD F) = ENNReal.ofReal (dedekindZeta_residue F) := by
    rw [← muIdeleClass_univ isFundamentalDomain_ideleClassFD, muIdeleClass_univ_eq_residue]
  have hres := (dedekindZeta_residue_pos F).le
  have hs : 0 ≤ Real.sqrt |(discr F : ℝ)| := Real.sqrt_nonneg _
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hm
  rw [weilIdeleMeasure, Measure.smul_apply, smul_eq_mul, inter_comm, h1, hset, tamIdeles_ideleSplit_preimage,
    Measure.prod_prod, hD, dtt_apply]
  change _ * (_ * volume (Icc (0 : ℝ) (Real.log m))) = _
  rw [Real.volume_Icc, sub_zero, weilCk_eq, mul_assoc, ENNReal.ofReal_mul hs, ENNReal.ofReal_mul hres]

end NumberFieldKB.WeilBNT
