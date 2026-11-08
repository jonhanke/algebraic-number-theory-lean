import NumberFieldKB.Pontryagin.ApproxIdentity
import NumberFieldKB.Pontryagin.Inversion

/-!
# Weil's dual measure on a locally compact commutative group, given Bochner (Weil VII.§2, p. 105)

$G$ is a locally compact commutative Hausdorff group with a regular Haar measure $\alpha$. Weil's transform is
`AbstractFourier.fourierLCA α Φ` $=\Phi^*$, $\Phi^*(g^*)=\int\Phi(g)\langle g,g^*\rangle\,d\alpha$, "admissible" is
`AbstractFourier.IsAdmissible`, and `IsDualMeasure α β` (in `NumberFieldKB.Pontryagin.Inversion`) is Fourier inversion
$\Phi(g)=\int\Phi^*(g^*)\langle -g,g^*\rangle\,d\beta(g^*)$ for every admissible $\Phi$.

* **`inversion_admissible`**: Fourier inversion holds for every admissible $\Phi$ with $\beta$ = `dualHaar α hB`.
  Proof: for $k$ in the inversion class, $\int\Phi(y)k(y^{-1}x)\,dy$ and $\int\Psi(y)k(y^{-1}x)\,dy$, with
  $\Psi(x)=\int\hat\Phi(\xi)\xi(x)\,d\beta$, are both $\int\hat\Phi\hat k\,\xi(x)\,d\beta$ (inversion for $k$ and Fubini),
  so $\Phi-\Psi$ vanishes (`eq_zero_of_forall_integral_isInvClass`).
* **`isDualMeasure_dualHaar`**, **`exists_isDualMeasure`**: the dual measure exists and is a Haar measure.
* **`isDualMeasure_unique`**: a regular Haar measure on $G^*$ that is dual to $\alpha$ is `dualHaar α hB`.
* **`isDualMeasure_smul`**: the dual of $c\alpha$ is $c^{-1}\beta$ (Weil: "if $\alpha$ is replaced by $c\alpha$, $\alpha^*$
  is replaced by $c^{-1}\alpha^*$").

References: Weil, *Basic Number Theory*, VII.§2; Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed.,
Theorem 4.33 and the remarks after it.
-/

open MeasureTheory Topology Filter ComplexConjugate

noncomputable section

namespace NumberFieldKB.Pontryagin

universe u

open WeilBNT.AbstractFourier

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

lemma fourierLCA_eq_fhat_inv (μ : Measure G) (Φ : G → ℂ) (χ : PontryaginDual G) :
    fourierLCA μ Φ χ = fhat μ Φ χ⁻¹ := by
  rw [fhat_eq_fourierLCA, inv_inv]

lemma continuous_pairing_swap : Continuous fun p : G × PontryaginDual G => ((p.2 p.1 : Circle) : ℂ) :=
  continuous_pairing.comp continuous_swap

/-- **Fourier inversion for admissible functions** (given Bochner), for the dual Haar measure. -/
theorem inversion_admissible (hB : BochnerTheorem.{u}) {Φ : G → ℂ}
    (hΦ : IsAdmissible μ (dualHaar μ hB) Φ) (g : G) :
    Φ g = ∫ χ, fourierLCA μ Φ χ * ((χ g⁻¹ : Circle) : ℂ) ∂(dualHaar μ hB) := by
  obtain ⟨hΦc, hΦi, hΦs⟩ := hΦ
  set lam := dualHaar μ hB
  have : lam.IsHaarMeasure := isHaarMeasure_dualHaar
  -- `Φ̂ = Φ* ∘ inv` is integrable
  have hhat : fhat μ Φ = fun ξ => fourierLCA μ Φ ξ⁻¹ := funext fun ξ => fhat_eq_fourierLCA μ Φ ξ
  have hΦhi : Integrable (fhat μ Φ) lam := by rw [hhat]; exact hΦs.comp_inv
  have hΦhc : Continuous (fhat μ Φ) := continuous_fhat μ hΦi
  -- the right-hand side is `Ψ g` with `Ψ x = ∫ Φ̂ ξ ξ(x) dλ`
  set Ψ : G → ℂ := fun x => ∫ ξ, fhat μ Φ ξ * ((ξ x : Circle) : ℂ) ∂lam
  have hrhs : ∫ χ, fourierLCA μ Φ χ * ((χ g⁻¹ : Circle) : ℂ) ∂lam = Ψ g := by
    rw [← integral_inv_eq_self]
    congr 1 with ξ
    rw [fhat_eq_fourierLCA]
    congr 1
    rw [dual_inv_apply, map_inv, inv_inv]
  rw [hrhs]
  have hΨc : Continuous Ψ :=
    continuous_integral_of_dominated lam (F := fun x ξ => fhat μ Φ ξ * ((ξ x : Circle) : ℂ))
      ((hΦhc.comp continuous_snd).mul continuous_pairing_swap) continuous_const (fun _ => zero_le_one)
      (fun ξ => norm_nonneg (fhat μ Φ ξ)) hΦhi.norm (fun x ξ => by simp)
  -- `Φ - Ψ` is annihilated by the class
  have hD := eq_zero_of_forall_integral_isInvClass μ (hΦc.sub hΨc) fun k hk x => by
    obtain ⟨hki, hkinv⟩ := inversion_isInvClass (hB := hB) hk
    have hkc := hk.continuous_fhat
    have hkx : Continuous fun y => k (y⁻¹ * x) := hk.continuous.comp (continuous_inv.mul continuous_const)
    have hkxs : HasCompactSupport fun y => k (y⁻¹ * x) :=
      hk.hasCompactSupport.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulRight x))
    have hkxi : Integrable (fun y => k (y⁻¹ * x)) μ := hkx.integrable_of_hasCompactSupport hkxs
    obtain ⟨Ck, hCk⟩ := hk.continuous.bounded_above_of_compact_support hk.hasCompactSupport
    have hCΨ : ∀ y, ‖Ψ y‖ ≤ ∫ ξ, ‖fhat μ Φ ξ‖ ∂lam := fun y => by
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      congr 1 with ξ
      simp
    have i1 : Integrable (fun y => Φ y * k (y⁻¹ * x)) μ :=
      hΦi.mul_bdd hkx.aestronglyMeasurable (Eventually.of_forall fun y => hCk _)
    have i2 : Integrable (fun y => Ψ y * k (y⁻¹ * x)) μ :=
      hkxi.bdd_mul hΨc.aestronglyMeasurable (Eventually.of_forall hCΨ)
    simp only [Pi.sub_apply, sub_mul]
    rw [integral_sub i1 i2, sub_eq_zero]
    -- both are `∫ Φ̂ k̂ ξ(x) dλ`
    have e1 : ∫ y, Φ y * k (y⁻¹ * x) ∂μ =
        ∫ ξ, fhat μ k ξ * ((ξ x : Circle) : ℂ) * fhat μ Φ ξ ∂lam := by
      simp_rw [hkinv]
      simp_rw [← integral_const_mul]
      rw [integral_integral_swap_of_dominated μ lam
        (F := fun y ξ => Φ y * (fhat μ k ξ * ((ξ (y⁻¹ * x) : Circle) : ℂ)))
        (a := fun y => ‖Φ y‖) (b := fun ξ => ‖fhat μ k ξ‖)
        ((hΦc.comp continuous_fst).mul ((hkc.comp continuous_snd).mul
          (continuous_pairing.comp (continuous_snd.prodMk (continuous_fst.inv.mul continuous_const)))))
        hΦc.norm (fun _ => norm_nonneg _) hΦi.norm hkc.norm (fun _ => norm_nonneg _) hki.norm
        (fun y ξ => by simp)]
      congr 1 with ξ
      unfold fhat
      rw [← integral_const_mul]
      congr 1 with y
      rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]
      ring
    have e2 : ∫ y, Ψ y * k (y⁻¹ * x) ∂μ =
        ∫ ξ, fhat μ k ξ * ((ξ x : Circle) : ℂ) * fhat μ Φ ξ ∂lam := by
      simp only [Ψ]
      simp_rw [← integral_mul_const]
      rw [integral_integral_swap_of_dominated μ lam
        (F := fun y ξ => fhat μ Φ ξ * ((ξ y : Circle) : ℂ) * k (y⁻¹ * x))
        (a := fun y => ‖k (y⁻¹ * x)‖) (b := fun ξ => ‖fhat μ Φ ξ‖)
        (((hΦhc.comp continuous_snd).mul continuous_pairing_swap).mul (hkx.comp continuous_fst))
        hkx.norm (fun _ => norm_nonneg _) hkxi.norm hΦhc.norm (fun _ => norm_nonneg _) hΦhi.norm
        (fun y ξ => by simp [mul_comm])]
      congr 1 with ξ
      rw [← integral_mul_left_eq_self _ x, ← integral_inv_eq_self]
      have hpt : ∀ y, fhat μ Φ ξ * ((ξ (x * y⁻¹) : Circle) : ℂ) * k ((x * y⁻¹)⁻¹ * x) =
          (fhat μ Φ ξ * ((ξ x : Circle) : ℂ)) * (k y * conj ((ξ y : Circle) : ℂ)) := by
        intro y
        rw [show (x * y⁻¹)⁻¹ * x = y by group, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]
        ring
      simp only [hpt]
      rw [integral_const_mul]
      simp only [fhat]
      ring
    rw [e1, e2]
  have := congrFun hD g
  simpa [sub_eq_zero] using this

/-- **Weil VII.§2, p. 105**: `dualHaar μ hB` is the dual measure of `μ` (given Bochner). -/
theorem isDualMeasure_dualHaar (hB : BochnerTheorem.{u}) : IsDualMeasure μ (dualHaar μ hB) :=
  fun _ hΦ g => inversion_admissible hB hΦ g

/-- **The dual measure exists** and is a regular Haar measure on $G^*$ (given Bochner). -/
theorem exists_isDualMeasure (hB : BochnerTheorem.{u}) :
    ∃ β : Measure (PontryaginDual G), β.IsHaarMeasure ∧ β.Regular ∧ IsDualMeasure μ β :=
  ⟨dualHaar μ hB, isHaarMeasure_dualHaar, inferInstance, isDualMeasure_dualHaar hB⟩

/-- **Uniqueness of the dual measure**: a regular Haar measure on $G^*$ dual to $\mu$ is `dualHaar μ hB`. -/
theorem isDualMeasure_unique (hB : BochnerTheorem.{u}) (β : Measure (PontryaginDual G)) [β.IsHaarMeasure]
    [β.Regular] (h : IsDualMeasure μ β) : β = dualHaar μ hB := by
  set lam := dualHaar μ hB
  have : lam.IsHaarMeasure := isHaarMeasure_dualHaar
  have hβ := Measure.isMulLeftInvariant_eq_smul_of_regular β lam
  set c := Measure.haarScalarFactor β lam
  obtain ⟨k, hk, hk1⟩ := exists_isInvClass_ne_zero (μ := μ)
  obtain ⟨hki, -⟩ := inversion_isInvClass (hB := hB) hk
  have hsi : Integrable (fourierLCA μ k) lam := by
    have : fourierLCA μ k = fun χ => fhat μ k χ⁻¹ := funext fun χ => fourierLCA_eq_fhat_inv μ k χ
    rw [this]; exact hki.comp_inv
  have hadm : IsAdmissible μ β k := by
    refine ⟨hk.continuous, hk.integrable, ?_⟩
    rw [hβ]; exact hsi.smul_measure_nnreal
  have e1 := h k hadm 1
  have e2 := isDualMeasure_dualHaar (μ := μ) hB k ⟨hk.continuous, hk.integrable, hsi⟩ 1
  rw [hβ, integral_smul_nnreal_measure] at e1
  rw [← e2, NNReal.smul_def] at e1
  have hc : (c : ℝ) = 1 := by
    have := e1
    have h' : (1 - (c : ℂ)) * k 1 = 0 := by
      rw [sub_mul, one_mul]
      nth_rw 1 [this]
      rw [Complex.real_smul]
      ring
    have := (mul_eq_zero.mp h').resolve_right hk1
    exact_mod_cast (sub_eq_zero.mp this).symm
  have hc1 : c = 1 := by exact_mod_cast hc
  rw [hβ, hc1, one_smul]

/-- **Scaling** (Weil VII.§2, p. 105): if $\beta$ is dual to $\alpha$ then $c^{-1}\beta$ is dual to $c\alpha$. -/
theorem isDualMeasure_smul {α : Measure G} {β : Measure (PontryaginDual G)} (h : IsDualMeasure α β)
    {c : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤) : IsDualMeasure (c • α) (c⁻¹ • β) := by
  rintro Φ ⟨hΦc, hΦi, hΦs⟩ g
  have hft : fourierLCA (c • α) Φ = fun χ => (c.toReal : ℂ) * fourierLCA α Φ χ := by
    funext χ
    unfold fourierLCA
    rw [integral_smul_measure, Complex.real_smul]
  have hi : Integrable Φ α := (integrable_smul_measure hc0 hct).mp hΦi
  have hs : Integrable (fourierLCA α Φ) β := by
    rw [hft] at hΦs
    have := (integrable_smul_measure (ENNReal.inv_ne_zero.mpr hct) (ENNReal.inv_ne_top.mpr hc0)).mp hΦs
    have hc' : (c.toReal : ℂ) ≠ 0 := by
      exact_mod_cast (ENNReal.toReal_pos hc0 hct).ne'
    simpa [hc'] using this.const_mul (c.toReal : ℂ)⁻¹
  rw [h Φ ⟨hΦc, hi, hs⟩ g, hft, integral_smul_measure, ENNReal.toReal_inv]
  simp_rw [mul_assoc]
  rw [integral_const_mul, Complex.real_smul, ← mul_assoc]
  have hc' : (c.toReal : ℂ) ≠ 0 := by exact_mod_cast (ENNReal.toReal_pos hc0 hct).ne'
  push_cast
  field_simp

section SelfDual

/-- **Weil VII.§2, p. 105, existence of a self-dual measure**: under an identification $\iota:G\cong G^*$ of
topological groups, some regular Haar measure $\alpha$ on $G$ has dual measure $\iota_*\alpha$ (given Bochner). -/
theorem exists_isDualMeasure_map_self (hB : BochnerTheorem.{u}) (ι : G ≃ₜ* PontryaginDual G)
    (μ₀ : Measure G) [μ₀.IsHaarMeasure] [μ₀.Regular] :
    ∃ α : Measure G, α.IsHaarMeasure ∧ α.Regular ∧ IsDualMeasure α (α.map ι) := by
  set lam := dualHaar μ₀ hB
  have : lam.IsHaarMeasure := isHaarMeasure_dualHaar
  have : (μ₀.map ι).Regular := Measure.Regular.map (μ := μ₀) ι.toHomeomorph
  have hc := Measure.isMulLeftInvariant_eq_smul_of_regular (μ₀.map ι) lam
  set c := Measure.haarScalarFactor (μ₀.map ι) lam
  have hcpos : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure (μ₀.map ι) lam
  set s : NNReal := NNReal.sqrt c
  have hs : s ≠ 0 := (NNReal.sqrt_pos.mpr hcpos).ne'
  set t : NNReal := s⁻¹
  have ht : t ≠ 0 := inv_ne_zero hs
  have htc : t * c = t⁻¹ := by
    have : c = s * s := (NNReal.mul_self_sqrt c).symm
    rw [this, inv_inv]
    field_simp
    exact inv_mul_cancel₀ hs
  refine ⟨(t : ENNReal) • μ₀, Measure.IsHaarMeasure.smul μ₀ (ENNReal.coe_ne_zero.mpr ht) ENNReal.coe_ne_top,
    Measure.Regular.smul ENNReal.coe_ne_top, ?_⟩
  have hd := isDualMeasure_smul (isDualMeasure_dualHaar (μ := μ₀) hB) (ENNReal.coe_ne_zero.mpr ht)
    (ENNReal.coe_ne_top (r := t))
  have hmap : ((t : ENNReal) • μ₀).map ι = (t : ENNReal)⁻¹ • lam := by
    rw [Measure.map_smul, hc, ENNReal.smul_def, smul_smul, ← ENNReal.coe_mul, htc, ENNReal.coe_inv ht]
    exact ι.continuous.aemeasurable
  rw [hmap]
  exact hd

/-- **Weil VII.§2, p. 105, uniqueness of the self-dual measure** (given Bochner). -/
theorem isDualMeasure_map_self_unique (hB : BochnerTheorem.{u}) (ι : G ≃ₜ* PontryaginDual G)
    (α α' : Measure G) [α.IsHaarMeasure] [α.Regular] [α'.IsHaarMeasure] [α'.Regular]
    (h : IsDualMeasure α (α.map ι)) (h' : IsDualMeasure α' (α'.map ι)) : α' = α := by
  have hs := Measure.isMulLeftInvariant_eq_smul_of_regular α' α
  set s := Measure.haarScalarFactor α' α
  have hspos : 0 < s := Measure.haarScalarFactor_pos_of_isHaarMeasure α' α
  have hs0 : (s : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hspos.ne'
  have : (α.map ι).Regular := Measure.Regular.map (μ := α) ι.toHomeomorph
  have : (α'.map ι).Regular := Measure.Regular.map (μ := α') ι.toHomeomorph
  -- two regular Haar measures dual to `α'`
  have h1 : α'.map ι = (s : ENNReal) • α.map ι := by
    rw [hs, Measure.map_smul, ENNReal.smul_def]
    exact ι.continuous.aemeasurable
  have h2 := isDualMeasure_smul h hs0 ENNReal.coe_ne_top
  rw [← ENNReal.smul_def, ← hs] at h2
  have : ((s : ENNReal)⁻¹ • α.map ι).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top) (ENNReal.inv_ne_top.mpr hs0)
  have : ((s : ENNReal)⁻¹ • α.map ι).Regular := Measure.Regular.smul (ENNReal.inv_ne_top.mpr hs0)
  have e := (isDualMeasure_unique hB _ h').trans (isDualMeasure_unique hB _ h2).symm
  rw [h1] at e
  -- evaluate on a compact neighbourhood of `1`
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : PontryaginDual G)
  have hpos : 0 < α.map ι K := Measure.measure_pos_of_mem_nhds _ hK1
  have hfin : α.map ι K ≠ ⊤ := hK.measure_lt_top.ne
  have he := congrArg (fun m : Measure (PontryaginDual G) => m K) e
  simp only [Measure.smul_apply, smul_eq_mul] at he
  have hss : (s : ENNReal) = (s : ENNReal)⁻¹ := (ENNReal.mul_left_inj hpos.ne' hfin).mp he
  have hs1 : s = 1 := by
    have h3 : (s : ENNReal) * s = 1 := by
      nth_rw 2 [hss]; exact ENNReal.mul_inv_cancel hs0 ENNReal.coe_ne_top
    have h4 : (s : ℝ) * s = 1 := by exact_mod_cast h3
    have h5 : (0 : ℝ) ≤ s := s.coe_nonneg
    have : (s : ℝ) = 1 := by nlinarith [sq_nonneg ((s : ℝ) - 1)]
    exact_mod_cast this
  rw [hs, hs1, one_smul]

end SelfDual

end NumberFieldKB.Pontryagin
