import NumberFieldKB.HeckeL.Dual
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The functional equation of Hecke L-functions and the root number

$F$ is a number field, $\chi$ a Hecke character, $\Lambda(s,\chi)$ its completed $L$-function (`completedHeckeL`,
$=A(\chi)^{s/2}L_\infty(s,\chi)L(s,\chi)$ for $\operatorname{Re}s+\sigma>1$).

* **`rootNumber χ`** $= W(\chi) = i^{m(\chi)}\,A(\chi)^{1/2}\,E(\chi)/C_\chi$: $i^{m(\chi)}$ from the archimedean places
  ($m(\chi) = \sum_{w\text{ real}}e_w+\sum_{w\text{ complex}}|k_w|$), $E(\chi)$ (`dualConst`) the product of the local
  constants of the dual test function (Gauss-sum integrals $\varepsilon_v(\chi)$ at the ramified places), $C_\chi$
  (`stdConst`) those of the test function.
* **The functional equation** (`completedHeckeL_functional_equation`):
  $$\Lambda(s,\chi) = W(\chi)\,\Lambda(1-s,\chi^{-1})$$
  for every $s\in\mathbb C$ if $\chi$ is not a power of the norm, and for $s\ne-c,1-c$ if $\chi = \|\cdot\|^c$
  (`IsPoleFree`). For unitary $\chi$, $\chi^{-1} = \bar\chi$.
* **$|W(\chi)| = 1$ for unitary $\chi$** (`norm_rootNumber`), by Tate's global argument: applying the functional
  equation twice gives $W(\chi)W(\chi^{-1}) = 1$, and $\Lambda(\bar s,\chi^{-1}) = \overline{\Lambda(s,\chi)}$
  (`completedHeckeL_inv_conj`) gives $W(\chi^{-1}) = \overline{W(\chi)}$.

Tate's thesis, Cassels–Fröhlich Ch. XV, §4.4–4.5 [unverified locators]; Neukirch, *Algebraic Number Theory*,
Ch. VII, Thm. 8.5 [unverified locator].
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Filter Set
open Topology
open QuadFormsKB QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical ComplexConjugate

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

open GlobalZeta LocalZeta

/-! ### The identity theorem off a finite set -/

theorem exists_re_lt_notMem (S : Finset ℂ) (a : ℝ) : ∃ z : ℂ, z.re < a ∧ z ∉ S := by
  have hinj : Function.Injective fun n : ℕ => (((a - 1 - n : ℝ)) : ℂ) := fun m n h => by
    have := Complex.ofReal_injective h
    exact_mod_cast (by linarith : (m : ℝ) = n)
  obtain ⟨z, ⟨n, rfl⟩, hz⟩ := (Set.infinite_range_of_injective hinj).exists_notMem_finset S
  refine ⟨_, ?_, hz⟩
  simp only [Complex.ofReal_re]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem exists_re_gt_notMem (S : Finset ℂ) (a : ℝ) : ∃ z : ℂ, a < z.re ∧ z ∉ S := by
  obtain ⟨z, hz, hzS⟩ := exists_re_lt_notMem (S.image fun z => -z) (-a)
  refine ⟨-z, by simp; linarith, fun h => hzS ?_⟩
  exact Finset.mem_image.mpr ⟨-z, h, neg_neg z⟩

/-- **Identity theorem off a finite set**: two functions holomorphic off the finite set $S$ that agree on an open set
$W$ meeting the complement of $S$ agree off $S$. -/
theorem eq_of_eqOn_open {f g : ℂ → ℂ} (S : Finset ℂ) (hf : ∀ s ∉ S, DifferentiableAt ℂ f s)
    (hg : ∀ s ∉ S, DifferentiableAt ℂ g s) {W : Set ℂ} (hW : IsOpen W) {z₀ : ℂ} (hz₀ : z₀ ∈ W) (hz₀S : z₀ ∉ S)
    (heq : ∀ s ∈ W, f s = g s) {s : ℂ} (hs : s ∉ S) : f s = g s := by
  set U : Set ℂ := (S : Set ℂ)ᶜ
  have hU : IsOpen U := S.finite_toSet.isClosed.isOpen_compl
  have hpc : IsPreconnected U :=
    (S.finite_toSet.countable.isPathConnected_compl_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)).isConnected.isPreconnected
  have hfa : AnalyticOnNhd ℂ f U :=
    DifferentiableOn.analyticOnNhd (fun t ht => (hf t ht).differentiableWithinAt) hU
  have hga : AnalyticOnNhd ℂ g U :=
    DifferentiableOn.analyticOnNhd (fun t ht => (hg t ht).differentiableWithinAt) hU
  have hev : f =ᶠ[𝓝 z₀] g := by
    filter_upwards [hW.mem_nhds hz₀] with t ht using heq t ht
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hpc hz₀S hev hs

/-! ### Poles -/

/-- $s$ is not a pole of $\Lambda(\cdot,\chi)$: if $\chi = \|\cdot\|^c$ then $s\ne-c$ and $s\ne1-c$. -/
def IsPoleFree (χ : HeckeCharacter F) (s : ℂ) : Prop :=
  ∀ c : ℂ, χ = HeckeCharacter.normPow F c → s ≠ -c ∧ s ≠ 1 - c

theorem differentiableAt_completedHeckeL {χ : HeckeCharacter F} {s : ℂ} (hs : IsPoleFree χ s) :
    DifferentiableAt ℂ (completedHeckeL χ) s := by
  by_cases h : ∃ c : ℂ, χ = HeckeCharacter.normPow F c
  · obtain ⟨c, rfl⟩ := h
    exact differentiableAt_completedHeckeL_normPow c (hs c rfl).1 (hs c rfl).2
  · push Not at h
    exact differentiable_completedHeckeL h s

theorem isPoleFree_inv_one_sub {χ : HeckeCharacter F} {s : ℂ} (hs : IsPoleFree χ s) :
    IsPoleFree χ⁻¹ (1 - s) := by
  intro c hc
  have hχ : χ = HeckeCharacter.normPow F (-c) := by
    rw [HeckeCharacter.normPow_neg, ← hc]
    exact (inv_inv χ).symm
  obtain ⟨h1, h2⟩ := hs (-c) hχ
  constructor
  · intro h; apply h2; linear_combination -h
  · intro h; apply h1; linear_combination -h

/-- The exceptional set: $\{-c, 1-c\}$ if $\chi = \|\cdot\|^c$, empty otherwise. -/
def poleSet (χ : HeckeCharacter F) : Finset ℂ :=
  if h : ∃ c : ℂ, χ = HeckeCharacter.normPow F c then {-h.choose, 1 - h.choose} else ∅

theorem isPoleFree_of_notMem {χ : HeckeCharacter F} {s : ℂ} (hs : s ∉ poleSet χ) : IsPoleFree χ s := by
  intro c hc
  have h : ∃ c : ℂ, χ = HeckeCharacter.normPow F c := ⟨c, hc⟩
  have hc' : h.choose = c := normPow_injective (h.choose_spec.symm.trans hc)
  rw [poleSet, dif_pos h, hc'] at hs
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
  exact hs

theorem notMem_poleSet {χ : HeckeCharacter F} {s : ℂ} (hs : IsPoleFree χ s) : s ∉ poleSet χ := by
  unfold poleSet
  split_ifs with h
  · obtain ⟨h1, h2⟩ := hs _ h.choose_spec
    simp [h1, h2]
  · simp

/-! ### The root number and the functional equation -/

/-- **The root number** $W(\chi) = i^{m(\chi)}A(\chi)^{1/2}E(\chi)/C_\chi$ (`archExp`, `condDisc`, `dualConst`,
`stdConst`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.5 [unverified locator] (the constant of the functional equation)"]
def rootNumber (χ : HeckeCharacter F) : ℂ :=
  Complex.I ^ archExp χ * ((condDisc χ : ℝ) : ℂ) ^ (1 / 2 : ℂ) * dualConst χ / (stdConst χ : ℂ)

theorem condDisc_cpow_ne_zero (χ : HeckeCharacter F) (z : ℂ) : ((condDisc χ : ℝ) : ℂ) ^ z ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => condDisc_ne_zero χ h.1

/-- The functional equation in the half-plane $\operatorname{Re}s>\sigma+1$:
$\Lambda(1-s,\chi) = W(\chi)\Lambda(s,\chi^{-1})$. -/
theorem completedHeckeL_one_sub_of_re (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re - χ.shift) :
    completedHeckeL χ (1 - s) = rootNumber χ * completedHeckeL χ⁻¹ s := by
  have hs' : 1 < s.re + (χ⁻¹).shift := by rw [shift_inv]; linarith
  rw [completedHeckeL, globalZetaCont_one_sub _ _ hs, globalZeta_fourier_heckePhi χ hs,
    completedHeckeL_eq χ⁻¹ hs', condDisc_inv, rootNumber, zetaConst]
  have hπ : ((Real.pi : ℂ) ^ nrComplexPlaces F) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  have hC : ((stdConst χ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (stdConst_pos χ).ne'
  have hA : ((condDisc χ : ℝ) : ℂ) ^ ((1 - s) / 2) * ((condDisc χ : ℝ) : ℂ) ^ s =
      ((condDisc χ : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ((condDisc χ : ℝ) : ℂ) ^ (s / 2) := by
    rw [← Complex.cpow_add _ _ (condDisc_ne_zero χ), ← Complex.cpow_add _ _ (condDisc_ne_zero χ)]
    congr 1
    ring
  calc ((condDisc χ : ℝ) : ℂ) ^ ((1 - s) / 2) *
        ((Real.pi : ℂ) ^ nrComplexPlaces F * (stdConst χ : ℂ))⁻¹ *
        (Complex.I ^ archExp χ * (Real.pi : ℂ) ^ nrComplexPlaces F * dualConst χ *
          ((condDisc χ : ℝ) : ℂ) ^ s * gammaInf χ⁻¹ s * heckeL χ⁻¹ s)
      = (((condDisc χ : ℝ) : ℂ) ^ ((1 - s) / 2) * ((condDisc χ : ℝ) : ℂ) ^ s) *
          (Complex.I ^ archExp χ * dualConst χ / (stdConst χ : ℂ)) * (gammaInf χ⁻¹ s * heckeL χ⁻¹ s) := by
        field_simp
    _ = _ := by rw [hA]; field_simp

/-- **The functional equation of the Hecke $L$-function**: $\Lambda(s,\chi) = W(\chi)\,\Lambda(1-s,\chi^{-1})$, for every
$s$ that is not a pole (every $s$ unless $\chi = \|\cdot\|^c$, then $s\ne-c,1-c$). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.5 [unverified locator] (Λ(s, χ) = W(χ) Λ(1 − s, χ̄))"]
theorem completedHeckeL_functional_equation (χ : HeckeCharacter F) {s : ℂ} (hs : IsPoleFree χ s) :
    completedHeckeL χ s = rootNumber χ * completedHeckeL χ⁻¹ (1 - s) := by
  have hf : ∀ t ∉ poleSet χ, DifferentiableAt ℂ (completedHeckeL χ) t := fun t ht =>
    differentiableAt_completedHeckeL (isPoleFree_of_notMem ht)
  have hg : ∀ t ∉ poleSet χ, DifferentiableAt ℂ (fun t => rootNumber χ * completedHeckeL χ⁻¹ (1 - t)) t :=
    fun t ht => ((differentiableAt_completedHeckeL (isPoleFree_inv_one_sub (isPoleFree_of_notMem ht))).comp t
      ((differentiableAt_const _).sub differentiableAt_id)).const_mul _
  obtain ⟨z₀, hz₀, hz₀S⟩ := exists_re_lt_notMem (poleSet χ) (-χ.shift)
  refine eq_of_eqOn_open (poleSet χ) hf hg (isOpen_lt Complex.continuous_re continuous_const) hz₀ hz₀S
    (fun t ht => ?_) (notMem_poleSet hs)
  have ht' : 1 < (1 - t).re - χ.shift := by
    have : t.re < -χ.shift := ht
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have := completedHeckeL_one_sub_of_re χ ht'
  rwa [sub_sub_cancel] at this

/-! ### $W(\chi)W(\chi^{-1}) = 1$ -/

theorem heckeCharacter_inv_inv (χ : HeckeCharacter F) : χ⁻¹⁻¹ = χ := inv_inv χ

theorem completedHeckeL_ne_zero (χ : HeckeCharacter F) {s : ℂ} (hs : 1 < s.re + χ.shift) :
    completedHeckeL χ s ≠ 0 := by
  rw [completedHeckeL_eq χ hs]
  exact mul_ne_zero (mul_ne_zero (condDisc_cpow_ne_zero χ _) (gammaInf_ne_zero χ (by linarith)))
    (heckeL_ne_zero χ hs)

/-- **$W(\chi)\,W(\chi^{-1}) = 1$**: the functional equation applied twice. -/
theorem rootNumber_mul_rootNumber_inv (χ : HeckeCharacter F) : rootNumber χ * rootNumber χ⁻¹ = 1 := by
  obtain ⟨s, hs, hsS⟩ := exists_re_gt_notMem (poleSet χ) (1 - χ.shift)
  have hpf := isPoleFree_of_notMem hsS
  have h1 := completedHeckeL_functional_equation χ hpf
  have h2 := completedHeckeL_functional_equation χ⁻¹ (isPoleFree_inv_one_sub hpf)
  rw [sub_sub_cancel, heckeCharacter_inv_inv] at h2
  have hne := completedHeckeL_ne_zero χ (s := s) (by linarith)
  rw [h2, ← mul_assoc] at h1
  have := mul_right_cancel₀ hne (h1.symm.trans (one_mul _).symm)
  exact this

/-! ### Complex conjugation -/

theorem conj_ofReal_cpow {a : ℝ} (ha : 0 < a) (z : ℂ) : conj ((a : ℂ) ^ z) = (a : ℂ) ^ conj z := by
  have harg : (a : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ha.le]; exact Real.pi_pos.ne
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

theorem conj_eq_inv_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : conj z = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
  simp

theorem conj_of_re_eq_zero {t : ℂ} (ht : t.re = 0) : conj t = -t := by
  apply Complex.ext <;> simp [ht]

/-- For unitary $\chi$: $\overline{L_\infty(\bar s,\chi)} = L_\infty(s,\chi^{-1})$. -/
theorem conj_gammaInf {χ : HeckeCharacter F} (hχ : χ.IsUnitary) (s : ℂ) :
    conj (gammaInf χ (conj s)) = gammaInf χ⁻¹ s := by
  have hσ : χ.shift = 0 := (χ.shift_eq_zero_iff).mpr hχ
  unfold gammaInf
  rw [map_mul, map_prod, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [← Complex.Gammaℝ_conj, map_add, map_add, Complex.conj_conj, Complex.conj_natCast,
      conj_of_re_eq_zero (by rw [χ.re_realExponent w.2, hσ]), realExponent_inv, eW_inv]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [← Complex.Gammaℂ_conj, map_add, map_add, Complex.conj_conj, map_div₀, map_div₀, Complex.conj_natCast,
      map_ofNat, conj_of_re_eq_zero (by rw [χ.re_complexExponent w.2, hσ, mul_zero]),
      (complexComponent_inv_eq χ w.2).1, kW_inv, Int.natAbs_neg]

/-- For unitary $\chi$ and $\operatorname{Re}s>1$: $\overline{L(\bar s,\chi)} = L(s,\chi^{-1})$. -/
theorem conj_heckeL {χ : HeckeCharacter F} (hχ : χ.IsUnitary) {s : ℂ} (hs : 1 < s.re) :
    conj (heckeL χ (conj s)) = heckeL χ⁻¹ s := by
  have hσ : χ.shift = 0 := (χ.shift_eq_zero_iff).mpr hχ
  have h1 := (hasProd_heckeL χ (s := conj s) (by rw [Complex.conj_re, hσ, add_zero]; exact hs)).map
    (starRingEnd ℂ) Complex.continuous_conj
  have h2 := hasProd_heckeL χ⁻¹ (s := s) (by rw [shift_inv, hσ, neg_zero, add_zero]; exact hs)
  refine h1.unique ?_
  convert h2 using 1
  funext v
  simp only [Function.comp_apply]
  unfold localL
  by_cases hv : χ.IsUnramifiedAt v
  · have hv' : (χ⁻¹).IsUnramifiedAt v := (isUnramifiedAt_inv_iff χ v).mpr hv
    rw [if_pos hv, if_pos hv', map_inv₀, map_sub, map_one, rV, rV, map_mul, inv_finiteComponent,
      conj_ofReal_cpow (normV_pos v), map_neg, Complex.conj_conj]
    have hn : ‖((χ.finiteComponent v (Analysis.ϖU v) : ℂˣ) : ℂ)‖ = 1 := by
      rw [HeckeCharacter.norm_finiteComponent_eq_rpow, hσ, Real.rpow_zero]
    rw [conj_eq_inv_of_norm_eq_one hn]
  · have hv' : ¬ (χ⁻¹).IsUnramifiedAt v := by rwa [isUnramifiedAt_inv_iff]
    rw [if_neg hv, if_neg hv', map_one]

/-- For unitary $\chi$ and $\operatorname{Re}s>1$: $\Lambda(s,\chi^{-1}) = \overline{\Lambda(\bar s,\chi)}$. -/
theorem completedHeckeL_inv_eq_conj_of_re {χ : HeckeCharacter F} (hχ : χ.IsUnitary) {s : ℂ} (hs : 1 < s.re) :
    completedHeckeL χ⁻¹ s = conj (completedHeckeL χ (conj s)) := by
  have hσ : χ.shift = 0 := (χ.shift_eq_zero_iff).mpr hχ
  rw [completedHeckeL_eq χ⁻¹ (by rw [shift_inv, hσ, neg_zero, add_zero]; exact hs),
    completedHeckeL_eq χ (by rw [Complex.conj_re, hσ, add_zero]; exact hs), map_mul, map_mul,
    conj_ofReal_cpow (condDisc_pos χ), conj_gammaInf hχ, conj_heckeL hχ hs, condDisc_inv, map_div₀,
    Complex.conj_conj, map_ofNat]

theorem isPoleFree_inv_conj {χ : HeckeCharacter F} (hχ : χ.IsUnitary) {s : ℂ} (hs : IsPoleFree χ s) :
    IsPoleFree χ⁻¹ (conj s) := by
  intro c hc
  have hχc : χ = HeckeCharacter.normPow F (-c) := by
    rw [HeckeCharacter.normPow_neg, ← hc]
    exact (inv_inv χ).symm
  have hre : c.re = 0 := by
    have := (HeckeCharacter.isUnitary_normPow_iff (F := F) (-c)).mp (hχc ▸ hχ)
    simpa using this
  obtain ⟨h1, h2⟩ := hs (-c) hχc
  have hcc : conj c = -c := conj_of_re_eq_zero hre
  constructor
  · intro h
    apply h1
    have := congrArg conj h
    rw [Complex.conj_conj, map_neg, hcc] at this
    linear_combination this
  · intro h
    apply h2
    have := congrArg conj h
    rw [Complex.conj_conj, map_sub, map_one, hcc] at this
    linear_combination this

/-- **Conjugation symmetry** for unitary $\chi$: $\Lambda(\bar s,\chi^{-1}) = \overline{\Lambda(s,\chi)}$ for every $s$ that is
not a pole. -/
theorem completedHeckeL_inv_conj {χ : HeckeCharacter F} (hχ : χ.IsUnitary) {s : ℂ} (hs : IsPoleFree χ s) :
    completedHeckeL χ⁻¹ (conj s) = conj (completedHeckeL χ s) := by
  set S : Finset ℂ := poleSet χ⁻¹ ∪ (poleSet χ).image conj
  have hf : ∀ t ∉ S, DifferentiableAt ℂ (completedHeckeL χ⁻¹) t := fun t ht =>
    differentiableAt_completedHeckeL (isPoleFree_of_notMem fun h => ht (Finset.mem_union_left _ h))
  have hg : ∀ t ∉ S, DifferentiableAt ℂ (fun t => conj (completedHeckeL χ (conj t))) t := fun t ht => by
    have hct : conj t ∉ poleSet χ := fun h =>
      ht (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨conj t, h, Complex.conj_conj t⟩))
    have := (differentiableAt_completedHeckeL (isPoleFree_of_notMem hct)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  obtain ⟨z₀, hz₀, hz₀S⟩ := exists_re_gt_notMem S 1
  have hsS : conj s ∉ S := by
    simp only [S, Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
    refine ⟨notMem_poleSet (isPoleFree_inv_conj hχ hs), fun x hx hxs => ?_⟩
    have : x = s := by rw [← Complex.conj_conj x, hxs, Complex.conj_conj]
    exact notMem_poleSet hs (this ▸ hx)
  have := eq_of_eqOn_open S hf hg (isOpen_lt continuous_const Complex.continuous_re) hz₀ hz₀S
    (fun t ht => completedHeckeL_inv_eq_conj_of_re hχ ht) hsS
  rwa [Complex.conj_conj] at this

/-! ### $|W(\chi)| = 1$ -/

/-- **$W(\chi^{-1}) = \overline{W(\chi)}$** for unitary $\chi$. -/
theorem rootNumber_inv_eq_conj {χ : HeckeCharacter F} (hχ : χ.IsUnitary) :
    rootNumber χ⁻¹ = conj (rootNumber χ) := by
  have hχ' : (χ⁻¹).IsUnitary := by
    have hσ : χ.shift = 0 := (χ.shift_eq_zero_iff).mpr hχ
    rw [← HeckeCharacter.shift_eq_zero_iff, shift_inv, hσ, neg_zero]
  set S : Finset ℂ := ((poleSet χ⁻¹).image fun x => 1 - x) ∪ ((poleSet χ).image fun x => 1 - conj x) ∪
    (poleSet χ⁻¹).image conj
  obtain ⟨t, ht, htS⟩ := exists_re_gt_notMem S 1
  set s := 1 - t
  have hS1 : s ∉ poleSet χ⁻¹ := fun h => htS (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨s, h, by simp [s]⟩)))
  have hS2 : conj s ∉ poleSet χ := fun h => htS (Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨conj s, h, by simp [s]⟩)))
  have hS3 : conj t ∉ poleSet χ⁻¹ := fun h => htS (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨conj t, h, Complex.conj_conj t⟩))
  -- the functional equation for χ⁻¹ at s
  have e1 := completedHeckeL_functional_equation χ⁻¹ (isPoleFree_of_notMem hS1)
  rw [heckeCharacter_inv_inv] at e1
  -- conjugation symmetry at conj s, the functional equation for χ at conj s, conjugation symmetry for χ⁻¹
  have e2 := completedHeckeL_inv_conj hχ (isPoleFree_of_notMem hS2)
  rw [Complex.conj_conj] at e2
  have e3 := completedHeckeL_functional_equation χ (isPoleFree_of_notMem hS2)
  have e4 := completedHeckeL_inv_conj hχ' (isPoleFree_of_notMem hS3)
  rw [heckeCharacter_inv_inv, Complex.conj_conj] at e4
  have hts : 1 - conj s = conj t := by simp [s]
  rw [e3, map_mul, hts, ← e4] at e2
  have hne : completedHeckeL χ (1 - s) ≠ 0 := by
    rw [show 1 - s = t by simp [s]]
    exact completedHeckeL_ne_zero χ (by rw [(χ.shift_eq_zero_iff).mpr hχ, add_zero]; exact ht)
  have : rootNumber χ⁻¹ * completedHeckeL χ (1 - s) = conj (rootNumber χ) * completedHeckeL χ (1 - s) := by
    rw [← e1, e2, show (1 - s) = t by simp [s]]
  exact mul_right_cancel₀ hne this

/-- **$|W(\chi)| = 1$** for a unitary Hecke character $\chi$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.5 [unverified locator] (|W(χ)| = 1)"]
theorem norm_rootNumber {χ : HeckeCharacter F} (hχ : χ.IsUnitary) : ‖rootNumber χ‖ = 1 := by
  have h := rootNumber_mul_rootNumber_inv χ
  rw [rootNumber_inv_eq_conj hχ, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have h' : ‖rootNumber χ‖ ^ 2 = 1 := by exact_mod_cast h
  have := norm_nonneg (rootNumber χ)
  nlinarith [sq_nonneg (‖rootNumber χ‖ - 1)]

end

end NumberFieldKB.HeckeL
