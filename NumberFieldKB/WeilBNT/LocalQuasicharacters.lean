import NumberFieldKB.LocalZeta.NonArchimedean
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, VII.§3, Prop. 8: quasicharacters of $k_v^\times$

$k$ is a number field (`F`), $v$ a finite place, $K=k_v$ (`v.adicCompletion F`, a $p$-field), $R^\times$ its unit group
(QuadFormsKB `unitsVSub v`, the maximal compact subgroup of $K^\times$), $\pi$ the prime element `ϖU v` (QuadFormsKB),
and $\operatorname{mod}_K(x)=\lvert x\rvert_v$ the module (Mathlib's `distribHaarChar`, equal to $N(v)^{-\operatorname{ord}_v x}$,
NumberFieldKB `distribHaarChar_of_mem_shell`). A *quasicharacter* of $K^\times$ is a continuous morphism
$K^\times\to\mathbb C^\times$; it is *principal* (Weil VII.§3 Def. 6) if it is trivial on $R^\times$.

* **`weil_VII_3_prop8_principal`**: the principal quasicharacters of $K^\times$ are exactly the
  $x\mapsto\operatorname{mod}_K(x)^s$, $s\in\mathbb C$.
* **`weil_VII_3_prop8`**: every quasicharacter $\omega$ is $\omega(x)=\operatorname{mod}_K(x)^s\,\psi(x)$ with $\psi$ a
  character ($\lvert\psi\rvert=1$) of $K^\times$ such that $\psi(\pi)=1$;
  **`weil_VII_3_prop8_unique`**: the two factors are unique (the product is direct).

Weil's proof (Prop. 7 and its Corollaries for $G=K^\times=R^\times\times\pi^{\mathbb Z}$, $\omega_1=\operatorname{mod}_K$):
choose $s$ with $\operatorname{mod}_K(\pi)^s=\omega(\pi)$; then $\psi=\omega\operatorname{mod}_K^{-s}$ has $\psi(\pi)=1$,
and it is a character because $R^\times$ is compact (Lemma 3).
-/

open IsDedekindDomain NumberField MeasureTheory Topology
open QuadFormsKB QuadFormsKB.Analysis QuadFormsKB.Tamagawa.Measure.Weil NumberFieldKB.LocalZeta

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

theorem unitsVSub_eq' : unitsVSub v = {u : Fvˣ | (u : Fv) ∈ v.adicCompletionIntegers F ∧
    ((u⁻¹ : Fvˣ) : Fv) ∈ v.adicCompletionIntegers F} := by
  ext u
  simp only [unitsVSub, Set.mem_ofPred_eq, HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val,
    map_inv₀]
  constructor
  · intro h; rw [h, inv_one]; exact ⟨le_rfl, le_rfl⟩
  · rintro ⟨h1, h2⟩
    have h0 : Valued.v (u : Fv) ≠ 0 := by simp
    have := mul_le_mul' (le_refl (Valued.v (u : Fv))) h2
    rw [mul_inv_cancel₀ h0, mul_one] at this
    exact le_antisymm h1 this

theorem isCompact_unitsVSub' : IsCompact (unitsVSub v) := by
  have hO : IsCompact (v.adicCompletionIntegers F : Set Fv) := by
    have := QuadFormsKB.Analysis.isCompact_latticeV v 0
    convert this using 1
    ext x; simp [QuadFormsKB.Analysis.mem_latticeV, HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [unitsVSub_eq', Units.isEmbedding_embedProduct.isCompact_iff]
  have hK : IsCompact ((v.adicCompletionIntegers F : Set Fv) ×ˢ
      (MulOpposite.op '' (v.adicCompletionIntegers F : Set Fv))) :=
    hO.prod (hO.image MulOpposite.continuous_op)
  have hC : IsClosed {p : Fv × Fvᵐᵒᵖ | p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1} :=
    (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)) continuous_const).inter
      (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)
  have hset : Units.embedProduct Fv '' {u : Fvˣ | (u : Fv) ∈ v.adicCompletionIntegers F ∧
      ((u⁻¹ : Fvˣ) : Fv) ∈ v.adicCompletionIntegers F} =
      ((v.adicCompletionIntegers F : Set Fv) ×ˢ (MulOpposite.op '' (v.adicCompletionIntegers F : Set Fv))) ∩
        {p : Fv × Fvᵐᵒᵖ | p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨u, ⟨hu, hu'⟩, h⟩
      simp only [Units.embedProduct_apply, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨hu, ⟨_, hu', rfl⟩⟩, u.mul_inv, u.inv_mul⟩
    · rintro ⟨⟨hx, ⟨y', hy', rfl⟩⟩, h1, h2⟩
      exact ⟨⟨x, y', h1, h2⟩, ⟨hx, hy'⟩, rfl⟩
  rw [hset]
  exact hK.inter_right hC

theorem distribHaarChar_pos'(x : Fvˣ) : (0 : ℝ) < (distribHaarChar Fv x : ℝ) := by
  have h : distribHaarChar Fv x * distribHaarChar Fv x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h))

/-- $x\mapsto\operatorname{mod}_K(x)^s$ as a homomorphism to $\mathbb C^\times$. -/
def modPow (s : ℂ) : Fvˣ →* ℂˣ where
  toFun x := Units.mk0 (((distribHaarChar Fv x : ℝ) : ℂ) ^ s) (by
    rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨h, -⟩
    exact (distribHaarChar_pos' v x).ne' (by exact_mod_cast h))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [map_mul, NNReal.coe_mul, Complex.ofReal_mul, Units.val_mul, Units.val_mk0]
    exact Complex.mul_cpow_ofReal_nonneg (distribHaarChar_pos' v x).le (distribHaarChar_pos' v y).le s

theorem modPow_apply (s : ℂ) (x : Fvˣ) : (modPow v s x : ℂ) = ((distribHaarChar Fv x : ℝ) : ℂ) ^ s := rfl

theorem continuous_modPow (s : ℂ) : Continuous (modPow v s) := by
  rw [Units.continuous_iff]
  have hc : Continuous fun x : Fvˣ => ((distribHaarChar Fv x : ℝ) : ℂ) ^ s :=
    Continuous.cpow (Complex.continuous_ofReal.comp (continuous_distribHaarChar_v v).subtype_val) continuous_const
      (fun x => Or.inl (by simpa using distribHaarChar_pos' v x))
  refine ⟨hc, ?_⟩
  have : (fun x : Fvˣ => ((modPow v s x)⁻¹ : ℂˣ).val) = fun x => (((distribHaarChar Fv x : ℝ) : ℂ) ^ s)⁻¹ := by
    ext x; rw [Units.val_inv_eq_inv_val]; rfl
  simp only [this]
  exact hc.inv₀ fun x => (modPow v s x).ne_zero

theorem modPow_unit (s : ℂ) {u : Fvˣ} (hu : u ∈ unitsVSub v) : modPow v s u = 1 := by
  ext
  rw [modPow_apply, distribHaarChar_eq_one_of_mem_unitsVSub hu]; simp

theorem decomp (x : Fvˣ) : ∃ (n : ℤ) (w : Fvˣ), w ∈ unitsVSub v ∧ x = ϖU v ^ n * w := by
  have h := mem_shell_log v x
  generalize (-WithZero.log (Valued.v (x : Fv))) = n at h
  rw [shell_eq_preimage] at h
  exact ⟨n, ϖU v ^ (-n) * x, h, by group⟩

theorem norm_eq_one_of_mem_unitsVSub (ω : Fvˣ →* ℂˣ) (hω : Continuous ω) {u : Fvˣ} (hu : u ∈ unitsVSub v) :
    ‖(ω u : ℂ)‖ = 1 := by
  have hpow : ∀ (x : Fvˣ), x ∈ unitsVSub v → ∀ n : ℕ, x ^ n ∈ unitsVSub v := by
    intro x hx n
    show Valued.v (((x ^ n : Fvˣ)) : Fv) = 1
    have : Valued.v (x : Fv) = 1 := hx
    simp [this]
  have hinv : ∀ (x : Fvˣ), x ∈ unitsVSub v → x⁻¹ ∈ unitsVSub v := by
    intro x hx
    show Valued.v (((x⁻¹ : Fvˣ)) : Fv) = 1
    have : Valued.v (x : Fv) = 1 := hx
    simp [this]
  have hc : Continuous fun x : Fvˣ => ‖(ω x : ℂ)‖ :=
    continuous_norm.comp (Units.continuous_val.comp hω)
  obtain ⟨M, hM⟩ := ((isCompact_unitsVSub' v).image hc).isBounded.subset_closedBall 0
  have hb : ∀ x ∈ unitsVSub v, ‖(ω x : ℂ)‖ ≤ M := fun x hx => by
    have := hM ⟨x, hx, rfl⟩
    rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] at this
  have hnot : ∀ x ∈ unitsVSub v, ¬ 1 < ‖(ω x : ℂ)‖ := fun x hx h1 => by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h1
    have := hb (x ^ n) (hpow x hx n)
    rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
    linarith
  have hne : ‖(ω u : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ω u).ne_zero
  refine le_antisymm (not_lt.mp (hnot u hu)) (not_lt.mp fun hlt => hnot u⁻¹ (hinv u hu) ?_)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv]
  exact one_lt_inv₀ (lt_of_le_of_ne (norm_nonneg _) hne.symm) |>.mpr hlt

theorem exists_s (ω : Fvˣ →* ℂˣ) : ∃ s : ℂ, modPow v s (ϖU v) = ω (ϖU v) := by
  have hm0 := modV_pos' v
  have hm1 := modV_lt_one v
  have hlog : Complex.log ((modV v : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_log hm0.le]
    exact_mod_cast (Real.log_neg hm0 hm1).ne
  refine ⟨Complex.log (ω (ϖU v) : ℂ) / Complex.log ((modV v : ℝ) : ℂ), ?_⟩
  ext
  rw [modPow_apply]
  change (((modV v : ℝ) : ℂ)) ^ _ = _
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hm0.ne'), mul_div_cancel₀ _ hlog,
    Complex.exp_log (ω (ϖU v)).ne_zero]

theorem eq_modPow (ω : Fvˣ →* ℂˣ) (s : ℂ) (hu : ∀ u ∈ unitsVSub v, ω u = 1)
    (hp : modPow v s (ϖU v) = ω (ϖU v)) : ω = modPow v s := by
  ext x
  have h := mem_shell_log v x
  rw [apply_of_mem_shell v hu h, apply_of_mem_shell v (fun u hu => modPow_unit v s hu) h, hp]

/-- **Weil, VII.§3, Prop. 8, first assertion.** A quasicharacter $\omega$ of $K^\times=k_v^\times$ is principal (trivial
on $R^\times$) if and only if $\omega(x)=\operatorname{mod}_K(x)^s$ for some $s\in\mathbb C$. -/
@[kb "weil1973bnt" "Ch. VII, §3, Prop. 8, first assertion (K = k_v, k a number field)"]
theorem weil_VII_3_prop8_principal (ω : Fvˣ →* ℂˣ) (_hω : Continuous ω) :
    (∀ u ∈ unitsVSub v, ω u = 1) ↔
      ∃ s : ℂ, ∀ x : Fvˣ, (ω x : ℂ) = ((distribHaarChar Fv x : ℝ) : ℂ) ^ s := by
  constructor
  · intro hu
    obtain ⟨s, hs⟩ := exists_s v ω
    exact ⟨s, fun x => by rw [eq_modPow v ω s hu hs]; rfl⟩
  · rintro ⟨s, hs⟩ u hu
    have : ω = modPow v s := by ext x; exact hs x
    rw [this]; exact modPow_unit v s hu

/-- **Weil, VII.§3, Prop. 8, second assertion (existence).** Every quasicharacter $\omega$ of $K^\times=k_v^\times$ is
$\omega(x)=\operatorname{mod}_K(x)^s\,\psi(x)$ with $s\in\mathbb C$ and $\psi$ a character of $K^\times$ (continuous, of
absolute value $1$) with $\psi(\pi)=1$. -/
@[kb "weil1973bnt" "Ch. VII, §3, Prop. 8, second assertion (K = k_v, k a number field)"]
theorem weil_VII_3_prop8 (ω : Fvˣ →* ℂˣ) (hω : Continuous ω) :
    ∃ (s : ℂ) (ψ : Fvˣ →* ℂˣ), Continuous ψ ∧ ψ (ϖU v) = 1 ∧ (∀ x, ‖(ψ x : ℂ)‖ = 1) ∧
      ∀ x : Fvˣ, (ω x : ℂ) = ((distribHaarChar Fv x : ℝ) : ℂ) ^ s * (ψ x : ℂ) := by
  obtain ⟨s, hs⟩ := exists_s v ω
  refine ⟨s, ω * (modPow v s)⁻¹, hω.mul (continuous_modPow v s).inv, ?_, ?_, ?_⟩
  · simp [hs]
  · intro x
    obtain ⟨n, w, hw, rfl⟩ := decomp v x
    have e1 : (ω * (modPow v s)⁻¹) (ϖU v ^ n * w) = ω w := by
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_zpow, ← hs, modPow_unit v s hw]
      group
    rw [e1]
    exact norm_eq_one_of_mem_unitsVSub v ω hω hw
  · intro x
    have := (modPow v s x).ne_zero
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, ← modPow_apply]
    field_simp

/-- **Weil, VII.§3, Prop. 8, second assertion (the product is direct).** If
$\operatorname{mod}_K^s\,\psi=\operatorname{mod}_K^{s'}\,\psi'$ with $\psi(\pi)=\psi'(\pi)=1$, then $\psi=\psi'$ and
$\operatorname{mod}_K^s=\operatorname{mod}_K^{s'}$. -/
@[kb "weil1973bnt" "Ch. VII, §3, Prop. 8, second assertion (K = k_v, k a number field)"]
theorem weil_VII_3_prop8_unique (s s' : ℂ) (ψ ψ' : Fvˣ →* ℂˣ) (hψ : ψ (ϖU v) = 1) (hψ' : ψ' (ϖU v) = 1)
    (h : ∀ x : Fvˣ, ((distribHaarChar Fv x : ℝ) : ℂ) ^ s * (ψ x : ℂ) =
      ((distribHaarChar Fv x : ℝ) : ℂ) ^ s' * (ψ' x : ℂ)) :
    ψ = ψ' ∧ ∀ x : Fvˣ, ((distribHaarChar Fv x : ℝ) : ℂ) ^ s = ((distribHaarChar Fv x : ℝ) : ℂ) ^ s' := by
  have hψ1 : ∀ x, ψ x = ψ' x := by
    intro x
    obtain ⟨n, w, hw, rfl⟩ := decomp v x
    have := h w
    simp only [distribHaarChar_eq_one_of_mem_unitsVSub hw, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow,
      one_mul] at this
    have e := Units.ext this
    simp [map_mul, map_zpow, hψ, hψ', e]
  refine ⟨MonoidHom.ext hψ1, fun x => ?_⟩
  have := h x
  rw [hψ1 x] at this
  exact mul_right_cancel₀ (ψ' x).ne_zero this

end NumberFieldKB.WeilBNT
