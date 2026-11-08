import NumberFieldKB.WeilBNT.AdeleAnnihilator
import NumberFieldKB.WeilBNT.AdeleSelfDuality

/-!
# Weil, *Basic Number Theory*, VII.§2, Def. 4: differental ideles

$k$ is a number field (`K`), $k_{\mathbb A}$ Mathlib's adele ring ($k_\infty\times\mathbb A^{\mathrm{fin}}_k$) and
$\chi=\chi_\infty\prod_v\chi_v$ the standard character `chiA K` (`AdeleAnnihilator`): $\chi_\infty(x)=e(\operatorname{Tr}x)$
on $k_\infty$, $\chi_v=$ QuadFormsKB's `psiV v` at a finite place. The order $\nu(v)$ of $\chi_v$ (II.§5 Def. 4: the
largest $\nu$ with $\chi_v=1$ on $P_v^{-\nu}$) is the exponent $d_v$ of the local different: $\chi_v=1$ exactly on
$\mathfrak d_v^{-1}=P_v^{-d_v}$ (QuadFormsKB `invDiffV`, `diffExp`, `mem_invDiffV_iff`).

* `IsDifferentalIdele`: **Def. 4.** An idele $a$ is *differental* for $\chi$ if $\operatorname{ord}_v(a_v)=\nu(v)$ at every
  finite place, i.e. $\{y:\chi_v(xy)=1\text{ for all }x\in r_v\}=\{y: |a_vy|_v\le1\}$, and
  $\chi_v(x)=e(-a_vx)$ at the real places, $\chi_v(x)=e(-a_vx-\bar a_v\bar x)$ at the imaginary ones; at infinity this
  is stated for $k_\infty$ at once: $\chi_\infty(x)=e(-\operatorname{Tr}_\infty(a_\infty x))$ for all $x\in k_\infty$
  (equivalent to the placewise conditions, taking $x$ supported at one place).
* **`weil_VII_2_def4_exists`**: differental ideles exist ($a_\infty=-1$, $a_v=\varpi_v^{d_v}$).
* **`weil_VII_2_def4_unique`**: two differental ideles differ by an idele with component $1$ at infinity and units at
  every finite place.
-/

open IsDedekindDomain NumberField QuadFormsKB.Analysis NumberField.mixedEmbedding

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K

/-- **Def. 4.** The idele $a$ is differental for the standard character. -/
def IsDifferentalIdele (a : 𝔸ˣ) : Prop :=
  (∀ (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletion K),
      y ∈ invDiffV v ↔ Valued.v ((a : 𝔸).2 v * y) ≤ 1) ∧
    ∀ x : InfiniteAdeleRing K, chiInf K x =
      Real.fourierChar (-(traceInf (InfiniteAdeleRing.ringEquiv_mixedSpace K ((a : 𝔸).1 * x))))

/-- The finite component $\varpi_v^{d_v}$ of the differental idele. -/
def diffComp (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletion K :=
  QuadFormsKB.HN.ϖ v ^ (diffExp v : ℤ)

theorem diffComp_ne_zero (v : HeightOneSpectrum (𝓞 K)) : diffComp v ≠ 0 :=
  zpow_ne_zero _ (QuadFormsKB.HN.ϖ_ne_zero v)

/-- A family of local elements equal to $1$ wherever the different exponent vanishes is integral almost
everywhere. -/
theorem eventually_integral_of_diffExp (b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    (hb : ∀ v, diffExp v = 0 → b v = 1) : ∀ᶠ v in Filter.cofinite, b v ∈ v.adicCompletionIntegers K := by
  rw [Filter.eventually_cofinite]
  refine (finite_support_diffExp (F := K)).subset fun v hv => ?_
  simp only [Function.mem_support, ne_eq, Nat.cast_eq_zero]
  intro h
  exact hv (by rw [hb v h]; exact one_mem _)

/-- $\exp(-d)\,w\le 1$ iff $w\le\exp d$. -/
theorem exp_neg_mul_le_one_iff (d : ℤ) (w : WithZero (Multiplicative ℤ)) :
    WithZero.exp (-d) * w ≤ 1 ↔ w ≤ WithZero.exp d := by
  have h : WithZero.exp (-d) * WithZero.exp d = 1 := by
    rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  constructor
  · intro h1
    calc w = WithZero.exp d * (WithZero.exp (-d) * w) := by
          rw [← mul_assoc, mul_comm (WithZero.exp d), h, one_mul]
      _ ≤ WithZero.exp d * 1 := mul_le_mul' le_rfl h1
      _ = WithZero.exp d := mul_one _
  · intro h1
    calc WithZero.exp (-d) * w ≤ WithZero.exp (-d) * WithZero.exp d := mul_le_mul' le_rfl h1
      _ = 1 := h

/-- The differental idele $(-1,(\varpi_v^{d_v})_v)$. -/
def diffIdele : 𝔸ˣ where
  val := ((-1 : InfiniteAdeleRing K),
    (⟨diffComp, eventually_integral_of_diffExp _ fun v h => by simp [diffComp, h]⟩ :
      FiniteAdeleRing (𝓞 K) K))
  inv := ((-1 : InfiniteAdeleRing K),
    (⟨fun v => (diffComp v)⁻¹, eventually_integral_of_diffExp _ fun v h => by simp [diffComp, h]⟩ :
      FiniteAdeleRing (𝓞 K) K))
  val_inv := Prod.ext (show (-1 : InfiniteAdeleRing K) * -1 = 1 by simp) (FiniteAdeleRing.ext K fun v => mul_inv_cancel₀ (diffComp_ne_zero v))
  inv_val := Prod.ext (show (-1 : InfiniteAdeleRing K) * -1 = 1 by simp) (FiniteAdeleRing.ext K fun v => inv_mul_cancel₀ (diffComp_ne_zero v))

/-- **Def. 4**: differental ideles exist. -/
@[kb "weil1973bnt" "Ch. VII, §2, Def. 4 (differental ideles exist; number field, standard character)"]
theorem weil_VII_2_def4_exists : ∃ a : 𝔸ˣ, IsDifferentalIdele a := by
  refine ⟨diffIdele, fun v y => ?_, fun x => ?_⟩
  · change y ∈ invDiffV v ↔ Valued.v (diffComp v * y) ≤ 1
    rw [mem_invDiffV_iff, map_mul, diffComp, valued_ϖ_zpow, exp_neg_mul_le_one_iff]
  · change chiInf K x = Real.fourierChar
      (-(traceInf (InfiniteAdeleRing.ringEquiv_mixedSpace K ((-1 : InfiniteAdeleRing K) * x))))
    rw [neg_one_mul, map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace K) x, traceInf_neg, neg_neg]
    rfl

/-- If $\psi\circ d=1$ for a real linear form $d$, then $d=0$. -/
theorem linear_eq_zero_of_fourierChar_eq_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d : V →ₗ[ℝ] ℝ) (hd : ∀ x, Real.fourierChar (d x) = 1) : d = 0 := by
  ext x
  have hint : ∀ y, ∃ n : ℤ, d y = n := by
    intro y
    have := hd y
    rw [Real.fourierChar_apply', Circle.exp_eq_one] at this
    obtain ⟨n, hn⟩ := this
    exact ⟨n, by
      have hp : (2 * Real.pi) ≠ 0 := by positivity
      apply mul_left_cancel₀ hp; linarith⟩
  obtain ⟨m, hm⟩ := hint x
  by_contra hne
  have hm0 : (m : ℝ) ≠ 0 := by
    intro h; apply hne; simp [hm, h]
  obtain ⟨n, hn⟩ := hint ((1 / (2 * m) : ℝ) • x)
  rw [map_smul, hm, smul_eq_mul] at hn
  have : (1 / (2 * (m : ℝ))) * m = 1 / 2 := by field_simp
  rw [this] at hn
  have h2 : (1 : ℝ) = 2 * n := by linarith
  have : (1 : ℤ) = 2 * n := by exact_mod_cast h2
  omega

/-- Two nonzero local elements with the same unit-ball condition have the same valuation. -/
theorem valued_eq_of_iff {F : Type*} [Field F] [Valued F (WithZero (Multiplicative ℤ))] {α β : F}
    (hα : α ≠ 0) (hβ : β ≠ 0) (h : ∀ y, Valued.v (α * y) ≤ 1 ↔ Valued.v (β * y) ≤ 1) :
    Valued.v α = Valued.v β := by
  have h1 := (h α⁻¹).1 (by rw [mul_inv_cancel₀ hα, map_one])
  have h2 := (h β⁻¹).2 (by rw [mul_inv_cancel₀ hβ, map_one])
  have hva : Valued.v α ≠ 0 := (map_ne_zero _).2 hα
  have hvb : Valued.v β ≠ 0 := (map_ne_zero _).2 hβ
  rw [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 hva), one_mul] at h1
  rw [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 hvb), one_mul] at h2
  exact le_antisymm h2 h1

/-- **Def. 4**: a differental idele is unique up to an idele with component $1$ at infinity and unit components at
the finite places. -/
@[kb "weil1973bnt" "Ch. VII, §2, Def. 4 (uniqueness up to units)"]
theorem weil_VII_2_def4_unique {a b : 𝔸ˣ} (ha : IsDifferentalIdele a) (hb : IsDifferentalIdele b) :
    ((a / b : 𝔸ˣ) : 𝔸).1 = 1 ∧ ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((a / b : 𝔸ˣ) : 𝔸).2 v) = 1 := by
  have hab := Units.mul_inv b
  have h1 : (b : 𝔸).1 * ((b⁻¹ : 𝔸ˣ) : 𝔸).1 = 1 := congrArg Prod.fst hab
  have hd : ((a / b : 𝔸ˣ) : 𝔸) = (a : 𝔸) * ((b⁻¹ : 𝔸ˣ) : 𝔸) := by
    rw [div_eq_mul_inv, Units.val_mul]
  have hnz : ∀ (c : 𝔸ˣ) (v : HeightOneSpectrum (𝓞 K)), (c : 𝔸).2 v ≠ 0 := fun c v =>
    left_ne_zero_of_mul_eq_one (congrArg (fun z : 𝔸 => z.2 v) (Units.mul_inv c))
  have hinf : (a : 𝔸).1 = (b : 𝔸).1 := by
    have hz : ∀ z : mixedSpace K,
        Real.fourierChar (-(traceInf (InfiniteAdeleRing.ringEquiv_mixedSpace K (a : 𝔸).1 * z))) =
        Real.fourierChar (-(traceInf (InfiniteAdeleRing.ringEquiv_mixedSpace K (b : 𝔸).1 * z))) := by
      intro z
      have e := (ha.2 ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z)).symm.trans
        (hb.2 ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z))
      rwa [map_mul, map_mul, RingEquiv.apply_symm_apply] at e
    have h0 := linear_eq_zero_of_fourierChar_eq_one
      (traceMulL (InfiniteAdeleRing.ringEquiv_mixedSpace K (a : 𝔸).1) -
        traceMulL (InfiniteAdeleRing.ringEquiv_mixedSpace K (b : 𝔸).1)) (fun z => by
      have e := hz z
      rw [AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, inv_inj] at e
      rw [LinearMap.sub_apply, traceMulL_apply, traceMulL_apply, AddChar.map_sub_eq_div, e, div_self'])
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
      (traceMulL_injective (sub_eq_zero.mp h0))
  refine ⟨?_, fun v => ?_⟩
  · rw [hd, Prod.fst_mul, hinf]
    exact h1
  · rw [hd, Prod.snd_mul]
    have hv : Valued.v ((a : 𝔸).2 v) = Valued.v ((b : 𝔸).2 v) :=
      valued_eq_of_iff (hnz a v) (hnz b v) fun y => (ha.1 v y).symm.trans (hb.1 v y)
    have h3 : (((b : 𝔸).2 * ((b⁻¹ : 𝔸ˣ) : 𝔸).2) : FiniteAdeleRing (𝓞 K) K) v = 1 := by
      have := congrArg Prod.snd hab
      rw [Prod.snd_mul, Prod.snd_one] at this
      rw [this]; rfl
    rw [show ((a : 𝔸).2 * ((b⁻¹ : 𝔸ˣ) : 𝔸).2) v = (a : 𝔸).2 v * ((b⁻¹ : 𝔸ˣ) : 𝔸).2 v from rfl,
      map_mul, hv, ← map_mul]
    have h4 : (b : 𝔸).2 v * ((b⁻¹ : 𝔸ˣ) : 𝔸).2 v = 1 := h3
    rw [h4, map_one]

end NumberFieldKB.WeilBNT
