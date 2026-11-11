import NumberFieldKB.MilneCFT.Ch5Ideles
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Weil, *Basic Number Theory*, Chapter XIII, §4, Lemma 6: the ideles of $\mathbb Q$

Weil's Lemma 6 (p. 257): there is a direct product decomposition
$$\mathbb Q_{\mathbb A}^\times=\mathbb Q^\times\times\mathbb R_+^\times\times\prod_p\mathbb Z_p^\times ,$$
where $\mathbb R_+^\times$ and the $\mathbb Z_p^\times$ are subgroups of the quasifactors $\mathbb R^\times=\mathbb Q_\infty^\times$
and $\mathbb Q_p^\times$ of $\mathbb Q_{\mathbb A}^\times$.

Weil's proof: the morphism $r(z)=\operatorname{sgn}(z_\infty)\prod_p\lvert z_p\rvert_p^{-1}$ of $\mathbb Q_{\mathbb A}^\times$
into $\mathbb Q^\times$ is the identity on $\mathbb Q^\times$ (by the product formula, IV.§4 Thm. 5), so it splits
$\mathbb Q_{\mathbb A}^\times=\mathbb Q^\times\times R$ with $R=\ker r=\mathbb R_+^\times\times\prod_p\mathbb Z_p^\times$.
Here the same splitting is proved through the ideal of an idele: $\lvert z_p\rvert_p^{-1}=p^{\operatorname{ord}_p z_p}$, so
$\prod_p\lvert z_p\rvert_p^{-1}$ is the positive generator of the fractional ideal $\prod_p p^{\operatorname{ord}_p z_p}$ of
$z$ (NumberFieldKB `MilneCFT.ideleToIdeal`, whose kernel is the ideles that are units at every finite place,
`MilneCFT.item_4_1`).

Main declarations (Mathlib's `IdeleGroup (𝓞 ℚ) ℚ`; the infinite place of $\mathbb Q$ is `Rat.infinitePlace`, a real
place, and $\mathbb Q_\infty$ is identified with $\mathbb R$ by `Completion.ringEquivRealOfIsReal`):
* **`ratInfComp z`**: the real number $z_\infty$;
* **`ratUnitIdeles`**: Weil's $R=\mathbb R_+^\times\times\prod_p\mathbb Z_p^\times$: the ideles with $z_\infty>0$ and
  $\lvert z_p\rvert_p=1$ for every prime $p$;
* **`weil_XIII_4_lemma6_inf`**, **`weil_XIII_4_lemma6_sup`**: $\mathbb Q^\times\cap R=\{1\}$ and
  $\mathbb Q^\times R=\mathbb Q_{\mathbb A}^\times$ (an internal direct product of the commutative group);
* **`weil_XIII_4_lemma6`**: $(\xi,u)\mapsto\xi u$ is a bijection $\mathbb Q^\times\times R\to\mathbb Q_{\mathbb A}^\times$.
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.WeilBNT

/-- The archimedean component $z_\infty\in\mathbb R$ of an idele $z$ of $\mathbb Q$. -/
def ratInfComp (z : IdeleGroup (𝓞 ℚ) ℚ) : ℝ :=
  Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace ((z : AdeleRing (𝓞 ℚ) ℚ).1 Rat.infinitePlace)

theorem ratInfComp_mul (z z' : IdeleGroup (𝓞 ℚ) ℚ) : ratInfComp (z * z') = ratInfComp z * ratInfComp z' := by
  unfold ratInfComp
  rw [← map_mul]; rfl

theorem ratInfComp_one : ratInfComp 1 = 1 := by
  unfold ratInfComp
  rw [← map_one (Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)]; rfl

theorem ratInfComp_inv (z : IdeleGroup (𝓞 ℚ) ℚ) : ratInfComp z⁻¹ = (ratInfComp z)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← ratInfComp_mul, inv_mul_cancel, ratInfComp_one]

/-- The archimedean component of a principal idele is the real number $\xi$. -/
theorem ratInfComp_unitEmbedding (a : ℚˣ) :
    ratInfComp (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) = (a : ℝ) := by
  unfold ratInfComp
  rw [Completion.ringEquivRealOfIsReal_apply]
  have := NumberFieldKB.MilneCFT.extEmbedding_coe (K := ℚ) Rat.isReal_infinitePlace (a : ℚ)
  refine this.trans ?_
  simp

instance : IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ)
    Rat.ringOfIntegersEquiv.symm.surjective

/-- Every unit fractional ideal of $\mathbb Z$ (= `𝓞 ℚ`) is principal. -/
theorem exists_principal (I : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) :
    ∃ ξ : ℚˣ, toPrincipalIdeal (𝓞 ℚ) ℚ ξ = I := by
  obtain ⟨g, hg⟩ := (FractionalIdeal.isPrincipal (R := 𝓞 ℚ) (K := ℚ) (I : FractionalIdeal (𝓞 ℚ)⁰ ℚ)).principal
  have hI : (I : FractionalIdeal (𝓞 ℚ)⁰ ℚ) = FractionalIdeal.spanSingleton (𝓞 ℚ)⁰ g := by
    rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_spanSingleton]
    exact hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    have : (I : FractionalIdeal (𝓞 ℚ)⁰ ℚ) = 0 := by rw [hI]; exact map_zero _
    exact I.ne_zero this
  exact ⟨Units.mk0 g hg0, by rw [toPrincipalIdeal_eq_iff]; exact hI.symm⟩

theorem toPrincipalIdeal_neg (ξ : ℚˣ) : toPrincipalIdeal (𝓞 ℚ) ℚ (-ξ) = toPrincipalIdeal (𝓞 ℚ) ℚ ξ := by
  rw [toPrincipalIdeal_eq_iff, Units.val_neg, coe_toPrincipalIdeal]
  refine FractionalIdeal.spanSingleton_eq_spanSingleton.mpr ⟨-1, ?_⟩
  simp

/-- A rational number whose principal idele is a unit at every finite place is $\pm1$. -/
theorem eq_one_or_neg_one_of_valuation_eq_one (ξ : ℚˣ) (h : ∀ v : HeightOneSpectrum (𝓞 ℚ),
    Valued.v (((IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ ξ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1) :
    (ξ : ℚ) = 1 ∨ (ξ : ℚ) = -1 := by
  have h1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ (ξ : ℚ) = 1 := by
    intro v
    have := h v
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact this
  have hx : (ξ : ℚ) ∈ (algebraMap (𝓞 ℚ) ℚ).range :=
    HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ _ fun v => (h1 v).le
  have hy : (ξ⁻¹ : ℚˣ).val ∈ (algebraMap (𝓞 ℚ) ℚ).range :=
    HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ _ fun v => by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h1 v, inv_one]
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  have hxy : x * y = 1 := by
    apply IsFractionRing.injective (𝓞 ℚ) ℚ
    rw [map_mul, hx, hy, map_one]; exact Units.mul_inv ξ
  have hu : IsUnit (Rat.ringOfIntegersEquiv x) :=
    (IsUnit.of_mul_eq_one (Rat.ringOfIntegersEquiv y) (by rw [← map_mul, hxy, map_one]))
  rcases Int.isUnit_iff.mp hu with h | h
  · left
    rw [← hx, ← Rat.ringOfIntegersEquiv_apply_coe, h]; simp
  · right
    rw [← hx, ← Rat.ringOfIntegersEquiv_apply_coe, h]; simp

/-- **Weil's $R=\mathbb R_+^\times\times\prod_p\mathbb Z_p^\times$** inside $\mathbb Q_{\mathbb A}^\times$: the ideles $z$ with
$z_\infty>0$ and $\lvert z_p\rvert_p=1$ (i.e. $z_p\in\mathbb Z_p^\times$) at every prime $p$. -/
def ratUnitIdeles : Subgroup (IdeleGroup (𝓞 ℚ) ℚ) where
  carrier := {z | 0 < ratInfComp z ∧ ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((z : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1}
  mul_mem' {z z'} hz hz' := by
    refine ⟨?_, fun v => ?_⟩
    · rw [ratInfComp_mul]; exact mul_pos hz.1 hz'.1
    · have h1 := hz.2 v
      have h2 := hz'.2 v
      change Valued.v (NumberFieldKB.MilneCFT.ideleFinAt z v) = 1 at h1
      change Valued.v (NumberFieldKB.MilneCFT.ideleFinAt z' v) = 1 at h2
      show Valued.v (NumberFieldKB.MilneCFT.ideleFinAt (z * z') v) = 1
      rw [NumberFieldKB.MilneCFT.ideleFinAt_mul, map_mul, h1, h2, one_mul]
  one_mem' := ⟨by rw [ratInfComp_one]; exact one_pos, fun v => by
    show Valued.v (NumberFieldKB.MilneCFT.ideleFinAt (1 : IdeleGroup (𝓞 ℚ) ℚ) v) = 1
    rw [NumberFieldKB.MilneCFT.ideleFinAt_one, map_one]⟩
  inv_mem' {z} hz := by
    refine ⟨?_, fun v => ?_⟩
    · rw [ratInfComp_inv]; exact inv_pos.mpr hz.1
    · have h1 := hz.2 v
      change Valued.v (NumberFieldKB.MilneCFT.ideleFinAt z v) = 1 at h1
      show Valued.v (NumberFieldKB.MilneCFT.ideleFinAt z⁻¹ v) = 1
      rw [NumberFieldKB.MilneCFT.ideleFinAt_inv, map_inv₀, h1, inv_one]

/-- **Weil, XIII.§4, Lemma 6, first half**: $\mathbb Q^\times\cap(\mathbb R_+^\times\times\prod_p\mathbb Z_p^\times)=\{1\}$
in $\mathbb Q_{\mathbb A}^\times$ (a rational number that is a unit at every prime is $\pm1$, and it is positive). -/
@[kb "weil1973bnt" "Ch. XIII, §4, Lemma 6 (p. 257)"]
theorem weil_XIII_4_lemma6_inf :
    IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ ⊓ ratUnitIdeles = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro z ⟨⟨ξ, rfl⟩, hpos, hval⟩
  rcases eq_one_or_neg_one_of_valuation_eq_one ξ hval with h | h
  · have : ξ = 1 := Units.ext h
    rw [this, map_one]
  · exfalso
    rw [ratInfComp_unitEmbedding, h] at hpos
    norm_num at hpos

/-- **Weil, XIII.§4, Lemma 6, second half**: $\mathbb Q_{\mathbb A}^\times=\mathbb Q^\times\cdot(\mathbb R_+^\times\times
\prod_p\mathbb Z_p^\times)$. -/
@[kb "weil1973bnt" "Ch. XIII, §4, Lemma 6 (p. 257)"]
theorem weil_XIII_4_lemma6_sup :
    IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ ⊔ ratUnitIdeles = ⊤ := by
  rw [eq_top_iff]
  intro z _
  have hz0 : ratInfComp z ≠ 0 := by
    intro h0
    have := ratInfComp_mul z z⁻¹
    rw [mul_inv_cancel, ratInfComp_one, h0, zero_mul] at this
    exact zero_ne_one this.symm
  obtain ⟨ξ, hξ⟩ := exists_principal (NumberFieldKB.MilneCFT.ideleToIdeal ℚ z)
  obtain ⟨η, hη, hηpos⟩ : ∃ η : ℚˣ, toPrincipalIdeal (𝓞 ℚ) ℚ η = NumberFieldKB.MilneCFT.ideleToIdeal ℚ z ∧
      0 < (η : ℝ) * ratInfComp z := by
    have hne : (ξ : ℝ) * ratInfComp z ≠ 0 := mul_ne_zero (by exact_mod_cast ξ.ne_zero) hz0
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨-ξ, by rw [toPrincipalIdeal_neg]; exact hξ, ?_⟩
      push_cast
      linarith
    · exact ⟨ξ, hξ, hgt⟩
  have hη0 : (η : ℝ) ≠ 0 := by exact_mod_cast η.ne_zero
  rw [Subgroup.mem_sup]
  refine ⟨IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ η, ⟨η, rfl⟩,
    IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ η⁻¹ * z, ⟨?_, ?_⟩, ?_⟩
  · rw [ratInfComp_mul, ratInfComp_unitEmbedding]
    have : ((η⁻¹ : ℚˣ) : ℝ) * ratInfComp z = ((η : ℝ) * ratInfComp z) * ((η : ℝ)⁻¹) ^ 2 := by
      push_cast
      field_simp
    rw [this]
    positivity
  · refine (NumberFieldKB.MilneCFT.item_4_1 (K := ℚ)).2 _ |>.mp ?_
    rw [map_mul, NumberFieldKB.MilneCFT.ideleToIdeal_unitEmbedding, map_inv, hη, inv_mul_cancel]
  · simp

/-- **Weil, XIII.§4, Lemma 6** (direct product decomposition
$\mathbb Q_{\mathbb A}^\times=\mathbb Q^\times\times\mathbb R_+^\times\times\prod_p\mathbb Z_p^\times$): every idele of
$\mathbb Q$ is uniquely $\xi u$ with $\xi\in\mathbb Q^\times$ and $u\in\mathbb R_+^\times\times\prod_p\mathbb Z_p^\times$. -/
@[kb "weil1973bnt" "Ch. XIII, §4, Lemma 6 (p. 257)"]
theorem weil_XIII_4_lemma6 :
    Function.Bijective fun p : ℚˣ × ratUnitIdeles =>
      IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ p.1 * (p.2 : IdeleGroup (𝓞 ℚ) ℚ) := by
  constructor
  · rintro ⟨ξ, u⟩ ⟨ξ', u'⟩ h
    simp only at h
    have key : IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ (ξ'⁻¹ * ξ) =
        (u' : IdeleGroup (𝓞 ℚ) ℚ) * (u : IdeleGroup (𝓞 ℚ) ℚ)⁻¹ := by
      rw [map_mul, map_inv, eq_mul_inv_iff_mul_eq, mul_assoc, h, ← mul_assoc, ← map_inv, ← map_mul,
        inv_mul_cancel, map_one, one_mul]
    have hmem : IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ (ξ'⁻¹ * ξ) ∈
        IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ ⊓ ratUnitIdeles :=
      ⟨⟨_, rfl⟩, by rw [key]; exact Subgroup.mul_mem _ u'.2 (Subgroup.inv_mem _ u.2)⟩
    rw [weil_XIII_4_lemma6_inf, Subgroup.mem_bot] at hmem
    have h1 : (ξ'⁻¹ * ξ : ℚˣ) = 1 := by
      have := congrArg ratInfComp hmem
      rw [ratInfComp_unitEmbedding, ratInfComp_one] at this
      apply Units.ext
      have : ((ξ'⁻¹ * ξ : ℚˣ) : ℚ) = 1 := by exact_mod_cast this
      simpa using this
    have hξ : ξ = ξ' := by
      have := congrArg (fun x => ξ' * x) h1
      simpa using this
    subst hξ
    have : u = u' := Subtype.ext (mul_left_cancel h)
    rw [this]
  · intro z
    have := weil_XIII_4_lemma6_sup ▸ Subgroup.mem_top z
    obtain ⟨a, ⟨ξ, rfl⟩, b, hb, rfl⟩ := Subgroup.mem_sup.mp this
    exact ⟨(ξ, ⟨b, hb⟩), rfl⟩

end NumberFieldKB.WeilBNT
