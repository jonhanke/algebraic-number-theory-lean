import NumberFieldKB.HeckeCharacter.Basic

/-!
# Local components, ramification and the conductor of a Hecke character

$F$ is a number field and $\chi$ a Hecke character of $F$ (`HeckeCharacter F`).

* **Continuity of the local embeddings** $F_v^\times\to\mathbb A_F^\times\to C_F$ (Mathlib v4.35.0 defines
  `IdeleGroup.ofAdicCompletion`, `IdeleGroup.ofCompletion` and their idele class versions but does not prove them
  continuous): `IdeleGroup.continuous_ofAdicCompletion`, `IdeleGroup.continuous_ofCompletion`.
* **Local components** $\chi_v = \chi|_{F_v^\times}$: `HeckeCharacter.finiteComponent` at a finite place
  $v = \mathfrak p$, `HeckeCharacter.infiniteComponent` at an infinite place; their absolute values
  $|\chi_v(u)| = \|u\|_v^\sigma$ (`norm_finiteComponent_apply`, `norm_infiniteComponent_apply`).
* **The unit filtration** $U_v^{(n)} = \{u : |u|_v = 1,\ |u - 1|_v\le N(v)^{-n}\}$ (`unitFiltration`); $U_v^{(0)}$ is the unit
  group $\mathcal O_v^\times$ (`mem_unitFiltration_zero_iff`) and the $U_v^{(n)}$ form a basis of neighbourhoods of $1$
  (`exists_unitFiltration_subset`).
* **Unramified places**: $\chi$ is unramified at $\mathfrak p$ if $\chi_{\mathfrak p}$ is trivial on
  $\mathcal O_{\mathfrak p}^\times$ (`HeckeCharacter.IsUnramifiedAt`); **all but finitely many places are unramified**
  (`HeckeCharacter.eventually_isUnramifiedAt`).
* **The conductor**: the exponent $a_v(\chi)$ = least $n$ with $\chi_v$ trivial on $U_v^{(n)}$
  (`conductorExponent`, `conductorExponent_le_iff`, `conductorExponent_eq_zero_iff`), and the ideal
  $\mathfrak f(\chi) = \prod_v\mathfrak p_v^{a_v(\chi)}$ (`conductor`); $\mathfrak p\mid\mathfrak f(\chi)$ exactly when
  $\chi$ is ramified at $\mathfrak p$ (`dvd_conductor_iff`).

The proof that almost every place is unramified: $\chi$ composed with the continuous map
$\prod_v\mathcal O_v^\times\to C_F$ (product topology) is trivial on almost every factor, because $\mathbb C^\times$ has
no small subgroups (`NumberFieldKB.HeckeCharacters.eventually_eq_one_of_continuous_pi`).

Adapted from Tau Ceti (`TauCeti/NumberTheory/NumberField/Global/HeckeCharacter/FiniteComponent.lean` and
`InfinityType.lean`, commit a57def64, Copyright (c) 2026 The Tau Ceti contributors, released under the Apache 2.0
license): the definitions `finiteComponent`, `infiniteComponent`, `conductorExponent` and the conductor ideal as
$\prod_v v^{a_v}$. Tau Ceti derives finiteness of ramification from its moduli and idele congruence subgroups; we prove
it directly from the product topology on $\prod_v\mathcal O_v^\times$ instead (shorter, no moduli).
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Filter Topology
open scoped NNReal RestrictedProduct

namespace NumberFieldKB

noncomputable section

variable {F : Type} [Field F] [NumberField F]

namespace Ideles

/-! ### Continuity of the local embeddings -/

/-- The embedding $F_v\to\mathbb A_{F,f}$ (the element in the coordinate $v$, $1$ elsewhere) is continuous. -/
theorem FiniteAdeleRing.continuous_ofAdicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (FiniteAdeleRing.ofAdicCompletion F v) := by
  let := Classical.decEq (HeightOneSpectrum (𝓞 F))
  -- It factors through the restricted product with respect to the principal filter of `{v}ᶜ`.
  have hle : (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 {v}ᶜ :=
    le_principal_iff.mpr (by simp)
  let g : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, (w.adicCompletionIntegers F : Set (w.adicCompletion F))]_[𝓟 {v}ᶜ] := fun x =>
    ⟨Pi.mulSingle v x, eventually_principal.mpr fun w hw => by
      rw [Pi.mulSingle_eq_of_ne (by simpa using hw)]
      exact one_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.mpr (continuous_mulSingle v)
  have heq : (FiniteAdeleRing.ofAdicCompletion F v : v.adicCompletion F → FiniteAdeleRing (𝓞 F) F) =
      RestrictedProduct.inclusion _ _ hle ∘ g := by
    funext x
    refine FiniteAdeleRing.ext _ fun w => ?_
    change RestrictedProduct.mulSingle _ v x w = Pi.mulSingle v x w
    rw [RestrictedProduct.coe_mulSingle_apply]
  rw [heq]
  exact (RestrictedProduct.continuous_inclusion hle).comp hg

/-- The embedding $F_v^\times\to\mathbb A_F^\times$ at a finite place is continuous. -/
theorem IdeleGroup.continuous_ofAdicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (IdeleGroup.ofAdicCompletion (𝓞 F) F v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · simp only [Function.comp_def, IdeleGroup.val_ofAdicCompletion_apply]
    exact continuous_const.prodMk ((FiniteAdeleRing.continuous_ofAdicCompletion v).comp Units.continuous_val)
  · simp only [← map_inv, IdeleGroup.val_ofAdicCompletion_apply]
    exact continuous_const.prodMk ((FiniteAdeleRing.continuous_ofAdicCompletion v).comp Units.continuous_coe_inv)

omit [NumberField F] in
/-- The embedding $F_w\to\mathbb A_{F,\infty}$ at an infinite place is continuous. -/
theorem InfiniteAdeleRing.continuous_ofCompletion (w : InfinitePlace F) :
    Continuous (NumberField.InfiniteAdeleRing.ofCompletion w) := by
  classical
  have : (NumberField.InfiniteAdeleRing.ofCompletion w : w.Completion → InfiniteAdeleRing F) =
      fun x => Pi.mulSingle w x := by
    funext x j
    rw [NumberField.InfiniteAdeleRing.ofCompletion_apply]
  rw [this]
  exact continuous_mulSingle w

/-- The embedding $F_w^\times\to\mathbb A_F^\times$ at an infinite place is continuous. -/
theorem IdeleGroup.continuous_ofCompletion (w : InfinitePlace F) :
    Continuous (IdeleGroup.ofCompletion (𝓞 F) F w) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · simp only [Function.comp_def, IdeleGroup.val_ofCompletion_apply]
    exact ((InfiniteAdeleRing.continuous_ofCompletion w).comp Units.continuous_val).prodMk continuous_const
  · simp only [← map_inv, IdeleGroup.val_ofCompletion_apply]
    exact ((InfiniteAdeleRing.continuous_ofCompletion w).comp Units.continuous_coe_inv).prodMk continuous_const

/-! ### Norms of the local ideles -/

/-- The idele $u$ at the finite place $v$ (and $1$ elsewhere) has norm $\|u\|_v$. -/
theorem coe_ideleGroupNorm_ofAdicCompletion (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    (ideleGroupNorm F (IdeleGroup.ofAdicCompletion (𝓞 F) F v u) : ℝ) = ‖(u : v.adicCompletion F)‖ := by
  let := Classical.decEq (HeightOneSpectrum (𝓞 F))
  rw [coe_ideleGroupNorm, AdeleRing.norm_apply_of_isUnit (Units.isUnit _), IdeleGroup.val_ofAdicCompletion_apply]
  have h1 : ∏ w : InfinitePlace F, ‖(1 : InfiniteAdeleRing F) w‖ ^ w.mult = 1 :=
    Finset.prod_eq_one fun w _ => by
      change ‖(1 : w.Completion)‖ ^ w.mult = 1
      rw [norm_one, one_pow]
  have h2 : ∀ w, ‖(FiniteAdeleRing.ofAdicCompletion F v (u : v.adicCompletion F)) w‖ =
      Pi.mulSingle (M := fun _ => ℝ) v ‖(u : v.adicCompletion F)‖ w := fun w => by
    change ‖RestrictedProduct.mulSingle _ v (u : v.adicCompletion F) w‖ = _
    rw [RestrictedProduct.coe_mulSingle_apply]
    by_cases hw : w = v
    · subst hw
      simp
    · simp [Pi.mulSingle_eq_of_ne hw]
  simp only [h1, one_mul, h2]
  rw [finprod_eq_single _ v (fun w hw => Pi.mulSingle_eq_of_ne hw _), Pi.mulSingle_eq_same]

/-- The idele $u$ at the infinite place $w$ (and $1$ elsewhere) has norm $\|u\|_w^{m_w}$, $m_w\in\{1,2\}$. -/
theorem coe_ideleGroupNorm_ofCompletion (w : InfinitePlace F) (u : w.Completionˣ) :
    (ideleGroupNorm F (IdeleGroup.ofCompletion (𝓞 F) F w u) : ℝ) = ‖(u : w.Completion)‖ ^ w.mult := by
  classical
  rw [coe_ideleGroupNorm, AdeleRing.norm_apply_of_isUnit (Units.isUnit _), IdeleGroup.val_ofCompletion_apply]
  have h2 : ∏ᶠ v, ‖(1 : FiniteAdeleRing (𝓞 F) F) v‖ = 1 := by
    have : ∀ v : HeightOneSpectrum (𝓞 F), ‖(1 : FiniteAdeleRing (𝓞 F) F) v‖ = 1 := fun v => by
      change ‖(1 : v.adicCompletion F)‖ = 1
      exact norm_one
    simp only [this, finprod_one]
  simp only [h2, mul_one]
  rw [Finset.prod_eq_single w]
  · rw [NumberField.InfiniteAdeleRing.ofCompletion_apply, Pi.mulSingle_eq_same]
  · intro j _ hj
    rw [NumberField.InfiniteAdeleRing.ofCompletion_apply, Pi.mulSingle_eq_of_ne hj, norm_one, one_pow]
  · simp

end Ideles

open Ideles

/-! ### The unit filtration -/

/-- **The unit filtration** at a finite place $v$: $U_v^{(n)} = \{u\in F_v^\times : |u|_v = 1,\ |u - 1|_v\le e^{-n}\}$
(valuations written multiplicatively, `WithZero.exp`). $U_v^{(0)}=\mathcal O_v^\times$ and $U_v^{(n)} = 1+\mathfrak p_v^n$
for $n\ge1$. -/
def unitFiltration (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Subgroup (v.adicCompletion F)ˣ where
  carrier := {u | Valued.v (u : v.adicCompletion F) = 1 ∧
    Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ))}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' {a b} ha hb := by
    refine ⟨by rw [Units.val_mul, map_mul, ha.1, hb.1, one_mul], ?_⟩
    have e : ((a * b : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1 =
        (a : v.adicCompletion F) * ((b : v.adicCompletion F) - 1) + ((a : v.adicCompletion F) - 1) := by
      rw [Units.val_mul]; ring
    rw [e]
    refine Valuation.map_add_le _ ?_ ha.2
    rw [map_mul, ha.1, one_mul]
    exact hb.2
  inv_mem' {a} ha := by
    have hinv : Valued.v ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, ha.1, inv_one]
    refine ⟨hinv, ?_⟩
    have e : ((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1 =
        -(((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * ((a : v.adicCompletion F) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one]; ring
    rw [e, Valuation.map_neg, map_mul, hinv, one_mul]
    exact ha.2

theorem mem_unitFiltration {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} {u : (v.adicCompletion F)ˣ} :
    u ∈ unitFiltration v n ↔ Valued.v (u : v.adicCompletion F) = 1 ∧
      Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) := Iff.rfl

/-- $U_v^{(0)}$ is the unit group $\mathcal O_v^\times = \{u : |u|_v = 1\}$. -/
theorem mem_unitFiltration_zero_iff {v : HeightOneSpectrum (𝓞 F)} {u : (v.adicCompletion F)ˣ} :
    u ∈ unitFiltration v 0 ↔ Valued.v (u : v.adicCompletion F) = 1 := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [Nat.cast_zero, neg_zero, WithZero.exp_zero, sub_eq_add_neg]
  exact Valuation.map_add_le _ h.le (by rw [Valuation.map_neg, map_one])

theorem unitFiltration_antitone {v : HeightOneSpectrum (𝓞 F)} : Antitone (unitFiltration (F := F) v) :=
  fun _ _ hnm _ hu => ⟨hu.1, hu.2.trans (WithZero.exp_le_exp.mpr (by omega))⟩

/-- **The unit filtration is a basis of neighbourhoods of $1$** in $F_v^\times$. -/
theorem exists_unitFiltration_subset {v : HeightOneSpectrum (𝓞 F)} {W : Set (v.adicCompletion F)ˣ}
    (hW : W ∈ 𝓝 1) : ∃ n, (unitFiltration v n : Set (v.adicCompletion F)ˣ) ⊆ W := by
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Units.val_one, mem_comap] at hW
  obtain ⟨W', hW', hsub⟩ := hW
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hW'
  set g := MonoidWithZeroHom.ValueGroup₀.embedding γ.1
  have hg : g ≠ 0 := (γ.isUnit.map MonoidWithZeroHom.ValueGroup₀.embedding).ne_zero
  refine ⟨(-(WithZero.log g) + 1).toNat, fun u hu => hsub (hγ ?_)⟩
  change Valued.v.restrict ((u : v.adicCompletion F) - 1) < γ
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt hu.2 ?_
  have h : WithZero.exp (-(((-(WithZero.log g) + 1).toNat : ℕ) : ℤ)) < WithZero.exp (WithZero.log g) :=
    WithZero.exp_lt_exp.mpr (by omega)
  rwa [WithZero.exp_log hg] at h

namespace HeckeCharacter

/-! ### Local components -/

/-- **The component of $\chi$ at a finite place** $v$: $\chi_v = \chi|_{F_v^\times}$, through
$F_v^\times\to\mathbb A_F^\times\to C_F$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §3.2 [unverified locator] (c_p, the restriction of c to k_p^×)"]
def finiteComponent (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ →ₜ* ℂˣ :=
  χ.comp ⟨IdeleClassGroup.ofAdicCompletion (𝓞 F) F v,
    QuotientGroup.continuous_mk.comp (IdeleGroup.continuous_ofAdicCompletion v)⟩

@[simp] theorem finiteComponent_apply (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    χ.finiteComponent v u = χ (IdeleGroup.ofAdicCompletion (𝓞 F) F v u : IdeleClassGroup (𝓞 F) F) := rfl

/-- **The component of $\chi$ at an infinite place** $w$: $\chi_w = \chi|_{F_w^\times}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §3.2 [unverified locator] (c_p at the archimedean primes)"]
def infiniteComponent (χ : HeckeCharacter F) (w : InfinitePlace F) : w.Completionˣ →ₜ* ℂˣ :=
  χ.comp ⟨IdeleClassGroup.ofCompletion (𝓞 F) F w,
    QuotientGroup.continuous_mk.comp (IdeleGroup.continuous_ofCompletion w)⟩

@[simp] theorem infiniteComponent_apply (χ : HeckeCharacter F) (w : InfinitePlace F) (u : w.Completionˣ) :
    χ.infiniteComponent w u = χ (IdeleGroup.ofCompletion (𝓞 F) F w u : IdeleClassGroup (𝓞 F) F) := rfl

/-- $|\chi_v(u)| = \|u\|_v^\sigma$ at a finite place, $\sigma$ the shift of $\chi$. -/
theorem norm_finiteComponent_apply (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    ‖(χ.finiteComponent v u : ℂ)‖ = ‖(u : v.adicCompletion F)‖ ^ χ.shift := by
  rw [finiteComponent_apply, norm_apply_eq_rpow_shift, ideleClassNorm_mk, coe_ideleGroupNorm_ofAdicCompletion]

/-- $|\chi_w(u)| = \|u\|_w^{m_w\sigma}$ at an infinite place ($m_w = 1$ real, $2$ complex). -/
theorem norm_infiniteComponent_apply (χ : HeckeCharacter F) (w : InfinitePlace F) (u : w.Completionˣ) :
    ‖(χ.infiniteComponent w u : ℂ)‖ = (‖(u : w.Completion)‖ ^ w.mult) ^ χ.shift := by
  rw [infiniteComponent_apply, norm_apply_eq_rpow_shift, ideleClassNorm_mk, coe_ideleGroupNorm_ofCompletion]

/-! ### Unramified places -/

/-- $\chi$ is **unramified** at the finite place $v$ if $\chi_v$ is trivial on the units $\mathcal O_v^\times$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.3 [unverified locator] (unramified quasi-characters)"]
def IsUnramifiedAt (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ.finiteComponent v u = 1

/-- The idele with coordinates $x_v\in\mathcal O_v^\times$ at the finite places and $1$ at the infinite places. -/
private def piUnitsVal (x : ∀ v : HeightOneSpectrum (𝓞 F), unitFiltration v 0) : AdeleRing (𝓞 F) F :=
  (1, RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
    fun v => ⟨((x v : (v.adicCompletion F)ˣ) : v.adicCompletion F),
      (mem_adicCompletionIntegers _ _ _).mpr (mem_unitFiltration_zero_iff.mp (x v).2).le⟩)

private theorem continuous_piUnitsVal : Continuous (piUnitsVal (F := F)) := by
  refine continuous_const.prodMk ((RestrictedProduct.isOpenEmbedding_structureMap fun v =>
    Valued.isOpen_valuationSubring _).continuous.comp ?_)
  exact continuous_pi fun v => (Units.continuous_val.comp
    (continuous_subtype_val.comp (continuous_apply v))).subtype_mk _

private theorem piUnitsVal_mul (x y : ∀ v : HeightOneSpectrum (𝓞 F), unitFiltration v 0) :
    piUnitsVal (x * y) = piUnitsVal x * piUnitsVal y := by
  refine Prod.ext (mul_one 1).symm (FiniteAdeleRing.ext _ fun v => ?_)
  change ((x v * y v : unitFiltration v 0) : (v.adicCompletion F)ˣ).val = (x v : (v.adicCompletion F)ˣ).val *
    (y v : (v.adicCompletion F)ˣ).val
  rfl

private theorem piUnitsVal_one : piUnitsVal (1 : ∀ v : HeightOneSpectrum (𝓞 F), unitFiltration v 0) = 1 := by
  refine Prod.ext rfl (FiniteAdeleRing.ext _ fun v => ?_)
  rfl

/-- The continuous map $\prod_v\mathcal O_v^\times\to\mathbb A_F^\times$. -/
private def piUnitsIdele (x : ∀ v : HeightOneSpectrum (𝓞 F), unitFiltration v 0) : IdeleGroup (𝓞 F) F where
  val := piUnitsVal x
  inv := piUnitsVal x⁻¹
  val_inv := by rw [← piUnitsVal_mul, mul_inv_cancel, piUnitsVal_one]
  inv_val := by rw [← piUnitsVal_mul, inv_mul_cancel, piUnitsVal_one]

private theorem continuous_piUnitsIdele : Continuous (piUnitsIdele (F := F)) :=
  Units.continuous_iff.mpr ⟨continuous_piUnitsVal, continuous_piUnitsVal.comp continuous_inv⟩

private theorem piUnitsIdele_mulSingle (v : HeightOneSpectrum (𝓞 F)) (u : unitFiltration v 0) :
    letI := Classical.decEq (HeightOneSpectrum (𝓞 F))
    piUnitsIdele (Pi.mulSingle v u) = IdeleGroup.ofAdicCompletion (𝓞 F) F v (u : (v.adicCompletion F)ˣ) := by
  let := Classical.decEq (HeightOneSpectrum (𝓞 F))
  refine Units.ext (Prod.ext rfl (FiniteAdeleRing.ext _ fun w => ?_))
  rw [IdeleGroup.val_ofAdicCompletion_apply]
  change ((Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => unitFiltration w 0) v u w :
      unitFiltration w 0) : (w.adicCompletion F)ˣ).val =
    FiniteAdeleRing.ofAdicCompletion F v ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F) w
  change _ = Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v
    ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F) w
  by_cases hw : w = v
  · subst hw
    simp
  · simp [Pi.mulSingle_eq_of_ne hw]

/-- **A Hecke character is unramified at all but finitely many places.** -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §3.2 [unverified locator] (c_p unramified for almost all p)"]
theorem eventually_isUnramifiedAt (χ : HeckeCharacter F) : ∀ᶠ v in cofinite, χ.IsUnramifiedAt v := by
  let := Classical.decEq (HeightOneSpectrum (𝓞 F))
  have hcont : Continuous fun x : (∀ v : HeightOneSpectrum (𝓞 F), unitFiltration v 0) =>
      χ (piUnitsIdele x : IdeleClassGroup (𝓞 F) F) :=
    (map_continuous χ).comp (QuotientGroup.continuous_mk.comp continuous_piUnitsIdele)
  have h := HeckeCharacters.eventually_eq_one_of_continuous_pi
    (fun x => χ (piUnitsIdele x : IdeleClassGroup (𝓞 F) F)) hcont
    (by
      have : piUnitsIdele (1 : ∀ v : HeightOneSpectrum (𝓞 F), unitFiltration v 0) = 1 :=
        Units.ext piUnitsVal_one
      simp [this])
    (fun v => (χ.finiteComponent v : (v.adicCompletion F)ˣ →* ℂˣ).comp (unitFiltration v 0).subtype)
    (fun v u => by simp [piUnitsIdele_mulSingle])
  refine h.mono fun v hv u hu => ?_
  have := DFunLike.congr_fun hv ⟨u, mem_unitFiltration_zero_iff.mpr hu⟩
  simpa using this

/-! ### The conductor -/

/-- At every finite place, $\chi_v$ is trivial on some $U_v^{(n)}$ ($\mathbb C^\times$ has no small subgroups). -/
theorem exists_finiteComponent_eq_one (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ n, ∀ u ∈ unitFiltration v n, χ.finiteComponent v u = 1 := by
  set U : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1 / 2}
  have hU : IsOpen U :=
    isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have h1 : χ.finiteComponent v ⁻¹' U ∈ 𝓝 1 :=
    (χ.finiteComponent v).continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simp [U]))
  obtain ⟨n, hn⟩ := exists_unitFiltration_subset h1
  refine ⟨n, fun u hu => ?_⟩
  have h := MonoidHom.eq_one_of_norm_sub_one_lt
    ((χ.finiteComponent v : (v.adicCompletion F)ˣ →* ℂˣ).comp (unitFiltration v n).subtype)
    fun x => hn x.2
  exact DFunLike.congr_fun h ⟨u, hu⟩

/-- **The conductor exponent** $a_v(\chi)$: the least $n$ such that $\chi_v$ is trivial on $U_v^{(n)}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.3 [unverified locator] (the conductor p^ν of a ramified quasi-character)"]
def conductorExponent (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  sInf {n | ∀ u ∈ unitFiltration v n, χ.finiteComponent v u = 1}

theorem finiteComponent_eq_one_of_mem (χ : HeckeCharacter F) {v : HeightOneSpectrum (𝓞 F)}
    {u : (v.adicCompletion F)ˣ} (hu : u ∈ unitFiltration v (χ.conductorExponent v)) :
    χ.finiteComponent v u = 1 :=
  Nat.sInf_mem (s := {n | ∀ u ∈ unitFiltration v n, χ.finiteComponent v u = 1})
    (χ.exists_finiteComponent_eq_one v) u hu

/-- **Characterization**: $a_v(\chi)\le n$ exactly when $\chi_v$ is trivial on $U_v^{(n)}$. -/
theorem conductorExponent_le_iff (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    χ.conductorExponent v ≤ n ↔ ∀ u ∈ unitFiltration v n, χ.finiteComponent v u = 1 :=
  ⟨fun h _ hu => χ.finiteComponent_eq_one_of_mem (unitFiltration_antitone h hu), fun h => Nat.sInf_le h⟩

/-- $a_v(\chi) = 0$ exactly when $\chi$ is unramified at $v$. -/
theorem conductorExponent_eq_zero_iff (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    χ.conductorExponent v = 0 ↔ χ.IsUnramifiedAt v := by
  rw [← Nat.le_zero, conductorExponent_le_iff]
  exact ⟨fun h u hu => h u (mem_unitFiltration_zero_iff.mpr hu),
    fun h u hu => h u (mem_unitFiltration_zero_iff.mp hu)⟩

private theorem hasFiniteMulSupport_pow_conductorExponent (χ : HeckeCharacter F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal ^ χ.conductorExponent v).Finite := by
  refine χ.eventually_isUnramifiedAt.mono fun v hv => ?_
  simp [(conductorExponent_eq_zero_iff χ v).mpr hv]

/-- **The conductor** of $\chi$: the integral ideal $\mathfrak f(\chi) = \prod_v\mathfrak p_v^{a_v(\chi)}$ (a finite
product by `eventually_isUnramifiedAt`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §3.2 [unverified locator] (the conductor of a quasi-character of C_k)"]
def conductor (χ : HeckeCharacter F) : Ideal (𝓞 F) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), v.asIdeal ^ χ.conductorExponent v

/-- **A prime divides the conductor exactly when $\chi$ is ramified there.** -/
theorem dvd_conductor_iff (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F)) :
    v.asIdeal ∣ χ.conductor ↔ ¬ χ.IsUnramifiedAt v := by
  rw [← conductorExponent_eq_zero_iff, conductor,
    finprod_eq_prod_of_mulSupport_subset _ χ.hasFiniteMulSupport_pow_conductorExponent.coe_toFinset.symm.subset]
  have hprime : Prime v.asIdeal := v.prime
  constructor
  · intro h
    obtain ⟨w, hw, hdvd⟩ := hprime.dvd_finsetProd_iff _ |>.mp h
    have hw' : w.asIdeal ^ χ.conductorExponent w ≠ 1 := by simpa using hw
    have hvw : v.asIdeal ∣ w.asIdeal := hprime.dvd_of_dvd_pow hdvd
    have heq : w = v := by
      have hle : w.asIdeal ≤ v.asIdeal := Ideal.le_of_dvd hvw
      exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hle)
    subst heq
    intro h0
    exact hw' (by rw [h0, pow_zero])
  · intro h
    have hmem : v ∈ χ.hasFiniteMulSupport_pow_conductorExponent.toFinset := by
      rw [Set.Finite.mem_toFinset, Function.mem_mulSupport]
      intro h1
      rw [Ideal.one_eq_top] at h1
      exact v.isPrime.ne_top (top_le_iff.mp (h1 ▸ Ideal.pow_le_self h))
    exact (dvd_pow_self _ h).trans (Finset.dvd_prod_of_mem _ hmem)

/-- **The conductor is trivial exactly when $\chi$ is unramified everywhere.** -/
theorem conductor_eq_top_iff (χ : HeckeCharacter F) :
    χ.conductor = ⊤ ↔ ∀ v, χ.IsUnramifiedAt v := by
  refine ⟨fun h v => ?_, fun h => ?_⟩
  · by_contra hv
    have := (dvd_conductor_iff χ v).mpr hv
    rw [h, ← Ideal.one_eq_top] at this
    exact v.isPrime.ne_top (Ideal.isUnit_iff.mp (isUnit_of_dvd_one this))
  · rw [conductor, ← Ideal.one_eq_top]
    simp only [(conductorExponent_eq_zero_iff χ _).mpr (h _), pow_zero, finprod_one]

end HeckeCharacter

end

end NumberFieldKB
