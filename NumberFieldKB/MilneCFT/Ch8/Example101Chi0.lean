import NumberFieldKB.MilneCFT.Ch8.Example101Arith
import NumberFieldKB.WeilBNT.IdeleCharacterExtension
import NumberFieldKB.HeckeCharacter.Local
import NumberFieldKB.MilneCFT.Ch5Density
import NumberFieldKB.TauCetiPort.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.Topology.Algebra.Group.Units

/-!
# The character $\chi_0$ of Milne, *CFT*, VIII, Example 10.1

By Weil's Proposition VII.8.17 (`WeilBNT.exists_extension`): the idèle character of $\mathbb Q(\zeta_3)$ trivial on
$K^\times$, equal on the idèles trivial at $3$ to the ideal character $\varphi_0((\alpha)) = \bar\alpha/|\alpha|$
($\alpha \equiv 1 \bmod 3$).
-/

open NumberField IsDedekindDomain NumberFieldKB.WeilBNT NumberFieldKB.MilneCFT
open scoped nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace NumberFieldKB.MilneCFT.Ch8.Ex101

/-! ### The character $z \mapsto \bar z/|z|$ of $\mathbb C^\times$ -/

/-- $z \mapsto \bar z / |z|$ on $\mathbb C^\times$. -/
def psi0 : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 (starRingEnd ℂ (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)) (by
    have := z.ne_zero
    simpa using this)
  map_one' := by ext; simp
  map_mul' z w := by
    ext
    simp only [Units.val_mul, map_mul, norm_mul, Complex.ofReal_mul, Units.val_mk0]
    field_simp

theorem psi0_val (z : ℂˣ) : ((psi0 z : ℂˣ) : ℂ) = starRingEnd ℂ (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem norm_psi0 (z : ℂˣ) : ‖((psi0 z : ℂˣ) : ℂ)‖ = 1 := by
  rw [psi0_val, norm_div, Complex.norm_real, Complex.norm_conj, norm_norm]
  exact div_self (by simpa using z.ne_zero)

theorem continuous_psi0 : Continuous psi0 := by
  rw [Units.continuous_iff]
  have hne : ∀ z : ℂˣ, ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun z => by simpa using z.ne_zero
  constructor
  · show Continuous fun z : ℂˣ => starRingEnd ℂ (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)
    exact (Complex.continuous_conj.comp Units.continuous_val).div
      (Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val)) hne
  · have : (fun z : ℂˣ => (((psi0 z)⁻¹ : ℂˣ) : ℂ)) =
        fun z : ℂˣ => ((‖(z : ℂ)‖ : ℝ) : ℂ) / starRingEnd ℂ (z : ℂ) := by
      funext z
      rw [Units.val_inv_eq_inv_val, psi0_val, inv_div]
    rw [this]
    exact (Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val)).div
      (Complex.continuous_conj.comp Units.continuous_val)
      (fun z => by simpa using z.ne_zero)

/-! ### The infinite place -/

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- The continuous extension of $\sigma$ to the completion at $w$ (for $w$ the place of $\sigma$). -/
def eσ (σ : K →+* ℂ) (w : InfinitePlace K) : w.Completion →+* ℂ := by
  classical
  exact if w.embedding = σ then InfinitePlace.Completion.extensionEmbedding w
    else (starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding w)

theorem continuous_eσ (σ : K →+* ℂ) (w : InfinitePlace K) : Continuous (eσ σ w) := by
  unfold eσ
  split_ifs
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
  · exact Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous

theorem eσ_coe (σ : K →+* ℂ) (w : InfinitePlace K) (hw : w = InfinitePlace.mk σ) (x : K) :
    eσ σ w (x : w.Completion) = σ x := by
  have h0 : InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) = w.embedding x := by
    have := InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)
    simpa using this
  unfold eσ
  split_ifs with h
  · rw [h0, h]
  · have := InfinitePlace.embedding_mk_eq σ
    rw [← hw] at this
    rcases this with h1 | h1
    · exact absurd h1 h
    · simp only [RingHom.comp_apply, h0, h1]
      simp [ComplexEmbedding.conjugate_coe_eq]


/-! ### The data of Proposition 17 -/

/-- The set $S = \{(\lambda)\}$ of primes above $3$. -/
def S0 : Finset (HeightOneSpectrum (𝓞 K)) := {vL}

/-- At the infinite places, all units. -/
def gInf0 : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ := fun _ => ⊤

/-- The units $u$ of $K_v$ with $v(u - 1) \le c$ (for $c < 1$). -/
def ballUnits (v : HeightOneSpectrum (𝓞 K)) (c : WithZero (Multiplicative ℤ)) (hc : c < 1) :
    Subgroup ((v.adicCompletion K)ˣ) where
  carrier := {u | Valued.v ((u : v.adicCompletion K) - 1) ≤ c}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have := val_mul_sub_one_le Valued.v hc ha hb
    simpa using this
  inv_mem' := fun {a} ha => by
    have := val_inv_sub_one_le Valued.v hc ha
    simpa using this

theorem mem_ballUnits {v : HeightOneSpectrum (𝓞 K)} {c : WithZero (Multiplicative ℤ)} {hc : c < 1}
    {u : (v.adicCompletion K)ˣ} : u ∈ ballUnits v c hc ↔ Valued.v ((u : v.adicCompletion K) - 1) ≤ c := Iff.rfl

theorem isOpen_ballUnits (v : HeightOneSpectrum (𝓞 K)) {c : WithZero (Multiplicative ℤ)} (hc : c < 1)
    (hc0 : c ≠ 0) : IsOpen (ballUnits v c hc : Set ((v.adicCompletion K)ˣ)) := by
  have h1 : IsOpen {x : v.adicCompletion K | Valued.v x ≤ c} := HeightOneSpectrum.isOpen_setOf_valued_le (K := K) v hc0
  have h2 : Continuous fun u : (v.adicCompletion K)ˣ => (u : v.adicCompletion K) - 1 :=
    Units.continuous_val.sub continuous_const
  exact h1.preimage h2

theorem valued_three_lt_one (v : S0 (K := K)) : Valued.v (((3 : K)) : v.1.adicCompletion K) < 1 := by
  obtain ⟨v, hv⟩ := v
  have hv' : v = vL := Finset.mem_singleton.1 hv
  subst hv'
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact val_three_vL_lt_one

theorem valued_three_ne_zero (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((3 : K)) : v.adicCompletion K) ≠ 0 := by
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (map_ne_zero _).2 (by norm_num)

/-- At $v = (\lambda)$: the units $\equiv 1 \bmod 3$. -/
def gFin0 : ∀ v : S0 (K := K), Subgroup ((v.1.adicCompletion K)ˣ) := fun v =>
  ballUnits v.1 (Valued.v (((3 : K)) : v.1.adicCompletion K)) (valued_three_lt_one v)

theorem isOpen_gInf0 : ∀ w : InfinitePlace K, IsOpen (gInf0 w : Set (w.Completion)ˣ) := fun _ => isOpen_univ

theorem isOpen_gFin0 : ∀ v : S0 (K := K), IsOpen (gFin0 v : Set ((v.1.adicCompletion K)ˣ)) :=
  fun v => isOpen_ballUnits v.1 _ (valued_three_ne_zero v.1)

theorem gFin0_val : ∀ v : S0 (K := K), ∀ u ∈ gFin0 v, Valued.v (u : v.1.adicCompletion K) = 1 :=
  fun v _ hu => val_eq_one_of_sub_one_le Valued.v (valued_three_lt_one v) hu


theorem coe_eq_algebraMap (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (x : v.adicCompletion K) = algebraMap K (v.adicCompletion K) x := rfl

theorem valued_coe_sub_one (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    Valued.v ((x : v.adicCompletion K) - 1) = v.valuation K (x - 1) := by
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  rw [coe_eq_algebraMap, coe_eq_algebraMap, ← map_one (algebraMap K (v.adicCompletion K)), ← map_sub]

/-- The principal ideles $\xi$ whose components lie in $g$ (i.e. $\xi \equiv 1 \bmod 3$). -/
def A0 : Subgroup Kˣ :=
  (gGP S0 gInf0 gFin0 : Subgroup (IdeleGroup (𝓞 K) K)).comap (IdeleGroup.unitEmbedding (𝓞 K) K)

theorem mem_A0_iff {ξ : Kˣ} : ξ ∈ A0 (K := K) ↔
    pproj S0 (IdeleGroup.unitEmbedding (𝓞 K) K ξ) ∈ gProd S0 gInf0 gFin0 := Iff.rfl

theorem mem_A0 {ξ : Kˣ} : ξ ∈ A0 (K := K) ↔
    (vL (K := K)).valuation K ((ξ : K) - 1) ≤ (vL (K := K)).valuation K (3 : K) := by
  rw [mem_A0_iff]
  constructor
  · intro h
    have := h.2 ⟨vL, Finset.mem_singleton_self _⟩
    change Valued.v (((ξ : K) : (vL (K := K)).adicCompletion K) - 1) ≤ Valued.v (((3 : K)) : (vL (K := K)).adicCompletion K) at this
    rwa [valued_coe_sub_one, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
  · intro h
    refine ⟨fun w => Subgroup.mem_top _, fun v => ?_⟩
    obtain ⟨v, hv⟩ := v
    have hv' : v = vL := Finset.mem_singleton.1 hv
    subst hv'
    change Valued.v (((ξ : K) : (vL (K := K)).adicCompletion K) - 1) ≤ Valued.v (((3 : K)) : (vL (K := K)).adicCompletion K)
    rwa [valued_coe_sub_one, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-- The ideals prime to $3$. -/
abbrev Ideals3 : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  sIdeals (((S0 (K := K) : Finset (HeightOneSpectrum (𝓞 K)))) : Set (HeightOneSpectrum (𝓞 K)))

/-- The embedding of `A0` into $g \cdot G_P$. -/
def embA : A0 (K := K) →* gGP (S0 (K := K)) gInf0 gFin0 :=
  MonoidHom.codRestrict ((IdeleGroup.unitEmbedding (𝓞 K) K).comp (A0 (K := K)).subtype) _ fun ξ => ξ.2

/-- $\xi \mapsto (\xi)$ from `A0` to the ideals prime to $3$. -/
def fA : A0 (K := K) →* Ideals3 (K := K) :=
  (idGP (gInf := gInf0) gFin0_val).comp embA

theorem fA_val (a : A0 (K := K)) :
    ((fA a : Ideals3 (K := K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toPrincipalIdeal (𝓞 K) K a := by
  rw [← ideleToIdeal_unitEmbedding]; rfl

theorem fA_injective : Function.Injective (fA (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : toPrincipalIdeal (𝓞 K) K (a : Kˣ) = 1 := by
    rw [← fA_val, ha]; rfl
  rw [toPrincipalIdeal_eq_iff, Units.val_one, ← map_one (FractionalIdeal.spanSingleton (𝓞 K)⁰),
    FractionalIdeal.spanSingleton_eq_spanSingleton] at h1
  obtain ⟨z, hz⟩ := h1
  have hz' : algebraMap (𝓞 K) K z * ((a : Kˣ) : K) = 1 := by
    have : (z : 𝓞 K) • ((a : Kˣ) : K) = 1 := hz
    rwa [Algebra.smul_def] at this
  have h2 : algebraMap (𝓞 K) K ((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * algebraMap (𝓞 K) K z = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have ha' : ((a : Kˣ) : K) = algebraMap (𝓞 K) K ((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    linear_combination (algebraMap (𝓞 K) K ((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) * hz' - ((a : Kˣ) : K) * h2
  have hmem := mem_A0.1 a.2
  have h3 : (3 : 𝓞 K) ∣ ((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) - 1 := by
    rw [dvd_three_iff]
    have : ((((z⁻¹ : (𝓞 K)ˣ) : 𝓞 K) - 1 : 𝓞 K) : K) = ((a : Kˣ) : K) - 1 := by
      rw [ha']; simp
    rw [this]
    exact hmem
  have := unit_eq_one_of_dvd h3
  apply Subtype.ext
  apply Units.ext
  rw [ha', this]
  simp

theorem fA_surjective : Function.Surjective (fA (K := K)) := by
  intro b
  have hb : (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈
      sIdeals (((S0 (K := K) : Finset (HeightOneSpectrum (𝓞 K)))) : Set (HeightOneSpectrum (𝓞 K))) := b.2
  rw [sIdeals_eq_closure] at hb
  have hle : Subgroup.closure (primeUnitIdeal '' ((((S0 (K := K) : Finset (HeightOneSpectrum (𝓞 K)))) :
      Set (HeightOneSpectrum (𝓞 K)))ᶜ)) ≤ (fA (K := K)).range.map (Ideals3 (K := K)).subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨v, hv, rfl⟩
    have hvL : v ≠ vL := fun h => hv (by subst h; simp [S0])
    obtain ⟨ξ0, h3, hspan⟩ := exists_gen_one_mod_three hvL
    have hξ0 : ξ0 ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at hspan
      exact v.ne_bot hspan
    let ξ : Kˣ := Units.mk0 (ξ0 : K) (by simpa using hξ0)
    have hξ : ξ ∈ A0 (K := K) := by
      rw [mem_A0]
      have e : ((ξ : Kˣ) : K) - 1 = ((ξ0 - 1 : 𝓞 K) : K) := by simp [ξ]
      rw [e]
      exact (dvd_three_iff _).1 h3
    refine Subgroup.mem_map.2 ⟨fA ⟨ξ, hξ⟩, MonoidHom.mem_range.2 ⟨_, rfl⟩, ?_⟩
    show ((fA ⟨ξ, hξ⟩ : Ideals3 (K := K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = primeUnitIdeal v
    rw [fA_val]
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    show _ = ((v.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    rw [hspan, FractionalIdeal.coeIdeal_span_singleton]
    rfl
  obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 (hle hb)
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hy
  exact ⟨a, Subtype.ext hyb⟩

theorem exists_phi0 {Γ : Type*} [CommGroup Γ] (ψ : A0 (K := K) →* Γ) :
    ∃ φ : Ideals3 (K := K) →* Γ, ∀ a, φ (fA a) = ψ a := by
  let e := MulEquiv.ofBijective (fA (K := K)) ⟨fA_injective, fA_surjective⟩
  refine ⟨ψ.comp e.symm.toMonoidHom, fun a => ?_⟩
  show ψ (e.symm (e a)) = ψ a
  rw [MulEquiv.symm_apply_apply]

/-- The ideal character $\varphi_0$ satisfying the condition of Proposition 17. -/
theorem exists_prop17Condition (ψInf : ∀ w, gInf0 w →* ℂˣ) (ψFin : ∀ v : S0 (K := K), gFin0 v →* ℂˣ) :
    ∃ φ : Ideals3 (K := K) →* ℂˣ,
      (∀ a : A0 (K := K), φ (fA a) = psiProd ψInf ψFin (pprojG (embA a))) ∧
      Prop17Condition S0 gInf0 gFin0 φ ψInf ψFin := by
  obtain ⟨φ, hφ⟩ := exists_phi0 ((psiProd ψInf ψFin).comp ((pprojG (S := S0) (gInf := gInf0) (gFin := gFin0)).comp embA))
  refine ⟨φ, hφ, fun ξ hξ b hb => ?_⟩
  have : b = fA ⟨ξ, hξ⟩ := Subtype.ext (hb.trans (fA_val ⟨ξ, hξ⟩).symm)
  rw [this, hφ]
  rfl

/-! ### The infinite place -/

theorem card_infinitePlace : Fintype.card (InfinitePlace K) = 1 := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 3) K (by decide), zero_add,
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := 3)]
  rfl

theorem place_eq (σ : K →+* ℂ) (w : InfinitePlace K) : w = InfinitePlace.mk σ := by
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.1 (card_infinitePlace (K := K))
  rw [hx w, hx (InfinitePlace.mk σ)]

/-- $\psi_\infty(z) = \bar{e(z)}/|e(z)|$. -/
def psiInf (σ : K →+* ℂ) (w : InfinitePlace K) : gInf0 w →* ℂˣ :=
  (psi0.comp (Units.map (eσ σ w : w.Completion →* ℂ))).comp (gInf0 w).subtype

/-- $\psi_v = 1$ at the finite places. -/
def psiFin : ∀ v : S0 (K := K), gFin0 v →* ℂˣ := fun _ => 1

theorem continuous_psiInf (σ : K →+* ℂ) (w : InfinitePlace K) : Continuous (psiInf σ w) :=
  (continuous_psi0.comp ((Continuous.units_map _ (continuous_eσ σ w)).comp continuous_subtype_val))

theorem norm_psiProd (σ : K →+* ℂ) (c : gProd S0 gInf0 gFin0) :
    ‖((psiProd (psiInf σ) psiFin c : ℂˣ) : ℂ)‖ = 1 := by
  rw [psiProd_apply, Units.val_mul, norm_mul]
  have h1 : ‖(((∏ w, psiInf σ w (gProdInf w c)) : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.coe_prod, norm_prod]
    exact Finset.prod_eq_one fun w _ => norm_psi0 _
  have h2 : (∏ v : S0 (K := K), psiFin v (gProdFin v c)) = 1 :=
    Finset.prod_eq_one fun v _ => rfl
  rw [h1, h2]; simp

theorem psiProd_pprojG_embA (σ : K →+* ℂ) (a : A0 (K := K)) :
    ((psiProd (psiInf σ) psiFin (pprojG (embA a)) : ℂˣ) : ℂ) =
      starRingEnd ℂ (σ ((a : Kˣ) : K)) / ((‖σ ((a : Kˣ) : K)‖ : ℝ) : ℂ) := by
  rw [psiProd_apply, Units.val_mul]
  have h2 : (∏ v : S0 (K := K), psiFin v (gProdFin v (pprojG (embA a)))) = 1 :=
    Finset.prod_eq_one fun v _ => rfl
  have h1 : (∏ w, psiInf σ w (gProdInf w (pprojG (embA a)))) =
      psiInf σ (InfinitePlace.mk σ) (gProdInf (InfinitePlace.mk σ) (pprojG (embA a))) :=
    Fintype.prod_eq_single _ fun w hw => absurd (place_eq σ w) hw
  rw [h1, h2, Units.val_one, mul_one]
  show ((psi0 (Units.map (eσ σ (InfinitePlace.mk σ) : (InfinitePlace.mk σ).Completion →* ℂ)
    (pinf (InfinitePlace.mk σ) (IdeleGroup.unitEmbedding (𝓞 K) K (a : Kˣ)))) : ℂˣ) : ℂ) = _
  rw [psi0_val]
  have : ((Units.map (eσ σ (InfinitePlace.mk σ) : (InfinitePlace.mk σ).Completion →* ℂ)
    (pinf (InfinitePlace.mk σ) (IdeleGroup.unitEmbedding (𝓞 K) K (a : Kˣ))) : ℂˣ) : ℂ) = σ ((a : Kˣ) : K) := by
    rw [Units.coe_map]
    exact eσ_coe σ _ rfl _
  rw [this]


/-- **The idèle character $\omega_0$** (Weil, VII.8, Prop. 17): continuous, trivial on $K^\times$, unitary, and on
idèles trivial at $3$ whose ideal is $(\xi)$, $\xi \equiv 1 \bmod 3$, it takes the value $\bar{\sigma\xi}/|\sigma\xi|$. -/
theorem exists_omega0 (σ : K →+* ℂ) :
    ∃ ω : IdeleGroup (𝓞 K) K →* ℂˣ, Continuous ω ∧
      (∀ ξ : Kˣ, ω (IdeleGroup.unitEmbedding (𝓞 K) K ξ) = 1) ∧ (∀ x, ‖(ω x : ℂ)‖ = 1) ∧
      ∀ x ∈ idelesTrivialAt (((S0 (K := K) : Finset (HeightOneSpectrum (𝓞 K)))) : Set (HeightOneSpectrum (𝓞 K))),
        ∀ ξ : Kˣ, ξ ∈ A0 (K := K) → ideleToIdeal K x = toPrincipalIdeal (𝓞 K) K ξ →
          (ω x : ℂ) = starRingEnd ℂ (σ (ξ : K)) / ((‖σ (ξ : K)‖ : ℝ) : ℂ) := by
  obtain ⟨φ, hφ, hc⟩ := exists_prop17Condition (psiInf σ) psiFin
  obtain ⟨ω, hωc, hωG, hωK⟩ := exists_extension isOpen_gInf0 isOpen_gFin0 gFin0_val φ (psiInf σ) psiFin
    (continuous_psiInf σ) (fun v => continuous_const) hc
  have hφn : ∀ b : Ideals3 (K := K), ‖(φ b : ℂ)‖ = 1 := by
    intro b
    obtain ⟨a, rfl⟩ := fA_surjective b
    rw [hφ]
    exact norm_psiProd σ _
  refine ⟨ω, hωc, hωK, ?_, ?_⟩
  · intro x
    have hx : x ∈ gGP S0 gInf0 gFin0 ⊔ (IdeleGroup.unitEmbedding (𝓞 K) K).range := by
      rw [gGP_sup_range_eq_top isOpen_gInf0 isOpen_gFin0]; exact Subgroup.mem_top x
    obtain ⟨h, hh, k, ⟨ξ, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hx
    rw [map_mul, hωK, mul_one]
    have := hωG ⟨h, hh⟩
    change (ω h : ℂˣ) = _ at this
    rw [this, fGP_apply, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, norm_psiProd, hφn]
    simp
  · intro x hx ξ hξ hxξ
    have hb : ((fA ⟨ξ, hξ⟩ : Ideals3 (K := K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x := by
      rw [fA_val, hxξ]
    have h1 := fGP_of_mem_idelesTrivialAt gFin0_val φ (psiInf σ) psiFin x hx _ hb
    have h2 := hωG ⟨x, idelesTrivialAt_le_gGP hx⟩
    change (ω x : ℂˣ) = _ at h2
    rw [h1, hφ] at h2
    rw [h2]
    exact psiProd_pprojG_embA σ ⟨ξ, hξ⟩


theorem primeUnitIdeal_eq {v : HeightOneSpectrum (𝓞 K)} {ξ : 𝓞 K} (hξ0 : (ξ : K) ≠ 0)
    (h : v.asIdeal = Ideal.span {ξ}) :
    primeUnitIdeal v = toPrincipalIdeal (𝓞 K) K (Units.mk0 (ξ : K) hξ0) := by
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  show ((v.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = _
  rw [h, FractionalIdeal.coeIdeal_span_singleton]
  rfl

theorem three_dvd_sub_one_mem_A0 {ξ : 𝓞 K} (hξ0 : (ξ : K) ≠ 0) (h3 : (3 : 𝓞 K) ∣ ξ - 1) :
    Units.mk0 (ξ : K) hξ0 ∈ A0 (K := K) := by
  rw [mem_A0]
  have e : ((Units.mk0 (ξ : K) hξ0 : Kˣ) : K) - 1 = ((ξ - 1 : 𝓞 K) : K) := by simp
  rw [e]
  exact (dvd_three_iff _).1 h3

/-- **The character $\omega_0$ with its values** at the idèles supported at one prime. -/
theorem exists_omega0_values (σ : K →+* ℂ) :
    ∃ ω : IdeleGroup (𝓞 K) K →* ℂˣ, Continuous ω ∧
      (∀ ξ : Kˣ, ω (IdeleGroup.unitEmbedding (𝓞 K) K ξ) = 1) ∧ (∀ x, ‖(ω x : ℂ)‖ = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), (3 : 𝓞 K) ∉ v.asIdeal → ∀ u : (v.adicCompletion K)ˣ,
        Valued.v (u : v.adicCompletion K) = 1 → ω (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) = 1) ∧
      (∀ ξ : 𝓞 K, (3 : 𝓞 K) ∣ ξ - 1 → ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal = Ideal.span {ξ} →
        ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = WithZero.exp (-1) →
          (ω (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) : ℂ) =
            starRingEnd ℂ (σ (ξ : K)) / ((‖σ (ξ : K)‖ : ℝ) : ℂ)) := by
  obtain ⟨ω, hc, hK, hn, hv⟩ := exists_omega0 σ
  have htriv : ∀ (v : HeightOneSpectrum (𝓞 K)), v ≠ vL → ∀ u : (v.adicCompletion K)ˣ,
      IdeleGroup.ofAdicCompletion (𝓞 K) K v u ∈
        idelesTrivialAt (((S0 (K := K) : Finset (HeightOneSpectrum (𝓞 K)))) : Set (HeightOneSpectrum (𝓞 K))) := by
    intro v hvL u
    refine ⟨fun w => ofAdicCompletion_infAt v u w, fun w hw => ?_⟩
    have : w = vL := Finset.mem_singleton.1 hw
    exact ofAdicCompletion_finAt_ne (fun h => hvL (h.symm.trans this)) u
  refine ⟨ω, hc, hK, hn, ?_, ?_⟩
  · intro v h3 u hu
    have hvL : v ≠ vL := fun h => h3 (h ▸ three_mem_vL)
    have := hv _ (htriv v hvL u) 1 (one_mem _) (by
      rw [map_one]; exact ideleToIdeal_ofAdicCompletion_unit v u hu)
    apply Units.ext
    rw [this]; simp
  · intro ξ h3 v hspan u hu
    have hξ0 : (ξ : K) ≠ 0 := by
      intro h0
      have : ξ = 0 := by exact_mod_cast h0
      subst this
      rw [Ideal.span_singleton_eq_bot.2 rfl] at hspan
      exact v.ne_bot hspan
    have hvL : v ≠ vL := by
      intro h
      subst h
      rw [vL_asIdeal] at hspan
      have h1 : lam ∣ ξ := Ideal.span_singleton_le_span_singleton.1 hspan.ge
      have h2 : lam ∣ ξ - 1 := lam_dvd_three.trans h3
      have h4 : lam ∣ (1 : 𝓞 K) := by
        have := dvd_sub h1 h2
        simpa using this
      exact lam_prime.not_isUnit (isUnit_of_dvd_one h4)
    exact hv _ (htriv v hvL u) _ (three_dvd_sub_one_mem_A0 hξ0 h3)
      (by rw [ideleToIdeal_ofAdicCompletion_uniformizer v u hu, primeUnitIdeal_eq hξ0 hspan])

end NumberFieldKB.MilneCFT.Ch8.Ex101
