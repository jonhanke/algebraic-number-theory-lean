import NumberFieldKB.MilneCFT.LubinTate.KroneckerWeber
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.Herbrand.UpperQuotient
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.FiniteExtension.IntermediateField
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.RamificationIndex

/-!
# Our ramification filtrations are Tau Ceti's (Milne, *CFT*, I, §4)

$K$ is a nonarchimedean local field, $\Omega$ a separable closure and $L\subseteq\Omega$ a finite Galois extension
of $K$. Our filtrations (`LubinTate/KroneckerWeber.lean`) use only the $K$-algebra $L$: the ring
$\mathcal O_L$ = `integers L` (the integral closure of $\mathcal O_K$), the ideal $\mathfrak m_L$ = `maxIdealL L`
(the radical of $\mathfrak m_K\mathcal O_L$), the lower groups `ramificationGroup L i`, `ramificationGroupReal L u`,
the Herbrand function `herbrandPhi L` and the upper groups `upperRamificationGroup L v`. Tau Ceti's (ported under
`NumberFieldKB/TauCetiPort/`, Apache 2.0) need a local-field structure on $L$ (a valuative relation extending $K$'s);
Tau Ceti installs the unique one on a finite intermediate field (`TauCeti.finiteIntermediateFieldValuativeRel`).

For **any** such structure on $L$ this file proves:

* `comap_maxIdealL`: $\mathfrak m_L$ is the maximal ideal of $\mathcal O_L = $ `𝒪[L]`
  (`TauCeti.integerRingEquivIntegralClosure`; $\mathfrak m_K\mathcal O_L = \mathfrak m_L^{e}$ with $e>0$);
* `ramificationGroup_eq_lowerRamificationGroup`, `ramificationGroupReal_eq_lowerRamificationGroupReal`: the lower
  filtrations agree;
* `herbrandPhi_eq_herbrand`: the Herbrand functions agree on $[-1,\infty)$;
* `upperRamificationGroup_eq`: the upper filtrations agree for $v\ge0$.

Then **`herbrandQuotient`** proves the named statement `HerbrandQuotient` (Milne, *CFT*, I, Proposition 4.4) from
Tau Ceti's `TauCeti.LocalFieldsRamification.map_restrictNormalHom_upperRamificationGroup`.
-/

open scoped ValuativeRel

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Compatible

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [ValuativeRel L] [TopologicalSpace L]
  [ValuativeExtension K L] [IsNonarchimedeanLocalField L]

omit [FiniteDimensional K L] in
/-- $\mathfrak m_L$ (`maxIdealL L`, the radical of $\mathfrak m_K\mathcal O_L$) is the maximal ideal of `𝒪[L]`,
through `TauCeti.integerRingEquivIntegralClosure`. -/
theorem comap_maxIdealL :
    (maxIdealL L).comap ((TauCeti.integerRingEquivIntegralClosure K L).toRingEquiv :
      𝒪[L] →+* integers L) = 𝓂[L] := by
  set f : 𝒪[L] ≃+* integers L := (TauCeti.integerRingEquivIntegralClosure K L).toRingEquiv
  have he : (f : 𝒪[L] →+* integers L).comp (algebraMap 𝒪[K] 𝒪[L]) = algebraMap 𝒪[K] (integers L) :=
    RingHom.ext fun x => (TauCeti.integerRingEquivIntegralClosure K L).commutes x
  have hmap : (𝓂[K].map (algebraMap 𝒪[K] (integers L))).comap (f : 𝒪[L] →+* integers L) =
      𝓂[K].map (algebraMap 𝒪[K] 𝒪[L]) := by
    rw [← he, ← Ideal.map_map]
    exact Ideal.comap_map_of_bijective (f : 𝒪[L] →+* integers L) f.bijective
  rw [maxIdealL, Ideal.comap_radical, hmap, TauCeti.map_maximalIdeal_eq_maximalIdeal_pow,
    Ideal.radical_pow _ TauCeti.ramificationIndex_pos.ne',
    (IsLocalRing.maximalIdeal.isMaximal _).isPrime.radical]

omit [FiniteDimensional K L] in
theorem mem_maxIdealL_pow_iff (n : ℕ) (b : integers L) :
    b ∈ maxIdealL L ^ n ↔ (TauCeti.integerRingEquivIntegralClosure K L).symm b ∈ 𝓂[L] ^ n := by
  set f : 𝒪[L] ≃+* integers L := (TauCeti.integerRingEquivIntegralClosure K L).toRingEquiv
  have h1 : maxIdealL L = (𝓂[L]).map (f : 𝒪[L] →+* integers L) := by
    rw [← comap_maxIdealL L]
    exact (Ideal.map_comap_of_surjective (f : 𝒪[L] →+* integers L) f.surjective _).symm
  rw [h1, ← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  rfl

open TauCeti.LocalFieldsRamification

/-- **The lower ramification groups agree**: our $G_i$ (`ramificationGroup L i`) is Tau Ceti's
`lowerRamificationGroup K L i`, for every $i\ge0$. -/
theorem ramificationGroup_eq_lowerRamificationGroup (i : ℕ) :
    ramificationGroup L i = lowerRamificationGroup K L i := by
  ext σ
  rw [mem_lowerRamificationGroup_iff]
  have hi : ((i : ℤ) + 1).toNat = i + 1 := by omega
  rw [hi]
  set e := TauCeti.integerRingEquivIntegralClosure K L
  constructor
  · intro hσ x
    have hx : (x : L) ∈ integers L := by
      rw [← TauCeti.coe_integerRingEquivIntegralClosure_apply (K := K) x]
      exact (e x).2
    obtain ⟨b, hb, hba⟩ := hσ (x : L) hx
    have : e.symm b = σ • x - x := by
      apply Subtype.ext
      rw [TauCeti.coe_integerRingEquivIntegralClosure_symm_apply, hba]
      simp
    rw [← this]
    exact (mem_maxIdealL_pow_iff L _ b).1 hb
  · intro hσ a ha
    set x : 𝒪[L] := e.symm ⟨a, ha⟩ with hxdef
    have hxa : (x : L) = a := by
      rw [hxdef, TauCeti.coe_integerRingEquivIntegralClosure_symm_apply]
    refine ⟨e (σ • x - x), ?_, ?_⟩
    · rw [mem_maxIdealL_pow_iff, AlgEquiv.symm_apply_apply]
      exact hσ x
    · rw [TauCeti.coe_integerRingEquivIntegralClosure_apply]
      simp [hxa]

/-- **The real-indexed lower ramification groups agree**: `ramificationGroupReal L u` ($G_{\lceil u\rceil}$, and
$G$ for $u\le-1$) is Tau Ceti's `lowerRamificationGroupReal K L u`, for every real $u$. -/
theorem ramificationGroupReal_eq_lowerRamificationGroupReal (u : ℝ) :
    ramificationGroupReal L u = lowerRamificationGroupReal K L u := by
  rw [lowerRamificationGroupReal_def, ramificationGroupReal]
  split_ifs with hu
  · rw [lowerRamificationGroup_eq_top_of_le_neg_one]
    exact Int.ceil_le.2 (by exact_mod_cast hu)
  · rw [not_le] at hu
    have h0 : 0 ≤ ⌈u⌉ := Int.ceil_nonneg_of_neg_one_lt hu
    rw [ramificationGroup_eq_lowerRamificationGroup]
    congr 1
    rw [← Int.ceil_toNat, Int.toNat_of_nonneg h0]

/-- On $(-1,\infty)$, our integrand $1/(G_0:G_t)$ is Tau Ceti's $\#G_t/\#G_0$. -/
theorem inv_relIndex_eq (t : ℝ) (ht : -1 < t) :
    1 / ((ramificationGroupReal L t).relIndex (ramificationGroup L 0) : ℝ) =
      (Nat.card (lowerRamificationGroupReal K L t) : ℝ) / Nat.card (lowerRamificationGroup K L 0) := by
  rw [ramificationGroupReal_eq_lowerRamificationGroupReal, ramificationGroup_eq_lowerRamificationGroup,
    Nat.cast_zero]
  have hle : lowerRamificationGroupReal K L t ≤ lowerRamificationGroup K L 0 := by
    rw [lowerRamificationGroupReal_def]
    exact lowerRamificationGroup_antitone K L (by exact_mod_cast Int.ceil_nonneg_of_neg_one_lt ht)
  have h := Subgroup.relIndex_mul_card (lowerRamificationGroupReal K L t) (lowerRamificationGroup K L 0)
  rw [inf_of_le_left hle] at h
  have hpos : (0 : ℝ) < Nat.card (lowerRamificationGroupReal K L t) := by
    exact_mod_cast Nat.card_pos
  have hpos' : (0 : ℝ) < ((lowerRamificationGroupReal K L t).relIndex (lowerRamificationGroup K L 0) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at h; exact (Nat.card_pos.ne' h.symm))
  have h' : ((lowerRamificationGroupReal K L t).relIndex (lowerRamificationGroup K L 0) : ℝ) *
      Nat.card (lowerRamificationGroupReal K L t) = Nat.card (lowerRamificationGroup K L 0) := by
    exact_mod_cast h
  rw [← h']
  field_simp

variable [IsGalois K L]

/-- **The Herbrand functions agree** on $[-1,\infty)$: our `herbrandPhi L u` is Tau Ceti's `herbrand K L u`. -/
theorem herbrandPhi_eq_herbrand (u : ℝ) (hu : -1 ≤ u) :
    herbrandPhi L u = (herbrand K L ⟨u, hu⟩ : ℝ) := by
  rw [coe_herbrand, herbrandPhi]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
  have ht' : -1 < t := by
    rw [Set.uIoc, Set.mem_Ioc] at ht
    have : -1 ≤ min 0 u := le_min (by norm_num) hu
    linarith [ht.1]
  exact inv_relIndex_eq L t ht'

/-- **The upper ramification groups agree** for $v\ge0$: our `upperRamificationGroup L v`
($G_{\psi(v)}$, $\psi(v)$ the least $u\ge0$ with $\varphi(u)\ge v$) is Tau Ceti's `upperRamificationGroup K L v`. -/
theorem upperRamificationGroup_eq (v : ℝ) (hv : 0 ≤ v) :
    upperRamificationGroup L v =
      TauCeti.LocalFieldsRamification.upperRamificationGroup K L ⟨v, by simp only [Set.mem_Ici]; linarith⟩ := by
  set V : RamificationIndexDomain := ⟨v, by simp only [Set.mem_Ici]; linarith⟩
  set w := inverseHerbrand K L V
  have hw : herbrand K L w = V := herbrand_inverseHerbrand K L V
  have h0 : herbrand K L ⟨0, by simp⟩ = ⟨0, by simp⟩ := Subtype.ext (by rw [coe_herbrand]; simp)
  have hw0 : (0 : ℝ) ≤ w := by
    by_contra hlt
    rw [not_le] at hlt
    have : herbrand K L w < herbrand K L ⟨0, by simp⟩ := herbrand_strictMono K L (Subtype.mk_lt_mk.2 hlt)
    rw [hw, h0, Subtype.mk_lt_mk] at this
    linarith
  have hφ : ∀ u : ℝ, ∀ hu : 0 ≤ u, herbrandPhi L u = (herbrand K L ⟨u, by simp only [Set.mem_Ici]; linarith⟩ : ℝ) :=
    fun u hu => herbrandPhi_eq_herbrand L u (by linarith)
  have hS : {u : ℝ | 0 ≤ u ∧ v ≤ herbrandPhi L u} = Set.Ici (w : ℝ) := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_Ici]
    constructor
    · rintro ⟨hu0, hvu⟩
      by_contra hlt
      rw [not_le] at hlt
      have : herbrand K L ⟨u, by simp only [Set.mem_Ici]; linarith⟩ < herbrand K L w :=
        herbrand_strictMono K L (Subtype.mk_lt_mk.2 hlt)
      rw [hw, ← Subtype.coe_lt_coe, ← hφ u hu0] at this
      exact absurd hvu (not_le.2 this)
    · intro hwu
      refine ⟨hw0.trans hwu, ?_⟩
      have : herbrand K L w ≤ herbrand K L ⟨u, by simp only [Set.mem_Ici]; linarith [hw0.trans hwu]⟩ :=
        (herbrand_strictMono K L).monotone (Subtype.mk_le_mk.2 hwu)
      rw [hw, ← Subtype.coe_le_coe, ← hφ u (hw0.trans hwu)] at this
      exact this
  rw [upperRamificationGroup, hS, csInf_Ici, ramificationGroupReal_eq_lowerRamificationGroupReal,
    upperRamificationGroup_def]

end Compatible

/-! ### Proposition 4.4 -/

variable (K Ω) in
/-- **Proposition 4.4 (Herbrand), proved** (Milne, *CFT*, I, Proposition 4.4, p. 46; Serre, *Local Fields*, IV.3,
Proposition 14): the named statement `HerbrandQuotient` holds: for finite Galois $M\supseteq L\supseteq K$ inside
$\Omega$ and $v\ge0$, restriction maps $\mathrm{Gal}(M/K)^v$ onto $\mathrm{Gal}(L/K)^v$. From Tau Ceti's
`TauCeti.LocalFieldsRamification.map_restrictNormalHom_upperRamificationGroup` (ported), with $L$ and $M$ given Tau
Ceti's local-field structures (`TauCeti.finiteIntermediateFieldValuativeRel`), $M$ a valuative extension of $L$ by
uniqueness of the extended valuation (`AlgHom.valuativeExtension`), and `upperRamificationGroup_eq`. -/
@[kb "milne2020cft" "Ch. I, Proposition 4.4"]
theorem herbrandQuotient : HerbrandQuotient K Ω := by
  refine ⟨fun L M _ _ _ _ h v hv => ?_⟩
  let _ : ValuativeRel L := TauCeti.finiteIntermediateFieldValuativeRel K Ω L
  let _ : TopologicalSpace L := TauCeti.finiteIntermediateFieldTopology K Ω L
  have : ValuativeExtension K L := TauCeti.finiteIntermediateField_valuativeExtension K Ω L
  have : IsNonarchimedeanLocalField L := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω L
  let _ : ValuativeRel M := TauCeti.finiteIntermediateFieldValuativeRel K Ω M
  let _ : TopologicalSpace M := TauCeti.finiteIntermediateFieldTopology K Ω M
  have : ValuativeExtension K M := TauCeti.finiteIntermediateField_valuativeExtension K Ω M
  have : IsNonarchimedeanLocalField M := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω M
  let _ : Algebra L M := (IntermediateField.inclusion h).toAlgebra
  have : ValuativeExtension L M := (IntermediateField.inclusion h).valuativeExtension
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite L M := Module.Finite.of_restrictScalars_finite K L M
  rw [upperRamificationGroup_eq M v hv, upperRamificationGroup_eq L v hv]
  exact TauCeti.LocalFieldsRamification.map_restrictNormalHom_upperRamificationGroup K L M _

end NumberFieldKB.MilneCFT.LocalCFT
