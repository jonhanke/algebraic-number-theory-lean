import NumberFieldKB.MilneCFT.Ch5IdelicMain
import NumberFieldKB.MilneANT.Ch8Examples

/-!
# The idèles of $\mathbb Q$ (Milne, *Class Field Theory*, Chapter V, §5, pp. 180–182)

**Lemma 5.9** (`lemma_5_9`), $C_\mathbb Q \cong \mathbb R_{>0}\times\hat{\mathbb Z}^\times$ (`ideleClassGroup_rat`), and
the Artin map of $\mathbb Q(\zeta_m)$ (`artin_cyclotomic`, also Milne's Example 4.10).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev Filter Topology
open scoped nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

/-! ## The example of $\mathbb Q$ (pp. 180–182) -/

/-! ### Helpers for Lemma 5.9 -/

section Rat59

open NumberFieldKB.Chebotarev.RatIdele

/-- Every infinite place of $\mathbb Q$ is real. -/
theorem infinitePlace_isReal (w : InfinitePlace ℚ) : w.IsReal := by
  obtain rfl := Subsingleton.elim w Rat.infinitePlace
  exact Rat.isReal_infinitePlace

/-- The isomorphism of topological groups $\mathbb R \cong \prod_{w\mid\infty}\mathbb Q_w$ (multiplicative structure). -/
def realInf : ℝ ≃ₜ* InfiniteAdeleRing ℚ where
  toFun r := fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (infinitePlace_isReal w)).symm r
  invFun f := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace (f Rat.infinitePlace)
  left_inv r := by simp
  right_inv f := by
    funext w
    obtain rfl := Subsingleton.elim w Rat.infinitePlace
    exact RingEquiv.symm_apply_apply _ _
  map_mul' r s := by
    funext w
    rw [Pi.mul_apply]
    exact map_mul _ _ _
  continuous_toFun := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal (infinitePlace_isReal w)).symm.continuous
  continuous_invFun := by
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous.comp
      (continuous_apply Rat.infinitePlace)

theorem realInf_apply (r : ℝ) (w : InfinitePlace ℚ) (hw : w.IsReal) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (realInf r w) = r := by
  show InfinitePlace.Completion.ringEquivRealOfIsReal hw
    ((InfinitePlace.Completion.ringEquivRealOfIsReal (infinitePlace_isReal w)).symm r) = r
  exact RingEquiv.apply_symm_apply _ _


/-- Valuation one in terms of integrality of an element and its inverse. -/
theorem val_eq_one_of_le_of_inv_le {a b : WithZero (Multiplicative ℤ)} (ha : a ≤ 1) (hb : b ≤ 1) (hab : a * b = 1) :
    a = 1 := by
  refine le_antisymm ha ?_
  by_contra hlt
  replace hlt := not_le.mp hlt
  have : a * b ≤ a * 1 := mul_le_mul' le_rfl hb
  rw [hab, mul_one] at this
  exact absurd hlt (not_lt.mpr this)

/-- The units $\prod_p\mathbb Z_p^\times$ of the finite idèles of $\mathbb Q$ form an open subgroup. -/
theorem isOpen_finiteIdeleUnits :
    IsOpen (finiteIdeleUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
  have hO : IsOpen {f : FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ v : Pl, f v ∈ v.adicCompletionIntegers ℚ} :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : Pl => v.adicCompletion ℚ)
      (A := fun v : Pl => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
      (fun v => Valued.isOpen_valuationSubring _)
  have h1 : IsOpen {x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ | ∀ v : Pl, (x : FiniteAdeleRing (𝓞 ℚ) ℚ) v ∈
      v.adicCompletionIntegers ℚ} := hO.preimage Units.continuous_val
  have h2 : IsOpen {x : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ | ∀ v : Pl, ((x⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v ∈ v.adicCompletionIntegers ℚ} := hO.preimage Units.continuous_coe_inv
  convert h1.inter h2 using 1
  ext x
  constructor
  · intro hx
    refine ⟨fun v => ?_, fun v => ?_⟩
    · exact (hx v).le
    · have h := QuadFormsKB.Tamagawa.Measure.Weil.valued_mul_inv x v
      rw [hx v, one_mul] at h
      exact h.le
  · rintro ⟨h1, h2⟩ v
    exact val_eq_one_of_le_of_inv_le (h1 v) (h2 v) (QuadFormsKB.Tamagawa.Measure.Weil.valued_mul_inv x v)

/-- The splitting of an idèle of $\mathbb Q$ into its infinite and finite parts, as a homeomorphism. -/
abbrev splitE : IdQ ≃ₜ (InfiniteAdeleRing ℚ)ˣ × (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := Homeomorph.prodUnits

/-- $t \mapsto t$ in the infinite units. -/
def posInf : Units.posSubgroup ℝ →* (InfiniteAdeleRing ℚ)ˣ :=
  ((Units.mapContinuousMulEquiv realInf).toMulEquiv : ℝˣ ≃* (InfiniteAdeleRing ℚ)ˣ).toMonoidHom.comp
    (Units.posSubgroup ℝ).subtype

/-- The idèle $t$ at $\infty$ and $1$ at the finite primes. -/
def posPartHom : Units.posSubgroup ℝ →* IdQ :=
  (MulEquiv.prodUnits.symm : (InfiniteAdeleRing ℚ)ˣ × (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ≃* IdQ).toMonoidHom.comp
    ((MonoidHom.inl _ _).comp posInf)

/-- The idèle $u$ at the finite primes and $1$ at $\infty$. -/
def finPartHom : finiteIdeleUnits ℚ →* IdQ :=
  (MulEquiv.prodUnits.symm : (InfiniteAdeleRing ℚ)ˣ × (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ≃* IdQ).toMonoidHom.comp
    ((MonoidHom.inr _ _).comp (finiteIdeleUnits ℚ).subtype)

theorem splitE_posPart_mul_finPart (t : Units.posSubgroup ℝ) (u : finiteIdeleUnits ℚ) :
    posPartHom t * finPartHom u = splitE.symm (posInf t, (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) := by
  show MulEquiv.prodUnits.symm (posInf t, 1) * MulEquiv.prodUnits.symm (1, (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) = _
  rw [← map_mul]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]
  rfl

theorem isOpenEmbedding_posInf : IsOpenEmbedding posInf := by
  have h1 : IsOpen (Units.posSubgroup ℝ : Set ℝˣ) := by
    have : (Units.posSubgroup ℝ : Set ℝˣ) = Units.val ⁻¹' (Set.Ioi 0) := by
      ext x; simp [Units.mem_posSubgroup]
    rw [this]
    exact isOpen_Ioi.preimage Units.continuous_val
  exact (Units.mapContinuousMulEquiv realInf).toHomeomorph.isOpenEmbedding.comp h1.isOpenEmbedding_subtypeVal

theorem isOpenEmbedding_posPart_mul_finPart :
    IsOpenEmbedding (fun x : Units.posSubgroup ℝ × finiteIdeleUnits ℚ => posPartHom x.1 * finPartHom x.2) := by
  have h : (fun x : Units.posSubgroup ℝ × finiteIdeleUnits ℚ => posPartHom x.1 * finPartHom x.2) =
      splitE.symm ∘ Prod.map posInf (Subtype.val : finiteIdeleUnits ℚ → (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    funext x
    exact splitE_posPart_mul_finPart x.1 x.2
  rw [h]
  exact splitE.symm.isOpenEmbedding.comp
    (isOpenEmbedding_posInf.prodMap (isOpen_finiteIdeleUnits.isOpenEmbedding_subtypeVal))

theorem ideleInfAt_posPart (t : Units.posSubgroup ℝ) (w : InfinitePlace ℚ) :
    ideleInfAt (posPartHom t) w = realInf ((t : ℝˣ) : ℝ) w := rfl

theorem ideleFinAt_posPart (t : Units.posSubgroup ℝ) (v : Pl) : ideleFinAt (posPartHom t) v = 1 := rfl

theorem ideleInfAt_finPart (u : finiteIdeleUnits ℚ) (w : InfinitePlace ℚ) : ideleInfAt (finPartHom u) w = 1 := rfl

theorem ideleFinAt_finPart (u : finiteIdeleUnits ℚ) (v : Pl) :
    ideleFinAt (finPartHom u) v = ((u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v := rfl

theorem realPart_posPart (t : Units.posSubgroup ℝ) : realPart (posPartHom t) = ((t : ℝˣ) : ℝ) :=
  realInf_apply _ Rat.infinitePlace Rat.isReal_infinitePlace

theorem realPart_finPart (u : finiteIdeleUnits ℚ) : realPart (finPartHom u) = 1 := map_one eInf

/-- The product of the prime-power factors of the rational part is positive. -/
theorem finprod_ratFactor_pos (x : IdQ) : 0 < ((∏ᶠ v, ratFactor x v : ℚˣ) : ℚ) := by
  refine finprod_induction (p := fun a : ℚˣ => 0 < (a : ℚ)) (f := ratFactor x) (by simp)
    (fun a b ha hb => by simpa using mul_pos ha hb) (fun v => ?_)
  show 0 < ((prU v ^ ordV v x : ℚˣ) : ℚ)
  rw [Units.val_zpow_eq_zpow_val]
  exact zpow_pos (by simpa [prU] using (pr_prime v).pos) _

/-- The real component of $x/q(x)$ is positive. -/
theorem realPart_unitPart_pos (x : IdQ) : 0 < realPart (unitPart x) := by
  have hq : ((ratPart x : ℚˣ) : ℚ) = ((sgnInf x : ℚˣ) : ℚ) * ((∏ᶠ v, ratFactor x v : ℚˣ) : ℚ) := by
    rw [ratPart_apply, Units.val_mul]
  have hP := finprod_ratFactor_pos x
  have hr : realPart (unitPart x) = realPart x * (((ratPart x : ℚˣ) : ℚ) : ℝ)⁻¹ := by
    have h1 : realPart (diag (ratPart x))⁻¹ = (realPart (diag (ratPart x)))⁻¹ := by
      refine eq_inv_of_mul_eq_one_right ?_
      rw [← realPart_mul, mul_inv_cancel, realPart_one]
    rw [unitPart_apply, realPart_mul, h1, realPart_diag]
  rw [hr]
  have hx := realPart_ne_zero x
  have hs : ((sgnInf x : ℚˣ) : ℚ) = if 0 < realPart x then 1 else -1 := by
    show (((if 0 < realPart x then 1 else -1 : ℚˣ)) : ℚ) = _
    split_ifs <;> simp
  by_cases h0 : 0 < realPart x
  · simp only [hs, h0, ↓reduceIte, one_mul] at hq
    rw [hq]
    exact mul_pos h0 (inv_pos.mpr (by exact_mod_cast hP))
  · have hneg : realPart x < 0 := lt_of_le_of_ne (not_lt.mp h0) hx
    simp only [hs, h0, ↓reduceIte] at hq
    have hq' : ((ratPart x : ℚˣ) : ℚ) < 0 := by rw [hq]; linarith
    have : (((ratPart x : ℚˣ) : ℚ) : ℝ) < 0 := by exact_mod_cast hq'
    exact mul_pos_of_neg_of_neg hneg (inv_lt_zero.mpr this)

/-- Every idèle of $\mathbb Q$ is $a\,t\,u$. -/
theorem decomp_surj (x : IdQ) : ∃ (a : ℚˣ) (t : Units.posSubgroup ℝ) (u : finiteIdeleUnits ℚ),
    diag a * posPartHom t * finPartHom u = x := by
  set y := unitPart x with hy
  have hxy : x = diag (ratPart x) * y := by
    rw [hy, unitPart_apply, mul_left_comm, mul_inv_cancel, mul_one]
  let t : Units.posSubgroup ℝ :=
    ⟨Units.mk0 (realPart y) (realPart_ne_zero y), (Units.mem_posSubgroup _).mpr (realPart_unitPart_pos x)⟩
  let u : finiteIdeleUnits ℚ :=
    ⟨Units.map (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ →+*
      FiniteAdeleRing (𝓞 ℚ) ℚ).toMonoidHom y, fun v => valued_unitPart v x⟩
  refine ⟨ratPart x, t, u, ?_⟩
  have hy' : y = posPartHom t * finPartHom u := by
    rw [splitE_posPart_mul_finPart]
    apply splitE.injective
    rw [Homeomorph.apply_symm_apply]
    refine Prod.ext (Units.ext ?_) rfl
    funext w
    obtain rfl := Subsingleton.elim w Rat.infinitePlace
    exact (RingEquiv.symm_apply_apply (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
      ((y : AdeleRing (𝓞 ℚ) ℚ).1 Rat.infinitePlace)).symm
  rw [mul_assoc, ← hy', ← hxy]

theorem comm_aux {G : Type*} [CommGroup G] (A B C D E F : G) (h : A * B * C = D * E * F) :
    A * D⁻¹ = (E * B⁻¹) * (F * C⁻¹) := by
  calc A * D⁻¹ = (A * B * C) * (B * C)⁻¹ * D⁻¹ := by group
    _ = (D * E * F) * (B * C)⁻¹ * D⁻¹ := by rw [h]
    _ = (E * F) * (B * C)⁻¹ := by rw [mul_comm _ D⁻¹]; group
    _ = (E * B⁻¹) * (F * C⁻¹) := by rw [mul_inv]; exact mul_mul_mul_comm _ _ _ _

/-- The rational part of $s\cdot w$, $s>0$ real at $\infty$, $w$ a unit at every finite place, is $1$. -/
theorem ratPart_posPart_mul_finPart (s : Units.posSubgroup ℝ) (w : finiteIdeleUnits ℚ) :
    ratPart (posPartHom s * finPartHom w) = 1 := by
  refine ratPart_eq_one_of ?_ fun v => ?_
  · rw [realPart_mul, realPart_posPart, realPart_finPart, mul_one]
    exact (Units.mem_posSubgroup _).mp s.2
  · have h1 : Valued.v (((posPartHom s * finPartHom w : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1 := by
      show Valued.v ((1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
        ((w : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1
      rw [show (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 from rfl, one_mul]
      exact w.2 v
    refine ⟨h1.le, ?_⟩
    have h2 := QuadFormsKB.Tamagawa.Measure.Weil.valued_mul_inv
      (Units.map (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ →+*
        FiniteAdeleRing (𝓞 ℚ) ℚ).toMonoidHom (posPartHom s * finPartHom w)) v
    rw [show Valued.v (((Units.map (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ) :
      AdeleRing (𝓞 ℚ) ℚ →+* FiniteAdeleRing (𝓞 ℚ) ℚ).toMonoidHom (posPartHom s * finPartHom w) :
      (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 from h1, one_mul] at h2
    exact h2.le

/-- Uniqueness of the decomposition. -/
theorem decomp_inj {a a' : ℚˣ} {t t' : Units.posSubgroup ℝ} {u u' : finiteIdeleUnits ℚ}
    (h : diag a * posPartHom t * finPartHom u = diag a' * posPartHom t' * finPartHom u') :
    a = a' ∧ t = t' ∧ u = u' := by
  have h1 := comm_aux _ _ _ _ _ _ h
  have h2 : diag (a * a'⁻¹) = posPartHom (t' * t⁻¹) * finPartHom (u' * u⁻¹) := by
    rw [map_mul, map_inv, map_mul, map_inv, map_mul, map_inv]
    exact h1
  have h3 : a * a'⁻¹ = 1 := by
    have := ratPart_diag (a * a'⁻¹)
    rw [h2, ratPart_posPart_mul_finPart] at this
    exact this.symm
  have haa : a = a' := mul_inv_eq_one.mp h3
  subst haa
  rw [mul_assoc, mul_assoc] at h
  have h4 := mul_left_cancel h
  have h5 := isOpenEmbedding_posPart_mul_finPart.injective (a₁ := (t, u)) (a₂ := (t', u')) h4
  exact ⟨rfl, congrArg Prod.fst h5, congrArg Prod.snd h5⟩

/-- The decomposition map, as a function of the three components. -/
theorem decomp_bijective : Function.Bijective (fun x : ℚˣ × Units.posSubgroup ℝ × finiteIdeleUnits ℚ =>
    IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ x.1 * posPartHom x.2.1 * finPartHom x.2.2) := by
  refine ⟨fun x y h => ?_, fun x => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := decomp_inj h
    exact Prod.ext h1 (Prod.ext h2 h3)
  · obtain ⟨a, t, u, h⟩ := decomp_surj x
    exact ⟨(a, t, u), h⟩

theorem lemma_5_9_aux :
    ∃ (posPart : Units.posSubgroup ℝ →* IdeleGroup (𝓞 ℚ) ℚ)
      (finPart : finiteIdeleUnits ℚ →* IdeleGroup (𝓞 ℚ) ℚ),
      (∀ t : Units.posSubgroup ℝ, (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (ideleInfAt (posPart t) w) = ((t : ℝˣ) : ℝ)) ∧
        ∀ v, ideleFinAt (posPart t) v = 1) ∧
      (∀ u : finiteIdeleUnits ℚ, (∀ w, ideleInfAt (finPart u) w = 1) ∧
        ∀ v, ideleFinAt (finPart u) v = ((u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ∧
      Function.Bijective (fun x : ℚˣ × Units.posSubgroup ℝ × finiteIdeleUnits ℚ =>
        IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ x.1 * posPart x.2.1 * finPart x.2.2) ∧
      Topology.IsOpenEmbedding (fun x : Units.posSubgroup ℝ × finiteIdeleUnits ℚ => posPart x.1 * finPart x.2) :=
  ⟨posPartHom, finPartHom, fun t => ⟨fun w hw => realInf_apply _ w hw, fun v => ideleFinAt_posPart t v⟩,
    fun u => ⟨fun w => ideleInfAt_finPart u w, fun v => ideleFinAt_finPart u v⟩, decomp_bijective,
    isOpenEmbedding_posPart_mul_finPart⟩

theorem ideleClassGroup_rat_aux :
    Nonempty (Units.posSubgroup ℝ × finiteIdeleUnits ℚ ≃ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) := by
  let F : Units.posSubgroup ℝ × finiteIdeleUnits ℚ →* IdQ := posPartHom.coprod finPartHom
  have hF : ∀ x, F x = posPartHom x.1 * finPartHom x.2 := fun x => by
    simp [F, MonoidHom.coprod_apply]
  let f : Units.posSubgroup ℝ × finiteIdeleUnits ℚ →* IdeleClassGroup (𝓞 ℚ) ℚ :=
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ)).comp F
  have hFe : IsOpenEmbedding F := by
    have : (F : _ → _) = fun x => posPartHom x.1 * finPartHom x.2 := funext hF
    rw [this]; exact isOpenEmbedding_posPart_mul_finPart
  have hcont : Continuous f := continuous_quot_mk.comp hFe.continuous
  have hopen : IsOpenMap f := (QuotientGroup.isOpenMap_coe).comp hFe.isOpenMap
  have hbij : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun c => ?_⟩
    · have h1 : (QuotientGroup.mk (F x) : IdeleClassGroup (𝓞 ℚ) ℚ) = QuotientGroup.mk (F y) := hxy
      rw [QuotientGroup.eq] at h1
      obtain ⟨a, ha⟩ := h1
      have ha' : diag a = (F x)⁻¹ * F y := ha
      have hy : F y = diag a * F x := by
        calc F y = F x * ((F x)⁻¹ * F y) := (mul_inv_cancel_left _ _).symm
          _ = diag a * F x := by rw [← ha', mul_comm]
      have h2 : diag a * posPartHom x.1 * finPartHom x.2 = diag 1 * posPartHom y.1 * finPartHom y.2 := by
        rw [map_one, one_mul, mul_assoc, ← hF x, ← hF y, hy]
      obtain ⟨-, h3, h4⟩ := decomp_inj h2
      exact Prod.ext h3 h4
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
      obtain ⟨a, t, u, h⟩ := decomp_surj x
      refine ⟨(t, u), ?_⟩
      show (QuotientGroup.mk (F (t, u)) : IdeleClassGroup (𝓞 ℚ) ℚ) = QuotientGroup.mk x
      rw [QuotientGroup.eq]
      refine ⟨a, ?_⟩
      show diag a = (F (t, u))⁻¹ * x
      rw [hF, ← h, mul_assoc, mul_comm (diag a), ← mul_assoc, inv_mul_cancel, one_mul]
  let H := (Equiv.ofBijective f hbij).toHomeomorphOfContinuousOpen hcont hopen
  exact ⟨{ toMulEquiv := MulEquiv.ofBijective f hbij
           continuous_toFun := hcont
           continuous_invFun := H.symm.continuous }⟩

end Rat59

/-- **Lemma 5.9** (Milne, *CFT*, V, p. 180): $(r, t, (u_p)) \mapsto (rt, ru_2, ru_3, \dots)$,
$\mathbb Q^\times \times \mathbb R_{>0} \times \prod_p\mathbb Z_p^\times \to I_\mathbb Q$, is an isomorphism of topological
groups ($\mathbb Q^\times$ discrete): it is a bijective homomorphism, and on $\mathbb R_{>0}\times\prod_p\mathbb Z_p^\times$
it is a topological embedding onto an open subgroup. Here `posPart t` is the idèle $t$ at $\infty$, $1$ at the finite
primes, and `finPart u` is $u$ at the finite primes, $1$ at $\infty$. -/
@[kb "milne2020cft" "Ch. V, Lemma 5.9"]
theorem lemma_5_9 :
    ∃ (posPart : Units.posSubgroup ℝ →* IdeleGroup (𝓞 ℚ) ℚ)
      (finPart : finiteIdeleUnits ℚ →* IdeleGroup (𝓞 ℚ) ℚ),
      (∀ t : Units.posSubgroup ℝ, (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (ideleInfAt (posPart t) w) = ((t : ℝˣ) : ℝ)) ∧
        ∀ v, ideleFinAt (posPart t) v = 1) ∧
      (∀ u : finiteIdeleUnits ℚ, (∀ w, ideleInfAt (finPart u) w = 1) ∧
        ∀ v, ideleFinAt (finPart u) v = ((u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ∧
      Function.Bijective (fun x : ℚˣ × Units.posSubgroup ℝ × finiteIdeleUnits ℚ =>
        IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ x.1 * posPart x.2.1 * finPart x.2.2) ∧
      Topology.IsOpenEmbedding (fun x : Units.posSubgroup ℝ × finiteIdeleUnits ℚ => posPart x.1 * finPart x.2) :=
  lemma_5_9_aux

/-- **After Lemma 5.9** (Milne, *CFT*, V, p. 180): $C_\mathbb Q \cong \mathbb R_{>0}\times\prod_p\mathbb Z_p^\times =
\mathbb R_{>0}\times\hat{\mathbb Z}^\times$ as topological groups. -/
@[kb "milne2020cft" "Ch. V, §5, p. 180 (C_Q ≅ R_{>0} × Ẑ^×)"]
theorem ideleClassGroup_rat :
    Nonempty (Units.posSubgroup ℝ × finiteIdeleUnits ℚ ≃ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) :=
  ideleClassGroup_rat_aux

/-! ### Helpers for the Artin map of $\mathbb Q(\zeta_m)$ -/

section ArtinCyclotomic

open NumberFieldKB.Chebotarev.RatIdele

/-- The prime of `ℤ` below a prime of `𝓞 ℚ` has ramification index one. -/
theorem ramIdx_base (v : Pl) : v.asIdeal.ramificationIdx ℤ = 1 := by
  have h1 : Algebra.FormallyUnramified ℤ (𝓞 ℚ) := by
    let e : 𝓞 ℚ ≃ₐ[ℤ] ℤ := AlgEquiv.ofRingEquiv (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))
      (fun x => by simp)
    exact (Algebra.FormallyUnramified.iff_of_equiv e).mpr inferInstance
  have : Algebra.IsUnramifiedAt ℤ v.asIdeal := inferInstance
  exact Ideal.ramificationIdx_eq_one _ _


/-- A prime of `ℤ` below `v` is `span {p}`. -/
theorem under_eq_span (v : Pl) : v.asIdeal.comap (algebraMap ℤ (𝓞 ℚ)) = Ideal.span {((pr v : ℕ) : ℤ)} := by
  have hp : Prime ((pr v : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp (pr_prime v)
  have hmax : (Ideal.span {((pr v : ℕ) : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime hp.ne_zero).mpr hp |>.isMaximal (by simpa using hp.ne_zero)
  have hle : Ideal.span {((pr v : ℕ) : ℤ)} ≤ v.asIdeal.comap (algebraMap ℤ (𝓞 ℚ)) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    have := (natCast_mem_asIdeal_iff v (pr v)).mpr dvd_rfl
    simpa using this
  exact (hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) hle).symm

theorem liesOver_span (L : Type) [Field L] [NumberField L] (v : Pl) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver v.asIdeal] : Q.LiesOver (Ideal.span {((pr v : ℕ) : ℤ)}) := by
  refine ⟨?_⟩
  rw [← under_eq_span]
  have h1 : Q.under (𝓞 ℚ) = v.asIdeal := (Ideal.LiesOver.over (p := v.asIdeal) (P := Q)).symm
  have h2 : (Q.under (𝓞 ℚ)).under ℤ = Q.under ℤ := Ideal.under_under (A := ℤ) (B := 𝓞 ℚ) Q
  rw [← h2, h1]

theorem ramIdx_eq (L : Type) [Field L] [NumberField L] (v : Pl) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver v.asIdeal] : Q.ramificationIdx (𝓞 ℚ) = Q.ramificationIdx ℤ := by
  have := Ideal.ramificationIdx_tower (R := ℤ) (S := 𝓞 ℚ) (T := 𝓞 L) v.asIdeal Q
  rw [this, ramIdx_base, one_mul]


section Cyc

variable (m : ℕ) [NeZero m] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L]

/-- A finite place of `ℚ` not dividing `m` is unramified in `ℚ(ζ_m)`. -/
theorem unramified_of_not_dvd {v : Pl} (hv : ¬ pr v ∣ m) : v ∈ unramifiedPrimes ℚ L := by
  have : Fact (pr v).Prime := ⟨pr_prime v⟩
  show Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro Q _ hQ
  have := liesOver_span L v Q
  rw [ramIdx_eq L v Q]
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd (pr v) L Q hv

/-- A finite place `p ∣ m` unramified in `ℚ(ζ_m)` has `p = 2` and `v_2(m) = 1`. -/
theorem eq_two_of_unramified {v : Pl} (hu : v ∈ unramifiedPrimes ℚ L) (hd : pr v ∣ m) :
    pr v = 2 ∧ m.factorization (pr v) = 1 := by
  have hp : (pr v).Prime := pr_prime v
  have : Fact (pr v).Prime := ⟨hp⟩
  have hm0 : m ≠ 0 := NeZero.ne m
  have hpos : 0 < m.factorization (pr v) := hp.factorization_pos_of_dvd hm0 hd
  obtain ⟨k, hk⟩ : ∃ k, m.factorization (pr v) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hn : m = (pr v) ^ (k + 1) * (m / (pr v) ^ (m.factorization (pr v))) := by
    rw [← hk]; exact (Nat.ordProj_mul_ordCompl_eq_self m (pr v)).symm
  have hnd : ¬ pr v ∣ m / (pr v) ^ (m.factorization (pr v)) := Nat.not_dvd_ordCompl hp hm0
  rw [hk] at hn hnd ⊢
  obtain ⟨⟨Q, hQp, hQo⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 L)
  have h1 : Q.ramificationIdx (𝓞 ℚ) = 1 := Algebra.IsUnramifiedIn.ramificationIdx_eq_one hu hQo
  have := liesOver_span L v Q
  rw [ramIdx_eq L v Q] at h1
  rw [IsCyclotomicExtension.Rat.ramificationIdx_eq m L Q hn hnd] at h1
  have h2 : 2 ≤ pr v := hp.two_le
  have h3 : (pr v) ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  have h4 : 1 ≤ (pr v) ^ k := Nat.one_le_iff_ne_zero.mpr h3
  have h5 : 1 ≤ pr v - 1 := by omega
  have h6 : (pr v) ^ k = 1 ∧ pr v - 1 = 1 := by
    constructor <;> nlinarith
  refine ⟨by omega, ?_⟩
  have : k = 0 := by
    by_contra hk0
    have : pr v ≤ (pr v) ^ k := Nat.le_self_pow hk0 _
    omega
  omega



/-- The only residue of a unit modulo `2` is `1`. -/
theorem zmod_two_unit {a b : ZMod (2 ^ 1)} (h : a * b = 1) : a = 1 := by
  revert a b; decide

/-- Real positivity at the infinite place from ramification: for `m > 2` the real place ramifies. -/
theorem ramifiesIn_infinite (hm : 2 < m) : InfinitePlace.RamifiesIn L Rat.infinitePlace := by
  refine ⟨Rat.isReal_infinitePlace, ?_⟩
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (K := L) Rat.infinitePlace
  refine ⟨w, hw, ?_⟩
  by_contra hc
  have hr : w.IsReal := by simpa [InfinitePlace.not_isComplex_iff_isReal] using hc
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ L
  set ψ := InfinitePlace.embedding_of_isReal hr
  have h1 : (ψ (IsCyclotomicExtension.zeta m ℚ L)) ^ m = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  have h2 : |ψ (IsCyclotomicExtension.zeta m ℚ L)| = 1 := by
    have : |ψ (IsCyclotomicExtension.zeta m ℚ L)| ^ m = 1 := by rw [← abs_pow, h1, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) (NeZero.ne m)).mp this
  have h3 : (ψ (IsCyclotomicExtension.zeta m ℚ L)) ^ 2 = 1 := by
    rw [← sq_abs, h2, one_pow]
  have h4 : (IsCyclotomicExtension.zeta m ℚ L) ^ 2 = 1 := by
    apply ψ.injective
    rw [map_pow, h3, map_one]
  have := Nat.le_of_dvd (by norm_num) (hζ.dvd_of_pow_eq_one 2 h4)
  omega



/-- Integrality of an idele with the valuation `1` at a finite place, and of its inverse. -/
theorem mem_integers_of_val_eq_one {u : IdQ} {v : Pl} (h : Valued.v (ideleFinAt u v) = 1) :
    (u : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ ∧
      ((u⁻¹ : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ := by
  refine ⟨le_of_eq h, ?_⟩
  have : ((u⁻¹ : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 v = (ideleFinAt u v)⁻¹ := by
    have e : ((u⁻¹ : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 v = ((compV v u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := rfl
    rw [e, map_inv, Units.val_inv_eq_inv_val]
    rfl
  show Valued.v (((u⁻¹ : IdQ) : AdeleRing (𝓞 ℚ) ℚ).2 v) ≤ 1
  rw [this, map_inv₀, h, inv_one]

/-- Reduction of a unit modulo `p^e` with `p^e = 2`: trivial. -/
theorem redP_unit_two {z : Kp 2 Nat.prime_two} (h : Valued.v z = 1) : redP 2 Nat.prime_two 1 z = 1 := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at h
  have h1 : Valued.v z⁻¹ ≤ 1 := by rw [map_inv₀, h, inv_one]
  have := redP_mul (p := 2) (hp := Nat.prime_two) (e := 1) h.le h1
  rw [mul_inv_cancel₀ hz0, redP_one] at this
  exact zmod_two_unit this.symm

/-- If `v (a - 1) < 1` then `v a = 1`. -/
theorem val_eq_one_of_sub_lt_one {F : Type*} [Field F] (v : Valuation F (WithZero (Multiplicative ℤ))) {a : F}
    {γ : WithZero (Multiplicative ℤ)} (hγ : γ < 1) (ha : v (a - 1) ≤ γ) : v a = 1 := by
  have := Valuation.map_eq_of_sub_lt v (x := 1) (y := a) (by simpa using ha.trans_lt hγ)
  simpa using this

/-- Reduction of a unit modulo `p^e` with `p = 2`, `e = 1`. -/
theorem redP_eq_one_of_two {p : ℕ} (hp : p.Prime) {e : ℕ} (he : e = 1) (hp2 : p = 2) (z : Kp p hp)
    (h : Valued.v z = 1) : redP p hp e z = 1 := by
  subst hp2; subst he; exact redP_unit_two h

/-- If `v (z - 1) ≤ exp (-m)` and `e ≤ m` then the reduction of `z` modulo `p^e` is `1`. -/
theorem redP_eq_one_of_close {p : ℕ} (hp : p.Prime) {e m : ℕ} (hle : e ≤ m) {z : Kp p hp}
    (h : Valued.v (z - 1) ≤ WithZero.exp (-(m : ℤ))) : redP p hp e z = 1 := by
  apply redP_eq_one
  have hP : Valued.v (p : Kp p hp) = WithZero.exp (-1) := valued_placeOf
  have h0 : Valued.v ((p : Kp p hp) ^ e) = WithZero.exp (-(e : ℤ)) := by
    rw [map_pow, hP, ← WithZero.exp_nsmul]; congr 1; simp
  rw [map_div₀, h0]
  have h1 : Valued.v (z - 1) ≤ WithZero.exp (-(e : ℤ)) :=
    h.trans (WithZero.exp_le_exp.mpr (by omega))
  exact (div_le_one₀ WithZero.exp_pos).mpr h1

/-- **The key local lemma**: `r(u) = 1` for idèles satisfying the hypotheses of property (a) for `ℚ(ζ_m)`. -/
theorem resMod_eq_one_of_local (u : IdQ)
    (h1 : ∀ v : Pl, v ∈ unramifiedPrimes ℚ L → Valued.v (ideleFinAt u v) = 1)
    (h2 : ∀ v : Pl, v ∉ unramifiedPrimes ℚ L → Valued.v (ideleFinAt u v - 1) ≤ WithZero.exp (-(m : ℤ)))
    (h3 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), InfinitePlace.RamifiesIn L w →
      IsPosAt w hw (ideleInfAt u w)) : resMod m u = 1 := by
  by_cases hm2 : m ≤ 2
  · have h : resMod m u * resMod m u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h0 : 0 < m := NeZero.pos m
    interval_cases m
    · exact Subsingleton.elim _ _
    · exact zmod_two_unit h
  · have hm2' : 2 < m := by omega
    have hpos : 0 < realPart u :=
      h3 Rat.infinitePlace Rat.isReal_infinitePlace (ramifiesIn_infinite m L hm2')
    have hγ : WithZero.exp (-(m : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hone : ∀ v : Pl, Valued.v (ideleFinAt u v) = 1 := fun v => by
      by_cases hv : v ∈ unramifiedPrimes ℚ L
      · exact h1 v hv
      · exact val_eq_one_of_sub_lt_one Valued.v hγ (h2 v hv)
    have hq : ratPart u = 1 := ratPart_eq_one_of hpos (fun v => mem_integers_of_val_eq_one (hone v))
    have hu : unitPart u = u := by rw [unitPart_apply, hq, map_one, inv_one, mul_one]
    refine resMod_eq_one_of m fun p => ?_
    rw [hu]
    obtain ⟨p, hpm⟩ := p
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
    by_cases hv : placeP m ⟨p, hpm⟩ ∈ unramifiedPrimes ℚ L
    · have hpr : pr (placeP m ⟨p, hpm⟩) = p := pr_placeOf p hpp
      obtain ⟨hp2, he⟩ := eq_two_of_unramified m L hv (by rw [hpr]; exact Nat.dvd_of_mem_primeFactors hpm)
      rw [hpr] at hp2 he
      exact redP_eq_one_of_two hpp he hp2 _ (hone _)
    · have hle : m.factorization p ≤ m := (Nat.factorization_lt p (NeZero.ne m)).le
      exact redP_eq_one_of_close hpp hle (h2 _ hv)



variable [IsGalois ℚ L]

/-- The isomorphism `Gal(ℚ(ζ_m)/ℚ) ≃ (ℤ/m)ˣ`. -/
def cycIso : Gal(L/ℚ) ≃* (ZMod m)ˣ :=
  IsCyclotomicExtension.autEquivPow L (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))

theorem cycIso_apply (σ : Gal(L/ℚ)) :
    cycIso m L σ = (IsCyclotomicExtension.zeta_spec m ℚ L).autToPow ℚ σ := rfl

/-- **The candidate Artin map of `ℚ(ζ_m)`**: `x ↦ (ζ ↦ ζ^{r(x)⁻¹})`. -/
def cycArtin : IdQ →* Gal(L/ℚ) :=
  ((cycIso m L).symm : (ZMod m)ˣ →* Gal(L/ℚ)).comp (resMod m).toHomUnits⁻¹

theorem cycIso_cycArtin (x : IdQ) : cycIso m L (cycArtin m L x) = ((resMod m).toHomUnits x)⁻¹ := by
  simp [cycArtin]

theorem cycArtin_diag (a : ℚˣ) : cycArtin m L (diag a) = 1 := by
  have h : (resMod m).toHomUnits (diag a) = 1 := Units.ext (by simp [resMod_diag])
  simp [cycArtin, h]

theorem isOpen_ker_cycArtin : IsOpen ((cycArtin m L).ker : Set IdQ) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [eventually_resMod_eq_one m] with x hx
  have h : (resMod m).toHomUnits x = 1 := Units.ext (by simp [hx])
  show cycArtin m L x = 1
  simp [cycArtin, h]

theorem cycArtin_local : ∃ n : ℕ, ∀ u : IdQ,
    (∀ v : Pl, v ∈ unramifiedPrimes ℚ L → Valued.v (ideleFinAt u v) = 1) →
    (∀ v : Pl, v ∉ unramifiedPrimes ℚ L → Valued.v (ideleFinAt u v - 1) ≤ WithZero.exp (-(n : ℤ))) →
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal), InfinitePlace.RamifiesIn L w → IsPosAt w hw (ideleInfAt u w)) →
    cycArtin m L u = 1 := by
  refine ⟨m, fun u h1 h2 h3 => ?_⟩
  have hr := resMod_eq_one_of_local m L u h1 h2 h3
  have h : (resMod m).toHomUnits u = 1 := Units.ext (by simp [hr])
  simp [cycArtin, h]



/-- If `σ ζ = ζ^n` then `σ` corresponds to `n` in `(ℤ/m)ˣ`. -/
theorem autToPow_eq_of_apply {σ : Gal(L/ℚ)} {n : ℕ}
    (h : σ (IsCyclotomicExtension.zeta m ℚ L) = IsCyclotomicExtension.zeta m ℚ L ^ n) :
    (((IsCyclotomicExtension.zeta_spec m ℚ L).autToPow ℚ σ : (ZMod m)ˣ) : ZMod m) = n := by
  have s1 := (IsCyclotomicExtension.zeta_spec m ℚ L).autToPow_spec ℚ σ
  rw [h] at s1
  have := MilneANT.natCast_eq_of_zeta_pow_eq (IsCyclotomicExtension.zeta_spec m ℚ L) s1
  rwa [ZMod.natCast_zmod_val] at this

/-- **Frobenius criterion**: if `σ ζ = ζ^n` and `r(x) n = 1` then `cycArtin x = σ`. -/
theorem cycArtin_eq_of_apply {x : IdQ} {σ : Gal(L/ℚ)} {n : ℕ}
    (h : σ (IsCyclotomicExtension.zeta m ℚ L) = IsCyclotomicExtension.zeta m ℚ L ^ n)
    (hr : resMod m x * (n : ZMod m) = 1) : cycArtin m L x = σ := by
  apply (cycIso m L).injective
  rw [cycIso_cycArtin, cycIso_apply]
  have hσ := autToPow_eq_of_apply m L h
  have : (resMod m).toHomUnits x * (IsCyclotomicExtension.zeta_spec m ℚ L).autToPow ℚ σ = 1 :=
    Units.ext (by simp [hσ, hr])
  exact inv_eq_of_mul_eq_one_right this

/-- Componentwise criterion for `r(x) n = 1`. -/
theorem resMod_mul_eq_one {x : IdQ} {n : ℕ}
    (h : ∀ p : m.primeFactors, redP p (Nat.prime_of_mem_primeFactors p.2) (m.factorization p)
      (compV (placeP m p) (unitPart x)).val * (n : ZMod ((p : ℕ) ^ m.factorization p)) = 1) :
    resMod m x * (n : ZMod m) = 1 := by
  have e : (n : ZMod m) = (ZMod.equivPi m (NeZero.ne m)).symm (fun p => (n : ZMod ((p : ℕ) ^ m.factorization p))) := by
    rw [← map_natCast (ZMod.equivPi m (NeZero.ne m)).symm n]
    rfl
  rw [e, resMod_apply, resModFun, ← map_mul, ← map_one (ZMod.equivPi m (NeZero.ne m)).symm]
  congr 1
  funext p
  exact h p

end Cyc

section Unif

/-- The reduction of the `unitPart` of a uniformizer idele at another place is the inverse of `p_v`. -/
theorem redP_unitPart_uniformizer {v : Pl} (π : (v.adicCompletion ℚ)ˣ)
    (hπ : Valued.v (π : v.adicCompletion ℚ) = WithZero.exp (-1)) {q : ℕ} (hq : q.Prime) (e : ℕ)
    (hw : placeOf q hq ≠ v) :
    redP q hq e (compV (placeOf q hq) (unitPart (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π))).val *
      ((pr v : ℕ) : ZMod (q ^ e)) = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, x = IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π := ⟨_, rfl⟩
  rw [← hx]
  have hq' : ratPart x = prU v := by rw [hx, ratPart_ofAdicCompletion v π 1 hπ, zpow_one]
  have hcomp : (compV (placeOf q hq) (unitPart x) : (placeOf q hq).adicCompletion ℚ) =
      ((((prU v)⁻¹ : ℚˣ) : ℚ) : _) := by
    rw [unitPart_apply, hq', ← map_inv diag (prU v), map_mul, Units.val_mul, hx,
      compV_ofAdicCompletion_ne hw, Units.val_one, one_mul, coe_compV_diag]
  rw [hcomp]
  have hA := (valued_prU_inv _ v hw).le
  have h1 := redP_mul (p := q) (hp := hq) (e := e) hA (valued_natCast_le_one _ (pr v))
  have h2 := redP_natCast (p := q) (hp := hq) (e := e) (pr v)
  have h3 : ((((prU v)⁻¹ : ℚˣ) : ℚ) : (placeOf q hq).adicCompletion ℚ) *
      ((pr v : ℕ) : (placeOf q hq).adicCompletion ℚ) = 1 := by
    have hq : (((prU v)⁻¹ : ℚˣ) : ℚ) * ((pr v : ℕ) : ℚ) = 1 := by
      rw [Units.val_inv_eq_inv_val]
      exact inv_mul_cancel₀ (show ((prU v : ℚˣ) : ℚ) ≠ 0 from (prU v).ne_zero)
    have := congrArg (cq (placeOf q (by assumption))) hq
    rw [map_mul, map_one, eq_ratCast, eq_ratCast, Rat.cast_natCast] at this
    exact this
  rw [h3, redP_one, h2] at h1
  exact h1.symm

end Unif


section Cyc2

variable (m : ℕ) [NeZero m] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L]
  [IsAbelianGalois ℚ L]

/-- For `p ∤ m` the Frobenius at `p` sends `ζ` to `ζ^p`. -/
theorem artinFrob_zeta_of_not_dvd {v : Pl} (hv : ¬ pr v ∣ m) :
    artinFrob L v (IsCyclotomicExtension.zeta m ℚ L) = IsCyclotomicExtension.zeta m ℚ L ^ pr v := by
  obtain ⟨Q⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 L)
  rw [artinFrob_eq L v (unramified_of_not_dvd m L hv) Q]
  exact (MilneANT.example_8_18 m L v hv Q).1

/-- For `m = 2k` with `k` odd, the Frobenius at `2` sends `ζ` to `ζ^(k+2)`. -/
theorem artinFrob_zeta_two {t : ℕ} (hk : m = 2 * (2 * t + 1)) {v : Pl} (hv2 : pr v = 2)
    (hu : v ∈ unramifiedPrimes ℚ L) :
    artinFrob L v (IsCyclotomicExtension.zeta m ℚ L) = IsCyclotomicExtension.zeta m ℚ L ^ (2 * t + 1 + 2) := by
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ L
  set ζ := IsCyclotomicExtension.zeta m ℚ L with hζdef
  have hm0 : 0 < m := NeZero.pos m
  have : NeZero (2 * t + 1) := ⟨by omega⟩
  have hk1 : ζ ^ (2 * t + 1) = -1 := by
    have := hζ.pow hm0 (show m = (2 * t + 1) * 2 by omega)
    exact this.eq_neg_one_of_two_right
  have hη : IsPrimitiveRoot (ζ ^ 2) (2 * t + 1) := hζ.pow hm0 hk
  have hζeq : ζ = -(ζ ^ 2) ^ (t + 1) := by
    have : (ζ ^ 2) ^ (t + 1) = ζ ^ (2 * t + 1) * ζ := by rw [← pow_mul, ← pow_succ]; congr 1
    rw [this, hk1]; ring
  have hcyc : IsCyclotomicExtension {2 * t + 1} ℚ L := by
    rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨ζ ^ 2, hη⟩, fun x => ?_⟩
    have hx : x ∈ Algebra.adjoin ℚ {b : L | b ^ m = 1} :=
      ((IsCyclotomicExtension.iff_singleton (n := m) (A := ℚ) (B := L)).mp inferInstance).2 x
    have hmem : ζ ∈ Algebra.adjoin ℚ {b : L | b ^ (2 * t + 1) = 1} := by
      have h1 : ζ ^ 2 ∈ Algebra.adjoin ℚ {b : L | b ^ (2 * t + 1) = 1} :=
        Algebra.subset_adjoin hη.pow_eq_one
      have h2 := Subalgebra.neg_mem _ (Subalgebra.pow_mem _ h1 (t + 1))
      rwa [← hζeq] at h2
    refine Algebra.adjoin_le ?_ hx
    intro b hb
    obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hb
    exact Subalgebra.pow_mem _ hmem _
  have hη' := IsCyclotomicExtension.zeta_spec (2 * t + 1) ℚ L
  obtain ⟨Q⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 L)
  have hcop : (Ideal.absNorm v.asIdeal).Coprime (2 * t + 1) := by
    rw [RatIdele.absNorm_asIdeal, hv2]
    exact Nat.coprime_two_left.mpr (by simp)
  have hσ := MilneANT.arithFrob_zeta (2 * t + 1) hcop Q (isArithFrobAt_frobAt ℚ L v Q)
  rw [RatIdele.absNorm_asIdeal, hv2] at hσ
  rw [artinFrob_eq L v hu Q]
  set σ := frobAt ℚ L v Q
  obtain ⟨j, -, hj⟩ := hη'.eq_pow_of_pow_eq_one hη.pow_eq_one
  have hσ2 : σ (ζ ^ 2) = (ζ ^ 2) ^ 2 := by
    rw [← hj, map_pow, hσ]; ring
  have h1 : σ ζ = -((ζ ^ 2) ^ 2) ^ (t + 1) := by
    conv_lhs => rw [hζeq]
    rw [map_neg, map_pow, hσ2]
  rw [h1]
  have h2 : ζ ^ (2 * (2 * t + 1)) = 1 := by rw [← hk]; exact hζ.pow_eq_one
  have h3 : ((ζ ^ 2) ^ 2) ^ (t + 1) = ζ ^ 2 := by
    have : ((ζ ^ 2) ^ 2) ^ (t + 1) = ζ ^ (2 * (2 * t + 1)) * ζ ^ 2 := by ring
    rw [this, h2, one_mul]
  have h4 : ζ ^ (2 * t + 1 + 2) = -(ζ ^ 2) := by
    rw [pow_add, hk1]; ring
  rw [h3, h4]



/-- The `p = 2` component of `r (uniformizer) * (2k)`-type product. -/
theorem two_component {e : ℕ} (he : e = 1) (t : ℕ) (z : Kp 2 Nat.prime_two) (hz : Valued.v z = 1) :
    redP 2 Nat.prime_two e z * ((2 * t + 1 + 2 : ℕ) : ZMod (2 ^ e)) = 1 := by
  subst he
  rw [redP_unit_two hz]
  have h2 : (2 : ZMod (2 ^ 1)) = 0 := by decide
  push_cast
  rw [h2]; simp

/-- **`r` of a uniformizer at `2` in `ℚ(ζ_{2k})`, `k` odd**: `r(x) (k + 2) = 1`. -/
theorem resMod_uniformizer_two {t : ℕ} (hk : m = 2 * (2 * t + 1)) (he : m.factorization 2 = 1) {v : Pl}
    (hv2 : pr v = 2) (π : (v.adicCompletion ℚ)ˣ) (hπ : Valued.v (π : v.adicCompletion ℚ) = WithZero.exp (-1)) :
    resMod m (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π) * ((2 * t + 1 + 2 : ℕ) : ZMod m) = 1 := by
  refine resMod_mul_eq_one m fun ⟨p, hpm⟩ => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
  by_cases hp2 : p = 2
  · subst hp2
    exact two_component he t _ (valued_unitPart _ _)
  · have hw : placeOf p hpp ≠ v := by
      intro h
      have := pr_placeOf p hpp
      rw [h, hv2] at this
      exact hp2 this.symm
    have h1 := redP_unitPart_uniformizer π hπ hpp (m.factorization p) hw
    rw [hv2] at h1
    have hdvd : p ^ m.factorization p ∣ 2 * t + 1 := by
      have h3 : p ^ m.factorization p ∣ 2 * (2 * t + 1) := hk ▸ Nat.ordProj_dvd m p
      have h4 : (p ^ m.factorization p).Coprime 2 :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hpp Nat.prime_two).mpr hp2)
      exact h4.dvd_of_dvd_mul_left h3
    have h5 : ((2 * t + 1 + 2 : ℕ) : ZMod (p ^ m.factorization p)) = ((2 : ℕ) : ZMod (p ^ m.factorization p)) := by
      rw [Nat.cast_add, (ZMod.natCast_eq_zero_iff _ _).mpr hdvd, zero_add]
    show _ * ((2 * t + 1 + 2 : ℕ) : ZMod (p ^ m.factorization p)) = 1
    rw [h5]
    exact h1

/-- **The Frobenius property (b) of Summary 5.10 for `cycArtin`.** -/
theorem cycArtin_frobenius (v : Pl) (hv : v ∈ unramifiedPrimes ℚ L) (π : (v.adicCompletion ℚ)ˣ)
    (hπ : Valued.v (π : v.adicCompletion ℚ) = WithZero.exp (-1)) :
    cycArtin m L (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π) = artinFrob L v := by
  by_cases hd : pr v ∣ m
  · obtain ⟨hp2, he⟩ := eq_two_of_unramified m L hv hd
    obtain ⟨k, hk⟩ := hd
    rw [hp2] at hk he
    have hodd : Odd k := by
      by_contra hne
      rw [Nat.not_odd_iff_even] at hne
      obtain ⟨j, hj⟩ := hne
      have h4 : 2 ^ 2 ∣ m := ⟨j, by rw [hk, hj]; ring⟩
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (NeZero.ne m)).mp h4
      omega
    obtain ⟨t, rfl⟩ := hodd
    exact cycArtin_eq_of_apply m L (artinFrob_zeta_two m L hk hp2 hv)
      (resMod_uniformizer_two m hk he hp2 π hπ)
  · have hcop : (pr v).Coprime m := (Nat.Prime.coprime_iff_not_dvd (pr_prime v)).mpr hd
    exact cycArtin_eq_of_apply m L (artinFrob_zeta_of_not_dvd m L hd)
      (resMod_mul_eq_one m fun p => redP_unitPart_uniformizer π hπ _ _ (placeOf_ne m hcop p))



/-- `cycArtin` has the properties (a), (b) of Summary 5.10. -/
theorem isIdelicArtinMap_cycArtin : IsIdelicArtinMap L (cycArtin m L) :=
  ⟨isOpen_ker_cycArtin m L, cycArtin_local m L, cycArtin_frobenius m L⟩

end Cyc2

end ArtinCyclotomic

/-- **The Artin map of $\mathbb Q(\zeta_m)$** (Milne, *CFT*, V, p. 181 ("the global reciprocity map is the reciprocal of
$I_\mathbb Q \to \hat{\mathbb Z}^\times \to \mathrm{Gal}(\mathbb Q^{\mathrm{cyc}}/\mathbb Q)$"), and Example 4.10): every
homomorphism $\varphi : I_\mathbb Q \to \mathrm{Gal}(\mathbb Q(\zeta_m)/\mathbb Q)$ with the properties of Summary 5.10 and
trivial on $\mathbb Q^\times$ acts by $\varphi(x)(\zeta_m) = \zeta_m^{r(x)^{-1}}$, $r(x) \in (\mathbb Z/m)^\times$ the residue
of the $\hat{\mathbb Z}^\times$-component of $x$ (`Chebotarev.RatIdele.resMod`). -/
@[kb "milne2020cft" "Ch. V, §5, p. 181 (the Artin map of Q(ζ_m)); Example 4.10"]
theorem artin_cyclotomic (m : ℕ) [NeZero m] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L]
    [IsAbelianGalois ℚ L] (φ : IdeleGroup (𝓞 ℚ) ℚ →* Gal(L/ℚ)) (hφ : IsIdelicArtinMap L φ)
    (hK : ∀ a : ℚˣ, φ (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ a) = 1) (x : IdeleGroup (𝓞 ℚ) ℚ) :
    ((IsCyclotomicExtension.zeta_spec m ℚ L).autToPow ℚ (φ x) : ZMod m) * Chebotarev.RatIdele.resMod m x = 1 := by
  have h := idelicArtin_unique L φ (cycArtin m L) hφ (isIdelicArtinMap_cycArtin m L) hK (cycArtin_diag m L)
  rw [h, ← cycIso_apply, cycIso_cycArtin]
  simp

end NumberFieldKB.MilneCFT
