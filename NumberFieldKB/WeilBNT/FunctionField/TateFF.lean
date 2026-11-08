import NumberFieldKB.WeilBNT.FunctionField.IdeleZeta
import NumberFieldKB.WeilBNT.FunctionField.IdeleQuotient
import NumberFieldKB.WeilBNT.FunctionField.FourierFF
import NumberFieldKB.WeilBNT.FunctionField.HeckeFE

/-!
# Tate's thesis for a function field: theta series on the cosets $\pi^DU$ (Weil VII.§5, characteristic $p$)

$k$ is a global function field with field of constants $\mathbb F_q$, $U=\prod_v\mathfrak r_v^\times$
(`integralUnits`), $\pi^D$ the idele with components $\pi_v^{D(v)}$ (`piD`), $\mu$ a Haar measure on
$k_{\mathbb A}^\times$, $\omega$ a quasicharacter of $G_k=k_{\mathbb A}^\times/k^\times$ (`FFHeckeCharacter`) and
$\Phi$ a Schwartz–Bruhat function on $k_{\mathbb A}$.

This file contains the local ingredients of Tate's proof of VII.§5 Thm. 2 in characteristic $p$:
* `FFHeckeCharacter.ev`: $\omega$ as a function on ideles; it is invariant under $k^\times$, has absolute value $1$ on
  $U$, and $\int_U\omega\,d\mu=\mu(U)$ or $0$ according as $\omega$ is trivial on $U$ or not.
* `cosInd_mul`, `fourierFF_mulRight`: for an idele $z$ the function $x\mapsto\Phi(xz)$ is Schwartz–Bruhat with
  Fourier transform $y\mapsto\lvert z\rvert^{-1}\hat\Phi(yz^{-1})$.
* **`poisson_idele`**: $\sum_{\xi\in k}\Phi(\xi z)=q^{1-g}\lvert z\rvert^{-1}\sum_{\eta\in k}\hat\Phi(\eta z^{-1})$.
-/

open MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal

namespace NumberFieldKB.WeilBNT.FF

noncomputable section

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

set_option linter.unusedSectionVars false

open FFIdeleGroup FFAdeleRing

/-! ### Schwartz–Bruhat functions are continuous -/

namespace FFAdeleRing

theorem IsSchwartzBruhat.continuous {Φ : FFAdeleRing Fq k → ℂ} (hΦ : IsSchwartzBruhat Φ) : Continuous Φ := by
  obtain ⟨-, b, -, hinv⟩ := hΦ
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine (continuousAt_const : ContinuousAt (fun _ => Φ x) x).congr ?_
  have hU : (U b : Set (FFAdeleRing Fq k)) ∈ 𝓝 0 := (isOpen_U b).mem_nhds (U b).zero_mem
  have : (fun y => y - x) ⁻¹' (U b : Set (FFAdeleRing Fq k)) ∈ 𝓝 x := by
    apply (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
    simpa using hU
  filter_upwards [this] with y hy
  have := hinv x (y - x) hy
  rw [add_sub_cancel] at this
  exact this.symm

/-- Membership in `U a` after multiplication by an idele: $xz\in U(\mathfrak a)\iff x\in U(\mathfrak a+\operatorname{div}z)$. -/
theorem mul_mem_U_iff (a : Divisor Fq k) (z : FFIdeleGroup Fq k) (x : FFAdeleRing Fq k) :
    x * (z : FFAdeleRing Fq k) ∈ U a ↔ x ∈ U (a + div z) := by
  simp only [mem_U_iff]
  refine forall_congr' fun v => ?_
  have hz0 : comp z v ≠ 0 := comp_ne_zero z v
  have hv : Valued.v (comp z v) = WithZero.exp (-(div z v)) := by
    rw [div_apply]
    exact Place.valued_eq_exp_neg_ordC v hz0
  show Valued.v (x v * comp z v) ≤ _ ↔ _
  rw [map_mul, hv, Finsupp.add_apply]
  constructor
  · intro h
    have h2 := mul_le_mul' h (le_refl (WithZero.exp (div z v)))
    rwa [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one, ← WithZero.exp_add] at h2
  · intro h
    have h2 := mul_le_mul' h (le_refl (WithZero.exp (-(div z v))))
    rwa [← WithZero.exp_add, add_neg_cancel_right] at h2

/-- Coset indicators under multiplication by an idele. -/
theorem cosInd_mul (b : Divisor Fq k) (r : FFAdeleRing Fq k) (z : FFIdeleGroup Fq k) (x : FFAdeleRing Fq k) :
    cosInd b r (x * (z : FFAdeleRing Fq k)) = cosInd (b + div z) (r * ((z⁻¹ : FFIdeleGroup Fq k) : FFAdeleRing Fq k)) x := by
  classical
  have h : x * (z : FFAdeleRing Fq k) - r = (x - r * ((z⁻¹ : FFIdeleGroup Fq k) : FFAdeleRing Fq k)) *
      (z : FFAdeleRing Fq k) := by
    rw [sub_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  rw [cosInd_apply, cosInd_apply, h, mul_mem_U_iff]


variable (ψ₀ : AddChar Fq Circle)

/-- For an idele $z$, $x\mapsto\Phi(xz)$ is Schwartz–Bruhat. -/
theorem IsSchwartzBruhat.mulRight {Φ : FFAdeleRing Fq k → ℂ} (hΦ : IsSchwartzBruhat Φ) (z : FFIdeleGroup Fq k) :
    IsSchwartzBruhat fun x => Φ (x * (z : FFAdeleRing Fq k)) := by
  obtain ⟨a, b, hs, hinv⟩ := hΦ
  refine ⟨a + div z, b + div z, fun x hx => hs _ fun h => hx ((mul_mem_U_iff a z x).1 h), fun x u hu => ?_⟩
  have hu' : u * (z : FFAdeleRing Fq k) ∈ U b := (mul_mem_U_iff b z u).2 hu
  show Φ ((x + u) * (z : FFAdeleRing Fq k)) = Φ (x * (z : FFAdeleRing Fq k))
  rw [add_mul]
  exact hinv _ _ hu'

open Classical in
/-- **Fourier transform of $x\mapsto\Phi(xz)$**: $y\mapsto\lvert z\rvert^{-1}\hat\Phi(yz^{-1})$, with
$\lvert z\rvert^{-1}=q^{\deg\operatorname{div}z}$. -/
theorem fourierFF_mulRight (hψ₀ : ψ₀ ≠ 1) {Φ : FFAdeleRing Fq k → ℂ} (hΦ : IsSchwartzBruhat Φ)
    (z : FFIdeleGroup Fq k) (y : FFAdeleRing Fq k) :
    fourierFF ψ₀ (fun x => Φ (x * (z : FFAdeleRing Fq k))) y =
      (Nat.card Fq : ℂ) ^ Divisor.deg (div z) *
        fourierFF ψ₀ Φ (y * ((z⁻¹ : FFIdeleGroup Fq k) : FFAdeleRing Fq k)) := by
  obtain ⟨a, b, n, ρ, -, -, hdec⟩ := exists_decomp hΦ
  have hdec' : ∀ x, Φ (x * (z : FFAdeleRing Fq k)) = ∑ i, Φ (ρ i) *
      cosInd (b + div z) (ρ i * ((z⁻¹ : FFIdeleGroup Fq k) : FFAdeleRing Fq k)) x := fun x => by
    rw [hdec]; simp_rw [cosInd_mul]
  rw [fourierFF_of_decomp ψ₀ hψ₀ hdec' y, fourierFF_of_decomp ψ₀ hψ₀ hdec, Finset.mul_sum]
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := Fq); exact_mod_cast this.ne'
  refine Finset.sum_congr rfl fun i _ => ?_
  have hiff : y ∈ U (canonical Fq k - (b + div z)) ↔
      y * ((z⁻¹ : FFIdeleGroup Fq k) : FFAdeleRing Fq k) ∈ U (canonical Fq k - b) := by
    rw [mul_mem_U_iff, div_inv']
    rw [show canonical Fq k - b + -div z = canonical Fq k - (b + div z) by abel]
  by_cases hy : y ∈ U (canonical Fq k - (b + div z))
  · rw [if_pos hy, if_pos (hiff.1 hy), map_add, zpow_add₀ hq0]
    have : ρ i * ((z⁻¹ : FFIdeleGroup Fq k) : FFAdeleRing Fq k) * y =
        ρ i * (y * ((z⁻¹ : FFIdeleGroup Fq k) : FFAdeleRing Fq k)) := by ring
    rw [this]; ring
  · rw [if_neg hy, if_neg (fun h => hy (hiff.2 h))]; ring

/-- **Poisson summation at an idele** (Weil VII.§2 applied to $x\mapsto\Phi(xz)$):
$\sum_{\xi\in k}\Phi(\xi z)=q^{1-g}\lvert z\rvert^{-1}\sum_{\eta\in k}\hat\Phi(\eta z^{-1})$. -/
theorem poisson_idele (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) {Φ : FFAdeleRing Fq k → ℂ}
    (hΦ : IsSchwartzBruhat Φ) (z : FFIdeleGroup Fq k) :
    ∑ᶠ ξ : k, Φ (diag ξ * (z : FFAdeleRing Fq k)) =
      (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * ((Nat.card Fq : ℂ) ^ Divisor.deg (div z) *
        ∑ᶠ η : k, fourierFF ψ₀ Φ (diag η * ((z⁻¹ : FFIdeleGroup Fq k) : FFAdeleRing Fq k))) := by
  rw [weil_VII_2_poisson_ff ψ₀ hc hψ₀ (hΦ.mulRight z)]
  congr 1
  simp_rw [fourierFF_mulRight ψ₀ hψ₀ hΦ z]
  exact finsum_const_mul' _ _

end FFAdeleRing

/-! ### The units `U` as a subgroup; integrals over `U` -/

namespace FFIdeleGroup

theorem mul_mem_integralUnits {u w : FFIdeleGroup Fq k} (hu : u ∈ integralUnits) (hw : w ∈ integralUnits) :
    u * w ∈ integralUnits := by
  rw [mem_integralUnits_iff_div] at *
  rw [div_mul, hu, hw, add_zero]

theorem inv_mem_integralUnits {u : FFIdeleGroup Fq k} (hu : u ∈ integralUnits) : u⁻¹ ∈ integralUnits := by
  rw [mem_integralUnits_iff_div] at *
  rw [div_inv', hu, neg_zero]

variable (Fq k) in
/-- $U=\prod_v\mathfrak r_v^\times$ as a subgroup of $k_{\mathbb A}^\times$. -/
def unitsSubgroup : Subgroup (FFIdeleGroup Fq k) where
  carrier := integralUnits
  one_mem' := one_mem_integralUnits
  mul_mem' := mul_mem_integralUnits
  inv_mem' := inv_mem_integralUnits

theorem mem_unitsSubgroup {u : FFIdeleGroup Fq k} : u ∈ unitsSubgroup Fq k ↔ u ∈ integralUnits := Iff.rfl

theorem mul_mem_integralUnits_iff {u₀ : FFIdeleGroup Fq k} (hu₀ : u₀ ∈ integralUnits) (u : FFIdeleGroup Fq k) :
    u₀ * u ∈ integralUnits ↔ u ∈ integralUnits := by
  constructor
  · intro h
    have := mul_mem_integralUnits (inv_mem_integralUnits hu₀) h
    rwa [inv_mul_cancel_left] at this
  · exact mul_mem_integralUnits hu₀

/-- Left translation by an element of `U` preserves integrals over `U`. -/
theorem setIntegral_integralUnits_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (FFIdeleGroup Fq k)) [μ.IsMulLeftInvariant] {u₀ : FFIdeleGroup Fq k} (hu₀ : u₀ ∈ integralUnits)
    (f : FFIdeleGroup Fq k → E) :
    ∫ u in integralUnits, f (u₀ * u) ∂μ = ∫ u in integralUnits, f u ∂μ := by
  have hpre : (fun u => u₀ * u) ⁻¹' integralUnits = (integralUnits : Set (FFIdeleGroup Fq k)) := by
    ext u; exact mul_mem_integralUnits_iff hu₀ u
  have := (measurePreserving_mul_left μ u₀).setIntegral_preimage_emb
    (MeasurableEquiv.mulLeft u₀).measurableEmbedding f integralUnits
  rw [hpre] at this
  exact this

theorem inv_preimage_integralUnits : (Inv.inv : FFIdeleGroup Fq k → FFIdeleGroup Fq k) ⁻¹' integralUnits =
    integralUnits := by
  ext u
  refine ⟨fun h => ?_, inv_mem_integralUnits⟩
  have := inv_mem_integralUnits h
  rwa [inv_inv] at this

/-- **Inversion preserves the Haar measure on `U`** (uniqueness of Haar measure on sets with compact closure,
applied to $\mu$ and its image under $u\mapsto u^{-1}$, which agree on $U=U^{-1}$). -/
theorem restrict_integralUnits_map_inv (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure] :
    (μ.restrict integralUnits).map Inv.inv = μ.restrict integralUnits := by
  ext s hs
  rw [Measure.map_apply measurable_inv hs, Measure.restrict_apply (measurable_inv hs),
    Measure.restrict_apply hs]
  have : μ.IsMulRightInvariant := ⟨fun g => by
    have : (fun x => x * g) = (fun x => g * x) := funext fun x => mul_comm x g
    rw [this]; exact map_mul_left_eq_self μ g⟩
  have : μ.inv.IsMulLeftInvariant := Measure.inv.instIsMulLeftInvariant
  set c := Measure.haarScalarFactor μ.inv μ
  have key : ∀ t ⊆ (integralUnits : Set (FFIdeleGroup Fq k)), μ.inv t = c • μ t := fun t ht =>
    Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure μ.inv μ
      (isCompact_integralUnits.closure_of_subset ht)
  have hinv : ∀ t : Set (FFIdeleGroup Fq k), μ.inv t = μ (Inv.inv ⁻¹' t) := fun t => by
    rw [Measure.inv_apply]; rfl
  have hc : c = 1 := by
    have h1 := key _ subset_rfl
    rw [hinv, inv_preimage_integralUnits] at h1
    have h0 := measure_integralUnits_pos μ
    have ht := measure_integralUnits_lt_top μ
    have : (1 : ℝ≥0∞) * μ integralUnits = (c : ℝ≥0∞) * μ integralUnits := by rw [one_mul]; exact h1
    exact ENNReal.coe_eq_one.1 ((ENNReal.mul_left_inj h0.ne' ht.ne).1 this).symm
  have h2 := key (s ∩ integralUnits) Set.inter_subset_right
  rw [hc, one_smul, hinv] at h2
  rw [← h2]
  congr 1
  ext u
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  rw [show u⁻¹ ∈ integralUnits ↔ u ∈ integralUnits from by
    rw [← Set.mem_preimage, inv_preimage_integralUnits]]

/-- Inversion preserves integrals over `U`. -/
theorem setIntegral_integralUnits_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure] (f : FFIdeleGroup Fq k → E) :
    ∫ u in integralUnits, f u⁻¹ ∂μ = ∫ u in integralUnits, f u ∂μ := by
  conv_rhs => rw [← restrict_integralUnits_map_inv μ]
  exact ((MeasurableEquiv.inv (FFIdeleGroup Fq k)).measurableEmbedding.integral_map f).symm

end FFIdeleGroup

/-! ### Quasicharacters as functions on ideles -/

namespace FFHeckeCharacter

/-- A quasicharacter $\omega$ of $G_k$ as a function on $k_{\mathbb A}^\times$. -/
def ev (ω : FFHeckeCharacter Fq k) (z : FFIdeleGroup Fq k) : ℂ := ((ω (QuotientGroup.mk z) : ℂˣ) : ℂ)

variable (ω : FFHeckeCharacter Fq k)

theorem ev_mul (z w : FFIdeleGroup Fq k) : ω.ev (z * w) = ω.ev z * ω.ev w := by
  simp [ev, QuotientGroup.mk_mul]

theorem ev_one : ω.ev 1 = 1 := by simp [ev]

theorem ev_ne_zero (z : FFIdeleGroup Fq k) : ω.ev z ≠ 0 := Units.ne_zero _

theorem ev_inv (z : FFIdeleGroup Fq k) : ω.ev z⁻¹ = (ω.ev z)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← ev_mul, inv_mul_cancel, ev_one]

theorem ev_zpow (z : FFIdeleGroup Fq k) (n : ℤ) : ω.ev (z ^ n) = ω.ev z ^ n := by
  simp [ev, QuotientGroup.mk_zpow]

theorem ev_principal_mul (ξ : kˣ) (z : FFIdeleGroup Fq k) : ω.ev (principal ξ * z) = ω.ev z := by
  have : (QuotientGroup.mk (principal ξ * z) : FFIdeleClassGroup Fq k) = QuotientGroup.mk z := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (MonoidHom.mem_range.2 ⟨ξ, rfl⟩), one_mul]
  simp only [ev, this]

theorem ev_principal (ξ : kˣ) : ω.ev (principal ξ) = 1 := by
  simpa [ev_one] using ω.ev_principal_mul ξ 1

theorem continuous_ev : Continuous ω.ev :=
  Units.continuous_val.comp (ω.continuous_toFun.comp continuous_quot_mk)

/-- $\lvert\omega\rvert=1$ on $U$ (the image of the compact group $U$ in $\mathbb R_{>0}$ is bounded). -/
theorem norm_ev_of_mem {u : FFIdeleGroup Fq k} (hu : u ∈ integralUnits) : ‖ω.ev u‖ = 1 := by
  obtain ⟨B, hB⟩ := isCompact_integralUnits.exists_bound_of_continuousOn (ω.continuous_ev.continuousOn)
  have hpow : ∀ n : ℤ, ‖ω.ev u‖ ^ n ≤ B := fun n => by
    rw [← norm_zpow, ← ev_zpow]
    exact hB _ ((unitsSubgroup Fq k).zpow_mem (mem_unitsSubgroup.2 hu) n)
  have hpos : 0 < ‖ω.ev u‖ := norm_pos_iff.2 (ω.ev_ne_zero u)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hgt' : 1 < ‖ω.ev u‖⁻¹ := one_lt_inv_iff₀.2 ⟨hpos, hlt⟩
    obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt').eventually_gt_atTop B |>.exists
    have := hpow (-(n : ℤ))
    rw [zpow_neg, zpow_natCast, ← inv_pow] at this
    linarith
  · obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop B |>.exists
    have := hpow n
    rw [zpow_natCast] at this
    linarith

/-- **Orthogonality on `U`**: $\int_U\omega\,d\mu$ is $\mu(U)$ if $\omega$ is trivial on $U$ and $0$ otherwise. -/
theorem setIntegral_ev (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure] [Decidable (∀ u ∈ integralUnits, ω.ev u = 1)] :
    ∫ u in integralUnits, ω.ev u ∂μ =
      if ∀ u ∈ integralUnits, ω.ev u = 1 then ((μ integralUnits).toReal : ℂ) else 0 := by
  split_ifs with h
  · rw [setIntegral_congr_fun isOpen_integralUnits.measurableSet (fun u hu => h u hu), setIntegral_const,
      Complex.real_smul, mul_one]
    rfl
  · push Not at h
    obtain ⟨u₀, hu₀, hne⟩ := h
    have := setIntegral_integralUnits_mul_left μ hu₀ ω.ev
    simp_rw [ev_mul] at this
    rw [integral_const_mul] at this
    have h2 : (ω.ev u₀ - 1) * ∫ u in integralUnits, ω.ev u ∂μ = 0 := by
      rw [sub_mul, this, one_mul, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)

end FFHeckeCharacter

/-! ### The ideles `π^D` -/

namespace FFIdeleGroup

theorem ext_comp {z w : FFIdeleGroup Fq k} (h : ∀ v, comp z v = comp w v) : z = w :=
  Units.ext <| by ext v; exact h v

theorem piD_add (D E : Divisor Fq k) : piD (D + E) = piD D * piD E := by
  refine ext_comp fun v => ?_
  rw [comp_mul, comp_piD, comp_piD, comp_piD, Finsupp.add_apply, zpow_add, Units.val_mul]

theorem piD_zero : piD (0 : Divisor Fq k) = 1 := by
  refine ext_comp fun v => ?_
  rw [comp_piD, comp_one, Finsupp.zero_apply, zpow_zero, Units.val_one]

theorem piD_neg (D : Divisor Fq k) : piD (-D) = (piD D)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← piD_add, neg_add_cancel, piD_zero]

theorem piD_sub (D E : Divisor Fq k) : piD (D - E) = piD D * (piD E)⁻¹ := by
  rw [sub_eq_add_neg, piD_add, piD_neg]

theorem piD_nsmul (n : ℕ) (D : Divisor Fq k) : piD (n • D) = piD D ^ n := by
  induction n with
  | zero => rw [zero_smul, piD_zero, pow_zero]
  | succ m ih => rw [succ_nsmul, piD_add, ih, pow_succ]

/-- $\xi\,(\pi^{\operatorname{div}\xi})^{-1}\in U$. -/
theorem principal_mul_piD_inv_mem (ξ : kˣ) : (piD (Divisor.div ξ))⁻¹ * principal (Fq := Fq) ξ ∈ integralUnits :=
  (mem_fiber_iff (Divisor.div ξ) (principal ξ)).1 (div_principal ξ)

theorem piD_mul_mem_U_iff (a D : Divisor Fq k) {u : FFIdeleGroup Fq k} (hu : u ∈ integralUnits) :
    ((piD D * u : FFIdeleGroup Fq k) : FFAdeleRing Fq k) ∈ U a ↔ -a ≤ D := by
  rw [mem_U_iff]
  refine forall_congr' fun v => ?_
  show Valued.v (comp (piD D * u) v) ≤ _ ↔ _
  rw [valued_comp_piD_mul D hu, WithZero.exp_le_exp, Finsupp.neg_apply]
  omega

theorem fiber_eq_image (D : Divisor Fq k) :
    {z : FFIdeleGroup Fq k | div z = D} = (fun u => piD D * u) '' integralUnits := by
  ext z
  rw [Set.mem_setOf_eq, mem_fiber_iff]
  exact ⟨fun h => ⟨_, h, mul_inv_cancel_left _ _⟩, by rintro ⟨u, hu, rfl⟩; rwa [inv_mul_cancel_left]⟩

theorem isCompact_fiber (D : Divisor Fq k) : IsCompact {z : FFIdeleGroup Fq k | div z = D} := by
  rw [fiber_eq_image]
  exact isCompact_integralUnits.image (continuous_const.mul continuous_id)

end FFIdeleGroup

namespace FFAdeleRing

/-- A Schwartz–Bruhat function is bounded. -/
theorem IsSchwartzBruhat.exists_bound {Φ : FFAdeleRing Fq k → ℂ} (hΦ : IsSchwartzBruhat Φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖Φ x‖ ≤ B := by
  classical
  obtain ⟨a, b, n, ρ, -, -, hdec⟩ := exists_decomp hΦ
  refine ⟨∑ i, ‖Φ (ρ i)‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun x => ?_⟩
  rw [hdec]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [_root_.norm_mul, cosInd_apply]
  split_ifs <;> simp

end FFAdeleRing

/-! ### The zeta integral of a quasicharacter, coset by coset -/

namespace FFIdeleGroup

/-- **Weil's zeta integral** $Z(\omega\omega_s,\Phi)=\int\Phi(z)\omega(z)\lvert z\rvert^s\,d\mu(z)$ (VII.§4 (4)) for the
quasicharacter $\omega\omega_s$. For $\omega=1$ this is `zetaIntegral`. -/
def zetaQ (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k) (Φ : FFAdeleRing Fq k → ℂ) (s : ℂ) : ℂ :=
  ∫ z, Φ (z : FFAdeleRing Fq k) * ω.ev z * omegaS s z ∂μ

/-- The integral over the coset $\pi^DU$: $g(D)=\int_U\Phi(\pi^Du)\,\omega(\pi^Du)\,d\mu(u)$. -/
def gInt (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k) (Φ : FFAdeleRing Fq k → ℂ)
    (D : Divisor Fq k) : ℂ :=
  ∫ u in integralUnits, Φ ((piD D * u : FFIdeleGroup Fq k) : FFAdeleRing Fq k) * ω.ev (piD D * u) ∂μ

theorem gInt_eq_zero {μ : Measure (FFIdeleGroup Fq k)} {ω : FFHeckeCharacter Fq k} {Φ : FFAdeleRing Fq k → ℂ}
    {a : Divisor Fq k} (hs : ∀ x, x ∉ U a → Φ x = 0) {D : Divisor Fq k} (hD : ¬ -a ≤ D) :
    gInt μ ω Φ D = 0 := by
  rw [gInt]
  refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
  rw [hs _ (fun h => hD ((piD_mul_mem_U_iff a D hu).1 h)), zero_mul]

theorem continuous_integrand {ω : FFHeckeCharacter Fq k} {Φ : FFAdeleRing Fq k → ℂ}
    (hΦ : FFAdeleRing.IsSchwartzBruhat Φ) (s : ℂ) :
    Continuous fun z : FFIdeleGroup Fq k => Φ (z : FFAdeleRing Fq k) * ω.ev z * omegaS s z :=
  ((hΦ.continuous.comp Units.continuous_val).mul ω.continuous_ev).mul (continuous_omegaS s)

/-- **The zeta integral as a series over divisors**: if $\lvert\omega(z)\omega_s(z)\rvert=\lvert z\rvert^\sigma$ with
$\sigma>1$, the integral converges absolutely and $Z(\omega\omega_s,\Phi)=\sum_Dg(D)\,u^{\deg D}$, $u=q^{-s}$. -/
theorem hasSum_zetaQ (hc : IsConstantField Fq k) (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure]
    (ω : FFHeckeCharacter Fq k) {Φ : FFAdeleRing Fq k → ℂ} (hΦ : FFAdeleRing.IsSchwartzBruhat Φ) {s : ℂ}
    {σ : ℝ} (hσ : ∀ z, ‖ω.ev z‖ * ‖omegaS s z‖ = (norm z : ℝ) ^ σ) (h1 : 1 < σ) :
    Integrable (fun z : FFIdeleGroup Fq k => Φ (z : FFAdeleRing Fq k) * ω.ev z * omegaS s z) μ ∧
      HasSum (fun D => gInt μ ω Φ D * uS Fq s ^ Divisor.deg D) (zetaQ μ ω Φ s) := by
  obtain ⟨B, hB0, hB⟩ := hΦ.exists_bound
  obtain ⟨a, -, hs, -⟩ := id hΦ
  set f := fun z : FFIdeleGroup Fq k => Φ (z : FFAdeleRing Fq k) * ω.ev z * omegaS s z with hf
  have hq1 : (1 : ℝ) < Nat.card Fq := by exact_mod_cast (Finite.one_lt_card (α := Fq))
  have hq0 : (0 : ℝ) < Nat.card Fq := by linarith
  set r : ℝ := (Nat.card Fq : ℝ) ^ (-σ) with hr
  have hr0 : 0 ≤ r := (Real.rpow_pos_of_pos hq0 _).le
  have hnormz : ∀ z : FFIdeleGroup Fq k, ((norm z : ℝ)) ^ σ = r ^ Divisor.deg (div z) := fun z => by
    rw [norm_eq, NNReal.coe_zpow, NNReal.coe_natCast, ← Real.rpow_intCast, ← Real.rpow_mul hq0.le,
      ← Real.rpow_intCast, hr, ← Real.rpow_mul hq0.le]
    congr 1; push_cast; ring
  have hpiece : ∀ D : Divisor Fq k, ∫ z in {z | div z = D}, f z ∂μ = gInt μ ω Φ D * uS Fq s ^ Divisor.deg D := by
    intro D
    rw [setIntegral_fiber μ D f, gInt, ← integral_mul_const]
    refine setIntegral_congr_fun isOpen_integralUnits.measurableSet fun u hu => ?_
    simp only [hf]
    rw [omegaS_eq, div_piD_mul D hu]
  have hpiecen : ∀ D : Divisor Fq k, ∫ z in {z | div z = D}, ‖f z‖ ∂μ ≤
      (B * (μ integralUnits).toReal) * ‖(cone ∅ (-a)).indicator (fun D => ((r : ℂ)) ^ Divisor.deg D) D‖ := by
    intro D
    rw [setIntegral_fiber μ D (fun z => ‖f z‖)]
    by_cases hD : -a ≤ D
    · have hmem : D ∈ cone ∅ (-a) := ⟨fun v hv => absurd hv (Finset.notMem_empty v), fun v => hD v⟩
      rw [Set.indicator_of_mem hmem, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      have hle : ∀ u ∈ integralUnits, ‖f (piD D * u)‖ ≤ B * r ^ Divisor.deg D := fun u hu => by
        simp only [hf]
        rw [_root_.norm_mul, _root_.norm_mul, mul_assoc, hσ, hnormz, div_piD_mul D hu]
        exact mul_le_mul_of_nonneg_right (hB _) (zpow_nonneg hr0 _)
      calc ∫ u in integralUnits, ‖f (piD D * u)‖ ∂μ ≤ ∫ u in integralUnits, B * r ^ Divisor.deg D ∂μ :=
            setIntegral_mono_on (by
              refine ContinuousOn.integrableOn_compact isCompact_integralUnits ?_
              exact ((continuous_integrand hΦ s).comp (continuous_const.mul continuous_id)).norm.continuousOn)
              (integrableOn_const (measure_integralUnits_lt_top μ).ne) isOpen_integralUnits.measurableSet hle
        _ = _ := by rw [setIntegral_const, smul_eq_mul, Measure.real]; ring
    · rw [Set.indicator_of_notMem (fun h => hD fun v => h.2 v)]
      rw [norm_zero, mul_zero]
      refine le_of_eq (setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_)
      simp only [hf]
      rw [hs _ (fun h => hD ((piD_mul_mem_U_iff a D hu).1 h)), zero_mul, zero_mul, norm_zero]
  obtain ⟨N, α, -, hsum⟩ := hasSum_cone hc ∅ (-a)
  have hqr : ‖(Nat.card Fq : ℂ) * (r : ℂ)‖ < 1 := by
    rw [_root_.norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hr,
      ← Real.rpow_one_add' hq0.le (by linarith)]
    · exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  obtain ⟨-, hSn⟩ := hsum (r : ℂ) hqr
  have hint : IntegrableOn f (⋃ D : Divisor Fq k, {z | div z = D}) μ :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun D => ContinuousOn.integrableOn_compact (isCompact_fiber D) (continuous_integrand hΦ s).continuousOn)
      (Summable.of_nonneg_of_le (fun D => integral_nonneg fun z => norm_nonneg _) hpiecen
        (hSn.mul_left _))
  have hHS := hasSum_integral_iUnion (fun D => measurableSet_fiber D) pairwise_disjoint_fiber hint
  simp_rw [hpiece] at hHS
  rw [iUnion_fiber, setIntegral_univ] at hHS
  rw [iUnion_fiber] at hint
  exact ⟨integrableOn_univ.1 hint, hHS⟩

end FFIdeleGroup

/-! ### Theta series on a coset `π^E U` -/

namespace FFIdeleGroup

open Classical in
/-- The coefficient $a_n=\sum_{\deg D=n}g(D)$ of $u^n$ in $Z(\omega\omega_s,\Phi)$. -/
def aCoef (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k) (Φ : FFAdeleRing Fq k → ℂ) (n : ℤ) : ℂ :=
  ∑ᶠ D ∈ {D : Divisor Fq k | Divisor.deg D = n}, gInt μ ω Φ D

theorem finite_setOf_le_add_div (a E : Divisor Fq k) : {ξ : kˣ | -a ≤ E + Divisor.div ξ}.Finite := by
  haveI : Finite (E + a).riemannRochSpace := Module.finite_of_finite Fq
  refine Set.Finite.of_finite_image (f := fun ξ : kˣ => (ξ : k)) ?_ (fun x _ y _ h => Units.ext h)
  refine (Set.toFinite ((E + a).riemannRochSpace : Set k)).subset ?_
  rintro _ ⟨ξ, hξ, rfl⟩
  rw [SetLike.mem_coe, Divisor.mem_riemannRochSpace_iff_ord _ ξ.ne_zero]
  intro v
  have := hξ v
  simp only [Finsupp.neg_apply, Finsupp.add_apply, Divisor.div_apply] at this ⊢
  omega

theorem principal_mul_piD (ξ : kˣ) (E : Divisor Fq k) (u : FFIdeleGroup Fq k) :
    principal ξ * (piD E * u) = piD (E + Divisor.div ξ) * (((piD (Divisor.div ξ))⁻¹ * principal ξ) * u) := by
  rw [piD_add, mul_assoc (piD E), mul_assoc, mul_inv_cancel_left]
  exact mul_left_comm (principal ξ : FFIdeleGroup Fq k) _ _

theorem div_mem_principalDivisors (ξ : kˣ) : Divisor.div ξ ∈ principalDivisors Fq k :=
  AddMonoidHom.mem_range.2 ⟨Additive.ofMul ξ, rfl⟩

/-- **The theta identity on a coset** (unfolding $k^\times$): for $\Phi$ supported in $U(\mathfrak a)$,
$\int_U\omega(\pi^Eu)\sum_{\xi\in k^\times}\Phi(\xi\pi^Eu)\,d\mu(u)=(q-1)\sum_{D\sim E}g(D)$. -/
theorem setIntegral_theta (hc : IsConstantField Fq k) (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure]
    (ω : FFHeckeCharacter Fq k) {Φ : FFAdeleRing Fq k → ℂ} (hΦ : FFAdeleRing.IsSchwartzBruhat Φ)
    {a : Divisor Fq k} (hs : ∀ x, x ∉ U a → Φ x = 0) (E : Divisor Fq k) :
    ∫ u in integralUnits, ω.ev (piD E * u) *
        ∑ᶠ ξ : kˣ, Φ ((principal ξ * (piD E * u) : FFIdeleGroup Fq k) : FFAdeleRing Fq k) ∂μ =
      ((Nat.card Fq : ℂ) - 1) * ∑ᶠ D ∈ {D : Divisor Fq k | D - E ∈ principalDivisors Fq k}, gInt μ ω Φ D := by
  classical
  set T := (finite_setOf_le_add_div a E).toFinset with hT
  have hmemT : ∀ ξ, ξ ∈ T ↔ -a ≤ E + Divisor.div ξ := fun ξ => by simp [hT]
  have hsupp : ∀ u ∈ integralUnits, ∀ ξ : kˣ,
      Φ ((principal ξ * (piD E * u) : FFIdeleGroup Fq k) : FFAdeleRing Fq k) ≠ 0 → ξ ∈ T := by
    intro u hu ξ hne
    rw [hmemT]
    rw [principal_mul_piD] at hne
    by_contra h
    exact hne (hs _ fun hm => h ((piD_mul_mem_U_iff a _
      (mul_mem_integralUnits (principal_mul_piD_inv_mem ξ) hu)).1 hm))
  have h1 : ∀ u ∈ integralUnits, ω.ev (piD E * u) *
      ∑ᶠ ξ : kˣ, Φ ((principal ξ * (piD E * u) : FFIdeleGroup Fq k) : FFAdeleRing Fq k) =
      ∑ ξ ∈ T, Φ ((principal ξ * (piD E * u) : FFIdeleGroup Fq k) : FFAdeleRing Fq k) * ω.ev (piD E * u) := by
    intro u hu
    rw [finsum_eq_sum_of_support_subset _ (s := T) (fun ξ hξ => hsupp u hu ξ hξ), Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [setIntegral_congr_fun isOpen_integralUnits.measurableSet h1]
  have hcont : ∀ ξ : kˣ, Continuous fun u : FFIdeleGroup Fq k =>
      Φ ((principal ξ * (piD E * u) : FFIdeleGroup Fq k) : FFAdeleRing Fq k) * ω.ev (piD E * u) := fun ξ =>
    (hΦ.continuous.comp (Units.continuous_val.comp
      (continuous_const.mul (continuous_const.mul continuous_id)))).mul
      (ω.continuous_ev.comp (continuous_const.mul continuous_id))
  rw [integral_finset_sum _ fun ξ _ =>
    ContinuousOn.integrableOn_compact isCompact_integralUnits (hcont ξ).continuousOn]
  have h2 : ∀ ξ : kˣ, ∫ u in integralUnits,
      Φ ((principal ξ * (piD E * u) : FFIdeleGroup Fq k) : FFAdeleRing Fq k) * ω.ev (piD E * u) ∂μ =
      gInt μ ω Φ (E + Divisor.div ξ) := by
    intro ξ
    have hε := principal_mul_piD_inv_mem (Fq := Fq) ξ
    have := setIntegral_integralUnits_mul_left μ hε (fun w =>
      Φ ((piD (E + Divisor.div ξ) * w : FFIdeleGroup Fq k) : FFAdeleRing Fq k) *
        ω.ev (piD (E + Divisor.div ξ) * w))
    rw [gInt, ← this]
    refine setIntegral_congr_fun isOpen_integralUnits.measurableSet fun u _ => ?_
    rw [← principal_mul_piD, ← ω.ev_principal_mul ξ (piD E * u)]
  simp_rw [h2]
  -- regroup by `D = E + div ξ`
  set φ : kˣ → Divisor Fq k := fun ξ => E + Divisor.div ξ with hφ
  rw [Finset.sum_comp (fun D => gInt μ ω Φ D) φ]
  have hcard : ∀ D ∈ T.image φ, (T.filter fun ξ => φ ξ = D).card = Nat.card Fq - 1 := by
    intro D hD
    obtain ⟨ξ₀, hξ₀, rfl⟩ := Finset.mem_image.1 hD
    have hset : ((T.filter fun ξ => φ ξ = φ ξ₀ : Finset kˣ) : Set kˣ) = divSet (Fq := Fq) (Divisor.div ξ₀) := by
      ext ξ
      simp only [Finset.coe_filter, Set.mem_setOf_eq, divSet, hφ]
      constructor
      · rintro ⟨-, h⟩; exact add_left_cancel h
      · intro h; refine ⟨?_, by rw [h]⟩; rw [hmemT, h]; exact (hmemT ξ₀).1 hξ₀
    have := encard_divSet (Fq := Fq) hc (E := Divisor.div ξ₀) (ξ₀ := ξ₀) rfl
    rw [← hset, Set.encard_coe_eq_coe_finsetCard] at this
    exact_mod_cast this
  rw [Finset.sum_congr rfl fun D hD => by rw [hcard D hD]]
  have hq1 : 1 ≤ Nat.card Fq := Nat.card_pos
  simp_rw [nsmul_eq_mul]
  rw [← Finset.mul_sum, Nat.cast_sub hq1, Nat.cast_one]
  congr 1
  symm
  refine finsum_mem_eq_sum_of_subset _ ?_ ?_
  · rintro D ⟨hD, hne⟩
    obtain ⟨ξ, hξ⟩ := (mem_principalDivisors_iff _).1 hD
    have hle : -a ≤ D := by
      by_contra h
      exact hne (gInt_eq_zero hs h)
    refine Finset.mem_image.2 ⟨ξ, (hmemT ξ).2 ?_, ?_⟩
    · rw [hξ, add_sub_cancel]; exact hle
    · simp only [hφ, hξ, add_sub_cancel]
  · intro D hD
    obtain ⟨ξ, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hD)
    simp only [Set.mem_setOf_eq, hφ, add_sub_cancel_left]
    exact div_mem_principalDivisors ξ

end FFIdeleGroup

/-! ### The quasicharacters `ω_t` and `ω_1 ω⁻¹` -/

namespace FFHeckeCharacter

/-- A continuous morphism $k_{\mathbb A}^\times\to\mathbb C^\times$ trivial on $k^\times$, as a quasicharacter of
$G_k$. -/
def ofIdeleHom (f : FFIdeleGroup Fq k →* ℂˣ) (hf : Continuous f) (hP : ∀ ξ : kˣ, f (principal ξ) = 1) :
    FFHeckeCharacter Fq k where
  toMonoidHom := QuotientGroup.lift _ f (by rintro _ ⟨ξ, rfl⟩; exact hP ξ)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 hf

theorem ev_ofIdeleHom (f : FFIdeleGroup Fq k →* ℂˣ) (hf : Continuous f) (hP : ∀ ξ : kˣ, f (principal ξ) = 1)
    (z : FFIdeleGroup Fq k) : (ofIdeleHom f hf hP).ev z = (f z : ℂ) := rfl

/-- $z\mapsto\omega_t(z)=\lvert z\rvert^t=(q^{-t})^{\deg\operatorname{div}z}$ as a morphism to $\mathbb C^\times$. -/
def omegaHom (t : ℂ) : FFIdeleGroup Fq k →* ℂˣ where
  toFun z := Units.mk0 (uS Fq t ^ Divisor.deg (div z)) (zpow_ne_zero _ (uS_ne_zero t))
  map_one' := by ext; simp [FFIdeleGroup.div_one]
  map_mul' z w := by ext; simp [FFIdeleGroup.div_mul, zpow_add₀ (uS_ne_zero t)]

theorem continuous_omegaHom (t : ℂ) : Continuous (omegaHom (Fq := Fq) (k := k) t) := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  refine (continuousAt_const : ContinuousAt (fun _ => omegaHom t z) z).congr ?_
  filter_upwards [div_eventually_eq z] with w hw
  ext; simp [omegaHom, hw]

variable (Fq k) in
/-- **The quasicharacter $\omega_t(z)=\lvert z\rvert^t$** of $G_k$. -/
def omegaQC (t : ℂ) : FFHeckeCharacter Fq k :=
  ofIdeleHom (omegaHom t) (continuous_omegaHom t) fun ξ => by
    ext; simp [omegaHom, div_principal, Divisor.deg_div_eq_zero]

theorem ev_omegaQC (t : ℂ) (z : FFIdeleGroup Fq k) : (omegaQC Fq k t).ev z = omegaS t z := by
  rw [omegaQC, ev_ofIdeleHom, omegaS_eq]; rfl

/-- **The dual quasicharacter** $\check\omega=\omega_1\omega^{-1}$ of Weil's functional equation. -/
def dual (ω : FFHeckeCharacter Fq k) : FFHeckeCharacter Fq k := omegaQC Fq k 1 * ω⁻¹

theorem ev_dual (ω : FFHeckeCharacter Fq k) (z : FFIdeleGroup Fq k) :
    ω.dual.ev z = omegaS 1 z * (ω.ev z)⁻¹ := by
  rw [← ev_omegaQC]
  show ((omegaQC Fq k 1 (QuotientGroup.mk z) * (ω (QuotientGroup.mk z))⁻¹ : ℂˣ) : ℂ) = _
  rw [Units.val_mul, Units.val_inv_eq_inv_val]; rfl

end FFHeckeCharacter

/-! ### The full theta series and its functional equation on a coset -/

theorem finsum_k_eq (f : k → ℂ) (hf : (Function.support f).Finite) :
    ∑ᶠ ξ : k, f ξ = f 0 + ∑ᶠ ξ : kˣ, f ξ := by
  have hU : (Set.univ : Set k) = insert 0 (Set.range (Units.val : kˣ → k)) := by
    ext x
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_range, true_iff]
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr ⟨Units.mk0 x hx, rfl⟩
  have h0 : (0 : k) ∉ Set.range (Units.val : kˣ → k) := by
    rintro ⟨ξ, hξ⟩; exact ξ.ne_zero hξ
  rw [← finsum_mem_univ, hU, finsum_mem_insert' f h0 (hf.subset Set.inter_subset_right),
    finsum_mem_range (fun a b h => Units.ext h)]

namespace FFIdeleGroup

/-- The full theta integral $\int_U\omega(\pi^Eu)\sum_{\xi\in k}\Phi(\xi\pi^Eu)\,d\mu(u)$. -/
def thetaFull (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k) (Φ : FFAdeleRing Fq k → ℂ)
    (E : Divisor Fq k) : ℂ :=
  ∫ u in integralUnits, ω.ev (piD E * u) *
    ∑ᶠ ξ : k, Φ (diag ξ * ((piD E * u : FFIdeleGroup Fq k) : FFAdeleRing Fq k)) ∂μ

theorem coe_principal_mul (ξ : kˣ) (z : FFIdeleGroup Fq k) :
    ((principal ξ * z : FFIdeleGroup Fq k) : FFAdeleRing Fq k) = diag (ξ : k) * (z : FFAdeleRing Fq k) := rfl

variable (ψ₀ : AddChar Fq Circle)

/-- **The functional equation of the theta integral on a coset** (Poisson summation at $\pi^Eu$ and $u\mapsto u^{-1}$):
$\Theta_{\omega,\Phi}(E)=q^{1-g}\,\Theta_{\check\omega,\hat\Phi}(-E)$. -/
theorem thetaFull_fe (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) (μ : Measure (FFIdeleGroup Fq k))
    [μ.IsHaarMeasure] (ω : FFHeckeCharacter Fq k) {Φ : FFAdeleRing Fq k → ℂ}
    (hΦ : FFAdeleRing.IsSchwartzBruhat Φ) (E : Divisor Fq k) :
    thetaFull μ ω Φ E = (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) *
      thetaFull μ ω.dual (fourierFF ψ₀ Φ) (-E) := by
  rw [thetaFull, thetaFull, ← integral_const_mul,
    ← setIntegral_integralUnits_inv μ (fun u => (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) *
      (ω.dual.ev (piD (-E) * u) * ∑ᶠ ξ : k, fourierFF ψ₀ Φ
        (diag ξ * ((piD (-E) * u : FFIdeleGroup Fq k) : FFAdeleRing Fq k))))]
  refine setIntegral_congr_fun isOpen_integralUnits.measurableSet fun u hu => ?_
  have hinv : piD (-E) * u⁻¹ = (piD E * u)⁻¹ := by rw [piD_neg]; exact (mul_inv (piD E) u).symm
  rw [hinv, poisson_idele ψ₀ hc hψ₀ hΦ (piD E * u), FFHeckeCharacter.ev_dual, FFHeckeCharacter.ev_inv, inv_inv,
    div_piD_mul E hu, omegaS_eq, div_inv', div_piD_mul E hu, map_neg, uS, Complex.cpow_neg_one]
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := Fq); exact_mod_cast this.ne'
  rw [inv_zpow', neg_neg]
  ring

end FFIdeleGroup

/-! ### Class sums and the coefficients `a_n` -/

namespace FFIdeleGroup

/-- The class sum $\sum_{D\sim E}g(D)$. -/
def classSum (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k) (Φ : FFAdeleRing Fq k → ℂ)
    (E : Divisor Fq k) : ℂ :=
  ∑ᶠ D ∈ {D : Divisor Fq k | D - E ∈ principalDivisors Fq k}, gInt μ ω Φ D

theorem classSum_congr (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k) (Φ : FFAdeleRing Fq k → ℂ)
    {E E' : Divisor Fq k} (h : E - E' ∈ principalDivisors Fq k) : classSum μ ω Φ E = classSum μ ω Φ E' := by
  have hset : {D : Divisor Fq k | D - E ∈ principalDivisors Fq k} = {D | D - E' ∈ principalDivisors Fq k} := by
    ext D
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hD
      have := (principalDivisors Fq k).add_mem hD h
      rwa [sub_add_sub_cancel] at this
    · intro hD
      have := (principalDivisors Fq k).sub_mem hD h
      rwa [sub_sub_sub_cancel_right] at this
  unfold classSum
  rw [hset]

theorem deg_eq_of_sub_mem {D E : Divisor Fq k} (h : D - E ∈ principalDivisors Fq k) :
    Divisor.deg D = Divisor.deg E := by
  obtain ⟨ξ, hξ⟩ := (mem_principalDivisors_iff _).1 h
  have := Divisor.deg_div_eq_zero (Fq := Fq) ξ
  rw [hξ, map_sub] at this
  omega

/-- **The coefficient $a_n$ as a sum of class sums** over the classes of degree $n$, represented by
`baseDiv b₁ n C` ($\deg b_1=1$). -/
theorem aCoef_eq_sum_classSum (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k)
    {Φ : FFAdeleRing Fq k → ℂ} {a : Divisor Fq k} (hs : ∀ x, x ∉ U a → Φ x = 0) [Fintype (ClassGroup0 Fq k)]
    {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) (n : ℤ) :
    aCoef μ ω Φ n = ∑ C : ClassGroup0 Fq k, classSum μ ω Φ (baseDiv b₁ n C) := by
  classical
  set S := (finite_cone_deg (Fq := Fq) (k := k) ∅ (-a) n).toFinset with hS
  have hmemS : ∀ D, D ∈ S ↔ -a ≤ D ∧ Divisor.deg D = n := fun D => by
    simp only [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq, cone, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true, true_and]
    exact Iff.rfl
  have hA : aCoef μ ω Φ n = ∑ D ∈ S, gInt μ ω Φ D := by
    refine finsum_mem_eq_sum_of_subset _ ?_ ?_
    · rintro D ⟨hD, hne⟩
      exact (hmemS D).2 ⟨by by_contra h; exact hne (gInt_eq_zero hs h), hD⟩
    · intro D hD; exact ((hmemS D).1 (Finset.mem_coe.1 hD)).2
  have hC : ∀ C, classSum μ ω Φ (baseDiv b₁ n C) = ∑ D ∈ S with clsOf hb D = C, gInt μ ω Φ D := by
    intro C
    refine finsum_mem_eq_sum_of_subset _ ?_ ?_
    · rintro D ⟨hD, hne⟩
      have hdeg : Divisor.deg D = n := by rw [deg_eq_of_sub_mem hD, deg_baseDiv hb]
      refine Finset.mem_filter.2 ⟨(hmemS D).2 ⟨by by_contra h; exact hne (gInt_eq_zero hs h), hdeg⟩, ?_⟩
      exact (clsOf_eq_iff hb hdeg C).2 hD
    · intro D hD
      obtain ⟨hDS, hcl⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hD)
      exact (clsOf_eq_iff hb ((hmemS D).1 hDS).2 C).1 hcl
  rw [hA, Finset.sum_congr rfl fun C _ => hC C]
  exact (Finset.sum_fiberwise S (clsOf hb) (gInt μ ω Φ)).symm

/-- `a_n` from any system of representatives of the classes of degree `n`. -/
theorem aCoef_eq_sum_classSum_of_reps (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k)
    {Φ : FFAdeleRing Fq k → ℂ} {a : Divisor Fq k} (hs : ∀ x, x ∉ U a → Φ x = 0) [Fintype (ClassGroup0 Fq k)]
    {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) (n : ℤ) (E : ClassGroup0 Fq k → Divisor Fq k)
    (σ : ClassGroup0 Fq k ≃ ClassGroup0 Fq k) (hE : ∀ C, E C - baseDiv b₁ n (σ C) ∈ principalDivisors Fq k) :
    ∑ C, classSum μ ω Φ (E C) = aCoef μ ω Φ n := by
  rw [aCoef_eq_sum_classSum μ ω hs hb n, Finset.sum_congr rfl fun C _ => classSum_congr μ ω Φ (hE C)]
  exact Equiv.sum_comp σ (fun C => classSum μ ω Φ (baseDiv b₁ n C))

/-- `-baseDiv b₁ n C` represents the class `-C` in degree `-n`. -/
theorem neg_baseDiv_sub_mem {b₁ : Divisor Fq k} (n : ℤ) (C : ClassGroup0 Fq k) :
    -baseDiv b₁ n C - baseDiv b₁ (-n) (Equiv.neg _ C) ∈ principalDivisors Fq k := by
  have hmem : (-repKer C - repKer (-C) : (Divisor.deg (Fq := Fq) (k := k)).ker) ∈
      (principalDivisors Fq k).addSubgroupOf (Divisor.deg (Fq := Fq) (k := k)).ker := by
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_neg, mk_repKer, mk_repKer]
    abel
  have := AddSubgroup.mem_addSubgroupOf.1 hmem
  convert this using 1
  simp only [baseDiv, Equiv.neg_apply, AddSubgroup.coe_sub, AddSubgroup.coe_neg, neg_smul]
  abel

/-! ### Splitting the full theta integral -/

theorem theta_integrableOn (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure]
    (ω : FFHeckeCharacter Fq k) {Φ : FFAdeleRing Fq k → ℂ} (hΦ : FFAdeleRing.IsSchwartzBruhat Φ)
    {a : Divisor Fq k} (hs : ∀ x, x ∉ U a → Φ x = 0) (E : Divisor Fq k) :
    IntegrableOn (fun u => ω.ev (piD E * u) *
        ∑ᶠ ξ : kˣ, Φ ((principal ξ * (piD E * u) : FFIdeleGroup Fq k) : FFAdeleRing Fq k)) integralUnits μ := by
  classical
  set T := (finite_setOf_le_add_div a E).toFinset with hT
  have hmemT : ∀ ξ, ξ ∈ T ↔ -a ≤ E + Divisor.div ξ := fun ξ => by simp [hT]
  have h1 : ∀ u ∈ integralUnits, ∑ ξ ∈ T, ω.ev (piD E * u) *
      Φ ((principal ξ * (piD E * u) : FFIdeleGroup Fq k) : FFAdeleRing Fq k) = ω.ev (piD E * u) *
      ∑ᶠ ξ : kˣ, Φ ((principal ξ * (piD E * u) : FFIdeleGroup Fq k) : FFAdeleRing Fq k) := by
    intro u hu
    rw [finsum_eq_sum_of_support_subset _ (s := T) ?_, Finset.mul_sum]
    intro ξ hne
    rw [Function.mem_support, principal_mul_piD] at hne
    rw [Finset.mem_coe, hmemT]
    by_contra h
    exact hne (hs _ fun hm => h ((piD_mul_mem_U_iff a _
      (mul_mem_integralUnits (principal_mul_piD_inv_mem ξ) hu)).1 hm))
  refine IntegrableOn.congr_fun ?_ h1 isOpen_integralUnits.measurableSet
  refine integrable_finset_sum _ fun ξ _ => ContinuousOn.integrableOn_compact isCompact_integralUnits ?_
  exact ((ω.continuous_ev.comp (continuous_const.mul continuous_id)).mul
    (hΦ.continuous.comp (Units.continuous_val.comp
      (continuous_const.mul (continuous_const.mul continuous_id))))).continuousOn

/-- $\Theta_{\omega,\Phi}(E)=\Phi(0)\int_U\omega(\pi^Eu)\,d\mu+(q-1)\sum_{D\sim E}g(D)$. -/
theorem thetaFull_eq (hc : IsConstantField Fq k) (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure]
    (ω : FFHeckeCharacter Fq k) {Φ : FFAdeleRing Fq k → ℂ} (hΦ : FFAdeleRing.IsSchwartzBruhat Φ)
    {a : Divisor Fq k} (hs : ∀ x, x ∉ U a → Φ x = 0) (E : Divisor Fq k) :
    thetaFull μ ω Φ E = Φ 0 * ∫ u in integralUnits, ω.ev (piD E * u) ∂μ +
      ((Nat.card Fq : ℂ) - 1) * classSum μ ω Φ E := by
  rw [classSum, ← setIntegral_theta hc μ ω hΦ hs E, ← integral_const_mul, ← integral_add]
  · rw [thetaFull]
    refine setIntegral_congr_fun isOpen_integralUnits.measurableSet fun u hu => ?_
    rw [finsum_k_eq _ (FFAdeleRing.finite_support_diag (hΦ.mulRight (piD E * u)))]
    have : (diag (0 : k) : FFAdeleRing Fq k) = 0 := map_zero diagHom
    simp only [coe_principal_mul, this, zero_mul]
    ring
  · exact (ContinuousOn.integrableOn_compact isCompact_integralUnits
      (continuous_const.mul (FFHeckeCharacter.continuous_ev ω |>.comp
        (continuous_const.mul continuous_id))).continuousOn)
  · exact theta_integrableOn μ ω hΦ hs E

end FFIdeleGroup

/-! ### The per-degree functional equation and the polar terms -/

namespace FFIdeleGroup

theorem piD_zsmul (n : ℤ) (D : Divisor Fq k) : piD (n • D) = piD D ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [natCast_zsmul, piD_nsmul, zpow_natCast]
  · rw [neg_smul, natCast_zsmul, piD_neg, piD_nsmul, zpow_neg, zpow_natCast]

/-- $D\mapsto\pi^D$ as a morphism from the (multiplicative) divisor group. -/
def piDHom : Multiplicative (Divisor Fq k) →* FFIdeleGroup Fq k where
  toFun D := piD (Multiplicative.toAdd D)
  map_one' := piD_zero
  map_mul' D E := piD_add _ _

/-- The polar sum $\sum_C\int_U\omega(\pi^{E_C}u)\,d\mu(u)$ over a family of divisors. -/
def poleSum (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k) [Fintype (ClassGroup0 Fq k)]
    (E : ClassGroup0 Fq k → Divisor Fq k) : ℂ :=
  ∑ C, ∫ u in integralUnits, ω.ev (piD (E C) * u) ∂μ

variable (ψ₀ : AddChar Fq Circle)

/-- **The functional equation in degree $n$**:
$\Phi(0)P_n(\omega)+(q-1)a_n(\omega,\Phi)=q^{1-g}\big(\hat\Phi(0)P_{-n}(\check\omega)+(q-1)a_{-n}(\check\omega,\hat\Phi)\big)$,
with the polar sums $P$ over `baseDiv b₁ n C` and over `-baseDiv b₁ n C`. -/
theorem aCoef_fe (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure]
    (ω : FFHeckeCharacter Fq k) {Φ : FFAdeleRing Fq k → ℂ} (hΦ : FFAdeleRing.IsSchwartzBruhat Φ)
    [Fintype (ClassGroup0 Fq k)] {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) (n : ℤ) :
    Φ 0 * poleSum μ ω (baseDiv b₁ n) + ((Nat.card Fq : ℂ) - 1) * aCoef μ ω Φ n =
      (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * (fourierFF ψ₀ Φ 0 * poleSum μ ω.dual (fun C => -baseDiv b₁ n C) +
        ((Nat.card Fq : ℂ) - 1) * aCoef μ ω.dual (fourierFF ψ₀ Φ) (-n)) := by
  obtain ⟨a, -, hs, -⟩ := id hΦ
  obtain ⟨a', -, hs', -⟩ := id (FFAdeleRing.isSchwartzBruhat_fourierFF ψ₀ hψ₀ hΦ)
  have hL : ∑ C, thetaFull μ ω Φ (baseDiv b₁ n C) =
      Φ 0 * poleSum μ ω (baseDiv b₁ n) + ((Nat.card Fq : ℂ) - 1) * aCoef μ ω Φ n := by
    simp_rw [thetaFull_eq hc μ ω hΦ hs]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, aCoef_eq_sum_classSum μ ω hs hb n, poleSum]
  have hR : ∑ C, thetaFull μ ω.dual (fourierFF ψ₀ Φ) (-baseDiv b₁ n C) =
      fourierFF ψ₀ Φ 0 * poleSum μ ω.dual (fun C => -baseDiv b₁ n C) +
        ((Nat.card Fq : ℂ) - 1) * aCoef μ ω.dual (fourierFF ψ₀ Φ) (-n) := by
    simp_rw [thetaFull_eq hc μ ω.dual (FFAdeleRing.isSchwartzBruhat_fourierFF ψ₀ hψ₀ hΦ) hs']
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, poleSum,
      aCoef_eq_sum_classSum_of_reps μ ω.dual hs' hb (-n) (fun C => -baseDiv b₁ n C) (Equiv.neg _)
        (fun C => neg_baseDiv_sub_mem n C)]
  rw [← hL, ← hR, Finset.mul_sum]
  exact Finset.sum_congr rfl fun C _ => thetaFull_fe ψ₀ hc hψ₀ μ ω hΦ _

/-! #### Evaluation of the polar sums -/

/-- $\omega$ is trivial on the ideles of norm $1$, i.e. $\omega=\omega_t$ for some $t$ (Weil: the quasicharacters
trivial on $G_k^1$). -/
def IsNormOneTrivial (ω : FFHeckeCharacter Fq k) : Prop := ∀ z ∈ normOne Fq k, ω.ev z = 1

theorem piD_mul_mem_normOne {E : Divisor Fq k} (hE : Divisor.deg E = 0) {u : FFIdeleGroup Fq k}
    (hu : u ∈ integralUnits) : piD E * u ∈ normOne Fq k := by
  rw [mem_normOne_iff, div_piD_mul E hu, hE]

theorem ev_piD_mul_of_trivial {ω : FFHeckeCharacter Fq k} (hω : IsNormOneTrivial ω) {b₁ : Divisor Fq k}
    (hb : Divisor.deg b₁ = 1) (E : Divisor Fq k) {u : FFIdeleGroup Fq k} (hu : u ∈ integralUnits) :
    ω.ev (piD E * u) = ω.ev (piD b₁) ^ Divisor.deg E := by
  have h : piD E * u = piD b₁ ^ Divisor.deg E * (piD (E - Divisor.deg E • b₁) * u) := by
    rw [piD_sub, piD_zsmul, ← mul_assoc, mul_comm (piD b₁ ^ _), mul_assoc (piD E), inv_mul_cancel, mul_one]
  rw [h, FFHeckeCharacter.ev_mul, FFHeckeCharacter.ev_zpow, hω _ (piD_mul_mem_normOne (by
    rw [map_sub, map_zsmul, hb, smul_eq_mul, mul_one, sub_self]) hu), mul_one]

/-- The polar sum of a quasicharacter trivial on the ideles of norm 1: $h\,\mu(U)\,\lambda^m$. -/
theorem poleSum_of_trivial (μ : Measure (FFIdeleGroup Fq k)) {ω : FFHeckeCharacter Fq k}
    (hω : IsNormOneTrivial ω) [Fintype (ClassGroup0 Fq k)] {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1)
    {m : ℤ} (E : ClassGroup0 Fq k → Divisor Fq k) (hE : ∀ C, Divisor.deg (E C) = m) :
    poleSum μ ω E = (Fintype.card (ClassGroup0 Fq k) : ℂ) * ((μ integralUnits).toReal : ℂ) *
      ω.ev (piD b₁) ^ m := by
  rw [poleSum]
  have : ∀ C, ∫ u in integralUnits, ω.ev (piD (E C) * u) ∂μ =
      ((μ integralUnits).toReal : ℂ) * ω.ev (piD b₁) ^ m := fun C => by
    rw [setIntegral_congr_fun isOpen_integralUnits.measurableSet
      (fun u hu => ev_piD_mul_of_trivial hω hb (E C) hu), setIntegral_const, hE C, Complex.real_smul]
    rfl
  rw [Finset.sum_congr rfl fun C _ => this C, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The polar sum vanishes unless $\omega$ is trivial on the ideles of norm 1 (orthogonality on $U$ and on $D_0/P$). -/
theorem poleSum_of_not_trivial (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure] {ω : FFHeckeCharacter Fq k}
    (hω : ¬ IsNormOneTrivial ω) [Fintype (ClassGroup0 Fq k)] {b₁ : Divisor Fq k} (m : ℤ)
    (E : ClassGroup0 Fq k → Divisor Fq k) (σ : ClassGroup0 Fq k ≃ ClassGroup0 Fq k)
    (hE : ∀ C, E C - baseDiv b₁ m (σ C) ∈ principalDivisors Fq k) :
    poleSum μ ω E = 0 := by
  classical
  rw [poleSum]
  have hsplit : ∀ D : Divisor Fq k, ∫ u in integralUnits, ω.ev (piD D * u) ∂μ =
      ω.ev (piD D) * ∫ u in integralUnits, ω.ev u ∂μ := fun D => by
    simp_rw [FFHeckeCharacter.ev_mul]; exact integral_const_mul _ _
  simp_rw [hsplit, FFHeckeCharacter.setIntegral_ev]
  by_cases hU : ∀ u ∈ integralUnits, ω.ev u = 1
  · simp only [if_pos hU]
    rw [← Finset.sum_mul]
    -- the character `D ↦ ω(π^D)` of the divisor group
    let χ : Multiplicative (Divisor Fq k) →* ℂˣ :=
      (ω : FFIdeleClassGroup Fq k →* ℂˣ).comp ((QuotientGroup.mk' _).comp piDHom)
    have hχ : ∀ D, ((χ (Multiplicative.ofAdd D) : ℂˣ) : ℂ) = ω.ev (piD D) := fun D => rfl
    have hP : ∀ f : kˣ, χ (Multiplicative.ofAdd (Divisor.div f)) = 1 := fun f => by
      apply Units.ext
      rw [hχ, Units.val_one]
      have h := principal_mul_piD_inv_mem (Fq := Fq) f
      have : piD (Divisor.div f) = principal (Fq := Fq) f * ((piD (Divisor.div f))⁻¹ * principal f)⁻¹ := by
        rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]
      rw [this, FFHeckeCharacter.ev_principal_mul, FFHeckeCharacter.ev_inv, hU _ h, inv_one]
    have hcl : ∀ D D' : Divisor Fq k, D - D' ∈ principalDivisors Fq k → ω.ev (piD D) = ω.ev (piD D') := by
      intro D D' h
      obtain ⟨f, hf⟩ := (mem_principalDivisors_iff _).1 h
      rw [← hχ, ← hχ, show D = D' + Divisor.div f by rw [hf]; abel, ofAdd_add, map_mul, hP, mul_one]
    rw [Finset.sum_congr rfl fun C _ => hcl _ _ (hE C)]
    rw [Equiv.sum_comp σ (fun C => ω.ev (piD (baseDiv b₁ m C)))]
    -- a degree-zero divisor where `χ` is nontrivial
    unfold IsNormOneTrivial at hω
    push Not at hω
    obtain ⟨z, hz, hne⟩ := hω
    have hdeg : Divisor.deg (div z) = 0 := (mem_normOne_iff z).1 hz
    have hz' : ω.ev z = ω.ev (piD (div z)) := by
      have hmem := (mem_fiber_iff (div z) z).1 rfl
      have : z = piD (div z) * ((piD (div z))⁻¹ * z) := by rw [mul_inv_cancel_left]
      rw [this, FFHeckeCharacter.ev_mul, hU _ hmem, mul_one, ← this]
    have hne' : χ (Multiplicative.ofAdd (div z)) ≠ 1 := fun h => hne (by
      rw [hz', ← hχ, h, Units.val_one])
    have := sum_class_eq_zero χ hP b₁ m (div z) hdeg hne'
    simp only [hχ] at this
    rw [this, zero_mul]
  · simp only [if_neg hU, mul_zero, Finset.sum_const_zero]

end FFIdeleGroup

/-! ### The coefficients for large and small degree -/

namespace FFIdeleGroup

theorem aCoef_eq_zero_of_lt (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k)
    {Φ : FFAdeleRing Fq k → ℂ} {a : Divisor Fq k} (hs : ∀ x, x ∉ U a → Φ x = 0) {n : ℤ}
    (hn : n < -Divisor.deg a) : aCoef μ ω Φ n = 0 := by
  rw [aCoef]
  refine finsum_mem_eq_zero_of_forall_eq_zero fun D hD => gInt_eq_zero hs fun h => ?_
  have := Divisor.deg_mono h
  rw [map_neg, show Divisor.deg D = n from hD] at this
  omega

theorem isNormOneTrivial_dual_iff (ω : FFHeckeCharacter Fq k) :
    IsNormOneTrivial ω.dual ↔ IsNormOneTrivial ω := by
  have h : ∀ z ∈ normOne Fq k, ω.dual.ev z = (ω.ev z)⁻¹ := fun z hz => by
    rw [FFHeckeCharacter.ev_dual, omegaS_eq, (mem_normOne_iff z).1 hz, zpow_zero, one_mul]
  refine ⟨fun H z hz => ?_, fun H z hz => ?_⟩
  · have := H z hz; rw [h z hz] at this; exact inv_eq_one.1 this
  · rw [h z hz, H z hz, inv_one]

theorem ev_dual_piD {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) (ω : FFHeckeCharacter Fq k) :
    ω.dual.ev (piD b₁) = (Nat.card Fq : ℂ)⁻¹ * (ω.ev (piD b₁))⁻¹ := by
  rw [FFHeckeCharacter.ev_dual, omegaS_eq, div_piD, hb, zpow_one, uS, Complex.cpow_neg_one]

variable (ψ₀ : AddChar Fq Circle)

open Classical in
/-- **The coefficients for large degree**: for $n>\deg\hat{\mathfrak a}$ ($\hat\Phi$ supported in
$U(\hat{\mathfrak a})$), $a_n=c_\mu\lambda^n\big(q^{1-g}\hat\Phi(0)q^n-\Phi(0)\big)$ if $\omega$ is trivial on the ideles of
norm 1 ($\lambda=\omega(\pi^{b_1})$, $\deg b_1=1$) and $a_n=0$ otherwise. -/
theorem aCoef_tail (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure]
    (ω : FFHeckeCharacter Fq k) {Φ : FFAdeleRing Fq k → ℂ} (hΦ : FFAdeleRing.IsSchwartzBruhat Φ)
    {a' : Divisor Fq k} (hs' : ∀ x, x ∉ U a' → fourierFF ψ₀ Φ x = 0)
    {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) {n : ℤ} (hn : Divisor.deg a' < n) :
    aCoef μ ω Φ n = if IsNormOneTrivial ω then zetaConst μ * ω.ev (piD b₁) ^ n *
      ((Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ 0 * (Nat.card Fq : ℂ) ^ n - Φ 0) else 0 := by
  haveI : Finite (ClassGroup0 Fq k) := finite_classGroup0
  haveI : Fintype (ClassGroup0 Fq k) := Fintype.ofFinite _
  have hfe := aCoef_fe ψ₀ hc hψ₀ μ ω hΦ hb n
  rw [aCoef_eq_zero_of_lt μ ω.dual hs' (by omega), mul_zero, add_zero] at hfe
  have hq1 : (Nat.card Fq : ℂ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Nat.card Fq := by exact_mod_cast (Finite.one_lt_card (α := Fq))
    intro h
    have h' : (Nat.card Fq : ℂ) = 1 := sub_eq_zero.1 h
    have : ((Nat.card Fq : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact h'
    have := Complex.ofReal_injective this
    linarith
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := Fq); exact_mod_cast this.ne'
  split_ifs with hω
  · have hlam : ω.ev (piD b₁) ≠ 0 := ω.ev_ne_zero _
    rw [poleSum_of_trivial μ hω hb (baseDiv b₁ n) (fun C => deg_baseDiv hb n C),
      poleSum_of_trivial μ ((isNormOneTrivial_dual_iff ω).2 hω) hb (fun C => -baseDiv b₁ n C)
        (fun C => by rw [map_neg, deg_baseDiv hb]), ev_dual_piD hb] at hfe
    rw [zetaConst, Nat.card_eq_fintype_card]
    have hreal : (μ.real integralUnits : ℂ) = ((μ integralUnits).toReal : ℂ) := rfl
    rw [hreal]
    rw [mul_zpow, inv_zpow', inv_zpow', neg_neg] at hfe
    field_simp
    linear_combination hfe
  · rw [poleSum_of_not_trivial μ hω (b₁ := b₁) n (baseDiv b₁ n) (Equiv.refl _) (fun C => by simp),
      poleSum_of_not_trivial μ (fun h => hω ((isNormOneTrivial_dual_iff ω).1 h)) (-n)
        (fun C => -baseDiv b₁ n C) (Equiv.neg _) (fun C => neg_baseDiv_sub_mem n C)] at hfe
    simp only [mul_zero, zero_add] at hfe
    exact (mul_eq_zero.1 hfe).resolve_left hq1

end FFIdeleGroup

/-! ### The zeta integral as a rational function of `u = q^{-s}` -/

namespace FFIdeleGroup

/-- **Regrouping by degree**: $Z(\omega\omega_s,\Phi)=\sum_na_nu^n$. -/
theorem hasSum_aCoef (hc : IsConstantField Fq k) (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure]
    (ω : FFHeckeCharacter Fq k) {Φ : FFAdeleRing Fq k → ℂ} (hΦ : FFAdeleRing.IsSchwartzBruhat Φ) {s : ℂ}
    {σ : ℝ} (hσ : ∀ z, ‖ω.ev z‖ * ‖omegaS s z‖ = (norm z : ℝ) ^ σ) (h1 : 1 < σ) :
    HasSum (fun n : ℤ => aCoef μ ω Φ n * uS Fq s ^ n) (zetaQ μ ω Φ s) := by
  classical
  obtain ⟨-, hS⟩ := hasSum_zetaQ hc μ ω hΦ hσ h1
  obtain ⟨a, -, hs, -⟩ := id hΦ
  set f : Divisor Fq k → ℂ := fun D => gInt μ ω Φ D * uS Fq s ^ Divisor.deg D with hf
  let e := Equiv.sigmaFiberEquiv (Divisor.deg (Fq := Fq) (k := k))
  have hfib : ∀ n : ℤ, HasSum (fun y : {D : Divisor Fq k // Divisor.deg D = n} => f y)
      (aCoef μ ω Φ n * uS Fq s ^ n) := by
    intro n
    set F := (finite_cone_deg (Fq := Fq) (k := k) ∅ (-a) n).toFinset with hF
    have hmemF : ∀ D, D ∈ F ↔ -a ≤ D ∧ Divisor.deg D = n := fun D => by
      simp only [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, cone, Finset.notMem_empty, IsEmpty.forall_iff,
        implies_true, true_and]
      exact Iff.rfl
    let Fs : Finset {D : Divisor Fq k // Divisor.deg D = n} := F.subtype (fun D => Divisor.deg D = n)
    have hA : aCoef μ ω Φ n = ∑ D ∈ F, gInt μ ω Φ D := by
      refine finsum_mem_eq_sum_of_subset _ ?_ ?_
      · rintro D ⟨hD, hne⟩
        exact (hmemF D).2 ⟨by by_contra h; exact hne (gInt_eq_zero hs h), hD⟩
      · intro D hD; exact ((hmemF D).1 (Finset.mem_coe.1 hD)).2
    have : HasSum (fun y : {D : Divisor Fq k // Divisor.deg D = n} => f y) (∑ y ∈ Fs, f y) :=
      hasSum_sum_of_ne_finset_zero (by
        intro y hy
        simp only [Fs, Finset.mem_subtype, hmemF, not_and] at hy
        simp only [hf]
        rw [gInt_eq_zero hs (fun h => hy h y.2), zero_mul])
    convert this using 1
    rw [hA, Finset.sum_mul, Finset.sum_subtype_eq_sum_filter,
      Finset.filter_true_of_mem (fun D hD => ((hmemF D).1 hD).2)]
    refine Finset.sum_congr rfl fun D hD => ?_
    simp only [hf, ((hmemF D).1 hD).2]
  have hσ' : HasSum (f ∘ e) (zetaQ μ ω Φ s) := e.hasSum_iff.2 hS
  exact hσ'.sigma (fun n => hfib n)

end FFIdeleGroup

namespace FFIdeleGroup

variable (ψ₀ : AddChar Fq Circle)

open Classical in
/-- **The rational function** $R(u)=\sum_{|n|\le M}a_nu^n+c_\mu\Big(\frac{\Phi'(0)(q\lambda u)^{M+1}}{1-q\lambda u}
-\frac{\Phi(0)(\lambda u)^{M+1}}{1-\lambda u}\Big)$, the second term only when $\omega$ is trivial on the ideles of norm
1; $\lambda=\omega(\pi^{b_1})$ and $\Phi'=q^{1-g}\hat\Phi$ (the Fourier transform for the self-dual measure). -/
def zetaRat (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k) (Φ : FFAdeleRing Fq k → ℂ)
    (b₁ : Divisor Fq k) (M : ℕ) (u : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(M : ℤ)) M, aCoef μ ω Φ n * u ^ n +
    if IsNormOneTrivial ω then zetaConst μ *
      ((Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ 0 *
          ((Nat.card Fq : ℂ) * (ω.ev (piD b₁) * u)) ^ (M + 1) / (1 - (Nat.card Fq : ℂ) * (ω.ev (piD b₁) * u)) -
        Φ 0 * (ω.ev (piD b₁) * u) ^ (M + 1) / (1 - ω.ev (piD b₁) * u))
    else 0

theorem sum_Ico_eq_sum_Icc {f : ℤ → ℂ} (M : ℕ) (h : f (-((M : ℤ) + 1)) = 0) :
    ∑ n ∈ Finset.Ico (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ), f n = ∑ n ∈ Finset.Icc (-(M : ℤ)) M, f n := by
  symm
  refine Finset.sum_subset (fun n hn => ?_) (fun n hn hn' => ?_)
  · rw [Finset.mem_Icc] at hn; rw [Finset.mem_Ico]; push_cast; omega
  · rw [Finset.mem_Ico] at hn; rw [Finset.mem_Icc] at hn'; push_cast at hn
    have : n = -((M : ℤ) + 1) := by omega
    rw [this, h]

/-- **The zeta integral is the rational function `zetaRat`** wherever it converges ($\lvert\omega\omega_s\rvert=\omega_\sigma$,
$\sigma>1$), for every cutoff $M\ge\deg\mathfrak a,\deg\hat{\mathfrak a}$. -/
theorem zetaQ_eq_zetaRat (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) (μ : Measure (FFIdeleGroup Fq k))
    [μ.IsHaarMeasure] (ω : FFHeckeCharacter Fq k) {Φ : FFAdeleRing Fq k → ℂ}
    (hΦ : FFAdeleRing.IsSchwartzBruhat Φ) {a a' : Divisor Fq k} (hs : ∀ x, x ∉ U a → Φ x = 0)
    (hs' : ∀ x, x ∉ U a' → fourierFF ψ₀ Φ x = 0) {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) {M : ℕ}
    (hMa : Divisor.deg a ≤ M) (hMa' : Divisor.deg a' ≤ M) {s : ℂ} {σ : ℝ}
    (hσ : ∀ z, ‖ω.ev z‖ * ‖omegaS s z‖ = (norm z : ℝ) ^ σ) (h1 : 1 < σ) :
    zetaQ μ ω Φ s = zetaRat ψ₀ μ ω Φ b₁ M (uS Fq s) := by
  classical
  have H := hasSum_aCoef hc μ ω hΦ hσ h1
  set u := uS Fq s with hu
  set lam := ω.ev (piD b₁) with hlam
  set q : ℂ := (Nat.card Fq : ℂ) with hq
  have hlow : ∀ n : ℤ, n < -(M : ℤ) → aCoef μ ω Φ n = 0 := fun n hn =>
    aCoef_eq_zero_of_lt μ ω hs (by omega)
  have htail := fun n (hn : (M : ℤ) < n) => aCoef_tail ψ₀ hc hψ₀ μ ω hΦ hs' hb (n := n) (by omega)
  rw [zetaRat]
  split_ifs with hω
  · -- the norm of `λ u`
    have hq1 : (1 : ℝ) < Nat.card Fq := by exact_mod_cast (Finite.one_lt_card (α := Fq))
    have hq0 : (0 : ℝ) < Nat.card Fq := by linarith
    have hnl : ‖lam * u‖ = (Nat.card Fq : ℝ) ^ (-σ) := by
      have := hσ (piD b₁)
      rw [omegaS_eq, div_piD, hb, zpow_one, norm_piD, hb] at this
      rw [_root_.norm_mul, hu, hlam, this]
      push_cast
      rw [← Real.rpow_intCast, ← Real.rpow_mul hq0.le]
      norm_num
    have hlu : ‖lam * u‖ < 1 := by
      rw [hnl]; exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
    have hqlu : ‖q * (lam * u)‖ < 1 := by
      rw [_root_.norm_mul, hnl, hq, Complex.norm_natCast,
        ← Real.rpow_one_add' hq0.le (by linarith)]
      · exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
    have hlam0 : lam ≠ 0 := ω.ev_ne_zero _
    set c' : ℤ → ℂ := fun n => aCoef μ ω Φ n * lam ^ (-n) with hc'
    have hE : EvForm q c' (M + 1) (zetaConst μ * (q ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ 0))
        (-(zetaConst μ * Φ 0)) := by
      refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · simp only [hc']; rw [hlow n (by push_cast at hn; omega), zero_mul]
      · simp only [hc']
        rw [htail n (by push_cast at hn; omega), if_pos hω, zpow_neg]
        field_simp
        ring
    have H2 := hasSum_evForm hE hqlu hlu
    have heq : (fun n : ℤ => c' n * (lam * u) ^ n) = fun n => aCoef μ ω Φ n * u ^ n := by
      ext n
      simp only [hc']
      rw [mul_zpow, zpow_neg]
      field_simp
    rw [heq] at H2
    rw [H.unique H2, sum_Ico_eq_sum_Icc M (by rw [hlow _ (by omega), zero_mul])]
    ring
  · have H2 : HasSum (fun n : ℤ => aCoef μ ω Φ n * u ^ n)
        (∑ n ∈ Finset.Icc (-(M : ℤ)) M, aCoef μ ω Φ n * u ^ n) := by
      refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with hn | hn
      · rw [hlow n hn, zero_mul]
      · rw [htail n hn, if_neg hω, zero_mul]
    rw [H.unique H2, add_zero]

end FFIdeleGroup

/-! ### The functional equation of the rational function -/

theorem sum_Icc_zpow {x : ℂ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.Icc (-(M : ℤ)) M, x ^ n = ((x ^ M)⁻¹ - x ^ M * x) / (1 - x) := by
  have h1 : ∑ n ∈ Finset.Icc (-(M : ℤ)) M, x ^ n = ∑ j ∈ Finset.range (2 * M + 1), x ^ ((j : ℤ) - M) := by
    refine Finset.sum_nbij' (fun n => (n + M).toNat) (fun j => (j : ℤ) - M) (fun n hn => ?_) (fun j hj => ?_)
      (fun n hn => ?_) (fun j hj => ?_) (fun n hn => ?_)
    · simp only [Finset.mem_Icc] at hn; simp only [Finset.mem_range]; omega
    · simp only [Finset.mem_range] at hj; simp only [Finset.mem_Icc]; omega
    · simp only [Finset.mem_Icc] at hn; omega
    · simp
    · simp only [Finset.mem_Icc] at hn; congr 1; omega
  have h2 : ∀ j : ℕ, x ^ ((j : ℤ) - M) = (x ^ M)⁻¹ * x ^ j := fun j => by
    rw [zpow_sub₀ hx0, zpow_natCast, zpow_natCast, div_eq_mul_inv, mul_comm]
  rw [h1, Finset.sum_congr rfl fun j _ => h2 j, ← Finset.mul_sum, geom_sum_eq hx1]
  have hxM : x ^ M ≠ 0 := pow_ne_zero _ hx0
  have h3 : (1 : ℂ) - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx1)
  have h4 : x - 1 ≠ 0 := sub_ne_zero.2 hx1
  field_simp
  ring

theorem sum_Icc_neg (f : ℤ → ℂ) (M : ℕ) :
    ∑ n ∈ Finset.Icc (-(M : ℤ)) M, f (-n) = ∑ n ∈ Finset.Icc (-(M : ℤ)) M, f n := by
  refine Finset.sum_nbij' (fun n => -n) (fun n => -n) (fun n hn => ?_) (fun n hn => ?_) (fun n _ => neg_neg n)
    (fun n _ => neg_neg n) (fun n _ => rfl)
  · simp only [Finset.mem_Icc] at hn ⊢; omega
  · simp only [Finset.mem_Icc] at hn ⊢; omega

namespace FFIdeleGroup

theorem aCoef_eq_finset_sum (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k)
    {Φ : FFAdeleRing Fq k → ℂ} {a : Divisor Fq k} (hs : ∀ x, x ∉ U a → Φ x = 0) (n : ℤ) :
    aCoef μ ω Φ n = ∑ D ∈ (finite_cone_deg (Fq := Fq) (k := k) ∅ (-a) n).toFinset, gInt μ ω Φ D := by
  have hmemF : ∀ D, D ∈ (finite_cone_deg (Fq := Fq) (k := k) ∅ (-a) n).toFinset ↔ -a ≤ D ∧ Divisor.deg D = n :=
    fun D => by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, cone, Finset.notMem_empty, IsEmpty.forall_iff,
        implies_true, true_and]
      exact Iff.rfl
  refine finsum_mem_eq_sum_of_subset _ ?_ ?_
  · rintro D ⟨hD, hne⟩
    exact (hmemF D).2 ⟨by by_contra h; exact hne (gInt_eq_zero hs h), hD⟩
  · intro D hD; exact ((hmemF D).1 (Finset.mem_coe.1 hD)).2

theorem gInt_const_mul (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k) (Φ : FFAdeleRing Fq k → ℂ)
    (c : ℂ) (D : Divisor Fq k) : gInt μ ω (fun x => c * Φ x) D = c * gInt μ ω Φ D := by
  rw [gInt, gInt, ← integral_const_mul]
  simp_rw [mul_assoc]

theorem aCoef_const_mul (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k)
    {Φ : FFAdeleRing Fq k → ℂ} {a : Divisor Fq k} (hs : ∀ x, x ∉ U a → Φ x = 0) (c : ℂ) (n : ℤ) :
    aCoef μ ω (fun x => c * Φ x) n = c * aCoef μ ω Φ n := by
  rw [aCoef_eq_finset_sum μ ω hs, aCoef_eq_finset_sum μ ω (Φ := fun x => c * Φ x)
    (fun x hx => by rw [hs x hx, mul_zero]), Finset.mul_sum]
  exact Finset.sum_congr rfl fun D _ => gInt_const_mul μ ω Φ c D

end FFIdeleGroup

namespace FFAdeleRing

variable (ψ₀ : AddChar Fq Circle)

theorem fourierFF_const_mul (Φ : FFAdeleRing Fq k → ℂ) (c : ℂ) (y : FFAdeleRing Fq k) :
    fourierFF ψ₀ (fun x => c * Φ x) y = c * fourierFF ψ₀ Φ y := by
  rw [fourierFF, fourierFF, ← integral_const_mul]
  simp_rw [mul_assoc]

theorem IsSchwartzBruhat.const_mul {Φ : FFAdeleRing Fq k → ℂ} (hΦ : IsSchwartzBruhat Φ) (c : ℂ) :
    IsSchwartzBruhat fun x => c * Φ x := by
  obtain ⟨a, b, hs, hinv⟩ := hΦ
  exact ⟨a, b, fun x hx => by simp [hs x hx], fun x u hu => by simp only [hinv x u hu]⟩

end FFAdeleRing

end

end NumberFieldKB.WeilBNT.FF

namespace NumberFieldKB.WeilBNT.FF

noncomputable section

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

set_option linter.unusedSectionVars false

open FFIdeleGroup FFAdeleRing

namespace FFIdeleGroup

variable (ψ₀ : AddChar Fq Circle)

open Classical in
/-- **The coefficient relation** $a_{-n}(\check\omega,\Phi')=a_n(\omega,\Phi)+c_\mu\big(\Phi(0)\lambda^n-\Phi'(0)q^n\lambda^n\big)$
(the last term only when $\omega$ is trivial on the ideles of norm 1), $\Phi'=q^{1-g}\hat\Phi$. -/
theorem aCoef_dual (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure]
    (ω : FFHeckeCharacter Fq k) {Φ : FFAdeleRing Fq k → ℂ} (hΦ : FFAdeleRing.IsSchwartzBruhat Φ)
    {a' : Divisor Fq k} (hs' : ∀ x, x ∉ U a' → fourierFF ψ₀ Φ x = 0)
    {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) (n : ℤ) :
    aCoef μ ω.dual (fun x => (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ x) (-n) =
      aCoef μ ω Φ n + if IsNormOneTrivial ω then zetaConst μ * (Φ 0 * ω.ev (piD b₁) ^ n -
        (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ 0 * (Nat.card Fq : ℂ) ^ n *
          ω.ev (piD b₁) ^ n) else 0 := by
  haveI : Finite (ClassGroup0 Fq k) := finite_classGroup0
  haveI : Fintype (ClassGroup0 Fq k) := Fintype.ofFinite _
  have hfe := aCoef_fe ψ₀ hc hψ₀ μ ω hΦ hb n
  rw [aCoef_const_mul μ ω.dual hs']
  have hq1 : (Nat.card Fq : ℂ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Nat.card Fq := by exact_mod_cast (Finite.one_lt_card (α := Fq))
    intro h
    have h' : (Nat.card Fq : ℂ) = 1 := sub_eq_zero.1 h
    have : ((Nat.card Fq : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact h'
    have := Complex.ofReal_injective this
    linarith
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := Fq); exact_mod_cast this.ne'
  split_ifs with hω
  · rw [poleSum_of_trivial μ hω hb (baseDiv b₁ n) (fun C => deg_baseDiv hb n C),
      poleSum_of_trivial μ ((isNormOneTrivial_dual_iff ω).2 hω) hb (fun C => -baseDiv b₁ n C)
        (fun C => by rw [map_neg, deg_baseDiv hb]), ev_dual_piD hb] at hfe
    rw [mul_zpow, inv_zpow', inv_zpow', neg_neg] at hfe
    rw [zetaConst, Nat.card_eq_fintype_card (α := ClassGroup0 Fq k)]
    have hreal : (μ.real integralUnits : ℂ) = ((μ integralUnits).toReal : ℂ) := rfl
    rw [hreal]
    field_simp
    linear_combination -hfe
  · rw [poleSum_of_not_trivial μ hω (b₁ := b₁) n (baseDiv b₁ n) (Equiv.refl _) (fun C => by simp),
      poleSum_of_not_trivial μ (fun h => hω ((isNormOneTrivial_dual_iff ω).1 h)) (-n)
        (fun C => -baseDiv b₁ n C) (Equiv.neg _) (fun C => neg_baseDiv_sub_mem n C)] at hfe
    simp only [mul_zero, zero_add, add_zero] at hfe ⊢
    have := mul_left_cancel₀ hq1 (hfe.trans (by ring : _ = ((Nat.card Fq : ℂ) - 1) *
      ((Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * aCoef μ ω.dual (fourierFF ψ₀ Φ) (-n))))
    exact this.symm

end FFIdeleGroup

namespace FFIdeleGroup

variable (ψ₀ : AddChar Fq Circle)

/-- **The functional equation of the rational function**: $R_{\omega,\Phi}(u)=R_{\check\omega,\Phi'}(u^{-1})$,
$\Phi'=q^{1-g}\hat\Phi$, for $u\ne0$ away from the poles. -/
theorem zetaRat_fe (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) (μ : Measure (FFIdeleGroup Fq k)) [μ.IsHaarMeasure]
    (ω : FFHeckeCharacter Fq k) {Φ : FFAdeleRing Fq k → ℂ} (hΦ : FFAdeleRing.IsSchwartzBruhat Φ)
    {a' : Divisor Fq k} (hs' : ∀ x, x ∉ U a' → fourierFF ψ₀ Φ x = 0)
    {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) (M : ℕ) {u : ℂ} (hu : u ≠ 0)
    (hx : IsNormOneTrivial ω → ω.ev (piD b₁) * u ≠ 1)
    (hy : IsNormOneTrivial ω → (Nat.card Fq : ℂ) * (ω.ev (piD b₁) * u) ≠ 1) :
    zetaRat ψ₀ μ ω Φ b₁ M u =
      zetaRat ψ₀ μ ω.dual (fun x => (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ x) b₁ M u⁻¹ := by
  classical
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := Fq); exact_mod_cast this.ne'
  have hlam0 : ω.ev (piD b₁) ≠ 0 := ω.ev_ne_zero _
  -- the double transform at `0`
  have hFF : (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ (fun x => (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ x) 0 = Φ 0 := by
    rw [fourierFF_const_mul, fourierFF_fourierFF ψ₀ hc hψ₀ hΦ, neg_zero, ← mul_assoc, ← mul_assoc,
      ← zpow_add₀ hq0, ← zpow_add₀ hq0,
      show (1 - Rep.genusInt Fq k) + (1 - Rep.genusInt Fq k) + (2 * Rep.genusInt Fq k - 2) = 0 by ring,
      zpow_zero, one_mul]
  -- the sum part
  have hsum : ∑ n ∈ Finset.Icc (-(M : ℤ)) M, aCoef μ ω.dual (fun x => (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ x) n * u⁻¹ ^ n =
      ∑ n ∈ Finset.Icc (-(M : ℤ)) M, aCoef μ ω Φ n * u ^ n +
        if IsNormOneTrivial ω then zetaConst μ * (Φ 0 * ∑ n ∈ Finset.Icc (-(M : ℤ)) M, (ω.ev (piD b₁) * u) ^ n -
          (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ 0 * ∑ n ∈ Finset.Icc (-(M : ℤ)) M, ((Nat.card Fq : ℂ) * (ω.ev (piD b₁) * u)) ^ n) else 0 := by
    rw [← sum_Icc_neg]
    simp_rw [aCoef_dual ψ₀ hc hψ₀ μ ω hΦ hs' hb]
    split_ifs with hω
    · simp_rw [add_mul, Finset.sum_add_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun n _ => by rw [inv_zpow', neg_neg]
      · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [inv_zpow', neg_neg, mul_zpow, mul_zpow, mul_zpow]
        ring
    · simp only [add_zero]
      exact Finset.sum_congr rfl fun n _ => by rw [inv_zpow', neg_neg]
  rw [zetaRat, zetaRat, hsum, ev_dual_piD hb]
  simp only [isNormOneTrivial_dual_iff]
  split_ifs with hω
  · have hx' := hx hω
    have hy' := hy hω
    have hx0 : ω.ev (piD b₁) * u ≠ 0 := mul_ne_zero hlam0 hu
    have hy0 : (Nat.card Fq : ℂ) * (ω.ev (piD b₁) * u) ≠ 0 := mul_ne_zero hq0 hx0
    rw [sum_Icc_zpow hx0 hx' M, sum_Icc_zpow hy0 hy' M]
    rw [show (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ (fun x => (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ x) 0 = Φ 0 from hFF]
    have e1 : (Nat.card Fq : ℂ) * ((Nat.card Fq : ℂ)⁻¹ * (ω.ev (piD b₁))⁻¹ * u⁻¹) = (ω.ev (piD b₁) * u)⁻¹ := by field_simp
    have e2 : (Nat.card Fq : ℂ)⁻¹ * (ω.ev (piD b₁))⁻¹ * u⁻¹ = ((Nat.card Fq : ℂ) * (ω.ev (piD b₁) * u))⁻¹ := by field_simp
    rw [e1, e2]
    generalize (∑ n ∈ Finset.Icc (-(M : ℤ)) M, aCoef μ ω Φ n * u ^ n) = S
    generalize ω.ev (piD b₁) * u = X at hx' hy' hx0 hy0 ⊢
    have h1 : (1 : ℂ) - X ≠ 0 := sub_ne_zero.2 (Ne.symm hx')
    have h2 : (1 : ℂ) - (Nat.card Fq : ℂ) * X ≠ 0 := sub_ne_zero.2 (Ne.symm hy')
    have h3 : X - 1 ≠ 0 := sub_ne_zero.2 hx'
    have h4 : (Nat.card Fq : ℂ) * X - 1 ≠ 0 := sub_ne_zero.2 hy'
    have hxM : X ^ M ≠ 0 := pow_ne_zero _ hx0
    have hyM : ((Nat.card Fq : ℂ) * X) ^ M ≠ 0 := pow_ne_zero _ hy0
    rw [inv_pow, inv_pow, pow_succ, pow_succ]
    field_simp
    ring
  · simp only [add_zero]

end FFIdeleGroup

/-! ### Partial fractions, holomorphy and the polar parts -/

theorem pow_succ_div_one_sub {x : ℂ} (hx : x ≠ 1) (M : ℕ) :
    x ^ (M + 1) / (1 - x) = (1 - x)⁻¹ - ∑ j ∈ Finset.range (M + 1), x ^ j := by
  have h1 : (1 : ℂ) - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hg := geom_sum_mul_neg x (M + 1)
  field_simp
  linear_combination hg

namespace FFIdeleGroup

variable (ψ₀ : AddChar Fq Circle)

open Classical in
/-- `zetaRat` in partial fractions: the polar terms are $c_\mu\Phi'(0)(1-q\lambda u)^{-1}$ and
$-c_\mu\Phi(0)(1-\lambda u)^{-1}$, plus a Laurent polynomial. This is the form in which the continuation is stated. -/
def zetaPF (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k) (Φ : FFAdeleRing Fq k → ℂ)
    (b₁ : Divisor Fq k) (M : ℕ) (u : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(M : ℤ)) M, aCoef μ ω Φ n * u ^ n +
    if IsNormOneTrivial ω then zetaConst μ *
      ((Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ 0 *
          ((1 - (Nat.card Fq : ℂ) * (ω.ev (piD b₁) * u))⁻¹ -
            ∑ j ∈ Finset.range (M + 1), ((Nat.card Fq : ℂ) * (ω.ev (piD b₁) * u)) ^ j) -
        Φ 0 * ((1 - ω.ev (piD b₁) * u)⁻¹ - ∑ j ∈ Finset.range (M + 1), (ω.ev (piD b₁) * u) ^ j))
    else 0

theorem zetaRat_eq_zetaPF (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k)
    (Φ : FFAdeleRing Fq k → ℂ) (b₁ : Divisor Fq k) (M : ℕ) {u : ℂ}
    (hx : IsNormOneTrivial ω → ω.ev (piD b₁) * u ≠ 1)
    (hy : IsNormOneTrivial ω → (Nat.card Fq : ℂ) * (ω.ev (piD b₁) * u) ≠ 1) :
    zetaRat ψ₀ μ ω Φ b₁ M u = zetaPF ψ₀ μ ω Φ b₁ M u := by
  rw [zetaRat, zetaPF]
  split_ifs with hω
  · rw [mul_div_assoc, mul_div_assoc, pow_succ_div_one_sub (hx hω), pow_succ_div_one_sub (hy hω)]
  · rfl

theorem analyticAt_zetaPF (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k)
    (Φ : FFAdeleRing Fq k → ℂ) (b₁ : Divisor Fq k) (M : ℕ) {s : ℂ}
    (hx : IsNormOneTrivial ω → ω.ev (piD b₁) * uS Fq s ≠ 1)
    (hy : IsNormOneTrivial ω → (Nat.card Fq : ℂ) * (ω.ev (piD b₁) * uS Fq s) ≠ 1) :
    AnalyticAt ℂ (fun s => zetaPF ψ₀ μ ω Φ b₁ M (uS Fq s)) s := by
  classical
  have hL : AnalyticAt ℂ (fun s => ∑ n ∈ Finset.Icc (-(M : ℤ)) M, aCoef μ ω Φ n * uS Fq s ^ n) s :=
    Finset.analyticAt_fun_sum (f := fun n s => aCoef μ ω Φ n * uS Fq s ^ n) _ fun n _ => analyticAt_const.mul ((analyticAt_uS s).zpow (uS_ne_zero s))
  have hX : AnalyticAt ℂ (fun s => ω.ev (piD b₁) * uS Fq s) s := analyticAt_const.mul (analyticAt_uS s)
  have hY : AnalyticAt ℂ (fun s => (Nat.card Fq : ℂ) * (ω.ev (piD b₁) * uS Fq s)) s := analyticAt_const.mul hX
  unfold zetaPF
  by_cases hω : IsNormOneTrivial ω
  · simp only [if_pos hω]
    refine hL.add (analyticAt_const.mul (AnalyticAt.sub (analyticAt_const.mul (AnalyticAt.sub ?_ ?_))
      (analyticAt_const.mul (AnalyticAt.sub ?_ ?_))))
    · exact (analyticAt_const.sub hY).inv (sub_ne_zero.2 (Ne.symm (hy hω)))
    · exact Finset.analyticAt_fun_sum _ fun j _ => hY.pow j
    · exact (analyticAt_const.sub hX).inv (sub_ne_zero.2 (Ne.symm (hx hω)))
    · exact Finset.analyticAt_fun_sum _ fun j _ => hX.pow j
  · simp only [if_neg hω, add_zero]
    exact hL

theorem meromorphicOn_zetaPF (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k)
    (Φ : FFAdeleRing Fq k → ℂ) (b₁ : Divisor Fq k) (M : ℕ) :
    MeromorphicOn (fun s => zetaPF ψ₀ μ ω Φ b₁ M (uS Fq s)) Set.univ := by
  classical
  intro s _
  have hL : AnalyticAt ℂ (fun s => ∑ n ∈ Finset.Icc (-(M : ℤ)) M, aCoef μ ω Φ n * uS Fq s ^ n) s :=
    Finset.analyticAt_fun_sum (f := fun n s => aCoef μ ω Φ n * uS Fq s ^ n) _ fun n _ => analyticAt_const.mul ((analyticAt_uS s).zpow (uS_ne_zero s))
  have hX : AnalyticAt ℂ (fun s => ω.ev (piD b₁) * uS Fq s) s := analyticAt_const.mul (analyticAt_uS s)
  have hY : AnalyticAt ℂ (fun s => (Nat.card Fq : ℂ) * (ω.ev (piD b₁) * uS Fq s)) s := analyticAt_const.mul hX
  unfold zetaPF
  by_cases hω : IsNormOneTrivial ω
  · simp only [if_pos hω]
    refine hL.meromorphicAt.add (analyticAt_const.meromorphicAt.mul (MeromorphicAt.sub
      (analyticAt_const.meromorphicAt.mul (MeromorphicAt.sub ?_ ?_))
      (analyticAt_const.meromorphicAt.mul (MeromorphicAt.sub ?_ ?_))))
    · exact (analyticAt_const.sub hY).meromorphicAt.inv
    · exact (Finset.analyticAt_fun_sum _ fun j _ => hY.pow j).meromorphicAt
    · exact (analyticAt_const.sub hX).meromorphicAt.inv
    · exact (Finset.analyticAt_fun_sum _ fun j _ => hX.pow j).meromorphicAt
  · simp only [if_neg hω, add_zero]
    exact hL.meromorphicAt

theorem ev_eq_of_trivial {ω : FFHeckeCharacter Fq k} (hω : IsNormOneTrivial ω) {b₁ : Divisor Fq k}
    (hb : Divisor.deg b₁ = 1) (z : FFIdeleGroup Fq k) :
    ω.ev z = ω.ev (piD b₁) ^ Divisor.deg (div z) := by
  have hmem := (mem_fiber_iff (div z) z).1 rfl
  have : z = piD (div z) * ((piD (div z))⁻¹ * z) := by rw [mul_inv_cancel_left]
  conv_lhs => rw [this]
  exact ev_piD_mul_of_trivial hω hb _ hmem

theorem isNormOneTrivial_of_eq_omegaS {ω : FFHeckeCharacter Fq k} {s₀ : ℂ} {f : FFIdeleGroup Fq k → ℂ}
    (hf : ∀ z ∈ normOne Fq k, f z = 1) (h : ∀ z, ω.ev z * omegaS s₀ z = f z) : IsNormOneTrivial ω := by
  intro z hz
  have := h z
  rw [hf z hz, omegaS_eq, (mem_normOne_iff z).1 hz, zpow_zero, mul_one] at this
  exact this

theorem uS_sub (s s₀ : ℂ) : uS Fq (s - s₀) = uS Fq s * (uS Fq s₀)⁻¹ := by
  have hq : (Nat.card Fq : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := Fq); exact_mod_cast this.ne'
  rw [uS, uS, uS, neg_sub, Complex.cpow_sub _ _ hq, Complex.cpow_neg, Complex.cpow_neg, inv_inv, div_eq_mul_inv,
    mul_comm]

/-- **The polar part at $\omega_0$**: if $\omega\omega_{s_0}=1$, then
$Z(s)+c_\mu\Phi(0)(1-q^{-(s-s_0)})^{-1}$ is holomorphic at $s_0$. -/
theorem analyticAt_zetaPF_add_pole (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k)
    (Φ : FFAdeleRing Fq k → ℂ) {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) (M : ℕ) {s₀ : ℂ}
    (h0 : ∀ z, ω.ev z * omegaS s₀ z = 1) :
    AnalyticAt ℂ (fun s => zetaPF ψ₀ μ ω Φ b₁ M (uS Fq s) + zetaConst μ * Φ 0 * (1 - uS Fq (s - s₀))⁻¹) s₀ := by
  have hω : IsNormOneTrivial ω := isNormOneTrivial_of_eq_omegaS (fun _ _ => rfl) h0
  have hlam : ω.ev (piD b₁) * uS Fq s₀ = 1 := by
    have := h0 (piD b₁); rwa [omegaS_eq, div_piD, hb, zpow_one] at this
  have hl : ω.ev (piD b₁) = (uS Fq s₀)⁻¹ := eq_inv_of_mul_eq_one_left hlam
  have hX : ∀ s, ω.ev (piD b₁) * uS Fq s = uS Fq (s - s₀) := fun s => by
    rw [uS_sub, hl, mul_comm]
  have hq1 : (Nat.card Fq : ℂ) ≠ 1 := by
    exact_mod_cast (show Nat.card Fq ≠ 1 from (Finite.one_lt_card (α := Fq)).ne')
  have heq : (fun s => zetaPF ψ₀ μ ω Φ b₁ M (uS Fq s) + zetaConst μ * Φ 0 * (1 - uS Fq (s - s₀))⁻¹) =
      fun s => ∑ n ∈ Finset.Icc (-(M : ℤ)) M, aCoef μ ω Φ n * uS Fq s ^ n + zetaConst μ *
        ((Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ 0 *
          ((1 - (Nat.card Fq : ℂ) * uS Fq (s - s₀))⁻¹ -
            ∑ j ∈ Finset.range (M + 1), ((Nat.card Fq : ℂ) * uS Fq (s - s₀)) ^ j) +
          Φ 0 * ∑ j ∈ Finset.range (M + 1), uS Fq (s - s₀) ^ j) := by
    ext s
    rw [zetaPF, if_pos hω, hX]
    ring
  rw [heq]
  have hU : AnalyticAt ℂ (fun s => uS Fq (s - s₀)) s₀ := by
    have := (analyticAt_uS (Fq := Fq) 0).comp_sub s₀
    rwa [zero_add] at this
  refine (Finset.analyticAt_fun_sum (f := fun n s => aCoef μ ω Φ n * uS Fq s ^ n) _ fun n _ => analyticAt_const.mul
    ((analyticAt_uS s₀).zpow (uS_ne_zero s₀))).add (analyticAt_const.mul (AnalyticAt.add
    (analyticAt_const.mul (AnalyticAt.sub ?_ ?_)) (analyticAt_const.mul ?_)))
  · refine (analyticAt_const.sub (analyticAt_const.mul hU)).inv ?_
    show (1 : ℂ) - _ * uS Fq (s₀ - s₀) ≠ 0
    rw [sub_self, uS, neg_zero, Complex.cpow_zero, mul_one, sub_ne_zero]; exact Ne.symm hq1
  · exact Finset.analyticAt_fun_sum _ fun j _ => (analyticAt_const.mul hU).pow j
  · exact Finset.analyticAt_fun_sum _ fun j _ => hU.pow j

/-- **The polar part at $\omega_1$**: if $\omega\omega_{s_0}=\omega_1$, then
$Z(s)-c_\mu\Phi'(0)(1-q^{-(s-s_0)})^{-1}$ is holomorphic at $s_0$, $\Phi'=q^{1-g}\hat\Phi$. -/
theorem analyticAt_zetaPF_sub_pole (μ : Measure (FFIdeleGroup Fq k)) (ω : FFHeckeCharacter Fq k)
    (Φ : FFAdeleRing Fq k → ℂ) {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) (M : ℕ) {s₀ : ℂ}
    (h1 : ∀ z, ω.ev z * omegaS s₀ z = omegaS 1 z) :
    AnalyticAt ℂ (fun s => zetaPF ψ₀ μ ω Φ b₁ M (uS Fq s) - zetaConst μ *
      ((Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ 0) * (1 - uS Fq (s - s₀))⁻¹) s₀ := by
  have hω : IsNormOneTrivial ω := isNormOneTrivial_of_eq_omegaS (f := omegaS 1) (fun z hz => by
    rw [omegaS_eq, (mem_normOne_iff z).1 hz, zpow_zero]) h1
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := Fq); exact_mod_cast this.ne'
  have hlam : (Nat.card Fq : ℂ) * (ω.ev (piD b₁) * uS Fq s₀) = 1 := by
    have := h1 (piD b₁)
    rw [omegaS_eq, omegaS_eq, div_piD, hb, zpow_one, zpow_one] at this
    have hu1 : uS Fq 1 = (Nat.card Fq : ℂ)⁻¹ := by rw [uS, Complex.cpow_neg_one]
    rw [this, hu1, mul_inv_cancel₀ hq0]
  have hl : (Nat.card Fq : ℂ) * ω.ev (piD b₁) = (uS Fq s₀)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_assoc]; exact hlam)
  have hY : ∀ s, (Nat.card Fq : ℂ) * (ω.ev (piD b₁) * uS Fq s) = uS Fq (s - s₀) := fun s => by
    rw [uS_sub, ← mul_assoc, hl, mul_comm]
  have hX : ∀ s, ω.ev (piD b₁) * uS Fq s = (Nat.card Fq : ℂ)⁻¹ * uS Fq (s - s₀) := fun s => by
    rw [← hY]; field_simp
  have hq1 : (Nat.card Fq : ℂ)⁻¹ ≠ 1 := by
    rw [Ne, inv_eq_one]
    exact_mod_cast (show Nat.card Fq ≠ 1 from (Finite.one_lt_card (α := Fq)).ne')
  have heq : (fun s => zetaPF ψ₀ μ ω Φ b₁ M (uS Fq s) - zetaConst μ *
      ((Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ 0) * (1 - uS Fq (s - s₀))⁻¹) =
      fun s => ∑ n ∈ Finset.Icc (-(M : ℤ)) M, aCoef μ ω Φ n * uS Fq s ^ n + zetaConst μ *
        (-((Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ 0 *
            ∑ j ∈ Finset.range (M + 1), uS Fq (s - s₀) ^ j) -
          Φ 0 * ((1 - (Nat.card Fq : ℂ)⁻¹ * uS Fq (s - s₀))⁻¹ -
            ∑ j ∈ Finset.range (M + 1), ((Nat.card Fq : ℂ)⁻¹ * uS Fq (s - s₀)) ^ j)) := by
    ext s
    rw [zetaPF, if_pos hω, hY, hX]
    ring
  rw [heq]
  have hU : AnalyticAt ℂ (fun s => uS Fq (s - s₀)) s₀ := by
    have := (analyticAt_uS (Fq := Fq) 0).comp_sub s₀
    rwa [zero_add] at this
  refine (Finset.analyticAt_fun_sum (f := fun n s => aCoef μ ω Φ n * uS Fq s ^ n) _ fun n _ => analyticAt_const.mul
    ((analyticAt_uS s₀).zpow (uS_ne_zero s₀))).add (analyticAt_const.mul (AnalyticAt.sub
    (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun j _ => hU.pow j)).neg
    (analyticAt_const.mul (AnalyticAt.sub ?_ ?_))))
  · refine (analyticAt_const.sub (analyticAt_const.mul hU)).inv ?_
    show (1 : ℂ) - _ * uS Fq (s₀ - s₀) ≠ 0
    rw [sub_self, uS, neg_zero, Complex.cpow_zero, mul_one, sub_ne_zero]; exact Ne.symm hq1
  · exact Finset.analyticAt_fun_sum _ fun j _ => (analyticAt_const.mul hU).pow j

end FFIdeleGroup

/-! ### Weil VII.§5 Thm. 2 for function fields, every quasicharacter -/

namespace FFIdeleGroup

variable (ψ₀ : AddChar Fq Circle)

theorem uS_neg (s : ℂ) : uS Fq (-s) = (uS Fq s)⁻¹ := by
  rw [uS, uS, neg_neg, Complex.cpow_neg, inv_inv]

theorem norm_lam_uS {ω : FFHeckeCharacter Fq k} {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) {s : ℂ} {σ : ℝ}
    (hσ : ∀ z, ‖ω.ev z‖ * ‖omegaS s z‖ = (norm z : ℝ) ^ σ) :
    ‖ω.ev (piD b₁) * uS Fq s‖ = (Nat.card Fq : ℝ) ^ (-σ) := by
  have hq0 : (0 : ℝ) < Nat.card Fq := by exact_mod_cast (Nat.card_pos (α := Fq))
  have := hσ (piD b₁)
  rw [omegaS_eq, div_piD, hb, zpow_one, norm_piD, hb] at this
  rw [_root_.norm_mul, this]
  push_cast
  rw [← Real.rpow_intCast, ← Real.rpow_mul hq0.le]
  norm_num

theorem lam_uS_ne_one {ω : FFHeckeCharacter Fq k} {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) {s : ℂ} {σ : ℝ}
    (hσ : ∀ z, ‖ω.ev z‖ * ‖omegaS s z‖ = (norm z : ℝ) ^ σ) (h1 : 1 < σ) :
    ω.ev (piD b₁) * uS Fq s ≠ 1 ∧ (Nat.card Fq : ℂ) * (ω.ev (piD b₁) * uS Fq s) ≠ 1 := by
  have hq1 : (1 : ℝ) < Nat.card Fq := by exact_mod_cast (Finite.one_lt_card (α := Fq))
  have hq0 : (0 : ℝ) < Nat.card Fq := by linarith
  have hn := norm_lam_uS hb hσ
  constructor
  · intro h
    have : ‖ω.ev (piD b₁) * uS Fq s‖ < 1 := by
      rw [hn]; exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
    rw [h, norm_one] at this; exact lt_irrefl _ this
  · intro h
    have : ‖(Nat.card Fq : ℂ) * (ω.ev (piD b₁) * uS Fq s)‖ < 1 := by
      rw [_root_.norm_mul, hn, Complex.norm_natCast, ← Real.rpow_one_add' hq0.le (by linarith)]
      · exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
    rw [h, norm_one] at this; exact lt_irrefl _ this

/-- Off $\omega_0$: if $\omega$ is trivial on the ideles of norm 1 and $\lambda u=1$, then $\omega\omega_s=1$. -/
theorem eq_one_of_lam_uS {ω : FFHeckeCharacter Fq k} (hω : IsNormOneTrivial ω) {b₁ : Divisor Fq k}
    (hb : Divisor.deg b₁ = 1) {s : ℂ} (h : ω.ev (piD b₁) * uS Fq s = 1) (z : FFIdeleGroup Fq k) :
    ω.ev z * omegaS s z = 1 := by
  rw [ev_eq_of_trivial hω hb, omegaS_eq, ← mul_zpow, h, one_zpow]

/-- Off $\omega_1$: if $\omega$ is trivial on the ideles of norm 1 and $q\lambda u=1$, then $\omega\omega_s=\omega_1$. -/
theorem eq_omega1_of_lam_uS {ω : FFHeckeCharacter Fq k} (hω : IsNormOneTrivial ω) {b₁ : Divisor Fq k}
    (hb : Divisor.deg b₁ = 1) {s : ℂ} (h : (Nat.card Fq : ℂ) * (ω.ev (piD b₁) * uS Fq s) = 1)
    (z : FFIdeleGroup Fq k) : ω.ev z * omegaS s z = omegaS 1 z := by
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := Fq); exact_mod_cast this.ne'
  have hu1 : uS Fq 1 = (Nat.card Fq : ℂ)⁻¹ := by rw [uS, Complex.cpow_neg_one]
  have h' : ω.ev (piD b₁) * uS Fq s = uS Fq 1 := by
    rw [hu1]; exact eq_inv_of_mul_eq_one_right h
  rw [ev_eq_of_trivial hω hb, omegaS_eq, omegaS_eq, ← mul_zpow, h']

/-- **Weil, VII.§5 Thm. 2, function fields, every quasicharacter.** Let $\omega$ be a quasicharacter of
$G_k=k_{\mathbb A}^\times/k^\times$, $\Phi$ a Schwartz–Bruhat function on $k_{\mathbb A}$, $\Phi'=q^{1-g}\hat\Phi$ its
Fourier transform for the self-dual measure, $\check\omega=\omega_1\omega^{-1}$, and $\mu$ any Haar measure on
$k_{\mathbb A}^\times$ ($c_\mu=h\,\mu(\prod_v\mathfrak r_v^\times)/(q-1)$, `zetaConst`; $c_\mu=1$ for Weil's measure). There are
meromorphic functions $Z$, $Z'$ on $\mathbb C$ such that
* $Z(s)=Z(\omega\omega_s,\Phi)$ and $Z'(s)=Z(\check\omega\omega_s,\Phi')$ wherever the integrals converge absolutely
  ($\lvert\omega\omega_s\rvert=\omega_\sigma$ with $\sigma>1$);
* away from the $s$ with $\omega\omega_s=\omega_0$ or $\omega\omega_s=\omega_1$, $Z$ is holomorphic at $s$, $Z'$ is
  holomorphic at $-s$, and **$Z(\omega\omega_s,\Phi)=Z(\check\omega\omega_{-s},\Phi')$**, i.e.
  $Z(\omega,\Phi)=Z(\omega_1\omega^{-1},\Phi')$ on the whole space of quasicharacters;
* where $\omega\omega_{s_0}=\omega_0$, $Z(s)+c_\mu\Phi(0)(1-q^{-(s-s_0)})^{-1}$ is holomorphic at $s_0$, and where
  $\omega\omega_{s_0}=\omega_1$, $Z(s)-c_\mu\Phi'(0)(1-q^{-(s-s_0)})^{-1}$ is holomorphic at $s_0$ (simple poles with
  residues $-c_\mu\Phi(0)$ and $c_\mu\Phi'(0)$ in the variable $q^{-(s-s_0)}$). -/
@[kb "weil1973bnt" "Ch. VII, §5, Thm. 2 (p. 121), function fields, every quasicharacter: meromorphic continuation, functional equation Z(ω, Φ) = Z(ω_1 ω^-1, Φ'), poles at ω_0 and ω_1 with residues"]
theorem weil_VII_5_thm2_ff_quasi (hc : IsConstantField Fq k) (hψ₀ : ψ₀ ≠ 1) (μ : Measure (FFIdeleGroup Fq k))
    [μ.IsHaarMeasure] (ω : FFHeckeCharacter Fq k) {Φ : FFAdeleRing Fq k → ℂ}
    (hΦ : FFAdeleRing.IsSchwartzBruhat Φ) :
    ∃ Z Z' : ℂ → ℂ,
      (∀ (s : ℂ) (σ : ℝ), (∀ z, ‖ω.ev z‖ * ‖omegaS s z‖ = (norm z : ℝ) ^ σ) → 1 < σ →
        Integrable (fun z : FFIdeleGroup Fq k => Φ (z : FFAdeleRing Fq k) * ω.ev z * omegaS s z) μ ∧
          zetaQ μ ω Φ s = Z s) ∧
      (∀ (s : ℂ) (σ : ℝ), (∀ z, ‖ω.dual.ev z‖ * ‖omegaS s z‖ = (norm z : ℝ) ^ σ) → 1 < σ →
        Integrable (fun z : FFIdeleGroup Fq k => (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) *
          fourierFF ψ₀ Φ (z : FFAdeleRing Fq k) * ω.dual.ev z * omegaS s z) μ ∧
          zetaQ μ ω.dual (fun x => (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ x) s = Z' s) ∧
      MeromorphicOn Z Set.univ ∧ MeromorphicOn Z' Set.univ ∧
      (∀ s : ℂ, (¬ ∀ z, ω.ev z * omegaS s z = 1) → (¬ ∀ z, ω.ev z * omegaS s z = omegaS 1 z) →
        AnalyticAt ℂ Z s ∧ AnalyticAt ℂ Z' (-s) ∧ Z s = Z' (-s)) ∧
      (∀ s₀ : ℂ, (∀ z, ω.ev z * omegaS s₀ z = 1) →
        AnalyticAt ℂ (fun s => Z s + zetaConst μ * Φ 0 * (1 - uS Fq (s - s₀))⁻¹) s₀) ∧
      (∀ s₀ : ℂ, (∀ z, ω.ev z * omegaS s₀ z = omegaS 1 z) →
        AnalyticAt ℂ (fun s => Z s - zetaConst μ *
          ((Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) * fourierFF ψ₀ Φ 0) * (1 - uS Fq (s - s₀))⁻¹) s₀) := by
  classical
  obtain ⟨b₁, hb⟩ := weil_VII_5_cor5_ff hc
  obtain ⟨a, -, hs, -⟩ := id hΦ
  have hΦh := FFAdeleRing.isSchwartzBruhat_fourierFF ψ₀ hψ₀ hΦ
  obtain ⟨a', -, hs', -⟩ := id hΦh
  set Q : ℂ := (Nat.card Fq : ℂ) ^ (1 - Rep.genusInt Fq k) with hQ
  set Φ' : FFAdeleRing Fq k → ℂ := fun x => Q * fourierFF ψ₀ Φ x with hΦ'
  have hΦ'sb : FFAdeleRing.IsSchwartzBruhat Φ' := hΦh.const_mul Q
  have hsΦ' : ∀ x, x ∉ U a' → Φ' x = 0 := fun x hx => by simp only [hΦ', hs' x hx, mul_zero]
  have hsΦ'' : ∀ x, x ∉ U a → fourierFF ψ₀ Φ' x = 0 := fun x hx => by
    rw [hΦ', fourierFF_const_mul, fourierFF_fourierFF ψ₀ hc hψ₀ hΦ, hs (-x) (fun h => hx (by
      have := (U a).neg_mem h; rwa [neg_neg] at this)), mul_zero, mul_zero]
  set M : ℕ := max (Divisor.deg a).toNat (Divisor.deg a').toNat with hM
  have hMa : Divisor.deg a ≤ M := by rw [hM]; push_cast; omega
  have hMa' : Divisor.deg a' ≤ M := by rw [hM]; push_cast; omega
  -- the dual's polar data
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := Fq); exact_mod_cast this.ne'
  have hlam0 : ω.ev (piD b₁) ≠ 0 := ω.ev_ne_zero _
  have hdx : ∀ s, ω.dual.ev (piD b₁) * uS Fq (-s) = ((Nat.card Fq : ℂ) * (ω.ev (piD b₁) * uS Fq s))⁻¹ :=
    fun s => by rw [ev_dual_piD hb, uS_neg, mul_inv, mul_inv]; ring
  have hdy : ∀ s, (Nat.card Fq : ℂ) * (ω.dual.ev (piD b₁) * uS Fq (-s)) = (ω.ev (piD b₁) * uS Fq s)⁻¹ :=
    fun s => by rw [hdx]; field_simp
  refine ⟨fun s => zetaPF ψ₀ μ ω Φ b₁ M (uS Fq s), fun s => zetaPF ψ₀ μ ω.dual Φ' b₁ M (uS Fq s),
    fun s σ hσ h1 => ?_, fun s σ hσ h1 => ?_, meromorphicOn_zetaPF ψ₀ μ ω Φ b₁ M,
    meromorphicOn_zetaPF ψ₀ μ ω.dual Φ' b₁ M, fun s h0 h1 => ?_,
    fun s₀ h0 => analyticAt_zetaPF_add_pole ψ₀ μ ω Φ hb M h0,
    fun s₀ h1 => analyticAt_zetaPF_sub_pole ψ₀ μ ω Φ hb M h1⟩
  · obtain ⟨hx, hy⟩ := lam_uS_ne_one hb hσ h1
    refine ⟨(hasSum_zetaQ hc μ ω hΦ hσ h1).1, ?_⟩
    rw [zetaQ_eq_zetaRat ψ₀ hc hψ₀ μ ω hΦ hs hs' hb hMa hMa' hσ h1,
      zetaRat_eq_zetaPF ψ₀ μ ω Φ b₁ M (fun _ => hx) (fun _ => hy)]
  · obtain ⟨hx, hy⟩ := lam_uS_ne_one hb hσ h1
    have hint := (hasSum_zetaQ hc μ ω.dual hΦ'sb hσ h1).1
    refine ⟨by simpa only [hΦ'] using hint, ?_⟩
    rw [zetaQ_eq_zetaRat ψ₀ hc hψ₀ μ ω.dual hΦ'sb hsΦ' hsΦ'' hb hMa' hMa hσ h1,
      zetaRat_eq_zetaPF ψ₀ μ ω.dual Φ' b₁ M (fun _ => hx) (fun _ => hy)]
  · have hx : IsNormOneTrivial ω → ω.ev (piD b₁) * uS Fq s ≠ 1 := fun hω h => h0 (eq_one_of_lam_uS hω hb h)
    have hy : IsNormOneTrivial ω → (Nat.card Fq : ℂ) * (ω.ev (piD b₁) * uS Fq s) ≠ 1 := fun hω h =>
      h1 (eq_omega1_of_lam_uS hω hb h)
    have hx' : IsNormOneTrivial ω.dual → ω.dual.ev (piD b₁) * uS Fq (-s) ≠ 1 := fun hω h => by
      rw [hdx, inv_eq_one] at h; exact hy ((isNormOneTrivial_dual_iff ω).1 hω) h
    have hy' : IsNormOneTrivial ω.dual → (Nat.card Fq : ℂ) * (ω.dual.ev (piD b₁) * uS Fq (-s)) ≠ 1 :=
      fun hω h => by
        rw [hdy, inv_eq_one] at h; exact hx ((isNormOneTrivial_dual_iff ω).1 hω) h
    refine ⟨analyticAt_zetaPF ψ₀ μ ω Φ b₁ M hx hy, analyticAt_zetaPF ψ₀ μ ω.dual Φ' b₁ M hx' hy', ?_⟩
    show zetaPF ψ₀ μ ω Φ b₁ M (uS Fq s) = zetaPF ψ₀ μ ω.dual Φ' b₁ M (uS Fq (-s))
    rw [← zetaRat_eq_zetaPF ψ₀ μ ω Φ b₁ M hx hy, ← zetaRat_eq_zetaPF ψ₀ μ ω.dual Φ' b₁ M hx' hy',
      zetaRat_fe ψ₀ hc hψ₀ μ ω hΦ hs' hb M (uS_ne_zero s) hx hy, uS_neg]

end FFIdeleGroup

end

end NumberFieldKB.WeilBNT.FF
