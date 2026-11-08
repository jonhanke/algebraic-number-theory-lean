import NumberFieldKB.WeilBNT.FunctionField.HeckeLFF
import NumberFieldKB.WeilBNT.FunctionField.AdeleVolume
import NumberFieldKB.WeilBNT.FunctionField.SchmidtP
import NumberFieldKB.WeilBNT.FunctionField.EulerFF
import NumberFieldKB.WeilBNT.FunctionField.RayCount

/-!
# L-series of ramified Hecke characters of a function field (Weil VII.§7, Thm. 6)

Let $\omega$ be a Hecke character of the function field $k$ with conductor $\mathfrak f=\sum_vf(v)\,v$
(`FFHeckeCharacter.conductor`).

* `eq_one_of_forall_mem_unitFiltration`: $\omega$ is trivial on the ideles $z$ with $z_v\in U_v^{(f(v))}$ for every
  $v$.
* `divIdele`: the idele $\prod_v\pi_v^{a(v)}$ attached to a divisor (a fixed prime element $\pi_v$ of $k_v$ at each
  place), a morphism with $\operatorname{div}=\mathrm{id}$; `rayChar`: the character
  $\chi_\omega(\mathfrak a)=\omega(\prod_v\pi_v^{a(v)})$ of the divisor group. On divisors prime to $\mathfrak f$ it does
  not depend on the choice of the $\pi_v$ (`rayChar_eq`).
* Ray classes modulo $\mathfrak f$: `CongOne f ξ` ($\xi\equiv1\bmod\mathfrak f$) and `IsRayPrincipal f d`
  ($d=\operatorname{div}\xi$ with $\xi\equiv1\bmod\mathfrak f$); $\chi_\omega$ is trivial on ray-principal divisors
  (`rayChar_rayPrincipal`), so it is a character of the ray class group modulo $\mathfrak f$.
* `lSeriesF`: $L(u,\omega)=\sum_{\mathfrak a\succ0,\ (\mathfrak a,\mathfrak f)=1}\chi_\omega(\mathfrak a)u^{\deg\mathfrak a}$;
  for $\mathfrak f=0$ it is the L-series of `HeckeLFF.lean` (`lSeriesF_eq_lSeries`).
* **`weil_VII_7_thm6_degree`** (Weil VII.§7, Thm. 6, degree bound): if $\mathbb F_q$ is the field of constants and
  $\omega$ is not principal, $L(u,\omega)$ is a polynomial of degree at most $2g-2+\deg\mathfrak f$.
* **`weil_VII_7_euler`** (Weil VII.§7, (11)): $L(u,\omega)=\prod_{v\notin\operatorname{supp}\mathfrak f}
  (1-\omega(\pi_v)u^{\deg v})^{-1}$ in $\mathbb C[[u]]$.

Proof of the bound for $\mathfrak f\ne0$: for $\deg\mathfrak b-\deg\mathfrak f>2g-2$ and $\mathfrak b$ prime to
$\mathfrak f$, the effective divisors in the ray class of $\mathfrak b$ correspond to the $\xi\in L(\mathfrak b)$ with
$\xi\equiv1\bmod\mathfrak f$; these form a coset of $L(\mathfrak b-\mathfrak f)$ (nonempty by the adelic form of
Riemann–Roch, VI Cor. 3 of Thm. 2), so every ray class of degree $n$ contains $q^{n-\deg\mathfrak f-g+1}$ effective
divisors. A ramified place gives, by approximation, a divisor $\mathfrak d_0$ of degree $0$ prime to $\mathfrak f$ with
$\chi_\omega(\mathfrak d_0)\ne1$, and the double count of `HeckeLFF.lean` shows that the coefficient of $u^n$ vanishes.
-/

open scoped WithZero NNReal PowerSeries.WithPiTopology
open Valuation Filter

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace FFHeckeCharacter

/-! ### Triviality on $\prod_vU_v^{(f(v))}$ -/

/-- The inclusion $\prod_vU_v^{(n_v)}\to\prod_v\mathfrak r_v^\times$. -/
def filtIncl (n : Place Fq k → ℕ) :
    (∀ v : Place Fq k, unitFiltration v (n v)) →* (∀ v : Place Fq k, unitFiltration v 0) :=
  MonoidHom.pi fun v => (Subgroup.inclusion (unitFiltration_antitone (Nat.zero_le (n v)))).comp
    (Pi.evalMonoidHom (fun v : Place Fq k => ↥(unitFiltration v (n v))) v)

theorem continuous_filtIncl (n : Place Fq k → ℕ) : Continuous (filtIncl (Fq := Fq) (k := k) n) :=
  continuous_pi fun v => by
    change Continuous fun x : (∀ v : Place Fq k, unitFiltration v (n v)) =>
      (⟨((x v : unitFiltration v (n v)) : v.Completionˣ), unitFiltration_antitone (Nat.zero_le (n v)) (x v).2⟩ :
        unitFiltration v 0)
    exact (continuous_subtype_val.comp (continuous_apply v)).subtype_mk _

/-- **$\omega$ is trivial on $\prod_vU_v^{(f(v))}$**: if every component of $z$ lies in $U_v^{(f(v))}$, then
$\omega(z)=1$. -/
theorem eq_one_of_forall_mem_unitFiltration (ω : FFHeckeCharacter Fq k) (z : FFIdeleGroup Fq k)
    (hz : ∀ v, Valued.v (FFIdeleGroup.comp z v) = 1 ∧
      Valued.v (FFIdeleGroup.comp z v - 1) ≤ WithZero.exp (-(ω.conductorExponent v : ℤ))) :
    ω (QuotientGroup.mk z) = 1 := by
  classical
  set n := ω.conductorExponent with hn
  set F : (∀ v : Place Fq k, unitFiltration v (n v)) →* ℂˣ := (ω : FFIdeleClassGroup Fq k →* ℂˣ).comp
      ((QuotientGroup.mk' _).comp (piUnitsIdele.comp (filtIncl n))) with hF
  have hcont : Continuous F :=
    (map_continuous ω).comp (QuotientGroup.continuous_mk.comp
      (continuous_piUnitsIdele.comp (continuous_filtIncl n)))
  have h1 : F = 1 := eq_one_of_continuous_pi (G := fun v : Place Fq k => ↥(unitFiltration v (n v))) F hcont
    fun v u => by
      have hm : filtIncl n (Pi.mulSingle v u) =
          Pi.mulSingle v (Subgroup.inclusion (unitFiltration_antitone (Nat.zero_le (n v))) u) := by
        funext w
        by_cases hw : w = v
        · subst hw; simp [filtIncl]
        · simp [filtIncl, Pi.mulSingle_eq_of_ne hw]
      change ω (QuotientGroup.mk (piUnitsIdele (filtIncl n (Pi.mulSingle v u)))) = 1
      rw [hm, piUnitsIdele_mulSingle]
      exact ω.component_eq_one_of_mem u.2
  have hzu : ∀ v, FFIdeleGroup.comp z v ≠ 0 := FFIdeleGroup.comp_ne_zero z
  let x : ∀ v : Place Fq k, unitFiltration v (n v) := fun v =>
    ⟨Units.mk0 (FFIdeleGroup.comp z v) (hzu v), by simpa [mem_unitFiltration] using hz v⟩
  have hx : piUnitsIdele (filtIncl n x) = z := by
    refine Units.ext ?_
    ext v
    rfl
  have := DFunLike.congr_fun h1 x
  rw [hF] at this
  change ω (QuotientGroup.mk (piUnitsIdele (filtIncl n x))) = 1 at this
  rwa [hx] at this

end FFHeckeCharacter

/-! ### The idele of a divisor and the ray class character -/

namespace FFIdeleGroup

/-- The $v$-component $k_{\mathbb A}^\times\to k_v^\times$ as a morphism. -/
def compU (w : Place Fq k) : FFIdeleGroup Fq k →* w.Completionˣ where
  toFun z := Units.mk0 (comp z w) (comp_ne_zero z w)
  map_one' := Units.ext (comp_one w)
  map_mul' z z' := Units.ext (comp_mul z z' w)

@[simp] theorem coe_compU (w : Place Fq k) (z : FFIdeleGroup Fq k) :
    (compU w z : w.Completion) = comp z w := rfl

open Classical in
theorem compU_single (v w : Place Fq k) (x : v.Completionˣ) :
    compU w (single v x) = if h : v = w then h ▸ x else 1 := by
  by_cases h : v = w
  · subst h; exact Units.ext (by simp [comp_single_self])
  · rw [dite_eq_right_iff.mpr fun h0 => absurd h0 h]; exact Units.ext (by simp [comp_single_ne (Ne.symm h)])

/-- The fixed prime element $\pi_v$ of $k_v$ (`FFAdeleRing.uniC`), as a unit. -/
def uniU (v : Place Fq k) : v.Completionˣ := Units.mk0 (FFAdeleRing.uniC v) (FFAdeleRing.uniC_ne_zero v)

/-- **The idele of a divisor**, $\mathfrak a\mapsto\prod_v\pi_v^{a(v)}$ (a fixed prime element $\pi_v$ at each
place). -/
def divIdele : Multiplicative (Divisor Fq k) →* FFIdeleGroup Fq k where
  toFun a := (Multiplicative.toAdd a).prod fun v n => single v (uniU v) ^ n
  map_one' := Finsupp.prod_zero_index
  map_mul' _ _ := Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)

theorem compU_divIdele (a : Divisor Fq k) (w : Place Fq k) :
    compU w (divIdele (Multiplicative.ofAdd a)) = uniU w ^ a w := by
  classical
  change compU w (a.prod fun v n => single v (uniU v) ^ n) = _
  rw [Finsupp.prod, map_prod]
  simp_rw [map_zpow, compU_single]
  by_cases hw : w ∈ a.support
  · rw [Finset.prod_eq_single w]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hw h
  · rw [Finset.prod_eq_one]
    · rw [Finsupp.notMem_support_iff.mp hw, zpow_zero]
    · intro b hb
      have : b ≠ w := fun e => hw (e ▸ hb)
      simp [this]

theorem comp_divIdele (a : Divisor Fq k) (w : Place Fq k) :
    comp (divIdele (Multiplicative.ofAdd a)) w = FFAdeleRing.uniC w ^ a w := by
  rw [← coe_compU, compU_divIdele, Units.val_zpow_eq_zpow_val]
  rfl

theorem valued_comp_divIdele (a : Divisor Fq k) (w : Place Fq k) :
    Valued.v (comp (divIdele (Multiplicative.ofAdd a)) w) = WithZero.exp (-a w) := by
  rw [comp_divIdele, FFAdeleRing.valued_zpow (FFAdeleRing.valued_uniC w)]

theorem div_divIdele (a : Divisor Fq k) : div (divIdele (Multiplicative.ofAdd a)) = a := by
  ext w
  rw [div_apply, Place.ordC, valued_comp_divIdele, WithZero.log_exp, neg_neg]

end FFIdeleGroup

/-- An element of $k_v$ with $v(x-1)\le e^{-m}$, $m\ge1$, is a unit. -/
theorem Place.valued_eq_one_of_sub_one {v : Place Fq k} {x : v.Completion} {m : ℤ} (hm : 0 < m)
    (h : Valued.v (x - 1) ≤ WithZero.exp (-m)) : Valued.v x = 1 := by
  have hlt : Valued.v (x - 1) < Valued.v (1 : v.Completion) := by
    rw [map_one]
    exact lt_of_le_of_lt h (by rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega))
  have := Valuation.map_add_eq_of_lt_right (Valued.v : Valuation v.Completion ℤᵐ⁰) hlt
  rwa [sub_add_cancel, map_one] at this

namespace FFHeckeCharacter

/-- **The ray class character** $\chi_\omega(\mathfrak a)=\omega(\prod_v\pi_v^{a(v)})$ of the divisor group. On
divisors prime to the conductor it does not depend on the prime elements (`rayChar_eq`). -/
def rayChar (ω : FFHeckeCharacter Fq k) : Multiplicative (Divisor Fq k) →* ℂˣ :=
  (ω : FFIdeleClassGroup Fq k →* ℂˣ).comp ((QuotientGroup.mk' _).comp FFIdeleGroup.divIdele)

theorem rayChar_apply (ω : FFHeckeCharacter Fq k) (a : Multiplicative (Divisor Fq k)) :
    ω.rayChar a = ω (QuotientGroup.mk (FFIdeleGroup.divIdele a)) := rfl

/-- For an idele $z$ with $z_v\equiv1\bmod\mathfrak p_v^{f(v)}$ at the ramified places, $\omega(z)=
\chi_\omega(\operatorname{div}z)$. -/
theorem rayChar_eq (ω : FFHeckeCharacter Fq k) (z : FFIdeleGroup Fq k)
    (hz : ∀ v, 0 < ω.conductor v →
      Valued.v (FFIdeleGroup.comp z v - 1) ≤ WithZero.exp (-ω.conductor v)) :
    ω (QuotientGroup.mk z) = ω.rayChar (Multiplicative.ofAdd (FFIdeleGroup.div z)) := by
  set a := FFIdeleGroup.div z with ha
  set w := z * (FFIdeleGroup.divIdele (Multiplicative.ofAdd a))⁻¹ with hw
  have hcomp : ∀ v, FFIdeleGroup.comp w v =
      FFIdeleGroup.comp z v * ((FFAdeleRing.uniC v ^ a v)⁻¹) := by
    intro v
    rw [← FFIdeleGroup.coe_compU, hw, map_mul, _root_.map_inv, FFIdeleGroup.compU_divIdele, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val]
    rfl
  have hzv : ∀ v, Valued.v (FFIdeleGroup.comp z v) = WithZero.exp (-a v) := fun v => by
    rw [Place.valued_eq_exp_neg_ordC v (FFIdeleGroup.comp_ne_zero z v), ha, FFIdeleGroup.div_apply]
  have hwv : ∀ v, Valued.v (FFIdeleGroup.comp w v) = 1 := fun v => by
    rw [hcomp, map_mul, map_inv₀, FFAdeleRing.valued_zpow (FFAdeleRing.valued_uniC v), hzv,
      ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have h1 : ω (QuotientGroup.mk w) = 1 := by
    refine ω.eq_one_of_forall_mem_unitFiltration w fun v => ⟨hwv v, ?_⟩
    rcases Nat.eq_zero_or_pos (ω.conductorExponent v) with h0 | hpos
    · rw [h0, Nat.cast_zero, neg_zero, WithZero.exp_zero, sub_eq_add_neg]
      exact Valuation.map_add_le _ (hwv v).le (by rw [Valuation.map_neg, map_one])
    · have hf : 0 < ω.conductor v := by rw [conductor_apply]; exact_mod_cast hpos
      have hzv1 := Place.valued_eq_one_of_sub_one hf (hz v hf)
      have hav : a v = 0 := by
        have := hzv v
        rw [hzv1, ← WithZero.exp_zero, WithZero.exp_inj] at this
        omega
      rw [hcomp, hav, zpow_zero, inv_one, mul_one]
      have := hz v hf
      rwa [conductor_apply] at this
  have : z = w * FFIdeleGroup.divIdele (Multiplicative.ofAdd a) := by rw [hw, inv_mul_cancel_right]
  rw [this, QuotientGroup.mk_mul, map_mul, h1, one_mul]
  rfl

/-! ### Ray classes modulo $\mathfrak f$ (`CongOne`, `IsRayPrincipal`: `RayCount.lean`) -/

/-- $\chi_\omega$ is trivial on divisors that are ray-principal modulo the conductor: it is a character of the ray class
group modulo $\mathfrak f$. -/
theorem rayChar_rayPrincipal (ω : FFHeckeCharacter Fq k) {d : Divisor Fq k}
    (hd : IsRayPrincipal ω.conductor d) : ω.rayChar (Multiplicative.ofAdd d) = 1 := by
  obtain ⟨ξ, hξ, rfl⟩ := hd
  have h := ω.rayChar_eq (FFIdeleGroup.principal (Fq := Fq) ξ) fun v hv => by
    rw [FFIdeleGroup.comp_principal, ← map_one v.toCompletion, ← _root_.map_sub, Place.valued_toCompletion]
    exact hξ v hv
  rw [FFIdeleGroup.div_principal] at h
  rw [← h]
  have : (QuotientGroup.mk (FFIdeleGroup.principal (Fq := Fq) ξ) : FFIdeleClassGroup Fq k) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨ξ, rfl⟩
  rw [this, map_one]

/-- **The L-series** $L(u,\omega)=\sum_{\mathfrak a\succ0,\ (\mathfrak a,\mathfrak f)=1}\chi_\omega(\mathfrak a)
u^{\deg\mathfrak a}$ of a Hecke character of conductor $\mathfrak f$, in $u=q^{-s}$: the sum over effective divisors
supported on the unramified places. -/
def lSeriesF (ω : FFHeckeCharacter Fq k) : PowerSeries ℂ :=
  divisorSeries ω.rayChar {v | ω.conductor v = 0}

/-- At an unramified place, $\chi_\omega(v)=\omega_v(\pi)$ for every prime element $\pi$ of $k_v$. -/
theorem rayChar_single (ω : FFHeckeCharacter Fq k) {v : Place Fq k} (hv : ω.conductor v = 0)
    (x : v.Completionˣ) (hx : Valued.v (x : v.Completion) = WithZero.exp (-1)) :
    ω.rayChar (Multiplicative.ofAdd (Finsupp.single v 1)) = ω.component v x := by
  have h := ω.rayChar_eq (FFIdeleGroup.single v x) fun w hw => by
    have hwv : w ≠ v := fun e => by rw [e, hv] at hw; exact lt_irrefl _ hw
    rw [FFIdeleGroup.comp_single_ne hwv, sub_self, map_zero]
    exact zero_le'
  rw [FFIdeleGroup.div_single] at h
  have : v.ordC (x : v.Completion) = 1 := by rw [Place.ordC, hx, WithZero.log_exp, neg_neg]
  rw [this] at h
  rw [← h, component_apply]

/-- **The Euler product** of $L(u,\omega)$ (Weil VII.§7, (11), in $u=q^{-s}$): $L(u,\omega)=
\prod_{v\notin\operatorname{supp}\mathfrak f}(1-\chi_\omega(v)u^{\deg v})^{-1}$, a product of formal power series
converging in the coefficientwise topology; $\chi_\omega(v)=\omega_v(\pi_v)$ (`rayChar_single`). -/
@[kb "weil1973bnt" "Ch. VII, §7, Def. (11) (p. 133), function fields: Euler product of L(u, omega) in u = q^-s"]
theorem weil_VII_7_euler (ω : FFHeckeCharacter Fq k) :
    HasProd (fun v : {v : Place Fq k | ω.conductor v = 0} =>
      eulerFactor ((ω.rayChar (Multiplicative.ofAdd (Finsupp.single (v : Place Fq k) 1)) : ℂˣ) : ℂ)
        (v : Place Fq k).degree) ω.lSeriesF :=
  hasProd_eulerFactor ω.rayChar _

/-- For conductor $0$ the L-series is that of `HeckeLFF.lean`. -/
theorem lSeriesF_eq_lSeries (ω : FFHeckeCharacter Fq k) (hω : ∀ v, ω.IsUnramifiedAt v) :
    ω.lSeriesF = ω.lSeries hω := by
  ext n
  rw [lSeriesF, divisorSeries, lSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  have hT : ∀ a ∈ (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) (n : ℤ)).toFinset,
      ∀ v ∈ a.support, v ∈ {v : Place Fq k | ω.conductor v = 0} :=
    fun a _ v _ => (ω.conductor_apply_eq_zero_iff v).mpr (hω v)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [if_pos (hT a ha), rayChar_apply, ← ω.divChar_div hω, FFIdeleGroup.div_divIdele]

open Classical in
/-- $\chi_\omega(\operatorname{div}\xi)=\omega_v(u)^{-1}$ if $\xi\equiv u\bmod\mathfrak p_v^{f(v)}$ at one ramified place
$v$ and $\xi\equiv1\bmod\mathfrak f$ at the others. -/
theorem rayChar_div_of_approx (ω : FFHeckeCharacter Fq k) {v : Place Fq k} (hv : 0 < ω.conductor v)
    (u : v.Completionˣ) (hu : Valued.v (u : v.Completion) = 1) (ξ : kˣ)
    (hξv : Valued.v (v.toCompletion (ξ : k) - u) ≤ WithZero.exp (-ω.conductor v))
    (hξw : ∀ w, w ≠ v → 0 < ω.conductor w → w.valuation ((ξ : k) - 1) ≤ WithZero.exp (-ω.conductor w)) :
    ω.rayChar (Multiplicative.ofAdd (Divisor.div ξ)) = (ω.component v u)⁻¹ := by
  have hξv0 : v.toCompletion (ξ : k) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ v.toCompletion.injective]; exact ξ.ne_zero
  set y : v.Completionˣ := Units.mk0 _ hξv0 with hy
  -- `y u⁻¹ ∈ U^{(f(v))}`
  have hyu : Valued.v (((y * u⁻¹ : v.Completionˣ) : v.Completion) - 1) ≤ WithZero.exp (-ω.conductor v) := by
    have e : ((y * u⁻¹ : v.Completionˣ) : v.Completion) - 1 =
        (v.toCompletion (ξ : k) - u) * ((u⁻¹ : v.Completionˣ) : v.Completion) := by
      rw [Units.val_mul, sub_mul, Units.mul_inv]; rfl
    rw [e, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one, mul_one]
    exact hξv
  have hyu1 : Valued.v ((y * u⁻¹ : v.Completionˣ) : v.Completion) = 1 :=
    Place.valued_eq_one_of_sub_one hv hyu
  have hy1 : Valued.v (y : v.Completion) = 1 := by
    have : (y : v.Completion) = ((y * u⁻¹ : v.Completionˣ) : v.Completion) * u := by
      rw [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this, map_mul, hyu1, hu, one_mul]
  have hcomp : ω.component v y = ω.component v u := by
    have h1 : ω.component v (y * u⁻¹) = 1 := ω.component_eq_one_of_mem (by
      rw [mem_unitFiltration]
      refine ⟨hyu1, ?_⟩
      have := hyu
      rwa [conductor_apply] at this)
    rw [map_mul, _root_.map_inv, mul_inv_eq_one] at h1
    exact h1
  set z := FFIdeleGroup.principal (Fq := Fq) ξ * (FFIdeleGroup.single v y)⁻¹ with hz
  have hcz : ∀ w, FFIdeleGroup.comp z w = if w = v then 1 else w.toCompletion (ξ : k) := by
    intro w
    rw [← FFIdeleGroup.coe_compU, hz, map_mul, _root_.map_inv, FFIdeleGroup.compU_single]
    by_cases hw : w = v
    · subst hw
      rw [dif_pos rfl, if_pos rfl]
      have hp : FFIdeleGroup.compU w (FFIdeleGroup.principal (Fq := Fq) ξ) = y := Units.ext rfl
      rw [hp, mul_inv_cancel, Units.val_one]
    · rw [if_neg hw, dif_neg (Ne.symm hw), inv_one, mul_one]
      rfl
  have h := ω.rayChar_eq z fun w hw => by
    rw [hcz]
    by_cases hwv : w = v
    · rw [if_pos hwv, sub_self, map_zero]; exact zero_le'
    · rw [if_neg hwv, ← map_one w.toCompletion, ← _root_.map_sub, Place.valued_toCompletion]
      exact hξw w hwv hw
  have hdiv : FFIdeleGroup.div z = Divisor.div ξ := by
    ext w
    rw [FFIdeleGroup.div_apply, hcz]
    by_cases hwv : w = v
    · subst hwv
      rw [if_pos rfl, Divisor.div_apply, ← Place.ordC_toCompletion]
      have : w.ordC (w.toCompletion (ξ : k)) = 0 := by
        have h1 : Valued.v (w.toCompletion (ξ : k)) = 1 := hy1
        rw [Place.ordC, h1]; simp
      rw [this, Place.ordC]; simp
    · rw [if_neg hwv, Divisor.div_apply, Place.ordC_toCompletion]
  rw [hdiv] at h
  rw [← h, hz, QuotientGroup.mk_mul, map_mul, QuotientGroup.mk_inv, _root_.map_inv]
  have : (QuotientGroup.mk (FFIdeleGroup.principal (Fq := Fq) ξ) : FFIdeleClassGroup Fq k) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨ξ, rfl⟩
  rw [this, map_one, one_mul, ← component_apply, hcomp]

/-- **A ramified character is nontrivial on a divisor class of degree $0$ prime to $\mathfrak f$**: if
$\mathfrak f\ne0$ there is a divisor $\mathfrak d_0$ of degree $0$ prime to $\mathfrak f$ with
$\chi_\omega(\mathfrak d_0)\ne1$ (approximation at the ramified places, VI Cor. 3 of Thm. 2). -/
theorem exists_deg_zero_rayChar_ne_one (hc : IsConstantField Fq k) (ω : FFHeckeCharacter Fq k)
    (hf : ω.conductor ≠ 0) :
    ∃ d : Divisor Fq k, Divisor.deg d = 0 ∧ (∀ v, 0 < ω.conductor v → d v = 0) ∧
      ω.rayChar (Multiplicative.ofAdd d) ≠ 1 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, ω.conductor v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hf (Finsupp.ext hh)
  have hvpos : 0 < ω.conductor v := lt_of_le_of_ne (by simp) (Ne.symm hv)
  have hexp : 0 < ω.conductorExponent v := by
    have := hvpos; rw [conductor_apply] at this; exact_mod_cast this
  -- a unit in `U^{(f(v)-1)}` on which `ω_v` is nontrivial
  obtain ⟨u, hu, hωu⟩ : ∃ u ∈ unitFiltration v (ω.conductorExponent v - 1), ω.component v u ≠ 1 := by
    by_contra hh
    push_neg at hh
    have := (ω.conductorExponent_le_iff v (ω.conductorExponent v - 1)).mpr hh
    omega
  have hu1 : Valued.v (u : v.Completion) = 1 := hu.1
  -- approximation: `ξ ≡ u` at `v`, `ξ ≡ 1` at the other ramified places
  obtain ⟨a₁, ha₁, ha₁P⟩ := weil_VII_5_cor5_P hc ω.conductor.support
  have hg0 := genusInt_nonneg hc
  have hdf : 0 ≤ Divisor.deg ω.conductor := Divisor.deg_nonneg ω.conductor_nonneg
  set N : ℤ := 2 * Rep.genusInt Fq k + Divisor.deg ω.conductor with hN
  set a : Divisor Fq k := N • a₁ - ω.conductor with ha
  have hdeg : 2 * Rep.genusInt Fq k - 2 < Divisor.deg a := by
    rw [ha, _root_.map_sub, map_zsmul, ha₁, smul_eq_mul, mul_one]; omega
  set x : FFAdeleRing Fq k := FFAdeleRing.diag 1 + FFAdeleRing.adeleSingle v ((u : v.Completion) - 1) with hx
  obtain ⟨ξ, hξ⟩ := FFAdeleRing.weil_VI_2_cor3_adelic hc hdeg x
  rw [FFAdeleRing.mem_U_iff] at hξ
  have haw : ∀ w, 0 < ω.conductor w → a w = -ω.conductor w := fun w hw => by
    have : a₁ w = 0 := ha₁P w (Finsupp.mem_support_iff.mpr hw.ne')
    simp [ha, this]
  have hξv : Valued.v (v.toCompletion ξ - u) ≤ WithZero.exp (-ω.conductor v) := by
    have h := hξ v
    rw [haw v hvpos] at h
    have e : (x - FFAdeleRing.diag ξ : FFAdeleRing Fq k) v = -(v.toCompletion ξ - u) := by
      show (FFAdeleRing.diag 1 : FFAdeleRing Fq k) v + FFAdeleRing.adeleSingle v ((u : v.Completion) - 1) v -
        (FFAdeleRing.diag ξ : FFAdeleRing Fq k) v = _
      rw [FFAdeleRing.adeleSingle_same]
      show v.toCompletion 1 + ((u : v.Completion) - 1) - v.toCompletion ξ = _
      rw [map_one]; ring
    rwa [e, Valuation.map_neg] at h
  have hξw : ∀ w, w ≠ v → 0 < ω.conductor w → w.valuation (ξ - 1) ≤ WithZero.exp (-ω.conductor w) := by
    intro w hwv hw
    have h := hξ w
    rw [haw w hw] at h
    have e : (x - FFAdeleRing.diag ξ : FFAdeleRing Fq k) w = -(w.toCompletion (ξ - 1)) := by
      show (FFAdeleRing.diag 1 : FFAdeleRing Fq k) w + FFAdeleRing.adeleSingle v ((u : v.Completion) - 1) w -
        (FFAdeleRing.diag ξ : FFAdeleRing Fq k) w = _
      rw [FFAdeleRing.adeleSingle_ne _ _ hwv]
      show w.toCompletion 1 + 0 - w.toCompletion ξ = _
      rw [_root_.map_sub, map_one]; ring
    rwa [e, Valuation.map_neg, Place.valued_toCompletion] at h
  -- `ξ` is a unit at `v`
  have hξv1 : Valued.v (v.toCompletion ξ) = 1 := by
    have hlt : Valued.v (v.toCompletion ξ - u) < Valued.v (u : v.Completion) := by
      rw [hu1]
      exact lt_of_le_of_lt hξv (by rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega))
    have := Valuation.map_add_eq_of_lt_right (Valued.v : Valuation v.Completion ℤᵐ⁰) hlt
    rwa [sub_add_cancel, hu1] at this
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hξv1
    exact zero_ne_one hξv1
  set ξu : kˣ := Units.mk0 ξ hξ0
  refine ⟨Divisor.div ξu, Divisor.deg_div_eq_zero ξu, fun w hw => ?_, ?_⟩
  · rw [Divisor.div_apply]
    by_cases hwv : w = v
    · subst hwv
      rw [← Place.ordC_toCompletion, Place.ordC]
      have : Valued.v (w.toCompletion (ξu : k)) = 1 := hξv1
      rw [this]; simp
    · have h1 := Place.valued_eq_one_of_sub_one (v := w) (x := w.toCompletion ξ) hw (by
        rw [← map_one w.toCompletion, ← _root_.map_sub, Place.valued_toCompletion]; exact hξw w hwv hw)
      rw [← Place.ordC_toCompletion, Place.ordC]
      have : Valued.v (w.toCompletion (ξu : k)) = 1 := h1
      rw [this]; simp
  · rw [ω.rayChar_div_of_approx hvpos u hu1 ξu hξv hξw]
    exact inv_ne_one.mpr hωu

/-- A divisor that is ray-principal modulo $\mathfrak f$ has degree $0$ and is prime to $\mathfrak f$. -/
theorem _root_.NumberFieldKB.WeilBNT.FF.IsRayPrincipal.deg_eq_zero {f d : Divisor Fq k}
    (h : IsRayPrincipal f d) : Divisor.deg d = 0 ∧ ∀ v, 0 < f v → d v = 0 := by
  obtain ⟨ξ, hξ, rfl⟩ := h
  exact ⟨Divisor.deg_div_eq_zero ξ, fun v hv => by
    rw [Divisor.div_apply]; exact Divisor.ord_eq_zero_of_valuation_eq_one v (hξ.valuation_eq_one hv)⟩

open Classical in
/-- The number of effective divisors of degree $n$ prime to $\mathfrak f$ in the ray class of $\mathfrak c$ is
$q^{n-\deg\mathfrak f-g+1}$ when $n-\deg\mathfrak f>2g-2$. -/
theorem card_filter_rayClass (hc : IsConstantField Fq k) {f c : Divisor Fq k} (hf : 0 ≤ f) (hf0 : f ≠ 0)
    {n : ℕ} (hn : 2 * Rep.genusInt Fq k - 2 + Divisor.deg f < n) (hcn : Divisor.deg c = n)
    (hcf : ∀ v, 0 < f v → c v = 0) (A : Finset (Divisor Fq k))
    (hA : ∀ a, a ∈ A ↔ (0 ≤ a ∧ Divisor.deg a = n) ∧ ∀ v, 0 < f v → a v = 0) :
    (A.filter (fun a' => IsRayPrincipal f (a' - c))).card =
      Nat.card Fq ^ ((n : ℤ) - Divisor.deg f - Rep.genusInt Fq k + 1).toNat := by
  have hdeg : 2 * Rep.genusInt Fq k - 2 < Divisor.deg (c - f) := by rw [_root_.map_sub]; omega
  have hell := weil_VI_2_cor2 hc hdeg
  rw [_root_.map_sub, hcn] at hell
  have hE : (c - f).ell = ((n : ℤ) - Divisor.deg f - Rep.genusInt Fq k + 1).toNat := by omega
  rw [← hE, ← card_rayClass_effective hc hf hf0 hcf hdeg, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
  rw [Finset.mem_filter, hA]
  constructor
  · rintro ⟨⟨⟨h0, _⟩, _⟩, h⟩
    exact ⟨h0, h⟩
  · rintro ⟨h0, h⟩
    obtain ⟨hd, hp⟩ := h.deg_eq_zero
    refine ⟨⟨⟨h0, ?_⟩, fun v hv => ?_⟩, h⟩
    · rw [_root_.map_sub, hcn] at hd; omega
    · have := hp v hv
      rw [Finsupp.sub_apply, hcf v hv] at this
      omega

/-- The coefficient of $u^n$ in $L(u,\omega)$ is $\sum\chi_\omega(\mathfrak a)$ over the effective divisors of degree
$n$ prime to $\mathfrak f$ (given as any finset with these members). -/
theorem coeff_lSeriesF_eq_sum (ω : FFHeckeCharacter Fq k) (n : ℕ) (A : Finset (Divisor Fq k))
    (hA : ∀ a, a ∈ A ↔ (0 ≤ a ∧ Divisor.deg a = n) ∧ ∀ v, 0 < ω.conductor v → a v = 0) :
    PowerSeries.coeff n ω.lSeriesF = ∑ a ∈ A, ((ω.rayChar (Multiplicative.ofAdd a) : ℂˣ) : ℂ) := by
  have hP : ∀ a : Divisor Fq k, (∀ v ∈ a.support, v ∈ {v : Place Fq k | ω.conductor v = 0}) ↔
      ∀ v, 0 < ω.conductor v → a v = 0 := fun a => by
    refine ⟨fun h v hv => ?_, fun h v hv => ?_⟩
    · by_contra hav
      exact absurd (h v (Finsupp.mem_support_iff.mpr hav)) hv.ne'
    · by_contra hfv
      have hv' : 0 < ω.conductor v := lt_of_le_of_ne (by simp) (Ne.symm hfv)
      exact Finsupp.mem_support_iff.mp hv (h v hv')
  have hAS : A ⊆ (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) (n : ℤ)).toFinset := fun a ha => by
    rw [Set.Finite.mem_toFinset]; exact ((hA a).mp ha).1
  rw [lSeriesF, divisorSeries, PowerSeries.coeff_mk, Finset.sum_filter]
  refine (Finset.sum_subset hAS ?_).symm.trans (Finset.sum_congr rfl fun a ha => ?_)
  · intro a haS haA
    rw [Set.Finite.mem_toFinset] at haS
    split_ifs with h
    · exact absurd ((hA a).mpr ⟨haS, (hP a).mp h⟩) haA
    · rfl
  · split_ifs with h
    · rfl
    · exact absurd ((hP a).mpr ((hA a).mp ha).2) h

/-- The coefficients of $L(u,\omega)$ vanish in degrees $n>2g-2+\deg\mathfrak f$ for ramified $\omega$. -/
theorem coeff_lSeriesF_eq_zero (hc : IsConstantField Fq k) (ω : FFHeckeCharacter Fq k)
    (hf : ω.conductor ≠ 0) (n : ℕ) (hn : 2 * Rep.genusInt Fq k - 2 + Divisor.deg ω.conductor < n) :
    PowerSeries.coeff n ω.lSeriesF = 0 := by
  classical
  obtain ⟨d₀, hd₀, hd₀f, hχ⟩ := exists_deg_zero_rayChar_ne_one hc ω hf
  have hf0 : 0 ≤ ω.conductor := ω.conductor_nonneg
  set A := (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) (n : ℤ)).toFinset.filter
      (fun a => ∀ v, 0 < ω.conductor v → a v = 0) with hA
  have hmemA : ∀ a, a ∈ A ↔ (0 ≤ a ∧ Divisor.deg a = n) ∧ ∀ v, 0 < ω.conductor v → a v = 0 := by
    intro a
    rw [hA, Finset.mem_filter, Set.Finite.mem_toFinset]
    rfl
  set E := Nat.card Fq ^ ((n : ℤ) - Divisor.deg ω.conductor - Rep.genusInt Fq k + 1).toNat with hE
  have hcount : ∀ c, Divisor.deg c = n → (∀ v, 0 < ω.conductor v → c v = 0) →
      (A.filter fun a' => IsRayPrincipal ω.conductor (a' - c)).card = E :=
    fun c hcn hcf => card_filter_rayClass hc hf0 hf hn hcn hcf A hmemA
  set χ : Divisor Fq k → ℂ := fun a => ((ω.rayChar (Multiplicative.ofAdd a) : ℂˣ) : ℂ) with hχdef
  have hP : ∀ a a' : Divisor Fq k, IsRayPrincipal ω.conductor (a' - (a + d₀)) → χ a' = χ a * χ d₀ := by
    intro a a' h
    have e : a' = (a + d₀) + (a' - (a + d₀)) := by abel
    calc χ a' = χ ((a + d₀) + (a' - (a + d₀))) := by rw [← e]
      _ = χ a * χ d₀ := by
        simp only [hχdef]
        rw [ofAdd_add, ofAdd_add, map_mul, map_mul, ω.rayChar_rayPrincipal h, mul_one, Units.val_mul]
  have hsum : PowerSeries.coeff n ω.lSeriesF = ∑ a ∈ A, χ a := by
    exact coeff_lSeriesF_eq_sum ω n A hmemA
  rw [hsum]
  have key1 : ∑ a ∈ A, ∑ a' ∈ A, (if IsRayPrincipal ω.conductor (a' - (a + d₀)) then χ a' else 0) =
      (E : ℂ) * χ d₀ * ∑ a ∈ A, χ a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨⟨_, han⟩, haf⟩ := (hmemA a).mp ha
    have hdeg : Divisor.deg (a + d₀) = n := by rw [map_add, hd₀, add_zero, han]
    have hpf : ∀ v, 0 < ω.conductor v → (a + d₀) v = 0 := fun v hv => by
      rw [Finsupp.add_apply, haf v hv, hd₀f v hv, add_zero]
    rw [← Finset.sum_filter,
      Finset.sum_congr rfl (fun a' ha' => hP a a' (Finset.mem_filter.mp ha').2), Finset.sum_const,
      nsmul_eq_mul, hcount _ hdeg hpf]
    ring
  have key2 : ∑ a ∈ A, ∑ a' ∈ A, (if IsRayPrincipal ω.conductor (a' - (a + d₀)) then χ a' else 0) =
      (E : ℂ) * ∑ a ∈ A, χ a := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' ha' => ?_
    obtain ⟨⟨_, han⟩, haf⟩ := (hmemA a').mp ha'
    have hdeg : Divisor.deg (a' - d₀) = n := by rw [_root_.map_sub, hd₀, sub_zero, han]
    have hpf : ∀ v, 0 < ω.conductor v → (a' - d₀) v = 0 := fun v hv => by
      rw [Finsupp.sub_apply, haf v hv, hd₀f v hv, sub_zero]
    have hiff : ∀ a : Divisor Fq k, (IsRayPrincipal ω.conductor (a' - (a + d₀)) ↔
        IsRayPrincipal ω.conductor (a - (a' - d₀))) := fun a => by
      have e : a - (a' - d₀) = -(a' - (a + d₀)) := by abel
      rw [e]
      exact ⟨isRayPrincipal_neg, fun h => by simpa using isRayPrincipal_neg h⟩
    rw [Finset.sum_congr rfl (fun a _ => if_congr (hiff a) rfl rfl), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul, hcount _ hdeg hpf]
  have hEne : (E : ℂ) ≠ 0 := by
    rw [hE]; exact_mod_cast pow_ne_zero _ (Nat.card_pos (α := Fq)).ne'
  have hfd : χ d₀ ≠ 1 := fun h => hχ (Units.val_eq_one.mp h)
  have hz : (E : ℂ) * (∑ a ∈ A, χ a) * (1 - χ d₀) = 0 := by
    linear_combination key2.symm.trans key1
  rcases mul_eq_zero.mp hz with h | h
  · exact (mul_eq_zero.mp h).resolve_left hEne
  · exact absurd (sub_eq_zero.mp h).symm hfd

/-- **Weil VII.§7, Thm. 6, degree bound**: if $\mathbb F_q$ is the field of constants and $\omega$ is a non-principal
Hecke character of conductor $\mathfrak f$, then $L(u,\omega)=\sum_{\mathfrak a\succ0,\ (\mathfrak a,\mathfrak f)=1}
\chi_\omega(\mathfrak a)u^{\deg\mathfrak a}$ is a polynomial of degree at most $2g-2+\deg\mathfrak f$. -/
@[kb "weil1973bnt" "Ch. VII, §7, Thm. 6 (p. 134), function fields: L(u, omega) is a polynomial of degree at most 2g - 2 + deg f"]
theorem weil_VII_7_thm6_degree (hc : IsConstantField Fq k) (ω : FFHeckeCharacter Fq k)
    (hnp : ¬ ω.IsPrincipal) :
    ∃ P : Polynomial ℂ, (P.natDegree : ℤ) ≤ 2 * (genus Fq k : ℤ) - 2 + Divisor.deg ω.conductor ∧
      (P : PowerSeries ℂ) = ω.lSeriesF := by
  classical
  by_cases hf : ω.conductor = 0
  · have hω : ∀ v, ω.IsUnramifiedAt v := fun v =>
      (ω.conductor_apply_eq_zero_iff v).mp (by rw [hf]; rfl)
    obtain ⟨P, hP, hPL⟩ := weil_VII_7_thm6_unramified hc ω hω hnp
    refine ⟨P, by rw [hf, map_zero, add_zero]; exact hP, ?_⟩
    rw [hPL, lSeriesF_eq_lSeries ω hω]
  have hge := genus_eq hc
  set D := 2 * Rep.genusInt Fq k - 2 + Divisor.deg ω.conductor with hD
  by_cases hD0 : 0 ≤ D
  · refine ⟨PowerSeries.trunc (D.toNat + 1) ω.lSeriesF, ?_, ?_⟩
    · have : (PowerSeries.trunc (D.toNat + 1) ω.lSeriesF).natDegree ≤ D.toNat := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro m hm
        rw [PowerSeries.coeff_trunc, if_neg (by omega)]
      rw [hge]; omega
    · ext m
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs with h
      · rfl
      · exact (coeff_lSeriesF_eq_zero hc ω hf m (by omega)).symm
  · exfalso
    have h0 := coeff_lSeriesF_eq_zero hc ω hf 0 (by omega)
    have hset : ∀ a : Divisor Fq k, a ∈ ({0} : Finset (Divisor Fq k)) ↔
        (0 ≤ a ∧ Divisor.deg a = ((0 : ℕ) : ℤ)) ∧ ∀ v, 0 < ω.conductor v → a v = 0 := by
      intro a
      rw [Finset.mem_singleton]
      constructor
      · rintro rfl
        simp
      · rintro ⟨⟨h1, h2⟩, _⟩
        exact Divisor.eq_zero_of_deg_eq_zero h1 (by simpa using h2)
    rw [coeff_lSeriesF_eq_sum ω 0 {0} hset] at h0
    simp at h0

end FFHeckeCharacter

end NumberFieldKB.WeilBNT.FF
