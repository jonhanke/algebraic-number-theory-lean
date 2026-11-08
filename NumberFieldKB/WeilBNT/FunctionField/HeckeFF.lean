import NumberFieldKB.WeilBNT.FunctionField.Idele
import NumberFieldKB.HeckeCharacter.Units

/-!
# Hecke characters of a function field and their conductor divisor (Weil VII.§3, §7)

For a global function field $k$ over $\mathbb F_q$, a **Hecke character** (Weil's quasicharacter of
$G_k=k_{\mathbb A}^\times/k^\times$, VII.§3) is a continuous morphism $\omega$ of the idele class group into
$\mathbb C^\times$ (`FFHeckeCharacter`, the function-field counterpart of the number-field `HeckeCharacter`).

* `FFIdeleGroup.continuous_single`: the embedding $k_v^\times\to k_{\mathbb A}^\times$ is continuous;
  `FFHeckeCharacter.component`: the local component $\omega_v=\omega|_{k_v^\times}$.
* `FF.unitFiltration`: $U_v^{(n)}=\{u:v(u)=1,\ v(u-1)\le e^{-n}\}$, a basis of neighbourhoods of $1$
  (`exists_unitFiltration_subset`).
* `FFHeckeCharacter.IsUnramifiedAt`; **`FFHeckeCharacter.eventually_isUnramifiedAt`**: $\omega$ is unramified at almost
  all places ($\mathbb C^\times$ has no small subgroups, `NumberFieldKB.HeckeCharacters.eventually_eq_one_of_continuous_pi`).
* `FFHeckeCharacter.conductorExponent` $f(v)$ (least $n$ with $\omega_v$ trivial on $U_v^{(n)}$) and
  **`FFHeckeCharacter.conductor`** $\mathfrak f=\sum_vf(v)\,v$, Weil VII.§7, Def. p. 134 (a divisor).
* `FFHeckeCharacter.eq_one_of_forall_unit`: if $\omega$ is unramified everywhere ($\mathfrak f=0$), it is trivial on
  $\prod_v\mathfrak r_v^\times$.

The construction follows the number-field file `NumberFieldKB/HeckeCharacter/Local.lean`.
-/

open scoped WithZero RestrictedProduct NNReal
open Valuation IsDedekindDomain Topology Filter

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace FFAdeleRing

/-- The embedding $k_v\to k_{\mathbb A}$ with $1$ at the other places. -/
def ofCompletion (v : Place Fq k) (x : v.Completion) : FFAdeleRing Fq k :=
  letI := Classical.decEq (Place Fq k)
  RestrictedProduct.mulSingle (fun w : Place Fq k => w.completionIntegers) v x

theorem continuous_ofCompletion (v : Place Fq k) : Continuous (ofCompletion (Fq := Fq) (k := k) v) := by
  let := Classical.decEq (Place Fq k)
  have hle : (cofinite : Filter (Place Fq k)) ≤ 𝓟 {v}ᶜ := le_principal_iff.mpr (by simp)
  let g : v.Completion → Πʳ w : Place Fq k,
      [w.Completion, (w.completionIntegers : Set w.Completion)]_[𝓟 {v}ᶜ] := fun x =>
    ⟨Pi.mulSingle v x, eventually_principal.mpr fun w hw => by
      rw [Pi.mulSingle_eq_of_ne (by simpa using hw)]
      exact one_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.mpr (continuous_mulSingle v)
  have heq : (ofCompletion v : v.Completion → FFAdeleRing Fq k) =
      RestrictedProduct.inclusion _ _ hle ∘ g := by
    funext x
    ext w
    change RestrictedProduct.mulSingle _ v x w = Pi.mulSingle v x w
    rw [RestrictedProduct.coe_mulSingle_apply]
  rw [heq]
  exact (RestrictedProduct.continuous_inclusion hle).comp hg

end FFAdeleRing

namespace FFIdeleGroup

theorem val_single (v : Place Fq k) (x : v.Completionˣ) :
    ((single v x : FFIdeleGroup Fq k) : FFAdeleRing Fq k) = FFAdeleRing.ofCompletion v (x : v.Completion) := by
  classical
  ext w
  change comp (single v x) w = _
  by_cases h : w = v
  · subst h
    rw [comp_single_self]
    simp [FFAdeleRing.ofCompletion]
  · rw [comp_single_ne h]
    simp [FFAdeleRing.ofCompletion, Pi.mulSingle_eq_of_ne h]

theorem single_mul (v : Place Fq k) (x y : v.Completionˣ) : single v (x * y) = single v x * single v y := by
  refine Units.ext ?_
  ext w
  change comp (single v (x * y)) w = comp (single v x * single v y) w
  rw [comp_mul]
  by_cases h : w = v
  · subst h; rw [comp_single_self, comp_single_self, comp_single_self, Units.val_mul]
  · rw [comp_single_ne h, comp_single_ne h, comp_single_ne h, mul_one]

theorem single_one (v : Place Fq k) : single v (1 : v.Completionˣ) = 1 := by
  refine Units.ext ?_
  ext w
  change comp (single v 1) w = comp 1 w
  rw [comp_one]
  by_cases h : w = v
  · subst h; rw [comp_single_self, Units.val_one]
  · rw [comp_single_ne h]

/-- The embedding $k_v^\times\to k_{\mathbb A}^\times$ as a morphism. -/
def singleHom (v : Place Fq k) : v.Completionˣ →* FFIdeleGroup Fq k where
  toFun := single v
  map_one' := single_one v
  map_mul' := single_mul v

theorem continuous_single (v : Place Fq k) : Continuous (single (Fq := Fq) (k := k) v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : ((↑) ∘ single (Fq := Fq) (k := k) v) = FFAdeleRing.ofCompletion v ∘ (↑) := by
      funext x; exact val_single v x
    rw [this]
    exact (FFAdeleRing.continuous_ofCompletion v).comp Units.continuous_val
  · have : (fun x : v.Completionˣ => ((single (Fq := Fq) (k := k) v x)⁻¹ : FFIdeleGroup Fq k).val) =
        FFAdeleRing.ofCompletion v ∘ (fun x : v.Completionˣ => ((x⁻¹ : v.Completionˣ) : v.Completion)) := by
      funext x
      have : (single (Fq := Fq) (k := k) v x)⁻¹ = single v x⁻¹ := by
        rw [eq_comm, eq_inv_iff_mul_eq_one, ← single_mul, inv_mul_cancel, single_one]
      rw [this]
      exact val_single v x⁻¹
    rw [this]
    exact (FFAdeleRing.continuous_ofCompletion v).comp Units.continuous_coe_inv

end FFIdeleGroup

variable (Fq k) in
/-- **The idele class group** $G_k=k_{\mathbb A}^\times/k^\times$ of a function field. -/
abbrev FFIdeleClassGroup : Type _ :=
  FFIdeleGroup Fq k ⧸ (FFIdeleGroup.principal (Fq := Fq) (k := k)).range

instance FFIdeleClassGroup.normal :
    (FFIdeleGroup.principal (Fq := Fq) (k := k)).range.Normal :=
  ⟨fun n hn g => by rw [mul_comm g n, mul_inv_cancel_right]; exact hn⟩

variable (Fq k) in
/-- **A Hecke character** of the function field $k$ (Weil VII.§3: a quasicharacter of $G_k$): a continuous morphism
$k_{\mathbb A}^\times/k^\times\to\mathbb C^\times$. -/
abbrev FFHeckeCharacter : Type _ := ContinuousMonoidHom (FFIdeleClassGroup Fq k) ℂˣ

/-- **The unit filtration** at $v$: $U_v^{(n)}=\{u\in k_v^\times: v(u)=1,\ v(u-1)\le e^{-n}\}$; $U_v^{(0)}=\mathfrak r_v^\times$
and $U_v^{(n)}=1+\mathfrak p_v^n$ for $n\ge1$. -/
def unitFiltration (v : Place Fq k) (n : ℕ) : Subgroup v.Completionˣ where
  carrier := {u | Valued.v (u : v.Completion) = 1 ∧
    Valued.v ((u : v.Completion) - 1) ≤ WithZero.exp (-(n : ℤ))}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' {a b} ha hb := by
    refine ⟨by rw [Units.val_mul, map_mul, ha.1, hb.1, one_mul], ?_⟩
    have e : ((a * b : v.Completionˣ) : v.Completion) - 1 =
        (a : v.Completion) * ((b : v.Completion) - 1) + ((a : v.Completion) - 1) := by
      rw [Units.val_mul]; ring
    rw [e]
    refine Valuation.map_add_le _ ?_ ha.2
    rw [map_mul, ha.1, one_mul]
    exact hb.2
  inv_mem' {a} ha := by
    have hinv : Valued.v ((a⁻¹ : v.Completionˣ) : v.Completion) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, ha.1, inv_one]
    refine ⟨hinv, ?_⟩
    have e : ((a⁻¹ : v.Completionˣ) : v.Completion) - 1 =
        -(((a⁻¹ : v.Completionˣ) : v.Completion) * ((a : v.Completion) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one]; ring
    rw [e, Valuation.map_neg, map_mul, hinv, one_mul]
    exact ha.2

theorem mem_unitFiltration {v : Place Fq k} {n : ℕ} {u : v.Completionˣ} :
    u ∈ unitFiltration v n ↔ Valued.v (u : v.Completion) = 1 ∧
      Valued.v ((u : v.Completion) - 1) ≤ WithZero.exp (-(n : ℤ)) := Iff.rfl

theorem mem_unitFiltration_zero_iff {v : Place Fq k} {u : v.Completionˣ} :
    u ∈ unitFiltration v 0 ↔ Valued.v (u : v.Completion) = 1 := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [Nat.cast_zero, neg_zero, WithZero.exp_zero, sub_eq_add_neg]
  exact Valuation.map_add_le _ h.le (by rw [Valuation.map_neg, map_one])

theorem unitFiltration_antitone {v : Place Fq k} : Antitone (unitFiltration v) :=
  fun _ _ hnm _ hu => ⟨hu.1, hu.2.trans (WithZero.exp_le_exp.mpr (by omega))⟩

/-- The unit filtration is a basis of neighbourhoods of $1$ in $k_v^\times$. -/
theorem exists_unitFiltration_subset {v : Place Fq k} {W : Set v.Completionˣ}
    (hW : W ∈ 𝓝 1) : ∃ n, (unitFiltration v n : Set v.Completionˣ) ⊆ W := by
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Units.val_one, mem_comap] at hW
  obtain ⟨W', hW', hsub⟩ := hW
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hW'
  set g := MonoidWithZeroHom.ValueGroup₀.embedding γ.1
  have hg : g ≠ 0 := (γ.isUnit.map MonoidWithZeroHom.ValueGroup₀.embedding).ne_zero
  refine ⟨(-(WithZero.log g) + 1).toNat, fun u hu => hsub (hγ ?_)⟩
  change Valued.v.restrict ((u : v.Completion) - 1) < γ
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt hu.2 ?_
  have h : WithZero.exp (-(((-(WithZero.log g) + 1).toNat : ℕ) : ℤ)) < WithZero.exp (WithZero.log g) :=
    WithZero.exp_lt_exp.mpr (by omega)
  rwa [WithZero.exp_log hg] at h

namespace FFHeckeCharacter

/-- **The local component** $\omega_v=\omega|_{k_v^\times}$ of a Hecke character. -/
def component (ω : FFHeckeCharacter Fq k) (v : Place Fq k) : v.Completionˣ →ₜ* ℂˣ :=
  ω.comp ⟨(QuotientGroup.mk' _).comp (FFIdeleGroup.singleHom v),
    QuotientGroup.continuous_mk.comp (FFIdeleGroup.continuous_single v)⟩

@[simp] theorem component_apply (ω : FFHeckeCharacter Fq k) (v : Place Fq k) (u : v.Completionˣ) :
    ω.component v u = ω (QuotientGroup.mk (FFIdeleGroup.single v u)) := rfl

/-- $\omega$ is **unramified** at $v$ if $\omega_v$ is trivial on $\mathfrak r_v^\times$. -/
def IsUnramifiedAt (ω : FFHeckeCharacter Fq k) (v : Place Fq k) : Prop :=
  ∀ u : v.Completionˣ, Valued.v (u : v.Completion) = 1 → ω.component v u = 1

/-- The idele with components $x_v\in\mathfrak r_v^\times$. -/
def piUnitsVal (x : ∀ v : Place Fq k, unitFiltration v 0) : FFAdeleRing Fq k :=
  RestrictedProduct.structureMap (fun v : Place Fq k => v.Completion)
    (fun v => (v.completionIntegers : Set v.Completion)) cofinite
    fun v => ⟨((x v : v.Completionˣ) : v.Completion), (mem_unitFiltration_zero_iff.mp (x v).2).le⟩

theorem continuous_piUnitsVal : Continuous (piUnitsVal (Fq := Fq) (k := k)) := by
  refine (RestrictedProduct.isOpenEmbedding_structureMap fun v =>
    Valued.isOpen_valuationSubring _).continuous.comp ?_
  exact continuous_pi fun v => (Units.continuous_val.comp
    (continuous_subtype_val.comp (continuous_apply v))).subtype_mk _

theorem piUnitsVal_mul (x y : ∀ v : Place Fq k, unitFiltration v 0) :
    piUnitsVal (x * y) = piUnitsVal x * piUnitsVal y := by
  ext v; rfl

theorem piUnitsVal_one : piUnitsVal (1 : ∀ v : Place Fq k, unitFiltration v 0) = 1 := by
  ext v; rfl

/-- The continuous morphism $\prod_v\mathfrak r_v^\times\to k_{\mathbb A}^\times$. -/
def piUnitsIdele : (∀ v : Place Fq k, unitFiltration v 0) →* FFIdeleGroup Fq k where
  toFun x :=
    { val := piUnitsVal x
      inv := piUnitsVal x⁻¹
      val_inv := by rw [← piUnitsVal_mul, mul_inv_cancel, piUnitsVal_one]
      inv_val := by rw [← piUnitsVal_mul, inv_mul_cancel, piUnitsVal_one] }
  map_one' := Units.ext piUnitsVal_one
  map_mul' x y := Units.ext (piUnitsVal_mul x y)

theorem continuous_piUnitsIdele : Continuous (piUnitsIdele (Fq := Fq) (k := k)) :=
  Units.continuous_iff.mpr ⟨continuous_piUnitsVal, continuous_piUnitsVal.comp continuous_inv⟩

theorem piUnitsIdele_mulSingle (v : Place Fq k) (u : unitFiltration v 0) :
    letI := Classical.decEq (Place Fq k)
    piUnitsIdele (Pi.mulSingle v u) = FFIdeleGroup.single v (u : v.Completionˣ) := by
  classical
  refine Units.ext ?_
  ext w
  change ((Pi.mulSingle (M := fun w : Place Fq k => unitFiltration w 0) v u w :
      unitFiltration w 0) : w.Completionˣ).val = _
  by_cases hw : w = v
  · subst hw
    simp [FFIdeleGroup.single, RestrictedProduct.mkUnit]
  · simp [Pi.mulSingle_eq_of_ne hw, FFIdeleGroup.single, RestrictedProduct.mkUnit, hw]

/-- **A Hecke character of a function field is unramified at all but finitely many places.** -/
theorem eventually_isUnramifiedAt (ω : FFHeckeCharacter Fq k) : ∀ᶠ v in cofinite, ω.IsUnramifiedAt v := by
  let := Classical.decEq (Place Fq k)
  have hcont : Continuous fun x : (∀ v : Place Fq k, unitFiltration v 0) =>
      ω (QuotientGroup.mk (piUnitsIdele x)) :=
    (map_continuous ω).comp (QuotientGroup.continuous_mk.comp continuous_piUnitsIdele)
  have h := NumberFieldKB.HeckeCharacters.eventually_eq_one_of_continuous_pi
    (fun x => ω (QuotientGroup.mk (piUnitsIdele x))) hcont
    (by simp)
    (fun v => (ω.component v : v.Completionˣ →* ℂˣ).comp (unitFiltration v 0).subtype)
    (fun v u => by simp [piUnitsIdele_mulSingle])
  refine h.mono fun v hv u hu => ?_
  have := DFunLike.congr_fun hv ⟨u, mem_unitFiltration_zero_iff.mpr hu⟩
  simpa using this

/-- At every place, $\omega_v$ is trivial on some $U_v^{(n)}$. -/
theorem exists_component_eq_one (ω : FFHeckeCharacter Fq k) (v : Place Fq k) :
    ∃ n, ∀ u ∈ unitFiltration v n, ω.component v u = 1 := by
  set U : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1 / 2}
  have hU : IsOpen U :=
    isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have h1 : ω.component v ⁻¹' U ∈ 𝓝 1 :=
    (ω.component v).continuous.continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by simp [U, FFIdeleGroup.single_one]))
  obtain ⟨n, hn⟩ := exists_unitFiltration_subset h1
  refine ⟨n, fun u hu => ?_⟩
  have h := MonoidHom.eq_one_of_norm_sub_one_lt
    ((ω.component v : v.Completionˣ →* ℂˣ).comp (unitFiltration v n).subtype)
    fun x => hn x.2
  exact DFunLike.congr_fun h ⟨u, hu⟩

/-- **The conductor exponent** $f(v)$: the least $n$ such that $\omega_v$ is trivial on $U_v^{(n)}$ (Weil VII.§2,
Def. 1 of the order of a quasicharacter of a $p$-field, used in VII.§7). -/
def conductorExponent (ω : FFHeckeCharacter Fq k) (v : Place Fq k) : ℕ :=
  sInf {n | ∀ u ∈ unitFiltration v n, ω.component v u = 1}

theorem component_eq_one_of_mem (ω : FFHeckeCharacter Fq k) {v : Place Fq k} {u : v.Completionˣ}
    (hu : u ∈ unitFiltration v (ω.conductorExponent v)) : ω.component v u = 1 :=
  Nat.sInf_mem (s := {n | ∀ u ∈ unitFiltration v n, ω.component v u = 1})
    (ω.exists_component_eq_one v) u hu

theorem conductorExponent_le_iff (ω : FFHeckeCharacter Fq k) (v : Place Fq k) (n : ℕ) :
    ω.conductorExponent v ≤ n ↔ ∀ u ∈ unitFiltration v n, ω.component v u = 1 :=
  ⟨fun h _ hu => ω.component_eq_one_of_mem (unitFiltration_antitone h hu), fun h => Nat.sInf_le h⟩

theorem conductorExponent_eq_zero_iff (ω : FFHeckeCharacter Fq k) (v : Place Fq k) :
    ω.conductorExponent v = 0 ↔ ω.IsUnramifiedAt v := by
  rw [← Nat.le_zero, conductorExponent_le_iff]
  exact ⟨fun h u hu => h u (mem_unitFiltration_zero_iff.mpr hu),
    fun h u hu => h u (mem_unitFiltration_zero_iff.mp hu)⟩

theorem finite_conductorExponent_ne_zero (ω : FFHeckeCharacter Fq k) :
    {v : Place Fq k | ((ω.conductorExponent v : ℕ) : ℤ) ≠ 0}.Finite := by
  refine (Filter.eventually_cofinite.1 ω.eventually_isUnramifiedAt).subset ?_
  intro v hv hun
  apply hv
  simp [(conductorExponent_eq_zero_iff ω v).mpr hun]

/-- **The conductor of $\omega$** (Weil VII.§7, Def. p. 134, characteristic $p$): the divisor
$\mathfrak f=\sum_vf(v)\cdot v$. -/
@[kb "weil1973bnt" "Ch. VII, §7, Def. p. 134 (the conductor of a quasicharacter as a divisor), function fields"]
def conductor (ω : FFHeckeCharacter Fq k) : Divisor Fq k :=
  Finsupp.ofSupportFinite (fun v => (ω.conductorExponent v : ℤ)) ω.finite_conductorExponent_ne_zero

@[simp] theorem conductor_apply (ω : FFHeckeCharacter Fq k) (v : Place Fq k) :
    ω.conductor v = ω.conductorExponent v := rfl

theorem conductor_nonneg (ω : FFHeckeCharacter Fq k) : 0 ≤ ω.conductor := fun v => by simp

/-- $v$ lies in the support of the conductor exactly when $\omega$ is ramified at $v$. -/
theorem conductor_apply_eq_zero_iff (ω : FFHeckeCharacter Fq k) (v : Place Fq k) :
    ω.conductor v = 0 ↔ ω.IsUnramifiedAt v := by
  rw [conductor_apply, Nat.cast_eq_zero, conductorExponent_eq_zero_iff]

/-- A continuous morphism from a product of topological groups into $\mathbb C^\times$ that is trivial on every
factor is trivial. -/
theorem eq_one_of_continuous_pi {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, CommGroup (G i)]
    [∀ i, TopologicalSpace (G i)] (f : (∀ i, G i) →* ℂˣ) (hf : Continuous f)
    (h : ∀ i (x : G i), f (Pi.mulSingle i x) = 1) : f = 1 := by
  classical
  set U : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1 / 2}
  have hU : IsOpen U :=
    isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have h1 : f ⁻¹' U ∈ 𝓝 (1 : ∀ i, G i) :=
    hf.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simp [U]))
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, hI, t, ht, hsub⟩ := h1
  -- the subgroup of elements trivial on `I`
  let H : Subgroup (∀ i, G i) :=
    { carrier := {y | ∀ i ∈ I, y i = 1}
      one_mem' := fun i _ => rfl
      mul_mem' := fun {a b} ha hb i hi => by simp [ha i hi, hb i hi]
      inv_mem' := fun {a} ha i hi => by simp [ha i hi] }
  have hH : f.comp H.subtype = 1 := by
    refine MonoidHom.eq_one_of_norm_sub_one_lt _ fun y => ?_
    refine hsub fun i hi => ?_
    have : (y : ∀ i, G i) i = 1 := y.2 i hi
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, this]
    exact mem_of_mem_nhds (ht i)
  ext x
  have hfin : ∀ s : Finset ι, f (∏ i ∈ s, Pi.mulSingle i (x i)) = 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, map_mul, h, ih, one_mul]
  have hI' := hI.toFinset
  set y : ∀ i, G i := fun i => if i ∈ I then 1 else x i with hy
  have hyH : y ∈ H := fun i hi => by simp [hy, hi]
  have hx : x = (∏ i ∈ hI.toFinset, Pi.mulSingle i (x i)) * y := by
    funext j
    rw [Pi.mul_apply, Finset.prod_apply]
    by_cases hj : j ∈ I
    · rw [Finset.prod_eq_single j]
      · simp [hy, hj]
      · intro b _ hb; simp [Pi.mulSingle_eq_of_ne' hb]
      · intro hj'; exact absurd ((Set.Finite.mem_toFinset hI).2 hj) hj'
    · rw [Finset.prod_eq_one]
      · simp [hy, hj]
      · intro b hb
        have hb' : b ∈ I := (Set.Finite.mem_toFinset hI).1 hb
        have : b ≠ j := fun e => hj (e ▸ hb')
        simp [Pi.mulSingle_eq_of_ne' this]
  have hfy : f y = 1 := DFunLike.congr_fun hH ⟨y, hyH⟩
  rw [hx, map_mul, hfin, hfy, one_mul]
  rfl

/-- If $\omega$ is unramified everywhere (conductor $0$), it is trivial on $\prod_v\mathfrak r_v^\times$, i.e. on the
ideles all of whose components are units. -/
theorem eq_one_of_forall_unit (ω : FFHeckeCharacter Fq k) (hω : ∀ v, ω.IsUnramifiedAt v)
    (z : FFIdeleGroup Fq k) (hz : ∀ v, Valued.v (FFIdeleGroup.comp z v) = 1) :
    ω (QuotientGroup.mk z) = 1 := by
  classical
  have hcont : Continuous ((ω : FFIdeleClassGroup Fq k →* ℂˣ).comp
      ((QuotientGroup.mk' _).comp piUnitsIdele)) :=
    (map_continuous ω).comp (QuotientGroup.continuous_mk.comp continuous_piUnitsIdele)
  have h1 := eq_one_of_continuous_pi (G := fun v : Place Fq k => ↥(unitFiltration v 0))
    ((ω : FFIdeleClassGroup Fq k →* ℂˣ).comp ((QuotientGroup.mk' _).comp piUnitsIdele)) hcont
    fun v u => by
      change ω (QuotientGroup.mk (piUnitsIdele (Pi.mulSingle v u))) = 1
      rw [piUnitsIdele_mulSingle]
      exact hω v u (mem_unitFiltration_zero_iff.mp u.2)
  -- write `z` as an element of `∏ r_v^×`
  have hzu : ∀ v, FFIdeleGroup.comp z v ≠ 0 := FFIdeleGroup.comp_ne_zero z
  let x : ∀ v : Place Fq k, unitFiltration v 0 := fun v =>
    ⟨Units.mk0 (FFIdeleGroup.comp z v) (hzu v), mem_unitFiltration_zero_iff.mpr (by simpa using hz v)⟩
  have hx : piUnitsIdele x = z := by
    refine Units.ext ?_
    ext v
    rfl
  have := DFunLike.congr_fun h1 x
  simpa [hx] using this

end FFHeckeCharacter

end NumberFieldKB.WeilBNT.FF
