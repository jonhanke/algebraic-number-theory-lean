import NumberFieldKB.WeilBNT.FunctionField.AdeleMeasure
import NumberFieldKB.WeilBNT.FunctionField.ZetaFinal

/-!
# Effective divisors in a ray class (counting with Riemann–Roch)

For a nonzero effective divisor $\mathfrak f$ (a modulus) of the function field $k$:

* `CongOne f ξ`: $\xi\equiv1\bmod\mathfrak f$, i.e. $v(\xi-1)\le e^{-f(v)}$ at every place with $f(v)>0$;
  `IsRayPrincipal f d`: $\mathfrak d=\operatorname{div}\xi$ with $\xi\equiv1\bmod\mathfrak f$ (a subgroup:
  `isRayPrincipal_zero`, `isRayPrincipal_add`, `isRayPrincipal_neg`).
* `exists_congOne_mem`: if $\mathfrak b$ is prime to $\mathfrak f$ and $\deg(\mathfrak b-\mathfrak f)>2g-2$, some
  $\xi\in L(\mathfrak b)$ has $\xi\equiv1\bmod\mathfrak f$ (the adelic Riemann–Roch, VI Cor. 3 of Thm. 2).
* **`card_rayClass_effective`**: under the same hypotheses and with $\mathbb F_q$ the field of constants, the ray class
  of $\mathfrak b$ modulo $\mathfrak f$ contains exactly $q^{\lambda(\mathfrak b-\mathfrak f)}$ effective divisors.
-/

open scoped WithZero

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

/-- $\xi\equiv1\bmod\mathfrak f$: $v(\xi-1)\le e^{-f(v)}$ at every place with $f(v)>0$. -/
def CongOne (f : Divisor Fq k) (ξ : k) : Prop :=
  ∀ v : Place Fq k, 0 < f v → v.valuation (ξ - 1) ≤ WithZero.exp (-f v)

/-- $\mathfrak d$ is **ray-principal modulo $\mathfrak f$**: $\mathfrak d=\operatorname{div}\xi$ with
$\xi\equiv1\bmod\mathfrak f$. -/
def IsRayPrincipal (f d : Divisor Fq k) : Prop :=
  ∃ ξ : kˣ, CongOne f (ξ : k) ∧ Divisor.div ξ = d

/-- If $\xi\equiv1\bmod\mathfrak f$ and $f(v)>0$ then $v(\xi)=1$. -/
theorem CongOne.valuation_eq_one {f : Divisor Fq k} {ξ : k} (h : CongOne f ξ) {v : Place Fq k}
    (hv : 0 < f v) : v.valuation ξ = 1 := by
  have h1 : v.valuation (ξ - 1) < v.valuation 1 := by
    rw [map_one]
    exact lt_of_le_of_lt (h v hv) (by
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega))
  have := Valuation.map_add_eq_of_lt_left v.valuation h1
  rw [add_sub_cancel, map_one] at this
  exact this

/-- $\equiv1\bmod\mathfrak f$ is multiplicative. -/
theorem CongOne.mul {f : Divisor Fq k} {ξ η : k} (hξ : CongOne f ξ) (hη : CongOne f η) :
    CongOne f (ξ * η) := by
  intro v hv
  have e : ξ * η - 1 = ξ * (η - 1) + (ξ - 1) := by ring
  rw [e]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ (hξ v hv))
  rw [map_mul, hξ.valuation_eq_one hv, one_mul]
  exact hη v hv

/-- $\equiv1\bmod\mathfrak f$ is stable under inversion. -/
theorem CongOne.inv {f : Divisor Fq k} {ξ : k} (hξ : CongOne f ξ) : CongOne f ξ⁻¹ := by
  intro v hv
  have h0 : ξ ≠ 0 := by
    rintro rfl
    have := hξ.valuation_eq_one hv
    simp at this
  have e : ξ⁻¹ - 1 = -(ξ⁻¹ * (ξ - 1)) := by field_simp; ring
  rw [e, Valuation.map_neg, map_mul, map_inv₀, hξ.valuation_eq_one hv]
  simpa using hξ v hv

theorem isRayPrincipal_zero (f : Divisor Fq k) : IsRayPrincipal f 0 := by
  refine ⟨1, fun v _ => ?_, Divisor.div_one⟩
  simp

theorem isRayPrincipal_add {f d e : Divisor Fq k} (hd : IsRayPrincipal f d) (he : IsRayPrincipal f e) :
    IsRayPrincipal f (d + e) := by
  obtain ⟨ξ, hξ, rfl⟩ := hd
  obtain ⟨η, hη, rfl⟩ := he
  exact ⟨ξ * η, by simpa using hξ.mul hη, Divisor.div_mul ξ η⟩

theorem isRayPrincipal_neg {f d : Divisor Fq k} (hd : IsRayPrincipal f d) : IsRayPrincipal f (-d) := by
  obtain ⟨ξ, hξ, rfl⟩ := hd
  exact ⟨ξ⁻¹, by simpa using hξ.inv, Divisor.div_inv ξ⟩

/-- The adele equal to $1$ at the places with $f(v)>0$ and $0$ elsewhere. -/
def modAdele (f : Divisor Fq k) : FFAdeleRing Fq k :=
  ⟨fun w => if 0 < f w then 1 else 0, by
    refine Filter.eventually_cofinite.2 (f.support.finite_toSet.subset ?_)
    intro w hw
    by_contra h
    apply hw
    have : ¬ 0 < f w := fun h' => h (by simpa using h'.ne')
    simp only [this, if_false]
    exact (w.completionIntegers).zero_mem⟩

/-- Pointwise nonnegativity of an effective divisor. -/
theorem apply_nonneg_of_nonneg {f : Divisor Fq k} (hf : 0 ≤ f) (v : Place Fq k) : 0 ≤ f v := by
  simpa using Finsupp.le_def.1 hf v

/-- If $\mathfrak b$ is prime to $\mathfrak f$ and $\deg(\mathfrak b-\mathfrak f)>2g-2$, some $\xi\in L(\mathfrak b)$
satisfies $\xi\equiv1\bmod\mathfrak f$. -/
theorem exists_congOne_mem (hc : IsConstantField Fq k) {f b : Divisor Fq k} (hf : 0 ≤ f)
    (hb : ∀ v, 0 < f v → b v = 0) (hdeg : 2 * Rep.genusInt Fq k - 2 < Divisor.deg (b - f)) :
    ∃ ξ ∈ b.riemannRochSpace, CongOne f ξ := by
  obtain ⟨ξ, hξ⟩ := FFAdeleRing.weil_VI_2_cor3_adelic hc hdeg (modAdele f)
  rw [FFAdeleRing.mem_U_iff] at hξ
  have key : ∀ v : Place Fq k, 0 < f v → v.valuation (ξ - 1) ≤ WithZero.exp (-f v) := by
    intro v hv
    have h := hξ v
    have e : Valued.v ((modAdele f - FFAdeleRing.diag (Fq := Fq) ξ : FFAdeleRing Fq k) v) =
        v.valuation (1 - ξ) := by
      show Valued.v ((if 0 < f v then (1 : v.Completion) else 0) - v.toCompletion ξ) = _
      rw [if_pos hv, ← map_one v.toCompletion, ← map_sub, Place.valued_toCompletion]
    have e2 : (b - f) v = -f v := by simp [hb v hv]
    rw [e, e2] at h
    rw [Valuation.map_sub_swap]
    exact h
  refine ⟨ξ, ?_, fun v hv => key v hv⟩
  rw [Divisor.mem_riemannRochSpace_iff]
  intro v
  rcases (apply_nonneg_of_nonneg hf v).lt_or_eq with hv | hv
  · have h1 : v.valuation ξ ≤ 1 := by
      have : ξ = 1 + (ξ - 1) := by ring
      rw [this]
      refine (Valuation.map_add _ _ _).trans (max_le (by simp) ?_)
      refine (key v hv).trans ?_
      rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.2 (by omega)
    rw [hb v hv]; simpa using h1
  · have h := hξ v
    have e : Valued.v ((modAdele f - FFAdeleRing.diag (Fq := Fq) ξ : FFAdeleRing Fq k) v) =
        v.valuation ξ := by
      show Valued.v ((if 0 < f v then (1 : v.Completion) else 0) - v.toCompletion ξ) = _
      rw [if_neg (by omega), zero_sub, Valuation.map_neg, Place.valued_toCompletion]
    have e2 : (b - f) v = b v := by simp [← hv]
    rw [e, e2] at h
    exact h

/-- A ray-congruent-to-one element is nonzero when the modulus is nonzero. -/
theorem CongOne.ne_zero {f : Divisor Fq k} (hf : 0 ≤ f) (hf0 : f ≠ 0) {ξ : k} (h : CongOne f ξ) :
    ξ ≠ 0 := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hf0 (Finsupp.ext hh)
  have hv' : 0 < f v := lt_of_le_of_ne (apply_nonneg_of_nonneg hf v) (Ne.symm hv)
  rintro rfl
  have := h.valuation_eq_one hv'
  simp at this

/-- Two elements $\equiv1\bmod\mathfrak f$ with the same divisor are equal. -/
theorem CongOne.eq_of_div_eq (hc : IsConstantField Fq k) {f : Divisor Fq k} (hf : 0 ≤ f) (hf0 : f ≠ 0)
    {ξ η : kˣ} (hξ : CongOne f (ξ : k)) (hη : CongOne f (η : k)) (h : (Divisor.div ξ : Divisor Fq k) = Divisor.div η) :
    ξ = η := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hf0 (Finsupp.ext hh)
  have hv' : 0 < f v := lt_of_le_of_ne (apply_nonneg_of_nonneg hf v) (Ne.symm hv)
  have h0 : Divisor.div (ξ * η⁻¹) = (0 : Divisor Fq k) := by
    rw [Divisor.div_mul, Divisor.div_inv, h]; abel
  obtain ⟨c, hcx⟩ := hc _ ((Divisor.div_eq_zero_iff _).1 h0)
  have hcx' : (ξ : k) = algebraMap Fq k c * η := by
    have : ((ξ * η⁻¹ : kˣ) : k) = ξ * (η : k)⁻¹ := by simp
    rw [this] at hcx
    have hη0 : (η : k) ≠ 0 := η.ne_zero
    field_simp at hcx
    rw [← hcx]
  have hc1 : c = 1 := by
    by_contra hne
    have hsub : (ξ : k) - η = algebraMap Fq k (c - 1) * η := by
      rw [map_sub, map_one]; nth_rewrite 1 [hcx']; ring
    have h1 : v.valuation ((ξ : k) - η) < 1 := by
      have e : (ξ : k) - η = ((ξ : k) - 1) - ((η : k) - 1) := by ring
      rw [e]
      refine lt_of_le_of_lt ((Valuation.map_sub _ _ _).trans (max_le (hξ v hv') (hη v hv'))) ?_
      rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
    rw [hsub, map_mul, Place.valuation_algebraMap v (sub_ne_zero.2 hne),
      hη.valuation_eq_one hv', one_mul] at h1
    exact lt_irrefl _ h1
  apply Units.ext
  rw [hcx', hc1, map_one, one_mul]

/-- Elements of $L(\mathfrak b-\mathfrak f)$ are $\le e^{-f(v)}$ at places of the modulus. -/
theorem rr_sub_le {f b : Divisor Fq k} (hb : ∀ v, 0 < f v → b v = 0) {η : k}
    (hη : η ∈ (b - f).riemannRochSpace) {v : Place Fq k} (hv : 0 < f v) :
    v.valuation η ≤ WithZero.exp (-f v) := by
  have := (Divisor.mem_riemannRochSpace_iff _ _).1 hη v
  have e : (b - f) v = -f v := by simp [hb v hv]
  rwa [e] at this

/-- $L(\mathfrak b-\mathfrak f)\subseteq L(\mathfrak b)$ for effective $\mathfrak f$. -/
theorem rr_sub_mem {f b : Divisor Fq k} (hf : 0 ≤ f) {η : k}
    (hη : η ∈ (b - f).riemannRochSpace) : η ∈ b.riemannRochSpace := by
  rw [Divisor.mem_riemannRochSpace_iff] at hη ⊢
  intro v
  refine (hη v).trans (WithZero.exp_le_exp.2 ?_)
  have := apply_nonneg_of_nonneg hf v
  simp only [Finsupp.coe_sub, Pi.sub_apply]
  omega

/-- **The number of effective divisors in a ray class**: for a nonzero effective modulus $\mathfrak f$ and a divisor
$\mathfrak b$ prime to $\mathfrak f$ with $\deg(\mathfrak b-\mathfrak f)>2g-2$, the effective divisors $\mathfrak a$
with $\mathfrak a-\mathfrak b$ ray-principal modulo $\mathfrak f$ number $q^{\lambda(\mathfrak b-\mathfrak f)}$. -/
theorem card_rayClass_effective (hc : IsConstantField Fq k) {f b : Divisor Fq k} (hf : 0 ≤ f) (hf0 : f ≠ 0)
    (hb : ∀ v, 0 < f v → b v = 0) (hdeg : 2 * Rep.genusInt Fq k - 2 < Divisor.deg (b - f)) :
    Nat.card {a : Divisor Fq k // 0 ≤ a ∧ IsRayPrincipal f (a - b)} = Nat.card Fq ^ (b - f).ell := by
  obtain ⟨ξ₀, hξ₀L, hξ₀⟩ := exists_congOne_mem hc hf hb hdeg
  have hnz : ∀ ξ : {ξ : k // ξ ∈ b.riemannRochSpace ∧ CongOne f ξ}, ξ.1 ≠ 0 :=
    fun ξ => ξ.2.2.ne_zero hf hf0
  have hpos : ∀ ξ : {ξ : k // ξ ∈ b.riemannRochSpace ∧ CongOne f ξ},
      0 ≤ b + Divisor.div (Units.mk0 ξ.1 (hnz ξ)) := by
    intro ξ
    have h1 := (Divisor.mem_riemannRochSpace_iff_ord b (hnz ξ)).1 ξ.2.1
    rw [Finsupp.le_def]
    intro v
    have := h1 v
    simp only [Finsupp.coe_add, Pi.add_apply, Divisor.div_apply, Units.val_mk0, Finsupp.coe_zero,
      Pi.zero_apply]
    omega
  -- step A
  have hA : Nat.card {ξ : k // ξ ∈ b.riemannRochSpace ∧ CongOne f ξ} =
      Nat.card {a : Divisor Fq k // 0 ≤ a ∧ IsRayPrincipal f (a - b)} := by
    refine Nat.card_eq_of_bijective
      (fun ξ => ⟨b + Divisor.div (Units.mk0 ξ.1 (hnz ξ)), hpos ξ,
        Units.mk0 ξ.1 (hnz ξ), by simpa using ξ.2.2, by simp⟩) ⟨?_, ?_⟩
    · intro ξ ξ' h
      have h1 := congrArg Subtype.val h
      simp only at h1
      have h2 := add_left_cancel h1
      have h3 := CongOne.eq_of_div_eq hc hf hf0 (ξ := Units.mk0 ξ.1 (hnz ξ))
        (η := Units.mk0 ξ'.1 (hnz ξ')) (by simpa using ξ.2.2) (by simpa using ξ'.2.2) h2
      exact Subtype.ext (congrArg Units.val h3)
    · rintro ⟨a, ha0, u, hu, hd⟩
      have hmem : (u : k) ∈ b.riemannRochSpace := by
        rw [Divisor.mem_riemannRochSpace_iff_ord b u.ne_zero]
        intro v
        have h1 := Finsupp.le_def.1 ha0 v
        have h2 := congrArg (fun d : Divisor Fq k => d v) hd
        simp only [Divisor.div_apply, Finsupp.coe_sub, Pi.sub_apply] at h2
        simp only [Finsupp.coe_zero, Pi.zero_apply] at h1
        omega
      refine ⟨⟨(u : k), hmem, hu⟩, ?_⟩
      apply Subtype.ext
      simp only
      have : Units.mk0 (u : k) u.ne_zero = u := Units.ext rfl
      rw [this, hd]
      abel
  -- step B
  have hB : Nat.card {ξ : k // ξ ∈ b.riemannRochSpace ∧ CongOne f ξ} =
      Nat.card (b - f).riemannRochSpace := by
    refine Nat.card_eq_of_bijective
      (fun ξ => ⟨ξ.1 - ξ₀, ?_⟩) ⟨?_, ?_⟩
    · rw [Divisor.mem_riemannRochSpace_iff]
      intro v
      rcases (apply_nonneg_of_nonneg hf v).lt_or_eq with hv | hv
      · have e : (b - f) v = -f v := by simp [hb v hv]
        rw [e]
        have e2 : ξ.1 - ξ₀ = (ξ.1 - 1) - (ξ₀ - 1) := by ring
        rw [e2]
        exact (Valuation.map_sub _ _ _).trans (max_le (ξ.2.2 v hv) (hξ₀ v hv))
      · have e : (b - f) v = b v := by simp [← hv]
        rw [e]
        exact (Divisor.mem_riemannRochSpace_iff _ _).1 (b.riemannRochSpace.sub_mem ξ.2.1 hξ₀L) v
    · intro ξ ξ' h
      have := congrArg Subtype.val h
      exact Subtype.ext (sub_left_inj.1 this)
    · rintro ⟨η, hη⟩
      refine ⟨⟨ξ₀ + η, b.riemannRochSpace.add_mem hξ₀L (rr_sub_mem hf hη), ?_⟩, ?_⟩
      · intro v hv
        have e : ξ₀ + η - 1 = (ξ₀ - 1) + η := by ring
        rw [e]
        exact (Valuation.map_add _ _ _).trans (max_le (hξ₀ v hv) (rr_sub_le hb hη hv))
      · apply Subtype.ext
        simp
  rw [hA.symm, hB]
  classical
  have : Fintype Fq := Fintype.ofFinite Fq
  have : Finite (b - f).riemannRochSpace := Module.finite_of_finite Fq
  have : Fintype (b - f).riemannRochSpace := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card (α := (b - f).riemannRochSpace), Module.card_eq_pow_finrank (K := Fq),
    Nat.card_eq_fintype_card (α := Fq)]
  rfl

end NumberFieldKB.WeilBNT.FF
