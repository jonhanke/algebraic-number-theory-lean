import NumberFieldKB.WeilBNT.FunctionField.Zeta
import Mathlib.Data.Int.Interval

/-!
# Two of the inputs of `weil_VII_6_thm4`, proved

* **`Place.finite_setOf_degree_le`**: only finitely many places have degree $\le n$.
* **`Divisor.finite_setOf_effective_deg_eq`**: only finitely many effective divisors have a given degree (the field
  `finite_effective` of `WeilZetaInputs`; Tau Ceti `finite_setOf_isEffective_degree_le`).
* **`Divisor.finiteDimensional_riemannRochSpace`**: $A(\mathfrak a)$ is finite-dimensional over $\mathbb F_q$ (the field
  `finiteDimensional` of `WeilZetaInputs`).
-/

open scoped Polynomial

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

theorem Place.valuation_lt_one_of_mem_maximalIdeal' (w : Place Fq k) (z : w.integers)
    (hz : z ∈ IsLocalRing.maximalIdeal w.integers) : w.valuation (z : k) < 1 := by
  by_contra h
  have h1 : w.valuation (z : k) = 1 := le_antisymm z.2 (not_lt.mp h)
  have hz0 : (z : k) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h1
    simp at h1
  apply mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hz)
  refine isUnit_iff_exists_inv.mpr ⟨⟨(z : k)⁻¹, ?_⟩, ?_⟩
  · show w.valuation _ ≤ 1
    rw [map_inv₀, h1]
    simp
  · ext
    simp [hz0]

theorem Place.valuation_prod_lt_one (v : Place Fq k) (x : k) (hx : v.valuation x ≤ 1) (n : ℕ)
    (hn : v.degree ≤ n) :
    v.valuation (∏ d ∈ Finset.Icc 1 n, (x ^ (Nat.card Fq ^ d) - x)) < 1 := by
  let z : v.integers := ⟨x, hx⟩
  let G : v.integers := ∏ d ∈ Finset.Icc 1 n, (z ^ (Nat.card Fq ^ d) - z)
  have hG : (G : k) = ∏ d ∈ Finset.Icc 1 n, (x ^ (Nat.card Fq ^ d) - x) := by
    simp [G, z]
  rw [← hG]
  apply Place.valuation_lt_one_of_mem_maximalIdeal'
  rw [← IsLocalRing.residue_eq_zero_iff, map_prod]
  refine Finset.prod_eq_zero (i := v.degree) (Finset.mem_Icc.mpr ⟨v.degree_pos, hn⟩) ?_
  rw [map_sub, map_pow, sub_eq_zero]
  haveI := Fintype.ofFinite v.residueField
  have hc := v.card_residueField
  rw [Nat.card_eq_fintype_card] at hc
  rw [← hc]
  exact FiniteField.pow_card _

theorem prod_ne_zero_aux (s : SeparatingElement Fq k) (n : ℕ) :
    ∏ d ∈ Finset.Icc 1 n, (s.x ^ (Nat.card Fq ^ d) - s.x) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro d hd
  have hinj : Function.Injective (Polynomial.aeval (R := Fq) s.x) :=
    transcendental_iff_injective.mp s.transcendental
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have h2 : 2 ≤ Nat.card Fq := Nat.succ_le_of_lt Finite.one_lt_card
  have hm : 2 ≤ Nat.card Fq ^ d :=
    h2.trans (Nat.le_self_pow (by omega) _)
  intro h
  have hp : Polynomial.aeval (R := Fq) s.x ((Polynomial.X : Fq[X]) ^ (Nat.card Fq ^ d) - Polynomial.X) =
      Polynomial.aeval (R := Fq) s.x 0 := by
    simpa using h
  have := hinj hp
  have h3 := congrArg (fun p => p.coeff (Nat.card Fq ^ d)) this
  simp [Polynomial.coeff_X, Polynomial.coeff_X_pow] at h3
  rw [if_neg (by omega)] at h3
  simp at h3

theorem finite_setOf_degree_le_aux (s : SeparatingElement Fq k) (n : ℕ) :
    {v : Place Fq k | v.degree ≤ n ∧ v.valuation s.x ≤ 1}.Finite := by
  refine (Place.finite_setOf_valuation_ne_one_of_le_one s.modelRing (prod_ne_zero_aux s n)).subset ?_
  rintro v ⟨hd, hx⟩
  exact ⟨fun a => s.valuation_le_one_of_valuation_x_le_one v hx a,
    (Place.valuation_prod_lt_one v s.x hx n hd).ne⟩

/-- Only finitely many places have degree at most $n$. -/
theorem Place.finite_setOf_degree_le (n : ℕ) : {v : Place Fq k | v.degree ≤ n}.Finite := by
  obtain ⟨s⟩ := weil_III_2_lemma1 (Fq := Fq) (k := k)
  refine ((finite_setOf_degree_le_aux s n).union (finite_setOf_degree_le_aux s.inv n)).subset ?_
  intro v hv
  rcases le_total (v.valuation s.x) 1 with h | h
  · exact Or.inl ⟨hv, h⟩
  · refine Or.inr ⟨hv, ?_⟩
    rw [SeparatingElement.inv_x, map_inv₀]
    exact inv_le_one_of_one_le₀ h

theorem Divisor.apply_mul_degree_le_deg {a : Divisor Fq k} (ha : 0 ≤ a) (v : Place Fq k) :
    a v * (v.degree : ℤ) ≤ Divisor.deg a := by
  by_cases hv : a v = 0
  · rw [hv, zero_mul]
    exact Divisor.deg_nonneg ha
  · rw [Divisor.deg_eq_sum]
    exact Finset.single_le_sum (f := fun w => a w * (w.degree : ℤ))
      (fun w _ => mul_nonneg (by simpa using ha w) (Nat.cast_nonneg _))
      (Finsupp.mem_support_iff.mpr hv)

/-- Only finitely many effective divisors have degree $n$. -/
theorem Divisor.finite_setOf_effective_deg_eq (n : ℤ) :
    {a : Divisor Fq k | 0 ≤ a ∧ Divisor.deg a = n}.Finite := by
  rcases lt_or_ge n 0 with hn | hn
  · convert Set.finite_empty
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h0, h1⟩
    have := Divisor.deg_nonneg h0
    omega
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hS := Place.finite_setOf_degree_le (Fq := Fq) (k := k) N
    haveI : Finite {v : Place Fq k | v.degree ≤ N} := hS.to_subtype
    let g : Divisor Fq k → ({v : Place Fq k | v.degree ≤ N} → ℤ) := fun a v => a v
    have hbound : ∀ a : Divisor Fq k, 0 ≤ a → Divisor.deg a = N → ∀ v, a v ≠ 0 →
        v.degree ≤ N ∧ a v ≤ N := by
      intro a ha hd v hv
      have h1 := Divisor.apply_mul_degree_le_deg ha v
      have h2 : 1 ≤ a v := by
        have := (by simpa using ha v : 0 ≤ a v)
        omega
      have h3 : 1 ≤ (v.degree : ℤ) := by exact_mod_cast v.degree_pos
      rw [hd] at h1
      constructor
      · have : (v.degree : ℤ) ≤ N := by nlinarith
        exact_mod_cast this
      · nlinarith
    refine Set.Finite.of_finite_image (f := g) ?_ ?_
    · refine (Set.Finite.pi (t := fun _ : {v : Place Fq k | v.degree ≤ N} => Set.Icc (0 : ℤ) N)
        (fun _ => Set.finite_Icc _ _)).subset ?_
      rintro _ ⟨a, ⟨ha, hd⟩, rfl⟩
      intro v _
      refine ⟨by simpa using ha v, ?_⟩
      by_cases hv : a v = 0
      · simp only [g, hv]; exact_mod_cast Nat.zero_le _
      · exact (hbound a ha hd v hv).2
    · intro a ha b hb hab
      ext v
      by_cases hv : v ∈ {v : Place Fq k | v.degree ≤ N}
      · exact congrFun hab ⟨v, hv⟩
      · have h1 : a v = 0 := by
          by_contra h
          exact hv (hbound a ha.1 ha.2 v h).1
        have h2 : b v = 0 := by
          by_contra h
          exact hv (hbound b hb.1 hb.2 v h).1
        rw [h1, h2]

theorem Divisor.riemannRochSpace_mono {a b : Divisor Fq k} (h : a ≤ b) :
    a.riemannRochSpace ≤ b.riemannRochSpace := by
  intro f hf
  rw [Divisor.mem_riemannRochSpace_iff] at hf ⊢
  intro v
  exact (hf v).trans (WithZero.exp_le_exp.mpr (h v))

theorem Divisor.finiteDimensional_of_ker (a : Divisor Fq k) (v : Place Fq k) (N : Submodule Fq k)
    [FiniteDimensional Fq N]
    (h : ∀ f ∈ a.riemannRochSpace, v.valuation f < WithZero.exp (a v) → f ∈ N) :
    FiniteDimensional Fq a.riemannRochSpace := by
  obtain ⟨π, hπ⟩ := v.valuation_surjective (WithZero.exp (-1))
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hmul : ∀ (f : k) (m : ℤ), v.valuation (f * π ^ m) = v.valuation f * WithZero.exp (-m) := by
    intro f m
    rw [map_mul, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul]
    congr 2
    ring
  have hmem : ∀ f : a.riemannRochSpace, v.valuation ((f : k) * π ^ (a v)) ≤ 1 := by
    intro f
    rw [hmul]
    calc v.valuation (f : k) * WithZero.exp (-a v) ≤ WithZero.exp (a v) * WithZero.exp (-a v) :=
          mul_le_mul_left ((Divisor.mem_riemannRochSpace_iff a _).mp f.2 v) _
      _ = 1 := by rw [← WithZero.exp_add]; simp
  let ψ : a.riemannRochSpace →ₗ[Fq] v.residueField :=
    { toFun := fun f => IsLocalRing.residue v.integers ⟨(f : k) * π ^ (a v), hmem f⟩
      map_add' := by
        intro f g
        rw [← map_add]
        congr 1
        ext
        simp [add_mul]
      map_smul' := by
        intro c f
        rw [Algebra.smul_def]
        show _ = (IsLocalRing.residue v.integers (algebraMap Fq v.integers c)) * _
        rw [← map_mul]
        congr 1
        ext
        simp [Algebra.smul_def, mul_assoc]
        exact Or.inl rfl }
  have hker : ∀ f : a.riemannRochSpace, ψ f = 0 → (f : k) ∈ N := by
    intro f hf
    apply h _ f.2
    have h1 := Place.valuation_lt_one_of_mem_maximalIdeal' v _
      ((IsLocalRing.residue_eq_zero_iff _).mp hf)
    have h2 : v.valuation ((f : k) * π ^ (a v)) < 1 := h1
    rw [hmul] at h2
    have h3 : v.valuation (f : k) = (v.valuation (f : k) * WithZero.exp (-a v)) * WithZero.exp (a v) := by
      rw [mul_assoc, ← WithZero.exp_add]; simp
    rw [h3]
    calc _ < 1 * WithZero.exp (a v) := mul_lt_mul_of_pos_right h2 (by simp)
      _ = _ := one_mul _
  let ι : LinearMap.ker ψ →ₗ[Fq] N :=
    LinearMap.codRestrict N (a.riemannRochSpace.subtype ∘ₗ (LinearMap.ker ψ).subtype)
      (fun x => hker x.1 (LinearMap.mem_ker.mp x.2))
  haveI : Module.Finite Fq (LinearMap.ker ψ) :=
    Module.Finite.of_injective ι (by
      intro x y hxy
      have := congrArg (fun z : N => (z : k)) hxy
      exact Subtype.ext (Subtype.ext this))
  haveI : Module.Finite Fq v.residueField := Module.Finite.of_finite
  have hfg : (⊤ : Submodule Fq a.riemannRochSpace).FG := by
    refine Submodule.fg_of_fg_map_of_fg_inf_ker ψ (IsNoetherian.noetherian _) ?_
    rw [top_inf_eq]
    exact Module.Finite.iff_fg.mp inferInstance
  exact ⟨hfg⟩

theorem Divisor.finiteDimensional_of_nonneg :
    ∀ (n : ℕ) (a : Divisor Fq k), 0 ≤ a → Divisor.deg a = n →
      FiniteDimensional Fq a.riemannRochSpace := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha hd
    by_cases ha0 : a = 0
    · subst ha0
      obtain ⟨v⟩ := Place.nonempty (Fq := Fq) (k := k)
      refine Divisor.finiteDimensional_of_ker 0 v ⊥ ?_
      intro f hf hlt
      rw [Submodule.mem_bot]
      by_contra hf0
      have halg : IsAlgebraic Fq f := by
        refine Divisor.isAlgebraic_of_forall_valuation_le_one f fun w => ?_
        simpa using (Divisor.mem_riemannRochSpace_iff _ _).mp hf w
      have hne : v.valuation f ≠ 1 := by
        simp only [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero] at hlt
        exact hlt.ne
      exact Valuation.transcendental_of_ne_one (v := v.valuation) Fq f hf0 hne halg
    · obtain ⟨v, hv⟩ : ∃ v, a v ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact ha0 (Finsupp.ext hcon)
      have hav : 1 ≤ a v := by
        have := (by simpa using ha v : 0 ≤ a v)
        omega
      have hb : 0 ≤ a - Finsupp.single v 1 := by
        intro w
        by_cases hw : w = v
        · subst hw
          simp
          omega
        · simpa [Finsupp.single_apply, Ne.symm hw] using ha w
      have hdb : Divisor.deg (a - Finsupp.single v 1) = (n : ℤ) - v.degree := by
        rw [map_sub, hd, Divisor.deg_single]
        ring
      have hdp := v.degree_pos
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (Divisor.deg_nonneg hb)
      have hmn : m < n := by omega
      haveI := ih m hmn _ hb (by rw [← hm])
      refine Divisor.finiteDimensional_of_ker a v (a - Finsupp.single v 1).riemannRochSpace ?_
      intro f hf hlt
      rw [Divisor.mem_riemannRochSpace_iff] at hf ⊢
      intro w
      by_cases hw : w = v
      · subst hw
        simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same]
        by_cases hf0 : w.valuation f = 0
        · rw [hf0]; exact zero_le'
        · rw [← WithZero.exp_log hf0] at hlt ⊢
          rw [WithZero.exp_lt_exp] at hlt
          exact WithZero.exp_le_exp.mpr (by omega)
      · simpa [Finsupp.single_apply, Ne.symm hw] using hf w

/-- $A(\mathfrak a)$ is finite-dimensional over $\mathbb F_q$. -/
theorem Divisor.finiteDimensional_riemannRochSpace (a : Divisor Fq k) :
    FiniteDimensional Fq a.riemannRochSpace := by
  let a' : Divisor Fq k := Finsupp.mapRange (fun n : ℤ => max n 0) (by simp) a
  have ha' : 0 ≤ a' := fun v => by simp [a']
  have hle : a ≤ a' := fun v => by simp [a']
  haveI : FiniteDimensional Fq a'.riemannRochSpace :=
    Divisor.finiteDimensional_of_nonneg (Divisor.deg a').toNat a' ha'
      (Int.toNat_of_nonneg (Divisor.deg_nonneg ha')).symm
  exact Submodule.finiteDimensional_of_le (Divisor.riemannRochSpace_mono hle)

variable (Fq k) in
/-- **Named input** for Weil VII.§6 Thm. 4 after the two fields proved above are removed. Riemann–Roch (Weil VI.§2
Thm. 2; Tau Ceti `isRiemannRochDivisor_weilDifferentialDivisor`), finiteness of $D_0(k)/P(k)$ (Tau Ceti
`finite_ker_degreeClass`), a divisor of degree $1$ (Weil VII.§5 Cor. 5) and $\deg\operatorname{div}\xi=0$ (Tau Ceti
`degree_principal`). -/
structure WeilZetaCoreInputs : Prop where
  riemannRoch : ∃ (g : ℕ) (c : Divisor Fq k), ∀ a : Divisor Fq k,
    (a.ell : ℤ) = Divisor.deg a + 1 - g + (c - a).ell
  finite_classGroup0 : Finite (ClassGroup0 Fq k)
  exists_deg_one : ∃ a : Divisor Fq k, Divisor.deg a = 1
  deg_div : ∀ f : kˣ, Divisor.deg (Divisor.div f : Divisor Fq k) = 0

/-- The full input structure from the core inputs and the two fields proved here. -/
theorem WeilZetaCoreInputs.toWeilZetaInputs (H : WeilZetaCoreInputs Fq k) : WeilZetaInputs Fq k :=
  ⟨H.riemannRoch, Divisor.finiteDimensional_riemannRochSpace, H.finite_classGroup0,
    Divisor.finite_setOf_effective_deg_eq, H.exists_deg_one, H.deg_div⟩

/-- **Weil VII.§6 Thm. 4**, conditional on `WeilZetaCoreInputs` only. -/
@[kb "weil1973bnt" "Ch. VII, §6, Thm. 4 (p. 130), conditional on WeilZetaCoreInputs"]
theorem weil_VII_6_thm4_core (hc : IsConstantField Fq k) (H : WeilZetaCoreInputs Fq k) :
    ∃ P : ℤ[X], P.natDegree = 2 * H.toWeilZetaInputs.genus ∧ P.eval 0 = 1 ∧
      P.eval 1 = Nat.card (ClassGroup0 Fq k) ∧
      zetaSeries Fq k * ((1 - PowerSeries.X) * (1 - (Nat.card Fq : PowerSeries ℤ) * PowerSeries.X)) =
        (P : PowerSeries ℤ) ∧
      ∀ i ≤ 2 * H.toWeilZetaInputs.genus,
        P.coeff (2 * H.toWeilZetaInputs.genus - i) * (Nat.card Fq : ℤ) ^ i =
          (Nat.card Fq : ℤ) ^ H.toWeilZetaInputs.genus * P.coeff i :=
  weil_VII_6_thm4 hc H.toWeilZetaInputs

end NumberFieldKB.WeilBNT.FF
