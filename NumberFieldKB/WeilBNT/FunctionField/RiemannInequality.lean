import NumberFieldKB.WeilBNT.FunctionField.ProductFormula

/-!
# Riemann's inequality and the finiteness of the class number (Weil VI.§1–2)

* **`Divisor.ell_le_of_le`**: for $\mathfrak a\prec\mathfrak b$ (i.e. `a ≤ b`),
  $\lambda(\mathfrak b)-\lambda(\mathfrak a)\le\deg\mathfrak b-\deg\mathfrak a$.
* **`Divisor.ell_add_div`**: $\lambda(\mathfrak a+\operatorname{div}\xi)=\lambda(\mathfrak a)$ (multiplication by $\xi$).
* **`Divisor.riemannRochSpace_eq_bot_of_deg_neg`**: $A(\mathfrak a)=0$ if $\deg\mathfrak a<0$ (product formula).
* **`Divisor.exists_deg_sub_ell_le`** (Riemann's theorem): $\deg\mathfrak a-\lambda(\mathfrak a)$ is bounded above.
* **`finite_classGroup0`**: $D_0(k)/P(k)$ is finite (Weil VI.§1, text p. 97; Tau Ceti `finite_ker_degreeClass`).
-/

open scoped Polynomial
open IntermediateField

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

namespace Divisor

instance (a : Divisor Fq k) : FiniteDimensional Fq a.riemannRochSpace :=
  finiteDimensional_riemannRochSpace a

theorem valuation_eq_exp_neg_ord (v : Place Fq k) {f : k} (hf : f ≠ 0) :
    v.valuation f = WithZero.exp (-v.ord f) := by
  have hv : v.valuation f ≠ 0 := by simpa using hf
  rw [Place.ord, neg_neg, WithZero.exp_log hv]

theorem ord_mul' (v : Place Fq k) {f g : k} (hf : f ≠ 0) (hg : g ≠ 0) :
    v.ord (f * g) = v.ord f + v.ord g := by
  have hf' : v.valuation f ≠ 0 := by simpa using hf
  have hg' : v.valuation g ≠ 0 := by simpa using hg
  simp only [Place.ord, map_mul]
  rw [WithZero.log_mul hf' hg']
  ring

theorem ord_pow' (v : Place Fq k) {f : k} (hf : f ≠ 0) (j : ℕ) : v.ord (f ^ j) = j * v.ord f := by
  induction j with
  | zero => simp [Place.ord]
  | succ j ih =>
    rw [pow_succ, ord_mul' v (pow_ne_zero _ hf) hf, ih]
    push_cast
    ring

theorem ord_inv' (v : Place Fq k) {f : k} (hf : f ≠ 0) : v.ord f⁻¹ = - v.ord f := by
  have := ord_mul' v hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf] at this
  have h1 : v.ord (1 : k) = 0 := by simp [Place.ord]
  omega

theorem mem_riemannRochSpace_iff_ord (a : Divisor Fq k) {f : k} (hf : f ≠ 0) :
    f ∈ a.riemannRochSpace ↔ ∀ v : Place Fq k, -a v ≤ v.ord f := by
  rw [mem_riemannRochSpace_iff]
  refine forall_congr' fun v => ?_
  rw [valuation_eq_exp_neg_ord v hf, WithZero.exp_le_exp]
  omega

theorem mem_add_div_iff (a : Divisor Fq k) (f : kˣ) (g : k) :
    g ∈ (a + div f).riemannRochSpace ↔ g * f ∈ a.riemannRochSpace := by
  by_cases hg : g = 0
  · subst hg; simp
  · have hgf : g * f ≠ 0 := mul_ne_zero hg f.ne_zero
    rw [mem_riemannRochSpace_iff_ord _ hg, mem_riemannRochSpace_iff_ord _ hgf]
    refine forall_congr' fun v => ?_
    rw [ord_mul' v hg f.ne_zero]
    simp only [Finsupp.add_apply, div_apply]
    omega

theorem exists_residue_map (a : Divisor Fq k) (v : Place Fq k) :
    ∃ ψ : a.riemannRochSpace →ₗ[Fq] v.residueField,
      ∀ f : a.riemannRochSpace, ψ f = 0 → v.valuation (f : k) < WithZero.exp (a v) := by
  obtain ⟨π, hπ⟩ := v.valuation_surjective (WithZero.exp (-1))
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
  refine ⟨ψ, fun f hf => ?_⟩
  have h1 := Place.valuation_lt_one_of_mem_maximalIdeal' v _
    ((IsLocalRing.residue_eq_zero_iff _).mp hf)
  have h2 : v.valuation ((f : k) * π ^ (a v)) < 1 := h1
  rw [hmul] at h2
  have h3 : v.valuation (f : k) = (v.valuation (f : k) * WithZero.exp (-a v)) * WithZero.exp (a v) := by
    rw [mul_assoc, ← WithZero.exp_add]; simp
  rw [h3]
  calc _ < 1 * WithZero.exp (a v) := mul_lt_mul_of_pos_right h2 (by simp)
    _ = _ := one_mul _

/-- $\lambda(\mathfrak a+v)\le\lambda(\mathfrak a)+\deg v$. -/
theorem ell_add_single_le (a : Divisor Fq k) (v : Place Fq k) :
    (a + Finsupp.single v 1).ell ≤ a.ell + v.degree := by
  obtain ⟨ψ, hψ⟩ := exists_residue_map (a + Finsupp.single v 1) v
  have hker : ∀ f : (a + Finsupp.single v 1).riemannRochSpace, ψ f = 0 → (f : k) ∈ a.riemannRochSpace := by
    intro f hf
    have h := hψ f hf
    have hf2 := (mem_riemannRochSpace_iff _ _).mp f.2
    rw [mem_riemannRochSpace_iff]
    intro w
    by_cases hw : w = v
    · subst hw
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at h
      by_cases hf0 : w.valuation (f : k) = 0
      · rw [hf0]; exact zero_le
      · rw [← WithZero.exp_log hf0] at h ⊢
        rw [WithZero.exp_lt_exp] at h
        exact WithZero.exp_le_exp.mpr (by omega)
    · simpa [Finsupp.single_apply, Ne.symm hw] using hf2 w
  let ι : LinearMap.ker ψ →ₗ[Fq] a.riemannRochSpace :=
    LinearMap.codRestrict _ ((Submodule.subtype _) ∘ₗ (LinearMap.ker ψ).subtype)
      (fun x => hker x.1 (LinearMap.mem_ker.mp x.2))
  have hι : Function.Injective ι := by
    intro x y hxy
    have := congrArg (fun z : a.riemannRochSpace => (z : k)) hxy
    exact Subtype.ext (Subtype.ext this)
  haveI : Module.Finite Fq v.residueField := Module.Finite.of_finite
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  have h2 : Module.finrank Fq (LinearMap.range ψ) ≤ v.degree := Submodule.finrank_le _
  have h3 : Module.finrank Fq (LinearMap.ker ψ) ≤ a.ell := LinearMap.finrank_le_finrank_of_injective hι
  unfold ell at *
  omega

/-- $\lambda(\mathfrak b)\le\lambda(\mathfrak a)+\deg\mathfrak b-\deg\mathfrak a$ for $\mathfrak a\le\mathfrak b$. -/
theorem ell_le_of_le {a b : Divisor Fq k} (h : a ≤ b) :
    (b.ell : ℤ) ≤ a.ell + (deg b - deg a) := by
  suffices H : ∀ (n : ℕ) (a b : Divisor Fq k), a ≤ b → (deg (b - a)).toNat = n →
      (b.ell : ℤ) ≤ a.ell + (deg b - deg a) from H _ a b h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab hn
    by_cases heq : a = b
    · subst heq; simp
    · obtain ⟨v, hv⟩ : ∃ v, a v ≠ b v := by
        by_contra hcon
        push Not at hcon
        exact heq (Finsupp.ext hcon)
      have hlt : a v < b v := lt_of_le_of_ne (hab v) hv
      have hab' : a + Finsupp.single v 1 ≤ b := by
        intro w
        by_cases hw : w = v
        · subst hw; simp; omega
        · simpa [Finsupp.single_apply, Ne.symm hw] using hab w
      have hd : deg (b - (a + Finsupp.single v 1)) = deg (b - a) - v.degree := by
        rw [sub_add_eq_sub_sub, map_sub, deg_single]; simp
      have hdp := v.degree_pos
      have hnn : 0 ≤ deg (b - a) := deg_nonneg (sub_nonneg.mpr hab)
      have hlt' : (deg (b - (a + Finsupp.single v 1))).toNat < n := by
        have hnn2 := deg_nonneg (sub_nonneg.mpr hab')
        rw [hd] at hnn2
        rw [← hn, hd]
        omega
      have := ih _ hlt' _ b hab' rfl
      have h2 := ell_add_single_le a v
      rw [map_add, deg_single] at this
      simp only [one_mul] at this
      omega

theorem deg_sub_ell_mono {a b : Divisor Fq k} (h : a ≤ b) :
    deg a - (a.ell : ℤ) ≤ deg b - b.ell := by
  have := ell_le_of_le h
  omega

/-- Multiplication by $\xi$: $A(\mathfrak a+\operatorname{div}\xi)\cong A(\mathfrak a)$. -/
def riemannRochSpaceDivEquiv (a : Divisor Fq k) (f : kˣ) :
    (a + div f).riemannRochSpace ≃ₗ[Fq] a.riemannRochSpace where
  toFun g := ⟨g.1 * f, (mem_add_div_iff a f g.1).1 g.2⟩
  invFun h := ⟨h.1 * ((f⁻¹ : kˣ) : k), (mem_add_div_iff a f _).2 (by
    have : h.1 * ((f⁻¹ : kˣ) : k) * (f : k) = h.1 := by simp
    rw [this]; exact h.2)⟩
  map_add' g h := by ext; simp [add_mul]
  map_smul' c g := by ext; simp [Algebra.smul_def, mul_assoc]
  left_inv g := by ext; simp
  right_inv h := by ext; simp

theorem ell_add_div (a : Divisor Fq k) (f : kˣ) : (a + div f).ell = a.ell :=
  (riemannRochSpaceDivEquiv a f).finrank_eq

theorem riemannRochSpace_eq_bot_of_deg_neg {a : Divisor Fq k} (ha : deg a < 0) :
    a.riemannRochSpace = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  by_contra hne
  have h1 : 0 ≤ a + Divisor.div (Units.mk0 f hne) :=
    (nonneg_add_div_iff a (Units.mk0 f hne)).mpr hf
  have h2 := Divisor.deg_nonneg h1
  rw [map_add, deg_div_eq_zero] at h2
  omega

theorem ell_eq_zero_of_deg_neg' {a : Divisor Fq k} (ha : deg a < 0) : a.ell = 0 := by
  unfold ell
  rw [riemannRochSpace_eq_bot_of_deg_neg ha]
  exact finrank_bot Fq k

/-- The pole divisor $B=(x)_\infty$ of a separating element has degree $[k:\mathbb F_q(x)]$. -/
theorem deg_pole_divisor (s : SeparatingElement Fq k) :
    deg (div s.inv.unit : Divisor Fq k).pos = (Module.finrank Fq⟮s.x⟯ k : ℤ) := by
  have h2 := s.inv.deg_zeros
  have e : Module.finrank Fq⟮s.inv.x⟯ k = Module.finrank Fq⟮s.x⟯ k := by
    rw [SeparatingElement.inv_x, adjoin_inv_eq]
  rw [e] at h2
  exact h2

theorem linearIndependent_basis_mul_pow (s : SeparatingElement Fq k) (m : ℕ)
    (b : Module.Basis (Fin (Module.finrank Fq⟮s.x⟯ k)) Fq⟮s.x⟯ k) :
    LinearIndependent Fq (fun ij : Fin (Module.finrank Fq⟮s.x⟯ k) × Fin (m + 1) =>
      b ij.1 * s.x ^ (ij.2 : ℕ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hinj : Function.Injective (Polynomial.aeval (R := Fq) s.x) :=
    transcendental_iff_injective.mp s.transcendental
  let e : Fin (Module.finrank Fq⟮s.x⟯ k) → Fq⟮s.x⟯ := fun i =>
    ∑ j : Fin (m + 1), algebraMap Fq Fq⟮s.x⟯ (g (i, j)) * (AdjoinSimple.gen Fq s.x) ^ (j : ℕ)
  have he : ∀ i, ((e i : Fq⟮s.x⟯) : k) = ∑ j : Fin (m + 1), algebraMap Fq k (g (i, j)) * s.x ^ (j : ℕ) := by
    intro i
    simp [e]
  have hsum : ∑ i, e i • b i = 0 := by
    rw [← hg, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.smul_def, he, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    ring
  have h0 := Fintype.linearIndependent_iff.mp b.linearIndependent e hsum
  intro ⟨i, j⟩
  have h1 : ∑ j : Fin (m + 1), algebraMap Fq k (g (i, j)) * s.x ^ (j : ℕ) = 0 := by
    rw [← he, h0 i]; rfl
  have h2 : Polynomial.aeval (R := Fq) s.x (∑ j : Fin (m + 1), Polynomial.C (g (i, j)) * Polynomial.X ^ (j : ℕ)) = 0 := by
    simpa [map_sum] using h1
  have h3 := hinj (h2.trans (map_zero _).symm)
  have h4 := congrArg (fun p => p.coeff (j : ℕ)) h3
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at h4
  rw [Finset.sum_eq_single j] at h4
  · simpa using h4
  · intro j' _ hj'
    rw [if_neg]
    intro h
    exact hj' (Fin.ext h.symm)
  · simp

theorem ell_lower_bound (s : SeparatingElement Fq k) :
    ∃ C : Divisor Fq k, 0 ≤ C ∧ ∀ m : ℕ,
      Module.finrank Fq⟮s.x⟯ k * (m + 1) ≤ (m • (div s.inv.unit : Divisor Fq k).pos + C).ell := by
  classical
  haveI : FiniteDimensional Fq⟮s.x⟯ k :=
    FunctionField.finiteDimensional_of_adjoin_transcendental s.transcendental
  let b := Module.finBasis Fq⟮s.x⟯ k
  let u : Fin (Module.finrank Fq⟮s.x⟯ k) → kˣ := fun i => Units.mk0 (b i) (b.ne_zero i)
  let C : Divisor Fq k := ∑ i, (-(div (u i))).pos
  refine ⟨C, Finset.sum_nonneg (fun i _ v => by simp), fun m => ?_⟩
  have hC : ∀ i v, -v.ord (b i) ≤ C v := by
    intro i v
    have h1 : (-(div (u i))).pos v ≤ C v := by
      simp only [C, Finsupp.finset_sum_apply]
      exact Finset.single_le_sum (f := fun i => (-(div (u i))).pos v)
        (fun i _ => by simp) (Finset.mem_univ i)
    simp only [pos_apply, Finsupp.coe_neg, Pi.neg_apply, div_apply] at h1
    have := le_max_left (-v.ord ((u i : kˣ) : k)) 0
    exact this.trans h1
  have hmem : ∀ ij : Fin (Module.finrank Fq⟮s.x⟯ k) × Fin (m + 1),
      b ij.1 * s.x ^ (ij.2 : ℕ) ∈
        (m • (div s.inv.unit : Divisor Fq k).pos + C).riemannRochSpace := by
    intro ij
    have hb0 : (b ij.1 : k) ≠ 0 := b.ne_zero ij.1
    have hx0 := s.x_ne_zero
    rw [mem_riemannRochSpace_iff_ord _ (mul_ne_zero hb0 (pow_ne_zero _ hx0))]
    intro v
    rw [ord_mul' v hb0 (pow_ne_zero _ hx0), ord_pow' v hx0]
    have h1 := hC ij.1 v
    have h2 : ((div s.inv.unit : Divisor Fq k).pos v) = max (- v.ord s.x) 0 := by
      simp only [pos_apply, div_apply]
      show max (v.ord (s.inv.x)) 0 = _
      rw [SeparatingElement.inv_x, ord_inv' v hx0]
    have hj : (ij.2 : ℕ) ≤ m := Nat.lt_succ_iff.mp ij.2.2
    have hj' : ((ij.2 : ℕ) : ℤ) ≤ m := by exact_mod_cast hj
    simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul, h2]
    rcases le_total 0 (v.ord s.x) with h | h
    · rw [max_eq_right (by omega)]
      nlinarith
    · rw [max_eq_left (by omega)]
      have : ((ij.2 : ℕ) : ℤ) * (-v.ord s.x) ≤ (m : ℤ) * (-v.ord s.x) :=
        mul_le_mul_of_nonneg_right hj' (by omega)
      nlinarith
  let w : Fin (Module.finrank Fq⟮s.x⟯ k) × Fin (m + 1) → (m • (div s.inv.unit : Divisor Fq k).pos + C).riemannRochSpace :=
    fun ij => ⟨b ij.1 * s.x ^ (ij.2 : ℕ), hmem ij⟩
  have hli : LinearIndependent Fq w :=
    LinearIndependent.of_comp (Submodule.subtype _) (linearIndependent_basis_mul_pow s m b)
  have := hli.fintype_card_le_finrank
  simpa [Divisor.ell] using this

/-- Riemann's inequality along multiples of the pole divisor. -/
theorem exists_pole_bound (s : SeparatingElement Fq k) :
    ∃ C : Divisor Fq k, ∀ m : ℕ,
      (Module.finrank Fq⟮s.x⟯ k : ℤ) * (m + 1) - deg C ≤
        ((m • (div s.inv.unit : Divisor Fq k).pos).ell : ℤ) := by
  obtain ⟨C, hC0, hC⟩ := ell_lower_bound s
  refine ⟨C, fun m => ?_⟩
  have h1 := ell_le_of_le (le_add_of_nonneg_right hC0 : m • (div s.inv.unit : Divisor Fq k).pos ≤
    m • (div s.inv.unit : Divisor Fq k).pos + C)
  have h2 := hC m
  rw [map_add] at h1
  have h3 : ((Module.finrank Fq⟮s.x⟯ k * (m + 1) : ℕ) : ℤ) ≤ _ := Nat.cast_le.mpr h2
  push_cast at h3
  linarith

/-- The Riemann bound for the multiples of the pole divisor of a separating element. -/
theorem exists_pole_gamma (s : SeparatingElement Fq k) :
    ∃ γ : ℤ, ∀ m : ℕ, deg (m • (div s.inv.unit : Divisor Fq k).pos) -
      ((m • (div s.inv.unit : Divisor Fq k).pos).ell : ℤ) ≤ γ := by
  obtain ⟨C, hC⟩ := exists_pole_bound s
  refine ⟨deg C - Module.finrank Fq⟮s.x⟯ k, fun m => ?_⟩
  have h1 := hC m
  rw [map_nsmul, deg_pole_divisor]
  simp only [nsmul_eq_mul]
  linarith

/-- **Riemann's theorem**: $\deg\mathfrak a-\lambda(\mathfrak a)$ is bounded above. -/
theorem exists_deg_sub_ell_le : ∃ γ : ℤ, ∀ a : Divisor Fq k, deg a - (a.ell : ℤ) ≤ γ := by
  obtain ⟨s⟩ := weil_III_2_lemma1 (Fq := Fq) (k := k)
  obtain ⟨C, hC⟩ := exists_pole_bound s
  obtain ⟨γ, hγ⟩ := exists_pole_gamma s
  haveI : FiniteDimensional Fq⟮s.x⟯ k :=
    FunctionField.finiteDimensional_of_adjoin_transcendental s.transcendental
  have hn : 0 < Module.finrank Fq⟮s.x⟯ k := Module.finrank_pos
  refine ⟨γ, fun a => ?_⟩
  set B : Divisor Fq k := (div s.inv.unit : Divisor Fq k).pos with hB
  set D : Divisor Fq k := a.pos with hD
  have hD0 : 0 ≤ D := fun v => by simp [hD]
  have hDa : a ≤ D := fun v => by simp [hD]
  set m : ℕ := (deg C + deg D).toNat with hm
  have h1 := hC m
  have h2 := ell_le_of_le (sub_le_self (m • B) hD0)
  rw [map_sub] at h2
  have hn' : (1 : ℤ) ≤ Module.finrank Fq⟮s.x⟯ k := by exact_mod_cast hn
  have hm' : deg C + deg D ≤ m := by omega
  have hpos : 0 < ((m • B - D).ell : ℤ) := by nlinarith
  have hne : (m • B - D).riemannRochSpace ≠ ⊥ := by
    intro h
    have : (m • B - D).ell = 0 := by unfold ell; rw [h]; exact finrank_bot Fq k
    omega
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let u : kˣ := Units.mk0 f hf0
  have hu : 0 ≤ (m • B - D) + div u := (nonneg_add_div_iff _ u).mpr hf
  have hle : a + div u⁻¹ ≤ m • B := by
    rw [div_inv]
    intro v
    have := hu v
    have := hDa v
    simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.coe_neg, Pi.neg_apply,
      Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub] at *
    omega
  have h3 := deg_sub_ell_mono hle
  rw [ell_add_div, map_add, deg_div_eq_zero, add_zero] at h3
  have := hγ m
  omega

end Divisor

/-- **The class number is finite**: $D_0(k)/P(k)$ is finite (Weil VI.§1, text p. 97). -/
@[kb "weil1973bnt" "Ch. VI, text p.97 (D_0(k)/P(k) is finite), function fields"]
theorem finite_classGroup0 : Finite (ClassGroup0 Fq k) := by
  classical
  obtain ⟨γ, hγ⟩ := Divisor.exists_deg_sub_ell_le (Fq := Fq) (k := k)
  obtain ⟨P⟩ := Place.nonempty (Fq := Fq) (k := k)
  have hP := P.degree_pos
  set m : ℕ := γ.toNat + 1 with hm
  have hmP : γ < (m : ℤ) * P.degree := by
    have : (1 : ℤ) ≤ P.degree := by exact_mod_cast hP
    have : (γ.toNat : ℤ) ≥ γ := Int.self_le_toNat γ
    push_cast [hm]
    nlinarith
  let rep : ClassGroup0 Fq k → Divisor.deg.ker :=
    Function.surjInv QuotientAddGroup.mk_surjective
  have hrep : ∀ c, (QuotientAddGroup.mk (rep c) : ClassGroup0 Fq k) = c := fun c =>
    Function.surjInv_eq QuotientAddGroup.mk_surjective c
  have hex : ∀ c : ClassGroup0 Fq k, ∃ u : kˣ,
      0 ≤ (rep c : Divisor Fq k) + m • Finsupp.single P 1 + Divisor.div u := by
    intro c
    set a : Divisor Fq k := (rep c : Divisor Fq k) + m • Finsupp.single P 1 with ha
    have hdeg : Divisor.deg a = (m : ℤ) * P.degree := by
      have : Divisor.deg (rep c : Divisor Fq k) = 0 := (rep c).2
      rw [ha, map_add, this, map_nsmul, Divisor.deg_single]
      simp
    have h1 := hγ a
    have hpos : 0 < (a.ell : ℤ) := by omega
    have hne : a.riemannRochSpace ≠ ⊥ := by
      intro h
      have : a.ell = 0 := by unfold Divisor.ell; rw [h]; exact finrank_bot Fq k
      omega
    obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨Units.mk0 f hf0, (nonneg_add_div_iff a _).mpr hf⟩
  choose u hu using hex
  let F : ClassGroup0 Fq k → {E : Divisor Fq k // 0 ≤ E ∧ Divisor.deg E = (m : ℤ) * P.degree} :=
    fun c => ⟨(rep c : Divisor Fq k) + m • Finsupp.single P 1 + Divisor.div (u c), hu c, by
      have : Divisor.deg (rep c : Divisor Fq k) = 0 := (rep c).2
      rw [map_add, map_add, this, Divisor.deg_div_eq_zero, map_nsmul, Divisor.deg_single]
      simp⟩
  haveI : Finite {E : Divisor Fq k // 0 ≤ E ∧ Divisor.deg E = (m : ℤ) * P.degree} :=
    (Divisor.finite_setOf_effective_deg_eq ((m : ℤ) * P.degree)).to_subtype
  refine Finite.of_injective F fun c c' h => ?_
  have h' : (rep c : Divisor Fq k) + m • Finsupp.single P 1 + Divisor.div (u c) =
      (rep c' : Divisor Fq k) + m • Finsupp.single P 1 + Divisor.div (u c') :=
    congrArg Subtype.val h
  rw [← hrep c, ← hrep c', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf,
    mem_principalDivisors_iff]
  refine ⟨u c * (u c')⁻¹, ?_⟩
  rw [Divisor.div_mul, Divisor.div_inv]
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
  rw [← sub_eq_zero]
  have e : (Divisor.div (u c) + -Divisor.div (u c') : Divisor Fq k) - (-(rep c : Divisor Fq k) + (rep c' : Divisor Fq k)) =
      ((rep c : Divisor Fq k) + m • Finsupp.single P 1 + Divisor.div (u c)) -
        ((rep c' : Divisor Fq k) + m • Finsupp.single P 1 + Divisor.div (u c')) := by abel
  rw [e, h', sub_self]

end NumberFieldKB.WeilBNT.FF
