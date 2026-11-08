import NumberFieldKB.WeilBNT.FunctionField.HeckeRayFF

/-!
# Functional equation of $L(u,\omega)$ for unramified $\omega$ (Weil VII.§7, Thm. 6, conductor $0$)

Let $\chi$ be a character of the divisor group of $k$ trivial on principal divisors and nontrivial on some divisor of
degree $0$ (for an everywhere unramified non-principal Hecke character $\omega$, $\chi=\chi_\omega$, `HeckeLFF.lean`),
and $L(u,\chi)=\sum_{\mathfrak a\succ0}\chi(\mathfrak a)u^{\deg\mathfrak a}$ (`divisorSeries χ univ`).

* **`divisorSeries_functional_equation`**: if $\mathbb F_q$ is the field of constants, for $0\le n\le2g-2$ the
  coefficients satisfy $c_n(\chi)=\chi(\mathfrak c)\,q^{\,n-g+1}\,c_{2g-2-n}(\chi^{-1})$, $\mathfrak c$ a canonical
  divisor; equivalently $L(u,\chi)=\chi(\mathfrak c)\,(q^{1/2}u)^{2g-2}\,L(1/qu,\chi^{-1})$.
* `coeff_divisorSeries_top`: the coefficient of $u^{2g-2}$ is $\chi(\mathfrak c)\,q^{g-1}\ne0$.
* **`weil_VII_7_thm6_unramified_exact`**, **`weil_VII_7_thm6_unramified_fe`**: for an everywhere unramified
  non-principal $\omega$, $L(u,\omega)$ is a polynomial of degree exactly $2g-2$ with
  $P(u,\omega)=\omega(\mathfrak c)(q^{1/2}u)^{2g-2}P(1/qu,\omega^{-1})$ (Weil's $\kappa_\omega(b)=\omega(\mathfrak c)$
  here, the local constants being trivial).

Proof (Riemann–Roch, as for the zeta function): grouping effective divisors by classes,
$(q-1)c_n=\sum_{\deg\bar{\mathfrak a}=n}\chi(\bar{\mathfrak a})(q^{\lambda(\mathfrak a)}-1)$, the $-1$'s cancel because
$\chi$ is nontrivial on the classes of degree $0$, and $\bar{\mathfrak a}\mapsto\bar{\mathfrak c}-\bar{\mathfrak a}$ with
$\lambda(\mathfrak a)=\lambda(\mathfrak c-\mathfrak a)+\deg\mathfrak a-g+1$ gives the symmetry.
-/

open scoped WithZero

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

/-- The sum $\sum_{\mathfrak a\succ0,\ \deg\mathfrak a=m}\chi(\mathfrak a)$ over effective divisors of degree `m`. -/
def effSumInt (χ : Multiplicative (Divisor Fq k) →* ℂˣ) (m : ℤ) : ℂ :=
  ∑ a ∈ (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) m).toFinset,
    ((χ (Multiplicative.ofAdd a) : ℂˣ) : ℂ)

/-- The coefficients of `divisorSeries χ univ` are the sums `effSumInt χ n`. -/
theorem coeff_divisorSeries_univ (χ : Multiplicative (Divisor Fq k) →* ℂˣ) (n : ℕ) :
    PowerSeries.coeff n (divisorSeries χ Set.univ) = effSumInt χ (n : ℤ) := by
  classical
  rw [divisorSeries, PowerSeries.coeff_mk, effSumInt, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp

/-- A character trivial on principal divisors takes equal values on divisors differing by a principal one. -/
theorem chi_eq_of_sub_mem (χ : Multiplicative (Divisor Fq k) →* ℂˣ)
    (hP : ∀ f : kˣ, χ (Multiplicative.ofAdd (Divisor.div f)) = 1) {a b : Divisor Fq k}
    (h : a - b ∈ principalDivisors Fq k) : χ (Multiplicative.ofAdd a) = χ (Multiplicative.ofAdd b) := by
  obtain ⟨u, hu⟩ := (mem_principalDivisors_iff _).mp h
  have : a = b + Divisor.div u := by rw [hu]; abel
  rw [this, ofAdd_add, map_mul, hP u, mul_one]

/-- Equality of `ell` on divisors differing by a principal divisor. -/
theorem ell_eq_of_sub_mem {a b : Divisor Fq k} (h : a - b ∈ principalDivisors Fq k) : a.ell = b.ell := by
  obtain ⟨u, hu⟩ := (mem_principalDivisors_iff _).mp h
  have : a = b + Divisor.div u := by rw [hu]; abel
  rw [this, Divisor.ell_add_div]

/-- A chosen degree-$0$ divisor representing a class of $D_0/P$. -/
def repKer (C : ClassGroup0 Fq k) : (Divisor.deg (Fq := Fq) (k := k)).ker :=
  Function.surjInv (f := (QuotientAddGroup.mk : (Divisor.deg (Fq := Fq) (k := k)).ker → ClassGroup0 Fq k))
    QuotientAddGroup.mk_surjective C

/-- `repKer C` represents `C`. -/
theorem mk_repKer (C : ClassGroup0 Fq k) :
    (QuotientAddGroup.mk (repKer C) : ClassGroup0 Fq k) = C :=
  Function.surjInv_eq (f := (QuotientAddGroup.mk : (Divisor.deg (Fq := Fq) (k := k)).ker → ClassGroup0 Fq k))
    QuotientAddGroup.mk_surjective C

/-- `repKer C` has degree `0`. -/
theorem deg_repKer (C : ClassGroup0 Fq k) : Divisor.deg (repKer C : Divisor Fq k) = 0 :=
  AddMonoidHom.mem_ker.mp (repKer C).2

/-- The chosen divisor of degree `m` in the class `C` (relative to a divisor `b₁`, normally of degree `1`). -/
def baseDiv (b₁ : Divisor Fq k) (m : ℤ) (C : ClassGroup0 Fq k) : Divisor Fq k :=
  m • b₁ + (repKer C : Divisor Fq k)

/-- `baseDiv b₁ m C` has degree `m`. -/
theorem deg_baseDiv {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) (m : ℤ) (C : ClassGroup0 Fq k) :
    Divisor.deg (baseDiv b₁ m C) = m := by
  simp [baseDiv, hb, deg_repKer]

/-- The class of degree $0$ of `a - deg a • b₁`. -/
def clsOf {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) (a : Divisor Fq k) : ClassGroup0 Fq k :=
  QuotientAddGroup.mk (⟨a - Divisor.deg a • b₁, by
    apply AddMonoidHom.mem_ker.mpr
    rw [map_sub, map_zsmul, hb]; simp⟩ : (Divisor.deg (Fq := Fq) (k := k)).ker)

/-- A divisor of degree `m` lies in the class `C` iff it differs from `baseDiv b₁ m C` by a principal divisor. -/
theorem clsOf_eq_iff {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) {m : ℤ} {a : Divisor Fq k}
    (ha : Divisor.deg a = m) (C : ClassGroup0 Fq k) :
    clsOf hb a = C ↔ a - baseDiv b₁ m C ∈ principalDivisors Fq k := by
  rw [show (clsOf hb a = C) = (clsOf hb a = QuotientAddGroup.mk (repKer C)) by rw [mk_repKer]]
  unfold clsOf
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  have : a - baseDiv b₁ m C = -((-(a - Divisor.deg a • b₁)) + (repKer C : Divisor Fq k)) := by
    simp only [baseDiv, ha]; abel
  rw [this, neg_mem_iff]
  simp

/-- Class sum: $(q-1)\sum_{\deg\mathfrak a=m}\chi(\mathfrak a)=\sum_C\chi(\mathfrak b_C)(q^{\lambda(\mathfrak b_C)}-1)$. -/
theorem class_sum (hc : IsConstantField Fq k) (χ : Multiplicative (Divisor Fq k) →* ℂˣ)
    (hP : ∀ f : kˣ, χ (Multiplicative.ofAdd (Divisor.div f)) = 1) [Fintype (ClassGroup0 Fq k)]
    {b₁ : Divisor Fq k} (hb : Divisor.deg b₁ = 1) (m : ℤ) :
    ((Nat.card Fq : ℂ) - 1) * effSumInt χ m =
      ∑ C : ClassGroup0 Fq k, ((χ (Multiplicative.ofAdd (baseDiv b₁ m C)) : ℂˣ) : ℂ) *
        ((Nat.card Fq : ℂ) ^ (baseDiv b₁ m C).ell - 1) := by
  classical
  have hq : 2 ≤ Nat.card Fq := Finite.one_lt_card
  set A := (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) m).toFinset with hA
  have hmemA : ∀ a, a ∈ A ↔ 0 ≤ a ∧ Divisor.deg a = m := fun a => by simp [hA]
  have h1 : effSumInt χ m = ∑ C : ClassGroup0 Fq k, ∑ a ∈ A with clsOf hb a = C,
      ((χ (Multiplicative.ofAdd a) : ℂˣ) : ℂ) :=
    (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  have hdegb := deg_baseDiv hb m C
  have hfilt : (A.filter fun a => clsOf hb a = C) =
      A.filter fun a => a - baseDiv b₁ m C ∈ principalDivisors Fq k :=
    Finset.filter_congr fun a ha => clsOf_eq_iff hb ((hmemA a).mp ha).2 C
  rw [hfilt, Finset.sum_congr rfl (fun a ha =>
      show ((χ (Multiplicative.ofAdd a) : ℂˣ) : ℂ) =
        ((χ (Multiplicative.ofAdd (baseDiv b₁ m C)) : ℂˣ) : ℂ) by
        rw [chi_eq_of_sub_mem χ hP (Finset.mem_filter.mp ha).2]),
    Finset.sum_const, nsmul_eq_mul, hA, FFHeckeCharacter.card_filter_eq_effClassCount m _ hdegb]
  have hspec := effClassCount_spec_of_fd hc (baseDiv b₁ m C)
    (Divisor.finiteDimensional_riemannRochSpace _)
  have h2 : ((Nat.card Fq : ℂ) - 1) * (effClassCount (baseDiv b₁ m C) : ℂ) + 1 =
      (Nat.card Fq : ℂ) ^ (baseDiv b₁ m C).ell := by
    have := congrArg (Nat.cast : ℕ → ℂ) hspec
    push_cast [Nat.cast_sub (by omega : 1 ≤ Nat.card Fq)] at this
    exact this
  rw [← h2]
  ring

/-- If $\chi$ is nontrivial on a degree-$0$ divisor, the sum of $\chi$ over the chosen representatives of degree `m`
vanishes. -/
theorem sum_class_eq_zero (χ : Multiplicative (Divisor Fq k) →* ℂˣ)
    (hP : ∀ f : kˣ, χ (Multiplicative.ofAdd (Divisor.div f)) = 1) [Fintype (ClassGroup0 Fq k)]
    (b₁ : Divisor Fq k) (m : ℤ) (d : Divisor Fq k) (hd0 : Divisor.deg d = 0)
    (hχ : χ (Multiplicative.ofAdd d) ≠ 1) :
    ∑ C : ClassGroup0 Fq k, ((χ (Multiplicative.ofAdd (baseDiv b₁ m C)) : ℂˣ) : ℂ) = 0 := by
  set δ : ClassGroup0 Fq k :=
    QuotientAddGroup.mk (⟨d, AddMonoidHom.mem_ker.mpr hd0⟩ : (Divisor.deg (Fq := Fq) (k := k)).ker) with hδ
  have key : ∀ C : ClassGroup0 Fq k,
      ((χ (Multiplicative.ofAdd (baseDiv b₁ m (C + δ))) : ℂˣ) : ℂ) =
        ((χ (Multiplicative.ofAdd (baseDiv b₁ m C)) : ℂˣ) : ℂ) * ((χ (Multiplicative.ofAdd d) : ℂˣ) : ℂ) := by
    intro C
    have hmem : (repKer (C + δ) - repKer C - ⟨d, AddMonoidHom.mem_ker.mpr hd0⟩ :
        (Divisor.deg (Fq := Fq) (k := k)).ker) ∈
        (principalDivisors Fq k).addSubgroupOf (Divisor.deg (Fq := Fq) (k := k)).ker := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_sub, mk_repKer,
        mk_repKer]
      show C + δ - C - δ = 0
      abel
    have hmem' := AddSubgroup.mem_addSubgroupOf.mp hmem
    have e : baseDiv b₁ m (C + δ) - (baseDiv b₁ m C + d) =
        ((repKer (C + δ) - repKer C - ⟨d, AddMonoidHom.mem_ker.mpr hd0⟩ :
          (Divisor.deg (Fq := Fq) (k := k)).ker) : Divisor Fq k) := by
      simp only [baseDiv, AddSubgroup.coe_sub]; abel
    rw [chi_eq_of_sub_mem χ hP (a := baseDiv b₁ m (C + δ)) (b := baseDiv b₁ m C + d) (by rw [e]; exact hmem'),
      ofAdd_add, map_mul, Units.val_mul]
  have hcomp := Equiv.sum_comp (Equiv.addRight δ)
    (fun C => ((χ (Multiplicative.ofAdd (baseDiv b₁ m C)) : ℂˣ) : ℂ))
  simp only [Equiv.coe_addRight] at hcomp
  simp_rw [key] at hcomp
  rw [← Finset.sum_mul] at hcomp
  have hne : ((χ (Multiplicative.ofAdd d) : ℂˣ) : ℂ) ≠ 1 := fun h => hχ (Units.val_eq_one.mp h)
  have : (∑ C : ClassGroup0 Fq k, ((χ (Multiplicative.ofAdd (baseDiv b₁ m C)) : ℂˣ) : ℂ)) *
      (1 - ((χ (Multiplicative.ofAdd d) : ℂˣ) : ℂ)) = 0 := by
    linear_combination hcomp.symm
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hne

/-- The only effective divisor of degree `0` is `0`, so the sum is `1`. -/
theorem effSumInt_zero (χ : Multiplicative (Divisor Fq k) →* ℂˣ) : effSumInt χ 0 = 1 := by
  have hset : (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) 0).toFinset = {0} := by
    ext a
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact Divisor.eq_zero_of_deg_eq_zero h1 h2
    · rintro rfl
      simp
  rw [effSumInt, hset]
  simp

/-- Under the hypotheses of the functional equation the genus is positive (otherwise $\sum_{\deg=0}\chi=1$
contradicts the vanishing of $\sum_C\chi(\mathfrak b_C)$). -/
theorem genusInt_pos (hc : IsConstantField Fq k) (χ : Multiplicative (Divisor Fq k) →* ℂˣ)
    (hP : ∀ f : kˣ, χ (Multiplicative.ofAdd (Divisor.div f)) = 1)
    (hd : ∃ d : Divisor Fq k, Divisor.deg d = 0 ∧ χ (Multiplicative.ofAdd d) ≠ 1) :
    1 ≤ Rep.genusInt Fq k := by
  classical
  by_contra hg
  have hg0 := genusInt_nonneg hc
  haveI : Finite (ClassGroup0 Fq k) := finite_classGroup0
  haveI : Fintype (ClassGroup0 Fq k) := Fintype.ofFinite _
  obtain ⟨b₁, hb₁⟩ := weil_VII_5_cor5_ff hc
  obtain ⟨d, hd0, hχd⟩ := hd
  have hq2 : 2 ≤ Nat.card Fq := Finite.one_lt_card
  have hq1 : ((Nat.card Fq : ℂ) - 1) ≠ 0 := by
    intro h
    have h1 : (Nat.card Fq : ℂ) = 1 := by linear_combination h
    have h2 : Nat.card Fq = 1 := by exact_mod_cast h1
    omega
  have h1 := class_sum hc χ hP hb₁ 0
  rw [effSumInt_zero] at h1
  have hdc := (weil_VI_2_cor1 hc).1
  have hell : ∀ C, (baseDiv b₁ 0 C).ell = 1 := by
    intro C
    have h := weil_VI_2_thm2 (baseDiv b₁ 0 C)
    have h0 : (canonical Fq k - baseDiv b₁ 0 C).ell = 0 :=
      Divisor.ell_eq_zero_of_deg_neg' (by rw [map_sub, hdc, deg_baseDiv hb₁]; omega)
    rw [h0, deg_baseDiv hb₁] at h
    omega
  simp_rw [hell, pow_one, ← Finset.sum_mul] at h1
  rw [sum_class_eq_zero χ hP b₁ 0 d hd0 hχd, zero_mul, mul_one] at h1
  exact hq1 h1

/-- **Functional equation** of $L(u,\chi)$ for a class character $\chi$ nontrivial in degree $0$, coefficientwise:
$c_n(\chi)=\chi(\mathfrak c)\,q^{n-g+1}\,c_{2g-2-n}(\chi^{-1})$ for $0\le n\le 2g-2$. -/
theorem divisorSeries_functional_equation (hc : IsConstantField Fq k)
    (χ : Multiplicative (Divisor Fq k) →* ℂˣ)
    (hP : ∀ f : kˣ, χ (Multiplicative.ofAdd (Divisor.div f)) = 1)
    (hd : ∃ d : Divisor Fq k, Divisor.deg d = 0 ∧ χ (Multiplicative.ofAdd d) ≠ 1)
    (n : ℕ) (hn : (n : ℤ) ≤ 2 * Rep.genusInt Fq k - 2) :
    PowerSeries.coeff n (divisorSeries χ Set.univ) =
      ((χ (Multiplicative.ofAdd (canonical Fq k)) : ℂˣ) : ℂ) *
        (Nat.card Fq : ℂ) ^ ((n : ℤ) - Rep.genusInt Fq k + 1) *
        PowerSeries.coeff (2 * Rep.genusInt Fq k - 2 - n).toNat (divisorSeries χ⁻¹ Set.univ) := by
  classical
  haveI : Finite (ClassGroup0 Fq k) := finite_classGroup0
  haveI : Fintype (ClassGroup0 Fq k) := Fintype.ofFinite _
  obtain ⟨b₁, hb₁⟩ := weil_VII_5_cor5_ff hc
  obtain ⟨d, hd0, hχd⟩ := hd
  have hq2 : 2 ≤ Nat.card Fq := Finite.one_lt_card
  have hqne : (Nat.card Fq : ℂ) ≠ 0 := by exact_mod_cast (by omega : Nat.card Fq ≠ 0)
  have hq1 : ((Nat.card Fq : ℂ) - 1) ≠ 0 := by
    intro h
    have h1 : (Nat.card Fq : ℂ) = 1 := by linear_combination h
    have h2 : Nat.card Fq = 1 := by exact_mod_cast h1
    omega
  set g := Rep.genusInt Fq k with hg
  set c := canonical Fq k with hcdef
  have hdc : Divisor.deg c = 2 * g - 2 := (weil_VI_2_cor1 hc).1
  have hn0 : (0 : ℤ) ≤ 2 * g - 2 - n := by omega
  have e : (((2 * g - 2 - n).toNat : ℕ) : ℤ) = 2 * g - 2 - n := Int.toNat_of_nonneg hn0
  rw [coeff_divisorSeries_univ, coeff_divisorSeries_univ, e]
  have hk0 : c - ((2 * g - 2) • b₁) ∈ (Divisor.deg (Fq := Fq) (k := k)).ker := by
    apply AddMonoidHom.mem_ker.mpr
    rw [map_sub, map_zsmul, hb₁, hdc]; simp
  set κ : ClassGroup0 Fq k := QuotientAddGroup.mk ⟨_, hk0⟩ with hκ
  have hprin : ∀ (m : ℤ) (C : ClassGroup0 Fq k),
      c - baseDiv b₁ m C - baseDiv b₁ (2 * g - 2 - m) (κ - C) ∈ principalDivisors Fq k := by
    intro m C
    have hmem : (⟨_, hk0⟩ - repKer C - repKer (κ - C) : (Divisor.deg (Fq := Fq) (k := k)).ker) ∈
        (principalDivisors Fq k).addSubgroupOf (Divisor.deg (Fq := Fq) (k := k)).ker := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_sub, mk_repKer,
        mk_repKer]
      exact sub_self _
    have hmem' := AddSubgroup.mem_addSubgroupOf.mp hmem
    have e : c - baseDiv b₁ m C - baseDiv b₁ (2 * g - 2 - m) (κ - C) =
        ((⟨_, hk0⟩ - repKer C - repKer (κ - C) : (Divisor.deg (Fq := Fq) (k := k)).ker) : Divisor Fq k) := by
      simp only [baseDiv, AddSubgroup.coe_sub]
      have hsm : ((2 * g - 2) • b₁) = m • b₁ + (2 * g - 2 - m) • b₁ := by
        rw [← add_smul]; congr 1; ring
      rw [hsm]; abel
    rw [e]; exact hmem'
  have hφ : ∀ C : ClassGroup0 Fq k, ((baseDiv b₁ n C).ell : ℤ) =
      n + 1 - g + (baseDiv b₁ (2 * g - 2 - n) (κ - C)).ell := by
    intro C
    rw [weil_VI_2_thm2 (baseDiv b₁ n C), deg_baseDiv hb₁, ell_eq_of_sub_mem (hprin n C)]
  have hχφ : ∀ C : ClassGroup0 Fq k, ((χ (Multiplicative.ofAdd (baseDiv b₁ n C)) : ℂˣ) : ℂ) =
      ((χ (Multiplicative.ofAdd c) : ℂˣ) : ℂ) *
        ((χ (Multiplicative.ofAdd (baseDiv b₁ (2 * g - 2 - n) (κ - C))) : ℂˣ) : ℂ)⁻¹ := by
    intro C
    have hm : c - (baseDiv b₁ n C + baseDiv b₁ (2 * g - 2 - n) (κ - C)) ∈ principalDivisors Fq k := by
      convert hprin n C using 1; abel
    have h := chi_eq_of_sub_mem χ hP hm
    have h2 : ((χ (Multiplicative.ofAdd c) : ℂˣ) : ℂ) =
        ((χ (Multiplicative.ofAdd (baseDiv b₁ n C)) : ℂˣ) : ℂ) *
          ((χ (Multiplicative.ofAdd (baseDiv b₁ (2 * g - 2 - n) (κ - C))) : ℂˣ) : ℂ) := by
      rw [h, ofAdd_add, map_mul, Units.val_mul]
    have hne := Units.ne_zero (χ (Multiplicative.ofAdd (baseDiv b₁ (2 * g - 2 - n) (κ - C))))
    rw [h2]; field_simp
  have hP' : ∀ f : kˣ, χ⁻¹ (Multiplicative.ofAdd (Divisor.div f)) = 1 := fun f => by
    rw [MonoidHom.inv_apply, hP, inv_one]
  have hχd' : χ⁻¹ (Multiplicative.ofAdd d) ≠ 1 := fun h =>
    hχd (by rwa [MonoidHom.inv_apply, inv_eq_one] at h)
  have hA : ((Nat.card Fq : ℂ) - 1) * effSumInt χ (n : ℤ) = ∑ C : ClassGroup0 Fq k,
      ((χ (Multiplicative.ofAdd (baseDiv b₁ n C)) : ℂˣ) : ℂ) * (Nat.card Fq : ℂ) ^ (baseDiv b₁ n C).ell := by
    rw [class_sum hc χ hP hb₁]
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, sum_class_eq_zero χ hP b₁ n d hd0 hχd, sub_zero]
  have hB : ((Nat.card Fq : ℂ) - 1) * effSumInt χ⁻¹ (2 * g - 2 - n) = ∑ C : ClassGroup0 Fq k,
      ((χ⁻¹ (Multiplicative.ofAdd (baseDiv b₁ (2 * g - 2 - n) C)) : ℂˣ) : ℂ) *
        (Nat.card Fq : ℂ) ^ (baseDiv b₁ (2 * g - 2 - n) C).ell := by
    rw [class_sum hc χ⁻¹ hP' hb₁]
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, sum_class_eq_zero χ⁻¹ hP' b₁ _ d hd0 hχd', sub_zero]
  have hterm : ∀ C : ClassGroup0 Fq k,
      ((χ (Multiplicative.ofAdd (baseDiv b₁ n C)) : ℂˣ) : ℂ) * (Nat.card Fq : ℂ) ^ (baseDiv b₁ n C).ell =
        ((χ (Multiplicative.ofAdd c) : ℂˣ) : ℂ) * (Nat.card Fq : ℂ) ^ ((n : ℤ) + 1 - g) *
          (((χ⁻¹ (Multiplicative.ofAdd (baseDiv b₁ (2 * g - 2 - n) (κ - C))) : ℂˣ) : ℂ) *
            (Nat.card Fq : ℂ) ^ (baseDiv b₁ (2 * g - 2 - n) (κ - C)).ell) := by
    intro C
    have hpow : (Nat.card Fq : ℂ) ^ (baseDiv b₁ n C).ell = (Nat.card Fq : ℂ) ^ ((n : ℤ) + 1 - g) *
        (Nat.card Fq : ℂ) ^ (baseDiv b₁ (2 * g - 2 - n) (κ - C)).ell := by
      rw [← zpow_natCast, hφ C, zpow_add₀ hqne, zpow_natCast]
    rw [hpow, hχφ C, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    ring
  have hcomp := Equiv.sum_comp (Equiv.subLeft κ) (fun C : ClassGroup0 Fq k =>
    ((χ⁻¹ (Multiplicative.ofAdd (baseDiv b₁ (2 * g - 2 - n) C)) : ℂˣ) : ℂ) *
        (Nat.card Fq : ℂ) ^ (baseDiv b₁ (2 * g - 2 - n) C).ell)
  simp only [Equiv.subLeft_apply] at hcomp
  refine mul_left_cancel₀ hq1 ?_
  have hN : ((n : ℤ) - g + 1) = (n : ℤ) + 1 - g := by ring
  rw [hN, hA, Finset.sum_congr rfl (fun C _ => hterm C), ← Finset.mul_sum, hcomp, ← hB]
  ring

/-- The top coefficient: $c_{2g-2}(\chi)=\chi(\mathfrak c)\,q^{g-1}$. -/
theorem coeff_divisorSeries_top (hc : IsConstantField Fq k)
    (χ : Multiplicative (Divisor Fq k) →* ℂˣ)
    (hP : ∀ f : kˣ, χ (Multiplicative.ofAdd (Divisor.div f)) = 1)
    (hd : ∃ d : Divisor Fq k, Divisor.deg d = 0 ∧ χ (Multiplicative.ofAdd d) ≠ 1) :
    PowerSeries.coeff (2 * Rep.genusInt Fq k - 2).toNat (divisorSeries χ Set.univ) =
      ((χ (Multiplicative.ofAdd (canonical Fq k)) : ℂˣ) : ℂ) * (Nat.card Fq : ℂ) ^ (Rep.genusInt Fq k - 1) := by
  have hg1 := genusInt_pos hc χ hP hd
  have h := divisorSeries_functional_equation hc χ hP hd (2 * Rep.genusInt Fq k - 2).toNat (by omega)
  have h0 : (2 * Rep.genusInt Fq k - 2 - (((2 * Rep.genusInt Fq k - 2).toNat : ℕ) : ℤ)).toNat = 0 := by
    omega
  have h1 : (((2 * Rep.genusInt Fq k - 2).toNat : ℕ) : ℤ) - Rep.genusInt Fq k + 1 =
      Rep.genusInt Fq k - 1 := by omega
  have h2 : PowerSeries.coeff 0 (divisorSeries χ⁻¹ Set.univ) = 1 := by
    rw [coeff_divisorSeries_univ, Nat.cast_zero, effSumInt_zero]
  rw [h, h0, h1, h2, mul_one]

namespace FFHeckeCharacter

/-- The L-series of `HeckeLFF.lean` is the divisor series of the divisor character. -/
theorem lSeries_eq_divisorSeries (ω : FFHeckeCharacter Fq k) (hω : ∀ v, ω.IsUnramifiedAt v) :
    ω.lSeries hω = divisorSeries (ω.divChar hω) Set.univ := by
  ext n
  rw [lSeries, PowerSeries.coeff_mk, coeff_divisorSeries_univ]
  rfl

/-- **Weil VII.§7, Thm. 6** for conductor $0$, exact degree: for an everywhere unramified non-principal $\omega$ (and
$\mathbb F_q$ the field of constants), $L(u,\omega)$ is a polynomial of degree exactly $2g-2$. -/
@[kb "weil1973bnt" "Ch. VII, §7, Thm. 6 (p. 134), conductor 0: L(u, omega) is a polynomial of degree exactly 2g - 2"]
theorem weil_VII_7_thm6_unramified_exact (hc : IsConstantField Fq k) (ω : FFHeckeCharacter Fq k)
    (hω : ∀ v, ω.IsUnramifiedAt v) (hnp : ¬ ω.IsPrincipal) :
    ∃ P : Polynomial ℂ, (P.natDegree : ℤ) = 2 * (genus Fq k : ℤ) - 2 ∧ (P : PowerSeries ℂ) = ω.lSeries hω := by
  obtain ⟨P, hPdeg, hPeq⟩ := weil_VII_7_thm6_unramified hc ω hω hnp
  obtain ⟨d, hd0, hd⟩ := exists_deg_zero_divChar_ne_one ω hω hnp
  have htop := coeff_divisorSeries_top hc (ω.divChar hω) (ω.divChar_principal hω) ⟨d, hd0, hd⟩
  rw [← ω.lSeries_eq_divisorSeries hω, ← hPeq, Polynomial.coeff_coe] at htop
  have hqne : (Nat.card Fq : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hne : P.coeff (2 * Rep.genusInt Fq k - 2).toNat ≠ 0 := by
    rw [htop]; exact mul_ne_zero (Units.ne_zero _) (zpow_ne_zero _ hqne)
  have hge := genus_eq hc
  refine ⟨P, ?_, hPeq⟩
  have := Polynomial.le_natDegree_of_ne_zero hne
  omega

/-- **Weil VII.§7, Thm. 6** for conductor $0$, functional equation: $L(u,\omega)=\omega(\mathfrak c)\,
(q^{1/2}u)^{2g-2}L(1/qu,\omega^{-1})$, coefficientwise; here $L(u,\omega^{-1})$ is the divisor series of
$\chi_\omega^{-1}$ and $\mathfrak c$ is a canonical divisor. -/
@[kb "weil1973bnt" "Ch. VII, §7, Thm. 6 (p. 134), conductor 0: functional equation P(u, omega) = omega(c) (q^(1/2) u)^(2g-2) P(1/qu, omega^-1)"]
theorem weil_VII_7_thm6_unramified_fe (hc : IsConstantField Fq k) (ω : FFHeckeCharacter Fq k)
    (hω : ∀ v, ω.IsUnramifiedAt v) (hnp : ¬ ω.IsPrincipal) (n : ℕ)
    (hn : (n : ℤ) ≤ 2 * (genus Fq k : ℤ) - 2) :
    PowerSeries.coeff n (ω.lSeries hω) =
      ((ω.divChar hω (Multiplicative.ofAdd (canonical Fq k)) : ℂˣ) : ℂ) *
        (Nat.card Fq : ℂ) ^ ((n : ℤ) - genus Fq k + 1) *
        PowerSeries.coeff (2 * (genus Fq k : ℤ) - 2 - n).toNat (divisorSeries (ω.divChar hω)⁻¹ Set.univ) := by
  obtain ⟨d, hd0, hd⟩ := exists_deg_zero_divChar_ne_one ω hω hnp
  rw [lSeries_eq_divisorSeries]
  rw [genus_eq hc] at hn ⊢
  exact divisorSeries_functional_equation hc _ (ω.divChar_principal hω) ⟨d, hd0, hd⟩ n hn

end FFHeckeCharacter

end NumberFieldKB.WeilBNT.FF
