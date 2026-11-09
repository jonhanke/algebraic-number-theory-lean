import NumberFieldKB.MilneCFT.LubinTate.PowerSeries

/-!
# The Lubin–Tate series $\mathcal F_\pi$ and Lemma 2.11 (Milne, *Class Field Theory*, Chapter I, §2)

**Setting.** Milne takes $A = \mathcal O_K$ for a nonarchimedean local field $K$, a prime element $\pi$ and
$q = |A/\mathfrak m|$. The algebra of §2 uses only the properties collected in `LubinTateHyp A π q`: $q > 1$; $\pi$
is a non-zero-divisor; $\pi^r - 1$ is a unit for $r \ge 1$ (true when $\pi$ lies in the maximal ideal of a local ring);
$a^q \equiv a \pmod \pi$ for every $a \in A$; and $\pi \mid \binom qk$ for $0 < k < q$ (so that $x \mapsto x^q$ is
additive on every $A/(\pi)$-algebra, in particular on polynomials over $A/(\pi)$: "the simple form that the binomial
theorem takes in characteristic $p$"). They hold in the book's setting
(`lubinTateHyp_of_isNonarchimedeanLocalField`, in `NumberFieldKB.MilneCFT.LubinTate.Padic`).
-/

open MvPowerSeries

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

variable {A : Type*} [CommRing A]

/-- The hypotheses on $(A, \pi, q)$ used in Milne's §2: $q > 1$, $\pi$ is a non-zero-divisor, $\pi^r - 1$ is a unit
for $r \ge 1$, $a^q \equiv a \pmod\pi$ for all $a$, and $\pi \mid \binom qk$ for $0 < k < q$. They hold for the ring
of integers of a nonarchimedean local field, a prime element and the order of the residue field. -/
structure LubinTateHyp (A : Type*) [CommRing A] (π : A) (q : ℕ) : Prop where
  one_lt : 1 < q
  isSMulRegular : IsSMulRegular A π
  isUnit_pow_sub_one : ∀ r : ℕ, 1 ≤ r → IsUnit (π ^ r - 1)
  pow_sub_mem : ∀ a : A, a ^ q - a ∈ Ideal.span {π}
  choose_mem : ∀ k : ℕ, 0 < k → k < q → (q.choose k : A) ∈ Ideal.span {π}

/-- **The set $\mathcal F_\pi$** (Milne, *CFT*, I, Definition 2.9): power series $f \in A[[X]]$ with
$f(X) = \pi X + (\deg \ge 2)$ and $f(X) \equiv X^q \pmod \pi$ (coefficientwise). -/
@[kb "milne2020cft" "Ch. I, Definition 2.9"]
def lubinTateSeries (π : A) (q : ℕ) : Set (PowerSeries A) :=
  {f | PowerSeries.constantCoeff f = 0 ∧ PowerSeries.coeff 1 f = π ∧
    ∀ n : ℕ, PowerSeries.coeff n f - PowerSeries.coeff n (PowerSeries.X ^ q) ∈ Ideal.span {π}}

/-- **Example 2.10 (a)** (Milne, *CFT*, I): $\pi X + X^q \in \mathcal F_\pi$ (for $q \ge 2$). -/
@[kb "milne2020cft" "Ch. I, Example 2.10 (a)"]
theorem C_mul_X_add_X_pow_mem (π : A) {q : ℕ} (hq : 2 ≤ q) :
    PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q ∈ lubinTateSeries π q := by
  have hq1 : 1 ≠ q := by omega
  have hq0 : q ≠ 0 := by omega
  refine ⟨by simp [hq0], ?_, ?_⟩
  · simp [PowerSeries.coeff_X_pow, hq1]
  · intro n
    rw [map_add, add_sub_cancel_right, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
    split_ifs
    · simp
    · simp

/-! ### Helper lemmas for Lemma 2.11

The proof builds the series degree by degree. `Vanishes d ψ` says that all coefficients of `ψ` of total
degree below `d` are zero, and `defect f g φ` is the difference of the two sides of the functional equation. -/

section Vanishing

variable {σ : Type*} {R : Type*} [CommRing R]

/-- All coefficients of total degree below `d` vanish. -/
def Vanishes (d : ℕ) (ψ : MvPowerSeries σ R) : Prop :=
  ∀ α : σ →₀ ℕ, α.degree < d → coeff α ψ = 0

lemma Vanishes.mono {d e : ℕ} (h : e ≤ d) {ψ : MvPowerSeries σ R} (hψ : Vanishes d ψ) :
    Vanishes e ψ :=
  fun α hα => hψ α (lt_of_lt_of_le hα h)

lemma Vanishes.zero (d : ℕ) : Vanishes d (0 : MvPowerSeries σ R) := fun α _ => by simp

lemma Vanishes.add {d : ℕ} {x y : MvPowerSeries σ R} (hx : Vanishes d x) (hy : Vanishes d y) :
    Vanishes d (x + y) := fun α hα => by simp [hx α hα, hy α hα]

lemma Vanishes.sub {d : ℕ} {x y : MvPowerSeries σ R} (hx : Vanishes d x) (hy : Vanishes d y) :
    Vanishes d (x - y) := fun α hα => by simp [hx α hα, hy α hα]

lemma Vanishes.mul {a b : ℕ} {P Q : MvPowerSeries σ R} (hP : Vanishes a P) (hQ : Vanishes b Q) :
    Vanishes (a + b) (P * Q) := by
  classical
  intro α hα
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  have : p.1.degree + p.2.degree = α.degree := by rw [← map_add, hp]
  by_cases h : p.1.degree < a
  · rw [hP _ h, zero_mul]
  · rw [hQ p.2 (by omega), mul_zero]

lemma Vanishes.mul_right {a : ℕ} {P : MvPowerSeries σ R} (hP : Vanishes a P)
    (Q : MvPowerSeries σ R) : Vanishes a (P * Q) := by
  simpa using hP.mul (show Vanishes 0 Q from fun α hα => absurd hα (Nat.not_lt_zero _))

lemma vanishes_one_iff {ψ : MvPowerSeries σ R} : Vanishes 1 ψ ↔ constantCoeff ψ = 0 := by
  constructor
  · intro h
    simpa using h 0 (by simp)
  · intro h α hα
    have : α = 0 := by
      rw [← Finsupp.degree_eq_zero_iff]; omega
    subst this
    simpa using h

lemma Vanishes.pow {φ : MvPowerSeries σ R} (hφ : Vanishes 1 φ) (n : ℕ) : Vanishes n (φ ^ n) := by
  induction n with
  | zero => exact fun α hα => absurd hα (Nat.not_lt_zero _)
  | succ n ih => rw [pow_succ]; exact ih.mul hφ

lemma vanishes_sub_iff [Finite σ] {d : ℕ} {x y : MvPowerSeries σ R} :
    Vanishes d (x - y) ↔ truncTotal d x = truncTotal d y := by
  constructor
  · intro h
    ext α
    rw [coeff_truncTotal_eq_ite, coeff_truncTotal_eq_ite]
    split_ifs with hα
    · have := h α hα
      rwa [map_sub, sub_eq_zero] at this
    · rfl
  · intro h α hα
    have := congrArg (fun p => p.coeff α) h
    rw [coeff_truncTotal _ hα, coeff_truncTotal _ hα] at this
    simp [this]

end Vanishing

section Series

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {π : A}

/-- Substituting power series that agree below degree `d` into a fixed power series gives power
series that agree below degree `d`. -/
lemma vanishes_subst_sub (f : PowerSeries A) {d : ℕ} {φ ψ : MvPowerSeries σ A}
    (hφ : constantCoeff φ = 0) (hψ : constantCoeff ψ = 0) (h : Vanishes d (φ - ψ)) :
    Vanishes d (f.subst φ - f.subst ψ) := by
  rw [vanishes_sub_iff] at h ⊢
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.truncTotal_subst (fun _ => hφ), MvPowerSeries.truncTotal_subst (fun _ => hψ)]
  simp only [h]

/-- A power series with zero constant term and linear coefficient `π` is `πX` plus a multiple of
`X²`. -/
lemma exists_eq_C_mul_X_add {f : PowerSeries A} (h0 : PowerSeries.constantCoeff f = 0)
    (h1 : PowerSeries.coeff 1 f = π) :
    ∃ u : PowerSeries A, f = PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ 2 * u := by
  obtain ⟨h, rfl⟩ := PowerSeries.X_dvd_iff.mpr h0
  have hc : PowerSeries.constantCoeff h = π := by
    have := PowerSeries.coeff_succ_X_mul (R := A) 0 h
    simp [← h1]
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.mpr
    (show PowerSeries.constantCoeff (h - PowerSeries.C π) = 0 by simp [hc])
  refine ⟨u, ?_⟩
  have : h = PowerSeries.C π + PowerSeries.X * u := by rw [← hu]; ring
  rw [this]; ring

lemma subst_eq_of_decomp {f u : PowerSeries A}
    (hfu : f = PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ 2 * u) {ψ : MvPowerSeries σ A}
    (hψ : constantCoeff ψ = 0) :
    f.subst ψ = MvPowerSeries.C π * ψ + ψ ^ 2 * u.subst ψ := by
  have h := PowerSeries.HasSubst.of_constantCoeff_zero hψ
  rw [hfu, PowerSeries.subst_add h, PowerSeries.subst_mul h, PowerSeries.subst_mul h,
    PowerSeries.subst_pow h, PowerSeries.subst_X h, PowerSeries.subst_C]

/-- The first order behaviour of `f ∘ (φ + Q)` when `Q` vanishes below degree `d`. -/
lemma f_subst_add_sub {f u : PowerSeries A}
    (hfu : f = PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ 2 * u) {d : ℕ} (hd : 1 ≤ d)
    {φ Q : MvPowerSeries σ A} (hφ : constantCoeff φ = 0) (hQ : Vanishes d Q) :
    Vanishes (d + 1) (f.subst (φ + Q) - f.subst φ - MvPowerSeries.C π * Q) := by
  have hQ0 : constantCoeff Q = 0 := vanishes_one_iff.mp (hQ.mono hd)
  have hφQ : constantCoeff (φ + Q) = 0 := by simp [hφ, hQ0]
  have hdiff : Vanishes d (u.subst (φ + Q) - u.subst φ) :=
    vanishes_subst_sub u hφQ hφ (by simpa using hQ)
  have key : f.subst (φ + Q) - f.subst φ - MvPowerSeries.C π * Q =
      (Q * (φ + (φ + Q))) * u.subst (φ + Q) + φ ^ 2 * (u.subst (φ + Q) - u.subst φ) := by
    rw [subst_eq_of_decomp hfu hφQ, subst_eq_of_decomp hfu hφ]; ring
  rw [key]
  have h1 : Vanishes (d + 1) (Q * (φ + (φ + Q))) := by
    have : Vanishes 1 (φ + (φ + Q)) := vanishes_one_iff.mpr (by simp [hφ, hQ0])
    exact hQ.mul this
  have h2 : Vanishes (2 + d) (φ ^ 2 * (u.subst (φ + Q) - u.subst φ)) :=
    ((vanishes_one_iff.mpr hφ).pow 2).mul hdiff
  exact (h1.mul_right _).add (h2.mono (by omega))

lemma finsupp_eq_of_le_of_degree_eq {β α : σ →₀ ℕ} (h : β ≤ α) (hd : β.degree = α.degree) :
    β = α := by
  have h1 : α = β + (α - β) := (add_tsub_cancel_of_le h).symm
  have h2 : α.degree = β.degree + (α - β).degree := by
    conv_lhs => rw [h1]
    rw [map_add]
  have h3 : (α - β).degree = 0 := by omega
  rw [Finsupp.degree_eq_zero_iff, tsub_eq_zero_iff_le] at h3
  exact le_antisymm h h3

/-- The substitution `X_i ↦ g(X_i)`. -/
def gSub (g : PowerSeries A) : σ → MvPowerSeries σ A := fun i => g.subst (X i : MvPowerSeries σ A)

lemma gSub_eq {g h : PowerSeries A} (hgh : g = PowerSeries.X * h) (s : σ) :
    gSub g s = X s * h.subst (X s : MvPowerSeries σ A) := by
  simp only [gSub]
  rw [hgh, PowerSeries.subst_mul (PowerSeries.HasSubst.X s),
    PowerSeries.subst_X (PowerSeries.HasSubst.X s)]

lemma gSub_prod {g h : PowerSeries A} (hgh : g = PowerSeries.X * h)
    (hh : PowerSeries.constantCoeff h = π) (β : σ →₀ ℕ) :
    ∃ K : MvPowerSeries σ A, constantCoeff K = π ^ β.degree ∧
      (β.prod fun s e => gSub g s ^ e) = monomial β 1 * K := by
  refine ⟨β.prod fun s e => (h.subst (X s : MvPowerSeries σ A)) ^ e, ?_, ?_⟩
  · rw [map_finsuppProd]
    have : ∀ s : σ, constantCoeff (h.subst (X s : MvPowerSeries σ A)) = π := fun s => by
      rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero (by simp), hh]; simp
    simp [this, Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  · rw [MvPowerSeries.monomial_one_eq, ← Finsupp.prod_mul]
    apply Finsupp.prod_congr
    intro s _
    rw [gSub_eq hgh, mul_pow]

lemma constantCoeff_gSub {g h : PowerSeries A} (hgh : g = PowerSeries.X * h) (s : σ) :
    constantCoeff (gSub g s) = 0 := by
  rw [gSub_eq hgh s, map_mul]; simp

lemma hasSubst_gSub {g h : PowerSeries A} (hgh : g = PowerSeries.X * h) :
    HasSubst (gSub g : σ → MvPowerSeries σ A) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_gSub hgh)

lemma coeff_subst_gSub {g h : PowerSeries A} (hgh : g = PowerSeries.X * h)
    (hh : PowerSeries.constantCoeff h = π) {d : ℕ} {Q : MvPowerSeries σ A} (hQ : Vanishes d Q)
    {α : σ →₀ ℕ} (hα : α.degree ≤ d) :
    coeff α (Q.subst (gSub g)) = if α.degree = d then π ^ d * coeff α Q else 0 := by
  have hG : HasSubst (gSub g : σ → MvPowerSeries σ A) := hasSubst_gSub hgh
  rw [coeff_subst hG]
  have hterm : ∀ β : σ →₀ ℕ, β ≠ α →
      coeff β Q • coeff α (β.prod fun s e => gSub g s ^ e) = 0 := by
    intro β hβ
    by_cases hQβ : coeff β Q = 0
    · simp [hQβ]
    · obtain ⟨K, -, hK⟩ := gSub_prod hgh hh β
      rw [hK, coeff_monomial_mul]
      have hdβ : d ≤ β.degree := by
        by_contra hlt
        exact hQβ (hQ β (not_le.mp hlt))
      split_ifs with hle
      · exfalso
        apply hβ
        have := Finsupp.degree_mono hle
        exact finsupp_eq_of_le_of_degree_eq hle (by omega)
      · simp
  split_ifs with hdeg
  · rw [finsum_eq_single _ α (fun β hβ => hterm β hβ)]
    obtain ⟨K, hK0, hK⟩ := gSub_prod hgh hh α
    rw [hK, coeff_monomial_mul]
    simp only [le_refl, ↓reduceIte, tsub_self, one_mul]
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hK0, hdeg, smul_eq_mul, mul_comm]
  · apply finsum_eq_zero_of_forall_eq_zero
    intro β
    by_cases hβ : β = α
    · subst hβ
      have : coeff β Q = 0 := hQ β (by omega)
      simp [this]
    · exact hterm β hβ

/-- The defect `f ∘ φ - φ ∘ (g(X_1), …, g(X_n))` in the functional equation of Lemma 2.11. -/
def defect (f g : PowerSeries A) (φ : MvPowerSeries σ A) : MvPowerSeries σ A :=
  f.subst φ - φ.subst (gSub g)

lemma coeff_defect_add {f g u h : PowerSeries A}
    (hfu : f = PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ 2 * u)
    (hgh : g = PowerSeries.X * h) (hh : PowerSeries.constantCoeff h = π) {d : ℕ} (hd : 1 ≤ d)
    {φ Q : MvPowerSeries σ A} (hφ : constantCoeff φ = 0) (hQ : Vanishes d Q)
    {α : σ →₀ ℕ} (hα : α.degree ≤ d) :
    coeff α (defect f g (φ + Q)) = coeff α (defect f g φ) +
      if α.degree = d then (π - π ^ d) * coeff α Q else 0 := by
  have h1 := f_subst_add_sub hfu hd hφ hQ α (by omega)
  rw [map_sub, map_sub, coeff_C_mul] at h1
  have h2 := coeff_subst_gSub hgh hh hQ hα
  have h3 : (φ + Q).subst (gSub g) = φ.subst (gSub g) + Q.subst (gSub g) :=
    subst_add (hasSubst_gSub hgh) φ Q
  have h1' : coeff α (f.subst (φ + Q)) = coeff α (f.subst φ) + π * coeff α Q := by
    linear_combination h1
  simp only [defect, map_sub, h3, map_add, h2, h1']
  split_ifs with hdeg
  · ring
  · have : coeff α Q = 0 := hQ α (by omega)
    rw [this]; ring

lemma vanishes_subst_gSub {g h : PowerSeries A} (hgh : g = PowerSeries.X * h) {d : ℕ}
    {φ ψ : MvPowerSeries σ A} (hd : Vanishes d (φ - ψ)) :
    Vanishes d (φ.subst (gSub g) - ψ.subst (gSub g)) := by
  rw [vanishes_sub_iff] at hd ⊢
  rw [MvPowerSeries.truncTotal_subst (f := φ) (constantCoeff_gSub hgh),
    MvPowerSeries.truncTotal_subst (f := ψ) (constantCoeff_gSub hgh)]
  simp only [hd]

lemma vanishes_defect_sub {f g h : PowerSeries A} (hgh : g = PowerSeries.X * h) {d : ℕ}
    {φ ψ : MvPowerSeries σ A} (hφ : constantCoeff φ = 0) (hψ : constantCoeff ψ = 0)
    (hd : Vanishes d (φ - ψ)) : Vanishes d (defect f g φ - defect f g ψ) := by
  have e : defect f g φ - defect f g ψ =
      (f.subst φ - f.subst ψ) - (φ.subst (gSub g) - ψ.subst (gSub g)) := by
    unfold defect; ring
  rw [e]
  exact (vanishes_subst_sub f hφ hψ hd).sub (vanishes_subst_gSub hgh hd)

lemma add_pow_eq_of_choose {S : Type*} [CommRing S] {q : ℕ} (hq : 0 < q)
    (hc : ∀ j, 0 < j → j < q → ((q.choose j : ℕ) : S) = 0) (x y : S) :
    (x + y) ^ q = x ^ q + y ^ q := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
  have : ∑ i ∈ Finset.range n, x ^ (i + 1) * y ^ (n + 1 - (i + 1)) *
      ((n + 1).choose (i + 1) : S) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hc (i + 1) (by omega) (by omega)]
    simp
  rw [this]
  simp
  ring

/-- Frobenius on polynomials: in a ring where `a ^ q = a` and `q.choose j = 0` for `0 < j < q`,
substituting `X_i ↦ X_i ^ q` is the same as raising to the `q`-th power. -/
lemma subst_pow_coe_polynomial {k : Type*} [CommRing k] {q : ℕ} (hq : 0 < q)
    (hk : ∀ a : k, a ^ q = a) (hc : ∀ j, 0 < j → j < q → ((q.choose j : ℕ) : k) = 0)
    (p : MvPolynomial σ k) :
    (p : MvPowerSeries σ k).subst (fun i => (X i : MvPowerSeries σ k) ^ q) =
      (p : MvPowerSeries σ k) ^ q := by
  have hS : HasSubst (fun i : σ => (X i : MvPowerSeries σ k) ^ q) := HasSubst.X_pow hq.ne'
  have hc' : ∀ j, 0 < j → j < q → ((q.choose j : ℕ) : MvPowerSeries σ k) = 0 := by
    intro j hj hjq
    rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := k)), hc j hj hjq, map_zero]
  induction p using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.coe_C, subst_C, ← map_pow, hk]
  | add p r hp hr =>
    rw [MvPolynomial.coe_add, subst_add hS, hp, hr, add_pow_eq_of_choose hq hc']
  | mul_X p i hp =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul hS, subst_X hS, hp, mul_pow]

lemma map_eq_X_pow {q : ℕ} {f : PowerSeries A} (hf : f ∈ lubinTateSeries π q) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {π})) f = PowerSeries.X ^ q := by
  ext n
  rw [PowerSeries.coeff_map, Ideal.Quotient.eq.mpr (hf.2.2 n)]
  by_cases hn : n = q <;> simp [PowerSeries.coeff_X_pow, hn]

/-- The defect of a polynomial with zero constant term has all coefficients divisible by `π`. -/
lemma coeff_defect_poly_mem {q : ℕ} (H : LubinTateHyp A π q) {f g h : PowerSeries A}
    (hf : f ∈ lubinTateSeries π q) (hg : g ∈ lubinTateSeries π q) (hgh : g = PowerSeries.X * h)
    (p : MvPolynomial σ A) (hp : constantCoeff (p : MvPowerSeries σ A) = 0) (α : σ →₀ ℕ) :
    coeff α (defect f g (p : MvPowerSeries σ A)) ∈ Ideal.span {π} := by
  set mk := Ideal.Quotient.mk (Ideal.span {π}) with hmk
  have hφ : PowerSeries.HasSubst (p : MvPowerSeries σ A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hp
  have hφ' : PowerSeries.HasSubst (MvPowerSeries.map mk (p : MvPowerSeries σ A)) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hp,
      map_zero]
  have e1 : MvPowerSeries.map mk (f.subst (p : MvPowerSeries σ A)) =
      (MvPowerSeries.map mk (p : MvPowerSeries σ A)) ^ q := by
    rw [PowerSeries.map_subst hφ, map_eq_X_pow hf, PowerSeries.subst_pow hφ',
      PowerSeries.subst_X hφ']
  have e2 : MvPowerSeries.map mk ((p : MvPowerSeries σ A).subst (gSub g)) =
      (MvPowerSeries.map mk (p : MvPowerSeries σ A)).subst
        (fun i => (X i : MvPowerSeries σ (A ⧸ Ideal.span {π})) ^ q) := by
    rw [MvPowerSeries.map_subst (hasSubst_gSub hgh)]
    congr 1
    funext i
    simp only [gSub]
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.X i), map_eq_X_pow hg, MvPowerSeries.map_X,
      PowerSeries.subst_pow (PowerSeries.HasSubst.X i),
      PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
  have e3 : MvPowerSeries.map mk (p : MvPowerSeries σ A) =
      ((MvPolynomial.map mk p : MvPolynomial σ (A ⧸ Ideal.span {π})) :
        MvPowerSeries σ (A ⧸ Ideal.span {π})) := by
    ext β
    simp [MvPolynomial.coeff_coe, coeff_map, MvPolynomial.coeff_map]
  have hk : ∀ a : A ⧸ Ideal.span {π}, a ^ q = a := by
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← map_pow]
    exact Ideal.Quotient.eq.mpr (H.pow_sub_mem a)
  have hc : ∀ j, 0 < j → j < q → ((q.choose j : ℕ) : A ⧸ Ideal.span {π}) = 0 := by
    intro j hj hjq
    rw [← map_natCast mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (H.choose_mem j hj hjq)
  have hz : MvPowerSeries.map mk (defect f g (p : MvPowerSeries σ A)) = 0 := by
    unfold defect
    rw [map_sub, e1, e2, e3, subst_pow_coe_polynomial (by have := H.one_lt; omega) hk hc,
      sub_self]
  have := congrArg (coeff α) hz
  rw [coeff_map, map_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

/-- The defect of any series with zero constant term has all coefficients divisible by `π`. -/
lemma coeff_defect_mem_span {q : ℕ} (H : LubinTateHyp A π q) {f g h : PowerSeries A}
    (hf : f ∈ lubinTateSeries π q) (hg : g ∈ lubinTateSeries π q) (hgh : g = PowerSeries.X * h)
    (φ : MvPowerSeries σ A) (hφ : constantCoeff φ = 0) (α : σ →₀ ℕ) :
    coeff α (defect f g φ) ∈ Ideal.span {π} := by
  set p : MvPolynomial σ A := truncTotal (α.degree + 1) φ with hpdef
  have hpc : ∀ β : σ →₀ ℕ, β.degree < α.degree + 1 → coeff β (p : MvPowerSeries σ A) = coeff β φ :=
    fun β hβ => by rw [MvPolynomial.coeff_coe, hpdef, coeff_truncTotal _ hβ]
  have hp0 : constantCoeff (p : MvPowerSeries σ A) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hpc 0 (by simp), coeff_zero_eq_constantCoeff_apply,
      hφ]
  have hd : Vanishes (α.degree + 1) (φ - (p : MvPowerSeries σ A)) := fun β hβ => by
    rw [map_sub, hpc β hβ, sub_self]
  have := vanishes_defect_sub (f := f) hgh hφ hp0 hd α (Nat.lt_succ_self _)
  rw [map_sub, sub_eq_zero] at this
  rw [this]
  exact coeff_defect_poly_mem H hf hg hgh p hp0 α

lemma exists_eq_X_mul {g : PowerSeries A} (h0 : PowerSeries.constantCoeff g = 0)
    (h1 : PowerSeries.coeff 1 g = π) :
    ∃ h : PowerSeries A, g = PowerSeries.X * h ∧ PowerSeries.constantCoeff h = π := by
  obtain ⟨h, rfl⟩ := PowerSeries.X_dvd_iff.mpr h0
  refine ⟨h, rfl, ?_⟩
  have := PowerSeries.coeff_succ_X_mul (R := A) 0 h
  simp [← h1]

lemma eq_zero_of_sub_pow_mul_eq_zero {q : ℕ} (H : LubinTateHyp A π q) {N : ℕ} (hN : 2 ≤ N)
    {c : A} (h : (π - π ^ N) * c = 0) : c = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have hw := H.isUnit_pow_sub_one (m + 1) (by omega)
  have h2 : π * ((π ^ (m + 1) - 1) * c) = 0 := by linear_combination (-1 : A) * h
  have h3 := H.isSMulRegular (show π • ((π ^ (m + 1) - 1) * c) = π • (0 : A) by
    simpa [smul_eq_mul] using h2)
  exact (hw.mul_right_eq_zero).mp h3

lemma vanishes_sub_of_defect {q : ℕ} (H : LubinTateHyp A π q) {f g u h : PowerSeries A}
    (hfu : f = PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ 2 * u)
    (hgh : g = PowerSeries.X * h) (hh : PowerSeries.constantCoeff h = π)
    {φ ψ : MvPowerSeries σ A} (hφ : constantCoeff φ = 0) (hψ : constantCoeff ψ = 0)
    (hlin : ∀ i : σ, coeff (Finsupp.single i 1) φ = coeff (Finsupp.single i 1) ψ)
    {N : ℕ} (hN : 2 ≤ N) (hdφ : Vanishes N (defect f g φ)) (hdψ : Vanishes N (defect f g ψ)) :
    Vanishes N (φ - ψ) := by
  induction N, hN using Nat.le_induction with
  | base =>
    intro α hα
    rw [map_sub, sub_eq_zero]
    by_cases h0 : α.degree = 0
    · rw [Finsupp.degree_eq_zero_iff] at h0
      subst h0
      simp only [coeff_zero_eq_constantCoeff_apply, hφ, hψ]
    · have h1 : α.degree = 1 := by omega
      have : α ∈ Set.range (fun a : σ => Finsupp.single a 1) := by
        rw [Finsupp.range_single_one]; exact h1
      obtain ⟨i, rfl⟩ := this
      exact hlin i
  | succ N hN ih =>
    have ih' := ih (hdφ.mono (by omega)) (hdψ.mono (by omega))
    intro α hα
    by_cases hlt : α.degree < N
    · exact ih' α hlt
    · have hdeg : α.degree = N := by omega
      have hQ : Vanishes N (ψ - φ) := fun β hβ => by
        have := ih' β hβ
        rw [map_sub, sub_eq_zero] at this ⊢
        exact this.symm
      have key := coeff_defect_add (f := f) (g := g) hfu hgh hh (by omega) hφ hQ (le_of_eq hdeg)
      rw [add_sub_cancel, hdψ α (by omega)] at key
      rw [hdφ α (by omega)] at key
      simp only [hdeg, ↓reduceIte] at key
      have := eq_zero_of_sub_pow_mul_eq_zero H hN (c := coeff α (ψ - φ))
        (by linear_combination (-1 : A) * key)
      rw [map_sub] at this ⊢
      linear_combination -this

/-- The inductive step of Lemma 2.11: a series satisfying the equation below degree `N` can be
corrected by a series vanishing below degree `N` so that it satisfies the equation below
degree `N + 1`. -/
lemma exists_step {q : ℕ} (H : LubinTateHyp A π q) {f g u h : PowerSeries A}
    (hf : f ∈ lubinTateSeries π q) (hg : g ∈ lubinTateSeries π q)
    (hfu : f = PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ 2 * u)
    (hgh : g = PowerSeries.X * h) (hh : PowerSeries.constantCoeff h = π)
    {N : ℕ} (hN : 2 ≤ N) {φ : MvPowerSeries σ A} (hφ : constantCoeff φ = 0)
    (hd : Vanishes N (defect f g φ)) :
    ∃ Q : MvPowerSeries σ A, Vanishes N Q ∧ Vanishes (N + 1) (defect f g (φ + Q)) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have hc : ∀ α : σ →₀ ℕ, ∃ c : A, c * π = coeff α (defect f g φ) := fun α =>
    Ideal.mem_span_singleton'.mp (coeff_defect_mem_span H hf hg hgh φ hφ α)
  choose c hc using hc
  have hw := H.isUnit_pow_sub_one (m + 1) (by omega)
  obtain ⟨uinv, hwu⟩ : ∃ uinv : A, (π ^ (m + 1) - 1) * uinv = 1 := ⟨_, hw.mul_val_inv⟩
  obtain ⟨Q, hQc⟩ : ∃ Q : MvPowerSeries σ A,
      ∀ α, coeff α Q = if α.degree = m + 2 then uinv * c α else 0 :=
    ⟨fun α => if α.degree = m + 2 then uinv * c α else 0, fun α => rfl⟩
  have hQ : Vanishes (m + 2) Q := fun α hα => by
    rw [hQc]; simp only [show α.degree ≠ m + 2 by omega, ↓reduceIte]
  refine ⟨Q, hQ, ?_⟩
  intro α hα
  rw [coeff_defect_add hfu hgh hh (by omega) hφ hQ (by omega : α.degree ≤ m + 2)]
  by_cases hdeg : α.degree = m + 2
  · simp only [hdeg, ↓reduceIte, hQc]
    rw [← hc α]
    linear_combination (-(c α * π)) * hwu
  · rw [hd α (by omega)]
    simp [hdeg]

/-- For every `N ≥ 2` there is a series with the prescribed linear part satisfying the equation
below degree `N`. -/
lemma exists_defect_vanishes {q : ℕ} (H : LubinTateHyp A π q) {f g u h : PowerSeries A}
    (hf : f ∈ lubinTateSeries π q) (hg : g ∈ lubinTateSeries π q)
    (hfu : f = PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ 2 * u)
    (hgh : g = PowerSeries.X * h) (hh : PowerSeries.constantCoeff h = π) (a : σ → A) {N : ℕ}
    (hN : 2 ≤ N) :
    ∃ φ : MvPowerSeries σ A, constantCoeff φ = 0 ∧
      (∀ i, coeff (Finsupp.single i 1) φ = a i) ∧ Vanishes N (defect f g φ) := by
  induction N, hN using Nat.le_induction with
  | base =>
    obtain ⟨Q, hQdef⟩ : ∃ Q : MvPowerSeries σ A, Q = ∑ i, MvPowerSeries.C (a i) * X i := ⟨_, rfl⟩
    have hQc : ∀ j, coeff (Finsupp.single j 1) Q = a j := by
      intro j
      simp [hQdef, map_sum, coeff_C_mul, coeff_X, Finsupp.single_left_inj, Finset.sum_ite_eq]
    have hQ : Vanishes 1 Q := vanishes_one_iff.mpr (by simp [hQdef, map_sum])
    have hd0 : defect f g (0 : MvPowerSeries σ A) = 0 := by
      unfold defect
      have : (0 : MvPowerSeries σ A).subst (gSub g) = 0 := by
        rw [← coe_substAlgHom (hasSubst_gSub hgh), map_zero]
      rw [this, PowerSeries.subst_zero_of_constantCoeff_zero hf.1, sub_zero]
    refine ⟨Q, vanishes_one_iff.mp hQ, hQc, ?_⟩
    intro α hα
    have := coeff_defect_add (f := f) (g := g) hfu hgh hh (le_refl 1) (φ := 0) (Q := Q)
      (by simp) hQ (by omega : α.degree ≤ 1)
    rw [zero_add, hd0] at this
    rw [this]
    simp
  | succ N hN ih =>
    obtain ⟨φ, h0, h1, hd⟩ := ih
    obtain ⟨Q, hQ, hQd⟩ := exists_step H hf hg hfu hgh hh hN h0 hd
    refine ⟨φ + Q, ?_, ?_, hQd⟩
    · rw [map_add, h0, vanishes_one_iff.mp (hQ.mono (by omega)), add_zero]
    · intro i
      rw [map_add, h1, hQ _ (by rw [Finsupp.degree_single]; omega), add_zero]

end Series

variable {π : A} {q : ℕ}

/-- **Lemma 2.11** (Milne, *CFT*, I): for $f, g \in \mathcal F_\pi$ and a linear form
$\phi_1 = \sum_i a_i X_i$, there is a unique $\phi \in A[[X_1, \dots, X_n]]$ with $\phi = \phi_1 + (\deg \ge 2)$ and
$f(\phi(X_1, \dots, X_n)) = \phi(g(X_1), \dots, g(X_n))$. Stated for any finite index set `σ` (Milne: $n$
variables). -/
@[kb "milne2020cft" "Ch. I, Lemma 2.11"]
theorem exists_unique_lubinTate (H : LubinTateHyp A π q) {σ : Type*} [Fintype σ] [DecidableEq σ]
    (a : σ → A) {f g : PowerSeries A} (hf : f ∈ lubinTateSeries π q) (hg : g ∈ lubinTateSeries π q) :
    ∃! φ : MvPowerSeries σ A, constantCoeff φ = 0 ∧ (∀ i, coeff (Finsupp.single i 1) φ = a i) ∧
      f.subst φ = φ.subst (fun i => g.subst (X i : MvPowerSeries σ A)) := by
  obtain ⟨u, hfu⟩ := exists_eq_C_mul_X_add hf.1 hf.2.1
  obtain ⟨h, hgh, hh⟩ := exists_eq_X_mul hg.1 hg.2.1
  have hex : ∀ N : ℕ, ∃ φ : MvPowerSeries σ A, constantCoeff φ = 0 ∧
      (∀ i, coeff (Finsupp.single i 1) φ = a i) ∧ Vanishes (N + 2) (defect f g φ) :=
    fun N => exists_defect_vanishes H hf hg hfu hgh hh a (by omega)
  choose Φ hΦ0 hΦ1 hΦd using hex
  have hagree : ∀ M M' : ℕ, ∀ α : σ →₀ ℕ, α.degree < M + 2 → α.degree < M' + 2 →
      coeff α (Φ M) = coeff α (Φ M') := by
    intro M M' α h1 h2
    have := vanishes_sub_of_defect H hfu hgh hh (hΦ0 M) (hΦ0 M') (fun i => by rw [hΦ1, hΦ1])
      (N := min M M' + 2) (by omega) ((hΦd M).mono (by omega)) ((hΦd M').mono (by omega)) α
      (by omega)
    rwa [map_sub, sub_eq_zero] at this
  obtain ⟨φ, hφc⟩ : ∃ φ : MvPowerSeries σ A, ∀ α, coeff α φ = coeff α (Φ α.degree) :=
    ⟨fun α => coeff α (Φ α.degree), fun α => rfl⟩
  have hφΦ : ∀ M, Vanishes (M + 2) (φ - Φ M) := fun M α hα => by
    rw [map_sub, hφc, sub_eq_zero]
    exact hagree _ _ α (by omega) hα
  have hφ0 : constantCoeff φ = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hφc, map_zero, coeff_zero_eq_constantCoeff_apply]
    exact hΦ0 0
  have hφ1 : ∀ i, coeff (Finsupp.single i 1) φ = a i := by
    intro i
    rw [hφc, Finsupp.degree_single, hΦ1]
  have hdef : defect f g φ = 0 := by
    ext α
    have h1 := vanishes_defect_sub (f := f) hgh hφ0 (hΦ0 α.degree) (hφΦ α.degree) α (by omega)
    have h2 := hΦd α.degree α (by omega)
    rw [map_sub, h2, sub_zero] at h1
    simpa using h1
  refine ⟨φ, ⟨hφ0, hφ1, sub_eq_zero.mp hdef⟩, ?_⟩
  rintro ψ ⟨hψ0, hψ1, hψ⟩
  ext α
  have hψd : defect f g ψ = 0 := sub_eq_zero.mpr hψ
  have := vanishes_sub_of_defect H hfu hgh hh hψ0 hφ0 (fun i => by rw [hψ1, hφ1])
    (N := α.degree + 2) (by omega) (by rw [hψd]; exact Vanishes.zero _)
    (by rw [hdef]; exact Vanishes.zero _) α (by omega)
  rwa [map_sub, sub_eq_zero] at this

/-- The power series of Lemma 2.11: the unique $\phi = \sum_i a_i X_i + (\deg \ge 2)$ with
$f \circ \phi = \phi(g(X_1), \dots, g(X_n))$. -/
def lubinTatePhi (H : LubinTateHyp A π q) {σ : Type*} [Fintype σ] [DecidableEq σ] (a : σ → A)
    {f g : PowerSeries A} (hf : f ∈ lubinTateSeries π q) (hg : g ∈ lubinTateSeries π q) :
    MvPowerSeries σ A :=
  (exists_unique_lubinTate H a hf hg).exists.choose

section Phi

variable (H : LubinTateHyp A π q) {σ : Type*} [Fintype σ] [DecidableEq σ] (a : σ → A)
  {f g : PowerSeries A} (hf : f ∈ lubinTateSeries π q) (hg : g ∈ lubinTateSeries π q)

theorem lubinTatePhi_spec :
    constantCoeff (lubinTatePhi H a hf hg) = 0 ∧
      (∀ i, coeff (Finsupp.single i 1) (lubinTatePhi H a hf hg) = a i) ∧
      f.subst (lubinTatePhi H a hf hg) =
        (lubinTatePhi H a hf hg).subst (fun i => g.subst (X i : MvPowerSeries σ A)) :=
  (exists_unique_lubinTate H a hf hg).exists.choose_spec

/-- Uniqueness in Lemma 2.11, in the form used below. -/
theorem eq_lubinTatePhi {φ : MvPowerSeries σ A} (h0 : constantCoeff φ = 0)
    (h1 : ∀ i, coeff (Finsupp.single i 1) φ = a i)
    (h : f.subst φ = φ.subst (fun i => g.subst (X i : MvPowerSeries σ A))) :
    φ = lubinTatePhi H a hf hg :=
  (exists_unique_lubinTate H a hf hg).unique ⟨h0, h1, h⟩ (lubinTatePhi_spec H a hf hg)

end Phi

end NumberFieldKB.MilneCFT
