import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import QuadFormsKB.Citation

/-!
# Power series and formal group laws (Milne, *Class Field Theory*, Chapter I, §2, first half)

Composition of power series (Lemma 2.1), evaluation at elements of the maximal ideal (Remark 2.2), homomorphisms
of formal group laws (Definition 2.6, Example 2.7, Lemma 2.8) and the inverse series (Exercise 2.21).

**Conventions.** Mathlib's `FormalGroup A` (Definition 2.3) is a power series $F(X,Y) \in A[[X,Y]]$ with
$F = X + Y + (\deg \ge 2)$ and associativity; commutativity is the class `FormalGroup.IsComm`. Milne's Definition
2.3 also asks for an inverse series $i_F$; it exists and is unique (Exercise 2.21, `exists_unique_inv`), and
`FormalGroup.inv` is it. For power series $f, g$ with $g(0) = 0$, Mathlib writes $f \circ g$ as `f.subst g`, and
$F(f(T), g(T))$ is `F.toPowerSeries.subst ![f, g]`. Variables are indexed from 0 (`X 0`, `X 1` for Milne's
$X, Y$). Remark 2.4 ($F(X,0) = X$, $F(0,Y) = Y$) is Mathlib's `FormalGroup.Xzero_eq_X`, `FormalGroup.zeroX_eq_X`;
Example 2.5 (a), (b) are Mathlib's `FormalGroup.𝔾ₐ`, `FormalGroup.𝔾ₘ`.
-/

open MvPowerSeries

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

variable {A : Type*} [CommRing A]

/-! ## Lemma 2.1: composition of power series -/

/-- **Lemma 2.1 (a)** (Milne, *CFT*, I): for $f \in A[[T]]$ and $g, h \in TA[[T]]$,
$f \circ (g \circ h) = (f \circ g) \circ h$. Mathlib's `PowerSeries.subst_comp_subst_apply`, restated. -/
@[kb "milne2020cft" "Ch. I, Lemma 2.1 (a)"]
theorem subst_subst_assoc (f : PowerSeries A) {g h : PowerSeries A} (hg : PowerSeries.constantCoeff g = 0)
    (hh : PowerSeries.constantCoeff h = 0) :
    f.subst (g.subst h) = PowerSeries.subst h (f.subst g) :=
  (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hg)
    (PowerSeries.HasSubst.of_constantCoeff_zero' hh) f).symm

/-- Coefficient 1 of $f \circ g$ for $g(0) = 0$. -/
theorem coeff_one_subst_aux {g : PowerSeries A} (hg : PowerSeries.constantCoeff g = 0) (f : PowerSeries A) :
    PowerSeries.coeff 1 (f.subst g) = PowerSeries.coeff 1 f * PowerSeries.coeff 1 g := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hg),
    finsum_eq_single _ 1]
  · simp
  · intro d hd
    rcases Nat.lt_or_ge d 2 with h | h
    · have : d = 0 := by omega
      subst this
      simp
    · have : PowerSeries.coeff 1 (g ^ d) = 0 := by
        apply PowerSeries.coeff_of_lt_order
        have := PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg
        have h2 : ((1 : ℕ) : ℕ∞) < d := by exact_mod_cast h
        exact lt_of_lt_of_le (by exact_mod_cast h2) this
      simp [this]

/-- **Lemma 2.1 (b)** (Milne, *CFT*, I): for $f = \sum_{i \ge 1} a_i T^i$ there is $g \in TA[[T]]$ with
$f \circ g = T$ if and only if $a_1$ is a unit. -/
@[kb "milne2020cft" "Ch. I, Lemma 2.1 (b)"]
theorem exists_subst_eq_X_iff {f : PowerSeries A} (hf : PowerSeries.constantCoeff f = 0) :
    (∃ g : PowerSeries A, PowerSeries.constantCoeff g = 0 ∧ f.subst g = PowerSeries.X) ↔
      IsUnit (PowerSeries.coeff 1 f) := by
  constructor
  · rintro ⟨g, hg, hfg⟩
    have h1 : PowerSeries.coeff 1 (f.subst g) = PowerSeries.coeff 1 f * PowerSeries.coeff 1 g :=
      coeff_one_subst_aux hg f
    rw [hfg, PowerSeries.coeff_X] at h1
    simp only [ite_true] at h1
    exact IsUnit.of_mul_eq_one _ h1.symm
  · intro h
    exact ⟨f.substInvOfIsUnit h, PowerSeries.constantCoeff_substInvOfIsUnit f h,
      PowerSeries.subst_substInvOfIsUnit_right f hf h⟩

/-- **Lemma 2.1 (b), uniqueness and two-sidedness** (Milne, *CFT*, I): if $a_1$ is a unit, the $g \in TA[[T]]$ with
$f \circ g = T$ is unique, and $g \circ f = T$. Mathlib's `PowerSeries.substInvOfIsUnit` is $g$. -/
@[kb "milne2020cft" "Ch. I, Lemma 2.1 (b)"]
theorem existsUnique_subst_eq_X {f : PowerSeries A} (hf : PowerSeries.constantCoeff f = 0)
    (h1 : IsUnit (PowerSeries.coeff 1 f)) :
    ∃! g : PowerSeries A, PowerSeries.constantCoeff g = 0 ∧ f.subst g = PowerSeries.X ∧
      g.subst f = PowerSeries.X := by
  refine ⟨f.substInvOfIsUnit h1, ⟨PowerSeries.constantCoeff_substInvOfIsUnit f h1,
    PowerSeries.subst_substInvOfIsUnit_right f hf h1,
    PowerSeries.subst_substInvOfIsUnit_left f hf h1⟩, ?_⟩
  rintro g ⟨hg0, hg1, -⟩
  exact PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X f hf h1
    (PowerSeries.HasSubst.of_constantCoeff_zero' hg0) hg1

/-! ## Remark 2.2: evaluation at elements of the maximal ideal -/

section LocalFieldHelpers
open ValuativeRel Filter Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The topology of a nonarchimedean local field is nonarchimedean. -/
theorem nonarchK : NonarchimedeanRing K := by
  have h := Valuation.toTopologicalSpace_eq (R := K) (valuation K)
  have : @NonarchimedeanRing K _ (valuation K).subgroups_basis.topology :=
    (valuation K).subgroups_basis.nonarchimedean
  rw [← h] at this
  exact this

/-- A sequence in $\mathcal O_K$ with valuations eventually below every $\gamma$ tends to $0$. -/
theorem tendsto_zero_of_valuation_lt {ι : Type*} (l : Filter ι) (x : ι → 𝒪[K])
    (h : ∀ γ : (ValueGroupWithZero K)ˣ, ∀ᶠ i in l, valuation K (x i : K) < γ) :
    Tendsto x l (𝓝 0) := by
  rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff, show (((0 : 𝒪[K])) : K) = 0 from rfl]
  rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff]
  intro γ _
  simpa using h γ

/-- $\mathcal O_K$ is a nonarchimedean additive group. -/
theorem nonarchO : NonarchimedeanAddGroup 𝒪[K] := by
  have := nonarchK K
  refine { is_nonarchimedean := fun U hU => ?_ }
  rw [nhds_induced] at hU
  obtain ⟨W, hW, hWU⟩ := Filter.mem_comap.mp hU
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean W hW
  refine ⟨V.comap (𝒪[K].subtype.toAddMonoidHom) continuous_subtype_val, ?_⟩
  intro z hz
  apply hWU
  exact hV hz

/-- Remark 2.2, proof. -/
theorem exists_hasSum_eval_aux (f : PowerSeries 𝒪[K]) {c : 𝒪[K]} (hc : c ∈ 𝓂[K]) :
    ∃ y : 𝒪[K], HasSum (fun i : ℕ => PowerSeries.coeff i f * c ^ i) y ∧
      (PowerSeries.constantCoeff f ∈ 𝓂[K] → y ∈ 𝓂[K]) := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  have := nonarchO K
  have : CompleteSpace 𝒪[K] := inferInstance
  have hvc : valuation K (c : K) < 1 :=
    (Valuation.Integer.not_isUnit_iff_valuation_lt_one (x := c)).1
      (by simpa using (IsLocalRing.mem_maximalIdeal _).1 hc)
  have ht : Tendsto (fun i : ℕ => PowerSeries.coeff i f * c ^ i) cofinite (𝓝 0) := by
    rw [Nat.cofinite_eq_atTop]
    apply tendsto_zero_of_valuation_lt
    intro γ
    have : MulArchimedean (ValueGroupWithZero K) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hvc γ
    rw [eventually_atTop]
    refine ⟨n, fun i hi => ?_⟩
    have ha : valuation K ((PowerSeries.coeff i f : 𝒪[K]) : K) ≤ 1 :=
      (Valuation.mem_integer_iff _ _).1 (PowerSeries.coeff i f).2
    calc valuation K ((PowerSeries.coeff i f * c ^ i : 𝒪[K]) : K)
        = valuation K ((PowerSeries.coeff i f : 𝒪[K]) : K) * valuation K (c : K) ^ i := by simp
      _ ≤ 1 * valuation K (c : K) ^ i := by gcongr
      _ = valuation K (c : K) ^ i := one_mul _
      _ ≤ valuation K (c : K) ^ n := pow_le_pow_right_of_le_one' hvc.le hi
      _ < γ := hn
  have hs := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ht
  refine ⟨_, hs.hasSum, fun h0 => ?_⟩
  have hcl : IsClosed (𝓂[K] : Set 𝒪[K]) := IsNoetherianRing.isClosed_ideal _
  refine hcl.mem_of_tendsto hs.hasSum.tendsto_sum_nat (Eventually.of_forall fun s => ?_)
  refine Submodule.sum_mem _ fun i _ => ?_
  rcases i with _ | i
  · simpa using h0
  · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hc _ (Nat.succ_pos i))

end LocalFieldHelpers

open scoped ValuativeRel in
/-- **Remark 2.2** (Milne, *CFT*, I): for $A = \mathcal O_K$ (a complete discrete valuation ring), $f \in A[[T]]$ and
$c \in \mathfrak m$, the series $\sum_i a_i c^i$ converges in $A$, to an element of $\mathfrak m$ if $a_0 \in \mathfrak m$.
Milne states it for any complete discrete valuation ring; here for the ring of integers of a nonarchimedean local
field. -/
@[kb "milne2020cft" "Ch. I, Remark 2.2 (A = O_K)"]
theorem exists_hasSum_eval (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : PowerSeries 𝒪[K]) {c : 𝒪[K]} (hc : c ∈ 𝓂[K]) :
    ∃ y : 𝒪[K], HasSum (fun i : ℕ => PowerSeries.coeff i f * c ^ i) y ∧
      (PowerSeries.constantCoeff f ∈ 𝓂[K] → y ∈ 𝓂[K]) :=
  exists_hasSum_eval_aux K f hc

/-! ## Homomorphisms of formal group laws (Definition 2.6, Example 2.7) -/

/-- **Homomorphism of formal group laws** (Milne, *CFT*, I, Definition 2.6): a power series $h \in TA[[T]]$ with
$h(F(X,Y)) = G(h(X), h(Y))$. An endomorphism of $F$ is a homomorphism $F \to F$. -/
@[kb "milne2020cft" "Ch. I, Definition 2.6", ext]
structure FormalGroupHom (F G : FormalGroup A) where
  /-- The underlying power series $h(T)$. -/
  toPowerSeries : PowerSeries A
  /-- $h$ has no constant term. -/
  constantCoeff_eq_zero : PowerSeries.constantCoeff toPowerSeries = 0
  /-- $h(F(X,Y)) = G(h(X), h(Y))$. -/
  map_add : toPowerSeries.subst F.toPowerSeries =
    G.toPowerSeries.subst ![toPowerSeries.subst (X 0 : MvPowerSeries (Fin 2) A),
      toPowerSeries.subst (X 1 : MvPowerSeries (Fin 2) A)]

namespace FormalGroupHom

variable {F G : FormalGroup A}

/-- A homomorphism $h : F \to G$ is an **isomorphism** if there is a homomorphism $h' : G \to F$ with
$h \circ h' = T = h' \circ h$ (Milne, *CFT*, I, Definition 2.6). -/
@[kb "milne2020cft" "Ch. I, Definition 2.6 (isomorphism)"]
def IsIso (h : FormalGroupHom F G) : Prop :=
  ∃ h' : FormalGroupHom G F, h.toPowerSeries.subst h'.toPowerSeries = PowerSeries.X ∧
    h'.toPowerSeries.subst h.toPowerSeries = PowerSeries.X

end FormalGroupHom

/-- Substituting into $1$ gives $1$. -/
theorem psubst_one {B : Type*} [CommRing B] {a : MvPowerSeries (Fin 2) B} (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst a (1 : PowerSeries B) = 1 := by
  rw [← PowerSeries.coe_substAlgHom ha, map_one]

/-- **Example 2.7** (Milne, *CFT*, I): $(1+T)^n - 1$ is an endomorphism of the multiplicative formal group law
$X + Y + XY$. Milne takes $n = p$ prime; the statement holds for every $n$. -/
@[kb "milne2020cft" "Ch. I, Example 2.7"]
def gmPow (n : ℕ) : FormalGroupHom (FormalGroup.𝔾ₘ (R := A)) FormalGroup.𝔾ₘ where
  toPowerSeries := (1 + PowerSeries.X) ^ n - 1
  constantCoeff_eq_zero := by simp
  map_add := by
    have h1 : PowerSeries.HasSubst ((X 0 : MvPowerSeries (Fin 2) A) + X 1 + X 0 * X 1) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    have h2 : MvPowerSeries.HasSubst
        (![((1 + PowerSeries.X) ^ n - 1 : PowerSeries A).subst (X 0 : MvPowerSeries (Fin 2) A),
          ((1 + PowerSeries.X) ^ n - 1 : PowerSeries A).subst (X 1 : MvPowerSeries (Fin 2) A)]) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
        fin_cases i <;> simp [PowerSeries.constantCoeff_subst_of_constantCoeff_zero])
    have h0 : ∀ i : Fin 2, PowerSeries.HasSubst (X i : MvPowerSeries (Fin 2) A) := fun i =>
      PowerSeries.HasSubst.X i
    have e : ∀ i : Fin 2, PowerSeries.subst (X i : MvPowerSeries (Fin 2) A)
        ((1 + PowerSeries.X) ^ n - 1 : PowerSeries A) = (1 + X i) ^ n - 1 := fun i => by
      rw [PowerSeries.subst_sub (h0 i), PowerSeries.subst_pow (h0 i), PowerSeries.subst_add (h0 i),
        PowerSeries.subst_X (h0 i), psubst_one (h0 i)]
    simp only [FormalGroup.𝔾ₘ_toPowerSeries]
    rw [PowerSeries.subst_sub h1, PowerSeries.subst_pow h1, PowerSeries.subst_add h1,
      PowerSeries.subst_X h1, psubst_one h1, e, e]
    have h3 : MvPowerSeries.HasSubst
        (![(1 + X 0) ^ n - 1, (1 + X 1) ^ n - 1] : Fin 2 → MvPowerSeries (Fin 2) A) := by
      simpa [e] using h2
    rw [e, e] at h2
    rw [MvPowerSeries.subst_add h2, MvPowerSeries.subst_add h2, MvPowerSeries.subst_mul h2,
      MvPowerSeries.subst_X h2, MvPowerSeries.subst_X h2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have e2 : (1 + (X 0 + X 1 + X 0 * X 1) : MvPowerSeries (Fin 2) A) = (1 + X 0) * (1 + X 1) := by
      ring
    rw [e2, mul_pow]
    ring

/-! ## The inverse series (Exercise 2.21) -/

/-- If $G \equiv G' \pmod{X^n}$ then $K(X,G) \equiv K(X,G') \pmod{X^n}$. -/
theorem subst_agree (K : MvPowerSeries (Fin 2) A) {G G' : PowerSeries A}
    (hG : PowerSeries.constantCoeff G = 0) (hG' : PowerSeries.constantCoeff G' = 0) (n : ℕ)
    (h : ∀ m < n, PowerSeries.coeff m G = PowerSeries.coeff m G') :
    ∀ m < n, PowerSeries.coeff m (K.subst ![PowerSeries.X, G]) =
      PowerSeries.coeff m (K.subst ![PowerSeries.X, G']) := by
  intro m hm
  have h1 : ∀ i, MvPowerSeries.constantCoeff (![PowerSeries.X, G] i : MvPowerSeries Unit A) = 0 := by
    intro i; fin_cases i; exacts [PowerSeries.constantCoeff_X, hG]
  have h2 : ∀ i, MvPowerSeries.constantCoeff (![PowerSeries.X, G'] i : MvPowerSeries Unit A) = 0 := by
    intro i; fin_cases i; exacts [PowerSeries.constantCoeff_X, hG']
  have e1 := MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
    (f := K) (x := fun _ => n) (k := n) (hasSubst_of_constantCoeff_zero h1) (fun _ => le_rfl)
  have e2 := MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
    (f := K) (x := fun _ => n) (k := n) (hasSubst_of_constantCoeff_zero h2) (fun _ => le_rfl)
  have e3 : (fun i => ((![PowerSeries.X, G] i : MvPowerSeries Unit A).truncTotal n).toMvPowerSeries) =
      (fun i => ((![PowerSeries.X, G'] i : MvPowerSeries Unit A).truncTotal n).toMvPowerSeries) := by
    funext i
    fin_cases i
    · rfl
    · congr 1
      ext d
      have hd : d = Finsupp.single () (d ()) := by
        exact Finsupp.ext fun u => by rw [Subsingleton.elim u ()]; simp
      have hdeg : d.degree = d () := by
        conv_lhs => rw [hd]
        simp
      rw [MvPowerSeries.coeff_truncTotal_eq_ite, MvPowerSeries.coeff_truncTotal_eq_ite]
      by_cases hlt : d.degree < n
      · rw [ite_eq_left hlt, ite_eq_left hlt, hd]
        exact h _ (by rwa [hdeg] at hlt)
      · rw [ite_eq_right hlt, ite_eq_right hlt]
  rw [e3] at e1
  have hdeg : (Finsupp.single () m : Unit →₀ ℕ).degree < n := by simpa using hm
  have := congrArg (fun p : MvPolynomial Unit A => p.coeff (Finsupp.single () m)) (e1.trans e2.symm)
  rw [MvPowerSeries.coeff_truncTotal _ hdeg, MvPowerSeries.coeff_truncTotal _ hdeg] at this
  exact this

/-- Coefficients of $F(0, X)$. -/
theorem coeff_subst_zero_X (F : MvPowerSeries (Fin 2) A) (n : ℕ) :
    PowerSeries.coeff n (F.subst ![0, PowerSeries.X]) = MvPowerSeries.coeff (Finsupp.single 1 n) F := by
  change MvPowerSeries.coeff (Finsupp.single () n)
    (MvPowerSeries.subst ![0, MvPowerSeries.X ()] F) = _
  rw [MvPowerSeries.coeff_subst HasSubst.zero_X,
    finsum_eq_single _ (Finsupp.single 1 n)]
  · simp [MvPowerSeries.coeff_X_pow]
  · intro d hd
    by_cases h0 : d 0 = 0
    · have hd1 : d 1 ≠ n := fun h => hd (by
        ext i; fin_cases i <;> simp [h0, h])
      have hp : (d.prod fun s e => ![0, MvPowerSeries.X ()] s ^ e) =
          (MvPowerSeries.X () : MvPowerSeries Unit A) ^ d 1 := by
        rw [Finsupp.prod, Finset.prod_eq_single 1]
        · simp
        · intro b _ hb
          fin_cases b
          · simp [h0]
          · exact absurd rfl hb
        · intro h1
          simp only [Finsupp.mem_support_iff, not_not] at h1
          simp [h1]
      rw [hp, MvPowerSeries.coeff_X_pow]
      have : (Finsupp.single () n : Unit →₀ ℕ) ≠ Finsupp.single () (d 1) := by
        intro h
        exact hd1 (by simpa using (congrArg (fun f : Unit →₀ ℕ => f ()) h).symm)
      simp [this]
    · have hp : (d.prod fun s e => ![0, MvPowerSeries.X ()] s ^ e) =
          (0 : MvPowerSeries Unit A) := by
        rw [Finsupp.prod]
        refine Finset.prod_eq_zero (i := 0) (by simpa using h0) ?_
        simp [h0]
      simp [hp]

/-- $F(0,Y) = Y$ gives $F = Y + X K$. -/
theorem exists_K (F : MvPowerSeries (Fin 2) A)
    (hY : F.subst ![0, PowerSeries.X] = (PowerSeries.X : PowerSeries A)) :
    ∃ K : MvPowerSeries (Fin 2) A, F = X 1 + X 0 * K := by
  have : (X 0 : MvPowerSeries (Fin 2) A) ^ 1 ∣ F - X 1 := by
    rw [MvPowerSeries.X_pow_dvd_iff]
    intro m hm
    have h0 : m 0 = 0 := by omega
    have hm : m = Finsupp.single 1 (m 1) := by
      ext i; fin_cases i <;> simp [h0]
    have h1 := coeff_subst_zero_X F (m 1)
    rw [hY, PowerSeries.coeff_X, ← hm] at h1
    rw [map_sub, ← h1, MvPowerSeries.coeff_X, hm]
    by_cases h : m 1 = 1
    · simp [h]
    · have : Finsupp.single (1 : Fin 2) (m 1) ≠ Finsupp.single 1 1 := by
        intro h'
        exact h (by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 1) h')
      simp [h, this]
  obtain ⟨K, hK⟩ := this
  exact ⟨K, by rw [← pow_one (X 0 : MvPowerSeries (Fin 2) A), ← hK]; ring⟩

/-- Existence and uniqueness of a fixed point of a contracting map on $TA[[T]]$. -/
theorem exists_unique_fixed (Φ : PowerSeries A → PowerSeries A)
    (hΦ0 : ∀ G, PowerSeries.constantCoeff (Φ G) = 0)
    (hC : ∀ n G G', PowerSeries.constantCoeff G = 0 → PowerSeries.constantCoeff G' = 0 →
      (∀ m < n, PowerSeries.coeff m G = PowerSeries.coeff m G') →
        ∀ m < n + 1, PowerSeries.coeff m (Φ G) = PowerSeries.coeff m (Φ G')) :
    ∃! G : PowerSeries A, PowerSeries.constantCoeff G = 0 ∧ Φ G = G := by
  let S : ℕ → PowerSeries A := fun n => Nat.rec 0 (fun _ g => Φ g) n
  have hS : ∀ n, S (n + 1) = Φ (S n) := fun n => rfl
  have hS0 : ∀ n, PowerSeries.constantCoeff (S n) = 0 := by
    intro n
    cases n with
    | zero => simp [S]
    | succ n => rw [hS]; exact hΦ0 _
  have ha : ∀ n, ∀ m < n, PowerSeries.coeff m (S (n + 1)) = PowerSeries.coeff m (S n) := by
    intro n
    induction n with
    | zero => intro m hm; omega
    | succ n ih =>
      intro m hm
      rw [hS (n + 1), hS n]
      exact hC n (S (n + 1)) (S n) (hS0 (n + 1)) (hS0 n) ih m hm
  have hb : ∀ m n, m + 1 ≤ n → PowerSeries.coeff m (S n) = PowerSeries.coeff m (S (m + 1)) := by
    intro m n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [ha n m (by omega), ih]
  let G : PowerSeries A := PowerSeries.mk fun m => PowerSeries.coeff m (S (m + 1))
  have hG : ∀ m n, m < n → PowerSeries.coeff m G = PowerSeries.coeff m (S n) := by
    intro m n hmn
    rw [PowerSeries.coeff_mk, hb m n hmn]
  have hG0 : PowerSeries.constantCoeff G = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hG 0 1 one_pos,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hS0]
  have hfix : Φ G = G := by
    ext m
    have := hC m G (S m) hG0 (hS0 m) (fun k hk => hG k m hk) m (Nat.lt_succ_self m)
    rw [this, ← hS m, ← hG m (m + 1) (Nat.lt_succ_self m)]
  refine ⟨G, ⟨hG0, hfix⟩, ?_⟩
  rintro G' ⟨hG'0, hG'fix⟩
  have : ∀ n, ∀ m < n, PowerSeries.coeff m G' = PowerSeries.coeff m G := by
    intro n
    induction n with
    | zero => intro m hm; omega
    | succ n ih =>
      intro m hm
      have := hC n G' G hG'0 hG0 ih m hm
      rwa [hG'fix, hfix] at this
  ext m
  exact this (m + 1) m (Nat.lt_succ_self m)

/-- **Exercise 2.21** (Milne, *CFT*, I): if $F(X,Y) \in A[[X,Y]]$ satisfies $F(X,0) = X$ and $F(0,Y) = Y$, there is
a unique $G \in XA[[X]]$ with $F(X, G(X)) = 0$; so axiom (c) of Definition 2.3 is redundant. (Milne writes
$G = -X + \sum_{i \ge 2} a_i X^i$; the linear coefficient $-1$ is forced.) -/
@[kb "milne2020cft" "Ch. I, Exercise 2.21"]
theorem exists_unique_inv (F : MvPowerSeries (Fin 2) A)
    (hX : F.subst ![PowerSeries.X, 0] = (PowerSeries.X : PowerSeries A))
    (hY : F.subst ![0, PowerSeries.X] = (PowerSeries.X : PowerSeries A)) :
    ∃! G : PowerSeries A, PowerSeries.constantCoeff G = 0 ∧
      F.subst ![PowerSeries.X, G] = (0 : PowerSeries A) := by
  -- only `hY` is needed: `F(0,Y) = Y` gives `F = Y + X K`
  have _ := hX
  obtain ⟨K, hK⟩ := exists_K F hY
  have key : ∀ G : PowerSeries A, PowerSeries.constantCoeff G = 0 →
      F.subst ![PowerSeries.X, G] = G + PowerSeries.X * K.subst ![PowerSeries.X, G] := by
    intro G hG
    have h1 : ∀ i, MvPowerSeries.constantCoeff
        (![PowerSeries.X, G] i : MvPowerSeries Unit A) = 0 := by
      intro i; fin_cases i; exacts [PowerSeries.constantCoeff_X, hG]
    have ha := hasSubst_of_constantCoeff_zero h1
    rw [hK, MvPowerSeries.subst_add ha, MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha,
      MvPowerSeries.subst_X ha]
    rfl
  let Φ : PowerSeries A → PowerSeries A := fun G => -(PowerSeries.X * K.subst ![PowerSeries.X, G])
  have hfix : ∀ G : PowerSeries A, PowerSeries.constantCoeff G = 0 →
      (F.subst ![PowerSeries.X, G] = 0 ↔ Φ G = G) := by
    intro G hG
    rw [key G hG]
    constructor
    · intro h
      show -(PowerSeries.X * K.subst ![PowerSeries.X, G]) = G
      linear_combination -h
    · intro h
      have h' : -(PowerSeries.X * K.subst ![PowerSeries.X, G]) = G := h
      linear_combination -h'
  have hΦ0 : ∀ G, PowerSeries.constantCoeff (Φ G) = 0 := by
    intro G; simp [Φ]
  have hC : ∀ n G G', PowerSeries.constantCoeff G = 0 → PowerSeries.constantCoeff G' = 0 →
      (∀ m < n, PowerSeries.coeff m G = PowerSeries.coeff m G') →
        ∀ m < n + 1, PowerSeries.coeff m (Φ G) = PowerSeries.coeff m (Φ G') := by
    intro n G G' hG hG' h m hm
    simp only [Φ, map_neg]
    rcases m with _ | m
    · simp
    · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
      rw [subst_agree K hG hG' n h m (by omega)]
  obtain ⟨G, ⟨hG0, hGfix⟩, hGu⟩ := exists_unique_fixed Φ hΦ0 hC
  refine ⟨G, ⟨hG0, (hfix G hG0).2 hGfix⟩, ?_⟩
  rintro G' ⟨hG'0, hG'⟩
  exact hGu G' ⟨hG'0, (hfix G' hG'0).1 hG'⟩

/-- **The inverse series $i_F$** of a formal group law (Milne, *CFT*, I, Definition 2.3 (c)): the unique
$i_F \in XA[[X]]$ with $F(X, i_F(X)) = 0$ (Exercise 2.21). -/
@[kb "milne2020cft" "Ch. I, Definition 2.3 (c); Exercise 2.21"]
def _root_.FormalGroup.inv (F : FormalGroup A) : PowerSeries A :=
  (exists_unique_inv F.toPowerSeries F.Xzero_eq_X F.zeroX_eq_X).exists.choose

theorem _root_.FormalGroup.inv_spec (F : FormalGroup A) :
    PowerSeries.constantCoeff F.inv = 0 ∧
      F.toPowerSeries.subst ![PowerSeries.X, F.inv] = (0 : PowerSeries A) :=
  (exists_unique_inv F.toPowerSeries F.Xzero_eq_X F.zeroX_eq_X).exists.choose_spec

/-! ### Substitution calculus for formal group laws -/

section FormalGroupCalculus

variable {σ τ : Type*}

/-- Two series without constant term can be substituted. -/
theorem hasSubst_pair {a b : MvPowerSeries σ A} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : MvPowerSeries.HasSubst ![a, b] :=
  hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simpa)

/-- $G(a,b)$ has no constant term when $a, b$ have none. -/
theorem constantCoeff_pair {G : MvPowerSeries (Fin 2) A} (hG : MvPowerSeries.constantCoeff G = 0)
    {a b : MvPowerSeries σ A} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.constantCoeff (G.subst ![a, b]) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pair ha hb)
    (fun i => by fin_cases i <;> simpa) hG

/-- Constant coefficient of a substitution. -/
theorem constantCoeff_psubst {ψ : MvPowerSeries σ A} (hψ : MvPowerSeries.constantCoeff ψ = 0)
    {f : PowerSeries A} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst ψ f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hψ f hf

/-- Substitution commutes with forming $G(a,b)$. -/
theorem subst_pair_comp (G : MvPowerSeries (Fin 2) A) {a b : MvPowerSeries σ A}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0)
    {c : σ → MvPowerSeries τ A} (hc : MvPowerSeries.HasSubst c) :
    MvPowerSeries.subst c (G.subst ![a, b]) =
      G.subst ![MvPowerSeries.subst c a, MvPowerSeries.subst c b] := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_pair ha hb) hc]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Substitution of a single series into $G(a,b)$. -/
theorem psubst_pair_comp (G : MvPowerSeries (Fin 2) A) {a b : PowerSeries A}
    (ha : PowerSeries.constantCoeff a = 0) (hb : PowerSeries.constantCoeff b = 0)
    {ψ : MvPowerSeries τ A} (hψ : MvPowerSeries.constantCoeff ψ = 0) :
    PowerSeries.subst ψ (G.subst ![a, b]) =
      G.subst ![PowerSeries.subst ψ a, PowerSeries.subst ψ b] :=
  subst_pair_comp G ha hb (c := fun _ => ψ) (hasSubst_of_constantCoeff_zero fun _ => hψ)

/-- Substituting into $0$. -/
theorem psubst_zero {ψ : MvPowerSeries τ A} (hψ : MvPowerSeries.constantCoeff ψ = 0) :
    PowerSeries.subst ψ (0 : PowerSeries A) = 0 := by
  rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero hψ), map_zero]

/-- Mixed associativity of substitution. -/
theorem subst_psubst (c : σ → MvPowerSeries τ A) (hc : MvPowerSeries.HasSubst c)
    {p : MvPowerSeries σ A} (hp : MvPowerSeries.constantCoeff p = 0) (f : PowerSeries A) :
    MvPowerSeries.subst c (PowerSeries.subst p f) = PowerSeries.subst (MvPowerSeries.subst c p) f :=
  MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hp).const hc f

/-- $G(x, 0) = x$. -/
theorem subst_Xzero (G : FormalGroup A) {x : MvPowerSeries σ A}
    (hx : MvPowerSeries.constantCoeff x = 0) : G.toPowerSeries.subst ![x, 0] = x := by
  have h := psubst_pair_comp G.toPowerSeries (a := (PowerSeries.X : PowerSeries A)) (b := 0)
    PowerSeries.constantCoeff_X (by simp) hx
  have e : G.toPowerSeries.subst ![PowerSeries.X, (0 : PowerSeries A)] = PowerSeries.X :=
    G.Xzero_eq_X
  rw [e, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hx),
    psubst_zero hx] at h
  exact h.symm

/-- $G(0, x) = x$. -/
theorem subst_zeroX (G : FormalGroup A) {x : MvPowerSeries σ A}
    (hx : MvPowerSeries.constantCoeff x = 0) : G.toPowerSeries.subst ![0, x] = x := by
  have h := psubst_pair_comp G.toPowerSeries (a := (0 : PowerSeries A)) (b := PowerSeries.X)
    (by simp) PowerSeries.constantCoeff_X hx
  have e : G.toPowerSeries.subst ![(0 : PowerSeries A), PowerSeries.X] = PowerSeries.X :=
    G.zeroX_eq_X
  rw [e, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hx),
    psubst_zero hx] at h
  exact h.symm

/-- $G(x, i_G(x)) = 0$. -/
theorem subst_inv (G : FormalGroup A) {x : MvPowerSeries σ A}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    G.toPowerSeries.subst ![x, G.inv.subst x] = 0 := by
  have h := psubst_pair_comp G.toPowerSeries (a := (PowerSeries.X : PowerSeries A)) (b := G.inv)
    PowerSeries.constantCoeff_X G.inv_spec.1 hx
  rw [G.inv_spec.2, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hx),
    psubst_zero hx] at h
  exact h.symm

/-- $G(G(a,b),G(c,d)) = G(G(a,c),G(b,d))$ for a commutative formal group law. -/
theorem four_swap (G : FormalGroup A) [G.IsComm] {a b c d : MvPowerSeries σ A}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0)
    (hc : MvPowerSeries.constantCoeff c = 0) (hd : MvPowerSeries.constantCoeff d = 0) :
    G.toPowerSeries.subst ![G.toPowerSeries.subst ![a, b], G.toPowerSeries.subst ![c, d]] =
      G.toPowerSeries.subst ![G.toPowerSeries.subst ![a, c], G.toPowerSeries.subst ![b, d]] := by
  have h0 := G.zero_constantCoeff
  have sa := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have sb := PowerSeries.HasSubst.of_constantCoeff_zero hb
  have sc := PowerSeries.HasSubst.of_constantCoeff_zero hc
  have sd := PowerSeries.HasSubst.of_constantCoeff_zero hd
  have scd := PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_pair h0 hc hd)
  have sbd := PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_pair h0 hb hd)
  calc G.toPowerSeries.subst ![G.toPowerSeries.subst ![a, b], G.toPowerSeries.subst ![c, d]]
      = G.toPowerSeries.subst ![a, G.toPowerSeries.subst ![b, G.toPowerSeries.subst ![c, d]]] :=
        G.assoc' sa sb scd
    _ = G.toPowerSeries.subst ![a, G.toPowerSeries.subst ![G.toPowerSeries.subst ![b, c], d]] := by
        rw [G.assoc' sb sc sd]
    _ = G.toPowerSeries.subst ![a, G.toPowerSeries.subst ![G.toPowerSeries.subst ![c, b], d]] := by
        rw [G.comm' sb sc]
    _ = G.toPowerSeries.subst ![a, G.toPowerSeries.subst ![c, G.toPowerSeries.subst ![b, d]]] := by
        rw [G.assoc' sc sb sd]
    _ = G.toPowerSeries.subst ![G.toPowerSeries.subst ![a, c], G.toPowerSeries.subst ![b, d]] :=
        (G.assoc' sa sc sbd).symm

/-- Cancellation: if $G(s,t) = 0$ then $t = i_G(s)$. -/
theorem eq_inv_of_subst_eq_zero (G : FormalGroup A) [G.IsComm] {s t : MvPowerSeries σ A}
    (hs : MvPowerSeries.constantCoeff s = 0) (ht : MvPowerSeries.constantCoeff t = 0)
    (h : G.toPowerSeries.subst ![s, t] = 0) : t = G.inv.subst s := by
  have hi : MvPowerSeries.constantCoeff (G.inv.subst s) = 0 :=
    constantCoeff_psubst hs G.inv_spec.1
  have ss := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have si := PowerSeries.HasSubst.of_constantCoeff_zero hi
  have st := PowerSeries.HasSubst.of_constantCoeff_zero ht
  calc t = G.toPowerSeries.subst ![0, t] := (subst_zeroX G ht).symm
    _ = G.toPowerSeries.subst ![G.toPowerSeries.subst ![G.inv.subst s, s], t] := by
        rw [G.comm' si ss, subst_inv G hs]
    _ = G.toPowerSeries.subst ![G.inv.subst s, G.toPowerSeries.subst ![s, t]] :=
        G.assoc' si ss st
    _ = G.toPowerSeries.subst ![G.inv.subst s, 0] := by rw [h]
    _ = G.inv.subst s := subst_Xzero G hi

/-- $i_G(G(u,v)) = G(i_G(u), i_G(v))$. -/
theorem inv_subst_add (G : FormalGroup A) [G.IsComm] {u v : MvPowerSeries σ A}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    G.inv.subst (G.toPowerSeries.subst ![u, v]) =
      G.toPowerSeries.subst ![G.inv.subst u, G.inv.subst v] := by
  have h0 := G.zero_constantCoeff
  have hiu := constantCoeff_psubst hu G.inv_spec.1
  have hiv := constantCoeff_psubst hv G.inv_spec.1
  refine (eq_inv_of_subst_eq_zero G (constantCoeff_pair h0 hu hv) (constantCoeff_pair h0 hiu hiv)
    ?_).symm
  rw [four_swap G hu hv hiu hiv, subst_inv G hu, subst_inv G hv]
  have := subst_Xzero G (x := (0 : MvPowerSeries σ A)) (by simp)
  exact this

/-- Associativity of composition with a multivariate series. -/
theorem psubst_psubst {f : PowerSeries A} (hf : PowerSeries.constantCoeff f = 0)
    {ψ : MvPowerSeries τ A} (hψ : MvPowerSeries.constantCoeff ψ = 0) (h : PowerSeries A) :
    PowerSeries.subst ψ (PowerSeries.subst f h) = PowerSeries.subst (PowerSeries.subst ψ f) h :=
  PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hf)
    (PowerSeries.HasSubst.of_constantCoeff_zero hψ) h

/-- A homomorphism is compatible with $F(u,v)$. -/
theorem hom_subst_add {F G : FormalGroup A} (f : FormalGroupHom F G) {u v : MvPowerSeries σ A}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    f.toPowerSeries.subst (F.toPowerSeries.subst ![u, v]) =
      G.toPowerSeries.subst ![f.toPowerSeries.subst u, f.toPowerSeries.subst v] := by
  have hc := hasSubst_pair hu hv
  have h1 := subst_psubst ![u, v] hc F.zero_constantCoeff f.toPowerSeries
  have hX0 : MvPowerSeries.constantCoeff (X 0 : MvPowerSeries (Fin 2) A) = 0 := by simp
  have hX1 : MvPowerSeries.constantCoeff (X 1 : MvPowerSeries (Fin 2) A) = 0 := by simp
  rw [← h1, f.map_add,
    subst_pair_comp G.toPowerSeries (constantCoeff_psubst hX0 f.constantCoeff_eq_zero)
      (constantCoeff_psubst hX1 f.constantCoeff_eq_zero) hc,
    subst_psubst ![u, v] hc hX0, subst_psubst ![u, v] hc hX1,
    MvPowerSeries.subst_X hc, MvPowerSeries.subst_X hc]
  rfl

end FormalGroupCalculus

/-! ## Lemma 2.8: the group of homomorphisms and the ring of endomorphisms -/

namespace FormalGroupHom

variable {F G : FormalGroup A} [G.IsComm]

/-- $f +_G g = G(f(T), g(T))$ (Milne, *CFT*, I, before Lemma 2.8). -/
instance : Add (FormalGroupHom F G) where
  add f g :=
    { toPowerSeries := G.toPowerSeries.subst ![f.toPowerSeries, g.toPowerSeries]
      constantCoeff_eq_zero :=
        constantCoeff_pair G.zero_constantCoeff f.constantCoeff_eq_zero g.constantCoeff_eq_zero
      map_add := by
        have hX0 : MvPowerSeries.constantCoeff (X 0 : MvPowerSeries (Fin 2) A) = 0 := by simp
        have hX1 : MvPowerSeries.constantCoeff (X 1 : MvPowerSeries (Fin 2) A) = 0 := by simp
        rw [psubst_pair_comp G.toPowerSeries f.constantCoeff_eq_zero g.constantCoeff_eq_zero
          F.zero_constantCoeff, f.map_add, g.map_add,
          psubst_pair_comp G.toPowerSeries f.constantCoeff_eq_zero g.constantCoeff_eq_zero hX0,
          psubst_pair_comp G.toPowerSeries f.constantCoeff_eq_zero g.constantCoeff_eq_zero hX1]
        exact four_swap G (constantCoeff_psubst hX0 f.constantCoeff_eq_zero)
          (constantCoeff_psubst hX1 f.constantCoeff_eq_zero)
          (constantCoeff_psubst hX0 g.constantCoeff_eq_zero)
          (constantCoeff_psubst hX1 g.constantCoeff_eq_zero) }

/-- The zero homomorphism. -/
instance : Zero (FormalGroupHom F G) where
  zero :=
    { toPowerSeries := 0
      constantCoeff_eq_zero := by simp
      map_add := by
        have hX0 : MvPowerSeries.constantCoeff (X 0 : MvPowerSeries (Fin 2) A) = 0 := by simp
        have hX1 : MvPowerSeries.constantCoeff (X 1 : MvPowerSeries (Fin 2) A) = 0 := by simp
        rw [psubst_zero F.zero_constantCoeff, psubst_zero hX0, psubst_zero hX1]
        exact (subst_Xzero G (x := (0 : MvPowerSeries (Fin 2) A)) (by simp)).symm }

/-- $-f = i_G \circ f$. -/
instance : Neg (FormalGroupHom F G) where
  neg f :=
    { toPowerSeries := G.inv.subst f.toPowerSeries
      constantCoeff_eq_zero :=
        PowerSeries.constantCoeff_subst_eq_zero f.constantCoeff_eq_zero _ G.inv_spec.1
      map_add := by
        have hX0 : MvPowerSeries.constantCoeff (X 0 : MvPowerSeries (Fin 2) A) = 0 := by simp
        have hX1 : MvPowerSeries.constantCoeff (X 1 : MvPowerSeries (Fin 2) A) = 0 := by simp
        rw [psubst_psubst f.constantCoeff_eq_zero F.zero_constantCoeff, f.map_add,
          psubst_psubst f.constantCoeff_eq_zero hX0, psubst_psubst f.constantCoeff_eq_zero hX1]
        exact inv_subst_add G (constantCoeff_psubst hX0 f.constantCoeff_eq_zero)
          (constantCoeff_psubst hX1 f.constantCoeff_eq_zero) }

theorem add_toPowerSeries (f g : FormalGroupHom F G) :
    (f + g).toPowerSeries = G.toPowerSeries.subst ![f.toPowerSeries, g.toPowerSeries] := rfl

theorem zero_toPowerSeries : (0 : FormalGroupHom F G).toPowerSeries = 0 := rfl

theorem neg_toPowerSeries (f : FormalGroupHom F G) : (-f).toPowerSeries = G.inv.subst f.toPowerSeries := rfl

/-- **Lemma 2.8 (a)** (Milne, *CFT*, I): for formal group laws $F$, $G$ ($G$ commutative), $\mathrm{Hom}(F,G)$ is an
abelian group under $f +_G g$. -/
@[kb "milne2020cft" "Ch. I, Lemma 2.8 (a)"]
instance instAddCommGroup : AddCommGroup (FormalGroupHom F G) where
  add_assoc := by
    intro f g h
    ext1
    exact G.assoc' (PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero)
      (PowerSeries.HasSubst.of_constantCoeff_zero' g.constantCoeff_eq_zero)
      (PowerSeries.HasSubst.of_constantCoeff_zero' h.constantCoeff_eq_zero)
  zero_add := by
    intro f
    ext1
    exact subst_zeroX G f.constantCoeff_eq_zero
  add_zero := by
    intro f
    ext1
    exact subst_Xzero G f.constantCoeff_eq_zero
  add_comm := by
    intro f g
    ext1
    exact G.comm' (PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero)
      (PowerSeries.HasSubst.of_constantCoeff_zero' g.constantCoeff_eq_zero)
  neg_add_cancel := by
    intro f
    ext1
    have hi : PowerSeries.constantCoeff (G.inv.subst f.toPowerSeries) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero f.constantCoeff_eq_zero _ G.inv_spec.1
    show G.toPowerSeries.subst ![G.inv.subst f.toPowerSeries, f.toPowerSeries] = 0
    rw [G.comm' (PowerSeries.HasSubst.of_constantCoeff_zero' hi)
      (PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero)]
    exact subst_inv G f.constantCoeff_eq_zero
  nsmul := nsmulRec
  zsmul := zsmulRec

variable {F : FormalGroup A} [F.IsComm]

/-- Composition of endomorphisms. -/
instance : Mul (FormalGroupHom F F) where
  mul f g :=
    { toPowerSeries := f.toPowerSeries.subst g.toPowerSeries
      constantCoeff_eq_zero :=
        PowerSeries.constantCoeff_subst_eq_zero g.constantCoeff_eq_zero _ f.constantCoeff_eq_zero
      map_add := by
        have hX0 : MvPowerSeries.constantCoeff (X 0 : MvPowerSeries (Fin 2) A) = 0 := by simp
        have hX1 : MvPowerSeries.constantCoeff (X 1 : MvPowerSeries (Fin 2) A) = 0 := by simp
        rw [psubst_psubst g.constantCoeff_eq_zero F.zero_constantCoeff, g.map_add,
          hom_subst_add f (constantCoeff_psubst hX0 g.constantCoeff_eq_zero)
            (constantCoeff_psubst hX1 g.constantCoeff_eq_zero),
          psubst_psubst g.constantCoeff_eq_zero hX0, psubst_psubst g.constantCoeff_eq_zero hX1] }

/-- The identity endomorphism $T$. -/
instance : One (FormalGroupHom F F) where
  one :=
    { toPowerSeries := PowerSeries.X
      constantCoeff_eq_zero := by simp
      map_add := by
        have hX0 : MvPowerSeries.constantCoeff (X 0 : MvPowerSeries (Fin 2) A) = 0 := by simp
        have hX1 : MvPowerSeries.constantCoeff (X 1 : MvPowerSeries (Fin 2) A) = 0 := by simp
        rw [PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
          PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hX0),
          PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hX1)]
        have : (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 2) A) = X := by
          funext i; fin_cases i <;> rfl
        rw [this, MvPowerSeries.subst_self]
        rfl }

theorem mul_toPowerSeries (f g : FormalGroupHom F F) :
    (f * g).toPowerSeries = f.toPowerSeries.subst g.toPowerSeries := rfl

theorem one_toPowerSeries : (1 : FormalGroupHom F F).toPowerSeries = PowerSeries.X := rfl

/-- **Lemma 2.8 (b)** (Milne, *CFT*, I): for a (commutative) formal group law $F$, $\mathrm{End}(F)$ is a ring, with
addition $+_F$ and multiplication $f \circ g$. -/
@[kb "milne2020cft" "Ch. I, Lemma 2.8 (b)"]
instance instRing : Ring (FormalGroupHom F F) where
  mul_assoc := by
    intro f g h
    ext1
    exact (subst_subst_assoc f.toPowerSeries g.constantCoeff_eq_zero h.constantCoeff_eq_zero).symm
  one_mul := by
    intro f
    ext1
    exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' f.constantCoeff_eq_zero)
  mul_one := by
    intro f
    ext1
    exact PowerSeries.X_subst _
  left_distrib := by
    intro f g h
    ext1
    exact hom_subst_add f g.constantCoeff_eq_zero h.constantCoeff_eq_zero
  right_distrib := by
    intro f g h
    ext1
    exact psubst_pair_comp F.toPowerSeries f.constantCoeff_eq_zero g.constantCoeff_eq_zero
      h.constantCoeff_eq_zero
  zero_mul := by
    intro f
    ext1
    exact psubst_zero f.constantCoeff_eq_zero
  mul_zero := by
    intro f
    ext1
    exact PowerSeries.subst_zero_of_constantCoeff_zero f.constantCoeff_eq_zero
  zsmul := zsmulRec
  neg_add_cancel := neg_add_cancel

end FormalGroupHom

end NumberFieldKB.MilneCFT
