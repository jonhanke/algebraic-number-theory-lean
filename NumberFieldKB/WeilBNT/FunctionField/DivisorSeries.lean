import NumberFieldKB.WeilBNT.FunctionField.ZetaFinal
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Divisor series $\sum_D u^{\deg D}$ over translated cones of effective divisors

Auxiliary counting for the zeta integrals of function-field ideles (`FunctionField/IdeleZeta.lean`).
$k$ is a global function field with field of constants $\mathbb F_q$, genus $g$ and $h=\lvert D_0/P\rvert$.

* `EvForm q c N α β`: the sequence $c:\mathbb Z\to\mathbb C$ vanishes for $n<-N$ and equals $\alpha q^n+\beta$ for
  $n\ge N$. **`hasSum_evForm`**: then, for $\lvert qu\rvert<1$,
  $\sum_n c_nu^n=\sum_{-N\le n<N}c_nu^n+\alpha(qu)^N/(1-qu)+\beta u^N/(1-u)$.
* `offCount T n`: the number of effective divisors of degree $n$ prime to the finite set of places $T$.
  **`evForm_offCount`**: it has the form $\alpha q^n+\beta$ for $n$ large, with $\beta=-h/(q-1)$ if $T=\emptyset$ and
  $\beta=0$ otherwise (from $A_n=h(q^{n+1-g}-1)/(q-1)$ for $n\ge 2g-1$, Riemann–Roch, and
  $\#_{T\cup\{v\}}(n)=\#_T(n)-\#_T(n-\deg v)$).
* **`hasSum_cone`**: for a divisor $D^*$, $\sum_{D\in D^*+C_T}u^{\deg D}$ ($C_T$ = effective divisors prime to $T$)
  converges absolutely for $0<\lvert u\rvert<1/q$, with the value given by `hasSum_evForm`.
-/

open Filter Topology
open scoped BigOperators

namespace NumberFieldKB.WeilBNT.FF

noncomputable section

/-! ### Sequences of the form `α q^n + β` -/

/-- $c_n=0$ for $n<-N$ and $c_n=\alpha q^n+\beta$ for $n\ge N$. -/
def EvForm (q : ℂ) (c : ℤ → ℂ) (N : ℕ) (α β : ℂ) : Prop :=
  (∀ n : ℤ, n < -(N : ℤ) → c n = 0) ∧ ∀ n : ℤ, (N : ℤ) ≤ n → c n = α * q ^ n + β

theorem EvForm.mono {q : ℂ} {c : ℤ → ℂ} {N N' : ℕ} {α β : ℂ} (h : EvForm q c N α β) (hN : N ≤ N') :
    EvForm q c N' α β :=
  ⟨fun n hn => h.1 n (by omega), fun n hn => h.2 n (by omega)⟩

theorem EvForm.shift {q : ℂ} (hq : q ≠ 0) {c : ℤ → ℂ} {N : ℕ} {α β : ℂ} (h : EvForm q c N α β) (d : ℤ) :
    EvForm q (fun n => c (n - d)) (N + d.natAbs) (α * q ^ (-d)) β := by
  refine ⟨fun n hn => h.1 _ (by omega), fun n hn => ?_⟩
  simp only
  rw [h.2 _ (by omega), mul_assoc, ← zpow_add₀ hq]
  congr 3; ring

theorem EvForm.sub_shift {q : ℂ} (hq : q ≠ 0) {c : ℤ → ℂ} {N : ℕ} {α β : ℂ} (h : EvForm q c N α β) (d : ℕ) :
    EvForm q (fun n => c n - c (n - d)) (N + d) (α * (1 - q ^ (-(d : ℤ)))) 0 := by
  refine ⟨fun n hn => by simp only; rw [h.1 n (by omega), h.1 (n - d) (by omega), sub_zero], fun n hn => ?_⟩
  simp only
  rw [h.2 n (by omega), h.2 (n - d) (by omega), sub_eq_add_neg (n : ℤ), zpow_add₀ hq]
  ring

theorem EvForm.smul {q : ℂ} {c : ℤ → ℂ} {N : ℕ} {α β : ℂ} (h : EvForm q c N α β) (a : ℂ) :
    EvForm q (fun n => a * c n) N (a * α) (a * β) :=
  ⟨fun n hn => by simp only; rw [h.1 n hn, mul_zero], fun n hn => by simp only; rw [h.2 n hn]; ring⟩

/-- **The sum of a series with coefficients of the form `α q^n + β`.** -/
theorem hasSum_evForm {q u : ℂ} {c : ℤ → ℂ} {N : ℕ} {α β : ℂ} (h : EvForm q c N α β)
    (hqu : ‖q * u‖ < 1) (hu : ‖u‖ < 1) :
    HasSum (fun n : ℤ => c n * u ^ n)
      (∑ n ∈ Finset.Ico (-(N : ℤ)) N, c n * u ^ n + α * (q * u) ^ N / (1 - q * u) + β * u ^ N / (1 - u)) := by
  classical
  have hsplit : (fun n : ℤ => c n * u ^ n) = fun n : ℤ =>
      (if n < N then c n * u ^ n else 0) + (if (N : ℤ) ≤ n then α * (q * u) ^ n + β * u ^ n else 0) := by
    ext n
    by_cases hn : (N : ℤ) ≤ n
    · rw [if_neg (by omega), if_pos hn, zero_add, h.2 n hn, mul_zpow]; ring
    · rw [if_pos (by omega), if_neg hn, add_zero]
  have H1 : HasSum (fun n : ℤ => if n < N then c n * u ^ n else 0)
      (∑ n ∈ Finset.Ico (-(N : ℤ)) N, c n * u ^ n) := by
    rw [show (∑ n ∈ Finset.Ico (-(N : ℤ)) N, c n * u ^ n) =
        ∑ n ∈ Finset.Ico (-(N : ℤ)) N, (if n < N then c n * u ^ n else 0) from
      Finset.sum_congr rfl fun n hn => by rw [if_pos (Finset.mem_Ico.1 hn).2]]
    refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hn
    rcases hn with hn | hn
    · rw [if_pos (by omega), h.1 n hn, zero_mul]
    · rw [if_neg (by omega)]
  have H2 : HasSum (fun n : ℤ => if (N : ℤ) ≤ n then α * (q * u) ^ n + β * u ^ n else 0)
      (α * (q * u) ^ N / (1 - q * u) + β * u ^ N / (1 - u)) := by
    let i : ℕ → ℤ := fun m => (N : ℤ) + m
    have hi : Function.Injective i := fun a b hab => by simp only [i] at hab; omega
    have hrange : ∀ n ∉ Set.range i, (if (N : ℤ) ≤ n then α * (q * u) ^ n + β * u ^ n else 0) = 0 := by
      intro n hn
      rw [if_neg]
      intro hNn
      exact hn ⟨(n - N).toNat, by simp only [i]; omega⟩
    rw [← hi.hasSum_iff hrange]
    have hcomp : (fun n : ℤ => if (N : ℤ) ≤ n then α * (q * u) ^ n + β * u ^ n else 0) ∘ i =
        fun m : ℕ => α * (q * u) ^ N * (q * u) ^ m + β * u ^ N * u ^ m := by
      ext m
      simp only [Function.comp, i]
      rw [if_pos (by omega), show ((N : ℤ) + (m : ℤ)) = ((N + m : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
        pow_add, pow_add]
      ring
    rw [hcomp]
    have g1 := (hasSum_geometric_of_norm_lt_one hqu).mul_left (α * (q * u) ^ N)
    have g2 := (hasSum_geometric_of_norm_lt_one hu).mul_left (β * u ^ N)
    convert g1.add g2 using 1
    rw [div_eq_mul_inv, div_eq_mul_inv]
  have H := H1.add H2
  rw [← hsplit] at H
  convert H using 1
  ring

/-! ### Sums over a set with finite degree fibres -/

/-- **Reindexing by the degree.** If $G\subset X$ has finite fibres for $\deg:X\to\mathbb Z$, with $c_n$ elements of
degree $n$, and $\sum_nc_nu^n$ converges absolutely, then $\sum_{x\in G}u^{\deg x}$ converges absolutely to the same
value. -/
theorem hasSum_indicator_deg {X : Type*} (deg : X → ℤ) (G : Set X)
    (hfin : ∀ n : ℤ, {x | x ∈ G ∧ deg x = n}.Finite) (u : ℂ) (S : ℂ)
    (hS : HasSum (fun n : ℤ => ({x | x ∈ G ∧ deg x = n}.ncard : ℂ) * u ^ n) S)
    (hSn : Summable (fun n : ℤ => ({x | x ∈ G ∧ deg x = n}.ncard : ℝ) * ‖u‖ ^ n)) :
    HasSum (fun x => G.indicator (fun x => u ^ deg x) x) S ∧
      Summable (fun x => ‖G.indicator (fun x => u ^ deg x) x‖) := by
  classical
  set f : X → ℂ := fun x => G.indicator (fun x => u ^ deg x) x with hf
  let e := Equiv.sigmaFiberEquiv deg
  -- fibre sums
  have hfib : ∀ n : ℤ, HasSum (fun y : {x // deg x = n} => f y)
      (({x | x ∈ G ∧ deg x = n}.ncard : ℂ) * u ^ n) := by
    intro n
    set F := (hfin n).toFinset
    let Fs : Finset {x // deg x = n} := F.subtype (fun x => deg x = n)
    have : HasSum (fun y : {x // deg x = n} => f y) (∑ y ∈ Fs, f y) := hasSum_sum_of_ne_finset_zero (by
      intro y hy
      simp only [Fs, Finset.mem_subtype, F, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_and] at hy
      simp only [hf, Set.indicator_apply]
      rw [if_neg]
      intro hG; exact hy hG y.2)
    convert this using 1
    rw [Finset.sum_congr rfl (g := fun _ => u ^ n)]
    · rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => ((hfin n).mem_toFinset.1 hx).2),
        Set.ncard_eq_toFinset_card _ (hfin n)]
    · intro y hy
      simp only [Fs, Finset.mem_subtype, F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hy
      simp only [hf, Set.indicator_apply, if_pos hy.1, y.2]
  have hfibn : ∀ n : ℤ, HasSum (fun y : {x // deg x = n} => ‖f y‖)
      (({x | x ∈ G ∧ deg x = n}.ncard : ℝ) * ‖u‖ ^ n) := by
    intro n
    set F := (hfin n).toFinset
    let Fs : Finset {x // deg x = n} := F.subtype (fun x => deg x = n)
    have : HasSum (fun y : {x // deg x = n} => ‖f y‖) (∑ y ∈ Fs, ‖f y‖) := hasSum_sum_of_ne_finset_zero (by
      intro y hy
      simp only [Fs, Finset.mem_subtype, F, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_and] at hy
      simp only [hf, Set.indicator_apply]
      rw [if_neg, norm_zero]
      intro hG; exact hy hG y.2)
    convert this using 1
    rw [Finset.sum_congr rfl (g := fun _ => ‖u‖ ^ n)]
    · rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => ((hfin n).mem_toFinset.1 hx).2),
        Set.ncard_eq_toFinset_card _ (hfin n)]
    · intro y hy
      simp only [Fs, Finset.mem_subtype, F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hy
      simp only [hf, Set.indicator_apply, if_pos hy.1, y.2, norm_zpow]
  -- absolute summability on the sigma type
  have hsumσ : Summable (fun p : Σ n : ℤ, {x // deg x = n} => ‖f (e p)‖) := by
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun n => (hfibn n).summable, ?_⟩
    convert hSn using 1
    ext n
    exact (hfibn n).tsum_eq
  have hsum : Summable (fun x => ‖f x‖) := (e.summable_iff.1 hsumσ)
  refine ⟨?_, hsum⟩
  have htot : HasSum f (∑' x, f x) := (hsum.of_norm).hasSum
  have hσ : HasSum (f ∘ e) (∑' x, f x) := e.hasSum_iff.2 htot
  have := hσ.sigma (fun n => hfib n)
  rwa [this.unique hS] at htot

/-! ### Effective divisors prime to a finite set of places -/

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

set_option linter.unusedSectionVars false

open Classical

variable (Fq k) in
/-- Effective divisors with $E(v)=0$ for $v\in T$. -/
def offSet (T : Finset (Place Fq k)) : Set (Divisor Fq k) := {E | 0 ≤ E ∧ ∀ v ∈ T, E v = 0}

variable (Fq k) in
/-- The number of effective divisors of degree $n$ prime to $T$. -/
def offCount (T : Finset (Place Fq k)) (n : ℤ) : ℕ := {E | E ∈ offSet Fq k T ∧ Divisor.deg E = n}.ncard

theorem finite_offSet_deg (T : Finset (Place Fq k)) (n : ℤ) :
    {E | E ∈ offSet Fq k T ∧ Divisor.deg E = n}.Finite :=
  (Divisor.finite_setOf_effective_deg_eq (Fq := Fq) (k := k) n).subset fun E hE => ⟨hE.1.1, hE.2⟩

theorem offCount_empty (n : ℤ) : offCount Fq k ∅ n = effCountInt Fq k n := by
  rw [offCount, effCountInt, ← Nat.card_coe_set_eq]
  congr 2
  ext E
  simp [offSet]
  exact Iff.rfl

/-- $\#_{T\cup\{v\}}(n)=\#_T(n)-\#_T(n-\deg v)$. -/
theorem offCount_insert (T : Finset (Place Fq k)) {v : Place Fq k} (hv : v ∉ T) (n : ℤ) :
    (offCount Fq k (insert v T) n : ℤ) = offCount Fq k T n - offCount Fq k T (n - v.degree) := by
  classical
  set A := {E | E ∈ offSet Fq k T ∧ Divisor.deg E = n}
  set B := {E | E ∈ offSet Fq k (insert v T) ∧ Divisor.deg E = n}
  set C := {E | E ∈ offSet Fq k T ∧ Divisor.deg E = n - v.degree}
  have hBA : B ⊆ A := fun E hE => ⟨⟨hE.1.1, fun w hw => hE.1.2 w (Finset.mem_insert_of_mem hw)⟩, hE.2⟩
  have hAB : A \ B = (fun E => E + Finsupp.single v 1) '' C := by
    ext E
    constructor
    · rintro ⟨hA, hB⟩
      have hEv : E v ≠ 0 := by
        intro h0
        apply hB
        refine ⟨⟨hA.1.1, fun w hw => ?_⟩, hA.2⟩
        rcases Finset.mem_insert.1 hw with rfl | hw
        · exact h0
        · exact hA.1.2 w hw
      have hpos : 1 ≤ E v := by have := hA.1.1 v; simp at this; omega
      refine ⟨E - Finsupp.single v 1, ⟨⟨fun w => ?_, fun w hw => ?_⟩, ?_⟩, by simp⟩
      · by_cases hw : w = v
        · subst hw; simp; omega
        · simp [Ne.symm hw]; exact hA.1.1 w
      · have hwv : w ≠ v := fun h => hv (h ▸ hw)
        simp [Ne.symm hwv, hA.1.2 w hw]
      · rw [map_sub, Divisor.deg_single, hA.2]; ring
    · rintro ⟨F, hF, rfl⟩
      refine ⟨⟨⟨fun w => ?_, fun w hw => ?_⟩, ?_⟩, fun hB => ?_⟩
      · have := hF.1.1 w
        have h2 : (0 : ℤ) ≤ (Finsupp.single v (1 : ℤ)) w := by
          rw [Finsupp.single_apply]; split_ifs <;> omega
        simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply] at this h2 ⊢
        omega
      · have hwv : w ≠ v := fun h => hv (h ▸ hw)
        simp [Ne.symm hwv, hF.1.2 w hw]
      · rw [map_add, Divisor.deg_single, hF.2]; ring
      · have h1 := hB.1.2 v (Finset.mem_insert_self v T)
        have h2 := hF.1.1 v
        simp at h1 h2
        omega
  have hAfin : A.Finite := finite_offSet_deg T n
  have hinj : Function.Injective (fun E : Divisor Fq k => E + Finsupp.single v 1) := add_left_injective _
  have hcard : A.ncard = B.ncard + C.ncard := by
    rw [← Set.ncard_sdiff_add_ncard_of_subset hBA hAfin, hAB, Set.ncard_image_of_injective _ hinj, add_comm]
  show (B.ncard : ℤ) = A.ncard - C.ncard
  omega

/-- **The counts `offCount T n` have the form $\alpha q^n+\beta$ for $n$ large**, with $\beta=-h/(q-1)$ if
$T=\emptyset$ and $\beta=0$ otherwise. -/
theorem evForm_offCount (hc : IsConstantField Fq k) (T : Finset (Place Fq k)) :
    ∃ (N : ℕ) (α : ℂ), EvForm (Nat.card Fq : ℂ) (fun n => (offCount Fq k T n : ℂ)) N α
      (if T = ∅ then -((Nat.card (ClassGroup0 Fq k) : ℂ) / ((Nat.card Fq : ℂ) - 1)) else 0) := by
  classical
  have hq2 : 2 ≤ Nat.card Fq := Finite.one_lt_card
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by exact_mod_cast (show Nat.card Fq ≠ 0 by omega)
  have hqm1 : (Nat.card Fq : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast (show Nat.card Fq ≠ 1 by omega)
  induction T using Finset.induction_on with
  | empty =>
    set H := (weilZetaCoreInputs (Fq := Fq) (k := k) hc).toWeilZetaInputs
    have hZ := exists_zetaAlg hc H
    set g := H.genus
    set h := Nat.card (ClassGroup0 Fq k)
    set q := Nat.card Fq
    refine ⟨2 * g, (h : ℂ) * (q : ℂ) ^ (1 - (g : ℤ)) / ((q : ℂ) - 1), ?_⟩
    rw [if_pos rfl]
    refine ⟨fun n hn => ?_, fun n hn => ?_⟩
    · simp only
      rw [offCount_empty]
      have := hZ.neg n (by omega)
      simp only [Nat.cast_eq_zero]
      exact_mod_cast this
    · simp only
      rw [offCount_empty]
      have hb := hZ.big n (by push_cast; omega)
      have hb' : ((q : ℂ) - 1) * ((effCountInt Fq k n : ℤ) : ℂ) =
          (h : ℂ) * ((q : ℂ) ^ (n + 1 - (g : ℤ)) - 1) := by
        have := congrArg (fun x : ℚ => (x : ℂ)) hb
        push_cast at this
        exact this
      push_cast at hb'
      have hA : (effCountInt Fq k n : ℂ) = (h : ℂ) * ((q : ℂ) ^ (n + 1 - (g : ℤ)) - 1) / ((q : ℂ) - 1) := by
        rw [eq_div_iff hqm1, mul_comm]; exact hb'
      rw [hA, sub_eq_add_neg (n + 1) (g : ℤ), zpow_add₀ hq0, zpow_add₀ hq0, zpow_one,
        sub_eq_add_neg (1 : ℤ) (g : ℤ), zpow_add₀ hq0, zpow_one]
      field_simp
      ring
  | insert v T hv ih =>
    obtain ⟨N, α, hE⟩ := ih
    refine ⟨N + v.degree, α * (1 - (Nat.card Fq : ℂ) ^ (-(v.degree : ℤ))), ?_⟩
    rw [if_neg (Finset.insert_ne_empty v T)]
    have := hE.sub_shift hq0 v.degree
    have heq : (fun n => (offCount Fq k (insert v T) n : ℂ)) =
        fun n => (offCount Fq k T n : ℂ) - (offCount Fq k T (n - v.degree) : ℂ) := by
      ext n
      have := offCount_insert T hv n
      exact_mod_cast this
    rw [heq]
    exact this

/-! ### Translated cones -/

/-- The divisors $D$ with $D(v)=D^*(v)$ for $v\in T$ and $D\ge D^*$: the translate $D^*+C_T$. -/
def cone (T : Finset (Place Fq k)) (Dst : Divisor Fq k) : Set (Divisor Fq k) :=
  {D | (∀ v ∈ T, D v = Dst v) ∧ ∀ v, Dst v ≤ D v}

theorem cone_eq_image (T : Finset (Place Fq k)) (Dst : Divisor Fq k) :
    cone T Dst = (fun E => Dst + E) '' offSet Fq k T := by
  ext D
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨D - Dst, ⟨fun v => ?_, fun v hv => ?_⟩, by simp⟩
    · have := h2 v; simp; omega
    · simp [h1 v hv]
  · rintro ⟨E, ⟨hE0, hET⟩, rfl⟩
    refine ⟨fun v hv => by simp [hET v hv], fun v => ?_⟩
    have := hE0 v; simp at this ⊢; omega

theorem ncard_cone_deg (T : Finset (Place Fq k)) (Dst : Divisor Fq k) (n : ℤ) :
    {D | D ∈ cone T Dst ∧ Divisor.deg D = n}.ncard = offCount Fq k T (n - Divisor.deg Dst) := by
  rw [offCount]
  have : {D | D ∈ cone T Dst ∧ Divisor.deg D = n} =
      (fun E => Dst + E) '' {E | E ∈ offSet Fq k T ∧ Divisor.deg E = n - Divisor.deg Dst} := by
    ext D
    rw [cone_eq_image]
    constructor
    · rintro ⟨⟨E, hE, rfl⟩, hd⟩
      exact ⟨E, ⟨hE, by rw [map_add] at hd; omega⟩, rfl⟩
    · rintro ⟨E, ⟨hE, hd⟩, rfl⟩
      exact ⟨⟨E, hE, rfl⟩, by rw [map_add]; omega⟩
  rw [this, Set.ncard_image_of_injective _ (add_right_injective Dst)]

theorem finite_cone_deg (T : Finset (Place Fq k)) (Dst : Divisor Fq k) (n : ℤ) :
    {D | D ∈ cone T Dst ∧ Divisor.deg D = n}.Finite := by
  have : {D | D ∈ cone T Dst ∧ Divisor.deg D = n} =
      (fun E => Dst + E) '' {E | E ∈ offSet Fq k T ∧ Divisor.deg E = n - Divisor.deg Dst} := by
    ext D
    rw [cone_eq_image]
    constructor
    · rintro ⟨⟨E, hE, rfl⟩, hd⟩
      exact ⟨E, ⟨hE, by rw [map_add] at hd; omega⟩, rfl⟩
    · rintro ⟨E, ⟨hE, hd⟩, rfl⟩
      exact ⟨⟨E, hE, rfl⟩, by rw [map_add]; omega⟩
  rw [this]
  exact (finite_offSet_deg T _).image _

/-- **The series over a translated cone.** For $0<\lvert u\rvert$, $\lvert qu\rvert<1$, the series
$\sum_{D\in D^*+C_T}u^{\deg D}$ converges absolutely; its coefficient sequence (by degree) has the form
$\alpha q^n+\beta$ for $n$ large, with $\beta$ as in `evForm_offCount`. -/
theorem hasSum_cone (hc : IsConstantField Fq k) (T : Finset (Place Fq k)) (Dst : Divisor Fq k) :
    ∃ (N : ℕ) (α : ℂ), EvForm (Nat.card Fq : ℂ)
      (fun n => ({D | D ∈ cone T Dst ∧ Divisor.deg D = n}.ncard : ℂ)) N α
      (if T = ∅ then -((Nat.card (ClassGroup0 Fq k) : ℂ) / ((Nat.card Fq : ℂ) - 1)) else 0) ∧
      ∀ u : ℂ, ‖(Nat.card Fq : ℂ) * u‖ < 1 →
        HasSum (fun D => (cone T Dst).indicator (fun D => u ^ Divisor.deg D) D)
          (∑ n ∈ Finset.Ico (-(N : ℤ)) N, ({D | D ∈ cone T Dst ∧ Divisor.deg D = n}.ncard : ℂ) * u ^ n +
            α * ((Nat.card Fq : ℂ) * u) ^ N / (1 - (Nat.card Fq : ℂ) * u) +
            (if T = ∅ then -((Nat.card (ClassGroup0 Fq k) : ℂ) / ((Nat.card Fq : ℂ) - 1)) else 0) *
              u ^ N / (1 - u)) ∧
        Summable (fun D => ‖(cone T Dst).indicator (fun D => u ^ Divisor.deg D) D‖) := by
  have hq2 : 2 ≤ Nat.card Fq := Finite.one_lt_card
  have hq0 : (Nat.card Fq : ℂ) ≠ 0 := by exact_mod_cast (show Nat.card Fq ≠ 0 by omega)
  obtain ⟨N, α, hE⟩ := evForm_offCount hc T
  have hE' := hE.shift hq0 (Divisor.deg Dst)
  have hcoef : (fun n => ({D | D ∈ cone T Dst ∧ Divisor.deg D = n}.ncard : ℂ)) =
      fun n => (offCount Fq k T (n - Divisor.deg Dst) : ℂ) := by
    ext n; rw [ncard_cone_deg]
  refine ⟨N + (Divisor.deg Dst).natAbs, α * (Nat.card Fq : ℂ) ^ (-Divisor.deg Dst), by rw [hcoef]; exact hE',
    fun u hqu => ?_⟩
  have hqn : (1 : ℝ) ≤ ‖(Nat.card Fq : ℂ)‖ := by
    rw [Complex.norm_natCast]; exact_mod_cast (show 1 ≤ Nat.card Fq by omega)
  have hu : ‖u‖ < 1 := by
    rw [norm_mul] at hqu
    calc ‖u‖ ≤ ‖(Nat.card Fq : ℂ)‖ * ‖u‖ := le_mul_of_one_le_left (norm_nonneg _) hqn
      _ < 1 := hqu
  have hEc : EvForm (Nat.card Fq : ℂ) (fun n => ({D | D ∈ cone T Dst ∧ Divisor.deg D = n}.ncard : ℂ))
      (N + (Divisor.deg Dst).natAbs) (α * (Nat.card Fq : ℂ) ^ (-Divisor.deg Dst))
      (if T = ∅ then -((Nat.card (ClassGroup0 Fq k) : ℂ) / ((Nat.card Fq : ℂ) - 1)) else 0) := by
    rw [hcoef]; exact hE'
  have hS := hasSum_evForm hEc hqu hu
  -- absolute convergence: the same computation at `‖u‖`
  have hqu' : ‖(Nat.card Fq : ℂ) * (‖u‖ : ℂ)‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm, ← norm_mul]; exact hqu
  have hu' : ‖((‖u‖ : ℝ) : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]; exact hu
  have hSn := (hasSum_evForm hEc hqu' hu').summable
  have hSn' : Summable (fun n : ℤ => ({D | D ∈ cone T Dst ∧ Divisor.deg D = n}.ncard : ℝ) * ‖u‖ ^ n) := by
    rw [← Complex.summable_ofReal]
    convert hSn using 1
    ext n
    push_cast
    rfl
  exact hasSum_indicator_deg Divisor.deg (cone T Dst) (finite_cone_deg T Dst) u _ hS hSn'

end

end NumberFieldKB.WeilBNT.FF
