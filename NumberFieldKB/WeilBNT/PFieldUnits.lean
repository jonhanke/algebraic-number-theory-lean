import NumberFieldKB.WeilBNT.PField
import Mathlib.RingTheory.LittleWedderburn

/-!
# Weil, *Basic Number Theory*, I.§4 Lemma 5, Thm. 7 and II.§3 Prop. 8: units of $p$-fields

$K$ is a $p$-field (`hK : IsPField K p`), $R$ = `pR hK`, $P$ = `pP hK`, $q$ = `pq hK` (I.§4, Thm. 6, `PField`).
$P^\nu=\{x:\operatorname{mod}_K(x)\le q^{-\nu}\}$ (Def. 3).

* `weil_I_4_lemma5`: Lemma 5, $(1+P)^{p^n}\subseteq1+P^{n+1}$ (Weil's generality: $K$ need not be commutative).
* `weil_I_4_thm7_exists`, `weil_I_4_thm7_cyclic`, `weil_I_4_thm7_repr`: Thm. 7, $K^\times$ has a subgroup of order
  $q-1$; every such subgroup is cyclic, and $M=M^\times\cup\{0\}$ is a full set of representatives of $R/P$.
* `weil_I_4_thm7_comm`: Thm. 7, commutative case: there is only one such subgroup, the group of roots of $1$ of order
  prime to $p$.
* `weil_II_3_text_p32`: II.§3, text p. 32 (commutative $K$): every $x\in K^\times$ is uniquely
  $\pi^n\mu u$ with $n\in\mathbb Z$, $\mu\in M^\times$, $u\in1+P$.
* `weil_II_3_prop8_aut`: II.§3, Prop. 8, first assertion: for $n$ prime to $p$ and $\nu\ge1$, $x\mapsto x^n$ maps
  $1+P^\nu$ bijectively onto itself.
* `weil_II_3_prop8_index`: II.§3, Prop. 8, last assertion: $(K^\times)^n$ has index $n\cdot(n,q-1)$ in $K^\times$
  (commutative $K$, $n$ prime to $p$). It is open by `weil_II_3_prop8_open`.
-/

open Topology Filter
open scoped NNReal Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ}

/-- $1+P^\nu$, as a set: the $x$ with $\operatorname{mod}_K(x-1)\le q^{-\nu}$. -/
def onePlusP (hK : IsPField K p) (ν : ℕ) : Set K := {x | modK K (x - 1) ≤ ((pq hK : ℝ≥0) ^ ν)⁻¹}

section Toolbox

/-- $q^{-1}$, with $q=$ `pq hK`. -/
abbrev qi (hK : IsPField K p) : ℝ≥0 := ((pq hK : ℕ) : ℝ≥0)⁻¹

theorem mem_onePlusP {hK : IsPField K p} {ν : ℕ} {x : K} :
    x ∈ onePlusP hK ν ↔ modK K (x - 1) ≤ qi hK ^ ν := by
  simp [onePlusP, qi, inv_pow]

theorem modK_one' : modK K (1 : K) = 1 := by
  simpa using modK_units (K := K) 1

theorem one_lt_pq_nat (hK : IsPField K p) : 1 < pq hK := by
  obtain ⟨f, hf, h⟩ := weil_I_4_thm6_residue hK
  rw [h]; exact Nat.one_lt_pow (by omega) hK.1.one_lt

theorem qi_lt_one (hK : IsPField K p) : qi hK < 1 := by
  have := one_lt_pq_nat hK
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast this)

theorem modK_sub_le_max (hK : IsPField K p) (x y : K) :
    modK K (x - y) ≤ max (modK K x) (modK K y) := by
  rw [sub_eq_add_neg]
  refine (isUltrametricMod_of_isPField hK x (-y)).trans ?_
  rw [modK_neg]

theorem modK_le_qi_of_lt_one (hK : IsPField K p) {x : K} (hx : modK K x < 1) :
    modK K x ≤ qi hK := by
  by_cases h0 : x = 0
  · simp [h0]
  obtain ⟨n, hn⟩ := weil_I_4_thm6_range hK h0
  have hq : (1 : ℝ≥0) < (pq hK : ℝ≥0) := by exact_mod_cast one_lt_pq_nat hK
  have hn' : n ≤ -1 := by
    by_contra hc
    push Not at hc
    have : (1 : ℝ≥0) ≤ (pq hK : ℝ≥0) ^ n := one_le_zpow₀ hq.le (by omega)
    rw [← hn] at this
    exact absurd hx (not_lt.2 this)
  rw [hn]
  calc (pq hK : ℝ≥0) ^ n ≤ (pq hK : ℝ≥0) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hq.le hn'
    _ = qi hK := by simp [qi]

theorem modK_sum_le (hK : IsPField K p) {ι : Type*} (s : Finset ι) (f : ι → K) {c : ℝ≥0}
    (h : ∀ i ∈ s, modK K (f i) ≤ c) : modK K (∑ i ∈ s, f i) ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (isUltrametricMod_of_isPField hK _ _).trans
      (max_le (h a (by simp)) (ih fun i hi => h i (by simp [hi])))

theorem modK_natCast_le_one (hK : IsPField K p) (n : ℕ) : modK K (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (isUltrametricMod_of_isPField hK _ _).trans (max_le ih modK_one'.le)

theorem modK_intCast_le_one (hK : IsPField K p) (a : ℤ) : modK K (a : K) ≤ 1 := by
  rcases Int.eq_nat_or_neg a with ⟨k, rfl | rfl⟩
  · simpa using modK_natCast_le_one hK k
  · simpa [modK_neg] using modK_natCast_le_one hK k

theorem modK_choose_le (hK : IsPField K p) {i : ℕ} (hi0 : i ≠ 0) (hip : i < p) :
    modK K ((p.choose i : ℕ) : K) ≤ qi hK := by
  obtain ⟨c, hc⟩ : p ∣ p.choose i := by simpa using Nat.Prime.dvd_choose_pow (n := 1) hK.1 hi0 (by simpa using hip.ne)
  rw [hc, Nat.cast_mul, modK_mul]
  calc modK K (p : K) * modK K (c : K) ≤ qi hK * 1 :=
        mul_le_mul' (modK_le_qi_of_lt_one hK hK.2) (modK_natCast_le_one hK c)
    _ = qi hK := mul_one _

theorem modK_pow_prime_sub_one (hK : IsPField K p) {y : K} {k : ℕ} (hk : 1 ≤ k)
    (hy : modK K y ≤ qi hK ^ k) : modK K ((1 + y) ^ p - 1) ≤ qi hK ^ (k + 1) := by
  have hq1 : qi hK ≤ 1 := (qi_lt_one hK).le
  have hp2 : 2 ≤ p := hK.1.two_le
  rw [add_comm, (Commute.one_right y).add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, one_mul,
    add_sub_cancel_right]
  refine modK_sum_le hK _ _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [modK_mul, modK_pow]
  have h1 : modK K y ^ (i + 1) ≤ (qi hK ^ k) ^ (i + 1) := pow_le_pow_left₀ zero_le hy _
  rw [← pow_mul] at h1
  by_cases hip : i + 1 < p
  · have h2 := modK_choose_le hK (Nat.succ_ne_zero i) hip
    have h3 : qi hK ^ (k * (i + 1)) ≤ qi hK ^ k :=
      pow_le_pow_of_le_one zero_le hq1 (by nlinarith)
    calc modK K y ^ (i + 1) * modK K ((p.choose (i + 1) : ℕ) : K)
        ≤ qi hK ^ k * qi hK := mul_le_mul' (h1.trans h3) h2
      _ = qi hK ^ (k + 1) := (pow_succ _ _).symm
  · have hi' : i + 1 = p := by omega
    rw [hi', Nat.choose_self, Nat.cast_one, modK_one', mul_one]
    rw [hi'] at h1
    exact h1.trans (pow_le_pow_of_le_one zero_le hq1 (by nlinarith))

@[kb "weil1973bnt" "Ch. I, §4, Lemma 5"]
theorem weil_I_4_lemma5 (hK : IsPField K p) (n : ℕ) {x : K} (hx : x ∈ onePlusP hK 1) :
    x ^ (p ^ n) ∈ onePlusP hK (n + 1) := by
  rw [mem_onePlusP] at hx ⊢
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have := modK_pow_prime_sub_one hK (y := x ^ (p ^ n) - 1) (k := n + 1) (by omega) ih
    rw [add_sub_cancel, ← pow_mul, ← pow_succ] at this
    exact this

end Toolbox

section Residue

/-- The two-sided ideal $P$ of the ring $R$. -/
def pIdealU (hK : IsPField K p) : Ideal (pR hK) where
  carrier := {x | modK K (x : K) < 1}
  add_mem' {a b} ha hb := (pPAdd hK).add_mem ha hb
  zero_mem' := by simp
  smul_mem' c x hx := by
    show modK K (((c * x : pR hK)) : K) < 1
    rw [Subring.coe_mul, modK_mul]
    calc modK K (c : K) * modK K (x : K) ≤ 1 * modK K (x : K) :=
          mul_le_mul' (mem_pR.1 c.2) le_rfl
      _ < 1 := by rw [one_mul]; exact hx

theorem mem_pIdealU {hK : IsPField K p} {x : pR hK} : x ∈ pIdealU hK ↔ modK K (x : K) < 1 := Iff.rfl

instance (hK : IsPField K p) : (pIdealU hK).IsTwoSided :=
  ⟨fun {a} b ha => by
    rw [mem_pIdealU] at ha ⊢
    rw [Subring.coe_mul, modK_mul]
    calc modK K (a : K) * modK K (b : K) ≤ modK K (a : K) * 1 :=
          mul_le_mul' le_rfl (mem_pR.1 b.2)
      _ < 1 := by rw [mul_one]; exact ha⟩

theorem card_quot_pIdeal (hK : IsPField K p) : Nat.card (pR hK ⧸ pIdealU hK) = pq hK := by
  show Nat.card (pR hK ⧸ pIdealU hK) = Nat.card (pR hK ⧸ pPAdd hK)
  exact Nat.card_congr (Equiv.refl _)

instance qFinite (hK : IsPField K p) : Finite (pR hK ⧸ pIdealU hK) := by
  have h : Nat.card (pR hK ⧸ pIdealU hK) ≠ 0 := by
    rw [card_quot_pIdeal]; have := one_lt_pq_nat hK; omega
  exact Nat.finite_of_card_ne_zero h

instance qIsDomain (hK : IsPField K p) : IsDomain (pR hK ⧸ pIdealU hK) := by
  have : Nontrivial (pR hK ⧸ pIdealU hK) := ⟨⟨0, Ideal.Quotient.mk _ 1, fun h => by
    have h' : Ideal.Quotient.mk (pIdealU hK) 1 = 0 := h.symm
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_pIdealU] at h'
    simp [modK_one'] at h'⟩⟩
  have : NoZeroDivisors (pR hK ⧸ pIdealU hK) := ⟨fun {a b} h => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, mem_pIdealU, Subring.coe_mul, modK_mul] at h
    simp only [Ideal.Quotient.eq_zero_iff_mem, mem_pIdealU]
    by_contra hc
    rw [not_or, not_lt, not_lt] at hc
    have h1 : modK K (r : K) = 1 := le_antisymm (mem_pR.1 r.2) hc.1
    have h2 : modK K (s : K) = 1 := le_antisymm (mem_pR.1 s.2) hc.2
    rw [h1, h2, one_mul] at h
    exact lt_irrefl _ h⟩
  exact NoZeroDivisors.to_isDomain _

/-- The residue ring $R/P$ is a field (Wedderburn). -/
def qField (hK : IsPField K p) : Field (pR hK ⧸ pIdealU hK) :=
  letI : Fintype (pR hK ⧸ pIdealU hK) := Fintype.ofFinite _
  letI : DivisionRing (pR hK ⧸ pIdealU hK) :=
    @Fintype.divisionRingOfIsDomain _ _ _ (Classical.decEq _) _
  littleWedderburn _

/-- The residue field $R/P$, as a type synonym (so that only the field structure is visible). -/
def Qt (hK : IsPField K p) : Type _ := pR hK ⧸ pIdealU hK

instance (hK : IsPField K p) : Field (Qt hK) := qField hK

instance (hK : IsPField K p) : Finite (Qt hK) := qFinite hK

/-- The reduction map $R\to R/P$. -/
def resMap (hK : IsPField K p) : pR hK →+* Qt hK where
  toFun := Ideal.Quotient.mk (pIdealU hK)
  map_one' := (Ideal.Quotient.mk (pIdealU hK)).map_one
  map_mul' := (Ideal.Quotient.mk (pIdealU hK)).map_mul
  map_zero' := (Ideal.Quotient.mk (pIdealU hK)).map_zero
  map_add' := (Ideal.Quotient.mk (pIdealU hK)).map_add

theorem resMap_surjective (hK : IsPField K p) : Function.Surjective (resMap hK) :=
  Ideal.Quotient.mk_surjective

theorem resMap_eq_zero (hK : IsPField K p) (r : pR hK) :
    resMap hK r = 0 ↔ modK K (r : K) < 1 :=
  Ideal.Quotient.eq_zero_iff_mem

theorem card_Qt (hK : IsPField K p) : Nat.card (Qt hK) = pq hK := card_quot_pIdeal hK

theorem res_pow_card (hK : IsPField K p) (r : pR hK) (hr : modK K (r : K) = 1) :
    modK K ((r : K) ^ (pq hK - 1) - 1) < 1 := by
  have hne : resMap hK r ≠ 0 := by
    rw [Ne, resMap_eq_zero]; simp [hr]
  letI : Fintype (Qt hK) := Fintype.ofFinite _
  have h := FiniteField.pow_card_sub_one_eq_one (resMap hK r) hne
  rw [Fintype.card_eq_nat_card, card_Qt] at h
  have h3 : resMap hK (r ^ (pq hK - 1) - 1) = 0 := by
    rw [map_sub, map_pow, h, map_one, sub_self]
  rw [resMap_eq_zero] at h3
  simpa using h3

theorem exists_residue_generator (hK : IsPField K p) :
    ∃ x : K, modK K x = 1 ∧ ∀ j : ℕ, modK K (x ^ j - 1) < 1 → (pq hK - 1) ∣ j := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (Qt hK)ˣ)
  have hord : orderOf g = pq hK - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, card_Qt]
  obtain ⟨r, hr⟩ := resMap_surjective hK (g : Qt hK)
  have h1 : modK K (r : K) = 1 := by
    refine le_antisymm (mem_pR.1 r.2) (not_lt.1 fun hlt => ?_)
    have := (resMap_eq_zero hK r).2 hlt
    rw [hr] at this
    exact g.ne_zero this
  refine ⟨(r : K), h1, fun j hj => ?_⟩
  rw [← hord]
  apply orderOf_dvd_of_pow_eq_one
  have h3 : resMap hK (r ^ j - 1) = 0 := by
    rw [resMap_eq_zero]; simpa using hj
  rw [map_sub, map_pow, hr, map_one, sub_eq_zero] at h3
  exact Units.ext (by simpa using h3)

end Residue

section Teichmuller

theorem tendsto_zero_of_modK_le (hK : IsPField K p) {u : ℕ → K}
    (h : ∀ n, modK K (u n) ≤ qi hK ^ n) : Tendsto u atTop (𝓝 0) := by
  rw [hasBasis_nhds_zero_modK.tendsto_right_iff]
  intro ε hε
  have ht : Tendsto (fun n : ℕ => qi hK ^ n) atTop (𝓝 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (qi_lt_one hK)
  filter_upwards [ht.eventually (ge_mem_nhds hε)] with n hn
  exact (h n).trans hn

theorem exists_tendsto_of_step (hK : IsPField K p) {a : ℕ → K}
    (h : ∀ n, modK K (a (n + 1) - a n) ≤ qi hK ^ n) : ∃ L, Tendsto a atTop (𝓝 L) := by
  have hd : Tendsto (fun n => a (n + 1) - a n) atTop (𝓝 0) := tendsto_zero_of_modK_le hK h
  obtain ⟨s, hs⟩ := weil_I_4_cor1_thm6 hK hd
  have h2 : Tendsto (fun n => a 0 + ∑ i ∈ Finset.range n, (a (i + 1) - a i)) atTop
      (𝓝 (a 0 + s)) := tendsto_const_nhds.add hs.tendsto_sum_nat
  refine ⟨a 0 + s, h2.congr fun n => ?_⟩
  rw [Finset.sum_range_sub]; abel

/-- The Teichmuller representative $\omega(x)=\lim x^{q^n}$. -/
def teich (hK : IsPField K p) (x : K) : K := limUnder atTop (fun n : ℕ => x ^ (pq hK ^ n))

theorem teich_step (hK : IsPField K p) {x : K} (hx : modK K x = 1) (n : ℕ) :
    modK K (x ^ (pq hK ^ (n + 1)) - x ^ (pq hK ^ n)) ≤ qi hK ^ (n + 1) := by
  obtain ⟨f, hf, hqf⟩ := weil_I_4_thm6_residue hK
  have hz : x ^ (pq hK - 1) ∈ onePlusP hK 1 := by
    rw [mem_onePlusP, pow_one]
    exact modK_le_qi_of_lt_one hK (res_pow_card hK ⟨x, hx.le⟩ hx)
  have h5 := weil_I_4_lemma5 hK (f * n) hz
  rw [mem_onePlusP] at h5
  have hpq : p ^ (f * n) = pq hK ^ n := by rw [hqf, ← pow_mul]
  rw [← pow_mul, hpq] at h5
  have hq1 : 1 ≤ pq hK := (one_lt_pq_nat hK).le
  have e : pq hK ^ (n + 1) = pq hK ^ n + (pq hK - 1) * pq hK ^ n := by
    obtain ⟨q', hq'⟩ : ∃ q', pq hK = q' + 1 := ⟨pq hK - 1, by omega⟩
    rw [hq']; simp only [Nat.add_sub_cancel]; ring
  have e2 : x ^ (pq hK ^ (n + 1)) - x ^ (pq hK ^ n) =
      x ^ (pq hK ^ n) * (x ^ ((pq hK - 1) * pq hK ^ n) - 1) := by
    rw [mul_sub, mul_one, ← pow_add, ← e]
  rw [e2, modK_mul, modK_pow, hx, one_pow, one_mul]
  exact h5.trans (pow_le_pow_of_le_one zero_le (qi_lt_one hK).le (by nlinarith))

theorem teich_tendsto (hK : IsPField K p) {x : K} (hx : modK K x = 1) :
    Tendsto (fun n : ℕ => x ^ (pq hK ^ n)) atTop (𝓝 (teich hK x)) := by
  refine tendsto_nhds_limUnder (exists_tendsto_of_step hK fun n => ?_)
  exact (teich_step hK hx n).trans (pow_le_pow_of_le_one zero_le (qi_lt_one hK).le (by omega))

theorem teich_sub_le (hK : IsPField K p) {x : K} (hx : modK K x = 1) :
    modK K (teich hK x - x) ≤ qi hK := by
  have hcl : IsClosed {z : K | modK K (z - x) ≤ qi hK} :=
    isClosed_le (continuous_modK.comp (continuous_id.sub continuous_const)) continuous_const
  refine hcl.mem_of_tendsto (teich_tendsto hK hx) (Eventually.of_forall fun n => ?_)
  show modK K (x ^ (pq hK ^ n) - x) ≤ qi hK
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : modK K (x ^ (pq hK ^ (n + 1)) - x ^ (pq hK ^ n)) ≤ qi hK :=
      (teich_step hK hx n).trans (by
        calc qi hK ^ (n + 1) ≤ qi hK ^ 1 :=
              pow_le_pow_of_le_one zero_le (qi_lt_one hK).le (by omega)
          _ = qi hK := pow_one _)
    rw [← sub_add_sub_cancel _ (x ^ (pq hK ^ n))]
    exact (isUltrametricMod_of_isPField hK _ _).trans (max_le h1 ih)

theorem modK_teich (hK : IsPField K p) {x : K} (hx : modK K x = 1) : modK K (teich hK x) = 1 := by
  have h := modK_add_eq_of_lt (isUltrametricMod_of_isPField hK) (x := x) (y := teich hK x - x)
    (by rw [hx]; exact lt_of_le_of_lt (teich_sub_le hK hx) (qi_lt_one hK))
  rw [add_sub_cancel, hx] at h
  exact h

theorem teich_pow_card (hK : IsPField K p) {x : K} (hx : modK K x = 1) :
    teich hK x ^ pq hK = teich hK x := by
  have h1 : Tendsto (fun n : ℕ => (x ^ (pq hK ^ n)) ^ pq hK) atTop (𝓝 (teich hK x ^ pq hK)) :=
    ((continuous_pow (pq hK)).tendsto _).comp (teich_tendsto hK hx)
  have h2 : Tendsto (fun n : ℕ => x ^ (pq hK ^ (n + 1))) atTop (𝓝 (teich hK x)) :=
    (teich_tendsto hK hx).comp (tendsto_add_atTop_nat 1)
  have h3 : (fun n : ℕ => (x ^ (pq hK ^ n)) ^ pq hK) = fun n : ℕ => x ^ (pq hK ^ (n + 1)) := by
    funext n; rw [← pow_mul, ← pow_succ]
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

theorem teich_pow_card_sub_one (hK : IsPField K p) {x : K} (hx : modK K x = 1) :
    teich hK x ^ (pq hK - 1) = 1 := by
  have hne : teich hK x ≠ 0 := modK_pos_iff.1 (by rw [modK_teich hK hx]; exact one_pos)
  have h := teich_pow_card hK hx
  have hq1 : 1 ≤ pq hK := (one_lt_pq_nat hK).le
  have e : pq hK = (pq hK - 1) + 1 := by omega
  rw [e, pow_succ'] at h
  have h' : teich hK x * teich hK x ^ (pq hK - 1) = teich hK x * 1 := by
    rw [mul_one]; convert h using 3
  exact mul_left_cancel₀ hne h'

theorem pow_eq_pow_of_modEq {z : K} {k a b : ℕ} (hz : z ^ k = 1) (h : a ≡ b [MOD k]) :
    z ^ a = z ^ b := by
  have key : ∀ c, z ^ c = z ^ (c % k) := fun c => by
    conv_lhs => rw [← Nat.div_add_mod c k, pow_add, pow_mul, hz, one_pow, one_mul]
  rw [key a, key b, h]

theorem teich_eq_of_pow (hK : IsPField K p) {z : K} {k : ℕ} (hk : 0 < k) (hkp : Nat.Coprime k p)
    (hz : z ^ k = 1) : teich hK z = z := by
  have hz1 : modK K z = 1 := by
    have : modK K z ^ k = 1 := by rw [← modK_pow, hz, modK_one']
    exact (pow_eq_one_iff_of_nonneg zero_le hk.ne').1 this
  obtain ⟨f, hf, hqf⟩ := weil_I_4_thm6_residue hK
  have hkq : Nat.Coprime k (pq hK) := by rw [hqf]; exact hkp.pow_right f
  refine tendsto_nhds_unique_of_frequently_eq (teich_tendsto hK hz1) tendsto_const_nhds ?_
  rw [Filter.frequently_atTop]
  intro N
  refine ⟨Nat.totient k * N, Nat.le_mul_of_pos_left _ (Nat.totient_pos.2 hk), ?_⟩
  have hmod : pq hK ^ (Nat.totient k * N) ≡ 1 [MOD k] := by
    rw [pow_mul]
    simpa using ((Nat.ModEq.pow_totient hkq.symm).pow N)
  have := pow_eq_pow_of_modEq hz hmod
  simpa using this

theorem teich_eq_one (hK : IsPField K p) {z : K} (hz : modK K (z - 1) < 1) : teich hK z = 1 := by
  have hz1 : modK K z = 1 := by
    have h := modK_add_eq_of_lt (isUltrametricMod_of_isPField hK) (x := 1) (y := z - 1)
      (by rw [modK_one']; exact hz)
    rw [add_sub_cancel, modK_one'] at h
    exact h
  obtain ⟨f, hf, hqf⟩ := weil_I_4_thm6_residue hK
  have hmem : z ∈ onePlusP hK 1 := by
    rw [mem_onePlusP, pow_one]; exact modK_le_qi_of_lt_one hK hz
  have h0 : Tendsto (fun n : ℕ => z ^ (pq hK ^ n) - 1) atTop (𝓝 0) := by
    refine tendsto_zero_of_modK_le hK fun n => ?_
    have h5 := weil_I_4_lemma5 hK (f * n) hmem
    rw [mem_onePlusP] at h5
    have hpq : p ^ (f * n) = pq hK ^ n := by rw [hqf, ← pow_mul]
    rw [hpq] at h5
    exact h5.trans (pow_le_pow_of_le_one zero_le (qi_lt_one hK).le (by nlinarith))
  have h1 : Tendsto (fun n : ℕ => z ^ (pq hK ^ n)) atTop (𝓝 1) := by
    simpa using h0.add_const 1
  exact tendsto_nhds_unique (teich_tendsto hK hz1) h1

end Teichmuller

section Thm7

theorem coprime_pq_sub_one (hK : IsPField K p) : Nat.Coprime (pq hK - 1) p := by
  obtain ⟨f, hf, hqf⟩ := weil_I_4_thm6_residue hK
  have hp := hK.1
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  have h2 : p ∣ pq hK := by rw [hqf]; exact dvd_pow_self p (by omega)
  have h3 : p ∣ pq hK - (pq hK - 1) := Nat.dvd_sub h2 hd
  have h4 : pq hK - (pq hK - 1) = 1 := by have := one_lt_pq_nat hK; omega
  rw [h4] at h3
  exact hp.ne_one (Nat.dvd_one.1 h3)

theorem subgroup_elem (hK : IsPField K p) (M : Subgroup Kˣ) (hM : Nat.card M = pq hK - 1)
    (μ : M) : ((μ : Kˣ) : K) ^ (pq hK - 1) = 1 ∧ modK K ((μ : Kˣ) : K) = 1 := by
  have h : ((μ : Kˣ) : K) ^ (pq hK - 1) = 1 := by
    have h0 := congrArg (fun m : M => ((m : Kˣ) : K)) (pow_card_eq_one' (G := M) (x := μ))
    simpa [hM] using h0
  refine ⟨h, ?_⟩
  have hpos : 0 < pq hK - 1 := by have := one_lt_pq_nat hK; omega
  have : modK K ((μ : Kˣ) : K) ^ (pq hK - 1) = 1 := by rw [← modK_pow, h, modK_one']
  exact (pow_eq_one_iff_of_nonneg zero_le hpos.ne').1 this

theorem subgroup_inj (hK : IsPField K p) (M : Subgroup Kˣ) (hM : Nat.card M = pq hK - 1)
    (μ : M) (h : modK K (((μ : Kˣ) : K) - 1) < 1) : μ = 1 := by
  have hpos : 0 < pq hK - 1 := by have := one_lt_pq_nat hK; omega
  have h1 := teich_eq_of_pow hK hpos (coprime_pq_sub_one hK) (subgroup_elem hK M hM μ).1
  rw [teich_eq_one hK h] at h1
  exact Subtype.ext (Units.ext (by simpa using h1.symm))

/-- The reduction map from a subgroup `M` of order `q - 1` to `(R/P)ˣ`. -/
def redM (hK : IsPField K p) (M : Subgroup Kˣ) (hM : Nat.card M = pq hK - 1) : M →* (Qt hK)ˣ :=
  MonoidHom.toHomUnits
    ((resMap hK : pR hK →* Qt hK).comp
      { toFun := fun μ => ⟨((μ : Kˣ) : K), (subgroup_elem hK M hM μ).2.le⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp) })

theorem redM_apply (hK : IsPField K p) (M : Subgroup Kˣ) (hM : Nat.card M = pq hK - 1) (μ : M) :
    ((redM hK M hM μ : (Qt hK)ˣ) : Qt hK) =
      resMap hK ⟨((μ : Kˣ) : K), (subgroup_elem hK M hM μ).2.le⟩ := rfl

theorem redM_eq_iff (hK : IsPField K p) (M : Subgroup Kˣ) (hM : Nat.card M = pq hK - 1) (μ ν : M) :
    redM hK M hM μ = redM hK M hM ν ↔ modK K (((μ : Kˣ) : K) - ((ν : Kˣ) : K)) < 1 := by
  rw [← Units.val_inj, redM_apply, redM_apply, ← sub_eq_zero, ← map_sub, resMap_eq_zero]
  rfl

theorem redM_injective (hK : IsPField K p) (M : Subgroup Kˣ) (hM : Nat.card M = pq hK - 1) :
    Function.Injective (redM hK M hM) := by
  rw [injective_iff_map_eq_one]
  intro μ h
  have h2 : modK K (((μ : Kˣ) : K) - ((1 : M) : Kˣ)) < 1 :=
    (redM_eq_iff hK M hM μ 1).1 (by rw [h, map_one])
  exact subgroup_inj hK M hM μ (by simpa using h2)

end Thm7

@[kb "weil1973bnt" "Ch. I, §4, Thm. 7 (existence)"]
theorem weil_I_4_thm7_exists (hK : IsPField K p) : ∃ M : Subgroup Kˣ, Nat.card M = pq hK - 1 := by
  obtain ⟨x, hx, hgen⟩ := exists_residue_generator hK
  have hpos : 0 < pq hK - 1 := by have := one_lt_pq_nat hK; omega
  have hμ0 : teich hK x ≠ 0 := modK_pos_iff.1 (by rw [modK_teich hK hx]; exact one_pos)
  let u : Kˣ := Units.mk0 (teich hK x) hμ0
  have hu1 : u ^ (pq hK - 1) = 1 := Units.ext (by simpa [u] using teich_pow_card_sub_one hK hx)
  refine ⟨Subgroup.zpowers u, ?_⟩
  rw [Nat.card_zpowers]
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hu1) ?_
  have hj : (teich hK x) ^ (orderOf u) = 1 := by
    have h := congrArg Units.val (pow_orderOf_eq_one u)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    exact h
  let rx : pR hK := ⟨x, hx.le⟩
  let rμ : pR hK := ⟨teich hK x, (modK_teich hK hx).le⟩
  have hres : resMap hK rx = resMap hK rμ := by
    rw [← sub_eq_zero, ← map_sub, resMap_eq_zero]
    show modK K (x - teich hK x) < 1
    rw [← modK_neg, neg_sub]
    exact lt_of_le_of_lt (teich_sub_le hK hx) (qi_lt_one hK)
  have hrμ : rμ ^ (orderOf u) = 1 := Subtype.ext (by simpa [rμ] using hj)
  have h3 : resMap hK (rx ^ (orderOf u) - 1) = 0 := by
    rw [map_sub, map_pow, hres, ← map_pow, hrμ, map_one, sub_self]
  rw [resMap_eq_zero] at h3
  exact hgen _ (by simpa [rx] using h3)

@[kb "weil1973bnt" "Ch. I, §4, Thm. 7 (cyclic)"]
theorem weil_I_4_thm7_cyclic (hK : IsPField K p) (M : Subgroup Kˣ) (hM : Nat.card M = pq hK - 1) :
    IsCyclic M := by
  have : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; have := one_lt_pq_nat hK; omega)
  exact isCyclic_of_injective_ringHom ((Units.coeHom (Qt hK)).comp (redM hK M hM))
    (Units.val_injective.comp (redM_injective hK M hM))

/-- Thm. 7: $M^\times\cup\{0\}$ is a full set of representatives of $R/P$: its elements lie in $R$, and every
element of $R$ is congruent modulo $P$ to exactly one of them. -/
@[kb "weil1973bnt" "Ch. I, §4, Thm. 7 (a set of representatives of R/P)"]
theorem weil_I_4_thm7_repr (hK : IsPField K p) (M : Subgroup Kˣ) (hM : Nat.card M = pq hK - 1) :
    (∀ μ ∈ M, ((μ : Kˣ) : K) ∈ pR hK) ∧
      ∀ x ∈ pR hK, ∃! m : K, (m = 0 ∨ ∃ μ ∈ M, m = ((μ : Kˣ) : K)) ∧ x - m ∈ pP hK := by
  have hmod := fun μ : M => (subgroup_elem hK M hM μ).2
  refine ⟨fun μ hμ => mem_pR.2 (hmod ⟨μ, hμ⟩).le, ?_⟩
  intro x hx
  have hinj : ∀ μ ν : M, modK K (((μ : Kˣ) : K) - ((ν : Kˣ) : K)) < 1 → μ = ν :=
    fun μ ν h => redM_injective hK M hM ((redM_eq_iff hK M hM μ ν).2 h)
  rcases (mem_pR.1 hx).lt_or_eq with hlt | h1
  · refine ⟨0, ⟨Or.inl rfl, by simpa [pP] using hlt⟩, ?_⟩
    rintro m ⟨(rfl | ⟨μ, hμ, rfl⟩), hm⟩
    · rfl
    · exfalso
      have hm' : modK K (x - ((μ : Kˣ) : K)) < 1 := hm
      have h := modK_sub_le_max hK x (x - ((μ : Kˣ) : K))
      rw [sub_sub_cancel] at h
      have h2 : modK K ((μ : Kˣ) : K) < 1 := lt_of_le_of_lt h (max_lt hlt hm')
      rw [hmod ⟨μ, hμ⟩] at h2
      exact lt_irrefl _ h2
  · have hne : resMap hK ⟨x, hx⟩ ≠ 0 := by
      rw [Ne, resMap_eq_zero]; simp [h1]
    have hbij : Function.Bijective (redM hK M hM) :=
      (redM_injective hK M hM).bijective_of_nat_card_le (by rw [Nat.card_units, card_Qt, hM])
    obtain ⟨μ, hμ⟩ := hbij.2 (Units.mk0 _ hne)
    have hxμ : modK K (x - ((μ : Kˣ) : K)) < 1 := by
      have h := congrArg Units.val hμ
      rw [redM_apply, Units.val_mk0] at h
      have h3 : resMap hK (⟨x, hx⟩ - ⟨((μ : Kˣ) : K), (hmod μ).le⟩) = 0 := by
        rw [map_sub, h, sub_self]
      rw [resMap_eq_zero] at h3
      exact h3
    refine ⟨((μ : Kˣ) : K), ⟨Or.inr ⟨μ, μ.2, rfl⟩, hxμ⟩, ?_⟩
    rintro m ⟨(rfl | ⟨ν, hν, rfl⟩), hm⟩
    · exfalso
      have hm' : modK K (x - 0) < 1 := hm
      rw [sub_zero, h1] at hm'
      exact lt_irrefl _ hm'
    · have hm' : modK K (x - ((ν : Kˣ) : K)) < 1 := hm
      have h := modK_sub_le_max hK (x - ((ν : Kˣ) : K)) (x - ((μ : Kˣ) : K))
      rw [sub_sub_sub_cancel_left] at h
      have h2 : modK K (((μ : Kˣ) : K) - ((ν : Kˣ) : K)) < 1 :=
        lt_of_le_of_lt h (max_lt hm' hxμ)
      have := hinj μ ⟨ν, hν⟩ h2
      exact (congrArg (fun m : M => ((m : Kˣ) : K)) this).symm

section Prop8Tools

theorem modK_eq_one_of_op (hK : IsPField K p) {a : K} (ha : modK K (a - 1) < 1) :
    modK K a = 1 := by
  have h := modK_add_eq_of_lt (isUltrametricMod_of_isPField hK) (x := 1) (y := a - 1)
    (by rw [modK_one']; exact ha)
  rw [add_sub_cancel, modK_one'] at h
  exact h

theorem op_mul (hK : IsPField K p) {a b : K} (ha : modK K (a - 1) < 1) (hb : modK K (b - 1) < 1) :
    modK K (a * b - 1) < 1 := by
  have h1 := modK_eq_one_of_op hK ha
  have e : a * b - 1 = a * (b - 1) + (a - 1) := by rw [mul_sub, mul_one]; abel
  rw [e]
  refine lt_of_le_of_lt (isUltrametricMod_of_isPField hK _ _) (max_lt ?_ ha)
  rw [modK_mul, h1, one_mul]; exact hb

theorem op_pow (hK : IsPField K p) {a : K} (ha : modK K (a - 1) < 1) (i : ℕ) :
    modK K (a ^ i - 1) < 1 := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ]; exact op_mul hK ih ha

theorem op_of_mem (hK : IsPField K p) {ν : ℕ} (hν : 1 ≤ ν) {x : K} (hx : x ∈ onePlusP hK ν) :
    modK K (x - 1) < 1 := by
  rw [mem_onePlusP] at hx
  refine lt_of_le_of_lt hx (lt_of_le_of_lt (pow_le_pow_of_le_one zero_le (qi_lt_one hK).le hν)
    (by rw [pow_one]; exact qi_lt_one hK))

theorem modK_natCast_eq_one (hK : IsPField K p) {n : ℕ} (hn : Nat.Coprime n p) :
    modK K (n : K) = 1 := by
  refine le_antisymm (modK_natCast_le_one hK n) (not_lt.1 fun hlt => ?_)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hn
  have h : (a : K) * n + b * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hab
  have h1 : modK K ((a : K) * n) < 1 := by
    rw [modK_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (modK_intCast_le_one hK a)) hlt
  have h2 : modK K ((b : K) * p) < 1 := by
    rw [modK_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (modK_intCast_le_one hK b)) hK.2
  have := (isUltrametricMod_of_isPField hK _ _).trans_lt (max_lt h1 h2)
  rw [h, modK_one'] at this
  exact lt_irrefl _ this

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  [LocallyCompactSpace F] [T2Space F] [(𝓝[≠] (0 : F)).NeBot]

theorem geom_sum_close (hF : IsPField F p) (n : ℕ) {x y : F} (hx : modK F (x - 1) < 1)
    (hy : modK F (y - 1) < 1) :
    modK F ((∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) - n) ≤ qi hF := by
  have e : (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) - n =
      ∑ i ∈ Finset.range n, (x ^ i * y ^ (n - 1 - i) - 1) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [e]
  exact modK_sum_le hF _ _ fun i _ =>
    modK_le_qi_of_lt_one hF (op_mul hF (op_pow hF hx i) (op_pow hF hy _))

theorem modK_pow_sub_pow (hF : IsPField F p) {n : ℕ} (hn : Nat.Coprime n p) {x y : F}
    (hx : modK F (x - 1) < 1) (hy : modK F (y - 1) < 1) :
    modK F (x ^ n - y ^ n) = modK F (x - y) := by
  have hS := geom_sum_close hF n hx hy
  have hn1 := modK_natCast_eq_one hF hn
  have hSn : modK F (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) = 1 := by
    have h := modK_add_eq_of_lt (isUltrametricMod_of_isPField hF) (x := (n : F))
      (y := (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) - n)
      (by rw [hn1]; exact lt_of_le_of_lt hS (qi_lt_one hF))
    rw [add_sub_cancel, hn1] at h
    exact h
  rw [← geom_sum₂_mul, modK_mul, hSn, one_mul]

theorem newton_contract (hF : IsPField F p) {n : ℕ} (hn : Nat.Coprime n p) (y : F) {x x' : F}
    (hx : modK F (x - 1) < 1) (hx' : modK F (x' - 1) < 1) :
    modK F ((x - (x ^ n - y) / n) - (x' - (x' ^ n - y) / n)) ≤ qi hF * modK F (x - x') := by
  have hn1 := modK_natCast_eq_one hF hn
  have hn0 : (n : F) ≠ 0 := by
    intro h; rw [h, modK_eq_zero_iff.2 rfl] at hn1; exact zero_ne_one hn1
  set S := ∑ i ∈ Finset.range n, x ^ i * x' ^ (n - 1 - i) with hSdef
  have hS : x ^ n = x' ^ n + S * (x - x') := by
    have := geom_sum₂_mul x x' n
    rw [← hSdef] at this
    linear_combination -this
  have e : (x - (x ^ n - y) / n) - (x' - (x' ^ n - y) / n) = (x - x') * ((n : F) - S) / n := by
    rw [hS]; field_simp; ring
  rw [e, div_eq_mul_inv, modK_mul, modK_mul, modK_inv hn0, hn1, inv_one, mul_one, mul_comm]
  refine mul_le_mul' ?_ le_rfl
  have := geom_sum_close hF n hx hx'
  rw [← hSdef, ← modK_neg, neg_sub] at this
  exact this

theorem ne_zero_of_coprime (hK : IsPField K p) {n : ℕ} (hn : Nat.Coprime n p) : n ≠ 0 := by
  rintro rfl
  exact hK.1.ne_one ((Nat.coprime_zero_left p).1 hn)

theorem modK_zero' : modK K (0 : K) = 0 := modK_eq_zero_iff.2 rfl

theorem qi_pos (hK : IsPField K p) : 0 < qi hK := by
  have := one_lt_pq_nat hK
  exact inv_pos.2 (by exact_mod_cast (by omega : 0 < pq hK))

theorem pow_mem_onePlusP (hF : IsPField F p) {n : ℕ} (hn : Nat.Coprime n p) {ν : ℕ} (hν : 1 ≤ ν)
    {x : F} (hx : x ∈ onePlusP hF ν) : x ^ n ∈ onePlusP hF ν := by
  have h1 := op_of_mem hF hν hx
  have h := modK_pow_sub_pow hF hn h1 (y := 1) (by rw [sub_self, modK_zero']; exact one_pos)
  rw [mem_onePlusP] at hx ⊢
  rw [one_pow] at h
  rw [h]; exact hx

theorem exists_pow_eq (hF : IsPField F p) {n : ℕ} (hn : Nat.Coprime n p) {ν : ℕ} (hν : 1 ≤ ν)
    {y : F} (hy : y ∈ onePlusP hF ν) : ∃ x ∈ onePlusP hF ν, x ^ n = y := by
  have hn1 := modK_natCast_eq_one hF hn
  have hnF : (n : F) ≠ 0 := by
    intro h; rw [h, modK_zero'] at hn1; exact zero_ne_one hn1
  let T : F → F := fun z => z - (z ^ n - y) / n
  let a : ℕ → F := fun k => Nat.rec (motive := fun _ => F) 1 (fun _ z => T z) k
  have ha0 : a 0 = 1 := rfl
  have ha_succ : ∀ k, a (k + 1) = T (a k) := fun k => rfl
  have hmem : ∀ k, a k ∈ onePlusP hF ν := by
    intro k
    induction k with
    | zero => rw [ha0, mem_onePlusP, sub_self, modK_zero']; exact zero_le
    | succ k ih =>
      rw [ha_succ]
      have hzn := pow_mem_onePlusP hF hn hν ih
      rw [mem_onePlusP] at ih hzn hy ⊢
      have h1 : modK F ((a k) ^ n - y) ≤ qi hF ^ ν := by
        have e : (a k) ^ n - y = ((a k) ^ n - 1) - (y - 1) := by ring
        rw [e]; exact (modK_sub_le_max hF _ _).trans (max_le hzn hy)
      have e2 : T (a k) - 1 = (a k - 1) - ((a k) ^ n - y) / n := by simp only [T]; ring
      rw [e2]
      refine (modK_sub_le_max hF _ _).trans (max_le ih ?_)
      rw [div_eq_mul_inv, modK_mul, modK_inv hnF, hn1, inv_one, mul_one]
      exact h1
  have hop : ∀ k, modK F (a k - 1) < 1 := fun k => op_of_mem hF hν (hmem k)
  have hstep : ∀ k, modK F (a (k + 1) - a k) ≤ qi hF ^ k := by
    intro k
    induction k with
    | zero =>
      have h := modK_sub_le_max hF (a 1) (a 0)
      rw [modK_eq_one_of_op hF (hop 1), modK_eq_one_of_op hF (hop 0), max_self] at h
      simpa using h
    | succ k ih =>
      have h := newton_contract hF hn y (hop (k + 1)) (hop k)
      show modK F (T (a (k + 1)) - T (a k)) ≤ qi hF ^ (k + 1)
      refine h.trans ?_
      rw [pow_succ']
      exact mul_le_mul' le_rfl ih
  obtain ⟨L, hL⟩ := exists_tendsto_of_step hF hstep
  have hLmem : L ∈ onePlusP hF ν := by
    have hcl : IsClosed (onePlusP hF ν) := by
      have : onePlusP hF ν = {x | modK F (x - 1) ≤ qi hF ^ ν} := by
        ext x; exact mem_onePlusP
      rw [this]
      exact isClosed_le (continuous_modK.comp (continuous_id.sub continuous_const))
        continuous_const
    exact hcl.mem_of_tendsto hL (Eventually.of_forall hmem)
  refine ⟨L, hLmem, ?_⟩
  have h1 : Tendsto (fun k => a k ^ n - y) atTop (𝓝 (L ^ n - y)) :=
    (((continuous_pow n).tendsto L).comp hL).sub tendsto_const_nhds
  have h2 : Tendsto (fun k => a k - a (k + 1)) atTop (𝓝 0) := by
    simpa using hL.sub (hL.comp (tendsto_add_atTop_nat 1))
  have h3 : Tendsto (fun k => (n : F) * (a k - a (k + 1))) atTop (𝓝 0) := by
    simpa using h2.const_mul (n : F)
  have h4 : (fun k => a k ^ n - y) = fun k => (n : F) * (a k - a (k + 1)) := by
    funext k; rw [ha_succ]; simp only [T]; field_simp; ring
  rw [h4] at h1
  exact sub_eq_zero.1 (tendsto_nhds_unique h1 h3)

end Prop8Tools

/-- Thm. 7, commutative case: the subgroup of order $q-1$ is unique, and it is the group of roots of $1$ of order
prime to $p$. -/
@[kb "weil1973bnt" "Ch. I, §4, Thm. 7 (commutative case)"]
theorem weil_I_4_thm7_comm {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [LocallyCompactSpace F] [T2Space F] [(𝓝[≠] (0 : F)).NeBot] (hF : IsPField F p) (M : Subgroup Fˣ)
    (hM : Nat.card M = pq hF - 1) (x : Fˣ) :
    x ∈ M ↔ ∃ m : ℕ, 0 < m ∧ Nat.Coprime m p ∧ x ^ m = 1 := by
  have hpos : 0 < pq hF - 1 := by have := one_lt_pq_nat hF; omega
  constructor
  · intro hx
    refine ⟨pq hF - 1, hpos, coprime_pq_sub_one hF, ?_⟩
    have h := pow_card_eq_one' (G := M) (x := ⟨x, hx⟩)
    rw [hM] at h
    exact congrArg Subtype.val h
  · rintro ⟨m, hm, hmp, hxm⟩
    have hxF : (x : F) ^ m = 1 := by
      have := congrArg Units.val hxm
      simpa using this
    have hz := teich_eq_of_pow hF hm hmp hxF
    have hx1 : modK F (x : F) = 1 := by
      have : modK F (x : F) ^ m = 1 := by rw [← modK_pow, hxF, modK_one']
      exact (pow_eq_one_iff_of_nonneg zero_le hm.ne').1 this
    have h2 := teich_pow_card_sub_one hF hx1
    rw [hz] at h2
    classical
    have : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; omega)
    have : Fintype M := Fintype.ofFinite M
    let T := (Polynomial.nthRoots (pq hF - 1) (1 : F)).toFinset
    have hT : T.card ≤ pq hF - 1 :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
    let Im : Finset F := Finset.univ.image (fun μ : M => ((μ : Fˣ) : F))
    have hIm : Im ⊆ T := by
      intro y hy
      obtain ⟨μ, -, rfl⟩ := Finset.mem_image.1 hy
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hpos]
      exact (subgroup_elem hF M hM μ).1
    have hinj : Function.Injective (fun μ : M => ((μ : Fˣ) : F)) :=
      fun a b h => Subtype.ext (Units.ext h)
    have hcard : Im.card = pq hF - 1 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card, hM]
    have hEq : Im = T := Finset.eq_of_subset_of_card_le hIm (by omega)
    have hxT : (x : F) ∈ T := by
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hpos]; exact h2
    rw [← hEq] at hxT
    obtain ⟨μ, -, hμ⟩ := Finset.mem_image.1 hxT
    have : (μ : Fˣ) = x := Units.ext hμ
    rw [← this]; exact μ.2

/-- II.§3, text p. 32: $K^\times=\pi^{\mathbb Z}\times M^\times\times(1+P)$ for commutative $K$. -/
@[kb "weil1973bnt" "Ch. II, §3, text p. 32 (the decomposition of the multiplicative group)"]
theorem weil_II_3_text_p32 {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [LocallyCompactSpace F] [T2Space F] [(𝓝[≠] (0 : F)).NeBot] (hF : IsPField F p) (M : Subgroup Fˣ)
    (hM : Nat.card M = pq hF - 1) {π : F} (hπ : π ≠ 0) (hP : pP hF = (fun r => π * r) '' (pR hF : Set F))
    (x : F) (hx : x ≠ 0) :
    ∃! t : ℤ × M × F, t.2.2 ∈ onePlusP hF 1 ∧ x = π ^ t.1 * ((t.2.1 : Fˣ) : F) * t.2.2 := by
  have hmπ : modK F π = (pq hF : ℝ≥0)⁻¹ := weil_I_4_thm6_modK_prime hF hπ hP
  obtain ⟨-, hrepr⟩ := weil_I_4_thm7_repr hF M hM
  have hq1 : (1 : ℝ≥0) < (pq hF : ℝ≥0) := by exact_mod_cast one_lt_pq_nat hF
  have hq0 : (pq hF : ℝ≥0) ≠ 0 := (zero_lt_one.trans hq1).ne'
  have hmπt : ∀ t : ℤ, modK F (π ^ t) = (pq hF : ℝ≥0) ^ (-t) := by
    intro t; rw [modK_zpow hπ, hmπ, inv_zpow']
  have hmM := fun μ : M => (subgroup_elem hF M hM μ).2
  have hinj : ∀ μ ν : M, modK F (((μ : Fˣ) : F) - ((ν : Fˣ) : F)) < 1 → μ = ν :=
    fun μ ν h => redM_injective hF M hM ((redM_eq_iff hF M hM μ ν).2 h)
  have key : ∀ (a b : ℤ) (μ ν : M) (u w : F), modK F (u - 1) < 1 → modK F (w - 1) < 1 →
      π ^ a * ((μ : Fˣ) : F) * u = π ^ b * ((ν : Fˣ) : F) * w → a = b ∧ μ = ν ∧ u = w := by
    intro a b μ ν u w hu hw h
    have hu1 := modK_eq_one_of_op hF hu
    have hw1 := modK_eq_one_of_op hF hw
    have hmod := congrArg (modK F) h
    rw [modK_mul, modK_mul, modK_mul, modK_mul, hmπt, hmπt, hmM, hmM, hu1, hw1, mul_one, mul_one,
      mul_one, mul_one] at hmod
    have hab : a = b := by
      have := zpow_right_injective₀ (zero_lt_one.trans hq1) hq1.ne' hmod
      omega
    subst hab
    rw [mul_assoc, mul_assoc] at h
    have h' := mul_left_cancel₀ (zpow_ne_zero _ hπ) h
    have hμν : μ = ν := by
      apply hinj
      have e : ((μ : Fˣ) : F) - ((ν : Fˣ) : F) =
          ((ν : Fˣ) : F) * (w - 1) - ((μ : Fˣ) : F) * (u - 1) := by linear_combination h'
      rw [e]
      refine lt_of_le_of_lt (modK_sub_le_max hF _ _) (max_lt ?_ ?_)
      · rw [modK_mul, hmM]; simpa using hw
      · rw [modK_mul, hmM]; simpa using hu
    subst hμν
    exact ⟨rfl, rfl, mul_left_cancel₀ (Units.ne_zero _) h'⟩
  obtain ⟨n, hn⟩ := weil_I_4_thm6_range hF hx
  have hπt0 : π ^ (-n) ≠ 0 := zpow_ne_zero _ hπ
  have hy1 : modK F ((π ^ (-n))⁻¹ * x) = 1 := by
    rw [modK_mul, modK_inv hπt0, hmπt, hn, neg_neg]
    exact inv_mul_cancel₀ (zpow_ne_zero _ hq0)
  obtain ⟨m', ⟨hm'1, hm'2⟩, -⟩ := hrepr ((π ^ (-n))⁻¹ * x) (mem_pR.2 hy1.le)
  rcases hm'1 with rfl | ⟨μ, hμ, rfl⟩
  · exfalso
    have : modK F ((π ^ (-n))⁻¹ * x - 0) < 1 := hm'2
    rw [sub_zero, hy1] at this
    exact lt_irrefl _ this
  have hμ1 := hmM ⟨μ, hμ⟩
  have hμ0 : ((μ : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have hm'2' : modK F ((π ^ (-n))⁻¹ * x - ((μ : Fˣ) : F)) < 1 := hm'2
  have hu : modK F ((π ^ (-n))⁻¹ * x / ((μ : Fˣ) : F) - 1) < 1 := by
    have e : (π ^ (-n))⁻¹ * x / ((μ : Fˣ) : F) - 1 =
        ((π ^ (-n))⁻¹ * x - ((μ : Fˣ) : F)) / ((μ : Fˣ) : F) := by field_simp
    rw [e, div_eq_mul_inv, modK_mul, modK_inv hμ0]
    simp only [hμ1, inv_one, mul_one]
    exact hm'2'
  refine ⟨(-n, ⟨μ, hμ⟩, (π ^ (-n))⁻¹ * x / ((μ : Fˣ) : F)), ⟨?_, ?_⟩, ?_⟩
  · show (π ^ (-n))⁻¹ * x / ((μ : Fˣ) : F) ∈ onePlusP hF 1
    rw [mem_onePlusP, pow_one]; exact modK_le_qi_of_lt_one hF hu
  · show x = π ^ (-n) * ((μ : Fˣ) : F) * ((π ^ (-n))⁻¹ * x / ((μ : Fˣ) : F))
    field_simp
  · rintro ⟨a, ν, w⟩ ⟨hw, hxe⟩
    have hw' : modK F (w - 1) < 1 := op_of_mem hF le_rfl hw
    have hxe' : x = π ^ a * ((ν : Fˣ) : F) * w := hxe
    have hxe2 : π ^ a * ((ν : Fˣ) : F) * w =
        π ^ (-n) * ((μ : Fˣ) : F) * ((π ^ (-n))⁻¹ * x / ((μ : Fˣ) : F)) := by
      rw [← hxe']; field_simp
    obtain ⟨h1, h2, h3⟩ := key a (-n) ν ⟨μ, hμ⟩ w _ hw' hu hxe2
    rw [h1, h2, h3]

@[kb "weil1973bnt" "Ch. II, §3, Prop. 8 (x ↦ x^n is an automorphism of 1 + P^ν)"]
theorem weil_II_3_prop8_aut {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [LocallyCompactSpace F] [T2Space F] [(𝓝[≠] (0 : F)).NeBot] (hF : IsPField F p) {n : ℕ}
    (hn : Nat.Coprime n p) {ν : ℕ} (hν : 1 ≤ ν) :
    Set.BijOn (fun x : F => x ^ n) (onePlusP hF ν) (onePlusP hF ν) := by
  refine ⟨fun x hx => pow_mem_onePlusP hF hn hν hx, fun x hx x' hx' h => ?_, fun y hy => ?_⟩
  · have := modK_pow_sub_pow hF hn (op_of_mem hF hν hx) (op_of_mem hF hν hx')
    have h' : x ^ n = x' ^ n := h
    rw [h', sub_self, modK_zero'] at this
    exact sub_eq_zero.1 (modK_eq_zero_iff.1 this.symm)
  · obtain ⟨x, hx, hxy⟩ := exists_pow_eq hF hn hν hy
    exact ⟨x, hx, hxy⟩

@[kb "weil1973bnt" "Ch. II, §3, Prop. 8 (the n-th powers are open)"]
theorem weil_II_3_prop8_open {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [LocallyCompactSpace F] [T2Space F] [(𝓝[≠] (0 : F)).NeBot] (hF : IsPField F p) {n : ℕ}
    (hn : Nat.Coprime n p) (hn0 : 0 < n) :
    IsOpen ((Units.val : Fˣ → F) '' (MonoidHom.range (powMonoidHom n : Fˣ →* Fˣ) : Set Fˣ)) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨u, ⟨w, rfl⟩, rfl⟩
  set a : F := (((powMonoidHom n : Fˣ →* Fˣ) w : Fˣ) : F) with ha
  have ha' : a = (w : F) ^ n := by simp [ha]
  have ha0 : a ≠ 0 := Units.ne_zero _
  have hapos : 0 < modK F a := modK_pos_iff.2 ha0
  have hc : 0 < modK F a * qi hF := mul_pos hapos (qi_pos hF)
  have hV : {z : F | modK F (z - a) < modK F a * qi hF} ∈ 𝓝 a := by
    refine (isOpen_lt (continuous_modK.comp (continuous_id.sub continuous_const))
      continuous_const).mem_nhds ?_
    show modK F (a - a) < modK F a * qi hF
    rw [sub_self, modK_zero']; exact hc
  refine Filter.mem_of_superset hV fun z hz => ?_
  have hz' : modK F (z - a) < modK F a * qi hF := hz
  have hv : z / a ∈ onePlusP hF 1 := by
    rw [mem_onePlusP, pow_one]
    have e : z / a - 1 = (z - a) / a := by field_simp
    rw [e, div_eq_mul_inv, modK_mul, modK_inv ha0]
    exact ((mul_inv_lt_iff₀ hapos).2 (by rwa [mul_comm] at hz')).le
  obtain ⟨x, hx, hxz⟩ := exists_pow_eq hF hn le_rfl hv
  have hx1 : modK F x = 1 := modK_eq_one_of_op hF (op_of_mem hF le_rfl hx)
  have hx0 : x ≠ 0 := fun h => by rw [h, modK_zero'] at hx1; exact zero_ne_one hx1
  refine ⟨(w * Units.mk0 x hx0) ^ n, ⟨w * Units.mk0 x hx0, rfl⟩, ?_⟩
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mk0, mul_pow, hxz, ← ha']
  field_simp

@[kb "weil1973bnt" "Ch. II, §3, Prop. 8 (the index n·(n, q-1))"]
theorem weil_II_3_prop8_index {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [LocallyCompactSpace F] [T2Space F] [(𝓝[≠] (0 : F)).NeBot] (hF : IsPField F p) {n : ℕ}
    (hn : Nat.Coprime n p) (hn0 : 0 < n) :
    (MonoidHom.range (powMonoidHom n : Fˣ →* Fˣ)).index = n * Nat.gcd n (pq hF - 1) := by
  obtain ⟨M, hM⟩ := weil_I_4_thm7_exists hF
  obtain ⟨π, hπ, hP, -⟩ := weil_I_4_thm6_prime hF
  have hdec : ∀ x : Fˣ, ∃! t : ℤ × M × F, t.2.2 ∈ onePlusP hF 1 ∧
      (x : F) = π ^ t.1 * ((t.2.1 : Fˣ) : F) * t.2.2 :=
    fun x => weil_II_3_text_p32 hF M hM hπ hP x x.ne_zero
  choose d hd hdu using hdec
  have hone1 : (1 : F) ∈ onePlusP hF 1 := by
    rw [mem_onePlusP, sub_self, modK_zero']; exact zero_le
  have hmul : ∀ x y : Fˣ, d (x * y) =
      ((d x).1 + (d y).1, (d x).2.1 * (d y).2.1, (d x).2.2 * (d y).2.2) := by
    intro x y
    symm
    apply hdu
    obtain ⟨hx1, hx2⟩ := hd x
    obtain ⟨hy1, hy2⟩ := hd y
    refine ⟨?_, ?_⟩
    · show (d x).2.2 * (d y).2.2 ∈ onePlusP hF 1
      rw [mem_onePlusP, pow_one]
      exact modK_le_qi_of_lt_one hF
        (op_mul hF (op_of_mem hF le_rfl hx1) (op_of_mem hF le_rfl hy1))
    · show ((x * y : Fˣ) : F) = π ^ ((d x).1 + (d y).1) *
        (((((d x).2.1 * (d y).2.1 : M) : Fˣ)) : F) * ((d x).2.2 * (d y).2.2)
      rw [Units.val_mul, hx2, hy2]
      simp only [zpow_add₀ hπ, Subgroup.coe_mul, Units.val_mul]
      ring
  have hone : d 1 = (0, 1, 1) := by
    symm
    apply hdu
    refine ⟨hone1, ?_⟩
    simp
  let lam : Fˣ →* Multiplicative ℤ × M :=
    { toFun := fun x => (Multiplicative.ofAdd (d x).1, (d x).2.1)
      map_one' := by rw [hone]; rfl
      map_mul' := fun x y => by rw [hmul]; rfl }
  have hlam : ∀ x, lam x = (Multiplicative.ofAdd (d x).1, (d x).2.1) := fun _ => rfl
  let S : Subgroup (Multiplicative ℤ × M) :=
    (AddSubgroup.zmultiples (n : ℤ)).toSubgroup.prod (powMonoidHom n : M →* M).range
  have hS : ∀ s : Multiplicative ℤ × M, s ∈ S ↔
      (∃ k : ℤ, k * (n : ℤ) = Multiplicative.toAdd s.1) ∧ ∃ μ : M, μ ^ n = s.2 := by
    intro s
    simp only [S, Subgroup.mem_prod, MonoidHom.mem_range, powMonoidHom_apply]
    refine and_congr ?_ Iff.rfl
    show Multiplicative.toAdd s.1 ∈ AddSubgroup.zmultiples (n : ℤ) ↔ _
    rw [AddSubgroup.mem_zmultiples_iff]
    simp only [smul_eq_mul]
  have hsurj : Function.Surjective lam := by
    rintro ⟨a, μ⟩
    refine ⟨(Units.mk0 π hπ) ^ (Multiplicative.toAdd a) * (μ : Fˣ), ?_⟩
    have h := hdu ((Units.mk0 π hπ) ^ (Multiplicative.toAdd a) * (μ : Fˣ))
      (Multiplicative.toAdd a, μ, 1) ⟨hone1, by simp⟩
    rw [hlam, ← h]
    rfl
  have hH : MonoidHom.range (powMonoidHom n : Fˣ →* Fˣ) = S.comap lam := by
    ext x
    rw [Subgroup.mem_comap, hS]
    constructor
    · rintro ⟨y, rfl⟩
      rw [show (powMonoidHom n : Fˣ →* Fˣ) y = y ^ n from rfl, map_pow, Prod.pow_fst, Prod.pow_snd,
        toAdd_pow]
      exact ⟨⟨Multiplicative.toAdd (lam y).1, by simp [mul_comm]⟩, ⟨(lam y).2, rfl⟩⟩
    · rintro ⟨⟨k, hk⟩, ν, hν⟩
      rw [hlam] at hk hν
      simp only [toAdd_ofAdd] at hk
      obtain ⟨w, hw, hwu⟩ := exists_pow_eq hF hn le_rfl (hd x).1
      have hw1 : modK F w = 1 := modK_eq_one_of_op hF (op_of_mem hF le_rfl hw)
      have hw0 : w ≠ 0 := fun h => by rw [h, modK_zero'] at hw1; exact zero_ne_one hw1
      refine ⟨(Units.mk0 π hπ) ^ k * (ν : Fˣ) * Units.mk0 w hw0, ?_⟩
      apply Units.ext
      show ((((Units.mk0 π hπ) ^ k * (ν : Fˣ) * Units.mk0 w hw0) ^ n : Fˣ) : F) = x
      have e1 : (π ^ k) ^ n = π ^ (d x).1 := by
        rw [← zpow_natCast, ← zpow_mul, hk]
      have e2 : (((ν : Fˣ)) : F) ^ n = (((d x).2.1 : Fˣ) : F) := by
        have hν' : ν ^ n = (d x).2.1 := hν
        rw [← hν']; simp
      rw [(hd x).2]
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_zpow_eq_zpow_val,
        Units.val_mk0]
      rw [mul_pow, mul_pow, e1, e2, hwu]
  rw [hH, Subgroup.index_comap_of_surjective _ hsurj, Subgroup.index_prod]
  have : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; have := one_lt_pq_nat hF; omega)
  have := weil_I_4_thm7_cyclic hF M hM
  rw [AddSubgroup.index_toSubgroup, Int.index_zmultiples, IsCyclic.index_powMonoidHom_range, hM,
    Nat.gcd_comm]
  simp

end NumberFieldKB.WeilBNT.FieldModule
