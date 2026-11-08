import NumberFieldKB.WeilBNT.PFieldUnramified

/-!
# Weil, *Basic Number Theory*, I.§4, Thm. 7 (normalizing prime element) and Prop. 5: division algebras over
# $p$-fields

$D$ is a $p$-field (`hD : IsPField D p`), commutative or not, with maximal compact subring $R$ (`pR hD`), maximal
ideal $P$ (`pP hD`) and module $q$ (`pq hD`); $M^\times$ is a subgroup of $D^\times$ of order $q-1$ (Thm. 7).
$K_0$ is the center of $D$ (`Subring.center D`, a field, with the subspace topology).

* `weil_I_4_thm7_normalizer`: Thm. 7, last assertion (p. 16). There is a prime element $\pi$ of $D$ ($P=\pi R$) with
  $\pi M^\times=M^\times\pi$.
* `isClosed_center`: the center is closed; with the subspace topology it is a locally compact topological field.
* `weil_I_4_prop5_center`: Prop. 5, first assertion. $K_0$ is a $p$-field and $D$ has finite dimension over it.
* `weil_I_4_prop5`: Prop. 5 (p. 20–21). Let $d$ be the modular degree of $D$ over $K_0$ ($q=q_0^d$). Then
  $[D:K_0]=d^2$; $K_1=K_0(M^\times)$ (`pK1 M`) is a maximal commutative subfield of $D$, of dimension $d$ over $K_0$,
  unramified over $K_0$ (its residue field is that of $D$: every element of $R$ is congruent modulo $P$ to an element
  of $K_1$); and there is a prime element $\pi$ of $D$ with (a) $\pi^d$ a prime element of $K_0$
  ($P\cap K_0=\pi^d(R\cap K_0)$); (b) $1,\pi,\dots,\pi^{d-1}$ is a basis of $D$ as a left vector space over $K_1$ and
  generates $R$ as a left $R_1$-module ($R_1=R\cap K_1$); (c) $x\mapsto\pi^{-1}x\pi$ maps $K_1$ onto itself, its fixed
  field in $K_1$ is $K_0$, and it has order exactly $d$ on $K_1$, so it generates the Galois group of $K_1$ over $K_0$.
  The order of ramification $d$ of $D$ over $K_0$ is (a).

Weil states (a)–(c) for every maximal unramified commutative subfield $K_1$ of degree $d$; here $K_1=K_0(M^\times)$
for an arbitrary $M^\times$ (by Cor. 3 of Thm. 7 every such $K_1$ is of this form).
-/

open Topology Filter
open scoped NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

variable {D : Type*} [DivisionRing D] [TopologicalSpace D] [IsTopologicalDivisionRing D]
  [LocallyCompactSpace D] [T2Space D] [(𝓝[≠] (0 : D)).NeBot] {p : ℕ}

/-- Every ring automorphism of a finite field of characteristic `p` is a power of the Frobenius. -/
theorem ringAut_eq_frob {k : Type*} [Field k] [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (τ : RingAut k) : ∃ r : ℕ, ∀ x, τ x = x ^ (p ^ r) := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let τ' : k ≃ₐ[ZMod p] k := AlgEquiv.ofRingEquiv (f := τ) (fun c => by
    have := RingHom.ext_zmod (τ.toRingHom.comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) k)
    exact congrArg (fun f => f c) this)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).2 τ'
  refine ⟨n.1, fun x => ?_⟩
  have h1 : τ' x = x ^ (p ^ n.1) := by
    rw [← hn]
    simp only [AlgEquiv.coe_pow]
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]
  exact h1

/-- Conjugation by a nonzero element, as a ring automorphism. -/
def conjEquiv {a : D} (ha : a ≠ 0) : D ≃+* D where
  toFun x := a * x * a⁻¹
  invFun x := a⁻¹ * x * a
  left_inv x := by simp [mul_assoc, ha]
  right_inv x := by simp [mul_assoc, ha]
  map_mul' x y := by simp [mul_assoc, ha]
  map_add' x y := by simp [mul_add, add_mul]

theorem conjEquiv_apply {a : D} (ha : a ≠ 0) (x : D) : conjEquiv ha x = a * x * a⁻¹ := rfl

theorem continuous_conjEquiv {a : D} (ha : a ≠ 0) : Continuous (conjEquiv ha) := by
  show Continuous (fun x : D => a * x * a⁻¹)
  fun_prop

theorem continuous_conjEquiv_symm {a : D} (ha : a ≠ 0) : Continuous (conjEquiv ha).symm := by
  show Continuous (fun x : D => a⁻¹ * x * a)
  fun_prop

/-- Conjugation by a nonzero element acts on the residue field as a power of the Frobenius: for `x` in `R`,
`a x a⁻¹ ≡ x^(p^r)` modulo `P`. -/
theorem conj_residue_frob (hD : IsPField D p) {a : D} (ha : a ≠ 0) :
    ∃ r : ℕ, ∀ x : D, modK D x ≤ 1 → modK D (a * x * a⁻¹ - x ^ (p ^ r)) < 1 := by
  haveI : Fact p.Prime := ⟨hD.1⟩
  have hmod := weil_I_4_cor3_thm6 hD (conjEquiv ha) (continuous_conjEquiv ha) (continuous_conjEquiv_symm ha)
  let σR : pR hD →+* pR hD :=
    { toFun := fun x => ⟨a * (x : D) * a⁻¹, mem_pR.2 (by
        have := hmod (x : D)
        rw [conjEquiv_apply] at this
        rw [this]; exact mem_pR.1 x.2)⟩
      map_one' := Subtype.ext (by simp [ha])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc, ha])
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp [mul_add, add_mul]) }
  let τ0 : Qt hD →+* Qt hD :=
    Ideal.Quotient.lift (pIdealU hD) ((resMap hD).comp σR) (by
      intro b hb
      show resMap hD (σR b) = 0
      rw [resMap_eq_zero]
      have := hmod (b : D)
      rw [conjEquiv_apply] at this
      show modK D (a * (b : D) * a⁻¹) < 1
      rw [this]; exact hb)
  let τ : RingAut (Qt hD) :=
    RingEquiv.ofBijective τ0 (Finite.injective_iff_bijective.1 τ0.injective)
  haveI : CharP (Qt hD) p := (CharP.charP_iff_prime_eq_zero hD.1).2 (by
    have h : resMap hD ((p : pR hD)) = 0 := by
      rw [resMap_eq_zero]; simpa using hD.2
    simpa [map_natCast] using h)
  obtain ⟨r, hr⟩ := ringAut_eq_frob τ
  refine ⟨r, fun x hx => ?_⟩
  have h := hr (resMap hD ⟨x, hx⟩)
  have h0 : τ (resMap hD ⟨x, hx⟩) = resMap hD (σR ⟨x, hx⟩) := rfl
  have h2 : resMap hD (σR ⟨x, hx⟩ - (⟨x, hx⟩ : pR hD) ^ (p ^ r)) = 0 := by
    rw [map_sub, map_pow, ← h, h0, sub_self]
  rw [resMap_eq_zero] at h2
  exact h2

/-- If `x - y` has smaller module than `y`, then `x` and `y` have the same module. -/
theorem modK_eq_of_sub_lt (hD : IsPField D p) {x y : D} (h : modK D (x - y) < modK D y) :
    modK D x = modK D y := by
  have h1 : modK D x ≤ modK D y := by
    have := modK_sub_le_max hD y (y - x)
    rw [sub_sub_cancel] at this
    have h' : modK D (y - x) < modK D y := by rw [← modK_neg, neg_sub]; exact h
    exact this.trans (max_le le_rfl h'.le)
  rcases h1.lt_or_eq with hlt | heq
  · exfalso
    have := modK_sub_le_max hD x (x - y)
    rw [sub_sub_cancel] at this
    exact absurd (this.trans_lt (max_lt hlt h)) (lt_irrefl _)
  · exact heq

/-- **Weil, I.§4, Thm. 7, last assertion**: there is a prime element $\pi$ of $D$ with $\pi M^\times=M^\times\pi$. -/
@[kb "weil1973bnt" "Ch. I, §4, Thm. 7 (a prime element normalizing M)"]
theorem weil_I_4_thm7_normalizer (hD : IsPField D p) (M : Subgroup Dˣ) (hM : Nat.card M = pq hD - 1) :
    ∃ π : D, π ≠ 0 ∧ pP hD = (fun r => π * r) '' (pR hD : Set D) ∧
      (∀ μ ∈ M, ∃ ν ∈ M, π * ((μ : Dˣ) : D) = ((ν : Dˣ) : D) * π) ∧
      ∀ ν ∈ M, ∃ μ ∈ M, π * ((μ : Dˣ) : D) = ((ν : Dˣ) : D) * π := by
  classical
  haveI : Fact p.Prime := ⟨hD.1⟩
  obtain ⟨ϖ, hϖ0, hϖP, -⟩ := weil_I_4_thm6_prime hD
  have hq1 := one_lt_pq_nat hD
  have hϖmod : modK D ϖ = qi hD := weil_I_4_thm6_modK_prime hD hϖ0 hϖP
  have hϖpos : 0 < modK D ϖ := modK_pos_iff.2 hϖ0
  obtain ⟨r, hr⟩ := conj_residue_frob hD hϖ0
  set e := p ^ r with he
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; omega)
  haveI : Fintype M := Fintype.ofFinite M
  haveI := weil_I_4_thm7_cyclic hD M hM
  have hcomm : ∀ a b : M, a * b = b * a := fun a b => by
    letI := IsCyclic.commGroup (α := M)
    exact mul_comm a b
  have hcommD : ∀ a b : M, ((a : Dˣ) : D) * ((b : Dˣ) : D) = ((b : Dˣ) : D) * ((a : Dˣ) : D) := fun a b => by
    have := congrArg (fun m : M => ((m : Dˣ) : D)) (hcomm a b)
    simpa using this
  have hmodM : ∀ μ : M, modK D ((μ : Dˣ) : D) = 1 := fun μ => (subgroup_elem hD M hM μ).2
  have hne : ∀ μ : M, ((μ : Dˣ) : D) ≠ 0 := fun μ => Units.ne_zero _
  -- the terms of the sum
  let t : M → D := fun μ => ((μ : Dˣ) : D) ^ e * ϖ * ((μ : Dˣ) : D)⁻¹
  have hterm : ∀ μ : M, modK D (t μ - ϖ) ≤ qi hD * modK D ϖ := by
    intro μ
    set u : D := ((μ : Dˣ) : D) with hu
    have hu0 : u ≠ 0 := hne μ
    have hue0 : u ^ e ≠ 0 := pow_ne_zero _ hu0
    have h1 : t μ - ϖ = (u ^ e * (ϖ * u⁻¹ * ϖ⁻¹ - (u ^ e)⁻¹)) * ϖ := by
      simp only [t, mul_sub, sub_mul, mul_assoc, inv_mul_cancel₀ hϖ0, mul_one, mul_inv_cancel₀ hue0,
        one_mul]
      rfl
    have h2 : modK D (ϖ * u⁻¹ * ϖ⁻¹ - (u ^ e)⁻¹) < 1 := by
      have := hr u⁻¹ (by rw [modK_inv hu0, hmodM μ]; simp)
      rwa [inv_pow] at this
    have h3 : modK D (u ^ e * (ϖ * u⁻¹ * ϖ⁻¹ - (u ^ e)⁻¹)) < 1 := by
      rw [modK_mul, modK_pow, hmodM μ, one_pow, one_mul]; exact h2
    rw [h1, modK_mul]
    exact mul_le_mul' (modK_le_qi_of_lt_one hD h3) le_rfl
  let S : D := ∑ μ : M, t μ
  have hcard : (Finset.univ : Finset M).card = pq hD - 1 := by
    rw [Finset.card_univ, Fintype.card_eq_nat_card, hM]
  set n : ℕ := pq hD - 1 with hn
  have hqn : (pq hD : D) = (n : D) + 1 := by
    rw [← Nat.cast_succ]; congr 1; omega
  have hS : modK D (S - (n : D) * ϖ) ≤ qi hD * modK D ϖ := by
    have : S - (n : D) * ϖ = ∑ μ : M, (t μ - ϖ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
    rw [this]
    exact modK_sum_le hD _ _ (fun μ _ => hterm μ)
  have hqmod : modK D (pq hD : D) ≤ qi hD := by
    obtain ⟨f, hf, hqf⟩ := weil_I_4_thm6_residue hD
    apply modK_le_qi_of_lt_one hD
    rw [hqf, Nat.cast_pow, modK_pow]
    exact pow_lt_one₀ zero_le hD.2 (by omega)
  let π' : D := -S
  have hπ'ϖ : π' - ϖ = -(S - (n : D) * ϖ) - (pq hD : D) * ϖ := by
    rw [hqn]; simp only [π']; noncomm_ring
  have hqiϖ : qi hD * modK D ϖ < modK D ϖ := mul_lt_of_lt_one_left hϖpos (qi_lt_one hD)
  have hclose : modK D (π' - ϖ) < modK D ϖ := by
    rw [hπ'ϖ]
    refine lt_of_le_of_lt ((modK_sub_le_max hD _ _).trans (max_le ?_ ?_)) hqiϖ
    · rw [modK_neg]; exact hS
    · rw [modK_mul]; exact mul_le_mul' hqmod le_rfl
  have hπ'mod : modK D π' = modK D ϖ := modK_eq_of_sub_lt hD hclose
  have hπ'0 : π' ≠ 0 := modK_pos_iff.1 (by rw [hπ'mod]; exact hϖpos)
  have hπ'mod' : modK D π' = qi hD := by rw [hπ'mod, hϖmod]
  have hπ'P : pP hD = (fun r => π' * r) '' (pR hD : Set D) := by
    refine pP_eq_left (hK := hD) hπ'0 (by rw [hπ'mod']; exact qi_lt_one hD) (fun x hx => ?_)
    rw [hπ'mod']; exact modK_le_qi_of_lt_one hD hx
  -- conjugation by M
  have key : ∀ ν μ : M, ((ν : Dˣ) : D) ^ e * t μ * ((ν : Dˣ) : D)⁻¹ = t (ν * μ) := by
    intro ν μ
    have hc := hcommD ν μ
    simp only [t, Subgroup.coe_mul, Units.val_mul, mul_inv_rev]
    rw [(Commute.mul_pow hc e)]
    simp only [mul_assoc]
  have hconj : ∀ ν : M, ((ν : Dˣ) : D) ^ e * π' * ((ν : Dˣ) : D)⁻¹ = π' := by
    intro ν
    have : ((ν : Dˣ) : D) ^ e * S * ((ν : Dˣ) : D)⁻¹ = S := by
      rw [Finset.mul_sum, Finset.sum_mul]
      calc _ = ∑ μ : M, t (ν * μ) := Finset.sum_congr rfl (fun μ _ => key ν μ)
        _ = S := Equiv.sum_comp (Equiv.mulLeft ν) t
    simp only [π', mul_neg, neg_mul, this]
  have hπ'ν : ∀ ν : M, π' * ((ν : Dˣ) : D) = ((ν : Dˣ) : D) ^ e * π' := by
    intro ν
    have := congrArg (fun y => y * ((ν : Dˣ) : D)) (hconj ν)
    simp only [inv_mul_cancel_right₀ (hne ν)] at this
    exact this.symm
  refine ⟨π', hπ'0, hπ'P, ?_, ?_⟩
  · intro μ hμ
    refine ⟨((⟨μ, hμ⟩ : M) ^ e : M), (⟨μ, hμ⟩ ^ e : M).2, ?_⟩
    have := hπ'ν ⟨μ, hμ⟩
    simpa using this
  · intro ν hν
    have hcop : (Nat.card M).Coprime e := by
      rw [hM]; exact (coprime_pq_sub_one hD).pow_right r
    let g : M ≃ M := powCoprime hcop
    refine ⟨((g.symm ⟨ν, hν⟩ : M) : Dˣ), (g.symm ⟨ν, hν⟩).2, ?_⟩
    have h1 := hπ'ν (g.symm ⟨ν, hν⟩)
    have h2 : g (g.symm ⟨ν, hν⟩) = ⟨ν, hν⟩ := g.apply_symm_apply _
    have h3 : (g.symm ⟨ν, hν⟩) ^ e = ⟨ν, hν⟩ := h2
    rw [h1]
    have := congrArg (fun m : M => ((m : Dˣ) : D)) h3
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val] at this
    rw [this]

/-- The center of a Hausdorff topological ring is closed. -/
theorem isClosed_center : IsClosed (Subring.center D : Set D) := by
  have : (Subring.center D : Set D) = ⋂ x : D, {y | x * y = y * x} := by
    ext y
    simp [Subring.mem_center_iff, eq_comm]
  rw [this]
  exact isClosed_iInter fun x =>
    isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

/-- The center, with the subspace topology, is a topological division ring. -/
instance center_isTopologicalDivisionRing : IsTopologicalDivisionRing (Subring.center D) where
  continuousAt_inv₀ x hx := by
    rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
    have hx' : (x : D) ≠ 0 := fun h => hx (Subtype.ext h)
    exact (continuousAt_inv₀ hx').comp (continuous_subtype_val.continuousAt (x := x))

instance center_locallyCompactSpace : LocallyCompactSpace (Subring.center D) :=
  (isClosed_center (D := D)).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- The center of a $p$-field is not discrete (Weil: it contains $\pi^{\nu n}$ for all $n$). -/
theorem center_neBot (hD : IsPField D p) : (𝓝[≠] (0 : Subring.center D)).NeBot := by
  classical
  obtain ⟨M, hM⟩ := weil_I_4_thm7_exists hD
  obtain ⟨π, hπ0, hπP, hπM, -⟩ := weil_I_4_thm7_normalizer hD M hM
  have hq1 := one_lt_pq_nat hD
  have hπmod : modK D π = qi hD := weil_I_4_thm6_modK_prime hD hπ0 hπP
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; omega)
  -- conjugation by `π` permutes `M`
  have hπM' : ∀ μ : M, ∃ ν : M, π * ((μ : Dˣ) : D) = ((ν : Dˣ) : D) * π := fun μ => by
    obtain ⟨ν, hν, h⟩ := hπM μ μ.2
    exact ⟨⟨ν, hν⟩, h⟩
  choose c hc using hπM'
  have hcinj : Function.Injective c := by
    intro a b hab
    have h1 := hc a
    rw [hab, ← hc b] at h1
    have h2 := mul_left_cancel₀ hπ0 h1
    exact Subtype.ext (Units.ext h2)
  have hcbij : Function.Bijective c := Finite.injective_iff_bijective.1 hcinj
  let σ : Equiv.Perm M := Equiv.ofBijective c hcbij
  have hpow : ∀ (n : ℕ) (μ : M), π ^ n * ((μ : Dˣ) : D) = (((σ ^ n) μ : M) : Dˣ) * π ^ n := by
    intro n
    induction n with
    | zero => intro μ; simp
    | succ n ih =>
      intro μ
      rw [pow_succ', mul_assoc, ih, ← mul_assoc, ← mul_assoc]
      have := hc ((σ ^ n) μ)
      have h2 : (σ ^ (n + 1)) μ = c ((σ ^ n) μ) := by rw [pow_succ', Equiv.Perm.mul_apply]; rfl
      rw [h2, ← this, mul_assoc]
  set k := orderOf σ with hk
  have hk0 : 0 < k := orderOf_pos σ
  have hzM : ∀ μ ∈ M, π ^ k * ((μ : Dˣ) : D) = ((μ : Dˣ) : D) * π ^ k := by
    intro μ hμ
    rw [hpow k ⟨μ, hμ⟩, hk, pow_orderOf_eq_one]
    rfl
  set z : D := π ^ k with hz
  have hz0 : z ≠ 0 := pow_ne_zero _ hπ0
  have hzπ : ∀ i : ℕ, z * π ^ i = π ^ i * z := fun i => (Commute.pow_pow_self π k i).eq
  -- `z` commutes with every element of `R`
  have hR : ∀ x : D, modK D x ≤ 1 → z * x = x * z := by
    intro x hx
    obtain ⟨hAR, hrep⟩ := weil_I_4_thm7_repr hD M hM
    have hq : (1 : ℝ≥0) < (pq hD : ℝ≥0) := by exact_mod_cast hq1
    have hqi : ((pq hD : ℝ≥0) ^ 1)⁻¹ = qi hD := by simp [qi]
    obtain ⟨a, ⟨ha, hsum⟩, -⟩ := weil_I_4_cor2_thm6 hD hπ0 (n := 1) le_rfl (by rw [hqi]; exact hπmod)
      (A := {m | m = 0 ∨ ∃ μ ∈ M, m = ((μ : Dˣ) : D)})
      (fun m hm => by
        rcases hm with rfl | ⟨μ, hμ, rfl⟩
        · exact (pR hD).zero_mem
        · exact hAR μ hμ)
      (fun y hy => by
        obtain ⟨m, ⟨hm1, hm2⟩, huniq⟩ := hrep y hy
        have hiff : ∀ w : D, w ∈ pP hD ↔ modK D w ≤ ((pq hD : ℝ≥0) ^ 1)⁻¹ := fun w => by
          rw [hqi]
          exact ⟨fun h => modK_le_qi_of_lt_one hD h, fun h => lt_of_le_of_lt h (qi_lt_one hD)⟩
        exact ⟨m, ⟨hm1, (hiff _).1 hm2⟩, fun a' ⟨ha1, ha2⟩ => huniq a' ⟨ha1, (hiff _).2 ha2⟩⟩)
      0 (by simpa using hx)
    have h1 := hsum.mul_left z
    have h2 := hsum.mul_right z
    have hfun : (fun i : ℕ => z * (a i * π ^ ((i : ℤ) + 0))) = fun i : ℕ => a i * π ^ ((i : ℤ) + 0) * z := by
      funext i
      have hai : z * a i = a i * z := by
        rcases ha i with h | ⟨μ, hμ, h⟩
        · rw [h]; simp
        · rw [h]; exact hzM μ hμ
      have : π ^ ((i : ℤ) + 0) = π ^ i := by simp
      rw [this, ← mul_assoc, hai, mul_assoc, hzπ i, mul_assoc]
    rw [hfun] at h1
    exact h1.unique h2
  -- `z` commutes with everything
  have hall : ∀ x : D, z * x = x * z := by
    intro x
    by_cases hx0 : x = 0
    · simp [hx0]
    have htπ : Filter.Tendsto (fun n : ℕ => π ^ n) Filter.atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_iff_modK π).2 (by rw [hπmod]; exact qi_lt_one hD)
    have ht : Filter.Tendsto (fun n : ℕ => π ^ n * x) Filter.atTop (𝓝 0) := by
      simpa using htπ.mul_const x
    have hm : Filter.Tendsto (fun n : ℕ => modK D (π ^ n * x)) Filter.atTop (𝓝 0) := by
      have := (continuous_modK (K := D)).tendsto 0 |>.comp ht
      rw [Function.comp_def, modK_zero] at this
      exact this
    obtain ⟨m, hm1⟩ := (hm.eventually_lt_const one_pos).exists
    have hy := hR _ hm1.le
    have hzm : Commute z ((π ^ m)⁻¹) := (Commute.pow_pow_self π k m).inv_right₀
    have hzy : Commute z (π ^ m * x) := hy
    have := hzm.mul_right hzy
    rwa [inv_mul_cancel_left₀ (pow_ne_zero _ hπ0)] at this
  have hzc : ∀ n : ℕ, z ^ (n + 1) ∈ Subring.center D := fun n => by
    rw [Subring.mem_center_iff]
    intro g
    exact (Commute.pow_right (show Commute z g from hall g).symm (n + 1)).eq
  have hzmod : modK D z < 1 := by
    rw [hz, modK_pow, hπmod]; exact pow_lt_one₀ zero_le (qi_lt_one hD) hk0.ne'
  have htz : Filter.Tendsto (fun n : ℕ => z ^ n) Filter.atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_iff_modK z).2 hzmod
  let w : ℕ → Subring.center D := fun n => ⟨z ^ (n + 1), hzc n⟩
  have hw : Filter.Tendsto w Filter.atTop (𝓝 0) := by
    rw [tendsto_subtype_rng]
    exact htz.comp (Filter.tendsto_add_atTop_nat 1)
  have hw' : Filter.Tendsto w Filter.atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hw, Filter.Eventually.of_forall fun n => by
      intro h
      exact pow_ne_zero (n + 1) hz0 (congrArg Subtype.val h)⟩
  exact hw'.neBot

/-- **Weil, I.§4, Prop. 5, first assertion**: the center $K_0$ of a $p$-field $D$ is a $p$-field, and $D$ has finite
dimension over $K_0$. -/
@[kb "weil1973bnt" "Ch. I, §4, Prop. 5 (the center is a p-field, of finite codimension)"]
theorem weil_I_4_prop5_center (hD : IsPField D p) :
    IsPField (Subring.center D) p ∧ FiniteDimensional (Subring.center D) D := by
  haveI := center_neBot hD
  have hpf : IsPField (Subring.center D) p := by
    refine ⟨hD.1, ?_⟩
    rw [← tendsto_pow_atTop_nhds_zero_iff_modK]
    have h := (tendsto_pow_atTop_nhds_zero_iff_modK (K := D) (p : D)).2 hD.2
    rw [tendsto_subtype_rng]
    simpa using h
  haveI : ContinuousSMul (Subring.center D) D := ⟨by
    have : ∀ (c : Subring.center D) (x : D), c • x = (c : D) * x := fun _ _ => rfl
    simp_rw [this]
    exact (continuous_subtype_val.comp continuous_fst).mul continuous_snd⟩
  exact ⟨hpf, weil_I_2_thm3_cor2_finiteDimensional (K := Subring.center D) (V := D)⟩

instance center_continuousSMul : ContinuousSMul (Subring.center D) D := ⟨by
  have : ∀ (c : Subring.center D) (x : D), c • x = (c : D) * x := fun _ _ => rfl
  simp_rw [this]
  exact (continuous_subtype_val.comp continuous_fst).mul continuous_snd⟩

/-! ### The normalizing prime element and the permutation of `M` it induces -/

/-- A subgroup `M` of order `q - 1` together with a prime element `π` with `πM = Mπ` (Thm. 7). -/
structure NormData (hD : IsPField D p) (M : Subgroup Dˣ) where
  hM : Nat.card M = pq hD - 1
  π : D
  π_ne : π ≠ 0
  π_P : pP hD = (fun r => π * r) '' (pR hD : Set D)
  fwd : ∀ μ ∈ M, ∃ ν ∈ M, π * ((μ : Dˣ) : D) = ((ν : Dˣ) : D) * π
  bwd : ∀ ν ∈ M, ∃ μ ∈ M, π * ((μ : Dˣ) : D) = ((ν : Dˣ) : D) * π

namespace NormData

variable {hD : IsPField D p} {M : Subgroup Dˣ} (N : NormData hD M)

include N

theorem finite : Finite M := Nat.finite_of_card_ne_zero (by
  rw [N.hM]; have := one_lt_pq_nat hD; omega)

theorem exists_c (μ : M) : ∃ ν : M, N.π * ((μ : Dˣ) : D) = ((ν : Dˣ) : D) * N.π := by
  obtain ⟨ν, hν, h⟩ := N.fwd μ μ.2
  exact ⟨⟨ν, hν⟩, h⟩

/-- Conjugation by `π` as a map `M → M`: `π μ = c(μ) π`. -/
def c (μ : M) : M := Classical.choose (N.exists_c μ)

theorem pi_mul (μ : M) : N.π * ((μ : Dˣ) : D) = ((N.c μ : M) : Dˣ) * N.π :=
  Classical.choose_spec (N.exists_c μ)

theorem c_injective : Function.Injective N.c := by
  intro a b hab
  have h1 := N.pi_mul a
  rw [hab, ← N.pi_mul b] at h1
  exact Subtype.ext (Units.ext (mul_left_cancel₀ N.π_ne h1))

/-- The permutation of `M` induced by conjugation by `π`. -/
def σ : Equiv.Perm M :=
  haveI := N.finite
  Equiv.ofBijective N.c (Finite.injective_iff_bijective.1 N.c_injective)

theorem σ_apply (μ : M) : N.σ μ = N.c μ := rfl

/-- The order of conjugation by `π` on `M`. -/
def ν : ℕ := orderOf N.σ

theorem ν_pos : 0 < N.ν := by
  haveI := N.finite
  exact orderOf_pos N.σ

theorem mnez (μ : M) : ((μ : Dˣ) : D) ≠ 0 := Units.ne_zero _

theorem modK_M (μ : M) : modK D ((μ : Dˣ) : D) = 1 := (subgroup_elem hD M N.hM μ).2

theorem mcomm (a b : M) : ((a : Dˣ) : D) * ((b : Dˣ) : D) = ((b : Dˣ) : D) * ((a : Dˣ) : D) := by
  haveI := weil_I_4_thm7_cyclic hD M N.hM
  have h : a * b = b * a := by
    letI := IsCyclic.commGroup (α := M)
    exact mul_comm a b
  have := congrArg (fun m : M => ((m : Dˣ) : D)) h
  simpa using this

theorem M_eq_of_close {a b : M} (h : modK D (((a : Dˣ) : D) - ((b : Dˣ) : D)) < 1) : a = b :=
  redM_injective hD M N.hM ((redM_eq_iff hD M N.hM a b).2 h)

theorem pow_mul_nat (n : ℕ) (μ : M) :
    N.π ^ n * ((μ : Dˣ) : D) = (((N.σ ^ n) μ : M) : Dˣ) * N.π ^ n := by
  induction n generalizing μ with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, ← mul_assoc]
    have := N.pi_mul ((N.σ ^ n) μ)
    have h2 : (N.σ ^ (n + 1)) μ = N.c ((N.σ ^ n) μ) := by
      rw [pow_succ', Equiv.Perm.mul_apply]; rfl
    rw [h2, ← this, mul_assoc]

theorem pow_mul_int (k : ℤ) (μ : M) :
    N.π ^ k * ((μ : Dˣ) : D) = (((N.σ ^ k) μ : M) : Dˣ) * N.π ^ k := by
  rcases k with n | n
  · simpa using N.pow_mul_nat n μ
  · have h := N.pow_mul_nat (n + 1) ((N.σ ^ (n + 1))⁻¹ μ)
    have h2 : (N.σ ^ (n + 1)) ((N.σ ^ (n + 1))⁻¹ μ) = μ := by simp
    rw [h2] at h
    have hπ := N.π_ne
    have h3 : N.π ^ (Int.negSucc n) = (N.π ^ (n + 1))⁻¹ := by
      rw [zpow_negSucc]
    rw [h3, zpow_negSucc]
    have e : (N.σ ^ (n + 1))⁻¹ = (N.σ ^ (n + 1))⁻¹ := rfl
    calc (N.π ^ (n + 1))⁻¹ * ((μ : Dˣ) : D)
        = (N.π ^ (n + 1))⁻¹ * (((μ : Dˣ) : D) * N.π ^ (n + 1)) * (N.π ^ (n + 1))⁻¹ := by
          rw [mul_assoc, mul_inv_cancel_right₀ (pow_ne_zero _ hπ)]
      _ = _ := by
          rw [← h]
          simp [mul_assoc, hπ]

theorem central_of_comm {z : D} (hzπ : z * N.π = N.π * z)
    (hzM : ∀ μ : M, z * ((μ : Dˣ) : D) = ((μ : Dˣ) : D) * z) : z ∈ Subring.center D := by
  classical
  have hq1 := one_lt_pq_nat hD
  have hπ0 := N.π_ne
  have hπmod : modK D N.π = qi hD := weil_I_4_thm6_modK_prime hD hπ0 N.π_P
  have hzπ' : ∀ i : ℕ, z * N.π ^ i = N.π ^ i * z :=
    fun i => (Commute.pow_right (show Commute z N.π from hzπ) i).eq
  have hR : ∀ x : D, modK D x ≤ 1 → z * x = x * z := by
    intro x hx
    obtain ⟨hAR, hrep⟩ := weil_I_4_thm7_repr hD M N.hM
    have hqi : ((pq hD : ℝ≥0) ^ 1)⁻¹ = qi hD := by simp [qi]
    obtain ⟨a, ⟨ha, hsum⟩, -⟩ := weil_I_4_cor2_thm6 hD hπ0 (n := 1) le_rfl (by rw [hqi]; exact hπmod)
      (A := {m | m = 0 ∨ ∃ μ ∈ M, m = ((μ : Dˣ) : D)})
      (fun m hm => by
        rcases hm with rfl | ⟨μ, hμ, rfl⟩
        · exact (pR hD).zero_mem
        · exact hAR μ hμ)
      (fun y hy => by
        obtain ⟨m, ⟨hm1, hm2⟩, huniq⟩ := hrep y hy
        have hiff : ∀ w : D, w ∈ pP hD ↔ modK D w ≤ ((pq hD : ℝ≥0) ^ 1)⁻¹ := fun w => by
          rw [hqi]
          exact ⟨fun h => modK_le_qi_of_lt_one hD h, fun h => lt_of_le_of_lt h (qi_lt_one hD)⟩
        exact ⟨m, ⟨hm1, (hiff _).1 hm2⟩, fun a' ⟨ha1, ha2⟩ => huniq a' ⟨ha1, (hiff _).2 ha2⟩⟩)
      0 (by simpa using hx)
    have h1 := hsum.mul_left z
    have h2 := hsum.mul_right z
    have hfun : (fun i : ℕ => z * (a i * N.π ^ ((i : ℤ) + 0))) =
        fun i : ℕ => a i * N.π ^ ((i : ℤ) + 0) * z := by
      funext i
      have hai : z * a i = a i * z := by
        rcases ha i with h | ⟨μ, hμ, h⟩
        · rw [h]; simp
        · rw [h]; exact hzM ⟨μ, hμ⟩
      have : N.π ^ ((i : ℤ) + 0) = N.π ^ i := by simp
      rw [this, ← mul_assoc, hai, mul_assoc, hzπ' i, mul_assoc]
    rw [hfun] at h1
    exact h1.unique h2
  have hall : ∀ x : D, z * x = x * z := by
    intro x
    by_cases hx0 : x = 0
    · simp [hx0]
    have htπ : Filter.Tendsto (fun n : ℕ => N.π ^ n) Filter.atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_iff_modK N.π).2 (by rw [hπmod]; exact qi_lt_one hD)
    have ht : Filter.Tendsto (fun n : ℕ => N.π ^ n * x) Filter.atTop (𝓝 0) := by
      simpa using htπ.mul_const x
    have hm : Filter.Tendsto (fun n : ℕ => modK D (N.π ^ n * x)) Filter.atTop (𝓝 0) := by
      have := (continuous_modK (K := D)).tendsto 0 |>.comp ht
      rw [Function.comp_def, modK_zero] at this
      exact this
    obtain ⟨m, hm1⟩ := (hm.eventually_lt_const one_pos).exists
    have hy := hR _ hm1.le
    have hzm : Commute z ((N.π ^ m)⁻¹) := (Commute.pow_right (show Commute z N.π from hzπ) m).inv_right₀
    have hzy : Commute z (N.π ^ m * x) := hy
    have := hzm.mul_right hzy
    rwa [inv_mul_cancel_left₀ (pow_ne_zero _ hπ0)] at this
  rw [Subring.mem_center_iff]
  intro g
  exact (hall g).symm

/-- An element commuting with `M` has module an integer power of `q^ν` (it is `π^n` times a unit commuting with
`M`, which forces `ν ∣ n`). -/
theorem val_of_comm {x : D} (hx0 : x ≠ 0) (hx : ∀ μ : M, x * ((μ : Dˣ) : D) = ((μ : Dˣ) : D) * x) :
    ∃ m : ℤ, modK D x = (pq hD : ℝ≥0) ^ ((N.ν : ℤ) * m) := by
  have hπ0 := N.π_ne
  have hq1 := one_lt_pq_nat hD
  have hq0 : (pq hD : ℝ≥0) ≠ 0 := by positivity
  have hπmod : modK D N.π = qi hD := weil_I_4_thm6_modK_prime hD hπ0 N.π_P
  obtain ⟨n, hn⟩ := weil_I_4_thm6_range hD hx0
  set u : D := x * N.π ^ n with hu
  have hu1 : modK D u = 1 := by
    rw [hu, modK_mul, modK_zpow hπ0, hπmod, hn]
    simp only [qi, inv_zpow']
    rw [← zpow_add₀ hq0]; simp
  obtain ⟨hAR, hrep⟩ := weil_I_4_thm7_repr hD M N.hM
  obtain ⟨m₀, ⟨hm0, hmP⟩, -⟩ := hrep u hu1.le
  rcases hm0 with rfl | ⟨m, hmM, rfl⟩
  · exfalso
    have : modK D (u - 0) < 1 := hmP
    rw [sub_zero, hu1] at this
    exact lt_irrefl _ this
  set m' : M := ⟨m, hmM⟩ with hm'
  have hmP' : modK D (u - ((m' : Dˣ) : D)) < 1 := hmP
  have hσ : ∀ μ : M, (N.σ ^ (-n)) μ = μ := by
    intro μ
    set μ' := (N.σ ^ (-n)) μ with hμ'
    have key : u * ((μ' : Dˣ) : D) = ((μ : Dˣ) : D) * u := by
      have h1 := N.pow_mul_int n μ'
      have h2 : (N.σ ^ n) μ' = μ := by
        rw [hμ', ← Equiv.Perm.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero]; rfl
      rw [h2] at h1
      rw [hu, mul_assoc, h1, ← mul_assoc, hx μ, mul_assoc]
    have hclose : modK D (((m' * μ' : M) : Dˣ) - ((μ * m' : M) : Dˣ) : D) < 1 := by
      have e : (((m' * μ' : M) : Dˣ) : D) - (((μ * m' : M) : Dˣ) : D) =
          ((m' : Dˣ) - u : D) * ((μ' : Dˣ) : D) + ((μ : Dˣ) : D) * (u - ((m' : Dˣ) : D)) := by
        simp only [Subgroup.coe_mul, Units.val_mul]
        rw [sub_mul, mul_sub, key]; abel
      rw [e]
      refine lt_of_le_of_lt (isUltrametricMod_of_isPField hD _ _) (max_lt ?_ ?_)
      · rw [modK_mul, N.modK_M, mul_one, ← modK_neg, neg_sub]; exact hmP'
      · rw [modK_mul, N.modK_M, one_mul]; exact hmP'
    have heq := N.M_eq_of_close hclose
    have : m' * μ' = m' * μ := by rw [heq]; exact Subtype.ext (Units.ext (N.mcomm μ m'))
    exact mul_left_cancel this
  have h1 : N.σ ^ (-n) = 1 := Equiv.ext hσ
  have h2 : N.σ ^ n = 1 := by
    have := congrArg (fun s => s⁻¹) h1
    simpa [zpow_neg] using this
  have hdvd : (N.ν : ℤ) ∣ n := (orderOf_dvd_iff_zpow_eq_one).2 h2
  obtain ⟨m, hm⟩ := hdvd
  exact ⟨m, by rw [hn, hm]⟩

end NormData

/-- $K_1=K_0(M^\times)$: the subfield of $D$ generated by the center and $M^\times$. -/
def pK1 (M : Subgroup Dˣ) : Subfield D :=
  Subfield.closure (Set.range (algebraMap (Subring.center D) D) ∪ (fun μ : Dˣ => (μ : D)) '' (M : Set Dˣ))

theorem comm_of_closure {S T : Set D} (h : ∀ s ∈ S, ∀ t ∈ T, Commute s t) {x : D}
    (hx : x ∈ Subfield.closure S) : ∀ t ∈ T, Commute x t := by
  induction hx using Subfield.closure_induction with
  | mem x hx => exact fun t ht => h x hx t ht
  | one => exact fun t _ => Commute.one_left t
  | add x y _ _ hx hy => exact fun t ht => (hx t ht).add_left (hy t ht)
  | neg x _ hx => exact fun t ht => (hx t ht).neg_left
  | inv x _ hx => exact fun t ht => (hx t ht).inv_left₀
  | mul x y _ _ hx hy => exact fun t ht => (hx t ht).mul_left (hy t ht)

theorem mem_pK1_center (M : Subgroup Dˣ) {x : D} (hx : x ∈ Subring.center D) : x ∈ pK1 M :=
  Subfield.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)

theorem mem_pK1_M (M : Subgroup Dˣ) {μ : Dˣ} (hμ : μ ∈ M) : (μ : D) ∈ pK1 M :=
  Subfield.subset_closure (Or.inr ⟨μ, hμ, rfl⟩)

/-- `K₁` as a submodule over the center. -/
def K1sub (M : Subgroup Dˣ) : Submodule (Subring.center D) D where
  carrier := pK1 M
  add_mem' := fun ha hb => (pK1 M).add_mem ha hb
  zero_mem' := (pK1 M).zero_mem
  smul_mem' := fun c x hx => (pK1 M).mul_mem (mem_pK1_center M c.2) hx

theorem isClosed_pK1 (hD : IsPField D p) (M : Subgroup Dˣ) : IsClosed (pK1 M : Set D) := by
  haveI := center_neBot hD
  haveI := (weil_I_4_prop5_center hD).2
  exact isClosed_of_finiteDimensional (K := Subring.center D) (V := D) (K1sub M)

/-- `K₁` is an algebra over the center. -/
instance pK1_algebra (M : Subgroup Dˣ) : Algebra (Subring.center D) (pK1 M) :=
  subfieldAlgebra (pK1 M) (fun x => mem_pK1_center M x.2)

theorem pK1_smul_coe (M : Subgroup Dˣ) (a : Subring.center D) (y : pK1 M) :
    ((a • y : pK1 M) : D) = (a : D) * (y : D) := rfl

/-- The inclusion `K₁ → D` as a linear map over the center. -/
def pK1_incl (M : Subgroup Dˣ) : pK1 M →ₗ[Subring.center D] D where
  toFun y := y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pK1_incl_injective (M : Subgroup Dˣ) : Function.Injective (pK1_incl (D := D) M) :=
  Subtype.val_injective

namespace NormData

variable {hD : IsPField D p} {M : Subgroup Dˣ} (N : NormData hD M)

include N

theorem comm_gen : ∀ s ∈ (Set.range (algebraMap (Subring.center D) D) ∪
      (fun μ : Dˣ => (μ : D)) '' (M : Set Dˣ)), ∀ t ∈ (Set.range (algebraMap (Subring.center D) D) ∪
      (fun μ : Dˣ => (μ : D)) '' (M : Set Dˣ)), Commute s t := by
  rintro s (⟨a, rfl⟩ | ⟨μ, hμ, rfl⟩) t (⟨b, rfl⟩ | ⟨ν, hν, rfl⟩)
  · exact (Subring.mem_center_iff.1 a.2 _).symm
  · exact (Subring.mem_center_iff.1 a.2 _).symm
  · exact (Subring.mem_center_iff.1 b.2 _)
  · exact N.mcomm ⟨μ, hμ⟩ ⟨ν, hν⟩

theorem pK1_comm_gen {x : D} (hx : x ∈ pK1 M) : ∀ t ∈ (Set.range (algebraMap (Subring.center D) D) ∪
      (fun μ : Dˣ => (μ : D)) '' (M : Set Dˣ)), Commute x t :=
  comm_of_closure N.comm_gen hx

theorem pK1_comm {x y : D} (hx : x ∈ pK1 M) (hy : y ∈ pK1 M) : x * y = y * x := by
  have := comm_of_closure (S := Set.range (algebraMap (Subring.center D) D) ∪
      (fun μ : Dˣ => (μ : D)) '' (M : Set Dˣ)) (T := {x})
    (fun s hs t ht => by rw [Set.mem_singleton_iff.1 ht]; exact (N.pK1_comm_gen hx s hs).symm) hy x rfl
  exact this.eq.symm

theorem pK1_comm_M {x : D} (hx : x ∈ pK1 M) (μ : M) : x * ((μ : Dˣ) : D) = ((μ : Dˣ) : D) * x :=
  (N.pK1_comm_gen hx _ (Or.inr ⟨μ, μ.2, rfl⟩)).eq

theorem pi_pow_comm (μ : M) : N.π ^ N.ν * ((μ : Dˣ) : D) = ((μ : Dˣ) : D) * N.π ^ N.ν := by
  have := N.pow_mul_nat N.ν μ
  rw [this]
  have h1 : N.σ ^ N.ν = 1 := pow_orderOf_eq_one N.σ
  rw [h1]; rfl

theorem pi_pow_central : N.π ^ N.ν ∈ Subring.center D :=
  N.central_of_comm ((Commute.pow_left (Commute.refl N.π) N.ν).eq) (fun μ => N.pi_pow_comm μ)

theorem modK_pi : modK D N.π = qi hD := weil_I_4_thm6_modK_prime hD N.π_ne N.π_P

theorem modK_pi_pow (n : ℕ) : modK D (N.π ^ n) = qi hD ^ n := by rw [modK_pow, N.modK_pi]

theorem le_of_comm_lt_one {t : D} (ht : ∀ μ : M, t * ((μ : Dˣ) : D) = ((μ : Dˣ) : D) * t)
    (hlt : modK D t < 1) : modK D t ≤ qi hD ^ N.ν := by
  by_cases h0 : t = 0
  · simp [h0]
  obtain ⟨j, hj⟩ := N.val_of_comm h0 ht
  have hq1 := one_lt_pq_nat hD
  have hq : (1 : ℝ≥0) < (pq hD : ℝ≥0) := by exact_mod_cast hq1
  have hν := N.ν_pos
  have hneg : (N.ν : ℤ) * j < 0 := by
    by_contra hc
    push Not at hc
    rw [hj] at hlt
    exact absurd hlt (not_lt.2 (one_le_zpow₀ hq.le hc))
  have hj1 : j ≤ -1 := by
    by_contra hc
    push Not at hc
    have : 0 ≤ (N.ν : ℤ) * j := mul_nonneg (by positivity) (by omega)
    omega
  have : (N.ν : ℤ) * j ≤ -(N.ν : ℤ) := by nlinarith
  rw [hj]
  calc (pq hD : ℝ≥0) ^ ((N.ν : ℤ) * j) ≤ (pq hD : ℝ≥0) ^ (-(N.ν : ℤ)) :=
        zpow_le_zpow_right₀ hq.le this
    _ = qi hD ^ N.ν := by rw [zpow_neg, zpow_natCast, qi, inv_pow]

theorem exists_digit {u : D} (hu : modK D u ≤ 1) :
    ∃ m₀ : D, m₀ ∈ pK1 M ∧ (∀ μ : M, m₀ * ((μ : Dˣ) : D) = ((μ : Dˣ) : D) * m₀) ∧ modK D (u - m₀) < 1 := by
  obtain ⟨hAR, hrep⟩ := weil_I_4_thm7_repr hD M N.hM
  obtain ⟨m₀, ⟨hm0, hmP⟩, -⟩ := hrep u hu
  rcases hm0 with rfl | ⟨m, hmM, rfl⟩
  · exact ⟨0, (pK1 M).zero_mem, fun μ => by simp, hmP⟩
  · exact ⟨_, mem_pK1_M M hmM, fun μ => N.mcomm ⟨m, hmM⟩ μ, hmP⟩

/-- Elements commuting with `M` are in `K₁`. -/
theorem comm_mem_pK1 {x : D} (hx : ∀ μ : M, x * ((μ : Dˣ) : D) = ((μ : Dˣ) : D) * x) : x ∈ pK1 M := by
  have hq1 := one_lt_pq_nat hD
  set Pi : D := N.π ^ N.ν with hPi
  have hPiC : Pi ∈ Subring.center D := N.pi_pow_central
  have hPi0 : Pi ≠ 0 := pow_ne_zero _ N.π_ne
  set r : ℝ≥0 := qi hD ^ N.ν with hr
  have hPimod : modK D Pi = r := N.modK_pi_pow N.ν
  have hr1 : r < 1 := pow_lt_one₀ zero_le (qi_lt_one hD) N.ν_pos.ne'
  have hr0 : 0 < r := pow_pos (qi_pos hD) _
  have hPin : ∀ n : ℕ, Pi ^ n ∈ Subring.center D := fun n => (Subring.center D).pow_mem hPiC n
  have hPinK : ∀ n : ℕ, Pi ^ n ∈ pK1 M := fun n => mem_pK1_center M (hPin n)
  have hcent : ∀ (z : D), z ∈ Subring.center D → ∀ y : D, z * y = y * z :=
    fun z hz y => (Subring.mem_center_iff.1 hz y).symm
  have S : ∀ k : ℕ, ∀ n : ℕ, ∀ y : D, (∀ μ : M, y * ((μ : Dˣ) : D) = ((μ : Dˣ) : D) * y) →
      modK D y ≤ r ^ n → ∃ z ∈ pK1 M, modK D (y - z) ≤ r ^ (n + k) := by
    intro k
    induction k with
    | zero => intro n y _ hy; exact ⟨0, (pK1 M).zero_mem, by simpa using hy⟩
    | succ k ih =>
      intro n y hyC hy
      have hPn0 : Pi ^ n ≠ 0 := pow_ne_zero _ hPi0
      have hPnmod : modK D (Pi ^ n) = r ^ n := by rw [modK_pow, hPimod]
      set u : D := y * (Pi ^ n)⁻¹ with hu
      have hcn : ∀ μ : M, Commute (Pi ^ n) ((μ : Dˣ) : D) := fun μ => hcent _ (hPin n) _
      have huC : ∀ μ : M, u * ((μ : Dˣ) : D) = ((μ : Dˣ) : D) * u := by
        intro μ
        exact ((show Commute y ((μ : Dˣ) : D) from hyC μ).mul_left (hcn μ).inv_left₀).eq
      have hu1 : modK D u ≤ 1 := by
        rw [hu, modK_mul, modK_inv hPn0, hPnmod]
        exact (mul_inv_le_iff₀ (pow_pos hr0 n)).2 (by simpa using hy)
      obtain ⟨m₀, hm₀K, hm₀C, hm₀P⟩ := N.exists_digit hu1
      set t : D := u - m₀ with ht
      have htC : ∀ μ : M, t * ((μ : Dˣ) : D) = ((μ : Dˣ) : D) * t := fun μ =>
        ((show Commute u ((μ : Dˣ) : D) from huC μ).sub_left (show Commute m₀ ((μ : Dˣ) : D) from hm₀C μ)).eq
      have htle : modK D t ≤ r := N.le_of_comm_lt_one htC hm₀P
      have hy'eq : y - m₀ * Pi ^ n = t * Pi ^ n := by
        simp only [ht, hu, sub_mul, inv_mul_cancel_right₀ hPn0]
      have hy'C : ∀ μ : M, (y - m₀ * Pi ^ n) * ((μ : Dˣ) : D) = ((μ : Dˣ) : D) * (y - m₀ * Pi ^ n) := fun μ =>
        ((show Commute y ((μ : Dˣ) : D) from hyC μ).sub_left
          ((show Commute m₀ ((μ : Dˣ) : D) from hm₀C μ).mul_left (hcn μ))).eq
      have hy'le : modK D (y - m₀ * Pi ^ n) ≤ r ^ (n + 1) := by
        rw [hy'eq, modK_mul, hPnmod, pow_succ, mul_comm (r ^ n) r]
        exact mul_le_mul' htle le_rfl
      obtain ⟨z', hz'K, hz'⟩ := ih (n + 1) _ hy'C hy'le
      refine ⟨m₀ * Pi ^ n + z', (pK1 M).add_mem ((pK1 M).mul_mem hm₀K (hPinK n)) hz'K, ?_⟩
      have : y - (m₀ * Pi ^ n + z') = (y - m₀ * Pi ^ n) - z' := by abel
      rw [this, show n + (k + 1) = n + 1 + k by ring]
      exact hz'
  have hPit : Filter.Tendsto (fun n : ℕ => Pi ^ n) Filter.atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_iff_modK Pi).2 (by rw [hPimod]; exact hr1)
  by_cases hx0 : x = 0
  · rw [hx0]; exact (pK1 M).zero_mem
  have ht : Filter.Tendsto (fun n : ℕ => Pi ^ n * x) Filter.atTop (𝓝 0) := by
    simpa using hPit.mul_const x
  have hm : Filter.Tendsto (fun n : ℕ => modK D (Pi ^ n * x)) Filter.atTop (𝓝 0) := by
    have := (continuous_modK (K := D)).tendsto 0 |>.comp ht
    rw [Function.comp_def, modK_zero] at this
    exact this
  obtain ⟨N₀, hN₀⟩ := (hm.eventually_lt_const one_pos).exists
  set x₁ : D := Pi ^ N₀ * x with hx₁
  have hx₁C : ∀ μ : M, x₁ * ((μ : Dˣ) : D) = ((μ : Dˣ) : D) * x₁ := fun μ =>
    ((show Commute (Pi ^ N₀) ((μ : Dˣ) : D) from hcent _ (hPin N₀) _).mul_left
      (show Commute x ((μ : Dˣ) : D) from hx μ)).eq
  choose z hzK hz using fun k : ℕ => S k 0 x₁ hx₁C (by simpa using hN₀.le)
  have hlim : Filter.Tendsto z Filter.atTop (𝓝 x₁) := by
    rw [← tendsto_sub_nhds_zero_iff]
    refine tendsto_zero_of_modK_le hD (fun k => ?_)
    have h1 := hz k
    rw [zero_add] at h1
    have h2 : modK D (z k - x₁) = modK D (x₁ - z k) := by rw [← modK_neg, neg_sub]
    rw [h2]
    refine h1.trans ?_
    rw [hr, ← pow_mul]
    exact pow_le_pow_of_le_one zero_le (qi_lt_one hD).le (by nlinarith [N.ν_pos])
  have hx₁K : x₁ ∈ pK1 M := (isClosed_pK1 hD M).mem_of_tendsto hlim (Filter.Eventually.of_forall hzK)
  have : x = (Pi ^ N₀)⁻¹ * x₁ := by rw [hx₁, inv_mul_cancel_left₀ (pow_ne_zero _ hPi0)]
  rw [this]
  exact (pK1 M).mul_mem ((pK1 M).inv_mem (hPinK N₀)) hx₁K

end NormData

/-- A sum of elements with pairwise distinct nonzero modules has module the largest one. -/
theorem modK_sum_distinct (hD : IsPField D p) {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → D)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i ≠ 0 → f j ≠ 0 → modK D (f i) ≠ modK D (f j)) :
    (∀ j ∈ s, modK D (f j) ≤ modK D (∑ i ∈ s, f i)) ∧
      (∑ i ∈ s, f i = 0 ∨ ∃ j ∈ s, modK D (∑ i ∈ s, f i) = modK D (f j)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ihA, ihB⟩ := ih (fun i hi j hj => hdist i (Finset.mem_insert_of_mem hi) j
      (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert ha]
    set S := ∑ i ∈ s, f i with hSdef
    by_cases hfa : f a = 0
    · rw [hfa, zero_add]
      refine ⟨fun j hj => ?_, ?_⟩
      · rcases Finset.mem_insert.1 hj with rfl | hj
        · simp [hfa]
        · exact ihA j hj
      · rcases ihB with h | ⟨j, hj, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, Finset.mem_insert_of_mem hj, h⟩
    by_cases hS : S = 0
    · rw [hS, add_zero]
      refine ⟨fun j hj => ?_, Or.inr ⟨a, Finset.mem_insert_self _ _, rfl⟩⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact le_rfl
      · have := ihA j hj
        rw [hS, modK_zero] at this
        exact this.trans zero_le
    obtain ⟨j₀, hj₀, hSj⟩ : ∃ j₀ ∈ s, modK D S = modK D (f j₀) := by
      rcases ihB with h | h
      · exact absurd h hS
      · exact h
    have hSpos : 0 < modK D S := modK_pos_iff.2 hS
    have hfj0 : f j₀ ≠ 0 := by
      intro h; rw [h, modK_zero] at hSj; exact hSpos.ne' hSj
    have haj : a ≠ j₀ := fun h => ha (h ▸ hj₀)
    have hne : modK D (f a) ≠ modK D S := by
      rw [hSj]
      exact hdist a (Finset.mem_insert_self _ _) j₀ (Finset.mem_insert_of_mem hj₀) haj hfa hfj0
    have hU := isUltrametricMod_of_isPField hD
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsum : modK D (f a + S) = modK D S := by
        rw [add_comm]; exact modK_add_eq_of_lt hU hlt
      refine ⟨fun j hj => ?_, Or.inr ⟨j₀, Finset.mem_insert_of_mem hj₀, by rw [hsum, hSj]⟩⟩
      rw [hsum]
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact hlt.le
      · exact ihA j hj
    · have hsum : modK D (f a + S) = modK D (f a) := modK_add_eq_of_lt hU hgt
      refine ⟨fun j hj => ?_, Or.inr ⟨a, Finset.mem_insert_self _ _, hsum⟩⟩
      rw [hsum]
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact le_rfl
      · exact (ihA j hj).trans hgt.le

namespace NormData

variable {hD : IsPField D p} {M : Subgroup Dˣ} (N : NormData hD M)

include N

theorem modK_K1_term {c : D} (hc : c ∈ pK1 M) (hc0 : c ≠ 0) (j : ℕ) :
    ∃ m : ℤ, modK D c = (pq hD : ℝ≥0) ^ ((N.ν : ℤ) * m) ∧
      modK D (c * N.π ^ j) = (pq hD : ℝ≥0) ^ ((N.ν : ℤ) * m - j) := by
  have hq1 := one_lt_pq_nat hD
  have hq0 : (pq hD : ℝ≥0) ≠ 0 := by positivity
  obtain ⟨m, hm⟩ := N.val_of_comm hc0 (fun μ => N.pK1_comm_M hc μ)
  refine ⟨m, hm, ?_⟩
  rw [modK_mul, N.modK_pi_pow, hm, qi, inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hq0]
  congr 1

theorem basis_core (c : Fin N.ν → D) (hc : ∀ j, c j ∈ pK1 M) :
    (∀ j : Fin N.ν, modK D (c j * N.π ^ (j : ℕ)) ≤ modK D (∑ i, c i * N.π ^ (i : ℕ))) ∧
    (modK D (∑ i, c i * N.π ^ (i : ℕ)) ≤ 1 ↔ ∀ i, modK D (c i) ≤ 1) := by
  have hq1 := one_lt_pq_nat hD
  have hq : (1 : ℝ≥0) < (pq hD : ℝ≥0) := by exact_mod_cast hq1
  have hq0 : (0 : ℝ≥0) < (pq hD : ℝ≥0) := lt_trans one_pos hq
  have hdist : ∀ i ∈ (Finset.univ : Finset (Fin N.ν)), ∀ j ∈ (Finset.univ : Finset (Fin N.ν)), i ≠ j →
      c i * N.π ^ (i : ℕ) ≠ 0 → c j * N.π ^ (j : ℕ) ≠ 0 →
      modK D (c i * N.π ^ (i : ℕ)) ≠ modK D (c j * N.π ^ (j : ℕ)) := by
    intro i _ j _ hij hi hj heq
    have hci : c i ≠ 0 := fun h => hi (by rw [h, zero_mul])
    have hcj : c j ≠ 0 := fun h => hj (by rw [h, zero_mul])
    obtain ⟨mi, -, hmi⟩ := N.modK_K1_term (hc i) hci i
    obtain ⟨mj, -, hmj⟩ := N.modK_K1_term (hc j) hcj j
    rw [hmi, hmj] at heq
    have h2 := zpow_right_injective₀ hq0 hq.ne' heq
    have hk : (N.ν : ℤ) * (mi - mj) = (i : ℤ) - j := by linarith
    have hi' := i.2
    have hj' := j.2
    rcases lt_trichotomy (mi - mj) 0 with h | h | h
    · nlinarith
    · rw [h] at hk
      exact hij (Fin.ext (by omega))
    · nlinarith
  obtain ⟨hA, -⟩ := modK_sum_distinct hD Finset.univ (fun i : Fin N.ν => c i * N.π ^ (i : ℕ)) hdist
  refine ⟨fun j => hA j (Finset.mem_univ _), ⟨fun hs j => ?_, fun hall => ?_⟩⟩
  · have h1 : modK D (c j * N.π ^ (j : ℕ)) ≤ 1 := (hA j (Finset.mem_univ _)).trans hs
    by_cases hcj : c j = 0
    · simp [hcj]
    obtain ⟨m, hm, hm2⟩ := N.modK_K1_term (hc j) hcj j
    rw [hm2] at h1
    have h3 : (N.ν : ℤ) * m - j ≤ 0 := by
      by_contra hcon
      push Not at hcon
      exact absurd h1 (not_le.2 (one_lt_zpow₀ hq hcon))
    have hj' := j.2
    have hνpos : (0 : ℤ) < N.ν := by exact_mod_cast N.ν_pos
    have hj'' : ((j : ℕ) : ℤ) < N.ν := by exact_mod_cast hj'
    have h4 : m ≤ 0 := by
      by_contra hm1
      push Not at hm1
      nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ m by omega) hνpos.le]
    rw [hm]
    exact zpow_le_one_of_nonpos₀ hq.le (by nlinarith)
  · refine modK_sum_le hD _ _ (fun i _ => ?_)
    rw [modK_mul, N.modK_pi_pow]
    calc modK D (c i) * qi hD ^ (i : ℕ) ≤ 1 * 1 :=
          mul_le_mul' (hall i) (pow_le_one₀ zero_le (qi_lt_one hD).le)
      _ = 1 := one_mul 1

theorem expansion {x : D} (hx : modK D x ≤ 1) :
    ∃ a : ℕ → D, (∀ i, a i = 0 ∨ ∃ μ ∈ M, a i = ((μ : Dˣ) : D)) ∧
      HasSum (fun i : ℕ => a i * N.π ^ i) x := by
  classical
  have hπ0 := N.π_ne
  obtain ⟨hAR, hrep⟩ := weil_I_4_thm7_repr hD M N.hM
  have hqi : ((pq hD : ℝ≥0) ^ 1)⁻¹ = qi hD := by simp [qi]
  obtain ⟨a, ⟨ha, hsum⟩, -⟩ := weil_I_4_cor2_thm6 hD hπ0 (n := 1) le_rfl (by rw [hqi]; exact N.modK_pi)
    (A := {m | m = 0 ∨ ∃ μ ∈ M, m = ((μ : Dˣ) : D)})
    (fun m hm => by
      rcases hm with rfl | ⟨μ, hμ, rfl⟩
      · exact (pR hD).zero_mem
      · exact hAR μ hμ)
    (fun y hy => by
      obtain ⟨m, ⟨hm1, hm2⟩, huniq⟩ := hrep y hy
      have hiff : ∀ w : D, w ∈ pP hD ↔ modK D w ≤ ((pq hD : ℝ≥0) ^ 1)⁻¹ := fun w => by
        rw [hqi]
        exact ⟨fun h => modK_le_qi_of_lt_one hD h, fun h => lt_of_le_of_lt h (qi_lt_one hD)⟩
      exact ⟨m, ⟨hm1, (hiff _).1 hm2⟩, fun a' ⟨ha1, ha2⟩ => huniq a' ⟨ha1, (hiff _).2 ha2⟩⟩)
    0 (by simpa using hx)
  exact ⟨a, ha, by simpa using hsum⟩

end NormData

/-- The `K₀`-submodule of sums `∑_{i<n} c_i π^i` with `c_i ∈ K₁`. -/
def Wsub (M : Subgroup Dˣ) (π : D) (n : ℕ) : Submodule (Subring.center D) D where
  carrier := {x | ∃ c : Fin n → pK1 M, x = ∑ i, (c i : D) * π ^ (i : ℕ)}
  add_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
    refine ⟨fun i => c i + c' i, ?_⟩
    simp [add_mul, Finset.sum_add_distrib]
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro a _ ⟨c, rfl⟩
    refine ⟨fun i => ⟨(a : D) * c i, (pK1 M).mul_mem (mem_pK1_center M a.2) (c i).2⟩, ?_⟩
    show (a : D) * _ = _
    simp [Finset.mul_sum, mul_assoc]

theorem isClosed_Wsub (hD : IsPField D p) (M : Subgroup Dˣ) (π : D) (n : ℕ) :
    IsClosed (Wsub M π n : Set D) := by
  haveI := center_neBot hD
  haveI := (weil_I_4_prop5_center hD).2
  exact isClosed_of_finiteDimensional (K := Subring.center D) (V := D) (Wsub M π n)

theorem center_inv_mem {z : D} (hz : z ∈ Subring.center D) : z⁻¹ ∈ Subring.center D := by
  rw [Subring.mem_center_iff] at hz ⊢
  intro g
  exact (Commute.inv_right₀ (show Commute g z from hz g)).eq

namespace NormData

variable {hD : IsPField D p} {M : Subgroup Dˣ} (N : NormData hD M)

include N

theorem single_mem {y : D} (hy : y ∈ pK1 M) {j : ℕ} (hj : j < N.ν) :
    y * N.π ^ j ∈ Wsub M N.π N.ν := by
  refine ⟨fun l => if (l : ℕ) = j then ⟨y, hy⟩ else 0, ?_⟩
  rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin N.ν)]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ j := fun h => hb (Fin.ext h)
    simp [this]
  · simp

theorem mem_W_of_R {x : D} (hx : modK D x ≤ 1) : x ∈ Wsub M N.π N.ν := by
  obtain ⟨a, ha, hsum⟩ := N.expansion hx
  have hPiC := N.pi_pow_central
  have hterm : ∀ i, a i * N.π ^ i ∈ Wsub M N.π N.ν := by
    intro i
    have e : N.π ^ i = (N.π ^ N.ν) ^ (i / N.ν) * N.π ^ (i % N.ν) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have haK : a i ∈ pK1 M := by
      rcases ha i with h | ⟨μ, hμ, h⟩
      · rw [h]; exact (pK1 M).zero_mem
      · rw [h]; exact mem_pK1_M M hμ
    rw [e, ← mul_assoc]
    exact N.single_mem ((pK1 M).mul_mem haK (mem_pK1_center M ((Subring.center D).pow_mem hPiC _)))
      (Nat.mod_lt _ N.ν_pos)
  exact (isClosed_Wsub hD M N.π N.ν).mem_of_tendsto hsum.tendsto_sum_nat
    (Filter.Eventually.of_forall fun n => Submodule.sum_mem _ fun i _ => hterm i)

theorem mem_W (x : D) : x ∈ Wsub M N.π N.ν := by
  have hPiC := N.pi_pow_central
  have hr1 : modK D (N.π ^ N.ν) < 1 := by
    rw [N.modK_pi_pow]; exact pow_lt_one₀ zero_le (qi_lt_one hD) N.ν_pos.ne'
  have hPit : Filter.Tendsto (fun n : ℕ => (N.π ^ N.ν) ^ n) Filter.atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_iff_modK _).2 hr1
  have ht : Filter.Tendsto (fun n : ℕ => (N.π ^ N.ν) ^ n * x) Filter.atTop (𝓝 0) := by
    simpa using hPit.mul_const x
  have hm : Filter.Tendsto (fun n : ℕ => modK D ((N.π ^ N.ν) ^ n * x)) Filter.atTop (𝓝 0) := by
    have := (continuous_modK (K := D)).tendsto 0 |>.comp ht
    rw [Function.comp_def, modK_zero] at this
    exact this
  obtain ⟨N₀, hN₀⟩ := (hm.eventually_lt_const one_pos).exists
  have h1 := N.mem_W_of_R hN₀.le
  have hc : ((N.π ^ N.ν) ^ N₀)⁻¹ ∈ Subring.center D := center_inv_mem ((Subring.center D).pow_mem hPiC N₀)
  have h2 := (Wsub M N.π N.ν).smul_mem ⟨_, hc⟩ h1
  have h3 : (⟨_, hc⟩ : Subring.center D) • ((N.π ^ N.ν) ^ N₀ * x) = x := by
    show ((N.π ^ N.ν) ^ N₀)⁻¹ * ((N.π ^ N.ν) ^ N₀ * x) = x
    exact inv_mul_cancel_left₀ (pow_ne_zero _ (pow_ne_zero _ N.π_ne)) x
  rwa [h3] at h2

theorem basis_unique (x : D) :
    ∃! c : Fin N.ν → pK1 M, x = ∑ i, (c i : D) * N.π ^ (i : ℕ) := by
  obtain ⟨c, hc⟩ := N.mem_W x
  refine ⟨c, hc, fun c' hc' => ?_⟩
  have hz : ∑ i, (((c i : D) - c' i) * N.π ^ (i : ℕ)) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [← hc, ← hc', sub_self]
  have hcore := (N.basis_core (fun i => (c i : D) - c' i) (fun i => (pK1 M).sub_mem (c i).2 (c' i).2)).1
  funext j
  have h1 := hcore j
  rw [hz, modK_zero] at h1
  have h2 : ((c j : D) - c' j) * N.π ^ (j : ℕ) = 0 := modK_eq_zero_iff.1 (le_antisymm h1 zero_le)
  rcases mul_eq_zero.1 h2 with h | h
  · exact (Subtype.ext (sub_eq_zero.1 h)).symm
  · exact absurd h (pow_ne_zero _ N.π_ne)

theorem prime_center {x : D} (hx : x ∈ Subring.center D) (hlt : modK D x < 1) :
    ∃ y ∈ Subring.center D, modK D y ≤ 1 ∧ x = N.π ^ N.ν * y := by
  have hxC : ∀ μ : M, x * ((μ : Dˣ) : D) = ((μ : Dˣ) : D) * x :=
    fun μ => (Subring.mem_center_iff.1 hx _).symm
  have hle := N.le_of_comm_lt_one hxC hlt
  have hP0 : (N.π ^ N.ν) ≠ 0 := pow_ne_zero _ N.π_ne
  refine ⟨(N.π ^ N.ν)⁻¹ * x, (Subring.center D).mul_mem (center_inv_mem N.pi_pow_central) hx, ?_, ?_⟩
  · rw [modK_mul, modK_inv hP0, N.modK_pi_pow]
    exact (inv_mul_le_iff₀ (pow_pos (qi_pos hD) _)).2 (by simpa using hle)
  · rw [mul_inv_cancel_left₀ hP0]

/-- The coordinate map `(c_i) ↦ ∑ c_i π^i`. -/
def Phi : (Fin N.ν → pK1 M) →ₗ[Subring.center D] D where
  toFun c := ∑ i, (c i : D) * N.π ^ (i : ℕ)
  map_add' c c' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    show _ = (a : D) * _
    simp [Finset.mul_sum, mul_assoc, pK1_smul_coe]

theorem Phi_bijective : Function.Bijective N.Phi := by
  refine ⟨fun c c' h => ?_, fun x => ?_⟩
  · exact (N.basis_unique (N.Phi c)).unique rfl h
  · obtain ⟨c, hc, -⟩ := N.basis_unique x
    exact ⟨c, hc.symm⟩

theorem finrank_D_eq :
    Module.finrank (Subring.center D) D = N.ν * Module.finrank (Subring.center D) (pK1 M) := by
  haveI := center_neBot hD
  haveI hfd := (weil_I_4_prop5_center hD).2
  haveI : Module.Finite (Subring.center D) (pK1 M) :=
    Module.Finite.of_injective (pK1_incl M) (pK1_incl_injective M)
  have e := (LinearEquiv.ofBijective N.Phi N.Phi_bijective).finrank_eq
  rw [Module.finrank_pi_fintype] at e
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at e
  exact e.symm

theorem conj_mem {x : D} (hx : x ∈ pK1 M) : N.π⁻¹ * x * N.π ∈ pK1 M := by
  apply N.comm_mem_pK1
  intro μ
  have hπ0 := N.π_ne
  have h1 := N.pi_mul μ
  have hx' := N.pK1_comm_M hx (N.c μ)
  have h2 : N.π⁻¹ * (((N.c μ : M) : Dˣ) : D) = ((μ : Dˣ) : D) * N.π⁻¹ := by
    calc N.π⁻¹ * (((N.c μ : M) : Dˣ) : D) = N.π⁻¹ * ((((N.c μ : M) : Dˣ) : D) * N.π) * N.π⁻¹ := by
          simp [mul_assoc, hπ0]
      _ = N.π⁻¹ * (N.π * ((μ : Dˣ) : D)) * N.π⁻¹ := by rw [h1]
      _ = ((μ : Dˣ) : D) * N.π⁻¹ := by simp [mul_assoc, hπ0]
  calc N.π⁻¹ * x * N.π * ((μ : Dˣ) : D) = N.π⁻¹ * x * (N.π * ((μ : Dˣ) : D)) := by rw [mul_assoc _ N.π]
    _ = N.π⁻¹ * x * ((((N.c μ : M) : Dˣ) : D) * N.π) := by rw [h1]
    _ = N.π⁻¹ * (x * (((N.c μ : M) : Dˣ) : D)) * N.π := by simp [mul_assoc]
    _ = N.π⁻¹ * ((((N.c μ : M) : Dˣ) : D) * x) * N.π := by rw [hx']
    _ = (N.π⁻¹ * (((N.c μ : M) : Dˣ) : D)) * x * N.π := by simp [mul_assoc]
    _ = ((μ : Dˣ) : D) * (N.π⁻¹ * x * N.π) := by rw [h2]; simp [mul_assoc]

/-- Conjugation by `π⁻¹ · π` on `K₁`, as an algebra homomorphism over the center. -/
def alphaHom : pK1 M →ₐ[Subring.center D] pK1 M where
  toFun x := ⟨N.π⁻¹ * x * N.π, N.conj_mem x.2⟩
  map_one' := Subtype.ext (by simp [N.π_ne])
  map_mul' x y := Subtype.ext (by simp [mul_assoc, N.π_ne])
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp [mul_add, add_mul])
  commutes' c := Subtype.ext (by
    show N.π⁻¹ * (c : D) * N.π = c
    rw [Subring.mem_center_iff.1 c.2 N.π⁻¹, mul_assoc, inv_mul_cancel₀ N.π_ne, mul_one])

theorem finrank_pK1 : Module.finrank (Subring.center D) (pK1 M) = N.ν := by
  haveI := center_neBot hD
  haveI hfd := (weil_I_4_prop5_center hD).2
  have hπ0 := N.π_ne
  letI : Field (pK1 M) := { (inferInstance : DivisionRing (pK1 M)) with
    mul_comm := fun a b => Subtype.ext (N.pK1_comm a.2 b.2) }
  haveI : FiniteDimensional (Subring.center D) (pK1 M) :=
    Module.Finite.of_injective (pK1_incl M) (pK1_incl_injective M)
  let α : pK1 M ≃ₐ[Subring.center D] pK1 M := AlgEquiv.ofBijective N.alphaHom (AlgHom.bijective _)
  have hα : ∀ x : pK1 M, (α x : D) = N.π⁻¹ * x * N.π := fun x => rfl
  have hαk : ∀ (k : ℕ) (x : pK1 M), ((α ^ k) x : D) = (N.π ^ k)⁻¹ * x * N.π ^ k := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, AlgEquiv.mul_apply, ih (α x), hα, pow_succ']
      simp [mul_inv_rev, mul_assoc]
  have h1 : α ^ N.ν = 1 := by
    ext x
    show ((α ^ N.ν) x : D) = x
    rw [hαk]
    have := Subring.mem_center_iff.1 N.pi_pow_central (x : D)
    rw [mul_assoc, this, inv_mul_cancel_left₀ (pow_ne_zero _ hπ0)]
  have h2 : ∀ m : ℕ, 0 < m → m < N.ν → α ^ m ≠ 1 := by
    intro m hm0 hmν h
    have hσ : N.σ ^ m = 1 := by
      refine Equiv.ext (fun μ => ?_)
      have hx := congrArg (fun e : pK1 M ≃ₐ[Subring.center D] pK1 M =>
        (e ⟨((μ : Dˣ) : D), mem_pK1_M M μ.2⟩ : D)) h
      simp only [hαk] at hx
      have hx2 : ((μ : Dˣ) : D) * N.π ^ m = N.π ^ m * ((μ : Dˣ) : D) := by
        have hpm : N.π ^ m ≠ 0 := pow_ne_zero _ hπ0
        have : (N.π ^ m)⁻¹ * ((μ : Dˣ) : D) * N.π ^ m = ((μ : Dˣ) : D) := hx
        calc ((μ : Dˣ) : D) * N.π ^ m = N.π ^ m * ((N.π ^ m)⁻¹ * ((μ : Dˣ) : D) * N.π ^ m) := by
              simp [mul_assoc, hpm]
          _ = N.π ^ m * ((μ : Dˣ) : D) := by rw [this]
      have hx3 := N.pow_mul_nat m μ
      rw [← hx2] at hx3
      have := mul_right_cancel₀ (pow_ne_zero m hπ0) hx3
      have e2 : ((N.σ ^ m) μ : M) = μ := Subtype.ext (Units.ext this.symm)
      rw [Equiv.Perm.one_apply]
      exact e2
    have : N.ν ∣ m := orderOf_dvd_of_pow_eq_one hσ
    exact absurd (Nat.le_of_dvd hm0 this) (by omega)
  have horder : orderOf α = N.ν := (orderOf_eq_iff N.ν_pos).2 ⟨h1, fun m hm hm0 => h2 m hm0 hm⟩
  set H : Subgroup (pK1 M ≃ₐ[Subring.center D] pK1 M) := Subgroup.zpowers α with hH
  have hfix : IntermediateField.fixedField H = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hαx : α x = x := hx α (Subgroup.mem_zpowers α)
    have hxe : N.π⁻¹ * (x : D) * N.π = x := congrArg Subtype.val hαx
    have hπx : (x : D) * N.π = N.π * x := by
      calc (x : D) * N.π = N.π * (N.π⁻¹ * x * N.π) := by simp [mul_assoc, hπ0]
        _ = N.π * x := by rw [hxe]
    have hc : (x : D) ∈ Subring.center D := N.central_of_comm hπx (fun μ => N.pK1_comm_M x.2 μ)
    exact IntermediateField.mem_bot.2 ⟨⟨x, hc⟩, Subtype.ext rfl⟩
  have key := IntermediateField.finrank_fixedField_eq_card (F := Subring.center D) (E := pK1 M) H
  rw [hfix, IntermediateField.finrank_bot'] at key
  rw [key, hH, Nat.card_zpowers, horder]

theorem numbers [(𝓝[≠] (0 : Subring.center D)).NeBot] (hK₀ : IsPField (Subring.center D) p) :
    pq hD = pq hK₀ ^ N.ν ∧ Module.finrank (Subring.center D) D = N.ν ^ 2 := by
  haveI hfd := (weil_I_4_prop5_center hD).2
  obtain ⟨π₀, hπ0, hπP, -⟩ := weil_I_4_thm6_prime hK₀
  obtain ⟨e, f, he, hf, hq, hmod, hfr⟩ := weil_I_4_cor6_thm6 (K := Subring.center D) (K' := D) hK₀ hD hπ0 hπP
  have hq1 := one_lt_pq_nat hD
  have hqR : (1 : ℝ≥0) < (pq hD : ℝ≥0) := by exact_mod_cast hq1
  have halg : ∀ x : Subring.center D, algebraMap (Subring.center D) D x = (x : D) := fun x => rfl
  have hqe : (1 : ℝ≥0) < (pq hD : ℝ≥0) ^ e := one_lt_pow₀ hqR (by omega)
  have hqν : ((pq hD : ℝ≥0) ^ N.ν)⁻¹ = qi hD ^ N.ν := by rw [qi, inv_pow]
  -- ν ≤ e
  have h1 : N.ν ≤ e := by
    have hx : modK D ((π₀ : Subring.center D) : D) < 1 := by
      rw [← halg, hmod]; exact inv_lt_one_of_one_lt₀ hqe
    obtain ⟨y, -, hy, hxy⟩ := N.prime_center π₀.2 hx
    have : ((pq hD : ℝ≥0) ^ e)⁻¹ ≤ qi hD ^ N.ν := by
      have h2 : modK D (algebraMap (Subring.center D) D π₀) = modK D (N.π ^ N.ν) * modK D y := by
        rw [halg, hxy, modK_mul]
      rw [hmod, N.modK_pi_pow] at h2
      rw [h2]
      calc qi hD ^ N.ν * modK D y ≤ qi hD ^ N.ν * 1 := mul_le_mul' le_rfl hy
        _ = qi hD ^ N.ν := mul_one _
    rw [← hqν] at this
    have hq0 : (0 : ℝ≥0) < (pq hD : ℝ≥0) := lt_trans one_pos hqR
    have h3 := (inv_le_inv₀ (pow_pos hq0 e) (pow_pos hq0 N.ν)).1 this
    exact (pow_le_pow_iff_right₀ hqR).1 h3
  -- e ≤ ν
  have h2 : e ≤ N.ν := by
    let Pi' : Subring.center D := ⟨N.π ^ N.ν, N.pi_pow_central⟩
    have hlt : modK (Subring.center D) Pi' < 1 := by
      rw [← weil_I_4_cor5_thm6_P (K' := D) Pi', halg]
      show modK D (N.π ^ N.ν) < 1
      rw [N.modK_pi_pow]; exact pow_lt_one₀ zero_le (qi_lt_one hD) N.ν_pos.ne'
    have hmem : Pi' ∈ pP hK₀ := hlt
    rw [hπP] at hmem
    obtain ⟨r, hr, hrr⟩ := hmem
    have hrD : N.π ^ N.ν = (π₀ : D) * (r : D) := congrArg Subtype.val hrr.symm
    have hrle : modK D (r : D) ≤ 1 := by
      have := (weil_I_4_cor5_thm6_R (K' := D) (r : Subring.center D)).2 (mem_pR.1 hr)
      rwa [halg] at this
    have : qi hD ^ N.ν ≤ ((pq hD : ℝ≥0) ^ e)⁻¹ := by
      have h4 : modK D (N.π ^ N.ν) = qi hD ^ N.ν := N.modK_pi_pow N.ν
      rw [← h4, hrD, modK_mul, ← halg, hmod]
      calc ((pq hD : ℝ≥0) ^ e)⁻¹ * modK D (r : D) ≤ ((pq hD : ℝ≥0) ^ e)⁻¹ * 1 := mul_le_mul' le_rfl hrle
        _ = _ := mul_one _
    rw [← hqν] at this
    have hq0 : (0 : ℝ≥0) < (pq hD : ℝ≥0) := lt_trans one_pos hqR
    have h3 := (inv_le_inv₀ (pow_pos hq0 N.ν) (pow_pos hq0 e)).1 this
    exact (pow_le_pow_iff_right₀ hqR).1 h3
  have heν : e = N.ν := le_antisymm h2 h1
  have hfin := N.finrank_D_eq
  rw [N.finrank_pK1, hfr, heν] at hfin
  have hfν : f = N.ν := by
    have := N.ν_pos
    exact Nat.eq_of_mul_eq_mul_left this hfin
  subst hfν
  exact ⟨hq, by rw [hfr, heν]; ring⟩

theorem moved_by_pow {j : ℕ} (hj0 : 0 < j) (hjν : j < N.ν) :
    ∃ x ∈ pK1 M, (N.π ^ j)⁻¹ * x * N.π ^ j ≠ x := by
  have hπ0 := N.π_ne
  have hσ : N.σ ^ j ≠ 1 := by
    intro h
    have h1 := Nat.le_of_dvd hj0 (orderOf_dvd_of_pow_eq_one h)
    have h2 : N.ν = orderOf N.σ := rfl
    omega
  obtain ⟨μ, hμ⟩ : ∃ μ : M, (N.σ ^ j) μ ≠ μ := by
    by_contra hcon
    push Not at hcon
    exact hσ (Equiv.ext hcon)
  refine ⟨(((N.σ ^ j) μ : M) : Dˣ), mem_pK1_M M ((N.σ ^ j) μ).2, fun h => hμ ?_⟩
  have h1 := N.pow_mul_nat j μ
  have h2 : (N.π ^ j)⁻¹ * (((N.σ ^ j) μ : M) : Dˣ) * N.π ^ j = ((μ : Dˣ) : D) := by
    rw [mul_assoc, ← h1, inv_mul_cancel_left₀ (pow_ne_zero _ hπ0)]
  rw [h2] at h
  exact Subtype.ext (Units.ext h.symm)

theorem finrank_span : Module.finrank (Subring.center D)
    (Submodule.span (Subring.center D) (pK1 M : Set D)) = N.ν := by
  have hsp : Submodule.span (Subring.center D) (pK1 M : Set D) = K1sub M := Submodule.span_eq (K1sub M)
  rw [hsp]
  let e : K1sub M ≃ₗ[Subring.center D] pK1 M :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun y => ⟨y, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [e.finrank_eq]
  exact N.finrank_pK1

theorem conj_fixed_iff {x : D} (hx : x ∈ pK1 M) :
    N.π⁻¹ * x * N.π = x ↔ x ∈ Subring.center D := by
  have hπ0 := N.π_ne
  constructor
  · intro hxe
    have hπx : x * N.π = N.π * x := by
      calc x * N.π = N.π * (N.π⁻¹ * x * N.π) := by simp [mul_assoc, hπ0]
        _ = N.π * x := by rw [hxe]
    exact N.central_of_comm hπx (fun μ => N.pK1_comm_M hx μ)
  · intro hxc
    have := Subring.mem_center_iff.1 hxc N.π⁻¹
    rw [this, mul_assoc, inv_mul_cancel₀ hπ0, mul_one]

end NormData

/-- **Weil, I.§4, Prop. 5** (structure of division algebras over $p$-fields). See the module docstring. -/
@[kb "weil1973bnt" "Ch. I, §4, Prop. 5 (p. 20-21)"]
theorem weil_I_4_prop5 (hD : IsPField D p) (M : Subgroup Dˣ) (hM : Nat.card M = pq hD - 1) :
    haveI := center_neBot hD
    ∃ (hK₀ : IsPField (Subring.center D) p) (d : ℕ), 1 ≤ d ∧ pq hD = pq hK₀ ^ d ∧
      Module.finrank (Subring.center D) D = d ^ 2 ∧
      -- $K_1$ is commutative, maximal commutative, of dimension $d$ over $K_0$, unramified
      (∀ x ∈ pK1 M, ∀ y ∈ pK1 M, x * y = y * x) ∧
      (∀ x : D, (∀ y ∈ pK1 M, x * y = y * x) → x ∈ pK1 M) ∧
      Module.finrank (Subring.center D) (Submodule.span (Subring.center D) (pK1 M : Set D)) = d ∧
      (∀ x ∈ pR hD, ∃ y ∈ pK1 M, modK D (x - y) < 1) ∧
      ∃ π : D, π ≠ 0 ∧ pP hD = (fun r => π * r) '' (pR hD : Set D) ∧
        -- (a) $\pi^d$ is a prime element of $K_0$
        (π ^ d ∈ Subring.center D ∧ ∀ x ∈ Subring.center D, modK D x < 1 →
          ∃ y ∈ Subring.center D, modK D y ≤ 1 ∧ x = π ^ d * y) ∧
        -- (b) $1,\pi,\dots,\pi^{d-1}$ is a left basis over $K_1$ and generates $R$ over $R_1$
        (∀ x : D, ∃! c : Fin d → pK1 M, x = ∑ i, (c i : D) * π ^ (i : ℕ)) ∧
        (∀ c : Fin d → pK1 M, modK D (∑ i, (c i : D) * π ^ (i : ℕ)) ≤ 1 ↔ ∀ i, modK D (c i : D) ≤ 1) ∧
        -- (c) conjugation by $\pi$ generates the Galois group of $K_1$ over $K_0$
        (∀ x ∈ pK1 M, π⁻¹ * x * π ∈ pK1 M) ∧
        (∀ x ∈ pK1 M, π⁻¹ * x * π = x ↔ x ∈ Subring.center D) ∧
        (∀ x ∈ pK1 M, (π ^ d)⁻¹ * x * π ^ d = x) ∧
        ∀ j : ℕ, 0 < j → j < d → ∃ x ∈ pK1 M, (π ^ j)⁻¹ * x * π ^ j ≠ x := by
  haveI := center_neBot hD
  obtain ⟨π, hπ0, hπP, hf, hb⟩ := weil_I_4_thm7_normalizer hD M hM
  let N : NormData hD M := ⟨hM, π, hπ0, hπP, hf, hb⟩
  have hK₀ := (weil_I_4_prop5_center hD).1
  obtain ⟨hq, hfin⟩ := N.numbers hK₀
  refine ⟨hK₀, N.ν, N.ν_pos, hq, hfin, fun x hx y hy => N.pK1_comm hx hy,
    fun x hx => N.comm_mem_pK1 (fun μ => hx _ (mem_pK1_M M μ.2)), N.finrank_span,
    fun x hx => ?_, N.π, N.π_ne, N.π_P, ⟨N.pi_pow_central, fun x hx hlt => N.prime_center hx hlt⟩,
    fun x => N.basis_unique x,
    fun c => (N.basis_core (fun i => (c i : D)) (fun i => (c i).2)).2,
    fun x hx => N.conj_mem hx, fun x hx => N.conj_fixed_iff hx, fun x hx => ?_,
    fun j hj0 hjd => N.moved_by_pow hj0 hjd⟩
  · obtain ⟨m, hm, -, h⟩ := N.exists_digit (mem_pR.1 hx)
    exact ⟨m, hm, h⟩
  · have := Subring.mem_center_iff.1 N.pi_pow_central x
    rw [mul_assoc, this, inv_mul_cancel_left₀ (pow_ne_zero _ N.π_ne)]

end NumberFieldKB.WeilBNT.FieldModule
