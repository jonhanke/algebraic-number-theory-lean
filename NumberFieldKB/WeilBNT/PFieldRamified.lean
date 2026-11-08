import NumberFieldKB.WeilBNT.PFieldExtensions
import NumberFieldKB.WeilBNT.PFieldUnits
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Weil, *Basic Number Theory*, I.§4, Prop. 4 and Cor. 1 of Prop. 4: fully ramified division algebras

$K$ is a commutative $p$-field, $K'$ a division algebra of finite dimension over $K$ with its natural topology; by
Cor. 5 of Thm. 6 (`PFieldExtensions`) $K'$ is a $p$-field. It is *fully ramified* over $K$ if its modular degree is
$f=1$, i.e. $q'=q$ (Def. 4).

* **`weil_I_4_prop4`**: Prop. 4. If $K'$ is fully ramified over $K$ and $\pi'$ is a prime element of $K'$, then $K'$ is
  commutative, $K'=K(\pi')$, and $R'=R[\pi']$.
* `weil_I_4_cor1_prop4`: Cor. 1 of Prop. 4. A commutative $p$-field $K$ of characteristic $p$ is of degree $p$ over
  its subfield $K^p$ of $p$-th powers, and $K=K^p(\pi)$ for a prime element $\pi$.
-/

open Topology Filter
open scoped NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ}
  {K' : Type*} [DivisionRing K'] [Algebra K K'] [FiniteDimensional K K'] [TopologicalSpace K']
  [IsTopologicalDivisionRing K'] [T2Space K'] [ContinuousSMul K K'] [LocallyCompactSpace K']
  [(𝓝[≠] (0 : K')).NeBot]

/-- The ring map $R\to R'$ induced by the structure map $K\to K'$. -/
def algR (hK : IsPField K p) (hK' : IsPField K' p) : pR hK →+* pR hK' where
  toFun x := ⟨algebraMap K K' x, mem_pR.2 ((weil_I_4_cor5_thm6_R (K' := K') (x : K)).2 (mem_pR.1 x.2))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

/-- If $q'=q$, then the images of a full set of representatives $A_0$ of $R$ modulo $P$ form a full set of
representatives of $R'$ modulo $P'$. -/
theorem rep_aux (hK : IsPField K p) (hK' : IsPField K' p) (hf : pq hK' = pq hK) :
    ∃ A0 : Set K, A0 ⊆ pR hK ∧ ∀ x ∈ pR hK', ∃! a, a ∈ algebraMap K K' '' A0 ∧
      modK K' (x - a) ≤ ((pq hK' : ℝ≥0) ^ 1)⁻¹ := by
  classical
  have hle : pPAdd hK ≤ (pPAdd hK').comap (algR hK hK').toAddMonoidHom := by
    intro x hx
    show modK K' (algebraMap K K' (x : K)) < 1
    exact (weil_I_4_cor5_thm6_P (K' := K') (x : K)).2 hx
  let m : (pR hK ⧸ pPAdd hK) →+ (pR hK' ⧸ pPAdd hK') :=
    QuotientAddGroup.map _ _ (algR hK hK').toAddMonoidHom hle
  have hinj : Function.Injective m := by
    intro a b
    induction a using QuotientAddGroup.induction_on with | H a => ?_
    induction b using QuotientAddGroup.induction_on with | H b => ?_
    intro hab
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, QuotientAddGroup.eq] at hab
    rw [QuotientAddGroup.eq]
    have h1 : modK K' (algebraMap K K' (-(a : K) + (b : K))) < 1 := by
      have : modK K' ((-(algR hK hK' a) + algR hK hK' b : pR hK') : K') < 1 := hab
      simpa [algR] using this
    exact (weil_I_4_cor5_thm6_P (K' := K') _).1 h1
  have _ := finite_quotient_pPAdd hK'
  have hcard : Nat.card (pR hK' ⧸ pPAdd hK') ≤ Nat.card (pR hK ⧸ pPAdd hK) := by
    have h1 : Nat.card (pR hK' ⧸ pPAdd hK') = pq hK' := rfl
    have h2 : Nat.card (pR hK ⧸ pPAdd hK) = pq hK := rfl
    rw [h1, h2, hf]
  have hbij := hinj.bijective_of_nat_card_le hcard
  let s : (pR hK ⧸ pPAdd hK) → pR hK := fun u => (QuotientAddGroup.mk_surjective u).choose
  have hs : ∀ u, ((s u : pR hK) : pR hK ⧸ pPAdd hK) = u := fun u =>
    (QuotientAddGroup.mk_surjective u).choose_spec
  have hseq : ∀ u v, modK K ((s u : K) - (s v : K)) < 1 → u = v := by
    intro u v h
    rw [← hs u, ← hs v, QuotientAddGroup.eq]
    show modK K (((-(s u) + s v : pR hK)) : K) < 1
    have : (((-(s u) + s v : pR hK)) : K) = -((s u : K) - s v) := by push_cast; ring
    rw [this, modK_neg]
    exact h
  refine ⟨Set.range fun u => ((s u : pR hK) : K), ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact (s u).2
  · intro x hx
    obtain ⟨u, hu⟩ := hbij.2 ((⟨x, hx⟩ : pR hK') : pR hK' ⧸ pPAdd hK')
    have e2 : m ((s u : pR hK) : pR hK ⧸ pPAdd hK) =
        ((algR hK hK' (s u) : pR hK') : pR hK' ⧸ pPAdd hK') := rfl
    rw [hs u] at e2
    have e3 := e2.symm.trans hu
    have h1 : modK K' (x - algebraMap K K' (s u : K)) < 1 := by
      have h := QuotientAddGroup.eq.1 e3
      have h' : modK K' (((-(algR hK hK' (s u)) + ⟨x, hx⟩ : pR hK')) : K') < 1 := h
      simpa [algR, neg_add_eq_sub] using h'
    refine ⟨algebraMap K K' (s u : K), ⟨⟨_, ⟨u, rfl⟩, rfl⟩, ?_⟩, ?_⟩
    · have := modK_le_qi_of_lt_one hK' h1
      simpa [qi] using this
    · rintro b ⟨⟨b0, ⟨v, rfl⟩, rfl⟩, hb⟩
      have hlt : ((pq hK' : ℝ≥0) ^ 1)⁻¹ < 1 := by simpa [qi] using qi_lt_one hK'
      have h2 : modK K' (algebraMap K K' (s v : K) - algebraMap K K' (s u : K)) < 1 := by
        have : algebraMap K K' (s v : K) - algebraMap K K' (s u : K) =
            (x - algebraMap K K' (s u : K)) - (x - algebraMap K K' (s v : K)) := by abel
        rw [this]
        exact lt_of_le_of_lt (modK_sub_le_max hK' _ _) (max_lt h1 (lt_of_le_of_lt hb hlt))
      have h3 : modK K ((s v : K) - s u) < 1 := by
        rw [← map_sub] at h2
        exact (weil_I_4_cor5_thm6_P (K' := K') _).1 h2
      rw [hseq v u h3]

/-- Prop. 4, the core: every element of $R'$ is $\sum_{j<e}c_j\pi'^j$ with $c_j\in R$, where $e=[K':K]$. -/
theorem prop4_core (hK : IsPField K p) (hK' : IsPField K' p) (hf : pq hK' = pq hK) {π' : K'}
    (hπ'0 : π' ≠ 0) (hπ' : pP hK' = (fun r => π' * r) '' (pR hK' : Set K')) :
    ∀ x ∈ pR hK', ∃ c : Fin (Module.finrank K K') → K, (∀ j, c j ∈ pR hK) ∧
      x = ∑ j, algebraMap K K' (c j) * π' ^ (j : ℕ) := by
  classical
  obtain ⟨π, hπ0, hπ, -⟩ := weil_I_4_thm6_prime hK
  obtain ⟨e, f, he, hf1, hqf, hmod, hfin⟩ := weil_I_4_cor6_thm6 (K' := K') hK hK' hπ0 hπ
  have hq2 := two_le_pq hK
  have hf1' : f = 1 := by
    rw [hf] at hqf
    have : pq hK ^ f = pq hK ^ 1 := by rw [pow_one]; exact hqf.symm
    exact Nat.pow_right_injective hq2 this
  subst hf1'
  rw [mul_one] at hfin
  have hU := isUltrametricMod_of_isPField hK'
  have hq1 : (1 : ℝ≥0) < (pq hK' : ℝ≥0) := by exact_mod_cast one_lt_pq_nat hK'
  have hπR : π ∈ pR hK := by
    have : π ∈ pP hK := by rw [hπ]; exact ⟨1, (pR hK).one_mem, mul_one π⟩
    exact mem_pR.2 (le_of_lt this)
  have hπ₀0 : algebraMap K K' π ≠ 0 := by simpa using hπ0
  have hc_eq : modK K' (algebraMap K K' π) = ((pq hK' : ℝ≥0) ^ Module.finrank K K')⁻¹ := by
    rw [hmod, hfin]
  have hc1 : modK K' (algebraMap K K' π) < 1 := by
    rw [hc_eq]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq1 (by omega))
  have hc0 : 0 < modK K' (algebraMap K K' π) := by
    rw [hc_eq]; exact inv_pos.2 (by positivity)
  obtain ⟨A0, hA0R, hrep⟩ := rep_aux (K' := K') hK hK' hf
  have hA : algebraMap K K' '' A0 ⊆ pR hK' := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_pR.2 ((weil_I_4_cor5_thm6_R (K' := K') a).2 (mem_pR.1 (hA0R ha)))
  have hπ'mod : modK K' π' = ((pq hK' : ℝ≥0) ^ 1)⁻¹ := by
    rw [pow_one]; exact weil_I_4_thm6_modK_prime hK' hπ'0 hπ'
  -- one step: `x ≡ m (mod π)` with `m` a combination of `1, π', ..., π'^(e-1)` over `R`
  have hstep : ∀ x ∈ pR hK', ∃ c : Fin (Module.finrank K K') → K, (∀ j, c j ∈ pR hK) ∧
      modK K' (x - ∑ j, algebraMap K K' (c j) * π' ^ (j : ℕ)) ≤ modK K' (algebraMap K K' π) := by
    intro x hx
    obtain ⟨a, ⟨ha, hs⟩, -⟩ := weil_I_4_cor2_thm6 hK' hπ'0 (n := 1) le_rfl hπ'mod hA hrep 0
      (x := x) (by simpa using mem_pR.1 hx)
    choose b hbA hb using ha
    have hs' : HasSum (fun i : ℕ => algebraMap K K' (b i) * π' ^ i) x := by
      convert hs using 2 with i
      rw [hb i, add_zero, zpow_natCast]
    have hmodb : ∀ i, modK K' (algebraMap K K' (b i)) ≤ 1 := fun i =>
      (weil_I_4_cor5_thm6_R (K' := K') _).2 (mem_pR.1 (hA0R (hbA i)))
    refine ⟨fun j => b j, fun j => hA0R (hbA _), ?_⟩
    have h1 := (hasSum_nat_add_iff' (Module.finrank K K')).2 hs'
    have h2 : ∑ j : Fin (Module.finrank K K'), algebraMap K K' (b j) * π' ^ (j : ℕ) =
        ∑ i ∈ Finset.range (Module.finrank K K'), algebraMap K K' (b i) * π' ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => algebraMap K K' (b i) * π' ^ i) _
    rw [h2, hc_eq]
    refine modK_le_of_hasSum hU h1 fun n => ?_
    rw [modK_mul, modK_pow, hπ'mod, pow_one, ← inv_pow]
    calc modK K' (algebraMap K K' (b (n + Module.finrank K K'))) *
          ((pq hK' : ℝ≥0)⁻¹) ^ (n + Module.finrank K K')
        ≤ 1 * ((pq hK' : ℝ≥0)⁻¹) ^ (n + Module.finrank K K') := mul_le_mul' (hmodb _) le_rfl
      _ ≤ ((pq hK' : ℝ≥0)⁻¹) ^ Module.finrank K K' := by
        rw [one_mul]
        exact pow_le_pow_of_le_one zero_le (inv_le_one_of_one_le₀ hq1.le) (Nat.le_add_left _ _)
  let g : (Fin (Module.finrank K K') → K) → K' := fun c =>
    ∑ j, algebraMap K K' (c j) * π' ^ (j : ℕ)
  have hg : Continuous g := by
    refine continuous_finsetSum _ fun j _ => ?_
    exact ((continuous_algebraMap K K').comp (continuous_apply j)).mul continuous_const
  let S : Set (Fin (Module.finrank K K') → K) := Set.pi Set.univ fun _ => (pR hK : Set K)
  have hS : IsCompact S := isCompact_univ_pi fun _ => weil_I_4_thm6_isCompact hK
  have hMc : IsClosed (g '' S) := (hS.image hg).isClosed
  have hadd : ∀ m1 ∈ g '' S, ∀ m2 ∈ g '' S, m1 + m2 ∈ g '' S := by
    rintro _ ⟨c1, hc1, rfl⟩ _ ⟨c2, hc2, rfl⟩
    refine ⟨fun j => c1 j + c2 j, fun j hj => add_mem (hc1 j hj) (hc2 j hj), ?_⟩
    simp [g, add_mul, Finset.sum_add_distrib]
  have hmul : ∀ r ∈ pR hK, ∀ m ∈ g '' S, algebraMap K K' r * m ∈ g '' S := by
    rintro r hr _ ⟨c, hc, rfl⟩
    refine ⟨fun j => r * c j, fun j hj => mul_mem hr (hc j hj), ?_⟩
    simp [g, Finset.mul_sum, mul_assoc]
  have hind : ∀ N : ℕ, ∀ x ∈ pR hK', ∃ m ∈ g '' S,
      modK K' (x - m) ≤ modK K' (algebraMap K K' π) ^ N := by
    intro N
    induction N with
    | zero =>
      intro x hx
      exact ⟨0, ⟨0, fun j _ => (pR hK).zero_mem, by simp [g]⟩, by simpa using mem_pR.1 hx⟩
    | succ N ih =>
      intro x hx
      obtain ⟨c0, hc0R, h0⟩ := hstep x hx
      have hm0 : g c0 ∈ g '' S := ⟨c0, fun j _ => hc0R j, rfl⟩
      have hy : (algebraMap K K' π)⁻¹ * (x - g c0) ∈ pR hK' := by
        rw [mem_pR, modK_mul, modK_inv hπ₀0]
        calc (modK K' (algebraMap K K' π))⁻¹ * modK K' (x - g c0)
            ≤ (modK K' (algebraMap K K' π))⁻¹ * modK K' (algebraMap K K' π) := mul_le_mul' le_rfl h0
          _ = 1 := inv_mul_cancel₀ hc0.ne'
      obtain ⟨m1, hm1, h1⟩ := ih _ hy
      refine ⟨g c0 + algebraMap K K' π * m1, hadd _ hm0 _ (hmul π hπR _ hm1), ?_⟩
      have : x - (g c0 + algebraMap K K' π * m1) =
          algebraMap K K' π * ((algebraMap K K' π)⁻¹ * (x - g c0) - m1) := by
        rw [mul_sub, mul_inv_cancel_left₀ hπ₀0]; abel
      rw [this, modK_mul, pow_succ']
      exact mul_le_mul' le_rfl h1
  intro x hx
  choose m hmM hmx using fun N => hind N x hx
  have hlim0 : Tendsto (fun N => x - m N) atTop (𝓝 0) :=
    tendsto_zero_of_modK_le_pow hc1 hmx
  have hlim : Tendsto m atTop (𝓝 x) := by
    have := (tendsto_const_nhds (x := x)).sub hlim0
    simpa using this
  have hx' : x ∈ g '' S := hMc.mem_of_tendsto hlim (Eventually.of_forall hmM)
  obtain ⟨c, hcS, hcx⟩ := hx'
  exact ⟨c, fun j => hcS j trivial, hcx.symm⟩

@[kb "weil1973bnt" "Ch. I, §4, Prop. 4"]
theorem weil_I_4_prop4 (hK : IsPField K p) (hK' : IsPField K' p) (hf : pq hK' = pq hK) {π' : K'}
    (hπ'0 : π' ≠ 0) (hπ' : pP hK' = (fun r => π' * r) '' (pR hK' : Set K')) :
    (∀ x y : K', x * y = y * x) ∧ Algebra.adjoin K {π'} = ⊤ ∧
      ∀ x ∈ pR hK', ∃ P : Polynomial K, (∀ i, P.coeff i ∈ pR hK) ∧ x = Polynomial.aeval π' P := by
  classical
  have hcore := prop4_core hK hK' hf hπ'0 hπ'
  have hR : ∀ x ∈ pR hK', ∃ P : Polynomial K, (∀ i, P.coeff i ∈ pR hK) ∧
      x = Polynomial.aeval π' P := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := hcore x hx
    refine ⟨∑ j : Fin (Module.finrank K K'), Polynomial.C (c j) * Polynomial.X ^ (j : ℕ), ?_, ?_⟩
    · intro i
      rw [Polynomial.finsetSum_coeff]
      refine (pR hK).sum_mem fun j _ => ?_
      rw [Polynomial.coeff_C_mul_X_pow]
      split_ifs
      · exact hc j
      · exact (pR hK).zero_mem
    · simp [map_sum]
  obtain ⟨π, hπ0, hπ, -⟩ := weil_I_4_thm6_prime hK
  have hπ₀0 : algebraMap K K' π ≠ 0 := by simpa using hπ0
  have hπlt : modK K π < 1 := by
    have : π ∈ pP hK := by rw [hπ]; exact ⟨1, (pR hK).one_mem, mul_one π⟩
    exact this
  have hc1 : modK K' (algebraMap K K' π) < 1 := by
    rw [modK_algebraMap]
    exact pow_lt_one₀ zero_le hπlt (finrank_ne_zero_aux (K := K) (K' := K'))
  have hall : ∀ x : K', ∃ P : Polynomial K, x = Polynomial.aeval π' P := by
    intro x
    by_cases hx0 : x = 0
    · exact ⟨0, by simp [hx0]⟩
    have hr0 : 0 < modK K' x := modK_pos_iff.2 hx0
    have h1 : Tendsto (fun k : ℕ => modK K' (algebraMap K K' π) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one zero_le hc1
    obtain ⟨k, hk⟩ := (h1.eventually (gt_mem_nhds (inv_pos.2 hr0))).exists
    have hk1 : algebraMap K K' π ^ k * x ∈ pR hK' := by
      rw [mem_pR, modK_mul, modK_pow]
      calc modK K' (algebraMap K K' π) ^ k * modK K' x ≤ (modK K' x)⁻¹ * modK K' x :=
            mul_le_mul' hk.le le_rfl
        _ = 1 := inv_mul_cancel₀ hr0.ne'
    obtain ⟨P, -, hP⟩ := hR _ hk1
    refine ⟨Polynomial.C ((π ^ k)⁻¹) * P, ?_⟩
    rw [map_mul, Polynomial.aeval_C, ← hP]
    have : algebraMap K K' ((π ^ k)⁻¹) = (algebraMap K K' π ^ k)⁻¹ := by simp
    rw [this, inv_mul_cancel_left₀ (pow_ne_zero _ hπ₀0)]
  refine ⟨?_, ?_, hR⟩
  · intro x y
    obtain ⟨P, rfl⟩ := hall x
    obtain ⟨Q, rfl⟩ := hall y
    rw [← map_mul, ← map_mul, mul_comm]
  · rw [Algebra.adjoin_singleton_eq_range_aeval, eq_top_iff]
    intro x _
    obtain ⟨P, hP⟩ := hall x
    exact ⟨P, hP.symm⟩

/-- The type `F` (a field) regarded as the base field of `F` over itself through the Frobenius map; the
synonym keeps the Frobenius algebra structure apart from `Algebra.id`. -/
def FrobBase (F : Type*) : Type _ := F

instance (F : Type*) [Field F] : Field (FrobBase F) := inferInstanceAs (Field F)

instance (F : Type*) [TopologicalSpace F] : TopologicalSpace (FrobBase F) :=
  inferInstanceAs (TopologicalSpace F)

instance (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] :
    IsTopologicalDivisionRing (FrobBase F) := inferInstanceAs (IsTopologicalDivisionRing F)

instance (F : Type*) [TopologicalSpace F] [LocallyCompactSpace F] :
    LocallyCompactSpace (FrobBase F) := inferInstanceAs (LocallyCompactSpace F)

instance (F : Type*) [TopologicalSpace F] [T2Space F] : T2Space (FrobBase F) :=
  inferInstanceAs (T2Space F)

instance (F : Type*) [Field F] [TopologicalSpace F] [(𝓝[≠] (0 : F)).NeBot] :
    (𝓝[≠] (0 : FrobBase F)).NeBot := inferInstanceAs ((𝓝[≠] (0 : F)).NeBot)

@[kb "weil1973bnt" "Ch. I, §4, Cor. 1 of Prop. 4"]
theorem weil_I_4_cor1_prop4 {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [LocallyCompactSpace F] [T2Space F] [(𝓝[≠] (0 : F)).NeBot] (hF : IsPField F p) [CharP F p]
    {π : F} (hπ0 : π ≠ 0) (hπ : pP hF = (fun r => π * r) '' (pR hF : Set F)) :
    haveI : Fact p.Prime := ⟨hF.1⟩
    Module.finrank (frobenius F p).fieldRange F = p ∧
      IntermediateField.adjoin (frobenius F p).fieldRange {π} = ⊤ := by
  have : Fact p.Prime := ⟨hF.1⟩
  let _ : Algebra (FrobBase F) F := (show FrobBase F →+* F from frobenius F p).toAlgebra
  have hsmul : ∀ (a : FrobBase F) (x : F), a • x = (show F from a) ^ p * x := fun a x => rfl
  have : ContinuousSMul (FrobBase F) F := ⟨by
    show Continuous fun z : FrobBase F × F => (show F from z.1) ^ p * z.2
    exact (continuous_fst.pow p).mul continuous_snd⟩
  have : FiniteDimensional (FrobBase F) F := weil_I_2_thm3_cor2_finiteDimensional
  have hK : IsPField (FrobBase F) p := hF
  obtain ⟨-, hadj, -⟩ := weil_I_4_prop4 (K := FrobBase F) (K' := F) hK hF rfl hπ0 hπ
  obtain ⟨e, f, he, hf1, hqf, hmod, hfin⟩ :=
    weil_I_4_cor6_thm6 (K := FrobBase F) (K' := F) hK hF (π := π) hπ0 hπ
  have hq2 := two_le_pq hF
  have hf1' : f = 1 := by
    have : pq hF ^ f = pq hF ^ 1 := by rw [pow_one]; exact hqf.symm
    exact Nat.pow_right_injective hq2 this
  subst hf1'
  have hq1 : (1 : ℝ≥0) < (pq hF : ℝ≥0) := by exact_mod_cast one_lt_pq_nat hF
  have hep : e = p := by
    have h1 : modK F (π ^ p) = ((pq hF : ℝ≥0) ^ e)⁻¹ := hmod
    rw [modK_pow, weil_I_4_thm6_modK_prime hF hπ0 hπ, ← inv_pow] at h1
    have h2 : (pq hF : ℝ≥0) ^ p = (pq hF : ℝ≥0) ^ e := inv_injective (by simpa using h1)
    have h3 : pq hF ^ p = pq hF ^ e := by exact_mod_cast h2
    exact (Nat.pow_right_injective hq2 h3).symm
  have hrank : Module.finrank (FrobBase F) F = Module.finrank (frobenius F p).fieldRange F := by
    unfold Module.finrank
    congr 1
    refine rank_eq_of_equiv_equiv (R := FrobBase F) (R' := (frobenius F p).fieldRange)
      (fun a => ⟨(show F from a) ^ p, ⟨a, rfl⟩⟩) (AddEquiv.refl F) ⟨?_, ?_⟩ ?_
    · intro a b hab
      have : (show F from a) ^ p = (show F from b) ^ p := congrArg Subtype.val hab
      exact frobenius_inj F p this
    · rintro ⟨y, a, rfl⟩
      exact ⟨a, rfl⟩
    · intro a m
      rfl
  refine ⟨?_, ?_⟩
  · rw [← hrank, hfin, hep, mul_one]
  · rw [eq_top_iff]
    intro x _
    rw [Algebra.adjoin_singleton_eq_range_aeval, eq_top_iff] at hadj
    obtain ⟨P, hP⟩ := hadj (Algebra.mem_top : x ∈ ⊤)
    have hP' : Polynomial.aeval π P = x := hP
    rw [← hP', Polynomial.aeval_eq_sum_range]
    set L := IntermediateField.adjoin (frobenius F p).fieldRange {π}
    refine L.sum_mem fun i _ => ?_
    rw [hsmul]
    refine L.mul_mem ?_ (_root_.pow_mem (IntermediateField.mem_adjoin_simple_self _ π) i)
    exact L.algebraMap_mem (⟨_, ⟨P.coeff i, rfl⟩⟩ : (frobenius F p).fieldRange)

end NumberFieldKB.WeilBNT.FieldModule
