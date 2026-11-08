import NumberFieldKB.WeilBNT.PFieldUnitsZp
import Mathlib.Algebra.Module.PID
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Group.Units

/-!
# Weil, *Basic Number Theory*, II.§3, Prop. 9 and its Corollary: the structure of $1+P$ in characteristic $0$

$K$ is a commutative $p$-field of characteristic $0$ (`hK : IsPField K p`, `[CharZero K]`), $1+P$ the
$\mathbb Z_p$-module `Additive (onePlusPUnits hK)` of `PFieldUnitsZp` ($a\cdot u=u^a$).

* `zp_module_finite_of_compact`: a compact Hausdorff topological $\mathbb Z_p$-module $M$ (continuous action) in which
  $pM$ is open is finitely generated (topological Nakayama lemma).
* `exists_pow_p_bijOn`: with $\operatorname{mod}_K(p)=q^{-c}$ ($c\ge1$), for all large $N$ the map $x\mapsto x^p$ is a
  bijection of $1+P^N$ onto $1+P^{N+c}$ (Weil's binomial estimate (3)).
* `zpModule_finite`: $1+P$ is a finitely generated $\mathbb Z_p$-module.
* **`weil_II_3_prop9`**: $1+P\cong\mathbb Z_p^d\times\mathbb Z_p/p^m\mathbb Z_p$ as $\mathbb Z_p$-modules, where
  $p^d=\operatorname{mod}_K(p)^{-1}$ (so $d=[K:\mathbb Q_p]$, and $\mathbb Z_p^d\cong R$ by II.§2, Thm. 1, as Weil notes
  on p. 33) and $m$ is the largest integer such that $K$ contains a primitive $p^m$-th root of $1$.
* **`weil_II_3_prop9_cor`**: for $n\ge1$, $(K^\times)^n$ is open, of finite index $n\,(n,r)\,\operatorname{mod}_K(n)^{-1}$
  in $K^\times$, $r$ the (finite) number of roots of $1$ in $K$.
-/

open Topology Filter
open scoped NNReal Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

/-- **Topological Nakayama lemma** for $\mathbb Z_p$: a compact Hausdorff topological $\mathbb Z_p$-module in which
$pM$ is open is finitely generated. -/
theorem zp_module_finite_of_compact {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    [TopologicalSpace M] [CompactSpace M] [T2Space M] [IsTopologicalAddGroup M]
    (hcont : Continuous fun q : ℤ_[p] × M => q.1 • q.2)
    (hopen : IsOpen (((p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] M) : Submodule ℤ_[p] M) : Set M)) :
    Module.Finite ℤ_[p] M := by
  classical
  set P : Set M := (((p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] M) : Submodule ℤ_[p] M) : Set M) with hP
  have hP0 : (0 : M) ∈ P := Submodule.zero_mem _
  -- finitely many cosets of `pM` cover `M`
  obtain ⟨t, -, hcover⟩ := isCompact_univ.elim_nhds_subcover (fun x : M => {y | y - x ∈ P})
    (fun x _ => (hopen.preimage (continuous_id.sub continuous_const)).mem_nhds (by simpa using hP0))
  have hspan : ∀ x : M, ∃ s ∈ t, x - s ∈ P := fun x => by
    have := hcover (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨s, hs, hxs⟩ := this
    exact ⟨s, hs, hxs⟩
  set N : Submodule ℤ_[p] M := Submodule.span ℤ_[p] (t : Set M) with hNdef
  -- `N` is closed: image of a compact set
  have hNclosed : IsClosed (N : Set M) := by
    let v : t → M := fun i => (i : M)
    have hN : (N : Set M) = Set.range (Fintype.linearCombination ℤ_[p] v) := by
      have h1 : Submodule.span ℤ_[p] (Set.range v) = N := by
        rw [hNdef]; congr 1; ext x; simp [v]
      rw [← h1, ← Fintype.range_linearCombination]; rfl
    rw [hN]
    have hc : Continuous (Fintype.linearCombination ℤ_[p] v) := by
      have : (Fintype.linearCombination ℤ_[p] v : (t → ℤ_[p]) → M) = fun c => ∑ i, c i • v i := by
        funext c; rfl
      rw [this]
      exact continuous_finsetSum _ fun i _ =>
        hcont.comp (f := fun c : t → ℤ_[p] => (c i, v i)) ((continuous_apply i).prodMk continuous_const)
    exact (isCompact_range hc).isClosed
  have hstep : ∀ k : ℕ, ∀ m : M, ∃ n ∈ N, ∃ x : M, m = n + (p : ℤ_[p]) ^ k • x := by
    intro k
    induction k with
    | zero => intro m; exact ⟨0, N.zero_mem, m, by simp⟩
    | succ k ih =>
      intro m
      obtain ⟨n, hn, x, rfl⟩ := ih m
      obtain ⟨s, hs, hxs⟩ := hspan x
      obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hxs
      have hx : x = s + (p : ℤ_[p]) • y := by rw [hy]; abel
      refine ⟨n + (p : ℤ_[p]) ^ k • s, N.add_mem hn (N.smul_mem _ (Submodule.subset_span hs)), y, ?_⟩
      rw [hx, smul_add, smul_smul, ← pow_succ]
      abel
  have hsmall : ∀ W ∈ 𝓝 (0 : M), ∃ k : ℕ, ∀ x : M, (p : ℤ_[p]) ^ k • x ∈ W := by
    intro W hW
    have hO : IsOpen {q : ℤ_[p] × M | q.1 • q.2 ∈ interior W} :=
      isOpen_interior.preimage hcont
    obtain ⟨u, v, hu, -, hu0, hv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : ℤ_[p])))
      isCompact_univ hO (by
        rintro ⟨a, x⟩ ⟨ha, -⟩
        have ha' : a = 0 := ha
        subst ha'
        show (0 : ℤ_[p]) • x ∈ interior W
        rw [zero_smul]
        exact mem_interior_iff_mem_nhds.2 hW)
    have ht : Tendsto (fun k : ℕ => (p : ℤ_[p]) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
        rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))
    obtain ⟨k, hk⟩ := (ht.eventually (hu.mem_nhds (hu0 rfl))).exists
    refine ⟨k, fun x => interior_subset (huv (Set.mk_mem_prod hk (hv (Set.mem_univ x))))⟩
  have hmem : ∀ m : M, m ∈ N := by
    intro m
    have : m ∈ closure (N : Set M) := by
      rw [mem_closure_iff_nhds]
      intro s hs
      have hW : (fun y => m - y) ⁻¹' s ∈ 𝓝 (0 : M) :=
        (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds (by simpa using hs)
      obtain ⟨k, hk⟩ := hsmall _ hW
      obtain ⟨n, hn, x, hm⟩ := hstep k m
      refine ⟨n, ?_, hn⟩
      have := hk x
      simp only [Set.mem_preimage] at this
      have e : m - (p : ℤ_[p]) ^ k • x = n := by rw [hm]; abel
      rwa [e] at this
    rwa [hNclosed.closure_eq] at this
  exact ⟨⟨t, eq_top_iff.2 fun m _ => hmem m⟩⟩

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot] {p : ℕ} [hp : Fact p.Prime]

theorem modK_mul_sub_one_le (hK : IsPField K p) {a b : K} {e : ℝ≥0} (he : e < 1)
    (ha : modK K (a - 1) ≤ e) (hb : modK K (b - 1) ≤ e) : modK K (a * b - 1) ≤ e := by
  have h1 := modK_eq_one_of_op hK (lt_of_le_of_lt ha he)
  have eq : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  rw [eq]
  refine (isUltrametricMod_of_isPField hK _ _).trans (max_le ?_ ha)
  rw [modK_mul, h1, one_mul]; exact hb

theorem geom_sum_close_le (hK : IsPField K p) {N : ℕ} {x x' : K} (hx : modK K (x - 1) ≤ qi hK ^ N)
    (hx' : modK K (x' - 1) ≤ qi hK ^ N) (hN : 1 ≤ N) :
    modK K ((∑ i ∈ Finset.range p, x ^ i * x' ^ (p - 1 - i)) - p) ≤ qi hK ^ N := by
  have hlt : qi hK ^ N < 1 := pow_lt_one₀ zero_le (qi_lt_one hK) (by omega)
  have e : (∑ i ∈ Finset.range p, x ^ i * x' ^ (p - 1 - i)) - p =
      ∑ i ∈ Finset.range p, (x ^ i * x' ^ (p - 1 - i) - 1) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [e]
  exact modK_sum_le hK _ _ fun i _ => modK_mul_sub_one_le hK hlt (modK_pow_sub_one_le hK hlt hx i)
    (modK_pow_sub_one_le hK hlt hx' _)

theorem modK_pow_p_sub (hK : IsPField K p) {c N : ℕ} (hmp : modK K (p : K) = qi hK ^ c) (hcN : c < N)
    {x x' : K} (hx : modK K (x - 1) ≤ qi hK ^ N) (hx' : modK K (x' - 1) ≤ qi hK ^ N) :
    modK K (x ^ p - x' ^ p) = qi hK ^ c * modK K (x - x') := by
  have hS := geom_sum_close_le hK hx hx' (by omega)
  have hSn : modK K (∑ i ∈ Finset.range p, x ^ i * x' ^ (p - 1 - i)) = qi hK ^ c := by
    have h := modK_add_eq_of_lt (isUltrametricMod_of_isPField hK) (x := (p : K))
      (y := (∑ i ∈ Finset.range p, x ^ i * x' ^ (p - 1 - i)) - p)
      (by rw [hmp]; exact lt_of_le_of_lt hS (pow_lt_pow_right_of_lt_one₀ (qi_pos hK) (qi_lt_one hK) hcN))
    rw [add_sub_cancel, hmp] at h
    exact h
  rw [← geom_sum₂_mul, modK_mul, hSn]

theorem modK_div_p_le (hK : IsPField K p) {c M : ℕ} (hmp : modK K (p : K) = qi hK ^ c)
    (hp0 : (p : K) ≠ 0) {w : K} (hw : modK K w ≤ qi hK ^ (M + c)) : modK K (w / p) ≤ qi hK ^ M := by
  rw [div_eq_mul_inv, modK_mul, modK_inv hp0, hmp]
  calc modK K w * (qi hK ^ c)⁻¹ ≤ qi hK ^ (M + c) * (qi hK ^ c)⁻¹ := by gcongr
    _ = qi hK ^ M := by rw [pow_add]; exact mul_inv_cancel_right₀ (pow_ne_zero c (qi_pos hK).ne') _

/-- Contraction estimate for the Newton step $z\mapsto z-(z^p-y)/p$. -/
theorem newton_contract_p (hK : IsPField K p) {c N : ℕ} (hmp : modK K (p : K) = qi hK ^ c)
    (hp0 : (p : K) ≠ 0) (hcN : c < N) (y : K) {z z' : K} (hz : modK K (z - 1) ≤ qi hK ^ N)
    (hz' : modK K (z' - 1) ≤ qi hK ^ N) :
    modK K ((z - (z ^ p - y) / p) - (z' - (z' ^ p - y) / p)) ≤ qi hK * modK K (z - z') := by
  set S := ∑ i ∈ Finset.range p, z ^ i * z' ^ (p - 1 - i) with hSdef
  have hS : z ^ p = z' ^ p + S * (z - z') := by
    have := geom_sum₂_mul z z' p
    rw [← hSdef] at this
    linear_combination -this
  have e : (z - (z ^ p - y) / p) - (z' - (z' ^ p - y) / p) = (z - z') * (((p : K) - S) / p) := by
    rw [hS]; field_simp; ring
  rw [e, modK_mul, mul_comm]
  refine mul_le_mul' ?_ le_rfl
  have h1 := geom_sum_close_le hK hz hz' (by omega)
  rw [← hSdef, ← modK_neg, neg_sub] at h1
  have := modK_div_p_le hK hmp hp0 (M := N - c) (w := (p : K) - S)
    (by rwa [Nat.sub_add_cancel hcN.le])
  refine this.trans ?_
  calc qi hK ^ (N - c) ≤ qi hK ^ 1 :=
        pow_le_pow_of_le_one zero_le (qi_lt_one hK).le (by omega)
    _ = qi hK := pow_one _

/-- Weil's estimate (3), in the form used here: with $\operatorname{mod}_K(p)=q^{-c}$, for $N$ large
$x\mapsto x^p$ maps $1+P^N$ bijectively onto $1+P^{N+c}$. -/
theorem exists_pow_p_bijOn [CharZero K] (hK : IsPField K p) :
    ∃ c N₀ : ℕ, 1 ≤ c ∧ modK K (p : K) = qi hK ^ c ∧
      ∀ N ≥ N₀, Set.BijOn (fun x : K => x ^ p) (onePlusP hK N) (onePlusP hK (N + c)) := by
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hK.1.ne_zero
  obtain ⟨n, hn⟩ := weil_I_4_thm6_range hK hp0
  have hq : (1 : ℝ≥0) < (pq hK : ℝ≥0) := by exact_mod_cast one_lt_pq_nat hK
  have hn' : n < 0 := by
    by_contra hc
    push Not at hc
    have : (1 : ℝ≥0) ≤ (pq hK : ℝ≥0) ^ n := one_le_zpow₀ hq.le hc
    rw [← hn] at this
    exact absurd hK.2 (not_lt.2 this)
  obtain ⟨c, rfl⟩ : ∃ c : ℕ, n = -(c : ℤ) := ⟨n.natAbs, by omega⟩
  have hc1 : 1 ≤ c := by omega
  have hmp : modK K (p : K) = qi hK ^ c := by
    rw [hn, zpow_neg, zpow_natCast, qi, inv_pow]
  refine ⟨c, c + 1, hc1, hmp, fun N hN => ?_⟩
  have hcN : c < N := by omega
  have hlt : qi hK ^ N < 1 := pow_lt_one₀ zero_le (qi_lt_one hK) (by omega)
  have hone : (1 : K) ∈ onePlusP hK N := by
    rw [mem_onePlusP, sub_self, modK_zero']; exact zero_le
  have hmaps : ∀ x ∈ onePlusP hK N, x ^ p ∈ onePlusP hK (N + c) := by
    intro x hx
    rw [mem_onePlusP] at hx ⊢
    have h := modK_pow_p_sub hK hmp hcN hx (x' := 1) (by rw [sub_self, modK_zero']; exact zero_le)
    rw [one_pow] at h
    rw [h, pow_add, mul_comm (qi hK ^ N)]
    exact mul_le_mul' le_rfl hx
  refine ⟨hmaps, fun x hx x' hx' h => ?_, fun y hy => ?_⟩
  · have h' : x ^ p = x' ^ p := h
    have := modK_pow_p_sub hK hmp hcN (mem_onePlusP.1 hx) (mem_onePlusP.1 hx')
    rw [h', sub_self, modK_zero'] at this
    have h0 : modK K (x - x') = 0 := by
      rcases mul_eq_zero.1 this.symm with h | h
      · exact absurd h (pow_ne_zero c (qi_pos hK).ne')
      · exact h
    exact sub_eq_zero.1 (modK_eq_zero_iff.1 h0)
  · rw [mem_onePlusP] at hy
    let T : K → K := fun z => z - (z ^ p - y) / p
    let a : ℕ → K := fun k => Nat.rec (motive := fun _ => K) 1 (fun _ z => T z) k
    have ha0 : a 0 = 1 := rfl
    have ha_succ : ∀ k, a (k + 1) = T (a k) := fun k => rfl
    have hbound : ∀ z : K, modK K (z - 1) ≤ qi hK ^ N → modK K ((z ^ p - y) / p) ≤ qi hK ^ N := by
      intro z hz
      refine modK_div_p_le hK hmp hp0 ?_
      have h1 := modK_pow_p_sub hK hmp hcN hz (x' := 1) (by rw [sub_self, modK_zero']; exact zero_le)
      rw [one_pow] at h1
      have h2 : modK K (z ^ p - 1) ≤ qi hK ^ (N + c) := by
        rw [h1, pow_add, mul_comm (qi hK ^ N)]; exact mul_le_mul' le_rfl hz
      have e : z ^ p - y = (z ^ p - 1) - (y - 1) := by ring
      rw [e]; exact (modK_sub_le_max hK _ _).trans (max_le h2 hy)
    have hmem : ∀ k, modK K (a k - 1) ≤ qi hK ^ N := by
      intro k
      induction k with
      | zero => rw [ha0, sub_self, modK_zero']; exact zero_le
      | succ k ih =>
        rw [ha_succ]
        have e2 : T (a k) - 1 = (a k - 1) - ((a k) ^ p - y) / p := by simp only [T]; ring
        rw [e2]
        exact (modK_sub_le_max hK _ _).trans (max_le ih (hbound _ ih))
    have hstep : ∀ k, modK K (a (k + 1) - a k) ≤ qi hK ^ k := by
      intro k
      induction k with
      | zero =>
        have e : a (0 + 1) - a 0 = -((a 0 ^ p - y) / p) := by rw [ha_succ]; simp only [T]; ring
        rw [e, modK_neg]
        exact (hbound _ (hmem 0)).trans (by rw [pow_zero]; exact hlt.le)
      | succ k ih =>
        have h := newton_contract_p hK hmp hp0 hcN y (hmem (k + 1)) (hmem k)
        show modK K (T (a (k + 1)) - T (a k)) ≤ qi hK ^ (k + 1)
        refine h.trans ?_
        rw [pow_succ']
        exact mul_le_mul' le_rfl ih
    obtain ⟨L, hL⟩ := exists_tendsto_of_step hK hstep
    have hLmem : L ∈ onePlusP hK N := by
      have hcl : IsClosed (onePlusP hK N) := by
        have : onePlusP hK N = {x | modK K (x - 1) ≤ qi hK ^ N} := by
          ext x; exact mem_onePlusP
        rw [this]
        exact isClosed_le (continuous_modK.comp (continuous_id.sub continuous_const)) continuous_const
      exact hcl.mem_of_tendsto hL (Eventually.of_forall fun k => mem_onePlusP.2 (hmem k))
    refine ⟨L, hLmem, ?_⟩
    show L ^ p = y
    have h1 : Tendsto (fun k => a k ^ p - y) atTop (𝓝 (L ^ p - y)) :=
      (((continuous_pow p).tendsto L).comp hL).sub tendsto_const_nhds
    have h2 : Tendsto (fun k => a k - a (k + 1)) atTop (𝓝 0) := by
      simpa using hL.sub (hL.comp (tendsto_add_atTop_nat 1))
    have h3 : Tendsto (fun k => (p : K) * (a k - a (k + 1))) atTop (𝓝 0) := by
      simpa using h2.const_mul (p : K)
    have h4 : (fun k => a k ^ p - y) = fun k => (p : K) * (a k - a (k + 1)) := by
      funext k; rw [ha_succ]; simp only [T]; field_simp; ring
    rw [h4] at h1
    exact sub_eq_zero.1 (tendsto_nhds_unique h1 h3)

/-- $1+P$ is a finitely generated $\mathbb Z_p$-module (characteristic $0$). -/
theorem zpModule_finite [CharZero K] (hK : IsPField K p) :
    Module.Finite ℤ_[p] (Additive (onePlusPUnits hK)) := by
  obtain ⟨c, N₀, hc1, hmp, hbij⟩ := exists_pow_p_bijOn hK
  let e : onePlusPUnits hK → K := fun g => ((g : Kˣ) : K)
  have hemb : Topology.IsEmbedding e :=
    Units.isEmbedding_val₀.comp Topology.IsEmbedding.subtypeVal
  have hrange : Set.range e = onePlusP hK 1 := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact mem_onePlusP.2 (by simpa using modK_le_qi_of_lt_one hK g.2)
    · intro hx
      have hx' := op_of_mem hK le_rfl hx
      have hx1 := modK_eq_one_of_op hK hx'
      have hx0 : x ≠ 0 := fun h => by rw [h, modK_zero'] at hx1; exact zero_ne_one hx1
      exact ⟨⟨Units.mk0 x hx0, hx'⟩, rfl⟩
  have hcl : IsClosed (onePlusP hK 1) := by
    have : onePlusP hK 1 = {x | modK K (x - 1) ≤ qi hK ^ 1} := by
      ext x; exact mem_onePlusP
    rw [this]
    exact isClosed_le (continuous_modK.comp (continuous_id.sub continuous_const)) continuous_const
  have hcomp : CompactSpace (onePlusPUnits hK) := by
    rw [← isCompact_univ_iff, hemb.isCompact_iff, Set.image_univ, hrange]
    refine (weil_I_4_thm6_isCompact hK).of_isClosed_subset hcl fun x hx => ?_
    exact mem_pR.2 (modK_eq_one_of_op hK (op_of_mem hK le_rfl hx)).le
  have hcont : Continuous fun q : ℤ_[p] × Additive (onePlusPUnits hK) => q.1 • q.2 := by
    have h1 : Continuous fun q : ℤ_[p] × Additive (onePlusPUnits hK) =>
        (zpPow hK q.1 q.2.toMul : onePlusPUnits hK) :=
      hemb.continuous_iff.2 (by
        have := (continuous_zpPow hK).comp
          (continuous_fst.prodMk (continuous_toMul.comp continuous_snd) :
            Continuous fun q : ℤ_[p] × Additive (onePlusPUnits hK) => (q.1, q.2.toMul))
        exact this)
    exact continuous_ofMul.comp h1
  have : T2Space (onePlusPUnits hK) := hemb.t2Space
  have : T2Space (Additive (onePlusPUnits hK)) := inferInstanceAs (T2Space (onePlusPUnits hK))
  have : IsTopologicalAddGroup (Additive (onePlusPUnits hK)) :=
    { continuous_add := continuous_ofMul.comp
        ((continuous_toMul.comp continuous_fst).mul (continuous_toMul.comp continuous_snd))
      continuous_neg := continuous_ofMul.comp (continuous_toMul.inv) }
  refine zp_module_finite_of_compact hcont ?_
  set H : Submodule ℤ_[p] (Additive (onePlusPUnits hK)) :=
    (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] (Additive (onePlusPUnits hK))) with hH
  have hN1 : 1 ≤ max N₀ 1 := le_max_right _ _
  have hsub : ∀ x : onePlusPUnits hK, modK K (e x - 1) ≤ qi hK ^ (max N₀ 1 + c) →
      Additive.ofMul x ∈ H := by
    intro x hx
    obtain ⟨x', hx', hxx'⟩ := (hbij (max N₀ 1) (le_max_left _ _)).surjOn (mem_onePlusP.2 hx)
    have hx'1 := op_of_mem hK hN1 hx'
    have hm1 := modK_eq_one_of_op hK hx'1
    have hx'0 : x' ≠ 0 := fun h => by rw [h, modK_zero'] at hm1; exact zero_ne_one hm1
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
      ⟨Additive.ofMul (⟨Units.mk0 x' hx'0, hx'1⟩ : onePlusPUnits hK), Submodule.mem_top, ?_⟩
    change Additive.ofMul (zpPow hK (p : ℤ_[p]) (⟨Units.mk0 x' hx'0, hx'1⟩ : onePlusPUnits hK)) =
      Additive.ofMul x
    rw [zpPow_natCast]
    congr 1
    apply onePlusPUnits_ext
    simpa using hxx'
  have hW : IsOpen {g : Additive (onePlusPUnits hK) |
      modK K (e g.toMul - 1) < qi hK ^ (max N₀ 1 + c)} :=
    isOpen_lt (continuous_modK.comp ((hemb.continuous.comp continuous_toMul).sub continuous_const))
      continuous_const
  have h0 : (0 : Additive (onePlusPUnits hK)) ∈ {g : Additive (onePlusPUnits hK) |
      modK K (e g.toMul - 1) < qi hK ^ (max N₀ 1 + c)} := by
    show modK K (e 1 - 1) < _
    have : e 1 = 1 := rfl
    rw [this, sub_self, modK_zero']
    exact pow_pos (qi_pos hK) _
  have := AddSubgroup.isOpen_of_mem_nhds H.toAddSubgroup
    (Filter.mem_of_superset (hW.mem_nhds h0) fun g hg => hsub g.toMul hg.le)
  exact this

/-- The subgroup $p\,\mathbb Z_p^d$ of $\mathbb Z_p^d$ has index $p^d$. -/
theorem index_range_smul_p_pi (d : ℕ) :
    (DistribSMul.toAddMonoidHom (Fin d → ℤ_[p]) (p : ℤ_[p])).range.index = p ^ d := by
  let Ψ : (Fin d → ℤ_[p]) →+ (Fin d → ZMod p) :=
    { toFun := fun f i => PadicInt.toZMod (f i)
      map_zero' := by ext; simp
      map_add' := by intro f g; ext; simp }
  have hker : Ψ.ker = (DistribSMul.toAddMonoidHom (Fin d → ℤ_[p]) (p : ℤ_[p])).range := by
    ext f
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro h
      have hd : ∀ i, (p : ℤ_[p]) ∣ f i := fun i => by
        have h1 : PadicInt.toZMod (f i) = 0 := congrFun h i
        have : f i ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := h1
        rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
        exact this
      choose g hg using hd
      exact ⟨g, by ext i; simp [hg i]⟩
    · rintro ⟨g, rfl⟩
      ext i
      have : PadicInt.toZMod ((p : ℤ_[p]) * g i) = 0 := by
        rw [map_mul]; simp
      simp [Ψ]
  have hsurj : Function.Surjective Ψ := by
    intro g
    have hs := ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[p] →+* ZMod p)
    exact ⟨fun i => (hs (g i)).choose, by ext i; exact (hs (g i)).choose_spec⟩
  rw [← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top_of_surjective _ hsurj]
  simp [Nat.card_eq_fintype_card]

/-- Core index computation: if $V\cap T=0$, $V$ has finite index, $pV\le V$ and $M/T\cong\mathbb Z_p^d$, then
$[V:pV]=p^d$. -/
theorem relIndex_smul_p_eq {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] (T : Submodule ℤ_[p] M)
    {d : ℕ} (e : (M ⧸ T) ≃ₗ[ℤ_[p]] (Fin d → ℤ_[p]))
    (V : AddSubgroup M) (hVT : V ⊓ T.toAddSubgroup = ⊥) (hV : V.index ≠ 0)
    (hV' : V.map (DistribSMul.toAddMonoidHom M (p : ℤ_[p])) ≤ V) :
    (V.map (DistribSMul.toAddMonoidHom M (p : ℤ_[p]))).relIndex V = p ^ d := by
  set φ := DistribSMul.toAddMonoidHom M (p : ℤ_[p]) with hφ
  set φF := DistribSMul.toAddMonoidHom (M ⧸ T) (p : ℤ_[p]) with hφF
  let π : M →+ (M ⧸ T) := T.mkQ.toAddMonoidHom
  have hp0 : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hφF : Function.Injective φF := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : (p : ℤ_[p]) • x = 0 := hx
    have h2 : (p : ℤ_[p]) • e x = 0 := by rw [← map_smul, h1, map_zero]
    rcases smul_eq_zero.1 h2 with h | h
    · exact absurd h hp0
    · exact e.injective (by rw [h, map_zero])
  let ψ : V →+ (M ⧸ T) := π.comp V.subtype
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : (x : M) ∈ T := by
      have : π (x : M) = 0 := hx
      exact (Submodule.Quotient.mk_eq_zero T).1 this
    have h2 : (x : M) ∈ V ⊓ T.toAddSubgroup := ⟨x.2, h1⟩
    rw [hVT] at h2
    exact Subtype.ext (AddSubgroup.mem_bot.1 h2)
  set V' := V.map φ with hV'def
  have E1 : (V'.map π).index = V'.relIndex V * (V.map π).index := by
    have h1 := AddSubgroup.index_map_of_injective (V'.addSubgroupOf V) hψ
    have h2 : (V'.addSubgroupOf V).map ψ = V'.map π := by
      have := AddSubgroup.map_addSubgroupOf_eq_of_le hV'
      show (V'.addSubgroupOf V).map (π.comp V.subtype) = _
      rw [← AddSubgroup.map_map, this]
    have h3 : ψ.range = V.map π := by
      show (π.comp V.subtype).range = _
      rw [AddMonoidHom.range_comp, AddSubgroup.range_subtype]
    rw [← h2, h1, ← h3]
    rfl
  have E2 : ((V.map π).map φF).index = (V.map π).index * φF.range.index :=
    AddSubgroup.index_map_of_injective _ hφF
  have hW' : (V.map π).map φF = V'.map π := by
    rw [AddSubgroup.map_map, hV'def, AddSubgroup.map_map]
    have hc : φF.comp π = π.comp φ := AddMonoidHom.ext fun x => by simp [φ, φF, π]
    rw [hc]
  have E3 : φF.range.index = p ^ d := by
    rw [← index_range_smul_p_pi d, ← AddSubgroup.index_map_equiv φF.range e.toAddEquiv]
    congr 1
    ext y
    simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp [φF]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨φF (e.symm x), ⟨e.symm x, rfl⟩, by simp [φF]⟩
  have E4 : (V.map π).index ≠ 0 := by
    intro h
    have := AddSubgroup.index_map_dvd (H := V) (f := π) (Submodule.mkQ_surjective T)
    rw [h] at this
    exact hV (Nat.eq_zero_of_zero_dvd this)
  have key : V'.relIndex V * (V.map π).index = (V.map π).index * p ^ d := by
    rw [← E1, ← hW', E2, E3]
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero E4) (by rw [key, mul_comm])

section Counting

/-- The value in $K$ of an element of the $\mathbb Z_p$-module $1+P$. -/
def aval (hK : IsPField K p) (x : Additive (onePlusPUnits hK)) : K := (((x.toMul : onePlusPUnits hK) : Kˣ) : K)

theorem aval_add (hK : IsPField K p) (a b : Additive (onePlusPUnits hK)) :
    aval hK (a + b) = aval hK a * aval hK b := rfl

theorem aval_zero (hK : IsPField K p) : aval hK (0 : Additive (onePlusPUnits hK)) = 1 := rfl

theorem aval_neg (hK : IsPField K p) (a : Additive (onePlusPUnits hK)) :
    aval hK (-a) = (aval hK a)⁻¹ := by simp [aval]

theorem aval_op (hK : IsPField K p) (a : Additive (onePlusPUnits hK)) : modK K (aval hK a - 1) < 1 :=
  a.toMul.2

theorem aval_ne_zero (hK : IsPField K p) (a : Additive (onePlusPUnits hK)) : aval hK a ≠ 0 :=
  Units.ne_zero _

theorem aval_inj (hK : IsPField K p) {a b : Additive (onePlusPUnits hK)} (h : aval hK a = aval hK b) :
    a = b :=
  congrArg Additive.ofMul (onePlusPUnits_ext h)

theorem aval_smul_p (hK : IsPField K p) (a : Additive (onePlusPUnits hK)) :
    aval hK ((p : ℤ_[p]) • a) = aval hK a ^ p := by
  have h : aval hK ((p : ℤ_[p]) • a) = zpPowVal hK (p : ℤ_[p]) (aval hK a) := rfl
  rw [h, zpPowVal_natCast hK (aval_op hK a)]

/-- The subgroup $1+P^j$ ($j\ge1$) of the $\mathbb Z_p$-module $1+P$. -/
def Vsub (hK : IsPField K p) (j : ℕ) (hj : 1 ≤ j) : AddSubgroup (Additive (onePlusPUnits hK)) where
  carrier := {x | modK K (aval hK x - 1) ≤ qi hK ^ j}
  add_mem' {a b} ha hb := by
    show modK K (aval hK (a + b) - 1) ≤ _
    rw [aval_add]
    exact modK_mul_sub_one_le hK (pow_lt_one₀ zero_le (qi_lt_one hK) (by omega)) ha hb
  zero_mem' := by
    show modK K (aval hK 0 - 1) ≤ _
    rw [aval_zero, sub_self, modK_zero']; exact zero_le
  neg_mem' {a} ha := by
    show modK K (aval hK (-a) - 1) ≤ _
    have h1 := modK_eq_one_of_op hK (aval_op hK a)
    have e : aval hK (-a) - 1 = -(aval hK a - 1) * (aval hK a)⁻¹ := by
      rw [aval_neg]; field_simp [aval_ne_zero hK a]; ring
    rw [e, modK_mul, modK_neg, modK_inv (aval_ne_zero hK a), h1, inv_one, mul_one]
    exact ha

theorem mem_Vsub {hK : IsPField K p} {j : ℕ} {hj : 1 ≤ j} {x : Additive (onePlusPUnits hK)} :
    x ∈ Vsub hK j hj ↔ modK K (aval hK x - 1) ≤ qi hK ^ j := Iff.rfl

theorem Vsub_one (hK : IsPField K p) : Vsub hK 1 le_rfl = ⊤ := by
  ext x
  simp only [AddSubgroup.mem_top, iff_true]
  rw [mem_Vsub, pow_one]
  exact modK_le_qi_of_lt_one hK (aval_op hK x)

theorem Vsub_antitone (hK : IsPField K p) {j : ℕ} (hj : 1 ≤ j) :
    Vsub hK (j + 1) (by omega) ≤ Vsub hK j hj := by
  intro x hx
  rw [mem_Vsub] at hx ⊢
  exact hx.trans (pow_le_pow_of_le_one zero_le (qi_lt_one hK).le (Nat.le_succ j))

/-- The additive ball $\{y:\operatorname{mod}_K(y)\le q^{-\nu}\}$. -/
def ballAddZp (hK : IsPField K p) (ν : ℕ) : AddSubgroup K where
  carrier := {y | modK K y ≤ qi hK ^ ν}
  add_mem' {a b} ha hb := (isUltrametricMod_of_isPField hK a b).trans (max_le ha hb)
  zero_mem' := by show modK K 0 ≤ _; rw [modK_zero']; exact zero_le
  neg_mem' {a} ha := by show modK K (-a) ≤ _; rw [modK_neg]; exact ha

theorem mem_ballAdd {hK : IsPField K p} {ν : ℕ} {y : K} : y ∈ ballAddZp hK ν ↔ modK K y ≤ qi hK ^ ν :=
  Iff.rfl

theorem relIndex_ballAdd_zero (hK : IsPField K p) :
    (ballAddZp hK 1).relIndex (ballAddZp hK 0) = pq hK := by
  let eR : ↥(ballAddZp hK 0) ≃+ ↥(pR hK) :=
    { toFun := fun x => ⟨x.1, mem_pR.2 (by
        have h : modK K x.1 ≤ qi hK ^ 0 := x.2
        simpa using h)⟩
      invFun := fun x => ⟨x.1, by simpa [mem_ballAdd] using mem_pR.1 x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun _ _ => rfl }
  have h : ((ballAddZp hK 1).addSubgroupOf (ballAddZp hK 0)).map (eR : ↥(ballAddZp hK 0) →+ ↥(pR hK)) =
      pPAdd hK := by
    ext x
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : modK K y.1 ≤ qi hK ^ 1 := hy
      show modK K y.1 < 1
      exact lt_of_le_of_lt (by simpa using this) (qi_lt_one hK)
    · intro hx
      refine ⟨eR.symm x, ?_, eR.apply_symm_apply x⟩
      show modK K x.1 ≤ qi hK ^ 1
      rw [pow_one]; exact modK_le_qi_of_lt_one hK hx
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_map_equiv _ eR, h]
  rfl

theorem relIndex_ballAdd (hK : IsPField K p) (j : ℕ) :
    (ballAddZp hK (j + 1)).relIndex (ballAddZp hK j) = pq hK := by
  obtain ⟨π, hπ0, hP, -⟩ := weil_I_4_thm6_prime hK
  have hmπ : modK K π = qi hK := weil_I_4_thm6_modK_prime hK hπ0 hP
  let f : K →+ K := AddMonoidHom.mulLeft (π ^ j)
  have hf : Function.Injective f := mul_right_injective₀ (pow_ne_zero j hπ0)
  have hj0 : qi hK ^ j ≠ 0 := pow_ne_zero j (qi_pos hK).ne'
  have hmap : ∀ ν, (ballAddZp hK ν).map f = ballAddZp hK (ν + j) := by
    intro ν
    ext y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      show modK K (π ^ j * z) ≤ _
      rw [modK_mul, modK_pow, hmπ, pow_add, mul_comm (qi hK ^ ν)]
      exact mul_le_mul' le_rfl hz
    · intro hy
      have hy' : modK K y ≤ qi hK ^ (ν + j) := hy
      refine ⟨(π ^ j)⁻¹ * y, ?_, mul_inv_cancel_left₀ (pow_ne_zero j hπ0) y⟩
      show modK K ((π ^ j)⁻¹ * y) ≤ _
      rw [modK_mul, modK_inv (pow_ne_zero j hπ0), modK_pow, hmπ]
      calc (qi hK ^ j)⁻¹ * modK K y ≤ (qi hK ^ j)⁻¹ * qi hK ^ (ν + j) := by gcongr
        _ = qi hK ^ ν := by rw [pow_add, mul_comm (qi hK ^ ν), inv_mul_cancel_left₀ hj0]
  have h1 := hmap 1
  have h0 := hmap 0
  rw [zero_add] at h0
  rw [add_comm 1 j] at h1
  rw [← h1, ← h0, AddSubgroup.relIndex_map_map_of_injective _ _ hf]
  exact relIndex_ballAdd_zero hK

theorem relIndex_Vsub (hK : IsPField K p) {j : ℕ} (hj : 1 ≤ j) :
    (Vsub hK (j + 1) (by omega)).relIndex (Vsub hK j hj) = pq hK := by
  set H := (ballAddZp hK (j + 1)).addSubgroupOf (ballAddZp hK j) with hH
  have hjq : qi hK ^ j * qi hK ^ j ≤ qi hK ^ (j + 1) := by
    rw [← pow_add]; exact pow_le_pow_of_le_one zero_le (qi_lt_one hK).le (by omega)
  let χ : Vsub hK j hj →+ (↥(ballAddZp hK j) ⧸ H) :=
    { toFun := fun x => QuotientAddGroup.mk ⟨aval hK x.1 - 1, x.2⟩
      map_zero' := by
        have : (⟨aval hK ((0 : Vsub hK j hj) : Additive (onePlusPUnits hK)) - 1,
            (0 : Vsub hK j hj).2⟩ : ↥(ballAddZp hK j)) = 0 := Subtype.ext (by simp [aval_zero])
        exact congrArg QuotientAddGroup.mk this
      map_add' := fun a b => by
        show QuotientAddGroup.mk _ = QuotientAddGroup.mk _ + QuotientAddGroup.mk _
        rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq, hH, AddSubgroup.mem_addSubgroupOf]
        change modK K (-(aval hK (a.1 + b.1) - 1) + ((aval hK a.1 - 1) + (aval hK b.1 - 1))) ≤ _
        have e : -(aval hK (a.1 + b.1) - 1) + ((aval hK a.1 - 1) + (aval hK b.1 - 1)) =
            -((aval hK a.1 - 1) * (aval hK b.1 - 1)) := by rw [aval_add]; ring
        rw [e, modK_neg, modK_mul]
        exact (mul_le_mul' a.2 b.2).trans hjq }
  have hker : χ.ker = (Vsub hK (j + 1) (by omega)).addSubgroupOf (Vsub hK j hj) := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    show QuotientAddGroup.mk _ = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff, hH, AddSubgroup.mem_addSubgroupOf]
    rfl
  have hsurj : Function.Surjective χ := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | _ y =>
      obtain ⟨y, hy⟩ := y
      have hy' : modK K y ≤ qi hK ^ j := hy
      have hlt : modK K ((1 + y) - 1) < 1 := by
        rw [add_sub_cancel_left]
        exact lt_of_le_of_lt hy' (pow_lt_one₀ zero_le (qi_lt_one hK) (by omega))
      have h1 := modK_eq_one_of_op hK hlt
      have h0 : (1 + y) ≠ 0 := fun h => by rw [h, modK_zero'] at h1; exact zero_ne_one h1
      let x : Additive (onePlusPUnits hK) := Additive.ofMul ⟨Units.mk0 (1 + y) h0, hlt⟩
      have hx : aval hK x = 1 + y := rfl
      have hxm : x ∈ Vsub hK j hj := by
        show modK K (aval hK x - 1) ≤ _
        rw [hx, add_sub_cancel_left]; exact hy'
      refine ⟨⟨x, hxm⟩, ?_⟩
      show QuotientAddGroup.mk _ = QuotientAddGroup.mk _
      congr 1
      exact Subtype.ext (by show aval hK x - 1 = y; rw [hx, add_sub_cancel_left])
  unfold AddSubgroup.relIndex
  rw [← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top_of_surjective χ hsurj,
    AddSubgroup.card_top, ← AddSubgroup.index_eq_card]
  exact relIndex_ballAdd hK j

theorem index_Vsub (hK : IsPField K p) (k : ℕ) :
    (Vsub hK (k + 1) (by omega)).index = pq hK ^ k := by
  induction k with
  | zero => simp [Vsub_one]
  | succ k ih =>
    have h := AddSubgroup.relIndex_mul_index (Vsub_antitone hK (j := k + 1) (by omega))
    rw [relIndex_Vsub hK (by omega), ih] at h
    rw [← h, pow_succ, mul_comm]

theorem Vsub_mono (hK : IsPField K p) {j j' : ℕ} (hj : 1 ≤ j) (hj' : 1 ≤ j') (h : j ≤ j') :
    Vsub hK j' hj' ≤ Vsub hK j hj := by
  intro x hx
  rw [mem_Vsub] at hx ⊢
  exact hx.trans (pow_le_pow_of_le_one zero_le (qi_lt_one hK).le h)

/-- The element of $1+P$ with prescribed value in $K$. -/
def ofK (hK : IsPField K p) (x : K) (h : modK K (x - 1) < 1) : Additive (onePlusPUnits hK) :=
  Additive.ofMul ⟨Units.mk0 x (fun h0 => by
    have h1 := modK_eq_one_of_op hK h
    rw [h0, modK_zero'] at h1; exact zero_ne_one h1), h⟩

theorem aval_ofK (hK : IsPField K p) (x : K) (h : modK K (x - 1) < 1) : aval hK (ofK hK x h) = x := rfl

theorem Vsub_map_p [CharZero K] (hK : IsPField K p) {c N₀ : ℕ}
    (hbij : ∀ N ≥ N₀, Set.BijOn (fun x : K => x ^ p) (onePlusP hK N) (onePlusP hK (N + c)))
    {N : ℕ} (hN : N₀ ≤ N) (hN1 : 1 ≤ N) :
    (Vsub hK N hN1).map (DistribSMul.toAddMonoidHom (Additive (onePlusPUnits hK)) (p : ℤ_[p])) =
      Vsub hK (N + c) (by omega) := by
  ext y
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : aval hK x ∈ onePlusP hK N := mem_onePlusP.2 hx
    have := (hbij N hN).mapsTo hx'
    show modK K (aval hK ((p : ℤ_[p]) • x) - 1) ≤ _
    rw [aval_smul_p]
    exact mem_onePlusP.1 this
  · intro hy
    have hy' : aval hK y ∈ onePlusP hK (N + c) := mem_onePlusP.2 hy
    obtain ⟨x', hx', hxx'⟩ := (hbij N hN).surjOn hy'
    have hx'1 := op_of_mem hK hN1 hx'
    refine ⟨ofK hK x' hx'1, mem_onePlusP.1 hx', ?_⟩
    apply aval_inj hK
    show aval hK ((p : ℤ_[p]) • ofK hK x' hx'1) = _
    rw [aval_smul_p, aval_ofK]
    exact hxx'

theorem Vsub_inf_torsion [CharZero K] (hK : IsPField K p) :
    ∃ N₁ : ℕ, ∀ (N : ℕ) (hN : 1 ≤ N), N₁ ≤ N →
      Vsub hK N hN ⊓ (Submodule.torsion ℤ_[p] (Additive (onePlusPUnits hK))).toAddSubgroup = ⊥ := by
  obtain ⟨N₁, hN1, h⟩ := exists_close_N hK
  refine ⟨N₁, fun N hN hNN => ?_⟩
  rw [eq_bot_iff]
  rintro x ⟨hx, hxT⟩
  rw [AddSubgroup.mem_bot]
  have hxT' : x ∈ Submodule.torsion ℤ_[p] (Additive (onePlusPUnits hK)) := hxT
  rw [Submodule.mem_torsion_iff] at hxT'
  obtain ⟨⟨a, ha⟩, hax⟩ := hxT'
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hex : ∃ a : ℤ_[p], a ≠ 0 ∧ a • Additive.ofMul x.toMul = 0 := ⟨a, ha0, hax⟩
  obtain ⟨k, hk⟩ := ((weil_II_3_prop9_torsion hK x.toMul).2).1 (((weil_II_3_prop9_torsion hK x.toMul).1).1 hex)
  have hζ : aval hK x ^ (p ^ k) = 1 := by
    have := congrArg (fun w : onePlusPUnits hK => ((w : Kˣ) : K)) hk
    simpa [aval] using this
  have hclose : modK K (aval hK x - 1) ≤ qi hK ^ N₁ :=
    (mem_Vsub.1 hx).trans (pow_le_pow_of_le_one zero_le (qi_lt_one hK).le hNN)
  exact aval_inj hK (by rw [aval_zero]; exact h _ ⟨k, hζ⟩ hclose)

theorem relIndex_Vsub_p [CharZero K] (hK : IsPField K p) {c N₀ : ℕ} (hc1 : 1 ≤ c)
    (_hbij : ∀ N ≥ N₀, Set.BijOn (fun x : K => x ^ p) (onePlusP hK N) (onePlusP hK (N + c)))
    {N : ℕ} (hN : N₀ ≤ N) (hN1 : 1 ≤ N) :
    (Vsub hK (N + c) (by omega)).relIndex (Vsub hK N hN1) = pq hK ^ c := by
  have h := AddSubgroup.relIndex_mul_index (Vsub_mono hK hN1 (by omega) (Nat.le_add_right N c))
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have e : N' + 1 + c = (N' + c) + 1 := by ring
  have h1 := index_Vsub hK N'
  have h2 := index_Vsub hK (N' + c)
  simp only [e] at h h1 h2 ⊢
  rw [h1, h2] at h
  have hq : 0 < pq hK ^ N' := pow_pos (by have := one_lt_pq_nat hK; omega) _
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  rw [h, pow_add, mul_comm]

theorem index_Vsub_ne_zero (hK : IsPField K p) {j : ℕ} (hj : 1 ≤ j) : (Vsub hK j hj).index ≠ 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [index_Vsub]
  exact pow_ne_zero _ (by have := one_lt_pq_nat hK; omega)

/-- The free part of $1+P$ has rank $d$ with $p^d=\operatorname{mod}_K(p)^{-1}$. -/
theorem exists_free_part [CharZero K] (hK : IsPField K p) :
    ∃ d : ℕ, Nonempty ((Additive (onePlusPUnits hK) ⧸
        Submodule.torsion ℤ_[p] (Additive (onePlusPUnits hK))) ≃ₗ[ℤ_[p]] (Fin d → ℤ_[p])) ∧
      (p : ℝ≥0) ^ d = (modK K (p : K))⁻¹ := by
  have hfin := zpModule_finite hK
  obtain ⟨c, N₀, hc1, hmp, hbij⟩ := exists_pow_p_bijOn hK
  obtain ⟨N₁, hN₁⟩ := Vsub_inf_torsion hK
  set N := max (max N₀ N₁) 1 with hNdef
  have hN1 : 1 ≤ N := le_max_right _ _
  have hNN₀ : N₀ ≤ N := (le_max_left _ _).trans (le_max_left _ _)
  have hNN₁ : N₁ ≤ N := (le_max_right _ _).trans (le_max_left _ _)
  let e := (Module.finBasis ℤ_[p] (Additive (onePlusPUnits hK) ⧸
    Submodule.torsion ℤ_[p] (Additive (onePlusPUnits hK)))).equivFun
  refine ⟨_, ⟨e⟩, ?_⟩
  have hmap := Vsub_map_p hK hbij hNN₀ hN1
  have core := relIndex_smul_p_eq (Submodule.torsion ℤ_[p] (Additive (onePlusPUnits hK))) e
    (Vsub hK N hN1) (hN₁ N hN1 hNN₁) (index_Vsub_ne_zero hK hN1)
    (by rw [hmap]; exact Vsub_mono hK hN1 (by omega) (Nat.le_add_right N c))
  rw [hmap, relIndex_Vsub_p hK hc1 hbij hNN₀ hN1] at core
  have h1 : (p : ℝ≥0) ^ (Module.finrank ℤ_[p] (Additive (onePlusPUnits hK) ⧸
      Submodule.torsion ℤ_[p] (Additive (onePlusPUnits hK)))) = (pq hK : ℝ≥0) ^ c := by
    exact_mod_cast core.symm
  rw [h1, hmp, qi, inv_pow, inv_inv]

/-- If $a\neq0$ kills $x$ then $x^{p^{v(a)}}=1$. -/
theorem pow_valuation_eq_one (hK : IsPField K p) (x : Additive (onePlusPUnits hK)) {a : ℤ_[p]}
    (ha : a ≠ 0) (h : a • x = 0) : x.toMul ^ (p ^ a.valuation) = 1 := by
  set u := x.toMul
  have h' : zpPow hK a u = 1 := h
  have hspec := PadicInt.unitCoeff_spec ha
  set w : ℤ_[p]ˣ := PadicInt.unitCoeff ha
  set k := a.valuation
  have hv : zpPow hK ((p : ℤ_[p]) ^ k) u = u ^ (p ^ k) := by
    have := zpPow_natCast hK (p ^ k) u
    simpa using this
  have h3 : zpPow hK (w : ℤ_[p]) (u ^ (p ^ k)) = 1 := by
    rw [← hv, ← zpPow_mul, ← hspec]; exact h'
  have := congrArg (zpPow hK ((w⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) h3
  rw [← zpPow_mul, Units.inv_mul, zpPow_one, one_zpPow] at this
  exact this

theorem mem_torsion_iff_finOrder (hK : IsPField K p) (x : Additive (onePlusPUnits hK)) :
    x ∈ Submodule.torsion ℤ_[p] (Additive (onePlusPUnits hK)) ↔ IsOfFinOrder x.toMul := by
  rw [Submodule.mem_torsion_iff, isOfFinOrder_iff_pow_eq_one]
  constructor
  · rintro ⟨⟨a, ha⟩, hax⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    exact ((weil_II_3_prop9_torsion hK x.toMul).1).1 ⟨a, ha0, hax⟩
  · intro h
    obtain ⟨a, ha0, hax⟩ := ((weil_II_3_prop9_torsion hK x.toMul).1).2 h
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩, hax⟩

theorem torsion_equiv (hK : IsPField K p) {m : ℕ}
    (hcyc : IsCyclic (CommGroup.torsion (onePlusPUnits hK)))
    (hcard : Nat.card (CommGroup.torsion (onePlusPUnits hK)) = p ^ m) :
    Nonempty (Submodule.torsion ℤ_[p] (Additive (onePlusPUnits hK)) ≃ₗ[ℤ_[p]]
      ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m}) := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  let g' : onePlusPUnits hK := g.1
  have hord : orderOf g' = p ^ m := by
    have := orderOf_eq_card_of_forall_mem_zpowers hg
    rw [hcard] at this
    rw [← this]; exact Subgroup.orderOf_coe g
  let γ : Additive (onePlusPUnits hK) := Additive.ofMul g'
  let ℓ : ℤ_[p] →ₗ[ℤ_[p]] Additive (onePlusPUnits hK) := LinearMap.toSpanSingleton ℤ_[p] _ γ
  have hℓ : ∀ a, ℓ a = a • γ := fun a => rfl
  have hγpow : ((p : ℤ_[p]) ^ m) • γ = 0 := by
    show Additive.ofMul (zpPow hK ((p : ℤ_[p]) ^ m) g') = 0
    have : (p : ℤ_[p]) ^ m = ((p ^ m : ℕ) : ℤ_[p]) := by push_cast; rfl
    rw [this, zpPow_natCast, ← hord, pow_orderOf_eq_one]
    rfl
  have hker : LinearMap.ker ℓ = Ideal.span {(p : ℤ_[p]) ^ m} := by
    ext a
    rw [LinearMap.mem_ker, Ideal.mem_span_singleton, hℓ]
    constructor
    · intro h
      by_cases ha : a = 0
      · rw [ha]; exact dvd_zero _
      · have h1 := pow_valuation_eq_one hK γ ha h
        have h2 : orderOf g' ∣ p ^ a.valuation := orderOf_dvd_of_pow_eq_one h1
        rw [hord] at h2
        have h3 : m ≤ a.valuation := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 h2
        refine (pow_dvd_pow _ h3).trans ?_
        conv_rhs => rw [PadicInt.unitCoeff_spec ha]
        exact Dvd.intro_left _ rfl
    · rintro ⟨b, rfl⟩
      rw [mul_comm, mul_smul, hγpow]
      exact congrArg Additive.ofMul (one_zpPow hK b)
  have hγT : γ ∈ Submodule.torsion ℤ_[p] (Additive (onePlusPUnits hK)) := by
    rw [mem_torsion_iff_finOrder]
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨p ^ m, pow_pos hp.out.pos m, by
      rw [← hord]; exact pow_orderOf_eq_one g'⟩
  have hrange : LinearMap.range ℓ = Submodule.torsion ℤ_[p] (Additive (onePlusPUnits hK)) := by
    ext t
    rw [LinearMap.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      exact Submodule.smul_mem _ a hγT
    · intro ht
      rw [mem_torsion_iff_finOrder] at ht
      have hmem : t.toMul ∈ CommGroup.torsion (onePlusPUnits hK) := ht
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨t.toMul, hmem⟩)
      refine ⟨(k : ℤ_[p]), ?_⟩
      apply Additive.toMul.injective
      show zpPow hK (k : ℤ_[p]) g' = t.toMul
      rw [zpPow_intCast]
      exact congrArg Subtype.val hk
  exact ⟨(LinearEquiv.ofEq _ _ hrange).symm.trans
    ((ℓ.quotKerEquivRange).symm.trans (Submodule.quotEquivOfEq _ _ hker))⟩

end Counting

/-- Prop. 9 together with the order and cyclicity of the torsion subgroup. -/
theorem prop9_strong [CharZero K] (hK : IsPField K p) :
    ∃ d m : ℕ, (p : ℝ≥0) ^ d = (modK K (p : K))⁻¹ ∧
      Nat.card (CommGroup.torsion (onePlusPUnits hK)) = p ^ m ∧
      IsCyclic (CommGroup.torsion (onePlusPUnits hK)) ∧
      IsGreatest {k : ℕ | ∃ ζ : K, IsPrimitiveRoot ζ (p ^ k)} m ∧
      Nonempty (Additive (onePlusPUnits hK) ≃ₗ[ℤ_[p]]
        (Fin d → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m})) := by
  have hfin := zpModule_finite hK
  obtain ⟨d, ⟨e⟩, hd⟩ := exists_free_part hK
  obtain ⟨m, hcyc, hcard, hmax⟩ := weil_II_3_prop9_torsion_finite hK
  obtain ⟨eT⟩ := torsion_equiv hK hcyc hcard
  refine ⟨d, m, hd, hcard, hcyc, hmax, ?_⟩
  set T := Submodule.torsion ℤ_[p] (Additive (onePlusPUnits hK)) with hT
  obtain ⟨s, hs⟩ := Module.projective_lifting_property T.mkQ LinearMap.id
    (Submodule.mkQ_surjective T)
  have hs' : ∀ f, T.mkQ (s f) = f := fun f => LinearMap.congr_fun hs f
  let Φ : ((Additive (onePlusPUnits hK) ⧸ T) × T) →ₗ[ℤ_[p]] Additive (onePlusPUnits hK) :=
    s.coprod T.subtype
  have hΦ : Function.Bijective Φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨f, t⟩ h
      have h1 : s f + (t : Additive (onePlusPUnits hK)) = 0 := h
      have h2 : f = 0 := by
        have := congrArg T.mkQ h1
        rw [map_add, hs', map_zero] at this
        have h3 : T.mkQ (t : Additive (onePlusPUnits hK)) = 0 := (Submodule.Quotient.mk_eq_zero T).2 t.2
        rwa [h3, add_zero] at this
      subst h2
      have : (t : Additive (onePlusPUnits hK)) = 0 := by simpa using h1
      have ht0 : t = 0 := Subtype.ext this
      rw [ht0]; rfl
    · intro x
      have hmem : x - s (T.mkQ x) ∈ T := by
        rw [← Submodule.Quotient.mk_eq_zero T]
        show T.mkQ (x - s (T.mkQ x)) = 0
        rw [map_sub, hs', sub_self]
      exact ⟨(T.mkQ x, ⟨_, hmem⟩), by simp [Φ]⟩
  exact ⟨((LinearEquiv.ofBijective Φ hΦ).symm).trans (LinearEquiv.prodCongr e eT)⟩

/-- **Weil, II.§3, Prop. 9.** For a commutative $p$-field $K$ of characteristic $0$, the $\mathbb Z_p$-module $1+P$ is
isomorphic to $\mathbb Z_p^d\times\mathbb Z_p/p^m\mathbb Z_p$, where $p^d=\operatorname{mod}_K(p)^{-1}$ ($\mathbb Z_p^d\cong R$)
and $m$ is the largest integer such that $K$ contains a primitive $p^m$-th root of $1$. -/
@[kb "weil1973bnt" "Ch. II, §3, Prop. 9"]
theorem weil_II_3_prop9 [CharZero K] (hK : IsPField K p) :
    ∃ d m : ℕ, (p : ℝ≥0) ^ d = (modK K (p : K))⁻¹ ∧
      IsGreatest {k : ℕ | ∃ ζ : K, IsPrimitiveRoot ζ (p ^ k)} m ∧
      Nonempty (Additive (onePlusPUnits hK) ≃ₗ[ℤ_[p]]
        (Fin d → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m})) := by
  obtain ⟨d, m, hd, -, -, hmax, he⟩ := prop9_strong hK
  exact ⟨d, m, hd, hmax, he⟩

section CorAux

theorem index_span_pow (k : ℕ) :
    (Ideal.span {(p : ℤ_[p]) ^ k}).toAddSubgroup.index = p ^ k := by
  let f : ℤ_[p] →+ ZMod (p ^ k) := (PadicInt.toZModPow k : ℤ_[p] →+* ZMod (p ^ k)).toAddMonoidHom
  have hker : f.ker = (Ideal.span {(p : ℤ_[p]) ^ k}).toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker]
    show PadicInt.toZModPow k x = 0 ↔ _
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]; rfl
  have hsurj : Function.Surjective f := ZMod.ringHom_surjective _
  rw [← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top_of_surjective f hsurj,
    AddSubgroup.card_top]
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [Nat.card_eq_fintype_card, ZMod.card]

theorem index_range_pk_pi (d k : ℕ) :
    (DistribSMul.toAddMonoidHom (Fin d → ℤ_[p]) ((p : ℤ_[p]) ^ k)).range.index = (p ^ k) ^ d := by
  have h : (DistribSMul.toAddMonoidHom (Fin d → ℤ_[p]) ((p : ℤ_[p]) ^ k)).range =
      AddSubgroup.pi Set.univ (fun _ : Fin d => (Ideal.span {(p : ℤ_[p]) ^ k}).toAddSubgroup) := by
    ext f
    rw [AddMonoidHom.mem_range, AddSubgroup.mem_pi]
    constructor
    · rintro ⟨g, rfl⟩ i -
      show (p : ℤ_[p]) ^ k • g i ∈ Ideal.span {(p : ℤ_[p]) ^ k}
      rw [smul_eq_mul]
      exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
    · intro h
      have hd : ∀ i, ∃ g, (p : ℤ_[p]) ^ k * g = f i := fun i => by
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (h i (Set.mem_univ i))
        exact ⟨c, hc.symm⟩
      choose g hg using hd
      exact ⟨g, by ext i; simp [hg i]⟩
  rw [h, AddSubgroup.index_pi]
  simp [index_span_pow]

/-- The range of multiplication by $r$ only depends on $r$ up to a unit. -/
theorem range_smul_unit {X : Type*} [AddCommGroup X] [Module ℤ_[p] X] (a : ℤ_[p]) {u : ℤ_[p]}
    (hu : IsUnit u) :
    (DistribSMul.toAddMonoidHom X (a * u)).range = (DistribSMul.toAddMonoidHom X a).range := by
  obtain ⟨u', rfl⟩ := hu
  ext x
  simp only [AddMonoidHom.mem_range, DistribSMul.toAddMonoidHom_apply]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(u' : ℤ_[p]) • y, by rw [smul_smul, mul_comm]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨((u'⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • y, by rw [smul_smul, mul_assoc, Units.mul_inv, mul_one]⟩

theorem range_smul_prod {X Y : Type*} [AddCommGroup X] [Module ℤ_[p] X] [AddCommGroup Y]
    [Module ℤ_[p] Y] (r : ℤ_[p]) :
    (DistribSMul.toAddMonoidHom (X × Y) r).range =
      (DistribSMul.toAddMonoidHom X r).range.prod (DistribSMul.toAddMonoidHom Y r).range := by
  ext ⟨x, y⟩
  simp only [AddMonoidHom.mem_range, AddSubgroup.mem_prod, DistribSMul.toAddMonoidHom_apply]
  constructor
  · rintro ⟨⟨a, b⟩, h⟩
    exact ⟨⟨a, congrArg Prod.fst h⟩, ⟨b, congrArg Prod.snd h⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(a, b), by simp [ha, hb]⟩

theorem index_range_pk_quot (k m : ℕ) :
    (DistribSMul.toAddMonoidHom (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m})
      ((p : ℤ_[p]) ^ k)).range.index = p ^ min k m := by
  set N := Ideal.span {(p : ℤ_[p]) ^ m} with hN
  let f : ℤ_[p] →+ (ℤ_[p] ⧸ N) := (Submodule.mkQ N).toAddMonoidHom
  have hf : Function.Surjective f := Submodule.mkQ_surjective N
  have hc : (DistribSMul.toAddMonoidHom (ℤ_[p] ⧸ N) ((p : ℤ_[p]) ^ k)).range.comap f =
      (Ideal.span {(p : ℤ_[p]) ^ (min k m)}).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_comap, AddMonoidHom.mem_range]
    show (∃ y : ℤ_[p] ⧸ N, (p : ℤ_[p]) ^ k • y = Submodule.Quotient.mk x) ↔
      x ∈ Ideal.span {(p : ℤ_[p]) ^ (min k m)}
    rw [Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective N y
      have h1 : Submodule.Quotient.mk ((p : ℤ_[p]) ^ k * z) = (Submodule.Quotient.mk x : ℤ_[p] ⧸ N) := by
        rw [← hy]; rfl
      have h2 : (p : ℤ_[p]) ^ k * z - x ∈ N := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, h1, sub_self]
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 h2
      have e : x = (p : ℤ_[p]) ^ k * z - (p : ℤ_[p]) ^ m * w := by rw [← hw]; ring
      rw [e]
      exact dvd_sub (Dvd.dvd.mul_right (pow_dvd_pow _ (min_le_left _ _)) _)
        (Dvd.dvd.mul_right (pow_dvd_pow _ (min_le_right _ _)) _)
    · rintro ⟨y, rfl⟩
      rcases le_total k m with hkm | hkm
      · rw [min_eq_left hkm]
        exact ⟨Submodule.Quotient.mk y, rfl⟩
      · rw [min_eq_right hkm]
        refine ⟨0, ?_⟩
        rw [smul_zero]
        symm
        rw [Submodule.Quotient.mk_eq_zero]
        exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
  rw [← AddSubgroup.index_comap_of_surjective _ hf, hc, index_span_pow]

theorem index_pow_onePlus (hK : IsPField K p) {v n' d m : ℕ} (hn' : Nat.Coprime n' p)
    (e : Additive (onePlusPUnits hK) ≃ₗ[ℤ_[p]]
      (Fin d → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m})) :
    (powMonoidHom (p ^ v * n') : onePlusPUnits hK →* onePlusPUnits hK).range.index =
      (p ^ v) ^ d * p ^ min v m := by
  set n := p ^ v * n' with hn
  have h1 : (powMonoidHom n : onePlusPUnits hK →* onePlusPUnits hK).range.index =
      (Subgroup.toAddSubgroup (powMonoidHom n : onePlusPUnits hK →* onePlusPUnits hK).range).index :=
    Subgroup.index_toAddSubgroup.symm
  have h2 : Subgroup.toAddSubgroup (powMonoidHom n : onePlusPUnits hK →* onePlusPUnits hK).range =
      (DistribSMul.toAddMonoidHom (Additive (onePlusPUnits hK)) (n : ℤ_[p])).range := by
    ext x
    rw [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨Additive.ofMul y, ?_⟩
      show (n : ℤ_[p]) • Additive.ofMul y = x
      have : (n : ℤ_[p]) • Additive.ofMul y = Additive.ofMul (zpPow hK (n : ℤ_[p]) y) := rfl
      rw [this, zpPow_natCast]
      exact congrArg Additive.ofMul hy
    · rintro ⟨y, rfl⟩
      refine ⟨y.toMul, ?_⟩
      have : (n : ℤ_[p]) • y = Additive.ofMul (zpPow hK (n : ℤ_[p]) y.toMul) := rfl
      show y.toMul ^ n = ((n : ℤ_[p]) • y).toMul
      rw [this, zpPow_natCast]; rfl
  have hu : IsUnit (n' : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hn'.symm
  have hcast : (n : ℤ_[p]) = (p : ℤ_[p]) ^ v * (n' : ℤ_[p]) := by rw [hn]; push_cast; rfl
  have h3 : (DistribSMul.toAddMonoidHom (Additive (onePlusPUnits hK)) (n : ℤ_[p])).range =
      (DistribSMul.toAddMonoidHom (Additive (onePlusPUnits hK)) ((p : ℤ_[p]) ^ v)).range := by
    rw [hcast]; exact range_smul_unit _ hu
  have h4 := AddSubgroup.index_map_equiv
    (DistribSMul.toAddMonoidHom (Additive (onePlusPUnits hK)) ((p : ℤ_[p]) ^ v)).range e.toAddEquiv
  have h5 : AddSubgroup.map (e.toAddEquiv : _ →+ _)
      (DistribSMul.toAddMonoidHom (Additive (onePlusPUnits hK)) ((p : ℤ_[p]) ^ v)).range =
      (DistribSMul.toAddMonoidHom ((Fin d → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m}))
        ((p : ℤ_[p]) ^ v)).range := by
    ext y
    simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, DistribSMul.toAddMonoidHom_apply]
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨e z, by simp⟩
    · rintro ⟨z, rfl⟩
      exact ⟨_, ⟨e.symm z, rfl⟩, by simp⟩
  rw [h1, h2, h3, ← h4, h5, range_smul_prod, AddSubgroup.index_prod, index_range_pk_pi,
    index_range_pk_quot]

/-- The decomposition $K^\times\cong\pi^{\mathbb Z}\times M^\times\times(1+P)$ as an isomorphism of groups. -/
theorem exists_decomp_equiv (hK : IsPField K p) :
    ∃ M0 : Subgroup Kˣ, Nat.card M0 = pq hK - 1 ∧
      Nonempty (Multiplicative ℤ × M0 × onePlusPUnits hK ≃* Kˣ) := by
  obtain ⟨M0, hM0⟩ := weil_I_4_thm7_exists hK
  obtain ⟨π, hπ, hP, -⟩ := weil_I_4_thm6_prime hK
  refine ⟨M0, hM0, ?_⟩
  let f : Multiplicative ℤ × M0 × onePlusPUnits hK →* Kˣ :=
    MonoidHom.mk' (fun t => (Units.mk0 π hπ) ^ (Multiplicative.toAdd t.1) * (t.2.1 : Kˣ) * (t.2.2 : Kˣ))
      (by
        intro a b
        apply Units.ext
        simp [zpow_add₀ hπ]
        ring)
  have hdec := fun x : Kˣ => weil_II_3_text_p32 hK M0 hM0 hπ hP x x.ne_zero
  refine ⟨MulEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · rintro a b hab
    have hab' : f a = f b := hab
    have hpred : ∀ c : Multiplicative ℤ × M0 × onePlusPUnits hK, f c = f a →
        ((Multiplicative.toAdd c.1, c.2.1, ((c.2.2 : Kˣ) : K)) : ℤ × M0 × K).2.2 ∈ onePlusP hK 1 ∧
        ((f a : Kˣ) : K) = π ^ (Multiplicative.toAdd c.1) * ((c.2.1 : Kˣ) : K) * ((c.2.2 : Kˣ) : K) := by
      intro c hc
      refine ⟨mem_onePlusP.2 (by simpa using modK_le_qi_of_lt_one hK c.2.2.2), ?_⟩
      rw [← hc]
      simp [f]
    obtain ⟨t, -, ht⟩ := hdec (f a)
    have h1 := ht _ (hpred a rfl)
    have h2 := ht _ (hpred b hab'.symm)
    have h3 := h1.trans h2.symm
    simp only [Prod.mk.injEq] at h3
    obtain ⟨h31, h32, h33⟩ := h3
    refine Prod.ext (Multiplicative.toAdd.injective h31) (Prod.ext h32 ?_)
    exact onePlusPUnits_ext h33
  · intro x
    obtain ⟨⟨z, μ, w⟩, ⟨hw, hx⟩, -⟩ := hdec x
    have hw' := op_of_mem hK le_rfl hw
    have hw1 := modK_eq_one_of_op hK hw'
    have hw0 : w ≠ 0 := fun h => by rw [h, modK_zero'] at hw1; exact zero_ne_one hw1
    refine ⟨(Multiplicative.ofAdd z, μ, ⟨Units.mk0 w hw0, hw'⟩), ?_⟩
    apply Units.ext
    simp only [f, MonoidHom.mk'_apply]
    simp
    rw [hx]

/-- Every element of $1+P^N$ ($N$ large) is an $n$-th power of an element of $1+P$. -/
theorem exists_nth_root_near_one [CharZero K] (hK : IsPField K p) {v n' : ℕ} (hn' : Nat.Coprime n' p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ x ∈ onePlusP hK N, ∃ w ∈ onePlusP hK 1, w ^ (p ^ v * n') = x := by
  obtain ⟨c, N₀, hc1, hmp, hbij⟩ := exists_pow_p_bijOn hK
  set N₀' := max N₀ 1 with hN₀'
  have hN₀1 : 1 ≤ N₀' := le_max_right _ _
  have hA : ∀ v : ℕ, ∀ x ∈ onePlusP hK (N₀' + v * c), ∃ w ∈ onePlusP hK N₀', w ^ (p ^ v) = x := by
    intro v
    induction v with
    | zero => intro x hx; exact ⟨x, by simpa using hx, by simp⟩
    | succ v ih =>
      intro x hx
      have hx' : x ∈ onePlusP hK ((N₀' + v * c) + c) := by
        have : N₀' + (v + 1) * c = (N₀' + v * c) + c := by ring
        rwa [this] at hx
      obtain ⟨z, hz, hzx⟩ := (hbij (N₀' + v * c) (by
        have := Nat.le_add_right N₀' (v * c)
        exact (le_max_left _ _).trans this)).surjOn hx'
      obtain ⟨w, hw, hwz⟩ := ih z hz
      refine ⟨w, hw, ?_⟩
      rw [pow_succ, pow_mul, hwz]
      exact hzx
  refine ⟨N₀' + v * c, by omega, fun x hx => ?_⟩
  obtain ⟨w', hw', hw'x⟩ := hA v x hx
  obtain ⟨w, hw, hww⟩ := (weil_II_3_prop8_aut hK hn' (ν := N₀') hN₀1).surjOn hw'
  refine ⟨w, ?_, ?_⟩
  · rw [mem_onePlusP] at hw ⊢
    exact hw.trans (pow_le_pow_of_le_one zero_le (qi_lt_one hK).le hN₀1)
  · rw [mul_comm, pow_mul]
    have : w ^ n' = w' := hww
    rw [this]; exact hw'x

theorem isOpen_pow_range [CharZero K] (hK : IsPField K p) {n : ℕ} (hn0 : 0 < n) {v n' : ℕ}
    (hn : n = p ^ v * n') (hn' : Nat.Coprime n' p) :
    IsOpen ((Units.val : Kˣ → K) '' (MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ) : Set Kˣ)) := by
  obtain ⟨N, hN1, hN⟩ := exists_nth_root_near_one hK (v := v) hn'
  subst hn
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨u, ⟨w, rfl⟩, rfl⟩
  set a : K := (((powMonoidHom (p ^ v * n') : Kˣ →* Kˣ) w : Kˣ) : K) with ha
  have ha' : a = (w : K) ^ (p ^ v * n') := by simp [ha]
  have ha0 : a ≠ 0 := Units.ne_zero _
  have hapos : 0 < modK K a := modK_pos_iff.2 ha0
  have hc : 0 < modK K a * qi hK ^ N := mul_pos hapos (pow_pos (qi_pos hK) N)
  have hV : {z : K | modK K (z - a) < modK K a * qi hK ^ N} ∈ 𝓝 a := by
    refine (isOpen_lt (continuous_modK.comp (continuous_id.sub continuous_const))
      continuous_const).mem_nhds ?_
    show modK K (a - a) < modK K a * qi hK ^ N
    rw [sub_self, modK_zero']; exact hc
  refine Filter.mem_of_superset hV fun z hz => ?_
  have hz' : modK K (z - a) < modK K a * qi hK ^ N := hz
  have hv : z / a ∈ onePlusP hK N := by
    rw [mem_onePlusP]
    have e : z / a - 1 = (z - a) / a := by field_simp
    rw [e, div_eq_mul_inv, modK_mul, modK_inv ha0]
    exact ((mul_inv_lt_iff₀ hapos).2 (by rwa [mul_comm] at hz')).le
  obtain ⟨x, hx, hxz⟩ := hN _ hv
  have hx' := op_of_mem hK le_rfl hx
  have hx1 : modK K x = 1 := modK_eq_one_of_op hK hx'
  have hx0 : x ≠ 0 := fun h => by rw [h, modK_zero'] at hx1; exact zero_ne_one hx1
  refine ⟨(w * Units.mk0 x hx0) ^ (p ^ v * n'), ⟨w * Units.mk0 x hx0, rfl⟩, ?_⟩
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mk0, mul_pow, hxz, ← ha']
  field_simp

theorem range_pow_prod {A B : Type*} [CommGroup A] [CommGroup B] (n : ℕ) :
    (powMonoidHom n : A × B →* A × B).range =
      (powMonoidHom n : A →* A).range.prod (powMonoidHom n : B →* B).range := by
  ext ⟨a, b⟩
  simp only [MonoidHom.mem_range, Subgroup.mem_prod, powMonoidHom_apply]
  constructor
  · rintro ⟨⟨x, y⟩, h⟩
    exact ⟨⟨x, congrArg Prod.fst h⟩, ⟨y, congrArg Prod.snd h⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨(x, y), by simp [hx, hy]⟩

theorem index_pow_int (n : ℕ) :
    (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range.index = n := by
  have h : (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range =
      (AddSubgroup.zmultiples (n : ℤ)).toSubgroup := by
    ext y
    simp only [MonoidHom.mem_range, powMonoidHom_apply]
    show (∃ x : Multiplicative ℤ, x ^ n = y) ↔ Multiplicative.toAdd y ∈ AddSubgroup.zmultiples (n : ℤ)
    rw [AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Multiplicative.toAdd x, by simp [mul_comm]⟩
    · rintro ⟨k, hk⟩
      exact ⟨Multiplicative.ofAdd k, by
        apply Multiplicative.toAdd.injective
        simp [← hk, mul_comm]⟩
  rw [h, AddSubgroup.index_toSubgroup, Int.index_zmultiples]
  simp

theorem index_pow_units (hK : IsPField K p) {M0 : Subgroup Kˣ} (hM0 : Nat.card M0 = pq hK - 1)
    (Φ : Multiplicative ℤ × M0 × onePlusPUnits hK ≃* Kˣ) {v n' d m : ℕ} (hn' : Nat.Coprime n' p)
    (e : Additive (onePlusPUnits hK) ≃ₗ[ℤ_[p]]
      (Fin d → ℤ_[p]) × (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m})) :
    (powMonoidHom (p ^ v * n') : Kˣ →* Kˣ).range.index =
      (p ^ v * n') * Nat.gcd (pq hK - 1) (p ^ v * n') * ((p ^ v) ^ d * p ^ min v m) := by
  set n := p ^ v * n' with hn
  have hfM : Finite M0 := Nat.finite_of_card_ne_zero (by rw [hM0]; have := one_lt_pq_nat hK; omega)
  have hcyc := weil_I_4_thm7_cyclic hK M0 hM0
  have h1 : (powMonoidHom n : Kˣ →* Kˣ).range =
      (powMonoidHom n : Multiplicative ℤ × M0 × onePlusPUnits hK →* _).range.map (Φ : Multiplicative ℤ × M0 × onePlusPUnits hK →* Kˣ) := by
    ext y
    simp only [MonoidHom.mem_range, Subgroup.mem_map, powMonoidHom_apply]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨Φ.symm x, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨Φ x, by simp⟩
  rw [h1, Subgroup.index_map_equiv _ Φ, range_pow_prod, Subgroup.index_prod, range_pow_prod,
    Subgroup.index_prod, index_pow_int, IsCyclic.index_powMonoidHom_range, hM0,
    index_pow_onePlus hK hn' e]
  ring

theorem torsion_units_card (hK : IsPField K p) {M0 : Subgroup Kˣ} (hM0 : Nat.card M0 = pq hK - 1)
    (Φ : Multiplicative ℤ × M0 × onePlusPUnits hK ≃* Kˣ) {m : ℕ}
    (hcard : Nat.card (CommGroup.torsion (onePlusPUnits hK)) = p ^ m) :
    Finite (CommGroup.torsion Kˣ) ∧ Nat.card (CommGroup.torsion Kˣ) = (pq hK - 1) * p ^ m := by
  have hfM : Finite M0 := Nat.finite_of_card_ne_zero (by rw [hM0]; have := one_lt_pq_nat hK; omega)
  have hfT : Finite (CommGroup.torsion (onePlusPUnits hK)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
  let F : M0 × CommGroup.torsion (onePlusPUnits hK) → CommGroup.torsion Kˣ := fun a =>
    ⟨Φ (1, a.1, a.2.1), by
      have h : IsOfFinOrder ((1 : Multiplicative ℤ), a.1, a.2.1) :=
        IsOfFinOrder.prod_iff.2 ⟨IsOfFinOrder.one, IsOfFinOrder.prod_iff.2 ⟨isOfFinOrder_of_finite _, a.2.2⟩⟩
      exact (MonoidHom.isOfFinOrder Φ.toMonoidHom h : _)⟩
  have hinj : Function.Injective F := by
    rintro ⟨μ, u⟩ ⟨μ', u'⟩ h
    have h1 : Φ (1, μ, u.1) = Φ (1, μ', u'.1) := congrArg Subtype.val h
    have h2 := Φ.injective h1
    simp only [Prod.mk.injEq, true_and] at h2
    obtain ⟨rfl, h3⟩ := h2
    rw [Subtype.ext h3]
  have hsurj : Function.Surjective F := by
    rintro ⟨ζ, hζ⟩
    have hy : IsOfFinOrder (Φ.symm ζ) := MonoidHom.isOfFinOrder Φ.symm.toMonoidHom hζ
    obtain ⟨⟨z, μ, u⟩, hyζ⟩ : ∃ y, Φ y = ζ := ⟨Φ.symm ζ, by simp⟩
    have hy : IsOfFinOrder ((z, μ, u) : Multiplicative ℤ × M0 × onePlusPUnits hK) := by
      have := MonoidHom.isOfFinOrder Φ.symm.toMonoidHom hζ
      simpa [← hyζ] using this
    obtain ⟨hz, hrest⟩ := IsOfFinOrder.prod_iff.1 hy
    obtain ⟨-, hu⟩ := IsOfFinOrder.prod_iff.1 hrest
    have hz1 : z = 1 := by
      obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hz
      have h2 : (n : ℤ) * Multiplicative.toAdd z = 0 := by
        have := congrArg Multiplicative.toAdd h
        simpa using this
      have h3 : Multiplicative.toAdd z = 0 := by
        rcases mul_eq_zero.1 h2 with h4 | h4
        · exact absurd h4 (by exact_mod_cast hn.ne')
        · exact h4
      exact Multiplicative.toAdd.injective h3
    refine ⟨(μ, ⟨u, hu⟩), Subtype.ext ?_⟩
    show Φ (1, μ, u) = ζ
    rw [← hyζ, hz1]
  exact ⟨Finite.of_surjective F hsurj, by
    rw [Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩).symm, Nat.card_prod, hM0, hcard]⟩

end CorAux

/-- **Weil, II.§3, Corollary of Prop. 9.** For $n\ge1$, $(K^\times)^n$ is an open subgroup of $K^\times$ of finite index
$n\,(n,r)\,\operatorname{mod}_K(n)^{-1}$, where $r$ is the number of roots of $1$ in $K$ (a finite number). -/
@[kb "weil1973bnt" "Ch. II, §3, Cor. of Prop. 9"]
theorem weil_II_3_prop9_cor [CharZero K] (hK : IsPField K p) {n : ℕ} (hn : 0 < n) :
    Finite (CommGroup.torsion Kˣ) ∧
    IsOpen ((Units.val : Kˣ → K) '' (MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ) : Set Kˣ)) ∧
    (MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ)).index ≠ 0 ∧
    ((MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ)).index : ℝ≥0) =
      n * Nat.gcd n (Nat.card (CommGroup.torsion Kˣ)) * (modK K (n : K))⁻¹ := by
  obtain ⟨d, m, hd, hcard, hcyc, hmax, ⟨e⟩⟩ := prop9_strong hK
  obtain ⟨M0, hM0, ⟨Φ⟩⟩ := exists_decomp_equiv hK
  obtain ⟨hfin, hr⟩ := torsion_units_card hK hM0 Φ hcard
  obtain ⟨v, n', hn', hnn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.ne_one
  have hcop : Nat.Coprime n' p := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hn').symm
  have hidx := index_pow_units hK hM0 Φ hcop e (v := v)
  have hpq : 0 < pq hK - 1 := by have := one_lt_pq_nat hK; omega
  subst hnn
  refine ⟨hfin, isOpen_pow_range hK hn rfl hcop, ?_, ?_⟩
  · rw [hidx]
    exact Nat.pos_iff_ne_zero.1 (Nat.mul_pos (Nat.mul_pos hn (Nat.gcd_pos_of_pos_left _ hpq))
      (Nat.mul_pos (pow_pos (pow_pos hp.out.pos _) _) (pow_pos hp.out.pos _)))
  · have hg : Nat.gcd (p ^ v * n') (Nat.card (CommGroup.torsion Kˣ)) =
        Nat.gcd (pq hK - 1) (p ^ v * n') * p ^ min v m := by
      rw [hr, Nat.Coprime.gcd_mul _ ((coprime_pq_sub_one hK).pow_right m), Nat.gcd_comm _ (pq hK - 1)]
      congr 1
      rw [Nat.Coprime.gcd_mul_right_cancel _ (hcop.pow_right m)]
      rcases le_total v m with h | h
      · rw [min_eq_left h]; exact Nat.gcd_eq_left (pow_dvd_pow p h)
      · rw [min_eq_right h]; exact Nat.gcd_eq_right (pow_dvd_pow p h)
    have hmod : (modK K ((p ^ v * n' : ℕ) : K))⁻¹ = (((p ^ v) ^ d : ℕ) : ℝ≥0) := by
      have h1 : modK K (((p ^ v * n' : ℕ)) : K) = modK K (p : K) ^ v := by
        push_cast
        rw [modK_mul, modK_pow, modK_natCast_eq_one hK hcop, mul_one]
      rw [h1, ← inv_pow, ← hd, ← pow_mul]
      push_cast
      rw [← pow_mul, mul_comm]
    rw [hidx, hg, hmod]
    push_cast
    ring

end NumberFieldKB.WeilBNT.FieldModule
