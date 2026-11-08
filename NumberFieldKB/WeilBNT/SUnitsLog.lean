import Mathlib.NumberTheory.NumberField.ProductFormula
import NumberFieldKB.WeilBNT.RootsOfUnity

/-!
# Weil, *Basic Number Theory*, IV.§4: the $P$-units and their logarithms (first half of Theorem 9)

$k$ is a number field, $P=P_\infty\cup S$ with $S$ a finite set of finite places, and
$$E(P)=\{e\in k^\times:\ \lvert e\rvert_v=1\ \text{for } v\notin P\}$$
(Weil, p. 77). Weil proves Theorem 9 ($E(P)\cong\mu_k\times\mathbb Z^{\lvert P\rvert-1}$) by mapping $\Omega(P)$ onto
$G=\Omega(P)/U\subset\mathbb R^{P}$ by the logarithms of the absolute values and applying Lemma 5 to the image $\Gamma$ of
$E(P)$. This file has the parts of that argument that concern $E(P)$ alone:

* **`sUnits K S`**: the group $E(P)$ (`mem_sUnits_iff_finitePlace`: $\lvert e\rvert_v=1$ for $v\notin S$);
* **`logEmb K S`**: $e\mapsto(\log\lvert e\rvert_v)_{v\in P}$, with Weil's normalization $\lvert x\rvert_w=\|x\|^{m_w}$
  at the infinite places ($m_w=2$ at complex places); additive on $k^\times$ (`logEmb_mul`);
* **`sum_logEmb_eq_zero`**: for $e\in E(P)$ the coordinates sum to $0$ (Theorem 5, the product formula), so $\Gamma$ lies
  in the hyperplane $G_1$;
* **`logEmb_eq_zero_iff`**: the kernel of $E(P)\to\Gamma$ is the group of roots of unity (Theorem 8; Weil:
  "$E(P)\cap U=E$");
* **`finite_logEmb_bounded`**: only finitely many $e\in E(P)$ have all $\lvert\log\lvert e\rvert_v\rvert\le B$, i.e.
  $\Gamma$ is discrete with finite fibres (Weil: "$WU$ is compact and has a finite intersection with $E(P)$"; here, as in
  Theorem 8, by clearing the denominators at $S$ with a rational integer and Mathlib's `Embeddings.finite_of_norm_le`).
-/

open IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.WeilBNT

variable (K : Type*) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- Weil's $E(P)$ for $P=P_\infty\cup S$: the elements of $k^\times$ that are units at every finite place outside $S$. -/
def sUnits : Subgroup Kˣ where
  carrier := {e | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v.valuation K (e : K) = 1}
  mul_mem' {a b} ha hb v hv := by rw [Units.val_mul, map_mul, ha v hv, hb v hv, one_mul]
  one_mem' v _ := by simp
  inv_mem' {a} ha v hv := by rw [Units.val_inv_eq_inv_val, map_inv₀, ha v hv, inv_one]

/-- The places in $P=P_\infty\cup S$. -/
abbrev PlP := InfinitePlace K ⊕ S

/-- The logarithmic embedding $e\mapsto(\log\lvert e\rvert_v)_{v\in P}$ with Weil's module normalization. -/
def logEmb (e : K) : PlP K S → ℝ
  | .inl w => w.mult * Real.log (w e)
  | .inr v => Real.log (FinitePlace.mk v.1 e)

variable {K S}

theorem finitePlace_eq_one_iff (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    FinitePlace.mk v x = 1 ↔ v.valuation K x = 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding', NNReal.coe_eq_one,
    WithZeroMulInt.toNNReal_eq_one_iff _ (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v).ne']

theorem finitePlace_le_one_iff (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    FinitePlace.mk v x ≤ 1 ↔ v.valuation K x ≤ 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding', ← NNReal.coe_one, NNReal.coe_le_coe,
    WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)]

theorem mem_sUnits_iff_finitePlace {e : Kˣ} :
    e ∈ sUnits K S ↔ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → FinitePlace.mk v (e : K) = 1 :=
  forall₂_congr fun v _ => (finitePlace_eq_one_iff v _).symm

theorem logEmb_mul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : logEmb K S (a * b) = logEmb K S a + logEmb K S b := by
  funext i
  rcases i with w | v
  · simp only [logEmb, map_mul, Pi.add_apply]
    rw [Real.log_mul ((map_ne_zero w).mpr ha) ((map_ne_zero w).mpr hb)]
    ring
  · simp only [logEmb, map_mul, Pi.add_apply]
    rw [Real.log_mul ((map_ne_zero _).mpr ha) ((map_ne_zero _).mpr hb)]

theorem logEmb_one : logEmb K S 1 = 0 := by
  funext i; rcases i with w | v <;> simp [logEmb]

/-- **The product formula on $E(P)$** (Weil, IV.§4 Thm. 5): $\sum_{v\in P}\log\lvert e\rvert_v=0$. -/
theorem sum_logEmb_eq_zero {e : Kˣ} (he : e ∈ sUnits K S) : ∑ i, logEmb K S (e : K) i = 0 := by
  have hpf := prod_abs_eq_one (K := K) e.ne_zero
  have hfin : ∏ᶠ w : FinitePlace K, w (e : K) = ∏ v ∈ S, FinitePlace.mk v (e : K) := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    simp only [FinitePlace.equivHeightOneSpectrum_symm_apply]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvS
    exact hv ((mem_sUnits_iff_finitePlace.mp he) v hvS)
  rw [hfin] at hpf
  have hpos_inf : ∀ w : InfinitePlace K, w (e : K) ^ w.mult ≠ 0 :=
    fun w => pow_ne_zero _ ((map_ne_zero w).mpr e.ne_zero)
  have hpos_fin : ∀ v ∈ S, FinitePlace.mk v (e : K) ≠ 0 := fun v _ => (map_ne_zero _).mpr e.ne_zero
  have hlog := congrArg Real.log hpf
  rw [Real.log_one, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun w _ => hpos_inf w)
    (Finset.prod_ne_zero_iff.mpr hpos_fin), Real.log_prod (fun w _ => hpos_inf w),
    Real.log_prod hpos_fin] at hlog
  rw [Fintype.sum_sum_type]
  simp only [logEmb]
  rw [← hlog]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.log_pow]
  · exact (Finset.sum_coe_sort S fun v => Real.log (FinitePlace.mk v (e : K)))

/-- **The kernel of $E(P)\to\Gamma$ is the group of roots of unity** (Weil: $E(P)\cap U=E$, with Theorem 8). -/
theorem logEmb_eq_zero_iff {e : Kˣ} (he : e ∈ sUnits K S) :
    logEmb K S (e : K) = 0 ↔ ∃ n : ℕ, 0 < n ∧ (e : K) ^ n = 1 := by
  rw [← weil_IV_4_thm8_rootsOfUnity e.ne_zero]
  constructor
  · intro h0
    refine ⟨fun w => ?_, fun v => ?_⟩
    · have h := congrFun h0 (.inl w)
      simp only [logEmb, Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero] at h
      rcases h with h | h
      · exact absurd h w.mult_ne_zero
      · have hw : 0 < w (e : K) := InfinitePlace.pos_iff.mpr e.ne_zero
        rcases Real.log_eq_zero.mp h with h | h | h
        · exact absurd h hw.ne'
        · exact h.le
        · linarith
    · by_cases hv : v ∈ S
      · have h := congrFun h0 (.inr ⟨v, hv⟩)
        simp only [logEmb, Pi.zero_apply] at h
        have hpos : 0 < FinitePlace.mk v (e : K) := FinitePlace.pos_iff.mpr e.ne_zero
        rcases Real.log_eq_zero.mp h with h | h | h
        · exact absurd h hpos.ne'
        · exact ((finitePlace_eq_one_iff v _).mp h).le
        · linarith
      · exact (he v hv).le
  · intro hF
    obtain ⟨n, hn, hen⟩ := (weil_IV_4_thm8_rootsOfUnity e.ne_zero).mp hF
    have habs : ∀ f : K →*₀ ℝ, (∀ x, 0 ≤ f x) → f (e : K) = 1 := by
      intro f hf
      have h : f (e : K) ^ n = 1 := by rw [← map_pow, hen, map_one]
      exact (pow_eq_one_iff_of_nonneg (hf _) hn.ne').mp h
    funext i
    rcases i with w | v
    · simp only [logEmb, Pi.zero_apply]
      have h : w (e : K) ^ n = 1 := by rw [← map_pow, hen, map_one]
      rw [(pow_eq_one_iff_of_nonneg (by positivity : (0 : ℝ) ≤ w (e : K)) hn.ne').mp h, Real.log_one, mul_zero]
    · simp only [logEmb, Pi.zero_apply]
      have : FinitePlace.mk v.1 (e : K) = 1 := by
        have h := habs (FinitePlace.mk v.1).1.toMonoidWithZeroHom (fun x => (FinitePlace.mk v.1).1.nonneg x)
        exact h
      rw [this, Real.log_one]

/-- A rational integer has absolute value at most $1$ at every finite place. -/
theorem finitePlace_natCast_le_one (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) : FinitePlace.mk v (n : K) ≤ 1 := by
  have h := FinitePlace.norm_le_one K v (n : 𝓞 K)
  rw [map_natCast] at h
  rwa [FinitePlace.mk_apply]

/-- **$\Gamma$ is discrete** (Weil, proof of Thm. 9): only finitely many $e\in E(P)$ have
$\lvert\log\lvert e\rvert_v\rvert\le B$ for every $v\in P$. -/
theorem finite_logEmb_bounded (B : ℝ) :
    {e : Kˣ | e ∈ sUnits K S ∧ ∀ i, |logEmb K S (e : K) i| ≤ B}.Finite := by
  classical
  set C := Real.exp |B| with hC
  have hC1 : 1 ≤ C := Real.one_le_exp (abs_nonneg B)
  -- the norm of $v$ is small at $v$
  have hsmall : ∀ v : HeightOneSpectrum (𝓞 K), ∃ m : ℕ,
      FinitePlace.mk v ((Ideal.absNorm v.asIdeal : ℕ) : K) ^ m < C⁻¹ := by
    intro v
    have hlt : FinitePlace.mk v ((Ideal.absNorm v.asIdeal : ℕ) : K) < 1 := by
      have h := (FinitePlace.norm_lt_one_iff_mem K v ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K)).mpr
        (Ideal.absNorm_mem v.asIdeal)
      rw [map_natCast] at h
      rwa [FinitePlace.mk_apply]
    exact exists_pow_lt_of_lt_one (inv_pos.mpr (by positivity)) hlt
  choose mv hmv using hsmall
  set m := S.sup mv
  set d : ℕ := ∏ v ∈ S, (Ideal.absNorm v.asIdeal) ^ m with hd
  have hd0 : (d : K) ≠ 0 := by
    rw [Nat.cast_ne_zero, hd, Finset.prod_ne_zero_iff]
    intro v _
    exact pow_ne_zero _ (Ideal.absNorm_ne_zero_of_nonZeroDivisors ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)
  have hdv : ∀ v ∈ S, FinitePlace.mk v (d : K) ≤ C⁻¹ := by
    intro v hv
    rw [hd, Nat.cast_prod, map_prod, ← Finset.mul_prod_erase S _ hv]
    have h1 : ∏ x ∈ S.erase v, FinitePlace.mk v (((Ideal.absNorm x.asIdeal) ^ m : ℕ) : K) ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => (FinitePlace.mk v).1.nonneg _) fun x _ => finitePlace_natCast_le_one v _
    have h2 : FinitePlace.mk v (((Ideal.absNorm v.asIdeal) ^ m : ℕ) : K) ≤ C⁻¹ := by
      rw [Nat.cast_pow, map_pow]
      have h0 : 0 ≤ FinitePlace.mk v ((Ideal.absNorm v.asIdeal : ℕ) : K) := (FinitePlace.mk v).1.nonneg _
      have hle1 := finitePlace_natCast_le_one v (Ideal.absNorm v.asIdeal)
      exact (pow_le_pow_of_le_one h0 hle1 (Finset.le_sup hv)).trans (hmv v).le
    calc _ ≤ C⁻¹ * 1 := mul_le_mul h2 h1 (Finset.prod_nonneg fun _ _ => (FinitePlace.mk v).1.nonneg _)
          (by positivity)
      _ = C⁻¹ := mul_one _
  -- the target finite set
  have hT := Embeddings.finite_of_norm_le K ℂ ((d : ℝ) * C)
  refine ((hT.preimage (f := fun e : Kˣ => (d : K) * (e : K)) fun a _ b _ hab => ?_).subset) ?_
  · exact Units.val_injective (mul_left_cancel₀ hd0 hab)
  rintro e ⟨he, hB⟩
  have hlogle : ∀ i, logEmb K S (e : K) i ≤ |B| := fun i => (le_abs_self _).trans ((hB i).trans (le_abs_self B))
  refine ⟨?_, fun φ => ?_⟩
  · -- integrality: all valuations of $d e$ are at most one
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((d : K) * (e : K)) fun v => by
      rw [← finitePlace_le_one_iff, map_mul]
      by_cases hv : v ∈ S
      · have he_le : FinitePlace.mk v (e : K) ≤ C := by
          have h := hlogle (.inr ⟨v, hv⟩)
          simp only [logEmb] at h
          exact (Real.log_le_iff_le_exp (FinitePlace.pos_iff.mpr e.ne_zero)).mp h
        calc FinitePlace.mk v (d : K) * FinitePlace.mk v (e : K) ≤ C⁻¹ * C :=
              mul_le_mul (hdv v hv) he_le ((FinitePlace.mk v).1.nonneg _) (by positivity)
          _ = 1 := inv_mul_cancel₀ (by positivity)
      · rw [(mem_sUnits_iff_finitePlace.mp he) v hv, mul_one]
        exact finitePlace_natCast_le_one v d
    show IsIntegral ℤ ((d : K) * (e : K))
    rw [← hr]
    exact (RingOfIntegers.isIntegral r).algebraMap
  · -- archimedean bound
    have hw : InfinitePlace.mk φ (e : K) ≤ C := by
      have h := hlogle (.inl (InfinitePlace.mk φ))
      simp only [logEmb] at h
      have hpos : 0 < InfinitePlace.mk φ (e : K) := InfinitePlace.pos_iff.mpr e.ne_zero
      rw [← Real.log_le_iff_le_exp hpos]
      by_cases hl : Real.log (InfinitePlace.mk φ (e : K)) ≤ 0
      · exact hl.trans (abs_nonneg B)
      · push Not at hl
        have hm : (1 : ℝ) ≤ (InfinitePlace.mk φ).mult := by exact_mod_cast InfinitePlace.one_le_mult
        nlinarith
    rw [InfinitePlace.apply] at hw
    simp only [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg d)

end NumberFieldKB.WeilBNT

end
