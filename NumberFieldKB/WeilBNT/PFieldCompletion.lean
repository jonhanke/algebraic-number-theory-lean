import NumberFieldKB.WeilBNT.PFieldUnits
import NumberFieldKB.LocalZeta.NonArchimedean

/-!
# Completions of a number field are $p$-fields in Weil's sense (comparison)

For a number field $k$ (`F`) and a finite place $v$ with residue characteristic $p$, the completion $k_v$
(`v.adicCompletion F`) is a nondiscrete locally compact field, Weil's module $\operatorname{mod}_{k_v}$ (`modK`,
I.§2) is the normalized absolute value, and $k_v$ is a $p$-field (I.§3, Def. 2) whose module $q$ (I.§4, Def. 3) is the
absolute norm $N(v)$ of $v$. This compares the convention of `FieldModule`/`PField` (Weil's, defined from Haar measure)
with the valuation conventions used elsewhere in the knowledge base (`Valued.v`, QuadFormsKB's `modV`).

* `modK_adicCompletion`: if $v(x)=\exp(-n)$ (i.e. $\operatorname{ord}_v x=n$), then
  $\operatorname{mod}_{k_v}(x)=N(v)^{-n}$.
* `isPField_adicCompletion`: $k_v$ is a $p$-field; `pq_adicCompletion`: its $q$ is $N(v)$.
* `weil_II_3_prop8_index_adicCompletion`: II.§3, Prop. 8, last assertion, for $K=k_v$: $(k_v^\times)^n$ has index
  $n\cdot(n,N(v)-1)$ when $n$ is prime to $p$ (the first assertions for $k_v$ are in `LocalPowers`).
-/

open IsDedekindDomain NumberField Topology MeasureTheory
open scoped NNReal
open QuadFormsKB QuadFormsKB.Analysis NumberFieldKB.LocalZeta IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace NumberFieldKB.WeilBNT.FieldModule

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

instance neBot_nhdsNE_adicCompletion : (𝓝[≠] (0 : Fv)).NeBot := inferInstance

/-- The absolute norm of a finite place is at least $2$. -/
theorem two_le_absNorm : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  omega

theorem modK_adicCompletion {x : Fv} {n : ℤ} (hx : Valued.v x = WithZero.exp (-n)) :
    modK Fv x = ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ (-n) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  rw [modK, dif_neg hx0]
  apply NNReal.coe_injective
  have hmem : Units.mk0 x hx0 ∈ shell v n := hx
  rw [distribHaarChar_of_mem_shell v hmem, modV_eq, NNReal.coe_zpow, NNReal.coe_natCast, inv_zpow']

/-- A nonzero element has a valuation $\exp(-n)$ for some integer $n$. -/
theorem exists_valued_eq {x : Fv} (hx : x ≠ 0) : ∃ n : ℤ, Valued.v x = WithZero.exp (-n) :=
  ⟨-WithZero.log (Valued.v x), by rw [neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)]⟩

/-- For a nonzero element of valuation $\exp(-n)$, the module is below $1$ exactly when $n\ge1$. -/
theorem modK_adicCompletion_lt_one_iff {x : Fv} {n : ℤ} (hn : Valued.v x = WithZero.exp (-n)) :
    modK Fv x < 1 ↔ 1 ≤ n := by
  rw [modK_adicCompletion v hn]
  have h2 : (1 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := by exact_mod_cast two_le_absNorm v
  constructor
  · intro h
    by_contra hn1
    push Not at hn1
    have : (1 : ℝ≥0) ≤ (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-n) :=
      one_le_zpow₀ h2.le (by omega)
    exact absurd h (not_lt.2 this)
  · intro h
    exact zpow_lt_one_of_neg₀ h2 (by omega)

theorem isPField_adicCompletion {p : ℕ} (hp : p.Prime) (hpv : (p : 𝓞 F) ∈ v.asIdeal) : IsPField Fv p := by
  refine ⟨hp, ?_⟩
  have hval : Valued.v ((p : ℕ) : Fv) < 1 := by
    have e : ((p : ℕ) : Fv) = (((p : ℕ) : F) : Fv) := (map_natCast (algebraMap F Fv) p).symm
    have h1 : v.valuation F ((p : ℕ) : F) < 1 := by
      have := (v.valuation_lt_one_iff_mem (K := F) ((p : ℕ) : 𝓞 F)).2 hpv
      simpa using this
    rw [e]
    exact (valuedAdicCompletion_eq_valuation' (R := 𝓞 F) (K := F) (v := v) ((p : ℕ) : F)).trans_lt h1
  have hp0 : ((p : ℕ) : Fv) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨n, hn⟩ := exists_valued_eq v hp0
  rw [modK_adicCompletion_lt_one_iff v hn]
  rw [hn] at hval
  have : WithZero.exp (-n) < WithZero.exp (0 : ℤ) := by simpa using hval
  have := WithZero.exp_lt_exp.1 this
  omega

theorem pq_adicCompletion {p : ℕ} (hp : p.Prime) (hpv : (p : 𝓞 F) ∈ v.asIdeal) :
    pq (isPField_adicCompletion v hp hpv) = Ideal.absNorm v.asIdeal := by
  set hK := isPField_adicCompletion v hp hpv
  have hπv : Valued.v (HN.ϖ v) = WithZero.exp (-(1 : ℤ)) := by
    simpa using valued_ϖ_zpow v 1
  have hπ0 := HN.ϖ_ne_zero v
  have h2 : (1 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := by exact_mod_cast two_le_absNorm v
  have hP : pP hK = (fun r => HN.ϖ v * r) '' (pR hK : Set Fv) := by
    ext x
    constructor
    · intro hx
      have hx' : modK Fv x < 1 := hx
      by_cases hx0 : x = 0
      · exact ⟨0, (pR hK).zero_mem, by simp [hx0]⟩
      obtain ⟨m, hm⟩ := exists_valued_eq v hx0
      have hm1 := (modK_adicCompletion_lt_one_iff v hm).1 hx'
      refine ⟨x / HN.ϖ v, ?_, mul_div_cancel₀ _ hπ0⟩
      have hv : Valued.v (x / HN.ϖ v) = WithZero.exp (-(m - 1)) := by
        rw [map_div₀, hm, hπv, ← WithZero.exp_sub]
        congr 1; ring
      show modK Fv (x / HN.ϖ v) ≤ 1
      rw [modK_adicCompletion v hv]
      exact zpow_le_one_of_nonpos₀ h2.le (by omega)
    · rintro ⟨r, hr, rfl⟩
      show modK Fv (HN.ϖ v * r) < 1
      rw [modK_mul, modK_adicCompletion v (n := 1) hπv]
      have hr' : modK Fv r ≤ 1 := hr
      calc _ ≤ (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-1 : ℤ) * 1 := by gcongr
        _ < 1 := by
          rw [mul_one]; exact zpow_lt_one_of_neg₀ h2 (by norm_num)
  have h := weil_I_4_thm6_modK_prime hK hπ0 hP
  rw [modK_adicCompletion v (n := 1) hπv] at h
  have h' : ((Ideal.absNorm v.asIdeal : ℝ≥0)) = (pq hK : ℝ≥0) := by
    rw [zpow_neg_one] at h
    exact inv_injective h
  exact_mod_cast h'.symm

@[kb "weil1973bnt" "Ch. II, §3, Prop. 8, last assertion (K = k_v, k a number field)"]
theorem weil_II_3_prop8_index_adicCompletion {p : ℕ} (hp : p.Prime) (hpv : (p : 𝓞 F) ∈ v.asIdeal) {n : ℕ}
    (hn : Nat.Coprime n p) (hn0 : 0 < n) :
    (MonoidHom.range (powMonoidHom n : Fvˣ →* Fvˣ)).index = n * Nat.gcd n (Ideal.absNorm v.asIdeal - 1) := by
  rw [← pq_adicCompletion v hp hpv]
  exact weil_II_3_prop8_index (isPField_adicCompletion v hp hpv) hn hn0

end NumberFieldKB.WeilBNT.FieldModule
