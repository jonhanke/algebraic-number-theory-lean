import NumberFieldKB.WeilBNT.RayGroup
import QuadFormsKB.Tamagawa.QuatOrderGlobal
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Weil, *Basic Number Theory*, II.§3, Prop. 8 (first assertions): $n$-th powers in $k_v^\times$, $n$ prime to $p$

$k$ is a number field (`K`), $v$ a finite place, $K_v=k_v$ (`v.adicCompletion K`), $p$ the residue characteristic,
$1+\mathfrak p^\nu$ the subgroup `unitsOnePlusPow v ν` of $k_v^\times$ (from `RayGroup`). "$n$ prime to $p$" is
`(n : 𝓞 K) ∉ v.asIdeal` ($n$ is a unit in the residue field).

* **`weil_II_3_prop8_bijOn`**: for $n$ prime to $p$ and $\nu\ge1$, $x\mapsto x^n$ maps $1+\mathfrak p^\nu$ bijectively
  onto itself (it is an automorphism of that group).
* **`weil_II_3_prop8_isOpen`**: the group $(k_v^\times)^n$ of $n$-th powers is open in $k_v^\times$.

The index $n\cdot(n,q-1)$ of $(k_v^\times)^n$ (the last assertion of Prop. 8) is not formalized here.

*Proof.* Weil deduces the first assertion from the $\mathbb Z_p$-module structure of $1+\mathfrak p$ ($n$ is invertible
in $\mathbb Z_p$). Here it is proved directly, without that structure: surjectivity by Hensel's lemma for the complete
discrete valuation ring $r_v$ applied to $X^n-y$ (its derivative $nX^{n-1}$ is a unit at $X=1$), injectivity from
$x^n-1=(x-1)(1+x+\dots+x^{n-1})$ with the second factor $\equiv n\not\equiv0$; then
$(k_v^\times)^n\supseteq1+\mathfrak p$ is open.
-/

open IsDedekindDomain NumberField Topology

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]


omit [NumberField K] in
theorem val_nat_eq_one (v : HeightOneSpectrum (𝓞 K)) [NumberField K] {n : ℕ} (hn : (n : 𝓞 K) ∉ v.asIdeal) :
    Valued.v ((n : ℕ) : v.adicCompletion K) = 1 := by
  have e : ((n : ℕ) : v.adicCompletion K) =
      algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (n : 𝓞 K)) := by simp
  rw [e]
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (K := K) (v := v)
    (algebraMap (𝓞 K) K (n : 𝓞 K))]
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 hn

theorem pow_sub_one_le (v : HeightOneSpectrum (𝓞 K)) (z : v.adicCompletion K) (hz : Valued.v z = 1)
    (i : ℕ) : Valued.v (z ^ i - 1) ≤ Valued.v (z - 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : z ^ (i + 1) - 1 = z * (z ^ i - 1) + (z - 1) := by ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ le_rfl)
    rw [map_mul, hz, one_mul]; exact ih

theorem mem_max_iff (v : HeightOneSpectrum (𝓞 K)) (a : v.adicCompletionIntegers K) :
    a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔ Valued.v a.1 < 1 :=
  Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))))

theorem val_pow_sub_one (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : (n : 𝓞 K) ∉ v.asIdeal)
    (z : v.adicCompletion K) (hz : Valued.v z = 1) (h : Valued.v (z - 1) < 1) :
    Valued.v (z ^ n - 1) = Valued.v (z - 1) := by
  have hs : Valued.v (∑ i ∈ Finset.range n, z ^ i) = 1 := by
    have hlt : Valued.v (∑ i ∈ Finset.range n, z ^ i - (n : v.adicCompletion K)) < 1 := by
      have : ∑ i ∈ Finset.range n, z ^ i - (n : v.adicCompletion K) =
          ∑ i ∈ Finset.range n, (z ^ i - 1) := by
        rw [Finset.sum_sub_distrib]; simp
      rw [this]
      exact Valuation.map_sum_lt' _ zero_lt_one fun i _ => (pow_sub_one_le v z hz i).trans_lt h
    have e : ∑ i ∈ Finset.range n, z ^ i =
        (n : v.adicCompletion K) + (∑ i ∈ Finset.range n, z ^ i - (n : v.adicCompletion K)) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ (by rw [val_nat_eq_one v hn]; exact hlt),
      val_nat_eq_one v hn]
  rw [← geom_sum_mul, map_mul, hs, one_mul]

/-- **Weil, II.§3, Prop. 8, first assertion** ($K=k_v$, $k$ a number field). For $n$ prime to the residue
characteristic and $\nu\ge1$, $x\mapsto x^n$ maps $1+\mathfrak p_v^\nu$ bijectively onto itself. -/
@[kb "weil1973bnt" "Ch. II, §3, Prop. 8, first assertion (K = k_v, k a number field)"]
theorem weil_II_3_prop8_bijOn (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : (n : 𝓞 K) ∉ v.asIdeal)
    {ν : ℕ} (hν : 1 ≤ ν) :
    Set.BijOn (fun x : (v.adicCompletion K)ˣ => x ^ n)
      (unitsOnePlusPow (K := K) v ν : Set (v.adicCompletion K)ˣ)
      (unitsOnePlusPow (K := K) v ν : Set (v.adicCompletion K)ˣ) := by
  have hn0 : n ≠ 0 := by
    rintro rfl; apply hn; simp
  have hmem : ∀ u : (v.adicCompletion K)ˣ, u ∈ unitsOnePlusPow (K := K) v ν →
      Valued.v (u : v.adicCompletion K) = 1 ∧ Valued.v ((u : v.adicCompletion K) - 1) < 1 := by
    intro u hu
    refine ⟨hu.1, hu.2.trans_lt ?_⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  refine ⟨fun x hx => Subgroup.pow_mem _ hx n, ?_, ?_⟩
  · intro x hx y hy hxy
    have hxy' : x ^ n = y ^ n := hxy
    have hz : x * y⁻¹ ∈ unitsOnePlusPow (K := K) v ν := Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy)
    have hzn : ((x * y⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, mul_pow, hxy', inv_pow, mul_inv_cancel]; rfl
    obtain ⟨h1, h2⟩ := hmem _ hz
    have := val_pow_sub_one v hn _ h1 h2
    rw [hzn, sub_self, map_zero] at this
    have h0 : ((x * y⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 = 0 :=
      (Valuation.zero_iff _).1 this.symm
    have : x * y⁻¹ = 1 := Units.ext (sub_eq_zero.1 h0)
    exact mul_inv_eq_one.1 this
  · intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    let yA : v.adicCompletionIntegers K := ⟨(y : v.adicCompletion K), by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hy1.le⟩
    have hmon : (Polynomial.X ^ n - Polynomial.C yA : Polynomial (v.adicCompletionIntegers K)).Monic :=
      Polynomial.monic_X_pow_sub_C _ hn0
    have hroot0 : (Polynomial.X ^ n - Polynomial.C yA :
        Polynomial (v.adicCompletionIntegers K)).eval 1 ∈ IsLocalRing.maximalIdeal _ := by
      rw [mem_max_iff]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, one_pow]
      show Valued.v ((1 : v.adicCompletion K) - (y : v.adicCompletion K)) < 1
      rw [← Valuation.map_neg]; simp only [neg_sub]
      exact hy2.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    have hder : IsUnit ((Polynomial.derivative (Polynomial.X ^ n - Polynomial.C yA :
        Polynomial (v.adicCompletionIntegers K))).eval 1) := by
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
        sub_zero, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]
      have := val_nat_eq_one v (K := K) hn
      simpa using this
    obtain ⟨a, ha, ha1⟩ := HenselianLocalRing.is_henselian _ hmon 1 hroot0 hder
    rw [mem_max_iff] at ha1
    have hapow : (a : v.adicCompletion K) ^ n = (y : v.adicCompletion K) := by
      have := ha.eq_zero
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at this
      have := congrArg (fun t : v.adicCompletionIntegers K => (t : v.adicCompletion K)) (sub_eq_zero.1 this)
      simpa using this
    have ha1' : Valued.v ((a : v.adicCompletion K) - 1) < 1 := by simpa using ha1
    have hav : Valued.v (a : v.adicCompletion K) = 1 := by
      have := Valuation.map_eq_of_sub_lt (Valued.v (R := v.adicCompletion K))
        (x := 1) (y := (a : v.adicCompletion K)) (by rw [map_one]; exact ha1')
      rwa [map_one] at this
    have hane : (a : v.adicCompletion K) ≠ 0 := by
      intro h; rw [h, map_zero] at hav; exact zero_ne_one hav
    refine ⟨Units.mk0 _ hane, ⟨hav, ?_⟩, ?_⟩
    · have := val_pow_sub_one v hn _ hav ha1'
      rw [hapow] at this
      show Valued.v ((a : v.adicCompletion K) - 1) ≤ _
      rw [← this]; exact hy2
    · apply Units.ext
      simpa using hapow

/-- **Weil, II.§3, Prop. 8, second assertion** ($K=k_v$, $k$ a number field). For $n$ prime to the residue
characteristic, the subgroup $(k_v^\times)^n$ of $n$-th powers is open in $k_v^\times$. -/
@[kb "weil1973bnt" "Ch. II, §3, Prop. 8, second assertion, openness (K = k_v, k a number field)"]
theorem weil_II_3_prop8_isOpen (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : (n : 𝓞 K) ∉ v.asIdeal) :
    IsOpen (Set.range (fun x : (v.adicCompletion K)ˣ => x ^ n)) := by
  have hsub : (unitsOnePlusPow (K := K) v 1) ≤ (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range := by
    intro u hu
    obtain ⟨x, _, hx⟩ := (weil_II_3_prop8_bijOn v hn le_rfl).surjOn hu
    exact ⟨x, hx⟩
  have := Subgroup.isOpen_mono hsub (isOpen_unitsOnePlusPow v 1)
  convert this using 1
  ext x
  simp [powMonoidHom]

end NumberFieldKB.WeilBNT
