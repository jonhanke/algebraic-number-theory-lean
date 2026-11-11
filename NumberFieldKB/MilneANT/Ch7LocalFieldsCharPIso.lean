import NumberFieldKB.MilneANT.Ch7LocalFieldsCharP
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Milne, *Algebraic Number Theory*, Remark 7.49(c): local fields of characteristic $p$ are Laurent series fields

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), bib key `milne2020ant`, Remark 7.49(c), p. 127:
a nonarchimedean local field of characteristic $p \ne 0$ is isomorphic to $k((T))$ for a finite field $k$.

Proof (using `Ch7LocalFieldsCharP`): let $k \subseteq K$ be the Teichmüller subfield (`Remark749c.exists_teichmuller`) and
$\pi$ a uniformizer (`exists_uniformizer`).
* `evalHom`: $\sum c_n T^n \mapsto \sum c_n \pi^n$ is a ring homomorphism $k[[T]] \to K$ (the series converges since
  $|c_n \pi^n| \le |\pi|^n$ in the complete space $K$; multiplicativity is the Cauchy product formula for absolutely
  summable series).
* `evalHom_injective`: $f = T^m g$ with $g(0) \ne 0$, so $\varphi(f) = \pi^m \varphi(g)$ with $\varphi(g)$ a unit.
* `exists_series`: every $x$ with $|x| \le 1$ is $\varphi(f)$: successive approximation $x_n = c_n + \pi x_{n+1}$ with
  $c_n$ Teichmüller representatives (`hmax` shows $|x_{n+1}| \le 1$), and $x - \sum_{i<N} c_i\pi^i = \pi^N x_N \to 0$.
* `remark7_49c`: extend $\varphi$ to $k((T)) = \operatorname{Frac}(k[[T]])$ (`IsFractionRing.lift`); it is surjective
  since each $x \ne 0$ is $\pi^n u$ with $|u| = 1$ (`value_eq_zpow`).
-/

open scoped PowerSeries

namespace NumberFieldKB.MilneANT
namespace Remark749c

section series

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ} [CompleteSpace (WithAbs v)]
  (k : Subfield K) (π : K)

/-- The `n`-th term `c_n π^n` of the image of a power series. -/
noncomputable def term (f : PowerSeries k) (n : ℕ) : K := ((PowerSeries.coeff n f : k) : K) * π ^ n

/-- The sum `∑ c_n π^n` (computed in the complete space `WithAbs v`). -/
noncomputable def evalSeries (v : AbsoluteValue K ℝ) (f : PowerSeries k) : K :=
  WithAbs.ofAbs (∑' n, WithAbs.toAbs v (term k π f n))

variable {k π}

lemma v_term_le (hk : ∀ c : k, v c ≤ 1) (f : PowerSeries k) (n : ℕ) :
    v (term k π f n) ≤ v π ^ n := by
  unfold term
  rw [map_mul, map_pow]
  calc v ((PowerSeries.coeff n f : k) : K) * v π ^ n ≤ 1 * v π ^ n := by
        gcongr; exact hk _
    _ = v π ^ n := one_mul _

lemma summable_term (hk : ∀ c : k, v c ≤ 1) (hπ1 : v π < 1) (f : PowerSeries k) :
    Summable (fun n => ‖WithAbs.toAbs v (term k π f n)‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => by rw [WithAbs.norm_toAbs_eq]; exact v_term_le hk f n)
    (summable_geometric_of_lt_one (v.nonneg π) hπ1)

omit [CompleteSpace (WithAbs v)] in
lemma toAbs_sum {ι : Type*} (s : Finset ι) (a : ι → K) :
    WithAbs.toAbs v (∑ i ∈ s, a i) = ∑ i ∈ s, WithAbs.toAbs v (a i) :=
  map_sum (WithAbs.equiv v).symm a s

lemma hasSum_term (hk : ∀ c : k, v c ≤ 1) (hπ1 : v π < 1) (f : PowerSeries k) :
    HasSum (fun n => WithAbs.toAbs v (term k π f n))
      (WithAbs.toAbs v (evalSeries k π v f)) :=
  (summable_term hk hπ1 f).of_norm.hasSum

lemma evalSeries_of_single (hk : ∀ c : k, v c ≤ 1) (hπ1 : v π < 1) (f : PowerSeries k) (m : ℕ)
    (h : ∀ n, n ≠ m → term k π f n = 0) : evalSeries k π v f = term k π f m := by
  have h1 : HasSum (fun n => WithAbs.toAbs v (term k π f n)) (WithAbs.toAbs v (term k π f m)) :=
    hasSum_single m (fun n hn => by rw [h n hn]; rfl)
  exact congrArg WithAbs.ofAbs ((hasSum_term hk hπ1 f).unique h1)

lemma term_mul (f g : PowerSeries k) (n : ℕ) :
    ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, term k π f kl.1 * term k π g kl.2 = term k π (f * g) n := by
  unfold term
  rw [PowerSeries.coeff_mul]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun kl hkl => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; ring

/-- The evaluation homomorphism `k⟦T⟧ → K`, `T ↦ π`. -/
noncomputable def evalHom (hk : ∀ c : k, v c ≤ 1) (hπ1 : v π < 1) : PowerSeries k →+* K where
  toFun := evalSeries k π v
  map_one' := by
    rw [evalSeries_of_single hk hπ1 1 0 (fun n hn => by simp [term, PowerSeries.coeff_one, hn])]
    simp [term]
  map_zero' := by
    rw [evalSeries_of_single hk hπ1 0 0 (fun n hn => by simp [term])]
    simp [term]
  map_add' f g := by
    have h1 := (hasSum_term hk hπ1 f).add (hasSum_term hk hπ1 g)
    have h2 := hasSum_term hk hπ1 (f + g)
    have e : (fun n => WithAbs.toAbs v (term k π (f + g) n)) =
        fun n => WithAbs.toAbs v (term k π f n) + WithAbs.toAbs v (term k π g n) := by
      funext n
      have : term k π (f + g) n = term k π f n + term k π g n := by
        simp only [term, map_add]; push_cast; ring
      rw [this]; rfl
    rw [e] at h2
    exact congrArg WithAbs.ofAbs (h2.unique h1)
  map_mul' f g := by
    have h := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_term hk hπ1 f)
      (summable_term hk hπ1 g)
    have h2 := (hasSum_term hk hπ1 (f * g)).tsum_eq
    have e : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, WithAbs.toAbs v (term k π f kl.1) *
        WithAbs.toAbs v (term k π g kl.2) = WithAbs.toAbs v (term k π (f * g) n) := by
      intro n
      rw [← term_mul, toAbs_sum]
      simp only [WithAbs.toAbs_mul]
    simp_rw [e] at h
    rw [(hasSum_term hk hπ1 f).tsum_eq, (hasSum_term hk hπ1 g).tsum_eq, h2] at h
    exact (congrArg WithAbs.ofAbs h).symm

lemma evalHom_apply (hk : ∀ c : k, v c ≤ 1) (hπ1 : v π < 1) (f : PowerSeries k) :
    evalHom hk hπ1 f = evalSeries k π v f := rfl

lemma evalHom_X (hk : ∀ c : k, v c ≤ 1) (hπ1 : v π < 1) :
    evalHom hk hπ1 (PowerSeries.X : PowerSeries k) = π := by
  rw [evalHom_apply, evalSeries_of_single hk hπ1 _ 1
    (fun n hn => by simp [term, PowerSeries.coeff_X, hn])]
  simp [term]

lemma evalHom_injective (hk : ∀ c : k, v c ≤ 1) (hπ1 : v π < 1) (hπ0 : π ≠ 0) :
    Function.Injective (evalHom hk hπ1) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra hf0
  obtain ⟨g, hg⟩ := PowerSeries.X_pow_order_dvd (φ := f)
  have hc := PowerSeries.coeff_order hf0
  generalize f.order.toNat = m at hg hc
  have hcm : PowerSeries.coeff m f = PowerSeries.constantCoeff g := by
    rw [hg, PowerSeries.coeff_X_pow_mul', if_pos (le_refl m), Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hg0 : PowerSeries.constantCoeff g ≠ 0 := hcm ▸ hc
  have hu : IsUnit g := PowerSeries.isUnit_iff_constantCoeff.2 (isUnit_iff_ne_zero.2 hg0)
  have h1 : evalHom hk hπ1 f = π ^ m * evalHom hk hπ1 g := by
    rw [hg, map_mul, map_pow, evalHom_X]
  rw [h1] at hf
  exact mul_ne_zero (pow_ne_zero _ hπ0) (hu.map _).ne_zero hf

lemma exists_series (hk : ∀ c : k, v c ≤ 1) (hπ1 : v π < 1) (hπ0 : 0 < v π) (T : K → k)
    (hT : ∀ y, v y ≤ 1 → v (y - T y) < 1) (hmax : ∀ y, v y < 1 → v y ≤ v π) (x : K)
    (hx : v x ≤ 1) : ∃ f : PowerSeries k, evalHom hk hπ1 f = x := by
  have hπne : π ≠ 0 := fun h => by simp [h] at hπ0
  set g : K → K := fun z => (z - T z) / π with hg
  have hy1 : ∀ n, v (g^[n] x) ≤ 1 := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      show v ((g^[n] x - T (g^[n] x)) / π) ≤ 1
      rw [map_div₀, div_le_one hπ0]
      exact hmax _ (hT _ ih)
  refine ⟨PowerSeries.mk (fun n => T (g^[n] x)), ?_⟩
  set f := PowerSeries.mk (fun n => T (g^[n] x)) with hf
  have hS : ∀ N, x - ∑ i ∈ Finset.range N, term k π f i = π ^ N * g^[N] x := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ← sub_sub, ih, Function.iterate_succ_apply']
      simp only [term, hf, PowerSeries.coeff_mk, hg]
      field_simp
      ring
  have hbound : ∀ N, v (∑ i ∈ Finset.range N, term k π f i - x) ≤ v π ^ N := by
    intro N
    rw [v.map_sub, hS, map_mul, map_pow]
    calc v π ^ N * v (g^[N] x) ≤ v π ^ N * 1 := by gcongr; exact hy1 N
      _ = v π ^ N := mul_one _
  have hT1 := (hasSum_term hk hπ1 f).tendsto_sum_nat
  have hT2 : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, WithAbs.toAbs v (term k π f i))
      Filter.atTop (nhds (WithAbs.toAbs v x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun N => dist_nonneg) (fun N => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg π) hπ1)
    rw [← toAbs_sum, dist_toAbs]
    exact hbound N
  exact congrArg WithAbs.ofAbs (tendsto_nhds_unique hT1 hT2)

end series

end Remark749c

open Remark749c in
/-- **Remark 7.49(c)** (Milne, v3.08, p. 127): a nonarchimedean local field of characteristic $p \ne 0$ is isomorphic
to a field of formal Laurent series $k((T))$ over a finite field $k$. -/
@[kb "milne2020ant" "v3.08, Remark 7.49, p. 127"]
theorem remark7_49c : Remark7_49c := by
  refine ⟨fun K _ v hchar hK => ?_⟩
  have hv := isNonarchimedean_of_ringChar_ne_zero v hchar
  obtain ⟨k, hkfin, hk1, hkex⟩ := exists_teichmuller hv hK hchar
  obtain ⟨π, hπ0, hπ1, hπmax⟩ := exists_uniformizer hv hK
  have := hK.completeSpace
  have hk : ∀ c : k, v c ≤ 1 := by
    intro c
    by_cases h : c = 0
    · subst h; simp
    · exact (hk1 c h).le
  have hπne : π ≠ 0 := fun h => by simp [h] at hπ0
  have hex : ∀ y : K, ∃ c : k, v y ≤ 1 → v (y - c) < 1 := by
    intro y
    by_cases h : v y ≤ 1
    · obtain ⟨c, hc, -⟩ := hkex y h
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose T hT using hex
  have hinj := evalHom_injective hk hπ1 hπne
  let L : LaurentSeries k →+* K := IsFractionRing.lift (A := PowerSeries k) hinj
  have hLa : ∀ f, L (algebraMap (PowerSeries k) (LaurentSeries k) f) = evalHom hk hπ1 f :=
    fun f => IsFractionRing.lift_algebraMap hinj f
  have hsurj : Function.Surjective L := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    obtain ⟨n, hn⟩ := value_eq_zpow hv hK ⟨hπ0, hπ1, hπmax⟩ x hx
    have hu : v (x / π ^ n) ≤ 1 := by
      rw [map_div₀, map_zpow₀, hn, div_self (zpow_pos hπ0 n).ne']
    obtain ⟨f, hf⟩ := exists_series hk hπ1 hπ0 T hT hπmax _ hu
    refine ⟨(algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) ^ n *
      algebraMap (PowerSeries k) (LaurentSeries k) f, ?_⟩
    rw [map_mul, map_zpow₀, hLa, hLa, evalHom_X, hf]
    field_simp
  exact ⟨k, inferInstance, hkfin, ⟨(RingEquiv.ofBijective L ⟨L.injective, hsurj⟩).symm⟩⟩

end NumberFieldKB.MilneANT
