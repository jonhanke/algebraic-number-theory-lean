import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Continuous characters with values in $\mathbb C^\times$

Three facts about continuous homomorphisms into $\mathbb C^\times$ that the theory of Hecke characters uses:

* **No small subgroups** (`MonoidHom.eq_one_of_norm_sub_one_lt`): a homomorphism from a group into $\mathbb C^\times$
  whose values all lie in the disc $|z - 1| < 1/2$ is trivial. The proof is the squaring estimate
  $|z^2 - 1| \ge \tfrac32|z - 1|$ on that disc (`norm_sq_sub_one_ge`).
* **Compact groups are unitary** (`ContinuousMonoidHom.norm_eq_one_of_compactSpace`): a continuous character of a
  compact group has values of absolute value $1$.
* **Characters of a product are trivial on almost all factors**
  (`ContinuousMonoidHom.eventually_comp_mulSingle_eq_one`): a continuous character of a product
  $\prod_i G_i$ of topological groups (product topology) is trivial on $G_i$ for all but finitely many $i$.

The third is the reason a Hecke character is unramified at almost every place. Tau Ceti proves the first in more
generality (`NoSmallSubgroups`, for normed algebras); we prove the special case directly.
-/

namespace NumberFieldKB.HeckeCharacters

open Filter Topology

/-- **The squaring estimate**: on the disc $|z - 1| < 1/2$, $|z^2 - 1| \ge \tfrac32\,|z - 1|$. -/
theorem norm_sq_sub_one_ge {z : ℂ} (hz : ‖z - 1‖ < 1 / 2) : 3 / 2 * ‖z - 1‖ ≤ ‖z ^ 2 - 1‖ := by
  have hfac : z ^ 2 - 1 = (z + 1) * (z - 1) := by ring
  have h2 : (3 : ℝ) / 2 ≤ ‖z + 1‖ := by
    have h := norm_sub_norm_le (2 : ℂ) (-(z - 1))
    have e : (2 : ℂ) - -(z - 1) = z + 1 := by ring
    rw [e, norm_neg, Complex.norm_two] at h
    linarith
  rw [hfac, norm_mul]
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- A complex number all of whose powers lie in the disc $|z - 1| < 1/2$ is $1$. -/
theorem eq_one_of_forall_norm_pow_sub_one_lt {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hsq := norm_sq_sub_one_ge (h (2 ^ k))
      rw [← pow_mul, ← pow_succ] at hsq
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = 3 / 2 * ((3 / 2) ^ k * ‖z - 1‖) := by ring
        _ ≤ 3 / 2 * ‖z ^ (2 ^ k) - 1‖ := by gcongr
        _ ≤ _ := hsq
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ hpos] at hk
  have h1 := key k
  have h2 := h (2 ^ k)
  linarith

/-- **$\mathbb C^\times$ has no small subgroups**: a homomorphism from a monoid into $\mathbb C^\times$ with every value
in the disc $|z - 1| < 1/2$ is trivial. -/
theorem _root_.MonoidHom.eq_one_of_norm_sub_one_lt {G : Type*} [Monoid G] (f : G →* ℂˣ)
    (h : ∀ g, ‖(f g : ℂ) - 1‖ < 1 / 2) : f = 1 := by
  ext g
  refine eq_one_of_forall_norm_pow_sub_one_lt fun n => ?_
  have := h (g ^ n)
  rwa [map_pow, Units.val_pow_eq_pow_val] at this

/-- **A continuous character of a compact group is unitary**: its values have absolute value $1$. -/
theorem _root_.ContinuousMonoidHom.norm_eq_one_of_compactSpace {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] (f : G →ₜ* ℂˣ) (g : G) : ‖(f g : ℂ)‖ = 1 := by
  have hc : Continuous fun x : G => ‖(f x : ℂ)‖ :=
    continuous_norm.comp (Units.continuous_val.comp f.continuous)
  obtain ⟨M, hM⟩ := (isCompact_univ.image hc).isBounded.subset_closedBall 0
  have hb : ∀ x : G, ‖(f x : ℂ)‖ ≤ M := fun x => by
    have := hM ⟨x, Set.mem_univ _, rfl⟩
    rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] at this
  have hnot : ∀ x : G, ¬ 1 < ‖(f x : ℂ)‖ := fun x hx => by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hx
    have := hb (x ^ n)
    rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
    linarith
  have hne : ‖(f g : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (f g).ne_zero
  refine le_antisymm (not_lt.mp (hnot g)) (not_lt.mp fun hlt => hnot g⁻¹ ?_)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv]
  exact one_lt_inv₀ (lt_of_le_of_ne (norm_nonneg _) hne.symm) |>.mpr hlt

/-- **Characters restricted from a product are trivial on almost every factor.** Let $g$ be a continuous map from
$\prod_i G_i$ (product topology) to $\mathbb C^\times$ with $g(1) = 1$, and let $h_i : G_i\to\mathbb C^\times$ be
homomorphisms with $h_i(x) = g(\text{the element } x \text{ in the factor } i)$. Then $h_i = 1$ for all but finitely
many $i$. ($g$ itself need not be a homomorphism.) -/
theorem eventually_eq_one_of_continuous_pi {ι : Type*} [DecidableEq ι]
    {G : ι → Type*} [∀ i, Monoid (G i)] [∀ i, TopologicalSpace (G i)] (g : (∀ i, G i) → ℂˣ)
    (hg : Continuous g) (hg1 : g 1 = 1) (h : ∀ i, G i →* ℂˣ) (hh : ∀ i x, h i x = g (Pi.mulSingle i x)) :
    ∀ᶠ i in cofinite, h i = 1 := by
  set U : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1 / 2}
  have hU : IsOpen U :=
    isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have h1 : g ⁻¹' U ∈ 𝓝 (1 : ∀ i, G i) :=
    hg.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simp [U, hg1]))
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, hI, t, ht, hsub⟩ := h1
  refine hI.eventually_cofinite_notMem.mono fun i hi => ?_
  refine MonoidHom.eq_one_of_norm_sub_one_lt (h i) fun x => ?_
  rw [hh]
  refine hsub fun j hj => ?_
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  simp only [Pi.mulSingle_eq_of_ne hji]
  exact mem_of_mem_nhds (ht j)

/-- **A continuous character of a product is trivial on almost every factor**: for a continuous homomorphism $f$
from $\prod_i G_i$ (product topology) into $\mathbb C^\times$, for all but finitely many $i$ the restriction of $f$ to
the factor $G_i$ is trivial. -/
theorem _root_.ContinuousMonoidHom.eventually_comp_mulSingle_eq_one {ι : Type*} [DecidableEq ι]
    {G : ι → Type*} [∀ i, Monoid (G i)] [∀ i, TopologicalSpace (G i)] (f : (∀ i, G i) →* ℂˣ)
    (hf : Continuous f) : ∀ᶠ i in cofinite, ∀ x : G i, f (Pi.mulSingle i x) = 1 :=
  (eventually_eq_one_of_continuous_pi f hf (map_one f) (fun i => f.comp (MonoidHom.mulSingle G i))
    fun _ _ => rfl).mono fun _ hi x => DFunLike.congr_fun hi x

end NumberFieldKB.HeckeCharacters
