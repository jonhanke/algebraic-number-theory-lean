import NumberFieldKB.Chebotarev.PrimeDensity
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Equidistribution of primes from character sums
$F$ is a number field and $f$ assigns to each nonzero prime $\mathfrak p$ of $\mathcal O_F$ an element of a finite
abelian group. The orthogonality relations turn bounds on character sums into densities:

* **`hasDirichletDensity_fibre_of_subgroup`**: $M$ a finite commutative monoid (e.g. `ZMod m`, whose characters are
  Mathlib's Dirichlet characters), $H\le M^\times$, $f(\mathfrak p)\in H$ for all $\mathfrak p$. If for every
  character $\chi$ of $M$ that is non-trivial on $H$ the sum $\sum_{\mathfrak p}\chi(f(\mathfrak p))N\mathfrak p^{-s}$ is
  $O(1)$ as $s\to1^+$, then every fibre $\{f = h\}$, $h\in H$, has Dirichlet density $1/|H|$.
* **`hasDirichletDensity_fibre`**: the case of a finite abelian group $G$ and $H = G$: if
  $\sum_{\mathfrak p}\psi(f(\mathfrak p))N\mathfrak p^{-s} = O(1)$ for every character $\psi\ne1$ of $G$, each fibre
  of $f$ has density $1/|G|$.
* The orthogonality relation used, `sum_mulChar_apply_units`: $\sum_\chi\chi(u) = |M^\times|\,[u = 1]$
  (Mathlib proves it for Dirichlet characters, `DirichletCharacter.sum_characters_eq`; this is the same proof for any
  finite commutative monoid).

The trivial character contributes $P(s) = \sum_{\mathfrak p}N\mathfrak p^{-s}$, and the characters trivial on $H$ form
a group of order $[M^\times:H]$ (Mathlib's `MulChar.card_subgroupOrderIsoSubgroupMulChar`); this is where
$1/|H|$ comes from.
-/

open Complex Filter Topology Asymptotics IsDedekindDomain NumberField Set
open QuadFormsKB.NFEuler NumberFieldKB.NonVanishing

namespace NumberFieldKB.Chebotarev

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Orthogonality -/

section Orthogonality

variable {M : Type*} [CommMonoid M] [Finite M]

instance (priority := 100) neZero_exponent_units_complex : NeZero ((Monoid.exponent Mˣ : ℕ) : ℂ) :=
  ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩

/-- $\sum_\chi\chi(u) = 0$ for a unit $u\ne1$ of a finite commutative monoid. -/
theorem sum_mulChar_apply_units_eq_zero [Fintype (MulChar M ℂ)] {u : Mˣ} (hu : u ≠ 1) :
    ∑ χ : MulChar M ℂ, χ u = 0 := by
  have hu' : (u : M) ≠ 1 := fun h => hu (Units.val_eq_one.mp h)
  obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity M ℂ hu'
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

open scoped Classical in
/-- **Orthogonality**: $\sum_\chi\chi(u) = |M^\times|$ if $u = 1$, else $0$. -/
theorem sum_mulChar_apply_units [Fintype (MulChar M ℂ)] (u : Mˣ) :
    ∑ χ : MulChar M ℂ, χ u = if u = 1 then (Nat.card Mˣ : ℂ) else 0 := by
  split_ifs with hu
  · subst hu
    simp only [Units.val_one, map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [← Nat.card_eq_fintype_card, MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity M ℂ]
  · exact sum_mulChar_apply_units_eq_zero hu

theorem norm_mulChar_apply_units (χ : MulChar M ℂ) (u : Mˣ) : ‖χ u‖ = 1 := by
  have : Fintype Mˣ := Fintype.ofFinite _
  have h := congrArg (fun ψ : MulChar M ℂ => ψ u) χ.pow_card_eq_one
  simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at h
  exact Complex.norm_eq_one_of_pow_eq_one h Fintype.card_ne_zero

end Orthogonality

/-! ### Densities of fibres -/

variable {F : Type} [Field F] [NumberField F]

local notation "Pr" => HeightOneSpectrum (𝓞 F)

/-- The prime sum of an indicator: $\sum_{\mathfrak p}\mathbf 1_S(\mathfrak p)N\mathfrak p^{-s} = P_S(s)$. -/
theorem primeSum_indicator (S : Set Pr) (s : ℝ) :
    primeSum (S.indicator fun _ => (1 : ℂ)) s = (S.primeIdealZetaSum s : ℂ) := by
  rw [primeIdealZetaSum_eq_tsum_indicator, Complex.ofReal_tsum, primeSum]
  congr 1
  funext v
  by_cases hv : v ∈ S
  · rw [indicator_of_mem hv, indicator_of_mem hv, one_mul, nps, Complex.ofReal_cpow (by positivity),
      Complex.ofReal_neg]
  · rw [indicator_of_notMem hv, indicator_of_notMem hv, zero_mul, Complex.ofReal_zero]

/-- **Equidistribution in a subgroup from character sums.** Let $M$ be a finite commutative monoid,
$H\le M^\times$, and $f(\mathfrak p)\in H$ for every prime $\mathfrak p$. If
$\sum_{\mathfrak p}\chi(f(\mathfrak p))N\mathfrak p^{-s} = O(1)$ as $s\to1^+$ for every character $\chi$ of $M$
that is non-trivial on $H$, then each fibre $\{\mathfrak p : f(\mathfrak p) = h\}$, $h\in H$, has Dirichlet density
$1/|H|$. -/
@[kb "neukirch1999" "Ch. VII, §13 (Dirichlet density from L-function bounds via orthogonality) [unverified locator]"]
theorem hasDirichletDensity_fibre_of_subgroup {M : Type*} [CommMonoid M] [Finite M] (H : Subgroup Mˣ)
    (f : Pr → Mˣ) (hf : ∀ v, f v ∈ H)
    (hχ : ∀ χ : MulChar M ℂ, (∃ h ∈ H, χ h ≠ 1) →
      (fun s : ℝ => primeSum (fun v => χ (f v)) s) =O[𝓝[>] 1] (fun _ => (1 : ℂ)))
    {g : Mˣ} (hg : g ∈ H) : {v | f v = g}.HasDirichletDensity (1 / Nat.card H) := by
  classical
  have : Fintype (MulChar M ℂ) := Fintype.ofFinite _
  have : Finite Mˣ := inferInstance
  set A : Finset (MulChar M ℂ) := Finset.univ.filter fun χ => ∀ h ∈ H, χ h = 1
  set S : Set Pr := {v | f v = g}
  set P : ℝ → ℝ := fun s => (univ : Set Pr).primeIdealZetaSum s
  set n : ℕ := Nat.card Mˣ
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hnH : (Nat.card H : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  -- the characters trivial on `H`: `|A| = [Mˣ : H]`
  have hA : (A.card : ℝ) * Nat.card H = n := by
    have h1 := MulChar.card_subgroupOrderIsoSubgroupMulChar (M := M) (R := ℂ) (H := H)
    have h2 : Nat.card (MulChar.subgroupOrderIsoSubgroupMulChar M ℂ H).ofDual = A.card := by
      rw [← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun χ => by
        simp [A, MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff])
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup H
    rw [h1] at h2
    simp only [n]
    rw [h3, ← h2]
    push_cast; ring
  -- summability of the character sums
  have hnorm : ∀ χ : MulChar M ℂ, ∀ v, ‖χ (f v)‖ ≤ 1 := fun χ v => (norm_mulChar_apply_units χ (f v)).le
  -- the key identity, for `s > 1`:
  -- `∑_χ χ(g⁻¹) X_χ(s) = |Mˣ| P_S(s)` and `X_χ(s) = P(s)` for `χ ∈ A`
  have hkey : ∀ s : ℝ, 1 < s → ∑ χ : MulChar M ℂ, χ (g⁻¹ : Mˣ) * primeSum (fun v => χ (f v)) s =
      n * (S.primeIdealZetaSum s : ℂ) := fun s hs => by
    have hs' : 1 < (s : ℂ).re := by simpa using hs
    simp only [primeSum]
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum fun χ _ => ((summable_mul_nps (hnorm χ) hs').mul_left _)]
    rw [← primeSum_indicator, primeSum, ← tsum_mul_left]
    congr 1
    funext v
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    have : ∑ χ : MulChar M ℂ, χ (g⁻¹ : Mˣ) * χ (f v) = ∑ χ : MulChar M ℂ, χ ((g⁻¹ * f v : Mˣ) : M) := by
      simp [Units.val_mul, map_mul]
    rw [this]
    simp only [sum_mulChar_apply_units, inv_mul_eq_one]
    by_cases hv : v ∈ S
    · have hv' : g = f v := (show f v = g from hv).symm
      rw [if_pos hv', indicator_of_mem hv]; ring
    · have hv' : ¬ g = f v := fun h => hv h.symm
      rw [if_neg hv', indicator_of_notMem hv]; ring
  have htriv : ∀ χ ∈ A, ∀ s : ℝ, χ (g⁻¹ : Mˣ) * primeSum (fun v => χ (f v)) s = (P s : ℂ) := by
    intro χ hχA s
    have hχ1 : ∀ h ∈ H, χ h = 1 := (Finset.mem_filter.mp hχA).2
    rw [hχ1 _ (H.inv_mem hg), one_mul, primeIdealZetaSum_univ_eq]
    congr 1
    funext v
    exact hχ1 _ (hf v)
  -- the non-trivial characters contribute `O(1)`
  have hrest : (fun s : ℝ => ∑ χ ∈ Finset.univ \ A, χ (g⁻¹ : Mˣ) * primeSum (fun v => χ (f v)) s)
      =O[𝓝[>] 1] (fun _ => (1 : ℂ)) := by
    refine IsBigO.fun_sum fun χ hχmem => ?_
    have hχA : ¬ ∀ h ∈ H, χ h = 1 := by simpa [A] using hχmem
    push_neg at hχA
    exact (hχ χ hχA).const_mul_left _
  -- assemble: `|Mˣ| P_S - |A| P = O(1)`
  have hmain : (fun s : ℝ => (n : ℂ) * (S.primeIdealZetaSum s : ℂ) - A.card * (P s : ℂ))
      =O[𝓝[>] 1] (fun _ => (1 : ℂ)) := by
    refine hrest.congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [← hkey s hs, ← Finset.sum_sdiff (Finset.subset_univ A), Finset.sum_congr rfl fun χ hχ => htriv χ hχ s,
      Finset.sum_const, nsmul_eq_mul]
    ring
  refine hasDirichletDensity_of_isBigO ?_
  have hre : (fun s : ℝ => S.primeIdealZetaSum s - 1 / (Nat.card H) * P s) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    have h2 : (fun s : ℝ => ((n : ℂ)⁻¹ * ((n : ℂ) * (S.primeIdealZetaSum s : ℂ) - A.card * (P s : ℂ))))
        =O[𝓝[>] 1] (fun _ => (1 : ℂ)) := hmain.const_mul_left _
    refine IsBigO.trans ?_ (h2.trans (isBigO_of_le _ fun _ => by simp))
    refine isBigO_of_le _ fun s => le_of_eq ?_
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hcoef : (A.card : ℝ) / n = 1 / Nat.card H := by
      rw [div_eq_div_iff hnR hnH, one_mul]; exact hA
    rw [show (n : ℂ)⁻¹ * ((n : ℂ) * (S.primeIdealZetaSum s : ℂ) - A.card * (P s : ℂ)) =
        ((S.primeIdealZetaSum s - (A.card : ℝ) / n * P s : ℝ) : ℂ) by push_cast; field_simp,
      Complex.norm_real, hcoef]
  exact hre

/-- **Equidistribution in a finite abelian group.** If $f$ maps primes to a finite abelian group $G$ and
$\sum_{\mathfrak p}\psi(f(\mathfrak p))N\mathfrak p^{-s} = O(1)$ as $s\to1^+$ for every character $\psi\ne1$ of $G$,
then each fibre of $f$ has Dirichlet density $1/|G|$. -/
theorem hasDirichletDensity_fibre {G : Type*} [CommGroup G] [Finite G] (f : Pr → G)
    (hψ : ∀ ψ : MulChar G ℂ, ψ ≠ 1 →
      (fun s : ℝ => primeSum (fun v => ψ (f v)) s) =O[𝓝[>] 1] (fun _ => (1 : ℂ)))
    (g : G) : {v | f v = g}.HasDirichletDensity (1 / Nat.card G) := by
  have h := hasDirichletDensity_fibre_of_subgroup (M := G) ⊤ (fun v => toUnits (f v)) (fun _ => trivial)
    (fun χ ⟨h, _, hh⟩ => by
      refine hψ χ fun h1 => hh ?_
      rw [h1, MulChar.one_apply_coe]) (g := toUnits g) trivial
  have hS : {v | toUnits (f v) = toUnits g} = {v : Pr | f v = g} := by
    ext v; simp
  have hc : Nat.card (⊤ : Subgroup Gˣ) = Nat.card G := by
    rw [Subgroup.card_top]; exact Nat.card_congr toUnits.toEquiv.symm
  rwa [hS, hc] at h

end

end NumberFieldKB.Chebotarev
