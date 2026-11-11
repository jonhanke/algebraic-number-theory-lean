import Mathlib.NumberTheory.Ostrowski
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import NumberFieldKB.MilneANT.Ch7LocalFields

/-!
# Milne, *Algebraic Number Theory*, Remark 7.49(b): nonarchimedean local fields of characteristic zero

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`,
Remark 7.49(b), p. 127. Page numbers are Milne's printed pages.

**Statement.** A nonarchimedean local field $K$ of characteristic $0$ is a finite extension of $\mathbb Q_p$ for
some prime $p$, and its absolute value is equivalent to the extension of the $p$-adic one
(`NumberFieldKB.MilneANT.Remark7_49b`, proved here as `remark_7_49b`).

**Proof outline** (Milne: the closure of $\mathbb Q$ in $K$ is $\mathbb Q_p$, and $K$ is finite over it by local
compactness).
1. For nonarchimedean $v$ and $n \in \mathbb N$, $v(n) \le 1$ (`Remark749b.nat_le_one`).
2. The restriction of $v$ to $\mathbb Q$ is nontrivial: otherwise the points $c\cdot n$ ($n \in \mathbb N$) of a
   small ball are pairwise at distance $v(c) > 0$, contradicting compactness (`Remark749b.restrict_nontrivial`).
3. Ostrowski (`Rat.AbsoluteValue.equiv_padic_of_bounded`) gives a prime $p$ and $t > 0$ with
   $v|_{\mathbb Q}^t = |\cdot|_p$.
4. Normalise to $w = v^t$ (`Remark749b.rpowAV`, an absolute value since $v$ is ultrametric); $w \sim v$, so
   $K$ is still locally compact, hence complete, for $w$.
5. The isometric embedding $\mathbb Q \to K$ extends by density and completeness to a ring homomorphism
   $\varphi : \mathbb Q_p \to K$ with $w(\varphi x) = \|x\|$ (`Remark749b.exists_padic_embedding`).
6. $K$ is a normed $\mathbb Q_p$-space through $\varphi$ and locally compact, hence finite dimensional
   (`Remark749b.finiteDimensional_of_locallyCompact`, from `FiniteDimensional.of_locallyCompactSpace`).
7. $v\circ\varphi = (\|\cdot\|_p)^{1/t}$, so the two absolute values are equivalent.
-/

namespace NumberFieldKB.MilneANT
namespace Remark749b

variable {K : Type*} [Field K]

/-- The absolute value `v ^ s` for a nonarchimedean `v` and `s > 0`. -/
noncomputable def rpowAV (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (s : ℝ) (hs : 0 < s) :
    AbsoluteValue K ℝ where
  toFun x := v x ^ s
  map_mul' x y := by simp [Real.mul_rpow (v.nonneg x) (v.nonneg y)]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) s
  eq_zero' x := by
    simp [Real.rpow_eq_zero_iff_of_nonneg (v.nonneg x), hs.ne']
  add_le' x y := by
    have h1 : v (x + y) ^ s ≤ (max (v x) (v y)) ^ s :=
      Real.rpow_le_rpow (v.nonneg _) (hv x y) hs.le
    have h2 : (max (v x) (v y)) ^ s = max (v x ^ s) (v y ^ s) :=
      Real.rpow_max (v.nonneg x) (v.nonneg y) hs.le
    have h3 := max_le_add_of_nonneg (Real.rpow_nonneg (v.nonneg x) s)
      (Real.rpow_nonneg (v.nonneg y) s)
    exact h1.trans (h2 ▸ h3)

@[simp] lemma rpowAV_apply (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (s : ℝ) (hs : 0 < s)
    (x : K) : rpowAV v hv s hs x = v x ^ s := rfl

/-- A nonarchimedean absolute value is at most `1` on the natural numbers. -/
lemma nat_le_one {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) (n : ℕ) : v (n : K) ≤ 1 :=
  hv.apply_natCast_le_one (by simp) (by simp)

/-- Local compactness forbids the restriction to `ℚ` being trivial. -/
lemma restrict_nontrivial {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) [CharZero K]
    (h : IsLocalFieldMilne v) :
    (v.comp (algebraMap ℚ K).injective).IsNontrivial := by
  by_contra hnt
  have H : ∀ q : ℚ, q ≠ 0 → v (algebraMap ℚ K q) = 1 := by
    intro q hq
    have := AbsoluteValue.not_isNontrivial_apply hnt hq
    simpa using this
  have := h.locallyCompact
  obtain ⟨s, hs, hs0⟩ := exists_compact_mem_nhds (0 : WithAbs v)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs0
  obtain ⟨x, hx0, hx1⟩ := h.isNontrivial
  obtain ⟨y, hy0, hy1⟩ : ∃ y : K, y ≠ 0 ∧ v y < 1 := by
    rcases lt_or_gt_of_ne hx1 with h' | h'
    · exact ⟨x, hx0, h'⟩
    · refine ⟨x⁻¹, inv_ne_zero hx0, ?_⟩
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h'
  have hy2 : 0 < v y := v.pos hy0
  obtain ⟨N, hN⟩ := (tendsto_pow_atTop_nhds_zero_of_lt_one hy2.le hy1).eventually
    (Iio_mem_nhds hε) |>.exists
  set c : K := y ^ N with hc
  have hcpos : 0 < v c := by rw [hc, map_pow]; positivity
  have hcε : v c < ε := by rw [hc, map_pow]; exact hN
  let a : ℕ → WithAbs v := fun n => WithAbs.toAbs v (c * n)
  have ha : ∀ n, a n ∈ s := by
    intro n
    apply hball
    rw [Metric.mem_ball, dist_zero_right, WithAbs.norm_eq_apply_ofAbs]
    show v (c * n) < ε
    rw [map_mul]
    calc v c * v (n : K) ≤ v c * 1 := by
          gcongr; exact nat_le_one hv n
      _ < ε := by simpa using hcε
  obtain ⟨l, -, φ, hφ, hlim⟩ := hs.tendsto_subseq ha
  have hcau := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hcau
  obtain ⟨M, hM⟩ := hcau (v c) hcpos
  have h1 := hM M le_rfl (M+1) (by omega)
  have hne : φ M ≠ φ (M+1) := (hφ.injective).ne (by omega)
  have : dist ((a ∘ φ) M) ((a ∘ φ) (M+1)) = v c := by
    show dist (a (φ M)) (a (φ (M+1))) = v c
    rw [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs]
    show v (c * (φ M : K) - c * (φ (M+1) : K)) = v c
    rw [← mul_sub, map_mul]
    have : v ((φ M : K) - (φ (M+1) : K)) = 1 := by
      have := H ((φ M : ℚ) - (φ (M+1) : ℚ)) (by
        intro h0
        apply hne
        have : ((φ M : ℚ)) = (φ (M+1) : ℚ) := sub_eq_zero.1 h0
        exact_mod_cast this)
      simpa using this
    rw [this, mul_one]
  rw [this] at h1
  exact lt_irrefl _ h1

open Rat.AbsoluteValue in
/-- If `K` is complete for `w` and `w` restricts to the `p`-adic absolute value on `ℚ`, then `ℚ → K` extends to a
ring homomorphism `ℚ_[p] → K` preserving absolute values. -/
lemma exists_padic_embedding [CharZero K] (p : ℕ) [Fact p.Prime] (w : AbsoluteValue K ℝ)
    [CompleteSpace (WithAbs w)] (hw : ∀ q : ℚ, w (algebraMap ℚ K q) = padicNorm p q) :
    ∃ φ : ℚ_[p] →+* K, ∀ x, w (φ x) = ‖x‖ := by
  let i : WithAbs (padic p) →+* ℚ_[p] :=
    (Rat.castHom ℚ_[p]).comp (WithAbs.equiv (padic p)).toRingHom
  let f : WithAbs (padic p) →+* WithAbs w :=
    (WithAbs.equiv w).symm.toRingHom.comp
      ((algebraMap ℚ K).comp (WithAbs.equiv (padic p)).toRingHom)
  have hi : Isometry i := by
    refine Isometry.of_dist_eq fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs]
    show ‖((x.ofAbs : ℚ) : ℚ_[p]) - ((y.ofAbs : ℚ) : ℚ_[p])‖ = _
    rw [← Rat.cast_sub, Padic.eq_padicNorm]
    rfl
  have hf : Isometry f := by
    refine Isometry.of_dist_eq fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs]
    show w (algebraMap ℚ K (x.ofAbs) - algebraMap ℚ K (y.ofAbs)) = _
    rw [← map_sub, hw]
    rfl
  have ue : IsUniformInducing i := hi.isUniformInducing
  have dr : DenseRange i := by
    have h1 : DenseRange (Rat.cast : ℚ → ℚ_[p]) := Padic.denseRange_ratCast p
    have h2 := (WithAbs.equiv (padic p)).surjective.range_comp (Rat.cast : ℚ → ℚ_[p])
    unfold DenseRange at h1 ⊢
    exact h2 ▸ h1
  let g : ℚ_[p] →+* WithAbs w := IsDenseInducing.extendRingHom ue dr hf.uniformContinuous
  have hg : Continuous g :=
    (uniformContinuous_uniformly_extend ue dr hf.uniformContinuous).continuous
  have hgi : ∀ x, g (i x) = f x := fun x =>
    (ue.isDenseInducing dr).extend_eq hf.continuous x
  refine ⟨(WithAbs.equiv w).toRingHom.comp g, fun x => ?_⟩
  have key : ∀ x, ‖g x‖ = ‖x‖ := by
    intro x
    refine dr.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) fun a => ?_
    rw [hgi, ← dist_zero_right, ← dist_zero_right (a := i a)]
    have := hf.dist_eq a 0
    have h2 := hi.dist_eq a 0
    rw [map_zero] at this h2
    rw [this, h2]
  show w (g x).ofAbs = ‖x‖
  rw [← WithAbs.norm_eq_apply_ofAbs]
  exact key x

/-- If `K` is locally compact for `w`, and `φ : ℚ_[p] → K` is `w`-isometric, then `K` is finite dimensional over
`ℚ_[p]`. -/
lemma finiteDimensional_of_locallyCompact (p : ℕ) [Fact p.Prime] (w : AbsoluteValue K ℝ)
    [LocallyCompactSpace (WithAbs w)] (φ : ℚ_[p] →+* K) (hφ : ∀ x, w (φ x) = ‖x‖) :
    @FiniteDimensional ℚ_[p] K _ _ φ.toModule := by
  let φ' : ℚ_[p] →+* WithAbs w := (WithAbs.equiv w).symm.toRingHom.comp φ
  let _i1 : Module ℚ_[p] (WithAbs w) := φ'.toModule
  let _i2 : NormedSpace ℚ_[p] (WithAbs w) :=
    { norm_smul_le := fun c x => by
        show ‖φ' c * x‖ ≤ ‖c‖ * ‖x‖
        rw [norm_mul]
        have : ‖φ' c‖ = ‖c‖ := by
          rw [WithAbs.norm_eq_apply_ofAbs]
          exact hφ c
        rw [this] }
  have hfd : FiniteDimensional ℚ_[p] (WithAbs w) :=
    FiniteDimensional.of_locallyCompactSpace ℚ_[p]
  let _i3 : Module ℚ_[p] K := φ.toModule
  let e : K ≃ₗ[ℚ_[p]] WithAbs w :=
    { (WithAbs.equiv w).symm.toAddEquiv with
      map_smul' := fun c x => rfl }
  exact e.symm.finiteDimensional

end Remark749b

/-- **Remark 7.49(b).** A nonarchimedean local field $K$ of characteristic zero is a finite extension of
$\mathbb Q_p$ for some prime $p$, and its absolute value is equivalent to the extension of the $p$-adic absolute
value. Proof: the restriction to $\mathbb Q$ is nontrivial by local compactness, hence $p$-adic up to a power by
Ostrowski; after normalising, $\mathbb Q \to K$ extends to $\mathbb Q_p \to K$ by completeness, and $K$ is finite
dimensional over $\mathbb Q_p$ because it is a locally compact normed $\mathbb Q_p$-space. -/
@[kb "milne2020ant" "v3.08, Remark 7.49, p. 127"]
theorem remark_7_49b : Remark7_49b := by
  refine ⟨fun K _ _ v hv h => ?_⟩
  have hu := Remark749b.restrict_nontrivial hv h
  have hbdd : ∀ n : ℕ, (v.comp (algebraMap ℚ K).injective) n ≤ 1 := fun n => by
    simpa using Remark749b.nat_le_one hv n
  obtain ⟨p, ⟨hp, heq⟩, -⟩ := Rat.AbsoluteValue.equiv_padic_of_bounded hu hbdd
  obtain ⟨t, ht, hpt⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 heq
  have hw : ∀ q : ℚ, (Remark749b.rpowAV v hv t ht) (algebraMap ℚ K q) = padicNorm p q := by
    intro q
    have := congrFun hpt q
    simpa using this
  have hvw : v.IsEquiv (Remark749b.rpowAV v hv t ht) :=
    AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨t, ht, rfl⟩
  have hlc : LocallyCompactSpace (WithAbs (Remark749b.rpowAV v hv t ht)) := by
    have h1 := (AbsoluteValue.isEquiv_iff_isHomeomorph _ _).1 hvw
    have := h.locallyCompact
    exact h1.homeomorph.symm.isOpenEmbedding.locallyCompactSpace
  have hcomp : CompleteSpace (WithAbs (Remark749b.rpowAV v hv t ht)) :=
    IsLeftUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace _
  obtain ⟨φ, hφ⟩ := Remark749b.exists_padic_embedding p (Remark749b.rpowAV v hv t ht) hw
  refine ⟨p, hp, φ, Remark749b.finiteDimensional_of_locallyCompact p _ φ hφ, ?_⟩
  rw [AbsoluteValue.isEquiv_iff_exists_rpow_eq]
  exact ⟨t, ht, funext fun x => hφ x⟩

end NumberFieldKB.MilneANT
