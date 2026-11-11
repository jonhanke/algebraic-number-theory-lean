import NumberFieldKB.MilneANT.Ch8Prop810
import NumberFieldKB.MilneANT.Ch7OstrowskiFinite
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Milne, *Algebraic Number Theory*, Remark 8.3: extensions of the $\mathfrak p$-adic absolute value

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), bib key `milne2020ant`, Remark 8.3, p. 136.

For an extension $L/K$ of number fields and a prime $\mathfrak p$ of $K$, the extensions of
$\lVert\cdot\rVert_{\mathfrak p}$ to $L$ correspond to the primes $\mathfrak P \mid \mathfrak p$, and the local degree
$[L_w : K_{\mathfrak p}]$ is $e(\mathfrak P/\mathfrak p) f(\mathfrak P/\mathfrak p)$. Outline:

* `Remark83.exists_unique_prime_of_extension`: an extension $w$ is nonarchimedean and nontrivial, hence (Ostrowski,
  `exists_finitePlace_isEquiv`) equivalent to some $\lVert\cdot\rVert_{\mathfrak P}$; $\mathfrak P$ lies over
  $\mathfrak p$ and is unique (same elements of value $<1$).
* `Remark83.existsUnique_extension_of_prime`: conversely $\lVert\cdot\rVert_{\mathfrak P}^{1/(ef)}$ extends
  $\lVert\cdot\rVert_{\mathfrak p}$ (Mathlib's formula $\lVert x\rVert_{\mathfrak P} = \lVert x\rVert_{\mathfrak p}^{ef}$),
  and two equivalent extensions of a nontrivial absolute value coincide. Together: `Remark83.extensionsEquivPrimesOver`.
* `Remark83.finrank_completion_of_lowerBound`: from the lower bound `LocalDegreeLowerBound`
  ($ef \le [L_w:K_{\mathfrak p}]$), Proposition 8.2 ($\sum_w [L_w : K_{\mathfrak p}] = [L:K]$) and
  $\sum_{\mathfrak P} ef = [L:K]$, equality holds termwise.
* `remark_8_3_of_lowerBound`: the degree of the minimal polynomial of $\alpha$ over $K_{\mathfrak p}$ in $L_w$ is
  $[L_w:K_{\mathfrak p}]$ (Proposition 8.1, `Prop81.hMap_bijective`).

The hypothesis $\mathcal O_L = \mathcal O_K[\alpha]$ is only used to see that $\alpha$ generates $L$ over $K$
(`Remark83.adjoin_eq_top_of_adjoin`); the result holds for any primitive $\alpha \in \mathcal O_L$.
-/

open NumberField IsDedekindDomain
open scoped TensorProduct Polynomial

namespace NumberFieldKB.MilneANT

noncomputable section

/-- The lower bound e f ≤ [L_w : K_𝔭] (proved in `Ch8LocalDegreeLower.lean`). -/
def LocalDegreeLowerBound : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L)) [P.asIdeal.LiesOver 𝔭.asIdeal]
    (w : Extensions L (FinitePlace.mk 𝔭).1), w.1.IsEquiv (FinitePlace.mk P).1 →
    letI := extAlgebra (FinitePlace.mk 𝔭).1 w
    P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) ≤
      Module.finrank (FinitePlace.mk 𝔭).1.Completion w.1.Completion

namespace Remark83

section Rpow

variable {F : Type*} [Field F]

/-- A positive real power of a nonarchimedean absolute value is an absolute value. -/
def rpowAbv (w : AbsoluteValue F ℝ) (hna : IsNonarchimedean w) (s : ℝ) (hs : 0 < s) :
    AbsoluteValue F ℝ where
  toFun x := w x ^ s
  map_mul' x y := by simp [map_mul, Real.mul_rpow (w.nonneg x) (w.nonneg y)]
  nonneg' x := Real.rpow_nonneg (w.nonneg x) s
  eq_zero' x := by
    constructor
    · intro h
      exact w.eq_zero.1 ((Real.rpow_eq_zero (w.nonneg x) hs.ne').1 h)
    · rintro rfl
      simp [Real.zero_rpow hs.ne']
  add_le' x y := by
    have hx := Real.rpow_nonneg (w.nonneg x) s
    have hy := Real.rpow_nonneg (w.nonneg y) s
    calc w (x + y) ^ s ≤ (max (w x) (w y)) ^ s :=
          Real.rpow_le_rpow (w.nonneg _) (hna x y) hs.le
      _ ≤ w x ^ s + w y ^ s := by
        rcases le_total (w x) (w y) with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; linarith

theorem rpowAbv_apply (w : AbsoluteValue F ℝ) (hna : IsNonarchimedean w) (s : ℝ) (hs : 0 < s)
    (x : F) : rpowAbv w hna s hs x = w x ^ s := rfl

end Rpow

section Basic

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem apply_algebraMap_of_liesOver {v : AbsoluteValue K ℝ} (w : AbsoluteValue L ℝ)
    [w.LiesOver v] (x : K) : w (algebraMap K L x) = v x :=
  congrArg (fun u : AbsoluteValue K ℝ => u x) (AbsoluteValue.LiesOver.under_eq w v)

theorem mk_apply_algebraMap (𝔭 : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver 𝔭.asIdeal] (x : K) :
    (FinitePlace.mk P).1 (algebraMap K L x) =
      (FinitePlace.mk 𝔭).1 x ^ (P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K)) :=
  FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap 𝔭 P x

omit [NumberField K] [NumberField L] in
theorem algebraMap_comm (x : 𝓞 K) :
    algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) x) = algebraMap K L (algebraMap (𝓞 K) K x) := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L, IsScalarTower.algebraMap_apply (𝓞 K) K L]

theorem liesOver_of_isEquiv (𝔭 : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L))
    (w : AbsoluteValue L ℝ) [w.LiesOver (FinitePlace.mk 𝔭).1] (h : w.IsEquiv (FinitePlace.mk P).1) :
    P.asIdeal.LiesOver 𝔭.asIdeal := by
  refine ⟨?_⟩
  ext x
  rw [Ideal.mem_comap, ← FinitePlace.norm_lt_one_iff_mem L P, algebraMap_comm]
  rw [← FinitePlace.norm_lt_one_iff_mem K 𝔭]
  change (FinitePlace.mk 𝔭).1 _ < 1 ↔ (FinitePlace.mk P).1 _ < 1
  rw [← apply_algebraMap_of_liesOver (v := (FinitePlace.mk 𝔭).1) w, h.lt_one_iff]

theorem isNonarchimedean_mk (𝔭 : HeightOneSpectrum (𝓞 K)) : IsNonarchimedean (FinitePlace.mk 𝔭).1 :=
  fun x y => FinitePlace.add_le (FinitePlace.mk 𝔭) x y

theorem eq_of_isEquiv_of_liesOver {v : AbsoluteValue K ℝ} (hv : v.IsNontrivial)
    (w₁ w₂ : AbsoluteValue L ℝ) [w₁.LiesOver v] [w₂.LiesOver v] (h : w₁.IsEquiv w₂) : w₁ = w₂ := by
  obtain ⟨c, hc, hw⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 h
  obtain ⟨x, hx0, hx1⟩ := hv
  have h1 : v x ^ c = v x := by
    have := congr_fun hw (algebraMap K L x)
    rwa [apply_algebraMap_of_liesOver (v := v) w₁, apply_algebraMap_of_liesOver (v := v) w₂] at this
  have hpos : 0 < v x := v.pos hx0
  have hlog : Real.log (v x) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos hx1
  have h2 : Real.log (v x) = c * Real.log (v x) := by
    conv_lhs => rw [← h1]
    exact Real.log_rpow hpos c
  have hc1 : c = 1 := by
    have : (1 - c) * Real.log (v x) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hlog
  subst hc1
  refine AbsoluteValue.ext fun y => ?_
  have := congr_fun hw y
  simpa using this

theorem eq_of_isEquiv_mk {P Q : HeightOneSpectrum (𝓞 L)}
    (h : (FinitePlace.mk P).1.IsEquiv (FinitePlace.mk Q).1) : P = Q := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [← FinitePlace.norm_lt_one_iff_mem L P, ← FinitePlace.norm_lt_one_iff_mem L Q]
  exact h.lt_one_iff

/-- **Remark 8.3, part 1.** Every extension $w$ of $\lVert\cdot\rVert_{\mathfrak p}$ to $L$ is equivalent to
$\lVert\cdot\rVert_{\mathfrak P}$ for exactly one prime $\mathfrak P$ of $L$, and $\mathfrak P$ lies over
$\mathfrak p$. -/
@[kb "milne2020ant" "v3.08, Rem. 8.3, p. 136"]
theorem exists_unique_prime_of_extension (𝔭 : HeightOneSpectrum (𝓞 K))
    (w : Extensions L (FinitePlace.mk 𝔭).1) :
    ∃! P : HeightOneSpectrum (𝓞 L),
      P.asIdeal.LiesOver 𝔭.asIdeal ∧ w.1.IsEquiv (FinitePlace.mk P).1 := by
  have := w.2
  have hna : IsNonarchimedean w.1 := by
    apply isNonarchimedean_of_natCast_le_one
    intro n
    have : w.1 (n : L) = (FinitePlace.mk 𝔭).1 (n : K) := by
      rw [← map_natCast (algebraMap K L) n]
      exact apply_algebraMap_of_liesOver (v := (FinitePlace.mk 𝔭).1) w.1 _
    rw [this]
    exact (isNonarchimedean_mk 𝔭).apply_natCast_le_one (by simp) (by simp)
  have hnt : w.1.IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ := FinitePlace.isNontrivial_milne K (FinitePlace.mk 𝔭)
    refine ⟨algebraMap K L x, by simpa using hx0, ?_⟩
    rw [apply_algebraMap_of_liesOver (v := (FinitePlace.mk 𝔭).1) w.1]
    exact hx1
  obtain ⟨Pl, hPl⟩ := exists_finitePlace_isEquiv w.1 hnt hna
  have h' : w.1.IsEquiv (FinitePlace.mk (FinitePlace.maximalIdeal Pl)).1 := by
    rw [FinitePlace.mk_maximalIdeal]
    exact hPl
  refine ⟨FinitePlace.maximalIdeal Pl, ⟨liesOver_of_isEquiv 𝔭 _ w.1 h', h'⟩, ?_⟩
  rintro Q ⟨-, hQ⟩
  exact eq_of_isEquiv_mk (hQ.symm.trans h')

/-- **Remark 8.3, existence**: for a prime $\mathfrak P$ of $L$ over $\mathfrak p$, the extension of
$\lVert\cdot\rVert_{\mathfrak p}$ to $L$ equivalent to $\lVert\cdot\rVert_{\mathfrak P}$ exists and is unique:
it is $\lVert\cdot\rVert_{\mathfrak P}^{1/(e f)}$. -/
@[kb "milne2020ant" "v3.08, Rem. 8.3, p. 136"]
theorem existsUnique_extension_of_prime (𝔭 : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver 𝔭.asIdeal] :
    ∃! w : Extensions L (FinitePlace.mk 𝔭).1, w.1.IsEquiv (FinitePlace.mk P).1 := by
  set e := P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) with he
  have hepos : 0 < (e : ℝ) := by
    have : 0 < e := mul_pos (P.asIdeal.ramificationIdx_pos (𝓞 K)) (P.asIdeal.inertiaDeg_pos (𝓞 K))
    exact_mod_cast this
  have hs : 0 < 1 / (e : ℝ) := by positivity
  let w0 := rpowAbv (FinitePlace.mk P).1 (isNonarchimedean_mk P) (1 / (e : ℝ)) hs
  have hlies : w0.LiesOver (FinitePlace.mk 𝔭).1 := by
    refine ⟨AbsoluteValue.ext fun x => ?_⟩
    change w0 (algebraMap K L x) = _
    rw [rpowAbv_apply, mk_apply_algebraMap 𝔭 P x, ← Real.rpow_natCast, ← Real.rpow_mul
      ((FinitePlace.mk 𝔭).1.nonneg x), mul_one_div_cancel hepos.ne', Real.rpow_one]
  have hequiv : w0.IsEquiv (FinitePlace.mk P).1 := by
    refine AbsoluteValue.isEquiv_iff_exists_rpow_eq.2 ⟨(e : ℝ), hepos, funext fun x => ?_⟩
    rw [rpowAbv_apply, ← Real.rpow_mul ((FinitePlace.mk P).1.nonneg x), one_div_mul_cancel hepos.ne',
      Real.rpow_one]
  refine ⟨⟨w0, hlies⟩, hequiv, ?_⟩
  rintro ⟨w1, hw1⟩ h1
  have := hw1
  refine Subtype.ext ?_
  exact eq_of_isEquiv_of_liesOver (FinitePlace.isNontrivial_milne K (FinitePlace.mk 𝔭)) w1 w0
    (h1.trans hequiv.symm)

/-- The bijection between the extensions of $\lVert\cdot\rVert_{\mathfrak p}$ to $L$ and the primes of $L$ above
$\mathfrak p$ (Remark 8.3). -/
@[kb "milne2020ant" "v3.08, Rem. 8.3, p. 136"]
def extensionsEquivPrimesOver (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Extensions L (FinitePlace.mk 𝔭).1 ≃ {P : HeightOneSpectrum (𝓞 L) // P.asIdeal.LiesOver 𝔭.asIdeal} where
  toFun w := ⟨(exists_unique_prime_of_extension 𝔭 w).exists.choose,
    (exists_unique_prime_of_extension 𝔭 w).exists.choose_spec.1⟩
  invFun P := by
    haveI := P.2
    exact (existsUnique_extension_of_prime 𝔭 P.1).exists.choose
  left_inv w := by
    obtain ⟨hl, he⟩ := (exists_unique_prime_of_extension 𝔭 w).exists.choose_spec
    have := hl
    exact ((existsUnique_extension_of_prime 𝔭
      (exists_unique_prime_of_extension 𝔭 w).exists.choose).unique
      (existsUnique_extension_of_prime 𝔭 _).exists.choose_spec he)
    -- (extension attached to the prime of `w`) = `w`
  right_inv P := by
    have := P.2
    refine Subtype.ext ?_
    set w := (existsUnique_extension_of_prime 𝔭 P.1).exists.choose with hw
    have hwP : w.1.IsEquiv (FinitePlace.mk P.1).1 :=
      (existsUnique_extension_of_prime 𝔭 P.1).exists.choose_spec
    exact (exists_unique_prime_of_extension 𝔭 w).unique
      (exists_unique_prime_of_extension 𝔭 w).exists.choose_spec ⟨P.2, hwP⟩

end Basic

section Degree

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The primes of $L$ over $\mathfrak p$ (as height-one primes) are the elements of `primesOver`. -/
def primesOverEquiv (𝔭 : HeightOneSpectrum (𝓞 K)) :
    {P : HeightOneSpectrum (𝓞 L) // P.asIdeal.LiesOver 𝔭.asIdeal} ≃ 𝔭.asIdeal.primesOver (𝓞 L) where
  toFun P := ⟨P.1.asIdeal, P.1.isPrime, P.2⟩
  invFun Q := ⟨⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver 𝔭.ne_bot Q.2⟩, Q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_extensions (v : AbsoluteValue K ℝ) : Finite (Extensions L v) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  exact Finite.of_equiv _ (Prop81.corrEquiv v hα).symm

/-- $\sum_w [L_w : K_v] = [L : K]$ (from Proposition 8.2). -/
theorem sum_finrank_completion (v : AbsoluteValue K ℝ) [Fintype (Extensions L v)] :
    letI : ∀ w : Extensions L v, Algebra v.Completion w.1.Completion := extAlgebra v
    ∑ w : Extensions L v, Module.finrank v.Completion w.1.Completion = Module.finrank K L := by
  classical
  let _ : ∀ w : Extensions L v, Algebra v.Completion w.1.Completion := extAlgebra v
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  obtain ⟨e0, -⟩ := exists_tensor_algEquiv_pi v.Completion hα
  let e1 : (w : Extensions L v) → AdjoinRoot (Prop81.phi v w α).1 ≃ₐ[v.Completion] w.1.Completion :=
    fun w => AlgEquiv.ofBijective (Prop81.hMap v w α) (Prop81.hMap_bijective v hα w)
  let e : v.Completion ⊗[K] L ≃ₐ[v.Completion] ((w : Extensions L v) → w.1.Completion) :=
    e0.trans ((AlgEquiv.piCongrLeft v.Completion (fun g : Prop81.Fac v α => AdjoinRoot g.1)
      (Prop81.corrEquiv v hα)).symm.trans (AlgEquiv.piCongrRight e1))
  have hfin : ∀ w : Extensions L v, Module.Finite v.Completion w.1.Completion := fun w =>
    Module.Finite.of_surjective ((LinearMap.proj w).comp e.toLinearMap)
      ((Function.surjective_eval w).comp e.surjective)
  have hfree : ∀ w : Extensions L v, Module.Free v.Completion w.1.Completion := fun w =>
    Module.Free.of_divisionRing _ _
  calc ∑ w : Extensions L v, Module.finrank v.Completion w.1.Completion
      = Module.finrank v.Completion ((w : Extensions L v) → w.1.Completion) :=
        (Module.finrank_pi_fintype v.Completion).symm
    _ = Module.finrank v.Completion (v.Completion ⊗[K] L) := (LinearEquiv.finrank_eq e.toLinearEquiv).symm
    _ = Module.finrank K L := Module.finrank_baseChange

/-- **Local degree** (conditional on the lower bound `LocalDegreeLowerBound`): if $w$ is the extension of
$\lVert\cdot\rVert_{\mathfrak p}$ attached to the prime $\mathfrak P$ over $\mathfrak p$, then
$[L_w : K_{\mathfrak p}] = e(\mathfrak P/\mathfrak p) f(\mathfrak P/\mathfrak p)$. Summing the lower bound over
$w$ gives $\sum_w [L_w:K_{\mathfrak p}] = [L:K] = \sum_{\mathfrak P} e f$, forcing equality termwise. -/
@[kb "milne2020ant" "v3.08, Rem. 8.3, p. 136"]
theorem finrank_completion_of_lowerBound (h : LocalDegreeLowerBound)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L)) [P.asIdeal.LiesOver 𝔭.asIdeal]
    (w : Extensions L (FinitePlace.mk 𝔭).1) (hw : w.1.IsEquiv (FinitePlace.mk P).1) :
    letI := extAlgebra (FinitePlace.mk 𝔭).1 w
    Module.finrank (FinitePlace.mk 𝔭).1.Completion w.1.Completion =
      P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) := by
  classical
  have hfinite := finite_extensions (K := K) (L := L) (FinitePlace.mk 𝔭).1
  let _ := Fintype.ofFinite (Extensions L (FinitePlace.mk 𝔭).1)
  let _ : ∀ w : Extensions L (FinitePlace.mk 𝔭).1, Algebra (FinitePlace.mk 𝔭).1.Completion
      w.1.Completion := extAlgebra (FinitePlace.mk 𝔭).1
  let prim : Extensions L (FinitePlace.mk 𝔭).1 → HeightOneSpectrum (𝓞 L) := fun w =>
    (extensionsEquivPrimesOver 𝔭 w).1
  have hprim : ∀ w, (prim w).asIdeal.LiesOver 𝔭.asIdeal ∧ w.1.IsEquiv (FinitePlace.mk (prim w)).1 :=
    fun w => (exists_unique_prime_of_extension 𝔭 w).exists.choose_spec
  have hle : ∀ w : Extensions L (FinitePlace.mk 𝔭).1,
      (prim w).asIdeal.ramificationIdx (𝓞 K) * (prim w).asIdeal.inertiaDeg (𝓞 K) ≤
        Module.finrank (FinitePlace.mk 𝔭).1.Completion w.1.Completion := fun w => by
    have := (hprim w).1
    exact h K L 𝔭 (prim w) w (hprim w).2
  have hsum1 := sum_finrank_completion (K := K) (L := L) (FinitePlace.mk 𝔭).1
  have hsum2 : ∑ w : Extensions L (FinitePlace.mk 𝔭).1,
      (prim w).asIdeal.ramificationIdx (𝓞 K) * (prim w).asIdeal.inertiaDeg (𝓞 K) =
        Module.finrank K L := by
    rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L,
      ← Ideal.sum_ramification_inertia_eq_finrank 𝔭.asIdeal (𝓞 L)]
    exact Fintype.sum_equiv ((extensionsEquivPrimesOver 𝔭).trans (primesOverEquiv 𝔭)) _ _
      (fun w => rfl)
  have heq := (Finset.sum_eq_sum_iff_of_le (fun w _ => hle w)).1 (hsum2.trans hsum1.symm) w
    (Finset.mem_univ _)
  have hP : P = prim w := (exists_unique_prime_of_extension 𝔭 w).unique ⟨inferInstance, hw⟩ (hprim w)
  rw [← heq, hP]

omit [NumberField K] in
/-- If $\mathcal O_L =\mathcal O_K[\alpha]$ then $\alpha$ generates $L$ over $K$. -/
theorem adjoin_eq_top_of_adjoin (α : 𝓞 L) (hα : Algebra.adjoin (𝓞 K) {α} = ⊤) :
    IntermediateField.adjoin K {(α : L)} = ⊤ := by
  set S := IntermediateField.adjoin K {(α : L)} with hS
  have hint : ∀ y : 𝓞 L, (y : L) ∈ S := by
    intro y
    have hy : y ∈ Algebra.adjoin (𝓞 K) {α} := hα ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact IntermediateField.mem_adjoin_simple_self K _
    | algebraMap r =>
      have : ((algebraMap (𝓞 K) (𝓞 L) r : 𝓞 L) : L) = algebraMap K L (algebraMap (𝓞 K) K r) :=
        algebraMap_comm r
      rw [this]
      exact S.algebraMap_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  rw [← hab]
  exact div_mem (hint a) (hint b)

end Degree

end Remark83

open Remark83 in
/-- **Remark 8.3** (Milne, p. 136), conditional on the lower bound $e f \le [L_w : K_{\mathfrak p}]$ for the
extension $w$ attached to $\mathfrak P \mid \mathfrak p$ (`LocalDegreeLowerBound`). Part 1 is unconditional
(`Remark83.exists_unique_prime_of_extension`); for part 2, take $w$ from
`Remark83.existsUnique_extension_of_prime`: since $\alpha$ generates $L$ over $K$, the minimal polynomial of
$\alpha$ over $K_{\mathfrak p}$ in $L_w$ has degree $[L_w : K_{\mathfrak p}]$ (Proposition 8.1,
`Prop81.hMap_bijective`), which is $e f$ by `Remark83.finrank_completion_of_lowerBound`. (The hypothesis
$\mathcal O_L = \mathcal O_K[\alpha]$ is used only to get that $\alpha$ generates $L$.) -/
@[kb "milne2020ant" "v3.08, Rem. 8.3, p. 136"]
theorem remark_8_3_of_lowerBound (h : LocalDegreeLowerBound) : Remark8_3 := by
  refine ⟨?_⟩
  intro K L _ _ _ _ _ α hα 𝔭
  refine ⟨fun w => exists_unique_prime_of_extension 𝔭 w, fun P hP => ?_⟩
  have := hP
  obtain ⟨w, hw, -⟩ := existsUnique_extension_of_prime 𝔭 P
  refine ⟨w, hw, ?_⟩
  let _ := extAlgebra (FinitePlace.mk 𝔭).1 w
  have hadj := adjoin_eq_top_of_adjoin (K := K) (L := L) α hα
  have hbij := Prop81.hMap_bijective (FinitePlace.mk 𝔭).1 hadj w
  let e := AlgEquiv.ofBijective (Prop81.hMap (FinitePlace.mk 𝔭).1 w (α : L)) hbij
  have hne : (Prop81.phi (FinitePlace.mk 𝔭).1 w (α : L)).1 ≠ 0 :=
    (Prop81.phi (FinitePlace.mk 𝔭).1 w (α : L)).2.1.ne_zero
  have h1 : Module.finrank (FinitePlace.mk 𝔭).1.Completion
      (AdjoinRoot (Prop81.phi (FinitePlace.mk 𝔭).1 w (α : L)).1) =
        (Prop81.phi (FinitePlace.mk 𝔭).1 w (α : L)).1.natDegree := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim]
  have h2 := LinearEquiv.finrank_eq e.toLinearEquiv
  calc (minpoly (FinitePlace.mk 𝔭).1.Completion ((α : L) : w.1.Completion)).natDegree
      = (Prop81.phi (FinitePlace.mk 𝔭).1 w (α : L)).1.natDegree := rfl
    _ = _ := h1.symm
    _ = _ := h2
    _ = _ := finrank_completion_of_lowerBound h 𝔭 P w hw

end

end NumberFieldKB.MilneANT
