import NumberFieldKB.MilneEC.Ch3Elliptic
import NumberFieldKB.MilneEC.Ch3JInvariant
import NumberFieldKB.MilneEC.Ch3Torus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Milne, Elliptic Curves, Chapter III §3: `ℂ/Λ ≅ E(Λ)(ℂ)`

Proposition 3.7, Proposition 3.8, Corollary 3.9, Remark 3.11 and Exercise 3.24 (a) of Milne,
*Elliptic Curves* (`milne2006ec`, pdf pp. 100–108).

Conventions.
* `E(Λ)` is `curveOf L` (`Ch3Defs.lean`): Milne's point `(x : y : 1)` of
  `Y²Z = 4X³ − g₄XZ² − g₆Z³` is the point `(x, y/2)` of Mathlib's
  `Y² = X³ − (g₄/4)X − g₆/4`, and `(0 : 1 : 0)` is Mathlib's `0`.
* Mathlib has no complex structure on `E(ℂ)`.  Milne describes the natural one by local
  coordinates (pdf p. 100): `x` near affine points with `y ≠ 0`, `y` near the points with
  `y = 0`, and `x/y` near `(0 : 1 : 0)`.  Proposition 3.7 is stated as: the map is a bijection,
  and in each of these local coordinates it is holomorphic with nonzero derivative (a local
  biholomorphism); by the holomorphic inverse function theorem these two facts together say it is
  an isomorphism of Riemann surfaces.

Proof architecture (all helpers are in the namespace `CurveAux`).
* `count_orders`: for a doubly periodic `f` not identically zero, the orders of `f` on `ℂ/Λ` have
  finite support, total `0`, and weighted sum `0` in `ℂ/Λ` (from Proposition 2.1 on a period
  parallelogram whose boundary avoids the zeros and poles, chosen by a countability argument).
* `wpSub_zero_set`, `exists_wp_eq`, `wp_eq_cases`: `℘ - c` has exactly two zeros mod `Λ`.
* `prop_3_7_bijective'`, `prop_3_7_local'`: Proposition 3.7.
* `add_gen`, `cor_3_9'`: the line `℘' - m℘ - c` has three zeros summing to `0`; the generic
  addition formula is compared with Mathlib's `addX`, `addY`; the degenerate cases follow by
  splitting `w = (w - t) + t` for a generic `t`.
* `wp_eq_near_zero`, `lattice_eq_of_g_eq`: if `g₂, g₃` agree then `℘_Λ = ℘_Λ'` near `0` (via the
  local coordinates `t² ℘ = 1` and the first-order differential equation), hence `Λ = Λ'`.
* `exists_lattice_with_g`: surjectivity of `Λ ↦ (g₂, g₃)` from the surjectivity of `j`.
-/

open Complex Set Filter Topology

namespace NumberFieldKB.MilneEC.III

/-! ### Helpers -/

namespace CurveAux
section Count

variable (L : PeriodPair) {f : ℂ → ℂ}

lemma ord_top_ne (hf : IsDoublyPeriodic L.lattice f) (hf0 : ∃ z, meromorphicOrderAt f z ≠ ⊤)
    (z : ℂ) : meromorphicOrderAt f z ≠ ⊤ :=
  (Meromorphic.exists_meromorphicOrderAt_ne_top_iff_forall hf.1).1 hf0 z

lemma meromorphicOrderAt_add_lattice (hf : IsDoublyPeriodic L.lattice f) (z : ℂ) {ω : ℂ}
    (hω : ω ∈ L.lattice) : meromorphicOrderAt f (z + ω) = meromorphicOrderAt f z := by
  have h := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (f := f) (c := ω) (x := z)
  have e : (f ∘ (· + ω)) = f := funext fun x => hf.2 ω hω x
  rw [e] at h
  exact h.symm

/-- Punctured neighbourhoods contain no zeros or poles. -/
lemma eventually_order_zero (hf : IsDoublyPeriodic L.lattice f)
    (hf0 : ∃ z, meromorphicOrderAt f z ≠ ⊤) (x : ℂ) :
    ∀ᶠ y in 𝓝[≠] x, meromorphicOrderAt f y = 0 := by
  have h1 := (hf.1 x).eventually_analyticAt
  have h2 := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf.1 x)).1 (ord_top_ne L hf hf0 x)
  filter_upwards [h1, h2] with y hy1 hy2
  rw [hy1.meromorphicOrderAt_eq]
  have : analyticOrderAt f y = 0 := hy1.analyticOrderAt_eq_zero.2 hy2
  simp [this]

/-- The order function on `ℂ/Λ`. -/
noncomputable def ordQ (hf : IsDoublyPeriodic L.lattice f) : ℂ ⧸ L.lattice → ℤ :=
  Quotient.lift (ord f) fun a b h => by
    obtain ⟨ω, hω, rfl⟩ : ∃ ω ∈ L.lattice, b = a + ω :=
      ⟨b - a, by
        have := (Submodule.quotientRel_def L.lattice).1 h
        simpa [← L.lattice.neg_mem_iff (x := a - b)] using this, by simp⟩
    unfold ord
    rw [meromorphicOrderAt_add_lattice L hf a hω]

@[simp] lemma ordQ_mk (hf : IsDoublyPeriodic L.lattice f) (z : ℂ) :
    ordQ L hf (Submodule.Quotient.mk z) = ord f z := rfl

lemma repr_comb' (s t : ℝ) (i : Fin 2) :
    L.basis.repr ((s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂) i = if i = 0 then s else t := by
  have h1 : ((s : ℂ) * L.ω₁ + (t : ℂ) * L.ω₂) = s • L.basis 0 + t • L.basis 1 := by
    simp [Complex.real_smul]
  rw [h1, map_add, map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]
  fin_cases i <;> simp

lemma countable_of_isolated_aux {B : Set ℂ} (h : ∀ z ∈ B, ∃ U ∈ 𝓝 z, U ∩ B ⊆ {z}) :
    B.Countable := by
  have hd : DiscreteTopology B := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro ⟨z, hz⟩
    obtain ⟨U, hU, hUB⟩ := h z hz
    rw [isOpen_induced_iff]
    obtain ⟨V, hVU, hVo, hzV⟩ := mem_nhds_iff.mp hU
    refine ⟨V, hVo, ?_⟩
    ext ⟨w, hw⟩
    simp only [mem_preimage, mem_singleton_iff, Subtype.mk.injEq]
    constructor
    · intro hwV
      exact hUB ⟨hVU hwV, hw⟩
    · rintro rfl; exact hzV
  exact (HereditarilyLindelofSpace.isLindelof B).countable hd

lemma exists_real_notMem {S : Set ℝ} (h : S.Countable) : ∃ a, a ∉ S := by
  by_contra hh
  push Not at hh
  exact Cardinal.not_countable_real (by rwa [Set.eq_univ_of_forall hh] at h)

lemma exists_complex_notMem {S : Set ℂ} (h : S.Countable) : ∃ a, a ∉ S := by
  by_contra hh
  push Not at hh
  exact not_countable_complex (by rwa [Set.eq_univ_of_forall hh] at h)

lemma exists_z₀ (hf : IsDoublyPeriodic L.lattice f) (hf0 : ∃ z, meromorphicOrderAt f z ≠ ⊤) :
    ∃ z₀, ∀ P ∈ frontier (periodParallelogram L.ω₁ L.ω₂ z₀), meromorphicOrderAt f P = 0 := by
  set T : Set ℂ := {P | meromorphicOrderAt f P ≠ 0} with hT
  have hTc : T.Countable := by
    apply countable_of_isolated_aux
    intro z _
    have := eventually_order_zero L hf hf0 z
    rw [eventually_nhdsWithin_iff] at this
    obtain ⟨U, hU, hUo, hzU⟩ := eventually_nhds_iff.1 this
    refine ⟨U, hUo.mem_nhds hzU, ?_⟩
    rintro y ⟨hyU, hyT⟩
    by_contra hne
    exact hyT (hU y hyU hne)
  set A : Set ℝ := (fun p => L.basis.repr p 0) '' T with hA
  set B : Set ℝ := (fun p => L.basis.repr p 1) '' T with hB
  have hAc : A.Countable := hTc.image _
  have hBc : B.Countable := hTc.image _
  obtain ⟨a, ha⟩ := (hAc.union (hAc.image (fun x => x - 1))) |> exists_real_notMem
  obtain ⟨b, hb⟩ := (hBc.union (hBc.image (fun x => x - 1))) |> exists_real_notMem
  refine ⟨(a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂, ?_⟩
  intro P hP
  by_contra hPT
  rw [frontier_periodParallelogram] at hP
  obtain ⟨⟨s, t, hs, ht, rfl⟩, hnot⟩ := hP
  have hr0 : L.basis.repr (↑a * L.ω₁ + ↑b * L.ω₂ + ↑s * L.ω₁ + ↑t * L.ω₂) 0 = a + s := by
    have : (↑a * L.ω₁ + ↑b * L.ω₂ + ↑s * L.ω₁ + ↑t * L.ω₂ : ℂ) =
        ((a + s : ℝ) : ℂ) * L.ω₁ + ((b + t : ℝ) : ℂ) * L.ω₂ := by push_cast; ring
    rw [this, repr_comb']; simp
  have hr1 : L.basis.repr (↑a * L.ω₁ + ↑b * L.ω₂ + ↑s * L.ω₁ + ↑t * L.ω₂) 1 = b + t := by
    have : (↑a * L.ω₁ + ↑b * L.ω₂ + ↑s * L.ω₁ + ↑t * L.ω₂ : ℂ) =
        ((a + s : ℝ) : ℂ) * L.ω₁ + ((b + t : ℝ) : ℂ) * L.ω₂ := by push_cast; ring
    rw [this, repr_comb']; simp
  have hmemT : (↑a * L.ω₁ + ↑b * L.ω₂ + ↑s * L.ω₁ + ↑t * L.ω₂ : ℂ) ∈ T := hPT
  have hA1 : a + s ∈ A := ⟨_, hmemT, hr0⟩
  have hB1 : b + t ∈ B := ⟨_, hmemT, hr1⟩
  have hnot' : ¬ (s ∈ Ioo (0 : ℝ) 1 ∧ t ∈ Ioo (0 : ℝ) 1) := fun h => hnot ⟨s, t, h.1, h.2, rfl⟩
  by_cases hs' : s ∈ Ioo (0 : ℝ) 1
  · have ht' : t ∉ Ioo (0 : ℝ) 1 := fun h => hnot' ⟨hs', h⟩
    have : t = 0 ∨ t = 1 := by
      rcases ht with ⟨h0, h1⟩
      by_contra hh; push Not at hh
      exact ht' ⟨lt_of_le_of_ne h0 (Ne.symm hh.1), lt_of_le_of_ne h1 hh.2⟩
    rcases this with rfl | rfl
    · exact hb (Or.inl (by simpa using hB1))
    · exact hb (Or.inr ⟨b + 1, hB1, by ring⟩)
  · have : s = 0 ∨ s = 1 := by
      rcases hs with ⟨h0, h1⟩
      by_contra hh; push Not at hh
      exact hs' ⟨lt_of_le_of_ne h0 (Ne.symm hh.1), lt_of_le_of_ne h1 hh.2⟩
    rcases this with rfl | rfl
    · exact ha (Or.inl (by simpa using hA1))
    · exact ha (Or.inr ⟨a + 1, hA1, by ring⟩)

lemma ord_ne_zero_iff (hf : IsDoublyPeriodic L.lattice f) (hf0 : ∃ z, meromorphicOrderAt f z ≠ ⊤)
    (z : ℂ) : ord f z ≠ 0 ↔ meromorphicOrderAt f z ≠ 0 := by
  have h := ord_top_ne L hf hf0 z
  unfold ord
  constructor
  · intro h1 h2
    apply h1
    rw [h2]; simp
  · intro h1 h2
    apply h1
    have := WithTop.coe_untop₀_of_ne_top h
    rw [h2] at this
    exact_mod_cast this.symm

theorem count_orders (hf : IsDoublyPeriodic L.lattice f) (hf0 : ∃ z, meromorphicOrderAt f z ≠ ⊤) :
    (Function.support (ordQ L hf)).Finite ∧ ∑ᶠ q, ordQ L hf q = 0 ∧
      ∑ᶠ q, ordQ L hf q • q = 0 := by
  classical
  obtain ⟨z₀, hD⟩ := exists_z₀ L hf hf0
  obtain ⟨hfin, -, hsum, hsum2⟩ := prop_2_1 L hf hf0 z₀ hD
  set D := periodParallelogram L.ω₁ L.ω₂ z₀ with hDdef
  set F : Finset ℂ := hfin.toFinset with hF
  have hFmem : ∀ P, P ∈ F ↔ P ∈ D ∧ ord f P ≠ 0 := by
    intro P
    rw [hF, Set.Finite.mem_toFinset]
    simp only [Set.mem_ofPred_eq]
    rw [ord_ne_zero_iff L hf hf0]
  -- uniqueness of representatives
  have hex : ∀ z, ord f z ≠ 0 → ∃! ω, ω ∈ L.lattice ∧ z + ω ∈ D := by
    intro z hz
    refine existsUnique_add_mem_periodParallelogram L z₀ z fun ω hω hfr => ?_
    have h1 := hD _ hfr
    rw [meromorphicOrderAt_add_lattice L hf z hω] at h1
    exact (ord_ne_zero_iff L hf hf0 z).1 hz h1
  have hrel : ∀ P P' : ℂ, (Submodule.Quotient.mk P : ℂ ⧸ L.lattice) = Submodule.Quotient.mk P' →
      ∃ ω ∈ L.lattice, P' = P + ω := by
    intro P P' h
    refine ⟨P' - P, ?_, by ring⟩
    have := (Submodule.Quotient.eq L.lattice).1 h
    simpa using L.lattice.neg_mem this
  have hinj : Set.InjOn (fun P : ℂ => (Submodule.Quotient.mk P : ℂ ⧸ L.lattice)) (F : Set ℂ) := by
    intro P hP P' hP' h
    obtain ⟨ω, hω, rfl⟩ := hrel P P' h
    have hP1 := (hFmem P).1 hP
    have hP2 := (hFmem _).1 hP'
    obtain ⟨ω₀, -, huniq⟩ := hex P hP1.2
    have h1 := huniq ω ⟨hω, hP2.1⟩
    have h2 := huniq 0 ⟨L.lattice.zero_mem, by simpa using hP1.1⟩
    have : ω = 0 := h1.trans h2.symm
    rw [this, add_zero]
  have hsupp : Function.support (ordQ L hf) = ((F.image fun P : ℂ => (Submodule.Quotient.mk P : ℂ ⧸ L.lattice) : Finset _) : Set _) := by
    ext q
    induction q using Submodule.Quotient.induction_on with
    | H z =>
      simp only [Function.mem_support, ordQ_mk, Finset.coe_image, Set.mem_image, Finset.mem_coe]
      constructor
      · intro hz
        obtain ⟨ω, ⟨hω, hmem⟩, -⟩ := hex z hz
        refine ⟨z + ω, (hFmem _).2 ⟨hmem, ?_⟩, ?_⟩
        · unfold ord; rw [meromorphicOrderAt_add_lattice L hf z hω]; exact hz
        · exact (Submodule.Quotient.eq _).2 (by simpa using L.lattice.neg_mem hω)
      · rintro ⟨P, hP, hPz⟩
        obtain ⟨ω, hω, rfl⟩ := hrel P z hPz
        have := ((hFmem P).1 hP).2
        unfold ord at this ⊢
        rwa [meromorphicOrderAt_add_lattice L hf P hω]
  have hS : ∀ g : ℂ → ℤ, (∀ P, g P ≠ 0 → ord f P ≠ 0) →
      ∑ᶠ (P) (_ : P ∈ D), g P = ∑ P ∈ F, g P := by
    intro g hg
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext P
    simp only [Set.mem_inter_iff, Finset.mem_coe, Function.mem_support, hFmem]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hg P h2⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  have hS2 : ∑ᶠ (P) (_ : P ∈ D), ((ord f P : ℤ) : ℂ) * P = ∑ P ∈ F, ((ord f P : ℤ) : ℂ) * P := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext P
    simp only [Set.mem_inter_iff, Finset.mem_coe, Function.mem_support, hFmem]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, h2⟩
      intro h0; apply h2; simp [h0]
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  have hfinS : (Function.support (ordQ L hf)).Finite := by
    rw [hsupp]; exact Finset.finite_toSet _
  refine ⟨hfinS, ?_, ?_⟩
  · rw [finsum_eq_sum_of_support_subset _ (subset_of_eq hsupp), Finset.sum_image hinj]
    simp only [ordQ_mk]
    rw [← hS _ (fun P hP => hP), hsum]
  · have hsub : Function.support (fun q : ℂ ⧸ L.lattice => ordQ L hf q • q) ⊆
        ↑(F.image fun P : ℂ => (Submodule.Quotient.mk P : ℂ ⧸ L.lattice)) := by
      intro q hq
      apply subset_of_eq hsupp
      by_contra h
      apply hq
      simp only [Function.mem_support, not_not] at h
      simp [h]
    rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_image hinj]
    have : ∑ P ∈ F, ordQ L hf (Submodule.Quotient.mk P) • (Submodule.Quotient.mk P : ℂ ⧸ L.lattice) =
        Submodule.Quotient.mk (∑ P ∈ F, ((ord f P : ℤ) : ℂ) * P) := by
      have hm := map_sum (Submodule.mkQ L.lattice) (fun P => ((ord f P : ℤ) : ℂ) * P) F
      simp only [Submodule.mkQ_apply] at hm
      rw [hm]
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [ordQ_mk, ← Submodule.Quotient.mk_smul, zsmul_eq_mul]
    rw [this, ← hS2]
    exact (Submodule.Quotient.mk_eq_zero _).2 hsum2

lemma ord_nonneg_of_analytic {z : ℂ} (hfa : AnalyticAt ℂ f z) : 0 ≤ ord f z := by
  unfold ord
  have := hfa.meromorphicOrderAt_nonneg
  exact WithTop.untop₀_nonneg.2 this

lemma natCast_le_ord_iff {z : ℂ} (hfa : AnalyticAt ℂ f z) (htop : meromorphicOrderAt f z ≠ ⊤)
    (n : ℕ) : (n : ℤ) ≤ ord f z ↔ ∀ i < n, iteratedDeriv i f z = 0 := by
  rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hfa]
  unfold ord
  rw [hfa.meromorphicOrderAt_eq] at htop ⊢
  generalize analyticOrderAt f z = a at htop ⊢
  induction a using ENat.recTopCoe with
  | top => simp at htop
  | coe k => simp

lemma zero_set (hf : IsDoublyPeriodic L.lattice f) (m : ℕ) (hm0 : 0 < m)
    (hm : meromorphicOrderAt f 0 = -(m : ℤ)) (hana : ∀ z ∉ L.lattice, AnalyticAt ℂ f z) :
    ∃ S : Finset (ℂ ⧸ L.lattice), (∀ q ∈ S, 1 ≤ ordQ L hf q ∧ q ≠ 0) ∧
      (∀ z ∉ L.lattice, 1 ≤ ord f z → Submodule.Quotient.mk z ∈ S) ∧
      ∑ q ∈ S, ordQ L hf q = m ∧ ∑ q ∈ S, ordQ L hf q • q = 0 := by
  classical
  have hf0 : ∃ z, meromorphicOrderAt f z ≠ ⊤ := ⟨0, by rw [hm]; exact WithTop.coe_ne_top⟩
  obtain ⟨hfin, hsum, hsum2⟩ := count_orders L hf hf0
  have hq0 : ordQ L hf 0 = -(m : ℤ) := by
    rw [← Submodule.Quotient.mk_zero L.lattice, ordQ_mk]
    unfold ord; rw [hm]; rfl
  set Sf := hfin.toFinset with hSf
  have hmemSf : ∀ q, q ∈ Sf ↔ ordQ L hf q ≠ 0 := by
    intro q; rw [hSf, Set.Finite.mem_toFinset, Function.mem_support]
  have h0mem : (0 : ℂ ⧸ L.lattice) ∈ Sf := by
    rw [hmemSf, hq0]; omega
  refine ⟨Sf.erase 0, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rw [Finset.mem_erase] at hq
    refine ⟨?_, hq.1⟩
    obtain ⟨hq0', hq1⟩ := hq
    have hne := (hmemSf q).1 hq1
    induction q using Submodule.Quotient.induction_on with
    | H z =>
      have hz : z ∉ L.lattice := fun h => hq0' ((Submodule.Quotient.mk_eq_zero _).2 h)
      have := ord_nonneg_of_analytic (hana z hz)
      rw [ordQ_mk] at hne ⊢
      omega
  · intro z hz h1
    rw [Finset.mem_erase]
    refine ⟨fun h => hz ((Submodule.Quotient.mk_eq_zero _).1 h), (hmemSf _).2 ?_⟩
    rw [ordQ_mk]; omega
  · have h1 : ∑ q ∈ Sf, ordQ L hf q = 0 := by
      rw [← finsum_eq_sum_of_support_subset (s := Sf) _ (by simp [hSf])]; exact hsum
    rw [← Finset.add_sum_erase Sf _ h0mem, hq0] at h1
    omega
  · have h1 : ∑ q ∈ Sf, ordQ L hf q • q = 0 := by
      rw [← finsum_eq_sum_of_support_subset (s := Sf) (fun q => ordQ L hf q • q)
        (by
          intro q hq
          simp only [Function.mem_support] at hq
          rw [Finset.mem_coe, hmemSf]
          intro h; apply hq; rw [h, zero_smul])]
      exact hsum2
    rw [← Finset.add_sum_erase Sf _ h0mem] at h1
    simpa using h1

end Count

section Comb

lemma comb_two_ne {α : Type*} [DecidableEq α] (S : Finset α) (g : α → ℤ) (hpos : ∀ q ∈ S, 1 ≤ g q)
    {a b : α} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) : g a + g b ≤ ∑ q ∈ S, g q := by
  have hsub : ({a, b} : Finset α) ⊆ S := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := g)
    (fun i hi _ => by linarith [hpos i hi])
  rwa [Finset.sum_pair hab] at this

lemma comb_two {α : Type*} [DecidableEq α] (S : Finset α) (g : α → ℤ) (hpos : ∀ q ∈ S, 1 ≤ g q)
    (hsum : ∑ q ∈ S, g q = 2) {a b : α} (ha : a ∈ S) (hb : b ∈ S) (hab : a = b → 2 ≤ g a) :
    ∀ q ∈ S, q = a ∨ q = b := by
  intro q hq
  by_contra h
  push Not at h
  by_cases hab' : a = b
  · subst hab'
    have h2 := hab rfl
    have := comb_two_ne S g hpos ha hq (Ne.symm h.1)
    linarith [hpos q hq]
  · have hsub : ({a, b, q} : Finset α) ⊆ S := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := g)
      (fun i hi _ => by linarith [hpos i hi])
    rw [Finset.sum_insert (by simp [hab', Ne.symm h.1]), Finset.sum_pair (Ne.symm h.2)] at this
    linarith [hpos q hq, hpos a ha, hpos b hb]

lemma comb_three {A : Type*} [AddCommGroup A] [DecidableEq A] (S : Finset A) (g : A → ℤ)
    (hpos : ∀ q ∈ S, 1 ≤ g q) (hsum : ∑ q ∈ S, g q = 3) (hw : ∑ q ∈ S, g q • q = 0)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    ∃ u ∈ S, a + b + u = 0 ∧ (u = a → 2 ≤ g a) ∧ (u = b → 2 ≤ g b) := by
  set S1 := (S.erase a).erase b with hS1
  have hb' : b ∈ S.erase a := Finset.mem_erase.2 ⟨Ne.symm hab, hb⟩
  have e1 : g a + (g b + ∑ q ∈ S1, g q) = 3 := by
    rw [Finset.add_sum_erase _ _ hb', Finset.add_sum_erase _ _ ha]; exact hsum
  have e2 : g a • a + (g b • b + ∑ q ∈ S1, g q • q) = 0 := by
    rw [Finset.add_sum_erase _ (fun q => g q • q) hb', Finset.add_sum_erase _ (fun q => g q • q) ha]
    exact hw
  have hpa := hpos a ha
  have hpb := hpos b hb
  have hcard : (S1.card : ℤ) ≤ ∑ q ∈ S1, g q := by
    have : ∑ q ∈ S1, (1 : ℤ) ≤ ∑ q ∈ S1, g q :=
      Finset.sum_le_sum fun q hq => hpos q (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq))
    simpa using this
  have hc : S1.card = 0 ∨ S1.card = 1 := by omega
  rcases hc with hc | hc
  · rw [Finset.card_eq_zero] at hc
    rw [hc] at e1 e2
    simp only [Finset.sum_empty, add_zero] at e1 e2
    have : (g a = 2 ∧ g b = 1) ∨ (g a = 1 ∧ g b = 2) := by omega
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨a, ha, ?_, fun _ => by omega, fun h => absurd h hab⟩
      rw [h1, h2] at e2
      simp only [two_smul, one_smul] at e2
      rw [← e2]; abel
    · refine ⟨b, hb, ?_, fun h => absurd h.symm hab, fun _ => by omega⟩
      rw [h1, h2] at e2
      simp only [two_smul, one_smul] at e2
      rw [← e2]; abel
  · obtain ⟨u, hu⟩ := Finset.card_eq_one.1 hc
    have huS1 : u ∈ S1 := by rw [hu]; simp
    have hu1 := Finset.mem_erase.1 huS1
    have hu2 := Finset.mem_erase.1 hu1.2
    rw [hu] at e1 e2
    simp only [Finset.sum_singleton] at e1 e2
    have hpu := hpos u hu2.2
    have h1 : g a = 1 := by omega
    have h2 : g b = 1 := by omega
    have h3 : g u = 1 := by omega
    refine ⟨u, hu2.2, ?_, fun h => absurd h hu2.1, fun h => absurd h hu1.1⟩
    rw [h1, h2, h3] at e2
    simp only [one_smul] at e2
    rw [← e2]; abel

end Comb

section Wp

variable (L : PeriodPair)

/-- `℘ - c`. -/
noncomputable def wpSub (c : ℂ) : ℂ → ℂ := fun u => L.weierstrassP u - c

lemma wpSub_doublyPeriodic (c : ℂ) : IsDoublyPeriodic L.lattice (wpSub L c) := by
  refine ⟨?_, fun ω hω u => ?_⟩
  · have := L.meromorphic_weierstrassP
    unfold wpSub
    fun_prop
  · simp [wpSub, L.weierstrassP_add_coe u ⟨ω, hω⟩]

lemma wpSub_order (c : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) :
    meromorphicOrderAt (wpSub L c) ω = -(2 : ℕ) := by
  have : wpSub L c = L.weierstrassP + fun _ => -c := funext fun u => by
    simp [wpSub, sub_eq_add_neg]
  rw [this, meromorphicOrderAt_add_eq_left_of_lt (by fun_prop), L.order_weierstrassP ω hω]
  · norm_num
  · rw [L.order_weierstrassP ω hω]
    have : 0 ≤ meromorphicOrderAt (fun _ : ℂ => -c) ω := (analyticAt_const (x := ω)).meromorphicOrderAt_nonneg
    exact lt_of_lt_of_le (by decide) this

lemma wpSub_analytic (c : ℂ) {z : ℂ} (hz : z ∉ L.lattice) : AnalyticAt ℂ (wpSub L c) z :=
  (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const

lemma wpSub_zero_set (c : ℂ) :
    ∃ S : Finset (ℂ ⧸ L.lattice), (∀ q ∈ S, 1 ≤ ordQ L (wpSub_doublyPeriodic L c) q ∧ q ≠ 0) ∧
      (∀ z ∉ L.lattice, 1 ≤ ord (wpSub L c) z → Submodule.Quotient.mk z ∈ S) ∧
      ∑ q ∈ S, ordQ L (wpSub_doublyPeriodic L c) q = 2 ∧
      ∑ q ∈ S, ordQ L (wpSub_doublyPeriodic L c) q • q = 0 := by
  have := zero_set L (wpSub_doublyPeriodic L c) 2 (by norm_num)
    (wpSub_order L c L.lattice.zero_mem) (fun z hz => wpSub_analytic L c hz)
  simpa using this

lemma one_le_ord_wpSub_iff (c : ℂ) {z : ℂ} (hz : z ∉ L.lattice) :
    1 ≤ ord (wpSub L c) z ↔ L.weierstrassP z = c := by
  have hf0 : ∃ z, meromorphicOrderAt (wpSub L c) z ≠ ⊤ :=
    ⟨0, by rw [wpSub_order L c L.lattice.zero_mem]; exact WithTop.coe_ne_top⟩
  have := natCast_le_ord_iff (wpSub_analytic L c hz)
    (ord_top_ne L (wpSub_doublyPeriodic L c) hf0 z) 1
  simp only [Nat.cast_one, Nat.lt_one_iff, forall_eq, iteratedDeriv_zero] at this
  rw [this, wpSub, sub_eq_zero]

lemma two_le_ord_wpSub_iff (c : ℂ) {z : ℂ} (hz : z ∉ L.lattice) :
    2 ≤ ord (wpSub L c) z ↔ L.weierstrassP z = c ∧ L.derivWeierstrassP z = 0 := by
  have hf0 : ∃ z, meromorphicOrderAt (wpSub L c) z ≠ ⊤ :=
    ⟨0, by rw [wpSub_order L c L.lattice.zero_mem]; exact WithTop.coe_ne_top⟩
  have := natCast_le_ord_iff (wpSub_analytic L c hz)
    (ord_top_ne L (wpSub_doublyPeriodic L c) hf0 z) 2
  simp only [Nat.cast_ofNat] at this
  have hd : deriv (wpSub L c) z = L.derivWeierstrassP z := by
    have : wpSub L c = fun u => L.weierstrassP u - c := rfl
    rw [this, deriv_sub_const, PeriodPair.deriv_weierstrassP]
  rw [this]
  constructor
  · intro h
    have h0 := h 0 (by norm_num)
    have h1 := h 1 (by norm_num)
    rw [iteratedDeriv_zero] at h0
    rw [iteratedDeriv_one, hd] at h1
    exact ⟨sub_eq_zero.1 h0, h1⟩
  · rintro ⟨h0, h1⟩ i hi
    interval_cases i
    · rw [iteratedDeriv_zero]; exact sub_eq_zero.2 h0
    · rw [iteratedDeriv_one, hd]; exact h1

end Wp

section Bij

variable (L : PeriodPair)

lemma wp_eq_of_sub_mem {x y : ℂ} (h : x - y ∈ L.lattice) : L.weierstrassP x = L.weierstrassP y := by
  have := L.weierstrassP_add_coe y ⟨x - y, h⟩
  simpa using this

lemma dwp_eq_of_sub_mem {x y : ℂ} (h : x - y ∈ L.lattice) :
    L.derivWeierstrassP x = L.derivWeierstrassP y := by
  have := L.derivWeierstrassP_add_coe y ⟨x - y, h⟩
  simpa using this

lemma neg_notMem_lattice {z : ℂ} (hz : z ∉ L.lattice) : -z ∉ L.lattice :=
  fun h => hz (by simpa using L.lattice.neg_mem h)

lemma dwp_eq_zero_of_mk_neg {z : ℂ}
    (h : (Submodule.Quotient.mk z : ℂ ⧸ L.lattice) = Submodule.Quotient.mk (-z)) :
    L.derivWeierstrassP z = 0 := by
  have h1 := dwp_eq_of_sub_mem L ((Submodule.Quotient.eq _).1 h)
  rw [L.derivWeierstrassP_neg] at h1
  linear_combination h1 / 2

lemma wp_eq_cases {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (h : L.weierstrassP w = L.weierstrassP z) :
    (Submodule.Quotient.mk w : ℂ ⧸ L.lattice) = Submodule.Quotient.mk z ∨
      (Submodule.Quotient.mk w : ℂ ⧸ L.lattice) = Submodule.Quotient.mk (-z) := by
  classical
  obtain ⟨S, hS1, hS2, hS3, -⟩ := wpSub_zero_set L (L.weierstrassP z)
  have ha : (Submodule.Quotient.mk z : ℂ ⧸ L.lattice) ∈ S :=
    hS2 z hz ((one_le_ord_wpSub_iff L _ hz).2 rfl)
  have hb : (Submodule.Quotient.mk (-z) : ℂ ⧸ L.lattice) ∈ S :=
    hS2 (-z) (neg_notMem_lattice L hz) ((one_le_ord_wpSub_iff L _ (neg_notMem_lattice L hz)).2
      (L.weierstrassP_neg z))
  have hwS : (Submodule.Quotient.mk w : ℂ ⧸ L.lattice) ∈ S :=
    hS2 w hw ((one_le_ord_wpSub_iff L _ hw).2 h)
  refine comb_two S _ (fun q hq => (hS1 q hq).1) hS3 ha hb (fun hab => ?_) _ hwS
  rw [ordQ_mk]
  exact (two_le_ord_wpSub_iff L _ hz).2 ⟨rfl, dwp_eq_zero_of_mk_neg L hab⟩

lemma mk_neg_eq_of_dwp_zero {z : ℂ} (hz : z ∉ L.lattice) (h : L.derivWeierstrassP z = 0) :
    (Submodule.Quotient.mk z : ℂ ⧸ L.lattice) = Submodule.Quotient.mk (-z) := by
  classical
  by_contra hne
  obtain ⟨S, hS1, hS2, hS3, -⟩ := wpSub_zero_set L (L.weierstrassP z)
  have ha : (Submodule.Quotient.mk z : ℂ ⧸ L.lattice) ∈ S :=
    hS2 z hz ((one_le_ord_wpSub_iff L _ hz).2 rfl)
  have hb : (Submodule.Quotient.mk (-z) : ℂ ⧸ L.lattice) ∈ S :=
    hS2 (-z) (neg_notMem_lattice L hz) ((one_le_ord_wpSub_iff L _ (neg_notMem_lattice L hz)).2
      (L.weierstrassP_neg z))
  have h1 := comb_two_ne S _ (fun q hq => (hS1 q hq).1) ha hb hne
  have h2 : 2 ≤ ordQ L (wpSub_doublyPeriodic L (L.weierstrassP z)) (Submodule.Quotient.mk z) := by
    rw [ordQ_mk]
    exact (two_le_ord_wpSub_iff L _ hz).2 ⟨rfl, h⟩
  have h3 := (hS1 _ hb).1
  rw [hS3] at h1
  linarith

lemma exists_wp_eq (c : ℂ) : ∃ z, z ∉ L.lattice ∧ L.weierstrassP z = c := by
  classical
  obtain ⟨S, hS1, hS2, hS3, -⟩ := wpSub_zero_set L c
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hS3
    simp at hS3
  obtain ⟨q, hq⟩ := hne
  induction q using Submodule.Quotient.induction_on with
  | H z =>
    have hz : z ∉ L.lattice := fun h => (hS1 _ hq).2 ((Submodule.Quotient.mk_eq_zero _).2 h)
    refine ⟨z, hz, ?_⟩
    have := (hS1 _ hq).1
    rw [ordQ_mk] at this
    exact (one_le_ord_wpSub_iff L _ hz).1 this

end Bij

section ToCurve

open WeierstrassCurve.Affine in
theorem toCurve_of_mem (L : PeriodPair) {z : ℂ} (hz : z ∈ L.lattice) : toCurve L z = 0 := by
  simp [toCurve, hz]

theorem toCurve_of_notMem (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    ∃ h, toCurve L z = WeierstrassCurve.Affine.Point.some (W' := (curveOf L).toAffine)
      (L.weierstrassP z) (L.derivWeierstrassP z / 2) h := by
  unfold toCurve; rw [dite_eq_right_of_eq_false (eq_false hz)]; exact ⟨_, rfl⟩

end ToCurve

end CurveAux

open CurveAux

/-! ### The map `ℂ/Λ → E(Λ)(ℂ)` -/

theorem toCurve_add_coe (L : PeriodPair) (z : ℂ) (ω : L.lattice) :
    toCurve L (z + ω) = toCurve L z := by
  by_cases hz : z ∈ L.lattice
  · rw [toCurve_of_mem L hz, toCurve_of_mem L (L.lattice.add_mem hz ω.2)]
  · have hz' : z + ω ∉ L.lattice := fun h => hz (by simpa using L.lattice.sub_mem h ω.2)
    obtain ⟨h1, e1⟩ := toCurve_of_notMem L hz
    obtain ⟨h2, e2⟩ := toCurve_of_notMem L hz'
    rw [e1, e2]
    simp only [PeriodPair.weierstrassP_add_coe, PeriodPair.derivWeierstrassP_add_coe]

/-- The map `[z] ↦ (℘(z) : ℘'(z) : 1)`, `[0] ↦ (0 : 1 : 0)` of Proposition 3.7 (Milne, pdf p. 100),
on `ℂ/Λ`. -/
noncomputable def toCurveQuot (L : PeriodPair) : ℂ ⧸ L.lattice → (curveOf L).toAffine.Point :=
  Quotient.lift (toCurve L) fun a b h => by
    obtain ⟨ω, rfl⟩ : ∃ ω : L.lattice, b = a + ω :=
      ⟨⟨b - a, by
        have := (Submodule.quotientRel_def L.lattice).1 h
        simpa [← L.lattice.neg_mem_iff (x := a - b)] using this⟩, by simp⟩
    exact (toCurve_add_coe L a ω).symm

@[simp] theorem toCurveQuot_mk (L : PeriodPair) (z : ℂ) :
    toCurveQuot L (Submodule.Quotient.mk z) = toCurve L z := rfl

namespace CurveAux

section ToCurveB

variable (L : PeriodPair)

lemma toCurve_eq_some {z : ℂ} (hz : z ∉ L.lattice) {x y : ℂ} (hx : L.weierstrassP z = x)
    (hy : L.derivWeierstrassP z / 2 = y) (h : (curveOf L).toAffine.Nonsingular x y) :
    toCurve L z = WeierstrassCurve.Affine.Point.some x y h := by
  obtain ⟨h1, e1⟩ := toCurve_of_notMem L hz
  rw [e1]
  subst hx hy
  rfl

lemma toCurve_neg (z : ℂ) : toCurve L (-z) = -toCurve L z := by
  by_cases hz : z ∈ L.lattice
  · rw [toCurve_of_mem L hz, toCurve_of_mem L (L.lattice.neg_mem hz)]; rfl
  · obtain ⟨h1, e1⟩ := toCurve_of_notMem L hz
    obtain ⟨h2, e2⟩ := toCurve_of_notMem L (neg_notMem_lattice L hz)
    rw [e1, e2, WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    refine ⟨L.weierstrassP_neg z, ?_⟩
    simp [WeierstrassCurve.Affine.negY, curveOf, L.derivWeierstrassP_neg]
    ring

lemma toCurve_eq_zero_iff (z : ℂ) : toCurve L z = 0 ↔ z ∈ L.lattice := by
  constructor
  · intro h
    by_contra hz
    obtain ⟨h1, e1⟩ := toCurve_of_notMem L hz
    rw [e1] at h
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ h
  · exact toCurve_of_mem L

theorem prop_3_7_bijective' : Function.Bijective (toCurveQuot L) := by
  constructor
  · intro q1 q2
    induction q1 using Submodule.Quotient.induction_on with
    | H z =>
    induction q2 using Submodule.Quotient.induction_on with
    | H w =>
    simp only [toCurveQuot_mk]
    intro h
    by_cases hz : z ∈ L.lattice
    · have hw : w ∈ L.lattice := by
        rw [← toCurve_eq_zero_iff, ← h]; exact toCurve_of_mem L hz
      rw [(Submodule.Quotient.mk_eq_zero _).2 hz, (Submodule.Quotient.mk_eq_zero _).2 hw]
    · have hw : w ∉ L.lattice := by
        intro hw
        apply hz
        rw [← toCurve_eq_zero_iff, h]; exact toCurve_of_mem L hw
      obtain ⟨h1, e1⟩ := toCurve_of_notMem L hz
      obtain ⟨h2, e2⟩ := toCurve_of_notMem L hw
      rw [e1, e2, WeierstrassCurve.Affine.Point.some.injEq] at h
      obtain ⟨hx, hy⟩ := h
      rcases wp_eq_cases L hz hw hx.symm with h3 | h3
      · exact h3.symm
      · -- w ≡ -z
        have h4 : L.derivWeierstrassP w = L.derivWeierstrassP (-z) :=
          dwp_eq_of_sub_mem L ((Submodule.Quotient.eq _).1 h3)
        rw [L.derivWeierstrassP_neg] at h4
        have h5 : L.derivWeierstrassP z = 0 := by linear_combination hy + h4 / 2
        exact (mk_neg_eq_of_dwp_zero L hz h5).trans h3.symm
  · intro P
    cases P with
    | zero => exact ⟨Submodule.Quotient.mk 0, toCurve_of_mem L L.lattice.zero_mem⟩
    | some x y h =>
      obtain ⟨z, hz, hzx⟩ := exists_wp_eq L x
      have heq := (WeierstrassCurve.Affine.equation_iff _ _).1 h.1
      simp only [curveOf] at heq
      have hsq := L.derivWeierstrassP_sq z hz
      rw [hzx] at hsq
      have h2 : (L.derivWeierstrassP z / 2) ^ 2 = y ^ 2 := by
        rw [div_pow, hsq]
        simp only [PeriodPair.g₂] at *
        linear_combination (-1 : ℂ) * heq
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3
      · exact ⟨Submodule.Quotient.mk z, by simpa using toCurve_eq_some L hz hzx h3 h⟩
      · refine ⟨Submodule.Quotient.mk (-z), ?_⟩
        rw [toCurveQuot_mk]
        refine toCurve_eq_some L (neg_notMem_lattice L hz) (by rw [L.weierstrassP_neg, hzx]) ?_ h
        rw [L.derivWeierstrassP_neg]
        linear_combination -h3

lemma deriv_ne_zero_of_dwp_zero {z : ℂ} (hz : z ∉ L.lattice) (h : L.derivWeierstrassP z = 0) :
    deriv L.derivWeierstrassP z ≠ 0 := by
  classical
  intro h2
  obtain ⟨S, hS1, hS2, hS3, -⟩ := wpSub_zero_set L (L.weierstrassP z)
  have hf0 : ∃ y, meromorphicOrderAt (wpSub L (L.weierstrassP z)) y ≠ ⊤ :=
    ⟨0, by rw [wpSub_order L _ L.lattice.zero_mem]; exact WithTop.coe_ne_top⟩
  have ha : (Submodule.Quotient.mk z : ℂ ⧸ L.lattice) ∈ S :=
    hS2 z hz ((one_le_ord_wpSub_iff L _ hz).2 rfl)
  have h3 : 3 ≤ ordQ L (wpSub_doublyPeriodic L (L.weierstrassP z)) (Submodule.Quotient.mk z) := by
    rw [ordQ_mk]
    have := natCast_le_ord_iff (wpSub_analytic L (L.weierstrassP z) hz)
      (ord_top_ne L (wpSub_doublyPeriodic L (L.weierstrassP z)) hf0 z) 3
    simp only [Nat.cast_ofNat] at this
    rw [this]
    have hd : deriv (wpSub L (L.weierstrassP z)) = L.derivWeierstrassP := by
      funext u
      have : wpSub L (L.weierstrassP z) = fun u => L.weierstrassP u - L.weierstrassP z := rfl
      rw [this, deriv_sub_const, PeriodPair.deriv_weierstrassP]
    intro i hi
    interval_cases i
    · rw [iteratedDeriv_zero]; simp [wpSub]
    · rw [iteratedDeriv_one, hd]; exact h
    · rw [iteratedDeriv_succ, iteratedDeriv_one, hd]; exact h2
  have := Finset.single_le_sum (f := fun q => ordQ L (wpSub_doublyPeriodic L (L.weierstrassP z)) q)
    (fun q hq => by linarith [(hS1 q hq).1]) ha
  linarith

theorem prop_3_7_local' :
    (∀ z ∉ L.lattice, deriv L.weierstrassP z = L.derivWeierstrassP z) ∧
      (∀ z ∉ L.lattice, L.derivWeierstrassP z = 0 → deriv L.derivWeierstrassP z ≠ 0) ∧
      ∀ ω ∈ L.lattice, ∃ g : ℂ → ℂ, AnalyticAt ℂ g ω ∧ g ω = 0 ∧ deriv g ω = -1 / 2 ∧
        g =ᶠ[𝓝[≠] ω] fun z => L.weierstrassP z / L.derivWeierstrassP z := by
  refine ⟨fun z _ => PeriodPair.deriv_weierstrassP L ▸ rfl, fun z hz h => deriv_ne_zero_of_dwp_zero L hz h, ?_⟩
  intro ω hω
  set A : ℂ → ℂ := fun z => L.weierstrassPExcept ω z - 1 / ω ^ 2 with hA
  set B : ℂ → ℂ := fun z => L.derivWeierstrassPExcept ω z with hB
  have hAa : AnalyticAt ℂ A ω := (L.analyticAt_weierstrassPExcept ω).sub analyticAt_const
  have hBa : AnalyticAt ℂ B ω := L.analyticAt_derivWeierstrassPExcept ω
  set Q : ℂ → ℂ := fun z => (1 + A z * (z - ω) ^ 2) / (-2 + B z * (z - ω) ^ 3) with hQ
  have hden : (-2 + B ω * (ω - ω) ^ 3) ≠ 0 := by simp
  have hQa : AnalyticAt ℂ Q ω := by
    refine AnalyticAt.div ?_ ?_ hden
    · fun_prop
    · fun_prop
  have hQω : Q ω = -1 / 2 := by simp [hQ]; norm_num
  refine ⟨fun z => (z - ω) * Q z, by fun_prop, by simp, ?_, ?_⟩
  · have h1 : HasDerivAt (fun z => (z - ω) * Q z) (1 * Q ω + (ω - ω) * deriv Q ω) ω :=
      ((hasDerivAt_id ω).sub_const ω).mul hQa.differentiableAt.hasDerivAt
    rw [h1.deriv]; simp [hQω]
  · filter_upwards [self_mem_nhdsWithin] with z (hzω : z ≠ ω)
    have hw : z - ω ≠ 0 := sub_ne_zero.2 hzω
    have hP : L.weierstrassP z = 1 / (z - ω) ^ 2 + A z := by
      have := L.weierstrassPExcept_add ⟨ω, hω⟩ z
      simp only [hA]; simp only at this; linear_combination -this
    have hdP : L.derivWeierstrassP z = B z - 2 / (z - ω) ^ 3 := by
      have := L.derivWeierstrassPExcept_sub ⟨ω, hω⟩ z
      simp only [hB]; simp only at this; linear_combination -this
    rw [hP, hdP]
    simp only [hQ]
    by_cases hD : -2 + B z * (z - ω) ^ 3 = 0
    · have : B z - 2 / (z - ω) ^ 3 = 0 := by
        field_simp
        linear_combination hD
      rw [this, hD]; simp
    · have : B z - 2 / (z - ω) ^ 3 ≠ 0 := by
        intro h0; apply hD; field_simp at h0; linear_combination h0
      field_simp
      ring

lemma mk_eq_of_coords {z v : ℂ} (hz : z ∉ L.lattice) (hv : v ∉ L.lattice)
    (h1 : L.weierstrassP z = L.weierstrassP v) (h2 : L.derivWeierstrassP z = L.derivWeierstrassP v) :
    (Submodule.Quotient.mk z : ℂ ⧸ L.lattice) = Submodule.Quotient.mk v := by
  apply (prop_3_7_bijective' L).1
  simp only [toCurveQuot_mk]
  obtain ⟨h3, e3⟩ := toCurve_of_notMem L hz
  obtain ⟨h4, e4⟩ := toCurve_of_notMem L hv
  rw [e3, e4]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨h1, by rw [h2]⟩

end ToCurveB

section Add

variable (L : PeriodPair)

lemma wp_expand (ω : ℂ) (hω : ω ∈ L.lattice) (z : ℂ) :
    L.weierstrassP z = 1 / (z - ω) ^ 2 + (L.weierstrassPExcept ω z - 1 / ω ^ 2) := by
  have := L.weierstrassPExcept_add ⟨ω, hω⟩ z
  simp only at this
  linear_combination -this

lemma dwp_expand (ω : ℂ) (hω : ω ∈ L.lattice) (z : ℂ) :
    L.derivWeierstrassP z = L.derivWeierstrassPExcept ω z - 2 / (z - ω) ^ 3 := by
  have := L.derivWeierstrassPExcept_sub ⟨ω, hω⟩ z
  simp only at this
  linear_combination -this

/-- The function `℘' - m℘ - c` defining a line. -/
noncomputable def lineF (m c : ℂ) : ℂ → ℂ :=
  fun u => L.derivWeierstrassP u - m * L.weierstrassP u - c

lemma lineF_doublyPeriodic (m c : ℂ) : IsDoublyPeriodic L.lattice (lineF L m c) := by
  refine ⟨?_, fun ω hω u => ?_⟩
  · have h1 := L.meromorphic_derivWeierstrassP
    have h2 := L.meromorphic_weierstrassP
    unfold lineF
    fun_prop
  · simp [lineF, L.weierstrassP_add_coe u ⟨ω, hω⟩, L.derivWeierstrassP_add_coe u ⟨ω, hω⟩]

lemma lineF_analytic (m c : ℂ) {z : ℂ} (hz : z ∉ L.lattice) : AnalyticAt ℂ (lineF L m c) z :=
  ((L.analyticOnNhd_derivWeierstrassP z hz).sub
    (analyticAt_const.mul (L.analyticOnNhd_weierstrassP z hz))).sub analyticAt_const

lemma lineF_order (m c : ℂ) : meromorphicOrderAt (lineF L m c) 0 = -(3 : ℕ) := by
  have hm : MeromorphicAt (lineF L m c) 0 := (lineF_doublyPeriodic L m c).1 0
  have key : meromorphicOrderAt (lineF L m c) 0 = ((-3 : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_eq_int_iff hm]
    set A : ℂ → ℂ := fun z => L.weierstrassPExcept 0 z - 1 / (0 : ℂ) ^ 2 with hA
    set B : ℂ → ℂ := fun z => L.derivWeierstrassPExcept 0 z with hB
    have hAa : AnalyticAt ℂ A 0 := (L.analyticAt_weierstrassPExcept 0).sub analyticAt_const
    have hBa : AnalyticAt ℂ B 0 := L.analyticAt_derivWeierstrassPExcept 0
    refine ⟨fun z => -2 - m * z + z ^ 3 * (B z - m * A z - c), by fun_prop, by simp, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0)
    have hP := wp_expand L 0 L.lattice.zero_mem z
    have hdP := dwp_expand L 0 L.lattice.zero_mem z
    simp only [lineF, hP, hdP, smul_eq_mul, sub_zero]
    rw [zpow_neg]
    simp only [hA, hB]
    field_simp
    ring
  rw [key]
  rfl

lemma lineF_zero_set (m c : ℂ) :
    ∃ S : Finset (ℂ ⧸ L.lattice), (∀ q ∈ S, 1 ≤ ordQ L (lineF_doublyPeriodic L m c) q ∧ q ≠ 0) ∧
      (∀ z ∉ L.lattice, 1 ≤ ord (lineF L m c) z → Submodule.Quotient.mk z ∈ S) ∧
      ∑ q ∈ S, ordQ L (lineF_doublyPeriodic L m c) q = 3 ∧
      ∑ q ∈ S, ordQ L (lineF_doublyPeriodic L m c) q • q = 0 := by
  have := zero_set L (lineF_doublyPeriodic L m c) 3 (by norm_num)
    (lineF_order L m c) (fun z hz => lineF_analytic L m c hz)
  simpa using this

lemma one_le_ord_lineF_iff (m c : ℂ) {z : ℂ} (hz : z ∉ L.lattice) :
    1 ≤ ord (lineF L m c) z ↔ lineF L m c z = 0 := by
  have hf0 : ∃ y, meromorphicOrderAt (lineF L m c) y ≠ ⊤ :=
    ⟨0, by rw [lineF_order L m c]; exact WithTop.coe_ne_top⟩
  have := natCast_le_ord_iff (lineF_analytic L m c hz)
    (ord_top_ne L (lineF_doublyPeriodic L m c) hf0 z) 1
  simpa using this

lemma vieta {x₁ x₂ x m c g₂ g₃ : ℂ} (h₁ : 4 * x₁ ^ 3 - g₂ * x₁ - g₃ = (m * x₁ + c) ^ 2)
    (h₂ : 4 * x₂ ^ 3 - g₂ * x₂ - g₃ = (m * x₂ + c) ^ 2)
    (h : 4 * x ^ 3 - g₂ * x - g₃ = (m * x + c) ^ 2) (h12 : x₁ ≠ x₂) (hx1 : x ≠ x₁)
    (hx2 : x ≠ x₂) : x = m ^ 2 / 4 - x₁ - x₂ := by
  set r := m ^ 2 / 4 - x₁ - x₂ with hr
  set α := -g₂ - 2 * m * c - 4 * (x₁ * x₂ + (x₁ + x₂) * r) with hα
  set β := -g₃ - c ^ 2 + 4 * x₁ * x₂ * r with hβ
  have e1 : α * x₁ + β = 0 := by
    simp only [hα, hβ, hr]; linear_combination h₁
  have e2 : α * x₂ + β = 0 := by
    simp only [hα, hβ, hr]; linear_combination h₂
  have hα0 : α = 0 := by
    have : α * (x₁ - x₂) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.1 this with h0 | h0
    · exact h0
    · exact absurd (sub_eq_zero.1 h0) h12
  have hβ0 : β = 0 := by rw [hα0] at e1; linear_combination e1
  have : 4 * ((x - x₁) * (x - x₂) * (x - r)) = 0 := by
    simp only [hα, hβ, hr] at hα0 hβ0 ⊢
    linear_combination h - x * hα0 - hβ0
  rcases mul_eq_zero.1 this with h0 | h0
  · norm_num at h0
  rcases mul_eq_zero.1 h0 with h0 | h0
  · rcases mul_eq_zero.1 h0 with h0 | h0
    · exact absurd (sub_eq_zero.1 h0) hx1
    · exact absurd (sub_eq_zero.1 h0) hx2
  · exact sub_eq_zero.1 h0

theorem add_gen {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (hzw : z + w ∉ L.lattice)
    (hzw' : z - w ∉ L.lattice) (h2z : z + z + w ∉ L.lattice) (h2w : z + w + w ∉ L.lattice) :
    toCurve L (z + w) = toCurve L z + toCurve L w := by
  classical
  have hx : L.weierstrassP z ≠ L.weierstrassP w := by
    intro h
    rcases wp_eq_cases L hz hw h.symm with h3 | h3
    · apply hzw'
      have := L.lattice.neg_mem ((Submodule.Quotient.eq _).1 h3)
      simpa using this
    · apply hzw
      have := (Submodule.Quotient.eq _).1 h3
      simpa [add_comm] using this
  set x₁ := L.weierstrassP z with hx₁
  set x₂ := L.weierstrassP w with hx₂
  set Y₁ := L.derivWeierstrassP z with hY₁
  set Y₂ := L.derivWeierstrassP w with hY₂
  have hx12 : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hx
  set m := (Y₁ - Y₂) / (x₁ - x₂) with hm
  set c := Y₁ - m * x₁ with hc
  have hYw : Y₂ = m * x₂ + c := by
    simp only [hc, hm]; field_simp; ring
  obtain ⟨S, hS1, hS2, hS3, hS4⟩ := lineF_zero_set L m c
  have ha : (Submodule.Quotient.mk z : ℂ ⧸ L.lattice) ∈ S :=
    hS2 z hz ((one_le_ord_lineF_iff L m c hz).2 (by simp [lineF, hc, hx₁, hY₁]))
  have hb : (Submodule.Quotient.mk w : ℂ ⧸ L.lattice) ∈ S :=
    hS2 w hw ((one_le_ord_lineF_iff L m c hw).2 (by simp only [lineF]; rw [← hx₂, ← hY₂, hYw]; ring))
  have hab : (Submodule.Quotient.mk z : ℂ ⧸ L.lattice) ≠ Submodule.Quotient.mk w :=
    fun h => hzw' (by simpa using (Submodule.Quotient.eq _).1 h)
  obtain ⟨u, huS, hu0, -, -⟩ := comb_three S _ (fun q hq => (hS1 q hq).1) hS3 hS4 ha hb hab
  have hu : u = Submodule.Quotient.mk (-(z + w)) := by
    have : (Submodule.Quotient.mk (z + w) : ℂ ⧸ L.lattice) + u = 0 := by
      rw [Submodule.Quotient.mk_add, ← hu0]
    rw [Submodule.Quotient.mk_neg]
    exact eq_neg_of_add_eq_zero_right this
  set v := -(z + w) with hv
  have hvL : v ∉ L.lattice := neg_notMem_lattice L hzw
  have hord : 1 ≤ ord (lineF L m c) v := by
    have := (hS1 u huS).1
    rw [hu, ordQ_mk] at this
    exact this
  have hfv : L.derivWeierstrassP v = m * L.weierstrassP v + c := by
    have := (one_le_ord_lineF_iff L m c hvL).1 hord
    simp only [lineF] at this
    linear_combination this
  have hxv1 : L.weierstrassP v ≠ x₁ := by
    intro h
    have h' : (Submodule.Quotient.mk z : ℂ ⧸ L.lattice) = Submodule.Quotient.mk v := by
      refine mk_eq_of_coords L hz hvL h.symm ?_
      rw [hfv, h]; simp only [hc, hY₁]; ring
    apply h2z
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add,
      ← hu0, hu]
    rw [← h']
    abel
  have hxv2 : L.weierstrassP v ≠ x₂ := by
    intro h
    have h' : (Submodule.Quotient.mk w : ℂ ⧸ L.lattice) = Submodule.Quotient.mk v := by
      refine mk_eq_of_coords L hw hvL h.symm ?_
      rw [hfv, h, ← hYw]
    apply h2w
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add,
      ← hu0, hu]
    rw [← h']
  have hF : ∀ y ∉ L.lattice, 4 * L.weierstrassP y ^ 3 - L.g₂ * L.weierstrassP y - L.g₃ =
      L.derivWeierstrassP y ^ 2 := fun y hy => (L.derivWeierstrassP_sq y hy).symm
  have hxvr : L.weierstrassP v = m ^ 2 / 4 - x₁ - x₂ := by
    refine vieta (c := c) (g₂ := L.g₂) (g₃ := L.g₃) ?_ ?_ ?_ hx hxv1 hxv2
    · rw [hF z hz]; simp only [hc]; ring
    · rw [hF w hw, ← hY₂, hYw]
    · rw [hF v hvL, hfv]
  obtain ⟨h1, e1⟩ := toCurve_of_notMem L hz
  obtain ⟨h2, e2⟩ := toCurve_of_notMem L hw
  rw [e1, e2, WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  apply toCurve_eq_some L hzw
  · have : L.weierstrassP (z + w) = L.weierstrassP v := by
      rw [hv, L.weierstrassP_neg]
    rw [this, hxvr]
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope_of_X_ne hx, curveOf]
    simp only [hm]
    field_simp
    ring
  · have : L.derivWeierstrassP (z + w) = - L.derivWeierstrassP v := by
      rw [hv, L.derivWeierstrassP_neg, neg_neg]
    rw [this, hfv, hxvr]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope_of_X_ne hx, curveOf]
    simp only [hc, hm]
    field_simp
    ring

lemma lattice_countable : (L.lattice : Set ℂ).Countable := by
  have : (L.lattice : Set ℂ) =
      Set.range (fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂) := by
    ext x
    simp [PeriodPair.mem_lattice]
  rw [this]
  exact Set.countable_range _

lemma exists_t (l : List (ℂ × ℤ)) (hl : ∀ p ∈ l, p.2 ≠ 0) :
    ∃ t : ℂ, ∀ p ∈ l, p.1 + p.2 * t ∉ L.lattice := by
  have hc : (⋃ p ∈ l, {t : ℂ | p.1 + p.2 * t ∈ L.lattice}).Countable := by
    refine Set.Countable.biUnion (l.finite_toSet.countable) fun p hp => ?_
    have hp2 : (p.2 : ℂ) ≠ 0 := by exact_mod_cast hl p hp
    have hinj : Function.Injective (fun t : ℂ => p.1 + p.2 * t) := fun a b h => by
      have := add_left_cancel h
      exact mul_left_cancel₀ hp2 this
    exact (lattice_countable L).preimage hinj
  obtain ⟨t, ht⟩ := exists_complex_notMem hc
  refine ⟨t, fun p hp h => ht ?_⟩
  simp only [Set.mem_iUnion]
  exact ⟨p, hp, h⟩

theorem cor_3_9' (z w : ℂ) : toCurve L (z + w) = toCurve L z + toCurve L w := by
  classical
  by_cases hz : z ∈ L.lattice
  · rw [toCurve_of_mem L hz, zero_add]
    have := toCurve_add_coe L w ⟨z, hz⟩
    rw [add_comm]; exact this
  by_cases hw : w ∈ L.lattice
  · rw [toCurve_of_mem L hw, add_zero]
    exact toCurve_add_coe L z ⟨w, hw⟩
  by_cases hzw : z + w ∈ L.lattice
  · rw [toCurve_of_mem L hzw]
    have h1 : toCurve L w = toCurve L (-z + ((⟨z + w, hzw⟩ : L.lattice) : ℂ)) := by
      congr 1; simp
    rw [h1, toCurve_add_coe, toCurve_neg]
    simp
  -- generic case
  obtain ⟨t, ht⟩ := exists_t L [(w, -1), (z + w, -1), (z - w, 1), (z + z + w, -1),
    (z + w + w, -2), (0, 1), (z + w, -2), ((z + w) + (z + w), -1), (z + w, 1), (w, -2),
    (w + w, -1), (w, 1)] (by intro p hp; simp at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have mk_ht : ∀ (A : ℂ) (k : ℤ) (X : ℂ), (A, k) ∈ [(w, -1), (z + w, -1), (z - w, 1),
      (z + z + w, -1), (z + w + w, -2), (0, 1), (z + w, -2), ((z + w) + (z + w), -1),
      (z + w, 1), (w, -2), (w + w, -1), (w, 1)] → X = A + k * t → X ∉ L.lattice := by
    intro A k X hmem hX
    rw [hX]; exact ht (A, k) hmem
  have ht1 : w - t ∉ L.lattice := mk_ht w (-1) _ (by simp) (by push_cast; ring)
  have ht2 : z + (w - t) ∉ L.lattice := mk_ht (z + w) (-1) _ (by simp) (by push_cast; ring)
  have ht3 : z - (w - t) ∉ L.lattice := mk_ht (z - w) 1 _ (by simp) (by push_cast; ring)
  have ht4 : z + z + (w - t) ∉ L.lattice := mk_ht (z + z + w) (-1) _ (by simp) (by push_cast; ring)
  have ht5 : z + (w - t) + (w - t) ∉ L.lattice :=
    mk_ht (z + w + w) (-2) _ (by simp) (by push_cast; ring)
  have ht6 : t ∉ L.lattice := mk_ht 0 1 _ (by simp) (by push_cast; ring)
  have ht7 : z + (w - t) - t ∉ L.lattice := mk_ht (z + w) (-2) _ (by simp) (by push_cast; ring)
  have ht8 : z + (w - t) + (z + (w - t)) + t ∉ L.lattice :=
    mk_ht ((z + w) + (z + w)) (-1) _ (by simp) (by push_cast; ring)
  have ht9 : z + (w - t) + t + t ∉ L.lattice := mk_ht (z + w) 1 _ (by simp) (by push_cast; ring)
  have ht10 : w - t - t ∉ L.lattice := mk_ht w (-2) _ (by simp) (by push_cast; ring)
  have ht11 : w - t + (w - t) + t ∉ L.lattice :=
    mk_ht (w + w) (-1) _ (by simp) (by push_cast; ring)
  have ht12 : w - t + t + t ∉ L.lattice := mk_ht w 1 _ (by simp) (by push_cast; ring)
  have hzwt : z + (w - t) + t = z + w := by ring
  have hwt : w - t + t = w := by ring
  have e1 := add_gen L hz ht1 ht2 ht3 ht4 ht5
  have e2 := add_gen L ht2 ht6 (by rw [hzwt]; exact hzw) ht7 ht8 ht9
  have e3 := add_gen L ht1 ht6 (by rw [hwt]; exact hw) ht10 ht11 ht12
  rw [hzwt] at e2
  rw [hwt] at e3
  rw [e2, e1, e3]
  abel

end Add

section Rigidity

lemma exists_t_local (L : PeriodPair) : ∃ t : ℂ → ℂ, AnalyticAt ℂ t 0 ∧ t 0 = 0 ∧ deriv t 0 = 1 ∧
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), t z ^ 2 * L.weierstrassP z = 1 := by
  set A : ℂ → ℂ := fun z => L.weierstrassPExcept 0 z - 1 / (0 : ℂ) ^ 2 with hA
  have hAa : AnalyticAt ℂ A 0 := (L.analyticAt_weierstrassPExcept 0).sub analyticAt_const
  have hA0 : A 0 = 0 := by simp [hA]
  set q : ℂ → ℂ := fun z => 1 + A z * z ^ 2 with hq
  have hqa : AnalyticAt ℂ q 0 := by fun_prop
  have hq0 : q 0 = 1 := by simp [hq, hA0]
  have hslit : q 0 ∈ Complex.slitPlane := by rw [hq0]; exact Complex.one_mem_slitPlane
  set r : ℂ → ℂ := fun z => Complex.exp (-(Complex.log (q z)) / 2) with hr
  have hra : AnalyticAt ℂ r 0 := by
    have : AnalyticAt ℂ (fun z => Complex.log (q z)) 0 := hqa.clog hslit
    simp only [hr]
    fun_prop
  have hr0 : r 0 = 1 := by simp [hr, hq0]
  refine ⟨fun z => z * r z, by fun_prop, by simp, ?_, ?_⟩
  · have h := (hasDerivAt_id' (0 : ℂ)).mul hra.differentiableAt.hasDerivAt
    have e : (fun z : ℂ => z * r z) = (fun x : ℂ => x) * r := rfl
    rw [e, h.deriv]
    simp [hr0]
  · have hne : ∀ᶠ z in 𝓝 (0 : ℂ), q z ≠ 0 := hqa.continuousAt.eventually_ne (by rw [hq0]; exact one_ne_zero)
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hne] with z (hz : z ≠ 0) hqz
    have hP := wp_expand L 0 L.lattice.zero_mem z
    have hr2 : r z ^ 2 = (q z)⁻¹ := by
      simp only [hr]
      rw [← Complex.exp_nat_mul,
        show ((2 : ℕ) : ℂ) * (-(Complex.log (q z)) / 2) = -(Complex.log (q z)) by push_cast; ring,
        Complex.exp_neg, Complex.exp_log hqz]
    have hzP : z ^ 2 * L.weierstrassP z = q z := by
      rw [hP]
      simp only [hq, hA, sub_zero]
      field_simp
    show (z * r z) ^ 2 * L.weierstrassP z = 1
    calc (z * r z) ^ 2 * L.weierstrassP z = r z ^ 2 * (z ^ 2 * L.weierstrassP z) := by ring
      _ = 1 := by rw [hzP, hr2]; exact inv_mul_cancel₀ hqz

lemma dwp_ne_zero_near (L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), L.derivWeierstrassP z ≠ 0 := by
  have hf0 : meromorphicOrderAt (lineF L 0 0) 0 ≠ ⊤ := by
    rw [lineF_order]; exact WithTop.coe_ne_top
  have := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    ((lineF_doublyPeriodic L 0 0).1 0)).1 hf0
  filter_upwards [this] with z hz
  simpa [lineF] using hz

lemma notMem_near (L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  have h : ∀ᶠ y in 𝓝 (0 : ℂ), y ∈ ((L.lattice : Set ℂ) \ {0})ᶜ :=
    L.compl_lattice_sdiff_singleton_mem_nhds 0
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds h, self_mem_nhdsWithin] with y h1 h2 hy
  exact h1 ⟨hy, h2⟩

lemma wp_eq_near_zero {L L' : PeriodPair} (h2 : L.g₂ = L'.g₂) (h3 : L.g₃ = L'.g₃) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), L.weierstrassP z = L'.weierstrassP z := by
  obtain ⟨t, hta, ht0, htd, htq⟩ := exists_t_local L
  obtain ⟨t', hta', ht0', htd', htq'⟩ := exists_t_local L'
  have hd' : deriv t' 0 ≠ 0 := by rw [htd']; exact one_ne_zero
  have hsd := hta'.hasStrictDerivAt
  set R : ℂ → ℂ := hsd.localInverse _ _ _ hd' with hR
  have hRa : AnalyticAt ℂ R (t' 0) := hta'.analyticAt_localInverse hd'
  have hRright : ∀ᶠ y in 𝓝 (t' 0), t' (R y) = y := hsd.eventually_right_inverse hd'
  have hRleft : R (t' 0) = 0 := (hsd.eventually_left_inverse hd').self_of_nhds
  have hRd : HasDerivAt R 1 (t' 0) := by
    have := (hsd.to_localInverse hd').hasDerivAt
    exact this.congr_deriv (by rw [htd']; simp)
  have e0 : t 0 = t' 0 := by rw [ht0, ht0']
  have hRa' : AnalyticAt ℂ R (t 0) := by rw [e0]; exact hRa
  have hRd' : HasDerivAt R 1 (t 0) := by rw [e0]; exact hRd
  have hRright' : ∀ᶠ y in 𝓝 (t 0), t' (R y) = y := by rw [e0]; exact hRright
  set ψ : ℂ → ℂ := fun z => R (t z) with hψ
  have hψa : AnalyticAt ℂ ψ 0 := hRa'.comp hta
  have hψ0 : ψ 0 = 0 := by simp only [hψ]; rw [e0]; exact hRleft
  have hψd : deriv ψ 0 = 1 := by
    have := hRd'.comp 0 hta.differentiableAt.hasDerivAt
    have e : ψ = R ∘ t := rfl
    rw [e, this.deriv, htd]; ring
  have hψt : ∀ᶠ z in 𝓝 (0 : ℂ), t' (ψ z) = t z :=
    (hta.continuousAt.tendsto).eventually hRright'
  have hψc : ContinuousAt ψ 0 := hψa.continuousAt
  -- punctured neighbourhood facts
  have E1 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), t z ≠ 0 := by
    filter_upwards [htq] with z hz h0
    rw [h0] at hz; simp at hz
  have E2 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z ≠ 0 := by
    filter_upwards [E1, eventually_nhdsWithin_of_eventually_nhds hψt] with z h1 h2 h0
    apply h1
    rw [← h2, h0, ht0']
  have htend : Filter.Tendsto ψ (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, E2⟩
    have := hψc.tendsto
    rw [hψ0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have E3 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), t' (ψ z) ^ 2 * L'.weierstrassP (ψ z) = 1 := htend.eventually htq'
  have E5 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z ∉ L'.lattice := htend.eventually (notMem_near L')
  have E4 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), L'.weierstrassP (ψ z) = L.weierstrassP z := by
    filter_upwards [E1, E3, htq, eventually_nhdsWithin_of_eventually_nhds hψt] with z h1 h3' h4 h5
    rw [h5] at h3'
    have : t z ^ 2 * (L'.weierstrassP (ψ z) - L.weierstrassP z) = 0 := by
      linear_combination h3' - h4
    rcases mul_eq_zero.1 this with h | h
    · exact absurd ((pow_eq_zero_iff two_ne_zero).1 h) h1
    · exact sub_eq_zero.1 h
  have E6 : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ ψ z := hψa.eventually_analyticAt
  have hall : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice ∧ L.derivWeierstrassP z ≠ 0 ∧
      ψ z ∉ L'.lattice ∧ L'.weierstrassP (ψ z) = L.weierstrassP z ∧ AnalyticAt ℂ ψ z := by
    filter_upwards [notMem_near L, dwp_ne_zero_near L, E5, E4,
      eventually_nhdsWithin_of_eventually_nhds E6] with z a b c d e using ⟨a, b, c, d, e⟩
  obtain ⟨U, hU, hUo, h0U⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hall)
  have hderiv : ∀ z ∈ U, z ≠ 0 → deriv ψ z ^ 2 = 1 := by
    intro z hzU hz0
    obtain ⟨a, b, c, d, e⟩ := hU z hzU hz0
    have hψz : HasDerivAt ψ (deriv ψ z) z := e.differentiableAt.hasDerivAt
    have hwp' : HasDerivAt L'.weierstrassP (L'.derivWeierstrassP (ψ z)) (ψ z) := by
      have := (L'.analyticOnNhd_weierstrassP (ψ z) c).differentiableAt.hasDerivAt
      rwa [PeriodPair.deriv_weierstrassP] at this
    have hcomp := hwp'.comp z hψz
    have hwp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
      have := (L.analyticOnNhd_weierstrassP z a).differentiableAt.hasDerivAt
      rwa [PeriodPair.deriv_weierstrassP] at this
    have hnhds : U \ {0} ∈ 𝓝 z := (hUo.sdiff isClosed_singleton).mem_nhds ⟨hzU, hz0⟩
    have heq : (L'.weierstrassP ∘ ψ) =ᶠ[𝓝 z] L.weierstrassP := by
      filter_upwards [hnhds] with y hy
      exact (hU y hy.1 hy.2).2.2.2.1
    have hcomp' := hwp.congr_of_eventuallyEq heq
    have hprod : L'.derivWeierstrassP (ψ z) * deriv ψ z = L.derivWeierstrassP z :=
      hcomp.unique hcomp'
    have hsq1 := L'.derivWeierstrassP_sq (ψ z) c
    have hsq2 := L.derivWeierstrassP_sq z a
    rw [d, ← h2, ← h3] at hsq1
    have : L.derivWeierstrassP z ^ 2 * (deriv ψ z ^ 2 - 1) = 0 := by
      have e1 : L'.derivWeierstrassP (ψ z) ^ 2 = L.derivWeierstrassP z ^ 2 := by
        rw [hsq1, hsq2]
      calc L.derivWeierstrassP z ^ 2 * (deriv ψ z ^ 2 - 1)
          = (L'.derivWeierstrassP (ψ z) * deriv ψ z) ^ 2 - L.derivWeierstrassP z ^ 2 := by
            rw [← e1]; ring
        _ = 0 := by rw [hprod]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 h) b
    · exact sub_eq_zero.1 h
  have hcont : ContinuousAt (deriv ψ) 0 := hψa.deriv.continuousAt
  have hne1 : ∀ᶠ y in 𝓝 (0 : ℂ), deriv ψ y ≠ -1 :=
    hcont.eventually_ne (by rw [hψd]; norm_num)
  have hUev : ∀ᶠ y in 𝓝 (0 : ℂ), y ∈ U := hUo.mem_nhds h0U
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (hUev.and (hne1.and E6))
  have hderiv1 : ∀ y ∈ Metric.ball (0 : ℂ) ε, deriv ψ y = 1 := by
    intro y hy
    obtain ⟨hyU, hy1, hy2⟩ := hball y hy
    by_cases hy0 : y = 0
    · rw [hy0, hψd]
    · have h := hderiv y hyU hy0
      have : (deriv ψ y - 1) * (deriv ψ y + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · exact sub_eq_zero.1 h'
      · exact absurd (eq_neg_of_add_eq_zero_left h') hy1
  have hdiff : DifferentiableOn ℂ (fun y => ψ y - y) (Metric.ball (0 : ℂ) ε) := fun y hy =>
    ((hball y hy).2.2.differentiableAt.sub differentiableAt_id).differentiableWithinAt
  have hconst : ∀ y ∈ Metric.ball (0 : ℂ) ε, ψ y = y := by
    intro y hy
    have hf0 : (Metric.ball (0 : ℂ) ε).EqOn (deriv fun y => ψ y - y) 0 := by
      intro u hu
      rw [deriv_fun_sub (hball u hu).2.2.differentiableAt differentiableAt_fun_id, hderiv1 u hu]
      simp
    have := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) ε).isPreconnected
      hdiff hf0 hy (Metric.mem_ball_self hε)
    simp only [hψ0, sub_zero] at this
    linear_combination this
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with y hy hy0
  have := (hU y (hball y hy).1 hy0).2.2.2.1
  rw [hconst y hy] at this
  exact this.symm

lemma lattice_le_of_wp_eq {L L' : PeriodPair}
    (h : ∀ᶠ z in 𝓝[≠] (0 : ℂ), L.weierstrassP z = L'.weierstrassP z) :
    L.lattice ≤ L'.lattice := by
  intro ω hω
  by_contra hω'
  have hmero : Meromorphic (fun z => L.weierstrassP z - L'.weierstrassP z) :=
    L.meromorphic_weierstrassP.sub L'.meromorphic_weierstrassP
  have htop0 : meromorphicOrderAt (fun z => L.weierstrassP z - L'.weierstrassP z) 0 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [h] with z hz
    simp [hz]
  have := (hmero.exists_meromorphicOrderAt_eq_top_iff_forall.1 ⟨0, htop0⟩) ω
  rw [meromorphicOrderAt_eq_top_iff] at this
  have hcongr : L.weierstrassP =ᶠ[𝓝[≠] ω] L'.weierstrassP := by
    filter_upwards [this] with z hz
    exact sub_eq_zero.1 hz
  have h1 := meromorphicOrderAt_congr hcongr
  rw [L.order_weierstrassP ω hω] at h1
  have h2 : 0 ≤ meromorphicOrderAt L'.weierstrassP ω :=
    (L'.analyticOnNhd_weierstrassP ω hω').meromorphicOrderAt_nonneg
  rw [← h1] at h2
  exact absurd h2 (by decide)

theorem lattice_eq_of_g_eq {L L' : PeriodPair} (h2 : L.g₂ = L'.g₂) (h3 : L.g₃ = L'.g₃) :
    L.lattice = L'.lattice :=
  le_antisymm (lattice_le_of_wp_eq (wp_eq_near_zero h2 h3))
    (lattice_le_of_wp_eq (wp_eq_near_zero h2.symm h3.symm))

end Rigidity

section Surj

lemma exists_scale {A B a b : ℂ} (hΔ₀ : A ^ 3 - 27 * B ^ 2 ≠ 0) (hΔ : a ^ 3 - 27 * b ^ 2 ≠ 0)
    (h : A ^ 3 * b ^ 2 = a ^ 3 * B ^ 2) : ∃ u : ℂ, u ≠ 0 ∧ u ^ 4 * A = a ∧ u ^ 6 * B = b := by
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by
      intro hb; apply hΔ; subst hb; norm_num
    have hA : A = 0 := by
      have : A ^ 3 * b ^ 2 = 0 := by rw [h]; ring
      rcases mul_eq_zero.1 this with h' | h'
      · exact pow_eq_zero_iff (by norm_num) |>.1 h'
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h') hb
    have hB : B ≠ 0 := by
      intro hB; apply hΔ₀; rw [hA, hB]; norm_num
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (b / B) (by norm_num : 0 < 6)
    have hu0 : u ≠ 0 := by
      rintro rfl
      have : b / B = 0 := by rw [← hu]; norm_num
      exact (div_ne_zero hb hB) this
    refine ⟨u, hu0, by rw [hA]; ring, ?_⟩
    rw [hu]; field_simp
  by_cases hb : b = 0
  · subst hb
    have hB : B = 0 := by
      have : a ^ 3 * B ^ 2 = 0 := by rw [← h]; ring
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h') ha
      · exact pow_eq_zero_iff (by norm_num) |>.1 h'
    have hA : A ≠ 0 := by
      intro hA; apply hΔ₀; rw [hA, hB]; norm_num
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (a / A) (by norm_num : 0 < 4)
    have hu0 : u ≠ 0 := by
      rintro rfl
      have : a / A = 0 := by rw [← hu]; norm_num
      exact (div_ne_zero ha hA) this
    refine ⟨u, hu0, ?_, by rw [hB]; ring⟩
    rw [hu]; field_simp
  have hA : A ≠ 0 := by
    intro hA
    have : a ^ 3 * B ^ 2 = 0 := by rw [← h, hA]; ring
    rcases mul_eq_zero.1 this with h' | h'
    · exact ha (pow_eq_zero_iff (by norm_num) |>.1 h')
    · apply hΔ₀; rw [hA, pow_eq_zero_iff (by norm_num) |>.1 h']; norm_num
  have hB : B ≠ 0 := by
    intro hB
    have : A ^ 3 * b ^ 2 = 0 := by rw [h, hB]; ring
    rcases mul_eq_zero.1 this with h' | h'
    · exact hA (pow_eq_zero_iff (by norm_num) |>.1 h')
    · exact hb (pow_eq_zero_iff (by norm_num) |>.1 h')
  obtain ⟨u₀, hu₀⟩ := IsAlgClosed.exists_pow_nat_eq (a / A) (by norm_num : 0 < 4)
  have hu₀0 : u₀ ≠ 0 := by
    rintro rfl
    have : a / A = 0 := by rw [← hu₀]; norm_num
    exact (div_ne_zero ha hA) this
  have h4 : u₀ ^ 4 * A = a := by rw [hu₀]; field_simp
  have hsq : (u₀ ^ 6 * B) ^ 2 = b ^ 2 := by
    have : (u₀ ^ 6 * B) ^ 2 = (u₀ ^ 4) ^ 3 * B ^ 2 := by ring
    rw [this, hu₀]
    field_simp
    linear_combination -h
  have hsq' : (u₀ ^ 6 * B - b) * (u₀ ^ 6 * B + b) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hsq' with h' | h'
  · exact ⟨u₀, hu₀0, h4, sub_eq_zero.1 h'⟩
  · refine ⟨Complex.I * u₀, mul_ne_zero Complex.I_ne_zero hu₀0, ?_, ?_⟩
    · have : (Complex.I * u₀) ^ 4 = u₀ ^ 4 := by
        rw [mul_pow]; norm_num [show Complex.I ^ 4 = 1 from Complex.I_pow_four]
      rw [this, h4]
    · have : (Complex.I * u₀) ^ 6 = -u₀ ^ 6 := by
        rw [mul_pow]
        have : Complex.I ^ 6 = -1 := by
          rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, Complex.I_pow_four, one_mul, Complex.I_sq]
        rw [this]; ring
      rw [this]
      linear_combination -h'

/-- The lattice `c · Λ`. -/
noncomputable def scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    have hinj : LinearMap.ker (LinearMap.mulLeft ℝ c : ℂ →ₗ[ℝ] ℂ) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro a b hab
      exact mul_left_cancel₀ hc hab
    have := L.indep.map' (LinearMap.mulLeft ℝ c : ℂ →ₗ[ℝ] ℂ) hinj
    convert this using 1
    ext i
    fin_cases i <;> simp

lemma g_scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) :
    (scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ ∧ (scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := by
  have h4 := G_of_lattice_eq_smul (L := L) (L' := scalePair L c hc) hc rfl 4
  have h6 := G_of_lattice_eq_smul (L := L) (L' := scalePair L c hc) hc rfl 6
  refine ⟨?_, ?_⟩
  · simp only [PeriodPair.g₂, h4]; ring
  · simp only [PeriodPair.g₃, h6]; ring

theorem exists_lattice_with_g (a b : ℂ) (hΔ : a ^ 3 - 27 * b ^ 2 ≠ 0) :
    ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b := by
  obtain ⟨τ, hτ⟩ := jFun_surjective (1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2))
  set L₀ := periodPairOf τ with hL₀
  have hΔ₀ := g₂_cube_sub_g₃_sq_ne_zero L₀
  have hj : 1728 * L₀.g₂ ^ 3 / (L₀.g₂ ^ 3 - 27 * L₀.g₃ ^ 2) =
      1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2) := hτ
  have h : L₀.g₂ ^ 3 * b ^ 2 = a ^ 3 * L₀.g₃ ^ 2 := by
    rw [div_eq_div_iff hΔ₀ hΔ] at hj
    linear_combination hj / 1728 / 27 * (-1)
  obtain ⟨u, hu0, hu4, hu6⟩ := exists_scale hΔ₀ hΔ h
  refine ⟨scalePair L₀ u⁻¹ (inv_ne_zero hu0), ?_⟩
  obtain ⟨e2, e3⟩ := g_scalePair L₀ u⁻¹ (inv_ne_zero hu0)
  refine ⟨?_, ?_⟩
  · rw [e2, inv_pow, inv_inv, hu4]
  · rw [e3, inv_pow, inv_inv, hu6]

end Surj

end CurveAux

/-- Proposition 3.7 (Milne, pdf p. 100), bijectivity: `ℂ/Λ → E(Λ)(ℂ)` is a bijection. -/
@[kb "milne2006ec" "Ch. III, Prop. 3.7, pdf p. 100"]
theorem prop_3_7_bijective (L : PeriodPair) : Function.Bijective (toCurveQuot L) :=
  CurveAux.prop_3_7_bijective' L

/-- Proposition 3.7 (Milne, pdf p. 100), local form: in Milne's local coordinates on `E(ℂ)` the
map `z ↦ (℘(z) : ℘'(z) : 1)` has nonzero derivative:
(i) at `z ∉ Λ` with `℘'(z) ≠ 0`, the coordinate `x` pulls back to `℘`, with `℘'(z) ≠ 0`;
(ii) at `z ∉ Λ` with `℘'(z) = 0`, the coordinate `y` pulls back to `℘'`, with `℘''(z) ≠ 0`;
(iii) at `ω ∈ Λ`, the coordinate `x/y` pulls back to `℘/℘'`, which extends holomorphically
across `ω` with value `0` and derivative `-1/2`. -/
@[kb "milne2006ec" "Ch. III, Prop. 3.7, pdf p. 100"]
theorem prop_3_7_local (L : PeriodPair) :
    (∀ z ∉ L.lattice, deriv L.weierstrassP z = L.derivWeierstrassP z) ∧
      (∀ z ∉ L.lattice, L.derivWeierstrassP z = 0 → deriv L.derivWeierstrassP z ≠ 0) ∧
      ∀ ω ∈ L.lattice, ∃ g : ℂ → ℂ, AnalyticAt ℂ g ω ∧ g ω = 0 ∧ deriv g ω = -1 / 2 ∧
        g =ᶠ[𝓝[≠] ω] fun z => L.weierstrassP z / L.derivWeierstrassP z :=
  CurveAux.prop_3_7_local' L

/-! ### The addition formula -/

/-- Corollary 3.9 (Milne, pdf p. 101): `z ↦ (℘(z) : ℘'(z) : 1)` is a homomorphism of groups
`ℂ/Λ → E(Λ)`. -/
@[kb "milne2006ec" "Ch. III, Cor. 3.9, pdf p. 101"]
theorem cor_3_9 (L : PeriodPair) (z w : ℂ) :
    toCurve L (z + w) = toCurve L z + toCurve L w :=
  CurveAux.cor_3_9' L z w

/-- Propositions 3.7 and Corollary 3.9 together: `ℂ/Λ ≅ E(Λ)(ℂ)` as groups. -/
@[kb "milne2006ec" "Ch. III, Prop. 3.7 and Cor. 3.9, pdf pp. 100–101"]
noncomputable def quotEquivCurve (L : PeriodPair) : ℂ ⧸ L.lattice ≃+ (curveOf L).toAffine.Point :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (toCurveQuot L) (by
      rintro ⟨z⟩ ⟨w⟩
      exact cor_3_9 L z w))
    (prop_3_7_bijective L)

/-- Proposition 3.8 (Milne, pdf p. 101), the addition formula:
`℘(z + z') = ¼((℘'(z) − ℘'(z'))/(℘(z) − ℘(z')))² − ℘(z) − ℘(z')`, for `z, z', z + z' ∉ Λ` with
`℘(z) ≠ ℘(z')` (where both sides are finite). -/
@[kb "milne2006ec" "Ch. III, Prop. 3.8, pdf p. 101"]
theorem prop_3_8 (L : PeriodPair) {z z' : ℂ} (hz : z ∉ L.lattice) (hz' : z' ∉ L.lattice)
    (hzz' : z + z' ∉ L.lattice) (hne : L.weierstrassP z ≠ L.weierstrassP z') :
    L.weierstrassP (z + z') =
      1 / 4 * ((L.derivWeierstrassP z - L.derivWeierstrassP z') /
        (L.weierstrassP z - L.weierstrassP z')) ^ 2 - L.weierstrassP z - L.weierstrassP z' := by
  have h := cor_3_9 L z z'
  obtain ⟨h1, e1⟩ := CurveAux.toCurve_of_notMem L hz
  obtain ⟨h2, e2⟩ := CurveAux.toCurve_of_notMem L hz'
  obtain ⟨h3, e3⟩ := CurveAux.toCurve_of_notMem L hzz'
  rw [e3, e1, e2, WeierstrassCurve.Affine.Point.add_of_X_ne hne,
    WeierstrassCurve.Affine.Point.some.injEq] at h
  obtain ⟨hx, -⟩ := h
  rw [hx]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope_of_X_ne hne, curveOf]
  have hne' : L.weierstrassP z - L.weierstrassP z' ≠ 0 := sub_ne_zero.2 hne
  field_simp
  ring

/-- Exercise 3.24 (a) (Milne, pdf p. 108), corrected: the determinant with rows
`(℘(z₁), ℘'(z₁), 1)`, `(℘(z₂), ℘'(z₂), 1)`, `(℘(z₃), ℘'(z₃), 1)` vanishes when
`z₁ + z₂ + z₃ = 0` (and `z₁, z₂, z₃ ∉ Λ`, where the entries are finite): the three points of
`E(Λ)` sum to `0`, so they are collinear.  The book prints the third row as
`(℘(z₁ + z₂), ℘'(z₁ + z₂), 1)`, which is the row of `-z₃` up to the sign of `℘'` (`℘` is even,
`℘'` odd); with that row the determinant is in general nonzero. -/
@[kb "milne2006ec" "Ch. III, Exercise 3.24 (a), pdf p. 108"]
theorem exercise_3_24_a (L : PeriodPair) {z₁ z₂ z₃ : ℂ} (h₁ : z₁ ∉ L.lattice) (h₂ : z₂ ∉ L.lattice)
    (h₃ : z₃ ∉ L.lattice) (hsum : z₁ + z₂ + z₃ = 0) :
    Matrix.det !![L.weierstrassP z₁, L.derivWeierstrassP z₁, 1;
      L.weierstrassP z₂, L.derivWeierstrassP z₂, 1;
      L.weierstrassP z₃, L.derivWeierstrassP z₃, 1] = 0 := by
  have hz3 : z₃ = -(z₁ + z₂) := by linear_combination hsum
  have h12 : z₁ + z₂ ∉ L.lattice := by
    intro h; apply h₃; rw [hz3]; exact L.lattice.neg_mem h
  by_cases hne : L.weierstrassP z₁ = L.weierstrassP z₂
  · rcases CurveAux.wp_eq_cases L h₁ h₂ hne.symm with h | h
    · -- z₂ ≡ z₁: two equal rows
      have hd := CurveAux.dwp_eq_of_sub_mem L ((Submodule.Quotient.eq _).1 h)
      rw [Matrix.det_fin_three]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [← hne, ← hd]; ring
    · exfalso
      apply h₃
      have := (Submodule.Quotient.eq _).1 h
      have h' : z₂ - -z₁ = -z₃ := by rw [hz3]; ring
      rw [h'] at this
      simpa using L.lattice.neg_mem this
  · have h := cor_3_9 L z₁ z₂
    obtain ⟨e1, f1⟩ := CurveAux.toCurve_of_notMem L h₁
    obtain ⟨e2, f2⟩ := CurveAux.toCurve_of_notMem L h₂
    obtain ⟨e3, f3⟩ := CurveAux.toCurve_of_notMem L h12
    rw [f3, f1, f2, WeierstrassCurve.Affine.Point.add_of_X_ne hne,
      WeierstrassCurve.Affine.Point.some.injEq] at h
    obtain ⟨hx, hy⟩ := h
    have hp : L.weierstrassP z₃ = L.weierstrassP (z₁ + z₂) := by rw [hz3, L.weierstrassP_neg]
    have hq : L.derivWeierstrassP z₃ = -L.derivWeierstrassP (z₁ + z₂) := by
      rw [hz3, L.derivWeierstrassP_neg]
    have hne' : L.weierstrassP z₁ - L.weierstrassP z₂ ≠ 0 := sub_ne_zero.2 hne
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope_of_X_ne hne, curveOf] at hx hy
    rw [hp, hq, Matrix.det_fin_three]
    simp
    generalize L.weierstrassP (z₁ + z₂) = X3 at hx ⊢
    generalize L.derivWeierstrassP (z₁ + z₂) = W at hy ⊢
    have hW : W = 2 * (W / 2) := by ring
    rw [hW, hy, hx]
    field_simp
    ring

/-! ### Remark 3.11 (second part) -/

/-- Remark 3.11 (Milne, pdf pp. 102–103), second part: lattices correspond one-to-one to
isomorphism classes of pairs `(E, ω)` of an elliptic curve over `ℂ` and a nonzero holomorphic
differential.  Every pair is isomorphic to `(Y² = 4X³ − aX − b, dx/y)` for a
unique `(a, b)` with `a³ − 27b² ≠ 0`: the changes of variables between curves of this form are
`x = u²x'`, `y = u³y'`, which take `dx/y` to `u⁻¹dx'/y'` and `(a, b)` to `(u⁻⁴a, u⁻⁶b)`, so
preserving the differential forces `u = 1`.  The lattice `Λ` corresponds to `(E(Λ), dx/y)`
(`dx/y = dz`, first part), i.e. to `(a, b) = (g₄(Λ), g₆(Λ))`.  So the content is:
`Λ ↦ (g₄(Λ), g₆(Λ))` is a bijection from lattices onto `{(a, b) | a³ − 27b² ≠ 0}`. -/
@[kb "milne2006ec" "Ch. III, Rem. 3.11, lattices ↔ pairs (E, ω), pdf p. 102"]
theorem remark_3_11 :
    (∀ L : PeriodPair, L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0) ∧
      (∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b) ∧
      ∀ L L' : PeriodPair, L.g₂ = L'.g₂ → L.g₃ = L'.g₃ → L.lattice = L'.lattice :=
  ⟨g₂_cube_sub_g₃_sq_ne_zero, CurveAux.exists_lattice_with_g,
    fun _ _ h2 h3 => CurveAux.lattice_eq_of_g_eq h2 h3⟩

end NumberFieldKB.MilneEC.III
