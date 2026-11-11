import NumberFieldKB.MilneCFT.Ch5Ideles
import NumberFieldKB.HeckeCharacter.Local
import NumberFieldKB.MilneCFT.Ch5RayClassOrder
import QuadFormsKB.Lattices.SAApprox
import Mathlib.Computability.Reduce
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real

/-!
# Characters of idèles and norms of idèles (Milne, *Class Field Theory*, Chapter V, §4, pp. 173–177)

**Proposition 4.7** (`prop_4_7`, `prop_4_7_converse`), **Remark 4.8** (named `Remark4_8`, with `circle_noSmallSubgroups`),
**Remark 4.9** (`remark_4_9`), **Remark 4.11** (`remark_4_11_exists`, named `Remark4_11`), the norm of idèles
(`ideleNormMap`, `ideleNormMap_comm`), **Proposition 4.12** (`prop_4_12a`, named `Prop4_12b`, `prop_4_12c`), and
**Corollary 4.13** (named `Cor4_13`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev Filter Topology
open scoped nonZeroDivisors ValuativeRel RestrictedProduct
open NumberField.InfinitePlace

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-! ## Characters of ideals and of idèles (pp. 173–176) -/

/-! ### Neighbourhoods in the idèle group -/

/-- Every neighbourhood of `1` in a completion contains a ball. -/
theorem exists_valued_le_of_mem_nhds_one (v : HeightOneSpectrum (𝓞 K)) {s : Set (v.adicCompletion K)}
    (hs : s ∈ 𝓝 (1 : v.adicCompletion K)) :
    ∃ n : ℕ, ∀ y, Valued.v (y - 1) ≤ WithZero.exp (-(n : ℤ)) → y ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  set g := MonoidWithZeroHom.ValueGroup₀.embedding γ.1
  have hg : g ≠ 0 := (γ.isUnit.map MonoidWithZeroHom.ValueGroup₀.embedding).ne_zero
  refine ⟨(-(WithZero.log g) + 1).toNat, fun y hy => hγ ?_⟩
  change Valued.v.restrict (y - 1) < γ
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt hy ?_
  have h : WithZero.exp (-(((-(WithZero.log g) + 1).toNat : ℕ) : ℤ)) < WithZero.exp (WithZero.log g) :=
    WithZero.exp_lt_exp.mpr (by omega)
  rwa [WithZero.exp_log hg] at h

/-- Neighbourhoods of `1` in the finite adèle ring. -/
theorem finiteAdele_nhds_one {N : Set (FiniteAdeleRing (𝓞 K) K)} (hN : N ∈ 𝓝 (1 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ), ∀ f : FiniteAdeleRing (𝓞 K) K,
      (∀ v ∈ T, Valued.v (f v - 1) ≤ WithZero.exp (-(n : ℤ))) →
      (∀ v ∉ T, f v ∈ v.adicCompletionIntegers K) → f ∈ N := by
  classical
  have hA : ∀ v : HeightOneSpectrum (𝓞 K), IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => Valued.isOpen_valuationSubring _
  have hN0 : (N : Set (Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K,
      (v.adicCompletionIntegers K : Set (v.adicCompletion K))])) ∈
      𝓝 (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) cofinite (fun _ => 1)) := hN
  rw [RestrictedProduct.nhds_eq_map_structureMap hA] at hN0
  have hN' := Filter.mem_map.mp hN0
  rw [nhds_pi, Filter.mem_pi'] at hN'
  obtain ⟨I, t, ht, hIt⟩ := hN'
  have hn : ∀ v, ∃ n : ℕ, ∀ y : v.adicCompletion K, Valued.v (y - 1) ≤ WithZero.exp (-(n : ℤ)) →
      y ∈ v.adicCompletionIntegers K →
        ∃ h : y ∈ v.adicCompletionIntegers K, (⟨y, h⟩ : v.adicCompletionIntegers K) ∈ t v := by
    intro v
    have := ht v
    rw [nhds_subtype] at this
    obtain ⟨s, hs, hst⟩ := Filter.mem_comap.mp this
    obtain ⟨n, hn⟩ := exists_valued_le_of_mem_nhds_one v hs
    refine ⟨n, fun y hy hyI => ⟨hyI, hst (hn y hy)⟩⟩
  choose n hn using hn
  refine ⟨I, I.sup n + 1, fun f hf1 hf2 => ?_⟩
  have hmem : ∀ v, f v ∈ v.adicCompletionIntegers K := by
    intro v
    by_cases hv : v ∈ I
    · have := hf1 v hv
      have h2 : Valued.v (f v) = 1 := by
        have hlt : WithZero.exp (-((I.sup n + 1 : ℕ) : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
        exact val_eq_one_of_sub_one_le Valued.v hlt this
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact h2.le
    · exact hf2 v hv
  have : f = RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) cofinite (fun v => ⟨f v, hmem v⟩) := rfl
  rw [this]
  refine hIt ?_
  intro v hv
  obtain ⟨_, h⟩ := hn v (f v) (by
    refine (hf1 v hv).trans ?_
    rw [WithZero.exp_le_exp, neg_le_neg_iff]
    have := Finset.le_sup (f := n) hv
    exact_mod_cast (by omega : n v ≤ I.sup n + 1)) (hmem v)
  exact h

/-- Neighbourhoods of `1` in the idèle group contain all idèles that are `1` at the infinite places, close to `1` at
finitely many finite places and units elsewhere. -/
theorem idele_nhds_one {U : Set (IdeleGroup (𝓞 K) K)} (hU : U ∈ 𝓝 (1 : IdeleGroup (𝓞 K) K)) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ), ∀ y : IdeleGroup (𝓞 K) K,
      (∀ w, ideleInfAt y w = 1) → (∀ v ∈ T, Valued.v (ideleFinAt y v - 1) ≤ WithZero.exp (-(n : ℤ))) →
      (∀ v ∉ T, Valued.v (ideleFinAt y v) = 1) → y ∈ U := by
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [show Units.embedProduct (AdeleRing (𝓞 K) K) 1 =
      ((1 : AdeleRing (𝓞 K) K), MulOpposite.op (1 : AdeleRing (𝓞 K) K)) from rfl, nhds_prod_eq] at hV
  obtain ⟨V1, hV1, V2, hV2, hV12⟩ := Filter.mem_prod_iff.mp hV
  have hV2' : MulOpposite.op ⁻¹' V2 ∈ 𝓝 (1 : AdeleRing (𝓞 K) K) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by simpa using hV2)
  have hW := Filter.inter_mem hV1 hV2'
  rw [show (1 : AdeleRing (𝓞 K) K) = ((1 : InfiniteAdeleRing K), (1 : FiniteAdeleRing (𝓞 K) K)) from rfl,
    nhds_prod_eq] at hW
  obtain ⟨N1, hN1, N2, hN2, hN12⟩ := Filter.mem_prod_iff.mp hW
  obtain ⟨T, n, hTn⟩ := finiteAdele_nhds_one hN2
  refine ⟨T, n + 1, fun y hy1 hy2 hy3 => ?_⟩
  have hlt : WithZero.exp (-((n + 1 : ℕ) : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hle : WithZero.exp (-((n + 1 : ℕ) : ℤ)) ≤ (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.exp_le_exp]; omega
  have h1 : (y : AdeleRing (𝓞 K) K).1 = 1 := funext hy1
  have h1' : ((y⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).1 = 1 := funext fun w => by
    have := ideleInfAt_inv y w
    rw [hy1 w, inv_one] at this
    exact this
  have hf : (y : AdeleRing (𝓞 K) K).2 ∈ N2 := by
    refine hTn _ (fun v hv => (hy2 v hv).trans hle) (fun v hv => ?_)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact (hy3 v hv).le
  have hg : ((y⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 ∈ N2 := by
    refine hTn _ (fun v hv => ?_) (fun v hv => ?_)
    · have h := val_inv_sub_one_le Valued.v hlt (hy2 v hv)
      have e := ideleFinAt_inv y v
      change Valued.v (ideleFinAt y⁻¹ v - 1) ≤ _
      rw [e]
      exact h.trans hle
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (ideleFinAt y⁻¹ v) ≤ 1
      rw [ideleFinAt_inv, map_inv₀, hy3 v hv, inv_one]
  apply hVU
  have e1 := hN12 (show ((1 : InfiniteAdeleRing K), (y : AdeleRing (𝓞 K) K).2) ∈ N1 ×ˢ N2 from
    ⟨mem_of_mem_nhds hN1, hf⟩)
  have e2 := hN12 (show ((1 : InfiniteAdeleRing K), ((y⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2) ∈
      N1 ×ˢ N2 from ⟨mem_of_mem_nhds hN1, hg⟩)
  refine hV12 ⟨?_, ?_⟩
  · have : ((1 : InfiniteAdeleRing K), (y : AdeleRing (𝓞 K) K).2) = (y : AdeleRing (𝓞 K) K) := by
      exact Prod.ext h1.symm rfl
    rw [this] at e1
    exact e1.1
  · have : ((1 : InfiniteAdeleRing K), ((y⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2) =
        ((y⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K) := by
      exact Prod.ext h1'.symm rfl
    rw [this] at e2
    exact e2.2

/-! ### $W_\mathfrak m$ is open -/

/-- The set of elements of a completion within `exp (-k)` of `1` is open. -/
theorem isOpen_valued_sub_one_le (v : HeightOneSpectrum (𝓞 K)) (k : ℤ) :
    IsOpen {z : v.adicCompletion K | Valued.v (z - 1) ≤ WithZero.exp (-k)} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  refine Filter.mem_of_superset (QuadFormsKB.Lattices.valued_le_mem_nhds v y k) fun z hz => ?_
  have : z - 1 = (z - y) + (y - 1) := by ring
  show Valued.v (z - 1) ≤ _
  rw [this]
  exact Valuation.map_add_le _ hz hy

/-- The set of finite adèles that are in `1 + p^n` at the primes dividing `m` and integral elsewhere is open. -/
theorem isOpen_finiteAdele_cond (m : Modulus K) :
    IsOpen {f : FiniteAdeleRing (𝓞 K) K |
      (∀ v ∈ m.finiteSupport, Valued.v (f v - 1) ≤ WithZero.exp (-(m.ord v : ℤ))) ∧
      ∀ v ∉ m.finiteSupport, f v ∈ v.adicCompletionIntegers K} := by
  have hA : ∀ v : HeightOneSpectrum (𝓞 K), IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => Valued.isOpen_valuationSubring _
  have hfin : m.finiteSupport.Finite := Ideal.finite_factors m.finite_ne_bot
  show IsOpen ({f : FiniteAdeleRing (𝓞 K) K | ∀ v ∈ m.finiteSupport,
      Valued.v (f v - 1) ≤ WithZero.exp (-(m.ord v : ℤ))} ∩
    {f : FiniteAdeleRing (𝓞 K) K | ∀ v ∉ m.finiteSupport, f v ∈ v.adicCompletionIntegers K})
  refine IsOpen.inter ?_ ?_
  · have : {f : FiniteAdeleRing (𝓞 K) K | ∀ v ∈ m.finiteSupport,
        Valued.v (f v - 1) ≤ WithZero.exp (-(m.ord v : ℤ))} =
        ⋂ v ∈ m.finiteSupport, (fun f : FiniteAdeleRing (𝓞 K) K => f v) ⁻¹'
          {z : v.adicCompletion K | Valued.v (z - 1) ≤ WithZero.exp (-(m.ord v : ℤ))} := by
      ext f; simp
    rw [this]
    refine hfin.isOpen_biInter fun v _ => (isOpen_valued_sub_one_le v _).preimage ?_
    exact RestrictedProduct.continuous_eval v
  · exact RestrictedProduct.isOpen_forall_imp_mem hA (p := fun v => v ∉ m.finiteSupport)

/-- **$W_\mathfrak m$ is open** in the idèle group. -/
theorem isOpen_idelesW (m : Modulus K) : IsOpen (idelesW m : Set (IdeleGroup (𝓞 K) K)) := by
  set U1 : Set (AdeleRing (𝓞 K) K) :=
    {a | (∀ (w : InfinitePlace K) (hw : w ∈ m.infinite),
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (m.isReal_of_mem w hw) (a.1 w)) ∧ a.2 ∈
      {f : FiniteAdeleRing (𝓞 K) K | (∀ v ∈ m.finiteSupport,
        Valued.v (f v - 1) ≤ WithZero.exp (-(m.ord v : ℤ))) ∧
      ∀ v ∉ m.finiteSupport, f v ∈ v.adicCompletionIntegers K}} with hU1
  have hU1o : IsOpen U1 := by
    show IsOpen ({a : AdeleRing (𝓞 K) K | ∀ (w : InfinitePlace K) (hw : w ∈ m.infinite),
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (m.isReal_of_mem w hw) (a.1 w)} ∩
      (Prod.snd ⁻¹' {f : FiniteAdeleRing (𝓞 K) K | (∀ v ∈ m.finiteSupport, Valued.v (f v - 1) ≤
        WithZero.exp (-(m.ord v : ℤ))) ∧ ∀ v ∉ m.finiteSupport, f v ∈ v.adicCompletionIntegers K}))
    refine IsOpen.inter ?_ ((isOpen_finiteAdele_cond m).preimage continuous_snd)
    have : {a : AdeleRing (𝓞 K) K | ∀ (w : InfinitePlace K) (hw : w ∈ m.infinite),
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (m.isReal_of_mem w hw) (a.1 w)} =
        ⋂ (w : InfinitePlace K) (hw : w ∈ m.infinite), {a : AdeleRing (𝓞 K) K |
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (m.isReal_of_mem w hw) (a.1 w)} := by
      ext a; simp
    rw [this]
    refine isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun hw => ?_
    exact isOpen_lt continuous_const
      ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous.comp
        ((continuous_apply w).comp continuous_fst))
  have hone : ∀ x ∈ idelesW m, (x : AdeleRing (𝓞 K) K) ∈ U1 := by
    rintro x ⟨⟨hx1, hx2⟩, hx3⟩
    refine ⟨fun w hw => hx1 w hw, hx2, fun v hv => ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact (hx3 v hv).le
  have : (idelesW m : Set (IdeleGroup (𝓞 K) K)) =
      (fun x : IdeleGroup (𝓞 K) K => (x : AdeleRing (𝓞 K) K)) ⁻¹' U1 ∩
        (fun x : IdeleGroup (𝓞 K) K => ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)) ⁻¹' U1 := by
    ext x
    constructor
    · intro hx
      exact ⟨hone x hx, hone x⁻¹ (inv_mem hx)⟩
    · rintro ⟨⟨h1, h2, h3⟩, ⟨h1', -, h3'⟩⟩
      refine ⟨⟨fun w hw => h1 w hw, h2⟩, fun v hv => ?_⟩
      have ha := h3 v hv
      have hb := h3' v hv
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha hb
      have hm : Valued.v (ideleFinAt x v) * Valued.v (ideleFinAt x⁻¹ v) = 1 := by
        rw [← map_mul, ← ideleFinAt_mul, mul_inv_cancel, ideleFinAt_one, map_one]
      refine le_antisymm ha ?_
      calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (ideleFinAt x v) * Valued.v (ideleFinAt x⁻¹ v) := hm.symm
        _ ≤ Valued.v (ideleFinAt x v) * 1 := by gcongr; exact hb
        _ = Valued.v (ideleFinAt x v) := mul_one _
  rw [this]
  exact (hU1o.preimage Units.continuous_val).inter (hU1o.preimage Units.continuous_coe_inv)

/-! ### The infinite part lies in the identity component (Remark 4.9(a)) -/

theorem ideleFinAt_ofCompletion (w : InfinitePlace K) (u : w.Completionˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ideleFinAt (IdeleGroup.ofCompletion (𝓞 K) K w u) v = 1 := rfl

theorem ideleInfAt_ofCompletion_self (w : InfinitePlace K) (u : w.Completionˣ) :
    ideleInfAt (IdeleGroup.ofCompletion (𝓞 K) K w u) w = (u : w.Completion) := by
  classical
  show (Pi.mulSingle w (u : w.Completion) : InfiniteAdeleRing K) w = _
  simp

theorem ideleInfAt_ofCompletion_ne (w w' : InfinitePlace K) (h : w' ≠ w) (u : w.Completionˣ) :
    ideleInfAt (IdeleGroup.ofCompletion (𝓞 K) K w u) w' = 1 := by
  classical
  show (Pi.mulSingle w (u : w.Completion) : InfiniteAdeleRing K) w' = _
  simp [Pi.mulSingle_eq_of_ne h]

/-- A continuous homomorphism from the units of a real completion to a discrete group is trivial on the
positive elements. -/
theorem real_pos_ker {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G] (w : InfinitePlace K)
    (hw : w.IsReal) (τ : w.Completionˣ →* G) (hτ : Continuous τ) (u : w.Completionˣ)
    (hu : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (u : w.Completion)) : τ u = 1 := by
  set e := InfinitePlace.Completion.isometryEquivRealOfIsReal hw with he
  have hsymm : (e.symm : ℝ → w.Completion) = (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm := rfl
  let ρ : ℝ → w.Completionˣ := fun t =>
    ⟨e.symm (Real.exp t), e.symm (Real.exp (-t)), by
      rw [hsymm, ← map_mul, ← Real.exp_add]; simp, by
      rw [hsymm, ← map_mul, ← Real.exp_add]; simp⟩
  have hρ : Continuous ρ := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact e.symm.continuous.comp Real.continuous_exp
    · exact e.symm.continuous.comp (Real.continuous_exp.comp continuous_neg)
  have hconst : ∀ t, τ (ρ t) = τ (ρ 0) := fun t =>
    (PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℝ) (hτ.comp hρ) (x := t) (y := 0))
  have h0 : ρ 0 = 1 := by
    apply Units.ext
    show e.symm (Real.exp 0) = 1
    rw [Real.exp_zero]
    exact map_one (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
  have hu' : u = ρ (Real.log (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (u : w.Completion))) := by
    apply Units.ext
    show (u : w.Completion) = e.symm (Real.exp _)
    rw [Real.exp_log hu]
    exact ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm_apply_apply _).symm
  rw [hu', hconst, h0, map_one]

/-- A continuous homomorphism from the units of a complex completion to a discrete group is trivial. -/
theorem complex_ker {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G] (w : InfinitePlace K)
    (hw : w.IsComplex) (τ : w.Completionˣ →* G) (hτ : Continuous τ) (u : w.Completionˣ) : τ u = 1 := by
  set e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw with he
  have hsymm : (e.symm : ℂ → w.Completion) = (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm := rfl
  let ρ : ℂ → w.Completionˣ := fun t =>
    ⟨e.symm (Complex.exp t), e.symm (Complex.exp (-t)), by
      rw [hsymm, ← map_mul, ← Complex.exp_add]; simp, by
      rw [hsymm, ← map_mul, ← Complex.exp_add]; simp⟩
  have hρ : Continuous ρ := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact e.symm.continuous.comp Complex.continuous_exp
    · exact e.symm.continuous.comp (Complex.continuous_exp.comp continuous_neg)
  have hconst : ∀ t, τ (ρ t) = τ (ρ 0) := fun t =>
    (PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) (hτ.comp hρ) (x := t) (y := 0))
  have h0 : ρ 0 = 1 := by
    apply Units.ext
    show e.symm (Complex.exp 0) = 1
    rw [Complex.exp_zero, hsymm]
    exact map_one _
  have hne : InfinitePlace.Completion.ringEquivComplexOfIsComplex hw (u : w.Completion) ≠ 0 :=
    (map_ne_zero _).mpr u.ne_zero
  have hu' : u = ρ (Complex.log (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw (u : w.Completion))) := by
    apply Units.ext
    show (u : w.Completion) = e.symm (Complex.exp _)
    rw [Complex.exp_log hne]
    exact ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm_apply_apply _).symm
  rw [hu', hconst, h0, map_one]

/-- **Remark 4.9(a)**: a continuous homomorphism from the idèles to a discrete group is trivial on the idèles that are `1`
at every finite place and positive at every real place. -/
theorem infinite_part_ker {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (φ : IdeleGroup (𝓞 K) K →* G) (hφ : Continuous φ) (x : IdeleGroup (𝓞 K) K)
    (hx1 : ∀ v, ideleFinAt x v = 1)
    (hx2 : ∀ (w : InfinitePlace K) (hw : w.IsReal), IsPosAt w hw (ideleInfAt x w)) : φ x = 1 := by
  classical
  have key : ∀ (F : Finset (InfinitePlace K)) (x : IdeleGroup (𝓞 K) K), (∀ v, ideleFinAt x v = 1) →
      (∀ (w : InfinitePlace K) (hw : w.IsReal), IsPosAt w hw (ideleInfAt x w)) →
      (∀ w ∉ F, ideleInfAt x w = 1) → φ x = 1 := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro x h1 _ h3
      have : x = 1 := by
        apply Units.ext
        refine Prod.ext (funext fun w => h3 w (by simp)) ?_
        refine FiniteAdeleRing.ext _ fun v => h1 v
      rw [this, map_one]
    | insert a F haF ih =>
      intro x h1 h2 h3
      set u : (a.Completion)ˣ := ⟨ideleInfAt x a, ideleInfAt x⁻¹ a, by
        rw [← ideleInfAt_mul, mul_inv_cancel, ideleInfAt_one], by
        rw [← ideleInfAt_mul, inv_mul_cancel, ideleInfAt_one]⟩ with hu
      set y := IdeleGroup.ofCompletion (𝓞 K) K a u with hy
      have hφy : φ y = 1 := by
        have hτ : Continuous (φ.comp (IdeleGroup.ofCompletion (𝓞 K) K a)) :=
          hφ.comp (NumberFieldKB.Ideles.IdeleGroup.continuous_ofCompletion a)
        by_cases ha : a.IsReal
        · exact real_pos_ker a ha _ hτ u (h2 a ha)
        · exact complex_ker a (not_isReal_iff_isComplex.mp ha) _ hτ u
      have hx' : φ (x * y⁻¹) = 1 := by
        refine ih (x * y⁻¹) (fun v => ?_) (fun w hw => ?_) (fun w hw => ?_)
        · rw [ideleFinAt_mul, ideleFinAt_inv, hy, ideleFinAt_ofCompletion, h1 v]; simp
        · by_cases hwa : w = a
          · subst hwa
            rw [ideleInfAt_mul, ideleInfAt_inv, hy, ideleInfAt_ofCompletion_self]
            have : ideleInfAt x w * ((u : w.Completion))⁻¹ = 1 := mul_inv_cancel₀ u.ne_zero
            rw [this]
            unfold IsPosAt; simp
          · rw [ideleInfAt_mul, ideleInfAt_inv, hy, ideleInfAt_ofCompletion_ne a w hwa, inv_one, mul_one]
            exact h2 w hw
        · by_cases hwa : w = a
          · subst hwa
            rw [ideleInfAt_mul, ideleInfAt_inv, hy, ideleInfAt_ofCompletion_self]
            exact mul_inv_cancel₀ u.ne_zero
          · rw [ideleInfAt_mul, ideleInfAt_inv, hy, ideleInfAt_ofCompletion_ne a w hwa, inv_one, mul_one]
            exact h3 w (by simp [hwa, hw])
      calc φ x = φ (x * y⁻¹) * φ y := by rw [← map_mul, inv_mul_cancel_right]
        _ = 1 := by rw [hx', hφy, mul_one]
  exact key Finset.univ x hx1 hx2 (by simp)

/-! ### Splitting an idèle into its infinite part and local parts -/

/-- The infinite part of an idèle: $x_w$ at the infinite places and $1$ at the finite ones. -/
def infPart (x : IdeleGroup (𝓞 K) K) : IdeleGroup (𝓞 K) K where
  val := ((x : AdeleRing (𝓞 K) K).1, 1)
  inv := (((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).1, 1)
  val_inv := Prod.ext
    (show (x : AdeleRing (𝓞 K) K).1 * ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).1 = 1 from
      congrArg Prod.fst x.mul_inv)
    (show (1 : FiniteAdeleRing (𝓞 K) K) * 1 = 1 from mul_one _)
  inv_val := Prod.ext
    (show ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).1 * (x : AdeleRing (𝓞 K) K).1 = 1 from
      congrArg Prod.fst x.inv_mul)
    (show (1 : FiniteAdeleRing (𝓞 K) K) * 1 = 1 from mul_one _)

theorem ideleInfAt_infPart (x : IdeleGroup (𝓞 K) K) (w : InfinitePlace K) :
    ideleInfAt (infPart x) w = ideleInfAt x w := rfl

theorem ideleFinAt_infPart (x : IdeleGroup (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    ideleFinAt (infPart x) v = 1 := rfl

open scoped Classical in
/-- Restricting a finite adèle to a finite set of primes (and putting $1$ elsewhere). -/
def finRestrict (a : FiniteAdeleRing (𝓞 K) K) (P : Finset (HeightOneSpectrum (𝓞 K))) :
    FiniteAdeleRing (𝓞 K) K :=
  ⟨fun v => if v ∈ P then a v else 1, by
    filter_upwards [P.finite_toSet.eventually_cofinite_notMem] with v hv
    have : v ∉ P := by simpa using hv
    simp only [this, ite_false]
    exact one_mem _⟩

open scoped Classical in
theorem finRestrict_apply (a : FiniteAdeleRing (𝓞 K) K) (P : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) : finRestrict a P v = if v ∈ P then a v else 1 := rfl

open scoped Classical in
theorem finRestrict_mul (a b : FiniteAdeleRing (𝓞 K) K) (P : Finset (HeightOneSpectrum (𝓞 K))) :
    finRestrict a P * finRestrict b P = finRestrict (a * b) P := by
  refine FiniteAdeleRing.ext _ fun v => ?_
  change finRestrict a P v * finRestrict b P v = finRestrict (a * b) P v
  simp only [finRestrict_apply]
  split_ifs <;> first | rfl | simp

open scoped Classical in
theorem finRestrict_one (P : Finset (HeightOneSpectrum (𝓞 K))) :
    finRestrict (1 : FiniteAdeleRing (𝓞 K) K) P = 1 := by
  refine FiniteAdeleRing.ext _ fun v => ?_
  change finRestrict 1 P v = 1
  simp only [finRestrict_apply]
  split_ifs <;> rfl

/-- The local part of an idèle at a finite set $P$ of finite primes: $x_v$ for $v \in P$ and $1$ elsewhere (including
the infinite places). -/
def localPart (x : IdeleGroup (𝓞 K) K) (P : Finset (HeightOneSpectrum (𝓞 K))) : IdeleGroup (𝓞 K) K where
  val := (1, finRestrict (x : AdeleRing (𝓞 K) K).2 P)
  inv := (1, finRestrict ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 P)
  val_inv := Prod.ext (show (1 : InfiniteAdeleRing K) * 1 = 1 from mul_one _) (by
    show finRestrict (x : AdeleRing (𝓞 K) K).2 P *
      finRestrict ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 P = 1
    have h : (x : AdeleRing (𝓞 K) K).2 * ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 = 1 :=
      congrArg Prod.snd x.mul_inv
    rw [finRestrict_mul, h, finRestrict_one])
  inv_val := Prod.ext (show (1 : InfiniteAdeleRing K) * 1 = 1 from mul_one _) (by
    show finRestrict ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 P *
      finRestrict (x : AdeleRing (𝓞 K) K).2 P = 1
    have h : ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K).2 * (x : AdeleRing (𝓞 K) K).2 = 1 :=
      congrArg Prod.snd x.inv_mul
    rw [finRestrict_mul, h, finRestrict_one])

theorem ideleInfAt_localPart (x : IdeleGroup (𝓞 K) K) (P : Finset (HeightOneSpectrum (𝓞 K)))
    (w : InfinitePlace K) : ideleInfAt (localPart x P) w = 1 := rfl

open scoped Classical in
theorem ideleFinAt_localPart (x : IdeleGroup (𝓞 K) K) (P : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) :
    ideleFinAt (localPart x P) v = if v ∈ P then ideleFinAt x v else 1 := rfl

/-! ### Basic facts on ideals of idèles -/

theorem ideleToIdeal_mem_sIdeals_iff (S : Set (HeightOneSpectrum (𝓞 K))) (x : IdeleGroup (𝓞 K) K) :
    ideleToIdeal K x ∈ sIdeals S ↔ ∀ v ∈ S, Valued.v (ideleFinAt x v) = 1 := by
  refine forall_congr' fun v => forall_congr' fun hv => ?_
  have h2 := QuadFormsKB.Tamagawa.Measure.Weil.count_ideleIdeal
    (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K →+*
      FiniteAdeleRing (𝓞 K) K).toMonoidHom x) v
  have h3 := (QuadFormsKB.Tamagawa.Measure.Weil.ordAt_eq_zero_iff
    (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K →+*
      FiniteAdeleRing (𝓞 K) K).toMonoidHom x) v)
  have h2' : FractionalIdeal.count K v ((ideleToIdeal K x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = QuadFormsKB.Tamagawa.Measure.Weil.ordAt
      (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K →+*
      FiniteAdeleRing (𝓞 K) K).toMonoidHom x) v := h2
  show FractionalIdeal.count K v ((ideleToIdeal K x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = 0 ↔ _
  rw [h2']
  exact h3

/-- A homomorphism from the idèles to a discrete group with open kernel is continuous. -/
theorem continuous_of_isOpen_ker {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (φ : IdeleGroup (𝓞 K) K →* G) (h : IsOpen (φ.ker : Set (IdeleGroup (𝓞 K) K))) : Continuous φ := by
  rw [continuous_discrete_rng]
  intro b
  by_cases hb : ∃ x0, φ x0 = b
  · obtain ⟨x0, rfl⟩ := hb
    have : φ ⁻¹' {φ x0} = (fun y => x0⁻¹ * y) ⁻¹' (φ.ker : Set (IdeleGroup (𝓞 K) K)) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
      constructor
      · intro hy; rw [hy, inv_mul_cancel]
      · intro hy; exact (inv_mul_eq_one.mp hy).symm
    rw [this]
    exact h.preimage (continuous_const.mul continuous_id)
  · push Not at hb
    have : φ ⁻¹' {b} = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact hb y
    rw [this]
    exact isOpen_empty

/-- **Remark 4.9(c)/(d), the core**: a continuous homomorphism to a discrete group is trivial on the idèles that are
positive at the real places, close to $1$ at finitely many finite places, and units elsewhere. -/
theorem ker_contains {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (φ : IdeleGroup (𝓞 K) K →* G) (hφ : Continuous φ) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ), ∀ x : IdeleGroup (𝓞 K) K,
      (∀ (w : InfinitePlace K) (hw : w.IsReal), IsPosAt w hw (ideleInfAt x w)) →
      (∀ v ∈ T, Valued.v (ideleFinAt x v - 1) ≤ WithZero.exp (-(n : ℤ))) →
      (∀ v ∉ T, Valued.v (ideleFinAt x v) = 1) → φ x = 1 := by
  have hopen : IsOpen (φ.ker : Set (IdeleGroup (𝓞 K) K)) := by
    have : (φ.ker : Set (IdeleGroup (𝓞 K) K)) = φ ⁻¹' {1} := by
      ext y; simp
    rw [this]
    exact (isOpen_discrete _).preimage hφ
  obtain ⟨T, n, hTn⟩ := idele_nhds_one (hopen.mem_nhds (one_mem φ.ker))
  refine ⟨T, n, fun x h1 h2 h3 => ?_⟩
  have hy : x * (infPart x)⁻¹ ∈ φ.ker := by
    refine hTn _ (fun w => ?_) (fun v hv => ?_) (fun v hv => ?_)
    · rw [ideleInfAt_mul, ideleInfAt_inv, ideleInfAt_infPart]
      exact mul_inv_cancel₀ (ideleInfAt_ne_zero x w)
    · rw [ideleFinAt_mul, ideleFinAt_inv, ideleFinAt_infPart, inv_one, mul_one]
      exact h2 v hv
    · rw [ideleFinAt_mul, ideleFinAt_inv, ideleFinAt_infPart, inv_one, mul_one]
      exact h3 v hv
  have hinf : φ (infPart x) = 1 :=
    infinite_part_ker φ hφ _ (fun v => ideleFinAt_infPart x v) (fun w hw => h1 w hw)
  rw [MonoidHom.mem_ker, map_mul, map_inv, hinf, inv_one, mul_one] at hy
  exact hy

/-- A version of `ker_contains` that may be applied to any larger finite set and any larger exponent. -/
theorem ker_contains' {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (φ : IdeleGroup (𝓞 K) K →* G) (hφ : Continuous φ) :
    ∃ (T₀ : Finset (HeightOneSpectrum (𝓞 K))) (n₀ : ℕ), ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), T₀ ⊆ T →
      ∀ n : ℕ, n₀ ≤ n → 1 ≤ n → ∀ x : IdeleGroup (𝓞 K) K,
      (∀ (w : InfinitePlace K) (hw : w.IsReal), IsPosAt w hw (ideleInfAt x w)) →
      (∀ v ∈ T, Valued.v (ideleFinAt x v - 1) ≤ WithZero.exp (-(n : ℤ))) →
      (∀ v ∉ T, Valued.v (ideleFinAt x v) = 1) → φ x = 1 := by
  obtain ⟨T₀, n₀, h⟩ := ker_contains φ hφ
  refine ⟨T₀, n₀, fun T hT n hn hn1 x h1 h2 h3 => h x h1 (fun v hv => ?_) (fun v hv => ?_)⟩
  · refine (h2 v (hT hv)).trans ?_
    rw [WithZero.exp_le_exp]; omega
  · by_cases hvT : v ∈ T
    · refine val_eq_one_of_sub_one_le Valued.v (γ := WithZero.exp (-(n : ℤ))) ?_ (h2 v hvT)
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    · exact h3 v hvT

/-- A modulus with all real places and prescribed finite support and exponents. -/
theorem exists_modulus (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : Modulus K, m.infinite = {w | w.IsReal} ∧ m.finiteSupport = ↑T ∧ ∀ v ∈ T, n ≤ m.ord v := by
  classical
  have hne : ∏ v ∈ T, v.asIdeal ^ n ≠ ⊥ := by
    rw [Ideal.zero_eq_bot.symm]
    exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ v.ne_bot
  refine ⟨⟨∏ v ∈ T, v.asIdeal ^ n, hne, {w | w.IsReal}, fun _ h => h⟩, rfl, ?_, ?_⟩
  · ext v
    show v.asIdeal ∣ ∏ v ∈ T, v.asIdeal ^ n ↔ v ∈ T
    constructor
    · intro h
      obtain ⟨w, hw, h2⟩ := (v.prime.dvd_finsetProd_iff _).1 h
      have h3 := v.prime.dvd_of_dvd_pow h2
      have : v = w :=
        HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.1 h3)).symm
      exact this ▸ hw
    · intro h
      exact (dvd_pow_self _ (by omega)).trans (Finset.dvd_prod_of_mem _ h)
  · intro v hv
    show n ≤ (Associates.mk v.asIdeal).count (Associates.mk (∏ v ∈ T, v.asIdeal ^ n)).factors
    rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hne) v.associates_irreducible,
      ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
    exact Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal ^ n) hv

/-- $I_S$ for a finite set $S$ of finite primes (Milne, *CFT*, V, Proposition 4.7(c), with $S \supseteq S_\infty$): the
idèles with $a_v = 1$ for every $v \in S$ and every infinite $v$. -/
@[kb "milne2020cft" "Ch. V, Proposition 4.7 (the group I_S)"]
def idelesTrivialAt (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup (𝓞 K) K) where
  carrier := {x | (∀ w : InfinitePlace K, ideleInfAt x w = 1) ∧ ∀ v ∈ S, ideleFinAt x v = 1}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun w => ?_, fun v hv => ?_⟩
    · rw [ideleInfAt_mul, hx1 w, hy1 w, one_mul]
    · rw [ideleFinAt_mul, hx2 v hv, hy2 v hv, one_mul]
  one_mem' := ⟨fun w => ideleInfAt_one w, fun v _ => ideleFinAt_one v⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨fun w => ?_, fun v hv => ?_⟩
    · rw [ideleInfAt_inv, hx1 w, inv_one]
    · rw [ideleFinAt_inv, hx2 v hv, inv_one]

/-- Removing the infinite part and the local part at `T` from an idèle leaves an idèle in $I_S$ for $S \subseteq T$. -/
theorem splitTriv_mem (y : IdeleGroup (𝓞 K) K) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (S : Set (HeightOneSpectrum (𝓞 K))) (hST : S ⊆ ↑T) :
    y * (infPart y * localPart y T)⁻¹ ∈ idelesTrivialAt S := by
  classical
  refine ⟨fun w => ?_, fun v hv => ?_⟩
  · rw [ideleInfAt_mul, ideleInfAt_inv, ideleInfAt_mul, ideleInfAt_infPart, ideleInfAt_localPart, mul_one]
    exact mul_inv_cancel₀ (ideleInfAt_ne_zero y w)
  · have hvT : v ∈ T := hST hv
    rw [ideleFinAt_mul, ideleFinAt_inv, ideleFinAt_mul, ideleFinAt_infPart, ideleFinAt_localPart, if_pos hvT,
      one_mul]
    exact mul_inv_cancel₀ (ideleFinAt_ne_zero y v)

/-- **Proposition 4.7, existence.** -/
theorem prop_4_7_exists {G : Type} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (ψ : sIdeals S →* G)
    (hψ : AdmitsModulus S Set.univ ψ) :
    ∃ φ : IdeleGroup (𝓞 K) K →* G, Continuous φ ∧
      (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) ∧
      ∀ x ∈ idelesTrivialAt S, ∀ b : sIdeals S, (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
        φ x = ψ b := by
  obtain ⟨m, hmS, -, ψ', hψ'⟩ := (admitsModulus_iff_factors S hS Set.univ ψ).1 hψ
  set Φ : idelesMod m →* G := ψ'.comp (idelesModToRay m) with hΦ
  set π : idelesMod m →* IdeleClassGroup (𝓞 K) K :=
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)).comp (idelesMod m).subtype with hπ
  obtain ⟨hsurj, hker⟩ := prop_4_6b m
  have hπs : Function.Surjective π := hsurj
  have hle : π.ker ≤ Φ.ker := by
    intro x hx
    have hx' : ((x : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K) = 1 := hx
    obtain ⟨a, ha, hax⟩ := (hker x).1 hx'
    rw [MonoidHom.mem_ker, hΦ, MonoidHom.comp_apply]
    have : idelesModToRay m x = 1 := by
      show (QuotientGroup.mk _ : RayClassGroup m) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      refine ⟨a, ha, ?_⟩
      show toPrincipalIdeal (𝓞 K) K a = ideleToIdeal K (x : IdeleGroup (𝓞 K) K)
      rw [← hax, ideleToIdeal_unitEmbedding]
    rw [this, map_one]
  set Φ' : IdeleClassGroup (𝓞 K) K →* G :=
    π.liftOfRightInverse (Function.surjInv hπs) (Function.rightInverse_surjInv hπs) ⟨Φ, hle⟩ with hΦ'
  have hΦ'π : ∀ x : idelesMod m, Φ' (π x) = Φ x := fun x =>
    π.liftOfRightInverse_comp_apply (Function.surjInv hπs) (Function.rightInverse_surjInv hπs) ⟨Φ, hle⟩ x
  set φ : IdeleGroup (𝓞 K) K →* G := Φ'.comp (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) with hφ
  have hφx : ∀ y : idelesMod m, φ y = Φ y := fun y => hΦ'π y
  refine ⟨φ, ?_, ?_, ?_⟩
  · refine continuous_of_isOpen_ker φ ?_
    have hW : idelesW m ≤ φ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker, show φ x = φ ((⟨x, hx.1⟩ : idelesMod m) : IdeleGroup (𝓞 K) K) from rfl, hφx]
      have h1 : ideleToIdeal K x = 1 := by
        refine (item_4_1.2 x).2 fun v => ?_
        by_cases hv : v ∈ m.finiteSupport
        · exact val_eq_one_of_sub_one_le Valued.v (exp_neg_ord_lt_one m v hv) (hx.1.2 v hv)
        · exact hx.2 v hv
      have : idelesModToRay m ⟨x, hx.1⟩ = 1 := by
        show (QuotientGroup.mk _ : RayClassGroup m) = 1
        rw [← QuotientGroup.mk_one]
        congr 1
        exact Subtype.ext h1
      rw [hΦ, MonoidHom.comp_apply, this, map_one]
    exact Subgroup.isOpen_of_mem_nhds _
      (Filter.mem_of_superset ((isOpen_idelesW m).mem_nhds (one_mem _)) hW)
  · intro a
    show Φ' (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 K) K a)) = 1
    rw [(QuotientGroup.eq_one_iff _).2 (MonoidHom.mem_range.2 ⟨a, rfl⟩), map_one]
  · intro x hx b hb
    have hx' : x ∈ idelesMod m := by
      refine ⟨fun w hw => ?_, fun v hv => ?_⟩
      · rw [hx.1 w]; unfold IsPosAt; simp
      · rw [hx.2 v (hmS hv), sub_self, map_zero]; exact zero_le'
    have : idelesModToRay m ⟨x, hx'⟩ = sIdealsToRay m S hmS b := by
      show (QuotientGroup.mk _ : RayClassGroup m) = QuotientGroup.mk _
      congr 1
      exact Subtype.ext hb.symm
    rw [hψ']
    show φ x = ψ' (sIdealsToRay m S hmS b)
    rw [← this]
    exact hφx ⟨x, hx'⟩

/-- **Proposition 4.7, uniqueness.** -/
theorem prop_4_7_unique {G : Type} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (ψ : sIdeals S →* G)
    (φ φ' : IdeleGroup (𝓞 K) K →* G) (hφ : Continuous φ) (hφ' : Continuous φ')
    (hK : ∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1)
    (hK' : ∀ a : Kˣ, φ' (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1)
    (hc : ∀ x ∈ idelesTrivialAt S, ∀ b : sIdeals S, (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
      φ x = ψ b)
    (hc' : ∀ x ∈ idelesTrivialAt S, ∀ b : sIdeals S, (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
      φ' x = ψ b) : φ = φ' := by
  classical
  obtain ⟨T₀, n₀, h₀⟩ := ker_contains' φ hφ
  obtain ⟨T₁, n₁, h₁⟩ := ker_contains' φ' hφ'
  set T : Finset (HeightOneSpectrum (𝓞 K)) := hS.toFinset ∪ T₀ ∪ T₁ with hT
  set n : ℕ := n₀ + n₁ + 1 with hn
  obtain ⟨m, hminf, hmS, hmord⟩ := exists_modulus T n (by omega)
  obtain ⟨hsurj, -⟩ := prop_4_6b m
  have hST : S ⊆ ↑T := fun v hv => by simp [hT, hv]
  have key : ∀ y : idelesMod m, φ y = φ' y := by
    intro y
    obtain ⟨w, hw⟩ : ∃ w : IdeleGroup (𝓞 K) K,
        w = infPart (y : IdeleGroup (𝓞 K) K) * localPart (y : IdeleGroup (𝓞 K) K) T := ⟨_, rfl⟩
    have hmem : (y : IdeleGroup (𝓞 K) K) * w⁻¹ ∈ idelesTrivialAt S := by
      rw [hw]; exact splitTriv_mem _ T S hST
    have hI : ideleToIdeal K ((y : IdeleGroup (𝓞 K) K) * w⁻¹) ∈ sIdeals S :=
      (ideleToIdeal_mem_sIdeals_iff S _).2 fun v hv => by rw [hmem.2 v hv]; exact map_one _
    have hpos : ∀ (w' : InfinitePlace K) (hw' : w'.IsReal), IsPosAt w' hw' (ideleInfAt w w') := by
      intro w' hw'
      rw [hw, ideleInfAt_mul, ideleInfAt_infPart, ideleInfAt_localPart, mul_one]
      exact y.2.1 w' (by rw [hminf]; exact hw')
    have hv1 : ∀ v ∈ T, Valued.v (ideleFinAt w v - 1) ≤ WithZero.exp (-(n : ℤ)) := by
      intro v hv
      rw [hw, ideleFinAt_mul, ideleFinAt_infPart, ideleFinAt_localPart, if_pos hv, one_mul]
      refine (y.2.2 v (by rw [hmS]; exact hv)).trans ?_
      rw [WithZero.exp_le_exp]
      have := hmord v hv
      omega
    have hv2 : ∀ v ∉ T, Valued.v (ideleFinAt w v) = 1 := by
      intro v hv
      rw [hw, ideleFinAt_mul, ideleFinAt_infPart, ideleFinAt_localPart, if_neg hv, one_mul, map_one]
    have e0 : φ w = 1 :=
      h₀ T (by intro v hv; simp [hT, hv]) n (by omega) (by omega) w hpos hv1 hv2
    have e1 : φ' w = 1 :=
      h₁ T (by intro v hv; simp [hT, hv]) n (by omega) (by omega) w hpos hv1 hv2
    have hy : (y : IdeleGroup (𝓞 K) K) = ((y : IdeleGroup (𝓞 K) K) * w⁻¹) * w := by
      rw [inv_mul_cancel_right]
    calc φ y = φ ((y : IdeleGroup (𝓞 K) K) * w⁻¹) * φ w := by rw [← map_mul, ← hy]
      _ = ψ ⟨_, hI⟩ := by rw [e0, mul_one]; exact hc _ hmem ⟨_, hI⟩ rfl
      _ = φ' ((y : IdeleGroup (𝓞 K) K) * w⁻¹) * φ' w := by rw [e1, mul_one]; exact (hc' _ hmem ⟨_, hI⟩ rfl).symm
      _ = φ' y := by rw [← map_mul, ← hy]
  ext x
  obtain ⟨y, hy⟩ := hsurj (x : IdeleClassGroup (𝓞 K) K)
  have hy' : ((y : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K) = (x : IdeleClassGroup (𝓞 K) K) := hy
  rw [QuotientGroup.eq] at hy'
  obtain ⟨a, ha⟩ := hy'
  have hx : x = (y : IdeleGroup (𝓞 K) K) * IdeleGroup.unitEmbedding (𝓞 K) K a := by
    rw [ha]; group
  rw [hx, map_mul, map_mul, hK a, hK' a, mul_one, mul_one]
  exact key y

/-- The ideal of $x \cdot (\text{infinite part} \cdot \text{local part at } T)^{-1}$ is that of $x$ when $x$ is a unit at
the primes of $T$. -/
theorem ideleToIdeal_splitTriv (x : IdeleGroup (𝓞 K) K) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hx : ∀ v ∈ T, Valued.v (ideleFinAt x v) = 1) :
    ideleToIdeal K (x * (infPart x * localPart x T)⁻¹) = ideleToIdeal K x := by
  classical
  have : ideleToIdeal K (infPart x * localPart x T) = 1 := by
    refine (item_4_1.2 _).2 fun v => ?_
    rw [ideleFinAt_mul, ideleFinAt_infPart, ideleFinAt_localPart, one_mul]
    by_cases hv : v ∈ T
    · rw [if_pos hv]; exact hx v hv
    · rw [if_neg hv, map_one]
  rw [map_mul, map_inv, this, inv_one, mul_one]

/-- The ideal of $\mathrm{id} : I_S \to I^S$ as a homomorphism. -/
def idealOfTrivialAt (S : Set (HeightOneSpectrum (𝓞 K))) : idelesTrivialAt S →* sIdeals S :=
  MonoidHom.codRestrict ((ideleToIdeal K).comp (idelesTrivialAt S).subtype) (sIdeals S) (fun x =>
    (ideleToIdeal_mem_sIdeals_iff S x).2 fun v hv => by rw [x.2.2 v hv, map_one])

theorem idealOfTrivialAt_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : idelesTrivialAt S) :
    ((idealOfTrivialAt S x : sIdeals S) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x := rfl

/-- **Proposition 4.7** (Milne, *CFT*, V, p. 174): let $S$ be a finite set of primes ($S_\infty$ added) and $G$ a finite
abelian group. If $\psi : I^S \to G$ admits a modulus, there is a unique homomorphism $\varphi : I_K \to G$ such that
(a) $\varphi$ is continuous ($G$ discrete), (b) $\varphi(K^\times) = 1$, (c) $\varphi(a) = \psi(\mathrm{id}(a))$ for
$a \in I_S$. -/
@[kb "milne2020cft" "Ch. V, Proposition 4.7"]
theorem prop_4_7 {G : Type} [CommGroup G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (ψ : sIdeals S →* G)
    (hψ : AdmitsModulus S Set.univ ψ) :
    ∃! φ : IdeleGroup (𝓞 K) K →* G, Continuous φ ∧
      (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) ∧
      ∀ x ∈ idelesTrivialAt S, ∀ b : sIdeals S, (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
        φ x = ψ b := by
  obtain ⟨φ, h1, h2, h3⟩ := prop_4_7_exists S hS ψ hψ
  refine ⟨φ, ⟨h1, h2, h3⟩, fun φ' ⟨h1', h2', h3'⟩ => ?_⟩
  exact (prop_4_7_unique S hS ψ φ φ' h1 h1' h2 h2' h3 h3').symm

/-- **Proposition 4.7**, the converse (Milne, *CFT*, V, p. 174): every continuous homomorphism $\varphi : I_K \to G$
($G$ finite abelian, discrete) trivial on $K^\times$ arises from some $\psi : I^S \to G$ admitting a modulus. -/
@[kb "milne2020cft" "Ch. V, Proposition 4.7 (converse)"]
theorem prop_4_7_converse {G : Type} [CommGroup G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
    (φ : IdeleGroup (𝓞 K) K →* G) (hφ : Continuous φ)
    (hK : ∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 K))) (_ : S.Finite) (ψ : sIdeals S →* G), AdmitsModulus S Set.univ ψ ∧
      ∀ x ∈ idelesTrivialAt S, ∀ b : sIdeals S, (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
        φ x = ψ b := by
  classical
  obtain ⟨T, n₀, h⟩ := ker_contains φ hφ
  set S : Set (HeightOneSpectrum (𝓞 K)) := ↑T with hSdef
  have hf : Function.Surjective (idealOfTrivialAt S) := by
    intro b
    obtain ⟨x0, hx0⟩ := item_4_1.1 (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    have hx0S : ∀ v ∈ T, Valued.v (ideleFinAt x0 v) = 1 := by
      intro v hv
      have hb := b.2
      rw [← hx0, ideleToIdeal_mem_sIdeals_iff] at hb
      exact hb v hv
    have hmem : x0 * (infPart x0 * localPart x0 T)⁻¹ ∈ idelesTrivialAt S := splitTriv_mem x0 T S le_rfl
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    rw [idealOfTrivialAt_apply]
    show ideleToIdeal K (x0 * (infPart x0 * localPart x0 T)⁻¹) = _
    rw [ideleToIdeal_splitTriv x0 T hx0S, hx0]
  have hker : (idealOfTrivialAt S).ker ≤ (φ.comp (idelesTrivialAt S).subtype).ker := by
    intro x hx
    have hx1 : ideleToIdeal K (x : IdeleGroup (𝓞 K) K) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      exact this
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    have hu := (item_4_1.2 _).1 hx1
    refine h x ?_ ?_ ?_
    · intro w hw
      show 0 < _
      rw [x.2.1 w]; simp
    · intro v hv
      rw [x.2.2 v hv, sub_self, map_zero]; exact zero_le
    · intro v _; exact hu v
  set ψ : sIdeals S →* G := (idealOfTrivialAt S).liftOfRightInverse (Function.surjInv hf)
    (Function.rightInverse_surjInv hf) ⟨φ.comp (idelesTrivialAt S).subtype, hker⟩ with hψ
  have hψx : ∀ x : idelesTrivialAt S, ψ (idealOfTrivialAt S x) = φ x := fun x =>
    (idealOfTrivialAt S).liftOfRightInverse_comp_apply (Function.surjInv hf) (Function.rightInverse_surjInv hf)
      ⟨φ.comp (idelesTrivialAt S).subtype, hker⟩ x
  refine ⟨S, T.finite_toSet, ψ, ?_, ?_⟩
  · obtain ⟨m, hminf, hmS, hmord⟩ := exists_modulus T (n₀ + 1) (by omega)
    refine ⟨m, hmS.le, Set.subset_univ _, fun a ha haS => ?_⟩
    set a' := IdeleGroup.unitEmbedding (𝓞 K) K a with ha'
    have ham : a' ∈ idelesMod m := (mem_congruenceSubgroup_iff_mem_idelesMod m a).1 ha
    have hunit : ∀ v ∈ T, Valued.v (ideleFinAt a' v) = 1 := by
      intro v hv
      refine val_eq_one_of_sub_one_le Valued.v (exp_neg_ord_lt_one m v (by rw [hmS]; exact hv)) ?_
      exact ham.2 v (by rw [hmS]; exact hv)
    have hmem : a' * (infPart a' * localPart a' T)⁻¹ ∈ idelesTrivialAt S := splitTriv_mem a' T S le_rfl
    have hb : (⟨toPrincipalIdeal (𝓞 K) K a, haS⟩ : sIdeals S) = idealOfTrivialAt S ⟨_, hmem⟩ := by
      refine Subtype.ext ?_
      rw [idealOfTrivialAt_apply]
      show toPrincipalIdeal (𝓞 K) K a = ideleToIdeal K (a' * (infPart a' * localPart a' T)⁻¹)
      rw [ideleToIdeal_splitTriv a' T hunit, ha', ideleToIdeal_unitEmbedding]
    have hw : φ (infPart a' * localPart a' T) = 1 := by
      refine h _ (fun w' hw' => ?_) (fun v hv => ?_) (fun v hv => ?_)
      · rw [ideleInfAt_mul, ideleInfAt_infPart, ideleInfAt_localPart, mul_one]
        exact ham.1 w' (by rw [hminf]; exact hw')
      · rw [ideleFinAt_mul, ideleFinAt_infPart, ideleFinAt_localPart, if_pos hv, one_mul]
        refine (ham.2 v (by rw [hmS]; exact hv)).trans ?_
        rw [WithZero.exp_le_exp]
        have := hmord v hv
        omega
      · rw [ideleFinAt_mul, ideleFinAt_infPart, ideleFinAt_localPart, if_neg hv, one_mul, map_one]
    show ψ ⟨toPrincipalIdeal (𝓞 K) K a, haS⟩ = 1
    rw [hb, hψx]
    show φ (a' * (infPart a' * localPart a' T)⁻¹) = 1
    rw [map_mul, map_inv, hw, inv_one, mul_one, ha', hK a]
  · intro x hx b hb
    have : b = idealOfTrivialAt S ⟨x, hx⟩ := Subtype.ext (by rw [idealOfTrivialAt_apply]; exact hb)
    rw [this, hψx]

/-- A topological group **has no small subgroups** (Milne, *CFT*, V, Remark 4.8): some neighbourhood of $1$ contains no
nontrivial subgroup. -/
def NoSmallSubgroups (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥

/-- **Admissible homomorphism** (Milne, *CFT*, V, Remark 4.8, p. 174): $\psi : I^S \to G$ ($G$ a commutative topological
group) such that for every neighbourhood $N$ of $1$ there is a modulus $\mathfrak m$ (supported in $S$) with
$\psi(i(K_{\mathfrak m,1})) \subseteq N$. -/
@[kb "milne2020cft" "Ch. V, Remark 4.8 (admissible homomorphism)"]
def IsAdmissible {G : Type*} [CommGroup G] [TopologicalSpace G] (S : Set (HeightOneSpectrum (𝓞 K)))
    (ψ : sIdeals S →* G) : Prop :=
  ∀ N ∈ 𝓝 (1 : G), ∃ m : Modulus K, m.finiteSupport ⊆ S ∧
    ∀ a : Kˣ, a ∈ congruenceSubgroup m → ∀ h : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S, ψ ⟨_, h⟩ ∈ N

variable (K) in
/-- **Remark 4.8** (named statement; Milne, *CFT*, V, Remark 4.8, p. 174; Tate 1967, Prop. 4.1): for a commutative
topological group $G$, every admissible $\psi : I^S \to G$ defines a homomorphism $\varphi : I_K \to G$ with (a), (b),
(c) of Proposition 4.7; if $G$ is complete and has no small subgroups, every continuous $\varphi : I_K \to G$ trivial on
$K^\times$ arises from an admissible $\psi$. The circle group is such a $G$ (`circle_noSmallSubgroups`); admissible
$\psi : I^S \to \mathbb T$ are **Hecke characters**, equivalently continuous characters of $C_K$ with values in the circle
(the library's `HeckeCharacter` allows all of $\mathbb C^\times$). -/
@[kb "milne2020cft" "Ch. V, Remark 4.8 (input)"]
structure Remark4_8 : Prop where
  extend : ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (S : Set (HeightOneSpectrum (𝓞 K)))
    (ψ : sIdeals S →* G), S.Finite → IsAdmissible S ψ →
      ∃ φ : IdeleGroup (𝓞 K) K →* G, Continuous φ ∧ (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) ∧
        ∀ x ∈ idelesTrivialAt S, ∀ b : sIdeals S, (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
          φ x = ψ b
  converse : ∀ (G : Type) [CommGroup G] [UniformSpace G] [IsUniformGroup G] [CompleteSpace G],
    NoSmallSubgroups G → ∀ φ : IdeleGroup (𝓞 K) K →* G, Continuous φ →
      (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) →
      ∃ (S : Set (HeightOneSpectrum (𝓞 K))) (_ : S.Finite) (ψ : sIdeals S →* G), IsAdmissible S ψ ∧
        ∀ x ∈ idelesTrivialAt S, ∀ b : sIdeals S, (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
          φ x = ψ b

/-- The circle group has no small subgroups (Milne, *CFT*, V, Remark 4.8). -/
@[kb "milne2020cft" "Ch. V, Remark 4.8 (the circle group has no small subgroups)"]
theorem circle_noSmallSubgroups : NoSmallSubgroups Circle := by
  refine ⟨{z : Circle | 0 < (z : ℂ).re}, ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ (by simp)
    exact isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
  · intro H hH
    rw [eq_bot_iff]
    intro z hz
    by_contra hz1
    have hz1' : z ≠ 1 := hz1
    set θ := Complex.arg (z : ℂ) with hθ
    have hzexp : (z : ℂ) = Complex.exp (θ * Complex.I) := by
      have := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
      rw [Circle.norm_coe, Complex.ofReal_one, one_mul] at this
      exact this.symm
    have hθ0 : θ ≠ 0 := by
      intro h0
      apply hz1'
      apply Circle.ext
      rw [hzexp, h0]; simp
    have hpos : 0 < |θ| := abs_pos.2 hθ0
    have hex : ∃ k : ℕ, Real.pi / 2 ≤ k * |θ| := by
      obtain ⟨k, hk⟩ := Archimedean.arch (Real.pi / 2) hpos
      exact ⟨k, by simpa [nsmul_eq_mul] using hk⟩
    classical
    set k := Nat.find hex with hk
    have hkspec : Real.pi / 2 ≤ k * |θ| := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h
      rw [h] at hkspec
      simp at hkspec
      linarith [Real.pi_pos]
    have hkm : ¬ (Real.pi / 2 ≤ ((k - 1 : ℕ) : ℝ) * |θ|) := Nat.find_min hex (by omega)
    have hlt : ((k : ℝ) - 1) * |θ| < Real.pi / 2 := by
      push Not at hkm
      rwa [Nat.cast_sub (by omega), Nat.cast_one] at hkm
    have hre : 0 < (z : ℂ).re := hH hz
    have hθlt : |θ| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
    have hzk : (z ^ k) ∈ H := H.pow_mem hz k
    have hre2 : 0 < ((z ^ k : Circle) : ℂ).re := hH hzk
    rw [Circle.coe_pow, hzexp, ← Complex.exp_nat_mul,
      show (k : ℂ) * (θ * Complex.I) = ((k * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re] at hre2
    have hcos : Real.cos (k * θ) ≤ 0 := by
      have : Real.cos (k * θ) = Real.cos (k * |θ|) := by
        rcases abs_choice θ with h | h
        · rw [h]
        · rw [h, mul_neg, Real.cos_neg]
      rw [this]
      apply Real.cos_nonpos_of_pi_div_two_le_of_le hkspec
      nlinarith [Real.pi_pos]
    linarith

/-- **Remark 4.9** (Milne, *CFT*, V, p. 175): for $\varphi : I_K \to G$ continuous ($G$ discrete), trivial on $K^\times$,
with $\varphi(a) = \psi(\mathrm{id}(a))$ on $I_S$ (as in Proposition 4.7):
(a) $\varphi(a) = 1$ if $a_v = 1$ at every finite prime and $a_v > 0$ at every real prime;
(b) $\varphi(a) = 1$ if $a_v = 1$ for $v \in S$ (and $v$ infinite) and $a_v$ is a unit for $v \notin S$;
(c) $\varphi(a) = 1$ for $a$ close to $1$;
(d) there is $n$ such that $\varphi(a) = 1$ whenever $a_v > 0$ at the real primes, $a_v \in 1 + \hat{\mathfrak p}_v^n$ for
$v \in S$, and $a_v$ is a unit for the other finite $v$. -/
@[kb "milne2020cft" "Ch. V, Remark 4.9"]
theorem remark_4_9 {G : Type} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (ψ : sIdeals S →* G)
    (φ : IdeleGroup (𝓞 K) K →* G) (hφ : Continuous φ)
    (hc : ∀ x ∈ idelesTrivialAt S, ∀ b : sIdeals S, (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x →
      φ x = ψ b) :
    (∀ x : IdeleGroup (𝓞 K) K, (∀ v, ideleFinAt x v = 1) →
        (∀ (w : InfinitePlace K) (hw : w.IsReal), IsPosAt w hw (ideleInfAt x w)) → φ x = 1) ∧
      (∀ x ∈ idelesTrivialAt S, (∀ v ∉ S, Valued.v (ideleFinAt x v) = 1) → φ x = 1) ∧
      (∀ᶠ x in 𝓝 (1 : IdeleGroup (𝓞 K) K), φ x = 1) ∧
      ∃ n : ℕ, ∀ x : IdeleGroup (𝓞 K) K,
        (∀ (w : InfinitePlace K) (hw : w.IsReal), IsPosAt w hw (ideleInfAt x w)) →
        (∀ v ∈ S, Valued.v (ideleFinAt x v - 1) ≤ WithZero.exp (-(n : ℤ))) →
        (∀ v ∉ S, Valued.v (ideleFinAt x v) = 1) → φ x = 1 := by
  classical
  have p2 : ∀ x ∈ idelesTrivialAt S, (∀ v ∉ S, Valued.v (ideleFinAt x v) = 1) → φ x = 1 := by
    intro x hx hu
    have h1 : ideleToIdeal K x = 1 := by
      refine (item_4_1.2 x).2 fun v => ?_
      by_cases hv : v ∈ S
      · rw [hx.2 v hv, map_one]
      · exact hu v hv
    have := hc x hx 1 (by rw [h1]; rfl)
    rw [this, map_one]
  refine ⟨fun x hx1 hx2 => infinite_part_ker φ hφ x hx1 hx2, p2, ?_, ?_⟩
  · have hker : (φ ⁻¹' {1} : Set (IdeleGroup (𝓞 K) K)) ∈ 𝓝 (1 : IdeleGroup (𝓞 K) K) :=
      (isOpen_discrete _).preimage hφ |>.mem_nhds (by simp)
    exact Filter.mem_of_superset hker fun x hx => hx
  · obtain ⟨T, n₀, h⟩ := ker_contains φ hφ
    refine ⟨n₀ + 1, fun x h1 h2 h3 => ?_⟩
    set P : Finset (HeightOneSpectrum (𝓞 K)) := T \ hS.toFinset with hP
    have hZ : localPart x P ∈ idelesTrivialAt S := by
      refine ⟨fun w => ideleInfAt_localPart x P w, fun v hv => ?_⟩
      rw [ideleFinAt_localPart, if_neg]
      simp [hP, hS.mem_toFinset, hv]
    have hZ1 : φ (localPart x P) = 1 := by
      refine p2 _ hZ fun v hv => ?_
      rw [ideleFinAt_localPart]
      by_cases hvP : v ∈ P
      · rw [if_pos hvP]; exact h3 v hv
      · rw [if_neg hvP, map_one]
    have hlt : WithZero.exp (-((n₀ + 1 : ℕ) : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hx' : φ (x * (localPart x P)⁻¹) = 1 := by
      refine h _ (fun w hw => ?_) (fun v hv => ?_) (fun v hv => ?_)
      · rw [ideleInfAt_mul, ideleInfAt_inv, ideleInfAt_localPart, inv_one, mul_one]
        exact h1 w hw
      · rw [ideleFinAt_mul, ideleFinAt_inv, ideleFinAt_localPart]
        by_cases hvS : v ∈ S
        · have : v ∉ P := by simp [hP, hS.mem_toFinset, hvS]
          rw [if_neg this, inv_one, mul_one]
          refine (h2 v hvS).trans ?_
          rw [WithZero.exp_le_exp]; omega
        · have : v ∈ P := by simp [hP, hS.mem_toFinset, hvS, hv]
          rw [if_pos this, mul_inv_cancel₀ (ideleFinAt_ne_zero x v), sub_self, map_zero]
          exact zero_le
      · rw [ideleFinAt_mul, ideleFinAt_inv, ideleFinAt_localPart]
        by_cases hvS : v ∈ S
        · have : v ∉ P := by simp [hP, hS.mem_toFinset, hvS]
          rw [if_neg this, inv_one, mul_one]
          exact val_eq_one_of_sub_one_le Valued.v hlt (h2 v hvS)
        · have : v ∉ P := by simp [hP, hS.mem_toFinset, hvS, hv]
          rw [if_neg this, inv_one, mul_one]
          exact h3 v hvS
    calc φ x = φ (x * (localPart x P)⁻¹) * φ (localPart x P) := by rw [← map_mul, inv_mul_cancel_right]
      _ = 1 := by rw [hx', hZ1, mul_one]

/-- The quotient map $I^{S(\mathfrak m)} \to C_\mathfrak m$. -/
def toRayClass (m : Modulus K) : coprimeIdeals m →* RayClassGroup m := QuotientGroup.mk' _

/-- **Remark 4.11**, first part (Milne, *CFT*, V, p. 176): there is a unique continuous homomorphism
$\varphi_\mathfrak m : I_K \to C_\mathfrak m$ with $\varphi_\mathfrak m(K^\times) = 1$ and $\varphi_\mathfrak m(a) =
[\mathrm{id}(a)]$ for $a \in I_{S(\mathfrak m)}$ (Proposition 4.7 for $I^{S(\mathfrak m)} \to C_\mathfrak m$). -/
@[kb "milne2020cft" "Ch. V, Remark 4.11 (the map φ_m : I_K → C_m)"]
theorem remark_4_11_exists (m : Modulus K) :
    letI : TopologicalSpace (RayClassGroup m) := ⊥
    ∃! φ : IdeleGroup (𝓞 K) K →* RayClassGroup m, Continuous φ ∧
      (∀ a : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) ∧
      ∀ x ∈ idelesTrivialAt m.finiteSupport, ∀ b : sIdeals m.finiteSupport,
        (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x → φ x = toRayClass m b := by
  let _ : TopologicalSpace (RayClassGroup m) := ⊥
  have _ : DiscreteTopology (RayClassGroup m) := ⟨rfl⟩
  have _ : Finite (RayClassGroup m) := (theorem_1_7_card m).1
  let ψ : sIdeals m.finiteSupport →* RayClassGroup m := toRayClass m
  have hadm : AdmitsModulus m.finiteSupport Set.univ ψ := by
    refine ⟨m, subset_rfl, Set.subset_univ _, fun a ha h => ?_⟩
    exact (QuotientGroup.eq_one_iff (⟨toPrincipalIdeal (𝓞 K) K a, h⟩ : coprimeIdeals m)).2
      (Subgroup.mem_subgroupOf.2 ⟨a, ha, rfl⟩)
  exact prop_4_7 (G := RayClassGroup m) m.finiteSupport (Ideal.finite_factors m.finite_ne_bot) ψ hadm

/-- If $\mathfrak m \mid \mathfrak m'$ then $K_{\mathfrak m',1} \subseteq K_{\mathfrak m,1}$. -/
theorem congruenceSubgroup_mono {m m' : Modulus K} (h : m.Dvd m') :
    congruenceSubgroup m' ≤ congruenceSubgroup m := by
  rintro a ⟨h1, h2⟩
  refine ⟨fun w hw => h1 w (h.2 hw), fun v hv => ?_⟩
  refine (h2 v (hv.trans h.1)).trans ?_
  rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  unfold Modulus.ord
  refine Associates.count_le_count_of_le ?_ v.associates_irreducible ?_
  · exact (Associates.mk_ne_zero.2 m'.finite_ne_bot)
  · exact Associates.mk_le_mk_iff_dvd.2 h.1

/-- The map $C_{\mathfrak m'} \to C_\mathfrak m$ for $\mathfrak m \mid \mathfrak m'$. -/
def rayClassMap {m m' : Modulus K} (h : m.Dvd m') : RayClassGroup m' →* RayClassGroup m :=
  QuotientGroup.map _ _ (Subgroup.inclusion (fun I hI v hv => hI v (by
      exact dvd_trans hv h.1))) (by
    rintro ⟨I, hI⟩ hI'
    rw [Subgroup.mem_subgroupOf] at hI'
    obtain ⟨a, ha, rfl⟩ := hI'
    exact ⟨a, congruenceSubgroup_mono h ha, rfl⟩)

/-- The idèles $I_\infty^+$: $a_v = 1$ at every finite prime and $a_v > 0$ at every real prime (Milne, *CFT*, V,
Remark 4.11, p. 176): the identity component of $(K \otimes \mathbb R)^\times$. -/
def idelesInfPos (K : Type) [Field K] [NumberField K] : Subgroup (IdeleGroup (𝓞 K) K) where
  carrier := {x | (∀ v, ideleFinAt x v = 1) ∧ ∀ (w : InfinitePlace K) (hw : w.IsReal), IsPosAt w hw (ideleInfAt x w)}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · rw [ideleFinAt_mul, hx1 v, hy1 v, one_mul]
    · have h1 := hx2 w hw
      have h2 := hy2 w hw
      unfold IsPosAt at *
      rw [ideleInfAt_mul, map_mul]
      positivity
  one_mem' := by
    refine ⟨fun v => ideleFinAt_one v, fun w hw => ?_⟩
    unfold IsPosAt; rw [ideleInfAt_one]; simp
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · rw [ideleFinAt_inv, hx1 v, inv_one]
    · have h1 := hx2 w hw
      unfold IsPosAt at *
      rw [ideleInfAt_inv, map_inv₀]
      positivity

variable (K) in
/-- **Remark 4.11** (named statement; Milne, *CFT*, V, Remark 4.11, p. 176): the maps $\varphi_\mathfrak m$ combine to a
continuous homomorphism $I_K \to \varprojlim C_\mathfrak m$ that is onto (every compatible family $(c_\mathfrak m)$ is
attained), with kernel the closure of $I_\infty^+\cdot K^\times$. -/
@[kb "milne2020cft" "Ch. V, Remark 4.11 (input)"]
structure Remark4_11 : Prop where
  surjective : ∀ (φ : ∀ m : Modulus K, IdeleGroup (𝓞 K) K →* RayClassGroup m),
    (∀ m, (∀ a : Kˣ, φ m (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) ∧
      ∀ x ∈ idelesTrivialAt m.finiteSupport, ∀ b : sIdeals m.finiteSupport,
        (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x → φ m x = toRayClass m b) →
    ∀ c : ∀ m : Modulus K, RayClassGroup m, (∀ m m' (h : m.Dvd m'), rayClassMap h (c m') = c m) →
      ∃ x : IdeleGroup (𝓞 K) K, ∀ m, φ m x = c m
  ker_eq : ∀ (φ : ∀ m : Modulus K, IdeleGroup (𝓞 K) K →* RayClassGroup m),
    (∀ m, (∀ a : Kˣ, φ m (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1) ∧
      ∀ x ∈ idelesTrivialAt m.finiteSupport, ∀ b : sIdeals m.finiteSupport,
        (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = ideleToIdeal K x → φ m x = toRayClass m b) →
    ∀ x : IdeleGroup (𝓞 K) K, (∀ m, φ m x = 1) ↔
      x ∈ closure ((idelesInfPos K ⊔ IdeleGroup.principalSubgroup (𝓞 K) K : Subgroup _) : Set (IdeleGroup (𝓞 K) K))

/-! ## Norms of idèles (pp. 176–177) -/

/-- **The norm of idèles** $\mathrm{Nm}_{L/K} : I_L \to I_K$ (Milne, *CFT*, V, §4, p. 177): the library's
`Ideles.ideleRelNorm` for the basis `Module.finBasis K L`. -/
@[kb "milne2020cft" "Ch. V, §4, p. 177 (the norm of idèles)"]
def ideleNormMap (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    IdeleGroup (𝓞 L) L →ₜ* IdeleGroup (𝓞 K) K :=
  Ideles.ideleRelNorm (Module.finBasis K L)

section NormComm

/-- The kernel of `ideleToIdeal` is open. -/
theorem isOpen_ker_ideleToIdeal (F : Type) [Field F] [NumberField F] :
    IsOpen ((ideleToIdeal F).ker : Set (IdeleGroup (𝓞 F) F)) := by
  have hcont : Continuous (Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) :
      AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F).toMonoidHom) :=
    Continuous.units_map _ continuous_snd
  have : ((ideleToIdeal F).ker : Set (IdeleGroup (𝓞 F) F)) =
      (Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) :
        AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F).toMonoidHom) ⁻¹'
        (QuadFormsKB.Tamagawa.Measure.Weil.OHatUnits F : Set (FiniteAdeleRing (𝓞 F) F)ˣ) := by
    ext x
    exact QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal_eq_one_iff _
  rw [this]
  exact QuadFormsKB.Tamagawa.Measure.Weil.isOpen_OHatUnits.preimage hcont

/-- A homomorphism to $\mathbb Z$ that is continuous (for the discrete topology) is trivial on compact subgroups. -/
theorem eq_one_of_compact_subgroup {A : Type*} [Group A] [TopologicalSpace A]
    [TopologicalSpace (Multiplicative ℤ)] [DiscreteTopology (Multiplicative ℤ)]
    (χ : A →* Multiplicative ℤ) (hχ : Continuous χ) (U : Subgroup A) (hU : IsCompact (U : Set A))
    (u : A) (hu : u ∈ U) : χ u = 1 := by
  by_contra hne
  have hfin : (χ '' (U : Set A)).Finite := (hU.image hχ).finite_of_discrete
  have hne' : Multiplicative.toAdd (χ u) ≠ 0 := fun h0 =>
    hne (Multiplicative.toAdd.injective (h0.trans toAdd_one.symm))
  have hinj : Function.Injective (fun n : ℕ => χ u ^ n) := by
    intro n m h
    have h' : Multiplicative.toAdd (χ u ^ n) = Multiplicative.toAdd (χ u ^ m) := congrArg _ h
    rw [toAdd_pow, toAdd_pow] at h'
    exact_mod_cast mul_left_injective₀ hne' h'
  have hinf : (Set.range fun n : ℕ => χ u ^ n).Infinite := Set.infinite_range_of_injective hinj
  exact hinf (hfin.subset (by
    rintro _ ⟨n, rfl⟩
    exact ⟨u ^ n, U.pow_mem hu n, map_pow χ u n⟩))

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

/-- The order at `p` of the ideal of the norm of an idèle, as a homomorphism. -/
def normOrd (p : HeightOneSpectrum (𝓞 K)) : IdeleGroup (𝓞 L) L →* Multiplicative ℤ :=
  (countHom p).comp ((ideleToIdeal K).comp
    (ideleNormMap K L : IdeleGroup (𝓞 L) L →* IdeleGroup (𝓞 K) K))

theorem isOpen_ker_normOrd (p : HeightOneSpectrum (𝓞 K)) :
    IsOpen ((normOrd (K := K) L p).ker : Set (IdeleGroup (𝓞 L) L)) := by
  have hN := (isOpen_ker_ideleToIdeal K).preimage (ideleNormMap K L).continuous
  have h1 : (1 : IdeleGroup (𝓞 L) L) ∈
      (ideleNormMap K L).toContinuousMap ⁻¹' ((ideleToIdeal K).ker : Set (IdeleGroup (𝓞 K) K)) := by
    show ideleNormMap K L 1 ∈ ((ideleToIdeal K).ker : Set (IdeleGroup (𝓞 K) K))
    rw [map_one]; exact one_mem _
  have hsub : (ideleNormMap K L).toContinuousMap ⁻¹' ((ideleToIdeal K).ker : Set (IdeleGroup (𝓞 K) K)) ⊆
      ((normOrd (K := K) L p).ker : Set (IdeleGroup (𝓞 L) L)) := by
    intro x hx
    have h1 : ideleToIdeal K (ideleNormMap K L x) = 1 := hx
    show normOrd (K := K) L p x = 1
    simp [normOrd, h1]
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hN.mem_nhds h1) hsub)

theorem normOrd_ker (p : HeightOneSpectrum (𝓞 K)) (y : IdeleGroup (𝓞 L) L)
    (hy : ideleToIdeal L y = 1) : normOrd (K := K) L p y = 1 := by
  let _ : TopologicalSpace (Multiplicative ℤ) := ⊥
  have _ : DiscreteTopology (Multiplicative ℤ) := ⟨rfl⟩
  have hcont : Continuous (normOrd (K := K) L p) := continuous_of_isOpen_ker _ (isOpen_ker_normOrd L p)
  set g := infPart y with hgdef
  have hg1 : ideleToIdeal L g = 1 := (item_4_1.2 g).2 fun v => by
    rw [hgdef, ideleFinAt_infPart, map_one]
  have hg : normOrd (K := K) L p g = 1 := by
    have h2 : normOrd (K := K) L p (g * g) = 1 :=
      infinite_part_ker _ hcont (g * g) (fun v => by rw [ideleFinAt_mul, hgdef, ideleFinAt_infPart, one_mul])
        (fun w hw => by
          rw [ideleInfAt_mul, hgdef, ideleInfAt_infPart]
          have h0 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (ideleInfAt y w) ≠ 0 :=
            (map_ne_zero _).2 (ideleInfAt_ne_zero y w)
          unfold IsPosAt
          rw [map_mul]
          exact mul_self_pos.2 h0)
    rw [map_mul] at h2
    have h3 := congrArg Multiplicative.toAdd h2
    simp only [toAdd_mul, toAdd_one] at h3
    exact Multiplicative.toAdd.injective (by rw [toAdd_one]; omega)
  have hz1 : ideleToIdeal L (y * g⁻¹) = 1 := by rw [map_mul, map_inv, hy, hg1]; simp
  have hz : normOrd (K := K) L p (y * g⁻¹) = 1 := by
    set j : (FiniteAdeleRing (𝓞 L) L)ˣ →* IdeleGroup (𝓞 L) L :=
      Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) with hj
    have hjc : Continuous j := Continuous.units_map _
      (continuous_const.prodMk continuous_id :
        Continuous fun a : FiniteAdeleRing (𝓞 L) L => ((1 : InfiniteAdeleRing L), a))
    have hU : IsCompact (((QuadFormsKB.Tamagawa.Measure.Weil.OHatUnits L).map j : Subgroup _) :
        Set (IdeleGroup (𝓞 L) L)) := by
      rw [Subgroup.coe_map]
      exact (QuadFormsKB.Tamagawa.Measure.Weil.isCompact_OHatUnits (F := L)).image hjc
    refine eq_one_of_compact_subgroup _ hcont _ hU _ ⟨Units.map (RingHom.snd (InfiniteAdeleRing L)
      (FiniteAdeleRing (𝓞 L) L) : AdeleRing (𝓞 L) L →+* FiniteAdeleRing (𝓞 L) L).toMonoidHom (y * g⁻¹),
      (QuadFormsKB.Tamagawa.Measure.Weil.ideleIdeal_eq_one_iff _).1 hz1, ?_⟩
    apply Units.ext
    refine Prod.ext (funext fun w => ?_) rfl
    show (1 : w.Completion) = ideleInfAt (y * g⁻¹) w
    rw [ideleInfAt_mul, ideleInfAt_inv, hgdef, ideleInfAt_infPart]
    exact (mul_inv_cancel₀ (ideleInfAt_ne_zero y w)).symm
  calc normOrd (K := K) L p y = normOrd (K := K) L p (y * g⁻¹) * normOrd (K := K) L p g := by
        rw [← map_mul, inv_mul_cancel_right]
    _ = 1 := by rw [hz, hg, mul_one]

/-- The ideal of a local idèle. -/
theorem ideleToIdeal_ofAdicCompletion {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (u : (w.adicCompletion F)ˣ) :
    ideleToIdeal F (IdeleGroup.ofAdicCompletion (𝓞 F) F w u) =
      primeUnitIdeal w ^ (-(WithZero.log (Valued.v (u : w.adicCompletion F)))) := by
  classical
  refine QuadFormsKB.Tamagawa.Measure.Weil.fracIdeal_ext_count fun v => ?_
  have h2 := QuadFormsKB.Tamagawa.Measure.Weil.count_ideleIdeal (F := F)
    (Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F →+*
      FiniteAdeleRing (𝓞 F) F).toMonoidHom (IdeleGroup.ofAdicCompletion (𝓞 F) F w u)) v
  have h2' : FractionalIdeal.count F v ((ideleToIdeal F (IdeleGroup.ofAdicCompletion (𝓞 F) F w u) :
      (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) =
      QuadFormsKB.Tamagawa.Measure.Weil.ordAt (Units.map (RingHom.snd (InfiniteAdeleRing F)
        (FiniteAdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F).toMonoidHom
        (IdeleGroup.ofAdicCompletion (𝓞 F) F w u)) v := h2
  rw [h2', Units.val_zpow_eq_zpow_val, FractionalIdeal.count_zpow, count_primeUnitIdeal]
  unfold QuadFormsKB.Tamagawa.Measure.Weil.ordAt
  by_cases hvw : w = v
  · subst hvw
    have : ((Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) :
        AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F).toMonoidHom
        (IdeleGroup.ofAdicCompletion (𝓞 F) F w u) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
        FiniteAdeleRing (𝓞 F) F) w = (u : w.adicCompletion F) :=
      Ideles.finiteOfAdicCompletion_self w _
    rw [this]
    simp
  · have : ((Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) :
        AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F).toMonoidHom
        (IdeleGroup.ofAdicCompletion (𝓞 F) F w u) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
        FiniteAdeleRing (𝓞 F) F) v = 1 :=
      Ideles.finiteOfAdicCompletion_of_ne (Ne.symm hvw) _
    rw [this]
    simp [hvw]

/-- The norm diagram on ideals, for a local idèle. -/
theorem norm_comm_ofAdicCompletion (P : HeightOneSpectrum (𝓞 L)) (u : (P.adicCompletion L)ˣ) :
    ideleToIdeal K (ideleNormMap K L (IdeleGroup.ofAdicCompletion (𝓞 L) L P u)) =
      idealNorm K L (ideleToIdeal L (IdeleGroup.ofAdicCompletion (𝓞 L) L P u)) := by
  have hN : ideleNormMap K L (IdeleGroup.ofAdicCompletion (𝓞 L) L P u) =
      IdeleGroup.ofAdicCompletion (𝓞 K) K (primeBelow K L P) (Ideles.localNorm (Module.finBasis K L) P u) :=
    Ideles.ideleRelNorm_ofAdicCompletion (Module.finBasis K L) P u
  rw [hN, ideleToIdeal_ofAdicCompletion, ideleToIdeal_ofAdicCompletion, map_zpow, idealNorm_primeUnitIdeal,
    ← zpow_natCast, ← zpow_mul, Ideles.valued_localNorm, WithZero.log_pow]
  congr 1
  rw [nsmul_eq_mul]
  ring

open scoped Classical in
theorem localPart_insert (x : IdeleGroup (𝓞 L) L) (F : Finset (HeightOneSpectrum (𝓞 L)))
    (a : HeightOneSpectrum (𝓞 L)) (ha : a ∉ F) :
    localPart x (insert a F) = localPart x F *
      IdeleGroup.ofAdicCompletion (𝓞 L) L a (Units.mk0 (ideleFinAt x a) (ideleFinAt_ne_zero x a)) := by
  apply Units.ext
  refine Prod.ext (funext fun w => ?_) (FiniteAdeleRing.ext _ fun v => ?_)
  · show (1 : w.Completion) = 1 * 1
    rw [mul_one]
  · have e : ideleFinAt (IdeleGroup.ofAdicCompletion (𝓞 L) L a
        (Units.mk0 (ideleFinAt x a) (ideleFinAt_ne_zero x a))) v =
        FiniteAdeleRing.ofAdicCompletion L a (ideleFinAt x a) v := rfl
    change ideleFinAt (localPart x (insert a F)) v =
      ideleFinAt (localPart x F * IdeleGroup.ofAdicCompletion (𝓞 L) L a
        (Units.mk0 (ideleFinAt x a) (ideleFinAt_ne_zero x a))) v
    rw [ideleFinAt_mul, e, ideleFinAt_localPart, ideleFinAt_localPart]
    by_cases hva : v = a
    · subst hva
      rw [if_pos (Finset.mem_insert_self _ _), if_neg ha, Ideles.finiteOfAdicCompletion_self, one_mul]
    · by_cases hvF : v ∈ F
      · rw [if_pos (Finset.mem_insert_of_mem hvF), if_pos hvF, Ideles.finiteOfAdicCompletion_of_ne hva, mul_one]
      · rw [if_neg (by simp [hva, hvF]), if_neg hvF, Ideles.finiteOfAdicCompletion_of_ne hva, mul_one]

end NormComm

/-- **The norm diagram** (Milne, *CFT*, V, §4, p. 177): $\mathrm{Nm}_{L/K}$ commutes with $L^\times \to I_L$ and with
$\mathrm{id} : I_L \to I_L$ (ideals), so it induces $C_L \to C_K$ on idèle classes compatible with
$\mathrm{Nm} : I_L/i(L^\times) \to I_K/i(K^\times)$. -/
@[kb "milne2020cft" "Ch. V, §4, p. 177 (the norm commutes with K^× → I and id)"]
theorem ideleNormMap_comm (L : Type) [Field L] [NumberField L] [Algebra K L] :
    (∀ α : Lˣ, ideleNormMap K L (IdeleGroup.unitEmbedding (𝓞 L) L α) =
      IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (Algebra.norm K : L →* K) α)) ∧
    ∀ x : IdeleGroup (𝓞 L) L, ideleToIdeal K (ideleNormMap K L x) = idealNorm K L (ideleToIdeal L x) := by
  refine ⟨fun α => Ideles.ideleRelNorm_unitEmbedding (Module.finBasis K L) α, fun x => ?_⟩
  classical
  obtain ⟨z, hz⟩ : ∃ z : (FiniteAdeleRing (𝓞 L) L)ˣ, z = Units.map (RingHom.snd (InfiniteAdeleRing L)
    (FiniteAdeleRing (𝓞 L) L) : AdeleRing (𝓞 L) L →+* FiniteAdeleRing (𝓞 L) L).toMonoidHom x := ⟨_, rfl⟩
  have hfin := QuadFormsKB.Tamagawa.Measure.Weil.finite_ordAt z
  set F : Finset (HeightOneSpectrum (𝓞 L)) := hfin.toFinset with hF
  have key : ∀ F' : Finset (HeightOneSpectrum (𝓞 L)),
      ideleToIdeal K (ideleNormMap K L (localPart x F')) = idealNorm K L (ideleToIdeal L (localPart x F')) := by
    intro F'
    induction F' using Finset.induction_on with
    | empty =>
      have h1 : localPart x ∅ = 1 := by
        apply Units.ext
        refine Prod.ext rfl (FiniteAdeleRing.ext _ fun v => ?_)
        change ideleFinAt (localPart x ∅) v = 1
        rw [ideleFinAt_localPart, if_neg (Finset.notMem_empty v)]
      rw [h1, map_one, map_one, map_one, map_one]
    | insert a F' ha ih =>
      rw [localPart_insert L x F' a ha, map_mul, map_mul, map_mul, map_mul, ih, norm_comm_ofAdicCompletion]
  have hyker : ideleToIdeal L (x * (localPart x F)⁻¹) = 1 := by
    refine (item_4_1.2 _).2 fun v => ?_
    rw [ideleFinAt_mul, ideleFinAt_inv, ideleFinAt_localPart]
    by_cases hv : v ∈ F
    · rw [if_pos hv, mul_inv_cancel₀ (ideleFinAt_ne_zero x v), map_one]
    · rw [if_neg hv, inv_one, mul_one]
      have hv0 : QuadFormsKB.Tamagawa.Measure.Weil.ordAt z v = 0 := by
        by_contra h
        exact hv (hfin.mem_toFinset.2 h)
      have := (QuadFormsKB.Tamagawa.Measure.Weil.ordAt_eq_zero_iff z v).1 hv0
      rw [hz] at this
      exact this
  have hx : x = (x * (localPart x F)⁻¹) * localPart x F := by rw [inv_mul_cancel_right]
  have hN1 : ideleToIdeal K (ideleNormMap K L (x * (localPart x F)⁻¹)) = 1 := by
    refine QuadFormsKB.Tamagawa.Measure.Weil.fracIdeal_ext_count fun p => ?_
    have h0 := normOrd_ker (K := K) L p _ hyker
    have h3 : FractionalIdeal.count K p ((ideleToIdeal K (ideleNormMap K L (x * (localPart x F)⁻¹)) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
      have := congrArg Multiplicative.toAdd h0
      simpa [normOrd, countHom] using this
    rw [h3, Units.val_one, FractionalIdeal.count_one]
  have e1 : ideleToIdeal K (ideleNormMap K L x) = ideleToIdeal K (ideleNormMap K L (x * (localPart x F)⁻¹)) *
      ideleToIdeal K (ideleNormMap K L (localPart x F)) := by
    simp only [← map_mul, inv_mul_cancel_right]
  have e2 : idealNorm K L (ideleToIdeal L x) = idealNorm K L (ideleToIdeal L (x * (localPart x F)⁻¹)) *
      idealNorm K L (ideleToIdeal L (localPart x F)) := by
    simp only [← map_mul, inv_mul_cancel_right]
  rw [e1, e2, key F, hN1, hyker, map_one, one_mul]

/-- **Proposition 4.12(a)** (Milne, *CFT*, V, p. 177): $\mathrm{Nm}_{\mathbb C/\mathbb R}(\mathbb C^\times) = \mathbb R_{>0}$. -/
@[kb "milne2020cft" "Ch. V, Proposition 4.12(a)"]
theorem prop_4_12a : Set.range (fun z : ℂˣ => Algebra.norm ℝ (z : ℂ)) = Set.Ioi 0 := by
  ext t
  simp only [Set.mem_range, Set.mem_Ioi, Algebra.norm_complex_apply]
  constructor
  · rintro ⟨z, rfl⟩
    exact Complex.normSq_pos.2 z.ne_zero
  · intro ht
    refine ⟨Units.mk0 (Real.sqrt t : ℂ) ?_, ?_⟩
    · exact_mod_cast (Real.sqrt_pos.2 ht).ne'
    · simp only [Units.val_mk0, Complex.normSq_ofReal]
      exact Real.mul_self_sqrt ht.le

open LocalCFT in
/-- **Proposition 4.12(b)** (named statement; Milne, *CFT*, V, Proposition 4.12(b), p. 177, citing I, 1.3): for a finite
extension $L$ of a nonarchimedean local field $F$ (of characteristic zero), $\mathrm{Nm}_{L/F}(L^\times) \supseteq
1 + \mathfrak p_F^n$ for some $n$.

**Proved here** as `prop4_12b`, from the ported copy under `NumberFieldKB/TauCetiPort/` of Tau Ceti
`TauCeti.exists_unitFiltration_le_normGroup` (`TauCeti/NumberTheory/LocalField/Norm/Open.lean:107`) (read at Tau Ceti `7ed979dc`, ported from `67aa1716`). Needed to apply it here: Tau Ceti states it for a step of its unit filtration and without a restriction on
the characteristic; one must identify that step with the units congruent to one modulo the n-th power of the maximal
ideal. -/
@[kb "milne2020cft" "Ch. V, Proposition 4.12(b) (input)"]
structure Prop4_12b (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (Ω : Type*) [Field Ω] [Algebra F Ω] [IsSepClosure F Ω] : Prop where
  exists_pow : ∀ (L : IntermediateField F Ω) [FiniteDimensional F L], ∃ n : ℕ, ∀ u : Fˣ,
    (∃ x ∈ (𝓂[F]) ^ n, (u : F) = 1 + algebraMap 𝒪[F] F x) → u ∈ normGroup L

open LocalCFT in
/-- **Proposition 4.12(b), proved** (Milne, *CFT*, V, Proposition 4.12(b)): the named statement `Prop4_12b` holds,
from Tau Ceti's `TauCeti.exists_unitFiltration_le_normGroup` (ported,
`NumberFieldKB/TauCetiPort/NumberTheory/LocalField/Norm/Open.lean`): the norm group contains a step $U(F, n)$ of the
unit filtration, and every $1 + x$ with $x \in \mathfrak p_F^{n+1}$ lies in $U(F, n)$. No restriction on the
characteristic is needed. -/
@[kb "milne2020cft" "Ch. V, Proposition 4.12(b)"]
theorem prop4_12b (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (Ω : Type*) [Field Ω] [Algebra F Ω] [IsSepClosure F Ω] : Prop4_12b F Ω := by
  refine ⟨fun L _ => ?_⟩
  have : Algebra.IsSeparable F Ω := IsSepClosure.separable
  have : Algebra.IsSeparable F L := Algebra.isSeparable_tower_bot_of_isSeparable F L Ω
  obtain ⟨n, hn⟩ := TauCeti.exists_unitFiltration_le_normGroup (K := F) (L := L)
  refine ⟨n + 1, fun u ⟨x, hx, hux⟩ => hn ?_⟩
  have hxm : x ∈ 𝓂[F] := Ideal.pow_le_self (Nat.succ_ne_zero n) hx
  have hunit : IsUnit (1 + x) := by
    by_contra h
    have h1 : 1 + x ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal _).2 h
    exact (IsLocalRing.maximalIdeal.isMaximal 𝒪[F]).ne_top
      ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem h1 hxm))
  rw [TauCeti.mem_unitFiltration_iff_exists]
  refine ⟨hunit.unit, ?_, ?_⟩
  · simpa using Ideal.pow_le_pow_right (Nat.le_succ n) hx
  · simp [hux]; rfl

open LocalCFT in
/-- **Proposition 4.12(c)** (Milne, *CFT*, V, p. 177, citing III, 1.2; proved from the local inputs of Chapter I: the
local reciprocity law and the facts on unramified extensions): for a finite unramified extension $L$ of a nonarchimedean
local field $F$, $\mathrm{Nm}_{L/F}(L^\times) \supseteq \mathcal O_F^\times$. (Unramified extensions are abelian,
`UnramifiedInput`; here $L$ is taken abelian.) -/
@[kb "milne2020cft" "Ch. V, Proposition 4.12(c)"]
theorem prop_4_12c (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (Ω : Type*) [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]
    (hR : LocalReciprocityExistence F Ω) (hU : UnramifiedInput F Ω) (L : FiniteAbelianExt F Ω)
    (hL : IsUnramifiedExt L.toField) :
    (Units.map (algebraMap 𝒪[F] F).toMonoidHom).range ≤ normGroup L.toField := by
  obtain ⟨φ, hφ⟩ := hR.exists_artin
  intro x hx
  have h1 : φ L x = 1 := artin_unit_eq_one hU hφ (u := x) hx L hL
  rw [← hφ.ker_eq L]
  exact h1

variable (K) in
/-- **Corollary 4.13** (named statement; Milne, *CFT*, V, Corollary 4.13, p. 177, from Proposition 4.12 at every
place): for a finite extension $L/K$ of number fields, $\mathrm{Nm}_{L/K}(I_L) \supseteq W_\mathfrak m$ for some
modulus $\mathfrak m$.

**Proved elsewhere** (recorded, not imported): Tau Ceti
`TauCeti.GlobalNumberFields.exists_ideleCongruenceSubgroup_le_range_ideleNormMap`
(`TauCeti/NumberTheory/NumberField/Global/Ideles/Norm/Open.lean:67`) at Tau Ceti commit `7ed979dc`. Needed to apply it
here: identify Tau Ceti's congruence subgroup of the ideles for a modulus with our subgroup $W_\mathfrak m$. -/
@[kb "milne2020cft" "Ch. V, Corollary 4.13 (input)"]
structure Cor4_13 : Prop where
  exists_modulus : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L], ∃ m : Modulus K,
    idelesW m ≤ (ideleNormMap K L : IdeleGroup (𝓞 L) L →* IdeleGroup (𝓞 K) K).range

end NumberFieldKB.MilneCFT
