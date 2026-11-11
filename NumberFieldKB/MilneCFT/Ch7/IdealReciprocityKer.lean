import NumberFieldKB.MilneCFT.Ch7.IdealReciprocity
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Algebra.Group.Units

/-!
# The ideal-theoretic reciprocity law from the idelic one (Milne, *CFT*, Chapter V, Remark 5.8, reciprocity half)

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`: Chapter V,
Remark 5.8 (p. 180), Theorem 3.5 (p. 158), Proposition 4.12 (a) (p. 177).

Completes `Ch7/IdealReciprocity.lean`: the kernel of $\psi_{L/K}: I^{S(\mathfrak m)}\to\mathrm{Gal}(L/K)$ is
contained in $P_\mathfrak m\cdot\mathrm{Nm}(I_L^{S(\mathfrak m)})$. If $\psi(\mathfrak a) = 1$, choose $x\in
I_\mathfrak m$ with $\mathrm{id}(x)=\mathfrak a$; then $\phi(x) = 1$, so $x = c\,\mathrm{Nm}(y)$ with $c\in K^\times$.
Choose $\beta\in L^\times$ with $\beta y$ close to $1$ at the primes above $S(\mathfrak m)$
(`exists_mul_close_above`, weak approximation and continuity of the norm). Then $c' = c\,\mathrm{Nm}(\beta)^{-1} =
x\,\mathrm{Nm}(\beta y)^{-1}$ lies in $K_{\mathfrak m,1}$ (the norm of an idele is positive at the real places
ramified in $L$, `isPosAt_ideleNormMap`, Proposition 4.12 (a)), and $\mathfrak a = (c')\cdot\mathrm{Nm}(\mathrm{id}(\beta y))$
with $\mathrm{id}(\beta y)$ prime to $S(\mathfrak m)$ (`ideleNormMap_comm`).
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

/-! ## Locality of the idele norm -/

section Locality

open QuadFormsKB.Tamagawa.Measure.Weil NumberFieldKB.Ideles NumberField.mixedEmbedding Matrix

theorem adeleDet_mul_eq_of_idem (E : Adeles K) (hE : IsIdempotentElem E) (y : Adeles L)
    (h : adeleMap K L E * y = adeleMap K L E) :
    adeleDet (Module.finBasis K L) y * E = E := by
  have hM : adeleLmat (Module.finBasis K L) y * Matrix.scalar _ E = Matrix.scalar _ E := by
    rw [← adeleLmat_adeleMap (Module.finBasis K L) E, ← adeleLmat_mul, mul_comm y, h]
  have hdet := congrArg Matrix.det hM
  rw [det_mul, Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ] at hdet
  have hn : Fintype.card (Fin (Module.finrank K L)) ≠ 0 := by
    rw [← Module.finrank_eq_card_basis (Module.finBasis K L)]
    exact Module.finrank_pos.ne'
  rw [hE.pow_eq hn] at hdet
  exact hdet

theorem ideleFinAt_ideleNormMap_eq_one (v : HeightOneSpectrum (𝓞 K)) (z : IdeleGroup (𝓞 L) L)
    (hz : ∀ w : HeightOneSpectrum (𝓞 L), primeBelow K L w = v → ideleFinAt z w = 1) :
    ideleFinAt (ideleNormMap K L z) v = 1 := by
  classical
  set E : Adeles K := (0, eAdele v) with hEdef
  have hE : IsIdempotentElem E := Prod.ext (mul_zero 0) (eAdele_mul_self v)
  set y : Adeles L := ((ideleGroupEquiv L z : (Adeles L)ˣ) : Adeles L) with hy
  have h : adeleMap K L E * y = adeleMap K L E := by
    refine Prod.ext ?_ ?_
    · show infRingHom K L 0 * y.1 = infRingHom K L 0
      rw [map_zero, zero_mul]
    · refine FiniteAdeleRing.ext L fun w => ?_
      show (finMap K L (eAdele v)) w * (z : AdeleRing (𝓞 L) L).2 w = (finMap K L (eAdele v)) w
      rw [finMap_eAdele_apply]
      split_ifs with hw
      · rw [one_mul]; exact (hz w hw)
      · simp
  have h1 := adeleDet_mul_eq_of_idem L E hE y h
  have h2 := congrArg (fun a : Adeles K => a.2 v) h1
  have key : ideleFinAt (ideleNormMap K L z) v = (adeleDet (Module.finBasis K L) y).2 v :=
    congrArg (fun g : (Adeles K)ˣ => (g : Adeles K).2 v) (ideleGroupEquiv_ideleRelNorm (Module.finBasis K L) z)
  rw [key]
  simp only [Prod.snd_mul, hEdef] at h2
  have h3 : (eAdele v) v = 1 := by simp [eAdele_apply]
  change (adeleDet (Module.finBasis K L) y).2 v * (eAdele v) v = (eAdele v) v at h2
  rwa [h3, mul_one] at h2

open scoped Classical in
theorem normAtPlace_infRingHom_eq_zero (w : InfinitePlace K) (hw : w.IsReal) (u : InfinitePlace L)
    (hu : u.comap (algebraMap K L) ≠ w) :
    normAtPlace u (infRingHom K L ((Pi.single ⟨w, hw⟩ 1, 0) : mixedSpace K)) = 0 := by
  by_contra hne
  apply hu
  set E : mixedSpace K := (Pi.single ⟨w, hw⟩ 1, 0) with hE
  refine InfinitePlace.ext _ _ fun a => ?_
  have h1 : mixedEmbedding K a * E = (w.embedding_of_isReal hw a) • E := by
    refine Prod.ext (funext fun i => ?_) (by simp [hE])
    by_cases hi : i = ⟨w, hw⟩
    · subst hi; simp [hE, mixedEmbedding]
    · simp [hE, mixedEmbedding, Pi.single_eq_of_ne hi]
  have h2 := congrArg (fun X => normAtPlace u (infRingHom K L X)) h1
  simp only [map_mul] at h2
  have h3 : infRingHom K L ((w.embedding_of_isReal hw a) • E) = (w.embedding_of_isReal hw a) • infRingHom K L E :=
    map_smul (infMap K L) _ _
  rw [h3, infRingHom_mixedEmbedding, normAtPlace_smul, normAtPlace_apply] at h2
  have h4 : |w.embedding_of_isReal hw a| = w a := by
    rw [← Real.norm_eq_abs]; exact InfinitePlace.norm_embedding_of_isReal hw a
  rw [h4] at h2
  rw [InfinitePlace.comap_apply]
  exact mul_right_cancel₀ hne h2

open scoped Classical in
theorem extEmb_ideleInfAt_ideleNormMap_eq_one (w : InfinitePlace K) (hw : w.IsReal) (z : IdeleGroup (𝓞 L) L)
    (hz : ∀ u : InfinitePlace L, u.comap (algebraMap K L) = w → ideleInfAt z u = 1) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (ideleInfAt (ideleNormMap K L z) w) = 1 := by
  set E1 : mixedSpace K := (Pi.single ⟨w, hw⟩ 1, 0) with hE1
  set E : Adeles K := (E1, 0) with hEdef
  have hE : IsIdempotentElem E := by
    refine Prod.ext (Prod.ext ?_ (mul_zero 0)) (mul_zero 0)
    have hs : ∀ j : {w : InfinitePlace K // w.IsReal},
        (Pi.single j (1 : ℝ) : {w : InfinitePlace K // w.IsReal} → ℝ) * Pi.single j 1 = Pi.single j 1 :=
      fun j => by rw [← Pi.single_mul, mul_one]
    exact hs ⟨w, hw⟩
  set y : Adeles L := ((ideleGroupEquiv L z : (Adeles L)ˣ) : Adeles L) with hy
  have h : adeleMap K L E * y = adeleMap K L E := by
    refine Prod.ext ?_ ?_
    · refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · by_cases hc : i.1.comap (algebraMap K L) = w
        · have : (y.1.1 i) = 1 := by
            show InfinitePlace.Completion.extensionEmbeddingOfIsReal i.2 ((z : AdeleRing (𝓞 L) L).1 i.1) = 1
            rw [show (z : AdeleRing (𝓞 L) L).1 i.1 = 1 from hz i.1 hc, map_one]
          show (infRingHom K L E1).1 i * y.1.1 i = (infRingHom K L E1).1 i
          rw [this, mul_one]
        · have h0 := normAtPlace_infRingHom_eq_zero L w hw i.1 hc
          rw [normAtPlace_apply_of_isReal i.2, norm_eq_zero] at h0
          show (infRingHom K L E1).1 i * y.1.1 i = (infRingHom K L E1).1 i
          rw [h0, zero_mul]
      · by_cases hc : i.1.comap (algebraMap K L) = w
        · have : (y.1.2 i) = 1 := by
            show InfinitePlace.Completion.extensionEmbedding i.1 ((z : AdeleRing (𝓞 L) L).1 i.1) = 1
            rw [show (z : AdeleRing (𝓞 L) L).1 i.1 = 1 from hz i.1 hc, map_one]
          show (infRingHom K L E1).2 i * y.1.2 i = (infRingHom K L E1).2 i
          rw [this, mul_one]
        · have h0 := normAtPlace_infRingHom_eq_zero L w hw i.1 hc
          rw [normAtPlace_apply_of_isComplex i.2, norm_eq_zero] at h0
          show (infRingHom K L E1).2 i * y.1.2 i = (infRingHom K L E1).2 i
          rw [h0, zero_mul]
    · show finMap K L 0 * y.2 = finMap K L 0
      rw [map_zero, zero_mul]
  have h1 := adeleDet_mul_eq_of_idem L E hE y h
  have h2 := congrArg (fun a : Adeles K => a.1.1 ⟨w, hw⟩) h1
  have key : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (ideleInfAt (ideleNormMap K L z) w) =
      (adeleDet (Module.finBasis K L) y).1.1 ⟨w, hw⟩ :=
    congrArg (fun g : (Adeles K)ˣ => (g : Adeles K).1.1 ⟨w, hw⟩)
      (ideleGroupEquiv_ideleRelNorm (Module.finBasis K L) z)
  rw [key]
  simpa [hEdef, hE1] using h2

open scoped Classical in
theorem exists_sq_idele (y : IdeleGroup (𝓞 L) L) (P : InfinitePlace L → Prop)
    (hP : ∀ u, P u → u.IsComplex) :
    ∃ t : IdeleGroup (𝓞 L) L, (∀ u, P u → ideleInfAt t u * ideleInfAt t u = ideleInfAt y u) ∧
      (∀ u, ¬ P u → ideleInfAt t u = 1) ∧ (∀ v, ideleFinAt t v = 1) := by
  have hex : ∀ u : InfinitePlace L, ∃ s : u.Completion, s ≠ 0 ∧ (P u → s * s = ideleInfAt y u) ∧ (¬ P u → s = 1) := by
    intro u
    by_cases h : P u
    · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (hP u h)
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self (e (ideleInfAt y u))
      have hs : e.symm r * e.symm r = ideleInfAt y u := by
        rw [← map_mul, ← hr, RingEquiv.symm_apply_apply]
      refine ⟨e.symm r, ?_, fun _ => hs, fun h' => absurd h h'⟩
      intro h0
      rw [h0, mul_zero] at hs
      exact ideleInfAt_ne_zero y u hs.symm
    · exact ⟨1, one_ne_zero, fun h' => absurd h' h, fun _ => rfl⟩
  choose s hs0 hs1 hs2 using hex
  refine ⟨⟨((s : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L)),
    (((fun u => (s u)⁻¹) : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L)),
    Prod.ext (funext fun u => mul_inv_cancel₀ (hs0 u)) (mul_one _),
    Prod.ext (funext fun u => inv_mul_cancel₀ (hs0 u)) (mul_one _)⟩, ?_, ?_, ?_⟩
  · intro u hu; exact hs1 u hu
  · intro u hu; exact hs2 u hu
  · intro v; rfl

theorem isPosAt_ideleNormMap_of_forall (y : IdeleGroup (𝓞 L) L) (w : InfinitePlace K) (hw : w.IsReal)
    (hc : ∀ u : InfinitePlace L, u.comap (algebraMap K L) = w → u.IsComplex) :
    IsPosAt w hw (ideleInfAt (ideleNormMap K L y) w) := by
  obtain ⟨t, ht1, ht2, ht3⟩ := exists_sq_idele L y (fun u => u.comap (algebraMap K L) = w) hc
  obtain ⟨y₂, hy₂def⟩ : ∃ y₂ : IdeleGroup (𝓞 L) L, y₂ = y * (t * t)⁻¹ := ⟨_, rfl⟩
  have hy₂ : ∀ u : InfinitePlace L, u.comap (algebraMap K L) = w → ideleInfAt y₂ u = 1 := by
    intro u hu
    rw [hy₂def, ideleInfAt_mul, ideleInfAt_inv, ideleInfAt_mul, ht1 u hu]
    exact mul_inv_cancel₀ (ideleInfAt_ne_zero y u)
  have h1 := extEmb_ideleInfAt_ideleNormMap_eq_one L w hw y₂ hy₂
  have hy : y = y₂ * (t * t) := by rw [hy₂def]; group
  have hN : ideleNormMap K L y = ideleNormMap K L y₂ * (ideleNormMap K L t * ideleNormMap K L t) := by
    rw [← map_mul, ← map_mul, ← hy]
  unfold IsPosAt
  rw [hN, ideleInfAt_mul, ideleInfAt_mul, map_mul, map_mul, h1, one_mul]
  exact mul_self_pos.2 ((map_ne_zero _).2 (ideleInfAt_ne_zero _ w))

end Locality

/-- The norm of an idele is positive at every real place of $K$ that ramifies in the Galois extension $L$ (all
places above it are then complex; Proposition 4.12 (a)). -/
theorem isPosAt_ideleNormMap [IsGalois K L] (y : IdeleGroup (𝓞 L) L) (w : InfinitePlace K)
    (hw : InfinitePlace.RamifiesIn L w) :
    IsPosAt w hw.1 (ideleInfAt (ideleNormMap K L y) w) := by
  refine isPosAt_ideleNormMap_of_forall L y w hw.1 fun u hu => ?_
  obtain ⟨u₀, hu₀, hc₀⟩ := hw.2
  obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq (k := K) (w := u₀) (w' := u) (hu₀.trans hu.symm)
  rw [← hσ, InfinitePlace.isComplex_smul_iff]
  exact hc₀

section Approx

open scoped Topology

/-- A neighbourhood of `1` in the ideles contains a box. -/
theorem exists_box_idele {F : Type} [Field F] [NumberField F] (W : Set (IdeleGroup (𝓞 F) F))
    (hW : IsOpen W) (h1 : (1 : IdeleGroup (𝓞 F) F) ∈ W) :
    ∃ (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (ε : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ)),
      (∀ v, ε v ≠ 0) ∧ ∀ x : IdeleGroup (𝓞 F) F,
        (∀ w : InfinitePlace F, ideleInfAt x w = 1) →
        (∀ v, Valued.v (ideleFinAt x v) ≤ 1) →
        (∀ v, Valued.v (ideleFinAt x⁻¹ v) ≤ 1) →
        (∀ v ∈ S₀, Valued.v (ideleFinAt x v - 1) < ε v) →
        (∀ v ∈ S₀, Valued.v (ideleFinAt x⁻¹ v - 1) < ε v) → x ∈ W := by
  classical
  set e := Homeomorph.prodUnits (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F) with he
  have hU1 : W ∈ 𝓝 (1 : IdeleGroup (𝓞 F) F) := hW.mem_nhds h1
  have himg : e '' W ∈ 𝓝 ((1 : (InfiniteAdeleRing F)ˣ), (1 : (FiniteAdeleRing (𝓞 F) F)ˣ)) := by
    have h := e.map_nhds_eq (1 : IdeleGroup (𝓞 F) F)
    have h1 : e (1 : IdeleGroup (𝓞 F) F) = (1, 1) := rfl
    rw [h1] at h
    rw [← h]
    exact Filter.image_mem_map hU1
  rw [nhds_prod_eq, Filter.mem_prod_iff] at himg
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := himg
  obtain ⟨S, ε, hε, hbox⟩ := exists_box_units ht₂
  refine ⟨S, ε, hε, fun x h1' h2 h3 h4 h5 => ?_⟩
  have hinf : (e x).1 = 1 := Units.ext (funext fun w => h1' w)
  have hmem : e x ∈ e '' W := by
    refine hsub ⟨?_, hbox _ (fun v => h2 v) (fun v => h3 v) (fun v hv => h4 v hv) (fun v hv => h5 v hv)⟩
    rw [hinf]; exact mem_of_mem_nhds ht₁
  obtain ⟨y, hy, hyx⟩ := hmem
  rwa [← e.injective hyx]

/-- The component at a finite prime, as a homomorphism. -/
def finAtHom {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    IdeleGroup (𝓞 F) F →* v.adicCompletion F where
  toFun x := ideleFinAt x v
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The component at an infinite place, as a homomorphism. -/
def infAtHom {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) :
    IdeleGroup (𝓞 F) F →* w.Completion where
  toFun x := ideleInfAt x w
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The idele equal to `u w` at `w ∈ T` and `1` elsewhere. -/
def prodOfAdic {F : Type} [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F)))
    (u : (w : HeightOneSpectrum (𝓞 F)) → (w.adicCompletion F)ˣ) : IdeleGroup (𝓞 F) F :=
  ∏ w ∈ T, IdeleGroup.ofAdicCompletion (𝓞 F) F w (u w)

open scoped Classical in
theorem ideleFinAt_prodOfAdic {F : Type} [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F)))
    (u : (w : HeightOneSpectrum (𝓞 F)) → (w.adicCompletion F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ideleFinAt (prodOfAdic T u) v = if v ∈ T then (u v : v.adicCompletion F) else 1 := by
  classical
  have h : ideleFinAt (prodOfAdic T u) v =
      ∏ w ∈ T, ideleFinAt (IdeleGroup.ofAdicCompletion (𝓞 F) F w (u w)) v :=
    map_prod (finAtHom v) (fun w => IdeleGroup.ofAdicCompletion (𝓞 F) F w (u w)) T
  rw [h]
  split_ifs with hv
  · rw [Finset.prod_eq_single_of_mem v hv, ideleFinAt_ofAdic_self]
    intro w _ hne
    exact ideleFinAt_ofAdic_ne (Ne.symm hne) _
  · exact Finset.prod_eq_one fun w hw => ideleFinAt_ofAdic_ne (fun h => hv (by rw [h]; exact hw)) _

theorem ideleInfAt_prodOfAdic {F : Type} [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F)))
    (u : (w : HeightOneSpectrum (𝓞 F)) → (w.adicCompletion F)ˣ) (w : InfinitePlace F) :
    ideleInfAt (prodOfAdic T u) w = 1 := by
  have h : ideleInfAt (prodOfAdic T u) w =
      ∏ v ∈ T, ideleInfAt (IdeleGroup.ofAdicCompletion (𝓞 F) F v (u v)) w :=
    map_prod (infAtHom w) (fun v => IdeleGroup.ofAdicCompletion (𝓞 F) F v (u v)) T
  rw [h]
  exact Finset.prod_eq_one fun v _ => ideleInfAt_ofAdic v (u v) w

/-- The primes of `L` above a finite set of primes of `K` form a finite set. -/
theorem finite_primesAbove_ker {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    (primesAbove K L S).Finite := by
  have hsub : primesAbove K L S ⊆ ⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 L) | primeBelow K L w = v} :=
    fun w hw => Set.mem_biUnion hw rfl
  refine Set.Finite.subset (hS.biUnion fun v _ => ?_) hsub
  let f : {w : HeightOneSpectrum (𝓞 L) // primeBelow K L w = v} → v.asIdeal.primesOver (𝓞 L) :=
    fun w => ⟨w.1.asIdeal, w.1.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  exact Set.finite_coe_iff.1 (Finite.of_injective f hf)

end Approx

/-- Weak approximation for the norm: for an idele $y$ of $L$, a finite set $S$ of primes of $K$ and $N$, there is
$\beta\in L^\times$ such that $\beta y$ is a unit at every prime of $L$ above $S$ and $\mathrm{Nm}(\beta y)\equiv 1
\bmod \mathfrak p_v^N$ at every $v\in S$. -/
theorem exists_mul_close_above (y : IdeleGroup (𝓞 L) L) (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (N : ℕ) : ∃ β : Lˣ,
      (∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) ∈ HeightOneSpectrum.asIdeal '' S →
        Valued.v (ideleFinAt (IdeleGroup.unitEmbedding (𝓞 L) L β * y) w) = 1) ∧
      ∀ v ∈ S, Valued.v (ideleFinAt (ideleNormMap K L (IdeleGroup.unitEmbedding (𝓞 L) L β * y)) v - 1) ≤
        WithZero.exp (-(N : ℤ)) := by
  classical
  set A : Set (IdeleGroup (𝓞 K) K) :=
    {x | ∀ v ∈ S, Valued.v (ideleFinAt x v - 1) ≤ WithZero.exp (-(N : ℤ))} with hA
  have hAopen : IsOpen A := by
    have : A = ⋂ v ∈ S, (fun x : IdeleGroup (𝓞 K) K => ideleFinAt x v) ⁻¹'
        {z : v.adicCompletion K | Valued.v (z - 1) ≤ WithZero.exp (-(N : ℤ))} := by
      ext x; simp [hA]
    rw [this]
    refine hS.isOpen_biInter fun v _ => (isOpen_valued_sub_one_le v _).preimage ?_
    exact (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val)
  have hWopen : IsOpen ((ideleNormMap K L) ⁻¹' A) := hAopen.preimage (map_continuous (ideleNormMap K L))
  have hW1 : (1 : IdeleGroup (𝓞 L) L) ∈ (ideleNormMap K L) ⁻¹' A := by
    show ideleNormMap K L 1 ∈ A
    rw [map_one]
    intro v _
    rw [ideleFinAt_one, sub_self, map_zero]; exact zero_le
  obtain ⟨S₀, ε, hε, hbox⟩ := exists_box_idele (ideleNormMap K L ⁻¹' A) hWopen hW1
  set ε' : HeightOneSpectrum (𝓞 L) → WithZero (Multiplicative ℤ) :=
    fun w => min (ε w) (WithZero.exp (-1)) with hε'
  have hlt1 : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hε'0 : ∀ w, ε' w ≠ 0 := fun w =>
    (lt_min (zero_lt_iff.2 (hε w)) (zero_lt_iff.2 WithZero.exp_ne_zero)).ne'
  have hε'1 : ∀ w, ε' w ≤ WithZero.exp (-1) := fun w => min_le_right _ _
  have hε'2 : ∀ w, ε' w ≤ ε w := fun w => min_le_left _ _
  have hTfin := finite_primesAbove_ker (K := K) (L := L) hS
  set T := hTfin.toFinset with hT
  have hTmem : ∀ w, w ∈ T ↔ primeBelow K L w ∈ S := fun w => by
    rw [hT, Set.Finite.mem_toFinset]; rfl
  have hy0 : ∀ w, Valued.v (ideleFinAt y w) ≠ 0 := fun w => by
    rw [Ne, map_eq_zero]; exact ideleFinAt_ne_zero y w
  set γ : HeightOneSpectrum (𝓞 L) → WithZero (Multiplicative ℤ) :=
    fun w => ε' w * (Valued.v (ideleFinAt y w))⁻¹ with hγ
  have hγ0 : ∀ w, γ w ≠ 0 := fun w => mul_ne_zero (hε'0 w) (inv_ne_zero (hy0 w))
  choose c hc using fun w => exists_close w ((ideleFinAt y w)⁻¹) (γ w) (hγ0 w)
  obtain ⟨b, hb1, -⟩ := exists_approx T ∅ c γ (fun w _ => hγ0 w) (fun _ => 0)
  have hbT : ∀ w ∈ T, Valued.v (algebraMap L (w.adicCompletion L) b * ideleFinAt y w - 1) < ε' w := by
    intro w hw
    have h1 : Valued.v (algebraMap L (w.adicCompletion L) (b - c w)) < γ w := by
      have e : Valued.v (algebraMap L (w.adicCompletion L) (b - c w)) = w.valuation L (b - c w) :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ _
      rw [e]; exact hb1 w hw
    have hα := ideleFinAt_ne_zero y w
    have hinv : (ideleFinAt y w)⁻¹ * ideleFinAt y w = 1 := inv_mul_cancel₀ hα
    have e : algebraMap L (w.adicCompletion L) b * ideleFinAt y w - 1 =
        (algebraMap L (w.adicCompletion L) (b - c w) +
          (algebraMap L (w.adicCompletion L) (c w) - (ideleFinAt y w)⁻¹)) * ideleFinAt y w := by
      rw [map_sub]; linear_combination hinv
    rw [e, map_mul]
    have h2 := Valuation.map_add_lt _ h1 (hc w)
    calc _ < γ w * Valued.v (ideleFinAt y w) := mul_lt_mul_of_pos_right h2 (zero_lt_iff.2 (hy0 w))
      _ = ε' w := inv_mul_cancel_right₀ (hy0 w) (ε' w)
  obtain ⟨b', hb'0, hb'⟩ : ∃ b' : L, b' ≠ 0 ∧
      ∀ w ∈ T, Valued.v (algebraMap L (w.adicCompletion L) b' * ideleFinAt y w - 1) < ε' w := by
    by_cases hb0 : b = 0
    · refine ⟨1, one_ne_zero, fun w hw => ?_⟩
      exfalso
      have := hbT w hw
      rw [hb0, map_zero, zero_mul, zero_sub, Valuation.map_neg, map_one] at this
      exact lt_irrefl _ ((this.trans_le (hε'1 w)).trans hlt1)
    · exact ⟨b, hb0, hbT⟩
  set β : Lˣ := Units.mk0 b' hb'0 with hβ
  set z := IdeleGroup.unitEmbedding (𝓞 L) L β * y with hz
  have hzfin : ∀ w, ideleFinAt z w = algebraMap L (w.adicCompletion L) b' * ideleFinAt y w := fun w => by
    rw [hz, ideleFinAt_mul, ideleFinAt_unitEmbedding]; rfl
  have hzT : ∀ w ∈ T, Valued.v (ideleFinAt z w - 1) < ε' w := fun w hw => by
    rw [hzfin]; exact hb' w hw
  have hz1 : ∀ w ∈ T, Valued.v (ideleFinAt z w) = 1 := fun w hw =>
    val_eq_one_of_sub_one_le Valued.v hlt1 ((hzT w hw).le.trans (hε'1 w))
  refine ⟨β, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := hw
    have hvb : v = primeBelow K L w := HeightOneSpectrum.ext hvw
    exact hz1 w ((hTmem w).2 (hvb ▸ hv))
  · intro v hv
    set u : (w : HeightOneSpectrum (𝓞 L)) → (w.adicCompletion L)ˣ :=
      fun w => Units.mk0 (ideleFinAt z w) (ideleFinAt_ne_zero z w) with hu
    set z₁ := prodOfAdic T u with hz₁
    have hz1fin : ∀ w, ideleFinAt z₁ w = if w ∈ T then ideleFinAt z w else 1 :=
      fun w => ideleFinAt_prodOfAdic T u w
    have hz2 : ∀ w, primeBelow K L w = v → ideleFinAt (z * z₁⁻¹) w = 1 := by
      intro w hw
      have hwT : w ∈ T := (hTmem w).2 (hw ▸ hv)
      rw [ideleFinAt_mul, ideleFinAt_inv, hz1fin, if_pos hwT]
      exact mul_inv_cancel₀ (ideleFinAt_ne_zero z w)
    have hz1W : z₁ ∈ ideleNormMap K L ⁻¹' A := by
      refine hbox z₁ (ideleInfAt_prodOfAdic T u) ?_ ?_ ?_ ?_
      · intro w; rw [hz1fin]
        split_ifs with h
        · exact (hz1 w h).le
        · simp
      · intro w; rw [ideleFinAt_inv, hz1fin]
        split_ifs with h
        · rw [map_inv₀, hz1 w h, inv_one]
        · simp
      · intro w _; rw [hz1fin]
        split_ifs with h
        · exact (hzT w h).trans_le (hε'2 w)
        · rw [sub_self, map_zero]; exact zero_lt_iff.2 (hε w)
      · intro w _; rw [ideleFinAt_inv, hz1fin]
        split_ifs with h
        · have := val_inv_sub_one_le Valued.v (γ := Valued.v (ideleFinAt z w - 1))
            (((hzT w h).trans_le (hε'1 w)).trans hlt1) le_rfl
          exact this.trans_lt ((hzT w h).trans_le (hε'2 w))
        · rw [inv_one, sub_self, map_zero]; exact zero_lt_iff.2 (hε w)
    have hN : ideleNormMap K L z = ideleNormMap K L (z * z₁⁻¹) * ideleNormMap K L z₁ := by
      rw [← map_mul]; congr 1; group
    have hn := ideleFinAt_ideleNormMap_eq_one (K := K) L v (z * z₁⁻¹) hz2
    rw [hN, ideleFinAt_mul, hn, one_mul]
    exact (hz1W : ideleNormMap K L z₁ ∈ A) v hv

variable (hR : IdelicReciprocity K) [IsAbelianGalois K L]

/-- The kernel of $\psi_{L/K}$ on $I^{S(\mathfrak m)}$ is contained in $P_\mathfrak m\cdot\mathrm{Nm}(I_L^{S(\mathfrak m)})$
(Remark 5.8). -/
theorem ker_artinMap_le_of_idelic (m : Modulus K)
    (hm : ∀ v, v ∉ m.finiteSupport → v ∈ unramifiedPrimes K L) (hW : idelesW m ≤ (idelicArtinOf hR L).ker)
    (hinf : ∀ w ∈ m.infinite, InfinitePlace.RamifiesIn L w) :
    (artinMap L m.finiteSupport).ker ≤
      (rayPrincipal m ⊔ normIdeals K L m.finiteSupport).subgroupOf (sIdeals m.finiteSupport) := by
  classical
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hg' : artinTot L (g : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = 1 := hg
  rw [Subgroup.mem_subgroupOf]
  have hfin : m.finiteSupport.Finite := Ideal.finite_factors m.finite_ne_bot
  obtain ⟨x, hx, hxg⟩ := exists_mem_idelesMod_ideleToIdeal m (g : (FractionalIdeal (𝓞 K)⁰ K)ˣ) g.2
  have hφ : idelicArtinOf hR L x = 1 := by
    rw [idelicArtinOf_eq_artinTot hR L m hm hW x hx, hxg]; exact hg'
  have hxN : x ∈ ideleNormGroup L := by
    rw [← (idelicArtinOf_spec hR L).2.2.2]; exact MonoidHom.mem_ker.mpr hφ
  obtain ⟨p, ⟨c, rfl⟩, r, ⟨y, rfl⟩, hpr⟩ := Subgroup.mem_sup.mp hxN
  obtain ⟨β, hβ1, hβ2⟩ := exists_mul_close_above L y m.finiteSupport hfin (hfin.toFinset.sup m.ord)
  set z := IdeleGroup.unitEmbedding (𝓞 L) L β * y with hz
  set c' : Kˣ := c * (Units.map (Algebra.norm K : L →* K) β)⁻¹ with hc'
  have hNz : ideleNormMap K L z = IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (Algebra.norm K : L →* K) β) *
      ideleNormMap K L y := by
    rw [hz, map_mul, (ideleNormMap_comm (K := K) L).1]
  have hxz : x = IdeleGroup.unitEmbedding (𝓞 K) K c' * ideleNormMap K L z := by
    rw [hNz, hc', map_mul, map_inv, ← hpr]
    simp [mul_assoc]
  have hNzm : ideleNormMap K L z ∈ idelesMod m := by
    refine ⟨fun w hw => isPosAt_ideleNormMap L z w (hinf w hw), fun v hv => ?_⟩
    refine (hβ2 v hv).trans (WithZero.exp_le_exp.mpr ?_)
    have : m.ord v ≤ hfin.toFinset.sup m.ord := Finset.le_sup (f := m.ord) (hfin.mem_toFinset.mpr hv)
    omega
  have hc'm : c' ∈ congruenceSubgroup m := by
    rw [mem_congruenceSubgroup_iff_mem_idelesMod]
    have : IdeleGroup.unitEmbedding (𝓞 K) K c' = x * (ideleNormMap K L z)⁻¹ := by
      rw [hxz]; group
    rw [this]
    exact mul_mem hx (inv_mem hNzm)
  have hzs : ideleToIdeal L z ∈ sIdeals (primesAbove K L m.finiteSupport) := by
    intro w hw
    rw [count_ideleToIdeal, hβ1 w ⟨primeBelow K L w, hw, rfl⟩, WithZero.log_one]
    simp
  have hmem : (g : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ rayPrincipal m ⊔ normIdeals K L m.finiteSupport := by
    refine Subgroup.mem_sup.mpr ⟨toPrincipalIdeal (𝓞 K) K c', ⟨c', hc'm, rfl⟩,
      idealNorm K L (ideleToIdeal L z), ⟨_, hzs, rfl⟩, ?_⟩
    rw [← (ideleNormMap_comm (K := K) L).2, ← ideleToIdeal_unitEmbedding, ← map_mul, ← hxz, hxg]
  exact hmem

variable (K) in
/-- **Theorem 3.5 (the reciprocity law, ideal-theoretic form) from Theorem 5.3 (idelic form)** (Milne, *CFT*,
Chapter V, Remark 5.8, the reciprocity half): every finite abelian extension has a defining modulus. -/
@[kb "milne2020cft" "Ch. V, Remark 5.8 (Thm. 5.3 ⇒ Thm. 3.5)"]
theorem reciprocityLaw_ideal_of_idelic (hR : IdelicReciprocity K) : ReciprocityLaw K := by
  refine ⟨fun L _ _ _ _ => ?_⟩
  obtain ⟨m, hsupp, hinf, hW⟩ := exists_modulus_idelesW_le_ker hR L
  have hm : ∀ v, v ∉ m.finiteSupport → v ∈ unramifiedPrimes K L := fun v hv => by
    by_contra h
    exact hv (hsupp ▸ h)
  exact ⟨m, ⟨hsupp, fun w => (hinf w), artinMap_surjective_of_idelic hR L m hm hW,
    le_antisymm (ker_artinMap_le_of_idelic L hR m hm hW fun w hw => (hinf w).mp hw)
      (le_ker_artinMap_of_idelic hR L m hm hW)⟩⟩

end NumberFieldKB.MilneCFT
