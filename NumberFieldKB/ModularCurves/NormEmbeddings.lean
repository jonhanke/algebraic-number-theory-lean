import NumberFieldKB.ModularCurves.RiemannHurwitz
import NumberFieldKB.ModularCurves.PlaceNorm
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Norms as products over embeddings, and orders of norms at Tau Ceti's places

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. I, §4 and Ch. V, §2. Two inputs to the count of the fibres of
$j : X_0(N) \to X_0(1)$ (`FibreCount.lean`):

* the bridge between Tau Ceti's places (`TauCeti.Place`) and Milne's (`MilneEC.PrimeDivisor`) for restriction and
  relative degree (`toPrimeDivisor_restrict`, `relativeDegree_eq_residueDeg`), and through it the order of a norm
  $\operatorname{ord}_P(N_{K/F} z) = \sum_{P' \mid P} f(P')\operatorname{ord}_{P'}(z)$ for Tau Ceti's places
  (`ord_norm_place`, from Milne's `ord_norm`);
* for a finite separable $K/F$ and $[K : F]$ distinct $F$-embeddings $\sigma_i : K \to L$ into a field,
  $N_{K/F}(z) = \prod_i \sigma_i(z)$ in $L$ (`algebraMap_norm_eq_prod`).
-/

open TauCeti NumberFieldKB.MilneEC

noncomputable section

namespace NumberFieldKB.ModularCurves

section Bridge

variable {k F K : Type*} [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K]
  [IsScalarTower k F K] [FiniteDimensional F K] [Algebra.IsSeparable F K]

/-- A Milne prime divisor as a Tau Ceti place, with no function-field hypothesis: its normalized valuation. -/
def placeOfPrimeDivisor (Q : PrimeDivisor k K) : Place k K where
  valuation := Q.valuation
  valuation_surjective := by
    unfold PrimeDivisor.valuation
    have := Q.isDVR
    exact IsDedekindDomain.HeightOneSpectrum.valuation_surjective K _
  isTrivialOn := by
    refine ⟨fun c hc => ?_⟩
    have h1 : Q.valuation (algebraMap k K c) ≤ 1 := (Q.mem_O_iff_valuation_le_one _).1 (Q.algebraMap_mem c)
    have h2 : Q.valuation (algebraMap k K c⁻¹) ≤ 1 :=
      (Q.mem_O_iff_valuation_le_one _).1 (Q.algebraMap_mem c⁻¹)
    have hprod : Q.valuation (algebraMap k K c) * Q.valuation (algebraMap k K c⁻¹) = 1 := by
      rw [← map_mul, ← map_mul]; simp [hc]
    refine le_antisymm h1 (not_lt.1 fun hlt => hprod.not_lt ?_)
    calc Q.valuation (algebraMap k K c) * Q.valuation (algebraMap k K c⁻¹)
        ≤ Q.valuation (algebraMap k K c) * 1 := by gcongr
      _ = Q.valuation (algebraMap k K c) := mul_one _
      _ < 1 := hlt

theorem integers_placeOfPrimeDivisor (Q : PrimeDivisor k K) : (placeOfPrimeDivisor Q).integers = Q.O := by
  rw [Q.O_eq_valuationSubring]; rfl

theorem toPrimeDivisor_placeOfPrimeDivisor (Q : PrimeDivisor k K) :
    (placeOfPrimeDivisor Q).toPrimeDivisor = Q :=
  PrimeDivisor.ext_O (integers_placeOfPrimeDivisor Q)

theorem toPrimeDivisor_injective : Function.Injective (Place.toPrimeDivisor (k := k) (K := K)) :=
  fun _ _ h => Place.integers_injective (congrArg PrimeDivisor.O h)

/-- Finrank of residue fields only depends on the valuation ring up to equality. -/
theorem finrank_residue_congr (A : ValuationSubring F) (P' : Place k K)
    (hA : A = (P'.restrict k F).integers) (g : A →+* P'.integers) (hgl : IsLocalHom g)
    (hg : ∀ x : A, ((g x : P'.integers) : K) = algebraMap F K (x : F)) :
    (letI := (IsLocalRing.ResidueField.map g).toAlgebra;
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField P'.integers)) =
      Place.relativeDegree k F P' := by
  subst hA
  have : g = algebraMap (P'.restrict k F).integers P'.integers :=
    RingHom.ext fun x => Subtype.ext (by rw [hg, Place.coe_algebraMap_integers])
  subst this
  rw [Place.relativeDegree_def]
  have hinst : (IsLocalRing.ResidueField.map (algebraMap (P'.restrict k F).integers P'.integers)).toAlgebra =
      (inferInstance : Algebra (P'.restrict k F).ResidueField P'.ResidueField) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  exact congrArg (fun A : Algebra (P'.restrict k F).ResidueField P'.ResidueField =>
    @Module.finrank _ _ _ _ A.toModule) hinst

/-- Restriction of Tau Ceti's places is Milne's `comap`. -/
theorem toPrimeDivisor_restrict (P' : Place k K) :
    (P'.restrict k F).toPrimeDivisor = P'.toPrimeDivisor.comap (K := F) := by
  apply PrimeDivisor.ext_O
  ext x
  rw [Place.O_toPrimeDivisor, PrimeDivisor.mem_comap_O, Place.O_toPrimeDivisor,
    Place.mem_integers_restrict_iff]

/-- Tau Ceti's relative degree is Milne's residue degree. -/
theorem relativeDegree_eq_residueDeg (P' : Place k K) :
    Place.relativeDegree k F P' = P'.toPrimeDivisor.residueDeg (K := F) := by
  have : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
  refine (finrank_residue_congr (F := F) (P'.toPrimeDivisor.comap (K := F)).O P' ?_
    (P'.toPrimeDivisor.comapHom (K := F)) (inferInstanceAs (IsLocalHom (P'.toPrimeDivisor.comapHom (K := F))))
    fun x => rfl).symm
  rw [← Place.O_toPrimeDivisor, ← toPrimeDivisor_restrict (F := F) P']

/-- **The order of a norm** at Tau Ceti's places: $\operatorname{ord}_P(N_{K/F} z) =
\sum_{P' \mid P} f(P' \mid P)\operatorname{ord}_{P'}(z)$. -/
theorem ord_norm_place (P : Place k F) {z : K} (hz : z ≠ 0) :
    P.ord (Algebra.norm F z) =
      ∑ P' ∈ fibre (F' := K) P, (Place.relativeDegree k F P' : ℤ) * P'.ord z := by
  classical
  let : Algebra P.toPrimeDivisor.O K := ((algebraMap F K).comp (algebraMap P.toPrimeDivisor.O F)).toAlgebra
  have : IsScalarTower P.toPrimeDivisor.O F K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let S : Finset (PrimeDivisor k K) := (fibre (F' := K) P).map ⟨Place.toPrimeDivisor, toPrimeDivisor_injective⟩
  have hS : ∀ Q, Q ∈ S ↔ Q.comap (K := F) = P.toPrimeDivisor := by
    intro Q
    constructor
    · intro hQ
      obtain ⟨P', hP', rfl⟩ := Finset.mem_map.1 hQ
      show P'.toPrimeDivisor.comap (K := F) = _
      rw [← toPrimeDivisor_restrict, mem_fibre.1 hP']
    · intro hQ
      refine Finset.mem_map.2 ⟨placeOfPrimeDivisor Q, mem_fibre.2 ?_, toPrimeDivisor_placeOfPrimeDivisor Q⟩
      apply toPrimeDivisor_injective
      rw [toPrimeDivisor_restrict, toPrimeDivisor_placeOfPrimeDivisor, hQ]
  have h := ord_norm P.toPrimeDivisor S hS hz
  rw [Place.ord_toPrimeDivisor] at h
  rw [h, Finset.sum_map]
  refine Finset.sum_congr rfl fun P' _ => ?_
  simp only [Function.Embedding.coeFn_mk, Place.ord_toPrimeDivisor, relativeDegree_eq_residueDeg]

end Bridge

section NormProd

variable {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
  [FiniteDimensional F K] [Algebra.IsSeparable F K]

/-- **The norm is the product of the conjugates**: for $[K : F]$ distinct $F$-embeddings $\sigma_i : K \to L$,
$N_{K/F}(z) = \prod_i \sigma_i(z)$. -/
theorem algebraMap_norm_eq_prod {ι : Type*} [Fintype ι] (σ : ι → (K →ₐ[F] L)) (hσ : Function.Injective σ)
    (hcard : Fintype.card ι = Module.finrank F K) (z : K) :
    algebraMap F L (Algebra.norm F z) = ∏ i, σ i z := by
  let Ω := AlgebraicClosure L
  let ι' : L →ₐ[F] Ω := IsScalarTower.toAlgHom F L Ω
  have hinj : Function.Injective ι' := (algebraMap L Ω).injective
  have h := Algebra.norm_eq_prod_embeddings F Ω z
  let e : ι → (K →ₐ[F] Ω) := fun i => ι'.comp (σ i)
  have he : Function.Injective e := fun i j hij => hσ (AlgHom.ext fun x => hinj (by
    have := DFunLike.congr_fun hij x
    simpa [e] using this))
  have hc : Fintype.card ι = Fintype.card (K →ₐ[F] Ω) := by
    rw [hcard, AlgHom.card]
  have hb : Function.Bijective e := (Fintype.bijective_iff_injective_and_card e).2 ⟨he, hc⟩
  apply (algebraMap L Ω).injective
  have h2 : algebraMap L Ω (algebraMap F L (Algebra.norm F z)) = algebraMap F Ω (Algebra.norm F z) :=
    (IsScalarTower.algebraMap_apply F L Ω _).symm
  rw [h2, h, map_prod]
  exact (Fintype.prod_bijective e hb _ _ fun i => rfl).symm

end NormProd

end NumberFieldKB.ModularCurves
