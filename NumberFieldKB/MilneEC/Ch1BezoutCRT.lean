import NumberFieldKB.MilneEC.Ch1BezoutDefs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Bezout's theorem: the affine intersection as a sum of local intersection numbers

Part of the proof of Milne, *Elliptic Curves*, Theorem I.1.18 (Bezout), after Fulton 1969, §2.9,
Corollary 4: over an algebraically closed field, if $K[X, Y]/(f, g)$ is finite dimensional then the
common zeros of `f` and `g` are finitely many and
$\dim_K K[X, Y]/(f, g) = \sum_p \dim_K \mathcal O_p/(f, g)$.
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

theorem exists_algEquiv_localization_quotient {R : Type*} [CommRing R] (I : Ideal R)
    (Q : Ideal (R ⧸ I)) [Q.IsPrime] (P : Ideal R) [P.IsPrime]
    (hP : Q.comap (Ideal.Quotient.mk I) = P) :
    Nonempty (Localization.AtPrime Q ≃ₐ[R ⧸ I]
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))) := by
  subst hP
  have hsub : Algebra.algebraMapSubmonoid (R ⧸ I) (Q.comap (Ideal.Quotient.mk I)).primeCompl
      = Q.primeCompl :=
    Submonoid.map_comap_eq_of_surjective Ideal.Quotient.mk_surjective Q.primeCompl
  have : IsLocalization Q.primeCompl
      (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap R (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I))))) := by
    rw [← hsub]; infer_instance
  exact ⟨IsLocalization.algEquiv Q.primeCompl _ _⟩

theorem finrank_localization_quotient {R : Type*} [CommRing R] [Algebra K R] (I : Ideal R)
    (Q : Ideal (R ⧸ I)) [Q.IsPrime] (P : Ideal R) [P.IsPrime]
    (hP : Q.comap (Ideal.Quotient.mk I) = P) :
    Module.finrank K (Localization.AtPrime Q) =
      Module.finrank K (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) := by
  obtain ⟨e⟩ := exists_algEquiv_localization_quotient I Q P hP
  have : IsScalarTower K (R ⧸ I) (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply K R _ c, IsScalarTower.algebraMap_apply R (R ⧸ I) _,
        ← IsScalarTower.algebraMap_apply K R (R ⧸ I)]
  exact LinearEquiv.finrank_eq (e.restrictScalars K).toLinearEquiv

theorem algebraMap_mk_eq_zero_iff {R : Type*} [CommRing R] (I : Ideal R)
    (Q : Ideal (R ⧸ I)) [Q.IsPrime] (P : Ideal R) [P.IsPrime]
    (hP : Q.comap (Ideal.Quotient.mk I) = P) (q : R) :
    algebraMap (R ⧸ I) (Localization.AtPrime Q) (Ideal.Quotient.mk I q) = 0 ↔
      Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime P)))
        (algebraMap R (Localization.AtPrime P) q) = 0 := by
  obtain ⟨e⟩ := exists_algEquiv_localization_quotient I Q P hP
  rw [← map_eq_zero_iff e e.injective, e.commutes]
  exact Iff.rfl

theorem finrank_eq_sum_localization {A : Type*} [CommRing A] [Algebra K A] [Module.Finite K A]
    [Fintype (MaximalSpectrum A)] :
    Module.finrank K A =
      ∑ m : MaximalSpectrum A, Module.finrank K (Localization.AtPrime m.asIdeal) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  let e := (MaximalSpectrum.toPiLocalizationEquiv A).restrictScalars K
  have : ∀ m : MaximalSpectrum A, Module.Finite K (Localization.AtPrime m.asIdeal) := fun m =>
    Module.Finite.of_surjective (IsScalarTower.toAlgHom K A _).toLinearMap
      (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

theorem pointIdeal_eq_vanishingIdeal (p : K × K) :
    pointIdeal p = vanishingIdeal K {![p.1, p.2]} := by
  ext r
  simp [pointIdeal]

theorem pointIdeal_isMaximal [IsAlgClosed K] (p : K × K) : (pointIdeal p).IsMaximal :=
  (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).mpr
    ⟨_, pointIdeal_eq_vanishingIdeal p⟩

theorem exists_point_of_isMaximal [IsAlgClosed K] (M : Ideal (MvPolynomial (Fin 2) K))
    [M.IsMaximal] : ∃ p : K × K, M = pointIdeal p := by
  obtain ⟨x, hx⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).mp ‹M.IsMaximal›
  refine ⟨(x 0, x 1), ?_⟩
  have : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
  rw [pointIdeal_eq_vanishingIdeal]
  simp only [this]
  exact hx

theorem pointIdeal_injective : Function.Injective (pointIdeal (K := K)) := by
  intro p q h
  have h1 : (X 0 - C p.1 : MvPolynomial (Fin 2) K) ∈ pointIdeal p := by simp [pointIdeal]
  have h2 : (X 1 - C p.2 : MvPolynomial (Fin 2) K) ∈ pointIdeal p := by simp [pointIdeal]
  rw [h] at h1 h2
  simp [pointIdeal, sub_eq_zero] at h1 h2
  exact Prod.ext h1.symm h2.symm

theorem span_le_pointIdeal_iff (f g : MvPolynomial (Fin 2) K) (p : K × K) :
    Ideal.span {f, g} ≤ pointIdeal p ↔ p ∈ commonZeros f g := by
  simp [Ideal.span_le, commonZeros, pointIdeal, evalAt, Set.insert_subset_iff]

theorem exists_point_of_maximal [IsAlgClosed K] (f g : MvPolynomial (Fin 2) K)
    (m : MaximalSpectrum (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g})) :
    ∃ p ∈ commonZeros f g, m.asIdeal.comap (Ideal.Quotient.mk _) = pointIdeal p := by
  have hm := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span {f, g}))
    Ideal.Quotient.mk_surjective (K := m.asIdeal) (H := m.isMaximal)
  obtain ⟨p, hp⟩ := exists_point_of_isMaximal (K := K) (m.asIdeal.comap (Ideal.Quotient.mk _))
  refine ⟨p, ?_, hp⟩
  rw [← span_le_pointIdeal_iff, ← hp]
  intro x hx
  exact Ideal.mem_comap.mpr (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact zero_mem _)

theorem exists_maximal_of_point [IsAlgClosed K] (f g : MvPolynomial (Fin 2) K) (p : K × K)
    (hp : p ∈ commonZeros f g) :
    ∃ m : MaximalSpectrum (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g}),
      m.asIdeal.comap (Ideal.Quotient.mk _) = pointIdeal p := by
  have hle := (span_le_pointIdeal_iff f g p).mpr hp
  have hc : ((pointIdeal p).map (Ideal.Quotient.mk (Ideal.span {f, g}))).comap
      (Ideal.Quotient.mk (Ideal.span {f, g})) = pointIdeal p := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hle
  have hmax := pointIdeal_isMaximal p
  have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {f, g})) ≤ pointIdeal p := by
    rwa [Ideal.mk_ker]
  have := Ideal.IsMaximal.map_of_surjective_of_ker_le (f := Ideal.Quotient.mk (Ideal.span {f, g}))
    Ideal.Quotient.mk_surjective hker
  exact ⟨⟨_, this⟩, hc⟩

theorem map_span_pair_eq (f g : MvPolynomial (Fin 2) K) (p : K × K) :
    Ideal.span {algebraMap _ (LocalRingAt p) f, algebraMap _ (LocalRingAt p) g} =
      (Ideal.span {f, g}).map (algebraMap _ (LocalRingAt p)) := by
  rw [Ideal.map_span, Set.image_pair]

theorem mem_span_of_forall_localQuotient [IsAlgClosed K] (f g q : MvPolynomial (Fin 2) K)
    (hfin : Module.Finite K (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g}))
    (hq : ∀ p ∈ commonZeros f g,
      Ideal.Quotient.mk _ (algebraMap _ (LocalRingAt p) q) = (0 : LocalQuotientAt f g p)) :
    q ∈ Ideal.span {f, g} := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply MaximalSpectrum.toPiLocalization_injective (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g})
  funext m
  obtain ⟨p, hp, hpm⟩ := exists_point_of_maximal f g m
  have := m.isMaximal.isPrime
  have h := (algebraMap_mk_eq_zero_iff (Ideal.span {f, g}) m.asIdeal (pointIdeal p) hpm q).mpr
    (by rw [← map_span_pair_eq]; exact hq p hp)
  rw [map_zero]
  exact h

theorem finrank_quotient_eq_sum_numAt [IsAlgClosed K] (f g : MvPolynomial (Fin 2) K)
    (hfin : Module.Finite K (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g})) :
    ∃ S : Finset (K × K), (S : Set (K × K)) = commonZeros f g ∧
      Module.finrank K (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g}) = ∑ p ∈ S, numAt f g p := by
  classical
  have : Finite (MaximalSpectrum (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g})) := by
    have := IsArtinianRing.of_finite K (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g})
    infer_instance
  have : Fintype (MaximalSpectrum (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g})) :=
    Fintype.ofFinite _
  have hex : ∀ p : commonZeros f g, ∃ m : MaximalSpectrum
      (MvPolynomial (Fin 2) K ⧸ Ideal.span {f, g}),
      m.asIdeal.comap (Ideal.Quotient.mk _) = pointIdeal p.1 :=
    fun p => exists_maximal_of_point f g p.1 p.2
  choose m hm using hex
  have hinj : Function.Injective m := by
    intro p q h
    apply Subtype.ext
    apply pointIdeal_injective
    rw [← hm p, ← hm q, h]
  have hsurj : Function.Surjective m := by
    intro n
    obtain ⟨p, hp, hpn⟩ := exists_point_of_maximal f g n
    refine ⟨⟨p, hp⟩, ?_⟩
    apply MaximalSpectrum.ext
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rw [hm, hpn]
  have : Finite (commonZeros f g) := Finite.of_injective m hinj
  have : Fintype (commonZeros f g) := Fintype.ofFinite _
  have hS : (commonZeros f g).Finite := Set.toFinite _
  refine ⟨hS.toFinset, hS.coe_toFinset, ?_⟩
  rw [finrank_eq_sum_localization (K := K),
    Finset.sum_subtype hS.toFinset (p := (· ∈ commonZeros f g)) (by simp) (fun p => numAt f g p)]
  refine (Fintype.sum_bijective m ⟨hinj, hsurj⟩ _ _ ?_).symm
  intro p
  have := (m p).isMaximal.isPrime
  rw [finrank_localization_quotient (K := K) (Ideal.span {f, g}) (m p).asIdeal (pointIdeal p.1)
    (hm p)]
  unfold numAt LocalQuotientAt
  rw [map_span_pair_eq]

end NumberFieldKB.MilneEC.Bezout
