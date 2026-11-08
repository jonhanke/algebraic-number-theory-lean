import NumberFieldKB.Chebotarev.Basic
import NumberFieldKB.Chebotarev.FrobeniusNF
import NumberFieldKB.Chebotarev.FrobeniusEField

/-!
# Frobenius classes of primes of a number field

The number-field statements about Frobenius classes, proved from the abstract results of
(`Frobenius.lean`, `FrobeniusNF.lean`, `FrobeniusDeuring.lean`, `FrobeniusEField.lean`): finitely many primes ramify,
split completely = trivial Frobenius, Frobenius under restriction (Milne 8.13), and Deuring's count with
$E = L^{\langle\sigma\rangle}$.
-/

open NumberField IsDedekindDomain Filter Topology Set

namespace NumberFieldKB.Chebotarev

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section Frobenius

/-- Helper for `finite_compl_unramifiedPrimes`: a prime of `𝓞 K` that is ramified in `L` contains the
discriminant of `L` (as an integer). -/
theorem mem_of_not_isUnramifiedIn (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ Algebra.IsUnramifiedIn (𝓞 L) 𝔭.asIdeal) :
    algebraMap ℤ (𝓞 K) (NumberField.discr L) ∈ 𝔭.asIdeal := by
  unfold Algebra.IsUnramifiedIn at h
  push Not at h
  obtain ⟨Q, hQ, hQo, hQu⟩ := h
  haveI := hQ
  haveI := hQo
  have hQz : ¬ Algebra.IsUnramifiedAt ℤ Q := fun H =>
    hQu (Algebra.IsUnramifiedAt.of_restrictScalars ℤ (A := 𝓞 K) Q)
  have hQm : Q.IsMaximal := hQ.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q)
  obtain ⟨p, hp : _ = Ideal.span _⟩ := IsPrincipalIdealRing.principal (Q.under ℤ)
  have hp0 : p ≠ 0 := fun hp0 => Ideal.IsMaximal.ne_bot_of_isIntegral_int _
    (Ideal.eq_bot_of_under_eq_bot (hp.trans (by simp [hp0])))
  have hpp : Prime p := by rw [← Ideal.span_singleton_prime hp0, ← hp]; infer_instance
  have hdvd : p ∣ NumberField.discr L := by
    by_contra hnd
    have := (NumberField.not_dvd_discr_iff_forall_liesOver L (𝓞 L) hpp).mp hnd Q hQm
      ⟨hp.symm⟩
    exact hQz this
  obtain ⟨c, hc⟩ := hdvd
  have hpQ : p ∈ Q.under ℤ := by rw [hp]; exact Ideal.mem_span_singleton_self p
  have hp𝔭 : algebraMap ℤ (𝓞 K) p ∈ 𝔭.asIdeal := by
    have h1 : algebraMap ℤ (𝓞 K) p ∈ Q.under (𝓞 K) := by
      rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hpQ
    rwa [← Ideal.LiesOver.over (p := 𝔭.asIdeal) (P := Q)] at h1
  rw [hc, map_mul]
  exact Ideal.mul_mem_right _ _ hp𝔭

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- *Proved* (C4 + C5). **Only finitely many primes of `K` ramify in `L`** (they divide the relative discriminant;
Mathlib has the absolute version `NumberField.not_dvd_discr_iff_isUnramifiedIn`). -/
theorem finite_compl_unramifiedPrimes : (unramifiedPrimes K L)ᶜ.Finite := by
  have hd : (Ideal.span {algebraMap ℤ (𝓞 K) (NumberField.discr L)} : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact fun h => NumberField.discr_ne_zero L
      ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))).mp h)
  refine (Ideal.finite_factors hd).subset ?_
  intro 𝔭 h𝔭
  have := mem_of_not_isUnramifiedIn K L 𝔭 h𝔭
  exact (Ideal.dvd_span_singleton).mpr this

/-- **Unramifiedness descends along a tower**: a prime of `K` unramified in `M ⊇ L` is unramified in `L`. -/
theorem unramifiedPrimes_subset_of_tower (M : Type) [Field M] [NumberField M] [Algebra K M]
    [Algebra L M] [IsScalarTower K L M] [IsGalois K M]
    {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ unramifiedPrimes K M) : 𝔭 ∈ unramifiedPrimes K L := by
  intro Q hQ hQo
  obtain ⟨R, -, hR, hRo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Q (⊥ : Ideal (𝓞 M))
    (by
      intro x hx
      have : x = 0 := (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 M)) (by simpa using hx)
      simp [this])
  haveI := hR
  haveI : R.LiesOver Q := ⟨hRo.symm⟩
  haveI : R.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans R Q 𝔭.asIdeal
  haveI : Algebra.IsUnramifiedAt (𝓞 K) R := h𝔭 R hR inferInstance
  exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) Q R

/-- *Proved* (C4 + C5). **Split completely = unramified with trivial Frobenius.** -/
theorem splitPrimes_eq_frobSet_one : splitPrimes K L = frobSet K L (ConjClasses.mk 1) := by
  ext 𝔭
  constructor
  · intro h
    have hunr : 𝔭 ∈ unramifiedPrimes K L := by
      intro Q hQ hQo
      haveI := hQ
      haveI := hQo
      haveI := finite_quotient_of_ne_bot Q (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q)
      exact Ideal.ramificationIdx_eq_one_iff.mp (h ⟨Q, hQ, hQo⟩).1
    refine ⟨hunr, ?_⟩
    set Q : 𝔭.asIdeal.primesOver (𝓞 L) := Classical.arbitrary _
    rw [frobClass_eq_mk_frobAt K L 𝔭 Q, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left]
    haveI := Q.2.1
    haveI := Q.2.2
    haveI := finite_quotient_of_ne_bot Q.1 (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q.1)
    haveI : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := hunr Q.1 Q.2.1 Q.2.2
    exact (arithFrobAt_eq_one_iff_nf Q.1).mpr (h Q).2
  · rintro ⟨hunr, hcl⟩ Q
    have hQ := Q.2.1
    have hQo := Q.2.2
    haveI := hQ
    haveI := hQo
    haveI := finite_quotient_of_ne_bot Q.1 (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q.1)
    haveI hu : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := hunr Q.1 Q.2.1 Q.2.2
    refine ⟨Ideal.ramificationIdx_eq_one_iff.mpr hu, ?_⟩
    rw [frobClass_eq_mk_frobAt K L 𝔭 Q, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left] at hcl
    exact (arithFrobAt_eq_one_iff_nf Q.1).mp hcl

end Frobenius

section Restriction

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (M : Type) [Field M] [NumberField M] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M] [IsGalois K M]

/-- Unramifiedness of the restriction of an unramified prime to a Galois subextension. -/
theorem ramificationIdxIn_under_eq_one_of_tower (𝔓 : Ideal (𝓞 M)) [𝔓.IsPrime] [Finite (𝓞 M ⧸ 𝔓)]
    [Algebra.IsUnramifiedAt (𝓞 K) 𝔓] :
    ((𝔓.under (𝓞 L)).under (𝓞 K)).ramificationIdxIn (𝓞 L) = 1 := by
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx ((𝔓.under (𝓞 L)).under (𝓞 K)) (𝔓.under (𝓞 L))
    Gal(L/K)]
  have h1 : 𝔓.ramificationIdx (𝓞 K) = 1 := Ideal.ramificationIdx_eq_one 𝔓 (𝓞 K)
  have := Ideal.ramificationIdx_below_dvd (R := 𝓞 K) (S := 𝓞 L) (T := 𝓞 M) (𝔓.under (𝓞 L)) 𝔓
  rw [h1] at this
  exact Nat.dvd_one.mp this

/-- Frobenius and restriction to a Galois subextension, for a separate type `L`. -/
theorem restrictNormalHom_arithFrobAt_of_tower (𝔓 : Ideal (𝓞 M)) [𝔓.IsPrime] [Finite (𝓞 M ⧸ 𝔓)]
    [Algebra.IsUnramifiedAt (𝓞 K) 𝔓] :
    AlgEquiv.restrictNormalHom L (arithFrobAt (𝓞 K) Gal(M/K) 𝔓) =
      arithFrobAt (𝓞 K) Gal(L/K) (𝔓.under (𝓞 L)) := by
  have : Algebra.HasSeparableResidueFieldsAt (𝓞 K) (𝓞 L) ((𝔓.under (𝓞 L)).under (𝓞 K)) := by
    have : Finite (𝓞 K ⧸ (𝔓.under (𝓞 L)).under (𝓞 K)) := finite_quotient_under _
    have : ((𝔓.under (𝓞 L)).under (𝓞 K)).IsMaximal := isMaximal_under_of_finite _
    infer_instance
  have : Finite (𝓞 L ⧸ 𝔓.under (𝓞 L)) := finite_quotient_under 𝔓
  refine map_arithFrobAt_eq (A := 𝓞 K) (B := 𝓞 L) (C := 𝓞 M) (G := Gal(M/K)) (G' := Gal(L/K))
    (AlgEquiv.restrictNormalHom L) ?_ 𝔓 (ramificationIdxIn_under_eq_one_of_tower K L M 𝔓)
  intro g b
  apply Subtype.ext
  change algebraMap L M ((AlgEquiv.restrictNormalHom L g) (b : L)) = g (algebraMap L M (b : L))
  exact AlgEquiv.restrictNormal_commutes g L (b : L)

/-- *Proved* (C4 + C5). **Frobenius in quotients** (Milne 8.13 [unverified locator]): for $K \subseteq L \subseteq M$
with $M/K$ and $L/K$ Galois and $\mathfrak p$ unramified in `M`, $\mathrm{Frob}_{L/K}(\mathfrak p)$ is the image of
$\mathrm{Frob}_{M/K}(\mathfrak p)$ under restriction $\mathrm{Gal}(M/K) \to \mathrm{Gal}(L/K)$. -/
theorem frobClass_restrict {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ unramifiedPrimes K M) :
    frobClass K L 𝔭 = (frobClass K M 𝔭).map (AlgEquiv.restrictNormalHom L) := by
  set Q : 𝔭.asIdeal.primesOver (𝓞 M) := Classical.arbitrary _ with hQ
  haveI := Q.2.1
  haveI := Q.2.2
  haveI := isMaximal_of_mem_primesOver K M 𝔭 Q
  haveI : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := h𝔭 Q.1 Q.2.1 Q.2.2
  haveI : Finite (𝓞 M ⧸ Q.1) :=
    finite_quotient_of_ne_bot Q.1 (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q.1)
  let Q' : 𝔭.asIdeal.primesOver (𝓞 L) := ⟨Q.1.under (𝓞 L), inferInstance, inferInstance⟩
  rw [frobClass_eq_mk_frobAt K L 𝔭 Q', frobClass_eq_mk_frobAt K M 𝔭 Q]
  change _ = ConjClasses.mk (AlgEquiv.restrictNormalHom L (frobAt K M 𝔭 Q))
  congr 1
  haveI := Q'.2.1
  haveI := isMaximal_of_mem_primesOver K L 𝔭 Q'
  unfold frobAt
  exact (restrictNormalHom_arithFrobAt_of_tower K L M Q.1).symm

end Restriction

section Deuring

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- The Galois group `⟨σ⟩` of `L` over `E = L^⟨σ⟩` is a Galois group of the rings of integers. -/
theorem isGaloisGroup_zpowers_nf (σ : Gal(L/K)) :
    IsGaloisGroup (Subgroup.zpowers σ) (𝓞 (IntermediateField.fixedField (Subgroup.zpowers σ)))
      (𝓞 L) := by
  haveI : IsGaloisGroup (Subgroup.zpowers σ) (IntermediateField.fixedField (Subgroup.zpowers σ)) L :=
    IsGaloisGroup.subgroup Gal(L/K) K L _
  exact IsGaloisGroup.of_isFractionRing (Subgroup.zpowers σ) (𝓞 (IntermediateField.fixedField (Subgroup.zpowers σ)))
    (𝓞 L) (IntermediateField.fixedField (Subgroup.zpowers σ)) L

/-- Restricting `σ` viewed in `Gal(L/E)` back to `K` gives `σ`. -/
theorem restrictScalars_toFixedFieldGal (σ : Gal(L/K)) :
    (toFixedFieldGal K L σ).restrictScalars K = σ := rfl

/-- The conjugacy class of `σ` in the abelian group `Gal(L/E) = ⟨σ⟩` is a singleton. -/
theorem eq_of_isConj_toFixedFieldGal (σ : Gal(L/K))
    (x : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))))
    (h : IsConj x (toFixedFieldGal K L σ)) : x = toFixedFieldGal K L σ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h.symm
  have hcomm : c * toFixedFieldGal K L σ = toFixedFieldGal K L σ * c := by
    obtain ⟨y, rfl⟩ := (IntermediateField.fixingSubgroupEquiv
      (IntermediateField.fixedField (Subgroup.zpowers σ))).surjective c
    have hy : (y : Gal(L/K)) ∈ Subgroup.zpowers σ := by
      have h := IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ)
      rw [SetLike.ext_iff] at h
      exact (h _).mp y.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    let s : IntermediateField.fixingSubgroup
          (IntermediateField.fixedField (Subgroup.zpowers σ)) :=
      ⟨σ, by rw [IntermediateField.fixingSubgroup_fixedField]; exact Subgroup.mem_zpowers σ⟩
    have hys : y * s = s * y :=
      Subtype.ext (by
        show (y : Gal(L/K)) * σ = σ * (y : Gal(L/K))
        rw [← hn]; exact (Commute.zpow_self σ n))
    have := congrArg (IntermediateField.fixingSubgroupEquiv
      (IntermediateField.fixedField (Subgroup.zpowers σ))) hys
    simpa [toFixedFieldGal] using this
  rw [← hc, hcomm, mul_assoc, mul_inv_cancel, mul_one]

/-- Frobenius over `E` is `σ` iff Frobenius over `K` is `σ`, when `f(Q ∩ E | K) = 1`. -/
theorem arithFrobAt_E_eq_iff (σ : Gal(L/K)) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Finite (𝓞 L ⧸ Q)]
    [Algebra.IsUnramifiedAt (𝓞 K) Q]
    (h1 : (Q.under (𝓞 (IntermediateField.fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1) :
    arithFrobAt (𝓞 (IntermediateField.fixedField (Subgroup.zpowers σ))) Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))) Q = toFixedFieldGal K L σ ↔
      arithFrobAt (𝓞 K) Gal(L/K) Q = σ := by
  have := restrictScalars_arithFrobAt_eq_of_inertiaDeg_eq_one (K := K) Q
    (IntermediateField.fixedField (Subgroup.zpowers σ)) h1
  rw [← this]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    exact AlgEquiv.restrictScalars_injective K (h.trans (restrictScalars_toFixedFieldGal K L σ).symm)

theorem hasSep_congr {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {p q : Ideal A}
    [p.IsPrime] [q.IsPrime] (h : p = q) (hp : Algebra.HasSeparableResidueFieldsAt A B p) :
    Algebra.HasSeparableResidueFieldsAt A B q := by
  subst h
  convert hp


open Classical Pointwise in
/-- *Proved* from the abstract count (`FrobeniusEField.lean`). **Deuring's count.** Let $\sigma \in G$, $H = \langle\sigma\rangle$,
$E = L^H$, and $\mathfrak p$ a prime of `K` unramified in `L`. The number of primes $\mathfrak P$ of `E` above
$\mathfrak p$ with $f(\mathfrak P|\mathfrak p) = 1$ and $\mathrm{Frob}_{L/E}(\mathfrak P) = \sigma$ is
$|C_G(\sigma)|/\operatorname{ord}\sigma$ if $\mathrm{Frob}_{\mathfrak p} = [\sigma]$, and `0` otherwise.
(Used in Step 3 of the proof of the Chebotarev density theorem, the general case. For abelian `G` this is $[E:K]$, the count used in Step 2, the cyclic case.) -/
theorem deuring_count (σ : Gal(L/K)) {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ unramifiedPrimes K L) :
    {P : HeightOneSpectrum (𝓞 (IntermediateField.fixedField (Subgroup.zpowers σ))) |
        P.asIdeal.LiesOver 𝔭.asIdeal ∧ P.asIdeal.inertiaDeg (𝓞 K) = 1 ∧
        frobClass _ L P = ConjClasses.mk (toFixedFieldGal K L σ)}.ncard =
      if frobClass K L 𝔭 = ConjClasses.mk σ then
        Nat.card (Subgroup.centralizer ({σ} : Set Gal(L/K))) / orderOf σ
      else 0 := by
  set E := IntermediateField.fixedField (Subgroup.zpowers σ) with hE
  haveI : IsGaloisGroup (Subgroup.zpowers σ) (𝓞 E) (𝓞 L) := isGaloisGroup_zpowers_nf K L σ
  haveI hpmax : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  obtain ⟨Q₀⟩ : Nonempty (𝔭.asIdeal.primesOver (𝓞 L)) := inferInstance
  haveI := Q₀.2.1
  haveI := Q₀.2.2
  haveI := isMaximal_of_mem_primesOver K L 𝔭 Q₀
  haveI : Finite (𝓞 L ⧸ Q₀.1) :=
    finite_quotient_of_ne_bot _ (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q₀.1)
  haveI : Algebra.IsUnramifiedAt (𝓞 K) Q₀.1 := h𝔭 Q₀.1 Q₀.2.1 Q₀.2.2
  have hQ₀ : Q₀.1.under (𝓞 K) = 𝔭.asIdeal :=
    (Ideal.LiesOver.over (P := Q₀.1) (p := 𝔭.asIdeal)).symm
  have he : 𝔭.asIdeal.ramificationIdxIn (𝓞 L) = 1 := by
    have := ramificationIdxIn_eq_one_of_isUnramifiedAt (K := K) Q₀.1
    rwa [hQ₀] at this
  haveI hsep : Algebra.HasSeparableResidueFieldsAt (𝓞 K) (𝓞 L) 𝔭.asIdeal := by
    have := hasSeparableResidueFieldsAt_under (K := K) Q₀.1
    exact hasSep_congr hQ₀ this
  have hfin : ∀ P : 𝔭.asIdeal.primesOver (𝓞 L), Finite (𝓞 L ⧸ P.1) := fun P => by
    haveI := P.2.1
    haveI := P.2.2
    exact finite_quotient_of_ne_bot P.1 (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P.1)
  have hsepB : ∀ (P : Ideal (𝓞 L)) [P.IsPrime],
      Algebra.HasSeparableResidueFieldsAt (𝓞 E) (𝓞 L) (P.under (𝓞 E)) := by
    intro P _
    by_cases hP : P = ⊥
    · subst hP
      have h0 : Ideal.under (𝓞 E) (⊥ : Ideal (𝓞 L)) = ⊥ := Ideal.under_bot _ _
      have : Algebra.HasSeparableResidueFieldsAt (𝓞 E) (𝓞 L) (⊥ : Ideal (𝓞 E)) := inferInstance
      exact hasSep_congr h0.symm this
    · haveI := finite_quotient_of_ne_bot P hP
      exact hasSeparableResidueFieldsAt_under (K := E) P
  have hmain := card_eFieldPrimes_mul_orderOf (A := 𝓞 K) (C := 𝓞 L) (G := Gal(L/K)) (B := 𝓞 E)
    σ 𝔭.asIdeal hfin hsepB he
  set t := toFixedFieldGal K L σ with ht
  set T := eFieldPrimes (𝓞 L) (𝓞 E) σ 𝔭.asIdeal with hT
  set S := {P : HeightOneSpectrum (𝓞 E) |
        P.asIdeal.LiesOver 𝔭.asIdeal ∧ P.asIdeal.inertiaDeg (𝓞 K) = 1 ∧
        frobClass _ L P = ConjClasses.mk t} with hS
  have hfwd : ∀ P ∈ S, ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver P.asIdeal]
      [Finite (𝓞 L ⧸ Q)], arithFrobAt (𝓞 K) Gal(L/K) Q = σ := by
    intro P hP Q _ _ _
    haveI := hP.1
    haveI : Q.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans Q P.asIdeal 𝔭.asIdeal
    haveI : Algebra.IsUnramifiedAt (𝓞 K) Q := h𝔭 Q inferInstance inferInstance
    have hu : Q.under (𝓞 E) = P.asIdeal := (Ideal.LiesOver.over (P := Q) (p := P.asIdeal)).symm
    have h1 : (Q.under (𝓞 E)).inertiaDeg (𝓞 K) = 1 := by rw [hu]; exact hP.2.1
    haveI hQm : Q.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
    let Qp : P.asIdeal.primesOver (𝓞 L) := ⟨Q, inferInstance, inferInstance⟩
    have h2 := frobClass_eq_mk_frobAt E L P Qp
    rw [hP.2.2, ConjClasses.mk_eq_mk_iff_isConj] at h2
    have h3 : frobAt E L P Qp = t := eq_of_isConj_toFixedFieldGal K L σ _ h2.symm
    exact (arithFrobAt_E_eq_iff K L σ Q h1).mp h3
  have hbwd : ∀ (P : HeightOneSpectrum (𝓞 E)), P.asIdeal.LiesOver 𝔭.asIdeal →
      P.asIdeal.inertiaDeg (𝓞 K) = 1 → ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver P.asIdeal]
      [Finite (𝓞 L ⧸ Q)], arithFrobAt (𝓞 K) Gal(L/K) Q = σ → P ∈ S := by
    intro P hP1 hP2 Q _ _ _ hQ
    haveI := hP1
    haveI : Q.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans Q P.asIdeal 𝔭.asIdeal
    haveI : Algebra.IsUnramifiedAt (𝓞 K) Q := h𝔭 Q inferInstance inferInstance
    have hu : Q.under (𝓞 E) = P.asIdeal := (Ideal.LiesOver.over (P := Q) (p := P.asIdeal)).symm
    have h1 : (Q.under (𝓞 E)).inertiaDeg (𝓞 K) = 1 := by rw [hu]; exact hP2
    haveI hQm : Q.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
    let Qp : P.asIdeal.primesOver (𝓞 L) := ⟨Q, inferInstance, inferInstance⟩
    refine ⟨hP1, hP2, ?_⟩
    rw [frobClass_eq_mk_frobAt E L P Qp]
    congr 1
    exact (arithFrobAt_E_eq_iff K L σ Q h1).mpr hQ
  have hST : S.ncard = Nat.card T := by
    have himg : HeightOneSpectrum.asIdeal '' S = T := by
      ext Q
      constructor
      · rintro ⟨P, hP, rfl⟩
        haveI := P.isPrime
        haveI := hP.1
        obtain ⟨Q'⟩ : Nonempty (P.asIdeal.primesOver (𝓞 L)) := inferInstance
        haveI := Q'.2.1
        haveI := Q'.2.2
        haveI hfQ : Finite (𝓞 L ⧸ Q'.1) :=
          finite_quotient_of_ne_bot _ (Ideal.ne_bot_of_liesOver_of_ne_bot P.ne_bot Q'.1)
        haveI : Q'.1.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans Q'.1 P.asIdeal 𝔭.asIdeal
        haveI := hsepB Q'.1
        have hσ := hfwd P hP Q'.1
        have hu : Q'.1.under (𝓞 E) = P.asIdeal := (Ideal.LiesOver.over (P := Q'.1) (p := P.asIdeal)).symm
        refine ⟨P.isPrime, hP.1, hP.2.1, Q'.1, Q'.2.1, Q'.2.2, hfQ, ?_⟩
        exact arithFrobAt_subgroup_of_frobMap_eq σ 𝔭.asIdeal he Q'.1 hσ
      · rintro ⟨hQp, hQl, hQ1, P', hP'p, hP'l, hP'fin, hfrob⟩
        have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
        refine ⟨⟨Q, hQp, hne⟩, ?_, rfl⟩
        haveI : P'.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans P' Q 𝔭.asIdeal
        haveI : Algebra.IsUnramifiedAt (𝓞 K) P' := h𝔭 P' inferInstance inferInstance
        have hu : P'.under (𝓞 E) = Q := (Ideal.LiesOver.over (P := P') (p := Q)).symm
        haveI := hsepB P'
        haveI : P'.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
        have h1 : (P'.under (𝓞 E)).inertiaDeg (𝓞 K) = 1 := by rw [hu]; exact hQ1
        have hσ : arithFrobAt (𝓞 K) Gal(L/K) P' = σ := by
          have h1' : (P'.under (𝓞 E)).inertiaDeg (𝓞 K) = 1 := h1
          have := frobMap_eq_of_inertiaDeg_eq_one (A := 𝓞 K) (C := 𝓞 L) (G := Gal(L/K)) (B := 𝓞 E)
            σ 𝔭.asIdeal he P' h1' hfrob
          exact this
        exact hbwd ⟨Q, hQp, hne⟩ hQl hQ1 P' hσ
    rw [← himg, Nat.card_coe_set_eq,
      Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]
  by_cases hc : frobClass K L 𝔭 = ConjClasses.mk σ
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), hST]
    have h2 := frobClass_eq_mk_frobAt K L 𝔭 Q₀
    rw [hc, ConjClasses.mk_eq_mk_iff_isConj] at h2
    obtain ⟨c, hcc⟩ := isConj_iff.mp h2.symm
    have hs := frobMap_smul (A := 𝓞 K) (C := 𝓞 L) (G := Gal(L/K)) 𝔭.asIdeal hfin he c Q₀
    obtain ⟨P₀, h₀⟩ : ∃ P₀ : 𝔭.asIdeal.primesOver (𝓞 L), frobMap 𝔭.asIdeal hfin P₀ = σ :=
      ⟨_, hs.trans hcc⟩
    have := hmain P₀ h₀
    rw [← this, Nat.mul_div_cancel _ (orderOf_pos σ)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    have : S = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun P hP => hc ?_
      haveI := P.isPrime
      haveI := hP.1
      obtain ⟨Q'⟩ : Nonempty (P.asIdeal.primesOver (𝓞 L)) := inferInstance
      haveI := Q'.2.1
      haveI := Q'.2.2
      haveI hfQ : Finite (𝓞 L ⧸ Q'.1) :=
        finite_quotient_of_ne_bot _ (Ideal.ne_bot_of_liesOver_of_ne_bot P.ne_bot Q'.1)
      haveI : Q'.1.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans Q'.1 P.asIdeal 𝔭.asIdeal
      have hσ := hfwd P hP Q'.1
      let Q'' : 𝔭.asIdeal.primesOver (𝓞 L) := ⟨Q'.1, inferInstance, inferInstance⟩
      rw [frobClass_eq_mk_frobAt K L 𝔭 Q'']
      congr 1
    rw [this, Set.ncard_empty]

end Deuring

end

end NumberFieldKB.Chebotarev
