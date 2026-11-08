import NumberFieldKB.MilneCFT.Ch8.Eisenstein.LambdaCompletion

/-!
# A local field with the invariants of $\mathbb Q_p(\zeta_p)$ containing $\mathbb Q(\zeta_p)$ is the completion

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §5, the setting
of Proposition 5.12 (p. 248): $K_\lambda = \mathbb Q_p[\zeta_p]$.

Let $K = \mathbb Q(\zeta_p)$ and let $\iota : K \to K_l$ be a field embedding into a nonarchimedean local field whose
ring of integers has the uniformizer $\iota(1 - \zeta)$ and residue field with $p$ elements (the hypotheses of
`prop_5_12_full`). Then $\iota$ extends to a continuous isomorphism $K_\lambda \cong K_l$ from the completion at
$\lambda = (\zeta - 1)$ (`exists_completion_equiv`).

Proof: $\iota$ maps $\mathcal O_K$ into $\mathcal O_{K_l}$ (integrality), $\lambda$ into the maximal ideal and the
complement of $\lambda$ into the units; hence the valuation of $K_l$ restricted to $K$ is equivalent to the
$\lambda$-adic one (`isEquiv_comap`), $\iota$ is continuous, and it extends to the completion. The extension is onto:
its image contains the image of the compact ring $\mathcal O_\lambda$, which is closed and contains the dense subset
$\iota(\mathcal O_K)$ of $\mathcal O_{K_l}$ (digits in $\mathbb Z$, since the residue field is $\mathbb F_p$).
-/

open scoped ValuativeRel nonZeroDivisors
open NumberField IsDedekindDomain ValuativeRel

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.Eisenstein

variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ p)
variable {Kl : Type} [Field Kl] [ValuativeRel Kl] [TopologicalSpace Kl] [IsNonarchimedeanLocalField Kl]
variable (ι : K →+* Kl)

/-- Algebraic integers of $K$ land in the ring of integers of $K_l$. -/
theorem valuation_iota_le_one (x : 𝓞 K) : valuation Kl (ι (x : K)) ≤ 1 := by
  have hx : IsIntegral ℤ (ι (x : K)) := (RingOfIntegers.isIntegral_coe x).map ι.toIntAlgHom
  have : IsIntegral 𝒪[Kl] (ι (x : K)) := hx.tower_top
  exact (Valuation.integer.integers (valuation Kl)).mem_of_integral this

/-- $\iota$ on the rings of integers. -/
def iotaInt : 𝓞 K →+* 𝒪[Kl] :=
  (ι.comp (algebraMap (𝓞 K) K)).codRestrict _ (fun x => valuation_iota_le_one ι x)

theorem coe_iotaInt (x : 𝓞 K) : ((iotaInt ι x : 𝒪[Kl]) : Kl) = ι (x : K) := rfl

variable {ι} {lam : 𝒪[Kl]} (hlam : Irreducible lam) (hlamζ : (lam : Kl) = 1 - ι ζ)
include hlam hlamζ

theorem iotaInt_zeta_sub_one : iotaInt ι (hζ.toInteger - 1) = -lam := by
  apply Subtype.ext
  rw [coe_iotaInt]
  push_cast
  have hz : ((hζ.toInteger : 𝓞 K) : K) = ζ := hζ.coe_toInteger
  simp only [hz, hlamζ, map_sub, map_one]
  ring

/-- The preimage of the maximal ideal of $\mathcal O_{K_l}$ is $\lambda$. -/
theorem comap_iotaInt_maximalIdeal :
    (IsLocalRing.maximalIdeal 𝒪[Kl]).comap (iotaInt ι) = (lamPlace hζ).asIdeal := by
  have hle : (lamPlace hζ).asIdeal ≤ (IsLocalRing.maximalIdeal 𝒪[Kl]).comap (iotaInt ι) := by
    rw [lamPlace_asIdeal, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
      iotaInt_zeta_sub_one hζ hlam hlamζ, Ideal.neg_mem_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hlam.not_isUnit
  exact ((lamPlace hζ).isMaximal.eq_of_le (Ideal.comap_isPrime _ _).ne_top hle).symm

/-- Elements of $\mathcal O_K$ outside $\lambda$ go to units. -/
theorem valuation_iota_eq_one {x : 𝓞 K} (hx : x ∉ (lamPlace hζ).asIdeal) : valuation Kl (ι (x : K)) = 1 := by
  rw [← comap_iotaInt_maximalIdeal hζ hlam hlamζ, Ideal.mem_comap] at hx
  have hu : IsUnit (iotaInt ι x) := (IsLocalRing.notMem_maximalIdeal).mp hx
  have := (Valuation.integer.integers (valuation Kl)).isUnit_iff_valuation_eq_one.mp hu
  exact this

omit hlam hlamζ in
/-- Factor out the largest power of $\zeta - 1$. -/
theorem exists_eq_pow_mul {r : 𝓞 K} (hr : r ≠ 0) :
    ∃ (k : ℕ) (r' : 𝓞 K), r = (hζ.toInteger - 1) ^ k * r' ∧ r' ∉ (lamPlace hζ).asIdeal := by
  obtain ⟨k, r', h1, h2⟩ := WfDvdMonoid.max_power_factor hr hζ.zeta_sub_one_prime'.irreducible
  exact ⟨k, r', h2, by rwa [lamPlace_asIdeal, Ideal.mem_span_singleton]⟩

/-- The valuation of $K_l$ on $\iota(r)$, $r = (\zeta - 1)^k r'$. -/
theorem valuation_iota_pow_mul (k : ℕ) {r' : 𝓞 K} (hr' : r' ∉ (lamPlace hζ).asIdeal) :
    valuation Kl (ι (((hζ.toInteger - 1) ^ k * r' : 𝓞 K) : K)) = valuation Kl (lam : Kl) ^ k := by
  rw [← coe_iotaInt, map_mul, map_pow, iotaInt_zeta_sub_one hζ hlam hlamζ]
  push_cast
  rw [map_mul, map_pow, Valuation.map_neg, coe_iotaInt, valuation_iota_eq_one hζ hlam hlamζ hr', mul_one]

omit hlam hlamζ in
theorem valuation_lam_pow_mul (k : ℕ) {r' : 𝓞 K} (hr' : r' ∉ (lamPlace hζ).asIdeal) :
    (lamPlace hζ).valuation K (((hζ.toInteger - 1) ^ k * r' : 𝓞 K) : K) = WithZero.exp (-1) ^ k := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, map_mul, map_pow,
    HeightOneSpectrum.intValuation_singleton _ (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hp.out.one_lt) rfl,
    (HeightOneSpectrum.intValuation_eq_one_iff).mpr hr', mul_one]

theorem valuation_lam_lt_one : valuation Kl (lam : Kl) < 1 := by
  have := (Valuation.integer.integers (valuation Kl)).isUnit_iff_valuation_eq_one (x := lam)
  exact lt_of_le_of_ne lam.2 (fun h => hlam.not_isUnit (this.mpr h))

theorem valuation_lam_ne_zero : valuation Kl (lam : Kl) ≠ 0 := by
  rw [Ne, Valuation.zero_iff]
  intro h
  exact hlam.ne_zero (Subtype.ext h)

/-- **The two valuations on $K$ are equivalent**: the $\lambda$-adic one and the one of $K_l$ through $\iota$. -/
theorem isEquiv_comap : ((lamPlace hζ).valuation K).IsEquiv ((valuation Kl).comap ι) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hr : r ≠ 0 := by rintro rfl; simp at hx0
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨k, r', rfl, hr'⟩ := exists_eq_pow_mul hζ hr
  obtain ⟨m, s', rfl, hs'⟩ := exists_eq_pow_mul hζ hs0
  simp only [Valuation.comap_apply, map_div₀]
  rw [valuation_lam_pow_mul hζ k hr', valuation_lam_pow_mul hζ m hs']
  change _ ≤ 1 ↔ valuation Kl (ι (((hζ.toInteger - 1) ^ k * r' : 𝓞 K) : K)) /
    valuation Kl (ι (((hζ.toInteger - 1) ^ m * s' : 𝓞 K) : K)) ≤ 1
  rw [valuation_iota_pow_mul hζ hlam hlamζ k hr', valuation_iota_pow_mul hζ hlam hlamζ m hs']
  have ha : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ^ m ≠ 0 := pow_ne_zero _ WithZero.exp_ne_zero
  have hb : valuation Kl (lam : Kl) ^ m ≠ 0 := pow_ne_zero _ (valuation_lam_ne_zero hlam hlamζ)
  rw [div_le_one₀ (zero_lt_iff.mpr ha), div_le_one₀ (zero_lt_iff.mpr hb),
    pow_le_pow_iff_right_of_lt_one₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)
      (WithZero.exp_lt_exp.mpr (by norm_num)),
    pow_le_pow_iff_right_of_lt_one₀ (zero_lt_iff.mpr (valuation_lam_ne_zero hlam hlamζ))
      (valuation_lam_lt_one hlam hlamζ)]

/-- $\iota$ read on the type synonym `WithVal` carrying the $\lambda$-adic valuation. -/
def iotaW (ι : K →+* Kl) : WithVal ((lamPlace hζ).valuation K) →+* Kl :=
  ι.comp (WithVal.equiv ((lamPlace hζ).valuation K)).toRingHom

omit hlam hlamζ in
theorem iotaW_apply (x : WithVal ((lamPlace hζ).valuation K)) :
    iotaW hζ ι x = ι (WithVal.equiv _ x) := rfl

include hlam hlamζ in
/-- **$\iota$ is continuous** for the $\lambda$-adic topology. -/
theorem continuous_iotaW : Continuous (iotaW hζ ι) := by
  refine continuous_of_tendsto_nhds_zero (iotaW hζ ι) ?_
  rw [(IsValuativeTopology.hasBasis_nhds_zero _).tendsto_iff (IsValuativeTopology.hasBasis_nhds_zero Kl)]
  intro γ _
  obtain ⟨N, hN⟩ := exists_pow_lt₀ (valuation_lam_lt_one hlam hlamζ) γ
  set π : K := ((hζ.toInteger - 1 : 𝓞 K) : K)
  have hne : (hζ.toInteger - 1 : 𝓞 K) ≠ 0 := hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hp.out.one_lt
  have hπ0 : π ^ N ≠ 0 := pow_ne_zero _ (fun h => hne (RingOfIntegers.coe_injective (by
    rw [map_zero]; exact h)))
  set t : WithVal ((lamPlace hζ).valuation K) := (WithVal.equiv _).symm (π ^ N)
  have ht0 : valuation _ t ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    simpa [t] using hπ0
  refine ⟨Units.mk0 _ ht0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hx ⊢
  have h1 : (lamPlace hζ).valuation K (WithVal.equiv _ x) < (lamPlace hζ).valuation K (π ^ N) := by
    have := ((ValuativeRel.isEquiv (WithVal.valuation ((lamPlace hζ).valuation K))
      (valuation (WithVal ((lamPlace hζ).valuation K)))).lt_iff_lt).mpr hx
    simpa [t, WithVal.valuation] using this
  have h2 := (isEquiv_comap hζ hlam hlamζ).lt_iff_lt.mp h1
  simp only [Valuation.comap_apply] at h2
  rw [iotaW_apply]
  refine lt_of_lt_of_le h2 ?_
  have hπN : π ^ N = (((hζ.toInteger - 1) ^ N * 1 : 𝓞 K) : K) := by simp [π]
  rw [hπN, valuation_iota_pow_mul hζ hlam hlamζ N (by
    rw [lamPlace_asIdeal, Ideal.mem_span_singleton]
    exact hζ.zeta_sub_one_prime'.not_dvd_one)]
  exact hN.le

omit hlam hlamζ in
/-- The extension of $\iota$ to the completion $K_\lambda$. -/
def compToKl (ι : K →+* Kl) (hc : Continuous (iotaW hζ ι)) : Klam hζ →+* Kl :=
  letI : UniformSpace Kl := IsTopologicalAddGroup.rightUniformSpace Kl
  haveI : IsUniformAddGroup Kl := isUniformAddGroup_of_addCommGroup
  (UniformSpace.Completion.extensionHom (iotaW hζ ι) hc).comp
    (HeightOneSpectrum.adicCompletion.equiv K (lamPlace hζ)).toRingHom

omit hlam hlamζ in
theorem compToKl_algebraMap (ι : K →+* Kl) (hc : Continuous (iotaW hζ ι)) (x : K) :
    compToKl hζ ι hc (algebraMap K (Klam hζ) x) = ι x := by
  letI : UniformSpace Kl := IsTopologicalAddGroup.rightUniformSpace Kl
  haveI : IsUniformAddGroup Kl := isUniformAddGroup_of_addCommGroup
  change UniformSpace.Completion.extensionHom (iotaW hζ ι) hc
    (HeightOneSpectrum.adicCompletion.equiv K (lamPlace hζ) (algebraMap K (Klam hζ) x)) = _
  rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply]
  change UniformSpace.Completion.extensionHom (iotaW hζ ι) hc
    ((x : (lamPlace hζ).adicCompletion K).toCompletion) = _
  rw [HeightOneSpectrum.adicCompletion.coe_toCompletion, UniformSpace.Completion.extensionHom_coe]
  rfl

omit hlam hlamζ in
theorem continuous_compToKl (ι : K →+* Kl) (hc : Continuous (iotaW hζ ι)) :
    Continuous (compToKl hζ ι hc) := by
  letI : UniformSpace Kl := IsTopologicalAddGroup.rightUniformSpace Kl
  haveI : IsUniformAddGroup Kl := isUniformAddGroup_of_addCommGroup
  exact (UniformSpace.Completion.continuous_extension).comp
    (HeightOneSpectrum.adicCompletion.continuous_toCompletion K (lamPlace hζ))

omit [IsCyclotomicExtension {p} ℚ K] hlam hlamζ in
/-- A residue field with $p$ elements is $\mathbb F_p$: every class is the class of an integer. -/
theorem exists_intCast_residue (hres : Nat.card 𝓀[Kl] = p) (w : 𝓀[Kl]) : ∃ m : ℤ, (m : 𝓀[Kl]) = w := by
  classical
  letI : Fintype 𝓀[Kl] := Fintype.ofFinite _
  have hcard : Fintype.card 𝓀[Kl] = p := by rw [← Nat.card_eq_fintype_card]; exact hres
  haveI : CharP 𝓀[Kl] p := charP_of_card_eq_prime hcard
  set g : ZMod p →+* 𝓀[Kl] := ZMod.castHom (dvd_refl p) 𝓀[Kl]
  have hbij : Function.Bijective g := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨g.injective, by rw [ZMod.card, hcard]⟩
  obtain ⟨z, rfl⟩ := hbij.2 w
  refine ⟨(z.val : ℤ), ?_⟩
  simp [g]

include hζ in
/-- **$\iota(\mathcal O_K)$ is dense in $\mathcal O_{K_l}$**: every $z$ is congruent modulo $\lambda^N$ to some
$\iota(x)$. -/
theorem exists_iotaInt_approx (hres : Nat.card 𝓀[Kl] = p) (z : 𝒪[Kl]) (N : ℕ) :
    ∃ x : 𝓞 K, lam ^ N ∣ z - iotaInt ι x := by
  induction N with
  | zero => exact ⟨0, by simp⟩
  | succ N ih =>
    obtain ⟨x, w, hw⟩ := ih
    obtain ⟨m, hm⟩ := exists_intCast_residue hres (IsLocalRing.residue _ w)
    have hmem : w - m ∈ IsLocalRing.maximalIdeal 𝒪[Kl] := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_intCast, hm, sub_self]
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer lam).mp hlam, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hl : iotaInt ι (1 - hζ.toInteger) = lam := by
      rw [show (1 - hζ.toInteger : 𝓞 K) = -(hζ.toInteger - 1) by ring, map_neg,
        iotaInt_zeta_sub_one hζ hlam hlamζ, neg_neg]
    refine ⟨x + m * (1 - hζ.toInteger) ^ N, c, ?_⟩
    rw [map_add, map_mul, map_pow, hl, map_intCast]
    have : z - (iotaInt ι x + m * lam ^ N) = lam ^ N * (w - m) := by
      rw [mul_sub, ← hw]; ring
    rw [this, hc]
    ring

/-- **The extension of $\iota$ to $K_\lambda$ is onto.** -/
theorem compToKl_surjective (hc : Continuous (iotaW hζ ι)) (hres : Nat.card 𝓀[Kl] = p) :
    Function.Surjective (compToKl hζ ι hc) := by
  set f := compToKl hζ ι hc
  set S : Set Kl := f '' ((lamPlace hζ).adicCompletionIntegers K : Set (Klam hζ))
  have hS : IsClosed S := by
    have hcs : CompactSpace ((lamPlace hζ).adicCompletionIntegers K) := inferInstance
    have hcpt : IsCompact (((lamPlace hζ).adicCompletionIntegers K : Set (Klam hζ))) :=
      isCompact_iff_compactSpace.mpr hcs
    exact (hcpt.image (continuous_compToKl hζ ι hc)).isClosed
  have hInt : ∀ z : Kl, valuation Kl z ≤ 1 → z ∈ S := by
    intro z hz
    lift z to 𝒪[Kl] using hz
    rw [← hS.closure_eq, mem_closure_iff_nhds_basis' (IsValuativeTopology.hasBasis_nhds (z : Kl))]
    intro γ _
    obtain ⟨N, hN⟩ := exists_pow_lt₀ (valuation_lam_lt_one hlam hlamζ) γ
    obtain ⟨x, c, hxc⟩ := exists_iotaInt_approx hζ hlam hlamζ hres z N
    refine ⟨ι (x : K), ?_, algebraMap K (Klam hζ) (x : K), ?_, compToKl_algebraMap hζ ι hc _⟩
    · have h1 : ι (x : K) - (z : Kl) = -((lam : Kl) ^ N * (c : Kl)) := by
        have := congrArg (fun t : 𝒪[Kl] => (t : Kl)) hxc
        push_cast at this
        rw [coe_iotaInt] at this
        rw [← this]; ring
      change valuation Kl (ι (x : K) - (z : Kl)) < γ
      rw [h1, Valuation.map_neg, map_mul, map_pow]
      calc valuation Kl (lam : Kl) ^ N * valuation Kl (c : Kl) ≤ valuation Kl (lam : Kl) ^ N :=
            mul_le_of_le_one_right' c.2
        _ < γ := hN
    · have := HeightOneSpectrum.coe_mem_adicCompletionIntegers (lamPlace hζ) (K := K) x
      convert this using 1
  intro z
  by_cases hz : valuation Kl z ≤ 1
  · obtain ⟨y, -, hy⟩ := hInt z hz
    exact ⟨y, hy⟩
  · have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    have hzi : valuation Kl z⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hz))
    obtain ⟨y, -, hy⟩ := hInt z⁻¹ hzi
    exact ⟨y⁻¹, by rw [map_inv₀, hy, inv_inv]⟩

/-- **$K_l$ is the completion $K_\lambda$**: $\iota$ extends to a continuous isomorphism $K_\lambda \cong K_l$. -/
theorem exists_completion_equiv (hres : Nat.card 𝓀[Kl] = p) :
    ∃ e : Klam hζ ≃+* Kl, Continuous e ∧ ∀ x : K, e (algebraMap K (Klam hζ) x) = ι x := by
  have hc := continuous_iotaW hζ hlam hlamζ
  refine ⟨RingEquiv.ofBijective (compToKl hζ ι hc)
    ⟨(compToKl hζ ι hc).injective, compToKl_surjective hζ hlam hlamζ hc hres⟩,
    continuous_compToKl hζ ι hc, fun x => compToKl_algebraMap hζ ι hc x⟩

end NumberFieldKB.MilneCFT.Ch8.Eisenstein
