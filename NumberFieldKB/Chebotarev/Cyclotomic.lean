import NumberFieldKB.Chebotarev.DensityTools
import NumberFieldKB.Chebotarev.FrobeniusPrimes
import NumberFieldKB.Chebotarev.PrimeDensityOrth
import NumberFieldKB.Chebotarev.DirichletHecke

/-!
# Step 1 of the proof of Chebotarev's theorem: the cyclotomic case

From the Hecke characters $\chi\circ N_{F/\mathbb Q}$ of `DirichletHecke.lean`, the equidistribution
lemma `hasDirichletDensity_fibre_of_subgroup`, and the elementary bound `splitPrimes_upperBound` for the gap
"$\chi\circ N\ne1$ when $\chi$ is nontrivial on $\mathrm{Gal}(F(\zeta_m)/F)$".
-/

open NumberField IsDedekindDomain Filter Topology Set Asymptotics
open NumberFieldKB.HeckeL NumberFieldKB.HeckeCharacter NumberFieldKB.NonVanishing

namespace NumberFieldKB.Chebotarev

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## §2. Step 1: the cyclotomic case of Chebotarev's theorem -/

section Cyclotomic

variable {F : Type} [Field F] [NumberField F]

/-- If $N\mathfrak p$ is prime to `m`, then `m ∉ 𝔭`. -/
theorem natCast_notMem_of_coprime {v : HeightOneSpectrum (𝓞 F)} {m : ℕ}
    (hv : (Ideal.absNorm v.asIdeal).Coprime m) : (m : 𝓞 F) ∉ v.asIdeal := by
  intro hm
  haveI := v.isMaximal
  obtain ⟨p, n, hn, hpv, hp, hN⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
  rw [hN] at hv
  have hpm : Nat.Coprime p m := (Nat.coprime_pow_left_iff hn _ _).mp hv
  have hg := Nat.gcd_eq_gcd_ab p m
  rw [hpm] at hg
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h : (((p : ℤ) * Nat.gcdA p m + (m : ℤ) * Nat.gcdB p m : ℤ) : 𝓞 F) ∈ v.asIdeal := by
    push_cast
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hpv) (Ideal.mul_mem_right _ _ hm)
  rwa [← hg, Nat.cast_one, Int.cast_one] at h

/-- **Only finitely many primes have norm not prime to `m`** (they contain `m`). -/
theorem finite_not_coprime (m : ℕ) [NeZero m] :
    {v : HeightOneSpectrum (𝓞 F) | ¬ (Ideal.absNorm v.asIdeal).Coprime m}.Finite := by
  have hI : Ideal.span {(m : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast NeZero.ne m
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  simp only [Set.mem_ofPred_eq] at hv ⊢
  rw [Ideal.dvd_span_singleton]
  haveI := v.isMaximal
  obtain ⟨p, n, hn, hpv, hp, hN⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
  rw [hN, Nat.coprime_pow_left_iff hn, Nat.Prime.coprime_iff_not_dvd hp, not_not] at hv
  obtain ⟨k, rfl⟩ := hv
  push_cast
  exact Ideal.mul_mem_right _ _ hpv

variable (F) {M : Type} [Field M] [NumberField M] [Algebra F M]

/-- **Frobenius on roots of unity.** In $M = F(\zeta_m)$, at a prime $\mathfrak p$ with $N\mathfrak p$ prime to `m`,
every Frobenius element acts as $\zeta \mapsto \zeta^{N\mathfrak p}$: its image under
$\mathrm{Gal}(M/F) \hookrightarrow (\mathbb Z/m)^\times$ is $N\mathfrak p \bmod m$. -/
theorem autToPow_frobAt (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} F M] [IsGalois F M]
    {v : HeightOneSpectrum (𝓞 F)} (hv : (Ideal.absNorm v.asIdeal).Coprime m)
    (Q : v.asIdeal.primesOver (𝓞 M)) :
    ((IsCyclotomicExtension.zeta_spec m F M).autToPow F (frobAt F M v Q) : ZMod m) =
      (Ideal.absNorm v.asIdeal : ZMod m) := by
  have hζ := IsCyclotomicExtension.zeta_spec m F M
  set ζ := IsCyclotomicExtension.zeta m F M
  set σ := frobAt F M v Q
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  let z : 𝓞 M := ⟨ζ, (hζ.isIntegral hm).tower_top⟩
  have hz : z ^ m = 1 := by
    apply RingOfIntegers.ext
    show algebraMap (𝓞 M) M (z ^ m) = algebraMap (𝓞 M) M 1
    rw [map_pow, map_one]
    exact hζ.pow_eq_one
  haveI := Q.2.2
  have hQ : ((m : ℕ) : 𝓞 M) ∉ Q.1 := by
    intro h
    have h' : (m : 𝓞 F) ∈ Q.1.under (𝓞 F) := by
      rw [Ideal.mem_comap, map_natCast]; exact h
    rw [← Ideal.over_def Q.1 v.asIdeal] at h'
    exact natCast_notMem_of_coprime hv h'
  have hfr := (isArithFrobAt_frobAt F M v Q).apply_of_pow_eq_one hz hQ
  have hcard : Nat.card (𝓞 F ⧸ Q.1.under (𝓞 F)) = Ideal.absNorm v.asIdeal := by
    rw [← Ideal.over_def Q.1 v.asIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard] at hfr
  have h1 : σ ζ = ζ ^ Ideal.absNorm v.asIdeal := by
    have e1 : ((MulSemiringAction.toAlgHom (𝓞 F) (𝓞 M) σ z : 𝓞 M) : M) = σ ζ := rfl
    have e2 : ((z ^ Ideal.absNorm v.asIdeal : 𝓞 M) : M) = ζ ^ Ideal.absNorm v.asIdeal := by
      show algebraMap (𝓞 M) M (z ^ _) = _
      rw [map_pow]; rfl
    rw [← e1, hfr, e2]
  have h2 := hζ.autToPow_spec F σ
  rw [h1] at h2
  have key : ∀ a b : ℕ, ζ ^ a = ζ ^ b → (a : ZMod m) = b := fun a b hab => by
    have e : ∀ c : ℕ, ζ ^ c = ζ ^ (c % m) := fun c => by
      conv_lhs => rw [← Nat.mod_add_div c m, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    rw [e a, e b] at hab
    have := hζ.pow_inj (Nat.mod_lt _ hm) (Nat.mod_lt _ hm) hab
    rw [← ZMod.natCast_mod a m, ← ZMod.natCast_mod b m, this]
  have := key _ _ h2
  rwa [ZMod.natCast_zmod_val] at this

end Cyclotomic

section CyclotomicDensity

/-- *Proved* (conditional on `IdelicNormInput`). **Step 1, cyclotomic case.** For a cyclotomic extension $M = F(\zeta_m)$ of a number
field `F` and any $\tau \in \mathrm{Gal}(M/F)$, the unramified primes with Frobenius `τ` have Dirichlet density
$1/[M:F]$. (`Gal(M/F)` is abelian, so the class of `τ` is `{τ}`.)
*Proof route*: $\mathrm{Frob}_{\mathfrak p} = N\mathfrak p \bmod m$ under $\mathrm{Gal}(M/F) \hookrightarrow
(\mathbb Z/m)^\times$; the characters of $\mathrm{Gal}(M/F)$ are restrictions of Dirichlet characters $\chi$ mod
`m`, whose $L$-functions over `F` are the Hecke $L$-functions of $\chi\circ N_{F/\mathbb Q}$; orthogonality,
$\log L(s,\chi\circ N) = \sum_{\mathfrak p}\chi(N\mathfrak p)N\mathfrak p^{-s} + O(1)$, the pole of the trivial one
and non-vanishing at $s = 1$ of the others (`heckeLCont_ne_zero_of_one_le_re`). -/
theorem cyclotomic_density (hN : IdelicNormInput) (F M : Type) [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} F M] [IsGalois F M] (τ : Gal(M/F)) :
    (frobSet F M (ConjClasses.mk τ)).HasDirichletDensity (1 / Module.finrank F M) := by
  classical
  have hζ := IsCyclotomicExtension.zeta_spec m F M
  set ι : Gal(M/F) →* (ZMod m)ˣ := hζ.autToPow F with hι_def
  have hιinj : Function.Injective ι := hζ.autToPow_injective F
  set H : Subgroup (ZMod m)ˣ := ι.range with hH_def
  have hH : Nat.card H = Module.finrank F M := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv, IsGalois.card_aut_eq_finrank]
  have hcomm : ∀ a b : Gal(M/F), a * b = b * a := fun a b =>
    hιinj (by rw [map_mul, map_mul, mul_comm])
  -- the good primes: unramified in `M`, of norm prime to `m`
  set U : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | v ∈ unramifiedPrimes F M ∧ (Ideal.absNorm v.asIdeal).Coprime m} with hU_def
  have hUc : Uᶜ.Finite := by
    refine ((finite_compl_unramifiedPrimes F M).union (finite_not_coprime (F := F) m)).subset ?_
    intro v hv
    have hv' : ¬ (v ∈ unramifiedPrimes F M ∧ (Ideal.absNorm v.asIdeal).Coprime m) := hv
    rcases not_and_or.1 hv' with h | h
    · exact Or.inl h
    · exact Or.inr h
  set fr : HeightOneSpectrum (𝓞 F) → Gal(M/F) := fun v => frobAt F M v (Classical.arbitrary _)
    with hfr_def
  have hfrC : ∀ v, frobClass F M v = ConjClasses.mk (fr v) := fun v => rfl
  set f : HeightOneSpectrum (𝓞 F) → (ZMod m)ˣ := fun v => if v ∈ U then ι (fr v) else 1 with hf_def
  have hfU : ∀ v ∈ U, f v = ι (fr v) := fun v hv => ite_eq_left_of_eq_true _ _ (eq_true hv)
  have hfnU : ∀ v ∉ U, f v = 1 := fun v hv => ite_eq_right_of_eq_false _ _ (eq_false hv)
  have hfval : ∀ v ∈ U, ((f v : (ZMod m)ˣ) : ZMod m) = (Ideal.absNorm v.asIdeal : ZMod m) :=
    fun v hv => by rw [hfU v hv]; exact autToPow_frobAt F m hv.2 _
  have hfH : ∀ v, f v ∈ H := fun v => by
    by_cases hv : v ∈ U
    · rw [hfU v hv]; exact ⟨_, rfl⟩
    · rw [hfnU v hv]; exact H.one_mem
  -- characters `χ` mod `m` whose Hecke character `χ ∘ N` is nontrivial give bounded prime sums
  let Good : MulChar (ZMod m) ℂ → Prop := fun χ => ∃ ψ : HeckeCharacter F, IsDirichletLift χ ψ ∧ ψ ≠ 1
  have hnormf : ∀ χ : MulChar (ZMod m) ℂ, ∀ v, ‖χ (f v)‖ ≤ 1 := fun χ v =>
    (norm_mulChar_apply_units χ (f v)).le
  have hgood : ∀ χ, Good χ →
      (fun s : ℝ => primeSum (fun v => χ (f v)) s) =O[𝓝[>] 1] (fun _ => (1 : ℂ)) := by
    rintro χ ⟨ψ, hψ, hne⟩
    have h1 := isBigO_primeSum_heckeCoeff hψ.isUnitary (hψ.ne_normPow hne)
    have h2 := isBigO_primeSum_sub_of_finite (hnormf χ) (norm_heckeCoeff_le hψ.isUnitary)
      (hUc.subset fun v hv hvU => hv (by rw [hfval v hvU]; exact (hψ.heckeCoeff_eq hvU.2).symm))
    exact (h2.add h1).congr_left fun s => by ring
  -- if `χ ∘ N` is trivial then `χ(N𝔭) = 1` at the good primes
  have hbad : ∀ χ : MulChar (ZMod m) ℂ, ¬ Good χ → ∀ v ∈ U, χ (f v) = 1 := by
    intro χ hχ v hv
    obtain ⟨ψ, hψ⟩ := exists_isDirichletLift hN F χ
    have hψ1 : ψ = 1 := by
      by_contra h
      exact hχ ⟨ψ, hψ, h⟩
    rw [hfval v hv]
    by_contra hne
    exact hψ.ne_one_of_apply_ne_one hv.2 hne hψ1
  -- `B`: the common kernel of the characters with `χ ∘ N` trivial
  let B : Subgroup (ZMod m)ˣ := ⨅ (χ : MulChar (ZMod m) ℂ) (_ : ¬ Good χ), χ.toUnitHom.ker
  have hmemB : ∀ h : (ZMod m)ˣ, h ∈ B ↔ ∀ χ : MulChar (ZMod m) ℂ, ¬ Good χ → χ h = 1 := by
    intro h
    simp only [B, Subgroup.mem_iInf, MonoidHom.mem_ker]
    refine forall_congr' fun χ => forall_congr' fun _ => ?_
    rw [Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
  set H' : Subgroup (ZMod m)ˣ := H ⊓ B with hH'_def
  have hfH' : ∀ v, f v ∈ H' := fun v => by
    refine Subgroup.mem_inf.2 ⟨hfH v, (hmemB _).2 fun χ hχ => ?_⟩
    by_cases hv : v ∈ U
    · exact hbad χ hχ v hv
    · rw [hfnU v hv, Units.val_one, map_one]
  have hfibre' := hasDirichletDensity_fibre_of_subgroup H' f hfH'
    (fun χ ⟨h, hh, hχh⟩ => hgood χ (by
      by_contra hχ
      exact hχh (((hmemB h).1 (Subgroup.mem_inf.1 hh).2) χ hχ))) H'.one_mem
  -- the gap: the fibre of `1` lies in the split primes up to finitely many, so `|H| ≤ |H'|`
  have hsub : {v | f v = 1} ⊆ splitPrimes F M ∪ Uᶜ := by
    intro v hv
    by_cases hvU : v ∈ U
    · left
      rw [splitPrimes_eq_frobSet_one]
      refine ⟨hvU.1, ?_⟩
      rw [hfrC]
      have h1 : ι (fr v) = ι 1 := by rw [← hfU v hvU, map_one]; exact hv
      rw [hιinj h1]
    · exact Or.inr hvU
  have hle : 1 / (Nat.card H' : ℝ) ≤ 1 / (Nat.card H : ℝ) := by
    have hfin := hasDirichletDensity_zero_of_finite hUc
    rw [hasDirichletDensity_iff] at hfibre' hfin
    refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
    have hb' : b > 1 / (Module.finrank F M : ℝ) := by rwa [← hH]
    have hup := splitPrimes_upperBound (F := F) M b hb'
    have hlim := hfibre'.sub hfin
    rw [sub_zero] at hlim
    refine le_of_tendsto hlim ?_
    filter_upwards [hup, self_mem_nhdsWithin] with s hs (hs1 : 1 < s)
    have hP : 0 ≤ (univ : Set (HeightOneSpectrum (𝓞 F))).primeIdealZetaSum s :=
      Set.primeIdealZetaSum_nonneg _ _
    have h1 : {v | f v = 1}.primeIdealZetaSum s ≤
        (splitPrimes F M).primeIdealZetaSum s + Uᶜ.primeIdealZetaSum s := by
      calc _ ≤ (splitPrimes F M ∪ Uᶜ).primeIdealZetaSum s := primeIdealZetaSum_mono hsub hs1
        _ = (splitPrimes F M ∪ (Uᶜ \ splitPrimes F M)).primeIdealZetaSum s := by
            rw [Set.union_sdiff_self]
        _ = (splitPrimes F M).primeIdealZetaSum s + (Uᶜ \ splitPrimes F M).primeIdealZetaSum s :=
            primeIdealZetaSum_union_disjoint Set.disjoint_sdiff_right hs1
        _ ≤ _ := add_le_add le_rfl (primeIdealZetaSum_mono Set.sdiff_subset hs1)
    have h2 : dirichletRatio {v | f v = 1} s - dirichletRatio Uᶜ s ≤
        dirichletRatio (splitPrimes F M) s := by
      simp only [dirichletRatio]
      rw [← sub_div]
      exact div_le_div_of_nonneg_right (by linarith) hP
    linarith
  have hcard : Nat.card H ≤ Nat.card H' := by
    have h0 : (0 : ℝ) < Nat.card H' := by exact_mod_cast Nat.card_pos
    have h0' : (0 : ℝ) < Nat.card H := by exact_mod_cast Nat.card_pos
    rw [one_div_le_one_div h0 h0'] at hle
    exact_mod_cast hle
  have hHB : H ≤ B := by
    have : H' = H := Subgroup.eq_of_le_of_card_ge inf_le_left hcard
    rw [← this]
    exact inf_le_right
  -- equidistribution in `H`
  have hfibre := hasDirichletDensity_fibre_of_subgroup H f hfH
    (fun χ ⟨h, hh, hχh⟩ => hgood χ (by
      by_contra hχ
      exact hχh (((hmemB h).1 (hHB hh)) χ hχ))) (g := ι τ) ⟨τ, rfl⟩
  rw [hH] at hfibre
  refine HasDirichletDensity.congr_finite hfibre (hUc.subset ?_)
  intro v hv hvU
  have key : f v = ι τ ↔ v ∈ frobSet F M (ConjClasses.mk τ) := by
    rw [hfU v hvU, hιinj.eq_iff]
    change fr v = τ ↔ v ∈ unramifiedPrimes F M ∧ frobClass F M v = ConjClasses.mk τ
    rw [hfrC, ConjClasses.mk_eq_mk_iff_isConj]
    constructor
    · rintro rfl
      exact ⟨hvU.1, IsConj.refl _⟩
    · rintro ⟨-, hc⟩
      obtain ⟨c, hc⟩ := isConj_iff.1 hc
      rw [hcomm c, mul_inv_cancel_right] at hc
      exact hc
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (key.1 h1)
  · exact h2 (key.2 h1)

end CyclotomicDensity

end

end NumberFieldKB.Chebotarev
