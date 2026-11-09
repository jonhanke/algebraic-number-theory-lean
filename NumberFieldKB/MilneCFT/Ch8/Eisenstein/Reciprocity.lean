import NumberFieldKB.MilneCFT.Ch8.Eisenstein.LambdaCompletion
import NumberFieldKB.MilneCFT.Ch8.Eisenstein.SymbolBridge
import NumberFieldKB.MilneCFT.Ch8.Prop512Normalization
import NumberFieldKB.MilneCFT.Ch8.FurtwanglerEisenstein
import NumberFieldKB.MilneCFT.Ch8.Powers
import NumberFieldKB.MilneCFT.LocalCFT.ReciprocityTauCeti

/-!
# The Eisenstein reciprocity law

Source: K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Theorem 14.5.1; J. S. Milne,
*Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §5 (Theorem 5.11 and Proposition 5.12).

`eisensteinReciprocity` proves the named statement `EisensteinReciprocity` (Ireland–Rosen 14.5.1): for $p$ an odd
prime, $K = \mathbb Q(\zeta_p)$, $a \in \mathbb Z$ prime to $p$ and $\alpha \in \mathcal O_K$ a primary non-unit prime
to $a$, $(\alpha/a)_p = (a/\alpha)_p$.

We do not follow Ireland–Rosen's proof through Stickelberger's relation; we derive the law from the Hilbert
reciprocity law (Milne VIII, 5.10, `item_5_10`) for Tau Ceti's idèlic Artin map, as in Hasse's treatment. With
$A = a$, $B = \alpha$ and $f(v) = (A, B)_v$ the global Hilbert symbol (`hilbertArtin`) of $K(A^{1/p})$:

* at $v \notin S(A)$, $f(v) = (A/\mathfrak p_v)^{\mathrm{ord}_v B}$ (`item_5_8`);
* at $v \mid a$, $v \nmid p$, $f(v) = (B, A)_v^{-1} = (B/\mathfrak p_v)^{-\mathrm{ord}_v A}$: the global symbols are the
  local Hilbert pairings of $K_v$ (`hilbertArtin_eq_hilbertPairing`), which are skew-symmetric (Steinberg);
* at $\lambda = (1 - \zeta)$, $f(\lambda) = 1$: in $K_\lambda$, $A$ and $B$ are rational integers prime to $p$ times
  $U^{(2)}$, and Proposition 5.12 (b) applies (`hilbertPairing_intCast_primary`).

The product formula $\prod_v f(v) = 1$ ($K$ is totally complex) then reads $(A/B) = (B/A)$ for Milne's symbols
`powerResidueElt`, which are Tau Ceti's `Ideal.powerResidueSymbolIdeal` (`powerResidueSymbolIdeal_eq_powerResidueElt`).
-/

open scoped ValuativeRel nonZeroDivisors
open NumberField IsDedekindDomain NumberFieldKB.MilneCFT.LocalCFT

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.Eisenstein

variable {K : Type} [Field K] [NumberField K]

/-- The image of a unit of $K$ in a completion. -/
abbrev unitAt (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ) : (v.adicCompletion K)ˣ :=
  Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom b

/-- **Skew-symmetry of the global Hilbert symbol** at a finite place, for two Kummer extensions and idèlic Artin
maps trivial on $K^\times$ (from the local pairing, `hilbertArtin_eq_hilbertPairing` and
`IsSteinbergPairing.skew`). -/
theorem hilbertArtin_mul_hilbertArtin_swap {p : ℕ} [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (La : Type) [Field La] [NumberField La] [Algebra K La] [IsAbelianGalois K La]
    (Lb : Type) [Field Lb] [NumberField Lb] [Algebra K Lb] [IsAbelianGalois K Lb]
    {a b : Kˣ} {α : La} {β : Lb} (hα : α ^ p = algebraMap K La a) (hβ : β ^ p = algebraMap K Lb b)
    (φa : IdeleGroup (𝓞 K) K →* Gal(La/K)) (φb : IdeleGroup (𝓞 K) K →* Gal(Lb/K))
    (hφa : IsIdelicArtinMap La φa) (hφb : IsIdelicArtinMap Lb φb)
    (hφaK : ∀ c : Kˣ, φa (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1)
    (hφbK : ∀ c : Kˣ, φb (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1) (v : HeightOneSpectrum (𝓞 K)) :
    hilbertArtin La φa α v b * hilbertArtin Lb φb β v a = 1 := by
  set Kv := v.adicCompletion K
  obtain ⟨φ, hφ⟩ := (localReciprocityExistence Kv (SeparableClosure Kv)).exists_artin
  have hζ0 : IsUnit ζ := (hζ.isUnit (Fact.out : p.Prime).ne_zero)
  set ζv : Kvˣ := unitAt v hζ0.unit
  have hζv : IsPrimitiveRoot ζv p := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    exact hζ.map_of_injective (algebraMap K Kv).injective
  have h1 := hilbertArtin_eq_hilbertPairing La hζ hα φa hφa hφaK v hζv hφ b
  have h2 := hilbertArtin_eq_hilbertPairing Lb hζ hβ φb hφb hφbK v hζv hφ a
  have hsk := (hilbertPairing_isSteinberg hζv hφ).skew (unitAt v a) (unitAt v b)
  apply (algebraMap K Kv).injective
  rw [map_mul, h1, h2, map_one, ← Units.val_mul, hsk, Units.val_one]

section Cyclotomic

variable {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-- The only prime of $\mathbb Q(\zeta_p)$ containing $p$ is $\lambda = (\zeta - 1)$. -/
theorem eq_lamPlace_of_natCast_mem (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) :
    v = lamPlace hζ := by
  have h1 : hζ.toInteger - 1 ∈ v.asIdeal := by
    obtain ⟨u, hu⟩ := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζ
    rw [← hu] at hv
    have : (hζ.toInteger - 1) ^ (p - 1) ∈ v.asIdeal :=
      (v.isPrime.mem_or_mem hv).resolve_right
        (fun h => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit))
    exact v.isPrime.mem_of_pow_mem _ this
  have hle : (lamPlace hζ).asIdeal ≤ v.asIdeal := by
    rw [lamPlace_asIdeal, Ideal.span_le, Set.singleton_subset_iff]; exact h1
  exact (HeightOneSpectrum.ext ((lamPlace hζ).isMaximal.eq_of_le v.isPrime.ne_top hle)).symm

/-- **The symbol at $\lambda$ vanishes**: $(a, \alpha)_\lambda = 1$ for $a \in \mathbb Z$ prime to $p$ and $\alpha$
primary. -/
theorem hilbertArtin_lamPlace_eq_one (hp2 : p ≠ 2)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) {A : Kˣ} (hA : (A : K) = a) {β : L} (hβ : β ^ p = algebraMap K L A)
    (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (hφ : IsIdelicArtinMap L φ)
    (hφK : ∀ c : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1)
    {α : 𝓞 K} (hprim : TauCeti.IsEisensteinPrimary hζ.toInteger α) {B : Kˣ} (hB : (B : K) = α) :
    hilbertArtin L φ β (lamPlace hζ) B = 1 := by
  set Kl := (lamPlace hζ).adicCompletion K
  obtain ⟨φl, hφl⟩ := (localReciprocityExistence Kl (SeparableClosure Kl)).exists_artin
  have hζ0 : IsUnit ζ := (hζ.isUnit (Fact.out : p.Prime).ne_zero)
  set ζv : Klˣ := unitAt (lamPlace hζ) hζ0.unit
  have hζv : IsPrimitiveRoot ζv p := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    exact hζ.map_of_injective (algebraMap K Kl).injective
  have h1 := hilbertArtin_eq_hilbertPairing L hζ hβ φ hφ hφK (lamPlace hζ) hζv hφl B
  obtain ⟨hcopα, c, d, hd⟩ := hprim
  -- `c` is prime to `p`
  have hpc : ¬ (p : ℤ) ∣ c := by
    intro h
    have hc : hζ.toInteger - 1 ∣ (c : 𝓞 K) :=
      (IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' p hζ).mpr h
    have h2 : hζ.toInteger - 1 ∣ α := by
      have : α = (α - c) + c := by ring
      rw [this, hd]
      exact dvd_add (dvd_mul_of_dvd_left (dvd_pow_self _ two_ne_zero) _) hc
    exact (hζ.zeta_sub_one_prime').not_isUnit (hcopα.isUnit_of_dvd' h2 dvd_rfl)
  have hc0 : (c : K) ≠ 0 := by
    intro h; apply hpc; rw [Int.cast_eq_zero.mp h]; exact dvd_zero _
  -- valuations at `λ`
  have hcval : Valued.v (algebraMap K Kl (c : K)) = 1 := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply]
    have : (c : K) = algebraMap (𝓞 K) K (c : 𝓞 K) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff,
      lamPlace_asIdeal, Ideal.mem_span_singleton]
    intro h
    exact hpc ((IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' p hζ).mp h)
  have hdval : Valued.v (algebraMap K Kl (d : K)) ≤ 1 := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply]
    exact HeightOneSpectrum.valuation_le_one _ d
  set C : Klˣ := unitAt (lamPlace hζ) (Units.mk0 _ hc0)
  have hCc : (C : Kl) = algebraMap K Kl (c : K) := rfl
  have hC0 : (C : Kl) ≠ 0 := C.ne_zero
  set w : Klˣ := unitAt (lamPlace hζ) B * C⁻¹
  have hBw : unitAt (lamPlace hζ) B = C * w := by
    simp only [w]; rw [mul_left_comm, mul_inv_cancel, mul_one]
  set dd : Kl := algebraMap K Kl (d : K) / C
  have hdd : dd ∈ 𝒪[Kl] := by
    rw [HeightOneSpectrum.integer_eq_adicCompletionIntegers, ValuationSubring.mem_toSubring,
      HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hCc, hcval, div_one]
    exact hdval
  have hw : ∃ e : 𝒪[Kl], (w : Kl) = 1 + ((lamInt hζ : 𝒪[Kl]) : Kl) ^ 2 * e := by
    refine ⟨⟨dd, hdd⟩, ?_⟩
    have hαK : (α : K) = c + ((ζ - 1) ^ 2) * d := by
      have := congrArg (fun z : 𝓞 K => (z : K)) hd
      simp only [map_sub, map_mul, map_pow, map_intCast, map_one] at this
      have hz : algebraMap (𝓞 K) K hζ.toInteger = ζ := hζ.coe_toInteger
      rw [← sub_eq_iff_eq_add', this]
      simp only [hz]
    change (unitAt (lamPlace hζ) B * C⁻¹ : Klˣ).val = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, coe_lamInt]
    change algebraMap K Kl (B : K) * (C : Kl)⁻¹ = _
    rw [hB, hαK, map_add, map_mul, map_pow, map_sub, map_one, ← hCc]
    simp only [dd]
    rw [add_mul, mul_inv_cancel₀ hC0, div_eq_mul_inv]
    ring
  have hloc := hilbertPairing_intCast_primary hζ hp2 hζv hφl (unitAt (lamPlace hζ) A) C w
    ⟨a, ha, by simp [hA]⟩ ⟨c, hpc, rfl⟩ hw
  rw [← hBw] at hloc
  apply (algebraMap K Kl).injective
  rw [h1, hloc, Units.val_one, map_one]

/-- Membership in `Sset` for an element of $\mathcal O_K$: $v \in S(x)$ iff $n \in v$ or $x \in v$. -/
theorem mem_Sset_integer_iff (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    v ∈ Sset n {(x : K)} ↔ (n : 𝓞 K) ∈ v.asIdeal ∨ x ∈ v.asIdeal := by
  rw [← not_iff_not, notMem_Sset_iff, not_or, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff]

open Classical in
/-- The local factors of `powerResidueElt` have finite support. -/
theorem mulSupport_elt_finite (n : ℕ) (a b : K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => if v ∈ Sset n {a} then (1 : K) else
      powerResidue n a v ^ FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ b)).Finite := by
  refine (Filter.eventually_cofinite.mp
    (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 K)⁰ b))).subset ?_
  intro v hv h
  apply hv
  simp [h]

/-- **Eisenstein reciprocity in Milne's symbols**: for $a \in \mathbb Z$ prime to $p$ and $\alpha$ primary, prime to
$a$, $(a/\alpha) = (\alpha/a)$ for the symbols `powerResidueElt`. -/
theorem powerResidueElt_eisenstein (hp2 : p ≠ 2) {α : 𝓞 K} {a : ℤ}
    (hprim : TauCeti.IsEisensteinPrimary hζ.toInteger α) (hpa : ¬ (p : ℤ) ∣ a)
    (hcop : IsCoprime α (a : 𝓞 K)) :
    powerResidueElt p (a : K) (α : K) = powerResidueElt p (α : K) (a : K) := by
  classical
  have hp0 : 0 < p := hp.out.pos
  have hpK : IsTotallyComplex K :=
    IsCyclotomicExtension.Rat.isTotallyComplex (n := p) K (lt_of_le_of_ne hp.out.two_le (Ne.symm hp2))
  have ha0 : (a : K) ≠ 0 := by
    intro h; apply hpa; rw [Int.cast_eq_zero.mp h]; exact dvd_zero _
  have hα0 : (α : K) ≠ 0 := by
    intro h
    have h0 : α = 0 := RingOfIntegers.coe_injective (by simpa using h)
    rw [h0] at hprim
    exact (hζ.zeta_sub_one_prime').not_isUnit (hprim.1.isUnit_of_dvd' (dvd_zero _) dvd_rfl)
  set A : Kˣ := Units.mk0 _ ha0
  set B : Kˣ := Units.mk0 _ hα0
  obtain ⟨La, _, _, _, _, β, hβ, hβg⟩ := exists_kummer_field p hp0 ζ hζ (A : K) A.ne_zero
  obtain ⟨Lb, _, _, _, _, γ, hγ, hγg⟩ := exists_kummer_field p hp0 ζ hζ (B : K) B.ne_zero
  set φa := idelicArtinTauCeti La (K := K)
  set φb := idelicArtinTauCeti Lb (K := K)
  have hφa : IsIdelicArtinMap La φa := isIdelicArtinMap_tauCeti La
  have hφb : IsIdelicArtinMap Lb φb := isIdelicArtinMap_tauCeti Lb
  have hφaK : ∀ c : Kˣ, φa (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1 := idelicArtinTauCeti_principal La
  have hφbK : ∀ c : Kˣ, φb (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1 := idelicArtinTauCeti_principal Lb
  have hAa : (A : K) = ((a : 𝓞 K) : K) := by simp [A]
  have hBα : (B : K) = α := rfl
  -- the three local factors
  set f : HeightOneSpectrum (𝓞 K) → K := fun v => hilbertArtin La φa β v B
  set P1 : HeightOneSpectrum (𝓞 K) → K := fun v => if v ∈ Sset p {(A : K)} then 1 else
    powerResidue p (A : K) v ^ FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (B : K))
  set P2 : HeightOneSpectrum (𝓞 K) → K := fun v => if v ∈ Sset p {(B : K)} then 1 else
    powerResidue p (B : K) v ^ FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (A : K))
  -- `S(A) ∩ S(B) = {λ}`
  have hSS : ∀ v, v ∈ Sset p {(A : K)} → v ∈ Sset p {(B : K)} → v = lamPlace hζ := by
    intro v h1 h2
    rw [hAa, mem_Sset_integer_iff] at h1
    rw [hBα, mem_Sset_integer_iff] at h2
    refine eq_lamPlace_of_natCast_mem hζ v ?_
    rcases h1 with h1 | h1
    · exact h1
    rcases h2 with h2 | h2
    · exact h2
    exfalso
    obtain ⟨u, w, huw⟩ := hcop
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr
      (huw ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left u h2) (v.asIdeal.mul_mem_left w h1)))
  have hcount0 : ∀ v (x : Kˣ), v ∉ Sset p {(x : K)} →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 :=
    fun v x hv => count_eq_zero_of_val v _ x.ne_zero ((notMem_Sset_iff v p _).1 hv).2
  have h58a : ∀ v, v ∉ Sset p {(A : K)} → f v = powerResidue p (A : K) v ^
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (B : K)) :=
    fun v hv => item_5_8 La p hp0 ζ hζ (A : K) A.ne_zero β hβ hβg φa hφa v hv B
  have h58b : ∀ v, v ∉ Sset p {(B : K)} → hilbertArtin Lb φb γ v A = powerResidue p (B : K) v ^
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (A : K)) :=
    fun v hv => item_5_8 Lb p hp0 ζ hζ (B : K) B.ne_zero γ hγ hγg φb hφb v hv A
  -- the pointwise identity `f v * P2 v = P1 v`
  have hpt : ∀ v, f v * P2 v = P1 v := by
    intro v
    by_cases hvA : v ∈ Sset p {(A : K)}
    · by_cases hvB : v ∈ Sset p {(B : K)}
      · have hv := hSS v hvA hvB
        subst hv
        simp only [f, P1, P2, hvA, hvB, ite_true, mul_one]
        exact hilbertArtin_lamPlace_eq_one hζ hp2 La hpa (by simp [A]) hβ φa hφa hφaK hprim hBα
      · simp only [f, P1, P2, hvA, hvB, ite_true, ite_false]
        rw [← h58b v hvB]
        exact hilbertArtin_mul_hilbertArtin_swap hζ La Lb hβ hγ φa φb hφa hφb hφaK hφbK v
    · have hP2 : P2 v = 1 := by
        simp only [P2]
        split_ifs
        · rfl
        · rw [hcount0 v A hvA, zpow_zero]
      rw [hP2, mul_one]
      simp only [f, P1, hvA, ite_false]
      exact h58a v hvA
  -- finiteness of the supports
  have hfin1 : (Function.mulSupport P1).Finite := mulSupport_elt_finite p _ _
  have hfin2 : (Function.mulSupport P2).Finite := mulSupport_elt_finite p _ _
  have hfinf : (Function.mulSupport f).Finite := by
    refine (hfin1.union hfin2).subset ?_
    intro v hv
    by_contra hcon
    simp only [Set.mem_union, not_or, Function.mem_mulSupport, not_not] at hcon
    apply hv
    have h1 := hpt v
    rw [hcon.1, hcon.2, mul_one] at h1
    exact h1
  -- the product formula
  have hP := item_5_10 La p hp0 ζ hζ (A : K) A.ne_zero β hβ hβg φa hφa hφaK B
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.out.ne_zero] at hβ
    exact A.ne_zero ((algebraMap K La).injective (by simpa using hβ.symm))
  rw [Finset.prod_eq_one (fun w _ => hilbertArtinInf_totallyComplex La β hβ0 φa hφa w B), mul_one] at hP
  have key : (∏ᶠ v, f v) * ∏ᶠ v, P2 v = ∏ᶠ v, P1 v := by
    rw [← finprod_mul_distrib hfinf hfin2]
    exact finprod_congr hpt
  change (∏ᶠ v, f v) = 1 at hP
  rw [hP, one_mul] at key
  change (∏ᶠ v, P1 v) = ∏ᶠ v, P2 v
  exact key.symm

end Cyclotomic

/-- **The Eisenstein reciprocity law** (Ireland–Rosen, Theorem 14.5.1; the named statement `EisensteinReciprocity`),
proved from the Hilbert reciprocity law for Tau Ceti's idèlic Artin map: for an odd prime $p$, $K = \mathbb Q(\zeta_p)$,
$a \in \mathbb Z$ prime to $p$ and a primary $\alpha \in \mathcal O_K$ prime to $a$, $(\alpha/a)_p = (a/\alpha)_p$. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 5.14 (Eisenstein reciprocity, Ireland–Rosen 14.5.1; proved)"]
theorem eisensteinReciprocity : EisensteinReciprocity := by
  refine ⟨?_⟩
  intro p _ hp2 K _ _ _ ζ hζ α a hprim _ hpa hcop
  have hpα : IsCoprime α (p : 𝓞 K) := by
    refine (IsCyclotomicExtension.Rat.isCoprime_of_not_zeta_sub_one_dvd p hζ ?_).symm
    intro h
    exact (hζ.zeta_sub_one_prime').not_isUnit (hprim.1.isUnit_of_dvd' h dvd_rfl)
  have hap : IsCoprime (a : 𝓞 K) (p : 𝓞 K) := by
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
    have : IsCoprime a (p : ℤ) := (hpZ.irreducible.coprime_iff_not_dvd.mpr hpa).symm
    simpa using this.map (Int.castRingHom (𝓞 K))
  have ha0 : (a : 𝓞 K) ≠ 0 := by
    intro h
    have : (a : K) = 0 := by exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) h
    exact hpa (by rw [Int.cast_eq_zero.mp this]; exact dvd_zero _)
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact (hζ.zeta_sub_one_prime').not_isUnit (hprim.1.isUnit_of_dvd' (dvd_zero _) dvd_rfl)
  have hζ' : IsPrimitiveRoot ζ p := hζ
  have h1 := powerResidueSymbolIdeal_eq_powerResidueElt hζ ha0 hcop.symm hap
  have h2 := powerResidueSymbolIdeal_eq_powerResidueElt hζ hα0 hcop hpα
  have E := powerResidueElt_eisenstein hζ' hp2 hprim hpa hcop
  have hc : (((a : ℤ) : 𝓞 K) : K) = (a : K) := by push_cast; rfl
  rw [hc] at h1 h2
  exact RingOfIntegers.coe_injective (h1.trans (E.symm.trans h2.symm))
