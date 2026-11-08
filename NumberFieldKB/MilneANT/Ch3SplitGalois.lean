import NumberFieldKB.MilneANT.Ch3Split
import NumberFieldKB.MilneCFT.Ch5Complements

/-!
# Milne, *Algebraic Number Theory*, Remark 3.50: a Galois number field is determined by its split primes

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Remark 3.50, p. 65, and Theorem 8.38, p. 149;
bib key `milne2020ant`.

**`galoisDeterminedBySplitPrimes`** proves the named statement `GaloisDeterminedBySplitPrimes` (Ch3Split.lean)
unconditionally: two Galois number fields $K$, $K'$ are isomorphic iff $\mathrm{Spl}(K) = \mathrm{Spl}(K')$.

Proof. The set `splitPrimesQ K` of rational primes $p$ splitting completely in $K$ (primes of $\mathcal O_K$ above
$p\mathbb Z$) corresponds to the set `splitPrimes ℚ K` of primes $v$ of $\mathcal O_{\mathbb Q}$ splitting completely,
through $v \mapsto p_v$ (Mathlib `Rat.HeightOneSpectrum.primesEquiv`; `MilneCFT.mem_splitPrimes_rat_iff` compares
ramification indices and inertia degrees over $\mathbb Z$ and over $\mathcal O_{\mathbb Q}$). Isomorphic fields have
the same split primes (`MilneCFT.splitPrimes_congr_algEquiv`). Conversely, if the split primes agree, each of $K$,
$K'$ embeds in the other (`MilneCFT.nonempty_algHom_of_splitPrimes_diff_finite`, which is Milne's Theorem 8.38,
proved from Chebotarev's theorem with Dirichlet density), so they have the same degree and the embedding is an
isomorphism.
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev

namespace NumberFieldKB.MilneANT

/-- For a prime $v$ of $\mathcal O_{\mathbb Q}$ with residue characteristic $p$: $p$ splits completely in $N$ (in the
sense of `splitPrimesQ`) iff $v$ does (in the sense of `splitPrimes ℚ N`). -/
theorem ratPrime_mem_splitPrimesQ_iff (N : Type) [Field N] [NumberField N] (v : HeightOneSpectrum (𝓞 ℚ)) :
    ratPrime v ∈ splitPrimesQ N ↔ v ∈ splitPrimes ℚ N := by
  rw [MilneCFT.mem_splitPrimes_rat_iff]
  simp only [splitPrimesQ, Set.mem_setOf_eq, Rat.HeightOneSpectrum.prime_natGenerator v, true_and]

/-- `splitPrimesQ` and `splitPrimes ℚ` determine each other. -/
theorem splitPrimesQ_eq_iff (N N' : Type) [Field N] [NumberField N] [Field N'] [NumberField N'] :
    splitPrimesQ N = splitPrimesQ N' ↔ splitPrimes ℚ N = splitPrimes ℚ N' := by
  constructor
  · intro h
    ext v
    rw [← ratPrime_mem_splitPrimesQ_iff, ← ratPrime_mem_splitPrimesQ_iff, h]
  · intro h
    ext p
    by_cases hp : p.Prime
    · let E : HeightOneSpectrum (𝓞 ℚ) ≃ Nat.Primes := Rat.HeightOneSpectrum.primesEquiv
      let v : HeightOneSpectrum (𝓞 ℚ) := E.symm ⟨p, hp⟩
      have hv : ratPrime v = p := by
        have := congrArg Subtype.val (E.apply_symm_apply ⟨p, hp⟩)
        exact this
      rw [← hv, ratPrime_mem_splitPrimesQ_iff, ratPrime_mem_splitPrimesQ_iff, h]
    · simp [splitPrimesQ, hp]

/-- An embedding between number fields of the same degree over $\mathbb Q$ is an isomorphism. -/
private theorem nonempty_algEquiv_of_algHom (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    (f : K →ₐ[ℚ] K') (g : K' →ₐ[ℚ] K) : Nonempty (K ≃ₐ[ℚ] K') := by
  have h1 : Module.finrank ℚ K ≤ Module.finrank ℚ K' :=
    LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) f.toRingHom.injective
  have h2 : Module.finrank ℚ K' ≤ Module.finrank ℚ K :=
    LinearMap.finrank_le_finrank_of_injective (f := g.toLinearMap) g.toRingHom.injective
  have hsurj : Function.Surjective f := by
    have hinj : Function.Injective f.toLinearMap := f.toRingHom.injective
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm h1 h2)).mp hinj
  exact ⟨AlgEquiv.ofBijective f ⟨f.toRingHom.injective, hsurj⟩⟩

/-- **Remark 3.50**, second assertion (Milne's Theorem 8.38; proved, unconditionally): two Galois number fields are
isomorphic iff the same rational primes split completely in them. The named statement
`GaloisDeterminedBySplitPrimes` holds. -/
@[kb "milne2020ant" "v3.08, Remark 3.50 and Thm. 8.38, p. 65"]
theorem galoisDeterminedBySplitPrimes : GaloisDeterminedBySplitPrimes where
  iff K K' _ _ _ _ _ _ := by
    constructor
    · rintro ⟨e⟩
      exact (splitPrimesQ_eq_iff K K').mpr (MilneCFT.splitPrimes_congr_algEquiv e)
    · intro h
      have h' := (splitPrimesQ_eq_iff K K').mp h
      obtain ⟨f⟩ := MilneCFT.nonempty_algHom_of_splitPrimes_diff_finite (K := ℚ) K K' ∅ Set.finite_empty
        (by rw [Set.diff_empty, h'])
      obtain ⟨g⟩ := MilneCFT.nonempty_algHom_of_splitPrimes_diff_finite (K := ℚ) K' K ∅ Set.finite_empty
        (by rw [Set.diff_empty, h'])
      exact nonempty_algEquiv_of_algHom K K' f g

end NumberFieldKB.MilneANT
