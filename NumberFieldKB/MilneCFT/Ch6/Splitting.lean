import NumberFieldKB.MilneCFT.Intro.Theorems
import NumberFieldKB.MilneANT.Ch8DedekindProof
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Ring.Star

/-!
# Milne, *Class Field Theory*, Chapter VI §3: primes splitting in an extension

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

* **Example 3.7** (`example_3_7`): for a monic irreducible cubic $f$ over $\mathbb Z$, the primes modulo which $f$
  splits into linear factors have Dirichlet density $1/3$ or $1/6$ according as the Galois group is $C_3$ or $S_3$.
  Proved from Dedekind's theorem (`NumberFieldKB.MilneANT.dedekindFrobenius`) and the unconditional Chebotarev
  theorem of this library, via Milne, *ANT*, Example 8.36. Milne's "density" in §3 is the polar density; the polar
  form needs Theorem 3.4 in polar form (open), the Dirichlet form is proved here.
* **Corollary 3.8** (`cor_3_8`): for an abelian extension $L/K$ and a finite set $S$ of primes containing the ramified
  ones, the Artin map $I^S\to\mathrm{Gal}(L/K)$ is surjective. Proved from Chebotarev (every element of the Galois
  group is a Frobenius element at infinitely many primes), as in Milne's proof (which uses Theorem 3.4).
-/

open NumberField IsDedekindDomain Polynomial
open NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField NumberFieldKB.MilneANT

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch6

/-! ## Example 3.7 -/

/-- The primes $p$ of $\mathbb Q$ modulo which $f\in\mathbb Z[X]$ splits into linear factors. -/
def splitModPrimes (f : (𝓞 ℚ)[X]) : Set (HeightOneSpectrum (𝓞 ℚ)) :=
  {v | (f.map (algebraMap (𝓞 ℚ) v.asIdeal.ResidueField)).Splits}

open UniqueFactorizationMonoid in
theorem splits_iff_nf {k : Type*} [Field k] [DecidableEq k] (P : k[X]) (hm : P.Monic)
    (h3 : P.natDegree = 3) :
    P.Splits ↔ (UniqueFactorizationMonoid.normalizedFactors P).map natDegree = {1, 1, 1} := by
  have hP : P ≠ 0 := hm.ne_zero
  have hassoc : Associated (normalizedFactors P).prod P := prod_normalizedFactors hP
  constructor
  · intro hs
    have h1 : ∀ q ∈ normalizedFactors P, q.natDegree = 1 := by
      intro q hq
      have hirr := irreducible_of_normalized_factor q hq
      have hd : q ∣ P := dvd_of_mem_normalizedFactors hq
      have := (hs.of_dvd hP hd).natDegree_le_one_of_irreducible hirr
      have := hirr.natDegree_pos
      omega
    have hsum : ((normalizedFactors P).map natDegree).sum = 3 := by
      rw [← h3, ← natDegree_multiset_prod _ (zero_notMem_normalizedFactors _)]
      exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)
    have hrep : (normalizedFactors P).map natDegree =
        Multiset.replicate (normalizedFactors P).card 1 := by
      rw [Multiset.eq_replicate]
      refine ⟨by simp, fun b hb => ?_⟩
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hb
      exact h1 q hq
    rw [hrep] at hsum ⊢
    simp at hsum
    rw [hsum]; rfl
  · intro h
    have h1 : ∀ q ∈ normalizedFactors P, q.natDegree = 1 := by
      intro q hq
      have : q.natDegree ∈ (normalizedFactors P).map natDegree := Multiset.mem_map_of_mem _ hq
      rw [h] at this
      simpa using this
    have hs : (normalizedFactors P).prod.Splits := by
      apply Splits.multisetProd
      intro q hq
      have hq0 : q ≠ 0 := ne_zero_of_mem_normalizedFactors hq
      have hmo : q.Monic := by
        have := normalize_normalized_factor q hq
        rw [← this]; exact monic_normalize hq0
      exact Splits.of_natDegree_le_one_of_monic (h1 q hq).le hmo
    obtain ⟨u, hu⟩ := hassoc
    rw [← hu]
    exact hs.mul u.isUnit.splits

theorem splitModPrimes_symmDiff_finite (f : (𝓞 ℚ)[X]) (hf : f.Monic) (h3 : f.natDegree = 3)
    (hs : (f.map (algebraMap (𝓞 ℚ) ℚ)).Separable) :
    (symmDiff (splitModPrimes f) (factorizationTypeSet f {1, 1, 1})).Finite := by
  classical
  refine (finite_not_squarefree f hs).subset ?_
  intro 𝔭 h𝔭
  by_contra hn
  have hsq : Squarefree (f.map (algebraMap (𝓞 ℚ) 𝔭.asIdeal.ResidueField)) := not_not.1 hn
  have hm := hf.map (algebraMap (𝓞 ℚ) 𝔭.asIdeal.ResidueField)
  have hd : (f.map (algebraMap (𝓞 ℚ) 𝔭.asIdeal.ResidueField)).natDegree = 3 := by
    rw [hf.natDegree_map]; exact h3
  have key : 𝔭 ∈ splitModPrimes f ↔ 𝔭 ∈ factorizationTypeSet f {1, 1, 1} := by
    constructor
    · intro h
      exact ⟨hsq, (splits_iff_nf _ hm hd).1 h⟩
    · intro h
      exact (splits_iff_nf _ hm hd).2 h.2
  rcases Set.mem_symmDiff.1 h𝔭 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (key.1 h1)
  · exact h2 (key.2 h1)

/-- **Example 3.7** (Milne, *CFT*, Chapter VI, p. 193): let $f$ be an irreducible polynomial of degree $3$ (here monic
with integer coefficients; a rational cubic becomes one after scaling the variable, which changes finitely many
reductions). Its Galois group has order $3$ ($C_3$) or $6$ ($S_3$), and the set of primes $p$ for which $f$ splits
modulo $p$ has (Dirichlet) density $1/3$, respectively $1/6$. -/
@[kb "milne2020cft" "Ch. VI, Example 3.7 (Dirichlet density)"]
theorem example_3_7 (f : (𝓞 ℚ)[X]) (hf : f.Monic) (h3 : f.natDegree = 3)
    (hirr : Irreducible (f.map (algebraMap (𝓞 ℚ) ℚ))) :
    (Nat.card (f.map (algebraMap (𝓞 ℚ) ℚ)).Gal = 3 ∨ Nat.card (f.map (algebraMap (𝓞 ℚ) ℚ)).Gal = 6) ∧
    (Nat.card (f.map (algebraMap (𝓞 ℚ) ℚ)).Gal = 3 → (splitModPrimes f).HasDirichletDensity (1 / 3)) ∧
    (Nat.card (f.map (algebraMap (𝓞 ℚ) ℚ)).Gal = 6 → (splitModPrimes f).HasDirichletDensity (1 / 6)) := by
  classical
  have hdeg : (f.map (algebraMap (𝓞 ℚ) ℚ)).natDegree = 3 := by
    rw [natDegree_map_eq_of_injective (IsFractionRing.injective (𝓞 ℚ) ℚ)]
    exact h3
  set g := f.map (algebraMap (𝓞 ℚ) ℚ) with hg
  have hs : g.Separable := hirr.separable
  have hcard : Fintype.card (g.rootSet g.SplittingField) = 3 :=
    (card_rootSet_splittingField g hs).trans hdeg
  have hφ := galPerm_injective g
  have hdvd3 : 3 ∣ Nat.card g.Gal := by
    have := Polynomial.Gal.prime_degree_dvd_card hirr (by rw [hdeg]; norm_num)
    rwa [hdeg] at this
  have hdvd6 : Nat.card g.Gal ∣ 6 := by
    have h1 : Nat.card (MonoidHom.range (MulAction.toPermHom g.Gal (g.rootSet g.SplittingField))) ∣
        Nat.card (Equiv.Perm (g.rootSet g.SplittingField)) := Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm, Nat.card_eq_fintype_card (α := Equiv.Perm _),
      Fintype.card_perm, hcard] at h1
    exact h1
  have hcases : Nat.card g.Gal = 3 ∨ Nat.card g.Gal = 6 := by
    have hle : Nat.card g.Gal ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
    generalize Nat.card g.Gal = n at *
    obtain ⟨m, rfl⟩ := hdvd3
    have hm2 : m ≤ 2 := by omega
    interval_cases m <;> simp_all
  have hN : ∀ n : ℕ, Nat.card g.Gal = n → Fintype.card g.Gal = n := fun n h => by
    rwa [← Nat.card_eq_fintype_card]
  have key := factorizationType_hasDirichletDensity dedekindFrobenius f hf hs {1, 1, 1}
  have hc : Nat.card {σ : g.Gal // (galPerm g σ).partition.parts = {1, 1, 1}} = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact count3_triv _ hφ hcard
  rw [hc] at key
  have hsd := splitModPrimes_symmDiff_finite f hf h3 hs
  refine ⟨hcases, fun h => ?_, fun h => ?_⟩
  · rw [h] at key
    refine HasDirichletDensity.congr_finite (S := factorizationTypeSet f {1, 1, 1}) (by simpa using key) ?_
    rw [symmDiff_comm]; exact hsd
  · rw [h] at key
    refine HasDirichletDensity.congr_finite (S := factorizationTypeSet f {1, 1, 1}) (by simpa using key) ?_
    rw [symmDiff_comm]; exact hsd

/-! ## Corollary 3.8 -/

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **Corollary 3.8** (Milne, *CFT*, Chapter VI, p. 193): for every abelian extension $L/K$ and every finite set $S$ of
primes of $K$ containing those that ramify in $L$, the Artin map $\psi_{L/K} : I^S\to\mathrm{Gal}(L/K)$ is
surjective. The finite primes of $S$ are those dividing a modulus $\mathfrak m$, so $I^S$ is `coprimeIdeals m`; the
Artin map is any homomorphism sending each prime $\mathfrak p\notin S$ to its Frobenius element (it is unique, the
primes not in $S$ generating $I^S$). -/
@[kb "milne2020cft" "Ch. VI, Cor. 3.8"]
theorem cor_3_8 (_hab : ∀ σ τ : Gal(L/K), σ * τ = τ * σ) (m : Modulus K)
    (_hm : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ unramifiedPrimes K L → v.asIdeal ∣ m.finite)
    (ψ : coprimeIdeals m →* Gal(L/K))
    (hψ : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite) (Q : v.asIdeal.primesOver (𝓞 L)),
      ψ (coprimePrime m v hv) = frobAt K L v Q) :
    Function.Surjective ψ := by
  intro σ
  have hinf := setOf_frobAt_eq_infinite K L σ
  have hfin : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ m.finite}.Finite :=
    Ideal.finite_factors m.finite_ne_bot
  obtain ⟨v, ⟨hv, Q, hQ⟩, hvm⟩ := (hinf.sdiff hfin).nonempty
  exact ⟨coprimePrime m v hvm, (hψ v hvm Q).trans hQ⟩

end NumberFieldKB.MilneCFT.Ch6
