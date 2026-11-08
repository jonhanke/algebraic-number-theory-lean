import QuadFormsKB.Analysis.NFEulerProduct

/-!
# The Chebotarev density theorem: definitions and the density toolkit

The sorry-free API of the Chebotarev development, split off from `NumberFieldKB.Chebotarev.Statements` so
that the proof files can import it. The statements themselves (and their proofs) live in
`DensityTools.lean`, `FrobeniusPrimes.lean`, `Crossing.lean`, `Cyclotomic.lean`, `Descent.lean`, `Cyclic.lean` and
`Statements.lean`.

* Primes of $K$ are `HeightOneSpectrum (𝓞 K)` (forced by Mathlib's `NumberField.Set.HasDirichletDensity`).
* `frobAt K L 𝔭 Q`: the Frobenius element `arithFrobAt` of Mathlib at a prime `Q ∈ 𝔭.primesOver (𝓞 L)`.
* `frobClass K L 𝔭`: its conjugacy class, for an arbitrary `Q` over `𝔭`; it does not depend on `Q`
  (`frobClass_eq_mk_frobAt`).
* `unramifiedPrimes K L`, `frobSet K L C` (unramified primes with Frobenius class `C`), `splitPrimes K L`
  (every prime above has $e = f = 1$).
* `dirichletRatio`, additivity over finite disjoint families, the partition lemma
  `hasDirichletDensity_of_partition_iUnion`.
* `exists_prime_one_mod_not_dvd_discr`, `card_dvd_orderOf_ge` (counting for the cyclic case), `toFixedFieldGal`.
-/

open NumberField IsDedekindDomain Filter Topology Set

namespace NumberFieldKB.Chebotarev

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## §0. Frobenius classes of primes of `K` -/

section Frobenius

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- A prime of `𝓞 L` over a nonzero prime of `𝓞 K` is maximal (so its residue ring is a finite field). -/
theorem isMaximal_of_mem_primesOver (𝔭 : HeightOneSpectrum (𝓞 K)) (Q : 𝔭.asIdeal.primesOver (𝓞 L)) :
    Q.1.IsMaximal := by
  have := Q.2.1
  have := Q.2.2
  exact Q.2.1.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q.1)

variable [IsGalois K L]

/-- **The Frobenius element at `Q`**: Mathlib's `arithFrobAt` for the action of $\mathrm{Gal}(L/K)$ on `𝓞 L`. It
satisfies $\mathrm{Frob}_Q(x) \equiv x^{N\mathfrak p} \pmod Q$ (`isArithFrobAt_frobAt`); it is unique when
$\mathfrak p$ is unramified (`frobAt_eq_of_isArithFrobAt`) and an arbitrary choice modulo inertia otherwise. -/
def frobAt (𝔭 : HeightOneSpectrum (𝓞 K)) (Q : 𝔭.asIdeal.primesOver (𝓞 L)) : Gal(L/K) :=
  haveI := Q.2.1
  haveI := isMaximal_of_mem_primesOver K L 𝔭 Q
  arithFrobAt (𝓞 K) Gal(L/K) Q.1

theorem isArithFrobAt_frobAt (𝔭 : HeightOneSpectrum (𝓞 K)) (Q : 𝔭.asIdeal.primesOver (𝓞 L)) :
    IsArithFrobAt (𝓞 K) (frobAt K L 𝔭 Q) Q.1 := by
  haveI := Q.2.1
  haveI := isMaximal_of_mem_primesOver K L 𝔭 Q
  exact IsArithFrobAt.arithFrobAt (𝓞 K) Gal(L/K) Q.1

/-- **The Frobenius class of a prime `𝔭` of `K`**: the conjugacy class of `frobAt K L 𝔭 Q` for an arbitrary prime
`Q` of `𝓞 L` above `𝔭`. It does not depend on `Q` (`frobClass_eq_mk_frobAt`). For ramified `𝔭` it is only one of
several classes (Frobenius elements are unique modulo inertia); the density statements only use unramified `𝔭`. -/
def frobClass (𝔭 : HeightOneSpectrum (𝓞 K)) : ConjClasses Gal(L/K) :=
  ConjClasses.mk (frobAt K L 𝔭 (Classical.arbitrary _))

/-- The Frobenius class does not depend on the prime above `𝔭` (*proved*, from Mathlib's `isConj_arithFrobAt`). -/
theorem frobClass_eq_mk_frobAt (𝔭 : HeightOneSpectrum (𝓞 K)) (Q : 𝔭.asIdeal.primesOver (𝓞 L)) :
    frobClass K L 𝔭 = ConjClasses.mk (frobAt K L 𝔭 Q) := by
  unfold frobClass frobAt
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  set Q₀ : 𝔭.asIdeal.primesOver (𝓞 L) := Classical.arbitrary _
  haveI := Q₀.2.1
  haveI := Q₀.2.2
  haveI := isMaximal_of_mem_primesOver K L 𝔭 Q₀
  haveI := Q.2.1
  haveI := Q.2.2
  haveI := isMaximal_of_mem_primesOver K L 𝔭 Q
  exact isConj_arithFrobAt (𝓞 K) Gal(L/K) Q₀.1 Q.1
    ((Ideal.LiesOver.over (P := Q₀.1) (p := 𝔭.asIdeal)).symm.trans Ideal.LiesOver.over)

/-- The primes of `K` that are unramified in `L` (Mathlib's `Algebra.IsUnramifiedIn`: every prime of `𝓞 L` above
is unramified, i.e. $e = 1$ and the residue extension is separable). -/
def unramifiedPrimes : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔭 | Algebra.IsUnramifiedIn (𝓞 L) 𝔭.asIdeal}

/-- **The Chebotarev set** of a conjugacy class `C`: the unramified primes of `K` with Frobenius class `C`. -/
def frobSet (C : ConjClasses Gal(L/K)) : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔭 | 𝔭 ∈ unramifiedPrimes K L ∧ frobClass K L 𝔭 = C}

/-- The primes of `K` that **split completely** in `L`: every prime above has ramification index and inertia degree
`1`. Defined intrinsically (not through Frobenius) so that Milne 8.32 is a genuine statement. -/
def splitPrimes : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔭 | ∀ Q : 𝔭.asIdeal.primesOver (𝓞 L),
    Q.1.ramificationIdx (𝓞 K) = 1 ∧ Q.1.inertiaDeg (𝓞 K) = 1}

/-- **Uniqueness of Frobenius at an unramified prime** (*proved*): any `σ` with
$\sigma(x) \equiv x^{N\mathfrak p} \pmod Q$ is `frobAt K L 𝔭 Q`. From Mathlib's
`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt` and faithfulness of the action on `𝓞 L`. -/
theorem frobAt_eq_of_isArithFrobAt {𝔭 : HeightOneSpectrum (𝓞 K)} (h𝔭 : 𝔭 ∈ unramifiedPrimes K L)
    (Q : 𝔭.asIdeal.primesOver (𝓞 L)) {σ : Gal(L/K)} (hσ : IsArithFrobAt (𝓞 K) σ Q.1) :
    frobAt K L 𝔭 Q = σ := by
  haveI := Q.2.1
  haveI := Q.2.2
  haveI := isMaximal_of_mem_primesOver K L 𝔭 Q
  haveI : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := h𝔭 Q.1 Q.2.1 Q.2.2
  have h := (isArithFrobAt_frobAt K L 𝔭 Q).eq_of_isUnramifiedAt hσ
    (Ideal.primeCompl_le_nonZeroDivisors Q.1)
  haveI : FaithfulSMul Gal(L/K) (𝓞 L) := IsGaloisGroup.faithful (A := 𝓞 K)
  exact FaithfulSMul.eq_of_smul_eq_smul (α := 𝓞 L) fun x => DFunLike.congr_fun h x

end Frobenius

/-! ## §1. Density toolkit -/

section Density

variable {F : Type} [Field F] [NumberField F]

/-- The Dirichlet ratio $\sum_{\mathfrak p \in S} N\mathfrak p^{-s} / \sum_{\mathfrak p} N\mathfrak p^{-s}$ whose
limit as $s \to 1^+$ is the Dirichlet density (`NumberField.Set.HasDirichletDensity`, Mathlib). -/
def dirichletRatio (S : Set (HeightOneSpectrum (𝓞 F))) (s : ℝ) : ℝ :=
  S.primeIdealZetaSum s / (univ : Set (HeightOneSpectrum (𝓞 F))).primeIdealZetaSum s

theorem hasDirichletDensity_iff (S : Set (HeightOneSpectrum (𝓞 F))) (δ : ℝ) :
    S.HasDirichletDensity δ ↔ Tendsto (dirichletRatio S) (𝓝[>] 1) (𝓝 δ) := Iff.rfl

theorem summable_absNorm_rpow_subtype (S : Set (HeightOneSpectrum (𝓞 F))) {s : ℝ} (hs : 1 < s) :
    Summable ((fun 𝔭 : HeightOneSpectrum (𝓞 F) => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) ∘
      ((↑) : S → HeightOneSpectrum (𝓞 F))) :=
  (QuadFormsKB.NFEuler.summable_normP_rpow (F := F) hs).subtype S

theorem primeIdealZetaSum_union_disjoint {S T : Set (HeightOneSpectrum (𝓞 F))} (hST : Disjoint S T)
    {s : ℝ} (hs : 1 < s) :
    (S ∪ T).primeIdealZetaSum s = S.primeIdealZetaSum s + T.primeIdealZetaSum s := by
  simp only [Set.primeIdealZetaSum_def]
  exact Summable.tsum_union_disjoint hST (summable_absNorm_rpow_subtype S hs)
    (summable_absNorm_rpow_subtype T hs)

/-- For $s > 1$ the partial sums add over a finite disjoint family (*proved*). -/
theorem primeIdealZetaSum_iUnion {ι : Type} [Fintype ι] (S : ι → Set (HeightOneSpectrum (𝓞 F)))
    (hS : Pairwise (Function.onFun Disjoint S)) {s : ℝ} (hs : 1 < s) :
    (⋃ i, S i).primeIdealZetaSum s = ∑ i, (S i).primeIdealZetaSum s := by
  have hU : (⋃ i, S i) = ⋃ i ∈ (Finset.univ : Finset ι), S i := by simp
  simp only [Set.primeIdealZetaSum_def]
  rw [hU]
  exact Summable.tsum_finset_bUnion_disjoint (fun i _ j _ hij => hS hij)
    (fun i _ => summable_absNorm_rpow_subtype (S i) hs)

/-- For $s > 1$ the Dirichlet ratios add over a finite disjoint family (*proved*). -/
theorem dirichletRatio_iUnion {ι : Type} [Fintype ι] (S : ι → Set (HeightOneSpectrum (𝓞 F)))
    (hS : Pairwise (Function.onFun Disjoint S)) {s : ℝ} (hs : 1 < s) :
    dirichletRatio (⋃ i, S i) s = ∑ i, dirichletRatio (S i) s := by
  simp only [dirichletRatio, primeIdealZetaSum_iUnion S hS hs, Finset.sum_div]

/-- **Additivity** (*proved*): disjoint sets with densities `a`, `b` have union of density `a + b`. -/
theorem HasDirichletDensity.disjoint_union {S T : Set (HeightOneSpectrum (𝓞 F))} {a b : ℝ}
    (hS : S.HasDirichletDensity a) (hT : T.HasDirichletDensity b) (hST : Disjoint S T) :
    (S ∪ T).HasDirichletDensity (a + b) := by
  rw [hasDirichletDensity_iff] at *
  refine (hS.add hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  simp only [dirichletRatio, Set.primeIdealZetaSum_def]
  rw [Summable.tsum_union_disjoint hST (summable_absNorm_rpow_subtype S hs)
    (summable_absNorm_rpow_subtype T hs), add_div]

/-- **The partition step** (*proved*): if finitely many pairwise disjoint sets `S i` have
union of density `D`, and each has lower density at least `a i` with $\sum_i a_i = D$, then each `S i` has density
exactly `a i`. "Lower density at least `a`" is written out: for every `b < a`, eventually (as $s \to 1^+$) the
Dirichlet ratio is at least `b`. -/
theorem hasDirichletDensity_of_partition_iUnion {ι : Type} [Fintype ι] (S : ι → Set (HeightOneSpectrum (𝓞 F)))
    (hS : Pairwise (Function.onFun Disjoint S)) {D : ℝ} (hD : (⋃ i, S i).HasDirichletDensity D) (a : ι → ℝ)
    (ha : ∑ i, a i = D) (hlow : ∀ i, ∀ b < a i, ∀ᶠ s in 𝓝[>] 1, b ≤ dirichletRatio (S i) s) (i : ι) :
    (S i).HasDirichletDensity (a i) := by
  classical
  rw [hasDirichletDensity_iff] at hD ⊢
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨b', hbb', hb'⟩ := exists_between hb
    filter_upwards [hlow i b' hb'] with s hs
    exact hbb'.trans_le hs
  · set ε : ℝ := (b - a i) / (Fintype.card ι + 2) with hε
    have hcard : (0 : ℝ) < Fintype.card ι + 2 := by positivity
    have hεpos : 0 < ε := div_pos (by linarith) hcard
    have hεb : (Fintype.card ι : ℝ) * ε + 2 * ε = b - a i := by
      rw [← add_mul, hε, mul_div_cancel₀ _ hcard.ne']
    have hup := (tendsto_order.1 hD).2 (D + ε) (by linarith)
    have hlow' : ∀ᶠ s in 𝓝[>] 1, ∀ j, a j - ε ≤ dirichletRatio (S j) s :=
      Filter.eventually_all.2 fun j => hlow j (a j - ε) (by linarith)
    filter_upwards [hup, hlow', self_mem_nhdsWithin] with s hs1 hs2 (hs3 : 1 < s)
    have hsum := dirichletRatio_iUnion S hS hs3
    have e1 := Finset.add_sum_erase Finset.univ (fun j => dirichletRatio (S j) s) (Finset.mem_univ i)
    have e2 := Finset.add_sum_erase Finset.univ a (Finset.mem_univ i)
    have h3 : ∑ j ∈ Finset.univ.erase i, (a j - ε) ≤
        ∑ j ∈ Finset.univ.erase i, dirichletRatio (S j) s :=
      Finset.sum_le_sum fun j _ => hs2 j
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h3
    have h4 : ((Finset.univ.erase i).card : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast (Finset.card_erase_le).trans (le_of_eq Finset.card_univ)
    have h5 : ((Finset.univ.erase i).card : ℝ) * ε ≤ (Fintype.card ι : ℝ) * ε :=
      mul_le_mul_of_nonneg_right h4 hεpos.le
    rw [← ha] at hs1
    linarith

end Density

section Cyclic

/-- *Proved*, from Mathlib's Dirichlet theorem `Nat.infinite_setOfPred_prime_and_eq_mod`. **Choice of
the auxiliary prime**: for every `N ≥ 1` there is a prime $\ell \equiv 1 \pmod N$ not dividing the discriminant of
`L` (so $\ell$ is unramified in $L/\mathbb Q$). -/
theorem exists_prime_one_mod_not_dvd_discr (L : Type) [Field L] [NumberField L] (N : ℕ) (hN : 0 < N) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ N ∣ ℓ - 1 ∧ ¬ (ℓ : ℤ) ∣ NumberField.discr L := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hinf := Nat.infinite_setOfPred_prime_and_eq_mod (q := N) (a := 1) isUnit_one
  have hfin : {ℓ : ℕ | (ℓ : ℤ) ∣ NumberField.discr L}.Finite := by
    refine (Set.finite_Iic (NumberField.discr L).natAbs).subset fun ℓ hℓ => ?_
    have h := Int.natAbs_dvd_natAbs.mpr (show (ℓ : ℤ) ∣ NumberField.discr L from hℓ)
    rw [Int.natAbs_natCast] at h
    exact Set.mem_Iic.mpr (Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)) h)
  obtain ⟨ℓ, ⟨hℓp, hℓ1⟩, hℓd⟩ := (hinf.sdiff hfin).nonempty
  refine ⟨ℓ, hℓp, ?_, hℓd⟩
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hℓp.one_le, hℓ1, Nat.cast_one, sub_self]

/-- *Proved.* **Most elements of a cyclic group have order divisible by
`d`**: in a finite cyclic group `A` with $n^k \mid |A|$ ($k \ge 1$), and $d \mid n$, the elements whose order is divisible by
`d` make up at least a fraction $1 - \omega(n)/2^k$ of `A` ($\omega(n)$ = number of prime factors of `n`). -/
theorem card_dvd_orderOf_ge (A : Type) [CommGroup A] [Finite A] [IsCyclic A] {n d k : ℕ} (hn : 0 < n)
    (hk1 : 0 < k) (hd : d ∣ n) (hk : n ^ k ∣ Nat.card A) :
    (1 - (n.primeFactors.card : ℝ) / 2 ^ k) * Nat.card A ≤ {τ : A | d ∣ orderOf τ}.ncard := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  set N := Nat.card A with hN
  have hN0 : 0 < N := Nat.card_pos
  have hd0 : d ≠ 0 := by rintro rfl; exact hn.ne' (Nat.eq_zero_of_zero_dvd hd)
  -- a bad `τ` is killed by `N / q ^ k` for some prime `q ∣ n`
  have key : ∀ τ : A, ¬ d ∣ orderOf τ → ∃ q ∈ n.primeFactors, τ ^ (N / q ^ k) = 1 := by
    intro τ hτ
    have ho0 : orderOf τ ≠ 0 := (orderOf_pos τ).ne'
    have hoN : orderOf τ ∣ N := orderOf_dvd_natCard τ
    rw [← Nat.factorization_le_iff_dvd hd0 ho0, Finsupp.le_def] at hτ
    simp only [not_forall, not_le] at hτ
    obtain ⟨q, hq⟩ := hτ
    have hqd : q ∈ d.primeFactors := by
      rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.2 (by omega)
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqd
    have hqn : q ∈ n.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hqp, (Nat.dvd_of_mem_primeFactors hqd).trans hd, hn.ne'⟩
    have hqk : q ^ k ∣ N := (pow_dvd_pow_of_dvd (Nat.dvd_of_mem_primeFactors hqn) k).trans hk
    refine ⟨q, hqn, orderOf_dvd_iff_pow_eq_one.1 ?_⟩
    have hNq0 : N / q ^ k ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd hN0 hqk) (pow_pos hqp.pos k)).ne'
    rw [← Nat.factorization_le_iff_dvd ho0 hNq0, Nat.factorization_div hqk, Finsupp.le_def]
    intro r
    have hoNr := (Nat.factorization_le_iff_dvd ho0 hN0.ne').2 hoN r
    rw [Finsupp.coe_tsub, Pi.sub_apply, hqp.factorization_pow, Finsupp.single_apply]
    by_cases hrq : q = r
    · subst hrq
      simp only [ite_true]
      have h1 : (n ^ k).factorization q ≤ N.factorization q :=
        (Nat.factorization_le_iff_dvd (pow_ne_zero _ hn.ne') hN0.ne').2 hk q
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at h1
      have h2 : d.factorization q ≤ n.factorization q :=
        (Nat.factorization_le_iff_dvd hd0 hn.ne').2 hd q
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨a', ha'⟩ : ∃ a', d.factorization q = a' + 1 := ⟨d.factorization q - 1, by omega⟩
      have h3 : (k' + 1) * (a' + 1) ≤ (k' + 1) * n.factorization q :=
        Nat.mul_le_mul_left _ (ha' ▸ h2)
      have h4 : (k' + 1) * (a' + 1) = k' * a' + k' + a' + 1 := by ring
      omega
    · simp only [hrq, ite_false, tsub_zero]
      exact hoNr
  have hset : {τ : A | d ∣ orderOf τ} = ↑(Finset.univ.filter fun τ : A => d ∣ orderOf τ) := by
    ext; simp
  rw [hset, Set.ncard_coe_finset]
  have hbad : (Finset.univ.filter fun τ : A => ¬ d ∣ orderOf τ) ⊆
      n.primeFactors.biUnion fun q => Finset.univ.filter fun τ : A => τ ^ (N / q ^ k) = 1 := by
    intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact key τ hτ
  have hcardq : ∀ q ∈ n.primeFactors,
      ((Finset.univ.filter fun τ : A => τ ^ (N / q ^ k) = 1).card : ℝ) ≤ N / 2 ^ k := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqk : q ^ k ∣ N := (pow_dvd_pow_of_dvd (Nat.dvd_of_mem_primeFactors hq) k).trans hk
    have h1 := IsCyclic.card_pow_eq_one_le (α := A) (n := N / q ^ k)
      (Nat.div_pos (Nat.le_of_dvd hN0 hqk) (pow_pos hqp.pos k))
    have hq2 : (2 : ℝ) ^ k ≤ (q : ℝ) ^ k :=
      pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hqp.two_le) k
    calc ((Finset.univ.filter fun τ : A => τ ^ (N / q ^ k) = 1).card : ℝ)
        ≤ ((N / q ^ k : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (N : ℝ) / (q : ℝ) ^ k := by
          rw [Nat.cast_div hqk (by have := hqp.pos; positivity)]; push_cast; ring
      _ ≤ N / 2 ^ k := div_le_div_of_nonneg_left (by positivity) (by positivity) hq2
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset A))
    (fun τ : A => d ∣ orderOf τ)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hsplit
  have hb1 : ((Finset.univ.filter fun τ : A => ¬ d ∣ orderOf τ).card : ℝ) ≤
      ∑ q ∈ n.primeFactors, ((Finset.univ.filter fun τ : A => τ ^ (N / q ^ k) = 1).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hbad).trans Finset.card_biUnion_le
  have hb2 : ∑ q ∈ n.primeFactors, ((Finset.univ.filter fun τ : A => τ ^ (N / q ^ k) = 1).card : ℝ) ≤
      n.primeFactors.card * ((N : ℝ) / 2 ^ k) := by
    have := Finset.sum_le_sum hcardq
    rwa [Finset.sum_const, nsmul_eq_mul] at this
  have hs : ((Finset.univ.filter fun τ : A => d ∣ orderOf τ).card : ℝ) +
      ((Finset.univ.filter fun τ : A => ¬ d ∣ orderOf τ).card : ℝ) = N := by
    exact_mod_cast hsplit
  have : (1 - (n.primeFactors.card : ℝ) / 2 ^ k) * N = N - n.primeFactors.card * ((N : ℝ) / 2 ^ k) := by
    ring
  rw [this]
  linarith

end Cyclic

section Deuring

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- `σ` as an element of $\mathrm{Gal}(L/E)$, $E = L^{\langle\sigma\rangle}$. -/
def toFixedFieldGal (σ : Gal(L/K)) : Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))) :=
  IntermediateField.fixingSubgroupEquiv _
    ⟨σ, by rw [IntermediateField.fixingSubgroup_fixedField]; exact Subgroup.mem_zpowers σ⟩

end Deuring

end

end NumberFieldKB.Chebotarev
