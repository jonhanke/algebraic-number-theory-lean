import NumberFieldKB.MilneANT.Ch7Prop764Zero

/-!
# Erratum (statement fidelity) for Milne, Proposition 7.64

Erratum (statement fidelity) for Milne, *Algebraic Number Theory* v3.08, Prop. 7.64, p. 133 (bib key `milne2020ant`):
the named statement `Prop7_64` quantifies over $n = 0$ (`finrank = 0` means subfields of infinite degree) and is
**false** there; Milne means extensions of degree $n \ge 1$, proved as `prop_7_64_pos`.

**`not_prop764ZeroCase`** and **`not_prop764Original`**: the degree-zero case, and hence the first version of `Prop7_64`, fails; the named statement is corrected to `0 < n` and proved (`prop_7_64`, `Ch7Prop764Zero.lean`).

Proof outline. Let $\pi$ be a uniformizer of $A$. For a prime $\ell$ choose a compatible chain
$y_0 = \pi$, $y_{n+1}^\ell = y_n$ in $K^{\mathrm{al}}$, and let $E_\ell = \bigcup_n K(y_n)$ (`towerField`).
1. $X^{\ell^n} - \pi$ is Eisenstein, so irreducible over $K$ (`irreducible_X_pow_sub_C`), and $[K(y_n):K] = \ell^n$
   (`finrank_adjoin_pow`).
2. Hence $E_\ell$ has infinite degree: `finrank K E_ℓ = 0` (`finrank_towerField`).
3. In the integral closure $B$ of $A$ in $E_\ell$, with maximal ideal $\mathfrak P$ and $S = B_{\mathfrak P}$, the ideals
   $(y_n)S$ form a strictly increasing chain of ideals containing $\pi S$, so $S/\pi S$ is not Noetherian, has
   infinite length, and `ramIdxMilne` (a `toNat` of the length) is $0$ (`length_eq_top_of_chain`,
   `ramIdxMilne_eq_zero_of_chain`). So $E_\ell$ is "totally ramified" ($0 = 0$).
4. For distinct primes $\ell \ne \ell'$ the fields $E_\ell$, $E_{\ell'}$ differ (`towerField_ne`): $K(y_1) \subseteq
   K(y'_n)$ would give $\ell \mid \ell'^n$.
5. So the degree-zero set contains infinitely many fields.
-/

open IsLocalRing Polynomial IntermediateField

universe u v

namespace NumberFieldKB.MilneANT

section Deg

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]

/-- $X^m - \pi$ is irreducible over the fraction field (Eisenstein at the maximal ideal, then Gauss's lemma). -/
theorem irreducible_X_pow_sub_C (π : A) (hπ : Irreducible π) {m : ℕ} (hm : m ≠ 0) :
    Irreducible ((X ^ m - C (algebraMap A K π) : K[X])) := by
  have hmap : (X ^ m - C π : A[X]).map (algebraMap A K) = X ^ m - C (algebraMap A K π) := by
    simp
  rw [← hmap]
  have hmonic : (X ^ m - C π : A[X]).Monic := monic_X_pow_sub_C _ hm
  rw [← hmonic.irreducible_iff_irreducible_map_fraction_map (K := K)]
  have hprime : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ.prime
  have hdeg : (X ^ m - C π : A[X]).natDegree = m := natDegree_X_pow_sub_C
  refine Polynomial.IsEisensteinAt.irreducible (𝓟 := Ideal.span {π}) ?_ hprime hmonic.isPrimitive
    (by rw [hdeg]; omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [hmonic.leadingCoeff]
    exact fun h => hprime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  · intro n hn
    rw [hdeg] at hn
    rw [coeff_sub, coeff_X_pow, coeff_C]
    by_cases h0 : n = 0
    · subst h0; simp [hm.symm]
    · have hnm : n ≠ m := by omega
      simp [hnm, h0]
  · rw [coeff_sub, coeff_X_pow, coeff_C]
    simp [hm.symm]
    intro h
    rw [pow_two, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton] at h
    have hd : π * π ∣ π := by simpa using h
    obtain ⟨c, hc⟩ := hd
    have : π * (π * c) = π * 1 := by rw [← mul_assoc, ← hc, mul_one]
    have := mul_left_cancel₀ hπ.ne_zero this
    exact hπ.not_isUnit (isUnit_iff_exists_inv.2 ⟨c, by simpa [mul_comm] using this⟩)

end Deg

section Length

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [IsDomain S] [Algebra R S]

/-- If $q$ is a prime of a domain $S$ with $q \cap R = (\pi)$ and there is a chain $z_0 = \pi$, $z_{n+1}^\ell = z_n$
($\ell \ge 2$) of nonzero elements of $q$, then $S_q / \pi S_q$ has infinite length. -/
theorem length_eq_top_of_chain (q : Ideal S) [q.IsPrime] (π : R)
    (hp : q.under R = Ideal.span {π})
    (z : ℕ → S) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hz : ∀ n, z (n + 1) ^ ℓ = z n)
    (hq : ∀ n, z n ∈ q) (hne : ∀ n, z n ≠ 0) (h0 : z 0 = algebraMap R S π) :
    Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ (q.under R).map (algebraMap R (Localization.AtPrime q))) = ⊤ := by
  by_contra hne'
  have hN : IsNoetherian (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ (q.under R).map (algebraMap R (Localization.AtPrime q))) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 hne')).1
  set I : Ideal (Localization.AtPrime q) := (q.under R).map (algebraMap R (Localization.AtPrime q))
    with hI
  let w : ℕ → Localization.AtPrime q := fun n => algebraMap S (Localization.AtPrime q) (z n)
  have hw : ∀ n, w (n + 1) ^ ℓ = w n := fun n => by
    simp only [w, ← map_pow, hz]
  let J : ℕ → Ideal (Localization.AtPrime q) := fun n => Ideal.span {w n}
  have hJ : ∀ n, J n ≤ J (n + 1) := fun n => by
    simp only [J]
    rw [Ideal.span_singleton_le_span_singleton, ← hw n]
    exact dvd_pow_self _ (by omega)
  have hJm : Monotone J := monotone_nat_of_le_succ hJ
  have hIJ : ∀ n, I ≤ J n := fun n => by
    have h1 : I = Ideal.span {w 0} := by
      rw [hI, hp, Ideal.map_span, Set.image_singleton]
      simp only [w, h0]
      rw [← IsScalarTower.algebraMap_apply]
    rw [h1]
    exact hJm (Nat.zero_le n)
  have hinj : Function.Injective (algebraMap S (Localization.AtPrime q)) :=
    IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors
  have hstrict : ∀ n, w (n + 1) ∉ J n := fun n hmem => by
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hmem
    obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 2 := ⟨ℓ - 2, by omega⟩
    have hu0 : w (n + 1) ≠ 0 := fun h => hne (n + 1) (hinj (by simpa [w] using h))
    have h1 : w (n + 1) * 1 = w (n + 1) * (s * w (n + 1) ^ (k + 1)) := by
      rw [mul_one]
      nth_rewrite 1 [← hs, ← hw n]
      ring
    have h2 := mul_left_cancel₀ hu0 h1
    have hunit : IsUnit (w (n + 1)) :=
      isUnit_iff_exists_inv.2 ⟨s * w (n + 1) ^ k, by linear_combination h2.symm⟩
    have hmax : w (n + 1) ∈ maximalIdeal (Localization.AtPrime q) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q _).2 (hq _)
    exact hmax hunit
  let f : ℕ →o Submodule (Localization.AtPrime q) (Localization.AtPrime q ⧸ I) :=
    ⟨fun n => Submodule.map I.mkQ
      (J n : Submodule (Localization.AtPrime q) (Localization.AtPrime q)),
      fun a b hab => Submodule.map_mono (hJm hab)⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.2 hN f
  have h3 : f n = f (n + 1) := hn (n + 1) (by omega)
  have h4 : I ⊔ J n = I ⊔ J (n + 1) := by
    have := congrArg (Submodule.comap I.mkQ) h3
    change Submodule.comap I.mkQ (Submodule.map I.mkQ (J n : Submodule _ _)) =
      Submodule.comap I.mkQ (Submodule.map I.mkQ (J (n + 1) : Submodule _ _)) at this
    rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ] at this
    exact this
  rw [sup_eq_right.2 (hIJ n), sup_eq_right.2 (hIJ (n + 1))] at h4
  exact hstrict n (h4 ▸ Ideal.subset_span rfl)

end Length

section Ram

variable (A : Type u) [CommRing A]

omit [CommRing A] in
/-- A chain $y_{n+1}^\ell = y_n$ with $y_0 = \pi$ satisfies $y_n^{\ell^n} = \pi$. -/
theorem pow_chain_eq {L : Type*} [Field L] [CommRing A] [Algebra A L] (π : A) (y : ℕ → L) {ℓ : ℕ}
    (hy : ∀ n, y (n + 1) ^ ℓ = y n) (h0 : y 0 = algebraMap A L π) (n : ℕ) :
    y n ^ (ℓ ^ n) = algebraMap A L π := by
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [pow_succ', pow_mul, hy, ih]

variable [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]

/-- A field $L$ over a complete DVR $A$ containing a chain $y_{n+1}^\ell = y_n$, $y_0 = \pi$, has `ramIdxMilne = 0`. -/
theorem ramIdxMilne_eq_zero_of_chain {L : Type*} [Field L] [Algebra A L] (π : A)
    (hπ : Irreducible π) (hπ0 : algebraMap A L π ≠ 0) (y : ℕ → L) {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (hy : ∀ n, y (n + 1) ^ ℓ = y n) (h0 : y 0 = algebraMap A L π) :
    ramIdxMilne A L = 0 := by
  have hpow := pow_chain_eq A π y hy h0
  have hint : ∀ n, IsIntegral A (y n) := fun n =>
    IsIntegral.of_pow (pow_pos (show 0 < ℓ by omega) n) (by rw [hpow]; exact isIntegral_algebraMap)
  have hy0 : ∀ n, y n ≠ 0 := fun n h => by
    have := hpow n
    have hn : ℓ ^ n ≠ 0 := pow_ne_zero n (by omega)
    rw [h, zero_pow hn] at this
    exact hπ0 this.symm
  let z : ℕ → integralClosure A L := fun n => ⟨y n, hint n⟩
  have hzpow : ∀ n, z n ^ (ℓ ^ n) = algebraMap A (integralClosure A L) π := fun n =>
    Subtype.ext (hpow n)
  have hq : ∀ n, z n ∈ maximalIdeal (integralClosure A L) := fun n => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : IsUnit (algebraMap A (integralClosure A L) π) := by
      rw [← hzpow n]; exact hu.pow _
    exact hπ.not_isUnit ((isUnit_map_iff (algebraMap A (integralClosure A L)) π).1 h1)
  have hp : (maximalIdeal (integralClosure A L)).under A = Ideal.span {π} := by
    rw [← hπ.maximalIdeal_eq]
    ext a
    show algebraMap A (integralClosure A L) a ∈ maximalIdeal _ ↔ _
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, isUnit_map_iff]
  unfold ramIdxMilne
  rw [Ideal.ramificationIdx_def]
  rw [length_eq_top_of_chain (maximalIdeal (integralClosure A L)) π hp z hℓ
    (fun n => Subtype.ext (hy n)) hq (fun n h => hy0 n (congrArg Subtype.val h))
    (Subtype.ext h0)]
  rfl

end Ram

section Fields

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]

omit [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A] [IsFractionRing A K]
  [Algebra A K] [CommRing A] in
/-- Compatible chains of $\ell$-power roots in an algebraic closure. -/
theorem exists_pow_chain (x : AlgebraicClosure K) (ℓ : ℕ) :
    ∃ y : ℕ → AlgebraicClosure K, y 0 = x ∧ (0 < ℓ → ∀ n, y (n + 1) ^ ℓ = y n) := by
  by_cases hℓ : 0 < ℓ
  · choose f hf using fun z : AlgebraicClosure K => IsAlgClosed.exists_pow_nat_eq z hℓ
    exact ⟨fun n => Nat.rec x (fun _ z => f z) n, rfl, fun _ n => hf _⟩
  · exact ⟨fun _ => x, rfl, fun h => absurd h hℓ⟩

variable {A K}

omit [IsAdicComplete (maximalIdeal A) A] in
/-- $[K(y) : K] = m$ when $y^m = \pi$ for a uniformizer $\pi$ of $A$. -/
theorem finrank_adjoin_pow (π : A) (hπ : Irreducible π) {y : AlgebraicClosure K} {m : ℕ}
    (hm : m ≠ 0) (hy : y ^ m = algebraMap A (AlgebraicClosure K) π) :
    Module.finrank K K⟮y⟯ = m := by
  have hy' : y ^ m = algebraMap K (AlgebraicClosure K) (algebraMap A K π) := by
    rw [hy, ← IsScalarTower.algebraMap_apply]
  have hirr := irreducible_X_pow_sub_C (K := K) π hπ hm
  have hroot : aeval y (X ^ m - C (algebraMap A K π) : K[X]) = 0 := by
    simp [hy']
  have hmin : minpoly K y = X ^ m - C (algebraMap A K π) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot (monic_X_pow_sub_C _ hm)).symm
  have hint : IsIntegral K y := ⟨_, monic_X_pow_sub_C _ hm, hroot⟩
  rw [IntermediateField.adjoin.finrank hint, hmin, natDegree_X_pow_sub_C]

/-- The union $\bigcup_n K(y_n)$ of the tower generated by a chain. -/
noncomputable def towerField (y : ℕ → AlgebraicClosure K) : IntermediateField K (AlgebraicClosure K) :=
  ⨆ n, K⟮y n⟯

theorem adjoin_mono_of_chain {y : ℕ → AlgebraicClosure K} {ℓ : ℕ}
    (hy : ∀ n, y (n + 1) ^ ℓ = y n) : Monotone fun n => K⟮y n⟯ := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [IntermediateField.adjoin_simple_le_iff, ← hy n]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self K _) _

theorem mem_towerField (y : ℕ → AlgebraicClosure K) (n : ℕ) : y n ∈ towerField y :=
  (le_iSup (fun n => K⟮y n⟯) n) (IntermediateField.mem_adjoin_simple_self K _)

theorem mem_towerField_iff {y : ℕ → AlgebraicClosure K} {ℓ : ℕ}
    (hy : ∀ n, y (n + 1) ^ ℓ = y n) {x : AlgebraicClosure K} :
    x ∈ towerField y ↔ ∃ n, x ∈ K⟮y n⟯ := by
  have hdir : Directed (· ≤ ·) fun n => K⟮y n⟯ := (adjoin_mono_of_chain hy).directed_le
  have := IntermediateField.coe_iSup_of_directed hdir
  rw [towerField, ← SetLike.mem_coe, this]
  simp

omit [IsAdicComplete (maximalIdeal A) A] in
/-- The tower has infinite degree over $K$, i.e. `Module.finrank = 0`. -/
theorem finrank_towerField {π : A} (hπ : Irreducible π) {y : ℕ → AlgebraicClosure K} {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) (hy : ∀ n, y (n + 1) ^ ℓ = y n) (h0 : y 0 = algebraMap A _ π) :
    Module.finrank K (towerField y) = 0 := by
  apply Module.finrank_of_not_finite
  intro hfin
  have hle : ∀ n, K⟮y n⟯ ≤ towerField y := fun n => le_iSup (fun n => K⟮y n⟯) n
  have hfr : ∀ n, ℓ ^ n ≤ Module.finrank K (towerField y) := fun n => by
    rw [← finrank_adjoin_pow π hπ (pow_ne_zero n (by omega)) (pow_chain_eq A π y hy h0 n)]
    exact IntermediateField.finrank_le_of_le_right (hle n)
  have := hfr (Module.finrank K (towerField y))
  have h2 := Nat.lt_pow_self (show 1 < ℓ by omega) (n := Module.finrank K (towerField y))
  omega

omit [IsAdicComplete (maximalIdeal A) A] in
/-- Towers for distinct primes are distinct. -/
theorem towerField_ne {π : A} (hπ : Irreducible π) {y y' : ℕ → AlgebraicClosure K} {ℓ ℓ' : ℕ}
    (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hy : ∀ n, y (n + 1) ^ ℓ = y n)
    (h0 : y 0 = algebraMap A _ π) (hy' : ∀ n, y' (n + 1) ^ ℓ' = y' n)
    (h0' : y' 0 = algebraMap A _ π) (hne : ℓ ≠ ℓ') : towerField y ≠ towerField y' := by
  intro h
  have h1 : y 1 ∈ towerField y' := h ▸ mem_towerField y 1
  obtain ⟨n, hn⟩ := (mem_towerField_iff hy').1 h1
  have hle : K⟮y 1⟯ ≤ K⟮y' n⟯ := (IntermediateField.adjoin_simple_le_iff).2 hn
  have hd := IntermediateField.finrank_dvd_of_le_right hle
  rw [finrank_adjoin_pow π hπ (pow_ne_zero 1 hℓ.ne_zero) (pow_chain_eq A π y hy h0 1),
    finrank_adjoin_pow π hπ (pow_ne_zero n hℓ'.ne_zero) (pow_chain_eq A π y' hy' h0' n)] at hd
  rw [pow_one] at hd
  exact hne ((Nat.prime_dvd_prime_iff_eq hℓ hℓ').1 (hℓ.dvd_of_dvd_pow hd))

end Fields

section Main

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
  {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]

/-- **Erratum.** The degree-zero case of Milne's Proposition 7.64 is false: for each prime $\ell$ the field
$\bigcup_n K(\pi^{1/\ell^n})$ has infinite degree (`finrank = 0`) and `ramIdxMilne = 0`, so there are infinitely many
such fields. -/
theorem not_prop764ZeroCase [CharZero K] [Finite (ResidueField A)] : ¬ Prop764ZeroCase A K := by
  intro hfin
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  choose Y hY0 hY using fun ℓ : ℕ => exists_pow_chain K (algebraMap A (AlgebraicClosure K) π) ℓ
  have hmaps : Set.MapsTo (fun ℓ => towerField (Y ℓ))
      {ℓ : ℕ | ℓ.Prime}
      {E : IntermediateField K (AlgebraicClosure K) |
        Module.finrank K E = 0 ∧ IsTotallyRamifiedMilne A K E} := by
    intro ℓ hℓ
    have hℓ : ℓ.Prime := hℓ
    have hfr := finrank_towerField hπ hℓ.two_le (hY ℓ hℓ.pos) (hY0 ℓ)
    refine ⟨hfr, ?_⟩
    unfold IsTotallyRamifiedMilne
    rw [hfr]
    have hinj : Function.Injective (algebraMap A (towerField (Y ℓ))) := by
      have : algebraMap A (towerField (Y ℓ)) =
          (algebraMap K (towerField (Y ℓ))).comp (algebraMap A K) :=
        IsScalarTower.algebraMap_eq A K _
      rw [this]
      exact (algebraMap K _).injective.comp (IsFractionRing.injective A K)
    exact ramIdxMilne_eq_zero_of_chain A (L := towerField (Y ℓ)) π hπ
      (fun h => hπ.ne_zero (hinj (h.trans (map_zero _).symm)))
      (fun n => ⟨Y ℓ n, mem_towerField _ n⟩) hℓ.two_le
      (fun n => Subtype.ext (hY ℓ hℓ.pos n)) (Subtype.ext (hY0 ℓ))
  have hinjOn : Set.InjOn (fun ℓ => towerField (Y ℓ)) {ℓ : ℕ | ℓ.Prime} := by
    intro ℓ hℓ ℓ' hℓ' h
    by_contra hne
    exact towerField_ne hπ hℓ hℓ' (hY ℓ (hℓ : ℓ.Prime).pos) (hY0 ℓ) (hY ℓ' (hℓ' : ℓ'.Prime).pos)
      (hY0 ℓ') hne h
  exact (Set.infinite_of_injOn_mapsTo hinjOn hmaps Nat.infinite_setOfPred_prime) hfin

/-- **Erratum** for Milne, *Algebraic Number Theory* v3.08, Prop. 7.64, p. 133: the named statement `Prop7_64`
quantifies over $n = 0$ (`finrank` $0$ = subfields of infinite degree) and is false there; Milne means extensions of
degree $n \ge 1$, proved as `prop_7_64_pos`. -/
@[kb "milne2020ant" "v3.08, Prop. 7.64, p. 133"]
theorem not_prop764Original [CharZero K] [Finite (ResidueField A)] : ¬ Prop764Original A K :=
  fun h => not_prop764ZeroCase ((prop764Original_iff_zero A K).1 h)

end Main

end NumberFieldKB.MilneANT
