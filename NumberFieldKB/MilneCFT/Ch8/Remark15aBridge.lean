import NumberFieldKB.MilneCFT.Ch8.Remark15aLocal
import NumberFieldKB.MilneCFT.Ch8.Remark15aCheb
import NumberFieldKB.MilneCFT.Ch8.Eighth

/-!
# Glue for Remark VIII.1.5 (a): local powers, splitting fields, coprime exponents

* `forall_fixed_of_mem_powSet`: for `a ∈ P(q, S)` and a finite Galois `M/K` containing a primitive `q`-th root of
  unity `ζ` and a `q`-th root `α` of `a`, every `σ ∈ Gal(M/K)` fixes some `ζ^i α` (Chebotarev,
  `exists_isArithFrobAt_notMem`, at a place outside `S`, prime to `q`, where `a` is a unit; then
  `exists_pow_mul_fixed_of_isLocalPow`).
* `exists_splitting`: such an `M` exists for two elements `a, a'` at once.
* `mul_mem_powSet`, `pow_mem_powSet`, `mem_powSet_of_dvd`, `mem_powSet_of_pow_mem` (the last for exponents coprime to
  `q`): closure properties of `P(n, S)`.
* `exists_pow_mul_of_coprime`: in a commutative group, `x^s = y^t` with `s, t` coprime is an `st`-th power.
* `sixteen_mem_powSet`: `16 ∈ P(8, S)` when `S` contains the prime `2` (Milne's example; `exercise_1_3`).
-/

open IsDedekindDomain NumberField

namespace NumberFieldKB.MilneCFT.Ch8.R15a

variable {K : Type} [Field K] [NumberField K]

/-- Every Galois element fixes some root `ζ^i α` of a local `q`-th power. -/
theorem forall_fixed_of_mem_powSet {M : Type} [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    {q : ℕ} (hq : 0 < q) {ζ : M} (hζ : IsPrimitiveRoot ζ q) {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) {a : Kˣ} (ha : a ∈ powSet q S) {α : M} (hα : α ^ q = algebraMap K M (a : K)) :
    ∀ σ : M ≃ₐ[K] M, ∃ i : ℕ, σ (ζ ^ i * α) = ζ ^ i * α := by
  classical
  have hq0 : q ≠ 0 := hq.ne'
  have hfin1 : {v : HeightOneSpectrum (𝓞 K) | (q : 𝓞 K) ∈ v.asIdeal}.Finite := by
    have hn0 : ((q : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hq0
    refine (Ideal.finite_factors (Ideal.span_singleton_eq_bot.not.mpr hn0)).subset fun v hv => ?_
    exact (Ideal.dvd_span_singleton).2 hv
  have hfin2 : {v : HeightOneSpectrum (𝓞 K) | v.valuation K (a : K) ≠ 1}.Finite := by
    refine ((HeightOneSpectrum.Support.finite (𝓞 K) (a : K)).union
      (HeightOneSpectrum.Support.finite (𝓞 K) ((a : K)⁻¹))).subset fun v hv => ?_
    simp only [Set.mem_setOf_eq] at hv
    rcases lt_or_gt_of_ne hv with h | h
    · right
      show 1 < v.valuation K (a : K)⁻¹
      rw [map_inv₀]
      exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr (by simp), h⟩
    · left; exact h
  intro σ
  obtain ⟨v, hvA, Q, hQ, hQv, hF⟩ := exists_isArithFrobAt_notMem (K := K) (M := M) σ
    (hS.toFinset ∪ hfin1.toFinset ∪ hfin2.toFinset)
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hvA
  obtain ⟨⟨hvS, hvq⟩, hva⟩ := hvA
  exact exists_pow_mul_fixed_of_isLocalPow hF hζ hvq (not_not.mp hva) hα (ha v hvS)

open Polynomial in
/-- A finite Galois extension containing `ζ_q` and `q`-th roots of `a` and `a'`. -/
theorem exists_splitting {q : ℕ} (hq : 0 < q) (a a' : K) :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra K M) (_ : FiniteDimensional K M)
      (_ : IsGalois K M) (ζ α α' : M), IsPrimitiveRoot ζ q ∧ α ^ q = algebraMap K M a ∧
        α' ^ q = algebraMap K M a' := by
  classical
  have hq0 : q ≠ 0 := hq.ne'
  let P : K[X] := Polynomial.cyclotomic q K * (X ^ q - C a) * (X ^ q - C a')
  have hP0 : P ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (Polynomial.cyclotomic_ne_zero q K) ?_) ?_ <;>
      exact Polynomial.X_pow_sub_C_ne_zero hq _
  let M := P.SplittingField
  have : FiniteDimensional K M := inferInstance
  have : NumberField M := NumberField.of_module_finite K M
  have : IsGalois K M := ⟨⟩
  have h1 : Polynomial.Splits (P.map (algebraMap K M)) := Polynomial.SplittingField.splits P
  have hP0' : P.map (algebraMap K M) ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff (algebraMap K M).injective]; exact hP0
  have hroot : ∀ (f : K[X]), f ∣ P → f.map (algebraMap K M) ≠ 0 →
      (f.map (algebraMap K M)).degree ≠ 0 → ∃ x : M, (f.map (algebraMap K M)).eval x = 0 := by
    intro f hf h0 hdeg
    exact (h1.of_dvd hP0' (Polynomial.map_dvd _ hf)).exists_eval_eq_zero hdeg
  have hdegX : ∀ b : K, ((X ^ q - C b : K[X]).map (algebraMap K M)).degree ≠ 0 := by
    intro b
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, degree_X_pow_sub_C hq]
    exact_mod_cast hq0
  have hne : ∀ b : K, (X ^ q - C b : K[X]).map (algebraMap K M) ≠ 0 := by
    intro b
    rw [Ne, Polynomial.map_eq_zero_iff (algebraMap K M).injective]
    exact Polynomial.X_pow_sub_C_ne_zero hq _
  obtain ⟨ζ, hζ⟩ := hroot (Polynomial.cyclotomic q K)
    ⟨(X ^ q - C a) * (X ^ q - C a'), by simp only [P]; ring⟩
    (by
      rw [Ne, Polynomial.map_eq_zero_iff (algebraMap K M).injective]
      exact Polynomial.cyclotomic_ne_zero q K)
    (by
      rw [Polynomial.map_cyclotomic, Polynomial.degree_cyclotomic]
      exact_mod_cast Nat.totient_pos.mpr hq |>.ne')
  obtain ⟨α, hα⟩ := hroot (X ^ q - C a) ⟨Polynomial.cyclotomic q K * (X ^ q - C a'), by simp only [P]; ring⟩
    (hne a) (hdegX a)
  obtain ⟨α', hα'⟩ := hroot (X ^ q - C a') ⟨Polynomial.cyclotomic q K * (X ^ q - C a), by simp only [P]; ring⟩
    (hne a') (hdegX a')
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ζ, α, α', ?_, ?_, ?_⟩
  · haveI : NeZero (q : M) := ⟨by exact_mod_cast hq0⟩
    rw [Polynomial.map_cyclotomic] at hζ
    exact (Polynomial.isRoot_cyclotomic_iff).mp hζ
  · simpa [sub_eq_zero] using hα
  · simpa [sub_eq_zero] using hα'

theorem one_mem_powSet (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) : (1 : Kˣ) ∈ powSet n S := by
  intro v _
  exact ⟨1, by simp⟩

theorem mul_mem_powSet {n : ℕ} {S : Set (HeightOneSpectrum (𝓞 K))} {a b : Kˣ} (ha : a ∈ powSet n S)
    (hb : b ∈ powSet n S) : a * b ∈ powSet n S := by
  intro v hv
  obtain ⟨x, hx⟩ := ha v hv
  obtain ⟨y, hy⟩ := hb v hv
  exact ⟨x * y, by simp [mul_pow, hx, hy]⟩

theorem pow_mem_powSet (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (b : Kˣ) : b ^ n ∈ powSet n S := by
  intro v _
  exact ⟨algebraMap K (v.adicCompletion K) (b : K), by simp [map_pow]⟩

theorem mem_powSet_of_dvd {d n : ℕ} (hd : d ∣ n) {S : Set (HeightOneSpectrum (𝓞 K))} {a : Kˣ}
    (ha : a ∈ powSet n S) : a ∈ powSet d S := by
  intro v hv
  obtain ⟨x, hx⟩ := ha v hv
  obtain ⟨e, rfl⟩ := hd
  exact ⟨x ^ e, by rw [← pow_mul, mul_comm, hx]⟩

/-- If `c^m ∈ P(q, S)` with `m` prime to `q`, then `c ∈ P(q, S)`. -/
theorem mem_powSet_of_pow_mem {m q : ℕ} (hmq : Nat.Coprime m q) {S : Set (HeightOneSpectrum (𝓞 K))}
    {c : Kˣ} (hc : c ^ m ∈ powSet q S) : c ∈ powSet q S := by
  intro v hv
  obtain ⟨x, hx⟩ := hc v hv
  have hx' : x ^ q = (algebraMap K (v.adicCompletion K) (c : K)) ^ m := by
    rw [hx]; simp
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp at hmq
    subst hmq
    exact ⟨1, by simpa using hx'⟩
  have hc0 : algebraMap K (v.adicCompletion K) (c : K) ≠ 0 := by
    simpa using c.ne_zero
  set cc := algebraMap K (v.adicCompletion K) (c : K) with hcc
  rcases Nat.eq_or_lt_of_le hq with h1 | h1
  · subst h1
    exact ⟨cc, by simp [hcc]⟩
  obtain ⟨u, -, hu'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hmq h1
  have hk : m * u = 1 + q * (m * u / q) := by
    have := Nat.mod_add_div (m * u) q
    rw [hu'] at this; omega
  set k := m * u / q
  refine ⟨x ^ u / cc ^ k, ?_⟩
  have e : cc * (cc ^ k) ^ q = (x ^ u) ^ q := by
    calc cc * (cc ^ k) ^ q = cc ^ (1 + q * k) := by rw [pow_add, ← pow_mul, pow_one, mul_comm k q]
      _ = cc ^ (m * u) := by rw [hk]
      _ = (x ^ u) ^ q := by rw [pow_mul, ← hx', ← pow_mul, ← pow_mul, mul_comm]
  have hk0 : cc ^ k ≠ 0 := pow_ne_zero _ hc0
  rw [div_pow, ← e]
  field_simp
  exact hcc

/-- In a commutative group, `x^s = y^t` with `s, t` coprime is an `st`-th power. -/
theorem exists_pow_mul_of_coprime {G : Type*} [CommGroup G] {s t : ℕ} (hst : Nat.Coprime s t) {x y : G}
    (hxy : x ^ s = y ^ t) : ∃ z : G, z ^ (s * t) = x ^ s := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, (1 : ℤ) = s * a + t * b := by
    have := Nat.gcd_eq_gcd_ab s t
    rw [hst] at this
    exact ⟨_, _, by simpa [mul_comm] using this⟩
  refine ⟨x ^ b * y ^ a, ?_⟩
  have h1 : (x ^ b * y ^ a) ^ (s * t) = (x ^ (s : ℤ)) ^ (b * t) * (y ^ (t : ℤ)) ^ (a * s) := by
    rw [← zpow_natCast, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
    congr 2 <;> push_cast <;> ring
  have hxy' : x ^ (s : ℤ) = y ^ (t : ℤ) := by simpa using hxy
  have hb1 : b * t + a * s = 1 := by linarith
  rw [h1, ← hxy', ← zpow_add, hb1, zpow_one, zpow_natCast]

/-- `16 ∈ P(8, S)` when `S` contains the prime above `2`. -/
theorem sixteen_mem_powSet (S : Set (HeightOneSpectrum (𝓞 ℚ))) (hS : ∃ v ∈ S, (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    sixteenUnit ∈ powSet 8 S := by
  intro v hv
  obtain ⟨v₂, hv₂S, hv₂⟩ := hS
  have hgen : ∀ w : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∈ w.asIdeal →
      Rat.HeightOneSpectrum.natGenerator w = 2 := by
    intro w hw
    have h := (Rat.HeightOneSpectrum.natGenerator_dvd_iff w (n := 2)).mpr (by
      rw [show ((2 : ℕ) : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) (2 : 𝓞 ℚ) by
        rw [map_ofNat]; norm_num, Ideal.apply_mem_of_equiv_iff]
      exact hw)
    exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) Nat.prime_two).mp h
  have hne : Rat.HeightOneSpectrum.natGenerator v ≠ 2 := by
    intro h2
    apply hv
    have hv2 : v = v₂ := by
      apply Rat.HeightOneSpectrum.primesEquiv.injective
      apply Subtype.ext
      show Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator v₂
      rw [h2, hgen v₂ hv₂]
    rw [hv2]; exact hv₂S
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  obtain ⟨y, hy⟩ := sixteen_eighth_power_padic (Rat.HeightOneSpectrum.primesEquiv v : ℕ) hne
  letI : Algebra ℚ (v.adicCompletion ℚ) := HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
  let φ := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have h1 : (algebraMap ℚ (v.adicCompletion ℚ)) ((sixteenUnit : ℚˣ) : ℚ) =
      (((16 : ℚ)) : v.adicCompletion ℚ) := by
    have h16 : ((sixteenUnit : ℚˣ) : ℚ) = 16 := by simp [sixteenUnit]
    rw [h16]
    exact eq_ratCast _ _
  refine ⟨φ.symm y, EquivLike.injective φ ?_⟩
  refine Eq.trans ?_ (congrArg φ h1).symm
  rw [map_pow, φ.apply_symm_apply, hy, map_ratCast]
  norm_num

end NumberFieldKB.MilneCFT.Ch8.R15a
