import NumberFieldKB.MilneCFT.Ch8.ReciprocityLaw
import NumberFieldKB.MilneCFT.Ch8.CyclotomicNormCongr

/-!
# Prop. VIII.5.12 (b): the normalization $(\zeta, 1 - \lambda^{p-1})_\lambda = \zeta$, via the product formula

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §5,
Proposition 5.12 (b), p. 248: $(\eta_p, \lambda) = \zeta$. By (a) and (c), $(\eta_p, \lambda) = (\zeta, \eta_{p-1})$
(`IsSteinbergPairing.eta_p_lam_eq`); here the value $(\zeta, \eta_{p-1})_\lambda = \zeta$ is computed for Milne's
Hilbert symbol of $K = \mathbb Q(\zeta_p)$ at the prime $\lambda = (1 - \zeta)$, defined from an idèlic Artin map of
$L = K(\zeta^{1/p})$ trivial on $K^\times$ (`hilbertArtin`, Remark 5.9; the existence of such a map is the global
reciprocity law, a named input of Chapter V).

*Proof.* Product formula (5.10, `item_5_10`): $\prod_v (\zeta, b)_v = 1$, $b = \eta_{p-1} = 1 - \lambda^{p-1}$. The
infinite places are complex ($p$ odd), where the symbol is $1$. For $v \nmid p$, 5.8 (`item_5_8`) gives
$(\zeta, b)_v = (\zeta/\mathfrak p_v)^{\mathrm{ord}_v b} = \zeta^{\mathrm{ord}_v(b)(N v - 1)/p}$. Since every
$Nv \equiv 1 \pmod p$, $\sum_v \mathrm{ord}_v(b)(Nv - 1)/p \equiv (N(b) - 1)/p \pmod p$, and
$N(b) \equiv 1 - p \pmod{p^2}$ (`norm_one_sub_lam_pow_modEq`), so the sum is $\equiv -1$ and
$(\zeta, b)_\lambda = \zeta$.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace NumberFieldKB.MilneCFT.Ch8


theorem absNorm_eq_prod_count {K : Type} [Field K] [NumberField K] (J : Ideal (𝓞 K)) (hJ : J ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∉ T, (Associates.mk v.asIdeal).count (Associates.mk J).factors = 0) :
    Ideal.absNorm J = ∏ v ∈ T, Ideal.absNorm v.asIdeal ^
      (Associates.mk v.asIdeal).count (Associates.mk J).factors := by
  classical
  conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hJ]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_]
  · rw [map_prod]
    simp [HeightOneSpectrum.maxPowDividing, map_pow]
  · intro v hv
    by_contra hvT
    apply hv
    simp [HeightOneSpectrum.maxPowDividing, hT v hvT]

theorem modP_mul {p A B a b : ℤ} (hA : A ≡ 1 + p * a [ZMOD p ^ 2]) (hB : B ≡ 1 + p * b [ZMOD p ^ 2]) :
    A * B ≡ 1 + p * (a + b) [ZMOD p ^ 2] := by
  refine (hA.mul hB).trans ?_
  exact Int.modEq_iff_dvd.2 ⟨-(a * b), by ring⟩

theorem modP_pow {p A a : ℤ} (hA : A ≡ 1 + p * a [ZMOD p ^ 2]) (c : ℕ) :
    A ^ c ≡ 1 + p * (c * a) [ZMOD p ^ 2] := by
  induction c with
  | zero => simp [Int.ModEq.refl]
  | succ c ih =>
    have := modP_mul ih hA
    rw [pow_succ A c]
    have e : (1 + p * (((c + 1 : ℕ) : ℤ) * a)) = 1 + p * (c * a + a) := by push_cast; ring
    rw [e]
    exact this

theorem modP_prod {ι : Type*} (s : Finset ι) (p : ℤ) (A a : ι → ℤ)
    (h : ∀ i ∈ s, A i ≡ 1 + p * a i [ZMOD p ^ 2]) :
    ∏ i ∈ s, A i ≡ 1 + p * ∑ i ∈ s, a i [ZMOD p ^ 2] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Int.ModEq.refl]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact modP_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem sum_dvd_succ {ι : Type*} (s : Finset ι) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x c m : ι → ℕ)
    (hx : ∀ i ∈ s, x i = 1 + p * m i) (N : ℤ) (hN : N ≡ 1 - p [ZMOD (p : ℤ) ^ 2])
    (hM : N.natAbs = ∏ i ∈ s, x i ^ c i) :
    (p : ℤ) ∣ ((∑ i ∈ s, c i * m i : ℕ) : ℤ) + 1 := by
  have h1 : ∀ i ∈ s, ((x i ^ c i : ℕ) : ℤ) ≡ 1 + p * ((c i * m i : ℕ) : ℤ) [ZMOD (p : ℤ) ^ 2] := by
    intro i hi
    have := modP_pow (p := p) (A := (x i : ℤ)) (a := m i)
      (by rw [hx i hi]; push_cast; exact Int.ModEq.refl _) (c i)
    push_cast at this ⊢
    exact this
  have h2 := modP_prod s p (fun i => ((x i ^ c i : ℕ) : ℤ)) (fun i => ((c i * m i : ℕ) : ℤ)) h1
  rw [← Nat.cast_prod, ← hM, ← Nat.cast_sum] at h2
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Nat.cast_sum] at *
  set S : ℤ := ∑ i ∈ s, ((c i * m i : ℕ) : ℤ) with hS
  rcases Int.natAbs_eq N with h | h
  · have h3 := (h2.symm.trans (h ▸ hN : ((N.natAbs : ℕ) : ℤ) ≡ 1 - p [ZMOD (p : ℤ) ^ 2]))
    obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.1 h3
    have : (p : ℤ) * (-(S + 1)) = p * (p * k) := by linear_combination hk
    have := mul_left_cancel₀ hp0 this
    exact ⟨-k, by linarith⟩
  · exfalso
    obtain ⟨k1, hk1⟩ := Int.modEq_iff_dvd.1 hN
    obtain ⟨k2, hk2⟩ := Int.modEq_iff_dvd.1 h2
    have h4 : (2 : ℤ) = p * (p * (k1 + k2) + 1 - S) := by linear_combination hk1 + hk2 + h
    have h5 : (p : ℤ) ∣ 2 := ⟨_, h4⟩
    have h6 : p ∣ 2 := by exact_mod_cast h5
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h6)

theorem hilbertArtinInf_totallyComplex {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (α : L) (hα0 : α ≠ 0)
    (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (hφ : IsIdelicArtinMap L φ) (w : InfinitePlace K) (b : Kˣ) :
    hilbertArtinInf L φ α w b = 1 := by
  refine hilbertArtinInf_eq L φ α hα0 w b 1 ?_
  have : φ (IdeleGroup.ofCompletion (𝓞 K) K w (Units.map (algebraMap K _).toMonoidHom b)) = 1 := by
    obtain ⟨N, hN⟩ := hφ.local_ramified
    apply hN
    · intro v _
      rw [ideleFinAt_ofCompletion]; simp
    · intro v _
      rw [ideleFinAt_ofCompletion]; simp
    · intro w' hw' _
      exact absurd hw' (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w'))
  rw [this]; simp

/-- **Milne, *CFT*, VIII, Prop. 5.12 (b), normalization** (p. 248), in the form $(\zeta, 1 - \lambda^{p-1})_\lambda =
\zeta$, for the Hilbert symbol of $\mathbb Q(\zeta_p)$ ($p$ odd) at $\lambda = (1 - \zeta)$ defined by an idèlic Artin
map of $K(\zeta^{1/p})/K$ trivial on $K^\times$. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Prop. 5.12 (b), p. 248 (normalization, global symbol)"]
theorem hilbertArtin_zeta_eta {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (α : L)
    (hα : α ^ p = algebraMap K L ζ) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (φ : IdeleGroup (𝓞 K) K →* Gal(L/K)) (hφ : IsIdelicArtinMap L φ)
    (hφK : ∀ c : Kˣ, φ (IdeleGroup.unitEmbedding (𝓞 K) K c) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (hζ.toInteger - 1 : 𝓞 K) ∈ v.asIdeal)
    (b : Kˣ) (hb : (b : K) = 1 - (1 - ζ) ^ (p - 1)) :
    hilbertArtin L φ α v b = ζ := by
  classical
  have hp1 : p.Prime := hp.out
  have hp3 : 2 < p := lt_of_le_of_ne hp1.two_le (Ne.symm hp2)
  have : NeZero p := ⟨hp1.ne_zero⟩
  have : IsTotallyComplex K := IsCyclotomicExtension.Rat.isTotallyComplex (n := p) K hp3
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hp1.ne_zero] at hα
    exact hζ.ne_zero hp1.ne_zero ((algebraMap K L).injective (by simpa using hα.symm))
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp1.ne_zero
  set z : 𝓞 K := hζ.toInteger with hz
  have hzK : (z : K) = ζ := hζ.coe_toInteger
  set b₀ : 𝓞 K := 1 - (1 - z) ^ (p - 1) with hb₀
  have hbK : ((b₀ : 𝓞 K) : K) = (b : K) := by rw [hb, hb₀]; push_cast; simp [hzK]
  have hb_ne : b₀ ≠ 0 := fun h => b.ne_zero (by rw [← hbK, h]; rfl)
  set J : Ideal (𝓞 K) := Ideal.span {b₀} with hJdef
  have hJ : J ≠ 0 := by simp [J, hb_ne]
  set c : HeightOneSpectrum (𝓞 K) → ℕ := fun w => (Associates.mk w.asIdeal).count (Associates.mk J).factors
    with hc
  have hcount : ∀ w, FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K)) = (c w : ℤ) := by
    intro w
    have e : FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K) = (J : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← hbK]; exact (FractionalIdeal.coeIdeal_span_singleton b₀).symm
    rw [e, FractionalIdeal.count_coe K w hJ]
  have hc0 : ∀ w, w.valuation K (b : K) = 1 → c w = 0 := by
    intro w hw
    have := count_eq_zero_of_val w (b : K) b.ne_zero hw
    rw [hcount] at this
    exact_mod_cast this
  have hbv : v.valuation K (b : K) = 1 := by
    have hmem : (1 - z) ^ (p - 1) ∈ v.asIdeal := by
      apply Ideal.pow_mem_of_mem v.asIdeal ?_ (p - 1) (by omega)
      have : (1 - z) = -(z - 1) := by ring
      rw [this]; exact v.asIdeal.neg_mem hv
    have hnm : b₀ ∉ v.asIdeal := fun h => v.isPrime.ne_top (by
      rw [Ideal.eq_top_iff_one]
      have : (1 : 𝓞 K) = b₀ + (1 - z) ^ (p - 1) := by rw [hb₀]; ring
      rw [this]; exact v.asIdeal.add_mem h hmem)
    rw [← hbK]
    exact le_antisymm (v.valuation_le_one b₀)
      (not_lt.1 fun h => hnm ((v.valuation_lt_one_iff_mem (K := K) b₀).1 h))
  have hspan : ∀ w : HeightOneSpectrum (𝓞 K), (z - 1) ∈ w.asIdeal → w.asIdeal = Ideal.span {z - 1} := by
    intro w hw
    have hpr : Prime (z - 1) := hζ.zeta_sub_one_prime'
    have hmax : (Ideal.span {z - 1}).IsMaximal := by
      have : (Ideal.span {z - 1}).IsPrime := (Ideal.span_singleton_prime hpr.ne_zero).2 hpr
      exact Ideal.IsPrime.isMaximal this (by simpa using hpr.ne_zero)
    exact (hmax.eq_of_le w.isPrime.ne_top (by rwa [Ideal.span_singleton_le_iff_mem])).symm
  have hu : ∀ w : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ w.asIdeal → w = v := by
    intro w hw
    have hw1 : z - 1 ∈ w.asIdeal := by
      obtain ⟨u, hu⟩ := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hζ
      have : (z - 1) ^ (p - 1) ∈ w.asIdeal := by
        have : (z - 1) ^ (p - 1) = p * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
          have hu' : (z - 1) ^ (p - 1) * u = p := hu
          rw [← hu', mul_assoc]; simp
        rw [this]; exact w.asIdeal.mul_mem_right _ hw
      exact w.isPrime.mem_of_pow_mem _ this
    exact HeightOneSpectrum.ext ((hspan w hw1).trans (hspan v hv).symm)
  have hnotS : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v → w ∉ Sset p {ζ} := by
    intro w hw
    rw [notMem_Sset_iff]
    refine ⟨fun h => hw (hu w h), ?_⟩
    have hle : w.valuation K ζ ≤ 1 := by rw [← hzK]; exact w.valuation_le_one z
    refine le_antisymm hle (not_lt.1 fun h => ?_)
    have hm : z ∈ w.asIdeal := (w.valuation_lt_one_iff_mem (K := K) z).1 (by rw [← hzK] at h; exact h)
    have : z ^ p ∈ w.asIdeal := Ideal.pow_mem_of_mem _ hm p hp1.pos
    rw [hζ.toInteger_isPrimitiveRoot.pow_eq_one] at this
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  set T : Finset (HeightOneSpectrum (𝓞 K)) := (finite_val_ne_one (b : K) b.ne_zero).toFinset with hT
  have hmemT : ∀ w, w ∈ T ↔ w.valuation K (b : K) ≠ 1 := by intro w; simp [T]
  have hvT : v ∉ T := by rw [hmemT]; simpa using hbv
  have hcT : ∀ w ∉ T, c w = 0 := fun w hw => hc0 w (by simpa [hmemT] using hw)
  have hP := item_5_10 L p hp1.pos ζ hζ ζ hζ0 α hα hgen φ hφ hφK b
  rw [Finset.prod_eq_one (fun w _ => hilbertArtinInf_totallyComplex L α hα0 φ hφ w b), mul_one] at hP
  have hone : ∀ w ∉ insert v T, hilbertArtin L φ α w b = 1 := by
    intro w hw
    rw [Finset.mem_insert, not_or] at hw
    rw [item_5_8 L p hp1.pos ζ hζ ζ hζ0 α hα hgen φ hφ w (hnotS w hw.1) b, hcount, hcT w hw.2]
    simp
  have hfp : ∏ᶠ w : HeightOneSpectrum (𝓞 K), hilbertArtin L φ α w b =
      hilbertArtin L φ α v b * ∏ w ∈ T, hilbertArtin L φ α w b := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := insert v T) ?_, Finset.prod_insert hvT]
    intro w hw
    by_contra h
    exact hw (hone w h)
  have hres : ∀ w ∈ T, hilbertArtin L φ α w b = ζ ^ (c w * ((Ideal.absNorm w.asIdeal - 1) / p)) := by
    intro w hw
    have hwv : w ≠ v := fun h => hvT (h ▸ hw)
    rw [item_5_8 L p hp1.pos ζ hζ ζ hζ0 α hα hgen φ hφ w (hnotS w hwv) b, hcount, zpow_natCast]
    have : powerResidue p ζ w = ζ ^ ((Ideal.absNorm w.asIdeal - 1) / p) :=
      (powerResidue_unique p hp1.pos ζ hζ ζ w (hnotS w hwv) _
        ⟨by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow], by simp⟩).symm
    rw [this, ← pow_mul, mul_comm]
  have hx : ∀ w ∈ T, Ideal.absNorm w.asIdeal = 1 + p * ((Ideal.absNorm w.asIdeal - 1) / p) := by
    intro w hw
    have hwv : w ≠ v := fun h => hvT (h ▸ hw)
    obtain ⟨hnv, -⟩ := (notMem_Sset_iff w p ζ).1 (hnotS w hwv)
    have hd := dvd_absNorm_sub_one w hp1.pos hζ hnv
    have hpos : 0 < Ideal.absNorm w.asIdeal :=
      Nat.pos_of_ne_zero (fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
    have := Nat.mul_div_cancel' hd
    rw [this]; omega
  obtain ⟨N, hN1, hN2⟩ := norm_one_sub_lam_pow_modEq hp2 hζ
  have hNb : Algebra.norm ℤ b₀ = N := by
    have : ((Algebra.norm ℤ b₀ : ℤ) : ℚ) = N := by
      rw [Algebra.coe_norm_int, hbK, hb, ← hN1]
    exact_mod_cast this
  have hM : N.natAbs = ∏ w ∈ T, Ideal.absNorm w.asIdeal ^ c w := by
    rw [← hNb, ← Ideal.absNorm_span_singleton]
    exact absNorm_eq_prod_count J hJ T hcT
  have hdvd := sum_dvd_succ T p hp1 hp2 (fun w => Ideal.absNorm w.asIdeal) c
    (fun w => (Ideal.absNorm w.asIdeal - 1) / p) hx N hN2 hM
  have hdvd' : p ∣ (∑ w ∈ T, c w * ((Ideal.absNorm w.asIdeal - 1) / p)) + 1 := by exact_mod_cast hdvd
  rw [hfp, Finset.prod_congr rfl hres, Finset.prod_pow_eq_pow_sum] at hP
  have h1 : ζ ^ ((∑ w ∈ T, c w * ((Ideal.absNorm w.asIdeal - 1) / p)) + 1) = 1 :=
    (hζ.pow_eq_one_iff_dvd _).2 hdvd'
  calc hilbertArtin L φ α v b = hilbertArtin L φ α v b * ζ ^ ((∑ w ∈ T, c w * ((Ideal.absNorm w.asIdeal - 1) / p)) + 1) := by
        rw [h1, mul_one]
    _ = ζ := by rw [pow_succ, ← mul_assoc, hP, one_mul]

end NumberFieldKB.MilneCFT.Ch8