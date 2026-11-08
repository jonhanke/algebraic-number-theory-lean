import NumberFieldKB.MilneCFT.Ch8.ExplicitPairingSteinberg

open IntermediateField Polynomial

namespace NumberFieldKB.MilneCFT.Ch8

/-- Norm of `1 - α` when `X^p - a` is the minimal polynomial of `α` (`p` odd or not). -/
theorem norm_one_sub_gen {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {p : ℕ}
    {a : K} {α : Ω} (hmin : minpoly K α = X ^ p - C a) (hint : IsIntegral K α) :
    Algebra.norm K (1 - IntermediateField.AdjoinSimple.gen K α) = 1 - a := by
  set g := IntermediateField.AdjoinSimple.gen K α with hg
  have : FiniteDimensional K K⟮α⟯ := IntermediateField.adjoin.finiteDimensional hint
  have hgm : minpoly K g = X ^ p - C a := by
    rw [hg, IntermediateField.minpoly_gen, hmin]
  have hgint : IsIntegral K g := Algebra.IsIntegral.isIntegral g
  have hy : (1 : K⟮α⟯) - g = -g + algebraMap K K⟮α⟯ 1 := by simp [add_comm, sub_eq_add_neg]
  have hymin : minpoly K ((1 : K⟮α⟯) - g) =
      (-1) ^ p * ((X ^ p - C a).comp (-X)).comp (X - C 1) := by
    rw [hy, minpoly.add_algebraMap, minpoly.neg, hgm]
    simp
  have hyint : IsIntegral K ((1 : K⟮α⟯) - g) := Algebra.IsIntegral.isIntegral _
  have htop : Algebra.adjoin K {(1 : K⟮α⟯) - g} = ⊤ := by
    have h1 : Algebra.adjoin K {g} = ⊤ := (IntermediateField.adjoin.powerBasis hint).adjoin_gen_eq_top
    rw [eq_top_iff, ← h1, Algebra.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have h3 := Subalgebra.sub_mem (Algebra.adjoin K {(1 : K⟮α⟯) - g}) (Subalgebra.one_mem _)
      (Algebra.self_mem_adjoin_singleton K ((1 : K⟮α⟯) - g))
    simpa using h3
  have hnd : (PowerBasis.ofAdjoinEqTop hyint htop).dim = p := by
    have h1 := (PowerBasis.ofAdjoinEqTop hyint htop).natDegree_minpoly
    have h2 := (IntermediateField.adjoin.powerBasis hint).natDegree_minpoly
    have h3 := (PowerBasis.ofAdjoinEqTop hyint htop).finrank
    have h4 := (IntermediateField.adjoin.powerBasis hint).finrank
    simp only [PowerBasis.ofAdjoinEqTop_gen] at h1
    simp only [IntermediateField.adjoin.powerBasis_gen] at h2
    rw [← h3, h4, ← h2]
    show (minpoly K g).natDegree = p
    rw [hgm, natDegree_X_pow_sub_C]
  have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (PowerBasis.ofAdjoinEqTop hyint htop)
  simp only [PowerBasis.ofAdjoinEqTop_gen] at this
  rw [this, hnd, hymin, coeff_zero_eq_eval_zero]
  simp [← mul_assoc, ← mul_pow]

/-- **The Steinberg relation from the norm criterion** (Milne, *Class Field Theory*, III, Theorem 4.4 (d), p. 113:
$(a,b) = 1$ iff $b$ is a norm from $K[\sqrt[p]{a}]$; only the 'if' direction is used). If $a + b = 1$, then
$b = 1 - a = N_{K(\alpha)/K}(1 - \alpha)$ for $\alpha^p = a$ when $X^p - a$ is irreducible, and $a$ is a
$p$-th power otherwise (then $(a, b) = (c, b)^p = 1$). -/
theorem isSteinbergPairing_of_norm {K Ω M : Type*} [Field K] [Field Ω] [Algebra K Ω] [CommGroup M]
    {p : ℕ} (hp : p.Prime) (P : Kˣ →* Kˣ →* M) (hpow : ∀ x y, P x y ^ p = 1)
    (hroots : ∀ a : K, ∃ α : Ω, α ^ p = algebraMap K Ω a)
    (hnorm : ∀ (a b : Kˣ) (α : Ω), α ^ p = algebraMap K Ω (a : K) →
      (∃ x : K⟮α⟯, Algebra.norm K x = (b : K)) → P a b = 1) :
    IsSteinbergPairing P p := by
  refine ⟨hpow, fun a b hab => ?_⟩
  have hb : (b : K) = 1 - a := by rw [← hab]; ring
  by_cases hc : ∃ c : K, c ^ p = a
  · obtain ⟨c, hc⟩ := hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      have : (a : K) = 0 := by rw [← hc]; simp [hp.ne_zero]
      exact a.ne_zero this
    have : (Units.mk0 c hc0) ^ p = a := Units.ext (by simpa using hc)
    rw [← this, map_pow, MonoidHom.pow_apply, hpow]
  · push Not at hc
    obtain ⟨α, hα⟩ := hroots a
    have hirr := X_pow_sub_C_irreducible_of_prime hp hc
    have hint : IsIntegral K α := ⟨X ^ p - C (a : K), monic_X_pow_sub_C _ hp.ne_zero, by simp [hα]⟩
    have hmin : minpoly K α = X ^ p - C (a : K) :=
      (minpoly.eq_of_irreducible_of_monic hirr (by simp [hα]) (monic_X_pow_sub_C _ hp.ne_zero)).symm
    exact hnorm a b α hα ⟨1 - IntermediateField.AdjoinSimple.gen K α, by
      rw [norm_one_sub_gen hmin hint, hb]⟩

end NumberFieldKB.MilneCFT.Ch8
