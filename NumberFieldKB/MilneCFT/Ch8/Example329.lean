import NumberFieldKB.MilneCFT.Ch5Characters
import NumberFieldKB.MilneCFT.Ch8.Density

/-!
# Milne, *Class Field Theory*, Chapter V, Example 3.29: the conductor-discriminant formula for a quadratic field

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter V, Example 3.29
(pdf p. 174, printed p. 165). Locators give Milne's printed page numbers (printed page = pdf page − 9).

"Let $L = \mathbb Q[\sqrt d]$. Then $G \cong \mathbb Z/2\mathbb Z$, and there are only two characters $G \to
\mathbb C^\times$, namely, the trivial character $\chi_0$ and an injective character $\chi_1$. Therefore, the theorem
says that $\Delta_{L/\mathbb Q} = \mathfrak f_0(\chi_1) = \mathfrak f_0(L/\mathbb Q)$, as we showed in Example 3.11."

The file lives in Chapter VIII's folder because the conductor of the trivial character is computed with the
unconditional density theorem for ray classes (`Ch8.theorem_7_2`): every ray class contains primes outside any finite
set.

* `isCharConductor_one`: the conductor of the trivial character $\chi_0\circ\psi_{L/K}$ is the trivial modulus (over
  every number field $K$).
* `example_3_29`: for $L = \mathbb Q(\sqrt d)$, from the conductor-discriminant formula (`Theorem3_27`, named) and
  Example 3.11 (`Example3_11`, named): $\mathfrak d_{L/\mathbb Q} = \mathfrak f_0(\chi_1)$,
  $\mathfrak f_0(\chi_1) = \mathfrak f_0(L/\mathbb Q)$ for the conductor $\mathfrak f(L/\mathbb Q)$, and both are the
  ideal $(|\Delta_L|)$.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

/-- **The conductor of the trivial character** is the trivial modulus (`Modulus.one`): if $\mathfrak f$ is the conductor of
$\chi_0\circ\psi_{L/K}$ ($\chi_0$ trivial) then $\mathfrak f$ divides every modulus; in particular its finite part is
$\mathcal O_K$ and its infinite part is empty. -/
theorem isCharConductor_one {K : Type} [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (f : Modulus K) (hf : IsCharConductor (charOfGal L (1 : Gal(L/K) →* ℂˣ)) f) :
    f.finite = ⊤ ∧ f.infinite = ∅ := by
  classical
  obtain ⟨χ₁, ⟨⟨m', hm'S, hm'⟩, -⟩, ⟨S'', hfin, hsub, hcot⟩, -, hmin⟩ := hf
  have hkey : ∀ a : Kˣ, ∀ h : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals χ₁.S, χ₁.χ ⟨_, h⟩ = 1 := by
    intro a h
    have hx : toPrincipalIdeal (𝓞 K) K a ∈ coprimeIdeals m' := by
      rw [coprimeIdeals_eq_sIdeals, hm'S]; exact h
    set x : coprimeIdeals m' := ⟨_, hx⟩ with hxdef
    set c : RayClassGroup m' := QuotientGroup.mk x with hcdef
    have : Finite (RayClassGroup m') := (theorem_1_7_card m').1
    have hdens := Ch8.theorem_7_2 m' ⊥ c
    have hinf : {v : HeightOneSpectrum (𝓞 K) | ∃ hv : ¬ v.asIdeal ∣ m'.finite,
        c⁻¹ * rayClass m' v hv ∈ (⊥ : Subgroup (RayClassGroup m'))}.Infinite := by
      intro hfinite
      have h0 := NumberFieldKB.Chebotarev.hasDirichletDensity_of_finite hfinite
      have h2 := NumberFieldKB.Chebotarev.HasDirichletDensity.unique h0 hdens
      rw [Subgroup.index_bot] at h2
      have hpos : 0 < Nat.card (RayClassGroup m') := Nat.card_pos
      have : (0 : ℝ) < 1 / (Nat.card (RayClassGroup m') : ℝ) := by positivity
      linarith
    obtain ⟨v, ⟨hv, hvc⟩, hvS⟩ := hinf.exists_notMem_finite hfin
    rw [Subgroup.mem_bot, inv_mul_eq_one] at hvc
    have hq : QuotientGroup.mk x = (QuotientGroup.mk (coprimePrime m' v hv) : RayClassGroup m') := hvc
    rw [QuotientGroup.eq] at hq
    obtain ⟨b, hb, hbeq⟩ := hq
    have hbS : toPrincipalIdeal (𝓞 K) K b ∈ sIdeals χ₁.S := by
      rw [← hm'S]; exact rayPrincipal_le m' ⟨b, hb, rfl⟩
    have hPS : (coprimePrime m' v hv : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ sIdeals S'' := by
      intro w hw
      have hwv : w ≠ v := by rintro rfl; exact hvS hw
      exact FractionalIdeal.count_maximal_coprime K w hwv.symm
    have hPS' : (coprimePrime m' v hv : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ sIdeals χ₁.S := by
      rw [← hm'S]; exact (coprimePrime m' v hv).2
    have hPS0 : (coprimePrime m' v hv : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈
        sIdeals (charOfGal L (1 : Gal(L/K) →* ℂˣ)).S :=
      fun w hw => hPS w (hsub (Or.inl hw))
    have h1 := hcot _ hPS hPS0 hPS'
    have h1' : χ₁.χ ⟨_, hPS'⟩ = 1 := by
      rw [← h1]; rfl
    have hbχ : χ₁.χ ⟨toPrincipalIdeal (𝓞 K) K b, hbS⟩ = 1 := hm' b hb hbS
    have hmul : (⟨_, hPS'⟩ : sIdeals χ₁.S) = ⟨_, h⟩ * ⟨toPrincipalIdeal (𝓞 K) K b, hbS⟩ := by
      apply Subtype.ext
      have : (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ)⁻¹ * (coprimePrime m' v hv : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
          toPrincipalIdeal (𝓞 K) K b := hbeq.symm
      show (coprimePrime m' v hv : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = x * toPrincipalIdeal (𝓞 K) K b
      rw [← this]; group
    rw [hmul, map_mul, hbχ, mul_one] at h1'
    exact h1'
  have hone : (Modulus.one K).Dvd (Modulus.one K) := ⟨dvd_rfl, subset_rfl⟩
  have hdvd := hmin (Modulus.one K) (by
      intro v hv
      exfalso
      have : (⊤ : Ideal (𝓞 K)) ≤ v.asIdeal := Ideal.dvd_iff_le.1 hv
      exact v.isPrime.ne_top (top_le_iff.1 this)) (fun a _ h => hkey a h)
  refine ⟨top_le_iff.1 (Ideal.dvd_iff_le.1 hdvd.1), ?_⟩
  exact Set.subset_eq_empty hdvd.2 rfl

/-- **Example 3.29** (Milne, *CFT*, V, Example 3.29, p. 165): for $L = \mathbb Q(\sqrt d)$ ($d \ne 1$ square-free) and a
nontrivial character $\chi_1$ of $\mathrm{Gal}(L/\mathbb Q)$, the conductor-discriminant formula (`Theorem3_27`, named)
gives $\mathfrak d_{L/\mathbb Q} = \mathfrak f_0(\chi_1)$ and $\mathfrak f_0(\chi_1) = \mathfrak f_0(L/\mathbb Q)$; with
Example 3.11 (`Example3_11`, named) both equal $(|\Delta_L|)$. Here `f χ` is the conductor of $\chi\circ\psi_{L/\mathbb Q}$
(Milne's $\mathfrak f(\chi)$) and $\mathfrak f_0$ is its finite part. -/
@[kb "milne2020cft" "v4.03, Ch. V, Example 3.29, p. 165"]
theorem example_3_29 (h327 : Theorem3_27 ℚ) (h311 : Example3_11)
    (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] (d : ℤ) (s : L) (hd : Squarefree d) (hd1 : d ≠ 1)
    (hs : s ^ 2 = d) (hL : Module.finrank ℚ L = 2)
    (f : (Gal(L/ℚ) →* ℂˣ) → Modulus ℚ) (hf : ∀ χ, IsCharConductor (charOfGal L χ) (f χ))
    (χ₁ : Gal(L/ℚ) →* ℂˣ) (hχ₁ : χ₁ ≠ 1) :
    relDiscr ℚ L = (f χ₁).finite ∧
      (∀ g : Modulus ℚ, IsArtinConductor L g → (f χ₁).finite = g.finite) ∧
      (f χ₁).finite = Ideal.span {((discr L).natAbs : 𝓞 ℚ)} := by
  classical
  have hcard : Nat.card Gal(L/ℚ) = 2 := by
    exact (IsGalois.card_aut_eq_finrank ℚ L).trans hL
  have : Finite Gal(L/ℚ) := Nat.finite_of_card_ne_zero (by omega)
  -- every character is `1` or `χ₁`
  have hsq : ∀ (χ : Gal(L/ℚ) →* ℂˣ) (g : Gal(L/ℚ)), g ≠ 1 → (∀ x : Gal(L/ℚ), x = 1 ∨ x = g) →
      χ g = 1 ∨ χ g = -1 := by
    intro χ g hg hall
    have hgg : g * g = 1 := by
      rcases hall (g * g) with h | h
      · exact h
      · exact absurd (by simpa using h) hg
    have h2 : ((χ g : ℂˣ) : ℂ) * ((χ g : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul, hgg, map_one, Units.val_one]
    rcases mul_self_eq_one_iff.1 h2 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by simpa using h))
  have hall : ∃ g : Gal(L/ℚ), g ≠ 1 ∧ ∀ x : Gal(L/ℚ), x = 1 ∨ x = g := by
    obtain ⟨g, hg, huniq⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/ℚ))).1 hcard
    refine ⟨g, hg, fun x => ?_⟩
    by_cases hx : x = 1
    · exact Or.inl hx
    · exact Or.inr (huniq x hx)
  obtain ⟨g, hg, hgall⟩ := hall
  have hchar : ∀ χ : Gal(L/ℚ) →* ℂˣ, χ = 1 ∨ χ = χ₁ := by
    intro χ
    by_cases h1 : χ = 1
    · exact Or.inl h1
    · refine Or.inr ?_
      have hne : ∀ ψ : Gal(L/ℚ) →* ℂˣ, ψ ≠ 1 → ψ g = -1 := by
        intro ψ hψ
        rcases hsq ψ g hg hgall with h | h
        · exfalso; apply hψ
          ext x
          rcases hgall x with rfl | rfl
          · simp
          · simpa using h
        · exact h
      ext x
      rcases hgall x with rfl | rfl
      · simp
      · rw [hne χ h1, hne χ₁ hχ₁]
  have hf1 := isCharConductor_one L (f 1) (hf 1)
  have hf1dvd : ∀ m : Modulus ℚ, (f 1).Dvd m := fun m =>
    ⟨by rw [hf1.1]; exact Ideal.dvd_iff_le.2 le_top, by rw [hf1.2]; exact Set.empty_subset _⟩
  have hdisc := h327.disc L f hf
  have hprod : ∏ᶠ χ : Gal(L/ℚ) →* ℂˣ, (f χ).finite = (f χ₁).finite := by
    rw [finprod_eq_prod_of_mulSupport_subset (fun χ => (f χ).finite) (s := {1, χ₁})
      (fun χ _ => by
        rcases hchar χ with rfl | rfl <;> simp),
      Finset.prod_pair (Ne.symm hχ₁), hf1.1, Ideal.top_mul]
  have hartin : ∀ g : Modulus ℚ, IsArtinConductor L g → (f χ₁).finite = g.finite := by
    intro g hg
    have h := (h327.lcm L f hf g).1 hg
    have h' : ∀ m : Modulus ℚ, g.Dvd m ↔ (f χ₁).Dvd m := by
      intro m
      rw [h m]
      refine ⟨fun H => H χ₁, fun H χ => ?_⟩
      rcases hchar χ with rfl | rfl
      · exact hf1dvd m
      · exact H
    have hg1 : (f χ₁).Dvd g := (h' g).1 ⟨dvd_rfl, subset_rfl⟩
    have hg2 : g.Dvd (f χ₁) := (h' (f χ₁)).2 ⟨dvd_rfl, subset_rfl⟩
    exact le_antisymm (Ideal.dvd_iff_le.1 hg2.1) (Ideal.dvd_iff_le.1 hg1.1)
  refine ⟨hdisc.trans hprod, hartin, ?_⟩
  exact hartin _ (h311.conductor L d s hd hd1 hs hL)

end NumberFieldKB.MilneCFT
