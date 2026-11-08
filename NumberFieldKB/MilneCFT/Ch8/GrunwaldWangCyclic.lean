import NumberFieldKB.MilneCFT.Ch8.Remark15aUncond

/-!
# Grunwald–Wang, non-special case: `P(n, S) = K^{×n}` when the `2`-power cyclotomic extensions are cyclic

**Proved here:** `GW.powSet_subset_of_isCyclic`: if `K(ζ_{2^t})/K` is cyclic for every `2^t ∣ n`, then every element
of `P(n, S)` (Milne, *CFT*, VIII, p. 230; `powSet`) is an `n`-th power in `K` (Artin–Tate X, Theorem 1, the
non-special case).

Proof. For `n = 2^r m`, `m` odd, elements of `P(n, S)` are `m`-th powers of elements of `P(2^r, S)` (as in
`R15a.powSet_dichotomy`). For `q = 2^r`, every `σ ∈ Gal(M/K)`, `M = K(ζ_q, a^{1/q})`, fixes a root `ζ^i α`
(`R15a.forall_fixed_of_mem_powSet`); the image of the cyclotomic character `Gal(M/K) → (ℤ/q)^×` is isomorphic to
`Gal(K(ζ)/K) ≅ Gal(K(ζ_q)/K)` (both are `Gal(M/K)` modulo the stabilizer of `ζ`), hence cyclic, and
`R15a.exists_fixed_of_isCyclic_map` with `Γ = ⊤` gives a root fixed by everything.
-/

open IsDedekindDomain NumberField

namespace NumberFieldKB.MilneCFT.Ch8.GW

variable {K : Type} [Field K] [NumberField K]

theorem isCyclic_map_autToPow {M : Type} [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)
    (hcyc : IsCyclic (CyclotomicField q K ≃ₐ[K] CyclotomicField q K)) :
    IsCyclic ((⊤ : Subgroup (M ≃ₐ[K] M)).map (hζ.autToPow K)) := by
  let E := IntermediateField.adjoin K {ζ}
  haveI : IsCyclotomicExtension {q} K E := hζ.intermediateField_adjoin_isCyclotomicExtension K
  haveI : IsGalois K E := IsCyclotomicExtension.isGalois {q} K E
  haveI : Normal K E := inferInstance
  let e : CyclotomicField q K ≃ₐ[K] E := IsCyclotomicExtension.algEquiv {q} K (CyclotomicField q K) E
  haveI hE : IsCyclic (E ≃ₐ[K] E) :=
    isCyclic_of_surjective (AlgEquiv.autCongr e).toMonoidHom (AlgEquiv.autCongr e).surjective
  let ζE : E := ⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩
  have hζE : IsPrimitiveRoot ζE q :=
    IsPrimitiveRoot.of_map_of_injective (f := (E.val : E →+* M)) (by simpa [ζE] using hζ) E.val.injective
  have key : ∀ σ : M ≃ₐ[K] M, hζ.autToPow K σ = hζE.autToPow K (AlgEquiv.restrictNormalHom E σ) := by
    intro σ
    apply Units.ext
    apply ZMod.val_injective
    have h1 := hζ.autToPow_spec K σ
    have h2 := hζE.autToPow_spec K (AlgEquiv.restrictNormalHom E σ)
    have h3 : ((AlgEquiv.restrictNormalHom E σ) ζE : M) = σ ζ := by
      show ((σ.restrictNormal E) ζE : M) = σ ζ
      exact AlgEquiv.restrictNormal_commutes σ E ζE
    have h4 : ζ ^ ((hζE.autToPow K (AlgEquiv.restrictNormalHom E σ) : ZMod q).val) = σ ζ := by
      calc _ = ((ζE ^ ((hζE.autToPow K (AlgEquiv.restrictNormalHom E σ) : ZMod q).val) : E) : M) := by
            exact (map_pow E.val ζE _).symm
        _ = (((AlgEquiv.restrictNormalHom E σ) ζE : E) : M) := by rw [h2]
        _ = σ ζ := h3
    have := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h1.trans h4.symm)
    exact this
  have hmap : (⊤ : Subgroup (M ≃ₐ[K] M)).map (hζ.autToPow K) = (hζE.autToPow K).range := by
    ext x
    constructor
    · rintro ⟨σ, -, rfl⟩
      exact ⟨_, (key σ).symm⟩
    · rintro ⟨τ, rfl⟩
      obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) M τ
      exact ⟨σ, trivial, by rw [key, hσ]⟩
  rw [hmap]
  exact isCyclic_of_surjective (hζE.autToPow K).rangeRestrict (hζE.autToPow K).rangeRestrict_surjective

/-- **Non-special case of Remark VIII.1.5 (a)**: `P(n, S) = K^{×n}` when `K(ζ_{2^t})/K` is cyclic for all `2^t ∣ n`. -/
theorem powSet_subset_of_isCyclic {n : ℕ} (hn : 0 < n) {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    (hcyc : ∀ t : ℕ, 2 ^ t ∣ n →
      IsCyclic (CyclotomicField (2 ^ t) K ≃ₐ[K] CyclotomicField (2 ^ t) K)) :
    ∀ a ∈ powSet n S, ∃ b : Kˣ, b ^ n = a := by
  intro a ha
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  obtain ⟨c, hc⟩ := R15a.powSet_odd hS m hm a (R15a.mem_powSet_of_dvd (Dvd.intro_left _ rfl) ha)
  have hcop : Nat.Coprime m (2 ^ r) := (Nat.coprime_two_right.2 hm).pow_right r
  have hcS : c ∈ powSet (2 ^ r) S :=
    R15a.mem_powSet_of_pow_mem hcop (hc ▸ R15a.mem_powSet_of_dvd (Dvd.intro _ rfl) ha)
  have hq : 0 < 2 ^ r := pow_pos two_pos r
  haveI : NeZero (2 ^ r) := ⟨hq.ne'⟩
  obtain ⟨M, _, _, _, _, _, ζ, α, -, hζ, hα, -⟩ := R15a.exists_splitting (K := K) hq (c : K) (c : K)
  have hfa := R15a.forall_fixed_of_mem_powSet hq hζ hS hcS hα
  have hcI := isCyclic_map_autToPow (K := K) hζ (hcyc r (Dvd.intro _ rfl))
  obtain ⟨i, hi⟩ := R15a.exists_fixed_of_isCyclic_map hζ hfa ⊤ hcI
  obtain ⟨b, hb⟩ := R15a.pow_of_all_fixed hζ hα (fun g => hi g trivial)
  obtain ⟨d, hd⟩ := R15a.exists_units_pow hq hb
  exact ⟨d, by rw [pow_mul, hd, hc]⟩

end NumberFieldKB.MilneCFT.Ch8.GW
