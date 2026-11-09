import NumberFieldKB.MilneCFT.Ch7.ArtinMap
import NumberFieldKB.MilneCFT.Ch7.Cohomology
import NumberFieldKB.HilbertClassField.Artin

/-!
# Milne, *Class Field Theory*, Chapter VII §8: completion of the proof of the reciprocity law

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

* **Theorem 8.1 (a)** (`Theorem8_1a`, named statement): every global Artin map (`IsGlobalArtinMap`, Chapter VII §1)
  is trivial on the principal ideles $K^\times$. Part (b) (the sum of the local invariants of a class in $H^2(L/K)$ is
  $0$) needs the local invariant maps of Chapter III at the completions and is not formalized here.
* **Theorem 8.1 (a) implies the reciprocity law** (`reciprocity_of_thm_8_1a`, p. 221): with the second inequality
  (Theorem 5.1), $\psi_{L/K}$ is onto with kernel $K^\times\mathrm{Nm}(\mathbb I_L)$.
* **Example 8.2** (`Example8_2`, named statement): Theorem 8.1 (a) for $\mathbb Q(\zeta_m)/\mathbb Q$ (proved in Milne
  from the explicit local Artin maps of Chapter I, Example 3.13).
* **Lemma 8.4 (a)** (`lemma_8_4a`): Theorem 8.1 (a) passes to subextensions.
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.Ch7

variable (K : Type) [Field K] [NumberField K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

/-- **Theorem 8.1 (a)** (named statement; Milne, *CFT*, Chapter VII, p. 221): for every finite abelian extension
$L/K$ of number fields, the global Artin map $\psi_{L/K}$ takes the value $1$ on the principal ideles $K^\times$. -/
@[kb "milne2020cft" "Ch. VII, Thm. 8.1 (a) (input)"]
structure Theorem8_1a : Prop where
  principal_le_ker : ∀ ψ : ∀ E : AbExt K Ω, IdeleGroup (𝓞 K) K →* Gal(E.L/K), IsGlobalArtinMap K Ω ψ →
    ∀ E : AbExt K Ω, IdeleGroup.principalSubgroup (𝓞 K) K ≤ (ψ E).ker

variable {K Ω}

/-- There is a unit of $K_v$ with $\mathrm{ord}_v = 1$ (the image of a uniformizer of $K$). -/
theorem exists_unit_ordAt_eq_one (v : HeightOneSpectrum (𝓞 K)) :
    ∃ a : (v.adicCompletion K)ˣ, ordAt v a = 1 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have h : Valued.v (algebraMap K (v.adicCompletion K) π) = WithZero.exp (-1 : ℤ) := by
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π).trans hπ
  have hne : algebraMap K (v.adicCompletion K) π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  refine ⟨Units.mk0 _ hne, ?_⟩
  simp [ordAt, h]

/-- **Theorem 8.1 (a) implies the reciprocity law** (Milne, *CFT*, Chapter VII, p. 221): if $\psi$ is a global Artin
map trivial on $K^\times$ (Theorem 8.1 (a)), then for every finite abelian $L/K$, $\psi_{L/K}$ is surjective (the
Frobenius elements generate, Chebotarev) and its kernel is $K^\times\cdot\mathrm{Nm}(\mathbb I_L)$ (the second
inequality, Theorem 5.1 (a)), so $\mathbb I_K/K^\times\mathrm{Nm}(\mathbb I_L)\cong\mathrm{Gal}(L/K)$. -/
@[kb "milne2020cft" "Ch. VII, §8, p. 221 (Theorem 8.1 (a) implies the reciprocity law)"]
theorem reciprocity_of_thm_8_1a (h51 : Theorem5_1 K) (h81 : Theorem8_1a K Ω)
    (ψ : ∀ E : AbExt K Ω, IdeleGroup (𝓞 K) K →* Gal(E.L/K)) (hψ : IsGlobalArtinMap K Ω ψ) (E : AbExt K Ω) :
    Function.Surjective (ψ E) ∧ (ψ E).ker = principalNormIdeles K E.L := by
  have hsurj : Function.Surjective (ψ E) := by
    intro σ
    obtain ⟨v, hv, Q, hQ⟩ := (NumberFieldKB.HilbertClassField.setOf_frobAt_eq_infinite K E.L σ).nonempty
    obtain ⟨a, ha⟩ := exists_unit_ordAt_eq_one v
    exact ⟨IdeleGroup.ofAdicCompletion (𝓞 K) K v a, by rw [hψ.unramified E v hv Q a, ha, zpow_one, hQ]⟩
  refine ⟨hsurj, ?_⟩
  have hle : principalNormIdeles K E.L ≤ (ψ E).ker :=
    sup_le (h81.principal_le_ker ψ hψ E) (hψ.norm_le_ker E)
  have hn : 0 < Module.finrank K E.L := Module.finrank_pos
  have hker : (ψ E).ker.index = Module.finrank K E.L := by
    rw [Subgroup.index, ← IsGalois.card_aut_eq_finrank]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv
  obtain ⟨_, hdvd⟩ := h51.index_dvd E.L
  have hd1 : (ψ E).ker.index ∣ (principalNormIdeles K E.L).index := Subgroup.index_dvd_of_le hle
  have heq : (principalNormIdeles K E.L).index = (ψ E).ker.index := by
    rw [hker] at hd1 ⊢
    exact Nat.dvd_antisymm hdvd hd1
  have hrel := Subgroup.relIndex_mul_index hle
  rw [heq] at hrel
  have h1 : (principalNormIdeles K E.L).relIndex (ψ E).ker = 1 := by
    have hpos : (ψ E).ker.index ≠ 0 := by rw [hker]; omega
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) (by rw [one_mul]; exact hrel)
  exact (le_antisymm (Subgroup.relIndex_eq_one.1 h1) hle)

/-- **Example 8.2** (named statement; Milne, *CFT*, Chapter VII, p. 221): Theorem 8.1 (a) holds for the cyclotomic
extensions $\mathbb Q(\zeta_m)/\mathbb Q$: every global Artin map of $\mathbb Q$ is trivial on $\mathbb Q^\times$ on
every finite abelian extension of $\mathbb Q$ generated by a root of unity. -/
@[kb "milne2020cft" "Ch. VII, Example 8.2 (input)"]
structure Example8_2 (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] : Prop where
  principal_le_ker : ∀ ψ : ArtinFamily ℚ Ω, IsGlobalArtinMap ℚ Ω ψ →
    ∀ (E : AbExt ℚ Ω) (m : ℕ), IsCyclotomicExtension {m} ℚ E.L →
      IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ ≤ (ψ E).ker

/-- **Lemma 8.4 (a)** (Milne, *CFT*, Chapter VII, p. 222): if Theorem 8.1 (a) holds for $L/K$, it holds for every
subextension $L\supseteq K'\supseteq K$ ($\psi_{K'/K}$ is $\psi_{L/K}$ followed by restriction). -/
@[kb "milne2020cft" "Ch. VII, Lemma 8.4 (a)"]
theorem lemma_8_4a (ψ : ∀ E : AbExt K Ω, IdeleGroup (𝓞 K) K →* Gal(E.L/K)) (hψ : IsGlobalArtinMap K Ω ψ)
    (E E' : AbExt K Ω) (h : E'.L ≤ E.L) (hE : IdeleGroup.principalSubgroup (𝓞 K) K ≤ (ψ E).ker) :
    IdeleGroup.principalSubgroup (𝓞 K) K ≤ (ψ E').ker := by
  intro x hx
  rw [MonoidHom.mem_ker, ← hψ.compat E E' h x, (MonoidHom.mem_ker).mp (hE hx), map_one]

end NumberFieldKB.MilneCFT.Ch7
