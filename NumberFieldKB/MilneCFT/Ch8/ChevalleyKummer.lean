import Mathlib
import NumberFieldKB.MilneCFT.Ch8.ChevalleyLocal
import NumberFieldKB.MilneCFT.Ch8.ChevalleyGreedy
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.FrobeniusGeneration
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Frobenius.Kummer.LocalUnit
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Units.SUnit.Basic

/-!
# Kummer step of Chevalley's congruence theorem

Step 2 of the proof of Chevalley's theorem. Let `K'/K` be an extension
of number fields with a primitive `N`-th root of unity in `K'`, `S` a finite set of finite places of `K`, and
`A` a finite set of places of `K` containing those dividing `N`. There is a finite set `T` of places of `K`
outside `S ∪ A` such that every `S`-unit of `K` congruent to `1` at all places of `T` is an `N`-th power in
`K'`.

Proof: the `N`-th powers have finite index in the `S`-units (Tau Ceti
`relIndex_range_powMonoidHom_sUnits_numberField`); `M` = splitting field over `K'` of `∏_r (X^N - r)` for
representatives `r` contains an `N`-th root of every `S`-unit and is solvable over `K'` (Abel–Ruffini).
Frobenius elements of `M/K'` above places of `K` outside a finite set generate `Gal(M/K')` (Tau Ceti
`closure_isArithFrobAt_eq_top_tower`); finitely many suffice (`exists_finset_closure_eq_top`). At those places
`a ≡ 1` makes `a` an `N`-th power locally (`exists_pow_eq_of_valued_sub_one_lt`), and Tau Ceti
`exists_mem_intermediateField_pow_eq_iff_forall_exists_pow_eq_adicCompletion` with the bottom intermediate
field gives an `N`-th root in `K'`.
-/

open IsDedekindDomain NumberField
open scoped Classical

namespace NumberFieldKB.MilneCFT.Ch8.Chevalley

/-- Core of the Kummer step, for a given solvable Galois extension `M/K'` containing `N`-th roots of
all `S`-units. -/
theorem exists_places_pow_eq_aux {K K' M : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] [Field M] [NumberField M] [Algebra K M] [Algebra K' M] [IsScalarTower K K' M]
    [IsGalois K' M] [Group.IsSolvable (M ≃ₐ[K'] M)]
    {N : ℕ} {ζ : 𝓞 K'} (hζ : IsPrimitiveRoot ζ N)
    (S A : Finset (HeightOneSpectrum (𝓞 K))) (hA : ∀ v : HeightOneSpectrum (𝓞 K), (N : 𝓞 K) ∈ v.asIdeal → v ∈ A)
    (hroots : ∀ a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∃ α : M, α ^ N = algebraMap K M (a : K)) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint T (S ∪ A) ∧
      ∀ a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        (∀ v ∈ T, Valued.v (algebraMap K (v.adicCompletion K) (a : K) - 1) < 1) →
          ∃ c : K', c ^ N = algebraMap K K' (a : K) := by
  let R : HeightOneSpectrum (𝓞 K) → (M ≃ₐ[K'] M) → Prop := fun v τ =>
    v ∉ S ∪ A ∧ ∃ Q : HeightOneSpectrum (𝓞 M), Q.asIdeal.LiesOver v.asIdeal ∧
      IsArithFrobAt (𝓞 K') τ Q.asIdeal
  have hgen : ∀ F : Finset (HeightOneSpectrum (𝓞 K)),
      Subgroup.closure {g | ∃ i ∉ F, R i g} = ⊤ := by
    intro F
    refine eq_top_mono (Subgroup.closure_mono ?_)
      (TauCeti.ClassFieldTheory.closure_isArithFrobAt_eq_top_tower (K := K) (L := K') (M := M)
        (F ∪ (S ∪ A)))
    rintro τ ⟨v, hv, Q, hτ⟩
    refine ⟨v, fun h => hv (Finset.mem_union_left _ h), ?_, Q.1, Q.2, hτ⟩
    exact fun h => hv (Finset.mem_union_right _ h)
  obtain ⟨T, σ, hR, hcl⟩ := exists_finset_closure_eq_top R hgen
  refine ⟨T, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hv h
    exact (hR ⟨v, hv⟩).1 h
  intro a ha hcong
  choose Q hQ hfrob using fun i : T => (hR i).2
  let v : T → HeightOneSpectrum (𝓞 K') := fun i => (Q i).under (𝓞 K')
  have hQv : ∀ i : T, (Q i).asIdeal.LiesOver (v i).asIdeal := fun i => ⟨rfl⟩
  have hvi : ∀ i : T, (v i).asIdeal.LiesOver (i : HeightOneSpectrum (𝓞 K)).asIdeal := fun i =>
    have := hQ i
    have := hQv i
    Ideal.LiesOver.tower_bot (Q i).asIdeal (v i).asIdeal (i : HeightOneSpectrum (𝓞 K)).asIdeal
  have hn : ∀ i : T, (N : 𝓞 K') ∉ (v i).asIdeal := by
    intro i
    have := hQv i
    have := hvi i
    intro h
    have h2 : (N : 𝓞 K) ∈ (i : HeightOneSpectrum (𝓞 K)).asIdeal := by
      rw [Ideal.mem_of_liesOver (v i).asIdeal (i : HeightOneSpectrum (𝓞 K)).asIdeal (N : 𝓞 K)]
      simpa using h
    exact (hR i).1 (Finset.mem_union_right _ (hA _ h2))
  obtain ⟨α, hα⟩ := hroots a ha
  have hα' : α ^ N = algebraMap K' M (algebraMap K K' (a : K)) := by
    rw [hα, IsScalarTower.algebraMap_apply K K' M]
  have hmain := (TauCeti.NumberField.exists_mem_intermediateField_pow_eq_iff_forall_exists_pow_eq_adicCompletion
    (K := K') (M := M) (L := (⊥ : IntermediateField K' M)) (ι := T) (σ := σ)
    (Q := fun i => (Q i).asIdeal) (v := v) (n := N) (ζ := ζ) (a := algebraMap K K' (a : K)) (α := α)
    (fun i => (hfrob i))
    (by rw [IntermediateField.fixingSubgroup_bot]; exact hcl.symm) hζ ?_ ?_ hα').mpr ?_
  · obtain ⟨β, hβ, hβN⟩ := hmain
    obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hβ
    refine ⟨c, ?_⟩
    apply (algebraMap K' M).injective
    rw [map_pow]
    exact hβN
  · exact hn
  · intro i
    have := hvi i
    exact valuation_eq_one_of_valued_sub_one_lt (v i)
      (valued_sub_one_lt_of_liesOver (i : HeightOneSpectrum (𝓞 K)) (v i) (hcong i i.2))
  · intro i
    have := hvi i
    exact exists_pow_eq_of_valued_sub_one_lt (v i) (hn i)
      (valued_sub_one_lt_of_liesOver (i : HeightOneSpectrum (𝓞 K)) (v i) (hcong i i.2))

/-- **Kummer step.** -/
theorem exists_places_pow_eq {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] {N : ℕ} (hN : 0 < N) {ζ : 𝓞 K'} (hζ : IsPrimitiveRoot ζ N)
    (S A : Finset (HeightOneSpectrum (𝓞 K))) (hA : ∀ v : HeightOneSpectrum (𝓞 K), (N : 𝓞 K) ∈ v.asIdeal → v ∈ A) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint T (S ∪ A) ∧
      ∀ a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        (∀ v ∈ T, Valued.v (algebraMap K (v.adicCompletion K) (a : K) - 1) < 1) →
          ∃ c : K', c ^ N = algebraMap K K' (a : K) := by
  classical
  obtain ⟨G0, hG0, hGfin⟩ := Group.fg_iff.mp
    (inferInstance : Group.FG ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
  let G := hGfin.toFinset
  let f : ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) → Polynomial K' := fun g =>
    Polynomial.X ^ N - Polynomial.C (algebraMap K K' ((g : Kˣ) : K))
  let p : Polynomial K' := ∏ g ∈ G, f g
  let M := p.SplittingField
  have hpm : p.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun g _ => Polynomial.monic_X_pow_sub_C _ hN.ne'
  have : NumberField M := NumberField.of_module_finite K' M
  have : IsScalarTower K K' M := inferInstance
  have : Normal K' M := Normal.of_isSplittingField p
  have : Algebra.IsSeparable K' M := inferInstance
  have : IsGalois K' M := ⟨⟩
  have : Group.IsSolvable (M ≃ₐ[K'] M) := by
    have h : Group.IsSolvable p.Gal := by
      have := gal_prod_isSolvable (F := K') (s := G.val.map f) (by
        intro q hq
        obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hq
        exact gal_X_pow_sub_C_isSolvable _ _)
      exact this
    exact h
  refine exists_places_pow_eq_aux (K' := K') (M := M) hζ S A hA ?_
  intro a ha
  let P : Subgroup Kˣ := Subgroup.comap (Units.map (algebraMap K M : K →* M))
    (powMonoidHom N : Mˣ →* Mˣ).range
  have hle : (S : Set (HeightOneSpectrum (𝓞 K))).unit K ≤ P := by
    have hmap : (S : Set (HeightOneSpectrum (𝓞 K))).unit K =
        (Subgroup.closure (G : Set ↥((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) : Subgroup _).map (((S : Set (HeightOneSpectrum (𝓞 K))).unit K).subtype) := by
      have : (Subgroup.closure (G : Set ↥((S : Set (HeightOneSpectrum (𝓞 K))).unit K))) = ⊤ := by simpa [G] using hG0
      rw [this, ← MonoidHom.range_eq_map]
      simp
    rw [hmap, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    change _ ∈ P
    rw [Subgroup.mem_comap, MonoidHom.mem_range]
    have hsplit : (p.map (algebraMap K' M)).Splits := Polynomial.SplittingField.splits p
    have hdvd : (f g).map (algebraMap K' M) ∣ p.map (algebraMap K' M) :=
      Polynomial.map_dvd _ (Finset.dvd_prod_of_mem f hg)
    have hs2 := hsplit.of_dvd (Polynomial.map_ne_zero hpm.ne_zero) hdvd
    obtain ⟨α, hα⟩ := hs2.exists_eval_eq_zero (by
      simp only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
      rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hN.ne')]
      exact_mod_cast hN.ne')
    simp only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at hα
    have hα0 : α ≠ 0 := by
      rintro rfl
      have := hα
      rw [zero_pow hN.ne'] at this
      have h2 : algebraMap K M ((g : Kˣ) : K) = 0 := by
        simpa [IsScalarTower.algebraMap_apply K K' M] using this.symm
      exact (g : Kˣ).ne_zero ((map_eq_zero _).mp h2)
    refine ⟨Units.mk0 α hα0, ?_⟩
    ext
    simp [hα, IsScalarTower.algebraMap_apply K K' M]
  obtain ⟨u, hu⟩ := hle ha
  exact ⟨(u : M), by simpa using congrArg Units.val hu⟩

end NumberFieldKB.MilneCFT.Ch8.Chevalley
