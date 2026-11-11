import NumberFieldKB.MilneCFT.Ch8.Eighth
import NumberFieldKB.MilneCFT.Ch8.Remark15aBridge
import NumberFieldKB.TauCetiPort.RingTheory.DedekindDomain.SInteger.SelmerGroup.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Grunwald–Wang: finitely many auxiliary places detect `n`-th powers among Selmer elements

**Proved here:** `GW.exists_places_detect_pow`. Let `S` be a finite set of finite places and suppose `P(n, S') = K^{×n}`
for every finite `S'` (the non-special case, `GW.powSet_subset_of_isCyclic`). Then there is a finite set `P` of
finite places, disjoint from `S` and prime to `n`, such that every `a ∈ K^×` whose valuation is divisible by `n` at
every finite place outside `S` and which is a local `n`-th power at every place of `P` is an `n`-th power in `K`.

Proof. The Selmer group `K(S, n)` is finite (Tau Ceti `IsDedekindDomain.selmerGroup.finite`: class number theorem
and Dirichlet's unit theorem). For each of its classes not in `K^{×n}`, a representative is not in `P(n, S ∪ {v ∣ n})`,
so it is a non-`n`-th power at some place outside `S`, prime to `n`; collect these places. Being a local `n`-th power
is a property of the class modulo `K^{×n}`.
-/

open IsDedekindDomain NumberField

namespace NumberFieldKB.MilneCFT.Ch8.GW

variable {K : Type} [Field K] [NumberField K]

/-- **Auxiliary places detecting `n`-th powers** (for Grunwald–Wang, Artin–Tate X §2). -/
theorem exists_places_detect_pow {n : ℕ} (hn : 0 < n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hP : ∀ S' : Set (HeightOneSpectrum (𝓞 K)), S'.Finite → ∀ a ∈ powSet n S', ∃ b : Kˣ, b ^ n = a) :
    ∃ P : Finset (HeightOneSpectrum (𝓞 K)), Disjoint P S ∧ (∀ u ∈ P, (n : 𝓞 K) ∉ u.asIdeal) ∧
      ∀ a : Kˣ, (∀ u : HeightOneSpectrum (𝓞 K), u ∉ S → ∃ k : ℤ, u.valuation K (a : K) = WithZero.exp ((n : ℤ) * k)) →
        (∀ u ∈ P, IsLocalPow n (a : K) u) → ∃ b : Kˣ, b ^ n = a := by
  classical
  have hn0 : ((n : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hn.ne'
  have hD : {v : HeightOneSpectrum (𝓞 K) | (n : 𝓞 K) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (Ideal.span_singleton_eq_bot.not.mpr hn0)).subset fun v hv => ?_
    exact (Ideal.dvd_span_singleton).2 hv
  set T : Set (HeightOneSpectrum (𝓞 K)) := (S : Set _) ∪ {v | (n : 𝓞 K) ∈ v.asIdeal} with hT
  have hTf : T.Finite := S.finite_toSet.union hD
  have : NeZero n := ⟨hn.ne'⟩
  have : Finite (S : Set (HeightOneSpectrum (𝓞 K))) := S.finite_toSet
  have : Finite (selmerGroup (R := 𝓞 K) (K := K) (S := (S : Set _)) (n := n)) := inferInstance
  have := Fintype.ofFinite (selmerGroup (R := 𝓞 K) (K := K) (S := (S : Set _)) (n := n))
  let rep : selmerGroup (R := 𝓞 K) (K := K) (S := (S : Set _)) (n := n) → Kˣ :=
    fun c => Quotient.out (s := QuotientGroup.leftRel _) c.1
  have hrep : ∀ c, (QuotientGroup.mk (rep c) : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = c.1 :=
    fun c => Quotient.out_eq' (s₁ := QuotientGroup.leftRel _) c.1
  have key : ∀ c, ∃ U : Finset (HeightOneSpectrum (𝓞 K)), (∀ u ∈ U, u ∉ T) ∧
      ((¬ ∃ b : Kˣ, b ^ n = rep c) → ∃ u ∈ U, ¬ IsLocalPow n (rep c : K) u) := by
    intro c
    by_cases h : ∃ b : Kˣ, b ^ n = rep c
    · exact ⟨∅, by simp, fun h' => absurd h h'⟩
    · have : rep c ∉ powSet n T := fun hm => h (hP T hTf _ hm)
      simp only [powSet, Set.mem_ofPred_eq, not_forall] at this
      obtain ⟨u, hu, hl⟩ := this
      exact ⟨{u}, by simpa using hu, fun _ => ⟨u, by simp, hl⟩⟩
  choose U hU1 hU2 using key
  refine ⟨Finset.univ.biUnion U, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro u hu huS
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 hu
    exact hU1 c u hc (Or.inl huS)
  · intro u hu hd
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 hu
    exact hU1 c u hc (Or.inr hd)
  · intro a ha hloc
    have hmem : (QuotientGroup.mk a : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
        selmerGroup (R := 𝓞 K) (K := K) (S := (S : Set _)) (n := n) := by
      intro v hv
      rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
      obtain ⟨k, hk⟩ := ha v hv
      have h1 : (v.valuationOfNeZero a : WithZero (Multiplicative ℤ)) = ((Multiplicative.ofAdd ((n : ℤ) * k) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
        rw [HeightOneSpectrum.valuationOfNeZero_eq, hk]; rfl
      have h2 := WithZero.coe_injective h1
      rw [h2]
      exact ⟨k, rfl⟩
    set c : selmerGroup (R := 𝓞 K) (K := K) (S := (S : Set _)) (n := n) := ⟨_, hmem⟩ with hc
    have hq : (QuotientGroup.mk (rep c) : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = QuotientGroup.mk a :=
      hrep c
    rw [QuotientGroup.eq] at hq
    obtain ⟨b, hb⟩ := hq
    -- hb : b ^ n = (rep c)⁻¹ * a
    have hb' : a = rep c * b ^ n := by
      have : (powMonoidHom n : Kˣ →* Kˣ) b = b ^ n := rfl
      rw [this] at hb
      rw [hb]; group
    by_cases h : ∃ b' : Kˣ, b' ^ n = rep c
    · obtain ⟨b', hb''⟩ := h
      exact ⟨b' * b, by rw [mul_pow, hb'', hb']⟩
    · exfalso
      obtain ⟨u, huU, hl⟩ := hU2 c h
      apply hl
      obtain ⟨x, hx⟩ := hloc u (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, huU⟩)
      refine ⟨x * algebraMap K (u.adicCompletion K) ((b⁻¹ : Kˣ) : K), ?_⟩
      have : (rep c : K) = a * ((b⁻¹ : Kˣ) : K) ^ n := by
        have : rep c = a * (b⁻¹) ^ n := by rw [hb']; group
        exact_mod_cast congrArg (fun z : Kˣ => (z : K)) this
      rw [this, map_mul, map_pow, mul_pow, hx]

/-- **Auxiliary places detecting `P(n, S ∪ {v ∣ n})`** (the form used in the special case of Grunwald–Wang): there is a
finite set `P` of places outside `S`, prime to `n`, such that every `a ∈ K^×` with valuation divisible by `n` outside `S`
which is a local `n`-th power at every place of `P` is a local `n`-th power at every finite place outside `S ∪ {v ∣ n}`. -/
theorem exists_places_detect_powSet {n : ℕ} (hn : 0 < n) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ P : Finset (HeightOneSpectrum (𝓞 K)), Disjoint P S ∧ (∀ u ∈ P, (n : 𝓞 K) ∉ u.asIdeal) ∧
      ∀ a : Kˣ, (∀ u : HeightOneSpectrum (𝓞 K), u ∉ S → ∃ k : ℤ, u.valuation K (a : K) = WithZero.exp ((n : ℤ) * k)) →
        (∀ u ∈ P, IsLocalPow n (a : K) u) →
          a ∈ powSet n ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ {v | (n : 𝓞 K) ∈ v.asIdeal}) := by
  classical
  have hn0 : ((n : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hn.ne'
  set T : Set (HeightOneSpectrum (𝓞 K)) := (S : Set _) ∪ {v | (n : 𝓞 K) ∈ v.asIdeal} with hT
  have : NeZero n := ⟨hn.ne'⟩
  have : Finite (S : Set (HeightOneSpectrum (𝓞 K))) := S.finite_toSet
  have : Finite (selmerGroup (R := 𝓞 K) (K := K) (S := (S : Set _)) (n := n)) := inferInstance
  have := Fintype.ofFinite (selmerGroup (R := 𝓞 K) (K := K) (S := (S : Set _)) (n := n))
  let rep : selmerGroup (R := 𝓞 K) (K := K) (S := (S : Set _)) (n := n) → Kˣ :=
    fun c => Quotient.out (s := QuotientGroup.leftRel _) c.1
  have hrep : ∀ c, (QuotientGroup.mk (rep c) : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = c.1 :=
    fun c => Quotient.out_eq' (s₁ := QuotientGroup.leftRel _) c.1
  have key : ∀ c, ∃ U : Finset (HeightOneSpectrum (𝓞 K)), (∀ u ∈ U, u ∉ T) ∧
      (rep c ∉ powSet n T → ∃ u ∈ U, ¬ IsLocalPow n (rep c : K) u) := by
    intro c
    by_cases h : rep c ∈ powSet n T
    · exact ⟨∅, by simp, fun h' => absurd h h'⟩
    · have h' := h
      simp only [powSet, Set.mem_ofPred_eq, not_forall] at h'
      obtain ⟨u, hu, hl⟩ := h'
      exact ⟨{u}, by simpa using hu, fun _ => ⟨u, by simp, hl⟩⟩
  choose U hU1 hU2 using key
  refine ⟨Finset.univ.biUnion U, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro u hu huS
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 hu
    exact hU1 c u hc (Or.inl huS)
  · intro u hu hd
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 hu
    exact hU1 c u hc (Or.inr hd)
  · intro a ha hloc
    have hmem : (QuotientGroup.mk a : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
        selmerGroup (R := 𝓞 K) (K := K) (S := (S : Set _)) (n := n) := by
      intro v hv
      rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
      obtain ⟨k, hk⟩ := ha v hv
      have h1 : (v.valuationOfNeZero a : WithZero (Multiplicative ℤ)) =
          ((Multiplicative.ofAdd ((n : ℤ) * k) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
        rw [HeightOneSpectrum.valuationOfNeZero_eq, hk]; rfl
      have h2 := WithZero.coe_injective h1
      rw [h2]
      exact ⟨k, rfl⟩
    set c : selmerGroup (R := 𝓞 K) (K := K) (S := (S : Set _)) (n := n) := ⟨_, hmem⟩ with hc
    have hq : (QuotientGroup.mk (rep c) : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = QuotientGroup.mk a :=
      hrep c
    rw [QuotientGroup.eq] at hq
    obtain ⟨b, hb⟩ := hq
    have hb' : a = rep c * b ^ n := by
      have : (powMonoidHom n : Kˣ →* Kˣ) b = b ^ n := rfl
      rw [this] at hb
      rw [hb]; group
    by_cases h : rep c ∈ powSet n T
    · rw [hb']
      exact R15a.mul_mem_powSet h (R15a.pow_mem_powSet n T b)
    · exfalso
      obtain ⟨u, huU, hl⟩ := hU2 c h
      apply hl
      obtain ⟨x, hx⟩ := hloc u (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, huU⟩)
      refine ⟨x * algebraMap K (u.adicCompletion K) ((b⁻¹ : Kˣ) : K), ?_⟩
      have : (rep c : K) = a * ((b⁻¹ : Kˣ) : K) ^ n := by
        have : rep c = a * (b⁻¹) ^ n := by rw [hb']; group
        exact_mod_cast congrArg (fun z : Kˣ => (z : K)) this
      rw [this, map_mul, map_pow, mul_pow, hx]

end NumberFieldKB.MilneCFT.Ch8.GW
