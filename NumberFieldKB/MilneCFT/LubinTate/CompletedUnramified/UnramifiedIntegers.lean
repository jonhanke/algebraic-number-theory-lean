import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.Unramified.Maximal
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.ResidueCorrespondence
import Mathlib.RingTheory.RootsOfUnity.Lemmas

/-!
# The integers of the maximal unramified extension

Let `K` be a nonarchimedean local field and `Ω` a separably closed extension of `K`.  Inside `Ω`
sits the maximal unramified extension `Kun` of `K`, the union of the finite unramified extensions
of `K` (as defined in the Tau Ceti port).  This file studies its ring of integers `Run`, defined as
the integral closure of the integers `𝒪[K]` of `K` in `Kun`.

The main results are the following.

* `Run` is a discrete valuation ring, and any uniformizer `π` of `K` is a uniformizer of `Run`
  (`exists_unit_mul_pow`, `irreducible_algebraMap`, `maximalIdeal_eq_span`).  The key point is that
  every nonzero element of `Run` lives in a finite unramified extension of `K`, where `π` is still
  a uniformizer, and units of the integers of that finite extension stay units of `Run`.
* The Frobenius automorphism of `Kun` over `K` preserves integrality, hence restricts to a ring
  automorphism `frobRun` of `Run`, fixing the integers of `K` and satisfying the Frobenius
  congruence `frobRun r ≡ r ^ q` modulo the maximal ideal, where `q` is the number of elements of
  the residue field of `K` (`frobRun_sub_pow_mem`).
* The residue field of `Run` is algebraically closed (`residue_isAlgClosed`).  Every residue class
  is fixed by some power of the `q`-th power map, because some power of Frobenius is the identity
  on the finite level containing a lift; and for each `f ≥ 1` the polynomial `X ^ (q ^ f) - X` has
  `q ^ f` distinct roots in the residue field, the residues of zero and of the powers of a
  primitive root of unity of order `q ^ f - 1`.
-/

open scoped ValuativeRel

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace NumberFieldKB.MilneCFT.CompletedUnramified

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

/-- The maximal unramified extension of `K` inside `Ω` (Tau Ceti). -/
abbrev Kun : IntermediateField K Ω := TauCeti.maximalUnramifiedExtension K Ω

/-- Its ring of integers: the integral closure of `𝒪[K]`. -/
abbrev Run : Type := integralClosure 𝒪[K] (Kun K Ω)

section Aux

open TauCeti ValuativeRel

/-- The inclusion of `Run` into `Ω`. -/
private def toΩ : Run K Ω →+* Ω :=
  ((Kun K Ω).val : Kun K Ω →+* Ω).comp (integralClosure 𝒪[K] (Kun K Ω)).val.toRingHom

private theorem toΩ_injective : Function.Injective (toΩ K Ω) :=
  fun _ _ h ↦ Subtype.ext (Subtype.ext h)

private theorem toΩ_algebraMap (a : 𝒪[K]) :
    toΩ K Ω (algebraMap 𝒪[K] (Run K Ω) a) = algebraMap K Ω a := rfl

/-- Frobenius of `K^un`, restricted to the integers. -/
def frobRun : Run K Ω ≃+* Run K Ω :=
  (((TauCeti.maximalUnramifiedFrobenius K Ω).restrictScalars 𝒪[K]).mapIntegralClosure).toRingEquiv

theorem coe_frobRun (r : Run K Ω) :
    (((frobRun K Ω r : Kun K Ω)) : Ω) = ((TauCeti.maximalUnramifiedFrobenius K Ω (r : Kun K Ω) : Kun K Ω) : Ω) :=
  rfl

private theorem toΩ_frobRun_pow (n : ℕ) (r : Run K Ω) :
    toΩ K Ω ((frobRun K Ω ^ n) r) =
      (((TauCeti.maximalUnramifiedFrobenius K Ω ^ n) (r : Kun K Ω) : Kun K Ω) : Ω) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ]
    change toΩ K Ω ((frobRun K Ω ^ n) (frobRun K Ω r)) = _
    rw [ih, pow_succ, AlgEquiv.mul_apply]
    rfl

/-- Run a statement inside a finite unramified level `K_f`, carrying its canonical structure of
nonarchimedean local field, together with the comparison of the integers of the level with `Run`
and of Frobenius with the Frobenius of the level. -/
private theorem withLevel {f : ℕ} (hf : f ≠ 0) {P : Prop}
    (h : ∀ (L : IntermediateField K Ω), L = unramifiedExtension K Ω f →
      ∀ [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
      [ValuativeExtension K L] [IsUnramified K L] [FiniteDimensional K L] [IsGalois K L],
      (∀ x : Run K Ω, toΩ K Ω x ∈ L → ∃ y : 𝒪[L], ((y : L) : Ω) = toΩ K Ω x) →
      (∀ a : 𝒪[L], ∃ r : Run K Ω, toΩ K Ω r = ((a : L) : Ω)) →
      (∀ (n : ℕ) (r : Run K Ω) (y : L), toΩ K Ω r = (y : Ω) →
        toΩ K Ω ((frobRun K Ω ^ n) r) =
          (((frobeniusAlgEquiv (K := K) (L := L) ^ n) y : L) : Ω)) → P) : P := by
  letI := finiteIntermediateFieldValuativeRel K Ω (unramifiedExtension K Ω f)
  letI := finiteIntermediateFieldTopology K Ω (unramifiedExtension K Ω f)
  haveI := finiteIntermediateField_isNonarchimedeanLocalField K Ω (unramifiedExtension K Ω f)
  haveI := finiteIntermediateField_valuativeExtension K Ω (unramifiedExtension K Ω f)
  haveI : IsUnramified K (unramifiedExtension K Ω f) := isUnramified_unramifiedExtension hf
  have hle : unramifiedExtension K Ω f ≤ Kun K Ω :=
    unramifiedExtension_le_maximalUnramifiedExtension K Ω f
  let ι : unramifiedExtension K Ω f →ₐ[𝒪[K]] Kun K Ω :=
    (IntermediateField.inclusion hle).restrictScalars 𝒪[K]
  have hι : Function.Injective ι := IntermediateField.inclusion_injective hle
  have hint (a : unramifiedExtension K Ω f) : IsIntegral 𝒪[K] (ι a) ↔ IsIntegral 𝒪[K] a :=
    isIntegral_algHom_iff ι hι
  have hmem (a : unramifiedExtension K Ω f) :
      a ∈ 𝒪[unramifiedExtension K Ω f] ↔ IsIntegral 𝒪[K] a := by
    rw [integerRing_eq_integralClosure K (unramifiedExtension K Ω f)]
    exact Iff.rfl
  refine h _ rfl ?_ ?_ ?_
  · intro x hxf
    exact ⟨⟨⟨toΩ K Ω x, hxf⟩, (hmem _).2 ((hint _).1 x.2)⟩, rfl⟩
  · intro a
    exact ⟨⟨ι a, (hint _).2 ((hmem _).1 a.2)⟩, rfl⟩
  · intro n r y hy
    have hr : (r : Kun K Ω) = ⟨(y : Ω), hle y.2⟩ := Subtype.ext hy
    rw [toΩ_frobRun_pow, hr]
    have := coe_maximalUnramifiedFrobenius_zpow_apply_of_mem (K := K) (Ω := Ω) (f := f)
      (n : ℤ) y.2
    simpa [zpow_natCast] using this

/-- Every nonzero element of `Run` lying in the level `K_f` is a unit times a power of `π`. -/
private theorem exists_unit_mul_pow_of_mem {π : 𝒪[K]} (hπ : Irreducible π) {f : ℕ} (hf : f ≠ 0)
    {x : Run K Ω} (hx : x ≠ 0) (hxf : toΩ K Ω x ∈ unramifiedExtension K Ω f) :
    ∃ (n : ℕ) (v : (Run K Ω)ˣ), x = v * algebraMap 𝒪[K] (Run K Ω) π ^ n := by
  refine withLevel K Ω hf ?_
  intro L hL _ _ _ _ _ _ _ hlift1 lift _
  rw [← hL] at hxf
  obtain ⟨y, hy⟩ := hlift1 x hxf
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hx
    apply toΩ_injective K Ω
    rw [map_zero, ← hy]
    rfl
  have hϖ : Irreducible (algebraMap 𝒪[K] 𝒪[L] π) := IsUnramified.irreducible_algebraMap hπ
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  obtain ⟨r, hr⟩ := lift (u : 𝒪[L])
  obtain ⟨s, hs⟩ := lift ((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L])
  have hrs : r * s = 1 := by
    apply toΩ_injective K Ω
    rw [map_mul, hr, hs, map_one]
    have h2 : (u : 𝒪[L]) * ((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) = 1 := u.mul_inv
    exact congrArg (fun z : 𝒪[L] => ((z : L) : Ω)) h2
  have hsr : s * r = 1 := by rw [mul_comm]; exact hrs
  refine ⟨n, ⟨r, s, hrs, hsr⟩, ?_⟩
  apply toΩ_injective K Ω
  rw [map_mul, map_pow, toΩ_algebraMap]
  have := congrArg (fun z : 𝒪[L] => ((z : L) : Ω)) hu
  rw [hr, ← hy]
  simpa using this

end Aux

theorem exists_unit_mul_pow {π : 𝒪[K]} (hπ : Irreducible π) {x : Run K Ω} (hx : x ≠ 0) :
    ∃ (n : ℕ) (v : (Run K Ω)ˣ), x = v * algebraMap 𝒪[K] (Run K Ω) π ^ n := by
  obtain ⟨f, hf, hxf⟩ := TauCeti.mem_maximalUnramifiedExtension_iff.1 x.1.2
  exact exists_unit_mul_pow_of_mem K Ω hπ hf hx hxf

section Aux2

open TauCeti ValuativeRel

private theorem algebraMap_ne_zero {π : 𝒪[K]} (hπ : Irreducible π) :
    algebraMap 𝒪[K] (Run K Ω) π ≠ 0 := by
  intro h
  apply hπ.ne_zero
  have h2 := congrArg (toΩ K Ω) h
  rw [toΩ_algebraMap, map_zero] at h2
  have : algebraMap 𝒪[K] K π = 0 := (algebraMap K Ω).injective (by simpa using h2)
  exact (IsFractionRing.injective 𝒪[K] K) (by simpa using this)

private theorem not_isUnit_algebraMap {π : 𝒪[K]} (hπ : Irreducible π) :
    ¬ IsUnit (algebraMap 𝒪[K] (Run K Ω) π) := by
  rintro ⟨u, hu⟩
  set s : Run K Ω := ((u⁻¹ : (Run K Ω)ˣ) : Run K Ω) with hs
  have hmul : algebraMap 𝒪[K] (Run K Ω) π * s = 1 := by
    rw [← hu]; exact u.mul_inv
  have hπK : algebraMap 𝒪[K] K π ≠ 0 := by
    intro h
    exact hπ.ne_zero ((IsFractionRing.injective 𝒪[K] K) (by simpa using h))
  set c : K := (algebraMap 𝒪[K] K π)⁻¹ with hc
  have hsc : (s : Kun K Ω) = algebraMap K (Kun K Ω) c := by
    apply Subtype.ext
    have h1 := congrArg (toΩ K Ω) hmul
    rw [map_mul, toΩ_algebraMap, map_one] at h1
    have hπΩ : algebraMap K Ω (algebraMap 𝒪[K] K π) ≠ 0 :=
      (map_ne_zero (algebraMap K Ω)).2 hπK
    change toΩ K Ω s = algebraMap K Ω c
    rw [hc, map_inv₀]
    exact eq_inv_of_mul_eq_one_right h1
  have hint : IsIntegral 𝒪[K] (algebraMap K (Kun K Ω) c) := hsc ▸ s.2
  have hint' : IsIntegral 𝒪[K] c :=
    isIntegral_algebraMap_iff.1 hint
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
  apply hπ.not_isUnit
  refine IsUnit.of_mul_eq_one a ((IsFractionRing.injective 𝒪[K] K) ?_)
  rw [map_mul, ha, hc, map_one, mul_inv_cancel₀ hπK]

/-- A uniformizer of `K` stays irreducible in `Run`. -/
theorem irreducible_algebraMap {π : 𝒪[K]} (hπ : Irreducible π) :
    Irreducible (algebraMap 𝒪[K] (Run K Ω) π) := by
  set p := algebraMap 𝒪[K] (Run K Ω) π with hp
  have hp0 : p ≠ 0 := algebraMap_ne_zero K Ω hπ
  refine ⟨not_isUnit_algebraMap K Ω hπ, fun a b hab ↦ ?_⟩
  have ha0 : a ≠ 0 := by rintro rfl; exact hp0 (by simpa using hab)
  have hb0 : b ≠ 0 := by rintro rfl; exact hp0 (by simpa using hab)
  obtain ⟨n, v, hv⟩ := exists_unit_mul_pow K Ω hπ ha0
  obtain ⟨m, w, hw⟩ := exists_unit_mul_pow K Ω hπ hb0
  rcases n with _ | n'
  · left; rw [hv]; simp
  rcases m with _ | m'
  · right; rw [hw]; simp
  exfalso
  have h : p = (v : Run K Ω) * p ^ (n' + 1) * ((w : Run K Ω) * p ^ (m' + 1)) := by
    rw [← hv, ← hw]; exact hab
  have h2 : p * ((v : Run K Ω) * w * p ^ (n' + m') * p - 1) = 0 := by
    linear_combination (-1 : Run K Ω) * h
  have h3 := (mul_eq_zero.1 h2).resolve_left hp0
  exact not_isUnit_algebraMap K Ω hπ
    (IsUnit.of_mul_eq_one ((v : Run K Ω) * w * p ^ (n' + m')) (by linear_combination h3))

instance : IsDiscreteValuationRing (Run K Ω) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨algebraMap 𝒪[K] (Run K Ω) π, irreducible_algebraMap K Ω hπ, fun {x} hx ↦ ?_⟩
  obtain ⟨n, v, hv⟩ := exists_unit_mul_pow K Ω hπ hx
  exact ⟨n, v, by rw [hv, mul_comm]⟩

theorem maximalIdeal_eq_span {π : 𝒪[K]} (hπ : Irreducible π) :
    IsLocalRing.maximalIdeal (Run K Ω) = Ideal.span {algebraMap 𝒪[K] (Run K Ω) π} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 (irreducible_algebraMap K Ω hπ)

theorem frobRun_algebraMap (a : 𝒪[K]) :
    frobRun K Ω (algebraMap 𝒪[K] (Run K Ω) a) = algebraMap 𝒪[K] (Run K Ω) a := by
  apply toΩ_injective K Ω
  rw [toΩ_algebraMap]
  change (((TauCeti.maximalUnramifiedFrobenius K Ω)
    (algebraMap 𝒪[K] (Kun K Ω) a) : Kun K Ω) : Ω) = _
  rw [IsScalarTower.algebraMap_apply 𝒪[K] K (Kun K Ω), AlgEquiv.commutes]
  rfl

/-- The congruence for an element living in a finite level. -/
private theorem frobRun_sub_pow_mem_of_mem {π : 𝒪[K]} (hπ : Irreducible π) {f : ℕ} (hf : f ≠ 0)
    {r : Run K Ω} (hrf : toΩ K Ω r ∈ unramifiedExtension K Ω f) :
    frobRun K Ω r - r ^ Nat.card 𝓀[K] ∈ Ideal.span {algebraMap 𝒪[K] (Run K Ω) π} := by
  refine withLevel K Ω hf ?_
  intro L hL _ _ _ _ _ _ _ hlift1 hlift2 hfrob
  rw [← hL] at hrf
  obtain ⟨y, hy⟩ := hlift1 r hrf
  have h1 : toΩ K Ω (frobRun K Ω r) =
      ((frobeniusAlgEquiv (K := K) (L := L) (y : L) : L) : Ω) := by
    simpa using hfrob 1 r y hy.symm
  have hv := valuation_frobeniusAlgEquiv_sub_pow (K := K) (L := L) y
  let w : 𝒪[L] := ⟨frobeniusAlgEquiv (K := K) (L := L) (y : L) - (y : L) ^ Nat.card 𝓀[K], hv.le⟩
  have hw : w ∈ 𝓂[L] := (Valuation.mem_maximalIdeal_iff (v := valuation L)).2 hv
  have hmax : 𝓂[L] = Ideal.span {algebraMap 𝒪[K] 𝒪[L] π} := by
    rw [← IsUnramified.map_maximalIdeal (K := K) (L := L),
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.map_span,
      Set.image_singleton]
  rw [hmax, Ideal.mem_span_singleton] at hw
  obtain ⟨t, ht⟩ := hw
  obtain ⟨t', ht'⟩ := hlift2 t
  refine Ideal.mem_span_singleton.2 ⟨t', ?_⟩
  apply toΩ_injective K Ω
  rw [map_sub, map_pow, map_mul, toΩ_algebraMap, ht', h1, ← hy]
  have := congrArg (fun z : 𝒪[L] => ((z : L) : Ω)) ht
  simpa [w] using this

theorem frobRun_sub_pow_mem (r : Run K Ω) :
    frobRun K Ω r - r ^ Nat.card 𝓀[K] ∈ IsLocalRing.maximalIdeal (Run K Ω) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [maximalIdeal_eq_span K Ω hπ]
  obtain ⟨f, hf, hrf⟩ := TauCeti.mem_maximalUnramifiedExtension_iff.1 r.1.2
  exact frobRun_sub_pow_mem_of_mem K Ω hπ hf hrf

end Aux2

section Residue

open TauCeti ValuativeRel IsLocalRing Polynomial

/-- Some power of Frobenius fixes any given element of `Run`, since this holds on each finite
unramified level, where Frobenius has finite order. -/
private theorem exists_frobRun_pow_eq (r : Run K Ω) :
    ∃ d : ℕ, 0 < d ∧ (frobRun K Ω ^ d) r = r := by
  obtain ⟨f, hf, hrf⟩ := mem_maximalUnramifiedExtension_iff.1 r.1.2
  refine withLevel K Ω hf ?_
  intro L hL _ _ _ _ _ _ _ hlift1 _ hfrob
  rw [← hL] at hrf
  obtain ⟨y, hy⟩ := hlift1 r hrf
  refine ⟨orderOf (frobeniusAlgEquiv (K := K) (L := L)), orderOf_pos _, ?_⟩
  apply toΩ_injective K Ω
  rw [hfrob _ r y hy.symm, pow_orderOf_eq_one, AlgEquiv.one_apply]
  exact hy

/-- The `n`-th power of Frobenius acts on residue classes as the `q ^ n`-th power map. -/
private theorem residue_frobRun_pow (n : ℕ) (r : Run K Ω) :
    residue (Run K Ω) ((frobRun K Ω ^ n) r) = residue (Run K Ω) r ^ (Nat.card 𝓀[K] ^ n) := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    change residue (Run K Ω) ((frobRun K Ω ^ n) (frobRun K Ω r)) = _
    have h : residue (Run K Ω) (frobRun K Ω r) = residue (Run K Ω) r ^ Nat.card 𝓀[K] := by
      have := (residue_eq_zero_iff _).2 (frobRun_sub_pow_mem K Ω r)
      rw [map_sub, map_pow, sub_eq_zero] at this
      exact this
    rw [ih, h, ← pow_mul, pow_succ']

/-- Every residue class is fixed by some positive power of the `q`-th power map. -/
private theorem residue_pow_fixed (y : ResidueField (Run K Ω)) :
    ∃ d : ℕ, 0 < d ∧ y ^ (Nat.card 𝓀[K] ^ d) = y := by
  obtain ⟨r, rfl⟩ := residue_surjective y
  obtain ⟨d, hd, hr⟩ := exists_frobRun_pow_eq K Ω r
  refine ⟨d, hd, ?_⟩
  rw [← residue_frobRun_pow, hr]

private theorem isLocalHom_algebraMap : IsLocalHom (algebraMap 𝒪[K] (Run K Ω)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  refine ⟨fun a ha ↦ ?_⟩
  by_contra hna
  have h : a ∈ maximalIdeal 𝒪[K] := (mem_maximalIdeal a).2 hna
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton] at h
  obtain ⟨b, rfl⟩ := h
  rw [map_mul] at ha
  exact not_isUnit_algebraMap K Ω hπ (isUnit_of_mul_isUnit_left ha)

/-- The residue field of `Run` as an algebra over the residue field of `K`. -/
@[instance_reducible]
private def residueAlgebra : Algebra 𝓀[K] (ResidueField (Run K Ω)) :=
  haveI := isLocalHom_algebraMap K Ω
  (ResidueField.map (algebraMap 𝒪[K] (Run K Ω))).toAlgebra

/-- The residue field of `Run` contains a primitive root of unity of order `q ^ m - 1`. -/
private theorem exists_isPrimitiveRoot_residue {m : ℕ} (hm : m ≠ 0) :
    ∃ z : ResidueField (Run K Ω), IsPrimitiveRoot z (Nat.card 𝓀[K] ^ m - 1) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_natCard_pow_sub_one (K := K) Ω hm
  have hq : 1 < Nat.card 𝓀[K] ^ m := Nat.one_lt_pow hm Finite.one_lt_card
  have hunit := isUnit_natCast_natCard_pow_sub_one K hm
  have hζK : ζ ∈ Kun K Ω := mem_maximalUnramifiedExtension_of_pow_eq_one (K := K)
    (IsLocalRing.isUnit_natCast_iff_not_dvd.1 hunit) hζ.pow_eq_one
  have hint : IsIntegral 𝒪[K] (⟨ζ, hζK⟩ : Kun K Ω) := by
    refine IsIntegral.of_pow (n := Nat.card 𝓀[K] ^ m - 1) (by omega) ?_
    have : (⟨ζ, hζK⟩ : Kun K Ω) ^ (Nat.card 𝓀[K] ^ m - 1) = 1 := Subtype.ext hζ.pow_eq_one
    rw [this]
    exact isIntegral_one
  let μ : Run K Ω := ⟨⟨ζ, hζK⟩, hint⟩
  have hμ : IsPrimitiveRoot μ (Nat.card 𝓀[K] ^ m - 1) :=
    IsPrimitiveRoot.of_map_of_injective (f := toΩ K Ω) hζ (toΩ_injective K Ω)
  obtain ⟨n, hn⟩ : ∃ n, Nat.card 𝓀[K] ^ m - 1 = n + 1 := ⟨Nat.card 𝓀[K] ^ m - 2, by omega⟩
  rw [hn] at hμ hunit
  have hprod := hμ.prod_one_sub_pow_eq_order
  have hU : IsUnit ((n : Run K Ω) + 1) := by
    have := hunit.map (algebraMap 𝒪[K] (Run K Ω))
    simpa [map_natCast] using this
  have key : ∀ l : ℕ, 0 < l → l < n + 1 → IsUnit (1 - μ ^ l) := by
    intro l hl hln
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun k ↦ 1 - μ ^ (k + 1))
      (Finset.mem_range.2 (by omega))) (hprod ▸ hU)
  refine ⟨residue (Run K Ω) μ, ?_⟩
  rw [hn]
  refine IsPrimitiveRoot.mk_of_lt _ (by omega) ?_ ?_
  · rw [← map_pow, hμ.pow_eq_one, map_one]
  · intro l hl hln h
    have h0 : residue (Run K Ω) (1 - μ ^ l) = 0 := by
      rw [map_sub, map_one, map_pow, h, sub_self]
    exact (residue_ne_zero_iff_isUnit _ |>.2 (key l hl hln)) h0

/-- A field algebraic over a finite field `F`, containing a primitive root of unity of order
`|F| ^ m - 1` for every `m ≥ 1`, is algebraically closed. -/
private theorem isAlgClosed_of_primitiveRoots (F k : Type) [Field F] [Finite F] [Field k]
    [Algebra F k] [Algebra.IsAlgebraic F k]
    (hprim : ∀ m : ℕ, m ≠ 0 → ∃ z : k, IsPrimitiveRoot z (Nat.card F ^ m - 1)) :
    IsAlgClosed k := by
  refine IsAlgClosed.of_exists_root _ fun p _ hirr ↦ ?_
  haveI := Fact.mk hirr
  haveI : Module.Finite k (AdjoinRoot p) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  haveI : Algebra.IsAlgebraic k (AdjoinRoot p) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic F (AdjoinRoot p) := Algebra.IsAlgebraic.trans F k _
  have hαint : IsIntegral F (AdjoinRoot.root p) :=
    (Algebra.IsAlgebraic.isAlgebraic (AdjoinRoot.root p)).isIntegral
  haveI := IntermediateField.adjoin.finiteDimensional hαint
  haveI : Finite (IntermediateField.adjoin F {AdjoinRoot.root p}) := Module.finite_of_finite F
  letI := Fintype.ofFinite (IntermediateField.adjoin F {AdjoinRoot.root p})
  letI := Fintype.ofFinite F
  have hcard := Module.card_eq_pow_finrank (K := F) (V := IntermediateField.adjoin F {AdjoinRoot.root p})
  have hpow := FiniteField.pow_card (IntermediateField.AdjoinSimple.gen F (AdjoinRoot.root p))
  set m := Module.finrank F (IntermediateField.adjoin F {AdjoinRoot.root p}) with hmdef
  have hm : m ≠ 0 := Module.finrank_pos.ne'
  have hα : AdjoinRoot.root p ^ (Nat.card F ^ m) = AdjoinRoot.root p := by
    have := congrArg Subtype.val hpow
    rw [hcard, ← Nat.card_eq_fintype_card] at this
    exact this
  have hq : 1 < Nat.card F ^ m := Nat.one_lt_pow hm Finite.one_lt_card
  obtain ⟨z, hz⟩ := hprim m hm
  have hzE : IsPrimitiveRoot (algebraMap k (AdjoinRoot p) z) (Nat.card F ^ m - 1) :=
    hz.map_of_injective (algebraMap k (AdjoinRoot p)).injective
  haveI : NeZero (Nat.card F ^ m - 1) := ⟨by omega⟩
  have hroot : ∃ c : k, AdjoinRoot.root p = algebraMap k (AdjoinRoot p) c := by
    by_cases h0 : AdjoinRoot.root p = 0
    · exact ⟨0, by rw [h0, map_zero]⟩
    · have h1 : AdjoinRoot.root p ^ (Nat.card F ^ m - 1) = 1 := by
        apply mul_right_cancel₀ h0
        rw [← pow_succ, one_mul, Nat.sub_add_cancel hq.le]
        exact hα
      obtain ⟨i, -, hi⟩ := hzE.eq_pow_of_pow_eq_one h1
      exact ⟨z ^ i, by rw [map_pow, hi]⟩
  obtain ⟨c, hc⟩ := hroot
  refine ⟨c, ?_⟩
  have h0 := AdjoinRoot.eval₂_root p
  rw [hc, ← AdjoinRoot.algebraMap_eq, eval₂_at_apply, AdjoinRoot.algebraMap_eq] at h0
  exact (AdjoinRoot.of p).injective (by simpa using h0)

theorem residue_isAlgClosed : IsAlgClosed (IsLocalRing.ResidueField (Run K Ω)) := by
  letI : Algebra 𝓀[K] (ResidueField (Run K Ω)) := residueAlgebra K Ω
  have hq : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  haveI halg : Algebra.IsAlgebraic 𝓀[K] (ResidueField (Run K Ω)) := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨d, hd, hy⟩ := residue_pow_fixed K Ω y
    refine ⟨(X ^ (Nat.card 𝓀[K] ^ d) - X : 𝓀[K][X]),
      FiniteField.X_pow_card_sub_X_ne_zero _ (Nat.one_lt_pow hd.ne' hq), ?_⟩
    simp [hy]
  exact isAlgClosed_of_primitiveRoots 𝓀[K] (ResidueField (Run K Ω))
    fun m hm ↦ exists_isPrimitiveRoot_residue K Ω hm

end Residue

end NumberFieldKB.MilneCFT.CompletedUnramified
