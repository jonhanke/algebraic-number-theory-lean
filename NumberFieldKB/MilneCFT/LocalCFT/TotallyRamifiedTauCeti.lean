import NumberFieldKB.MilneCFT.LocalCFT.Complements
import NumberFieldKB.MilneCFT.LocalCFT.UnramifiedTauCeti
import NumberFieldKB.TauCetiPort.RingTheory.Norm.Units
import NumberFieldKB.MilneCFT.LubinTate.HerbrandTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.Norm.Basic
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.InertiaDegree

/-!
# Exercise 1.16 of Milne, *Class Field Theory*, Chapter I, proved from Tau Ceti

A finite extension $L/K$ of nonarchimedean local fields is totally ramified iff $\mathrm{Nm}(L^\times)$ contains a
prime element of $K$ (the named statement `TotallyRamifiedNormInput`).

Our `IsTotallyRamifiedExt L` ($\mathfrak m_K\mathcal O_L = \mathfrak P^{[L:K]}$ for a maximal ideal $\mathfrak P$ of
$\mathcal O_L$) is Tau Ceti's $e(L/K) = [L:K]$ (`isTotallyRamifiedExt_iff`), for the local-field structure on $L$
installed by Tau Ceti (`TauCeti.finiteIntermediateFieldValuativeRel`; any such structure works). Then the exercise is
Tau Ceti's norm formula $v_K(\mathrm{Nm}\,x) = f(L/K)\,v_L(x)$ (`TauCeti.normalizedValuation_norm`) with
$e f = [L:K]$ (`TauCeti.ramificationIndex_mul_inertiaDegree`); all ported under `NumberFieldKB/TauCetiPort/`
(Apache 2.0).
-/

open scoped ValuativeRel

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section LocalStructure

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [ValuativeRel L] [TopologicalSpace L]
  [ValuativeExtension K L] [IsNonarchimedeanLocalField L]

/-- $\mathfrak m_K\mathcal O_L$ is the image of $\mathfrak m_L^{e}$ under $\mathcal O_L \cong$ `integers L`. -/
theorem map_maximalIdeal_integers_eq :
    (𝓂[K]).map (algebraMap 𝒪[K] (integers L)) =
      (𝓂[L] ^ TauCeti.ramificationIndex K L).map
        ((TauCeti.integerRingEquivIntegralClosure K L : 𝒪[L] →+* integers L)) := by
  rw [← TauCeti.map_maximalIdeal_eq_maximalIdeal_pow]
  exact (map_maximalIdeal_integerRingEquiv (K := K) (Ω := Ω) L).symm

/-- **Our total ramification is Tau Ceti's** $e(L/K) = [L:K]$. -/
theorem isTotallyRamifiedExt_iff :
    IsTotallyRamifiedExt L ↔ TauCeti.ramificationIndex K L = Module.finrank K L := by
  set f : 𝒪[L] →+* integers L := (TauCeti.integerRingEquivIntegralClosure K L : 𝒪[L] →+* integers L)
    with hf
  have hfb : Function.Bijective f := (TauCeti.integerRingEquivIntegralClosure K L).bijective
  have hmap := map_maximalIdeal_integers_eq (K := K) (Ω := Ω) L
  have hm0 : 𝓂[L] ≠ ⊥ := IsDiscreteValuationRing.not_a_field 𝒪[L]
  have hm1 : 𝓂[L] ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal 𝒪[L]).ne_top
  have hinj := (Ideal.pow_right_strictAnti (𝓂[L]) hm0 hm1).injective
  constructor
  · rintro ⟨P, hP, hPe⟩
    have hPc : P.comap f = 𝓂[L] :=
      IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ hfb.2)
    have hP' : P = (𝓂[L]).map f := by
      rw [← hPc, Ideal.map_comap_of_surjective _ hfb.2]
    have h2 : (𝓂[L] ^ TauCeti.ramificationIndex K L).map f = (𝓂[L] ^ Module.finrank K L).map f := by
      rw [← hmap, hPe, hP', Ideal.map_pow]
    have h3 := congrArg (Ideal.comap f) h2
    rw [Ideal.comap_map_of_bijective _ hfb, Ideal.comap_map_of_bijective _ hfb] at h3
    exact hinj h3
  · intro he
    refine ⟨(𝓂[L]).map f, (Ideal.map_eq_top_or_isMaximal_of_surjective f hfb.2
      (IsLocalRing.maximalIdeal.isMaximal _)).resolve_left fun h => hm1 ?_, ?_⟩
    · rw [← Ideal.comap_map_of_bijective _ hfb (I := 𝓂[L]), h, Ideal.comap_top]
    rw [hmap, he, Ideal.map_pow]

/-- Total ramification in Tau Ceti's terms: $f(L/K) = 1$. -/
theorem isTotallyRamifiedExt_iff_inertiaDegree :
    IsTotallyRamifiedExt L ↔ TauCeti.inertiaDegree K L = 1 := by
  rw [isTotallyRamifiedExt_iff, ← TauCeti.ramificationIndex_mul_inertiaDegree (K := K) (L := L)]
  have hpos := TauCeti.ramificationIndex_pos (K := K) (L := L)
  constructor
  · intro h
    have : TauCeti.ramificationIndex K L * 1 =
        TauCeti.ramificationIndex K L * TauCeti.inertiaDegree K L := by rw [mul_one]; exact h
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  · intro h
    rw [h, mul_one]

end LocalStructure

variable (K Ω) in
/-- **Exercise 1.16, proved** (Milne, *CFT*, I, Exercise 1.16): the named statement `TotallyRamifiedNormInput` holds.
If $L/K$ is totally ramified ($f(L/K) = 1$) the norm of a prime element of $L$ is a prime element of $K$
(`TauCeti.isUniformizer_normUnits_iff`); conversely if $\pi = \mathrm{Nm}(x)$ then
$1 = v_K(\pi) = f(L/K)\,v_L(x)$, so $f(L/K) = 1$ (`TauCeti.toAdd_normalizedValuation_norm`). -/
@[kb "milne2020cft" "Ch. I, Exercise 1.16"]
theorem totallyRamifiedNormInput : TotallyRamifiedNormInput K Ω := by
  refine ⟨fun L _ => ?_⟩
  let _ : ValuativeRel L := TauCeti.finiteIntermediateFieldValuativeRel K Ω L
  let _ : TopologicalSpace L := TauCeti.finiteIntermediateFieldTopology K Ω L
  have : ValuativeExtension K L := TauCeti.finiteIntermediateField_valuativeExtension K Ω L
  have : IsNonarchimedeanLocalField L := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω L
  rw [isTotallyRamifiedExt_iff_inertiaDegree]
  constructor
  · intro hf
    obtain ⟨ϖ, hϖ⟩ := TauCeti.exists_isUniformizer (K := L)
    have hN := (TauCeti.isUniformizer_normUnits_iff (K := K) hϖ).2 hf
    obtain ⟨π, hπ, hπeq⟩ := (TauCeti.isUniformizer_iff_exists_irreducible K _).1 hN
    refine ⟨π, hπ, ϖ, ?_⟩
    apply Units.ext
    show Algebra.norm K (ϖ : L) = (π : K)
    rw [hπeq]
    rfl
  · rintro ⟨π, hπ, x, hx⟩
    have hxN : TauCeti.Algebra.normUnits K x = primeUnit hπ := Units.ext (congrArg Units.val hx)
    have hu : TauCeti.IsUniformizer (K := K) (primeUnit hπ) :=
      (TauCeti.isUniformizer_iff_exists_irreducible K _).2 ⟨π, hπ, rfl⟩
    have h1 := TauCeti.toAdd_normalizedValuation_norm (K := K) (L := L) x
    rw [hxN, (TauCeti.isUniformizer_def _).1 hu, toAdd_ofAdd] at h1
    have h2 : ((TauCeti.inertiaDegree K L : ℤ)) ∣ 1 := ⟨_, h1⟩
    have h3 := Int.eq_one_of_dvd_one (by positivity) h2
    exact_mod_cast h3

end NumberFieldKB.MilneCFT.LocalCFT
