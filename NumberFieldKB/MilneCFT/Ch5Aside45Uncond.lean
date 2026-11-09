import NumberFieldKB.MilneCFT.Ch5Extra
import NumberFieldKB.MilneCFT.Ch8.ChevalleyUncond

/-!
# Milne, *CFT*, V, Aside 4.5: every subgroup of finite index of `U_K` is open

**Proved here:** `aside4_5_finiteIndexOpen : Aside4_5_finiteIndexOpen K` (the "nontrivial theorem" of Aside 4.5,
p. 171), unconditionally.

Proof: Chevalley's congruence theorem with `S = ∅` (`Ch8.Chevalley.chevalleyCongruence`, Milne VIII, Theorem 2.3
step) gives a finite set `P` of primes such that every unit `a ≡ 1` at all `𝔭 ∈ P` lies in `H`. The set `W` of finite
idèles that are units everywhere and `≡ 1` at `P` is open, and its preimage in `K^×` lies in `H`; so `H` is a
neighbourhood of `1` for the induced group topology, hence open.
-/

open NumberField IsDedekindDomain Topology
open scoped Classical WithZero

noncomputable section

namespace NumberFieldKB.MilneCFT

variable (K : Type) [Field K] [NumberField K]

theorem isOpen_valued_sub_one_lt (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen {x : v.adicCompletion K | Valued.v (x - 1) < 1} := by
  have h := Valued.isOpen_ball (v.adicCompletion K)
    (1 : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).ValueGroup₀)
  have e : {x : v.adicCompletion K | Valued.v x < 1} =
      {x | (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict x < 1} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [Valuation.restrict_lt_iff_lt_embedding, map_one]
  rw [← e] at h
  exact h.preimage (continuous_id.sub continuous_const)

theorem unitsK_eq_unit : unitsK K = ((∅ : Set (HeightOneSpectrum (𝓞 K)))).unit K := by
  ext a
  rw [mem_unitsK_iff]
  exact ⟨fun h v _ => h v, fun h v => h v (Set.notMem_empty v)⟩

/-- **Aside 4.5, the nontrivial theorem** (Chevalley): for the topology induced by the finite idèles, every subgroup
of finite index of `U_K` is open. -/
@[kb "milne2020cft" "Ch. V, Aside 4.5, p. 171 (finite index subgroups of U_K are open)"]
theorem aside4_5_finiteIndexOpen : Aside4_5_finiteIndexOpen K := by
  refine ⟨?_⟩
  let _ : TopologicalSpace Kˣ := TopologicalSpace.induced (finiteDiag K) inferInstance
  have : IsTopologicalGroup Kˣ := isTopologicalGroup_induced (finiteDiag K)
  intro H hHU hfin
  have hE : ((∅ : Finset (HeightOneSpectrum (𝓞 K))) : Set (HeightOneSpectrum (𝓞 K))).unit K = unitsK K := by
    rw [Finset.coe_empty, unitsK_eq_unit]
  have hidx : H.relIndex (((∅ : Finset (HeightOneSpectrum (𝓞 K))) : Set (HeightOneSpectrum (𝓞 K))).unit K) ≠ 0 := by
    rw [hE]
    exact hfin.index_ne_zero
  obtain ⟨P, -, hP⟩ := (Ch8.Chevalley.chevalleyCongruence (K := K)).congr ∅ H (hE ▸ hHU) hidx ∅
  let W : Set (FiniteAdeleRing (𝓞 K) K)ˣ :=
    (QuadFormsKB.Tamagawa.Measure.Weil.OHatUnits K : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ∩
      ⋂ v ∈ P, {y | Valued.v ((y : FiniteAdeleRing (𝓞 K) K) v - 1) < 1}
  have hWo : IsOpen W := by
    refine QuadFormsKB.Tamagawa.Measure.Weil.isOpen_OHatUnits.inter
      (isOpen_biInter_finset fun v _ => (isOpen_valued_sub_one_lt K v).preimage ?_)
    have hev : Continuous (fun a : FiniteAdeleRing (𝓞 K) K => a v) := RestrictedProduct.continuous_eval v
    exact hev.comp Units.continuous_val
  have h1W : (1 : (FiniteAdeleRing (𝓞 K) K)ˣ) ∈ W := by
    refine ⟨one_mem _, Set.mem_iInter₂.2 fun v _ => ?_⟩
    simp
  refine Subgroup.isOpen_of_mem_nhds H (g := 1) ?_
  rw [nhds_induced, map_one]
  refine Filter.mem_comap.2 ⟨W, hWo.mem_nhds h1W, fun a ha => ?_⟩
  obtain ⟨ha1, ha2⟩ := ha
  refine hP a (hE ▸ (mem_unitsK_iff_finiteDiag a).2 ha1) fun v hv => ?_
  have h := Set.mem_iInter₂.1 ha2 v hv
  exact h

end NumberFieldKB.MilneCFT
