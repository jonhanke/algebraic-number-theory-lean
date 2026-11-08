import NumberFieldKB.WeilBNT.LocalClosures
import NumberFieldKB.WeilBNT.PFieldCompletion

/-!
# Weil, *Basic Number Theory*, III.§1, Corollary of Prop. 1

* `weil_III_1_cor_prop1`: a local field $K$ has finite dimension over the closure $K_0$ of the image of an infinite
  subfield $k_0$ of a field $k$ embedded in $K$ (Prop. 1 and I.§2 Cor. 2 of Thm. 3).
* **`weil_III_1_cor_prop1_adicCompletion`**: the Corollary for a finite place $w$ of a number field $k'$ and a number
  field $k\subseteq k'$: the completion $k'_w$ is a finite extension of the closure $K_0$ of $k$ in $k'_w$, which is a
  local field. (That $K_0$ is the completion of $k$ at the place $v$ below $w$ is not stated here.)
-/

open Topology IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.WeilBNT.FieldModule

/-- **Cor. of Prop. 1**, general form: $K$ is finite-dimensional over the closure $K_0$ of $\lambda(k_0)$. -/
theorem weil_III_1_cor_prop1 {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
    [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot]
    {k : Type*} [Field k] (k₀ : Subfield k) (hinf : (k₀ : Set k).Infinite) (emb : k →+* K) :
    letI : Algebra (k₀.map emb).topologicalClosure K := (Subfield.subtype _).toAlgebra
    FiniteDimensional (k₀.map emb).topologicalClosure K := by
  obtain ⟨-, hlc, hnd⟩ := weil_III_1_prop1_local k₀ hinf emb
  letI : Algebra (k₀.map emb).topologicalClosure K := (Subfield.subtype _).toAlgebra
  have hsm : ∀ (c : (k₀.map emb).topologicalClosure) (x : K), c • x = (c : K) * x := fun _ _ => rfl
  have : ContinuousSMul (k₀.map emb).topologicalClosure K :=
    ⟨by simp_rw [hsm]; exact (continuous_subtype_val.comp continuous_fst).mul continuous_snd⟩
  exact weil_I_2_thm3_cor2_finiteDimensional (K := (k₀.map emb).topologicalClosure) (V := K)

/-- **Cor. of Prop. 1**, finite places of number fields: $k'_w$ is a finite extension of the closure of $k$ in it, and
that closure is a local field. -/
@[kb "weil1973bnt" "Ch. III, §1, Cor. of Prop. 1 (finite places of number fields)"]
theorem weil_III_1_cor_prop1_adicCompletion {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k']
    [Algebra k k'] (w : HeightOneSpectrum (𝓞 k')) :
    let K₀ := ((⊤ : Subfield k).map ((algebraMap k' (w.adicCompletion k')).comp (algebraMap k k'))).topologicalClosure
    LocallyCompactSpace K₀ ∧ (𝓝[≠] (0 : K₀)).NeBot ∧
      letI : Algebra K₀ (w.adicCompletion k') := (Subfield.subtype _).toAlgebra
      FiniteDimensional K₀ (w.adicCompletion k') := by
  intro K₀
  have hinf : ((⊤ : Subfield k) : Set k).Infinite := by
    simpa using Set.infinite_univ (α := k)
  obtain ⟨-, hlc, hnd⟩ := weil_III_1_prop1_local (⊤ : Subfield k) hinf
    ((algebraMap k' (w.adicCompletion k')).comp (algebraMap k k'))
  exact ⟨hlc, hnd, weil_III_1_cor_prop1 (⊤ : Subfield k) hinf _⟩

end NumberFieldKB.WeilBNT.FieldModule
