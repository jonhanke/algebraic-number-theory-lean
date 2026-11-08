import NumberFieldKB.WeilBNT.FieldClassificationB
import NumberFieldKB.WeilBNT.PFieldStructure
import NumberFieldKB.WeilBNT.Frobenius
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.Convex.PathConnected

/-!
# Weil, *Basic Number Theory*, I.§3, Def. 2 and text p. 12: $\mathbb R$-fields

$K$ is a nondiscrete locally compact division ring (`FieldModule`). Weil (Def. 2) calls $K$ an *$\mathbb R$-field* if
it is an algebra over $\mathbb R$; here (`IsRField`): there is a continuous ring homomorphism
$f:\mathbb R\to K$ with central image (by Thm. 5 (b) this is the case (b) of Thm. 5 with $v=\infty$).

* **`weil_I_3_text_p12_connected`**: $K$ is connected if and only if it is an $\mathbb R$-field.
* **`weil_I_3_text_p12_classification`**: an $\mathbb R$-field is isomorphic, as a topological ring, to
  $\mathbb R$, $\mathbb C$ or the quaternions $\mathbb H$ (Frobenius' theorem, `frobenius_real_divisionAlgebra`, which
  Weil defers to Chap. IX-4).

*Proof.* A $p$-field is not connected: its maximal compact subring $R$ is open and compact, hence closed, and is not
all of $K$ ($x^{-1}\notin R$ for $x\ne0$ in $P$). By Thm. 5 every $K$ is a $p$-field (characteristic $p$, or
characteristic $0$ with $\mathbb Q_p\subset K$, where $\operatorname{mod}_K(p)=p^{-\delta}<1$) or an $\mathbb R$-field.
An $\mathbb R$-field is a real topological vector space, hence connected; it has finite dimension over $\mathbb R$
(Thm. 5 (b)), so Frobenius' theorem applies, and algebra isomorphisms between finite-dimensional real topological
vector spaces are homeomorphisms.
-/

open Topology

noncomputable section

namespace NumberFieldKB.WeilBNT.FieldModule

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K] [(𝓝[≠] (0 : K)).NeBot]

variable (K) in
/-- **Def. 2** ($\mathbb R$-fields): $K$ is an algebra over $\mathbb R$, i.e. there is a continuous ring homomorphism
$\mathbb R\to K$ with central image. -/
def IsRField : Prop := ∃ f : ℝ →+* K, Continuous f ∧ ∀ x y, f x * y = y * f x

/-- A $p$-field is not connected. -/
theorem not_connectedSpace_of_isPField {p : ℕ} (hK : IsPField K p) : ¬ ConnectedSpace K := by
  intro hc
  have hRo : IsOpen (pR hK : Set K) := (weil_I_4_thm6_isOpen hK).1
  have hRc : IsClosed (pR hK : Set K) := (weil_I_4_thm6_isCompact hK).isClosed
  have hPo : IsOpen (pP hK) := (weil_I_4_thm6_isOpen hK).2
  have h0 : (0 : K) ∈ pP hK := by
    show modK K 0 < 1
    simp
  obtain ⟨y, hyP, hy0⟩ : ∃ y ∈ pP hK, y ≠ 0 := by
    have hmem : pP hK ∈ 𝓝[≠] (0 : K) := mem_nhdsWithin_of_mem_nhds (hPo.mem_nhds h0)
    obtain ⟨y, hy⟩ := Filter.nonempty_of_mem (Filter.inter_mem hmem self_mem_nhdsWithin)
    exact ⟨y, hy.1, hy.2⟩
  have hU : (pR hK : Set K) = Set.univ :=
    (isClopen_iff.mp ⟨hRc, hRo⟩).resolve_left (Set.nonempty_iff_ne_empty.mp ⟨0, (pR hK).zero_mem⟩)
  have hyinv : y⁻¹ ∈ (pR hK : Set K) := by rw [hU]; trivial
  have h1 : modK K y⁻¹ ≤ 1 := hyinv
  rw [modK_inv hy0] at h1
  have hpos : 0 < modK K y := modK_pos_iff.2 hy0
  have hlt : modK K y < 1 := hyP
  have : (1 : NNReal) < (modK K y)⁻¹ := (one_lt_inv₀ hpos).2 hlt
  exact absurd h1 (not_le.2 this)

/-- An $\mathbb R$-field, with the algebra structure given by $f$, is a finite-dimensional real topological vector
space. -/
theorem finiteDimensional_of_isRField (f : ℝ →+* K) (hf : Continuous f) (hc : ∀ x y, f x * y = y * f x) :
    letI : Algebra ℝ K := f.toAlgebra' hc
    ContinuousSMul ℝ K ∧ FiniteDimensional ℝ K := by
  letI : Algebra ℝ K := f.toAlgebra' hc
  have hsmul : ∀ (c : ℝ) (x : K), c • x = f c * x := fun c x => Algebra.smul_def c x
  haveI : ContinuousSMul ℝ K :=
    ⟨by simp_rw [hsmul]; exact (hf.comp continuous_fst).mul continuous_snd⟩
  exact ⟨inferInstance, weil_I_2_thm3_cor2_finiteDimensional (K := ℝ) (V := K)⟩

/-- **Text p. 12.** $K$ is connected if and only if it is an $\mathbb R$-field. -/
@[kb "weil1973bnt" "Ch. I, §3, text p. 12 (an R-field is the same as a connected locally compact field)"]
theorem weil_I_3_text_p12_connected : ConnectedSpace K ↔ IsRField K := by
  constructor
  · intro hc
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
    · exfalso
      have hK : IsPField K (ringChar K) := by
        refine ⟨hp, ?_⟩
        have : ((ringChar K : ℕ) : K) = 0 := by simp
        rw [this, modK_zero]
        exact zero_lt_one
      exact not_connectedSpace_of_isPField hK hc
    · haveI : CharZero K := (CharP.ringChar_zero_iff_CharZero K).1 h0
      rcases weil_I_3_thm5_b (K := K) with ⟨p, hp, f, δ, b, -, -, hb, hmod⟩ | ⟨f, δ, b, hfc, hcomm, -, -⟩
      · exfalso
        have hδ : δ ≠ 0 := by
          rintro rfl
          obtain ⟨c, hc1⟩ := hb.2 1
          have : (1 : K) = 0 := by rw [← hc1]; simp
          exact one_ne_zero this
        have hK : IsPField K p := by
          refine ⟨hp.out, ?_⟩
          have h1 := hmod (p : ℚ_[p])
          rw [map_natCast] at h1
          have hnorm : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
          have hlt : ‖(p : ℚ_[p])‖ ^ δ < 1 := pow_lt_one₀ (norm_nonneg _) hnorm hδ
          rw [← h1] at hlt
          exact_mod_cast hlt
        exact not_connectedSpace_of_isPField hK hc
      · exact ⟨f, hfc, hcomm⟩
  · rintro ⟨f, hf, hc⟩
    letI : Algebra ℝ K := f.toAlgebra' hc
    obtain ⟨hcs, -⟩ := finiteDimensional_of_isRField f hf hc
    haveI := hcs
    have hpc : IsPreconnected (Set.univ : Set K) := convex_univ.isPreconnected
    exact { toPreconnectedSpace := ⟨hpc⟩, toNonempty := ⟨0⟩ }

/-- **Text p. 12.** An $\mathbb R$-field is isomorphic as a topological ring to $\mathbb R$, $\mathbb C$ or the
quaternions $\mathbb H$. -/
@[kb "weil1973bnt" "Ch. I, §3, text p. 12 (the R-fields are R, C and H)"]
theorem weil_I_3_text_p12_classification (h : IsRField K) :
    (∃ e : K ≃+* ℝ, Continuous e ∧ Continuous e.symm) ∨
    (∃ e : K ≃+* ℂ, Continuous e ∧ Continuous e.symm) ∨
    (∃ e : K ≃+* Quaternion ℝ, Continuous e ∧ Continuous e.symm) := by
  obtain ⟨f, hf, hc⟩ := h
  letI : Algebra ℝ K := f.toAlgebra' hc
  obtain ⟨hcs, hfd⟩ := finiteDimensional_of_isRField f hf hc
  haveI := hcs
  haveI := hfd
  rcases Frobenius.frobenius_real_divisionAlgebra K with h | h | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨e.toRingEquiv, LinearMap.continuous_of_finiteDimensional e.toLinearMap,
      LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap⟩
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inl ⟨e.toRingEquiv, LinearMap.continuous_of_finiteDimensional e.toLinearMap,
      LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap⟩)
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inr ⟨e.toRingEquiv, LinearMap.continuous_of_finiteDimensional e.toLinearMap,
      LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap⟩)

end NumberFieldKB.WeilBNT.FieldModule
