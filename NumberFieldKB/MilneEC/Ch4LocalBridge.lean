import NumberFieldKB.MilneEC.Ch4Local
import NumberFieldKB.MilneANT.Ch7Example754

/-!
# Milne, *Elliptic Curves*, Chapter IV, Lemma 3.3 and Remark 3.4, from Milne's *Algebraic Number Theory*

Source: J. S. Milne, *Elliptic Curves*, second edition (course notes `ectext6`, 2006), bib key `milne2006ec`,
Chapter IV, Lemma 3.3 and Remark 3.4, pdf p. 119. Milne proves neither: he cites his *Algebraic Number Theory*
(bib key `milne2020ant`), where the statements are Remark 7.53 (every finite separable extension of the residue field
lifts to a finite unramified extension) and Example 7.54 (the unramified extension of degree $n$ is the splitting field
of $X^{q^n} - X$). Both are proved in this library for a complete discrete valuation ring $A$ with fraction field $K$
(`MilneANT.remark_7_53`, `MilneANT.example_7_54`). Here they are specialised to $A = \mathbb Z_p$, $K = \mathbb Q_p$.

The bridge between the two definitions of "unramified":
* Elliptic Curves, p. 119 (`IsUnramifiedOverQp`): every maximal ideal of $\mathcal O_K$ is $p\mathcal O_K$;
* Algebraic Number Theory, p. 124 (`MilneANT.IsUnramifiedMilne`): the residue degree $f$ equals $[K : \mathbb Q_p]$.

They agree (`isUnramifiedOverQp_iff`) by $ef = n$ (`MilneANT.cor_7_42`) and $p\mathcal O_K = \mathfrak p_K^e$ in the
discrete valuation ring $\mathcal O_K$ (`MilneANT.Remark753.map_maximalIdeal_eq_pow`).
-/

open IsLocalRing Polynomial NumberFieldKB.MilneANT

namespace NumberFieldKB.MilneEC

variable (p : ℕ) [Fact p.Prime]

section Bridge

variable (K : Type) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]

omit [Algebra ℚ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K] in
/-- $p\mathcal O_K$ is the extension of the maximal ideal of $\mathbb Z_p$. -/
lemma span_p_eq_map :
    Ideal.span {(p : integralClosure ℤ_[p] K)} =
      Ideal.map (algebraMap ℤ_[p] (integralClosure ℤ_[p] K)) (maximalIdeal ℤ_[p]) := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]

/-- Unramified in the sense of Elliptic Curves (maximal ideal $= p\mathcal O_K$) implies unramified in the sense of
Algebraic Number Theory ($f = n$). -/
theorem isUnramifiedMilne_of_isUnramifiedOverQp (h : IsUnramifiedOverQp p K) :
    IsUnramifiedMilne ℤ_[p] ℚ_[p] K := by
  have : Module.Finite ℤ_[p] (integralClosure ℤ_[p] K) :=
    IsIntegralClosure.finite ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K)
  have := Remark753.isDVR_of_finite ℤ_[p] ℚ_[p] K
  have := Remark753.torsionFree_integralClosure ℤ_[p] ℚ_[p] K
  have := isLocalHom_algebraMap_integralClosure ℤ_[p] K
  have hpow := Remark753.map_maximalIdeal_eq_pow (A := ℤ_[p]) (B := integralClosure ℤ_[p] K)
  have hP := h (maximalIdeal _) inferInstance
  rw [span_p_eq_map, hpow] at hP
  have hP0 : maximalIdeal (integralClosure ℤ_[p] K) ≠ ⊥ := fun h0 =>
    IsDiscreteValuationRing.not_isField _ (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h0)
  have he : ramIdxMilne ℤ_[p] K = 1 := by
    show (maximalIdeal (integralClosure ℤ_[p] K)).ramificationIdx ℤ_[p] = 1
    generalize (maximalIdeal (integralClosure ℤ_[p] K)).ramificationIdx ℤ_[p] = e at hP
    rcases e with _ | _ | e
    · rw [pow_zero, Ideal.one_eq_top] at hP
      exact absurd hP (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    · rfl
    · have hlt := Ideal.pow_succ_lt_pow hP0 1
      have hle : maximalIdeal (integralClosure ℤ_[p] K) ^ (e + 1 + 1) ≤
          maximalIdeal (integralClosure ℤ_[p] K) ^ (1 + 1) := Ideal.pow_le_pow_right (by omega)
      rw [← hP] at hle
      rw [pow_one] at hlt
      exact absurd hle (not_le_of_gt hlt)
  have hef := cor_7_42 ℤ_[p] ℚ_[p] K
  rw [he, one_mul] at hef
  exact hef

/-- Unramified in the sense of Algebraic Number Theory implies unramified in the sense of Elliptic Curves. -/
theorem isUnramifiedOverQp_of_isUnramifiedMilne (h : IsUnramifiedMilne ℤ_[p] ℚ_[p] K) :
    IsUnramifiedOverQp p K := by
  intro P hP
  rw [IsLocalRing.eq_maximalIdeal hP, span_p_eq_map, Remark753.map_maximalIdeal_eq ℤ_[p] ℚ_[p] K h]

/-- The two definitions of an unramified extension of $\mathbb Q_p$ agree (Elliptic Curves p. 119; Algebraic Number
Theory p. 124). -/
theorem isUnramifiedOverQp_iff : IsUnramifiedOverQp p K ↔ IsUnramifiedMilne ℤ_[p] ℚ_[p] K :=
  ⟨isUnramifiedMilne_of_isUnramifiedOverQp p K, isUnramifiedOverQp_of_isUnramifiedMilne p K⟩

/-- For $K$ unramified, $\mathcal O_K / p\mathcal O_K$ is the residue field of $\mathcal O_K$. -/
noncomputable def quotSpanPEquiv (h : IsUnramifiedOverQp p K) :
    (integralClosure ℤ_[p] K) ⧸ Ideal.span {(p : integralClosure ℤ_[p] K)} ≃+*
      ResidueField (integralClosure ℤ_[p] K) :=
  Ideal.quotEquivOfEq (h _ (IsLocalRing.maximalIdeal.isMaximal _)).symm

instance : Finite (ResidueField ℤ_[p]) := Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv

lemma natCard_residueField_padicInt : Nat.card (ResidueField ℤ_[p]) = p := by
  rw [Nat.card_congr (PadicInt.residueField (p := p)).toEquiv, Nat.card_zmod]

/-- For $K$ unramified of degree $n$, the residue field of $\mathcal O_K$ has $p^n$ elements. -/
lemma natCard_residueField (h : IsUnramifiedMilne ℤ_[p] ℚ_[p] K) :
    Nat.card (ResidueField (integralClosure ℤ_[p] K)) =
      Nat.card (ResidueField ℤ_[p]) ^ Module.finrank ℚ_[p] K := by
  have hres := Example754.finrank_res ℤ_[p] ℚ_[p] K h
  have : Module.Finite (ResidueField ℤ_[p]) (ResidueField (integralClosure ℤ_[p] K)) :=
    Module.finite_of_finrank_pos (hres ▸ Module.finrank_pos)
  rw [Module.natCard_eq_pow_finrank (K := ResidueField ℤ_[p]), hres]

end Bridge

/-- **Lemma 3.3** (pdf p. 119), proved, from Milne's *Algebraic Number Theory*, Remark 7.53 (`remark_7_53`, the lift
of a finite separable extension of the residue field to a finite unramified extension). -/
@[kb "milne2006ec" "Ch. IV, Lemma 3.3, pdf p. 119"]
theorem lemma_3_3 : Lemma3_3 := by
  refine ⟨fun p _ k _ _ _ => ?_⟩
  let _ : Algebra (ResidueField ℤ_[p]) k :=
    ((algebraMap (ZMod p) k).comp (PadicInt.residueField (p := p)).toRingHom).toAlgebra
  have : Module.Finite (ResidueField ℤ_[p]) k := Module.Finite.of_finite
  have : Module.Finite (ZMod p) k := Module.Finite.of_finite
  obtain ⟨K, _, _, _, _, hfin, hK, ⟨e⟩⟩ := (remark_7_53 ℤ_[p] ℚ_[p]).exists_lift k
  have hK' := isUnramifiedOverQp_of_isUnramifiedMilne p K hK
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, hfin, hK', ?_,
    ⟨(quotSpanPEquiv p K hK').trans e.toRingEquiv⟩⟩
  -- degrees: compare cardinalities, `p ^ [K : ℚ_p] = #k = p ^ [k : 𝔽_p]`
  have h1 := natCard_residueField p K hK
  rw [natCard_residueField_padicInt, Nat.card_congr e.toEquiv,
    Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod] at h1
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h1).symm

/-- **Remark 3.4** (pdf p. 119), proved, from Milne's *Algebraic Number Theory*, Example 7.54 (`example_7_54`): an
unramified extension $K$ of $\mathbb Q_p$ whose residue field has $q$ elements is the splitting field of
$X^q - X$. -/
@[kb "milne2006ec" "Ch. IV, Remark 3.4, pdf p. 119"]
theorem remark_3_4 : Remark3_4 := by
  refine ⟨fun p _ K _ _ _ _ _ q hK hq => ?_⟩
  have hK' := isUnramifiedMilne_of_isUnramifiedOverQp p K hK
  have hsplit := (example_7_54 ℤ_[p] ℚ_[p]).isSplittingField K Module.finrank_pos hK'
  rw [← natCard_residueField p K hK', ← Nat.card_congr (quotSpanPEquiv p K hK).toEquiv, hq] at hsplit
  exact hsplit

end NumberFieldKB.MilneEC
