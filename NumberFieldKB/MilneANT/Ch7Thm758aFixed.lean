import NumberFieldKB.MilneANT.Ch7Thm758b
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Algebraic Number Theory*, Theorem 7.58(a): the fixed field of the inertia group

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`,
Theorem 7.58(a), fixed field, p. 130.

Setting as in `Ch7RamificationFields.lean`; $B$ is the integral closure of $A$ in $L$, $\mathfrak p$ its maximal ideal,
$l = B/\mathfrak p$, $k$ the residue field of $A$, $G_0$ the inertia group, $K_0$ the fixed field of $G_0$.

Milne deduces the statement from Proposition 7.50 and Corollary 7.51. The proof here is direct, and conditional on
the hypothesis `hA` of `theorem7_58aFixedField_of`: every $b \in B$ is congruent modulo $\mathfrak p$ to an element
fixed by $G_0$ (this is where $l/k$ separable is used). Outline.

* *$K_0/K$ is unramified* (`Thm758aFixed.isUnramified_fixedField`). $[L:K_0] = |G_0|$ (Artin) and
  $|G_0| f = n$ (`Thm758aFixed.card_inertia_mul_resDeg`, from `thm_7_58a`), so $[K_0:K] = f$. By `hA` the map
  $B_0/\mathfrak p_0 \to l$ is surjective, hence an isomorphism (it is an injective map of fields), so $K_0$ has
  residue degree $f$ (`Thm758aFixed.resDeg_fixedField`).
* *Maximality* (`Thm758aFixed.le_fixedField_of_unramified`). If $K'$ is unramified over $K$, the residue field $l'$
  is separable over $k$ of degree $[K':K]$; lift a primitive element $\bar\beta$ to $\beta \in B'$. The minimal
  polynomial $g$ of $\beta$ over $A$ reduces to the (separable) minimal polynomial of $\bar\beta$, so
  $K' = K(\beta)$. If $\sigma \in G_0$ had $\sigma\beta \ne \beta$, then $\sigma\beta \equiv \beta \pmod{\mathfrak p}$
  would give a double root of the separable reduction of $g$ in $l$
  (`Thm758aFixed.not_separable_of_two_roots`). Hence $\sigma$ fixes $K'$.
-/

open IsLocalRing

universe u v w

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneANT

namespace Thm758aFixed

/-- `resDegMilne` is the dimension of the residue field extension (copy of a private lemma). -/
lemma resDeg_eq_finrank (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] (E : Type w) [Field E] [Algebra A E] :
    resDegMilne A E = Module.finrank (ResidueField A) (ResidueField (integralClosure A E)) := by
  have hlies : (maximalIdeal (integralClosure A E)).LiesOver (maximalIdeal A) := by
    refine ⟨?_⟩
    ext x
    simp [Ideal.under, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  unfold resDegMilne
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) (maximalIdeal (integralClosure A E))]
  rfl

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]

include K in
/-- `Aut_k(l)` has order `f` (copy). -/
lemma card_aut_residue
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))] :
    Nat.card (ResidueField (integralClosure A L) ≃ₐ[ResidueField A] ResidueField (integralClosure A L)) =
      resDegMilne A L := by
  classical
  let B := integralClosure A L
  let _ : MulSemiringAction (L ≃ₐ[K] L) B :=
    MulSemiringAction.compHom _ (galRestrict A K L B).toMonoidHom
  have hsmul : ∀ (g : L ≃ₐ[K] L) (b : B), g • b = galRestrict A K L B g b := fun _ _ => rfl
  have : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  have : SMulCommClass (L ≃ₐ[K] L) A B :=
    ⟨fun g a b => by rw [hsmul, hsmul, map_smul]⟩
  have : SMulDistribClass (L ≃ₐ[K] L) B L :=
    ⟨fun g b l => by
      rw [Algebra.smul_def, Algebra.smul_def]
      change g (algebraMap B L b * l) = algebraMap B L (galRestrict A K L B g b) * g l
      rw [map_mul]; congr 1; exact (algebraMap_galRestrict_apply A g b).symm⟩
  have : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have : Algebra.IsInvariant A B (L ≃ₐ[K] L) :=
    (IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) A B K L).isInvariant
  have hn : Normal (ResidueField A) (ResidueField B) :=
    Ideal.Quotient.normal (L ≃ₐ[K] L) (maximalIdeal A) (maximalIdeal B)
  have hfin : Module.Finite A B := IsIntegralClosure.finite A K L B
  have : Module.Finite (ResidueField A) (ResidueField B) := inferInstance
  have : IsGalois (ResidueField A) (ResidueField B) := ⟨⟩
  rw [IsGalois.card_aut_eq_finrank, resDeg_eq_finrank]

include K in
/-- `|G_0| * f = n` (copy). -/
lemma card_inertia_mul_resDeg
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))] :
    Nat.card (ramificationGroupMilne A K L 0) * resDegMilne A L = Module.finrank K L := by
  obtain ⟨φ, -, hsurj, hker⟩ := thm_7_58a A K L
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 : Nat.card ((L ≃ₐ[K] L) ⧸ φ.ker) =
      Nat.card (ResidueField (integralClosure A L) ≃ₐ[ResidueField A] ResidueField (integralClosure A L)) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv
  have h3 : Nat.card φ.ker = Nat.card (ramificationGroupMilne A K L 0) := by rw [hker]
  rw [IsGalois.card_aut_eq_finrank] at h1
  rw [h2, h3, card_aut_residue A K L] at h1
  rw [h1, mul_comm]

variable (E : IntermediateField K L)

theorem scalarTower_E : IsScalarTower A E L :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K E]
    rfl)

attribute [local instance] scalarTower_E

/-- The inclusion of the integral closure of `A` in `E` into that in `L`. -/
noncomputable def incl : integralClosure A E →ₐ[A] integralClosure A L :=
  ((IsScalarTower.toAlgHom A E L).comp (integralClosure A E).val).codRestrict (integralClosure A L)
    (fun x => by
      have hx : IsIntegral A (x : E) := x.2
      exact hx.map (IsScalarTower.toAlgHom A E L))

lemma incl_coe (x : integralClosure A E) : ((incl A K L E x : integralClosure A L) : L) = ((x : E) : L) := rfl

instance incl_isLocalHom : IsLocalHom (incl A K L E) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 hx
  have hy' : ((x : E) : L) * (y : L) = 1 := by
    have := congrArg (fun z : integralClosure A L => (z : L)) hy
    simpa [incl_coe] using this
  have hxne : (x : E) ≠ 0 := by
    intro h0
    rw [h0] at hy'
    simp at hy'
  have hcoe : (((x : E)⁻¹ : E) : L) = (y : L) := by
    simp only [IntermediateField.coe_inv]
    exact (eq_inv_of_mul_eq_one_right hy').symm
  have hint : IsIntegral A ((x : E)⁻¹) := by
    have hyi : IsIntegral A (y : L) := y.2
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom A E L) (algebraMap E L).injective).1 ?_
    show IsIntegral A (((x : E)⁻¹ : E) : L)
    rw [hcoe]; exact hyi
  refine isUnit_iff_exists_inv.2 ⟨⟨(x : E)⁻¹, hint⟩, ?_⟩
  apply Subtype.ext
  exact mul_inv_cancel₀ hxne

/-- The residue map of the inclusion is injective. -/
lemma residueMap_injective :
    Function.Injective (ResidueField.mapAlgHom' (incl A K L E)) :=
  (ResidueField.mapAlgHom' (incl A K L E)).toRingHom.injective

include K in
/-- Part 1(b): the residue degree of the fixed field of `G_0` equals that of `L`. -/
lemma resDeg_fixedField
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]
    (hA : ∀ b : integralClosure A L, ∃ a : integralClosure A L,
      (∀ σ ∈ ramificationGroupMilne A K L 0, σ (a : L) = a) ∧
        b - a ∈ maximalIdeal (integralClosure A L)) :
    resDegMilne A (IntermediateField.fixedField (ramificationGroupMilne A K L 0)) = resDegMilne A L := by
  set E := IntermediateField.fixedField (ramificationGroupMilne A K L 0) with hE
  have hsurj : Function.Surjective (ResidueField.mapAlgHom' (incl A K L E)) := by
    intro x
    obtain ⟨b, rfl⟩ := residue_surjective x
    obtain ⟨a, ha, hab⟩ := hA b
    have hmem : (a : L) ∈ E := (IntermediateField.mem_fixedField_iff _ _).2 ha
    have hint : IsIntegral A (⟨(a : L), hmem⟩ : E) := by
      refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom A E L) (algebraMap E L).injective).1 ?_
      exact a.2
    refine ⟨residue _ (⟨⟨(a : L), hmem⟩, hint⟩ : integralClosure A E), ?_⟩
    rw [ResidueField.mapAlgHom'_residue]
    have : incl A K L E ⟨⟨(a : L), hmem⟩, hint⟩ = a := Subtype.ext rfl
    rw [this]
    exact (Ideal.Quotient.eq (I := maximalIdeal (integralClosure A L))).2 (by
      simpa using (Ideal.neg_mem_iff _).2 hab)
  rw [resDeg_eq_finrank, resDeg_eq_finrank]
  exact (LinearEquiv.ofBijective (ResidueField.mapAlgHom' (incl A K L E)).toLinearMap
    ⟨residueMap_injective A K L E, hsurj⟩).finrank_eq

include K in
/-- **Part 1**: the fixed field of `G_0` is unramified over `K`. -/
lemma isUnramified_fixedField
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]
    (hA : ∀ b : integralClosure A L, ∃ a : integralClosure A L,
      (∀ σ ∈ ramificationGroupMilne A K L 0, σ (a : L) = a) ∧
        b - a ∈ maximalIdeal (integralClosure A L)) :
    IsUnramifiedMilne A K (IntermediateField.fixedField (ramificationGroupMilne A K L 0)) := by
  unfold IsUnramifiedMilne
  rw [resDeg_fixedField A K L hA]
  have h1 := card_inertia_mul_resDeg A K L
  have h2 : Module.finrank (IntermediateField.fixedField (ramificationGroupMilne A K L 0)) L =
      Nat.card (ramificationGroupMilne A K L 0) :=
    IntermediateField.finrank_fixedField_eq_card _
  have h3 := Module.finrank_mul_finrank K (IntermediateField.fixedField (ramificationGroupMilne A K L 0)) L
  have hpos : 0 < Nat.card (ramificationGroupMilne A K L 0) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, ← h3, h2, mul_comm]

open Polynomial in
/-- A polynomial with two distinct roots congruent modulo the maximal ideal of a local domain has
non-separable reduction. -/
lemma not_separable_of_two_roots {B : Type*} [CommRing B] [IsDomain B] [IsLocalRing B]
    (G : B[X]) (b b' : B) (hb : G.IsRoot b) (hb' : G.IsRoot b') (hne : b ≠ b')
    (hmax : b' - b ∈ maximalIdeal B) : ¬ (G.map (residue B)).Separable := by
  intro hsep
  have h1 : (X - C b) * (G /ₘ (X - C b)) = G := mul_divByMonic_eq_iff_isRoot.2 hb
  have hq : (G /ₘ (X - C b)).IsRoot b' := by
    have h2 := congrArg (eval b') h1
    rw [eval_mul, eval_sub, eval_X, eval_C] at h2
    have h3 : (b' - b) * eval b' (G /ₘ (X - C b)) = 0 := by rw [h2]; exact hb'
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne.symm)
  have h4 : (X - C b') * ((G /ₘ (X - C b)) /ₘ (X - C b')) = G /ₘ (X - C b) :=
    mul_divByMonic_eq_iff_isRoot.2 hq
  have hres : residue B b' = residue B b := by
    exact (Ideal.Quotient.eq (I := maximalIdeal B)).2 hmax
  have hG : G.map (residue B) = (X - C (residue B b)) * (X - C (residue B b)) *
      ((G /ₘ (X - C b)) /ₘ (X - C b')).map (residue B) := by
    conv_lhs => rw [← h1, ← h4]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hres]
    ring
  have hsq := hsep.squarefree
  have hdvd : (X - C (residue B b)) * (X - C (residue B b)) ∣ G.map (residue B) :=
    ⟨_, hG⟩
  exact not_isUnit_X_sub_C _ (hsq _ hdvd)

include K in
/-- **Part 2**: every unramified subextension is contained in the fixed field of `G_0`. -/
lemma le_fixedField_of_unramified
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]
    (K' : IntermediateField K L) (hK' : IsUnramifiedMilne A K K') :
    K' ≤ IntermediateField.fixedField (ramificationGroupMilne A K L 0) := by
  classical
  have hsepKK' : Algebra.IsSeparable K K' := Algebra.isSeparable_tower_bot_of_isSeparable K K' L
  have hfinB' : Module.Finite A (integralClosure A K') := IsIntegralClosure.finite A K K' _
  have hsep' : Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A K')) :=
    Algebra.IsSeparable.of_algHom (ResidueField A) (ResidueField (integralClosure A L))
      (ResidueField.mapAlgHom' (incl A K L K'))
  obtain ⟨βb, hβb⟩ := Field.exists_primitive_element (ResidueField A) (ResidueField (integralClosure A K'))
  obtain ⟨β, rfl⟩ := residue_surjective βb
  have hn' : Module.finrank (ResidueField A) (ResidueField (integralClosure A K')) =
      Module.finrank K K' := by
    rw [← resDeg_eq_finrank]; exact hK'
  have hint0 : IsIntegral A β.1 := β.2
  have hgm := minpoly.monic hint0
  have hKdeg : (minpoly K β.1).natDegree = (minpoly A β.1).natDegree := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hint0, hgm.natDegree_map]
  have hdegle : (minpoly A β.1).natDegree ≤ Module.finrank K K' := by
    rw [← hKdeg]; exact minpoly.natDegree_le β.1
  have haev0 : Polynomial.aeval β (minpoly A β.1) = 0 := by
    have h := Polynomial.aeval_algHom_apply (integralClosure A K').val β (minpoly A β.1)
    have h' : Polynomial.aeval β.1 (minpoly A β.1) = 0 := minpoly.aeval A β.1
    exact Subtype.ext (h.symm.trans h')
  have hroot : Polynomial.aeval (residue _ β)
      ((minpoly A β.1).map (algebraMap A (ResidueField A))) = 0 := by
    rw [Polynomial.aeval_map_algebraMap (ResidueField A)]
    have h := Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom A (integralClosure A K') (ResidueField (integralClosure A K'))) β
      (minpoly A β.1)
    rw [haev0, map_zero] at h
    exact h
  have hdvd := minpoly.dvd (ResidueField A) (residue _ β) hroot
  have hminpoly_deg : (minpoly (ResidueField A) (residue _ β)).natDegree = Module.finrank K K' := by
    rw [← hn', ← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _), hβb,
      IntermediateField.finrank_top']
  have heq : (minpoly A β.1).map (algebraMap A (ResidueField A)) =
      minpoly (ResidueField A) (residue _ β) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (Algebra.IsIntegral.isIntegral _))
      (hgm.map _) hdvd (by rw [hgm.natDegree_map, hminpoly_deg]; exact hdegle)
  have hgdeg : (minpoly A β.1).natDegree = Module.finrank K K' := by
    have := congrArg Polynomial.natDegree heq
    rw [hgm.natDegree_map, hminpoly_deg] at this
    exact this
  have hsepg : ((minpoly A β.1).map (algebraMap A (ResidueField A))).Separable := by
    rw [heq]; exact Algebra.IsSeparable.isSeparable (ResidueField A) (residue _ β)
  have hadj : IntermediateField.adjoin K {((β.1 : K') : L)} = K' := by
    apply IntermediateField.eq_of_le_of_finrank_eq
    · exact IntermediateField.adjoin_simple_le_iff.2 β.1.2
    · have hmp : minpoly K ((β.1 : K') : L) = minpoly K β.1 :=
        minpoly.algebraMap_eq (algebraMap K' L).injective β.1
      rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _), hmp, hKdeg, hgdeg]
  have hα0 : Polynomial.aeval ((β.1 : K') : L) (minpoly A β.1) = 0 := by
    have h := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom A K' L) β.1 (minpoly A β.1)
    rw [minpoly.aeval, map_zero] at h
    exact h
  have hB : ∀ x : integralClosure A L, Polynomial.aeval (x : L) (minpoly A β.1) = 0 →
      Polynomial.aeval x (minpoly A β.1) = 0 := by
    intro x hx
    have h := Polynomial.aeval_algHom_apply (integralClosure A L).val x (minpoly A β.1)
    exact Subtype.ext (h.symm.trans hx)
  have hfix : ∀ σ ∈ ramificationGroupMilne A K L 0, σ ((β.1 : K') : L) = ((β.1 : K') : L) := by
    intro σ hσ
    by_contra hne
    have hσ' : IsInRamificationGroupMilne A K L 0 σ := hσ
    have hσα : Polynomial.aeval (σ ((β.1 : K') : L)) (minpoly A β.1) = 0 := by
      have h := Polynomial.aeval_algHom_apply (σ.restrictScalars A : L →ₐ[A] L) ((β.1 : K') : L)
        (minpoly A β.1)
      rw [hα0, map_zero] at h
      exact h
    let bα : integralClosure A L := incl A K L K' β
    have hintσ : IsIntegral A (σ ((β.1 : K') : L)) := by
      have : IsIntegral A ((β.1 : K') : L) := bα.2
      exact this.map (σ.restrictScalars A : L →ₐ[A] L)
    let b' : integralClosure A L := ⟨σ ((β.1 : K') : L), hintσ⟩
    have hmem := hσ' bα b' rfl
    rw [zero_add, pow_one] at hmem
    have hbα : Polynomial.aeval bα (minpoly A β.1) = 0 := hB bα hα0
    have hb' : Polynomial.aeval b' (minpoly A β.1) = 0 := hB b' hσα
    have hsep := not_separable_of_two_roots
      ((minpoly A β.1).map (algebraMap A (integralClosure A L))) bα b'
      (by rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap]; exact hbα)
      (by rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap]; exact hb')
      (fun h => hne (congrArg Subtype.val h).symm) hmem
    apply hsep
    rw [Polynomial.map_map]
    have hcomp : (residue (integralClosure A L)).comp (algebraMap A (integralClosure A L)) =
        (algebraMap (ResidueField A) (ResidueField (integralClosure A L))).comp
          (algebraMap A (ResidueField A)) := RingHom.ext fun _ => rfl
    rw [hcomp, ← Polynomial.map_map]
    exact hsepg.map
  rw [← hadj]
  exact IntermediateField.adjoin_simple_le_iff.2 ((IntermediateField.mem_fixedField_iff _ _).2 hfix)

end Thm758aFixed

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]

/-- **Theorem 7.58(a)**, fixed field, conditional on the congruence hypothesis `hA`: every element of
$B$ is congruent modulo $\mathfrak p$ to an element fixed by the inertia group $G_0$ (for $l/k$ separable). Then the
fixed field of $G_0$ is unramified over $K$ and contains every unramified subextension. The maximality part does not
use `hA`. -/
@[kb "milne2020ant" "v3.08, Thm. 7.58, p. 130"]
theorem theorem7_58aFixedField_of
    (hA : ∀ [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]
      (b : integralClosure A L), ∃ a : integralClosure A L,
        (∀ σ ∈ ramificationGroupMilne A K L 0, σ (a : L) = a) ∧
          b - a ∈ maximalIdeal (integralClosure A L)) :
    Theorem7_58aFixedField A K L :=
  ⟨fun {_} => ⟨Thm758aFixed.isUnramified_fixedField A K L (fun b => hA b),
    fun K' hK' => Thm758aFixed.le_fixedField_of_unramified A K L K' hK'⟩⟩

/-- **Theorem 7.58(a)**, fixed field, unconditionally: for $L/K$ Galois with $l/k$ separable, the fixed field of the
inertia group $G_0$ is the largest unramified subextension $K_0$ of $L/K$. Discharges the named statement
`Theorem7_58aFixedField` (the congruence hypothesis is `exists_inertia_fixed_residue`). -/
@[kb "milne2020ant" "v3.08, Thm. 7.58, p. 130"]
theorem theorem7_58aFixedField : Theorem7_58aFixedField A K L :=
  theorem7_58aFixedField_of A K L (fun b => exists_inertia_fixed_residue A K L b)

end NumberFieldKB.MilneANT
