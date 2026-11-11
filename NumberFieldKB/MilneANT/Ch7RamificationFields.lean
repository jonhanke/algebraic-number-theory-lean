import NumberFieldKB.MilneANT.Ch7Extensions
import NumberFieldKB.MilneANT.Ch7Ramification
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Algebraic Number Theory*, Chapter 7: ramification groups and subfields

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Setting as in `Ch7Extensions.lean` and `Ch7Ramification.lean`.

* **Theorem 7.58(a)**, fixed field (named statement `Theorem7_58aFixedField`): the fixed field of $G_0$ is the largest
  unramified subextension $K_0$ of $L/K$.
* Running text after Corollary 7.59 (p. 131): for Galois $L/K$, $L/K$ is unramified iff $G_0 = 1$
  (`isUnramifiedMilne_iff_inertia_eq_bot`), and tamely ramified iff $G_1 = 1$ (`isTamelyRamifiedMilne_iff`,
  conditional on Theorem 7.58(b)).
* **Proposition 7.64** (named statement `Prop7_64`): finitely many totally ramified extensions of a given degree.
-/

open IsLocalRing

universe u v w

namespace NumberFieldKB.MilneANT

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]

section Galois

variable (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]

/-- **Theorem 7.58(a)**, fixed field (named statement; Milne derives it from Proposition 7.50 and Corollary 7.51):
assume $l/k$ separable. The fixed field of the inertia group $G_0$ is the largest unramified extension $K_0$ of $K$
in $L$: it is unramified over $K$ and contains every unramified subextension. -/
@[kb "milne2020ant" "v3.08, Thm. 7.58, p. 130"]
structure Theorem7_58aFixedField : Prop where
  fixedField : ∀ [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))],
    IsUnramifiedMilne A K (IntermediateField.fixedField (ramificationGroupMilne A K L 0)) ∧
      ∀ K' : IntermediateField K L, IsUnramifiedMilne A K K' →
        K' ≤ IntermediateField.fixedField (ramificationGroupMilne A K L 0)

/-- `resDegMilne` is the dimension of the residue field extension. -/
private lemma resDeg_eq_finrank :
    resDegMilne A L = Module.finrank (ResidueField A) (ResidueField (integralClosure A L)) := by
  have hlies : (maximalIdeal (integralClosure A L)).LiesOver (maximalIdeal A) := by
    refine ⟨?_⟩
    ext x
    simp [Ideal.under, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  unfold resDegMilne
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) (maximalIdeal (integralClosure A L))]
  rfl

include K in
/-- `Aut_k(l)` has order `f` (the residue extension is Galois). -/
private lemma card_aut_residue
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
/-- `|G_0| * f = n`. -/
private lemma card_inertia_mul_resDeg
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

include K in
/-- `|G_0| = e`. -/
private lemma card_inertia_eq_ramIdx
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))] :
    Nat.card (ramificationGroupMilne A K L 0) = ramIdxMilne A L := by
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have h := card_inertia_mul_resDeg A K L
  have h' := cor_7_42 A K L
  have hf : resDegMilne A L ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h; omega
  exact mul_right_cancel₀ hf (h.trans h'.symm)

/-- Descending induction from `G_N = 1` to `G_1 = 1`. -/
private lemma bot_of_step {Γ : Type*} [Group Γ] (G : ℕ → Subgroup Γ) (N : ℕ) (hN : ∀ i ≥ N, G i = ⊥)
    (step : ∀ i, 1 ≤ i → G (i + 1) = ⊥ → G i = ⊥) : G 1 = ⊥ := by
  have hdown : ∀ d i, 1 ≤ i → N ≤ i + d → G i = ⊥ := by
    intro d
    induction d with
    | zero => intro i _ hi; exact hN i (by omega)
    | succ d ih => intro i hi hNi; exact step i hi (ih (i + 1) (by omega) (by omega))
  exact hdown N 1 le_rfl (by omega)

include K in
/-- If `G_{i+1} = 1` then `G_i` embeds in the additive group of `l`. -/
private lemma exists_inj (h : Theorem7_58b A K L)
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))] (i : ℕ) (hi : 1 ≤ i)
    (hb : ramificationGroupMilne A K L (i + 1) = ⊥) :
    ∃ θ : ramificationGroupMilne A K L i →* Multiplicative (ResidueField (integralClosure A L)),
      Function.Injective θ := by
  obtain ⟨θ, hθ⟩ := cor_7_59_additive A K L h i hi
  refine ⟨θ, (injective_iff_map_eq_one θ).2 fun g hg => ?_⟩
  have : g ∈ θ.ker := hg
  rw [hθ, hb, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at this
  exact Subtype.ext this

/-- Powers in `Multiplicative F`. -/
private lemma mult_pow_eq_one {F : Type*} [Field F] (x : Multiplicative F) (n : ℕ) :
    x ^ n = 1 ↔ (n : F) * Multiplicative.toAdd x = 0 := by
  rw [← toAdd_eq_zero, toAdd_pow, nsmul_eq_mul]

/-- **Unramified iff $G_0 = 1$** (Milne p. 131): for $L/K$ Galois with $l/k$ separable, $L/K$ is unramified iff the
inertia group is trivial. -/
@[kb "milne2020ant" "v3.08, Ch. 7, after Cor. 7.59, p. 131"]
theorem isUnramifiedMilne_iff_inertia_eq_bot
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))] :
    IsUnramifiedMilne A K L ↔ ramificationGroupMilne A K L 0 = ⊥ := by
  unfold IsUnramifiedMilne
  have h := card_inertia_mul_resDeg A K L
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  rw [← Subgroup.card_eq_one]
  constructor
  · intro hf
    rw [hf] at h
    exact Nat.eq_of_mul_eq_mul_right hn (h.trans (one_mul _).symm)
  · intro hc
    rw [hc, one_mul] at h
    exact h

/-- **Tamely ramified iff $G_1 = 1$** (Milne p. 131): for $L/K$ Galois with $l/k$ separable, $L/K$ is tamely ramified
($p = \operatorname{char} k$ does not divide $e$) iff $G_1 = 1$. Conditional on Theorem 7.58(b). -/
@[kb "milne2020ant" "v3.08, Ch. 7, after Cor. 7.59, p. 131"]
theorem isTamelyRamifiedMilne_iff (h : Theorem7_58b A K L)
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))] :
    IsTamelyRamifiedMilne A L ↔ ramificationGroupMilne A K L 1 = ⊥ := by
  have hG0 := card_inertia_eq_ramIdx A K L
  have hpos : 0 < Nat.card (ramificationGroupMilne A K L 0) := Nat.card_pos
  unfold IsTamelyRamifiedMilne IsWildlyRamifiedMilne
  rw [← hG0]
  obtain ⟨N, hN⟩ := lemma_7_57_eq_bot A K L
  have hcharP : CharP (ResidueField (integralClosure A L)) (ringChar (ResidueField A)) :=
    charP_of_injective_algebraMap (algebraMap (ResidueField A) (ResidueField (integralClosure A L))).injective _
  generalize ringChar (ResidueField A) = p at hcharP ⊢
  have hp := CharP.char_is_prime_or_zero (ResidueField (integralClosure A L)) p
  rcases hp with hp | hp
  · -- p prime
    have : Fact p.Prime := ⟨hp⟩
    have hcard : ∀ i, Nat.card (ramificationGroupMilne A K L i) ∣
        Nat.card (ramificationGroupMilne A K L 0) := fun i =>
      Subgroup.card_dvd_of_le (ramificationGroupMilne_antitone A K L (Nat.zero_le i))
    constructor
    · intro hndvd
      refine bot_of_step (ramificationGroupMilne A K L) N hN (fun i hi hb => ?_)
      obtain ⟨θ, hθ⟩ := exists_inj A K L h i hi hb
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      set x : ramificationGroupMilne A K L i := ⟨g, hg⟩
      have hpx : θ x ^ p = 1 := by
        rw [mult_pow_eq_one, CharP.cast_eq_zero, zero_mul]
      have hord : orderOf x ∣ p := by
        rw [orderOf_dvd_iff_pow_eq_one]
        exact hθ (by rw [map_pow, hpx, map_one])
      rcases (Nat.dvd_prime hp).1 hord with h1 | h1
      · have := orderOf_eq_one_iff.1 h1
        exact congrArg Subtype.val this
      · exfalso
        apply hndvd
        rw [← h1]
        exact (orderOf_dvd_natCard x).trans (hcard i)
    · intro hb hdvd
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
      obtain ⟨θ, hθ⟩ := cor_7_59_units A K L h
      have hu : θ g ^ p = 1 := by rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
      have hu' : ((θ g : (ResidueField (integralClosure A L))ˣ) : ResidueField (integralClosure A L)) = 1 := by
        have h0 : (((θ g : (ResidueField (integralClosure A L))ˣ) : ResidueField (integralClosure A L)) - 1) ^ p
            = 0 := by
          rw [sub_pow_char, ← Units.val_pow_eq_pow_val, hu]; simp
        have := pow_eq_zero_iff (n := p) hp.ne_zero |>.1 h0
        exact sub_eq_zero.1 this
      have hgk : g ∈ θ.ker := by
        rw [MonoidHom.mem_ker]; exact Units.ext hu'
      rw [hθ, hb, Subgroup.bot_subgroupOf, Subgroup.mem_bot] at hgk
      rw [hgk, orderOf_one] at hg
      exact hp.ne_one hg.symm
  · -- characteristic zero
    subst hp
    have : CharZero (ResidueField (integralClosure A L)) := CharP.charP_to_charZero _
    have h1 : ramificationGroupMilne A K L 1 = ⊥ := by
      refine bot_of_step (ramificationGroupMilne A K L) N hN (fun i hi hb => ?_)
      obtain ⟨θ, hθ⟩ := exists_inj A K L h i hi hb
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      set x : ramificationGroupMilne A K L i := ⟨g, hg⟩
      have hm : Nat.card (ramificationGroupMilne A K L i) ≠ 0 := Nat.card_pos.ne'
      have hpx : θ x ^ Nat.card (ramificationGroupMilne A K L i) = 1 := by
        rw [← map_pow, pow_card_eq_one', map_one]
      rw [mult_pow_eq_one] at hpx
      have := (mul_eq_zero.1 hpx).resolve_left (Nat.cast_ne_zero.2 hm)
      have h2 : θ x = 1 := toAdd_eq_zero.1 this
      exact congrArg Subtype.val (hθ (h2.trans (map_one θ).symm))
    exact ⟨fun _ => h1, fun _ => by rw [zero_dvd_iff]; omega⟩

end Galois

/-- **Proposition 7.64** (named statement). Assume $K$ has characteristic zero and finite residue field. Then, up to
isomorphism, there are only finitely many totally ramified extensions of $K$ of a given degree $n$. Stated inside an
algebraic closure (every finite extension embeds in $K^{\mathrm{al}}$, and each isomorphism class has finitely many
conjugates there): the set of subfields of $K^{\mathrm{al}}$ of degree $n$ that are totally ramified over $K$ is
finite. Milne's proof combines the compactness of the Eisenstein coefficients (Corollary 7.47) with
Proposition 7.63 (`prop_7_63`) and Proposition 7.55 (`prop_7_55`).

*Erratum:* the first version quantified over every `n : ℕ`, including $n = 0$, where
`Module.finrank K E = 0` means $E$ of infinite degree; that version is false (`not_prop764Original`,
`Ch7Prop764Erratum.lean`: the towers $K(\pi^{1/\ell^\infty})$, one for each prime $\ell$, have `ramIdxMilne = 0`).
Milne speaks of extensions of degree $n \ge 1$, which is now the hypothesis `0 < n`. -/
@[kb "milne2020ant" "v3.08, Prop. 7.64, p. 133"]
structure Prop7_64 [CharZero K] [Finite (ResidueField A)] : Prop where
  finite : ∀ n : ℕ, 0 < n →
    {E : IntermediateField K (AlgebraicClosure K) | Module.finrank K E = n ∧ IsTotallyRamifiedMilne A K E}.Finite

end NumberFieldKB.MilneANT
