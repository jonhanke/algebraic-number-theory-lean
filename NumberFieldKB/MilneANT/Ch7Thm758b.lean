import NumberFieldKB.MilneANT.Ch7RamificationFields
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Algebraic Number Theory*, Theorem 7.58(b) and Corollary 7.59, unconditionally

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`,
Theorem 7.58(b) and Corollary 7.59, p. 131.

Setting as in `Ch7Ramification.lean`: $A$ a complete discrete valuation ring with fraction field $K$, $L/K$ finite
Galois, $B$ the integral closure of $A$ in $L$ with maximal ideal $\mathfrak p = (\Pi)$, residue fields $k$, $l$ with
$l/k$ separable, $G_0$ the inertia group.

Theorem 7.58(b) asserts $G_i = \{\sigma \in G_0 : |\sigma\Pi - \Pi| < |\Pi|^i\}$ for $i \ge 1$. Proof outline:

1. (`exists_inertia_fixed_residue`) For every $b \in B$ there is $a \in B$ fixed by all of $G_0$ with
   $b - a \in \mathfrak p$. This is the statement that the fixed ring $B^{G_0}$ has the full residue field $l$. It follows
   from Mathlib's invariant-theory API: $B$ is invariant over $B^{G_0}$, so $l$ is normal over the residue field $k_0$ of
   $B^{G_0}$ (`Ideal.Quotient.normal`), finite, and separable (since $l/k$ is), hence Galois; every automorphism of
   $l/k_0$ lifts to the stabilizer of $\mathfrak p$ in $G_0$ (`Ideal.Quotient.stabilizerHom_surjective`), which acts
   trivially on $l$, so $\operatorname{Gal}(l/k_0)$ is trivial and $l = k_0$.
2. Writing $b = \sum_{j<N} a_j \Pi^j + c$ with $a_j \in B^{G_0}$ and $c \in \mathfrak p^N$ (induction on $N$) and
   using that $\sigma\Pi^j - \Pi^j$ is a multiple of $\sigma\Pi - \Pi$, one gets $\sigma b - b \in \mathfrak p^{i+1}$
   whenever $\sigma \in G_0$ and $\sigma\Pi - \Pi \in \mathfrak p^{i+1}$.

This differs from Milne's proof, which uses the valuation ring of the maximal unramified subextension $K_0$ (so that
$B = A_0[\Pi]$), in using the fixed ring of $G_0$ instead; the idea is the same. The inclusion $\subseteq$ is
`thm_7_58b_le`. The corollary statements `cor_7_59_*_unconditional` apply `cor_7_59_*` to `theorem_7_58b`.
-/

open IsLocalRing Pointwise

universe u v w

namespace NumberFieldKB.MilneANT

namespace Thm758b

section Generic

attribute [local instance] Ideal.Quotient.field

/-- A finite group acting on `B` trivially modulo a maximal ideal `Q` over a maximal `P` with separable residue
extension: every element of `B` is congruent modulo `Q` to a fixed element. -/
theorem fixed_residue {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (H : Type*) [Group H] [Finite H] [MulSemiringAction H B] [SMulCommClass H A B]
    (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] [P.IsMaximal] [Q.IsMaximal]
    [Algebra.IsSeparable (A ⧸ P) (B ⧸ Q)]
    (hfix : ∀ (h : H) (b : B), h • b - b ∈ Q) (b : B) :
    ∃ a : B, (∀ h : H, h • a = a) ∧ b - a ∈ Q := by
  let R := FixedPoints.subalgebra A B H
  have hint : Algebra.IsIntegral R B := Algebra.IsInvariant.isIntegral R B H
  have hP0 : (Q.under R).IsMaximal := Ideal.IsMaximal.under R Q
  have hnorm : Normal (R ⧸ Q.under R) (B ⧸ Q) := Ideal.Quotient.normal H (Q.under R) Q
  have hle : P ≤ (Q.under R).under A := by
    intro x hx
    have hx' : x ∈ Q.under A := (Ideal.LiesOver.over (p := P) (P := Q)) ▸ hx
    rw [Ideal.mem_comap, Ideal.mem_comap]
    simpa using hx'
  let _ : Algebra (A ⧸ P) (R ⧸ Q.under R) := Ideal.Quotient.algebraQuotientOfLEComap hle
  have : IsScalarTower (A ⧸ P) (R ⧸ Q.under R) (B ⧸ Q) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  have : Algebra.IsSeparable (R ⧸ Q.under R) (B ⧸ Q) :=
    Algebra.isSeparable_tower_top_of_isSeparable (A ⧸ P) _ _
  have := Ideal.Quotient.finite_of_isInvariant H (Q.under R) Q
  have : IsGalois (R ⧸ Q.under R) (B ⧸ Q) := { __ := hnorm }
  have htriv : ∀ f : (B ⧸ Q) ≃ₐ[R ⧸ Q.under R] (B ⧸ Q), f = 1 := by
    intro f
    obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective H (Q.under R) Q f
    rw [← hg]
    refine AlgEquiv.ext fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk Q (g.1 • x) = Ideal.Quotient.mk Q x
    exact (Ideal.Quotient.eq).mpr (hfix g.1 x)
  have hcard : Nat.card ((B ⧸ Q) ≃ₐ[R ⧸ Q.under R] (B ⧸ Q)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun f g => (htriv f).trans (htriv g).symm⟩, ⟨1⟩⟩
  have h1 : Module.finrank (R ⧸ Q.under R) (B ⧸ Q) = 1 := by
    rw [← IsGalois.card_aut_eq_finrank, hcard]
  have : Module.Free (R ⧸ Q.under R) (B ⧸ Q) := Module.Free.of_divisionRing _ _
  have h2 : (⊤ : Subalgebra (R ⧸ Q.under R) (B ⧸ Q)) = ⊥ :=
    (Subalgebra.bot_eq_top_of_finrank_eq_one h1).symm
  have hb : Ideal.Quotient.mk Q b ∈ (⊥ : Subalgebra (R ⧸ Q.under R) (B ⧸ Q)) := h2 ▸ Algebra.mem_top
  obtain ⟨y, hy⟩ := Algebra.mem_bot.mp hb
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨r.1, fun h => r.2 h, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact hy.symm

end Generic

/-- Generic form of step 2: if a ring endomorphism `f` of a ring `B` with `P = (ϖ)` preserves all powers of `P`,
fixes a set `S` of representatives of `B / P`, and moves `ϖ` by an element of `P ^ (i + 1)`, then it moves every
element of `B` by an element of `P ^ (i + 1)`. -/
theorem move_mem_pow {B : Type*} [CommRing B] {P : Ideal B} {ϖ : B} (hϖ : P = Ideal.span {ϖ})
    (f : B →+* B) (hf : ∀ (n : ℕ) (x : B), x ∈ P ^ n → f x ∈ P ^ n) (S : Set B)
    (hS : ∀ b : B, ∃ a ∈ S, b - a ∈ P) (hfS : ∀ a ∈ S, f a = a) (i : ℕ)
    (hi : f ϖ - ϖ ∈ P ^ (i + 1)) (b : B) : f b - b ∈ P ^ (i + 1) := by
  have key : ∀ N : ℕ, ∀ b : B, ∃ x : B, f x - x ∈ P ^ (i + 1) ∧ b - x ∈ P ^ N := by
    intro N
    induction N with
    | zero => intro b; exact ⟨0, by simp, by simp⟩
    | succ N ih =>
      intro b
      obtain ⟨x, hx, hbx⟩ := ih b
      rw [hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hbx
      obtain ⟨y, hy⟩ := hbx
      obtain ⟨a, haS, hya⟩ := hS y
      rw [hϖ, Ideal.mem_span_singleton] at hya
      obtain ⟨z, hz⟩ := hya
      refine ⟨x + ϖ ^ N * a, ?_, ?_⟩
      · have hd : f ϖ - ϖ ∣ f ϖ ^ N - ϖ ^ N := sub_dvd_pow_sub_pow _ _ _
        have hmem : f ϖ ^ N - ϖ ^ N ∈ P ^ (i + 1) := by
          obtain ⟨c, hc⟩ := hd
          rw [hc]; exact Ideal.mul_mem_right _ _ hi
        have : f (x + ϖ ^ N * a) - (x + ϖ ^ N * a) =
            (f x - x) + (f ϖ ^ N - ϖ ^ N) * a := by
          rw [map_add, map_mul, map_pow, hfS a haS]; ring
        rw [this]
        exact Ideal.add_mem _ hx (Ideal.mul_mem_right _ _ hmem)
      · rw [hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        refine ⟨z, ?_⟩
        have : b - (x + ϖ ^ N * a) = (b - x) - ϖ ^ N * a := by ring
        rw [this, hy, show y = a + ϖ * z by rw [← hz]; ring]
        ring
  obtain ⟨x, hx, hbx⟩ := key (i + 1) b
  have h1 : f (b - x) ∈ P ^ (i + 1) := hf _ _ hbx
  have : f b - b = (f x - x) + (f (b - x) - (b - x)) := by rw [map_sub]; ring
  rw [this]
  exact Ideal.add_mem _ hx (Ideal.sub_mem _ h1 hbx)

section Setting

attribute [local instance] Ideal.Quotient.field

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]

set_option linter.unusedSectionVars false

/-- The restriction of $\sigma \in G$ to a ring automorphism of $B$. -/
private noncomputable abbrev rB (σ : L ≃ₐ[K] L) : integralClosure A L ≃ₐ[A] integralClosure A L :=
  galRestrict A K L (integralClosure A L) σ

private lemma coe_rB (σ : L ≃ₐ[K] L) (b : integralClosure A L) :
    ((rB A K L σ b : integralClosure A L) : L) = σ b :=
  algebraMap_galRestrict_apply A σ b

private lemma rB_mem_max_iff (σ : L ≃ₐ[K] L) (x : integralClosure A L) :
    rB A K L σ x ∈ maximalIdeal (integralClosure A L) ↔ x ∈ maximalIdeal (integralClosure A L) := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_congr (MulEquiv.isUnit_map (rB A K L σ).toRingEquiv.toMulEquiv)

private lemma rB_mem_pow (n : ℕ) (σ : L ≃ₐ[K] L) {x : integralClosure A L}
    (hx : x ∈ maximalIdeal (integralClosure A L) ^ n) :
    rB A K L σ x ∈ maximalIdeal (integralClosure A L) ^ n := by
  set f : integralClosure A L →+* integralClosure A L := (rB A K L σ).toRingEquiv.toRingHom
  have hc : (maximalIdeal (integralClosure A L)).comap f = maximalIdeal (integralClosure A L) := by
    ext y
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (MulEquiv.isUnit_map (rB A K L σ).toRingEquiv.toMulEquiv)
  have h1 : (maximalIdeal (integralClosure A L)).map f ≤ maximalIdeal (integralClosure A L) :=
    Ideal.map_le_iff_le_comap.mpr hc.ge
  have h2 : ((maximalIdeal (integralClosure A L)) ^ n).map f ≤ maximalIdeal (integralClosure A L) ^ n := by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono h1 n
  exact h2 (Ideal.mem_map_of_mem f hx)

private lemma mem_group_iff (i : ℕ) (σ : L ≃ₐ[K] L) :
    σ ∈ ramificationGroupMilne A K L i ↔
      ∀ b : integralClosure A L, rB A K L σ b - b ∈ maximalIdeal (integralClosure A L) ^ (i + 1) := by
  change IsInRamificationGroupMilne A K L i σ ↔ _
  constructor
  · intro h b
    exact h b _ (coe_rB A K L σ b)
  · intro h b b' hb
    have : b' = rB A K L σ b := Subtype.ext (by rw [hb, coe_rB])
    rw [this]; exact h b

/-- **Fixed ring of the inertia group has the full residue field.** Assume $l/k$ is separable. For every $b \in B$
there is $a \in B$ fixed by all of $G_0$ with $b - a \in \mathfrak p$; i.e. the ring $B^{G_0}$ surjects onto the
residue field $l$ of $B$. -/
theorem exists_inertia_fixed_residue
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]
    (b : integralClosure A L) :
    ∃ a : integralClosure A L, (∀ σ ∈ ramificationGroupMilne A K L 0, σ (a : L) = (a : L)) ∧
      b - a ∈ maximalIdeal (integralClosure A L) := by
  classical
  have hsmul : ∀ (g : ramificationGroupMilne A K L 0) (x : integralClosure A L),
      g • x = rB A K L g.1 x := fun g x => Subtype.ext (by rw [coe_rB]; rfl)
  have hlies : (maximalIdeal (integralClosure A L)).LiesOver (maximalIdeal A) := by
    refine ⟨?_⟩
    ext x
    simp [Ideal.under, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hfix : ∀ (g : ramificationGroupMilne A K L 0) (x : integralClosure A L),
      g • x - x ∈ maximalIdeal (integralClosure A L) := by
    intro g x
    have := (mem_group_iff A K L 0 g.1).mp g.2 x
    rw [hsmul]
    rwa [zero_add, pow_one] at this
  have hsep : Algebra.IsSeparable (A ⧸ maximalIdeal A)
      (integralClosure A L ⧸ maximalIdeal (integralClosure A L)) :=
    inferInstanceAs (Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L)))
  obtain ⟨a, ha, hba⟩ := fixed_residue (A := A) (ramificationGroupMilne A K L 0) (maximalIdeal A)
    (maximalIdeal (integralClosure A L)) hfix b
  refine ⟨a, fun σ hσ => ?_, hba⟩
  have := ha ⟨σ, hσ⟩
  rw [hsmul] at this
  rw [← coe_rB A K L σ a, this]

end Setting

end Thm758b

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]

/-- **Fixed ring of the inertia group has the full residue field** (used for Theorem 7.58(a) and (b)). Assume the
residue field extension $l/k$ is separable. For every $b \in B$ there is $a \in B$ fixed by all of $G_0$ with
$b - a \in \mathfrak p$. -/
@[kb "milne2020ant" "v3.08, Thm. 7.58, p. 131"]
theorem exists_inertia_fixed_residue
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))]
    (b : integralClosure A L) :
    ∃ a : integralClosure A L, (∀ σ ∈ ramificationGroupMilne A K L 0, σ (a : L) = (a : L)) ∧
      b - a ∈ maximalIdeal (integralClosure A L) :=
  Thm758b.exists_inertia_fixed_residue A K L b

/-- **Theorem 7.58(b)**, unconditionally. Assume $l/k$ separable and let $\Pi$ generate $\mathfrak p$. For $i \ge 1$,
$G_i = \{\sigma \in G_0 : |\sigma\Pi - \Pi| < |\Pi|^i\}$. -/
@[kb "milne2020ant" "v3.08, Thm. 7.58, p. 131"]
theorem theorem_7_58b : Theorem7_58b A K L := by
  refine ⟨fun ϖ hϖ i _ σ => ⟨fun hσ => thm_7_58b_le A K L ϖ i σ hσ, ?_⟩⟩
  rintro ⟨hσ0, hϖ'⟩
  refine (Thm758b.mem_group_iff A K L i σ).mpr fun b => ?_
  exact Thm758b.move_mem_pow hϖ (Thm758b.rB A K L σ).toRingEquiv.toRingHom
    (fun n x hx => Thm758b.rB_mem_pow A K L n σ hx)
    {a | ∀ τ ∈ ramificationGroupMilne A K L 0, τ (a : L) = (a : L)}
    (fun b => by
      obtain ⟨a, ha, hba⟩ := exists_inertia_fixed_residue A K L b
      exact ⟨a, ha, hba⟩)
    (fun a ha => Subtype.ext (by
      change ((Thm758b.rB A K L σ a : integralClosure A L) : L) = (a : L)
      rw [Thm758b.coe_rB]; exact ha σ hσ0))
    i (hϖ' _ (Thm758b.coe_rB A K L σ ϖ)) b

/-- **Corollary 7.59**, $G_0/G_1 \hookrightarrow l^\times$, unconditionally (applies `cor_7_59_units` to
`theorem_7_58b`). -/
@[kb "milne2020ant" "v3.08, Cor. 7.59, p. 131"]
theorem cor_7_59_units_unconditional
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))] :
    ∃ θ : ramificationGroupMilne A K L 0 →* (ResidueField (integralClosure A L))ˣ,
      θ.ker = (ramificationGroupMilne A K L 1).subgroupOf (ramificationGroupMilne A K L 0) :=
  cor_7_59_units A K L (theorem_7_58b A K L)

/-- **Corollary 7.59**, $G_i/G_{i+1} \hookrightarrow l$ for $i \ge 1$, unconditionally (applies `cor_7_59_additive`
to `theorem_7_58b`). -/
@[kb "milne2020ant" "v3.08, Cor. 7.59, p. 131"]
theorem cor_7_59_additive_unconditional
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))] (i : ℕ) (hi : 1 ≤ i) :
    ∃ θ : ramificationGroupMilne A K L i →* Multiplicative (ResidueField (integralClosure A L)),
      θ.ker = (ramificationGroupMilne A K L (i + 1)).subgroupOf (ramificationGroupMilne A K L i) :=
  cor_7_59_additive A K L (theorem_7_58b A K L) i hi

/-- **Corollary 7.59**, last assertion, unconditionally: if the residue field $k$ is finite, then
$\operatorname{Gal}(L/K)$ is solvable (applies `cor_7_59_isSolvable` to `theorem_7_58b`). -/
@[kb "milne2020ant" "v3.08, Cor. 7.59, p. 131"]
theorem cor_7_59_isSolvable_unconditional [Finite (ResidueField A)] :
    Group.IsSolvable (L ≃ₐ[K] L) :=
  cor_7_59_isSolvable A K L (theorem_7_58b A K L)

/-- **Tamely ramified iff $G_1 = 1$** (Milne p. 131), unconditionally: for $L/K$ Galois with $l/k$ separable, $L/K$
is tamely ramified iff $G_1 = 1$ (applies `isTamelyRamifiedMilne_iff` to `theorem_7_58b`). -/
@[kb "milne2020ant" "v3.08, Ch. 7, after Cor. 7.59, p. 131"]
theorem isTamelyRamifiedMilne_iff_unconditional
    [Algebra.IsSeparable (ResidueField A) (ResidueField (integralClosure A L))] :
    IsTamelyRamifiedMilne A L ↔ ramificationGroupMilne A K L 1 = ⊥ :=
  isTamelyRamifiedMilne_iff A K L (theorem_7_58b A K L)

end NumberFieldKB.MilneANT
