import NumberFieldKB.MilneANT.Ch8Basic

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: computing Galois groups

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

The Galois group of a polynomial $f$ over $K$ is Mathlib's `Polynomial.Gal f` $= \mathrm{Gal}(E/K)$, $E$ the splitting
field, acting on the roots `f.rootSet E`; a permutation's "cycle type including fixed points" (Milne's
$\sigma = c_1\cdots c_s$ with $\sum n_i = n$) is Mathlib's `Equiv.Perm.partition`; the "degrees of the irreducible
factors" of a monic $f$ are the multiset `(normalizedFactors f).map natDegree`.

* **Theorem 8.20** (`Theorem8_20`, named statement, van der Waerden).
* **Proposition 8.21** (`prop_8_21`, proved), **Corollary 8.22** (`cor_8_22`, proved).
* **Remark 8.24** (`Remark8_24`, named statement).
* **Lemma 8.26** (`lemma_8_26`, proved); **Remark 8.28** (Mathlib, tagged).

Theorem 8.23 and its consequences (8.25, 8.27, 8.36, 8.37, 8.40(c)–(e)) are in `Ch8Dedekind.lean`.
-/

open NumberField IsDedekindDomain Polynomial UniqueFactorizationMonoid
open scoped Classical

namespace NumberFieldKB.MilneANT

noncomputable section

/-- The permutation of the roots of `f` in `E` induced by an element of a group acting on `E`. -/
abbrev rootPerm {F E G : Type*} [Field F] [Field E] [Algebra F E] [Group G] [MulSemiringAction G E]
    [SMulCommClass G F E] (f : F[X]) (σ : G) : Equiv.Perm (f.rootSet E) :=
  MulAction.toPermHom G (f.rootSet E) σ

/-- The permutation of the roots of `f` in its splitting field induced by an element of the Galois group
`Polynomial.Gal f` (Mathlib's action `Polynomial.Gal.galActionAux`). -/
abbrev galPerm {F : Type*} [Field F] (f : F[X]) (σ : f.Gal) : Equiv.Perm (f.rootSet f.SplittingField) :=
  MulAction.toPermHom f.Gal (f.rootSet f.SplittingField) σ

/-! ## Theorem 8.20 -/

/-- **Theorem 8.20** (van der Waerden; named statement). Let $f \in K[X]$ be separable of degree $n$ with roots
$\alpha_1, \dots, \alpha_n$ (numbered by `e`) in its splitting field $E$, let $\theta = \sum \alpha_i t_i$ and
$F(X, t) = \prod_{\sigma \in S_n}(X - \sigma_t\theta)$, where $\sigma_t$ permutes the variables $t_i$. Then $F$ has
coefficients in $K[t]$, and if $F_1 \in K[t][X]$ is the irreducible factor of $F$ divisible (over $E$) by
$X - \theta$, the permutations $\sigma$ with $\sigma_t F_1 = F_1$ are exactly the Galois group of $f$ (transported to
$S_n$ by `e`).

*Correction.* Milne takes "$F_1$" to be any irreducible factor; for a factor not divisible by $X - \theta$ the
stabilizer is a conjugate of the Galois group, not the group itself. -/
@[kb "milne2020ant" "v3.08, Thm. 8.20, p. 144"]
structure Theorem8_20 : Prop where
  galois_eq_stabilizer : ∀ (K : Type) [Field K] (f : K[X]) (_ : f.Separable) (n : ℕ)
    (e : Fin n ≃ f.rootSet f.SplittingField)
    (F₁ : (MvPolynomial (Fin n) K)[X]),
    let θ : MvPolynomial (Fin n) f.SplittingField := ∑ i, MvPolynomial.C (e i : f.SplittingField) * MvPolynomial.X i
    let F : (MvPolynomial (Fin n) f.SplittingField)[X] :=
      ∏ σ : Equiv.Perm (Fin n), (X - C (MvPolynomial.rename (R := f.SplittingField) σ θ))
    let ι : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) f.SplittingField :=
      MvPolynomial.map (algebraMap K f.SplittingField)
    Irreducible F₁ → F₁.map ι ∣ F → (X - C θ) ∣ F₁.map ι →
      ∀ σ : Equiv.Perm (Fin n),
        F₁.map (MvPolynomial.rename (R := K) σ).toRingHom = F₁ ↔
          ∃ g : f.Gal, ∀ i, g (e i : f.SplittingField) = (e (σ i) : f.SplittingField)

/-! ## Cycles of a permutation as classes of the cyclic-group orbit relation -/

section CycleBlocks

open Equiv Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The cycle (a class of "lie in the same cycle") of a permutation `σ` indexed by a class `q`, as a finset. -/
def cycleBlock (σ : Perm α) (q : Quotient (Perm.SameCycle.setoid σ)) : Finset α :=
  univ.filter fun x => (⟦x⟧ : Quotient (Perm.SameCycle.setoid σ)) = q

omit [DecidableEq α] in
/-- Membership in `cycleBlock`. -/
theorem mem_cycleBlock {σ : Perm α} {q : Quotient (Perm.SameCycle.setoid σ)} {x : α} :
    x ∈ cycleBlock σ q ↔ (⟦x⟧ : Quotient (Perm.SameCycle.setoid σ)) = q := by
  simp [cycleBlock]

omit [DecidableEq α] in
/-- The cycle of `x` consists of the points in the same cycle as `x`. -/
theorem mem_cycleBlock_mk {σ : Perm α} {x y : α} :
    y ∈ cycleBlock σ ⟦x⟧ ↔ σ.SameCycle x y := by
  rw [mem_cycleBlock, Quotient.eq (r := Perm.SameCycle.setoid σ)]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- For a non-fixed point `x`, the cycle of `x` is the support of `σ.cycleOf x`. -/
theorem cycleBlock_mk_eq_support {σ : Perm α} {x : α} (hx : σ x ≠ x) :
    cycleBlock σ ⟦x⟧ = (σ.cycleOf x).support := by
  ext y
  rw [mem_cycleBlock_mk, Perm.mem_support_cycleOf_iff' hx]

/-- The cycle of `x` is a singleton iff `x` is a fixed point. -/
theorem card_cycleBlock_eq_one_iff {σ : Perm α} {x : α} :
    (cycleBlock σ ⟦x⟧).card = 1 ↔ σ x = x := by
  constructor
  · intro h
    by_contra hx
    rw [Finset.card_eq_one] at h
    obtain ⟨a, ha⟩ := h
    have h1 : x ∈ cycleBlock σ ⟦x⟧ := mem_cycleBlock.2 rfl
    have h2 : σ x ∈ cycleBlock σ ⟦x⟧ :=
      mem_cycleBlock_mk.2 (Perm.SameCycle.apply_right (Perm.SameCycle.refl _ _))
    rw [ha, Finset.mem_singleton] at h1 h2
    exact hx (h2.trans h1.symm)
  · intro hx
    rw [Finset.card_eq_one]
    refine ⟨x, ?_⟩
    ext y
    rw [mem_cycleBlock_mk, Finset.mem_singleton]
    constructor
    · intro h
      exact (Perm.SameCycle.eq_of_left h hx).symm
    · rintro rfl; exact Perm.SameCycle.refl _ _

omit [DecidableEq α] in
/-- Every cycle is nonempty. -/
theorem card_cycleBlock_pos {σ : Perm α} (q : Quotient (Perm.SameCycle.setoid σ)) :
    0 < (cycleBlock σ q).card := by
  induction q using Quotient.inductionOn with
  | _ x => exact Finset.card_pos.2 ⟨x, mem_cycleBlock.2 rfl⟩

/-- The parts of the partition of a permutation are the sizes of its cycles (fixed points included). -/
theorem partition_parts_eq (σ : Perm α) :
    σ.partition.parts =
      (univ : Finset (Quotient (Perm.SameCycle.setoid σ))).val.map fun q => (cycleBlock σ q).card := by
  set f : Quotient (Perm.SameCycle.setoid σ) → ℕ := fun q => (cycleBlock σ q).card with hf
  set M := (univ : Finset (Quotient (Perm.SameCycle.setoid σ))).val.map f with hM
  have hfout : ∀ q, f q = (cycleBlock σ ⟦q.out⟧).card := fun q => by
    simp only [hf, Quotient.out_eq]
  have hout : ∀ q : Quotient (Perm.SameCycle.setoid σ), 2 ≤ f q → σ q.out ≠ q.out := fun q h hx => by
    have := (card_cycleBlock_eq_one_iff (σ := σ) (x := q.out)).2 hx
    rw [← hfout] at this
    omega
  have h1 : M.filter (fun n => 2 ≤ n) = σ.cycleType := by
    rw [hM, Multiset.filter_map, Perm.cycleType_def]
    refine Multiset.map_eq_map_of_bij_of_nodup f (Finset.card ∘ Perm.support)
      (Multiset.Nodup.filter _ (Finset.nodup _)) (Finset.nodup _)
      (fun q _ => σ.cycleOf q.out) ?_ ?_ ?_ ?_
    · intro q hq
      have hq' : 2 ≤ f q := by simpa using hq
      exact Perm.cycleOf_mem_cycleFactorsFinset_iff.2 (Perm.mem_support.2 (hout q hq'))
    · intro q₁ h₁ q₂ h₂ h
      have h₁' : 2 ≤ f q₁ := by simpa using h₁
      have h₂' : 2 ≤ f q₂ := by simpa using h₂
      have := (Perm.sameCycle_iff_cycleOf_eq_of_mem_support (Perm.mem_support.2 (hout q₁ h₁'))
        (Perm.mem_support.2 (hout q₂ h₂'))).2 h
      have h3 : (⟦q₁.out⟧ : Quotient (Perm.SameCycle.setoid σ)) = ⟦q₂.out⟧ := Quotient.sound this
      simpa using h3
    · intro c hc
      obtain ⟨hcyc, -⟩ := Perm.mem_cycleFactorsFinset_iff.1 hc
      obtain ⟨a, ha⟩ := hcyc.nonempty_support
      have hca := Perm.cycle_is_cycleOf ha hc
      have hax : σ a ≠ a := Perm.mem_support.1 (by
        have := Perm.cycleOf_mem_cycleFactorsFinset_iff (f := σ) (x := a)
        exact this.1 (hca ▸ hc))
      have hcard : f ⟦a⟧ = c.support.card := by
        simp only [hf]
        rw [cycleBlock_mk_eq_support hax, ← hca]
      refine ⟨⟦a⟧, ?_, ?_⟩
      · have := hcyc.two_le_card_support
        simp only [Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and, Function.comp]
        rw [hcard]
        omega
      · have : σ.SameCycle (⟦a⟧ : Quotient (Perm.SameCycle.setoid σ)).out a :=
          Quotient.mk_out (s := Perm.SameCycle.setoid σ) a
        rw [Perm.SameCycle.cycleOf_eq this, hca]
    · intro q hq
      have hq' : 2 ≤ f q := by simpa using hq
      simp only [Function.comp]
      rw [hfout, cycleBlock_mk_eq_support (hout q hq')]
  have h2 : M.filter (fun n => ¬ 2 ≤ n) = Multiset.replicate (Fintype.card α - σ.support.card) 1 := by
    rw [Multiset.eq_replicate]
    constructor
    · rw [hM, Multiset.filter_map, Multiset.card_map]
      have : Multiset.card (Multiset.filter ((fun n => ¬ 2 ≤ n) ∘ f)
            (univ : Finset (Quotient (Perm.SameCycle.setoid σ))).val)
          = (univ.filter fun q : Quotient (Perm.SameCycle.setoid σ) => ¬ 2 ≤ f q).card := rfl
      rw [this, ← Finset.card_compl]
      refine Finset.card_nbij' (fun q => q.out) (fun x => ⟦x⟧) ?_ ?_ ?_ ?_
      · intro q hq
        have hq' : ¬ 2 ≤ f q := by simpa using hq
        have := card_cycleBlock_pos q
        have h1' : f q = 1 := by simp only [hf] at hq' ⊢; omega
        rw [hfout] at h1'
        have := card_cycleBlock_eq_one_iff.1 h1'
        simp [Perm.mem_support, this]
      · intro x hx
        have hx' : σ x = x := by simpa [Perm.mem_support] using hx
        have : f ⟦x⟧ = 1 := card_cycleBlock_eq_one_iff.2 hx'
        simp [this]
      · intro q _
        simp
      · intro x hx
        have hx' : σ x = x := by simpa [Perm.mem_support] using hx
        have : σ.SameCycle (⟦x⟧ : Quotient (Perm.SameCycle.setoid σ)).out x :=
          Quotient.mk_out (s := Perm.SameCycle.setoid σ) x
        exact (Perm.SameCycle.eq_of_left this.symm hx').symm
    · intro b hb
      rw [hM, Multiset.filter_map] at hb
      simp only [Multiset.mem_map, Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and,
        Function.comp] at hb
      obtain ⟨q, hq, rfl⟩ := hb
      have := card_cycleBlock_pos q
      simp only [hf] at hq ⊢
      omega
  rw [Perm.parts_partition, ← h1, ← h2]
  exact Multiset.filter_add_not _ _

/-- A transitive permutation group containing a permutation of cycle type $(n-1, 1)$ and a transposition is the
full symmetric group (proof of Lemma 8.26). -/
theorem eq_top_of_transitive_of_cycleType_of_isSwap (H : Subgroup (Equiv.Perm α))
    (htrans : MulAction.IsPretransitive H α)
    (hcyc : ∃ σ ∈ H, σ.partition.parts = {Fintype.card α - 1, 1})
    (hswap : ∃ τ ∈ H, τ.IsSwap) : H = ⊤ := by
  obtain ⟨σ, hσH, hσ⟩ := hcyc
  rw [partition_parts_eq] at hσ
  have hcard : Fintype.card (Quotient (Perm.SameCycle.setoid σ)) = 2 := by
    have := congrArg Multiset.card hσ
    simpa using this
  have h1 : (1 : ℕ) ∈ (univ : Finset (Quotient (Perm.SameCycle.setoid σ))).val.map
      fun q => (cycleBlock σ q).card := by
    rw [hσ]; simp
  obtain ⟨q₀, -, hq₀⟩ := Multiset.mem_map.1 h1
  set a := q₀.out with ha
  have hq₀a : q₀ = ⟦a⟧ := (Quotient.out_eq q₀).symm
  have hfix : σ a = a := by
    apply card_cycleBlock_eq_one_iff.1
    rw [← hq₀a]; exact hq₀
  have hconn : ∀ b c, b ≠ a → c ≠ a → σ.SameCycle b c := by
    intro b c hb hc
    by_contra hbc
    have hne : ∀ d, d ≠ a → (⟦d⟧ : Quotient (Perm.SameCycle.setoid σ)) ≠ ⟦a⟧ := by
      intro d hd h
      have : σ.SameCycle d a := Quotient.exact h
      exact hd (Perm.SameCycle.eq_of_left this.symm hfix).symm
    have h3 : 2 < Fintype.card (Quotient (Perm.SameCycle.setoid σ)) := by
      rw [Fintype.two_lt_card_iff]
      refine ⟨⟦a⟧, ⟦b⟧, ⟦c⟧, (hne b hb).symm, (hne c hc).symm, fun h => hbc (Quotient.exact h)⟩
    omega
  -- all transpositions `swap a c` lie in `H`
  have hac : ∀ c, c ≠ a → Equiv.swap a c ∈ H := by
    obtain ⟨τ, hτH, x, y, hxy, rfl⟩ := hswap
    obtain ⟨g, hg⟩ := htrans.exists_smul_eq x a
    have hgx : (g : Equiv.Perm α) x = a := hg
    have hgy : (g : Equiv.Perm α) y ≠ a := by
      intro h
      exact hxy ((g : Equiv.Perm α).injective (hgx.trans h.symm))
    have hb : Equiv.swap a ((g : Equiv.Perm α) y) ∈ H := by
      have := Equiv.swap_apply_apply (g : Equiv.Perm α) x y
      rw [hgx] at this
      rw [this]
      exact H.mul_mem (H.mul_mem g.2 hτH) (H.inv_mem g.2)
    intro c hc
    obtain ⟨k, hk⟩ := hconn _ _ hgy hc
    have := Equiv.swap_apply_apply (σ ^ k) a ((g : Equiv.Perm α) y)
    have hka : (σ ^ k) a = a := Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfix k
    rw [hka, hk] at this
    rw [this]
    exact H.mul_mem (H.mul_mem (H.zpow_mem hσH k) hb) (H.inv_mem (H.zpow_mem hσH k))
  have hall : ∀ x y : α, x ≠ y → Equiv.swap x y ∈ H := by
    intro x y hxy
    by_cases hx : x = a
    · subst hx; exact hac y hxy.symm
    by_cases hy : y = a
    · subst hy; rw [Equiv.swap_comm]; exact hac x hx
    exact SubmonoidClass.swap_mem_trans H (by rw [Equiv.swap_comm]; exact hac x hx) (hac y hy)
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap]
  rw [Subgroup.closure_le]
  rintro _ ⟨x, y, hxy, rfl⟩
  exact hall x y hxy

end CycleBlocks

/-! ## Proposition 8.21 and Corollary 8.22 -/

section Orbits

variable {K : Type*} [Field K]

/-- **Proposition 8.21** (proved): if the Galois group $G$ of a monic separable $f \in K[X]$ has orbits of sizes
$n_1, \dots, n_s$ on the roots, then $f = f_1\cdots f_s$ with $f_i$ irreducible of degree $n_i$: the orbits of $G$ on
the roots correspond bijectively to the monic irreducible factors of $f$ (`normalizedFactors f`, whose product is
$f$), the orbit of size $n_i$ to a factor of degree $n_i$ (the factor whose roots are the orbit). -/
@[kb "milne2020ant" "v3.08, Prop. 8.21, p. 144"]
theorem prop_8_21 (f : K[X]) (hf : f.Monic) (hs : f.Separable) :
    ∃ e : MulAction.orbitRel.Quotient f.Gal (f.rootSet f.SplittingField) ≃ {g // g ∈ normalizedFactors f},
      ∀ O, (e O).1.natDegree = O.orbit.ncard ∧
        ∀ x : f.rootSet f.SplittingField, x ∈ O.orbit ↔ aeval (x : f.SplittingField) (e O).1 = 0 := by
  have hf0 : f ≠ 0 := hf.ne_zero
  have hint : ∀ x : f.SplittingField, IsIntegral K x := fun x => Algebra.IsIntegral.isIntegral x
  have hmem : ∀ x : f.rootSet f.SplittingField, minpoly K (x : f.SplittingField) ∈ normalizedFactors f := by
    intro x
    rw [mem_normalizedFactors_iff' hf0]
    refine ⟨minpoly.irreducible (hint _), (minpoly.monic (hint _)).normalize_eq_self,
      minpoly.dvd K _ ?_⟩
    exact (mem_rootSet.1 x.2).2
  have horb : ∀ x y : f.rootSet f.SplittingField, x ∈ MulAction.orbit f.Gal y ↔
      minpoly K (x : f.SplittingField) = minpoly K (y : f.SplittingField) := by
    intro x y
    constructor
    · rintro ⟨σ, rfl⟩
      exact minpoly.algEquiv_eq σ (y : f.SplittingField)
    · intro h
      obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K) (E := f.SplittingField)).1 h
      exact ⟨σ, Subtype.ext hσ⟩
  let Φ : MulAction.orbitRel.Quotient f.Gal (f.rootSet f.SplittingField) → {g // g ∈ normalizedFactors f} :=
    Quotient.lift (fun x => ⟨minpoly K (x : f.SplittingField), hmem x⟩) (by
      intro a b hab
      exact Subtype.ext ((horb _ _).1 hab))
  have hΦ : ∀ y : f.rootSet f.SplittingField,
      (Φ (Quotient.mk'' y)).1 = minpoly K (y : f.SplittingField) := fun y => rfl
  have hbij : Function.Bijective Φ := by
    constructor
    · intro p q
      induction p using Quotient.inductionOn' with | _ a => ?_
      induction q using Quotient.inductionOn' with | _ b => ?_
      intro h
      have h' : minpoly K (a : f.SplittingField) = minpoly K (b : f.SplittingField) := by
        have := congrArg Subtype.val h
        simpa [hΦ] using this
      exact Quotient.sound' ((horb _ _).2 h')
    · rintro ⟨g, hg⟩
      obtain ⟨hirr, hnorm, hdvd⟩ := (mem_normalizedFactors_iff' hf0).1 hg
      have hg0 : g ≠ 0 := hirr.ne_zero
      have hgm : g.Monic := (normalize_eq_self_iff_monic hg0).1 hnorm
      have hsplit : (f.map (algebraMap K f.SplittingField)).Splits := IsSplittingField.splits _ f
      have hsplitg : (g.map (algebraMap K f.SplittingField)).Splits :=
        Splits.of_dvd hsplit (Polynomial.map_ne_zero hf0) (Polynomial.map_dvd _ hdvd)
      have hdeg : (g.map (algebraMap K f.SplittingField)).degree ≠ 0 := by
        rw [Polynomial.degree_map]
        exact (Polynomial.degree_pos_of_irreducible hirr).ne'
      obtain ⟨a, ha⟩ := hsplitg.exists_eval_eq_zero hdeg
      have ha' : aeval a g = 0 := by
        rw [aeval_def, eval₂_eq_eval_map]; exact ha
      have haf : aeval a f = 0 := aeval_eq_zero_of_dvd_aeval_eq_zero hdvd ha'
      refine ⟨Quotient.mk'' ⟨a, mem_rootSet.2 ⟨hf0, haf⟩⟩, Subtype.ext ?_⟩
      rw [hΦ]
      exact (minpoly.eq_of_irreducible_of_monic hirr ha' hgm).symm
  refine ⟨Equiv.ofBijective Φ hbij, fun O => ?_⟩
  induction O using Quotient.inductionOn' with | _ y => ?_
  have he : ((Equiv.ofBijective Φ hbij) (Quotient.mk'' y)).1 = minpoly K (y : f.SplittingField) := rfl
  have horbit : ∀ x : f.rootSet f.SplittingField,
      x ∈ MulAction.orbitRel.Quotient.orbit
          (Quotient.mk'' y : MulAction.orbitRel.Quotient f.Gal (f.rootSet f.SplittingField)) ↔
        aeval (x : f.SplittingField) (minpoly K (y : f.SplittingField)) = 0 := by
    intro x
    rw [MulAction.orbitRel.Quotient.orbit_mk, horb]
    constructor
    · intro h
      rw [← h]; exact minpoly.aeval K _
    · intro h
      exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (hint _)) h
        (minpoly.monic (hint _))).symm
  rw [he]
  refine ⟨?_, fun x => horbit x⟩
  set g := minpoly K (y : f.SplittingField) with hg
  have hgdvd : g ∣ f := minpoly.dvd K _ (mem_rootSet.1 y.2).2
  have hgsep : g.Separable := hs.of_dvd hgdvd
  have hgsplit : (g.map (algebraMap K f.SplittingField)).Splits :=
    Splits.of_dvd (IsSplittingField.splits _ f) (Polynomial.map_ne_zero hf0) (Polynomial.map_dvd _ hgdvd)
  have himg : Subtype.val '' {x : f.rootSet f.SplittingField | aeval (x : f.SplittingField) g = 0} =
      (g.rootSet f.SplittingField : Set f.SplittingField) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_rootSet.2 ⟨(minpoly.monic (hint _)).ne_zero, hx⟩
    · intro hz
      have hz' := mem_rootSet.1 hz
      exact ⟨⟨z, mem_rootSet.2 ⟨hf0, aeval_eq_zero_of_dvd_aeval_eq_zero hgdvd hz'.2⟩⟩, hz'.2, rfl⟩
  have horbset : MulAction.orbitRel.Quotient.orbit
      (Quotient.mk'' y : MulAction.orbitRel.Quotient f.Gal (f.rootSet f.SplittingField)) =
      {x : f.rootSet f.SplittingField | aeval (x : f.SplittingField) g = 0} := by
    ext x; exact horbit x
  rw [horbset, ← Set.ncard_image_of_injective _ Subtype.val_injective, himg,
    ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact (card_rootSet_eq_natDegree hgsep hgsplit).symm

/-- **Corollary 8.22** (proved): over a finite field $k$, if $f$ is monic separable and the Frobenius element
$x\mapsto x^{|k|}$ of $\mathrm{Gal}(\ell/k)$ ($\ell$ the splitting field) is, as a permutation of the roots, a product
of disjoint cycles of lengths $n_1, \dots, n_s$ ($\sum n_i = n$, fixed points counted as cycles of length $1$), then $f$
is a product of irreducible polynomials of degrees $n_1, \dots, n_s$. -/
@[kb "milne2020ant" "v3.08, Cor. 8.22, p. 145"]
theorem cor_8_22 (k : Type*) [Field k] [Fintype k] (f : k[X]) (hf : f.Monic) (hs : f.Separable) :
    (galPerm f (FiniteField.frobeniusAlgEquivOfAlgebraic k f.SplittingField)).partition.parts =
      (normalizedFactors f).map natDegree := by
  obtain ⟨e, he⟩ := prop_8_21 f hf hs
  have hf0 : f ≠ 0 := hf.ne_zero
  set φ := FiniteField.frobeniusAlgEquivOfAlgebraic k f.SplittingField with hφ
  set σ := galPerm f φ with hσ
  have hgen : ∀ g : f.Gal, ∃ n : ℕ, φ ^ n = g := fun g => by
    obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k f.SplittingField).2 g
    exact ⟨n.1, hn⟩
  -- the cycles of the Frobenius permutation are the orbits of the Galois group
  have hcycle : ∀ a b : f.rootSet f.SplittingField,
      σ.SameCycle a b ↔ b ∈ MulAction.orbit f.Gal a := by
    intro a b
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨φ ^ i, ?_⟩
      have h1 : galPerm f (φ ^ i) = σ ^ i := map_zpow _ _ _
      rw [← hi, ← h1]
      rfl
    · rintro ⟨g, rfl⟩
      obtain ⟨n, rfl⟩ := hgen g
      refine ⟨(n : ℤ), ?_⟩
      have h1 : galPerm f (φ ^ n) = σ ^ n := map_pow _ _ _
      rw [zpow_natCast, ← h1]
      rfl
  let ε : Quotient (Equiv.Perm.SameCycle.setoid σ) →
      MulAction.orbitRel.Quotient f.Gal (f.rootSet f.SplittingField) :=
    Quotient.map (sa := Equiv.Perm.SameCycle.setoid σ) (sb := MulAction.orbitRel f.Gal _) id
      (fun a b h => (hcycle b a).1 h.symm)
  have hε : Function.Bijective ε := by
    constructor
    · intro p q
      induction p using Quotient.inductionOn with | _ a => ?_
      induction q using Quotient.inductionOn with | _ b => ?_
      intro h
      have h' : a ∈ MulAction.orbit f.Gal b := Quotient.exact h
      exact Quotient.sound ((hcycle b a).2 h').symm
    · intro O
      induction O using Quotient.inductionOn with | _ y => exact ⟨⟦y⟧, rfl⟩
  have hG : ∀ q, (cycleBlock σ q).card = (ε q).orbit.ncard := by
    intro q
    induction q using Quotient.inductionOn with
    | _ y =>
      have h1 : ε ⟦y⟧ = Quotient.mk'' y := rfl
      rw [h1, MulAction.orbitRel.Quotient.orbit_mk, ← Set.ncard_coe_finset]
      congr 1
      ext z
      simp only [Finset.mem_coe]
      rw [mem_cycleBlock_mk]
      exact hcycle y z
  have hmap : (Finset.univ : Finset (Quotient (Equiv.Perm.SameCycle.setoid σ))).val.map ε =
      Finset.univ.val := Multiset.map_univ_val_equiv (Equiv.ofBijective ε hε)
  have hnd : (normalizedFactors f).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hf0).1 hs.squarefree
  have hattach : (Finset.univ : Finset (MulAction.orbitRel.Quotient f.Gal
      (f.rootSet f.SplittingField))).val.map e = (normalizedFactors f).attach := by
    rw [Multiset.Nodup.ext (Multiset.Nodup.map e.injective Finset.univ.nodup) hnd.attach]
    intro g
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, Multiset.mem_attach,
      iff_true]
    exact e.surjective g
  rw [partition_parts_eq]
  calc (Finset.univ : Finset (Quotient (Equiv.Perm.SameCycle.setoid σ))).val.map
        (fun q => (cycleBlock σ q).card)
      = (Finset.univ : Finset (Quotient (Equiv.Perm.SameCycle.setoid σ))).val.map
          (fun q => (ε q).orbit.ncard) := Multiset.map_congr rfl (fun q _ => hG q)
    _ = ((Finset.univ : Finset (Quotient (Equiv.Perm.SameCycle.setoid σ))).val.map ε).map
          (fun O => O.orbit.ncard) := by rw [Multiset.map_map]; rfl
    _ = (Finset.univ : Finset (MulAction.orbitRel.Quotient f.Gal
          (f.rootSet f.SplittingField))).val.map (fun O => O.orbit.ncard) := by rw [hmap]
    _ = (Finset.univ : Finset (MulAction.orbitRel.Quotient f.Gal
          (f.rootSet f.SplittingField))).val.map (fun O => (e O).1.natDegree) :=
        Multiset.map_congr rfl (fun O _ => ((he O).1).symm)
    _ = ((Finset.univ : Finset (MulAction.orbitRel.Quotient f.Gal
          (f.rootSet f.SplittingField))).val.map e).map (fun g => g.1.natDegree) := by
        rw [Multiset.map_map]; rfl
    _ = ((normalizedFactors f).attach.map Subtype.val).map natDegree := by
        rw [hattach, Multiset.map_map]; rfl
    _ = (normalizedFactors f).map natDegree := by rw [Multiset.attach_map_val]

end Orbits

/-- **Remark 8.24** (named statement): the analogue of Theorem 8.23 for a real prime. If $K$ has a real place $v$ and
$f \in K[X]$ is separable of degree $n$ and factors over $\mathbb R$ (via $v$) with exactly $j$ irreducible quadratic
factors (the others linear), then the Galois group of $f$ contains a product of $j$ disjoint transpositions. -/
@[kb "milne2020ant" "v3.08, Rem. 8.24, p. 145"]
structure Remark8_24 : Prop where
  exists_perm : ∀ (K : Type) [Field K] [NumberField K] (v : InfinitePlace K) (hv : v.IsReal) (f : K[X])
    (_ : f.Separable),
    ∃ σ : f.Gal, (galPerm f σ).partition.parts =
      (normalizedFactors (f.map (v.embedding_of_isReal hv))).map natDegree

/-! ## Lemma 8.26, Examples 8.25 and 8.27 -/

/-- **Lemma 8.26** (proved): a transitive subgroup $H$ of $S_n$ containing an $(n-1)$-cycle and a transposition is
$S_n$. The $(n-1)$-cycle is stated as a permutation of cycle type $(n-1, 1)$ (fixed points included), which also
covers the degenerate case $n = 2$. -/
@[kb "milne2020ant" "v3.08, Lem. 8.26, p. 146"]
theorem lemma_8_26 {α : Type*} [Fintype α] [DecidableEq α] (H : Subgroup (Equiv.Perm α))
    (htrans : MulAction.IsPretransitive H α)
    (hcyc : ∃ σ ∈ H, σ.partition.parts = {Fintype.card α - 1, 1})
    (hswap : ∃ τ ∈ H, τ.IsSwap) : H = ⊤ :=
  eq_top_of_transitive_of_cycleType_of_isSwap H htrans hcyc hswap

-- Remark 8.28 (p. 146): a subgroup of S_p (p prime) containing an element of order p and a transposition is S_p.
attribute [kb "milne2020ant" "v3.08, Rem. 8.28, p. 146"] Equiv.Perm.closure_prime_cycle_swap


end

end NumberFieldKB.MilneANT
