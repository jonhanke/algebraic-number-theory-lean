import NumberFieldKB.WeilBNT.FunctionField.ConstantExtension
import NumberFieldKB.WeilBNT.FunctionField.SplitPrimes
import NumberFieldKB.WeilBNT.FunctionField.Schmidt
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# Places in the constant field extension (Weil III.§1 Prop. 1, III.§4 Thm. 4 Cor. 1; VII.§5 Cor. 5)

Let $\mathbb F_q$ be the field of constants of $k$, $n\ge1$ dividing every $\deg v$, and $k'=k\mathbb F_{q^n}=k[X]/(f)$
(`ConstExt`). For a separating $x$ and the model $A=A_x$, the integral closure $B$ of $A$ in $k'$ is a Dedekind
model of $k'$; since $f$ splits into distinct linear factors modulo every prime of $A$, every prime of $A$ splits
completely in $B$ (`primesOver_split`). Hence:

* **`exists_over`**: the restriction of a place $w$ of $k'$ to $k$ is a (normalized) place of $k$;
* **`card_over`**: each place of $k$ has exactly $n$ places of $k'$ above it, **`degree_eq_of_over`**: of the same
  degree over $\mathbb F_q$;
* **`weilSchmidtInput`**: the input `WeilSchmidtInput` of `Schmidt.lean` holds.
-/

open scoped Polynomial WithZero
open Polynomial IsDedekindDomain

noncomputable section

namespace NumberFieldKB.WeilBNT.FF

universe u v

variable {Fq : Type u} {k : Type v} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

section Ext

variable (f : Fq[X]) [Fact (Irreducible (f.map (algebraMap Fq k)))] [hmf : Fact f.Monic]
  [hsf : Fact f.Separable]

local notation "k'" => ConstExt k f

instance instFDConstExt : FiniteDimensional k k' := finiteDimensional_constExt f hmf.out

instance instSepConstExt : Algebra.IsSeparable k k' := isSeparable_constExt f hmf.out hsf.out

instance instFFConstExt : FunctionField Fq k' := functionField_constExt f hmf.out

/-- $w$ lies over $v$: $w$ restricts to $v$ on $k$. -/
def Over (w : Place Fq k') (v : Place Fq k) : Prop :=
  ∀ a : k, w.valuation (algebraMap k k' a) = v.valuation a

theorem over_unique {w : Place Fq k'} {v v' : Place Fq k} (h : Over f w v) (h' : Over f w v') : v = v' :=
  Place.ext (Valuation.ext fun a => (h a).symm.trans (h' a))

/-! ### A chart: the model $A=A_c$ of a separating element and its integral closure $B$ in $k'$ -/

section Chart

variable (c : SeparatingElement Fq k)

local notation "A" => c.modelRing

example : IsScalarTower A k k' := inferInstance

local notation "B" => integralClosure A k'

instance instDedekindB : IsDedekindDomain B :=
  IsIntegralClosure.isDedekindDomain A k k' B

instance instFracB : IsFractionRing B k' :=
  IsIntegralClosure.isFractionRing_of_finite_extension A k k' B

instance instFiniteB : Module.Finite A B :=
  IsIntegralClosure.finite A k k' B

instance instTorsionFreeB : Module.IsTorsionFree A B := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r b hrb => ?_
  have h1 : algebraMap A k' r * (b : k') = 0 := by
    have := congrArg Subtype.val hrb
    rwa [Subalgebra.coe_smul, Algebra.smul_def] at this
  rcases mul_eq_zero.mp h1 with h | h
  · left
    have h2 : algebraMap k k' (algebraMap A k r) = 0 := by
      rw [← IsScalarTower.algebraMap_apply]; exact h
    have h3 := (algebraMap k k').injective (h2.trans (map_zero _).symm)
    exact (IsFractionRing.injective A k) (h3.trans (map_zero _).symm)
  · exact Or.inr (Subtype.ext h)

theorem finrank_B : Module.finrank A B = f.natDegree := by
  rw [← IsFractionRing.finrank_eq A k B k', finrank_constExt f hmf.out]

/-- $\mathbb F_q\to A$. -/
instance instAlgFqModel : Algebra Fq A :=
  ((algebraMap Fq k).codRestrict c.modelRing c.algebraMap_mem_modelRing).toAlgebra

instance instTowerFqModel : IsScalarTower Fq A k := IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- A valuation of $k$, at most $1$ on $\mathbb F_q$ and on $c$, is at most $1$ on the model $A_c$. -/
theorem le_one_on_model {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (u : Valuation k Γ)
    (hFq : ∀ a : Fq, u (algebraMap Fq k a) ≤ 1) (hx : u c.x ≤ 1) (a : A) : u (a : k) ≤ 1 := by
  let g : Fq →+* u.integer :=
    { toFun := fun a => ⟨algebraMap Fq k a, hFq a⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let φ : Fq[X] →+* u.integer := Polynomial.eval₂RingHom g ⟨c.x, hx⟩
  have hφ : (algebraMap u.integer k).comp φ = (Polynomial.aeval c.x).toRingHom := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [φ, g]; rfl
    · simp [φ]; rfl
  have ha : @IsIntegral Fq[X] k _ _ c.polyAlgebra (a : k) := a.2
  obtain ⟨p, hp, hpa⟩ := ha
  have hint : IsIntegral u.integer (a : k) := by
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map, hφ]
    exact hpa
  exact (Valuation.integer.integers u).mem_of_integral hint

/-- A place $w$ of $k'$ with $w(c)\le1$ is at most $1$ on $B$. -/
theorem le_one_on_B (w : Place Fq k') (hw : w.valuation (algebraMap k k' c.x) ≤ 1) (b : B) :
    w.valuation (algebraMap B k' b) ≤ 1 := by
  let u : Valuation k ℤᵐ⁰ := w.valuation.comap (algebraMap k k')
  have hA : ∀ a : A, algebraMap A k' a ∈ w.integers := by
    intro a
    rw [Place.mem_integers_iff, IsScalarTower.algebraMap_apply A k k']
    refine le_one_on_model c u (fun a => ?_) hw a
    show w.valuation (algebraMap k k' (algebraMap Fq k a)) ≤ 1
    rw [← IsScalarTower.algebraMap_apply]
    exact (Place.mem_integers_iff w).1 (w.algebraMap_mem_integers a)
  exact (Place.mem_integers_of_isIntegral w hA b.2)

/-- The root $\theta$ of $f$ in $k'$, as an element of $B$. -/
def thetaB : B :=
  ⟨AdjoinRoot.root (f.map (algebraMap Fq k)), ⟨f.map (algebraMap Fq A), hmf.out.map _, by
    rw [← Polynomial.aeval_def, Polynomial.aeval_map_algebraMap, ← Polynomial.aeval_map_algebraMap k,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]⟩⟩

theorem aeval_thetaB : aeval (thetaB f c) (f.map (algebraMap Fq A)) = 0 := by
  apply Subtype.ext
  rw [← Subalgebra.aeval_coe, Subalgebra.coe_zero]
  show aeval (AdjoinRoot.root (f.map (algebraMap Fq k))) _ = 0
  rw [Polynomial.aeval_map_algebraMap, ← Polynomial.aeval_map_algebraMap k, AdjoinRoot.aeval_eq,
    AdjoinRoot.mk_self]

theorem dvd_of_aeval_thetaB (p : A[X]) (hp : aeval (thetaB f c) p = 0) : f.map (algebraMap Fq A) ∣ p := by
  have hm : (f.map (algebraMap Fq A)).Monic := hmf.out.map _
  have h1 : aeval (AdjoinRoot.root (f.map (algebraMap Fq k))) p = 0 := by
    have := congrArg Subtype.val hp
    rw [← Subalgebra.aeval_coe] at this
    exact this
  rw [← Polynomial.aeval_map_algebraMap k, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h1
  rw [← modByMonic_eq_zero_iff_dvd hm]
  apply Polynomial.map_injective (algebraMap A k) (IsFractionRing.injective A k)
  rw [Polynomial.map_modByMonic _ hm, Polynomial.map_zero, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq, modByMonic_eq_zero_iff_dvd (hmf.out.map _)]
  exact h1

/-- **Complete splitting at a prime of $A$** of degree divisible by $\deg f$. -/
theorem split_at (P : HeightOneSpectrum A)
    (hdiv : f.natDegree ∣ (Place.ofHeightOneSpectrum (Fq := Fq) (k := k) A P).degree)
    (hsplit : ∀ (L : Type v) [Field L] [Algebra Fq L] [Finite L], f.natDegree ∣ Module.finrank Fq L →
      (f.map (algebraMap Fq L)).Splits) :
    Fintype.card (P.asIdeal.primesOver B) = Module.finrank A B ∧
      ∀ Q : P.asIdeal.primesOver B, Q.1.ramificationIdx A = 1 ∧ Q.1.inertiaDeg A = 1 := by
  classical
  haveI hPmax : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
  letI : Field (A ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  haveI : Finite (A ⧸ P.asIdeal) := Place.finite_quotient_model c P
  have hfr := finrank_B f c
  have hm : (f.map (algebraMap Fq A)).Monic := hmf.out.map _
  -- the residue field has degree deg v over Fq
  have hcard : Module.finrank Fq (A ⧸ P.asIdeal) = (Place.ofHeightOneSpectrum (Fq := Fq) (k := k) A P).degree := by
    obtain ⟨g, hg⟩ := Place.exists_bijective_residue_ofHeightOneSpectrum (Fq := Fq) (k := k) A P
    have h1 : Nat.card (A ⧸ P.asIdeal) = Nat.card Fq ^ (Place.ofHeightOneSpectrum (Fq := Fq) (k := k) A P).degree := by
      rw [← Place.card_residueField]
      exact Nat.card_congr (Equiv.ofBijective g hg)
    have h2 := natCard_eq_pow_finrank (Fq := Fq) (A ⧸ P.asIdeal)
    have hq2 : 2 ≤ Nat.card Fq := Finite.one_lt_card
    exact Nat.pow_right_injective hq2 (h2.symm.trans h1)
  have hspl := hsplit (A ⧸ P.asIdeal) (by rw [hcard]; exact hdiv)
  set g := f.map (algebraMap Fq (A ⧸ P.asIdeal)) with hgdef
  have hgdeg : g.natDegree = f.natDegree := hmf.out.natDegree_map _
  have hcardroots : g.roots.card = f.natDegree := by
    rw [← hgdeg]; exact Polynomial.splits_iff_card_roots.mp hspl
  have hnodup : g.roots.Nodup := Polynomial.nodup_roots (hsf.out.map)
  set l := g.roots.toList with hl
  have hllen : l.length = Module.finrank A B := by
    rw [hl, Multiset.length_toList, hcardroots, hfr]
  have hlnodup : l.Nodup := by
    rw [← Multiset.coe_nodup, hl, Multiset.coe_toList]; exact hnodup
  let r : Fin (Module.finrank A B) → A := fun i =>
    (Ideal.Quotient.mk_surjective (I := P.asIdeal) (l.get (Fin.cast hllen.symm i))).choose
  have hr_spec : ∀ i, Ideal.Quotient.mk P.asIdeal (r i) = l.get (Fin.cast hllen.symm i) := fun i =>
    (Ideal.Quotient.mk_surjective (I := P.asIdeal) (l.get (Fin.cast hllen.symm i))).choose_spec
  have hmapF : (f.map (algebraMap Fq A)).map (Ideal.Quotient.mk P.asIdeal) = g := by
    rw [Polynomial.map_map]; rfl
  have hg0 : g ≠ 0 := (hmf.out.map _).ne_zero
  refine primesOver_split P.asIdeal P.ne_bot (f.map (algebraMap Fq A)) hm
    (by rw [hmf.out.natDegree_map, hfr]) (thetaB f c) (aeval_thetaB f c) (dvd_of_aeval_thetaB f c) r ?_ ?_
  · intro i
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hmapF,
      hr_spec]
    have hmem : l.get (Fin.cast hllen.symm i) ∈ g.roots := by
      rw [← Multiset.mem_toList, ← hl]; exact List.get_mem _ _
    exact (Polynomial.mem_roots hg0).mp hmem
  · intro i j hij hmem
    apply hij
    have h1 : Ideal.Quotient.mk P.asIdeal (r i) = Ideal.Quotient.mk P.asIdeal (r j) := by
      rw [Ideal.Quotient.eq]; exact hmem
    rw [hr_spec, hr_spec] at h1
    have := (List.Nodup.get_inj_iff hlnodup).mp h1
    exact Fin.cast_injective _ this

/-- With $e=1$, the place of a prime $Q$ of $B$ over $P$ restricts to the place of $P$. -/
theorem over_of_liesOver (P : HeightOneSpectrum A) (Q : HeightOneSpectrum B) [Q.asIdeal.LiesOver P.asIdeal]
    (he : Q.asIdeal.ramificationIdx A = 1) :
    Over (k := k) f (Place.ofHeightOneSpectrum B Q) (Place.ofHeightOneSpectrum A P) := by
  intro a
  have := HeightOneSpectrum.valuation_liesOver (K := k) k' P Q a
  rw [he, pow_one] at this
  exact this.symm

theorem liesOver_of_over (P : HeightOneSpectrum A) (Q : HeightOneSpectrum B)
    (h : Over (k := k) f (Place.ofHeightOneSpectrum B Q) (Place.ofHeightOneSpectrum A P)) :
    Q.asIdeal.LiesOver P.asIdeal := by
  constructor
  ext a
  rw [Ideal.under_def, Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := k),
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := k')]
  have h1 := h (algebraMap A k a)
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B k'] at h1
  simp only [Place.ofHeightOneSpectrum_valuation] at h1
  rw [h1]

theorem degree_eq_of_inertiaDeg (P : HeightOneSpectrum A) (Q : HeightOneSpectrum B)
    [Q.asIdeal.LiesOver P.asIdeal] (hf : Q.asIdeal.inertiaDeg A = 1) :
    (Place.ofHeightOneSpectrum (Fq := Fq) (k := ConstExt k f) B Q).degree = (Place.ofHeightOneSpectrum (Fq := Fq) (k := k) A P).degree := by
  haveI : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
  haveI : Q.asIdeal.IsMaximal := Q.isPrime.isMaximal Q.ne_bot
  have h := Ideal.cardQuot_pow_inertiaDeg P.asIdeal Q.asIdeal
  rw [hf, pow_one, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h
  obtain ⟨g₁, hg₁⟩ := Place.exists_bijective_residue_ofHeightOneSpectrum (Fq := Fq) (k := k) A P
  obtain ⟨g₂, hg₂⟩ := Place.exists_bijective_residue_ofHeightOneSpectrum (Fq := Fq) (k := ConstExt k f) B Q
  have h1 := Nat.card_congr (Equiv.ofBijective g₁ hg₁)
  have h2 := Nat.card_congr (Equiv.ofBijective g₂ hg₂)
  rw [Place.card_residueField] at h1 h2
  have hq2 : 2 ≤ Nat.card Fq := Finite.one_lt_card
  rw [← h] at h2
  exact Nat.pow_right_injective hq2 (h2.symm.trans h1)

end Chart

/-! ### All places -/

section Global

variable (hdivAll : ∀ v : Place Fq k, f.natDegree ∣ v.degree)
  (hsplit : ∀ (L : Type v) [Field L] [Algebra Fq L] [Finite L], f.natDegree ∣ Module.finrank Fq L →
    (f.map (algebraMap Fq L)).Splits)

theorem exists_chart_k' (s : SeparatingElement Fq k) (w : Place Fq k') :
    ∃ c : SeparatingElement Fq k, w.valuation (algebraMap k k' c.x) ≤ 1 := by
  rcases le_total (w.valuation (algebraMap k k' s.x)) 1 with h | h
  · exact ⟨s, h⟩
  · refine ⟨s.inv, ?_⟩
    rw [SeparatingElement.inv_x, map_inv₀, map_inv₀]
    exact inv_le_one_of_one_le₀ h

theorem exists_chart_k (s : SeparatingElement Fq k) (v : Place Fq k) :
    ∃ c : SeparatingElement Fq k, v.valuation c.x ≤ 1 := by
  rcases le_total (v.valuation s.x) 1 with h | h
  · exact ⟨s, h⟩
  · refine ⟨s.inv, ?_⟩
    rw [SeparatingElement.inv_x, map_inv₀]
    exact inv_le_one_of_one_le₀ h

theorem ne_bot_of_mem_primesOver (c : SeparatingElement Fq k) (P : HeightOneSpectrum c.modelRing)
    (Q : P.asIdeal.primesOver (integralClosure c.modelRing k')) : Q.1 ≠ ⊥ := by
  intro h
  have h1 : P.asIdeal = Q.1.under c.modelRing := Q.2.2.over
  rw [h, Ideal.under_bot] at h1
  exact P.ne_bot h1

include hdivAll hsplit in
/-- **Restriction**: every place of $k'$ lies over a place of $k$ (unramified, so the restriction is normalized). -/
theorem exists_over (w : Place Fq k') : ∃ v : Place Fq k, Over (k := k) f w v := by
  obtain ⟨s⟩ := weil_III_2_lemma1 (Fq := Fq) (k := k)
  obtain ⟨c, hc⟩ := exists_chart_k' f s w
  obtain ⟨Q, rfl⟩ := Place.exists_eq_ofHeightOneSpectrum (integralClosure c.modelRing k') w
    (le_one_on_B f c w hc)
  let P : HeightOneSpectrum c.modelRing := Q.under c.modelRing
  haveI : Q.asIdeal.LiesOver P.asIdeal := ⟨rfl⟩
  have hspl := split_at f c P (hdivAll _) hsplit
  have he := (hspl.2 ⟨Q.asIdeal, Q.isPrime, inferInstance⟩).1
  exact ⟨_, over_of_liesOver f c P Q he⟩

theorem eq_ofHeightOneSpectrum_of_over (c : SeparatingElement Fq k) (P : HeightOneSpectrum c.modelRing)
    (w : Place Fq k') (hw : Over (k := k) f w (Place.ofHeightOneSpectrum (Fq := Fq) (k := k) c.modelRing P)) :
    ∃ Q : HeightOneSpectrum (integralClosure c.modelRing k'), Q.asIdeal.LiesOver P.asIdeal ∧
      w = Place.ofHeightOneSpectrum (integralClosure c.modelRing k') Q := by
  have hx : w.valuation (algebraMap k k' c.x) ≤ 1 := by
    rw [hw c.x]
    exact Place.valuation_ofHeightOneSpectrum_algebraMap_le_one c.modelRing P ⟨c.x, c.x_mem_modelRing⟩
  obtain ⟨Q, rfl⟩ := Place.exists_eq_ofHeightOneSpectrum (integralClosure c.modelRing k') w
    (le_one_on_B f c w hx)
  exact ⟨Q, liesOver_of_over f c P Q hw, rfl⟩

include hdivAll hsplit in
/-- **Each place of $k$ has exactly $n$ places of $k'$ above it.** -/
theorem card_over (v : Place Fq k) :
    Nat.card {w : Place Fq k' // Over (k := k) f w v} = f.natDegree := by
  classical
  obtain ⟨s⟩ := weil_III_2_lemma1 (Fq := Fq) (k := k)
  obtain ⟨c, hc⟩ := exists_chart_k s v
  obtain ⟨P, rfl⟩ := Place.exists_eq_ofHeightOneSpectrum c.modelRing v
    (fun a => c.valuation_le_one_of_valuation_x_le_one v hc a)
  have hspl := split_at f c P (hdivAll _) hsplit
  let B := integralClosure c.modelRing k'
  let φ : P.asIdeal.primesOver B → {w : Place Fq k' // Over (k := k) f w
      (Place.ofHeightOneSpectrum (Fq := Fq) (k := k) c.modelRing P)} := fun Q =>
    haveI : (⟨Q.1, Q.2.1, ne_bot_of_mem_primesOver f c P Q⟩ : HeightOneSpectrum B).asIdeal.LiesOver
      P.asIdeal := Q.2.2
    ⟨Place.ofHeightOneSpectrum B ⟨Q.1, Q.2.1, ne_bot_of_mem_primesOver f c P Q⟩,
      over_of_liesOver f c P _ (hspl.2 Q).1⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro Q₁ Q₂ h
      have := Place.ofHeightOneSpectrum_injective (Fq := Fq) (k := ConstExt k f) B (congrArg Subtype.val h)
      exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal this)
    · rintro ⟨w, hw⟩
      obtain ⟨Q, hQ, rfl⟩ := eq_ofHeightOneSpectrum_of_over f c P w hw
      exact ⟨⟨Q.asIdeal, Q.isPrime, hQ⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card, hspl.1, finrank_B]

include hdivAll hsplit in
/-- **The places above $v$ have the same degree as $v$.** -/
theorem degree_eq_of_over {w : Place Fq k'} {v : Place Fq k} (h : Over (k := k) f w v) :
    w.degree = v.degree := by
  obtain ⟨s⟩ := weil_III_2_lemma1 (Fq := Fq) (k := k)
  obtain ⟨c, hc⟩ := exists_chart_k s v
  obtain ⟨P, rfl⟩ := Place.exists_eq_ofHeightOneSpectrum c.modelRing v
    (fun a => c.valuation_le_one_of_valuation_x_le_one v hc a)
  obtain ⟨Q, hQ, rfl⟩ := eq_ofHeightOneSpectrum_of_over f c P w h
  have hspl := split_at f c P (hdivAll _) hsplit
  exact degree_eq_of_inertiaDeg f c P Q (hspl.2 ⟨Q.asIdeal, Q.isPrime, hQ⟩).2

end Global

end Ext

/-- **The constant field extension splits every place** (Weil III.§1 Prop. 1, III.§4 Thm. 4 Cor. 1 and I.§1 Thm. 2,
as used in VII.§5 Cor. 5): the named input of `Schmidt.lean` holds. -/
theorem weilSchmidtInput : WeilSchmidtInput Fq k := by
  intro hc n hn hdiv
  obtain ⟨f, hm, hirr, hdeg, hsep, hsplit⟩ := exists_constantPoly.{u, v} (Fq := Fq) n hn
  haveI : Fact (Irreducible (f.map (algebraMap Fq k))) := ⟨irreducible_map_of_isConstantField hc hm hirr⟩
  haveI : Fact f.Monic := ⟨hm⟩
  haveI : Fact f.Separable := ⟨hsep⟩
  have hdivAll : ∀ v : Place Fq k, f.natDegree ∣ v.degree := by rw [hdeg]; exact hdiv
  have hsplit' : ∀ (L : Type v) [Field L] [Algebra Fq L] [Finite L], f.natDegree ∣ Module.finrank Fq L →
      (f.map (algebraMap Fq L)).Splits := by
    intro L _ _ _ h; rw [hdeg] at h; exact hsplit L h
  let res : Place Fq (ConstExt k f) → Place Fq k := fun w => (exists_over f hdivAll hsplit' w).choose
  have hres : ∀ w, Over (k := k) f w (res w) := fun w => (exists_over f hdivAll hsplit' w).choose_spec
  have hfib : ∀ v : Place Fq k, Nonempty ({w // res w = v} ≃ Fin n) := by
    intro v
    have h1 : {w // res w = v} ≃ {w // Over (k := k) f w v} :=
      Equiv.subtypeEquivRight fun w => ⟨fun h => h ▸ hres w, fun h => over_unique f (hres w) h⟩
    have h2 := card_over f hdivAll hsplit' v
    rw [hdeg] at h2
    haveI : Finite {w // Over (k := k) f w v} := Nat.finite_of_card_ne_zero (by omega)
    exact ⟨h1.trans ((Finite.equivFin _).trans (finCongr h2))⟩
  let e : Place Fq (ConstExt k f) ≃ Place Fq k × Fin n :=
    (Equiv.sigmaFiberEquiv res).symm.trans
      ((Equiv.sigmaCongrRight fun v => (hfib v).some).trans (Equiv.sigmaEquivProd _ _))
  refine ⟨ConstExt k f, inferInstance, inferInstance, inferInstance, inferInstance, instFFConstExt f, e,
    fun w => ?_⟩
  have : (e w).1 = res w := rfl
  rw [this]
  exact (degree_eq_of_over f hdivAll hsplit' (hres w)).symm

/-- **F. K. Schmidt's theorem** (Weil VII.§5, Cor. 5, $P=\emptyset$), unconditional: if $\mathbb F_q$ is the field of
constants, $k$ has a divisor of degree $1$. -/
@[kb "weil1973bnt" "Ch. VII, §5, Cor. 5 (p. 126), P empty, function fields"]
theorem weil_VII_5_cor5_ff (hc : IsConstantField Fq k) : ∃ a : Divisor Fq k, Divisor.deg a = 1 :=
  weil_VII_5_cor5 hc weilSchmidtInput

end NumberFieldKB.WeilBNT.FF
