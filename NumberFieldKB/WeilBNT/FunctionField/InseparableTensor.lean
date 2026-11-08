import NumberFieldKB.WeilBNT.FunctionField.InseparableLocal
import NumberFieldKB.WeilBNT.FunctionField.Separating
import NumberFieldKB.WeilBNT.PFieldRamified
import NumberFieldKB.WeilBNT.GaloisCompletions
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.SeparableDegree
import QuadFormsKB.Citation

/-!
# Weil III.§4, text p.57: Theorem 4 for purely inseparable $k'$ (function fields)

$k$ is a global function field over $\mathbb F_q$, $p=\operatorname{char}\mathbb F_q$, and $k'/k$ a finite purely
inseparable extension (itself a function field over $\mathbb F_q$), of exponent $e$ (Mathlib's
`IsPurelyInseparable.exponent`: the least $e$ with $a^{p^e}\in k$ for all $a\in k'$).

* **`finrank_eq_and_surjective_frobDown`**: $[k':k]=p^e$, and $k'^{p^e}=k$: the map
  $\varphi:a\mapsto a^{p^e}$, $k'\to k$ (Mathlib's `IsPurelyInseparable.iterateFrobenius`), is a ring isomorphism.
  Proof: $[k':k'^{p^e}]\le p^e$ because $k'=k'^{p^e}(x)$ for a separating element $x$ (Weil III.§2 Lemma 1,
  `weil_III_2_lemma1`), and $[k':k]\ge p^e$ (an element of exact exponent $e$ has degree $p^e$), so the tower
  $k'^{p^e}\subseteq k\subseteq k'$ collapses.
* **`placeAbove v`**: the place $w$ of $k'$ with $w(a)=v(a^{p^e})$; $w(c)=v(c)^{[k':k]}$ on $k$ (totally ramified,
  `placeAbove_algebraMap`), and it is the only place of $k'$ above $v$ (`eq_placeAbove`).
* **`complEquiv v`**: $\varphi$ extends to an isomorphism of complete fields $k'_w\cong k_v$.
* **`weil_III_4_text57`** (Weil III.§4, text p.57, function fields, purely inseparable $k'$): there is exactly one
  place $w$ of $k'$ above $v$, and $k_v\otimes_kk'\cong k'_w$ by $c\otimes a\mapsto j(c)\lambda_w(a)$, $j:k_v\to k'_w$
  the continuous extension of $k\to k'$. Proof: under $k'_w\cong k_v$, $j$ becomes $c\mapsto c^{p^e}$, so
  $[k'_w:k_v]=[k_v:k_v^{p^e}]=p^e$ (Weil I.§4 Cor. 1 of Prop. 4, `weil_I_4_cor1_prop4`, and induction); the image of
  $k_v\otimes_kk'$ contains $k_v^{p^e}$ and a prime element $\pi$, which generates $k_v$ over $k_v^{p^e}$
  ($X^{p^e}-\pi^{p^e}$ is irreducible: `irreducible_X_pow_char_pow_sub_C`); both sides have dimension $p^e$.

Weil states (text p.57) that Thm. 4 "remains valid" for inseparable $k'$ and proves it in Chap. VIII. This file
proves the purely inseparable case for function fields. A general finite $k'/k$ in characteristic $p$ mixes separable
and purely inseparable steps; the separable steps need Thm. 4 for separable extensions of function fields, which the
repository has only for constant field extensions (`PlaceSplitting.lean`); Thm. 4 itself is formalized for number
fields (`weil_III_4_thm4`). Weil writes $k'\otimes_kk_v$; here the factors are in the order $k_v\otimes_kk'$ (so that
$k_v$ acts on the left). The hypothesis that $k'$ is a function field over $\mathbb F_q$ (`FunctionField Fq k'` with
its scalar tower) is implied by $[k':k]<\infty$ and is assumed only to have the type class instances.

Generic lemmas (any field of characteristic $p$): `irreducible_X_pow_char_pow_sub_C` ($X^{p^n}-a$ is irreducible
when $a$ is not a $p$-th power; Mathlib has this only for $p\ne2$, `X_pow_sub_C_irreducible_of_prime_pow_of_ne_two`),
`finrank_iterateFrobenius_fieldRange` ($[F:F^p]=p\Rightarrow[F:F^{p^n}]=p^n$),
`finrank_iterateFrobenius_fieldRange_le` ($K/\mathbb F_q(x)$ separable $\Rightarrow[K:K^{p^n}]\le p^n$).
-/

open Polynomial IntermediateField
open scoped TensorProduct

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace NumberFieldKB.WeilBNT.FF

/-! ### Generic lemmas in characteristic $p$ -/

section Generic

/-- In characteristic $p$, $X^{p^n}-a$ is irreducible when $a$ is not a $p$-th power (all $p$, including $p=2$). -/
theorem irreducible_X_pow_char_pow_sub_C {K : Type*} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (n : ℕ) {a : K} (ha : ∀ b : K, b ^ p ≠ a) : Irreducible (X ^ (p ^ n) - C a) := by
  have : ExpChar K p := ExpChar.prime hp.out
  set f : K[X] := X ^ (p ^ n) - C a with hf
  have hfm : f.Monic := monic_X_pow_sub_C a (pow_pos hp.out.pos n).ne'
  have hf0 : f ≠ 0 := hfm.ne_zero
  have hfdeg : f.natDegree = p ^ n := natDegree_X_pow_sub_C
  have hfu : ¬ IsUnit f := fun h => by
    have := natDegree_eq_zero_of_isUnit h
    rw [hfdeg] at this
    exact (pow_pos hp.out.pos n).ne' this
  obtain ⟨g0, hg0i, hg0f⟩ := WfDvdMonoid.exists_irreducible_factor hfu hf0
  set g := g0 * C (g0.leadingCoeff)⁻¹ with hg
  have hg0 : g0 ≠ 0 := hg0i.ne_zero
  have hgm : g.Monic := monic_mul_leadingCoeff_inv hg0
  have hgi : Irreducible g := (irreducible_mul_isUnit (isUnit_C.2 (inv_ne_zero
    (leadingCoeff_ne_zero.2 hg0)).isUnit)).2 hg0i
  have hgf : g ∣ f := by
    obtain ⟨r, hr⟩ := hg0f
    exact ⟨C g0.leadingCoeff * r, by
      rw [hr, hg, mul_assoc, ← mul_assoc (C _), ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hg0),
        C_1, one_mul]⟩
  have hsep : g.natSepDegree = 1 := by
    have h1 : g.natSepDegree ≤ 1 := (natSepDegree_le_of_dvd g f hgf hf0).trans
      (natSepDegree_X_pow_char_pow_sub_C p n a).le
    have h2 : g.natSepDegree ≠ 0 := (natSepDegree_ne_zero_iff _).2 (Irreducible.natDegree_pos hgi).ne'
    omega
  obtain ⟨m, y, -, hgxy⟩ := hgm.eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible p hgi hsep
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) g
    (Irreducible.degree_pos hgi).ne'
  have hby : b ^ (p ^ m) = algebraMap K (AlgebraicClosure K) y := by
    rw [hgxy] at hb
    simpa [sub_eq_zero] using hb
  have hba : b ^ (p ^ n) = algebraMap K (AlgebraicClosure K) a := by
    have h2 : aeval b f = 0 := by
      obtain ⟨r, hr⟩ := hgf
      rw [hr, map_mul, hb, zero_mul]
    simpa [hf, sub_eq_zero] using h2
  have hmn : n ≤ m := by
    by_contra hlt
    push Not at hlt
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    apply ha (y ^ (p ^ d))
    apply (algebraMap K (AlgebraicClosure K)).injective
    rw [← hba, map_pow, map_pow, ← hby, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hdeg : f.natDegree ≤ g.natDegree := by
    rw [hfdeg, hgxy, natDegree_X_pow_sub_C]
    exact Nat.pow_le_pow_right hp.out.pos hmn
  have hfg := eq_of_monic_of_dvd_of_natDegree_le hgm hfm hgf hdeg
  rw [hfg]
  exact hgi

theorem fieldRange_iterateFrobenius_succ {F : Type*} [Field F] (p : ℕ) [ExpChar F p] (i : ℕ) :
    (iterateFrobenius F p (i + 1)).fieldRange =
      (frobenius F p).fieldRange.map (iterateFrobenius F p i) := by
  ext x
  simp only [RingHom.mem_fieldRange, Subfield.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y ^ p, ⟨y, rfl⟩, by simp [iterateFrobenius_def, ← pow_mul, pow_succ, mul_comm]⟩
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, by simp [iterateFrobenius_def, frobenius_def, ← pow_mul, pow_succ, mul_comm]⟩

theorem fieldRange_iterateFrobenius_eq_map {F : Type*} [Field F] (p : ℕ) [ExpChar F p] (i : ℕ) :
    (iterateFrobenius F p i).fieldRange = (⊤ : Subfield F).map (iterateFrobenius F p i) := by
  ext x
  simp [RingHom.mem_fieldRange, Subfield.mem_map]

/-- $[F:F^{p^n}]=p^n$ when $[F:F^p]=p$ (transport $[F:F^p]=p$ by $x\mapsto x^{p^i}$ and use the tower law). -/
theorem finrank_iterateFrobenius_fieldRange {F : Type*} [Field F] (p : ℕ) [ExpChar F p]
    (hdeg : Module.finrank (frobenius F p).fieldRange F = p) (n : ℕ) :
    Module.finrank (iterateFrobenius F p n).fieldRange F = p ^ n := by
  rw [← Subfield.relfinrank_top_right]
  induction n with
  | zero =>
    have : (iterateFrobenius F p 0).fieldRange = ⊤ := by
      rw [eq_top_iff]; intro x _; exact ⟨x, by simp [iterateFrobenius_def]⟩
    rw [this, Subfield.relfinrank_self, pow_zero]
  | succ m ih =>
    have hle1 : (iterateFrobenius F p (m + 1)).fieldRange ≤ (iterateFrobenius F p m).fieldRange := by
      rintro _ ⟨y, rfl⟩
      exact ⟨y ^ p, by simp [iterateFrobenius_def, ← pow_mul, pow_succ, mul_comm]⟩
    have h1 : Subfield.relfinrank (iterateFrobenius F p (m + 1)).fieldRange
        (iterateFrobenius F p m).fieldRange = p := by
      rw [fieldRange_iterateFrobenius_succ, fieldRange_iterateFrobenius_eq_map p m,
        Subfield.relfinrank_map_map, Subfield.relfinrank_top_right, hdeg]
    rw [← Subfield.relfinrank_mul_relfinrank hle1 le_top, h1, ih, pow_succ, mul_comm]

/-- If $K/\mathbb F_q(x)$ is separable ($\mathbb F_q$ finite, characteristic $p$), then $K=K^{p^n}(x)$ (the extension
$K/K^{p^n}(x)$ is separable and purely inseparable), so $[K:K^{p^n}]\le p^n$. -/
theorem finrank_iterateFrobenius_fieldRange_le {Fq K : Type*} [Field Fq] [Finite Fq] [Field K] [Algebra Fq K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (x : K) (hsep : Algebra.IsSeparable Fq⟮x⟯ K) (n : ℕ) :
    FiniteDimensional (iterateFrobenius K p n).fieldRange K ∧
      Module.finrank (iterateFrobenius K p n).fieldRange K ≤ p ^ n := by
  have : ExpChar K p := ExpChar.prime (Fact.out)
  have : CharP Fq p := (Algebra.charP_iff Fq K p).2 ‹_›
  have : ExpChar Fq p := ExpChar.prime (Fact.out)
  set R := (iterateFrobenius K p n).fieldRange with hR
  have hpow : ∀ a : K, a ^ (p ^ n) ∈ R := fun a => ⟨a, by simp [iterateFrobenius_def]⟩
  set E : IntermediateField R K := R⟮x⟯ with hE
  set f : R[X] := X ^ (p ^ n) - C ⟨x ^ (p ^ n), hpow x⟩ with hf
  have hfm : f.Monic := monic_X_pow_sub_C _ (pow_pos (Fact.out : p.Prime).pos n).ne'
  have hfx : aeval x f = 0 := by simp [hf]; exact sub_self _
  have hint : IsIntegral R x := ⟨f, hfm, by rwa [← aeval_def]⟩
  have hle : (Fq⟮x⟯).toSubfield ≤ E.toSubfield := by
    rw [adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨c, rfl⟩ | h)
    · obtain ⟨c', rfl⟩ := (bijective_iterateFrobenius Fq p n).2 c
      have : algebraMap Fq K (iterateFrobenius Fq p n c') = algebraMap Fq K c' ^ (p ^ n) := by
        simp [iterateFrobenius_def]
      rw [this]
      exact E.algebraMap_mem ⟨_, hpow _⟩
    · rw [Set.mem_singleton_iff.1 h]
      exact mem_adjoin_simple_self R x
  let _ : Algebra Fq⟮x⟯ E := (Subfield.inclusion hle).toAlgebra
  have : IsScalarTower Fq⟮x⟯ E K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsSeparable E K := Algebra.isSeparable_tower_top_of_isSeparable Fq⟮x⟯ E K
  have : IsPurelyInseparable E K := by
    rw [isPurelyInseparable_iff_pow_mem E p]
    intro a
    exact ⟨n, ⟨_, E.algebraMap_mem ⟨_, hpow a⟩⟩, rfl⟩
  have htop : E = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable E K a
    rw [← hy]; exact y.2
  have hfd : FiniteDimensional R E := adjoin.finiteDimensional hint
  have hfdK : FiniteDimensional R K := by
    rw [htop] at hfd
    exact (topEquiv (F := R) (E := K)).toLinearEquiv.finiteDimensional
  refine ⟨hfdK, ?_⟩
  rw [← finrank_top', ← htop, adjoin.finrank hint]
  have h1 := minpoly.min R x hfm hfx
  have h2 : f.natDegree = p ^ n := natDegree_X_pow_sub_C
  rw [← h2]
  exact natDegree_le_natDegree h1

end Generic

/-! ### The purely inseparable extension $k'/k$ -/

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

theorem charP_ringChar (K : Type*) [Field K] [Algebra Fq K] : CharP K (ringChar Fq) :=
  charP_of_injective_algebraMap (algebraMap Fq K).injective _

theorem fact_ringChar_prime : Fact (ringChar Fq).Prime := ⟨CharP.char_is_prime Fq _⟩

theorem expChar_ringChar (K : Type*) [Field K] [Algebra Fq K] : ExpChar K (ringChar Fq) :=
  haveI := charP_ringChar (Fq := Fq) K
  ExpChar.prime (CharP.char_is_prime Fq _)

section Insep

variable (Fq) {k' : Type*} [Field k'] [Algebra Fq k'] [Algebra (RatFunc Fq) k']
  [IsScalarTower Fq (RatFunc Fq) k'] [FunctionField Fq k'] [Algebra k k'] [FiniteDimensional k k']
  [IsPurelyInseparable k k']

variable (k k') in
/-- $\varphi:k'\to k$, $a\mapsto a^{p^e}$ ($e$ the exponent of $k'/k$). -/
def frobDown : k' →+* k :=
  haveI := expChar_ringChar (Fq := Fq) k
  IsPurelyInseparable.iterateFrobenius k k' (ringChar Fq) (le_refl (IsPurelyInseparable.exponent k k'))

theorem algebraMap_frobDown (a : k') :
    algebraMap k k' (frobDown Fq k k' a) = a ^ ringChar Fq ^ IsPurelyInseparable.exponent k k' := by
  haveI := expChar_ringChar (Fq := Fq) k
  exact IsPurelyInseparable.algebraMap_iterateFrobenius k (ringChar Fq) le_rfl a

theorem frobDown_algebraMap (c : k) :
    frobDown Fq k k' (algebraMap k k' c) = c ^ ringChar Fq ^ IsPurelyInseparable.exponent k k' := by
  haveI := expChar_ringChar (Fq := Fq) k
  exact IsPurelyInseparable.iterateFrobenius_algebraMap k' (ringChar Fq) le_rfl c

/-- **$[k':k]=p^e$ and $k'^{p^e}=k$.** -/
theorem finrank_eq_and_surjective_frobDown :
    Module.finrank k k' = ringChar Fq ^ IsPurelyInseparable.exponent k k' ∧
      Function.Surjective (frobDown Fq k k') := by
  haveI := fact_ringChar_prime (Fq := Fq)
  haveI := charP_ringChar (Fq := Fq) k
  haveI := charP_ringChar (Fq := Fq) k'
  haveI := expChar_ringChar (Fq := Fq) k
  haveI := expChar_ringChar (Fq := Fq) k'
  set p := ringChar Fq with hp
  set e := IsPurelyInseparable.exponent k k' with he
  obtain ⟨s⟩ := weil_III_2_lemma1 (Fq := Fq) (k := k')
  obtain ⟨hfd, hle⟩ := finrank_iterateFrobenius_fieldRange_le (Fq := Fq) p s.x s.isSeparable e
  set R' := (iterateFrobenius k' p e).fieldRange with hR'
  set Kk := (algebraMap k k').fieldRange with hKk
  have hRK : R' ≤ Kk := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := IsPurelyInseparable.exponent_def' k p a
    exact ⟨c, by rw [hc]; simp [iterateFrobenius_def, he]⟩
  have hKtop : Subfield.relfinrank Kk ⊤ = Module.finrank k k' := by
    rw [Subfield.relfinrank_top_right]
    exact (Algebra.finrank_eq_of_equiv_equiv ((algebraMap k k').rangeRestrictFieldEquiv)
      (RingEquiv.refl k') (by ext; rfl)).symm
  have hlow : p ^ e ≤ Module.finrank k k' := by
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · rw [h0, pow_zero]; exact Module.finrank_pos
    · obtain ⟨a, ha⟩ := IsPurelyInseparable.exponent_min' p (Nat.sub_lt hpos one_pos)
      have hel : IsPurelyInseparable.elemExponent k a = e := by
        refine le_antisymm (IsPurelyInseparable.elemExponent_le_exponent k a) ?_
        by_contra hlt
        push Not at hlt
        apply ha
        obtain ⟨c, hc⟩ := IsPurelyInseparable.elemExponent_def' k p a
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.le_sub_one_of_lt hlt)
        refine ⟨c ^ p ^ d, ?_⟩
        rw [map_pow, hc, ← pow_mul, ← pow_add, hd]
      rw [← hel, ← IsPurelyInseparable.minpoly_natDegree_eq' k p a]
      exact minpoly.natDegree_le a
  have htower := Subfield.relfinrank_mul_relfinrank hRK (le_top : Kk ≤ ⊤)
  rw [hKtop, Subfield.relfinrank_top_right] at htower
  have hpos : 0 < Module.finrank R' k' := Module.finrank_pos
  have hfpos : 0 < Module.finrank k k' := Module.finrank_pos
  have h1 : Subfield.relfinrank R' Kk = 1 := by
    rcases Nat.lt_or_ge (Subfield.relfinrank R' Kk) 2 with h | h
    · interval_cases hr : Subfield.relfinrank R' Kk
      · rw [zero_mul] at htower; omega
      · rfl
    · nlinarith
  rw [h1, one_mul] at htower
  refine ⟨le_antisymm (htower ▸ hle) hlow, fun c => ?_⟩
  have hc : algebraMap k k' c ∈ R' := (Subfield.relfinrank_eq_one_iff.1 h1) ⟨c, rfl⟩
  obtain ⟨b, hb⟩ := hc
  refine ⟨b, (algebraMap k k').injective ?_⟩
  rw [algebraMap_frobDown, ← hb]
  simp [iterateFrobenius_def, he, hp]

/-- The place $w$ of $k'$ above $v$: $w(a)=v(a^{p^e})$. -/
def placeAbove (v : Place Fq k) : Place Fq k' :=
  Place.mk' (v.valuation.comap (frobDown Fq k k')) fun g => by
    obtain ⟨c, hc⟩ := v.valuation_surjective g
    obtain ⟨b, rfl⟩ := (finrank_eq_and_surjective_frobDown Fq (k := k) (k' := k')).2 c
    exact ⟨b, hc⟩

theorem placeAbove_apply (v : Place Fq k) (a : k') :
    (placeAbove Fq (k' := k') v).valuation a = v.valuation (frobDown Fq k k' a) := rfl

/-- $w(c)=v(c)^{[k':k]}$ for $c\in k$: $w$ is totally ramified over $v$, $e(w/v)=[k':k]$. -/
theorem placeAbove_algebraMap (v : Place Fq k) (c : k) :
    (placeAbove Fq (k' := k') v).valuation (algebraMap k k' c) = v.valuation c ^ Module.finrank k k' := by
  rw [placeAbove_apply, frobDown_algebraMap, map_pow, (finrank_eq_and_surjective_frobDown Fq).1]

/-- **Uniqueness**: every place of $k'$ whose restriction to $k$ is equivalent to $v$ equals `placeAbove v`. -/
theorem eq_placeAbove (v : Place Fq k) (w' : Place Fq k')
    (h : (w'.valuation.comap (algebraMap k k')).IsEquiv v.valuation) : w' = placeAbove Fq v := by
  apply Place.eq_of_isEquiv
  rw [Valuation.isEquiv_iff_val_le_one]
  intro a
  rw [placeAbove_apply]
  have h1 : w'.valuation a ≤ 1 ↔ w'.valuation (a ^ ringChar Fq ^ IsPurelyInseparable.exponent k k') ≤ 1 := by
    rw [map_pow]
    exact (pow_le_one_iff_of_nonneg zero_le' (pow_pos (CharP.char_is_prime Fq _).pos _).ne').symm
  rw [h1, ← algebraMap_frobDown]
  exact (Valuation.isEquiv_iff_val_le_one.1 h)

/-- $\varphi$ as a ring isomorphism $k'\cong k$. -/
def frobDownEquiv : k' ≃+* k :=
  RingEquiv.ofBijective (frobDown Fq k k')
    ⟨(frobDown Fq k k').injective, (finrank_eq_and_surjective_frobDown Fq).2⟩

/-- **$k'_w\cong k_v$**: the completion of $\varphi$ ($w=v\circ\varphi$). -/
def complEquiv (v : Place Fq k) : (placeAbove Fq (k' := k') v).Completion ≃+* v.Completion :=
  UniformSpace.Completion.mapRingEquiv
    (WithVal.congr (placeAbove Fq (k' := k') v).valuation v.valuation (frobDownEquiv Fq))
    (continuous_withVal_congr _ _ (placeAbove Fq v).valuation_surjective _ fun _ => rfl)
    (by
      rw [WithVal.congr_symm]
      exact continuous_withVal_congr _ _ v.valuation_surjective _ fun y => by
        rw [placeAbove_apply]
        exact congrArg v.valuation ((frobDownEquiv Fq).apply_symm_apply y))

theorem complEquiv_toCompletion (v : Place Fq k) (a : k') :
    complEquiv Fq v ((placeAbove Fq v).toCompletion a) = v.toCompletion (frobDown Fq k k' a) := by
  have hu : UniformContinuous
      (WithVal.congr (placeAbove Fq (k' := k') v).valuation v.valuation (frobDownEquiv Fq)) :=
    uniformContinuous_addMonoidHom_of_continuous
      (f := (WithVal.congr (placeAbove Fq (k' := k') v).valuation v.valuation
        (frobDownEquiv Fq)).toRingHom.toAddMonoidHom)
      (continuous_withVal_congr _ _ (placeAbove Fq v).valuation_surjective _ fun _ => rfl)
  show UniformSpace.Completion.map _ _ = _
  rw [Place.toCompletion, RingHom.comp_apply]
  erw [UniformSpace.Completion.map_coe hu]
  rfl


/-- The $k$-algebra structure of $k_v$ (by $k\to k_v$). -/
def Place.completionAlgebra (v : Place Fq k) : Algebra k v.Completion := v.toCompletion.toAlgebra

attribute [local instance] Place.completionAlgebra

/-- **Weil III.§4, text p.57** (Theorem 4 for purely inseparable $k'$, function fields). For a finite purely
inseparable extension $k'/k$ and a place $v$ of $k$: there is a place $w$ of $k'$ with $w=v^{[k':k]}$ on $k$, it is
the only place of $k'$ above $v$ (every $w'$ whose restriction is equivalent to $v$ equals $w$), and for the continuous
$j:k_v\to k'_w$ extending $k\to k'$, $c\otimes a\mapsto j(c)\lambda_w(a)$ is a ring isomorphism
$k_v\otimes_kk'\cong k'_w$. -/
@[kb "weil1973bnt" "Ch. III, §4, text p. 57 (Thm. 4 for purely inseparable k', function fields)"]
theorem weil_III_4_text57 (v : Place Fq k) :
    ∃ w : Place Fq k',
      (∀ c : k, w.valuation (algebraMap k k' c) = v.valuation c ^ Module.finrank k k') ∧
      (∀ w' : Place Fq k', (w'.valuation.comap (algebraMap k k')).IsEquiv v.valuation → w' = w) ∧
      ∃ j : v.Completion →+* w.Completion, Continuous j ∧
        (∀ c : k, j (v.toCompletion c) = w.toCompletion (algebraMap k k' c)) ∧
        ∃ Ψ : v.Completion ⊗[k] k' ≃+* w.Completion,
          ∀ (c : v.Completion) (a : k'), Ψ (c ⊗ₜ a) = j c * w.toCompletion a := by
  refine ⟨placeAbove Fq v, placeAbove_algebraMap Fq v, fun w' h => eq_placeAbove Fq v w' h, ?_⟩
  haveI := fact_ringChar_prime (Fq := Fq)
  haveI := charP_ringChar (Fq := Fq) k
  haveI := expChar_ringChar (Fq := Fq) k
  set p := ringChar Fq with hp
  set e := IsPurelyInseparable.exponent k k' with he
  set w := placeAbove Fq (k' := k') v with hw
  set Φ := complEquiv Fq (k' := k') v with hΦ
  haveI : CharP v.Completion p := charP_of_injective_algebraMap (algebraMap k v.Completion).injective p
  haveI : ExpChar v.Completion p := ExpChar.prime (Fact.out)
  let fr : v.Completion →+* v.Completion := iterateFrobenius v.Completion p e
  have hfr : ∀ z, fr z = z ^ p ^ e := fun z => by simp [fr, iterateFrobenius_def]
  let j : v.Completion →+* w.Completion := Φ.symm.toRingHom.comp fr
  have hΦj : ∀ c, Φ (j c) = fr c := fun c => Φ.apply_symm_apply _
  have hj : ∀ c : k, j (v.toCompletion c) = w.toCompletion (algebraMap k k' c) := by
    intro c
    apply Φ.injective
    rw [hΦj, hΦ, complEquiv_toCompletion, frobDown_algebraMap, map_pow, hfr]
  have hjc : Continuous j := by
    have h1 : Continuous fr := by
      have : (fr : v.Completion → v.Completion) = fun z => z ^ p ^ e := funext hfr
      rw [this]; exact continuous_pow _
    exact UniformSpace.Completion.continuous_extension.comp h1
  refine ⟨j, hjc, hj, ?_⟩
  letI : Algebra k w.Completion := (w.toCompletion.comp (algebraMap k k')).toAlgebra
  let fK : k' →ₐ[k] w.Completion := { w.toCompletion with commutes' := fun _ => rfl }
  let fv : v.Completion →ₐ[k] w.Completion := { j with commutes' := fun r => hj r }
  let ψ := Algebra.TensorProduct.productMap fv fK
  have hψ : ∀ (c : v.Completion) (a : k'), ψ (c ⊗ₜ a) = j c * w.toCompletion a := fun _ _ => rfl
  -- the local degree $[k_v:k_v^{p^e}]=p^e$
  obtain ⟨hF, -⟩ := weil_ff_completion_isPField v
  obtain ⟨π0, hπ00, hπ0, -⟩ := FieldModule.weil_I_4_thm6_prime hF
  have hdeg : Module.finrank (frobenius v.Completion p).fieldRange v.Completion = p :=
    (FieldModule.weil_I_4_cor1_prop4 hF hπ00 hπ0).1
  set R' := fr.fieldRange with hR'
  have hdegE : Module.finrank R' v.Completion = p ^ e := finrank_iterateFrobenius_fieldRange p hdeg e
  have hpe : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  haveI : FiniteDimensional R' v.Completion := Module.finite_of_finrank_pos (hdegE ▸ hpe)
  -- a prime element generates $k_v$ over $k_v^{p^e}$
  obtain ⟨π, hπ⟩ := v.valuation_surjective (WithZero.exp (-1))
  set πv := v.toCompletion π with hπv_def
  have hπv : Valued.v πv = WithZero.exp (-1) := by rw [hπv_def, Place.valued_toCompletion, hπ]
  obtain ⟨b, hb⟩ := (finrank_eq_and_surjective_frobDown Fq (k := k) (k' := k')).2 π
  haveI : CharP R' p := (Algebra.charP_iff R' v.Completion p).2 inferInstance
  have hmemR : ∀ z : v.Completion, z ^ p ^ e ∈ R' := fun z => ⟨z, hfr z⟩
  set f : R'[X] := X ^ (p ^ e) - C ⟨πv ^ p ^ e, hmemR πv⟩ with hf
  have hfm : f.Monic := monic_X_pow_sub_C _ hpe.ne'
  have hfx : aeval πv f = 0 := by simp [hf]; exact sub_self _
  have hirr : Irreducible f := by
    refine irreducible_X_pow_char_pow_sub_C p e fun r hr => ?_
    obtain ⟨s, hs⟩ := r.2
    have h1 : (r : v.Completion) ^ p = πv ^ p ^ e := congrArg Subtype.val hr
    rw [← hs, hfr, ← pow_mul, mul_comm, pow_mul] at h1
    have h2 : s ^ p = πv := (iterateFrobenius v.Completion p e).injective (by
      simp only [iterateFrobenius_def]; exact h1)
    exact Place.not_pow_eq_of_valued_eq v hπv (Fact.out : p.Prime).two_le s h2
  have hint : IsIntegral R' πv := ⟨f, hfm, by rwa [← aeval_def]⟩
  have hmin : minpoly R' πv = f := (minpoly.eq_of_irreducible_of_monic hirr hfx hfm).symm
  have hadj : R'⟮πv⟯ = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [adjoin.finrank hint, hmin, natDegree_X_pow_sub_C, finrank_top', hdegE]
  have hΦb : Φ (w.toCompletion b) = πv := by rw [hΦ, complEquiv_toCompletion, hb]
  -- surjectivity
  have hsurj : Function.Surjective ψ := by
    intro z
    have hz : Φ z ∈ Algebra.adjoin R' {πv} := by
      rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hadj]
      exact Algebra.mem_top
    suffices H : ∀ y ∈ Algebra.adjoin R' {πv}, Φ.symm y ∈ ψ.range by
      simpa using H _ hz
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.1 hx, ← hΦb, RingEquiv.symm_apply_apply]
      exact ⟨1 ⊗ₜ b, show ψ (1 ⊗ₜ b) = _ by rw [hψ, map_one, one_mul]⟩
    | algebraMap r =>
      obtain ⟨c, hc⟩ := r.2
      refine ⟨c ⊗ₜ 1, ?_⟩
      show ψ (c ⊗ₜ 1) = _
      rw [hψ, map_one, mul_one]
      show Φ.symm (fr c) = _
      rw [hc]; rfl
    | add x y _ _ hx hy => simpa using Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => simpa using Subalgebra.mul_mem _ hx hy
  -- dimensions and injectivity
  letI : Algebra v.Completion w.Completion := j.toAlgebra
  let ψL : v.Completion ⊗[k] k' →ₗ[v.Completion] w.Completion :=
    { toFun := ψ
      map_add' := map_add ψ
      map_smul' := fun c t => by
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul c' a =>
          rw [TensorProduct.smul_tmul', hψ, hψ, RingHom.id_apply, Algebra.smul_def, Algebra.smul_def]
          simp only [Algebra.algebraMap_self, RingHom.id_apply, map_mul, mul_assoc]
          rfl
        | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add] }
  have hdimT : Module.finrank v.Completion (v.Completion ⊗[k] k') = p ^ e := by
    rw [Module.finrank_baseChange, (finrank_eq_and_surjective_frobDown Fq (k := k) (k' := k')).1]
  have hdimW : Module.finrank v.Completion w.Completion = p ^ e := by
    rw [← hdegE]
    refine Algebra.finrank_eq_of_equiv_equiv fr.rangeRestrictFieldEquiv Φ ?_
    ext c
    exact (hΦj c).symm
  haveI : Module.Free v.Completion w.Completion := Module.Free.of_divisionRing _ _
  haveI : FiniteDimensional v.Completion w.Completion := Module.finite_of_finrank_pos (hdimW ▸ hpe)
  have hinj : Function.Injective ψL :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdimT.trans hdimW.symm)).2 hsurj
  exact ⟨RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩, hψ⟩

end Insep

end NumberFieldKB.WeilBNT.FF
