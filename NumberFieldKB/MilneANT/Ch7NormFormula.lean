import NumberFieldKB.MilneANT.Ch7Places
import NumberFieldKB.MilneANT.Ch8ProductFormula

/-!
# Milne, *Algebraic Number Theory*, Lemma 7.16(b): the norm formula

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

The named statement `Lemma7_16b` of `Ch7Places.lean` is discharged from Proposition 8.7
(`prop_8_7_finite`, `prop_8_7_infinite`): for a prime $v$ of a number field $K$, a finite extension $L$ and
$\alpha \in L$, $\prod_{w \mid v} |\alpha|_w = |\operatorname{Nm}_{L/K}\alpha|_v$ with the normalized absolute values.
The work done here is identifying "$w$ lies over $v$" (restriction of absolute values is equivalent) with the
description of the primes above used in Proposition 8.7 (prime ideals lying over a prime ideal; infinite places
restricting to a given one).
-/

open NumberField IsDedekindDomain

namespace NumberFieldKB.MilneANT

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- A finite place of a number field is at most $1$ at $2$. -/
private theorem finitePlace_two_le_one (F : Type) [Field F] [NumberField F] (w : FinitePlace F) :
    w.1 (2 : F) ≤ 1 := by
  have := FinitePlace.norm_le_one F (FinitePlace.maximalIdeal w) (2 : 𝓞 F)
  rw [map_ofNat, FinitePlace.norm_embedding_eq] at this
  exact this

/-- An infinite place of a number field takes the value $2$ at $2$. -/
private theorem infinitePlace_two (F : Type) [Field F] [NumberField F] (u : InfinitePlace F) :
    u.1 (2 : F) = 2 := by
  exact_mod_cast u.map_natCast 2

/-- Lying over for two finite places: the prime ideal of $L$ lies over the prime ideal of $K$. -/
theorem liesOver_finite_finite_iff (P : HeightOneSpectrum (𝓞 L)) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    (placeOf L (.inl (FinitePlace.mk P))).LiesOver (placeOf K (.inl (FinitePlace.mk 𝔭))) ↔
      P.asIdeal.under (𝓞 K) = 𝔭.asIdeal := by
  change (AbsoluteValue.restrictMilne (K := K) (FinitePlace.mk P).1).IsEquiv (FinitePlace.mk 𝔭).1 ↔ _
  constructor
  · intro h
    refine Ideal.ext fun x => ?_
    rw [← FinitePlace.norm_lt_one_iff_mem K 𝔭 x]
    change _ ↔ (FinitePlace.mk 𝔭).1 (algebraMap (𝓞 K) K x) < 1
    rw [← h.lt_one_iff]
    change algebraMap (𝓞 K) (𝓞 L) x ∈ P.asIdeal ↔ _
    rw [← FinitePlace.norm_lt_one_iff_mem L P]
    have : algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) x) =
        algebraMap K L (algebraMap (𝓞 K) K x) := by
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [this]
    rfl
  · intro h
    have : P.asIdeal.LiesOver 𝔭.asIdeal := ⟨h.symm⟩
    have key : ∀ a : K, (AbsoluteValue.restrictMilne (K := K) (FinitePlace.mk P).1) a =
        (FinitePlace.mk 𝔭).1 a ^ (P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K)) :=
      fun a => lemma_8_6_finite K L 𝔭 P a
    have hpos : 0 < P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) :=
      Nat.mul_pos (Ideal.ramificationIdx_pos_of_isDedekindDomain' (p := 𝔭.asIdeal) P.asIdeal 𝔭.ne_bot)
        (Ideal.inertiaDeg_pos _ _)
    intro x y
    rw [key, key]
    exact pow_le_pow_iff_left₀ (by positivity) (by positivity) hpos.ne'

/-- A finite place of $L$ never lies over an infinite place of $K$. -/
theorem not_liesOver_finite_infinite (P : HeightOneSpectrum (𝓞 L)) (u : InfinitePlace K) :
    ¬ (placeOf L (.inl (FinitePlace.mk P))).LiesOver (placeOf K (.inr u)) := by
  intro h
  change (AbsoluteValue.restrictMilne (K := K) (FinitePlace.mk P).1).IsEquiv u.1 at h
  have h1 : u.1 (2 : K) ≤ 1 := by
    refine h.le_one_iff.1 ?_
    have := finitePlace_two_le_one L (FinitePlace.mk P)
    simpa [AbsoluteValue.restrictMilne, map_ofNat] using this
  rw [infinitePlace_two K u] at h1
  norm_num at h1

/-- An infinite place of $L$ never lies over a finite place of $K$. -/
theorem not_liesOver_infinite_finite (w : InfinitePlace L) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ¬ (placeOf L (.inr w)).LiesOver (placeOf K (.inl (FinitePlace.mk 𝔭))) := by
  intro h
  change (AbsoluteValue.restrictMilne (K := K) w.1).IsEquiv (FinitePlace.mk 𝔭).1 at h
  have h1 : (AbsoluteValue.restrictMilne (K := K) w.1) (2 : K) ≤ 1 :=
    h.le_one_iff.2 (finitePlace_two_le_one K (FinitePlace.mk 𝔭))
  have h2 : (AbsoluteValue.restrictMilne (K := K) w.1) (2 : K) = 2 := by
    simp only [AbsoluteValue.restrictMilne, AbsoluteValue.comp_apply, map_ofNat]
    exact infinitePlace_two L w
  rw [h2] at h1
  norm_num at h1

/-- Lying over for two infinite places: the restriction of the infinite place of $L$ is the infinite place of $K$. -/
theorem liesOver_infinite_infinite_iff (w : InfinitePlace L) (v : InfinitePlace K) :
    (placeOf L (.inr w)).LiesOver (placeOf K (.inr v)) ↔ w.comap (algebraMap K L) = v := by
  change (AbsoluteValue.restrictMilne (K := K) w.1).IsEquiv v.1 ↔ _
  rw [InfinitePlace.eq_iff_isEquiv]
  rfl

/-- **Lemma 7.16(b)** (norm formula). For every prime $v$ of the number field $K$ and every $\alpha$ in the finite
extension $L$, the product over the primes $w$ of $L$ lying over $v$ of the normalized absolute values
$|\alpha|_w$ equals the normalized absolute value $|\operatorname{Nm}_{L/K}\alpha|_v$. Proved from
Proposition 8.7. -/
@[kb "milne2020ant" "v3.08, Lemma 7.16, p. 112"]
theorem lemma_7_16b : Lemma7_16b K L := by
  refine ⟨fun v α => ?_⟩
  rw [finprod_subtype_eq_finprod_cond
    (f := fun w : FinitePlace L ⊕ InfinitePlace L => normalizedAbv w α)
    (fun w => (placeOf L w).LiesOver (placeOf K v))]
  rcases v with w | u
  · obtain ⟨𝔭, rfl⟩ : ∃ 𝔭, FinitePlace.mk 𝔭 = w :=
      ⟨FinitePlace.maximalIdeal w, FinitePlace.mk_maximalIdeal w⟩
    have hset : {x : FinitePlace L ⊕ InfinitePlace L |
        (placeOf L x).LiesOver (placeOf K (.inl (FinitePlace.mk 𝔭)))} =
        (fun P : HeightOneSpectrum (𝓞 L) => (Sum.inl (FinitePlace.mk P) : FinitePlace L ⊕ InfinitePlace L)) ''
          {P | P.asIdeal.under (𝓞 K) = 𝔭.asIdeal} := by
      ext x
      rcases x with w' | u'
      · obtain ⟨P, rfl⟩ : ∃ P, FinitePlace.mk P = w' :=
          ⟨FinitePlace.maximalIdeal w', FinitePlace.mk_maximalIdeal w'⟩
        rw [Set.mem_ofPred_eq, liesOver_finite_finite_iff K L P 𝔭]
        constructor
        · intro h
          exact ⟨P, h, rfl⟩
        · rintro ⟨Q, hQ, hQP⟩
          have hQP' := congrArg FinitePlace.maximalIdeal (Sum.inl.inj hQP)
          rw [FinitePlace.maximalIdeal_mk, FinitePlace.maximalIdeal_mk] at hQP'
          subst hQP'
          exact hQ
      · rw [Set.mem_ofPred_eq]
        constructor
        · intro h
          exact (not_liesOver_infinite_finite K L u' 𝔭 h).elim
        · rintro ⟨Q, _, h⟩
          cases h
    change ∏ᶠ x ∈ {x : FinitePlace L ⊕ InfinitePlace L |
        (placeOf L x).LiesOver (placeOf K (.inl (FinitePlace.mk 𝔭)))}, normalizedAbv x α = _
    rw [hset, finprod_mem_image (fun P _ Q _ h => by
      have h' := congrArg FinitePlace.maximalIdeal (Sum.inl.inj h)
      rwa [FinitePlace.maximalIdeal_mk, FinitePlace.maximalIdeal_mk] at h')]
    exact prop_8_7_finite K L 𝔭 α
  · have hset : {x : FinitePlace L ⊕ InfinitePlace L |
        (placeOf L x).LiesOver (placeOf K (.inr u))} =
        (fun w : InfinitePlace L => (Sum.inr w : FinitePlace L ⊕ InfinitePlace L)) ''
          {w | w.comap (algebraMap K L) = u} := by
      ext x
      rcases x with w' | u'
      · rw [Set.mem_ofPred_eq]
        constructor
        · intro h
          obtain ⟨P, rfl⟩ : ∃ P, FinitePlace.mk P = w' :=
            ⟨FinitePlace.maximalIdeal w', FinitePlace.mk_maximalIdeal w'⟩
          exact (not_liesOver_finite_infinite K L P u h).elim
        · rintro ⟨Q, _, h⟩
          cases h
      · rw [Set.mem_ofPred_eq, liesOver_infinite_infinite_iff K L u' u]
        constructor
        · intro h
          exact ⟨u', h, rfl⟩
        · rintro ⟨Q, hQ, hQP⟩
          cases hQP
          exact hQ
    change ∏ᶠ x ∈ {x : FinitePlace L ⊕ InfinitePlace L |
        (placeOf L x).LiesOver (placeOf K (.inr u))}, normalizedAbv x α = _
    rw [hset, finprod_mem_image (fun a _ b _ h => Sum.inr.inj h)]
    exact prop_8_7_infinite K L u α

end NumberFieldKB.MilneANT
