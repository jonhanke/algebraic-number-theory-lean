import NumberFieldKB.MilneCFT.Ch7.Kummer
import NumberFieldKB.MilneCFT.Ch7.FirstInequality
import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.SInteger

/-!
# Milne, *Class Field Theory*, Chapter VII §6: the Kummer setting of the second inequality

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

**Setting (p. 215).** $K$ contains a primitive $p$-th root of $1$ ($p$ prime); $S$ is a finite set of finite primes
containing the divisors of $p$ and a set of generators of the class group (Milne's $S$ also contains the infinite
primes; $s = |S| + $ the number of infinite primes); $M = K[U(S)^{1/p}]$ is the Kummer extension of the $S$-units, and
$L\subseteq M$ an intermediate field (Milne: $L = K[a_1^{1/p},\dots,a_r^{1/p}]$ with $a_i\in U(S)$; by Kummer theory
these are exactly the intermediate fields of $M$). This is `KummerSetting K p S M`.

* `kummerE S T p` $= E = \prod_{v\in S}K_v^{\times p}\times\prod_{v\in T}K_v^\times\times\prod_{v\notin S\cup T}U_v$
  (with $K_v^{\times p}$ at the infinite primes).
* `LocalNormInput K` (named statement): the local class field theory used in §§6, 9 — at a finite prime the local
  norm group of a finite abelian extension has index the local degree, and at an unramified prime it contains the units.
* **Lemmas 6.2, 6.3, 6.4, 6.6, 6.7, 6.9** and **Proposition 6.10**.
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField
open scoped Classical

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable {K : Type} [Field K] [NumberField K]

/-- $a\in K$ is an $n$-th power in $K_v$ ($v$ finite). -/
def IsPowAt (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (a : K) : Prop :=
  ∃ y : v.adicCompletion K, y ^ n = (a : v.adicCompletion K)

/-- $a\in K$ is an $n$-th power in $K_w$ ($w$ infinite). -/
def IsPowAtInf (w : InfinitePlace K) (n : ℕ) (a : K) : Prop :=
  ∃ y : w.Completion, y ^ n = (a : w.Completion)

/-- An idele component is an $n$-th power in $K_v$. -/
def ideleIsPowAt (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (x : IdeleGroup (𝓞 K) K) : Prop :=
  ∃ y : v.adicCompletion K, y ^ n = (x : AdeleRing (𝓞 K) K).2 v

/-- Componentwise product of adeles at an infinite place. -/
private lemma adele_mul_fst (a b : AdeleRing (𝓞 K) K) (w : InfinitePlace K) :
    (a * b).1 w = a.1 w * b.1 w := rfl

/-- Componentwise product of adeles at a finite place. -/
private lemma adele_mul_snd (a b : AdeleRing (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) :
    (a * b).2 v = a.2 v * b.2 v := rfl

/-- Componentwise unit of adeles at an infinite place. -/
private lemma adele_one_fst (w : InfinitePlace K) : (1 : AdeleRing (𝓞 K) K).1 w = 1 := rfl

/-- Componentwise unit of adeles at a finite place. -/
private lemma adele_one_snd (v : HeightOneSpectrum (𝓞 K)) : (1 : AdeleRing (𝓞 K) K).2 v = 1 := rfl

/-- The subgroup $E =\prod_{v\in S}K_v^{\times p}\times\prod_{v\in T}K_v^\times\times\prod_{v\notin S\cup T}U_v$ of
$\mathbb I_K$ (Milne, *CFT*, Chapter VII, Lemma 6.4; the infinite primes are in $S$). -/
def kummerE (S T : Set (HeightOneSpectrum (𝓞 K))) (p : ℕ) : Subgroup (IdeleGroup (𝓞 K) K) where
  carrier := {x | (∀ w : InfinitePlace K, ∃ y : w.Completion, y ^ p = (x : AdeleRing (𝓞 K) K).1 w) ∧
    (∀ v ∈ S, ideleIsPowAt v p x) ∧ ∀ v, v ∉ S → v ∉ T → Valued.v ((x : AdeleRing (𝓞 K) K).2 v) = 1}
  mul_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    refine ⟨fun w => ?_, fun v hv => ?_, fun v hvS hvT => ?_⟩
    · obtain ⟨a, ha⟩ := hx1 w
      obtain ⟨b, hb⟩ := hy1 w
      exact ⟨a * b, by rw [Units.val_mul, adele_mul_fst, ← ha, ← hb, mul_pow]⟩
    · obtain ⟨a, ha⟩ := hx2 v hv
      obtain ⟨b, hb⟩ := hy2 v hv
      exact ⟨a * b, by rw [Units.val_mul, adele_mul_snd, ← ha, ← hb, mul_pow]⟩
    · rw [Units.val_mul, adele_mul_snd, map_mul, hx3 v hvS hvT, hy3 v hvS hvT, one_mul]
  one_mem' := by
    refine ⟨fun w => ⟨1, ?_⟩, fun v hv => ⟨1, ?_⟩, fun v hvS hvT => ?_⟩
    · rw [Units.val_one, adele_one_fst, one_pow]
    · rw [Units.val_one, adele_one_snd, one_pow]
    · rw [Units.val_one, adele_one_snd, map_one]
  inv_mem' := by
    rintro x ⟨hx1, hx2, hx3⟩
    have hmul : ((x : AdeleRing (𝓞 K) K) * ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]; rfl
    refine ⟨fun w => ?_, fun v hv => ?_, fun v hvS hvT => ?_⟩
    · obtain ⟨a, ha⟩ := hx1 w
      have h := congrArg (fun z : AdeleRing (𝓞 K) K => z.1 w) hmul
      simp only [adele_mul_fst, adele_one_fst] at h
      refine ⟨a⁻¹, ?_⟩
      rw [inv_pow, ha]
      exact inv_eq_of_mul_eq_one_right h
    · obtain ⟨a, ha⟩ := hx2 v hv
      have h := congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) hmul
      simp only [adele_mul_snd, adele_one_snd] at h
      refine ⟨a⁻¹, ?_⟩
      rw [inv_pow, ha]
      exact inv_eq_of_mul_eq_one_right h
    · have h := congrArg (fun z : AdeleRing (𝓞 K) K => Valued.v (z.2 v)) hmul
      simp only [adele_mul_snd, adele_one_snd, map_mul, map_one, hx3 v hvS hvT, one_mul] at h
      exact h

/-- The local norm group $\{x\in K_v^\times : \iota_v(x)\in\mathrm{Nm}_{L/K}\mathbb I_L\}$ at a finite prime. -/
def localNormGroup (L : Type) [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (v.adicCompletion K)ˣ :=
  (normIdeles K L).comap (IdeleGroup.ofAdicCompletion (𝓞 K) K v)

/-- The local norm group at an infinite prime. -/
def localNormGroupInf (L : Type) [Field L] [NumberField L] [Algebra K L] (w : InfinitePlace K) :
    Subgroup w.Completionˣ :=
  (normIdeles K L).comap (IdeleGroup.ofCompletion (𝓞 K) K w)

variable (K) in
/-- **Local class field theory at the completions** (named statement; Milne, *CFT*, Chapter I, Theorem 1.1 (b), and
Chapter III, Proposition 1.2, as used in Chapter VII, Lemmas 6.4, 9.3 and Proposition 6.10): for a finite abelian
extension $L/K$ of number fields and a finite prime $v$ of $K$, the local norm group has index the local degree
$e(w/v)f(w/v)$; if $v$ is unramified in $L$ it contains the units $U_v$; at an infinite prime $w$ the local norm group
has index $1$ or $2$ according as $w$ does not or does ramify; and $K_v^\times/\mathrm{Nm}\cong
\mathrm{Gal}(L_w/K_v)$ is killed by every exponent of $\mathrm{Gal}(L/K)$ (`pow_le`). -/
@[kb "milne2020cft" "Ch. I, Thm. 1.1 (b), Ch. III, Prop. 1.2 (input, at completions of number fields)"]
structure LocalNormInput : Prop where
  index_eq : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (∀ σ τ : Gal(L/K), σ * τ = τ * σ) → ∀ (v : HeightOneSpectrum (𝓞 K)) (Q : v.asIdeal.primesOver (𝓞 L)),
      (localNormGroup L v).index = Q.1.ramificationIdx (𝓞 K) * Q.1.inertiaDeg (𝓞 K)
  units_le : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)), v ∈ unramifiedPrimes K L → localUnits K v ≤ localNormGroup L v
  index_inf : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (w : InfinitePlace K),
    (localNormGroupInf L w).index = if InfinitePlace.RamifiesIn L w then 2 else 1
  pow_le : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (∀ σ τ : Gal(L/K), σ * τ = τ * σ) → ∀ n : ℕ, (∀ σ : Gal(L/K), σ ^ n = 1) →
      ∀ (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ), x ^ n ∈ localNormGroup L v

/-! ## Proposition 6.10 -/

/-- The image of an $S$-unit in $U_v$ for $v\notin S$. -/
def sUnitToLocal (S : Set (HeightOneSpectrum (𝓞 K))) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    S.unit K →* localUnits K v where
  toFun x := ⟨Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) x,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2 (by
      have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 K) (v := v)
        ((x : Kˣ) : K)
      exact h.trans (Set.unit_valuation_eq_one S K x hv))⟩
  map_one' := Subtype.ext (Units.ext (by simp))
  map_mul' x y := Subtype.ext (Units.ext (by simp))

/-- The map $U(S)\to\prod_{v\in T}U_v/U_v^n$ (Milne, *CFT*, Chapter VII, Lemma 6.9 and Proposition 6.10), for $T$
disjoint from $S$. -/
def sUnitsToLocalQuot (S T : Set (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T) (n : ℕ) :
    S.unit K →* ((v : T) → localUnits K v.1 ⧸ (powMonoidHom n : localUnits K v.1 →* localUnits K v.1).range) :=
  MonoidHom.pi fun v => (QuotientGroup.mk' _).comp
    (sUnitToLocal S v.1 (Set.disjoint_right.mp hST v.2))

variable (K) in
/-- **Proposition 6.10** (named statement; Milne, *CFT*, Chapter VII, p. 219; Milne proves it from Lemma 4.5, i.e.
from the first inequality, Proposition 2.8 and local class field theory): let $K$ contain a primitive $n$-th root of
$1$; let $S$ be finite, containing the divisors of $n$ and generators of the class group; let $T$ be finite, disjoint
from $S$, with $U(S)\to\prod_{v\in T}U_v/U_v^n$ surjective. If $b\in K^\times$ is an $n$-th power in $K_v$ for all
$v\in S$ (and all infinite $v$) and a unit outside $S\cup T$, then $b\in K^{\times n}$. -/
@[kb "milne2020cft" "Ch. VII, Prop. 6.10 (input)"]
structure Prop6_10 : Prop where
  isPow : ∀ (n : ℕ), 0 < n → (∃ ζ : K, IsPrimitiveRoot ζ n) →
    ∀ (S T : Set (HeightOneSpectrum (𝓞 K))) (_ : S.Finite) (_ : T.Finite) (hST : Disjoint S T),
    (∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    Subgroup.closure ((fun v => primeClass K v) '' S) = ⊤ →
    Function.Surjective (sUnitsToLocalQuot S T hST n) →
    ∀ b : Kˣ, (∀ w : InfinitePlace K, IsPowAtInf w n (b : K)) → (∀ v ∈ S, IsPowAt v n (b : K)) →
      (∀ v, v ∉ S → v ∉ T → v.valuation K (b : K) = 1) → ∃ c : Kˣ, c ^ n = b

/-! ## The Kummer setting: Lemmas 6.2–6.9 -/

/-- **Milne's setting of §6** (p. 215): $p$ prime, $\zeta_p\in K$, $S$ finite containing the divisors of $p$ and
generators of the class group, and $M = K[U(S)^{1/p}]$: every $S$-unit has a $p$-th root in $M$ and these roots
generate $M$. -/
structure KummerSetting (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [Field M] [Algebra K M] :
    Prop where
  prime : p.Prime
  zeta : ∃ ζ : K, IsPrimitiveRoot ζ p
  finite : S.Finite
  dvd : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S
  classGroup : Subgroup.closure ((fun v => primeClass K v) '' S) = ⊤
  roots : ∀ u ∈ S.unit K, ∃ y : M, y ^ p = algebraMap K M (u : K)
  generates : IntermediateField.adjoin K {y : M | ∃ u ∈ S.unit K, y ^ p = algebraMap K M (u : K)} = ⊤

variable {p : ℕ} {S : Set (HeightOneSpectrum (𝓞 K))} {M : Type} [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

/-- The Frobenius elements $(\mathfrak p_v, M/K)$, $v\in T$, lie in $\mathrm{Gal}(M/L)$ and form an
$\mathbb F_p$-basis of it: $e\mapsto\prod_v(\mathfrak p_v, M/K)^{e_v}$ is a bijection from $\mathbb F_p^T$ onto
$\mathrm{Gal}(M/L)$ (the conclusion of Lemma 6.2). -/
def FrobBasis (p : ℕ) (L : IntermediateField K M) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (Q : ∀ v : T, v.1.asIdeal.primesOver (𝓞 M)) : Prop :=
  Set.BijOn (fun e : T → ZMod p => ((Finset.univ : Finset T).toList.map fun v => frobAt K M v.1 (Q v) ^ (e v).val).prod)
    Set.univ
    (L.fixingSubgroup : Set Gal(M/K))

/-- **Lemma 6.2** (Milne, *CFT*, Chapter VII, p. 215): in the setting, there is a finite set $T$ of primes of $K$,
disjoint from $S$ and unramified in $M$, whose Frobenius elements in $M/K$ form a basis of $\mathrm{Gal}(M/L)$. -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.2 (input)"]
structure Lemma6_2 (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] : Prop where
  exists_T : KummerSetting p S M → ∀ L : IntermediateField K M,
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (Q : ∀ v : T, v.1.asIdeal.primesOver (𝓞 M)),
      Disjoint (T : Set (HeightOneSpectrum (𝓞 K))) S ∧ (∀ v ∈ T, v ∈ unramifiedPrimes K M) ∧
        FrobBasis p L T Q

/-- **Lemma 6.3** (Milne, *CFT*, Chapter VII, p. 216): with $T$ as in Lemma 6.2, an $S$-unit $a$ becomes a $p$-th power
in $L$ if and only if it is a $p$-th power in $K_v$ for all $v\in T$. -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.3 (input)"]
structure Lemma6_3 (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] : Prop where
  iff : KummerSetting p S M → ∀ (L : IntermediateField K M) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (Q : ∀ v : T, v.1.asIdeal.primesOver (𝓞 M)), Disjoint (T : Set (HeightOneSpectrum (𝓞 K))) S →
    (∀ v ∈ T, v ∈ unramifiedPrimes K M) → FrobBasis p L T Q → ∀ a : Kˣ, a ∈ S.unit K →
    ((∃ y : L, y ^ p = algebraMap K L (a : K)) ↔ ∀ v ∈ T, IsPowAt v p (a : K))

/-- **Lemma 6.4** (Milne, *CFT*, Chapter VII, p. 216; uses local class field theory): with $T$ as in Lemma 6.2,
$E = \prod_{v\in S}K_v^{\times p}\times\prod_{v\in T}K_v^\times\times\prod_{v\notin S\cup T}U_v\subseteq
\mathrm{Nm}_{L/K}(\mathbb I_L)$. -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.4 (input)"]
structure Lemma6_4 (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] : Prop where
  le : KummerSetting p S M → ∀ (L : IntermediateField K M) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (Q : ∀ v : T, v.1.asIdeal.primesOver (𝓞 M)), Disjoint (T : Set (HeightOneSpectrum (𝓞 K))) S →
    (∀ v ∈ T, v ∈ unramifiedPrimes K M) → FrobBasis p L T Q → kummerE S T p ≤ normIdeles K L

/-- **Lemma 6.6** (Milne, *CFT*, Chapter VII, p. 217; uses Proposition 6.8): $(\mathbb I_{S\cup T} : E) = p^{2s}$,
$s$ the number of primes in $S$ together with the infinite primes. -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.6 (input)"]
structure Lemma6_6 (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] : Prop where
  index : KummerSetting p S M → ∀ T : Finset (HeightOneSpectrum (𝓞 K)),
    Disjoint (T : Set (HeightOneSpectrum (𝓞 K))) S →
    (kummerE S T p).relIndex (idelesS (S ∪ T)) = p ^ (2 * (S.ncard + Fintype.card (InfinitePlace K)))

/-- **Lemma 6.7** (Milne, *CFT*, Chapter VII, p. 217): with $T$ as in Lemma 6.2 ($|T| = t$),
$(U(S\cup T) : K^\times\cap E) = p^{s+t}$. -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.7 (input)"]
structure Lemma6_7 (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] : Prop where
  index : KummerSetting p S M → ∀ (L : IntermediateField K M) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (Q : ∀ v : T, v.1.asIdeal.primesOver (𝓞 M)), Disjoint (T : Set (HeightOneSpectrum (𝓞 K))) S →
    (∀ v ∈ T, v ∈ unramifiedPrimes K M) → FrobBasis p L T Q →
    ((kummerE S T p).comap (IdeleGroup.unitEmbedding (𝓞 K) K)).relIndex ((S ∪ T).unit K) =
      p ^ (S.ncard + Fintype.card (InfinitePlace K) + T.card)

/-- **Lemma 6.9** (Milne, *CFT*, Chapter VII, p. 218): with $T$ as in Lemma 6.2, $U(S)\to\prod_{v\in T}U_v/U_v^p$ is
surjective. -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.9 (input)"]
structure Lemma6_9 (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] : Prop where
  surjective : KummerSetting p S M → ∀ (L : IntermediateField K M) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (Q : ∀ v : T, v.1.asIdeal.primesOver (𝓞 M)) (hTS : Disjoint (T : Set (HeightOneSpectrum (𝓞 K))) S),
    (∀ v ∈ T, v ∈ unramifiedPrimes K M) → FrobBasis p L T Q →
    Function.Surjective (sUnitsToLocalQuot S (T : Set (HeightOneSpectrum (𝓞 K))) hTS.symm p)

end NumberFieldKB.MilneCFT.Ch7
