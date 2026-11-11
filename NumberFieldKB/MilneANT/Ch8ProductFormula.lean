import NumberFieldKB.MilneANT.Ch8Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: the product formula

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Places of a number field are Mathlib's `FinitePlace` (already normalized: $N\mathfrak p^{-\operatorname{ord}}$) and
`InfinitePlace`; the normalized absolute value is `normAbv` (`Ch8Basic.lean`).

* **Lemma 8.6** (`lemma_8_6_finite`, `lemma_8_6_infinite`, proved for the places of number fields).
* **Proposition 8.7** (`prop_8_7_finite`, `prop_8_7_infinite`, proved).
* **Theorem 8.8** (`thm_8_8`, the product formula, restated from Mathlib's `NumberField.prod_abs_eq_one`).
* **Aside 8.9** (`Aside8_9`, named statement: Artin–Whaples).
-/

open NumberField IsDedekindDomain

namespace NumberFieldKB.MilneANT

noncomputable section

/-! ## Lemma 8.6 and Proposition 8.7 -/

section NormFormula

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Lemma 8.6, finite places** (proved): for a prime $\mathfrak P$ of $L$ over $\mathfrak p$ of $K$ and $a \in K$,
$\lVert a\rVert_{\mathfrak P} = \lVert a\rVert_{\mathfrak p}^{n}$ with $n = e(\mathfrak P/\mathfrak p)f(\mathfrak P/\mathfrak p)$,
which is the local degree $[L_{\mathfrak P}:K_{\mathfrak p}]$ (Milne's $n = [L:K]$ for the local extension; Milne's
proof computes exactly $\lVert\pi\rVert = (1/N\mathfrak P)^e = (1/N\mathfrak p)^{ef}$). -/
@[kb "milne2020ant" "v3.08, Lem. 8.6, p. 137"]
theorem lemma_8_6_finite (𝔭 : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver 𝔭.asIdeal] (a : K) :
    FinitePlace.mk P (algebraMap K L a) =
      FinitePlace.mk 𝔭 a ^ (P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K)) :=
  FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap 𝔭 P a

/-- **Lemma 8.6, infinite places** (proved): for an infinite place $w$ of $L$ over $v$ of $K$ and $a \in K$, the
normalized absolute values satisfy $\lVert a\rVert_w = \lVert a\rVert_v^{n}$ with $n = [L_w : K_v] \in \{1, 2\}$
($2$ exactly when $v$ is real and $w$ complex). -/
@[kb "milne2020ant" "v3.08, Lem. 8.6, p. 137"]
theorem lemma_8_6_infinite (v : InfinitePlace K) (w : InfinitePlace L) (hw : w.comap (algebraMap K L) = v)
    (a : K) :
    normAbv L (.inr w) (algebraMap K L a) = normAbv K (.inr v) a ^ (w.mult / v.mult) := by
  have hdiv : w.mult = (w.mult / v.mult) * v.mult := by
    subst hw
    have hle := InfinitePlace.mult_comap_le (algebraMap K L) w
    unfold InfinitePlace.mult at hle ⊢
    by_cases h1 : (w.comap (algebraMap K L)).IsReal
    · simp [h1]
    · have : ¬ w.IsReal := fun h => h1 (InfinitePlace.IsReal.comap _ h)
      simp [h1, this]
  have hwa : w (algebraMap K L a) = v a := by rw [← hw, InfinitePlace.comap_apply]
  simp only [normAbv_inr, hwa, ← pow_mul]
  congr 1
  rw [mul_comm]; exact hdiv

/-- The set of primes of the ring of integers of $L$ above a prime of that of $K$ is finite. -/
theorem finite_primesAbove (𝔭 : HeightOneSpectrum (𝓞 K)) :
    {P : HeightOneSpectrum (𝓞 L) | P.asIdeal.under (𝓞 K) = 𝔭.asIdeal}.Finite := by
  have hfin := IsDedekindDomain.primesOver_finite 𝔭.asIdeal (𝓞 L)
  refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) (hfin.subset ?_)
    (fun P _ Q _ h => HeightOneSpectrum.ext h)
  rintro _ ⟨P, hP, rfl⟩
  exact ⟨P.isPrime, ⟨hP.symm⟩⟩

/-- The finite set of primes of the ring of integers of $L$ above a prime $\mathfrak p$ of that of $K$. -/
def primesAbove (𝔭 : HeightOneSpectrum (𝓞 K)) : Finset (HeightOneSpectrum (𝓞 L)) :=
  (finite_primesAbove K L 𝔭).toFinset

/-- Membership in `primesAbove`. -/
theorem mem_primesAbove {𝔭 : HeightOneSpectrum (𝓞 K)} {P : HeightOneSpectrum (𝓞 L)} :
    P ∈ primesAbove K L 𝔭 ↔ P.asIdeal.under (𝓞 K) = 𝔭.asIdeal := by
  simp [primesAbove]

/-- There is at least one prime above every prime. -/
theorem primesAbove_nonempty (𝔭 : HeightOneSpectrum (𝓞 K)) : (primesAbove K L 𝔭).Nonempty := by
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) 𝔭.asIdeal
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver 𝔭.ne_bot ⟨hPm.isPrime, hP⟩
  exact ⟨⟨P, hPm.isPrime, hne⟩, (mem_primesAbove K L).2 hP.over.symm⟩

open Classical in
/-- The multiplicity of a prime ideal in a prime ideal is $1$ if they are equal and $0$ otherwise. -/
theorem multiplicity_prime_prime (P Q : HeightOneSpectrum (𝓞 L)) :
    multiplicity P.asIdeal Q.asIdeal = if P = Q then 1 else 0 := by
  by_cases h : P = Q
  · subst h
    simp only [ite_true]
    exact multiplicity_self (FiniteMultiplicity.of_prime_left P.prime P.ne_bot)
  · simp only [h, ite_false]
    apply multiplicity_eq_zero_of_not_dvd
    rw [Ideal.dvd_iff_le]
    intro hle
    exact h (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hle).symm)

/-- The $\mathfrak p$-adic order of the relative norm of a nonzero ideal $J$ is
$\sum_{\mathfrak P\mid\mathfrak p} f(\mathfrak P/\mathfrak p)\operatorname{ord}_{\mathfrak P}(J)$. -/
theorem multiplicity_relNorm (𝔭 : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 L)) (hJ : J ≠ ⊥) :
    multiplicity 𝔭.asIdeal (Ideal.relNorm (𝓞 K) J) =
      ∑ P ∈ primesAbove K L 𝔭, P.asIdeal.inertiaDeg (𝓞 K) * multiplicity P.asIdeal J := by
  classical
  revert hJ
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd Ideal.zero_eq_bot h
  | h₂ J hu =>
    intro _
    rw [Ideal.isUnit_iff] at hu
    subst hu
    rw [Ideal.relNorm_top, ← Ideal.one_eq_top]
    simp
  | h₃ a p ha hp ih =>
    intro hJ
    have hpne : p ≠ ⊥ := hp.ne_zero
    have hpP : p.IsPrime := Ideal.isPrime_of_prime hp
    let Q : HeightOneSpectrum (𝓞 L) := ⟨p, hpP, hpne⟩
    have ha' : a ≠ ⊥ := ha
    have hmax : p.IsMaximal := Q.isMaximal
    have hrn : Ideal.relNorm (𝓞 K) p = (p.under (𝓞 K)) ^ p.inertiaDeg (𝓞 K) :=
      Ideal.relNorm_eq_pow_of_isMaximal p (p.under (𝓞 K))
    have hrp_ne : Ideal.relNorm (𝓞 K) p ≠ ⊥ := by rwa [Ne, Ideal.relNorm_eq_bot_iff]
    have hra_ne : Ideal.relNorm (𝓞 K) a ≠ ⊥ := by rwa [Ne, Ideal.relNorm_eq_bot_iff]
    rw [map_mul, multiplicity_mul 𝔭.prime
      (FiniteMultiplicity.of_prime_left 𝔭.prime (mul_ne_zero hrp_ne hra_ne)), ih ha']
    have hR : ∀ P ∈ primesAbove K L 𝔭, P.asIdeal.inertiaDeg (𝓞 K) * multiplicity P.asIdeal (p * a) =
        P.asIdeal.inertiaDeg (𝓞 K) * (if P = Q then 1 else 0) +
          P.asIdeal.inertiaDeg (𝓞 K) * multiplicity P.asIdeal a := by
      intro P _
      rw [multiplicity_mul P.prime (FiniteMultiplicity.of_prime_left P.prime hJ), ← mul_add,
        ← multiplicity_prime_prime]
    rw [Finset.sum_congr rfl hR, Finset.sum_add_distrib]
    congr 1
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
    by_cases hQ' : Q ∈ primesAbove K L 𝔭
    · have : p.under (𝓞 K) = 𝔭.asIdeal := (mem_primesAbove K L).1 hQ'
      simp only [hQ', ↓reduceIte, hrn, this]
      exact multiplicity_pow_self_of_prime 𝔭.prime _
    · simp only [hQ', ↓reduceIte, hrn]
      apply multiplicity_eq_zero_of_not_dvd
      intro hd
      apply hQ'
      rw [mem_primesAbove]
      have h1 := 𝔭.prime.dvd_of_dvd_pow hd
      rw [Ideal.dvd_iff_le] at h1
      exact (inferInstance : (p.under (𝓞 K)).IsMaximal).eq_of_le 𝔭.isPrime.ne_top h1

/-- Proposition 8.7 for a nonzero algebraic integer: the product of the normalized absolute values over the
primes above $\mathfrak p$ is the normalized absolute value of the norm. -/
theorem prop_8_7_finite_integral (𝔭 : HeightOneSpectrum (𝓞 K)) {x : 𝓞 L} (hx : x ≠ 0) :
    ∏ P ∈ primesAbove K L 𝔭, FinitePlace.mk P (x : L) =
      FinitePlace.mk 𝔭 (Algebra.norm K (x : L)) := by
  classical
  set n : 𝓞 K := Algebra.intNorm (𝓞 K) (𝓞 L) x with hn
  have hspan : Ideal.span {n} = Ideal.relNorm (𝓞 K) (Ideal.span {x}) :=
    (Ideal.relNorm_singleton _ x).symm
  have hI : Ideal.span {x} ≠ ⊥ := by simpa using hx
  have hn0 : n ≠ 0 := by
    intro h
    apply hI
    rw [← Ideal.relNorm_eq_bot_iff (R := 𝓞 K), ← hspan, h]
    simp
  have hnK : ((n : 𝓞 K) : K) = Algebra.norm K (x : L) :=
    Algebra.algebraMap_intNorm (K := K) (L := L) x
  have hmult := multiplicity_relNorm K L 𝔭 _ hI
  rw [← hspan] at hmult
  have h𝔭 := normAbv_finitePlace_mul_absNorm_pow K 𝔭 hn0
  rw [hmult] at h𝔭
  have hP : ∀ P ∈ primesAbove K L 𝔭, FinitePlace.mk P (x : L) *
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (P.asIdeal.inertiaDeg (𝓞 K) * multiplicity P.asIdeal (Ideal.span {x}))
        = 1 := by
    intro P hPmem
    have h := normAbv_finitePlace_mul_absNorm_pow L P hx
    have hlies : P.asIdeal.LiesOver 𝔭.asIdeal := ⟨((mem_primesAbove K L).1 hPmem).symm⟩
    have hN := Ideal.absNorm_pow_inertiaDeg 𝔭.asIdeal P.asIdeal
    rw [← hN, Nat.cast_pow, ← pow_mul] at h
    exact h
  have hprod : (∏ P ∈ primesAbove K L 𝔭, FinitePlace.mk P (x : L)) *
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (∑ P ∈ primesAbove K L 𝔭,
        P.asIdeal.inertiaDeg (𝓞 K) * multiplicity P.asIdeal (Ideal.span {x})) = 1 := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one hP
  have hpos : (0 : ℝ) < (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (∑ P ∈ primesAbove K L 𝔭,
        P.asIdeal.inertiaDeg (𝓞 K) * multiplicity P.asIdeal (Ideal.span {x})) := by
    have : 0 < Ideal.absNorm 𝔭.asIdeal := Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors
      ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩)
    positivity
  rw [← hnK]
  exact (mul_right_cancel₀ hpos.ne' (h𝔭.trans hprod.symm)).symm

/-- **Proposition 8.7, finite places** (proved): for a finite extension of number fields $L/K$, a prime
$\mathfrak p$ of $K$ and $\alpha \in L$, $\prod_{\mathfrak P\mid\mathfrak p}\lVert\alpha\rVert_{\mathfrak P} =
\lVert\mathrm{Nm}_{L/K}\alpha\rVert_{\mathfrak p}$ (normalized absolute values). -/
@[kb "milne2020ant" "v3.08, Prop. 8.7, p. 138"]
theorem prop_8_7_finite (𝔭 : HeightOneSpectrum (𝓞 K)) (α : L) :
    ∏ᶠ (P : HeightOneSpectrum (𝓞 L)) (_ : P.asIdeal.under (𝓞 K) = 𝔭.asIdeal), FinitePlace.mk P α =
      FinitePlace.mk 𝔭 (Algebra.norm K α) := by
  classical
  rw [finprod_cond_eq_prod_of_cond_iff (t := primesAbove K L 𝔭) _
    (fun {P} _ => (mem_primesAbove K L).symm)]
  by_cases hα : α = 0
  · subst hα
    obtain ⟨P, hP⟩ := primesAbove_nonempty K L 𝔭
    rw [Finset.prod_eq_zero hP (by simp)]
    simp
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) α
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hα
    have h1 := prop_8_7_finite_integral K L 𝔭 ha0
    have h2 := prop_8_7_finite_integral K L 𝔭 hb0
    have hbL : ((b : 𝓞 L) : L) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hb0
    have hnb : Algebra.norm K ((b : 𝓞 L) : L) ≠ 0 := Algebra.norm_ne_zero_iff.2 hbL
    have hnorm : Algebra.norm K (((a : 𝓞 L) : L) / ((b : 𝓞 L) : L)) =
        Algebra.norm K ((a : 𝓞 L) : L) / Algebra.norm K ((b : 𝓞 L) : L) := by
      rw [eq_div_iff hnb, ← map_mul, div_mul_cancel₀ _ hbL]
    simp only [map_div₀, Finset.prod_div_distrib]
    rw [← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, h1, h2, hnorm,
      map_div₀]

omit [NumberField K] in
open Classical in
/-- Counting extensions of a complex embedding $\varphi$ of $K$ to the embeddings of $L$ defining a given infinite
place $w$ over the place of $\varphi$: their number times $m_v$ is $m_w$. -/
theorem card_extensions_mul_mult (φ : K →+* ℂ) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = InfinitePlace.mk φ) :
    (Finset.univ.filter (fun σ : L →+* ℂ =>
        σ.comp (algebraMap K L) = φ ∧ InfinitePlace.mk σ = w)).card * (InfinitePlace.mk φ).mult =
      w.mult := by
  have hS := InfinitePlace.card_filter_mk_eq w
  have key : ∀ σ : L →+* ℂ, InfinitePlace.mk σ = w →
      σ.comp (algebraMap K L) = φ ∨ ComplexEmbedding.conjugate (σ.comp (algebraMap K L)) = φ := by
    intro σ h
    rw [← h, InfinitePlace.comap_mk] at hw
    exact InfinitePlace.mk_eq_iff.1 hw
  by_cases hφ : ComplexEmbedding.IsReal φ
  · have h1 : (InfinitePlace.mk φ).mult = 1 := by
      unfold InfinitePlace.mult; simp [InfinitePlace.isReal_mk_iff.2 hφ]
    rw [h1, mul_one, ← hS]
    congr 1
    apply Finset.filter_congr
    intro σ _
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rcases key σ h with h' | h'
    · exact h'
    · calc σ.comp (algebraMap K L)
          = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (σ.comp (algebraMap K L))) :=
            (ComplexEmbedding.involutive_conjugate K _).symm
        _ = ComplexEmbedding.conjugate φ := by rw [h']
        _ = φ := ComplexEmbedding.isReal_iff.1 hφ
  · have h2 : (InfinitePlace.mk φ).mult = 2 := by
      unfold InfinitePlace.mult
      rw [if_neg (fun h => hφ (InfinitePlace.isReal_mk_iff.1 h))]
    have hwc : w.mult = 2 := by
      unfold InfinitePlace.mult
      rw [if_neg]
      intro h
      apply hφ
      rw [← InfinitePlace.isReal_mk_iff, ← hw]
      exact InfinitePlace.IsReal.comap _ h
    rw [h2, hwc]
    have hS2 : (Finset.univ.filter (fun σ : L →+* ℂ => InfinitePlace.mk σ = w)).card = 2 := by
      rw [hS, hwc]
    set S := Finset.univ.filter (fun σ : L →+* ℂ => InfinitePlace.mk σ = w) with hSdef
    have hA : Finset.univ.filter (fun σ : L →+* ℂ =>
        σ.comp (algebraMap K L) = φ ∧ InfinitePlace.mk σ = w) =
        S.filter (fun σ => σ.comp (algebraMap K L) = φ) := by
      rw [hSdef, Finset.filter_filter]
      apply Finset.filter_congr; intro σ _; exact and_comm
    rw [hA]
    have hsplit := Finset.card_filter_add_card_filter_not (s := S)
      (fun σ : L →+* ℂ => σ.comp (algebraMap K L) = φ)
    have hAB : (S.filter (fun σ : L →+* ℂ => ¬ σ.comp (algebraMap K L) = φ)).card =
        (S.filter (fun σ : L →+* ℂ => σ.comp (algebraMap K L) = φ)).card := by
      refine Finset.card_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_
      · intro σ hσ
        simp only [Finset.mem_coe, Finset.mem_filter, hSdef, Finset.mem_univ, true_and] at hσ ⊢
        refine ⟨by rw [InfinitePlace.mk_conjugate_eq]; exact hσ.1, ?_⟩
        rcases key σ hσ.1 with h | h
        · exact absurd h hσ.2
        · rw [ComplexEmbedding.conjugate_comp]; exact h
      · intro σ hσ
        simp only [Finset.mem_coe, Finset.mem_filter, hSdef, Finset.mem_univ, true_and] at hσ ⊢
        refine ⟨by rw [InfinitePlace.mk_conjugate_eq]; exact hσ.1, ?_⟩
        rw [ComplexEmbedding.conjugate_comp, hσ.2]
        intro h
        exact hφ (ComplexEmbedding.isReal_iff.2 h)
      · intro σ _; exact ComplexEmbedding.involutive_conjugate L σ
      · intro σ _; exact ComplexEmbedding.involutive_conjugate L σ
    omega

/-- **Proposition 8.7, infinite places** (proved): for an infinite place $v$ of $K$ and $\alpha \in L$,
$\prod_{w\mid v}\lVert\alpha\rVert_w = \lVert\mathrm{Nm}_{L/K}\alpha\rVert_v$ (normalized absolute values). -/
@[kb "milne2020ant" "v3.08, Prop. 8.7, p. 138"]
theorem prop_8_7_infinite (v : InfinitePlace K) (α : L) :
    ∏ᶠ (w : InfinitePlace L) (_ : w.comap (algebraMap K L) = v), normAbv L (.inr w) α =
      normAbv K (.inr v) (Algebra.norm K α) := by
  classical
  obtain ⟨φ, rfl⟩ : ∃ φ : K →+* ℂ, InfinitePlace.mk φ = v :=
    ⟨v.embedding, InfinitePlace.mk_embedding v⟩
  let _ : Algebra K ℂ := φ.toAlgebra
  have hnorm := Algebra.norm_eq_prod_embeddings K ℂ α
  have hnorm' : ‖φ (Algebra.norm K α)‖ = ∏ σ : L →ₐ[K] ℂ, ‖σ α‖ := by
    have h2 : ‖φ (Algebra.norm K α)‖ = ‖algebraMap K ℂ (Algebra.norm K α)‖ := rfl
    rw [h2, hnorm, norm_prod]
  set T : Finset (L →+* ℂ) :=
    Finset.univ.filter (fun σ => σ.comp (algebraMap K L) = φ) with hT
  have hprod1 : ∏ σ : L →ₐ[K] ℂ, ‖σ α‖ = ∏ σ ∈ T, ‖σ α‖ := by
    refine Finset.prod_bij (fun σ _ => (σ : L →+* ℂ)) ?_ ?_ ?_ ?_
    · intro σ _
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      ext x
      exact σ.commutes x
    · intro σ _ τ _ h; exact AlgHom.toRingHom_injective h
    · intro τ hτ
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hτ
      refine ⟨{ τ with commutes' := ?_ }, Finset.mem_univ _, rfl⟩
      intro r
      exact congrArg (fun f : K →+* ℂ => f r) hτ
    · intro σ _; rfl
  set W : Finset (InfinitePlace L) :=
    Finset.univ.filter (fun w => w.comap (algebraMap K L) = InfinitePlace.mk φ) with hW
  have hmaps : ∀ σ ∈ T, InfinitePlace.mk σ ∈ W := by
    intro σ hσ
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    simp [hW, InfinitePlace.comap_mk, hσ]
  have hfib : ∏ σ ∈ T, ‖σ α‖ = ∏ w ∈ W, w α ^
      (Finset.univ.filter (fun σ : L →+* ℂ =>
        σ.comp (algebraMap K L) = φ ∧ InfinitePlace.mk σ = w)).card := by
    rw [← Finset.prod_fiberwise_of_maps_to hmaps]
    apply Finset.prod_congr rfl
    intro w _
    rw [Finset.prod_congr rfl (g := fun _ => w α), Finset.prod_const]
    · congr 2
      rw [hT, Finset.filter_filter]
    · intro σ hσ
      simp only [Finset.mem_filter] at hσ
      rw [← hσ.2]; rfl
  have hv : (InfinitePlace.mk φ) (Algebra.norm K α) = ∏ w ∈ W, w α ^
      (Finset.univ.filter (fun σ : L →+* ℂ =>
        σ.comp (algebraMap K L) = φ ∧ InfinitePlace.mk σ = w)).card := by
    rw [InfinitePlace.apply, hnorm', hprod1, hfib]
  rw [finprod_cond_eq_prod_of_cond_iff (t := W) _ (by intro w _; simp [hW])]
  simp only [normAbv_inr]
  rw [hv, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro w hw
  simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  rw [← pow_mul, card_extensions_mul_mult K L φ w hw]

end NormFormula

/-! ## Theorem 8.8 and Aside 8.9 -/

/-- **Theorem 8.8 (product formula)**: for a nonzero $\alpha$ in a number field, $\prod_w\lVert\alpha\rVert_w = 1$, the
product over all primes (finite and infinite places) of the normalized absolute values. Restated from Mathlib's
`NumberField.prod_abs_eq_one` (infinite part $\prod_w w(\alpha)^{m_w}$ times the finite part). -/
@[kb "milne2020ant" "v3.08, Thm. 8.8, p. 138"]
theorem thm_8_8 (K : Type*) [Field K] [NumberField K] {α : K} (hα : α ≠ 0) :
    ∏ᶠ w : FinitePlace K ⊕ InfinitePlace K, normAbv K w α = 1 := by
  have hfin : (fun w : FinitePlace K ⊕ InfinitePlace K => normAbv K w α).HasFiniteMulSupport := by
    refine Set.Finite.subset ((FinitePlace.hasFiniteMulSupport hα).image Sum.inl |>.union
      (Set.finite_range (Sum.inr : InfinitePlace K → _))) ?_
    rintro (w | w) hw
    · exact Or.inl ⟨w, hw, rfl⟩
    · exact Or.inr ⟨w, rfl⟩
  have hunion : (Set.univ : Set (FinitePlace K ⊕ InfinitePlace K)) =
      Set.range Sum.inl ∪ Set.range Sum.inr := by
    ext (w | w) <;> simp
  have hdisj : Disjoint (Set.range (Sum.inl : FinitePlace K → _))
      (Set.range (Sum.inr : InfinitePlace K → _)) := by
    rw [Set.disjoint_left]; rintro _ ⟨a, rfl⟩ ⟨b, h⟩; cases h
  rw [← finprod_mem_univ, hunion, finprod_mem_union' hdisj (hfin.subset Set.inter_subset_right) (hfin.subset Set.inter_subset_right)]
  · rw [finprod_mem_range Sum.inl_injective, finprod_mem_range Sum.inr_injective]
    simp only [normAbv_inl, normAbv_inr]
    have h := NumberField.prod_abs_eq_one hα
    rw [← finprod_eq_prod_of_fintype] at h
    rwa [mul_comm]

/-- **Aside 8.9** (Artin–Whaples, 1945; named statement): let $K$ be a field with a set $V$ of pairwise inequivalent
nontrivial absolute values such that (Axiom I) for every $a \ne 0$, $|a|_v \ne 1$ for only finitely many $v \in V$ and
$\prod_{v\in V}|a|_v = 1$, and (Axiom II) for at least one $v \in V$ the completion $K_v$ is a local field (locally
compact). Then $K$ is a global field (a number field, or a finite extension of $\mathbb F_q(T)$) and every nontrivial
absolute value of $K$ is equivalent to one in $V$. Milne's "set of representatives of primes" is the set $V$. -/
@[kb "milne2020ant" "v3.08, Aside 8.9, p. 138"]
structure Aside8_9 : Prop where
  global : ∀ (K : Type) [Field K] (V : Set (AbsoluteValue K ℝ)),
    (∀ v ∈ V, v.IsNontrivial) → (∀ v ∈ V, ∀ w ∈ V, v.IsEquiv w → v = w) →
    (∀ a : K, a ≠ 0 → {v ∈ V | v a ≠ 1}.Finite ∧ ∏ᶠ (v ∈ V), v a = 1) →
    (∃ v ∈ V, LocallyCompactSpace v.Completion) →
    (Nonempty (NumberField K) ∨
        ∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq) (_ : Algebra (RatFunc Fq) K), FiniteDimensional (RatFunc Fq) K) ∧
      ∀ w : AbsoluteValue K ℝ, w.IsNontrivial → ∃ v ∈ V, w.IsEquiv v

end

end NumberFieldKB.MilneANT
