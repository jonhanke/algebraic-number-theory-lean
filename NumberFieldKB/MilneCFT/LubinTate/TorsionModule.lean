import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.SetTheory.Cardinal.Finite
import QuadFormsKB.Citation

/-!
# Lemma 3.3 of Milne, *Class Field Theory*, Chapter I

A cyclicity criterion for torsion modules over a discrete valuation ring, used for the module $\Lambda_n$ of
Lubin–Tate torsion points (Proposition 3.4).
-/

noncomputable section

namespace NumberFieldKB.MilneCFT


section helpers

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {π : A}
  {M : Type*} [AddCommGroup M] [Module A M]

theorem mem_ker_pow_iff (k : ℕ) (x : M) :
    x ∈ LinearMap.ker (π ^ k • LinearMap.id : M →ₗ[A] M) ↔ π ^ k • x = 0 := by
  simp [LinearMap.mem_ker]

theorem card_quot_pow (hπ : Irreducible π) (n : ℕ) :
    Nat.card (A ⧸ Ideal.span {π ^ n}) = Nat.card (A ⧸ Ideal.span {π}) ^ n := by
  have hP : Ideal.span {π} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero
  haveI : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ.prime
  have := cardQuot_pow_of_prime (S := A) (P := Ideal.span {π}) hP (i := n)
  rw [Ideal.span_singleton_pow] at this
  simpa [Submodule.cardQuot_apply] using this

theorem card_ker_pow_aux (hπ : Irreducible π) [Finite (A ⧸ Ideal.span {π})]
    (h1 : Nat.card (LinearMap.ker (π • LinearMap.id : M →ₗ[A] M)) = Nat.card (A ⧸ Ideal.span {π}))
    (hsurj : Function.Surjective (π • LinearMap.id : M →ₗ[A] M)) (n : ℕ) :
    Nat.card (LinearMap.ker (π ^ n • LinearMap.id : M →ₗ[A] M)) =
      Nat.card (A ⧸ Ideal.span {π}) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨0⟩⟩
    have ha : a.1 = 0 := by simpa using a.2
    have hb : b.1 = 0 := by simpa using b.2
    exact Subtype.ext (ha.trans hb.symm)
  | succ n ih =>
    let f : LinearMap.ker (π ^ (n+1) • LinearMap.id : M →ₗ[A] M) →ₗ[A]
        LinearMap.ker (π ^ n • LinearMap.id : M →ₗ[A] M) :=
      (π • LinearMap.id : M →ₗ[A] M).restrict (fun x hx => by
        rw [mem_ker_pow_iff] at hx ⊢
        simp only [LinearMap.smul_apply, LinearMap.id_apply]
        rw [smul_smul, ← pow_succ, hx])
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hsurj y
      simp only [LinearMap.smul_apply, LinearMap.id_apply] at hx
      have hy' := (mem_ker_pow_iff n y).1 hy
      refine ⟨⟨x, (mem_ker_pow_iff _ x).2 ?_⟩, ?_⟩
      · rw [pow_succ, mul_smul, hx, hy']
      · apply Subtype.ext
        simpa [f] using hx
    have hker : Nat.card (LinearMap.ker f) =
        Nat.card (LinearMap.ker (π • LinearMap.id : M →ₗ[A] M)) := by
      apply Nat.card_congr
      refine
        { toFun := fun x => ⟨x.1.1, ?_⟩
          invFun := fun x => ⟨⟨x.1, ?_⟩, ?_⟩
          left_inv := fun x => rfl
          right_inv := fun x => rfl }
      · have h := congrArg Subtype.val (LinearMap.mem_ker.1 x.2)
        exact LinearMap.mem_ker.2 h
      · have := (LinearMap.mem_ker.1 x.2)
        simp only [LinearMap.smul_apply, LinearMap.id_apply] at this
        rw [mem_ker_pow_iff, pow_succ, mul_smul, this, smul_zero]
      · apply LinearMap.mem_ker.2
        apply Subtype.ext
        have := (LinearMap.mem_ker.1 x.2)
        simpa [f] using this
    have e := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
    rw [Nat.card_congr (f.quotKerEquivOfSurjective hf).toEquiv, hker, ih, h1] at e
    rw [e, pow_succ]; ring

end helpers

/-- **Lemma 3.3** (Milne, *CFT*, I): let $A$ be a discrete valuation ring with prime element $\pi$ and finite residue
field $A/(\pi)$ of $q$ elements, and $M$ an $A$-module with $M_n = \ker(\pi^n : M \to M)$. If (a) $M_1$ has $q$
elements and (b) $\pi : M \to M$ is surjective, then $M_n \cong A/(\pi^n)$; in particular $|M_n| = q^n$. (Milne's
$A$ is $\mathcal O_K$; the lemma holds for any discrete valuation ring with finite residue field.) -/
@[kb "milne2020cft" "Ch. I, Lemma 3.3"]
theorem lemma_3_3 {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {π : A}
    (hπ : Irreducible π) [Finite (A ⧸ Ideal.span {π})] {M : Type*} [AddCommGroup M] [Module A M]
    (h1 : Nat.card (LinearMap.ker (π • LinearMap.id : M →ₗ[A] M)) = Nat.card (A ⧸ Ideal.span {π}))
    (hsurj : Function.Surjective (π • LinearMap.id : M →ₗ[A] M)) (n : ℕ) :
    Nonempty (LinearMap.ker (π ^ n • LinearMap.id : M →ₗ[A] M) ≃ₗ[A] A ⧸ Ideal.span {π ^ n}) := by
  have hcard := card_ker_pow_aux hπ h1 hsurj
  have hq2 : 1 < Nat.card (A ⧸ Ideal.span {π}) := by
    have hne : Ideal.span {π} ≠ ⊤ := fun h => hπ.not_isUnit (Ideal.span_singleton_eq_top.1 h)
    haveI : Nontrivial (A ⧸ Ideal.span {π}) := Ideal.Quotient.nontrivial_iff.2 hne
    exact Finite.one_lt_card
  cases n with
  | zero =>
    haveI : Subsingleton (A ⧸ Ideal.span {π ^ 0}) := by
      rw [pow_zero, Ideal.span_singleton_one]
      exact Ideal.Quotient.subsingleton_iff.2 rfl
    haveI : Subsingleton (LinearMap.ker (π ^ 0 • LinearMap.id : M →ₗ[A] M)) :=
      ⟨fun a b => Subtype.ext (by
        have ha : a.1 = 0 := by simpa using a.2
        have hb : b.1 = 0 := by simpa using b.2
        exact ha.trans hb.symm)⟩
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  | succ m =>
    have hpos : ∀ k, Nat.card (LinearMap.ker (π ^ k • LinearMap.id : M →ₗ[A] M)) ≠ 0 := fun k => by
      rw [hcard k]; exact pow_ne_zero _ (by omega)
    haveI : Finite (LinearMap.ker (π ^ m • LinearMap.id : M →ₗ[A] M)) :=
      Nat.finite_of_card_ne_zero (hpos m)
    haveI : Finite (LinearMap.ker (π ^ (m+1) • LinearMap.id : M →ₗ[A] M)) :=
      Nat.finite_of_card_ne_zero (hpos (m+1))
    obtain ⟨x, hx, hxm⟩ : ∃ x ∈ LinearMap.ker (π ^ (m+1) • LinearMap.id : M →ₗ[A] M),
        π ^ m • x ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have hle : LinearMap.ker (π ^ (m+1) • LinearMap.id : M →ₗ[A] M) ≤
          LinearMap.ker (π ^ m • LinearMap.id : M →ₗ[A] M) := fun x hx =>
        (mem_ker_pow_iff m x).2 (hcon x hx)
      have := Nat.card_le_card_of_injective _ (Submodule.inclusion_injective hle)
      rw [hcard, hcard] at this
      have h2 : Nat.card (A ⧸ Ideal.span {π}) ^ m < Nat.card (A ⧸ Ideal.span {π}) ^ (m+1) :=
        Nat.pow_lt_pow_right hq2 (by omega)
      omega
    let x' : LinearMap.ker (π ^ (m+1) • LinearMap.id : M →ₗ[A] M) := ⟨x, hx⟩
    let φ := LinearMap.toSpanSingleton A (LinearMap.ker (π ^ (m+1) • LinearMap.id : M →ₗ[A] M)) x'
    have hφ : ∀ a : A, φ a = 0 ↔ a • x = 0 := fun a => by
      simp [φ, x', Subtype.ext_iff]
    have hker : LinearMap.ker φ = Ideal.span {π ^ (m+1)} := by
      have hmem : π ^ (m+1) ∈ LinearMap.ker φ :=
        LinearMap.mem_ker.2 ((hφ _).2 ((mem_ker_pow_iff _ x).1 hx))
      have hI : LinearMap.ker φ ≠ ⊥ := fun h => by
        rw [h] at hmem
        exact pow_ne_zero _ hπ.ne_zero (Submodule.mem_bot A |>.1 hmem)
      obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hπ
      rw [hk] at hmem ⊢
      have h1' : π ^ k ∣ π ^ (m+1) := Ideal.mem_span_singleton.1 hmem
      have hk1 : k ≤ m + 1 := (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).1 h1'
      have hk2 : ¬ k ≤ m := fun hkm => by
        have : π ^ m ∈ LinearMap.ker φ := by
          rw [hk]; exact Ideal.mem_span_singleton.2 (pow_dvd_pow π hkm)
        exact hxm ((hφ _).1 (LinearMap.mem_ker.1 this))
      have : k = m + 1 := by omega
      rw [this]
    let ψ := Submodule.liftQ (Ideal.span {π ^ (m+1)}) φ (le_of_eq hker.symm)
    have hinj : Function.Injective ψ :=
      LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot' _ φ hker.symm)
    have hbij : Function.Bijective ψ := by
      refine hinj.bijective_of_nat_card_le ?_
      rw [hcard, card_quot_pow hπ]
    exact ⟨(LinearEquiv.ofBijective ψ hbij).symm⟩

/-- The cardinality part of Lemma 3.3: $|M_n| = q^n$. -/
@[kb "milne2020cft" "Ch. I, Lemma 3.3 (|M_n| = q^n)"]
theorem lemma_3_3_card {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {π : A}
    (hπ : Irreducible π) [Finite (A ⧸ Ideal.span {π})] {M : Type*} [AddCommGroup M] [Module A M]
    (h1 : Nat.card (LinearMap.ker (π • LinearMap.id : M →ₗ[A] M)) = Nat.card (A ⧸ Ideal.span {π}))
    (hsurj : Function.Surjective (π • LinearMap.id : M →ₗ[A] M)) (n : ℕ) :
    Nat.card (LinearMap.ker (π ^ n • LinearMap.id : M →ₗ[A] M)) = Nat.card (A ⧸ Ideal.span {π}) ^ n :=
  card_ker_pow_aux hπ h1 hsurj n

end NumberFieldKB.MilneCFT
