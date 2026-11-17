import NumberFieldKB.MilneEC.Ch4Selmer
import NumberFieldKB.MilneEC.Ch4SelmerExplicit
import NumberFieldKB.MilneEC.Ch4Prop81Points
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Proposition 8.1: quadratic characters, localization, and the places of $\mathbb Q$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Proposition 8.1 (pdf p. 151).
Tools for comparing the Galois-cohomological Selmer group `selmerGroup ℚ (curveP p) 2` with the quartic torsors
of `Ch4SelmerExplicit`.

* `exists_sqrt_of_hom`: **Kummer theory for $\mathbb Z/2$.**  Over a perfect field $k$ of characteristic $0$,
  a continuous homomorphism $a : G_k \to \mathbb Z/2$ is $\sigma \mapsto [\sigma u \ne u]$ for some
  $u \in \bar k^\times$ with $u^2 \in k$ (Hilbert 90, `hilbert90_of_locally_constant`).
* `mul_mem_range_of_same_sign`: two square roots of elements of $K$ moved by the same automorphisms have product
  in $K$.
* `locTorsion_eq_zero_iff`: a class in $H^1(K, E_n)$ is locally trivial at $K_v$ exactly when its cocycle, pushed
  to $E(\bar K_v)$ along `decompHom`, is $\sigma \mapsto \sigma P - P$.
* `torsorSolvable_map`: local solvability of the quartics is transported along field homomorphisms; with
  `Rat.HeightOneSpectrum.adicCompletion.padicEquiv` and `InfinitePlace.Completion.ringEquivRealOfIsReal` this
  identifies the places of `selmerGroup` with $\mathbb Q_q$ and $\mathbb R$ (`torsorSolvable_adic_iff`,
  `torsorSolvable_infinite_iff`, `mem_isogenySelmer_of_places`, `places_of_mem_isogenySelmer`).
-/

open CategoryTheory groupCohomology WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneEC.Prop81

/-! ### Square roots and quadratic characters -/

section Quad

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- An automorphism maps a square root of an element of $K$ to $\pm$ itself. -/
theorem sq_fixed_sign {u : L} (hu : ∃ d : K, u ^ 2 = algebraMap K L d) (σ : L ≃ₐ[K] L) :
    σ u = u ∨ σ u = -u := by
  obtain ⟨d, hd⟩ := hu
  have h1 : (σ u) ^ 2 = u ^ 2 := by rw [← map_pow, hd, σ.commutes]
  have : (σ u - u) * (σ u + u) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 this with h | h
  · left; linear_combination h
  · right; linear_combination h

/-- Two square roots of elements of $K$, moved by the same automorphisms, have product in $K$. -/
theorem mul_mem_range_of_same_sign [IsGalois K L] {u w : L} (hu : ∃ d : K, u ^ 2 = algebraMap K L d)
    (hw : ∃ d : K, w ^ 2 = algebraMap K L d) (h : ∀ σ : L ≃ₐ[K] L, σ u = u ↔ σ w = w) :
    ∃ k : K, algebraMap K L k = u * w := by
  refine (InfiniteGalois.mem_range_algebraMap_iff_fixed (u * w)).2 fun σ => ?_
  rw [map_mul]
  by_cases hσ : σ u = u
  · rw [hσ, (h σ).1 hσ]
  · have hσw : σ w ≠ w := fun e => hσ ((h σ).2 e)
    rw [(sq_fixed_sign hu σ).resolve_left hσ, (sq_fixed_sign hw σ).resolve_left hσw]
    ring

/-- An element fixed by every automorphism of a Galois extension lies in the base. -/
theorem mem_range_of_fixed [IsGalois K L] {u : L} (h : ∀ σ : L ≃ₐ[K] L, σ u = u) :
    ∃ k : K, algebraMap K L k = u :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed u).2 h

end Quad

section Kummer

variable (k : Type) [Field k] [CharZero k]

/-- **Kummer theory for $\mathbb Z/2$.**  A homomorphism $a : G_k \to \mathbb Z/2$ with open kernel is
$\sigma \mapsto [\sigma u \ne u]$ for a square root $u \ne 0$ of an element of $k$. -/
theorem exists_sqrt_of_hom (a : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → ZMod 2)
    (ha : ∀ σ τ, a (σ * τ) = a σ + a τ) (hopen : IsOpen {σ | a σ = 0}) :
    ∃ u : AlgebraicClosure k, u ≠ 0 ∧ (∃ d : k, u ^ 2 = algebraMap k _ d) ∧
      ∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, σ u = u ↔ a σ = 0 := by
  have hval : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hxx : ∀ x : ZMod 2, x + x = 0 := by decide
  have hxy : ∀ x y : ZMod 2, 0 = x + y → y = x := by decide
  have h1 : a 1 = 0 := by
    have := ha 1 1
    rw [one_mul, hxx] at this
    exact this
  have hinv : ∀ σ, a σ⁻¹ = a σ := by
    intro σ
    have := ha σ σ⁻¹
    rw [mul_inv_cancel, h1] at this
    exact hxy _ _ this
  let H : Subgroup (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :=
    { carrier := {σ | a σ = 0}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at *
        rw [ha, hx, hy, add_zero]
      one_mem' := h1
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq] at *
        rw [hinv, hx] }
  have hHn : H.Normal := ⟨fun n hn g => by
    show a (g * n * g⁻¹) = 0
    have hn' : a n = 0 := hn
    rw [ha, ha, hn', hinv]
    rcases hval (a g) with h | h <;> rw [h] <;> decide⟩
  let s : ZMod 2 → (AlgebraicClosure k)ˣ := fun x => if x = 0 then 1 else -1
  have hs : ∀ x y : ZMod 2, s (x + y) = s x * s y := by
    intro x y
    rcases hval x with rfl | rfl <;> rcases hval y with rfl | rfl <;>
      simp [s, show (1 : ZMod 2) + 1 = 0 from rfl]
  let f : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → (AlgebraicClosure k)ˣ := fun σ => s (a σ)
  have hsfix : ∀ (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (x : ZMod 2), σ • s x = s x := by
    intro σ x
    apply Units.ext
    rcases hval x with h | h <;> simp [s, h, Units.coe_smul]
  have hf : IsMulCocycle₁ f := by
    intro g h
    show s (a (g * h)) = g • s (a h) * s (a g)
    rw [hsfix, ha, hs, mul_comm]
  have hfH : ∀ g h, h ∈ H → f (g * h) = f g := by
    intro g h hh
    have hh' : a h = 0 := hh
    show s (a (g * h)) = s (a g)
    rw [ha, hh', add_zero]
  obtain ⟨β, hβ⟩ := hilbert90_of_locally_constant f hf H hopen hfH
  have hβσ : ∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      σ (β : AlgebraicClosure k) = ((s (a σ) : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) * β := by
    intro σ
    have := congrArg Units.val (hβ σ)
    rw [Units.val_div_eq_div_val, div_eq_iff β.ne_zero] at this
    simpa [Units.coe_smul] using this
  refine ⟨β, β.ne_zero, ?_, fun σ => ?_⟩
  · obtain ⟨d, hd⟩ := mem_range_of_fixed (K := k) (u := (β : AlgebraicClosure k) ^ 2) fun σ => by
      rw [map_pow, hβσ, mul_pow]
      rcases hval (a σ) with h | h <;> simp [s, h]
    exact ⟨d, hd.symm⟩
  · rw [hβσ]
    rcases hval (a σ) with h | h
    · simp [s, h]
    · simp only [s, h, one_ne_zero, ite_false, Units.val_neg, Units.val_one, neg_mul, one_mul]
      constructor
      · intro e
        exfalso
        have : (2 : AlgebraicClosure k) * β = 0 := by linear_combination -e
        rcases mul_eq_zero.1 this with h2 | h2
        · exact two_ne_zero h2
        · exact β.ne_zero h2
      · intro e; exact e.elim

end Kummer

/-! ### Local triviality -/

section Local

variable (W : WeierstrassCurve ℚ) (Kv : Type) [Field Kv] [Algebra ℚ Kv]

/-- A class of $H^1(\mathbb Q, E_n)$ dies in $H^1(K_v, E)$ exactly when the localized cocycle is principal. -/
theorem locTorsion_eq_zero_iff (n : ℤ) (z : cocycles₁ (torsionRep W (AlgebraicClosure ℚ) n)) :
    locTorsion Kv W n (H1π _ z) = 0 ↔
      ∃ P : (W.toAffine⁄(AlgebraicClosure Kv)).Point,
        ∀ σ : AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv,
          Point.map (W' := W.toAffine) (closureEmb Kv)
              ((z (decompHom Kv σ) : torsionPoints W (AlgebraicClosure ℚ) n) :
                (W.toAffine⁄(AlgebraicClosure ℚ)).Point) =
            Point.map (W' := W.toAffine)
              ((AlgEquiv.restrictScalarsHom ℚ σ : AlgebraicClosure Kv ≃ₐ[ℚ] AlgebraicClosure Kv) :
                AlgebraicClosure Kv →ₐ[ℚ] AlgebraicClosure Kv) P - P := by
  change map (decompHom Kv) (localizeTorsion Kv W n) 1 (H1π _ z) = 0 ↔ _
  rw [H1π_comp_map_apply, H1π_eq_zero_iff]
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨P, fun σ => ?_⟩
    have := congrFun hP σ
    rw [d₀₁_hom_apply] at this
    exact this.symm
  · rintro ⟨P, hP⟩
    refine ⟨P, funext fun σ => ?_⟩
    rw [d₀₁_hom_apply]
    exact (hP σ).symm

/-- Transport of square-root behaviour along `closureEmb`: `decompHom σ` fixes `u` exactly when `σ` fixes its
image. -/
theorem decompHom_fixed_iff (σ : AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv) (u : AlgebraicClosure ℚ) :
    decompHom Kv σ u = u ↔ σ (closureEmb Kv u) = closureEmb Kv u := by
  rw [← closureEmb_decompHom]
  exact (closureEmb Kv).injective.eq_iff.symm

end Local

/-! ### The places of $\mathbb Q$ -/

section Places

/-- Local solvability of the quartics is transported along field homomorphisms. -/
theorem torsorSolvable_map {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F'] (f : F →+* F')
    {c d : ℚ} (h : TorsorSolvable F c d) : TorsorSolvable F' c d := by
  obtain ⟨N, M, e, hne, heq⟩ := h
  refine ⟨f N, f M, f e, ?_, ?_⟩
  · rcases hne with h | h
    · exact Or.inl ((map_ne_zero f).2 h)
    · exact Or.inr ((map_ne_zero f).2 h)
  · have := congrArg f heq
    simpa only [map_pow, map_add, map_mul, map_ratCast] using this

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

open IsDedekindDomain NumberField

/-- A field that is a $\mathbb Q$-algebra has characteristic $0$. -/
theorem charZero_of_algebraRat (F : Type*) [Field F] [Algebra ℚ F] : CharZero F :=
  charZero_of_injective_algebraMap (algebraMap ℚ F).injective

/-- The adic completions of $\mathbb Q$ have characteristic $0$ (a local instance of the files on Proposition 8.1:
Tau Ceti declares the general instance `adicCompletion_charZero`). -/
theorem charZero_adicCompletion_rat (v : HeightOneSpectrum (𝓞 ℚ)) : CharZero (v.adicCompletion ℚ) :=
  charZero_of_algebraRat _

attribute [local instance] charZero_adicCompletion_rat

/-- The completions of $\mathbb Q$ at its infinite place have characteristic $0$ (a local instance, like
`charZero_adicCompletion_rat`). -/
theorem charZero_completion_rat (w : InfinitePlace ℚ) : CharZero w.Completion := charZero_of_algebraRat _

attribute [local instance] charZero_completion_rat

theorem torsorSolvable_adic_iff (v : HeightOneSpectrum (𝓞 ℚ)) {c d : ℚ} :
    TorsorSolvable (v.adicCompletion ℚ) c d ↔
      TorsorSolvable ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] c d := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  let r : v.adicCompletion ℚ ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] := RingEquivClass.toRingEquiv e
  exact ⟨torsorSolvable_map r.toRingHom, torsorSolvable_map r.symm.toRingHom⟩

theorem torsorSolvable_infinite_iff (w : InfinitePlace ℚ) {c d : ℚ} :
    TorsorSolvable w.Completion c d ↔ TorsorSolvable ℝ c d := by
  have hw : w.IsReal := Subsingleton.elim Rat.infinitePlace w ▸ Rat.isReal_infinitePlace
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  exact ⟨torsorSolvable_map e.toRingHom, torsorSolvable_map e.symm.toRingHom⟩

/-- Membership in `isogenySelmer` from solvability at the places of `selmerGroup`. -/
theorem mem_isogenySelmer_of_places {c d : ℚ} (hd : d ≠ 0)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 ℚ), TorsorSolvable (v.adicCompletion ℚ) c d)
    (hinf : ∀ w : InfinitePlace ℚ, TorsorSolvable w.Completion c d) : d ∈ isogenySelmer c := by
  refine ⟨hd, fun q _ => ?_, (torsorSolvable_infinite_iff Rat.infinitePlace).1 (hinf _)⟩
  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = q :=
    ⟨Rat.HeightOneSpectrum.primesEquiv.symm ⟨q, Fact.out⟩, by simp⟩
  have := (torsorSolvable_adic_iff v).1 (hfin v)
  subst hv
  exact this

/-- Solvability at the places of `selmerGroup` from membership in `isogenySelmer`. -/
theorem places_of_mem_isogenySelmer {c d : ℚ} (h : d ∈ isogenySelmer c) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), TorsorSolvable (v.adicCompletion ℚ) c d) ∧
      ∀ w : InfinitePlace ℚ, TorsorSolvable w.Completion c d :=
  ⟨fun v => (torsorSolvable_adic_iff v).2 (h.2.1 _),
    fun w => (torsorSolvable_infinite_iff w).2 h.2.2⟩

end Places

end NumberFieldKB.MilneEC.Prop81
