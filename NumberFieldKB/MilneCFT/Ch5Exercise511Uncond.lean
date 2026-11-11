import NumberFieldKB.MilneCFT.Ch5IdelicMain
import NumberFieldKB.MilneCFT.Ch7.IdeleOpen
import NumberFieldKB.MilneCFT.Ch7.Prop68TauCeti
import NumberFieldKB.MilneCFT.Ch8.Powers
import NumberFieldKB.WeilBNT.LocalPowers
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Henselian
import Mathlib.Data.Finset.Functor
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star

/-!
# Milne, *Class Field Theory*, V, Exercise 5.11: a subgroup of finite index of the idele class group that is not open

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter V, Exercise 5.11, p. 182.

Proves `Exercise5_11 K` unconditionally (`exercise5_11`). The subgroup is the image of the kernel of a discontinuous
quadratic character $\Lambda$ of the idele group, built from an ultrafilter (helpers in `Ex511`):

* `exists_local_char`: for every finite prime $v$, a character $\mu_v : K_v^\times\to\{\pm1\}$ killing squares and
  nontrivial on some unit (the unit group has a nonsquare by `Ch7.prop6_8`; `exists_sq_char` separates it from the
  squares in the $\mathbb F_2$-vector space $K_v^\times/K_v^{\times 2}$).
* `isLocalPow_of_frob`, `infinite_isLocalPow`: for $a_1,\dots,a_k\in K^\times$, infinitely many primes $v$ have all
  $a_i$ squares in $K_v$ (primes of trivial Frobenius in the splitting field of $\prod(X^2-a_i)$, by Chebotarev
  `NumberFieldKB.HilbertClassField.setOf_frobAt_eq_infinite`; Euler's criterion in the residue field, then Hensel).
* `exists_ultrafilter`: an ultrafilter $U$ on the primes containing the cofinite sets and, for each $a\in K^\times$,
  the primes where $a$ is a square in $K_v$.
* `Lam`: $\Lambda(x)=\lim_U\mu_v(x_v)$ (`limU`, limit in a finite group along an ultrafilter); `lam_principal`:
  $\Lambda$ is trivial on $K^\times$; `not_isOpen_ker_lam`: $\ker\Lambda$ is not open (an open kernel would contain
  an idele equal to a `mu`-nontrivial unit at all primes outside a finite set, `mkIdele`, `Ch7.exists_finset_of_isOpen`).
* `exercise5_11`: $N=$ image of $\ker\Lambda$ in $\mathbb I_K/K^\times$ has index at most $2$ and preimage
  $\ker\Lambda$, hence is not open.
-/

open IsDedekindDomain NumberField
open scoped Topology nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT

namespace Ex511

variable {K : Type} [Field K] [NumberField K]

/-- A quadratic character of an abelian group killing squares and nontrivial on a nonsquare. -/
theorem exists_sq_char {G : Type*} [CommGroup G] (u0 : G) (hnsq : ∀ y : G, y ^ 2 ≠ u0) :
    ∃ μ : G →* Multiplicative (ZMod 2), (∀ y, μ (y ^ 2) = 1) ∧ μ u0 ≠ 1 := by
  set H : Subgroup G := (powMonoidHom 2 : G →* G).range with hH
  have hHsq : ∀ y : G, y ^ 2 ∈ H := fun y => ⟨y, rfl⟩
  have hQ : ∀ x : Additive (G ⧸ H), 2 • x = 0 := by
    intro x
    have key : ∀ q : G ⧸ H, 2 • Additive.ofMul q = (0 : Additive (G ⧸ H)) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H y =>
        rw [← ofMul_pow, ← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).2 (hHsq y)]
        rfl
    exact key (Additive.toMul x)
  let _inst : Module (ZMod 2) (Additive (G ⧸ H)) := by
    have := AddCommGroup.zmodModule (n := 2) hQ
    exact this
  have hx : Additive.ofMul (QuotientGroup.mk (s := H) u0) ∉ (⊥ : Submodule (ZMod 2) (Additive (G ⧸ H))) := by
    intro h
    rw [Submodule.mem_bot] at h
    have : (u0 : G ⧸ H) = 1 := h
    rw [QuotientGroup.eq_one_iff] at this
    obtain ⟨y, hy⟩ := this
    exact hnsq y hy
  obtain ⟨f, hf, -⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  let μ : G →* Multiplicative (ZMod 2) :=
    { toFun := fun y => Multiplicative.ofAdd (f (Additive.ofMul (QuotientGroup.mk (s := H) y)))
      map_one' := by
        have : Additive.ofMul (QuotientGroup.mk (s := H) (1 : G)) = 0 := rfl
        simp
      map_mul' := by
        intro a b
        have : Additive.ofMul (QuotientGroup.mk (s := H) (a * b)) =
          Additive.ofMul (QuotientGroup.mk (s := H) a) + Additive.ofMul (QuotientGroup.mk (s := H) b) := rfl
        simp }
  refine ⟨μ, fun y => ?_, ?_⟩
  · show Multiplicative.ofAdd (f (Additive.ofMul (QuotientGroup.mk (s := H) (y ^ 2)))) = 1
    rw [(QuotientGroup.eq_one_iff _).2 (hHsq y)]
    have : Additive.ofMul (1 : G ⧸ H) = 0 := rfl
    rw [this, map_zero]; rfl
  · intro h
    apply hf
    have : Multiplicative.ofAdd (f (Additive.ofMul (QuotientGroup.mk (s := H) u0))) = 1 := h
    exact this


/-- Every local unit group has a unit that is not a square, and a quadratic character of $K_v^\times$ that kills
squares and is nontrivial on this unit. -/
theorem exists_local_char (v : HeightOneSpectrum (𝓞 K)) :
    ∃ μ : (v.adicCompletion K)ˣ →* Multiplicative (ZMod 2),
      (∀ y, μ (y ^ 2) = 1) ∧ ∃ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 ∧ μ u ≠ 1 := by
  have h68 := Ch7.prop6_8 K
  have hidx := h68.index_pow_units v 2 (by norm_num)
  have hroots : 2 ≤ Ch7.numRootsOfUnity (v.adicCompletion K) 2 := by
    unfold Ch7.numRootsOfUnity
    have : Finite (rootsOfUnity 2 (v.adicCompletion K)) := inferInstance
    have h1 : Nontrivial (rootsOfUnity 2 (v.adicCompletion K)) := by
      refine ⟨⟨1, ⟨-1, by simp⟩, ?_⟩⟩
      intro h
      have h2 : ((1 : (v.adicCompletion K)ˣ)) = -1 := congrArg Subtype.val h
      have h3 : (1 : v.adicCompletion K) = -1 := congrArg Units.val h2
      have h4 : (2 : v.adicCompletion K) = 0 := by linear_combination h3
      exact two_ne_zero h4
    exact Nat.succ_le_of_lt (Finite.one_lt_card)
  have hne : (powMonoidHom 2 : Ch7.localUnits K v →* Ch7.localUnits K v).range ≠ ⊤ := by
    intro htop
    rw [← Subgroup.index_eq_one] at htop
    rw [hidx] at htop
    have := Nat.eq_one_of_mul_eq_one_right htop
    omega
  obtain ⟨u0, hu0⟩ : ∃ u0 : Ch7.localUnits K v, u0 ∉ (powMonoidHom 2 : Ch7.localUnits K v →* Ch7.localUnits K v).range := by
    by_contra hcon
    apply hne
    rw [eq_top_iff]
    intro x _
    by_contra hx
    exact hcon ⟨x, hx⟩
  have hu0v : Valued.v ((u0 : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.1 u0.2
  have hnsq : ∀ y : (v.adicCompletion K)ˣ, y ^ 2 ≠ (u0 : (v.adicCompletion K)ˣ) := by
    intro y hy
    have h1 : Valued.v (y : v.adicCompletion K) ^ 2 = 1 := by
      rw [← map_pow, ← hu0v, ← hy]
      simp
    have h2 : Valued.v (y : v.adicCompletion K) = 1 := ((pow_eq_one_iff).1 h1).resolve_right (by norm_num)
    have hy' : y ∈ Ch7.localUnits K v := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2 h2
    exact hu0 ⟨⟨y, hy'⟩, Subtype.ext hy⟩
  obtain ⟨μ, h1, h2⟩ := exists_sq_char (u0 : (v.adicCompletion K)ˣ) hnsq
  exact ⟨μ, h1, u0, hu0v, h2⟩

open NumberFieldKB.MilneCFT.Ch8 in
/-- If a prime $Q$ of $\\mathcal O_M$ above $v$ has trivial Frobenius ($y^{Nv} \\equiv y \\bmod Q$ for all $y$), and
$\\sqrt a\\in M$, then (for $v\\nmid 2$ and $a$ a $v$-unit) $a$ is a square in $K_v$. -/
theorem isLocalPow_of_frob {M : Type} [Field M] [NumberField M] [Algebra K M] (a : K) (β : M)
    (hβ : β ^ 2 = algebraMap K M a) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ Sset 2 {a})
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (hF : ∀ y : 𝓞 M, y ^ Ideal.absNorm v.asIdeal - y ∈ Q) : IsLocalPow 2 a v := by
  obtain ⟨hnv, hav⟩ := (notMem_Sset_iff v 2 a).1 hv
  obtain ⟨d, c, hd, hc, hcd⟩ := exists_scale v (n := 2) (by norm_num) a hav
  obtain ⟨B, hB⟩ := exists_beta (n := 2) (by norm_num) a M β hβ d c hcd
  have hQ_under : ∀ x : 𝓞 K, x ∈ v.asIdeal → algebraMap (𝓞 K) (𝓞 M) x ∈ Q := by
    intro x hx
    have : x ∈ Q.under (𝓞 K) := by rwa [← Ideal.over_def Q v.asIdeal]
    exact this
  have hQ_notin : ∀ x : 𝓞 K, algebraMap (𝓞 K) (𝓞 M) x ∈ Q → x ∈ v.asIdeal := fun x hx => by
    rw [Ideal.over_def Q v.asIdeal]; exact hx
  have e1 : (B : M) ^ 2 = algebraMap K M c := by
    rw [hB, mul_pow, hβ, ← map_pow, ← map_mul, hcd]
  have hBn : B ^ 2 = algebraMap (𝓞 K) (𝓞 M) c := RingOfIntegers.ext e1
  have hcQ : algebraMap (𝓞 K) (𝓞 M) c ∉ Q := fun h => hc (hQ_notin c h)
  have hBQ : B ∉ Q := fun h => hcQ (hBn ▸ Q.pow_mem_of_mem h 2 (by norm_num))
  -- the residue field
  have := v.isMaximal
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let _ : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  let _ : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hq : Ideal.absNorm v.asIdeal = Fintype.card (𝓞 K ⧸ v.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hchar : ringChar (𝓞 K ⧸ v.asIdeal) ≠ 2 := by
    intro h
    apply hnv
    have h2 : ((2 : ℕ) : 𝓞 K ⧸ v.asIdeal) = 0 := by
      have := ringChar.spec (𝓞 K ⧸ v.asIdeal) 2
      rw [h] at this
      exact this.2 (dvd_refl 2)
    have h3 : (Ideal.Quotient.mk v.asIdeal) ((2 : ℕ) : 𝓞 K) = 0 := by
      rw [map_natCast]; exact h2
    exact (Ideal.Quotient.eq_zero_iff_mem).1 h3
  have hodd := FiniteField.odd_card_of_char_ne_two hchar
  set q := Ideal.absNorm v.asIdeal with hqdef
  have hq2 : q = 2 * (q / 2) + 1 := by omega
  have hq1 : B * (B ^ (q - 1) - 1) ∈ Q := by
    have := hF B
    have e : B * (B ^ (q - 1) - 1) = B ^ q - B := by
      obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ]; ring
    rwa [e]
  have hq3 : B ^ (q - 1) - 1 ∈ Q := by
    rcases Ideal.IsPrime.mem_or_mem inferInstance hq1 with h | h
    · exact absurd h hBQ
    · exact h
  have hq4 : algebraMap (𝓞 K) (𝓞 M) (c ^ (q / 2) - 1) ∈ Q := by
    have e : B ^ (q - 1) = algebraMap (𝓞 K) (𝓞 M) c ^ (q / 2) := by
      rw [← hBn, ← pow_mul]; congr 1; omega
    rw [map_sub, map_pow, map_one, ← e]
    exact hq3
  have hq5 : c ^ (q / 2) - 1 ∈ v.asIdeal := hQ_notin _ hq4
  have hq6 : (Ideal.Quotient.mk v.asIdeal c) ^ (Fintype.card (𝓞 K ⧸ v.asIdeal) / 2) = 1 := by
    rw [← hq, ← sub_eq_zero, ← map_pow, ← map_one (Ideal.Quotient.mk v.asIdeal), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hq5
  have hc0 : Ideal.Quotient.mk v.asIdeal c ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨r, hr⟩ := (FiniteField.isSquare_iff hchar hc0).2 hq6
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hw : c - w * w ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hr, map_mul, sub_self]
  have hd0 : Ideal.Quotient.mk v.asIdeal d ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨e', he'⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk v.asIdeal d)⁻¹
  have hed : e' * d - 1 ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, he', map_one, inv_mul_cancel₀ hd0, sub_self]
  refine (exists_approx_iff_isLocalPow 2 (by norm_num) a v hv).1 ⟨e' * w, ?_⟩
  have hmem : (d * (e' * w)) ^ 2 - c ∈ v.asIdeal := by
    have : (d * (e' * w)) ^ 2 - c = (e' * d - 1) * w * ((e' * d + 1) * w) + (w * w - c) := by ring
    rw [this]
    refine v.asIdeal.add_mem (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hed)) ?_
    have := v.asIdeal.neg_mem hw
    simpa using this
  have hval : v.valuation K (algebraMap (𝓞 K) K ((d * (e' * w)) ^ 2 - c)) < 1 :=
    (v.valuation_lt_one_iff_mem (K := K) _).2 hmem
  have hcd' : algebraMap (𝓞 K) K c = (algebraMap (𝓞 K) K d) ^ 2 * a := hcd
  have e2 : algebraMap (𝓞 K) K ((d * (e' * w)) ^ 2 - c) =
      (algebraMap (𝓞 K) K d) ^ 2 * ((algebraMap (𝓞 K) K (e' * w)) ^ 2 - a) := by
    rw [map_sub, map_pow, hcd', map_mul]; ring
  have hd1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 := (v.valuation_eq_one_iff_notMem (K := K)).2 hd
  rw [e2, map_mul, map_pow, hd1] at hval
  simpa using hval

open NumberFieldKB.MilneCFT.Ch8 NumberFieldKB.Chebotarev Polynomial in
/-- **Finite intersection property**: for finitely many $a_1,\\dots,a_k\\in K^\\times$, infinitely many primes $v$ have
every $a_i$ a square in $K_v$ (Chebotarev in the splitting field of $\\prod(X^2-a_i)$). -/
theorem infinite_isLocalPow (s : Finset Kˣ) :
    {v : HeightOneSpectrum (𝓞 K) | ∀ a ∈ s, IsLocalPow 2 (a : K) v}.Infinite := by
  classical
  set p : K[X] := ∏ a ∈ s, (X ^ 2 - C (a : K)) with hp
  let M := p.SplittingField
  have : NumberField M := NumberField.of_module_finite K M
  have hp0 : p ≠ 0 := by
    rw [hp, Finset.prod_ne_zero_iff]
    intro a _
    exact (monic_X_pow_sub_C (a : K) (by norm_num : (2 : ℕ) ≠ 0)).ne_zero
  have hsplit := SplittingField.splits p
  have hroot : ∀ a ∈ s, ∃ β : M, β ^ 2 = algebraMap K M (a : K) := by
    intro a ha
    have hdvd : (X ^ 2 - C (a : K)) ∣ p := Finset.dvd_prod_of_mem _ ha
    have hs : Splits ((X ^ 2 - C (a : K)).map (algebraMap K M)) :=
      Splits.of_dvd hsplit (Polynomial.map_ne_zero hp0) (Polynomial.map_dvd _ hdvd)
    obtain ⟨β, hβ⟩ := hs.exists_eval_eq_zero (by
      rw [degree_map]
      rw [degree_X_pow_sub_C (by norm_num) _]
      norm_num)
    refine ⟨β, ?_⟩
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub, eval_pow, eval_X, eval_C] at hβ
    exact sub_eq_zero.1 hβ
  have hF : (⋃ a ∈ s, Sset 2 {(a : K)} : Set (HeightOneSpectrum (𝓞 K))).Finite :=
    Set.Finite.biUnion s.finite_toSet fun a _ => Sset_finite 2 (by norm_num) (a : K) a.ne_zero
  refine ((NumberFieldKB.HilbertClassField.setOf_frobAt_eq_infinite K M 1).sdiff hF).mono ?_
  rintro v ⟨⟨-, Q, hQ⟩, hvF⟩ a ha
  have hvS : v ∉ Sset 2 {(a : K)} := fun h => hvF (Set.mem_biUnion ha h)
  obtain ⟨β, hβ⟩ := hroot a ha
  have hQ1 := Q.2.1
  have hQ2 := Q.2.2
  have hσ := isArithFrobAt_frobAt K M v Q
  rw [hQ] at hσ
  have hcard : Nat.card (𝓞 K ⧸ Q.1.under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
    rw [← Ideal.over_def Q.1 v.asIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  refine isLocalPow_of_frob (a : K) β hβ v hvS Q.1 fun y => ?_
  have := hσ y
  rw [hcard] at this
  have h2 := Q.1.neg_mem this
  simpa using h2

open NumberFieldKB.MilneCFT.Ch8 Filter in
/-- An ultrafilter on the primes containing all cofinite sets and, for every $a\\in K^\\times$, the set of primes at
which $a$ is a square in $K_v$ (the finite intersection property is `infinite_isLocalPow`). -/
theorem exists_ultrafilter : ∃ U : Ultrafilter (HeightOneSpectrum (𝓞 K)),
    (∀ A : Set (HeightOneSpectrum (𝓞 K)), Aᶜ.Finite → A ∈ U) ∧
      ∀ a : Kˣ, {v | IsLocalPow 2 (a : K) v} ∈ U := by
  classical
  let S : Finset Kˣ → Set (HeightOneSpectrum (𝓞 K)) := fun s => {v | ∀ a ∈ s, IsLocalPow 2 (a : K) v}
  let F : Filter (HeightOneSpectrum (𝓞 K)) := Filter.cofinite ⊓ ⨅ s, 𝓟 (S s)
  have hdir : Directed (· ≥ ·) fun s : Finset Kˣ => 𝓟 (S s) := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · show 𝓟 (S (s ∪ t)) ≤ 𝓟 (S s)
      rw [principal_mono]
      intro v hv a ha
      exact hv a (Finset.mem_union_left _ ha)
    · show 𝓟 (S (s ∪ t)) ≤ 𝓟 (S t)
      rw [principal_mono]
      intro v hv a ha
      exact hv a (Finset.mem_union_right _ ha)
  have hne : F.NeBot := by
    rw [Filter.inf_neBot_iff]
    intro A hA B hB
    rw [Filter.mem_iInf_of_directed hdir] at hB
    obtain ⟨i, hi⟩ := hB
    rw [mem_principal] at hi
    have hinf : (S i).Infinite := infinite_isLocalPow i
    have hA' : Aᶜ.Finite := Filter.mem_cofinite.1 hA
    obtain ⟨x, hx1, hx2⟩ := (hinf.sdiff hA').nonempty
    exact ⟨x, by simpa using hx2, hi hx1⟩
  refine ⟨Ultrafilter.of F, fun A hA => ?_, fun a => ?_⟩
  · exact (Ultrafilter.of_le F) (Filter.mem_inf_of_left (Filter.mem_cofinite.2 hA))
  · refine Filter.mem_of_superset ((Ultrafilter.of_le F) (Filter.mem_inf_of_right
      (Filter.mem_iInf_of_mem ({a} : Finset Kˣ) (Filter.mem_principal_self _)))) ?_
    intro v hv
    exact hv a (Finset.mem_singleton_self a)

/-! ### Limits along an ultrafilter in a finite group -/

section Lim

variable {ι : Type*} {G : Type*} [Finite G]

/-- The limit of $f : \\iota \\to G$ along an ultrafilter $U$ ($G$ finite): the unique $g$ with $\\{f = g\\}\\in U$. -/
def limU (U : Ultrafilter ι) (f : ι → G) : G :=
  Classical.choose (Ultrafilter.eq_pure_of_finite (U.map f))

theorem limU_spec (U : Ultrafilter ι) (f : ι → G) : {i | f i = limU U f} ∈ U := by
  have h := Classical.choose_spec (Ultrafilter.eq_pure_of_finite (U.map f))
  have h : Ultrafilter.map f U = pure (limU U f) := h
  have h2 : ({limU U f} : Set G) ∈ (pure (limU U f) : Ultrafilter G) := Filter.mem_pure.2 rfl
  rw [← h] at h2
  exact h2

theorem limU_eq (U : Ultrafilter ι) (f : ι → G) (g : G) (h : {i | f i = g} ∈ U) : limU U f = g := by
  obtain ⟨i, hi1, hi2⟩ := Filter.nonempty_of_mem (Filter.inter_mem (limU_spec U f) h)
  exact hi1.symm.trans hi2

theorem limU_mul [Mul G] (U : Ultrafilter ι) (f g : ι → G) : limU U (f * g) = limU U f * limU U g := by
  refine limU_eq U _ _ ?_
  filter_upwards [limU_spec U f, limU_spec U g] with i h1 h2
  show f i * g i = _
  rw [h1, h2]

theorem limU_one [One G] (U : Ultrafilter ι) : limU U (1 : ι → G) = 1 := by
  refine limU_eq U _ _ ?_
  exact Filter.univ_mem' fun i => rfl

end Lim

/-! ### The idele components -/

variable (K) in
/-- The component at $v$ of an idele, as a unit of $K_v$. -/
def ideleComp (v : HeightOneSpectrum (𝓞 K)) : IdeleGroup (𝓞 K) K →* (v.adicCompletion K)ˣ :=
  Units.map ((RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v).comp
    (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))).toMonoidHom

theorem ideleComp_val (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup (𝓞 K) K) :
    ((ideleComp K v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : AdeleRing (𝓞 K) K).2 v := rfl

theorem ideleComp_unitEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    ((ideleComp K v (IdeleGroup.unitEmbedding (𝓞 K) K a) : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      algebraMap K (v.adicCompletion K) a := by
  rw [ideleComp_val]
  rfl

/-- The idele with trivial infinite components and finite components $g_v$ (units of $K_v$ of valuation $1$). -/
def mkIdele (g : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (hg : ∀ v, Valued.v ((g v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1) : IdeleGroup (𝓞 K) K where
  val := ((1 : InfiniteAdeleRing K),
    (RestrictedProduct.mk (fun v => ((g v : (v.adicCompletion K)ˣ) : v.adicCompletion K))
      (Filter.Eventually.of_forall fun v => by
        rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]; exact (hg v).le) :
      FiniteAdeleRing (𝓞 K) K))
  inv := ((1 : InfiniteAdeleRing K),
    (RestrictedProduct.mk (fun v => (((g v)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))
      (Filter.Eventually.of_forall fun v => by
        rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
        simp [hg v]) :
      FiniteAdeleRing (𝓞 K) K))
  val_inv := by
    refine Prod.ext (one_mul (1 : InfiniteAdeleRing K)) ?_
    apply RestrictedProduct.ext
    intro v
    exact Units.mul_inv (g v)
  inv_val := by
    refine Prod.ext (one_mul (1 : InfiniteAdeleRing K)) ?_
    apply RestrictedProduct.ext
    intro v
    exact Units.inv_mul (g v)

theorem mkIdele_fst (g : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) (hg) (w : InfinitePlace K) :
    (mkIdele g hg : AdeleRing (𝓞 K) K).1 w = 1 := rfl

theorem mkIdele_snd (g : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) (hg) (v) :
    (mkIdele g hg : AdeleRing (𝓞 K) K).2 v = ((g v : (v.adicCompletion K)ˣ) : v.adicCompletion K) := rfl

theorem ideleComp_mkIdele (g : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) (hg) (v) :
    ideleComp K v (mkIdele g hg) = g v := Units.ext rfl

/-! ### The discontinuous character -/

variable (K) in
/-- The chosen quadratic character $\\mu_v$ of $K_v^\\times$. -/
def mu (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* Multiplicative (ZMod 2) :=
  (exists_local_char v).choose

theorem mu_sq (v : HeightOneSpectrum (𝓞 K)) (y : (v.adicCompletion K)ˣ) : mu K v (y ^ 2) = 1 :=
  (exists_local_char v).choose_spec.1 y

theorem mu_nontriv (v : HeightOneSpectrum (𝓞 K)) :
    ∃ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 ∧ mu K v u ≠ 1 :=
  (exists_local_char v).choose_spec.2

open NumberFieldKB.MilneCFT.Ch8 in
theorem mu_unitEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) (h : IsLocalPow 2 (a : K) v) :
    mu K v (ideleComp K v (IdeleGroup.unitEmbedding (𝓞 K) K a)) = 1 := by
  obtain ⟨x, hx⟩ := h
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hx
    exact a.ne_zero ((map_eq_zero (algebraMap K (v.adicCompletion K))).1 hx.symm)
  have : Units.mk0 x hx0 ^ 2 = ideleComp K v (IdeleGroup.unitEmbedding (𝓞 K) K a) := by
    apply Units.ext
    rw [ideleComp_unitEmbedding, Units.val_pow_eq_pow_val, Units.val_mk0, hx]
  rw [← this]
  exact mu_sq v _

variable (K) in
/-- **The discontinuous character** $\\Lambda(x) = \\lim_{U}\\mu_v(x_v)$ of the idele group. -/
def Lam (U : Ultrafilter (HeightOneSpectrum (𝓞 K))) : IdeleGroup (𝓞 K) K →* Multiplicative (ZMod 2) where
  toFun x := limU U (fun v => mu K v (ideleComp K v x))
  map_one' := by
    have : (fun v => mu K v (ideleComp K v (1 : IdeleGroup (𝓞 K) K))) = 1 := by
      funext v; simp
    rw [this]; exact limU_one U
  map_mul' x y := by
    rw [← limU_mul]
    congr 1
    funext v
    simp

theorem lam_principal (U : Ultrafilter (HeightOneSpectrum (𝓞 K)))
    (hU : ∀ a : Kˣ, {v | Ch8.IsLocalPow 2 (a : K) v} ∈ U) (a : Kˣ) :
    Lam K U (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1 := by
  refine limU_eq U _ _ ?_
  filter_upwards [hU a] with v hv
  exact mu_unitEmbedding v a hv

theorem not_isOpen_ker_lam (U : Ultrafilter (HeightOneSpectrum (𝓞 K)))
    (hcof : ∀ A : Set (HeightOneSpectrum (𝓞 K)), Aᶜ.Finite → A ∈ U) :
    ¬ IsOpen ((Lam K U).ker : Set (IdeleGroup (𝓞 K) K)) := by
  classical
  intro hopen
  obtain ⟨S₀, hS⟩ := Ch7.exists_finset_of_isOpen (Lam K U).ker hopen
  choose u hu1 hu2 using fun v : HeightOneSpectrum (𝓞 K) => mu_nontriv (K := K) v
  let g : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ := fun v => if v ∈ S₀ then 1 else u v
  have hg : ∀ v, Valued.v ((g v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    intro v
    by_cases hv : v ∈ S₀
    · simp [g, hv]
    · simp [g, hv, hu1 v]
  have hx : mkIdele g hg ∈ (Lam K U).ker :=
    hS _ (mkIdele_fst g hg) (fun v hv => by rw [mkIdele_snd]; simp [g, hv])
      (fun v => by rw [mkIdele_snd]; exact hg v)
  have hne : Lam K U (mkIdele g hg) = Multiplicative.ofAdd (1 : ZMod 2) := by
    refine limU_eq U _ _ ?_
    refine Filter.mem_of_superset (hcof (↑S₀)ᶜ (by simp)) ?_
    intro v hv
    have hv' : v ∉ S₀ := hv
    show mu K v (ideleComp K v (mkIdele g hg)) = _
    rw [ideleComp_mkIdele]
    have h1 : mu K v (u v) ≠ 1 := hu2 v
    have : g v = u v := by simp [g, hv']
    rw [this]
    revert h1
    generalize mu K v (u v) = z
    revert z
    decide
  rw [MonoidHom.mem_ker, hne] at hx
  exact absurd hx (by decide)

end Ex511

open NumberFieldKB.MilneCFT.Ex511 in
/-- **Exercise 5.11** (Milne, *CFT*, V, p. 182): the idele class group of a number field has a subgroup of finite
index that is not open.

*Construction.* For each finite prime $v$ let $\\mu_v : K_v^\\times\\to\\{\\pm1\\}$ be a character killing squares and
nontrivial on a unit (`Ex511.exists_local_char`: $K_v^\\times/K_v^{\\times2}$ is an $\\mathbb F_2$-vector space, and a unit
is a nonsquare by the index formula of Proposition 6.8). By Chebotarev (in the splitting field of
$\\prod(X^2-a_i)$) and Hensel's lemma, for $a_1,\\dots,a_k\\in K^\\times$ infinitely many primes have all $a_i$ squares in
$K_v$ (`Ex511.infinite_isLocalPow`). So there is an ultrafilter $U$ on the primes containing the cofinite sets and,
for every $a\\in K^\\times$, the primes where $a$ is a square (`Ex511.exists_ultrafilter`). Then
$\\Lambda(x)=\\lim_U\\mu_v(x_v)$ is a character of the idele group, trivial on $K^\\times$ (`Ex511.lam_principal`), and not
continuous: an open kernel would contain an idele that is $1$ at finitely many primes and a unit with
$\\mu_v\\ne1$ at the cofinitely many remaining primes (`Ex511.not_isOpen_ker_lam`, via `Ch7.exists_finset_of_isOpen`),
but $\\Lambda$ of it is nontrivial. The image $N$ of $\\ker\\Lambda$ in the idele class group has index at most $2$ and
has preimage $\\ker\\Lambda$, so is not open. -/
@[kb "milne2020cft" "Ch. V, Exercise 5.11, p. 182"]
theorem exercise5_11 (K : Type) [Field K] [NumberField K] : Exercise5_11 K := by
  obtain ⟨U, hcof, hU⟩ := exists_ultrafilter (K := K)
  let P := IdeleGroup.principalSubgroup (𝓞 K) K
  have hP : P ≤ (Lam K U).ker := by
    rintro _ ⟨a, rfl⟩
    exact lam_principal U hU a
  have hcomap : ((Lam K U).ker.map (QuotientGroup.mk' P)).comap (QuotientGroup.mk' P) = (Lam K U).ker := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.2 hP
  refine ⟨⟨(Lam K U).ker.map (QuotientGroup.mk' P), ⟨?_⟩, ?_⟩⟩
  · rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective P), hcomap,
      Subgroup.index_ker]
    have : Finite (Lam K U).range := Finite.of_injective (Subtype.val : (Lam K U).range → _)
      Subtype.val_injective
    exact Nat.card_pos.ne'
  · intro hopen
    apply not_isOpen_ker_lam U hcof
    have := hopen.preimage (QuotientGroup.continuous_mk (N := P))
    have h2 := congrArg (fun H : Subgroup (IdeleGroup (𝓞 K) K) => (H : Set (IdeleGroup (𝓞 K) K))) hcomap
    simp only [Subgroup.coe_comap] at h2
    rw [← h2]
    exact this

end NumberFieldKB.MilneCFT
