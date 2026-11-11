import NumberFieldKB.MilneCFT.Ch6
import NumberFieldKB.MilneCFT.Ch5Density
import NumberFieldKB.MilneCFT.Ch5Artin
import NumberFieldKB.Chebotarev.Unconditional
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.Data.Set.Opposite

/-!
# Milne, *Class Field Theory*, Chapter VIII §7: density theorems

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §7,
printed pp. 258–260 (printed page = pdf page − 9).

Densities are Mathlib's Dirichlet densities `NumberField.Set.HasDirichletDensity` of sets of finite primes
(`HeightOneSpectrum (𝓞 K)`). Milne proves 7.2–7.4 from the reciprocity law; here they are proved unconditionally:
Theorem 7.2 from Chapter V, Theorem 2.5 (`theorem_2_5`, Hecke $L$-functions), Corollary 7.3 and Theorem 7.4 from the
unconditional Chebotarev density theorem of NumberFieldKB (`chebotarev_unconditional`).

* **Theorem 7.1** (`Theorem7_1`, named statement): $L(1,\chi) \ne 0$ for a nontrivial character of a ray class group.
* **Theorem 7.2** (`theorem_7_2`), **Corollary 7.3** (`cor_7_3`), **Theorem 7.4** (`theorem_7_4`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev Filter Topology

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {K : Type} [Field K] [NumberField K]

/-- Finite disjoint unions: if each `S i` has density `a i`, the union has density `∑ a i` (*proved*, from the
additivity of the Dirichlet ratio for `s > 1`). -/
theorem hasDirichletDensity_iUnion_fintype {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (S : ι → Set (HeightOneSpectrum (𝓞 F))) (hS : Pairwise (Function.onFun Disjoint S)) (a : ι → ℝ)
    (h : ∀ i, (S i).HasDirichletDensity (a i)) : (⋃ i, S i).HasDirichletDensity (∑ i, a i) := by
  rw [hasDirichletDensity_iff]
  have := tendsto_finsetSum (Finset.univ : Finset ι) (fun i _ => (hasDirichletDensity_iff _ _).1 (h i))
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  exact (dirichletRatio_iUnion S hS hs).symm

variable (K) in
/-- **Theorem 7.1** (named statement; Milne, *CFT*, VIII, Theorem 7.1, p. 258, "follows from the proof of Theorem VI 4.9
once one has the reciprocity law"): for every modulus $\mathfrak m$ of $K$ and every nontrivial character
$\chi : C_\mathfrak m \to \mathbb C^\times$, $L(1,\chi) \ne 0$: the Weber $L$-series (`weberLSeries`) tends to a nonzero
limit as $s \downarrow 1$ (Chapter VI's `WeberLOneNeZero`). (The non-vanishing at $s = 1$ of the attached Hecke
$L$-function is proved in NumberFieldKB, `Ch6.cor_4_10_idelic`; the missing link is the Euler product of the Weber
series, which is not formalized.) -/
@[kb "milne2020cft" "Ch. VIII, Theorem 7.1, p. 258 (input)"]
structure Theorem7_1 : Prop where
  ne_zero : ∀ (m : Modulus K) (χ : RayClassGroup m →* ℂˣ), χ ≠ 1 → Ch6.WeberLOneNeZero m χ

/-- **Theorem 7.2** (Milne, *CFT*, VIII, Theorem 7.2, p. 258): let $\mathfrak m$ be a modulus for $K$ and $H$ a
congruence subgroup for $\mathfrak m$ ($I^{S(\mathfrak m)} \supseteq H \supseteq i(K_{\mathfrak m,1})$, i.e. a
subgroup of $C_\mathfrak m$). For every class $k \in I^{S(\mathfrak m)}/H$ (a coset $c\,H$ in $C_\mathfrak m$), the
set of prime ideals in $k$ has Dirichlet density $1/(I^{S(\mathfrak m)} : H)$. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 7.2, p. 258"]
theorem theorem_7_2 (m : Modulus K) (H : Subgroup (RayClassGroup m)) (c : RayClassGroup m) :
    {v : HeightOneSpectrum (𝓞 K) | ∃ hv : ¬ v.asIdeal ∣ m.finite, c⁻¹ * rayClass m v hv ∈ H}.HasDirichletDensity
      (1 / H.index) := by
  classical
  haveI : Finite (RayClassGroup m) := (theorem_1_7_card m).1
  haveI : Fintype H := Fintype.ofFinite _
  have hset : {v : HeightOneSpectrum (𝓞 K) | ∃ hv : ¬ v.asIdeal ∣ m.finite, c⁻¹ * rayClass m v hv ∈ H} =
      ⋃ h : H, {v : HeightOneSpectrum (𝓞 K) | ∃ hv : ¬ v.asIdeal ∣ m.finite, rayClass m v hv = c * h} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hv, h⟩
      exact ⟨⟨_, h⟩, hv, by simp⟩
    · rintro ⟨h, hv, e⟩
      exact ⟨hv, by rw [e]; simp⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun h : H =>
      {v : HeightOneSpectrum (𝓞 K) | ∃ hv : ¬ v.asIdeal ∣ m.finite, rayClass m v hv = c * h}) := by
    intro a b hab
    refine Set.disjoint_left.2 fun v ⟨hv, ha⟩ ⟨hv', hb⟩ => hab (Subtype.ext ?_)
    have := ha.symm.trans hb
    have h := congrArg (fun z => c⁻¹ * z) this
    simpa using h
  have hden := hasDirichletDensity_iUnion_fintype _ hdisj (fun _ : H => (1 / Nat.card (RayClassGroup m) : ℝ))
    (fun h => theorem_2_5 m (c * h))
  rw [hset]
  convert hden using 1
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 : (Nat.card H : ℝ) * H.index = Nat.card (RayClassGroup m) := by
    exact_mod_cast H.card_mul_index
  have h2 : (Nat.card H : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [Fintype.card_eq_nat_card]
  have h3 : (H.index : ℝ) ≠ 0 := by exact_mod_cast Subgroup.index_ne_zero_of_finite
  rw [← h1]
  field_simp

/-- **Corollary 7.3** (Milne, *CFT*, VIII, Corollary 7.3, p. 258): let $L/K$ be a finite abelian extension with Galois
group $G$ and $\sigma \in G$. The prime ideals $\mathfrak p$ of $K$ unramified in $L$ with $(\mathfrak p, L/K) =
\sigma$ (`artinFrob`, Chapter V) have Dirichlet density $1/[L:K]$. -/
@[kb "milne2020cft" "Ch. VIII, Corollary 7.3, p. 258"]
theorem cor_7_3 (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (σ : Gal(L/K)) :
    {v : HeightOneSpectrum (𝓞 K) | v ∈ unramifiedPrimes K L ∧ artinFrob L v = σ}.HasDirichletDensity
      (1 / Module.finrank K L) := by
  haveI : IsGalois K L := inferInstance
  have hconj : ∀ a b : Gal(L/K), IsConj a b ↔ a = b := by
    intro a b
    rw [isConj_iff]
    constructor
    · rintro ⟨c, rfl⟩
      have : c * a = a * c := Std.Commutative.comm (op := (· * ·)) c a
      rw [this]; simp
    · rintro rfl; exact ⟨1, by simp⟩
  have hset : {v : HeightOneSpectrum (𝓞 K) | v ∈ unramifiedPrimes K L ∧ artinFrob L v = σ} =
      frobSet K L (ConjClasses.mk σ) := by
    ext v
    simp only [Set.mem_setOf_eq, frobSet]
    refine and_congr_right fun hv => ?_
    obtain ⟨Q⟩ : Nonempty (v.asIdeal.primesOver (𝓞 L)) := inferInstance
    rw [artinFrob_eq L v hv Q, frobClass_eq_mk_frobAt K L v Q, ConjClasses.mk_eq_mk_iff_isConj,
      hconj]
  have hcard : Nat.card (ConjClasses.mk σ).carrier = 1 := by
    have : (ConjClasses.mk σ).carrier = {σ} := by
      ext x
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, hconj, Set.mem_singleton_iff,
        eq_comm]
    rw [this]; simp
  have h := chebotarev_unconditional K L (ConjClasses.mk σ)
  rw [hcard, IsGalois.card_aut_eq_finrank] at h
  rw [hset]; simpa using h

/-- **Theorem 7.4, Chebotarev's density theorem** (Milne, *CFT*, VIII, Theorem 7.4, p. 259): let $L/K$ be a finite
Galois extension with group $G$ and $C \subseteq G$ stable under conjugation. The set $T$ of primes $\mathfrak p$
unramified in $L$ whose Frobenius class $(\mathfrak p, L/K)$ lies in $C$ has Dirichlet density $|C|/|G|$. (For a
single conjugacy class this is `chebotarev_unconditional`.) -/
@[kb "milne2020cft" "Ch. VIII, Theorem 7.4, p. 259"]
theorem theorem_7_4 (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (C : Set Gal(L/K))
    (hC : ∀ x ∈ C, ∀ τ : Gal(L/K), τ * x * τ⁻¹ ∈ C) :
    {v : HeightOneSpectrum (𝓞 K) | v ∈ unramifiedPrimes K L ∧ (frobClass K L v).carrier ⊆ C}.HasDirichletDensity
      (Nat.card C / Nat.card Gal(L/K)) := by
  classical
  haveI : Fintype Gal(L/K) := Fintype.ofFinite _
  let T : Set (ConjClasses Gal(L/K)) := {c | c.carrier ⊆ C}
  have hset : {v : HeightOneSpectrum (𝓞 K) | v ∈ unramifiedPrimes K L ∧ (frobClass K L v).carrier ⊆ C} =
      ⋃ c : T, frobSet K L c.1 := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, frobSet]
    constructor
    · rintro ⟨hv, h⟩
      exact ⟨⟨frobClass K L v, h⟩, hv, rfl⟩
    · rintro ⟨⟨c, hc⟩, hv, rfl⟩
      exact ⟨hv, hc⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun c : T => frobSet K L c.1) := by
    intro c d hcd
    refine Set.disjoint_left.2 fun v hc hd => hcd (Subtype.ext ?_)
    exact hc.2.symm.trans hd.2
  have hden := hasDirichletDensity_iUnion_fintype _ hdisj
    (fun c : T => (Nat.card c.1.carrier : ℝ) / Nat.card Gal(L/K))
    (fun c => chebotarev_unconditional K L c.1)
  rw [hset]
  convert hden using 1
  rw [← Finset.sum_div]
  congr 1
  have hCfin : (C.toFinite.toFinset) = C.toFinset := by ext; simp
  haveI : Fintype C := Fintype.ofFinite _
  haveI : DecidablePred (· ∈ C) := Classical.decPred _
  rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Gal(L/K) => ConjClasses.mk x)
    (t := (Finset.univ : Finset T).image (fun c => c.1))]
  · rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
    congr 2
    ext x
    simp only [Finset.mem_filter, Set.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨c.2 (ConjClasses.mem_carrier_iff_mk_eq.2 h), h⟩
  · intro x hx
    have hx : x ∈ C := by simpa using hx
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨⟨ConjClasses.mk x, ?_⟩, Finset.mem_univ _, rfl⟩
    intro y hy
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hy
    obtain ⟨c, hc⟩ := hy
    have hy : y = c⁻¹ * x * c⁻¹⁻¹ := by rw [← hc]; group
    rw [hy]
    exact hC x hx c⁻¹

end NumberFieldKB.MilneCFT.Ch8
