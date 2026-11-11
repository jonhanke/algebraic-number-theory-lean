import NumberFieldKB.MilneANT.Ch8GaloisGroups
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: Remark 8.24 (real primes)

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

Proves the named statement `Remark8_24`: complex conjugation, restricted to the splitting field through an embedding
extending the real place, permutes the roots of $f$ with one $2$-cycle for each irreducible quadratic factor of $f$
over $\mathbb R$ and fixes the real roots.
-/

open NumberField Polynomial UniqueFactorizationMonoid
open scoped Classical

namespace NumberFieldKB.MilneANT

noncomputable section

/-- Complex conjugation lifts to the Galois group: if $E/K$ is normal and $\iota : E \to \mathbb C$ is a
$K$-algebra map (the structure map of $K$ landing in the real numbers), some automorphism $\tau$ of $E/K$ satisfies
$\iota\circ\tau = \overline{\iota}$. -/
theorem exists_conj_aut {K E : Type*} [Field K] [Field E] [Algebra K E] [Normal K E] [Algebra K ℂ]
    (h : ∀ x : K, (starRingEnd ℂ) (algebraMap K ℂ x) = algebraMap K ℂ x) (ι : E →ₐ[K] ℂ) :
    ∃ τ : E ≃ₐ[K] E, ∀ x, ι (τ x) = (starRingEnd ℂ) (ι x) := by
  let c : ℂ ≃ₐ[K] ℂ := AlgEquiv.ofRingEquiv (f := Complex.conjAe.toRingEquiv) (fun x => h x)
  let L : IntermediateField K ℂ := ι.fieldRange
  let e : E ≃ₐ[K] L := AlgEquiv.ofInjectiveField ι
  have : Normal K L := Normal.of_algEquiv e
  let ρ : L ≃ₐ[K] L := AlgEquiv.restrictNormal c L
  refine ⟨e.trans (ρ.trans e.symm), fun x => ?_⟩
  have h1 : ((e (e.symm (ρ (e x))) : L) : ℂ) = ((ρ (e x) : L) : ℂ) := by rw [AlgEquiv.apply_symm_apply]
  have h2 : ((ρ (e x) : L) : ℂ) = c (ι x) := AlgEquiv.restrictNormal_commutes c L (e x)
  have h3 : ∀ y, ((e y : L) : ℂ) = ι y := fun y => rfl
  show ι (e.symm (ρ (e x))) = _
  rw [← h3, h1, h2]; rfl


/-- A multiset of natural numbers all equal to `1` or `2` has sum `count 1 + 2 * count 2`. -/
theorem sum_eq_count_of_mem{M : Multiset ℕ} (h : ∀ x ∈ M, x = 1 ∨ x = 2) :
    M.sum = M.count 1 + 2 * M.count 2 ∧ M.card = M.count 1 + M.count 2 := by
  induction M using Multiset.induction with
  | empty => simp
  | cons a M ih =>
    obtain ⟨h1, h2⟩ := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    rcases h a (Multiset.mem_cons_self _ _) with rfl | rfl
    · simp [h1, h2]; omega
    · simp [h1, h2]; omega

/-- Two multisets with entries in `{1, 2}`, with the same sum and the same number of `1`s, are equal. -/
theorem multiset_eq_of_one_two{M N : Multiset ℕ} (hM : ∀ x ∈ M, x = 1 ∨ x = 2)
    (hN : ∀ x ∈ N, x = 1 ∨ x = 2) (hs : M.sum = N.sum) (h1 : M.count 1 = N.count 1) : M = N := by
  have a := sum_eq_count_of_mem hM
  have b := sum_eq_count_of_mem hN
  have h2 : M.count 2 = N.count 2 := by omega
  ext n
  by_cases n1 : n = 1
  · subst n1; exact h1
  by_cases n2 : n = 2
  · subst n2; exact h2
  rw [Multiset.count_eq_zero.2 (fun h => by rcases hM n h with h | h <;> omega),
    Multiset.count_eq_zero.2 (fun h => by rcases hN n h with h | h <;> omega)]

/-- Irreducible factors of a real polynomial have degree `1` or `2`. -/
theorem factor_degrees_mem{g : ℝ[X]} :
    ∀ x ∈ (normalizedFactors g).map natDegree, x = 1 ∨ x = 2 := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
  have hirr := irreducible_of_normalized_factor p hp
  have h2 := hirr.degree_le_two
  have h1 : 1 ≤ p.natDegree := Polynomial.natDegree_pos_iff_degree_pos.2
    (Polynomial.degree_pos_of_irreducible hirr)
  have : p.natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_iff_degree_le.2 h2
    exact this
  omega

/-- The degrees of the irreducible factors of a nonzero real polynomial add up to its degree. -/
theorem factor_degrees_sum{g : ℝ[X]} (hg : g ≠ 0) :
    ((normalizedFactors g).map natDegree).sum = g.natDegree := by
  have hmonic : ∀ p ∈ normalizedFactors g, p.Monic := fun p hp =>
    ((Polynomial.mem_normalizedFactors_iff hg).1 hp).2.1
  rw [← Polynomial.natDegree_multiset_prod_of_monic _ hmonic]
  have := prod_normalizedFactors hg
  rw [Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated this)]

/-- For a squarefree real polynomial, the number of linear irreducible factors is the number of real roots. -/
theorem factor_degrees_count_one{g : ℝ[X]} (hg : g ≠ 0) (hs : Squarefree g) :
    ((normalizedFactors g).map natDegree).count 1 = g.roots.toFinset.card := by
  have hnd := (squarefree_iff_nodup_normalizedFactors hg).1 hs
  rw [Multiset.count_map]
  have hnd' : (Multiset.filter (fun a => 1 = a.natDegree) (normalizedFactors g)).Nodup :=
    hnd.filter _
  rw [← Multiset.toFinset_card_of_nodup hnd']
  symm
  apply Finset.card_bij (fun r _ => X - C r)
  · intro r hr
    have hr' : g.IsRoot r := (Polynomial.mem_roots hg).1 (Multiset.mem_toFinset.1 hr)
    simp only [Multiset.mem_toFinset, Multiset.mem_filter]
    refine ⟨(Polynomial.mem_normalizedFactors_iff hg).2 ⟨irreducible_X_sub_C r, monic_X_sub_C r,
      Polynomial.dvd_iff_isRoot.2 hr'⟩, by simp⟩
  · intro a _ b _ h
    simpa using h
  · intro p hp
    simp only [Multiset.mem_toFinset, Multiset.mem_filter] at hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hirr, hmon, hdvd⟩ := (Polynomial.mem_normalizedFactors_iff hg).1 hp1
    have hdeg : p.natDegree = 1 := hp2.symm
    have hp3 : p = X - C (-p.coeff 0) := by
      have := hmon.eq_X_add_C hdeg
      rw [this]; simp [sub_eq_add_neg]
    refine ⟨-p.coeff 0, ?_, hp3.symm⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hg, Polynomial.dvd_iff_isRoot.symm, ← hp3]
    exact hdvd

/-- Cycle type of an involution: all parts are `1` or `2`, they sum to the cardinality, and the parts equal to `1`
are the fixed points. -/
theorem involution_partition {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α)
    (h : σ * σ = 1) :
    (∀ x ∈ σ.partition.parts, x = 1 ∨ x = 2) ∧ σ.partition.parts.sum = Fintype.card α ∧
      σ.partition.parts.count 1 = Fintype.card (Function.fixedPoints σ) := by
  have hord : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  have hct : ∀ x ∈ σ.cycleType, x = 2 := fun x hx => by
    have h1 := Equiv.Perm.two_le_of_mem_cycleType hx
    have h2 : x ∣ 2 := (Equiv.Perm.dvd_of_mem_cycleType hx).trans hord
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  refine ⟨?_, σ.partition.parts_sum, ?_⟩
  · intro x hx
    rw [Equiv.Perm.parts_partition, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · exact Or.inr (hct x hx)
    · exact Or.inl (Multiset.eq_of_mem_replicate hx)
  · rw [Equiv.Perm.parts_partition, Multiset.count_add, Multiset.count_replicate_self,
      Multiset.count_eq_zero.2 (fun h1 => by have := Equiv.Perm.two_le_of_mem_cycleType h1; omega),
      Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType]
    simp

/-- **Remark 8.24 holds.** -/
@[kb "milne2020ant" "v3.08, Rem. 8.24, p. 145"]
theorem remark_8_24 : Remark8_24 := by
  refine ⟨fun K _ _ v hv f hf => ?_⟩
  set φ := v.embedding_of_isReal hv with hφ
  let _ : Algebra K ℂ := (Complex.ofRealHom.comp φ).toAlgebra
  let ι : f.SplittingField →ₐ[K] ℂ := IsAlgClosed.lift
  obtain ⟨τ, hτ⟩ := exists_conj_aut (E := f.SplittingField)
    (fun x => by exact Complex.conj_ofReal (φ x)) ι
  refine ⟨τ, ?_⟩
  have hf0 : f ≠ 0 := by rintro rfl; exact not_separable_zero hf
  have hg0 : f.map φ ≠ 0 := (Polynomial.map_ne_zero_iff φ.injective).2 hf0
  have hgs : (f.map φ).Separable := hf.map
  have hgdeg : (f.map φ).natDegree = f.natDegree := Polynomial.natDegree_map φ
  have hperm : ∀ r : f.rootSet f.SplittingField, ((galPerm f τ r : f.rootSet f.SplittingField) :
      f.SplittingField) = τ r := fun r => rfl
  have hinv : galPerm f τ * galPerm f τ = 1 := by
    ext r
    apply ι.injective
    show ι (((galPerm f τ) ((galPerm f τ) r) : f.rootSet f.SplittingField) : f.SplittingField) = ι r
    rw [hperm, hperm, hτ, hτ]
    simp
  obtain ⟨hP1, hP2, hP3⟩ := involution_partition _ hinv
  apply multiset_eq_of_one_two hP1 factor_degrees_mem
  · rw [hP2, factor_degrees_sum hg0, hgdeg]
    exact card_rootSet_eq_natDegree hf (SplittingField.splits f)
  · rw [hP3, factor_degrees_count_one hg0 hgs.squarefree]
    have hev : ∀ x : ℝ, aeval (R := K) (x : ℂ) f = (((f.map φ).eval x : ℝ) : ℂ) := by
      intro x
      rw [aeval_def, eval₂_eq_eval_map, show algebraMap K ℂ = Complex.ofRealHom.comp φ from rfl,
        ← Polynomial.map_map]
      rw [Polynomial.eval_map]
      exact Polynomial.eval₂_at_apply Complex.ofRealHom x
    have himg : ι '' f.rootSet f.SplittingField = f.rootSet ℂ :=
      Splits.image_rootSet_of_map_ne_zero (SplittingField.splits f) ι
        ((Polynomial.map_ne_zero_iff (algebraMap K ℂ).injective).2 hf0)
    have hreal : ∀ r : Function.fixedPoints (galPerm f τ),
        (((ι r.1.1).re : ℝ) : ℂ) = ι r.1.1 := by
      intro r
      have h1 : τ r.1.1 = r.1.1 := by
        have := congrArg Subtype.val r.2
        exact this
      have h2 := hτ r.1.1
      rw [h1] at h2
      exact Complex.conj_eq_iff_re.1 h2.symm
    have hroot : ∀ r : Function.fixedPoints (galPerm f τ),
        (ι r.1.1).re ∈ (f.map φ).roots.toFinset := by
      intro r
      have h1 : ι r.1.1 ∈ f.rootSet ℂ := himg ▸ ⟨r.1.1, r.1.2, rfl⟩
      have h2 := (mem_rootSet.1 h1).2
      rw [← hreal r, hev] at h2
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hg0]
      exact_mod_cast h2
    rw [← Fintype.card_coe (f.map φ).roots.toFinset]
    refine Fintype.card_congr (Equiv.ofBijective (fun r => ⟨(ι r.1.1).re, hroot r⟩) ⟨?_, ?_⟩)
    · intro r s hrs
      have h1 : (ι r.1.1).re = (ι s.1.1).re := congrArg Subtype.val hrs
      apply Subtype.ext
      apply Subtype.ext
      apply ι.injective
      show ι r.1.1 = ι s.1.1
      rw [← hreal r, ← hreal s, h1]
    · rintro ⟨x, hx⟩
      have hx' : (f.map φ).IsRoot x := (Polynomial.mem_roots hg0).1 (Multiset.mem_toFinset.1 hx)
      have h1 : (x : ℂ) ∈ f.rootSet ℂ := mem_rootSet.2 ⟨hf0, by rw [hev]; exact_mod_cast hx'⟩
      rw [← himg] at h1
      obtain ⟨r, hr, hrx⟩ := h1
      have hfix : galPerm f τ ⟨r, hr⟩ = ⟨r, hr⟩ := by
        apply Subtype.ext
        apply ι.injective
        show ι (τ r) = ι r
        rw [hτ, hrx]; exact Complex.conj_ofReal x
      refine ⟨⟨⟨r, hr⟩, hfix⟩, ?_⟩
      apply Subtype.ext
      show (ι r).re = x
      rw [hrx]; simp

end

end NumberFieldKB.MilneANT
