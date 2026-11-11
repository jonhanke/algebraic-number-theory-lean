import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4LocalInvariant

/-!
# Milne, Class Field Theory, Chapter IV, §4: a local invariant comes from an embedded unramified field

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`), Chapter IV, §4, p. 140.
If `r` is a local invariant of a division algebra `D` of degree `d²` over a nonarchimedean local field `K`, in
Milne's sense (`IsLocalInvariant`: a maximal subfield `L` unramified over `K`, its Frobenius, and a conjugating
element `α`), then, for the unramified extension `L₀` of degree `d` (the splitting field of `X^{q^d} - X`),
there is an embedding `ι : L₀ → D` with `ι (Frob x) = α ι(x) α⁻¹` and `r = ord α`
(`exists_algHom_of_isLocalInvariant`). This is the converse of `isLocalInvariant_of_algHom`.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch4

open TauCeti Polynomial

section Normalize

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- For any embedding `ι` of a finite extension local field `M` into a division algebra `D`,
`ord(ι y) = f(M/K) · v_M(y) / [M : K]`. -/
theorem ordD_algHom_eq_gen {M D : Type} [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [FiniteDimensional K M]
    [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    (ι : M →ₐ[K] D) (y : M) (hy : y ≠ 0) :
    ordD K D (ι y) =
      ((inertiaDegree K M : ℚ) * ((normalizedValuation M (Units.mk0 y hy)).toAdd : ℚ)) /
        Module.finrank K M := by
  let e : M ≃ₐ[K] ι.range := AlgEquiv.ofInjective ι ι.toRingHom.injective
  have hB : IsField ι.range := e.symm.toMulEquiv.isField (Field.toIsField M)
  have h1 := ordD_eq (K := K) (D := D) (E := ι.range) hB (e y)
  have hey : ((e y : ι.range) : D) = ι y := rfl
  rw [hey] at h1
  rw [h1, Algebra.norm_eq_of_algEquiv, ← e.toLinearEquiv.finrank_eq]
  have hN : Algebra.norm K y ≠ 0 := (Algebra.norm_ne_zero_iff).2 hy
  rw [ordK_eq_toAdd hN]
  have h2 := toAdd_normalizedValuation_norm (K := K) (Units.mk0 y hy)
  have h3 : Units.mk0 (Algebra.norm K y) hN = Algebra.normUnits K (Units.mk0 y hy) :=
    Units.ext (by rw [Algebra.coe_normUnits]; rfl)
  rw [h3, h2]
  push_cast
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- `X^n - X` splits in a field containing a primitive `(n-1)`-st root of unity, `n > 1`. -/
theorem splits_X_pow_sub_X_of_isPrimitiveRoot {M : Type} [Field M] [Algebra K M] {n : ℕ} (hn : 1 < n)
    {η : M} (hη : IsPrimitiveRoot η (n - 1)) :
    Splits ((X ^ n - X : K[X]).map (algebraMap K M)) := by
  classical
  have hn0 : NeZero (n - 1) := ⟨by omega⟩
  have hdeg : ((X ^ n - X : K[X]).map (algebraMap K M)).natDegree = n := by
    rw [Polynomial.natDegree_map]
    exact FiniteField.X_pow_card_sub_X_natDegree_eq K hn
  rw [splits_iff_card_roots, hdeg]
  set S : Finset M := insert 0 ((Finset.range (n - 1)).image (fun i => η ^ i)) with hS
  have hinj : Set.InjOn (fun i : ℕ => η ^ i) (Finset.range (n - 1) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hη.pow_inj hi hj hij
  have hS0 : (0 : M) ∉ (Finset.range (n - 1)).image (fun i => η ^ i) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro i _ h
    exact (hη.ne_zero (by omega)) (pow_eq_zero_iff'.1 h).1
  have hcard : S.card = n := by
    rw [hS, Finset.card_insert_of_notMem hS0, Finset.card_image_of_injOn hinj, Finset.card_range]
    omega
  have hne : ((X ^ n - X : K[X]).map (algebraMap K M)) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hroot : ∀ x : M, x ^ n = x → x ∈ ((X ^ n - X : K[X]).map (algebraMap K M)).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
    simp [hx]
  have hsub : S ⊆ ((X ^ n - X : K[X]).map (algebraMap K M)).roots.toFinset := by
    intro x hx
    rw [hS, Finset.mem_insert, Finset.mem_image] at hx
    apply hroot
    rcases hx with rfl | ⟨i, -, rfl⟩
    · exact zero_pow (by omega)
    · have : n = (n - 1) + 1 := by omega
      calc (η ^ i) ^ n = (η ^ i) ^ ((n - 1) + 1) := by rw [← this]
        _ = η ^ i := by
          rw [pow_succ, ← pow_mul, mul_comm i, pow_mul, hη.pow_eq_one, one_pow, one_mul]
  have h1 := Finset.card_le_card hsub
  have h2 := Multiset.toFinset_card_le ((X ^ n - X : K[X]).map (algebraMap K M)).roots
  have h3 := card_roots' ((X ^ n - X : K[X]).map (algebraMap K M))
  omega

set_option synthInstance.maxHeartbeats 400000 in
/-- **A local invariant comes from an embedding of the unramified extension** (Milne, *CFT*, IV, §4, p. 140): if
`r` is a local invariant of a division algebra `D` of degree `d²` over `K` (`IsLocalInvariant`), and `L₀/K` is the
unramified extension of degree `d` (the splitting field of `X^{q^d} - X`), then there are an embedding
`ι : L₀ → D` and `α ∈ Dˣ` with `ι (Frob x) = α ι(x) α⁻¹` and `r = ord α`. Converse of
`isLocalInvariant_of_algHom`. -/
theorem exists_algHom_of_isLocalInvariant {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {L₀ : Type} [Field L₀] [ValuativeRel L₀] [TopologicalSpace L₀] [IsNonarchimedeanLocalField L₀]
    [Algebra K L₀] [ValuativeExtension K L₀] [FiniteDimensional K L₀] [IsGalois K L₀] [IsUnramified K L₀]
    {d : ℕ}
    [Polynomial.IsSplittingField K L₀ (Polynomial.X ^ Nat.card 𝓀[K] ^ d - Polynomial.X)]
    (hL : Module.finrank K L₀ = d)
    {D : Type} [DivisionRing D] [Algebra K D] [FiniteDimensional K D] (hD : Module.finrank K D = d ^ 2)
    {r : ℚ} (h : IsLocalInvariant K D r) :
    ∃ (ι : L₀ →ₐ[K] D) (α : Dˣ),
      (∀ x, ι (TauCeti.frobeniusAlgEquiv (K := K) (L := L₀) x) = α * ι x * ↑α⁻¹) ∧
        r = ordD K D (α : D) := by
  obtain ⟨L, hLf, σ, α, hdim, hunr, hfrob, hconj, hr⟩ := h
  let _ : Field L := hLf.toField
  have hd0 : 0 < d := by rw [← hL]; exact Module.finrank_pos
  have hLd : Module.finrank K L = d := by
    rw [hD] at hdim
    exact (Nat.pow_left_injective (n := 2) (by norm_num) hdim).symm
  let _ := algebraicExtensionValuativeRel K L
  let _ := algebraicExtensionNormedFieldTopology K L
  have := finiteExtension_isNonarchimedeanLocalField K L
  have := algebraicExtension_valuativeExtension K L
  have hq : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  -- the inertia degree of `L` is `d`
  have hf : inertiaDegree K L = d := by
    obtain ⟨u, hu⟩ := normalizedValuation_surjective (K := L) (Multiplicative.ofAdd (1 : ℤ))
    have hx : (u : L) ≠ 0 := u.ne_zero
    obtain ⟨m, hm⟩ := hunr (u : L) hx
    have h1 : ordD K D (((u : L) : L) : D) = ((inertiaDegree K L : ℚ) * 1) / d := by
      have := ordD_algHom_eq_gen (K := K) (D := D) L.val (u : L) hx
      rw [hLd] at this
      have e : Units.mk0 (u : L) hx = u := Units.ext rfl
      rw [e, hu] at this
      simpa using this
    rw [h1] at hm
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0.ne'
    have h2 : (inertiaDegree K L : ℚ) = m * d := by
      field_simp at hm
      linarith
    have h3 : (inertiaDegree K L : ℤ) = m * d := by exact_mod_cast h2
    have hfpos : 0 < inertiaDegree K L := inertiaDegree_pos (K := K) (L := L)
    have hfle : inertiaDegree K L ≤ d := by
      rw [← hLd, ← ramificationIndex_mul_inertiaDegree K L]
      exact Nat.le_mul_of_pos_left _ (ramificationIndex_pos (K := K) (L := L))
    have hfpos' : (0 : ℤ) < inertiaDegree K L := by exact_mod_cast hfpos
    have hfle' : (inertiaDegree K L : ℤ) ≤ d := by exact_mod_cast hfle
    have hd0' : (0 : ℤ) < d := by exact_mod_cast hd0
    have hm1 : m = 1 := by
      rw [h3] at hfpos' hfle'
      have : 0 < m := pos_of_mul_pos_left hfpos' hd0'.le
      nlinarith
    have h4 : (inertiaDegree K L : ℤ) = d := by rw [h3, hm1]; simp
    exact_mod_cast h4
  have hcard : Nat.card 𝓀[L] = Nat.card 𝓀[K] ^ d := by rw [natCard_residueField K L, hf]
  obtain ⟨η, hη⟩ := exists_isPrimitiveRoot_natCard_residueField_sub_one L
  rw [hcard] at hη
  have hsplit : Splits ((X ^ Nat.card 𝓀[K] ^ d - X : K[X]).map (algebraMap K L)) :=
    splits_X_pow_sub_X_of_isPrimitiveRoot (Nat.one_lt_pow hd0.ne' hq) hη
  let φ : L₀ →ₐ[K] L := IsSplittingField.lift L₀ (X ^ Nat.card 𝓀[K] ^ d - X : K[X]) hsplit
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  have hφbij : Function.Bijective φ :=
    ⟨hφinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hL.trans hLd.symm) (f := φ.toLinearMap)).1 hφinj⟩
  let e : L₀ ≃ₐ[K] L := AlgEquiv.ofBijective φ hφbij
  let ι : L₀ →ₐ[K] D := L.val.comp φ
  let σ₀ : L₀ ≃ₐ[K] L₀ := (e.trans σ).trans e.symm
  have hι : ∀ y, ι y = ((e y : L) : D) := fun y => rfl
  have hσ₀ : ∀ y, ι (σ₀ y) = ((σ (e y) : L) : D) := by
    intro y
    simp [σ₀, hι]
  have hq0 : Nat.card 𝓀[K] ≠ 0 := Nat.card_pos.ne'
  have hσfrob : σ₀ = frobeniusAlgEquiv (K := K) (L := L₀) := by
    apply eq_frobeniusAlgEquiv_of_valuation_sub_pow_lt_one
    intro y
    set z : L₀ := (y : L₀) with hzdef
    by_cases hz0 : z = 0
    · rw [hz0, map_zero, zero_pow hq0, sub_zero]; simp
    have hint : 0 ≤ ((normalizedValuation L₀ (Units.mk0 z hz0)).toAdd : ℚ) := by
      have := (mem_integer_iff_toAdd_normalizedValuation_nonneg (Units.mk0 z hz0)).1
        (show ((Units.mk0 z hz0 : L₀ˣ) : L₀) ∈ 𝒪[L₀] from y.2)
      exact_mod_cast this
    have hord := ordD_algHom_eq hL ι z hz0
    have hnn : 0 ≤ ordD K D ((e z : L) : D) := by rw [← hι, hord]; exact hint
    have key := hfrob (e z) hnn
    rw [← hσ₀ z, ← hι] at key
    by_cases hw : σ₀ z - z ^ Nat.card 𝓀[K] = 0
    · rw [hw]; simp
    rcases key with key | key
    · exfalso
      apply hw
      apply ι.toRingHom.injective
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_pow, map_zero]
      rw [key, sub_self]
    · have h2 : ι (σ₀ z) - ι z ^ Nat.card 𝓀[K] = ι (σ₀ z - z ^ Nat.card 𝓀[K]) := by
        rw [map_sub, map_pow]
      rw [h2, ordD_algHom_eq hL ι _ hw] at key
      have h3 := (toAdd_normalizedValuation_le_iff_valuation_le (Units.mk0 _ hw) 1).not
      simp only [map_one, toAdd_one, Units.val_one, Units.val_mk0, not_le] at h3
      exact h3.1 (by exact_mod_cast key)
  refine ⟨ι, α, ?_, hr⟩
  intro x
  rw [← hσfrob, hσ₀, hconj]
  rfl

end Normalize

end NumberFieldKB.MilneCFT.Ch4
