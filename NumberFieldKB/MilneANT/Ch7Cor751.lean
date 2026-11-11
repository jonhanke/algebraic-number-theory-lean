import NumberFieldKB.MilneANT.Ch7Prop750
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.LocalRing.ResidueField.Instances

/-!
# Milne, *Algebraic Number Theory*, Corollaries 7.51 and 7.52, p. 128

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

Discharges `Cor7_51` (`cor_7_51`) and `Cor7_52` (`cor_7_52`). Key steps: the set of finite unramified subextensions
of `L/K` is closed under compositum (`Cor751.sup_FU`, via Prop. 7.50); `K₀` is its supremum, and a finite subextension
of `K₀` lies in a single finite unramified one by compactness. For finite residue field, roots of unity of order prime
to `p` are Hensel lifts of roots of unity of the residue fields (`Cor751.adjoin_FU`, `Cor751.le_adjoin_roots`).
-/

open IsLocalRing Polynomial

universe u v w

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneANT

namespace Cor751

open ResidueSub Prop750

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

section Main

variable [PerfectField K] [PerfectField (ResidueField A)] [Algebra.IsAlgebraic K L]

include A K

/-- Finite and unramified. -/
def FU (K' : IntermediateField K L) : Prop := FiniteDimensional K K' ∧ IsUnramifiedMilne A K K'

theorem le_of_residue_le {K3 K1 : IntermediateField K L} (f1 : FiniteDimensional K K1)
    (u1 : IsUnramifiedMilne A K K1) (f3 : FiniteDimensional K K3) (u3 : IsUnramifiedMilne A K K3)
    (hs : residueField' A K L K1 ≤ residueField' A K L K3) : K1 ≤ K3 := by
  have p := prop_7_50_aux A K L
  rw [p.le_iff K1 K3 f1 u1 f3 u3]
  intro x hx
  exact (mem_residueField'_iff A K L K3 x).1 (hs ((mem_residueField'_iff A K L K1 x).2 hx))

theorem sup_FU {K1 K2 : IntermediateField K L} (h1 : FU A K L K1) (h2 : FU A K L K2) :
    FU A K L (K1 ⊔ K2) := by
  obtain ⟨f1, u1⟩ := h1
  obtain ⟨f2, u2⟩ := h2
  have hsep : Algebra.IsSeparable K L := sep_of_perfect K L
  have : Algebra.IsSeparable K K1 := sep_of_perfect K K1
  have : Algebra.IsSeparable K K2 := sep_of_perfect K K2
  have : FiniteDimensional (ResidueField A) (residueField' A K L K1 ⊔ residueField' A K L K2 :
      IntermediateField (ResidueField A) (ResidueField (integralClosure A L))) := inferInstance
  obtain ⟨K3, f3, u3, hr3, -⟩ := construct A K L (residueField' A K L K1 ⊔ residueField' A K L K2)
  have h13 : K1 ≤ K3 := le_of_residue_le A K L f1 u1 f3 u3 (by rw [hr3]; exact le_sup_left)
  have h23 : K2 ≤ K3 := le_of_residue_le A K L f2 u2 f3 u3 (by rw [hr3]; exact le_sup_right)
  have hle : K1 ⊔ K2 ≤ K3 := sup_le h13 h23
  exact ⟨inferInstance, isUnramified_of_le A K L hle u3⟩

theorem bot_FU : FU A K L ⊥ := by
  have : Algebra.IsSeparable K L := sep_of_perfect K L
  obtain ⟨K0, f0, u0, -, hmin⟩ := construct A K L
    (⊥ : IntermediateField (ResidueField A) (ResidueField (integralClosure A L)))
  have : K0 = ⊥ := le_bot_iff.1 (hmin ⊥ inferInstance bot_le)
  subst this
  exact ⟨f0, u0⟩

/-- Compactness: a finite subextension of the supremum of a directed set lies in a member. -/
theorem exists_mem_of_le_sSup (K' : IntermediateField K L) [FiniteDimensional K K']
    (S : Set (IntermediateField K L)) (hne : S.Nonempty)
    (hdir : ∀ E1 ∈ S, ∀ E2 ∈ S, E1 ⊔ E2 ∈ S) (hle : K' ≤ sSup S) : ∃ E ∈ S, K' ≤ E := by
  obtain ⟨s, hs⟩ := (IntermediateField.essFiniteType_iff (F := K) (E := L) (K := K')).1 inferInstance
  have hc := IntermediateField.adjoin_finset_isCompactElement (F := K) s
  rw [hs, isCompactElement_iff_le_of_directed_sSup_le] at hc
  exact hc S hne (fun E1 h1 E2 h2 => ⟨E1 ⊔ E2, hdir _ h1 _ h2, le_sup_left, le_sup_right⟩) hle

/-- The supremum of all finite unramified subextensions. -/
noncomputable def Kmax : IntermediateField K L := sSup {E | FU A K L E}

theorem clause1 (K' : IntermediateField K L) (hf : FiniteDimensional K K') (hle : K' ≤ Kmax A K L) :
    IsUnramifiedMilne A K K' := by
  have hsep : Algebra.IsSeparable K L := sep_of_perfect K L
  obtain ⟨E, ⟨fE, uE⟩, hE⟩ := exists_mem_of_le_sSup A K L K' {E | FU A K L E} ⟨⊥, bot_FU A K L⟩
    (fun _ h1 _ h2 => sup_FU A K L h1 h2) hle
  exact isUnramified_of_le A K L hE uE

theorem clause2 (K' : IntermediateField K L) (h : FU A K L K') : K' ≤ Kmax A K L :=
  le_sSup h

/-! ## Roots of unity -/

theorem isUnit_deriv (n : ℕ) (hn : 0 < n) (hp : ¬ ringChar (ResidueField A) ∣ n) (b : integralClosure A L)
    (hb : residue (integralClosure A L) b ^ n = 1) :
    IsUnit (aeval b (derivative (X ^ n - C 1 : A[X]))) := by
  rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, ← Remark753.aeval_residue A L b]
  have hne : ((n : ℕ) : ResidueField (integralClosure A L)) ≠ 0 := by
    have h1 : ((n : ℕ) : ResidueField A) ≠ 0 := fun h => hp ((ringChar.spec (ResidueField A) n).1 h)
    intro h
    apply h1
    apply (algebraMap (ResidueField A) (ResidueField (integralClosure A L))).injective
    rw [map_natCast, map_zero]; exact h
  have hb0 : residue (integralClosure A L) b ≠ 0 := by
    intro h; rw [h, zero_pow hn.ne'] at hb; exact zero_ne_one hb
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul, aeval_X_pow,
    map_natCast]
  exact mul_ne_zero hne (pow_ne_zero _ hb0)

theorem exists_lift_root (n : ℕ) (hn : 0 < n) (hp : ¬ ringChar (ResidueField A) ∣ n) (b : integralClosure A L)
    (hb : residue (integralClosure A L) b ^ n = 1) :
    ∃ ζ : integralClosure A L, ζ ^ n = 1 ∧ residue (integralClosure A L) ζ = residue _ b := by
  have hsep : Algebra.IsSeparable K L := sep_of_perfect K L
  have h1 : aeval b (X ^ n - C 1 : A[X]) ∈ maximalIdeal (integralClosure A L) := by
    rw [← residue_eq_zero_iff, ← Remark753.aeval_residue A L b]
    simp [hb]
  obtain ⟨ζ, hζ, hd⟩ := HenselExt.hensel_of_algebraic A K L (X ^ n - C 1 : A[X])
    (monic_X_pow_sub_C 1 hn.ne') b h1 (isUnit_deriv A K L n hn hp b hb)
  refine ⟨ζ, ?_, (Ideal.Quotient.eq (I := maximalIdeal (integralClosure A L))).2 hd⟩
  simpa [sub_eq_zero] using hζ

theorem isIntegral_residue (b : integralClosure A L) :
    IsIntegral (ResidueField A) (residue (integralClosure A L) b) := by
  obtain ⟨p, hp, hpe⟩ := (Algebra.IsIntegral.isIntegral (R := A) b)
  refine ⟨p.map (algebraMap A (ResidueField A)), hp.map _, ?_⟩
  rw [← aeval_def, aeval_map_algebraMap, Remark753.aeval_residue A L b p]
  have : aeval b p = 0 := hpe
  rw [this, map_zero]

/-- (i) Roots of unity of order prime to `p` generate unramified extensions. -/
theorem adjoin_FU [Finite (ResidueField A)] (ζ : L) (n : ℕ) (hn : 0 < n)
    (hp : ¬ ringChar (ResidueField A) ∣ n) (hζ : ζ ^ n = 1) : FU A K L (IntermediateField.adjoin K {ζ}) := by
  have hsep : Algebra.IsSeparable K L := sep_of_perfect K L
  have hint : IsIntegral A ζ := IsIntegral.of_pow hn (by rw [hζ]; exact isIntegral_one)
  let ζ' : integralClosure A L := ⟨ζ, hint⟩
  have hζ' : ζ' ^ n = 1 := Subtype.ext (by simpa [ζ'] using hζ)
  have hres : residue (integralClosure A L) ζ' ^ n = 1 := by rw [← map_pow, hζ', map_one]
  have hintk : IsIntegral (ResidueField A) (residue (integralClosure A L) ζ') := isIntegral_residue A K L ζ'
  have : FiniteDimensional (ResidueField A) (IntermediateField.adjoin (ResidueField A)
      {residue (integralClosure A L) ζ'}) := IntermediateField.adjoin.finiteDimensional hintk
  obtain ⟨U, fU, uU, hrU, -⟩ := construct A K L
    (IntermediateField.adjoin (ResidueField A) {residue (integralClosure A L) ζ'})
  have hmem : residue (integralClosure A L) ζ' ∈ residueField' A K L U := by
    rw [hrU]; exact IntermediateField.mem_adjoin_simple_self _ _
  have hroot : aeval ζ' (X ^ n - C 1 : A[X]) = 0 := by simp [hζ']
  have hm := mem_of_residue A K L (X ^ n - C 1 : A[X]) ζ' (monic_X_pow_sub_C 1 hn.ne') hroot
    (isUnit_deriv A K L n hn hp ζ' hres) U hmem
  have hle : IntermediateField.adjoin K {ζ} ≤ U := IntermediateField.adjoin_simple_le_iff.2 hm
  have hintK : IsIntegral K ζ := hint.tower_top
  exact ⟨IntermediateField.adjoin.finiteDimensional hintK, isUnramified_of_le A K L hle uU⟩

/-- (ii) A finite unramified extension is generated by roots of unity of order prime to `p`. -/
theorem le_adjoin_roots [Finite (ResidueField A)] (K' : IntermediateField K L) (hf : FiniteDimensional K K')
    (hu : IsUnramifiedMilne A K K') :
    K' ≤ IntermediateField.adjoin K
      {ζ : L | ∃ n : ℕ, 0 < n ∧ ¬ ringChar (ResidueField A) ∣ n ∧ ζ ^ n = 1} := by
  have hsep : Algebra.IsSeparable K L := sep_of_perfect K L
  have : Algebra.IsSeparable K K' := sep_of_perfect K K'
  set Z : Set L := {ζ : L | ∃ n : ℕ, 0 < n ∧ ¬ ringChar (ResidueField A) ∣ n ∧ ζ ^ n = 1} with hZ
  set E : IntermediateField K L := IntermediateField.adjoin K (Z ∩ (K' : Set L)) with hE
  have hEK : E ≤ K' := IntermediateField.adjoin_le_iff.2 Set.inter_subset_right
  have fE : FiniteDimensional K E :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hEK).toLinearMap
      (IntermediateField.inclusion hEK).injective
  have uE : IsUnramifiedMilne A K K' → IsUnramifiedMilne A K E := fun h => isUnramified_of_le A K L hEK h
  have hkfin : Finite (residueField' A K L K') := Module.finite_of_finite (ResidueField A)
  have hsub : residueField' A K L K' ≤ residueField' A K L E := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 ((mem_residueField'_iff A K L K' x).1 hx)
    have hbK : (b : L) ∈ K' := hb
    by_cases h0 : residue (integralClosure A L) b = 0
    · rw [h0]; exact zero_mem _
    set k' := residueField' A K L K'
    let _ : Fintype k' := Fintype.ofFinite _
    let y : k' := ⟨residue (integralClosure A L) b, hx⟩
    have hy : y ≠ 0 := fun h => h0 (congrArg Subtype.val h)
    have hq : 1 < Fintype.card k' := Fintype.one_lt_card
    set m := Fintype.card k' - 1 with hm
    have hym : y ^ m = 1 := FiniteField.pow_card_sub_one_eq_one y hy
    have hbm : residue (integralClosure A L) b ^ m = 1 := congrArg Subtype.val hym
    have hmpos : 0 < m := by omega
    have hmk : ((m : ℕ) : ResidueField A) ≠ 0 := by
      intro h0'
      have h1 : ((m : ℕ) : k') = 0 := by
        rw [← map_natCast (algebraMap (ResidueField A) k'), h0', map_zero]
      have h2 : ((m : ℕ) : k') = -1 := by
        rw [hm, Nat.cast_sub (by omega), FiniteField.cast_card_eq_zero]; ring
      rw [h2] at h1
      exact one_ne_zero (neg_eq_zero.1 h1)
    have hp : ¬ ringChar (ResidueField A) ∣ m := fun h => hmk ((ringChar.spec (ResidueField A) m).2 h)
    obtain ⟨ζ, hζ, hres⟩ := exists_lift_root A K L m hmpos hp b hbm
    have hres' : residue (integralClosure A L) ζ ∈ residueField' A K L K' := by
      rw [hres]; exact hx
    have hζK : (ζ : L) ∈ K' := mem_of_residue A K L (X ^ m - C 1 : A[X]) ζ (monic_X_pow_sub_C 1 hmpos.ne')
      (by simp [hζ]) (isUnit_deriv A K L m hmpos hp ζ (by rw [← map_pow, hζ, map_one])) K' hres'
    have hζE : (ζ : L) ∈ E := IntermediateField.subset_adjoin K _
      ⟨⟨m, hmpos, hp, by simpa using congrArg Subtype.val hζ⟩, hζK⟩
    rw [← hres]
    exact residue_mem_residueField' A K L E ζ hζE
  have hsup : residueField' A K L E ≤ residueField' A K L K' := by
    intro x hx
    exact (mem_residueField'_iff A K L K' x).2
      (residueRange_mono A K L hEK ((mem_residueField'_iff A K L E x).1 hx))
  have hEeq : E = K' := eq_of_le_of_residue A K L E K' hEK (uE hu) hu (le_antisymm hsup hsub)
  rw [← hEeq]
  exact IntermediateField.adjoin.mono K _ _ Set.inter_subset_left

end Main

section AlgClosed

variable {L' : Type w} [Field L'] [Algebra A L']

theorem isAlgClosed_residue [IsAlgClosed L'] : IsAlgClosed (ResidueField (integralClosure A L')) := by
  refine IsAlgClosed.of_exists_root _ fun p hpm hpirr => ?_
  have hlift : p ∈ Polynomial.lifts (residue (integralClosure A L')) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => residue_surjective _
  obtain ⟨P, hPmap, hPdeg, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hpm
  have hnat : 0 < p.natDegree := Polynomial.natDegree_pos_iff_degree_pos.2
    (Polynomial.degree_pos_of_irreducible hpirr)
  have hQ : (P.map (algebraMap (integralClosure A L') L')).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (hPm.map _).ne_zero, hPm.natDegree_map, hPdeg]
    exact_mod_cast hnat.ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hQ
  have hx' : Polynomial.eval₂ (algebraMap (integralClosure A L') L') x P = 0 := by
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx
  have hxB : IsIntegral (integralClosure A L') x := ⟨P, hPm, hx'⟩
  have hxA : IsIntegral A x := isIntegral_trans (R := A) (A := integralClosure A L') x hxB
  let x' : integralClosure A L' := ⟨x, hxA⟩
  have h0 : algebraMap (integralClosure A L') L' (P.eval x') = 0 := by
    rw [← Polynomial.eval₂_at_apply]; exact hx'
  have h1 : P.eval x' = 0 :=
    (map_eq_zero_iff _ (Subtype.val_injective (p := fun y => y ∈ integralClosure A L'))).1 h0
  refine ⟨residue (integralClosure A L') x', ?_⟩
  rw [← hPmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, h1, map_zero]

theorem isAlgebraic_residue :
    Algebra.IsAlgebraic (ResidueField A) (ResidueField (integralClosure A L')) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨b, rfl⟩ := residue_surjective x
  exact (isIntegral_residue' A b).isAlgebraic
where
  isIntegral_residue' (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      [IsAdicComplete (maximalIdeal A) A] {L' : Type w} [Field L'] [Algebra A L']
      (b : integralClosure A L') :
      IsIntegral (ResidueField A) (residue (integralClosure A L') b) := by
    obtain ⟨p, hp, hpe⟩ := (Algebra.IsIntegral.isIntegral (R := A) b)
    refine ⟨p.map (algebraMap A (ResidueField A)), hp.map _, ?_⟩
    rw [← aeval_def, aeval_map_algebraMap, Remark753.aeval_residue A L' b p]
    have : aeval b p = 0 := hpe
    rw [this, map_zero]

end AlgClosed

end Cor751

/-- **Corollary 7.51** (Milne, p. 128). Discharges the named statement `Cor7_51`. -/
@[kb "milne2020ant" "v3.08, Cor. 7.51, p. 128"]
theorem cor_7_51 (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [PerfectField K] [PerfectField (ResidueField A)] [Algebra.IsAlgebraic K L] : Cor7_51 A K L where
  exists_max := ⟨Cor751.Kmax A K L, Cor751.clause1 A K L, fun K' hf hu => Cor751.clause2 A K L K' ⟨hf, hu⟩⟩
  rootsOfUnity := fun _ => by
    intro K₀
    refine ⟨fun K' hf hle => Cor751.clause1 A K L K' hf (hle.trans ?_), fun K' hf hu =>
      Cor751.le_adjoin_roots A K L K' hf hu⟩
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro ζ ⟨n, hn, hp, hζ⟩
    exact Cor751.clause2 A K L _ (Cor751.adjoin_FU A K L ζ n hn hp hζ) (IntermediateField.mem_adjoin_simple_self K ζ)

/-- **Corollary 7.52** (Milne, p. 128). Discharges the named statement `Cor7_52`. -/
@[kb "milne2020ant" "v3.08, Cor. 7.52, p. 128"]
theorem cor_7_52 (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    [PerfectField K] [PerfectField (ResidueField A)] : Cor7_52 A K where
  isAlgClosed := Cor751.isAlgClosed_residue A
  isAlgebraic := Cor751.isAlgebraic_residue A
  exists_un := by
    obtain ⟨K₀, h1, h2⟩ := (cor_7_51 A K (AlgebraicClosure K)).exists_max
    exact ⟨K₀, fun L' hL' => ⟨fun h => h2 L' hL' h, fun h => h1 L' hL' h⟩⟩

end NumberFieldKB.MilneANT
