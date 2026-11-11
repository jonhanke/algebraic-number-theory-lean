import NumberFieldKB.MilneCFT.Ch6.SecondInequality
import NumberFieldKB.MilneCFT.Ch5Density
import NumberFieldKB.MilneCFT.Ch8.WeberLTauCeti
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.Group.Units

/-!
# Milne, *Class Field Theory*, Chapter VI, Theorem 4.8, proved unconditionally

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VI, Theorem 4.8, p. 197.

**Theorem 4.8** (`theorem4_8`): for a modulus $\mathfrak m$ and a subgroup $H$ of the ray class group $C_\mathfrak m$, the
set of primes in $H$ has Dirichlet density $1/(C_\mathfrak m : H)$ in Milne's form (`MilneHasDirichletDensity`) when
$L(1,\chi)\ne0$ for all nontrivial $\chi$ trivial on $H$, and $0$ otherwise. This discharges the named statement
`Theorem4_8 K`. The $L(1,\chi)\neq0$ hypothesis always holds (`Ch8.theorem7_1`), so the first case occurs.

*Proof.* Following Milne, orthogonality on $C_\mathfrak m/H$:
$\sum_{\mathfrak p\in H}N\mathfrak p^{-s} = \frac1{(C_\mathfrak m:H)}\sum_{\chi}\sum_{\mathfrak p}\chi(\mathfrak p)N\mathfrak p^{-s}$,
the sum over the characters $\chi$ of $C_\mathfrak m/H$ (`isBigO_fibre_sub`). For $\chi\ne1$ the inner sum is $O(1)$
as $s\downarrow1$ (`isBigO_primeSum_rayChar`): this is the log-$L$ estimate for the finite-order Hecke character attached
to $\chi$ (`exists_heckeChar`), whose $L$-function is entire and nonzero at $1$; for $\chi=1$ it is
$\log\frac1{s-1}+O(1)$. The finitely many primes dividing $\mathfrak m_0$ change the sums by $O(1)$
(`milneHasDirichletDensity_congr_finite`).
-/

open Filter Topology Asymptotics NumberField IsDedekindDomain
open NumberFieldKB.Chebotarev NumberFieldKB.HeckeCharacter NumberFieldKB.HeckeL NumberFieldKB.NonVanishing
open QuadFormsKB

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.Ch6

variable {K : Type} [Field K] [NumberField K]

/-- Milne's Dirichlet density is insensitive to finite changes of the set. -/
theorem milneHasDirichletDensity_congr_finite {S T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (hS : MilneHasDirichletDensity S δ) (hST : (symmDiff S T).Finite) : MilneHasDirichletDensity T δ := by
  have h1 : (S \ T).Finite := hST.subset fun x hx => Or.inl hx
  have h2 : (T \ S).Finite := hST.subset fun x hx => Or.inr hx
  have hb : (fun s : ℝ => (T \ S).primeIdealZetaSum s - (S \ T).primeIdealZetaSum s)
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    refine IsBigO.of_bound ((T \ S).ncard + (S \ T).ncard) ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    have a1 := Set.primeIdealZetaSum_le_card_of_finite h1 (by linarith : 0 ≤ s)
    have a2 := Set.primeIdealZetaSum_le_card_of_finite h2 (by linarith : 0 ≤ s)
    have n1 := (S \ T).primeIdealZetaSum_nonneg s
    have n2 := (T \ S).primeIdealZetaSum_nonneg s
    rw [norm_one, mul_one, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  refine (hS.add hb).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  have eS : S = (S ∩ T) ∪ (S \ T) := (Set.inter_union_sdiff S T).symm
  have eT : T = (S ∩ T) ∪ (T \ S) := by rw [Set.inter_comm]; exact (Set.inter_union_sdiff T S).symm
  have dS : Disjoint (S ∩ T) (S \ T) := Set.disjoint_sdiff_inter.symm
  have dT : Disjoint (S ∩ T) (T \ S) := by
    rw [Set.inter_comm]; exact Set.disjoint_sdiff_inter.symm
  have hSs := primeIdealZetaSum_union_disjoint dS hs
  have hTs := primeIdealZetaSum_union_disjoint dT hs
  rw [← eS] at hSs
  rw [← eT] at hTs
  rw [hSs, hTs]
  ring

/-- **Orthogonality on a finite abelian group, $O(1)$ form.** If $f$ maps primes to a finite abelian group $Q$ and
$\sum_\mathfrak p\psi(f(\mathfrak p))N\mathfrak p^{-s}=O(1)$ for every character $\psi\ne1$ of $Q$, then
$\sum_{f(\mathfrak p)=1}N\mathfrak p^{-s}-\frac1{|Q|}\sum_\mathfrak pN\mathfrak p^{-s}=O(1)$ as $s\downarrow1$. -/
theorem isBigO_fibre_sub {Q : Type*} [CommGroup Q] [Finite Q] (f : HeightOneSpectrum (𝓞 K) → Q)
    (hψ : ∀ ψ : MulChar Q ℂ, ψ ≠ 1 →
      (fun s : ℝ => primeSum (fun v => ψ (f v)) s) =O[𝓝[>] 1] (fun _ => (1 : ℂ))) :
    (fun s : ℝ => {v | f v = 1}.primeIdealZetaSum s -
        1 / (Nat.card Q : ℝ) * (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s)
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  classical
  have : Fintype (MulChar Q ℂ) := Fintype.ofFinite _
  set S : Set (HeightOneSpectrum (𝓞 K)) := {v | f v = 1} with hS
  set P : ℝ → ℝ := fun s => (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s with hP
  set n : ℕ := Nat.card Qˣ with hn_def
  have hnQ : Nat.card Q = n := Nat.card_congr (toUnits (G := Q)).toEquiv
  have hn0 : 0 < n := by rw [← hnQ]; exact Nat.card_pos
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hnorm : ∀ χ : MulChar Q ℂ, ∀ v, ‖χ (f v)‖ ≤ 1 := fun χ v => by
    have := norm_mulChar_apply_units χ (toUnits (f v))
    simpa using this.le
  have hkey : ∀ s : ℝ, 1 < s → ∑ χ : MulChar Q ℂ, primeSum (fun v => χ (f v)) s =
      n * (S.primeIdealZetaSum s : ℂ) := fun s hs => by
    have hs' : 1 < (s : ℂ).re := by simpa using hs
    simp only [primeSum]
    rw [← Summable.tsum_finsetSum fun χ _ => summable_mul_nps (hnorm χ) hs']
    rw [← primeSum_indicator, primeSum, ← tsum_mul_left]
    congr 1
    funext v
    rw [← Finset.sum_mul]
    have h := sum_mulChar_apply_units (M := Q) (toUnits (f v))
    simp only [val_toUnits_apply] at h
    rw [h]
    by_cases hv : f v = 1
    · have : toUnits (f v) = 1 := by rw [hv]; exact map_one _
      simp only [this, ↓reduceIte]
      rw [Set.indicator_of_mem (show v ∈ S from hv)]; ring
    · have : ¬ toUnits (f v) = 1 := fun h' => hv ((toUnits (G := Q)).map_eq_one_iff.mp h')
      simp only [this, ↓reduceIte]
      rw [Set.indicator_of_notMem (show v ∉ S from hv)]; ring
  have hrest : (fun s : ℝ => ∑ χ ∈ Finset.univ.erase (1 : MulChar Q ℂ), primeSum (fun v => χ (f v)) s)
      =O[𝓝[>] 1] (fun _ => (1 : ℂ)) := by
    refine IsBigO.fun_sum fun χ hχ => hψ χ (Finset.ne_of_mem_erase hχ)
  have hone : ∀ s : ℝ, primeSum (fun v => (1 : MulChar Q ℂ) (f v)) s = (P s : ℂ) := fun s => by
    rw [hP]
    simp only
    rw [primeIdealZetaSum_univ_eq]
    congr 1
    funext v
    rw [MulChar.one_apply (Group.isUnit _)]
  have hmain : ∀ s : ℝ, 1 < s → (n : ℂ) * (S.primeIdealZetaSum s : ℂ) - P s =
      ∑ χ ∈ Finset.univ.erase (1 : MulChar Q ℂ), primeSum (fun v => χ (f v)) s := fun s hs => by
    rw [← hkey s hs, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : MulChar Q ℂ)), hone]
    ring
  have hcomplex : (fun s : ℝ => (((S.primeIdealZetaSum s - 1 / (Nat.card Q : ℝ) * P s : ℝ)) : ℂ))
      =O[𝓝[>] 1] (fun _ => (1 : ℂ)) := by
    refine (hrest.const_mul_left ((n : ℂ)⁻¹)).congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    rw [← hmain s hs, hnQ]
    push_cast
    field_simp
  obtain ⟨c, hc⟩ := hcomplex.bound
  refine IsBigO.of_bound c ?_
  filter_upwards [hc] with s hs
  rw [Complex.norm_real, norm_one, mul_one] at hs
  rw [norm_one, mul_one]
  exact hs

/-- **Character sums over primes, ray class characters.** For a character $\psi\ne1$ of $C_\mathfrak m$ and any
assignment $f$ of ray classes to primes agreeing with $\mathfrak p\mapsto[\mathfrak p]$ off $\mathfrak m_0$,
$\sum_\mathfrak p\psi(f(\mathfrak p))N\mathfrak p^{-s}=O(1)$ as $s\downarrow1$. -/
theorem isBigO_primeSum_rayChar (m : Modulus K) (f : HeightOneSpectrum (𝓞 K) → RayClassGroup m)
    (hf : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite), f v = rayClass m v hv)
    (ψ : MulChar (RayClassGroup m) ℂ) (hψ1 : ψ ≠ 1) :
    (fun s : ℝ => primeSum (fun v => ψ (f v)) s) =O[𝓝[>] 1] (fun _ => (1 : ℂ)) := by
  classical
  have : Finite (RayClassGroup m) := (theorem_1_7_card m).1
  have hS : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ m.finite}.Finite :=
    Ideal.finite_factors m.finite_ne_bot
  obtain ⟨Ψ, hpow, hne, hloc⟩ := exists_heckeChar m ψ
  have hn : Nat.card (RayClassGroup m) ≠ 0 := Nat.card_pos.ne'
  have h1 := isBigO_primeSum_heckeCoeff_of_pow_eq_one hn hpow (hne hψ1)
  have hU := isUnitary_of_pow_eq_one hn hpow
  have ha : ∀ v, ‖ψ (f v)‖ ≤ 1 := fun v => by
    refine (Complex.norm_eq_one_of_pow_eq_one (n := Nat.card (RayClassGroup m)) ?_ hn).le
    have := pow_card_eq_one' (G := RayClassGroup m) (x := f v)
    calc ψ (f v) ^ Nat.card (RayClassGroup m) = ψ (f v ^ Nat.card (RayClassGroup m)) := (map_pow ψ _ _).symm
      _ = 1 := by rw [this, map_one]
  have hdiff := isBigO_primeSum_sub_of_finite (a := fun v => ψ (f v)) (b := heckeCoeff Ψ) ha
    (norm_heckeCoeff_le hU) (hS.subset fun v hv => by
      by_contra hv'
      apply hv
      obtain ⟨hu, hval⟩ := hloc v hv'
      rw [hf v hv', heckeCoeff]; simp only [hu, ite_true]; exact hval.symm)
  refine (hdiff.add h1).congr_left fun s => ?_
  simp

/-- **Primes in a subgroup, generic form.** If $f$ maps primes to a finite abelian group $G$ with
$\sum_\mathfrak p\psi(f(\mathfrak p))N\mathfrak p^{-s}=O(1)$ for every character $\psi\ne1$ of $G$, then for every
subgroup $H$ the set $\{\mathfrak p: f(\mathfrak p)\in H\}$ has Dirichlet density $1/(G:H)$ (Milne's form). -/
theorem milneHasDirichletDensity_preimage {G : Type*} [CommGroup G] [Finite G] (H : Subgroup G)
    (f0 : HeightOneSpectrum (𝓞 K) → G)
    (hψ : ∀ ψ : MulChar G ℂ, ψ ≠ 1 →
      (fun s : ℝ => primeSum (fun v => ψ (f0 v)) s) =O[𝓝[>] 1] (fun _ => (1 : ℂ))) :
    MilneHasDirichletDensity {v | f0 v ∈ H} (1 / (H.index : ℝ)) := by
  classical
  let f : HeightOneSpectrum (𝓞 K) → G ⧸ H := fun v => QuotientGroup.mk (f0 v)
  have hψ' : ∀ ψ : MulChar (G ⧸ H) ℂ, ψ ≠ 1 →
      (fun s : ℝ => primeSum (fun v => ψ (f v)) s) =O[𝓝[>] 1] (fun _ => (1 : ℂ)) := by
    intro ψ hψ1
    let ψ' : MulChar G ℂ :=
      ⟨ψ.toMonoidHom.comp (QuotientGroup.mk' H), fun a ha => absurd (Group.isUnit a) ha⟩
    have hψ'1 : ψ' ≠ 1 := by
      intro h1
      apply hψ1
      refine MulChar.ext' fun q => ?_
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have := congrArg (fun χ : MulChar G ℂ => χ g) h1
      rw [MulChar.one_apply (Group.isUnit _)]
      rw [MulChar.one_apply (Group.isUnit g)] at this
      exact this
    exact hψ ψ' hψ'1
  have hfib := isBigO_fibre_sub f hψ'
  have hS : {v | f v = 1} = {v | f0 v ∈ H} := by
    ext v
    exact QuotientGroup.eq_one_iff _
  rw [hS] at hfib
  have hidx : (H.index : ℝ) = (Nat.card (G ⧸ H) : ℝ) := rfl
  unfold MilneHasDirichletDensity
  have hlog := (isBigO_primeIdealZetaSum_sub_log (F := K)).const_mul_left (1 / (H.index : ℝ))
  refine (hfib.add hlog).congr' ?_ EventuallyEq.rfl
  filter_upwards with s
  rw [hidx]
  ring

/-- **Theorem 4.8** (Milne, *CFT*, Chapter VI, Theorem 4.8, p. 197; here unconditional): for a modulus $\mathfrak m$ and
a subgroup $H$ of $C_\mathfrak m$, the set of primes in $H$ has Dirichlet density $1/(C_\mathfrak m:H)$ if
$L(1,\chi)\ne0$ for all nontrivial $\chi$ trivial on $H$, and $0$ otherwise; the condition always holds
(`Ch8.theorem7_1`), so the density is $1/(C_\mathfrak m:H)$. Proved by orthogonality on $C_\mathfrak m/H$
(`isBigO_fibre_sub`) and the boundedness of the character sums (`isBigO_primeSum_rayChar`, from the Hecke
$L$-functions). -/
@[kb "milne2020cft" "Ch. VI, Thm. 4.8"]
theorem theorem4_8 (K : Type) [Field K] [NumberField K] : Theorem4_8 K := by
  classical
  refine ⟨fun m H => ?_⟩
  have h71 := Ch8.theorem7_1 K
  have hcond : ∀ χ : RayClassGroup m →* ℂˣ, (∀ h ∈ H, χ h = 1) → χ ≠ 1 → WeberLOneNeZero m χ :=
    fun χ _ hχ => h71.ne_zero m χ hχ
  rw [if_pos hcond]
  have : Finite (RayClassGroup m) := (theorem_1_7_card m).1
  let f0 : HeightOneSpectrum (𝓞 K) → RayClassGroup m := fun v =>
    if hv : ¬ v.asIdeal ∣ m.finite then rayClass m v hv else 1
  have hf0 : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite), f0 v = rayClass m v hv :=
    fun v hv => by simp [f0, hv]
  have hdens := milneHasDirichletDensity_preimage H f0
    (fun ψ hψ1 => isBigO_primeSum_rayChar m f0 hf0 ψ hψ1)
  refine milneHasDirichletDensity_congr_finite hdens ?_
  refine (Ideal.finite_factors m.finite_ne_bot).subset fun v hv => ?_
  by_contra hvd
  have hvd' : ¬ v.asIdeal ∣ m.finite := hvd
  have key : f0 v ∈ H ↔ rayClass m v hvd' ∈ H := by rw [hf0 v hvd']
  rcases Set.mem_symmDiff.mp hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 ⟨hvd', key.mp h1⟩
  · obtain ⟨hv2, hv3⟩ := h1
    exact h2 (key.mpr hv3)

end NumberFieldKB.MilneCFT.Ch6