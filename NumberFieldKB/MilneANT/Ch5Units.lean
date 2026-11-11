import Mathlib.Algebra.QuadraticAlgebra.Discriminant
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import QuadFormsKB.Citation
import QuadFormsKB.Binary.FormAut
import QuadFormsKB.Literature.HasseNorm.SUnits

/-!
# Milne, *Algebraic Number Theory*, Chapter 5: units of quadratic fields, Remark 5.7, $S$-units

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers.

* **Example 5.3** (`example_5_3_isUnit_iff`, `example_5_3_neg`, `example_5_3_pos`): units of a quadratic field.
  Milne writes $K = \mathbb Q[\sqrt d]$ with $d$ squarefree; here the field is QuadFormsKB's `QField D`,
  $D$ the discriminant of $K$ ($D = d$ if $d \equiv 1 \bmod 4$, $D = 4d$ otherwise, so $D < 0 \iff d < 0$), with
  $\mathcal O_K = \mathbb Z[\omega]$, $\omega = (b_D + \sqrt D)/2$, $b_D = D \bmod 4$ (QuadFormsKB's `orderEquiv`).
  The two equations of Milne ($m^2 - n^2d = \pm1$, resp. $(2m+n)^2 - dn^2 = \pm 4$) become the single equation
  $(2m + b_D n)^2 - Dn^2 = \pm 4$ for $m + n\omega$: for $D = 4d$ it is $4(m^2 - dn^2) = \pm 4$, for $D = d$ it is
  Milne's second equation.
* **Real fields** (running text before Example 5.3, `torsionOrder_eq_two_of_isReal`): $\mu(K) = \{\pm 1\}$ for every
  number field with a real embedding.
* **Remark 5.7** (`remark_5_7`): $(3 + 4i)/5$ and its conjugate have absolute value $1$, as do their powers, but
  its powers form an infinite set (it is not an algebraic integer).
* **Theorem 5.11** (`theorem_5_11`): the group of $S$-units is finitely generated of rank $r + s + \#S - 1$.
  Proved in QuadFormsKB (`QuadFormsKB.HN.finrank_sUnit`, tagged to Milne's class field theory notes); restated
  here in Milne's form. The $S$-units are Mathlib's `Set.unit`, the $S$-integers Mathlib's `Set.integer`.
-/

open NumberField NumberField.InfinitePlace NumberField.Units IsDedekindDomain QuadFormsKB.Binary

namespace NumberFieldKB.MilneANT

/-- **Example 5.3, the unit equation.** Let $K$ be the quadratic field of discriminant $D$ (`QField D`), with
$\mathcal O_K = \{m + n\omega\}$. Then $m + n\omega$ is a unit iff $(2m + b_D n)^2 - Dn^2 = \pm 4$, where
$b_D = D \bmod 4 \in \{0, 1\}$; for $D = 4d$ this is Milne's $m^2 - n^2 d = \pm 1$ and for $D = d \equiv 1 \bmod 4$
Milne's $(2m + n)^2 - dn^2 = \pm 4$. -/
@[kb "milne2020ant" "v3.08, Example 5.3, p. 86"]
theorem example_5_3_isUnit_iff {D : ℤ} [IsQuadDisc D] (m n : ℤ) :
    IsUnit (orderEquiv D ⟨m, n⟩) ↔
      (2 * m + qb D * n) ^ 2 - D * n ^ 2 = 4 ∨ (2 * m + qb D * n) ^ 2 - D * n ^ 2 = -4 := by
  have hD4 := (IsQuadDisc.fund (D := D)).1
  have hq := discr_qa_qb hD4
  have hu : IsUnit (orderEquiv D ⟨m, n⟩) ↔ IsUnit (⟨m, n⟩ : QOrder D) :=
    MulEquiv.isUnit_map (orderEquiv D).toRingEquiv.toMulEquiv
  rw [hu, QuadraticAlgebra.isUnit_iff_norm_isUnit,
    Int.isUnit_iff, QuadraticAlgebra.norm_def]
  have hq' : qb D ^ 2 + 4 * qa D = D := hq
  have e : (2 * m + qb D * n) ^ 2 - D * n ^ 2 =
      4 * (m * m + qb D * m * n - qa D * n * n) := by
    linear_combination (n ^ 2) * hq'
  rw [e]
  generalize m * m + qb D * m * n - qa D * n * n = X
  omega

open NumberField.Units in
set_option backward.isDefEq.respectTransparency false in
/-- Helper: in a number field with a real place, every root of unity in the unit group is $1$ or $-1$ (the argument
of Mathlib's `torsionOrder_eq_two_of_odd_finrank`). -/
theorem torsion_cases (K : Type*) [Field K] [NumberField K] (hr : 0 < nrRealPlaces K) (x : torsion K) :
    (x : (𝓞 K)ˣ) = 1 ∨ (x : (𝓞 K)ˣ) = -1 := by
  by_cases! hc : 2 < orderOf (x : (𝓞 K)ˣ)
  · rw [← orderOf_units, ← orderOf_submonoid] at hc
    linarith [IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc
      (IsPrimitiveRoot.orderOf (x.1 : K))]
  · interval_cases hi : orderOf (x : (𝓞 K)ˣ)
    · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]
    · exact Or.intro_left _ (orderOf_eq_one_iff.1 hi)
    · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, ← Units.val_inj, Units.val_neg, Units.val_one, hi]

open NumberField.Units in
/-- Helper: a number field with a real place has exactly two roots of unity. -/
theorem torsionOrder_eq_two_of_nrRealPlaces_pos (K : Type*) [Field K] [NumberField K]
    (hr : 0 < nrRealPlaces K) : torsionOrder K = 2 := by
  classical
  let := Fintype.ofFinite (torsion K)
  rw [torsionOrder, Nat.card_eq_fintype_card]
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact torsion_cases K hr x

/-- **Example 5.3, $d < 0$.** For an imaginary quadratic field the unit group is finite, so $U_K = \mu(K)$; and
$\mu(K) = \{\pm 1\}$ except for $\mathbb Q[i]$ ($D = -4$, $\mu(K) = \{\pm 1, \pm i\}$) and $\mathbb Q[\sqrt{-3}]$
($D = -3$, $\mu(K)$ of order $6$). The order of $\mu(K)$ is QuadFormsKB's `torsionOrder_of_neg`. -/
@[kb "milne2020ant" "v3.08, Example 5.3, p. 86"]
theorem example_5_3_neg {D : ℤ} [IsQuadDisc D] (hD : D < 0) :
    Finite (𝓞 (QField D))ˣ ∧ torsion (QField D) = ⊤ ∧
      torsionOrder (QField D) = if D = -3 then 6 else if D = -4 then 4 else 2 := by
  have hr : rank (QField D) = 0 := by
    rw [rank, card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_of_neg hD, nrComplexPlaces_of_neg hD]
  have htop : torsion (QField D) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    obtain ⟨c, hc, -⟩ := exist_unique_eq_mul_prod (QField D) x
    have : IsEmpty (Fin (rank (QField D))) := by rw [hr]; infer_instance
    rw [hc, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    exact c.1.2
  refine ⟨?_, htop, torsionOrder_of_neg hD⟩
  have : Finite (torsion (QField D)) := inferInstance
  rw [htop] at this
  exact Finite.of_equiv _ (Subgroup.topEquiv (G := (𝓞 (QField D))ˣ)).toEquiv

/-- **Example 5.3, $d > 0$.** For a real quadratic field there are infinitely many units, and
$U_K = \pm u^{\mathbb Z}$ for a fundamental unit $u$. -/
@[kb "milne2020ant" "v3.08, Example 5.3, p. 86"]
theorem example_5_3_pos {D : ℤ} [IsQuadDisc D] (hD : 0 < D) :
    Infinite (𝓞 (QField D))ˣ ∧ ∃ u : (𝓞 (QField D))ˣ, ∀ v : (𝓞 (QField D))ˣ, ∃ m : ℤ, v = u ^ m ∨ v = -u ^ m := by
  have hr : rank (QField D) = 1 := by
    rw [rank, card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_of_pos hD, nrComplexPlaces_of_pos hD]
  have hreal : 0 < nrRealPlaces (QField D) := by rw [nrRealPlaces_of_pos hD]; norm_num
  refine ⟨?_, ?_⟩
  · by_contra hinf
    rw [not_infinite_iff_finite] at hinf
    have h1 := finrank_eq (QField D)
    have : Finite (Additive (𝓞 (QField D))ˣ) := inferInstanceAs (Finite (𝓞 (QField D))ˣ)
    have ht : Module.IsTorsion ℤ (Additive (𝓞 (QField D))ˣ) := by
      intro x
      refine ⟨⟨(addOrderOf x : ℤ), mem_nonZeroDivisors_of_ne_zero
        (by exact_mod_cast (addOrderOf_pos x).ne')⟩, ?_⟩
      simp
    rw [ht.finrank_eq_zero] at h1
    omega
  · have h0 : 0 < rank (QField D) := by omega
    refine ⟨fundSystem (QField D) ⟨0, h0⟩, fun v => ?_⟩
    obtain ⟨⟨ζ, f⟩, hc, -⟩ := exist_unique_eq_mul_prod (QField D) v
    have hsing : ∀ f : Fin (rank (QField D)) → ℤ, ∏ i, fundSystem (QField D) i ^ f i =
        fundSystem (QField D) ⟨0, h0⟩ ^ f ⟨0, h0⟩ := by
      intro f
      have : Subsingleton (Fin (rank (QField D))) := by rw [hr]; infer_instance
      rw [Fintype.prod_subsingleton _ ⟨0, h0⟩]
    rw [hsing] at hc
    refine ⟨f ⟨0, h0⟩, ?_⟩
    rcases torsion_cases (QField D) hreal ζ with h | h
    · left; rw [hc]; simp [h]
    · right; rw [hc]; simp [h]

/-- **Real fields have $\mu(K) = \{\pm 1\}$** (Milne, running text before Example 5.3, p. 86: "For all real fields,
i.e., fields with an embedding into $\mathbb R$, $\mu(K) = \{\pm 1\}$"). -/
@[kb "milne2020ant" "v3.08, Ch. 5, before Example 5.3, p. 86"]
theorem torsionOrder_eq_two_of_isReal {K : Type*} [Field K] [NumberField K] (φ : K →+* ℝ) :
    torsionOrder K = 2 := by
  exact torsionOrder_eq_two_of_nrRealPlaces_pos K
    (by
      have : IsReal (InfinitePlace.mk (Complex.ofRealHom.comp φ)) := by
        rw [isReal_mk_iff, ComplexEmbedding.isReal_iff]
        ext x; simp
      refine Nat.pos_of_ne_zero fun h => ?_
      simp [nrRealPlaces, Fintype.card_eq_zero_iff, isEmpty_subtype] at h
      exact (not_isReal_iff_isComplex.mpr (h _)) this)

/-- **Remark 5.7.** The integrality hypothesis in Corollary 5.6 is needed: $\alpha = (3 + 4i)/5$ and its
conjugate $\bar\alpha$ have absolute value $1$, as do all powers of $\alpha$, but the set
$\{1, \alpha, \alpha^2, \dots\}$ is not finite. (Consequently $\alpha$ is not an algebraic integer.) -/
@[kb "milne2020ant" "v3.08, Remark 5.7, p. 87"]
theorem remark_5_7 :
    ‖(3 + 4 * Complex.I) / 5‖ = 1 ∧ ‖starRingEnd ℂ ((3 + 4 * Complex.I) / 5)‖ = 1 ∧
      (∀ n : ℕ, ‖((3 + 4 * Complex.I) / 5) ^ n‖ = 1) ∧
      (Set.range fun n : ℕ => ((3 + 4 * Complex.I) / 5) ^ n).Infinite ∧
      ¬ IsIntegral ℤ ((3 + 4 * Complex.I) / 5) := by
  have h5 : ‖(3 + 4 * Complex.I : ℂ)‖ = 5 := by
    rw [show (3 + 4 * Complex.I : ℂ) = ((3 : ℝ) : ℂ) + (4 : ℝ) * Complex.I by push_cast; ring,
      Complex.norm_def, Complex.normSq_add_mul_I, show (3 : ℝ) ^ 2 + 4 ^ 2 = 5 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h1 : ‖(3 + 4 * Complex.I : ℂ) / 5‖ = 1 := by
    rw [norm_div, h5]; simp
  have hni : ¬ IsIntegral ℤ ((3 + 4 * Complex.I) / 5 : ℂ) := by
    intro h
    have hc : IsIntegral ℤ (starRingEnd ℂ ((3 + 4 * Complex.I) / 5)) :=
      h.map (starRingEnd ℂ).toIntAlgHom
    have hs := h.add hc
    have e : (3 + 4 * Complex.I) / 5 + starRingEnd ℂ ((3 + 4 * Complex.I) / 5) =
        algebraMap ℚ ℂ (6 / 5) := by
      apply Complex.ext <;> simp [Complex.div_re, Complex.div_im] <;> norm_num
    rw [e, isIntegral_algebraMap_iff] at hs
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hs
    simp at hy
    have : (y : ℚ) * 5 = 6 := by rw [hy]; norm_num
    have : y * 5 = 6 := by exact_mod_cast this
    omega
  refine ⟨h1, (Complex.norm_conj _).trans h1, fun n => by rw [norm_pow, h1, one_pow], ?_, hni⟩
  intro hfin
  obtain ⟨a, b, hab, he⟩ := hfin.exists_lt_map_eq_of_forall_mem
    (f := fun n : ℕ => ((3 + 4 * Complex.I) / 5 : ℂ) ^ n) (fun n => Set.mem_range_self n)
  have hne : ((3 + 4 * Complex.I) / 5 : ℂ) ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  have hk : ((3 + 4 * Complex.I) / 5 : ℂ) ^ (b - a) = 1 := by
    have : ((3 + 4 * Complex.I) / 5 : ℂ) ^ a * ((3 + 4 * Complex.I) / 5) ^ (b - a) =
        ((3 + 4 * Complex.I) / 5) ^ a * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hab.le, mul_one]; exact he.symm
    exact mul_left_cancel₀ (pow_ne_zero _ hne) this
  apply hni
  exact IsIntegral.of_pow (by omega) (hk ▸ isIntegral_one)

/-- **Theorem 5.11** (unit theorem for $S$-units). Let $S$ be a finite set of prime ideals of a number field $F$
with $r$ real and $2s$ nonreal complex embeddings. The group $U(S)$ of $S$-units (Mathlib's `Set.unit`:
$\{\alpha \in F^\times : \operatorname{ord}_{\mathfrak p}(\alpha) = 0 \text{ for all } \mathfrak p \notin S\}$) is
finitely generated, of rank $r + s + \#S - 1$ (the rank of a finitely generated abelian group is the dimension of
its free part, `Module.finrank ℤ` of the additive group). The proof is QuadFormsKB's `HN.finrank_sUnit`. -/
@[kb "milne2020ant" "v3.08, Theorem 5.11, p. 90"]
theorem theorem_5_11 {F : Type*} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Group.FG ((S : Set (HeightOneSpectrum (𝓞 F))).unit F) ∧
      (Module.finrank ℤ (Additive ((S : Set (HeightOneSpectrum (𝓞 F))).unit F)) : ℤ) =
        nrRealPlaces F + nrComplexPlaces F + S.card - 1 := by
  refine ⟨?_, ?_⟩
  · have : Module.Finite ℤ (Additive ((S : Set (HeightOneSpectrum (𝓞 F))).unit F)) :=
      inferInstanceAs (Module.Finite ℤ (Additive (QuadFormsKB.HN.SUnit (F := F) S)))
    exact GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp this)
  · have h := QuadFormsKB.HN.finrank_sUnit (F := F) S
    have hpos : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    have hc := card_eq_nrRealPlaces_add_nrComplexPlaces F
    rw [show (Module.finrank ℤ (Additive ((S : Set (HeightOneSpectrum (𝓞 F))).unit F)) : ℤ) =
      (Units.rank F + S.card : ℕ) from by exact_mod_cast h]
    rw [rank]
    push_cast [Nat.cast_sub (show 1 ≤ Fintype.card (InfinitePlace F) from hpos)]
    rw [hc]; push_cast; ring

end NumberFieldKB.MilneANT
